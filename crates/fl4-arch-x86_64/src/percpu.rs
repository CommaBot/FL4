//! Per-core backend state, and which core the caller runs on.
use core::cell::UnsafeCell;
use core::sync::atomic::{AtomicU64, Ordering};

/// Cores the backend has room for.
pub const MAX_CPUS: usize = 16;
pub const KSTACK_SIZE: usize = 64 * 1024;
pub const NO_IRQ: u64 = u64::MAX;

#[repr(C)]
pub struct PerCpu {
    /// Top of this core's kernel stack in KSTACKS.
    pub stack_top: u64,
    /// The core is in the idle loop.
    pub idle: bool,
    /// The kernel is polling for an interrupt (`take_pending_irq`).
    pub polling: bool,
    /// The IRQ a poll accepted.
    pub polled_irq: u64,
    /// TCB whose FPU state is live in this core's registers (0 = none).
    pub fpu_owner: u64,
    /// CR0.TS is set (the current thread may not use the FPU).
    pub ts_set: bool,
    /// User FS/GS bases currently loaded.
    pub fs_base: u64,
    pub gs_base: u64,
    /// Debug registers hold a thread's breakpoints.
    pub dr_loaded: bool,
    /// The user address space this core runs (CR3 value and ASID). With
    /// the skim window the kernel runs on its own tables (entry.S loads
    /// them on every entry) and `exit_cr3` is what the exit to user code
    /// loads.
    pub cr3: u64,
    pub asid: u64,
    pub exit_cr3: u64,
    /// The ASIDs this core's PCIDs hold (tlb.rs).
    pub pcids: [crate::tlb::Slot; crate::tlb::SLOTS],
    pub apic_id: u32,
    /// This core holds the serial gate.
    pub gate_held: bool,
    /// The deadline the timer is armed for (TSC ticks; 0 = none).
    pub armed: u64,
    /// A transaction runs on this core (Arch effects are queued).
    pub tx: bool,
    pub effects: [crate::arch::Effect; crate::arch::MAX_EFFECTS],
    pub neffects: usize,
    /// An interrupt accepted during the current entry, offered again if
    /// the entry's transaction reruns.
    pub held_irq: u64,
    /// The current run of the entry (transaction attempt or serial run)
    /// was given `held_irq`.
    pub held_used: bool,
    /// Initialized locally before enabling virtualization.
    pub spec_plan: Option<crate::spec::policy::Plan>,
    pub spec_rejected: Option<crate::spec::policy::Rejected>,
}

impl PerCpu {
    const fn new() -> PerCpu {
        PerCpu {
            stack_top: 0,
            idle: false,
            polling: false,
            polled_irq: NO_IRQ,
            fpu_owner: 0,
            ts_set: false,
            fs_base: 0,
            gs_base: 0,
            dr_loaded: false,
            cr3: 0,
            asid: 0,
            exit_cr3: 0,
            pcids: [crate::tlb::Slot::EMPTY; crate::tlb::SLOTS],
            apic_id: 0,
            gate_held: false,
            armed: 0,
            tx: false,
            effects: [crate::arch::Effect::Ack; crate::arch::MAX_EFFECTS],
            neffects: 0,
            held_irq: NO_IRQ,
            held_used: false,
            spec_plan: None,
            spec_rejected: None,
        }
    }
}

struct Cells(UnsafeCell<[PerCpu; MAX_CPUS]>);
// SAFETY: each core touches only its own entry, with interrupts disabled.
unsafe impl Sync for Cells {}

static PERCPU: Cells = Cells(UnsafeCell::new([const { PerCpu::new() }; MAX_CPUS]));

#[repr(C, align(4096))]
pub struct Stacks(pub UnsafeCell<[[u8; KSTACK_SIZE]; MAX_CPUS]>);
unsafe impl Sync for Stacks {}
pub static KSTACKS: Stacks = Stacks(UnsafeCell::new([[0; KSTACK_SIZE]; MAX_CPUS]));

/// The per-core entry areas (the kernel's `SkimCpu`s: entry stack and IST
/// stacks, one area per core, `SKIM_STRIDE` bytes apart from `SKIM_BASE`).
/// Registered once the kernel sets up its descriptor tables; 0 before.
static SKIM_BASE: AtomicU64 = AtomicU64::new(0);
static SKIM_STRIDE: AtomicU64 = AtomicU64::new(0);

/// Tell `cpu_index` where the per-core entry areas are.
pub fn register_entry_areas(base: u64, stride: u64) {
    SKIM_BASE.store(base, Ordering::Relaxed);
    SKIM_STRIDE.store(stride, Ordering::Relaxed);
}

/// The core whose stack `rsp` is on: core `c` runs the kernel on
/// KSTACKS[c], and takes NMI, #DB, #MC and #DF (and, briefly, every entry
/// from user mode) on the stacks of its entry area `c`. Anything else is
/// the boot core's early boot stack: core 0.
fn index_of(rsp: u64, kstacks: u64, skim_base: u64, skim_stride: u64) -> usize {
    let off = rsp.wrapping_sub(kstacks);
    if off < (MAX_CPUS * KSTACK_SIZE) as u64 {
        return (off / KSTACK_SIZE as u64) as usize;
    }
    let off = rsp.wrapping_sub(skim_base);
    if skim_stride != 0 && off < MAX_CPUS as u64 * skim_stride {
        return (off / skim_stride) as usize;
    }
    0
}

/// The calling core's index, from the stack pointer (`index_of`).
#[inline]
pub fn cpu_index() -> usize {
    let rsp: u64;
    unsafe { core::arch::asm!("mov {}, rsp", out(reg) rsp, options(nomem, nostack, preserves_flags)) };
    index_of(rsp, KSTACKS.0.get() as u64, SKIM_BASE.load(Ordering::Relaxed), SKIM_STRIDE.load(Ordering::Relaxed))
}

/// This core's state. Callers run with interrupts disabled and must not
/// hold two of these references at once.
#[allow(clippy::mut_from_ref)]
pub fn get() -> &'static mut PerCpu {
    get_for(cpu_index())
}

#[allow(clippy::mut_from_ref)]
pub fn get_for(i: usize) -> &'static mut PerCpu {
    unsafe { &mut (*PERCPU.0.get())[i] }
}

/// Set up `i`'s stack top; returns it.
pub fn init(i: usize) -> u64 {
    let base = unsafe { (*KSTACKS.0.get())[i].as_ptr() as u64 };
    let top = base + KSTACK_SIZE as u64;
    let p = get_for(i);
    p.stack_top = top;
    top
}

#[cfg(test)]
mod tests {
    use super::*;

    const KS: u64 = 0xffff_ffff_8040_0000;
    const SKIM: u64 = 0xffff_ffff_8030_0000;
    const STRIDE: u64 = 0x8000;

    #[test]
    fn every_kernel_stack_names_its_core() {
        for c in 0..MAX_CPUS {
            let base = KS + (c * KSTACK_SIZE) as u64;
            for rsp in [base, base + 8, base + KSTACK_SIZE as u64 - 8] {
                assert_eq!(index_of(rsp, KS, SKIM, STRIDE), c);
            }
        }
    }

    /// An NMI or #DB from user mode on core c runs on c's IST stacks, not
    /// KSTACKS: it must not be taken for core 0 (whose TCB, PerCpu and
    /// gate slot it would then use).
    #[test]
    fn entry_and_ist_stacks_name_their_core() {
        for c in 0..MAX_CPUS {
            let area = SKIM + c as u64 * STRIDE;
            // Header page, entry stack, then IST1..IST4.
            for page in 1..6 {
                let top = area + (page + 1) * 4096;
                assert_eq!(index_of(top - 176, KS, SKIM, STRIDE), c, "core {c} page {page}");
                assert_eq!(index_of(area + page * 4096, KS, SKIM, STRIDE), c);
            }
            assert_eq!(index_of(area + STRIDE - 8, KS, SKIM, STRIDE), c);
        }
    }

    #[test]
    fn other_stacks_are_the_boot_core() {
        // The early boot stack, and anything outside both ranges.
        assert_eq!(index_of(0xffff_ffff_8019_0000, KS, SKIM, STRIDE), 0);
        assert_eq!(index_of(SKIM + MAX_CPUS as u64 * STRIDE, KS, SKIM, STRIDE), 0);
        assert_eq!(index_of(KS + (MAX_CPUS * KSTACK_SIZE) as u64, KS, SKIM, STRIDE), 0);
        assert_eq!(index_of(SKIM - 8, KS, SKIM, STRIDE), 0);
        // Before the entry areas are registered.
        assert_eq!(index_of(SKIM + 3 * STRIDE + 4096, KS, 0, 0), 0);
    }

    #[test]
    fn the_real_kernel_stacks_name_their_core() {
        let base = KSTACKS.0.get() as u64;
        assert_eq!(index_of(base + 5 * KSTACK_SIZE as u64 + 100, base, 0, 0), 5);
    }
}
