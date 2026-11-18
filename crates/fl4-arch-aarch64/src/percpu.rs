//! Per-core backend state, reached through TPIDR_EL1. The first word is
//! read by the exception vectors (entry.S): the core's kernel stack top.
use core::cell::UnsafeCell;

/// Cores the backend has room for (and that have banked interrupt state,
/// `fl4_core::layout::irq::BANKED_CORES`).
pub const MAX_CPUS: usize = 16;
const _: () = assert!(MAX_CPUS as u64 == fl4_core::layout::irq::BANKED_CORES);
pub const KSTACK_SIZE: usize = 64 * 1024;
pub const NO_IRQ: u64 = u64::MAX;

#[repr(C)]
pub struct PerCpu {
    /// Read by entry.S at offset 0.
    pub stack_top: u64,
    /// This core's index, at offset 8.
    pub index: u64,
    /// The core is in the idle loop.
    pub idle: bool,
    /// TCB whose FP/SIMD state is live in this core's registers (0 = none).
    pub fpu_owner: u64,
    /// EL0 may use FP/SIMD (CPACR_EL1.FPEN), as last written.
    pub fp_enabled: bool,
    /// The user address space this core runs (TTBR0_EL1 value).
    pub ttbr0: u64,
    /// `mmu::ASID_GEN` when this core last flushed its TLB for it.
    pub asid_gen: u64,
    /// Another core invalidated the ASID this core runs: the exit checks
    /// that it still names the current thread's VSpace (`mmu::retired`).
    pub vspace_stale: bool,
    /// MPIDR_EL1 affinity of this core.
    pub mpidr: u64,
    /// GICv3: this core's redistributor (kernel virtual address). GICv2:
    /// the CPU interface number SGIs target.
    pub gicr: u64,
    pub gic_cpu: u64,
    /// This core holds the serial gate.
    pub gate_held: bool,
    /// The deadline the timer is armed for (counter ticks; 0 = none).
    pub armed: u64,
    /// A transaction runs on this core (Arch effects are queued).
    pub tx: bool,
    pub effects: [crate::arch::Effect; crate::arch::MAX_EFFECTS],
    pub neffects: usize,
    /// An interrupt accepted during the current entry, offered again if
    /// the entry's transaction reruns (a GIC interrupt ID).
    pub held_irq: u64,
    /// The current run of the entry was given `held_irq`.
    pub held_used: bool,
    /// The raw acknowledge value of the interrupt last taken (GICv2 SGIs
    /// carry their source in it, which the EOI needs).
    pub iar: u64,
}

impl PerCpu {
    const fn new() -> PerCpu {
        PerCpu {
            stack_top: 0,
            index: 0,
            idle: false,
            fpu_owner: 0,
            fp_enabled: true,
            ttbr0: 0,
            asid_gen: 0,
            vspace_stale: false,
            mpidr: 0,
            gicr: 0,
            gic_cpu: 0,
            gate_held: false,
            armed: 0,
            tx: false,
            effects: [crate::arch::Effect::Ack(0); crate::arch::MAX_EFFECTS],
            neffects: 0,
            held_irq: NO_IRQ,
            held_used: false,
            iar: 0,
        }
    }
}

struct Cells(UnsafeCell<[PerCpu; MAX_CPUS]>);
// SAFETY: each core touches only its own entry, with interrupts disabled;
// other cores read the few fields documented as shared.
unsafe impl Sync for Cells {}

static PERCPU: Cells = Cells(UnsafeCell::new([const { PerCpu::new() }; MAX_CPUS]));

#[repr(C, align(4096))]
pub struct Stacks(pub UnsafeCell<[[u8; KSTACK_SIZE]; MAX_CPUS]>);
unsafe impl Sync for Stacks {}
pub static KSTACKS: Stacks = Stacks(UnsafeCell::new([[0; KSTACK_SIZE]; MAX_CPUS]));

/// The calling core's index (TPIDR_EL1 points at its `PerCpu`).
#[inline]
pub fn cpu_index() -> usize {
    let p = crate::mrs!("tpidr_el1");
    if p == 0 {
        0
    } else {
        unsafe { (*(p as *const PerCpu)).index as usize }
    }
}

/// This core's state. Callers run with interrupts disabled and must not
/// hold two of these references at once.
#[allow(clippy::mut_from_ref)]
#[inline]
pub fn get() -> &'static mut PerCpu {
    let p = crate::mrs!("tpidr_el1");
    if p == 0 {
        get_for(0)
    } else {
        unsafe { &mut *(p as *mut PerCpu) }
    }
}

#[allow(clippy::mut_from_ref)]
pub fn get_for(i: usize) -> &'static mut PerCpu {
    unsafe { &mut (*PERCPU.0.get())[i] }
}

/// Give core `i` its index and kernel stack; returns the stack top.
pub fn init_stack(i: usize) -> u64 {
    let base = unsafe { (*KSTACKS.0.get())[i].as_ptr() as u64 };
    let top = base + KSTACK_SIZE as u64;
    let p = get_for(i);
    p.stack_top = top;
    p.index = i as u64;
    top
}

/// On core `i`: set up its state and point TPIDR_EL1 at it; returns its
/// kernel stack top.
pub fn init(i: usize) -> u64 {
    let top = init_stack(i);
    let p = get_for(i);
    p.mpidr = crate::cpu::mpidr();
    crate::msr!("tpidr_el1", p as *mut PerCpu as u64);
    top
}

/// The stack top of core `i`.
pub fn stack_top(i: usize) -> u64 {
    unsafe { (*KSTACKS.0.get())[i].as_ptr() as u64 + KSTACK_SIZE as u64 }
}
