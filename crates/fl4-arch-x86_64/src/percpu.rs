//! Per-core backend state. The first two words are read by the SYSCALL
//! entry stub through KERNEL_GS_BASE (kernel stack top, scratch).
use core::cell::UnsafeCell;

/// Cores the backend has room for; the SMP milestone raises this.
pub const MAX_CPUS: usize = 8;
pub const KSTACK_SIZE: usize = 64 * 1024;
pub const NO_IRQ: u64 = u64::MAX;

#[repr(C)]
pub struct PerCpu {
    /// Read by entry.S at offset 0.
    pub stack_top: u64,
    /// Scratch for entry.S at offset 8.
    pub scratch: u64,
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
    /// Current CR3 and the ASID it belongs to.
    pub cr3: u64,
    pub asid: u64,
    pub apic_id: u32,
}

impl PerCpu {
    const fn new() -> PerCpu {
        PerCpu {
            stack_top: 0,
            scratch: 0,
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
            apic_id: 0,
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

/// The calling core's index. One core until the SMP milestone.
#[inline]
pub fn cpu_index() -> usize {
    0
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
