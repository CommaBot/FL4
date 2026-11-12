//! The two traits that connect fl4-core to the world (DESIGN.md §6).
//!
//! `Store` is kernel memory, seen as 64-bit words addressed by kernel
//! virtual address (the kernel window maps all physical memory). Every
//! kernel object, every capability slot and the kernel's own global state
//! live in this memory, so the store is the whole kernel state apart from
//! the hardware. `Arch` is everything else the core asks the machine to do.

/// Kernel memory.
pub trait Store {
    /// Read the aligned word at `addr`.
    fn read(&self, addr: u64) -> u64;
    /// Write the aligned word at `addr`.
    fn write(&mut self, addr: u64, v: u64);
    /// Zero `len` bytes at `addr`; both are multiples of 8.
    fn zero(&mut self, addr: u64, len: u64);
    /// Base address of the kernel's global state (see `layout::ks`).
    fn ks_base(&self) -> u64;
    /// Index of the core this kernel entry runs on.
    fn cur_cpu(&self) -> u64;
}

/// Machine operations the kernel logic needs. Implemented by the x86_64
/// backend on hardware and by the simulator.
pub trait Arch {
    // Time (MCS): ticks are the timer's own units (the TSC on x86).
    fn now(&mut self) -> u64;
    fn set_deadline(&mut self, ticks: u64);
    fn us_to_ticks(&self, us: u64) -> u64;
    fn ticks_to_us(&self, ticks: u64) -> u64;
    /// Largest number of microseconds whose tick count fits in 64 bits.
    fn max_us(&self) -> u64;
    /// Kernel worst-case execution time, in ticks.
    fn kernel_wcet_ticks(&self) -> u64;

    /// Whether an interrupt is pending (preemption points).
    fn irq_pending(&mut self) -> bool;
    /// Take the highest pending interrupt, if any (seL4 receivePendingIRQ
    /// and getActiveIRQ). Returns `crate::syscall::NO_IRQ` for none.
    fn take_pending_irq(&mut self) -> u64;
    fn mask_irq(&mut self, irq: u64, mask: bool);
    fn ack_irq(&mut self, irq: u64);

    /// Switch to the address space whose top-level table is at `root`
    /// (a kernel virtual address).
    fn set_vspace(&mut self, root: u64, asid: u64);
    fn invalidate_page(&mut self, asid: u64, vaddr: u64);
    fn invalidate_asid(&mut self, asid: u64);
    /// Drop cached translations of paging structures (after unmapping a
    /// page table).
    fn invalidate_page_structures(&mut self, asid: u64);

    /// Program an IOAPIC pin to deliver `vector`. Returns false when the
    /// IOAPIC or pin does not exist.
    fn ioapic_map(&mut self, ioapic: u64, pin: u64, level: u64, polarity: u64, vector: u64) -> bool;
    /// l4h 0025: remappable-format IOAPIC entry with the caller's handle.
    fn ioapic_map_remapped(&mut self, ioapic: u64, pin: u64, level: u64, polarity: u64, vector: u64, handle: u64) -> bool;
    fn num_ioapics(&self) -> u64;
    fn ioapic_pins(&self, ioapic: u64) -> u64;

    fn port_in(&mut self, port: u64, size: u64) -> u64;
    fn port_out(&mut self, port: u64, size: u64, v: u64);

    /// Make sure the FPU state of the thread whose TCB is at `tcb` is in
    /// its TCB, not only in some CPU's registers.
    fn fpu_flush(&mut self, tcb: u64);
    /// Sanitise an XSAVE image in the TCB at `tcb` after it was written
    /// from user memory (l4h 0002).
    fn fpu_sanitise(&mut self, tcb: u64);
    /// The FPU state of `tcb` was replaced; reload it if it is live.
    fn fpu_reload(&mut self, tcb: u64);
    /// `tcb` is being deleted or moved away: forget any live FPU state.
    fn fpu_release(&mut self, tcb: u64);

    /// Debug console.
    fn putc(&mut self, c: u64);
    fn get_char(&mut self) -> u64;
    /// Stop the machine (seL4_DebugHalt).
    fn halt(&mut self);
}
