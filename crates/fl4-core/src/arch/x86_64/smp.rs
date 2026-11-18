/// An IPI arrived (seL4 `handleIPI`). Remote calls are serviced by the
/// architecture code before the kernel entry; a reschedule request makes
/// this core choose again.
pub fn handle_ipi<S: Store, A: Arch>(s: &mut S, a: &mut A, irq: u64) {
    let _ = a;
    if irq == crate::layout::irq::RESCHEDULE_IPI {
        sched::reschedule_required(s);
    }
}
