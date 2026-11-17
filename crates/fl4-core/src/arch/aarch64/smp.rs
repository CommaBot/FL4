/// AArch64: the reschedule SGI of any core.
pub fn handle_ipi<S: Store, A: Arch>(s: &mut S, a: &mut A, irq: u64) {
    let _ = a;
    if crate::layout::irq::id(irq) == crate::layout::irq::RESCHEDULE_ID {
        sched::reschedule_required(s);
    }
}
