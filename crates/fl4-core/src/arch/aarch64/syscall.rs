macro_rules! syscall_insn_len {
    () => {
        4
    };
}

macro_rules! trapped_syscall_number {
    ($s:expr, $t:expr, $number:expr) => {
        $t.reg($s, reg::X8)
    };
}

macro_rules! instruction_fault {
    ($code:expr) => {
        ($code >> 26) & 0x3f == 0x20
    };
}

/// AArch64 guest synchronous trap / SError delivered as `VCPUFault`.
pub fn handle_vcpu_fault<S: Store, A: Arch>(s: &mut S, a: &mut A, hsr: u64) {
    if budget_ok(s, a) {
        let t = sched::cur_thread(s);
        // Entry recorded `FAULT_IP = elr - 4` for HVC so budget exhaustion or
        // a remote stall retries the HVC; once committed to fault delivery,
        // `FAULT_IP` must match `NEXT_IP` (`elr`) so the VMM reply resumes
        // after the HVC (just like seL4).
        let next = t.reg(s, reg::NEXT_IP);
        t.set_reg(s, reg::FAULT_IP, next);
        faults::handle_fault(s, a, t, Fault::VcpuFault { hsr });
    }
    finish(s, a);
}

/// AArch64 VGIC maintenance interrupt (PPI 25) delivered as `VGICMaintenance`.
pub fn handle_vgic_maintenance_entry<S: Store, A: Arch>(s: &mut S, a: &mut A, eisr: u64) {
    sched::update_timestamp(s, a);
    sched::check_budget(s, a);
    crate::vcpu::handle_vgic_maintenance(s, a, eisr);
    finish(s, a);
}

/// AArch64 virtual PPI interrupt (PPI 27 vTimer) delivered as `VPPIEvent`.
pub fn handle_vppi_event_entry<S: Store, A: Arch>(s: &mut S, a: &mut A, irq_id: u64) {
    sched::update_timestamp(s, a);
    sched::check_budget(s, a);
    crate::vcpu::handle_vppi_event(s, a, irq_id);
    finish(s, a);
}

/// Complete an `ARMVCPURun` invocation on guest exit (VMFault, VCPUFault, VGICMaint).
pub fn handle_vcpu_run_exit<S: Store, A: Arch>(
    s: &mut S,
    a: &mut A,
    stop: u64,
    w1: u64,
    w2: u64,
    w3: u64,
) {
    sched::update_timestamp(s, a);
    let ct = sched::cur_thread(s);
    crate::vcpu::complete_run(s, a, ct, stop, w1, w2, w3);
    sched::check_budget(s, a);
    finish(s, a);
}

/// Complete an `ARMVCPURun` invocation on a virtual PPI interrupt (PPI 27 vTimer).
pub fn handle_vcpu_run_vppi<S: Store, A: Arch>(s: &mut S, a: &mut A, irq_id: u64) {
    sched::update_timestamp(s, a);
    let ct = sched::cur_thread(s);
    let v = s.read(ct.0.wrapping_add(crate::layout::tcb::RUN_VCPU));
    if v != 0 && irq_id == crate::layout::irq::TIMER_ID {
        let masked = s.read(v.wrapping_add(crate::vcpu::VPPI_MASKED));
        s.write(v.wrapping_add(crate::vcpu::VPPI_MASKED), masked | 1);
    }
    a.mask_irq(crate::layout::irq::of(irq_id, s.cur_cpu()), true);
    crate::vcpu::complete_run(s, a, ct, fl4_abi::consts::vcpu_run_stop::VPPI, irq_id, 0, 0);
    sched::check_budget(s, a);
    finish(s, a);
}
