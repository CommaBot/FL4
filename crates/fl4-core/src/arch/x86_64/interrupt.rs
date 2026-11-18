/// seL4 `decodeIRQControlInvocation` with the x86 arch part.
pub fn decode_irq_control<S: Store, A: Arch>(s: &mut S, a: &mut A, lbl: u64, length: u64, src: Slot, buf: u64, extra: &[Slot; 3]) -> KResult<()> {
    if lbl == label::IRQIssueIRQHandler {
        return decode_issue_isa(s, a, length, src, buf, extra);
    }
    let remapped = lbl == label::X86IRQIssueIRQHandlerIOAPICRemapped;
    if lbl != label::X86IRQIssueIRQHandlerIOAPIC && lbl != label::X86IRQIssueIRQHandlerMSI && !remapped {
        return illegal();
    }
    let min_len = if remapped { 8 } else { 7 };
    let cnode = match extra0(s, extra) {
        Some(c) if length >= min_len => c,
        _ => return truncated(),
    };
    let ct = sched::cur_thread(s);
    let index = msg::syscall_arg(s, ct, buf, 0);
    let depth = msg::syscall_arg(s, ct, buf, 1);
    let irq = msg::syscall_arg(s, ct, buf, 6);
    if irq > irqn::USER_MAX - irqn::USER_MIN {
        return range(0, irqn::USER_MAX - irqn::USER_MIN);
    }
    let irq = irq + irqn::USER_MIN;
    if is_irq_active(s, irq) {
        return Err(Exc::Sys(SysError::RevokeFirst));
    }
    let dest = cspace::lookup_target_slot(s, cnode, index, depth)?;
    cdt::ensure_empty_slot(s, dest)?;
    if lbl == label::X86IRQIssueIRQHandlerMSI {
        check_msi(s, buf)?;
    } else {
        map_ioapic(s, a, buf, irq + irqn::INT_OFFSET, remapped)?;
    }
    invoke_irq_control(s, a, irq, dest, src);
    Ok(())
}

/// `IRQIssueIRQHandler`: ISA IRQs only through the legacy PIC
/// (`Arch_checkIRQ`).
fn decode_issue_isa<S: Store, A: Arch>(s: &mut S, a: &mut A, length: u64, src: Slot, buf: u64, extra: &[Slot; 3]) -> KResult<()> {
    let cnode = match extra0(s, extra) {
        Some(c) if length >= 3 => c,
        _ => return truncated(),
    };
    let ct = sched::cur_thread(s);
    let irq = msg::syscall_arg(s, ct, buf, 0);
    let index = msg::syscall_arg(s, ct, buf, 1);
    let depth = msg::syscall_arg(s, ct, buf, 2);
    if a.num_ioapics() != 0 {
        return illegal();
    }
    if irq > irqn::ISA_MAX {
        return range(irqn::ISA_MIN, irqn::ISA_MAX);
    }
    if is_irq_active(s, irq) {
        return Err(Exc::Sys(SysError::RevokeFirst));
    }
    let dest = cspace::lookup_target_slot(s, cnode, index, depth)?;
    cdt::ensure_empty_slot(s, dest)?;
    sched::set_thread_state(s, ct, sched::TS_RESTART);
    invoke_irq_control(s, a, irq, dest, src);
    Ok(())
}

/// The PCI address of an MSI handler; the restart that follows success.
fn check_msi<S: Store>(s: &mut S, buf: u64) -> KResult<()> {
    let ct = sched::cur_thread(s);
    let bus = msg::syscall_arg(s, ct, buf, 2);
    let dev = msg::syscall_arg(s, ct, buf, 3);
    let func = msg::syscall_arg(s, ct, buf, 4);
    if bus > PCI_BUS_MAX {
        return range(0, PCI_BUS_MAX);
    }
    if dev > PCI_DEV_MAX {
        return range(0, PCI_DEV_MAX);
    }
    if func > PCI_FUNC_MAX {
        return range(0, PCI_FUNC_MAX);
    }
    sched::set_thread_state(s, ct, sched::TS_RESTART);
    Ok(())
}

/// Check an IOAPIC pin's arguments, restart the caller and route the pin.
fn map_ioapic<S: Store, A: Arch>(s: &mut S, a: &mut A, buf: u64, vector: u64, remapped: bool) -> KResult<()> {
    let ct = sched::cur_thread(s);
    let ioapic = msg::syscall_arg(s, ct, buf, 2);
    let pin = msg::syscall_arg(s, ct, buf, 3);
    let level = msg::syscall_arg(s, ct, buf, 4);
    let polarity = msg::syscall_arg(s, ct, buf, 5);
    let n = a.num_ioapics();
    if n == 0 {
        return illegal();
    }
    if ioapic >= n {
        return range(0, n - 1);
    }
    let pins = a.ioapic_pins(ioapic);
    if pin >= pins {
        return range(0, pins.wrapping_sub(1));
    }
    if level > 1 || polarity > 1 {
        return range(0, 1);
    }
    let handle = if remapped { msg::syscall_arg(s, ct, buf, 7) } else { 0 };
    if handle >= 1 << 16 {
        return range(0, 0xffff);
    }
    sched::set_thread_state(s, ct, sched::TS_RESTART);
    if remapped {
        a.ioapic_map_remapped(ioapic, pin, level, polarity, vector, handle);
    } else {
        a.ioapic_map(ioapic, pin, level, polarity, vector);
    }
    Ok(())
}
