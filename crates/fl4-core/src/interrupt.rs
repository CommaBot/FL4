//! IRQControl, IRQHandler and interrupt delivery (seL4 object/interrupt.c,
//! arch/x86/object/interrupt.c, l4h 0025).

use crate::capability::Cap;
use crate::cdt;
use crate::cspace;
use crate::error::{illegal, invalid_cap, range, truncated, Exc, KResult, SysError};
use crate::layout::{ks, irq as irqn, node};
use crate::machine::{Arch, Store};
use crate::msg;
use crate::notification;
use crate::obj::{ks_get, ks_set, node_set, Slot};
use crate::sched;
use fl4_abi::label;

pub const IRQ_INACTIVE: u64 = 0;
pub const IRQ_SIGNAL: u64 = 1;
pub const IRQ_TIMER: u64 = 2;
pub const IRQ_IPI: u64 = 3;
pub const IRQ_RESERVED: u64 = 4;

pub const PCI_BUS_MAX: u64 = 255;
pub const PCI_DEV_MAX: u64 = 31;
pub const PCI_FUNC_MAX: u64 = 7;

fn state_off(irq: u64) -> u64 {
    ks::IRQ_STATE.wrapping_add(irq.wrapping_mul(8))
}

pub fn irq_slot<S: Store>(s: &S, irq: u64) -> Slot {
    Slot(s.ks_base().wrapping_add(ks::IRQ_NODE).wrapping_add(irq.wrapping_mul(crate::layout::cte::SIZE)))
}

pub fn irq_state<S: Store>(s: &S, irq: u64) -> u64 {
    ks_get(s, state_off(irq))
}

pub fn is_irq_active<S: Store>(s: &S, irq: u64) -> bool {
    irq_state(s, irq) != IRQ_INACTIVE
}

/// seL4 `setIRQState`.
pub fn set_irq_state<S: Store, A: Arch>(s: &mut S, a: &mut A, st: u64, irq: u64) {
    ks_set(s, state_off(irq), st);
    a.mask_irq(irq, st == IRQ_INACTIVE);
}

fn invoke_irq_control<S: Store, A: Arch>(s: &mut S, a: &mut A, irq: u64, handler: Slot, control: Slot) {
    set_irq_state(s, a, IRQ_SIGNAL, irq);
    cdt::insert(s, Cap::IrqHandler { irq }, control, handler);
}

fn extra0<S: Store>(s: &S, extra: &[Slot; 3]) -> Option<Cap> {
    if extra[0].is_null() {
        None
    } else {
        Some(extra[0].cap(s))
    }
}

/// seL4 `decodeIRQControlInvocation` with the x86 arch part.
pub fn decode_irq_control<S: Store, A: Arch>(s: &mut S, a: &mut A, lbl: u64, length: u64, src: Slot, buf: u64, extra: &[Slot; 3]) -> KResult<()> {
    let ct = sched::cur_thread(s);
    if lbl == label::IRQIssueIRQHandler {
        let cnode = match extra0(s, extra) {
            Some(c) if length >= 3 => c,
            _ => return truncated(),
        };
        let irq = msg::syscall_arg(s, ct, buf, 0);
        let index = msg::syscall_arg(s, ct, buf, 1);
        let depth = msg::syscall_arg(s, ct, buf, 2);
        // Arch_checkIRQ: ISA IRQs only through the legacy PIC.
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
        return Ok(());
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
    let index = msg::syscall_arg(s, ct, buf, 0);
    let depth = msg::syscall_arg(s, ct, buf, 1);
    let mut irq = msg::syscall_arg(s, ct, buf, 6);
    if irq > irqn::USER_MAX - irqn::USER_MIN {
        return range(0, irqn::USER_MAX - irqn::USER_MIN);
    }
    irq += irqn::USER_MIN;
    if is_irq_active(s, irq) {
        return Err(Exc::Sys(SysError::RevokeFirst));
    }
    let vector = irq + irqn::INT_OFFSET;
    let dest = cspace::lookup_target_slot(s, cnode, index, depth)?;
    cdt::ensure_empty_slot(s, dest)?;
    if lbl == label::X86IRQIssueIRQHandlerMSI {
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
        invoke_irq_control(s, a, irq, dest, src);
        return Ok(());
    }
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
    invoke_irq_control(s, a, irq, dest, src);
    Ok(())
}

/// seL4 `decodeIRQHandlerInvocation`.
pub fn decode_irq_handler<S: Store, A: Arch>(s: &mut S, a: &mut A, lbl: u64, irq: u64, extra: &[Slot; 3]) -> KResult<()> {
    let ct = sched::cur_thread(s);
    if lbl == label::IRQAckIRQ {
        sched::set_thread_state(s, ct, sched::TS_RESTART);
        a.mask_irq(irq, false);
        Ok(())
    } else if lbl == label::IRQSetIRQHandler {
        let slot = extra[0];
        if slot.is_null() {
            return truncated();
        }
        let cap = slot.cap(s);
        match cap {
            Cap::Notification { send: true, .. } => {}
            _ => return invalid_cap(0),
        }
        sched::set_thread_state(s, ct, sched::TS_RESTART);
        let isl = irq_slot(s, irq);
        cdt::delete_one(s, a, isl);
        cdt::insert(s, cap, slot, isl);
        Ok(())
    } else if lbl == label::IRQClearIRQHandler {
        sched::set_thread_state(s, ct, sched::TS_RESTART);
        let isl = irq_slot(s, irq);
        cdt::delete_one(s, a, isl);
        Ok(())
    } else {
        illegal()
    }
}

pub fn deleting_irq_handler<S: Store, A: Arch>(s: &mut S, a: &mut A, irq: u64) {
    let isl = irq_slot(s, irq);
    cdt::delete_one(s, a, isl);
}

pub fn deleted_irq_handler<S: Store, A: Arch>(s: &mut S, a: &mut A, irq: u64) {
    set_irq_state(s, a, IRQ_INACTIVE, irq);
}

/// seL4 `handleInterrupt`.
pub fn handle_interrupt<S: Store, A: Arch>(s: &mut S, a: &mut A, irq: u64) {
    if irq > irqn::MAX {
        a.mask_irq(irq, true);
        a.ack_irq(irq);
        return;
    }
    let st = irq_state(s, irq);
    if st == IRQ_SIGNAL {
        if let Cap::Notification { ptr, badge, send: true, .. } = irq_slot(s, irq).cap(s) {
            notification::send_signal(s, a, ptr, badge);
        }
        a.mask_irq(irq, true);
    } else if st == IRQ_TIMER {
        let c = s.cur_cpu();
        node_set(s, c, node::REPROGRAM, 1);
        // l4h 0006: the hardware timer is no longer armed.
        node_set(s, c, node::ARMED, 0);
    } else if st == IRQ_IPI {
        crate::smp::handle_ipi(s, a, irq);
    } else if st == IRQ_INACTIVE {
        a.mask_irq(irq, true);
    }
    a.ack_irq(irq);
}
