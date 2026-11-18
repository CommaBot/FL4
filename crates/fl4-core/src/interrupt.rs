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

arch_items!("interrupt.rs");

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
    a.irq_free(irq);
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
