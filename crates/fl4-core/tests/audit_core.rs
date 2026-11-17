//! Regressions for fl4-core audit findings: the per-core debug TCB lists
//! across migration (finding 2), IRQ backend release on handler deletion
//! (finding 3b), and the hardware debug exception path (finding 8.1).

use fl4_abi::consts::object as ot;
use fl4_core::capability::{Cap, FrameSize};
use fl4_core::interrupt;
use fl4_core::layout::{cte, node, reg};
use fl4_core::machine::{Arch, Store};
use fl4_core::obj::{node_get, node_set, Sc, Slot, Tcb};
use fl4_core::{cdt, debug, objects, schedcontext, syscall};
use std::collections::BTreeMap;

#[derive(Default)]
struct Memory {
    words: BTreeMap<u64, u64>,
    cpu: u64,
}
impl Store for Memory {
    fn read(&self, a: u64) -> u64 {
        *self.words.get(&a).unwrap_or(&0)
    }
    fn write(&mut self, a: u64, v: u64) {
        self.words.insert(a, v);
    }
    fn zero(&mut self, a: u64, len: u64) {
        for i in (0..len).step_by(8) {
            self.write(a + i, 0);
        }
    }
    fn clear_free(&mut self, a: u64, len: u64) {
        self.zero(a, len);
    }
    fn ks_base(&self) -> u64 {
        0x100000
    }
    fn cur_cpu(&self) -> u64 {
        self.cpu
    }
}

#[derive(Default)]
struct Machine {
    time: u64,
    freed: Vec<u64>,
    masked: Vec<(u64, bool)>,
}
impl Arch for Machine {
    fn now(&mut self) -> u64 {
        self.time
    }
    fn set_deadline(&mut self, _: u64) {}
    fn us_to_ticks(&self, x: u64) -> u64 {
        x
    }
    fn ticks_to_us(&self, x: u64) -> u64 {
        x
    }
    fn max_us(&self) -> u64 {
        u64::MAX
    }
    fn kernel_wcet_ticks(&self) -> u64 {
        1
    }
    fn irq_pending(&mut self) -> bool {
        false
    }
    fn take_pending_irq(&mut self) -> u64 {
        u64::MAX
    }
    fn mask_irq(&mut self, irq: u64, mask: bool) {
        self.masked.push((irq, mask));
    }
    fn ack_irq(&mut self, _: u64) {}
    fn irq_free(&mut self, irq: u64) {
        self.freed.push(irq);
    }
    fn set_vspace(&mut self, _: u64, _: u64) {}
    fn invalidate_page(&mut self, _: u64, _: u64) {}
    fn invalidate_asid(&mut self, _: u64) {}
    fn invalidate_page_structures(&mut self, _: u64) {}
    fn ioapic_map(&mut self, _: u64, _: u64, _: u64, _: u64, _: u64) -> bool {
        false
    }
    fn ioapic_map_remapped(&mut self, _: u64, _: u64, _: u64, _: u64, _: u64, _: u64) -> bool {
        false
    }
    fn num_ioapics(&self) -> u64 {
        0
    }
    fn ioapic_pins(&self, _: u64) -> u64 {
        0
    }
    fn port_in(&mut self, _: u64, _: u64) -> u64 {
        0
    }
    fn port_out(&mut self, _: u64, _: u64, _: u64) {}
    fn fpu_flush(&mut self, _: u64) {}
    fn fpu_sanitise(&mut self, _: u64) {}
    fn fpu_reload(&mut self, _: u64) {}
    fn fpu_release(&mut self, _: u64) {}
    fn remote_stall(&mut self, _: u64) {}
    fn send_reschedule(&mut self, _: u64) {}
    fn putc(&mut self, _: u64) {}
    fn get_char(&mut self) -> u64 {
        0
    }
    fn halt(&mut self) {}
}

const DEBUG_TCBS: u64 = node::DEBUG_TCBS;

/// The TCBs on `cpu`'s debug list, checking its back links.
fn debug_list(s: &Memory, cpu: u64) -> Vec<u64> {
    let mut out = Vec::new();
    let mut prev = 0;
    let mut t = node_get(s, cpu, DEBUG_TCBS);
    while t != 0 {
        assert_eq!(Tcb(t).debug_prev(s), prev, "debug list of core {cpu} badly linked at {t:#x}");
        assert!(out.len() < 64, "debug list of core {cpu} does not end");
        out.push(t);
        prev = t;
        t = Tcb(t).debug_next(s);
    }
    out
}

fn thread(s: &mut Memory, a: &mut Machine, base: u64) -> Tcb {
    match objects::create_object(s, a, ot::Tcb, base, 0, false) {
        Cap::Thread { ptr } => Tcb(ptr),
        _ => unreachable!(),
    }
}

/// Finding 2: a thread created on core 0 (head of core 0's debug list) is
/// bound to an SC of core 1, then deleted; its memory is retyped. Creating
/// another thread on core 0 must not write through a stale list head into
/// the retyped object (slot 112 of a CNode, or offset 0xe00 of a user
/// frame, is where the stale head's `debug_prev` lies).
#[test]
fn migrated_thread_leaves_no_stale_head_over_a_retyped_cnode() {
    stale_head_case(false);
}

#[test]
fn migrated_thread_leaves_no_stale_head_over_a_retyped_frame() {
    stale_head_case(true);
}

fn stale_head_case(retype_as_frame: bool) {
    let mut s = Memory::default();
    let mut a = Machine::default();
    let victim_base = 0x40_0000;
    let victim = thread(&mut s, &mut a, victim_base);
    assert_eq!(debug_list(&s, 0), vec![victim_base]);

    let sc = Sc(0x50_0000);
    sc.set_cpu(&mut s, 1);
    schedcontext::bind_tcb(&mut s, &mut a, sc, victim);
    assert_eq!(victim.affinity(&s), 1);

    // Delete the thread: finalise its cap, then the untyped reset clears
    // the memory and retypes it.
    let _ = objects::finalise_cap(&mut s, &mut a, Cap::Thread { ptr: victim_base }, true, true);
    s.clear_free(victim_base, 1 << 12);
    let guarded = Cap::Endpoint { ptr: 0x60_0000, badge: 7, send: true, recv: true, grant: false, grant_reply: false };
    let slot112 = Slot(victim_base + 112 * cte::SIZE);
    assert_eq!(slot112.0, victim_base + 0xe00);
    if retype_as_frame {
        let c = objects::create_object(&mut s, &mut a, ot::X86Page4K, victim_base, 0, false);
        assert!(c == Cap::Frame { ptr: victim_base, size: FrameSize::Small, rights: 3, is_device: false, mapped: false, is_ept: false, asid: 0, vaddr: 0 });
    } else {
        let _ = objects::create_object(&mut s, &mut a, ot::CapTable, victim_base, 7, false);
        slot112.set_cap(&mut s, guarded);
    }

    let fresh_base = 0x70_0000;
    let fresh = thread(&mut s, &mut a, fresh_base);
    if retype_as_frame {
        for off in (0..(1u64 << 12)).step_by(8) {
            assert_eq!(s.read(victim_base + off), 0, "kernel wrote {:#x} into the user frame at {off:#x}", s.read(victim_base + off));
        }
    } else {
        assert!(slot112.cap(&s) == guarded, "slot 112 of the retyped CNode was overwritten");
    }
    assert_eq!(debug_list(&s, 0), vec![fresh_base]);
    assert_eq!(fresh.debug_next(&s), 0);
    assert_eq!(node_get(&s, 1, DEBUG_TCBS), 0);
}

/// Migrating to the core a thread is already on changes nothing.
#[test]
fn migrating_to_the_same_core_keeps_the_debug_list() {
    let mut s = Memory::default();
    let mut a = Machine::default();
    let t1 = thread(&mut s, &mut a, 0x40_0000);
    let t2 = thread(&mut s, &mut a, 0x41_0000);
    let sc = Sc(0x50_0000);
    schedcontext::bind_tcb(&mut s, &mut a, sc, t1);
    assert_eq!(debug_list(&s, 0), vec![t2.0, t1.0]);
    // Moving the tail, then the head, to core 1 keeps both lists linked.
    fl4_core::smp::migrate_tcb(&mut s, &mut a, t1, 1);
    assert_eq!(debug_list(&s, 0), vec![t2.0]);
    assert_eq!(debug_list(&s, 1), vec![t1.0]);
    fl4_core::smp::migrate_tcb(&mut s, &mut a, t2, 1);
    assert_eq!(debug_list(&s, 0), Vec::<u64>::new());
    assert_eq!(debug_list(&s, 1), vec![t2.0, t1.0]);
}

/// Finding 3b: deleting an IRQHandler cap releases the backend's routing
/// for that IRQ exactly once.
#[test]
fn deleting_an_irq_handler_frees_the_irq() {
    let mut s = Memory::default();
    let mut a = Machine::default();
    let irq = 5;
    interrupt::set_irq_state(&mut s, &mut a, interrupt::IRQ_SIGNAL, irq);
    let slot = Slot(0x40_0000);
    slot.set_cap(&mut s, Cap::IrqHandler { irq });
    cdt::delete(&mut s, &mut a, slot, true).ok().expect("delete");
    assert!(slot.cap(&s).is_null());
    assert_eq!(interrupt::irq_state(&s, irq), interrupt::IRQ_INACTIVE);
    assert_eq!(a.masked.last(), Some(&(irq, true)));
    assert_eq!(a.freed, vec![irq]);
}

const DR6_SINGLE_STEP: u64 = 1 << 14;
const EFLAGS_TF: u64 = 1 << 8;
const EFLAGS_RF: u64 = 1 << 16;
const SS_ENABLED: u64 = 6;
const SS_COUNT: u64 = 7;

/// Finding 8.1: a single step the user asked for with RFLAGS.TF itself
/// (the debug API's single step off) is reported once: TF is cleared.
#[test]
fn user_trap_flag_single_step_clears_tf() {
    let mut s = Memory::default();
    let t = Tcb(0x40_0000);
    t.set_reg(&mut s, reg::FLAGS, EFLAGS_TF | 0x202);
    t.set_reg(&mut s, reg::FAULT_IP, 0x1234);
    let f = debug::debug_exception(&mut s, t, 1, DR6_SINGLE_STEP);
    assert!(f.is_some());
    assert_eq!(t.reg(&s, reg::FLAGS), 0x202 | EFLAGS_RF);

    // With the debug API's single step on, TF stays for the next step.
    t.set_debug_reg(&mut s, SS_ENABLED, 1);
    t.set_reg(&mut s, reg::FLAGS, EFLAGS_TF | 0x202);
    let _ = debug::debug_exception(&mut s, t, 1, DR6_SINGLE_STEP);
    assert_eq!(t.reg(&s, reg::FLAGS), EFLAGS_TF | 0x202 | EFLAGS_RF);
}

/// Finding 8.1: a #DB that delivers no fault (a multi-step not run out)
/// still charges the time the thread ran.
#[test]
fn pending_single_step_still_charges_time() {
    let mut s = Memory::default();
    let mut a = Machine::default();
    let t = Tcb(0x40_0000);
    let sc = Sc(0x50_0000);
    node_set(&mut s, 0, node::CUR_THREAD, t.0);
    node_set(&mut s, 0, node::CUR_SC, sc.0);
    node_set(&mut s, 0, node::CUR_TIME, 100);
    t.set_sc(&mut s, sc.0);
    sc.set_tcb(&mut s, t.0);
    t.set_debug_reg(&mut s, SS_ENABLED, 1);
    t.set_debug_reg(&mut s, SS_COUNT, 3);
    a.time = 150;
    syscall::handle_debug_exception(&mut s, &mut a, 1, DR6_SINGLE_STEP);
    assert_eq!(t.debug_reg(&s, SS_COUNT), 2, "the step was counted");
    assert_eq!(node_get(&s, 0, node::CUR_TIME), 150, "the timestamp was not updated");
    // The SC has no budget left, so the 50 ticks are charged to it.
    assert_eq!(sc.consumed(&s), 50, "the time was not charged");
}
