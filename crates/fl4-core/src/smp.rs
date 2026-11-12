//! Cross-core operations. Until the SMP milestone (M3) FL4 runs on one
//! core, and these are the single-core behaviour seL4 has without
//! ENABLE_SMP_SUPPORT.

use crate::machine::{Arch, Store};
use crate::obj::Tcb;

/// seL4 `migrateTCB`: move a thread to the core of its new SC.
pub fn migrate_tcb<S: Store, A: Arch>(s: &mut S, a: &mut A, t: Tcb, core: u64) {
    let _ = a;
    t.set_affinity(s, core);
}

/// seL4 `remoteTCBStall`.
pub fn remote_tcb_stall<S: Store, A: Arch>(s: &mut S, a: &mut A, t: Tcb) {
    let _ = (s, a, t);
}

/// Ask `core` to reschedule (and reprogram its timer).
pub fn remote_reschedule<S: Store, A: Arch>(s: &mut S, a: &mut A, core: u64) {
    let _ = (s, a, core);
}

pub fn handle_ipi<S: Store, A: Arch>(s: &mut S, a: &mut A, irq: u64) {
    let _ = (s, a, irq);
}
