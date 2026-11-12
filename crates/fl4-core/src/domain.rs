//! The domain capability (seL4 object/domain.c, with the runtime domain
//! schedule of seL4 17.0).

use crate::capability::Cap;
use crate::error::{illegal, invalid_arg, range, truncated, KResult};
use crate::layout::{ks, NUM_DOMAINS, NUM_DOMAIN_SCHEDULES};
use crate::machine::Store;
use crate::msg;
use crate::obj::{ks_get, ks_set, Slot, Tcb};
use crate::sched;
use fl4_abi::label;

/// Durations are timer ticks and must fit in 56 bits.
const MAX_DURATION: u64 = (1 << 56) - 1;

pub fn decode<S: Store>(s: &mut S, lbl: u64, length: u64, buf: u64, extra: &[Slot; 3]) -> KResult<()> {
    let ct = sched::cur_thread(s);
    if lbl == label::DomainSetSet {
        if length == 0 {
            return truncated();
        }
        let dom = msg::syscall_arg(s, ct, buf, 0);
        if dom >= NUM_DOMAINS {
            return invalid_arg(0);
        }
        if extra[0].is_null() {
            return truncated();
        }
        let t = match extra[0].cap(s) {
            Cap::Thread { ptr } => Tcb(ptr),
            _ => return invalid_arg(1),
        };
        sched::set_thread_state(s, ct, sched::TS_RESTART);
        sched::set_domain(s, t, dom);
        Ok(())
    } else if lbl == label::DomainScheduleConfigure {
        if length < 3 {
            return truncated();
        }
        let index = msg::syscall_arg(s, ct, buf, 0);
        let dom = msg::syscall_arg(s, ct, buf, 1);
        let duration = msg::syscall_arg(s, ct, buf, 2);
        if index >= NUM_DOMAIN_SCHEDULES - 1 {
            return range(0, NUM_DOMAIN_SCHEDULES - 2);
        }
        if dom >= NUM_DOMAINS {
            return range(0, NUM_DOMAINS - 1);
        }
        if duration > MAX_DURATION {
            return invalid_arg(2);
        }
        if duration == 0 && dom != 0 {
            return invalid_arg(1);
        }
        if index == ks_get(s, ks::DOM_SCHED_START) && duration == 0 {
            return invalid_arg(2);
        }
        sched::set_thread_state(s, ct, sched::TS_RESTART);
        sched::set_dom_sched(s, index, dom, duration);
        Ok(())
    } else if lbl == label::DomainScheduleSetStart {
        if length < 1 {
            return truncated();
        }
        let index = msg::syscall_arg(s, ct, buf, 0);
        if index >= NUM_DOMAIN_SCHEDULES {
            return range(0, NUM_DOMAIN_SCHEDULES - 1);
        }
        if sched::dom_sched_duration(s, index) == 0 {
            return invalid_arg(0);
        }
        sched::set_thread_state(s, ct, sched::TS_RESTART);
        ks_set(s, ks::DOM_SCHED_START, index);
        ks_set(s, ks::DOMAIN_TIME, 0);
        ks_set(s, ks::DOM_SCHED_IDX, NUM_DOMAIN_SCHEDULES - 2);
        sched::reschedule_required(s);
        Ok(())
    } else {
        illegal()
    }
}
