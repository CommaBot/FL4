//! Untyped_Retype (seL4 object/untyped.c). Free indices are byte offsets.

use crate::capability::Cap;
use crate::cdt;
use crate::cspace;
use crate::error::{illegal, invalid_arg, range, truncated, Exc, KResult, LookupFault, SysError};
use crate::machine::{Arch, Store};
use crate::msg;
use crate::obj::Slot;
use crate::objects;
use crate::sched;
use fl4_abi::consts::{bits, object as ot};
use fl4_abi::label;

pub const RETYPE_FAN_OUT_LIMIT: u64 = 256;
/// KernelResetChunkBits, fixed at 16 (l4h 0030).
pub const RESET_CHUNK_BITS: u64 = 16;

fn align_up(v: u64, align: u64) -> u64 {
    let m = (1u64 << (align & 63)).wrapping_sub(1);
    v.wrapping_add(m) & !m
}

/// seL4 `decodeUntypedInvocation`.
pub fn decode<S: Store, A: Arch>(s: &mut S, a: &mut A, lbl: u64, length: u64, slot: Slot, cap: Cap, buf: u64, extra: &[Slot; 3]) -> KResult<()> {
    if lbl != label::UntypedRetype {
        return illegal();
    }
    if length < 6 || extra[0].is_null() {
        return truncated();
    }
    let ct = sched::cur_thread(s);
    let new_type = msg::syscall_arg(s, ct, buf, 0);
    let user_size = msg::syscall_arg(s, ct, buf, 1);
    let node_index = msg::syscall_arg(s, ct, buf, 2);
    let node_depth = msg::syscall_arg(s, ct, buf, 3);
    let node_offset = msg::syscall_arg(s, ct, buf, 4);
    let node_window = msg::syscall_arg(s, ct, buf, 5);
    let root_slot = extra[0];
    if new_type >= ot::Count {
        return invalid_arg(0);
    }
    let obj_size = match objects::object_size(new_type, user_size) {
        Some(z) => z,
        None => return invalid_arg(0),
    };
    if user_size >= 64 || obj_size > bits::MAX_UNTYPED {
        return range(0, bits::MAX_UNTYPED);
    }
    if new_type == ot::CapTable && user_size == 0 {
        return invalid_arg(1);
    }
    if new_type == ot::Untyped && user_size < bits::MIN_UNTYPED {
        return invalid_arg(1);
    }
    if new_type == ot::SchedContext && user_size < bits::MIN_SCHED_CONTEXT {
        return invalid_arg(1);
    }
    let node_cap = if node_depth == 0 {
        root_slot.cap(s)
    } else {
        let root = root_slot.cap(s);
        cspace::lookup_target_slot(s, root, node_index, node_depth)?.cap(s)
    };
    let (dest, radix) = match node_cap {
        Cap::CNode { ptr, radix, .. } => (ptr, radix),
        _ => {
            return Err(Exc::Sys(SysError::FailedLookup {
                source: false,
                lf: LookupFault::MissingCapability { bits_left: node_depth },
            }))
        }
    };
    let node_size = 1u64 << (radix & 63);
    if node_offset > node_size - 1 {
        return range(0, node_size - 1);
    }
    if node_window < 1 || node_window > RETYPE_FAN_OUT_LIMIT {
        return range(1, RETYPE_FAN_OUT_LIMIT);
    }
    if node_window > node_size - node_offset {
        return range(1, node_size - node_offset);
    }
    ensure_empty_slots(s, dest, node_offset, node_offset + node_window)?;
    let (ptr, block, free_index, device) = match cap {
        Cap::Untyped { ptr, size_bits, free_index, is_device } => (ptr, size_bits, free_index, is_device),
        _ => return illegal(),
    };
    let (free_index, reset) = match cdt::ensure_no_children(s, slot) {
        Err(_) => (free_index, false),
        Ok(()) => (0, true),
    };
    let free_ref = ptr.wrapping_add(free_index);
    let free_bytes = (1u64 << (block & 63)).wrapping_sub(free_index);
    if (free_bytes >> (obj_size & 63)) < node_window || obj_size >= 64 {
        return Err(Exc::Sys(SysError::NotEnoughMemory { bytes: free_bytes }));
    }
    if device && !objects::is_frame_type(new_type) && new_type != ot::Untyped {
        return invalid_arg(1);
    }
    let aligned = align_up(free_ref, obj_size);
    sched::set_thread_state(s, ct, sched::TS_RESTART);
    retype(s, a, slot, reset, aligned, new_type, user_size, dest, node_offset, node_window, device)
}

/// Every slot of `cnode` in [from, to) is empty. (The loop has no early
/// exit, which Aeneas cannot translate yet.)
fn ensure_empty_slots<S: Store>(s: &S, cnode: u64, from: u64, to: u64) -> KResult<()> {
    let mut r = Ok(());
    let mut i = from;
    while i < to && r.is_ok() {
        r = cdt::ensure_empty_slot(s, Slot::index(cnode, i));
        i += 1;
    }
    r
}

/// seL4 `resetUntypedCap`: clear the used part, top down, in chunks.
fn reset_untyped<S: Store, A: Arch>(s: &mut S, a: &mut A, slot: Slot) -> KResult<()> {
    let (ptr, block, free_index, device) = match slot.cap(s) {
        Cap::Untyped { ptr, size_bits, free_index, is_device } => (ptr, size_bits, free_index, is_device),
        _ => return Ok(()),
    };
    if free_index == 0 {
        return Ok(());
    }
    if device || block < RESET_CHUNK_BITS {
        if !device {
            s.zero(ptr, 1u64 << (block & 63));
        }
        slot.set_cap(s, Cap::Untyped { ptr, size_bits: block, free_index: 0, is_device: device });
        return Ok(());
    }
    let chunk = 1u64 << RESET_CHUNK_BITS;
    let mut offset = (free_index - 1) & !(chunk - 1);
    loop {
        s.zero(ptr.wrapping_add(offset), chunk);
        slot.set_cap(s, Cap::Untyped { ptr, size_bits: block, free_index: offset, is_device: device });
        if offset == 0 {
            return Ok(());
        }
        sched::preemption_point(s, a)?;
        // `offset` is a nonzero multiple of `chunk` here.
        offset = offset.saturating_sub(chunk);
    }
}

#[allow(clippy::too_many_arguments)]
fn retype<S: Store, A: Arch>(
    s: &mut S,
    a: &mut A,
    slot: Slot,
    reset: bool,
    base: u64,
    new_type: u64,
    user_size: u64,
    dest: u64,
    offset: u64,
    length: u64,
    device: bool,
) -> KResult<()> {
    if reset {
        reset_untyped(s, a, slot)?;
    }
    let size = objects::object_size(new_type, user_size).unwrap_or(0);
    let total = length << (size & 63);
    if let Cap::Untyped { ptr, size_bits, is_device, .. } = slot.cap(s) {
        let free_ref = base.wrapping_add(total);
        slot.set_cap(s, Cap::Untyped { ptr, size_bits, free_index: free_ref.wrapping_sub(ptr), is_device });
    }
    objects::create_new_objects(s, a, new_type, slot, dest, offset, length, base, user_size, device);
    Ok(())
}
