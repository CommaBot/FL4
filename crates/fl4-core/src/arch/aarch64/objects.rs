/// seL4 `getObjectSize` (AArch64), or None for an invalid type.
pub fn object_size(t: u64, user_size: u64) -> Option<u64> {
    if t == ot::Tcb {
        Some(bits::TCB)
    } else if t == ot::Endpoint {
        Some(bits::ENDPOINT)
    } else if t == ot::Notification {
        Some(bits::NOTIFICATION)
    } else if t == ot::CapTable {
        Some(bits::SLOT.wrapping_add(user_size))
    } else if t == ot::Untyped || t == ot::SchedContext {
        Some(user_size)
    } else if t == ot::Reply {
        Some(bits::REPLY)
    } else if t == ot::ArmSmallPage {
        Some(12)
    } else if t == ot::ArmLargePage {
        Some(21)
    } else if t == ot::ArmHugePage {
        Some(30)
    } else if t == ot::ArmPageTable || t == ot::ArmVSpace {
        Some(12)
    } else {
        None
    }
}

pub fn is_frame_type(t: u64) -> bool {
    t == ot::ArmSmallPage || t == ot::ArmLargePage || t == ot::ArmHugePage
}

/// AArch64: the initial FP/SIMD state is all zero, as the memory is.
fn init_fpu<S: Store>(s: &mut S, t: Tcb) {
    let _ = (s, t);
}

/// seL4 `Arch_createObject` (AArch64): VSpaces are `Cap::Pml4`, page
/// tables of every level `Cap::PageTable`.
fn create_arch_object<S: Store, A: Arch>(_s: &mut S, _a: &mut A, t: u64, base: u64, device: bool) -> Cap {
    if t == ot::ArmPageTable {
        Cap::PageTable { ptr: base, mapped: false, asid: 0, vaddr: 0 }
    } else if t == ot::ArmVSpace {
        Cap::Pml4 { ptr: base, mapped: false, asid: 0 }
    } else {
        let size = if t == ot::ArmSmallPage {
            FrameSize::Small
        } else if t == ot::ArmLargePage {
            FrameSize::Large
        } else {
            FrameSize::Huge
        };
        Cap::Frame { ptr: base, size, rights: VM_READ_WRITE, is_device: device, mapped: false, is_ept: false, asid: 0, vaddr: 0 }
    }
}
