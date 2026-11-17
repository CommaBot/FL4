/// seL4 `getObjectSize`, or None for an invalid type.
pub fn object_size(t: u64, user_size: u64) -> Option<u64> {
    if t == ot::X86Vcpu {
        Some(bits::VCPU)
    } else if t >= ot::X86EptPml4 && t <= ot::X86EptPt {
        Some(12)
    } else if t == ot::Tcb {
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
    } else if t == ot::X86Page4K {
        Some(12)
    } else if t == ot::X86LargePage {
        Some(21)
    } else if t == ot::X64HugePage {
        Some(30)
    } else if t == ot::X86PageTable || t == ot::X86PageDirectory || t == ot::X86Pdpt || t == ot::X64Pml4 {
        Some(12)
    } else {
        None
    }
}

pub fn is_frame_type(t: u64) -> bool {
    t == ot::X86Page4K || t == ot::X86LargePage || t == ot::X64HugePage
}

/// Initial FPU image of a new thread: x87 control word 0x37f and MXCSR
/// 0x1f80, everything else in its initial state (XSTATE_BV = 0).
fn init_fpu<S: Store>(s: &mut S, t: Tcb) {
    let f = t.fpu_addr();
    s.write(f, 0x037f);
    s.write(f.wrapping_add(24), 0x0000_ffff_0000_1f80);
}

fn create_arch_object<S: Store, A: Arch>(s: &mut S, a: &mut A, t: u64, base: u64, device: bool) -> Cap {
    if t == ot::X86Vcpu {
        crate::vcpu::init(s, a, base);
        Cap::Vcpu { ptr: base }
    } else if t >= ot::X86EptPml4 && t <= ot::X86EptPt {
        let level = if t == ot::X86EptPml4 { 0 } else if t == ot::X86EptPdpt { 39 } else if t == ot::X86EptPd { 30 } else { 21 };
        Cap::Ept { ptr: base, level, mapped: false, asid: 0, vaddr: 0 }
    } else if t == ot::X86Page4K || t == ot::X86LargePage || t == ot::X64HugePage {
        let size = if t == ot::X86Page4K {
            FrameSize::Small
        } else if t == ot::X86LargePage {
            FrameSize::Large
        } else {
            FrameSize::Huge
        };
        Cap::Frame { ptr: base, size, rights: VM_READ_WRITE, is_device: device, mapped: false, is_ept: false, asid: 0, vaddr: 0 }
    } else if t == ot::X86PageTable {
        Cap::PageTable { ptr: base, mapped: false, asid: 0, vaddr: 0 }
    } else if t == ot::X86PageDirectory {
        Cap::PageDirectory { ptr: base, mapped: false, asid: 0, vaddr: 0 }
    } else if t == ot::X86Pdpt {
        Cap::Pdpt { ptr: base, mapped: false, asid: 0, vaddr: 0 }
    } else {
        // X64Pml4
        vspace::copy_global_mappings(s, base);
        Cap::Pml4 { ptr: base, mapped: false, asid: 0 }
    }
}
