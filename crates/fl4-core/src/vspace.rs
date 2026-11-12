//! x86_64 virtual memory: page-table objects, frames, ASIDs and VM faults
//! (seL4 arch/x86/kernel/vspace.c and arch/x86/64/kernel/vspace.c), with
//! l4h's ExecuteNever (0009), DeferFlush and PML4_Flush (0017),
//! TestAndClearAccessed (0023) and DeriveSubframe (0029).

use crate::cap::{mask_vm_rights, Cap, FrameSize, Rights, VM_KERNEL_ONLY, VM_READ_ONLY};
use crate::cdt;
use crate::cspace;
use crate::error::{illegal, invalid_arg, invalid_cap, range, truncated, Exc, KResult, LookupFault, SysError};
use crate::layout::{self, ks, tcb as tl};
use crate::machine::{Arch, Store};
use crate::msg;
use crate::msginfo::MessageInfo;
use crate::obj::{ks_get, ks_set, Slot, Tcb};
use crate::sched;
use fl4_abi::consts::{bits, vm_attr, USER_TOP};
use fl4_abi::label;

const P_PRESENT: u64 = 1 << 0;
const P_RW: u64 = 1 << 1;
const P_US: u64 = 1 << 2;
const P_PWT: u64 = 1 << 3;
const P_PCD: u64 = 1 << 4;
const P_ACCESSED: u64 = 1 << 5;
const P_PS: u64 = 1 << 7;
const P_PAT_4K: u64 = 1 << 7;
const P_PAT_LARGE: u64 = 1 << 12;
const P_XD: u64 = 1 << 63;
const ADDR_MASK: u64 = 0x000f_ffff_ffff_f000;

pub const ASID_LOW_BITS: u64 = 9;
pub const N_ASID_POOLS: u64 = 8;

const PML4_INDEX_OFFSET: u64 = 39;
const PDPT_INDEX_OFFSET: u64 = 30;
const PD_INDEX_OFFSET: u64 = 21;

/// Whether the CPU enforces execute-disable; kept by the backend in the
/// global state at boot (DESIGN.md §3, EFER.NXE).
fn nx_enabled<S: Store>(s: &S) -> bool {
    ks_get(s, ks::FEATURES) & ks::FEATURE_NX != 0
}

fn entry<S: Store>(s: &S, table: u64, i: u64) -> u64 {
    s.read(table.wrapping_add((i & 511).wrapping_mul(8)))
}

fn entry_addr(table: u64, i: u64) -> u64 {
    table.wrapping_add((i & 511).wrapping_mul(8))
}

fn idx(vaddr: u64, shift: u64) -> u64 {
    (vaddr >> shift) & 511
}

fn table_of(e: u64) -> u64 {
    layout::pptr(e & ADDR_MASK)
}

// ---- entries ---------------------------------------------------------------

fn writable(rights: u64) -> u64 {
    if rights == VM_READ_ONLY {
        0
    } else {
        P_RW
    }
}

fn super_user(rights: u64) -> u64 {
    if rights == VM_KERNEL_ONLY {
        0
    } else {
        P_US
    }
}

fn attr_bits(attr: u64, pat: u64) -> u64 {
    (if attr & 1 != 0 { P_PWT } else { 0 })
        | (if attr & 2 != 0 { P_PCD } else { 0 })
        | (if attr & 4 != 0 { pat } else { 0 })
}

fn xd_bit<S: Store>(s: &S, attr: u64) -> u64 {
    if attr & vm_attr::EXECUTE_NEVER != 0 && nx_enabled(s) {
        P_XD
    } else {
        0
    }
}

fn make_user_page<S: Store>(s: &S, paddr: u64, attr: u64, rights: u64, large: bool) -> u64 {
    let pat = if large { P_PAT_LARGE } else { P_PAT_4K };
    (paddr & ADDR_MASK)
        | attr_bits(attr, pat)
        | super_user(rights)
        | writable(rights)
        | P_PRESENT
        | (if large { P_PS } else { 0 })
        | xd_bit(s, attr)
}

fn make_user_table(paddr: u64, attr: u64) -> u64 {
    (paddr & ADDR_MASK) | attr_bits(attr, 0) | P_US | P_RW | P_PRESENT
}

// ---- lookups ---------------------------------------------------------------

/// The PDPT entry address for `vaddr`, if its PML4 entry is present.
fn lookup_pdpt_slot<S: Store>(s: &S, pml4: u64, vaddr: u64) -> Result<u64, LookupFault> {
    let e = entry(s, pml4, idx(vaddr, 39));
    if e & P_PRESENT == 0 {
        return Err(LookupFault::MissingCapability { bits_left: PML4_INDEX_OFFSET });
    }
    Ok(entry_addr(table_of(e), idx(vaddr, 30)))
}

fn lookup_pd_slot<S: Store>(s: &S, pml4: u64, vaddr: u64) -> Result<u64, LookupFault> {
    let pdpte_addr = lookup_pdpt_slot(s, pml4, vaddr)?;
    let e = s.read(pdpte_addr);
    if e & P_PRESENT == 0 || e & P_PS != 0 {
        return Err(LookupFault::MissingCapability { bits_left: PDPT_INDEX_OFFSET });
    }
    Ok(entry_addr(table_of(e), idx(vaddr, 21)))
}

fn lookup_pt_slot<S: Store>(s: &S, pml4: u64, vaddr: u64) -> Result<u64, LookupFault> {
    let pde_addr = lookup_pd_slot(s, pml4, vaddr)?;
    let e = s.read(pde_addr);
    if e & P_PRESENT == 0 || e & P_PS != 0 {
        return Err(LookupFault::MissingCapability { bits_left: PD_INDEX_OFFSET });
    }
    Ok(entry_addr(table_of(e), idx(vaddr, 12)))
}

fn asid_table<S: Store>(s: &S, high: u64) -> u64 {
    ks_get(s, ks::ASID_TABLE.wrapping_add((high & 7).wrapping_mul(8)))
}

fn set_asid_table<S: Store>(s: &mut S, high: u64, pool: u64) {
    ks_set(s, ks::ASID_TABLE.wrapping_add((high & 7).wrapping_mul(8)), pool)
}

/// seL4 `findVSpaceForASID`: the PML4 assigned to `asid`.
pub fn find_vspace_for_asid<S: Store>(s: &S, asid: u64) -> Result<u64, LookupFault> {
    let pool = asid_table(s, asid >> ASID_LOW_BITS);
    if pool == 0 {
        return Err(LookupFault::InvalidRoot);
    }
    let root = s.read(pool.wrapping_add((asid & 511).wrapping_mul(8)));
    if root == 0 {
        return Err(LookupFault::InvalidRoot);
    }
    Ok(root)
}

pub fn is_valid_vtable_root(c: Cap) -> bool {
    matches!(c, Cap::Pml4 { mapped: true, .. })
}

/// x86 `checkValidIPCBuffer`.
pub fn check_valid_ipc_buffer(vptr: u64, c: Cap) -> KResult<()> {
    match c {
        Cap::Frame { is_device, .. } => {
            if is_device {
                return illegal();
            }
        }
        _ => return illegal(),
    }
    if vptr & ((1u64 << bits::IPC_BUFFER) - 1) != 0 {
        return Err(Exc::Sys(SysError::AlignmentError));
    }
    Ok(())
}

// ---- address-space switch ----------------------------------------------------

/// The kernel's own top-level table (no user mappings).
pub fn kernel_root<S: Store>(s: &S) -> u64 {
    ks_get(s, ks::KERNEL_ROOT)
}

/// seL4 `setVMRoot`.
pub fn set_vm_root<S: Store, A: Arch>(s: &mut S, a: &mut A, t: Tcb) {
    match t.slot(tl::SLOT_VTABLE).cap(s) {
        Cap::Pml4 { ptr, mapped: true, asid } => match find_vspace_for_asid(s, asid) {
            Ok(r) if r == ptr => a.set_vspace(ptr, asid),
            _ => set_kernel_vm_root(s, a),
        },
        _ => set_kernel_vm_root(s, a),
    }
}

pub fn set_kernel_vm_root<S: Store, A: Arch>(s: &mut S, a: &mut A) {
    let k = kernel_root(s);
    a.set_vspace(k, 0);
}

/// seL4 `copyGlobalMappings`: the kernel half of every address space.
pub fn copy_global_mappings<S: Store>(s: &mut S, new_root: u64) {
    let k = kernel_root(s);
    let mut i = 256;
    while i < 512 {
        let v = entry(s, k, i);
        s.write(entry_addr(new_root, i), v);
        i += 1;
    }
}

// ---- unmapping ---------------------------------------------------------------

/// seL4 `unmapPage`.
pub fn unmap_page<S: Store, A: Arch>(s: &mut S, a: &mut A, size: FrameSize, asid: u64, vaddr: u64, pptr: u64) {
    let root = match find_vspace_for_asid(s, asid) {
        Ok(r) => r,
        Err(_) => return,
    };
    let pa = layout::paddr(pptr);
    let slot = match size {
        FrameSize::Small => match lookup_pt_slot(s, root, vaddr) {
            Ok(x) => x,
            Err(_) => return,
        },
        FrameSize::Large => match lookup_pd_slot(s, root, vaddr) {
            Ok(x) => x,
            Err(_) => return,
        },
        FrameSize::Huge => match lookup_pdpt_slot(s, root, vaddr) {
            Ok(x) => x,
            Err(_) => return,
        },
    };
    let e = s.read(slot);
    let need_ps = !matches!(size, FrameSize::Small);
    if e & P_PRESENT == 0 || (e & ADDR_MASK) != pa || ((e & P_PS != 0) != need_ps) {
        return;
    }
    s.write(slot, 0);
    a.invalidate_page(asid, vaddr);
}

/// seL4 `unmapPageTable`.
pub fn unmap_page_table<S: Store, A: Arch>(s: &mut S, a: &mut A, asid: u64, vaddr: u64, pt: u64) {
    let root = match find_vspace_for_asid(s, asid) {
        Ok(r) => r,
        Err(_) => return,
    };
    let slot = match lookup_pd_slot(s, root, vaddr) {
        Ok(x) => x,
        Err(_) => return,
    };
    let e = s.read(slot);
    if e & P_PRESENT == 0 || e & P_PS != 0 || (e & ADDR_MASK) != layout::paddr(pt) {
        return;
    }
    // flushTable: drop translations of the pages this table maps.
    a.invalidate_asid(asid);
    s.write(slot, 0);
    a.invalidate_page_structures(asid);
}

/// seL4 `unmapPageDirectory`.
pub fn unmap_page_directory<S: Store, A: Arch>(s: &mut S, a: &mut A, asid: u64, vaddr: u64, pd: u64) {
    let root = match find_vspace_for_asid(s, asid) {
        Ok(r) => r,
        Err(_) => return,
    };
    let slot = match lookup_pdpt_slot(s, root, vaddr) {
        Ok(x) => x,
        Err(_) => return,
    };
    let e = s.read(slot);
    if e & P_PRESENT == 0 || e & P_PS != 0 || (e & ADDR_MASK) != layout::paddr(pd) {
        return;
    }
    a.invalidate_asid(asid);
    s.write(slot, 0);
    a.invalidate_page_structures(asid);
}

/// seL4 `unmapPDPT`.
pub fn unmap_pdpt<S: Store, A: Arch>(s: &mut S, a: &mut A, asid: u64, vaddr: u64, pdpt: u64) {
    let root = match find_vspace_for_asid(s, asid) {
        Ok(r) => r,
        Err(_) => return,
    };
    let slot = entry_addr(root, idx(vaddr, 39));
    let e = s.read(slot);
    if e & P_PRESENT == 0 || (e & ADDR_MASK) != layout::paddr(pdpt) {
        return;
    }
    a.invalidate_asid(asid);
    s.write(slot, 0);
}

/// seL4 `deleteASID`.
pub fn delete_asid<S: Store, A: Arch>(s: &mut S, a: &mut A, asid: u64, root: u64) {
    let pool = asid_table(s, asid >> ASID_LOW_BITS);
    if pool == 0 {
        return;
    }
    let e = pool.wrapping_add((asid & 511).wrapping_mul(8));
    if s.read(e) == root {
        a.invalidate_asid(asid);
        s.write(e, 0);
        let ct = sched::cur_thread(s);
        set_vm_root(s, a, ct);
    }
}

/// seL4 `deleteASIDPool`.
pub fn delete_asid_pool<S: Store, A: Arch>(s: &mut S, a: &mut A, base: u64, pool: u64) {
    if asid_table(s, base >> ASID_LOW_BITS) != pool {
        return;
    }
    let mut i = 0;
    while i < 512 {
        if s.read(pool.wrapping_add(i * 8)) != 0 {
            a.invalidate_asid(base + i);
        }
        i += 1;
    }
    set_asid_table(s, base >> ASID_LOW_BITS, 0);
    let ct = sched::cur_thread(s);
    set_vm_root(s, a, ct);
}

// ---- VM faults -----------------------------------------------------------------

/// seL4 `handleVMFault`: the fault for an access to `addr` with page-fault
/// error code `code`.
pub fn vm_fault(addr: u64, code: u64, instruction: bool) -> crate::error::Fault {
    crate::error::Fault::VmFault { addr, fsr: code, instruction }
}

// ---- invocations -----------------------------------------------------------------

fn extra(extra: &[Slot; 3], i: usize) -> Option<Slot> {
    if extra[i].is_null() {
        None
    } else {
        Some(extra[i])
    }
}

/// The PML4 and ASID named by an invocation's vspace argument, checked as
/// seL4 does for every map.
fn check_vspace<S: Store>(s: &S, vcap: Cap) -> KResult<(u64, u64)> {
    let (root, asid) = match vcap {
        Cap::Pml4 { ptr, mapped: true, asid } => (ptr, asid),
        _ => return invalid_cap(1),
    };
    match find_vspace_for_asid(s, asid) {
        Err(lf) => Err(Exc::Sys(SysError::FailedLookup { source: false, lf })),
        Ok(r) => {
            if r != root {
                invalid_cap(1)
            } else {
                Ok((root, asid))
            }
        }
    }
}

fn failed_lookup<T>(lf: LookupFault) -> KResult<T> {
    Err(Exc::Sys(SysError::FailedLookup { source: false, lf }))
}

fn reply1<S: Store>(s: &mut S, t: Tcb, call: bool, v: u64) {
    if call {
        let buf = msg::lookup_ipc_buffer(s, true, t);
        t.set_reg(s, crate::layout::reg::BADGE, 0);
        let n = msg::set_mr(s, t, buf, 0, v);
        msg::set_msg_info(s, t, MessageInfo::new(0, 0, 0, n));
    }
    sched::set_thread_state(s, t, sched::TS_RUNNING);
}

/// l4h 0017: what a remap must flush.
fn same_frame_and_type(old: u64, new: u64) -> bool {
    let m = ADDR_MASK | P_PWT | P_PCD | P_PAT_4K | P_PAT_LARGE | P_PS;
    old & m == new & m
}

fn rights_raised(old: u64, new: u64) -> bool {
    same_frame_and_type(old, new)
        && (new & P_RW) >= (old & P_RW)
        && (new & P_US) >= (old & P_US)
        && (new & P_XD) <= (old & P_XD)
}

fn rights_lowered(old: u64, new: u64) -> bool {
    same_frame_and_type(old, new)
        && (new & P_RW) <= (old & P_RW)
        && (new & P_US) <= (old & P_US)
        && (new & P_XD) >= (old & P_XD)
}

fn write_mapping<S: Store, A: Arch>(s: &mut S, a: &mut A, slot: u64, e: u64, asid: u64, vaddr: u64, defer: bool) {
    let old = s.read(slot);
    s.write(slot, e);
    if old & P_PRESENT == 0 {
        return;
    }
    if rights_raised(old, e) {
        a.invalidate_page(asid, vaddr);
        return;
    }
    if defer && rights_lowered(old, e) {
        return;
    }
    a.invalidate_asid(asid);
}

fn decode_frame<S: Store, A: Arch>(
    s: &mut S,
    a: &mut A,
    lbl: u64,
    length: u64,
    slot: Slot,
    cap: Cap,
    call: bool,
    buf: u64,
    ex: &[Slot; 3],
) -> KResult<()> {
    let ct = sched::cur_thread(s);
    let (ptr, size, rights, is_device, mapped, mapped_asid, mapped_vaddr) = match cap {
        Cap::Frame { ptr, size, rights, is_device, mapped, asid, vaddr } => (ptr, size, rights, is_device, mapped, asid, vaddr),
        _ => return illegal(),
    };
    if lbl == label::X86PageMap {
        let vslot = match extra(ex, 0) {
            Some(x) if length >= 3 => x,
            _ => return truncated(),
        };
        let vaddr = msg::syscall_arg(s, ct, buf, 0);
        let rights_mask = msg::syscall_arg(s, ct, buf, 1);
        let raw_attr = msg::syscall_arg(s, ct, buf, 2);
        let defer = raw_attr & vm_attr::DEFER_FLUSH != 0;
        let attr = raw_attr & !vm_attr::DEFER_FLUSH;
        let vcap = vslot.cap(s);
        let (root, asid) = match vcap {
            Cap::Pml4 { ptr, mapped: true, asid } => (ptr, asid),
            _ => return invalid_cap(1),
        };
        if mapped && mapped_asid != 0 {
            if mapped_asid != asid {
                return invalid_cap(1);
            }
            if mapped_vaddr != vaddr {
                return invalid_arg(0);
            }
        } else {
            let vtop = vaddr.wrapping_add(1u64 << size.bits());
            if vaddr > USER_TOP || vtop > USER_TOP {
                return invalid_arg(0);
            }
        }
        check_vspace(s, vcap)?;
        let vm = mask_vm_rights(rights, Rights::from_word(rights_mask));
        if vaddr & ((1u64 << size.bits()) - 1) != 0 {
            return Err(Exc::Sys(SysError::AlignmentError));
        }
        let paddr = layout::paddr(ptr);
        let new_cap = Cap::Frame { ptr, size, rights, is_device, mapped: true, asid, vaddr };
        match size {
            FrameSize::Small => {
                let pt_slot = match lookup_pt_slot(s, root, vaddr) {
                    Ok(x) => x,
                    Err(lf) => return failed_lookup(lf),
                };
                let e = make_user_page(s, paddr, attr, vm, false);
                sched::set_thread_state(s, ct, sched::TS_RESTART);
                slot.set_cap(s, new_cap);
                write_mapping(s, a, pt_slot, e, asid, vaddr, defer);
            }
            FrameSize::Large => {
                let pd_slot = match lookup_pd_slot(s, root, vaddr) {
                    Ok(x) => x,
                    Err(lf) => return failed_lookup(lf),
                };
                let old = s.read(pd_slot);
                if old & P_PRESENT != 0 && old & P_PS == 0 {
                    return Err(Exc::Sys(SysError::DeleteFirst));
                }
                let e = make_user_page(s, paddr, attr, vm, true);
                sched::set_thread_state(s, ct, sched::TS_RESTART);
                slot.set_cap(s, new_cap);
                write_mapping(s, a, pd_slot, e, asid, vaddr, defer);
            }
            FrameSize::Huge => {
                let pdpt_slot = match lookup_pdpt_slot(s, root, vaddr) {
                    Ok(x) => x,
                    Err(lf) => return failed_lookup(lf),
                };
                let old = s.read(pdpt_slot);
                if old & P_PRESENT != 0 && old & P_PS == 0 {
                    return Err(Exc::Sys(SysError::DeleteFirst));
                }
                let e = make_user_page(s, paddr, attr, vm, true);
                sched::set_thread_state(s, ct, sched::TS_RESTART);
                slot.set_cap(s, new_cap);
                write_mapping(s, a, pdpt_slot, e, asid, vaddr, defer);
            }
        }
        Ok(())
    } else if lbl == label::X86PageUnmap {
        sched::set_thread_state(s, ct, sched::TS_RESTART);
        if mapped && mapped_asid != 0 {
            unmap_page(s, a, size, mapped_asid, mapped_vaddr, ptr);
        }
        slot.set_cap(s, Cap::Frame { ptr, size, rights, is_device, mapped: false, asid: 0, vaddr: 0 });
        Ok(())
    } else if lbl == label::X86PageGetAddress {
        sched::set_thread_state(s, ct, sched::TS_RESTART);
        reply1(s, ct, call, layout::paddr(ptr));
        Ok(())
    } else if lbl == label::X86PageTestAndClearAccessed {
        if !matches!(size, FrameSize::Small | FrameSize::Large) || !mapped || mapped_asid == 0 {
            return illegal();
        }
        let root = match find_vspace_for_asid(s, mapped_asid) {
            Ok(r) => r,
            Err(_) => return invalid_cap(0),
        };
        let pa = layout::paddr(ptr);
        let e_addr = match size {
            FrameSize::Large => match lookup_pd_slot(s, root, mapped_vaddr) {
                Ok(x) => {
                    let e = s.read(x);
                    if e & P_PRESENT == 0 || e & P_PS == 0 || e & ADDR_MASK != pa {
                        return invalid_cap(0);
                    }
                    x
                }
                Err(_) => return invalid_cap(0),
            },
            _ => match lookup_pt_slot(s, root, mapped_vaddr) {
                Ok(x) => {
                    let e = s.read(x);
                    if e & P_PRESENT == 0 || e & ADDR_MASK != pa {
                        return invalid_cap(0);
                    }
                    x
                }
                Err(_) => return invalid_cap(0),
            },
        };
        let old = s.read(e_addr);
        s.write(e_addr, old & !P_ACCESSED);
        reply1(s, ct, call, if old & P_ACCESSED != 0 { 1 } else { 0 });
        Ok(())
    } else if lbl == label::X86PageDeriveSubframe {
        derive_subframe(s, a, length, slot, cap, buf, ex)
    } else {
        illegal()
    }
}

/// l4h 0029: 4 KiB aliases of a RAM-backed 2 MiB frame.
fn derive_subframe<S: Store, A: Arch>(s: &mut S, a: &mut A, length: u64, src: Slot, cap: Cap, buf: u64, ex: &[Slot; 3]) -> KResult<()> {
    let _ = a;
    let ct = sched::cur_thread(s);
    let node_slot = match extra(ex, 0) {
        Some(x) if length >= 6 => x,
        _ => return truncated(),
    };
    let (ptr, rights) = match cap {
        Cap::Frame { ptr, size: FrameSize::Large, rights, is_device: false, .. } => (ptr, rights),
        _ => return illegal(),
    };
    let node_index = msg::syscall_arg(s, ct, buf, 0);
    let node_depth = msg::syscall_arg(s, ct, buf, 1);
    let node_offset = msg::syscall_arg(s, ct, buf, 2);
    let offset = msg::syscall_arg(s, ct, buf, 3);
    let count = msg::syscall_arg(s, ct, buf, 4);
    if offset >= (1 << 21) || offset & 0xfff != 0 {
        return invalid_arg(3);
    }
    let max = ((1u64 << 21) - offset) >> 12;
    if count < 1 || count > max {
        return range(1, max);
    }
    let mut node_cap = node_slot.cap(s);
    if node_depth != 0 {
        node_cap = cspace::lookup_target_slot(s, node_cap, node_index, node_depth)?.cap(s);
    }
    let (dest, radix) = match node_cap {
        Cap::CNode { ptr, radix, .. } => (ptr, radix),
        _ => return failed_lookup(LookupFault::MissingCapability { bits_left: node_depth }),
    };
    let node_size = 1u64 << (radix & 63);
    if node_offset > node_size - 1 {
        return range(0, node_size - 1);
    }
    if count > node_size - node_offset {
        return range(1, node_size - node_offset);
    }
    let mut i = 0;
    while i < count {
        cdt::ensure_empty_slot(s, Slot::index(dest, node_offset + i))?;
        i += 1;
    }
    let mask = msg::syscall_arg(s, ct, buf, 5);
    let vm = mask_vm_rights(rights, Rights::from_word(mask));
    sched::set_thread_state(s, ct, sched::TS_RESTART);
    let base = ptr.wrapping_add(offset);
    let mut i = 0;
    while i < count {
        let c = Cap::Frame {
            ptr: base.wrapping_add(i << 12),
            size: FrameSize::Small,
            rights: vm,
            is_device: false,
            mapped: false,
            asid: 0,
            vaddr: 0,
        };
        cdt::insert(s, c, src, Slot::index(dest, node_offset + i));
        i += 1;
    }
    Ok(())
}

/// Shared shape of PT, PD and PDPT map/unmap. `level` is the shift of the
/// region the table covers (21, 30 or 39).
fn decode_table<S: Store, A: Arch>(
    s: &mut S,
    a: &mut A,
    lbl: u64,
    length: u64,
    slot: Slot,
    cap: Cap,
    buf: u64,
    ex: &[Slot; 3],
) -> KResult<()> {
    let ct = sched::cur_thread(s);
    let (map_lbl, unmap_lbl, level, ptr, mapped, masid, mvaddr) = match cap {
        Cap::PageTable { ptr, mapped, asid, vaddr } => (label::X86PageTableMap, label::X86PageTableUnmap, 21u64, ptr, mapped, asid, vaddr),
        Cap::PageDirectory { ptr, mapped, asid, vaddr } => {
            (label::X86PageDirectoryMap, label::X86PageDirectoryUnmap, 30u64, ptr, mapped, asid, vaddr)
        }
        Cap::Pdpt { ptr, mapped, asid, vaddr } => (label::X86PDPTMap, label::X86PDPTUnmap, 39u64, ptr, mapped, asid, vaddr),
        _ => return illegal(),
    };
    if lbl == unmap_lbl {
        if !cdt::is_final_capability(s, slot) {
            return Err(Exc::Sys(SysError::RevokeFirst));
        }
        sched::set_thread_state(s, ct, sched::TS_RESTART);
        if mapped {
            if level == 21 {
                unmap_page_table(s, a, masid, mvaddr, ptr);
            } else if level == 30 {
                unmap_page_directory(s, a, masid, mvaddr, ptr);
            } else {
                unmap_pdpt(s, a, masid, mvaddr, ptr);
            }
            s.zero(ptr, 4096);
        }
        slot.set_cap(s, with_mapping(cap, false, masid, mvaddr));
        return Ok(());
    }
    if lbl != map_lbl {
        return illegal();
    }
    let vslot = match extra(ex, 0) {
        Some(x) if length >= 2 => x,
        _ => return truncated(),
    };
    if mapped {
        return invalid_cap(0);
    }
    let vaddr = msg::syscall_arg(s, ct, buf, 0) & !((1u64 << level) - 1);
    let attr = msg::syscall_arg(s, ct, buf, 1);
    let vcap = vslot.cap(s);
    if !is_valid_vtable_root(vcap) {
        return invalid_cap(1);
    }
    if vaddr > USER_TOP {
        return invalid_arg(0);
    }
    let (root, asid) = check_vspace(s, vcap)?;
    let e_addr = if level == 21 {
        match lookup_pd_slot(s, root, vaddr) {
            Ok(x) => x,
            Err(lf) => return failed_lookup(lf),
        }
    } else if level == 30 {
        match lookup_pdpt_slot(s, root, vaddr) {
            Ok(x) => x,
            Err(lf) => return failed_lookup(lf),
        }
    } else {
        entry_addr(root, idx(vaddr, 39))
    };
    if s.read(e_addr) & P_PRESENT != 0 {
        return Err(Exc::Sys(SysError::DeleteFirst));
    }
    let e = make_user_table(layout::paddr(ptr), attr);
    sched::set_thread_state(s, ct, sched::TS_RESTART);
    slot.set_cap(s, with_mapping(cap, true, asid, vaddr));
    s.write(e_addr, e);
    a.invalidate_page_structures(asid);
    Ok(())
}

fn with_mapping(c: Cap, mapped: bool, asid: u64, vaddr: u64) -> Cap {
    let (asid, vaddr) = if mapped { (asid, vaddr) } else { (0, 0) };
    match c {
        Cap::PageTable { ptr, .. } => Cap::PageTable { ptr, mapped, asid, vaddr },
        Cap::PageDirectory { ptr, .. } => Cap::PageDirectory { ptr, mapped, asid, vaddr },
        Cap::Pdpt { ptr, .. } => Cap::Pdpt { ptr, mapped, asid, vaddr },
        other => other,
    }
}

/// seL4 `decodeX86MMUInvocation` and the x86_64 mode part.
#[allow(clippy::too_many_arguments)]
pub fn decode<S: Store, A: Arch>(
    s: &mut S,
    a: &mut A,
    lbl: u64,
    length: u64,
    slot: Slot,
    cap: Cap,
    call: bool,
    buf: u64,
    ex: &[Slot; 3],
) -> KResult<()> {
    let ct = sched::cur_thread(s);
    match cap {
        Cap::Frame { .. } => decode_frame(s, a, lbl, length, slot, cap, call, buf, ex),
        Cap::PageTable { .. } | Cap::PageDirectory { .. } | Cap::Pdpt { .. } => decode_table(s, a, lbl, length, slot, cap, buf, ex),
        Cap::Pml4 { mapped, asid, .. } => {
            if lbl == label::X86PML4Flush {
                if !mapped {
                    return invalid_cap(0);
                }
                sched::set_thread_state(s, ct, sched::TS_RESTART);
                a.invalidate_asid(asid);
                Ok(())
            } else {
                illegal()
            }
        }
        Cap::AsidControl => {
            if lbl != label::X86ASIDControlMakePool {
                return illegal();
            }
            let (parent, root_slot) = match (extra(ex, 0), extra(ex, 1)) {
                (Some(x), Some(y)) if length >= 2 => (x, y),
                _ => return truncated(),
            };
            let index = msg::syscall_arg(s, ct, buf, 0);
            let depth = msg::syscall_arg(s, ct, buf, 1);
            let untyped = parent.cap(s);
            let root = root_slot.cap(s);
            let mut i = 0;
            while i < N_ASID_POOLS && asid_table(s, i) != 0 {
                i += 1;
            }
            if i == N_ASID_POOLS {
                return Err(Exc::Sys(SysError::DeleteFirst));
            }
            let base = i << ASID_LOW_BITS;
            let frame = match untyped {
                Cap::Untyped { ptr, size_bits, is_device: false, .. } if size_bits == bits::ASID_POOL => ptr,
                _ => return invalid_cap(1),
            };
            cdt::ensure_no_children(s, parent)?;
            let dest = cspace::lookup_target_slot(s, root, index, depth)?;
            cdt::ensure_empty_slot(s, dest)?;
            sched::set_thread_state(s, ct, sched::TS_RESTART);
            if let Cap::Untyped { ptr, size_bits, is_device, .. } = untyped {
                parent.set_cap(s, Cap::Untyped { ptr, size_bits, free_index: 1u64 << size_bits, is_device });
            }
            s.zero(frame, 4096);
            cdt::insert(s, Cap::AsidPool { ptr: frame, asid_base: base }, parent, dest);
            set_asid_table(s, i, frame);
            Ok(())
        }
        Cap::AsidPool { ptr, asid_base } => {
            if lbl != label::X86ASIDPoolAssign {
                return illegal();
            }
            let vslot = match extra(ex, 0) {
                Some(x) => x,
                None => return truncated(),
            };
            let vroot = match vslot.cap(s) {
                Cap::Pml4 { ptr, mapped: false, .. } => ptr,
                _ => return invalid_cap(1),
            };
            let pool = asid_table(s, asid_base >> ASID_LOW_BITS);
            if pool == 0 {
                return Err(Exc::Sys(SysError::FailedLookup { source: false, lf: LookupFault::InvalidRoot }));
            }
            if pool != ptr {
                return invalid_cap(0);
            }
            let mut i = 0;
            while i < 512 && (asid_base + i == 0 || s.read(pool.wrapping_add(i * 8)) != 0) {
                i += 1;
            }
            if i == 512 {
                return Err(Exc::Sys(SysError::DeleteFirst));
            }
            let asid = asid_base + i;
            sched::set_thread_state(s, ct, sched::TS_RESTART);
            vslot.set_cap(s, Cap::Pml4 { ptr: vroot, mapped: true, asid });
            s.write(pool.wrapping_add((asid & 511) * 8), vroot);
            Ok(())
        }
        _ => invalid_cap(0),
    }
}
