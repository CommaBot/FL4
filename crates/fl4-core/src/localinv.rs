//! Frame-capability invocations beside the serial gate (DESIGN.md §7,
//! "Local paths"): CNode Copy and Mint of a frame cap, CNode Delete of a
//! small RAM frame cap, and the page map of a small frame (X86Page_Map on
//! x86_64, ARMPage_Map on AArch64). A guest maps every page through its
//! own frame-cap copy (l4h's vspace.c), so fork, exit and page faults are
//! mostly these three.
//!
//! `plan` resolves, without locks, the kernel words the general path of
//! the invocation may write besides the caller and this core: capability
//! slots and one page-table entry. It reads each word of those slots it
//! decides from once and records the value (`Plan::read`). The runtime
//! locks them (`fl4_store::lock`), and `syscall::handle_invocation_local`
//! runs the general decode only if every recorded word still holds its
//! value (`Plan::still_holds`), and declines otherwise.
//!
//! What may change outside the gate is exactly what these paths write:
//! the cap words of an empty slot (Copy, Mint) or of a frame-cap slot (Map,
//! Delete), the CDT links of any slot next to one, and a leaf page-table
//! entry of a small page. Every lookup a plan makes reads only other words:
//! CNode caps along a CPtr's path (a path through a slot being written
//! fails, as it does on either side of the write: the type tag is all in
//! the first cap word, an aligned 64-bit word that a load reads whole, and
//! neither the old nor the new cap of such a slot is a CNode, so this holds
//! whatever order the two words become visible in, on AArch64 as on x86),
//! the vspace cap, the ASID table and the paging structures above the leaf.
//! CPtrs, depths and the virtual address come from the caller's saved
//! registers; extra caps are looked up once, here, and the decode uses
//! those slots, so a change to the caller's IPC buffer in between cannot
//! move a write onto an unlocked word.
//!
//! The only Arch operation these paths make is the invalidation of one
//! page's translations by an unmap or a remap. On x86_64 it may make a
//! remote call (`CALL_LOCK`, fl4-arch-x86_64 smp.rs). On AArch64 it is a
//! broadcast TLBI that writes no kernel state; a map that would clean the
//! frame's cache lines first (a RAM frame mapped non-cacheable,
//! `vspace::install_page`) is left to the gate.
//!
//! Not yet exercised by fl4-sim, which generates no frame-cap copies,
//! maps or deletes.

use crate::capability::{Cap, FrameSize};
use crate::cspace;
use crate::ipc::{self, ExtraCaps};
use crate::layout::{cte, reg};
use crate::machine::Store;
use crate::msg;
use crate::obj::{Slot, Tcb};
use fl4_abi::label;
use fl4_abi::syscall as sc;

/// Words a local invocation may lock (`fl4_store::lock::MAX_HELD`).
pub const MAX_LOCKS: usize = 4;

/// A local invocation: the invoked slot, the extra caps, and what to lock
/// (capability slots, 32 bytes, then at most one page-table entry, 8).
#[derive(Clone, Copy)]
pub struct Plan {
    pub slot: Slot,
    pub extra: ExtraCaps,
    pub locks: [u64; MAX_LOCKS],
    pub n: usize,
    /// `locks[pte]` is a page-table entry, if `pte < n`.
    pub pte: usize,
    /// Words of the locked slots the plan was read from, and their values:
    /// the rest of what it read changes only under the gate.
    seen: [(u64, u64); MAX_LOCKS],
    nseen: usize,
    ok_words: bool,
}

impl Plan {
    fn new(slot: Slot, extra: ExtraCaps) -> Plan {
        Plan { slot, extra, locks: [0; MAX_LOCKS], n: 0, pte: MAX_LOCKS, seen: [(0, 0); MAX_LOCKS], nseen: 0, ok_words: true }
    }

    fn add(&mut self, addr: u64) -> bool {
        if addr == 0 {
            return true;
        }
        if self.n >= MAX_LOCKS {
            return false;
        }
        self.locks[self.n] = addr;
        self.n += 1;
        true
    }

    fn add_pte(&mut self, addr: u64) -> bool {
        self.pte = self.n;
        self.add(addr)
    }

    /// Read word `addr` of a slot the plan will lock, once: the plan
    /// decides from the value returned, and `still_holds` checks that very
    /// value under the locks. (Reading it again later could see a value
    /// another core's local path wrote since the decision.) Past
    /// `MAX_LOCKS` words, which no plan needs, the plan is refused.
    fn read<S: Store>(&mut self, s: &S, addr: u64) -> u64 {
        if self.nseen >= MAX_LOCKS {
            self.ok_words = false;
            return 0;
        }
        let v = s.read(addr);
        self.seen[self.nseen] = (addr, v);
        self.nseen += 1;
        v
    }

    /// The cap in `slot`, from words read once (`read`).
    fn read_cap<S: Store>(&mut self, s: &S, slot: Slot) -> Cap {
        let w0 = self.read(s, slot.0.wrapping_add(cte::CAP0));
        let w1 = self.read(s, slot.0.wrapping_add(cte::CAP1));
        Cap::decode(w0, w1)
    }

    /// With the plan's words locked: the words it was read from still hold
    /// what it read, so planning again would give the same plan.
    pub fn still_holds<S: Store>(&self, s: &S) -> bool {
        let mut i = 0;
        while i < self.nseen && i < MAX_LOCKS {
            let (addr, v) = self.seen[i];
            if s.read(addr) != v {
                return false;
            }
            i += 1;
        }
        true
    }
}

fn some_if(ok: bool, p: Plan) -> Option<Plan> {
    if ok && p.ok_words {
        Some(p)
    } else {
        None
    }
}

/// Argument `i` of `t`'s invocation, for `i` below msg::N_MSG_REGISTERS:
/// a saved register, which only `t` changes.
fn reg_arg<S: Store>(s: &S, t: Tcb, i: u64) -> u64 {
    msg::syscall_arg(s, t, 0, i)
}

/// A label `plan` may take, by the label alone (a register).
#[inline(always)]
pub fn is_local_label(lbl: u64) -> bool {
    lbl == label::CNodeCopy || lbl == label::CNodeMint || lbl == label::CNodeDelete || is_page_map(lbl)
}

#[cfg(not(feature = "aarch64"))]
fn is_page_map(lbl: u64) -> bool {
    lbl == label::X86PageMap
}

#[cfg(feature = "aarch64")]
fn is_page_map(lbl: u64) -> bool {
    lbl == label::ARMPageMap
}

/// A small, non-device frame cap outside an EPT.
fn small_ram_frame(c: Cap) -> bool {
    matches!(c, Cap::Frame { size: FrameSize::Small, is_device: false, is_ept: false, .. })
}

/// The plan for the current thread's `SysCall`, if it is a local
/// invocation whose lookups all succeed.
pub fn plan<S: Store>(s: &S, number: i64) -> Option<Plan> {
    if number != sc::SysCall {
        return None;
    }
    let t = crate::sched::cur_thread(s);
    let info = msg::msg_info(s, t);
    if !is_local_label(info.label) {
        return None;
    }
    let slot = match cspace::lookup_slot(s, t, t.reg(s, reg::CAP)) {
        Ok(r) => r.slot,
        Err(_) => return None,
    };
    let buf = msg::lookup_ipc_buffer(s, false, t);
    let extra = match ipc::lookup_extra_caps(s, t, buf, info) {
        Ok(e) => e,
        Err(_) => return None,
    };
    plan_with(s, t, info.label, slot, extra)
}

/// The plan for invoking `slot` with `extra`. Under the locks,
/// `Plan::still_holds` checks that it is still the plan.
pub fn plan_with<S: Store>(s: &S, t: Tcb, lbl: u64, slot: Slot, extra: ExtraCaps) -> Option<Plan> {
    let mut p = Plan::new(slot, extra);
    let cap = slot.cap(s);
    if lbl == label::CNodeCopy || lbl == label::CNodeMint {
        if !matches!(cap, Cap::CNode { .. }) || extra[0].is_null() {
            return None;
        }
        let dest = cspace::lookup_target_slot(s, cap, reg_arg(s, t, 0), reg_arg(s, t, 1)).ok()?;
        let src = cspace::lookup_source_slot(s, extra[0].cap(s), reg_arg(s, t, 2), reg_arg(s, t, 3)).ok()?;
        // An empty destination (a first cap word of 0), the source cap, and
        // the source's CDT link, which names the third slot. The test is on
        // the raw word, not `Cap::decode(..).is_null()`: decode also maps
        // the unused type tags to Null, but no kernel path writes one
        // (`Slot::set_cap` encodes Null as 0, `Slot::clear` writes 0, new
        // slots are zeroed), so at reachable states the two agree; a slot
        // whose nonzero word decodes to Null is left to the gate.
        let dest_w0 = p.read(s, dest.0.wrapping_add(cte::CAP0));
        let src_cap = p.read_cap(s, src);
        let next = Slot::next_of_word(p.read(s, src.0.wrapping_add(cte::NEXT)));
        if !matches!(src_cap, Cap::Frame { is_ept: false, .. }) || dest_w0 != 0 {
            return None;
        }
        let ok = p.add(dest.0) && p.add(src.0) && p.add(next.0);
        some_if(ok, p)
    } else if lbl == label::CNodeDelete {
        if !matches!(cap, Cap::CNode { .. }) {
            return None;
        }
        let dest = cspace::lookup_target_slot(s, cap, reg_arg(s, t, 0), reg_arg(s, t, 1)).ok()?;
        // The cap decides the page-table entry; its links the other slots.
        let c = p.read_cap(s, dest);
        let prev = Slot(p.read(s, dest.0.wrapping_add(cte::PREV)));
        let next = Slot::next_of_word(p.read(s, dest.0.wrapping_add(cte::NEXT)));
        if !small_ram_frame(c) {
            return None;
        }
        if !(p.add(dest.0) && p.add(prev.0) && p.add(next.0)) {
            return None;
        }
        match c {
            Cap::Frame { mapped: true, asid, vaddr, .. } if asid != 0 => {
                // As unmap_page: no mapping to clear if the lookups fail.
                match small_page_entry(s, asid, vaddr) {
                    Some(e) => {
                        let ok = p.add_pte(e);
                        some_if(ok, p)
                    }
                    None => some_if(true, p),
                }
            }
            _ => some_if(true, p),
        }
    } else if is_page_map(lbl) {
        // The frame cap, read once (`cap` above is not recorded).
        let frame = p.read_cap(s, slot);
        if !small_ram_frame(frame) || extra[0].is_null() {
            return None;
        }
        let root = match extra[0].cap(s) {
            Cap::Pml4 { ptr, mapped: true, .. } => ptr,
            _ => return None,
        };
        if !map_attr_local(reg_arg(s, t, 2)) {
            return None;
        }
        let e = page_entry(s, root, reg_arg(s, t, 0))?;
        let ok = p.add(slot.0) && p.add_pte(e);
        some_if(ok, p)
    } else {
        None
    }
}

/// The page-table entry `unmap_page` would clear for a small frame mapped
/// at `vaddr` with ASID `asid`; None if it would clear none.
#[cfg(not(feature = "aarch64"))]
fn small_page_entry<S: Store>(s: &S, asid: u64, vaddr: u64) -> Option<u64> {
    let root = crate::vspace::find_vspace_for_asid(s, asid).ok()?;
    page_entry(s, root, vaddr)
}

/// Only user addresses: a map above USER_TOP fails in the decode, and a
/// plan for one would walk (and lock) the kernel's half of the tables (on
/// x86_64; an AArch64 VSpace holds no kernel mappings, but maps nothing
/// above USER_TOP either).
fn page_entry<S: Store>(s: &S, root: u64, vaddr: u64) -> Option<u64> {
    if vaddr > fl4_abi::consts::USER_TOP {
        return None;
    }
    crate::vspace::small_page_entry(s, root, vaddr)
}

/// x86_64 maps never maintain caches.
#[cfg(not(feature = "aarch64"))]
fn map_attr_local(_attr: u64) -> bool {
    true
}

/// The page-table entry `unmap_page` would clear for a small frame mapped
/// at `vaddr` with ASID `asid`, in a VSpace or an `ArmHighVSpace`; None if
/// it would clear none. (Its invalidation, `invalidate_page` or
/// `invalidate_high_page`, is a broadcast TLBI either way.)
#[cfg(feature = "aarch64")]
fn small_page_entry<S: Store>(s: &S, asid: u64, vaddr: u64) -> Option<u64> {
    let (root, _) = crate::vspace::unmap_root(s, asid)?;
    crate::vspace::small_page_entry(s, root, vaddr)
}

/// A cacheable mapping: `install_page` maintains no cache for it, so the
/// map makes no Arch operation but the TLBI of a remap (module comment).
#[cfg(feature = "aarch64")]
fn map_attr_local(attr: u64) -> bool {
    attr & fl4_abi::consts::arm_vm_attr::PAGE_CACHEABLE != 0
}

#[cfg(test)]
mod tests {
    //! The destination test of a local CNode Copy or Mint.
    extern crate std;
    use super::*;
    use crate::capability::VM_READ_WRITE;
    use std::collections::BTreeMap;

    #[derive(Default)]
    struct Mem(BTreeMap<u64, u64>);
    impl Store for Mem {
        fn read(&self, a: u64) -> u64 {
            *self.0.get(&a).unwrap_or(&0)
        }
        fn write(&mut self, a: u64, v: u64) {
            self.0.insert(a, v);
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
            0x10_0000
        }
        fn cur_cpu(&self) -> u64 {
            0
        }
    }

    const THREAD: Tcb = Tcb(0x40_0000);
    const ROOT: Slot = Slot(0x60_0000);
    fn cnode() -> u64 {
        crate::layout::pptr(0x90_0000)
    }
    const SRC: u64 = 3;
    const DEST: u64 = 5;

    /// A CNode of 16 slots, invoked through `ROOT` and named again by the
    /// extra cap, slot `SRC` holding a frame cap; the call copies it to
    /// slot `DEST`, whose first two words are `w0` and `w1`.
    fn plan_for(lbl: u64, w0: u64, w1: u64) -> Option<Plan> {
        let mut s = Mem::default();
        ROOT.set_cap(&mut s, Cap::CNode { ptr: cnode(), radix: 4, guard_size: 0, guard: 0 });
        Slot::index(cnode(), SRC).set_cap(
            &mut s,
            Cap::Frame { ptr: crate::layout::pptr(0x20_0000), size: FrameSize::Small, rights: VM_READ_WRITE, is_device: false, mapped: false, is_ept: false, asid: 0, vaddr: 0 },
        );
        let dest = Slot::index(cnode(), DEST);
        s.write(dest.0 + cte::CAP0, w0);
        s.write(dest.0 + cte::CAP1, w1);
        for (i, v) in [DEST, 4, SRC, 4].into_iter().enumerate() {
            THREAD.set_reg(&mut s, msg::msg_register(i as u64), v);
        }
        plan_with(&s, THREAD, lbl, ROOT, [ROOT, Slot(0), Slot(0)])
    }

    /// The plan takes a destination whose first cap word is 0, and locks
    /// it with the source; a nonzero first word, even one that
    /// `Cap::decode` reads as Null (an unused type tag, or tag 0 with other
    /// bits set), leaves the invocation to the gate.
    #[test]
    fn copy_plan_requires_a_zero_destination_word() {
        for lbl in [label::CNodeCopy, label::CNodeMint] {
            let p = plan_for(lbl, 0, 0).expect("a local plan");
            assert_eq!(&p.locks[..p.n], &[Slot::index(cnode(), DEST).0, Slot::index(cnode(), SRC).0]);
            assert!(plan_for(lbl, 0, 0x1234).is_some(), "second word is not the type");
            let mut odd = std::vec![1u64, 0x0000_ffff_ffff_f000];
            for t in 0..32u64 {
                if Cap::decode(t << 59, 0).is_null() && t != 0 {
                    odd.push(t << 59);
                }
            }
            assert!(odd.len() > 2, "some tags are unused");
            for w0 in odd {
                assert!(Cap::decode(w0, 0).is_null());
                assert!(plan_for(lbl, w0, 0).is_none(), "{w0:#x}");
            }
            // A real cap in the destination: declined as before.
            let (w0, w1) = Cap::Thread { ptr: crate::layout::pptr(0x30_0000) }.encode();
            assert!(plan_for(lbl, w0, w1).is_none());
        }
    }
}
