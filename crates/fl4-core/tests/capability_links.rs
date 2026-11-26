use fl4_core::capability::Cap;
use fl4_core::layout::cte;
use fl4_core::machine::Store;
use fl4_core::obj::Slot;
use fl4_core::cdt;
use std::collections::BTreeMap;

#[derive(Default)]
struct Memory(BTreeMap<u64, u64>);
impl Store for Memory {
    fn fetch_and(&mut self, a: u64, m: u64) -> u64 { let old = self.read(a); self.write(a, old & m); old }
    fn read(&self, a: u64) -> u64 { *self.0.get(&a).unwrap_or(&0) }
    fn write(&mut self, a: u64, v: u64) { self.0.insert(a, v); }
    fn zero(&mut self, a: u64, len: u64) {
        for offset in (0..len).step_by(8) { self.write(a + offset, 0); }
    }
    fn clear_free(&mut self, a: u64, len: u64) { self.zero(a, len); }
    fn ks_base(&self) -> u64 { 0x100000 }
    fn cur_cpu(&self) -> u64 { 0 }
}

fn endpoint(badge: u64) -> Cap {
    Cap::Endpoint { ptr: 0x8000, badge, send: true, recv: true, grant: true, grant_reply: true }
}

fn check_links(s: &Memory, slot: Slot, prev: Slot, next: Slot, revocable: bool, first_badged: bool) {
    assert_eq!(slot.prev(s).0, prev.0);
    assert_eq!(slot.next(s).0, next.0);
    assert_eq!(slot.revocable(s), revocable);
    assert_eq!(slot.first_badged(s), first_badged);
}

#[test]
fn insertion_distinguishes_minted_children_from_unbadged_copies() {
    let mut s = Memory::default();
    let parent = Slot(0x1000);
    let copy = Slot(0x1020);
    // Exercise canonical high pointer reconstruction in the packed link.
    let minted = Slot(0xffff_8000_0000_1040);
    parent.set_cap(&mut s, endpoint(0));
    cdt::insert(&mut s, endpoint(0), parent, copy);
    cdt::insert(&mut s, endpoint(7), parent, minted);
    check_links(&s, parent, Slot(0), minted, false, false);
    check_links(&s, minted, parent, copy, true, true);
    check_links(&s, copy, minted, Slot(0), false, false);
    assert!(minted.cap(&s) == endpoint(7));
    assert!(!cdt::is_final_capability(&s, parent));
    assert!(!cdt::is_final_capability(&s, copy));
}

#[test]
fn moving_and_swapping_preserve_links_flags_and_reserved_metadata() {
    for revocable in [false, true] {
        for first_badged in [false, true] {
            let mut s = Memory::default();
            let (prev, src, next, dest, other) = (Slot(0x1000), Slot(0x1020), Slot(0x1040), Slot(0x1060), Slot(0x1080));
            src.set_cap(&mut s, endpoint(7));
            prev.set_next(&mut s, src);
            next.set_prev(&mut s, src);
            src.set_prev(&mut s, prev);
            src.set_next(&mut s, next);
            src.set_revocable(&mut s, revocable);
            src.set_first_badged(&mut s, first_badged);
            let reserved = 0xa5a0_0000_0000_0000;
            s.write(dest.0 + cte::NEXT, reserved);
            cdt::move_cap(&mut s, endpoint(7), src, dest);
            check_links(&s, dest, prev, next, revocable, first_badged);
            assert_eq!(prev.next(&s).0, dest.0);
            assert_eq!(next.prev(&s).0, dest.0);
            assert!(src.cap(&s).is_null());
            assert_eq!(s.read(dest.0 + cte::NEXT) & 0xfffc_0000_0000_0000, reserved);
            other.set_cap(&mut s, endpoint(9));
            cdt::swap(&mut s, endpoint(7), dest, endpoint(9), other);
            check_links(&s, other, prev, next, revocable, first_badged);
            check_links(&s, dest, Slot(0), Slot(0), false, false);
            assert_eq!(prev.next(&s).0, other.0);
            assert_eq!(next.prev(&s).0, other.0);
            assert!(other.cap(&s) == endpoint(7));
            assert!(dest.cap(&s) == endpoint(9));
        }
    }
}

#[test]
fn copying_an_untyped_marks_the_source_full_and_links_the_child() {
    let mut s = Memory::default();
    let (parent, child) = (Slot(0x1000), Slot(0x1020));
    let cap = Cap::Untyped { ptr: 0x20000, size_bits: 12, is_device: false, free_index: 0 };
    parent.set_cap(&mut s, cap);
    cdt::insert(&mut s, cap, parent, child);
    assert!(parent.cap(&s) == Cap::Untyped { ptr: 0x20000, size_bits: 12, is_device: false, free_index: 1 << 12 });
    assert!(child.cap(&s) == cap);
    check_links(&s, child, parent, Slot(0), true, true);
}
