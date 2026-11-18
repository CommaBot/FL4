/// CONFIG_PADDR_USER_DEVICE_TOP: 2^47.
pub const PADDR_USER_DEVICE_TOP: u64 = 1 << 47;

/// Map a page of the initial address space (seL4 `map_it_frame_cap`).
fn map_it_frame<S: Store>(s: &mut S, pml4: u64, vaddr: u64, paddr: u64) {
    let pdpt = next_table(s, pml4, vaddr, 39);
    let pd = next_table(s, pdpt, vaddr, 30);
    let pt = next_table(s, pd, vaddr, 21);
    s.write(entry_addr(pt, vaddr, 12), ((paddr | s.frame_masks().0) & 0x000f_ffff_ffff_f000) | 0x7);
}

/// seL4 `create_it_address_space` (x86_64).
fn create_it_address_space<S: Store>(s: &mut S, b: &mut Boot, it: Region, pml4: u64) -> Cap {
    vspace::copy_global_mappings(s, pml4);
    let cap = Cap::Pml4 { ptr: pml4, mapped: true, asid: IT_ASID };
    write_slot(s, root_slot(b, rs::InitThreadVSpace), cap);
    let first = b.slot_pos;
    // PDPTs, then page directories, then page tables, as seL4 does. The
    // loops count tables rather than step addresses, so they cannot wrap.
    let mut k: u64 = 0;
    while k < 3 {
        let level = 39 - 9 * k;
        let n = n_paging(it, level);
        let base = it.start & !((1u64 << (level & 63)).wrapping_sub(1));
        let mut j: u64 = 0;
        while j < n {
            let v = base.wrapping_add(j << (level & 63));
            let t = alloc(s, b, 12, 1);
            let e = (layout::paddr(t) & 0x000f_ffff_ffff_f000) | 0x7;
            let c = if level == 39 {
                s.write(entry_addr(pml4, v, 39), e);
                Cap::Pdpt { ptr: t, mapped: true, asid: IT_ASID, vaddr: v }
            } else if level == 30 {
                let pdpt = next_table(s, pml4, v, 39);
                s.write(entry_addr(pdpt, v, 30), e);
                Cap::PageDirectory { ptr: t, mapped: true, asid: IT_ASID, vaddr: v }
            } else {
                let pdpt = next_table(s, pml4, v, 39);
                let pd = next_table(s, pdpt, v, 30);
                s.write(entry_addr(pd, v, 21), e);
                Cap::PageTable { ptr: t, mapped: true, asid: IT_ASID, vaddr: v }
            };
            provide_cap(s, b, c);
            j += 1;
        }
        k += 1;
    }
    bi_set(s, b, bi::USER_IMAGE_PAGING, first);
    bi_set(s, b, bi::USER_IMAGE_PAGING + 1, b.slot_pos);
    cap
}

/// The root CNode, IO port control, domain and IRQ control caps, and the
/// initial IRQ states; returns the root CNode's cap.
fn init_root_cnode<S: Store>(s: &mut S, b: &Boot) -> Cap {
    let root_cap = Cap::CNode { ptr: b.root_cnode, radix: ROOT_CNODE_BITS, guard_size: 64 - ROOT_CNODE_BITS, guard: 0 };
    write_slot(s, root_slot(b, rs::InitThreadCNode), root_cap);
    write_slot(s, root_slot(b, rs::IOPortControl), Cap::IoPortControl);
    write_slot(s, root_slot(b, rs::Domain), Cap::Domain);
    init_irq_states(s);
    write_slot(s, root_slot(b, rs::IRQControl), Cap::IrqControl);
    root_cap
}

fn init_irq_states<S: Store>(s: &mut S) {
    let mut i = 0;
    while i <= irq::MAX {
        let st = if i == irq::TIMER {
            interrupt::IRQ_TIMER
        } else if i == irq::REMOTE_CALL_IPI || i == irq::RESCHEDULE_IPI {
            interrupt::IRQ_IPI
        } else {
            interrupt::IRQ_INACTIVE
        };
        ks_set(s, ks::IRQ_STATE.wrapping_add(i.wrapping_mul(8)), st);
        i += 1;
    }
}

fn objects_init_fpu<S: Store>(s: &mut S, t: Tcb) {
    let f = t.fpu_addr();
    s.write(f, 0x037f);
    s.write(f.wrapping_add(24), 0x0000_ffff_0000_1f80);
}
