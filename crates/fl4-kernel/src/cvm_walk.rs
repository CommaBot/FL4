//! The walk of the current user page tables by the user #VC (SEV-SNP,
//! snp.rs `user_vc`) and #VE (Intel TDX, tdx.rs `user_ve`) handlers, as a
//! plain function so host tests run it (xtask/tests/cvm_walk.rs).

const ADDR: u64 = 0x000f_ffff_ffff_f000;
const PRESENT: u64 = 1;
const WRITE: u64 = 1 << 1;
const USER: u64 = 1 << 2;
const HUGE: u64 = 1 << 7;
const NX: u64 = 1 << 63;

pub enum Access {
    Execute,
    Read,
    Write,
}

/// The physical address `va` reaches for `access` in the tables at `cr3`:
/// a user, present mapping with the rights `access` needs, private exactly
/// for an instruction fetch (MMIO is shared). `private` is SEV's C-bit, set
/// on private leaves; `shared` is TDX's S-bit, set on shared leaves; one of
/// them is 0. Neither is in a returned address, and with TDX no table
/// pointer may carry the S-bit: the VMM could then rewrite that table.
/// `read(pa)` reads the table entry at `pa` through the
/// kernel window, which maps [0, `window_top`): no table outside it is
/// read, and an instruction fetch's address is below it, as the caller
/// reads the instruction through the window as well. Above lie a hole up
/// to 510 GiB, the kernel image's alias at 510 GiB (whose bytes would be
/// decoded as the user's instruction), and from 512 GiB `pptr` wraps into
/// the lower half; a private device frame can lie there. MMIO addresses go
/// to the hypervisor and may lie anywhere.
pub fn translate(
    va: u64,
    access: Access,
    cr3: u64,
    private: u64,
    shared: u64,
    user_top: u64,
    window_top: u64,
    read: impl Fn(u64) -> u64,
) -> Option<u64> {
    if va > user_top {
        return None;
    }
    let visibility = private | shared;
    let mut table = cr3 & ADDR & !visibility;
    for shift in [39, 30, 21, 12] {
        if table.checked_add(4096).is_none_or(|end| end > window_top) {
            return None;
        }
        let e = read(table + ((va >> shift) & 511) * 8);
        if e & (PRESENT | USER) != PRESENT | USER
            || matches!(access, Access::Write) && e & WRITE == 0
            || matches!(access, Access::Execute) && e & NX != 0
        {
            return None;
        }
        let pa = e & ADDR & !visibility;
        if shift == 12 || (shift == 21 || shift == 30) && e & HUGE != 0 {
            let is_private = if shared != 0 { e & shared == 0 } else { e & private != 0 };
            if is_private != matches!(access, Access::Execute) {
                return None;
            }
            let offset = (1 << shift) - 1;
            let pa = (pa & !offset) | (va & offset);
            if matches!(access, Access::Execute) && pa >= window_top {
                return None;
            }
            return Some(pa);
        }
        if e & shared != 0 {
            return None;
        }
        table = pa;
    }
    None
}
