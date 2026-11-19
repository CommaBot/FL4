//! The SEV-SNP user #VC handler's walk of the current user page tables
//! (snp.rs `user_vc`), as a plain function so host tests run it
//! (xtask/tests/snp_walk.rs).

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

/// The physical address `va` reaches for `access` in the tables at `cr3`,
/// whose private (C-bit) mask is `private`: a user, present mapping with
/// the rights `access` needs, private exactly for an instruction fetch
/// (MMIO is shared). `read(pa)` reads the table entry at `pa` through the
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
    user_top: u64,
    window_top: u64,
    read: impl Fn(u64) -> u64,
) -> Option<u64> {
    if va > user_top {
        return None;
    }
    let mut table = cr3 & ADDR & !private;
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
        let pa = e & ADDR & !private;
        if shift == 12 || (shift == 21 || shift == 30) && e & HUGE != 0 {
            if (e & private != 0) != matches!(access, Access::Execute) {
                return None;
            }
            let offset = (1 << shift) - 1;
            let pa = (pa & !offset) | (va & offset);
            if matches!(access, Access::Execute) && pa >= window_top {
                return None;
            }
            return Some(pa);
        }
        table = pa;
    }
    None
}
