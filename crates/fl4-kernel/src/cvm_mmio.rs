//! Emulating a user program's MMIO access for an SEV-SNP (#VC) or TDX (#VE)
//! guest: decode the faulting instruction from its private code, check the
//! access against the program's own page tables, and do it through the
//! host. No address the host supplies is used.
use crate::cvm_walk::Access;
use crate::entry::Frame;
use fl4_arch_x86_64::cvm::mmio;

/// The instruction after one of `length` bytes at `rip`, within user space.
pub fn user_next_rip(rip: u64, length: u64) -> Option<u64> {
    rip.checked_add(length)
        .filter(|&next| next <= fl4_abi::consts::USER_TOP)
}

/// Emulate the MMIO instruction at `f.rip`, if it is one. `translate` is the
/// walk of the running thread's tables (see `cvm_walk::translate`), and
/// `io(pa, bytes, value)` makes the access: a store of `value`, or with
/// None a load. Returns false, changing nothing, for anything else.
pub fn user_mmio(
    f: &mut Frame,
    translate: impl Fn(u64, Access) -> Option<u64>,
    io: impl Fn(u64, u64, Option<u64>) -> u64,
) -> bool {
    use fl4_core::layout::pptr;
    let rip = f.rip;
    let fetch = |off| {
        let pa = translate(rip.checked_add(off)?, Access::Execute)?;
        Some(unsafe { (pptr(pa) as *const u8).read_volatile() })
    };
    let gprs = [
        &mut f.rax, &mut f.rcx, &mut f.rdx, &mut f.rbx, &mut f.rsp, &mut f.rbp, &mut f.rsi,
        &mut f.rdi, &mut f.r8, &mut f.r9, &mut f.r10, &mut f.r11, &mut f.r12, &mut f.r13,
        &mut f.r14, &mut f.r15,
    ];
    let values = core::array::from_fn(|i| *gprs[i]);
    let Some(access) = mmio::decode(rip, &values, fetch) else {
        return false;
    };
    let Some(next) = user_next_rip(rip, access.length) else {
        return false;
    };
    // Never let a single host operation cross a page boundary. Consult
    // the guest's own mappings instead of any address supplied by the VMM.
    if (access.address & 4095) + access.bytes > 4096 {
        return false;
    }
    let mode = match access.op {
        mmio::Operation::Write(_) => Access::Write,
        mmio::Operation::Read { .. } => Access::Read,
    };
    let Some(pa) = translate(access.address, mode) else {
        return false;
    };
    let mask = u64::MAX >> (64 - 8 * access.bytes);
    match access.op {
        mmio::Operation::Write(value) => {
            io(pa, access.bytes, Some(value & mask));
        }
        mmio::Operation::Read {
            register,
            shift,
            dest_bytes,
        } => {
            let value = io(pa, access.bytes, None) & mask;
            *gprs[register] = if dest_bytes >= 4 {
                value
            } else {
                let dest_mask = u64::MAX >> (64 - 8 * dest_bytes);
                (values[register] & !(dest_mask << shift)) | (value << shift)
            };
        }
    }
    f.rip = next;
    true
}
