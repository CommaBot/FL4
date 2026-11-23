//! Per-thread pointer authentication (`TCBSetPACKeys`), switched lazily.
//!
//! A thread's TCB holds its SCTLR_EL1 enables (EnIA, EnIB, EnDA, EnDB) and
//! its five keys, with a key generation that `TCBSetPACKeys` takes from
//! `next_epoch` (never reused). A core remembers whose keys (TCB and
//! generation) its key registers hold and which enables SCTLR_EL1 has, and
//! on the way to a thread writes only what differs: between threads
//! without pointer authentication nothing at all.
//!
//! With its enables clear a thread's PAC* and AUT* instructions leave
//! pointers as they are, whatever keys are loaded; PACGA, which no enable
//! governs, would still compute with the loaded APGA key. So a core that
//! goes from a thread's keys to a thread without pointer authentication
//! clears the APGA key, as boot did (boot.S), and forgets the owner: the
//! next thread with keys loads all ten.
//!
//! The kernel itself has no PAC instructions, so the enables (which also
//! govern EL1, or EL2 in VHE mode) never change what it runs. A VCPU
//! thread runs with the enables clear and the APGA key zero: in nVHE mode
//! the EL2 stub restores the host's boot SCTLR_EL1 when a guest exits, and
//! guests trap PAC instructions (HCR_EL2.API clear for them).
use crate::{cpu, percpu};
use core::sync::atomic::{AtomicU64, Ordering};
use fl4_core::layout::tcb as tl;

/// SCTLR_EL1 (SCTLR_EL2 in VHE mode) EnIA, EnIB, EnDA and EnDB.
const SCTLR_EN_IA: u64 = 1 << 31;
const SCTLR_EN_IB: u64 = 1 << 30;
const SCTLR_EN_DA: u64 = 1 << 27;
const SCTLR_EN_DB: u64 = 1 << 13;
const SCTLR_EN_ALL: u64 = SCTLR_EN_IA | SCTLR_EN_IB | SCTLR_EN_DA | SCTLR_EN_DB;

/// Key generations handed out so far; 0 is no thread's.
static NEXT_EPOCH: AtomicU64 = AtomicU64::new(1);

/// A key generation no thread has had (`Arch::next_pac_epoch`).
pub fn next_epoch() -> u64 {
    NEXT_EPOCH.fetch_add(1, Ordering::Relaxed)
}

/// The SCTLR enable bits of `pac_flag` bits `flags`.
pub fn sctlr_bits(flags: u64) -> u64 {
    use fl4_abi::consts::pac_flag;
    let mut v = 0;
    if flags & pac_flag::EN_IA != 0 {
        v |= SCTLR_EN_IA;
    }
    if flags & pac_flag::EN_IB != 0 {
        v |= SCTLR_EN_IB;
    }
    if flags & pac_flag::EN_DA != 0 {
        v |= SCTLR_EN_DA;
    }
    if flags & pac_flag::EN_DB != 0 {
        v |= SCTLR_EN_DB;
    }
    v
}

fn set_enables(flags: u64) {
    let v = crate::mrs!("sctlr_el1");
    crate::msr!("sctlr_el1", (v & !SCTLR_EN_ALL) | sctlr_bits(flags));
}

fn load_keys(tcb: u64) {
    let k = |i: u64| unsafe { core::ptr::read_volatile((tcb + tl::PAC_KEYS + i * 8) as *const u64) };
    crate::msr!("s3_0_c2_c1_0", k(0)); // APIAKeyLo_EL1
    crate::msr!("s3_0_c2_c1_1", k(1)); // APIAKeyHi_EL1
    crate::msr!("s3_0_c2_c1_2", k(2)); // APIBKeyLo_EL1
    crate::msr!("s3_0_c2_c1_3", k(3)); // APIBKeyHi_EL1
    crate::msr!("s3_0_c2_c2_0", k(4)); // APDAKeyLo_EL1
    crate::msr!("s3_0_c2_c2_1", k(5)); // APDAKeyHi_EL1
    crate::msr!("s3_0_c2_c2_2", k(6)); // APDBKeyLo_EL1
    crate::msr!("s3_0_c2_c2_3", k(7)); // APDBKeyHi_EL1
    crate::msr!("s3_0_c2_c3_0", k(8)); // APGAKeyLo_EL1
    crate::msr!("s3_0_c2_c3_1", k(9)); // APGAKeyHi_EL1
}

/// Run the thread whose TCB is at `tcb` (0: the idle thread or a VCPU
/// thread, as one without pointer authentication) with its enables and
/// keys. Exit path, interrupts masked.
#[inline]
pub fn switch_to(tcb: u64) {
    if !cpu::has_pauth() {
        return;
    }
    let pc = percpu::get();
    let flags = if tcb == 0 {
        0
    } else {
        let f = unsafe { core::ptr::read_volatile((tcb + tl::PAC_FLAGS) as *const u64) };
        f & fl4_abi::consts::pac_flag::MASK
    };
    if flags == 0 {
        if pc.pac_flags.get() == 0 && pc.pac_owner.get() == 0 {
            return;
        }
        if pc.pac_flags.get() != 0 {
            set_enables(0);
            pc.pac_flags.set(0);
        }
        if pc.pac_owner.get() != 0 {
            crate::msr!("s3_0_c2_c3_0", 0); // APGAKeyLo_EL1
            crate::msr!("s3_0_c2_c3_1", 0); // APGAKeyHi_EL1
            pc.pac_owner.set(0);
            pc.pac_epoch.set(0);
        }
        cpu::isb();
        return;
    }
    let mut dirty = false;
    let epoch = unsafe { core::ptr::read_volatile((tcb + tl::PAC_EPOCH) as *const u64) };
    if pc.pac_owner.get() != tcb || pc.pac_epoch.get() != epoch {
        load_keys(tcb);
        pc.pac_owner.set(tcb);
        pc.pac_epoch.set(epoch);
        dirty = true;
    }
    if pc.pac_flags.get() != flags {
        set_enables(flags);
        pc.pac_flags.set(flags);
        dirty = true;
    }
    if dirty {
        cpu::isb();
    }
}
