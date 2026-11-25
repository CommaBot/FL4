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

fn load_keys_incremental(pc: &percpu::PerCpu, tcb: u64, flags: u64) -> bool {
    use fl4_abi::consts::pac_flag;
    let k = |i: u64| unsafe { core::ptr::read_volatile((tcb + tl::PAC_KEYS + i * 8) as *const u64) };
    let mut cached = pc.pac_keys.get();
    let valid = pc.pac_keys_valid.get();
    let mut wrote = false;

    if flags & pac_flag::EN_IA != 0 {
        let lo = k(0);
        let hi = k(1);
        if !valid || cached[0] != lo || cached[1] != hi {
            crate::msr!("s3_0_c2_c1_0", lo); // APIAKeyLo_EL1
            crate::msr!("s3_0_c2_c1_1", hi); // APIAKeyHi_EL1
            cached[0] = lo;
            cached[1] = hi;
            wrote = true;
        }
    }
    if flags & pac_flag::EN_IB != 0 {
        let lo = k(2);
        let hi = k(3);
        if !valid || cached[2] != lo || cached[3] != hi {
            crate::msr!("s3_0_c2_c1_2", lo); // APIBKeyLo_EL1
            crate::msr!("s3_0_c2_c1_3", hi); // APIBKeyHi_EL1
            cached[2] = lo;
            cached[3] = hi;
            wrote = true;
        }
    }
    if flags & pac_flag::EN_DA != 0 {
        let lo = k(4);
        let hi = k(5);
        if !valid || cached[4] != lo || cached[5] != hi {
            crate::msr!("s3_0_c2_c2_0", lo); // APDAKeyLo_EL1
            crate::msr!("s3_0_c2_c2_1", hi); // APDAKeyHi_EL1
            cached[4] = lo;
            cached[5] = hi;
            wrote = true;
        }
    }
    if flags & pac_flag::EN_DB != 0 {
        let lo = k(6);
        let hi = k(7);
        if !valid || cached[6] != lo || cached[7] != hi {
            crate::msr!("s3_0_c2_c2_2", lo); // APDBKeyLo_EL1
            crate::msr!("s3_0_c2_c2_3", hi); // APDBKeyHi_EL1
            cached[6] = lo;
            cached[7] = hi;
            wrote = true;
        }
    }
    // APGA is not governed by an SCTLR enable bit, so always keep it synced.
    let ga_lo = k(8);
    let ga_hi = k(9);
    if !valid || cached[8] != ga_lo || cached[9] != ga_hi {
        crate::msr!("s3_0_c2_c3_0", ga_lo); // APGAKeyLo_EL1
        crate::msr!("s3_0_c2_c3_1", ga_hi); // APGAKeyHi_EL1
        cached[8] = ga_lo;
        cached[9] = ga_hi;
        wrote = true;
    }

    if wrote {
        pc.pac_keys.set(cached);
    }
    // A disabled pair keeps whatever the cache says hardware holds: it
    // cannot sign or authenticate until enabled, and enabling it again
    // compares and loads it here first. `switch_to` loads all 10 words while
    // the cache is invalid, so it is valid for every word from then on.
    wrote
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
            pc.pac_keys_valid.set(false);
        }
        cpu::isb();
        return;
    }
    let mut dirty = false;
    let epoch = unsafe { core::ptr::read_volatile((tcb + tl::PAC_EPOCH) as *const u64) };
    if pc.pac_owner.get() != tcb || pc.pac_epoch.get() != epoch {
        if !pc.pac_keys_valid.get() {
            // Cold cache: load all 10 words once so every pair in `pac_keys`
            // matches hardware, then future switches only touch changed pairs.
            let k = |i: u64| unsafe { core::ptr::read_volatile((tcb + tl::PAC_KEYS + i * 8) as *const u64) };
            let keys = [k(0), k(1), k(2), k(3), k(4), k(5), k(6), k(7), k(8), k(9)];
            crate::msr!("s3_0_c2_c1_0", keys[0]);
            crate::msr!("s3_0_c2_c1_1", keys[1]);
            crate::msr!("s3_0_c2_c1_2", keys[2]);
            crate::msr!("s3_0_c2_c1_3", keys[3]);
            crate::msr!("s3_0_c2_c2_0", keys[4]);
            crate::msr!("s3_0_c2_c2_1", keys[5]);
            crate::msr!("s3_0_c2_c2_2", keys[6]);
            crate::msr!("s3_0_c2_c2_3", keys[7]);
            crate::msr!("s3_0_c2_c3_0", keys[8]);
            crate::msr!("s3_0_c2_c3_1", keys[9]);
            pc.pac_keys.set(keys);
            pc.pac_keys_valid.set(true);
            dirty = true;
        } else if load_keys_incremental(pc, tcb, flags) {
            dirty = true;
        }
        pc.pac_owner.set(tcb);
        pc.pac_epoch.set(epoch);
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
