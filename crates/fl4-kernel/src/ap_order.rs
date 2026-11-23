//! The order `smp::start_aps` brings the application processors up in.
//! Free of hardware access, so the backend's host tests run it.

/// The cores to start, as `(cpu index, APIC ID)` with indices from 1, in
/// MADT order: each `eligible(i, id)` listing until `max` cores, the boot
/// core included, would run or `out` is full. Returns the entries filled.
pub fn select(
    apic_ids: &[u32],
    max: usize,
    mut eligible: impl FnMut(usize, u32) -> bool,
    out: &mut [(usize, u32)],
) -> usize {
    let mut n = 0;
    for (i, &id) in apic_ids.iter().enumerate() {
        if n + 1 >= max || n >= out.len() {
            break;
        }
        if eligible(i, id) {
            out[n] = (n + 1, id);
            n += 1;
        }
    }
    n
}

/// Start `aps` one after another. Under SEV-SNP each AP's page-state
/// changes (`prepare`: its GHCB page becoming shared, its VMSA page
/// becoming a VMSA) all happen first, while only the boot core runs.
/// A started AP waits at the boot barrier with interrupts off, so it
/// cannot take the remote invalidation an RMP change needs (sev.rs
/// `steps`), and the kernel windows map every AP's pages with global
/// large pages that it may already hold in its TLB. Without SNP nothing
/// is prepared.
pub fn bring_up(
    aps: &[(usize, u32)],
    snp: bool,
    mut prepare: impl FnMut(usize, u32),
    mut start: impl FnMut(usize, u32),
) {
    if snp {
        for &(c, id) in aps {
            prepare(c, id);
        }
    }
    for &(c, id) in aps {
        start(c, id);
    }
}

/// Whether a TD may start `cores` cores (the boot core included) with
/// `vcpus` vCPUs and a kernel limit of `max`: every vCPU, so that none
/// stays in firmware out of the kernel's hands, and so no more vCPUs than
/// the kernel can run.
pub fn tdx_cores_match(cores: usize, vcpus: usize, max: usize) -> bool {
    vcpus >= 1 && vcpus <= max && cores == vcpus
}

/// How a started core came up (`wait_start`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Started {
    /// The guest is poisoned (a TDX AP was rejected): stop at once.
    Poisoned,
    /// The core refused this reason (`smp::reject_ap`).
    Rejected(u8),
    Online,
    TimedOut,
}

/// Wait for a core to come up: poison first, on every pass and even when
/// the core is online before the first, then a rejection, then the core
/// online, then the deadline.
pub fn wait_start(
    poisoned: impl Fn() -> bool,
    rejected: impl Fn() -> u8,
    online: impl Fn() -> bool,
    expired: impl Fn() -> bool,
) -> Started {
    loop {
        if poisoned() {
            return Started::Poisoned;
        }
        match rejected() {
            0 => {}
            r => return Started::Rejected(r),
        }
        if online() {
            return Started::Online;
        }
        if expired() {
            return Started::TimedOut;
        }
        core::hint::spin_loop();
    }
}

/// The next piece of the memory being accepted for this core to take
/// (`smp::help_accept`): none once the guest is poisoned, when nothing is
/// taken, or once every piece is.
pub fn next_accept_chunk(poisoned: bool, next: &core::sync::atomic::AtomicU64, chunks: u64) -> Option<u64> {
    use core::sync::atomic::Ordering::Relaxed;
    if poisoned || next.load(Relaxed) >= chunks {
        return None;
    }
    let index = next.fetch_add(1, Relaxed);
    (index < chunks).then_some(index)
}
