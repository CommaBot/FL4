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
