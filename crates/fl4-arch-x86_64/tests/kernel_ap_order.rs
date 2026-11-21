//! Audit r12 F2: under SEV-SNP the boot core changes the RMP state of
//! every AP's GHCB (private to shared) and VMSA pages. A started AP waits
//! at the boot barrier with interrupts off, so it cannot take the remote
//! invalidation such a change needs, while the kernel windows map all of
//! `APS` with global large pages it may hold. Every change must therefore
//! happen before the first AP starts.
#![cfg(target_arch = "x86_64")]

#[allow(dead_code)]
#[path = "../../fl4-kernel/src/ap_order.rs"]
mod ap_order;

const SMP: &str = include_str!("../../fl4-kernel/src/smp.rs");
const SNP: &str = include_str!("../../fl4-kernel/src/snp.rs");

#[derive(Debug, PartialEq, Clone, Copy)]
enum Ev {
    Prepare(usize, u32),
    Start(usize, u32),
}

fn record(aps: &[(usize, u32)], snp: bool) -> Vec<Ev> {
    let log = std::cell::RefCell::new(Vec::new());
    ap_order::bring_up(
        aps,
        snp,
        |c, id| log.borrow_mut().push(Ev::Prepare(c, id)),
        |c, id| log.borrow_mut().push(Ev::Start(c, id)),
    );
    log.into_inner()
}

#[test]
fn snp_prepares_every_ap_before_starting_any() {
    let aps = [(1, 2), (2, 4), (3, 6)];
    let log = record(&aps, true);
    assert_eq!(log.len(), 6);
    let first_start = log.iter().position(|e| matches!(e, Ev::Start(..))).unwrap();
    assert!(log[..first_start].iter().all(|e| matches!(e, Ev::Prepare(..))));
    assert_eq!(first_start, aps.len());
    for (i, &(c, id)) in aps.iter().enumerate() {
        assert_eq!(log[i], Ev::Prepare(c, id));
        assert_eq!(log[aps.len() + i], Ev::Start(c, id));
    }
    // Without SNP there is no page state to change.
    assert_eq!(record(&aps, false), aps.iter().map(|&(c, id)| Ev::Start(c, id)).collect::<Vec<_>>());
    assert!(record(&[], true).is_empty());
}

#[test]
fn ap_selection_numbers_eligible_cores_up_to_the_limit() {
    let ids = [0, 2, 3, 2, 4, 6, 8];
    let mut out = [(0, 0); 8];
    // The boot core (0) and an ineligible core (3) are skipped; indices
    // stay dense; `max` counts the boot core.
    let n = ap_order::select(&ids, 4, |i, id| id != 0 && id != 3 && !ids[..i].contains(&id), &mut out);
    assert_eq!(&out[..n], &[(1, 2), (2, 4), (3, 6)]);
    let n = ap_order::select(&ids, 64, |_, id| id != 0, &mut out[..2]);
    assert_eq!(&out[..n], &[(1, 2), (2, 3)]);
    assert_eq!(ap_order::select(&ids, 1, |_, _| true, &mut out), 0);
}

/// The kernel uses the ordered bring-up, and `start_ap` itself changes no
/// page state (no PVALIDATE/PSC through `prepare_cpu`, no RMPADJUST).
#[test]
fn kernel_starts_snp_aps_only_after_all_page_state_changes() {
    let body = |src: &'static str, sig: &str| {
        let at = src.find(sig).unwrap_or_else(|| panic!("{sig} missing"));
        &src[at..at + src[at..].find("\n}\n").unwrap()]
    };
    let start_aps = body(SMP, "pub fn start_aps(");
    assert!(start_aps.contains("crate::ap_order::bring_up(&aps[..n], snp_guest,"), "{start_aps}");
    let prepare = start_aps.find("crate::snp::prepare_ap(").expect("prepare_ap");
    let start = start_aps.find("crate::snp::start_ap(").expect("start_ap");
    assert!(prepare < start);
    assert_eq!(start_aps.matches("crate::snp::").count(), 2);
    let start_ap = body(SNP, "pub fn start_ap(");
    for forbidden in ["prepare_cpu", "rmpadjust", "transition"] {
        assert!(!start_ap.contains(forbidden), "{forbidden} in start_ap");
    }
    let prepare_ap = body(SNP, "pub fn prepare_ap(");
    assert!(prepare_ap.contains("snp::prepare_cpu(") && prepare_ap.contains("rmpadjust"));
    assert!(!prepare_ap.contains("start_cpu"));
}
