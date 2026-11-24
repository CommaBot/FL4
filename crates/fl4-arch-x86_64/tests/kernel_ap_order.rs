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

/// Audit (TDX r1, fix 1; r2, R1-2): a TD starts every vCPU it has, so that
/// none stays in firmware out of the kernel's hands (the VMM writes the
/// MADT and could otherwise hold one back), and so does not boot with more
/// vCPUs than the kernel can run.
#[test]
fn a_td_starts_every_vcpu_and_no_more() {
    assert!(ap_order::tdx_cores_match(1, 1, 64));
    assert!(ap_order::tdx_cores_match(4, 4, 64));
    assert!(ap_order::tdx_cores_match(64, 64, 64));
    // More cores than vCPUs.
    assert!(!ap_order::tdx_cores_match(2, 1, 64));
    assert!(!ap_order::tdx_cores_match(5, 4, 64));
    // A vCPU left out of the MADT (or filtered out).
    assert!(!ap_order::tdx_cores_match(3, 4, 64));
    assert!(!ap_order::tdx_cores_match(1, 2, 64));
    // More vCPUs than the kernel runs: refused, not left parked.
    assert!(!ap_order::tdx_cores_match(64, 100, 64));
    assert!(!ap_order::tdx_cores_match(64, 65, 64));
    assert!(!ap_order::tdx_cores_match(0, 0, 64));
}

/// Audit (TDX r2, R1-6): the boot core stops on a poisoned guest first,
/// on every pass and even when the core it started is already online.
#[test]
fn a_poisoned_guest_stops_the_wait_before_anything_else() {
    use ap_order::{wait_start, Started};
    use std::cell::Cell;
    // Online before the first look, and poisoned: poisoned.
    assert_eq!(wait_start(|| true, || 0, || true, || false), Started::Poisoned);
    assert_eq!(wait_start(|| true, || 3, || true, || true), Started::Poisoned);
    // Poisoned while waiting.
    let passes = Cell::new(0);
    let r = wait_start(|| { passes.set(passes.get() + 1); passes.get() > 3 }, || 0, || false, || false);
    assert_eq!((r, passes.get()), (Started::Poisoned, 4));
    // Otherwise a rejection, then online, then the deadline.
    assert_eq!(wait_start(|| false, || 2, || true, || true), Started::Rejected(2));
    assert_eq!(wait_start(|| false, || 0, || true, || true), Started::Online);
    assert_eq!(wait_start(|| false, || 0, || false, || true), Started::TimedOut);
}

/// The checks around it in `start_aps`: before any core starts, and the
/// boot core stops as soon as the guest is poisoned, at every point it
/// commits to something.
#[test]
fn start_aps_checks_tdx_cores_first_and_stops_on_poison() {
    let at = SMP.find("pub fn start_aps(").unwrap();
    let f = &SMP[at..at + SMP[at..].find("\n}\n").unwrap()];
    let check = f.find("ap_order::tdx_cores_match(n + 1, vcpus, max)").expect("check");
    let bring = f.find("crate::ap_order::bring_up(").unwrap();
    assert!(check < bring);
    let start = &f[f.find("}, |c, id| {").unwrap()..];
    assert!(start.trim_start_matches("}, |c, id| {").trim_start().starts_with("halt_if_poisoned();"), "before each wakeup");
    let wait = start.find("crate::ap_order::wait_start(").unwrap();
    assert!(start[wait..].contains("fl4_arch_x86_64::cvm::poisoned,"));
    let after = wait + start[wait..].find(");\n").unwrap();
    assert!(start[after..].trim_start_matches(");").trim_start().starts_with("halt_if_poisoned();"), "after the wait");
    let finish = f.find("crate::tdx::finish_wakeup();").unwrap();
    assert!(f[..finish].trim_end().ends_with("if f.tdx_wakeup.is_some() {"));
    let tail = &f[f.rfind("crate::fail(\"AP startup timed out").unwrap()..];
    let (before_finish, after_finish) = tail.split_at(tail.find("crate::tdx::finish_wakeup();").unwrap());
    assert!(before_finish.contains("halt_if_poisoned();") && after_finish.contains("halt_if_poisoned();"));
    for loop_of in ["pub fn accept_memory(", "pub fn sync_patched_text("] {
        let g = &SMP[SMP.find(loop_of).unwrap()..];
        let g = &g[..g.find("\n}\n").unwrap()];
        let w = g.find("    while ").unwrap();
        assert!(g[..w].trim_end().ends_with("halt_if_poisoned();"), "{loop_of} before its loop");
        assert!(g[w..].lines().nth(1).unwrap().trim() == "halt_if_poisoned();", "{loop_of} in its loop");
    }
    let main = &SMP[SMP.find("extern \"C\" fn fl4_ap_main(").unwrap()..];
    let idt = main.find("gdt::load_boot_idt();").unwrap();
    let reg = main.find("fl4_arch_x86_64::tdx::register_ap();").expect("register_ap");
    assert!(idt < reg && reg < main.find("cpu::write_cr3(paging::root_paddr())").unwrap());
    // The core the VMM woke must be the one the boot core asked for, by
    // the one ID it reads (audit TDX r3, R2-1), checked before it is kept.
    let main = &main[..main.find("\n}\n").unwrap()];
    assert_eq!(main.matches("apic::id()").count(), 1, "read once");
    let read = main.find("let apic_id = apic::id();").expect("one read");
    let check = main.find("apic_id != WOKEN_APIC_ID[c as usize].load(Ordering::Acquire)").expect("APIC ID check");
    let reject = main.find("reject_ap(REJECT_APIC_ID);").unwrap();
    let keep = main.find("percpu::set_apic_id(apic_id);").expect("the checked ID kept");
    assert!(read < check && check < reject && reject < keep && keep < main.find("smp::set_online(c as usize);").unwrap());
    assert!(start.find("WOKEN_APIC_ID[c].store(id, Ordering::Release);").unwrap() < start.find("crate::tdx::start_ap(w, c, id);").unwrap());
}

/// Audit (TDX r3, R2-5): a poisoned guest takes no more memory to accept:
/// no piece is taken (the counter stays), and none past the last.
#[test]
fn a_poisoned_guest_takes_no_piece_to_accept() {
    use std::sync::atomic::{AtomicU64, Ordering};
    let next = AtomicU64::new(0);
    assert_eq!(ap_order::next_accept_chunk(true, &next, 4), None);
    assert_eq!(next.load(Ordering::Relaxed), 0, "nothing taken");
    assert_eq!(ap_order::next_accept_chunk(false, &next, 4), Some(0));
    assert_eq!(ap_order::next_accept_chunk(false, &next, 4), Some(1));
    assert_eq!(ap_order::next_accept_chunk(true, &next, 4), None);
    assert_eq!(next.load(Ordering::Relaxed), 2);
    assert_eq!(ap_order::next_accept_chunk(false, &next, 4), Some(2));
    assert_eq!(ap_order::next_accept_chunk(false, &next, 4), Some(3));
    assert_eq!(ap_order::next_accept_chunk(false, &next, 4), None);
    assert_eq!(next.load(Ordering::Relaxed), 4, "no claim once all are taken");
    // A claim that raced past the last piece is none either.
    let next = AtomicU64::new(9);
    assert_eq!(ap_order::next_accept_chunk(false, &next, 4), None);
    // In the kernel: poison is checked before anything is published, before
    // each claim, and in the TDX module call's own loop.
    let accept = &SMP[SMP.find("pub fn accept_memory(").unwrap()..];
    assert!(accept.find("halt_if_poisoned();").unwrap() < accept.find("ACCEPT_CHUNKS.store(").unwrap());
    let help = &SMP[SMP.find("fn help_accept() {").unwrap()..];
    let help = &help[..help.find("\n}\n").unwrap()];
    let l = help.find("    loop {\n        halt_if_poisoned();\n        let Some(index) = crate::ap_order::next_accept_chunk(fl4_arch_x86_64::cvm::poisoned(), &ACCEPT_NEXT, chunks) else { break };").expect("claim loop");
    assert!(!help[..l].contains("ACCEPT_NEXT.fetch_add") && !help[l..].contains("ACCEPT_NEXT.fetch_add"));
    let tdx = include_str!("../src/tdx.rs");
    let pages = &tdx[tdx.find("pub fn accept_pages(").unwrap()..];
    let w = pages.find("    while cur < end {\n").unwrap();
    assert!(pages[w..].lines().skip(1).take(3).any(|l| l.trim() == "cvm::halt_if_poisoned();"));
}
