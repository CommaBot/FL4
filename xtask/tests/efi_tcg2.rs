//! The UEFI loader's TPM event log (fl4-efi tcg2.rs, used by x86.rs
//! `boot` and lib.rs `start_default`): the exact length of the log
//! GetEventLog names, and the events the final events table gains after
//! the copy, appended whole without the ones the copy already holds. All
//! of it is firmware memory: what does not parse is refused, never read
//! past or panicked on.
#[allow(dead_code)]
#[path = "../../crates/fl4-efi/src/tcg2.rs"]
mod tcg2;

use tcg2::{AlgTable, FinalSnapshot};

const SHA1: u16 = 0x0004;
const SHA256: u16 = 0x000b;
const SHA384: u16 = 0x000c;
const BANKS: [(u16, u16); 3] = [(SHA1, 20), (SHA256, 32), (SHA384, 48)];

fn le32(v: &mut Vec<u8>, x: u32) {
    v.extend_from_slice(&x.to_le_bytes());
}

/// The Spec ID event (a legacy TCG_PCR_EVENT) listing `algs`.
fn spec_id_event(algs: &[(u16, u16)]) -> Vec<u8> {
    let mut ev = b"Spec ID Event03\0".to_vec();
    le32(&mut ev, 0); // platform class
    ev.extend_from_slice(&[0, 2, 0, 2]); // minor, major, errata, uintn size
    le32(&mut ev, algs.len() as u32);
    for &(a, s) in algs {
        ev.extend_from_slice(&a.to_le_bytes());
        ev.extend_from_slice(&s.to_le_bytes());
    }
    ev.push(0); // vendor info size
    let mut v = Vec::new();
    le32(&mut v, 0);
    le32(&mut v, 3);
    v.extend_from_slice(&[0; 20]);
    le32(&mut v, ev.len() as u32);
    v.extend_from_slice(&ev);
    v
}

/// A TCG_PCR_EVENT2 with a digest per bank in `algs` and `data`.
fn event2(pcr: u32, ty: u32, algs: &[(u16, u16)], data: &[u8]) -> Vec<u8> {
    let mut v = Vec::new();
    le32(&mut v, pcr);
    le32(&mut v, ty);
    le32(&mut v, algs.len() as u32);
    for &(a, s) in algs {
        v.extend_from_slice(&a.to_le_bytes());
        v.extend((0..s).map(|i| (i as u8) ^ pcr as u8));
    }
    le32(&mut v, data.len() as u32);
    v.extend_from_slice(data);
    v
}

/// A log: the Spec ID event, then `n` events; with the offset of the last.
fn log(algs: &[(u16, u16)], n: usize) -> (Vec<u8>, usize) {
    let mut v = spec_id_event(algs);
    let mut last = 0;
    for i in 0..n {
        last = v.len();
        v.extend(event2(i as u32 % 24, 0x8000_0001 + i as u32, algs, &vec![i as u8; 10 + i * 7]));
    }
    (v, last)
}

fn table(algs: &[(u16, u16)]) -> AlgTable {
    let mut t = AlgTable::EMPTY;
    t.n = algs.len();
    t.algs[..algs.len()].copy_from_slice(algs);
    t
}

/// A final events table holding `events`.
fn final_table(events: &[Vec<u8>]) -> Vec<u8> {
    let mut v = 1u64.to_le_bytes().to_vec();
    v.extend_from_slice(&(events.len() as u64).to_le_bytes());
    for e in events {
        v.extend_from_slice(e);
    }
    v
}

const LOC: u64 = 0x7e00_0000;

#[test]
fn the_spec_id_event_gives_its_length_and_banks() {
    let ev = spec_id_event(&BANKS);
    let (len, algs) = tcg2::spec_id(&ev[..]).unwrap();
    assert_eq!(len, ev.len());
    assert_eq!(len, 32 + 28 + 4 * 3 + 1);
    assert_eq!(algs, table(&BANKS));
    assert_eq!(algs.digest_size(SHA256), Some(32));
    assert_eq!(algs.digest_size(0x0012), None);
}

#[test]
fn a_multi_bank_event_has_its_exact_length() {
    let algs = table(&BANKS);
    let e = event2(7, 0x8000_0008, &BANKS, b"abcdefg");
    assert_eq!(e.len(), 12 + (2 + 20) + (2 + 32) + (2 + 48) + 4 + 7);
    assert_eq!(tcg2::event2_len(&e[..], 0, &algs), Some(e.len()));
    // Banks in another order, and fewer than the log has.
    let e = event2(0, 1, &[(SHA384, 48), (SHA1, 20)], &[]);
    assert_eq!(tcg2::event2_len(&e[..], 0, &algs), Some(e.len()));
    // At an offset, with more bytes after it.
    let mut v = vec![0xee; 5];
    v.extend(event2(1, 2, &BANKS, b"x"));
    let n = v.len() - 5;
    v.extend([0xff; 100]);
    assert_eq!(tcg2::event2_len(&v[..], 5, &algs), Some(n));
}

#[test]
fn the_main_log_runs_through_its_last_entry() {
    let (v, last) = log(&BANKS, 5);
    let mut mem = v.clone();
    mem.extend([0xcc; 4096]); // what follows the log in firmware memory
    let l = tcg2::main_log(&mem[..], LOC, LOC + last as u64, false).unwrap();
    assert_eq!(l.len, v.len());
    assert_eq!(l.algs, table(&BANKS));
    // Only the Spec ID event: last_entry == location.
    let (v, _) = log(&BANKS[1..2], 0);
    let l = tcg2::main_log(&v[..], LOC, LOC, false).unwrap();
    assert_eq!(l.len, v.len());
    // A TCG 1.2 log: legacy events throughout.
    let mut v = vec![0u8; 32];
    v[28..32].copy_from_slice(&9u32.to_le_bytes());
    v.extend([1; 9]);
    let mut e = vec![0u8; 32];
    e[4] = 1;
    e[28..32].copy_from_slice(&3u32.to_le_bytes());
    v.extend(&e);
    v.extend([2; 3]);
    let l = tcg2::main_log(&v[..], LOC, LOC + 41, true).unwrap();
    assert_eq!(l.len, v.len());
}

#[test]
fn no_log_and_bad_extents_are_refused() {
    let (v, last) = log(&BANKS, 3);
    let last = LOC + last as u64;
    assert_eq!(tcg2::main_log(&v[..], 0, last, false), None);
    assert_eq!(tcg2::main_log(&v[..], LOC, 0, false), None);
    assert_eq!(tcg2::main_log(&v[..], LOC, LOC - 1, false), None, "last entry before the log");
    assert_eq!(tcg2::main_log(&v[..], LOC, LOC + tcg2::MAX_EVENT_LOG as u64, false), None);
    assert_eq!(tcg2::main_log(&v[..], u64::MAX - 4, u64::MAX, false), None);
    // The last entry inside the Spec ID event.
    assert_eq!(tcg2::main_log(&v[..], LOC, LOC + 40, false), None);
    // The log cut short of its last event.
    assert_eq!(tcg2::main_log(&v[..v.len() - 1], LOC, last, false), None);
    // A log that would run past MAX_EVENT_LOG.
    let mut big = spec_id_event(&BANKS);
    let at = big.len();
    let mut e = event2(0, 1, &BANKS[..1], &[]);
    let n = e.len();
    e[n - 4..].copy_from_slice(&(tcg2::MAX_EVENT_LOG as u32).to_le_bytes());
    big.extend(&e);
    big.resize(at + n + tcg2::MAX_EVENT_LOG, 0);
    assert_eq!(tcg2::main_log(&big[..], LOC, LOC + at as u64, false), None);
}

#[test]
fn malformed_spec_id_events_are_refused() {
    let good = spec_id_event(&BANKS);
    let bad = |f: &dyn Fn(&mut Vec<u8>)| {
        let mut v = good.clone();
        f(&mut v);
        tcg2::spec_id(&v[..])
    };
    assert!(bad(&|_| {}).is_some());
    assert_eq!(bad(&|v| v[4] = 1), None, "not EV_NO_ACTION");
    assert_eq!(bad(&|v| v[32] = b's'), None, "signature");
    assert_eq!(bad(&|v| v[32 + 15] = b'!'), None, "signature's NUL");
    assert_eq!(bad(&|v| v[56..60].copy_from_slice(&0u32.to_le_bytes())), None, "no banks");
    assert_eq!(bad(&|v| v[56..60].copy_from_slice(&17u32.to_le_bytes())), None, "too many banks");
    assert_eq!(bad(&|v| v[56..60].copy_from_slice(&u32::MAX.to_le_bytes())), None);
    assert_eq!(bad(&|v| v[56..60].copy_from_slice(&4u32.to_le_bytes())), None, "banks past the event");
    assert_eq!(bad(&|v| v[28..32].copy_from_slice(&20u32.to_le_bytes())), None, "event too short");
    assert_eq!(bad(&|v| v[28..32].copy_from_slice(&u32::MAX.to_le_bytes())), None, "event past the buffer");
    assert_eq!(bad(&|v| v.truncate(31)), None);
    assert_eq!(tcg2::spec_id(&[][..]), None);
}

#[test]
fn malformed_events_are_refused() {
    let algs = table(&BANKS);
    let good = event2(3, 5, &BANKS, b"data");
    let bad = |f: &dyn Fn(&mut Vec<u8>)| {
        let mut v = good.clone();
        f(&mut v);
        tcg2::event2_len(&v[..], 0, &algs)
    };
    assert_eq!(bad(&|_| {}), Some(good.len()));
    assert_eq!(bad(&|v| v[8..12].copy_from_slice(&4u32.to_le_bytes())), None, "more digests than banks");
    assert_eq!(bad(&|v| v[8..12].copy_from_slice(&u32::MAX.to_le_bytes())), None);
    assert_eq!(bad(&|v| v[12..14].copy_from_slice(&0x0012u16.to_le_bytes())), None, "unknown algorithm");
    let n = good.len();
    assert_eq!(bad(&|v| v[n - 8..n - 4].copy_from_slice(&5u32.to_le_bytes())), None, "event past the buffer");
    assert_eq!(bad(&|v| v[n - 8..n - 4].copy_from_slice(&u32::MAX.to_le_bytes())), None);
    for cut in 0..n {
        assert_eq!(tcg2::event2_len(&good[..cut], 0, &algs), None, "cut at {cut}");
    }
    // Zeroed memory is no event.
    assert_eq!(tcg2::event2_len(&[0u8; 64][..], 0, &algs), None);
    // Offsets near usize::MAX do not wrap.
    assert_eq!(tcg2::event2_len(&good[..], usize::MAX - 3, &algs), None);
    assert_eq!(tcg2::event1_len(&good[..], usize::MAX - 20), None);
}

/// Linux's efi_tpm_eventlog_init: the events the table held when the log
/// was taken are in it, so only the rest are appended.
#[test]
fn final_events_after_the_copy_are_appended_once() {
    let algs = table(&BANKS);
    let (main, _) = log(&BANKS, 2);
    let evs: Vec<Vec<u8>> = (0..5).map(|i| event2(i, 0x8000_0007, &BANKS, &vec![0x40 + i as u8; 3 + i as usize])).collect();
    for pre in [0usize, 1, 3] {
        // The table at GetEventLog time, then after ExitBootServices.
        let before = final_table(&evs[..pre]);
        let snap = tcg2::final_snapshot(&before[..], &algs).unwrap();
        assert_eq!(snap, FinalSnapshot { nr_events: pre as u64, bytes: evs[..pre].iter().map(Vec::len).sum() });
        let mut after = final_table(&evs);
        after.extend([0xdd; 64]);
        let mut buf = main.clone();
        buf.resize(main.len() + tcg2::FINAL_SLACK, 0);
        let (len, lost) = tcg2::append_final(&after[..], &algs, &snap, &mut buf, main.len());
        assert!(!lost, "pre {pre}");
        let mut want = main.clone();
        for e in &evs[pre..] {
            want.extend(e);
        }
        assert_eq!(&buf[..len], &want[..], "pre {pre}");
        // Fewer events than at the snapshot: a table that went backwards.
        if pre > 0 {
            let fewer = final_table(&evs[..pre - 1]);
            assert_eq!(tcg2::append_final(&fewer[..], &algs, &snap, &mut buf, main.len()), (main.len(), true), "pre {pre}");
        }
        // Nothing new: nothing appended.
        let (len, lost) = tcg2::append_final(&before[..], &algs, &snap, &mut buf, main.len());
        assert_eq!((len, lost), (main.len(), false));
    }
}

/// Without room for every new event, whole events are appended up to the
/// slack and the log is marked truncated: never half an event.
#[test]
fn final_events_past_the_slack_truncate_whole_events() {
    let algs = table(&BANKS);
    let evs: Vec<Vec<u8>> = (0..4).map(|i| event2(i, 1, &BANKS, &[0x11; 100])).collect();
    let e = evs[0].len();
    let after = final_table(&evs);
    let snap = FinalSnapshot { nr_events: 0, bytes: 0 };
    for room in [0, 1, e - 1, e, e + 1, 2 * e + 7, 4 * e - 1] {
        let mut buf = vec![0u8; 10 + room];
        let (len, lost) = tcg2::append_final(&after[..], &algs, &snap, &mut buf, 10);
        let whole = room / e;
        assert_eq!(len, 10 + whole * e, "room {room}");
        assert!(lost, "room {room}");
        assert!(buf[len..].iter().all(|&b| b == 0), "room {room}: bytes past the last whole event");
        for (i, c) in buf[10..len].chunks(e).enumerate() {
            assert_eq!(c, &evs[i][..]);
        }
    }
    let mut buf = vec![0u8; 10 + 4 * e];
    assert_eq!(tcg2::append_final(&after[..], &algs, &snap, &mut buf, 10), (10 + 4 * e, false));
}

#[test]
fn malformed_final_events_tables_are_refused() {
    let algs = table(&BANKS);
    let evs: Vec<Vec<u8>> = (0..3).map(|i| event2(i, 1, &BANKS, b"x")).collect();
    let good = final_table(&evs);
    assert!(tcg2::final_snapshot(&good[..], &algs).is_some());
    let mut v = good.clone();
    v[0] = 2;
    assert_eq!(tcg2::final_snapshot(&v[..], &algs), None, "version");
    // More events than the table holds, up to 2^64 - 1.
    for nr in [4u64, 1 << 40, u64::MAX] {
        let mut v = good.clone();
        v[8..16].copy_from_slice(&nr.to_le_bytes());
        assert_eq!(tcg2::final_snapshot(&v[..], &algs), None, "{nr}");
    }
    assert_eq!(tcg2::final_snapshot(&good[..15], &algs), None);
    // After ExitBootServices: a table that no longer parses, or whose new
    // event is cut short, appends what is whole and marks the log.
    let snap = tcg2::final_snapshot(&final_table(&evs[..1])[..], &algs).unwrap();
    let mut buf = vec![0u8; 4096];
    let mut v = good.clone();
    v[0] = 0;
    assert_eq!(tcg2::append_final(&v[..], &algs, &snap, &mut buf, 0), (0, true));
    let (len, lost) = tcg2::append_final(&good[..good.len() - 1], &algs, &snap, &mut buf, 0);
    assert_eq!((len, lost), (evs[1].len(), true));
    let mut v = good.clone();
    v[8..16].copy_from_slice(&u64::MAX.to_le_bytes());
    let (len, lost) = tcg2::append_final(&v[..], &algs, &snap, &mut buf, 0);
    assert_eq!((len, lost), (evs[1].len() + evs[2].len(), true));
    // A snapshot past the table.
    let far = FinalSnapshot { nr_events: 1, bytes: usize::MAX };
    assert_eq!(tcg2::append_final(&good[..], &algs, &far, &mut buf, 0), (0, true));
    // A length past the buffer appends nothing.
    assert_eq!(tcg2::append_final(&good[..], &algs, &snap, &mut buf, 5000), (5000, true));
}

#[test]
fn the_flags_and_limits_are_the_abis() {
    use fl4_abi::consts::{bootinfo_header, tpm_event_log_flag};
    assert_eq!(bootinfo_header::TPM_EVENT_LOG, 12);
    assert_eq!(tcg2::TRUNCATED, tpm_event_log_flag::TRUNCATED);
    assert_eq!(tcg2::TCG_1_2, tpm_event_log_flag::TCG_1_2);
    assert_eq!(tcg2::MAX_EVENT_LOG as u64, fl4_bootinfo::MAX_TPM_LOG);
    assert!(tcg2::FINAL_SLACK < tcg2::MAX_EVENT_LOG);
    let mboot = include_str!("../../crates/fl4-kernel/src/mboot.rs");
    assert!(mboot.contains("pub const MAX_TPM_LOG: u64 = 1 << 20;"));
    assert!(mboot.contains("pub const MB2_TAG_TPM_EVENT_LOG: u32 = 0x464c_3401;"));
    let x86 = include_str!("../../crates/fl4-efi/src/x86.rs");
    assert!(x86.contains("const MB2_TAG_TPM_EVENT_LOG: u32 = 0x464c_3401;"));
    let h = include_str!("../../libsel4/include/sel4/bootinfo_types.h");
    assert!(h.contains("SEL4_BOOTINFO_HEADER_TPM_EVENT_LOG      = 12,"));
    assert!(h.contains("#define seL4_TpmEventLog_Truncated (1ul << 0)"));
    assert!(h.contains("#define seL4_TpmEventLog_Tcg12     (1ul << 1)"));
    let t = include_str!("../../crates/fl4-efi/src/tcg2.rs");
    assert!(t.contains("Guid(0x607f_766c, 0x7455, 0x42be, [0x93, 0x0b, 0xe4, 0xd7, 0x6d, 0xb2, 0x72, 0x0f])"));
    assert!(t.contains("Guid(0x1e2e_d096, 0x30e2, 0x4254, [0xbd, 0x89, 0x86, 0x3b, 0xbe, 0xf8, 0x23, 0x25])"));
}

/// A missing or broken log never stops the boot: `collect` has no `fail`.
#[test]
fn collecting_the_log_cannot_fail_the_boot() {
    let t = include_str!("../../crates/fl4-efi/src/tcg2.rs");
    let efi = &t[t.find("mod efi {").expect("efi glue")..];
    assert!(!efi.contains("fail("));
    assert!(!efi.contains("panic!") && !efi.contains(".unwrap()") && !efi.contains(".expect("));
    // finish runs without boot services: no console either.
    let finish = &efi[efi.find("pub fn finish(").unwrap()..];
    let finish = &finish[..finish.find("\n        }\n").unwrap()];
    assert!(!finish.contains("say!") && !finish.contains("bs()"));
}

/// x86: the tag goes among the fixed tags (before `tags_end`), the copy
/// before ExitBootServices, the final events after it and before the jump.
#[test]
fn the_x86_loader_finishes_the_log_after_exit_boot_services() {
    let x86 = include_str!("../../crates/fl4-efi/src/x86.rs");
    let body = &x86[x86.find("pub(super) fn boot(").expect("boot")..];
    let at = |s: &str| body.find(s).unwrap_or_else(|| panic!("{s}"));
    assert!(at("tcg2::collect()") < at("let len = "));
    assert!(at("t.copy_main(tpm_dst)") < at("(bs().exit_boot_services)"));
    assert!(at("info.tag(MB2_TAG_TPM_EVENT_LOG, 24)") < at("let tags_end = info.used"));
    let finish = at("t.finish(tpm_dst)");
    assert!(at("(bs().exit_boot_services)") < finish);
    assert!(finish < at("\"cli\","));
}

/// AArch64: the copy before ExitBootServices, the final events after it,
/// before the boot record and the log are cleaned to memory.
#[test]
fn the_aarch64_loader_finishes_the_log_before_cleaning() {
    let lib = include_str!("../../crates/fl4-efi/src/lib.rs");
    let body = &lib[lib.find("pub unsafe fn start_default(").expect("start_default")..];
    let at = |s: &str| body.find(s).unwrap_or_else(|| panic!("{s}"));
    assert!(at("tcg2::collect()") < at("(bs().exit_boot_services)"));
    assert!(at("t.copy_main(pa)") < at("(bs().get_memory_map)"));
    let finish = at("t.finish(*pa)");
    assert!(at("(bs().exit_boot_services)") < finish);
    assert!(finish < at("clean(region, region_len)"));
    assert!(at("clean(bi.tpm_log_paddr, bi.tpm_log_size.div_ceil(PAGE) * PAGE)") < at("enter(region, bi_off)"));
    assert!(at("write_bytes(pa as *mut u8, 0, (pages * PAGE) as usize)") < at("t.copy_main(pa)"));
}
