//! The UEFI confidential-computing event log (fl4-efi ccel.rs, on the
//! parsing of tcg2.rs): the `CCEL` ACPI table, a SHA-384 crypto agile log and
//! its final events, and the event that measures a boot file into RTMR[2].
#[allow(dead_code)]
#[path = "../../crates/fl4-efi/src/tcg2.rs"]
mod tcg2;
#[allow(dead_code)]
#[path = "../../crates/fl4-efi/src/ccel.rs"]
mod ccel;

use ccel::{area_limit, cc_event, ccel_area, choose, walk_log, MR_INDEX_RTMR2};
use tcg2::{append_final, final_snapshot, main_log, MAX_EVENT_LOG};

const SHA384: u16 = 0xc;

/// A log's Spec ID event listing SHA-384 only, as TDX firmware writes it.
fn spec_id() -> Vec<u8> {
    let mut ev = Vec::new();
    ev.extend(b"Spec ID Event03\0");
    ev.extend([0u8; 4]); // platform class
    ev.extend([0, 2, 0, 2]); // versions, uintn size
    ev.extend(1u32.to_le_bytes());
    ev.extend(SHA384.to_le_bytes());
    ev.extend(48u16.to_le_bytes());
    ev.push(0); // vendor info size
    let mut v = vec![0u8; 32];
    v[4..8].copy_from_slice(&3u32.to_le_bytes()); // EV_NO_ACTION
    v[28..32].copy_from_slice(&(ev.len() as u32).to_le_bytes());
    v.extend(ev);
    v
}

/// A `CC_EVENT` with one SHA-384 digest.
fn event(mr: u32, ty: u32, fill: u8, data: &[u8]) -> Vec<u8> {
    let mut v = Vec::new();
    v.extend(mr.to_le_bytes());
    v.extend(ty.to_le_bytes());
    v.extend(1u32.to_le_bytes());
    v.extend(SHA384.to_le_bytes());
    v.extend([fill; 48]);
    v.extend((data.len() as u32).to_le_bytes());
    v.extend(data);
    v
}

fn ccel(cc_type: u8, laml: u64, lasa: u64) -> Vec<u8> {
    let mut t = vec![0u8; 56];
    t[0..4].copy_from_slice(b"CCEL");
    t[4..8].copy_from_slice(&56u32.to_le_bytes());
    t[8] = 1;
    t[36] = cc_type;
    t[40..48].copy_from_slice(&laml.to_le_bytes());
    t[48..56].copy_from_slice(&lasa.to_le_bytes());
    t[9] = t.iter().fold(0u8, |s, b| s.wrapping_add(*b)).wrapping_neg();
    t
}

#[test]
fn the_ccel_table_gives_a_tdx_guests_log_area() {
    assert_eq!(ccel_area(&ccel(2, 0x1_0000, 0x7000_0000)[..]), Some((0x7000_0000, 0x1_0000)));
}

#[test]
fn a_ccel_table_is_refused_unless_it_is_a_valid_tdx_one() {
    // SEV's CC type.
    assert_eq!(ccel_area(&ccel(1, 0x1000, 0x7000_0000)[..]), None);
    // No area.
    assert_eq!(ccel_area(&ccel(2, 0, 0x7000_0000)[..]), None);
    assert_eq!(ccel_area(&ccel(2, 0x1000, 0)[..]), None);
    // Checksum.
    let mut t = ccel(2, 0x1000, 0x7000_0000);
    t[40] ^= 1;
    assert_eq!(ccel_area(&t[..]), None);
    // Signature.
    let mut t = ccel(2, 0x1000, 0x7000_0000);
    t[0] = b'X';
    t[9] = t[9].wrapping_sub(b'X'.wrapping_sub(b'C'));
    assert_eq!(ccel_area(&t[..]), None);
    // Shorter than its fields, or than it says.
    let mut t = ccel(2, 0x1000, 0x7000_0000);
    t[4..8].copy_from_slice(&55u32.to_le_bytes());
    assert_eq!(ccel_area(&t[..]), None);
    let t = ccel(2, 0x1000, 0x7000_0000);
    assert_eq!(ccel_area(&t[..40]), None);
}

#[test]
fn a_sha384_log_is_walked_to_its_first_zeroed_entry() {
    let mut log = spec_id();
    let header = log.len();
    log.extend(event(1, 0x8000_0001, 0xaa, b"first"));
    log.extend(event(3, 0xd, 0xbb, b"rootserver"));
    let end = log.len();
    log.resize(end + 256, 0);
    let (found, lost) = walk_log(&log[..], log.len()).unwrap();
    assert_eq!(found.len, end);
    assert!(!lost);
    assert_eq!(found.algs.digest_size(SHA384), Some(48));
    assert!(end > header);
}

#[test]
fn a_log_that_fills_its_area_is_complete() {
    let mut log = spec_id();
    log.extend(event(1, 1, 1, b"x"));
    let (found, lost) = walk_log(&log[..], log.len()).unwrap();
    assert_eq!(found.len, log.len());
    assert!(!lost);
}

#[test]
fn garbage_after_the_events_is_reported_as_a_truncated_log() {
    let mut log = spec_id();
    log.extend(event(1, 1, 1, b"x"));
    let end = log.len();
    // An event with a digest count above the log's algorithms.
    log.extend([1, 0, 0, 0, 1, 0, 0, 0, 9, 0, 0, 0, 0xc, 0, 0xff, 0xff]);
    log.resize(end + 64, 0xff);
    let (found, lost) = walk_log(&log[..], log.len()).unwrap();
    assert_eq!(found.len, end);
    assert!(lost);
}

#[test]
fn an_event_past_the_area_limit_ends_the_walk() {
    let mut log = spec_id();
    log.extend(event(1, 1, 1, b"inside"));
    let inside = log.len();
    log.extend(event(1, 1, 2, b"past the limit"));
    let (found, lost) = walk_log(&log[..], inside + 10).unwrap();
    assert_eq!(found.len, inside);
    assert!(lost);
}

#[test]
fn a_log_without_a_spec_id_event_is_no_log() {
    assert!(walk_log(&[0u8; 256][..], 256).is_none());
    let log = spec_id();
    assert!(walk_log(&log[..], log.len() - 1).is_none());
}

/// The protocol path: the log as GetEventLog gave it, then what the CC final
/// events table gained after that.
#[test]
fn final_events_are_appended_after_the_snapshot() {
    let mut log = spec_id();
    let last = log.len();
    log.extend(event(1, 1, 1, b"main"));
    let parsed = main_log(&log[..], 0x1000, 0x1000 + last as u64, false).unwrap();
    assert_eq!(parsed.len, log.len());

    let already = event(1, 2, 2, b"already in the log");
    let mut table = Vec::new();
    table.extend(1u64.to_le_bytes());
    table.extend(1u64.to_le_bytes());
    table.extend(&already);
    let snap = final_snapshot(&table[..], &parsed.algs).unwrap();
    assert_eq!(snap.nr_events, 1);

    let exit = event(2, 0x8000_0007, 3, b"Exit Boot Services Invocation");
    table[8..16].copy_from_slice(&2u64.to_le_bytes());
    table.extend(&exit);
    let mut buf = vec![0u8; log.len() + 4096];
    buf[..log.len()].copy_from_slice(&log);
    let (len, lost) = append_final(&table[..], &parsed.algs, &snap, &mut buf, log.len());
    assert!(!lost);
    assert_eq!(len, log.len() + exit.len());
    assert_eq!(&buf[log.len()..len], &exit[..]);
    // The result is one log, whose last event is the appended one.
    let (again, lost) = walk_log(&buf[..], buf.len()).unwrap();
    assert_eq!(again.len, len);
    assert!(!lost);
}

/// `EFI_CC_EVENT`: packed, 14-byte header, RTMR[2] is MR index 3.
#[test]
fn a_measured_file_is_an_ipl_event_for_rtmr2() {
    assert_eq!(MR_INDEX_RTMR2, 3);
    let mut buf = [0u8; 64];
    let n = cc_event(&mut buf, b"rootserver");
    assert_eq!(n, 4 + 14 + 10);
    assert_eq!(u32::from_le_bytes(buf[0..4].try_into().unwrap()), 28);
    assert_eq!(u32::from_le_bytes(buf[4..8].try_into().unwrap()), 14);
    assert_eq!(u16::from_le_bytes(buf[8..10].try_into().unwrap()), 1);
    assert_eq!(u32::from_le_bytes(buf[10..14].try_into().unwrap()), 3);
    assert_eq!(u32::from_le_bytes(buf[14..18].try_into().unwrap()), 0xd);
    assert_eq!(&buf[18..28], b"rootserver");
}

#[test]
fn a_long_name_is_cut_to_fit_the_event() {
    let mut buf = [0u8; 32];
    let n = cc_event(&mut buf, &[b'x'; 100]);
    assert_eq!(n, 32);
    assert_eq!(u32::from_le_bytes(buf[0..4].try_into().unwrap()), 32);
}

#[test]
fn the_area_taken_is_capped() {
    assert_eq!(area_limit(0x1000), 0x1000);
    assert_eq!(area_limit(u64::MAX), MAX_EVENT_LOG);
}

/// The kernel gets the log only from a TDX guest and the TPM log is
/// collected whatever happens to this one.
#[test]
fn the_loader_collects_both_logs_independently() {
    let x86 = include_str!("../../crates/fl4-efi/src/x86.rs");
    let tpm = x86.find("let tpm = tcg2::collect();").expect("TPM log collected");
    let cc = x86.find("let cc = if shared != 0 { ccel::collect() } else { None };").expect("CC log collected");
    assert!(tpm < cc);
    assert!(x86.contains("MB2_TAG_CC_EVENT_LOG: u32 = 0x464c_3402"));
    assert_eq!(x86.matches("ccel::measure_file(path, pa, len);").count(), 2, "rootserver= and module= files");
}

/// RTMR[2] is a TDX register: the options' files are measured only in a TD.
#[test]
fn boot_files_are_measured_only_in_a_td() {
    let x86 = include_str!("../../crates/fl4-efi/src/x86.rs");
    assert_eq!(x86.matches("if measure {\n                ccel::measure_file(path, pa, len);").count(), 2);
    let start = &x86[x86.find("pub unsafe fn start_default(").expect("start_default")..];
    let start = &start[..start.find("\n}\n").unwrap()];
    let check = start.find("let measure = sev().0 == 0 && tdx_shared_mask() != 0;").expect("TD check");
    assert!(check < start.find("boot_files(li, &opts, measure)").expect("boot_files"));
}

#[test]
fn a_protocol_log_that_can_follow_its_events_is_used() {
    let table_unused = || -> Option<&str> { panic!("the table is not needed") };
    assert_eq!(choose(Some("protocol"), |_| true, table_unused), Some("protocol"));
}

/// Without usable final events the `CCEL` table, which firmware keeps
/// appending to, is better; the protocol's main log remains the fallback.
#[test]
fn a_protocol_log_without_final_events_falls_back_to_the_table() {
    assert_eq!(choose(Some("protocol"), |_| false, || Some("table")), Some("table"));
    assert_eq!(choose(Some("protocol"), |_| false, || None), Some("protocol"));
    assert_eq!(choose(None, |_: &&str| true, || Some("table")), Some("table"));
    assert_eq!(choose(None::<&str>, |_| true, || None), None);
}

#[test]
fn an_area_ending_inside_an_entry_header_is_complete_if_zeroed() {
    let mut log = spec_id();
    log.extend(event(1, 1, 1, b"x"));
    let end = log.len();
    for tail in 1..16 {
        let mut area = log.clone();
        area.resize(end + tail, 0);
        let (found, lost) = walk_log(&area[..], area.len()).unwrap();
        assert_eq!((found.len, lost), (end, false), "{tail} zero bytes");
        *area.last_mut().unwrap() = 1;
        let (found, lost) = walk_log(&area[..], area.len()).unwrap();
        assert_eq!((found.len, lost), (end, true), "{tail} bytes, the last not zero");
    }
}

/// The five-level handoff turns off what forbids clearing CR0.PG before it
/// leaves long mode, and its GDT needs no write when a selector loads.
#[test]
fn the_five_level_handoff_clears_pcide_and_cet_first() {
    let x86 = include_str!("../../crates/fl4-efi/src/x86.rs");
    let blob = &x86[x86.find("\"fl4_handoff_la57:\"").expect("handoff")..x86.find("\"fl4_handoff_la57_end:\"").expect("end")];
    let clear = blob.find("andq $~((1 << 17) | (1 << 23)), %rax").expect("PCIDE and CET cleared");
    assert!(clear < blob.find("ljmpl *la57_to_compat").unwrap());
    for d in ["0x00cf9b000000ffff", "0x00af9b000000ffff", "0x00cf93000000ffff"] {
        assert!(blob.contains(d), "{d}");
    }
}

/// The GUIDs are UEFI's (edk2 MdePkg.dec), checked byte for byte.
#[test]
fn the_cc_guids_are_the_uefi_ones() {
    let c = include_str!("../../crates/fl4-efi/src/ccel.rs");
    assert!(c.contains("Guid(0x9675_1a3d, 0x72f4, 0x41a6, [0xa7, 0x94, 0xed, 0x5d, 0x0e, 0x67, 0xae, 0x6b])"));
    assert!(c.contains("Guid(0xdd4a_4648, 0x2de7, 0x4665, [0x96, 0x4d, 0x21, 0xd9, 0xef, 0x5f, 0xb4, 0x46])"));
}

/// HashLogExtendEvent's result: success, or `EFI_VOLUME_FULL` (RTMR[2]
/// extended, only the log is full), lets the file boot; anything else, or a
/// TD without the protocol at all, stops the boot.
#[test]
fn a_boot_file_that_cannot_be_measured_is_refused() {
    use ccel::{measure_status, VOLUME_FULL};
    assert_eq!(VOLUME_FULL, (1 << 63) | 11);
    assert!(measure_status(false, 0).is_err(), "no EFI_CC_MEASUREMENT_PROTOCOL");
    assert!(measure_status(false, VOLUME_FULL).is_err());
    assert_eq!(measure_status(true, 0), Ok(()));
    assert_eq!(measure_status(true, VOLUME_FULL), Ok(()));
    for r in [(1 << 63) | 2, (1 << 63) | 3, (1 << 63) | 7, (1 << 63) | 9, 1, u64::MAX] {
        assert!(measure_status(true, r).is_err(), "{r:#x}");
    }
}

/// In a TD a missing protocol fails the boot rather than skipping RTMR[2].
#[test]
fn measure_file_fails_closed_without_the_protocol() {
    let c = include_str!("../../crates/fl4-efi/src/ccel.rs");
    let f = &c[c.find("pub fn measure_file(").expect("measure_file")..];
    let f = &f[..f.find("\n    }\n").unwrap()];
    assert!(!f.contains("else { return }"), "a missing protocol must not return quietly");
    assert!(f.contains("let Some(cc) = protocol() else {"));
    assert!(f.contains("measure_status(false, 0)"));
    assert!(f.contains("measure_status(true, r as u64)"));
    assert!(f.contains("fail("));
}
