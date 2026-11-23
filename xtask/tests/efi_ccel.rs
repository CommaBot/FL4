//! The UEFI confidential-computing event log (fl4-efi ccel.rs, on the
//! parsing of tcg2.rs): the `CCEL` ACPI table, a SHA-384 crypto agile log and
//! its final events, and the event that measures a boot file into RTMR[2].
#[allow(dead_code)]
#[path = "../../crates/fl4-efi/src/tcg2.rs"]
mod tcg2;
#[allow(dead_code)]
#[path = "../../crates/fl4-efi/src/ccel.rs"]
mod ccel;
#[allow(dead_code)]
#[path = "../../crates/fl4-efi/src/acpi.rs"]
mod acpi;
#[allow(dead_code)]
#[path = "../../crates/fl4-efi/src/x86_mmap.rs"]
mod x86_mmap;
#[allow(dead_code)]
#[path = "../../crates/fl4-efi/src/snp_map.rs"]
mod snp_map;

use acpi::{sdt_ok, Phys};
use ccel::{area_limit, cc_event, ccel_area, ccel_area_in_map, choose, probe_ccel, walk_log, CcelArea, MR_INDEX_RTMR2};
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

/// The kernel gets the CC log only from a TDX guest and the TPM log only
/// outside one: a TD ignores any TPM.
#[test]
fn the_loader_collects_the_cc_log_in_a_td_and_the_tpm_log_otherwise() {
    let x86 = include_str!("../../crates/fl4-efi/src/x86.rs");
    let tpm = x86.find("let tpm = if shared == 0 { tcg2::collect() } else { None };").expect("TPM log collected");
    let cc = x86.find("let (cc, cc_areas) = if shared != 0 { ccel::collect() } else { (None, ccel::CcAreas::default()) };").expect("CC log collected");
    assert!(tpm < cc);
    assert_eq!(x86.matches("tcg2::collect()").count(), 1, "only outside a TD");
    assert_eq!(x86.matches("ccel::collect()").count(), 1, "only in a TD");
    assert!(x86.contains("MB2_TAG_CC_EVENT_LOG: u32 = 0x464c_3402"));
    assert!(x86.contains("ccel::measure_file(b\"rootserver\", path, pa, len);"), "rootserver= file");
    assert!(x86.contains("ccel::measure_file(b\"module\", path, pa, len);"), "module= files");
}

/// RTMR[2] is a TDX register: the options' files are measured into it only
/// in a TD, and into the TPM only outside one.
#[test]
fn boot_files_are_measured_only_in_a_td() {
    let x86 = include_str!("../../crates/fl4-efi/src/x86.rs");
    for role in ["rootserver", "module"] {
        let call = format!(
            "if measure {{\n                ccel::measure_file(b\"{role}\", path, pa, len);\n            }} else {{\n                tcg2::measure_file(b\"{role}\", path, pa, len).unwrap_or_else(|e| fail(e));\n            }}"
        );
        assert_eq!(x86.matches(&call).count(), 1, "{role}");
    }
    assert_eq!(x86.matches("ccel::measure_file(").count(), 2, "only these two");
    let is_tdx = &x86[x86.find("pub(super) fn is_tdx() -> bool {").expect("is_tdx")..];
    assert!(is_tdx[..is_tdx.find("\n}\n").unwrap()].contains("sev().0 == 0 && tdx_shared_mask() != 0"));
    let start = &x86[x86.find("pub unsafe fn start_default(").expect("start_default")..];
    let start = &start[..start.find("\n}\n").unwrap()];
    let check = start.find("let measure = is_tdx();").expect("TD check");
    assert!(check < start.find("boot_files(li, &opts, measure)").expect("boot_files"));
    let fw = include_str!("../../crates/fl4-efi/src/firmware.rs");
    assert!(fw.contains("pub fn is_tdx(&self) -> bool {\n        x86::is_tdx()\n    }"));
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

/// RTMR[2] gets the descriptor first (role, length, path: never empty),
/// then the contents only of a file that has any: a 0-byte file is not
/// handed to HashLogExtendEvent, which refuses to hash nothing.
#[test]
fn measure_file_extends_the_descriptor_then_nonempty_contents() {
    let c = include_str!("../../crates/fl4-efi/src/ccel.rs");
    let f = &c[c.find("pub fn measure_file(role: &[u8], path: &[u8], pa: u64, len: u64)").expect("measure_file")..];
    let f = &f[..f.find("\n    }\n").unwrap()];
    let at = |s: &str| f.find(s).unwrap_or_else(|| panic!("{s}"));
    assert!(at("file_descriptor(&mut desc, role, path, len)") < at("cc_event(&mut event, desc)"));
    let desc = at("hash_log_extend_event)(cc, 0, desc.as_ptr() as u64, n as u64, event.as_ptr())");
    let guard = at("if len > 0 {");
    let contents = at("hash_log_extend_event)(cc, 0, pa, len, event.as_ptr())");
    assert!(desc < guard && guard < contents);
    assert_eq!(f.matches("hash_log_extend_event)(").count(), 2);
    assert_eq!(f.matches("measure_status(true, r as u64)").count(), 2, "both extensions fail closed");
}

/// The CC event carries the whole descriptor (role, length, path) as its
/// data, so the log says which file and role a digest is for.
#[test]
fn the_cc_event_carries_the_descriptor() {
    let mut desc = [0u8; tcg2::DESC_MAX];
    let n = tcg2::file_descriptor(&mut desc, b"module", b"\\efi\\m.elf", 7);
    let mut buf = [0u8; 18 + tcg2::DESC_MAX];
    let len = cc_event(&mut buf, &desc[..n]);
    assert_eq!(len, 18 + n);
    assert_eq!(&buf[18..len], &desc[..n]);
}

/// A caller's bytes (`Firmware::measure_cc_file`) fail closed in RTMR[2]:
/// no protocol is `EFI_UNSUPPORTED`, nothing to hash is
/// `EFI_INVALID_PARAMETER`, and a result `measure_status` refuses is
/// returned as firmware gave it; each is said on the console.
#[test]
fn measure_bytes_fails_closed() {
    let c = include_str!("../../crates/fl4-efi/src/ccel.rs");
    assert!(c.contains("const UNSUPPORTED: Status = (1 << 63) | 3;"));
    assert!(c.contains("const INVALID_PARAMETER: Status = (1 << 63) | 2;"));
    let f = &c[c.find("pub fn measure_bytes(name: &[u8], pa: u64, len: u64) -> Result<(), Status> {").expect("measure_bytes")..];
    let f = &f[..f.find("\n    }\n").unwrap()];
    let at = |s: &str| f.find(s).unwrap_or_else(|| panic!("{s}"));
    let none = at("let Some(cc) = protocol() else {");
    let unsupported = at("return Err(UNSUPPORTED);");
    let empty = at("if len == 0 {");
    let invalid = at("return Err(INVALID_PARAMETER);");
    let event = at("cc_event(&mut event, name);");
    let ext = at("((*cc).hash_log_extend_event)(cc, 0, pa, len, event.as_ptr())");
    let chk = at("measure_status(true, r as u64).map_err(|e| {");
    assert!(none < at("measure_status(false, 0).unwrap_err()") && at("measure_status(false, 0).unwrap_err()") < unsupported);
    assert!(unsupported < empty && empty < invalid && invalid < event && event < ext && ext < chk);
    assert_eq!(f.matches("hash_log_extend_event)(").count(), 1);
    assert_eq!(f.matches("say!(").count(), 3, "every refusal is said");
    assert!(f.trim_end().ends_with("r\n        })"), "firmware's status is the error");
    assert!(!f.contains("fail("), "the caller decides, but must not boot");
}

/// `measure_cc_file` measures only in a TD, and passes a refusal back.
#[test]
fn measure_cc_file_measures_only_in_a_td() {
    let fw = include_str!("../../crates/fl4-efi/src/firmware.rs");
    let f = &fw[fw.find("pub fn measure_cc_file(&self, name: &[u8], bytes: &[u8]) -> Result<(), Status> {").expect("measure_cc_file")..];
    let f = &f[..f.find("\n    }\n").unwrap()];
    assert!(f.contains("if x86::is_tdx() {\n            ccel::measure_bytes(name, bytes.as_ptr() as u64, bytes.len() as u64)?;\n        }\n        Ok(())"));
    assert_eq!(fw.matches("ccel::measure_bytes(").count(), 1);
}

/// A command line becomes the Multiboot 2 command line tag (type 1, with
/// its NUL) among the fixed tags, before `tags_end`; none when empty, as
/// for `start_default` and `Firmware::boot`.
#[test]
fn a_command_line_is_a_multiboot2_tag_before_the_memory_map() {
    let x86 = include_str!("../../crates/fl4-efi/src/x86.rs");
    assert!(x86.contains("pub(super) fn boot(image: Handle, kernel: &[u8], files: &[BootFile<'_>], cmdline: &core::ffi::CStr) -> ! {"));
    let start = &x86[x86.find("pub unsafe fn start_default(").expect("start_default")..];
    let start = &start[..start.find("\n}\n").unwrap()];
    assert!(start.contains("boot(image, embedded::KERNEL, &files[..n], c\"\")"));
    let boot = &x86[x86.find("pub(super) fn boot(").unwrap()..];
    let at = |s: &str| boot.find(s).unwrap_or_else(|| panic!("{s}"));
    let guard = at("if !cmdline.is_empty() {");
    let bytes = at("let bytes = cmdline.to_bytes_with_nul();");
    let cap = at("if bytes.len() as u64 > PAGE {\n            fail(\"kernel command line too long\");");
    let tag = at("write(info.tag(1, bytes.len() as u64), bytes);");
    assert!(at("used: 8,") < guard && guard < bytes && bytes < cap && cap < tag);
    assert!(tag < at("let tags_end = info.used;"));
    assert_eq!(boot.matches("info.tag(1,").count(), 1);
    let fw = include_str!("../../crates/fl4-efi/src/firmware.rs");
    let b = &fw[fw.find("pub unsafe fn boot_with_cmdline(").expect("boot_with_cmdline")..];
    let b = &b[..b.find("\n    }\n").unwrap()];
    assert!(b.contains("cmdline: &core::ffi::CStr,"));
    assert!(b.contains("fail(\"invalid number of boot modules\");"));
    assert!(b.trim_end().ends_with("x86::boot(self.image, kernel, &files[..modules.len()], cmdline)"));
}

fn fix_checksum(table: &mut [u8], at: usize) {
    table[at] = 0;
    table[at] = table.iter().fold(0u8, |s, b| s.wrapping_add(*b)).wrapping_neg();
}

/// Physical memory for the ACPI reader: some regions of bytes, every read
/// whole inside one of them, and every refused read recorded (the loader's
/// memory map reader, x86.rs `EfiMap`, refuses what is not firmware memory).
#[derive(Default)]
pub struct Fake {
    regions: Vec<(u64, Vec<u8>)>,
    refused: std::cell::RefCell<Vec<(u64, usize)>>,
}

impl Fake {
    fn with(mut self, at: u64, bytes: Vec<u8>) -> Fake {
        self.regions.push((at, bytes));
        self
    }
}

impl Phys for Fake {
    fn read(&self, addr: u64, n: usize) -> Option<&[u8]> {
        let hit = self.regions.iter().find_map(|(at, b)| {
            let off = addr.checked_sub(*at)? as usize;
            b.get(off..off.checked_add(n)?)
        });
        if hit.is_none() {
            self.refused.borrow_mut().push((addr, n));
        }
        hit
    }
}

/// An RSDP of `revision` naming RSDT `rsdt` and XSDT `xsdt`, with valid
/// checksums.
fn rsdp(revision: u8, rsdt: u32, xsdt: u64) -> Vec<u8> {
    let mut r = vec![0u8; 36];
    r[..8].copy_from_slice(b"RSD PTR ");
    r[15] = revision;
    r[16..20].copy_from_slice(&rsdt.to_le_bytes());
    r[20..24].copy_from_slice(&36u32.to_le_bytes());
    r[24..32].copy_from_slice(&xsdt.to_le_bytes());
    fix_checksum(&mut r[..20], 8);
    fix_checksum(&mut r, 32);
    r
}

/// A system description table with a valid checksum.
fn sdt(sig: &[u8; 4], body: &[u8]) -> Vec<u8> {
    let mut t = vec![0u8; 36];
    t[..4].copy_from_slice(sig);
    t.extend_from_slice(body);
    let len = t.len() as u32;
    t[4..8].copy_from_slice(&len.to_le_bytes());
    fix_checksum(&mut t, 9);
    t
}

fn xsdt(entries: &[u64]) -> Vec<u8> {
    sdt(b"XSDT", &entries.iter().flat_map(|e| e.to_le_bytes()).collect::<Vec<_>>())
}

/// A TDX `CCEL` table naming a log area.
fn ccel_table(lasa: u64, laml: u64) -> Vec<u8> {
    let mut body = vec![0u8; 20];
    body[0] = 2; // CC type: TDX
    body[4..12].copy_from_slice(&laml.to_le_bytes());
    body[12..20].copy_from_slice(&lasa.to_le_bytes());
    sdt(b"CCEL", &body)
}

/// A MADT of `entries` (after the 8 bytes of local APIC address and flags).
fn madt(entries: &[u8]) -> Vec<u8> {
    let mut body = vec![0u8; 8];
    body.extend_from_slice(entries);
    sdt(b"APIC", &body)
}

fn wakeup(mailbox: u64, len: u8) -> Vec<u8> {
    let mut e = vec![0u8; len as usize];
    e[0] = 16;
    e[1] = len;
    if len >= 16 {
        e[8..16].copy_from_slice(&mailbox.to_le_bytes());
    }
    e
}

/// Audit (TDX r1, fix 5): the loader follows an RSDP only if its signature
/// and checksums hold (ACPI 1.0's over 20 bytes, and the extended one for
/// revision 2).
#[test]
fn the_rsdp_must_have_its_signature_and_checksums() {
    let at = 0x10_0000;
    let r = |bytes: Vec<u8>| acpi::rsdp(&Fake::default().with(at, bytes), at);
    let got = r(rsdp(2, 0x1000, 0x2000)).unwrap();
    assert_eq!((got.root, got.entry, got.v2, got.len), (0x2000, 8, true, 36));
    assert_eq!(r(rsdp(2, 0x1000, 0)).map(|g| (g.root, g.entry)), Some((0x1000, 4)));
    let v1 = r(rsdp(0, 0x1000, 0x2000)[..20].to_vec()).unwrap();
    assert_eq!((v1.root, v1.entry, v1.v2, v1.len), (0x1000, 4, false, 20));
    let mut b = rsdp(0, 0x1000, 0);
    b[16] ^= 1;
    assert_eq!(r(b), None, "ACPI 1.0 checksum");
    let mut b = rsdp(2, 0x1000, 0x2000);
    b[0] = b'X';
    assert_eq!(r(b), None, "signature");
    let mut b = rsdp(2, 0x1000, 0x2000);
    b[24] ^= 0x10;
    assert_eq!(r(b), None, "the XSDT address is under the extended checksum");
    for len in [20u32, 35, 4097] {
        let mut b = rsdp(2, 0x1000, 0x2000);
        b[20..24].copy_from_slice(&len.to_le_bytes());
        fix_checksum(&mut b, 32);
        assert_eq!(r(b), None, "{len}");
    }
    assert_eq!(r(rsdp(2, 0x1000, 0x2000)[..30].to_vec()), None, "cut short");
}

#[test]
fn a_root_table_must_be_whole_with_its_signature_and_checksum() {
    let x = xsdt(&[0x3000]);
    assert!(sdt_ok(&x, b"XSDT"));
    assert!(!sdt_ok(&x, b"RSDT"));
    assert!(!sdt_ok(&x[..40], b"XSDT"), "length is not the slice's");
    let mut bad = x.clone();
    bad[36] ^= 1;
    assert!(!sdt_ok(&bad, b"XSDT"), "checksum");
    assert!(!sdt_ok(&x[..36], b"XSDT"));
}

/// Audit (TDX r2, R1-3): every address in the tables is read through the
/// bounded reader: the CCEL table is found through valid tables, and a
/// table outside firmware memory is never read.
#[test]
fn the_ccel_table_is_found_only_through_readable_valid_tables() {
    let (r, x, c) = (0x10_0000u64, 0x20_0000u64, 0x30_0000u64);
    let mem = || Fake::default().with(r, rsdp(2, 0, x)).with(x, xsdt(&[c])).with(c, ccel_table(0x7f00_0000, 0x1_0000));
    assert_eq!(probe_ccel(&mem(), r), CcelArea::Found(0x7f00_0000, 0x1_0000));
    // A listed table outside readable memory: refused, not read, and it may
    // be a CCEL table (audit TDX r6, R5-2).
    let m = Fake::default().with(r, rsdp(2, 0, x)).with(x, xsdt(&[c]));
    assert_eq!(probe_ccel(&m, r), CcelArea::Unknown);
    assert_eq!(m.refused.borrow().as_slice(), [(c, 8)]);
    // An XSDT entry into a hole, then the real table: unknown all the same.
    let m = Fake::default().with(r, rsdp(2, 0, x)).with(x, xsdt(&[0xfee0_0000, c])).with(c, ccel_table(0x7f00_0000, 0x1_0000));
    assert_eq!(probe_ccel(&m, r), CcelArea::Unknown);
    assert_eq!(m.refused.borrow().as_slice(), [(0xfee0_0000, 8)]);
    // A zero entry and another table are passed over.
    let m = Fake::default().with(r, rsdp(2, 0, x)).with(x, xsdt(&[0, 0x40_0000, c])).with(0x40_0000, sdt(b"APIC", &[0; 8])).with(c, ccel_table(0x7f00_0000, 0x1_0000));
    assert_eq!(probe_ccel(&m, r), CcelArea::Found(0x7f00_0000, 0x1_0000));
    // An XSDT whose entries do not fill it: nothing is followed.
    let mut ragged = xsdt(&[c]);
    ragged.extend([0, 0, 0]);
    let len = ragged.len() as u32;
    ragged[4..8].copy_from_slice(&len.to_le_bytes());
    fix_checksum(&mut ragged, 9);
    let m = Fake::default().with(r, rsdp(2, 0, x)).with(x, ragged).with(c, ccel_table(0x7f00_0000, 0x1_0000));
    assert_eq!(probe_ccel(&m, r), CcelArea::Unknown, "the root table does not hold");
    // A bad XSDT checksum, or an XSDT longer than the reader reads.
    let mut bad = xsdt(&[c]);
    bad[36] ^= 1;
    let m = Fake::default().with(r, rsdp(2, 0, x)).with(x, bad).with(c, ccel_table(0x7f00_0000, 0x1_0000));
    assert_eq!(probe_ccel(&m, r), CcelArea::Unknown, "the root table does not hold");
    let mut long = xsdt(&[c]);
    long[4..8].copy_from_slice(&((acpi::MAX_SDT + 1) as u32).to_le_bytes());
    let m = Fake::default().with(r, rsdp(2, 0, x)).with(x, long).with(c, ccel_table(0x7f00_0000, 0x1_0000));
    assert_eq!(probe_ccel(&m, r), CcelArea::Unknown, "the root table does not hold");
}

/// Audit (TDX r2, R1-5): the CCEL log area must be whole in one
/// `EfiACPIReclaimMemory` (9) or `EfiACPIMemoryNVS` (10) descriptor:
/// memory boot services or the loader may still hand out (conventional,
/// boot services, loader) is read again after ExitBootServices and could
/// have been overwritten; MMIO, holes and unaccepted memory are never read.
#[test]
fn the_ccel_log_area_must_be_acpi_memory() {
    let map = [(0x10_0000u64, 0x10_0000u64, 7u32), (0x7f00_0000, 0x10_0000, 10), (0x7f80_0000, 0x1000, 9), (0xfe00_0000, 0x10_0000, 11), (0x9000_0000, 0x10_0000, 15), (0xa000_0000, 0x10_0000, 4), (0xb000_0000, 0x10_0000, 6), (0xc000_0000, 0x10_0000, 2)];
    assert!(ccel_area_in_map(0x7f00_0000, 0x10_0000, map));
    assert!(ccel_area_in_map(0x7f00_1000, 0x1000, map));
    assert!(ccel_area_in_map(0x7f80_0000, 0x1000, map));
    for (lasa, limit) in [
        (0x10_0000, 0x1000),         // conventional memory
        (0xa000_0000, 0x1000),       // boot services data
        (0xb000_0000, 0x1000),       // runtime services data
        (0xc000_0000, 0x1000),       // loader data
        (0x7f00_0000, 0x10_0001),    // one byte past the region
        (0x7f0f_f000, 0x2000),       // across into a hole
        (0x7f40_0000, 0x1000),       // in a hole
        (0xfe00_0000, 0x1000),       // MMIO
        (0x9000_0000, 0x1000),       // unaccepted
        (0, 0x1000),                 // the first page
        (0x800, 0x100),
        (u64::MAX - 0xfff, 0x2000),  // wraps
        (0x7f00_0000, 0),            // nothing
    ] {
        assert!(!ccel_area_in_map(lasa, limit, map), "{lasa:#x}+{limit:#x}");
    }
    let split = [(0x7f00_0000u64, 0x1000u64, 10u32), (0x7f00_1000, 0x1000, 10)];
    assert!(!ccel_area_in_map(0x7f00_0000, 0x2000, split), "two descriptors do not make one");
    assert!(!ccel_area_in_map(0x7f00_0000, 0x1000, [(0x7f00_0000u64, u64::MAX, 10u32)]));
}

/// Audit (TDX r2, R1-4): the loader names the MADT's one wakeup mailbox to
/// the kernel, from valid MADTs only, and none if there are two.
#[test]
fn the_loader_takes_the_one_wakeup_mailbox_of_valid_madts() {
    let (r, x, m1, m2) = (0x10_0000u64, 0x20_0000u64, 0x30_0000u64, 0x40_0000u64);
    let root = |m: &Fake| acpi::rsdp(m, r).unwrap();
    let one = Fake::default().with(r, rsdp(2, 0, x)).with(x, xsdt(&[m1])).with(m1, madt(&wakeup(0x7f00_0000, 16)));
    assert_eq!(acpi::wakeup_mailbox(&one, &root(&one)), Some(0x7f00_0000));
    // A short entry is no mailbox, before or after a good one.
    let mut e = wakeup(0, 8);
    e.extend(wakeup(0x7f00_0000, 16));
    e.extend(wakeup(0, 8));
    let m = Fake::default().with(r, rsdp(2, 0, x)).with(x, xsdt(&[m1])).with(m1, madt(&e));
    assert_eq!(acpi::wakeup_mailbox(&m, &root(&m)), Some(0x7f00_0000));
    // Two, in one MADT or two: none.
    let mut e = wakeup(0x7f00_0000, 16);
    e.extend(wakeup(0x7f00_1000, 24));
    let m = Fake::default().with(r, rsdp(2, 0, x)).with(x, xsdt(&[m1])).with(m1, madt(&e));
    assert_eq!(acpi::wakeup_mailbox(&m, &root(&m)), None);
    let m = Fake::default().with(r, rsdp(2, 0, x)).with(x, xsdt(&[m1, m2])).with(m1, madt(&wakeup(0x7f00_0000, 16))).with(m2, madt(&wakeup(0x7f00_1000, 16)));
    assert_eq!(acpi::wakeup_mailbox(&m, &root(&m)), None);
    // A MADT whose checksum fails is not read for one.
    let mut bad = madt(&wakeup(0x7f00_0000, 16));
    bad[44 + 8] ^= 1;
    let m = Fake::default().with(r, rsdp(2, 0, x)).with(x, xsdt(&[m1])).with(m1, bad);
    assert_eq!(acpi::wakeup_mailbox(&m, &root(&m)), None);
}

/// The mailbox page must be whole in one `EfiACPIMemoryNVS` (10)
/// descriptor, and clear of the loader's memory, the AP page, the ACPI
/// tables and the CC event log.
#[test]
fn the_wakeup_mailbox_must_be_an_nvs_page_of_its_own() {
    let map = [(0x7f00_0000u64, 0x4000u64, 10u32), (0x7f80_0000, 0x1000, 9), (0x7f90_0000, 0x1000, 5), (0x7fa0_0000, 0x1000, 6), (0x10_0000, 0x10_0000, 7), (0xfe00_0000, 0x1000, 11), (0x9000_0000, 0x1000, 15)];
    let avoid = [(0x7f00_2000u64, 0x7f00_2800u64)];
    assert!(acpi::mailbox_ok(0x7f00_0000, map, &avoid));
    assert!(acpi::mailbox_ok(0x7f00_3000, map, &avoid));
    for bad in [0, 0x7f00_0800, 0x7f00_2000, 0x7f00_4000, 0x7f80_0000, 0x7f90_0000, 0x7fa0_0000, 0x10_0000, 0xfe00_0000, 0x9000_0000, u64::MAX & !0xfff] {
        assert!(!acpi::mailbox_ok(bad, map, &avoid), "{bad:#x}");
    }
    // The tables: a mailbox on the RSDP, the XSDT or a table they list.
    let (r, x, m1) = (0x7f00_0000u64, 0x7f00_1000u64, 0x7f00_3000u64);
    let m = Fake::default().with(r, rsdp(2, 0, x)).with(x, xsdt(&[m1])).with(m1, madt(&wakeup(0x7f00_2000, 16)));
    let root = acpi::rsdp(&m, r).unwrap();
    for (page, hit) in [(r, true), (x, true), (m1, true), (0x7f00_2000, false)] {
        assert_eq!(acpi::overlaps_tables(&m, r, &root, page, page + 0x1000), hit, "{page:#x}");
    }
}

/// A FADT naming a FACS and a DSDT, by the 32-bit fields or the 64-bit ones.
fn fadt(facs32: u32, dsdt32: u32, x_facs: u64, x_dsdt: u64) -> Vec<u8> {
    let mut body = vec![0u8; 276 - 36];
    body[0..4].copy_from_slice(&facs32.to_le_bytes());
    body[4..8].copy_from_slice(&dsdt32.to_le_bytes());
    body[96..104].copy_from_slice(&x_facs.to_le_bytes());
    body[104..112].copy_from_slice(&x_dsdt.to_le_bytes());
    sdt(b"FACP", &body)
}

fn facs() -> Vec<u8> {
    let mut f = vec![0u8; 64];
    f[..4].copy_from_slice(b"FACS");
    f[4..8].copy_from_slice(&64u32.to_le_bytes());
    f
}

/// Audit (TDX r3, R2-3): the mailbox page must miss what the FADT names
/// (the FACS is ACPI NVS too), by either width, and the DSDT; a table whose
/// length cannot be read is taken to overlap.
#[test]
fn the_mailbox_misses_the_facs_and_dsdt_the_fadt_names() {
    let (r, x, f, page) = (0x10_0000u64, 0x20_0000u64, 0x30_0000u64, 0x7f00_0000u64);
    let check = |m: &Fake| acpi::overlaps_tables(m, r, &acpi::rsdp(m, r).unwrap(), page, page + 0x1000);
    let with_fadt = |fa: Vec<u8>| Fake::default().with(r, rsdp(2, 0, x)).with(x, xsdt(&[f])).with(f, fa);
    // FACS and DSDT elsewhere: clear.
    let m = with_fadt(fadt(0x40_0000, 0x50_0000, 0, 0)).with(0x40_0000, facs()).with(0x50_0000, sdt(b"DSDT", &[0; 8]));
    assert!(!check(&m));
    // The FACS on the page, by FIRMWARE_CTRL or X_FIRMWARE_CTRL.
    let m = with_fadt(fadt(page as u32 + 0x800, 0x50_0000, 0, 0)).with(page + 0x800, facs()).with(0x50_0000, sdt(b"DSDT", &[0; 8]));
    assert!(check(&m));
    let m = with_fadt(fadt(0, 0x50_0000, page + 0xfc0, 0)).with(page + 0xfc0, facs()).with(0x50_0000, sdt(b"DSDT", &[0; 8]));
    assert!(check(&m));
    // A FACS just before the page, whose 64 bytes reach into it.
    let m = with_fadt(fadt(page as u32 - 0x20, 0x50_0000, 0, 0)).with(page - 0x20, facs()).with(0x50_0000, sdt(b"DSDT", &[0; 8]));
    assert!(check(&m));
    // The DSDT on the page, by DSDT or X_DSDT.
    let m = with_fadt(fadt(0x40_0000, page as u32, 0, 0)).with(0x40_0000, facs()).with(page, sdt(b"DSDT", &[0; 8]));
    assert!(check(&m));
    let m = with_fadt(fadt(0x40_0000, 0, 0, page + 0x100)).with(0x40_0000, facs()).with(page + 0x100, sdt(b"DSDT", &[0; 8]));
    assert!(check(&m));
    // A FACS below the page whose length cannot be read: fail closed.
    let m = with_fadt(fadt(page as u32 - 0x1000, 0x50_0000, 0, 0)).with(0x50_0000, sdt(b"DSDT", &[0; 8]));
    assert!(check(&m));
    // One above the page cannot reach it, read or not.
    let m = with_fadt(fadt(page as u32 + 0x2000, 0x50_0000, 0, 0)).with(0x50_0000, sdt(b"DSDT", &[0; 8]));
    assert!(!check(&m));
    // A listed table that cannot be read at all: fail closed.
    let m = Fake::default().with(r, rsdp(2, 0, x)).with(x, xsdt(&[0x9000_0000]));
    assert!(check(&m));
}

/// Audit (TDX r3, R2-3; r4, R3-1, R4-1): the `CCEL` table's whole area
/// (LAML, past what is read) is known; the page right after it is clear.
#[test]
fn the_mailbox_misses_the_whole_ccel_area() {
    use ccel::{cc_areas, mailbox_clear_of, CcelArea};
    let nvs = [(0x7f00_0000u64, 0x80_0000u64)];
    let nvs10 = [(0x7f00_0000u64, 0x80_0000u64, 10u32)];
    // A CCEL area of 4 MiB from 0x7f00_0000: only its first MiB is read.
    let (r, x, c) = (0x10_0000u64, 0x20_0000u64, 0x30_0000u64);
    let m = Fake::default().with(r, rsdp(2, 0, x)).with(x, xsdt(&[c])).with(c, ccel_table(0x7f00_0000, 4 << 20));
    let ccel = ccel::probe_ccel(&m, r);
    assert_eq!(ccel, CcelArea::Found(0x7f00_0000, 4 << 20));
    assert!(area_limit(4 << 20) == MAX_EVENT_LOG);
    // The protocol's main log at LASA (as on EDK2): LAML bounds it.
    let a = cc_areas(ccel, Some((0x7f00_0000, Some(0x2000))), 0, None);
    assert_eq!(a.known[0], (0x7f00_0000, 0x7f40_0000));
    assert_eq!(a.unknown, [0, 0]);
    let tail = 0x7f00_0000 + MAX_EVENT_LOG as u64 + 0x10_0000;
    assert!(acpi::mailbox_ok(tail, nvs10, &[]));
    assert!(!mailbox_clear_of(tail, &a, nvs), "in the area past what is read");
    assert!(mailbox_clear_of(0x7f40_0000, &a, nvs), "the page right after LASA + LAML");
}

/// Audit (TDX r5, R4-1): the protocol's logs give no allocation size: a log
/// outside the `CCEL` area and the final events table go on up from their
/// start to an unknown end, parsed or not, with events or none. In their
/// descriptor a mailbox at or above their start is refused, one below
/// them is clear.
#[test]
fn a_protocol_log_has_no_known_end_in_its_descriptor() {
    use ccel::{cc_areas, mailbox_clear_of, CcAreas, CcelArea};
    let nvs = [(0x7f00_0000u64, 0x80_0000u64)];
    for final_bytes in [Some(0x300), Some(0), None] {
        let a = cc_areas(CcelArea::Absent, Some((0x7f40_0100, Some(0x1_2000))), 0x7f60_0040, final_bytes);
        assert_eq!(a.unknown, [0x7f40_0100, 0x7f60_0040], "{final_bytes:?}");
        // What they hold now, in whole pages, is known as well.
        assert_eq!(a.known[1], (0x7f40_0000, 0x7f41_3000));
        if let Some(b) = final_bytes {
            assert_eq!(a.known[2], (0x7f60_0000, (0x7f60_0040 + 16 + b as u64 + 0xfff) & !0xfff));
        }
        for refused in [0x7f40_0000, 0x7f41_3000, 0x7f50_0000, 0x7f60_0000, 0x7f60_1000, 0x7f70_0000] {
            assert!(!mailbox_clear_of(refused, &a, nvs), "{refused:#x} {final_bytes:?}");
        }
        for clear in [0x7f00_0000, 0x7f3f_f000] {
            assert!(mailbox_clear_of(clear, &a, nvs), "{clear:#x} {final_bytes:?}");
        }
    }
    // Without the main log, the final events table alone.
    let a = cc_areas(CcelArea::Absent, None, 0x7f60_0040, None);
    assert_eq!(a, CcAreas { known: [(0, 0); 3], unknown: [0, 0x7f60_0040], unverified: false });
    assert!(mailbox_clear_of(0x7f5f_f000, &a, nvs) && !mailbox_clear_of(0x7f60_1000, &a, nvs));
    // A mailbox in no descriptor is never clear.
    assert!(!mailbox_clear_of(0x9000_0000, &CcAreas::default(), nvs));
}

/// Audit (TDX r5, R4-1, R4-2): what can be shown apart is clear: a mailbox
/// in another NVS descriptor than the logs, and the page after a main log
/// the `CCEL` area holds. What could not be looked for is not.
#[test]
fn only_what_is_shown_apart_is_clear() {
    use ccel::{cc_areas, mailbox_clear_of, CcelArea};
    // (a) Another descriptor than the logs, below or above them.
    let two = [(0x7f00_0000u64, 0x60_0000u64), (0x7f60_0000, 0x20_0000)];
    let a = cc_areas(CcelArea::Absent, Some((0x7f60_1000, Some(0x1000))), 0x7f60_0040, Some(0));
    assert!(mailbox_clear_of(0x7f50_0000, &a, two));
    let a = cc_areas(CcelArea::Absent, Some((0x7f00_1000, Some(0x1000))), 0x7f00_0040, Some(0));
    assert!(mailbox_clear_of(0x7f70_0000, &a, two));
    // (b) A main log in the CCEL area: the next page after LASA + LAML.
    let nvs = [(0x7f00_0000u64, 0x80_0000u64)];
    let a = cc_areas(CcelArea::Found(0x7f00_0000, 0x1_0000), Some((0x7f00_0000, None)), 0, None);
    assert_eq!(a.unknown, [0, 0]);
    assert!(mailbox_clear_of(0x7f01_0000, &a, nvs));
    assert!(!mailbox_clear_of(0x7f00_f000, &a, nvs));
    // A CCEL table that could not be looked for: no mailbox is clear.
    let a = cc_areas(CcelArea::Unknown, None, 0, None);
    assert!(a.unverified);
    for m in [0x7f00_0000, 0x7f50_0000, 0x7f7f_f000] {
        assert!(!mailbox_clear_of(m, &a, nvs), "{m:#x}");
    }
    // Absent only when the tables hold and list none; Unknown when they
    // cannot be read.
    let (r, x) = (0x10_0000u64, 0x20_0000u64);
    let m = Fake::default().with(r, rsdp(2, 0, x)).with(x, xsdt(&[]));
    assert_eq!(ccel::probe_ccel(&m, r), CcelArea::Absent);
    let m = Fake::default().with(r, rsdp(2, 0, x));
    assert_eq!(ccel::probe_ccel(&m, r), CcelArea::Unknown, "root table unreadable");
    let m = Fake::default();
    assert_eq!(ccel::probe_ccel(&m, r), CcelArea::Unknown, "RSDP unreadable");
    // The loader looks once, and hands that answer to both the log it may
    // use and the areas; the areas reach the mailbox check.
    let c = include_str!("../../crates/fl4-efi/src/ccel.rs");
    let col = &c[c.find("pub fn collect()").unwrap()..];
    let col = &col[..col.find("\n    }\n").unwrap()];
    assert_eq!(col.matches("probe()").count(), 1);
    assert!(col.find("let (ccel, in_acpi_memory) = probe();").unwrap() < col.find("from_table(ccel, in_acpi_memory)").unwrap());
    assert!(col.contains("(log, cc_areas(ccel, seen.main, seen.final_table, seen.final_bytes))"));
    assert_eq!(c.matches("EfiMap::get()").count(), 1, "one memory map for the CCEL table");
    let ft = &c[c.find("fn from_table(").unwrap()..];
    assert!(!ft[..ft.find("\n    }\n").unwrap()].contains("EfiMap::get()"));
    let x86 = include_str!("../../crates/fl4-efi/src/x86.rs");
    assert!(x86.contains("let (cc, cc_areas) = if shared != 0 { ccel::collect() } else { (None, ccel::CcAreas::default()) };"));
    assert!(x86.contains("&& ccel::mailbox_clear_of(m, &cc_areas, map.descriptors().map(|(b, n, _, _)| (b, n)))"));
    assert!(!c.contains("FINAL_SLACK"), "no room guessed");
    // The final events table as it is after GetEventLog, which may install
    // it, and once more before the areas are made.
    let fp = &c[c.find("fn from_protocol(").unwrap()..];
    let fp = &fp[..fp.find("\n    }\n").unwrap()];
    let get = fp.find("get_event_log)(").unwrap();
    let read = fp.find("let final_table = config_table(EFI_CC_FINAL_EVENTS_TABLE_GUID);").unwrap();
    let keep = fp.find("seen.final_table = final_table;").expect("written back");
    assert!(get < read && read < keep);
    let again = col.find("if seen.final_table == 0 {\n            seen.final_table = config_table(EFI_CC_FINAL_EVENTS_TABLE_GUID);").expect("read again");
    assert!(again < col.find("(log, cc_areas(").unwrap());
}

/// Audit (TDX r4, R3-2): a FADT is read only whole, with its checksum, and
/// with the fields of its revision; anything less may hide a FACS or DSDT.
#[test]
fn a_short_or_broken_fadt_counts_as_overlapping() {
    let (r, x, f, page) = (0x10_0000u64, 0x20_0000u64, 0x30_0000u64, 0x7f00_0000u64);
    let check = |fa: Vec<u8>| {
        let m = Fake::default().with(r, rsdp(2, 0, x)).with(x, xsdt(&[f])).with(f, fa).with(0x40_0000, facs()).with(0x50_0000, sdt(b"DSDT", &[0; 8]));
        acpi::overlaps_tables(&m, r, &acpi::rsdp(&m, r).unwrap(), page, page + 0x1000)
    };
    let with_rev = |len: usize, rev: u8| {
        let mut t = fadt(0x40_0000, 0x50_0000, 0, 0);
        t.truncate(len);
        t[4..8].copy_from_slice(&(len as u32).to_le_bytes());
        t[8] = rev;
        fix_checksum(&mut t, 9);
        t
    };
    assert!(!check(with_rev(276, 6)));
    assert!(!check(with_rev(148, 2)));
    assert!(!check(with_rev(44, 1)), "revision 1 ends at its DSDT");
    assert!(check(with_rev(36, 1)), "no FIRMWARE_CTRL or DSDT");
    assert!(check(with_rev(40, 1)), "no DSDT");
    assert!(check(with_rev(140, 2)), "revision 2 without X_DSDT");
    assert!(check(with_rev(132, 5)), "no X fields");
    let mut bad = with_rev(276, 6);
    bad[100] ^= 1;
    assert!(check(bad), "checksum");
}

/// Audit (TDX r3, R2-4): the loader hands the kernel a whole RSDP: 20 bytes
/// for ACPI 1.0, and for ACPI 2.0 36 bytes whose length says 36 and whose
/// extended checksum holds, however long the firmware's was.
#[test]
fn the_kernel_gets_a_whole_rsdp_of_its_tags_length() {
    let at = 0x10_0000;
    let mut long = rsdp(2, 0x1000, 0x2000);
    long[20..24].copy_from_slice(&64u32.to_le_bytes());
    long.resize(64, 0x77);
    fix_checksum(&mut long, 32);
    let m = Fake::default().with(at, long.clone());
    let r = acpi::rsdp(&m, at).unwrap();
    assert_eq!((r.len, r.v2, r.root), (64, true, 0x2000));
    let (bytes, n) = acpi::canonical_rsdp(&m, at, &r).unwrap();
    assert_eq!(n, 36);
    assert_eq!(&bytes[..20], &long[..20]);
    assert_eq!(&bytes[24..32], &long[24..32]);
    assert_eq!(u32::from_le_bytes(bytes[20..24].try_into().unwrap()), 36);
    let copy = Fake::default().with(at, bytes.to_vec());
    assert_eq!(acpi::rsdp(&copy, at), Some(acpi::Rsdp { len: 36, v2: true, root: 0x2000, entry: 8 }));
    // ACPI 1.0: its 20 bytes.
    let v1 = rsdp(0, 0x1000, 0)[..20].to_vec();
    let m = Fake::default().with(at, v1.clone());
    let (bytes, n) = acpi::canonical_rsdp(&m, at, &acpi::rsdp(&m, at).unwrap()).unwrap();
    assert_eq!((n, &bytes[..20]), (20, &v1[..]));
    assert!(bytes[20..].iter().all(|&b| b == 0));
}

/// Audit (TDX r6, R5-1): a protocol main log at LASA is bounded by LAML only
/// as far as it lies within the area; what it holds is known in any case.
#[test]
fn a_main_log_at_lasa_is_bounded_only_within_the_ccel_area() {
    use ccel::{cc_areas, mailbox_clear_of};
    let nvs = [(0x7f00_0000u64, 0x80_0000u64)];
    let ccel = CcelArea::Found(0x7f00_0000, 0x1_0000);
    // Within the area: LAML bounds it; the page after LASA + LAML is clear.
    let a = cc_areas(ccel, Some((0x7f00_0000, Some(0x8000))), 0, None);
    assert_eq!(a.unknown, [0, 0]);
    assert_eq!(a.known[1], (0x7f00_0000, 0x7f00_8000));
    assert!(mailbox_clear_of(0x7f01_0000, &a, nvs));
    // Past the area: its pages past LAML, and on up in its descriptor, are
    // refused; another descriptor is clear.
    let a = cc_areas(ccel, Some((0x7f00_0000, Some(0x1_2345))), 0, None);
    assert_eq!(a.unknown, [0x7f00_0000, 0]);
    assert_eq!(a.known[1], (0x7f00_0000, 0x7f01_3000));
    for refused in [0x7f01_0000, 0x7f01_2000, 0x7f01_3000, 0x7f40_0000] {
        assert!(!mailbox_clear_of(refused, &a, nvs), "{refused:#x}");
    }
    assert!(mailbox_clear_of(0x8000_0000, &a, [nvs[0], (0x8000_0000, 0x1_0000)]));
    // Inside the area but not at LASA: no known bound.
    let a = cc_areas(ccel, Some((0x7f00_4000, Some(0x1000))), 0, None);
    assert_eq!(a.unknown, [0x7f00_4000, 0]);
    assert!(!mailbox_clear_of(0x7f01_0000, &a, nvs));
    // An end past 2^64 is no bound either.
    let a = cc_areas(CcelArea::Found(u64::MAX - 0xfff, 0x2000), Some((u64::MAX - 0xfff, None)), 0, None);
    assert_eq!(a.unknown[0], u64::MAX - 0xfff);
}

/// Audit (TDX r6, R5-2), from the tables to the mailbox: a CCEL table that
/// is unread, broken, or one of two that disagree, leaves no mailbox clear;
/// a whole CCEL table for another CC type is no TDX one.
#[test]
fn a_doubtful_ccel_table_leaves_no_mailbox_clear() {
    use ccel::{cc_areas, mailbox_clear_of};
    let nvs = [(0x7f00_0000u64, 0x80_0000u64)];
    let (r, x, c, d) = (0x10_0000u64, 0x20_0000u64, 0x30_0000u64, 0x40_0000u64);
    let with = |tables: &[u64], bodies: Vec<(u64, Vec<u8>)>| {
        let mut m = Fake::default().with(r, rsdp(2, 0, x)).with(x, xsdt(tables));
        for (at, b) in bodies {
            m = m.with(at, b);
        }
        m
    };
    let clear = |m: &Fake| {
        let ccel = probe_ccel(m, r);
        (ccel, mailbox_clear_of(0x7f50_0000, &cc_areas(ccel, None, 0, None), nvs))
    };
    // Its header only: the body cannot be read.
    let good = ccel_table(0x7f00_0000, 0x1_0000);
    let m = with(&[c], vec![(c, good[..8].to_vec())]);
    assert_eq!(clear(&m), (CcelArea::Unknown, false), "body unread");
    // A bad checksum.
    let mut bad = good.clone();
    bad[50] ^= 1;
    assert_eq!(clear(&with(&[c], vec![(c, bad)])), (CcelArea::Unknown, false), "checksum");
    // A length out of range.
    let mut short = good.clone();
    short.truncate(40);
    short[4..8].copy_from_slice(&40u32.to_le_bytes());
    fix_checksum(&mut short, 9);
    assert_eq!(clear(&with(&[c], vec![(c, short)])), (CcelArea::Unknown, false), "length");
    // A whole TDX table with no area, or one whose end wraps.
    assert_eq!(clear(&with(&[c], vec![(c, ccel_table(0, 0x1000))])).0, CcelArea::Unknown);
    assert_eq!(clear(&with(&[c], vec![(c, ccel_table(u64::MAX - 0xfff, 0x2000))])).0, CcelArea::Unknown);
    // Two TDX tables that disagree; two that agree are one.
    let other = ccel_table(0x7f20_0000, 0x1_0000);
    assert_eq!(clear(&with(&[c, d], vec![(c, good.clone()), (d, other)])), (CcelArea::Unknown, false), "conflict");
    assert_eq!(clear(&with(&[c, d], vec![(c, good.clone()), (d, good.clone())])), (CcelArea::Found(0x7f00_0000, 0x1_0000), true));
    // A whole CCEL table for another CC type (1, SEV): no TDX table.
    let mut sev = good.clone();
    sev[36] = 1;
    fix_checksum(&mut sev, 9);
    assert_eq!(clear(&with(&[c], vec![(c, sev)])), (CcelArea::Absent, true));
    // None at all.
    assert_eq!(clear(&with(&[d], vec![(d, sdt(b"APIC", &[0; 8]))])), (CcelArea::Absent, true));
}
