//! The UEFI confidential-computing event log (UEFI 2.10 §38,
//! `EFI_CC_MEASUREMENT_PROTOCOL`; ACPI 6.5 §5.2.35, the `CCEL` table): an
//! Intel TDX guest's RTMR measurements, in the crypto agile format of the
//! TPM event log and parsed by tcg2.rs. It is collected beside the TPM log
//! and independently of it.
//!
//! As in tcg2.rs the parsing is plain functions over a byte source, so
//! host tests run it (xtask/tests/efi_ccel.rs). A guest whose log is
//! missing or unusable boots without the record.

use crate::acpi::{self, Phys};
use crate::tcg2::{event2_len, spec_id, AlgTable, Log, Mem, EV_IPL, MAX_EVENT_LOG};
use crate::x86_mmap;
/// `EFI_VOLUME_FULL`: extended, but the log had no room for the event.
pub use crate::tcg2::VOLUME_FULL;

/// The `CCEL` table: its fixed part, through the log area's address.
const CCEL_LEN: usize = 56;
/// CC type in the `CCEL` table (ACPI 6.5 table 5.175).
const CC_TYPE_TDX: u8 = 2;
/// The CC measurement register RTMR[2] is (`EFI_CC_MR_INDEX`: 0 is MRTD, 1
/// is RTMR[0]).
pub const MR_INDEX_RTMR2: u32 = 3;
/// `EFI_CC_EVENT_HEADER`, packed: size, version, MR index, event type.
const CC_HEADER_LEN: usize = 14;
/// `EFI_CC_EVENT`: its size field, then the header, then the event data.
const CC_EVENT_FIXED: usize = 4 + CC_HEADER_LEN;

/// The log area (LASA, LAML) of a `CCEL` table in `m`, for a TDX guest.
pub fn ccel_area(m: &(impl Mem + ?Sized)) -> Option<(u64, u64)> {
    if m.bytes(0, 4)? != b"CCEL" {
        return None;
    }
    let len = u32::from_le_bytes(m.bytes(4, 4)?.try_into().ok()?) as usize;
    if !(CCEL_LEN..=4096).contains(&len) {
        return None;
    }
    let table = m.bytes(0, len)?;
    if table.iter().fold(0u8, |s, b| s.wrapping_add(*b)) != 0 || table[36] != CC_TYPE_TDX {
        return None;
    }
    let laml = u64::from_le_bytes(table[40..48].try_into().ok()?);
    let lasa = u64::from_le_bytes(table[48..56].try_into().ok()?);
    (lasa != 0 && laml != 0).then_some((lasa, laml))
}

/// Walk a crypto agile log in `m`, of at most `limit` bytes, to its end: the
/// first entry that is zeroed memory. Returns it and whether events may be
/// missing: the walk stopped at something that is neither that nor the end
/// of the area.
pub fn walk_log(m: &(impl Mem + ?Sized), limit: usize) -> Option<(Log, bool)> {
    let (mut off, algs): (usize, AlgTable) = spec_id(m)?;
    if off > limit {
        return None;
    }
    while let Some(l) = event2_len(m, off, &algs) {
        match off.checked_add(l) {
            Some(end) if end <= limit => off = end,
            _ => break,
        }
    }
    // An area can end less than one entry header after the last event.
    let rem = (limit - off).min(16);
    let clean = m.bytes(off, rem).is_some_and(|b| b.iter().all(|&x| x == 0));
    Some((Log { len: off, algs }, !clean))
}

/// Write an `EFI_CC_EVENT` for code loaded from `name` into `buf`, for
/// RTMR[2]; returns its length. A name that does not fit is cut: the event
/// data only labels the digest.
pub fn cc_event(buf: &mut [u8], name: &[u8]) -> usize {
    let n = name.len().min(buf.len() - CC_EVENT_FIXED);
    let size = CC_EVENT_FIXED + n;
    buf[0..4].copy_from_slice(&(size as u32).to_le_bytes());
    buf[4..8].copy_from_slice(&(CC_HEADER_LEN as u32).to_le_bytes());
    buf[8..10].copy_from_slice(&1u16.to_le_bytes());
    buf[10..14].copy_from_slice(&MR_INDEX_RTMR2.to_le_bytes());
    buf[14..18].copy_from_slice(&EV_IPL.to_le_bytes());
    buf[CC_EVENT_FIXED..size].copy_from_slice(&name[..n]);
    size
}

/// Which log to use. The protocol's when it can follow events to the end;
/// without usable final events the `CCEL` table can (firmware appends to it
/// in place), and the protocol's main log is the fallback if there is no
/// table.
pub fn choose<T>(protocol: Option<T>, complete: impl Fn(&T) -> bool, table: impl FnOnce() -> Option<T>) -> Option<T> {
    match protocol {
        Some(p) if complete(&p) => Some(p),
        Some(p) => table().or(Some(p)),
        None => table(),
    }
}

/// Whether a boot file was measured into RTMR[2] and may boot: there must
/// be an `EFI_CC_MEASUREMENT_PROTOCOL`, and its HashLogExtendEvent must have
/// extended the register (success, or `EFI_VOLUME_FULL`: only the log is
/// full).
pub fn measure_status(has_protocol: bool, status: u64) -> Result<(), &'static str> {
    if !has_protocol {
        return Err("EFI_CC_MEASUREMENT_PROTOCOL unavailable for RTMR[2] measurement");
    }
    match status {
        0 | VOLUME_FULL => Ok(()),
        _ => Err("cannot measure a boot file into RTMR[2]"),
    }
}

/// The largest log area taken.
pub fn area_limit(laml: u64) -> usize {
    laml.min(MAX_EVENT_LOG as u64) as usize
}

/// What the ACPI tables say of a `CCEL` table.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CcelArea {
    /// The RSDP and root table hold, every table they list could be read,
    /// and none is a `CCEL` table for TDX.
    Absent,
    /// Its log area: LASA, LAML (both nonzero, the end within 2^64).
    Found(u64, u64),
    /// The tables (or the memory map to read them by) could not be read,
    /// a listed table could not be, or a `CCEL` table is broken or one of
    /// two that disagree: there may be one, anywhere.
    Unknown,
}

/// The `CCEL` table's log area through the RSDP at `rsdp`: every table
/// through `p` and whole, with its checksum (acpi.rs). Only a table that is
/// shown to be no TDX `CCEL` table (another signature, or a whole `CCEL`
/// table for another CC type) is passed over; anything else that may be
/// one, unread or broken, is `Unknown`, and so are two that disagree.
pub fn probe_ccel<P: Phys + ?Sized>(p: &P, rsdp: u64) -> CcelArea {
    let Some(r) = acpi::rsdp(p, rsdp) else { return CcelArea::Unknown };
    let Some(tables) = acpi::tables(p, &r) else { return CcelArea::Unknown };
    let mut found: Option<(u64, u64)> = None;
    for t in tables {
        if t == 0 {
            continue;
        }
        let Some(head) = p.read(t, 8) else { return CcelArea::Unknown };
        if &head[..4] != b"CCEL" {
            continue;
        }
        let n = u32::from_le_bytes([head[4], head[5], head[6], head[7]]) as usize;
        if !(CCEL_LEN..=4096).contains(&n) {
            return CcelArea::Unknown;
        }
        let Some(table) = p.read(t, n) else { return CcelArea::Unknown };
        if table.iter().fold(0u8, |s, b| s.wrapping_add(*b)) != 0 {
            return CcelArea::Unknown;
        }
        if table[36] != CC_TYPE_TDX {
            continue;
        }
        // A whole TDX CCEL table: its area must be one (`ccel_area`: LASA
        // and LAML nonzero), end within 2^64, and agree with any other.
        let Some((lasa, laml)) = ccel_area(table) else { return CcelArea::Unknown };
        if lasa.checked_add(laml).is_none() || found.is_some_and(|f| f != (lasa, laml)) {
            return CcelArea::Unknown;
        }
        found = Some((lasa, laml));
    }
    found.map_or(CcelArea::Absent, |(lasa, laml)| CcelArea::Found(lasa, laml))
}

/// Whether the log area `[lasa, lasa + limit)` (`limit` from `area_limit`)
/// lies whole in one descriptor of the memory map, given as (base, bytes,
/// EFI type), of `EfiACPIReclaimMemory` (9) or `EfiACPIMemoryNVS` (10), as
/// firmware allocates it. The `CCEL` table that names it is the VMM's to
/// write, and the loader reads the area again after ExitBootServices: never
/// memory that boot services may hand out or the loader itself allocates
/// (conventional, boot services or loader memory), nor MMIO, a hole,
/// unaccepted memory or the first page.
pub fn ccel_area_in_map(lasa: u64, limit: usize, descriptors: impl IntoIterator<Item = (u64, u64, u32)>) -> bool {
    lasa >= 0x1000
        && x86_mmap::within(lasa, limit as u64, descriptors.into_iter().map(|(base, bytes, ty)| {
            (base, bytes, matches!(ty, x86_mmap::EFI_ACPI_RECLAIM | x86_mmap::EFI_ACPI_NVS))
        }))
}

/// The CC event log memory firmware keeps, whichever log the loader hands
/// on: what the wakeup mailbox must stay clear of (x86.rs).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct CcAreas {
    /// Whole pages known to hold a log: the `CCEL` area (LASA, LAML), the
    /// protocol's main log, the final events table ((0, 0) for none).
    pub known: [(u64, u64); 3],
    /// Where a log whose allocation's end is unknown starts: the
    /// protocol's main log (unless in the `CCEL` area), the final events
    /// table (0 for none). What a log holds now is not where firmware's
    /// allocation for it ends.
    pub unknown: [u64; 2],
    /// Whether a `CCEL` table could not be looked for (`CcelArea::Unknown`):
    /// no mailbox is clear of what is not known.
    pub unverified: bool,
}

const PAGE: u64 = 4096;

fn pages(start: u64, len: u64) -> (u64, u64) {
    (start & !(PAGE - 1), start.saturating_add(len).saturating_add(PAGE - 1) & !(PAGE - 1))
}

/// The `CcAreas` of a guest: `ccel` what the tables say of a `CCEL`
/// table, `main` the protocol's main log (its address and, if it parsed,
/// its length), `final_table` the final events table's address (0 for
/// none) and `final_bytes` its events' length if they parsed. Only the
/// `CCEL` area's allocation is known (LAML); the protocol's logs give no
/// allocation size, so each is known to hold what it holds now (whole
/// pages, nothing guessed) and goes on up from its start to an unknown end.
pub fn cc_areas(ccel: CcelArea, main: Option<(u64, Option<usize>)>, final_table: u64, final_bytes: Option<usize>) -> CcAreas {
    let mut a = CcAreas { unverified: ccel == CcelArea::Unknown, ..CcAreas::default() };
    if let CcelArea::Found(lasa, laml) = ccel {
        a.known[0] = pages(lasa, laml);
    }
    if let Some((at, len)) = main.filter(|&(at, _)| at != 0) {
        if let Some(len) = len {
            a.known[1] = pages(at, len as u64);
        }
        // The same allocation as the CCEL area (as on EDK2, where the main
        // log is at LASA), and what it holds within it: LAML bounds it.
        let in_ccel_area = match ccel {
            CcelArea::Found(lasa, laml) => {
                at == lasa && lasa.checked_add(laml).is_some_and(|end| len.is_none_or(|l| at.checked_add(l as u64).is_some_and(|e| e <= end)))
            }
            _ => false,
        };
        if !in_ccel_area {
            a.unknown[0] = at;
        }
    }
    if final_table != 0 {
        a.unknown[1] = final_table;
        if let Some(bytes) = final_bytes {
            a.known[2] = pages(final_table, (crate::tcg2::FINAL_HEADER + bytes) as u64);
        }
    }
    a
}

/// Whether the mailbox page at `mailbox` is clear of every CC log area:
/// none of `known`, and each log of unknown end provably apart. A log
/// grows up from its start within one allocation, so it is apart if it
/// starts in another descriptor of the map (`descriptors`: base, bytes)
/// than the mailbox or on a page past it; else the mailbox is refused, as
/// it is if a `CCEL` table could not be looked for.
pub fn mailbox_clear_of(mailbox: u64, areas: &CcAreas, descriptors: impl IntoIterator<Item = (u64, u64)>) -> bool {
    if areas.unverified {
        return false;
    }
    let end = mailbox.saturating_add(PAGE);
    if areas.known.iter().any(|&(s, e)| s < end && mailbox < e) {
        return false;
    }
    let Some((base, bytes)) = descriptors.into_iter().find(|&(b, n)| b <= mailbox && end <= b.saturating_add(n)) else {
        return false;
    };
    let in_mailbox_descriptor = |p: u64| base <= p && p < base.saturating_add(bytes);
    areas.unknown.iter().all(|&u| u == 0 || !in_mailbox_descriptor(u) || end <= (u & !(PAGE - 1)))
}

#[cfg(not(test))]
pub use efi::*;

/// What runs on firmware.
#[cfg(not(test))]
mod efi {
    use super::*;
    use crate::tcg2::{file_descriptor, final_snapshot, main_log, Raw, TpmLog, DESC_MAX, EFI_TCG2_EVENT_LOG_FORMAT_TCG_2, TCG_1_2, TRUNCATED};
    use crate::x86::EfiMap;
    use crate::{bs, config_table, fail, print, Con, Guid, Status, ACPI_10, ACPI_20, SUCCESS};

    pub const EFI_CC_MEASUREMENT_PROTOCOL_GUID: Guid = Guid(0x9675_1a3d, 0x72f4, 0x41a6, [0xa7, 0x94, 0xed, 0x5d, 0x0e, 0x67, 0xae, 0x6b]);
    pub const EFI_CC_FINAL_EVENTS_TABLE_GUID: Guid = Guid(0xdd4a_4648, 0x2de7, 0x4665, [0x96, 0x4d, 0x21, 0xd9, 0xef, 0x5f, 0xb4, 0x46]);
    /// `EFI_CC_MEASUREMENT_PROTOCOL` up to HashLogExtendEvent.
    #[repr(C)]
    struct CcProtocol {
        get_capability: usize,
        get_event_log: extern "efiapi" fn(*mut CcProtocol, u32, *mut u64, *mut u64, *mut u8) -> Status,
        hash_log_extend_event: extern "efiapi" fn(*mut CcProtocol, u64, u64, u64, *const u8) -> Status,
    }

    fn protocol() -> Option<*mut CcProtocol> {
        let mut p = core::ptr::null_mut();
        let r = (bs().locate_protocol)(&EFI_CC_MEASUREMENT_PROTOCOL_GUID, core::ptr::null(), &mut p);
        (r == SUCCESS && !p.is_null()).then_some(p as *mut CcProtocol)
    }

    /// Measure a file the load options named (`role`: rootserver or
    /// module) into RTMR[2], so that a quote covers it: its descriptor
    /// (tcg2.rs `file_descriptor`: role, length, path), then its contents
    /// in place unless it is empty (firmware refuses to hash nothing).
    /// Called only in a TD: a file that cannot be measured is not booted,
    /// and neither is one when firmware offers no
    /// `EFI_CC_MEASUREMENT_PROTOCOL` (`measure_status`).
    pub fn measure_file(role: &[u8], path: &[u8], pa: u64, len: u64) {
        let Some(cc) = protocol() else {
            fail(measure_status(false, 0).unwrap_err());
        };
        let mut desc = [0u8; DESC_MAX];
        let n = file_descriptor(&mut desc, role, path, len);
        let desc = &desc[..n];
        let mut event = [0u8; CC_EVENT_FIXED + DESC_MAX];
        cc_event(&mut event, desc);
        let r = unsafe { ((*cc).hash_log_extend_event)(cc, 0, desc.as_ptr() as u64, n as u64, event.as_ptr()) };
        if let Err(e) = measure_status(true, r as u64) {
            fail(e);
        }
        if len > 0 {
            let r = unsafe { ((*cc).hash_log_extend_event)(cc, 0, pa, len, event.as_ptr()) };
            if let Err(e) = measure_status(true, r as u64) {
                fail(e);
            }
        }
    }

    /// `EFI_UNSUPPORTED`: no `EFI_CC_MEASUREMENT_PROTOCOL`.
    const UNSUPPORTED: Status = (1 << 63) | 3;
    /// `EFI_INVALID_PARAMETER`: firmware refuses to hash nothing.
    const INVALID_PARAMETER: Status = (1 << 63) | 2;

    /// Measure caller-built bytes at `(pa, len)` into RTMR[2] as one event
    /// named `name`, so that a quote covers them. Called only in a TD: bytes
    /// that cannot be measured must not be booted, and neither must they
    /// when firmware offers no `EFI_CC_MEASUREMENT_PROTOCOL`
    /// (`measure_status`). The error, said on the console, is the caller's
    /// to act on: it must not boot them.
    pub fn measure_bytes(name: &[u8], pa: u64, len: u64) -> Result<(), Status> {
        let Some(cc) = protocol() else {
            say!("fl4-efi: {}", measure_status(false, 0).unwrap_err());
            return Err(UNSUPPORTED);
        };
        if len == 0 {
            say!("fl4-efi: refusing to measure empty bytes into RTMR[2]");
            return Err(INVALID_PARAMETER);
        }
        let mut event = [0u8; CC_EVENT_FIXED + 256];
        cc_event(&mut event, name);
        let r = unsafe { ((*cc).hash_log_extend_event)(cc, 0, pa, len, event.as_ptr()) };
        measure_status(true, r as u64).map_err(|e| {
            say!("fl4-efi: {}", e);
            r
        })
    }

    /// The log firmware keeps, found before ExitBootServices.
    pub enum CcLog {
        /// From the protocol, with the final events table.
        Protocol(TpmLog),
        /// From the `CCEL` table: firmware keeps appending in place.
        Table { lasa: u64, limit: usize, log: Log, flags: u64 },
    }

    impl CcLog {
        /// Bytes to set aside for the copy.
        pub fn capacity(&self) -> u64 {
            match self {
                CcLog::Protocol(t) => t.capacity(),
                CcLog::Table { limit, .. } => *limit as u64,
            }
        }

        /// The log so far (before ExitBootServices), to `dst`.
        pub fn copy_main(&self, dst: u64) {
            match self {
                CcLog::Protocol(t) => t.copy_main(dst),
                CcLog::Table { lasa, log, .. } => unsafe {
                    core::ptr::copy_nonoverlapping(*lasa as *const u8, dst as *mut u8, log.len)
                },
            }
        }

        /// The size and flags of the copy at `dst` so far.
        pub fn record(&self) -> (u64, u64) {
            match self {
                CcLog::Protocol(t) => t.record(),
                CcLog::Table { log, flags, .. } => (log.len as u64, *flags),
            }
        }

        /// After ExitBootServices: bring the copy at `dst` up to date.
        /// Returns its size and flags. Uses no boot services and does not
        /// print.
        pub fn finish(&self, dst: u64) -> (u64, u64) {
            match self {
                CcLog::Protocol(t) => t.finish(dst),
                CcLog::Table { lasa, limit, log, flags } => {
                    // The area is firmware-reserved and still mapped: read
                    // it again, with what ExitBootServices logged.
                    let m = Raw { base: *lasa, limit: *limit };
                    match walk_log(&m, *limit) {
                        Some((now, lost)) if now.len >= log.len => {
                            unsafe { core::ptr::copy_nonoverlapping(*lasa as *const u8, dst as *mut u8, now.len) };
                            (now.len as u64, flags | if lost { TRUNCATED } else { 0 })
                        }
                        _ => (log.len as u64, flags | TRUNCATED),
                    }
                }
            }
        }
    }

    /// What firmware said of its logs, used or not (`cc_areas`).
    #[derive(Default)]
    struct Seen {
        main: Option<(u64, Option<usize>)>,
        final_table: u64,
        final_bytes: Option<usize>,
    }

    fn from_protocol(cc: *mut CcProtocol, seen: &mut Seen) -> Option<CcLog> {
        let (mut location, mut last, mut truncated) = (0u64, 0u64, 0u8);
        let r = unsafe { ((*cc).get_event_log)(cc, EFI_TCG2_EVENT_LOG_FORMAT_TCG_2, &mut location, &mut last, &mut truncated) };
        if r != SUCCESS || location == 0 {
            return None;
        }
        seen.main = Some((location, None));
        if last == 0 {
            return None;
        }
        // Right after GetEventLog: the final events table holds what the
        // log already does.
        let final_table = config_table(EFI_CC_FINAL_EVENTS_TABLE_GUID);
        // Firmware may install it only now, with the first GetEventLog.
        if final_table != 0 {
            seen.final_table = final_table;
        }
        let m = Raw { base: location, limit: MAX_EVENT_LOG };
        let log = main_log(&m, location, last, false)?;
        seen.main = Some((location, Some(log.len)));
        let mut flags = if truncated != 0 { TRUNCATED } else { 0 };
        let mut snap = None;
        if final_table != 0 {
            snap = final_snapshot(&Raw { base: final_table, limit: MAX_EVENT_LOG }, &log.algs);
            seen.final_bytes = snap.as_ref().map(|s| s.bytes);
            if snap.is_none() {
                flags |= TRUNCATED;
            }
        } else {
            flags |= TRUNCATED;
        }
        debug_assert!(flags & TCG_1_2 == 0);
        say!("fl4-efi: CC event log {:#x} bytes at {:#x}{}", log.len, location, if snap.is_some() { ", final events table" } else { "" });
        Some(CcLog::Protocol(TpmLog::new(location, log, flags, final_table, snap)))
    }

    /// The log through the `CCEL` table, read through the memory map taken
    /// here once (GetMemoryMap): the tables only from firmware memory, the
    /// log area only from ACPI memory (`ccel_area_in_map`), both checked in
    /// `probe` with one memory map.
    fn from_table(ccel: CcelArea, in_acpi_memory: bool) -> Option<CcLog> {
        let CcelArea::Found(lasa, laml) = ccel else { return None };
        let limit = area_limit(laml);
        if !in_acpi_memory {
            say!("fl4-efi: CCEL log area at {:#x} is not ACPI memory: not used", lasa);
            return None;
        }
        let (log, lost) = walk_log(&Raw { base: lasa, limit }, limit)?;
        say!("fl4-efi: CC event log {:#x} bytes at {:#x} (CCEL table)", log.len, lasa);
        Some(CcLog::Table { lasa, limit, log, flags: if lost { TRUNCATED } else { 0 } })
    }

    /// Look for the `CCEL` table once, through one memory map
    /// (GetMemoryMap): what the tables say (`probe_ccel`; `Unknown` without
    /// a map or with an RSDP the system table names that does not hold,
    /// `Absent` without any), and whether its log area is ACPI memory.
    fn probe() -> (CcelArea, bool) {
        let Some(map) = EfiMap::get() else { return (CcelArea::Unknown, false) };
        let ccel = match map.rsdp() {
            Some((rsdp, _)) => probe_ccel(&map, rsdp),
            None if config_table(ACPI_20) == 0 && config_table(ACPI_10) == 0 => CcelArea::Absent,
            None => CcelArea::Unknown,
        };
        let in_acpi_memory = match ccel {
            CcelArea::Found(lasa, laml) => {
                ccel_area_in_map(lasa, area_limit(laml), map.descriptors().map(|(base, bytes, ty, _)| (base, bytes, ty)))
            }
            _ => false,
        };
        (ccel, in_acpi_memory)
    }

    /// The CC event log, from the protocol or the ACPI table (`choose`),
    /// and every CC log area firmware keeps, whichever log that is: the
    /// `CCEL` area, the protocol's main log and the final events table.
    /// Never fails the boot: anything else is a line on the console.
    pub fn collect() -> (Option<CcLog>, CcAreas) {
        // Once: the log it may hand on and the areas use the same answer.
        let (ccel, in_acpi_memory) = probe();
        let mut seen = Seen { final_table: config_table(EFI_CC_FINAL_EVENTS_TABLE_GUID), ..Seen::default() };
        let complete = |l: &CcLog| matches!(l, CcLog::Protocol(t) if t.has_final_events());
        let log = choose(protocol().and_then(|cc| from_protocol(cc, &mut seen)), complete, || from_table(ccel, in_acpi_memory));
        if log.is_none() {
            say!("fl4-efi: no usable CC event log");
        }
        // A GetEventLog that failed or found no events may have installed
        // the final events table all the same.
        if seen.final_table == 0 {
            seen.final_table = config_table(EFI_CC_FINAL_EVENTS_TABLE_GUID);
        }
        (log, cc_areas(ccel, seen.main, seen.final_table, seen.final_bytes))
    }
}
