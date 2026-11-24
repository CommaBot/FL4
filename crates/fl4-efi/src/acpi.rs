//! The ACPI tables as the x86_64 loader reads them before ExitBootServices:
//! the RSDP for the kernel's tag, the `CCEL` table (ccel.rs) and a TD's
//! multiprocessor wakeup mailbox (x86.rs). A VMM can write these tables, so
//! every address in them is read only through a `Phys`, which refuses what
//! is not firmware memory (x86.rs `EfiMap`: never MMIO, a hole or
//! unaccepted memory), and every table only whole, with its checksum.
//!
//! Plain functions over a `Phys`, so host tests run them
//! (xtask/tests/efi_ccel.rs, xtask/tests/efi_memory_types.rs).

/// Physical memory the loader may read.
pub trait Phys {
    /// The `n` bytes at `addr`, or None if any of them is not to be read.
    fn read(&self, addr: u64, n: usize) -> Option<&[u8]>;
}

/// The longest system description table read.
pub const MAX_SDT: usize = 1 << 16;
const SDT_HEADER: usize = 36;
const MADT_HEADER: usize = 44;
/// A FADT up to its DSDT field (revision 1), and up to X_DSDT (2 on).
const FADT_V1_LEN: usize = 44;
const FADT_V2_LEN: usize = 148;

/// The ACPI checksum: the bytes sum to zero.
fn sums_to_zero(b: &[u8]) -> bool {
    b.iter().fold(0u8, |s, x| s.wrapping_add(*x)) == 0
}

fn rd32(b: &[u8], o: usize) -> Option<u32> {
    Some(u32::from_le_bytes(b.get(o..o + 4)?.try_into().ok()?))
}

fn rd64(b: &[u8], o: usize) -> Option<u64> {
    Some(u64::from_le_bytes(b.get(o..o + 8)?.try_into().ok()?))
}

/// An RSDP that holds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Rsdp {
    /// Its length: 20 (ACPI 1.0) or its own (36 to 4096).
    pub len: usize,
    /// ACPI 2.0 or later: the bytes past the first 20 are fields.
    pub v2: bool,
    /// The root table: the XSDT (`entry` 8) if there is one, else the RSDT.
    pub root: u64,
    pub entry: usize,
}

/// The RSDP at `addr`: its signature and the ACPI 1.0 checksum over its
/// first 20 bytes hold, and for revision 2 or later also its length (36 to
/// 4096 bytes) and the extended checksum over that length.
pub fn rsdp<P: Phys + ?Sized>(p: &P, addr: u64) -> Option<Rsdp> {
    let v1 = p.read(addr, 20)?;
    if &v1[..8] != b"RSD PTR " || !sums_to_zero(v1) {
        return None;
    }
    let rsdt = rd32(v1, 16)? as u64;
    if v1[15] < 2 {
        return Some(Rsdp { len: 20, v2: false, root: rsdt, entry: 4 });
    }
    let len = rd32(p.read(addr.checked_add(20)?, 4)?, 0)? as usize;
    if !(36..=4096).contains(&len) {
        return None;
    }
    let all = p.read(addr, len)?;
    if !sums_to_zero(all) {
        return None;
    }
    Some(match rd64(all, 24)? {
        0 => Rsdp { len, v2: true, root: rsdt, entry: 4 },
        x => Rsdp { len, v2: true, root: x, entry: 8 },
    })
}

/// Whether `table` is a whole system description table with signature
/// `sig`: its header's length is the slice's, and its checksum holds.
pub fn sdt_ok(table: &[u8], sig: &[u8; 4]) -> bool {
    table.len() >= SDT_HEADER
        && &table[..4] == sig
        && rd32(table, 4).is_some_and(|l| l as usize == table.len())
        && sums_to_zero(table)
}

/// The whole table at `addr` with signature `sig`, at most `MAX_SDT` bytes,
/// if its checksum holds.
pub fn sdt<'a, P: Phys + ?Sized>(p: &'a P, addr: u64, sig: &[u8; 4]) -> Option<&'a [u8]> {
    let head = p.read(addr, SDT_HEADER)?;
    if &head[..4] != sig {
        return None;
    }
    let len = rd32(head, 4)? as usize;
    if !(SDT_HEADER..=MAX_SDT).contains(&len) {
        return None;
    }
    let t = p.read(addr, len)?;
    sdt_ok(t, sig).then_some(t)
}

/// The tables the root table lists, in order: None if the root table does
/// not hold, or its entries do not fill it exactly.
pub fn tables<'a, P: Phys + ?Sized>(p: &'a P, r: &Rsdp) -> Option<impl Iterator<Item = u64> + 'a> {
    let entry = r.entry;
    let t = sdt(p, r.root, if entry == 8 { b"XSDT" } else { b"RSDT" })?;
    if (t.len() - SDT_HEADER) % entry != 0 {
        return None;
    }
    Some(t[SDT_HEADER..].chunks_exact(entry).map(move |e| if entry == 8 { rd64(e, 0).unwrap_or(0) } else { rd32(e, 0).unwrap_or(0) as u64 }))
}

/// The multiprocessor wakeup mailbox (MADT type 16 with room for its
/// address, any version) of the MADTs that hold. None if there is none, or
/// more than one: ACPI allows one, and which one firmware polls would be
/// unknown.
pub fn wakeup_mailbox<P: Phys + ?Sized>(p: &P, r: &Rsdp) -> Option<u64> {
    let mut found = None;
    for t in tables(p, r)?.filter(|&t| t != 0) {
        let Some(madt) = sdt(p, t, b"APIC") else { continue };
        if madt.len() < MADT_HEADER {
            continue;
        }
        let mut at = MADT_HEADER;
        while madt.len() - at >= 2 {
            let (ty, l) = (madt[at], madt[at + 1] as usize);
            if l < 2 || l > madt.len() - at {
                break;
            }
            if ty == 16 && l >= 16 {
                if found.is_some() {
                    return None;
                }
                found = Some(rd64(madt, at + 8)?);
            }
            at += l;
        }
    }
    found
}

/// Whether `[start, end)` overlaps the RSDP at `addr`, its root table, a
/// table that lists, or the FACS and DSDT a FADT names (32- and 64-bit
/// fields). A table that starts below `end` but whose length cannot be
/// read might overlap, and a listed table that cannot be read at all might
/// be a FADT naming the page: either counts as overlapping (fail closed).
pub fn overlaps_tables<P: Phys + ?Sized>(p: &P, addr: u64, r: &Rsdp, start: u64, end: u64) -> bool {
    let hits = |a: u64, len: u64| a < end && start < a.saturating_add(len);
    // The structure at `a` whose header has its length at offset 4, at
    // least `min` bytes.
    let clash = |a: u64, min: u64| {
        if a == 0 || a >= end {
            return false;
        }
        match p.read(a, 8).and_then(|h| rd32(h, 4)) {
            Some(len) => hits(a, (len as u64).max(min)),
            None => true,
        }
    };
    if hits(addr, r.len as u64) || clash(r.root, SDT_HEADER as u64) {
        return true;
    }
    let Some(tables) = tables(p, r) else { return true };
    for t in tables.filter(|&t| t != 0) {
        if clash(t, SDT_HEADER as u64) {
            return true;
        }
        // Wherever it is, a table that cannot be read may be a FADT naming
        // a FACS or DSDT on the page.
        let Some(head) = p.read(t, SDT_HEADER) else { return true };
        if &head[..4] != b"FACP" {
            continue;
        }
        // A FADT that holds (`sdt`), with the fields its revision has:
        // FIRMWARE_CTRL (FACS) at 36 and DSDT at 40, and from revision 2
        // X_FIRMWARE_CTRL at 132 and X_DSDT at 140. Anything less may
        // hide a FACS or DSDT on the page.
        let Some(fadt) = sdt(p, t, b"FACP") else { return true };
        let min_len = if fadt[8] >= 2 { FADT_V2_LEN } else { FADT_V1_LEN };
        if fadt.len() < min_len {
            return true;
        }
        let facs = [rd32(fadt, 36).map(u64::from), rd64(fadt, 132)];
        let dsdt = [rd32(fadt, 40).map(u64::from), rd64(fadt, 140)];
        if facs.into_iter().flatten().any(|a| clash(a, 64)) || dsdt.into_iter().flatten().any(|a| clash(a, SDT_HEADER as u64)) {
            return true;
        }
    }
    false
}

/// The RSDP the loader hands the kernel (Multiboot 2 tag 14 or 15): its
/// first 20 bytes, or for ACPI 2.0 its first 36 with the length set to 36
/// and the extended checksum made again, so that the copy is a whole RSDP
/// and nothing of it lies past the tag. The bytes and their length.
pub fn canonical_rsdp<P: Phys + ?Sized>(p: &P, addr: u64, r: &Rsdp) -> Option<([u8; 36], usize)> {
    let n = if r.v2 { 36 } else { 20 };
    let mut buf = [0u8; 36];
    buf[..n].copy_from_slice(p.read(addr, n)?);
    if r.v2 {
        buf[20..24].copy_from_slice(&36u32.to_le_bytes());
        buf[32] = 0;
        buf[32] = buf.iter().fold(0u8, |s, x| s.wrapping_add(*x)).wrapping_neg();
    }
    Some((buf, n))
}

/// Whether the TD's wakeup mailbox page at `mailbox` is ACPI NVS memory as
/// ACPI (6.4+, Multiprocessor Wakeup Structure) and TDVF have it: page
/// aligned and whole in one `EfiACPIMemoryNVS` (10) descriptor of
/// `descriptors` (base, bytes, EFI type), and clear of every range of
/// `avoid` (the loader's own memory, the AP page, the ACPI tables, the CC
/// event log).
pub fn mailbox_ok(mailbox: u64, descriptors: impl IntoIterator<Item = (u64, u64, u32)>, avoid: &[(u64, u64)]) -> bool {
    const PAGE: u64 = 4096;
    const EFI_ACPI_NVS: u32 = 10;
    let Some(end) = mailbox.checked_add(PAGE) else { return false };
    mailbox != 0
        && mailbox % PAGE == 0
        && descriptors.into_iter().any(|(base, bytes, ty)| ty == EFI_ACPI_NVS && base <= mailbox && base.checked_add(bytes).is_some_and(|e| end <= e))
        && avoid.iter().all(|&(s, e)| e <= mailbox || end <= s)
}
