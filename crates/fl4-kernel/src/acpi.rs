//! Just enough ACPI to find the cores and IOAPICs (the MADT).
use fl4_core::layout::pptr;

pub const MAX_CPUS: usize = 64;
/// IOAPICs recorded from the MADT: the kernel drives the first
/// `ioapic::MAX_IOAPICS`, but every one's registers stay out of user
/// space's device memory.
pub const MAX_IOAPICS: usize = 64;
pub const RSDP_LEN: usize = 36;

const SDT_HEADER: u64 = 36;
const MADT_HEADER: u64 = 44;

pub struct Info {
    /// The RSDP: 20 bytes, then the ACPI 2.0 fields if it has valid ones.
    pub rsdp: [u8; RSDP_LEN],
    /// Only processors enabled at boot, excluding disabled hotplug slots.
    pub cpus: [u32; MAX_CPUS],
    pub n_cpus: usize,
    pub ioapics: [u64; MAX_IOAPICS],
    pub n_ioapics: usize,
    /// The MADT lists more IOAPICs than `ioapics` holds.
    pub ioapics_lost: bool,
}

fn rd8(p: u64) -> u8 {
    unsafe { core::ptr::read_volatile(pptr(p) as *const u8) }
}

fn rd32(p: u64) -> u32 {
    unsafe { core::ptr::read_unaligned(pptr(p) as *const u32) }
}

fn rd64(p: u64) -> u64 {
    unsafe { core::ptr::read_unaligned(pptr(p) as *const u64) }
}

fn checksum(p: u64, len: u64) -> bool {
    let mut s: u8 = 0;
    for i in 0..len {
        s = s.wrapping_add(rd8(p + i));
    }
    s == 0
}

fn find_rsdp_in(start: u64, end: u64) -> Option<u64> {
    let mut p = start;
    while p + 20 <= end {
        if valid_rsdp(p) {
            return Some(p);
        }
        p += 16;
    }
    None
}

fn find_rsdp() -> Option<u64> {
    let ebda = (unsafe { core::ptr::read_volatile(pptr(0x40e) as *const u16) } as u64) << 4;
    if ebda != 0 {
        if let Some(p) = find_rsdp_in(ebda, ebda + 1024) {
            return Some(p);
        }
    }
    find_rsdp_in(0xe0000, 0x100000)
}

fn sig(p: u64) -> u32 {
    rd32(p)
}

/// An RSDP at `p`: its signature and its ACPI 1.0 checksum hold.
fn valid_rsdp(p: u64) -> bool {
    rd64(p) == u64::from_le_bytes(*b"RSD PTR ") && checksum(p, 20)
}

/// The RSDP at `p` (valid) has ACPI 2.0 fields: revision 2 or later, a
/// length that covers them, and the extended checksum over that length.
fn rsdp_v2(p: u64) -> bool {
    let len = rd32(p + 20) as u64;
    rd8(p + 15) >= 2 && (RSDP_LEN as u64..=4096).contains(&len) && checksum(p, len)
}

/// Parse the ACPI tables. `given` is the RSDP the bootloader passed
/// (Multiboot 2's ACPI tags): UEFI firmware such as OVMF keeps its tables
/// elsewhere than the BIOS areas `find_rsdp` searches (GitHub issue #8).
///
/// Every length comes from firmware: tables and MADT entries are read only
/// within their own lengths, and those that are too short for their fields
/// are skipped.
pub fn init(given: Option<u64>) -> Option<Info> {
    let rsdp = match given {
        Some(p) if valid_rsdp(p) => p,
        _ => find_rsdp()?,
    };
    let mut info = Info { rsdp: [0; RSDP_LEN], cpus: [0; MAX_CPUS], n_cpus: 0, ioapics: [0; MAX_IOAPICS], n_ioapics: 0, ioapics_lost: false };
    let v2 = rsdp_v2(rsdp);
    for i in 0..if v2 { RSDP_LEN } else { 20 } {
        info.rsdp[i] = rd8(rsdp + i as u64);
    }
    let (root, entry, root_sig) = if v2 && rd64(rsdp + 24) != 0 {
        (rd64(rsdp + 24), 8, *b"XSDT")
    } else {
        (rd32(rsdp + 16) as u64, 4, *b"RSDT")
    };
    let len = rd32(root + 4) as u64;
    if sig(root) != u32::from_le_bytes(root_sig) || len < SDT_HEADER {
        return None;
    }
    let madt_sig = u32::from_le_bytes(*b"APIC");
    for i in 0..(len - SDT_HEADER) / entry {
        let e = root + SDT_HEADER + i * entry;
        let t = if entry == 8 { rd64(e) } else { rd32(e) as u64 };
        if sig(t) == madt_sig {
            parse_madt(t, &mut info);
        }
    }
    Some(info)
}

fn parse_madt(t: u64, info: &mut Info) {
    let len = rd32(t + 4) as u64;
    let end = match t.checked_add(len) {
        Some(e) if len >= MADT_HEADER => e,
        _ => return,
    };
    let mut p = t + MADT_HEADER;
    while end - p >= 2 {
        let ty = rd8(p);
        let l = rd8(p + 1) as u64;
        if l < 2 || l > end - p {
            break;
        }
        match ty {
            0 if l >= 8 => {
                // Only Enabled (bit 0) means ready for boot. Online Capable
                // (bit 1) alone requires runtime hotplug, which we do not support.
                let flags = rd32(p + 4);
                if flags & 1 != 0 && info.n_cpus < MAX_CPUS {
                    info.cpus[info.n_cpus] = rd8(p + 3) as u32;
                    info.n_cpus += 1;
                }
            }
            1 if l >= 12 => {
                if info.n_ioapics < MAX_IOAPICS {
                    info.ioapics[info.n_ioapics] = rd32(p + 4) as u64;
                    info.n_ioapics += 1;
                } else {
                    info.ioapics_lost = true;
                }
            }
            9 if l >= 16 => {
                // Processor local x2APIC uses the same Enabled flag.
                let flags = rd32(p + 8);
                if flags & 1 != 0 && info.n_cpus < MAX_CPUS {
                    info.cpus[info.n_cpus] = rd32(p + 4);
                    info.n_cpus += 1;
                }
            }
            _ => {}
        }
        p += l;
    }
}
