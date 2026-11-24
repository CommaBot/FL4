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
    /// The firmware's AP wakeup mailbox (MADT Multiprocessor Wakeup
    /// structure), how an Intel TDX guest starts its cores. Unvalidated:
    /// the VMM writes these tables.
    pub mp_wakeup_mailbox: Option<u64>,
    /// The first such structure as the MADT has it, for the boot log:
    /// (version, length, mailbox), the mailbox 0 if it is too short for one.
    pub mp_wakeup_raw: Option<(u16, u64, u64)>,
    /// More than one structure with a mailbox, in one MADT or several:
    /// which the firmware polls is unknown, so `mp_wakeup_mailbox` is None.
    pub mp_wakeup_duplicate: bool,
}

fn rd8(p: u64) -> u8 {
    unsafe { core::ptr::read_volatile(pptr(p) as *const u8) }
}

fn rd16(p: u64) -> u16 {
    unsafe { core::ptr::read_unaligned(pptr(p) as *const u16) }
}

fn rd32(p: u64) -> u32 {
    unsafe { core::ptr::read_unaligned(pptr(p) as *const u32) }
}

fn rd64(p: u64) -> u64 {
    unsafe { core::ptr::read_unaligned(pptr(p) as *const u64) }
}

/// What the kernel may read: `[p, p + len)` is in the kernel window's
/// mapping of `[0, top)` (the window maps only that much, paging.rs, and
/// past it lies the kernel image's mapping and then nothing), and the
/// caller's `readable` allows it (in a confidential guest only firmware
/// memory: never unaccepted memory, MMIO or a hole of the memory map).
struct Reader<'a> {
    top: u64,
    readable: &'a dyn Fn(u64, u64) -> bool,
}

impl Reader<'_> {
    fn ok(&self, p: u64, len: u64) -> bool {
        matches!(p.checked_add(len), Some(end) if end <= self.top) && (self.readable)(p, len)
    }
}

fn checksum(p: u64, len: u64) -> bool {
    let mut s: u8 = 0;
    for i in 0..len {
        s = s.wrapping_add(rd8(p + i));
    }
    s == 0
}

fn find_rsdp_in(r: &Reader, start: u64, end: u64) -> Option<u64> {
    let mut p = start;
    while p + 20 <= end {
        if r.ok(p, 20) && valid_rsdp(p) {
            return Some(p);
        }
        p += 16;
    }
    None
}

fn find_rsdp(r: &Reader) -> Option<u64> {
    if r.ok(0x40e, 2) {
        let ebda = (unsafe { core::ptr::read_volatile(pptr(0x40e) as *const u16) } as u64) << 4;
        if ebda != 0 {
            if let Some(p) = find_rsdp_in(r, ebda, ebda + 1024) {
                return Some(p);
            }
        }
    }
    find_rsdp_in(r, 0xe0000, 0x100000)
}

fn sig(p: u64) -> u32 {
    rd32(p)
}

/// An RSDP at `p` (readable for 20 bytes): its signature and its ACPI 1.0
/// checksum hold.
fn valid_rsdp(p: u64) -> bool {
    rd64(p) == u64::from_le_bytes(*b"RSD PTR ") && checksum(p, 20)
}

/// The RSDP at `p` (valid) has ACPI 2.0 fields: revision 2 or later, a
/// length that covers them and stays within `max` bytes (its Multiboot 2
/// tag), and the extended checksum over that length.
fn rsdp_v2(r: &Reader, p: u64, max: u64) -> bool {
    if max < RSDP_LEN as u64 || !r.ok(p, RSDP_LEN as u64) {
        return false;
    }
    let len = rd32(p + 20) as u64;
    rd8(p + 15) >= 2 && (RSDP_LEN as u64..=4096.min(max)).contains(&len) && r.ok(p, len) && checksum(p, len)
}

/// The longest XSDT, RSDT or MADT read: a length from the tables is no
/// reason to walk gigabytes.
pub const MAX_SDT_LEN: u64 = 1 << 20;

/// Parse the ACPI tables. `given` is the RSDP the bootloader passed
/// (Multiboot 2's ACPI tags) and the bytes its tag holds, which the RSDP is
/// read no further than: UEFI firmware such as OVMF keeps its tables
/// elsewhere than the BIOS areas `find_rsdp` searches (GitHub issue #8).
///
/// Every length comes from firmware: tables and MADT entries are read only
/// within their own lengths, and those that are too short for their fields
/// are skipped. So are tables not wholly below `top`, the end of the
/// physical memory the kernel window maps, or not wholly where `readable`
/// allows, an XSDT, RSDT or MADT longer than `MAX_SDT_LEN` or whose bytes
/// do not sum to zero (ACPI checksum), and a root table whose entries do
/// not fill it exactly.
pub fn init(given: Option<(u64, u64)>, top: u64, readable: &dyn Fn(u64, u64) -> bool) -> Option<Info> {
    let r = Reader { top, readable };
    let (rsdp, max) = match given {
        Some((p, max)) if max >= 20 && r.ok(p, 20) && valid_rsdp(p) => (p, max),
        // A BIOS area's RSDP is bounded by its own length alone.
        _ => (find_rsdp(&r)?, u64::MAX),
    };
    let mut info = Info { rsdp: [0; RSDP_LEN], cpus: [0; MAX_CPUS], n_cpus: 0, ioapics: [0; MAX_IOAPICS], n_ioapics: 0, ioapics_lost: false, mp_wakeup_mailbox: None, mp_wakeup_raw: None, mp_wakeup_duplicate: false };
    let v2 = rsdp_v2(&r, rsdp, max);
    for i in 0..if v2 { RSDP_LEN } else { 20 } {
        info.rsdp[i] = rd8(rsdp + i as u64);
    }
    // The 36 bytes handed on (BootInfo) are a whole RSDP of their own: its
    // length 36, and the extended checksum made again over them.
    if v2 {
        info.rsdp[20..24].copy_from_slice(&(RSDP_LEN as u32).to_le_bytes());
        info.rsdp[32] = 0;
        info.rsdp[32] = info.rsdp.iter().fold(0u8, |s, b| s.wrapping_add(*b)).wrapping_neg();
    }
    let (root, entry, root_sig) = if v2 && rd64(rsdp + 24) != 0 {
        (rd64(rsdp + 24), 8, *b"XSDT")
    } else {
        (rd32(rsdp + 16) as u64, 4, *b"RSDT")
    };
    if !r.ok(root, SDT_HEADER) {
        return None;
    }
    let len = rd32(root + 4) as u64;
    if sig(root) != u32::from_le_bytes(root_sig) || !(SDT_HEADER..=MAX_SDT_LEN).contains(&len)
        || (len - SDT_HEADER) % entry != 0 || !r.ok(root, len) || !checksum(root, len) {
        return None;
    }
    let madt_sig = u32::from_le_bytes(*b"APIC");
    for i in 0..(len - SDT_HEADER) / entry {
        let e = root + SDT_HEADER + i * entry;
        let t = if entry == 8 { rd64(e) } else { rd32(e) as u64 };
        if r.ok(t, SDT_HEADER) && sig(t) == madt_sig {
            parse_madt(&r, t, &mut info);
        }
    }
    Some(info)
}

/// Record a boot core once: firmware may list a core as both a Local APIC
/// and an x2APIC, or in two MADTs (and an SNP guest's hypervisor writes
/// the tables). Each listing would otherwise take a CPU slot of its own.
fn add_cpu(info: &mut Info, id: u32) {
    if info.cpus[..info.n_cpus].contains(&id) || info.n_cpus == MAX_CPUS {
        return;
    }
    info.cpus[info.n_cpus] = id;
    info.n_cpus += 1;
}

/// Whether `ids[i]` is that APIC ID's first listing (false past the end):
/// `smp::start_aps` starts each core once, as another INIT/SIPI (or SNP
/// AP creation) would take the running core off the slot it started on.
pub fn first_listing(ids: &[u32], i: usize) -> bool {
    i < ids.len() && !ids[..i].contains(&ids[i])
}

fn parse_madt(r: &Reader, t: u64, info: &mut Info) {
    let len = rd32(t + 4) as u64;
    if !(MADT_HEADER..=MAX_SDT_LEN).contains(&len) || !r.ok(t, len) || !checksum(t, len) {
        return;
    }
    let end = t + len;
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
                if flags & 1 != 0 {
                    add_cpu(info, rd8(p + 3) as u32);
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
                if flags & 1 != 0 {
                    add_cpu(info, rd32(p + 4));
                }
            }
            // Type, length, mailbox version and reserved, then its address.
            // As in Linux, any version with room for the address will do:
            // later versions only add fields after it (a reset vector),
            // which the kernel does not use. ACPI allows one; with two the
            // kernel would wake APs through a mailbox firmware may not
            // poll, so it uses neither.
            16 if l >= 4 => {
                let mailbox = if l >= 16 { rd64(p + 8) } else { 0 };
                if info.mp_wakeup_raw.is_none() {
                    info.mp_wakeup_raw = Some((rd16(p + 2), l, mailbox));
                }
                if l >= 16 {
                    if info.mp_wakeup_mailbox.is_some() || info.mp_wakeup_duplicate {
                        info.mp_wakeup_duplicate = true;
                        info.mp_wakeup_mailbox = None;
                    } else {
                        info.mp_wakeup_mailbox = Some(mailbox);
                    }
                }
            }
            _ => {}
        }
        p += l;
    }
}
