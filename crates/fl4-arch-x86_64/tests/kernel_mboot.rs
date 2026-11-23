// Exercise the kernel's parser against emulated physical memory.
extern crate self as fl4_core;

use std::cell::Cell;

thread_local! {
    static MEMORY: Cell<u64> = const { Cell::new(0) };
}

mod layout {
    pub fn pptr(address: u64) -> u64 {
        super::MEMORY.with(|base| base.get() + address)
    }
}

#[macro_export]
macro_rules! kprintln {
    ($($args:tt)*) => { eprintln!($($args)*) };
}

#[path = "../../fl4-kernel/src/mb2.rs"]
mod mb2;
#[allow(dead_code)]
#[path = "../../fl4-kernel/src/mboot.rs"]
mod mboot;
#[allow(dead_code)]
#[path = "../../fl4-kernel/src/acpi.rs"]
mod acpi;
#[allow(dead_code)]
#[path = "../../fl4-efi/src/acpi.rs"]
mod efi_acpi;

fn words(memory: &mut [u8], offset: usize, values: &[u32]) {
    for (chunk, value) in memory[offset..][..values.len() * 4]
        .chunks_exact_mut(4)
        .zip(values)
    {
        chunk.copy_from_slice(&value.to_le_bytes());
    }
}

fn parse(magic: u32, memory: &[u8]) -> mboot::BootInfo {
    MEMORY.with(|base| base.set(memory.as_ptr() as u64));
    let boot = mboot::parse(magic, 0).unwrap();
    MEMORY.with(|base| base.set(0));
    boot
}

#[test]
fn multiboot1_owns_the_module_name_and_truncates_it_to_the_abi() {
    let mut memory = [0; 256];
    words(&mut memory, 0, &[(1 << 3) | (1 << 6)]);
    words(&mut memory, 20, &[1, 64]);
    words(&mut memory, 44, &[24, 80]);
    words(&mut memory, 64, &[0x100000, 0x101000, 128, 0]);
    words(&mut memory, 80, &[20, 0x100000, 0, 0x100000, 0, 1]);
    memory[128..192].fill(b'x');

    let boot = parse(mboot::MB1_MAGIC, &memory);
    memory[128..192].fill(b'y');
    assert_eq!(boot.n_modules, 1);
    let module = &boot.modules[0];
    assert_eq!((module.start, module.end), (0x100000, 0x101000));
    assert_eq!(&module.name[..63], &[b'x'; 63]);
    assert_eq!(module.name[63], 0);
}

#[test]
fn multiboot2_owns_names_and_keeps_reads_inside_each_module_tag() {
    let mut memory = [0; 128];
    words(&mut memory, 0, &[112, 0]);
    words(&mut memory, 8, &[3, 29, 0x100000, 0x101000]);
    memory[24..37].copy_from_slice(b"guest-kernel\0");
    words(&mut memory, 40, &[3, 19, 0x101000, 0x102000]);
    // No terminator inside this tag. Padding is outside its declared size.
    memory[56..64].copy_from_slice(b"sdkpad!!");
    words(
        &mut memory,
        64,
        &[6, 40, 24, 0, 0x100000, 0, 0x100000, 0, 1, 0],
    );
    words(&mut memory, 104, &[0, 8]);

    let boot = parse(mboot::MB2_MAGIC, &memory);
    memory[8..64].fill(0);
    assert_eq!(boot.n_modules, 2);
    let guest = &boot.modules[0];
    assert_eq!((guest.start, guest.end), (0x100000, 0x101000));
    assert_eq!(&guest.name[..13], b"guest-kernel\0");
    assert!(guest.name[13..].iter().all(|&byte| byte == 0));
    assert_eq!(&boot.modules[1].name[..4], b"sdk\0");
}

/// Parse `memory` (information at its offset `info`), then look for
/// `opt` on the command line while the memory is still in place.
fn parse_with_option(magic: u32, memory: &[u8], info: u64, opt: &[u8]) -> Option<(mboot::BootInfo, bool)> {
    MEMORY.with(|base| base.set(memory.as_ptr() as u64));
    let boot = mboot::parse(magic, info);
    let found = boot.as_ref().map(|b| mboot::has_option(b, opt));
    MEMORY.with(|base| base.set(0));
    Some((boot?, found?))
}

/// A Multiboot 2 mmap tag at `offset` with one available entry.
fn mb2_mmap(memory: &mut [u8], offset: usize) {
    words(memory, offset, &[6, 40, 24, 0, 0x100000, 0, 0x100000, 0, 1, 0]);
}

/// Audit F6(a): the command line is read within its tag. A line with no
/// NUL ends with the tag; an empty tag (size 8) is an empty line, not the
/// bytes of the next tag.
#[test]
fn multiboot2_command_lines_stay_inside_their_tag() {
    let mut memory = [0u8; 128];
    words(&mut memory, 0, &[80, 0]);
    // "fb_console" with no NUL; the padding after it is not the line.
    words(&mut memory, 8, &[1, 18]);
    memory[16..26].copy_from_slice(b"fb_console");
    memory[26..32].copy_from_slice(b"=nope!");
    mb2_mmap(&mut memory, 32);
    words(&mut memory, 72, &[0, 8]);
    let (_, found) = parse_with_option(mboot::MB2_MAGIC, &memory, 0, b"fb_console").unwrap();
    assert!(found);

    let mut memory = [0u8; 128];
    words(&mut memory, 0, &[88, 0]);
    words(&mut memory, 8, &[1, 8]);
    // The next tag, an unknown one, whose payload reads like an option.
    words(&mut memory, 16, &[0x99, 24]);
    memory[24..35].copy_from_slice(b"fb_console\0");
    mb2_mmap(&mut memory, 40);
    words(&mut memory, 80, &[0, 8]);
    let (boot, found) = parse_with_option(mboot::MB2_MAGIC, &memory, 0, b"fb_console").unwrap();
    assert_eq!(boot.cmdline_len, 0);
    assert!(!found);
}

/// Audit F6(a): framebuffer, mmap and RSDP tags too short for what they
/// describe are ignored rather than read past their end.
#[test]
fn multiboot2_short_tags_are_ignored() {
    let mut memory = [0u8; 160];
    words(&mut memory, 0, &[152, 0]);
    // Framebuffer: 22 bytes of the 30 its fields take.
    words(&mut memory, 8, &[8, 22, 0xe000_0000, 0, 4096, 1024]);
    // Memory map: header only, then a real one.
    words(&mut memory, 32, &[6, 8]);
    mb2_mmap(&mut memory, 40);
    // RSDP 2.0 (tag 15) of 28 bytes, then RSDP 1.0 (tag 14) of 28.
    words(&mut memory, 80, &[15, 28]);
    words(&mut memory, 112, &[14, 28]);
    words(&mut memory, 144, &[0, 8]);
    let boot = parse(mboot::MB2_MAGIC, &memory);
    assert!(boot.fb.is_none());
    assert_eq!(boot.n_mmap, 1);
    assert_eq!(boot.rsdp, Some((112 + 8, 20)));
}

/// Audit F6(a): information that the boot mapping ([0, 4 GiB)) does not
/// hold is refused before any read of it.
#[test]
fn information_outside_the_boot_mapping_is_refused() {
    // Reads would land 4 GiB past this array: refused without one.
    let memory = [0u8; 8];
    for magic in [mboot::MB1_MAGIC, mboot::MB2_MAGIC] {
        assert!(parse_with_option(magic, &memory, (1 << 32) - 4, b"x").is_none());
    }
    // Multiboot 2 whose total size runs past 4 GiB.
    let mut memory = [0u8; 16];
    words(&mut memory, 0, &[u32::MAX, 0, 0, 8]);
    MEMORY.with(|base| base.set(memory.as_ptr() as u64));
    assert!(mboot::parse(mboot::MB2_MAGIC, 0).is_none());
    MEMORY.with(|base| base.set(0));
}

/// Audit F6(a): a Multiboot 1 module count past what is kept reads only
/// one entry more (to report it), and an mmap entry whose size cannot hold
/// an entry ends the map.
#[test]
fn multiboot1_bounds_modules_and_mmap_entries() {
    let mut memory = [0u8; 512];
    words(&mut memory, 0, &[(1 << 3) | (1 << 6)]);
    // 2^32 - 1 modules at 128; 10 entries (160 bytes) are there.
    words(&mut memory, 20, &[u32::MAX, 128]);
    for i in 0..10 {
        words(&mut memory, 128 + 16 * i, &[0x100000, 0x101000, 0, 0]);
    }
    // mmap at 300: one good entry, then one of size 0.
    words(&mut memory, 44, &[48, 300]);
    words(&mut memory, 300, &[20, 0x100000, 0, 0x100000, 0, 1]);
    words(&mut memory, 324, &[0, 0x200000, 0, 0x100000, 0, 1]);
    let boot = parse(mboot::MB1_MAGIC, &memory);
    assert_eq!(boot.n_modules, mboot::MAX_MODULES);
    assert_eq!(boot.n_mmap, 1);
}

/// A Multiboot 2 information with one mmap tag of `entries` (base, len,
/// type), 24 bytes each.
fn mb2_with_mmap(entries: &[(u64, u64, u32)]) -> Vec<u8> {
    let tag = 16 + 24 * entries.len();
    let total = 8 + tag + 8;
    let mut memory = vec![0u8; total];
    words(&mut memory, 0, &[total as u32, 0]);
    words(&mut memory, 8, &[6, tag as u32, 24, 0]);
    for (i, &(base, len, ty)) in entries.iter().enumerate() {
        let e = 24 + 24 * i;
        words(&mut memory, e, &[base as u32, (base >> 32) as u32, len as u32, (len >> 32) as u32, ty, 0]);
    }
    words(&mut memory, 8 + tag, &[0, 8]);
    memory
}

/// GRUB passes UEFI's own map on, often 150-300 entries, many of them
/// neighbours of one type. They merge, and none past the 128th is lost:
/// RAM up there would otherwise become user space's device memory.
#[test]
fn multiboot2_maps_merge_neighbours_and_keep_every_entry() {
    // 300 contiguous 1 MiB entries alternating in pairs of types 1 and 1,
    // then reserved: 100 runs of (RAM, RAM, reserved).
    let mut entries = Vec::new();
    for i in 0..300u64 {
        entries.push((0x10_0000 + i * 0x10_0000, 0x10_0000, if i % 3 == 2 { 2 } else { 1 }));
    }
    // And RAM at the top, where the loader puts things.
    entries.push((1 << 40, 1 << 30, 1));
    let memory = mb2_with_mmap(&entries);
    let boot = parse(mboot::MB2_MAGIC, &memory);
    assert!(!boot.mmap_lost);
    assert_eq!(boot.n_mmap, 201);
    assert_eq!((boot.mmap[0].base, boot.mmap[0].len, boot.mmap[0].ty), (0x10_0000, 0x20_0000, 1));
    let last = boot.mmap[boot.n_mmap - 1];
    assert_eq!((last.base, last.len, last.ty), (1 << 40, 1 << 30, 1));
}

/// A map with more distinct entries than the kernel keeps is reported, so
/// the kernel refuses to boot rather than lose what is past the limit.
#[test]
fn multiboot2_maps_past_the_limit_are_reported() {
    let mut entries = Vec::new();
    for i in 0..mboot::MAX_MMAP as u64 + 1 {
        entries.push((i * 0x20_0000, 0x10_0000, 1));
    }
    let boot = parse(mboot::MB2_MAGIC, &mb2_with_mmap(&entries));
    assert_eq!(boot.n_mmap, mboot::MAX_MMAP);
    assert!(boot.mmap_lost);
    let boot = parse(mboot::MB2_MAGIC, &mb2_with_mmap(&entries[..mboot::MAX_MMAP]));
    assert!(!boot.mmap_lost);
}

/// Multiboot 2 information with an mmap tag and an FL4 TPM event log tag
/// (fl4-efi x86.rs) of `size` bytes giving (paddr, size, flags).
fn mb2_with_tpm(size: u32, paddr: u64, log_size: u64, flags: u64) -> Vec<u8> {
    let mut memory = vec![0u8; 8 + 40 + 40 + 8];
    let total = memory.len() as u32;
    words(&mut memory, 0, &[total, 0]);
    mb2_mmap(&mut memory, 8);
    words(&mut memory, 48, &[mboot::MB2_TAG_TPM_EVENT_LOG, size]);
    memory[56..64].copy_from_slice(&paddr.to_le_bytes());
    memory[64..72].copy_from_slice(&log_size.to_le_bytes());
    memory[72..80].copy_from_slice(&flags.to_le_bytes());
    words(&mut memory, 88, &[0, 8]);
    memory
}

#[test]
fn multiboot2_tpm_event_log_tag_is_read() {
    assert_eq!(mboot::MB2_TAG_TPM_EVENT_LOG, 0x464c_3401);
    let boot = parse(mboot::MB2_MAGIC, &mb2_with_tpm(32, 0x7f00_0000, 0x1234, 1));
    let t = boot.tpm_log.expect("TPM event log");
    assert_eq!((t.paddr, t.size, t.flags), (0x7f00_0000, 0x1234, 1));
    // The largest log, ending exactly at 4 GiB.
    let top = (1u64 << 32) - mboot::MAX_TPM_LOG;
    let boot = parse(mboot::MB2_MAGIC, &mb2_with_tpm(32, top, mboot::MAX_TPM_LOG, 2));
    assert_eq!(boot.tpm_log.map(|t| (t.paddr, t.size, t.flags)), Some((top, mboot::MAX_TPM_LOG, 2)));
    // Without the tag there is no log.
    let boot = parse(mboot::MB2_MAGIC, &mb2_without_tpm());
    assert!(boot.tpm_log.is_none());
}

fn mb2_without_tpm() -> Vec<u8> {
    mb2_with_mmap(&[(0x10_0000, 0x10_0000, 1)])
}

/// A tag too short for its fields, an empty or oversized log, one in low
/// memory or one past the boot mapping is ignored, and the boot goes on.
#[test]
fn multiboot2_tpm_event_log_out_of_range_is_ignored() {
    for (size, paddr, log_size) in [
        (24, 0x7f00_0000, 0x1000),
        (32, 0x7f00_0000, 0),
        (32, 0x7f00_0000, mboot::MAX_TPM_LOG + 1),
        (32, 0x8_0000, 0x1000),
        (32, 0xffff_f000, 0x2000),
        (32, 1 << 32, 0x1000),
        (32, u64::MAX - 0xfff, 0x1000),
        (32, 0x7f00_0000, u64::MAX),
    ] {
        let boot = parse(mboot::MB2_MAGIC, &mb2_with_tpm(size, paddr, log_size, 0));
        assert!(boot.tpm_log.is_none(), "tag {size} at {paddr:#x} of {log_size:#x}");
        assert_eq!(boot.n_mmap, 1);
    }
}

/// Multiboot 2 information with an mmap tag and one more tag of `kind`
/// whose 8-byte fields follow its header.
fn mb2_with(kind: u32, fields: &[u64]) -> Vec<u8> {
    let mut memory = mb2_without_tpm();
    let total = u32::from_le_bytes(memory[0..4].try_into().unwrap()) as usize;
    // Replace the end tag.
    let at = total - 8;
    let size = 8 + 8 * fields.len();
    memory.resize(at + size + 8, 0);
    words(&mut memory, at, &[kind, size as u32]);
    for (i, f) in fields.iter().enumerate() {
        memory[at + 8 + 8 * i..][..8].copy_from_slice(&f.to_le_bytes());
    }
    words(&mut memory, at + size, &[0, 8]);
    words(&mut memory, 0, &[(at + size + 8) as u32]);
    memory
}

#[test]
fn multiboot2_cc_event_log_tag_is_read_apart_from_the_tpm_log() {
    assert_eq!(mboot::MB2_TAG_CC_EVENT_LOG, 0x464c_3402);
    let boot = parse(mboot::MB2_MAGIC, &mb2_with(mboot::MB2_TAG_CC_EVENT_LOG, &[0x7f00_0000, 0x1234, 1]));
    assert_eq!(boot.cc_log.map(|t| (t.paddr, t.size, t.flags)), Some((0x7f00_0000, 0x1234, 1)));
    assert!(boot.tpm_log.is_none());
    for (paddr, size) in [(0x7f00_0000, 0), (0x7f00_0000, mboot::MAX_TPM_LOG + 1), (0x8000, 0x10), ((1 << 32) - 8, 0x10)] {
        let boot = parse(mboot::MB2_MAGIC, &mb2_with(mboot::MB2_TAG_CC_EVENT_LOG, &[paddr, size, 0]));
        assert!(boot.cc_log.is_none(), "{paddr:#x} {size:#x}");
    }
}

#[test]
fn multiboot2_tdx_ap_page_tag_must_be_a_page_in_the_boot_mapping() {
    assert_eq!(mboot::MB2_TAG_TDX_AP_PAGE, 0x464c_3403);
    let boot = parse(mboot::MB2_MAGIC, &mb2_with(mboot::MB2_TAG_TDX_AP_PAGE, &[0x7e00_0000]));
    assert_eq!(boot.tdx_ap_page, Some(0x7e00_0000));
    for page in [0, 0x7e00_0800, 1 << 32] {
        let boot = parse(mboot::MB2_MAGIC, &mb2_with(mboot::MB2_TAG_TDX_AP_PAGE, &[page]));
        assert_eq!(boot.tdx_ap_page, None, "{page:#x}");
    }
}

/// Audit (TDX r2, R1-4): the wakeup mailbox fl4-efi checked comes as its
/// own tag, a whole page; the kernel still checks it against the MADT and
/// the memory map.
#[test]
fn multiboot2_tdx_mailbox_tag_must_be_a_page() {
    assert_eq!(mboot::MB2_TAG_TDX_MAILBOX, 0x464c_3404);
    let boot = parse(mboot::MB2_MAGIC, &mb2_with(mboot::MB2_TAG_TDX_MAILBOX, &[0x7f00_0000]));
    assert_eq!(boot.tdx_mailbox, Some(0x7f00_0000));
    assert_eq!(boot.tdx_ap_page, None);
    for page in [0, 0x7f00_0800] {
        let boot = parse(mboot::MB2_MAGIC, &mb2_with(mboot::MB2_TAG_TDX_MAILBOX, &[page]));
        assert_eq!(boot.tdx_mailbox, None, "{page:#x}");
    }
    let x86 = include_str!("../../fl4-efi/src/x86.rs");
    assert!(x86.contains("const MB2_TAG_TDX_MAILBOX: u32 = 0x464c_3404;"));
}

fn sum_to_zero(b: &mut [u8], at: usize) {
    b[at] = 0;
    b[at] = b.iter().fold(0u8, |s, x| s.wrapping_add(*x)).wrapping_neg();
}

/// Emulated memory as fl4-efi's reader sees it: `bytes` at physical 0.
struct Mem<'a>(&'a [u8]);

impl efi_acpi::Phys for Mem<'_> {
    fn read(&self, addr: u64, n: usize) -> Option<&[u8]> {
        self.0.get(addr as usize..(addr as usize).checked_add(n)?)
    }
}

/// Audit (TDX r3, R2-4), from the loader to the kernel: firmware's 64-byte
/// ACPI 2.0 RSDP becomes a whole 36-byte one in tag 15 (`canonical_rsdp`),
/// and the kernel reads it, and the tables through it, without a byte of
/// the next tag; a tag 15 whose RSDP claims more than the tag holds is no
/// ACPI 2.0 RSDP to the kernel.
#[test]
fn an_rsdp_tag_carries_a_whole_rsdp_and_is_read_within_it() {
    const XSDT: usize = 0x400;
    const MADT: usize = 0x440;
    const FW_RSDP: usize = 0x500;
    let mut memory = vec![0u8; 0x600];
    // The XSDT and an MADT with one enabled local APIC.
    let madt_len = 44 + 8;
    memory[MADT..MADT + 4].copy_from_slice(b"APIC");
    memory[MADT + 4..MADT + 8].copy_from_slice(&(madt_len as u32).to_le_bytes());
    memory[MADT + 44..MADT + 52].copy_from_slice(&[0, 8, 7, 7, 1, 0, 0, 0]);
    sum_to_zero(&mut memory[MADT..MADT + madt_len], 9);
    memory[XSDT..XSDT + 4].copy_from_slice(b"XSDT");
    memory[XSDT + 4..XSDT + 8].copy_from_slice(&44u32.to_le_bytes());
    memory[XSDT + 36..XSDT + 44].copy_from_slice(&(MADT as u64).to_le_bytes());
    sum_to_zero(&mut memory[XSDT..XSDT + 44], 9);
    // Firmware's RSDP: revision 2, 64 bytes.
    let fw = &mut memory[FW_RSDP..FW_RSDP + 64];
    fw[..8].copy_from_slice(b"RSD PTR ");
    fw[15] = 2;
    fw[20..24].copy_from_slice(&64u32.to_le_bytes());
    fw[24..32].copy_from_slice(&(XSDT as u64).to_le_bytes());
    fw[36..].fill(0x33);
    sum_to_zero(&mut fw[..20], 8);
    sum_to_zero(fw, 32);
    let m = Mem(&memory);
    let r = efi_acpi::rsdp(&m, FW_RSDP as u64).expect("firmware's RSDP");
    let (rsdp, n) = efi_acpi::canonical_rsdp(&m, FW_RSDP as u64, &r).unwrap();
    assert_eq!(n, 36);
    // Multiboot 2: tag 15 (8 + 36, padded to 48), then a tag of nonzero
    // bytes right after it, then the end tag.
    let mb2 = |rsdp: &[u8], next: u8| {
        let mut mem = memory.clone();
        let info = 0x100;
        let tag = info + 8;
        words(&mut mem, tag, &[6, 16 + 24, 24, 0]);
        mem[tag + 16..tag + 40].copy_from_slice(&[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x10, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]);
        let t15 = tag + 40;
        words(&mut mem, t15, &[15, 8 + rsdp.len() as u32]);
        mem[t15 + 8..t15 + 8 + rsdp.len()].copy_from_slice(rsdp);
        let next_at = t15 + (8 + rsdp.len() + 7) / 8 * 8;
        words(&mut mem, next_at, &[0x464c_3499, 40]);
        mem[next_at + 8..next_at + 40].fill(next);
        words(&mut mem, next_at + 40, &[0, 8]);
        words(&mut mem, info, &[(next_at + 48 - info) as u32, 0]);
        (mem, info as u64, t15 as u64 + 8)
    };
    let kernel = |mem: &[u8], info: u64| {
        MEMORY.with(|base| base.set(mem.as_ptr() as u64));
        let boot = mboot::parse(mboot::MB2_MAGIC, info).unwrap();
        let acpi = acpi::init(boot.rsdp, mem.len() as u64, &|_, _| true);
        MEMORY.with(|base| base.set(0));
        (boot.rsdp, acpi)
    };
    for next in [0, 0x5a, 0xff] {
        let (mem, info, at) = mb2(&rsdp[..n], next);
        let (given, acpi) = kernel(&mem, info);
        assert_eq!(given, Some((at, 36)));
        let acpi = acpi.expect("valid RSDP");
        assert_eq!(&acpi.cpus[..acpi.n_cpus], &[7], "next tag {next:#x}");
        assert_eq!(&acpi.rsdp[..], &rsdp[..]);
    }
    // Firmware's own 36 bytes, which say 64: what the extended checksum
    // would cover runs into the next tag, which here even makes it sum.
    let raw = memory[FW_RSDP..FW_RSDP + 36].to_vec();
    let (mut mem, info, at) = mb2(&raw, 0);
    let next = at as usize + 48; // past the next tag's header, in its fields
    let partial = mem[at as usize..at as usize + 64].iter().fold(0u8, |s, x| s.wrapping_add(*x));
    mem[next] = mem[next].wrapping_sub(partial);
    assert_eq!(mem[at as usize..at as usize + 64].iter().fold(0u8, |s, x| s.wrapping_add(*x)), 0);
    let (given, acpi) = kernel(&mem, info);
    assert_eq!(given, Some((at, 36)));
    // ACPI 1.0 by the first 20 bytes: the RSDT (0) is the tag area, no RSDT.
    assert!(acpi.is_none_or(|a| a.rsdp[20..].iter().all(|&b| b == 0)));
}
