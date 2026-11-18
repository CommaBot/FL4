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
    assert_eq!(boot.rsdp, Some(112 + 8));
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
