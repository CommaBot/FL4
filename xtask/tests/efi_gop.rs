//! The x86 UEFI loader's framebuffer tag (fl4-efi gop.rs, used by x86.rs
//! `boot`): the firmware's current Graphics Output mode becomes the
//! Multiboot 2 framebuffer tag GRUB would pass, which the kernel turns
//! into the X86_FRAMEBUFFER bootinfo record.
#[path = "../../crates/fl4-efi/src/gop.rs"]
mod gop;

/// The kernel's reading of a framebuffer tag (mboot.rs), checked against
/// its source below: the whole tag, with its type and size words.
const KERNEL_READ: &str = "8 if size >= 30 => b.fb = Some(Framebuffer { addr: rd64(t + 8), pitch: rd32(t + 16), width: rd32(t + 20), height: rd32(t + 24), bpp: rd8(t + 28), ty: rd8(t + 29) })";

/// A framebuffer size that holds every mode below.
const ANY: u64 = u64::MAX;

#[derive(Debug, PartialEq)]
struct Framebuffer {
    addr: u64,
    pitch: u32,
    width: u32,
    height: u32,
    bpp: u8,
    ty: u8,
}

/// The tag as the loader writes it (x86.rs `Info::tag`), read back as the
/// kernel does.
fn kernel_reads(payload: &[u8; gop::LEN]) -> Option<Framebuffer> {
    let mut tag = Vec::new();
    tag.extend_from_slice(&8u32.to_le_bytes());
    tag.extend_from_slice(&(gop::LEN as u32 + 8).to_le_bytes());
    tag.extend_from_slice(payload);
    let rd8 = |o: usize| tag[o];
    let rd32 = |o: usize| u32::from_le_bytes(tag[o..o + 4].try_into().unwrap());
    let rd64 = |o: usize| u64::from_le_bytes(tag[o..o + 8].try_into().unwrap());
    let (t, size) = (0, rd32(4) as usize);
    (rd32(0) == 8 && size >= 30).then(|| Framebuffer {
        addr: rd64(t + 8),
        pitch: rd32(t + 16),
        width: rd32(t + 20),
        height: rd32(t + 24),
        bpp: rd8(t + 28),
        ty: rd8(t + 29),
    })
}

#[test]
fn the_kernel_reads_the_tag_this_test_checks() {
    let mboot = include_str!("../../crates/fl4-kernel/src/mboot.rs");
    assert!(
        mboot.contains(KERNEL_READ),
        "mboot.rs reads the framebuffer tag differently"
    );
}

#[test]
fn both_32_bit_rgb_formats_become_grubs_tag() {
    // GRUB's struct multiboot_tag_framebuffer: 16-bit reserved at 30,
    // colour info at 32, 38 bytes in all.
    for (format, red, blue) in [(0, 0, 16), (1, 16, 0)] {
        let t = gop::tag(0x8000_0000, ANY, 1280, 800, format, 1344).unwrap();
        assert_eq!(
            kernel_reads(&t),
            Some(Framebuffer {
                addr: 0x8000_0000,
                pitch: 1344 * 4,
                width: 1280,
                height: 800,
                bpp: 32,
                ty: 1
            })
        );
        assert_eq!(t[22..24], [0, 0], "reserved");
        assert_eq!(t[24..30], [red, 8, 8, 8, blue, 8], "format {format}");
    }
    assert_eq!(gop::LEN + 8, 38);
}

#[test]
fn addresses_above_4_gib_survive() {
    let base = 0x38_0000_0000;
    let t = gop::tag(base, ANY, 1024, 768, 1, 1024).unwrap();
    assert_eq!(kernel_reads(&t).unwrap().addr, base);
}

#[test]
fn bit_mask_and_blt_only_modes_have_no_tag() {
    for format in [2, 3, 4, u32::MAX] {
        assert_eq!(
            gop::tag(0x8000_0000, ANY, 1024, 768, format, 1024),
            None,
            "format {format}"
        );
    }
}

#[test]
fn empty_or_inconsistent_modes_have_no_tag() {
    assert_eq!(
        gop::tag(0, ANY, 1024, 768, 0, 1024),
        None,
        "no framebuffer address"
    );
    assert_eq!(
        gop::tag(0x8000_0000, ANY, 0, 768, 0, 1024),
        None,
        "zero width"
    );
    assert_eq!(
        gop::tag(0x8000_0000, ANY, 1024, 0, 0, 1024),
        None,
        "zero height"
    );
    assert_eq!(
        gop::tag(0x8000_0000, ANY, 1024, 768, 0, 1023),
        None,
        "scan line shorter than a row"
    );
    assert_eq!(gop::tag(0x8000_0000, ANY, 1024, 768, 0, 0), None);
    // The pitch in bytes does not fit in 32 bits.
    assert_eq!(gop::tag(0x8000_0000, ANY, 1 << 30, 1, 0, 1 << 30), None);
    assert!(gop::tag(0x8000_0000, ANY, (1 << 30) - 1, 1, 0, (1 << 30) - 1).is_some());
    // The framebuffer would end past the address space.
    assert_eq!(gop::tag(u64::MAX - 4095, ANY, 1024, 1, 0, 1024), None);
    assert!(gop::tag(u64::MAX - 4096, ANY, 1024, 1, 0, 1024).is_some());
}

#[test]
fn the_rows_must_fit_in_the_framebuffer() {
    // 1024 pixels of 4 bytes per scan line, 768 lines.
    let bytes = 1024 * 4 * 768;
    assert!(gop::tag(0x8000_0000, bytes, 1000, 768, 0, 1024).is_some());
    assert_eq!(gop::tag(0x8000_0000, bytes - 1, 1000, 768, 0, 1024), None);
    assert_eq!(gop::tag(0x8000_0000, 0, 1000, 768, 0, 1024), None);
}

/// `boot` writes the tag among the fixed tags, before `tags_end` marks
/// where each ExitBootServices attempt rewrites the memory map, and only
/// outside SEV guests.
#[test]
fn the_loader_writes_the_tag_before_the_memory_map_and_not_under_sev() {
    let x86 = include_str!("../../crates/fl4-efi/src/x86.rs");
    let body = &x86[x86.find("pub(super) fn boot(").expect("boot")..];
    let write = body
        .find("info.tag(8, gop::LEN")
        .expect("boot does not write the framebuffer tag");
    let tags_end = body.find("let tags_end = info.used").expect("tags_end");
    assert!(write < tags_end);
    let guard = body[..write]
        .rfind("if mask | shared == 0 {")
        .expect("the framebuffer tag is not behind the SEV and TDX check");
    // The guard's block stays open up to the tag.
    let mut depth = 0;
    for c in body[guard..write].chars() {
        match c {
            '{' => depth += 1,
            '}' if depth == 1 => panic!("the SEV check's block closes before the tag"),
            '}' => depth -= 1,
            _ => {}
        }
    }
    assert!(body[guard..write].contains("framebuffer()"));
}
