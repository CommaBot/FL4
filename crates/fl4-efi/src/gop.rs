//! The Multiboot 2 framebuffer tag (type 8) for the firmware's current
//! Graphics Output mode (x86.rs `boot`). A plain function, so host tests
//! run it.

/// The tag's bytes after its type and size words. The layout is GRUB's
/// `struct multiboot_tag_framebuffer` (include/multiboot2.h) for direct
/// RGB, as GRUB writes it (multiboot_mbi2.c): address, pitch, width,
/// height, bpp, type, a 16-bit reserved field, then the red, green and
/// blue field positions and mask sizes. The kernel reads the first 22
/// bytes (mboot.rs).
pub const LEN: usize = 30;

/// The payload for a linear framebuffer at `base`, `size` bytes long,
/// `width` by `height` pixels with `per_line` pixels per scan line, in
/// UEFI pixel format `format`. Only the two 32-bit RGB formats have a
/// fixed layout: none for a bit mask or Blt-only mode, nor for an empty
/// or inconsistent one, including one whose rows do not fit in `size`.
pub fn tag(
    base: u64,
    size: u64,
    width: u32,
    height: u32,
    format: u32,
    per_line: u32,
) -> Option<[u8; LEN]> {
    // PixelRedGreenBlueReserved8BitPerColor puts red in the first byte,
    // PixelBlueGreenRedReserved8BitPerColor blue.
    let (red, blue) = match format {
        0 => (0, 16),
        1 => (16, 0),
        _ => return None,
    };
    let pitch = per_line.checked_mul(4)?;
    if base == 0 || width == 0 || height == 0 || per_line < width {
        return None;
    }
    let bytes = pitch as u64 * height as u64;
    if bytes > size {
        return None;
    }
    base.checked_add(bytes)?;
    let mut t = [0; LEN];
    t[0..8].copy_from_slice(&base.to_le_bytes());
    t[8..12].copy_from_slice(&pitch.to_le_bytes());
    t[12..16].copy_from_slice(&width.to_le_bytes());
    t[16..20].copy_from_slice(&height.to_le_bytes());
    t[20] = 32;
    t[21] = 1;
    t[24..30].copy_from_slice(&[red, 8, 8, 8, blue, 8]);
    Some(t)
}
