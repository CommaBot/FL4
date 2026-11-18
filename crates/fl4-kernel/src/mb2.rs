//! Walking Multiboot 2 boot information (no kernel dependencies, so the
//! backend's host tests include this file too).

/// Visit the tags of the Multiboot 2 information at `info` in order, as
/// `f(address, type, size)`, up to the end tag. `rd32` reads a 32-bit word.
///
/// A tag must hold its own 8-byte header and lie inside the information's
/// total size; the walk stops at the first that does not. (A size of 0
/// would otherwise never advance: the boot CPU would spin before printing
/// anything.)
pub fn tags(info: u64, rd32: impl Fn(u64) -> u32, mut f: impl FnMut(u64, u32, u64)) {
    let end = info.saturating_add(rd32(info) as u64);
    let mut t = info + 8;
    while t.saturating_add(8) <= end {
        let ty = rd32(t);
        let size = rd32(t + 4) as u64;
        if ty == 0 || size < 8 || size > end - t {
            break;
        }
        f(t, ty, size);
        t += (size + 7) & !7;
    }
}
