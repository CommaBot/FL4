// The kernel crate builds only for its target; this exercises its
// Multiboot 2 tag walk in the backend's host-test harness.
#[path = "../../fl4-kernel/src/mb2.rs"]
mod mb2;

use std::cell::Cell;

/// Multiboot 2 information at address 0x1000 built from `(type, size,
/// payload words)` tags; `size` is written as given, padding follows the
/// 8-byte alignment of the real size.
fn info(tags: &[(u32, u32, &[u32])]) -> Vec<u32> {
    let mut w = vec![0, 0];
    for &(ty, size, body) in tags {
        w.push(ty);
        w.push(size);
        w.extend_from_slice(body);
        while w.len() % 2 != 0 {
            w.push(0);
        }
    }
    w.push(0);
    w.push(8);
    w[0] = (w.len() * 4) as u32;
    w
}

/// Walk `words`, failing (rather than hanging) after far more reads than
/// any finite walk of them needs.
fn walk(words: &[u32]) -> Vec<(u64, u32, u64)> {
    let reads = Cell::new(0);
    let mut seen = Vec::new();
    mb2::tags(
        0x1000,
        |a| {
            reads.set(reads.get() + 1);
            assert!(reads.get() < 10_000, "tag walk does not terminate");
            let i = ((a - 0x1000) / 4) as usize;
            words.get(i).copied().unwrap_or(0xdead_beef)
        },
        |t, ty, size| seen.push((t, ty, size)),
    );
    seen
}

#[test]
fn walks_well_formed_tags_to_the_end_tag() {
    let w = info(&[(1, 12, &[0x41]), (6, 16 + 24, &[24, 0, 1, 2, 3, 4, 5, 6])]);
    assert_eq!(walk(&w), [(0x1008, 1, 12), (0x1018, 6, 40)]);
}

#[test]
fn zero_sized_tag_stops_the_walk() {
    // A tag of size 0 used to leave the walk on the same tag forever.
    let w = info(&[(1, 12, &[0x41]), (14, 0, &[]), (6, 40, &[24, 0, 1, 2, 3, 4, 5, 6])]);
    assert_eq!(walk(&w), [(0x1008, 1, 12)]);
}

#[test]
fn short_or_overlong_tags_stop_the_walk() {
    for bad in [1u32, 7, 0x1000] {
        let w = info(&[(1, 12, &[0x41]), (14, bad, &[0, 0])]);
        assert_eq!(walk(&w), [(0x1008, 1, 12)], "size {bad}");
    }
}
