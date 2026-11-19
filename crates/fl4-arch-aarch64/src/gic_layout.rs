//! Arithmetic over the GIC's register layout that touches no hardware, so
//! the host tests run it (xtask/tests/aarch64_boot.rs).

/// A GICv3 redistributor's RD and SGI frames (64 KiB each).
pub const GICR_FRAME: u64 = 0x2_0000;
/// With virtual LPIs (GICv4) a redistributor has two more frames.
pub const GICR_FRAME_VLPI: u64 = 0x4_0000;
/// GICR_TYPER: virtual LPIs (the VLPI frames follow) and the last frame.
const TYPER_VLPIS: u64 = 1 << 1;
const TYPER_LAST: u64 = 1 << 4;

/// Interrupt IDs the distributor's per-interrupt registers cover, from
/// GICD_TYPER: (ITLinesNumber + 1) * 32, short of the special INTIDs
/// 1020..1023 (IHI 0069: GICD_IPRIORITYR<n> and GICD_ITARGETSR<n> stop at
/// n = 254, GICD_IROUTER<n> at n = 1019; past them is reserved).
pub fn dist_lines(typer: u32) -> u64 {
    (((typer as u64 & 0x1f) + 1) * 32).min(1020)
}

/// Of the 32 interrupts from `first` (a multiple of 32), the bits of the
/// ones below `lines`: what a one-bit-per-interrupt register (enable,
/// pending, active, group) may be written with.
pub fn bank_bits(first: u64, lines: u64) -> u32 {
    if first >= lines {
        0
    } else if lines - first >= 32 {
        u32::MAX
    } else {
        (1u32 << (lines - first)) - 1
    }
}

/// GICv2: the GICD_ITARGETSR word that sends four SPIs to the calling
/// core, from its banked GICD_ITARGETSR0 (each byte that core's own CPU
/// interface bit). A uniprocessor GIC reads it as zero: interface 0.
pub fn v2_targets(itargetsr0: u32) -> u32 {
    let mut t = itargetsr0;
    t |= t >> 16;
    t |= t >> 8;
    let t = t & 0xff;
    (if t == 0 { 1 } else { t }) * 0x0101_0101
}

/// GICv2 CPU interfaces: GICD_ITARGETSR and GICD_SGIR target lists have
/// eight bits.
pub const V2_INTERFACES: usize = 8;

/// GICv2: the CPU interface bits a core's banked GICD_ITARGETSR0 gives
/// (each byte that core's own bit; zero on a uniprocessor GIC).
pub fn v2_interface(itargetsr0: u32) -> u64 {
    let mut t = itargetsr0;
    t |= t >> 16;
    t |= t >> 8;
    (t & 0xff) as u64
}

/// GICv2: whether SGIs can reach a core whose interface bits are `mine`
/// beside cores with `others`: exactly one interface, no other core's. A
/// core with none (or several) would be sent SGIs that reach nobody (or
/// another core too), so a remote call to it would never return.
pub fn v2_interface_ok(mine: u64, others: impl IntoIterator<Item = u64>) -> bool {
    mine < 1 << V2_INTERFACES && mine.is_power_of_two() && others.into_iter().all(|o| o != mine)
}

/// GICv3: whether SGIs can name Aff0 values of 16 and more: ICC_SGI1R_EL1's
/// range selector (RS, bits 44..47) is RES0 unless both the distributor
/// (GICD_TYPER.RSS, bit 26) and the sending core's CPU interface
/// (ICC_CTLR_EL1.RSS, bit 18) support it (IHI 0069).
pub fn v3_rss(gicd_typer: u32, icc_ctlr: u64) -> bool {
    gicd_typer & (1 << 26) != 0 && icc_ctlr & (1 << 18) != 0
}

/// GICv3: whether an SGI can name a core with affinity 0 `aff0`: without
/// the range selector only targets 0..15 exist, and a larger value would
/// reach the core at `aff0 % 16` instead.
pub fn v3_sgi_reaches(aff0: u64, rss: bool) -> bool {
    aff0 < 16 || rss
}

/// A redistributor's size from its GICR_TYPER.
fn frame_size(typer: u64) -> u64 {
    if typer & TYPER_VLPIS != 0 { GICR_FRAME_VLPI } else { GICR_FRAME }
}

/// Visit the redistributors in the `len` mapped bytes from `base`: each
/// one whose RD and SGI frames lie wholly inside, with its GICR_TYPER as
/// `typer` reads it (at the frame's first page), until `visit` says stop,
/// the last frame, or the end. Returns where the walk ended: past the last
/// redistributor visited (which can be past `base + len`: its VLPI frames),
/// and whether that one is the frame marked last.
fn walk(base: u64, len: u64, typer: impl Fn(u64) -> u64, mut visit: impl FnMut(u64, u64) -> bool) -> (u64, bool) {
    let Some(end) = base.checked_add(len) else { return (base, false) };
    let mut a = base;
    let mut reached = base;
    while a.checked_add(GICR_FRAME).is_some_and(|f| f <= end) {
        let t = typer(a);
        let Some(next) = a.checked_add(frame_size(t)) else { break };
        reached = next;
        if t & TYPER_LAST != 0 {
            visit(a, t);
            return (reached, true);
        }
        if !visit(a, t) {
            break;
        }
        a = next;
    }
    (reached, false)
}

/// The redistributor for affinity `aff` (GICR_TYPER[63:32]) among the
/// `len` mapped bytes from `base`: one whose RD and SGI frames are all
/// mapped, never one past the end or past the frame marked last.
pub fn find_frame(base: u64, len: u64, aff: u64, typer: impl Fn(u64) -> u64) -> Option<u64> {
    let mut found = None;
    walk(base, len, typer, |a, t| {
        if t >> 32 == aff {
            found = Some(a);
            false
        } else {
            true
        }
    });
    found
}

/// What boot keeps from user space of a redistributor range at `base`
/// that the tables gave `raw_len` bytes (0: no bound, up to the frame
/// marked last) and that is mapped for `len` bytes: the bytes from `base`
/// its redistributors occupy, at least `len`. None when the range had no
/// bound and the frame marked last is not within the mapping: where its
/// redistributors end is then unknown, and those past the mapping would
/// be user space's device memory.
pub fn reserve(base: u64, raw_len: u64, len: u64, typer: impl Fn(u64) -> u64) -> Option<u64> {
    let (end, last) = walk(base, len, typer, |_, _| true);
    if raw_len == 0 && !last {
        return None;
    }
    Some((end - base).max(len))
}

/// How many bytes from `base` the redistributors found in its `len`
/// mapped bytes occupy: more than `len` where the last has VLPI frames
/// (a MADT GICC entry gives each core's RD and SGI frames only).
pub fn span(base: u64, len: u64, typer: impl Fn(u64) -> u64) -> u64 {
    walk(base, len, typer, |_, _| true).0 - base
}

/// Record redistributor range (`base`, `len`; `len` 0: up to the frame
/// marked last) among the `*n` ranges of `ranges`. A bounded range that
/// overlaps recorded bounded ranges is merged with them into one covering
/// all: a MADT can give a GICR discovery range and its cores' GICC
/// redistributors in either order, and keeping only the first range from
/// a base (a core's two frames) would hand the rest of the discovery range
/// to user space, while recording each core's frames inside a discovery
/// range separately would fill `ranges`. Unbounded ranges are only
/// deduplicated. Returns false when the range cannot be recorded (no room,
/// address 0, or an end past the address space): the boot then fails
/// rather than give the range to user space.
pub fn add_redistributors(ranges: &mut [(u64, u64)], n: &mut usize, base: u64, len: u64) -> bool {
    if base == 0 {
        return false;
    }
    if len == 0 {
        if ranges[..*n].contains(&(base, 0)) {
            return true;
        }
        if *n == ranges.len() {
            return false;
        }
        ranges[*n] = (base, 0);
        *n += 1;
        return true;
    }
    let Some(mut end) = base.checked_add(len) else { return false };
    let mut start = base;
    // Absorb every overlapping bounded range, until none is left: merging
    // can widen the range over further recorded ones.
    loop {
        let mut merged = false;
        let mut i = 0;
        while i < *n {
            let (b, l) = ranges[i];
            if l != 0 && b < end && start < b + l {
                start = start.min(b);
                end = end.max(b + l);
                ranges.copy_within(i + 1..*n, i);
                *n -= 1;
                merged = true;
            } else {
                i += 1;
            }
        }
        if !merged {
            break;
        }
    }
    if *n == ranges.len() {
        return false;
    }
    ranges[*n] = (start, end - start);
    *n += 1;
    true
}

/// Whether core `me` changes interrupt `id`'s enable or trigger bits for
/// `core` by a remote call to that core. A GICv2 distributor banks IDs
/// 0..31 per CPU interface, so only the core itself reaches its copy
/// (another core writing them changes its own); GICv3 keeps every core's
/// in that core's redistributor, which any core reaches, and an SPI's are
/// in the distributor, shared by all.
pub fn banked_remote(gicv3: bool, id: u64, core: u64, me: u64) -> bool {
    !gicv3 && id < 32 && core != me
}
