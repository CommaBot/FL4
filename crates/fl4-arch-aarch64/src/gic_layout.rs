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

/// GICD_IGROUPR for the implemented interrupts `bits` of one bank. GICv3:
/// group 1. GICv2: group 0, as seL4's gic_v2.c: where the register is
/// writable (one security state, or the Secure view) a group 1 interrupt
/// reads 1022 from GICC_IAR unless AckCtl is set, and the Non-Secure view
/// makes the register RAZ/WI, so the zero changes nothing there.
pub fn spi_groups(gicv3: bool, bits: u32) -> u32 {
    if gicv3 { bits } else { 0 }
}

/// GICv2 GICC_CTLR: EnableGrp0 | EnableGrp1 | AckCtl where the Secure (or
/// only) view is the one seen, so GICC_IAR acknowledges a group 1
/// interrupt firmware left behind instead of reading 1022 for it forever.
/// FIQEn stays clear, so group 0 still signals IRQ.
/// In the Non-Secure view bit 0 is EnableGrp1 and bits 1 and 2 are RES0
/// there, as with the 3 written before.
pub const V2_GICC_CTLR: u32 = 0b111;

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
/// the last frame, or the end. Redistributors are `stride` bytes apart (a
/// device tree's `redistributor-stride`), or 0: each right after the
/// previous one's frames. Returns where the walk ended: past the last
/// redistributor visited (which can be past `base + len`: its VLPI frames;
/// with a stride, the padding after the last one up to `base + len`), and
/// whether that one is the frame marked last. None when the stride is
/// smaller than a redistributor's frames.
fn walk(base: u64, len: u64, stride: u64, typer: impl Fn(u64) -> u64, mut visit: impl FnMut(u64, u64) -> bool) -> Option<(u64, bool)> {
    // A range past the address space, a base off a page (GICR_TYPER is
    // read from it), or a stride off 64 KiB is no layout.
    let end = base.checked_add(len)?;
    if base & 0xfff != 0 || (stride != 0 && stride & 0xffff != 0) {
        return None;
    }
    let mut a = base;
    let mut reached = base;
    let mut visited = 0usize;
    while a.checked_add(GICR_FRAME).is_some_and(|f| f <= end) {
        let t = typer(a);
        let size = frame_size(t);
        if stride != 0 && stride < size {
            return None;
        }
        let frames_end = a.checked_add(size)?;
        visited += 1;
        if t & TYPER_LAST != 0 {
            visit(a, t);
            let padded = if stride != 0 { a.saturating_add(stride).min(end) } else { frames_end };
            return Some((frames_end.max(padded), true));
        }
        let next = a.checked_add(if stride != 0 { stride } else { size })?;
        reached = next;
        if !visit(a, t) {
            return Some((reached, false));
        }
        a = next;
    }
    // Not one redistributor whole in the range, or a next one begun in it
    // whose RD and SGI frames do not fit (its registers unseen). Ending
    // exactly at the range's end, or past it (VLPI frames), is whole.
    if visited == 0 || a < end {
        return None;
    }
    Some((reached, false))
}

/// Visit every redistributor frame in the `len` mapped bytes from `base`
/// (`walk`, `stride` apart), with its GICR_TYPER, up to the frame marked
/// last. False on a stride smaller than a redistributor.
pub fn for_each_frame(base: u64, len: u64, stride: u64, typer: impl Fn(u64) -> u64, mut visit: impl FnMut(u64, u64)) -> bool {
    walk(base, len, stride, typer, |a, t| {
        visit(a, t);
        true
    })
    .is_some()
}

/// The redistributor for affinity `aff` (GICR_TYPER[63:32]) among the
/// `len` mapped bytes from `base`: one whose RD and SGI frames are all
/// mapped, never one past the end or past the frame marked last.
pub fn find_frame(base: u64, len: u64, aff: u64, typer: impl Fn(u64) -> u64) -> Option<u64> {
    find_frame_strided(base, len, 0, aff, typer)
}

/// `find_frame` with redistributors `stride` bytes apart (0: packed).
pub fn find_frame_strided(base: u64, len: u64, stride: u64, aff: u64, typer: impl Fn(u64) -> u64) -> Option<u64> {
    let mut found = None;
    walk(base, len, stride, typer, |a, t| {
        if t >> 32 == aff {
            found = Some(a);
            false
        } else {
            true
        }
    })?;
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
    reserve_strided(base, raw_len, len, 0, typer)
}

/// `reserve` with redistributors `stride` bytes apart (0: packed); None
/// also when the stride is smaller than a redistributor.
pub fn reserve_strided(base: u64, raw_len: u64, len: u64, stride: u64, typer: impl Fn(u64) -> u64) -> Option<u64> {
    let (end, last) = walk(base, len, stride, typer, |_, _| true)?;
    if raw_len == 0 && !last {
        return None;
    }
    Some((end - base).max(len))
}

/// How many bytes from `base` the redistributors found in its `len`
/// mapped bytes occupy: more than `len` where the last has VLPI frames
/// (a MADT GICC entry gives each core's RD and SGI frames only).
pub fn span(base: u64, len: u64, typer: impl Fn(u64) -> u64) -> u64 {
    walk(base, len, 0, typer, |_, _| true).map_or(0, |w| w.0 - base)
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

/// Interrupt priorities (lower is more urgent) and the priority mask the
/// kernel timer's acknowledge beside the serial gate uses (gic.rs
/// `ack_timer_only`): each core's remote-call SGI, then its kernel timer,
/// are above the mask; every other interrupt (SPIs, LPIs, other SGIs and
/// PPIs) is at `PRIO`, at or below it. The values differ in their upper
/// three bits, so they keep their order in every view: any implemented
/// width (`stored`) and a GICv2's Non-secure view (`stored_ns`).
pub const REMOTE_PRIO: u32 = 0x40;
pub const TIMER_PRIO: u32 = 0x60;
pub const TIMER_PMR: u32 = 0x80;
pub const PRIO: u32 = 0xa0;
/// The priority mask that masks nothing.
pub const PMR_OPEN: u32 = 0xff;

/// What a priority field (or priority mask) with `bits` implemented bits
/// (4 to 8: the upper ones) holds after `p` is written in its Secure view,
/// a GIC with one security state, or GICv3 group 1.
pub fn stored(p: u32, bits: u32) -> u32 {
    let bits = bits.clamp(1, 8);
    p & (0xffu32 << (8 - bits)) & 0xff
}

/// What it holds after a Non-secure write of `p` to a GIC with two
/// security states (a GICv2's Non-secure view; a GICv3 with
/// GICD_CTLR.DS 0: its priority registers, and ICC_PMR_EL1 if
/// SCR_EL3.FIQ is 1): `(p >> 1) | 0x80` (GIC architecture v2, "Software
/// views of interrupt priority"; IHI 0069 4.8.6). This, `stored`'s value,
/// is what the GIC compares.
pub fn stored_ns(p: u32, bits: u32) -> u32 {
    stored((p >> 1) | 0x80, bits)
}

/// What a Non-secure read returns of a field so written: the stored value
/// shifted back, `(stored_ns << 1) & 0xff`. Read back, a shifted and an
/// unshifted field look alike, though the GIC compares different values.
pub fn readback_ns(p: u32, bits: u32) -> u32 {
    (stored_ns(p, bits) << 1) & 0xff
}

/// GICv3: the value to write to a priority register and to ICC_PMR_EL1 to
/// tell whether each is shifted (`stored_ns`): the least significant
/// implemented bit, for `pribits` (ICC_CTLR_EL1.PRIbits + 1) of 5 to 8;
/// 0 otherwise. Shifted, it is lost and reads back as 0.
pub fn v3_view_probe(pribits: u32) -> u32 {
    if (5..=8).contains(&pribits) {
        1u32 << (8 - pribits)
    } else {
        0
    }
}

/// GICv3: whether the priority registers and ICC_PMR_EL1 store priorities
/// alike, so that their read-back values compare as the GIC compares
/// them: from GICD_CTLR.DS (`ds`), `pribits` and what `v3_view_probe`'s
/// value read back as from a priority register (`prio_probe`) and from
/// ICC_PMR_EL1 (`pmr_probe`). With one security state (DS 1) neither is
/// shifted; with two, Non-secure priority registers are, and ICC_PMR_EL1
/// is only if SCR_EL3.FIQ is 1 (Linux `gic_has_group0`,
/// `gic_prio_masking`): with FIQ 0 the mask `TIMER_PMR` would hide the
/// timer itself.
pub fn v3_same_priority_view(ds: bool, pribits: u32, prio_probe: u32, pmr_probe: u32) -> bool {
    if !(5..=8).contains(&pribits) {
        return false;
    }
    if ds {
        prio_probe != 0 && pmr_probe != 0
    } else {
        prio_probe == 0 && pmr_probe == 0
    }
}

/// Whether the priorities read back from the GIC (the remote-call SGI's,
/// the kernel timer's, an interrupt left at `PRIO`), and the mask read
/// back after `TIMER_PMR` was written, let `ack_timer_only` acknowledge
/// the timer and the remote-call SGI and nothing else: both strictly
/// above the mask (an interrupt is signalled only above it), the other at
/// or below.
pub fn timer_only_ok(remote: u32, timer: u32, mask: u32, other: u32) -> bool {
    remote < mask && timer < mask && mask <= other
}

/// A GIC's acknowledge (GICC_IAR, ICC_IAR1_EL1) under priority mask
/// `pmr`, for host tests: the most urgent of the `pending` (ID, priority)
/// pairs strictly above the mask (the lowest ID among equals), or 1023.
pub fn acknowledge(pmr: u32, pending: &[(u64, u32)]) -> u64 {
    let mut best: Option<(u64, u32)> = None;
    for &(id, p) in pending {
        if p < pmr && best.is_none_or(|(bid, bp)| p < bp || (p == bp && id < bid)) {
            best = Some((id, p));
        }
    }
    best.map_or(1023, |(id, _)| id)
}

/// The interrupt ID in an acknowledge value: GICv3's whole value (its
/// INTIDs reach past 1023: extended SPIs and PPIs, LPIs), GICv2's low ten
/// bits (an SGI's source core is above them).
pub fn raw_id(gicv3: bool, raw: u64) -> u64 {
    if gicv3 { raw } else { raw & 0x3ff }
}

/// Whether an acknowledge value is a special INTID (1020..=1023: no
/// interrupt was acknowledged, so none is ended).
pub fn is_spurious(gicv3: bool, raw: u64) -> bool {
    raw == 1023 || (1020..=1023).contains(&raw_id(gicv3, raw))
}

/// Whether an acknowledge value is a real GICv3 interrupt the kernel has
/// no IRQ for: an extended SPI or PPI, or a reserved INTID, from 1024 up
/// to the first LPI (`lpi_id_base`). It was acknowledged, so it must be
/// ended (its running priority would otherwise block every interrupt of
/// equal or lower priority on the core), then dropped.
pub fn is_unsupported(gicv3: bool, raw: u64, lpi_id_base: u64) -> bool {
    gicv3 && (1024..lpi_id_base).contains(&raw_id(gicv3, raw))
}

/// GICD_TYPER: whether the distributor has LPIs (LPIS, bit 17), interrupt
/// ID bits (IDbits, bits 19..23, plus one) for `lpi_id_bits`, and, where it
/// bounds them (num_LPIs, bits 11..15, nonzero: 2^(num_LPIs + 1) LPIs),
/// at least `min_lpis` LPIs.
pub fn lpi_supported(gicv3: bool, gicd_typer: u32, lpi_id_bits: u64, min_lpis: u64) -> bool {
    let t = gicd_typer as u64;
    let num_lpis = (t >> 11) & 0x1f;
    gicv3
        && t & (1 << 17) != 0
        && ((t >> 19) & 0x1f) + 1 >= lpi_id_bits
        && (num_lpis == 0 || 1u64 << (num_lpis + 1) >= min_lpis)
}

/// An ITS's control and translation frames (64 KiB each): what the kernel
/// maps.
pub const ITS_SIZE: u64 = 0x2_0000;
/// A GICv4.1 ITS has a third frame, the virtual SGI frame (GITS_SGIR at
/// 0x2_0020), which is not user space's either (IHI 0069 12.18).
pub const ITS_SIZE_V4_1: u64 = 0x3_0000;
/// GITS_TYPER.VSGI (bit 39; bit 37 is VMOVP).
pub const ITS_TYPER_VSGI: u64 = 1 << 39;
/// GITS_TYPER fields only a GICv4.1 ITS has (RES0 before): VSGI, VMAPP
/// (40), SVPET (41..42), nID (43).
pub const ITS_TYPER_V4_1: u64 = 1 << 39 | 1 << 40 | 3 << 41 | 1 << 43;
/// GITS_PIDR2 (its ArchRev, bits 4..7: 3 for GICv3, 4 for GICv4).
pub const GITS_PIDR2: u64 = 0xffe8;

/// The bytes from its base an ITS occupies, from its GITS_TYPER, its
/// GITS_PIDR2 and the size the tables gave (`raw_len`, 0 when they give
/// none). A given size is the ITS's (a GICv4.0 ITS has two frames, and the
/// next device may follow them), unless it is less than two frames, or
/// than three for an ITS that shows GICv4.1 features: None, the tables
/// contradict the hardware. With none given: three frames for any GICv4
/// ITS (ArchRev 4; GICv4.1's vSGI frame may be there) or one that shows
/// GICv4.1 features, two otherwise.
pub fn its_span(typer: u64, pidr2: u32, raw_len: u64) -> Option<u64> {
    let v4_1 = typer & ITS_TYPER_V4_1 != 0;
    let arch_rev = (pidr2 >> 4) & 0xf;
    if raw_len != 0 {
        if raw_len < ITS_SIZE || (v4_1 && raw_len < ITS_SIZE_V4_1) {
            return None;
        }
        return Some(raw_len);
    }
    Some(if arch_rev >= 4 || v4_1 { ITS_SIZE_V4_1 } else { ITS_SIZE })
}

/// Whether an ITS is still set up by whoever ran before the kernel (a warm
/// takeover, whose caches may hold translations of the old tables): it
/// was enabled, or its command queue or a table is valid. Only these reset
/// to zero (IHI 0069 12.19.1-2); addresses and the queue's offsets reset
/// to UNKNOWN values, so they tell nothing. `basers`: GITS_BASER0 to 7.
pub fn its_is_warm(was_enabled: bool, cbaser: u64, basers: &[u64; 8]) -> bool {
    was_enabled || cbaser & BASER_VALID != 0 || basers.iter().any(|&b| b & BASER_VALID != 0)
}

/// Whether the kernel may take an ITS over: one that invalidates its
/// caches when its tables are made invalid (GITS_TYPER.INV) always; one
/// that does not only when it is not `warm` and the boot path guarantees
/// it comes from reset unused (`trusted_cold_handoff`), its caches empty.
pub fn its_takeover_allowed(inv: bool, warm: bool, trusted_cold_handoff: bool) -> bool {
    inv || (!warm && trusted_cold_handoff)
}

/// A distributor at `base` that the tables gave `raw_len` bytes (0: no
/// size) on GIC `version`: what the kernel maps of it and what it keeps
/// from user space, `(map_len, reserve_len)`. GICv3's is 64 KiB; a GICv2
/// one can be a single page (GIC-400 boards with the CPU interface right
/// after it). None when it is at 0, off a page, smaller than that, or past
/// `pa_limit`.
pub fn gicd_extent(version: u64, base: u64, raw_len: u64, pa_limit: u64) -> Option<(u64, u64)> {
    let min = if version == 3 { 0x1_0000 } else { 0x1000 };
    if base == 0 || base & 0xfff != 0 || (raw_len != 0 && raw_len < min) {
        return None;
    }
    let reserve = raw_len.max(min);
    base.checked_add(reserve).is_some_and(|e| e <= pa_limit).then_some((min, reserve))
}

/// GICD_TYPER: extended SPIs the distributor implements (ESPI, bit 8;
/// ESPI_range, bits 27..31: 32 per step), from INTID 4096.
pub fn espi_count(gicd_typer: u32) -> u64 {
    if gicd_typer & (1 << 8) == 0 { 0 } else { (((gicd_typer >> 27) & 0x1f) as u64 + 1) * 32 }
}

/// GICR_TYPER.PPInum (bits 27..31): words of extended PPIs from INTID 1056
/// (0: none, 1: up to 1087, 2: up to 1119).
pub fn eppi_words(gicr_typer: u64) -> u64 {
    ((gicr_typer >> 27) & 0x1f).min(2)
}

/// Table base register fields (IHI 0069 12.19, 12.11).
pub const BASER_VALID: u64 = 1 << 63;
const BASER_INDIRECT: u64 = 1 << 62;
/// GITS_BASER<n> page size field values: 4, 16 and 64 KiB.
pub const BASER_PSZ_4K: u64 = 0;
pub const BASER_PSZ_16K: u64 = 1;
pub const BASER_PSZ_64K: u64 = 2;

/// The physical address a GITS_BASER<n> value gives, for its page size
/// field `psz` (64 KiB pages put PA[51:48] in bits 12..15).
pub fn its_baser_pa(v: u64, psz: u64) -> u64 {
    if psz == BASER_PSZ_64K {
        (v & 0x0000_ffff_ffff_0000) | ((v >> 12) & 0xf) << 48
    } else {
        v & 0x0000_ffff_ffff_f000
    }
}

/// Whether GITS_BASER<n> reads back as asked: valid, flat, page size
/// `psz`, `pages` pages (the Size field, minus one), at `pa`.
pub fn its_baser_ok(got: u64, pa: u64, psz: u64, pages: u64) -> bool {
    got & BASER_VALID != 0
        && got & BASER_INDIRECT == 0
        && (got >> 8) & 3 == psz
        && got & 0xff == pages - 1
        && its_baser_pa(got, psz) == pa
}

/// Whether GITS_CBASER reads back as asked: valid, `pages` 4 KiB pages
/// at `pa`.
pub fn its_cbaser_ok(got: u64, pa: u64, pages: u64) -> bool {
    got & BASER_VALID != 0 && got & 0x000f_ffff_ffff_f000 == pa && got & 0xff == pages - 1
}

/// Whether GICR_PROPBASER reads back as asked: the table at `pa` for
/// `id_bits` interrupt ID bits.
pub fn propbaser_ok(got: u64, pa: u64, id_bits: u64) -> bool {
    got & 0x000f_ffff_ffff_f000 == pa && got & 0x1f == id_bits - 1
}

/// Whether GICR_PENDBASER reads back as asked: the table at `pa`.
pub fn pendbaser_ok(got: u64, pa: u64) -> bool {
    got & 0x000f_ffff_ffff_0000 == pa
}

/// The memory attributes of a GICR_PROPBASER or GICR_PENDBASER value
/// (shareability, inner and outer cacheability): every redistributor must
/// read back the same.
pub fn gicr_baser_attrs(v: u64) -> u64 {
    v & (3 << 10 | 7 << 7 | 7 << 56)
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
