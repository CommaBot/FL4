//! The GICv3 ITS (GIC architecture specification, IHI 0069, chapters 5
//! and 6): MSIs of PCI functions become LPIs, the kernel's IRQs from
//! `irq::LPI_BASE` (`fl4_core` `GetMSI`). Boot gives the ITS its tables
//! and every redistributor its LPI tables; afterwards `map` and `unmap`
//! issue the commands for one event at a time, under the serial gate.
//!
//! Every table is in kernel RAM that user space never gets. The kernel
//! writes the command queue and the LPI configuration table, and cleans
//! what it wrote to the point of coherency whatever shareability the ITS
//! accepted (where it accepts only non-shareable, it is asked for
//! non-cacheable memory, IHI 0069); the tables the GIC itself writes are
//! cleaned once, empty, at boot, and a device slot's ITT again, zeroed,
//! each time `map` gives the slot to a device (before its MAPD), so no
//! line the ITS wrote for an earlier device is read back or written over
//! it later.
//!
//! LPIs are edge triggered and have no active state: they are not masked
//! between a signal and its acknowledgement (as MSIs on x86_64), and a
//! deleted handler's event is discarded.
use crate::cpu;
use crate::gic_layout as gl;
use core::cell::UnsafeCell;
use fl4_core::layout::{irq, pptr};

/// Events per device (each device's ITT holds this many).
pub const EVENTS: u64 = 64;
const EVENT_BITS: u64 = 6;
/// Devices with an ITT at once.
pub const MAX_DEVICES: usize = 32;
/// Device IDs the device table covers at most: PCI requester IDs of
/// buses 0-15.
const DEVICE_IDS: u64 = 4096;

const PAGE64K: u64 = 0x1_0000;
/// The memory `init` lays out from its 64 KiB aligned base: the LPI
/// configuration table, the command queue, the device table, the
/// collection table, the ITTs, the vPE table (GICv4, kept empty), then one
/// pending table per core.
const PROP_OFF: u64 = 0;
const CMD_OFF: u64 = PAGE64K;
const DEV_OFF: u64 = 2 * PAGE64K;
const COLL_OFF: u64 = 3 * PAGE64K;
const ITT_OFF: u64 = 4 * PAGE64K;
const VPE_OFF: u64 = 5 * PAGE64K;
const PEND_OFF: u64 = 6 * PAGE64K;
const CMD_BYTES: u64 = PAGE64K;
const CMD_SLOTS: u64 = CMD_BYTES / 32;

/// Bytes `init` needs for `ncpus` cores, 64 KiB aligned.
pub const fn memory_size(ncpus: usize) -> u64 {
    PEND_OFF + ncpus as u64 * PAGE64K
}

/// LPI interrupt ID bits the configuration table covers (8192 + 8192).
const LPI_ID_BITS: u64 = 14;
const _: () = assert!(irq::LPI_ID_BASE + irq::NUM_LPIS <= 1 << LPI_ID_BITS);
const _: () = assert!(crate::percpu::MAX_CPUS <= u8::MAX as usize && (MAX_DEVICES as u64) < u8::MAX as u64 && EVENTS <= u8::MAX as u64);
/// LPI configuration table bit 1 is RES1 (IHI 0069: Non-secure Group 1).
const LPI_GROUP1: u8 = 1 << 1;
/// A disabled LPI at the priority of every other interrupt (gic.rs): what
/// every entry holds from boot and after `unmap`.
const LPI_DISABLED: u8 = 0xa0 | LPI_GROUP1;
/// An enabled LPI.
const LPI_ENABLED: u8 = LPI_DISABLED | 1;
/// Bytes of the LPI configuration table: one per LPI ID from 8192.
const PROP_BYTES: u64 = (1 << LPI_ID_BITS) - irq::LPI_ID_BASE;
const _: () = assert!(PROP_BYTES <= CMD_OFF - PROP_OFF);

const GITS_CTLR: u64 = 0x0;
const GITS_TYPER: u64 = 0x8;
const GITS_CBASER: u64 = 0x80;
const GITS_CWRITER: u64 = 0x88;
const GITS_CREADR: u64 = 0x90;
const GITS_BASER: u64 = 0x100;
/// GITS_CTLR: Enabled, and Quiescent (read only).
const CTLR_ENABLED: u32 = 1;
const CTLR_QUIESCENT: u32 = 1 << 31;
/// GITS_TYPER.INV (bit 46): making a table invalid invalidates the ITS's
/// cached translations from it.
const ITS_TYPER_INV: u64 = 1 << 46;
/// The translation frame's doorbell, 64 KiB into the ITS.
pub const GITS_TRANSLATER: u64 = 0x1_0040;
pub use crate::gic_layout::{ITS_SIZE, ITS_SIZE_V4_1, its_span as span_from_typer};
const _: () = assert!(ITS_SIZE == 2 * PAGE64K);

/// `span_from_typer` of the ITS mapped at `va` (None: the size the tables
/// gave contradicts the hardware).
pub fn span(va: u64, raw_len: u64) -> Option<u64> {
    span_from_typer(rd64(va + GITS_TYPER), rd32(va + gl::GITS_PIDR2), raw_len)
}

/// Take over the ITS mapped at `va` as boot finds it: disable it (if the
/// firmware left it enabled) and wait until it reports quiescent, which
/// it may not yet be even when disabled. None if it does not; otherwise
/// whether it was enabled (`init`'s `was_enabled`).
pub fn quiesce(va: u64) -> Option<bool> {
    let was_enabled = rd32(va + GITS_CTLR) & CTLR_ENABLED != 0;
    disable_its(va).then_some(was_enabled)
}

/// Turn off LPIs on every redistributor frame of `gicr_regions` (mapped
/// virtual address and length; frames `stride` apart, 0: packed) that the
/// firmware left them on: an enabled redistributor reads and writes the
/// firmware's LPI tables, in memory the kernel hands out. Err where one
/// will not turn off, or a register write does not complete, or the
/// stride is smaller than a redistributor.
pub fn quiesce_redistributors(gicr_regions: &[(u64, u64)], stride: u64) -> Result<(), &'static str> {
    let mut bad = None;
    for &(base, len) in gicr_regions {
        let ok = gl::for_each_frame(base, len, stride, |f| rd64(f + GICR_TYPER), |f, _| {
            if bad.is_some() {
                return;
            }
            if rd32(f + GICR_CTLR) & 1 != 0 {
                wr32(f + GICR_CTLR, rd32(f + GICR_CTLR) & !1);
                if !crate::gic::wait_gicr_rwp(f) || rd32(f + GICR_CTLR) & 1 != 0 {
                    bad = Some("firmware left redistributor LPIs enabled");
                }
            } else if !crate::gic::wait_gicr_rwp(f) {
                bad = Some("redistributor RWP stuck");
            }
        });
        if !ok {
            return Err("bad redistributor stride");
        }
    }
    bad.map_or(Ok(()), Err)
}

/// Why `init` declined.
#[derive(Clone, Copy, Debug)]
pub enum InitError {
    /// The hardware or its configuration is not one the kernel drives: the
    /// ITS is left off and the boot goes on without MSIs.
    Unsupported(&'static str),
    /// The ITS may still be translating (it does not quiesce): the boot
    /// must not go on.
    Unsafe(&'static str),
}

const GICR_CTLR: u64 = 0x0;
const GICR_TYPER: u64 = 0x8;
const GICR_PROPBASER: u64 = 0x70;
const GICR_PENDBASER: u64 = 0x78;

/// Normal, inner and outer write-back read/write-allocate, inner
/// shareable: the attributes the kernel window maps RAM with.
const CACHE_RAWAWB: u64 = 7;
/// Normal, inner non-cacheable: where the GIC takes no shareability.
const CACHE_NC: u64 = 1;
const SHARE_INNER: u64 = 1;
const SHARE_MASK: u64 = 3 << 10;
/// Where the InnerCache field is: GITS_BASER<n> and GITS_CBASER; GICR_PROPBASER
/// and GICR_PENDBASER.
const ITS_CACHE_SHIFT: u64 = 59;
const GICR_CACHE_SHIFT: u64 = 7;

const BASER_VALID: u64 = gl::BASER_VALID;
const BASER_TYPE_NONE: u64 = 0;
const BASER_TYPE_DEVICE: u64 = 1;
const BASER_TYPE_VPE: u64 = 2;
const BASER_TYPE_COLLECTION: u64 = 4;

struct Device {
    id: u64,
    /// Events mapped, a bit each; 0: the slot is free.
    events: u64,
}

struct Its {
    va: u64,
    mem: u64,
    ready: bool,
    pta: bool,
    num_devices: u64,
    /// Bytes of one ITT, 256-aligned.
    itt_size: u64,
    /// Cores with a collection (`init`'s `ncpus`).
    ncpus: usize,
    /// RDbase field of each core's collection (`target`).
    rdbase: [u64; crate::percpu::MAX_CPUS],
    cwriter: u64,
    devices: [Device; MAX_DEVICES],
    /// Per LPI: device slot + 1 (0: unmapped), event, core.
    lpis: [(u8, u8, u8); irq::NUM_LPIS as usize],
    /// A command failed: the ITS takes no more (and `ready` is false for
    /// good).
    failed: bool,
    /// After `failed`: the ITS was disabled and reported quiescent, so it
    /// translates no more events.
    quiesced: bool,
}

struct Global(UnsafeCell<Its>);
// SAFETY: boot runs before the other cores take interrupts or enter the
// kernel; afterwards only kernel entries under the serial gate call
// `map` and `unmap`. Each of `init`, `map`, `unmap` takes the one
// reference (`its()`) at its start and passes it down.
unsafe impl Sync for Global {}

static ITS: Global = Global(UnsafeCell::new(Its {
    va: 0,
    mem: 0,
    ready: false,
    pta: false,
    num_devices: 0,
    itt_size: 0,
    ncpus: 0,
    rdbase: [0; crate::percpu::MAX_CPUS],
    cwriter: 0,
    devices: [const { Device { id: 0, events: 0 } }; MAX_DEVICES],
    lpis: [(0, 0, 0); irq::NUM_LPIS as usize],
    failed: false,
    quiesced: false,
}));

fn its() -> &'static mut Its {
    // SAFETY: see `Global`.
    unsafe { &mut *ITS.0.get() }
}

fn rd32(a: u64) -> u32 {
    unsafe { core::ptr::read_volatile(a as *const u32) }
}
fn wr32(a: u64, v: u32) {
    unsafe { core::ptr::write_volatile(a as *mut u32, v) }
}
fn rd64(a: u64) -> u64 {
    unsafe { core::ptr::read_volatile(a as *const u64) }
}
fn wr64(a: u64, v: u64) {
    unsafe { core::ptr::write_volatile(a as *mut u64, v) }
}

/// Write table base register `reg` with `v` (write-back, inner shareable;
/// its InnerCache field at `cache_shift`) and return what it reads back.
/// Where the GIC reads the shareability back as non-shareable it would
/// not snoop the caches, so the register is written again asking for
/// non-cacheable, non-shareable memory instead (IHI 0069, as Linux), the
/// other fields unchanged.
fn wr_base(reg: u64, v: u64, cache_shift: u64) -> u64 {
    wr64(reg, v);
    let got = rd64(reg);
    if got & SHARE_MASK != 0 {
        return got;
    }
    wr64(reg, (v & !(7 << cache_shift) & !SHARE_MASK) | CACHE_NC << cache_shift);
    rd64(reg)
}

/// Disable the ITS at `va`, keeping GITS_CTLR's other fields (GICv4.1's
/// ITS_Number, ImDe), and wait until it reports quiescent. Returns whether
/// it did.
fn disable_its(va: u64) -> bool {
    let ctlr = rd32(va + GITS_CTLR);
    wr32(va + GITS_CTLR, ctlr & !CTLR_ENABLED);
    let mut n = 0u64;
    while rd32(va + GITS_CTLR) & CTLR_QUIESCENT == 0 {
        n += 1;
        if n > 10_000_000 {
            return false;
        }
        core::hint::spin_loop();
    }
    true
}

/// What the root task learns (`SEL4_BOOTINFO_HEADER_AARCH64_MSI_INFO`).
#[derive(Clone, Copy, Debug)]
pub struct Info {
    pub doorbell: u64,
    pub num_lpis: u64,
    pub num_events: u64,
    pub num_devices: u64,
}

/// Whether the distributor has LPIs, with enough interrupt ID bits and
/// every LPI the kernel numbers (`gic_layout::lpi_supported`).
pub fn supported() -> bool {
    gl::lpi_supported(crate::gic::version() == 3, crate::gic::dist_typer(), LPI_ID_BITS, irq::NUM_LPIS)
}

/// Set up the ITS mapped at `va` (physically `pa`, `ITS_SIZE` bytes) with
/// `memory_size(ncpus)` bytes of RAM at the 64 KiB aligned `mem`, and LPIs
/// on the first `ncpus` cores (`gicr_pa`: a core's redistributor's
/// physical address; `gicr_regions`: every mapped redistributor range,
/// virtual address and length). After `smp::start_aps`.
///
/// First, reads only: every redistributor frame of every range (cores
/// not started included) must have LPIs off and no register write
/// pending, and each started core's must have LPIs. Then every table base
/// register is written and read back (address, size and, on the
/// redistributors, the same attributes on every core) before the ITS or
/// any core's LPIs are enabled, so an error there leaves them all off.
/// Past that, a command failure disables the ITS again (`command`); a
/// redistributor's EnableLPIs may not clear once set, so its tables stay
/// the kernel's and every LPI stays disabled in the configuration table.
pub fn init(
    va: u64,
    pa: u64,
    mem: u64,
    ncpus: usize,
    gicr_pa: impl Fn(usize) -> Option<u64>,
    gicr_regions: &[(u64, u64)],
    was_enabled: bool,
    trusted_cold_handoff: bool,
) -> Result<Info, InitError> {
    use InitError::{Unsafe, Unsupported};
    let s = its();
    if !supported() {
        return Err(Unsupported("the distributor has no LPIs, or too few"));
    }
    if mem % PAGE64K != 0 || ncpus > s.rdbase.len() {
        return Err(Unsupported("bad ITS memory"));
    }
    // Quiescent before the tables' memory is touched: an ITS still
    // translating with the firmware's tables could write there.
    if !disable_its(va) {
        return Err(Unsafe("the ITS does not quiesce"));
    }
    let mva = pptr(mem);
    unsafe {
        core::ptr::write_bytes(mva as *mut u8, 0, memory_size(ncpus) as usize);
        // Every LPI disabled, with the RES1 group bit.
        core::ptr::write_bytes((mva + PROP_OFF) as *mut u8, LPI_DISABLED, PROP_BYTES as usize);
    }
    cpu::clean_inval_dcache_poc(mva, memory_size(ncpus));
    cpu::dsb_sy();

    let typer = rd64(va + GITS_TYPER);
    if typer & 1 == 0 {
        return Err(Unsupported("the ITS has no physical LPIs"));
    }
    // A warm takeover (the firmware or an earlier kernel left the ITS set
    // up, `gic_layout::its_is_warm`, `was_enabled` as boot found it): its
    // caches may hold translations of the old tables. An ITS that
    // invalidates them when its tables are made invalid (GITS_TYPER.INV,
    // IHI 0069 12.19.13) is taken over with every table and the command
    // queue made invalid first. One without INV is taken over only cold,
    // and only when the boot path guarantees it comes from reset unused
    // (`trusted_cold_handoff`; `gic_layout::its_takeover_allowed`): its
    // registers alone cannot tell that from firmware that used it and
    // then cleared it.
    let mut basers = [0u64; 8];
    for (i, b) in basers.iter_mut().enumerate() {
        *b = rd64(va + GITS_BASER + i as u64 * 8);
    }
    let warm = gl::its_is_warm(was_enabled, rd64(va + GITS_CBASER), &basers);
    if !gl::its_takeover_allowed(typer & ITS_TYPER_INV != 0, warm, trusted_cold_handoff) {
        return Err(Unsupported(if warm {
            "warm ITS takeover without GITS_TYPER.INV"
        } else {
            "ITS without GITS_TYPER.INV on a boot path that does not reset it"
        }));
    }
    if warm {
        for i in 0..8u64 {
            let reg = va + GITS_BASER + i * 8;
            let v = rd64(reg);
            if v & BASER_VALID != 0 {
                wr64(reg, v & !BASER_VALID);
                if rd64(reg) & BASER_VALID != 0 {
                    return Err(Unsupported("ITS BASER did not clear Valid"));
                }
            }
        }
        let cb = rd64(va + GITS_CBASER);
        if cb & BASER_VALID != 0 {
            wr64(va + GITS_CBASER, cb & !BASER_VALID);
            if rd64(va + GITS_CBASER) & BASER_VALID != 0 {
                return Err(Unsupported("ITS CBASER did not clear Valid"));
            }
        }
        cpu::dsb_sy();
    }
    let itt_esz = ((typer >> 4) & 0xf) + 1;
    let event_bits = ((typer >> 8) & 0x1f) + 1;
    let dev_bits = ((typer >> 13) & 0x1f) + 1;
    let pta = typer & (1 << 19) != 0;
    let hcc = (typer >> 24) & 0xff;
    let cil = typer & (1 << 36) != 0;
    let cid_bits = if cil { ((typer >> 32) & 0xf) + 1 } else { 16 };
    // GICv4.1 SVPET (bits 41..42): the vPE table is shared with the
    // redistributors, which the kernel does not set up.
    let svpet = (typer >> 41) & 3;
    if event_bits < EVENT_BITS || (ncpus as u64) > (1 << cid_bits) {
        return Err(Unsupported("the ITS has too few event or collection IDs"));
    }
    let mut num_devices = DEVICE_IDS.min(1 << dev_bits.min(32));
    let itt_size = (EVENTS * itt_esz).next_multiple_of(256);
    if itt_size * MAX_DEVICES as u64 > PAGE64K {
        return Err(Unsupported("ITTs too large"));
    }

    // The device table (flat), a collection table unless the ITS holds
    // every core's collection itself, and an empty vPE table where the ITS
    // has one (GICv4: enabling the ITS with it invalid is UNPREDICTABLE).
    let mut has_dev = false;
    let mut has_coll = false;
    for i in 0..8u64 {
        let reg = va + GITS_BASER + i * 8;
        let v = rd64(reg);
        let ty = (v >> 56) & 7;
        let esz = ((v >> 48) & 0x1f) + 1;
        let off = match ty {
            BASER_TYPE_NONE => continue,
            BASER_TYPE_DEVICE => {
                num_devices = num_devices.min(PAGE64K / esz);
                DEV_OFF
            }
            BASER_TYPE_COLLECTION if hcc < ncpus as u64 => {
                if (ncpus as u64) * esz > PAGE64K {
                    return Err(Unsupported("collection table too large"));
                }
                COLL_OFF
            }
            BASER_TYPE_COLLECTION => {
                // Every collection the kernel maps (one per core) is held
                // in the ITS itself (HCC), so the table is not needed and
                // stays invalid (IHI 0069 5.2.1, as Linux does).
                wr64(reg, 0);
                continue;
            }
            BASER_TYPE_VPE if svpet != 0 => return Err(Unsupported("the ITS has a shared GICv4 vPE table")),
            BASER_TYPE_VPE => VPE_OFF,
            _ => return Err(Unsupported("unsupported ITS table type")),
        };
        let base = mem + off;
        let mut ok = false;
        // Page sizes 64, 16 and 4 KiB: the first the ITS keeps.
        for (psz_field, psz) in [(gl::BASER_PSZ_64K, PAGE64K), (gl::BASER_PSZ_16K, 0x4000), (gl::BASER_PSZ_4K, 0x1000)] {
            let pages = PAGE64K / psz;
            let want = BASER_VALID | CACHE_RAWAWB << ITS_CACHE_SHIFT | ty << 56 | base | SHARE_INNER << 10 | psz_field << 8 | (pages - 1);
            let got = wr_base(reg, want, ITS_CACHE_SHIFT);
            if (got >> 8) & 3 == psz_field {
                ok = gl::its_baser_ok(got, base, psz_field, pages);
                break;
            }
        }
        if !ok {
            return Err(Unsupported("the ITS refuses its table"));
        }
        match ty {
            BASER_TYPE_DEVICE => has_dev = true,
            BASER_TYPE_COLLECTION => has_coll = true,
            _ => {}
        }
    }
    if !has_dev {
        return Err(Unsupported("the ITS has no device table"));
    }
    // Collections the ITS does not hold go to memory: without a table for
    // them MAPC of the cores past `hcc` would be lost.
    if hcc < ncpus as u64 && !has_coll {
        return Err(Unsupported("the ITS has no collection table"));
    }

    // The command queue.
    let cb = wr_base(va + GITS_CBASER, BASER_VALID | CACHE_RAWAWB << ITS_CACHE_SHIFT | (mem + CMD_OFF) | SHARE_INNER << 10 | (CMD_BYTES / 0x1000 - 1), ITS_CACHE_SHIFT);
    wr64(va + GITS_CWRITER, 0);
    if !gl::its_cbaser_ok(cb, mem + CMD_OFF, CMD_BYTES / 0x1000) {
        return Err(Unsupported("the ITS refuses its command queue"));
    }

    // Reads only: every redistributor frame, then each started core's.
    // Boot turned LPIs off everywhere (`quiesce_redistributors`): one on
    // again, or a write that does not complete, is not safe to go on with.
    let mut bad = None;
    for &(base, len) in gicr_regions {
        let ok = gl::for_each_frame(base, len, crate::gic::gicr_stride(), |f| rd64(f + GICR_TYPER), |f, _| {
            if bad.is_none() {
                if rd32(f + GICR_CTLR) & 1 != 0 {
                    bad = Some("redistributor LPIs enabled");
                } else if !crate::gic::wait_gicr_rwp(f) {
                    bad = Some("redistributor RWP stuck");
                }
            }
        });
        if !ok {
            bad = bad.or(Some("bad redistributor stride"));
        }
    }
    if let Some(e) = bad {
        return Err(Unsafe(e));
    }
    for c in 0..ncpus {
        let r = crate::percpu::gicr(c);
        if r == 0 {
            return Err(Unsupported("a core has no redistributor"));
        }
        let rt = rd64(r + GICR_TYPER);
        if rt & 1 == 0 {
            return Err(Unsupported("a redistributor has no LPIs"));
        }
        if rd32(r + GICR_CTLR) & 1 != 0 {
            return Err(Unsafe("redistributor LPIs enabled"));
        }
        if !crate::gic::wait_gicr_rwp(r) {
            return Err(Unsafe("redistributor RWP stuck"));
        }
        s.rdbase[c] = if pta {
            match gicr_pa(c) {
                Some(p) => p >> 16,
                None => return Err(Unsupported("a redistributor's address is unknown")),
            }
        } else {
            (rt >> 8) & 0xffff
        };
    }
    // Every started core's redistributor given its tables (one
    // configuration table, a pending table each) before any is enabled.
    let mut attrs = None;
    for c in 0..ncpus {
        let r = crate::percpu::gicr(c);
        let prop = wr_base(r + GICR_PROPBASER, (mem + PROP_OFF) | CACHE_RAWAWB << GICR_CACHE_SHIFT | SHARE_INNER << 10 | (LPI_ID_BITS - 1), GICR_CACHE_SHIFT);
        let pend_pa = mem + PEND_OFF + c as u64 * PAGE64K;
        let pend = wr_base(r + GICR_PENDBASER, 1 << 62 | pend_pa | CACHE_RAWAWB << GICR_CACHE_SHIFT | SHARE_INNER << 10, GICR_CACHE_SHIFT);
        if !gl::propbaser_ok(prop, mem + PROP_OFF, LPI_ID_BITS) || !gl::pendbaser_ok(pend, pend_pa) {
            return Err(Unsupported("a redistributor refuses its LPI tables"));
        }
        let a = (gl::gicr_baser_attrs(prop), gl::gicr_baser_attrs(pend));
        if *attrs.get_or_insert(a) != a {
            return Err(Unsupported("redistributors differ in their LPI tables' attributes"));
        }
    }
    s.va = va;
    s.mem = mem;
    s.pta = pta;
    s.cwriter = 0;
    s.num_devices = num_devices;
    s.itt_size = itt_size;
    s.failed = false;
    s.quiesced = false;

    cpu::dsb_sy();
    for c in 0..ncpus {
        let r = crate::percpu::gicr(c);
        wr32(r + GICR_CTLR, rd32(r + GICR_CTLR) | 1);
    }
    cpu::dsb_sy();
    wr32(va + GITS_CTLR, rd32(va + GITS_CTLR) | CTLR_ENABLED);
    for c in 0..ncpus {
        // MAPC: collection c to core c.
        command(s, [0x09, 0, BASER_VALID | s.rdbase[c] << 16 | c as u64, 0]);
        command(s, [0x05, 0, s.rdbase[c] << 16, 0]);
    }
    if s.failed {
        // `command` has disabled the ITS; no LPI is enabled in the
        // configuration table.
        return Err(if s.quiesced { Unsupported("the ITS does not take commands") } else { Unsafe("the ITS does not take commands, nor quiesce") });
    }
    s.ncpus = ncpus;
    s.ready = true;
    Ok(Info {
        doorbell: pa + GITS_TRANSLATER,
        num_lpis: irq::NUM_LPIS,
        num_events: EVENTS,
        num_devices,
    })
}

/// Queue one command and wait until the ITS has done it. On an error or
/// a timeout no more commands are issued (`failed`, and `ready` false for
/// good) and the ITS is disabled at once, so it translates no more events
/// (`quiesced` when it says so).
fn command(s: &mut Its, cmd: [u64; 4]) {
    if s.failed {
        return;
    }
    let slot = pptr(s.mem + CMD_OFF) + s.cwriter * 32;
    for (i, w) in cmd.iter().enumerate() {
        wr64(slot + i as u64 * 8, *w);
    }
    cpu::clean_dcache_poc(slot, 32);
    cpu::dsb_sy();
    s.cwriter = (s.cwriter + 1) % CMD_SLOTS;
    wr64(s.va + GITS_CWRITER, s.cwriter * 32);
    let mut n = 0u64;
    loop {
        let r = rd64(s.va + GITS_CREADR);
        if r & 1 != 0 || n > 100_000_000 {
            // Stalled on an error, or never done.
            s.failed = true;
            s.ready = false;
            s.quiesced = disable_its(s.va);
            return;
        }
        if (r >> 5) & (CMD_SLOTS - 1) == s.cwriter {
            return;
        }
        n += 1;
        core::hint::spin_loop();
    }
}

fn set_prop(s: &Its, n: u64, v: u8) {
    let a = pptr(s.mem + PROP_OFF) + n;
    unsafe { core::ptr::write_volatile(a as *mut u8, v) };
    cpu::clean_dcache_poc(a, 1);
    cpu::dsb_sy();
}

/// Map event `event` of device `device` to LPI `irq` on core `core`
/// (`fl4_core::machine::msi` codes; nothing changes unless OK). `irq` has
/// no mapping (its handler does not exist).
pub fn map(irq_n: u64, device: u64, event: u64, core: u64) -> u64 {
    use fl4_core::machine::msi;
    let s = its();
    if !s.ready || !irq::is_lpi(irq_n) || irq_n > irq::MAX || core as usize >= s.ncpus || core as usize >= s.rdbase.len() {
        return msi::NO_ITS;
    }
    if device >= s.num_devices {
        return msi::BAD_DEVICE;
    }
    if event >= EVENTS {
        return msi::BAD_EVENT;
    }
    let n = irq_n - irq::LPI_BASE;
    let slot = match s.devices.iter().position(|d| d.events != 0 && d.id == device) {
        Some(i) => {
            if s.devices[i].events & (1 << event) != 0 {
                return msi::BAD_EVENT;
            }
            i
        }
        None => {
            let Some(i) = s.devices.iter().position(|d| d.events == 0) else {
                return msi::NO_ITS;
            };
            // MAPD: the device's ITT, zeroed and out of the caches (an
            // earlier device's ITT may have been here).
            let itt = s.mem + ITT_OFF + i as u64 * s.itt_size;
            unsafe { core::ptr::write_bytes(pptr(itt) as *mut u8, 0, s.itt_size as usize) };
            cpu::clean_inval_dcache_poc(pptr(itt), s.itt_size);
            cpu::dsb_sy();
            command(s, [0x08 | device << 32, EVENT_BITS - 1, BASER_VALID | itt, 0]);
            s.devices[i].id = device;
            i
        }
    };
    set_prop(s, n, LPI_ENABLED);
    let intid = irq::LPI_ID_BASE + n;
    // MAPTI, then INV (the configuration just written), then SYNC.
    command(s, [0x0a | device << 32, event | intid << 32, core, 0]);
    command(s, [0x0c | device << 32, event, 0, 0]);
    command(s, [0x05, 0, s.rdbase[core as usize] << 16, 0]);
    if s.failed {
        // The ITS takes no more commands, and `ready` is false for good,
        // so neither this LPI nor the device slot is mapped again. Where it
        // did not quiesce the event may still translate: the LPI is left
        // disabled in the configuration table.
        set_prop(s, n, LPI_DISABLED);
        return msi::NO_ITS;
    }
    s.devices[slot].events |= 1 << event;
    s.lpis[n as usize] = (slot as u8 + 1, event as u8, core as u8);
    msi::OK
}

/// Undo `map` for LPI `irq` (nothing if it has no mapping).
pub fn unmap(irq_n: u64) {
    let s = its();
    if !irq::is_lpi(irq_n) || irq_n > irq::MAX {
        return;
    }
    let n = (irq_n - irq::LPI_BASE) as usize;
    let (slot1, event, core) = s.lpis[n];
    if slot1 == 0 {
        return;
    }
    let slot = slot1 as usize - 1;
    let device = s.devices[slot].id;
    let event = event as u64;
    set_prop(s, n as u64, LPI_DISABLED);
    // INV while the event still translates to the LPI and its collection,
    // so the target redistributor drops its cached (enabled)
    // configuration; then DISCARD the event, and the device's ITT with its
    // last event; then SYNC the redistributor the LPI was routed to.
    command(s, [0x0c | device << 32, event, 0, 0]);
    command(s, [0x0f | device << 32, event, 0, 0]);
    let last = s.devices[slot].events & !(1 << event) == 0;
    if last {
        command(s, [0x08 | device << 32, 0, 0, 0]);
    }
    command(s, [0x05, 0, s.rdbase[core as usize] << 16, 0]);
    // Where the ITS failed without quiescing, the event may still translate
    // to the LPI: its mapping stays recorded (quarantined; no `map` runs
    // again anyway), the LPI disabled.
    if !s.failed || s.quiesced {
        s.lpis[n] = (0, 0, 0);
        s.devices[slot].events &= !(1 << event);
    }
}
