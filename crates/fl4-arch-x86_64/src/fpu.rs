//! FPU state switching. Each TCB holds an XSAVE image at
//! `layout::tcb::FPU`. The registers keep the state of the last thread
//! that ran with the FPU (the owner) until another such thread runs, so a
//! switch to and from the idle thread or an FPU-less thread costs nothing.
//! Threads with seL4_TCBFlag_fpuDisabled run with CR0.TS set and get #NM.
//!
//! On CPUs that LazyFP (CVE-2018-3665) does not affect, the switch is lazy
//! (DESIGN.md §3): a thread that does not own the registers runs with
//! CR0.TS set, and its first FPU instruction traps (#NM) to `lazy_load`,
//! which saves the owner's state and loads the thread's. A thread that
//! never touches the FPU between IPCs then costs no FPU work at all. On
//! Intel CPUs, where #NM-deferred state can leak through speculation, the
//! switch stays eager: the incoming thread's state is loaded on the way
//! out of the kernel, whether it uses the FPU or not.
//!
//! The save instruction is the best the CPU has (DESIGN.md §3): XSAVES,
//! XSAVEC, XSAVEOPT, XSAVE, then FXSAVE. The first two write the compacted
//! format; an image leaves the FPU code (`flush`, for TCB_ReadFPU and
//! migration) in the standard format, and restore takes either.
use crate::cpu::{cpuid, msr, read_cr0, read_cr4, wrmsr, write_cr0, write_cr4, xsetbv};
use crate::percpu;
use core::arch::asm;
use core::sync::atomic::{AtomicBool, AtomicU32, AtomicU64, AtomicU8, Ordering};
use fl4_core::layout::tcb;

static XSAVE: AtomicBool = AtomicBool::new(false);
static LAZY: AtomicBool = AtomicBool::new(false);
static XCR0: AtomicU64 = AtomicU64::new(0);
static MXCSR_MASK: AtomicU64 = AtomicU64::new(0xffbf);
static INSN: AtomicU8 = AtomicU8::new(Insn::Fxsave as u8);
/// Per state component: standard-format offset and size, and whether the
/// compacted format aligns it to 64 bytes (CPUID 0DH sub-leaf i).
static STD_OFF: [AtomicU32; 64] = [const { AtomicU32::new(0) }; 64];
static SIZE: [AtomicU32; 64] = [const { AtomicU32::new(0) }; 64];
static ALIGN: AtomicU64 = AtomicU64::new(0);

#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
enum Insn {
    Fxsave = 0,
    Xsave = 1,
    Xsaveopt = 2,
    Xsavec = 3,
    Xsaves = 4,
}

fn insn() -> Insn {
    match INSN.load(Ordering::Relaxed) {
        1 => Insn::Xsave,
        2 => Insn::Xsaveopt,
        3 => Insn::Xsavec,
        4 => Insn::Xsaves,
        _ => Insn::Fxsave,
    }
}

/// AMX tile configuration and data (17, 18): left off, the data alone is
/// 8 KiB. They are enabled together or not at all.
const AMX: u64 = (1 << 17) | (1 << 18);
/// AVX-512 (opmask, ZMM_Hi256, Hi16_ZMM): together, and only with AVX.
const AVX512: u64 = 0xe0;
const AVX: u64 = 1 << 2;
/// MPX (BNDREGS, BNDCSR): together.
const MPX: u64 = 0x18;

const CR0_MP: u64 = 1 << 1;
const CR0_EM: u64 = 1 << 2;
const CR0_TS: u64 = 1 << 3;
const CR0_NE: u64 = 1 << 5;
const CR4_OSFXSR: u64 = 1 << 9;
const CR4_OSXMMEXCPT: u64 = 1 << 10;
const CR4_OSXSAVE: u64 = 1 << 18;

/// XSAVE header: XSTATE_BV, XCOMP_BV (bit 63: compacted).
const HDR: u64 = 512;
const COMPACTED: u64 = 1 << 63;

#[repr(C, align(64))]
struct Scratch([u8; 512]);

/// The user state components to enable: every one the CPU has except AMX,
/// dropping the largest groups until the image fits the TCB.
fn components() -> u64 {
    let sup = cpuid(0xd, 0);
    let mut x = (sup.eax as u64 | ((sup.edx as u64) << 32)) & !AMX;
    if x & AVX512 != AVX512 || x & AVX == 0 {
        x &= !AVX512;
    }
    if x & MPX != MPX {
        x &= !MPX;
    }
    for drop in [AVX512, MPX, 1 << 19] {
        xsetbv(0, x);
        if cpuid(0xd, 0).ebx as u64 <= tcb::FPU_SIZE {
            break;
        }
        x &= !drop;
    }
    x
}

/// Enable the FPU on this core and pick the state components and the save
/// instruction (the same on every core).
pub fn init() {
    write_cr0((read_cr0() & !(CR0_EM | CR0_TS)) | CR0_MP | CR0_NE);
    let mut cr4 = read_cr4() | CR4_OSFXSR | CR4_OSXMMEXCPT;
    let has_xsave = cpuid(1, 0).ecx & (1 << 26) != 0;
    if has_xsave {
        cr4 |= CR4_OSXSAVE;
    }
    write_cr4(cr4);
    if has_xsave {
        let x = components();
        xsetbv(0, x);
        XCR0.store(x, Ordering::Relaxed);
        XSAVE.store(true, Ordering::Relaxed);
        let mut align = 0u64;
        for i in 2..63 {
            if x & (1 << i) != 0 {
                let l = cpuid(0xd, i);
                SIZE[i as usize].store(l.eax, Ordering::Relaxed);
                STD_OFF[i as usize].store(l.ebx, Ordering::Relaxed);
                if l.ecx & 2 != 0 {
                    align |= 1 << i;
                }
            }
        }
        ALIGN.store(align, Ordering::Relaxed);
        let ext = cpuid(0xd, 1).eax;
        let i = if ext & (1 << 3) != 0 {
            // XSAVES saves supervisor state too; FL4 enables none.
            wrmsr(msr::XSS, 0);
            Insn::Xsaves
        } else if ext & (1 << 1) != 0 {
            Insn::Xsavec
        } else if ext & 1 != 0 {
            Insn::Xsaveopt
        } else {
            Insn::Xsave
        };
        INSN.store(i as u8, Ordering::Relaxed);
    }
    // LazyFP is an Intel erratum; AMD (and Hygon) are not affected.
    let v = cpuid(0, 0);
    let intel = v.ebx == 0x756e_6547 && v.edx == 0x4965_6e69 && v.ecx == 0x6c65_746e;
    LAZY.store(!intel, Ordering::Relaxed);
    unsafe { asm!("fninit", options(nomem, nostack)) };
    let mut f = Scratch([0; 512]);
    unsafe { asm!("fxsave64 [{}]", in(reg) f.0.as_mut_ptr(), options(nostack)) };
    let m = u32::from_le_bytes([f.0[28], f.0[29], f.0[30], f.0[31]]) as u64;
    MXCSR_MASK.store(if m == 0 { 0xffbf } else { m }, Ordering::Relaxed);
}

pub fn xcr0() -> u64 {
    XCR0.load(Ordering::Relaxed)
}

/// The save instruction, for the boot banner.
pub fn save_insn() -> &'static str {
    match insn() {
        Insn::Fxsave => "fxsave",
        Insn::Xsave => "xsave",
        Insn::Xsaveopt => "xsaveopt",
        Insn::Xsavec => "xsavec",
        Insn::Xsaves => "xsaves",
    }
}

/// FPU switching is lazy on this CPU.
pub fn lazy() -> bool {
    LAZY.load(Ordering::Relaxed)
}

/// Saves write the compacted format.
pub fn compacting() -> bool {
    matches!(insn(), Insn::Xsavec | Insn::Xsaves)
}

fn image(t: u64) -> *mut u8 {
    (t + tcb::FPU) as *mut u8
}

fn rd(p: *mut u8, off: u64) -> u64 {
    unsafe { core::ptr::read_volatile(p.add(off as usize) as *const u64) }
}

fn wr(p: *mut u8, off: u64, v: u64) {
    unsafe { core::ptr::write_volatile(p.add(off as usize) as *mut u64, v) }
}

/// Offsets of the components `comp` names in the compacted format.
fn compacted_offsets(comp: u64, out: &mut [u64; 64]) {
    let align = ALIGN.load(Ordering::Relaxed);
    let mut off = HDR + 64;
    for i in 2..63 {
        if comp & (1 << i) == 0 {
            continue;
        }
        if align & (1 << i) != 0 {
            off = (off + 63) & !63;
        }
        out[i] = off;
        off += SIZE[i].load(Ordering::Relaxed) as u64;
    }
}

/// Rewrite `t`'s compacted image in the standard format. Standard
/// offsets are never below compacted ones, so components move up, the
/// last first. Components in their initial state are zeroed.
fn to_standard(t: u64) {
    let p = image(t);
    let comp = rd(p, HDR + 8);
    if comp & COMPACTED == 0 {
        return;
    }
    let bv = rd(p, HDR);
    let mut coff = [0u64; 64];
    compacted_offsets(comp, &mut coff);
    for i in (2..63).rev() {
        if comp & (1 << i) == 0 {
            continue;
        }
        let size = SIZE[i].load(Ordering::Relaxed) as usize;
        let dst = STD_OFF[i].load(Ordering::Relaxed) as usize;
        unsafe {
            if bv & (1 << i) != 0 {
                core::ptr::copy(p.add(coff[i] as usize), p.add(dst), size);
            } else {
                core::ptr::write_bytes(p.add(dst), 0, size);
            }
        }
    }
    wr(p, HDR + 8, 0);
}

/// Rewrite `t`'s standard image in the compacted format XRSTORS needs:
/// components move down, the first first.
fn to_compacted(t: u64) {
    let p = image(t);
    if rd(p, HDR + 8) & COMPACTED != 0 {
        return;
    }
    let comp = XCR0.load(Ordering::Relaxed) & !COMPACTED;
    let mut coff = [0u64; 64];
    compacted_offsets(comp, &mut coff);
    for i in 2..63 {
        if comp & (1 << i) == 0 {
            continue;
        }
        let size = SIZE[i].load(Ordering::Relaxed) as usize;
        let src = STD_OFF[i].load(Ordering::Relaxed) as usize;
        unsafe { core::ptr::copy(p.add(src), p.add(coff[i] as usize), size) };
    }
    wr(p, HDR + 8, comp | COMPACTED);
}

fn save(t: u64) {
    let p = image(t);
    unsafe {
        match insn() {
            Insn::Xsaves => asm!("xsaves64 [{}]", in(reg) p, in("eax") u32::MAX, in("edx") u32::MAX, options(nostack)),
            Insn::Xsavec => asm!("xsavec64 [{}]", in(reg) p, in("eax") u32::MAX, in("edx") u32::MAX, options(nostack)),
            Insn::Xsaveopt => asm!("xsaveopt64 [{}]", in(reg) p, in("eax") u32::MAX, in("edx") u32::MAX, options(nostack)),
            Insn::Xsave => asm!("xsave64 [{}]", in(reg) p, in("eax") u32::MAX, in("edx") u32::MAX, options(nostack)),
            Insn::Fxsave => asm!("fxsave64 [{}]", in(reg) p, options(nostack)),
        }
    }
}

fn restore(t: u64) {
    let p = image(t);
    unsafe {
        match insn() {
            Insn::Xsaves => {
                to_compacted(t);
                asm!("xrstors64 [{}]", in(reg) p, in("eax") u32::MAX, in("edx") u32::MAX, options(nostack))
            }
            Insn::Fxsave => asm!("fxrstor64 [{}]", in(reg) p, options(nostack)),
            // XRSTOR takes both formats.
            _ => asm!("xrstor64 [{}]", in(reg) p, in("eax") u32::MAX, in("edx") u32::MAX, options(nostack)),
        }
    }
}

fn set_ts(on: bool) {
    let pc = percpu::get();
    if pc.ts_set != on {
        let c = read_cr0();
        write_cr0(if on { c | CR0_TS } else { c & !CR0_TS });
        pc.ts_set = on;
    }
}

/// Exit path: make the FPU right for thread `t`.
pub fn switch_to(t: u64, fpu_disabled: bool) {
    if fpu_disabled {
        set_ts(true);
        return;
    }
    let pc = percpu::get();
    if pc.fpu_owner == t {
        set_ts(false);
        return;
    }
    if lazy() {
        // The swap waits for the thread's first FPU instruction.
        set_ts(true);
        return;
    }
    set_ts(false);
    load(t);
}

/// Save the owner's state, if any, and load `t`'s.
fn load(t: u64) {
    let pc = percpu::get();
    if pc.fpu_owner != 0 {
        save(pc.fpu_owner);
    }
    restore(t);
    percpu::get().fpu_owner = t;
}

/// #NM from thread `t` on the lazy path: give it the FPU. Runs in the
/// entry glue with interrupts off, so no remote FPU call (`flush`,
/// `forget`) for this core can run in between.
pub fn lazy_load(t: u64) {
    set_ts(false);
    if percpu::get().fpu_owner != t {
        load(t);
    }
}

/// Write `t`'s state back to its TCB if it is live on this core.
pub fn flush_local(t: u64) {
    if percpu::get().fpu_owner == t {
        set_ts(false);
        save(t);
    }
}

/// Forget `t`'s state if it is live on this core.
pub fn forget_local(t: u64) {
    let pc = percpu::get();
    if pc.fpu_owner == t {
        pc.fpu_owner = 0;
    }
}

/// The core whose registers hold `t`'s FPU state, if any.
fn owner_core(t: u64) -> Option<usize> {
    (0..percpu::MAX_CPUS).find(|&c| unsafe { core::ptr::read_volatile(&percpu::get_for(c).fpu_owner) } == t)
}

/// Whether some core's registers hold `t`'s FPU state.
pub fn is_live(t: u64) -> bool {
    owner_core(t).is_some()
}

/// Write `t`'s live state, wherever it is, back to its TCB, in the
/// standard format. The caller holds the serial gate when another core may
/// hold the state.
pub fn flush(t: u64) {
    match owner_core(t) {
        Some(c) if c == percpu::cpu_index() => flush_local(t),
        Some(c) => crate::smp::remote_call(crate::smp::CALL_FPU_SAVE, t, 0, 1 << c),
        None => {}
    }
    if XSAVE.load(Ordering::Relaxed) {
        to_standard(t);
    }
}

/// `t`'s state is no longer (or no longer only) in some core's registers.
pub fn forget(t: u64) {
    match owner_core(t) {
        Some(c) if c == percpu::cpu_index() => forget_local(t),
        Some(c) => crate::smp::remote_call(crate::smp::CALL_FPU_DROP, t, 0, 1 << c),
        None => {}
    }
}

/// Make a user-written image safe for XRSTOR/FXRSTOR (l4h 0002).
pub fn sanitise(t: u64) {
    let f = t + tcb::FPU;
    unsafe {
        // MXCSR at byte 24 (low half of the word).
        let w = (f + 24) as *mut u64;
        let v = core::ptr::read_volatile(w);
        let mx = (v as u32 as u64) & MXCSR_MASK.load(Ordering::Relaxed);
        core::ptr::write_volatile(w, (v & !0xffff_ffff) | mx);
        if XSAVE.load(Ordering::Relaxed) {
            // XSAVE header at 512: XSTATE_BV, XCOMP_BV, then reserved.
            let h = (f + 512) as *mut u64;
            let bv = core::ptr::read_volatile(h) & XCR0.load(Ordering::Relaxed);
            core::ptr::write_volatile(h, bv);
            let mut i = 1;
            while i < 8 {
                core::ptr::write_volatile(h.add(i), 0);
                i += 1;
            }
        }
    }
}
