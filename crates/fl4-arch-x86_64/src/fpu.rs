//! FPU state switching. Each TCB holds an XSAVE image (standard format)
//! at `layout::tcb::FPU`. The registers keep the state of the last thread
//! that ran with the FPU (the owner) until another such thread runs, so a
//! switch to and from the idle thread or an FPU-less thread costs nothing.
//! Threads with seL4_TCBFlag_fpuDisabled run with CR0.TS set and get #NM.
use crate::cpu::{cpuid, read_cr0, read_cr4, write_cr0, write_cr4, xsetbv};
use crate::percpu;
use core::arch::asm;
use core::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use fl4_core::layout::tcb;

static XSAVE: AtomicBool = AtomicBool::new(false);
static XCR0: AtomicU64 = AtomicU64::new(0);
static MXCSR_MASK: AtomicU64 = AtomicU64::new(0xffbf);

/// x87, SSE, AVX, AVX-512 (opmask, ZMM_Hi256, Hi16_ZMM) and PKRU: the
/// feature set the 4 KiB TCB is sized for (FPU_STATE_SIZE 2696).
const WANTED: u64 = 0x2e7;

const CR0_MP: u64 = 1 << 1;
const CR0_EM: u64 = 1 << 2;
const CR0_TS: u64 = 1 << 3;
const CR0_NE: u64 = 1 << 5;
const CR4_OSFXSR: u64 = 1 << 9;
const CR4_OSXMMEXCPT: u64 = 1 << 10;
const CR4_OSXSAVE: u64 = 1 << 18;

#[repr(C, align(64))]
struct Scratch([u8; 512]);

/// Enable the FPU on this core and pick the state components.
pub fn init() {
    write_cr0((read_cr0() & !(CR0_EM | CR0_TS)) | CR0_MP | CR0_NE);
    let mut cr4 = read_cr4() | CR4_OSFXSR | CR4_OSXMMEXCPT;
    let has_xsave = cpuid(1, 0).ecx & (1 << 26) != 0;
    if has_xsave {
        cr4 |= CR4_OSXSAVE;
    }
    write_cr4(cr4);
    if has_xsave {
        let sup = cpuid(0xd, 0);
        let supported = sup.eax as u64 | ((sup.edx as u64) << 32);
        let mut x = WANTED & supported;
        if x & 0xe0 != 0xe0 || x & 4 == 0 {
            x &= !0xe0;
        }
        xsetbv(0, x);
        if cpuid(0xd, 0).ebx as u64 > tcb::FPU_SIZE {
            x &= !0x2e0;
            xsetbv(0, x);
        }
        XCR0.store(x, Ordering::Relaxed);
        XSAVE.store(true, Ordering::Relaxed);
    }
    unsafe { asm!("fninit", options(nomem, nostack)) };
    let mut f = Scratch([0; 512]);
    unsafe { asm!("fxsave64 [{}]", in(reg) f.0.as_mut_ptr(), options(nostack)) };
    let m = u32::from_le_bytes([f.0[28], f.0[29], f.0[30], f.0[31]]) as u64;
    MXCSR_MASK.store(if m == 0 { 0xffbf } else { m }, Ordering::Relaxed);
}

pub fn xcr0() -> u64 {
    XCR0.load(Ordering::Relaxed)
}

fn save(t: u64) {
    let p = (t + tcb::FPU) as *mut u8;
    unsafe {
        if XSAVE.load(Ordering::Relaxed) {
            asm!("xsave64 [{}]", in(reg) p, in("eax") u32::MAX, in("edx") u32::MAX, options(nostack));
        } else {
            asm!("fxsave64 [{}]", in(reg) p, options(nostack));
        }
    }
}

fn restore(t: u64) {
    let p = (t + tcb::FPU) as *const u8;
    unsafe {
        if XSAVE.load(Ordering::Relaxed) {
            asm!("xrstor64 [{}]", in(reg) p, in("eax") u32::MAX, in("edx") u32::MAX, options(nostack));
        } else {
            asm!("fxrstor64 [{}]", in(reg) p, options(nostack));
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
    set_ts(false);
    let pc = percpu::get();
    if pc.fpu_owner != t {
        if pc.fpu_owner != 0 {
            save(pc.fpu_owner);
        }
        restore(t);
        percpu::get().fpu_owner = t;
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

/// Write `t`'s live state, wherever it is, back to its TCB. The caller
/// holds the serial gate when another core may hold the state.
pub fn flush(t: u64) {
    match owner_core(t) {
        Some(c) if c == percpu::cpu_index() => flush_local(t),
        Some(c) => crate::smp::remote_call(crate::smp::CALL_FPU_SAVE, t, 0, 1 << c),
        None => {}
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
