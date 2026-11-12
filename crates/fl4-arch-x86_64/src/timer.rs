//! The kernel timer: the TSC as the clock, and the local APIC timer in
//! TSC-deadline mode when the CPU has it, one-shot mode otherwise
//! (detected at boot, DESIGN.md §3). Both are calibrated against the PIT.
use crate::apic;
use crate::cpu::{cpuid, rdtsc, wrmsr, msr};
use crate::pit;
use core::sync::atomic::{AtomicBool, AtomicU64, Ordering};

static TSC_MHZ: AtomicU64 = AtomicU64::new(1000);
static DEADLINE: AtomicBool = AtomicBool::new(false);
/// APIC timer ticks per TSC tick, as a 32.32 fixed-point number.
static APIC_RATIO: AtomicU64 = AtomicU64::new(1 << 32);

pub const KERNEL_WCET_US: u64 = 10;
const LVT_TSC_DEADLINE: u32 = 2 << 17;
/// 50 ms of PIT ticks.
const CALIBRATE_TICKS: u16 = (pit::HZ / 20) as u16;
const CALIBRATE_US: u64 = 50_000;

pub fn has_tsc_deadline() -> bool {
    cpuid(1, 0).ecx & (1 << 24) != 0
}

/// Calibrate and arm the timer on the boot core, delivering `vector`.
pub fn init(vector: u32) {
    let deadline = has_tsc_deadline();
    DEADLINE.store(deadline, Ordering::Relaxed);
    apic::write(apic::REG_LVT_TIMER, 1 << 16);
    apic::write(apic::REG_TIMER_DIV, 0xb);
    apic::write(apic::REG_TIMER_INIT, u32::MAX);
    let t0 = rdtsc();
    pit::wait(CALIBRATE_TICKS, || {});
    let t1 = rdtsc();
    let apic_ticks = (u32::MAX - apic::read(apic::REG_TIMER_CUR)) as u64;
    apic::write(apic::REG_TIMER_INIT, 0);
    let tsc = t1 - t0;
    let mhz = tsc / CALIBRATE_US;
    TSC_MHZ.store(if mhz == 0 { 1 } else { mhz }, Ordering::Relaxed);
    APIC_RATIO.store(((apic_ticks as u128) << 32).checked_div(tsc as u128).unwrap_or(1 << 32) as u64, Ordering::Relaxed);
    init_core(vector);
}

/// Program this core's LVT timer entry.
pub fn init_core(vector: u32) {
    if DEADLINE.load(Ordering::Relaxed) {
        apic::write(apic::REG_LVT_TIMER, vector | LVT_TSC_DEADLINE);
    } else {
        apic::write(apic::REG_TIMER_DIV, 0xb);
        apic::write(apic::REG_LVT_TIMER, vector);
    }
}

pub fn tsc_mhz() -> u64 {
    TSC_MHZ.load(Ordering::Relaxed)
}

pub fn deadline_mode() -> bool {
    DEADLINE.load(Ordering::Relaxed)
}

pub fn now() -> u64 {
    rdtsc()
}

/// Interrupt at TSC value `ticks` (or as soon as possible if it passed).
pub fn set_deadline(ticks: u64) {
    crate::percpu::get().armed = ticks;
    if DEADLINE.load(Ordering::Relaxed) {
        wrmsr(msr::TSC_DEADLINE, if ticks == 0 { 1 } else { ticks });
    } else {
        arm_countdown(ticks);
    }
}

/// APIC countdown mode (l4h 0014): convert with both rates, rounding up so
/// the count never runs out before the deadline. A delay longer than the
/// 32-bit count expires early and is re-armed by `early`.
fn arm_countdown(ticks: u64) {
    let delta = ticks.saturating_sub(rdtsc());
    let r = APIC_RATIO.load(Ordering::Relaxed) as u128;
    let a = ((delta as u128 * r + (1 << 32) - 1) >> 32) as u64;
    apic::write(apic::REG_TIMER_INIT, a.clamp(1, u32::MAX as u64) as u32);
}

/// A timer interrupt arrived: is it before the armed deadline (l4h 0012)?
/// Then it belongs to a deadline since replaced (TSC-deadline mode, where
/// the new deadline is already armed) or to a countdown that ran out of
/// count (re-armed here), and the kernel need not run. The time is checked
/// first, so a due interrupt costs no extra work.
pub fn early() -> bool {
    let armed = crate::percpu::get().armed;
    if armed == 0 || rdtsc() >= armed {
        return false;
    }
    if !DEADLINE.load(Ordering::Relaxed) {
        arm_countdown(armed);
    }
    true
}

pub fn us_to_ticks(us: u64) -> u64 {
    us.saturating_mul(tsc_mhz())
}

pub fn ticks_to_us(ticks: u64) -> u64 {
    ticks / tsc_mhz()
}

pub fn max_us() -> u64 {
    u64::MAX / tsc_mhz()
}
