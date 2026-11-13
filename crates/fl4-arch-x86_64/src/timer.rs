//! The kernel timer: the TSC as the clock, and the local APIC timer in
//! TSC-deadline mode when the CPU has it, one-shot mode otherwise
//! (detected at boot, DESIGN.md §3).
//!
//! The TSC rate comes, in order, from CPUID 15H/16H on Intel, from the
//! hypervisor's TSC leaf (40000010H, which KVM fills in), and from the PIT
//! as the median of five measurements. It is measured once, on the boot
//! core. The APIC timer's rate, needed only in one-shot mode, is measured
//! against the TSC.
use crate::apic;
use crate::cpu::{cpuid, rdtsc, wrmsr, msr};
use crate::pit;
use core::sync::atomic::{AtomicBool, AtomicU64, AtomicU8, Ordering};

static TSC_MHZ: AtomicU64 = AtomicU64::new(1000);
static DEADLINE: AtomicBool = AtomicBool::new(false);
/// APIC timer ticks per TSC tick, as a 32.32 fixed-point number.
static APIC_RATIO: AtomicU64 = AtomicU64::new(1 << 32);
/// Where the TSC rate came from (`Source`).
static SOURCE: AtomicU8 = AtomicU8::new(0);

pub const KERNEL_WCET_US: u64 = 10;
const LVT_TSC_DEADLINE: u32 = 2 << 17;
/// 20 ms of PIT ticks, per measurement.
const CALIBRATE_TICKS: u16 = (pit::HZ / 50) as u16;
const CALIBRATE_US: u64 = 20_000;
const RUNS: usize = 5;

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Source {
    Cpuid = 1,
    Hypervisor = 2,
    Pit = 3,
}

pub fn has_tsc_deadline() -> bool {
    cpuid(1, 0).ecx & (1 << 24) != 0
}

fn is_intel() -> bool {
    let v = cpuid(0, 0);
    // "GenuineIntel" in EBX, EDX, ECX.
    v.ebx == 0x756e_6547 && v.edx == 0x4965_6e69 && v.ecx == 0x6c65_746e
}

/// The TSC rate in kHz that the CPU reports (Intel CPUID 15H, or 16H's
/// base frequency when the crystal rate is not given).
fn cpuid_tsc_khz() -> Option<u64> {
    if !is_intel() {
        return None;
    }
    let max = cpuid(0, 0).eax;
    if max >= 0x15 {
        let l = cpuid(0x15, 0);
        if l.eax != 0 && l.ebx != 0 && l.ecx != 0 {
            return Some(l.ecx as u64 * l.ebx as u64 / l.eax as u64 / 1000);
        }
    }
    if max >= 0x16 {
        let base_mhz = cpuid(0x16, 0).eax & 0xffff;
        if base_mhz != 0 {
            return Some(base_mhz as u64 * 1000);
        }
    }
    None
}

/// The TSC rate in kHz a hypervisor reports in leaf 40000010H.
fn hypervisor_tsc_khz() -> Option<u64> {
    if cpuid(1, 0).ecx & (1 << 31) == 0 {
        return None;
    }
    if cpuid(0x4000_0000, 0).eax < 0x4000_0010 {
        return None;
    }
    let khz = cpuid(0x4000_0010, 0).eax;
    if khz == 0 {
        None
    } else {
        Some(khz as u64)
    }
}

/// TSC ticks in 20 ms of PIT time: the median of five measurements.
fn pit_tsc_per_run() -> u64 {
    let mut runs = [0u64; RUNS];
    for r in runs.iter_mut() {
        let t0 = rdtsc();
        pit::wait(CALIBRATE_TICKS, || {});
        *r = rdtsc() - t0;
    }
    runs.sort_unstable();
    runs[RUNS / 2]
}

/// Calibrate and arm the timer on the boot core, delivering `vector`.
pub fn init(vector: u32) {
    pit::quiet_channel0();
    let deadline = has_tsc_deadline();
    DEADLINE.store(deadline, Ordering::Relaxed);
    let (khz, src) = match cpuid_tsc_khz() {
        Some(k) => (k, Source::Cpuid),
        None => match hypervisor_tsc_khz() {
            Some(k) => (k, Source::Hypervisor),
            None => (pit_tsc_per_run() / (CALIBRATE_US / 1000), Source::Pit),
        },
    };
    let mhz = (khz + 500) / 1000;
    TSC_MHZ.store(if mhz == 0 { 1 } else { mhz }, Ordering::Relaxed);
    SOURCE.store(src as u8, Ordering::Relaxed);
    if !deadline {
        calibrate_apic();
    }
    init_core(vector);
}

/// APIC timer ticks per TSC tick, measured over 20 ms of TSC time.
fn calibrate_apic() {
    apic::write(apic::REG_LVT_TIMER, 1 << 16);
    apic::write(apic::REG_TIMER_DIV, 0xb);
    let tsc = us_to_ticks(CALIBRATE_US);
    apic::write(apic::REG_TIMER_INIT, u32::MAX);
    let t0 = rdtsc();
    while rdtsc() - t0 < tsc {
        core::hint::spin_loop();
    }
    let apic_ticks = (u32::MAX - apic::read(apic::REG_TIMER_CUR)) as u64;
    apic::write(apic::REG_TIMER_INIT, 0);
    APIC_RATIO.store(((apic_ticks as u128) << 32).checked_div(tsc as u128).unwrap_or(1 << 32) as u64, Ordering::Relaxed);
}

/// Where the TSC rate came from, for the boot banner.
pub fn source() -> &'static str {
    match SOURCE.load(Ordering::Relaxed) {
        1 => "CPUID",
        2 => "hypervisor",
        _ => "PIT",
    }
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

/// A timer interrupt arrived: is it stale (l4h 0012)? It is if the timer
/// is still armed for a later deadline: in TSC-deadline mode the
/// interrupt then belongs to a deadline since replaced; in countdown mode
/// the count ran out early (re-armed here). The kernel need not run then.
/// The time is checked first, so a due interrupt costs no MSR read. An
/// interrupt the hardware (or a hypervisor) delivers a little before the
/// deadline finds the deadline MSR cleared: it is due, not stale.
pub fn early() -> bool {
    let armed = crate::percpu::get().armed;
    if armed == 0 || rdtsc() >= armed {
        return false;
    }
    if DEADLINE.load(Ordering::Relaxed) {
        return crate::cpu::rdmsr(msr::TSC_DEADLINE) != 0;
    }
    arm_countdown(armed);
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
