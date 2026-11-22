//! The kernel timer: the TSC as the clock, and the local APIC timer in
//! TSC-deadline mode when the CPU has it, one-shot mode otherwise
//! (detected at boot, DESIGN.md §3).
//!
//! Under KVM the TSC rate comes from pvclock; other hypervisors may expose
//! a TSC frequency leaf. Native Intel CPUs use CPUID 15H/16H. The fallback
//! is the PIT, as the median of five measurements. Calibration runs once
//! on the boot core. The APIC timer's rate, needed only in one-shot mode,
//! is measured against the TSC.
use crate::apic;
use crate::cpu::{cpuid, rdtsc, wrmsr, msr, Cpuid};
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Source {
    Cpuid = 1,
    Hypervisor = 2,
    Pit = 3,
    Kvm = 4,
}

pub fn has_tsc_deadline() -> bool {
    cpuid(1, 0).ecx & (1 << 24) != 0
}

fn is_intel(read: impl Fn(u32, u32) -> Cpuid) -> bool {
    let v = read(0, 0);
    // "GenuineIntel" in EBX, EDX, ECX.
    v.ebx == 0x756e_6547 && v.edx == 0x4965_6e69 && v.ecx == 0x6c65_746e
}

/// The TSC rate in kHz that the CPU reports (Intel CPUID 15H, or 16H's
/// base frequency when the crystal rate is not given).
fn cpuid_tsc_khz(read: impl Fn(u32, u32) -> Cpuid) -> Option<u64> {
    if !is_intel(&read) {
        return None;
    }
    let max = read(0, 0).eax;
    if max >= 0x15 {
        let l = read(0x15, 0);
        if l.eax != 0 && l.ebx != 0 && l.ecx != 0 {
            return Some(l.ecx as u64 * l.ebx as u64 / l.eax as u64 / 1000);
        }
    }
    if max >= 0x16 {
        let base_mhz = read(0x16, 0).eax & 0xffff;
        if base_mhz != 0 {
            return Some(base_mhz as u64 * 1000);
        }
    }
    None
}

/// The TSC rate in kHz a hypervisor reports in leaf 40000010H.
fn hypervisor_tsc_khz(read: impl Fn(u32, u32) -> Cpuid) -> Option<u64> {
    if read(1, 0).ecx & (1 << 31) == 0 {
        return None;
    }
    if read(0x4000_0000, 0).eax < 0x4000_0010 {
        return None;
    }
    let khz = read(0x4000_0010, 0).eax;
    if khz == 0 {
        None
    } else {
        Some(khz as u64)
    }
}

fn reported_tsc_khz(
    read: impl Fn(u32, u32) -> Cpuid,
    kvm: impl FnOnce() -> Option<u64>,
) -> Option<(u64, Source)> {
    if read(1, 0).ecx & (1 << 31) != 0 {
        // A VM's native CPUID leaves can describe the physical host,
        // not its scaled virtual TSC (GCE C3: 1.9 GHz vs 2.7 GHz).
        kvm().map(|k| (k, Source::Kvm))
            .or_else(|| hypervisor_tsc_khz(read).map(|k| (k, Source::Hypervisor)))
    } else {
        cpuid_tsc_khz(read).map(|k| (k, Source::Cpuid))
    }
}

/// A TDX guest's TSC rate: CPUID 15H, which the TDX module fixes, and
/// nothing the VMM controls (leaf 40000010H, the PIT).
fn tdx_tsc_khz(read: impl Fn(u32, u32) -> Cpuid) -> Option<u64> {
    if !is_intel(&read) || read(0, 0).eax < 0x15 {
        return None;
    }
    let l = read(0x15, 0);
    if l.eax == 0 || l.ebx == 0 || l.ecx == 0 {
        return None;
    }
    Some(l.ecx as u64 * l.ebx as u64 / l.eax as u64 / 1000)
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
    let tdx = crate::tdx::active();
    if !tdx {
        pit::quiet_channel0();
    }
    let deadline = has_tsc_deadline();
    DEADLINE.store(deadline, Ordering::Relaxed);
    let (khz, src) = if tdx {
        // The VMM must not be able to change how the guest measures time.
        match tdx_tsc_khz(cpuid) {
            Some(k) => (k, Source::Cpuid),
            None => crate::tdx::terminate(9),
        }
    } else {
        reported_tsc_khz(cpuid, || {
            let mhz = crate::kvm_clock::tsc_mhz();
            (mhz != 0).then_some(u64::from(mhz) * 1000)
        }).unwrap_or_else(|| (pit_tsc_per_run() / (CALIBRATE_US / 1000), Source::Pit))
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
        4 => "KVM pvclock",
        _ => "PIT",
    }
}

/// Whether a core can run the timer in the mode the boot core chose:
/// TSC-deadline mode needs the core to have it (otherwise the LVT mode is
/// reserved and writing IA32_TSC_DEADLINE raises #GP in the kernel).
pub fn mode_supported(deadline: bool, has_tsc_deadline: bool) -> bool {
    !deadline || has_tsc_deadline
}

/// `mode_supported` for this core.
pub fn core_supported() -> bool {
    mode_supported(DEADLINE.load(Ordering::Relaxed), has_tsc_deadline())
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
    crate::percpu::get().armed.set(ticks);
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
    let armed = crate::percpu::get().armed.get();
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

#[cfg(test)]
mod tests {
    use super::*;

    fn gce_cpuid(leaf: u32, _: u32) -> Cpuid {
        let r = match leaf {
            0 => [0x1f, 0x756e6547, 0x6c65746e, 0x49656e69],
            1 => [0x806f8, 0, 1 << 31, 0],
            0x15 => [2, 152, 25_000_000, 0],
            0x16 => [2700, 3600, 100, 0],
            0x4000_0000 => [0x4000_0001, 0x4b4d564b, 0x564b4d56, 0x4d],
            _ => panic!("unadvertised leaf {leaf:x}"),
        };
        Cpuid { eax: r[0], ebx: r[1], ecx: r[2], edx: r[3] }
    }

    #[test]
    fn gce_virtual_tsc_overrides_physical_cpu_rate() {
        assert_eq!(cpuid_tsc_khz(gce_cpuid), Some(1_900_000));
        assert_eq!(reported_tsc_khz(gce_cpuid, || Some(2_700_000)), Some((2_700_000, Source::Kvm)));
        // No valid pvclock: use the PIT, never the misleading native leaves
        // or leaf 40000010H, which this KVM does not advertise.
        assert_eq!(reported_tsc_khz(gce_cpuid, || None), None);
    }

    #[test]
    fn native_cpuid_and_hypervisor_leaf_remain_available() {
        let native = |leaf, sub| {
            let mut r = gce_cpuid(leaf, sub);
            if leaf == 1 { r.ecx = 0; }
            r
        };
        assert_eq!(reported_tsc_khz(native, || panic!("native CPU queried KVM")), Some((1_900_000, Source::Cpuid)));
        let hypervisor = |leaf, sub| match leaf {
            0x4000_0000 => Cpuid { eax: 0x4000_0010, ebx: 0, ecx: 0, edx: 0 },
            0x4000_0010 => Cpuid { eax: 3_000_000, ebx: 0, ecx: 0, edx: 0 },
            _ => gce_cpuid(leaf, sub),
        };
        assert_eq!(reported_tsc_khz(hypervisor, || None), Some((3_000_000, Source::Hypervisor)));
    }

    /// A TD's CPUID 15H is the TDX module's, so it decides even though the
    /// hypervisor bit is set: not pvclock or the VMM's leaf 40000010H.
    #[test]
    fn tdx_takes_the_tsc_rate_from_leaf_15_only() {
        let td = |leaf, sub| match leaf {
            0x15 => Cpuid { eax: 1, ebx: 80, ecx: 25_000_000, edx: 0 },
            0x4000_0000 | 0x4000_0010 => panic!("asked the VMM"),
            _ => gce_cpuid(leaf, sub),
        };
        assert_eq!(tdx_tsc_khz(td), Some(2_000_000));
        // No usable leaf 15H: no rate, rather than one from leaf 16H.
        for zero in 0..3 {
            let bad = move |leaf, sub| match leaf {
                0x15 => {
                    let mut r = [1, 80, 25_000_000];
                    r[zero] = 0;
                    Cpuid { eax: r[0], ebx: r[1], ecx: r[2], edx: 0 }
                }
                _ => td(leaf, sub),
            };
            assert_eq!(tdx_tsc_khz(bad), None);
        }
        let old = |leaf, sub| {
            let mut r = gce_cpuid(leaf, sub);
            if leaf == 0 { r.eax = 0x14; }
            r
        };
        assert_eq!(tdx_tsc_khz(old), None);
        let amd = |leaf, sub| {
            let mut r = td(leaf, sub);
            if leaf == 0 { r.ebx = 0x6874_7541; }
            r
        };
        assert_eq!(tdx_tsc_khz(amd), None);
    }

    /// Audit F4: an application processor without TSC-deadline mode is
    /// refused when the boot core uses it; one-shot mode suits any core.
    #[test]
    fn tsc_deadline_mode_needs_every_core_to_have_it() {
        assert!(mode_supported(true, true));
        assert!(!mode_supported(true, false));
        assert!(mode_supported(false, true));
        assert!(mode_supported(false, false));
    }
}
