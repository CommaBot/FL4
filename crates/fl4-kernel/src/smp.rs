//! Starting the application processors (seL4 arch/x86/kernel/smp_sys.c).
use crate::{entry, gdt, kprintln, paging};
use core::sync::atomic::{AtomicBool, AtomicPtr, AtomicU32, AtomicU64, AtomicU8, AtomicUsize, Ordering};
use fl4_arch_x86_64::cvm::halt_if_poisoned;
use fl4_arch_x86_64::arch::TIMER_VECTOR;
use fl4_arch_x86_64::{apic, cpu, fpu, percpu, pit, sev::snp, smp, timer};
use fl4_core::boot::Region;
use fl4_core::layout::{pptr, MAX_NODES};
use fl4_core::sched;

core::arch::global_asm!(include_str!("ap.S"), options(att_syntax));

extern "C" {
    static fl4_ap_trampoline: u8;
    static fl4_ap_trampoline_end: u8;
    static fl4_ap_data: u8;
}

const AP_BASE: u64 = 0x8000;
/// The boot core has created the root task; started cores may schedule.
static BOOT_DONE: AtomicBool = AtomicBool::new(false);
/// Zero until the boot core patches text. Then the number of cores
/// whose instruction streams have been serialized since the patch.
static TEXT_SYNCED: AtomicU64 = AtomicU64::new(0);
// AP failures must reach the BSP: a panic halts only the failing CPU and
// would otherwise look like a startup timeout, allowing boot to continue.
static AP_REJECTED: AtomicU8 = AtomicU8::new(0);
const REJECT_SPEC: u8 = 1;
const REJECT_VM: u8 = 2;
const REJECT_APIC: u8 = 3;
const REJECT_FPU: u8 = 4;
const REJECT_TIMER: u8 = 5;
const REJECT_TLB: u8 = 6;
const REJECT_CR4: u8 = 7;
const REJECT_PAGING: u8 = 8;
const REJECT_APIC_ID: u8 = 9;
/// The APIC ID each core was woken as (a TD's mailbox command names it):
/// its local APIC must say the same before it goes online.
static WOKEN_APIC_ID: [AtomicU32; percpu::MAX_CPUS] = [const { AtomicU32::new(u32::MAX) }; percpu::MAX_CPUS];

fn reject_ap(reason: u8) -> ! {
    AP_REJECTED.store(reason, Ordering::Release);
    cpu::halt_forever()
}

/// CPU features the boot core enabled, for the other cores to match.
#[derive(Clone, Copy)]
pub struct Features {
    pub cr4: u64,
    pub window_top: u64,
    pub efer_nx: bool,
    /// The window uses 1 GiB pages (`paging::init`'s `huge`).
    pub huge: bool,
    /// The top of what the kernel maps or user space may map: RAM in the
    /// window and device memory (`device_top`), not only the window.
    pub paddr_top: u64,
    /// A TDX guest's way to start its cores, if it has one.
    pub tdx_wakeup: Option<crate::tdx::Wakeup>,
}

static mut FEATURES: Features = Features { window_top: 0, cr4: 0, efer_nx: false, huge: false, paddr_top: 0, tdx_wakeup: None };

/// PIT ticks for about `us` microseconds.
fn pit_us(us: u64) -> u16 {
    ((pit::HZ * us) / 1_000_000).clamp(1, 65535) as u16
}

fn wait_us(us: u64) {
    let end = cpu::rdtsc() + timer::us_to_ticks(us);
    while cpu::rdtsc() < end {
        core::hint::spin_loop();
    }
}

// Every per-core array the cores index by `percpu::cpu_index` without a
// bounds check (the serial gate's active flags and policy slots)
// and every core bit mask (u64) covers each core `start_aps` may start.
const _: () = assert!(
    percpu::MAX_CPUS <= fl4_sync::MAX_CPUS && percpu::MAX_CPUS <= 64
);

/// Start every other core listed in the MADT, up to the kernel's node
/// limit. Returns the number of cores running, the boot core included.
pub fn start_aps(apic_ids: &[u32], f: Features) -> usize {
    unsafe { FEATURES = f };
    let snp_guest = snp::active();
    if snp_guest && !snp::ap_creation() {
        kprintln!("FL4: SNP hypervisor does not advertise AP creation; using one core");
        return 1;
    }
    let tdx_guest = fl4_arch_x86_64::tdx::active();
    // fl4_boot has said why.
    if tdx_guest && f.tdx_wakeup.is_none() {
        return 1;
    }
    let max = (MAX_NODES as usize).min(percpu::MAX_CPUS);
    let bsp = percpu::apic_id(percpu::cpu_index());
    let smt_shift = fl4_arch_x86_64::spec::smt_shift();
    let tramp = unsafe { &fl4_ap_trampoline as *const u8 };
    let len = unsafe { &fl4_ap_trampoline_end as *const u8 as usize } - tramp as usize;
    let data_off = unsafe { &fl4_ap_data as *const u8 as usize } - tramp as usize;
    let boot_root = match f.tdx_wakeup {
        _ if snp_guest => 0,
        Some(w) => paging::ap_boot_root(w.page),
        None => paging::ap_boot_root(AP_BASE),
    };
    let mut aps = [(0usize, 0u32); percpu::MAX_CPUS];
    let n = crate::ap_order::select(apic_ids, max, |i, id| {
        if !crate::acpi::first_listing(apic_ids, i) || !fl4_arch_x86_64::spec::allow_ap(
            id, bsp, smt_shift, fl4_arch_x86_64::spec::no_smt()) {
            return false;
        }
        // An ID this APIC mode cannot name (an x2APIC entry above 0xfe in
        // xAPIC mode would be truncated to another core's), or the
        // broadcast ID, which would reset every core.
        if !apic::valid_physical_dest(id, apic::is_x2apic()) {
            kprintln!("FL4: skipping core with APIC id {:#x}: not addressable in this APIC mode", id);
            return false;
        }
        true
    }, &mut aps);
    // A TD's MADT is the VMM's, its vCPU count the TDX module's: no more
    // cores than vCPUs, and none of them left out, where it would wait in
    // firmware for a wakeup the kernel never sends.
    if tdx_guest {
        let vcpus = fl4_arch_x86_64::tdx::num_vcpus() as usize;
        if !crate::ap_order::tdx_cores_match(n + 1, vcpus, max) {
            kprintln!("FL4: the MADT gives {} usable core(s) for {} TDX vCPU(s) (kernel limit {})", n + 1, vcpus, max);
            crate::fail("TDX vCPUs and MADT cores do not match");
        }
    }
    // Cores 0..=n: the boot core and the indices `select` handed out.
    crate::entry::GATE.set_cores(n + 1);
    let entry = fl4_ap_main as *const () as u64;
    if let Some(w) = f.tdx_wakeup {
        crate::tdx::prepare_wakeup(w.page, boot_root, f.efer_nx, entry);
    }
    // A TDX VMM schedules the vCPU that has to come up.
    let start_timeout_us = if tdx_guest { 5_000_000 } else { 100_000 };
    crate::ap_order::bring_up(&aps[..n], snp_guest, |c, _| {
        crate::snp::prepare_ap(c, percpu::stack_top(c), entry);
    }, |c, id| {
        halt_if_poisoned();
        let before = smp::num_online();
        WOKEN_APIC_ID[c].store(id, Ordering::Release);
        if snp_guest {
            crate::snp::start_ap(c, id);
        } else if let Some(w) = f.tdx_wakeup {
            crate::tdx::start_ap(w, c, id);
        } else {
            unsafe {
                core::ptr::copy_nonoverlapping(tramp, pptr(AP_BASE) as *mut u8, len);
                let d = (pptr(AP_BASE) as usize + data_off) as *mut u64;
                d.write_volatile(boot_root);
                d.add(1).write_volatile((1 << 8) | if f.efer_nx { 1 << 11 } else { 0 });
                d.add(2).write_volatile(percpu::stack_top(c));
                d.add(3).write_volatile(entry);
                d.add(4).write_volatile(c as u64);
            }
            // INIT, then two STARTUPs with the trampoline's page number.
            apic::send_ipi(id, 0x4500);
            pit::wait(pit_us(10_000), || {});
            for _ in 0..2 {
                apic::send_ipi(id, 0x4600 | (AP_BASE >> 12) as u32);
                wait_us(200);
            }
        }
        let deadline = cpu::rdtsc() + timer::us_to_ticks(start_timeout_us);
        // A TDX AP the trampoline or `tdx::register_ap` rejected has
        // poisoned the guest: stop at once, also if the core is up.
        let started = crate::ap_order::wait_start(
            fl4_arch_x86_64::cvm::poisoned,
            || AP_REJECTED.load(Ordering::Acquire),
            || smp::num_online() != before,
            || cpu::rdtsc() >= deadline,
        );
        halt_if_poisoned();
        if let crate::ap_order::Started::Rejected(rejected) = started {
            kprintln!("FL4: rejecting AP with APIC id {}: {}", id, match rejected {
                REJECT_SPEC => "speculation capabilities differ between cores",
                REJECT_APIC => "local APIC outside the physical window",
                REJECT_FPU => "FPU state components or save format differ between cores",
                REJECT_TIMER => "TSC-deadline timer missing on this core",
                REJECT_TLB => "PCID or INVPCID missing on this core",
                REJECT_CR4 => "SMEP, SMAP or FSGSBASE missing on this core",
                REJECT_PAGING => "1 GiB pages missing, or physical addresses narrower than the system's, on this core",
                REJECT_APIC_ID => "its local APIC ID is not the one it was woken as",
                _ => "virtualization features differ between cores",
            });
            // VMX/SVM may already be active on other cores. Keep them at
            // BOOT_DONE and halt the BSP; never publish a partial backend.
            crate::fail("incompatible AP capabilities; refusing to start userspace");
        }
        if started != crate::ap_order::Started::Online {
            kprintln!("FL4: core with APIC id {} did not start", id);
            // An AP could still be probing. Do not reuse its per-core slot
            // or release userspace before its capabilities are known.
            crate::fail("AP startup timed out; refusing to start userspace");
        }
    });
    halt_if_poisoned();
    if f.tdx_wakeup.is_some() {
        crate::tdx::finish_wakeup();
    }
    halt_if_poisoned();
    smp::num_online() as usize
}

/// How much unaccepted memory one core takes at a time.
const ACCEPT_CHUNK: u64 = 64 << 20;
/// The ranges being accepted: published once, in static memory.
static ACCEPT_LIST: AtomicPtr<Region> = AtomicPtr::new(core::ptr::null_mut());
static ACCEPT_LEN: AtomicUsize = AtomicUsize::new(0);
static ACCEPT_CHUNKS: AtomicU64 = AtomicU64::new(0);
static ACCEPT_NEXT: AtomicU64 = AtomicU64::new(0);
static ACCEPT_DONE: AtomicU64 = AtomicU64::new(0);

/// Accept pieces of the published ranges until none is left.
fn help_accept() {
    let list = ACCEPT_LIST.load(Ordering::Acquire);
    if list.is_null() {
        return;
    }
    let ranges = unsafe { core::slice::from_raw_parts(list, ACCEPT_LEN.load(Ordering::Acquire)) };
    let chunks = ACCEPT_CHUNKS.load(Ordering::Acquire);
    // Once every piece is taken, a core waiting here only reads the counter.
    // A poisoned guest takes no more pieces.
    loop {
        halt_if_poisoned();
        let Some(index) = crate::ap_order::next_accept_chunk(fl4_arch_x86_64::cvm::poisoned(), &ACCEPT_NEXT, chunks) else { break };
        let Some((start, end)) = crate::bootmem::chunk_of(ranges, index, ACCEPT_CHUNK) else { break };
        fl4_arch_x86_64::tdx::accept_pages(start, end - start);
        ACCEPT_DONE.fetch_add(end - start, Ordering::AcqRel);
    }
}

/// Accept `ranges` (TDG.MEM.PAGE.ACCEPT) on every online core: the APs do
/// this while they wait for the root task (`fl4_ap_main`).
pub fn accept_memory(ranges: &'static [Region]) {
    let total: u64 = ranges.iter().map(|r| r.end - r.start).sum();
    if total == 0 {
        return;
    }
    halt_if_poisoned();
    ACCEPT_CHUNKS.store(crate::bootmem::chunk_count(ranges, ACCEPT_CHUNK), Ordering::Release);
    ACCEPT_LEN.store(ranges.len(), Ordering::Release);
    ACCEPT_LIST.store(ranges.as_ptr().cast_mut(), Ordering::Release);
    help_accept();
    halt_if_poisoned();
    while ACCEPT_DONE.load(Ordering::Acquire) < total {
        halt_if_poisoned();
        core::hint::spin_loop();
    }
    ACCEPT_LIST.store(core::ptr::null_mut(), Ordering::Release);
}

/// Synchronize the patched instructions before enabling the new native
/// entry path. APs acknowledge the patch while still at the boot barrier.
pub fn sync_patched_text() {
    cpu::serialize_instructions();
    TEXT_SYNCED.store(1, Ordering::Release);
    let online = smp::num_online();
    let deadline = cpu::rdtsc() + timer::us_to_ticks(100_000);
    halt_if_poisoned();
    while TEXT_SYNCED.load(Ordering::Acquire) < online {
        halt_if_poisoned();
        if cpu::rdtsc() >= deadline {
            crate::fail("AP did not synchronize patched instructions");
        }
        core::hint::spin_loop();
    }
}

/// The root task exists: let the other cores schedule.
pub fn release_aps() {
    BOOT_DONE.store(true, Ordering::Release);
}

/// An application processor, from the trampoline, on its kernel stack.
#[no_mangle]
extern "C" fn fl4_ap_main(c: u64) -> ! {
    let f = unsafe { FEATURES };
    // Before anything that can take #VE; then this vCPU must be one of the
    // TD's that has not run the kernel yet.
    if fl4_arch_x86_64::tdx::active() {
        gdt::load_boot_idt();
        fl4_arch_x86_64::tdx::register_ap();
    }
    if snp::active() { snp::register_cpu(); }
    // Natively before the boot core's tables, whose 1 GiB pages and
    // addresses a core without them faults on with no IDT; on SNP (CPUID
    // by #VC) once the core's own IDT is in, below.
    if !snp::active() && !cpu::core_paging_supported(f.huge, f.paddr_top) { reject_ap(REJECT_PAGING); }
    cpu::write_cr3(paging::root_paddr());
    // Natively before CR4.PCIDE, SMEP, SMAP and FSGSBASE, which fault on a
    // core without them, with no IDT yet to catch it (OSXSAVE and VMXE are
    // left to fpu::init and vm::init). An SNP AP starts with the boot
    // core's CR4 (snp::start_ap) and takes #VC for CPUID, so it checks once
    // its own GDT and IDT are in.
    if !snp::active() && !fl4_arch_x86_64::tlb::core_supported() { reject_ap(REJECT_TLB); }
    if !snp::active() && !cpu::core_cr4_supported(f.cr4) { reject_ap(REJECT_CR4); }
    cpu::write_cr4(f.cr4);
    let stack_top = percpu::stack_top(c as usize);
    gdt::init_core(c as usize, stack_top);
    if snp::active() && !fl4_arch_x86_64::tlb::core_supported() { reject_ap(REJECT_TLB); }
    if snp::active() && !cpu::core_cr4_supported(f.cr4) { reject_ap(REJECT_CR4); }
    if snp::active() && !cpu::core_paging_supported(f.huge, f.paddr_top) { reject_ap(REJECT_PAGING); }
    cpu::init_pat();
    if !fpu::init(false) { reject_ap(REJECT_FPU); }
    if !fl4_arch_x86_64::spec::init_core(false) { reject_ap(REJECT_SPEC); }
    if !fl4_arch_x86_64::vm::init(false) { reject_ap(REJECT_VM); }
    percpu::get().cr3.set(paging::root_paddr());
    if apic::enable(false, f.window_top).is_none() { reject_ap(REJECT_APIC); }
    apic::write(apic::REG_SVR, (1 << 8) | 0xff);
    apic::write(apic::REG_LVT_LINT0, 1 << 16);
    apic::write(apic::REG_LVT_LINT1, 1 << 16);
    apic::write(apic::REG_LVT_ERROR, 1 << 16);
    // Read once: in a TD without ENUM_TOPOLOGY the ID comes from the VMM
    // (#VE), and the one checked must be the one other cores send IPIs to.
    // The VMM picks which vCPU answers a mailbox wakeup: it must be the
    // core the boot core woke, by that ID.
    let apic_id = apic::id();
    if fl4_arch_x86_64::tdx::active() && apic_id != WOKEN_APIC_ID[c as usize].load(Ordering::Acquire) {
        reject_ap(REJECT_APIC_ID);
    }
    percpu::set_apic_id(apic_id);
    if !timer::core_supported() { reject_ap(REJECT_TIMER); }
    timer::init_core(TIMER_VECTOR);
    smp::set_online(c as usize);
    let mut text_synced = false;
    while !BOOT_DONE.load(Ordering::Acquire) {
        if !text_synced && TEXT_SYNCED.load(Ordering::Acquire) != 0 {
            cpu::serialize_instructions();
            TEXT_SYNCED.fetch_add(1, Ordering::AcqRel);
            text_synced = true;
        }
        help_accept();
        core::hint::spin_loop();
    }
    entry::lock();
    let mut s = entry::store();
    let mut a = fl4_arch_x86_64::arch::PhysArch;
    sched::schedule(&mut s, &mut a);
    sched::activate_thread(&mut s, &mut a);
    entry::exit()
}
