//! Intel TDX guest primitives: the TDCALL leaves of the TDX Module v1.5 ABI
//! and the TDG.VP.VMCALL services of the GHCI v1.5.
//!
//! Everything a TDG.VP.VMCALL returns comes from the untrusted VMM. Only the
//! registers a call names in its RCX bitmap reach the VMM, and each of them
//! holds an argument or zero, never a kernel value.
use crate::cpu::{self, Cpuid};
use crate::cvm;
use core::arch::asm;
use core::fmt::{self, Write};
use core::sync::atomic::{compiler_fence, AtomicBool, AtomicU64, Ordering};

// TDCALL leaves.
const TDG_VP_VMCALL: u64 = 0;
const TDG_VP_INFO: u64 = 1;
const TDG_MR_RTMR_EXTEND: u64 = 2;
const TDG_VP_VEINFO_GET: u64 = 3;
const TDG_MR_REPORT: u64 = 4;
const TDG_MEM_PAGE_ACCEPT: u64 = 6;
const TDG_VM_RD: u64 = 7;
const TDG_VM_WR: u64 = 8;

// TDCALL completion status: the class is in the upper half.
const STATUS_CLASS: u64 = 0xffff_ffff_0000_0000;
const OPERAND_BUSY: u64 = 0x8000_0200_0000_0000;
const PAGE_ALREADY_ACCEPTED: u64 = 0x0000_0b0a_0000_0000;
const PAGE_SIZE_MISMATCH: u64 = 0xc000_0b0b_0000_0000;

// TDG.VP.VMCALL sub-functions: VMX exit reasons, then the GHCI's own.
pub const EXIT_CPUID: u32 = 10;
pub const EXIT_HLT: u32 = 12;
pub const EXIT_IO: u32 = 30;
pub const EXIT_MSR_READ: u32 = 31;
pub const EXIT_MSR_WRITE: u32 = 32;
pub const EXIT_EPT_VIOLATION: u32 = 48;
pub const EXIT_WBINVD: u32 = 54;
const VMCALL_MAP_GPA: u64 = 0x10001;
const VMCALL_GET_QUOTE: u64 = 0x10002;
const VMCALL_REPORT_FATAL_ERROR: u64 = 0x10003;

/// TDG.VP.VMCALL status (R10): the VMM asks to continue from R11.
const VMCALL_RETRY: u64 = 1;

// The RCX bitmap of the registers a TDG.VP.VMCALL shows the VMM.
const R10: u64 = 1 << 10;
const R11: u64 = 1 << 11;
const R12: u64 = 1 << 12;
const R13: u64 = 1 << 13;
const R14: u64 = 1 << 14;
const R15: u64 = 1 << 15;

// TD attributes and TD-scope metadata fields (TDG.VM.RD, TDG.VM.WR).
pub const ATTR_DEBUG: u64 = 1 << 0;
pub const ATTR_SEPT_VE_DISABLE: u64 = 1 << 28;
pub const ATTR_PERFMON: u64 = 1 << 63;
const TDCS_CONFIG_FLAGS: u64 = 0x1110_0003_0000_0016;
const TDCS_TD_CTLS: u64 = 0x1110_0003_0000_0017;
const CONFIG_FLEXIBLE_PENDING_VE: u64 = 1 << 1;
const TD_CTLS_PENDING_VE_DISABLE: u64 = 1 << 0;
/// TD_CTLS.ENUM_TOPOLOGY: the TDX module answers the topology leaves
/// (CPUID 0BH and 1FH) itself, from what the VMM configured, instead of
/// raising #VE for them.
const TD_CTLS_ENUM_TOPOLOGY: u64 = 1 << 1;

const PAGE: u64 = 4096;
const HUGE: u64 = 2 << 20;
/// TDG.MEM.PAGE.ACCEPT's page level in RCX[2:0].
const LEVEL_4K: u64 = 0;
const LEVEL_2M: u64 = 1;
/// Tries of one page that another vCPU keeps busy.
const ACCEPT_BUSY_RETRIES: u32 = 1 << 16;
/// MapGPA RETRY answers in a row that make no progress.
const MAP_GPA_RETRIES: u32 = 16;
/// `report`'s output size.
pub const TDREPORT_BYTES: usize = 1024;

// Read by the entry and return stubs, including on skim page tables.
#[no_mangle]
#[cfg_attr(target_os = "none", link_section = ".bss.skim")]
static FL4_TDX_ACTIVE: AtomicBool = AtomicBool::new(false);

static GPAW: AtomicU64 = AtomicU64::new(0);
static ATTRIBUTES: AtomicU64 = AtomicU64::new(0);
static TD_CTLS: AtomicU64 = AtomicU64::new(0);
static VCPUS: AtomicU64 = AtomicU64::new(0);

/// The most vCPUs `register_vcpu` tells apart.
pub const MAX_VCPU_INDEX: usize = 1024;
/// The VCPU_INDEX (TDG.VP.INFO) of each vCPU that runs the kernel: each
/// may do so once.
static VCPU_SEEN: [AtomicU64; MAX_VCPU_INDEX / 64] = [const { AtomicU64::new(0) }; MAX_VCPU_INDEX / 64];

#[inline]
pub fn active() -> bool {
    FL4_TDX_ACTIVE.load(Ordering::Relaxed)
}

/// The registers of a TDCALL other than the leaf and status in RAX.
#[derive(Clone, Copy, Default)]
struct Regs {
    rcx: u64,
    rdx: u64,
    r8: u64,
    r9: u64,
    r10: u64,
    r11: u64,
}

/// A TDCALL to the TDX module; returns its status.
fn tdcall(leaf: u64, r: &mut Regs) -> u64 {
    let status: u64;
    unsafe {
        asm!(
            ".byte 0x66, 0x0f, 0x01, 0xcc", // TDCALL
            inlateout("rax") leaf => status,
            inlateout("rcx") r.rcx,
            inlateout("rdx") r.rdx,
            inlateout("r8") r.r8,
            inlateout("r9") r.r9,
            inlateout("r10") r.r10,
            inlateout("r11") r.r11,
            options(nostack),
        );
    }
    status
}

#[derive(Clone, Copy, Default)]
struct VmcallOut {
    status: u64,
    r11: u64,
    r12: u64,
    r13: u64,
    r14: u64,
    r15: u64,
}

/// TDG.VP.VMCALL with the registers of `expose` (R10 and R11 always) shown
/// to the VMM, all set here. Returns the TDCALL status too.
fn raw_vmcall(expose: u64, sub: u64, a12: u64, a13: u64, a14: u64, a15: u64) -> (u64, VmcallOut) {
    let mut o = VmcallOut::default();
    let tdcall_status: u64;
    unsafe {
        asm!(
            ".byte 0x66, 0x0f, 0x01, 0xcc", // TDCALL
            // The VMM chose the values now in the exposed registers.
            "lfence",
            inlateout("rax") TDG_VP_VMCALL => tdcall_status,
            inlateout("rcx") expose | R10 | R11 => _,
            inlateout("r10") 0u64 => o.status,
            inlateout("r11") sub => o.r11,
            inlateout("r12") a12 => o.r12,
            inlateout("r13") a13 => o.r13,
            inlateout("r14") a14 => o.r14,
            inlateout("r15") a15 => o.r15,
            lateout("rdx") _,
            lateout("rsi") _,
            lateout("rdi") _,
            lateout("r8") _,
            lateout("r9") _,
            options(nostack),
        );
    }
    (tdcall_status, o)
}

fn vmcall(expose: u64, sub: u64, a12: u64, a13: u64, a14: u64, a15: u64) -> VmcallOut {
    let (tdcall_status, o) = raw_vmcall(expose, sub, a12, a13, a14, a15);
    if tdcall_status != 0 {
        terminate_with(1, format_args!("sub={:#x} tdcall={:#x}", sub, tdcall_status));
    }
    o
}

/// The longest fatal line, its newline included.
const FATAL_LINE: usize = 160;
const COM1: u64 = 0x3f8;
const COM1_LSR: u64 = COM1 + 5;
const LSR_THRE: u64 = 0x20;
/// Polls of the transmitter for one byte, before the line stops polling.
const FATAL_LSR_POLLS: u32 = 65536;

/// A fatal line on the stack. What does not fit is cut: formatting never
/// fails or panics, and the newline always fits.
struct FatalLine {
    buf: [u8; FATAL_LINE],
    len: usize,
}

impl Write for FatalLine {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        let n = s.len().min(FATAL_LINE - 1 - self.len);
        self.buf[self.len..self.len + n].copy_from_slice(&s.as_bytes()[..n]);
        self.len += n;
        Ok(())
    }
}

fn fatal_line(reason: u8, detail: Option<fmt::Arguments<'_>>) -> FatalLine {
    let mut line = FatalLine { buf: [0; FATAL_LINE], len: 0 };
    let _ = match detail {
        Some(d) => write!(line, "FL4: TDX fatal (reason {reason}): {d}"),
        None => write!(line, "FL4: TDX fatal (reason {reason})"),
    };
    line.buf[line.len] = b'\n';
    line.len += 1;
    line
}

/// One byte to COM1. Uses `raw_vmcall` and ignores its status, so that a
/// failing VMCALL cannot come back here through `terminate`. After a byte
/// whose transmitter never went idle, `poll` is off and the rest is written
/// without waiting.
fn fatal_serial_byte(byte: u8, poll: &mut bool) {
    let io = R12 | R13 | R14 | R15;
    if *poll {
        let ready = (0..FATAL_LSR_POLLS).any(|_| raw_vmcall(io, EXIT_IO as u64, 1, 0, COM1_LSR, 0).1.r11 & LSR_THRE != 0);
        *poll = ready;
    }
    let _ = raw_vmcall(io, EXIT_IO as u64, 1, 1, COM1, byte as u64);
}

/// Write to COM1 with no lock and nothing that can terminate.
fn fatal_serial_write(bytes: &[u8]) {
    let mut poll = true;
    for &b in bytes {
        if b == b'\n' {
            fatal_serial_byte(b'\r', &mut poll);
        }
        fatal_serial_byte(b, &mut poll);
    }
}

fn fatal(reason: u8, detail: Option<fmt::Arguments<'_>>) -> ! {
    // Only the first failing vCPU reports, so lines do not interleave.
    if cvm::poison() {
        cpu::halt_forever();
    }
    let line = fatal_line(reason, detail);
    fatal_serial_write(&line.buf[..line.len]);
    let _ = raw_vmcall(R12 | R13, VMCALL_REPORT_FATAL_ERROR, reason as u64, 0, 0, 0);
    cpu::halt_forever()
}

/// Stop every core, for good: a VMM that ignores the report still gets no
/// more guest execution (`cvm::poison`, checked at each kernel entry and
/// exit).
pub fn terminate(reason: u8) -> ! {
    fatal(reason, None)
}

/// `terminate`, saying why on the serial console. The VMM reads that
/// console: `detail` may hold reason codes, TDCALL and VMCALL status, MSR
/// numbers, GPAs the VMM already knows, vectors and flags, and never a
/// register's contents, a value being written, a stack address or private
/// memory.
pub fn terminate_with(reason: u8, detail: fmt::Arguments<'_>) -> ! {
    fatal(reason, Some(detail))
}

/// Halt this vCPU for good, without an instruction that would take #VE.
pub fn halt_loop() -> ! {
    unsafe { asm!("cli", options(nomem, nostack)) };
    loop {
        let _ = raw_vmcall(R12, EXIT_HLT as u64, 1, 0, 0, 0);
        core::hint::spin_loop();
    }
}

/// This guest, as TDG.VP.INFO and TDG.VM.RD describe it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Info {
    pub gpaw: u64,
    pub shared_mask: u64,
    pub attributes: u64,
    pub num_vcpus: u64,
    pub max_vcpus: u64,
    /// This vCPU's VCPU_INDEX, which the TDX module assigns: unique in the
    /// TD and below `num_vcpus`.
    pub vcpu_index: u32,
}

/// CPUID.21H,0 says "IntelTDX    " in EBX, EDX, ECX.
pub fn is_tdx_signature(max_leaf: u32, ebx: u32, ecx: u32, edx: u32) -> bool {
    max_leaf >= 0x21 && ebx == u32::from_le_bytes(*b"Inte") && edx == u32::from_le_bytes(*b"lTDX")
        && ecx == u32::from_le_bytes(*b"    ")
}

/// The shared bit of a guest with this GPA width: the width's top bit.
/// TDX has 48- and 52-bit guests only.
pub fn shared_mask_of(gpaw: u64) -> Option<u64> {
    matches!(gpaw, 48 | 52).then(|| 1 << (gpaw - 1))
}

/// Detect a TDX guest. Runs first on the boot core, on the CPUID that a TD
/// gets from the TDX module, so the signature cannot be forged by the VMM of
/// a real TD; a non-TD that forges it faults on TDCALL.
pub fn probe() -> Option<Info> {
    use core::arch::x86_64::__cpuid_count;
    let max_leaf = __cpuid_count(0, 0).eax;
    if max_leaf < 0x21 {
        return None;
    }
    let l = __cpuid_count(0x21, 0);
    if !is_tdx_signature(max_leaf, l.ebx, l.ecx, l.edx) {
        return None;
    }
    let mut r = Regs::default();
    if tdcall(TDG_VP_INFO, &mut r) != 0 {
        return None;
    }
    let gpaw = r.rcx & 0x3f;
    Some(Info {
        gpaw,
        shared_mask: shared_mask_of(gpaw)?,
        attributes: r.rdx,
        num_vcpus: r.r8 & 0xffff_ffff,
        max_vcpus: r.r8 >> 32,
        vcpu_index: (r.r9 & 0xffff_ffff) as u32,
    })
}

/// Mark `vcpu_index` as running the kernel in `seen`. False if it is not a
/// vCPU of this TD (at or past `num_vcpus`, or past what `seen` holds) or
/// was marked before: two cores of the kernel on one vCPU, or one the TD
/// does not have, is the VMM's doing.
pub fn claim_vcpu(seen: &[AtomicU64], vcpu_index: u32, num_vcpus: u64) -> bool {
    let i = vcpu_index as usize;
    if vcpu_index as u64 >= num_vcpus || i >= seen.len() * 64 {
        return false;
    }
    let bit = 1u64 << (i % 64);
    seen[i / 64].fetch_or(bit, Ordering::AcqRel) & bit == 0
}

/// `claim_vcpu` on the kernel's record of the TD's vCPUs.
pub fn register_vcpu(vcpu_index: u32, num_vcpus: u64) -> bool {
    claim_vcpu(&VCPU_SEEN, vcpu_index, num_vcpus)
}

/// The number of vCPUs the TD has (TDG.VP.INFO NUM_VCPUS, at `init`).
pub fn num_vcpus() -> u64 {
    VCPUS.load(Ordering::Relaxed) & 0xffff_ffff
}

/// An AP's first act as a core of the kernel, before anything that can
/// take #VE: its VCPU_INDEX must be new and one of the TD's, or the TD ends.
pub fn register_ap() {
    let mut r = Regs::default();
    let status = tdcall(TDG_VP_INFO, &mut r);
    if status != 0 {
        terminate_with(11, format_args!("ap vp_info tdcall={:#x}", status));
    }
    let index = (r.r9 & 0xffff_ffff) as u32;
    if !register_vcpu(index, num_vcpus()) {
        terminate_with(11, format_args!("ap vcpu_index={} num_vcpus={}", index, num_vcpus()));
    }
}

fn vm_rd(field: u64) -> Option<u64> {
    let mut r = Regs { rdx: field, ..Regs::default() };
    (tdcall(TDG_VM_RD, &mut r) == 0).then_some(r.r8)
}

fn vm_wr(field: u64, value: u64, mask: u64) -> bool {
    let mut r = Regs { rdx: field, r8: value, r9: mask, ..Regs::default() };
    tdcall(TDG_VM_WR, &mut r) == 0
}

/// What to do about #VE on unaccepted private memory, which would let the
/// VMM raise an exception at any private access by removing a page.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SeptVe {
    /// Already off.
    Off,
    /// A debug TD keeps it, for diagnostics.
    Keep,
    /// Turn it off with TDG.VM.WR.
    Disable,
    /// It cannot be turned off.
    Refuse,
}

/// The decision of `SeptVe` (Linux `disable_sept_ve`): `config` is
/// TDCS.CONFIG_FLAGS and `ctls` TDCS.TD_CTLS, None for a TDX module without
/// them, where the attribute alone decides.
pub fn sept_ve_action(attributes: u64, config: Option<u64>, ctls: Option<u64>) -> SeptVe {
    let debug = attributes & ATTR_DEBUG != 0;
    if config.unwrap_or(0) & CONFIG_FLEXIBLE_PENDING_VE == 0 {
        return if attributes & ATTR_SEPT_VE_DISABLE != 0 {
            SeptVe::Off
        } else if debug {
            SeptVe::Keep
        } else {
            SeptVe::Refuse
        };
    }
    if ctls.unwrap_or(0) & TD_CTLS_PENDING_VE_DISABLE != 0 {
        SeptVe::Off
    } else if debug {
        SeptVe::Keep
    } else {
        SeptVe::Disable
    }
}

/// Take over as a TD, on the boot core, once #VE has a handler.
pub fn init(info: Info) {
    FL4_TDX_ACTIVE.store(true, Ordering::Release);
    cvm::set_hardened();
    GPAW.store(info.gpaw, Ordering::Relaxed);
    ATTRIBUTES.store(info.attributes, Ordering::Relaxed);
    VCPUS.store(info.num_vcpus | (info.max_vcpus << 32), Ordering::Relaxed);
    let config = vm_rd(TDCS_CONFIG_FLAGS);
    let ctls = vm_rd(TDCS_TD_CTLS);
    let action = sept_ve_action(info.attributes, config, ctls);
    let refused = match action {
        SeptVe::Off | SeptVe::Keep => false,
        SeptVe::Disable => !vm_wr(TDCS_TD_CTLS, TD_CTLS_PENDING_VE_DISABLE, TD_CTLS_PENDING_VE_DISABLE),
        SeptVe::Refuse => true,
    };
    if refused {
        terminate_with(2, format_args!("sept_ve action={:?} attrs={:#x} cfg={:x?} ctls={:x?}", action, info.attributes, config, ctls));
    }
    if !register_vcpu(info.vcpu_index, info.num_vcpus) {
        terminate_with(11, format_args!("bsp vcpu_index={} num_vcpus={}", info.vcpu_index, info.num_vcpus));
    }
    // Best effort: the topology leaves from the TDX module rather than by
    // #VE from the VMM. A module or VMM without a configured topology
    // refuses, and `virtual_cpuid` lets those leaves through #VE.
    let _ = vm_wr(TDCS_TD_CTLS, TD_CTLS_ENUM_TOPOLOGY, TD_CTLS_ENUM_TOPOLOGY);
    TD_CTLS.store(vm_rd(TDCS_TD_CTLS).unwrap_or(0), Ordering::Relaxed);
}

/// The record for `seL4_X86_TdxInfo`: gpaw, attributes, td_ctls,
/// num_vcpus, max_vcpus.
pub fn boot_info() -> [u64; 5] {
    let vcpus = VCPUS.load(Ordering::Relaxed);
    [
        GPAW.load(Ordering::Relaxed),
        ATTRIBUTES.load(Ordering::Relaxed),
        TD_CTLS.load(Ordering::Relaxed),
        vcpus & 0xffff_ffff,
        vcpus >> 32,
    ]
}

/// Whether a TD with these attributes has the performance counters that
/// CR4.PCE gives user code.
pub fn user_pmc_allowed(attributes: u64) -> bool {
    attributes & ATTR_PERFMON != 0
}

/// MSRs a kernel #VE forwards to the VMM: the architectural x2APIC registers
/// and its TSC-deadline timer, which the VMM emulates, and (read only) the
/// APIC base, which a TD may not write.
pub fn virtual_msr(msr: u32, write: bool) -> bool {
    match msr {
        cpu::msr::TSC_DEADLINE | 0x800..=0x83f => true,
        cpu::msr::APIC_BASE => !write,
        _ => false,
    }
}

/// CPUID leaves a kernel #VE forwards to the VMM: the topology leaves 0BH
/// and 1FH (`spec::smt_shift`), which take #VE unless TD_CTLS.ENUM_TOPOLOGY
/// is set. Every other leaf the kernel uses below the hypervisor range the
/// TDX module answers itself (TDX Module 1.5 CPUID virtualization), and
/// the hypervisor range goes to the VMM directly (`cpuid_is_vmm_leaf`): a
/// #VE on any other leaf is no answer the kernel should take from the VMM.
pub fn virtual_cpuid(leaf: u32) -> bool {
    matches!(leaf, 0x0b | 0x1f)
}

/// The one operand an unsupported kernel #VE may name on the console, which
/// the VMM reads: the MSR number of a verified RDMSR or WRMSR, or the leaf
/// of a CPUID. Never the raw registers: at any other instruction they hold
/// kernel data, and a WRMSR's RAX is the value being written.
pub fn ve_log_operand(exit_reason: u32, opcode: [u8; 2], rax: u64, rcx: u64) -> Option<u32> {
    match (exit_reason, opcode) {
        (EXIT_MSR_READ, [0x0f, 0x32]) | (EXIT_MSR_WRITE, [0x0f, 0x30]) => Some(rcx as u32),
        (EXIT_CPUID, [0x0f, 0xa2]) => Some(rax as u32),
        _ => None,
    }
}

/// What TDG.VP.VEINFO.GET says about the #VE this vCPU took.
#[derive(Clone, Copy, Debug)]
pub struct VeInfo {
    pub exit_reason: u32,
    pub qualification: u64,
    pub gla: u64,
    pub gpa: u64,
    pub instr_len: u32,
}

/// The current #VE's information. Until this runs, another #VE is a double
/// fault, so a #VE handler calls it before anything else.
pub fn ve_info() -> VeInfo {
    let mut r = Regs::default();
    let status = tdcall(TDG_VP_VEINFO_GET, &mut r);
    if status != 0 {
        terminate_with(3, format_args!("ve_info tdcall={:#x}", status));
    }
    VeInfo {
        exit_reason: r.rcx as u32,
        qualification: r.rdx,
        gla: r.r8,
        gpa: r.r9,
        instr_len: r.r10 as u32,
    }
}

/// What to do after TDG.MEM.PAGE.ACCEPT at a page level.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Accepted {
    Advance,
    /// The page is mapped smaller: accept this range in 4 KiB pages.
    Split,
    Retry,
    Fail,
}

fn accept_result(status: u64, level: u64) -> Accepted {
    match status & STATUS_CLASS {
        0 | PAGE_ALREADY_ACCEPTED => Accepted::Advance,
        PAGE_SIZE_MISMATCH if level != LEVEL_4K => Accepted::Split,
        OPERAND_BUSY => Accepted::Retry,
        _ => Accepted::Fail,
    }
}

/// Accept `[pa, pa + bytes)`, page-aligned private GPAs: in 2 MiB pages where
/// they fit and the VMM mapped them so, otherwise in 4 KiB pages.
pub fn accept_pages(pa: u64, bytes: u64) {
    let end = pa + bytes;
    let mut cur = pa;
    let mut small = false;
    let mut busy = 0;
    while cur < end {
        // Another core poisoned the guest: accept nothing more (also
        // between busy retries).
        cvm::halt_if_poisoned();
        let level = if !small && cur % HUGE == 0 && end - cur >= HUGE { LEVEL_2M } else { LEVEL_4K };
        let mut r = Regs { rcx: cur | level, ..Regs::default() };
        let status = tdcall(TDG_MEM_PAGE_ACCEPT, &mut r);
        match accept_result(status, level) {
            Accepted::Advance => {
                cur += if level == LEVEL_2M { HUGE } else { PAGE };
                small = false;
                busy = 0;
            }
            Accepted::Split => small = true,
            Accepted::Retry => {
                busy += 1;
                if busy > ACCEPT_BUSY_RETRIES {
                    terminate_with(4, format_args!("accept status={:#x} lvl={} cur={:#x} end={:#x} busy={}", status, level, cur, end, busy));
                }
                core::hint::spin_loop();
            }
            Accepted::Fail => terminate_with(4, format_args!("accept status={:#x} lvl={} cur={:#x} end={:#x} busy={}", status, level, cur, end, busy)),
        }
    }
}

/// How a MapGPA goes on after the VMM answered.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MapGpa {
    Done,
    /// Call again from this GPA, with this many fruitless answers so far.
    Continue(u64, u32),
    /// The VMM broke the protocol.
    Violation,
}

/// The next step of a MapGPA of `[cur, end)`. On RETRY, R11 is where to go on
/// from, and the VMM picks it: it must be page-aligned and in `(cur, end]`.
/// An answer of `cur` itself (no progress) is allowed `MAP_GPA_RETRIES` times.
pub fn map_gpa_step(cur: u64, end: u64, status: u64, r11: u64, stalled: u32) -> MapGpa {
    if status == 0 {
        return MapGpa::Done;
    }
    if status != VMCALL_RETRY || r11 & (PAGE - 1) != 0 || r11 < cur || r11 > end {
        return MapGpa::Violation;
    }
    if r11 == cur {
        return if stalled >= MAP_GPA_RETRIES { MapGpa::Violation } else { MapGpa::Continue(cur, stalled + 1) };
    }
    if r11 == end { MapGpa::Done } else { MapGpa::Continue(r11, 0) }
}

/// TDG.VP.VMCALL<MapGPA>: `gpa` carries the shared bit for private to
/// shared. A VMM that does not complete it ends the guest, as the page
/// would otherwise have an unknown state.
pub fn map_gpa(gpa: u64, bytes: u64) {
    let end = gpa + bytes;
    let mut cur = gpa;
    let mut stalled = 0;
    loop {
        let o = vmcall(R12 | R13, VMCALL_MAP_GPA, cur, end - cur, 0, 0);
        match map_gpa_step(cur, end, o.status, o.r11, stalled) {
            MapGpa::Done => return,
            MapGpa::Continue(next, s) => {
                cur = next;
                stalled = s;
            }
            MapGpa::Violation => terminate_with(5, format_args!("map_gpa status={:#x} cur={:#x} end={:#x} r11={:#x} stalled={}", o.status, cur, end, o.r11, stalled)),
        }
    }
}

/// TDG.VP.VMCALL<Instruction.CPUID>.
pub fn cpuid(leaf: u32, sub: u32) -> Cpuid {
    let o = vmcall(R12 | R13 | R14 | R15, EXIT_CPUID as u64, leaf as u64, sub as u64, 0, 0);
    if o.status != 0 {
        return Cpuid { eax: 0, ebx: 0, ecx: 0, edx: 0 };
    }
    Cpuid { eax: o.r12 as u32, ebx: o.r13 as u32, ecx: o.r14 as u32, edx: o.r15 as u32 }
}

/// CPUID leaves only the VMM can answer: asked directly instead of by #VE.
pub fn cpuid_is_vmm_leaf(leaf: u32) -> bool {
    (0x4000_0000..=0x4fff_ffff).contains(&leaf)
}

/// TDG.VP.VMCALL<Instruction.HLT>. `interrupt_blocked` tells the VMM not
/// to wake this vCPU for a pending interrupt.
pub fn hlt(interrupt_blocked: bool) {
    let o = vmcall(R12, EXIT_HLT as u64, interrupt_blocked as u64, 0, 0, 0);
    if o.status != 0 {
        terminate_with(6, format_args!("hlt status={:#x} blocked={}", o.status, interrupt_blocked));
    }
}

fn width_mask(bytes: u64) -> u64 {
    u64::MAX >> (64 - 8 * bytes)
}

/// TDG.VP.VMCALL<Instruction.IO>: `value` is written, or None to read. A
/// failed read gives all ones, as an absent device does.
pub fn io(port: u16, bytes: u64, value: Option<u32>) -> u32 {
    let write = value.is_some();
    let o = vmcall(R12 | R13 | R14 | R15, EXIT_IO as u64, bytes, write as u64, port as u64, value.unwrap_or(0) as u64);
    if write {
        return 0;
    }
    let value = if o.status == 0 { o.r11 } else { u64::MAX };
    (value & width_mask(bytes)) as u32
}

/// TDG.VP.VMCALL<Instruction.RDMSR>.
pub fn read_msr(msr: u32) -> u64 {
    let o = vmcall(R12, EXIT_MSR_READ as u64, msr as u64, 0, 0, 0);
    if o.status != 0 {
        terminate_with(7, format_args!("rdmsr msr={:#x} status={:#x}", msr, o.status));
    }
    o.r11
}

/// TDG.VP.VMCALL<Instruction.WRMSR>.
pub fn write_msr(msr: u32, value: u64) {
    let o = vmcall(R12 | R13, EXIT_MSR_WRITE as u64, msr as u64, value, 0, 0);
    if o.status != 0 {
        // Not the value: it can be private.
        terminate_with(7, format_args!("wrmsr msr={:#x} status={:#x}", msr, o.status));
    }
}

/// TDG.VP.VMCALL<#VE.RequestMMIO> at the shared GPA `gpa`: `write` is the
/// value to store, or None to load. A failed load gives all ones.
pub fn mmio(gpa: u64, bytes: u64, write: Option<u64>) -> u64 {
    let is_write = write.is_some();
    let o = vmcall(R12 | R13 | R14 | R15, EXIT_EPT_VIOLATION as u64, bytes, is_write as u64, gpa, write.unwrap_or(0));
    if is_write {
        return 0;
    }
    let value = if o.status == 0 { o.r11 } else { u64::MAX };
    value & width_mask(bytes)
}

/// TDG.VP.VMCALL<Instruction.WBINVD>.
pub fn wbinvd() {
    let o = vmcall(R12, EXIT_WBINVD as u64, 0, 0, 0, 0);
    if o.status != 0 {
        terminate_with(8, format_args!("wbinvd status={:#x}", o.status));
    }
}

/// TDG.VP.VMCALL<GetQuote> on a shared buffer. Returns the VMCALL status.
pub fn get_quote(shared_gpa: u64, bytes: u64) -> u64 {
    vmcall(R12 | R13, VMCALL_GET_QUOTE, shared_gpa, bytes, 0, 0).status
}

#[repr(C, align(1024))]
struct ReportBuf([u8; TDREPORT_BYTES]);

#[repr(C, align(64))]
struct DataBuf([u64; 8]);

/// Clear a kernel stack buffer that held report material, so that it does
/// not stay behind for a later stack user.
fn scrub<T>(v: &mut T) {
    let p = v as *mut T as *mut u8;
    for i in 0..core::mem::size_of::<T>() {
        unsafe { p.add(i).write_volatile(0) };
    }
    compiler_fence(Ordering::SeqCst);
}

/// TDG.MR.REPORT over `data`, on kernel stack buffers (which are private).
/// On success copies the TDREPORT to `frame`, a private frame's kernel
/// address. Returns the TDX module's status.
pub fn report(frame: u64, data: &[u64; 8]) -> u64 {
    let mut out = ReportBuf([0; TDREPORT_BYTES]);
    let mut input = DataBuf(*data);
    let mut r = Regs {
        rcx: cpu::image_paddr(out.0.as_mut_ptr() as u64),
        rdx: cpu::image_paddr(input.0.as_mut_ptr() as u64),
        ..Regs::default()
    };
    let status = tdcall(TDG_MR_REPORT, &mut r);
    if status == 0 {
        unsafe { core::ptr::copy_nonoverlapping(out.0.as_ptr(), frame as *mut u8, TDREPORT_BYTES) };
    }
    scrub(&mut out);
    scrub(&mut input);
    status
}

/// TDG.MR.RTMR.EXTEND of RTMR `index` with a SHA-384 digest. Returns the
/// TDX module's status.
pub fn extend_rtmr(index: u64, digest: &[u64; 6]) -> u64 {
    let mut input = DataBuf([digest[0], digest[1], digest[2], digest[3], digest[4], digest[5], 0, 0]);
    let mut r = Regs { rcx: cpu::image_paddr(input.0.as_mut_ptr() as u64), rdx: index, ..Regs::default() };
    let status = tdcall(TDG_MR_RTMR_EXTEND, &mut r);
    scrub(&mut input);
    status
}

#[cfg(test)]
mod tests {
    extern crate std;
    use super::*;

    #[test]
    fn the_signature_is_cpuid_21_in_ebx_edx_ecx() {
        let (ebx, edx, ecx) = (0x6574_6e49, 0x5844_546c, 0x2020_2020);
        assert!(is_tdx_signature(0x21, ebx, ecx, edx));
        assert!(!is_tdx_signature(0x20, ebx, ecx, edx));
        assert!(!is_tdx_signature(0x21, ebx, edx, ecx));
        assert!(!is_tdx_signature(0x21, 0, 0, 0));
    }

    #[test]
    fn the_shared_bit_is_the_top_gpa_bit_of_48_and_52_bit_guests() {
        assert_eq!(shared_mask_of(48), Some(1 << 47));
        assert_eq!(shared_mask_of(52), Some(1 << 51));
        for gpaw in [0, 1, 39, 47, 49, 51, 53, 63] {
            assert_eq!(shared_mask_of(gpaw), None, "{gpaw}");
        }
    }

    const S: u64 = 1 << 51;

    #[test]
    fn map_gpa_finishes_on_success_or_a_retry_at_the_end() {
        assert_eq!(map_gpa_step(S, S + 0x4000, 0, 0xdead, 0), MapGpa::Done);
        assert_eq!(map_gpa_step(S, S + 0x4000, VMCALL_RETRY, S + 0x4000, 0), MapGpa::Done);
    }

    #[test]
    fn map_gpa_retry_moves_strictly_forward_and_resets_the_stall_count() {
        assert_eq!(map_gpa_step(S, S + 0x4000, VMCALL_RETRY, S + 0x1000, 7), MapGpa::Continue(S + 0x1000, 0));
    }

    #[test]
    fn map_gpa_rejects_an_r11_out_of_range_or_off_a_page() {
        let (cur, end) = (S + 0x2000, S + 0x4000);
        for r11 in [cur - 0x1000, 0, end + 0x1000, u64::MAX & !0xfff, cur + 1, end - 1, cur + 0x800] {
            assert_eq!(map_gpa_step(cur, end, VMCALL_RETRY, r11, 0), MapGpa::Violation, "{r11:#x}");
        }
    }

    #[test]
    fn map_gpa_without_progress_is_bounded() {
        let (cur, end) = (S, S + 0x4000);
        let mut stalled = 0;
        for _ in 0..MAP_GPA_RETRIES {
            match map_gpa_step(cur, end, VMCALL_RETRY, cur, stalled) {
                MapGpa::Continue(next, s) => {
                    assert_eq!(next, cur);
                    assert_eq!(s, stalled + 1);
                    stalled = s;
                }
                other => panic!("{other:?}"),
            }
        }
        assert_eq!(map_gpa_step(cur, end, VMCALL_RETRY, cur, stalled), MapGpa::Violation);
    }

    #[test]
    fn map_gpa_errors_end_the_guest() {
        for status in [0x8000_0000_0000_0000, 0x8000_0000_0000_0002, 2] {
            assert_eq!(map_gpa_step(S, S + 0x1000, status, S + 0x1000, 0), MapGpa::Violation);
        }
    }

    #[test]
    fn accept_results_follow_the_module_status_class() {
        assert_eq!(accept_result(0, LEVEL_2M), Accepted::Advance);
        assert_eq!(accept_result(PAGE_ALREADY_ACCEPTED, LEVEL_2M), Accepted::Advance);
        assert_eq!(accept_result(PAGE_ALREADY_ACCEPTED | 0x1234, LEVEL_4K), Accepted::Advance);
        assert_eq!(accept_result(PAGE_SIZE_MISMATCH | 1, LEVEL_2M), Accepted::Split);
        // No smaller page to fall back to.
        assert_eq!(accept_result(PAGE_SIZE_MISMATCH, LEVEL_4K), Accepted::Fail);
        assert_eq!(accept_result(OPERAND_BUSY | 0x20, LEVEL_4K), Accepted::Retry);
        assert_eq!(accept_result(0xc000_0100_0000_0000, LEVEL_4K), Accepted::Fail);
    }

    #[test]
    fn sept_ve_must_be_off_unless_the_td_is_a_debug_td() {
        use SeptVe::*;
        let (off, dbg) = (ATTR_SEPT_VE_DISABLE, ATTR_DEBUG);
        // TDX module without the flexible control: the attribute decides.
        assert_eq!(sept_ve_action(off, None, None), Off);
        assert_eq!(sept_ve_action(0, None, None), Refuse);
        assert_eq!(sept_ve_action(dbg, Some(0), None), Keep);
        // With it, TD_CTLS decides whatever the attribute says.
        let flex = Some(CONFIG_FLEXIBLE_PENDING_VE);
        assert_eq!(sept_ve_action(0, flex, Some(TD_CTLS_PENDING_VE_DISABLE)), Off);
        assert_eq!(sept_ve_action(off, flex, Some(0)), Disable);
        assert_eq!(sept_ve_action(0, flex, Some(0)), Disable);
        assert_eq!(sept_ve_action(dbg, flex, Some(0)), Keep);
    }

    fn text(l: &FatalLine) -> &str {
        core::str::from_utf8(&l.buf[..l.len]).unwrap()
    }

    #[test]
    fn a_fatal_line_names_the_reason_and_its_detail() {
        assert_eq!(text(&fatal_line(9, None)), "FL4: TDX fatal (reason 9)\n");
        let l = fatal_line(7, Some(format_args!("rdmsr msr={:#x} status={:#x}", 0xc000_0083u32, 1u64)));
        assert_eq!(text(&l), "FL4: TDX fatal (reason 7): rdmsr msr=0xc0000083 status=0x1\n");
    }

    /// The longest real line fits, and a longer one is cut, with its newline.
    #[test]
    fn a_fatal_line_is_cut_to_fit_without_failing() {
        let m = u64::MAX;
        let l = fatal_line(5, Some(format_args!("map_gpa status={:#x} cur={:#x} end={:#x} r11={:#x} stalled={}", m, m, m, m, u32::MAX)));
        assert!(text(&l).ends_with("stalled=4294967295\n"), "{}", text(&l));
        assert!(l.len <= FATAL_LINE);
        for n in [FATAL_LINE - 40, FATAL_LINE, FATAL_LINE * 3] {
            let long = "x".repeat(n);
            let l = fatal_line(255, Some(format_args!("{long}")));
            assert!(l.len <= FATAL_LINE);
            assert_eq!(l.buf[l.len - 1], b'\n');
        }
        // Many small writes stop at the same place.
        let mut w = FatalLine { buf: [0; FATAL_LINE], len: 0 };
        for _ in 0..FATAL_LINE * 2 {
            write!(w, "y").unwrap();
        }
        assert_eq!(w.len, FATAL_LINE - 1);
    }

    /// The console is the VMM's: the failed WRMSR's line names the MSR and
    /// status, never the value being written.
    #[test]
    fn a_failed_wrmsr_does_not_log_its_value() {
        let src = include_str!("tdx.rs");
        let f = &src[src.find("pub fn write_msr(").unwrap()..];
        let f = &f[..f.find("\n}\n").unwrap()];
        let call = &f[f.find("terminate_with(").unwrap()..];
        assert_eq!(call.lines().next().unwrap(), "terminate_with(7, format_args!(\"wrmsr msr={:#x} status={:#x}\", msr, o.status));");
        const VALUE: u64 = 0x1122_3344_5566_7788;
        let (msr, status) = (0x6e0u32, 0x8000_0000_0000_0000u64);
        let l = fatal_line(7, Some(format_args!("wrmsr msr={:#x} status={:#x}", msr, status)));
        assert!(!text(&l).contains(&std::format!("{VALUE:x}")));
    }

    #[test]
    fn a_failed_ve_logs_only_the_msr_or_leaf_of_a_verified_instruction() {
        const SECRET: u64 = 0x1122_3344_5566_7788;
        assert_eq!(ve_log_operand(EXIT_MSR_WRITE, [0x0f, 0x30], SECRET, 0xc000_0083), Some(0xc000_0083));
        assert_eq!(ve_log_operand(EXIT_MSR_READ, [0x0f, 0x32], SECRET, 0x1b), Some(0x1b));
        assert_eq!(ve_log_operand(EXIT_CPUID, [0x0f, 0xa2], 0x4000_0000, SECRET), Some(0x4000_0000));
        // The exit reason and the instruction must agree.
        assert_eq!(ve_log_operand(EXIT_MSR_WRITE, [0x0f, 0x32], SECRET, SECRET), None);
        assert_eq!(ve_log_operand(EXIT_MSR_READ, [0x48, 0x89], SECRET, SECRET), None);
        assert_eq!(ve_log_operand(EXIT_CPUID, [0x90, 0x90], SECRET, SECRET), None);
        // An EPT violation or anything else names no register.
        assert_eq!(ve_log_operand(EXIT_EPT_VIOLATION, [0x0f, 0x30], SECRET, SECRET), None);
        assert_eq!(ve_log_operand(EXIT_HLT, [0xf4, 0], SECRET, SECRET), None);
    }

    #[test]
    fn only_a_perfmon_td_gets_user_counters() {
        assert!(user_pmc_allowed(ATTR_PERFMON));
        assert!(user_pmc_allowed(ATTR_PERFMON | ATTR_DEBUG));
        assert!(!user_pmc_allowed(0));
        assert!(!user_pmc_allowed(!ATTR_PERFMON));
    }

    #[test]
    fn the_ve_msr_whitelist_is_the_x2apic_and_its_timer() {
        for write in [false, true] {
            for msr in [0x800, 0x80b, 0x830, 0x83e, 0x83f, cpu::msr::TSC_DEADLINE] {
                assert!(virtual_msr(msr, write), "{msr:#x}");
            }
            for msr in [0x7ff, 0x840, 0x8ff, 0x10, 0x48, 0x10a, cpu::msr::EFER, cpu::msr::LSTAR] {
                assert!(!virtual_msr(msr, write), "{msr:#x}");
            }
        }
        assert!(virtual_msr(cpu::msr::APIC_BASE, false));
        assert!(!virtual_msr(cpu::msr::APIC_BASE, true));
    }

    /// Audit (TDX r1, fix 3): only the topology leaves go to the VMM on a
    /// kernel #VE; a #VE on a leaf the TDX module should answer, or any
    /// other, ends the TD.
    #[test]
    fn the_ve_cpuid_whitelist_is_the_topology_leaves() {
        assert!(virtual_cpuid(0x0b));
        assert!(virtual_cpuid(0x1f));
        for leaf in [0, 1, 2, 4, 6, 7, 0xa, 0xd, 0x15, 0x16, 0x1e, 0x20, 0x21, 0x4000_0000, 0x8000_0000, 0x8000_0001, 0x8000_0008, 0x0b00, 0x1f_0000_0b] {
            assert!(!virtual_cpuid(leaf), "{leaf:#x}");
        }
    }

    #[test]
    fn enum_topology_is_its_own_td_ctls_bit() {
        assert_eq!(TD_CTLS_ENUM_TOPOLOGY, 2);
        assert_eq!(TD_CTLS_ENUM_TOPOLOGY & TD_CTLS_PENDING_VE_DISABLE, 0);
    }

    /// Audit (TDX r1, fix 1): each vCPU runs the kernel once, and only a
    /// vCPU of the TD (VCPU_INDEX below NUM_VCPUS) may.
    #[test]
    fn each_vcpu_index_is_claimed_once_and_only_below_num_vcpus() {
        let seen: [AtomicU64; 2] = [const { AtomicU64::new(0) }; 2];
        assert!(claim_vcpu(&seen, 0, 4));
        assert!(claim_vcpu(&seen, 3, 4));
        assert!(!claim_vcpu(&seen, 0, 4), "a second core on vCPU 0");
        assert!(!claim_vcpu(&seen, 3, 4));
        assert!(!claim_vcpu(&seen, 4, 4), "not a vCPU of this TD");
        assert!(!claim_vcpu(&seen, u32::MAX, u64::MAX));
        assert!(claim_vcpu(&seen, 1, 4));
        assert!(claim_vcpu(&seen, 2, 4));
        // Past what the record holds, whatever NUM_VCPUS says.
        assert!(claim_vcpu(&seen, 127, 1 << 20));
        assert!(!claim_vcpu(&seen, 128, 1 << 20));
        assert!(!claim_vcpu(&seen, 0, 0));
        assert_eq!(seen[0].load(Ordering::Relaxed), 0xf);
        assert_eq!(seen[1].load(Ordering::Relaxed), 1 << 63);
        assert_eq!(VCPU_SEEN.len() * 64, MAX_VCPU_INDEX);
    }

    #[test]
    fn vmm_leaves_are_the_hypervisor_range() {
        assert!(cpuid_is_vmm_leaf(0x4000_0000));
        assert!(cpuid_is_vmm_leaf(0x4000_0010));
        assert!(!cpuid_is_vmm_leaf(0x15));
        assert!(!cpuid_is_vmm_leaf(0x8000_0008));
    }

    #[test]
    fn report_buffers_have_the_alignment_tdcall_requires() {
        assert_eq!(core::mem::align_of::<ReportBuf>(), 1024);
        assert_eq!(core::mem::size_of::<ReportBuf>(), 1024);
        assert_eq!(core::mem::align_of::<DataBuf>(), 64);
        assert_eq!(core::mem::size_of::<DataBuf>(), 64);
    }
}
