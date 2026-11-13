//! Kernel entry and exit: save the user registers into the current TCB,
//! dispatch to fl4-core, and restore whichever thread is current after.
use crate::kprintln;
use fl4_arch_x86_64::arch::PhysArch;
use fl4_arch_x86_64::{cpu, fpu, percpu};
use fl4_core::layout::{irq, node, reg, tcb as tl};
use fl4_core::machine::Store;
use fl4_core::obj::{node_get, Tcb};
use fl4_core::{debug, sched, syscall};
use fl4_arch_x86_64::arch;
use fl4_store::{tx, Phys, PhysStore};
use fl4_sync::SerialGate;
use fl4_arch_x86_64::smp;

core::arch::global_asm!(include_str!("entry.S"), options(att_syntax));

extern "C" {
    fn fl4_restore_user(regs: u64, stack_top: u64) -> !;
    fn fl4_idle(stack_top: u64) -> !;
}

/// The frame entry.S builds (see there).
#[repr(C)]
pub struct Frame {
    pub r15: u64,
    pub r14: u64,
    pub r13: u64,
    pub r12: u64,
    pub r11: u64,
    pub r10: u64,
    pub r9: u64,
    pub r8: u64,
    pub rbp: u64,
    pub rdi: u64,
    pub rsi: u64,
    pub rdx: u64,
    pub rcx: u64,
    pub rbx: u64,
    pub rax: u64,
    pub vector: u64,
    pub error: u64,
    pub rip: u64,
    pub cs: u64,
    pub rflags: u64,
    pub rsp: u64,
    pub ss: u64,
}

const VEC_SYSCALL: u64 = 0x100;
const VEC_SPURIOUS: u64 = 0xff;
const VEC_TRAP_MIN: u64 = 0xa0;
const VEC_IRQ_MIN: u64 = irq::INT_OFFSET;
const VEC_IRQ_MAX: u64 = irq::MAX + irq::INT_OFFSET;
const RFLAGS_IF: u64 = 1 << 9;
const RFLAGS_TF: u64 = 1 << 8;

static mut KS_BASE: u64 = 0;

/// The serial gate (DESIGN.md §7): kernel entries that cannot run as
/// transactions run holding it, with no transaction running.
pub static GATE: SerialGate = SerialGate::new();

/// Transaction attempts before an entry runs under the serial gate.
const TX_ATTEMPTS: u32 = 4;

pub fn set_ks_base(b: u64) {
    unsafe { KS_BASE = b };
}

/// Direct access to kernel memory (one core, the serial gate, or this
/// core's own thread context).
pub fn store() -> PhysStore {
    PhysStore { ks_base: unsafe { KS_BASE }, cpu: percpu::cpu_index() as u64, tx: false }
}

fn save_user(s: &mut PhysStore, f: &Frame) {
    let t = sched::cur_thread(s);
    let r = t.0 + tl::REGS;
    let w = |s: &mut PhysStore, i: u64, v: u64| s.write(r + i * 8, v);
    w(s, reg::RDI, f.rdi);
    w(s, reg::RSI, f.rsi);
    w(s, reg::RAX, f.rax);
    w(s, reg::RBX, f.rbx);
    w(s, reg::RBP, f.rbp);
    w(s, reg::R12, f.r12);
    w(s, reg::R13, f.r13);
    w(s, reg::R14, f.r14);
    w(s, reg::RDX, f.rdx);
    w(s, reg::R10, f.r10);
    w(s, reg::R8, f.r8);
    w(s, reg::R9, f.r9);
    w(s, reg::R15, f.r15);
    w(s, reg::FLAGS, f.rflags);
    w(s, reg::NEXT_IP, f.rip);
    w(s, reg::ERROR, f.error);
    w(s, reg::RSP, f.rsp);
    // A syscall restarts at the syscall instruction (two bytes long), for
    // when a remote stall cancels the entry before handle_syscall runs.
    w(s, reg::FAULT_IP, if f.vector == VEC_SYSCALL { f.rip.wrapping_sub(2) } else { f.rip });
    w(s, reg::R11, f.r11);
    w(s, reg::RCX, f.rcx);
}

fn kernel_fault(f: &Frame) -> ! {
    kprintln!(
        "rax {:#x} rbx {:#x} rcx {:#x} rdx {:#x} rsi {:#x} rdi {:#x} rbp {:#x}\nr8 {:#x} r9 {:#x} r10 {:#x} r11 {:#x} r12 {:#x} r13 {:#x} r14 {:#x} r15 {:#x}",
        f.rax, f.rbx, f.rcx, f.rdx, f.rsi, f.rdi, f.rbp, f.r8, f.r9, f.r10, f.r11, f.r12, f.r13, f.r14, f.r15
    );
    for p in [f.rdi, f.rsi, f.r9] {
        if p >> 40 == 0xffffff && p & 7 == 0 {
            let w = |i: u64| unsafe { core::ptr::read_volatile((p + 8 * i) as *const u64) };
            kprintln!("[{:#x}] {:#x} {:#x} {:#x} {:#x} {:#x} {:#x} {:#x} {:#x}", p, w(0), w(1), w(2), w(3), w(4), w(5), w(6), w(7));
        }
    }
    panic!(
        "kernel exception {:#x} error {:#x} at {:#x} (cr2 {:#x}, rsp {:#x})",
        f.vector,
        f.error,
        f.rip,
        cpu::read_cr2(),
        f.rsp
    )
}

/// Service a remote call addressed to this core (a stall runs the kernel's
/// stall logic on behalf of the core that holds the gate). Returns whether
/// this core's current thread was stalled.
fn service_remote() -> bool {
    smp::service(|| {
        let mut s = store();
        let mut a = PhysArch;
        fl4_core::smp::stall(&mut s, &mut a);
    })
}

/// Take the serial gate (on a multi-core system), servicing remote calls
/// while waiting. Returns false when a stall cancelled the entry: this core
/// then runs its idle thread, and the entry must not proceed for the thread
/// that made it (which restarts it later).
pub fn lock() -> bool {
    let stalled = core::cell::Cell::new(false);
    if smp::multi() {
        GATE.acquire(percpu::cpu_index() as u64, || {
            if service_remote() {
                stalled.set(true);
            }
        });
        percpu::get().gate_held = true;
    }
    !stalled.get()
}

fn unlock() {
    let pc = percpu::get();
    if pc.gate_held {
        pc.gate_held = false;
        GATE.release();
    }
}

/// Run the kernel's part of an entry (DESIGN.md §7). On one core it runs
/// directly. Otherwise it runs as a transaction, rerun on conflict, and
/// under the serial gate if it cannot run as one or keeps conflicting; the
/// gate is then released by `exit`. `body` must be repeatable: everything
/// it reads or writes goes through the store and Arch it is given. Returns
/// false when a stall cancelled a non-interrupt entry before it ran.
pub fn run_entry(irq: bool, mut body: impl FnMut(&mut PhysStore, &mut PhysArch)) -> bool {
    let mut a = PhysArch;
    let cpu = percpu::cpu_index() as u64;
    if !smp::multi() {
        body(&mut store(), &mut a);
        percpu::get().held_irq = percpu::NO_IRQ;
        return true;
    }
    let stalled = core::cell::Cell::new(false);
    for _ in 0..TX_ATTEMPTS {
        GATE.enter_tx(cpu, || {
            if service_remote() {
                stalled.set(true);
            }
        });
        if stalled.get() && !irq {
            GATE.leave_tx(cpu);
            return false;
        }
        tx::begin(cpu);
        percpu::get().tx = true;
        let mut s = PhysStore { ks_base: unsafe { KS_BASE }, cpu, tx: true };
        body(&mut s, &mut a);
        percpu::get().tx = false;
        let ok = tx::commit(cpu, &Phys);
        let serial = tx::needs_serial(cpu);
        tx::end(cpu);
        GATE.leave_tx(cpu);
        if ok {
            let c = smp::TX_COMMITS.fetch_add(1, core::sync::atomic::Ordering::Relaxed);
            if fl4_abi::config::DEBUG_BUILD && c & 0x3ffff == 0x3ffff {
                arch::print_stats();
            }
            arch::apply_effects();
            percpu::get().held_irq = percpu::NO_IRQ;
            return true;
        }
        smp::TX_ABORTS.fetch_add(1, core::sync::atomic::Ordering::Relaxed);
        arch::discard_effects();
        if serial {
            break;
        }
    }
    smp::SERIAL_ENTRIES.fetch_add(1, core::sync::atomic::Ordering::Relaxed);
    if !lock() && !irq {
        return false;
    }
    body(&mut store(), &mut a);
    percpu::get().held_irq = percpu::NO_IRQ;
    true
}

/// Called by entry.S for every kernel entry.
#[no_mangle]
extern "C" fn fl4_entry(f: &mut Frame) {
    let v = f.vector;
    let irq = (VEC_IRQ_MIN..=VEC_IRQ_MAX).contains(&v);
    if f.cs & 3 == 0 {
        let pc = percpu::get();
        if (VEC_IRQ_MIN..=VEC_SPURIOUS).contains(&v) {
            if pc.polling {
                // take_pending_irq accepted an interrupt: record it and
                // go back with interrupts off so only one is taken. (This
                // core holds the gate, so no remote call is meant for it.)
                if v <= VEC_IRQ_MAX {
                    pc.polled_irq = v - VEC_IRQ_MIN;
                }
                f.rflags &= !RFLAGS_IF;
                return;
            }
            if pc.idle {
                pc.idle = false;
                if v == smp::REMOTE_CALL_VECTOR as u64 {
                    service_remote();
                }
                if irq {
                    run_entry(true, |s, a| syscall::handle_interrupt_entry(s, a, v - VEC_IRQ_MIN));
                }
                exit();
            }
        }
        if v == 2 {
            return;
        }
        kernel_fault(f);
    }
    save_user(&mut store(), f);
    trace(f);
    if v == smp::REMOTE_CALL_VECTOR as u64 {
        service_remote();
    }
    // Machine state the entry reads once, outside the repeatable part.
    let cr2 = if v == 14 { cpu::read_cr2() } else { 0 };
    let dr6 = if v == 1 && fl4_abi::config::HARDWARE_DEBUG_API {
        let d = cpu::read_dr6();
        cpu::write_dr6(0xffff_0ff0);
        d
    } else {
        0
    };
    // An interrupt is handled even if a stall cancelled the entry: it has
    // been accepted and needs its EOI.
    run_entry(irq, |s, a| {
        if v == VEC_SYSCALL {
            syscall::handle_syscall(s, a, f.rdx as i64);
        } else if irq {
            syscall::handle_interrupt_entry(s, a, v - VEC_IRQ_MIN);
        } else if v == 14 {
            syscall::handle_vm_fault(s, a, cr2, f.error);
        } else if (v == 1 || v == 3) && fl4_abi::config::HARDWARE_DEBUG_API {
            syscall::handle_debug_exception(s, a, v, dr6);
        } else if v == 2 || v == VEC_SPURIOUS {
            // NMI or spurious interrupt: nothing to do.
        } else if v < 32 {
            syscall::handle_user_exception(s, a, v, f.error);
        } else if v >= VEC_TRAP_MIN {
            syscall::handle_trap_syscall(s, a, v);
        }
    });
    exit()
}

/// Leave the kernel to the current thread (or the idle loop), giving up
/// the serial gate. What follows touches only this core's thread, whose
/// context no other core changes without stalling this one first.
pub fn exit() -> ! {
    let s = &mut store();
    let ct = sched::cur_thread(s);
    let core = s.cur_cpu();
    let idle = ct.0 == node_get(s, core, node::IDLE_THREAD);
    unlock();
    let stack_top = percpu::get().stack_top;
    if idle {
        percpu::get().idle = true;
        unsafe { fl4_idle(stack_top) }
    }
    fpu::switch_to(ct.0, ct.flags(s) & fl4_abi::consts::tcb_flag::FPU_DISABLED != 0);
    let pc = percpu::get();
    let fs = ct.reg(s, reg::FS_BASE);
    if fs != pc.fs_base {
        cpu::wrmsr(cpu::msr::FS_BASE, fs);
        pc.fs_base = fs;
    }
    let gs = ct.reg(s, reg::GS_BASE);
    if gs != pc.gs_base {
        cpu::wrmsr(cpu::msr::GS_BASE, gs);
        pc.gs_base = gs;
    }
    if fl4_abi::config::HARDWARE_DEBUG_API {
        load_debug_state(s, ct);
    }
    unsafe { fl4_restore_user(ct.0 + tl::REGS, stack_top) }
}

/// Load a thread's breakpoints and single-step flag (seL4
/// `restore_user_debug_context`).
fn load_debug_state(s: &mut PhysStore, t: Tcb) {
    let dr7 = t.debug_reg(s, 5);
    let pc = percpu::get();
    if dr7 & 0xff != 0 || pc.dr_loaded {
        for i in 0..4 {
            cpu::write_dr(i, t.debug_reg(s, i));
        }
        cpu::write_dr7(dr7);
        pc.dr_loaded = dr7 & 0xff != 0;
    }
    if debug::single_step_enabled(s, t) {
        let f = t.reg(s, reg::FLAGS) | RFLAGS_TF;
        t.set_reg(s, reg::FLAGS, f);
    }
}

const TRACE_N: usize = 8192;
static mut TRACE: [[u64; 8]; TRACE_N] = [[0; 8]; TRACE_N];
static mut TRACE_I: usize = 0;

fn trace(f: &Frame) {
    if !fl4_abi::config::DEBUG_BUILD {
        return;
    }
    unsafe {
        let s = store();
        let ct = sched::cur_thread(&s).0;
        let e = [f.vector, f.rip, f.rdi, f.rsi, f.rdx, ct, f.rbx, f.rbp];
        // Collapse loops of period 1 and 2.
        if TRACE_I >= 2 && (TRACE[(TRACE_I - 1) % TRACE_N] == e || TRACE[(TRACE_I - 2) % TRACE_N] == e) {
            return;
        }
        TRACE[TRACE_I % TRACE_N] = e;
        TRACE_I += 1;
    }
}

/// Print the most recent kernel entries (for panics).
pub fn dump_trace() {
    unsafe {
        let n = TRACE_I;
        let start = n.saturating_sub(64);
        for i in start..n {
            let t = TRACE[i % TRACE_N];
            kprintln!("  #{} vec {:#x} rip {:#x} rdi {:#x} rsi {:#x} rdx {:#x} tcb {:#x}", i, t[0], t[1], t[2], t[3], t[4] as i64, t[5]);
        }
    }
}
