//! Kernel entry and exit: save the user registers into the current TCB,
//! dispatch to fl4-core, and restore whichever thread is current after.
use crate::kprintln;
use fl4_arch_x86_64::arch::PhysArch;
use fl4_arch_x86_64::{cpu, fpu, percpu};
use fl4_core::layout::{irq, node, reg, tcb as tl};
use fl4_core::machine::Store;
use fl4_core::obj::{node_get, Tcb};
use fl4_core::{debug, sched, syscall};
use fl4_store::PhysStore;

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

pub fn set_ks_base(b: u64) {
    unsafe { KS_BASE = b };
}

pub fn store() -> PhysStore {
    PhysStore { ks_base: unsafe { KS_BASE }, cpu: percpu::cpu_index() as u64 }
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
    w(s, reg::FAULT_IP, f.rip);
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

/// Called by entry.S for every kernel entry.
#[no_mangle]
extern "C" fn fl4_entry(f: &mut Frame) {
    let v = f.vector;
    let mut s = store();
    let mut a = PhysArch;
    if f.cs & 3 == 0 {
        let pc = percpu::get();
        if (VEC_IRQ_MIN..=VEC_SPURIOUS).contains(&v) {
            if pc.polling {
                // take_pending_irq accepted an interrupt: record it and
                // go back with interrupts off so only one is taken.
                if v <= VEC_IRQ_MAX {
                    pc.polled_irq = v - VEC_IRQ_MIN;
                }
                f.rflags &= !RFLAGS_IF;
                return;
            }
            if pc.idle {
                pc.idle = false;
                if v <= VEC_IRQ_MAX {
                    syscall::handle_interrupt_entry(&mut s, &mut a, v - VEC_IRQ_MIN);
                }
                exit(&mut s);
            }
        }
        if v == 2 {
            return;
        }
        kernel_fault(f);
    }
    save_user(&mut s, f);
    trace(f);
    if v == VEC_SYSCALL {
        syscall::handle_syscall(&mut s, &mut a, f.rdx as i64);
    } else if (VEC_IRQ_MIN..=VEC_IRQ_MAX).contains(&v) {
        syscall::handle_interrupt_entry(&mut s, &mut a, v - VEC_IRQ_MIN);
    } else if v == 14 {
        syscall::handle_vm_fault(&mut s, &mut a, cpu::read_cr2(), f.error);
    } else if (v == 1 || v == 3) && fl4_abi::config::HARDWARE_DEBUG_API {
        let dr6 = if v == 1 { cpu::read_dr6() } else { 0 };
        cpu::write_dr6(0xffff_0ff0);
        syscall::handle_debug_exception(&mut s, &mut a, v, dr6);
    } else if v == 2 || v == VEC_SPURIOUS {
        // NMI or spurious interrupt: nothing to do.
    } else if v < 32 {
        syscall::handle_user_exception(&mut s, &mut a, v, f.error);
    } else if v >= VEC_TRAP_MIN {
        syscall::handle_trap_syscall(&mut s, &mut a, v);
    }
    exit(&mut s)
}

/// Leave the kernel to the current thread (or the idle loop).
pub fn exit(s: &mut PhysStore) -> ! {
    let ct = sched::cur_thread(s);
    let core = s.cur_cpu();
    let stack_top = percpu::get().stack_top;
    if ct.0 == node_get(s, core, node::IDLE_THREAD) {
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
