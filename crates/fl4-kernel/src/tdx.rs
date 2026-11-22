//! Kernel side of an Intel TDX guest: #VE, and starting the other cores
//! through the ACPI wakeup mailbox.
//!
//! Nothing the VMM says is an address the kernel acts on: #VE information
//! comes from the TDX module, instructions from private memory, and MMIO
//! addresses from the guest's own page tables.
use crate::cvm_mmio::{self, user_next_rip};
use crate::cvm_walk::{self, Access};
use crate::entry::Frame;
use crate::{kprintln, paging};
use core::sync::atomic::{fence, AtomicU16, Ordering};
use fl4_arch_x86_64::tdx::{self as td, VeInfo};
use fl4_arch_x86_64::{cpu, cvm, percpu, timer};
use fl4_core::layout::pptr;

const RFLAGS_IF: u64 = 1 << 9;
const PAGE: u64 = 4096;
const MAILBOX_WAKEUP: u16 = 1;
/// How long firmware may take to acknowledge a wakeup: the VMM schedules
/// the vCPU that polls the mailbox.
const MAILBOX_ACK_US: u64 = 5_000_000;

/// A #VE in the kernel. Emulate only instructions that use virtual
/// hardware, after checking the opcode at a kernel text address: anything
/// else is the VMM's doing or a kernel bug, and ends the guest.
pub fn ve(f: &mut Frame, info: &VeInfo) {
    let (start, end) = paging::text_bounds();
    if f.rip < start || f.rip >= end.saturating_sub(2) {
        td::terminate_with(10, format_args!("kernel #VE {} outside text", info.exit_reason));
    }
    let op = unsafe { (f.rip as *const [u8; 2]).read() };
    let msr = f.rcx as u32;
    let length = match (info.exit_reason, op) {
        (td::EXIT_CPUID, [0x0f, 0xa2]) => {
            let r = td::cpuid(f.rax as u32, f.rcx as u32);
            f.rax = r.eax as u64;
            f.rbx = r.ebx as u64;
            f.rcx = r.ecx as u64;
            f.rdx = r.edx as u64;
            2
        }
        (td::EXIT_MSR_READ, [0x0f, 0x32]) if td::virtual_msr(msr, false) => {
            let value = td::read_msr(msr);
            f.rax = value as u32 as u64;
            f.rdx = value >> 32;
            2
        }
        (td::EXIT_MSR_WRITE, [0x0f, 0x30]) if td::virtual_msr(msr, true) => {
            td::write_msr(msr, (f.rdx << 32) | f.rax as u32 as u64);
            2
        }
        // Only the idle loop's: `sti; hlt`, so the interrupt that should
        // end this halt is still pending, and the handler's IF is clear.
        (td::EXIT_HLT, [0xf4, _]) if crate::entry::in_idle_loop(f.rip) => {
            td::hlt(f.rflags & RFLAGS_IF == 0);
            1
        }
        _ => {
            // The console is the VMM's: no raw registers (`ve_log_operand`).
            match td::ve_log_operand(info.exit_reason, op, f.rax, f.rcx) {
                Some(operand) => kprintln!("FL4: unsupported TDX #VE {} (MSR or leaf {:#x}) at text offset {:#x}", info.exit_reason, operand, f.rip - start),
                None => kprintln!("FL4: unsupported TDX #VE {} at text offset {:#x}", info.exit_reason, f.rip - start),
            }
            // Also if the line above could not get out.
            td::terminate_with(10, format_args!("unsupported #VE {}", info.exit_reason));
        }
    };
    f.rip += length;
}

/// Walk the running thread's tables through their private kernel aliases.
/// With the skim window CR3 is the kernel's by now, so take the thread's
/// from the per-core record.
fn translate(va: u64, access: Access) -> Option<u64> {
    cvm_walk::translate(
        va,
        access,
        percpu::get().cr3.get(),
        cvm::private_mask(),
        cvm::shared_mask(),
        fl4_abi::consts::USER_TOP,
        paging::window_top(),
        |pa| unsafe { (pptr(pa) as *const u64).read_volatile() },
    )
}

/// A #VE in user code, holding the serial gate so that no table being
/// walked goes away. Returns false if it is the thread's own fault.
pub fn user_ve(f: &mut Frame, info: &VeInfo) -> bool {
    match info.exit_reason {
        td::EXIT_CPUID => {
            let rip = f.rip;
            let fetch = |off| {
                let pa = translate(rip.checked_add(off)?, Access::Execute)?;
                Some(unsafe { (pptr(pa) as *const u8).read_volatile() })
            };
            if fetch(0) != Some(0x0f) || fetch(1) != Some(0xa2) {
                return false;
            }
            let Some(next) = user_next_rip(rip, 2) else {
                return false;
            };
            let r = td::cpuid(f.rax as u32, f.rcx as u32);
            f.rax = r.eax as u64;
            f.rbx = r.ebx as u64;
            f.rcx = r.ecx as u64;
            f.rdx = r.edx as u64;
            f.rip = next;
            true
        }
        // The walk requires a shared leaf: a private page the VMM removed
        // is the thread's fault, never an access to the VMM.
        td::EXIT_EPT_VIOLATION => cvm_mmio::user_mmio(f, translate, |pa, bytes, value| {
            td::mmio(pa | cvm::shared_mask(), bytes, value)
        }),
        _ => false,
    }
}

extern "C" {
    static fl4_tdx_ap_trampoline: u8;
    static fl4_tdx_ap_trampoline_end: u8;
    static fl4_tdx_ap_data: u8;
    static fl4_tdx_ap_gdt: u8;
    static fl4_tdx_ap_compat: u8;
    static fl4_tdx_ap_long: u8;
}

/// Offsets in the trampoline's data (ap.S): the far pointers' 32-bit
/// offsets, and the GDT pointer's base after its two limit bytes.
const DATA_TO_COMPAT: usize = 5 * 8;
const DATA_TO_LONG: usize = 6 * 8;
const DATA_GDT_BASE: usize = 7 * 8 + 2;

/// Where a TDX AP starts: the loader's page of code and the firmware's
/// wakeup mailbox.
#[derive(Clone, Copy)]
pub struct Wakeup {
    pub page: u64,
    pub mailbox: u64,
}

/// Copy the AP trampoline to the wakeup page and give it what it needs.
/// `page` and `boot_root` are below 4 GiB: the 32-bit part of the trampoline
/// uses them.
pub fn prepare_wakeup(page: u64, boot_root: u64, efer_nx: bool, entry: u64) {
    assert!(page < 1 << 32 && boot_root < 1 << 32);
    let tramp = core::ptr::addr_of!(fl4_tdx_ap_trampoline);
    let len = core::ptr::addr_of!(fl4_tdx_ap_trampoline_end) as usize - tramp as usize;
    assert!(len <= PAGE as usize);
    let offset = |sym: *const u8| sym as usize - tramp as usize;
    let dst = pptr(page) as *mut u8;
    unsafe {
        core::ptr::write_bytes(dst, 0, PAGE as usize);
        core::ptr::copy_nonoverlapping(tramp, dst, len);
        let d = dst.add(offset(core::ptr::addr_of!(fl4_tdx_ap_data))).cast::<u64>();
        d.write_volatile(boot_root);
        d.add(1).write_volatile(if efer_nx { 1 << 11 } else { 0 });
        d.add(3).write_volatile(entry);
        let at = |sym: *const u8| page + offset(sym) as u64;
        let bytes = d.cast::<u8>();
        bytes.add(DATA_TO_COMPAT).cast::<u32>().write_unaligned(at(core::ptr::addr_of!(fl4_tdx_ap_compat)) as u32);
        bytes.add(DATA_TO_LONG).cast::<u32>().write_unaligned(at(core::ptr::addr_of!(fl4_tdx_ap_long)) as u32);
        bytes.add(DATA_GDT_BASE).cast::<u64>().write_unaligned(at(core::ptr::addr_of!(fl4_tdx_ap_gdt)));
    }
    fence(Ordering::SeqCst);
}

/// Wake core `c`, whose APIC ID is `id`, through the mailbox. One at a time:
/// the trampoline's stack and index are in the shared page.
pub fn start_ap(w: Wakeup, c: usize, id: u32) {
    let data_off = core::ptr::addr_of!(fl4_tdx_ap_data) as usize - core::ptr::addr_of!(fl4_tdx_ap_trampoline) as usize;
    unsafe {
        let d = (pptr(w.page) as *mut u8).add(data_off).cast::<u64>();
        d.add(2).write_volatile(percpu::stack_top(c));
        d.add(4).write_volatile(c as u64);
    }
    let mb = pptr(w.mailbox);
    let command = unsafe { AtomicU16::from_ptr(mb as *mut u16) };
    let deadline = cpu::rdtsc() + timer::us_to_ticks(MAILBOX_ACK_US);
    let wait_idle = || {
        while command.load(Ordering::Acquire) != 0 {
            if cpu::rdtsc() >= deadline {
                crate::fail("TDX AP wakeup mailbox not acknowledged");
            }
            core::hint::spin_loop();
        }
    };
    wait_idle();
    unsafe {
        ((mb + 4) as *mut u32).write_volatile(id);
        ((mb + 8) as *mut u64).write_volatile(w.page);
    }
    // Firmware acts on the command once the fields above are visible.
    command.store(MAILBOX_WAKEUP, Ordering::Release);
    wait_idle();
}

/// The boot core is done with the wakeup page, now ordinary free RAM.
pub fn finish_wakeup(page: u64) {
    unsafe { core::ptr::write_bytes(pptr(page) as *mut u8, 0, PAGE as usize) };
}
