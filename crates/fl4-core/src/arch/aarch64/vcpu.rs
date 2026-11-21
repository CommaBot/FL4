//! AArch64 VCPU object, security sanitization, VGIC/VPPI faults and invocations.

use crate::capability::{Cap, VM_KERNEL_ONLY, VM_READ_WRITE};
use crate::error::{illegal, invalid_arg, invalid_cap, range, truncated, Exc, Fault, KResult, SysError};
use crate::faults;
use crate::layout::{irq, reg, tcb as tl};
use crate::machine::{Arch, Store};
use crate::msg;
use crate::msginfo::MessageInfo;
use crate::obj::{Ntfn, Slot, Tcb, NTFN_ACTIVE, NTFN_IDLE};
use crate::{regs, sched, smp, vspace};
use fl4_abi::consts::{vcpu_reg as vr, vcpu_run_stop, vcpu_state_mask as sm};
use fl4_abi::label;

// 4 KiB VCPU object layout.
pub const TCB: u64 = 0x000;
pub const OWNER_CPU: u64 = 0x008;
pub const VPPI_MASKED: u64 = 0x010;
pub const RUN_CALLER: u64 = 0x018;
pub const RUN_OFFSET: u64 = 0x020;
pub const RUN_OUT_MASK: u64 = 0x028;
pub const REGS: u64 = 0x040;

pub const SCTLR_EL1_DEFAULT: u64 = 0x30d0_0800;
pub const VMPIDR_DEFAULT: u64 = 0x8000_0000;

/// HCR_EL2 bits that must always be 1 when running a guest under VHE.
pub const HCR_FORCED_1: u64 = (1 << 0)  // VM
    | (1 << 1)  // SWIO
    | (1 << 3)  // FMO
    | (1 << 4)  // IMO
    | (1 << 5)  // AMO
    | (1 << 19) // TSC
    | (1 << 20) // TIDCP
    | (1 << 21) // TACR
    | (1 << 31) // RW
    | (1 << 34); // E2H

/// HCR_EL2 bits that a VMM is permitted to toggle for a guest (strict whitelist).
pub const HCR_VMM_ALLOWED: u64 = (1 << 6)  // VF
    | (1 << 7)  // VI
    | (1 << 8)  // VSE
    | (1 << 13) // TWI
    | (1 << 14) // TWE
    | (1 << 18) // TID3
    | (1 << 22) // TSW
    | (1 << 23) // TPC
    | (1 << 24) // TPU
    | (1 << 25) // TTLB
    | (1 << 26) // TVM
    | (1 << 30); // TRVM

/// Enforce mandatory HCR_EL2 bits and strip every bit outside `HCR_VMM_ALLOWED`.
pub fn sanitize_hcr(v: u64) -> u64 {
    (v & HCR_VMM_ALLOWED) | HCR_FORCED_1
}

/// Sanitize `ICH_HCR_EL2` (GICv3) or `GICH_HCR` (GICv2) to documented control/EOIcount bits.
pub fn sanitize_vgic_hcr(val: u64, gic_v3: bool) -> u64 {
    if gic_v3 {
        val & ((0x1f << 27) | (1 << 14) | (1 << 12) | (1 << 11) | (1 << 10) | 0xff)
    } else {
        val & ((0x1f << 27) | 0xff)
    }
}

/// Sanitize a VGIC list register value: always forces `HW = 0`, validates
/// `vINTID`, and masks reserved/host-controlled bits. Returns `None` if the
/// virtual interrupt ID is illegal.
pub fn sanitize_vgic_lr(val: u64, gic_v3: bool) -> Option<u64> {
    if gic_v3 {
        let state = (val >> 62) & 0x3;
        let vintid = val & 0xffff_ffff;
        if state != 0 && vintid > 1019 && vintid < 8192 {
            return None;
        }
        // Keep State[63:62], Group[60], Priority[55:48], EOI[41], vINTID[31:0]; HW[61]=0.
        const MASK_V3: u64 = (0x3 << 62) | (1 << 60) | (0xff << 48) | (1 << 41) | 0xffff_ffff;
        Some(val & MASK_V3)
    } else {
        let state = (val >> 28) & 0x3;
        let vintid = val & 0x3ff;
        if state != 0 && vintid > 1019 {
            return None;
        }
        // Keep Grp1[30], State[29:28], Priority[27:23], EOI[19], CPUID[12:10], vINTID[9:0]; HW[31]=0.
        const MASK_V2: u64 = (1 << 30) | (0x3 << 28) | (0x1f << 23) | (1 << 19) | (0x7 << 10) | 0x3ff;
        Some(val & MASK_V2)
    }
}

pub fn reg_addr(vcpu: u64, idx: u64) -> u64 {
    vcpu.wrapping_add(REGS).wrapping_add(idx.wrapping_mul(8))
}

pub fn reg_get<S: Store>(s: &S, vcpu: u64, idx: u64) -> u64 {
    s.read(reg_addr(vcpu, idx))
}

pub fn reg_set<S: Store>(s: &mut S, vcpu: u64, idx: u64, val: u64) {
    s.write(reg_addr(vcpu, idx), val);
}

pub fn bound<S: Store>(s: &S, t: Tcb) -> u64 {
    s.read(t.0.wrapping_add(tl::VCPU))
}

fn set_bound<S: Store>(s: &mut S, t: Tcb, vcpu: u64) {
    s.write(t.0.wrapping_add(tl::VCPU), vcpu);
}

/// Unused on AArch64 (guests run via `ARMVCPURun` or bound VCPU TCBs, not SysVMEnter).
pub fn enter<S: Store, A: Arch>(_s: &mut S, _a: &mut A, _t: Tcb) {}

/// Before entering a guest via `ARMVCPURun` (or after an interrupt wakes a
/// `TS_RUNNING_VM` caller's bound notification), consume any pending signal
/// and complete the run with `vcpu_run_stop::INTERRUPT`.
pub fn check<S: Store, A: Arch>(s: &mut S, a: &mut A, t: Tcb) {
    if t.state(s) != sched::TS_RUNNING_VM {
        return;
    }
    let v = s.read(t.0.wrapping_add(tl::RUN_VCPU));
    if v == 0 {
        sched::set_thread_state(s, t, sched::TS_RUNNING);
        return;
    }
    let n = Ntfn(t.bound_ntfn(s));
    if n.0 != 0 && n.state(s) == NTFN_ACTIVE {
        let badge = n.badge(s);
        n.set_state(s, NTFN_IDLE);
        complete_run(s, a, t, vcpu_run_stop::INTERRUPT, badge, 0, 0);
    }
}

/// Clear any active `ARMVCPURun` association when `t` is suspended or deleted.
pub fn cancel_run<S: Store, A: Arch>(s: &mut S, _a: &mut A, t: Tcb) {
    let v = s.read(t.0.wrapping_add(tl::RUN_VCPU));
    if v != 0 {
        s.write(v.wrapping_add(RUN_CALLER), 0);
        s.write(t.0.wrapping_add(tl::RUN_VCPU), 0);
    }
}

pub fn revoke_ports<S: Store, A: Arch>(_s: &mut S, _a: &mut A, _owner: u64, _first: u64, _last: u64) {}

/// Initialise a newly retyped 4 KiB VCPU object.
pub fn init<S: Store, A: Arch>(s: &mut S, a: &A, vcpu: u64) {
    s.write(vcpu.wrapping_add(TCB), 0);
    s.write(vcpu.wrapping_add(OWNER_CPU), 0);
    s.write(vcpu.wrapping_add(VPPI_MASKED), 0);
    s.write(vcpu.wrapping_add(RUN_CALLER), 0);
    s.write(vcpu.wrapping_add(RUN_OFFSET), 0);
    s.write(vcpu.wrapping_add(RUN_OUT_MASK), 0);
    reg_set(s, vcpu, vr::SCTLR, SCTLR_EL1_DEFAULT);
    reg_set(s, vcpu, vr::VMPIDR_EL2, VMPIDR_DEFAULT);
    reg_set(s, vcpu, vr::VPIDR_EL2, a.vcpu_midr());
    reg_set(s, vcpu, vr::HCR_EL2, HCR_FORCED_1);
    let gic_v3 = a.vcpu_gic_version() == 3;
    // ICH_HCR_EL2 / GICH_HCR: En (bit 0) | (GICv3: TALL0 bit 11).
    let vgic_hcr = 1 | if gic_v3 { 1 << 11 } else { 0 };
    reg_set(s, vcpu, vr::VGIC_HCR, vgic_hcr);
    reg_set(s, vcpu, vr::VGIC_VTR, a.vcpu_vgic_vtr());
    sync_vgic_elrsr(s, vcpu, num_lrs(a), gic_v3);
}

/// Recompute the cached `VGIC_ELRSR` empty-LR bitmap from the VCPU's in-memory
/// list registers so a `ReadState(VGIC)` before the VCPU ever runs on hardware
/// (e.g. preempted before `switch_to`) never observes a stale `ELRSR`.
fn sync_vgic_elrsr<S: Store>(s: &mut S, vcpu: u64, lrs: u64, gic_v3: bool) {
    let mut elrsr = 0u64;
    let mut i = 0u64;
    while i < lrs {
        let lr = reg_get(s, vcpu, vr::VGIC_LR0.wrapping_add(i));
        let state = if gic_v3 { (lr >> 62) & 0x3 } else { (lr >> 28) & 0x3 };
        if state == 0 {
            elrsr |= 1u64 << i;
        }
        i += 1;
    }
    reg_set(s, vcpu, vr::VGIC_ELRSR, elrsr);
}

fn num_lrs<A: Arch>(a: &A) -> u64 {
    let vtr = a.vcpu_vgic_vtr();
    if vtr == 0 {
        0
    } else {
        (vtr & 0x1f) + 1
    }
}

fn is_readonly_reg(r: u64) -> bool {
    matches!(
        r,
        vr::FAR_EL2 | vr::HPFAR_EL2 | vr::ESR_EL2 | vr::VGIC_VTR | vr::VGIC_MISR | vr::VGIC_EISR | vr::VGIC_ELRSR
    )
}

fn stall_vcpu<S: Store, A: Arch>(s: &mut S, a: &mut A, vcpu: u64) {
    let t = s.read(vcpu.wrapping_add(TCB));
    if t != 0 {
        smp::remote_tcb_stall(s, a, Tcb(t));
    }
    let caller = s.read(vcpu.wrapping_add(RUN_CALLER));
    if caller != 0 {
        smp::remote_tcb_stall(s, a, Tcb(caller));
    }
    a.vcpu_flush(vcpu);
}

fn unbind<S: Store, A: Arch>(s: &mut S, a: &mut A, vcpu: u64) {
    let caller_ptr = s.read(vcpu.wrapping_add(RUN_CALLER));
    if caller_ptr != 0 {
        let caller = Tcb(caller_ptr);
        smp::remote_tcb_stall(s, a, caller);
        if caller.state(s) == sched::TS_RUNNING_VM {
            complete_run(s, a, caller, vcpu_run_stop::INTERRUPT, 0, 0, 0);
        } else {
            s.write(vcpu.wrapping_add(RUN_CALLER), 0);
            s.write(caller_ptr.wrapping_add(tl::RUN_VCPU), 0);
        }
    }
    let t_ptr = s.read(vcpu.wrapping_add(TCB));
    if t_ptr == 0 {
        return;
    }
    let t = Tcb(t_ptr);
    smp::remote_tcb_stall(s, a, t);
    a.vcpu_flush(vcpu);
    s.write(vcpu.wrapping_add(TCB), 0);
    s.write(vcpu.wrapping_add(OWNER_CPU), 0);
    set_bound(s, t, 0);
    // Downgrade detached TCB's SPSR_EL1 back to native EL0t.
    let old_spsr = t.reg(s, reg::SPSR_EL1);
    t.set_reg(s, reg::SPSR_EL1, regs::sanitise(reg::SPSR_EL1, old_spsr));
    if t == sched::cur_thread(s) {
        vspace::set_vm_root(s, a, t);
    }
}

/// Detach any VCPU bound to `t` (called on TCB finalise).
pub fn detach<S: Store, A: Arch>(s: &mut S, a: &mut A, t: Tcb) {
    cancel_run(s, a, t);
    let v = bound(s, t);
    if v != 0 {
        unbind(s, a, v);
    }
}

/// Finalise a VCPU object on cap deletion.
pub fn finalise<S: Store, A: Arch>(s: &mut S, a: &mut A, vcpu: u64) {
    unbind(s, a, vcpu);
    a.vcpu_flush(vcpu);
}

/// Deliver a VGIC maintenance fault to the current VCPU thread (MCS guarded).
pub fn handle_vgic_maintenance<S: Store, A: Arch>(s: &mut S, a: &mut A, eisr: u64) {
    let ct = sched::cur_thread(s);
    if bound(s, ct) == 0 || !sched::is_schedulable(s, ct) || ct.in_queues(s) != 0 {
        return;
    }
    let (idx, idx_valid) = if eisr != 0 {
        (eisr.trailing_zeros() as u64, true)
    } else {
        (0, false)
    };
    faults::handle_fault(s, a, ct, Fault::VgicMaintenance { idx, idx_valid });
}

/// Deliver a virtual PPI fault (PPI 27 vTimer) to the current VCPU thread (MCS guarded).
pub fn handle_vppi_event<S: Store, A: Arch>(s: &mut S, a: &mut A, irq_id: u64) {
    let ct = sched::cur_thread(s);
    let v = bound(s, ct);
    if v == 0 || !sched::is_schedulable(s, ct) || ct.in_queues(s) != 0 {
        return;
    }
    if irq_id == irq::TIMER_ID {
        let masked = s.read(v.wrapping_add(VPPI_MASKED));
        s.write(v.wrapping_add(VPPI_MASKED), masked | 1);
    }
    a.mask_irq(irq::of(irq_id, s.cur_cpu()), true);
    faults::handle_fault(s, a, ct, Fault::VppiEvent { irq: irq_id });
}

fn reply1<S: Store>(s: &mut S, t: Tcb, call: bool, val: u64) {
    if call {
        let buf = msg::lookup_ipc_buffer(s, true, t);
        t.set_reg(s, reg::BADGE, 0);
        let n = msg::set_mr(s, t, buf, 0, val);
        msg::set_msg_info(s, t, MessageInfo::new(0, 0, 0, n));
    }
    sched::set_thread_state(s, t, sched::TS_RUNNING);
}

fn decode_set_tcb<S: Store, A: Arch>(s: &mut S, a: &mut A, vcpu: u64, ex: &[Slot; 3]) -> KResult<()> {
    if ex[0].is_null() {
        return truncated();
    }
    let target = match ex[0].cap(s) {
        Cap::Thread { ptr } => Tcb(ptr),
        _ => return illegal(),
    };
    let ct = sched::cur_thread(s);
    sched::set_thread_state(s, ct, sched::TS_RESTART);
    unbind(s, a, vcpu);
    let old_v = bound(s, target);
    if old_v != 0 {
        unbind(s, a, old_v);
    }
    smp::remote_tcb_stall(s, a, target);
    s.write(vcpu.wrapping_add(TCB), target.0);
    set_bound(s, target, vcpu);
    if target == sched::cur_thread(s) {
        vspace::set_vm_root(s, a, target);
    }
    Ok(())
}

fn decode_inject_irq<S: Store, A: Arch>(s: &mut S, a: &mut A, vcpu: u64, length: u64, buf: u64) -> KResult<()> {
    if length < 1 {
        return truncated();
    }
    let ct = sched::cur_thread(s);
    let mr0 = msg::syscall_arg(s, ct, buf, 0);
    let virq = mr0 & 0xffff;
    let priority = (mr0 >> 16) & 0xff;
    let group = (mr0 >> 24) & 0xff;
    let index = (mr0 >> 32) & 0xff;
    let lrs = num_lrs(a);
    let gic_v3 = a.vcpu_gic_version() == 3;
    if index >= lrs {
        return range(0, lrs.saturating_sub(1));
    }
    if group > 1 {
        return range(0, 1);
    }
    if virq > 1019 && !(gic_v3 && virq >= 8192) {
        return range(0, 1019);
    }
    stall_vcpu(s, a, vcpu);
    let lr_reg = vr::VGIC_LR0.wrapping_add(index);
    let cur = reg_get(s, vcpu, lr_reg);
    let active = if gic_v3 { (cur >> 62) & 0x3 != 0 } else { (cur >> 28) & 0x3 != 0 };
    if active {
        return Err(Exc::Sys(SysError::DeleteFirst));
    }
    // Pending (0b01), EOI = 1, HW = 0.
    let lr = if gic_v3 {
        (1u64 << 62) | ((group & 1) << 60) | ((priority & 0xff) << 48) | (1u64 << 41) | virq
    } else {
        ((group & 1) << 30) | (1u64 << 28) | ((priority & 0x1f) << 23) | (1u64 << 19) | (virq & 0x3ff)
    };
    sched::set_thread_state(s, ct, sched::TS_RESTART);
    reg_set(s, vcpu, lr_reg, lr);
    sync_vgic_elrsr(s, vcpu, lrs, gic_v3);
    Ok(())
}

fn decode_read_reg<S: Store, A: Arch>(s: &mut S, a: &mut A, vcpu: u64, length: u64, call: bool, buf: u64) -> KResult<()> {
    if length < 1 {
        return truncated();
    }
    let ct = sched::cur_thread(s);
    let field = msg::syscall_arg(s, ct, buf, 0);
    if field >= vr::NUM {
        return invalid_arg(0);
    }
    let lrs = num_lrs(a);
    if field >= vr::VGIC_LR0 && field - vr::VGIC_LR0 >= lrs {
        return invalid_arg(0);
    }
    stall_vcpu(s, a, vcpu);
    let gic_v3 = a.vcpu_gic_version() == 3;
    let val = if field == vr::VGIC_VTR {
        a.vcpu_vgic_vtr()
    } else if !gic_v3 && (vr::VGIC_AP1R0..=vr::VGIC_AP1R3).contains(&field) {
        0
    } else {
        reg_get(s, vcpu, field)
    };
    sched::set_thread_state(s, ct, sched::TS_RESTART);
    reply1(s, ct, call, val);
    Ok(())
}

fn decode_write_reg<S: Store, A: Arch>(s: &mut S, a: &mut A, vcpu: u64, length: u64, buf: u64) -> KResult<()> {
    if length < 2 {
        return truncated();
    }
    let ct = sched::cur_thread(s);
    let field = msg::syscall_arg(s, ct, buf, 0);
    let val = msg::syscall_arg(s, ct, buf, 1);
    if field >= vr::NUM || is_readonly_reg(field) {
        return invalid_arg(0);
    }
    let lrs = num_lrs(a);
    let gic_v3 = a.vcpu_gic_version() == 3;
    if field >= vr::VGIC_LR0 {
        if field - vr::VGIC_LR0 >= lrs {
            return invalid_arg(0);
        }
        let Some(san) = sanitize_vgic_lr(val, gic_v3) else {
            return invalid_arg(1);
        };
        stall_vcpu(s, a, vcpu);
        sched::set_thread_state(s, ct, sched::TS_RESTART);
        reg_set(s, vcpu, field, san);
        sync_vgic_elrsr(s, vcpu, lrs, gic_v3);
        return Ok(());
    }
    stall_vcpu(s, a, vcpu);
    sched::set_thread_state(s, ct, sched::TS_RESTART);
    if !gic_v3 && (vr::VGIC_AP1R0..=vr::VGIC_AP1R3).contains(&field) {
        return Ok(());
    }
    let v = if field == vr::HCR_EL2 {
        sanitize_hcr(val)
    } else if field == vr::VGIC_HCR {
        sanitize_vgic_hcr(val, gic_v3)
    } else {
        val
    };
    reg_set(s, vcpu, field, v);
    Ok(())
}

fn decode_ack_vppi<S: Store, A: Arch>(s: &mut S, a: &mut A, vcpu: u64, length: u64, buf: u64) -> KResult<()> {
    if length < 1 {
        return truncated();
    }
    let ct = sched::cur_thread(s);
    let irq_id = msg::syscall_arg(s, ct, buf, 0);
    if irq_id != irq::TIMER_ID {
        return invalid_arg(0);
    }
    stall_vcpu(s, a, vcpu);
    sched::set_thread_state(s, ct, sched::TS_RESTART);
    let masked = s.read(vcpu.wrapping_add(VPPI_MASKED));
    s.write(vcpu.wrapping_add(VPPI_MASKED), masked & !1);
    Ok(())
}

fn validate_vgic_lrs<S: Store>(s: &S, frame: u64, lrs: u64, gic_v3: bool) -> bool {
    let mut i = 0u64;
    while i < lrs {
        let r = vr::VGIC_LR0.wrapping_add(i);
        let val = s.read(frame.wrapping_add(r * 8));
        if sanitize_vgic_lr(val, gic_v3).is_none() {
            return false;
        }
        i += 1;
    }
    true
}

fn copy_reg_range_to_frame<S: Store>(s: &mut S, vcpu: u64, frame: u64, start: u64, end_incl: u64) {
    let mut r = start;
    while r <= end_incl {
        s.write(frame.wrapping_add(r * 8), reg_get(s, vcpu, r));
        r += 1;
    }
}

fn copy_reg_range_from_frame<S: Store>(s: &mut S, vcpu: u64, frame: u64, start: u64, end_incl: u64) {
    let mut r = start;
    while r <= end_incl {
        let val = s.read(frame.wrapping_add(r * 8));
        reg_set(s, vcpu, r, val);
        r += 1;
    }
}

/// Copy selected state groups from `vcpu` (and its bound TCB) into `frame`.
fn read_state_to_frame<S: Store, A: Arch>(s: &mut S, a: &A, vcpu: u64, frame: u64, mask: u64) {
    if mask == 0 {
        return;
    }
    if mask & sm::EL1_SYSREGS != 0 {
        copy_reg_range_to_frame(s, vcpu, frame, 0, vr::CSSELR_EL1);
        copy_reg_range_to_frame(s, vcpu, frame, vr::ACTLR_EL1, vr::MDCCINT_EL1);
    }
    if mask & sm::HYP != 0 {
        s.write(frame.wrapping_add(vr::VMPIDR_EL2 * 8), reg_get(s, vcpu, vr::VMPIDR_EL2));
        s.write(frame.wrapping_add(vr::VDISR_EL2 * 8), reg_get(s, vcpu, vr::VDISR_EL2));
        copy_reg_range_to_frame(s, vcpu, frame, vr::VPIDR_EL2, vr::VSESR_EL2);
        copy_reg_range_to_frame(s, vcpu, frame, vr::FAR_EL2, vr::ESR_EL2);
    }
    if mask & sm::TIMER != 0 {
        copy_reg_range_to_frame(s, vcpu, frame, vr::CNTV_CTL, vr::CNTKCTL_EL1);
        let vppi_addr = frame.wrapping_add((64 + 37) * 8);
        s.write(vppi_addr, s.read(vcpu.wrapping_add(VPPI_MASKED)));
    }
    if mask & sm::VGIC != 0 {
        let lrs = num_lrs(a);
        let gic_v3 = a.vcpu_gic_version() == 3;
        s.write(frame.wrapping_add(vr::VGIC_VTR * 8), a.vcpu_vgic_vtr());
        copy_reg_range_to_frame(s, vcpu, frame, vr::VGIC_HCR, vr::VGIC_AP0R3);
        let mut r = vr::VGIC_AP1R0;
        while r <= vr::VGIC_AP1R3 {
            let val = if gic_v3 { reg_get(s, vcpu, r) } else { 0 };
            s.write(frame.wrapping_add(r * 8), val);
            r += 1;
        }
        let mut i = 0u64;
        while i < 16 {
            let r = vr::VGIC_LR0.wrapping_add(i);
            let val = if i < lrs { reg_get(s, vcpu, r) } else { 0 };
            s.write(frame.wrapping_add(r * 8), val);
            i += 1;
        }
    }
    if mask & sm::GPRS != 0 {
        let gprs_base = frame.wrapping_add(64 * 8);
        let t_ptr = s.read(vcpu.wrapping_add(TCB));
        let mut i = 0u64;
        while i < reg::COUNT {
            let v = if t_ptr != 0 { Tcb(t_ptr).reg(s, i) } else { 0 };
            s.write(gprs_base.wrapping_add(i * 8), v);
            i += 1;
        }
    }
}

/// Copy selected state groups from `frame` into `vcpu` (and its bound TCB).
/// Callers must have validated LRs via `validate_vgic_lrs` when `mask & sm::VGIC != 0`.
fn write_state_from_frame<S: Store, A: Arch>(s: &mut S, a: &A, vcpu: u64, frame: u64, mask: u64) {
    if mask == 0 {
        return;
    }
    if mask & sm::EL1_SYSREGS != 0 {
        copy_reg_range_from_frame(s, vcpu, frame, 0, vr::CSSELR_EL1);
        copy_reg_range_from_frame(s, vcpu, frame, vr::ACTLR_EL1, vr::MDCCINT_EL1);
    }
    if mask & sm::HYP != 0 {
        reg_set(s, vcpu, vr::VMPIDR_EL2, s.read(frame.wrapping_add(vr::VMPIDR_EL2 * 8)));
        reg_set(s, vcpu, vr::VDISR_EL2, s.read(frame.wrapping_add(vr::VDISR_EL2 * 8)));
        reg_set(s, vcpu, vr::VPIDR_EL2, s.read(frame.wrapping_add(vr::VPIDR_EL2 * 8)));
        reg_set(s, vcpu, vr::HCR_EL2, sanitize_hcr(s.read(frame.wrapping_add(vr::HCR_EL2 * 8))));
        reg_set(s, vcpu, vr::VSESR_EL2, s.read(frame.wrapping_add(vr::VSESR_EL2 * 8)));
    }
    if mask & sm::TIMER != 0 {
        copy_reg_range_from_frame(s, vcpu, frame, vr::CNTV_CTL, vr::CNTKCTL_EL1);
        let vppi_addr = frame.wrapping_add((64 + 37) * 8);
        let m = s.read(vppi_addr) & 1;
        s.write(vcpu.wrapping_add(VPPI_MASKED), m);
    }
    if mask & sm::VGIC != 0 {
        let lrs = num_lrs(a);
        let gic_v3 = a.vcpu_gic_version() == 3;
        reg_set(s, vcpu, vr::VGIC_HCR, sanitize_vgic_hcr(s.read(frame.wrapping_add(vr::VGIC_HCR * 8)), gic_v3));
        reg_set(s, vcpu, vr::VGIC_VMCR, s.read(frame.wrapping_add(vr::VGIC_VMCR * 8)));
        copy_reg_range_from_frame(s, vcpu, frame, vr::VGIC_AP0R0, vr::VGIC_AP0R3);
        if gic_v3 {
            copy_reg_range_from_frame(s, vcpu, frame, vr::VGIC_AP1R0, vr::VGIC_AP1R3);
        }
        let mut i = 0u64;
        while i < lrs {
            let r = vr::VGIC_LR0.wrapping_add(i);
            let val = s.read(frame.wrapping_add(r * 8));
            if let Some(san) = sanitize_vgic_lr(val, gic_v3) {
                reg_set(s, vcpu, r, san);
            }
            i += 1;
        }
        sync_vgic_elrsr(s, vcpu, lrs, gic_v3);
        reg_set(s, vcpu, vr::VGIC_EISR, 0);
        reg_set(s, vcpu, vr::VGIC_MISR, 0);
    }
    if mask & sm::GPRS != 0 {
        let gprs_base = frame.wrapping_add(64 * 8);
        let t_ptr = s.read(vcpu.wrapping_add(TCB));
        if t_ptr != 0 {
            let t = Tcb(t_ptr);
            let mut i = 0u64;
            while i < reg::COUNT {
                let v = s.read(gprs_base.wrapping_add(i * 8));
                let v = if i == reg::SPSR_EL1 { regs::sanitise_vcpu_spsr(v) } else { v };
                t.set_reg(s, i, v);
                i += 1;
            }
            let pc = t.reg(s, reg::ELR_EL1);
            t.set_reg(s, reg::FAULT_IP, pc);
        }
    }
}

fn decode_state_transfer<S: Store, A: Arch>(
    s: &mut S,
    a: &mut A,
    vcpu: u64,
    length: u64,
    buf: u64,
    ex: &[Slot; 3],
    to_frame: bool,
) -> KResult<()> {
    if length < 2 || ex[0].is_null() {
        return truncated();
    }
    let ct = sched::cur_thread(s);
    let offset = msg::syscall_arg(s, ct, buf, 0);
    let mask = msg::syscall_arg(s, ct, buf, 1);
    if mask & !sm::ALL != 0 {
        return invalid_arg(1);
    }
    let (base, size) = match ex[0].cap(s) {
        Cap::Frame { ptr, size, rights, is_device, .. } => {
            if is_device || rights == VM_KERNEL_ONLY || (to_frame && rights != VM_READ_WRITE) {
                return invalid_cap(1);
            }
            (ptr, 1u64 << (size.bits() & 63))
        }
        _ => return invalid_cap(1),
    };
    if offset & 63 != 0 || offset >= size || size - offset < sm::SIZE {
        return invalid_arg(0);
    }
    let frame = base.wrapping_add(offset);
    let lrs = num_lrs(a);
    let gic_v3 = a.vcpu_gic_version() == 3;
    // Validate LRs before mutating state on WriteState.
    if !to_frame && mask & sm::VGIC != 0 && !validate_vgic_lrs(s, frame, lrs, gic_v3) {
        return invalid_arg(1);
    }
    stall_vcpu(s, a, vcpu);
    sched::set_thread_state(s, ct, sched::TS_RESTART);
    if to_frame {
        read_state_to_frame(s, a, vcpu, frame, mask);
    } else {
        write_state_from_frame(s, a, vcpu, frame, mask);
    }
    Ok(())
}

/// Complete an in-flight `ARMVCPURun` on `ct`, syncing `out_mask` back into
/// `ct`'s IPC buffer frame and returning `(stop, w1, w2, w3)` in `MR0..MR3`.
pub fn complete_run<S: Store, A: Arch>(
    s: &mut S,
    a: &mut A,
    ct: Tcb,
    stop: u64,
    w1: u64,
    w2: u64,
    w3: u64,
) {
    let vcpu = s.read(ct.0.wrapping_add(tl::RUN_VCPU));
    if vcpu == 0 {
        return;
    }
    a.vcpu_flush(vcpu);
    let offset = s.read(vcpu.wrapping_add(RUN_OFFSET));
    let out_mask = s.read(vcpu.wrapping_add(RUN_OUT_MASK));
    if out_mask != 0 {
        if let Cap::Frame { ptr, size, rights, is_device, .. } = ct.slot(tl::SLOT_BUFFER).cap(s) {
            let sz = 1u64 << (size.bits() & 63);
            if !is_device && rights == VM_READ_WRITE && offset & 63 == 0 && offset < sz && sz - offset >= sm::SIZE {
                read_state_to_frame(s, a, vcpu, ptr.wrapping_add(offset), out_mask);
            }
        }
    }
    s.write(vcpu.wrapping_add(RUN_CALLER), 0);
    s.write(ct.0.wrapping_add(tl::RUN_VCPU), 0);
    ct.set_reg(s, reg::BADGE, 0);
    ct.set_reg(s, msg::msg_register(0), stop);
    ct.set_reg(s, msg::msg_register(1), w1);
    ct.set_reg(s, msg::msg_register(2), w2);
    ct.set_reg(s, msg::msg_register(3), w3);
    msg::set_msg_info(s, ct, MessageInfo::new(0, 0, 0, 4));
    sched::set_thread_state(s, ct, sched::TS_RUNNING);
}

fn decode_run<S: Store, A: Arch>(s: &mut S, a: &mut A, vcpu: u64, length: u64, call: bool, buf: u64) -> KResult<()> {
    if !call {
        return illegal();
    }
    if length < 3 {
        return truncated();
    }
    let ct = sched::cur_thread(s);
    let offset = msg::syscall_arg(s, ct, buf, 0);
    let in_mask = msg::syscall_arg(s, ct, buf, 1);
    let out_mask = msg::syscall_arg(s, ct, buf, 2);
    if in_mask & !sm::ALL != 0 {
        return invalid_arg(1);
    }
    if out_mask & !sm::ALL != 0 {
        return invalid_arg(2);
    }
    let (base, size) = match ct.slot(tl::SLOT_BUFFER).cap(s) {
        Cap::Frame { ptr, size, rights, is_device, .. } => {
            if is_device || rights != VM_READ_WRITE {
                return illegal();
            }
            (ptr, 1u64 << (size.bits() & 63))
        }
        _ => return illegal(),
    };
    if offset & 63 != 0 || offset >= size || size - offset < sm::SIZE {
        return invalid_arg(0);
    }
    let v_tcb = s.read(vcpu.wrapping_add(TCB));
    if v_tcb == 0 || v_tcb == ct.0 {
        return illegal();
    }
    if s.read(vcpu.wrapping_add(RUN_CALLER)) != 0 {
        return Err(Exc::Sys(SysError::DeleteFirst));
    }
    let frame = base.wrapping_add(offset);
    let lrs = num_lrs(a);
    let gic_v3 = a.vcpu_gic_version() == 3;
    if in_mask & sm::VGIC != 0 && !validate_vgic_lrs(s, frame, lrs, gic_v3) {
        return invalid_arg(1);
    }
    stall_vcpu(s, a, vcpu);
    let me = s.cur_cpu().wrapping_add(1);
    let prev = s.read(vcpu.wrapping_add(OWNER_CPU));
    if prev != 0 && prev != me {
        a.fpu_flush(v_tcb);
        a.fpu_release(v_tcb);
    }
    s.write(vcpu.wrapping_add(OWNER_CPU), me);
    write_state_from_frame(s, a, vcpu, frame, in_mask);
    s.write(vcpu.wrapping_add(RUN_CALLER), ct.0);
    s.write(vcpu.wrapping_add(RUN_OFFSET), offset);
    s.write(vcpu.wrapping_add(RUN_OUT_MASK), out_mask);
    s.write(ct.0.wrapping_add(tl::RUN_VCPU), vcpu);
    vspace::set_stage2_root(s, a, Tcb(v_tcb));
    sched::set_thread_state(s, ct, sched::TS_RUNNING_VM);
    check(s, a, ct);
    Ok(())
}

/// Dispatch `seL4_ARM_VCPU` invocations.
#[allow(clippy::too_many_arguments)]
pub fn decode<S: Store, A: Arch>(
    s: &mut S,
    a: &mut A,
    lbl: u64,
    length: u64,
    vcpu: u64,
    call: bool,
    buf: u64,
    ex: &[Slot; 3],
) -> KResult<()> {
    if lbl == label::ARMVCPUSetTCB {
        decode_set_tcb(s, a, vcpu, ex)
    } else if lbl == label::ARMVCPUInjectIRQ {
        decode_inject_irq(s, a, vcpu, length, buf)
    } else if lbl == label::ARMVCPUReadReg {
        decode_read_reg(s, a, vcpu, length, call, buf)
    } else if lbl == label::ARMVCPUWriteReg {
        decode_write_reg(s, a, vcpu, length, buf)
    } else if lbl == label::ARMVCPUAckVPPI {
        decode_ack_vppi(s, a, vcpu, length, buf)
    } else if lbl == label::ARMVCPUReadState {
        decode_state_transfer(s, a, vcpu, length, buf, ex, true)
    } else if lbl == label::ARMVCPUWriteState {
        decode_state_transfer(s, a, vcpu, length, buf, ex, false)
    } else if lbl == label::ARMVCPURun {
        decode_run(s, a, vcpu, length, call, buf)
    } else {
        illegal()
    }
}

#[cfg(test)]
mod tests {
    extern crate std;
    use super::*;
    use std::collections::BTreeMap;

    struct Mem(BTreeMap<u64, u64>);
    impl Store for Mem {
        fn read(&self, a: u64) -> u64 { *self.0.get(&a).unwrap_or(&0) }
        fn write(&mut self, a: u64, v: u64) { self.0.insert(a, v); }
        fn zero(&mut self, a: u64, len: u64) { for i in (0..len).step_by(8) { self.write(a + i, 0); } }
        fn clear_free(&mut self, a: u64, len: u64) { self.zero(a, len) }
        fn ks_base(&self) -> u64 { 0x10_0000 }
        fn cur_cpu(&self) -> u64 { 0 }
    }

    struct DummyArch;
    impl Arch for DummyArch {
        fn now(&mut self) -> u64 { 0 }
        fn set_deadline(&mut self, _: u64) {}
        fn us_to_ticks(&self, x: u64) -> u64 { x }
        fn ticks_to_us(&self, x: u64) -> u64 { x }
        fn max_us(&self) -> u64 { u64::MAX }
        fn kernel_wcet_ticks(&self) -> u64 { 1 }
        fn irq_pending(&mut self) -> bool { false }
        fn take_pending_irq(&mut self) -> u64 { u64::MAX }
        fn mask_irq(&mut self, _: u64, _: bool) {}
        fn ack_irq(&mut self, _: u64) {}
        fn set_vspace(&mut self, _: u64, _: u64) {}
        fn invalidate_page(&mut self, _: u64, _: u64) {}
        fn invalidate_asid(&mut self, _: u64) {}
        fn invalidate_page_structures(&mut self, _: u64) {}
        fn ioapic_map(&mut self, _: u64, _: u64, _: u64, _: u64, _: u64) -> bool { false }
        fn ioapic_map_remapped(&mut self, _: u64, _: u64, _: u64, _: u64, _: u64, _: u64) -> bool { false }
        fn num_ioapics(&self) -> u64 { 0 }
        fn ioapic_pins(&self, _: u64) -> u64 { 0 }
        fn port_in(&mut self, _: u64, _: u64) -> u64 { 0 }
        fn port_out(&mut self, _: u64, _: u64, _: u64) {}
        fn fpu_flush(&mut self, _: u64) {}
        fn fpu_sanitise(&mut self, _: u64) {}
        fn fpu_reload(&mut self, _: u64) {}
        fn fpu_release(&mut self, _: u64) {}
        fn remote_stall(&mut self, _: u64) {}
        fn send_reschedule(&mut self, _: u64) {}
        fn cache_op(&mut self, _: u64, _: u64, _: u64, _: u64, _: u64, _: u64) {}
        fn hw_access_flag(&self) -> bool { true }
        fn max_spi(&self) -> u64 { 0 }
        fn configure_irq(&mut self, _: u64, _: bool, _: u64) {}
        fn putc(&mut self, _: u64) {}
        fn get_char(&mut self) -> u64 { 0 }
        fn halt(&mut self) {}
    }

    #[test]
    fn hcr_sanitization_enforces_forced_and_strips_forbidden() {
        assert_eq!(sanitize_hcr(0), HCR_FORCED_1);
        assert_ne!(HCR_FORCED_1 & (1 << 20), 0); // TIDCP
        // Hostile bits outside whitelist: TGE(27), DC(12), CD(32), ID(33), AT(44), FWB(46), ATA(56), NV*(42,43,45).
        let disallowed = (1 << 12) | (1 << 27) | (1 << 32) | (1 << 33) | (1 << 40) | (1 << 41)
            | (1 << 42) | (1 << 43) | (1 << 44) | (1 << 45) | (1 << 46) | (1 << 56);
        let hostile = disallowed | (1 << 13) | (1 << 18); // TWI + TID3 + disallowed
        let out = sanitize_hcr(hostile);
        assert_eq!(out & HCR_FORCED_1, HCR_FORCED_1);
        assert_eq!(out & disallowed, 0);
        assert_ne!(out & (1 << 13), 0);
        assert_ne!(out & (1 << 18), 0);
        // VGIC_HCR sanitization strips reserved bits on both GICv3 and GICv2.
        assert_eq!(sanitize_vgic_hcr(u64::MAX, true), (0x1f << 27) | (1 << 14) | (1 << 12) | (1 << 11) | (1 << 10) | 0xff);
        assert_eq!(sanitize_vgic_hcr(u64::MAX, false), (0x1f << 27) | 0xff);
    }

    #[test]
    fn vgic_lr_sanitization_gicv2_and_gicv3() {
        // GICv3: HW bit 61 always cleared; LPIs (>= 8192) allowed; 1020..=8191 rejected.
        let lr3 = (1u64 << 62) | (1 << 61) | (1 << 60) | (0xa0 << 48) | (1 << 41) | 33;
        let san3 = sanitize_vgic_lr(lr3, true).unwrap();
        assert_eq!(san3 & (1 << 61), 0);
        assert_eq!(san3 & 0xffff_ffff, 33);
        let lpi = (1u64 << 62) | (1 << 60) | 8192;
        assert_eq!(sanitize_vgic_lr(lpi, true).unwrap() & 0xffff_ffff, 8192);
        assert!(sanitize_vgic_lr((1u64 << 62) | 1020, true).is_none());
        assert!(sanitize_vgic_lr((1u64 << 62) | 8191, true).is_none());
        // GICv2: HW bit 31 always cleared; > 1019 rejected.
        let lr2 = (1u64 << 31) | (1 << 30) | (1 << 28) | (0x10 << 23) | (1 << 19) | 40;
        let san2 = sanitize_vgic_lr(lr2, false).unwrap();
        assert_eq!(san2 & (1 << 31), 0);
        assert_eq!(san2 & 0x3ff, 40);
        assert!(sanitize_vgic_lr((1u64 << 28) | 1020, false).is_none());
    }

    #[test]
    fn spsr_sanitization_and_detach_downgrades_to_el0t() {
        // VCPU allows EL0t (0), EL1t (4), EL1h (5); forces EL2 (8/9), EL3 (12/13), AArch32 (0x10) to EL1h (5).
        assert_eq!(regs::sanitise_vcpu_spsr(0x0) & 0x1f, 0x0);
        assert_eq!(regs::sanitise_vcpu_spsr(0x4) & 0x1f, 0x4);
        assert_eq!(regs::sanitise_vcpu_spsr(0x5) & 0x1f, 0x5);
        for bad in [0x8u64, 0x9, 0xc, 0xd, 0x10, 0x13] {
            assert_eq!(regs::sanitise_vcpu_spsr(bad) & 0x1f, 0x5, "bad mode {bad:#x}");
        }
        // Detaching a VCPU downgrades the TCB's SPSR_EL1 from EL1h back to EL0t.
        let mut s = Mem(BTreeMap::new());
        let mut a = DummyArch;
        let t = Tcb(0x20_0000);
        let v = 0x30_0000;
        s.write(v + TCB, t.0);
        set_bound(&mut s, t, v);
        let spsr = regs::sanitise_for_tcb(&s, t, reg::SPSR_EL1, 0x3c5);
        t.set_reg(&mut s, reg::SPSR_EL1, spsr);
        assert_eq!(t.reg(&s, reg::SPSR_EL1) & 0x1f, 0x5);
        detach(&mut s, &mut a, t);
        assert_eq!(bound(&s, t), 0);
        assert_eq!(t.reg(&s, reg::SPSR_EL1) & 0x1f, 0x0);
        assert_eq!(t.reg(&s, reg::SPSR_EL1), regs::PSTATE_USER);
    }

    struct VgicArch {
        gic_v3: bool,
        lrs: u64,
        fpu_flushed: std::vec::Vec<u64>,
        fpu_released: std::vec::Vec<u64>,
    }
    impl VgicArch {
        fn new(gic_v3: bool, lrs: u64) -> Self {
            Self { gic_v3, lrs, fpu_flushed: std::vec::Vec::new(), fpu_released: std::vec::Vec::new() }
        }
    }
    impl Arch for VgicArch {
        fn now(&mut self) -> u64 { 0 }
        fn set_deadline(&mut self, _: u64) {}
        fn us_to_ticks(&self, x: u64) -> u64 { x }
        fn ticks_to_us(&self, x: u64) -> u64 { x }
        fn max_us(&self) -> u64 { u64::MAX }
        fn kernel_wcet_ticks(&self) -> u64 { 1 }
        fn irq_pending(&mut self) -> bool { false }
        fn take_pending_irq(&mut self) -> u64 { u64::MAX }
        fn mask_irq(&mut self, _: u64, _: bool) {}
        fn ack_irq(&mut self, _: u64) {}
        fn set_vspace(&mut self, _: u64, _: u64) {}
        fn invalidate_page(&mut self, _: u64, _: u64) {}
        fn invalidate_asid(&mut self, _: u64) {}
        fn invalidate_page_structures(&mut self, _: u64) {}
        fn ioapic_map(&mut self, _: u64, _: u64, _: u64, _: u64, _: u64) -> bool { false }
        fn ioapic_map_remapped(&mut self, _: u64, _: u64, _: u64, _: u64, _: u64, _: u64) -> bool { false }
        fn num_ioapics(&self) -> u64 { 0 }
        fn ioapic_pins(&self, _: u64) -> u64 { 0 }
        fn port_in(&mut self, _: u64, _: u64) -> u64 { 0 }
        fn port_out(&mut self, _: u64, _: u64, _: u64) {}
        fn fpu_flush(&mut self, t: u64) { self.fpu_flushed.push(t); }
        fn fpu_sanitise(&mut self, _: u64) {}
        fn fpu_reload(&mut self, _: u64) {}
        fn fpu_release(&mut self, t: u64) { self.fpu_released.push(t); }
        fn remote_stall(&mut self, _: u64) {}
        fn send_reschedule(&mut self, _: u64) {}
        fn cache_op(&mut self, _: u64, _: u64, _: u64, _: u64, _: u64, _: u64) {}
        fn hw_access_flag(&self) -> bool { true }
        fn max_spi(&self) -> u64 { 0 }
        fn configure_irq(&mut self, _: u64, _: bool, _: u64) {}
        fn vcpu_vgic_vtr(&self) -> u64 { self.lrs - 1 }
        fn vcpu_gic_version(&self) -> u64 { if self.gic_v3 { 3 } else { 2 } }
        fn putc(&mut self, _: u64) {}
        fn get_char(&mut self) -> u64 { 0 }
        fn halt(&mut self) {}
    }

    #[test]
    fn vgic_elrsr_synced_and_eisr_misr_cleared_without_hw_save() {
        use crate::capability::FrameSize;
        use crate::layout::node;
        use crate::obj::node_set;

        for gic_v3 in [true, false] {
            let mut s = Mem(BTreeMap::new());
            let mut a = VgicArch::new(gic_v3, 4);
            let ct = Tcb(0x20_0000);
            node_set(&mut s, 0, node::CUR_THREAD, ct.0);
            let v = 0x30_0000;
            let frame = 0x40_0000;
            let slot = Slot(0x50_0000);
            slot.set_cap(&mut s, Cap::Frame {
                ptr: frame,
                size: FrameSize::Small,
                rights: VM_READ_WRITE,
                is_device: false,
                mapped: false,
                is_ept: false,
                asid: 0,
                vaddr: 0,
            });
            let ex = [slot, Slot(0), Slot(0)];

            // 1. init sets ELRSR = 0xf (all 4 LRs empty).
            init(&mut s, &a, v);
            assert_eq!(reg_get(&s, v, vr::VGIC_ELRSR), 0xf);

            // 2. InjectIRQ into LR0 -> bit 0 cleared (ELRSR == 0xe).
            let mr0 = 40u64 | (0x10 << 16) | (1 << 24) | (0 << 32);
            ct.set_reg(&mut s, msg::msg_register(0), mr0);
            assert!(decode_inject_irq(&mut s, &mut a, v, 1, 0).is_ok());
            assert_eq!(reg_get(&s, v, vr::VGIC_ELRSR), 0xe);

            // 3. WriteRegs(VGIC_LR0, 0) -> 0xf; WriteRegs(VGIC_LR0 + 2, pending) -> 0xb.
            ct.set_reg(&mut s, msg::msg_register(0), vr::VGIC_LR0);
            ct.set_reg(&mut s, msg::msg_register(1), 0);
            assert!(decode_write_reg(&mut s, &mut a, v, 2, 0).is_ok());
            assert_eq!(reg_get(&s, v, vr::VGIC_ELRSR), 0xf);

            let pending_lr = if gic_v3 {
                (1u64 << 62) | (1 << 60) | (0x80 << 48) | (1 << 41) | 40
            } else {
                (1u64 << 30) | (1 << 28) | (0x10 << 23) | (1 << 19) | 40
            };
            ct.set_reg(&mut s, msg::msg_register(0), vr::VGIC_LR0 + 2);
            ct.set_reg(&mut s, msg::msg_register(1), pending_lr);
            assert!(decode_write_reg(&mut s, &mut a, v, 2, 0).is_ok());
            assert_eq!(reg_get(&s, v, vr::VGIC_ELRSR), 0xb);

            // 4. WriteState(VGIC) with pending LR0+LR3 and stale EISR/MISR in memory ->
            //    immediate ReadState(VGIC) (no hw save) sees ELRSR == 0x6 and EISR == MISR == 0.
            reg_set(&mut s, v, vr::VGIC_EISR, 0x1);
            reg_set(&mut s, v, vr::VGIC_MISR, 0x3);
            s.write(frame + vr::VGIC_LR0 * 8, pending_lr);
            s.write(frame + (vr::VGIC_LR0 + 1) * 8, 0);
            s.write(frame + (vr::VGIC_LR0 + 2) * 8, 0);
            s.write(frame + (vr::VGIC_LR0 + 3) * 8, pending_lr);
            ct.set_reg(&mut s, msg::msg_register(0), 0);
            ct.set_reg(&mut s, msg::msg_register(1), sm::VGIC);
            assert!(decode_state_transfer(&mut s, &mut a, v, 2, 0, &ex, false).is_ok());
            assert!(decode_state_transfer(&mut s, &mut a, v, 2, 0, &ex, true).is_ok());
            assert_eq!(s.read(frame + vr::VGIC_ELRSR * 8), 0x6);
            assert_eq!(s.read(frame + vr::VGIC_EISR * 8), 0);
            assert_eq!(s.read(frame + vr::VGIC_MISR * 8), 0);
        }
    }

    #[test]
    fn arm_vcpu_run_exits_pending_ntfn_lifecycle_and_validation() {
        use crate::capability::{FrameSize, VM_READ_ONLY};
        use crate::layout::node;
        use crate::obj::node_set;

        struct CpuMem {
            mem: BTreeMap<u64, u64>,
            cpu: u64,
        }
        impl Store for CpuMem {
            fn read(&self, a: u64) -> u64 { *self.mem.get(&a).unwrap_or(&0) }
            fn write(&mut self, a: u64, v: u64) { self.mem.insert(a, v); }
            fn zero(&mut self, a: u64, len: u64) { for i in (0..len).step_by(8) { self.write(a + i, 0); } }
            fn clear_free(&mut self, a: u64, len: u64) { self.zero(a, len) }
            fn ks_base(&self) -> u64 { 0x10_0000 }
            fn cur_cpu(&self) -> u64 { self.cpu }
        }

        let mut s = CpuMem { mem: BTreeMap::new(), cpu: 0 };
        let mut a = VgicArch::new(true, 4);
        let ct = Tcb(0x20_0000);
        let gtcb = Tcb(0x21_0000);
        let v = 0x30_0000;
        let ipc_frame = 0x40_0000;
        let ntfn = Ntfn(0x50_0000);
        let ex = [Slot(0), Slot(0), Slot(0)];

        node_set(&mut s, 0, node::CUR_THREAD, ct.0);
        init(&mut s, &a, v);
        s.write(v + TCB, gtcb.0);
        set_bound(&mut s, gtcb, v);
        ct.slot(tl::SLOT_BUFFER).set_cap(&mut s, Cap::Frame {
            ptr: ipc_frame,
            size: FrameSize::Small,
            rights: VM_READ_WRITE,
            is_device: false,
            mapped: true,
            is_ept: false,
            asid: 1,
            vaddr: 0x1000,
        });

        // 1. Validation failures.
        // !call -> IllegalOperation
        assert!(matches!(decode(&mut s, &mut a, label::ARMVCPURun, 3, v, false, 0, &ex), Err(Exc::Sys(SysError::IllegalOperation))));
        // length < 3 -> TruncatedMessage
        assert!(matches!(decode(&mut s, &mut a, label::ARMVCPURun, 2, v, true, 0, &ex), Err(Exc::Sys(SysError::TruncatedMessage))));
        // bad in_mask / out_mask
        ct.set_reg(&mut s, msg::msg_register(0), 1024);
        ct.set_reg(&mut s, msg::msg_register(1), 0x100);
        ct.set_reg(&mut s, msg::msg_register(2), 0);
        assert!(matches!(decode(&mut s, &mut a, label::ARMVCPURun, 3, v, true, 0, &ex), Err(Exc::Sys(SysError::InvalidArgument { arg: 1 }))));
        ct.set_reg(&mut s, msg::msg_register(1), 0);
        ct.set_reg(&mut s, msg::msg_register(2), 0x100);
        assert!(matches!(decode(&mut s, &mut a, label::ARMVCPURun, 3, v, true, 0, &ex), Err(Exc::Sys(SysError::InvalidArgument { arg: 2 }))));
        // unaligned / OOB offset
        ct.set_reg(&mut s, msg::msg_register(0), 32);
        ct.set_reg(&mut s, msg::msg_register(2), 0);
        assert!(matches!(decode(&mut s, &mut a, label::ARMVCPURun, 3, v, true, 0, &ex), Err(Exc::Sys(SysError::InvalidArgument { arg: 0 }))));
        ct.set_reg(&mut s, msg::msg_register(0), 4096 - 512);
        assert!(matches!(decode(&mut s, &mut a, label::ARMVCPURun, 3, v, true, 0, &ex), Err(Exc::Sys(SysError::InvalidArgument { arg: 0 }))));
        // invalid VGIC LR in frame
        ct.set_reg(&mut s, msg::msg_register(0), 1024);
        ct.set_reg(&mut s, msg::msg_register(1), sm::VGIC);
        s.write(ipc_frame + 1024 + vr::VGIC_LR0 * 8, (1u64 << 62) | 1020);
        assert!(matches!(decode(&mut s, &mut a, label::ARMVCPURun, 3, v, true, 0, &ex), Err(Exc::Sys(SysError::InvalidArgument { arg: 1 }))));
        s.write(ipc_frame + 1024 + vr::VGIC_LR0 * 8, 0);
        // read-only IPC buffer rejected
        ct.slot(tl::SLOT_BUFFER).set_cap(&mut s, Cap::Frame {
            ptr: ipc_frame,
            size: FrameSize::Small,
            rights: VM_READ_ONLY,
            is_device: false,
            mapped: true,
            is_ept: false,
            asid: 1,
            vaddr: 0x1000,
        });
        assert!(matches!(decode(&mut s, &mut a, label::ARMVCPURun, 3, v, true, 0, &ex), Err(Exc::Sys(SysError::IllegalOperation))));
        ct.slot(tl::SLOT_BUFFER).set_cap(&mut s, Cap::Frame {
            ptr: ipc_frame,
            size: FrameSize::Small,
            rights: VM_READ_WRITE,
            is_device: false,
            mapped: true,
            is_ept: false,
            asid: 1,
            vaddr: 0x1000,
        });
        // v_tcb == ct rejected
        s.write(v + TCB, ct.0);
        assert!(matches!(decode(&mut s, &mut a, label::ARMVCPURun, 3, v, true, 0, &ex), Err(Exc::Sys(SysError::IllegalOperation))));
        s.write(v + TCB, gtcb.0);

        // 2. Sync VCPUFAULT exit with GPRS in/out.
        let state_off = 1024u64;
        let state_base = ipc_frame + state_off;
        s.write(state_base + 64 * 8 + reg::X0 * 8, 0x1234_5678);
        s.write(state_base + 64 * 8 + reg::ELR_EL1 * 8, 0x4000_0000);
        s.write(state_base + 64 * 8 + reg::SPSR_EL1 * 8, 0x3c5);
        ct.set_reg(&mut s, msg::msg_register(0), state_off);
        ct.set_reg(&mut s, msg::msg_register(1), sm::GPRS);
        ct.set_reg(&mut s, msg::msg_register(2), sm::GPRS);
        assert!(decode(&mut s, &mut a, label::ARMVCPURun, 3, v, true, 0, &ex).is_ok());
        assert_eq!(ct.state(&s), sched::TS_RUNNING_VM);
        assert_eq!(s.read(v + RUN_CALLER), ct.0);
        assert_eq!(s.read(ct.0 + tl::RUN_VCPU), v);
        assert_eq!(gtcb.reg(&s, reg::X0), 0x1234_5678);
        // Concurrent Run on same VCPU rejected with DeleteFirst.
        assert!(matches!(decode(&mut s, &mut a, label::ARMVCPURun, 3, v, true, 0, &ex), Err(Exc::Sys(SysError::DeleteFirst))));
        // Guest mutates X0 and exits with VCPUFAULT.
        gtcb.set_reg(&mut s, reg::X0, 0xdead_beef);
        complete_run(&mut s, &mut a, ct, vcpu_run_stop::VCPUFAULT, 0x5a00_0001, 0x1111, 0x2222);
        assert_eq!(ct.state(&s), sched::TS_RUNNING);
        assert_eq!(s.read(v + RUN_CALLER), 0);
        assert_eq!(s.read(ct.0 + tl::RUN_VCPU), 0);
        assert_eq!(ct.reg(&s, msg::msg_register(0)), vcpu_run_stop::VCPUFAULT);
        assert_eq!(ct.reg(&s, msg::msg_register(1)), 0x5a00_0001);
        assert_eq!(ct.reg(&s, msg::msg_register(2)), 0x1111);
        assert_eq!(ct.reg(&s, msg::msg_register(3)), 0x2222);
        assert_eq!(s.read(state_base + 64 * 8 + reg::X0 * 8), 0xdead_beef);

        // 3. VMFAULT and VGIC_MAINT exits.
        ct.set_reg(&mut s, msg::msg_register(0), state_off);
        ct.set_reg(&mut s, msg::msg_register(1), 0);
        ct.set_reg(&mut s, msg::msg_register(2), 0);
        assert!(decode(&mut s, &mut a, label::ARMVCPURun, 3, v, true, 0, &ex).is_ok());
        complete_run(&mut s, &mut a, ct, vcpu_run_stop::VMFAULT, 0x9200_0007, 0x5000_0000, 0x5000_0010);
        assert_eq!(ct.reg(&s, msg::msg_register(0)), vcpu_run_stop::VMFAULT);
        assert_eq!(ct.reg(&s, msg::msg_register(1)), 0x9200_0007);
        assert_eq!(ct.reg(&s, msg::msg_register(2)), 0x5000_0000);
        assert_eq!(ct.reg(&s, msg::msg_register(3)), 0x5000_0010);

        ct.set_reg(&mut s, msg::msg_register(0), state_off);
        ct.set_reg(&mut s, msg::msg_register(1), 0);
        ct.set_reg(&mut s, msg::msg_register(2), 0);
        assert!(decode(&mut s, &mut a, label::ARMVCPURun, 3, v, true, 0, &ex).is_ok());
        complete_run(&mut s, &mut a, ct, vcpu_run_stop::VGIC_MAINT, 0x4, 0, 0);
        assert_eq!(ct.reg(&s, msg::msg_register(0)), vcpu_run_stop::VGIC_MAINT);
        assert_eq!(ct.reg(&s, msg::msg_register(1)), 0x4);

        // 4. VPPI exit updates VPPI_MASKED |= 1 and completes with VPPI.
        ct.set_reg(&mut s, msg::msg_register(0), state_off);
        ct.set_reg(&mut s, msg::msg_register(1), 0);
        ct.set_reg(&mut s, msg::msg_register(2), sm::TIMER);
        assert!(decode(&mut s, &mut a, label::ARMVCPURun, 3, v, true, 0, &ex).is_ok());
        crate::syscall::handle_vcpu_run_vppi(&mut s, &mut a, irq::TIMER_ID);
        node_set(&mut s, 0, node::CUR_THREAD, ct.0);
        assert_eq!(s.read(v + VPPI_MASKED), 1);
        assert_eq!(ct.reg(&s, msg::msg_register(0)), vcpu_run_stop::VPPI);
        assert_eq!(ct.reg(&s, msg::msg_register(1)), irq::TIMER_ID);
        assert_eq!(s.read(state_base + (64 + 37) * 8), 1);

        // 5. Pending bound notification returns immediately with INTERRUPT + badge.
        ct.set_bound_ntfn(&mut s, ntfn.0);
        ntfn.set_state(&mut s, NTFN_ACTIVE);
        ntfn.set_badge(&mut s, 0xCAFE);
        ct.set_reg(&mut s, msg::msg_register(0), state_off);
        ct.set_reg(&mut s, msg::msg_register(1), 0);
        ct.set_reg(&mut s, msg::msg_register(2), 0);
        assert!(decode(&mut s, &mut a, label::ARMVCPURun, 3, v, true, 0, &ex).is_ok());
        assert_eq!(ct.state(&s), sched::TS_RUNNING);
        assert_eq!(ntfn.state(&s), NTFN_IDLE);
        assert_eq!(ct.reg(&s, msg::msg_register(0)), vcpu_run_stop::INTERRUPT);
        assert_eq!(ct.reg(&s, msg::msg_register(1)), 0xCAFE);
        assert_eq!(s.read(v + RUN_CALLER), 0);
        assert_eq!(s.read(ct.0 + tl::RUN_VCPU), 0);

        // 6. Cross-core OWNER_CPU triggers guest FPU flush+release; same-core does not.
        assert!(a.fpu_flushed.is_empty());
        assert!(a.fpu_released.is_empty());
        assert_eq!(s.read(v + OWNER_CPU), 1);
        s.cpu = 1;
        node_set(&mut s, 1, node::CUR_THREAD, ct.0);
        ct.set_reg(&mut s, msg::msg_register(0), state_off);
        ct.set_reg(&mut s, msg::msg_register(1), 0);
        ct.set_reg(&mut s, msg::msg_register(2), 0);
        assert!(decode(&mut s, &mut a, label::ARMVCPURun, 3, v, true, 0, &ex).is_ok());
        assert_eq!(s.read(v + OWNER_CPU), 2);
        assert_eq!(a.fpu_flushed, std::vec![gtcb.0]);
        assert_eq!(a.fpu_released, std::vec![gtcb.0]);
        complete_run(&mut s, &mut a, ct, vcpu_run_stop::INTERRUPT, 0, 0, 0);
        // Same-core (cpu 1 again) must NOT trigger another FPU flush/release.
        ct.set_reg(&mut s, msg::msg_register(0), state_off);
        ct.set_reg(&mut s, msg::msg_register(1), 0);
        ct.set_reg(&mut s, msg::msg_register(2), 0);
        assert!(decode(&mut s, &mut a, label::ARMVCPURun, 3, v, true, 0, &ex).is_ok());
        assert_eq!(a.fpu_flushed.len(), 1);
        assert_eq!(a.fpu_released.len(), 1);
        complete_run(&mut s, &mut a, ct, vcpu_run_stop::INTERRUPT, 0, 0, 0);
        s.cpu = 0;

        // 7. TCB suspend cancels active run cleanly.
        ct.set_reg(&mut s, msg::msg_register(0), state_off);
        ct.set_reg(&mut s, msg::msg_register(1), 0);
        ct.set_reg(&mut s, msg::msg_register(2), 0);
        assert!(decode(&mut s, &mut a, label::ARMVCPURun, 3, v, true, 0, &ex).is_ok());
        assert_eq!(ct.state(&s), sched::TS_RUNNING_VM);
        sched::suspend(&mut s, &mut a, ct);
        assert_eq!(ct.state(&s), sched::TS_INACTIVE);
        assert_eq!(s.read(v + RUN_CALLER), 0);
        assert_eq!(s.read(ct.0 + tl::RUN_VCPU), 0);

        // 8. VCPU finalise wakes active RUN_CALLER with INTERRUPT and clears links + OWNER_CPU.
        ct.set_reg(&mut s, msg::msg_register(0), state_off);
        ct.set_reg(&mut s, msg::msg_register(1), 0);
        ct.set_reg(&mut s, msg::msg_register(2), 0);
        assert!(decode(&mut s, &mut a, label::ARMVCPURun, 3, v, true, 0, &ex).is_ok());
        assert_eq!(ct.state(&s), sched::TS_RUNNING_VM);
        finalise(&mut s, &mut a, v);
        assert_eq!(ct.state(&s), sched::TS_RUNNING);
        assert_eq!(ct.reg(&s, msg::msg_register(0)), vcpu_run_stop::INTERRUPT);
        assert_eq!(ct.reg(&s, msg::msg_register(1)), 0);
        assert_eq!(s.read(v + RUN_CALLER), 0);
        assert_eq!(s.read(v + OWNER_CPU), 0);
        assert_eq!(s.read(ct.0 + tl::RUN_VCPU), 0);
    }
}
