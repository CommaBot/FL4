/-
P1: InvGaps' `irqControl`, `irqHandler`, `ioPortControl` and `ioPort`
families keep the invariants, from `DecPre`, the CSpace placement facts
`CdtHyps` (the target slot, the insertion), the invoked slot's `CapW`
(DecGap's `slot` hypothesis), the deletion placement facts `DelPlace` (the
IRQ handler slot's `delete_one`), the transfer's `XferHyps` (a port read's
reply buffer) and `IrqPlace` (an IrqHandler cap's IRQ is below 128; the extra
caps' slots are cap slots).  The IRQ-state write is a kernel-global word
(`obj.ks_set.blk`); the new IrqHandler / IoPort cap's insertion writes only
cap-slot words (`blk_of_capw`); the caller's restart is
`set_thread_state.restart_blk` / `Cur0.restart`.
-/
import Fl4Proofs.P1.QueueSchedCtl
import Fl4Proofs.P1.QueueDecCnode
import Fl4Proofs.P1.QueueDecDom
import Fl4Proofs.P1.QueueFinCur
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}

/-- The IRQ-state write of an IRQ below 128 keeps `BlkOK`. -/
theorem interrupt.set_irq_state.blk {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (v irq : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hi : irq.val < 128) :
    interrupt.set_irq_state st ar s a v irq ⦃ r => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ⦄ := by
  unfold interrupt.set_irq_state interrupt.state_off
  simp only [lift, bind_ok]
  refine WP.spec_bind (Pₘ := fun o : U64 => o.val = 224 + 8 * irq.val) ?_ fun o ho => ?_
  · refine WP.spec_bind P0.Consts.layout.ks.IRQ_STATE.spec fun b eb => ?_
    subst eb
    refine (WP.spec_ok _).2 ?_
    simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]; omega
  refine WP.spec_bind (obj.ks_set.blk s o v h (by omega) (by omega)) fun s1 h1 => ?_
  exact WP.spec_bind (hA.mask_irq a irq _) fun a1 _ => (WP.spec_ok _).2 h1.1

/-- **`invoke_irq_control`**: the IRQ-state write and the IrqHandler cap's
insertion under the IrqControl cap's slot. -/
theorem interrupt.invoke_irq_control.blk {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z) (s : S) (a : A) (irq handler control : U64)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hi : irq.val < 128) (hh : CapW T Ω Sg handler)
    (hc : CapW T Ω Sg control) :
    interrupt.invoke_irq_control st ar s a irq handler control ⦃ r => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold interrupt.invoke_irq_control
  refine WP.spec_bind (interrupt.set_irq_state.blk hA s a _ irq h hi) ?_
  rintro ⟨s1, a1⟩ h1
  try dsimp only
  refine WP.spec_bind (Pₘ := fun s2 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s2) ?_ fun s2 h2 => (WP.spec_ok _).2 h2
  unfold cdt.insert
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st control s1 hS) fun c0 _ => ?_
  exact WP.spec_mono (C.ins Ac s1 _ c0 control handler (BlkOK.bxi h1) hc hh) fun s2 w2 =>
    (blk_of_capw h1 w2 fun _ hb => hb).1

/-- **`check_msi`**: the caller's restart, or an error with the state unchanged. -/
theorem interrupt.check_msi.blk {s : S} {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (buf : U64) :
    interrupt.check_msi st s buf ⦃ r => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2 ∧ (∀ e, r.1 = .Err e → r.2 = s) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hct : L.curW s ∈ T := D.bxi.1.choose_spec.choose_spec.curT
  have K : ∀ r : core.result.Result Unit error.Exc,
      (ok (r, s) : Result _) ⦃ r => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2 ∧ (∀ e, r.1 = .Err e → r.2 = s) ⦄ :=
    fun r => (WP.spec_ok _).2 ⟨D.bxi.blk, fun _ _ => rfl⟩
  unfold interrupt.check_msi
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have e : ct = L.curW s := ect
  subst e
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun _ _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun _ _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun _ _ => ?_
  simp only [error.range, bind_ok]
  split
  · exact K _
  split
  · exact K _
  split
  · exact K _
  refine WP.spec_bind (sched.set_thread_state.restart_blk (Es := ∅) s _ D.bxi.blk hct (runnable_ok D.run).1
    (runnable_ok D.run).2) fun s1 h1 => ?_
  exact (WP.spec_ok _).2 ⟨h1.1, fun e he => by cases he⟩

/-- **`map_ioapic`**: the caller's restart and the arch's IOAPIC mapping, or an
error with the state unchanged. -/
theorem interrupt.map_ioapic.blk {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s : S}
    {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (a : A) (buf vector : U64) (remapped : Bool) :
    interrupt.map_ioapic st ar s a buf vector remapped ⦃ r =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1 ∧ (∀ e, r.1 = .Err e → r.2.1 = s) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hct : L.curW s ∈ T := D.bxi.1.choose_spec.choose_spec.curT
  have K : ∀ (r : core.result.Result Unit error.Exc) (a' : A),
      (ok (r, s, a') : Result _) ⦃ r =>
        BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1 ∧ (∀ e, r.1 = .Err e → r.2.1 = s) ⦄ :=
    fun r _ => (WP.spec_ok _).2 ⟨D.bxi.blk, fun _ _ => rfl⟩
  unfold interrupt.map_ioapic
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have e : ct = L.curW s := ect
  subst e
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun _ _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun _ _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun _ _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun _ _ => ?_
  refine WP.spec_bind (hA.num_ioapics a) fun n _ => ?_
  simp only [error.range, error.illegal, bind_ok]
  split
  · exact K _ _
  split
  · step as ⟨i, _⟩
    first | exact K _ _ | exact ⟨D.bxi.blk, by simp⟩
  refine WP.spec_bind (hA.ioapic_pins a _) fun pins _ => ?_
  split
  · simp only [lift, bind_ok]
    exact K _ _
  split
  · exact K _ _
  split
  · exact K _ _
  refine WP.spec_bind (Pₘ := fun _ => True) (by
    split
    · exact WP.spec_mono (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun _ _ => trivial
    · exact (WP.spec_ok _).2 trivial) fun handle _ => ?_
  step as ⟨i, _⟩
  split
  · exact K _ _
  refine WP.spec_bind (sched.set_thread_state.restart_blk (Es := ∅) s _ D.bxi.blk hct (runnable_ok D.run).1
    (runnable_ok D.run).2) fun s1 h1 => ?_
  split
  · refine WP.spec_bind (hA.ioapic_map_remapped a _ _ _ _ _ _) ?_
    rintro ⟨_, a1⟩ _
    exact (WP.spec_ok _).2 ⟨h1.1, fun e he => by cases he⟩
  · refine WP.spec_bind (hA.ioapic_map a _ _ _ _ _) ?_
    rintro ⟨_, a1⟩ _
    exact (WP.spec_ok _).2 ⟨h1.1, fun e he => by cases he⟩


theorem irq_branch_ok {α β : Type} (x : α) :
    core.result.Result.Insts.CoreOpsTry.branch (core.result.Result.Ok x : core.result.Result α β) =
      ok (core.ops.control_flow.ControlFlow.Continue x) := rfl

set_option hygiene false in
/-- An error leaf with the state unchanged. -/
local macro "errI" : tactic => `(tactic| first
  | exact D.err _
  | exact (WP.spec_ok _).2 (D.err _)
  | (simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok,
      error.illegal, error.truncated, error.range, error.invalid_cap, error.invalid_arg]
     first | exact D.err _ | exact (WP.spec_ok _).2 (D.err _)))

set_option hygiene false in
/-- The issue tail, from the target slot's lookup: the empty check, the
arch-specific step `m` (keeping `BlkOK`, or an error with `s`), then the
invocation. -/
local macro "irqtail" : tactic => `(tactic| (
  refine WP.spec_bind (C.tgt Ac s _ _ _ D.bxi) fun r hr => ?_
  rcases r with v | e
  swap
  · errI
  have hv := hr v rfl
  simp only [irq_branch_ok, bind_ok]
  refine WP.spec_bind (P0.cdt.ensure_empty_slot.p0 st s v hS) fun r1 _ => ?_
  rcases r1 with _ | e
  swap
  · errI
  simp only [irq_branch_ok, bind_ok]))

set_option maxHeartbeats 4000000 in
/-- **`decode_issue_isa`** (IRQIssueIRQHandler without IOAPICs). -/
theorem interrupt.decode_issue_isa.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z) {s : S} {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) (len src buf : U64)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hsrc : CapW T Ω Sg src) :
    interrupt.decode_issue_isa st ar s a len src buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hct : L.curW s ∈ T := D.bxi.1.choose_spec.choose_spec.curT
  unfold interrupt.decode_issue_isa
  refine WP.spec_bind (P0.interrupt.extra0.p0 st s extra hS) fun o _ => ?_
  rcases o with _ | c
  · errI
  try dsimp only
  split
  swap
  · errI
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have e : ct = L.curW s := ect
  subst e
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun irq _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun _ _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun _ _ => ?_
  refine WP.spec_bind (hA.num_ioapics a) fun n _ => ?_
  split
  · errI
  split
  · errI
  rename_i hirq
  have hi : irq.val < 128 := by
    simp only [layout.irq.ISA_MAX, gt_iff_lt, not_lt] at hirq; scalar_tac
  refine WP.spec_bind (P0.interrupt.is_irq_active.p0 st s irq hS) fun b _ => ?_
  split
  · errI
  irqtail
  refine WP.spec_bind (sched.set_thread_state.restart_blk (Es := ∅) s _ D.bxi.blk hct (runnable_ok D.run).1
    (runnable_ok D.run).2) fun s1 h1 => ?_
  refine WP.spec_bind (interrupt.invoke_irq_control.blk hA C s1 a irq v src h1.1 hi hv hsrc) ?_
  rintro ⟨s2, a1⟩ h2
  exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi h2))

set_option maxHeartbeats 8000000 in
/-- **`decode_irq_control`** keeps the invariants. -/
theorem interrupt.decode_irq_control.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z) {s : S} {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) (lbl len slot buf : U64)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hslot : CapW T Ω Sg slot) :
    interrupt.decode_irq_control st ar s a lbl len slot buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hct : L.curW s ∈ T := D.bxi.1.choose_spec.choose_spec.curT
  unfold interrupt.decode_irq_control
  split
  · exact interrupt.decode_issue_isa.dec hA C a len slot buf D hslot
  split
  · split
    · split
      · refine WP.spec_bind (Pₘ := fun _ => True) (by
          first | (split <;> exact (WP.spec_ok _).2 trivial) | exact (WP.spec_ok _).2 trivial) fun _ _ => ?_
        refine WP.spec_bind (P0.interrupt.extra0.p0 st s extra hS) fun o _ => ?_
        rcases o with _ | c
        · errI
        try dsimp only
        split
        swap
        · errI
        step with sched.cur_thread.spec as ⟨ct, ect⟩
        have e : ct = L.curW s := ect
        subst e
        refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun _ _ => ?_
        refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun _ _ => ?_
        refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun irq _ => ?_
        refine WP.spec_bind P0.Consts.layout.irq.USER_MAX.spec fun i ei => ?_
        subst ei
        step as ⟨i1, ei1⟩
        split
        · step as ⟨i2, _⟩
          errI
        rename_i hirq
        step as ⟨irq1, eirq1⟩
        have hi : irq1.val < 128 := by
          simp only [layout.irq.USER_MIN] at ei1 eirq1
          simp only [gt_iff_lt, not_lt] at hirq; scalar_tac
        refine WP.spec_bind (P0.interrupt.is_irq_active.p0 st s irq1 hS) fun b _ => ?_
        split
        · errI
        irqtail
        split
        · refine WP.spec_bind (interrupt.check_msi.blk D buf) ?_
          rintro ⟨r2, s1⟩ ⟨h1, he⟩
          try simp only [uncurry_apply_pair]
          rcases r2 with _ | e
          · simp only [irq_branch_ok, bind_ok]
            refine WP.spec_bind (interrupt.invoke_irq_control.blk hA C s1 a irq1 v slot h1 hi hv hslot) ?_
            rintro ⟨s2, a1⟩ h2
            exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi h2))
          · have e2 := he _ rfl
            simp only at e2
            subst e2
            errI
        · step as ⟨i2, _⟩
          refine WP.spec_bind (interrupt.map_ioapic.blk hA D a buf i2 _) ?_
          rintro ⟨r2, s1, a1⟩ ⟨h1, he⟩
          try simp only [uncurry_apply_pair]
          rcases r2 with _ | e
          · simp only [irq_branch_ok, bind_ok]
            refine WP.spec_bind (interrupt.invoke_irq_control.blk hA C s1 a1 irq1 v slot h1 hi hv hslot) ?_
            rintro ⟨s2, a2⟩ h2
            exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi h2))
          · have e2 := he _ rfl
            simp only at e2
            subst e2
            errI
      · errI
    · refine WP.spec_bind (Pₘ := fun _ => True) (by
        first | (split <;> exact (WP.spec_ok _).2 trivial) | exact (WP.spec_ok _).2 trivial) fun _ _ => ?_
      refine WP.spec_bind (P0.interrupt.extra0.p0 st s extra hS) fun o _ => ?_
      rcases o with _ | c
      · errI
      try dsimp only
      split
      swap
      · errI
      step with sched.cur_thread.spec as ⟨ct, ect⟩
      have e : ct = L.curW s := ect
      subst e
      refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun _ _ => ?_
      refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun _ _ => ?_
      refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun irq _ => ?_
      refine WP.spec_bind P0.Consts.layout.irq.USER_MAX.spec fun i ei => ?_
      subst ei
      step as ⟨i1, ei1⟩
      split
      · step as ⟨i2, _⟩
        errI
      rename_i hirq
      step as ⟨irq1, eirq1⟩
      have hi : irq1.val < 128 := by
        simp only [layout.irq.USER_MIN] at ei1 eirq1
        simp only [gt_iff_lt, not_lt] at hirq; scalar_tac
      refine WP.spec_bind (P0.interrupt.is_irq_active.p0 st s irq1 hS) fun b _ => ?_
      split
      · errI
      irqtail
      split
      · refine WP.spec_bind (interrupt.check_msi.blk D buf) ?_
        rintro ⟨r2, s1⟩ ⟨h1, he⟩
        try simp only [uncurry_apply_pair]
        rcases r2 with _ | e
        · simp only [irq_branch_ok, bind_ok]
          refine WP.spec_bind (interrupt.invoke_irq_control.blk hA C s1 a irq1 v slot h1 hi hv hslot) ?_
          rintro ⟨s2, a1⟩ h2
          exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi h2))
        · have e2 := he _ rfl
          simp only at e2
          subst e2
          errI
      · exfalso
        simp_all
  · refine WP.spec_bind (Pₘ := fun _ => True) (by
      first | (split <;> exact (WP.spec_ok _).2 trivial) | exact (WP.spec_ok _).2 trivial) fun _ _ => ?_
    refine WP.spec_bind (P0.interrupt.extra0.p0 st s extra hS) fun o _ => ?_
    rcases o with _ | c
    · errI
    try dsimp only
    split
    swap
    · errI
    step with sched.cur_thread.spec as ⟨ct, ect⟩
    have e : ct = L.curW s := ect
    subst e
    refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun _ _ => ?_
    refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun _ _ => ?_
    refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun irq _ => ?_
    refine WP.spec_bind P0.Consts.layout.irq.USER_MAX.spec fun i ei => ?_
    subst ei
    step as ⟨i1, ei1⟩
    split
    · step as ⟨i2, _⟩
      errI
    rename_i hirq
    step as ⟨irq1, eirq1⟩
    have hi : irq1.val < 128 := by
      simp only [layout.irq.USER_MIN] at ei1 eirq1
      simp only [gt_iff_lt, not_lt] at hirq; scalar_tac
    refine WP.spec_bind (P0.interrupt.is_irq_active.p0 st s irq1 hS) fun b _ => ?_
    split
    · errI
    irqtail
    split
    · refine WP.spec_bind (interrupt.check_msi.blk D buf) ?_
      rintro ⟨r2, s1⟩ ⟨h1, he⟩
      try simp only [uncurry_apply_pair]
      rcases r2 with _ | e
      · simp only [irq_branch_ok, bind_ok]
        refine WP.spec_bind (interrupt.invoke_irq_control.blk hA C s1 a irq1 v slot h1 hi hv hslot) ?_
        rintro ⟨s2, a1⟩ h2
        exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi h2))
      · have e2 := he _ rfl
        simp only at e2
        subst e2
        errI
    · step as ⟨i2, _⟩
      refine WP.spec_bind (interrupt.map_ioapic.blk hA D a buf i2 _) ?_
      rintro ⟨r2, s1, a1⟩ ⟨h1, he⟩
      try simp only [uncurry_apply_pair]
      rcases r2 with _ | e
      · simp only [irq_branch_ok, bind_ok]
        refine WP.spec_bind (interrupt.invoke_irq_control.blk hA C s1 a1 irq1 v slot h1 hi hv hslot) ?_
        rintro ⟨s2, a2⟩ h2
        exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi h2))
      · have e2 := he _ rfl
        simp only at e2
        subst e2
        errI

/-- **InvGaps' `irqControl`, discharged** from the CSpace placement facts. -/
theorem decGap_irqControl {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z) : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U .irqControl := by
  intro Ac s a lbl len slot cap blk call don fp buf extra hf D hslot
  cases cap <;> simp [capFam] at hf
  unfold syscall.decode_invocation
  step with sched.cur_thread.spec as ⟨ct, _⟩
  try dsimp only
  exact interrupt.decode_irq_control.dec hA C a lbl len slot buf D hslot


/-! ## The IRQ handler family -/

/-- The placement facts the IRQ handler decode rests on (P3's `valid_cap`
of an IrqHandler cap, and the extra caps' slots being cap slots, from
`lookup_extra_caps`). -/
structure IrqPlace (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) : Prop where
  irq : ∀ (Ac : Set U64) (s : S) (cap : capability.Cap) (extra : Aeneas.Std.Array obj.Slot 3#usize),
    DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra → ∀ i, cap = .IrqHandler i → i.val < 128
  extra : ∀ (Ac : Set U64) (s : S) (cap : capability.Cap) (extra : Aeneas.Std.Array obj.Slot 3#usize),
    DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra → ∀ sl ∈ extra.val, sl ≠ 0#u64 → CapW T Ω Sg sl

theorem SlotW.capw0 {x : U64} (h : SlotW T Ω Sg x) : CapW T Ω Sg x := by
  have h0 := h.2 0#u64 (by simp) (by simp)
  have e : core.num.U64.wrapping_add x 0#u64 = x := UScalar.eq_of_val_eq (by
    simp only [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; scalar_tac)
  rwa [e] at h0

/-- **`delete_one` of an IRQ's handler slot**: no cap, or a notification
cap's finalisation and the slot's emptying (as `finGap_irq`). -/
theorem cdt.delete_one.irq_cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    (P : DelPlace st T Cs Ω H Sg Rp Scs Nt Z V) {s0 s : S} {a : A} {irq : U64}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hi : irq.val < 128) :
    cdt.delete_one st ar s a (irqSlotA (L.ksb s) irq) ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  obtain ⟨Ac', hb⟩ := h.bxi
  have hW := irq_slotW hb hi
  unfold cdt.delete_one
  refine WP.spec_bind (WP.spec_and (P.irq Ac' s irq hb hi) (P.cap Ac' s _ hb hW)) fun c ⟨hc', hcd⟩ => ?_
  refine WP.spec_bind (P0.capability.Cap.is_null.p0 c) fun bn _ => ?_
  split
  · exact (WP.spec_ok _).2 h
  refine WP.spec_bind (P0.cdt.is_final_capability_with_cap.p0 st s _ c hS) fun f _ => ?_
  rcases hc' with rfl | ⟨n, b0, b1, b2, rfl⟩
  · simp [objects.finalise_cap_object]
    exact cdt.empty_slot.cur0 hA P h hW DelCapOK.null
  · obtain ⟨hn, hH⟩ := hcd.1.1.2.1 n b0 b1 b2 rfl
    refine WP.spec_bind (fin_ntfn_obj.cur0 (ar := ar) (a := a) (fin := f) (b0 := b0) (b1 := b1) (b2 := b2) h hn hH) ?_
    rintro ⟨_, s1, a1⟩ ⟨-, h1⟩
    exact cdt.empty_slot.cur0 hA P h1 hW DelCapOK.null

set_option maxHeartbeats 4000000 in
/-- **`decode_irq_handler`** (Ack, SetIRQHandler, ClearIRQHandler) keeps the
invariants. -/
theorem interrupt.decode_irq_handler.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z) {V : U64 → Prop} (P : DelPlace st T Cs Ω H Sg Rp Scs Nt Z V)
    {s : S} {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) (lbl irq : U64)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hi : irq.val < 128)
    (hx : ∀ sl ∈ extra.val, sl ≠ 0#u64 → CapW T Ω Sg sl) :
    interrupt.decode_irq_handler st ar s a lbl irq extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold interrupt.decode_irq_handler
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have e : ct = L.curW s := ect
  subst e
  split
  · refine WP.spec_bind (Cur0.restart D) fun s1 h1 => ?_
    refine WP.spec_bind (hA.mask_irq a irq false) fun a1 _ => ?_
    exact (WP.spec_ok _).2 h1.post
  split
  · have hl0 : (0#usize).val < extra.val.length := by rw [extra.property]; simp
    refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec extra 0#usize hl0) fun sl hsl => ?_
    have hmem : sl ∈ extra.val := hsl ▸ List.getElem_mem hl0
    simp only [obj.Slot.is_null, bind_ok]
    split
    · errI
    rename_i h0
    have hne : sl ≠ 0#u64 := by simpa using h0
    refine WP.spec_bind (P0.obj.Slot.cap.p0 st sl s hS) fun c _ => ?_
    rcases c with _ | _ | _ | ⟨n, b0, b1, b2⟩
    all_goals try (simp only [error.invalid_cap, bind_ok]; exact (WP.spec_ok _).2 (D.err _))
    all_goals try errI
    try dsimp only
    split
    swap
    · errI
    refine WP.spec_bind (Cur0.restart D) fun s1 h1 => ?_
    refine WP.spec_bind (interrupt.irq_slot.val s1 irq) fun isl e => ?_
    subst e
    obtain ⟨Ac1, hb1⟩ := h1.bxi
    have hW := (irq_slotW hb1 hi).capw0
    refine WP.spec_bind (cdt.delete_one.irq_cur0 hA P h1 hi) ?_
    rintro ⟨s2, a1⟩ h2
    try simp only [uncurry_apply_pair]
    obtain ⟨Ac2, hb2⟩ := h2.bxi
    refine WP.spec_bind (Pₘ := fun s3 => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s s3) ?_
      fun s3 h3 => (WP.spec_ok _).2 h3.post
    unfold cdt.insert
    refine WP.spec_bind (P0.obj.Slot.cap.p0 st sl s2 hS) fun c0 _ => ?_
    exact WP.spec_mono (C.ins Ac2 s2 _ c0 sl _ hb2 (hx sl hmem hne) hW) fun s3 w => h2.capw w fun _ hb => hb
  split
  · refine WP.spec_bind (Cur0.restart D) fun s1 h1 => ?_
    refine WP.spec_bind (interrupt.irq_slot.val s1 irq) fun isl e => ?_
    subst e
    refine WP.spec_bind (cdt.delete_one.irq_cur0 hA P h1 hi) ?_
    rintro ⟨s2, a1⟩ h2
    exact (WP.spec_ok _).2 h2.post
  · errI

/-- **InvGaps' `irqHandler`, discharged** from the CSpace and deletion
placement facts and `IrqPlace`. -/
theorem decGap_irqHandler {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z) {V : U64 → Prop} (P : DelPlace st T Cs Ω H Sg Rp Scs Nt Z V)
    (Pl : IrqPlace st T Cs Ω H Sg Rp Scs Nt Z U) : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U .irqHandler := by
  intro Ac s a lbl len slot cap blk call don fp buf extra hf D _hslot
  cases cap <;> simp [capFam] at hf
  rename_i irq
  unfold syscall.decode_invocation
  step with sched.cur_thread.spec as ⟨ct, _⟩
  try dsimp only
  exact interrupt.decode_irq_handler.dec hA C P a lbl irq D (Pl.irq _ _ _ _ D irq rfl) (Pl.extra _ _ _ _ D)


/-! ## The I/O port families -/

theorem mask16_lt (i : U64) : (i &&& 65535#u64).val < 65536 := by
  rw [UScalar.val_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

set_option maxHeartbeats 4000000 in
/-- **`ioport.decode_control`** (IOPortControl_Issue) keeps the invariants:
the restart, the I/O-port bitmap words (`set_mask.cur0`) and the IoPort cap's
insertion under the control cap's slot. -/
theorem ioport.decode_control.dec (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z) {A : Type _} {ar : machine.Arch A}
    {s : S} {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) (lbl len slot buf : U64)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hslot : CapW T Ω Sg slot) :
    ioport.decode_control st ar s a lbl len slot buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold ioport.decode_control
  split
  · errI
  split
  · errI
  have hl0 : (0#usize).val < extra.val.length := by rw [extra.property]; simp
  refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec extra 0#usize hl0) fun sl _ => ?_
  simp only [obj.Slot.is_null, bind_ok]
  split
  · errI
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have e : ct = L.curW s := ect
  subst e
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun i0 _ => ?_
  simp only [lift, bind_ok]
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun i1 _ => ?_
  try simp only [lift, bind_ok]
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun _ _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun _ _ => ?_
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st sl s hS) fun cn _ => ?_
  split
  · errI
  rename_i hlf
  have hfl : (i0 &&& 65535#u64).val ≤ (i1 &&& 65535#u64).val := Nat.le_of_not_lt fun h => hlf h
  refine WP.spec_bind (P0.ioport.range_free.p0 st s _ _ hS) fun b1 _ => ?_
  split
  swap
  · errI
  irqtail
  refine WP.spec_bind (Cur0.restart D) fun s2 h2 => ?_
  refine WP.spec_bind (ioport.set_mask.cur0 h2 (mask16_lt i1) hfl) fun s3 h3 => ?_
  obtain ⟨Ac3, hb3⟩ := h3.bxi
  refine WP.spec_bind (Pₘ := fun s4 => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s s4) ?_
    fun s4 h4 => (WP.spec_ok _).2 h4.post
  unfold cdt.insert
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st slot s3 hS) fun c0 _ => ?_
  exact WP.spec_mono (C.ins Ac3 s3 _ c0 slot v hb3 hslot hv) fun s4 w => h3.capw w fun _ hb => hb

/-- **InvGaps' `ioPortControl`, discharged** from the CSpace placement facts. -/
theorem decGap_ioPortControl {A : Type _} {ar : machine.Arch A} (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z) :
    DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U .ioPortControl := by
  intro Ac s a lbl len slot cap blk call don fp buf extra hf D hslot
  cases cap <;> simp [capFam] at hf
  unfold syscall.decode_invocation
  step with sched.cur_thread.spec as ⟨ct, _⟩
  try dsimp only
  exact ioport.decode_control.dec C a lbl len slot buf D hslot

set_option maxHeartbeats 4000000 in
/-- **`ioport.decode`** (the port reads and writes) keeps the invariants: the
restart, the arch's port access, for a read with a reply the current
thread's message registers (`XS`), then the thread set running. -/
theorem ioport.decode.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U) {s : S} {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) (lbl len : U64) (first last x : U64) (call : Bool)
    (buf : U64) (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) :
    ioport.decode st ar s a lbl len (.IoPort first last x) call buf ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hct : L.curW s ∈ T := D.bxi.1.choose_spec.choose_spec.curT
  unfold ioport.decode
  try dsimp only
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have e : ct = L.curW s := ect
  subst e
  refine WP.spec_bind (P0.ioport.port_size.p0 lbl) fun size _ => ?_
  split
  · errI
  refine WP.spec_bind (P0.ioport.is_port_in.p0 lbl) fun isin _ => ?_
  split
  · split
    · errI
    refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun i0 _ => ?_
    simp only [lift, bind_ok]
    refine WP.spec_bind (P0.ioport.allowed.p0 first last _ size) fun r _ => ?_
    rcases r with _ | e
    swap
    · errI
    simp only [irq_branch_ok, bind_ok]
    refine WP.spec_bind (sched.set_thread_state.restart_blk (Es := ∅) s _ D.bxi.blk hct (runnable_ok D.run).1
      (runnable_ok D.run).2) fun s1 ⟨h1, f1, hst1, _⟩ => ?_
    obtain ⟨Q, R, x1⟩ := BXI.xs (BlkOK.bxi h1) (D.user.ksb f1.1)
    refine WP.spec_bind (hA.port_in a _ size) ?_
    rintro ⟨v, a1⟩ _
    try simp only [uncurry_apply_pair]
    refine WP.spec_bind (Pₘ := fun s2 => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac ∅ Q R s1 s2) ?_ ?_
    · split
      · refine WP.spec_bind (E.buf Ac ∅ Q R s1 _ x1.1 hct) fun b hb => ?_
        refine WP.spec_bind (obj.Tcb.set_reg.xs (v := 0#u64) x1 hct (by simp [layout.reg.BADGE, layout.reg.RDI]))
          fun s3 x3 => ?_
        refine WP.spec_bind (msg.set_mr.xs x3 hct hb (by simp)) ?_
        rintro ⟨n, s4⟩ ⟨x4, -⟩
        try simp only [uncurry_apply_pair]
        refine WP.spec_bind (P0.msginfo.MessageInfo.new.p0 _ _ _ _) fun mi _ => ?_
        unfold msg.set_msg_info
        exact WP.spec_bind (P0.msginfo.MessageInfo.to_word.p0 _) fun w _ =>
          obj.Tcb.set_reg.xs (v := w) x4 hct (by simp [layout.reg.MSG_INFO, layout.reg.RSI])
      · exact (WP.spec_ok _).2 x1
    intro s2 x2
    have hst : L.mem s2 (stA (L.curW s)) = sched.TS_RESTART := by
      rw [stA_eq, x2.2.2.2.2.2.1 _ hct _ (by simp) (by simp) (by simp), ← stA_eq, hst1]
    refine WP.spec_bind (sched.set_thread_state.running_bxi x2.bxi hct hst) fun s3 h3 => ?_
    exact (WP.spec_ok _).2 (DecPost.ok_bxi h3)
  · split
    · errI
    refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun i0 _ => ?_
    simp only [lift, bind_ok]
    refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun raw _ => ?_
    refine WP.spec_bind (P0.ioport.allowed.p0 first last _ size) fun r _ => ?_
    rcases r with _ | e
    swap
    · errI
    simp only [irq_branch_ok, bind_ok]
    refine WP.spec_bind (Pₘ := fun _ => True) (by
      split
      · exact (WP.spec_ok _).2 trivial
      · split <;> exact (WP.spec_ok _).2 trivial) fun data _ => ?_
    refine WP.spec_bind (sched.set_thread_state.restart_blk (Es := ∅) s _ D.bxi.blk hct (runnable_ok D.run).1
      (runnable_ok D.run).2) fun s1 h1 => ?_
    refine WP.spec_bind (hA.port_out a _ size data) fun a1 _ => ?_
    exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi h1.1))

/-- **InvGaps' `ioPort`, discharged** from the transfer's placement facts
(the IPC buffer of a port read's reply). -/
theorem decGap_ioPort {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U) : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U .ioPort := by
  intro Ac s a lbl len slot cap blk call don fp buf extra hf D _hslot
  cases cap <;> simp [capFam] at hf
  rename_i first last x
  unfold syscall.decode_invocation
  step with sched.cur_thread.spec as ⟨ct, _⟩
  try dsimp only
  exact ioport.decode.dec hA E a lbl len first last x call buf D

end

end Fl4Proofs.P1
