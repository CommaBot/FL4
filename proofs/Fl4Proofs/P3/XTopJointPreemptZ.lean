/-
P3 (DESIGN.md §9): **the preemption path at `J` ending at `JAtZ`**
(KENTRY-PLAN kp8, item 7): XTopJointIrq's `JIrqSigHyp` [W] deleted.

kp7 found that only the sufficient-budget branch of `mcs_preemption_point`
reaches `check_interrupt` at a hole that is not `JAtZ`: there `OffOK` needs
l4v's `cur_sc_offset_ready` at the hole. It holds at every hole the
invocation can leave, by the time shift of the preemption point's time
update, without carrying anything through the invocation:

* `TShift σ0 σ`: the hole's time and consumed time are the base's moved by
  the same elapsed time (`update_time_stamp`: `cur_time := now`,
  `consumed_time += now - cur_time`, time not going back).
* `jAtPre_holeT`: every `JAtPre` state is a `JHole` with `TShift` from its
  base (a preempting `preemption_point`: `pp_err_eq`, `updateTimeStamp_eq'`
  and `NowAgree` [P]); `jAtPre_holeTN` also gives the base's no-switch and
  non-idle facts at the hole (kp10).
* `JHole.offOK_suff`: at such a hole with `CurInv`, a non-idle schedulable
  current thread and a sufficient head, `OffOK` holds. The base is `JAtZ`:
  for a positive consumed time its `OffOK` gives the head ready with it, for
  a zero one `Inv.rd` of the (runnable, bound, unreleased) current thread
  gives the head released (l4v `valid_sched`'s `released_sc` of a
  schedulable thread = `cur_sc_offset_ready 0`); XTopJointPP's `rdy_shift`
  moves both to the hole.
* `JHole.mcsPPJZ`: XTopJointPreempt's `JHole.mcsPPJ` with `JAt` after in
  every branch (the sufficient one by `JHole.toJ` with `offOK_suff` and
  `curOwn_of_curInv`; the charge branches were `JAtZ` already).
* `JAtZ.msArJ` (another machine state with the same memory and an arch
  state keeping `AR`), `jIrqHypZ_of`: `handle_interrupt` from a `JAt` state
  (XTopJointIrq's `JHole.handleIrqJ` over `JAtZ.toHole`; its signal premise
  is vacuous there: `JAtZ.off`, `JAtZ.own`).
* `JHole.afterInvJZ`: `after_invocation (Err _)` from a `JHole` with
  `TShift` under `PPCov ∨ PPCovT` refines `preemption_path` with `PPQZ`
  after: the spec fails, or an outcome with `JAt` after (no line pending:
  the post-budget-check state is `JAtZ`, for schedule at J, M7) or `XTopAt`
  after a handled line. `PPQZ.toPPQ`.
* `hPre_ofZ` / `dispatch_invokeJPZ` / `dispatch_invokeJEPZ`: XTopJointIrq's
  `hPre_ofI` / `dispatch_invokeJPI` / `dispatch_invokeJEPI` without
  `JIrqSigHyp` (remaining: `IrqPlat`, `PPPlat` [P], `hNS` [S],
  `JPreemptRestHypN` [W], as there).
-/
import Fl4Proofs.P3.XTopJointIrq
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-- **The hole's time words are the base's moved by the elapsed time**
(module docstring). -/
def TShift (σ0 σ : Fl4Spec.State Unit) : Prop :=
  σ0.curTime ≤ σ.curTime ∧ σ.consumedTime = σ0.consumedTime + (σ.curTime - σ0.curTime)

theorem TShift.refl (σ : Fl4Spec.State Unit) : TShift σ σ :=
  ⟨BitVec.le_refl _, by rw [BitVec.sub_self, BitVec.add_zero]⟩

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

variable (arI) in
/-- Some `JHole` with `TShift` from its base ends at `(s, a, σ)`. -/
def JHoleAtT (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s0 : S) (a0 : A)
    (σ0 : Fl4Spec.State Unit), JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ ∧ TShift σ0 σ ∧ VxE Z

theorem JHoleAtT.hole {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : JHoleAtT (L := L) arI AR s a σ) :
    JHoleAtV (L := L) arI AR s a σ :=
  let ⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh, _, _⟩ := h; ⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh, inferInstance⟩

/-- **`OffOK` at a shifted hole with a sufficient head** (module docstring). -/
theorem JHole.offOK_suff {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hT : TShift σ0 σ) (hC : CurInv σ)
    (hni : σ.curThread ≠ σ.idleThread) (hs : Fl4Spec.schedulable σ.curThread σ = true)
    (hsuf : ∀ y n, σ.kheap σ.curSc = some (.schedContext y n) →
      Fl4Spec.refillSufficient σ.consumedTime (Fl4Spec.refillHd y) = true) : OffOK σ := by
  have hid := curSc_ne_idleSc_of Hh.inv Hh.act hC hni
  have J := Hh.j0
  obtain ⟨xt, hkt, hxs, -⟩ := hC.tcb
  obtain ⟨x, scp, y', n', hkx, -, hrun, -, -, -⟩ := schedulable_inv hs
  rw [hkt] at hkx; cases hkx
  obtain ⟨ms, t, c, -, e⟩ := Hh.spec
  subst e
  intro _ y n hy _
  have hact := hC.active hid y n hy
  have hrd : (Fl4Spec.refillHd y).rTime + σ0.consumedTime ≤ σ0.curTime ∧
      (Fl4Spec.refillHd y).rTime ≤ σ0.curTime := by
    by_cases h0 : σ0.consumedTime = 0
    · have h := (J.inv.rd σ0.curThread xt hkt (Or.inl hrun) xt σ0.curSc y n hkt hxs hy hact hC.notRel).1
      simp only [Fl4Spec.refillReady, Fl4Spec.refillReady', decide_eq_true_eq, bv_add0] at h
      rw [h0, bv_add0]; exact ⟨h, h⟩
    · obtain ⟨-, h1, h2⟩ := J.off (bv_pos h0) y n hy (fun _ => hact)
      simp only [Fl4Spec.refillReady, Fl4Spec.refillReady', decide_eq_true_eq, bv_add0] at h1 h2
      exact ⟨h1, h2⟩
  obtain ⟨hs1, hs2⟩ := rdy_shift hrd.1 hrd.2 hT.1
  refine ⟨hsuf y n hy, ?_, ?_⟩
  · simp only [Fl4Spec.refillReady', decide_eq_true_eq]
    show (Fl4Spec.refillHd y).rTime + c ≤ t
    rw [show c = σ0.consumedTime + (t - σ0.curTime) from hT.2]; exact hs1
  · simp only [Fl4Spec.refillReady, Fl4Spec.refillReady', decide_eq_true_eq, bv_add0]; exact hs2

/-- **A `JAtZ` state at another machine state (same memory) and arch state
keeping `AR`** (the IRQ check). -/
theorem JAtZ.msArJ {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (ms : Fl4Spec.MachineState) (a' : A)
    (hum : ms.underlyingMemory = σ.machineState.underlyingMemory)
    (hAR : AR a σ.archState.x64CurrentCr3 → AR a' σ.archState.x64CurrentCr3) :
    ∃ Lst' : U64 → List U64, JAtZ (L := L) arI AR Z H Cs Ac Lst' D s a' { σ with machineState := ms } :=
  (J.toHole.msAr ms a' hum hAR).toJ J.off J.own

/-- **`JIrqHypZ` per state** (g3e): at every `JAt` state with `NativeScope`
there, no ∀-form `hNS`. -/
theorem jIrqHypZ_ofN (hARI : ARIface arI AR) (hAT : P0.ArchTotal arI) (hIP : IrqPlat arI AR)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄) :
    ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (w : U64) (i : Fl4Spec.Irq),
    JAt (L := L) arI AR s a σ → NativeScope σ → w.val = i.toNat → σ.machineState.irqMasks i = false →
    w.val ≠ 126 → w.val ≠ 127 →
    interrupt.handle_interrupt st arI s a w ⦃ r =>
      (Fl4Spec.handleInterrupt (Z := Unit) i σ).2 ∨
        ∃ z ∈ (Fl4Spec.handleInterrupt (Z := Unit) i σ).1, ∃ Z', XTopAt (L := L) AR Z' r.1 r.2 z.2 ⦄ := by
  intro s a σ w i hJ hN hwi _ h126 h127
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, _⟩ := hJ
  exact J.toHole.handleIrqJN hARI hAT hIP hmb hN (fun hO => absurd ⟨J.off, J.own⟩ hO) w i hwi h126 h127

end

end

end Fl4Proofs.P3
