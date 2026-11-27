/-
P3 (p3J gen 24): **the interrupt entry's footprint composed along P3's joint chain** — `IrqFootWC` [J] (gen 23)
derived from three per-phase footprint premises, with the IRQ handler's non-signal lines proved.

Gen 23 found that the entry footprint cannot come from P1's entry composites (vacuous) and has to be composed along
P3's own chain, which carries the `JAtZ` relation (cap typing, P1's `BlkOK`) to every intermediate state. Here:

* **`pre_projW`**: `update_timestamp` is a P2 `FootN` step (`sched.update_timestamp.kwN`), inside `ProjW` at the
  entry's `JAtZ` (P3JMcKwN); `check_budget` after it by **`BudFootJ`** [J].
* **`irq_projW`**: the IRQ handler at the `JAtZ` state after the budget check — every line that is not a signal
  line is proved (P3JMcIrqH's `JAtZ.handleIrqProjW`: masked / timer / IPI / inactive branches); a signal line by
  **`IrqSigFootJ`** [J].
* **`jEvRef_irqFt` / `jEvRef_irqIFt` / `jEvRef_irqAFt`**: StPostIrqEv's `jEvRef_irqSt` / `jEvRef_irqISt` /
  `jEvRef_irqASt` re-run (same leaves `utCheckBSt` / `utCheckBISt`, `handleIrqJIMSt`) with the footprint as the
  post instead of the finish: the `JAtZ (Z.mv G V) H Cs` states the leaves give after the budget check and after
  the handler are where `irq_projW` and **`FinFootJ`** [J] (the finish) are applied. `CKI` at those spec states:
  `ck_checkBudget` and `ck_handleEvent_other` (P3JCkW / P3JCkS). The three footprints compose by
  `WritesIn.projW_trans`.
* **Stage Q** (as P3JStIrqQ): `jEvRef_irqAFt` transported by IrqFixGen's `specD` (`MachPlat` ↦ `MachPlatT`,
  `IrqPlatA` ↦ `IrqPlatK`), giving `Fl4ProofsQ.P3.jEvRef_irqAFt` at the multicore tops' globals.
* **`irqFootWC_of_J`**: `IrqFootWC` (gen 23's [J]) is a theorem from `BudFootJ`, `IrqSigFootJ`, `FinFootJ` and
  globals the interrupt top already takes. **`kernel_entry_runMcWK_irqJ`**: the interrupt clause `RunMcWK` →
  `RunMcWK` with those three premises in place of `IrqFootWC`.

Named premises (all [J], FL4 footprints at a `JAtZ` state whose spec state is `CKI`, `VxE` ghosts):
* `BudFootJ`: after `update_timestamp` from such a state, `check_budget` writes only `ProjW H Cs`.
* `IrqSigFootJ`: `handle_interrupt` of a line ≤ 127 whose spec state is `IRQSignal` writes only `ProjW H Cs`.
  The composition takes it *or* `NoSig`-at-entry (no line of the entry's spec state is `IRQSignal`; the IRQ
  states are kept by the budget check, `MachF.mfk_checkBudget`), so a run that carries "no signal line" needs no
  `IrqSigFootJ`.
  On a run from FL4's boot this line state cannot arise (CKI excludes `irqControlCap`, so no handler is issued),
  but that is an inductive invariant not yet carried (handoff gen 24).
* `FinFootJ`: `syscall.finish` (schedule, activate, VCPU check) writes only `ProjW H Cs`.
Why they are plausible / what is missing: handoff gen 24. U45nv's globals as in `kernel_entry_runMcWK_irqWC`.
No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JMcIrqH
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Mc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop)

/-- **`BudFootJ` [J]**: from a `CKI` `JAtZ` state, after `update_timestamp`, `check_budget` writes only `ProjW`. -/
def BudFootJ : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit), JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → SInvCk.CKI σ →
    ∀ (s1 : S) (a1 : A), sched.update_timestamp st arI s a = ok (s1, a1) →
      sched.check_budget st arI s1 a1 ⦃ r => P1.WritesIn st s1 r.2.1 (ProjW (L := L) H Cs s1) ⦄

/-- **`IrqSigFootJ` [J]**: at a `CKI` `JAtZ` state, the handler of a signal line writes only `ProjW`. -/
def IrqSigFootJ : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit), JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → SInvCk.CKI σ →
    ∀ w : U64, w.val ≤ 127 → σ.interruptStates (BitVec.ofNat 8 w.val) = .irqSignal →
      interrupt.handle_interrupt st arI s a w ⦃ r => P1.WritesIn st s r.1 (ProjW (L := L) H Cs s) ⦄

/-- **`FinFootJ` [J]**: at a `CKI` `JAtZ` state, `syscall.finish` writes only `ProjW`. -/
def FinFootJ : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit), JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → SInvCk.CKI σ →
      syscall.finish st arI s a ⦃ r => P1.WritesIn st s r.1 (ProjW (L := L) H Cs s) ⦄

variable {arI AR}

/-- The budget prefix of the entry writes only `ProjW` (module docstring). -/
theorem pre_projW (hA : P0.ArchTotal arI) (hBud : BudFootJ (st := st) (L := L) arI AR) {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [hV : VxE Z] (hC : SInvCk.CKI σ) :
    (do let (s1, a1) ← sched.update_timestamp st arI s a; sched.check_budget st arI s1 a1) ⦃ r =>
      P1.WritesIn st s r.2.1 (ProjW (L := L) H Cs s) ⦄ := by
  obtain ⟨Q, R, hq⟩ := J.blk.1
  refine WP.spec_bind (spec_and_eq (sched.update_timestamp.kwN (Kp := ∅) (Nd := False) (T := P1.Heap.tcbs H)
    (Sg := P1.Heap.frame H) (Scs := P1.Heap.scs H) (Z := P1.Heap.scBits H) (Es := EH H) hA s a
    (SchedQueuesInvX.nodes hq) hq.cur) fun _ h => h) ?_
  rintro ⟨s1, a1⟩ ⟨f1, e1⟩
  try simp only [WP.uncurry'_pair] at f1
  have F1 : P1.WritesIn st s s1 (ProjW (L := L) H Cs s) :=
    projW_of_cur0wN J ((WritesA.w f1).mono fun _ hb => Or.inl hb)
  exact WP.spec_mono (hBud Z H Cs Ac Lst D s a σ J hV hC s1 a1 e1) fun r hr => F1.projW_trans hr

/-- The IRQ handler writes only `ProjW` (module docstring). -/
theorem irq_projW (hA : P0.ArchTotal arI) {Z : XSets}
    {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A}
    {σ : Fl4Spec.State Unit}
    (hSig : IrqSigFootJ (st := st) (L := L) arI AR ∨ ∀ j, σ.interruptStates j ≠ .irqSignal) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [hV : VxE Z]
    (hC : SInvCk.CKI σ) (w : U64) :
    interrupt.handle_interrupt st arI s a w ⦃ r => P1.WritesIn st s r.1 (ProjW (L := L) H Cs s) ⦄ := by
  rcases hSig with hSig | hNS
  swap
  · exact JAtZ.handleIrqProjW hA J w fun _ => hNS _
  by_cases h : w.val ≤ 127 ∧ σ.interruptStates (BitVec.ofNat 8 w.val) = .irqSignal
  · exact hSig Z H Cs Ac Lst D s a σ J hV hC w h.1 h.2
  · exact JAtZ.handleIrqProjW hA J w fun hle e => h ⟨hle, e⟩

end

end Fl4Proofs.P3.Mc

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4 Fl4Proofs.P3.Mc

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

open Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvF in
set_option maxHeartbeats 16000000 in
/-- **The interrupt entry from a non-idle thread writes only `ProjW`** (`jEvRef_irqSt`'s run, footprint post;
module docstring). -/
theorem jEvRef_irqFt {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a a' : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] (hX : SInvX σ) (hct : σ.curThread ≠ σ.idleThread)
    (hC : SInvCk.CKI σ) {w : U64} (hI : IrqHw AR MR a a' σ w)
    (hBud : BudFootJ (st := st) (L := L) arI AR)
    (hSig : IrqSigFootJ (st := st) (L := L) arI AR ∨ ∀ j, σ.interruptStates j ≠ .irqSignal)
    (hFn : FinFootJ (st := st) (L := L) arI AR)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.handle_interrupt_entry st arI s a' w ⦃ r => P1.WritesIn st s r.1 (ProjW (L := L) H Cs s) ⦄ := by
  obtain ⟨i, hgl, hwi⟩ := hI.line
  have hni := hX.entered hct
  have hS := hX.sb
  have hNS : NativeScope σ := hS.1.1.ns
  have hMK := hKD.toK
  obtain ⟨Lst0, J0⟩ := J.msArJ σ.machineState a' rfl (hI.ar _)
  have J0' : JAtZ (L := L) arI AR Z H Cs Ac Lst0 D s a' σ := J0
  have hCI : CurInv σ := J.cur.resolve_left (by rw [hni.2]; intro e; cases e)
  have hBu : KBudgetB arI a' σ := ⟨nowAgree_gai hM hI.mr hS.1.1.vmt, hCI, hX.offReady, Or.inr hX.ctQ⟩
  rw [handle_interrupt_entry_eq]
  refine WP.spec_bind (spec_and_eq (WP.spec_and (WP.spec_and
    (J0'.utCheckBSt hni hBu hNS hARI.toARKeep hA hnd hmrt hmb hmax htu)
    (ut_cb_mr hM hMK hA hI.mr s)) (pre_projW hA hBud J0' hC)) fun _ h => h) ?_
  rintro ⟨b, s2, a2⟩ ⟨⟨⟨⟨z, hz, -, G2, V2, Ac2, Lst2, D2, J2⟩, hM2⟩, F1⟩, -⟩
  have hE := Sched.updateTimeStamp_eq' hnd (doMachineOp_single (getCurrentTime_eq σ.machineState))
  have hz0 := hz
  obtain ⟨⟨u, σu⟩, hu, h2⟩ := hz0
  rw [hE] at hu
  have eu : σu = _ := congrArg Prod.snd (Set.mem_singleton_iff.1 hu)
  have hCz : SInvCk.CKI z.2 := SInvCk.ck_checkBudget σu (by rw [eu]; exact hC) z h2
  have hms : σu.machineState = gctState σ.machineState := by rw [eu]
  have his : σu.interruptStates = σ.interruptStates := by rw [eu]
  have hk := MachF.mfk_checkBudget σu _ h2
  have hVu : ValidIrqMasks σu := by
    intro j hj; rw [hms]; exact hS.1.1.vim j (his ▸ hj)
  have hV2 : ValidIrqMasks z.2 := msF_vim hVu hk
  have hk' := hk
  simp only [MachF.msF, Prod.mk.injEq] at hk'
  obtain ⟨k1, k2, k3, k4, k5⟩ := hk'
  have hgl2 : gaiLine false z.2.machineState = some i := by
    rw [gaiLine_congr (ms := σ.machineState) (by rw [k1, hms]; rfl) (by rw [k2, hms]; rfl)]; exact hgl
  set σ3 : Fl4Spec.State Unit := { z.2 with machineState := gaiState z.2.machineState } with hσ3
  have hC3 : SInvCk.CKI σ3 := hCz
  have hSig3 : IrqSigFootJ (st := st) (L := L) arI AR ∨ ∀ j, σ3.interruptStates j ≠ .irqSignal :=
    hSig.imp id fun h j => by show z.2.interruptStates j ≠ _; rw [k5, his]; exact h j
  have hga : Fl4Spec.doMachineOp (Z := Unit) (Fl4Spec.getActiveIRQ false) z.2 = ({(some i, σ3)}, False) := by
    rw [doMachineOp_single (getActiveIRQ_eq false z.2.machineState), hgl2]
  have hR3 : MR a2 σ3.machineState := hM.frame a2 _ _ hM2
    (by show z.2.machineState.irqMasks = _; rw [k1, hms]; rfl)
    (by show z.2.machineState.irqState + 1 = _; rw [k2, hms]; rfl)
    (by show z.2.machineState.timeState = _; rw [k3, hms]; rfl)
    (by show z.2.machineState.lastMachineTime = _; rw [k4, hms]; rfl)
  obtain ⟨Lst3, J3⟩ := J2.msArJ (gaiState z.2.machineState) a2 rfl id
  have hN2 : NativeScope z.2 := ik_bind ns_updateTimeStamp (fun _ => ns_checkBudget) σ hNS z hz
  have hN3 : NativeScope σ3 := SInvN.ns_of_kheap rfl hN2
  have hact3 : σ3.interruptStates i ≠ .irqInactive := by
    intro hin
    have h1 := hV2 i hin
    rw [gaiLine_unmasked hgl2] at h1
    cases h1
  refine WP.spec_bind (WP.spec_and (J3.handleIrqJIMSt hARI hA hIA hM hMK hmb hN3 hR3 w i hwi hI.lt hI.n126
    hI.n127) (irq_projW hA hSig3 J3 hC3 w)) ?_
  rintro ⟨s3, a3⟩ ⟨hP, F2⟩
  rcases hP with hin | ⟨z', hz', ⟨G3, V3, Ac3, Lst4, D3, J4⟩, -⟩
  · exact absurd hin hact3
  have hEv := mem_irqEv hz hga hz'
  have hC4 : SInvCk.CKI z'.2 := SInvCk.ck_handleEvent_other .interrupt (fun c e => by cases e) σ hC _ hEv
  exact WP.spec_mono (hFn _ H Cs Ac3 Lst4 D3 s3 a3 z'.2 J4 inferInstance hC4) fun r hr =>
    (F1.projW_trans F2).projW_trans hr

open Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvF in
set_option maxHeartbeats 16000000 in
/-- **The interrupt entry in the idle thread writes only `ProjW`** (`jEvRef_irqISt`'s run, footprint post). -/
theorem jEvRef_irqIFt {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a a' : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] (hX : SInvX σ) (hid : σ.curThread = σ.idleThread)
    (hC : SInvCk.CKI σ) {w : U64} (hI : IrqHw AR MR a a' σ w)
    (hBud : BudFootJ (st := st) (L := L) arI AR)
    (hSig : IrqSigFootJ (st := st) (L := L) arI AR ∨ ∀ j, σ.interruptStates j ≠ .irqSignal)
    (hFn : FinFootJ (st := st) (L := L) arI AR)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.handle_interrupt_entry st arI s a' w ⦃ r => P1.WritesIn st s r.1 (ProjW (L := L) H Cs s) ⦄ := by
  obtain ⟨i, hgl, hwi⟩ := hI.line
  have hres : σ.schedulerAction = .resumeCurThread := hX.cr.2
  have hS := hX.sb
  have hMK := hKD.toK
  have hNS : NativeScope σ := hS.1.1.ns
  obtain ⟨Lst0, J0⟩ := J.msArJ σ.machineState a' rfl (hI.ar _)
  have J0' : JAtZ (L := L) arI AR Z H Cs Ac Lst0 D s a' σ := J0
  have hCI : CurInv σ := J.cur.resolve_left (by rw [hres]; intro e; cases e)
  have hBu : KBudgetB arI a' σ := ⟨nowAgree_gai hM hI.mr hS.1.1.vmt, hCI, hX.offReady, Or.inr hX.ctQ⟩
  rw [handle_interrupt_entry_eq]
  refine WP.spec_bind (spec_and_eq (WP.spec_and (WP.spec_and
    (J0'.utCheckBISt hres hid hBu hARI.toARKeep hA hnd hmrt hmb hmax htu)
    (ut_cb_mr hM hMK hA hI.mr s)) (pre_projW hA hBud J0' hC)) fun _ h => h) ?_
  rintro ⟨b, s2, a2⟩ ⟨⟨⟨⟨z, hz, -, G2, V2, Ac2, Lst2, D2, J2⟩, hM2⟩, F1⟩, -⟩
  have hE := Sched.updateTimeStamp_eq' hnd (doMachineOp_single (getCurrentTime_eq σ.machineState))
  have hz0 := hz
  obtain ⟨⟨u, σu⟩, hu, h2⟩ := hz0
  rw [hE] at hu
  have eu : σu = _ := congrArg Prod.snd (Set.mem_singleton_iff.1 hu)
  have hCz : SInvCk.CKI z.2 := SInvCk.ck_checkBudget σu (by rw [eu]; exact hC) z h2
  have hms : σu.machineState = gctState σ.machineState := by rw [eu]
  have his : σu.interruptStates = σ.interruptStates := by rw [eu]
  have hk := MachF.mfk_checkBudget σu _ h2
  have hVu : ValidIrqMasks σu := by
    intro j hj; rw [hms]; exact hS.1.1.vim j (his ▸ hj)
  have hV2 : ValidIrqMasks z.2 := msF_vim hVu hk
  have hk' := hk
  simp only [MachF.msF, Prod.mk.injEq] at hk'
  obtain ⟨k1, k2, k3, k4, k5⟩ := hk'
  have hgl2 : gaiLine false z.2.machineState = some i := by
    rw [gaiLine_congr (ms := σ.machineState) (by rw [k1, hms]; rfl) (by rw [k2, hms]; rfl)]; exact hgl
  set σ3 : Fl4Spec.State Unit := { z.2 with machineState := gaiState z.2.machineState } with hσ3
  have hC3 : SInvCk.CKI σ3 := hCz
  have hSig3 : IrqSigFootJ (st := st) (L := L) arI AR ∨ ∀ j, σ3.interruptStates j ≠ .irqSignal :=
    hSig.imp id fun h j => by show z.2.interruptStates j ≠ _; rw [k5, his]; exact h j
  have hga : Fl4Spec.doMachineOp (Z := Unit) (Fl4Spec.getActiveIRQ false) z.2 = ({(some i, σ3)}, False) := by
    rw [doMachineOp_single (getActiveIRQ_eq false z.2.machineState), hgl2]
  have hR3 : MR a2 σ3.machineState := hM.frame a2 _ _ hM2
    (by show z.2.machineState.irqMasks = _; rw [k1, hms]; rfl)
    (by show z.2.machineState.irqState + 1 = _; rw [k2, hms]; rfl)
    (by show z.2.machineState.timeState = _; rw [k3, hms]; rfl)
    (by show z.2.machineState.lastMachineTime = _; rw [k4, hms]; rfl)
  obtain ⟨Lst3, J3⟩ := J2.msArJ (gaiState z.2.machineState) a2 rfl id
  have hN2 : NativeScope z.2 := ik_bind ns_updateTimeStamp (fun _ => ns_checkBudget) σ hNS z hz
  have hN3 : NativeScope σ3 := SInvN.ns_of_kheap rfl hN2
  have hact3 : σ3.interruptStates i ≠ .irqInactive := by
    intro hin
    have h1 := hV2 i hin
    rw [gaiLine_unmasked hgl2] at h1
    cases h1
  refine WP.spec_bind (WP.spec_and (J3.handleIrqJIMSt hARI hA hIA hM hMK hmb hN3 hR3 w i hwi hI.lt hI.n126
    hI.n127) (irq_projW hA hSig3 J3 hC3 w)) ?_
  rintro ⟨s3, a3⟩ ⟨hP, F2⟩
  rcases hP with hin | ⟨z', hz', ⟨G3, V3, Ac3, Lst4, D3, J4⟩, -⟩
  · exact absurd hin hact3
  have hEv := mem_irqEv hz hga hz'
  have hC4 : SInvCk.CKI z'.2 := SInvCk.ck_handleEvent_other .interrupt (fun c e => by cases e) σ hC _ hEv
  exact WP.spec_mono (hFn _ H Cs Ac3 Lst4 D3 s3 a3 z'.2 J4 inferInstance hC4) fun r hr =>
    (F1.projW_trans F2).projW_trans hr

set_option maxHeartbeats 8000000 in
/-- **The interrupt entry from any current thread writes only `ProjW`** (module docstring). -/
theorem jEvRef_irqAFt {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a a' : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] (hX : SInvX σ)
    (hC : SInvCk.CKI σ) {w : U64} (hI : IrqHw AR MR a a' σ w)
    (hBud : BudFootJ (st := st) (L := L) arI AR)
    (hSig : IrqSigFootJ (st := st) (L := L) arI AR ∨ ∀ j, σ.interruptStates j ≠ .irqSignal)
    (hFn : FinFootJ (st := st) (L := L) arI AR)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.handle_interrupt_entry st arI s a' w ⦃ r => P1.WritesIn st s r.1 (ProjW (L := L) H Cs s) ⦄ := by
  by_cases hct : σ.curThread = σ.idleThread
  · exact jEvRef_irqIFt J hX hct hC hI hBud hSig hFn hARI hA hnd hM hKD hIA hmrt hmb hmax htu
  · exact jEvRef_irqFt J hX hct hC hI hBud hSig hFn hARI hA hnd hM hKD hIA hmrt hmb hmax htu

end

end

end Fl4Proofs.P3
