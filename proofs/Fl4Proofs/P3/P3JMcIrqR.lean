/-
P3 (p3J gen 25): **the budget check on a round-robin run writes only `ProjW`** — `BudFootJ` [J] discharged at the
entry states of `RR` runs, and the interrupt footprint chain re-run with it.

* **`budFoot_rr`** (no premise): at a `JAtZ` state whose spec action is resume (every kernel entry, `SInvX`'s `RS`)
  and whose spec state is `RR` (P3JRrSys: every SC has period `0`), after `update_timestamp` the FL4 `check_budget`
  writes only `ProjW H Cs`. Proof: P1's `EntryInv` at the entry (`JAtZ.entryInv`), its post-timestamp facts
  (`sched.update_timestamp.entry`); the current SC's FL4 period word is `0` (`ScRelW.period` with `rr_period`) and
  `update_timestamp` writes only the current node (`.fr`, the period word lies outside every node, `out_ne_node`);
  so P2's round-robin `sched.check_budget.rr` applies (no timeout fault), a `FootN ∅ False` step, inside `ProjW` by
  P3JMcKwN's `cur0wN_projW` at the post-timestamp nodes.
* **`pre_projW_rr`**: P3JMcIrqF's `pre_projW` with `budFoot_rr` for `BudFootJ`.
* **`jEvRef_irqFtR` / `jEvRef_irqIFtR` / `jEvRef_irqAFtR`**: P3JMcIrqF's three chain theorems with `RR σ` in
  place of `BudFootJ` (text copy: `hBud` ↦ `hRR`, `pre_projW hA hBud J0' hC` ↦ `pre_projW_rr hA J0' hX.cr.2 hRR`).

Named premises: `IrqSigFootJ` (or `NoSig`) and `FinFootJ` [J] as in P3JMcIrqF; no `BudFootJ`.
No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JMcIrqF
import Fl4Proofs.P3.P3JRrSys
import Fl4Proofs.P3.XTopJointEntryInv29
import Fl4Proofs.P2.EntryIrq
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Mc
open fl4_core Classical Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Stall

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop}

set_option maxHeartbeats 4000000 in
/-- **On a round-robin run the budget check writes only `ProjW`** (module docstring). -/
theorem budFoot_rr (hA : P0.ArchTotal arI) {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hres : σ.schedulerAction = .resumeCurThread)
    (hRR : SInvRr.RR σ) (s1 : S) (a1 : A) (e1 : sched.update_timestamp st arI s a = ok (s1, a1)) :
    sched.check_budget st arI s1 a1 ⦃ r => P1.WritesIn st s1 r.2.1 (ProjW (L := L) H Cs s1) ⦄ := by
  have hI := J.entryInv hres
  have hI' := hI
  obtain ⟨⟨Q0, R0, h0⟩, -, hX0, -, -, -, -, -⟩ := hI'
  have U1 := sched.update_timestamp.entry hA s a hI
  have U2 := sched.update_timestamp.fr hA s a (h0.nodes _ h0.cur)
  rw [e1] at U1 U2
  simp only [WP.spec_ok, WP.uncurry'_pair] at U1 U2
  obtain ⟨⟨⟨Q1, R1, hq1⟩, hB1, hX1, hSg1, hS1⟩, ecs1, hcA1, hna1, hcsc1, -⟩ := U1
  -- the spec period of the current SC is `0`, so is FL4's
  have hC : CurInv σ := J.curInv (by rw [hres]; intro e; cases e)
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0', hc, hs⟩ := hS.lists
  obtain ⟨hscC, -, -, -, -, -, -⟩ := CurInv.facts hS J.inv hC
  have ecsc : L.cscW s = nodeW st s Z.c layout.node.CUR_SC := by
    show L.mem s (L.nodeAt s (L.cpu s) _) = _; rw [hc.cur]; rfl
  obtain ⟨x, n, hk, hx⟩ := hs.scs _ hscC
  have hx0 : x.scPeriod = 0 := SInvRr.rr_period hRR hk
  have hp0 : L.rperiod s (L.cscW s) = 0#u64 := by
    rw [ecsc]; exact P1.eq_of_bv (by rw [← hx.period, hx0]; rfl)
  -- `update_timestamp` writes only the current node: the period word is kept
  have hcS : L.cscW s ∈ P1.Heap.scs H := hX0.2.2.cur
  obtain ⟨hP, hz⟩ := hX0.1.sc _ hcS
  obtain ⟨h8c, h128, -⟩ := sc_lo hP hz
  have hpz : layout.sc.PERIOD.val = 0 := by simp [layout.sc.PERIOD]
  have hpv : (periodA (L.cscW s)).val = (L.cscW s).val := by
    unfold periodA; rw [sc_word_val (o := layout.sc.PERIOD) hP hz (by rw [hpz]; omega), hpz, Nat.add_zero]
  have hal : Aligned (periodA (L.cscW s)) := by unfold Aligned; rw [hpv]; exact h8c
  have hpin : InSC (L.cscW s) (P1.Heap.scBits H (L.cscW s)) (periodA (L.cscW s)) := ⟨by omega, by omega⟩
  have hp1 : L.rperiod s1 (L.cscW s1) = 0#u64 := by
    rw [ecs1, ← hp0]
    unfold LawfulStore.rperiod
    refine U2.mem_eq hal ?_
    rintro ⟨o, -, ho, -, e⟩
    exact out_ne_node (h0.omega _ (hX0.1.scW _ hcS _ hal hpin)) h0.cur (h0.nodes _ h0.cur) ho
      (congrArg UScalar.val e).symm
  refine WP.spec_mono (sched.check_budget.rr (Kp := ∅) (Nd := False) (Es := (∅ : Set U64)) hA s1 a1 Q1 R1 hq1
    hB1 hX1 hSg1 hS1 hcsc1 hna1 hcA1 (fun _ h => h) (fun _ _ _ => ⟨hp1, fun h => h⟩)) ?_
  rintro ⟨b, s2, a2⟩ hr
  try simp only [WP.uncurry'_pair] at hr
  obtain ⟨-, F, -, -⟩ := hr
  exact (WritesA.w F).mono fun _ hb => cur0wN_projW J.kern.heap (hq1.nodes) (Or.inl hb)

/-- `pre_projW` with `budFoot_rr` for `BudFootJ` (module docstring). -/
theorem pre_projW_rr (hA : P0.ArchTotal arI) {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hres : σ.schedulerAction = .resumeCurThread)
    (hRR : SInvRr.RR σ) :
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
  exact WP.spec_mono (budFoot_rr hA J hres hRR s1 a1 e1) fun r hr => F1.projW_trans hr

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
theorem jEvRef_irqFtR {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a a' : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] (hX : SInvX σ) (hct : σ.curThread ≠ σ.idleThread)
    (hC : SInvCk.CKI σ) {w : U64} (hI : IrqHw AR MR a a' σ w)
    (hRR : SInvRr.RR σ)
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
    (ut_cb_mr hM hMK hA hI.mr s)) (pre_projW_rr hA J0' hX.cr.2 hRR)) fun _ h => h) ?_
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
theorem jEvRef_irqIFtR {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a a' : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] (hX : SInvX σ) (hid : σ.curThread = σ.idleThread)
    (hC : SInvCk.CKI σ) {w : U64} (hI : IrqHw AR MR a a' σ w)
    (hRR : SInvRr.RR σ)
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
    (ut_cb_mr hM hMK hA hI.mr s)) (pre_projW_rr hA J0' hX.cr.2 hRR)) fun _ h => h) ?_
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
theorem jEvRef_irqAFtR {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a a' : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] (hX : SInvX σ)
    (hC : SInvCk.CKI σ) {w : U64} (hI : IrqHw AR MR a a' σ w)
    (hRR : SInvRr.RR σ)
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
  · exact jEvRef_irqIFtR J hX hct hC hI hRR hSig hFn hARI hA hnd hM hKD hIA hmrt hmb hmax htu
  · exact jEvRef_irqFtR J hX hct hC hI hRR hSig hFn hARI hA hnd hM hKD hIA hmrt hmb hmax htu

end

end

end Fl4Proofs.P3
