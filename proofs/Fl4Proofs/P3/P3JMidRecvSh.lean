/-
P3 (p3J gen 51): **`MidRecvSw` reduced to the three stable receive leaves at a mid state** (the receive shell
without `Entered`, the first-phase fact `CtOK`, `CanBlock` at every mid state and the three `ProjW` footprints
proved; gen 49's items 1, 5 and 6).

`MidRecvSw` (P3JMidCls) asks `handle_recv true cr` at an `ok` outcome `y` of the spec's first phase from a dispatch
state, with `MidStF y.2` and `y.2.schedulerAction ≠ resumeCurThread`, to end in `RecvRelSF Z H Cs`. Here:

* **`JAtZ.canBlockMid`**: P1's `CanBlock` of the current thread at every `JAtZ` state with `MidStF` and `CtOK`
  (resumed: `canBlockCurG`; a switch to another thread: XTopJointRecvMid's `canBlockCurM` with `CurInv` from
  `JAtZ.curInv`; `chooseNewThread` with `CurInv`: XTopJointRecvSigC's `canBlockCurMC`; `chooseNewThread`, ct without
  an SC: `canBlockCurG`'s SC-less branch with XTopJointKEntry22M's `Sched.Inv.notRel_of_noSc`).
* **`recvSigFtB`**: the notification receive writes only `ProjW H Cs s` given `CanBlock` (gen 28's
  `Mc.recvSignalProjW`, P3JSigSt's `ntfn_epState3`). With P3JMidCls's `recvIpcFtB` and P3JMcFlt's `faultProjWB`
  (both generalised in place this gen from `recvIpcFtE` / `faultProjW`, which are now their instances) the three
  leaves' footprints hold at every mid state.
* **`ctOK_disp`**: `CtOK` at every outcome of the first phase from a dispatch state of the entry: XTopJointChooseB's
  `jMidChooseFact` with `CQ ∧ NQ` from P3JMidSpec's `midEntry_disp`, `CurInv` and `Sched.Inv` from the dispatch
  state's `JAtZ` (`Entered` there), `JMidPerfHypQ` / `JMidPerfHypB` from XTopJointPerfI's `jMidPerfHypQ_of2` /
  `jMidPerfHypB_of2` on XTopJointKEntry27b's `jPerfRegHyp_27b` / `jPerfIrqSlotHyp_27b` (from `SInvB σ`).
* **`RecvRelS Z H Cs`**: `RelTopM ∧ JStabR Z H Cs` (`RecvRelSF` without the footprint).
* **`RecvLvSt Z H Cs ct`**: the three blocking receive leaves (endpoint receive, notification receive, cap fault;
  XTopJointKEntry10M's `JRecvLeavesR` shape) ending in `RecvRelS Z H Cs`.
* **`handle_recvMidSw`**: at a `JAtZ (Z.mv G V)` state with `MidStF` and `CtOK`, `RecvLvSt` gives `handle_recv true
  cr` in `RecvRelSF Z H Cs`: P3JRecvCls's `handle_recvJStL` (the shell of `handle_recvJSt` without `Entered`,
  generalised in place this gen) with each leaf's footprint from `canBlockMid`.
* **`MidRecvLv` [J]**: `RecvLvSt` at the states `MidRecvSw` speaks of (same antecedents, `RecvLvSt (Z.mv G V) H Cs
  ct` for the current thread `ct` of the mid state). **`midRecvSw_of_lv`**: `MidRecvLv → MidRecvSw` from the entry
  state's `JAtZ`, `SInvX` and a non-idle current thread.

Narrowing honesty: `MidRecvLv` speaks of sub-calls of `handle_recv` (the leaves, at every held cap), so it is not
implied by `MidRecvSw` (as gen 30's `recvIpc`); it implies it (`midRecvSw_of_lv`). So no new top: the brief asks for
both directions. What `MidRecvLv` still asks is exactly gen 49's items 2–4 at stable ghosts, without footprints: the
non-stable proofs exist (XTopJointKEntry11M … 27MD, leaves ending in `RJR`).

Named premises: `MidRecvLv` [J] (above; not in a top). No sorry. New module; existing statements unchanged
(`handle_recvJSt`, `faultProjW`, `recvIpcFtE` are one-call instances of their generalisations).
-/
import Fl4Proofs.P3.P3JMidSpec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Mc
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.JBoot Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs Fl4Proofs.P3.JBootQ
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 51) **P1's `CanBlock` of the current thread at a mid state** (module docstring). -/
theorem JAtZ.canBlockMid {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) (hF : MidStF σ) (hok : MidRun.CtOK σ) :
    P1.CanBlock st (P1.Heap.tcbs H) Ac s ct := by
  obtain ⟨hcur, x, hk⟩ := J.curEq hct
  have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hk' : σ.kheap σ.curThread = some (.tcb x) := by rw [hcur]; exact hk
  have hrn : Fl4Spec.runnable x.tcbState = true := hF.run x hk'
  cases hsa : σ.schedulerAction with
  | resumeCurThread =>
    have hC : CurInv σ := J.curInv (by rw [hsa]; intro e; cases e)
    exact J.canBlockCurG hctT hcur hk hrn hF.ni (by rw [← hcur]; exact hC.notRel) (Or.inl hsa) hF.nq
  | switchThread u =>
    have hC : CurInv σ := J.curInv (by rw [hsa]; intro e; cases e)
    have hu : u ≠ ct.bv := by
      intro e; apply hF.nsw; rw [hsa, e, hcur]
    exact J.canBlockCurM hctT hcur hk hrn hF.ni (by rw [← hcur]; exact hC.notRel) (Or.inr (Or.inr ⟨u, hsa, hu⟩))
      hF.nq
  | chooseNewThread =>
    rcases hok with hC | ⟨y, hy, h0⟩
    · exact J.canBlockCurMC hctT hcur hk hrn hF.ni (by rw [← hcur]; exact hC.notRel) ⟨hF.ni, hF.run, hsa, hC⟩
        hF.nq
    · rw [hk'] at hy; cases hy
      exact J.canBlockCurG hctT hcur hk hrn hF.ni (by rw [← hcur]; exact J.inv.notRel_of_noSc hk' h0)
        (Or.inr ⟨hsa, h0⟩) hF.nq

set_option maxHeartbeats 4000000 in
/-- (p3J gen 51) **The notification receive writes only `ProjW H Cs s`** where the current thread can block
(module docstring). -/
theorem recvSigFtB (hAT : P0.ArchTotal arI) {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64}
    {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {ct : U64} (hcb : P1.CanBlock st (P1.Heap.tcbs H) Ac s ct) (blocking : Bool) {p : U64}
    {x : Fl4Spec.Notification} (hk : σ.kheap p.bv = some (.notification x)) :
    notification.receive_signal st arI s a ct p blocking ⦃ r =>
      P1.WritesIn st s r.1 (Mc.ProjW (L := L) H Cs s) ⦄ := by
  obtain ⟨-, hHn, h3⟩ := ntfn_epState3 J hk
  obtain ⟨⟨Q0, R0, h0⟩, hB0, hX0, hS0, hSg0⟩ := J.blk
  refine WP.spec_mono (Mc.recvSignalProjW (L := L) hAT J.kern.heap s a ct p blocking Q0 R0 h0 hB0 hX0 hS0 hSg0 hcb
    hHn hHn h3) ?_
  rintro ⟨s', a'⟩ hW
  simpa only [WP.uncurry'_pair] using hW

set_option maxHeartbeats 4000000 in
/-- (p3J gen 51) **`CtOK` at every outcome of the first phase from a dispatch state of the entry** (module
docstring). -/
theorem ctOK_disp (hnd : Fl4Spec.numDomains = 1) {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ σb : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hX : SInvX σ) (hct : σ.curThread ≠ σ.idleThread)
    (hBA : BudgetAt σ σb true) {Z' : XSets} {H' : P1.Heap} {Cs' Ac' : Set U64} {Lst' : U64 → List U64}
    {D' : Set U64} {s' : S} {a' : A} (J' : JAtZ (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' σb)
    (cptr : Fl4Spec.CapRef) :
    ∀ y ∈ ((Fl4Spec.fl4HandleInvocationR (Z := Unit) true false false true true cptr).run σb).1,
      MidRun.CtOK y.2 := by
  have hS := hX.sb
  obtain ⟨hnib, hcq, hnqb⟩ := midEntry_disp hnd J hX hct hBA
  have hC : CurInv σb := J'.cur.resolve_left (by rw [hnib.2]; intro e; cases e)
  exact MidRun.jMidChooseFact true true cptr σb hcq hnqb hC J'.inv
    (MidRun.jMidPerfHypQ_of2 hcq hnqb (jPerfRegHyp_27b hnd hS hct hBA cptr) (jPerfIrqSlotHyp_27b hnd hS hBA cptr))
    (MidRun.jMidPerfHypB_of2 hcq hnqb (jPerfRegHyp_27b hnd hS hct hBA cptr) (jPerfIrqSlotHyp_27b hnd hS hBA cptr))

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- (p3J gen 51) **The relation a stable receive leaf ends in** (`RecvRelSF` without the footprint). -/
def RecvRelS (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit) : Prop :=
  RelTopM (L := L) s1 σ1 ∧ JStabR (L := L) arI AR Z H Cs s1 a1 σ1

/-- (p3J gen 51) **The three blocking receive leaves at stable ghosts** (module docstring; XTopJointKEntry10M's
`JRecvLeavesR` with the post `RecvRelS Z H Cs`). -/
structure RecvLvSt (Z : XSets) (H : P1.Heap) (Cs : Set U64) (ct : U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) :
    Prop where
  ipc : ∀ p b sd g gr rc rc', (∃ x, σ.kheap p.bv = some (.endpoint x)) →
    ((rc = .Null ∧ rc' = .nullCap) ∨
      (CapRel rc rc' ∧ ∃ q g', rc = .Reply q g' ∧ ∃ x, σ.kheap q.bv = some (.reply x))) →
    JHeld (L := L) Z.th s (.Endpoint p b sd true g gr) → (∀ q g', rc = .Reply q g' → JHeld (L := L) Z.th s rc) →
    endpoint.receive_ipc st arI s a ct (.Endpoint p b sd true g gr) true rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) true rc' σ).1,
        RecvRelS (L := L) arI AR Z H Cs r.1 r.2 z.2 ⦄
  sig : ∀ p b w rd ac, CapRel (.Notification p b w rd) ac → (∃ x, σ.kheap p.bv = some (.notification x)) →
    JHeld (L := L) Z.th s (.Notification p b w rd) →
    notification.receive_signal st arI s a ct p true ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveSignal (Z := Unit) ct.bv ac true σ).1, RecvRelS (L := L) arI AR Z H Cs r.1 r.2 z.2 ⦄
  flt : ∀ cptr lf lf', LookupFaultRel lf lf' →
    faults.handle_fault st arI s a ct (.Cap cptr true lf) ⦃ r =>
      ∃ z ∈ (Fl4Spec.handleFault (Z := Unit) ct.bv (.capFault (Fl4Spec.ofBl (Fl4Spec.toBl cptr.bv)) true lf') σ).1,
        RecvRelS (L := L) arI AR Z H Cs r.1 r.2 z.2 ⦄

/-- (p3J gen 51) **`MidRecvLv` [J]**: the stable receive leaves at the mid states `MidRecvSw` speaks of (module
docstring). -/
def MidRecvLv (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64)
    (c : Fl4Spec.Syscall) : Prop :=
  ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A),
    KFrontB (L := L) arI s a s' a' → JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
    MR a' σb.machineState → SInvCk.CKI σb → SInvRr.RR σb →
    ∀ ct rg sr cr, sched.cur_thread st s' = ok ct → MidSysR n c rg sr cr →
    ∀ y ∈ ((Fl4Spec.fl4HandleInvocationR (Z := Unit) true false false true true
        (Fl4Spec.toBl (L.mem s' (Endp.regA ct rg)).bv)).run σb).1, y.1 = .ok () →
      y.2.schedulerAction ≠ .resumeCurThread → MidStF y.2 →
      ∀ (G : MdbGhost) (V : XVs) (Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s1 : S) (a1 : A),
        JAtZ (L := L) arI AR (Z.mv G V) H Cs Ac Lst D s1 a1 y.2 → ∀ ct1, sched.cur_thread st s1 = ok ct1 →
        RecvLvSt (L := L) arI AR (Z.mv G V) H Cs ct1 s1 a1 y.2

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 51) **The receive at a mid state from its stable leaves** (module docstring). -/
theorem handle_recvMidSw (hA : P0.ArchTotal arI) {Z : XSets} {H : P1.Heap} {Cs : Set U64} {G : MdbGhost}
    {V : XVs} {Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} {s1 : S} {a1 : A} {σm : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR (Z.mv G V) H Cs Ac Lst D s1 a1 σm) (hF : MidStF σm) (hok : MidRun.CtOK σm)
    {ct : U64} (hct : sched.cur_thread st s1 = ok ct) (hL : RecvLvSt (L := L) arI AR (Z.mv G V) H Cs ct s1 a1 σm)
    (cr : Bool) :
    syscall.handle_recv st arI s1 a1 true cr ⦃ r => ∃ z ∈ (Fl4Spec.handleRecv (Z := Unit) true cr σm).1,
      RecvRelSF (L := L) arI AR Z H Cs s1 r.1 r.2 z.2 ⦄ := by
  have hcb := JAtZ.canBlockMid J hct hF hok
  refine WP.spec_mono (handle_recvJStL (Z := Z.mv G V) (V := V) hA s1 a1 σm J hct true cr ?_ ?_ ?_) ?_
  · intro p b sd g gr rc rc' hpE hrc hHd hHr
    refine WP.spec_mono (WP.spec_and (hL.ipc p b sd g gr rc rc' hpE hrc hHd hHr)
      (recvIpcFtB hA J hF.cki hcb true p b sd g gr rc hHd hHr)) ?_
    rintro r ⟨⟨z, hz, hr1, hr2⟩, hW⟩
    exact ⟨z, hz, hr1, hr2, hW⟩
  · intro p b w rd ac hcr hex hHd
    obtain ⟨x, hk⟩ := hex
    refine WP.spec_mono (WP.spec_and (hL.sig p b w rd ac hcr ⟨x, hk⟩ hHd) (recvSigFtB hA J hcb true hk)) ?_
    rintro r ⟨⟨z, hz, hr1, hr2⟩, hW⟩
    exact ⟨z, hz, hr1, hr2, hW⟩
  · intro cptr lf lf' h
    refine WP.spec_mono (WP.spec_and (hL.flt cptr lf lf' h) (faultProjWB hA J hF.cki hct hcb (.Cap cptr true lf))) ?_
    rintro r ⟨⟨z, hz, hr1, hr2⟩, hW⟩
    exact ⟨z, hz, hr1, hr2, hW⟩
  · rintro r ⟨z, hz, hr1, hr2, hW⟩
    exact ⟨z, hz, hr1, JStabR.mv hr2, hW⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 51) **`MidRecvLv → MidRecvSw`** (module docstring). -/
theorem midRecvSw_of_lv (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    {n : I64} {c : Fl4Spec.Syscall} (h : MidRecvLv (L := L) arI AR MR Z H Cs s a σ n c) :
    MidRecvSw (L := L) arI AR MR Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J' hMR hCb hRR ct rg sr cr hct hm y hy hok hnr hF G V Ac1 Lst1 D1 s1 a1 J1
  have hct1 := cur_thread_eq (L := L) s1
  generalize L.mem s1 (L.nodeAt s1 (L.cpu s1) layout.node.CUR_THREAD) = ct1 at hct1
  exact handle_recvMidSw hA J1 hF (ctOK_disp hnd J hX hni hBA J' _ y hy) hct1
    (h σb hBA V' Ac' Lst' D' s' a' hKF J' hMR hCb hRR ct rg sr cr hct hm y hy hok hnr hF G V Ac1 Lst1 D1 s1 a1 J1 ct1
      hct1) cr

end

end

end Fl4Proofs.P3.Mc
