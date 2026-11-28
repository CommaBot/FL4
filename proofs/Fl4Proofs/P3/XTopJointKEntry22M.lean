/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN sch22 (c3)): **`kernel_entryJ22M`:
the endpoint receive with a linked reply at a `chooseNewThread` mid state
with `CurInv`.** `JMidLeavesHyp12` [W] (XTopJointKEntry21M) asked
`receive_ipc` under `chooseNewThread ∧ (¬ CurInv ∨ IpcLinked)`. At a `MidC`
state with a linked reply it is XTopJointRecvIpcLinkC's `jRecvIpcLinkC`
(the spec's cancel of the linked thread keeps `CurInv`: `cancelLink_curInv`).
`JRecvLeavesRN13` asks every receive leaf only under
`chooseNewThread ∧ ¬ CurInv`; `.toRN12`; `JMidLeavesHyp13` [W] =
`JMidLeavesHyp12` concluding `JRecvLeavesRN13`, `jMidLeavesHyp_of13`,
`KDispHyps22M`, `.to21M`, NEW TOP `kernel_entryJ22M`.

`Inv.notRel_of_noSc` (for the SC-less leaves still asked): a thread without
an SC is in no release queue (`Inv.rel`).
-/
import Fl4Proofs.P3.XTopJointRecvIpcLinkC
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-- **A thread without an SC is in no release queue** (`Inv.rel`). -/
theorem Sched.Inv.notRel_of_noSc {σ : Fl4Spec.State Unit} (hI : Sched.Inv σ) {t : Fl4Spec.ObjRef}
    {x : Fl4Spec.Tcb} (hk : σ.kheap t = some (.tcb x)) (hsc : x.tcbSchedContext = none) :
    t ∉ σ.releaseQueue := fun hm => by
  obtain ⟨x0, scp, -, -, hk0, hs0, -⟩ := hI.rel t hm
  rw [hk] at hk0; cases hk0
  rw [hsc] at hs0; cases hs0

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JRecvLeavesRN12` with every receive leaf asked only where `CurInv`
fails** (module docstring). -/
structure JRecvLeavesRN13 (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) (ct : U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop where
  ipc : ∀ p b sd g gr rc rc', (∃ x, σ.kheap p.bv = some (.endpoint x)) →
    ((rc = .Null ∧ rc' = .nullCap) ∨
      (CapRel rc rc' ∧ ∃ q g', rc = .Reply q g' ∧ ∃ x, σ.kheap q.bv = some (.reply x))) →
    JHeld (L := L) th s (.Endpoint p b sd true g gr) → (∀ q g', rc = .Reply q g' → JHeld (L := L) th s rc) →
    σ.schedulerAction = .chooseNewThread → ¬ CurInv σ →
    endpoint.receive_ipc st arI s a ct (.Endpoint p b sd true g gr) true rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) true rc' σ).1,
        RJR (L := L) arI AR r.1 r.2 z.2 ⦄
  sig : ∀ p b w rd ac, CapRel (.Notification p b w rd) ac → (∃ x, σ.kheap p.bv = some (.notification x)) →
    JHeld (L := L) th s (.Notification p b w rd) → σ.schedulerAction = .chooseNewThread → ¬ CurInv σ →
    notification.receive_signal st arI s a ct p true ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveSignal (Z := Unit) ct.bv ac true σ).1, RJR (L := L) arI AR r.1 r.2 z.2 ⦄
  flt : ∀ cptr lf lf', LookupFaultRel lf lf' → σ.schedulerAction = .chooseNewThread → ¬ CurInv σ →
    faults.handle_fault st arI s a ct (.Cap cptr true lf) ⦃ r =>
      ∃ z ∈ (Fl4Spec.handleFault (Z := Unit) ct.bv (.capFault (Fl4Spec.ofBl (Fl4Spec.toBl cptr.bv)) true lf') σ).1,
        RJR (L := L) arI AR r.1 r.2 z.2 ⦄

/-- **[W] The receive leaves at a non-resumed mid state, every leaf
narrowed to `chooseNewThread ∧ ¬ CurInv`** (module docstring):
`JMidLeavesHyp12` concluding `JRecvLeavesRN13`. -/
def JMidLeavesHyp13 (AR : A → Fl4Spec.Cr3 → Prop) (cptr : Fl4Spec.CapRef) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ y ∈ ((Fl4Spec.fl4HandleInvocationR (Z := Unit) true false false true true cptr).run σ).1, y.1 = .ok () →
    y.2.schedulerAction ≠ .resumeCurThread → (∀ d p, y.2.curThread ∉ y.2.readyQueues d p) →
    y.2.schedulerAction ≠ .switchThread y.2.curThread →
    (∀ x, y.2.kheap y.2.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler) →
    ∀ (s1 : S) (a1 : A), RelTopM (L := L) s1 y.2 → CurRun y.2 → y.2.curThread ≠ y.2.idleThread →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s1 a1 y.2 → [VxE Z] → ∀ ct, sched.cur_thread st s1 = ok ct →
        JRecvLeavesRN13 (L := L) arI AR Z.th ct s1 a1 y.2

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop}

/-- **`JRecvLeavesRN12` from `JRecvLeavesRN13`**: the endpoint receive with
a linked reply at a `MidC` state by `jRecvIpcLinkC`. -/
theorem JRecvLeavesRN13.toRN12 (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] {ct : U64} (hct : sched.cur_thread st s = ok ct)
    (hni1 : σ.curThread ≠ σ.idleThread) (hrun : CurRun σ) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (h : JRecvLeavesRN13 (L := L) arI AR Z.th ct s a σ) : JRecvLeavesRN12 (L := L) arI AR Z.th ct s a σ where
  sig := h.sig
  flt := h.flt
  ipc := fun p b sd g gr rc rc' hpE hrc hHd hHr ho hl => by
    by_cases hC : CurInv σ
    · obtain ⟨q, g', rfl, hi0⟩ := hl.resolve_left (fun h => h hC)
      obtain ⟨hcur, -⟩ := J.curEq hct
      have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
      have hE : MidC σ := ⟨hni1, hrun, ho, hC⟩
      rcases hrc with ⟨h0, -⟩ | ⟨hcr, q', g'', e, xr, hkr⟩
      · cases h0
      · cases e
        exact jRecvIpcLinkC hAT hmax htu J hctT hcur hE hnq p b sd g gr q g' rc' hpE hcr hkr hHd
          (hHr q g' rfl) hi0
    · exact h.ipc p b sd g gr rc rc' hpE hrc hHd hHr ho hC

/-- **`JMidLeavesHyp12` from `JMidLeavesHyp13`** (module docstring). -/
theorem jMidLeavesHyp_of13 (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    {cptr : Fl4Spec.CapRef} {σ : Fl4Spec.State Unit}
    (hL : JMidLeavesHyp13 (L := L) arI AR cptr σ) : JMidLeavesHyp12 (L := L) arI AR cptr σ := by
  intro y hy hok ha hnq hsw hvf s1 a1 hR hrun hni1 Z H Cs Ac Lst D J _ ct hct
  exact (hL y hy hok ha hnq hsw hvf s1 a1 hR hrun hni1 Z H Cs Ac Lst D J ct hct).toRN12 hAT hmax (htu a1) J hct
    hni1 hrun hnq

end

end

end Fl4Proofs.P3
