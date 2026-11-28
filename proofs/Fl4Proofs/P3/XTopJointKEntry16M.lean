/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN sch18): **`kernel_entryJ16M`:
the notification receive and the cap fault at a switch mid state.**
`JMidLeavesHyp6` [W] (XTopJointKEntry15M) asked `receive_signal` under
`SigOpen` and `handle_fault` under `FltOpen`. At a switch mid state (`MidE`,
action `switchThread u`, u ≠ ct):

* the notification receive in every case: `jRecvSigHypM2_of`
  (XTopJointRecvSigRetM; the SC return by `JAtZ.recvSigRetJM`);
* the cap fault outside `FltDon` (the donating send to a waiting receiver
  without an SC): `JAtZ.faultHypJZM2` (XTopJointFaultRecvM).

`JRecvLeavesRN7` asks the receives only under a pending reschedule and the
fault only under a pending reschedule or `FltDon`; `.toRN6`;
`JMidLeavesHyp7` [W] = `JMidLeavesHyp6` concluding `JRecvLeavesRN7` (same l4v
counterpart and truth argument as sch15-17), `jMidLeavesHyp_of7`,
`KDispHyps16M`, `.to15M`, NEW TOP `kernel_entryJ16M`.
-/
import Fl4Proofs.P3.XTopJointKEntry15M
import Fl4Proofs.P3.XTopJointRecvSigRetM
import Fl4Proofs.P3.XTopJointFaultRecvM
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JRecvLeavesRN6` with the notification receive asked only under a pending
reschedule and the cap fault only under a pending reschedule or `FltDon`**
(module docstring). -/
structure JRecvLeavesRN7 (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) (ct : U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop where
  ipc : ∀ p b sd g gr rc rc', (∃ x, σ.kheap p.bv = some (.endpoint x)) →
    ((rc = .Null ∧ rc' = .nullCap) ∨
      (CapRel rc rc' ∧ ∃ q g', rc = .Reply q g' ∧ ∃ x, σ.kheap q.bv = some (.reply x))) →
    JHeld (L := L) th s (.Endpoint p b sd true g gr) → (∀ q g', rc = .Reply q g' → JHeld (L := L) th s rc) →
    σ.schedulerAction = .chooseNewThread →
    endpoint.receive_ipc st arI s a ct (.Endpoint p b sd true g gr) true rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) true rc' σ).1,
        RJR (L := L) arI AR r.1 r.2 z.2 ⦄
  sig : ∀ p b w rd ac, CapRel (.Notification p b w rd) ac → (∃ x, σ.kheap p.bv = some (.notification x)) →
    JHeld (L := L) th s (.Notification p b w rd) → σ.schedulerAction = .chooseNewThread →
    notification.receive_signal st arI s a ct p true ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveSignal (Z := Unit) ct.bv ac true σ).1, RJR (L := L) arI AR r.1 r.2 z.2 ⦄
  flt : ∀ cptr lf lf', LookupFaultRel lf lf' → (σ.schedulerAction = .chooseNewThread ∨ FltDon σ) →
    faults.handle_fault st arI s a ct (.Cap cptr true lf) ⦃ r =>
      ∃ z ∈ (Fl4Spec.handleFault (Z := Unit) ct.bv (.capFault (Fl4Spec.ofBl (Fl4Spec.toBl cptr.bv)) true lf') σ).1,
        RJR (L := L) arI AR r.1 r.2 z.2 ⦄

/-- **[W] The receive leaves at a non-resumed mid state, narrowed further**
(module docstring): `JMidLeavesHyp6` concluding `JRecvLeavesRN7`. -/
def JMidLeavesHyp7 (AR : A → Fl4Spec.Cr3 → Prop) (cptr : Fl4Spec.CapRef) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ y ∈ ((Fl4Spec.fl4HandleInvocationR (Z := Unit) true false false true true cptr).run σ).1, y.1 = .ok () →
    y.2.schedulerAction ≠ .resumeCurThread → (∀ d p, y.2.curThread ∉ y.2.readyQueues d p) →
    y.2.schedulerAction ≠ .switchThread y.2.curThread →
    (∀ x, y.2.kheap y.2.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler) →
    ∀ (s1 : S) (a1 : A), RelTopM (L := L) s1 y.2 → CurRun y.2 → y.2.curThread ≠ y.2.idleThread →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s1 a1 y.2 → [VxE Z] → ∀ ct, sched.cur_thread st s1 = ok ct →
        JRecvLeavesRN7 (L := L) arI AR Z.th ct s1 a1 y.2

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop}

/-- **`JRecvLeavesRN6` from `JRecvLeavesRN7`** at a non-resumed mid state
with no switch to ct: `jRecvSigHypM2_of` / `JAtZ.faultHypJZM2` unless a
reschedule is pending (or, for the fault, `FltDon`). -/
theorem JRecvLeavesRN7.toRN6 (hAT : P0.ArchTotal arI)
    {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] {ct : U64} (hct : sched.cur_thread st s = ok ct)
    (hni1 : σ.curThread ≠ σ.idleThread) (hrun : CurRun σ) (hsw : σ.schedulerAction ≠ .resumeCurThread)
    (hsc : σ.schedulerAction ≠ .switchThread σ.curThread) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hvfh : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler)
    (h : JRecvLeavesRN7 (L := L) arI AR Z.th ct s a σ) : JRecvLeavesRN6 (L := L) arI AR Z.th ct s a σ where
  ipc := h.ipc
  sig := fun p b w rd ac hcr hex hHd _ => by
    by_cases ho : σ.schedulerAction = .chooseNewThread
    · exact h.sig p b w rd ac hcr hex hHd ho
    · obtain ⟨hcur, -⟩ := J.curEq hct
      have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
      have hE : MidE σ := by
        refine ⟨hni1, hrun, Or.inr ?_⟩
        cases e : σ.schedulerAction with
        | resumeCurThread => exact absurd e hsw
        | chooseNewThread => exact absurd e ho
        | switchThread u => exact ⟨u, rfl, fun hu => hsc (by rw [e, hu])⟩
      exact jRecvSigHypM2_of hAT J hctT hcur hE hsw hnq p b w rd ac hcr hex hHd
  flt := fun cptr lf lf' hl _ => by
    by_cases ho : σ.schedulerAction = .chooseNewThread ∨ FltDon σ
    · exact h.flt cptr lf lf' hl ho
    · have hE : MidE σ := by
        refine ⟨hni1, hrun, Or.inr ?_⟩
        cases e : σ.schedulerAction with
        | resumeCurThread => exact absurd e hsw
        | chooseNewThread => exact absurd (Or.inl e) ho
        | switchThread u => exact ⟨u, rfl, fun hu => hsc (by rw [e, hu])⟩
      exact J.faultHypJZM2 hAT hE hsw hct hnq hvfh (fun h' => ho (Or.inr h'))
        ⟨cptr, true, lf, lf', rfl, by rw [ofBl_toBl64], hl⟩

/-- **`JMidLeavesHyp6` from `JMidLeavesHyp7`** (module docstring). -/
theorem jMidLeavesHyp_of7 (hAT : P0.ArchTotal arI)
    {cptr : Fl4Spec.CapRef} {σ : Fl4Spec.State Unit}
    (hL : JMidLeavesHyp7 (L := L) arI AR cptr σ) : JMidLeavesHyp6 (L := L) arI AR cptr σ := by
  intro y hy hok ha hnq hsw hvf s1 a1 hR hrun hni1 Z H Cs Ac Lst D J _ ct hct
  exact (hL y hy hok ha hnq hsw hvf s1 a1 hR hrun hni1 Z H Cs Ac Lst D J ct hct).toRN6 hAT J hct hni1
    hrun ha hsw hnq hvf

end

end

end Fl4Proofs.P3
