/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN sch20): **`kernel_entryJ19M`:
the cap fault at a `chooseNewThread` mid state with `CurInv`, outside a
waiting receiver.** `JMidLeavesHyp9` [W] (XTopJointKEntry18M) asked the cap
fault's `handle_fault` under `chooseNewThread`. Where `CurInv` holds there and
ct's fault handler is not an endpoint with a waiting receiver (`FltRecv`),
it is `JAtZ.faultHypJZC` (XTopJointFaultC: no handler, or the blocking fault
send). `JRecvLeavesRN10` asks the cap fault only under
`chooseNewThread ∧ (¬ CurInv ∨ FltRecv)`; `.toRN9`; `JMidLeavesHyp10` [W] =
`JMidLeavesHyp9` concluding `JRecvLeavesRN10`, `jMidLeavesHyp_of10`,
`KDispHyps19M`, `.to18M`, NEW TOP `kernel_entryJ19M`.
-/
import Fl4Proofs.P3.XTopJointKEntry18M
import Fl4Proofs.P3.XTopJointFaultC
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JRecvLeavesRN9` with the cap fault asked only where `CurInv` fails
or a receiver waits on ct's fault endpoint** (module docstring). -/
structure JRecvLeavesRN10 (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) (ct : U64) (s : S) (a : A)
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
    JHeld (L := L) th s (.Notification p b w rd) → σ.schedulerAction = .chooseNewThread → ¬ CurInv σ →
    notification.receive_signal st arI s a ct p true ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveSignal (Z := Unit) ct.bv ac true σ).1, RJR (L := L) arI AR r.1 r.2 z.2 ⦄
  flt : ∀ cptr lf lf', LookupFaultRel lf lf' → σ.schedulerAction = .chooseNewThread → (¬ CurInv σ ∨ FltRecv σ) →
    faults.handle_fault st arI s a ct (.Cap cptr true lf) ⦃ r =>
      ∃ z ∈ (Fl4Spec.handleFault (Z := Unit) ct.bv (.capFault (Fl4Spec.ofBl (Fl4Spec.toBl cptr.bv)) true lf') σ).1,
        RJR (L := L) arI AR r.1 r.2 z.2 ⦄

/-- **[W] The receive leaves at a non-resumed mid state, the cap fault
narrowed to `¬ CurInv ∨ FltRecv`** (module docstring): `JMidLeavesHyp9`
concluding `JRecvLeavesRN10`. -/
def JMidLeavesHyp10 (AR : A → Fl4Spec.Cr3 → Prop) (cptr : Fl4Spec.CapRef) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ y ∈ ((Fl4Spec.fl4HandleInvocationR (Z := Unit) true false false true true cptr).run σ).1, y.1 = .ok () →
    y.2.schedulerAction ≠ .resumeCurThread → (∀ d p, y.2.curThread ∉ y.2.readyQueues d p) →
    y.2.schedulerAction ≠ .switchThread y.2.curThread →
    (∀ x, y.2.kheap y.2.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler) →
    ∀ (s1 : S) (a1 : A), RelTopM (L := L) s1 y.2 → CurRun y.2 → y.2.curThread ≠ y.2.idleThread →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s1 a1 y.2 → [VxE Z] → ∀ ct, sched.cur_thread st s1 = ok ct →
        JRecvLeavesRN10 (L := L) arI AR Z.th ct s1 a1 y.2

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop}

/-- **`JRecvLeavesRN9` from `JRecvLeavesRN10`**: the cap fault at a
`chooseNewThread` state with `CurInv` outside `FltRecv` by `JAtZ.faultHypJZC`. -/
theorem JRecvLeavesRN10.toRN9 (hAT : P0.ArchTotal arI)
    {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] {ct : U64} (hct : sched.cur_thread st s = ok ct)
    (hni1 : σ.curThread ≠ σ.idleThread) (hrun : CurRun σ) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hvfh : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler)
    (h : JRecvLeavesRN10 (L := L) arI AR Z.th ct s a σ) : JRecvLeavesRN9 (L := L) arI AR Z.th ct s a σ where
  ipc := h.ipc
  sig := h.sig
  flt := fun cptr lf lf' hl ho => by
    by_cases hC : CurInv σ
    · by_cases hR : FltRecv σ
      · exact h.flt cptr lf lf' hl ho (Or.inr hR)
      · have hE : MidC σ := ⟨hni1, hrun, ho, hC⟩
        exact J.faultHypJZC hE hE.nr hct hnq hvfh hR ⟨cptr, true, lf, lf', rfl, by rw [ofBl_toBl64], hl⟩
    · exact h.flt cptr lf lf' hl ho (Or.inl hC)

/-- **`JMidLeavesHyp9` from `JMidLeavesHyp10`** (module docstring). -/
theorem jMidLeavesHyp_of10 (hAT : P0.ArchTotal arI)
    {cptr : Fl4Spec.CapRef} {σ : Fl4Spec.State Unit}
    (hL : JMidLeavesHyp10 (L := L) arI AR cptr σ) : JMidLeavesHyp9 (L := L) arI AR cptr σ := by
  intro y hy hok ha hnq hsw hvf s1 a1 hR hrun hni1 Z H Cs Ac Lst D J _ ct hct
  exact (hL y hy hok ha hnq hsw hvf s1 a1 hR hrun hni1 Z H Cs Ac Lst D J ct hct).toRN9 hAT J hct hni1 hrun hnq hvf

end

end

end Fl4Proofs.P3
