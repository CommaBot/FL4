/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN sch16): **`kernel_entryJ12M`:
the cap-fault leaf narrowed.** `JMidLeavesHyp2` [W] (XTopJointKEntry11M)
asked `handle_fault` of a cap fault at every non-resumed mid state. At a
switch mid state XTopJointFaultM proves it for a null handler and an endpoint
handler without a waiting receiver (`JAtZ.faultHypJZM`, outside `FltOpen`).

* `JRecvLeavesRN3`: `JRecvLeavesRN2` with the fault leaf asked only under
  `FltOpen` (a pending reschedule, or an endpoint handler with a waiting
  receiver); `JRecvLeavesRN3.toRN2` (from ct's valid fault handler at the
  mid state, which `JMidLeavesHyp` already gives).
* `JMidLeavesHyp3` [W]: `JMidLeavesHyp2` concluding `JRecvLeavesRN3` (l4v
  as before: receive_ipc_corres / receive_signal_corres / handle_fault_corres
  inside handle_recv_corres under scheduler_act_sane; every case left is a
  case of sch15's `JMidLeavesHyp`, true in reachable states),
  `jMidLeavesHyp_of3`, `KDispHyps12M`, `.to11M`, NEW TOP `kernel_entryJ12M`
  = `kernel_entryJ11M` with `KDispHyps12M`.
-/
import Fl4Proofs.P3.XTopJointFaultM
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JRecvLeavesRN2` with the fault leaf narrowed to `FltOpen`** (module
docstring). -/
structure JRecvLeavesRN3 (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) (ct : U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop where
  ipc : ∀ p b sd g gr rc rc', (∃ x, σ.kheap p.bv = some (.endpoint x)) →
    ((rc = .Null ∧ rc' = .nullCap) ∨
      (CapRel rc rc' ∧ ∃ q g', rc = .Reply q g' ∧ ∃ x, σ.kheap q.bv = some (.reply x))) →
    JHeld (L := L) th s (.Endpoint p b sd true g gr) → (∀ q g', rc = .Reply q g' → JHeld (L := L) th s rc) →
    IpcOpen (L := L) ct s σ p rc →
    endpoint.receive_ipc st arI s a ct (.Endpoint p b sd true g gr) true rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) true rc' σ).1,
        RJR (L := L) arI AR r.1 r.2 z.2 ⦄
  sig : ∀ p b w rd ac, CapRel (.Notification p b w rd) ac → (∃ x, σ.kheap p.bv = some (.notification x)) →
    JHeld (L := L) th s (.Notification p b w rd) → SigOpen σ p →
    notification.receive_signal st arI s a ct p true ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveSignal (Z := Unit) ct.bv ac true σ).1, RJR (L := L) arI AR r.1 r.2 z.2 ⦄
  flt : ∀ cptr lf lf', LookupFaultRel lf lf' → FltOpen σ →
    faults.handle_fault st arI s a ct (.Cap cptr true lf) ⦃ r =>
      ∃ z ∈ (Fl4Spec.handleFault (Z := Unit) ct.bv (.capFault (Fl4Spec.ofBl (Fl4Spec.toBl cptr.bv)) true lf') σ).1,
        RJR (L := L) arI AR r.1 r.2 z.2 ⦄

/-- **[W] The receive leaves at a non-resumed mid state, narrowed further**
(module docstring): `JMidLeavesHyp2` concluding `JRecvLeavesRN3`. -/
def JMidLeavesHyp3 (AR : A → Fl4Spec.Cr3 → Prop) (cptr : Fl4Spec.CapRef) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ y ∈ ((Fl4Spec.fl4HandleInvocationR (Z := Unit) true false false true true cptr).run σ).1, y.1 = .ok () →
    y.2.schedulerAction ≠ .resumeCurThread → (∀ d p, y.2.curThread ∉ y.2.readyQueues d p) →
    y.2.schedulerAction ≠ .switchThread y.2.curThread →
    (∀ x, y.2.kheap y.2.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler) →
    ∀ (s1 : S) (a1 : A), RelTopM (L := L) s1 y.2 → CurRun y.2 → y.2.curThread ≠ y.2.idleThread →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s1 a1 y.2 → [VxE Z] → ∀ ct, sched.cur_thread st s1 = ok ct →
        JRecvLeavesRN3 (L := L) arI AR Z.th ct s1 a1 y.2

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop}

/-- **`JRecvLeavesRN2` from `JRecvLeavesRN3`** at a non-resumed mid state
with no switch to ct: `JAtZ.faultHypJZM` outside `FltOpen`. -/
theorem JRecvLeavesRN3.toRN2 (hAT : P0.ArchTotal arI) {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] {ct : U64} (hct : sched.cur_thread st s = ok ct)
    (hni1 : σ.curThread ≠ σ.idleThread) (hrun : CurRun σ) (hsw : σ.schedulerAction ≠ .resumeCurThread)
    (hsc : σ.schedulerAction ≠ .switchThread σ.curThread) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hvfh : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler)
    (h : JRecvLeavesRN3 (L := L) arI AR Z.th ct s a σ) : JRecvLeavesRN2 (L := L) arI AR Z.th ct s a σ where
  ipc := h.ipc
  sig := h.sig
  flt := fun cptr lf lf' hl => by
    by_cases ho : FltOpen σ
    · exact h.flt cptr lf lf' hl ho
    · have hE : MidE σ := by
        refine ⟨hni1, hrun, Or.inr ?_⟩
        cases e : σ.schedulerAction with
        | resumeCurThread => exact absurd e hsw
        | chooseNewThread => exact absurd (Or.inl e) ho
        | switchThread u => exact ⟨u, rfl, fun hu => hsc (by rw [e, hu])⟩
      exact J.faultHypJZM hE hsw hct hnq hvfh ho ⟨cptr, true, lf, lf', rfl, by rw [ofBl_toBl64], hl⟩

/-- **`JMidLeavesHyp2` from `JMidLeavesHyp3`** (module docstring). -/
theorem jMidLeavesHyp_of3 (hAT : P0.ArchTotal arI) {cptr : Fl4Spec.CapRef} {σ : Fl4Spec.State Unit}
    (hL : JMidLeavesHyp3 (L := L) arI AR cptr σ) : JMidLeavesHyp2 (L := L) arI AR cptr σ := by
  intro y hy hok ha hnq hsw hvf s1 a1 hR hrun hni1 Z H Cs Ac Lst D J _ ct hct
  exact (hL y hy hok ha hnq hsw hvf s1 a1 hR hrun hni1 Z H Cs Ac Lst D J ct hct).toRN2 hAT J hct hni1 hrun ha hsw hnq hvf

end

end

end Fl4Proofs.P3
