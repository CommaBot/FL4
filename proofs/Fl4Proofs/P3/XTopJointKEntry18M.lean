/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN sch20): **`kernel_entryJ18M`:
the notification receive at a `chooseNewThread` mid state with `CurInv`.**
`JMidLeavesHyp8` [W] (XTopJointKEntry17M) asked every receive leaf under
`chooseNewThread`. Where `CurInv` holds there the notification receive is
`jRecvSigHypC2_of` (XTopJointRecvSigC). `JRecvLeavesRN9` asks the notification
receive only under `chooseNewThread ∧ ¬ CurInv` (in reachable states: ct
without an SC, below), the endpoint receive and the cap fault under
`chooseNewThread` as before; `.toRN8`; `JMidLeavesHyp9` [W] = `JMidLeavesHyp8`
concluding `JRecvLeavesRN9`, `jMidLeavesHyp_of9`, `KDispHyps18M`, `.to17M`,
NEW TOP `kernel_entryJ18M`.

Why `¬ CurInv` means "ct has no SC" at these states (sch20 STEP 1): the first
phase is ReplyRecv / NBSendRecv / NBSendWait's invocation with
`firstPhase = true`, and the first-phase decode yields only `FirstInv`
invocations (`okAll_decodeFirst`; FL4 `decode_invocation`'s `first_phase`
checks, C seL4 c98d70ad objecttype.c `decodeInvocation`: thread, domain,
SchedContext, SchedControl and CNode caps are rejected in the first phase).
None of Untyped, endpoint send, notification signal, reply, IRQ control /
handler, arch invocations binds an SC to ct, moves ct to the release queue
or changes the current SC; the only way ct loses `CurInv` while runnable is
giving its SC away (an endpoint send donating to a passive receiver, a reply
returning a donated SC).
-/
import Fl4Proofs.P3.XTopJointKEntry17M
import Fl4Proofs.P3.XTopJointRecvSigC
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JRecvLeavesRN8` with the notification receive asked only where
`CurInv` fails** (module docstring). -/
structure JRecvLeavesRN9 (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) (ct : U64) (s : S) (a : A)
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
  flt : ∀ cptr lf lf', LookupFaultRel lf lf' → σ.schedulerAction = .chooseNewThread →
    faults.handle_fault st arI s a ct (.Cap cptr true lf) ⦃ r =>
      ∃ z ∈ (Fl4Spec.handleFault (Z := Unit) ct.bv (.capFault (Fl4Spec.ofBl (Fl4Spec.toBl cptr.bv)) true lf') σ).1,
        RJR (L := L) arI AR r.1 r.2 z.2 ⦄

/-- **[W] The receive leaves at a non-resumed mid state, the notification
receive narrowed to `¬ CurInv`** (module docstring): `JMidLeavesHyp8`
concluding `JRecvLeavesRN9`. -/
def JMidLeavesHyp9 (AR : A → Fl4Spec.Cr3 → Prop) (cptr : Fl4Spec.CapRef) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ y ∈ ((Fl4Spec.fl4HandleInvocationR (Z := Unit) true false false true true cptr).run σ).1, y.1 = .ok () →
    y.2.schedulerAction ≠ .resumeCurThread → (∀ d p, y.2.curThread ∉ y.2.readyQueues d p) →
    y.2.schedulerAction ≠ .switchThread y.2.curThread →
    (∀ x, y.2.kheap y.2.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler) →
    ∀ (s1 : S) (a1 : A), RelTopM (L := L) s1 y.2 → CurRun y.2 → y.2.curThread ≠ y.2.idleThread →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s1 a1 y.2 → [VxE Z] → ∀ ct, sched.cur_thread st s1 = ok ct →
        JRecvLeavesRN9 (L := L) arI AR Z.th ct s1 a1 y.2

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop}

/-- **`JRecvLeavesRN8` from `JRecvLeavesRN9`**: the notification receive at
a `chooseNewThread` state with `CurInv` by `jRecvSigHypC2_of`. -/
theorem JRecvLeavesRN9.toRN8 (hAT : P0.ArchTotal arI)
    {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] {ct : U64} (hct : sched.cur_thread st s = ok ct)
    (hni1 : σ.curThread ≠ σ.idleThread) (hrun : CurRun σ) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (h : JRecvLeavesRN9 (L := L) arI AR Z.th ct s a σ) : JRecvLeavesRN8 (L := L) arI AR Z.th ct s a σ where
  ipc := h.ipc
  flt := h.flt
  sig := fun p b w rd ac hcr hex hHd ho => by
    by_cases hC : CurInv σ
    · obtain ⟨hcur, -⟩ := J.curEq hct
      have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
      have hE : MidC σ := ⟨hni1, hrun, ho, hC⟩
      exact jRecvSigHypC2_of hAT J hctT hcur hE hE.nr hnq p b w rd ac hcr hex hHd
    · exact h.sig p b w rd ac hcr hex hHd ho hC

/-- **`JMidLeavesHyp8` from `JMidLeavesHyp9`** (module docstring). -/
theorem jMidLeavesHyp_of9 (hAT : P0.ArchTotal arI)
    {cptr : Fl4Spec.CapRef} {σ : Fl4Spec.State Unit}
    (hL : JMidLeavesHyp9 (L := L) arI AR cptr σ) : JMidLeavesHyp8 (L := L) arI AR cptr σ := by
  intro y hy hok ha hnq hsw hvf s1 a1 hR hrun hni1 Z H Cs Ac Lst D J _ ct hct
  exact (hL y hy hok ha hnq hsw hvf s1 a1 hR hrun hni1 Z H Cs Ac Lst D J ct hct).toRN8 hAT J hct hni1 hrun hnq

end

end

end Fl4Proofs.P3
