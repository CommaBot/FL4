/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN sch24 (d3)): **`kernel_entryJ24M`:
the endpoint receive with a linked reply at a `chooseNewThread` mid state
where ct has no SC.** `JMidLeavesHyp14` [W] (XTopJointKEntry23M) asked
`receive_ipc` where ct has an SC, or the reply is linked to another thread
(`IpcLinked`), or one of the two SC donations to ct. Where ct has no SC
(`MidN`) and neither donation happens, the linked case is XTopJointRecvIpcLinkN's
`jRecvIpcLinkN`. `JRecvLeavesRN15` asks the endpoint receive only where ct
has an SC or `IpcActDon` or `IpcPushDon`; `.toRN14`; `JMidLeavesHyp15` [W] =
`JMidLeavesHyp14` concluding `JRecvLeavesRN15`, `jMidLeavesHyp_of15`,
`KDispHyps24M`, `.to23M`, NEW TOP `kernel_entryJ24M`.
-/
import Fl4Proofs.P3.XTopJointRecvIpcLinkN
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JRecvLeavesRN14` without the linked reply** (module docstring). -/
structure JRecvLeavesRN15 (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) (ct : U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop where
  ipc : ∀ p b sd g gr rc rc', (∃ x, σ.kheap p.bv = some (.endpoint x)) →
    ((rc = .Null ∧ rc' = .nullCap) ∨
      (CapRel rc rc' ∧ ∃ q g', rc = .Reply q g' ∧ ∃ x, σ.kheap q.bv = some (.reply x))) →
    JHeld (L := L) th s (.Endpoint p b sd true g gr) → (∀ q g', rc = .Reply q g' → JHeld (L := L) th s rc) →
    σ.schedulerAction = .chooseNewThread → ¬ CurInv σ →
    (CtSc σ ∨ IpcActDon σ ∨ IpcPushDon σ p.bv rc) →
    endpoint.receive_ipc st arI s a ct (.Endpoint p b sd true g gr) true rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) true rc' σ).1,
        RJR (L := L) arI AR r.1 r.2 z.2 ⦄
  sig : ∀ p b w rd ac, CapRel (.Notification p b w rd) ac → (∃ x, σ.kheap p.bv = some (.notification x)) →
    JHeld (L := L) th s (.Notification p b w rd) → σ.schedulerAction = .chooseNewThread → ¬ CurInv σ →
    (CtSc σ ∨ SigDon σ p.bv) →
    notification.receive_signal st arI s a ct p true ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveSignal (Z := Unit) ct.bv ac true σ).1, RJR (L := L) arI AR r.1 r.2 z.2 ⦄
  flt : ∀ cptr lf lf', LookupFaultRel lf lf' → σ.schedulerAction = .chooseNewThread → ¬ CurInv σ → CtSc σ →
    faults.handle_fault st arI s a ct (.Cap cptr true lf) ⦃ r =>
      ∃ z ∈ (Fl4Spec.handleFault (Z := Unit) ct.bv (.capFault (Fl4Spec.ofBl (Fl4Spec.toBl cptr.bv)) true lf') σ).1,
        RJR (L := L) arI AR r.1 r.2 z.2 ⦄

/-- **[W] The receive leaves at a non-resumed mid state, the SC-less ones
narrowed to the donations** (module docstring): `JMidLeavesHyp14`
concluding `JRecvLeavesRN15`. -/
def JMidLeavesHyp15 (AR : A → Fl4Spec.Cr3 → Prop) (cptr : Fl4Spec.CapRef) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ y ∈ ((Fl4Spec.fl4HandleInvocationR (Z := Unit) true false false true true cptr).run σ).1, y.1 = .ok () →
    y.2.schedulerAction ≠ .resumeCurThread → (∀ d p, y.2.curThread ∉ y.2.readyQueues d p) →
    y.2.schedulerAction ≠ .switchThread y.2.curThread →
    (∀ x, y.2.kheap y.2.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler) →
    ∀ (s1 : S) (a1 : A), RelTopM (L := L) s1 y.2 → CurRun y.2 → y.2.curThread ≠ y.2.idleThread →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s1 a1 y.2 → [VxE Z] → ∀ ct, sched.cur_thread st s1 = ok ct →
        JRecvLeavesRN15 (L := L) arI AR Z.th ct s1 a1 y.2

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop}

/-- **`JRecvLeavesRN14` from `JRecvLeavesRN15`**: the linked reply where ct
has no SC and neither donation happens by `jRecvIpcLinkN`. -/
theorem JRecvLeavesRN15.toRN14 (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] {ct : U64} (hct : sched.cur_thread st s = ok ct)
    (hni1 : σ.curThread ≠ σ.idleThread) (hrun : CurRun σ) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (h : JRecvLeavesRN15 (L := L) arI AR Z.th ct s a σ) : JRecvLeavesRN14 (L := L) arI AR Z.th ct s a σ where
  sig := h.sig
  flt := h.flt
  ipc := fun p b sd g gr rc rc' hpE hrc hHd hHr ho hC hx => by
    by_cases hy : CtSc σ ∨ IpcActDon σ ∨ IpcPushDon σ p.bv rc
    · exact h.ipc p b sd g gr rc rc' hpE hrc hHd hHr ho hC hy
    · have hl : IpcLinked (L := L) s rc := by
        rcases hx with h1 | h1 | h1 | h1
        · exact absurd (Or.inl h1) hy
        · exact h1
        · exact absurd (Or.inr (Or.inl h1)) hy
        · exact absurd (Or.inr (Or.inr h1)) hy
      obtain ⟨q, g', rfl, hi0⟩ := hl
      have hN : MidN σ := midN_of hni1 hrun ho (fun h' => hy (Or.inl h'))
      obtain ⟨hcur, -⟩ := J.curEq hct
      have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
      rcases hrc with ⟨h0, -⟩ | ⟨hcr, q', g'', e, xr, hkr⟩
      · cases h0
      · cases e
        exact jRecvIpcLinkN hAT hmax htu J hctT hcur hN hnq p b sd g gr q g' rc' hpE hcr hkr hHd
          (hHr q g' rfl) hi0 (fun h' => hy (Or.inr (Or.inl h'))) (fun h' => hy (Or.inr (Or.inr h')))

/-- **`JMidLeavesHyp14` from `JMidLeavesHyp15`** (module docstring). -/
theorem jMidLeavesHyp_of15 (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    {cptr : Fl4Spec.CapRef} {σ : Fl4Spec.State Unit}
    (hL : JMidLeavesHyp15 (L := L) arI AR cptr σ) : JMidLeavesHyp14 (L := L) arI AR cptr σ := by
  intro y hy hok ha hnq hsw hvf s1 a1 hR hrun hni1 Z H Cs Ac Lst D J _ ct hct
  exact (hL y hy hok ha hnq hsw hvf s1 a1 hR hrun hni1 Z H Cs Ac Lst D J ct hct).toRN14 hAT hmax (htu a1) J hct
    hni1 hrun hnq

end

end

end Fl4Proofs.P3
