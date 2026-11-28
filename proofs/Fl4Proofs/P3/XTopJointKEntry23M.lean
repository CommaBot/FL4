/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN sch23b (c2)): **`kernel_entryJ23M`:
the receive leaves at a `chooseNewThread` mid state where ct has no SC.**
`JMidLeavesHyp13` [W] (XTopJointKEntry22M) asked every receive leaf under
`chooseNewThread ∧ ¬ CurInv`. Where ct has no SC (`MidN`, XTopJointMidN) they
are proved: the cap fault every case (XTopJointFaultN's `faultHypJZN`), the
notification receive outside `SigDon` (XTopJointRecvSigN's
`jRecvSigHypN_of`), the endpoint receive with a null or free reply outside
`IpcActDon` / `IpcPushDon` (XTopJointRecvIpcN's `jRecvIpcUN`).
`JRecvLeavesRN14` asks: the fault only where ct has an SC (`CtSc`); the
notification receive where ct has an SC or `SigDon`; the endpoint receive
where ct has an SC, or the reply is linked to another thread (`IpcLinked`),
or `IpcActDon`, or `IpcPushDon`. `.toRN13`; `JMidLeavesHyp14` [W] =
`JMidLeavesHyp13` concluding `JRecvLeavesRN14`, `jMidLeavesHyp_of14`,
`KDispHyps23M`, `.to22M`, NEW TOP `kernel_entryJ23M`.
-/
import Fl4Proofs.P3.XTopJointFaultN
import Fl4Proofs.P3.XTopJointRecvIpcN
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-- **ct has an SC** (module docstring). -/
def CtSc (σ : Fl4Spec.State Unit) : Prop :=
  ∃ x, σ.kheap σ.curThread = some (.tcb x) ∧ x.tcbSchedContext ≠ none

theorem midN_of {σ : Fl4Spec.State Unit} (hni1 : σ.curThread ≠ σ.idleThread) (hrun : CurRun σ)
    (ho : σ.schedulerAction = .chooseNewThread) (hc : ¬ CtSc σ) : MidN σ :=
  ⟨hni1, hrun, ho, fun x hx => by
    by_contra hne
    exact hc ⟨x, hx, hne⟩⟩

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JRecvLeavesRN13` with every SC-less leaf proved but the donations and
the linked reply** (module docstring). -/
structure JRecvLeavesRN14 (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) (ct : U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop where
  ipc : ∀ p b sd g gr rc rc', (∃ x, σ.kheap p.bv = some (.endpoint x)) →
    ((rc = .Null ∧ rc' = .nullCap) ∨
      (CapRel rc rc' ∧ ∃ q g', rc = .Reply q g' ∧ ∃ x, σ.kheap q.bv = some (.reply x))) →
    JHeld (L := L) th s (.Endpoint p b sd true g gr) → (∀ q g', rc = .Reply q g' → JHeld (L := L) th s rc) →
    σ.schedulerAction = .chooseNewThread → ¬ CurInv σ →
    (CtSc σ ∨ IpcLinked (L := L) s rc ∨ IpcActDon σ ∨ IpcPushDon σ p.bv rc) →
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
narrowed to the donations and the linked reply** (module docstring):
`JMidLeavesHyp13` concluding `JRecvLeavesRN14`. -/
def JMidLeavesHyp14 (AR : A → Fl4Spec.Cr3 → Prop) (cptr : Fl4Spec.CapRef) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ y ∈ ((Fl4Spec.fl4HandleInvocationR (Z := Unit) true false false true true cptr).run σ).1, y.1 = .ok () →
    y.2.schedulerAction ≠ .resumeCurThread → (∀ d p, y.2.curThread ∉ y.2.readyQueues d p) →
    y.2.schedulerAction ≠ .switchThread y.2.curThread →
    (∀ x, y.2.kheap y.2.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler) →
    ∀ (s1 : S) (a1 : A), RelTopM (L := L) s1 y.2 → CurRun y.2 → y.2.curThread ≠ y.2.idleThread →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s1 a1 y.2 → [VxE Z] → ∀ ct, sched.cur_thread st s1 = ok ct →
        JRecvLeavesRN14 (L := L) arI AR Z.th ct s1 a1 y.2

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop}

/-- **`JRecvLeavesRN13` from `JRecvLeavesRN14`**: the SC-less leaves by
`faultHypJZN`, `jRecvSigHypN_of`, `jRecvIpcUN`. -/
theorem JRecvLeavesRN14.toRN13 (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] {ct : U64} (hct : sched.cur_thread st s = ok ct)
    (hni1 : σ.curThread ≠ σ.idleThread) (hrun : CurRun σ) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hvfh : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler)
    (h : JRecvLeavesRN14 (L := L) arI AR Z.th ct s a σ) : JRecvLeavesRN13 (L := L) arI AR Z.th ct s a σ where
  ipc := fun p b sd g gr rc rc' hpE hrc hHd hHr ho hC => by
    by_cases hx : CtSc σ ∨ IpcLinked (L := L) s rc ∨ IpcActDon σ ∨ IpcPushDon σ p.bv rc
    · exact h.ipc p b sd g gr rc rc' hpE hrc hHd hHr ho hC hx
    · have hN : MidN σ := midN_of hni1 hrun ho (fun h' => hx (Or.inl h'))
      obtain ⟨hcur, -⟩ := J.curEq hct
      have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
      have hun : rc = .Null ∨ ∃ q g', rc = .Reply q g' ∧ L.mem s (Endp.rTcbA q) = 0#u64 := by
        rcases hrc with ⟨h0, -⟩ | ⟨-, q, g', e, -⟩
        · exact Or.inl h0
        · refine Or.inr ⟨q, g', e, ?_⟩
          by_contra hne
          exact hx (Or.inr (Or.inl ⟨q, g', e, hne⟩))
      exact jRecvIpcUN hAT hmax htu J hctT hcur hN hnq p b sd g gr rc rc' hpE hrc hHd hHr hun
        (fun h' => hx (Or.inr (Or.inr (Or.inl h')))) (fun h' => hx (Or.inr (Or.inr (Or.inr h'))))
  sig := fun p b w rd ac hcr hex hHd ho hC => by
    by_cases hx : CtSc σ ∨ SigDon σ p.bv
    · exact h.sig p b w rd ac hcr hex hHd ho hC hx
    · have hN : MidN σ := midN_of hni1 hrun ho (fun h' => hx (Or.inl h'))
      obtain ⟨hcur, -⟩ := J.curEq hct
      have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
      exact jRecvSigHypN_of hAT J hctT hcur hN hN.nr hnq p b w rd ac hcr hex hHd (fun h' => hx (Or.inr h'))
  flt := fun cptr lf lf' hl ho hC => by
    by_cases hx : CtSc σ
    · exact h.flt cptr lf lf' hl ho hC hx
    · have hN : MidN σ := midN_of hni1 hrun ho hx
      exact J.faultHypJZN hAT hN hN.nr hct hnq hvfh ⟨cptr, true, lf, lf', rfl, by rw [ofBl_toBl64], hl⟩

/-- **`JMidLeavesHyp13` from `JMidLeavesHyp14`** (module docstring). -/
theorem jMidLeavesHyp_of14 (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    {cptr : Fl4Spec.CapRef} {σ : Fl4Spec.State Unit}
    (hL : JMidLeavesHyp14 (L := L) arI AR cptr σ) : JMidLeavesHyp13 (L := L) arI AR cptr σ := by
  intro y hy hok ha hnq hsw hvf s1 a1 hR hrun hni1 Z H Cs Ac Lst D J _ ct hct
  exact (hL y hy hok ha hnq hsw hvf s1 a1 hR hrun hni1 Z H Cs Ac Lst D J ct hct).toRN13 hAT hmax (htu a1) J hct
    hni1 hrun hnq hvf

end

end

end Fl4Proofs.P3
