/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN sch29): **`kernel_entryJ27M`:
the mid premise on the receive leaves is gone.** `JMidLeavesHyp17` [W]
(XTopJointKEntry26MD) asked the endpoint receive at a `chooseNewThread`
mid state with `¬ CurInv` only at the reply-push SC donation to ct
(`IpcPushDon`). XTopJointRecvIpcPushDonD proves every endpoint receive at a
`MidN` state (`jRecvIpcUDD`, `jRecvIpcLinkDD`), the donation included, and
`jMidChooseFact`'s `CtOK` gives `MidN` there (`not_ctSc_of`, `midN_of`).

* `JRecvLeavesRN17.of_ok`: `JRecvLeavesRN17` from `CtOK` alone (what
  KENTRY-PLAN sch27 called `JRecvLeavesRN18 = {}`: no premise is left on the
  receive leaves).
* `jMidLeavesHyp17_of`: `JMidLeavesHyp17` from the first-phase fact.
* `KDispHyps27M` (mid: `JMidPerfHypQ` [W], `JMidPerfHypB` [W], `JMidVfhHyp`
  [J]; no leaf premise); `.to26M` (`jMidChooseFact` from the dispatch state,
  as `KDispHyps26M.to25M`); NEW TOP `kernel_entryJ27M`.
-/
import Fl4Proofs.P3.XTopJointKEntry26MD
import Fl4Proofs.P3.XTopJointRecvIpcPushDonD
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop}

/-- **The receive leaves at a non-resumed mid state from `CtOK`** (module
docstring): every endpoint receive at `MidN`, the reply-push donation
included. -/
theorem JRecvLeavesRN17.of_ok (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] {ct : U64} (hct : sched.cur_thread st s = ok ct)
    (hni1 : σ.curThread ≠ σ.idleThread) (hrun : CurRun σ) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hok : MidRun.CtOK σ) : JRecvLeavesRN17 (L := L) arI AR Z.th ct s a σ where
  ipc := fun p b sd g gr rc rc' hpE hrc hHd hHr ho hC _ => by
    have hN : MidN σ := midN_of hni1 hrun ho (not_ctSc_of hok hC)
    obtain ⟨hcur, -⟩ := J.curEq hct
    have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
    rcases hrc with ⟨h0, h0'⟩ | ⟨hcr, q, g', e, xr, hkr⟩
    · exact jRecvIpcUDD hAT hmax hmb htu J hctT hcur hN hnq p b sd g gr rc rc' hpE (Or.inl ⟨h0, h0'⟩)
        hHd hHr (Or.inl h0)
    · subst e
      by_cases hi0 : L.mem s (Endp.rTcbA q) = 0#u64
      · exact jRecvIpcUDD hAT hmax hmb htu J hctT hcur hN hnq p b sd g gr _ rc' hpE
          (Or.inr ⟨hcr, q, g', rfl, xr, hkr⟩) hHd hHr (Or.inr ⟨q, g', rfl, hi0⟩)
      · exact jRecvIpcLinkDD hAT hmax hmb htu J hctT hcur hN hnq p b sd g gr q g' rc' hpE hcr hkr hHd
          (hHr q g' rfl) hi0

/-- **`JMidLeavesHyp17` from the first-phase fact** (module docstring). -/
theorem jMidLeavesHyp17_of (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    {cptr : Fl4Spec.CapRef} {σ : Fl4Spec.State Unit}
    (hF : ∀ y ∈ ((Fl4Spec.fl4HandleInvocationR (Z := Unit) true false false true true cptr).run σ).1,
      MidRun.CtOK y.2) : JMidLeavesHyp17 (L := L) arI AR cptr σ := by
  intro y hy _ _ hnq _ _ s1 a1 _ hrun hni1 Z H Cs Ac Lst D J _ ct hct
  exact JRecvLeavesRN17.of_ok hAT hmax hmb (htu a1) J hct hni1 hrun hnq (hF y hy)

end

end

end Fl4Proofs.P3
