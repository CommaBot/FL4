/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN sch27 (3)): **`kernel_entryJ26M`:
sch23's first-phase fact wired in.** `JMidLeavesHyp16` [W]
(XTopJointKEntry25MD) asked the receive leaves at a `chooseNewThread` mid
state with `¬ CurInv` only where ct has an SC (`CtSc`), or, for the endpoint
receive, at the two SC donations to ct (`IpcActDon`, `IpcPushDon`). At such a
state XTopJointChooseB's `jMidChooseFact` gives `CtOK` (`CurInv` or ct
SC-less), so `¬ CurInv ∧ CtSc` is contradictory: the notification receive
and the cap fault leave the mid premise entirely.

* `BudgetAt.entered`: the dispatch state of the entry is `Entered` (the
  `FaultIP` write changes one TCB, the time stamp only the clock fields, a
  budget check answering `true` nothing).
* `JRecvLeavesRN17`: the endpoint receive only, at `IpcPushDon` (the
  reply-push donation, not proved); `.toRN16` from `CtOK` and, at
  `IpcActDon` (ct SC-less, so `MidN`), XTopJointRecvIpcActDonD's
  `jRecvIpcUDN` (null or free reply) / `jRecvIpcLinkDN` (linked reply).
* `JMidLeavesHyp17` [W] = `JMidLeavesHyp16` concluding `JRecvLeavesRN17`;
  `jMidLeavesHyp_of17` (from `jMidChooseFact`'s conclusion).
* `KDispHyps26M` (mid: `JMidPerfHypQ` [W], `JMidPerfHypB` [W], `JMidVfhHyp`
  [J], `JMidLeavesHyp17` [W]); `.to25M` from the dispatch-state facts
  (`JAtZ.midCQ`: `CQ`, `NQ`; `JAtZ.cur` with `Entered`: `CurInv`;
  `JAtZ.inv`: `Sched.Inv`); NEW TOP `kernel_entryJ26M`.
-/
import Fl4Proofs.P3.XTopJointKEntry25MD
import Fl4Proofs.P3.XTopJointChooseB
import Fl4Proofs.P3.XTopJointRecvIpcActDonD
import Fl4Proofs.P3.XTopJointMachRel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-- **The dispatch state of the entry is `Entered`** (module docstring). -/
theorem BudgetAt.entered (hnd : Fl4Spec.numDomains = 1) {σ σb : Fl4Spec.State Unit} {x : Fl4Spec.Tcb}
    (hk : σ.kheap σ.curThread = some (.tcb x)) (hni : Entered σ) (h : BudgetAt σ σb true) : Entered σb := by
  obtain ⟨σ0, h0, hb⟩ := h
  rw [fl4SyscallFaultIP_eq hk] at h0
  have e0 : σ0 = faultIPSt σ σ.curThread x := congrArg Prod.snd (Set.mem_singleton_iff.1 h0)
  subst e0
  have hE := Sched.updateTimeStamp_eq' hnd
    (doMachineOp_single (getCurrentTime_eq (faultIPSt σ σ.curThread x).machineState))
  obtain ⟨⟨u, σu⟩, hu, h2⟩ := hb
  rw [hE] at hu
  have e : σu = _ := congrArg Prod.snd (Set.mem_singleton_iff.1 hu)
  have hb' : σb = σu := Sched.checkBudgetRestart_true h2 rfl
  rw [hb', e]
  exact hni

/-- `CtOK` and `¬ CurInv` exclude `CtSc`. -/
theorem not_ctSc_of {σ : Fl4Spec.State Unit} (hok : MidRun.CtOK σ) (hC : ¬ CurInv σ) : ¬ CtSc σ := by
  rintro ⟨x, hx, hne⟩
  rcases hok with h | ⟨y, hy, h0⟩
  · exact hC h
  · rw [hx] at hy; cases hy; exact hne h0

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The receive leaves left at a non-resumed mid state**: the endpoint
receive at the reply-push SC donation to ct (module docstring). -/
structure JRecvLeavesRN17 (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) (ct : U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop where
  ipc : ∀ p b sd g gr rc rc', (∃ x, σ.kheap p.bv = some (.endpoint x)) →
    ((rc = .Null ∧ rc' = .nullCap) ∨
      (CapRel rc rc' ∧ ∃ q g', rc = .Reply q g' ∧ ∃ x, σ.kheap q.bv = some (.reply x))) →
    JHeld (L := L) th s (.Endpoint p b sd true g gr) → (∀ q g', rc = .Reply q g' → JHeld (L := L) th s rc) →
    σ.schedulerAction = .chooseNewThread → ¬ CurInv σ → IpcPushDon σ p.bv rc →
    endpoint.receive_ipc st arI s a ct (.Endpoint p b sd true g gr) true rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) true rc' σ).1,
        RJR (L := L) arI AR r.1 r.2 z.2 ⦄

/-- **[W] The receive leaves at a non-resumed mid state, narrowed to the
reply-push donation** (module docstring): `JMidLeavesHyp16` concluding
`JRecvLeavesRN17`. -/
def JMidLeavesHyp17 (AR : A → Fl4Spec.Cr3 → Prop) (cptr : Fl4Spec.CapRef) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ y ∈ ((Fl4Spec.fl4HandleInvocationR (Z := Unit) true false false true true cptr).run σ).1, y.1 = .ok () →
    y.2.schedulerAction ≠ .resumeCurThread → (∀ d p, y.2.curThread ∉ y.2.readyQueues d p) →
    y.2.schedulerAction ≠ .switchThread y.2.curThread →
    (∀ x, y.2.kheap y.2.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler) →
    ∀ (s1 : S) (a1 : A), RelTopM (L := L) s1 y.2 → CurRun y.2 → y.2.curThread ≠ y.2.idleThread →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s1 a1 y.2 → [VxE Z] → ∀ ct, sched.cur_thread st s1 = ok ct →
        JRecvLeavesRN17 (L := L) arI AR Z.th ct s1 a1 y.2

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop}

/-- **`JRecvLeavesRN16` from `JRecvLeavesRN17` and `CtOK`** (module
docstring). -/
theorem JRecvLeavesRN17.toRN16 (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] {ct : U64} (hct : sched.cur_thread st s = ok ct)
    (hni1 : σ.curThread ≠ σ.idleThread) (hrun : CurRun σ) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hok : MidRun.CtOK σ) (h : JRecvLeavesRN17 (L := L) arI AR Z.th ct s a σ) :
    JRecvLeavesRN16 (L := L) arI AR Z.th ct s a σ where
  ipc := fun p b sd g gr rc rc' hpE hrc hHd hHr ho hC hd => by
    have hy : ¬ CtSc σ := not_ctSc_of hok hC
    by_cases hP : IpcPushDon σ p.bv rc
    · exact h.ipc p b sd g gr rc rc' hpE hrc hHd hHr ho hC hP
    · have hN : MidN σ := midN_of hni1 hrun ho hy
      obtain ⟨hcur, -⟩ := J.curEq hct
      have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
      rcases hrc with ⟨h0, h0'⟩ | ⟨hcr, q, g', e, xr, hkr⟩
      · exact jRecvIpcUDN hAT hmax hmb htu J hctT hcur hN hnq p b sd g gr rc rc' hpE (Or.inl ⟨h0, h0'⟩)
          hHd hHr (Or.inl h0) hP
      · subst e
        by_cases hi0 : L.mem s (Endp.rTcbA q) = 0#u64
        · exact jRecvIpcUDN hAT hmax hmb htu J hctT hcur hN hnq p b sd g gr _ rc' hpE
            (Or.inr ⟨hcr, q, g', rfl, xr, hkr⟩) hHd hHr (Or.inr ⟨q, g', rfl, hi0⟩) hP
        · exact jRecvIpcLinkDN hAT hmax hmb htu J hctT hcur hN hnq p b sd g gr q g' rc' hpE hcr hkr hHd
            (hHr q g' rfl) hi0 hP
  sig := fun _ _ _ _ _ _ _ _ _ hC hy => absurd hy (not_ctSc_of hok hC)
  flt := fun _ _ _ _ _ hC hy => absurd hy (not_ctSc_of hok hC)

/-- **`JMidLeavesHyp16` from `JMidLeavesHyp17` and the first-phase fact**. -/
theorem jMidLeavesHyp_of17 (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    {cptr : Fl4Spec.CapRef} {σ : Fl4Spec.State Unit}
    (hF : ∀ y ∈ ((Fl4Spec.fl4HandleInvocationR (Z := Unit) true false false true true cptr).run σ).1,
      MidRun.CtOK y.2)
    (hL : JMidLeavesHyp17 (L := L) arI AR cptr σ) : JMidLeavesHyp16 (L := L) arI AR cptr σ := by
  intro y hy hok ha hnq hsw hvf s1 a1 hR hrun hni1 Z H Cs Ac Lst D J _ ct hct
  exact (hL y hy hok ha hnq hsw hvf s1 a1 hR hrun hni1 Z H Cs Ac Lst D J ct hct).toRN16 hAT hmax hmb (htu a1)
    J hct hni1 hrun hnq (hF y hy)

end

end

end Fl4Proofs.P3
