/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN sch17): **`kernel_entryJ13M`:
the reply-pushing head senders proved under a pending switch.**
`JMidLeavesHyp3` [W] (XTopJointKEntry12M) asked `receive_ipc` under
`IpcOpen` (a pending reschedule, or not `IpcDoneM`). At a switch mid state
(`MidE`, action `switchThread u`, u ≠ ct) XTopJointRecvSendPM proves two
more unlinked cases, ending in `JAtZ` (so `RJR` by `.toR`):

* `RecvSendPushCase` (a head sender in `PushOK`: the reply is pushed and the
  sender blocks on it; the receiver not lending its SC):
  `JAtZ.recvSendP0XM`;
* `RecvSendTmoCaseM` (a head sender with a timeout fault and an SC,
  `TmoOK`, the same receiver): `JAtZ.recvSendT0XM`.

`IpcDoneM2` = `IpcDoneM` or one of these with a null or free reply,
`jRecvIpcDoneM2`; `IpcOpen2` = a pending reschedule or not `IpcDoneM2`;
`JRecvLeavesRN4` (`JRecvLeavesRN3` with the endpoint receive asked only under
`IpcOpen2`), `.toRN3`; `JMidLeavesHyp4` [W] = `JMidLeavesHyp3` concluding
`JRecvLeavesRN4` (same l4v counterpart: receive_ipc_corres /
receive_signal_corres / handle_fault_corres inside handle_recv_corres under
scheduler_act_sane; every case left is a case of sch15's `JMidLeavesHyp`,
true in reachable states), `jMidLeavesHyp_of4`, `KDispHyps13M`, `.to12M`,
NEW TOP `kernel_entryJ13M` = `kernel_entryJ12M` with `KDispHyps13M`.

(p3J gen 53) Each receive leaf ending in `RJR` / `RJ` here has a post-parametric form `…Q` (post
`RelTopM ∧ Pq`, `Pq` from every `JAtZR` / `JAtZ` at `Z.mv G V` with the entry's `H`, `Cs` by `hPq`; the proof moved
there); the original statement is unchanged and is its one-line instance. No new premises.
-/
import Fl4Proofs.P3.XTopJointRecvSendPM
import Fl4Proofs.P3.XTopJointKEntry12M
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- The case `JAtZ.recvSendT0XM` proves: the receiver as in
`RecvSendPushCase` (blocking), the endpoint's head sender with a timeout
fault and an SC (`TmoOK`). -/
def RecvSendTmoCaseM (ct : U64) (σ : Fl4Spec.State Unit) (p : U64) : Prop :=
  (∀ xt, σ.kheap ct.bv = some (.tcb xt) → xt.tcbBoundNotification = none ∨
    ∃ n xn, xt.tcbBoundNotification = some n ∧ σ.kheap n = some (.notification xn) ∧
      Fl4Spec.isActive xn = false ∧ (true = true → ¬ (xn.ntfnSc = xt.tcbSchedContext ∧ xn.ntfnSc ≠ none))) ∧
    ∃ sd q xs, σ.kheap p.bv = some (.endpoint (.sendEP (sd :: q))) ∧ σ.kheap sd = some (.tcb xs) ∧ TmoOK xs

/-- **The endpoint receives proved at a switch mid state, sch17** (module
docstring). -/
def IpcDoneM2 (ct : U64) (s : S) (σ : Fl4Spec.State Unit) (p : U64) (rc : capability.Cap) : Prop :=
  IpcDoneM (L := L) ct s σ p rc ∨
    ((rc = .Null ∨ ∃ q g', rc = .Reply q g' ∧ L.mem s (rTcbA q) = 0#u64) ∧
      (RecvSendPushCase ct true σ p rc ∨ RecvSendTmoCaseM ct σ p))

/-- The endpoint receives `JRecvLeavesRN4` still asks (module docstring). -/
def IpcOpen2 (ct : U64) (s : S) (σ : Fl4Spec.State Unit) (p : U64) (rc : capability.Cap) : Prop :=
  σ.schedulerAction = .chooseNewThread ∨ ¬ IpcDoneM2 (L := L) ct s σ p rc

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 53) **`jRecvIpcDoneM2` with its post as a parameter** (module docstring: `Pq` from every `JAtZR` at `Z.mv G V` with the entry's `H`, `Cs`; `jRecvIpcDoneM2` is its instance at `RJR`). -/
theorem jRecvIpcDoneM2Q (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] {ct : U64}
    (ht : ct ∈ Z.T) (hcur : σ.curThread = ct.bv) (hni : MidE σ) (hsw : σ.schedulerAction ≠ .resumeCurThread)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (p b : U64) (sd g gr : Bool) (rc : capability.Cap) (rc' : Fl4Spec.Cap)
    (hpE : ∃ x, σ.kheap p.bv = some (.endpoint x))
    (hrc : (rc = .Null ∧ rc' = .nullCap) ∨
      (CapRel rc rc' ∧ ∃ q g', rc = .Reply q g' ∧ ∃ x, σ.kheap q.bv = some (.reply x)))
    (hHd : JHeld (L := L) Z.th s (.Endpoint p b sd true g gr))
    (hHr : ∀ q g', rc = .Reply q g' → JHeld (L := L) Z.th s rc)
    (hD : IpcDoneM2 (L := L) ct s σ p rc)
    {Pq : S → A → Fl4Spec.State Unit → Prop}
    (hPq : ∀ (G : MdbGhost) (V : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64) (s' : S)
      (a' : A) (σ' : Fl4Spec.State Unit), JAtZR (L := L) arI AR (Z.mv G V) H Cs Ac' Lst' D' s' a' σ' → Pq s' a' σ') :
    endpoint.receive_ipc st arI s a ct (.Endpoint p b sd true g gr) true rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) true rc' σ).1,
        RelTopM (L := L) r.1 z.2 ∧ Pq r.1 r.2 z.2 ⦄ := by
  rcases hD with hD | ⟨hun, hcp | hcT⟩
  · exact jRecvIpcDoneMQ hAT J ht hcur hni hsw hnq p b sd g gr rc rc' hpE hrc hHd hHr hD hPq
  all_goals
    obtain ⟨xe, hke⟩ := hpE
    obtain ⟨e, he, h⟩ := J.obj.ep _ xe hke
    rw [Sched.bv_inj h] at he
    have hA : ∃ u, σ.schedulerAction = .switchThread u ∧ u ≠ ct.bv := by
      obtain ⟨u, e1, hu⟩ := hni.2.2.resolve_left hsw
      exact ⟨u, e1, by rw [← hcur]; exact hu⟩
    have hI := J.xtop.irelK J.ks J.buf
    obtain ⟨xt, hkt, -⟩ := hI.1.tcb ct ht
    obtain ⟨rv, hra⟩ := J.replyArg_of hrc hun
    have hrun := hni.run xt (by rw [hcur]; exact hkt)
  · obtain ⟨hbn, sd0, q, xs, hke', hks, hok⟩ := hcp
    obtain ⟨sdU, -, hsde⟩ := J.obj.tcb _ xs hks
    subst hsde
    have hrv0 : rv ≠ 0#u64 := by
      rcases hra with ⟨h1, -, -⟩ | ⟨_, _, _, _, hr, -⟩
      · exact absurd h1 hok.1
      · exact (J.rp.align rv hr).2.1
    obtain ⟨-, hcovR⟩ := J.recvCov_of he hHd hHr hra
    exact J.recvSendP0XMQ hAT ht hkt hrun (hbn xt hkt) hcur hni.1 hnq hA he hke' hks b sd true g gr hra
      (hcovR hrv0) hok b.bv (rightsOf sd true g gr) (fun _ _ _ _ _ _ _ _ J' => hPq _ _ _ _ _ _ _ _ J'.toR)
  · obtain ⟨hbn, sd0, q, xs, hke', hks, hok⟩ := hcT
    obtain ⟨sdU, -, hsde⟩ := J.obj.tcb _ xs hks
    subst hsde
    exact J.recvSendT0XMQ hAT hmax htu ht hkt hrun (hbn xt hkt) hcur hni.1 hnq hA he hke' hks
      b sd true g gr hra (J.recvCov_of he hHd hHr hra).2 hok b.bv (rightsOf sd true g gr) (fun _ _ _ _ _ _ _ _ J' => hPq _ _ _ _ _ _ _ _ J'.toR)

set_option maxHeartbeats 4000000 in
/-- **`IpcDoneM2`'s receives at a switch mid state** (module docstring). -/
theorem jRecvIpcDoneM2 (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] {ct : U64}
    (ht : ct ∈ Z.T) (hcur : σ.curThread = ct.bv) (hni : MidE σ) (hsw : σ.schedulerAction ≠ .resumeCurThread)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (p b : U64) (sd g gr : Bool) (rc : capability.Cap) (rc' : Fl4Spec.Cap)
    (hpE : ∃ x, σ.kheap p.bv = some (.endpoint x))
    (hrc : (rc = .Null ∧ rc' = .nullCap) ∨
      (CapRel rc rc' ∧ ∃ q g', rc = .Reply q g' ∧ ∃ x, σ.kheap q.bv = some (.reply x)))
    (hHd : JHeld (L := L) Z.th s (.Endpoint p b sd true g gr))
    (hHr : ∀ q g', rc = .Reply q g' → JHeld (L := L) Z.th s rc)
    (hD : IpcDoneM2 (L := L) ct s σ p rc) :
    endpoint.receive_ipc st arI s a ct (.Endpoint p b sd true g gr) true rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) true rc' σ).1,
        RJR (L := L) arI AR r.1 r.2 z.2 ⦄ :=
  jRecvIpcDoneM2Q (Pq := fun s' a' σ' => ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    JAtZR (L := L) arI AR Z H Cs Ac Lst D s' a' σ' ∧ VxE Z)
    hAT hmax htu J ht hcur hni hsw hnq p b sd g gr rc rc' hpE hrc hHd hHr hD (fun _ _ _ _ _ _ _ _ J' => ⟨_, _, _, _, _, _, J', inferInstance⟩)

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JRecvLeavesRN3` with the endpoint receive narrowed to `IpcOpen2`**
(module docstring). -/
structure JRecvLeavesRN4 (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) (ct : U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop where
  ipc : ∀ p b sd g gr rc rc', (∃ x, σ.kheap p.bv = some (.endpoint x)) →
    ((rc = .Null ∧ rc' = .nullCap) ∨
      (CapRel rc rc' ∧ ∃ q g', rc = .Reply q g' ∧ ∃ x, σ.kheap q.bv = some (.reply x))) →
    JHeld (L := L) th s (.Endpoint p b sd true g gr) → (∀ q g', rc = .Reply q g' → JHeld (L := L) th s rc) →
    IpcOpen2 (L := L) ct s σ p rc →
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
(module docstring): `JMidLeavesHyp3` concluding `JRecvLeavesRN4`. -/
def JMidLeavesHyp4 (AR : A → Fl4Spec.Cr3 → Prop) (cptr : Fl4Spec.CapRef) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ y ∈ ((Fl4Spec.fl4HandleInvocationR (Z := Unit) true false false true true cptr).run σ).1, y.1 = .ok () →
    y.2.schedulerAction ≠ .resumeCurThread → (∀ d p, y.2.curThread ∉ y.2.readyQueues d p) →
    y.2.schedulerAction ≠ .switchThread y.2.curThread →
    (∀ x, y.2.kheap y.2.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler) →
    ∀ (s1 : S) (a1 : A), RelTopM (L := L) s1 y.2 → CurRun y.2 → y.2.curThread ≠ y.2.idleThread →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s1 a1 y.2 → [VxE Z] → ∀ ct, sched.cur_thread st s1 = ok ct →
        JRecvLeavesRN4 (L := L) arI AR Z.th ct s1 a1 y.2

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop}

/-- **`JRecvLeavesRN3` from `JRecvLeavesRN4`** at a non-resumed mid state
with no switch to ct: `jRecvIpcDoneM2` outside `IpcOpen2`. -/
theorem JRecvLeavesRN4.toRN3 (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] {ct : U64} (hct : sched.cur_thread st s = ok ct)
    (hni1 : σ.curThread ≠ σ.idleThread) (hrun : CurRun σ) (hsw : σ.schedulerAction ≠ .resumeCurThread)
    (hsc : σ.schedulerAction ≠ .switchThread σ.curThread) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (h : JRecvLeavesRN4 (L := L) arI AR Z.th ct s a σ) : JRecvLeavesRN3 (L := L) arI AR Z.th ct s a σ where
  sig := h.sig
  flt := h.flt
  ipc := fun p b sd g gr rc rc' hpE hrc hHd hHr _ => by
    by_cases ho : IpcOpen2 (L := L) ct s σ p rc
    · exact h.ipc p b sd g gr rc rc' hpE hrc hHd hHr ho
    · obtain ⟨hcur, -⟩ := J.curEq hct
      have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
      have hE : MidE σ := by
        refine ⟨hni1, hrun, Or.inr ?_⟩
        cases e : σ.schedulerAction with
        | resumeCurThread => exact absurd e hsw
        | chooseNewThread => exact absurd (Or.inl e) ho
        | switchThread u => exact ⟨u, rfl, fun hu => hsc (by rw [e, hu])⟩
      exact jRecvIpcDoneM2 hAT hmax htu J hctT hcur hE hsw hnq p b sd g gr rc rc' hpE hrc hHd hHr
        (Classical.not_not.1 fun hd => ho (Or.inr hd))

/-- **`JMidLeavesHyp3` from `JMidLeavesHyp4`** (module docstring). -/
theorem jMidLeavesHyp_of4 (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    {cptr : Fl4Spec.CapRef} {σ : Fl4Spec.State Unit}
    (hL : JMidLeavesHyp4 (L := L) arI AR cptr σ) : JMidLeavesHyp3 (L := L) arI AR cptr σ := by
  intro y hy hok ha hnq hsw hvf s1 a1 hR hrun hni1 Z H Cs Ac Lst D J _ ct hct
  exact (hL y hy hok ha hnq hsw hvf s1 a1 hR hrun hni1 Z H Cs Ac Lst D J ct hct).toRN3 hAT hmax (htu a1) J hct hni1
    hrun ha hsw hnq

end

end

end Fl4Proofs.P3
