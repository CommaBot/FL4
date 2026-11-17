/-
P3 (DESIGN.md §9), CSpace: **the scheduler's spec invariants across a
CNode-only step** (`KeepC`: only CNode objects change, and the state's other
fields kept, `CnK`'s `abs0`): the invariants read no CNode, so they are kept
(`NSC`, `Inv`, `CurInv`, `OffOK`, `ActIdle`, `BlockedScActive`, `ScLinkHyp`,
`CurOwn`, `CurRun`). For the slot steps of `JAtZ`'s closure (an insertion, a
CNode-only step).
-/
import Fl4Proofs.P3.XTopJointStep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched Fl4Proofs.P3.Ipc

noncomputable section

section Spec
open Fl4Spec

/-- A step changing only CNode objects, the ready queues and the scheduler
action (a scheduler step's or a CNode-only step's shape). -/
structure HStep (σ σ' : State Unit) : Prop where
  kc : KeepC σ σ'
  rel : σ'.releaseQueue = σ.releaseQueue
  ct : σ'.curThread = σ.curThread
  csc : σ'.curSc = σ.curSc
  time : σ'.curTime = σ.curTime
  cons : σ'.consumedTime = σ.consumedTime
  idle : σ'.idleThread = σ.idleThread

/-- A CNode-only step: only CNode objects change; the scheduler's fields
kept. -/
structure CnStep (σ σ' : State Unit) : Prop extends HStep σ σ' where
  rq : σ'.readyQueues = σ.readyQueues
  act : σ'.schedulerAction = σ.schedulerAction

theorem CnStep.of_cnK {σ σ' : State Unit} (hK : CnK σ σ') (hC : KeepC σ σ') : CnStep σ σ' :=
  ⟨⟨hC, (by have e := congrArg AbstractState.releaseQueue hK.1; exact e),
    (by have e := congrArg AbstractState.curThread hK.1; exact e), (by have e := congrArg AbstractState.curSc hK.1; exact e),
    (by have e := congrArg AbstractState.curTime hK.1; exact e),
    (by have e := congrArg AbstractState.consumedTime hK.1; exact e), (by have e := congrArg AbstractState.idleThread hK.1; exact e)⟩,
    (by have e := congrArg AbstractState.readyQueues hK.1; exact e),
    (by have e := congrArg AbstractState.schedulerAction hK.1; exact e)⟩

variable {σ σ' : State Unit}

/-- A lookup of a non-CNode object is the same after. -/
theorem HStep.look (h : HStep σ σ') {p : ObjRef} {ko : KernelObject} (hko : ∀ r cs, ko ≠ .cnode r cs) :
    σ'.kheap p = some ko ↔ σ.kheap p = some ko := by
  rcases h.kc p with e | ⟨r, cs, cs', h1, h2⟩
  · rw [e]
  · rw [h1, h2]; exact ⟨fun e => absurd (Option.some.inj e).symm (hko _ _), fun e => absurd (Option.some.inj e).symm (hko _ _)⟩

theorem HStep.tcb (h : HStep σ σ') {p : ObjRef} {x : Tcb} :
    σ'.kheap p = some (.tcb x) ↔ σ.kheap p = some (.tcb x) := h.look (fun _ _ e => by cases e)
theorem HStep.sc (h : HStep σ σ') {p : ObjRef} {y : SchedContext} {n : Nat} :
    σ'.kheap p = some (.schedContext y n) ↔ σ.kheap p = some (.schedContext y n) := h.look (fun _ _ e => by cases e)
theorem HStep.ntfn (h : HStep σ σ') {p : ObjRef} {x : Notification} :
    σ'.kheap p = some (.notification x) ↔ σ.kheap p = some (.notification x) := h.look (fun _ _ e => by cases e)

theorem HStep.sched_eq (h : HStep σ σ') (t : ObjRef) : Fl4Spec.schedulable t σ' = Fl4Spec.schedulable t σ := by
  cases e : Fl4Spec.schedulable t σ with
  | true =>
    obtain ⟨x, scp, y, n, h1, h2, h3, h4, h5, h6⟩ := schedulable_inv e
    exact schedulable_of (h.tcb.2 h1) h2 h3 (h.sc.2 h4) h5 (by rw [h.rel]; exact h6)
  | false =>
    cases e' : Fl4Spec.schedulable t σ' with
    | false => rfl
    | true =>
      obtain ⟨x, scp, y, n, h1, h2, h3, h4, h5, h6⟩ := schedulable_inv e'
      rw [schedulable_of (h.tcb.1 h1) h2 h3 (h.sc.1 h4) h5 (by rw [← h.rel]; exact h6)] at e
      cases e

theorem Sched.NSC.cn {N C : Set U64} (hN : NSC N C σ) (h : HStep σ σ') : NSC N C σ' :=
  fun n hn x p hx hp => hN n hn x p (h.ntfn.1 hx) hp

theorem CurRun.cn (hR : CurRun σ) (h : HStep σ σ') : CurRun σ' := fun x hx =>
  hR x (by rw [← h.ct]; exact h.tcb.1 hx)

theorem CurRunW.cn (hR : CurRunW σ) (h : HStep σ σ') : CurRunW σ' :=
  Or.imp (fun r => r.cn h) (fun e => by rw [h.ct, h.idle]; exact e) hR

theorem Sched.ScLinkHyp.cn (hL : ScLinkHyp σ) (h : HStep σ σ') : ScLinkHyp σ' := by
  refine ⟨fun sc y k f hy hf => ?_, fun sc y k n hy hn => ?_, fun t x n ht hn => ?_, fun sc y k hy hs =>
    hL.scSpor sc y k (h.sc.1 hy) hs⟩
  · obtain ⟨x, hx⟩ := hL.scTcb sc y k f (h.sc.1 hy) hf; exact ⟨x, h.tcb.2 hx⟩
  · obtain ⟨x, hx⟩ := hL.scNtfn sc y k n (h.sc.1 hy) hn; exact ⟨x, h.ntfn.2 hx⟩
  · obtain ⟨x', hx'⟩ := hL.tcbNtfn t x n (h.tcb.1 ht) hn; exact ⟨x', h.ntfn.2 hx'⟩

theorem Sched.BlockedScActive.cn (hB : BlockedScActive σ) (h : HStep σ σ') : BlockedScActive σ' :=
  ⟨fun p y n t x hp hyt hx hq => hB.tcb p y n t x (h.sc.1 hp) hyt (h.tcb.1 hx) hq,
    fun p y n hp hr => hB.replies p y n (h.sc.1 hp) hr⟩

theorem Sched.CurInv.cn (hI : CurInv σ) (h : HStep σ σ') : CurInv σ' := by
  obtain ⟨xt, hkt, hxs, hnb⟩ := hI.tcb
  obtain ⟨x, n, hx⟩ := hI.sc
  refine ⟨⟨xt, by rw [h.ct]; exact h.tcb.2 hkt, by rw [h.csc]; exact hxs, hnb⟩,
    ⟨x, n, by rw [h.csc]; exact h.sc.2 hx⟩, fun hne y m hy => ?_, by rw [h.ct, h.rel]; exact hI.notRel⟩
  rw [h.csc] at hne hy
  exact hI.active hne y m (h.sc.1 hy)

theorem Sched.OffOK.cn (hO : OffOK σ) (h : HStep σ σ') : OffOK σ' := by
  intro hc y n hy
  rw [h.cons] at hc ⊢; rw [h.time]
  rw [h.csc] at hy
  exact hO hc y n (h.sc.1 hy)

theorem Sched.ActIdle.cn (hA : ActIdle σ) (h : CnStep σ σ') : ActIdle σ' := by
  obtain ⟨hS, x, hx, h1, h2, h3⟩ := hA
  refine ⟨fun t ht => ?_, x, by rw [h.idle]; exact h.tcb.2 hx, h1, h2, by rw [h.idle, h.rel]; exact h3⟩
  rw [h.act] at ht
  rw [h.toHStep.sched_eq]; exact hS t ht

theorem Sched.CurOwn.cn {T : Set U64} (hO : CurOwn T σ) (h : HStep σ σ') : CurOwn T σ' := by
  obtain ⟨u, hu, xt, hkt, hxs, hown, hnr⟩ := hO
  refine ⟨u, hu, xt, h.tcb.2 hkt, by rw [h.csc]; exact hxs, fun y n hy => ?_, fun h0 hm => ?_⟩
  · rw [h.csc] at hy; exact hown y n (h.sc.1 hy)
  · rw [h.cons] at h0; rw [h.rel] at hm; exact hnr h0 hm

theorem Sched.CurOwnW.cn {T C : Set U64} (hO : CurOwnW T C σ) (h : HStep σ σ') : CurOwnW T C σ' :=
  hO.imp (fun o => o.cn h) h.csc fun y n hy => Or.inr ⟨y, h.sc.1 hy, rfl⟩

theorem specRt_cn (h : HStep σ σ') {u scp : ObjRef} {x : Tcb} {y : SchedContext} {n : Nat}
    (hk : σ.kheap u = some (.tcb x)) (hsc : x.tcbSchedContext = some scp)
    (hky : σ.kheap scp = some (.schedContext y n)) (hne : y.scRefills ≠ []) : specRt σ' u = specRt σ u := by
  rw [specRt_eq (h.tcb.2 hk) hsc (h.sc.2 hky) hne, specRt_eq hk hsc hky hne]

theorem Sched.Inv.cn (hI : Inv σ) (h : CnStep σ σ') : Inv σ' := by
  refine ⟨fun d p u hu => ?_, fun u hu => ?_, ?_, fun u x hx hc => ?_, fun p y n hy => hI.refills p y n (h.sc.1 hy),
    fun u x p hx hp => ?_, fun q x p hx hp => ?_, fun p y n hy => hI.ne p y n (h.sc.1 hy),
    fun p y n hy => hI.rr p y n (h.sc.1 hy)⟩
  · rw [h.rq] at hu
    obtain ⟨x, scp, y, n, h1, h2, h3, h4, h5⟩ := hI.rq d p u hu
    exact ⟨x, scp, y, n, h.tcb.2 h1, h2, h3, h.sc.2 h4, h5⟩
  · rw [h.rel] at hu
    obtain ⟨x, scp, y, n, h1, h2, h3, h4, h5⟩ := hI.rel u hu
    exact ⟨x, scp, y, n, h.tcb.2 h1, h2, h3, h.sc.2 h4, h5⟩
  · rw [h.rel]
    refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab => ?_) hI.sorted
    obtain ⟨xa, pa, ya, na, h1, h2, -, h4, h5⟩ := hI.rel a ha
    obtain ⟨xb, pb, yb, nb, g1, g2, -, g4, g5⟩ := hI.rel b hb
    rw [specRt_cn h.toHStep h1 h2 h4 (hI.ne _ _ _ h4 h5), specRt_cn h.toHStep g1 g2 g4 (hI.ne _ _ _ g4 g5)]
    exact hab
  · intro x' scp y n h1 h2 h3 h4 h5
    rw [h.rel] at h5
    have hr := hI.rd u x (h.tcb.1 hx) hc x' scp y n (h.tcb.1 h1) h2 (h.sc.1 h3) h4 h5
    unfold released at hr ⊢; rw [h.time]; exact hr
  · obtain ⟨y, n, hy, hyt⟩ := hI.back u x p (h.tcb.1 hx) hp
    exact ⟨y, n, h.sc.2 hy, hyt⟩
  · obtain ⟨y, n, hy⟩ := hI.ntfnSc q x p (h.ntfn.1 hx) hp
    exact ⟨y, n, h.sc.2 hy⟩

theorem prioOf_cn (h : HStep σ σ') (u : ObjRef) : Sched.prioOf σ' u = Sched.prioOf σ u := by
  rcases h.kc u with e | ⟨r, cs, cs', h1, h2⟩
  · unfold Sched.prioOf tcbsOf tcbsOfKh optMap; rw [e]
  · unfold Sched.prioOf tcbsOf tcbsOfKh optMap; rw [h1, h2]; rfl

theorem Sched.IpcSorted.cn (hS : IpcSorted σ) (h : HStep σ σ') : IpcSorted σ' :=
  ⟨fun p x hp => (hS.1 p x ((h.look (fun _ _ e => by cases e)).1 hp)).congr fun u _ => prioOf_cn h u,
    fun p x hp => (hS.2 p x (h.ntfn.1 hp)).congr fun u _ => prioOf_cn h u⟩

theorem CurInvW.cn (hC : σ.schedulerAction = .chooseNewThread ∨ CurInv σ) (h : CnStep σ σ') :
    σ'.schedulerAction = .chooseNewThread ∨ CurInv σ' := by
  rcases hC with e | hI
  · left; rw [h.act]; exact e
  · right; exact hI.cn h.toHStep

end Spec

end

end Fl4Proofs.P3
