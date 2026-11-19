/-
P3 (DESIGN.md §9), VSpace: **the spec's side of `MakePool` at `J`** (spec
only; toward XTopJointMakePool's `JAtZ` after the ASID control cap's
`MakePool` when its region is clean).

* `MpFr σ σ'`: every object kept, a CNode replaced by one of the same
  radix, or an empty cell given an arch object (the pool); the scheduler's
  fields kept. `MakePool`'s spec step from the restart's state has this
  shape once the region holds no object (VsMakePoolRel's `MpMid`).
* The scheduler's spec invariants across an `MpFr` step (as
  XTopJointFinVsSpec's for `ArFr`: they read no CNode and no arch object):
  `NSC`, `Inv`, `CurInv`, `OffOK`, `ActIdle`, `BlockedScActive`, `CurOwnW`,
  `IpcSorted`, `CurRunM`; the global PML4 kept a PML4 (`HasPm`).
-/
import Fl4Proofs.P3.XTopJointFinVsSpec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched Fl4Proofs.P3.Ipc

noncomputable section

section Spec
open Fl4Spec

/-- **The frame of `MakePool`'s spec step** (module docstring). -/
structure MpFr (σ σ' : State Unit) : Prop where
  kh : ∀ p, σ'.kheap p = σ.kheap p ∨
    (∃ r cs cs', σ.kheap p = some (.cnode r cs) ∧ σ'.kheap p = some (.cnode r cs')) ∨
    (σ.kheap p = none ∧ ∃ a, σ'.kheap p = some (.archObj a))
  ct : σ'.curThread = σ.curThread
  idle : σ'.idleThread = σ.idleThread
  cons : σ'.consumedTime = σ.consumedTime
  time : σ'.curTime = σ.curTime
  csc : σ'.curSc = σ.curSc
  isc : σ'.idleSc = σ.idleSc
  act : σ'.schedulerAction = σ.schedulerAction
  rq : σ'.readyQueues = σ.readyQueues
  rel : σ'.releaseQueue = σ.releaseQueue
  gpml4 : σ'.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4

variable {σ σ' : State Unit}

/-- A lookup of an object other than a CNode or an arch object is the same
after. -/
theorem MpFr.look (h : MpFr σ σ') {p : ObjRef} {ko : KernelObject} (hk : ∀ a, ko ≠ .archObj a)
    (hc : ∀ r cs, ko ≠ .cnode r cs) : σ'.kheap p = some ko ↔ σ.kheap p = some ko := by
  rcases h.kh p with e | ⟨r, cs, cs', h1, h2⟩ | ⟨h1, a, h2⟩
  · rw [e]
  · rw [h1, h2]
    exact ⟨fun e => absurd (Option.some.inj e).symm (hc _ _), fun e => absurd (Option.some.inj e).symm (hc _ _)⟩
  · rw [h1, h2]
    exact ⟨fun e => absurd (Option.some.inj e).symm (hk _), fun e => by cases e⟩

theorem MpFr.tcbF (h : MpFr σ σ') {p : ObjRef} {x : Tcb} (hx : σ.kheap p = some (.tcb x)) :
    ∃ y, σ'.kheap p = some (.tcb y) ∧ CapsOnly x y :=
  ⟨x, (h.look (fun _ e => by cases e) (fun _ _ e => by cases e)).2 hx, CapsOnly.refl x⟩

theorem MpFr.tcbB (h : MpFr σ σ') {p : ObjRef} {y : Tcb} (hy : σ'.kheap p = some (.tcb y)) :
    ∃ x, σ.kheap p = some (.tcb x) ∧ CapsOnly x y :=
  ⟨y, (h.look (fun _ e => by cases e) (fun _ _ e => by cases e)).1 hy, CapsOnly.refl y⟩

theorem MpFr.sc (h : MpFr σ σ') {p : ObjRef} {y : SchedContext} {n : Nat} :
    σ'.kheap p = some (.schedContext y n) ↔ σ.kheap p = some (.schedContext y n) :=
  h.look (fun _ e => by cases e) (fun _ _ e => by cases e)
theorem MpFr.ntfn (h : MpFr σ σ') {p : ObjRef} {x : Notification} :
    σ'.kheap p = some (.notification x) ↔ σ.kheap p = some (.notification x) :=
  h.look (fun _ e => by cases e) (fun _ _ e => by cases e)
theorem MpFr.ep (h : MpFr σ σ') {p : ObjRef} {x : Endpoint} :
    σ'.kheap p = some (.endpoint x) ↔ σ.kheap p = some (.endpoint x) :=
  h.look (fun _ e => by cases e) (fun _ _ e => by cases e)
theorem MpFr.reply (h : MpFr σ σ') {p : ObjRef} {x : Reply} :
    σ'.kheap p = some (.reply x) ↔ σ.kheap p = some (.reply x) :=
  h.look (fun _ e => by cases e) (fun _ _ e => by cases e)
theorem MpFr.tcb (h : MpFr σ σ') {p : ObjRef} {x : Tcb} :
    σ'.kheap p = some (.tcb x) ↔ σ.kheap p = some (.tcb x) :=
  h.look (fun _ e => by cases e) (fun _ _ e => by cases e)

/-- An arch object before is kept. -/
theorem MpFr.arch (h : MpFr σ σ') {p : ObjRef} {a : ArchKernelObj} (hp : σ.kheap p = some (.archObj a)) :
    σ'.kheap p = some (.archObj a) := by
  rcases h.kh p with e | ⟨r, cs, cs', h1, h2⟩ | ⟨h1, a', h2⟩
  · rw [e]; exact hp
  · rw [hp] at h1; cases h1
  · rw [hp] at h1; cases h1

theorem MpFr.recvB (h : MpFr σ σ') {d : U64} (hd : RecvB σ' d) : RecvB σ d := by
  obtain ⟨x, t, xt, h1, h2, h3, h4⟩ := hd
  exact ⟨x, t, xt, h.reply.1 h1, h2, h.tcb.1 h3, h4⟩

theorem MpFr.szKeep (h : MpFr σ σ') : Sched.SzKeep σ σ' := fun _ x _ hp => ⟨x, h.sc.1 hp⟩

theorem MpFr.hasPm (h : MpFr σ σ') {g : ObjRef} (hp : HasPm σ g) : HasPm σ' g := by
  obtain ⟨pt, hpt⟩ := hp
  exact ⟨pt, h.arch hpt⟩

theorem MpFr.sched_eq (h : MpFr σ σ') (t : ObjRef) : Fl4Spec.schedulable t σ' = Fl4Spec.schedulable t σ := by
  cases e : Fl4Spec.schedulable t σ with
  | true =>
    obtain ⟨x, scp, y, n, h1, h2, h3, h4, h5, h6⟩ := schedulable_inv e
    obtain ⟨x', hx', hc⟩ := h.tcbF h1
    exact schedulable_of hx' (by rw [hc.sc]; exact h2) (by rw [hc.st]; exact h3) (h.sc.2 h4) h5
      (by rw [h.rel]; exact h6)
  | false =>
    cases e' : Fl4Spec.schedulable t σ' with
    | false => rfl
    | true =>
      obtain ⟨x, scp, y, n, h1, h2, h3, h4, h5, h6⟩ := schedulable_inv e'
      obtain ⟨x', hx', hc⟩ := h.tcbB h1
      rw [schedulable_of hx' (by rw [← hc.sc]; exact h2) (by rw [← hc.st]; exact h3) (h.sc.1 h4) h5
        (by rw [← h.rel]; exact h6)] at e
      cases e

theorem Sched.NSC.mp {N C : Set U64} (hN : NSC N C σ) (h : MpFr σ σ') : NSC N C σ' :=
  fun n hn x p hx hp => hN n hn x p (h.ntfn.1 hx) hp

theorem CurRun.mp (hR : CurRun σ) (h : MpFr σ σ') : CurRun σ' := fun y hy => by
  rw [h.ct] at hy
  obtain ⟨x, hx, hc⟩ := h.tcbB hy
  rw [hc.st]; exact hR x hx

theorem CurRunW.mp (hR : CurRunW σ) (h : MpFr σ σ') : CurRunW σ' :=
  Or.imp (fun r => r.mp h) (fun e => by rw [h.ct, h.idle]; exact e) hR

theorem CurRunM.mp (hR : CurRunM σ) (h : MpFr σ σ') : CurRunM σ' :=
  Or.imp (fun e' => by rw [h.act]; exact e') (fun r => r.mp h) hR

theorem Sched.BlockedScActive.mp (hB : BlockedScActive σ) (h : MpFr σ σ') : BlockedScActive σ' :=
  ⟨fun p y n t x hp hyt hx hq => by
      obtain ⟨x0, hx0, hc⟩ := h.tcbB hx
      exact hB.tcb p y n t x0 (h.sc.1 hp) hyt hx0 (by rw [← hc.st]; exact hq),
    fun p y n hp hr => hB.replies p y n (h.sc.1 hp) hr⟩

theorem Sched.CurInv.mp (hI : CurInv σ) (h : MpFr σ σ') : CurInv σ' := by
  obtain ⟨xt, hkt, hxs, hnb⟩ := hI.tcb
  obtain ⟨x, n, hx⟩ := hI.sc
  obtain ⟨yt, hyt, hc⟩ := h.tcbF hkt
  refine ⟨⟨yt, by rw [h.ct]; exact hyt, by rw [h.csc, hc.sc]; exact hxs, by rw [hc.st]; exact hnb⟩,
    ⟨x, n, by rw [h.csc]; exact h.sc.2 hx⟩, fun hne y m hy => ?_, by rw [h.ct, h.rel]; exact hI.notRel⟩
  rw [h.csc, h.isc] at hne; rw [h.csc] at hy
  exact hI.active hne y m (h.sc.1 hy)

theorem Sched.OffOK.mp (hO : OffOK σ) (h : MpFr σ σ') : OffOK σ' := by
  intro hc y n hy ha
  rw [h.cons] at hc ⊢; rw [h.time]
  rw [h.csc] at hy; rw [h.csc, h.isc] at ha
  exact hO hc y n (h.sc.1 hy) ha

theorem Sched.ActIdle.mp (hA : ActIdle σ) (h : MpFr σ σ') : ActIdle σ' := by
  obtain ⟨hS, x, hx, h1, h2, h3⟩ := hA
  obtain ⟨y, hy, hc⟩ := h.tcbF hx
  refine ⟨fun t ht => ?_, y, by rw [h.idle]; exact hy, by rw [hc.sc, h.isc]; exact h1, by rw [hc.st]; exact h2,
    by rw [h.idle, h.rel]; exact h3⟩
  rw [h.act] at ht
  rw [h.sched_eq]; exact hS t ht

theorem Sched.CurOwn.mp {T : Set U64} (hO : CurOwn T σ) (h : MpFr σ σ') : CurOwn T σ' := by
  obtain ⟨u, hu, xt, hkt, hxs, hown, hnr⟩ := hO
  obtain ⟨yt, hyt, hc⟩ := h.tcbF hkt
  refine ⟨u, hu, yt, hyt, by rw [h.csc, hc.sc]; exact hxs, fun y n hy => ?_, fun h0 hm => ?_⟩
  · rw [h.csc] at hy; exact hown y n (h.sc.1 hy)
  · rw [h.cons] at h0; rw [h.rel] at hm; exact hnr h0 hm

theorem Sched.CurOwnW.mp {T C : Set U64} (hO : CurOwnW T C σ) (h : MpFr σ σ') : CurOwnW T C σ' :=
  hO.imp (fun o => o.mp h) h.csc fun y n hy => Or.inr ⟨y, h.sc.1 hy, rfl⟩

theorem specRt_mp (h : MpFr σ σ') {u scp : ObjRef} {x : Tcb} {y : SchedContext} {n : Nat}
    (hk : σ.kheap u = some (.tcb x)) (hsc : x.tcbSchedContext = some scp)
    (hky : σ.kheap scp = some (.schedContext y n)) (hne : y.scRefills ≠ []) : specRt σ' u = specRt σ u := by
  obtain ⟨x', hx', hc⟩ := h.tcbF hk
  rw [specRt_eq hx' (by rw [hc.sc]; exact hsc) (h.sc.2 hky) hne, specRt_eq hk hsc hky hne]

theorem Sched.Inv.mp (hI : Inv σ) (h : MpFr σ σ') : Inv σ' := by
  refine ⟨fun d p u hu => ?_, fun u hu => ?_, ?_, fun u x hx hc => ?_, fun p y n hy => hI.refills p y n (h.sc.1 hy),
    fun u x p hx hp => ?_, fun q x p hx hp => ?_, fun p y n hy => hI.ne p y n (h.sc.1 hy),
    fun p y n hy => hI.rr p y n (h.sc.1 hy)⟩
  · rw [h.rq] at hu
    obtain ⟨x, scp, y, n, h1, h2, h3, h4, h5⟩ := hI.rq d p u hu
    obtain ⟨x', hx', hc⟩ := h.tcbF h1
    exact ⟨x', scp, y, n, hx', by rw [hc.sc]; exact h2, by rw [hc.st]; exact h3, h.sc.2 h4, h5⟩
  · rw [h.rel] at hu
    obtain ⟨x, scp, y, n, h1, h2, h3, h4, h5⟩ := hI.rel u hu
    obtain ⟨x', hx', hc⟩ := h.tcbF h1
    exact ⟨x', scp, y, n, hx', by rw [hc.sc]; exact h2, by rw [hc.st]; exact h3, h.sc.2 h4, h5⟩
  · rw [h.rel]
    refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab => ?_) hI.sorted
    obtain ⟨xa, pa, ya, na, h1, h2, -, h4, h5⟩ := hI.rel a ha
    obtain ⟨xb, pb, yb, nb, g1, g2, -, g4, g5⟩ := hI.rel b hb
    rw [specRt_mp h h1 h2 h4 (hI.ne _ _ _ h4 h5), specRt_mp h g1 g2 g4 (hI.ne _ _ _ g4 g5)]
    exact hab
  · obtain ⟨x0, hx0, hc0⟩ := h.tcbB hx
    intro x' scp y n h1 h2 h3 h4 h5
    rw [h.rel] at h5
    rw [hx] at h1; cases h1
    have hr := hI.rd u x0 hx0 (by rw [← hc0.st]; exact hc) x0 scp y n hx0 (by rw [← hc0.sc]; exact h2)
      (h.sc.1 h3) h4 h5
    unfold released at hr ⊢; rw [h.time]; exact hr
  · obtain ⟨x0, hx0, hc0⟩ := h.tcbB hx
    obtain ⟨y, n, hy, hyt⟩ := hI.back u x0 p hx0 (by rw [← hc0.sc]; exact hp)
    exact ⟨y, n, h.sc.2 hy, hyt⟩
  · obtain ⟨y, n, hy⟩ := hI.ntfnSc q x p (h.ntfn.1 hx) hp
    exact ⟨y, n, h.sc.2 hy⟩

theorem prioOf_mp (h : MpFr σ σ') (u : ObjRef) : Sched.prioOf σ' u = Sched.prioOf σ u := by
  rcases h.kh u with e | ⟨r, cs, cs', h1, h2⟩ | ⟨h1, a, h2⟩
  · unfold Sched.prioOf tcbsOf tcbsOfKh optMap; rw [e]
  · unfold Sched.prioOf tcbsOf tcbsOfKh optMap; rw [h1, h2]; rfl
  · unfold Sched.prioOf tcbsOf tcbsOfKh optMap; rw [h1, h2]; rfl

theorem Sched.IpcSorted.mp (hS : IpcSorted σ) (h : MpFr σ σ') : IpcSorted σ' :=
  ⟨fun p x hp => (hS.1 p x (h.ep.1 hp)).congr fun u _ => prioOf_mp h u,
    fun p x hp => (hS.2 p x (h.ntfn.1 hp)).congr fun u _ => prioOf_mp h u⟩

theorem CurInvW.mp (hC : σ.schedulerAction = .chooseNewThread ∨ CurInv σ) (h : MpFr σ σ') :
    σ'.schedulerAction = .chooseNewThread ∨ CurInv σ' := by
  rcases hC with e | hI
  · left; rw [h.act]; exact e
  · right; exact hI.mp h

end Spec

end

end Fl4Proofs.P3
