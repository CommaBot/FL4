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

/-- Every object kept, a CNode replaced by one of the same size, or a TCB by
one alike but for its caps (`CapsOnly`). -/
def KeepCT (σ σ' : State Unit) : Prop :=
  ∀ p, σ'.kheap p = σ.kheap p ∨ (∃ r cs cs', σ.kheap p = some (.cnode r cs) ∧ σ'.kheap p = some (.cnode r cs')) ∨
    ∃ x y, σ.kheap p = some (.tcb x) ∧ σ'.kheap p = some (.tcb y) ∧ CapsOnly x y

theorem KeepC.t {σ σ' : State Unit} (h : KeepC σ σ') : KeepCT σ σ' := fun p =>
  (h p).imp_right Or.inl

theorem KeepCT.of_cnK {σ σ' : State Unit} (h : CnK σ σ') : KeepCT σ σ' := fun p => h.2 p

/-- A step changing only CNode objects and TCBs' caps, the ready queues and
the scheduler action (a scheduler step's or a slot step's shape). -/
structure HStep (σ σ' : State Unit) : Prop where
  kc : KeepCT σ σ'
  rel : σ'.releaseQueue = σ.releaseQueue
  ct : σ'.curThread = σ.curThread
  csc : σ'.curSc = σ.curSc
  time : σ'.curTime = σ.curTime
  cons : σ'.consumedTime = σ.consumedTime
  idle : σ'.idleThread = σ.idleThread
  isc : σ'.idleSc = σ.idleSc

/-- A slot step: only CNode objects and TCBs' caps change; the scheduler's
fields kept. -/
structure CnStep (σ σ' : State Unit) : Prop extends HStep σ σ' where
  rq : σ'.readyQueues = σ.readyQueues
  act : σ'.schedulerAction = σ.schedulerAction

theorem CnStep.of_cnK {σ σ' : State Unit} (hK : CnK σ σ') : CnStep σ σ' :=
  ⟨⟨KeepCT.of_cnK hK, (by have e := congrArg AbstractState.releaseQueue hK.1; exact e),
    (by have e := congrArg AbstractState.curThread hK.1; exact e), (by have e := congrArg AbstractState.curSc hK.1; exact e),
    (by have e := congrArg AbstractState.curTime hK.1; exact e),
    (by have e := congrArg AbstractState.consumedTime hK.1; exact e), (by have e := congrArg AbstractState.idleThread hK.1; exact e),
    (by have e := congrArg AbstractState.idleSc hK.1; exact e)⟩,
    (by have e := congrArg AbstractState.readyQueues hK.1; exact e),
    (by have e := congrArg AbstractState.schedulerAction hK.1; exact e)⟩

theorem Ipc.CapsOnly.st {x y : Tcb} (h : CapsOnly x y) : y.tcbState = x.tcbState := h.1
theorem Ipc.CapsOnly.buf {x y : Tcb} (h : CapsOnly x y) : y.tcbIpcBuffer = x.tcbIpcBuffer := h.2.1
theorem Ipc.CapsOnly.ntfn {x y : Tcb} (h : CapsOnly x y) : y.tcbBoundNotification = x.tcbBoundNotification := h.2.2.2.1
theorem Ipc.CapsOnly.mcp {x y : Tcb} (h : CapsOnly x y) : y.tcbMcpriority = x.tcbMcpriority := h.2.2.2.2.1
theorem Ipc.CapsOnly.sc {x y : Tcb} (h : CapsOnly x y) : y.tcbSchedContext = x.tcbSchedContext := h.2.2.2.2.2.1
theorem Ipc.CapsOnly.yld {x y : Tcb} (h : CapsOnly x y) : y.tcbYieldTo = x.tcbYieldTo := h.2.2.2.2.2.2.1
theorem Ipc.CapsOnly.prio {x y : Tcb} (h : CapsOnly x y) : y.tcbPriority = x.tcbPriority := h.2.2.2.2.2.2.2.1

theorem KBack.of_keepCT {σ σ' : State Unit} (h : KeepCT σ σ') : KBack σ σ' := by
  intro o ko' ho
  rcases h o with e | ⟨r, cs, cs', h1, h2⟩ | ⟨x, y, h1, h2, -⟩
  · rw [e] at ho; exact ⟨ko', ho, id, id, id, id, id, id⟩
  · rw [h2] at ho; cases ho
    refine ⟨_, h1, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp
  · rw [h2] at ho; cases ho
    refine ⟨_, h1, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp

theorem SzKeep.of_keepCT {σ σ' : State Unit} (h : KeepCT σ σ') : Sched.SzKeep σ σ' := by
  intro p x n hp
  rcases h p with e | ⟨r, cs, cs', h1, h2⟩ | ⟨x', y, h1, h2, -⟩
  · exact ⟨x, e ▸ hp⟩
  · rw [h2] at hp; cases hp
  · rw [h2] at hp; cases hp

variable {σ σ' : State Unit}

/-- No reply bound to a receiver gained (`ScRecvLinks`' `KhRB`): CNodes and
TCBs' caps change. -/
theorem HStep.khrb (h : HStep σ σ') : KhRB σ σ' := by
  intro p o' hp
  rcases h.kc p with e | ⟨r, cs, cs', h1, h2⟩ | ⟨x, y, h1, h2, hc⟩
  · exact ⟨o', by rw [← e]; exact hp, ObjRB.refl o'⟩
  · obtain rfl := Option.some.inj (hp.symm.trans h2)
    exact ⟨_, h1, ObjRB.other (fun _ e => by cases e) (fun _ e => by cases e)⟩
  · obtain rfl := Option.some.inj (hp.symm.trans h2)
    exact ⟨_, h1, ObjRB.tcb (Or.inl hc.1)⟩

/-- A lookup of an object other than a CNode or a TCB is the same after. -/
theorem HStep.look (h : HStep σ σ') {p : ObjRef} {ko : KernelObject} (hko : ∀ r cs, ko ≠ .cnode r cs)
    (hkt : ∀ x, ko ≠ .tcb x) : σ'.kheap p = some ko ↔ σ.kheap p = some ko := by
  rcases h.kc p with e | ⟨r, cs, cs', h1, h2⟩ | ⟨x, y, h1, h2, -⟩
  · rw [e]
  · rw [h1, h2]; exact ⟨fun e => absurd (Option.some.inj e).symm (hko _ _), fun e => absurd (Option.some.inj e).symm (hko _ _)⟩
  · rw [h1, h2]; exact ⟨fun e => absurd (Option.some.inj e).symm (hkt _), fun e => absurd (Option.some.inj e).symm (hkt _)⟩

/-- A TCB before is one alike but for its caps after. -/
theorem HStep.tcbF (h : HStep σ σ') {p : ObjRef} {x : Tcb} (hx : σ.kheap p = some (.tcb x)) :
    ∃ y, σ'.kheap p = some (.tcb y) ∧ CapsOnly x y := by
  rcases h.kc p with e | ⟨r, cs, cs', h1, h2⟩ | ⟨x', y, h1, h2, h3⟩
  · exact ⟨x, by rw [e, hx], CapsOnly.refl x⟩
  · rw [hx] at h1; cases h1
  · rw [hx] at h1; cases h1; exact ⟨y, h2, h3⟩

/-- A TCB after is one alike but for its caps before. -/
theorem HStep.tcbB (h : HStep σ σ') {p : ObjRef} {y : Tcb} (hy : σ'.kheap p = some (.tcb y)) :
    ∃ x, σ.kheap p = some (.tcb x) ∧ CapsOnly x y := by
  rcases h.kc p with e | ⟨r, cs, cs', h1, h2⟩ | ⟨x, y', h1, h2, h3⟩
  · exact ⟨y, by rw [← e, hy], CapsOnly.refl y⟩
  · rw [hy] at h2; cases h2
  · rw [hy] at h2; cases h2; exact ⟨x, h1, h3⟩

theorem HStep.sc (h : HStep σ σ') {p : ObjRef} {y : SchedContext} {n : Nat} :
    σ'.kheap p = some (.schedContext y n) ↔ σ.kheap p = some (.schedContext y n) :=
  h.look (fun _ _ e => by cases e) (fun _ e => by cases e)
theorem HStep.ntfn (h : HStep σ σ') {p : ObjRef} {x : Notification} :
    σ'.kheap p = some (.notification x) ↔ σ.kheap p = some (.notification x) :=
  h.look (fun _ _ e => by cases e) (fun _ e => by cases e)

theorem HStep.sched_eq (h : HStep σ σ') (t : ObjRef) : Fl4Spec.schedulable t σ' = Fl4Spec.schedulable t σ := by
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

theorem Sched.NSC.cn {N C : Set U64} (hN : NSC N C σ) (h : HStep σ σ') : NSC N C σ' :=
  fun n hn x p hx hp => hN n hn x p (h.ntfn.1 hx) hp

theorem CurRun.cn (hR : CurRun σ) (h : HStep σ σ') : CurRun σ' := fun y hy => by
  rw [h.ct] at hy
  obtain ⟨x, hx, hc⟩ := h.tcbB hy
  rw [hc.st]; exact hR x hx

theorem CurRunW.cn (hR : CurRunW σ) (h : HStep σ σ') : CurRunW σ' :=
  Or.imp (fun r => r.cn h) (fun e => by rw [h.ct, h.idle]; exact e) hR

theorem CurRunM.cn (hR : CurRunM σ) (h : HStep σ σ')
    (ha : σ'.schedulerAction = .chooseNewThread ∨ σ'.schedulerAction = σ.schedulerAction) : CurRunM σ' :=
  hR.of_cn (fun r => r.cn h) ha

theorem Sched.ScLinkHyp.cn (hL : ScLinkHyp σ) (h : HStep σ σ') : ScLinkHyp σ' := by
  refine ⟨fun sc y k f hy hf => ?_, fun sc y k n hy hn => ?_, fun t x n ht hn => ?_, fun sc y k hy hs =>
    hL.scSpor sc y k (h.sc.1 hy) hs⟩
  · obtain ⟨x, hx⟩ := hL.scTcb sc y k f (h.sc.1 hy) hf
    obtain ⟨x', hx', -⟩ := h.tcbF hx; exact ⟨x', hx'⟩
  · obtain ⟨x, hx⟩ := hL.scNtfn sc y k n (h.sc.1 hy) hn; exact ⟨x, h.ntfn.2 hx⟩
  · obtain ⟨x0, hx0, hc⟩ := h.tcbB ht
    obtain ⟨x', hx'⟩ := hL.tcbNtfn t x0 n hx0 (by rw [← hc.ntfn]; exact hn); exact ⟨x', h.ntfn.2 hx'⟩

theorem Sched.BlockedScActive.cn (hB : BlockedScActive σ) (h : HStep σ σ') : BlockedScActive σ' :=
  ⟨fun p y n t x hp hyt hx hq => by
      obtain ⟨x0, hx0, hc⟩ := h.tcbB hx
      exact hB.tcb p y n t x0 (h.sc.1 hp) hyt hx0 (by rw [← hc.st]; exact hq),
    fun p y n hp hr => hB.replies p y n (h.sc.1 hp) hr⟩

theorem Sched.CurInv.cn (hI : CurInv σ) (h : HStep σ σ') : CurInv σ' := by
  obtain ⟨xt, hkt, hxs, hnb⟩ := hI.tcb
  obtain ⟨x, n, hx⟩ := hI.sc
  obtain ⟨yt, hyt, hc⟩ := h.tcbF hkt
  refine ⟨⟨yt, by rw [h.ct]; exact hyt, by rw [h.csc, hc.sc]; exact hxs, by rw [hc.st]; exact hnb⟩,
    ⟨x, n, by rw [h.csc]; exact h.sc.2 hx⟩, fun hne y m hy => ?_, by rw [h.ct, h.rel]; exact hI.notRel⟩
  rw [h.csc, h.isc] at hne; rw [h.csc] at hy
  exact hI.active hne y m (h.sc.1 hy)

theorem Sched.OffOK.cn (hO : OffOK σ) (h : HStep σ σ') : OffOK σ' := by
  intro hc y n hy ha
  rw [h.cons] at hc ⊢; rw [h.time]
  rw [h.csc] at hy; rw [h.csc, h.isc] at ha
  exact hO hc y n (h.sc.1 hy) ha

theorem Sched.ActIdle.cn (hA : ActIdle σ) (h : CnStep σ σ') : ActIdle σ' := by
  obtain ⟨hS, x, hx, h1, h2, h3⟩ := hA
  obtain ⟨y, hy, hc⟩ := h.tcbF hx
  refine ⟨fun t ht => ?_, y, by rw [h.idle]; exact hy, by rw [hc.sc, h.isc]; exact h1, by rw [hc.st]; exact h2,
    by rw [h.idle, h.rel]; exact h3⟩
  rw [h.act] at ht
  rw [h.toHStep.sched_eq]; exact hS t ht

theorem Sched.CurOwn.cn {T : Set U64} (hO : CurOwn T σ) (h : HStep σ σ') : CurOwn T σ' := by
  obtain ⟨u, hu, xt, hkt, hxs, hown, hnr⟩ := hO
  obtain ⟨yt, hyt, hc⟩ := h.tcbF hkt
  refine ⟨u, hu, yt, hyt, by rw [h.csc, hc.sc]; exact hxs, fun y n hy => ?_, fun h0 hm => ?_⟩
  · rw [h.csc] at hy; exact hown y n (h.sc.1 hy)
  · rw [h.cons] at h0; rw [h.rel] at hm; exact hnr h0 hm

theorem Sched.CurOwnW.cn {T C : Set U64} (hO : CurOwnW T C σ) (h : HStep σ σ') : CurOwnW T C σ' :=
  hO.imp (fun o => o.cn h) h.csc fun y n hy => Or.inr ⟨y, h.sc.1 hy, rfl⟩

theorem specRt_cn (h : HStep σ σ') {u scp : ObjRef} {x : Tcb} {y : SchedContext} {n : Nat}
    (hk : σ.kheap u = some (.tcb x)) (hsc : x.tcbSchedContext = some scp)
    (hky : σ.kheap scp = some (.schedContext y n)) (hne : y.scRefills ≠ []) : specRt σ' u = specRt σ u := by
  obtain ⟨x', hx', hc⟩ := h.tcbF hk
  rw [specRt_eq hx' (by rw [hc.sc]; exact hsc) (h.sc.2 hky) hne, specRt_eq hk hsc hky hne]

theorem Sched.Inv.cn (hI : Inv σ) (h : CnStep σ σ') : Inv σ' := by
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
    rw [specRt_cn h.toHStep h1 h2 h4 (hI.ne _ _ _ h4 h5), specRt_cn h.toHStep g1 g2 g4 (hI.ne _ _ _ g4 g5)]
    exact hab
  · obtain ⟨x0, hx0, hc0⟩ := h.tcbB hx
    intro x' scp y n h1 h2 h3 h4 h5
    rw [h.rel] at h5
    rw [hx] at h1; cases h1
    have hr := hI.rd u x0 hx0 (hc.congr hc0.1.symm fun _ => hc0.2.2.1.symm) x0 scp y n hx0 (by rw [← hc0.sc]; exact h2)
      (h.sc.1 h3) h4 h5
    unfold released at hr ⊢; rw [h.time]; exact hr
  · obtain ⟨x0, hx0, hc0⟩ := h.tcbB hx
    obtain ⟨y, n, hy, hyt⟩ := hI.back u x0 p hx0 (by rw [← hc0.sc]; exact hp)
    exact ⟨y, n, h.sc.2 hy, hyt⟩
  · obtain ⟨y, n, hy⟩ := hI.ntfnSc q x p (h.ntfn.1 hx) hp
    exact ⟨y, n, h.sc.2 hy⟩

theorem prioOf_cn (h : HStep σ σ') (u : ObjRef) : Sched.prioOf σ' u = Sched.prioOf σ u := by
  rcases h.kc u with e | ⟨r, cs, cs', h1, h2⟩ | ⟨x, y, h1, h2, h3⟩
  · unfold Sched.prioOf tcbsOf tcbsOfKh optMap; rw [e]
  · unfold Sched.prioOf tcbsOf tcbsOfKh optMap; rw [h1, h2]; rfl
  · rw [Sched.prioOf_eq h1, Sched.prioOf_eq h2, h3.prio]

theorem Sched.IpcSorted.cn (hS : IpcSorted σ) (h : HStep σ σ') : IpcSorted σ' :=
  ⟨fun p x hp => (hS.1 p x ((h.look (fun _ _ e => by cases e) (fun _ e => by cases e)).1 hp)).congr
      fun u _ => prioOf_cn h u,
    fun p x hp => (hS.2 p x (h.ntfn.1 hp)).congr fun u _ => prioOf_cn h u⟩

theorem CurInvW.cn (hC : σ.schedulerAction = .chooseNewThread ∨ CurInv σ) (h : CnStep σ σ') :
    σ'.schedulerAction = .chooseNewThread ∨ CurInv σ' := by
  rcases hC with e | hI
  · left; rw [h.act]; exact e
  · right; exact hI.cn h.toHStep

end Spec

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

/-- **`IpcFrKeep` of a CSpace step** (`KeepCT`) from `J`: each TCB's FL4
buffer slot kept or emptied (`IpcFrKeep.of_slot2`). -/
theorem JAtZ.slot2Fr {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {mem' : U64 → U64} {σ' : Fl4Spec.State Unit}
    (hkc : KeepCT σ σ') (hR' : StateRel Z.th mem' σ')
    (h2 : ∀ q, Z.th q = some .tcb → capAt mem' (slotOf q 2) = capAt (L.mem s) (slotOf q 2) ∨
      capV mem' (slotOf q 2) = .Null) : IpcFrKeep σ σ' := by
  refine IpcFrKeep.of_slot2 (fun p => ?_) J.xtop.rel.2.1.1 hR' (fun t x hx => ?_) h2
  · rcases hkc p with e | h | ⟨x, y, h1, h2, hc⟩
    · exact Or.inl e
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl ⟨x, y, h1, h2, hc.2.1⟩))
  · rcases hkc t with e | ⟨r, cs, cs', -, h1⟩ | ⟨x0, y, h1, h1', -⟩
    · rw [e] at hx; exact J.thOfTcb hx
    · rw [hx] at h1; cases h1
    · exact J.thOfTcb h1

end

end

end Fl4Proofs.P3
