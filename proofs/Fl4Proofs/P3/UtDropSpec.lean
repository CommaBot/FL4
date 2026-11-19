/-
P3 (DESIGN.md §9), Untyped's reset (the drop step), part 2: **the spec's
invariants across the detype** (l4v `delete_objects`: `detype` of the
untyped's region, `freeMemory` on it; handoff/utj.md "Round 8").

* `SDrop Rg σ σ'`: the objects at `Rg` removed, every other cell kept, the
  scheduler's fields kept (the machine state may change).
* `SKeep Rg σ`: no link of the spec state names an object of `Rg` (l4v
  `sym_refs` with `if_live_then_nonz_cap`: the region of a childless
  untyped holds only dead objects, which nothing live names; discharged at
  `J` from `DeadP`, UtDropJ).  Every link is stated with both ends kept: a
  dead object has no outgoing link either.
* The scheduler's spec invariants across an `SDrop` given `SKeep`:
  `SchedValid`, `Inv`, `BlockedScActive`, `ScLinkHyp`, `CurInv`, `OffOK`,
  `ActIdle`, `IpcSorted`, `CurRunM`, and at the kept sets (`KeepS`) `NSC`,
  `CurOwnW`, `ObjCover`.
-/
import Fl4Proofs.P3.UtDropSets
import Fl4Proofs.P3.XTopJointMakePoolSpec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched

noncomputable section

section Spec
open Fl4Spec

/-- **The spec's detype of a region** (module docstring). -/
structure SDrop (Rg : ObjRef → Prop) (σ σ' : State Unit) : Prop where
  kin : ∀ p, Rg p → σ'.kheap p = none
  kout : ∀ p, ¬ Rg p → σ'.kheap p = σ.kheap p
  ct : σ'.curThread = σ.curThread
  idle : σ'.idleThread = σ.idleThread
  cons : σ'.consumedTime = σ.consumedTime
  time : σ'.curTime = σ.curTime
  csc : σ'.curSc = σ.curSc
  isc : σ'.idleSc = σ.idleSc
  act : σ'.schedulerAction = σ.schedulerAction
  rq : σ'.readyQueues = σ.readyQueues
  rel : σ'.releaseQueue = σ.releaseQueue

/-- **No link names an object of the region** (module docstring). -/
structure SKeep (Rg : ObjRef → Prop) (σ : State Unit) : Prop where
  send : ∀ t x e pl, σ.kheap t = some (.tcb x) → x.tcbState = .blockedOnSend e pl → ¬ Rg t ∧ ¬ Rg e
  recv : ∀ t x e r d, σ.kheap t = some (.tcb x) → x.tcbState = .blockedOnReceive e r d →
    ¬ Rg t ∧ ¬ Rg e ∧ ∀ r', r = some r' → ¬ Rg r'
  ntfnW : ∀ t x n, σ.kheap t = some (.tcb x) → x.tcbState = .blockedOnNotification n → ¬ Rg t ∧ ¬ Rg n
  onReply : ∀ t x r, σ.kheap t = some (.tcb x) → x.tcbState = .blockedOnReply r → ¬ Rg t ∧ ¬ Rg r
  tcbSc : ∀ t x c, σ.kheap t = some (.tcb x) → x.tcbSchedContext = some c → ¬ Rg t ∧ ¬ Rg c
  tcbNtfn : ∀ t x n, σ.kheap t = some (.tcb x) → x.tcbBoundNotification = some n → ¬ Rg t ∧ ¬ Rg n
  tcbYield : ∀ t x c, σ.kheap t = some (.tcb x) → x.tcbYieldTo = some c → ¬ Rg t ∧ ¬ Rg c
  epQ : ∀ e x, σ.kheap e = some (.endpoint x) → ∀ u ∈ x.epQueue, ¬ Rg e ∧ ¬ Rg u
  ntfnQ : ∀ n x, σ.kheap n = some (.notification x) → ∀ u ∈ ntfnQueueOf x, ¬ Rg n ∧ ¬ Rg u
  ntfnB : ∀ n x t, σ.kheap n = some (.notification x) → x.ntfnBoundTcb = some t → ¬ Rg n ∧ ¬ Rg t
  ntfnSc : ∀ n x c, σ.kheap n = some (.notification x) → x.ntfnSc = some c → ¬ Rg n ∧ ¬ Rg c
  replyT : ∀ r x t, σ.kheap r = some (.reply x) → x.replyTcb = some t → ¬ Rg r ∧ ¬ Rg t
  scT : ∀ c y k t, σ.kheap c = some (.schedContext y k) → y.scTcb = some t → ¬ Rg c ∧ ¬ Rg t
  scN : ∀ c y k n, σ.kheap c = some (.schedContext y k) → y.scNtfn = some n → ¬ Rg c ∧ ¬ Rg n
  scY : ∀ c y k t, σ.kheap c = some (.schedContext y k) → y.scYieldFrom = some t → ¬ Rg c ∧ ¬ Rg t
  scR : ∀ c y k r, σ.kheap c = some (.schedContext y k) → r ∈ y.scReplies → ¬ Rg c ∧ ¬ Rg r
  rq : ∀ d p u, u ∈ σ.readyQueues d p → ¬ Rg u
  rel : ∀ u ∈ σ.releaseQueue, ¬ Rg u
  act : ∀ t, σ.schedulerAction = .switchThread t → ¬ Rg t
  idle : ¬ Rg σ.idleThread ∧ ¬ Rg σ.idleSc
  cur : ¬ Rg σ.curThread ∧ ¬ Rg σ.curSc

variable {Rg : ObjRef → Prop} {σ σ' : State Unit}

theorem SDrop.back (h : SDrop Rg σ σ') {p : ObjRef} {ko : KernelObject} (hp : σ'.kheap p = some ko) :
    ¬ Rg p ∧ σ.kheap p = some ko := by
  by_cases hr : Rg p
  · rw [h.kin p hr] at hp; cases hp
  · exact ⟨hr, by rw [← h.kout p hr]; exact hp⟩

theorem SDrop.fwd (h : SDrop Rg σ σ') {p : ObjRef} {ko : KernelObject} (hr : ¬ Rg p) (hp : σ.kheap p = some ko) :
    σ'.kheap p = some ko := by
  rw [h.kout p hr]; exact hp

theorem SDrop.szKeep (h : SDrop Rg σ σ') : Sched.SzKeep σ σ' := fun _ x _ hp => ⟨x, (h.back hp).2⟩

theorem SDrop.sched_eq (h : SDrop Rg σ σ') (K : SKeep Rg σ) {t : ObjRef} (ht : schedulable t σ = true) :
    schedulable t σ' = true := by
  obtain ⟨x, scp, y, n, h1, h2, h3, h4, h5, h6⟩ := schedulable_inv ht
  obtain ⟨k1, k2⟩ := K.tcbSc t x scp h1 h2
  exact schedulable_of (h.fwd k1 h1) h2 h3 (h.fwd k2 h4) h5 (by rw [h.rel]; exact h6)

theorem SDrop.qrdy (h : SDrop Rg σ σ') {u : ObjRef} (hu : ¬ Rg u) (hq : QRdy σ u) : QRdy σ' u := by
  obtain ⟨x, hx, hr⟩ := hq
  refine ⟨x, h.fwd hu hx, fun hn c hc y k hy ha => ?_⟩
  rw [h.time]; exact hr hn c hc y k (h.back hy).2 ha

/-- **`SchedValid` across the detype.** -/
theorem Sched.SchedValid.drop (hV : SchedValid σ) (K : SKeep Rg σ) (h : SDrop Rg σ σ') : SchedValid σ' := by
  refine ⟨fun e x he => ?_, fun n x hn => ?_, fun t x ep ro d ht hs => ?_, fun t x ep pl ht hs => ?_,
    fun t x n ht hs => ?_, fun t x ep r d ht hs => ?_, fun t x r ht hs => ?_, fun r xr t hr ht => ?_,
    fun sc y k r hy hr => ?_, fun sc y k f hy hf => ?_, fun sc y k n hy hn => ?_, fun sc y k t hy ht => ?_,
    fun t x p ht hp => ?_, fun t x n ht hn => ?_, fun n xn t hn ht => ?_,
    fun sc y k hy hs => hV.scSpor sc y k (h.back hy).2 hs⟩
  · have hb := (h.back he).2
    obtain ⟨h1, h2⟩ := hV.epQ e x hb
    exact ⟨h1, fun u hu => h.qrdy (K.epQ e x hb u hu).2 (h2 u hu)⟩
  · have hb := (h.back hn).2
    obtain ⟨h1, h2⟩ := hV.ntfnQ n x hb
    refine ⟨h1, fun u hu => ?_⟩
    obtain ⟨xu, hxu, hst⟩ := h2 u hu
    exact ⟨xu, h.fwd (K.ntfnQ n x hb u hu).2 hxu, hst⟩
  · have hb := (h.back ht).2
    obtain ⟨xe, hxe, hm⟩ := hV.recvQ t x ep ro d hb hs
    exact ⟨xe, h.fwd (K.recv t x ep ro d hb hs).2.1 hxe, hm⟩
  · have hb := (h.back ht).2
    obtain ⟨xe, hxe, hm⟩ := hV.sendQ t x ep pl hb hs
    exact ⟨xe, h.fwd (K.send t x ep pl hb hs).2 hxe, hm⟩
  · have hb := (h.back ht).2
    obtain ⟨xn, hxn, hm⟩ := hV.ntfnW t x n hb hs
    exact ⟨xn, h.fwd (K.ntfnW t x n hb hs).2 hxn, hm⟩
  · have hb := (h.back ht).2
    obtain ⟨xr, hxr, hm⟩ := hV.recvReply t x ep r d hb hs
    exact ⟨xr, h.fwd ((K.recv t x ep _ d hb hs).2.2 r rfl) hxr, hm⟩
  · have hb := (h.back ht).2
    obtain ⟨xr, hxr, hm⟩ := hV.onReply t x r hb hs
    exact ⟨xr, h.fwd (K.onReply t x r hb hs).2 hxr, hm⟩
  · have hb := (h.back hr).2
    obtain ⟨x, hx, hm⟩ := hV.replyTcb r xr t hb ht
    exact ⟨x, h.fwd (K.replyT r xr t hb ht).2 hx, hm⟩
  · have hb := (h.back hy).2
    obtain ⟨xr, hxr, hm⟩ := hV.replies sc y k r hb hr
    exact ⟨xr, h.fwd (K.scR sc y k r hb hr).2 hxr, hm⟩
  · have hb := (h.back hy).2
    obtain ⟨x, hx⟩ := hV.scTcb sc y k f hb hf
    exact ⟨x, h.fwd (K.scT sc y k f hb hf).2 hx⟩
  · have hb := (h.back hy).2
    obtain ⟨x, hx⟩ := hV.scNtfn sc y k n hb hn
    exact ⟨x, h.fwd (K.scN sc y k n hb hn).2 hx⟩
  · have hb := (h.back hy).2
    obtain ⟨x, hx, hm⟩ := hV.scYieldFrom sc y k t hb ht
    exact ⟨x, h.fwd (K.scY sc y k t hb ht).2 hx, hm⟩
  · have hb := (h.back ht).2
    obtain ⟨y, k, hy⟩ := hV.tcbYieldTo t x p hb hp
    exact ⟨y, k, h.fwd (K.tcbYield t x p hb hp).2 hy⟩
  · have hb := (h.back ht).2
    obtain ⟨x, hx⟩ := hV.tcbNtfn t x n hb hn
    exact ⟨x, h.fwd (K.tcbNtfn t _ n hb hn).2 hx⟩
  · have hb := (h.back hn).2
    obtain ⟨x, hx⟩ := hV.ntfnTcb n xn t hb ht
    exact ⟨x, h.fwd (K.ntfnB n xn t hb ht).2 hx⟩

theorem Sched.ScLinkHyp.drop (hL : ScLinkHyp σ) (K : SKeep Rg σ) (h : SDrop Rg σ σ') : ScLinkHyp σ' := by
  refine ⟨fun sc y k f hy hf => ?_, fun sc y k n hy hn => ?_, fun t x n ht hn => ?_,
    fun sc y k hy hs => hL.scSpor sc y k (h.back hy).2 hs⟩
  · have hb := (h.back hy).2
    obtain ⟨x, hx⟩ := hL.scTcb sc y k f hb hf
    exact ⟨x, h.fwd (K.scT sc y k f hb hf).2 hx⟩
  · have hb := (h.back hy).2
    obtain ⟨x, hx⟩ := hL.scNtfn sc y k n hb hn
    exact ⟨x, h.fwd (K.scN sc y k n hb hn).2 hx⟩
  · have hb := (h.back ht).2
    obtain ⟨x, hx⟩ := hL.tcbNtfn t x n hb hn
    exact ⟨x, h.fwd (K.tcbNtfn t _ n hb hn).2 hx⟩

theorem Sched.BlockedScActive.drop (hB : BlockedScActive σ) (h : SDrop Rg σ σ') : BlockedScActive σ' :=
  ⟨fun p y n t x hp hyt hx hq => hB.tcb p y n t x (h.back hp).2 hyt (h.back hx).2 hq,
    fun p y n hp hr => hB.replies p y n (h.back hp).2 hr⟩

theorem CurRun.drop (hR : CurRun σ) (h : SDrop Rg σ σ') : CurRun σ' := fun y hy => by
  rw [h.ct] at hy; exact hR y (h.back hy).2

theorem CurRunM.drop (hR : CurRunM σ) (h : SDrop Rg σ σ') : CurRunM σ' :=
  Or.imp (fun e' => by rw [h.act]; exact e') (fun r => Or.imp (fun r => r.drop h)
    (fun e => by rw [h.ct, h.idle]; exact e) r) hR

theorem Sched.CurInv.drop (hI : CurInv σ) (K : SKeep Rg σ) (h : SDrop Rg σ σ') : CurInv σ' := by
  obtain ⟨xt, hkt, hxs, hnb⟩ := hI.tcb
  obtain ⟨x, n, hx⟩ := hI.sc
  refine ⟨⟨xt, by rw [h.ct]; exact h.fwd K.cur.1 hkt, by rw [h.csc]; exact hxs, hnb⟩,
    ⟨x, n, by rw [h.csc]; exact h.fwd K.cur.2 hx⟩, fun hne y m hy => ?_, by rw [h.ct, h.rel]; exact hI.notRel⟩
  rw [h.csc, h.isc] at hne; rw [h.csc] at hy
  exact hI.active hne y m (h.back hy).2

theorem CurInvW.drop (hC : σ.schedulerAction = .chooseNewThread ∨ CurInv σ) (K : SKeep Rg σ) (h : SDrop Rg σ σ') :
    σ'.schedulerAction = .chooseNewThread ∨ CurInv σ' :=
  hC.imp (fun e => by rw [h.act]; exact e) (fun hI => hI.drop K h)

theorem Sched.OffOK.drop (hO : OffOK σ) (h : SDrop Rg σ σ') : OffOK σ' := by
  intro hc y n hy ha
  rw [h.cons] at hc ⊢; rw [h.time]
  rw [h.csc] at hy; rw [h.csc, h.isc] at ha
  exact hO hc y n (h.back hy).2 ha

theorem Sched.ActIdle.drop (hA : ActIdle σ) (K : SKeep Rg σ) (h : SDrop Rg σ σ') : ActIdle σ' := by
  obtain ⟨hS, x, hx, h1, h2, h3⟩ := hA
  refine ⟨fun t ht => ?_, x, by rw [h.idle]; exact h.fwd K.idle.1 hx, by rw [h.isc]; exact h1, h2,
    by rw [h.idle, h.rel]; exact h3⟩
  rw [h.act] at ht
  exact h.sched_eq K (hS t ht)

theorem specRt_drop (h : SDrop Rg σ σ') (K : SKeep Rg σ) {u scp : ObjRef} {x : Tcb} {y : SchedContext} {n : Nat}
    (hk : σ.kheap u = some (.tcb x)) (hsc : x.tcbSchedContext = some scp)
    (hky : σ.kheap scp = some (.schedContext y n)) (hne : y.scRefills ≠ []) : specRt σ' u = specRt σ u := by
  obtain ⟨k1, k2⟩ := K.tcbSc u x scp hk hsc
  rw [specRt_eq (h.fwd k1 hk) hsc (h.fwd k2 hky) hne, specRt_eq hk hsc hky hne]

/-- **`Inv` across the detype.** -/
theorem Sched.Inv.drop (hI : Inv σ) (K : SKeep Rg σ) (h : SDrop Rg σ σ') : Inv σ' := by
  refine ⟨fun d p u hu => ?_, fun u hu => ?_, ?_, fun u x hx hc => ?_, fun p y n hy => hI.refills p y n (h.back hy).2,
    fun u x p hx hp => ?_, fun q x p hx hp => ?_, fun p y n hy => hI.ne p y n (h.back hy).2,
    fun p y n hy => hI.rr p y n (h.back hy).2⟩
  · rw [h.rq] at hu
    obtain ⟨x, scp, y, n, h1, h2, h3, h4, h5⟩ := hI.rq d p u hu
    obtain ⟨k1, k2⟩ := K.tcbSc u x scp h1 h2
    exact ⟨x, scp, y, n, h.fwd k1 h1, h2, h3, h.fwd k2 h4, h5⟩
  · rw [h.rel] at hu
    obtain ⟨x, scp, y, n, h1, h2, h3, h4, h5⟩ := hI.rel u hu
    obtain ⟨k1, k2⟩ := K.tcbSc u x scp h1 h2
    exact ⟨x, scp, y, n, h.fwd k1 h1, h2, h3, h.fwd k2 h4, h5⟩
  · rw [h.rel]
    refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab => ?_) hI.sorted
    obtain ⟨xa, pa, ya, na, h1, h2, -, h4, h5⟩ := hI.rel a ha
    obtain ⟨xb, pb, yb, nb, g1, g2, -, g4, g5⟩ := hI.rel b hb
    rw [specRt_drop h K h1 h2 h4 (hI.ne _ _ _ h4 h5), specRt_drop h K g1 g2 g4 (hI.ne _ _ _ g4 g5)]
    exact hab
  · have hx0 := (h.back hx).2
    intro x' scp y n h1 h2 h3 h4 h5
    rw [h.rel] at h5
    rw [hx] at h1; cases h1
    have hr := hI.rd u x hx0 hc x scp y n hx0 h2 (h.back h3).2 h4 h5
    unfold released at hr ⊢; rw [h.time]; exact hr
  · have hx0 := (h.back hx).2
    obtain ⟨y, n, hy, hyt⟩ := hI.back u x p hx0 hp
    exact ⟨y, n, h.fwd (K.tcbSc u x p hx0 hp).2 hy, hyt⟩
  · have hx0 := (h.back hx).2
    obtain ⟨y, n, hy⟩ := hI.ntfnSc q x p hx0 hp
    exact ⟨y, n, h.fwd (K.ntfnSc q x p hx0 hp).2 hy⟩

theorem prioOf_drop (h : SDrop Rg σ σ') {u : ObjRef} (hu : ¬ Rg u) : Sched.prioOf σ' u = Sched.prioOf σ u := by
  unfold Sched.prioOf tcbsOf tcbsOfKh optMap; rw [h.kout u hu]

theorem Sched.IpcSorted.drop (hS : IpcSorted σ) (K : SKeep Rg σ) (h : SDrop Rg σ σ') : IpcSorted σ' := by
  refine ⟨fun p x hp => ?_, fun p x hp => ?_⟩
  · have hb := (h.back hp).2
    exact (hS.1 p x hb).congr fun u hu => prioOf_drop h (K.epQ p x hb u hu).2
  · have hb := (h.back hp).2
    exact (hS.2 p x hb).congr fun u hu => prioOf_drop h (K.ntfnQ p x hb u hu).2

/-! ### At the kept sets -/

/-- The kept-set predicate of a region: off it. -/
abbrev KOff (Rg : ObjRef → Prop) : U64 → Prop := fun q => ¬ Rg q.bv

theorem Sched.NSC.drop {N C : Set U64} (hN : NSC N C σ) (K : SKeep Rg σ) (h : SDrop Rg σ σ') :
    NSC (KeepS (KOff Rg) N) (KeepS (KOff Rg) C) σ' := by
  intro n hn x p hx hp
  have hb := (h.back hx).2
  obtain ⟨sc, hsc, e⟩ := hN n hn.1 x p hb hp
  refine ⟨sc, ⟨hsc, ?_⟩, e⟩
  show ¬ Rg sc.bv
  rw [e]; exact (K.ntfnSc _ x p hb hp).2

theorem Sched.CurOwn.drop {T : Set U64} (hO : CurOwn T σ) (K : SKeep Rg σ) (h : SDrop Rg σ σ') :
    CurOwn (KeepS (KOff Rg) T) σ' := by
  obtain ⟨u, hu, xt, hkt, hxs, hown, hnr⟩ := hO
  have k1 := (K.tcbSc _ xt _ hkt hxs).1
  refine ⟨u, ⟨hu, k1⟩, xt, h.fwd k1 hkt, by rw [h.csc]; exact hxs, fun y n hy => ?_, fun h0 hm => ?_⟩
  · rw [h.csc] at hy; exact hown y n (h.back hy).2
  · rw [h.cons] at h0; rw [h.rel] at hm; exact hnr h0 hm

theorem Sched.CurOwnW.drop {T C : Set U64} (hO : CurOwnW T C σ) (K : SKeep Rg σ) (h : SDrop Rg σ σ') :
    CurOwnW (KeepS (KOff Rg) T) (KeepS (KOff Rg) C) σ' := by
  rcases hO with hO | ⟨⟨sc, hsc, e⟩, hn⟩
  · exact Or.inl (hO.drop K h)
  · refine Or.inr ⟨⟨sc, ⟨hsc, ?_⟩, by rw [h.csc]; exact e⟩, fun y n hy => ?_⟩
    · show ¬ Rg sc.bv
      rw [e]; exact K.cur.2
    · rw [h.csc] at hy; exact hn y n (h.back hy).2

theorem Sched.ObjCover.drop {N T E R C : Set U64} (hO : ObjCover N T E R C σ) (h : SDrop Rg σ σ') :
    ObjCover (KeepS (KOff Rg) N) (KeepS (KOff Rg) T) (KeepS (KOff Rg) E) (KeepS (KOff Rg) R)
      (KeepS (KOff Rg) C) σ' := by
  refine ⟨fun o x hx => ?_, fun o x hx => ?_, fun o x hx => ?_, fun o x hx => ?_, fun o y k hx => ?_⟩
  · obtain ⟨k0, hb⟩ := h.back hx
    obtain ⟨t, ht, e⟩ := hO.tcb o x hb
    exact ⟨t, ⟨ht, by show ¬ Rg t.bv; rw [e]; exact k0⟩, e⟩
  · obtain ⟨k0, hb⟩ := h.back hx
    obtain ⟨t, ht, e⟩ := hO.ntfn o x hb
    exact ⟨t, ⟨ht, by show ¬ Rg t.bv; rw [e]; exact k0⟩, e⟩
  · obtain ⟨k0, hb⟩ := h.back hx
    obtain ⟨t, ht, e⟩ := hO.ep o x hb
    exact ⟨t, ⟨ht, by show ¬ Rg t.bv; rw [e]; exact k0⟩, e⟩
  · obtain ⟨k0, hb⟩ := h.back hx
    obtain ⟨t, ht, e⟩ := hO.reply o x hb
    exact ⟨t, ⟨ht, by show ¬ Rg t.bv; rw [e]; exact k0⟩, e⟩
  · obtain ⟨k0, hb⟩ := h.back hx
    obtain ⟨t, ht, e⟩ := hO.sc o y k hb
    exact ⟨t, ⟨ht, by show ¬ Rg t.bv; rw [e]; exact k0⟩, e⟩

end Spec

end

end Fl4Proofs.P3
