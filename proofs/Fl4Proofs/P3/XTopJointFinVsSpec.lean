/-
P3 (DESIGN.md §9), VSpace: **the spec's arch finalisation changes only arch
objects** (spec side only), toward `JAtZ` after a native VSpace cap's
finalisation (XTopJointFinVs).

* `archF`: the state's fields but the arch objects' contents, the ASID table,
  the current CR3 and the machine state (an arch object kept as one of the
  same arch type, `aType`). `fa_archFinaliseCap`: every outcome of
  `arch_finalise_cap` keeps `archF` (VsDom's `FK`, the monad's combinators,
  with the leaves `set_object` of an arch object over one of the same type,
  `do_machine_op` and `get_cap`).
* `ArFr σ σ'`: the frame `archF` gives: every object kept or an arch object
  replaced by one of the same arch type, the scheduler's and the CSpace's
  fields kept.
* The scheduler's spec invariants across an `ArFr` step (as SpecKeepC's for
  a CNode-only step: they read no arch object): `NSC`, `Inv`, `CurInv`,
  `OffOK`, `ActIdle`, `BlockedScActive`, `CurOwnW`, `IpcSorted`, `CurRunM`;
  the global PML4 kept a PML4 (`HasPm`).
-/
import Fl4Proofs.P3.SpecKeepC
import Fl4Proofs.P3.XTopFinVs
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched Fl4Proofs.P3.Ipc

noncomputable section

section Spec
open Fl4Spec

/-- An arch object forgotten. -/
def eraseA : Option KernelObject → Option KernelObject
  | some (.archObj _) => none
  | o => o

/-- **The fields an arch finalisation keeps** (module docstring). -/
def archF (σ : State Unit) :=
  ((fun p => eraseA (σ.kheap p)), (fun p => (σ.kheap p).map aType), σ.cdt, σ.isOriginalCap, σ.curThread,
    σ.idleThread, σ.consumedTime, σ.curTime, σ.curSc, σ.reprogramTimer, σ.schedulerAction, σ.domainTime,
    σ.readyQueues, σ.releaseQueue, σ.archState.x64GlobalPml4, σ.curDomain, σ.idleSc)

theorem archF_eq {σ σ' : State Unit} (h1 : ∀ q, eraseA (σ'.kheap q) = eraseA (σ.kheap q))
    (h2 : ∀ q, (σ'.kheap q).map aType = (σ.kheap q).map aType) (hc : σ'.cdt = σ.cdt)
    (ho : σ'.isOriginalCap = σ.isOriginalCap) (h3 : σ'.curThread = σ.curThread) (h4 : σ'.idleThread = σ.idleThread)
    (h5 : σ'.consumedTime = σ.consumedTime) (h6 : σ'.curTime = σ.curTime) (h7 : σ'.curSc = σ.curSc)
    (h8 : σ'.reprogramTimer = σ.reprogramTimer) (h9 : σ'.schedulerAction = σ.schedulerAction)
    (h10 : σ'.domainTime = σ.domainTime) (h11 : σ'.readyQueues = σ.readyQueues)
    (h12 : σ'.releaseQueue = σ.releaseQueue) (h13 : σ'.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4)
    (h14 : σ'.curDomain = σ.curDomain) (h15 : σ'.idleSc = σ.idleSc := by first | rfl | assumption) :
    archF σ' = archF σ := by
  unfold archF
  rw [funext h1, funext h2, hc, ho, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]

theorem archF_upd {σ : State Unit} {p : ObjRef} {a0 a : ArchKernelObj} (hk : σ.kheap p = some (.archObj a0))
    (ht : aaType a0 = aaType a) :
    archF { σ with kheap := Function.update σ.kheap p (some (.archObj a)) } = archF σ := by
  refine archF_eq (fun q => ?_) (fun q => ?_) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  · show eraseA (Function.update σ.kheap p (some (.archObj a)) q) = eraseA (σ.kheap q)
    by_cases e : q = p
    · subst e; rw [Function.update_self, hk]; rfl
    · rw [Function.update_of_ne e]
  · show (Function.update σ.kheap p (some (.archObj a)) q).map aType = (σ.kheap q).map aType
    by_cases e : q = p
    · subst e; rw [Function.update_self, hk]; simp [aType, ht]
    · rw [Function.update_of_ne e]

/-- `set_object` of an arch object (over one of the same type). -/
theorem fa_setObject (p : ObjRef) (a : ArchKernelObj) : Vs.FK archF (setObject (Z := Unit) p (.archObj a)) := by
  intro σ x hx
  obtain ⟨k, hk, hty, e⟩ := MaxK.mk_setObject_mem hx
  rw [e]
  cases k with
  | archObj a0 => exact archF_upd hk (by simpa [aType] using hty)
  | cnode r cs => simp only [aType] at hty; split at hty <;> cases hty
  | schedContext y n => simp only [aType] at hty; split at hty <;> cases hty
  | _ => simp [aType] at hty

theorem fa_doMachineOp {α : Type} (mop : NonDet MachineState α) : Vs.FK archF (doMachineOp (Z := Unit) mop) := by
  unfold doMachineOp
  refine Vs.dk_bind (Vs.dk_gets _) (fun _ => Vs.dk_bind (Vs.dk_selectF _) (fun x => ?_))
  obtain ⟨r, ms⟩ := x
  exact Vs.dk_bind (Vs.dk_modify (fun σ => rfl)) (fun _ => Vs.dk_pure _)

theorem fk_getCapG {β : Type} (f : State Unit → β) (sl : CslotPtr) : Vs.FK f (getCap (Z := Unit) sl) := by
  obtain ⟨o, r⟩ := sl; unfold getCap; dk_auto0

set_option maxHeartbeats 8000000 in
/-- **Every outcome of `arch_finalise_cap` keeps `archF`.** -/
theorem fa_archFinaliseCap (c : ArchCap) (x : Bool) : Vs.FK archF (archFinaliseCap (Z := Unit) c x) := by
  unfold archFinaliseCap
  repeat' (first | exact fa_setObject _ _ | exact fk_getCapG _ _ | exact fa_doMachineOp _ | dk_step0 | fk_unf | sched_unf | vs_unf)

theorem fa_finaliseCap_arch (ac : ArchCap) (b : Bool) :
    Vs.FK archF (finaliseCap (Z := Unit) (.archObjectCap ac) b) :=
  fa_archFinaliseCap ac b

/-- **The frame of an arch finalisation** (module docstring). -/
structure ArFr (σ σ' : State Unit) : Prop where
  kh : ∀ p, σ'.kheap p = σ.kheap p ∨ ∃ a a', σ.kheap p = some (.archObj a) ∧ σ'.kheap p = some (.archObj a') ∧
    aaType a' = aaType a
  cdt : σ'.cdt = σ.cdt
  orig : σ'.isOriginalCap = σ.isOriginalCap
  ct : σ'.curThread = σ.curThread
  idle : σ'.idleThread = σ.idleThread
  cons : σ'.consumedTime = σ.consumedTime
  time : σ'.curTime = σ.curTime
  csc : σ'.curSc = σ.curSc
  isc : σ'.idleSc = σ.idleSc
  repr : σ'.reprogramTimer = σ.reprogramTimer
  act : σ'.schedulerAction = σ.schedulerAction
  dt : σ'.domainTime = σ.domainTime
  rq : σ'.readyQueues = σ.readyQueues
  rel : σ'.releaseQueue = σ.releaseQueue
  gpml4 : σ'.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4
  cdom : σ'.curDomain = σ.curDomain

theorem eraseA_cases (o : Option KernelObject) :
    (eraseA o = o ∧ ∀ a, o ≠ some (.archObj a)) ∨ ∃ a, o = some (.archObj a) := by
  rcases o with _ | o
  · exact Or.inl ⟨rfl, fun a h => by cases h⟩
  · cases o with
    | archObj a => exact Or.inr ⟨a, rfl⟩
    | _ => exact Or.inl ⟨rfl, fun a h => by cases h⟩

theorem ArFr.of_eq {σ σ' : State Unit} (h : archF σ' = archF σ) : ArFr σ σ' := by
  simp only [archF, Prod.mk.injEq] at h
  obtain ⟨h1, h2, hc, ho, hct, hid, hcons, htime, hcsc, hrep, hact, hdt, hrq, hrel, hgp, hcd, hisc⟩ := h
  refine ⟨fun p => ?_, hc, ho, hct, hid, hcons, htime, hcsc, hisc, hrep, hact, hdt, hrq, hrel, hgp, hcd⟩
  have e1 : eraseA (σ'.kheap p) = eraseA (σ.kheap p) := congrFun h1 p
  have e2 : (σ'.kheap p).map aType = (σ.kheap p).map aType := congrFun h2 p
  rcases eraseA_cases (σ.kheap p) with ⟨f1, -⟩ | ⟨a, g1⟩ <;>
    rcases eraseA_cases (σ'.kheap p) with ⟨f2, n2⟩ | ⟨a', g2⟩
  · left; rw [← f1, ← f2]; exact e1
  · exfalso
    rw [g2, f1] at e1
    have e0 : σ.kheap p = none := e1.symm
    rw [g2, e0] at e2; cases e2
  · exfalso
    rw [g1, f2] at e1
    have e0 : σ'.kheap p = none := e1
    rw [g1, e0] at e2; cases e2
  · right
    refine ⟨a, a', g1, g2, ?_⟩
    rw [g1, g2] at e2
    simpa [aType] using e2

/-- `ArFr` of an outcome of a VSpace cap's spec finalisation. -/
theorem ArFr.of_fin {ac : ArchCap} {b : Bool} {σ σ' : State Unit} {x : Cap × Cap}
    (hm : (x, σ') ∈ (finaliseCap (Z := Unit) (.archObjectCap ac) b σ).1) : ArFr σ σ' :=
  ArFr.of_eq (fa_finaliseCap_arch ac b σ (x, σ') hm)

variable {σ σ' : State Unit}

/-- No reply bound to a receiver gained (`ScRecvLinks`' `KhRB`): only arch
objects change. -/
theorem ArFr.khrb (h : ArFr σ σ') : KhRB σ σ' := by
  intro p o' hp
  rcases h.kh p with e | ⟨a, a', h1, h2, -⟩
  · exact ⟨o', by rw [← e]; exact hp, ObjRB.refl o'⟩
  · obtain rfl := Option.some.inj (hp.symm.trans h2)
    exact ⟨_, h1, ObjRB.other (fun _ e => by cases e) (fun _ e => by cases e)⟩

/-- A lookup of an object other than an arch object is the same after. -/
theorem ArFr.look (h : ArFr σ σ') {p : ObjRef} {ko : KernelObject} (hk : ∀ a, ko ≠ .archObj a) :
    σ'.kheap p = some ko ↔ σ.kheap p = some ko := by
  rcases h.kh p with e | ⟨a, a', h1, h2, -⟩
  · rw [e]
  · rw [h1, h2]
    exact ⟨fun e => absurd (Option.some.inj e).symm (hk _), fun e => absurd (Option.some.inj e).symm (hk _)⟩

theorem ArFr.tcbF (h : ArFr σ σ') {p : ObjRef} {x : Tcb} (hx : σ.kheap p = some (.tcb x)) :
    ∃ y, σ'.kheap p = some (.tcb y) ∧ CapsOnly x y :=
  ⟨x, (h.look (fun _ e => by cases e)).2 hx, CapsOnly.refl x⟩

theorem ArFr.tcbB (h : ArFr σ σ') {p : ObjRef} {y : Tcb} (hy : σ'.kheap p = some (.tcb y)) :
    ∃ x, σ.kheap p = some (.tcb x) ∧ CapsOnly x y :=
  ⟨y, (h.look (fun _ e => by cases e)).1 hy, CapsOnly.refl y⟩

theorem ArFr.sc (h : ArFr σ σ') {p : ObjRef} {y : SchedContext} {n : Nat} :
    σ'.kheap p = some (.schedContext y n) ↔ σ.kheap p = some (.schedContext y n) :=
  h.look (fun _ e => by cases e)
theorem ArFr.ntfn (h : ArFr σ σ') {p : ObjRef} {x : Notification} :
    σ'.kheap p = some (.notification x) ↔ σ.kheap p = some (.notification x) :=
  h.look (fun _ e => by cases e)

theorem ArFr.kback (h : ArFr σ σ') : KBack σ σ' := by
  intro o ko' ho
  rcases h.kh o with e | ⟨a, a', h1, h2, -⟩
  · rw [e] at ho; exact ⟨ko', ho, id, id, id, id, id, id⟩
  · rw [h2] at ho; cases ho
    refine ⟨_, h1, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp

theorem ArFr.ksz (h : ArFr σ σ') : KSz σ σ' := by
  intro o ko' ho
  rcases h.kh o with e | ⟨a, a', h1, h2, ht⟩
  · exact ⟨ko', by rw [← e]; exact ho, rfl⟩
  · rw [h2] at ho; cases ho
    exact ⟨_, h1, by simp [aType, ht]⟩

theorem ArFr.ksub (h : ArFr σ σ') : KSub σ σ' := by
  intro o
  refine ⟨fun r cs ho hw => ⟨cs, (h.look (fun _ e => by cases e)).1 ho, hw⟩,
    fun t ho => ⟨t, (h.look (fun _ e => by cases e)).1 ho⟩, fun h0 => ?_⟩
  rcases h.kh o with e | ⟨a, a', h1, -, -⟩
  · rw [e, h0]
  · rw [h0] at h1; cases h1

theorem ArFr.szKeep (h : ArFr σ σ') : Sched.SzKeep σ σ' := fun _ x _ hp => ⟨x, h.sc.1 hp⟩

theorem ArFr.hasPm (h : ArFr σ σ') {g : ObjRef} (hp : HasPm σ g) : HasPm σ' g := by
  obtain ⟨pt, hpt⟩ := hp
  rcases h.kh g with e | ⟨a, a', h1, h2, ht⟩
  · exact ⟨pt, by rw [e]; exact hpt⟩
  · rw [hpt] at h1
    cases h1
    cases a' with
    | pageMapL4 f => exact ⟨f, h2⟩
    | dataPage d sz => by_cases hd : d <;> simp [aaType, hd] at ht
    | _ => simp [aaType] at ht

theorem ArFr.sched_eq (h : ArFr σ σ') (t : ObjRef) : Fl4Spec.schedulable t σ' = Fl4Spec.schedulable t σ := by
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

theorem Sched.NSC.ar {N C : Set U64} (hN : NSC N C σ) (h : ArFr σ σ') : NSC N C σ' :=
  fun n hn x p hx hp => hN n hn x p (h.ntfn.1 hx) hp

theorem CurRun.ar (hR : CurRun σ) (h : ArFr σ σ') : CurRun σ' := fun y hy => by
  rw [h.ct] at hy
  obtain ⟨x, hx, hc⟩ := h.tcbB hy
  rw [hc.st]; exact hR x hx

theorem CurRunW.ar (hR : CurRunW σ) (h : ArFr σ σ') : CurRunW σ' :=
  Or.imp (fun r => r.ar h) (fun e => by rw [h.ct, h.idle]; exact e) hR

theorem CurRunM.ar (hR : CurRunM σ) (h : ArFr σ σ') : CurRunM σ' :=
  Or.imp (fun e' => by rw [h.act]; exact e') (fun r => r.ar h) hR

theorem Sched.BlockedScActive.ar (hB : BlockedScActive σ) (h : ArFr σ σ') : BlockedScActive σ' :=
  ⟨fun p y n t x hp hyt hx hq => by
      obtain ⟨x0, hx0, hc⟩ := h.tcbB hx
      exact hB.tcb p y n t x0 (h.sc.1 hp) hyt hx0 (by rw [← hc.st]; exact hq),
    fun p y n hp hr => hB.replies p y n (h.sc.1 hp) hr⟩

theorem Sched.CurInv.ar (hI : CurInv σ) (h : ArFr σ σ') : CurInv σ' := by
  obtain ⟨xt, hkt, hxs, hnb⟩ := hI.tcb
  obtain ⟨x, n, hx⟩ := hI.sc
  obtain ⟨yt, hyt, hc⟩ := h.tcbF hkt
  refine ⟨⟨yt, by rw [h.ct]; exact hyt, by rw [h.csc, hc.sc]; exact hxs, by rw [hc.st]; exact hnb⟩,
    ⟨x, n, by rw [h.csc]; exact h.sc.2 hx⟩, fun hne y m hy => ?_, by rw [h.ct, h.rel]; exact hI.notRel⟩
  rw [h.csc, h.isc] at hne; rw [h.csc] at hy
  exact hI.active hne y m (h.sc.1 hy)

theorem Sched.OffOK.ar (hO : OffOK σ) (h : ArFr σ σ') : OffOK σ' := by
  intro hc y n hy ha
  rw [h.cons] at hc ⊢; rw [h.time]
  rw [h.csc] at hy; rw [h.csc, h.isc] at ha
  exact hO hc y n (h.sc.1 hy) ha

theorem Sched.ActIdle.ar (hA : ActIdle σ) (h : ArFr σ σ') : ActIdle σ' := by
  obtain ⟨hS, x, hx, h1, h2, h3⟩ := hA
  obtain ⟨y, hy, hc⟩ := h.tcbF hx
  refine ⟨fun t ht => ?_, y, by rw [h.idle]; exact hy, by rw [hc.sc, h.isc]; exact h1, by rw [hc.st]; exact h2,
    by rw [h.idle, h.rel]; exact h3⟩
  rw [h.act] at ht
  rw [h.sched_eq]; exact hS t ht

theorem Sched.CurOwn.ar {T : Set U64} (hO : CurOwn T σ) (h : ArFr σ σ') : CurOwn T σ' := by
  obtain ⟨u, hu, xt, hkt, hxs, hown, hnr⟩ := hO
  obtain ⟨yt, hyt, hc⟩ := h.tcbF hkt
  refine ⟨u, hu, yt, hyt, by rw [h.csc, hc.sc]; exact hxs, fun y n hy => ?_, fun h0 hm => ?_⟩
  · rw [h.csc] at hy; exact hown y n (h.sc.1 hy)
  · rw [h.cons] at h0; rw [h.rel] at hm; exact hnr h0 hm

theorem Sched.CurOwnW.ar {T C : Set U64} (hO : CurOwnW T C σ) (h : ArFr σ σ') : CurOwnW T C σ' :=
  hO.imp (fun o => o.ar h) h.csc fun y n hy => Or.inr ⟨y, h.sc.1 hy, rfl⟩

theorem specRt_ar (h : ArFr σ σ') {u scp : ObjRef} {x : Tcb} {y : SchedContext} {n : Nat}
    (hk : σ.kheap u = some (.tcb x)) (hsc : x.tcbSchedContext = some scp)
    (hky : σ.kheap scp = some (.schedContext y n)) (hne : y.scRefills ≠ []) : specRt σ' u = specRt σ u := by
  obtain ⟨x', hx', hc⟩ := h.tcbF hk
  rw [specRt_eq hx' (by rw [hc.sc]; exact hsc) (h.sc.2 hky) hne, specRt_eq hk hsc hky hne]

theorem Sched.Inv.ar (hI : Inv σ) (h : ArFr σ σ') : Inv σ' := by
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
    rw [specRt_ar h h1 h2 h4 (hI.ne _ _ _ h4 h5), specRt_ar h g1 g2 g4 (hI.ne _ _ _ g4 g5)]
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

theorem prioOf_ar (h : ArFr σ σ') (u : ObjRef) : Sched.prioOf σ' u = Sched.prioOf σ u := by
  rcases h.kh u with e | ⟨a, a', h1, h2, -⟩
  · unfold Sched.prioOf tcbsOf tcbsOfKh optMap; rw [e]
  · unfold Sched.prioOf tcbsOf tcbsOfKh optMap; rw [h1, h2]; rfl

theorem Sched.IpcSorted.ar (hS : IpcSorted σ) (h : ArFr σ σ') : IpcSorted σ' :=
  ⟨fun p x hp => (hS.1 p x ((h.look (fun _ e => by cases e)).1 hp)).congr fun u _ => prioOf_ar h u,
    fun p x hp => (hS.2 p x (h.ntfn.1 hp)).congr fun u _ => prioOf_ar h u⟩

theorem CurInvW.ar (hC : σ.schedulerAction = .chooseNewThread ∨ CurInv σ) (h : ArFr σ σ') :
    σ'.schedulerAction = .chooseNewThread ∨ CurInv σ' := by
  rcases hC with e | hI
  · left; rw [h.act]; exact e
  · right; exact hI.ar h

/-! ### The ASID table: an arch finalisation only clears entries -/

/-- The ASID table. -/
def tblF (σ : State Unit) : AsidHighIndex → Option ObjRef := σ.archState.x64AsidTable

theorem ft_setObject (p : ObjRef) (o : KernelObject) : Vs.FK tblF (setObject (Z := Unit) p o) := by
  unfold setObject; dk_auto0

theorem ft_doMachineOp {α : Type} (mop : NonDet MachineState α) : Vs.FK tblF (doMachineOp (Z := Unit) mop) := by
  unfold doMachineOp
  refine Vs.dk_bind (Vs.dk_gets _) (fun _ => Vs.dk_bind (Vs.dk_selectF _) (fun x => ?_))
  obtain ⟨r, ms⟩ := x
  exact Vs.dk_bind (Vs.dk_modify (fun σ => rfl)) (fun _ => Vs.dk_pure _)

/-- `FK tblF` of the spec's VSpace operations that do not write the table. -/
macro "ft_auto" : tactic => `(tactic| repeat' (first | exact ft_setObject _ _ | exact fk_getCapG _ _ | exact ft_doMachineOp _ | dk_step0 | fk_unf | sched_unf | vs_unf))

/-- **An empty ASID-table entry stays empty** across every outcome of `m`. -/
def TN {α : Type} (m : NonDet (State Unit) α) : Prop :=
  ∀ σ x, x ∈ (m σ).1 → ∀ i, σ.archState.x64AsidTable i = none → x.2.archState.x64AsidTable i = none

theorem tn_of_fk {α : Type} {m : NonDet (State Unit) α} (h : Vs.FK tblF m) : TN m := by
  intro σ x hx i hi
  have e : tblF x.2 = tblF σ := h σ x hx
  simp only [tblF] at e
  rw [e]; exact hi

theorem tn_bind {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : TN m)
    (hg : ∀ a, TN (g a)) : TN (m >>= g) := by
  intro σ x ⟨y, hy, hx⟩ i hi
  exact hg y.1 y.2 x hx i (hm σ y hy i hi)

set_option maxHeartbeats 8000000 in
/-- `delete_asid_pool` clears one entry of the table (the one it read). -/
theorem tn_deleteAsidPool (b : Asid) (ptr : ObjRef) : TN (deleteAsidPool (Z := Unit) b ptr) := by
  intro σ x hx i hi
  unfold deleteAsidPool at hx
  obtain ⟨y1, hy1, hx⟩ := hx
  obtain ⟨-, rfl⟩ := hy1
  obtain ⟨y2, hy2, hx⟩ := hx
  have e2 := Set.mem_singleton_iff.1 hy2
  subst e2
  dsimp only at hx
  unfold NonDet.when at hx
  split at hx
  · obtain ⟨z1, hz1, hx⟩ := hx
    have e1 : tblF z1.2 = tblF σ := (by ft_auto : Vs.FK tblF _) _ _ hz1
    dsimp only at hx
    obtain ⟨z2, hz2, hx⟩ := hx
    have e2 : tblF z2.2 = tblF z1.2 := (by ft_auto : Vs.FK tblF _) _ _ hz2
    dsimp only at hx
    obtain ⟨z3, hz3, hx⟩ := hx
    have e3 := Set.mem_singleton_iff.1 hz3
    subst e3
    dsimp only at hx
    obtain ⟨z4, hz4, hx⟩ := hx
    have e4 := Set.mem_singleton_iff.1 hz4
    subst e4
    dsimp only at hx
    have e5 := (by ft_auto : Vs.FK tblF _) _ _ hx
    simp only [tblF] at e1 e2 e5 ⊢
    rw [e5, Function.update_apply]
    split_ifs
    · rfl
    · exact hi
  · rw [Set.mem_singleton_iff.1 hx]; exact hi

set_option maxHeartbeats 8000000 in
/-- **The spec's arch finalisation keeps an empty ASID-table entry empty**
(only `delete_asid_pool` writes the table, clearing an entry). -/
theorem tn_archFinaliseCap (c : ArchCap) (x : Bool) : TN (archFinaliseCap (Z := Unit) c x) := by
  unfold archFinaliseCap
  split
  · exact tn_bind (tn_deleteAsidPool _ _) fun _ => tn_of_fk (Vs.dk_pure _)
  all_goals exact tn_of_fk (by ft_auto)

end Spec

end

end Fl4Proofs.P3
