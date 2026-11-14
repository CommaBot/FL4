/-
P3 (DESIGN.md §9), scheduling contexts: **`complete_yield_to`, SchedContext
`YieldTo` and `Consumed`** against l4v `complete_yield_to`,
`sched_context_yield_to` and `return_consumed`.

`set_consumed`'s message writes (`lookup_ipc_buffer`, the badge register,
`set_mr`, `set_msg_info`: `msgW`) are the Ep side's: `MsgOK` is the
hypothesis that they refine the spec's `reply_from_kernel` (keeping
`SchedRel` and `NtfnStateRel`), change only TCBs' user context and the user
memory on the spec side (`ArchStep`), and write no `YIELD_TO` word.

* `ArchStep`: the spec side of a message write keeps `Inv`, `NSC`,
  `schedulable` and the yield fields;
* `YieldRel.clear`, `YieldRel.pair`: the yield-to relation across
  `sched_context_cancel_yield_to` and the yield-to link of `YieldTo`.
-/
import Fl4Proofs.P3.ScYield
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

/-- The spec side of a message write: only TCBs' user context and the user
memory change. -/
def ArchStep (σ σ' : State Unit) : Prop :=
  σ'.exst = σ.exst ∧
  { σ'.toAbstractState with kheap := σ.kheap, machineState := σ.machineState } = σ.toAbstractState ∧
  ∀ p, σ'.kheap p = σ.kheap p ∨
    ∃ x y, σ.kheap p = some (.tcb x) ∧ σ'.kheap p = some (.tcb y) ∧ y = { x with tcbArch := y.tcbArch }

theorem ArchStep.abs {σ σ' : State Unit} (h : ArchStep σ σ') :
    σ'.readyQueues = σ.readyQueues ∧ σ'.releaseQueue = σ.releaseQueue ∧ σ'.curThread = σ.curThread ∧
    σ'.schedulerAction = σ.schedulerAction ∧ σ'.curTime = σ.curTime ∧ σ'.idleThread = σ.idleThread := by
  have e := h.2.1
  exact ⟨(by have := congrArg AbstractState.readyQueues e; exact this),
    (by have := congrArg AbstractState.releaseQueue e; exact this),
    (by have := congrArg AbstractState.curThread e; exact this),
    (by have := congrArg AbstractState.schedulerAction e; exact this),
    (by have := congrArg AbstractState.curTime e; exact this),
    (by have := congrArg AbstractState.idleThread e; exact this)⟩

theorem ArchStep.tcb {σ σ' : State Unit} (h : ArchStep σ σ') {p : ObjRef} {x : Tcb}
    (hk : σ.kheap p = some (.tcb x)) : ∃ y, σ'.kheap p = some (.tcb y) ∧ y = { x with tcbArch := y.tcbArch } := by
  rcases h.2.2 p with e | ⟨a, b, ha, hb, e⟩
  · exact ⟨x, e.trans hk, rfl⟩
  · rw [hk] at ha; cases ha; exact ⟨b, hb, e⟩

theorem ArchStep.tcb_back {σ σ' : State Unit} (h : ArchStep σ σ') {p : ObjRef} {y : Tcb}
    (hk : σ'.kheap p = some (.tcb y)) : ∃ x, σ.kheap p = some (.tcb x) ∧ y = { x with tcbArch := y.tcbArch } := by
  rcases h.2.2 p with e | ⟨a, b, ha, hb, e⟩
  · exact ⟨y, by rw [← e]; exact hk, rfl⟩
  · rw [hk] at hb; cases hb; exact ⟨a, ha, e⟩

theorem ArchStep.nontcb {σ σ' : State Unit} (h : ArchStep σ σ') {p : ObjRef} {o : KernelObject}
    (ho : ∀ x, o ≠ .tcb x) : σ'.kheap p = some o ↔ σ.kheap p = some o := by
  rcases h.2.2 p with e | ⟨a, b, ha, hb, e⟩
  · rw [e]
  · rw [ha, hb]; constructor <;> intro h' <;> cases h' <;> exact absurd rfl (ho _)

theorem ArchStep.sc {σ σ' : State Unit} (h : ArchStep σ σ') {p : ObjRef} {y : SchedContext} {n : Nat} :
    σ'.kheap p = some (.schedContext y n) ↔ σ.kheap p = some (.schedContext y n) :=
  h.nontcb fun _ e => by cases e

theorem ArchStep.ykeep {σ σ' : State Unit} (h : ArchStep σ σ') : YKeep σ σ' := by
  refine ⟨fun p x hp => ?_, fun p x n hp => ⟨x, h.sc.2 hp, rfl⟩, fun p y n hp => ⟨y, h.sc.1 hp, rfl⟩⟩
  obtain ⟨y, hy, e⟩ := h.tcb hp
  exact ⟨y, hy, by rw [e]⟩

theorem ArchStep.nsc {N C : Set U64} {σ σ' : State Unit} (h : ArchStep σ σ') (hN : NSC N C σ) : NSC N C σ' :=
  fun n hn x p hx hp => hN n hn x p ((h.nontcb fun _ e => by cases e).1 hx) hp

/-- The invariant across a step changing TCBs but not their state or SC. -/
theorem Inv.tcbView {σ σ' : State Unit} (h : Inv σ)
    (hk : ∀ p, σ'.kheap p = σ.kheap p ∨ ∃ x y, σ.kheap p = some (.tcb x) ∧ σ'.kheap p = some (.tcb y) ∧
      y.tcbState = x.tcbState ∧ y.tcbSchedContext = x.tcbSchedContext)
    (hq : σ'.readyQueues = σ.readyQueues) (hr : σ'.releaseQueue = σ.releaseQueue) (ht : σ'.curTime = σ.curTime) :
    Inv σ' := by
  have kf : ∀ q y, σ.kheap q = some (.tcb y) → ∃ y', σ'.kheap q = some (.tcb y') ∧
      y'.tcbState = y.tcbState ∧ y'.tcbSchedContext = y.tcbSchedContext := by
    intro q y hq
    rcases hk q with e | ⟨a, b, ha, hb, e1, e2⟩
    · exact ⟨y, e.trans hq, rfl, rfl⟩
    · rw [hq] at ha; cases ha; exact ⟨b, hb, e1, e2⟩
  have kb : ∀ q y', σ'.kheap q = some (.tcb y') → ∃ y, σ.kheap q = some (.tcb y) ∧
      y'.tcbState = y.tcbState ∧ y'.tcbSchedContext = y.tcbSchedContext := by
    intro q y' hq
    rcases hk q with e | ⟨a, b, ha, hb, e1, e2⟩
    · exact ⟨y', by rw [← e]; exact hq, rfl, rfl⟩
    · rw [hq] at hb; cases hb; exact ⟨a, ha, e1, e2⟩
  have ks : ∀ q y m, σ'.kheap q = some (.schedContext y m) ↔ σ.kheap q = some (.schedContext y m) := by
    intro q y m
    rcases hk q with e | ⟨a, b, ha, hb, -, -⟩
    · rw [e]
    · rw [ha, hb]; simp
  have kn' : ∀ q y, σ'.kheap q = some (.notification y) ↔ σ.kheap q = some (.notification y) := by
    intro q y
    rcases hk q with e | ⟨a, b, ha, hb, -, -⟩
    · rw [e]
    · rw [ha, hb]; simp
  have rt : ∀ u ∈ σ.releaseQueue, specRt σ' u = specRt σ u := by
    intro u hu
    obtain ⟨xu, scp, yu, nu, h1, h2, -, h4, -⟩ := h.rel u hu
    obtain ⟨xu', h1', -, e2⟩ := kf u xu h1
    have hne := h.ne scp yu nu h4
    rw [specRt_eq h1' (e2.trans h2) ((ks _ _ _).2 h4) hne, specRt_eq h1 h2 h4 hne]
  refine ⟨fun d q u hu => ?_, fun u hu => ?_, ?_, fun u y hy hc => ?_, fun q y m hy => ?_,
    fun u y q hy hq => ?_, fun q y q' hy hq => ?_, fun q y m hy => ?_, fun q y m hy => ?_⟩
  · rw [hq] at hu
    obtain ⟨xu, scp, yu, nu, h1, h2, h3, h4, h5⟩ := h.rq d q u hu
    obtain ⟨xu', h1', e1, e2⟩ := kf u xu h1
    exact ⟨xu', scp, yu, nu, h1', e2.trans h2, by rw [e1]; exact h3, (ks _ _ _).2 h4, h5⟩
  · rw [hr] at hu
    obtain ⟨xu, scp, yu, nu, h1, h2, h3, h4, h5⟩ := h.rel u hu
    obtain ⟨xu', h1', e1, e2⟩ := kf u xu h1
    exact ⟨xu', scp, yu, nu, h1', e2.trans h2, by rw [e1]; exact h3, (ks _ _ _).2 h4, h5⟩
  · rw [hr]
    refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab => ?_) h.sorted
    rw [rt a ha, rt b hb]; exact hab
  · intro x' scp yu nu h1 h2 h3 h4 h5
    obtain ⟨y0, hy0, e1, -⟩ := kb u y hy
    obtain ⟨x0, hx0, -, e2⟩ := kb u x' h1
    rw [released_congr ht]
    exact h.rd u y0 hy0 (by rw [← e1]; exact hc) x0 scp yu nu hx0 (by rw [← e2]; exact h2) ((ks _ _ _).1 h3) h4
      (by rw [← hr]; exact h5)
  · exact h.refills q y m ((ks _ _ _).1 hy)
  · obtain ⟨y0, hy0, -, e2⟩ := kb u y hy
    obtain ⟨yq, mq, h1, h2⟩ := h.back u y0 q hy0 (by rw [← e2]; exact hq)
    exact ⟨yq, mq, (ks _ _ _).2 h1, h2⟩
  · obtain ⟨yq, mq, h1⟩ := h.ntfnSc q y q' ((kn' _ _).1 hy) hq
    exact ⟨yq, mq, (ks _ _ _).2 h1⟩
  · exact h.ne q y m ((ks _ _ _).1 hy)
  · exact h.rr q y m ((ks _ _ _).1 hy)

theorem ArchStep.inv {σ σ' : State Unit} (h : ArchStep σ σ') (hI : Inv σ) : Inv σ' := by
  obtain ⟨e1, e2, -, -, e5, -⟩ := h.abs
  refine hI.tcbView (fun p => ?_) e1 e2 e5
  rcases h.2.2 p with e | ⟨a, b, ha, hb, e⟩
  · exact Or.inl e
  · exact Or.inr ⟨a, b, ha, hb, by rw [e], by rw [e]⟩

theorem ArchStep.schedulable {σ σ' : State Unit} (h : ArchStep σ σ') (u : ObjRef) :
    schedulable u σ' = schedulable u σ := by
  obtain ⟨-, e2, -, -, -, -⟩ := h.abs
  have hsc : ∀ p, scsOf σ' p = scsOf σ p := by
    intro p
    rcases h.2.2 p with e | ⟨a, b, ha, hb, e⟩
    · simp only [scsOfKh, optMap, e]
    · simp only [scsOfKh, optMap, ha, hb]; rfl
  unfold Fl4Spec.schedulable
  apply decide_eq_decide.2
  rw [e2]
  rcases h.2.2 u with e | ⟨a, b, ha, hb, e⟩
  · simp only [optPred, optMapSome, optMap, tcbsOfKh, e, hsc]
  · have h1 : tcbsOf σ u = some a := by simp only [tcbsOfKh, optMap, ha]; rfl
    have h2 : tcbsOf σ' u = some b := by simp only [tcbsOfKh, optMap, hb]; rfl
    simp only [optPred, optMapSome, optMap, h1, h2, hsc]
    rw [e]

theorem nd_pure_one {σ' α : Type} {a b : α} {s s' : σ'}
    (h : (pure a : NonDet σ' α) s = ({(b, s')}, False)) : s' = s ∧ b = a := by
  change (({(a, s)}, False) : Set (α × σ') × Prop) = ({(b, s')}, False) at h
  have := (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst h)))
  exact ⟨this.2.symm, this.1.symm⟩

/-! ### The yield-to steps -/

theorem cancelYieldTo_some {σ : State Unit} {t p : ObjRef} {x : Tcb} {y : SchedContext} {n : Nat}
    (hkt : σ.kheap t = some (.tcb x)) (hyt : x.tcbYieldTo = some p)
    (hkp : σ.kheap p = some (.schedContext y n)) (hpt : p ≠ t) :
    schedContextCancelYieldTo (Z := Unit) t σ = ({((), updK (updSc σ p { y with scYieldFrom := none } n) t
      (.tcb { x with tcbYieldTo := none }))}, False) := by
  unfold schedContextCancelYieldTo
  rw [nd_bind_one (Fl4Proofs.P3.Endp.getTcbObjRef_eq _ hkt), hyt]
  show (setScObjRef scYieldFromUpdate p none >>= fun _ => setTcbObjRef tcbYieldToUpdate t none) σ = _
  rw [nd_bind_one (updateSchedContext_eq hkp _)]
  have hkt' : (updSc σ p (scYieldFromUpdate (fun _ => none) y) n).kheap t = some (.tcb x) := by
    simp [updK, Ne.symm hpt, hkt]
  exact threadSet_eq _ hkt'

theorem completeYieldTo_some {σ : State Unit} {t p : ObjRef} {x : Tcb}
    (hkt : σ.kheap t = some (.tcb x)) (hyt : x.tcbYieldTo = some p) :
    completeYieldTo (Z := Unit) t σ = (setConsumed p t >>= fun _ => schedContextCancelYieldTo t) σ := by
  unfold completeYieldTo
  rw [nd_bind_one (Fl4Proofs.P3.Endp.getTcbObjRef_eq _ hkt), hyt]; rfl

theorem completeYieldTo_none {σ : State Unit} {t : ObjRef} {x : Tcb}
    (hkt : σ.kheap t = some (.tcb x)) (hyt : x.tcbYieldTo = none) :
    completeYieldTo (Z := Unit) t σ = ({((), σ)}, False) := by
  unfold completeYieldTo
  rw [nd_bind_one (Fl4Proofs.P3.Endp.getTcbObjRef_eq _ hkt), hyt]; rfl


/-- What the later steps of `YieldTo` read, kept: TCBs' state, SC,
priority and domain, SCs' bound TCB and activity, the release queue and
the current thread. -/
structure SFrame (σ σ' : State Unit) : Prop where
  tcb : ∀ p x, σ.kheap p = some (.tcb x) → ∃ x', σ'.kheap p = some (.tcb x') ∧ x'.tcbState = x.tcbState ∧
    x'.tcbSchedContext = x.tcbSchedContext ∧ x'.tcbPriority = x.tcbPriority ∧ x'.tcbDomain = x.tcbDomain
  sc : ∀ p x n, σ.kheap p = some (.schedContext x n) → ∃ x', σ'.kheap p = some (.schedContext x' n) ∧
    x'.scTcb = x.scTcb ∧ scActive x' = scActive x
  rel : σ'.releaseQueue = σ.releaseQueue
  cur : σ'.curThread = σ.curThread
  act : σ'.schedulerAction = σ.schedulerAction
  idle : σ'.idleThread = σ.idleThread

theorem SFrame.refl (σ : State Unit) : SFrame σ σ :=
  ⟨fun _ x h => ⟨x, h, rfl, rfl, rfl, rfl⟩, fun _ x _ h => ⟨x, h, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩

theorem SFrame.trans {σ σ1 σ2 : State Unit} (h1 : SFrame σ σ1) (h2 : SFrame σ1 σ2) : SFrame σ σ2 := by
  refine ⟨fun p x hp => ?_, fun p x n hp => ?_, h2.rel.trans h1.rel, h2.cur.trans h1.cur, h2.act.trans h1.act,
    h2.idle.trans h1.idle⟩
  · obtain ⟨y, hy, a1, a2, a3, a4⟩ := h1.tcb p x hp
    obtain ⟨z, hz, b1, b2, b3, b4⟩ := h2.tcb p y hy
    exact ⟨z, hz, b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4⟩
  · obtain ⟨y, hy, a1, a2⟩ := h1.sc p x n hp
    obtain ⟨z, hz, b1, b2⟩ := h2.sc p y n hy
    exact ⟨z, hz, b1.trans a1, b2.trans a2⟩

theorem ArchStep.sframe {σ σ' : State Unit} (h : ArchStep σ σ') : SFrame σ σ' := by
  obtain ⟨-, e2, e3, e4, -, e6⟩ := h.abs
  refine ⟨fun p x hp => ?_, fun p x n hp => ⟨x, h.sc.2 hp, rfl, rfl⟩, e2, e3, e4, e6⟩
  obtain ⟨y, hy, e⟩ := h.tcb hp
  exact ⟨y, hy, by rw [e], by rw [e], by rw [e], by rw [e]⟩

theorem SFrame.updSc {σ : State Unit} {p : ObjRef} {x x' : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext x n)) (e1 : x'.scTcb = x.scTcb) (e2 : x'.scRefillMax = x.scRefillMax) :
    SFrame σ (updSc σ p x' n) := by
  refine ⟨fun q y hq => ?_, fun q y m hq => ?_, rfl, rfl, rfl, rfl⟩
  · have h : q ≠ p := by rintro rfl; rw [hk] at hq; cases hq
    exact ⟨y, by simp [updK, h, hq], rfl, rfl, rfl, rfl⟩
  · by_cases h : q = p
    · subst h; rw [hk] at hq; cases hq
      exact ⟨x', by simp [updK], e1, by simp only [scActive, e2]⟩
    · exact ⟨y, by simp [updK, h, hq], rfl, rfl⟩

theorem SFrame.ytUpd {σ : State Unit} {p : ObjRef} {x : Tcb} (hk : σ.kheap p = some (.tcb x)) (v : Option ObjRef) :
    SFrame σ (updK σ p (.tcb { x with tcbYieldTo := v })) := by
  refine ⟨fun q y hq => ?_, fun q y m hq => ?_, rfl, rfl, rfl, rfl⟩
  · by_cases h : q = p
    · subst h; rw [hk] at hq; cases hq
      exact ⟨{ x with tcbYieldTo := v }, by simp [updK], rfl, rfl, rfl, rfl⟩
    · exact ⟨y, by simp [updK, h, hq], rfl, rfl, rfl, rfl⟩
  · have h : q ≠ p := by rintro rfl; rw [hk] at hq; cases hq
    exact ⟨y, by simp [updK, h, hq], rfl, rfl⟩

theorem SFrame.schedulable {σ σ' : State Unit} (h : SFrame σ σ') {u : ObjRef} (hs : schedulable u σ = true) :
    schedulable u σ' = true := by
  obtain ⟨x, scp, y, n, h1, h2, h3, h4, h5, h6⟩ := schedulable_inv hs
  obtain ⟨x', h1', a1, a2, -, -⟩ := h.tcb u x h1
  obtain ⟨y', h4', -, b2⟩ := h.sc scp y n h4
  exact schedulable_of h1' (a2.trans h2) (by rw [a1]; exact h3) h4' (b2.trans h5) (by rw [h.rel]; exact h6)

/-- **`ActIdle` under `SFrame`.** -/
theorem ActIdle.sframe {σ σ' : State Unit} (h : ActIdle σ) (hf : SFrame σ σ') : ActIdle σ' := by
  obtain ⟨hA, x, h1, h2, h3, h4⟩ := h
  obtain ⟨x', h1', e1, e2, -, -⟩ := hf.tcb _ x h1
  exact ⟨fun t ht => hf.schedulable (hA t (hf.act ▸ ht)), x', by rw [hf.idle]; exact h1', e2.trans h2,
    e1.trans h3, by rw [hf.idle, hf.rel]; exact h4⟩

/-- `reschedule_required` ends with `choose_new_thread`, keeping the heap, the
release queue and the idle thread. -/
theorem rescheduleRequired_act {σ σ' : State Unit} (hA : ActReady σ)
    (he : rescheduleRequired (Z := Unit) σ = ({((), σ')}, False)) :
    σ'.schedulerAction = .chooseNewThread ∧ σ'.kheap = σ.kheap ∧ σ'.releaseQueue = σ.releaseQueue ∧
      σ'.idleThread = σ.idleThread := by
  cases ha : σ.schedulerAction with
  | switchThread t =>
    by_cases hs : schedulable t σ = true
    · obtain ⟨x, -, -, -, hk, -⟩ := schedulable_inv hs
      have he1 := tcbSchedAction_gen hk tcbSchedEnqueue
      have e := the_result (rescheduleRequired_sched ha hs hA he1) he
      subst e
      exact ⟨rfl, rfl, rfl, rfl⟩
    · have e := the_result (rescheduleRequired_notsched ha (by simpa using hs)) he
      subst e; exact ⟨rfl, rfl, rfl, rfl⟩
  | resumeCurThread =>
    have e := the_result (rescheduleRequired_noswitch (fun t h => by rw [ha] at h; cases h)) he
    subst e; exact ⟨rfl, rfl, rfl, rfl⟩
  | chooseNewThread =>
    have e := the_result (rescheduleRequired_noswitch (fun t h => by rw [ha] at h; cases h)) he
    subst e; exact ⟨rfl, rfl, rfl, rfl⟩


theorem getScObjRef_eq {σ : State Unit} {p : ObjRef} {x : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext x n)) (f : SchedContext → Option ObjRef) :
    getScObjRef (Z := Unit) f p σ = ({(f x, σ)}, False) := by
  unfold getScObjRef; rw [nd_bind_one (getSchedContext_eq hk)]; rfl

/-- `sched_context_resume` of an SC whose thread, if schedulable, has it
released, is a no-op. -/
theorem resume_spec_noop {σ : State Unit} {p t : ObjRef} {x : SchedContext} {n : Nat} {xt : Tcb}
    (hk : σ.kheap p = some (.schedContext x n)) (htc : x.scTcb = some t) (hkt : σ.kheap t = some (.tcb xt))
    (hne : x.scRefills ≠ [])
    (hrun : schedulable t σ = true → runnable xt.tcbState = true ∧ scActive x = true)
    (hrel : schedulable t σ = true → released σ x) :
    schedContextResume (Z := Unit) p σ = ({((), σ)}, False) := by
  unfold schedContextResume
  rw [nd_bind_one (getSchedContext_eq hk), htc,
    nd_bind_one (show NonDet.assertOpt (σ := State Unit) (some t) σ = ({(t, σ)}, False) from rfl), nd_gets_bind]
  by_cases hs : schedulable t σ = true
  · obtain ⟨h1, h2⟩ := hrun hs
    have hc := hrel hs
    simp only [NonDet.when, hs, ↓reduceIte]
    rw [nd_bind_one (threadGet_eq _ hkt), nd_bind_one (getScRefillReady_eq hk hne),
      nd_bind_one (getScRefillSufficient_eq hk hne 0)]
    rw [ite_f (fun h => h.2.2 hc)]; rfl
  · simp only [NonDet.when, hs, Bool.false_eq_true, ↓reduceIte]; rfl

/-- Under `Inv`, the SC's thread (bound both ways), if schedulable, has it
released and runnable. -/
theorem Inv.yieldRes {σ : State Unit} (h : Inv σ) {p t : ObjRef} {x : SchedContext} {n : Nat} {xt : Tcb}
    (hk : σ.kheap p = some (.schedContext x n)) (hkt : σ.kheap t = some (.tcb xt))
    (hxt : xt.tcbSchedContext = some p) :
    (schedulable t σ = true → runnable xt.tcbState = true ∧ scActive x = true) ∧
    (schedulable t σ = true → released σ x) := by
  refine ⟨fun hs => ?_, fun hs => ?_⟩ <;>
  · obtain ⟨x', scp, y, m, h1, h2, h3, h4, h5, h6⟩ := schedulable_inv hs
    rw [hkt] at h1; cases h1
    rw [hxt] at h2; cases h2
    rw [hk] at h4; cases h4
    first
      | exact ⟨h3, h5⟩
      | exact h.rd t xt hkt (Or.inl h3) xt p x n hkt hxt hk h5 h6


/-- l4v `sched_context_yield_to`'s `return_now` computation. -/
def yieldSwitch (scPtr : ObjRef) : SMonad Unit Bool := do
  let scTcbOpt ← getScObjRef SchedContext.scTcb scPtr
  let tcbPtr ← NonDet.assertOpt scTcbOpt
  let schedulable ← NonDet.gets (schedulable tcbPtr)
  if schedulable then do
    let ctPtr ← NonDet.gets fun s : State Unit => s.curThread
    let prios ← threadGet Tcb.tcbPriority tcbPtr
    let ctPrios ← threadGet Tcb.tcbPriority ctPtr
    if prios < ctPrios
    then do
      tcbSchedAction tcbSchedDequeue tcbPtr
      tcbSchedAction tcbSchedEnqueue tcbPtr
      pure true
    else do
      setTcbObjRef tcbYieldToUpdate ctPtr (some scPtr)
      setScObjRef scYieldFromUpdate scPtr (some ctPtr)
      tcbSchedAction tcbSchedDequeue tcbPtr
      tcbSchedAction tcbSchedEnqueue ctPtr
      tcbSchedAction tcbSchedEnqueue tcbPtr
      rescheduleRequired
      pure false
  else pure true

end Spec

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- **`sched_context_cancel_yield_to`'s effect on the yield-to relation**:
the pair `(y, p)` is cut. -/
theorem YieldRel.clear {T C : Set U64} {m m' : U64 → U64} {σ : Fl4Spec.State Unit} (h : YieldRel T C m σ)
    {y p : U64} (hy : y ∈ T) (hyp : m (yieldA y) = p) (hp0 : p ≠ 0#u64) {xy : Fl4Spec.Tcb}
    {yp : Fl4Spec.SchedContext} {n : Nat}
    (hky : σ.kheap y.bv = some (.tcb xy)) (hkp : σ.kheap p.bv = some (.schedContext yp n))
    (hm' : ∀ u ∈ T, u ≠ y → m' (yieldA u) = m (yieldA u)) (hmy : m' (yieldA y) = 0#u64) :
    YieldRel T C m' (updK (updSc σ p.bv { yp with scYieldFrom := none } n) y.bv
      (.tcb { xy with tcbYieldTo := none })) := by
  have hpy : p.bv ≠ y.bv := fun e => by rw [e, hky] at hkp; cases hkp
  obtain ⟨-, zy, ky, hzy, ezy⟩ := h.toSc y hy (by rw [hyp]; exact hp0)
  rw [hyp] at hzy; rw [hkp] at hzy; cases hzy
  refine ⟨fun u hu => ?_, fun u hu h0 => ?_, fun sc hsc z k hz q hq => ?_⟩
  · by_cases e : u = y
    · rw [e]
      exact ⟨{ xy with tcbYieldTo := none }, by simp [updK], by rw [hmy, optRef_zero]⟩
    · obtain ⟨x, hx, ex⟩ := h.tcb u hu
      have hpu : p.bv ≠ u.bv := fun e' => by rw [e', hx] at hkp; cases hkp
      exact ⟨x, by simp [updK, bv_ne e, Ne.symm hpu, hx], by rw [hm' u hu e]; exact ex⟩
  · have e : u ≠ y := by rintro rfl; exact h0 hmy
    rw [hm' u hu e] at h0 ⊢
    obtain ⟨h1, z, k, hz, ez⟩ := h.toSc u hu h0
    have hne : (m (yieldA u)).bv ≠ p.bv := by
      intro e'
      rw [e', hkp] at hz; cases hz
      exact e (eq_of_bv (Option.some.inj (ez.symm.trans ezy)))
    have hny : (m (yieldA u)).bv ≠ y.bv := fun e' => by rw [e', hky] at hz; cases hz
    exact ⟨h1, z, k, by simp [updK, hne, hny, hz], ez⟩
  · by_cases e : sc = p
    · subst e; simp [updK, hpy] at hz; obtain ⟨rfl, -⟩ := hz; cases hq
    · have hny : sc.bv ≠ y.bv := fun e' => by simp [updK, e'] at hz
      have hz' : σ.kheap sc.bv = some (.schedContext z k) := by simpa [updK, hny, bv_ne e] using hz
      obtain ⟨t', ht', e1, e2⟩ := h.frm sc hsc z k hz' q hq
      have ht'y : t' ≠ y := by rintro rfl; exact e (e2.symm.trans hyp)
      exact ⟨t', ht', e1, by rw [hm' t' ht' ht'y]; exact e2⟩

/-- **The yield-to link of `YieldTo`**: `ct` yields to `sc`. -/
theorem YieldRel.pair {T C : Set U64} {m m' : U64 → U64} {σ : Fl4Spec.State Unit} (h : YieldRel T C m σ)
    (hC0 : ∀ q ∈ C, q ≠ 0#u64) {ct sc : U64} (hct : ct ∈ T) (hsc : sc ∈ C) (hm0 : m (yieldA ct) = 0#u64)
    {xc : Fl4Spec.Tcb} {ysc : Fl4Spec.SchedContext} {n : Nat}
    (hkc : σ.kheap ct.bv = some (.tcb xc)) (hks : σ.kheap sc.bv = some (.schedContext ysc n))
    (hyf : ysc.scYieldFrom = none)
    (hm' : ∀ u ∈ T, u ≠ ct → m' (yieldA u) = m (yieldA u)) (hmc : m' (yieldA ct) = sc) :
    YieldRel T C m' (updSc (updK σ ct.bv (.tcb { xc with tcbYieldTo := some sc.bv })) sc.bv
      { ysc with scYieldFrom := some ct.bv } n) := by
  have hpc : sc.bv ≠ ct.bv := fun e => by rw [e, hkc] at hks; cases hks
  refine ⟨fun u hu => ?_, fun u hu h0 => ?_, fun q hq z k hz p hp => ?_⟩
  · by_cases e : u = ct
    · rw [e]
      exact ⟨{ xc with tcbYieldTo := some sc.bv }, by simp [updK, Ne.symm hpc], by rw [hmc, optRef_ne (hC0 sc hsc)]⟩
    · obtain ⟨x, hx, ex⟩ := h.tcb u hu
      have hpu : sc.bv ≠ u.bv := fun e' => by rw [e', hx] at hks; cases hks
      exact ⟨x, by simp [updK, bv_ne e, Ne.symm hpu, hx], by rw [hm' u hu e]; exact ex⟩
  · by_cases e : u = ct
    · rw [e, hmc]
      exact ⟨hsc, { ysc with scYieldFrom := some ct.bv }, n, by simp [updK], rfl⟩
    · rw [hm' u hu e] at h0 ⊢
      obtain ⟨h1, z, k, hz, ez⟩ := h.toSc u hu h0
      have hne : (m (yieldA u)).bv ≠ sc.bv := by
        intro e'; rw [e', hks] at hz; cases hz; rw [hyf] at ez; cases ez
      have hnc : (m (yieldA u)).bv ≠ ct.bv := fun e' => by rw [e', hkc] at hz; cases hz
      exact ⟨h1, z, k, by simp [updK, hne, hnc, hz], ez⟩
  · by_cases e : q = sc
    · subst e
      simp [updK] at hz; obtain ⟨rfl, -⟩ := hz
      cases hp
      exact ⟨ct, hct, rfl, hmc⟩
    · have hnc : q.bv ≠ ct.bv := fun e' => by simp [updK, e', Ne.symm hpc] at hz
      have hz' : σ.kheap q.bv = some (.schedContext z k) := by simpa [updK, hnc, bv_ne e] using hz
      obtain ⟨t', ht', e1, e2⟩ := h.frm q hq z k hz' p hp
      have ht'c : t' ≠ ct := by rintro rfl; rw [hm0] at e2; exact hC0 q hq e2.symm
      exact ⟨t', ht', e1, by rw [hm' t' ht' ht'c]; exact e2⟩


/-- `set_consumed`'s message writes (`write_msg`). -/
def msgW (st : machine.Store S) (s1 : S) (t c : U64) : Result S := do
  let buf ← msg.lookup_ipc_buffer st s1 true t
  let s2 ← obj.Tcb.set_reg st t s1 layout.reg.BADGE 0#u64
  let (len, s3) ← msg.set_mr st s2 t buf 0#u64 c
  let mi ← msginfo.MessageInfo.new 0#u64 0#u64 0#u64 len
  msg.set_msg_info st s3 t mi

theorem set_consumed_eq (s : S) (a : A) (sc t : U64) (wm : Bool) :
    schedcontext.set_consumed st ar s a sc t wm =
      (do let (c, s1) ← schedcontext.update_consumed st ar s a sc; if wm then msgW st s1 t c else ok s1) := by
  unfold schedcontext.set_consumed msgW; rfl

/-- **The Ep side's message hypothesis**: `set_consumed`'s message writes
refine `reply_from_kernel` with the consumed time, keeping the scheduler and
notification relations; on the spec side only TCBs' user context and the
user memory change, no `YIELD_TO` word is written, and FL4 writes only `t`'s
registers (`SFoot`: TCB words past offset 256; `msgW` writes the badge, the
first message register and the message info). -/
def MsgOK (st : machine.Store S) [L : LawfulStore st] (N T C : Set U64) (c : U64) : Prop :=
  ∀ (s1 : S) (σ1 : Fl4Spec.State Unit) (t v : U64), t ∈ T → SchedRel st N T C c s1 σ1 →
    NtfnStateRel N T (L.mem s1) σ1 →
    msgW st s1 t v ⦃ s' => ∃ σ', Fl4Spec.replyFromKernel (Z := Unit) t.bv (0, Fl4Spec.wordsFromTime v.bv) σ1 =
      ({((), σ')}, False) ∧ SchedRel st N T C c s' σ' ∧ NtfnStateRel N T (L.mem s') σ' ∧ ArchStep σ1 σ' ∧
      WritesIn st s1 s' (fun b => ¬ YW T b) ∧ WritesIn st s1 s' (SFoot st T c s1) ⦄

/-- **`set_consumed` refines l4v `set_consumed`** (`write_msg`) or
`sched_context_update_consumed` (no message). -/
theorem set_consumed_refines {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hY : YieldRel T C (L.mem s) σ) {p : U64} (hpC : p ∈ C) {t : U64} (ht : t ∈ T) (wm : Bool)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, ar.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) (hmsg : MsgOK st N T C c) :
    schedcontext.set_consumed st ar s a p t wm ⦃ s2 => ∃ (cv : U64) (σ1 σ2 : Fl4Spec.State Unit),
      Fl4Spec.schedContextUpdateConsumed (Z := Unit) p.bv σ = ({(cv.bv, σ1)}, False) ∧
      (wm = true → Fl4Spec.replyFromKernel (Z := Unit) t.bv (0, Fl4Spec.wordsFromTime cv.bv) σ1 =
        ({((), σ2)}, False)) ∧ (wm = false → σ2 = σ1) ∧
      SchedRel st N T C c s2 σ2 ∧ NtfnStateRel N T (L.mem s2) σ2 ∧ NSC N C σ2 ∧ Inv σ2 ∧
      YieldRel T C (L.mem s2) σ2 ∧ SFrame σ σ2 ∧ YKeep σ σ2 ∧ WritesIn st s s2 (fun b => ¬ YW T b) ∧
      WritesIn st s s2 (KFoot st T N C c s σ) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hT := hc.tcbs
  have hsw8 := sw_hdr hS hpC (K := 8#u64) (by simp) (by simp) (by decide)
  obtain ⟨ysc, nsc, hksc, hxsc⟩ := hs.scs p hpC
  obtain ⟨ha8, hin8⟩ := hxsc.hdr (K := 8#u64) (by simp) (by simp)
  rw [set_consumed_eq]
  refine WP.spec_bind (update_consumed_refines s a σ hS hR hN hI hpC hmax htu) ?_
  rintro ⟨cv, s1⟩ ⟨σ1, hsp1, hS1, hR1, hN1, hI1, -, v, hs1⟩
  simp only at hs1 hS1 hR1 hN1 hI1 hsp1
  subst hs1
  obtain ⟨w, hσ1⟩ : ∃ w, σ1 = updSc σ p.bv { ysc with scConsumed := w } nsc := by
    unfold Fl4Spec.schedContextUpdateConsumed at hsp1
    rw [nd_bind_one (getSchedContext_eq hksc), nd_pure_bind'] at hsp1
    split_ifs at hsp1
    all_goals
      rw [nd_bind_one (updateSchedContext_eq hksc _)] at hsp1
      exact ⟨_, (nd_pure_one hsp1).1⟩
  have hyk1 : YKeep σ σ1 := by rw [hσ1]; exact YKeep.updSc hksc rfl
  have hsf1 : SFrame σ σ1 := by rw [hσ1]; exact SFrame.updSc hksc rfl rfl
  have hw1 : WritesIn st s (L.wr s (scW p 8#u64) v) (fun b => ¬ YW T b) :=
    (writesIn_wr ha8).mono fun b hb => hb ▸ not_yw_scin hS hpC hin8
  have hY1 : YieldRel T C (L.mem (L.wr s (scW p 8#u64) v)) σ1 := hY.frame (WritesIn.yield_keep hT hw1) hyk1
  have hk1 : WritesIn st s (L.wr s (scW p 8#u64) v) (KFoot st T N C c s σ) :=
    (writesIn_wr ha8).mono fun b hb => hb ▸ KFoot.of_sw hsw8
  cases wm
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact (WP.spec_ok _).mpr ⟨cv, σ1, σ1, hsp1, fun h => absurd h (by decide), fun _ => rfl, hS1, hR1, hN1, hI1,
      hY1, hsf1, hyk1, hw1, hk1⟩
  · simp only [↓reduceIte]
    refine WP.spec_mono (hmsg _ σ1 t cv ht hS1 hR1) ?_
    rintro s2 ⟨σ2, hrfk, hS2, hR2, hA2, hw2, hf2⟩
    exact ⟨cv, σ1, σ2, hsp1, fun _ => hrfk, fun h => absurd h (by decide), hS2, hR2, hA2.nsc hN1, hA2.inv hI1,
      hY1.frame (WritesIn.yield_keep hT hw2) hA2.ykeep, hsf1.trans hA2.sframe, hyk1.trans hA2.ykeep, WritesIn.yw_trans hw1 hw2,
      WritesIn.kfoot_sfoot hk1 hf2⟩

/-- **`complete_yield_to` refines l4v `complete_yield_to`**: if `y` yields to
an SC, its consumed time is reported (`set_consumed`, the message part by
`MsgOK`) and the yield-to pair is cut. -/
theorem complete_yield_to_refines {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hY : YieldRel T C (L.mem s) σ) {y : U64} (hy : y ∈ T)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, ar.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) (hmsg : MsgOK st N T C c) :
    schedcontext.complete_yield_to st ar s a y ⦃ r => r.2 = a ∧ ∃ σ',
      Fl4Spec.completeYieldTo (Z := Unit) y.bv σ = ({((), σ')}, False) ∧
      SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧
      YieldRel T C (L.mem r.1) σ' ∧ SFrame σ σ' ∧ L.mem r.1 (yieldA y) = 0#u64 ∧
      (∀ u ∈ T, u ≠ y → L.mem r.1 (yieldA u) = L.mem s (yieldA u)) ∧
      WritesIn st s r.1 (TFoot st T N C c s σ) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hT := hc.tcbs
  have hy0 : y ≠ 0#u64 := fun e => (hc.tcbs y hy).ne0 (by rw [e]; rfl)
  obtain ⟨xy, hky, eyt⟩ := hY.tcb y hy
  unfold schedcontext.complete_yield_to
  step as ⟨b, hb⟩
  simp only [hb, hy0, decide_false, Bool.false_eq_true, ↓reduceIte]
  step with obj.Tcb.yield_to.spec as ⟨i, hi⟩
  subst hi
  by_cases hi0 : L.mem s (yieldA y) = 0#u64
  · have : (L.mem s (yieldA y) != 0#u64) = false := by simp [hi0]
    simp only [this, Bool.false_eq_true, ↓reduceIte]
    refine (WP.spec_ok _).mpr ⟨rfl, σ, completeYieldTo_none hky (by rw [eyt, hi0, optRef_zero]), hS, hR, hN, hI, hY, SFrame.refl σ,
      hi0, fun _ _ _ => rfl, WritesIn.refl _ _⟩
  obtain ⟨p, hp⟩ : ∃ p, L.mem s (yieldA y) = p := ⟨_, rfl⟩
  rw [hp] at hi0 eyt ⊢
  have hb' : (p != 0#u64) = true := by simp [hi0]
  simp only [hb', ↓reduceIte]
  obtain ⟨hpC, ysc, nsc, hksc, eyf⟩ := hY.toSc y hy (by rw [hp]; exact hi0)
  rw [hp] at hpC hksc
  have hsw56 := sw_hdr hS hpC (K := 56#u64) (by simp) (by simp) (by decide)
  have hal56 : Aligned (scW p 56#u64) := by
    obtain ⟨x0, n0, -, hx0⟩ := hs.scs p hpC; exact (hx0.hdr (K := 56#u64) (by simp) (by simp)).1
  refine WP.spec_bind (set_consumed_refines s a σ hS hR hN hI hY hpC hy true hmax htu hmsg) ?_
  rintro s2 ⟨cv, σ1, σ2, hsp1, hrfk', -, hS2, hR2, hN2, hI2, hY2, hsf2, -, hw12, hk12⟩
  have hrfk := hrfk' rfl
  have hm2 : L.mem s2 (yieldA y) = p := (WritesIn.yield_keep hT hw12 y hy).trans hp
  -- `cancel_yield_to`
  unfold schedcontext.cancel_yield_to
  step as ⟨b2, hb2⟩
  simp only [hb2, hy0, decide_false, Bool.false_eq_true, ↓reduceIte]
  step with obj.Tcb.yield_to.spec as ⟨i2, hi2⟩
  rw [hm2] at hi2
  subst hi2
  simp only [hb', ↓reduceIte]
  obtain ⟨x2, hk2y, ey2⟩ := hY2.tcb y hy
  obtain ⟨-, y2, n2, hk2p, -⟩ := hY2.toSc y hy (by rw [hm2]; exact hi0)
  rw [hm2] at ey2 hk2p
  have hcan : (do
      let s1 ← obj.Sc.set_yield_from st i2 s2 0#u64
      obj.Tcb.set_yield_to st y s1 0#u64) ⦃ s4 =>
        s4 = L.wr (L.wr s2 (scYieldFromA i2) 0#u64) (yieldA y) 0#u64 ⦄ :=
    WP.spec_bind (obj.Sc.set_yield_from.spec s2 _ 0#u64) fun s3 h3 => h3 ▸ obj.Tcb.set_yield_to.spec _ y 0#u64
  refine WP.spec_bind hcan ?_
  rintro s4 rfl
  obtain ⟨hS3, hf3, hK3, hw3⟩ := hS2.set_sc_yf hpC hk2p 0#u64
  rw [optRef_zero] at hS3 hK3
  have hpy : i2.bv ≠ y.bv := fun e => by rw [e, hk2y] at hk2p; cases hk2p
  have hkay : (updSc σ2 i2.bv { y2 with scYieldFrom := none } n2).kheap y.bv = some (.tcb x2) := by
    simp [updK, Ne.symm hpy, hk2y]
  obtain ⟨hS4, hf4, hK4⟩ := hS3.set_yt hy hkay 0#u64
  rw [optRef_zero] at hS4 hK4
  have hm4 : ∀ u ∈ T, u ≠ y → L.mem (L.wr (L.wr s2 (scYieldFromA i2) 0#u64) (yieldA y) 0#u64) (yieldA u) =
      L.mem s2 (yieldA u) := by
    intro u hu hne
    rw [L.mem_wr_ne (yieldA_aligned hT hy) (yieldA_aligned hT hu)
      (fun e => hne (yieldA_inj hT hy hu (UScalar.eq_of_val_eq e.symm)))]
    exact WritesIn.yield_keep hT hw3 u hu
  have hmy : L.mem (L.wr (L.wr s2 (scYieldFromA i2) 0#u64) (yieldA y) 0#u64) (yieldA y) = 0#u64 :=
    L.mem_wr_same (yieldA_aligned hT hy)
  have hwy : WritesIn st s2 (L.wr (L.wr s2 (scYieldFromA i2) 0#u64) (yieldA y) 0#u64) (TFoot st T N C c s σ) :=
    ((writesIn_wr (st := st) (s := s2) (v := 0#u64)
        (show Aligned (scYieldFromA i2) by rw [scYieldFromA_eq]; exact hal56)).trans
      (writesIn_wr (st := st) (s := L.wr s2 (scYieldFromA i2) 0#u64) (v := 0#u64) (yieldA_aligned hT hy))).mono
      fun b hb => by
        rcases hb with rfl | rfl
        · exact Or.inl (KFoot.of_sw (by rw [scYieldFromA_eq]; exact hsw56))
        · exact Or.inr ⟨y, hy, rfl⟩
  refine (WP.spec_ok _).mpr ⟨rfl, _, ?_, hS4, (hR2.frame hS2.placed hf3 hK3).frame hS3.placed hf4 hK4,
    hN2.updSc.updTcb, (hI2.scFields (y' := { y2 with scYieldFrom := none }) hk2p rfl rfl rfl rfl).ytUpd hkay none,
    hY2.clear hy hm2 hi0 hk2y hk2p hm4 hmy,
    hsf2.trans ((SFrame.updSc (x' := { y2 with scYieldFrom := none }) hk2p rfl rfl).trans (SFrame.ytUpd hkay none)), hmy,
    fun u hu hne => (hm4 u hu hne).trans (WritesIn.yield_keep hT hw12 u hu),
    WritesIn.tfoot_add (WritesIn.tfoot_of_kfoot hk12) hwy⟩
  rw [completeYieldTo_some hky (by rw [eyt, optRef_ne hi0])]
  have hsc : Fl4Spec.setConsumed (Z := Unit) i2.bv y.bv σ = ({((), σ2)}, False) := by
    unfold Fl4Spec.setConsumed; rw [nd_bind_one hsp1]; exact hrfk
  rw [nd_bind_one hsc]
  exact cancelYieldTo_some hk2y (by rw [ey2, optRef_ne hi0]) hk2p hpy


/-- **`resume` is a no-op** when the SC's thread, if schedulable, has it
released. -/
theorem resume_noop {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hR : NtfnStateRel N T (L.mem s) σ) (hS : SchedRel st N T C c s σ)
    (hmb : sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    {sc : U64} (hsc : sc ∈ C) (hsc0 : sc ≠ 0#u64) {t : U64} (ht : t ∈ T)
    (htw : L.mem s (scW sc 24#u64) = t) (hts : L.mem s (scA t) = sc)
    {x : Fl4Spec.SchedContext} {n : Nat} (hk : σ.kheap sc.bv = some (.schedContext x n))
    (hrel : Fl4Spec.schedulable t.bv σ = true → released σ x) :
    schedcontext.resume st ar s a sc ⦃ r => r = (s, a) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x', n', hk', hx⟩ := hs.scs sc hsc
  rw [hk] at hk'; cases hk'
  have ht0 : t ≠ 0#u64 := fun e => (hc.tcbs t ht).ne0 (by rw [e]; rfl)
  have hne : x.scRefills ≠ [] := by rw [hx.refills]; exact refills_ne hx.wf
  have hsched := schedulable_eq hR hS ht
  rw [hts] at hsched
  unfold schedcontext.resume
  step as ⟨b, b_post⟩
  simp only [b_post, hsc0, decide_false, Bool.false_eq_true, ↓reduceIte]
  step as ⟨i, i_post⟩
  have hi : i = t := by rw [i_post, scTcbA_eq, htw]
  subst hi
  step as ⟨b1, b1_post⟩
  simp only [b1_post, ht0, decide_false, Bool.false_eq_true, ↓reduceIte]
  step with sched.is_schedulable.spec' as ⟨b2, b2_post⟩
  rw [hts, hsched] at b2_post
  subst b2_post
  by_cases hsb : Fl4Spec.schedulable i.bv σ = true
  · simp only [hsb, ↓reduceIte]
    obtain ⟨hr1, hr2⟩ := hrel hsb
    refine WP.spec_bind (ready_refines s σ hS hsc hk) ?_
    intro b3 hb3
    rw [getScRefillReady_eq hk hne] at hb3
    have eb3 := (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst hb3))).1
    have h3 : b3 = true := eb3.symm.trans hr1
    simp only [h3, ↓reduceIte]
    refine WP.spec_bind (sufficient_refines s a σ hS hsc hk 0#u64 hmb) ?_
    intro b4 hb4
    rw [getScRefillSufficient_eq hk hne] at hb4
    have eb4 := (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst hb4))).1
    have h4 : b4 = true := eb4.symm.trans hr2
    simp only [h4, ↓reduceIte]
    exact (WP.spec_ok _).mpr rfl
  · simp only [hsb, Bool.false_eq_true, ↓reduceIte]
    exact (WP.spec_ok _).mpr rfl


theorem SFrame.of_kheap {σ σ' : Fl4Spec.State Unit} (hk : σ'.kheap = σ.kheap) (hr : σ'.releaseQueue = σ.releaseQueue)
    (hc : σ'.curThread = σ.curThread) (ha : σ'.schedulerAction = σ.schedulerAction)
    (hi : σ'.idleThread = σ.idleThread) : SFrame σ σ' :=
  ⟨fun p x h => ⟨x, by rw [hk]; exact h, rfl, rfl, rfl, rfl⟩, fun p x n h => ⟨x, by rw [hk]; exact h, rfl, rfl⟩, hr,
    hc, ha, hi⟩

/-- **`dequeue`** with the relations and the yield-to relation. -/
theorem dequeue_rels {N T C : Set U64} {c : U64} (s : S) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hY : YieldRel T C (L.mem s) σ) {t : U64} (ht : t ∈ T) :
    sched.dequeue st s t ⦃ s' => ∃ σ', Fl4Spec.tcbSchedAction (Z := Unit) Fl4Spec.tcbSchedDequeue t.bv σ =
      ({((), σ')}, False) ∧ SchedRel st N T C c s' σ' ∧ NtfnStateRel N T (L.mem s') σ' ∧ NSC N C σ' ∧ Inv σ' ∧
      YieldRel T C (L.mem s') σ' ∧ σ'.kheap = σ.kheap ∧ σ'.releaseQueue = σ.releaseQueue ∧
      SFrame σ σ' ∧ WritesIn st s s' (SFoot st T c s) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨xt, hkt, -⟩ := hs.tcb t ht
  refine WP.spec_mono (WP.spec_and (WP.spec_and (dequeue_refines s σ hS t ht) (dequeue_yw hS ht))
    (dequeue_sfoot hS ht)) ?_
  rintro s' ⟨⟨⟨σ', he, hk, hr, hf, hS'⟩, hw⟩, hwf⟩
  have hσ' := the_result (tcbSchedAction_gen hkt Fl4Spec.tcbSchedDequeue) he
  refine ⟨σ', he, hS', hR.frame hS.placed hf (KView.of_kheap hk), fun n hn x p hx hp => hN n hn x p (hk ▸ hx) hp,
    ?_, hY.frame (WritesIn.yield_keep hc.tcbs hw) (YKeep.of_kheap hk), hk, hr,
    SFrame.of_kheap hk hr (by rw [hσ']; rfl) (by rw [hσ']; rfl) (by rw [hσ']; rfl), hwf⟩
  rw [hσ']; exact hI.qchange (qchange_dequeue hkt)

/-- **`enqueue`** of a schedulable thread, with the relations. -/
theorem enqueue_rels {N T C : Set U64} {c : U64} (s : S) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hY : YieldRel T C (L.mem s) σ) {t : U64} (ht : t ∈ T) (hsch : Fl4Spec.schedulable t.bv σ = true) :
    sched.enqueue st s t ⦃ s' => ∃ σ', Fl4Spec.tcbSchedAction (Z := Unit) Fl4Spec.tcbSchedEnqueue t.bv σ =
      ({((), σ')}, False) ∧ SchedRel st N T C c s' σ' ∧ NtfnStateRel N T (L.mem s') σ' ∧ NSC N C σ' ∧ Inv σ' ∧
      YieldRel T C (L.mem s') σ' ∧ σ'.kheap = σ.kheap ∧ σ'.releaseQueue = σ.releaseQueue ∧
      SFrame σ σ' ∧ WritesIn st s s' (SFoot st T c s) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨xt, hkt, -⟩ := hs.tcb t ht
  have hrb : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by
    have hd := schedulable_eq hR hS ht
    rw [hsch] at hd
    exact (of_decide_eq_true hd).2.2.2
  refine WP.spec_mono (WP.spec_and (WP.spec_and (enqueue_refines s σ hS t ht fun _ => hrb) (enqueue_yw hS ht))
    (enqueue_sfoot hS ht)) ?_
  rintro s' ⟨⟨⟨σ', he, hk, hr, hf, hS'⟩, hw⟩, hwf⟩
  have hσ' := the_result (tcbSchedAction_gen hkt Fl4Spec.tcbSchedEnqueue) he
  refine ⟨σ', he, hS', hR.frame hS.placed hf (KView.of_kheap hk), fun n hn x p hx hp => hN n hn x p (hk ▸ hx) hp,
    ?_, hY.frame (WritesIn.yield_keep hc.tcbs hw) (YKeep.of_kheap hk), hk, hr,
    SFrame.of_kheap hk hr (by rw [hσ']; rfl) (by rw [hσ']; rfl) (by rw [hσ']; rfl), hwf⟩
  rw [hσ']; exact hI.qchange (qchange_enqueue hkt hsch)

/-- **`reschedule_required`** with the relations. -/
theorem reschedule_rels {N T C : Set U64} {c : U64} (s : S) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hY : YieldRel T C (L.mem s) σ) :
    sched.reschedule_required st s ⦃ s' => ∃ σ', Fl4Spec.rescheduleRequired (Z := Unit) σ = ({((), σ')}, False) ∧
      SchedRel st N T C c s' σ' ∧ NtfnStateRel N T (L.mem s') σ' ∧ NSC N C σ' ∧ Inv σ' ∧
      YieldRel T C (L.mem s') σ' ∧ σ'.schedulerAction = .chooseNewThread ∧ σ'.kheap = σ.kheap ∧
      σ'.releaseQueue = σ.releaseQueue ∧ σ'.idleThread = σ.idleThread ∧ WritesIn st s s' (SFoot st T c s) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  refine WP.spec_mono (WP.spec_and (WP.spec_and (reschedule_required_refines s σ hR hS hI.actReady)
    (reschedule_required_yw hS)) (reschedule_required_sfoot hS)) ?_
  rintro s' ⟨⟨⟨σ', he, hk, hr, hf, hS'⟩, hw⟩, hwf⟩
  obtain ⟨σ1, he1, hq1⟩ := rescheduleRequired_qchange hI.actReady
  have hσ' := the_result he1 he
  obtain ⟨g1, g2, g3, g4⟩ := rescheduleRequired_act hI.actReady he
  refine ⟨σ', he, hS', hR.frame hS.placed hf (KView.of_kheap hk), fun n hn x p hx hp => hN n hn x p (hk ▸ hx) hp,
    ?_, hY.frame (WritesIn.yield_keep hc.tcbs hw) (YKeep.of_kheap hk), g1, g2, g3, g4, hwf⟩
  rw [hσ']; exact hI.qchange hq1

/-- **`yield_switches` refines `sched_context_yield_to`'s `return_now`
computation** (the negation), for an SC bound to `t`, with no yielder, the
current thread `ct` schedulable and yielding to nothing. On one core the
SC's core is the current one. -/
theorem yield_switches_refines {N T C : Set U64} {c : U64} (s : S) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hY : YieldRel T C (L.mem s) σ) (hC0 : ∀ q ∈ C, q ≠ 0#u64)
    {sc : U64} (hsc : sc ∈ C) {x : Fl4Spec.SchedContext} {n : Nat} (hk : σ.kheap sc.bv = some (.schedContext x n))
    (hyf : x.scYieldFrom = none) {t : U64} (ht : t ∈ T) (htc : x.scTcb = some t.bv)
    {ct : U64} (hct : ct ∈ T) (hcur : σ.curThread = ct.bv) (hyc : L.mem s (yieldA ct) = 0#u64)
    (hcs : Fl4Spec.schedulable ct.bv σ = true) :
    schedcontext.yield_switches st s sc ct ⦃ r => ∃ σ', yieldSwitch sc.bv σ = ({(!r.1, σ')}, False) ∧
      SchedRel st N T C c r.2 σ' ∧ NtfnStateRel N T (L.mem r.2) σ' ∧ NSC N C σ' ∧ Inv σ' ∧
      YieldRel T C (L.mem r.2) σ' ∧
      (r.1 = false → SFrame σ σ') ∧ (ActIdle σ → ActIdle σ') ∧ WritesIn st s r.2 (TFoot st T N C c s σ) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hT := hc.tcbs
  obtain ⟨x', n', hk', hx⟩ := hs.scs sc hsc
  rw [hk] at hk'; cases hk'
  have hsw56 := sw_hdr hS hsc (K := 56#u64) (by simp) (by simp) (by decide)
  have hal56 := (hx.hdr (K := 56#u64) (by simp) (by simp)).1
  obtain ⟨xt, hkt, -, -, -, hpt⟩ := hs.tcb t ht
  obtain ⟨xc, hkc, -, -, -, hpc⟩ := hs.tcb ct hct
  have htw := word24_of hS hsc hk htc
  have hsc0 := hC0 sc hsc
  have hct0 : ct ≠ 0#u64 := fun e => (hc.tcbs ct hct).ne0 (by rw [e]; rfl)
  have hpre : ∀ (k : Fl4Spec.ObjRef → Bool → Fl4Spec.SMonad Unit Bool),
      (Fl4Spec.getScObjRef Fl4Spec.SchedContext.scTcb sc.bv >>= fun scTcbOpt =>
        Fl4Spec.NonDet.assertOpt scTcbOpt >>= fun tcbPtr =>
          Fl4Spec.NonDet.gets (Fl4Spec.schedulable tcbPtr) >>= fun b => k tcbPtr b) σ =
        k t.bv (Fl4Spec.schedulable t.bv σ) σ := by
    intro k
    rw [nd_bind_one (getScObjRef_eq hk _), htc,
      nd_bind_one (show Fl4Spec.NonDet.assertOpt (σ := Fl4Spec.State Unit) (some t.bv) σ = ({(t.bv, σ)}, False)
        from rfl), nd_gets_bind]
  unfold schedcontext.yield_switches
  step with obj.Sc.tcb.spec as ⟨i, hi⟩
  rw [scTcbA_eq, htw] at hi
  subst hi
  step with sched.is_schedulable.spec' as ⟨b, hb⟩
  rw [schedulable_eq hR hS ht] at hb
  subst hb
  by_cases hsb : Fl4Spec.schedulable i.bv σ = true
  swap
  · simp only [hsb, Bool.false_eq_true, ↓reduceIte]
    refine (WP.spec_ok _).mpr ⟨σ, ?_, hS, hR, hN, hI, hY, fun _ => SFrame.refl σ, id, WritesIn.refl _ _⟩
    unfold yieldSwitch
    rw [hpre]
    simp only [hsb, Bool.false_eq_true, ↓reduceIte]; rfl
  simp only [hsb, ↓reduceIte]
  step with obj.Sc.cpu.spec as ⟨i1, hi1⟩
  have hi1' : i1 = c := by rw [hi1, scCoreA_eq]; exact hS.core sc hsc
  subst hi1'
  step with LawfulStore.cur_cpu_spec as ⟨i2, hi2⟩
  rw [hc.cur] at hi2
  subst hi2
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  step with obj.Tcb.prio.spec as ⟨i3, hi3⟩
  step with obj.Tcb.prio.spec as ⟨i4, hi4⟩
  subst hi3 hi4
  by_cases hlt : L.mem s (prioA i) < L.mem s (prioA ct)
  · simp only [hlt, ↓reduceIte]
    refine WP.spec_bind (dequeue_rels s σ hS hR hN hI hY ht) ?_
    rintro s1 ⟨σ1, he1, hS1, hR1, hN1, hI1, hY1, hk1, hr1, hf1, hw1⟩
    have hsb1 : Fl4Spec.schedulable i.bv σ1 = true := by rw [schedulable_heap hk1 hr1]; exact hsb
    refine WP.spec_bind (enqueue_rels s1 σ1 hS1 hR1 hN1 hI1 hY1 ht hsb1) ?_
    rintro s2 ⟨σ2, he2, hS2, hR2, hN2, hI2, hY2, hk2, hr2, hf2, hw2⟩
    refine (WP.spec_ok _).mpr ⟨σ2, ?_, hS2, hR2, hN2, hI2, hY2, fun _ => hf1.trans hf2,
      fun h => ActIdle.sframe h (hf1.trans hf2), WritesIn.tfoot_sfoot (WritesIn.tfoot_of_sfoot hw1) hw2⟩
    unfold yieldSwitch
    rw [hpre]
    simp only [hsb, ↓reduceIte]
    rw [nd_gets_bind, hcur, nd_bind_one (threadGet_eq _ hkt), nd_bind_one (threadGet_eq _ hkc),
      ite_eq_left ((prio_lt_iff hpt hpc).1 hlt), nd_bind_one he1, nd_bind_one he2]; rfl
  · simp only [hlt, ↓reduceIte]
    refine WP.spec_bind (obj.Tcb.set_yield_to.spec s ct sc) ?_
    rintro s1 rfl
    obtain ⟨hS1, hf1, hK1⟩ := hS.set_yt hct hkc sc
    rw [optRef_ne hsc0] at hS1 hK1
    have hpc' : sc.bv ≠ ct.bv := fun e => by rw [e, hkc] at hk; cases hk
    have hka : (updK σ ct.bv (.tcb { xc with tcbYieldTo := some sc.bv })).kheap sc.bv =
        some (.schedContext x n) := by simp [updK, hpc', hk]
    refine WP.spec_bind (obj.Sc.set_yield_from.spec _ sc ct) ?_
    rintro s2 rfl
    obtain ⟨hS2, hf2, hK2, hw2⟩ := hS1.set_sc_yf hsc hka ct
    rw [optRef_ne hct0] at hS2 hK2
    have hR2 := (hR.frame hS.placed hf1 hK1).frame hS1.placed hf2 hK2
    have hN2 := (hN.updTcb (t := ct.bv) (x := { xc with tcbYieldTo := some sc.bv })).updSc
      (p := sc.bv) (y := { x with scYieldFrom := some ct.bv }) (n := n)
    have hI2 := (hI.ytUpd hkc (some sc.bv)).scFields (y' := { x with scYieldFrom := some ct.bv }) hka rfl rfl rfl rfl
    have hY2 := hY.pair hC0 hct hsc hyc hkc hk hyf (m' := L.mem (L.wr (L.wr s (yieldA ct) sc) (scYieldFromA sc) ct))
      (fun u hu hne => by
        rw [WritesIn.yield_keep hT hw2 u hu, L.mem_wr_ne (yieldA_aligned hT hct) (yieldA_aligned hT hu)
          (fun e => hne (yieldA_inj hT hct hu (UScalar.eq_of_val_eq e).symm))])
      (by rw [WritesIn.yield_keep hT hw2 ct hct]; exact L.mem_wr_same (yieldA_aligned hT hct))
    have hsf := (SFrame.ytUpd hkc (some sc.bv)).trans
      (SFrame.updSc (x' := { x with scYieldFrom := some ct.bv }) hka rfl rfl)
    refine WP.spec_bind (dequeue_rels _ _ hS2 hR2 hN2 hI2 hY2 ht) ?_
    rintro s3 ⟨σ3, he3, hS3, hR3, hN3, hI3, hY3, hk3, hr3, hf3, hw3⟩
    have hcs3 : Fl4Spec.schedulable ct.bv σ3 = true := by rw [schedulable_heap hk3 hr3]; exact hsf.schedulable hcs
    refine WP.spec_bind (enqueue_rels s3 σ3 hS3 hR3 hN3 hI3 hY3 hct hcs3) ?_
    rintro s4 ⟨σ4, he4, hS4, hR4, hN4, hI4, hY4, hk4, hr4, hf4, hw4⟩
    have hsb4 : Fl4Spec.schedulable i.bv σ4 = true := by
      rw [schedulable_heap hk4 hr4, schedulable_heap hk3 hr3]; exact hsf.schedulable hsb
    refine WP.spec_bind (enqueue_rels s4 σ4 hS4 hR4 hN4 hI4 hY4 ht hsb4) ?_
    rintro s5 ⟨σ5, he5, hS5, hR5, hN5, hI5, hY5, -, -, hf5, hw5⟩
    refine WP.spec_bind (reschedule_rels s5 σ5 hS5 hR5 hN5 hI5 hY5) ?_
    rintro s6 ⟨σ6, he6, hS6, hR6, hN6, hI6, hY6, ha6, hk6, hr6, hi6, hw6⟩
    have hw2 : WritesIn st s (L.wr (L.wr s (yieldA ct) sc) (scYieldFromA sc) ct) (TFoot st T N C i2 s σ) :=
      ((writesIn_wr (st := st) (s := s) (v := sc) (yieldA_aligned hT hct)).trans
        (writesIn_wr (st := st) (s := L.wr s (yieldA ct) sc) (v := ct)
          (show Aligned (scYieldFromA sc) by rw [scYieldFromA_eq]; exact hal56))).mono fun b hb => by
        rcases hb with rfl | rfl
        · exact Or.inr ⟨ct, hct, rfl⟩
        · exact Or.inl (KFoot.of_sw (by rw [scYieldFromA_eq]; exact hsw56))
    refine (WP.spec_ok _).mpr ⟨σ6, ?_, hS6, hR6, hN6, hI6, hY6, fun h => absurd h (by simp), fun h =>
      ActIdle.of_noswitch ((ActIdle.sframe h (((hsf.trans hf3).trans hf4).trans hf5)).2.of hi6 (by rw [hk6])
        (by rw [hr6]; exact id)) (fun t e => by rw [ha6] at e; cases e),
      WritesIn.tfoot_sfoot (WritesIn.tfoot_sfoot (WritesIn.tfoot_sfoot (WritesIn.tfoot_sfoot hw2 hw3) hw4) hw5) hw6⟩
    unfold yieldSwitch
    rw [hpre]
    simp only [hsb, ↓reduceIte]
    rw [nd_gets_bind, hcur, nd_bind_one (threadGet_eq _ hkt), nd_bind_one (threadGet_eq _ hkc),
      ite_eq_right (fun h => hlt ((prio_lt_iff hpt hpc).2 h))]
    show (Fl4Spec.threadSet _ ct.bv >>= _) σ = _
    rw [nd_bind_one (threadSet_eq _ hkc)]
    show (Fl4Spec.updateSchedContext sc.bv _ >>= _) (updK σ ct.bv (.tcb { xc with tcbYieldTo := some sc.bv })) = _
    rw [nd_bind_one (updateSchedContext_eq hka _)]
    show (Fl4Spec.tcbSchedAction (Z := Unit) Fl4Spec.tcbSchedDequeue i.bv >>= _)
      (updSc (updK σ ct.bv (.tcb { xc with tcbYieldTo := some sc.bv })) sc.bv
      { x with scYieldFrom := some ct.bv } n) = _
    rw [nd_bind_one he3, nd_bind_one he4, nd_bind_one he5,
      nd_bind_one he6]; rfl


theorem obj.Sc.yield_from.spec' (s : S) (c : obj.Sc) :
    obj.Sc.yield_from st c s ⦃ v => v = L.mem s (scYieldFromA c) ⦄ := by
  unfold obj.Sc.yield_from; step*; simp_all [scYieldFromA]

theorem nd_when_false_y {σ' : Type} {P : Prop} [Decidable P] (h : ¬ P) (m : Fl4Spec.NonDet σ' Unit) :
    Fl4Spec.NonDet.when P m = pure () := by
  unfold Fl4Spec.NonDet.when; rw [ite_eq_right h]; rfl

theorem optRef_eq_none {v : U64} (h : optRef v = none) : v = 0#u64 := by
  unfold optRef at h; split_ifs at h with h0
  · exact h0

/-- **SchedContext `YieldTo` refines l4v `sched_context_yield_to`**, for an SC
bound both ways to `t`, from the current thread `ct` (schedulable, yielding
to nothing): the SC's yielder (if any) completes its yield, `resume` is a
no-op (the invariant has a schedulable bound thread's SC released), and
either `ct` yields to `t` (the spec returns no data) or the call returns at
once with the consumed time: then FL4 writes the reply (if `call`, by
`MsgOK`) and sets `ct` running, as l4v's `handle_invocation` does after
`reply_from_kernel`. -/
theorem yield_to_refines {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hY : YieldRel T C (L.mem s) σ) (hC0 : ∀ q ∈ C, q ≠ 0#u64)
    {sc : U64} (hsc : sc ∈ C) {x : Fl4Spec.SchedContext} {n : Nat} (hk : σ.kheap sc.bv = some (.schedContext x n))
    {t : U64} (ht : t ∈ T) (htc : x.scTcb = some t.bv) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hxt : xt.tcbSchedContext = some sc.bv)
    {ct : U64} (hct : ct ∈ T) (hcur : σ.curThread = ct.bv) {xc : Fl4Spec.Tcb} (hkc : σ.kheap ct.bv = some (.tcb xc))
    (hyc : xc.tcbYieldTo = none) (hcs : Fl4Spec.schedulable ct.bv σ = true) (hAI : ActIdle σ) (call : Bool)
    (hmb : sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, ar.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) (hmsg : MsgOK st N T C c) :
    schedcontext.yield_to st ar s a sc call ⦃ r => r.2 = a ∧
      ∃ (data : List Fl4Spec.Data) (σ1 σ2 : Fl4Spec.State Unit),
      Fl4Spec.schedContextYieldTo (Z := Unit) sc.bv σ = ({(data, σ1)}, False) ∧
      ((data = [] ∧ σ2 = σ1) ∨
        (do
          Fl4Spec.NonDet.when (call = true) (Fl4Spec.replyFromKernel (Z := Unit) ct.bv (0, data))
          Fl4Spec.setThreadState (Z := Unit) ct.bv .running : Fl4Spec.SMonad Unit Unit) σ1 = ({((), σ2)}, False)) ∧
      SchedRel st N T C c r.1 σ2 ∧ NtfnStateRel N T (L.mem r.1) σ2 ∧ NSC N C σ2 ∧ Inv σ2 ∧
      YieldRel T C (L.mem r.1) σ2 ∧ ActIdle σ2 ∧ WritesIn st s r.1 (TFoot st T N C c s σ) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hT := hc.tcbs
  obtain ⟨x0, n0, hk0, hx⟩ := hs.scs sc hsc
  rw [hk] at hk0; cases hk0
  have hsc0 := hC0 sc hsc
  obtain ⟨xc0, hkc0, ehc⟩ := hY.tcb ct hct
  rw [hkc] at hkc0; cases hkc0
  have hyc0 : L.mem s (yieldA ct) = 0#u64 := optRef_eq_none (ehc ▸ hyc)
  have hyfw : x.scYieldFrom = optRef (L.mem s (scYieldFromA sc)) := by rw [scYieldFromA_eq]; exact hx.yieldFrom
  unfold schedcontext.yield_to
  step with obj.Sc.yield_from.spec' as ⟨yf, hyf⟩
  subst hyf
  step with obj.Tcb.is_null.spec as ⟨b, hb⟩
  subst hb
  refine WP.spec_bind (show _ ⦃ r => r.2 = a ∧ ∃ σc, (Fl4Spec.NonDet.when (x.scYieldFrom ≠ none) (do
        Fl4Spec.completeYieldTo (Z := Unit) (Fl4Spec.the x.scYieldFrom)
        let o ← Fl4Spec.getScObjRef (Z := Unit) Fl4Spec.SchedContext.scYieldFrom sc.bv
        Fl4Spec.NonDet.assert (o = none)) : Fl4Spec.SMonad Unit Unit) σ = ({((), σc)}, False) ∧
      SchedRel st N T C c r.1 σc ∧ NtfnStateRel N T (L.mem r.1) σc ∧ NSC N C σc ∧ Inv σc ∧
      YieldRel T C (L.mem r.1) σc ∧ SFrame σ σc ∧ L.mem r.1 (yieldA ct) = 0#u64 ∧
      (∀ x1, σc.kheap sc.bv = some (.schedContext x1 n) → x1.scYieldFrom = none) ∧
      WritesIn st s r.1 (TFoot st T N C c s σ) ⦄ from ?_) ?_
  · by_cases h0 : L.mem s (scYieldFromA sc) = 0#u64
    · simp only [h0, decide_true, ↓reduceIte]
      refine (WP.spec_ok _).mpr ⟨rfl, σ, ?_, hS, hR, hN, hI, hY, SFrame.refl σ, hyc0, fun x1 h1 => ?_, WritesIn.refl _ _⟩
      · rw [nd_when_false_y (by rw [hyfw, h0, optRef_zero]; simp)]; rfl
      · rw [hk] at h1; cases h1; rw [hyfw, h0, optRef_zero]
    · simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte]
      have hxf : x.scYieldFrom = some (L.mem s (scYieldFromA sc)).bv := by rw [hyfw, optRef_ne h0]
      obtain ⟨u, hu, hub, hum⟩ := hY.frm sc hsc x n hk _ hxf
      have hue := eq_of_bv hub
      rw [← hue] at hxf ⊢
      have hcu : ct ≠ u := fun e => by rw [e, hum] at hyc0; exact hsc0 hyc0
      refine WP.spec_mono (complete_yield_to_refines s a σ hS hR hN hI hY hu hmax htu hmsg) ?_
      rintro ⟨s1, a1⟩ ⟨ha1, σc, hcy, hS1, hR1, hN1, hI1, hY1, hsf1, hmu, hmo, hwc⟩
      have hyf1 : ∀ x1, σc.kheap sc.bv = some (.schedContext x1 n) → x1.scYieldFrom = none := by
        intro x1 h1
        cases e : x1.scYieldFrom with
        | none => rfl
        | some q =>
          obtain ⟨v, hv, -, hvm⟩ := hY1.frm sc hsc x1 n h1 q e
          by_cases hvu : v = u
          · subst hvu; rw [hmu] at hvm; exact absurd hvm.symm hsc0
          · rw [hmo v hv hvu] at hvm
            obtain ⟨-, z, k, hz, ez⟩ := hY.toSc v hv (by rw [hvm]; exact hsc0)
            rw [hvm, hk] at hz; cases hz
            rw [hxf] at ez
            exact absurd (eq_of_bv (Option.some.inj ez)).symm hvu
      refine ⟨ha1, σc, ?_, hS1, hR1, hN1, hI1, hY1, hsf1, by rw [hmo ct hct hcu]; exact hyc0, hyf1, hwc⟩
      obtain ⟨x1, hk1, -, -⟩ := hsf1.sc _ x n hk
      unfold Fl4Spec.NonDet.when
      rw [ite_eq_left (by rw [hxf]; simp)]
      rw [hxf]
      show (Fl4Spec.completeYieldTo u.bv >>= _) σ = _
      rw [nd_bind_one hcy, nd_bind_one (getScObjRef_eq hk1 _), hyf1 x1 hk1]
      show (({x | (none : Option Fl4Spec.ObjRef) = none ∧ x = ((), σc)}, ¬ (none : Option Fl4Spec.ObjRef) = none) :
        Set (Unit × Fl4Spec.State Unit) × Prop) = _
      simp
  rintro ⟨s1, a1⟩ ⟨ha1, σc, hw1, hS1, hR1, hN1, hI1, hY1, hsf1, hyc1, hyf1, hwf1⟩
  have hzc : SzKeepC C σ σc := SzKeepC.of_fwd hS fun p x n hp => by
    obtain ⟨x', h, -⟩ := hsf1.sc p x n hp; exact ⟨x', h⟩
  simp only at ha1 hS1 hR1 hN1 hI1 hY1 hyc1
  subst a1
  obtain ⟨Q1, R1, hc1, hs1⟩ := hS1.lists
  -- the spec objects after the yielder's completion
  obtain ⟨x1, hk1, htc1', -⟩ := hsf1.sc _ x n hk
  have htc1 : x1.scTcb = some t.bv := htc1'.trans htc
  obtain ⟨xt1, hkt1, -, hxt1', -, -⟩ := hsf1.tcb _ xt hkt
  have hxt1 : xt1.tcbSchedContext = some sc.bv := hxt1'.trans hxt
  have hcur1 : σc.curThread = ct.bv := hsf1.cur.trans hcur
  have hcs1 : Fl4Spec.schedulable ct.bv σc = true := hsf1.schedulable hcs
  obtain ⟨hrun1, hrel1⟩ := hI1.yieldRes hk1 hkt1 hxt1
  have hne1 := hI1.ne _ _ _ hk1
  have hres : Fl4Spec.schedContextResume (Z := Unit) sc.bv σc = ({((), σc)}, False) :=
    resume_spec_noop hk1 htc1 hkt1 hne1 hrun1 hrel1
  refine WP.spec_bind (resume_noop s1 a σc hR1 hS1 hmb hsc hsc0 ht (word24_of hS1 hsc hk1 htc1)
    (scA_of hS1 ht hkt1 hxt1) hk1 hrel1) ?_
  rintro r rfl
  step with sched.cur_thread.spec' as ⟨ct', hct'⟩
  have hct'' : ct' = ct := by
    rw [hct', hc1.cur]; exact eq_of_bv (hs1.curThread.symm.trans hcur1)
  subst hct''
  refine WP.spec_bind (yield_switches_refines s1 σc hS1 hR1 hN1 hI1 hY1 hC0 hsc hk1 (hyf1 x1 hk1) ht htc1 hct hcur1
    hyc1 hcs1) ?_
  rintro ⟨b1, s3⟩ ⟨σ3, hsw, hS3, hR3, hN3, hI3, hY3, hk3, hAI3', hws3⟩
  have hw3 := WritesIn.tfoot_trans hwf1 hzc hws3
  have hAI3 := hAI3' (ActIdle.sframe hAI hsf1)
  have hsw' := hsw
  unfold yieldSwitch at hsw'
  have hpre : Fl4Spec.schedContextYieldTo (Z := Unit) sc.bv σ =
      (if (!b1) = true then Fl4Spec.returnConsumed (Z := Unit) sc.bv else pure []) σ3 := by
    unfold Fl4Spec.schedContextYieldTo
    rw [nd_bind_one (getScObjRef_eq hk _), nd_bind_one hw1, nd_bind_one hres, nd_bind_one hsw']
  generalize Fl4Spec.schedContextYieldTo (Z := Unit) sc.bv σ = RES at hpre ⊢
  cases b1
  · -- the call returns at once
    show (if false = true then _ else _) ⦃ _ ⦄
    rw [ite_eq_right (fun h => Bool.false_ne_true h)]
    have hsf3 := hk3 rfl
    refine WP.spec_bind (set_consumed_refines s3 a σ3 hS3 hR3 hN3 hI3 hY3 hsc hct call hmax htu hmsg) ?_
    rintro s4 ⟨cv, σa, σb, hspc, hrt, hrf, hS4, hR4, hN4, hI4, hY4, hsf4, -, -, hwk4⟩
    have hz3 : SzKeepC C σ σ3 := SzKeepC.of_fwd hS fun p x n hp => by
      obtain ⟨x', h, -⟩ := (hsf1.trans hsf3).sc p x n hp; exact ⟨x', h⟩
    have hw4 := WritesIn.tfoot_trans hw3 hz3 (WritesIn.tfoot_of_kfoot hwk4)
    obtain ⟨xc4, hkc4, hst4, -, -, -⟩ := (hsf1.trans (hsf3.trans hsf4)).tcb _ xc hkc
    have hrun : Fl4Spec.runnable xc.tcbState = true := by
      obtain ⟨xq, -, -, -, hq1, -, hq3, -⟩ := schedulable_inv hcs
      rw [hkc] at hq1; cases hq1; exact hq3
    have hrun4 : Fl4Spec.runnable xc4.tcbState = true := by rw [hst4]; exact hrun
    refine WP.spec_bind (WP.spec_and (WP.spec_and (set_thread_state_refines s4 σb hR4 hS4 hct hkc4
      (not_in_ntfnQueue hR4 hct hkc4 hrun4) sched.TS_RUNNING .running (by rw [tsVals.1]; rfl)
      (fun n h => by cases h)) (set_thread_state_yw hS4 hct _)) (set_thread_state_sfoot hS4 hct _)) ?_
    rintro s5 ⟨⟨⟨σ5, he5, hR5, hS5⟩, hw5⟩, hwf5⟩
    have hσ5 := the_result (Fl4Proofs.P3.Notif.setThreadState_eq .running hkc4) he5
    refine (WP.spec_ok _).mpr ⟨rfl, Fl4Spec.wordsFromTime cv.bv, σa, σ5, ?_, Or.inr ?_, hS5, hR5, ?_, ?_, ?_,
      by rw [hσ5]; exact ActIdle.ofSts (ActIdle.updState (ActIdle.sframe hAI3 hsf4) hkc4 hrun4 .running rfl) _,
      WritesIn.tfoot_sfoot hw4 hwf5⟩
    · rw [hpre]
      show (Fl4Spec.returnConsumed (Z := Unit) sc.bv) σ3 = _
      unfold Fl4Spec.returnConsumed
      rw [nd_bind_one hspc]; rfl
    · cases call
      · rw [nd_when_false_y (by decide), nd_pure_bind', ← hrf rfl]; exact he5
      · unfold Fl4Spec.NonDet.when
        rw [ite_eq_left rfl, nd_bind_one (hrt rfl)]; exact he5
    · rw [hσ5]; unfold Fl4Proofs.P3.Notif.stsAct; split <;> exact hN4.updTcb
    · rw [hσ5]; exact hI4.setRunnable hkc4 hrun4 rfl
    · exact hY4.frame (WritesIn.yield_keep hT hw5) (by rw [hσ5]; exact (YKeep.updTcb (x' := { xc4 with tcbState := .running }) hkc4 rfl).trans (YKeep.stsAct _))
  · show (if true = true then _ else _) ⦃ _ ⦄
    rw [ite_eq_left rfl]
    exact (WP.spec_ok _).mpr ⟨rfl, [], σ3, σ3, by rw [hpre]; rfl, Or.inl ⟨rfl, rfl⟩, hS3, hR3, hN3, hI3, hY3, hAI3, hw3⟩


theorem stsAct_cur' {σ : Fl4Spec.State Unit} {t : Fl4Spec.ObjRef} :
    (Fl4Proofs.P3.Notif.stsAct σ t).curThread = σ.curThread := by
  unfold Fl4Proofs.P3.Notif.stsAct; split <;> rfl

theorem stsAct_rel' {σ : Fl4Spec.State Unit} {t : Fl4Spec.ObjRef} :
    (Fl4Proofs.P3.Notif.stsAct σ t).releaseQueue = σ.releaseQueue := by
  unfold Fl4Proofs.P3.Notif.stsAct; split <;> rfl

/-- `set_thread_state` of a runnable `ct` to a runnable state, with the
relations and the yield-to relation. -/
theorem set_runnable_rels {N T C : Set U64} {c : U64} (s : S) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hY : YieldRel T C (L.mem s) σ) {ct : U64} (hct : ct ∈ T) {xc : Fl4Spec.Tcb}
    (hkc : σ.kheap ct.bv = some (.tcb xc)) (hrun : Fl4Spec.runnable xc.tcbState = true)
    (v : U64) (ts : Fl4Spec.ThreadState) (hv : v.val = tsCode ts) (hts : Fl4Spec.runnable ts = true) :
    sched.set_thread_state st s ct v ⦃ s' => ∃ σ', Fl4Spec.setThreadState (Z := Unit) ct.bv ts σ = ({((), σ')}, False) ∧
      σ' = Fl4Proofs.P3.Notif.stsAct (updK σ ct.bv (.tcb { xc with tcbState := ts })) ct.bv ∧
      SchedRel st N T C c s' σ' ∧ NtfnStateRel N T (L.mem s') σ' ∧ NSC N C σ' ∧ Inv σ' ∧
      YieldRel T C (L.mem s') σ' ∧ (ActIdle σ → ActIdle σ') ∧ WritesIn st s s' (SFoot st T c s) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hnb : ∀ n, ts ≠ .blockedOnNotification n := fun n h => by rw [h] at hts; cases hts
  refine WP.spec_mono (WP.spec_and (WP.spec_and (set_thread_state_refines s σ hR hS hct hkc
    (not_in_ntfnQueue hR hct hkc hrun) v ts hv hnb) (set_thread_state_yw hS hct v)) (set_thread_state_sfoot hS hct v)) ?_
  rintro s' ⟨⟨⟨σ', he, hR', hS'⟩, hw⟩, hwf⟩
  have hσ' := the_result (Fl4Proofs.P3.Notif.setThreadState_eq ts hkc) he
  refine ⟨σ', he, hσ', hS', hR', ?_, ?_, ?_, fun h => by rw [hσ']; exact ActIdle.ofSts (ActIdle.updState h hkc hrun ts hts) _,
    hwf⟩
  · rw [hσ']; unfold Fl4Proofs.P3.Notif.stsAct; split <;> exact hN.updTcb
  · rw [hσ']; exact hI.setRunnable hkc hrun hts
  · exact hY.frame (WritesIn.yield_keep hc.tcbs hw)
      (by rw [hσ']; exact (YKeep.updTcb (x' := { xc with tcbState := ts }) hkc rfl).trans (YKeep.stsAct _))

/-- **SchedContext `Consumed`** (the decoder's branch: restart, `set_consumed`,
running) refines l4v's `return_consumed` between `handle_invocation`'s
restart and its reply (`reply_from_kernel` if `call`, by `MsgOK`) and
`set_thread_state Running`. -/
theorem sc_consumed_refines {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hY : YieldRel T C (L.mem s) σ) {sc : U64} (hsc : sc ∈ C) {ct : U64} (hct : ct ∈ T) {xc : Fl4Spec.Tcb}
    (hkc : σ.kheap ct.bv = some (.tcb xc)) (hrun : Fl4Spec.runnable xc.tcbState = true) (hAI : ActIdle σ)
    (call : Bool) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, ar.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) (hmsg : MsgOK st N T C c) :
    (do
      let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
      let s3 ← schedcontext.set_consumed st ar s2 a sc ct call
      let s4 ← sched.set_thread_state st s3 ct sched.TS_RUNNING
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s4, a)) ⦃ r => r.1 = .Ok () ∧ r.2.2 = a ∧
      ∃ (σ1 : Fl4Spec.State Unit) (data : List Fl4Spec.Data) (σ2 σ3 : Fl4Spec.State Unit),
      Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) ∧
      Fl4Spec.returnConsumed (Z := Unit) sc.bv σ1 = ({(data, σ2)}, False) ∧
      (do
        Fl4Spec.NonDet.when (call = true) (Fl4Spec.replyFromKernel (Z := Unit) ct.bv (0, data))
        Fl4Spec.setThreadState (Z := Unit) ct.bv .running : Fl4Spec.SMonad Unit Unit) σ2 = ({((), σ3)}, False) ∧
      SchedRel st N T C c r.2.1 σ3 ∧ NtfnStateRel N T (L.mem r.2.1) σ3 ∧ NSC N C σ3 ∧ Inv σ3 ∧
      YieldRel T C (L.mem r.2.1) σ3 ∧ ActIdle σ3 ∧ WritesIn st s r.2.1 (KFoot st T N C c s σ) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  refine WP.spec_bind (set_runnable_rels s σ hS hR hN hI hY hct hkc hrun _ .restart (by rw [tsVals.2.1]; rfl) rfl) ?_
  rintro s2 ⟨σ1, he1, hσ1, hS1, hR1, hN1, hI1, hY1, hA1, hw1⟩
  refine WP.spec_bind (set_consumed_refines s2 a σ1 hS1 hR1 hN1 hI1 hY1 hsc hct call hmax htu hmsg) ?_
  rintro s3 ⟨cv, σa, σb, hspc, hrt, hrf, hS3, hR3, hN3, hI3, hY3, hsf3, -, -, hw3⟩
  have hz1 : SzKeep σ σ1 := by
    rw [hσ1]; intro q x m hq
    rw [stsAct_kheap] at hq
    exact SzKeep.updK hkc (fun _ _ e => by cases e) q x m hq
  have hw13 := WritesIn.kfoot_trans (WritesIn.kfoot_of_sfoot (N := N) (C := C) (σ := σ) hw1) (SzKeepC.of hz1) hw3
  have hkc1 : σ1.kheap ct.bv = some (.tcb { xc with tcbState := .restart }) := by
    rw [hσ1, stsAct_kheap]; simp [updK]
  obtain ⟨xc3, hkc3, hst3, -, -, -⟩ := hsf3.tcb _ _ hkc1
  have hrun3 : Fl4Spec.runnable xc3.tcbState = true := by rw [hst3]; rfl
  refine WP.spec_bind (set_runnable_rels s3 σb hS3 hR3 hN3 hI3 hY3 hct hkc3 hrun3 _ .running
    (by rw [tsVals.1]; rfl) rfl) ?_
  rintro s4 ⟨σ4, he4, -, hS4, hR4, hN4, hI4, hY4, hA4, hw4⟩
  refine (WP.spec_ok _).mpr ⟨rfl, rfl, σ1, Fl4Spec.wordsFromTime cv.bv, σa, σ4, he1, ?_, ?_, hS4, hR4, hN4, hI4, hY4,
    hA4 (ActIdle.sframe (hA1 hAI) hsf3), WritesIn.kfoot_sfoot hw13 hw4⟩
  · unfold Fl4Spec.returnConsumed; rw [nd_bind_one hspc]; rfl
  · cases call
    · rw [nd_when_false_y (by decide), nd_pure_bind', ← hrf rfl]; exact he4
    · unfold Fl4Spec.NonDet.when
      rw [ite_eq_left rfl, nd_bind_one (hrt rfl)]; exact he4

/-- **SchedContext `YieldTo`** (the decoder's branch after its checks:
restart, `yield_to`) refines l4v's `set_thread_state Restart` and
`sched_context_yield_to` (with `handle_invocation`'s reply and
`set_thread_state Running` when the call returns at once). -/
theorem yieldto_invoke_refines {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hY : YieldRel T C (L.mem s) σ) (hC0 : ∀ q ∈ C, q ≠ 0#u64)
    {sc : U64} (hsc : sc ∈ C) {x : Fl4Spec.SchedContext} {n : Nat} (hk : σ.kheap sc.bv = some (.schedContext x n))
    {t : U64} (ht : t ∈ T) (htc : x.scTcb = some t.bv) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hxt : xt.tcbSchedContext = some sc.bv)
    {ct : U64} (hct : ct ∈ T) (hctt : ct ≠ t) (hcur : σ.curThread = ct.bv) {xc : Fl4Spec.Tcb}
    (hkc : σ.kheap ct.bv = some (.tcb xc))
    (hyc : xc.tcbYieldTo = none) (hcs : Fl4Spec.schedulable ct.bv σ = true) (hAI : ActIdle σ) (call : Bool)
    (hmb : sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, ar.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) (hmsg : MsgOK st N T C c) :
    (do
      let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
      let (s3, a2) ← schedcontext.yield_to st ar s2 a sc call
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s3, a2)) ⦃ r => r.1 = .Ok () ∧ r.2.2 = a ∧
      ∃ (σ0 : Fl4Spec.State Unit) (data : List Fl4Spec.Data) (σ1 σ2 : Fl4Spec.State Unit),
      Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ0)}, False) ∧
      Fl4Spec.schedContextYieldTo (Z := Unit) sc.bv σ0 = ({(data, σ1)}, False) ∧
      ((data = [] ∧ σ2 = σ1) ∨
        (do
          Fl4Spec.NonDet.when (call = true) (Fl4Spec.replyFromKernel (Z := Unit) ct.bv (0, data))
          Fl4Spec.setThreadState (Z := Unit) ct.bv .running : Fl4Spec.SMonad Unit Unit) σ1 = ({((), σ2)}, False)) ∧
      SchedRel st N T C c r.2.1 σ2 ∧ NtfnStateRel N T (L.mem r.2.1) σ2 ∧ NSC N C σ2 ∧ Inv σ2 ∧
      YieldRel T C (L.mem r.2.1) σ2 ∧ ActIdle σ2 ∧ WritesIn st s r.2.1 (TFoot st T N C c s σ) ⦄ := by
  obtain ⟨xq, scq, yq, nq, hq1, hq2, hq3, hq4, hq5, hq6⟩ := schedulable_inv hcs
  rw [hkc] at hq1; cases hq1
  refine WP.spec_bind (set_runnable_rels s σ hS hR hN hI hY hct hkc hq3 _ .restart (by rw [tsVals.2.1]; rfl) rfl) ?_
  rintro s2 ⟨σ1, he1, hσ1, hS1, hR1, hN1, hI1, hY1, hA1, hwr1⟩
  have hko : ∀ q, q ≠ ct.bv → σ1.kheap q = σ.kheap q := fun q hq => by rw [hσ1, stsAct_kheap]; simp [updK, hq]
  have hkc1 : σ1.kheap ct.bv = some (.tcb { xc with tcbState := .restart }) := by
    rw [hσ1, stsAct_kheap]; simp [updK]
  have hpc : sc.bv ≠ ct.bv := fun e => by rw [e, hkc] at hk; cases hk
  have hk1 : σ1.kheap sc.bv = some (.schedContext x n) := by rw [hko _ hpc]; exact hk
  have hkt1 : σ1.kheap t.bv = some (.tcb xt) := by rw [hko _ (bv_ne (Ne.symm hctt))]; exact hkt
  have hcur1 : σ1.curThread = ct.bv := by rw [hσ1, stsAct_cur']; exact hcur
  have hrel1 : σ1.releaseQueue = σ.releaseQueue := by rw [hσ1, stsAct_rel']; rfl
  have hscq : scq ≠ ct.bv := fun e => by rw [e, hkc] at hq4; cases hq4
  have hcs1 : Fl4Spec.schedulable ct.bv σ1 = true :=
    schedulable_of hkc1 hq2 rfl (by rw [hko _ hscq]; exact hq4) hq5 (by rw [hrel1]; exact hq6)
  refine WP.spec_bind (yield_to_refines s2 a σ1 hS1 hR1 hN1 hI1 hY1 hC0 hsc hk1 ht htc hkt1 hxt hct hcur1 hkc1
    hyc hcs1 (hA1 hAI) call hmb hmax htu hmsg) ?_
  rintro ⟨s3, a2⟩ ⟨ha2, data, σa, σb, hyt, hcase, hS3, hR3, hN3, hI3, hY3, hA3, hw3⟩
  have hz1 : SzKeepC C σ σ1 := SzKeepC.of fun q x m hq => by
    rw [hσ1, stsAct_kheap] at hq
    exact SzKeep.updK hkc (fun _ _ e => by cases e) q x m hq
  exact (WP.spec_ok _).mpr ⟨rfl, ha2, σ1, data, σa, σb, he1, hyt, hcase, hS3, hR3, hN3, hI3, hY3, hA3,
    WritesIn.tfoot_trans (WritesIn.tfoot_of_sfoot hwr1) hz1 hw3⟩

end

end

end Fl4Proofs.P3.Sched
