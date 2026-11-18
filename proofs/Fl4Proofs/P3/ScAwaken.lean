/-
P3 (DESIGN.md §9), scheduler: **`awaken`** (Schedule_A) and its pieces.

* `release_remove_repr`, `release_remove_head_refines`: FL4's
  `release_remove` of the release queue's head refines l4v
  `tcb_release_remove`: the head leaves the queue and the `REPROGRAM` word
  is set (`reprogram_timer`), the rest of the footprint being the queue's
  `Sched` links, its head and tail words and the thread's `IN_QUEUES` word.
* `Inv.relPop`: releasing a ready head keeps `Inv` (its head refill holds at
  least `MIN_BUDGET`, `Inv.headMin`, so it is released).
* `Calm` (ScIdle.lean): what `awaken` keeps (the heap, the current thread,
  SC and times, the idle thread, the domain).
* `awaken_loop_refines`: FL4's loop against l4v's `whileLoop`, given fewer
  release-queue members than the fuel.
* `SchedPreW`, `CurOwn`, `awaken_refinesW`: `awaken` from a mid-entry state
  (a pending reschedule stays pending, `possibleSwitchTo_cn`).
-/
import Fl4Proofs.P3.ScSchedule
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

theorem filter_ne_head {t : ObjRef} {rest : List ObjRef} (hn : t ∉ rest) :
    (t :: rest).filter (fun x => decide (t ≠ x)) = rest := by
  rw [List.filter_cons_of_neg (by simp)]
  exact List.filter_eq_self.2 fun a ha => by
    have : t ≠ a := fun e => hn (e ▸ ha)
    simpa using this

/-- **The spec's `tcb_release_remove` of the release queue's head.** -/
theorem tcbReleaseRemove_head {σ : State Unit} {t : ObjRef} {rest : List ObjRef}
    (hq : σ.releaseQueue = t :: rest) (hn : t ∉ rest) :
    tcbReleaseRemove (Z := Unit) t σ = ({((), setRel σ rest true)}, False) := by
  unfold tcbReleaseRemove
  rw [nd_gets_bind, hq]
  unfold NonDet.when
  rw [if_pos ⟨by simp, rfl⟩]
  rw [nd_bind_one (show NonDet.modify (fun s : State Unit => { s with reprogramTimer := true }) σ =
    ({((), { σ with reprogramTimer := true })}, False) from rfl)]
  rw [nd_pure_bind']
  unfold setReleaseQueue tcbSchedDequeue
  rw [filter_ne_head hn]
  rfl

theorem suff0_of {r : Refill} (h : MIN_BUDGET ≤ r.rAmount) : refillSufficient 0 r = true := by
  unfold refillSufficient refillCapacity
  have : ¬ r.rAmount < 0 := by rw [BitVec.lt_def]; simp
  rw [if_neg this]; simpa using h

/-- An active SC's head holds at least `MIN_BUDGET` (`Inv.refills`, `Inv.rr`). -/
theorem Inv.headMin {σ : State Unit} (h : Inv σ) {p : ObjRef} {y : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext y n)) (ha : scActive y = true) : MIN_BUDGET ≤ (refillHd y).rAmount := by
  by_cases hp : y.scPeriod = 0
  · exact (h.rr p y n hk ha hp).2.2
  · exact (h.refills p y n hk ha hp).2.2.2

/-- **Releasing the release queue's head keeps `Inv`** when its refill is
ready. -/
theorem Inv.relPop {σ : State Unit} (h : Inv σ) {t : ObjRef} {rest : List ObjRef}
    (hq : σ.releaseQueue = t :: rest)
    (hrd : ∀ x scp y n, σ.kheap t = some (.tcb x) → x.tcbSchedContext = some scp →
      σ.kheap scp = some (.schedContext y n) → refillReady σ.curTime (refillHd y) = true) (bb : Bool) :
    Inv (setRel σ rest bb) := by
  have hsub : ∀ u ∈ rest, u ∈ σ.releaseQueue := fun u hu => by rw [hq]; exact List.mem_cons_of_mem _ hu
  refine ⟨h.rq, fun u hu => h.rel u (hsub u hu), ?_, fun u x hx hc => ?_, h.refills, h.back, h.ntfnSc, h.ne, h.rr⟩
  · have hs := h.sorted
    rw [hq] at hs
    refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab => ?_) (List.pairwise_cons.1 hs).2
    obtain ⟨xa, pa, ya, na, h1, h2, -, h4, h5⟩ := h.rel a (hsub a ha)
    obtain ⟨xb, pb, yb, nb, g1, g2, -, g4, g5⟩ := h.rel b (hsub b hb)
    have nea := h.ne _ _ _ h4 h5
    have neb := h.ne _ _ _ g4 g5
    rw [specRt_eq (σ := setRel σ rest bb) h1 h2 h4 nea, specRt_eq (σ := setRel σ rest bb) g1 g2 g4 neb]
    rw [specRt_eq h1 h2 h4 nea, specRt_eq g1 g2 g4 neb] at hab
    exact hab
  · intro x' scp y n h1 h2 h3 h4 h5
    by_cases e : u = t
    · subst e
      exact ⟨hrd x' scp y n h1 h2 h3, suff0_of (h.headMin h3 h4)⟩
    · have h5' : u ∉ σ.releaseQueue := by
        rw [hq]; intro hm; rcases List.mem_cons.1 hm with e' | hm
        · exact e e'
        · exact h5 hm
      exact h.rd u x hx hc x' scp y n h1 h2 h3 h4 h5'

theorem readRQ_nil {σ : State Unit} (hq : σ.releaseQueue = []) :
    readReleaseQNonEmptyAndReady (Z := Unit) σ = some false := by
  show Option.bind (Lookup.asks (fun s : State Unit => s.releaseQueue) σ) (fun rq =>
    (if rq = [] then Lookup.oreturn false else readTcbRefillReady (the rq.head?)) σ) = _
  simp [Lookup.asks, hq, Lookup.oreturn]

theorem readRQ_cons {σ : State Unit} {t : ObjRef} {rest : List ObjRef} (hq : σ.releaseQueue = t :: rest)
    {x : Tcb} {scp : ObjRef} {y : SchedContext} {n : Nat} (hk : σ.kheap t = some (.tcb x))
    (hsc : x.tcbSchedContext = some scp) (hky : σ.kheap scp = some (.schedContext y n)) (hne : y.scRefills ≠ []) :
    readReleaseQNonEmptyAndReady (Z := Unit) σ = some (refillReady σ.curTime (refillHd y)) := by
  have h0 : getTcb (Z := Unit) t σ = some x := by simp [getTcb, readObject, hk]
  have h1 : readTcbObjRef (Z := Unit) Tcb.tcbSchedContext t σ = some (some scp) := by
    change Option.bind (getTcb (Z := Unit) t σ) (fun a => Lookup.oreturn a.tcbSchedContext σ) = _
    rw [h0, ← hsc]; rfl
  have h2 : readScRefillReady (Z := Unit) scp σ = some (refillReady σ.curTime (refillHd y)) := by
    show Option.bind (readRefillHead scp σ) (fun h => Option.bind (Lookup.asks (fun s : State Unit => s.curTime) σ)
      (fun ct => Lookup.oreturn (refillReady ct h) σ)) = _
    rw [readRefillHead_eq hky hne]; rfl
  have h3 : readTcbRefillReady (Z := Unit) t σ = some (refillReady σ.curTime (refillHd y)) := by
    show Option.bind (readTcbObjRef Tcb.tcbSchedContext t σ) (fun o => Option.bind (Lookup.oassertOpt o σ)
      (fun p => Option.bind (readScRefillReady p σ) (fun r => Lookup.oreturn r σ))) = _
    rw [h1]
    show Option.bind (readScRefillReady scp σ) (fun r => Lookup.oreturn r σ) = _
    rw [h2]; rfl
  show Option.bind (Lookup.asks (fun s : State Unit => s.releaseQueue) σ) (fun rq =>
    (if rq = [] then Lookup.oreturn false else readTcbRefillReady (the rq.head?)) σ) = _
  simp only [Lookup.asks, hq, Option.bind_some, reduceCtorEq, ↓reduceIte, List.head?_cons]
  exact h3

/-- **One round of `awaken`**: the head leaves the release queue, then
`possible_switch_to`. -/
theorem tcbReleaseDequeue_eq {σ σ2 : State Unit} {t : ObjRef} {rest : List ObjRef}
    (hq : σ.releaseQueue = t :: rest) (hn : t ∉ rest)
    (h2 : possibleSwitchTo (Z := Unit) t (setRel σ rest true) = ({((), σ2)}, False)) :
    tcbReleaseDequeue (Z := Unit) σ = ({((), σ2)}, False) := by
  unfold tcbReleaseDequeue
  rw [nd_gets_bind, hq, nd_bind_one (assert_true (by simp) σ)]
  show (Fl4Spec.NonDet.bind (tcbReleaseRemove (the (some t))) fun _ => possibleSwitchTo (the (some t))) σ = _
  rw [the_some]
  exact (nd_bind_one (tcbReleaseRemove_head hq hn) (fun _ => possibleSwitchTo (Z := Unit) t)).trans h2

theorem pair_fst_eq {α : Type} {a b : α} {σ : State Unit}
    (h : (({(a, σ)}, False) : Set (α × State Unit) × Prop) = ({(b, σ)}, False)) : a = b :=
  (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst h))).1

theorem CurInv.sub {σ σ' : State Unit} (h : CurInv σ) (hc : Calm σ σ')
    (hsub : ∀ u ∈ σ'.releaseQueue, u ∈ σ.releaseQueue) : CurInv σ' := by
  obtain ⟨hk, h1, h2, -⟩ := hc
  obtain ⟨xt, hkt, hxs, hnb⟩ := h.tcb
  obtain ⟨x, n, hx⟩ := h.sc
  exact ⟨⟨xt, by rw [hk, h1]; exact hkt, by rw [h2]; exact hxs, hnb⟩, ⟨x, n, by rw [hk, h2]; exact hx⟩,
    fun hid y m hy => h.active (h2 ▸ hid) y m (by rw [hk, h2] at hy; exact hy),
    fun hm => h.notRel (by rw [← h1]; exact hsub _ hm)⟩

theorem OffOK.calm {σ σ' : State Unit} (h : OffOK σ) (hc : Calm σ σ') : OffOK σ' := by
  obtain ⟨hk, -, h2, h3, h4, -⟩ := hc
  intro h0 y n hy ha
  rw [h4] at h0 ⊢; rw [h3]; rw [hk, h2] at hy; rw [h2] at ha
  exact h h0 y n hy ha

/-- `possible_switch_to` keeps a pending reschedule pending. -/
theorem possibleSwitchTo_cn {σ σ' : State Unit} (h : Inv σ) {t : ObjRef} (hs : schedulable t σ = true)
    (he : possibleSwitchTo (Z := Unit) t σ = ({((), σ')}, False))
    (hcn : σ.schedulerAction = .chooseNewThread) : σ'.schedulerAction = .chooseNewThread := by
  obtain ⟨x, -, -, -, hk, -⟩ := schedulable_inv hs
  rw [possibleSwitchTo_unfold hk] at he
  split_ifs at he with g1 g2 g3
  · rw [tcbSchedAction_gen hk] at he
    rw [pair_eq he]; exact hcn
  · obtain ⟨σ1, h1, hq1, -⟩ := rescheduleRequired_calm h.actReady
    rw [nd_bind_one h1] at he
    have hk1 : σ1.kheap t = some (.tcb x) := by rw [hq1.1]; exact hk
    rw [tcbSchedAction_gen hk1] at he
    rw [pair_eq he]
    rw [rescheduleRequired_noswitch (fun t h => by rw [hcn] at h; cases h)] at h1
    have e := pair_eq h1
    first | (rw [← e]; rfl) | (rw [e]; rfl) | (subst e; rfl)
  · exact absurd hcn (by rw [not_not.1 g3]; intro e; cases e)
  · rw [pair_eq he]; exact hcn

/-- `reschedule_required` leaves a reschedule pending (as ScMidCur's
`rescheduleRequired_cn`). -/
theorem rescheduleRequired_cnA {σ : State Unit} {x : Unit × State Unit}
    (hx : x ∈ (rescheduleRequired (Z := Unit) σ).1) : x.2.schedulerAction = .chooseNewThread := by
  unfold rescheduleRequired setSchedulerAction at hx
  obtain ⟨y, -, hx⟩ := hx
  generalize y.1 = act at hx
  cases act with
  | switchThread t =>
    obtain ⟨z, -, hx⟩ := hx
    obtain ⟨w, -, hx⟩ := hx
    rw [Set.mem_singleton_iff.1 hx]
  | resumeCurThread =>
    first | (rw [Set.mem_singleton_iff.1 hx]) | (obtain ⟨w, -, hx⟩ := hx; rw [Set.mem_singleton_iff.1 hx])
  | chooseNewThread =>
    first | (rw [Set.mem_singleton_iff.1 hx]) | (obtain ⟨w, -, hx⟩ := hx; rw [Set.mem_singleton_iff.1 hx])

/-- `possible_switch_to` resumes nothing newly: a pending reschedule or
switch stays one or the other. -/
theorem possibleSwitchTo_nr {σ σ' : State Unit} (h : Inv σ) {t : ObjRef} (hs : schedulable t σ = true)
    (he : possibleSwitchTo (Z := Unit) t σ = ({((), σ')}, False))
    (hnr : σ.schedulerAction ≠ .resumeCurThread) : σ'.schedulerAction ≠ .resumeCurThread := by
  obtain ⟨x, -, -, -, hk, -⟩ := schedulable_inv hs
  rw [possibleSwitchTo_unfold hk] at he
  split_ifs at he
  · rw [tcbSchedAction_gen hk] at he
    rw [pair_eq he]; exact hnr
  · obtain ⟨σ1, h1, hq1, -⟩ := rescheduleRequired_calm h.actReady
    have hc1 : σ1.schedulerAction = .chooseNewThread :=
      rescheduleRequired_cnA (x := ((), σ1)) (by rw [h1]; exact Set.mem_singleton _)
    rw [nd_bind_one h1] at he
    have hk1 : σ1.kheap t = some (.tcb x) := by rw [hq1.1]; exact hk
    rw [tcbSchedAction_gen hk1] at he
    rw [pair_eq he]
    intro e
    have e' : σ1.schedulerAction = .resumeCurThread := e
    rw [hc1] at e'; cases e'
  · rw [pair_eq he]; exact hnr

/-- What `schedule` assumes of its state besides `SchedRel`: the invariants
`Inv`, `CurInv`, `OffOK` and `ActIdle`, and the domain scope (domain time
nonzero, so the domain does not end). -/
def SchedPre (σ : State Unit) : Prop :=
  Inv σ ∧ CurInv σ ∧ OffOK σ ∧ ActIdle σ ∧ σ.domainTime ≠ 0

/-- **The current SC's owner** (what `schedule`'s commit of the outgoing SC
reads when no `CurInv` holds): a TCB `u` of `T` bound to the current SC,
which names it, and out of the release queue while time is to be charged. -/
def CurOwn (T : Set U64) (σ : State Unit) : Prop :=
  ∃ u ∈ T, ∃ xt, σ.kheap u.bv = some (.tcb xt) ∧ xt.tcbSchedContext = some σ.curSc ∧
    (∀ x n, σ.kheap σ.curSc = some (.schedContext x n) → x.scTcb = some u.bv) ∧
    (0 < σ.consumedTime → u.bv ∉ σ.releaseQueue)

theorem CurOwn.sub {T : Set U64} {σ σ' : State Unit} (h : CurOwn T σ) (hc : Calm σ σ')
    (hsub : ∀ u ∈ σ'.releaseQueue, u ∈ σ.releaseQueue) : CurOwn T σ' := by
  obtain ⟨hk, -, h2, -, h4, -⟩ := hc
  obtain ⟨u, hu, xt, hkt, hxs, hown, hnr⟩ := h
  exact ⟨u, hu, xt, by rw [hk]; exact hkt, by rw [h2]; exact hxs,
    fun x n hx => hown x n (by rw [hk, h2] at hx; exact hx),
    fun h0 hm => hnr (by rw [← h4]; exact h0) (hsub _ hm)⟩

/-- **The current SC owned, or bound to no thread** (after the current
thread's deletion of its own TCB, or of its SC's binding): an SC of `C`
naming no thread. -/
def CurOwnW (T C : Set U64) (σ : State Unit) : Prop :=
  CurOwn T σ ∨ ((∃ sc ∈ C, sc.bv = σ.curSc) ∧ ∀ x n, σ.kheap σ.curSc = some (.schedContext x n) → x.scTcb = none)

theorem CurOwnW.sub {T C : Set U64} {σ σ' : State Unit} (h : CurOwnW T C σ) (hc : Calm σ σ')
    (hsub : ∀ u ∈ σ'.releaseQueue, u ∈ σ.releaseQueue) : CurOwnW T C σ' := by
  rcases h with h | ⟨hcs, hun⟩
  · exact Or.inl (h.sub hc hsub)
  · obtain ⟨hk, -, h2, -⟩ := hc
    exact Or.inr ⟨by rw [h2]; exact hcs, fun x n hx => hun x n (by rw [hk, h2] at hx; exact hx)⟩

/-- **`CurOwnW` across a step** whose owned case is kept and which keeps the
current SC and does not bind it. -/
theorem CurOwnW.imp {T C : Set U64} {σ σ' : State Unit} (h : CurOwnW T C σ) (h1 : CurOwn T σ → CurOwn T σ')
    (h2 : σ'.curSc = σ.curSc)
    (h3 : ∀ x n, σ'.kheap σ.curSc = some (.schedContext x n) →
      x.scTcb = none ∨ ∃ y, σ.kheap σ.curSc = some (.schedContext y n) ∧ x.scTcb = y.scTcb) :
    CurOwnW T C σ' := by
  rcases h with h | ⟨hcs, hun⟩
  · exact Or.inl (h1 h)
  · refine Or.inr ⟨by rw [h2]; exact hcs, fun x n hx => ?_⟩
    rw [h2] at hx
    rcases h3 x n hx with e | ⟨y, hy, e⟩
    · exact e
    · rw [e]; exact hun y n hy

/-- **`schedule`'s precondition mid-entry** (`SchedPre` with `CurInv` only
unless a reschedule is pending, and the current SC owned or unbound). -/
def SchedPreW (T C : Set U64) (σ : State Unit) : Prop :=
  Inv σ ∧ (σ.schedulerAction = .chooseNewThread ∨ CurInv σ) ∧ OffOK σ ∧ ActIdle σ ∧ σ.domainTime ≠ 0 ∧
    CurOwnW T C σ

/-- A notification signal (l4v `send_signal`). -/
def Signal (σ σ' : State Unit) : Prop := ∃ n b, sendSignal (Z := Unit) n b σ = ({((), σ')}, False)

/-- One TCB timer fired (`timer::fire`'s loop body, l4h 0003): its thread's
bound notification signalled, if it has one (`Signal`), then the core's
timer reprogram requested (FL4 sets `REPROGRAM` after every fired timer,
which `SchedRel` relates to `reprogram_timer`; the l4h timer queue itself is
not modelled, as for SetTimer). -/
def Fire (σ σ' : State Unit) : Prop :=
  ∃ σ1, (σ1 = σ ∨ Signal σ σ1) ∧ σ' = { σ1 with reprogramTimer := true }

/-- A sequence of fired TCB timers (`Fire`): the spec-visible effect of FL4's
TCB timers (`timer::fire`, l4h 0003). -/
def Fires : State Unit → State Unit → Prop := Relation.ReflTransGen Fire

end Spec

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T : Set U64}

/-- The release queue's head and tail words. -/
def RelHT (o : Nat) : Prop := o = 64 ∨ o = 72

/-- `release_remove`'s tail after the `REPROGRAM` write: the `Sched` links of
the queue, its head and tail words and `t`'s `IN_QUEUES` word. -/
theorem release_remove_tail (s : S) (c t : U64) (xs : List U64) (hT : TcbPlaced T) (ht : t ∈ T)
    (hN : NodePlaced st T s c) (h : QueueRel (L.mem s) T .Sched (L.relQ s c) xs) (htx : t ∈ xs) :
    (do
      let q ← sched.q_get st s c layout.node.RELEASE_HEAD
      let (q1, s2) ← tcbqueue.remove st s tcbqueue.Link.Sched q t
      let s3 ← sched.q_set st s2 c layout.node.RELEASE_HEAD q1
      sched.set_flag st s3 t sched.Q_RELEASE false) ⦃ s' => WritesIn st s s' (L.QFoot s xs c RelHT t) ⦄ := by
  have hta : TcbAddr t := hT t ht
  step as ⟨q, q_post⟩
  have hq' : q = L.relQ s c := by rw [q_post]; rfl
  refine WP.spec_bind (tcbqueue.remove.rel s .Sched q t xs hT (hq' ▸ h) htx) ?_
  rintro ⟨q1, s2⟩ h2
  simp only [WP.uncurry'_pair] at h2
  obtain ⟨-, hf2, -, -⟩ := h2
  have w02 := hf2.writesIn
  step as ⟨s3, s3_post⟩
  have w23 : WritesIn st s2 s3 (L.NodeOf s c RelHT) := by
    rw [s3_post, nodeAt_of_ksb w02.1, nodeAt_of_ksb w02.1]
    exact ((writesIn_node (P := RelHT) hN (by rw [relh_val]; simp [RelHT]) (by rw [relh_val]; omega)
      (by rw [relh_val])).trans (writesIn_node (P := RelHT) hN (by rw [relt_val]; simp [RelHT])
        (by rw [relt_val]; omega) (by rw [relt_val]))).mono fun b hb => by rcases hb with hb | hb <;> exact hb
  step as ⟨s4, s4_post⟩
  simp only [Bool.false_eq_true, ite_false] at s4_post
  have w34 : WritesIn st s3 s4 (· = inqA t) := by rw [s4_post]; exact writesIn_inq hta
  refine ((w02.trans w23).trans w34).mono fun b hb => ?_
  rcases hb with (h | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))

/-- **`release_remove` of the release queue's head sets `REPROGRAM`** (and
leaves it set). -/
theorem release_remove_repr (s : S) (t : U64) (xs : List U64) (hT : TcbPlaced T) (ht : t ∈ T)
    (hN : NodePlaced st T s (L.mem s (affA t))) (hN' : NodePlaced st T s (L.cpu s))
    (h : QueueRel (L.mem s) T .Sched (L.relQ s (L.mem s (affA t))) xs)
    (hq1 : (L.mem s (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64) (htx : t ∈ xs)
    (hhd : L.mem s (L.nodeAt s (L.mem s (affA t)) layout.node.RELEASE_HEAD) = t) :
    sched.release_remove st s t ⦃ s' =>
      L.mem s' (L.nodeAt s' (L.mem s (affA t)) layout.node.REPROGRAM) = 1#u64 ⦄ := by
  unfold sched.release_remove
  step as ⟨b, b_post⟩
  have hb : b = true := by rw [b_post]; exact decide_eq_true hq1
  simp only [hb, ↓reduceIte]
  step as ⟨cpu, cpu_post⟩
  step as ⟨i, i_post⟩
  subst cpu_post
  rw [if_pos (by rw [i_post, hhd])]
  step as ⟨s1, s1_post⟩
  have hk1 : L.ksb s1 = L.ksb s := by rw [s1_post, L.ksb_wr]
  have hN1 := nodePlaced_ksb hN hk1
  have hN1' : NodePlaced st T s1 (L.cpu s1) := by
    rw [s1_post, L.cpu_wr]; exact nodePlaced_ksb hN' (by rw [L.ksb_wr])
  have h1 : QueueRel (L.mem s1) T .Sched (L.relQ s1 (L.mem s (affA t))) xs := by
    rw [s1_post, relQ_wr_node hN hN (by rw [repr_val]; omega) (by rw [repr_val]) (fun _ => by rw [repr_val]; omega)]
    exact h.wr_node hT hN (by rw [repr_val]; omega) (by rw [repr_val])
  refine WP.spec_mono (release_remove_tail s1 _ t xs hT ht hN1 h1 htx) ?_
  intro s' hw
  rw [node_qfoot hT h.mem hN1 hN1' ht hw hN1 (by rw [repr_val]; omega) (by rw [repr_val])
    (fun _ => by rw [repr_val]; simp [RelHT]) (fun _ => by rw [repr_val]; omega)]
  rw [s1_post, nodeAt_of_ksb (L.ksb_wr _ _ _), L.mem_wr_same (nodeAt_aligned hN (by rw [repr_val]; omega) (by rw [repr_val]))]

/-- **`release_remove` of the release queue's head refines
`tcb_release_remove`**: the head leaves the queue and `reprogram_timer` is
set. -/
theorem release_remove_head_refines {N C : Set U64} {c : U64} (s : S) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) {t : U64} (ht : t ∈ T) {rest : List Fl4Spec.ObjRef}
    (hq : σ.releaseQueue = t.bv :: rest) :
    sched.release_remove st s t ⦃ s' => Fl4Spec.tcbReleaseRemove (Z := Unit) t.bv σ =
      ({((), setRel σ rest true)}, False) ∧ FootEq N T (L.mem s) (L.mem s') ∧
      SchedRel st N T C c s' (setRel σ rest true) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hT := hc.tcbs
  have haf := hc.aff t ht
  have hN : NodePlaced st T s (L.mem s (affA t)) := by rw [haf]; exact hc.node
  have hN' : NodePlaced st T s (L.cpu s) := by rw [hc.cur]; exact hc.node
  have hrel : QueueRel (L.mem s) T .Sched (L.relQ s (L.mem s (affA t))) R := by rw [haf]; exact hc.release
  obtain ⟨R0, hR, hR0⟩ : ∃ R0, R = t :: R0 ∧ R0.map UScalar.bv = rest := by
    have e := hs.rel
    rw [hq] at e
    match R, e with
    | a :: R0, e =>
      simp only [List.map_cons, List.cons.injEq] at e
      exact ⟨R0, by rw [eq_of_bv e.1.symm], e.2.symm⟩
  have htR : t ∈ R := by rw [hR]; exact List.mem_cons_self
  have hq1 := (hc.released t ht).2 htR
  have hnd := hc.release.nodup
  rw [hR] at hnd
  have htn : t ∉ R0 := (List.nodup_cons.1 hnd).1
  have hhd : L.mem s (L.nodeAt s (L.mem s (affA t)) layout.node.RELEASE_HEAD) = t := by
    have := hrel.head; rw [hR] at this; exact this
  have hW : ∀ w ∈ R, w ∈ T := hc.release.mem
  have h1 := sched.release_remove.rel s t R hT ht hN hrel (fun _ => htR)
  have h2 := sched.release_remove.foot s t R hT ht hN hN' hrel (fun _ => htR)
  have h3 := release_remove_repr s t R hT ht hN hN' hrel hq1 htR hhd
  refine WP.spec_mono (WP.spec_and h1 (WP.spec_and h2 h3)) ?_
  rintro s' ⟨hRc, ⟨hw, hinq⟩, hrp⟩
  rw [if_pos hq1, hR, List.erase_cons_head] at hRc
  rw [if_pos hq1] at hinq
  rw [haf] at hRc hw hrp
  have hrest : rest = R0.map UScalar.bv := hR0.symm
  refine ⟨tcbReleaseRemove_head hq (by rw [hrest]; intro hm; rw [mem_map_bv] at hm; exact htn hm),
    qfoot_footEq hS hc ht hW hw, ?_⟩
  have := hS.rstep hc hs ht (W := R) (R' := R0) (tIn := False) (fun w hw => Or.inr hw)
    (fun _ hm => hc.excl t ht hm htR) hw hRc
    (fun y => by
      constructor
      · intro hy; exact Or.inr ⟨fun e => htn (e ▸ hy), by rw [hR]; exact List.mem_cons_of_mem _ hy⟩
      · rintro (⟨-, h⟩ | ⟨hne, hy⟩)
        · exact h.elim
        · rw [hR] at hy; rcases List.mem_cons.1 hy with e | hy
          · exact absurd e hne
          · exact hy)
    (by rw [hinq, andn_qr_qr]; simp) (by rw [hinq, andn_qr_qq]) (fun h => h.elim)
  have e1 : nodeW st s' c layout.node.REPROGRAM = 1#u64 := hrp
  rw [e1, ← hrest] at this
  simpa using this

/-- **`awaken`'s loop refines l4v `awaken`**, keeping `Inv` and `Calm`, given
fewer threads in the release queue than `fuel`. -/
theorem awaken_loop_refines {N C : Set U64} {c : U64} (s : S) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hA : ActSched σ) (fuel : U64) (hf : σ.releaseQueue.length < fuel.val) :
    sched.awaken_loop st s fuel ⦃ s' => ∃ σ', Fl4Spec.awaken (Z := Unit) σ = ({((), σ')}, False) ∧
      SchedRel st N T C c s' σ' ∧ NtfnStateRel N T (L.mem s') σ' ∧ NSC N C σ' ∧ Inv σ' ∧
      (ActSched σ' ∧ (σ.schedulerAction = .chooseNewThread → σ'.schedulerAction = .chooseNewThread) ∧
        (σ.schedulerAction ≠ .resumeCurThread → σ'.schedulerAction ≠ .resumeCurThread)) ∧
      Calm σ σ' ∧ (∀ u ∈ σ'.releaseQueue, u ∈ σ.releaseQueue) ∧ WritesIn st s s' (SFoot st T c s) ⦄ := by
  unfold sched.awaken_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.val) (inv := fun x => ∃ σk,
    SchedRel st N T C c x.1 σk ∧ NtfnStateRel N T (L.mem x.1) σk ∧ NSC N C σk ∧ Inv σk ∧
    (ActSched σk ∧ (σ.schedulerAction = .chooseNewThread → σk.schedulerAction = .chooseNewThread) ∧
      (σ.schedulerAction ≠ .resumeCurThread → σk.schedulerAction ≠ .resumeCurThread)) ∧
    σk.releaseQueue.length < x.2.val ∧ Fl4Spec.awaken (Z := Unit) σ = Fl4Spec.awaken (Z := Unit) σk ∧
    Calm σ σk ∧ (∀ u ∈ σk.releaseQueue, u ∈ σ.releaseQueue) ∧ WritesIn st s x.1 (SFoot st T c s))
  · rintro ⟨sk, fk⟩ ⟨σk, hSk, hRk, hNk, hIk, ⟨hAk, hCk, hNRk⟩, hlen, hloop, hcalm, hsub, hwk⟩
    dsimp only at *
    obtain ⟨Q, R, hc, hs⟩ := hSk.lists
    unfold sched.awaken_loop.body
    have hfp : fk > 0#u64 := by rw [gt_iff_val]; simp; omega
    simp only [hfp, ↓reduceIte]
    refine WP.spec_bind (fuel_dec hfp) ?_
    intro fk1 hfk1
    step with LawfulStore.cur_cpu_spec as ⟨cpu, hcpu⟩
    rw [hc.cur] at hcpu
    subst cpu
    step with obj.node_get.spec as ⟨i1, hi1⟩
    have hhd : i1 = R.headD 0#u64 := by rw [hi1]; exact hc.release.head
    step with obj.Tcb.is_null.spec as ⟨b, hb⟩
    cases R with
    | nil =>
      have hb' : b = true := by rw [hb, hhd]; rfl
      simp only [hb', ↓reduceIte, WP.spec_ok]
      have hq : σk.releaseQueue = [] := by rw [hs.rel]; rfl
      refine ⟨σk, ?_, hSk, hRk, hNk, hIk, hAk, hCk, hNRk, hcalm, hsub, hwk⟩
      rw [hloop]; unfold Fl4Spec.awaken
      exact wl_done (by rw [readRQ_nil hq]; simp [Fl4Spec.the])
    | cons t R0 =>
      have ht : t ∈ T := hc.release.mem t List.mem_cons_self
      have hi1t : i1 = t := hhd
      subst hi1t
      have hb' : b = false := by rw [hb]; exact decide_eq_false (hc.release.ne0 hc.tcbs _ List.mem_cons_self)
      simp only [hb', Bool.false_eq_true, ↓reduceIte]
      have hq : σk.releaseQueue = i1.bv :: R0.map UScalar.bv := by rw [hs.rel]; rfl
      obtain ⟨x, scp, y, n, h1, h2, h3, h4, h5⟩ := hIk.rel i1.bv (by rw [hq]; exact List.mem_cons_self)
      obtain ⟨x', hk', -, -, hsc, -⟩ := hs.tcb i1 ht
      rw [h1] at hk'; cases hk'
      have h0 : L.mem sk (scA i1) ≠ 0#u64 := fun e => by rw [hsc, e, optRef_zero] at h2; cases h2
      have hscp : scp = (L.mem sk (scA i1)).bv := by rw [hsc, optRef_ne h0] at h2; cases h2; rfl
      subst hscp
      have hscC := hs.scMem i1 ht h0
      have hne := hIk.ne _ _ _ h4 h5
      step with obj.Tcb.sc.spec as ⟨i2, hi2⟩
      subst hi2
      refine WP.spec_bind (ready_refines sk σk hSk hscC h4 h5) ?_
      intro b1 hb1
      rw [getScRefillReady_eq h4 hne] at hb1
      have hb1' : b1 = Fl4Spec.refillReady σk.curTime (Fl4Spec.refillHd y) := (pair_fst_eq hb1).symm
      have hC : Fl4Spec.the (Fl4Spec.readReleaseQNonEmptyAndReady (Z := Unit) σk) = b1 := by
        rw [readRQ_cons hq h1 h2 h4 hne, hb1']; rfl
      by_cases hr : b1 = true
      · simp only [hr, ↓reduceIte]
        have hnd : i1.bv ∉ R0.map UScalar.bv := by
          rw [mem_map_bv]; exact (List.nodup_cons.1 hc.release.nodup).1
        refine WP.spec_bind (WP.spec_and (release_remove_head_refines sk σk hSk ht hq) (release_remove_sfoot hSk ht)) ?_
        rintro s1 ⟨⟨he1, hf1, hS1⟩, hw1⟩
        have hR1 : NtfnStateRel N T (L.mem s1) (setRel σk (R0.map UScalar.bv) true) :=
          hRk.frame hSk.placed hf1 (KView.of_kheap rfl)
        have hI1 : Inv (setRel σk (R0.map UScalar.bv) true) :=
          hIk.relPop hq (fun x0 scp0 y0 n0 g1 g2 g3 => by
            rw [h1] at g1; cases g1; rw [h2] at g2; cases g2; rw [h4] at g3; cases g3
            rw [← hb1', hr]) true
        have hsch : Fl4Spec.schedulable i1.bv (setRel σk (R0.map UScalar.bv) true) = true :=
          schedulable_of (σ := setRel σk (R0.map UScalar.bv) true) h1 h2 h3 h4 h5
            (show i1.bv ∉ (setRel σk (R0.map UScalar.bv) true).releaseQueue from hnd)
        refine WP.spec_bind (WP.spec_and (possible_switch_to_refines s1 _ hR1 hS1 hI1.actReady i1 ht)
          (possible_switch_to_sfoot hR1 hS1 hI1.actReady ht)) ?_
        rintro s2 ⟨⟨σ2, he2, hk2, hf2, hS2⟩, hw2⟩
        rw [WP.spec_ok]
        have hq2 := possibleSwitchTo_qchange hI1 hsch he2
        have hc2 := possibleSwitchTo_calm hI1 hsch he2
        have hA1 : ActSched (setRel σk (R0.map UScalar.bv) true) :=
          hAk.sub rfl (fun u hu => by rw [hq]; exact List.mem_cons_of_mem _ hu) rfl
        refine ⟨⟨σ2, hS2, hR1.frame hS1.placed hf2 (KView.of_kheap hk2), ?_, hI1.qchange hq2,
          possibleSwitchTo_actSched hI1 hsch hA1 he2, fun h => possibleSwitchTo_cn hI1 hsch he2 (hCk h),
            fun h => possibleSwitchTo_nr hI1 hsch he2 (hNRk h), ?_, ?_,
          hcalm.trans ((Calm.refl _).trans hc2), fun u hu => ?_, WritesIn.sfoot_trans (WritesIn.sfoot_trans hwk hw1) hw2⟩, ?_⟩
        · intro m hm x0 p hx hp; rw [hk2] at hx; exact hNk m hm x0 p hx hp
        · rw [hq2.2.1]; show (R0.map UScalar.bv).length < fk1.val
          rw [hfk1]; rw [hq] at hlen; simp at hlen ⊢; omega
        · rw [hloop]; unfold Fl4Spec.awaken
          exact wl_step (by rw [hC]; exact hr) (tcbReleaseDequeue_eq hq hnd he2)
        · rw [hq2.2.1] at hu
          exact hsub u (by rw [hq]; exact List.mem_cons_of_mem _ hu)
        · rw [hfk1]; omega
      · have hr' : b1 = false := by simpa using hr
        simp only [hr', Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        refine ⟨σk, ?_, hSk, hRk, hNk, hIk, hAk, hCk, hNRk, hcalm, hsub, hwk⟩
        rw [hloop]; unfold Fl4Spec.awaken
        exact wl_done (by rw [hC, hr']; simp)
  · exact ⟨σ, hS, hR, hN, hI, ⟨hA, id, id⟩, hf, rfl, Calm.refl σ, fun _ h => h, WritesIn.refl _ _⟩

/-- The release queue is shorter than `WALK_FUEL`: its members are distinct
TCB addresses, none of them 0 or 1. -/
theorem rel_len_lt {N C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) : σ.releaseQueue.length < layout.WALK_FUEL.val := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  rw [hs.rel, List.length_map, walk_fuel_val]
  have h01 : ∀ t ∈ R, t ≠ 0#u64 ∧ t ≠ 1#u64 := fun t ht => tcb_ne01 (hc.tcbs t (hc.release.mem t ht))
  have hnd : (0#u64 :: 1#u64 :: R).Nodup := by
    refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨fun hm => (h01 _ hm).2 rfl, hc.release.nodup⟩⟩
    intro hm
    rcases List.mem_cons.1 hm with e | hm
    · exact absurd (congrArg UScalar.val e) (by simp)
    · exact (h01 _ hm).1 rfl
  have := nodup_length_le hnd
  simp at this; omega

/-- **The current thread owns the current SC** under `CurInv`. -/
theorem curOwn_of_curInv {N C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (hI : Inv σ) (hC : CurInv σ) : CurOwn T σ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨xt, hkt, hxs, -⟩ := hC.tcb
  have hct := hc.curT
  refine ⟨_, hct, xt, by rw [← hs.curThread]; exact hkt, hxs, fun x n hx => ?_, fun _ => by
    rw [← hs.curThread]; exact hC.notRel⟩
  obtain ⟨y, m, hky, hyt⟩ := hI.back _ xt _ hkt hxs
  rw [hx] at hky; cases hky; rw [hyt, hs.curThread]

theorem SchedPre.toW {N C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (h : SchedPre σ) : SchedPreW T C σ :=
  ⟨h.1, Or.inr h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, Or.inl (curOwn_of_curInv hS h.1 h.2.1)⟩

/-- **`awaken_refines` from `SchedPreW`.** -/
theorem awaken_refinesW {A : Type} {ar : machine.Arch A} {N C : Set U64} {c : U64} (s : S) (a : A)
    (σ : Fl4Spec.State Unit) {Pf : S × A → Fl4Spec.State Unit → Prop}
    (hfire : timer.fire st ar s a ⦃ r => ∃ σ1, Fires σ σ1 ∧ SchedRel st N T C c r.1 σ1 ∧
      NtfnStateRel N T (L.mem r.1) σ1 ∧ NSC N C σ1 ∧ SchedPreW T C σ1 ∧ Pf r σ1 ⦄) :
    sched.awaken st ar s a ⦃ r => ∃ σ1 σ2, Fires σ σ1 ∧ Fl4Spec.awaken (Z := Unit) σ1 = ({((), σ2)}, False) ∧
      SchedRel st N T C c r.1 σ2 ∧ NtfnStateRel N T (L.mem r.1) σ2 ∧ NSC N C σ2 ∧ SchedPreW T C σ2 ∧ Calm σ1 σ2 ∧
      (σ1.schedulerAction = .chooseNewThread → σ2.schedulerAction = .chooseNewThread) ∧
      (σ1.schedulerAction ≠ .resumeCurThread → σ2.schedulerAction ≠ .resumeCurThread) ∧
      (∀ u ∈ σ2.releaseQueue, u ∈ σ1.releaseQueue) ∧
      ∃ rf : S × A, Pf rf σ1 ∧ r.2 = rf.2 ∧ WritesIn st rf.1 r.1 (SFoot st T c rf.1) ⦄ := by
  unfold sched.awaken
  refine WP.spec_bind hfire ?_
  rintro ⟨s1, a1⟩ ⟨σ1, hF, hS1, hR1, hN1, ⟨hI1, hC1, hO1, ⟨hA1, hId1⟩, hd1, hW1⟩, hPf⟩
  refine WP.spec_bind (awaken_loop_refines s1 σ1 hS1 hR1 hN1 hI1 hA1 _ (rel_len_lt hS1)) ?_
  rintro s2 ⟨σ2, h2, hS2, hR2, hN2, hI2, ⟨hA2, hcn2, hnr2⟩, hc2, hsub, hw2⟩
  rw [WP.spec_ok]
  refine ⟨σ1, σ2, hF, h2, hS2, hR2, hN2, ⟨hI2, ?_, hO1.calm hc2, ⟨hA2, hId1.sub hc2 hsub⟩,
    by rw [hc2.2.2.2.2.2.2.2]; exact hd1, hW1.sub hc2 hsub⟩, hc2, hcn2, hnr2, hsub, (s1, a1), hPf, rfl, hw2⟩
  rcases hC1 with e | hC
  · exact Or.inl (hcn2 e)
  · exact Or.inr (hC.sub hc2 hsub)

/-- **`awaken` refines l4v `awaken`**, after FL4's TCB timers (`timer::fire`,
the hypothesis `hfire`: a sequence of signals, keeping the relations and
`SchedPre`). -/
theorem awaken_refines {A : Type} {ar : machine.Arch A} {N C : Set U64} {c : U64} (s : S) (a : A)
    (σ : Fl4Spec.State Unit)
    (hfire : timer.fire st ar s a ⦃ r => ∃ σ1, Fires σ σ1 ∧ SchedRel st N T C c r.1 σ1 ∧
      NtfnStateRel N T (L.mem r.1) σ1 ∧ NSC N C σ1 ∧ SchedPre σ1 ⦄) :
    sched.awaken st ar s a ⦃ r => ∃ σ1 σ2, Fires σ σ1 ∧ Fl4Spec.awaken (Z := Unit) σ1 = ({((), σ2)}, False) ∧
      SchedRel st N T C c r.1 σ2 ∧ NtfnStateRel N T (L.mem r.1) σ2 ∧ NSC N C σ2 ∧ SchedPre σ2 ∧ Calm σ1 σ2 ∧
      ∀ u ∈ σ2.releaseQueue, u ∈ σ1.releaseQueue ⦄ := by
  unfold sched.awaken
  refine WP.spec_bind hfire ?_
  rintro ⟨s1, a1⟩ ⟨σ1, hF, hS1, hR1, hN1, hI1, hC1, hO1, ⟨hA1, hId1⟩, hd1⟩
  refine WP.spec_bind (awaken_loop_refines s1 σ1 hS1 hR1 hN1 hI1 hA1 _ (rel_len_lt hS1)) ?_
  rintro s2 ⟨σ2, h2, hS2, hR2, hN2, hI2, ⟨hA2, -⟩, hc2, hsub, -⟩
  rw [WP.spec_ok]
  exact ⟨σ1, σ2, hF, h2, hS2, hR2, hN2, ⟨hI2, hC1.sub hc2 hsub, hO1.calm hc2, ⟨hA2, hId1.sub hc2 hsub⟩,
    by rw [hc2.2.2.2.2.2.2.2]; exact hd1⟩, hc2, hsub⟩

end
end
end Fl4Proofs.P3.Sched
