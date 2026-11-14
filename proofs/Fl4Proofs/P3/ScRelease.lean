/-
P3 (DESIGN.md §9), scheduling contexts: **the release queue**.

* `SchedRel.rstep`: a release-queue operation (P1 footprint `QFoot … RelOffs`:
  `Sched` links of the queue and the thread, the core's `REPROGRAM` and
  release-queue words, the thread's `IN_QUEUES`, the current core's
  `IPI_PENDING`) gives `SchedRel` for the new ghost list, with the spec's
  `release_queue` replaced and `reprogram_timer` read off the `REPROGRAM`
  word.
* `readyTimesAppend_eq`: the spec's `ready_times_append` on related states is
  the ordered insertion by FL4's ready times.
* `release_enqueue_refines`: `sched::release_enqueue` refines
  `tcb_release_enqueue` up to `reprogram_timer` (the only caller here,
  `postpone`, sets it afterwards on both sides), for a thread with an SC in
  no queue, given a release queue sorted by ready time whose members have
  SCs (`RelOK`, l4v `valid_release_q`/`sorted_release_q`).
-/
import Fl4Proofs.P3.ScTails
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- The spec state with the release queue replaced and `reprogram_timer`
set to `b`. -/
def setRel (σ : Fl4Spec.State Unit) (q : List Fl4Spec.ObjRef) (b : Bool) : Fl4Spec.State Unit :=
  { σ with releaseQueue := q, reprogramTimer := b }

/-- One release-queue operation on thread `t` (P1 `inv_release_step`'s
shape): `SchedRel` for the new ghost list. -/
theorem SchedRel.rstep {N T C : Set U64} {c : U64} {s s' : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {Q : U64 → List U64} {R : List U64} (hc : SchedCore st T c s Q R)
    (hs : SchedSpec st T C c s Q R σ) {t : U64} (ht : t ∈ T) {W R' : List U64} {tIn : Prop}
    (hW1 : ∀ w ∈ W, w = t ∨ w ∈ R) (hWt : t ∈ W → t ∉ Q (L.mem s (prioA t)))
    (hw : WritesIn st s s' (L.QFoot s W c RelOffs t))
    (hRc : QueueRel (L.mem s') T .Sched (L.relQ s' c) R')
    (hmem : ∀ y, y ∈ R' ↔ (y = t ∧ tIn) ∨ (y ≠ t ∧ y ∈ R))
    (hqr : (L.mem s' (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64 ↔ tIn)
    (hqq : L.mem s' (inqA t) &&& sched.Q_QUEUED = L.mem s (inqA t) &&& sched.Q_QUEUED)
    (hnq : tIn → t ∉ Q (L.mem s (prioA t))) :
    SchedRel st N T C c s' (setRel σ (R'.map UScalar.bv)
      (decide (nodeW st s' c layout.node.REPROGRAM ≠ 0#u64))) := by
  have hT := hc.tcbs
  have hN := hc.node
  have hN' : NodePlaced st T s (L.cpu s) := by rw [hc.cur]; exact hN
  have hW : ∀ w ∈ W, w ∈ T := fun w hw' => by
    rcases hW1 w hw' with rfl | hq
    · exact ht
    · exact hc.release.mem w hq
  have hk : L.ksb s' = L.ksb s := hw.1
  have haff : ∀ y ∈ T, L.mem s' (affA y) = L.mem s (affA y) := fun y hy => aff_qfoot hT hW hN hN' ht hw hy
  have hprio : ∀ y ∈ T, L.mem s' (prioA y) = L.mem s (prioA y) := fun y hy => prio_qfoot hT hW hN hN' ht hw hy
  have hinq : ∀ y ∈ T, y ≠ t → L.mem s' (inqA y) = L.mem s (inqA y) :=
    fun y hy hyt => inq_qfoot hT hW hN hN' ht hw hy hyt
  have hnode : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 56 → o.val ≠ 64 → o.val ≠ 72 → o.val ≠ 120 →
      nodeW st s' c o = nodeW st s c o := by
    intro o ho h8 h56 h64 h72 h120
    unfold Fl4Proofs.P3.Sched.nodeW
    exact node_qfoot hT hW hN hN' ht hw hN ho h8 (fun _ => by simp only [RelOffs]; omega)
      (fun _ => h120)
  have hact : nodeW st s' c layout.node.SCHED_ACTION = nodeW st s c layout.node.SCHED_ACTION :=
    hnode _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
      (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
      (by simp [layout.node.SCHED_ACTION])
  have hcd : L.mem s' (curDomA st s) = L.mem s (curDomA st s) := by
    refine hw.mem_eq (curDomA_aligned hN) (not_qfoot_out hT hW hN hc.cur ht (fun y hy => ?_) ?_)
    · have := hc.ksOut y hy; rw [curDomA_val hN]; omega
    · have h2 := hN.fits
      rw [curDomA_val hN]; simp only [LawfulStore.nodeBase] at h2 ⊢; omega
  have hmx : ∀ sc ∈ C, ScAgree st s s' sc := fun sc hsc a ha hin =>
    hw.mem_eq ha (not_qfoot_out hT hW hN hc.cur ht (hS.scOutIn hsc hin).2.2.1 (hS.scOutIn hsc hin).2.1)
  have hm := hs.rmax_eq hmx
  have hWQ : ∀ p : U64, p.val < 256 → ∀ y ∈ Q p, y ∉ W := by
    intro p hp y hy hyW
    have hyT := (hc.ready.1.rel p hp).mem y hy
    have hpy := hc.inQ p hp y hy
    rcases hW1 y hyW with rfl | hq
    · exact hWt hyW (by rw [hpy]; exact hy)
    · exact hc.excl y hyT (by rw [hpy]; exact hy) hq
  have hcore : SchedCore st T c s' Q R' := by
    refine ⟨hT, nodePlaced_ksb hN hk, hw.2.1.trans hc.cur, fun y hy => (haff y hy).trans (hc.aff y hy),
      fun y hy => (hprio y hy) ▸ hc.prio y hy, ?_, hRc, fun p' hp' y hy => ?_, fun y hy => ?_,
      fun y hy => ?_, fun y hy hq => ?_, ?_, ?_, by rw [hk]; exact hc.ksOut⟩
    · exact hc.ready.qfoot hT hW hN hN' ht hw hN (fun _ o ho _ => by simp only [RelOffs]; omega) hWQ
    · exact (hprio y ((hc.ready.1.rel p' hp').mem y hy)).trans (hc.inQ p' hp' y hy)
    · rw [hprio y hy]
      by_cases e : y = t
      · subst e
        have hq0 : (L.mem s' (inqA y) &&& sched.Q_QUEUED) ≠ 0#u64 ↔ (L.mem s (inqA y) &&& sched.Q_QUEUED) ≠ 0#u64 := by
          rw [hqq]
        rw [hq0]; exact hc.queued y hy
      · rw [hinq y hy e]; exact hc.queued y hy
    · by_cases e : y = t
      · subst e; rw [hqr, hmem]; simp
      · rw [hinq y hy e, hc.released y hy, hmem]; simp [e]
    · rw [hprio y hy] at hq
      intro hr
      rcases (hmem y).1 hr with ⟨rfl, hin⟩ | ⟨-, hr'⟩
      · exact hnq hin hq
      · exact hc.excl y hy hq hr'
    · rw [hnode _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
        (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
        (by simp [layout.node.CUR_THREAD])]; exact hc.curT
    · rw [hnode _ (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD])
        (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD])
        (by simp [layout.node.IDLE_THREAD])]; exact hc.idleT
  refine ⟨hS.placed, fun o ho => by rw [nodeAt_ksb hk]; exact hS.nodeNW o ho,
    by rw [curDomA_ksb hk]; exact hS.domNW, by rw [dtA_ksb hk]; exact hS.dtNW,
    scOut_transfer hk (SzKeep.of_kheap rfl) hS.scOut, scDisj_transfer (SzKeep.of_kheap rfl) hS.scDisj,
    by rw [hact]; exact hS.actW, by rw [hact]; exact hS.act, rfl, hs.core_eq hmx hS.core, Q, R', hcore, ?_⟩
  have w : ∀ o : U64, o.val < 64 → o.val % 8 = 0 → o.val ≠ 56 → nodeW st s' c o = nodeW st s c o :=
    fun o h1 h2 h3 => hnode o (by omega) h2 h3 (by omega) (by omega) (by omega)
  refine ⟨hs.rq, hs.rqDom, rfl, ?_, ?_, ?_, ?_, ?_, fun y hy => ?_, fun y hy => ?_, fun sc hsc => ?_,
    by rw [w _ (by simp [layout.node.IDLE_SC]) (by simp [layout.node.IDLE_SC]) (by simp [layout.node.IDLE_SC])]; exact hs.idleSc,
    by rw [dtA_ksb hk, dt_qfoot hT hW hN hc.cur ht hc.ksOut hw]; exact hs.domTime,
    by rw [w layout.node.IDLE_THREAD (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD])]; exact hs.idleTh⟩
  · rw [w layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])]
    exact hs.curThread
  · rw [w layout.node.CUR_SC (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])]
    exact hs.curSc
  · rw [w layout.node.CUR_TIME (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])]
    exact hs.curTime
  · rw [w layout.node.CONSUMED (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])]
    exact hs.consumed
  · rw [curDomA_ksb hk, hcd]; exact hs.curDom
  · obtain ⟨x, hkx, h1, h2, h3, h4⟩ := hs.tcb y hy
    have ed : L.mem s' (domA y) = L.mem s (domA y) :=
      field_qfoot hT hW hN hN' ht hw hy (K := 3432#u64) (by simp) (by simp) (by simp) (fun _ => by simp)
    have es : L.mem s' (scA y) = L.mem s (scA y) := sc_qfoot hT hW hN hN' ht hw hy
    exact ⟨x, hkx, h1, by rw [ed]; exact h2, by rw [es]; exact h3, by rw [hprio y hy]; exact h4⟩
  · rw [sc_qfoot hT hW hN hN' ht hw hy]; exact hs.scMem y hy
  · obtain ⟨x, n, hkx, e⟩ := hs.scs sc hsc
    exact ⟨x, n, hkx, e.agree (hmx sc hsc)⟩

end

/-! ## The spec's `tcb_release_enqueue` -/

section Spec
open Fl4Spec

theorem readTcbReadyTime_eq {σ : State Unit} {u p : ObjRef} {x : Tcb} {y : SchedContext} {n : Nat}
    (hk : σ.kheap u = some (.tcb x)) (hsc : x.tcbSchedContext = some p)
    (hky : σ.kheap p = some (.schedContext y n)) (hne : y.scRefills ≠ []) :
    readTcbReadyTime (Z := Unit) u σ = some (refillHd y).rTime := by
  have h0 : getTcb (Z := Unit) u σ = some x := by simp [getTcb, readObject, hk]
  have h1 : threadRead (Z := Unit) Tcb.tcbSchedContext u σ = some (some p) := by
    change Option.bind (getTcb (Z := Unit) u σ) (fun a => Lookup.oreturn a.tcbSchedContext σ) = _
    rw [h0, ← hsc]; rfl
  have h2 : readReadyTime (Z := Unit) p σ = some (refillHd y).rTime := by
    show Option.bind (readRefillHead p σ) (fun h => Lookup.oreturn h.rTime σ) = _
    rw [readRefillHead_eq hky hne]; rfl
  show Option.bind (threadRead Tcb.tcbSchedContext u σ) (fun o => Option.bind (Lookup.oassert (o ≠ none) σ)
    (fun _ => readReadyTime (the o) σ)) = _
  rw [h1]
  simp only [Option.bind_some, Lookup.oassert, ne_eq, reduceCtorEq, not_false_eq_true, ↓reduceIte, Lookup.oreturn]
  exact h2

theorem getsThe_some {α : Type} {σ : State Unit} {f : State Unit → Option α} {a : α} (h : f σ = some a) :
    NonDet.getsThe f σ = ({(a, σ)}, False) := by
  simp [NonDet.getsThe, h, NonDet.assertOpt]; rfl

/-- The spec's ordered insertion of `t` (ready time `g t`) into `qs` by the
ready times `g`. -/
def specInsT (qs : List ObjRef) (g : ObjRef → Time) (t : ObjRef) : List ObjRef :=
  qs.takeWhile (fun y => @decide (g y ≤ g t) (Classical.propDecidable _)) ++
    t :: qs.dropWhile (fun y => @decide (g y ≤ g t) (Classical.propDecidable _))

theorem readyTimesAppend_eq {σ : State Unit} (t : ObjRef) (qs : List ObjRef) (g : ObjRef → Time)
    (ht : readTcbReadyTime (Z := Unit) t σ = some (g t))
    (hq : ∀ y ∈ qs, readTcbReadyTime (Z := Unit) y σ = some (g y)) :
    readyTimesAppend (Z := Unit) t qs σ = ({(specInsT qs g t, σ)}, False) := by
  unfold readyTimesAppend orderedInsert
  rw [nd_bind_one (getsThe_some ht),
    nd_bind_one (mapM_one (fun t' => NonDet.getsThe (readTcbReadyTime (Z := Unit) t')) g qs
      (fun y hy => getsThe_some (hq y hy))),
    nd_pure_bind', nd_pure_bind']
  show ({(_, σ)}, False) = _
  congr
  simp only [List.map_append, List.map_cons, zip_takeWhile, zip_dropWhile, List.append_assoc,
    List.singleton_append, specInsT]

theorem tcbReleaseEnqueue_eq {σ : State Unit} (t : ObjRef) (g : ObjRef → Time)
    (ht : readTcbReadyTime (Z := Unit) t σ = some (g t))
    (hq : ∀ y ∈ σ.releaseQueue, readTcbReadyTime (Z := Unit) y σ = some (g y)) :
    ∃ b, tcbReleaseEnqueue (Z := Unit) t σ = ({((), setRel σ (specInsT σ.releaseQueue g t) b)}, False) := by
  unfold tcbReleaseEnqueue
  rw [nd_gets_bind, nd_bind_one (readyTimesAppend_eq t _ g ht hq)]
  unfold setReleaseQueue
  rw [nd_bind_one (show NonDet.modify (fun s : State Unit => { s with releaseQueue := specInsT σ.releaseQueue g t }) σ =
    ({((), { σ with releaseQueue := specInsT σ.releaseQueue g t })}, False) from rfl)]
  simp only [NonDet.when]
  split
  · exact ⟨true, rfl⟩
  · exact ⟨σ.reprogramTimer, rfl⟩

end Spec

/-! ## `release_enqueue` -/

/-- The spec's ready time of a thread. -/
def specRt (σ : Fl4Spec.State Unit) (u : Fl4Spec.ObjRef) : Fl4Spec.Time :=
  Fl4Spec.the (Fl4Spec.readTcbReadyTime (Z := Unit) u σ)

/-- The release queue's members have SCs and it is sorted by ready time
(l4v `valid_release_q`, `sorted_release_q`). -/
structure RelOK (σ : Fl4Spec.State Unit) : Prop where
  sc : ∀ u ∈ σ.releaseQueue, ∃ x p, σ.kheap u = some (.tcb x) ∧ x.tcbSchedContext = some p
  sorted : σ.releaseQueue.Pairwise (fun a b => specRt σ a ≤ specRt σ b)

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

theorem readyTime_rel {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {u : U64} (hu : u ∈ T) (h0 : L.mem s (scA u) ≠ 0#u64) :
    Fl4Spec.readTcbReadyTime (Z := Unit) u.bv σ = some (L.rtime s u).bv := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x, hk, -, -, hsc, -⟩ := hs.tcb u hu
  obtain ⟨y, n, hky, hy⟩ := hs.scs _ (hs.scMem u hu h0)
  rw [readTcbReadyTime_eq hk (by rw [hsc, optRef_ne h0]) hky (by rw [hy.refills]; exact refills_ne hy.wf),
    refillHd_eq hy.wf hy.refills, rf0_eq hy.wf]
  rfl

theorem takeWhile_map_bv (P : Fl4Spec.ObjRef → Bool) (Q : U64 → Bool) :
    ∀ R : List U64, (∀ y ∈ R, P y.bv = Q y) → (R.map UScalar.bv).takeWhile P = (R.takeWhile Q).map UScalar.bv
  | [], _ => rfl
  | a :: R, h => by
    simp only [List.map_cons, List.takeWhile_cons, h a List.mem_cons_self]
    split
    · rw [List.map_cons, takeWhile_map_bv P Q R fun y hy => h y (List.mem_cons_of_mem _ hy)]
    · rfl

theorem dropWhile_map_bv (P : Fl4Spec.ObjRef → Bool) (Q : U64 → Bool) :
    ∀ R : List U64, (∀ y ∈ R, P y.bv = Q y) → (R.map UScalar.bv).dropWhile P = (R.dropWhile Q).map UScalar.bv
  | [], _ => rfl
  | a :: R, h => by
    simp only [List.map_cons, List.dropWhile_cons, h a List.mem_cons_self]
    split
    · exact dropWhile_map_bv P Q R fun y hy => h y (List.mem_cons_of_mem _ hy)
    · rfl

/-- **`release_enqueue` refines `tcb_release_enqueue`**, up to
`reprogram_timer`, for a thread with an SC that is in no queue, given
`RelOK`. -/
theorem release_enqueue_refines {N T C : Set U64} {c : U64} (s : S) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hRel : RelOK σ) (t : U64) (ht : t ∈ T) (h0 : L.mem s (scA t) ≠ 0#u64)
    (hq0 : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64) (hr0 : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64) :
    sched.release_enqueue st s t ⦃ s' => ∃ q b, Fl4Spec.tcbReleaseEnqueue (Z := Unit) t.bv σ =
      ({((), setRel σ q b)}, False) ∧ (∀ u, u ∈ q ↔ u = t.bv ∨ u ∈ σ.releaseQueue) ∧ FootEq N T (L.mem s) (L.mem s') ∧
      SchedRel st N T C c s' (setRel σ q (decide (nodeW st s' c layout.node.REPROGRAM ≠ 0#u64))) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hT := hc.tcbs
  have haf := hc.aff t ht
  have hN : NodePlaced st T s (L.mem s (affA t)) := by rw [haf]; exact hc.node
  have hN' : NodePlaced st T s (L.cpu s) := by rw [hc.cur]; exact hc.node
  have htR : t ∉ R := fun hm => (hc.released t ht).2 hm hr0
  have hnq : t ∉ Q (L.mem s (prioA t)) := fun hm => (hc.queued t ht).2 hm hq0
  have hrel : QueueRel (L.mem s) T .Sched (L.relQ s (L.mem s (affA t))) R := by rw [haf]; exact hc.release
  have hW : ∀ w ∈ t :: R, w ∈ T := by
    intro w hw; rcases List.mem_cons.1 hw with rfl | hw
    · exact ht
    · exact hc.release.mem w hw
  -- the release queue's members have SCs; it is sorted
  have hRsc : ∀ u ∈ R, L.mem s (scA u) ≠ 0#u64 := by
    intro u hu h0'
    obtain ⟨x, p, hk, hsc⟩ := hRel.sc u.bv (by rw [hs.rel]; exact List.mem_map_of_mem hu)
    obtain ⟨x', hk', -, -, hsc', -⟩ := hs.tcb u (hc.release.mem u hu)
    rw [hk] at hk'; cases hk'
    rw [hsc', h0', optRef_zero] at hsc; cases hsc
  have hrt : ∀ u ∈ R, specRt σ u.bv = (L.rtime s u).bv := fun u hu => by
    unfold specRt; rw [readyTime_rel hS (hc.release.mem u hu) (hRsc u hu)]; rfl
  have hsort : TimeSorted (L.rtime s) R := by
    have := hRel.sorted
    rw [hs.rel, List.pairwise_map] at this
    refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab => ?_) this
    rw [hrt a ha, hrt b hb, BitVec.le_def] at hab
    exact hab
  set g : Fl4Spec.ObjRef → Fl4Spec.Time := fun p => (L.rtime s ⟨p⟩).bv
  obtain ⟨b, he⟩ := tcbReleaseEnqueue_eq (σ := σ) t.bv g (readyTime_rel hS ht h0) (by
    rw [hs.rel]; intro y hy
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hy
    exact readyTime_rel hS (hc.release.mem u hu) (hRsc u hu))
  have hP : ∀ y ∈ R, @decide (g y.bv ≤ g t.bv) (Classical.propDecidable _) = decide (L.rtime s y ≤ L.rtime s t) :=
    fun y _ => decide_eq_decide.2 (u64_le_bv _ _).symm
  have hq' : specInsT σ.releaseQueue g t.bv = (relIns (L.rtime s) (L.rtime s t) t R).map UScalar.bv := by
    rw [relIns_eq_sorted _ _ t R hsort, hs.rel]
    unfold specInsT
    rw [takeWhile_map_bv _ _ R hP, dropWhile_map_bv _ _ R hP]
    simp
  have h1 := sched.release_enqueue.rel s t R hT ht htR hN hN' hrel
  have h2 := sched.release_enqueue.foot s t R hT ht htR hN hN' hrel
  refine WP.spec_mono (WP.spec_and h1 h2) ?_
  rintro s' ⟨hRc, hw, hinq⟩
  rw [haf] at hRc hw
  refine ⟨_, b, he, fun u => ?_, qfoot_footEq hS hc ht hW hw, ?_⟩
  · rw [hq', hs.rel]
    simp only [List.mem_map, mem_relIns]
    constructor
    · rintro ⟨v, hv | hv, rfl⟩
      · exact Or.inl (by rw [hv])
      · exact Or.inr ⟨v, hv, rfl⟩
    · rintro (rfl | ⟨v, hv, rfl⟩)
      · exact ⟨t, Or.inl rfl, rfl⟩
      · exact ⟨v, Or.inr hv, rfl⟩
  rw [hq']
  exact hS.rstep hc hs ht (W := t :: R) (tIn := True) (fun w hw => List.mem_cons.1 hw) (fun _ => hnq) hw hRc
    (fun y => by rw [mem_relIns]; by_cases e : y = t <;> simp [e])
    (by rw [hinq, or_qr_qr]; simpa using qr_ne) (by rw [hinq, or_qr_qq]) (fun _ => hnq)

end

end

end Fl4Proofs.P3.Sched
