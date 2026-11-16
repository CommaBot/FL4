/-
P3 (DESIGN.md §9), IPC and scheduling: **`set_priority` on `IRel`**
(TcbXRest's SetPriority, for the Thread cap at `XTop`).

* `SchedRel.prio_wr`: the scheduler relation across a priority write of a
  thread in no ready queue (the spec's `thread_set_priority`).
-/
import Fl4Proofs.P3.IpcSendDon
import Fl4Proofs.P3.SchedQueue
import Fl4Proofs.P3.SchedSwitch
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp

noncomputable section

section Prio
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

theorem specPrio_toNat {v : U64} (hv : v.val < 256) : (specPrio v).toNat = v.val := by
  unfold specPrio; simp [BitVec.toNat_ofNat]; omega

set_option maxHeartbeats 4000000 in
/-- **The scheduler relation across a priority write** of a thread in no
ready queue: FL4 writes its `PRIO` word, the spec its `tcb_priority`. -/
theorem SchedRel.prio_wr {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {t : U64} (ht : t ∈ T) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x))
    (hq0 : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64) (v : U64) (hv : v.val < 256) :
    SchedRel st N T C c (L.wr s (prioA t) v) (updK σ t.bv (.tcb { x with tcbPriority := specPrio v })) := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hT := hc.tcbs
  have hta := hT t ht
  have hpa := (a_prio hta).1
  have hpv := val_prio hta
  have h12 : (2 : ℕ) ^ 12 = 4096 := by norm_num
  set s' := L.wr s (prioA t) v with hs'
  have hm : ∀ b, Aligned b → b.val ≠ t.val + 3448 → L.mem s' b = L.mem s b :=
    fun b hb h => rd_wr_ne hpa hb (fun e => h (by rw [← e, hpv]))
  have hk' : L.ksb s' = L.ksb s := L.ksb_wr _ _ _
  have hcpu : L.cpu s' = L.cpu s := L.cpu_wr _ _ _
  have hnode : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o) :=
    fun o ho h8 => hm _ (nodeAt_aligned hc.node ho h8) (by have := nodeAt_out hc.node ho ht; omega)
  have hnW : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → nodeW st s' c o = nodeW st s c o := fun o ho h8 => by
    unfold Fl4Proofs.P3.Sched.nodeW; rw [nodeAt_ksb hk']; exact hnode o ho h8
  -- the TCB words other than `t`'s priority
  have hfield : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (y ≠ t ∨ K.val ≠ 3448) →
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := by
    intro y hy K hK hK8 hne
    have hya := hT y hy
    refine hm _ (field_aligned hya hK hK8) ?_
    rw [tfield_val hya hK]
    by_cases e : y = t
    · subst e; rcases hne with h | h
      · exact absurd rfl h
      · omega
    · have a1 := hta.align; have a2 := hya.align
      have := val_ne_of_ne e
      rw [h12] at a1 a2
      omega
  have hlink : ∀ y ∈ T, L.mem s' (nextA .Sched y) = L.mem s (nextA .Sched y) ∧
      L.mem s' (prevA .Sched y) = L.mem s (prevA .Sched y) := fun y hy =>
    ⟨hfield y hy _ (by simp [nextOff]) (by simp [nextOff]) (Or.inr (by simp [nextOff])),
      hfield y hy _ (by simp [prevOff]) (by simp [prevOff]) (Or.inr (by simp [prevOff]))⟩
  have hprio : ∀ y ∈ T, y ≠ t → L.mem s' (prioA y) = L.mem s (prioA y) := fun y hy e =>
    hfield y hy _ (by simp) (by simp) (Or.inl e)
  have hinq : ∀ y ∈ T, L.mem s' (inqA y) = L.mem s (inqA y) := fun y hy =>
    hfield y hy _ (by simp) (by simp) (Or.inr (by simp))
  have hnq : ∀ p : U64, p.val < 256 → t ∉ Q p := by
    intro p hp hm'
    have e := hc.inQ p hp t hm'
    exact ((hc.queued t ht).2 (by rw [e]; exact hm')) hq0
  have hmx : ∀ sc ∈ C, ScAgree st s s' sc := fun sc hsc a ha hin =>
    hm a ha (by have := (hS.scOutIn hsc hin).2.2.1 t ht; omega)
  have hks : ∀ b, Aligned b → (L.ksb s).val ≤ b.val → b.val < (L.ksb s).val + 13568 → L.mem s' b = L.mem s b :=
    fun b hb h1 h2 => hm b hb (by have := hc.ksOut t ht; rw [h12] at this; omega)
  have hcd : L.mem s' (curDomA st s) = L.mem s (curDomA st s) := by
    have h2 := hc.node.fits
    have hv' : (curDomA st s).val = (L.ksb s).val + 8 := by
      simp only [LawfulStore.nodeBase] at h2
      simp [curDomA, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    have hal : Aligned (curDomA st s) := by
      have h1 := hc.node.align
      unfold Aligned; rw [hv']; simp only [LawfulStore.nodeBase] at h1; omega
    exact hks _ hal (by rw [hv']; omega) (by rw [hv']; omega)
  have hdt : L.mem s' (dtA st s) = L.mem s (dtA st s) := by
    have hv' := dtA_val hc.node
    exact hks _ (dtA_aligned hc.node) (by rw [hv']; omega) (by rw [hv']; omega)
  have hviews : ViewsEq st s s' c := by
    refine ⟨fun p hp => ?_, ?_, fun g hg => ?_⟩
    · simp only [LawfulStore.rqQ, nodeAt_ksb hk']
      rw [hnode _ (by rw [rqOff_val hp]; omega) (by rw [rqOff_val hp]; omega),
        hnode _ (by rw [rqTailOff_val hp]; omega) (by rw [rqTailOff_val hp]; omega)]
    · simp only [LawfulStore.l1W, nodeAt_ksb hk']
      exact hnode _ (by rw [l1Off_val]; omega) (by rw [l1Off_val])
    · simp only [LawfulStore.l2W, nodeAt_ksb hk']
      exact hnode _ (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega)
  have hrel : L.relQ s' c = L.relQ s c := by
    simp only [LawfulStore.relQ, nodeAt_ksb hk']
    rw [hnode _ (by rw [relh_val]; omega) (by rw [relh_val]), hnode _ (by rw [relt_val]; omega) (by rw [relt_val])]
  have hcore : SchedCore st T c s' Q R := by
    refine ⟨hT, nodePlaced_ksb hc.node hk', hcpu.trans hc.cur,
      fun y hy => (hfield y hy _ (by simp) (by simp) (Or.inr (by simp))).trans (hc.aff y hy),
      fun y hy => ?_, ⟨hc.ready.1.agree hviews.1 fun p hp y hy => hlink y ((hc.ready.1.rel p hp).mem y hy),
        hc.ready.2.views hviews⟩,
      by rw [hrel]; exact ⟨hc.release.nodup, hc.release.mem, hc.release.head, hc.release.last,
        hc.release.seg.congr fun y hy => ⟨(hlink y (hc.release.mem y hy)).2, (hlink y (hc.release.mem y hy)).1⟩⟩,
      fun p hp y hy => ?_, fun y hy => ?_, fun y hy => by rw [hinq y hy]; exact hc.released y hy,
      fun y hy hq => ?_, ?_, ?_, by rw [hk']; exact hc.ksOut⟩
    · by_cases e : y = t
      · subst e; rw [hs', rd_wr_eq hpa]; exact hv
      · rw [hprio y hy e]; exact hc.prio y hy
    · have hyT := (hc.ready.1.rel p hp).mem y hy
      have e : y ≠ t := fun e => hnq p hp (e ▸ hy)
      rw [hprio y hyT e]; exact hc.inQ p hp y hy
    · rw [hinq y hy]
      by_cases e : y = t
      · subst e; rw [hs', rd_wr_eq hpa]
        exact ⟨fun h => absurd hq0 h, fun h => absurd h (hnq v hv)⟩
      · rw [hprio y hy e]; exact hc.queued y hy
    · by_cases e : y = t
      · subst e; rw [hs', rd_wr_eq hpa] at hq; exact absurd hq (hnq v hv)
      · rw [hprio y hy e] at hq; exact hc.excl y hy hq
    · rw [hnW _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])]; exact hc.curT
    · rw [hnW _ (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD])]; exact hc.idleT
  have hact : nodeW st s' c layout.node.SCHED_ACTION = nodeW st s c layout.node.SCHED_ACTION :=
    hnW _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
  have hz : SzKeep σ (updK σ t.bv (.tcb { x with tcbPriority := specPrio v })) :=
    SzKeep.updK hk (fun _ _ h => by cases h)
  have hkO : ∀ q, q ≠ t.bv → (updK σ t.bv (.tcb { x with tcbPriority := specPrio v })).kheap q = σ.kheap q :=
    fun q e => by simp [updK, Function.update_of_ne e]
  refine ⟨hS.placed, fun o ho => by rw [nodeAt_ksb hk']; exact hS.nodeNW o ho,
    by rw [curDomA_ksb hk']; exact hS.domNW, by rw [dtA_ksb hk']; exact hS.dtNW,
    scOut_transfer hk' hz hS.scOut, scDisj_transfer hz hS.scDisj, by rw [hact]; exact hS.actW,
    by rw [hact]; exact hS.act,
    (by rw [hnW _ (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])]; exact hS.repr),
    hs.core_eq hmx hS.core, Q, R, hcore, ?_⟩
  refine ⟨hs.rq, hs.rqDom, hs.rel, ?_, ?_, ?_, ?_, ?_, fun y hy => ?_, fun y hy => ?_, fun sc hsc => ?_,
    by rw [hnW _ (by simp [layout.node.IDLE_SC]) (by simp [layout.node.IDLE_SC])]; exact hs.idleSc,
    by rw [dtA_ksb hk', hdt]; exact hs.domTime,
    by rw [hnW _ (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD])]; exact hs.idleTh⟩
  · rw [hnW _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])]; exact hs.curThread
  · rw [hnW _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])]; exact hs.curSc
  · rw [hnW _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])]; exact hs.curTime
  · rw [hnW _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])]; exact hs.consumed
  · rw [curDomA_ksb hk', hcd]; exact hs.curDom
  · obtain ⟨y0, hky, h1, h2, h3, h4⟩ := hs.tcb y hy
    have ed : L.mem s' (domA y) = L.mem s (domA y) := hfield y hy _ (by simp) (by simp) (Or.inr (by simp))
    have es : L.mem s' (scA y) = L.mem s (scA y) := hfield y hy _ (by simp) (by simp) (Or.inr (by simp))
    by_cases e : y = t
    · subst e; rw [hk] at hky; cases hky
      refine ⟨{ x with tcbPriority := specPrio v }, by simp [updK], h1, by rw [ed]; exact h2, by rw [es]; exact h3, ?_⟩
      rw [hs', rd_wr_eq hpa]; exact (specPrio_toNat hv).symm
    · refine ⟨y0, by rw [hkO _ (fun h => e (eq_of_bv h))]; exact hky, h1, by rw [ed]; exact h2, by rw [es]; exact h3,
        by rw [hprio y hy e]; exact h4⟩
  · have es : L.mem s' (scA y) = L.mem s (scA y) := hfield y hy _ (by simp) (by simp) (Or.inr (by simp))
    rw [es]; exact hs.scMem y hy
  · obtain ⟨y0, n, hky, e⟩ := hs.scs sc hsc
    have hne : sc.bv ≠ t.bv := fun h => by rw [h, hk] at hky; cases hky
    exact ⟨y0, n, by rw [hkO _ hne]; exact hky, e.agree (hmx sc hsc)⟩

end Prio

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Reorder
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T E R : Set U64} {B : Set (U64 × Fl4Spec.Word)}

/-- **`reorder_ep`** of a member, with its frame: `t` taken out and put back
in priority order, the state kept. -/
theorem ep_reorder_full (hP : EPlaced T E R B) (s : S) {e : U64} (he : e ∈ E) (t : obj.Tcb) (xs : List U64)
    (h : QueueRel (L.mem s) T .Ep (qOf (L.mem s) e) xs) (ht : t ∈ xs) :
    endpoint.reorder_ep st s e t ⦃ s' =>
      QueueRel (L.mem s') T .Ep (qOf (L.mem s') e)
        (insPrio (fun y => L.mem s (prioA y)) (L.mem s (prioA t)) t (xs.erase t)) ∧
      stOf (L.mem s') e = stOf (L.mem s) e ∧ QAgree T e xs (L.mem s) (L.mem s') ∧
      WritesIn st s s' (EWrite T E R B) ⦄ := by
  have hE := hP.epPlaced he
  have hT := hP.tcb
  unfold endpoint.reorder_ep
  step with P1.obj.Ep.state.spec as ⟨st0, hst0⟩
  step with P1.endpoint.get_queue.spec as ⟨q, q_post⟩
  subst q_post hst0
  refine WP.spec_bind (tcbqueue.remove.rel s .Ep _ t xs hT h ht) ?_
  rintro ⟨q1, s1⟩ h1
  simp only [WP.uncurry'_pair] at h1
  obtain ⟨hr1, hf1, -, -⟩ := h1
  have htT : t ∈ T := h.mem t ht
  have hn : t ∉ xs.erase t := h.nodup.not_mem_erase
  refine WP.spec_bind (tcbqueue.append_by_prio.rel s1 .Ep q1 t _ hT hr1 htT hn) ?_
  rintro ⟨q2, s2⟩ h2
  simp only [WP.uncurry'_pair] at h2
  obtain ⟨hr2, hf2⟩ := h2
  have hW : ∀ w ∈ xs, w ∈ T := h.mem
  have hWa : ∀ w ∈ xs, TcbAddr w := h.addr hT
  have hpr : ∀ y, TcbAddr y → L.mem s1 (prioA y) = L.mem s (prioA y) := fun y hy => prio_framed hy hWa hf1
  have hf : Framed st .Ep xs s s2 := hf1.trans (hf2.mono fun w hw => by
    rcases List.mem_cons.1 hw with rfl | hw
    · exact ht
    · exact List.mem_of_mem_erase hw)
  step with P1.endpoint.set_queue.spec as ⟨s3, hs3⟩
  subst hs3
  obtain ⟨h3, h4⟩ := ep_set_queue (state := L.epState s e) hT hE hr2
  obtain ⟨q1', q2'⟩ := qagree_of hP he hW hf q2.head ((q2.end &&& ~~~3#u64) ||| (L.epState s e &&& 3#u64))
  refine ⟨?_, by rw [← epState_eq, h4, epState_and3, epState_eq], q1', q2'⟩
  have e' : insPrio (fun y => L.mem s1 (prioA y)) (L.mem s1 (prioA t)) t (xs.erase t) =
      insPrio (fun y => L.mem s (prioA y)) (L.mem s (prioA t)) t (xs.erase t) := by
    rw [hpr t (hWa t ht)]
    exact insPrio_congr fun y hy => hpr y (hWa y (List.mem_of_mem_erase hy))
  rw [← e']; exact h3

/-- The spec's `reorder_ep` of a queued thread. -/
theorem reorderEp_eq {σ : Fl4Spec.State Unit} {e t : Fl4Spec.ObjRef} {x : Fl4Spec.Endpoint} {xt : Fl4Spec.Tcb}
    (hk : σ.kheap e = some (.endpoint x)) (hkt : σ.kheap t = some (.tcb xt)) (htq : t ∈ x.epQueue)
    (g : Fl4Spec.ObjRef → Fl4Spec.Priority)
    (hq : ∀ y ∈ Fl4Spec.removeAll t x.epQueue, ∃ z, σ.kheap y = some (.tcb z) ∧ z.tcbPriority = g y) :
    Fl4Spec.reorderEp (Z := Unit) e t σ = ({((), updK σ e (.endpoint (Fl4Spec.updateEpQueue x
      (specIns (Fl4Spec.removeAll t x.epQueue) g xt.tcbPriority t) true)))}, False) := by
  have hne : x.epQueue ≠ [] := List.ne_nil_of_mem htq
  have hni : x ≠ .idleEP := by rintro rfl; exact hne rfl
  unfold Fl4Spec.reorderEp
  rw [nd_bind_one (getEndpoint_eq hk), nd_bind_one (assert_true' hni σ), nd_pure_bind',
    nd_bind_one (assert_true' hne σ), nd_pure_bind', nd_bind_one (tcbAppend_eq hkt _ g hq)]
  exact setEndpoint_eq _ hk

variable {SR : S → Fl4Spec.State Unit → Prop}

set_option maxHeartbeats 4000000 in
/-- **`reorder_ep` refines `reorder_ep`** for a thread queued on the
endpoint, the rest of the queue sorted by priority. -/
theorem ep_reorder_rel (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B) (s : S) (σ : Fl4Spec.State Unit)
    (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ) {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb}
    (hkt : σ.kheap t.bv = some (.tcb xt)) {e : U64} (he : e ∈ E) {x : Fl4Spec.Endpoint}
    (hk : σ.kheap e.bv = some (.endpoint x)) (htq : t.bv ∈ x.epQueue)
    (hsort : ∀ xs, QueueRel (L.mem s) T .Ep (qOf (L.mem s) e) xs →
      PrioSorted (fun y => L.mem s (prioA y)) (xs.erase t)) :
    endpoint.reorder_ep st s e t ⦃ s' =>
      ∃ σ', Fl4Spec.reorderEp (Z := Unit) e.bv t.bv σ = ({((), σ')}, False) ∧
        EpStateRel T E R B (L.mem s') σ' ∧ SR s' σ' ∧ ∃ y, σ' = updK σ e.bv (.endpoint y) ⦄ := by
  have hx := hR.at_ep he hk
  have hxt := hR.at_tcb ht hkt
  obtain ⟨xs, hQ, hxs, hB⟩ := hx.queue
  have htxs : t ∈ xs := by
    rw [hxs] at htq; obtain ⟨y, hy, ey⟩ := List.mem_map.1 htq; rw [← eq_of_bv ey]; exact hy
  have hnd := hQ.nodup
  have hsorted := hsort xs hQ
  refine WP.spec_mono (ep_reorder_full hP s he t xs hQ htxs) ?_
  rintro s' ⟨hA1, hA2, hA3, hA4⟩
  set ys := insPrio (fun y => L.mem s (prioA y)) (L.mem s (prioA t)) t (xs.erase t) with hys
  have hrm : Fl4Spec.removeAll t.bv x.epQueue = (xs.erase t).map UScalar.bv := by rw [hxs]; exact removeAll_map hnd t
  have hq : ∀ y ∈ Fl4Spec.removeAll t.bv x.epQueue, ∃ z, σ.kheap y = some (.tcb z) ∧ z.tcbPriority = prioOf σ y := by
    intro y hy
    rw [hrm] at hy
    obtain ⟨y', hy'x, rfl⟩ := List.mem_map.1 hy
    obtain ⟨z, hz, -⟩ := hR.tcb y' (hQ.mem y' (List.mem_of_mem_erase hy'x))
    exact ⟨z, hz, by simp [prioOf, hz]⟩
  have hlist : specIns (Fl4Spec.removeAll t.bv x.epQueue) (prioOf σ) xt.tcbPriority t.bv = ys.map UScalar.bv := by
    rw [specIns, hrm, List.takeWhile_map, List.dropWhile_map]
    simp only [ys, insPrio_eq_sorted _ _ t _ hsorted, List.map_append, List.map_cons]
    have hc' : ∀ y ∈ xs.erase t, ((fun y => @decide (prioOf σ y ≥ xt.tcbPriority) (Classical.propDecidable _)) ∘
        UScalar.bv) y = (fun y => !decide (L.mem s (prioA t) > L.mem s (prioA y))) y := by
      intro y hy
      obtain ⟨z, hz, hzr⟩ := hR.tcb y (hQ.mem y (List.mem_of_mem_erase hy))
      have hpz : prioOf σ y.bv = z.tcbPriority := by simp [prioOf, hz]
      simp only [Function.comp, hpz]
      convert (prio_ge_iff _ _ _ _ hxt.prio hzr.prio).symm using 2
    rw [takeWhile_congr' hc', dropWhile_congr' hc']
  refine ⟨_, by rw [reorderEp_eq hk hkt htq (prioOf σ) hq, hlist], ?_, hH.stable _ _ _ _ hSR hA4 (EpStep.ep hk),
    _, rfl⟩
  refine hR.upd_ep hP he _ (hA3.mono fun b ⟨_, h2, h3⟩ => ⟨h2, fun ⟨w, hw, hl⟩ => h3 ⟨w, hQ.mem w hw,
    (hB w hw).1, hl⟩⟩) ?_
  have hmem : ∀ y ∈ ys, y ∈ xs := fun y hy => by
    rcases mem_insPrio_sorted hsorted hy with rfl | hy'
    · exact htxs
    · exact List.mem_of_mem_erase hy'
  have hne : ys ≠ [] := insPrio_ne_nil hsorted
  have hkeep : ∀ y ∈ ys, L.mem s' (tStA y) = L.mem s (tStA y) ∧ L.mem s' (tBlockA y) = L.mem s (tBlockA y) := by
    intro y hy
    have hyT := hQ.mem y (hmem y hy)
    have hya := hP.tcb y hyT
    have g : ∀ a : U64, Aligned a → TF y a → L.mem s' a = L.mem s a := by
      intro a ha hf
      refine hA3 a ha ⟨fun hw => ?_, fun ⟨w, hw, hl⟩ => ?_⟩
      · have := hP.et e he y hyT; unfold EW at hw; have := hf.range; omega
      · by_cases ew : w = y
        · subst ew; exact hl.not_tf hf
        · have := tcb_disj hP (hQ.mem w hw) hyT (Ne.symm ew); unfold TL at hl; have := hf.range; omega
    exact ⟨g _ (a_st hya).1 (a_st hya).2, g _ (a_blk hya).1 (a_blk hya).2⟩
  cases x with
  | idleEP => simp [Fl4Spec.Endpoint.epQueue] at htq
  | sendEP q =>
    obtain ⟨h1, xs0, -, hq0, -, h4⟩ := hx
    have hxs0 : xs0 = xs := by
      apply List.map_injective_iff.2 (fun a b h => eq_of_bv h)
      rw [← hq0]; exact hxs
    subst hxs0
    refine ⟨by rw [hA2]; exact h1, ys, hne, rfl, hA1, fun y hy => ?_⟩
    obtain ⟨k1, k2⟩ := hkeep y hy
    obtain ⟨q1, q2⟩ := h4 y (hmem y hy)
    exact ⟨by rw [k1]; exact q1, by rw [k2]; exact q2⟩
  | recvEP q =>
    obtain ⟨h1, xs0, -, hq0, -, h4⟩ := hx
    have hxs0 : xs0 = xs := by
      apply List.map_injective_iff.2 (fun a b h => eq_of_bv h)
      rw [← hq0]; exact hxs
    subst hxs0
    refine ⟨by rw [hA2]; exact h1, ys, hne, rfl, hA1, fun y hy => ?_⟩
    obtain ⟨k1, k2⟩ := hkeep y hy
    obtain ⟨q1, q2⟩ := h4 y (hmem y hy)
    exact ⟨by rw [k1]; exact q1, by rw [k2]; exact q2⟩

end Reorder

end

end Fl4Proofs.P3.Endp

namespace Fl4Proofs.P3.Notif
open fl4_core Fl4Proofs.P1

noncomputable section

section ReorderN
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {N T : Set U64}

/-- **`reorder_ntfn`** of a member, with its frame. -/
theorem ntfn_reorder_full (hP : NPlaced T N) (s : S) {n : U64} (hn : n ∈ N) (t : obj.Tcb) (xs : List U64)
    (h : QueueRel (L.mem s) T .Ep (qOf (L.mem s) n) xs) (ht : t ∈ xs) :
    notification.reorder_ntfn st s n t ⦃ s' =>
      QueueRel (L.mem s') T .Ep (qOf (L.mem s') n)
        (insPrio (fun y => L.mem s (prioA y)) (L.mem s (prioA t)) t (xs.erase t)) ∧
      stOf (L.mem s') n = stOf (L.mem s) n ∧ QKeeps st N T n xs s s' ⦄ := by
  have hE : EpPlaced T n :=
    ⟨by have := (hP.ntfn n hn).align; omega, by have := (hP.ntfn n hn).fits; omega,
     fun t ht => by have := hP.disj n hn t ht; omega⟩
  have hT := hP.tcb
  unfold notification.reorder_ntfn
  step with P1.obj.Ntfn.state.spec as ⟨st0, hst0⟩
  step with P1.notification.get_queue.spec as ⟨q, q_post⟩
  subst q_post hst0
  refine WP.spec_bind (tcbqueue.remove.rel s .Ep _ t xs hT h ht) ?_
  rintro ⟨q1, s1⟩ h1
  simp only [WP.uncurry'_pair] at h1
  obtain ⟨hr1, hf1, -, -⟩ := h1
  have htT : t ∈ T := h.mem t ht
  have hn' : t ∉ xs.erase t := h.nodup.not_mem_erase
  refine WP.spec_bind (tcbqueue.append_by_prio.rel s1 .Ep q1 t _ hT hr1 htT hn') ?_
  rintro ⟨q2, s2⟩ h2
  simp only [WP.uncurry'_pair] at h2
  obtain ⟨hr2, hf2⟩ := h2
  have hW : ∀ w ∈ xs, w ∈ T := h.mem
  have hWa : ∀ w ∈ xs, TcbAddr w := h.addr hT
  have hpr : ∀ y, TcbAddr y → L.mem s1 (prioA y) = L.mem s (prioA y) := fun y hy => prio_framed hy hWa hf1
  have hf : Framed st .Ep xs s s2 := hf1.trans (hf2.mono fun w hw => by
    rcases List.mem_cons.1 hw with rfl | hw
    · exact ht
    · exact List.mem_of_mem_erase hw)
  step with P1.notification.set_queue.spec as ⟨s3, hs3⟩
  subst hs3
  obtain ⟨h3, h4⟩ := ep_set_queue (state := L.epState s n) hT hE hr2
  refine ⟨?_, by rw [← epState_eq, h4, epState_and3, epState_eq], qkeeps_of hP hn hW hf _ _⟩
  have e' : insPrio (fun y => L.mem s1 (prioA y)) (L.mem s1 (prioA t)) t (xs.erase t) =
      insPrio (fun y => L.mem s (prioA y)) (L.mem s (prioA t)) t (xs.erase t) := by
    rw [hpr t (hWa t ht)]
    exact insPrio_congr fun y hy => hpr y (hWa y (List.mem_of_mem_erase hy))
  rw [← e']; exact h3

/-- The spec's `reorder_ntfn` of a queued thread. -/
theorem reorderNtfn_eq {σ : Fl4Spec.State Unit} {n t : Fl4Spec.ObjRef} {x : Fl4Spec.Notification} {xt : Fl4Spec.Tcb}
    (hk : σ.kheap n = some (.notification x)) (hkt : σ.kheap t = some (.tcb xt)) {q : List Fl4Spec.ObjRef}
    (hw : x.ntfnObj = .waitingNtfn q) (htq : t ∈ q)
    (g : Fl4Spec.ObjRef → Fl4Spec.Priority)
    (hq : ∀ y ∈ Fl4Spec.removeAll t q, ∃ z, σ.kheap y = some (.tcb z) ∧ z.tcbPriority = g y) :
    Fl4Spec.reorderNtfn (Z := Unit) n t σ = ({((), updK σ n (.notification
      { x with ntfnObj := .waitingNtfn (specIns (Fl4Spec.removeAll t q) g xt.tcbPriority t) }))}, False) := by
  have hne : q ≠ [] := List.ne_nil_of_mem htq
  unfold Fl4Spec.reorderNtfn
  rw [nd_bind_one (getNotification_eq hk), nd_bind_one (Endp.assert_true' (by rw [hw]; rfl) σ), nd_pure_bind']
  simp only [Fl4Spec.ntfnQueueOf, hw, Fl4Spec.Ntfn.ntfnQueue]
  rw [nd_bind_one (Endp.assert_true' hne σ), nd_pure_bind', nd_bind_one (tcbAppend_eq hkt _ g hq)]
  exact setNotification_eq _ hk

end ReorderN

end

end Fl4Proofs.P3.Notif

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

section PrioW
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- A TCB's endpoint relation across a write of its priority word. -/
theorem _root_.Fl4Proofs.P3.Endp.TcbRelE.prio_wr {m m' : U64 → U64} {t : U64} {x : Fl4Spec.Tcb} (ht : TcbAddr t) (h : TcbRelE R m t x)
    (hA : ∀ b, Aligned b → b.val ≠ t.val + 3448 → m' b = m b) (pr : Fl4Spec.Priority)
    (hp : (m' (prioA t)).val = pr.toNat) : TcbRelE R m' t { x with tcbPriority := pr } := by
  have g : ∀ {b : U64}, Aligned b → b.val ≠ t.val + 3448 → m' b = m b := fun hb hv => hA _ hb hv
  refine ⟨?_, fun e he => ?_, fun e d hs => ?_, fun e r d hs => ?_, fun r hs => ?_, fun r => ?_, hp, ?_, ?_, ?_, ?_⟩
  · rw [g (a_st ht).1 (by rw [val_st ht]; omega)]; exact h.st
  · rw [g (a_blk ht).1 (by rw [val_blk ht]; omega)]; exact h.blk e he
  · rw [g (a_badge ht).1 (by rw [val_badge ht]; omega), g (a_flags ht).1 (by rw [val_flags ht]; omega)]
    exact h.send e d hs
  · rw [g (a_reply ht).1 (by rw [val_reply ht]; omega)]; exact h.recv e r d hs
  · rw [g (a_reply ht).1 (by rw [val_reply ht]; omega)]; exact h.reply r hs
  · rw [g (a_reg ht r).1 (by rw [regA_val ht (regIdx_lt r)]; have := regIdx_lt r; omega)]; exact h.regs r
  · rw [g (a_fault ht).1 (by rw [val_fault ht]; omega)]; exact h.fault0
  · rw [g (a_fault ht).1 (by rw [val_fault ht]; omega)]; exact h.faultT
  · rw [g (a_bound ht).1 (by rw [val_bound ht]; omega)]; exact h.bound
  · exact h.faultR.congr' ht (fun v => v ≠ t.val + 3448) hA fun k h1 h2 => by omega

/-- The notification relation across a write of a TCB's priority word. -/
theorem ntfn_upd_prio {Z : Type} (hP : CPlaced N T E R B) {m m' : U64 → U64} {σ : Fl4Spec.State Z}
    (hR : NtfnStateRel N T m σ) {t : U64} (ht : t ∈ T) (x' : Fl4Spec.Tcb)
    (hA : ∀ a, Aligned a → a.val ≠ t.val + 3448 → m' a = m a)
    (hx : TcbRel1 m' t x') : NtfnStateRel N T m' (updK σ t.bv (.tcb x')) := by
  have hta := hP.n.tcb t ht
  let P : Nat → Prop := fun v => v ≠ t.val + 3448
  have h12 : (2 : ℕ) ^ 12 = 4096 := by norm_num
  refine hR.upd_tcb ht x' (fun n hn => nwordsEq_of (hP.n.ntfn n hn) P hA fun k hk => ?_)
    (fun y hy hne => tfieldsEq_of (hP.n.tcb y hy) P hA ?_ ?_ ?_ ?_)
    (fun y hy => tlinksEq_of (hP.n.tcb y hy) P hA ?_ ?_) (Or.inr ⟨hA _ (a_st hta).1 (by rw [val_st hta]; omega),
      hA _ (a_blk hta).1 (by rw [val_blk hta]; omega)⟩) hx
  · have := hP.n.disj n hn t ht; show _ ≠ _; omega
  all_goals
    show _ ≠ _
    first
    | (have := tcb_disj hP.e ht hy hne; omega)
    | (by_cases e : y = t
       · subst e; omega
       · have := tcb_disj hP.e ht hy e; omega)

set_option maxHeartbeats 4000000 in
/-- **`IRel` across a priority write** of a thread in no ready queue (FL4's
`PRIO` word, the spec's `thread_set_priority`). -/
theorem prio_wr_irel (hP0 : IPlaced N T E R B) {s : S} {σ : Fl4Spec.State Unit}
    (hX : IRel st th cr N T C E R B c s σ) {t : U64} (ht : t ∈ T) {x : Fl4Spec.Tcb}
    (hk : σ.kheap t.bv = some (.tcb x)) (hq0 : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64) (v : U64)
    (hv : v.val < 256) :
    IRel st th cr N T C E R B c (L.wr s (prioA t) v) (updK σ t.bv (.tcb { x with tcbPriority := specPrio v })) := by
  have hP := hP0.e
  have hta := hP.tcb t ht
  have hpa := (a_prio hta).1
  have hpv := val_prio hta
  have hA : ∀ b, Aligned b → b.val ≠ t.val + 3448 → L.mem (L.wr s (prioA t) v) b = L.mem s b :=
    fun b hb h => rd_wr_ne hpa hb (fun e => h (by rw [← e, hpv]))
  have hpr : (L.mem (L.wr s (prioA t) v) (prioA t)).val = (specPrio v).toNat := by
    rw [rd_wr_eq hpa, specPrio_toNat hv]
  obtain ⟨hIR, hT, hSE⟩ := hX
  have hE := hIR.toE
  have hN := hIR.toN
  obtain ⟨x0, hk0, hxe⟩ := hE.tcb t ht
  rw [hk] at hk0; cases hk0
  have hE' : EpStateRel T E R B (L.mem (L.wr s (prioA t) v)) (updK σ t.bv (.tcb { x with tcbPriority := specPrio v })) :=
    hE.upd_tcb hP ht _ (fun b hb hh => hA b hb fun e => hh.2 (TF.of_val (a_prio hta).2 (by rw [hpv]; exact e)))
      (Or.inr ⟨hA _ (a_st hta).1 (by rw [val_st hta]; omega), hA _ (a_blk hta).1 (by rw [val_blk hta]; omega)⟩)
      (hxe.prio_wr hta hA _ hpr)
  obtain ⟨x1, hk1, hx1⟩ := hN.tcb t ht
  rw [hk] at hk1; cases hk1
  have hN' := ntfn_upd_prio hP0.toC hN ht { x with tcbPriority := specPrio v } hA
    ⟨by rw [hA _ (a_st hta).1 (by rw [val_st hta]; omega)]; exact hx1.st,
      fun n hn => by rw [hA _ (a_blk hta).1 (by rw [val_blk hta]; omega)]; exact hx1.blk n hn,
      (by rw [hA _ (by rw [badgeRegA_eq_regA]; exact (a_reg hta _).1) (by
        rw [badgeRegA_eq_regA, regA_val hta (regIdx_lt _)]; have := regIdx_lt Fl4Spec.badge_register; omega)]
          exact hx1.badge), hpr⟩
  have hsc : ∀ y ∈ T, ∀ z, (updK σ t.bv (.tcb { x with tcbPriority := specPrio v })).kheap y.bv = some (.tcb z) →
      z.tcbSchedContext = optRef (L.mem (L.wr s (prioA t) v) (scA y)) := by
    intro y hy z hz
    have hya := hP.tcb y hy
    have es : L.mem (L.wr s (prioA t) v) (scA y) = L.mem s (scA y) := hA _ (field_aligned hya (by simp) (by simp)) (by
      unfold scA; rw [tfield_val hya (by simp)]
      by_cases e : y = t
      · subst e; simp
      · have := tcb_disj hP ht hy e; simp; omega)
    rw [es]
    by_cases e : y.bv = t.bv
    · rw [e] at hz; simp [updK] at hz; subst hz
      obtain ⟨x2, hk2, h2⟩ := hIR.tcb t ht; rw [hk] at hk2; cases hk2
      rw [eq_of_bv e]; exact h2.sc
    · simp only [updK, Function.update_of_ne e] at hz
      obtain ⟨x2, hk2, h2⟩ := hIR.tcb y hy; rw [hz] at hk2; cases hk2; exact h2.sc
  refine ⟨IpcRel.of hN' hE' hsc, ⟨hT.frame (writesIn_wr hpa) (fun a ha => Or.inl ⟨t, ht, ?_, ?_⟩)
    (fun a ha => by rw [ha]; exact NoBufW.off hP.tcb ht (by simp) (by simp)) ?_ rfl rfl
    (VsKeep.updK_tcb hk rfl), hSE.1.prio_wr ht hk hq0 v hv, hSE.2.mono (L.ksb_wr _ _ _)
      (SzKeep.updK hk (fun _ _ h => by cases h))⟩⟩
  · rw [ha, hpv]; omega
  · rw [ha, hpv]; omega
  · refine ⟨fun o => ?_, fun o r cs hc' _ => ?_, fun o y hy => ?_, rfl, rfl⟩
    · by_cases e : o = t.bv
      · subst e
        refine ⟨fun r cs h _ => by simp [updK] at h, fun _ _ => ⟨x, hk⟩, fun hn => by rw [hk] at hn; cases hn⟩
      · simp only [updK, Function.update_of_ne e]
        exact ⟨fun r cs h hw => ⟨cs, h, hw⟩, fun y h => ⟨y, h⟩, id⟩
    · have e : o ≠ t.bv := by rintro rfl; rw [hk] at hc'; cases hc'
      simp only [updK, Function.update_of_ne e]; exact hc'
    · by_cases e : o = t.bv
      · subst e; rw [hk] at hy; cases hy
        exact ⟨{ x with tcbPriority := specPrio v }, by simp [updK], rfl⟩
      · exact ⟨y, by simp only [updK, Function.update_of_ne e]; exact hy, rfl⟩

end PrioW


section ReorderI
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

theorem scRelM_hsc {m : U64 → U64} {σ : Fl4Spec.State Unit} (h : ScRelM T m σ) :
    ∀ t ∈ T, ∀ x, σ.kheap t.bv = some (.tcb x) → x.tcbSchedContext = optRef (m (scA t)) := by
  intro t ht x hx
  obtain ⟨y, hy, e⟩ := h t ht
  rw [hx] at hy; cases hy; exact e

set_option maxHeartbeats 4000000 in
/-- **`reorder_ep` on `IRel`**. -/
theorem ep_reorder_irel (hP0 : IPlaced N T E R B) (s : S) (σ : Fl4Spec.State Unit)
    (hX : IRel st th cr N T C E R B c s σ) {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb}
    (hkt : σ.kheap t.bv = some (.tcb xt)) {e : U64} (he : e ∈ E) {x : Fl4Spec.Endpoint}
    (hk : σ.kheap e.bv = some (.endpoint x)) (htq : t.bv ∈ x.epQueue)
    (hsort : ∀ xs, QueueRel (L.mem s) T .Ep (qOf (L.mem s) e) xs →
      PrioSorted (fun y => L.mem s (prioA y)) (xs.erase t)) :
    endpoint.reorder_ep st s e t ⦃ s' =>
      ∃ σ', Fl4Spec.reorderEp (Z := Unit) e.bv t.bv σ = ({((), σ')}, False) ∧
        IRel st th cr N T C E R B c s' σ' ⦄ := by
  have hH := (ipcCore_top (st := st) (th := th) (cr := cr) (N := N) (C := C) (c := c) hP0.e).epHyps hP0
  obtain ⟨hIR, hSRT⟩ := hX
  have hP := hP0.e
  obtain ⟨xs, hQ, hxs, hB⟩ := (hIR.toE.at_ep he hk).queue
  have htxs : t ∈ xs := by
    rw [hxs] at htq; obtain ⟨y, hy, ey⟩ := List.mem_map.1 htq; rw [← eq_of_bv ey]; exact hy
  refine WP.spec_mono (WP.spec_and (ep_reorder_rel hH hP s σ hIR.toE ⟨hSRT, ScRelM.of hIR⟩ ht hkt he hk htq hsort)
    (WP.spec_mono (ep_reorder_full hP s he t xs hQ htxs) fun _ h => h.2.2.1)) ?_
  rintro s' ⟨⟨σ', hm, hR', hS', y, rfl⟩, hQA⟩
  have hkv : Notif.KView σ (updK σ e.bv (.endpoint y)) := by
    refine ⟨fun p z h => ?_, fun p z h => ⟨z, ?_, rfl, rfl, rfl⟩⟩
    · have : p ≠ e.bv := by intro h'; rw [h', hk] at h; cases h
      simp [updK, this, h]
    · have : p ≠ e.bv := by intro h'; rw [h', hk] at h; cases h
      simp [updK, this, h]
  have hW : ∀ w ∈ xs, w ∈ T ∧ (L.mem s (tStA w)).val ≠ 6 := fun w hw =>
    ⟨hQ.mem w hw, by rcases (hB w hw).2 with h | h <;> rw [h] <;> simp⟩
  have hN' := ntfn_frame_ep hP0.toC hIR.toN he hW hQA hkv
  exact ⟨_, hm, IpcRel.of hN' hR' (scRelM_hsc hS'.2), hS'.1⟩

set_option maxHeartbeats 4000000 in
/-- **`reorder_ntfn` on `IRel`**. -/
theorem ntfn_reorder_irel (hP0 : IPlaced N T E R B) (s : S) (σ : Fl4Spec.State Unit)
    (hX : IRel st th cr N T C E R B c s σ) {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb}
    (hkt : σ.kheap t.bv = some (.tcb xt)) {n : U64} (hn : n ∈ N) {x : Fl4Spec.Notification}
    (hk : σ.kheap n.bv = some (.notification x)) {q : List Fl4Spec.ObjRef} (hwq : x.ntfnObj = .waitingNtfn q)
    (htq : t.bv ∈ q)
    (hsort : ∀ xs, QueueRel (L.mem s) T .Ep (qOf (L.mem s) n) xs →
      PrioSorted (fun y => L.mem s (prioA y)) (xs.erase t)) :
    notification.reorder_ntfn st s n t ⦃ s' =>
      ∃ σ', Fl4Spec.reorderNtfn (Z := Unit) n.bv t.bv σ = ({((), σ')}, False) ∧
        IRel st th cr N T C E R B c s' σ' ⦄ := by
  obtain ⟨hIR, hSRT⟩ := hX
  have hP := hP0
  have hx2 := hIR.toN.at_ntfn hn hk
  have hxt := hIR.toN.at_tcb ht hkt
  obtain ⟨xs, hQ, hxs, hB⟩ := hx2.obj.queue
  have hxs' : q = xs.map UScalar.bv := by rw [← hxs, hwq]; rfl
  have htxs : t ∈ xs := by
    rw [hxs'] at htq; obtain ⟨y, hy, ey⟩ := List.mem_map.1 htq; rw [← eq_of_bv ey]; exact hy
  have hnd := hQ.nodup
  have hsorted := hsort xs hQ
  refine WP.spec_mono (ntfn_reorder_full hP.n s hn t xs hQ htxs) ?_
  rintro s' ⟨hA1, hA2, hA3⟩
  set ys := insPrio (fun y => L.mem s (prioA y)) (L.mem s (prioA t)) t (xs.erase t) with hys
  have hmem : ∀ y ∈ ys, y ∈ xs := fun y hy => by
    rcases mem_insPrio_sorted hsorted hy with rfl | hy'
    · exact htxs
    · exact List.mem_of_mem_erase hy'
  have hR4 : IpcRel N T E R B (L.mem s')
      (updK σ n.bv (.notification { x with ntfnObj := .waitingNtfn (ys.map UScalar.bv) })) := by
    have hbw : ∀ w ∈ xs, w ∈ T ∧ L.mem s (tBlockA w) = n := fun w hw => ⟨hQ.mem w hw, (hB w hw).2⟩
    refine hIR.upd_ntfn hP hn _ (fun b hb ⟨_, hnw, hnl⟩ => hA3.agree b hb
        (fun w hw => by
          obtain ⟨hwT, hwb⟩ := hbw w hw
          have hwa := hP.e.tcb w hwT
          exact ⟨fun e => hnl ⟨w, hwT, hwb, Or.inl (by rw [e, val_next hwa])⟩,
            fun e => hnl ⟨w, hwT, hwb, Or.inr (by rw [e, val_prev hwa])⟩⟩)
        (fun e => hnw (e ▸ (nw_words hP hn).1)) (fun e => hnw (e ▸ (nw_words hP hn).2.1)))
      ⟨?_, ?_, ?_, ?_⟩
    · have h1 : stOf (L.mem s) n = 1#u64 := by
        have := hx2.obj; rw [hwq] at this; exact this.1
      refine ⟨by rw [hA2]; exact h1, ys, insPrio_ne_nil hsorted, rfl, hA1, fun y hy => ?_⟩
      have hyT : y ∈ T := hQ.mem y (hmem y hy)
      have e := hA3.tcb y hyT
      exact ⟨by rw [e.st]; exact (hB y (hmem y hy)).1, by rw [e.blk]; exact (hB y (hmem y hy)).2⟩
    · show x.ntfnBoundTcb = _; rw [hA3.bound]; exact hx2.bound
    · rw [hA3.bound]; exact hx2.bound_mem
    · show x.ntfnSc = _; rw [hA3.sc]; exact hx2.sc
  have hrm : Fl4Spec.removeAll t.bv q = (xs.erase t).map UScalar.bv := by rw [hxs']; exact removeAll_map hnd t
  have hq : ∀ y ∈ Fl4Spec.removeAll t.bv q, ∃ z, σ.kheap y = some (.tcb z) ∧ z.tcbPriority = Notif.prioOf σ y := by
    intro y hy
    rw [hrm] at hy
    obtain ⟨y', hy'x, rfl⟩ := List.mem_map.1 hy
    obtain ⟨z, hz, -⟩ := hIR.toN.tcb y' (hQ.mem y' (List.mem_of_mem_erase hy'x))
    exact ⟨z, hz, by simp [Notif.prioOf, hz]⟩
  have hlist : specIns (Fl4Spec.removeAll t.bv q) (Notif.prioOf σ) xt.tcbPriority t.bv = ys.map UScalar.bv := by
    rw [specIns, hrm, List.takeWhile_map, List.dropWhile_map]
    simp only [ys, insPrio_eq_sorted _ _ t _ hsorted, List.map_append, List.map_cons]
    have hc' : ∀ y ∈ xs.erase t, ((fun y => @decide (Notif.prioOf σ y ≥ xt.tcbPriority) (Classical.propDecidable _)) ∘
        UScalar.bv) y = (fun y => !decide (L.mem s (prioA t) > L.mem s (prioA y))) y := by
      intro y hy
      obtain ⟨z, hz, hzr⟩ := hIR.toN.tcb y (hQ.mem y (List.mem_of_mem_erase hy))
      have hpz : Notif.prioOf σ y.bv = z.tcbPriority := by simp [Notif.prioOf, hz]
      simp only [Function.comp, hpz]
      convert (prio_ge_iff _ _ _ _ hxt.prio hzr.prio).symm using 2
    rw [takeWhile_congr' hc', dropWhile_congr' hc']
  have hK := NtfnStep.ntfn (y := { x with ntfnObj := .waitingNtfn (ys.map UScalar.bv) }) hk rfl rfl
  refine ⟨_, by rw [reorderNtfn_eq hk hkt hwq htq (Notif.prioOf σ) hq, hlist], hR4,
    hSRT.1.stableN hSRT.2.1.placed hA3.foot hK, hSRT.2.1.stable hA3.foot hK,
    hSRT.2.2.mono hA3.foot.1 (SzKeep.ntfnStep hK)⟩

end ReorderI


section Requeue
open Fl4Spec in
theorem nks_tcbSchedActionI (f : ObjRef → List ObjRef → List ObjRef) (t : ObjRef) :
    NKS (tcbSchedAction (Z := Unit) f t) := by
  unfold tcbSchedAction threadGet getTcbQueue setTcbQueue
  nks_auto

open Fl4Spec in
theorem nks_rescheduleRequiredI : NKS (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired getScRefillSufficient getScRefillReady threadGet tcbSchedAction getTcbQueue
    setTcbQueue setSchedulerAction
  nks_auto

theorem NKS.of_eq {m : Fl4Spec.NonDet (Fl4Spec.State Unit) Unit} (h : NKS m) {σ σ' : Fl4Spec.State Unit}
    (he : m σ = ({((), σ')}, False)) : ScOnlyK σ σ' :=
  h σ ((), σ') (by rw [he]; exact Set.mem_singleton _)

variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

set_option maxHeartbeats 8000000 in
/-- **`set_priority`'s requeue on `IRel`**: `dequeue`, the priority word,
`enqueue`, `reschedule_required`, against the spec's (the thread not in the
release queue, the action's thread ready on `IRel`, `ActReady`). -/
theorem requeue_irel (hP0 : IPlaced N T E R B) {s : S} {σ : Fl4Spec.State Unit}
    (hX : IRel st th cr N T C E R B c s σ) {t : U64} (ht : t ∈ T)
    (hr0 : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64) (v : U64) (hv : v.val < 256)
    (hAct : ∀ s' σ', IRel st th cr N T C E R B c s' σ' → ActReady σ') :
    (do
      let s1 ← sched.dequeue st s t
      let s2 ← obj.Tcb.set_prio st t s1 v
      let s3 ← sched.enqueue st s2 t
      sched.reschedule_required st s3) ⦃ s' => ∃ σ', (do
        Fl4Spec.tcbSchedAction (Z := Unit) Fl4Spec.tcbSchedDequeue t.bv
        Fl4Spec.threadSetPriority (Z := Unit) t.bv (specPrio v)
        Fl4Spec.tcbSchedAction (Z := Unit) Fl4Spec.tcbSchedEnqueue t.bv
        Fl4Spec.rescheduleRequired (Z := Unit)) σ = ({((), σ')}, False) ∧
      IRel st th cr N T C E R B c s' σ' ⦄ := by
  have hS := hX.2.2.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hp := hc.prio t ht
  have haf := hc.aff t ht
  have hN : NodePlaced st T s (L.mem s (affA t)) := by rw [haf]; exact hc.node
  have hN' : NodePlaced st T s (L.cpu s) := by rw [hc.cur]; exact hc.node
  have hR1 : ReadyQueues st T s (L.mem s (affA t)) Q := by rw [haf]; exact hc.ready
  refine WP.spec_bind (WP.spec_and (WP.spec_and (dequeue_refines s σ hS t ht) (dequeue_sfootI hS ht))
    (sched.dequeue.foot s t _ hc.tcbs ht hp hN hN' (hR1.1.rel _ hp) (hc.queued t ht).1)) ?_
  rintro s1 ⟨⟨⟨σ1, he1, -, -, -, hS1⟩, hw1⟩, -, hinq1⟩
  have hX1 := sc_step_lift hP0 hX (hw1.mono fun _ h => Or.inr h) (NKS.of_eq (nks_tcbSchedActionI _ _) he1) hS1
  have hq1 : (L.mem s1 (inqA t) &&& sched.Q_QUEUED) = 0#u64 := by
    rw [hinq1]; split_ifs with h
    · exact andn_qq_qq _
    · exact not_not.1 h
  have hrel1 : (L.mem s1 (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by
    rw [hinq1]; split_ifs
    · rw [andn_qq_qr]; exact hr0
    · exact hr0
  step with P1.obj.Tcb.set_prio.spec as ⟨s2, hs2⟩
  subst hs2
  obtain ⟨x1, hkx1, -⟩ := hX1.1.tcb t ht
  have hX2 := prio_wr_irel hP0 hX1 ht hkx1 hq1 v hv
  have hta := hc.tcbs t ht
  have hinq2 : L.mem (L.wr s1 (prioA t) v) (inqA t) = L.mem s1 (inqA t) :=
    rd_wr_ne (a_prio hta).1 (field_aligned hta (by simp) (by simp)) (fun e => by
      have := congrArg UScalar.val e; rw [val_prio hta, inqA_eq, tfield_val hta (by simp)] at this; simp at this)
  have hS2 := hX2.2.2.1
  refine WP.spec_bind (WP.spec_and (enqueue_refines _ _ hS2 t ht (fun _ => by rw [hinq2]; exact hrel1))
    (enqueue_sfootI hS2 ht)) ?_
  rintro s3 ⟨⟨σ3, he3, -, -, -, hS3⟩, hw3⟩
  have hX3 := sc_step_lift hP0 hX2 (hw3.mono fun _ h => Or.inr h) (NKS.of_eq (nks_tcbSchedActionI _ _) he3) hS3
  refine WP.spec_mono (WP.spec_and (reschedule_required_refines s3 σ3 hX3.1.toN hS3 (hAct _ _ hX3))
    (reschedule_required_sfootI hS3)) ?_
  rintro s4 ⟨⟨σ4, he4, -, -, -, hS4⟩, hw4⟩
  have hX4 := sc_step_lift hP0 hX3 (hw4.mono fun _ h => Or.inr h) (NKS.of_eq nks_rescheduleRequiredI he4) hS4
  refine ⟨σ4, ?_, hX4⟩
  rw [nd_bind_one he1]
  show (Fl4Spec.threadSet _ t.bv >>= _) σ1 = _
  rw [nd_bind_one (threadSet_eq _ hkx1), nd_bind_one he3]
  exact he4

end Requeue

/-! ## The spec's `set_priority` -/

section SpecP
open Fl4Spec

theorem ucast8_specPrio (v : U64) : (ucast 8 v.bv : BitVec 8) = specPrio v := by
  unfold specPrio; apply BitVec.eq_of_toNat_eq; simp [ucast]

/-- The spec's `set_priority` of a runnable thread. -/
theorem setPriority_run {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (hr : runnable x.tcbState = true) (pr : Priority) :
    setPriority (Z := Unit) t pr σ =
      (if t ∈ σ.readyQueues x.tcbDomain x.tcbPriority ∨ t = σ.curThread then (do
        tcbSchedAction (Z := Unit) tcbSchedDequeue t
        threadSetPriority (Z := Unit) t pr
        tcbSchedAction (Z := Unit) tcbSchedEnqueue t
        rescheduleRequired (Z := Unit)) σ
      else threadSetPriority (Z := Unit) t pr σ) := by
  unfold setPriority
  rw [nd_bind_one (getThreadState_eq hk)]
  simp only [hr, ↓reduceIte]
  rw [nd_bind_one (threadGet_eq _ hk), nd_bind_one (threadGet_eq _ hk), nd_bind_one (getTcbQueue_eq _ _ _)]
  show (NonDet.gets (fun s : State Unit => s.curThread) >>= _) σ = _
  rw [nd_gets_bind]
  split <;> rfl

/-- The spec's `set_priority` of a thread that is not runnable. -/
theorem setPriority_blk {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (hr : runnable x.tcbState = false) (pr : Priority) :
    setPriority (Z := Unit) t pr σ = (do
      threadSetPriority (Z := Unit) t pr
      NonDet.maybeM (fun ep => reorderEp (Z := Unit) ep t) (epBlocked x.tcbState)
      NonDet.maybeM (fun ntfn => reorderNtfn (Z := Unit) ntfn t) (ntfnBlocked x.tcbState)) σ := by
  unfold setPriority
  rw [nd_bind_one (getThreadState_eq hk)]
  simp only [hr, Bool.false_eq_true, ↓reduceIte]

end SpecP

/-! ## `set_priority` of a runnable thread -/

section Run
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

set_option maxHeartbeats 8000000 in
/-- **`set_priority` of a runnable thread on `IRel`**: requeued when queued or
current (the current thread in no release queue, l4v `ct_not_in_release_q`
[J]), otherwise only its priority. -/
theorem prio_run_irel (hP0 : IPlaced N T E R B) {s : S} {σ : Fl4Spec.State Unit}
    (hX : IRel st th cr N T C E R B c s σ) {t : U64} (ht : t ∈ T) {x : Fl4Spec.Tcb}
    (hk : σ.kheap t.bv = some (.tcb x)) (hrun : Fl4Spec.runnable x.tcbState = true) (v : U64) (hv : v.val < 256)
    (hAct : ∀ s' σ', IRel st th cr N T C E R B c s' σ' → ActReady σ')
    (hRel : σ.curThread = t.bv → t.bv ∉ σ.releaseQueue) :
    (do
      let b ← sched.queued st s t
      if b then do
        let s1 ← sched.dequeue st s t
        let s2 ← obj.Tcb.set_prio st t s1 v
        let s3 ← sched.enqueue st s2 t
        sched.reschedule_required st s3
      else do
        let t1 ← sched.cur_thread st s
        let b1 ← obj.Tcb.Insts.CoreCmpPartialEqTcb.eq t t1
        if b1 then do
          let s1 ← sched.dequeue st s t
          let s2 ← obj.Tcb.set_prio st t s1 v
          let s3 ← sched.enqueue st s2 t
          sched.reschedule_required st s3
        else obj.Tcb.set_prio st t s v) ⦃ s' => ∃ σ',
      Fl4Spec.setPriority (Z := Unit) t.bv (Fl4Spec.ucast 8 v.bv) σ = ({((), σ')}, False) ∧
        IRel st th cr N T C E R B c s' σ' ⦄ := by
  have hS := hX.2.2.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  obtain ⟨x', hk', hd0, -, -, hpr⟩ := hs.tcb t ht
  rw [hk] at hk'; cases hk'
  have hp := hc.prio t ht
  have hprio : x.tcbPriority = specPrio (L.mem s (prioA t)) := (specPrio_eq hpr).symm
  have hrq : σ.readyQueues x.tcbDomain x.tcbPriority = (Q (L.mem s (prioA t))).map UScalar.bv := by
    rw [hd0, hprio]; exact hs.rq _ hp
  have hrel0 : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64 ↔ t.bv ∉ σ.releaseQueue := by
    rw [hs.rel, mem_map_bv]
    constructor
    · intro h0 hm; exact (hc.released t ht).2 hm h0
    · intro hn; by_contra h0; exact hn ((hc.released t ht).1 h0)
  have req : (σ.curThread = t.bv ∨ t.bv ∈ σ.readyQueues x.tcbDomain x.tcbPriority) →
      (do
        let s1 ← sched.dequeue st s t
        let s2 ← obj.Tcb.set_prio st t s1 v
        let s3 ← sched.enqueue st s2 t
        sched.reschedule_required st s3) ⦃ s' => ∃ σ',
        Fl4Spec.setPriority (Z := Unit) t.bv (Fl4Spec.ucast 8 v.bv) σ = ({((), σ')}, False) ∧
          IRel st th cr N T C E R B c s' σ' ⦄ := by
    intro hcq
    have hr0 : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by
      rw [hrel0]
      rcases hcq with h | h
      · exact hRel h
      · intro hm
        rw [hrq, mem_map_bv] at h
        rw [hs.rel, mem_map_bv] at hm
        exact hc.excl t ht h hm
    refine WP.spec_mono (requeue_irel hP0 hX ht hr0 v hv hAct) ?_
    rintro s' ⟨σ', he, hX'⟩
    refine ⟨σ', ?_, hX'⟩
    rw [setPriority_run hk hrun, if_pos (hcq.elim (fun h => Or.inr h.symm) Or.inl), ucast8_specPrio]
    exact he
  step with P1.sched.queued.spec as ⟨b, hb⟩
  subst hb
  by_cases hq : (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64
  · simp only [hq, ne_eq, not_false_eq_true, decide_true, ↓reduceIte]
    refine req (Or.inr ?_)
    rw [hrq, mem_map_bv]; exact (hc.queued t ht).1 hq
  · simp only [hq, decide_false, Bool.false_eq_true, ↓reduceIte]
    step with P1.sched.cur_thread.spec as ⟨t1, ht1⟩
    subst ht1
    unfold obj.Tcb.Insts.CoreCmpPartialEqTcb.eq
    simp only [bind_ok]
    have hcur : σ.curThread = (L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD)).bv := by
      rw [hs.curThread, hc.cur]; rfl
    by_cases e : t = L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD)
    · simp only [e, decide_true, ↓reduceIte]
      rw [← e]
      exact req (Or.inl (by rw [hcur, ← e]))
    · simp only [e, decide_false, Bool.false_eq_true, ↓reduceIte]
      step with P1.obj.Tcb.set_prio.spec as ⟨s2, hs2⟩
      subst hs2
      refine ⟨_, ?_, prio_wr_irel hP0 hX ht hk (not_not.1 hq) v hv⟩
      rw [setPriority_run hk hrun, if_neg ?_, ucast8_specPrio]
      · show Fl4Spec.threadSet _ t.bv σ = _
        rw [threadSet_eq _ hk]
      · rintro (h | h)
        · rw [hrq, mem_map_bv] at h
          exact hq ((hc.queued t ht).2 h)
        · rw [hcur] at h; exact e (eq_of_bv h)

end Run

/-! ## `set_priority` on `IRel` -/

section SetP
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- A queue relation back across a priority write (it reads no priority). -/
theorem qrel_prio_back {m m' : U64 → U64} (hT : TcbPlaced T) {t e : U64} (ht : t ∈ T)
    (hA : ∀ b, Aligned b → b.val ≠ t.val + 3448 → m' b = m b)
    (hh : Aligned (epHeadA e) ∧ (epHeadA e).val ≠ t.val + 3448) (hs : Aligned (epTSA e) ∧ (epTSA e).val ≠ t.val + 3448)
    {xs : List U64} (h : QueueRel m' T .Ep (qOf m' e) xs) : QueueRel m T .Ep (qOf m e) xs := by
  have hq : qOf m' e = qOf m e := by unfold qOf; rw [hA _ hh.1 hh.2, hA _ hs.1 hs.2]
  rw [hq] at h
  have h12 : (2 : ℕ) ^ 12 = 4096 := by norm_num
  have hta := hT t ht
  refine ⟨h.nodup, h.mem, h.head, h.last, h.seg.congr fun y hy => ?_⟩
  have hya := hT y (h.mem y hy)
  have hne : ∀ K : U64, K.val < 4096 → K.val ≠ 3448 → (core.num.U64.wrapping_add y K).val ≠ t.val + 3448 := by
    intro K hK hK'
    rw [tfield_val hya hK]
    by_cases e : y = t
    · subst e; omega
    · have a1 := hta.align; have a2 := hya.align
      have := val_ne_of_ne e
      rw [h12] at a1 a2; omega
  exact ⟨(hA _ (prevA_aligned hya .Ep) (hne _ (by simp [prevOff]) (by simp [prevOff]))).symm,
    (hA _ (nextA_aligned hya .Ep) (hne _ (by simp [nextOff]) (by simp [nextOff]))).symm⟩

set_option maxHeartbeats 16000000 in
/-- **`set_priority` on `IRel`**: the requeue of a queued or current runnable
thread (`prio_run_irel`), the reorder of an endpoint (`ep_reorder_irel`) or
notification (`ntfn_reorder_irel`) queue the thread is blocked on, else the
priority word. Named: `ActReady` on `IRel` [J], the current thread in no
release queue [J], `SchedValid` [J], `Inv` [J], `ObjCover` [J], the endpoint and
notification queues sorted (`QSorted`) [J]. -/
theorem set_priority_irel (hP0 : IPlaced N T E R B) {s : S} {σ : Fl4Spec.State Unit}
    (hX : IRel st th cr N T C E R B c s σ) {t : U64} (ht : t ∈ T) (v : U64) (hv : v.val < 256)
    (hAct : ∀ s' σ', IRel st th cr N T C E R B c s' σ' → ActReady σ')
    (hRel : σ.curThread = t.bv → t.bv ∉ σ.releaseQueue) (hSV : SchedValid σ) (hInv : Inv σ)
    (hOC : ObjCover N T E R C σ) (hSE : QSorted st T E s) (hSN : QSorted st T N s) :
    sched.set_priority st s t v ⦃ s' => ∃ σ',
      Fl4Spec.setPriority (Z := Unit) t.bv (Fl4Spec.ucast 8 v.bv) σ = ({((), σ')}, False) ∧
        IRel st th cr N T C E R B c s' σ' ⦄ := by
  have hP := hP0.e
  have hT := hP.tcb
  have hta := hT t ht
  obtain ⟨x, hk, hxe⟩ := hX.1.toE.tcb t ht
  have hS := hX.2.2.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hpa := (a_prio hta).1
  have hpv := val_prio hta
  have hA : ∀ b, Aligned b → b.val ≠ t.val + 3448 → L.mem (L.wr s (prioA t) v) b = L.mem s b :=
    fun b hb h => rd_wr_ne hpa hb (fun e => h (by rw [← e, hpv]))
  -- a thread that is not runnable is in no ready queue
  have hnq : Fl4Spec.runnable x.tcbState = false → (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 := by
    intro hr
    by_contra hq
    have hm := (hc.queued t ht).1 hq
    have hin : t.bv ∈ σ.readyQueues 0 (specPrio (L.mem s (prioA t))) := by
      rw [hs.rq _ (hc.prio t ht), mem_map_bv]; exact hm
    obtain ⟨x2, scp, y2, n2, hk2, -, hr2, -, -⟩ := hInv.rq _ _ _ hin
    rw [hk] at hk2; cases hk2; rw [hr] at hr2; cases hr2
  -- the plain priority write
  have plain : Fl4Spec.runnable x.tcbState = false → Fl4Spec.epBlocked x.tcbState = none →
      Fl4Spec.ntfnBlocked x.tcbState = none →
      obj.Tcb.set_prio st t s v ⦃ s' => ∃ σ',
        Fl4Spec.setPriority (Z := Unit) t.bv (Fl4Spec.ucast 8 v.bv) σ = ({((), σ')}, False) ∧
          IRel st th cr N T C E R B c s' σ' ⦄ := by
    intro hr he hn
    step with P1.obj.Tcb.set_prio.spec as ⟨s2, hs2⟩
    subst hs2
    refine ⟨_, ?_, prio_wr_irel hP0 hX ht hk (hnq hr) v hv⟩
    rw [setPriority_blk hk hr, ucast8_specPrio]
    show (Fl4Spec.threadSet _ t.bv >>= _) σ = _
    rw [nd_bind_one (threadSet_eq _ hk), he, hn]
    show ((pure () : Fl4Spec.NonDet (Fl4Spec.State Unit) Unit) >>= fun _ =>
      (pure () : Fl4Spec.NonDet (Fl4Spec.State Unit) Unit)) _ = _
    rw [nd_pure_bind']
    rfl
  -- the endpoint reorder
  have epB : ∀ e : Fl4Spec.ObjRef, Fl4Spec.runnable x.tcbState = false → Fl4Spec.epBlocked x.tcbState = some e →
      Fl4Spec.ntfnBlocked x.tcbState = none →
      (∃ xe, σ.kheap e = some (.endpoint xe) ∧ t.bv ∈ xe.epQueue) →
      (do
        let s1 ← obj.Tcb.set_prio st t s v
        let i ← obj.Tcb.block_obj st t s1
        endpoint.reorder_ep st s1 i t) ⦃ s' => ∃ σ',
        Fl4Spec.setPriority (Z := Unit) t.bv (Fl4Spec.ucast 8 v.bv) σ = ({((), σ')}, False) ∧
          IRel st th cr N T C E R B c s' σ' ⦄ := by
    intro e hr he hn ⟨xe, hke, htq⟩
    step with P1.obj.Tcb.set_prio.spec as ⟨s1, hs1⟩
    subst hs1
    step with P1.obj.Tcb.block_obj.spec as ⟨w, hw⟩
    subst hw
    have hwv : L.mem (L.wr s (prioA t) v) (blockA t) = L.mem s (tBlockA t) :=
      hA _ (a_blk hta).1 (by show (tBlockA t).val ≠ _; rw [val_blk hta]; omega)
    rw [hwv]
    have hwe : (L.mem s (tBlockA t)).bv = e := hxe.blk e he
    obtain ⟨e', he', ee'⟩ := hOC.ep e xe hke
    have hw' : L.mem s (tBlockA t) = e' := eq_of_bv (hwe.trans ee'.symm)
    rw [hw']
    subst ee'
    have hX1 := prio_wr_irel hP0 hX ht hk (hnq hr) v hv
    have het : e'.bv ≠ t.bv := fun h => by rw [h, hk] at hke; cases hke
    have hke1 : (updK σ t.bv (.tcb { x with tcbPriority := specPrio v })).kheap e'.bv = some (.endpoint xe) := by
      simp [updK, het, hke]
    have hkt1 : (updK σ t.bv (.tcb { x with tcbPriority := specPrio v })).kheap t.bv =
        some (.tcb { x with tcbPriority := specPrio v }) := by simp [updK]
    have hsort : ∀ xs, QueueRel (L.mem (L.wr s (prioA t) v)) T .Ep (qOf (L.mem (L.wr s (prioA t) v)) e') xs →
        PrioSorted (fun y => L.mem (L.wr s (prioA t) v) (prioA y)) (xs.erase t) := by
      intro xs hq
      have hq0 := qrel_prio_back hT ht hA ⟨(a_head hP he').1, by rw [val_head]; have := hP.et e' he' t ht; omega⟩
        ⟨(a_ts hP he').1, by rw [val_ts hP he']; have := hP.et e' he' t ht; omega⟩ hq
      have hs0 : PrioSorted _ (xs.erase t) := (hSE e' he' xs hq0).sublist (List.erase_sublist (a := t))
      refine prioSorted_congr hs0 fun y hy => ?_
      have hyt : y ≠ t := fun h => hq0.nodup.not_mem_erase (h ▸ hy)
      have hya := hT y (hq0.mem y (List.mem_of_mem_erase hy))
      refine hA _ (a_prio hya).1 ?_
      rw [val_prio hya]
      have a1 := hta.align; have a2 := hya.align
      have := val_ne_of_ne hyt
      have h12 : (2 : ℕ) ^ 12 = 4096 := by norm_num
      rw [h12] at a1 a2; omega
    refine WP.spec_mono (ep_reorder_irel hP0 _ _ hX1 ht hkt1 he' hke1 htq hsort) ?_
    rintro s' ⟨σ', hm, hX'⟩
    refine ⟨σ', ?_, hX'⟩
    rw [setPriority_blk hk hr, ucast8_specPrio]
    show (Fl4Spec.threadSet _ t.bv >>= _) σ = _
    rw [nd_bind_one (threadSet_eq _ hk), he, hn]
    show (Fl4Spec.reorderEp e'.bv t.bv >>= _) _ = _
    rw [nd_bind_one hm]
    rfl
  -- the notification reorder
  have ntB : ∀ n : Fl4Spec.ObjRef, Fl4Spec.runnable x.tcbState = false → Fl4Spec.epBlocked x.tcbState = none →
      Fl4Spec.ntfnBlocked x.tcbState = some n →
      (∃ xn, σ.kheap n = some (.notification xn) ∧ t.bv ∈ Fl4Spec.ntfnQueueOf xn) →
      (do
        let s1 ← obj.Tcb.set_prio st t s v
        let i ← obj.Tcb.block_obj st t s1
        notification.reorder_ntfn st s1 i t) ⦃ s' => ∃ σ',
        Fl4Spec.setPriority (Z := Unit) t.bv (Fl4Spec.ucast 8 v.bv) σ = ({((), σ')}, False) ∧
          IRel st th cr N T C E R B c s' σ' ⦄ := by
    intro n hr he hn ⟨xn, hkn, htq⟩
    step with P1.obj.Tcb.set_prio.spec as ⟨s1, hs1⟩
    subst hs1
    step with P1.obj.Tcb.block_obj.spec as ⟨w, hw⟩
    subst hw
    have hwv : L.mem (L.wr s (prioA t) v) (blockA t) = L.mem s (tBlockA t) :=
      hA _ (a_blk hta).1 (by show (tBlockA t).val ≠ _; rw [val_blk hta]; omega)
    rw [hwv]
    obtain ⟨x1, hk1, hx1⟩ := hX.1.toN.tcb t ht
    rw [hk] at hk1; cases hk1
    have hwn : (L.mem s (tBlockA t)).bv = n := by
      cases hts : x.tcbState <;> simp [hts, Fl4Spec.ntfnBlocked] at hn
      subst hn; exact hx1.blk _ hts
    obtain ⟨n', hn', en'⟩ := hOC.ntfn n xn hkn
    have hw' : L.mem s (tBlockA t) = n' := eq_of_bv (hwn.trans en'.symm)
    rw [hw']
    subst en'
    have hX1 := prio_wr_irel hP0 hX ht hk (hnq hr) v hv
    have hnt : n'.bv ≠ t.bv := fun h => by rw [h, hk] at hkn; cases hkn
    have hkn1 : (updK σ t.bv (.tcb { x with tcbPriority := specPrio v })).kheap n'.bv = some (.notification xn) := by
      simp [updK, hnt, hkn]
    have hkt1 : (updK σ t.bv (.tcb { x with tcbPriority := specPrio v })).kheap t.bv =
        some (.tcb { x with tcbPriority := specPrio v }) := by simp [updK]
    obtain ⟨q, hwq⟩ : ∃ q, xn.ntfnObj = .waitingNtfn q := by
      cases h : xn.ntfnObj with
      | idleNtfn => simp [Fl4Spec.ntfnQueueOf, h, Fl4Spec.Ntfn.ntfnQueue] at htq
      | activeNtfn b => simp [Fl4Spec.ntfnQueueOf, h, Fl4Spec.Ntfn.ntfnQueue] at htq
      | waitingNtfn q => exact ⟨q, rfl⟩
    have htq' : t.bv ∈ q := by simpa [Fl4Spec.ntfnQueueOf, hwq, Fl4Spec.Ntfn.ntfnQueue] using htq
    have hna := hP0.n.ntfn n' hn'
    have hsort : ∀ xs, QueueRel (L.mem (L.wr s (prioA t) v)) T .Ep (qOf (L.mem (L.wr s (prioA t) v)) n') xs →
        PrioSorted (fun y => L.mem (L.wr s (prioA t) v) (prioA y)) (xs.erase t) := by
      intro xs hq
      have hdisj := hP0.n.disj n' hn' t ht
      have hq0 := qrel_prio_back hT ht hA
        ⟨(foot_head hP0.n hn').1, by have := (nw_words hP0 hn').1; unfold NW at this; omega⟩
        ⟨(foot_ts hP0.n hn').1, by have := (nw_words hP0 hn').2.1; unfold NW at this; omega⟩ hq
      have hs0 : PrioSorted _ (xs.erase t) := (hSN n' hn' xs hq0).sublist (List.erase_sublist (a := t))
      refine prioSorted_congr hs0 fun y hy => ?_
      have hyt : y ≠ t := fun h => hq0.nodup.not_mem_erase (h ▸ hy)
      have hya := hT y (hq0.mem y (List.mem_of_mem_erase hy))
      refine hA _ (a_prio hya).1 ?_
      rw [val_prio hya]
      have a1 := hta.align; have a2 := hya.align
      have := val_ne_of_ne hyt
      have h12 : (2 : ℕ) ^ 12 = 4096 := by norm_num
      rw [h12] at a1 a2; omega
    refine WP.spec_mono (ntfn_reorder_irel hP0 _ _ hX1 ht hkt1 hn' hkn1 hwq htq' hsort) ?_
    rintro s' ⟨σ', hm, hX'⟩
    refine ⟨σ', ?_, hX'⟩
    rw [setPriority_blk hk hr, ucast8_specPrio]
    show (Fl4Spec.threadSet _ t.bv >>= _) σ = _
    rw [nd_bind_one (threadSet_eq _ hk), he, hn]
    show ((pure () : Fl4Spec.NonDet (Fl4Spec.State Unit) Unit) >>= _) _ = _
    rw [nd_pure_bind']
    exact hm
  -- the dispatch on the state word
  unfold sched.set_priority
  step with Notif.obj.Tcb.state.spec as ⟨st0, hst0⟩
  subst hst0
  have hst := hxe.st
  unfold sched.TS_RUNNING sched.TS_RESTART sched.TS_RUNNING_VM sched.TS_BLOCKED_ON_RECV sched.TS_BLOCKED_ON_SEND
    sched.TS_BLOCKED_ON_NTFN
  cases hts : x.tcbState with
  | running =>
    have hv0 : L.mem s (tStA t) = 1#u64 := UScalar.eq_of_val_eq (by rw [hst, hts]; rfl)
    simp only [hv0, ↓reduceIte]
    exact prio_run_irel hP0 hX ht hk (by rw [hts]; rfl) v hv hAct hRel
  | restart =>
    have hv0 : L.mem s (tStA t) = 2#u64 := UScalar.eq_of_val_eq (by rw [hst, hts]; rfl)
    simp (config := { decide := true }) only [hv0, ↓reduceIte]
    exact prio_run_irel hP0 hX ht hk (by rw [hts]; rfl) v hv hAct hRel
  | runningVM =>
    have hv0 : L.mem s (tStA t) = 8#u64 := UScalar.eq_of_val_eq (by rw [hst, hts]; rfl)
    simp (config := { decide := true }) only [hv0, ↓reduceIte]
    exact prio_run_irel hP0 hX ht hk (by rw [hts]; rfl) v hv hAct hRel
  | inactive =>
    have hv0 : L.mem s (tStA t) = 0#u64 := UScalar.eq_of_val_eq (by rw [hst, hts]; rfl)
    simp (config := { decide := true }) only [hv0, ↓reduceIte]
    exact plain (by rw [hts]; rfl) (by rw [hts]; rfl) (by rw [hts]; rfl)
  | idleThreadState =>
    have hv0 : L.mem s (tStA t) = 7#u64 := UScalar.eq_of_val_eq (by rw [hst, hts]; rfl)
    simp (config := { decide := true }) only [hv0, ↓reduceIte]
    exact plain (by rw [hts]; rfl) (by rw [hts]; rfl) (by rw [hts]; rfl)
  | blockedOnReply r =>
    have hv0 : L.mem s (tStA t) = 5#u64 := UScalar.eq_of_val_eq (by rw [hst, hts]; rfl)
    simp (config := { decide := true }) only [hv0, ↓reduceIte]
    exact plain (by rw [hts]; rfl) (by rw [hts]; rfl) (by rw [hts]; rfl)
  | blockedOnReceive e r d =>
    have hv0 : L.mem s (tStA t) = 3#u64 := UScalar.eq_of_val_eq (by rw [hst, hts]; rfl)
    simp (config := { decide := true }) only [hv0, ↓reduceIte]
    exact epB e (by rw [hts]; rfl) (by rw [hts]; rfl) (by rw [hts]; rfl) (hSV.recvQ _ _ _ _ _ hk hts)
  | blockedOnSend e d =>
    have hv0 : L.mem s (tStA t) = 4#u64 := UScalar.eq_of_val_eq (by rw [hst, hts]; rfl)
    simp (config := { decide := true }) only [hv0, ↓reduceIte]
    exact epB e (by rw [hts]; rfl) (by rw [hts]; rfl) (by rw [hts]; rfl) (hSV.sendQ _ _ _ _ hk hts)
  | blockedOnNotification n =>
    have hv0 : L.mem s (tStA t) = 6#u64 := UScalar.eq_of_val_eq (by rw [hst, hts]; rfl)
    simp (config := { decide := true }) only [hv0, ↓reduceIte]
    exact ntB n (by rw [hts]; rfl) (by rw [hts]; rfl) (by rw [hts]; rfl) (hSV.ntfnW _ _ _ hk hts)

end SetP

end

end Fl4Proofs.P3.Ipc
