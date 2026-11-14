/-
P3 (DESIGN.md §9), scheduling contexts: writing the SC pointer fields, and
**`maybe_return_sched_context` refines l4v `maybe_return_sc`**
(SchedContext_A), discharging `RecvHyps.returnSc` (NtfnRecv.lean) given
the refill hypothesis `ActReady` of the state (needed when the returning
thread is the current one: `reschedule_required`).

* `ScRel1.wr_hdr`: a write to a non-ring header word of an SC leaves the
  ring, the refill max and the other header words alone;
* `SchedRel.set_sc_tcb`: `sc.set_tcb v` ↔ `sc_tcb := v`;
* `SchedRel.set_tcb_sc`: `t.set_sc v` ↔ `tcb_sched_context := v` (for `v`
  0 or an SC of `C`).
-/
import Fl4Proofs.P3.ScNtfn
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- A non-ring header word. -/
def HdrK (K : U64) : Prop := K = 8#u64 ∨ K = 24#u64 ∨ K = 40#u64 ∨ K = 48#u64 ∨ K = 56#u64 ∨ K = 64#u64

theorem ScRel1.wr_hdr {s : S} {sc : U64} {x : Fl4Spec.SchedContext} {n : Nat} (h : ScRel1 st s sc x n)
    {K : U64} (hK : HdrK K) (v : U64) :
    let s' := L.wr s (scW sc K) v
    RefillsWF st s' sc n ∧ L.rperiod s' sc = L.rperiod s sc ∧ L.rmax s' sc = L.rmax s sc ∧
      L.refills s' sc = L.refills s sc ∧
      (∀ K' : U64, K'.val < 96 → K'.val % 8 = 0 → K' ≠ K → L.mem s' (scW sc K') = L.mem s (scW sc K')) ∧
      L.mem s' (scW sc K) = v ∧ WritesIn st s s' (ScIn st s sc) := by
  intro s'
  obtain ⟨h8, h2, hfit⟩ := h.bounds
  have hKv : K.val < 96 ∧ K.val % 8 = 0 := by rcases hK with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  have ha := h.hdr hKv.1 hKv.2
  have hne : ∀ b : U64, Aligned b → b.val ≠ (scW sc K).val → L.mem s' b = L.mem s b :=
    fun b hb hb' => L.mem_wr_ne ha.1 hb (Ne.symm hb')
  have hv := scW_val (sc := sc) (K := K) (by omega)
  have hw : ∀ K' : U64, K'.val < 96 → K'.val % 8 = 0 → K' ≠ K → L.mem s' (scW sc K') = L.mem s (scW sc K') := by
    intro K' h1 h2 h3
    refine hne _ (h.hdr h1 h2).1 ?_
    rw [scW_val (by omega), hv]
    exact fun e => h3 (UScalar.eq_of_val_eq (by omega))
  have K72 : (72#u64 : U64) ≠ K := by rcases hK with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have K80 : (80#u64 : U64) ≠ K := by rcases hK with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have K88 : (88#u64 : U64) ≠ K := by rcases hK with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have K0 : (0#u64 : U64) ≠ K := by rcases hK with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have em : L.rmax s' sc = L.rmax s sc := by
    simp only [LawfulStore.rmax, maxA_eq]; exact hw _ (by simp) (by simp) K72
  have eh : L.rhead s' sc = L.rhead s sc := by
    simp only [LawfulStore.rhead, headA_eq]; exact hw _ (by simp) (by simp) K80
  have et : L.rtail s' sc = L.rtail s sc := by
    simp only [LawfulStore.rtail, tailA_eq]; exact hw _ (by simp) (by simp) K88
  have ep : L.rperiod s' sc = L.rperiod s sc := by
    simp only [LawfulStore.rperiod, periodA_eq]; exact hw _ (by simp) (by simp) K0
  have hW' : RefillsWF st s' sc n := h.wf.of_hdr em (by rw [eh]; exact h.wf.head_lt) (by rw [et]; exact h.wf.tail_lt)
  have hsz : L.size s' sc = L.size s sc := by simp only [LawfulStore.size, em, eh, et]
  have hrs : L.refills s' sc = L.refills s sc := by
    simp only [LawfulStore.refills, hsz]
    refine List.map_congr_left fun k _ => ?_
    have hix : L.ix s' sc k = L.ix s sc k := by simp only [LawfulStore.ix, em, eh]
    obtain ⟨-, -, -, -, -, hin⟩ := h.wf.inside
    obtain ⟨h1, h2', -⟩ := hin _ (h.wf.ix_lt k)
    unfold LawfulStore.rf LawfulStore.refill
    rw [hix, hne _ (by unfold Aligned; rw [h1]; omega) (by rw [h1, hv]; omega),
      hne _ (by unfold Aligned; rw [h2']; omega) (by rw [h2', hv]; omega)]
  refine ⟨hW', ep, em, hrs, hw, rd_wr_eq ha.1, (writesIn_wr ha.1).mono fun b hb => hb ▸ ha.2⟩

/-- Writing an SC's `TCB` word. -/
theorem SchedRel.set_sc_tcb {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {sc : U64} (hsc : sc ∈ C) {x : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap sc.bv = some (.schedContext x n)) (v : U64) :
    SchedRel st N T C c (L.wr s (scW sc 24#u64) v) (updSc σ sc.bv { x with scTcb := optRef v } n) ∧
      FootEq N T (L.mem s) (L.mem (L.wr s (scW sc 24#u64) v)) ∧
      KView σ (updSc σ sc.bv { x with scTcb := optRef v } n) := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x', n', hk', hx⟩ := hs.scs sc hsc
  rw [hk] at hk'; cases hk'
  obtain ⟨hW', ep, em, hrs, hw, hv, hwr⟩ := hx.wr_hdr (K := 24#u64) (by simp [HdrK]) v
  have hx' : ScRel1 st (L.wr s (scW sc 24#u64) v) sc { x with scTcb := optRef v } n :=
    ⟨hW', by rw [ep]; exact hx.period, by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.consumed,
      by rw [hv], by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.ntfn,
      by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.badge,
      by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.yieldFrom,
      by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.sporadic, by rw [em]; exact hx.max,
      by rw [hrs]; exact hx.refills⟩
  exact ⟨hS.sc_update hsc hk (hwr.mono fun b hb => hx.in_obj hb) (hw _ (by simp) (by simp) (by decide)) _ hx', scin_footEq hS hsc hwr, KView.of_sc hk⟩

/-- Writing a TCB's `SC` word, with `0` or an SC of `C`. -/
theorem SchedRel.set_tcb_sc {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {t : U64} (ht : t ∈ T) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x))
    {v : U64} (hv : v = 0#u64 ∨ v ∈ C) :
    SchedRel st N T C c (L.wr s (scA t) v) (updK σ t.bv (.tcb { x with tcbSchedContext := optRef v })) ∧
      FootEq N T (L.mem s) (L.mem (L.wr s (scA t) v)) ∧
      KView σ (updK σ t.bv (.tcb { x with tcbSchedContext := optRef v })) := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hN := hc.node
  have hta := hc.tcbs t ht
  have hA : Aligned (scA t) := field_aligned hta (K := 3464#u64) (by simp) (by simp)
  set s' := L.wr s (scA t) v
  have hk' : L.ksb s' = L.ksb s := L.ksb_wr _ _ _
  have nfo : ∀ b : U64, Aligned b → b ≠ scA t → L.mem s' b = L.mem s b := fun b hb hne => rd_wr_ne hA hb (Ne.symm hne)
  have nout : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o) :=
    fun o ho h8 => nfo _ (nodeAt_aligned hN ho h8) (nodeAt_ne_tfield hN ho ht hta (by simp))
  have tf : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (y = t → K ≠ 3464#u64) →
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := by
    intro y hy K h1 h2 h3
    refine nfo _ (field_aligned (hc.tcbs y hy) h1 h2) ?_
    show core.num.U64.wrapping_add y K ≠ core.num.U64.wrapping_add t 3464#u64
    rw [Ne, tt_eq_iff (hc.tcbs y hy) hta h1 (by simp)]
    rintro ⟨rfl, rfl⟩; exact h3 rfl rfl
  have hcag : CAgree st T c s s' := ⟨hk', L.cpu_wr _ _ _, fun o ho h8 _ _ _ _ _ => nout o ho h8,
    fun y hy K hK => by
      obtain ⟨h1, h2, -⟩ := schedField_ok (K := K) (by rcases hK with h | h | h | h | h <;> simp [SchedField, h])
      exact tf y hy K h1 h2 (fun _ => by rcases hK with h | h | h | h | h <;> subst h <;> decide)⟩
  have hscw : ∀ sc ∈ C, ScAgree st s s' sc := fun sc hsc a ha hin => nfo a ha (fun e => by
    have := (hS.scOutIn hsc hin).2.2.1 t ht
    rw [e, show (scA t).val = t.val + 3464 from by
      have := hta.fits; simp [scA, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega] at this
    omega)
  have hm := hs.rmax_eq hscw
  have nw : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → nodeW st s' c o = nodeW st s c o := by
    intro o ho h8; unfold Fl4Proofs.P3.Sched.nodeW; rw [nodeAt_ksb hk']; exact nout o ho h8
  have hdom : L.mem s' (curDomA st s) = L.mem s (curDomA st s) := nfo _ (curDomA_aligned hN) (fun e => by
    have h1 := hc.ksOut t ht
    have := congrArg UScalar.val e
    rw [curDomA_val hN, show (scA t).val = t.val + 3464 from by
      have := hta.fits; simp [scA, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega] at this
    omega)
  have hdt : L.mem s' (dtA st s) = L.mem s (dtA st s) := nfo _ (dtA_aligned hN) (fun e => by
    have h1 := hc.ksOut t ht
    have := congrArg UScalar.val e
    rw [dtA_val hN, show (scA t).val = t.val + 3464 from by
      have := hta.fits; simp [scA, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega] at this
    omega)
  refine ⟨⟨hS.placed, fun o ho => by rw [nodeAt_ksb hk']; exact hS.nodeNW o ho,
    by rw [curDomA_ksb hk']; exact hS.domNW, by rw [dtA_ksb hk']; exact hS.dtNW,
    scOut_transfer hk' (SzKeep.updK hk fun _ _ e => by cases e) hS.scOut,
    scDisj_transfer (SzKeep.updK hk fun _ _ e => by cases e) hS.scDisj,
    by rw [nw _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])]; exact hS.actW,
    by rw [nw _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])]; exact hS.act,
    by rw [nw _ (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])]; exact hS.repr,
    hs.core_eq hscw hS.core, Q, R, hc.agree hcag, ?_⟩, ?_, ?_⟩
  · refine ⟨hs.rq, hs.rqDom, hs.rel, ?_, ?_, ?_, ?_, ?_, fun y hy => ?_, fun y hy => ?_, fun sc hsc => ?_,
      by rw [nw _ (by simp [layout.node.IDLE_SC]) (by simp [layout.node.IDLE_SC])]; exact hs.idleSc,
      by rw [dtA_ksb hk', hdt]; exact hs.domTime,
      by rw [nw layout.node.IDLE_THREAD (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD])]; exact hs.idleTh⟩
    · rw [nw _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])]; exact hs.curThread
    · rw [nw _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])]; exact hs.curSc
    · rw [nw _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])]; exact hs.curTime
    · rw [nw _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])]; exact hs.consumed
    · rw [curDomA_ksb hk', hdom]; exact hs.curDom
    · obtain ⟨z, hkz, h1, h2, h3, h4⟩ := hs.tcb y hy
      have ed : L.mem s' (domA y) = L.mem s (domA y) := tf y hy (3432#u64) (by simp) (by simp) (fun _ => by decide)
      have ep : L.mem s' (prioA y) = L.mem s (prioA y) := tf y hy (3448#u64) (by simp) (by simp) (fun _ => by decide)
      by_cases e : y = t
      · subst e
        rw [hk] at hkz; cases hkz
        exact ⟨{ x with tcbSchedContext := optRef v }, by simp [updK], h1, by rw [ed]; exact h2,
          by rw [rd_wr_eq hA], by rw [ep]; exact h4⟩
      · have es : L.mem s' (scA y) = L.mem s (scA y) := tf y hy (3464#u64) (by simp) (by simp) (fun h => absurd h e)
        exact ⟨z, by simp [updK, bv_inj e, hkz], h1, by rw [ed]; exact h2, by rw [es]; exact h3, by rw [ep]; exact h4⟩
    · by_cases e : y = t
      · subst e; rw [rd_wr_eq hA]; intro h0; rcases hv with rfl | hv
        · exact absurd rfl h0
        · exact hv
      · have es : L.mem s' (scA y) = L.mem s (scA y) := tf y hy (3464#u64) (by simp) (by simp) (fun h => absurd h e)
        rw [es]; exact hs.scMem y hy
    · obtain ⟨z, m, hkz, hz⟩ := hs.scs sc hsc
      have : sc.bv ≠ t.bv := by intro e; rw [e, hk] at hkz; cases hkz
      exact ⟨z, m, by simp [updK, this, hkz], hz.agree (hscw sc hsc)⟩
  · intro a ha hf
    refine nfo a ha (fun e => ?_)
    subst e
    rcases hf with ⟨n0, hn0, h1, h2⟩ | ⟨y, hy, e | e | e | e | e | e⟩
    · have := hS.placed.disj n0 hn0 t ht
      rw [show (scA t).val = t.val + 3464 from by
        have := hta.fits; simp [scA, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega] at h1 h2
      omega
    all_goals first
      | (rw [tStA_eq] at e)
      | (rw [tBlockA_eq] at e)
      | (rw [badgeRegA_eq] at e)
      | (rw [prioA_eq'] at e)
      | (rw [nextEp_eq] at e)
      | (rw [prevEp_eq] at e)
    all_goals (rw [show scA t = core.num.U64.wrapping_add t 3464#u64 from rfl, tt_eq_iff hta (hc.tcbs y hy)
      (by simp) (by simp)] at e; obtain ⟨-, e⟩ := e; exact absurd e (by decide))
  · refine ⟨fun p z hp => ?_, fun p z hp => ?_⟩
    · have : p ≠ t.bv := by rintro rfl; rw [hk] at hp; cases hp
      simp [updK, this, hp]
    · by_cases e : p = t.bv
      · subst e; rw [hk] at hp; cases hp
        exact ⟨{ x with tcbSchedContext := optRef v }, by simp [updK], rfl, rfl, rfl⟩
      · exact ⟨z, by simp [updK, e, hp], rfl, rfl, rfl⟩

end

end

end Fl4Proofs.P3.Sched
