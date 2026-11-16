/-
P3 (DESIGN.md §9), scheduling contexts: **`update_timestamp` refines l4v
`update_time_stamp`** (`update_timestamp_refines`) and keeps `Inv` and
`CurInv`.

The spec's clock is `do_machine_op getCurrentTime`; FL4's is the arch
`now`. Their agreement, and that the clock does not go back (l4v gets it
from `getCurrentTime`'s definition and `cur_time` being the last machine
time), is the hypothesis `hnow`. `Inv` reads the current time only through
`refill_ready`, which a later time keeps (`Inv.time`). One domain (`hnd`):
the domain-time update is skipped on both sides.
-/
import Fl4Proofs.P3.ScCharge8
import Fl4Proofs.P3.ScConsumed
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

/-- **A later current time keeps `Inv`**: a ready refill stays ready. -/
theorem Inv.time {σ σ' : State Unit} (h : Inv σ) (hk : σ'.kheap = σ.kheap)
    (hq : σ'.readyQueues = σ.readyQueues) (hr : σ'.releaseQueue = σ.releaseQueue) (ht : σ.curTime ≤ σ'.curTime) :
    Inv σ' := by
  refine ⟨fun d p u hu => ?_, fun u hu => ?_, ?_, fun u x hx hc => ?_, fun p y n hy => ?_,
    fun u x p hx hp => ?_, fun q x p hx hp => ?_, fun p y n hy => ?_, fun p y n hy => ?_⟩
  · rw [hq] at hu; rw [hk]; exact h.rq d p u hu
  · rw [hr] at hu; rw [hk]; exact h.rel u hu
  · rw [hr]
    refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab => ?_) h.sorted
    obtain ⟨xa, pa, ya, na, h1, h2, -, h4, h5⟩ := h.rel a ha
    obtain ⟨xb, pb, yb, nb, g1, g2, -, g4, g5⟩ := h.rel b hb
    rw [specRt_eq (by rw [hk]; exact h1) h2 (by rw [hk]; exact h4) (h.ne _ _ _ h4 h5),
      specRt_eq (by rw [hk]; exact g1) g2 (by rw [hk]; exact g4) (h.ne _ _ _ g4 g5)]
    rw [specRt_eq h1 h2 h4 (h.ne _ _ _ h4 h5), specRt_eq g1 g2 g4 (h.ne _ _ _ g4 g5)] at hab
    exact hab
  · rw [hk] at hx
    intro x' scp y n h1 h2 h3 h4 h5
    rw [hk] at h1 h3; rw [hr] at h5
    obtain ⟨r1, r2⟩ := h.rd u x hx hc x' scp y n h1 h2 h3 h4 h5
    refine ⟨?_, r2⟩
    simp only [refillReady', decide_eq_true_eq] at r1 ⊢
    exact BitVec.le_trans r1 ht
  · rw [hk] at hy; exact h.refills p y n hy
  · rw [hk] at hx ⊢; exact h.back u x p hx hp
  · rw [hk] at hx ⊢; exact h.ntfnSc q x p hx hp
  · rw [hk] at hy; exact h.ne p y n hy
  · rw [hk] at hy; exact h.rr p y n hy

end Spec

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

@[step] theorem sched.cur_time.spec' (s : S) :
    sched.cur_time st s ⦃ v => v = nodeW st s (L.cpu s) layout.node.CUR_TIME ⦄ := by
  unfold sched.cur_time; step*; simp_all [nodeW]

/-- `SchedRel` only reads these fields of the spec state. -/
theorem SchedRel.spec_congr {N T C : Set U64} {c : U64} {s : S} {σ σ' : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (hk : σ'.kheap = σ.kheap) (h1 : σ'.readyQueues = σ.readyQueues)
    (h2 : σ'.releaseQueue = σ.releaseQueue) (h3 : σ'.curThread = σ.curThread)
    (h4 : σ'.schedulerAction = σ.schedulerAction) (h5 : σ'.curSc = σ.curSc) (h6 : σ'.curTime = σ.curTime)
    (h7 : σ'.consumedTime = σ.consumedTime) (h8 : σ'.reprogramTimer = σ.reprogramTimer)
    (h9 : σ'.curDomain = σ.curDomain) (h10 : σ'.domainTime = σ.domainTime) (h11 : σ'.idleThread = σ.idleThread) :
    SchedRel st N T C c s σ' := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  refine ⟨hS.placed, hS.nodeNW, hS.domNW, hS.dtNW, scOut_transfer rfl (SzKeep.of_kheap hk) hS.scOut,
    scDisj_transfer (SzKeep.of_kheap hk) hS.scDisj, hS.actW, by rw [h4]; exact hS.act,
    by rw [h8]; exact hS.repr, hS.core, Q, R, hc, ?_⟩
  exact ⟨fun p hp => by rw [h1]; exact hs.rq p hp, fun d p hd => by rw [h1]; exact hs.rqDom d p hd,
    by rw [h2]; exact hs.rel, by rw [h3]; exact hs.curThread, by rw [h5]; exact hs.curSc,
    by rw [h6]; exact hs.curTime, by rw [h7]; exact hs.consumed, by rw [h9]; exact hs.curDom,
    fun t ht => by rw [hk]; exact hs.tcb t ht, hs.scMem, fun sc hsc => by rw [hk]; exact hs.scs sc hsc, hs.idleSc,
    by rw [h10]; exact hs.domTime, by rw [h11]; exact hs.idleTh⟩

/-- Writing the node's `CUR_TIME` word. -/
theorem SchedRel.set_node_curtime {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (v : U64) :
    SchedRel st N T C c (L.wr s (L.nodeAt s c layout.node.CUR_TIME) v) { σ with curTime := v.bv } ∧
      FootEq N T (L.mem s) (L.mem (L.wr s (L.nodeAt s c layout.node.CUR_TIME) v)) ∧
      ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 48 →
        nodeW st (L.wr s (L.nodeAt s c layout.node.CUR_TIME) v) c o = nodeW st s c o := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hN := hc.node
  have h48 : layout.node.CUR_TIME.val = 48 := by simp [layout.node.CUR_TIME]
  have hA : Aligned (L.nodeAt s c layout.node.CUR_TIME) := nodeAt_aligned hN (by omega) (by omega)
  set s' := L.wr s (L.nodeAt s c layout.node.CUR_TIME) v
  have hk : L.ksb s' = L.ksb s := L.ksb_wr _ _ _
  have hne : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 48 →
      L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o) := by
    intro o ho h8 hne
    refine rd_wr_ne hA (nodeAt_aligned hN ho h8) fun e => hne ?_
    have := congrArg UScalar.val e
    rw [nodeAt_val hN (by omega), nodeAt_val hN ho] at this; omega
  have nw : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 48 → nodeW st s' c o = nodeW st s c o := by
    intro o ho h8 h; unfold Fl4Proofs.P3.Sched.nodeW; rw [nodeAt_ksb hk]; exact hne o ho h8 h
  have htf : ∀ y ∈ T, ∀ K, SchedField K →
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := by
    intro y hy K hK
    obtain ⟨h1, h2, -⟩ := schedField_ok hK
    exact rd_wr_ne hA (field_aligned (hc.tcbs y hy) h1 h2) (nodeAt_ne_tfield hN (by omega) hy (hc.tcbs y hy) h1)
  have hdom : L.mem s' (curDomA st s) = L.mem s (curDomA st s) := by
    refine rd_wr_ne hA (curDomA_aligned hN) fun e => ?_
    have := congrArg UScalar.val e
    rw [nodeAt_val hN (by omega), curDomA_val hN] at this
    simp only [LawfulStore.nodeBase] at this; omega
  have hscw : ∀ sc ∈ C, ScAgree st s s' sc := by
    intro sc hsc a hal hin
    refine rd_wr_ne hA hal fun e => ?_
    have := congrArg UScalar.val e
    rw [nodeAt_val hN (by omega)] at this
    have := (hS.scOutIn hsc hin).2.1; omega
  have hca : CAgree st T c s s' := ⟨hk, L.cpu_wr _ _ _, fun o ho h8 _ _ _ h _ => hne o ho h8 h,
    fun y hy K hK => htf y hy K (by rcases hK with h | h | h | h | h <;> simp [SchedField, h])⟩
  have hm := hs.rmax_eq hscw
  refine ⟨⟨hS.placed, fun o ho => by rw [nodeAt_ksb hk]; exact hS.nodeNW o ho,
    by rw [curDomA_ksb hk]; exact hS.domNW, by rw [dtA_ksb hk]; exact hS.dtNW,
    scOut_transfer hk (SzKeep.of_kheap rfl) hS.scOut, scDisj_transfer (SzKeep.of_kheap rfl) hS.scDisj,
    by rw [nw _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
      (by simp [layout.node.SCHED_ACTION])]; exact hS.actW,
    by rw [nw _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
      (by simp [layout.node.SCHED_ACTION])]; exact hS.act,
    by rw [nw _ (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])
      (by simp [layout.node.REPROGRAM])]; exact hS.repr,
    hs.core_eq hscw hS.core, Q, R, hc.agree hca, ?_⟩, node_wr_foot hS (by omega) (by omega), nw⟩
  refine ⟨hs.rq, hs.rqDom, hs.rel, ?_, ?_, ?_, ?_, ?_, fun y hy => ?_, fun y hy => ?_, fun sc hsc => ?_,
    by rw [nw layout.node.IDLE_SC (by simp [layout.node.IDLE_SC]) (by simp [layout.node.IDLE_SC]) (by simp [layout.node.IDLE_SC])]; exact hs.idleSc,
    by rw [dtA_ksb hk, dt_wr_node hN (by omega) (by omega)]; exact hs.domTime,
    by rw [nw layout.node.IDLE_THREAD (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD])]; exact hs.idleTh⟩
  · rw [nw layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
      (by simp [layout.node.CUR_THREAD])]; exact hs.curThread
  · rw [nw layout.node.CUR_SC (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
      (by simp [layout.node.CUR_SC])]; exact hs.curSc
  · show v.bv = _
    unfold Fl4Proofs.P3.Sched.nodeW; rw [nodeAt_ksb hk, rd_wr_eq hA]
  · rw [nw layout.node.CONSUMED (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
      (by simp [layout.node.CONSUMED])]; exact hs.consumed
  · rw [curDomA_ksb hk, hdom]; exact hs.curDom
  · obtain ⟨x, hkx, h1, h2, h3, h4⟩ := hs.tcb y hy
    have e1 : L.mem s' (domA y) = L.mem s (domA y) := htf y hy _ (by simp [SchedField])
    have e2 : L.mem s' (scA y) = L.mem s (scA y) := htf y hy _ (by simp [SchedField])
    have e3 : L.mem s' (prioA y) = L.mem s (prioA y) := htf y hy _ (by simp [SchedField])
    exact ⟨x, hkx, h1, by rw [e1]; exact h2, by rw [e2]; exact h3, by rw [e3]; exact h4⟩
  · have e2 : L.mem s' (scA y) = L.mem s (scA y) := htf y hy _ (by simp [SchedField])
    rw [e2]; exact hs.scMem y hy
  · obtain ⟨x, n, hkx, e⟩ := hs.scs sc hsc
    exact ⟨x, n, hkx, e.agree (hscw sc hsc)⟩

theorem num_domains_eq : layout.NUM_DOMAINS = 1#u64 := by
  unfold layout.NUM_DOMAINS fl4_abi.config.NUM_DOMAINS; rfl

/-- **`update_timestamp` refines `update_time_stamp`**, keeping `Inv`, `CurInv`,
the scheduler action and the node words other than the time and consumed
time. -/
theorem update_timestamp_refines {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ)
    (hnd : Fl4Spec.numDomains = 1)
    (hnow : ar.now a ⦃ r => ∃ ms, Fl4Spec.doMachineOp (Z := Unit) Fl4Spec.getCurrentTime σ =
      ({(r.1.bv, { σ with machineState := ms })}, False) ∧ σ.curTime ≤ r.1.bv ⦄) :
    sched.update_timestamp st ar s a ⦃ r => ∃ σ', Fl4Spec.updateTimeStamp (Z := Unit) σ = ({((), σ')}, False) ∧
      SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ (Inv σ → Inv σ') ∧
      (CurInv σ → CurInv σ') ∧ σ'.schedulerAction = σ.schedulerAction ∧
      (∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 40 → o.val ≠ 48 → nodeW st r.1 c o = nodeW st s c o) ∧
      (OffReady σ → OffReady σ') ∧ (ActIdle σ → ActIdle σ') ∧ (∀ t ∈ T, TmoKeep st t s σ r.1 σ') ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  unfold sched.update_timestamp
  step with sched.cur_time.spec' as ⟨prev, hprev⟩
  rw [hc.cur] at hprev
  subst hprev
  refine WP.spec_bind hnow ?_
  rintro ⟨now, a1⟩ ⟨ms, hm, hle⟩
  step with LawfulStore.cur_cpu_spec as ⟨cpu, hcpu⟩
  rw [hc.cur] at hcpu
  subst cpu
  step with obj.node_set.spec as ⟨s1, hs1⟩
  subst hs1
  try simp only [lift, bind_ok]
  set σm : Fl4Spec.State Unit := { σ with machineState := ms } with hσm
  have hSm : SchedRel st N T C c s σm := hS.spec_congr rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  obtain ⟨hS1, hf1, nw1⟩ := hSm.set_node_curtime now
  set s1 := L.wr s (L.nodeAt s c layout.node.CUR_TIME) now with hs1d
  have hc1 := hS1.lists.choose_spec.choose_spec.1.cur
  have hcons1 := hS1.lists.choose_spec.choose_spec.2.consumed
  step with sched.consumed.spec' as ⟨i, hi⟩
  rw [hc1] at hi
  subst hi
  try simp only [lift, bind_ok]
  step with sched.set_consumed.spec' as ⟨s2, hs2⟩
  rw [hc1] at hs2
  subst hs2
  obtain ⟨hS2, hf2, nw2⟩ := hS1.set_node_consumed (core.num.U64.wrapping_add (nodeW st s1 c layout.node.CONSUMED)
    (core.num.U64.wrapping_sub now (nodeW st s c layout.node.CUR_TIME)))
  rw [num_domains_eq, if_neg (by decide)]
  rw [WP.spec_ok]
  set σ' : Fl4Spec.State Unit := { { σm with curTime := now.bv } with
    consumedTime := σm.consumedTime + (now.bv - σ.curTime) } with hσ'
  have ht : (core.num.U64.wrapping_add (nodeW st s1 c layout.node.CONSUMED)
      (core.num.U64.wrapping_sub now (nodeW st s c layout.node.CUR_TIME))).bv = σm.consumedTime + (now.bv - σ.curTime) := by
    rw [core.num.U64.wrapping_add_bv_eq, core.num.U64.wrapping_sub_bv_eq, ← hcons1, hs.curTime]
  rw [ht] at hS2
  have hspec : Fl4Spec.updateTimeStamp (Z := Unit) σ = ({((), σ')}, False) := by
    unfold Fl4Spec.updateTimeStamp
    rw [nd_gets_bind, nd_bind_one hm, nd_pure_bind',
      nd_bind_one (rfl : Fl4Spec.NonDet.modify (fun s : Fl4Spec.State Unit => { s with curTime := now.bv }) σm =
        ({((), { σm with curTime := now.bv })}, False)),
      nd_bind_one (rfl : Fl4Spec.NonDet.modify (fun s : Fl4Spec.State Unit =>
        { s with consumedTime := s.consumedTime + (now.bv - σ.curTime) }) { σm with curTime := now.bv } =
        ({((), σ')}, False)), nd_gets_bind]
    unfold Fl4Spec.NonDet.when
    rw [if_neg (by rw [hnd]; decide)]
    rfl
  refine ⟨σ', hspec, hS2, hR.frame hS.placed (FootEq.trans' hf1 hf2) (KView.of_kheap rfl), hN,
    fun hI => hI.time rfl rfl rfl hle, fun hC => hC.congr rfl rfl rfl rfl, rfl, fun o h1 h2 h3 h4 => ?_,
    fun ho y m hy => ?_, fun hA => hA.keep (TKeepE.of_kheap _ rfl) (fun _ h => h) (Or.inl rfl) rfl,
    fun t ht => (TmoKeep.node_wr hS ht (o := layout.node.CUR_TIME) (by simp [layout.node.CUR_TIME])
      (by simp [layout.node.CUR_TIME]) now (σ' := { σm with curTime := now.bv }) rfl).trans
      (TmoKeep.node_wr hS1 ht (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]) _ rfl)⟩
  · rw [nw2 o h1 h2 h3, nw1 o h1 h2 h4]
  · have h0 : (Fl4Spec.refillHd y).rTime.toNat + σ.consumedTime.toNat ≤ σ.curTime.toNat := ho y m hy
    have hle0 : σ.curTime ≤ now.bv := hle
    have hle' : σ.curTime.toNat ≤ now.bv.toNat := by rw [← BitVec.le_def]; exact hle0
    have hlt := now.bv.isLt
    show (Fl4Spec.refillHd y).rTime.toNat + (σ.consumedTime + (now.bv - σ.curTime)).toNat ≤ now.bv.toNat
    rw [BitVec.toNat_add, BitVec.toNat_sub_of_le hle0, Nat.mod_eq_of_lt (by omega)]
    omega

end

end

end Fl4Proofs.P3.Sched
