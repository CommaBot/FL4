/-
P3 (DESIGN.md §9), scheduling contexts: the writes of `charge_budget` and
`commit_time` besides the refills: an SC's `CONSUMED` word
(`SchedRel.set_sc_consumed`, the spec's `sc_consumed`) and the node's
`CONSUMED` word (`SchedRel.set_node_consumed`, the spec's `consumed_time`).
-/
import Fl4Proofs.P3.ScInvB
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

@[step] theorem obj.Sc.consumed.spec' (s : S) (sc : obj.Sc) :
    obj.Sc.consumed st sc s ⦃ v => v = L.mem s (scW sc 8#u64) ⦄ := by
  unfold obj.Sc.consumed; step*; simp_all [scW, layout.sc.CONSUMED]
@[step] theorem obj.Sc.set_consumed.spec' (s : S) (sc : obj.Sc) (v : U64) :
    obj.Sc.set_consumed st sc s v ⦃ s' => s' = L.wr s (scW sc 8#u64) v ⦄ := by
  unfold obj.Sc.set_consumed; step*; simp_all [scW, layout.sc.CONSUMED]
@[step] theorem obj.Sc.badge.spec' (s : S) (sc : obj.Sc) :
    obj.Sc.badge st sc s ⦃ v => v = L.mem s (scW sc 48#u64) ⦄ := by
  unfold obj.Sc.badge; step*; simp_all [scW, layout.sc.BADGE]
@[step] theorem sched.consumed.spec' (s : S) :
    sched.consumed st s ⦃ v => v = nodeW st s (L.cpu s) layout.node.CONSUMED ⦄ := by
  unfold sched.consumed; step*; simp_all [nodeW]
@[step] theorem sched.set_consumed.spec' (s : S) (v : U64) :
    sched.set_consumed st s v ⦃ s' => s' = L.wr s (L.nodeAt s (L.cpu s) layout.node.CONSUMED) v ⦄ := by
  unfold sched.set_consumed; step*; simp_all
@[step] theorem sched.idle_sc.spec' (s : S) :
    sched.idle_sc st s ⦃ v => v = nodeW st s (L.cpu s) layout.node.IDLE_SC ⦄ := by
  unfold sched.idle_sc; step*; simp_all [nodeW]
@[step] theorem sched.set_reprogram.spec' (s : S) :
    sched.set_reprogram st s ⦃ s' => s' = L.wr s (L.nodeAt s (L.cpu s) layout.node.REPROGRAM) 1#u64 ⦄ := by
  unfold sched.set_reprogram; step*; simp_all

/-- Writing an SC's `CONSUMED` word. -/
theorem SchedRel.set_sc_consumed {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {sc : U64} (hsc : sc ∈ C) {x : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap sc.bv = some (.schedContext x n)) (v : U64) :
    SchedRel st N T C c (L.wr s (scW sc 8#u64) v) (updSc σ sc.bv { x with scConsumed := v.bv } n) ∧
      FootEq N T (L.mem s) (L.mem (L.wr s (scW sc 8#u64) v)) ∧
      KView σ (updSc σ sc.bv { x with scConsumed := v.bv } n) := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x', n', hk', hx⟩ := hs.scs sc hsc
  rw [hk] at hk'; cases hk'
  obtain ⟨hW', ep, em, hrs, hw, hv, hwr⟩ := hx.wr_hdr (K := 8#u64) (by simp [HdrK]) v
  have hx' : ScRel1 st (L.wr s (scW sc 8#u64) v) sc { x with scConsumed := v.bv } n :=
    ⟨hW', by rw [ep]; exact hx.period, by rw [hv],
      by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.tcb, by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.ntfn,
      by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.badge,
      by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.yieldFrom,
      by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.sporadic, by rw [em]; exact hx.max,
      by rw [hrs]; exact hx.refills⟩
  exact ⟨hS.sc_update hsc hk hwr em (hw _ (by simp) (by simp) (by decide)) _ hx', scin_footEq hS hsc hwr,
    KView.of_sc hk⟩

/-- Writing the node's `CONSUMED` word. -/
theorem SchedRel.set_node_consumed {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (v : U64) :
    SchedRel st N T C c (L.wr s (L.nodeAt s c layout.node.CONSUMED) v) { σ with consumedTime := v.bv } ∧
      FootEq N T (L.mem s) (L.mem (L.wr s (L.nodeAt s c layout.node.CONSUMED) v)) ∧
      ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 40 →
        nodeW st (L.wr s (L.nodeAt s c layout.node.CONSUMED) v) c o = nodeW st s c o := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hN := hc.node
  have h40 : layout.node.CONSUMED.val = 40 := by simp [layout.node.CONSUMED]
  have hA : Aligned (L.nodeAt s c layout.node.CONSUMED) := nodeAt_aligned hN (by omega) (by omega)
  set s' := L.wr s (L.nodeAt s c layout.node.CONSUMED) v
  have hk : L.ksb s' = L.ksb s := L.ksb_wr _ _ _
  have hne : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 40 →
      L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o) := by
    intro o ho h8 hne
    refine rd_wr_ne hA (nodeAt_aligned hN ho h8) fun e => hne ?_
    have := congrArg UScalar.val e
    rw [nodeAt_val hN (by omega), nodeAt_val hN ho] at this; omega
  have nw : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 40 → nodeW st s' c o = nodeW st s c o := by
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
    have := (hS.scOut sc hsc a hin).2.1; omega
  have hca : CAgree st T c s s' := ⟨hk, L.cpu_wr _ _ _, fun o ho h8 _ _ h _ => hne o ho h8 h,
    fun y hy K hK => htf y hy K (by rcases hK with h | h | h | h | h <;> simp [SchedField, h])⟩
  have hm := hs.rmax_eq hscw
  refine ⟨⟨hS.placed, fun o ho => by rw [nodeAt_ksb hk]; exact hS.nodeNW o ho,
    by rw [curDomA_ksb hk]; exact hS.domNW, scOut_transfer hk hm hS.scOut, scDisj_transfer hm hS.scDisj,
    by rw [nw _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
      (by simp [layout.node.SCHED_ACTION])]; exact hS.actW,
    by rw [nw _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
      (by simp [layout.node.SCHED_ACTION])]; exact hS.act,
    by rw [nw _ (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])
      (by simp [layout.node.REPROGRAM])]; exact hS.repr,
    hs.core_eq hscw hS.core, Q, R, hc.agree hca, ?_⟩, node_wr_foot hS (by omega) (by omega), nw⟩
  refine ⟨hs.rq, hs.rqDom, hs.rel, ?_, ?_, ?_, ?_, ?_, fun y hy => ?_, fun y hy => ?_, fun sc hsc => ?_⟩
  · rw [nw layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
      (by simp [layout.node.CUR_THREAD])]; exact hs.curThread
  · rw [nw layout.node.CUR_SC (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
      (by simp [layout.node.CUR_SC])]; exact hs.curSc
  · rw [nw layout.node.CUR_TIME (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
      (by simp [layout.node.CUR_TIME])]; exact hs.curTime
  · show v.bv = _
    unfold Fl4Proofs.P3.Sched.nodeW; rw [nodeAt_ksb hk, rd_wr_eq hA]
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

end

end

end Fl4Proofs.P3.Sched
