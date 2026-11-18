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
  obtain ⟨hst, ep, em, hw, hv, hwr⟩ := hx.wr_hdr (K := 8#u64) (by simp [HdrK]) v
  have hx' : ScRelW st σ.idleSc (L.wr s (scW sc 8#u64) v) sc { x with scConsumed := v.bv } n :=
    ⟨hx.pl, by rw [ep]; exact hx.period, by rw [hv], by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.tcb, by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.ntfn, by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.badge, by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.yieldFrom, by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.sporadic, fun h0 => by rw [em]; exact hx.spor (by rwa [hw _ (by simp) (by simp) (by decide)] at h0), fun h0 => by rw [em]; exact hx.idle h0, by rw [em]; exact hx.max, fun h0 => ScRel1.ofWF (hst (by rwa [em] at h0)).1 (by rw [ep]; exact hx.period) (by rw [hv]) (by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.tcb) (by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.ntfn) (by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.badge) (by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.yieldFrom) (by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.sporadic) (by rw [em]; exact hx.max) (by rw [(hst (by rwa [em] at h0)).2]; exact (hx.act (by rwa [em] at h0)).refills)⟩
  exact ⟨hS.sc_updateW hsc hk (hwr.mono fun b hb => hx.in_obj hb) (hw _ (by simp) (by simp) (by decide)) _ hx', scin_footEq hS hsc hwr,
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
    have := (hS.scOutIn hsc hin).2.1; omega
  have hca : CAgree st T c s s' := ⟨hk, L.cpu_wr _ _ _, fun o ho h8 _ _ h _ _ _ _ _ => hne o ho h8 h,
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


/-! ## The current thread's timeout-handler slot, kept -/

section Tmo
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- **The words of `ct`'s timeout-handler slot (TCB slot 4, bytes 128..160)
and the spec's handler of `ct`, kept from `(s0, σ0)`**: what
`valid_timeout_handler` reads (`hval`). -/
def TmoKeep (st : machine.Store S) [L : LawfulStore st] (ct : U64) (s0 : S) (σ0 : Fl4Spec.State Unit) (s : S)
    (σ : Fl4Spec.State Unit) : Prop :=
  (∀ b : U64, Aligned b → ct.val + 128 ≤ b.val → b.val < ct.val + 160 → L.mem s b = L.mem s0 b) ∧
  ∀ x0, σ0.kheap ct.bv = some (.tcb x0) → ∃ x, σ.kheap ct.bv = some (.tcb x) ∧
    x.tcbTimeoutHandler = x0.tcbTimeoutHandler

theorem TmoKeep.refl (ct : U64) (s : S) (σ : Fl4Spec.State Unit) : TmoKeep st ct s σ s σ :=
  ⟨fun _ _ _ _ => rfl, fun x0 h => ⟨x0, h, rfl⟩⟩

theorem TmoKeep.trans {ct : U64} {s1 s2 s3 : S} {σ1 σ2 σ3 : Fl4Spec.State Unit} (h1 : TmoKeep st ct s1 σ1 s2 σ2)
    (h2 : TmoKeep st ct s2 σ2 s3 σ3) : TmoKeep st ct s1 σ1 s3 σ3 := by
  refine ⟨fun b hb e1 e2 => (h2.1 b hb e1 e2).trans (h1.1 b hb e1 e2), fun x0 hx0 => ?_⟩
  obtain ⟨x1, hx1, e1⟩ := h1.2 x0 hx0
  obtain ⟨x2, hx2, e2⟩ := h2.2 x1 hx1
  exact ⟨x2, hx2, e2.trans e1⟩

/-- `TmoKeep` from writes outside `ct`'s first 256 bytes and the TCB's
handler kept. -/
theorem TmoKeep.of_writes {ct : U64} {s0 s : S} {σ0 σ : Fl4Spec.State Unit} {W : U64 → Prop}
    (hw : WritesIn st s0 s W) (hW : ∀ b, W b → b.val < ct.val ∨ ct.val + 256 ≤ b.val)
    (hK : ∀ x0, σ0.kheap ct.bv = some (.tcb x0) → ∃ x, σ.kheap ct.bv = some (.tcb x) ∧
      x.tcbTimeoutHandler = x0.tcbTimeoutHandler) : TmoKeep st ct s0 σ0 s σ :=
  ⟨fun b hb e1 e2 => hw.mem_eq hb fun hb' => by rcases hW b hb' with e | e <;> omega, hK⟩

theorem TmoKeep.of_kheap {ct : U64} {s0 s : S} {σ0 σ : Fl4Spec.State Unit} {W : U64 → Prop}
    (hw : WritesIn st s0 s W) (hW : ∀ b, W b → b.val < ct.val ∨ ct.val + 256 ≤ b.val)
    (hk : σ.kheap ct.bv = σ0.kheap ct.bv) : TmoKeep st ct s0 σ0 s σ :=
  TmoKeep.of_writes hw hW fun x0 h => ⟨x0, by rw [hk]; exact h, rfl⟩

/-- **A scheduler footprint word is outside every TCB's first 256 bytes**
(its slots): TCB words at `SOff` offsets, node words, notification words
and SC words. -/
theorem kfoot_tslot {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {ct : U64} (ht : ct ∈ T) {b : U64} (hb : KFoot st T N C c s σ b) :
    b.val < ct.val ∨ ct.val + 256 ≤ b.val := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hca := hc.tcbs ct ht
  have h12 : (2 : ℕ) ^ 12 = 4096 := by norm_num
  have ca := hca.align
  rw [h12] at ca
  rcases hb with (⟨y, hy, K, hK, rfl⟩ | ⟨h1, h2⟩) | ⟨n, hn, h1, h2⟩ | ⟨sc, hsc, x, n, hk, hobj, -⟩
  · have hya := hc.tcbs y hy
    have ya := hya.align
    rw [h12] at ya
    obtain ⟨k1, k2, -, -⟩ := hK
    rw [tfield_val hya k2]
    by_cases e : y.val = ct.val
    · omega
    · omega
  · have := hc.node.disj ct ht; rw [h12] at this; omega
  · have := hS.placed.disj n hn ct ht; omega
  · have := (hS.scOut sc hsc x n hk b hobj).2.2.1 ct ht; omega

/-- A node word is outside every TCB's first 256 bytes. -/
theorem node_tslot {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {ct : U64} (ht : ct ∈ T) {o : U64} (ho : o.val < 4288) :
    (L.nodeAt s c o).val < ct.val ∨ ct.val + 256 ≤ (L.nodeAt s c o).val := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have := hc.node.disj ct ht
  rw [nodeAt_val hc.node ho]
  have h12 : (2 : ℕ) ^ 12 = 4096 := by norm_num
  rw [h12] at this; omega

/-- **A node write keeps `TmoKeep`**, the spec's heap unchanged. -/
theorem TmoKeep.node_wr {N T C : Set U64} {c : U64} {s : S} {σ σ' : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {ct : U64} (ht : ct ∈ T) {o : U64} (ho : o.val < 4288) (h8 : o.val % 8 = 0)
    (v : U64) (hk : σ'.kheap = σ.kheap) : TmoKeep st ct s σ (L.wr s (L.nodeAt s c o) v) σ' := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  refine TmoKeep.of_kheap (writesIn_wr (nodeAt_aligned hc.node ho h8)) (fun b e => ?_) (by rw [hk])
  rw [e]; exact node_tslot hS ht ho

end Tmo

end

end Fl4Proofs.P3.Sched
