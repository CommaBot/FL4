/-
P3 (DESIGN.md §9), TCB invocations: **Bind/UnbindNotification on `IRel`**:
FL4 writes the notification's `BOUND_TCB` word and the TCB's
`BOUND_NOTIFICATION` word, the spec the two bound fields.

* `sre_tcb_wr`: `SRE` across a write of a TCB word that is no scheduler
  field, the spec's TCB keeping its domain, SC and priority.
* `NtfnStateRel.set_bound`, `SchedRel.set_ntfn_bound`: the notification's
  bound word (as ScNtfnBind's `set_sc`).
* `TcbRelE.bound_wr`: a TCB's endpoint relation across its bound word.
* **`bound_wr_irel`**: `IRel` across both writes.
-/
import Fl4Proofs.P3.IpcSetPrio
import Fl4Proofs.P3.ScNtfnBind
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

section Bound
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- **`SRE` across a write of a TCB word that is no scheduler field.** -/
theorem sre_tcb_wr {s : S} {σ : Fl4Spec.State Unit} (hS : SRE st N T C E R B c s σ) {t : U64} (ht : t ∈ T)
    {x x' : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) {K : U64} (hK : K.val < 4096) (hK8 : K.val % 8 = 0)
    (hKs : ∀ K', SchedField K' → K'.val ≠ K.val) (v : U64)
    (h1 : x'.tcbDomain = x.tcbDomain) (h2 : x'.tcbSchedContext = x.tcbSchedContext)
    (h3 : x'.tcbPriority = x.tcbPriority) :
    SRE st N T C E R B c (L.wr s (core.num.U64.wrapping_add t K) v) (updK σ t.bv (.tcb x')) := by
  obtain ⟨Q, R0, hc, -⟩ := hS.1.lists
  have hta := hc.tcbs t ht
  have ha := sagree_tcb_wr hS.1 ht hK hK8 hKs v
  have hw : Aligned (core.num.U64.wrapping_add t K) := field_aligned hta hK hK8
  have hn : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      nodeW st (L.wr s (core.num.U64.wrapping_add t K) v) c o = nodeW st s c o := fun o ho h8 => by
    unfold Fl4Proofs.P3.Sched.nodeW; rw [Sched.nodeAt_ksb (st := st) (L.ksb_wr _ _ _)]
    exact rd_wr_ne hw (nodeAt_aligned hc.node ho h8) (Ne.symm (nodeAt_ne_tfield hc.node ho ht hta hK))
  refine ⟨hS.1.of_sagreeE ha (hn _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]))
    (hn _ (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])) hS.1.nodeNW hS.1.domNW hS.1.dtNW
    (SchedStep.updK_tcb hk h1 h2 h3), hS.2.mono (L.ksb_wr _ _ _) (SzKeep.updK hk (fun _ _ h => by cases h))⟩

/-- **Writing a notification's bound word** keeps the notification relation. -/
theorem ntfn_set_bound {s : S} {σ : Fl4Spec.State Unit}
    (hR : NtfnStateRel N T (L.mem s) σ) (hP : NPlaced T N) {n : U64} (hn : n ∈ N)
    {x : Fl4Spec.Notification} (hk : σ.kheap n.bv = some (.notification x)) (v : U64) (hv : v ≠ 0#u64 → v ∈ T) :
    NtfnStateRel N T (L.mem (L.wr s (nBoundA n) v))
      (updK σ n.bv (.notification { x with ntfnBoundTcb := optRef v })) := by
  have hw : NWr st N T n s (L.wr s (nBoundA n) v) := by
    rw [nBoundA_eq]; exact nwr_wr hP hn (by simp) (by simp) s v
  have hna := hP.ntfn n hn
  obtain ⟨x0, hk0, hx0⟩ := hR.ntfn n hn
  rw [hk] at hk0; cases hk0
  have ha := (nword hP hn (K := 24#u64) (by simp) (by simp)).1
  have keep : ∀ K : U64, K.val < 40 → K.val % 8 = 0 → K ≠ 24#u64 →
      L.mem (L.wr s (nBoundA n) v) (core.num.U64.wrapping_add n K) = L.mem s (core.num.U64.wrapping_add n K) := by
    intro K h1 h2 h3
    rw [nBoundA_eq]
    exact rd_wr_ne ha (nword hP hn h1 h2).1 (nwords_ne hna (by simp) (by omega) (Ne.symm h3))
  have hh : L.mem (L.wr s (nBoundA n) v) (epHeadA n) = L.mem s (epHeadA n) := by
    rw [epHeadA_eq]; exact keep _ (by simp) (by simp) (by decide)
  have ht : L.mem (L.wr s (nBoundA n) v) (epTSA n) = L.mem s (epTSA n) := by
    rw [epTSA_eq]; exact keep _ (by simp) (by simp) (by decide)
  have hb : L.mem (L.wr s (nBoundA n) v) (nBadgeA n) = L.mem s (nBadgeA n) := by
    rw [nBadgeA_eq]; exact keep _ (by simp) (by simp) (by decide)
  have hsc : L.mem (L.wr s (nBoundA n) v) (nScA n) = L.mem s (nScA n) := by
    rw [nScA_eq]; exact keep _ (by simp) (by simp) (by decide)
  have hbd : L.mem (L.wr s (nBoundA n) v) (nBoundA n) = v := by rw [nBoundA_eq]; exact rd_wr_eq ha
  refine hR.upd_ntfn hn _ hw.ntfn (fun y hy => (hw.tcb y hy).1) (fun y hy _ => (hw.tcb y hy).2) ?_
  refine ⟨NtfnObjRel.frame_sc hx0.obj hh ht hb (fun y hy _ => ⟨(hw.tcb y hy).1.st, (hw.tcb y hy).1.blk, (hw.tcb y hy).2⟩),
    ?_, ?_, ?_⟩
  · show optRef v = _; rw [hbd]
  · rw [hbd]; exact hv
  · show x.ntfnSc = _; rw [hsc]; exact hx0.sc

/-- **Writing a notification's bound word** keeps the scheduler relation. -/
theorem sched_set_ntfn_bound {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {n : U64} (hn : n ∈ N) {x : Fl4Spec.Notification}
    (hk : σ.kheap n.bv = some (.notification x)) (x' : Fl4Spec.Notification) (v : U64) :
    SchedRel st N T C c (L.wr s (nBoundA n) v) (updK σ n.bv (.notification x')) := by
  have hw : NWr st N T n s (L.wr s (nBoundA n) v) := by
    rw [nBoundA_eq]; exact nwr_wr hS.placed hn (by simp) (by simp) s v
  refine hS.stableW hw.foot ⟨rfl, rfl, fun q => ?_⟩
  by_cases e : q = n.bv
  · subst e; exact Or.inr (Or.inl ⟨x, x', hk, by simp [updK]⟩)
  · exact Or.inl (by simp [updK, e])

/-- A TCB's endpoint relation across a write of its bound word. -/
theorem _root_.Fl4Proofs.P3.Endp.TcbRelE.bound_wr {m m' : U64 → U64} {t : U64} {x : Fl4Spec.Tcb} (ht : TcbAddr t)
    (h : TcbRelE R m t x) (hA : ∀ b, Aligned b → b.val ≠ t.val + 3368 → m' b = m b) (nb : Option Fl4Spec.ObjRef)
    (hp : nb = optRef (m' (tBoundA t))) : TcbRelE R m' t { x with tcbBoundNotification := nb } := by
  have g : ∀ {b : U64}, Aligned b → b.val ≠ t.val + 3368 → m' b = m b := fun hb hv => hA _ hb hv
  refine ⟨?_, fun e he => ?_, fun e d hs => ?_, fun e r d hs => ?_, fun r hs => ?_, fun r => ?_, ?_, ?_, ?_, hp, ?_⟩
  · rw [g (a_st ht).1 (by rw [val_st ht]; omega)]; exact h.st
  · rw [g (a_blk ht).1 (by rw [val_blk ht]; omega)]; exact h.blk e he
  · rw [g (a_badge ht).1 (by rw [val_badge ht]; omega), g (a_flags ht).1 (by rw [val_flags ht]; omega)]
    exact h.send e d hs
  · rw [g (a_reply ht).1 (by rw [val_reply ht]; omega)]; exact h.recv e r d hs
  · rw [g (a_reply ht).1 (by rw [val_reply ht]; omega)]; exact h.reply r hs
  · rw [g (a_reg ht r).1 (by rw [regA_val ht (regIdx_lt r)]; have := regIdx_lt r; omega)]; exact h.regs r
  · rw [g (a_prio ht).1 (by rw [val_prio ht]; omega)]; exact h.prio
  · rw [g (a_fault ht).1 (by rw [val_fault ht]; omega)]; exact h.fault0
  · rw [g (a_fault ht).1 (by rw [val_fault ht]; omega)]; exact h.faultT
  · exact h.faultR.congr' ht (fun v => v ≠ t.val + 3368) hA fun k h1 h2 => by omega

/-- A notification update keeps `VsKeep`. -/
theorem VsKeep.updK_ntfn {σ : Fl4Spec.State Unit} {p : Fl4Spec.ObjRef} {x y : Fl4Spec.Notification}
    (hk : σ.kheap p = some (.notification x)) : VsKeep σ (updK σ p (.notification y)) := by
  refine ⟨rfl, rfl, rfl, rfl, fun q ao hq => ?_, SzKeep.updK hk (fun _ _ h => by cases h), fun q z hq => ?_⟩
  · have e : q ≠ p := by rintro rfl; rw [hk] at hq; cases hq
    simp [updK, Function.update_of_ne e]
  · have e : q ≠ p := by rintro rfl; rw [hk] at hq; cases hq
    exact ⟨z, by simpa [updK, Function.update_of_ne e] using hq, rfl⟩

/-- A notification update keeps the caps. -/
theorem CKeep.updK_ntfn {σ : Fl4Spec.State Unit} {p : Fl4Spec.ObjRef} {x y : Fl4Spec.Notification}
    (hk : σ.kheap p = some (.notification x)) : CKeep σ (updK σ p (.notification y)) := by
  refine ⟨fun o => ?_, fun o r cs hc' _ => ?_, fun o z hz => ?_, rfl, rfl⟩
  · by_cases e : o = p
    · subst e
      refine ⟨fun r cs h _ => by simp [updK] at h, fun z h => by simp [updK] at h, fun hn => by rw [hk] at hn; cases hn⟩
    · simp only [updK, Function.update_of_ne e]
      exact ⟨fun r cs h hw => ⟨cs, h, hw⟩, fun y h => ⟨y, h⟩, id⟩
  · have e : o ≠ p := by rintro rfl; rw [hk] at hc'; cases hc'
    simp only [updK, Function.update_of_ne e]; exact hc'
  · have e : o ≠ p := by rintro rfl; rw [hk] at hz; cases hz
    exact ⟨z, by simp only [updK, Function.update_of_ne e]; exact hz, rfl⟩

/-- A TCB update with the same caps keeps the caps. -/
theorem CKeep.updK_tcbB {σ : Fl4Spec.State Unit} {p : Fl4Spec.ObjRef} {x : Fl4Spec.Tcb}
    (hk : σ.kheap p = some (.tcb x)) (nb : Option Fl4Spec.ObjRef) :
    CKeep σ (updK σ p (.tcb { x with tcbBoundNotification := nb })) := by
  refine ⟨fun o => ?_, fun o r cs hc' _ => ?_, fun o y hy => ?_, rfl, rfl⟩
  · by_cases e : o = p
    · subst e
      refine ⟨fun r cs h _ => by simp [updK] at h, fun _ _ => ⟨x, hk⟩, fun hn => by rw [hk] at hn; cases hn⟩
    · simp only [updK, Function.update_of_ne e]
      exact ⟨fun r cs h hw => ⟨cs, h, hw⟩, fun y h => ⟨y, h⟩, id⟩
  · have e : o ≠ p := by rintro rfl; rw [hk] at hc'; cases hc'
    simp only [updK, Function.update_of_ne e]; exact hc'
  · by_cases e : o = p
    · subst e; rw [hk] at hy; cases hy
      exact ⟨{ x with tcbBoundNotification := nb }, by simp [updK], rfl⟩
    · exact ⟨y, by simp only [updK, Function.update_of_ne e]; exact hy, rfl⟩

set_option maxHeartbeats 8000000 in
/-- **`IRel` across the two bound words** (Bind/UnbindNotification): the
notification's `BOUND_TCB` to `vn`, then the TCB's `BOUND_NOTIFICATION` to
`vp`. -/
theorem bound_wr_irel (hP0 : IPlaced N T E R B) {s : S} {σ : Fl4Spec.State Unit}
    (hX : IRel st th cr N T C E R B c s σ) {p n : U64} (hp : p ∈ T) (hn : n ∈ N) {x : Fl4Spec.Tcb}
    {xn : Fl4Spec.Notification} (hk : σ.kheap p.bv = some (.tcb x)) (hkn : σ.kheap n.bv = some (.notification xn))
    (vn vp : U64) (hvn : vn ≠ 0#u64 → vn ∈ T) :
    IRel st th cr N T C E R B c (L.wr (L.wr s (nBoundA n) vn) (tBoundA p) vp)
      (updK (updK σ n.bv (.notification { xn with ntfnBoundTcb := optRef vn })) p.bv
        (.tcb { x with tcbBoundNotification := optRef vp })) := by
  have hP := hP0.e
  have hT := hP.tcb
  have hpa := hT p hp
  obtain ⟨hIR, hT1, hSE⟩ := hX
  -- the notification's bound word
  have hna := hP0.n.ntfn n hn
  have hba : Aligned (nBoundA n) := by rw [nBoundA_eq]; exact (nword hP0.n hn (K := 24#u64) (by simp) (by simp)).1
  have hbv : (nBoundA n).val = n.val + 24 := by rw [nBoundA_eq]; exact nfield_val hna (by simp)
  set x1 : Fl4Spec.Notification := { xn with ntfnBoundTcb := optRef vn }
  set s1 := L.wr s (nBoundA n) vn
  set σA := updK σ n.bv (.notification x1)
  have hN1 := ntfn_set_bound hIR.toN hP0.n hn hkn vn hvn
  have hx1 : NtfnRel1 (L.mem s1) T n x1 := by
    obtain ⟨y, hy, hy1⟩ := hN1.ntfn n hn
    simp [updK] at hy; subst hy; exact hy1
  have hIR1 : IpcRel N T E R B (L.mem s1) σA := by
    refine hIR.upd_ntfn hP0 hn x1 (fun b hb ⟨_, hnw, _⟩ => rd_wr_ne hba hb fun e => hnw ?_) hx1
    subst e; unfold NW; rw [hbv]; omega
  have hNT : NoBufW T (nBoundA n) := NoBufW.out hT fun t ht => by have := hP0.n.disj n hn t ht; omega
  have hSRT1 : SRT st th cr N T C E R B c (SRE st N T C E R B c) s1 σA :=
    ⟨hT1.frame (writesIn_wr hba) (fun a ha => Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, by rw [ha, hbv]; omega,
        by rw [ha, hbv]; omega⟩)))) (fun a ha => by rw [ha]; exact hNT) (CKeep.updK_ntfn hkn) rfl rfl
      (VsKeep.updK_ntfn hkn),
     sched_set_ntfn_bound hSE.1 hn hkn x1 vn, hSE.2.mono (L.ksb_wr _ _ _) (SzKeep.updK hkn (fun _ _ h => by cases h))⟩
  -- the TCB's bound word
  have hpn : p.bv ≠ n.bv := fun e => by rw [e, hkn] at hk; cases hk
  have hkA : σA.kheap p.bv = some (.tcb x) := by simp [σA, updK, hpn, hk]
  have hta := (a_bound hpa).1
  have hbvp := val_bound hpa
  have hA : ∀ b, Aligned b → b.val ≠ p.val + 3368 → L.mem (L.wr s1 (tBoundA p) vp) b = L.mem s1 b :=
    fun b hb h => rd_wr_ne hta hb (fun e => h (by rw [← e, hbvp]))
  obtain ⟨y1, hky1, hyr⟩ := hIR1.tcb p hp
  rw [hkA] at hky1; cases hky1
  have hTR : TcbRel R (L.mem (L.wr s1 (tBoundA p) vp)) p { x with tcbBoundNotification := optRef vp } := by
    refine TcbRel.of (hyr.toE.bound_wr hpa hA _ (by rw [rd_wr_eq hta])) ?_ ?_
    · exact ⟨by rw [hA _ (a_st hpa).1 (by rw [val_st hpa]; omega)]; exact hyr.st,
        fun n' hn' => by rw [hA _ (a_blk hpa).1 (by rw [val_blk hpa]; omega)]; exact hyr.blkN n' hn',
        by rw [hA _ (by rw [badgeRegA_eq_regA]; exact (a_reg hpa _).1) (by
          rw [badgeRegA_eq_regA, regA_val hpa (regIdx_lt _)]; have := regIdx_lt Fl4Spec.badge_register; omega)]
           rw [badgeRegA_eq_regA]; exact hyr.regs _,
        by rw [hA _ (a_prio hpa).1 (by rw [val_prio hpa]; omega)]; exact hyr.prio⟩
    · show x.tcbSchedContext = _
      rw [hA _ (scA_aligned hpa) (by rw [scA_val hpa]; omega)]
      exact hyr.sc
  have hIR2 := hIR1.upd_tcb hP0 hp _ (fun b hb ⟨_, hn'⟩ => hA b hb fun e => hn' (Or.inl (TF.of_val (a_bound hpa).2
      (by rw [hbvp]; exact e))))
    (Or.inr ⟨hA _ (a_st hpa).1 (by rw [val_st hpa]; omega), hA _ (a_blk hpa).1 (by rw [val_blk hpa]; omega)⟩) hTR
  refine ⟨hIR2, hSRT1.1.frame (writesIn_wr hta) (fun a ha => Or.inl ⟨p, hp, by rw [ha, hbvp]; omega,
      by rw [ha, hbvp]; omega⟩) (fun a ha => by rw [ha]; exact NoBufW.off hT hp (by simp) (by simp))
    (CKeep.updK_tcbB hkA _) rfl rfl (VsKeep.updK_tcb hkA rfl), ?_⟩
  exact sre_tcb_wr hSRT1.2 hp hkA (K := 3368#u64) (by simp) (by simp) (fun K' h => by
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) vp rfl rfl rfl

end Bound

end

end Fl4Proofs.P3.Ipc
