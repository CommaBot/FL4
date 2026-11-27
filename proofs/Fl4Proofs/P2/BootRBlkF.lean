/-
# P2 (line p3mc, gen 39, unit F): P1's `BlkOK` (`JAtZ.blk`) at the second boot start

At `sR` (P2/BootRMem) with the heap `HR` (P1's sets `HR.tcbs = {tiB, tRw}`, `HR.scs = {sciB, scRw}`, both SCs of
size `2^7`, no reply or notification; `Ω = HR.omega` = the two SCs, the three paging structures and the
kernel-state block; `Sg = HR.frame` = the two SCs' words), core set `CsB = {0}` and active SCs
**`AcR = {sciB, scRw}`** (gen 35's `P2/BootBlkF` at `sB`, now with the running root thread `tRw` current, bound to
`scRw`):

* `uF_sqi` (`SchedQueuesInv`: empty ready / release queues, no endpoint queue (the idle thread in state 7, the
  root thread running), the root thread current, the idle thread idle, action resume; `Ω` outside both TCBs and
  core 0's node);
* `uF_boundInv` (`BoundInv` both ways: each thread bound to its SC, both active);
* `uF_xInv` (`XInv`: `ObjsOK` from `HeapOK HR` (`ObjsOK.of_heap`), `ReplyInv` vacuous, `ScExtra`: the two SC /
  TCB links, empty timer trees `uF_coreTree`, no notification);
* `uF_scsOK` (`SCsOK`: both SCs' refills well formed, `uF_refillsWF`; the idle SC apart from the current SC
  `scRw`), `uF_sgOK`;
* **`blk_R`**: `BlkOK bst HR.tcbs CsB HR.omega HR HR.frame HR.replies HR.scs HR.ntfns HR.scBits AcR sR`.

No premise. No existing statement changed.
-/
import Fl4Proofs.P2.BootRZ
import Fl4Proofs.P2.BootBlkF
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.BootSt
open fl4_core Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P1 Classical

noncomputable section

/-! ## Offsets and words of `sR` -/

theorem uF_tR_off {k : U64} {n : Nat} (hk : k.val = n) (hn : n < 4096) :
    (core.num.U64.wrapping_add tRw k).val = 18446744071562076160 + n :=
  wa_val (by rw [tRw_val, hk]) (by omega)

theorem uF_scR_off {k : U64} {n : Nat} (hk : k.val = n) (hn : n < 4096) :
    (core.num.U64.wrapping_add scRw k).val = 18446744071562080256 + n :=
  wa_val (by rw [scRw_val, hk]) (by omega)

/-- A word of either TCB at offset `≥ 32` other than `STATE` / `SC`: 0. -/
theorem uF_tw0 {t : U64} (ht : t = tiB ∨ t = tRw) {K : U64} {k : Nat} (hK : K.val = k) (hk : k < 4096)
    (h8 : k % 8 = 0) (h0 : 32 ≤ k) (h1 : k ≠ 3328) (h2 : k ≠ 3464) :
    bsL.mem sR (core.num.U64.wrapping_add t K) = 0#u64 := by
  rcases ht with rfl | rfl
  · rw [memR_at (tiB_off hK hk) (by omega)]; exact wordR_zero_of (by omega)
  · rw [memR_at (uF_tR_off hK hk) (by omega)]; exact wordR_zero_of (by omega)

/-- The two SCs' addresses. -/
theorem uF_scv {c : U64} (hc : c = sciB ∨ c = scRw) :
    c.val = 18446744071562096640 ∨ c.val = 18446744071562080256 := by
  rcases hc with rfl | rfl
  · exact Or.inl sciB_val
  · exact Or.inr scRw_val

theorem uF_sc_off {c : U64} (hc : c = sciB ∨ c = scRw) {K : U64} {k : Nat} (hK : K.val = k) (hk : k < 4096) :
    (core.num.U64.wrapping_add c K).val = c.val + k := by
  rcases uF_scv hc with h | h
  · exact wa_val (by rw [hK]) (by rw [h]; omega)
  · exact wa_val (by rw [hK]) (by rw [h]; omega)

/-- A word of either SC other than `TCB`, `REFILL_MAX`, `REFILL_TAIL` and the two `MAX_PERIOD` words: 0. -/
theorem uF_sw0 {c : U64} (hc : c = sciB ∨ c = scRw) {K : U64} {k : Nat} (hK : K.val = k) (hk : k < 128)
    (h8 : k % 8 = 0) (h1 : k ≠ 24) (h2 : k ≠ 72) (h3 : k ≠ 88) (h4 : k ≠ 104) (h5 : k ≠ 112) :
    bsL.mem sR (core.num.U64.wrapping_add c K) = 0#u64 := by
  have hv := uF_sc_off hc hK (by omega)
  rcases uF_scv hc with h | h
  · rw [memR_at hv (by rw [h]; omega), h]; exact wordR_zero_of (by omega)
  · rw [memR_at hv (by rw [h]; omega), h]; exact wordR_zero_of (by omega)

/-- A node-0 word of `sR` by offset. -/
theorem uF_nw {o : U64} {k : Nat} (ho : o.val = k) (hk : k < 4288) (h8 : k % 8 = 0) :
    bsL.mem sR (bsL.nodeAt sR 0#u64 o) = wordR (18446744071562114304 + k) :=
  memR_at (by rw [sR_nodeAt_val (by omega), ho]) (by omega)

/-- A node-0 word other than the four thread / SC words: 0. -/
theorem uF_nw0 {o : U64} {k : Nat} (ho : o.val = k) (hk : k < 4288) (h8 : k % 8 = 0) (h1 : k ≠ 0) (h2 : k ≠ 8)
    (h3 : k ≠ 24) (h4 : k ≠ 32) : bsL.mem sR (bsL.nodeAt sR 0#u64 o) = 0#u64 := by
  rw [uF_nw ho hk h8]; exact wordR_zero_of (by omega)

theorem uF_stI : bsL.mem sR (P1.stA tiB) = 7#u64 := by
  have hv : (P1.stA tiB).val = 18446744071562072064 + 3328 := by
    rw [P1.stA_eq]; simp only [core.num.U64.wrapping_add_val_eq, tiB_val]; simp [U64.size, U64.numBits]
  rw [memR_at hv (by omega), wordR_of (by omega)]; simp [wordB]

theorem uF_stR : bsL.mem sR (P1.stA tRw) = 1#u64 := by
  have hv : (P1.stA tRw).val = 18446744071562076160 + 3328 := by
    rw [P1.stA_eq]; simp only [core.num.U64.wrapping_add_val_eq, tRw_val]; simp [U64.size, U64.numBits]
  rw [memR_at hv (by omega)]; simp [wordR]

theorem uF_scI : bsL.mem sR (scA tiB) = sciB := by
  rw [memR_at (a := scA tiB) (tiB_off (n := 3464) (by decide) (by omega)) (by omega), wordR_of (by omega)]
  simp [wordB]

theorem uF_scRR : bsL.mem sR (scA tRw) = scRw := by
  rw [memR_at (a := scA tRw) (uF_tR_off (n := 3464) (by decide) (by omega)) (by omega)]
  simp [wordR]

theorem uF_scTcbI : bsL.mem sR (scTcbA sciB) = tiB := by
  unfold scTcbA
  rw [memR_at (sciB_off (n := 24) (by simp [layout.sc.TCB]) (by omega)) (by omega), wordR_of (by omega)]
  simp [wordB]

theorem uF_scTcbR : bsL.mem sR (scTcbA scRw) = tRw := by
  unfold scTcbA
  rw [memR_at (uF_scR_off (n := 24) (by simp [layout.sc.TCB]) (by omega)) (by omega)]
  simp [wordR]

theorem uF_rmax {c : U64} (hc : c = sciB ∨ c = scRw) : bsL.rmax sR c = 2#u64 := by
  unfold LawfulStore.rmax maxA
  rcases hc with rfl | rfl
  · rw [memR_at (sciB_off (n := 72) (by simp [layout.sc.REFILL_MAX]) (by omega)) (by omega), wordR_of (by omega)]
    simp [wordB]
  · rw [memR_at (uF_scR_off (n := 72) (by simp [layout.sc.REFILL_MAX]) (by omega)) (by omega)]
    simp [wordR]

theorem uF_rhead {c : U64} (hc : c = sciB ∨ c = scRw) : bsL.rhead sR c = 0#u64 := by
  unfold LawfulStore.rhead headA
  exact uF_sw0 hc (k := 80) (by simp [layout.sc.REFILL_HEAD]) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)

theorem uF_rtail {c : U64} (hc : c = sciB ∨ c = scRw) : bsL.rtail sR c = 1#u64 := by
  unfold LawfulStore.rtail tailA
  rcases hc with rfl | rfl
  · rw [memR_at (sciB_off (n := 88) (by simp [layout.sc.REFILL_TAIL]) (by omega)) (by omega), wordR_of (by omega)]
    simp [wordB]
  · rw [memR_at (uF_scR_off (n := 88) (by simp [layout.sc.REFILL_TAIL]) (by omega)) (by omega)]
    simp [wordR]

theorem uF_refillsWF {c : U64} (hc : c = sciB ∨ c = scRw) :
    RefillsWF bst sR c (0 + Fl4Spec.minSchedContextBits) where
  placed := by
    rcases uF_scv hc with h | h <;>
    exact ⟨by simp [Fl4Spec.minSchedContextBits], by rw [h]; simp [Fl4Spec.minSchedContextBits],
      by rw [h]; simp [Fl4Spec.minSchedContextBits]⟩
  min_le := by rw [uF_rmax hc]; simp [sporadic.MIN_REFILLS]
  le_abs := by rw [uF_rmax hc]; simp [absMax, Fl4Spec.minSchedContextBits]
  head_lt := by rw [uF_rhead hc, uF_rmax hc]; decide
  tail_lt := by rw [uF_rtail hc, uF_rmax hc]; decide

theorem uF_scRw_ne0 : scRw ≠ 0#u64 := fun e => by
  have := congrArg UScalar.val e; rw [scRw_val] at this; exact absurd this (by decide)

theorem uF_tRw_ne0 : tRw ≠ 0#u64 := fun e => by
  have := congrArg UScalar.val e; rw [tRw_val] at this; exact absurd this (by decide)

/-! ## P1's sets of `HR` -/

theorem uF_tcbs {t : U64} (h : t ∈ HR.tcbs) : t = tiB ∨ t = tRw := by
  rcases HR_cases h with ⟨e, -⟩ | ⟨-, k⟩ | ⟨e, -⟩ | ⟨-, k⟩ | ⟨-, k⟩ | ⟨k, -⟩ | ⟨k, -⟩
  · exact Or.inr (eq_of_val'' (by rw [e, tRw_val]))
  · cases k
  · exact Or.inl (eq_of_val'' (by rw [e, tiB_val]))
  all_goals cases k

theorem uF_scs {c : U64} (h : c ∈ HR.scs) : c = sciB ∨ c = scRw := by
  obtain ⟨z, hz⟩ := h
  rcases HR_cases hz with ⟨-, k⟩ | ⟨e, -⟩ | ⟨-, k⟩ | ⟨e, -⟩ | ⟨-, k⟩ | ⟨k, -⟩ | ⟨k, -⟩
  · cases k
  · exact Or.inr (eq_of_val'' (by rw [e, scRw_val]))
  · cases k
  · exact Or.inl (eq_of_val'' (by rw [e, sciB_val]))
  all_goals cases k

theorem uF_replies {r : U64} (h : r ∈ HR.replies) : False := by
  rcases HR_cases h with ⟨-, k⟩ | ⟨-, k⟩ | ⟨-, k⟩ | ⟨-, k⟩ | ⟨-, k⟩ | ⟨k, -⟩ | ⟨k, -⟩ <;> cases k

theorem uF_ntfns {n : U64} (h : n ∈ HR.ntfns) : False := by
  rcases HR_cases h with ⟨-, k⟩ | ⟨-, k⟩ | ⟨-, k⟩ | ⟨-, k⟩ | ⟨-, k⟩ | ⟨k, -⟩ | ⟨k, -⟩ <;> cases k

theorem uF_scBits {c : U64} (hc : c = sciB ∨ c = scRw) : HR.scBits c = 7 := by
  rcases hc with rfl | rfl
  · exact Heap.scBits_eq HR_sci
  · exact Heap.scBits_eq HR_scR

theorem uF_scH {c : U64} (hc : c = sciB ∨ c = scRw) : HR c = some (.sc 7) := by
  rcases hc with rfl | rfl
  · exact HR_sci
  · exact HR_scR

theorem uF_HR_of_HB {p : U64} {k : HKind} (hp : HB p = some k) : HR p = some k := by
  have hne : p.val ≠ 18446744071562076160 ∧ p.val ≠ 18446744071562080256 := by
    rcases HB_cases hp with ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, g1, -⟩ | ⟨-, g1, -⟩ <;> omega
  unfold HR; rw [if_neg hne.1, if_neg hne.2]; exact hp

/-- The frame words: the two SCs' words. -/
theorem uF_frame {b : U64} (h : b ∈ HR.frame) : b.val % 8 = 0 ∧
    ((18446744071562096640 ≤ b.val ∧ b.val < 18446744071562096640 + 128) ∨
     (18446744071562080256 ≤ b.val ∧ b.val < 18446744071562080256 + 128)) := by
  obtain ⟨ha, p, k, hp, hk, h1, h2⟩ := h
  refine ⟨ha, ?_⟩
  rcases HR_cases hp with ⟨-, rfl⟩ | ⟨e, rfl⟩ | ⟨-, rfl⟩ | ⟨e, rfl⟩ | ⟨-, rfl⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · rcases hk with h | ⟨z, h⟩ | ⟨h, -⟩ <;> cases h
  · simp only [HKind.bits, Nat.reducePow] at h2; right; omega
  · rcases hk with h | ⟨z, h⟩ | ⟨h, -⟩ <;> cases h
  · simp only [HKind.bits, Nat.reducePow] at h2; left; omega
  all_goals (rcases hk with h | ⟨z, h⟩ | ⟨h, -⟩ <;> cases h)

theorem uF_inFrame {c : U64} (hc : c = sciB ∨ c = scRw) {b : U64} (h1 : c.val ≤ b.val)
    (h2 : b.val < c.val + 2 ^ 7) (h8 : b.val % 8 = 0) : b ∈ HR.frame :=
  ⟨h8, c, .sc 7, uF_scH hc, Or.inr (Or.inl ⟨7, rfl⟩), h1, h2⟩

/-- An SC word (offset `k < 128`, aligned) is a frame word. -/
theorem uF_scw_frame {c : U64} (hc : c = sciB ∨ c = scRw) {K : U64} {k : Nat} (hK : K.val = k) (hk : k < 128)
    (h8 : k % 8 = 0) : core.num.U64.wrapping_add c K ∈ HR.frame := by
  have hv := uF_sc_off hc hK (by omega)
  have hc8 := uF_scv hc
  exact uF_inFrame hc (by rw [hv]; omega) (by rw [hv]; simp only [Nat.reducePow]; omega)
    (by rw [hv]; omega)

/-- The words of `Ω` lie in `[scRw, node 0)`. -/
theorem uF_omega {b : U64} (h : b ∈ HR.omega) : b.val % 8 = 0 ∧
    18446744071562080256 ≤ b.val ∧ b.val < 18446744071562114304 := by
  obtain ⟨ha, p, k, hp, hk, h1, h2⟩ := h
  refine ⟨ha, ?_⟩
  rcases HR_cases hp with ⟨-, rfl⟩ | ⟨e, rfl⟩ | ⟨-, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨rfl, g1, g2, g3⟩ |
      ⟨rfl, g1, g2, g3, -⟩
  · rcases hk with h | ⟨z, h⟩ | ⟨z, h⟩ | ⟨h, -⟩ <;> cases h
  · simp only [HKind.bits, Nat.reducePow] at h2; omega
  · rcases hk with h | ⟨z, h⟩ | ⟨z, h⟩ | ⟨h, -⟩ <;> cases h
  all_goals (simp only [HKind.bits, Nat.reducePow] at h2; omega)

theorem uF_ksOmega : ∀ o : U64, o.val < 13568 → o.val % 8 = 0 →
    core.num.U64.wrapping_add (bsL.ksb sR) o ∈ HR.omega := by
  intro o ho h8
  have h := ksOmega_B o ho h8
  rw [sB_ksb] at h
  rw [sR_ksb]
  obtain ⟨ha, p, k, hp, hk, hin⟩ := h
  exact ⟨ha, p, k, uF_HR_of_HB hp, hk, hin⟩

/-! ## The threads' words -/

theorem uF_t0 {t : U64} (ht : t ∈ HR.tcbs) {K : U64} {k : Nat} (hK : K.val = k) (hk : k < 4096)
    (h8 : k % 8 = 0) (h0 : 32 ≤ k) (h1 : k ≠ 3328) (h2 : k ≠ 3464) :
    bsL.mem sR (core.num.U64.wrapping_add t K) = 0#u64 := uF_tw0 (uF_tcbs ht) hK hk h8 h0 h1 h2

theorem uF_inq {t : U64} (ht : t ∈ HR.tcbs) : bsL.mem sR (inqA t) = 0#u64 :=
  uF_t0 ht (k := 3592) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)
theorem uF_aff {t : U64} (ht : t ∈ HR.tcbs) : bsL.mem sR (affA t) = 0#u64 :=
  uF_t0 ht (k := 3520) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)
theorem uF_prio {t : U64} (ht : t ∈ HR.tcbs) : bsL.mem sR (prioA t) = 0#u64 :=
  uF_t0 ht (k := 3448) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)
theorem uF_bound {t : U64} (ht : t ∈ HR.tcbs) : bsL.mem sR (boundA t) = 0#u64 :=
  uF_t0 ht (k := 3368) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)
theorem uF_td {t : U64} (ht : t ∈ HR.tcbs) : bsL.mem sR (tdA t) = 0#u64 :=
  uF_t0 ht (k := 3528) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)
theorem uF_tl {t : U64} (ht : t ∈ HR.tcbs) : bsL.mem sR (tlA t) = 0#u64 :=
  uF_t0 ht (k := 3544) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)
theorem uF_tr {t : U64} (ht : t ∈ HR.tcbs) : bsL.mem sR (trA t) = 0#u64 :=
  uF_t0 ht (k := 3552) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)
theorem uF_tp {t : U64} (ht : t ∈ HR.tcbs) : bsL.mem sR (tpA t) = 0#u64 :=
  uF_t0 ht (k := 3560) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)
theorem uF_dn {t : U64} (ht : t ∈ HR.tcbs) : bsL.mem sR (dnA t) = 0#u64 :=
  uF_t0 ht (k := 3576) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)
theorem uF_dp {t : U64} (ht : t ∈ HR.tcbs) : bsL.mem sR (dpA t) = 0#u64 :=
  uF_t0 ht (k := 3584) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)
theorem uF_yield {t : U64} (ht : t ∈ HR.tcbs) : bsL.mem sR (yieldA t) = 0#u64 :=
  uF_t0 ht (k := 3472) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)

theorem uF_st {t : U64} (ht : t ∈ HR.tcbs) :
    bsL.mem sR (P1.stA t) = 7#u64 ∨ bsL.mem sR (P1.stA t) = 1#u64 := by
  rcases uF_tcbs ht with rfl | rfl
  · exact Or.inl uF_stI
  · exact Or.inr uF_stR

theorem uF_not_blocked1 : ¬ Blocked (1#u64) := by
  simp [Blocked, sched.TS_BLOCKED_ON_SEND, sched.TS_BLOCKED_ON_RECV, sched.TS_BLOCKED_ON_NTFN]

theorem uF_not_blocked {t : U64} (ht : t ∈ HR.tcbs) : ¬ Blocked (bsL.mem sR (P1.stA t)) := by
  rcases uF_st ht with e | e <;> rw [e]
  · exact not_blocked7
  · exact uF_not_blocked1

/-! ## The SCs' words -/

theorem uF_scCore {c : U64} (hc : c = sciB ∨ c = scRw) : bsL.mem sR (scCoreA c) = 0#u64 := by
  unfold scCoreA
  exact uF_sw0 hc (k := 16) (by simp [layout.sc.CORE]) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)

theorem uF_scReply {c : U64} (hc : c = sciB ∨ c = scRw) : bsL.mem sR (scReplyA c) = 0#u64 := by
  unfold scReplyA
  exact uF_sw0 hc (k := 32) (by simp [layout.sc.REPLY]) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)

theorem uF_scNtfn {c : U64} (hc : c = sciB ∨ c = scRw) : bsL.mem sR (scNtfnA c) = 0#u64 := by
  unfold scNtfnA
  exact uF_sw0 hc (k := 40) (by simp [layout.sc.NTFN]) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)

theorem uF_scYf {c : U64} (hc : c = sciB ∨ c = scRw) : bsL.mem sR (scYieldFromA c) = 0#u64 := by
  unfold scYieldFromA
  exact uF_sw0 hc (k := 56) (by simp [layout.sc.YIELD_FROM]) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)

theorem uF_spor {c : U64} (hc : c = sciB ∨ c = scRw) : bsL.mem sR (sporA c) = 0#u64 := by
  unfold sporA
  exact uF_sw0 hc (k := 64) (by simp [layout.sc.SPORADIC]) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)

/-! ## `SchedQueuesInv` -/

theorem uF_nodePlaced : NodePlaced bst HR.tcbs sR 0#u64 :=
  ⟨by rw [sR_nodeBase _ rfl], by rw [sR_nodeBase _ rfl]; norm_num, fun t ht => by
    rcases uF_tcbs ht with rfl | rfl
    · rw [sR_nodeBase _ rfl, tiB_val]; omega
    · rw [sR_nodeBase _ rfl, tRw_val]; omega⟩

theorem uF_actionW : bsL.actionW sR = 0#u64 := by
  unfold LawfulStore.actionW; rw [sR_cpu]
  exact uF_nw0 act_val (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

theorem uF_act_notT (h : bsL.actionW sR ∈ HR.tcbs) : False := by
  rw [uF_actionW] at h
  rcases uF_tcbs h with e | e
  · exact tiB_ne0' e.symm
  · exact uF_tRw_ne0 e.symm

theorem uF_ready : ReadyQueues bst HR.tcbs sR 0#u64 (fun _ => []) := by
  refine ⟨⟨fun p hp => ⟨List.nodup_nil, fun _ h => (List.not_mem_nil h).elim, ?_, ?_, trivial⟩,
    fun _ _ _ _ _ x h => (List.not_mem_nil h).elim⟩, ⟨fun p hp => ?_, fun i hi => ?_⟩⟩
  · show bsL.mem sR (bsL.nodeAt sR 0#u64 (rqOff p)) = 0#u64
    exact uF_nw0 (rqOff_val hp) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · show bsL.mem sR (bsL.nodeAt sR 0#u64 (rqTailOff p)) = 0#u64
    exact uF_nw0 (rqTailOff_val hp) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · show (bsL.mem sR (bsL.nodeAt sR 0#u64 (l2Off (p.val / 64)))).bv.getLsbD (p.val % 64) = true ↔ _
    rw [uF_nw0 (l2Off_val (by omega)) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    simp
  · show (bsL.mem sR (bsL.nodeAt sR 0#u64 l1Off)).bv.getLsbD i = true ↔ _
    rw [uF_nw0 l1Off_val (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    simp only [LawfulStore.l2W]
    constructor
    · intro h; simp at h
    · rintro ⟨hi4, hne⟩
      exact absurd (uF_nw0 (l2Off_val hi4) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)) hne

theorem uF_release : QueueRel (bsL.mem sR) HR.tcbs .Sched (bsL.relQ sR 0#u64) [] := by
  refine ⟨List.nodup_nil, fun _ h => (List.not_mem_nil h).elim, ?_, ?_, trivial⟩
  · show bsL.mem sR (bsL.nodeAt sR 0#u64 layout.node.RELEASE_HEAD) = 0#u64
    exact uF_nw0 (k := 64) (by simp [layout.node.RELEASE_HEAD]) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)
  · show bsL.mem sR (bsL.nodeAt sR 0#u64 (core.num.U64.wrapping_add layout.node.RELEASE_HEAD 8#u64)) = 0#u64
    exact uF_nw0 (k := 72) (by simp [layout.node.RELEASE_HEAD, core.num.U64.wrapping_add_val_eq, U64.size,
      U64.numBits]) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

theorem uF_sqi : SchedQueuesInv bst HR.tcbs CsB HR.omega HR sR (fun _ _ => []) (fun _ => []) where
  tcbs := fun t ht => by
    rcases uF_tcbs ht with rfl | rfl
    · exact tiB_addr
    · exact tRw_addr
  nodes c hc := by rw [mem_CsB hc]; exact uF_nodePlaced
  cur := by rw [sR_cpu]; rfl
  aff t ht := by rw [uF_aff ht]; rfl
  prio t ht := by rw [uF_prio ht]; decide
  ready c hc := by rw [mem_CsB hc]; exact uF_ready
  release c hc := by rw [mem_CsB hc]; exact uF_release
  inQ _ _ _ _ _ h := (List.not_mem_nil h).elim
  inR _ _ _ h := (List.not_mem_nil h).elim
  queued t ht := by rw [uF_inq ht]; simp
  released t ht := by rw [uF_inq ht]; simp
  excl _ _ h := (List.not_mem_nil h).elim
  action := Or.inl uF_actionW
  runQ _ _ _ _ _ h := (List.not_mem_nil h).elim
  runR _ _ _ h := (List.not_mem_nil h).elim
  actOK h := (uF_act_notT h).elim
  eps := by
    refine ⟨∅, fun _ => [], fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim,
      fun t ht _ hb => absurd hb (uF_not_blocked ht), ?_⟩
    refine ⟨fun t ht _ hs => ?_, fun t ht _ hs => ?_, fun e => ?_, fun _ h => h.elim, fun _ h => h.elim,
      fun _ h => h.elim⟩
    · rcases hs with h | h
      · exact absurd (Or.inl h) (uF_not_blocked ht)
      · exact absurd (Or.inr (Or.inl h)) (uF_not_blocked ht)
    · exact absurd (Or.inr (Or.inr hs)) (uF_not_blocked ht)
    · constructor
      · intro h; exact h.elim
      · rintro (h | h) <;>
          rcases HR_cases h with ⟨-, k⟩ | ⟨-, k⟩ | ⟨-, k⟩ | ⟨-, k⟩ | ⟨-, k⟩ | ⟨k, -⟩ | ⟨k, -⟩ <;> cases k
  curT := by
    show bsL.curW sR ∈ HR.tcbs
    rw [sR_curW]; exact HR_tR
  idleT := by
    show bsL.idleW sR ∈ HR.tcbs
    rw [sR_idleW]; exact HR_ti
  ksOut t ht := by
    rcases uF_tcbs ht with rfl | rfl
    · rw [sR_ksb, kbB_val, tiB_val]; omega
    · rw [sR_ksb, kbB_val, tRw_val]; omega
  omega a ha := by
    obtain ⟨h8, h1, h2⟩ := uF_omega ha
    refine ⟨h8, fun t ht => ?_, fun c hc => ?_⟩
    · rcases uF_tcbs ht with rfl | rfl
      · rw [tiB_val]; omega
      · rw [tRw_val]; omega
    · rw [mem_CsB hc, sR_nodeBase _ rfl]; omega

/-! ## `BoundInv` -/

theorem uF_boundInv : BoundInv bst HR.tcbs AcR sR where
  q t ht h := by rw [uF_inq ht] at h; simp at h
  r t ht h := by rw [uF_inq ht] at h; simp at h
  act h := (uF_act_notT h).elim
  idle := by rw [sR_idleW, uF_scI]; exact sciB_ne0
  resume _ := by rw [sR_curW, uF_scRR]; exact uF_scRw_ne0
  idleNB := by rw [sR_idleW, uF_stI]; exact not_blockedR7
  sact t ht _ _ := by
    rcases uF_tcbs ht with rfl | rfl
    · rw [uF_scI]; exact Or.inl rfl
    · rw [uF_scRR]; exact Or.inr rfl

/-! ## `XInv` -/

theorem uF_objsOK : ObjsOK bst HR.omega HR.frame HR.replies HR.scs HR.ntfns HR.scBits sR :=
  ObjsOK.of_heap heapR_ok HR_zero sR

theorem uF_replyInv : ReplyInv bst HR.tcbs HR.replies HR.scs sR where
  reply t ht h := by
    rcases uF_st ht with e | e <;> rw [e] at h <;> exact absurd h (by simp [sched.TS_BLOCKED_ON_REPLY])
  recv t ht h := by
    rcases uF_st ht with e | e <;> rw [e] at h <;> exact absurd h (by simp [sched.TS_BLOCKED_ON_RECV])
  next _ h := (uF_replies h).elim
  prev _ h := (uF_replies h).elim
  back _ h := (uF_replies h).elim
  screp c hc h := by rw [uF_scReply (uF_scs hc)] at h; exact absurd rfl h
  idle c hc _ := uF_scReply (uF_scs hc)
  head _ h := (uF_replies h).elim

theorem uF_coreTree : CoreTree bst HR.tcbs sR 0#u64 .leaf where
  rep := TRB.Rep.leaf _ _ (uF_nw0 timer_root_val (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
  nodup := List.nodup_nil
  inT _ h := (List.not_mem_nil h).elim
  armed _ h := (List.not_mem_nil h).elim
  core _ h := (List.not_mem_nil h).elim
  sorted := List.Pairwise.nil
  bal := ⟨0, TRB.Bal.leaf⟩
  black := rfl
  min := uF_nw0 timer_min_val (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

theorem uF_scExtra : ScExtra bst HR.tcbs CsB HR.scs HR.ntfns sR where
  bound t ht _ := by
    rcases uF_tcbs ht with rfl | rfl
    · rw [uF_scI, uF_scTcbI, uF_scCore (Or.inl rfl)]
      exact ⟨⟨7, HR_sci⟩, rfl, rfl⟩
    · rw [uF_scRR, uF_scTcbR, uF_scCore (Or.inr rfl)]
      exact ⟨⟨7, HR_scR⟩, rfl, rfl⟩
  cur := by rw [sR_cscW]; exact ⟨7, HR_scR⟩
  core c hc := by rw [uF_scCore (uF_scs hc)]; rfl
  bnd t ht h := by rw [uF_bound ht] at h; exact absurd rfl h
  nsc _ h := (uF_ntfns h).elim
  tm := {
    npl := fun c hc => by rw [mem_CsB hc]; exact uF_nodePlaced
    lt := fun y hy => by rw [uF_tl hy]; exact Tz.zero
    rt := fun y hy => by rw [uF_tr hy]; exact Tz.zero
    pt := fun y hy => by rw [uF_tp hy]; exact Tz.zero
    root := fun c hc => by
      rw [mem_CsB hc, uF_nw0 timer_root_val (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact Tz.zero
    min := fun c hc => by
      rw [mem_CsB hc, uF_nw0 timer_min_val (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact Tz.zero
    core := fun y hy h => by rw [uF_td hy] at h; exact absurd rfl h
    dn := fun y hy => by rw [uF_dn hy]; exact Tz.zero
    dp := fun y hy => by rw [uF_dp hy]; exact Tz.zero
    dh := fun c hc => by
      rw [mem_CsB hc, uF_nw0 debug_val (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact Tz.zero }
  ntb _ h := (uF_ntfns h).elim
  rb := {
    tree := fun c hc => by rw [mem_CsB hc]; exact ⟨_, uF_coreTree⟩
    armed := fun y hy h => by rw [uF_td hy] at h; exact absurd rfl h
    idle := fun y hy _ => ⟨uF_tl hy, uF_tr hy, uF_tp hy⟩ }
  scn c hc h := by rw [uF_scNtfn (uF_scs hc)] at h; exact absurd rfl h
  yt := ⟨fun c hc _ => by
      rcases uF_scs hc with rfl | rfl
      · rw [uF_scTcbI]; exact HR_ti
      · rw [uF_scTcbR]; exact HR_tR,
    fun t ht h => by rw [uF_yield ht] at h; exact absurd rfl h,
    fun c hc h => by rw [uF_scYf (uF_scs hc)] at h; exact absurd rfl h⟩
  bs := ⟨fun t ht h => by rw [uF_bound ht] at h; exact absurd rfl h,
    fun _ h => (uF_ntfns h).elim,
    fun c hc _ h => by rw [uF_scNtfn (uF_scs hc)] at h; exact absurd rfl h⟩
  tsc c hc _ _ := by
    rcases uF_scs hc with rfl | rfl
    · rw [uF_scTcbI, uF_scI]
    · rw [uF_scTcbR, uF_scRR]
  aff t ht _ := by
    rcases uF_tcbs ht with rfl | rfl
    · rw [uF_scI, uF_scCore (Or.inl rfl), uF_aff HR_ti]
    · rw [uF_scRR, uF_scCore (Or.inr rfl), uF_aff HR_tR]

theorem uF_xInv : XInv bst HR.tcbs CsB HR.omega HR.frame HR.replies HR.scs HR.ntfns HR.scBits sR :=
  ⟨uF_objsOK, uF_replyInv, uF_scExtra⟩

/-! ## `SCsOK`, `SgOK` -/

theorem uF_scsOK : SCsOK bst HR.tcbs HR.omega HR.frame HR.scs HR.scBits AcR sR where
  sub _ h := Heap.frame_omega h
  ks b h := by
    have := uF_frame h
    rw [sR_ksb, kbB_val]; omega
  ksΩ := uF_ksOmega
  disj t ht _ hne b hin := by
    rcases uF_tcbs ht with rfl | rfl
    · rw [uF_scI, uF_scBits (Or.inl rfl)] at hin
      obtain ⟨h1, h2⟩ := hin
      rw [sR_cscW, uF_scBits (Or.inr rfl)]
      show b.val < scRw.val ∨ scRw.val + 2 ^ 7 ≤ b.val
      rw [sciB_val] at h1 h2
      rw [scRw_val]
      simp only [Nat.reducePow] at h2 ⊢
      omega
    · rw [uF_scRR, sR_cscW] at hne; exact absurd rfl hne
  all c hc := by
    have hc' := uF_scs hc
    rw [uF_scBits hc']
    refine ⟨fun _ => uF_refillsWF hc',
      uF_scw_frame hc' (k := 72) (by simp [layout.sc.REFILL_MAX]) (by omega) (by omega),
      fun b hb hin => ?_⟩
    obtain ⟨h1, h2⟩ := hin
    exact uF_inFrame hc' h1 h2 hb
  act c hc := by
    rcases uF_scs hc with rfl | rfl
    · rw [uF_rmax (Or.inl rfl)]; exact ⟨fun _ => by decide, fun _ => Or.inl rfl⟩
    · rw [uF_rmax (Or.inr rfl)]; exact ⟨fun _ => by decide, fun _ => Or.inr rfl⟩
  spor c hc h := by rw [uF_spor (uF_scs hc)] at h; exact absurd rfl h
  spSg c hc := uF_scw_frame (uF_scs hc) (k := 64) (by simp [layout.sc.SPORADIC]) (by omega) (by omega)
  rep c hc h := by rw [uF_scReply (uF_scs hc)] at h; exact absurd rfl h
  repSg c hc := uF_scw_frame (uF_scs hc) (k := 32) (by simp [layout.sc.REPLY]) (by omega) (by omega)
  scKs c hc := by
    have hc' := uF_scs hc
    rw [uF_scBits hc', sR_ksb, kbB_val]
    rcases uF_scv hc' with h | h <;> rw [h] <;> left <;> norm_num

theorem uF_sgOK : SgOK bst HR.omega HR.frame sR := uF_scsOK.sg

/-- **P1's `BlkOK` at the second boot start** (`JAtZ.blk`). -/
theorem blk_R : BlkOK bst (Heap.tcbs HR) CsB (Heap.omega HR) HR (Heap.frame HR) (Heap.replies HR) (Heap.scs HR)
    (Heap.ntfns HR) (Heap.scBits HR) AcR sR :=
  ⟨⟨_, _, uF_sqi⟩, uF_boundInv, uF_xInv, uF_scsOK, uF_sgOK⟩

end

end Fl4Proofs.P2.BootSt
