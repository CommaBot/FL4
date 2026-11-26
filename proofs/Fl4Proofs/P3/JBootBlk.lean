/-
P3 (line jboot, gen 3): **P1's `BlkOK` at the witness** (`JAtZ.blk`): the store `w0` (JBootMem), P1's heap `Hw`
(JBootZ), the cores `Csw = {0}` and the active SCs `C0 = {idle SC}`.

`Hw`'s sets: its TCBs are `T0` (`tcbs_Hw`), its SCs `C0` (`scs_Hw`, size exponent 7: `scBits_idS`), it has no
reply and no notification (`replies_Hw`, `ntfns_Hw`); its `Ω` words lie in `[kernelBase + 0x3000,
kernelBase + 0x7080)` or in the kernel-state block (`omega_pos`), its frame words are the idle SC's (`frame_pos`),
and every block word is in its `Ω` (`ks_omega`, from `ksH_omega`).

* **`w0_sqi`** (`SchedQueuesInv`, empty ready, release and endpoint queues), **`w0_bound`** (`BoundInv`),
  **`w0_objs`** (`ObjsOK`), **`w0_reply`** (`ReplyInv`), **`w0_scx`** (P1's `ScExtra`, the empty timer tree),
  **`w0_scsok`** (`SCsOK`), **`w0_sgok`** (`SgOK`), and **`w0_blk`** (`BlkOK`).

No sorry; no premises. New module; no existing statement changed.
-/
import Fl4Proofs.P3.JBootZ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.JBoot
open fl4_core Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit Classical

noncomputable section

set_option maxHeartbeats 1000000

/-! ## `Hw`'s sets -/

theorem Hw_kind {p : U64} {k : HKind} (h : Hw p = some k) : k = .tcb ∨ k = .sc 7 ∨ ∃ z, k = .other z := by
  rcases Hw_some h with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | h5
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨12, rfl⟩)
  · exact Or.inr (Or.inr ⟨5, rfl⟩)
  · rcases ksH_some h5 with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact Or.inr (Or.inr ⟨5, rfl⟩)
    · exact Or.inr (Or.inr ⟨3, rfl⟩)

theorem tcbs_Hw : Heap.tcbs Hw = T0 := by
  ext p
  simp only [Heap.tcbs, Set.mem_setOf_eq, T0, Set.mem_singleton_iff]
  constructor
  · intro h
    rcases Hw_some h with ⟨e, -⟩ | ⟨-, e⟩ | ⟨e, -⟩ | ⟨e, -⟩ | h5
    · exact e
    · cases e
    · cases e
    · cases e
    · rcases ksH_some h5 with ⟨e, -⟩ | ⟨e, -⟩ <;> cases e
  · rintro rfl; exact Hw_idT

theorem scs_Hw : Heap.scs Hw = C0 := by
  ext p
  simp only [Heap.scs, Set.mem_setOf_eq, C0, Set.mem_singleton_iff]
  constructor
  · rintro ⟨z, h⟩
    rcases Hw_some h with ⟨-, e⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | h5
    · cases e
    · exact e
    · cases e
    · cases e
    · rcases ksH_some h5 with ⟨e, -⟩ | ⟨e, -⟩ <;> cases e
  · rintro rfl; exact ⟨7, Hw_idS⟩

theorem replies_Hw : Heap.replies Hw = ∅ := by
  ext p
  simp only [Heap.replies, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro h
  rcases Hw_kind h with e | e | ⟨z, e⟩ <;> cases e

theorem ntfns_Hw : Heap.ntfns Hw = ∅ := by
  ext p
  simp only [Heap.ntfns, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro h
  rcases Hw_kind h with e | e | ⟨z, e⟩ <;> cases e

theorem scBits_idS : Heap.scBits Hw idS = 7 := by unfold Heap.scBits; rw [Hw_idS]

theorem Hw_of_ksH {p : U64} {k : HKind} (h : ksH fkb p = some k) : Hw p = some k := by
  have hv := ksH_some h
  rw [fkb_val] at hv
  have hb : 18446744071562133504 ≤ p.val ∧ p.val < 18446744071562133504 + 13568 := by
    rcases hv with ⟨-, h1, h2, -⟩ | ⟨-, h1, h2, -⟩ <;> omega
  unfold Hw
  rw [if_neg (fun e => by rw [e, idT_val] at hb; omega), if_neg (fun e => by rw [e, idS_val] at hb; omega),
    if_neg (by omega), if_neg (by omega)]
  exact h

/-- `Ω`'s words by position. -/
theorem omega_pos {b : U64} (h : b ∈ Heap.omega Hw) : b.val % 8 = 0 ∧
    ((18446744071562080256 ≤ b.val ∧ b.val < 18446744071562096768) ∨
     (18446744071562133504 ≤ b.val ∧ b.val < 18446744071562147072)) := by
  obtain ⟨hal, p, k, hp, hk, hin⟩ := h
  refine ⟨hal, ?_⟩
  unfold InObj at hin
  rcases Hw_pos hp with ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩
  · rcases hk with e' | ⟨z, e'⟩ | ⟨z, e'⟩ | ⟨e', -⟩ <;> cases e'
  all_goals simp only [HKind.bits, Nat.reducePow] at hin; omega

/-- The frame words are the idle SC's. -/
theorem frame_pos {b : U64} (h : b ∈ Heap.frame Hw) :
    b.val % 8 = 0 ∧ 18446744071562096640 ≤ b.val ∧ b.val < 18446744071562096768 := by
  obtain ⟨hal, p, k, hp, hk, hin⟩ := h
  refine ⟨hal, ?_⟩
  unfold InObj at hin
  rcases Hw_pos hp with ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
  all_goals try (rcases hk with e' | ⟨z, e'⟩ | ⟨e', -⟩ <;> cases e'; done)
  simp only [HKind.bits, Nat.reducePow] at hin; omega

theorem frame_of {b : U64} (hb : b.val % 8 = 0) (h1 : idS.val ≤ b.val) (h2 : b.val < idS.val + 128) :
    b ∈ Heap.frame Hw :=
  ⟨hb, idS, .sc 7, Hw_idS, Or.inr (Or.inl ⟨7, rfl⟩), h1, by simp only [HKind.bits, Nat.reducePow]; omega⟩

theorem scw_frame (K : U64) (hK : K.val < 128) (h8 : K.val % 8 = 0) :
    core.num.U64.wrapping_add idS K ∈ Heap.frame Hw := by
  have hv := wa_val (a := idS) (b := K) (by rw [idS_val]; omega)
  exact frame_of (by rw [hv, idS_val]; omega) (by rw [hv]; omega) (by rw [hv]; omega)

/-- **Every word of the kernel-state block is in `Ω`.** -/
theorem ks_omega : ∀ o : U64, o.val < 13568 → o.val % 8 = 0 →
    core.num.U64.wrapping_add (wL.ksb w0) o ∈ Heap.omega Hw := by
  intro o ho h8
  obtain ⟨hal, p, k, hp, hk, hin⟩ := ksH_omega (kb := fkb) fkb_lt fkb_fit.2.2 o ho h8
  exact ⟨hal, p, k, Hw_of_ksH hp, hk, hin⟩

/-! ## Words of the image -/

theorem actW0 : wL.actionW w0 = 0#u64 := act_w0
theorem idleW0 : wL.idleW w0 = idT := idleT_w0
theorem curW0 : wL.curW w0 = idT := curT_w0
theorem cscW0 : wL.cscW w0 = idS := curSc_w0

theorem st7 : wL.mem w0 (P1.stA idT) = 7#u64 := by
  rw [P1.stA_eq, tcbW_v _ (by decide) (by decide)]; decide

theorem n4 : (7#u64) ≠ sched.TS_BLOCKED_ON_SEND := by unfold sched.TS_BLOCKED_ON_SEND; decide
theorem n3 : (7#u64) ≠ sched.TS_BLOCKED_ON_RECV := by unfold sched.TS_BLOCKED_ON_RECV; decide
theorem n6 : (7#u64) ≠ sched.TS_BLOCKED_ON_NTFN := by unfold sched.TS_BLOCKED_ON_NTFN; decide
theorem n5 : (7#u64) ≠ sched.TS_BLOCKED_ON_REPLY := by unfold sched.TS_BLOCKED_ON_REPLY; decide

theorem nbl7 : ¬ Blocked (7#u64) := by
  rintro (h | h | h)
  · exact n4 h
  · exact n3 h
  · exact n6 h

theorem nbr7 : ¬ BlockedR (7#u64) := by
  rintro (h | h)
  · exact nbl7 h
  · exact n5 h

theorem bound_w0 : wL.mem w0 (boundA idT) = 0#u64 := by
  unfold boundA; exact JBoot.tcbZ _ (by decide) (by decide) (by decide) (by decide)
theorem blk_yield_w0 : wL.mem w0 (yieldA idT) = 0#u64 := by
  unfold yieldA; exact JBoot.tcbZ _ (by decide) (by decide) (by decide) (by decide)
theorem td_w0 : wL.mem w0 (tdA idT) = 0#u64 := by
  unfold tdA; exact JBoot.tcbZ _ (by decide) (by decide) (by decide) (by decide)
theorem tl_w0 : wL.mem w0 (tlA idT) = 0#u64 := by
  unfold tlA; exact JBoot.tcbZ _ (by decide) (by decide) (by decide) (by decide)
theorem tr_w0 : wL.mem w0 (trA idT) = 0#u64 := by
  unfold trA; exact JBoot.tcbZ _ (by decide) (by decide) (by decide) (by decide)
theorem tp_w0 : wL.mem w0 (tpA idT) = 0#u64 := by
  unfold tpA; exact JBoot.tcbZ _ (by decide) (by decide) (by decide) (by decide)
theorem blk_dn_w0 : wL.mem w0 (dnA idT) = 0#u64 := by
  unfold dnA; exact JBoot.tcbZ _ (by decide) (by decide) (by decide) (by decide)
theorem blk_dp_w0 : wL.mem w0 (dpA idT) = 0#u64 := by
  unfold dpA; exact JBoot.tcbZ _ (by decide) (by decide) (by decide) (by decide)

/-- A zero word of the idle SC. -/
theorem scZ (K : U64) (hK : K.val < 128) (h8 : K.val % 8 = 0) (h1 : K.val ≠ 24) (h2 : K.val ≠ 72)
    (h3 : K.val ≠ 88) (h4 : K.val ≠ 104) (h5 : K.val ≠ 112) :
    wL.mem w0 (core.num.U64.wrapping_add idS K) = 0#u64 := by
  rw [scW_v K hK h8]; img0

theorem scTcb_w0 : wL.mem w0 (scTcbA idS) = idT := by
  unfold scTcbA layout.sc.TCB; rw [scW_v _ (by decide) (by decide)]; decide
theorem scCore_w0 : wL.mem w0 (scCoreA idS) = 0#u64 := by
  unfold scCoreA layout.sc.CORE
  exact scZ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem blk_scReply_w0 : wL.mem w0 (scReplyA idS) = 0#u64 := by
  unfold scReplyA layout.sc.REPLY
  exact scZ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem scNtfn_w0 : wL.mem w0 (scNtfnA idS) = 0#u64 := by
  unfold scNtfnA layout.sc.NTFN
  exact scZ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem scYf_w0 : wL.mem w0 (scYieldFromA idS) = 0#u64 := by
  unfold scYieldFromA layout.sc.YIELD_FROM
  exact scZ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- A zero word of core 0's node. -/
theorem nodeZ (o : U64) (ho : o.val < 4288) (h8 : o.val % 8 = 0) (h0 : o.val ≠ 0) (h1 : o.val ≠ 8)
    (h2 : o.val ≠ 24) (h3 : o.val ≠ 32) : wL.mem w0 (wL.nodeAt w0 0#u64 o) = 0#u64 := by
  rw [show wL.mem w0 (wL.nodeAt w0 0#u64 o) = nodeW wst w0 0#u64 o from rfl, nodeW_v o ho h8]; img0

theorem troot_w0 : wL.mem w0 (wL.nodeAt w0 0#u64 layout.node.TIMER_ROOT) = 0#u64 := by
  unfold layout.node.TIMER_ROOT
  exact nodeZ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem tmin_w0 : wL.mem w0 (wL.nodeAt w0 0#u64 layout.node.TIMER_MIN) = 0#u64 := by
  unfold layout.node.TIMER_MIN
  exact nodeZ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem dbg_w0 : wL.mem w0 (wL.nodeAt w0 0#u64 layout.node.DEBUG_TCBS) = 0#u64 := by
  unfold layout.node.DEBUG_TCBS
  exact nodeZ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem memT0 {t : U64} (h : t ∈ T0) : t = idT := Set.mem_singleton_iff.mp h
theorem memC0 {c : U64} (h : c ∈ C0) : c = idS := Set.mem_singleton_iff.mp h
theorem memCs {c : U64} (h : c ∈ Csw) : c = 0#u64 := Set.mem_singleton_iff.mp h

/-! ## The scheduler queues -/

/-- **`SchedQueuesInv` at the witness** (every queue empty). -/
theorem w0_sqi : SchedQueuesInv wst T0 Csw (Heap.omega Hw) Hw w0 (fun _ _ => []) (fun _ => []) where
  tcbs := tcbPlaced_T0
  nodes c hc := by rw [memCs hc]; exact nodePlaced_w0
  cur := rfl
  aff t ht := by rw [memT0 ht, aff_w0]; rfl
  prio := w0_schedCore.prio
  ready c hc := by rw [memCs hc]; exact w0_schedCore.ready
  release c hc := by rw [memCs hc]; exact w0_schedCore.release
  inQ _ _ _ _ _ h := (List.not_mem_nil h).elim
  inR _ _ _ h := (List.not_mem_nil h).elim
  queued := w0_schedCore.queued
  released := w0_schedCore.released
  excl := w0_schedCore.excl
  action := Or.inl actW0
  runQ _ _ _ _ _ h := (List.not_mem_nil h).elim
  runR _ _ _ h := (List.not_mem_nil h).elim
  actOK h := by rw [actW0] at h; exact absurd (memT0 h) (by decide)
  eps := ⟨∅, fun _ => [], fun _ he => he.elim, fun _ he => he.elim, fun _ he => he.elim, fun _ he => he.elim,
    fun t ht _ hb => by rw [memT0 ht, st7] at hb; exact absurd hb nbl7,
    fun t ht _ hs => by rw [memT0 ht, st7] at hs; rcases hs with h | h; exact absurd h n4; exact absurd h n3,
    fun t ht _ hs => by rw [memT0 ht, st7] at hs; exact absurd hs n6,
    fun e => ⟨fun he => he.elim, fun h => by
      rcases h with h | h <;> rcases Hw_kind h with e | e | ⟨z, e⟩ <;> cases e⟩,
    fun _ he => he.elim, fun _ he => he.elim, fun _ he => he.elim⟩
  curT := w0_schedCore.curT
  idleT := w0_schedCore.idleT
  ksOut := w0_schedCore.ksOut
  omega a ha := by
    obtain ⟨hal, hr⟩ := omega_pos ha
    refine ⟨hal, fun t ht => ?_, fun c hc => ?_⟩
    · rw [memT0 ht, idT_val]; omega
    · rw [memCs hc, nodeBase_w0]; omega

/-- **`BoundInv` at the witness.** -/
theorem w0_bound : BoundInv wst T0 C0 w0 where
  q t ht h := by rw [memT0 ht, inq_w0] at h; simp at h
  r t ht h := by rw [memT0 ht, inq_w0] at h; simp at h
  act h := by rw [actW0] at h; exact absurd (memT0 h) (by decide)
  idle := by rw [idleW0, sc_w0]; decide
  resume _ := by rw [curW0, sc_w0]; decide
  idleNB := by rw [idleW0, st7]; exact nbr7
  sact t ht _ _ := by rw [memT0 ht, sc_w0]; rfl

/-! ## The objects -/

/-- **`ObjsOK` at the witness** (one SC, no reply, no notification). -/
theorem w0_objs : ObjsOK wst (Heap.omega Hw) (Heap.frame Hw) ∅ C0 ∅ (Heap.scBits Hw) w0 where
  rp _ h := h.elim
  sc c hc := by rw [memC0 hc, scBits_idS]; exact ⟨⟨by decide, by decide, by decide⟩, le_refl _⟩
  rpW _ h := h.elim
  scW c hc b hb hin := by
    rw [memC0 hc, scBits_idS] at hin
    exact Heap.frame_omega (frame_of hb hin.1 (by have := hin.2; simp only [Nat.reducePow] at this; omega))
  fixW c hc := by
    rw [memC0 hc]
    exact ⟨by unfold scTcbA layout.sc.TCB; exact scw_frame _ (by decide) (by decide),
      by unfold scCoreA layout.sc.CORE; exact scw_frame _ (by decide) (by decide)⟩
  scDisj c hc c' hc' hne := absurd ((memC0 hc).trans (memC0 hc').symm) hne
  rpSc _ h := h.elim
  repW c hc := by rw [memC0 hc]; unfold scReplyA layout.sc.REPLY; exact scw_frame _ (by decide) (by decide)
  ntW _ h := h.elim
  ntRp _ h := h.elim
  ntSc _ h := h.elim
  ntAl _ h := h.elim
  ntP _ h := h.elim
  ntB _ h := h.elim
  ntORp _ h := h.elim
  ntOSc _ h := h.elim
  snW c hc := by rw [memC0 hc]; unfold scNtfnA layout.sc.NTFN; exact scw_frame _ (by decide) (by decide)
  syW c hc := by
    rw [memC0 hc]; unfold scYieldFromA layout.sc.YIELD_FROM; exact scw_frame _ (by decide) (by decide)
  mxW c hc := by rw [memC0 hc]; unfold maxA layout.sc.REFILL_MAX; exact scw_frame _ (by decide) (by decide)
  nt0 _ h := h.elim
  rp0 _ h := h.elim
  sc0 c hc := by rw [memC0 hc]; decide

/-- **`ReplyInv` at the witness** (no reply; the idle thread neither blocked on a reply nor receiving). -/
theorem w0_reply : ReplyInv wst T0 ∅ C0 w0 where
  reply t ht h := by rw [memT0 ht, st7] at h; exact absurd h n5
  recv t ht h := by rw [memT0 ht, st7] at h; exact absurd h n3
  next _ h := h.elim
  prev _ h := h.elim
  back _ h := h.elim
  screp c hc h := by rw [memC0 hc, blk_scReply_w0] at h; exact absurd rfl h
  idle c hc _ := by rw [memC0 hc, blk_scReply_w0]
  head _ h := h.elim

/-- **P1's `ScExtra` at the witness** (the idle thread bound to the idle SC on core 0; the empty timer tree). -/
theorem w0_scx : P1.ScExtra wst T0 Csw C0 ∅ w0 where
  bound t ht _ := by rw [memT0 ht, sc_w0, scTcb_w0, scCore_w0]; exact ⟨rfl, rfl, rfl⟩
  cur := by rw [cscW0]; rfl
  core c hc := by rw [memC0 hc, scCore_w0]; rfl
  bnd t ht h := by rw [memT0 ht, bound_w0] at h; exact absurd rfl h
  nsc _ h := h.elim
  tm := {
    npl := fun c hc => by rw [memCs hc]; exact nodePlaced_w0
    lt := fun y hy => by rw [memT0 hy, tl_w0]; exact Or.inl rfl
    rt := fun y hy => by rw [memT0 hy, tr_w0]; exact Or.inl rfl
    pt := fun y hy => by rw [memT0 hy, tp_w0]; exact Or.inl rfl
    root := fun c hc => by rw [memCs hc, troot_w0]; exact Or.inl rfl
    min := fun c hc => by rw [memCs hc, tmin_w0]; exact Or.inl rfl
    core := fun y hy h => by rw [memT0 hy, td_w0] at h; exact absurd rfl h
    dn := fun y hy => by rw [memT0 hy, blk_dn_w0]; exact Or.inl rfl
    dp := fun y hy => by rw [memT0 hy, blk_dp_w0]; exact Or.inl rfl
    dh := fun c hc => by rw [memCs hc, dbg_w0]; exact Or.inl rfl }
  ntb _ h := h.elim
  rb := {
    tree := fun c hc => by
      rw [memCs hc]
      exact ⟨.leaf, {
        rep := TRB.Rep.leaf _ _ troot_w0
        nodup := List.nodup_nil
        inT := fun _ h => (List.not_mem_nil h).elim
        armed := fun _ h => (List.not_mem_nil h).elim
        core := fun _ h => (List.not_mem_nil h).elim
        sorted := List.Pairwise.nil
        bal := ⟨0, TRB.Bal.leaf⟩
        black := rfl
        min := tmin_w0 }⟩
    armed := fun y hy h => by rw [memT0 hy, td_w0] at h; exact absurd rfl h
    idle := fun y hy _ => by rw [memT0 hy, tl_w0, tr_w0, tp_w0]; exact ⟨rfl, rfl, rfl⟩ }
  scn c hc h := by rw [memC0 hc, scNtfn_w0] at h; exact absurd rfl h
  yt := ⟨fun c hc _ => by rw [memC0 hc, scTcb_w0]; rfl,
    fun t ht h => by rw [memT0 ht, blk_yield_w0] at h; exact absurd rfl h,
    fun c hc h => by rw [memC0 hc, scYf_w0] at h; exact absurd rfl h⟩
  bs := {
    tb := fun t ht h => by rw [memT0 ht, bound_w0] at h; exact absurd rfl h
    nt := fun _ h => h.elim
    sn := fun c hc _ h => by rw [memC0 hc, scNtfn_w0] at h; exact absurd rfl h }
  tsc c hc _ _ := by rw [memC0 hc, scTcb_w0, sc_w0]
  aff t ht _ := by rw [memT0 ht, sc_w0, scCore_w0, aff_w0]

/-- **`SCsOK` at the witness.** -/
theorem w0_scsok : SCsOK wst T0 (Heap.omega Hw) (Heap.frame Hw) C0 (Heap.scBits Hw) C0 w0 where
  sub _ hb := Heap.frame_omega hb
  ks b hb := by have := frame_pos hb; left; rw [ksb_w0, fkb_val]; omega
  ksΩ := ks_omega
  disj t ht _ h2 := by rw [memT0 ht, sc_w0, cscW0] at h2; exact absurd rfl h2
  all c hc := by
    rw [memC0 hc, scBits_idS]
    have wf7 : RefillsWF wst w0 idS 7 := wf_idS
    exact ⟨fun _ => wf7, by unfold maxA layout.sc.REFILL_MAX; exact scw_frame _ (by decide) (by decide),
      fun b hb hin => frame_of hb hin.1 (by have := hin.2; simp only [Nat.reducePow] at this; omega)⟩
  act c hc := ⟨fun _ => by rw [memC0 hc, rmax_w0]; decide, fun _ => hc⟩
  spor c hc _ := hc
  spSg c hc := by rw [memC0 hc]; unfold sporA layout.sc.SPORADIC; exact scw_frame _ (by decide) (by decide)
  rep c hc _ := hc
  repSg c hc := by rw [memC0 hc]; unfold scReplyA layout.sc.REPLY; exact scw_frame _ (by decide) (by decide)
  scKs c hc := by rw [memC0 hc, scBits_idS]; left; rw [ksb_w0, fkb_val, idS_val]; decide

/-- **`SgOK` at the witness.** -/
theorem w0_sgok : SgOK wst (Heap.omega Hw) (Heap.frame Hw) w0 where
  sub _ hb := Heap.frame_omega hb
  ks b hb := by have := frame_pos hb; left; rw [ksb_w0, fkb_val]; omega
  ksΩ := ks_omega

/-- **`JAtZ.blk` at the witness: P1's `BlkOK`.** -/
theorem w0_blk : P1.BlkOK wst (P1.Heap.tcbs Hw) Csw (P1.Heap.omega Hw) Hw (P1.Heap.frame Hw) (P1.Heap.replies Hw)
    (P1.Heap.scs Hw) (P1.Heap.ntfns Hw) (P1.Heap.scBits Hw) C0 w0 := by
  rw [tcbs_Hw, replies_Hw, scs_Hw, ntfns_Hw]
  exact ⟨⟨_, _, w0_sqi⟩, w0_bound, ⟨w0_objs, w0_reply, w0_scx⟩, w0_scsok, w0_sgok⟩

end

end Fl4Proofs.P3.JBoot
