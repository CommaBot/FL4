/-
# P2 (line p3mc, gen 39, unit B): the CSpace / MDB `JAtZ` fields at the second boot start

Every slot of the typed heap `thR` is the root slot `tRw` (cap `Thread tRw`), the timeout-handler slot `tmoW`
(cap `SchedContext scRw 7`), both revocable with links 0, or holds four zero words (`slotR_cases`), so the MDB
ghost is **`GR`** (two one-slot chains `[tRw]`, `[tmoW]`, no parent). At `ZR` (P2/BootRZ), as gen 34's
`P2/BootMdbF` at `(sB, σB)`:

* `placed_R` (`Placed thR`), `delBound_R` (`DelBound`, `DelBound.of_placed`);
* `mdbLinks_R` (`MdbLinks`), `cdtRel_R` (`CdtRel`: `initCdt` empty, `σR`'s original-cap map true exactly at the two
  capped slots (`iocR_iff`), whose revocable bits are set (`revOf_R_root`, `revOf_R_tmo`), elsewhere 0), `finM_R`
  (`FinM` at every tree: the two caps name different objects, `uB_novl`), `delInv_R` (`DelInv`), `utInv_R`
  (`UtInv` at `GR`: neither cap's range wraps), `sfree_R` (`SpecFree`), `utc_R` (no untyped cap), `zD_R` (no
  zombie);
* **`jcov_R`** (`JCovD thR HR GR DB CsB sR`): the root TCB covered by the thread cap's range, the root SC by the SC
  cap's range, the idle TCB / SC exempt as idle objects, the block's objects as `KsObj`, the three paging
  structures dead (`DB`).

No premise. No existing statement changed.
-/
import Fl4Proofs.P2.BootRZ
import Fl4Proofs.P2.BootMdbF
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.BootSt
open fl4_core Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P1 Classical

noncomputable section

theorem placed_R : Placed thR where
  align p k hp := by rcases thR_cases hp with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, g1, g2, g3⟩ <;> omega
  fits p k hp := by
    rcases thR_cases hp with ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨rfl, g1, g2, g3⟩ <;> simp only [P3.objSize, Nat.pow_zero] <;>
      omega
  disj p q kp kq hp hq hne := by
    have hv := U64.ne_of_val hne
    rcases thR_cases hp with ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨rfl, g1, g2, g3⟩ <;>
      rcases thR_cases hq with ⟨f, rfl⟩ | ⟨f, rfl⟩ | ⟨rfl, f1, f2, f3⟩ <;>
      simp only [P3.objSize, Nat.pow_zero] <;> omega
  high p k hp := by rcases thR_cases hp with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, g1, g2, g3⟩ <;> omega

theorem delBound_R : DelBound thR := DelBound.of_placed placed_R

theorem uB_GR_chains : GR.chains = [[tRw], [tmoW]] := rfl

theorem uB_tRw_ne_tmoW : tRw ≠ tmoW := fun e => by
  have := congrArg UScalar.val e; rw [tRw_val, tmoW_val] at this; omega

theorem uB_memGR {x : U64} (h : x ∈ GR.chains.flatten) : x = tRw ∨ x = tmoW := by
  rw [uB_GR_chains] at h; simpa using h

theorem uB_chGR {ch : List U64} (h : ch ∈ GR.chains) : ch = [tRw] ∨ ch = [tmoW] := by
  rw [uB_GR_chains] at h; simpa using h

theorem uB_noDesc {x y : U64} : ¬ Mdb.Desc GR.par y x := by
  intro h
  rcases h with h | ⟨_, h⟩ <;> simp [GR] at h

theorem uB_root_nn : capV (bsL.mem sR) tRw ≠ .Null := by
  rw [capV_R_root]; intro e; cases e

theorem uB_tmo_nn : capV (bsL.mem sR) tmoW ≠ .Null := by
  rw [capV_R_tmo]; intro e; cases e

theorem uB_null {y : U64} (hy : IsSlot thR y) (h1 : y ≠ tRw) (h2 : y ≠ tmoW) : capV (bsL.mem sR) y = .Null := by
  rcases slotR_cases hy with e | e | h
  · exact absurd e h1
  · exact absurd e h2
  · exact h.1

theorem mdbLinks_R : MdbLinks thR (bsL.mem sR) GR where
  tree := by
    refine ⟨by rw [uB_GR_chains]; simp [uB_tRw_ne_tmoW], ?_, fun _ _ h => by simp [GR] at h⟩
    intro ch _ pre x post _
    exact ⟨[], post, rfl, fun y => ⟨fun h => absurd h uB_noDesc, fun h => by cases h⟩⟩
  ne_nil ch h := by
    rcases uB_chGR h with rfl | rfl <;> exact List.cons_ne_nil _ _
  chain ch h := by
    rcases uB_chGR h with rfl | rfl <;> simp
  head ch h _ := by
    rcases uB_chGR h with rfl | rfl
    · exact prevOf_R_root
    · exact prevOf_R_tmo
  last ch h _ := by
    rcases uB_chGR h with rfl | rfl
    · exact nextOf_R_root
    · exact nextOf_R_tmo
  members a := by
    constructor
    · intro h
      rcases uB_memGR h with rfl | rfl
      · exact ⟨isSlot_R_root, _, capAt_capV _ _, uB_root_nn⟩
      · exact ⟨isSlot_R_tmo, _, capAt_capV _ _, uB_tmo_nn⟩
    · rintro ⟨hs, c, hc, hn⟩
      rw [capAt_capV] at hc
      have e := slotR_nonnull hs (by rw [ok_inj_ff hc]; exact hn)
      rw [uB_GR_chains]
      rcases e with rfl | rfl <;> simp

theorem uB_cslotI (t : U64) (i : Nat) (hi : i < tcbSlots) :
    cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex i) = slotOf t i := by
  show slotAddr t.bv (Fl4Spec.ofBl _) = _
  rw [slotAddr_ofBl, tcbCnodeIndex_blVal i hi]

theorem uB_cslot_root : cslotAddr (tRp, Fl4Spec.tcbCnodeIndex 0) = tRw := by
  rw [show tRp = tRw.bv from rfl, uB_cslotI tRw 0 (by decide)]
  exact eq_of_val'' (by rw [slotOf_val (by rw [tRw_val]; omega), tRw_val])

theorem uB_cslot_tmo : cslotAddr (tRp, Fl4Spec.tcbCnodeIndex 4) = tmoW := by
  rw [show tRp = tRw.bv from rfl, uB_cslotI tRw 4 (by decide)]
  exact eq_of_val'' (by rw [slotOf_val (by rw [tRw_val]; omega), tRw_val, tmoW_val])

theorem cdtRel_R : CdtRel thR (bsL.mem sR) (σR (Z := Unit)) GR where
  cdt _ _ := rfl
  cdt_slot _ _ h := by cases h
  orig sl hs := by
    by_cases e0 : sl = (tRp, Fl4Spec.tcbCnodeIndex 0)
    · rw [(iocR_iff sl).2 (Or.inl e0), e0, uB_cslot_root, revOf_R_root]
    by_cases e4 : sl = (tRp, Fl4Spec.tcbCnodeIndex 4)
    · rw [(iocR_iff sl).2 (Or.inr e4), e4, uB_cslot_tmo, revOf_R_tmo]
    have hf : (σR (Z := Unit)).isOriginalCap sl = false :=
      Bool.eq_false_iff.2 (fun h => ((iocR_iff sl).1 h).elim e0 e4)
    rw [hf]
    rcases slotR_cases hs.isSlot with h | h | ⟨-, -, -, h, -⟩
    · exact absurd (cslotAddr_inj placed_R hs absSlot_R_root (by rw [h, uB_cslot_root])) e0
    · exact absurd (cslotAddr_inj placed_R hs absSlot_R_tmo (by rw [h, uB_cslot_tmo])) e4
    · exact h.symm
  par_slot _ _ h := by cases h

theorem uB_gor_thr : Fl4Spec.genObjRefs (absCap (.Thread tRw)) = {Fl4Spec.GenObjRef.objRef tRw.bv} := by
  ext g
  simp [Fl4Spec.genObjRefs, absCap, Fl4Spec.objRefs, Fl4Spec.capIrqs, Fl4Spec.capIrqOpt, Fl4Spec.archCapSetMap]

theorem uB_gor_sc : Fl4Spec.genObjRefs (absCap (.SchedContext scRw 7#u64)) = {Fl4Spec.GenObjRef.objRef scRw.bv} := by
  ext g
  simp [Fl4Spec.genObjRefs, absCap, Fl4Spec.objRefs, Fl4Spec.capIrqs, Fl4Spec.capIrqOpt, Fl4Spec.archCapSetMap]

/-- The two caps of the MDB name different objects. -/
theorem uB_novl : ¬ Ovl (absCap (.Thread tRw)) (absCap (.SchedContext scRw 7#u64)) := by
  unfold Ovl
  rw [uB_gor_thr, uB_gor_sc]
  intro h
  apply h
  ext g
  constructor
  · rintro ⟨h1, h2⟩
    rw [Set.mem_singleton_iff] at h1 h2
    rw [h1] at h2
    exact absurd (Fl4Spec.GenObjRef.objRef.inj h2) tRp_ne_scRp
  · intro h'; cases h'

theorem uB_capV_GR {x : U64} (hx : x ∈ GR.chains.flatten) :
    capV (bsL.mem sR) x = .Thread tRw ∨ capV (bsL.mem sR) x = .SchedContext scRw 7#u64 := by
  rcases uB_memGR hx with rfl | rfl
  · exact Or.inl capV_R_root
  · exact Or.inr capV_R_tmo

/-- Two slots of the MDB whose caps overlap are one. -/
theorem uB_ovl_eq {x y : U64} (hx : x = tRw ∨ x = tmoW) (hy : y = tRw ∨ y = tmoW)
    (h : Ovl (absCap (capV (bsL.mem sR) x)) (absCap (capV (bsL.mem sR) y))) : x = y := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · rfl
  · rw [capV_R_root, capV_R_tmo] at h; exact absurd h uB_novl
  · rw [capV_R_tmo, capV_R_root] at h; exact absurd h.symm uB_novl
  · rfl

theorem finM_R : ∀ G, MdbLinks thR (bsL.mem sR) G → FinM (bsL.mem sR) G := by
  intro G hM
  have hm : ∀ x ∈ G.chains.flatten, x = tRw ∨ x = tmoW := fun x hx => by
    obtain ⟨hs, c, hc, hn⟩ := (hM.members x).1 hx
    rw [capAt_capV] at hc
    exact slotR_nonnull hs (by rw [ok_inj_ff hc]; exact hn)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ch1 h1 ch2 h2 x hx y hy hov
    have e := uB_ovl_eq (hm x (List.mem_flatten.2 ⟨ch1, h1, hx⟩)) (hm y (List.mem_flatten.2 ⟨ch2, h2, hy⟩)) hov
    subst e
    exact chains_same placed_R hM hM h1 h2 hx hy
  · intro x hx y hy hne hov
    exact absurd (uB_ovl_eq (hm x hx) (hm y hy) hov) hne
  · intro x hx _ _ _ hf
    rcases hm x hx with rfl | rfl
    · rw [capV_R_root] at hf; simp [isFrame] at hf
    · rw [capV_R_tmo] at hf; simp [isFrame] at hf
  · intro x hx _ _ _ hz
    rcases hm x hx with rfl | rfl
    · rw [capV_R_root] at hz; simp [isZb] at hz
    · rw [capV_R_tmo] at hz; simp [isZb] at hz

theorem delInv_R : DelInv thR (bsL.mem sR) where
  zwf y hy p zt n h := by
    rcases slotR_cases hy with rfl | rfl | ⟨hn, -⟩
    · rw [capV_R_root] at h; cases h
    · rw [capV_R_tmo] at h; cases h
    · rw [hn] at h; cases h
  zu y y' hy _ _ p zt n p' zt' n' h := by
    rcases slotR_cases hy with rfl | rfl | ⟨hn, -⟩
    · rw [capV_R_root] at h; cases h
    · rw [capV_R_tmo] at h; cases h
    · rw [hn] at h; cases h
  nc y hy hnull := by
    rcases slotR_cases hy with rfl | rfl | ⟨-, h1, h2, -⟩
    · exact absurd hnull uB_root_nn
    · exact absurd hnull uB_tmo_nn
    · exact ⟨h1, h2⟩

theorem uB_sizeF_thread (q : U64) : sizeF (.Thread q) = fl4_abi.consts.bits.TCB := ok_inj (size_eq _).symm
theorem uB_sizeF_sc (q b : U64) : sizeF (.SchedContext q b) = b := ok_inj (size_eq _).symm
theorem uB_ptrF_sc (q b : U64) : ptrF (.SchedContext q b) = q := ok_inj (ptr_eq _).symm
theorem uB_physF_sc (q b : U64) : physF (.SchedContext q b) = true := ok_inj (phys_eq _).symm

/-- The root thread cap's last byte. -/
theorem uB_topF_R : topF (.Thread tRw) = 18446744071562076160 + 4095 := by
  unfold topF
  rw [ptrF_thread, uB_sizeF_thread]
  have hm : (maskF fl4_abi.consts.bits.TCB).val = 4095 := by
    have hT : fl4_abi.consts.bits.TCB.val = 12 := by simp [fl4_abi.consts.bits.TCB]
    rw [maskF_val (b := fl4_abi.consts.bits.TCB) (by rw [hT]; decide), hT] <;> rfl
  simp only [core.num.U64.wrapping_add_val_eq, hm, tRw_val]; simp [U64.size, U64.numBits]

/-- The root SC cap's last byte. -/
theorem uB_topF_sc : topF (.SchedContext scRw 7#u64) = 18446744071562080256 + 127 := by
  unfold topF
  rw [uB_ptrF_sc, uB_sizeF_sc]
  have hm : (maskF 7#u64).val = 127 := by
    have h7 : (7#u64 : U64).val = 7 := by simp
    rw [maskF_val (b := 7#u64) (by rw [h7]; decide), h7] <;> rfl
  simp only [core.num.U64.wrapping_add_val_eq, hm, scRw_val]; simp [U64.size, U64.numBits]

theorem uB_notUt {x p sb fi : U64} {d : Bool} (hx : x ∈ GR.chains.flatten)
    (h : capV (bsL.mem sR) x = .Untyped p sb fi d) : False := by
  rcases uB_capV_GR hx with e | e <;> rw [e] at h <;> cases h

theorem utInv_R : UtInv (bsL.mem sR) GR where
  reg x hx _ := by
    rcases uB_capV_GR hx with e | e <;> rw [e] <;> unfold baseF
    · rw [ptrF_thread, uB_topF_R]; have := tRw_val; omega
    · rw [uB_ptrF_sc, uB_topF_sc]; have := scRw_val; omega
  inc x hx p sb fi d h := (uB_notUt hx h).elim
  noov x hx p sb fi d h := (uB_notUt hx h).elim
  excl x hx y hy hne p sb fi fi' d d' h := (uB_notUt hx h).elim
  fib x hx p sb fi d h := (uB_notUt hx h).elim
  drange x hx p sb fi d h := (uB_notUt hx h).elim

theorem sfree_R : SpecFree (bsL.mem sR) GR (σR (Z := Unit)) := by
  intro x hx p sb fi h
  exact (uB_notUt hx h).elim

theorem utc_R : ∀ sl p sb fi dev, AbsSlot thR sl → capAt (bsL.mem sR) (cslotAddr sl) = ok (.Untyped p sb fi dev) →
    dev = false → Sched.UtCapP3 (L := bsL) LocPlatM.archT thR sR (σR (Z := Unit)) GR sl p sb fi := by
  intro sl p sb fi dev hs hc _
  rw [capAt_capV] at hc
  rcases slotR_cases hs.isSlot with e | e | ⟨hn, -⟩
  · rw [e, capV_R_root] at hc; cases ok_inj_ff hc
  · rw [e, capV_R_tmo] at hc; cases ok_inj_ff hc
  · rw [hn] at hc; cases ok_inj_ff hc

theorem zD_R : ∀ p ∈ ZTcb (L := bsL) thR sR, p ∈ DB := by
  rintro p ⟨y, hy, zt, n, h, -⟩
  rcases slotR_cases hy with rfl | rfl | ⟨hn, -⟩
  · rw [capV_R_root] at h; cases h
  · rw [capV_R_tmo] at h; cases h
  · rw [hn] at h; cases h

theorem uB_idleScW : idleScW (L := bsL) sR = sciB := by
  unfold idleScW
  rw [sR_cpu]
  have h0 : layout.node.IDLE_SC.val = 32 := by simp [layout.node.IDLE_SC]
  rw [memR_mem (nodeR_aligned (by omega) (by omega)), sR_nodeAt_val (by omega), h0]
  rw [wordR_of (by omega)]
  simp [wordB]

/-- An object of the kernel-state block is a `KsObj` (`thR`, `HR`). -/
theorem uB_ksObj {q : U64} (h1 : 18446744071562100736 ≤ q.val) (h2 : q.val < 18446744071562100736 + 13568) :
    KsObj (L := bsL) thR HR sR q := by
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩ <;> unfold KsIn <;> rw [sR_ksb, kbB_val]
  · rcases thR_cases hk with ⟨e, -⟩ | ⟨e, -⟩ | ⟨rfl, g1, g2, g3⟩
    · omega
    · omega
    · simp only [P3.objSize, Nat.pow_zero]; omega
  · rcases HR_cases hk with ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨rfl, g1, g2, g3⟩ | ⟨rfl, g1, g2, g3, -⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · simp only [HKind.bits, Nat.reducePow]; omega
    · simp only [HKind.bits, Nat.reducePow]; omega

theorem uB_tRw_mem : tRw ∈ GR.chains.flatten := by rw [uB_GR_chains]; simp
theorem uB_tmoW_mem : tmoW ∈ GR.chains.flatten := by rw [uB_GR_chains]; simp

/-- The thread cap covers the root TCB's 4096 bytes. -/
theorem uB_cov_tR {q : U64} (e : q.val = 18446744071562076160) {n : Nat} (hn : n ≤ 4096) :
    Covered (bsL.mem sR) GR q.val (q.val + n) := by
  refine ⟨tRw, uB_tRw_mem, ?_, ?_, ?_, ?_⟩ <;> rw [capV_R_root]
  · exact physF_thread _
  · rfl
  · unfold baseF; rw [ptrF_thread]; have := tRw_val; omega
  · rw [uB_topF_R]; omega

/-- The SC cap covers the root SC's 128 bytes. -/
theorem uB_cov_scR {q : U64} (e : q.val = 18446744071562080256) {n : Nat} (hn : n ≤ 128) :
    Covered (bsL.mem sR) GR q.val (q.val + n) := by
  refine ⟨tmoW, uB_tmoW_mem, ?_, ?_, ?_, ?_⟩ <;> rw [capV_R_tmo]
  · exact uB_physF_sc _ _
  · rfl
  · unfold baseF; rw [uB_ptrF_sc]; have := scRw_val; omega
  · rw [uB_topF_sc]; omega

theorem jcov_R : JCovD (L := bsL) thR HR GR DB CsB sR where
  th q k hq := by
    rcases thR_cases hq with ⟨e, rfl⟩ | ⟨e, -⟩ | ⟨-, g1, g2, -⟩
    · left; exact uB_cov_tR e (by simp [P3.objSize])
    · right; right; left; left
      rw [sR_idleW]; exact eq_of_val'' (by rw [e, tiB_val])
    · right; right; right; exact uB_ksObj (by omega) (by omega)
  h q k hq := by
    rcases HR_cases hq with ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, g1, g2, -⟩ | ⟨-, g1, g2, -⟩
    · left; exact uB_cov_tR e (by simp [HKind.bits])
    · left; exact uB_cov_scR e (by simp [HKind.bits])
    · right; right; left; left
      rw [sR_idleW]; exact eq_of_val'' (by rw [e, tiB_val])
    · right; right; left; right
      rw [uB_idleScW]; exact eq_of_val'' (by rw [e, sciB_val])
    · right; left; exact e
    · right; right; right; exact uB_ksObj (by omega) (by omega)
    · right; right; right; exact uB_ksObj (by omega) (by omega)
  dead q hq := by
    have hq' : q.val = 18446744071562084352 ∨ q.val = 18446744071562088448 ∨ q.val = 18446744071562092544 := hq
    have hH : HR q = some (.other 12) := by
      unfold HR HB
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos hq']
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun z h => ?_⟩ <;> rw [hH] at h <;> cases h
  ks x hx p sb fi h := (uB_notUt hx h).elim
  idleOut x hx p sb fi h := (uB_notUt hx h).elim
  dx q hq h := by
    have hq' : q.val = 18446744071562084352 ∨ q.val = 18446744071562088448 ∨ q.val = 18446744071562092544 := hq
    rcases HR_cases h with ⟨e, -⟩ | ⟨-, e⟩ | ⟨e, -⟩ | ⟨-, e⟩ | ⟨-, e⟩ | ⟨e, -⟩ | ⟨e, -⟩
    · omega
    · cases e
    · omega
    all_goals cases e

end

end Fl4Proofs.P2.BootSt
