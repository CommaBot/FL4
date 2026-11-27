/-
# P2 (line p3mc, gen 39, unit D): `XTopAt.rel` (`RelTopB`) at the second boot start

At `(sR, σR)` with the ghosts `ZR` (MDB ghost `GR` = two one-slot chains `[tRw]`, `[tmoW]`, no parent), every part of P3's `RelTopB`,
gen 35's `P2/BootRelF` ported:

* `Placed thR` (`uD_placed`);
* `CRel`: `uD_stateRel` (`StateRel`: the IRQ CNodes as at `σB`; the idle TCB's six null slots; the root TCB's slot 0
  `Thread tRw` related to `threadCap tRp`, slot 4 `SchedContext scRw 7` to `schedContextCap scRp 0`, its other
  four slots null), `uD_slotsValid`, **`uD_mdbLinks`** (`MdbLinks` at `GR`: two one-slot chains, links 0),
  **`uD_cdtRel`** (`CdtRel`: `cdt` empty, the original slots exactly the two revocable ones, `cslotAddr_inj`),
  `uD_mdbInv`;
* `FinInv`: `uD_kTyped` (`KTyped thR σR`), `uD_finM` (the thread cap and the SC cap name different objects);
* `uD_domRel` (`DomRel`: `σB`'s domain table words, untouched by `wordR`);
* `uD_mdbOKV` (`MdbOKV` at `GR`: neither cap is a frame / untyped / VSpace cap; their ranges `[tRw, tRw + 4096)`
  and `[scRw, scRw + 128)` do not wrap and are disjoint);
* `uD_ipcApart` (both TCBs' IPC words `[t + 256, t + 4096)` miss every slot), `uD_scApart` (both SCs' 128 bytes);
* **`relTopB_R`**: all of `RelTopB thR GR ∅ {tiB, tRw} {sciB, scRw} ∅ ∅ ∅ 0 sR σR`.

No premise. No existing statement changed.
-/
import Fl4Proofs.P2.BootRWordF
import Fl4Proofs.P2.BootRelF
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.BootSt
open fl4_core Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P1 Classical

noncomputable section

/-! ## Placement and slots -/

theorem uD_placed : Placed thR where
  align p k hp := by rcases thR_cases hp with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, g1, g2, g3⟩ <;> omega
  fits p k hp := by
    rcases thR_cases hp with ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨rfl, g1, g2, g3⟩ <;>
      simp only [P3.objSize, Nat.pow_zero] <;> omega
  disj p q kp kq hp hq hne := by
    have hv := U64.ne_of_val hne
    rcases thR_cases hp with ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨rfl, g1, g2, g3⟩ <;>
      rcases thR_cases hq with ⟨f, rfl⟩ | ⟨f, rfl⟩ | ⟨rfl, f1, f2, f3⟩ <;>
      simp only [P3.objSize, Nat.pow_zero] <;> omega
  high p k hp := by rcases thR_cases hp with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, g1, g2, g3⟩ <;> omega

/-- A slot of `thR`: aligned, its 32 bytes in a TCB's slot area or the IRQ node. -/
theorem uD_slot_range {y : U64} (hy : IsSlot thR y) : y.val % 32 = 0 ∧
    ((18446744071562072064 ≤ y.val ∧ y.val + 32 ≤ 18446744071562072064 + 192) ∨
      (18446744071562076160 ≤ y.val ∧ y.val + 32 ≤ 18446744071562076160 + 192) ∨
      (18446744071562100736 + 1248 ≤ y.val ∧ y.val + 32 ≤ 18446744071562100736 + 5344)) := by
  obtain ⟨p, i, hi, rfl⟩ := hy
  rcases hi with ⟨r, hp, hir⟩ | ⟨hp, hit⟩
  · rcases thR_cases hp with ⟨-, e⟩ | ⟨-, e⟩ | ⟨e, g1, g2, g3⟩
    · cases e
    · cases e
    · cases e
      simp only [Nat.pow_zero] at hir
      rw [slotOf_val (by omega)]
      exact ⟨by omega, Or.inr (Or.inr ⟨by omega, by omega⟩)⟩
  · rcases thR_cases hp with ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩
    · simp only [tcbSlots] at hit
      rw [slotOf_val (by omega)]
      exact ⟨by omega, Or.inr (Or.inl ⟨by omega, by omega⟩)⟩
    · simp only [tcbSlots] at hit
      rw [slotOf_val (by omega)]
      exact ⟨by omega, Or.inl ⟨by omega, by omega⟩⟩
    · cases e

/-- A slot of `thR` other than the root and timeout-handler slots holds the null cap. -/
theorem uD_capAt_ne {y : U64} (hy : IsSlot thR y) (hn : y.val ≠ 18446744071562076160)
    (hn4 : y.val ≠ 18446744071562076288) : capAt (bsL.mem sR) y = ok .Null := by
  rcases slotR_cases hy with e | e | ⟨h, -⟩
  · exact absurd (show y.val = 18446744071562076160 by rw [e, tRw_val]) hn
  · exact absurd (show y.val = 18446744071562076288 by rw [e, tmoW_val]) hn4
  · rw [capAt_capV, h]

theorem uD_root_slot : slotOf tRw 0 = tRw :=
  eq_of_val'' (by rw [slotOf_val (by rw [tRw_val]; omega), tRw_val])

theorem uD_tmo_slot : slotOf tRw 4 = tmoW :=
  eq_of_val'' (by rw [slotOf_val (by rw [tRw_val]; omega), tRw_val, tmoW_val])

theorem uD_tR_ne_tmo : tRw ≠ tmoW := fun e => by
  have := congrArg UScalar.val e; rw [tRw_val, tmoW_val] at this; omega

theorem uD_seven : (7#u64 : U64).val = 7 := rfl

/-- The root TCB's slots 1, 2, 3, 5: null caps. -/
theorem uD_tcbR_map {i : Nat} (hi : i < 6) (h0 : i ≠ 0) (h4 : i ≠ 4) :
    Fl4Spec.tcbCnodeMap tcbR (Fl4Spec.tcbCnodeIndex i) = some .nullCap := by
  interval_cases i
  · exact absurd rfl h0
  · simp only [Fl4Spec.tcbCnodeMap, Function.update_apply]
    repeat (first | rw [if_neg (by decide)] | rw [if_pos rfl])
    all_goals rfl
  · simp only [Fl4Spec.tcbCnodeMap, Function.update_apply]
    repeat (first | rw [if_neg (by decide)] | rw [if_pos rfl])
    all_goals rfl
  · simp only [Fl4Spec.tcbCnodeMap, Function.update_apply]
    repeat (first | rw [if_neg (by decide)] | rw [if_pos rfl])
    all_goals rfl
  · exact absurd rfl h4
  · simp only [Fl4Spec.tcbCnodeMap, Function.update_apply]
    repeat (first | rw [if_neg (by decide)] | rw [if_pos rfl])
    all_goals rfl

/-- The SC cap of the timeout-handler slot is related to the spec's `schedContextCap scRp 0`. -/
theorem uD_capRel_sc : CapRel (.SchedContext scRw 7#u64) (.schedContextCap scRp 0) := by
  refine ⟨show Fl4Spec.minSchedContextBits ≤ (7#u64 : U64).val by
    rw [uD_seven]; simp [Fl4Spec.minSchedContextBits], ?_⟩
  show Fl4Spec.Cap.schedContextCap scRp ((7#u64 : U64).val - Fl4Spec.minSchedContextBits) = _
  rw [uD_seven]; simp [Fl4Spec.minSchedContextBits]

/-! ## `CRel` -/

theorem uD_stateRel : StateRel thR (bsL.mem sR) (σR (Z := Unit)) where
  cnode p r hp := by
    rcases thR_cases hp with ⟨-, e⟩ | ⟨-, e⟩ | ⟨e, g1, g2, g3⟩
    · cases e
    · cases e
    · cases e
      have hne1 : p.bv ≠ tRp := fun h => by
        have h' := congrArg BitVec.toNat h
        rw [tRp_toNat] at h'
        change p.val = _ at h'
        omega
      have hne2 : p.bv ≠ scRp := fun h => by
        have h' := congrArg BitVec.toNat h
        rw [scRp_toNat] at h'
        change p.val = _ at h'
        omega
      refine ⟨Fl4Spec.emptyCnode 0, ?_, ?_, ?_⟩
      · show kheapR p.bv = _
        rw [kheapR_of_ne hne1 hne2]
        exact kheapB_irqObj (by omega) g2 g3
      · unfold Fl4Spec.wellFormedCnodeN Fl4Spec.emptyCnode Fl4Spec.dom; ext x; simp
      · intro idx hl
        have hidx : idx = [] := List.length_eq_zero_iff.1 hl
        subst hidx
        refine ⟨.Null, .nullCap, ?_, ?_, ⟨trivial, rfl⟩⟩
        · rw [slotAddr_ofBl]
          have hb : blVal 0 ([] : List Bool) = 0 := by simp [blVal]
          rw [hb]
          refine uD_capAt_ne ⟨p, 0, Or.inl ⟨0, hp, by norm_num⟩, rfl⟩ ?_ ?_
          · rw [slotOf_val (by omega)]; omega
          · rw [slotOf_val (by omega)]; omega
        · simp [Fl4Spec.emptyCnode]
  tcb t ht := by
    rcases thR_cases ht with ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩
    · have : t = tRw := eq_of_val'' (by rw [e, tRw_val])
      subst this
      refine ⟨tcbR, uD_σR_tR, fun i hi => ?_⟩
      have hi6 : i < 6 := hi
      by_cases h0 : i = 0
      · subst h0
        refine ⟨.Thread tRw, .threadCap tRp, ?_, tcbR_root, ⟨trivial, rfl⟩⟩
        show capAt _ (slotOf tRw 0) = _
        rw [uD_root_slot, capAt_capV, capV_R_root]
      by_cases h4 : i = 4
      · subst h4
        refine ⟨.SchedContext scRw 7#u64, .schedContextCap scRp 0, ?_, tcbR_tmo, uD_capRel_sc⟩
        show capAt _ (slotOf tRw 4) = _
        rw [uD_tmo_slot, capAt_capV, capV_R_tmo]
      · have hv : (slotOf tRw i).val = 18446744071562076160 + 32 * i := by
          rw [slotOf_val (by rw [tRw_val]; omega), tRw_val]
        refine ⟨.Null, .nullCap, uD_capAt_ne ⟨tRw, i, Or.inr ⟨thR_tR, hi⟩, rfl⟩ ?_ ?_,
          uD_tcbR_map hi6 h0 h4, ⟨trivial, rfl⟩⟩
        · rw [hv]; omega
        · rw [hv]; omega
    · have : t = tiB := eq_of_val' (by rw [e, tiB_val])
      subst this
      refine ⟨idleTcbB, uD_σR_ti, fun i hi => ?_⟩
      have hi6 : i < 6 := hi
      have hv : (slotOf tiB i).val = 18446744071562072064 + 32 * i := by
        rw [slotOf_val (by rw [tiB_val]; omega), tiB_val]
      refine ⟨.Null, .nullCap, uD_capAt_ne ⟨tiB, i, Or.inr ⟨thR_ti, hi⟩, rfl⟩ ?_ ?_, idleMap hi6,
        ⟨trivial, rfl⟩⟩
      · rw [hv]; omega
      · rw [hv]; omega
    · cases e

theorem uD_capValid {y : U64} (hy : IsSlot thR y) {c : capability.Cap} (hc : capAt (bsL.mem sR) y = ok c) :
    CapValid thR c := by
  rcases slotR_cases hy with rfl | rfl | ⟨hn, -⟩
  · rw [capAt_capV, capV_R_root] at hc
    cases ok_inj_ff hc
    exact thR_tR
  · rw [capAt_capV, capV_R_tmo] at hc
    cases ok_inj_ff hc
    show scRw ≠ 0#u64
    intro e; have := congrArg UScalar.val e; rw [scRw_val] at this; exact absurd this (by decide)
  · rw [capAt_capV, hn] at hc
    cases ok_inj_ff hc
    trivial

theorem uD_slotsValid : SlotsValid thR (bsL.mem sR) where
  cnode p r hp i hi c hc := uD_capValid ⟨p, i, Or.inl ⟨r, hp, hi⟩, rfl⟩ hc
  tcb t ht i hi c hc := uD_capValid ⟨t, i, Or.inr ⟨ht, hi⟩, rfl⟩ hc

theorem uD_flat : GR.chains.flatten = [tRw, tmoW] := rfl

theorem uD_mem_flat {x : U64} (h : x ∈ GR.chains.flatten) : x = tRw ∨ x = tmoW := by
  rw [uD_flat] at h; simpa using h

theorem uD_mem_chains {ch : List U64} (h : ch ∈ GR.chains) : ch = [tRw] ∨ ch = [tmoW] := by
  have h' : ch ∈ [[tRw], [tmoW]] := h
  simpa using h'

/-- The two caps of the MDB. -/
theorem uD_capV_flat {x : U64} (h : x ∈ GR.chains.flatten) :
    capV (bsL.mem sR) x = .Thread tRw ∨ capV (bsL.mem sR) x = .SchedContext scRw 7#u64 := by
  rcases uD_mem_flat h with rfl | rfl
  · exact Or.inl capV_R_root
  · exact Or.inr capV_R_tmo

theorem uD_desc {y x : U64} (h : Mdb.Desc GR.par y x) : False := by
  cases h with
  | single h => simp [GR] at h
  | tail _ h => simp [GR] at h

theorem uD_mdbLinks : MdbLinks thR (bsL.mem sR) GR where
  tree := ⟨by rw [uD_flat]; exact List.nodup_cons.2 ⟨by simp [uD_tR_ne_tmo], List.nodup_singleton _⟩,
    fun ch _ pre x post _ => ⟨[], post, rfl, fun y => ⟨fun h => (uD_desc h).elim, fun h => by cases h⟩⟩,
    fun a b h => by simp [GR] at h⟩
  ne_nil ch h := by rcases uD_mem_chains h with rfl | rfl <;> simp
  chain ch h := by rcases uD_mem_chains h with rfl | rfl <;> simp
  head ch h hne := by
    rcases uD_mem_chains h with rfl | rfl
    · exact prevOf_R_root
    · exact prevOf_R_tmo
  last ch h hne := by
    rcases uD_mem_chains h with rfl | rfl
    · exact nextOf_R_root
    · exact nextOf_R_tmo
  members a := by
    constructor
    · intro h
      rcases uD_mem_flat h with rfl | rfl
      · exact ⟨isSlot_R_root, _, by rw [capAt_capV, capV_R_root], by intro h; cases h⟩
      · exact ⟨isSlot_R_tmo, _, by rw [capAt_capV, capV_R_tmo], by intro h; cases h⟩
    · rintro ⟨hs, c, hc, hn⟩
      rw [uD_flat]
      rcases slotR_nonnull hs (by intro h; rw [capAt_capV, h] at hc; exact hn (ok_inj_ff hc).symm) with e | e
      · rw [e]; simp
      · rw [e]; simp

/-- The root slot's spec address. -/
theorem uD_root_cslot : cslotAddr (tRp, Fl4Spec.tcbCnodeIndex 0) = tRw := by
  apply UScalar.eq_of_val_eq
  show (tRp + Fl4Spec.ofBl (Fl4Spec.tcbCnodeIndex 0) * 32#64).toNat =
    (BitVec.ofNat 64 18446744071562076160).toNat
  decide

/-- The timeout-handler slot's spec address. -/
theorem uD_tmo_cslot : cslotAddr (tRp, Fl4Spec.tcbCnodeIndex 4) = tmoW := by
  apply UScalar.eq_of_val_eq
  show (tRp + Fl4Spec.ofBl (Fl4Spec.tcbCnodeIndex 4) * 32#64).toNat =
    (BitVec.ofNat 64 18446744071562076288).toNat
  decide

theorem uD_cdtRel : CdtRel thR (bsL.mem sR) (σR (Z := Unit)) GR where
  cdt _ _ := rfl
  cdt_slot _ _ h := by cases h
  orig sl hs := by
    by_cases e0 : sl = (tRp, Fl4Spec.tcbCnodeIndex 0)
    · subst e0
      rw [(iocR_iff _).2 (Or.inl rfl), uD_root_cslot, revOf_R_root]
    by_cases e4 : sl = (tRp, Fl4Spec.tcbCnodeIndex 4)
    · subst e4
      rw [(iocR_iff _).2 (Or.inr rfl), uD_tmo_cslot, revOf_R_tmo]
    · have h1 : (σR (Z := Unit)).isOriginalCap sl = false := by
        cases h : (σR (Z := Unit)).isOriginalCap sl
        · rfl
        · exact absurd ((iocR_iff sl).1 h) (fun h' => h'.elim e0 e4)
      rw [h1]
      rcases slotR_cases hs.isSlot with h2 | h2 | ⟨-, -, -, h2, -⟩
      · exact absurd (cslotAddr_inj uD_placed hs absSlot_R_root (by rw [h2, uD_root_cslot])) e0
      · exact absurd (cslotAddr_inj uD_placed hs absSlot_R_tmo (by rw [h2, uD_tmo_cslot])) e4
      · exact h2.symm
  par_slot _ _ h := by cases h

theorem uD_srSelf : srM (bsL.mem sR) tRw tRw = true := by
  unfold srM; rw [capV_R_root]; exact srB_of_eq (by simp [objects.same_region_as])

theorem uD_srSelf_tmo : srM (bsL.mem sR) tmoW tmoW = true := by
  unfold srM; rw [capV_R_tmo]; exact srB_of_eq (by simp [objects.same_region_as])

theorem uD_nextOf_flat {y : U64} (hy : y ∈ GR.chains.flatten) : nextOf (bsL.mem sR) y = 0#u64 := by
  rcases uD_mem_flat hy with rfl | rfl
  · exact nextOf_R_root
  · exact nextOf_R_tmo

theorem uD_mdbInv : MdbInv (bsL.mem sR) GR where
  orig c p h := by simp [GR] at h
  desc x y h := (uD_desc h).elim
  after y hy hn := absurd (uD_nextOf_flat hy) hn
  chunk ch h := by rcases uD_mem_chains h with rfl | rfl <;> exact ⟨trivial, trivial⟩
  badges y hy hn := absurd (uD_nextOf_flat hy) hn
  utrev x hx h := by rcases uD_capV_flat hx with e | e <;> rw [e] at h <;> simp [isUt] at h
  self x hx _ := by
    rcases uD_mem_flat hx with rfl | rfl
    · exact uD_srSelf
    · exact uD_srSelf_tmo

theorem uD_crel : CRel thR (bsL.mem sR) (σR (Z := Unit)) GR :=
  ⟨uD_stateRel, uD_slotsValid, uD_mdbLinks, uD_cdtRel, uD_mdbInv⟩

/-! ## `FinInv` -/

theorem uD_thR_of_thB {o : BitVec 64} (h : o ≠ tRp) : thR ⟨o⟩ = thB ⟨o⟩ := by
  unfold thR
  rw [if_neg]
  intro e
  apply h
  apply BitVec.eq_of_toNat_eq
  rw [tRp_toNat]
  exact e

theorem uD_kTyped : KTyped thR (σR (Z := Unit)) := by
  intro o
  refine ⟨fun r cs h hw => ?_, fun t h => ?_⟩
  · rcases kheapR_cases h with ⟨-, e⟩ | ⟨-, e⟩ | ⟨e1, -, hb⟩
    · cases e
    · cases e
    · rw [uD_thR_of_thB e1]; exact (kTyped_B o).1 r cs hb hw
  · rcases kheapR_cases h with ⟨e, -⟩ | ⟨-, e⟩ | ⟨e1, -, hb⟩
    · subst e; exact thR_tR
    · cases e
    · rw [uD_thR_of_thB e1]; exact (kTyped_B o).2 t hb

theorem uD_gen_thread (p : U64) :
    Fl4Spec.genObjRefs (absCap (.Thread p)) = {Fl4Spec.GenObjRef.objRef p.bv} := by
  ext g
  simp [Fl4Spec.genObjRefs, absCap, Fl4Spec.objRefs, Fl4Spec.capIrqs, Fl4Spec.capIrqOpt, Fl4Spec.archCapSetMap]

theorem uD_gen_sc (p sb : U64) :
    Fl4Spec.genObjRefs (absCap (.SchedContext p sb)) = {Fl4Spec.GenObjRef.objRef p.bv} := by
  ext g
  simp [Fl4Spec.genObjRefs, absCap, Fl4Spec.objRefs, Fl4Spec.capIrqs, Fl4Spec.capIrqOpt, Fl4Spec.archCapSetMap]

/-- The thread cap and the SC cap name different objects. -/
theorem uD_not_ovl : ¬ Ovl (absCap (.Thread tRw)) (absCap (.SchedContext scRw 7#u64)) := by
  unfold Ovl
  rw [uD_gen_thread, uD_gen_sc]
  intro h
  apply h
  rw [Set.singleton_inter_eq_empty]
  intro e
  rw [Set.mem_singleton_iff] at e
  exact absurd (Fl4Spec.GenObjRef.objRef.inj e) (by decide)

theorem uD_finM : FinM (bsL.mem sR) GR where
  conn ch1 h1 ch2 h2 x hx y hy hov := by
    rcases uD_mem_chains h1 with rfl | rfl <;> rcases uD_mem_chains h2 with rfl | rfl
    · rfl
    · rw [List.mem_singleton.1 hx, List.mem_singleton.1 hy, capV_R_root, capV_R_tmo] at hov
      exact absurd hov uD_not_ovl
    · rw [List.mem_singleton.1 hx, List.mem_singleton.1 hy, capV_R_root, capV_R_tmo] at hov
      exact absurd hov.symm uD_not_ovl
    · rfl
  key x hx y hy hne hov _ _ _ := by
    rcases uD_mem_flat hx with rfl | rfl <;> rcases uD_mem_flat hy with rfl | rfl
    · exact absurd rfl hne
    · rw [capV_R_root, capV_R_tmo] at hov; exact absurd hov uD_not_ovl
    · rw [capV_R_root, capV_R_tmo] at hov; exact absurd hov.symm uD_not_ovl
    · exact absurd rfl hne
  fnest x hx y hy hne hf _ _ := by
    rcases uD_capV_flat hx with e | e <;> rw [e] at hf <;> simp [isFrame] at hf
  zfin x hx y hy hne hz := by
    rcases uD_capV_flat hx with e | e <;> rw [e] at hz <;> simp [isZb] at hz

theorem uD_finInv : FinInv thR (bsL.mem sR) (σR (Z := Unit)) GR := ⟨uD_kTyped, uD_finM⟩

/-! ## The domain schedule -/

theorem uD_domRel : DomRel (bsL.mem sR) (bsL.ksb sR) (σR (Z := Unit)) := by
  rw [sR_ksb]
  refine ⟨rfl, fun i hi => ?_, ?_, ?_⟩
  · have hev := ksWB_val (entOff_val hi) (by omega)
    have hdv := ksWB_val (durOff_val hi) (by omega)
    rw [memR_at hev (by omega), memR_at hdv (by omega), wordR_of (by omega), wordR_of (by omega)]
    rcases (by omega : i.val = 0 ∨ i.val = 1) with h0 | h0 <;> rw [h0]
    · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [wordB, σR, σB] <;> first | rfl | decide
    · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [wordB, σR, σB] <;> first | rfl | decide
  · rw [memR_at (ksWB_val (o := 32#u64) (n := 32) (by decide) (by omega)) (by omega), wordR_zero_of (by omega)]; rfl
  · rw [memR_at (ksWB_val (o := 24#u64) (n := 24) (by decide) (by omega)) (by omega), wordR_zero_of (by omega)]

/-! ## The MDB invariants -/

theorem uD_sizeF_thread (q : U64) : sizeF (.Thread q) = fl4_abi.consts.bits.TCB := ok_inj (size_eq _).symm

theorem uD_sizeF_sc (q sb : U64) : sizeF (.SchedContext q sb) = sb := ok_inj (size_eq _).symm

theorem uD_ptrF_sc (q sb : U64) : ptrF (.SchedContext q sb) = q := ok_inj (ptr_eq _).symm

theorem uD_tcbBits : (fl4_abi.consts.bits.TCB).val = 12 := by simp [fl4_abi.consts.bits.TCB]

theorem uD_base_thread : baseF (capability.Cap.Thread tRw) = 18446744071562076160 := by
  unfold baseF; rw [ptrF_thread, tRw_val]

theorem uD_top_thread : topF (capability.Cap.Thread tRw) = 18446744071562076160 + 4095 := by
  unfold topF
  rw [ptrF_thread, uD_sizeF_thread]
  have hm : (maskF fl4_abi.consts.bits.TCB).val = 2 ^ 12 - 1 := by
    rw [maskF_val (by rw [uD_tcbBits]; omega), uD_tcbBits]
  simp only [core.num.U64.wrapping_add_val_eq, hm, tRw_val]
  (try simp [U64.size, U64.numBits]) <;> omega

theorem uD_base_sc : baseF (capability.Cap.SchedContext scRw 7#u64) = 18446744071562080256 := by
  unfold baseF; rw [uD_ptrF_sc, scRw_val]

theorem uD_top_sc : topF (capability.Cap.SchedContext scRw 7#u64) = 18446744071562080256 + 127 := by
  unfold topF
  rw [uD_ptrF_sc, uD_sizeF_sc]
  have hm : (maskF 7#u64).val = 2 ^ 7 - 1 := by
    rw [maskF_val (by rw [uD_seven]; omega), uD_seven]
  simp only [core.num.U64.wrapping_add_val_eq, hm, scRw_val]
  (try simp [U64.size, U64.numBits]) <;> omega

/-- The thread cap's range `[tRw, tRw + 4095]` does not wrap. -/
theorem uD_reg : baseF (capability.Cap.Thread tRw) ≤ topF (.Thread tRw) := by
  rw [uD_base_thread, uD_top_thread]; omega

/-- The SC cap's range `[scRw, scRw + 127]` does not wrap. -/
theorem uD_reg_sc : baseF (capability.Cap.SchedContext scRw 7#u64) ≤ topF (.SchedContext scRw 7#u64) := by
  rw [uD_base_sc, uD_top_sc]; omega

theorem uD_frameInv : Vs.FrameInv (bsL.mem sR) GR := by
  intro x hx p r m ep a va h
  rcases uD_capV_flat hx with e | e <;> rw [e] at h <;> cases h

theorem uD_utInv : UtInv (bsL.mem sR) GR where
  reg x hx _ := by
    rcases uD_capV_flat hx with e | e <;> rw [e]
    · exact uD_reg
    · exact uD_reg_sc
  inc x hx p sb fi d h := by rcases uD_capV_flat hx with e | e <;> rw [e] at h <;> cases h
  noov x hx p sb fi d h := by rcases uD_capV_flat hx with e | e <;> rw [e] at h <;> cases h
  excl x hx y hy hne p sb fi fi' d d' h := by rcases uD_capV_flat hx with e | e <;> rw [e] at h <;> cases h
  fib x hx p sb fi d h := by rcases uD_capV_flat hx with e | e <;> rw [e] at h <;> cases h
  drange x hx p sb fi d h := by rcases uD_capV_flat hx with e | e <;> rw [e] at h <;> cases h

theorem uD_noOv : NoOverlap (bsL.mem sR) GR := by
  intro x hx y hy _ _ _
  rcases uD_mem_flat hx with rfl | rfl <;> rcases uD_mem_flat hy with rfl | rfl
  · rw [capV_R_root]; exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl⟩))
  · left; rw [capV_R_root, capV_R_tmo]; unfold Disj
    rw [uD_base_thread, uD_top_thread, uD_base_sc, uD_top_sc]; omega
  · left; rw [capV_R_root, capV_R_tmo]; unfold Disj
    rw [uD_base_thread, uD_top_thread, uD_base_sc, uD_top_sc]; omega
  · rw [capV_R_tmo]; exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl⟩))

theorem uD_utWin : UtWin (bsL.mem sR) GR := by
  intro x hx; rcases uD_capV_flat hx with e | e <;> rw [e] <;> trivial

theorem uD_vsMdb : Vs.VsMdbInv kbB (bsL.mem sR) GR :=
  ⟨⟨∅, ∅, ∅, ∅, ∅, fun x hx => by rcases uD_capV_flat hx with e | e <;> rw [e] <;> trivial⟩,
    fun x hx p sb fi h => by rcases uD_capV_flat hx with e | e <;> rw [e] at h <;> cases h⟩

theorem uD_mdbOKV : MdbOKV (bsL.ksb sR) (bsL.mem sR) GR :=
  ⟨⟨uD_frameInv, uD_utInv, uD_noOv⟩, uD_utWin, uD_vsMdb⟩

/-! ## The IPC words and the SCs apart from the slots -/

theorem uD_ipcApart : Ipc.IpcApart ZR.th ZR.N ZR.T ZR.E ZR.R ZR.B (bsL.ksb sR) ZR.c := by
  show Ipc.IpcApart thR ∅ {tiB, tRw} ∅ ∅ ∅ kbB 0#u64
  have h00 : (0#u64 : U64).val = 0 := rfl
  refine ⟨fun a ha x hx ⟨h1, h2⟩ => ?_, fun a h1 h2 x hx ⟨h3, h4⟩ => ?_, fun a ha => ?_,
    fun a h1 h2 h0 x hx ⟨h3, h4⟩ => ?_, by rw [kbB_val]; norm_num, kbB_al8⟩
  · obtain ⟨-, hr⟩ := uD_slot_range hx
    rcases ha with ⟨t, ht, g1, g2⟩ | ⟨e, he, -⟩ | ⟨r, hr', -⟩ | ⟨n, hn, -⟩ | ⟨wp, hw, -⟩
    · rcases ZR_T.1 ht with rfl | rfl
      · rw [tiB_val] at g1 g2; omega
      · rw [tRw_val] at g1 g2; omega
    · exact he.elim
    · exact hr'.elim
    · exact hn.elim
    · exact hw.elim
  · obtain ⟨-, hr⟩ := uD_slot_range hx
    rw [kbB_val, h00] at h1 h2; omega
  · rcases ha with ⟨t, ht, g1, g2⟩ | ⟨e, he, -⟩ | ⟨r, hr', -⟩ | ⟨n, hn, -⟩ | ⟨wp, hw, -⟩
    · rcases ZR_T.1 ht with rfl | rfl
      · rw [tiB_val] at g1 g2; rw [kbB_val]; omega
      · rw [tRw_val] at g1 g2; rw [kbB_val]; omega
    · exact he.elim
    · exact hr'.elim
    · exact hn.elim
    · exact hw.elim
  · obtain ⟨-, hr⟩ := uD_slot_range hx
    rw [kbB_val] at h1 h2 h0; omega

theorem uD_scApart : Ipc.ScApart ZR.th ZR.C (σR (Z := Unit)) := by
  intro sc hsc x n hk a ha y hy ⟨h1, h2⟩
  obtain ⟨-, hr⟩ := uD_slot_range hy
  rcases ZR_C.1 hsc with rfl | rfl
  · rw [uD_σR_sci] at hk
    cases hk
    obtain ⟨g1, g2⟩ := ha
    rw [sciB_val] at g1 g2
    simp only [Fl4Spec.minSchedContextBits, Nat.zero_add, Nat.reducePow] at g2
    omega
  · rw [uD_σR_scR] at hk
    cases hk
    obtain ⟨g1, g2⟩ := ha
    rw [scRw_val] at g1 g2
    simp only [Fl4Spec.minSchedContextBits, Nat.zero_add, Nat.reducePow] at g2
    omega

/-- **`XTopAt.rel` at the second boot start.** -/
theorem relTopB_R : Ipc.RelTopB (L := bsL) ZR.th ZR.G ZR.N ZR.T ZR.C ZR.E ZR.R ZR.B ZR.c sR (σR (Z := Unit)) :=
  ⟨uD_placed, uD_crel, uD_finInv, uD_domRel, uD_mdbOKV, uD_ipcApart, uD_scApart⟩

end

end Fl4Proofs.P2.BootSt
