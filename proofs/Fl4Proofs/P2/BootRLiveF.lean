/-
# P2 (line p3mc, gen 39, unit F): the placement, liveness and carried `JAtZ` fields at the second boot start

At `(sR, σR)` with the ghosts `ZR` (MDB ghost `GR` = one chain `[tRw]`), `HR`, `CsB` (gen 35's `P2/BootLiveF` at
`(sB, σB)`):

* `rp_R` (`RPlaced`: no reply), `apart_R` (`SlotsApart`: the two TCBs' slots `[t, t + 192)` below their words from
  256 on, the IRQ node far from both SCs and core 0's node);
* `live_R` (`LiveDN`: the root slot `tRw` holds `Thread tRw`, a cap of `GR`'s chain, so `LiveJ.slots` at
  `q = tRw` is met by the cap itself (`RefsObj`); every other slot is null and not original (`slotR_cases`,
  `iocR_iff`), so not in use; the debug lists empty (`DEBUG_TCBS` 0, both TCBs' debug links 0); no zombie);
* `carry_R` (`JCarry`: no buffer word, `HR`'s paging structures as `σB`'s (`archFit_B`), no untyped cap, no
  table cap, no VSpace path (the ASID table empty, `uF_vsPath`)).

No premise. No existing statement changed.
-/
import Fl4Proofs.P2.BootRBlkF
import Fl4Proofs.P2.BootLiveF
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.BootSt
open fl4_core Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P1 Classical

noncomputable section

/-! ## Slots of `thR` -/

/-- A slot of `thR`: aligned, its 32 bytes in one of the two TCBs' slot areas or the IRQ node. -/
theorem uF_slot_range {y : U64} (hy : IsSlot thR y) : y.val % 32 = 0 ∧
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

/-- A slot of an object of `thR` at the root slot's address is a slot of the root TCB. -/
theorem uF_slotAt {q : U64} {i : Nat} (h : IsSlotAt thR q i) : q = tRw ∨ slotOf q i ≠ tRw := by
  rcases h with ⟨r, hp, hir⟩ | ⟨hp, hit⟩
  · rcases thR_cases hp with ⟨-, e⟩ | ⟨-, e⟩ | ⟨e, g1, g2, g3⟩
    · cases e
    · cases e
    · cases e
      simp only [Nat.pow_zero] at hir
      right; intro e
      have := congrArg UScalar.val e
      rw [slotOf_val (by omega), tRw_val] at this; omega
  · rcases thR_cases hp with ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩
    · exact Or.inl (eq_of_val'' (by rw [e, tRw_val]))
    · simp only [tcbSlots] at hit
      right; intro e'
      have := congrArg UScalar.val e'
      rw [slotOf_val (by omega), tRw_val] at this; omega
    · cases e

/-- The root slot's address. -/
theorem uF_cslot_root : cslotAddr (tRp, Fl4Spec.tcbCnodeIndex 0) = tRw := by
  show slotAddr tRw.bv (Fl4Spec.ofBl _) = _
  rw [slotAddr_ofBl, tcbCnodeIndex_blVal 0 (by decide)]
  apply eq_of_val''
  show (slotOf tRw 0).val = tRw.val
  rw [slotOf_val (by rw [tRw_val]; omega)]
  rfl

/-! ## `RPlaced`, `SlotsApart` -/

theorem rp_R : RPlaced bst ZR.N ZR.T ZR.C ZR.R ZR.c sR (σR (Z := Unit)) where
  align _ h := h.elim
  ksb _ h := h.elim
  tcb _ h := h.elim
  ntfn _ h := h.elim
  sc _ h := h.elim

/-- The two SCs of `σR` have size bits 0. -/
theorem uF_scBits0 {sc : U64} (hsc : sc ∈ ZR.C) {x : Fl4Spec.SchedContext} {n : Nat}
    (hk : (σR (Z := Unit)).kheap sc.bv = some (.schedContext x n)) : n = 0 := by
  rcases ZR_C.1 hsc with e | e <;> subst e
  · rw [sciB_bv, σR_kheap, kheapR_of_ne (p := Fl4Spec.idleScPtr) (by decide) (by decide), kheapB_sci] at hk
    cases hk; rfl
  · rw [scRw_bv, σR_kheap, kheapR_scR] at hk
    cases hk; rfl

theorem apart_R : SlotsApart (st := bst) ZR.th ZR.T ZR.N ZR.C ZR.R ZR.c sR (σR (Z := Unit)) := by
  intro a ha
  obtain ⟨-, hr⟩ := uF_slot_range ha
  refine ⟨fun t ht => ?_, ?_, fun _ h => h.elim, fun sc hsc x n hk => ?_, fun _ h => h.elim⟩
  · rcases ZR_T.1 ht with e | e <;> subst e
    · rw [tiB_val]; omega
    · rw [tRw_val]; omega
  · rw [show ZR.c = 0#u64 from rfl, sR_nodeBase _ rfl]; omega
  · rw [uF_scBits0 hsc hk]
    simp only [Fl4Spec.minSchedContextBits, Nat.zero_add, Nat.reducePow]
    rcases ZR_C.1 hsc with e | e <;> subst e
    · rw [sciB_val]; omega
    · rw [scRw_val]; omega

/-! ## Liveness -/

theorem uF_root_mem : tRw ∈ GR.chains.flatten := by simp [GR]

theorem uF_GR_mem {x : U64} (hx : x ∈ GR.chains.flatten) : x = tRw := by simpa [GR] using hx

theorem uF_nullOrig : NullOrig thR (bsL.mem sR) (σR (Z := Unit)) := fun sl _ hn => by
  cases h : (σR (Z := Unit)).isOriginalCap sl with
  | false => rfl
  | true =>
    rw [(iocR_iff sl).1 h, uF_cslot_root, capV_R_root] at hn
    cases hn

theorem uF_liveJ : LiveJ (L := bsL) thR HR GR sR (σR (Z := Unit)) where
  slots q i hqi hu := by
    rcases uF_slotAt hqi with rfl | hne
    · left
      refine ⟨tRw, uF_root_mem, ?_⟩
      rw [capV_R_root]
      exact rfl
    · exfalso
      rcases slotR_cases ⟨q, i, hqi, rfl⟩ with e | ⟨hn, -⟩
      · exact hne e
      · rcases hu with h | ⟨x, hx, ho⟩
        · exact h hn
        · rw [(iocR_iff x).1 ho, uF_cslot_root] at hx
          exact hne hx.symm
  dbg n h := by
    have h0 : dbgHead (L := bsL) sR = 0#u64 := sR_dbg_word
    rw [h0, dbgNth_zero] at h; exact absurd rfl h
  zslots y hy p zt n h := by
    rcases slotR_cases hy with rfl | ⟨hn, -⟩
    · rw [capV_R_root] at h; cases h
    · rw [hn] at h; cases h
  zdead y hy p zt n h := by
    rcases slotR_cases hy with rfl | ⟨hn, -⟩
    · rw [capV_R_root] at h; cases h
    · rw [hn] at h; cases h

theorem uF_dbgWF : DbgWF (Heap.tcbs HR) CsB (bsL.mem sR) (dbgHd (L := bsL) sR) :=
  ⟨fun _ => [], {
    head := fun c hc => by rw [mem_CsB hc]; exact sR_dbg_word
    next := fun _ _ _ h => (List.not_mem_nil h).elim
    prev := fun _ _ _ h => (List.not_mem_nil h).elim
    nodup := fun _ _ => List.nodup_nil
    zero := fun _ _ h => (List.not_mem_nil h).elim
    mem := fun _ _ _ h => (List.not_mem_nil h).elim
    off := fun y hy _ => ⟨uF_dn hy, uF_dp hy⟩ }⟩

theorem live_R : LiveDN (L := bsL) ZR.th HR CsB ZR.G sR (σR (Z := Unit)) :=
  ⟨uF_liveJ, uF_dbgWF, uF_nullOrig⟩

/-! ## `JCarry` -/

theorem uF_vsPath {k : Nat} {q : U64} {a v : Nat} (h : Vs.VsPath (bsL.mem sR) kbB k q a v) : False := by
  induction h with
  | tbl hi h0 =>
    apply h0
    rw [memR_at (Vs.atA_val (by rw [kbB_val]; norm_num) hi) (by rw [kbB_val]; omega), kbB_val]
    exact wordR_zero_of (by omega)
  | pool _ _ _ _ ih => exact ih
  | l4 _ _ _ ih => exact ih
  | l3 _ _ _ _ ih => exact ih
  | l2 _ _ _ _ ih => exact ih

theorem uF_archFit : ArchFitHyp HR (σR (Z := Unit)) := by
  intro o ao n ho hH
  rcases kheapR_cases ho with ⟨-, e⟩ | ⟨-, e⟩ | ⟨e1, e2, hB⟩
  · cases e
  · cases e
  · have n1 : (⟨o⟩ : U64).val ≠ 18446744071562076160 := fun e =>
      e1 (BitVec.eq_of_toNat_eq (by rw [tRp_toNat]; exact e))
    have n2 : (⟨o⟩ : U64).val ≠ 18446744071562080256 := fun e =>
      e2 (BitVec.eq_of_toNat_eq (by rw [scRp_toNat]; exact e))
    unfold HR at hH
    rw [if_neg n1, if_neg n2] at hH
    exact archFit_B o ao n hB hH

theorem uF_vsNamed : Vs.VsNamed ZR.th (bsL.mem sR) (bsL.ksb sR) where
  named k q a v h := by rw [sR_ksb] at h; exact (uF_vsPath h).elim
  uref y _ hy _ _ hn := by
    rcases slotR_cases hy with rfl | ⟨h0, -⟩
    · rw [capV_R_root] at hn; exact absurd rfl hn
    · rw [h0] at hn; exact absurd rfl hn
  uun y _ hy _ _ hu := by
    rcases slotR_cases hy with rfl | ⟨h0, -⟩
    · rw [capV_R_root] at hu; exact (show False from hu).elim
    · rw [h0] at hu; exact (show False from hu).elim
  empty y hy hu := by
    rcases slotR_cases hy with rfl | ⟨h0, -⟩
    · rw [capV_R_root] at hu; exact (show False from hu).elim
    · rw [h0] at hu; exact (show False from hu).elim
  poolT y hy q b h := by
    rcases slotR_cases hy with rfl | ⟨h0, -⟩
    · rw [capV_R_root] at h; cases h
    · rw [h0] at h; cases h

theorem carry_R : JCarry (L := bsL) ZR HR CsB sR (σR (Z := Unit)) where
  bufPg _ h := h.elim
  archFit := uF_archFit
  devApart x hx p sb fi hc := by
    have e := uF_GR_mem hx
    subst e
    rw [capV_R_root] at hc; cases hc
  devSep x hx y hy p sb fi p' sb' fi' hc hd := by
    have e := uF_GR_mem hx
    subst e
    rw [capV_R_root] at hc; cases hc
  vsTyp y hy := by
    rcases slotR_cases hy with rfl | ⟨hn, -⟩
    · rw [capV_R_root]; trivial
    · rw [hn]; trivial
  devTab x hx p sb fi hc := by
    have e := uF_GR_mem hx
    subst e
    rw [capV_R_root] at hc; cases hc
  vsNamed _ := uF_vsNamed

end

end Fl4Proofs.P2.BootSt
