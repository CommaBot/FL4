/-
# P2 (line p3mc, gen 39, unit D): `XTopAt.rel` (`RelTopB`) at the second boot start

At `(sR, σR)` with the ghosts `ZR` (MDB ghost `GR` = one chain `[tRw]`, no parent), every part of P3's `RelTopB`,
gen 35's `P2/BootRelF` ported:

* `Placed thR` (`uD_placed`);
* `CRel`: `uD_stateRel` (`StateRel`: the IRQ CNodes as at `σB`; the idle TCB's six null slots; the root TCB's slot 0
  `Thread tRw` related to `threadCap tRp`, its other five slots null), `uD_slotsValid` (the thread cap names
  `thR`'s TCB `tRw`), **`uD_mdbLinks`** (`MdbLinks` at `GR`: the one-slot chain, links 0), **`uD_cdtRel`**
  (`CdtRel`: `cdt` empty, the original slot exactly the revocable root slot, `cslotAddr_inj`), `uD_mdbInv`;
* `FinInv`: `uD_kTyped` (`KTyped thR σR`), `uD_finM` (one slot: vacuous but `conn`);
* `uD_domRel` (`DomRel`: `σB`'s domain table words, untouched by `wordR`);
* `uD_mdbOKV` (`MdbOKV` at `GR`: the thread cap is no frame / untyped / VSpace cap, its range `[tRw, tRw + 4096)`
  does not wrap);
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

/-- A slot of `thR` other than the root slot holds the null cap. -/
theorem uD_capAt_ne {y : U64} (hy : IsSlot thR y) (hn : y.val ≠ 18446744071562076160) :
    capAt (bsL.mem sR) y = ok .Null := by
  rcases slotR_cases hy with e | ⟨h, -⟩
  · exact absurd (show y.val = 18446744071562076160 by rw [e, tRw_val]) hn
  · rw [capAt_capV, h]

theorem uD_root_slot : slotOf tRw 0 = tRw :=
  eq_of_val'' (by rw [slotOf_val (by rw [tRw_val]; omega), tRw_val])

/-- The root TCB's slots 1 … 5: null caps. -/
theorem uD_tcbR_map {i : Nat} (hi : i < 6) (h0 : i ≠ 0) :
    Fl4Spec.tcbCnodeMap tcbR (Fl4Spec.tcbCnodeIndex i) = some .nullCap := by
  interval_cases i
  · exact absurd rfl h0
  all_goals
    simp only [Fl4Spec.tcbCnodeMap, Function.update_apply]
    repeat (first | rw [if_neg (by decide)] | rw [if_pos rfl])
    all_goals rfl

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
          refine uD_capAt_ne ⟨p, 0, Or.inl ⟨0, hp, by norm_num⟩, rfl⟩ ?_
          rw [slotOf_val (by omega)]; omega
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
      · refine ⟨.Null, .nullCap, uD_capAt_ne ⟨tRw, i, Or.inr ⟨thR_tR, hi⟩, rfl⟩ ?_,
          uD_tcbR_map hi6 h0, ⟨trivial, rfl⟩⟩
        rw [slotOf_val (by rw [tRw_val]; omega), tRw_val]; omega
    · have : t = tiB := eq_of_val' (by rw [e, tiB_val])
      subst this
      refine ⟨idleTcbB, uD_σR_ti, fun i hi => ?_⟩
      have hi6 : i < 6 := hi
      refine ⟨.Null, .nullCap, uD_capAt_ne ⟨tiB, i, Or.inr ⟨thR_ti, hi⟩, rfl⟩ ?_, idleMap hi6,
        ⟨trivial, rfl⟩⟩
      rw [slotOf_val (by rw [tiB_val]; omega), tiB_val]; omega
    · cases e

theorem uD_capValid {y : U64} (hy : IsSlot thR y) {c : capability.Cap} (hc : capAt (bsL.mem sR) y = ok c) :
    CapValid thR c := by
  rcases slotR_cases hy with rfl | ⟨hn, -⟩
  · rw [capAt_capV, capV_R_root] at hc
    cases ok_inj_ff hc
    exact thR_tR
  · rw [capAt_capV, hn] at hc
    cases ok_inj_ff hc
    trivial

theorem uD_slotsValid : SlotsValid thR (bsL.mem sR) where
  cnode p r hp i hi c hc := uD_capValid ⟨p, i, Or.inl ⟨r, hp, hi⟩, rfl⟩ hc
  tcb t ht i hi c hc := uD_capValid ⟨t, i, Or.inr ⟨ht, hi⟩, rfl⟩ hc

theorem uD_flat : GR.chains.flatten = [tRw] := rfl

theorem uD_mem_flat {x : U64} (h : x ∈ GR.chains.flatten) : x = tRw := by
  rw [uD_flat] at h; exact List.mem_singleton.1 h

theorem uD_mem_chains {ch : List U64} (h : ch ∈ GR.chains) : ch = [tRw] := List.mem_singleton.1 h

theorem uD_desc {y x : U64} (h : Mdb.Desc GR.par y x) : False := by
  cases h with
  | single h => simp [GR] at h
  | tail _ h => simp [GR] at h

theorem uD_mdbLinks : MdbLinks thR (bsL.mem sR) GR where
  tree := ⟨by rw [uD_flat]; exact List.nodup_singleton _,
    fun ch _ pre x post _ => ⟨[], post, rfl, fun y => ⟨fun h => (uD_desc h).elim, fun h => by cases h⟩⟩,
    fun a b h => by simp [GR] at h⟩
  ne_nil ch h := by rw [uD_mem_chains h]; simp
  chain ch h := by rw [uD_mem_chains h]; simp
  head ch h hne := by
    obtain rfl := uD_mem_chains h
    exact prevOf_R_root
  last ch h hne := by
    obtain rfl := uD_mem_chains h
    exact nextOf_R_root
  members a := by
    rw [uD_flat, List.mem_singleton]
    constructor
    · rintro rfl
      exact ⟨isSlot_R_root, _, by rw [capAt_capV, capV_R_root], by intro h; cases h⟩
    · rintro ⟨hs, c, hc, hn⟩
      exact slotR_nonnull hs (by intro h; rw [capAt_capV, h] at hc; exact hn (ok_inj_ff hc).symm)

/-- The root slot's spec address. -/
theorem uD_root_cslot : cslotAddr (tRp, Fl4Spec.tcbCnodeIndex 0) = tRw := by
  apply UScalar.eq_of_val_eq
  show (tRp + Fl4Spec.ofBl (Fl4Spec.tcbCnodeIndex 0) * 32#64).toNat =
    (BitVec.ofNat 64 18446744071562076160).toNat
  decide

theorem uD_cdtRel : CdtRel thR (bsL.mem sR) (σR (Z := Unit)) GR where
  cdt _ _ := rfl
  cdt_slot _ _ h := by cases h
  orig sl hs := by
    by_cases e : sl = (tRp, Fl4Spec.tcbCnodeIndex 0)
    · subst e
      rw [(iocR_iff _).2 rfl, uD_root_cslot, revOf_R_root]
    · have h1 : (σR (Z := Unit)).isOriginalCap sl = false := by
        cases h : (σR (Z := Unit)).isOriginalCap sl
        · rfl
        · exact absurd ((iocR_iff sl).1 h) e
      rw [h1]
      rcases slotR_cases hs.isSlot with h2 | ⟨-, -, -, h2, -⟩
      · exact absurd (cslotAddr_inj uD_placed hs absSlot_R_root (by rw [h2, uD_root_cslot])) e
      · exact h2.symm
  par_slot _ _ h := by cases h

theorem uD_srSelf : srM (bsL.mem sR) tRw tRw = true := by
  unfold srM; rw [capV_R_root]; exact srB_of_eq (by simp [objects.same_region_as])

theorem uD_mdbInv : MdbInv (bsL.mem sR) GR where
  orig c p h := by simp [GR] at h
  desc x y h := (uD_desc h).elim
  after y hy hn := by rw [uD_mem_flat hy] at hn; exact absurd nextOf_R_root hn
  chunk ch h := by rw [uD_mem_chains h]; exact ⟨trivial, trivial⟩
  badges y hy hn := by rw [uD_mem_flat hy] at hn; exact absurd nextOf_R_root hn
  utrev x hx h := by rw [uD_mem_flat hx, capV_R_root] at h; simp [isUt] at h
  self x hx _ := by rw [uD_mem_flat hx]; exact uD_srSelf

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

theorem uD_finM : FinM (bsL.mem sR) GR where
  conn ch1 h1 ch2 h2 _ _ _ _ _ := by rw [uD_mem_chains h1, uD_mem_chains h2]
  key x hx y hy hne := by rw [uD_mem_flat hx, uD_mem_flat hy] at hne; exact absurd rfl hne
  fnest x hx y hy hne := by rw [uD_mem_flat hx, uD_mem_flat hy] at hne; exact absurd rfl hne
  zfin x hx y hy hne := by rw [uD_mem_flat hx, uD_mem_flat hy] at hne; exact absurd rfl hne

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

theorem uD_tcbBits : (fl4_abi.consts.bits.TCB).val = 12 := by simp [fl4_abi.consts.bits.TCB]

/-- The thread cap's range `[tRw, tRw + 4095]` does not wrap. -/
theorem uD_reg : baseF (capability.Cap.Thread tRw) ≤ topF (.Thread tRw) := by
  unfold baseF topF
  rw [ptrF_thread, uD_sizeF_thread]
  have hm : (maskF fl4_abi.consts.bits.TCB).val = 2 ^ 12 - 1 := by
    rw [maskF_val (by rw [uD_tcbBits]; omega), uD_tcbBits]
  simp only [core.num.U64.wrapping_add_val_eq, hm, tRw_val]
  (try simp [U64.size, U64.numBits]) <;> omega

theorem uD_frameInv : Vs.FrameInv (bsL.mem sR) GR := by
  intro x hx p r m ep a va h
  rw [uD_mem_flat hx, capV_R_root] at h; cases h

theorem uD_utInv : UtInv (bsL.mem sR) GR where
  reg x hx _ := by rw [uD_mem_flat hx, capV_R_root]; exact uD_reg
  inc x hx p sb fi d h := by rw [uD_mem_flat hx, capV_R_root] at h; cases h
  noov x hx p sb fi d h := by rw [uD_mem_flat hx, capV_R_root] at h; cases h
  excl x hx y hy hne := by rw [uD_mem_flat hx, uD_mem_flat hy] at hne; exact absurd rfl hne
  fib x hx p sb fi d h := by rw [uD_mem_flat hx, capV_R_root] at h; cases h
  drange x hx p sb fi d h := by rw [uD_mem_flat hx, capV_R_root] at h; cases h

theorem uD_noOv : NoOverlap (bsL.mem sR) GR := by
  intro x hx y hy _ _ _
  rw [uD_mem_flat hx, uD_mem_flat hy, capV_R_root]
  exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl⟩))

theorem uD_utWin : UtWin (bsL.mem sR) GR := by
  intro x hx; rw [uD_mem_flat hx, capV_R_root]; trivial

theorem uD_vsMdb : Vs.VsMdbInv kbB (bsL.mem sR) GR :=
  ⟨⟨∅, ∅, ∅, ∅, ∅, fun x hx => by rw [uD_mem_flat hx, capV_R_root]; trivial⟩,
    fun x hx p sb fi h => by rw [uD_mem_flat hx, capV_R_root] at h; cases h⟩

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
