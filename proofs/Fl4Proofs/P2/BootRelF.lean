/-
# P2 (line p3mc, gen 35): `XTopAt.rel` (`RelTopB`) at the boot

At `(sB, σB)` with the ghosts `ZB G0` (gen 34's `G0`: no MDB chains), every part of P3's `RelTopB`:

* `Placed` (gen 34's `placed_B`);
* `CRel`: **`stateRel_B`** (`StateRel`: each of `thB`'s 128 IRQ-node CNodes is `σB`'s one-slot `emptyCnode 0` at the
  same address, `kheapB_irqObj`; the idle TCB's six slots are the idle TCB's six null caps, `idleMap`; every FL4
  slot null, `slot_capAt`), `slotsValid_B` (null caps are valid), `mdbLinks_B` / `cdtRel_B` (gen 34),
  `mdbInv_B` (`MdbInv` at `G0`: no chain, no parent);
* `FinInv`: **`kTyped_B`** (`KTyped`: `σB`'s CNodes are the IRQ CNodes, its one TCB the idle TCB, all in `thB`),
  `finM_B` (gen 34);
* **`domRel_B`** (`DomRel`: `domainList = [(0, −1), (0, 0)]` = the table words (0, 2^56 − 1), (0, 0); start index 0,
  `DOM_SCHED_IDX` 0);
* `mdbOKV_B` (`MdbOKV` at `G0`, vacuous: no chain);
* **`ipcApart_B`** (`IpcApart`: the idle TCB's IPC words `[ti + 256, ti + 4096)` miss its slots `[ti, ti + 192)` and
  the IRQ node; core 0's node and the rest of the block hold no slot);
* `scApart_B` (`ScApart`: the idle SC's 128 bytes hold no slot);
* **`relTopB_B`**: all of `RelTopB thB G0 ∅ {tiB} {sciB} ∅ ∅ ∅ 0 sB σB`.

No premise. No existing statement changed except the root import list.
-/
import Fl4Proofs.P2.BootWordF
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.BootSt
open fl4_core Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P1 Classical

noncomputable section

/-! ## The IRQ-node CNodes and the idle TCB's slots -/

/-- `σB`'s IRQ CNode at an address of `thB`'s IRQ node. -/
theorem kheapB_irqObj {p : U64} (h1 : 18446744071562101984 ≤ p.val) (h2 : p.val < 18446744071562100736 + 5344)
    (h3 : (p.val - 18446744071562100736) % 32 = 0) :
    kheapB p.bv = some (.cnode 0 (Fl4Spec.emptyCnode 0)) := by
  have hne : ∀ q : Fl4Spec.ObjRef, q.toNat + 4096 ≤ kbB.val → p.bv ≠ q := by
    intro q hq e
    have : p.val = q.toNat := by rw [← e]; rfl
    rw [kbB_val] at hq; omega
  obtain ⟨b1, b2, b3, b4, b5⟩ := σB_below
  have hex : ∃ irq : Fl4Spec.Irq, irq.toNat < 128 ∧
      irqNodeB + (Fl4Spec.ucast 64 irq <<< Fl4Spec.cteLevelBits) = p.bv := by
    refine ⟨BitVec.ofNat 8 ((p.val - 18446744071562101984) / 32), ?_, ?_⟩
    · simp only [BitVec.toNat_ofNat, Nat.reducePow]; omega
    · apply BitVec.eq_of_toNat_eq
      have hv := σB_node_val (BitVec.ofNat 8 ((p.val - 18446744071562101984) / 32))
      change (irqNodeB + _).toNat = _ at hv
      rw [hv, kbB_val]
      simp only [BitVec.toNat_ofNat, Nat.reducePow]
      show _ = p.val
      omega
  unfold kheapB
  rw [Function.update_of_ne (hne _ b4), Function.update_of_ne (hne _ b3), Function.update_of_ne (hne _ b2),
    Function.update_of_ne (hne _ b5), Function.update_of_ne (hne _ b1), if_pos hex]

/-- An IRQ-node address is a CNode of `thB`. -/
theorem thB_irq {p : U64} (h1 : 18446744071562100736 + 1248 ≤ p.val) (h2 : p.val < 18446744071562100736 + 5344)
    (h3 : (p.val - 18446744071562100736) % 32 = 0) : thB p = some (.cnode 0) := by
  unfold thB
  rw [if_neg (by omega), if_pos ⟨h1, h2, h3⟩]

/-- The idle TCB's six slots: null caps. -/
theorem idleMap {i : Nat} (hi : i < 6) :
    Fl4Spec.tcbCnodeMap idleTcbB (Fl4Spec.tcbCnodeIndex i) = some .nullCap := by
  simp only [Fl4Spec.tcbCnodeMap, Function.update_apply]
  split_ifs with h5 h4 h3 h2 h1 h0 <;> try rfl
  interval_cases i <;> simp_all

theorem stateRel_B : StateRel thB (bsL.mem sB) (σB (Z := Unit)) where
  cnode p r hp := by
    rcases thB_cases hp with ⟨-, e⟩ | ⟨e, g1, g2, g3⟩
    · cases e
    · cases e
      refine ⟨Fl4Spec.emptyCnode 0, kheapB_irqObj (by omega) g2 g3, ?_, ?_⟩
      · unfold Fl4Spec.wellFormedCnodeN Fl4Spec.emptyCnode Fl4Spec.dom; ext x; simp
      · intro idx hl
        have hidx : idx = [] := List.length_eq_zero_iff.1 hl
        subst hidx
        refine ⟨.Null, .nullCap, ?_, ?_, ⟨trivial, rfl⟩⟩
        · rw [slotAddr_ofBl]; exact slot_capAt ⟨p, _, Or.inl ⟨0, hp, by simp [blVal]⟩, rfl⟩
        · simp [Fl4Spec.emptyCnode]
  tcb t ht := by
    rcases thB_cases ht with ⟨e, -⟩ | ⟨e, -⟩
    · have : t = tiB := eq_of_val' (by rw [e, tiB_val])
      subst this
      exact ⟨idleTcbB, σB_ti, fun i hi =>
        ⟨.Null, .nullCap, slot_capAt ⟨tiB, i, Or.inr ⟨thB_ti, hi⟩, rfl⟩, idleMap hi, ⟨trivial, rfl⟩⟩⟩
    · cases e

theorem slotsValid_B : SlotsValid thB (bsL.mem sB) where
  cnode p r hp i hi c hc := by
    rw [slot_capAt ⟨p, i, Or.inl ⟨r, hp, hi⟩, rfl⟩] at hc
    cases ok_inj_ff hc; trivial
  tcb t ht i hi c hc := by
    rw [slot_capAt ⟨t, i, Or.inr ⟨ht, hi⟩, rfl⟩] at hc
    cases ok_inj_ff hc; trivial

theorem desc_G0 {y x : U64} (h : Mdb.Desc G0.par y x) : False := by
  cases h with
  | single h => simp [G0] at h
  | tail _ h => simp [G0] at h

theorem mdbInv_B : MdbInv (bsL.mem sB) G0 where
  orig c p h := by simp [G0] at h
  desc x y h := (desc_G0 h).elim
  after y hy := by simp [G0] at hy
  chunk ch h := by simp [G0] at h
  badges y hy := by simp [G0] at hy
  utrev x hx := by simp [G0] at hx
  self x hx := by simp [G0] at hx

theorem crel_B : CRel thB (bsL.mem sB) (σB (Z := Unit)) G0 :=
  ⟨stateRel_B, slotsValid_B, mdbLinks_B, cdtRel_B, mdbInv_B⟩

/-! ## `FinInv` -/

theorem kTyped_B : KTyped thB (σB (Z := Unit)) := by
  intro o
  refine ⟨fun r cs h _ => ?_, fun t h => ?_⟩
  · rcases kheapB_cases h with ⟨-, _, e⟩ | ⟨-, _, _, e⟩ | ⟨-, _, e⟩ | ⟨⟨irq, hi, e⟩, e2⟩
    · cases e
    · cases e
    · cases e
    · cases e2
      have hv := σB_node_val irq
      change (irqNodeB + _).toNat = _ at hv
      rw [e, kbB_val] at hv
      exact thB_irq (p := ⟨o⟩) (by show _ ≤ o.toNat; omega) (by show o.toNat < _; omega)
        (by show (o.toNat - _) % 32 = 0; omega)
  · obtain ⟨e, -⟩ := kheapB_tcb h
    subst e
    rw [← tiB_bv]; exact thB_ti

theorem finInv_B : FinInv thB (bsL.mem sB) (σB (Z := Unit)) G0 := ⟨kTyped_B, finM_B G0 mdbLinks_B⟩

/-! ## The domain schedule -/

theorem ksWB_val {o : U64} {n : Nat} (ho : o.val = n) (hn : n < 13568) :
    (ksW kbB o).val = 18446744071562100736 + n := by
  rw [ksW_val (by rw [kbB_val, ho]; omega), kbB_val, ho]

theorem domRel_B : DomRel (bsL.mem sB) (bsL.ksb sB) (σB (Z := Unit)) := by
  rw [sB_ksb]
  refine ⟨rfl, fun i hi => ?_, ?_, ?_⟩
  · have hev := ksWB_val (entOff_val hi) (by omega)
    have hdv := ksWB_val (durOff_val hi) (by omega)
    rw [memB_at hev (by omega), memB_at hdv (by omega)]
    rcases (by omega : i.val = 0 ∨ i.val = 1) with h0 | h0 <;> rw [h0]
    · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [wordB, σB] <;> first | rfl | decide
    · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [wordB, σB] <;> first | rfl | decide
  · rw [memB_at (ksWB_val (o := 32#u64) (n := 32) (by decide) (by omega)) (by omega), wordB_zero_of (by omega)]; rfl
  · rw [memB_at (ksWB_val (o := 24#u64) (n := 24) (by decide) (by omega)) (by omega), wordB_zero_of (by omega)]

/-! ## The MDB invariants (vacuous) -/

theorem mdbOKV_B : MdbOKV (bsL.ksb sB) (bsL.mem sB) G0 :=
  ⟨⟨fun x hx => by simp [G0] at hx, utInv_B, fun x hx => by simp [G0] at hx⟩, fun x hx => by simp [G0] at hx,
    ⟨⟨∅, ∅, ∅, ∅, ∅, fun x hx => by simp [G0] at hx⟩, fun x hx => by simp [G0] at hx⟩⟩

/-! ## The IPC words and the SCs apart from the slots -/

theorem ipcApart_B : Ipc.IpcApart (ZB G0).th (ZB G0).N (ZB G0).T (ZB G0).E (ZB G0).R (ZB G0).B (bsL.ksb sB)
    (ZB G0).c := by
  show Ipc.IpcApart thB ∅ {tiB} ∅ ∅ ∅ kbB 0#u64
  have h00 : (0#u64 : U64).val = 0 := rfl
  refine ⟨fun a ha x hx ⟨h1, h2⟩ => ?_, fun a h1 h2 x hx ⟨h3, h4⟩ => ?_, fun a ha => ?_,
    fun a h1 h2 h0 x hx ⟨h3, h4⟩ => ?_, by rw [kbB_val]; norm_num, kbB_al8⟩
  · obtain ⟨-, hr⟩ := slot_range hx
    rcases ha with ⟨t, ht, g1, g2⟩ | ⟨e, he, -⟩ | ⟨r, hr', -⟩ | ⟨n, hn, -⟩ | ⟨wp, hw, -⟩
    · have : t = tiB := ht
      subst this; rw [tiB_val] at g1 g2; omega
    · exact he.elim
    · exact hr'.elim
    · exact hn.elim
    · exact hw.elim
  · obtain ⟨-, hr⟩ := slot_range hx
    rw [kbB_val, h00] at h1 h2; omega
  · rcases ha with ⟨t, ht, g1, g2⟩ | ⟨e, he, -⟩ | ⟨r, hr', -⟩ | ⟨n, hn, -⟩ | ⟨wp, hw, -⟩
    · have : t = tiB := ht
      subst this; rw [tiB_val] at g1 g2; rw [kbB_val]; omega
    · exact he.elim
    · exact hr'.elim
    · exact hn.elim
    · exact hw.elim
  · obtain ⟨-, hr⟩ := slot_range hx
    rw [kbB_val] at h1 h2 h0; omega

theorem scApart_B : Ipc.ScApart (ZB G0).th (ZB G0).C (σB (Z := Unit)) := by
  intro sc hsc x n hk a ha y hy ⟨h1, h2⟩
  have e : sc = sciB := hsc
  subst e
  rw [σB_sci] at hk
  cases hk
  obtain ⟨-, hr⟩ := slot_range hy
  obtain ⟨g1, g2⟩ := ha
  rw [sciB_val] at g1 g2
  simp only [Fl4Spec.minSchedContextBits, Nat.zero_add, Nat.reducePow] at g2
  omega

/-- **`XTopAt.rel` at the boot.** -/
theorem relTopB_B : Ipc.RelTopB (L := bsL) (ZB G0).th (ZB G0).G (ZB G0).N (ZB G0).T (ZB G0).C (ZB G0).E (ZB G0).R
    (ZB G0).B (ZB G0).c sB (σB (Z := Unit)) :=
  ⟨placed_B, crel_B, finInv_B, domRel_B, mdbOKV_B, ipcApart_B, scApart_B⟩

end

end Fl4Proofs.P2.BootSt
