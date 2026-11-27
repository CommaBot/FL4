/-
# P2 (line p3mc, gen 35): the placement, liveness and carried `JAtZ` fields at the boot

At `(sB, σB)` with the ghosts `ZB G0`, `HB`, `CsB`:

* `rp_B` (`RPlaced`: no reply), `apart_B` (`SlotsApart`: the idle TCB's slots `[ti, ti + 192)` below its words from
  256 on, the IRQ node far from the idle SC and core 0's node);
* `live_B` (`LiveDN`: every slot null and no original cap, so no slot in use (`NullOrig.notInUse`); the debug lists
  empty (`DEBUG_TCBS` 0, the idle TCB's debug links 0); no zombie);
* `carry_B` (`JCarry`: no buffer word, `HB`'s three `other 12` paging structures no larger than `σB`'s tables, no
  untyped cap, no table cap, no VSpace path (the ASID table empty, `vsPath_B`)).

No premise. No existing statement changed except the root import list.
-/
import Fl4Proofs.P2.BootBlkF
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.BootSt
open fl4_core Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P1 Classical

noncomputable section

theorem rp_B : RPlaced bst (ZB G0).N (ZB G0).T (ZB G0).C (ZB G0).R (ZB G0).c sB (σB (Z := Unit)) where
  align _ h := h.elim
  ksb _ h := h.elim
  tcb _ h := h.elim
  ntfn _ h := h.elim
  sc _ h := h.elim

theorem apart_B : SlotsApart (st := bst) (ZB G0).th (ZB G0).T (ZB G0).N (ZB G0).C (ZB G0).R (ZB G0).c sB
    (σB (Z := Unit)) := by
  intro a ha
  obtain ⟨-, hr⟩ := slot_range ha
  refine ⟨fun t ht => ?_, ?_, fun _ h => h.elim, fun sc hsc x n hk => ?_, fun _ h => h.elim⟩
  · rw [show t = tiB from ht, tiB_val]; omega
  · rw [show (ZB G0).c = 0#u64 from rfl, sB_nodeBase _ rfl]; omega
  · rw [show sc = sciB from hsc, σB_sci] at hk
    cases hk
    rw [show sc = sciB from hsc, sciB_val]
    simp only [Fl4Spec.minSchedContextBits, Nat.zero_add, Nat.reducePow]
    omega

/-! ## Liveness -/

theorem dbgNth_zero (m : U64 → U64) : ∀ n, dbgNth m n 0#u64 = 0#u64
  | 0 => rfl
  | _ + 1 => by simp [dbgNth]

theorem dbgHead_B : dbgHead (L := bsL) sB = 0#u64 := sB_dbg_word

theorem nullOrig_B : NullOrig thB (bsL.mem sB) (σB (Z := Unit)) := fun sl _ _ => iocB_false sl

theorem notInUse_B {y : U64} (hy : IsSlot thB y) : ¬ InUse (bsL.mem sB) (σB (Z := Unit)) y :=
  nullOrig_B.notInUse (fun sl h => by rw [iocB_false] at h; cases h) (slot_null hy)

theorem liveJ_B : LiveJ (L := bsL) thB HB G0 sB (σB (Z := Unit)) where
  slots q i hqi hu := absurd hu (notInUse_B ⟨q, i, hqi, rfl⟩)
  dbg n h := by rw [dbgHead_B, dbgNth_zero] at h; exact absurd rfl h
  zslots y hy p zt n h := by rw [slot_null hy] at h; cases h
  zdead y hy p zt n h := by rw [slot_null hy] at h; cases h

theorem dbgWF_B : DbgWF (Heap.tcbs HB) CsB (bsL.mem sB) (dbgHd (L := bsL) sB) :=
  ⟨fun _ => [], {
    head := fun c hc => by rw [mem_CsB hc]; exact sB_dbg_word
    next := fun _ _ _ h => (List.not_mem_nil h).elim
    prev := fun _ _ _ h => (List.not_mem_nil h).elim
    nodup := fun _ _ => List.nodup_nil
    zero := fun _ _ h => (List.not_mem_nil h).elim
    mem := fun _ _ _ h => (List.not_mem_nil h).elim
    off := fun y hy _ => by
      rw [tcbs_HB hy]
      exact ⟨tw0 (k := 3576) (by decide) (by omega) (by omega) (by omega) (by omega),
        tw0 (k := 3584) (by decide) (by omega) (by omega) (by omega) (by omega)⟩ }⟩

theorem live_B : LiveDN (L := bsL) (ZB G0).th HB CsB (ZB G0).G sB (σB (Z := Unit)) :=
  ⟨liveJ_B, dbgWF_B, nullOrig_B⟩

/-! ## `JCarry` -/

theorem vsPath_B {k : Nat} {q : U64} {a v : Nat} (h : Vs.VsPath (bsL.mem sB) kbB k q a v) : False := by
  induction h with
  | tbl hi h0 =>
    apply h0
    rw [memB_at (Vs.atA_val (by rw [kbB_val]; norm_num) hi) (by rw [kbB_val]; omega), kbB_val]
    exact wordB_zero_of (by omega)
  | pool _ _ _ _ ih => exact ih
  | l4 _ _ _ ih => exact ih
  | l3 _ _ _ _ ih => exact ih
  | l2 _ _ _ _ ih => exact ih

theorem archFit_B : ArchFitHyp HB (σB (Z := Unit)) := by
  intro o ao n ho hH
  rcases kheapB_cases ho with ⟨-, _, e⟩ | ⟨-, _, _, e⟩ | ⟨e, -⟩ | ⟨-, e⟩
  · cases e
  · cases e
  · have hv : (⟨o⟩ : U64).val = 18446744071562084352 ∨ (⟨o⟩ : U64).val = 18446744071562088448 ∨
        (⟨o⟩ : U64).val = 18446744071562092544 := by
      show o.toNat = _ ∨ o.toNat = _ ∨ o.toNat = _
      rcases e with rfl | rfl | rfl
      · left; decide
      · right; left; decide
      · right; right; decide
    have h12 : HB ⟨o⟩ = some (.other 12) := by
      unfold HB; rw [if_neg (by omega), if_neg (by omega), if_pos hv]
    rw [h12] at hH
    cases hH
    rcases e with rfl | rfl | rfl
    · rw [σB_kheap, kheapB_pml4] at ho; cases ho; decide
    · rw [σB_kheap, kheapB_pdpt] at ho; cases ho; decide
    · rw [σB_kheap, kheapB_pd] at ho; cases ho; decide
  · cases e

theorem vsNamed_B : Vs.VsNamed (ZB G0).th (bsL.mem sB) (bsL.ksb sB) where
  named k q a v h := by rw [sB_ksb] at h; exact (vsPath_B h).elim
  uref y _ hy _ _ hn := by rw [slot_null hy] at hn; exact absurd rfl hn
  uun y _ hy _ _ hu := by rw [slot_null hy] at hu; exact (show False from hu).elim
  empty y hy hu := by rw [slot_null hy] at hu; exact (show False from hu).elim
  poolT y hy q b h := by rw [slot_null hy] at h; cases h

theorem carry_B : JCarry (L := bsL) (ZB G0) HB CsB sB (σB (Z := Unit)) where
  bufPg _ h := h.elim
  archFit := archFit_B
  devApart x hx := by simp [ZB, G0] at hx
  devSep x hx := by simp [ZB, G0] at hx
  vsTyp y hy := by rw [slot_null hy]; trivial
  devTab x hx := by simp [ZB, G0] at hx
  vsNamed _ := vsNamed_B

end

end Fl4Proofs.P2.BootSt
