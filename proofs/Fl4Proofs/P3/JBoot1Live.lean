/-
P3 (line jboot, gen 4): **the liveness bundle and the `JCarry` facts at the richer witness** (`w1`, `σ1`, the
ghosts of JBoot1Z).

* **`w1_liveJ`** (`LiveJ`): the slots in use are the root TCB's CSpace slot (its TCB is named by the thread cap
  in the root CNode) and the root CNode's two slots (named by the CNode cap in the root TCB); core 0's debug
  list is empty; no zombie. **`w1_dbgWF`** (`DbgWF`, empty lists: both TCBs' debug words zero),
  **`w1_nullOrig`**, hence **`w1_live`** (`JAtZ.live`).
* **`w1_vsNamed`**, **`w1_archFit`**, hence **`w1_carry`** (`JAtZ.carry`).

No sorry; no premises. New module; no existing statement changed.
-/
import Fl4Proofs.P3.JBoot1Blk
import Fl4Proofs.P3.JBootLive
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.JBoot
open fl4_core Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit Classical

noncomputable section

set_option maxHeartbeats 1000000

theorem dbgHead_w1 : dbgHead (L := wL) w1 = 0#u64 := by
  show nodeW wst w1 0#u64 layout.node.DEBUG_TCBS = 0#u64
  rw [show layout.node.DEBUG_TCBS = 88#u64 by unfold layout.node.DEBUG_TCBS; rfl, nodeW1_v _ (by decide) (by decide)]
  decide

/-- **`LiveJ` at `w1`.** -/
theorem w1_liveJ : LiveJ (L := wL) thW1 Hw1 G1 w1 σ1 where
  slots q i hs hu := by
    left
    have hsl : IsSlot thW1 (slotOf q i) := ⟨q, i, hs, rfl⟩
    have hv := IsSlotAt.val placed_thW1 hs
    rcases hu with h | ⟨x, -, hx⟩
    · rcases slot1_cases hsl with ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | e
      · -- the root TCB's slot 0: its TCB is named by the thread cap at `rC`
        have hq : q = rT := by
          have := congrArg UScalar.val e; rw [hv, rT_val] at this
          rcases hs with ⟨r, hq, hi⟩ | ⟨hq, hi⟩ <;> rcases thW1_pos hq with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ |
            ⟨e2, ⟨j, hj, e1⟩ | ⟨j, hj, hj2, e1⟩⟩ <;> (try cases e2) <;>
            first
            | exact UScalar.eq_of_val_eq (by rw [rT_val]; omega)
            | (simp only [Nat.pow_one, Nat.pow_zero] at hi; omega)
            | (unfold tcbSlots at hi; omega)
        subst hq
        exact ⟨rC, G1_flat.2 (Or.inr (Or.inl rfl)), by rw [capV_rC]; rfl⟩
      · have hq : q = rC := by
          have := congrArg UScalar.val e; rw [hv, rC_val] at this
          rcases hs with ⟨r, hq, hi⟩ | ⟨hq, hi⟩ <;> rcases thW1_pos hq with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ |
            ⟨e2, ⟨j, hj, e1⟩ | ⟨j, hj, hj2, e1⟩⟩ <;> (try cases e2) <;>
            first
            | exact UScalar.eq_of_val_eq (by rw [rC_val]; omega)
            | (simp only [Nat.pow_one, Nat.pow_zero] at hi; omega)
            | (unfold tcbSlots at hi; omega)
        subst hq
        exact ⟨rT, G1_flat.2 (Or.inl rfl), by rw [capV_rT]; rfl⟩
      · have hq : q = rC := by
          have := congrArg UScalar.val e; rw [hv] at this; change _ = 18446744071562108960 at this
          rcases hs with ⟨r, hq, hi⟩ | ⟨hq, hi⟩ <;> rcases thW1_pos hq with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ |
            ⟨e2, ⟨j, hj, e1⟩ | ⟨j, hj, hj2, e1⟩⟩ <;> (try cases e2) <;>
            first
            | exact UScalar.eq_of_val_eq (by rw [rC_val]; omega)
            | (simp only [Nat.pow_one, Nat.pow_zero] at hi; omega)
            | (unfold tcbSlots at hi; omega)
        subst hq
        exact ⟨rT, G1_flat.2 (Or.inl rfl), by rw [capV_rT]; rfl⟩
      · exact absurd e h
    · cases hx
  dbg n h := by rw [dbgHead_w1, dbgNth_zero] at h; exact absurd rfl h
  zslots y hy p zt n h := by
    rcases slot1_cases hy with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ | e <;> rw [e] at h <;> cases h
  zdead y hy p zt n h := by
    rcases slot1_cases hy with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ | e <;> rw [e] at h <;> cases h

/-- **`DbgWF` at `w1`** (empty lists). -/
theorem w1_dbgWF : DbgWF (Heap.tcbs Hw1) Csw (wL.mem w1) (dbgHd (L := wL) w1) := by
  refine ⟨fun _ => [], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc
    rw [Csw, Set.mem_singleton_iff] at hc; subst hc
    exact dbgHead_w1
  · intro c _ x hx; cases hx
  · intro c _ x hx; cases hx
  · intro c _; exact List.nodup_nil
  · intro c _ h; cases h
  · intro c _ x hx; cases hx
  · intro y hy _
    rw [tcbs_Hw1] at hy
    exact ⟨dn_w1 y hy, dp_w1 y hy⟩

/-- **`NullOrig` at `w1`.** -/
theorem w1_nullOrig : NullOrig thW1 (wL.mem w1) σ1 := fun _ _ _ => rfl

/-- **`JAtZ.live` at `w1`.** -/
theorem w1_live : LiveDN (L := wL) thW1 Hw1 Csw G1 w1 σ1 := ⟨w1_liveJ, w1_dbgWF, w1_nullOrig⟩

/-! ## `JCarry` -/

theorem atA_w1 (hi : U64) (h : hi.val < 2048) : wL.mem w1 (Vs.atA fkb hi) = 0#u64 := by
  have hv : (Vs.atA fkb hi).val = 18446744071562133504 + 288000 + 8 * hi.val := by
    unfold Vs.atA
    simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits, fkb_val]
    omega
  rw [mem1_al hv (by omega)]; img1z

theorem vsPath1_none {k : Nat} {q : U64} {a v : Nat} (h : Vs.VsPath (wL.mem w1) fkb k q a v) : False := by
  induction h with
  | tbl hi hne => exact hne (atA_w1 _ hi)
  | pool _ _ _ _ ih => exact ih
  | l4 _ _ _ ih => exact ih
  | l3 _ _ _ _ ih => exact ih
  | l2 _ _ _ _ ih => exact ih

/-- **`VsNamed` at `w1`.** -/
theorem w1_vsNamed : Vs.VsNamed thW1 (wL.mem w1) fkb where
  named k q a v h := (vsPath1_none h).elim
  uref y y' hy _ _ hn := by
    rcases slot1_cases hy with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ | e <;> rw [e] at hn <;> exact absurd rfl hn
  uun y y' hy _ _ ht := by
    rcases slot1_cases hy with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ | e <;> rw [e] at ht <;> cases ht
  empty y hy ht := by
    rcases slot1_cases hy with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ | e <;> rw [e] at ht <;> cases ht
  poolT y hy q b h := by
    rcases slot1_cases hy with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ | e <;> rw [e] at h <;> cases h

/-- **`ArchFitHyp` at `w1`.** -/
theorem w1_archFit : ArchFitHyp Hw1 σ1 := by
  intro o ao n hk hH
  rcases kh1_some hk with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ | ⟨n1, n2, n3, h'⟩
  · cases e
  · cases e
  · cases e
  · rw [Hw1_old (fun e => n1 (congrArg UScalar.bv e)) (fun e => n2 (congrArg UScalar.bv e))
      (fun e => n3 (congrArg UScalar.bv e))] at hH
    exact w0_archFit o ao n h' hH

/-- **`JAtZ.carry` at `w1`.** -/
theorem w1_carry : JCarry (L := wL) Zw1 Hw1 Csw w1 σ1 where
  bufPg wp hw := hw.elim
  archFit := w1_archFit
  devApart x hx _ _ _ h := (flat1_nut hx h).elim
  devSep x hx _ _ _ _ _ _ _ _ h _ := (flat1_nut hx h).elim
  vsTyp y hy := by
    show Vs.TabR _ (capV (wL.mem w1) y)
    rcases slot1_cases hy with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ | e <;> rw [e] <;> trivial
  devTab x hx _ _ _ h := (flat1_nut hx h).elim
  vsNamed _ := w1_vsNamed

end

end Fl4Proofs.P3.JBoot
