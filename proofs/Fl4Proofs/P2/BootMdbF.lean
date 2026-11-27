/-
# P2 (line p3mc, gen 34): the CSpace / MDB `JAtZ` fields at the boot state (all slots null, empty MDB)

Every slot of the boot typed heap `thB` holds the null cap with zero links in `memB` (`slot_word0`), so the MDB ghost is
**`G0`** (no chains, no parents) and every MDB tree of `thB` at `sB` has no chains (`links_nil`). At `ZB G0`:

* `placed_B` (`Placed thB`), `delBound_B` (`DelBound`, `DelBound.of_placed`);
* `mdbLinks_B` (`MdbLinks`), `cdtRel_B` (`CdtRel`: `initCdt` empty, `σB`'s original-cap map false = the revocable
  bits 0), `finM_B` (`FinM` at every tree), `delInv_B` (`DelInv`), `utInv_B` (`UtInv` at `G0`), `sfree_B`
  (`SpecFree`), `utc_B` (no untyped cap), `zD_B` (no zombie);
* **`jcov_B`**: `JCovD thB HB G0 DB CsB sB` (the idle TCB / SC exempt as idle objects, the block's objects as
  `KsObj`, the three paging structures dead: `DB`).

No premise. No existing statement changed except the root import list.
-/
import Fl4Proofs.P2.BootSpecF
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.BootSt
open fl4_core Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P1 Classical

noncomputable section

/-- The boot MDB ghost: no chains, no parents. -/
def G0 : MdbGhost := ⟨[], fun _ => none⟩

theorem placed_B : Placed thB where
  align p k hp := by rcases thB_cases hp with ⟨e, -⟩ | ⟨-, g1, g2, g3⟩ <;> omega
  fits p k hp := by
    rcases thB_cases hp with ⟨e, rfl⟩ | ⟨rfl, g1, g2, g3⟩ <;> simp only [P3.objSize, Nat.pow_zero] <;> omega
  disj p q kp kq hp hq hne := by
    have hv := U64.ne_of_val hne
    rcases thB_cases hp with ⟨e, rfl⟩ | ⟨rfl, g1, g2, g3⟩ <;> rcases thB_cases hq with ⟨f, rfl⟩ | ⟨rfl, f1, f2, f3⟩ <;>
      simp only [P3.objSize, Nat.pow_zero] <;> omega
  high p k hp := by rcases thB_cases hp with ⟨e, -⟩ | ⟨-, g1, g2, g3⟩ <;> omega

theorem delBound_B : DelBound thB := DelBound.of_placed placed_B

/-- A slot of `thB`: aligned, its 32 bytes in the idle TCB's slot area or the IRQ node. -/
theorem slot_range {y : U64} (hy : IsSlot thB y) : y.val % 32 = 0 ∧
    ((18446744071562072064 ≤ y.val ∧ y.val + 32 ≤ 18446744071562072064 + 192) ∨
      (18446744071562100736 + 1248 ≤ y.val ∧ y.val + 32 ≤ 18446744071562100736 + 5344)) := by
  obtain ⟨p, i, hi, rfl⟩ := hy
  rcases hi with ⟨r, hp, hir⟩ | ⟨hp, hit⟩
  · rcases thB_cases hp with ⟨-, e⟩ | ⟨e, g1, g2, g3⟩
    · cases e
    · cases e
      simp only [Nat.pow_zero] at hir
      rw [slotOf_val (by omega)]
      exact ⟨by omega, Or.inr ⟨by omega, by omega⟩⟩
  · rcases thB_cases hp with ⟨e, -⟩ | ⟨e, -⟩
    · simp only [tcbSlots] at hit
      rw [slotOf_val (by omega)]
      exact ⟨by omega, Or.inl ⟨by omega, by omega⟩⟩
    · cases e

/-- **Every word of a slot of `thB` is 0 in `sB`.** -/
theorem slot_word0 {y : U64} (hy : IsSlot thB y) {K : U64} (hK : K.val < 32) (h8 : K.val % 8 = 0) :
    bsL.mem sB (wordOf y K) = 0#u64 := by
  obtain ⟨ha, hr⟩ := slot_range hy
  have hw : (wordOf y K).val = y.val + K.val := by
    show (core.num.U64.wrapping_add y K).val = _
    simp only [core.num.U64.wrapping_add_val_eq]; simp [U64.size, U64.numBits]; omega
  rw [memB_mem (by show _ % 8 = 0; rw [hw]; omega), hw]
  exact wordB_zero (by omega)

theorem slot_capAt {y : U64} (hy : IsSlot thB y) : capAt (bsL.mem sB) y = ok .Null := by
  rw [capAt_capV, slot_null hy]

theorem mdbLinks_B : MdbLinks thB (bsL.mem sB) G0 where
  tree := ⟨List.nodup_nil, fun _ h => (by cases h), fun _ _ h => (by cases h)⟩
  ne_nil _ h := by cases h
  chain _ h := by cases h
  head _ h := by cases h
  last _ h := by cases h
  members a := by
    constructor
    · intro h; cases h
    · rintro ⟨hs, c, hc, hn⟩
      rw [slot_capAt hs] at hc
      exact absurd (ok_inj_ff hc).symm hn

/-- **Every MDB tree of `thB` at `sB` has no chains.** -/
theorem links_nil {G : MdbGhost} (hM : MdbLinks thB (bsL.mem sB) G) : G.chains = [] := by
  have hf : G.chains.flatten = [] := by
    apply List.eq_nil_iff_forall_not_mem.2
    intro a ha
    obtain ⟨hs, c, hc, hn⟩ := (hM.members a).1 ha
    rw [slot_capAt hs] at hc
    exact hn (ok_inj_ff hc).symm
  cases hG : G.chains with
  | nil => rfl
  | cons ch rest =>
    have hne := hM.ne_nil ch (by rw [hG]; exact List.mem_cons_self)
    rw [hG, List.flatten_cons] at hf
    exact absurd (List.append_eq_nil_iff.1 hf).1 hne

theorem cdtRel_B : CdtRel thB (bsL.mem sB) (σB (Z := Unit)) G0 where
  cdt _ _ := rfl
  cdt_slot _ _ h := by cases h
  orig sl hs := by
    rw [iocB_false]
    have h0 := slot_word0 hs.isSlot (K := 24#u64) (by decide) (by decide)
    unfold revOf; rw [h0]; rfl
  par_slot _ _ h := by cases h

theorem finM_B : ∀ G, MdbLinks thB (bsL.mem sB) G → FinM (bsL.mem sB) G := by
  intro G hM
  have hG := links_nil hM
  constructor <;> (intro x hx; rw [hG] at hx; first | cases hx | simp at hx)

theorem delInv_B : DelInv thB (bsL.mem sB) where
  zwf y hy p zt n h := by rw [slot_null hy] at h; cases h
  zu y y' hy _ _ p zt n p' zt' n' h := by rw [slot_null hy] at h; cases h
  nc y hy _ := ⟨slot_word0 hy (K := 16#u64) (by decide) (by decide), by
    unfold nextOf; rw [slot_word0 hy (K := 24#u64) (by decide) (by decide)]; rfl⟩

theorem utInv_B : UtInv (bsL.mem sB) G0 := by
  constructor <;> (intro x hx; first | cases hx | simp [G0] at hx)

theorem sfree_B : SpecFree (bsL.mem sB) G0 (σB (Z := Unit)) := fun _ h => by cases h

theorem utc_B : ∀ sl p sb fi dev, AbsSlot thB sl → capAt (bsL.mem sB) (cslotAddr sl) = ok (.Untyped p sb fi dev) →
    dev = false → Sched.UtCapP3 (L := bsL) LocPlatM.archT thB sB (σB (Z := Unit)) G0 sl p sb fi := by
  intro sl p sb fi dev hs hc _
  rw [slot_capAt hs.isSlot] at hc
  cases ok_inj_ff hc

theorem zD_B : ∀ p ∈ ZTcb (L := bsL) thB sB, p ∈ DB := by
  rintro p ⟨y, hy, zt, n, h, -⟩
  rw [slot_null hy] at h; cases h

theorem sB_idleScW : idleScW (L := bsL) sB = sciB := by
  unfold idleScW
  rw [sB_cpu]
  have h0 : layout.node.IDLE_SC.val = 32 := by simp [layout.node.IDLE_SC]
  rw [memB_mem (node_aligned (by omega) (by omega)), sB_nodeAt_val (by omega), h0]
  simp [wordB]

/-- An object of the kernel-state block is a `KsObj`. -/
theorem ksObj_B {q : U64} (h1 : 18446744071562100736 ≤ q.val) (h2 : q.val < 18446744071562100736 + 13568) :
    KsObj (L := bsL) thB HB sB q := by
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩ <;> unfold KsIn <;> rw [sB_ksb, kbB_val]
  · rcases thB_cases hk with ⟨e, -⟩ | ⟨rfl, g1, g2, g3⟩
    · omega
    · simp only [P3.objSize, Nat.pow_zero]; omega
  · rcases HB_cases hk with ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨rfl, g1, g2, g3⟩ | ⟨rfl, g1, g2, g3, -⟩
    · omega
    · omega
    · omega
    · simp only [HKind.bits, Nat.reducePow]; omega
    · simp only [HKind.bits, Nat.reducePow]; omega

theorem jcov_B : JCovD (L := bsL) thB HB G0 DB CsB sB where
  th q k hq := by
    right
    rcases thB_cases hq with ⟨e, -⟩ | ⟨-, g1, g2, -⟩
    · right; left; left
      rw [sB_idleW]; exact eq_of_val' (by rw [e, tiB_val])
    · right; right; exact ksObj_B (by omega) (by omega)
  h q k hq := by
    right
    rcases HB_cases hq with ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, g1, g2, -⟩ | ⟨-, g1, g2, -⟩
    · right; left; left
      rw [sB_idleW]; exact eq_of_val' (by rw [e, tiB_val])
    · right; left; right
      rw [sB_idleScW]; exact eq_of_val' (by rw [e, sciB_val])
    · left; exact e
    · right; right; exact ksObj_B (by omega) (by omega)
    · right; right; exact ksObj_B (by omega) (by omega)
  dead q hq := by
    have hH : HB q = some (.other 12) := by
      unfold HB
      have hq' : q.val = 18446744071562084352 ∨ q.val = 18446744071562088448 ∨ q.val = 18446744071562092544 := hq
      rw [if_neg (by omega), if_neg (by omega), if_pos hq']
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun z h => ?_⟩ <;> rw [hH] at h <;> cases h
  ks _ h := by cases h
  idleOut _ h := by cases h
  dx q hq h := by
    have hq' : q.val = 18446744071562084352 ∨ q.val = 18446744071562088448 ∨ q.val = 18446744071562092544 := hq
    rcases HB_cases h with ⟨e, -⟩ | ⟨-, e⟩ | ⟨-, e⟩ | ⟨e, -⟩ | ⟨e, -⟩
    · omega
    all_goals cases e

end

end Fl4Proofs.P2.BootSt
