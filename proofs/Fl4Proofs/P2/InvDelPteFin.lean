/-
# P2 (line invj, generation 4): finalising and deleting a **mapped** frame cap (the CNodeDelete PTE arm)

stpost's `finCap_frame_keep` / `finImm_frame_keep` / `del_frame_keep` (P2/InvBlkFin.lean) cover a frame cap whose
finalisation makes no access (`FrNo`). For a mapped small RAM frame cap with a non-zero ASID the finalisation is the
`unmap_page` call (P2/InvDelPteRun.lean: `unmap_pte`, `unmapLeaf_st`):

* `finCap_frame_pte`: `finalise_cap` returns null remainder / cleanup at `unmap_page`'s state and Arch state;
* `finImm_frame_pte`: `finalise_slot_immediate` stops at its first round there;
* **`del_frame_pte`**: `cdt.delete` of the slot returns `Ok ()`; past `unmap_page` it writes slot words only
  (the slot's links read at `unmap_page`'s state, `hlk`).

No named premise. No existing statement changes.
-/
import Fl4Proofs.P2.InvDelPteRun
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField NullOrFrame TcbSlot
  slotOwner)

section run
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type} (ar : machine.Arch A)
variable {K : KLayout}

/-- `finalise_cap` of a mapped non-device non-EPT small frame cap with a non-zero ASID: `unmap_page`, then null
remainder and cleanup. -/
theorem finCap_frame_pte {x : S} {a : A} {fp rt asid va : U64} {fin : Bool} (hA : asid ≠ 0#u64)
    {y : (capability.Cap × capability.Cap) × S × A}
    (h : objects.finalise_cap st ar x a (.Frame fp .Small rt false true false asid va) fin false = ok y) :
    y.1 = (.Null, .Null) ∧ vspace.unmap_page st ar x a .Small asid va fp = ok (y.2.1, y.2.2) := by
  have hA' : (asid != 0#u64) = true := by simpa using hA
  unfold objects.finalise_cap objects.finalise_cap_object at h
  simp only [bind_ok, ↓reduceIte, hA', Bool.false_eq_true] at h
  obtain ⟨⟨x1, a1⟩, hu, h⟩ := bind_eq_ok h
  have e : y = ((.Null, .Null), x1, a1) := by
    cases fin <;> simp only [Bool.false_eq_true, ↓reduceIte, uncurry_apply_pair] at h <;>
      exact (ok_inj_ff h).symm
  subst e
  exact ⟨rfl, hu⟩

set_option maxHeartbeats 4000000 in
/-- **`finalise_slot_immediate` on such a frame cap returns at its first round**, at `unmap_page`'s state, with a
null cleanup. -/
theorem finImm_frame_pte {x : S} {a : A} {slot fp rt asid va : U64}
    (hc : obj.Slot.cap st slot x = ok (.Frame fp .Small rt false true false asid va)) (hA : asid ≠ 0#u64)
    {y : core.result.Result cdt.Finalised error.Exc × S × A}
    (h : cdt.finalise_slot_immediate st ar x a slot = ok y) :
    ∃ x1 a1, vspace.unmap_page st ar x a .Small asid va fp = ok (x1, a1) ∧
      y = (.Ok { success := true, cleanup := .Null }, x1, a1) := by
  unfold cdt.finalise_slot_immediate cdt.finalise_slot_immediate_loop at h
  rw [loop] at h
  obtain ⟨cf, hb, h⟩ := bind_eq_ok h
  have hf : layout.WALK_FUEL > 0#u64 := by simp [layout.WALK_FUEL, U64.rMax]
  obtain ⟨v, hv, -⟩ := spec_ex_fd (U64.sub_spec (x := layout.WALK_FUEL) (y := 1#u64)
    (by simp [layout.WALK_FUEL, U64.rMax]))
  unfold cdt.finalise_slot_immediate_loop.body at hb
  simp only [hf, ↓reduceIte, hv, bind_ok, hc, capability.Cap.is_null, Bool.false_eq_true] at hb
  obtain ⟨fin, -, hb⟩ := bind_eq_ok hb
  obtain ⟨⟨⟨rem, cl⟩, s1, a1⟩, hfc, hb⟩ := bind_eq_ok hb
  obtain ⟨e1, hu⟩ := finCap_frame_pte ar hA hfc
  simp only [Prod.mk.injEq] at e1
  obtain ⟨hr1, hr2⟩ := e1
  rw [hr1, hr2] at hb
  simp only [cdt.cap_removable, bind_ok, ↓reduceIte, uncurry_apply_pair] at hb
  rw [← ok_inj_ff hb] at h
  try dsimp only at h
  exact ⟨s1, a1, hu, (ok_inj_ff h).symm⟩

/-- **Deleting a slot that holds a mapped small RAM frame cap with a non-zero ASID** returns `Ok ()`; past
`unmap_page` it writes slot words only. -/
theorem del_frame_pte {x : S} {a : A} {dest fp rt asid va : U64} (hL : Slot8 K) (hd : dest ∈ K.slots)
    (hc : obj.Slot.cap st dest x = ok (.Frame fp .Small rt false true false asid va)) (hA : asid ≠ 0#u64)
    (hlk : ∀ x1 a1, vspace.unmap_page st ar x a .Small asid va fp = ok (x1, a1) →
      (L.mem x1 (core.num.U64.wrapping_add dest layout.cte.PREV) ≠ 0#u64 →
        L.mem x1 (core.num.U64.wrapping_add dest layout.cte.PREV) ∈ K.slots) ∧
      (∀ nx, obj.Slot.next st dest x1 = ok nx → nx ≠ 0#u64 → nx ∈ K.slots))
    {y : core.result.Result Unit error.Exc × S × A}
    (h : cdt.delete st ar x a dest true = ok y) :
    y.1 = .Ok () ∧ ∃ x1 a1, vspace.unmap_page st ar x a .Small asid va fp = ok (x1, a1) ∧
      WritesIn st x1 y.2.1 (SlotW K) := by
  unfold cdt.delete at h
  simp only [↓reduceIte] at h
  obtain ⟨⟨r, s1, a1⟩, hf, h⟩ := bind_eq_ok h
  obtain ⟨x1, a2, hu, e⟩ := finImm_frame_pte ar hc hA hf
  simp only [Prod.mk.injEq] at e
  obtain ⟨hr, hs1, ha1⟩ := e
  rw [hr, hs1, ha1] at h
  obtain ⟨cf, ecf, h⟩ := bind_eq_ok h
  try simp only [core.result.Result.Insts.CoreOpsTry.branch] at ecf
  rw [← ok_inj_ff ecf] at h
  try dsimp only at h
  obtain ⟨⟨s2, a3⟩, he, h⟩ := bind_eq_ok h
  rw [← ok_inj_ff h]
  obtain ⟨hp, hn⟩ := hlk x1 a2 hu
  exact ⟨rfl, x1, a2, hu, (emptySlot_keep ar hL hd hp hn he).1⟩

end run

end Fl4Proofs.P2.PathObl
