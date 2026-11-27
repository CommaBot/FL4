/-
P3x for virtualization (line virt, gen 24, item 3a): **`VCapped` across the extracted swaps** — `cdt.swap` (the
CNode `Swap` / `Rotate` steps' and `cap_swap_for_delete`'s core) and `cdt.cap_swap_for_delete` (the zombie path of
a deletion), at the level of FL4's extracted functions (gen 23 had only the cap-level `VCappedM.of_swap`).

FL4 source: `crates/fl4-core/src/cdt.rs` `swap(s, c1, slot1, c2, slot2)` writes `c1` into `slot2` and `c2` into
`slot1` and relinks the MDB neighbours (slot words only); `cap_swap_for_delete(s, slot1, slot2)` is a no-op on
equal slots and otherwise `swap(s, cap(slot1), slot1, cap(slot2), slot2)` (Funs.lean `cdt.cap_swap_for_delete`).

* **`swap_vcapped`**: `cdt.swap st s c1 s1 c2 s2` on two distinct MDB slots keeps `VCappedM V th` whenever each
  swapped-in cap keeps the VCPU of the cap it replaces (`hc1`: `slot1` held `Vcpu v` ⇒ `c1 = Vcpu v`; `hc2`
  likewise): from CnFrame's `swap_trace` (every other slot's cap kept, `slot2` ← `c1`, `slot1` ← `c2`). The CNode
  `Swap`/`Rotate` callers pass `update_cap_data` results, which keep `Vcpu` caps (objects.rs l. 180,
  VirtVCapped's `update_cap_data_vcpu`).
* **`swap_for_delete_vcapped`**: `cdt.cap_swap_for_delete st s s1 s2` on two MDB slots keeps `VCappedM V th`
  unconditionally (it swaps the slots' own caps; the equal-slot case writes nothing).

Hypotheses: `Placed th`, `MdbLinks th (L.mem s) G`, both slots on the MDB (`∈ G.chains.flatten`: the callers'
slots hold non-null caps), the caps' encodings well formed (`EncWf`, as `swap_trace`). Named premises: none. New file
only; no existing statement changed.
-/
import Fl4Proofs.P3.VirtVCapped
import Fl4Proofs.P3.CnFrame
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtVCappedSwap
open fl4_core Fl4Proofs.P3 Fl4Proofs.P3.VirtVCapped Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {V : Set U64} {th : TypedHeap}

/-- `VCappedM` after a cap-level swap given by its three cap facts. -/
theorem vcapped_of_swapCaps {m m' : U64 → U64} {s1 s2 : U64} {c1 c2 : capability.Cap}
    (h : VCappedM V th m) (h1 : IsSlot th s1) (h2 : IsSlot th s2)
    (hc1 : ∀ v, capV m s1 = .Vcpu v → c1 = .Vcpu v) (hc2 : ∀ v, capV m s2 = .Vcpu v → c2 = .Vcpu v)
    (hk : ∀ y, IsSlot th y → y ≠ s1 → y ≠ s2 → capV m' y = capV m y)
    (hw2 : capV m' s2 = c1) (hw1 : capV m' s1 = c2) : VCappedM V th m' :=
  VCappedM.of_caps h (fun _ h => h) fun y hy v _ hcv => by
    by_cases e1 : y = s1
    · subst e1; exact ⟨s2, h2, by rw [hw2]; exact hc1 v hcv⟩
    · by_cases e2 : y = s2
      · subst e2; exact ⟨s1, h1, by rw [hw1]; exact hc2 v hcv⟩
      · exact ⟨y, hy, (hk y hy e1 e2).trans hcv⟩

/-- **`cdt.swap` keeps `VCapped`** (module docstring). -/
theorem swap_vcapped (hP : Placed th) (s : S) (G : MdbGhost) (hM : MdbLinks th (L.mem s) G)
    {s1 s2 : U64} (h1m : s1 ∈ G.chains.flatten) (h2m : s2 ∈ G.chains.flatten) (hne : s1 ≠ s2)
    (c1 c2 : capability.Cap) (he1 : EncWf c1) (he2 : EncWf c2)
    (hc1 : ∀ v, capV (L.mem s) s1 = .Vcpu v → c1 = .Vcpu v) (hc2 : ∀ v, capV (L.mem s) s2 = .Vcpu v → c2 = .Vcpu v)
    (h : VCappedM V th (L.mem s)) :
    cdt.swap st s c1 s1 c2 s2 ⦃ s' => VCappedM V th (L.mem s') ⦄ := by
  have hs1 : IsSlot th s1 := ((hM.members _).1 h1m).1
  have hs2 : IsSlot th s2 := ((hM.members _).1 h2m).1
  exact WP.spec_mono (swap_trace hP s G hM h1m h2m hne c1 c2 he1 he2) fun _ ⟨_, hk, hw2, hw1⟩ =>
    vcapped_of_swapCaps h hs1 hs2 hc1 hc2 hk hw2 hw1

/-- **`cdt.cap_swap_for_delete` keeps `VCapped`** (module docstring). -/
theorem swap_for_delete_vcapped (hP : Placed th) (s : S) (G : MdbGhost) (hM : MdbLinks th (L.mem s) G)
    {s1 s2 : U64} (h1m : s1 ∈ G.chains.flatten) (h2m : s2 ∈ G.chains.flatten) (h : VCappedM V th (L.mem s)) :
    cdt.cap_swap_for_delete st s s1 s2 ⦃ s' => VCappedM V th (L.mem s') ⦄ := by
  unfold cdt.cap_swap_for_delete
  have heq : obj.Slot.Insts.CoreCmpPartialEqSlot.eq s1 s2 = ok (decide (s1 = s2)) := rfl
  rw [heq]
  simp only [bind_ok]
  by_cases hne : s1 = s2
  · simp only [hne, decide_true, ↓reduceIte, WP.spec_ok]
    exact h
  · simp only [hne, decide_false, Bool.false_eq_true, ↓reduceIte, slot_cap_eq, capAt_capV, bind_ok]
    have he1 : EncWf (capV (L.mem s) s1) := by
      have h := capAt_capV (L.mem s) s1; rw [capAt_words] at h; exact decode_encWf h
    have he2 : EncWf (capV (L.mem s) s2) := by
      have h := capAt_capV (L.mem s) s2; rw [capAt_words] at h; exact decode_encWf h
    exact swap_vcapped hP s G hM h1m h2m hne _ _ he1 he2 (fun v e => e) (fun v e => e) h

end

end
end Fl4Proofs.P3.VirtVCappedSwap
