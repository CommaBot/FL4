/-
P3 (issue #16, F1 stage 4; F1-PLAN §4, KENTRY-PLAN f3): **`VsNamed` across the
VSpace and finalise steps, word-level generic forms.**

* `wstep k w` / `rstep k a v i` / `bnd k`: the walk's step out of entry word `w`
  of a level-`k` table (5 a pool: the word itself when non-zero and native;
  4 a PML4: `eT w` when present; 3, 2: `eT w` when present and not a large /
  huge page; 1 none), the ref it adds, and the entry bound (256 for a PML4's
  user half, else 512). `VsPath.stepW` / `VsPath.inv`: `VsPath` in that uniform
  form.
* **`VsPath.sub_new`** (master inclusion): if every ASID-table word after is
  the one before or a new pool node, every step after out of a node before is
  the one before or into a new node, and new nodes have no step after, then a
  walk after is a walk before or a new node.
* Per class (pre-state `VsNamed`; the slots fixed):
  - **`VsNamed.down`**: steps only removed (the walk words kept or cleared),
    the caps of slots `Del` deleted (unkeyed after), the other keyed caps kept,
    and every walk after named before only by deleted slots also named by a
    kept slot of the same key (`hgone`: a non-final copy, `uref`). Instances:
    **`VsNamed.shrink`** (no slot deleted: frame map / remap / unmap, PML4
    flush, the unmap halves of finalise: `delete_asid`, `delete_asid_pool`,
    `unmap_page_table` …) and **`VsNamed.delSlot`** (one slot emptied:
    `emptySlot` / `cteDelete`, finalise of a VSpace cap with its unmap).
  - **`VsNamed.mapTab`**: an unmapped table / PML4 cap's slot `y0` mapped at
    ref `(a0, v0)` and one new step into its table `q0` out of entry `i0` of a
    walk node `p0` one level up (PT / PD / PDPT map; ASID assign, `k0 = 4`, the
    pool entry).
  - **`VsNamed.unmapTab`**: a table cap with no other cap of its key made
    unmapped, its walk gone, its table empty after (table Unmap).
  - **`VsNamed.makePool`**: a fresh pool `q0` written into a zero ASID-table
    word `hi0`, its entries empty, and a pool cap at base `hi0 · 512` put into
    an unkeyed slot (MakePool).
* Site helpers: `VsNamed.unNotWalk` (an unmapped cap's table is no walk node),
  `VsPath.det` (a walk node is determined by its level and ref),
  `VsNamed.gone` (a final cap's walk is gone once the walk step at its ref is
  cleared).
-/
import Fl4Proofs.P3.VsNamedKeep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Classical

noncomputable section

/-! ## The uniform walk step -/

/-- The entry bound of a level-`k` table (a PML4's user half). -/
def bnd (k : Nat) : Nat := if k = 4 then 256 else 512

/-- The walk's step out of entry word `w` of a level-`k` table (module
docstring). -/
def wstep (k : Nat) (w : U64) : Option U64 :=
  if k = 5 then (if w ≠ 0#u64 ∧ w &&& 1#u64 = 0#u64 then some w else none)
  else if k = 4 then (if eP w then some (eT w) else none)
  else if k = 3 ∨ k = 2 then (if eP w ∧ ¬ eS w then some (eT w) else none)
  else none

/-- The ref a step out of entry `i` of a level-`k` node at ref `(a, v)` gives. -/
def rstep (k a v i : Nat) : Nat × Nat :=
  if k = 5 then (a + i, 0) else if k = 4 then (a, i * 2 ^ 39) else if k = 3 then (a, v + i * 2 ^ 30)
  else (a, v + i * 2 ^ 21)

theorem bnd_le (k : Nat) : bnd k ≤ 512 := by unfold bnd; split_ifs <;> omega

theorem wstep5 {w q : U64} : wstep 5 w = some q ↔ (w ≠ 0#u64 ∧ w &&& 1#u64 = 0#u64) ∧ w = q := by
  unfold wstep
  rw [if_pos rfl]
  by_cases h : w ≠ 0#u64 ∧ w &&& 1#u64 = 0#u64
  · rw [if_pos h]; simp only [Option.some.injEq]; exact ⟨fun e => ⟨h, e⟩, fun e => e.2⟩
  · rw [if_neg h]; simp only [reduceCtorEq, false_iff]; exact fun e => h e.1

theorem wstep4 {w q : U64} : wstep 4 w = some q ↔ eP w ∧ eT w = q := by
  unfold wstep
  rw [if_neg (by decide), if_pos rfl]
  by_cases h : eP w
  · rw [if_pos h]; simp only [Option.some.injEq]; exact ⟨fun e => ⟨h, e⟩, fun e => e.2⟩
  · rw [if_neg h]; simp only [reduceCtorEq, false_iff]; exact fun e => h e.1

theorem wstep32 {k : Nat} (hk : k = 3 ∨ k = 2) {w q : U64} :
    wstep k w = some q ↔ (eP w ∧ ¬ eS w) ∧ eT w = q := by
  unfold wstep
  rw [if_neg (by omega), if_neg (by omega), if_pos hk]
  by_cases h : eP w ∧ ¬ eS w
  · rw [if_pos h]; simp only [Option.some.injEq]; exact ⟨fun e => ⟨h, e⟩, fun e => e.2⟩
  · rw [if_neg h]; simp only [reduceCtorEq, false_iff]; exact fun e => h e.1

/-- A table entry without the present bit is no step. -/
theorem wstep_none {k : Nat} {w : U64} (hk : k ≠ 5) (h : ¬ eP w) : wstep k w = none := by
  unfold wstep
  rw [if_neg hk]
  split_ifs with h1 h2 h3 <;> first | rfl | exact absurd h2 h | exact absurd h3.1 h

/-- The zero word is no step. -/
theorem wstep_zero (k : Nat) : wstep k 0#u64 = none := by
  by_cases hk : k = 5
  · subst hk; unfold wstep; rw [if_pos rfl, if_neg (fun h => h.1 rfl)]
  · exact wstep_none hk (by simp [eP])

section
variable {m m' : U64 → U64} {ksb : U64}

/-- **A step out of a walk node is a walk node.** -/
theorem VsPath.stepW {k : Nat} {p : U64} {a v : Nat} {i q : U64} (h : VsPath m ksb k p a v) (hk2 : 2 ≤ k)
    (hk5 : k ≤ 5) (hi : i.val < bnd k) (hw : wstep k (m (peA p i)) = some q) :
    VsPath m ksb (k - 1) q (rstep k a v i.val).1 (rstep k a v i.val).2 := by
  obtain rfl | rfl | rfl | rfl : k = 5 ∨ k = 4 ∨ k = 3 ∨ k = 2 := by omega
  · obtain ⟨⟨h0, ht⟩, rfl⟩ := wstep5.1 hw
    cases h.v5
    have := VsPath.pool h (by simpa [bnd] using hi) h0 ht
    simpa [rstep] using this
  · obtain ⟨hp, rfl⟩ := wstep4.1 hw
    cases h.v4
    have := VsPath.l4 h (by simpa [bnd] using hi) hp
    simpa [rstep] using this
  · obtain ⟨⟨hp, hs⟩, rfl⟩ := (wstep32 (.inl rfl)).1 hw
    have := VsPath.l3 h (by simpa [bnd] using hi) hp hs
    simpa [rstep] using this
  · obtain ⟨⟨hp, hs⟩, rfl⟩ := (wstep32 (.inr rfl)).1 hw
    have := VsPath.l2 h (by simpa [bnd] using hi) hp hs
    simpa [rstep] using this

/-- **A walk node in the uniform form**: an ASID-table word, or a step out of
a node one level up. -/
theorem VsPath.inv {k : Nat} {q : U64} {a v : Nat} (h : VsPath m ksb k q a v) :
    (k = 5 ∧ ∃ hi : U64, hi.val < 2048 ∧ m (atA ksb hi) ≠ 0#u64 ∧ q = m (atA ksb hi) ∧ a = hi.val * 512 ∧ v = 0) ∨
    ∃ (p : U64) (a0 v0 : Nat) (i : U64), VsPath m ksb (k + 1) p a0 v0 ∧ 2 ≤ k + 1 ∧ k + 1 ≤ 5 ∧
      i.val < bnd (k + 1) ∧ wstep (k + 1) (m (peA p i)) = some q ∧ (a, v) = rstep (k + 1) a0 v0 i.val := by
  cases h with
  | tbl hh h0 => exact .inl ⟨rfl, _, hh, h0, rfl, rfl, rfl⟩
  | pool hp hl h0 ht =>
    exact .inr ⟨_, _, _, _, hp, by omega, by omega, by simpa [bnd] using hl, wstep5.2 ⟨⟨h0, ht⟩, rfl⟩,
      by simp [rstep]⟩
  | l4 hp hi he =>
    exact .inr ⟨_, _, _, _, hp, by omega, by omega, by simpa [bnd] using hi, wstep4.2 ⟨he, rfl⟩, by simp [rstep]⟩
  | l3 hp hi he hs =>
    exact .inr ⟨_, _, _, _, hp, by omega, by omega, by simpa [bnd] using hi,
      (wstep32 (.inl rfl)).2 ⟨⟨he, hs⟩, rfl⟩, by simp [rstep]⟩
  | l2 hp hi he hs =>
    exact .inr ⟨_, _, _, _, hp, by omega, by omega, by simpa [bnd] using hi,
      (wstep32 (.inr rfl)).2 ⟨⟨he, hs⟩, rfl⟩, by simp [rstep]⟩

/-- **(F1 stage 4) The master inclusion** (module docstring). -/
theorem VsPath.sub_new (New : Nat → U64 → Nat → Nat → Prop)
    (hT : ∀ hi : U64, hi.val < 2048 → m' (atA ksb hi) ≠ 0#u64 →
      m' (atA ksb hi) = m (atA ksb hi) ∨ New 5 (m' (atA ksb hi)) (hi.val * 512) 0)
    (hS : ∀ (k : Nat) (p : U64) (a v : Nat) (i q : U64), VsPath m ksb k p a v → 2 ≤ k → k ≤ 5 → i.val < bnd k →
      wstep k (m' (peA p i)) = some q →
      wstep k (m (peA p i)) = some q ∨ New (k - 1) q (rstep k a v i.val).1 (rstep k a v i.val).2)
    (hN : ∀ (k : Nat) (p : U64) (a v : Nat) (i : U64), New k p a v → 2 ≤ k → k ≤ 5 → i.val < bnd k →
      wstep k (m' (peA p i)) = none)
    {k : Nat} {q : U64} {a v : Nat} (h : VsPath m' ksb k q a v) : VsPath m ksb k q a v ∨ New k q a v := by
  have step : ∀ {k : Nat} {p : U64} {a v : Nat} {i q : U64}, (VsPath m ksb k p a v ∨ New k p a v) → 2 ≤ k →
      k ≤ 5 → i.val < bnd k → wstep k (m' (peA p i)) = some q →
      VsPath m ksb (k - 1) q (rstep k a v i.val).1 (rstep k a v i.val).2 ∨
        New (k - 1) q (rstep k a v i.val).1 (rstep k a v i.val).2 := by
    intro k p a v i q ih h2 h5 hi hw
    rcases ih with ih | ih
    · rcases hS k p a v i q ih h2 h5 hi hw with e | e
      · exact .inl (ih.stepW h2 h5 hi e)
      · exact .inr e
    · rw [hN k p a v i ih h2 h5 hi] at hw; cases hw
  induction h with
  | tbl hh h0 =>
    rcases hT _ hh h0 with e | e
    · rw [e] at h0 ⊢; exact .inl (.tbl hh h0)
    · exact .inr e
  | pool _ hl h0 ht ih =>
    have := step ih (by decide) (by decide) (by simpa [bnd] using hl) (wstep5.2 ⟨⟨h0, ht⟩, rfl⟩)
    simpa [rstep] using this
  | l4 _ hi he ih =>
    have := step ih (by decide) (by decide) (by simpa [bnd] using hi) (wstep4.2 ⟨he, rfl⟩)
    simpa [rstep] using this
  | l3 _ hi he hs ih =>
    have := step ih (by decide) (by decide) (by simpa [bnd] using hi) ((wstep32 (.inl rfl)).2 ⟨⟨he, hs⟩, rfl⟩)
    simpa [rstep] using this
  | l2 _ hi he hs ih =>
    have := step ih (by decide) (by decide) (by simpa [bnd] using hi) ((wstep32 (.inr rfl)).2 ⟨⟨he, hs⟩, rfl⟩)
    simpa [rstep] using this

/-- **Walks only removed**: the ASID-table words kept or cleared, every step
out of a walk node kept or removed. -/
theorem VsPath.sub_down
    (hT : ∀ hi : U64, hi.val < 2048 → m' (atA ksb hi) = m (atA ksb hi) ∨ m' (atA ksb hi) = 0#u64)
    (hW : ∀ (k : Nat) (p : U64) (a v : Nat) (i : U64), VsPath m ksb k p a v → 2 ≤ k → k ≤ 5 → i.val < bnd k →
      wstep k (m' (peA p i)) = wstep k (m (peA p i)) ∨ wstep k (m' (peA p i)) = none)
    {k : Nat} {q : U64} {a v : Nat} (h : VsPath m' ksb k q a v) : VsPath m ksb k q a v := by
  have := VsPath.sub_new (m := m) (fun _ _ _ _ => False) (fun hi hh h0 => by
      rcases hT hi hh with e | e
      · exact .inl e
      · exact absurd e h0)
    (fun k p a v i q hp h2 h5 hi hw => by
      rcases hW k p a v i hp h2 h5 hi with e | e
      · rw [← e]; exact .inl hw
      · rw [e] at hw; cases hw)
    (fun _ _ _ _ _ h => h.elim) h
  rcases this with h | h
  · exact h
  · exact h.elim

/-! ## Cap facts -/

theorem not_tabUn_of_ref {c : capability.Cap} {a v : Nat} (h : VRefOf c = some (true, a, v)) : ¬ TabUn c := by
  intro hu
  obtain ⟨-, a', v', h'⟩ := tabUn_iff.1 hu
  rw [h] at h'; simp at h'

theorem not_tabUn_of_vref {c : capability.Cap} {k : Nat} {q : U64} {a v : Nat} (h : VRef c k q a v) : ¬ TabUn c :=
  not_tabUn_of_ref h.2

theorem pool_key {q b : U64} : VKey (.AsidPool q b) = some (5, q) := rfl

/-- A pool cap's base is below `2^20` (`VCapW`), so its ASID-table index is in
range. -/
theorem pool_hi {P L4 L3 L2 L1 : Set U64} {q b : U64} (h : VCapW P L4 L3 L2 L1 (.AsidPool q b)) {hi : U64}
    (hib : hi.val * 512 = b.val) : hi.val < 2048 ∧ q ≠ 0#u64 := by
  simp only [VCapW, VCapOK] at h
  obtain ⟨⟨-, hq⟩, -, hb20⟩ := h
  exact ⟨by omega, hq⟩

end

/-! ## Per class -/

section Ops
variable {th : TypedHeap} {m m' : U64 → U64} {ksb : U64}

/-- **(F1 stage 4) Walks removed, some slots' caps deleted** (module
docstring). -/
theorem VsNamed.down (hN : VsNamed th m ksb) (Del : U64 → Prop)
    (hK : ∀ y, IsSlot th y → ¬ Del y → (VKey (capV m y) ≠ none ∨ VKey (capV m' y) ≠ none) → capV m' y = capV m y)
    (hD : ∀ y, IsSlot th y → Del y → VKey (capV m' y) = none)
    (hT : ∀ hi : U64, hi.val < 2048 → m' (atA ksb hi) = m (atA ksb hi) ∨ m' (atA ksb hi) = 0#u64)
    (hW : ∀ (k : Nat) (p : U64) (a v : Nat) (i : U64), VsPath m ksb k p a v → 2 ≤ k → k ≤ 5 → i.val < bnd k →
      wstep k (m' (peA p i)) = wstep k (m (peA p i)) ∨ wstep k (m' (peA p i)) = none)
    (hE : ∀ y, IsSlot th y → ¬ Del y → TabUn (capV m y) → ∀ k q, VKey (capV m y) = some (k, q) →
      ∀ i : U64, i.val < bnd k → ¬ eP (m' (peA q i)))
    (hP : ∀ y, IsSlot th y → ¬ Del y → ∀ q b, capV m y = .AsidPool q b → ∀ hi : U64, hi.val * 512 = b.val →
      m' (atA ksb hi) = q)
    (hgone : ∀ k q a v, VsPath m' ksb k q a v → ∀ y, IsSlot th y → Del y → VRef (capV m y) k q a v →
      ∃ y1, IsSlot th y1 ∧ ¬ Del y1 ∧ VKey (capV m y1) = VKey (capV m y)) :
    VsNamed th m' ksb := by
  have nd : ∀ y, IsSlot th y → VKey (capV m' y) ≠ none → ¬ Del y := fun y hy hk hd => hk (hD y hy hd)
  have kk : ∀ y, IsSlot th y → VKey (capV m' y) ≠ none → capV m' y = capV m y :=
    fun y hy hk => hK y hy (nd y hy hk) (.inr hk)
  refine ⟨fun k q a v h => ?_, fun y y' hy hy' hk hn => ?_, fun y y' hy hy' hk hu => ?_,
    fun y hy hu k q hk i hi => ?_, fun y hy q b hb hi hib => ?_⟩
  · obtain ⟨y, hy, hr⟩ := hN.named k q a v (VsPath.sub_down hT hW h)
    by_cases hd : Del y
    · obtain ⟨y1, hy1, hd1, hk1⟩ := hgone k q a v h y hy hd hr
      have hu := hN.uref y1 y hy1 hy hk1 (by rw [hk1, hr.1]; simp)
      have hc := hK y1 hy1 hd1 (.inl (by rw [hk1, hr.1]; simp))
      exact ⟨y1, hy1, by rw [hc, hk1]; exact hr.1, by rw [hc, hu]; exact hr.2⟩
    · have hc := hK y hy hd (.inl (by rw [hr.1]; simp))
      exact ⟨y, hy, by rw [hc]; exact hr⟩
  · have hn' : VKey (capV m' y') ≠ none := by rw [← hk]; exact hn
    rw [kk y hy hn, kk y' hy' hn'] at hk ⊢
    rw [kk y hy hn] at hn
    exact hN.uref y y' hy hy' hk hn
  · have hn := tabUn_key hu
    have hn' : VKey (capV m' y') ≠ none := by rw [← hk]; exact hn
    rw [kk y hy hn, kk y' hy' hn'] at hk
    rw [kk y hy hn] at hu
    exact hN.uun y y' hy hy' hk hu
  · have hn := tabUn_key hu
    have hc := kk y hy hn
    rw [hc] at hu hk
    exact hE y hy (nd y hy hn) hu k q hk i hi
  · have hn : VKey (capV m' y) ≠ none := by rw [hb]; simp [VKey]
    have hc := kk y hy hn
    rw [hc] at hb
    exact hP y hy (nd y hy hn) q b hb hi hib

/-- **(F1 stage 4) Walks removed, the keyed caps kept** (frame map / remap /
unmap, PML4 flush, the unmap halves of finalise). -/
theorem VsNamed.shrink (hN : VsNamed th m ksb)
    (hK : ∀ y, IsSlot th y → (VKey (capV m y) ≠ none ∨ VKey (capV m' y) ≠ none) → capV m' y = capV m y)
    (hT : ∀ hi : U64, hi.val < 2048 → m' (atA ksb hi) = m (atA ksb hi) ∨ m' (atA ksb hi) = 0#u64)
    (hW : ∀ (k : Nat) (p : U64) (a v : Nat) (i : U64), VsPath m ksb k p a v → 2 ≤ k → k ≤ 5 → i.val < bnd k →
      wstep k (m' (peA p i)) = wstep k (m (peA p i)) ∨ wstep k (m' (peA p i)) = none)
    (hE : ∀ y, IsSlot th y → TabUn (capV m y) → ∀ k q, VKey (capV m y) = some (k, q) →
      ∀ i : U64, i.val < bnd k → ¬ eP (m' (peA q i)))
    (hP : ∀ y, IsSlot th y → ∀ q b, capV m y = .AsidPool q b → ∀ hi : U64, hi.val * 512 = b.val →
      m' (atA ksb hi) = q) :
    VsNamed th m' ksb :=
  hN.down (fun _ => False) (fun y hy _ h => hK y hy h) (fun _ _ h => h.elim) hT hW
    (fun y hy _ => hE y hy) (fun y hy _ => hP y hy) (fun _ _ _ _ _ _ _ h => h.elim)

/-- **(F1 stage 4) One slot's cap deleted** (`emptySlot`, with a finalise's
unmap before it): every walk after named only by the deleted cap is named by
another cap of its key (a non-final cap) — for a final cap, its walk is gone. -/
theorem VsNamed.delSlot (hN : VsNamed th m ksb) {y0 : U64}
    (hK : ∀ y, IsSlot th y → y ≠ y0 → (VKey (capV m y) ≠ none ∨ VKey (capV m' y) ≠ none) → capV m' y = capV m y)
    (hD : VKey (capV m' y0) = none)
    (hT : ∀ hi : U64, hi.val < 2048 → m' (atA ksb hi) = m (atA ksb hi) ∨ m' (atA ksb hi) = 0#u64)
    (hW : ∀ (k : Nat) (p : U64) (a v : Nat) (i : U64), VsPath m ksb k p a v → 2 ≤ k → k ≤ 5 → i.val < bnd k →
      wstep k (m' (peA p i)) = wstep k (m (peA p i)) ∨ wstep k (m' (peA p i)) = none)
    (hE : ∀ y, IsSlot th y → y ≠ y0 → TabUn (capV m y) → ∀ k q, VKey (capV m y) = some (k, q) →
      ∀ i : U64, i.val < bnd k → ¬ eP (m' (peA q i)))
    (hP : ∀ y, IsSlot th y → y ≠ y0 → ∀ q b, capV m y = .AsidPool q b → ∀ hi : U64, hi.val * 512 = b.val →
      m' (atA ksb hi) = q)
    (hgone : ∀ k q a v, VsPath m' ksb k q a v → VRef (capV m y0) k q a v →
      ∃ y1, IsSlot th y1 ∧ y1 ≠ y0 ∧ VKey (capV m y1) = VKey (capV m y0)) :
    VsNamed th m' ksb :=
  hN.down (· = y0) hK (fun _ _ h => by rw [h]; exact hD) hT hW hE hP
    (fun k q a v h y _ hd hr => by subst hd; exact hgone k q a v h hr)

/-- The non-final case of `delSlot`'s `hgone`: another slot holds a cap of
the deleted cap's key. -/
theorem gone_of_copy {y0 y1 : U64} (hy1 : IsSlot th y1) (hne : y1 ≠ y0)
    (hk : VKey (capV m y1) = VKey (capV m y0)) :
    ∀ k q a v, VsPath m' ksb k q a v → VRef (capV m y0) k q a v →
      ∃ y1, IsSlot th y1 ∧ y1 ≠ y0 ∧ VKey (capV m y1) = VKey (capV m y0) :=
  fun _ _ _ _ _ _ => ⟨y1, hy1, hne, hk⟩

/-- **(F1 stage 4) A table map / ASID assign** (module docstring). The step
out of `(k0 + 1, p0, i0)` is the new one; `p0`'s walks all carry the ref
`(a1, v1)` (`uref`). -/
theorem VsNamed.mapTab {P L4 L3 L2 L1 : Set U64} (hN : VsNamed th m ksb) (hS : VsSlotsW th P L4 L3 L2 L1 m)
    {y0 : U64} (hy0 : IsSlot th y0) {k0 : Nat} {q0 : U64} {a0 v0 : Nat} (hk1 : 1 ≤ k0) (hk4 : k0 ≤ 4)
    (hu0 : TabUn (capV m y0)) (hkey0 : VKey (capV m y0) = some (k0, q0))
    (hkey1 : VKey (capV m' y0) = some (k0, q0)) (hr1 : VRefOf (capV m' y0) = some (true, a0, v0))
    (hK : ∀ y, IsSlot th y → y ≠ y0 → (VKey (capV m y) ≠ none ∨ VKey (capV m' y) ≠ none) → capV m' y = capV m y)
    {p0 i0 : U64} {a1 v1 : Nat} (hp0 : VsPath m ksb (k0 + 1) p0 a1 v1) (hi0 : i0.val < bnd (k0 + 1))
    (hw0 : wstep (k0 + 1) (m' (peA p0 i0)) = some q0) (hr0 : rstep (k0 + 1) a1 v1 i0.val = (a0, v0))
    (hT : TblSame ksb m m')
    (hW : ∀ (k : Nat) (p : U64) (a v : Nat) (i : U64), VsPath m ksb k p a v → 2 ≤ k → k ≤ 5 → i.val < bnd k →
      ¬ (k = k0 + 1 ∧ p = p0 ∧ i = i0) → wstep k (m' (peA p i)) = wstep k (m (peA p i)))
    (hE : ∀ y, IsSlot th y → TabUn (capV m y) → ∀ k q, VKey (capV m y) = some (k, q) →
      ∀ i : U64, i.val < bnd k → ¬ eP (m' (peA q i))) :
    VsNamed th m' ksb := by
  -- every walk to `p0` carries `p0`'s ref
  have href : ∀ a v, VsPath m ksb (k0 + 1) p0 a v → a = a1 ∧ v = v1 := by
    intro a v h
    obtain ⟨y, hy, hk, hr⟩ := hN.named _ _ _ _ h
    obtain ⟨y', hy', hk', hr'⟩ := hN.named _ _ _ _ hp0
    have := hN.uref y y' hy hy' (by rw [hk, hk']) (by rw [hk]; simp)
    rw [hr, hr'] at this; simp at this; exact this
  have hW' : ∀ (k : Nat) (p : U64) (a v : Nat) (i q : U64), VsPath m ksb k p a v → 2 ≤ k → k ≤ 5 →
      i.val < bnd k → wstep k (m' (peA p i)) = some q →
      wstep k (m (peA p i)) = some q ∨ (k - 1 = k0 ∧ q = q0 ∧ (rstep k a v i.val).1 = a0 ∧
        (rstep k a v i.val).2 = v0) := by
    intro k p a v i q hp h2 h5 hi hw
    by_cases e : k = k0 + 1 ∧ p = p0 ∧ i = i0
    · obtain ⟨rfl, rfl, rfl⟩ := e
      obtain ⟨rfl, rfl⟩ := href a v hp
      rw [hw0] at hw; cases hw
      exact .inr ⟨by omega, rfl, by rw [hr0], by rw [hr0]⟩
    · rw [← hW k p a v i hp h2 h5 hi e]; exact .inl hw
  have hNew : ∀ (k : Nat) (p : U64) (a v : Nat) (i : U64), (k = k0 ∧ p = q0 ∧ a = a0 ∧ v = v0) → 2 ≤ k → k ≤ 5 →
      i.val < bnd k → wstep k (m' (peA p i)) = none := by
    rintro k p a v i ⟨rfl, rfl, -, -⟩ _ _ hi
    exact wstep_none (by omega) (hE y0 hy0 hu0 _ _ hkey0 i hi)
  have hsub := fun {k q a v} (h : VsPath m' ksb k q a v) =>
    VsPath.sub_new (fun k q a v => k = k0 ∧ q = q0 ∧ a = a0 ∧ v = v0)
      (fun hi hh _ => .inl (hT hi hh)) hW' hNew h
  have hc1 : ¬ TabUn (capV m' y0) := not_tabUn_of_ref hr1
  -- a slot other than `y0` keyed after has its cap kept
  have kk : ∀ y, IsSlot th y → y ≠ y0 → VKey (capV m' y) ≠ none → capV m' y = capV m y :=
    fun y hy hne hk => hK y hy hne (.inr hk)
  -- no other slot has `y0`'s key
  have only0 : ∀ y, IsSlot th y → y ≠ y0 → VKey (capV m y) ≠ some (k0, q0) := by
    intro y hy hne hk
    exact hne (hN.uun y0 y hy0 hy (by rw [hkey0, hk]) hu0).symm
  have only1 : ∀ y, IsSlot th y → y ≠ y0 → VKey (capV m' y) ≠ some (k0, q0) := by
    intro y hy hne hk
    have hc := kk y hy hne (by rw [hk]; simp)
    rw [hc] at hk; exact only0 y hy hne hk
  refine ⟨fun k q a v h => ?_, fun y y' hy hy' hk hn => ?_, fun y y' hy hy' hk hu => ?_,
    fun y hy hu k q hk i hi => ?_, fun y hy q b hb hi hib => ?_⟩
  · rcases hsub h with h | ⟨rfl, rfl, rfl, rfl⟩
    · obtain ⟨y, hy, hr⟩ := hN.named k q a v h
      have hne : y ≠ y0 := by rintro rfl; exact not_tabUn_of_vref hr hu0
      have hc := hK y hy hne (.inl (by rw [hr.1]; simp))
      exact ⟨y, hy, by rw [hc]; exact hr⟩
    · exact ⟨y0, hy0, hkey1, hr1⟩
  · by_cases e : y = y0
    · subst e
      by_cases e' : y' = y
      · rw [e']
      · exact absurd (hk.symm.trans hkey1) (only1 y' hy' e')
    · by_cases e' : y' = y0
      · subst e'; exact absurd (hk.trans hkey1) (only1 y hy e)
      · have hn' : VKey (capV m' y') ≠ none := by rw [← hk]; exact hn
        rw [kk y hy e hn, kk y' hy' e' hn'] at hk ⊢
        rw [kk y hy e hn] at hn
        exact hN.uref y y' hy hy' hk hn
  · have e : y ≠ y0 := by rintro rfl; exact hc1 hu
    have hn := tabUn_key hu
    by_cases e' : y' = y0
    · subst e'; exact absurd (hk.trans hkey1) (only1 y hy e)
    · have hn' : VKey (capV m' y') ≠ none := by rw [← hk]; exact hn
      rw [kk y hy e hn, kk y' hy' e' hn'] at hk
      rw [kk y hy e hn] at hu
      exact hN.uun y y' hy hy' hk hu
  · have e : y ≠ y0 := by rintro rfl; exact hc1 hu
    have hc := kk y hy e (tabUn_key hu)
    rw [hc] at hu hk
    exact hE y hy hu k q hk i hi
  · have e : y ≠ y0 := by
      rintro rfl; rw [hb] at hkey1
      simp only [VKey, Option.some.injEq, Prod.mk.injEq] at hkey1
      have := hkey1.1; omega
    have hc := kk y hy e (by rw [hb]; simp [VKey])
    rw [hc] at hb
    have hcw := hS y hy
    rw [hb] at hcw
    rw [hT _ (pool_hi hcw hib).1]
    exact hN.poolT y hy q b hb hi hib

/-- **(F1 stage 4) A table Unmap** (module docstring): the cap at `y0` the only
one of its key, unmapped after, no walk to its table after, the unmapped
tables empty after. -/
theorem VsNamed.unmapTab {P L4 L3 L2 L1 : Set U64} (hN : VsNamed th m ksb) (hS : VsSlotsW th P L4 L3 L2 L1 m)
    {y0 : U64} {k0 : Nat} {q0 : U64} (hkey0 : VKey (capV m y0) = some (k0, q0))
    (huq : ∀ y, IsSlot th y → y ≠ y0 → VKey (capV m y) ≠ VKey (capV m y0))
    (hu1 : TabUn (capV m' y0)) (hkey1 : VKey (capV m' y0) = some (k0, q0))
    (hK : ∀ y, IsSlot th y → y ≠ y0 → (VKey (capV m y) ≠ none ∨ VKey (capV m' y) ≠ none) → capV m' y = capV m y)
    (hT : TblSame ksb m m')
    (hW : ∀ (k : Nat) (p : U64) (a v : Nat) (i : U64), VsPath m ksb k p a v → 2 ≤ k → k ≤ 5 → i.val < bnd k →
      wstep k (m' (peA p i)) = wstep k (m (peA p i)) ∨ wstep k (m' (peA p i)) = none)
    (hgone : ∀ a v, ¬ VsPath m' ksb k0 q0 a v)
    (hE : ∀ y, IsSlot th y → TabUn (capV m' y) → ∀ k q, VKey (capV m' y) = some (k, q) →
      ∀ i : U64, i.val < bnd k → ¬ eP (m' (peA q i))) :
    VsNamed th m' ksb := by
  have kk : ∀ y, IsSlot th y → y ≠ y0 → VKey (capV m' y) ≠ none → capV m' y = capV m y :=
    fun y hy hne hk => hK y hy hne (.inr hk)
  have only1 : ∀ y, IsSlot th y → y ≠ y0 → VKey (capV m' y) ≠ some (k0, q0) := by
    intro y hy hne hk
    have hc := kk y hy hne (by rw [hk]; simp)
    rw [hc] at hk; exact huq y hy hne (hk.trans hkey0.symm)
  refine ⟨fun k q a v h => ?_, fun y y' hy hy' hk hn => ?_, fun y y' hy hy' hk hu => ?_,
    fun y hy hu k q hk i hi => hE y hy hu k q hk i hi, fun y hy q b hb hi hib => ?_⟩
  · have h0 := VsPath.sub_down (fun hi hh => .inl (hT hi hh)) hW h
    obtain ⟨y, hy, hr⟩ := hN.named k q a v h0
    have hne : y ≠ y0 := by
      rintro rfl
      obtain ⟨hk, -⟩ := hr; rw [hkey0] at hk; simp at hk; obtain ⟨rfl, rfl⟩ := hk
      exact hgone a v h
    have hc := hK y hy hne (.inl (by rw [hr.1]; simp))
    exact ⟨y, hy, by rw [hc]; exact hr⟩
  · by_cases e : y = y0
    · subst e
      by_cases e' : y' = y
      · rw [e']
      · exact absurd (hk.symm.trans hkey1) (only1 y' hy' e')
    · by_cases e' : y' = y0
      · subst e'; exact absurd (hk.trans hkey1) (only1 y hy e)
      · have hn' : VKey (capV m' y') ≠ none := by rw [← hk]; exact hn
        rw [kk y hy e hn, kk y' hy' e' hn'] at hk ⊢
        rw [kk y hy e hn] at hn
        exact hN.uref y y' hy hy' hk hn
  · have hn := tabUn_key hu
    by_cases e : y = y0
    · subst e
      by_cases e' : y' = y
      · exact e'.symm
      · exact absurd (hk.symm.trans hkey1) (only1 y' hy' e')
    · by_cases e' : y' = y0
      · subst e'; exact absurd (hk.trans hkey1) (only1 y hy e)
      · have hn' : VKey (capV m' y') ≠ none := by rw [← hk]; exact hn
        rw [kk y hy e hn, kk y' hy' e' hn'] at hk
        rw [kk y hy e hn] at hu
        exact hN.uun y y' hy hy' hk hu
  · have e : y ≠ y0 := by rintro rfl; rw [hb] at hu1; exact hu1
    have hc := kk y hy e (by rw [hb]; simp [VKey])
    rw [hc] at hb
    have hcw := hS y hy
    rw [hb] at hcw
    rw [hT _ (pool_hi hcw hib).1]
    exact hN.poolT y hy q b hb hi hib

/-- **(F1 stage 4) MakePool** (module docstring). -/
theorem VsNamed.makePool {P L4 L3 L2 L1 : Set U64} (hN : VsNamed th m ksb) (hS : VsSlotsW th P L4 L3 L2 L1 m)
    {y0 q0 b0 hi0 : U64} (hy0 : IsSlot th y0) (hc1 : capV m' y0 = .AsidPool q0 b0) (hk0 : VKey (capV m y0) = none)
    (hb0 : b0.val = hi0.val * 512) (hhi0 : hi0.val < 2048) (hq0 : q0 ≠ 0#u64)
    (hfresh : ∀ y, IsSlot th y → VKey (capV m y) ≠ some (5, q0))
    (hK : ∀ y, IsSlot th y → y ≠ y0 → (VKey (capV m y) ≠ none ∨ VKey (capV m' y) ≠ none) → capV m' y = capV m y)
    (hT0 : m (atA ksb hi0) = 0#u64) (hT0' : m' (atA ksb hi0) = q0)
    (hT : ∀ hi : U64, hi.val < 2048 → hi ≠ hi0 → m' (atA ksb hi) = m (atA ksb hi))
    (hW : ∀ (k : Nat) (p : U64) (a v : Nat) (i : U64), VsPath m ksb k p a v → 2 ≤ k → k ≤ 5 → i.val < bnd k →
      wstep k (m' (peA p i)) = wstep k (m (peA p i)))
    (hZ : ∀ i : U64, i.val < 512 → wstep 5 (m' (peA q0 i)) = none)
    (hE : ∀ y, IsSlot th y → TabUn (capV m y) → ∀ k q, VKey (capV m y) = some (k, q) →
      ∀ i : U64, i.val < bnd k → ¬ eP (m' (peA q i))) :
    VsNamed th m' ksb := by
  have hsub := fun {k q a v} (h : VsPath m' ksb k q a v) =>
    VsPath.sub_new (fun k q a v => k = 5 ∧ q = q0 ∧ a = hi0.val * 512 ∧ v = 0)
      (fun hi hh _ => by
        by_cases e : hi = hi0
        · subst e; exact .inr ⟨rfl, hT0', rfl, rfl⟩
        · exact .inl (hT hi hh e))
      (fun k p a v i q hp h2 h5 hi hw => .inl (by rw [← hW k p a v i hp h2 h5 hi]; exact hw))
      (fun k p a v i ⟨e1, e2, _, _⟩ _ _ hi => by subst e1; subst e2; exact hZ i (by simpa [bnd] using hi)) h
  have kk : ∀ y, IsSlot th y → y ≠ y0 → VKey (capV m' y) ≠ none → capV m' y = capV m y :=
    fun y hy hne hk => hK y hy hne (.inr hk)
  have hkey1 : VKey (capV m' y0) = some (5, q0) := by rw [hc1]; rfl
  have only1 : ∀ y, IsSlot th y → y ≠ y0 → VKey (capV m' y) ≠ some (5, q0) := by
    intro y hy hne hk
    have hc := kk y hy hne (by rw [hk]; simp)
    rw [hc] at hk; exact hfresh y hy hk
  refine ⟨fun k q a v h => ?_, fun y y' hy hy' hk hn => ?_, fun y y' hy hy' hk hu => ?_,
    fun y hy hu k q hk i hi => ?_, fun y hy q b hb hi hib => ?_⟩
  · rcases hsub h with h | ⟨rfl, rfl, rfl, rfl⟩
    · obtain ⟨y, hy, hr⟩ := hN.named k q a v h
      have hne : y ≠ y0 := by
        rintro rfl; have h1 := hr.1; rw [hk0] at h1; simp at h1
      have hc := hK y hy hne (.inl (by rw [hr.1]; simp))
      exact ⟨y, hy, by rw [hc]; exact hr⟩
    · exact ⟨y0, hy0, hkey1, by rw [hc1]; simp [VRefOf, hb0]⟩
  · by_cases e : y = y0
    · subst e
      by_cases e' : y' = y
      · rw [e']
      · exact absurd (hk.symm.trans hkey1) (only1 y' hy' e')
    · by_cases e' : y' = y0
      · subst e'; exact absurd (hk.trans hkey1) (only1 y hy e)
      · have hn' : VKey (capV m' y') ≠ none := by rw [← hk]; exact hn
        rw [kk y hy e hn, kk y' hy' e' hn'] at hk ⊢
        rw [kk y hy e hn] at hn
        exact hN.uref y y' hy hy' hk hn
  · have e : y ≠ y0 := by rintro rfl; rw [hc1] at hu; exact hu
    have hn := tabUn_key hu
    by_cases e' : y' = y0
    · subst e'; exact absurd (hk.trans hkey1) (only1 y hy e)
    · have hn' : VKey (capV m' y') ≠ none := by rw [← hk]; exact hn
      rw [kk y hy e hn, kk y' hy' e' hn'] at hk
      rw [kk y hy e hn] at hu
      exact hN.uun y y' hy hy' hk hu
  · have e : y ≠ y0 := by rintro rfl; rw [hc1] at hu; exact hu
    have hc := kk y hy e (tabUn_key hu)
    rw [hc] at hu hk
    exact hE y hy hu k q hk i hi
  · by_cases e : y = y0
    · subst e
      rw [hc1] at hb; cases hb
      have : hi = hi0 := UScalar.eq_of_val_eq (by omega)
      subst this; exact hT0'
    · have hc := kk y hy e (by rw [hb]; simp [VKey])
      rw [hc] at hb
      have hcw := hS y hy
      rw [hb] at hcw
      obtain ⟨hh, hq⟩ := pool_hi hcw hib
      have hpt := hN.poolT y hy q b hb hi hib
      have hne : hi ≠ hi0 := by rintro rfl; rw [hT0] at hpt; exact hq hpt.symm
      rw [hT hi hh hne]; exact hpt

end Ops

/-! ## The deletion loop's window (KENTRY-PLAN f4 (13), f4g) -/

/-- (f4g) **`VsNamed` but at the slot `x`**, which the deletion loop empties next: every walk
node named by a slot other than `x`, and `uref` / `uun` / `empty` / `poolT` at the other
slots. `VsNamed.ofPend`: once `x` is emptied (the other slots and the walk words kept),
`VsNamed` holds. Produced at the finalisation (`VsNamed.pend`: a final cap's walk gone, or
another cap of its key; `VsPend.of_nokey` for an unkeyed cap). -/
structure VsPend (th : TypedHeap) (m : U64 → U64) (ksb : U64) (x : U64) : Prop where
  named : ∀ k q a v, VsPath m ksb k q a v → ∃ y, IsSlot th y ∧ y ≠ x ∧ VRef (capV m y) k q a v
  uref : ∀ y y', IsSlot th y → IsSlot th y' → y ≠ x → y' ≠ x → VKey (capV m y) = VKey (capV m y') →
    VKey (capV m y) ≠ none → VRefOf (capV m y) = VRefOf (capV m y')
  uun : ∀ y y', IsSlot th y → IsSlot th y' → y ≠ x → y' ≠ x → VKey (capV m y) = VKey (capV m y') →
    TabUn (capV m y) → y = y'
  empty : ∀ y, IsSlot th y → y ≠ x → TabUn (capV m y) → ∀ k q, VKey (capV m y) = some (k, q) →
    ∀ i : U64, i.val < (if k = 4 then 256 else 512) → ¬ eP (m (peA q i))
  poolT : ∀ y, IsSlot th y → y ≠ x → ∀ q b, capV m y = .AsidPool q b → ∀ hi : U64, hi.val * 512 = b.val →
    m (atA ksb hi) = q

section Pend
variable {th : TypedHeap} {m m' : U64 → U64} {ksb : U64}

/-- **(f4g) Walks removed, the slots kept, `x`'s walk gone or named by another cap of its key**:
`VsPend` at `x` (as `VsNamed.down`, the slot `x` exempt). -/
theorem VsNamed.pend (hN : VsNamed th m ksb) {x : U64}
    (hc : ∀ y, IsSlot th y → capV m' y = capV m y)
    (hT : ∀ hi : U64, hi.val < 2048 → m' (atA ksb hi) = m (atA ksb hi) ∨ m' (atA ksb hi) = 0#u64)
    (hW : ∀ (k : Nat) (p : U64) (a v : Nat) (i : U64), VsPath m ksb k p a v → 2 ≤ k → k ≤ 5 → i.val < bnd k →
      wstep k (m' (peA p i)) = wstep k (m (peA p i)) ∨ wstep k (m' (peA p i)) = none)
    (hE : ∀ y, IsSlot th y → y ≠ x → TabUn (capV m y) → ∀ k q, VKey (capV m y) = some (k, q) →
      ∀ i : U64, i.val < bnd k → ¬ eP (m' (peA q i)))
    (hP : ∀ y, IsSlot th y → y ≠ x → ∀ q b, capV m y = .AsidPool q b → ∀ hi : U64, hi.val * 512 = b.val →
      m' (atA ksb hi) = q)
    (hgone : ∀ k q a v, VsPath m' ksb k q a v → VRef (capV m x) k q a v →
      ∃ y1, IsSlot th y1 ∧ y1 ≠ x ∧ VKey (capV m y1) = VKey (capV m x)) :
    VsPend th m' ksb x := by
  refine ⟨fun k q a v h => ?_, fun y y' hy hy' _ _ hk hn => ?_, fun y y' hy hy' _ _ hk hu => ?_,
    fun y hy hyx hu k q hk i hi => ?_, fun y hy hyx q b hb hi hib => ?_⟩
  · obtain ⟨y, hy, hr⟩ := hN.named k q a v (VsPath.sub_down hT hW h)
    by_cases e : y = x
    · subst e
      obtain ⟨y1, hy1, hne, hk1⟩ := hgone k q a v h hr
      have hu := hN.uref y1 y hy1 hy hk1 (by rw [hk1, hr.1]; simp)
      exact ⟨y1, hy1, hne, by rw [hc y1 hy1, hk1]; exact hr.1, by rw [hc y1 hy1, hu]; exact hr.2⟩
    · exact ⟨y, hy, e, by rw [hc y hy]; exact hr⟩
  · rw [hc y hy, hc y' hy'] at hk ⊢; rw [hc y hy] at hn; exact hN.uref y y' hy hy' hk hn
  · rw [hc y hy, hc y' hy'] at hk; rw [hc y hy] at hu; exact hN.uun y y' hy hy' hk hu
  · rw [hc y hy] at hu hk; exact hE y hy hyx hu k q hk i (by unfold bnd; exact hi)
  · rw [hc y hy] at hb; exact hP y hy hyx q b hb hi hib

/-- `VsPend` at the state itself, `x`'s walks named by another cap of its key. -/
theorem VsNamed.pendSelf (hN : VsNamed th m ksb) {x : U64}
    (hgone : ∀ k q a v, VsPath m ksb k q a v → VRef (capV m x) k q a v →
      ∃ y1, IsSlot th y1 ∧ y1 ≠ x ∧ VKey (capV m y1) = VKey (capV m x)) :
    VsPend th m ksb x :=
  hN.pend (fun _ _ => rfl) (fun _ _ => .inl rfl) (fun _ _ _ _ _ _ _ _ _ => .inl rfl)
    (fun y hy _ hu k q hk i hi => hN.empty y hy hu k q hk i (by unfold bnd at hi; exact hi))
    (fun y hy _ => hN.poolT y hy) hgone

/-- `VsPend` at an unkeyed slot. -/
theorem VsPend.of_nokey (hN : VsNamed th m ksb) {x : U64} (hk : VKey (capV m x) = none) : VsPend th m ksb x :=
  hN.pendSelf fun _ _ _ _ _ hr => absurd (hr.1.symm.trans hk) (by simp)

/-- `VsPend` at a slot with another cap of its key (a non-final cap). -/
theorem VsPend.of_copy (hN : VsNamed th m ksb) {x y1 : U64} (hy1 : IsSlot th y1) (hne : y1 ≠ x)
    (hk : VKey (capV m y1) = VKey (capV m x)) : VsPend th m ksb x :=
  hN.pendSelf fun _ _ _ _ _ _ => ⟨y1, hy1, hne, hk⟩

end Pend

/-! ## Site helpers -/

section Help
variable {th : TypedHeap} {m : U64 → U64} {ksb : U64}

/-- **An unmapped cap's table is no walk node** at its key (`named` + `uun`). -/
theorem VsNamed.unNotWalk (hN : VsNamed th m ksb) {y : U64} (hy : IsSlot th y) (hu : TabUn (capV m y))
    {k : Nat} {q : U64} (hk : VKey (capV m y) = some (k, q)) {a v : Nat} : ¬ VsPath m ksb k q a v := by
  intro h
  obtain ⟨y', hy', hr⟩ := hN.named k q a v h
  have := hN.uun y y' hy hy' (by rw [hk, hr.1]) hu
  subst this
  exact not_tabUn_of_vref hr hu

/-- **The walks to a node carry one ref** (`named` + `uref`). -/
theorem VsNamed.ref_eq (hN : VsNamed th m ksb) {k : Nat} {q : U64} {a v a' v' : Nat}
    (h : VsPath m ksb k q a v) (h' : VsPath m ksb k q a' v') : a = a' ∧ v = v' := by
  obtain ⟨y, hy, hk, hr⟩ := hN.named _ _ _ _ h
  obtain ⟨y', hy', hk', hr'⟩ := hN.named _ _ _ _ h'
  have := hN.uref y y' hy hy' (by rw [hk, hk']) (by rw [hk]; simp)
  rw [hr, hr'] at this; simp at this; exact this

/-- The ref structure of a walk node: the vaddr prefix a multiple of the
level's span, below `2^48`. -/
def RefOK : Nat → Nat → Prop
  | 5, v => v = 0
  | 4, v => v = 0
  | 3, v => v % 2 ^ 39 = 0 ∧ v < 2 ^ 47
  | 2, v => v % 2 ^ 30 = 0 ∧ v < 2 ^ 48
  | _, v => v % 2 ^ 21 = 0 ∧ v < 2 ^ 48

theorem VsPath.refOK {k : Nat} {q : U64} {a v : Nat} (h : VsPath m ksb k q a v) : RefOK k v := by
  induction h with
  | tbl => rfl
  | pool => rfl
  | l4 _ hi _ _ => exact ⟨by omega, by omega⟩
  | l3 _ hi _ _ ih =>
    obtain ⟨h1, h2⟩ := ih
    exact ⟨by omega, by omega⟩
  | l2 _ hi _ _ ih =>
    obtain ⟨h1, h2⟩ := ih
    exact ⟨by omega, by omega⟩

theorem VsPath.base5 {q : U64} {a v : Nat} (h : VsPath m ksb 5 q a v) : a % 512 = 0 := by
  cases h; omega

/-- **A walk node is determined by its level and ref.** -/
theorem VsPath.det {k : Nat} {q q' : U64} {a v : Nat} (h : VsPath m ksb k q a v) (h' : VsPath m ksb k q' a v) :
    q = q' := by
  induction h generalizing q' with
  | @tbl hi hh h0 =>
    rcases h'.inv with ⟨-, hi', -, -, e, ha, -⟩ | ⟨p, a0, v0, i, -, -, h5, -⟩
    · have : hi = hi' := UScalar.eq_of_val_eq (by omega)
      subst this; exact e.symm
    · omega
  | @pool p b lo hp hl h0 ht ih =>
    rcases h'.inv with ⟨h5, -⟩ | ⟨p', a0, v0, i, hp', -, -, hi', hw, hr⟩
    · omega
    · have hb := hp.base5
      have hb' := hp'.base5
      have hv0 := hp'.v5
      subst hv0
      simp [rstep] at hr
      simp [bnd] at hi'
      obtain rfl : a0 = b := by omega
      have := ih (q' := p') hp'
      subst this
      have : i = lo := UScalar.eq_of_val_eq (by omega)
      subst this
      exact ((wstep5.1 hw).2)
  | @l4 p a i hp hi he ih =>
    rcases h'.inv with ⟨h5, -⟩ | ⟨p', a0, v0, i', hp', -, -, hi', hw, hr⟩
    · omega
    · have hv0 := hp'.v4
      subst hv0
      simp [rstep] at hr
      simp [bnd] at hi'
      obtain ⟨rfl, hr⟩ := hr
      have := ih (q' := p') hp'
      subst this
      have : i' = i := UScalar.eq_of_val_eq (by omega)
      subst this
      exact ((wstep4.1 hw).2)
  | @l3 p a v i hp hi he hs ih =>
    rcases h'.inv with ⟨h5, -⟩ | ⟨p', a0, v0, i', hp', -, -, hi', hw, hr⟩
    · omega
    · have r1 : RefOK 3 v := hp.refOK
      have r2 : RefOK 3 v0 := hp'.refOK
      obtain ⟨r1a, -⟩ := r1
      obtain ⟨r2a, -⟩ := r2
      simp [rstep] at hr
      simp [bnd] at hi'
      obtain ⟨rfl, hr⟩ := hr
      obtain rfl : v0 = v := by omega
      have := ih (q' := p') hp'
      subst this
      have : i' = i := UScalar.eq_of_val_eq (by omega)
      subst this
      exact (((wstep32 (.inl rfl)).1 hw).2)
  | @l2 p a v i hp hi he hs ih =>
    rcases h'.inv with ⟨h5, -⟩ | ⟨p', a0, v0, i', hp', -, -, hi', hw, hr⟩
    · omega
    · have r1 : RefOK 2 v := hp.refOK
      have r2 : RefOK 2 v0 := hp'.refOK
      obtain ⟨r1a, -⟩ := r1
      obtain ⟨r2a, -⟩ := r2
      simp [rstep] at hr
      simp [bnd] at hi'
      obtain ⟨rfl, hr⟩ := hr
      obtain rfl : v0 = v := by omega
      have := ih (q' := p') hp'
      subst this
      have : i' = i := UScalar.eq_of_val_eq (by omega)
      subst this
      exact (((wstep32 (.inr rfl)).1 hw).2)

end Help

end

end Fl4Proofs.P3.Vs
