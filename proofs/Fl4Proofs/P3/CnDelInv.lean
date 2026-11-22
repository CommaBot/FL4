/-
P3 (DESIGN.md §9), CSpace: **`DelInv` (the deletions' invariant) and the
slot operations that keep it** — the definition (used by `rec_del`'s proofs,
DelInv) and its preservation by `cdt::insert`, `cdt::move_cap` and
`cdt::swap`, the primitive steps of the CNode invocations and of the IRQ and
IO-port control inserts (StepSem's `slot`/`cslot` steps owe it).

`DelInv.of_kept`: `DelInv` after a step from the origins of its zombies (an
injective map to zombies before) and the empty slots' links.
-/
import Fl4Proofs.P3.CnFrame
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-- A well-formed zombie: over a TCB (type 65, at most 5 slots) or over a
CNode of radix `zt` (at most `2 ^ zt` slots). -/
def ZOK (th : TypedHeap) (p zt n : U64) : Prop :=
  (zt.val = 65 ∧ th p = some .tcb ∧ n.val ≤ tcbSlots) ∨
  (zt.val ≠ 65 ∧ th p = some (.cnode zt.val) ∧ n.val ≤ 2 ^ zt.val)

structure DelInv (th : TypedHeap) (mem : U64 → U64) : Prop where
  zwf : ∀ y, IsSlot th y → ∀ p zt n, capV mem y = .Zombie p zt n → ZOK th p zt n
  zu : ∀ y y', IsSlot th y → IsSlot th y' → y ≠ y' → ∀ p zt n p' zt' n',
    capV mem y = .Zombie p zt n → capV mem y' = .Zombie p' zt' n' → p ≠ p'
  nc : ∀ y, IsSlot th y → capV mem y = .Null → prevOf mem y = 0#u64 ∧ nextOf mem y = 0#u64

/-- **`DelInv` after a step from its zombies' origins**: each zombie after is
one before at `f` of its slot, `f` one-to-one on the zombies after, and the
empty slots after have clear links. -/
theorem DelInv.of_kept {th : TypedHeap} {m m' : U64 → U64} (hD : DelInv th m) (f : U64 → U64)
    (hz : ∀ y, IsSlot th y → ∀ p zt n, capV m' y = .Zombie p zt n →
      IsSlot th (f y) ∧ capV m (f y) = .Zombie p zt n)
    (hinj : ∀ y y', IsSlot th y → IsSlot th y' → y ≠ y' → ∀ p zt n p' zt' n', capV m' y = .Zombie p zt n →
      capV m' y' = .Zombie p' zt' n' → f y ≠ f y')
    (hn : ∀ y, IsSlot th y → capV m' y = .Null → prevOf m' y = 0#u64 ∧ nextOf m' y = 0#u64) : DelInv th m' :=
  ⟨fun y hy p zt n h => hD.zwf _ (hz y hy p zt n h).1 p zt n (hz y hy p zt n h).2,
    fun y y' hy hy' hne p zt n p' zt' n' h h' => hD.zu _ _ (hz y hy p zt n h).1 (hz y' hy' p' zt' n' h').1
      (hinj y y' hy hy' hne p zt n p' zt' n' h h') p zt n p' zt' n' (hz y hy p zt n h).2 (hz y' hy' p' zt' n' h').2,
    hn⟩

/-- Caps of the same shape: a zombie is its own shape. -/
theorem zombie_of_shape {c d : capability.Cap} (h : shape c = shape d) {p zt n : U64} (hc : c = .Zombie p zt n) :
    d = c := by
  subst hc
  cases d <;> simp_all [shape]

/-- `set_untyped_cap_as_full` writes an untyped cap. -/
theorem fullF_zombie {a c u : capability.Cap} (h : fullF a c = some u) {p zt n : U64} : u ≠ .Zombie p zt n := by
  rintro rfl
  cases a <;> cases c <;> simp [fullF] at h

/-- The caps naming an endpoint, a notification or a reply (the objects
`CapTyped` constrains), a frame, an EPT table, a VSpace table or (f1) PML4, or an SC
(`CapObjH`). -/
def tyObj : capability.Cap → Bool
  | .Endpoint .. => true
  | .SchedContext .. => true
  | .Notification .. => true
  | .Reply .. => true
  | .Frame .. => true
  | .Ept .. => true
  | .PageTable .. => true
  | .PageDirectory .. => true
  | .Pdpt .. => true
  | .Pml4 .. => true
  | _ => false

theorem tyObj_of_shape {c d : capability.Cap} (h : shape c = shape d) : tyObj c = tyObj d := by
  cases c <;> cases d <;> simp_all [shape, tyObj]

/-- **The slots' caps keep their objects**: each cap after names no endpoint,
notification, reply, frame or EPT table, or is of the shape of a cap before (P3's `CapTyped`
is kept, `JPlaced.slot`). -/
def TypedKept (th : TypedHeap) (m m' : U64 → U64) : Prop :=
  ∀ a, IsSlot th a → tyObj (capV m' a) = false ∨ ∃ b, IsSlot th b ∧ shape (capV m' a) = shape (capV m b)

theorem TypedKept.refl (th : TypedHeap) (m : U64 → U64) : TypedKept th m m :=
  fun a ha => Or.inr ⟨a, ha, rfl⟩

theorem TypedKept.trans {th : TypedHeap} {m1 m2 m3 : U64 → U64} (h1 : TypedKept th m1 m2) (h2 : TypedKept th m2 m3) :
    TypedKept th m1 m3 := by
  intro a ha
  rcases h2 a ha with h | ⟨b, hb, hs⟩
  · exact Or.inl h
  rcases h1 b hb with h' | ⟨c, hc, hs'⟩
  · exact Or.inl (by rw [tyObj_of_shape hs]; exact h')
  · exact Or.inr ⟨c, hc, hs.trans hs'⟩

/-- A step writing one cap `c` (of the shape of a cap before, or naming no
endpoint, notification or reply). -/
theorem typedKept_set {th : TypedHeap} {m m' : U64 → U64} {d : U64} {c : capability.Cap}
    (hcap : ∀ a, IsSlot th a → capV m' a = if a = d then c else capV m a)
    (hc : tyObj c = false ∨ ∃ b, IsSlot th b ∧ shape c = shape (capV m b)) : TypedKept th m m' := by
  intro a ha
  rw [hcap a ha]
  split_ifs
  · exact hc
  · exact Or.inr ⟨a, ha, rfl⟩

theorem fullF_tyObj {a c u : capability.Cap} (h : fullF a c = some u) : tyObj u = false := by
  unfold fullF at h
  split at h
  · split_ifs at h <;> cases h <;> rfl
  · cases h

/-- **`cdt::insert`'s caps keep their objects** (`insert_trace`'s caps). -/
theorem typedKept_ins {th : TypedHeap} {m m' : U64 → U64} {src dest : U64} {srcC c : capability.Cap}
    (hs : IsSlot th src) (hsv : capV m src = srcC)
    (hoth : ∀ y, IsSlot th y → y ≠ src → y ≠ dest → capV m' y = capV m y) (hdc : capV m' dest = c)
    (hsc : capV m' src = (fullF srcC c).getD srcC) (hsh : shape c = shape srcC) : TypedKept th m m' := by
  intro a ha
  by_cases h1 : a = dest
  · subst h1; rw [hdc]; exact Or.inr ⟨src, hs, by rw [hsv]; exact hsh⟩
  by_cases h2 : a = src
  · subst h2; rw [hsc]
    cases hf : fullF srcC c with
    | none => exact Or.inr ⟨a, hs, by rw [hsv]; rfl⟩
    | some u => exact Or.inl (fullF_tyObj hf)
  · exact Or.inr ⟨a, ha, by rw [hoth a ha h2 h1]⟩

/-- **`cdt::move_cap`'s caps keep their objects.** -/
theorem typedKept_mov {th : TypedHeap} {m m' : U64 → U64} {src dest : U64} {c : capability.Cap}
    (hs : IsSlot th src) (hoth : ∀ y, IsSlot th y → y ≠ src → y ≠ dest → capV m' y = capV m y)
    (hdc : capV m' dest = c) (hsc : capV m' src = .Null) (hsh : shape c = shape (capV m src)) :
    TypedKept th m m' := by
  intro a ha
  by_cases h1 : a = dest
  · subst h1; rw [hdc]; exact Or.inr ⟨src, hs, hsh⟩
  by_cases h2 : a = src
  · subst h2; rw [hsc]; exact Or.inl rfl
  · exact Or.inr ⟨a, ha, by rw [hoth a ha h2 h1]⟩

/-- **`cdt::swap`'s caps keep their objects.** -/
theorem typedKept_swap {th : TypedHeap} {m m' : U64 → U64} {s1 s2 : U64} {c1 c2 : capability.Cap}
    (hs1 : IsSlot th s1) (hs2 : IsSlot th s2) (hoth : ∀ y, IsSlot th y → y ≠ s1 → y ≠ s2 → capV m' y = capV m y)
    (h2c : capV m' s2 = c1) (h1c : capV m' s1 = c2) (hsh1 : shape c1 = shape (capV m s1))
    (hsh2 : shape c2 = shape (capV m s2)) : TypedKept th m m' := by
  intro a ha
  by_cases e2 : a = s2
  · subst e2; rw [h2c]; exact Or.inr ⟨s1, hs1, hsh1⟩
  by_cases e1 : a = s1
  · subst e1; rw [h1c]; exact Or.inr ⟨s2, hs2, hsh2⟩
  · exact Or.inr ⟨a, ha, by rw [hoth a ha e1 e2]⟩

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem capV_null_not_mem {th : TypedHeap} {m : U64 → U64} {G : MdbGhost} (hM : MdbLinks th m G) {y : U64}
    (h : capV m y = .Null) : y ∉ G.chains.flatten := fun hm => by
  obtain ⟨-, c0, h0, hn0⟩ := (hM.members y).1 hm
  rw [capAt_capV, h] at h0; exact hn0 (by simpa using h0.symm)

/-- **`cdt::insert` of a non-null, non-zombie cap keeps `DelInv`**, a
`set_untyped_cap_as_full` of the source included (TcbCaps' `insert_delinv`
without `fullF … = none`). -/
theorem insert_delinv_imp {th : TypedHeap} (hP : Placed th) (s : S) (G : MdbGhost) (hM : MdbLinks th (L.mem s) G)
    {src dest : U64} (hsrc : src ∈ G.chains.flatten) (hd : IsSlot th dest) (hdest : dest ∉ G.chains.flatten)
    {srcC : capability.Cap} (hsrcC : capAt (L.mem s) src = ok srcC)
    (c : capability.Cap) (he : EncWf c) (hcn : c ≠ .Null) (hzc : isZb c = false) :
    cdt.insert st s c src dest ⦃ s' => DelInv th (L.mem s) → DelInv th (L.mem s') ⦄ := by
  have hslot : ∀ x, x ∈ G.chains.flatten → IsSlot th x := fun x h => ((hM.members x).1 h).1
  have hs := hslot src hsrc
  have hne : src ≠ dest := fun e => hdest (e ▸ hsrc)
  have hes : EncWf srcC := by have h := hsrcC; rw [capAt_words] at h; exact decode_encWf h
  have hsv : capV (L.mem s) src = srcC := capV_of_capAt hsrcC
  have hsn : srcC ≠ .Null := by
    obtain ⟨-, c0, h0, hn0⟩ := (hM.members src).1 hsrc
    rw [hsrcC] at h0; rw [eq_of_ok_eq h0]; exact hn0
  have hnx : nextOf (L.mem s) src = 0#u64 ∨
      (IsSlot th (nextOf (L.mem s) src) ∧ nextOf (L.mem s) src ≠ dest ∧ nextOf (L.mem s) src ≠ src) := by
    rcases hM.next_mem hsrc with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨hslot _ h1, fun e => hdest (e ▸ h1), h2⟩
  have hNs : nextOf (L.mem s) src ≠ src := by
    rcases hnx with h | ⟨-, -, h⟩
    · rw [h]; exact (hs.ne_zero hP).symm
    · exact h
  have hNc : Canonical (nextOf (L.mem s) src) := by
    rcases hnx with h | ⟨h, -, -⟩
    · rw [h]; exact canonical_zero
    · exact h.canonical hP
  refine WP.spec_mono (WP.spec_and (insert_mem hP s c src dest hs hd hne srcC hsrcC hnx)
    (Vs.insert_trace hP s G hM hsrc hd hdest hsrcC c he)) ?_
  rintro s' ⟨hW, -, hoth, hdc, hsc⟩ hD
  refine DelInv.of_kept hD id (fun y hy p zt n h => ⟨hy, ?_⟩) (fun y y' _ _ hyy _ _ _ _ _ _ _ _ => hyy)
    (fun y hy h => ?_)
  · by_cases h1 : y = dest
    · subst h1; rw [hdc] at h; subst h; simp [isZb] at hzc
    by_cases h2 : y = src
    · subst h2
      show capV (L.mem s) y = _
      rw [hsv]; rw [hsc] at h
      cases hf : fullF srcC c with
      | none => rw [hf] at h; exact h
      | some u => rw [hf] at h; exact absurd h (fullF_zombie hf)
    · show capV (L.mem s) y = _
      rw [← hoth y hy h2 h1]; exact h
  · have hyd : y ≠ dest := fun e => by subst e; rw [hdc] at h; exact hcn h
    have hys : y ≠ src := fun e => by
      subst e; rw [hsc] at h
      cases hf : fullF srcC c with
      | none => rw [hf] at h; exact hsn h
      | some u => rw [hf] at h; exact (fullF_some hf hes).2.2 h
    rw [hoth y hy hys hyd] at h
    have hym := capV_null_not_mem hM h
    have hyn : ¬ (nextOf (L.mem s) src ≠ 0#u64 ∧ y = nextOf (L.mem s) src) := by
      rintro ⟨h0, rfl⟩
      rcases hM.next_mem hsrc with h1 | ⟨h1, -⟩
      · exact h0 h1
      · exact hym h1
    rw [hW.prevOf' hy hNs, hW.nextOf' hP hy hd hne hNc, if_neg hyd, if_neg hyn, if_neg hyd, if_neg hys]
    exact hD.nc y hy h

/-- **`cdt::move_cap` keeps `DelInv`**: the moved cap non-null and of the
source's shape (a zombie moves as it is), the source cleared. -/
theorem move_delinv_imp {th : TypedHeap} (hP : Placed th) (s : S) (G : MdbGhost) (hM : MdbLinks th (L.mem s) G)
    {src dest : U64} (hsrc : src ∈ G.chains.flatten) (hd : IsSlot th dest) (hdest : dest ∉ G.chains.flatten)
    (c : capability.Cap) (he : EncWf c) (hcn : c ≠ .Null) (hsh : shape c = shape (capV (L.mem s) src)) :
    cdt.move_cap st s c src dest ⦃ s' => DelInv th (L.mem s) → DelInv th (L.mem s') ⦄ := by
  have hslot : ∀ x, x ∈ G.chains.flatten → IsSlot th x := fun x h => ((hM.members x).1 h).1
  have hs := hslot src hsrc
  have hne : src ≠ dest := fun e => hdest (e ▸ hsrc)
  have hnx : nextOf (L.mem s) src = 0#u64 ∨
      (IsSlot th (nextOf (L.mem s) src) ∧ nextOf (L.mem s) src ≠ dest ∧ nextOf (L.mem s) src ≠ src) := by
    rcases hM.next_mem hsrc with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨hslot _ h1, fun e => hdest (e ▸ h1), h2⟩
  have hpv : prevOf (L.mem s) src = 0#u64 ∨
      (IsSlot th (prevOf (L.mem s) src) ∧ prevOf (L.mem s) src ≠ dest ∧ prevOf (L.mem s) src ≠ src) := by
    by_cases h0 : prevOf (L.mem s) src = 0#u64
    · exact Or.inl h0
    · obtain ⟨h1, h2⟩ := hM.prev_link hsrc h0
      refine Or.inr ⟨hslot _ h1, fun e => hdest (e ▸ h1), fun e => ?_⟩
      rw [e] at h2
      rcases hM.next_mem hsrc with h | ⟨-, h⟩
      · rw [h] at h2; exact hs.ne_zero hP h2.symm
      · exact h h2
  have hNc : Canonical (nextOf (L.mem s) src) := by
    rcases hnx with h | ⟨h, -, -⟩
    · rw [h]; exact canonical_zero
    · exact h.canonical hP
  refine WP.spec_mono (move_mem hP s c src dest hs hd hne hpv hnx) ?_
  intro s' hW hD
  have hcv : ∀ a, IsSlot th a → capV (L.mem s') a =
      if a = dest then c else if a = src then .Null else capV (L.mem s) a := by
    intro a ha
    have h := hW.capAt' ha he hne
    rw [capAt_capV, capAt_capV] at h
    split_ifs at h ⊢ <;> exact eq_of_ok_eq h
  refine DelInv.of_kept hD (fun y => if y = dest then src else y) (fun y hy p zt n h => ?_)
    (fun y y' hy hy' hyy p zt n p' zt' n' h h' => ?_) (fun y hy h => ?_)
  · rw [hcv y hy] at h
    by_cases h1 : y = dest
    · rw [if_pos h1] at h
      simp only [h1, ↓reduceIte]
      exact ⟨hs, by rw [zombie_of_shape hsh h]; exact h⟩
    · rw [if_neg h1] at h
      by_cases h2 : y = src
      · rw [if_pos h2] at h; cases h
      · rw [if_neg h2] at h; simp only [h1, ↓reduceIte]; exact ⟨hy, h⟩
  · have hz : ∀ x, IsSlot th x → ∀ p zt n, capV (L.mem s') x = .Zombie p zt n → x ≠ src := by
      intro x hx p zt n hz e
      rw [hcv x hx, if_neg (by rw [e]; exact hne), if_pos e] at hz; cases hz
    have h1 := hz y hy p zt n h
    have h2 := hz y' hy' p' zt' n' h'
    by_cases e1 : y = dest <;> by_cases e2 : y' = dest <;> simp only [e1, e2, ↓reduceIte]
    · exact absurd (e1.trans e2.symm) hyy
    · exact fun e => h2 e.symm
    · exact h1
    · exact hyy
  · have hyd : y ≠ dest := fun e => by rw [hcv y hy, if_pos e] at h; exact hcn h
    by_cases hys : y = src
    · rw [hW.prevOf' hy hne, hW.nextOf' hP hy hd hne hNc, if_neg hyd, if_pos hys, if_neg hyd, if_pos hys]
      exact ⟨rfl, rfl⟩
    rw [hcv y hy, if_neg hyd, if_neg hys] at h
    have hym := capV_null_not_mem hM h
    have hyn : ¬ (nextOf (L.mem s) src ≠ 0#u64 ∧ y = nextOf (L.mem s) src) := by
      rintro ⟨h0, rfl⟩
      rcases hM.next_mem hsrc with h1 | ⟨h1, -⟩
      · exact h0 h1
      · exact hym h1
    have hyp : ¬ (prevOf (L.mem s) src ≠ 0#u64 ∧ y = prevOf (L.mem s) src) := by
      rintro ⟨h0, rfl⟩
      exact hym (hM.prev_link hsrc h0).1
    rw [hW.prevOf' hy hne, hW.nextOf' hP hy hd hne hNc, if_neg hyd, if_neg hys, if_neg hyn, if_neg hyd, if_neg hys,
      if_neg hyp]
    exact hD.nc y hy h

/-- **`cdt::swap` keeps `DelInv`**: two linked slots' caps exchanged, each new
cap of the shape of the one it replaces' partner (zombies swap as they
are). -/
theorem swap_delinv_imp {th : TypedHeap} (hP : Placed th) (s : S) (G : MdbGhost) (hM : MdbLinks th (L.mem s) G)
    {s1 s2 : U64} (h1m : s1 ∈ G.chains.flatten) (h2m : s2 ∈ G.chains.flatten) (hne : s1 ≠ s2)
    (c1 c2 : capability.Cap) (he1 : EncWf c1) (he2 : EncWf c2) (hn1 : c1 ≠ .Null) (hn2 : c2 ≠ .Null)
    (hsh1 : shape c1 = shape (capV (L.mem s) s1)) (hsh2 : shape c2 = shape (capV (L.mem s) s2)) :
    cdt.swap st s c1 s1 c2 s2 ⦃ s' => DelInv th (L.mem s) → DelInv th (L.mem s') ⦄ := by
  have hs1 : IsSlot th s1 := ((hM.members _).1 h1m).1
  have hs2 : IsSlot th s2 := ((hM.members _).1 h2m).1
  obtain ⟨hP1, hN1⟩ := hM.nb hP h1m
  obtain ⟨hP2, hN2⟩ := hM.nb hP h2m
  refine WP.spec_mono (swap_fields hP s c1 c2 s1 s2 hs1 hs2 hne he1 he2 hP1 hN1 hP2 hN2) ?_
  intro s' hW hD
  have hcv : ∀ a, IsSlot th a → capV (L.mem s') a =
      if a = s2 then c1 else if a = s1 then c2 else capV (L.mem s) a := by
    intro a ha
    have h := (hW a ha).1
    rw [capAt_capV, capAt_capV] at h
    split_ifs at h ⊢ <;> exact eq_of_ok_eq h
  -- every special link value of the swap is `0`, `s1`, `s2` or a linked slot
  have hlk : ∀ x, x = 0#u64 ∨ x ∈ G.chains.flatten → ∀ y, IsSlot th y → capV (L.mem s) y = .Null → y ≠ x := by
    rintro x (rfl | hx) y hy hn rfl
    · exact hy.ne_zero hP rfl
    · exact capV_null_not_mem hM hn hx
  have hmem : ∀ x ∈ G.chains.flatten, prevOf (L.mem s) x = 0#u64 ∨ prevOf (L.mem s) x ∈ G.chains.flatten := by
    intro x hx
    by_cases h0 : prevOf (L.mem s) x = 0#u64
    · exact Or.inl h0
    · exact Or.inr (hM.prev_link hx h0).1
  have hmen : ∀ x ∈ G.chains.flatten, nextOf (L.mem s) x = 0#u64 ∨ nextOf (L.mem s) x ∈ G.chains.flatten := by
    intro x hx
    rcases hM.next_mem hx with h | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  refine DelInv.of_kept hD (fun y => if y = s2 then s1 else if y = s1 then s2 else y) (fun y hy p zt n h => ?_)
    (fun y y' hy hy' hyy p zt n p' zt' n' h h' => ?_) (fun y hy h => ?_)
  · rw [hcv y hy] at h
    by_cases e2 : y = s2
    · rw [if_pos e2] at h; simp only [e2, ↓reduceIte]
      exact ⟨hs1, by rw [zombie_of_shape hsh1 h]; exact h⟩
    · rw [if_neg e2] at h
      by_cases e1 : y = s1
      · rw [if_pos e1] at h; simp only [if_neg e2, if_pos e1]
        exact ⟨hs2, by rw [zombie_of_shape hsh2 h]; exact h⟩
      · rw [if_neg e1] at h; simp only [e2, e1, ↓reduceIte]; exact ⟨hy, h⟩
  · -- the map is a bijection (the transposition of `s1` and `s2`)
    clear hcv hW hlk hmem hmen h h'
    intro e
    apply hyy
    by_cases a2 : y = s2 <;> by_cases a1 : y = s1 <;> by_cases b2 : y' = s2 <;> by_cases b1 : y' = s1 <;>
      simp_all
  · have hy2 : y ≠ s2 := fun e => by rw [hcv y hy, if_pos e] at h; exact hn1 h
    have hy1 : y ≠ s1 := fun e => by rw [hcv y hy, if_neg hy2, if_pos e] at h; exact hn2 h
    rw [hcv y hy, if_neg hy2, if_neg hy1] at h
    have hD0 := hD.nc y hy h
    have ne : ∀ x, x = 0#u64 ∨ x ∈ G.chains.flatten → y ≠ x := fun x hx => hlk x hx y hy h
    have e1 := ne _ (hmem s1 h1m)
    have e2 := ne _ (hmen s1 h1m)
    have e3 := ne _ (hmem s2 h2m)
    have e4 := ne _ (hmen s2 h2m)
    obtain ⟨-, hpv, hnx, -, -⟩ := hW y hy
    clear hcv hW hlk hmem hmen ne hD
    try dsimp only at hpv hnx
    rw [hpv, hnx]
    constructor <;> (split_ifs <;> first | exact hD0.1 | exact hD0.2 | (exfalso; simp_all))

end

end

end Fl4Proofs.P3
