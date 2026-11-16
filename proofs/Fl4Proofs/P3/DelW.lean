/-
P3 (DESIGN.md §9), CSpace: **an invariant `W` threaded through the
deletion** (the approved W-threading design). The spec's finalisation and
preemption point are nondeterministic, so a further relation (the composite
`XTop`) cannot be recovered after the deletion from its start: the loops
carry it, as `W s a σ G` beside `DState th s σ G` (`W` sees the arch state
and the ghost tree too), and each step of the deletion keeps it by a
premise:

* `FinObjHypW`, `PPHypDW`, `PostDelHypW`: `FinObjHyp`, `PPHypD`,
  `PostDelHyp` with `W` before and after (at the spec outcome they choose).
* `SlotHypW`: a slot edit of the deletion (a zombie written, a swap for
  delete, a slot emptied) keeps `W`: FL4 writes only slot words
  (`Vs.SlotFrame2`), the spec's step is `CnK`, with `DState` before and
  after and the ghost step.
* `set_zombie_frame`, `swap_for_delete_frame`, `empty_null_frame` and the
  spec's `capSwapForDelete_nkn`, `emptySlot_null_nkn`: those facts for the
  three edits.
* `FinObjHyp.w`, `PPHypD.w`, `PostDelHyp.w`, `slotHypW_true`: the premises
  at `W := True` (the plain CSpace theorems are these instances).
-/
import Fl4Proofs.P3.DelRound
import Fl4Proofs.P3.CnFrame
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-! ## The spec's slot edits are `CnK` -/

section Spec
open Fl4Spec Ipc

/-- **`cap_swap_for_delete` changes CNodes, TCBs' caps, the CDT and the
original bits only.** -/
theorem capSwapForDelete_nkn (s1 s2 : CslotPtr) : NKN (capSwapForDelete (Z := Unit) s1 s2) := by
  unfold capSwapForDelete NonDet.when
  split
  · exact nkn_bind (nkn_getCap _) (fun _ => nkn_bind (nkn_getCap _) (fun _ => capSwap_nkn _ _ _ _))
  · exact nkn_pure' _

/-- **`empty_slot` with no cleanup changes CNodes, TCBs' caps, the CDT and
the original bits only.** -/
theorem emptySlot_null_nkn (sl : CslotPtr) : NKN (emptySlot (Z := Unit) sl .nullCap) := by
  unfold emptySlot setCdt setOriginal postCapDeletion
  repeat (first | exact nkn_getCap _ | exact nkn_setCap _ _ | exact nkn_doExtendedOp _ |
    exact nkn_pure _ | exact nkn_pure' _ | exact nkn_fail | exact nkn_gets _ | exact nkn_get |
    exact nkn_assert _ | exact nkn_get_put (fun σ => ⟨rfl, fun _ => Or.inl rfl⟩) |
    exact nkn_modify (fun σ => ⟨rfl, fun _ => Or.inl rfl⟩) | (refine nkn_bind ?_ (fun _ => ?_)) |
    (apply nkn_ite) | split)

theorem mem_of_single {α : Type} {m : NonDet (State Unit) α} {σ : State Unit} {x : α × State Unit}
    (h : m σ = ({x}, False)) : x ∈ (m σ).1 := by rw [h]; rfl

end Spec

/-! ## FL4's slot edits write only slot words -/

section
variable {th : TypedHeap} {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- A slot's neighbours are null or slots: a linked slot's by the links, an
unlinked slot's are null (`DelInv`). -/
theorem nb_of (hP : Placed th) {m : U64 → U64} {G : MdbGhost} (hM : MdbLinks th m G) (hD : DelInv th m)
    {y : U64} (hy : IsSlot th y) :
    (prevOf m y = 0#u64 ∨ IsSlot th (prevOf m y)) ∧ (nextOf m y = 0#u64 ∨ IsSlot th (nextOf m y)) := by
  by_cases hm : y ∈ G.chains.flatten
  · exact hM.nb hP hm
  · have hn : capV m y = .Null := by
      by_contra hn
      exact hm ((hM.members y).2 ⟨hy, _, capAt_capV _ _, hn⟩)
    obtain ⟨h1, h2⟩ := hD.nc y hy hn
    exact ⟨Or.inl h1, Or.inl h2⟩

/-- **`cap_swap_for_delete` writes only slot words**, for any two slots. -/
theorem swap_for_delete_frame (hP : Placed th) (s : S) {G : MdbGhost} (hM : MdbLinks th (L.mem s) G)
    (hD : DelInv th (L.mem s)) {s1 s2 : U64} (h1 : IsSlot th s1) (h2 : IsSlot th s2) :
    cdt.cap_swap_for_delete st s s1 s2 ⦃ s' => Vs.SlotFrame2 (L := L) th s s' ⦄ := by
  unfold cdt.cap_swap_for_delete
  have heq : obj.Slot.Insts.CoreCmpPartialEqSlot.eq s1 s2 = ok (decide (s1 = s2)) := rfl
  rw [heq]
  simp only [bind_ok]
  by_cases hne : s1 = s2
  · simp only [hne, decide_true, ↓reduceIte, WP.spec_ok]
    exact Vs.SlotFrame2.refl s
  · simp only [hne, decide_false, Bool.false_eq_true, ↓reduceIte, slot_cap_eq, capAt_capV, bind_ok]
    have he1 : EncWf (capV (L.mem s) s1) := by
      have h := capAt_capV (L.mem s) s1; rw [capAt_words] at h; exact decode_encWf h
    have he2 : EncWf (capV (L.mem s) s2) := by
      have h := capAt_capV (L.mem s) s2; rw [capAt_words] at h; exact decode_encWf h
    obtain ⟨hP1, hN1⟩ := nb_of hP hM hD h1
    obtain ⟨hP2, hN2⟩ := nb_of hP hM hD h2
    exact swap_frame2 hP s _ _ s1 s2 h1 h2 hne hP1 hN1 hP2 hN2 he1 he2

/-- **`set_cap` of a slot writes only slot words.** -/
theorem set_zombie_frame (hP : Placed th) (s : S) {x : U64} (hx : IsSlot th x) (c : capability.Cap) :
    obj.Slot.set_cap st x s c ⦃ s' => Vs.SlotFrame2 (L := L) th s s' ⦄ :=
  set_cap_frame2 hP s x hx c

/-- **`empty_slot` with no cleanup writes only slot words.** -/
theorem empty_null_frame {A : Type} (ar : machine.Arch A) (hP : Placed th) (s : S) (a : A) {G : MdbGhost}
    (hM : MdbLinks th (L.mem s) G) (hD : DelInv th (L.mem s)) {x : U64} (hx : IsSlot th x) :
    cdt.empty_slot st ar s a x .Null ⦃ r => Vs.SlotFrame2 (L := L) th s r.1 ∧ r.2 = a ⦄ := by
  obtain ⟨hp, hn⟩ := nb_of hP hM hD hx
  exact Vs.empty_frame2 hP s a x hx _ (capAt_capV _ _) hp hn

end

/-! ## The premises with `W` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`FinObjHyp` with `W`** before and after. -/
def FinObjHypW (W : S → A → Fl4Spec.State Unit → MdbGhost → Prop) (th : TypedHeap) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (c : capability.Cap),
    DState (L := L) th s σ G → W s a σ G → AbsSlot th sl → capAt (L.mem s) (cslotAddr sl) = ok c →
    FinObjKind c →
    objects.finalise_cap st arI s a c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) false ⦃ r =>
      r.1.1 = finRem c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) ∧ CleanCap r.1.2 ∧ CapWf r.1.2 ∧
      ∃ σ' G', ((absCap r.1.1, absCap r.1.2), σ') ∈
          (Fl4Spec.finaliseCap (Z := Unit) (absCap c) (decide (Fl4Spec.isFinalCap' (absCap c) σ)) σ).1 ∧
        DState (L := L) th r.2.1 σ' G' ∧ capV (L.mem r.2.1) (cslotAddr sl) = c ∧
        (∀ y, IsSlot th y → y ≠ cslotAddr sl → capV (L.mem r.2.1) y = capV (L.mem s) y ∨
          (capV (L.mem r.2.1) y = .Null ∧ isZb (capV (L.mem s) y) = false)) ∧
        MdbStep (L.mem s) G (L.mem r.2.1) G' ∧ W r.2.1 r.2.2 σ' G' ⦄

/-- **`PPHypD` with `W`** before and after. -/
def PPHypDW (W : S → A → Fl4Spec.State Unit → MdbGhost → Prop) (th : TypedHeap) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost), DState (L := L) th s σ G → W s a σ G →
    sched.preemption_point st arI s a ⦃ r =>
      SlotsSame th (L.mem s) (L.mem r.2.1) ∧ ∃ σ',
        ((r.1 = .Ok () ∧ (.ok (), σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1) ∨
          (r.1 = .Err .Preempted ∧ (.error (), σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1)) ∧
        CRel th (L.mem r.2.1) σ' G ∧ W r.2.1 r.2.2 σ' G ⦄

/-- **`PostDelHyp` with `W`** before and after. -/
def PostDelHypW (W : S → A → Fl4Spec.State Unit → MdbGhost → Prop) (th : TypedHeap) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (cl : capability.Cap),
    DState (L := L) th s σ G → W s a σ G → CleanCap cl → cl ≠ .Null → CapWf cl →
    objects.post_cap_deletion st arI s a cl ⦃ r =>
      SlotsSame th (L.mem s) (L.mem r.1) ∧ ∃ σ',
        ((), σ') ∈ (Fl4Spec.postCapDeletion (Z := Unit) (absCap cl) σ).1 ∧ CRel th (L.mem r.1) σ' G ∧
        W r.1 r.2 σ' G ⦄

/-- **The deletion's slot edits keep `W`**: FL4 writing only slot words, the
spec's step `CnK`, `DState` before and after, with the ghost step. -/
def SlotHypW (W : S → A → Fl4Spec.State Unit → MdbGhost → Prop) (th : TypedHeap) : Prop :=
  ∀ (s s' : S) (a : A) (σ σ' : Fl4Spec.State Unit) (G G' : MdbGhost), W s a σ G →
    DState (L := L) th s σ G → DState (L := L) th s' σ' G' → Vs.SlotFrame2 (L := L) th s s' →
    Ipc.CnK σ σ' → MdbStep (L.mem s) G (L.mem s') G' → W s' a σ' G'

/-- The W-premises bundled. -/
structure DelHypsW (W : S → A → Fl4Spec.State Unit → MdbGhost → Prop) (th : TypedHeap) : Prop where
  fin : FinObjHypW (L := L) arI W th
  pp : PPHypDW (L := L) arI W th
  post : PostDelHypW (L := L) arI W th
  slot : SlotHypW (L := L) (A := A) W th

/-- `W := True`. -/
abbrev WTrue : S → A → Fl4Spec.State Unit → MdbGhost → Prop := fun _ _ _ _ => True

theorem FinObjHyp.w {th : TypedHeap} (h : FinObjHyp (L := L) arI th) : FinObjHypW (L := L) arI WTrue th := by
  intro s a σ G sl c hDS _ hA hc hk
  refine WP.spec_mono (h s a σ G sl c hDS hA hc hk) ?_
  rintro r ⟨h1, h2, h3, σ', G', h4, h5, h6, h7, h8⟩
  exact ⟨h1, h2, h3, σ', G', h4, h5, h6, h7, h8, trivial⟩

theorem PPHypD.w {th : TypedHeap} (h : PPHypD (L := L) arI th) : PPHypDW (L := L) arI WTrue th := by
  intro s a σ G hDS _
  refine WP.spec_mono (h s a σ G hDS) ?_
  rintro r ⟨h1, σ', h2, h3⟩
  exact ⟨h1, σ', h2, h3, trivial⟩

theorem PostDelHyp.w {th : TypedHeap} (h : PostDelHyp (L := L) arI th) : PostDelHypW (L := L) arI WTrue th := by
  intro s a σ G cl hDS _ h1 h2 h3
  refine WP.spec_mono (h s a σ G cl hDS h1 h2 h3) ?_
  rintro r ⟨h1, σ', h2, h3⟩
  exact ⟨h1, σ', h2, h3, trivial⟩

theorem delHypsW_true {th : TypedHeap} (hO : FinObjHyp (L := L) arI th) (hPP : PPHypD (L := L) arI th)
    (hPD : PostDelHyp (L := L) arI th) : DelHypsW (L := L) arI WTrue th :=
  ⟨hO.w arI, hPP.w arI, hPD.w arI, fun _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial⟩

end

end

end Fl4Proofs.P3
