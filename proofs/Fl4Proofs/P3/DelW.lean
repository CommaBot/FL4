/-
P3 (DESIGN.md §9), CSpace: **an invariant `W` threaded through the
deletion** (the approved W-threading design). The spec's finalisation and
preemption point are nondeterministic, so a further relation (the composite
`XTop`) cannot be recovered after the deletion from its start: the loops
carry it, as `W s a σ G` beside `DState th s σ G` (`W` sees the arch state
and the ghost tree too), and each step of the deletion keeps it by a
premise:

* `FinObjHypW`, `PPHypDW`, `PostDelHypW`: `FinObjHyp`, `PPHypD`,
  `PostDelHyp` with `W` before and after (at the spec outcome they choose);
  after a preemption, `Wp` (`WPost`: the loops stop there).
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

/-- **`PPHypD` with `W`** before and `W` after (`Wp` after a preemption). -/
def PPHypDW (W Wp : S → A → Fl4Spec.State Unit → MdbGhost → Prop) (th : TypedHeap) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost), DState (L := L) th s σ G → W s a σ G →
    sched.preemption_point st arI s a ⦃ r =>
      SlotsSame th (L.mem s) (L.mem r.2.1) ∧ ∃ σ',
        ((r.1 = .Ok () ∧ (.ok (), σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1) ∨
          (r.1 = .Err .Preempted ∧ (.error (), σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1)) ∧
        CRel th (L.mem r.2.1) σ' G ∧ WPost W Wp r.1 r.2.1 r.2.2 σ' G ⦄

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
  pp : PPHypDW (L := L) arI W W th
  post : PostDelHypW (L := L) arI W th
  slot : SlotHypW (L := L) (A := A) W th

/-- `W := True`. -/
abbrev WTrue : S → A → Fl4Spec.State Unit → MdbGhost → Prop := fun _ _ _ _ => True

theorem FinObjHyp.w {th : TypedHeap} (h : FinObjHyp (L := L) arI th) : FinObjHypW (L := L) arI WTrue th := by
  intro s a σ G sl c hDS _ hA hc hk
  refine WP.spec_mono (h s a σ G sl c hDS hA hc hk) ?_
  rintro r ⟨h1, h2, h3, σ', G', h4, h5, h6, h7, h8⟩
  exact ⟨h1, h2, h3, σ', G', h4, h5, h6, h7, h8, trivial⟩

theorem PPHypD.w {th : TypedHeap} (h : PPHypD (L := L) arI th) : PPHypDW (L := L) arI WTrue WTrue th := by
  intro s a σ G hDS _
  refine WP.spec_mono (h s a σ G hDS) ?_
  rintro r ⟨h1, σ', h2, h3⟩
  exact ⟨h1, σ', h2, h3, WPost_self.2 trivial⟩

theorem PostDelHyp.w {th : TypedHeap} (h : PostDelHyp (L := L) arI th) : PostDelHypW (L := L) arI WTrue th := by
  intro s a σ G cl hDS _ h1 h2 h3
  refine WP.spec_mono (h s a σ G cl hDS h1 h2 h3) ?_
  rintro r ⟨h1, σ', h2, h3⟩
  exact ⟨h1, σ', h2, h3, trivial⟩

theorem delHypsW_true {th : TypedHeap} (hO : FinObjHyp (L := L) arI th) (hPP : PPHypD (L := L) arI th)
    (hPD : PostDelHyp (L := L) arI th) : DelHypsW (L := L) arI WTrue th :=
  ⟨hO.w arI, hPP.w arI, hPD.w arI, fun _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial⟩

/-! ## The premises with a readiness predicate `Rd`

`SlotHypW` asks every slot edit to keep `W`, which is false for a `W` that
carries a coverage invariant (`JAtZ`'s `JCovD`): emptying the only cap of a
live object loses its cover. What makes the deletion's edits safe is a fact
about the edited slot that the loop knows at the edit: the slot's cap was
finalised just before (its objects dead or covered by another cap). The
premises below thread it as a readiness predicate `Rd s a σ G x` (the slot
`x` is ready to be emptied), produced by the finalisation and consumed by the
empty, and split `SlotHypW` by edit:

* `FinObjHypWR`: `FinObjHypW` with `Rd` at the finalised slot after.
* `RdTrivHyp`: `Rd` at the slot of a cap whose finalisation does nothing to
  the state (no object: the trivial caps, CNode caps, zombies).
* `ZombieHypW`: a zombie written over a cap alike it (`CapAlike`: the same
  range and objects), the other slots kept.
* `SwapHypW`: the zombie at a slot swapped with its first slot.
* `EmptyHypWR`: a non-null slot emptied (`empty_slot` with a null cleanup),
  the other slots kept, given `Rd` at it before.
* `DelHypsWR`: the seven premises bundled; `DelHypsW.toR`: from `DelHypsW`
  at `Rd := True` (`RdT`), so `DelHypsW` users are unchanged.

The loop empties a slot only when the finalisation's remainder is removable
(`RmOK`: null, or a zombie with no slot left but possibly its own), so
`Rd` is asked only then: `FinObjHypWRc` (`FinObjHypWR` with `Rd` under
`RmOK`), and `RdTrivHyp` given what a removable remainder says of a CNode
cap (not final, or of radix `0` in its own slot) and of a zombie (its count
`0`, or `1` in its own first slot). A final thread or CNode cap's slot is
then never asked to be ready (its remainder is a zombie still naming
slots).
-/

/-- **A removable remainder at `x`**: null, or a zombie of count `0`, or of
count `1` at its own first slot (FL4's `cap_removable`). -/
def RmOK (rem : capability.Cap) (x : U64) : Prop :=
  rem = .Null ∨ ∃ p zt n, rem = .Zombie p zt n ∧ (n.val = 0 ∨ (n.val = 1 ∧ p = x))

/-- No readiness asked. -/
abbrev RdT : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop := fun _ _ _ _ _ => True

/-- **`FinObjHypW` with `Rd`** at the finalised slot after, for the object
caps of the kinds `Kd`. -/
def FinObjHypWRK (W : S → A → Fl4Spec.State Unit → MdbGhost → Prop)
    (Rd : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop) (th : TypedHeap)
    (Kd : capability.Cap → Prop) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (c : capability.Cap),
    DState (L := L) th s σ G → W s a σ G → AbsSlot th sl → capAt (L.mem s) (cslotAddr sl) = ok c →
    FinObjKind c → Kd c →
    objects.finalise_cap st arI s a c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) false ⦃ r =>
      r.1.1 = finRem c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) ∧ CleanCap r.1.2 ∧ CapWf r.1.2 ∧
      ∃ σ' G', ((absCap r.1.1, absCap r.1.2), σ') ∈
          (Fl4Spec.finaliseCap (Z := Unit) (absCap c) (decide (Fl4Spec.isFinalCap' (absCap c) σ)) σ).1 ∧
        DState (L := L) th r.2.1 σ' G' ∧ capV (L.mem r.2.1) (cslotAddr sl) = c ∧
        (∀ y, IsSlot th y → y ≠ cslotAddr sl → capV (L.mem r.2.1) y = capV (L.mem s) y ∨
          (capV (L.mem r.2.1) y = .Null ∧ isZb (capV (L.mem s) y) = false)) ∧
        MdbStep (L.mem s) G (L.mem r.2.1) G' ∧ W r.2.1 r.2.2 σ' G' ∧ Rd r.2.1 r.2.2 σ' G' (cslotAddr sl) ⦄

/-- **`FinObjHypW` with `Rd`** at the finalised slot after, every object cap. -/
abbrev FinObjHypWR (W : S → A → Fl4Spec.State Unit → MdbGhost → Prop)
    (Rd : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop) (th : TypedHeap) : Prop :=
  FinObjHypWRK (L := L) arI W Rd th (fun _ => True)

/-- **`FinObjHypWR` with `Rd` only when the remainder is removable** (the
loop's use, module docstring). -/
def FinObjHypWRc (W : S → A → Fl4Spec.State Unit → MdbGhost → Prop)
    (Rd : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop) (th : TypedHeap) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (c : capability.Cap),
    DState (L := L) th s σ G → W s a σ G → AbsSlot th sl → capAt (L.mem s) (cslotAddr sl) = ok c →
    FinObjKind c → True →
    objects.finalise_cap st arI s a c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) false ⦃ r =>
      r.1.1 = finRem c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) ∧ CleanCap r.1.2 ∧ CapWf r.1.2 ∧
      ∃ σ' G', ((absCap r.1.1, absCap r.1.2), σ') ∈
          (Fl4Spec.finaliseCap (Z := Unit) (absCap c) (decide (Fl4Spec.isFinalCap' (absCap c) σ)) σ).1 ∧
        DState (L := L) th r.2.1 σ' G' ∧ capV (L.mem r.2.1) (cslotAddr sl) = c ∧
        (∀ y, IsSlot th y → y ≠ cslotAddr sl → capV (L.mem r.2.1) y = capV (L.mem s) y ∨
          (capV (L.mem r.2.1) y = .Null ∧ isZb (capV (L.mem s) y) = false)) ∧
        MdbStep (L.mem s) G (L.mem r.2.1) G' ∧ W r.2.1 r.2.2 σ' G' ∧
        (RmOK r.1.1 (cslotAddr sl) → Rd r.2.1 r.2.2 σ' G' (cslotAddr sl)) ⦄

/-- `FinObjHypWR` gives `FinObjHypWRc`. -/
theorem FinObjHypWRK.c {W : S → A → Fl4Spec.State Unit → MdbGhost → Prop}
    {Rd : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop} {th : TypedHeap}
    (h : FinObjHypWR (L := L) arI W Rd th) : FinObjHypWRc (L := L) arI W Rd th := by
  intro s a σ G sl c hDS hW hA hc hk _
  refine WP.spec_mono (h s a σ G sl c hDS hW hA hc hk trivial) ?_
  rintro r ⟨h1, h2, h3, σ', G', h4, h5, h6, h7, h8, h9, h10⟩
  exact ⟨h1, h2, h3, σ', G', h4, h5, h6, h7, h8, h9, fun _ => h10⟩

/-- **`Rd` at the slot of a cap finalised without effect** (not an object
cap: the trivial caps, CNode caps, zombies; their finalisation leaves the
state as it is), when the remainder is removable: a CNode cap not final (or
of radix `0` in its own slot), a zombie of count `0` (or `1` in its own
first slot). -/
def RdTrivHyp (W : S → A → Fl4Spec.State Unit → MdbGhost → Prop)
    (Rd : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop) (th : TypedHeap) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (c : capability.Cap),
    DState (L := L) th s σ G → W s a σ G → AbsSlot th sl → capAt (L.mem s) (cslotAddr sl) = ok c →
    c ≠ .Null → ¬ FinObjKind c →
    (∀ p r gs g, c = .CNode p r gs g → Fl4Spec.isFinalCap' (absCap c) σ → r.val = 0 ∧ p = cslotAddr sl) →
    (∀ p zt n, c = .Zombie p zt n → n.val = 0 ∨ (n.val = 1 ∧ p = cslotAddr sl)) →
    Rd s a σ G (cslotAddr sl)

/-- **A zombie written over a cap alike it keeps `W`** (the other slots kept,
the spec's `set_cap`, the same ghost tree). -/
def ZombieHypW (W : S → A → Fl4Spec.State Unit → MdbGhost → Prop) (th : TypedHeap) : Prop :=
  ∀ (s s' : S) (a : A) (σ σ' : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (p zt n : U64),
    W s a σ G → DState (L := L) th s σ G → DState (L := L) th s' σ' G → Vs.SlotFrame2 (L := L) th s s' →
    Fl4Spec.setCap (Z := Unit) (absCap (.Zombie p zt n)) sl σ = ({((), σ')}, False) → AbsSlot th sl →
    capV (L.mem s) (cslotAddr sl) ≠ .Null → capV (L.mem s') (cslotAddr sl) = .Zombie p zt n →
    CapAlike (.Zombie p zt n) (capV (L.mem s) (cslotAddr sl)) →
    (∀ y, IsSlot th y → y ≠ cslotAddr sl → capV (L.mem s') y = capV (L.mem s) y) →
    MdbStep (L.mem s) G (L.mem s') G → W s' a σ' G

/-- **The zombie at a slot swapped with its first slot keeps `W`** (the
spec's `cap_swap_for_delete`, the ghost tree renamed). -/
def SwapHypW (W : S → A → Fl4Spec.State Unit → MdbGhost → Prop) (th : TypedHeap) : Prop :=
  ∀ (s s' : S) (a : A) (σ σ' : Fl4Spec.State Unit) (G G' : MdbGhost) (sl : Fl4Spec.CslotPtr) (p zt n : U64),
    W s a σ G → DState (L := L) th s σ G → DState (L := L) th s' σ' G' → Vs.SlotFrame2 (L := L) th s s' →
    Fl4Spec.capSwapForDelete (Z := Unit) (homeSl p zt) sl σ = ({((), σ')}, False) → AbsSlot th sl →
    capV (L.mem s) (cslotAddr sl) = .Zombie p zt n → p ≠ cslotAddr sl →
    G' = renG G (Equiv.swap p (cslotAddr sl)) →
    (∀ y, IsSlot th y → capV (L.mem s') y = if y = cslotAddr sl then capV (L.mem s) p
      else if y = p then capV (L.mem s) (cslotAddr sl) else capV (L.mem s) y) →
    MdbStep (L.mem s) G (L.mem s') G' → W s' a σ' G'

/-- **A ready non-null slot emptied keeps `W`** (FL4's `empty_slot` with a
null cleanup, the spec's `empty_slot` with a null cleanup, the other slots
kept). -/
def EmptyHypWR (W : S → A → Fl4Spec.State Unit → MdbGhost → Prop)
    (Rd : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop) (th : TypedHeap) : Prop :=
  ∀ (s s' : S) (a : A) (σ σ' : Fl4Spec.State Unit) (G G' : MdbGhost) (sl : Fl4Spec.CslotPtr),
    W s a σ G → Rd s a σ G (cslotAddr sl) → DState (L := L) th s σ G → DState (L := L) th s' σ' G' →
    Vs.SlotFrame2 (L := L) th s s' → ((), σ') ∈ (Fl4Spec.emptySlot (Z := Unit) sl .nullCap σ).1 →
    AbsSlot th sl → capV (L.mem s) (cslotAddr sl) ≠ .Null → capV (L.mem s') (cslotAddr sl) = .Null →
    (∀ y, IsSlot th y → y ≠ cslotAddr sl → capV (L.mem s') y = capV (L.mem s) y) →
    MdbStep (L.mem s) G (L.mem s') G' → W s' a σ' G'

/-- The premises with `Rd` bundled. -/
structure DelHypsWR (W Wp : S → A → Fl4Spec.State Unit → MdbGhost → Prop)
    (Rd : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop) (th : TypedHeap) : Prop where
  fin : FinObjHypWRc (L := L) arI W Rd th
  triv : RdTrivHyp (L := L) W Rd th
  pp : PPHypDW (L := L) arI W Wp th
  post : PostDelHypW (L := L) arI W th
  zomb : ZombieHypW (L := L) (A := A) W th
  swap : SwapHypW (L := L) (A := A) W th
  empty : EmptyHypWR (L := L) W Rd th

theorem FinObjHypW.r {W : S → A → Fl4Spec.State Unit → MdbGhost → Prop} {th : TypedHeap}
    (h : FinObjHypW (L := L) arI W th) : FinObjHypWR (L := L) arI W RdT th := by
  intro s a σ G sl c hDS hW hA hc hk _
  refine WP.spec_mono (h s a σ G sl c hDS hW hA hc hk) ?_
  rintro r ⟨h1, h2, h3, σ', G', h4, h5, h6, h7, h8, h9⟩
  exact ⟨h1, h2, h3, σ', G', h4, h5, h6, h7, h8, h9, trivial⟩

/-- `SlotHypW` gives the three edits' premises. -/
theorem SlotHypW.zomb {W : S → A → Fl4Spec.State Unit → MdbGhost → Prop} {th : TypedHeap}
    (h : SlotHypW (L := L) (A := A) W th) : ZombieHypW (L := L) (A := A) W th :=
  fun s s' a σ σ' G sl _ _ _ hW hD hD' hF hsc _ _ _ _ _ hmS =>
    h s s' a σ σ' G G hW hD hD' hF (Ipc.nkn_setCap _ _ σ ((), σ') (mem_of_single hsc)) hmS

theorem SlotHypW.swap {W : S → A → Fl4Spec.State Unit → MdbGhost → Prop} {th : TypedHeap}
    (h : SlotHypW (L := L) (A := A) W th) : SwapHypW (L := L) (A := A) W th :=
  fun s s' a σ σ' G G' _ p zt _ hW hD hD' hF hsw _ _ _ _ _ hmS =>
    h s s' a σ σ' G G' hW hD hD' hF (capSwapForDelete_nkn _ _ σ ((), σ') (mem_of_single hsw)) hmS

theorem SlotHypW.empty {W : S → A → Fl4Spec.State Unit → MdbGhost → Prop} {th : TypedHeap}
    (h : SlotHypW (L := L) (A := A) W th) : EmptyHypWR (L := L) W RdT th :=
  fun s s' a σ σ' G G' _ hW _ hD hD' hF hes _ _ _ _ hmS =>
    h s s' a σ σ' G G' hW hD hD' hF (emptySlot_null_nkn _ σ ((), σ') hes) hmS

/-- **`DelHypsW` is `DelHypsWR` at `Rd := True`.** -/
theorem DelHypsW.toR {W : S → A → Fl4Spec.State Unit → MdbGhost → Prop} {th : TypedHeap}
    (h : DelHypsW (L := L) arI W th) : DelHypsWR (L := L) arI W W RdT th :=
  ⟨(h.fin.r arI).c arI, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial, h.pp, h.post, h.slot.zomb, h.slot.swap, h.slot.empty⟩

/-! ## A slot fact `Rz` from the finalisation to the zombie write

The loop writes a zombie over a non-zombie cap only right after
finalising that cap, at the state the finalisation ends in. A slot fact
`Rz` the finalisation establishes there (as `Rd` for the empty) is handed
to the zombie write: `FinObjHypWRcZ` (`FinObjHypWRc` whose post adds `Rz`
at the finalised slot), `ZombieHypWZ` (`ZombieHypW` given `Rz` at the
slot when it holds a thread cap; the loop's zombie-count write and the
caps finalised without effect discharge it vacuously), `DelHypsWRZ` (the
bundle), `DelHypsWR.toZ` (at `Rz := True`, `RzT`).
-/

/-- No slot fact handed to the zombie write. -/
abbrev RzT : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop := fun _ _ _ _ _ => True

/-- **`FinObjHypWRc` with `Rz`** at the finalised slot after. -/
def FinObjHypWRcZ (W : S → A → Fl4Spec.State Unit → MdbGhost → Prop)
    (Rd Rz : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop) (th : TypedHeap) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (c : capability.Cap),
    DState (L := L) th s σ G → W s a σ G → AbsSlot th sl → capAt (L.mem s) (cslotAddr sl) = ok c →
    FinObjKind c → True →
    objects.finalise_cap st arI s a c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) false ⦃ r =>
      r.1.1 = finRem c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) ∧ CleanCap r.1.2 ∧ CapWf r.1.2 ∧
      ∃ σ' G', ((absCap r.1.1, absCap r.1.2), σ') ∈
          (Fl4Spec.finaliseCap (Z := Unit) (absCap c) (decide (Fl4Spec.isFinalCap' (absCap c) σ)) σ).1 ∧
        DState (L := L) th r.2.1 σ' G' ∧ capV (L.mem r.2.1) (cslotAddr sl) = c ∧
        (∀ y, IsSlot th y → y ≠ cslotAddr sl → capV (L.mem r.2.1) y = capV (L.mem s) y ∨
          (capV (L.mem r.2.1) y = .Null ∧ isZb (capV (L.mem s) y) = false)) ∧
        MdbStep (L.mem s) G (L.mem r.2.1) G' ∧ W r.2.1 r.2.2 σ' G' ∧
        (RmOK r.1.1 (cslotAddr sl) → Rd r.2.1 r.2.2 σ' G' (cslotAddr sl)) ∧
        Rz r.2.1 r.2.2 σ' G' (cslotAddr sl) ⦄

/-- **`ZombieHypW` given `Rz`** at the slot when it holds a thread cap. -/
def ZombieHypWZ (W : S → A → Fl4Spec.State Unit → MdbGhost → Prop)
    (Rz : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop) (th : TypedHeap) : Prop :=
  ∀ (s s' : S) (a : A) (σ σ' : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (p zt n : U64),
    W s a σ G → (∀ q, capV (L.mem s) (cslotAddr sl) = .Thread q → Rz s a σ G (cslotAddr sl)) →
    DState (L := L) th s σ G → DState (L := L) th s' σ' G → Vs.SlotFrame2 (L := L) th s s' →
    Fl4Spec.setCap (Z := Unit) (absCap (.Zombie p zt n)) sl σ = ({((), σ')}, False) → AbsSlot th sl →
    capV (L.mem s) (cslotAddr sl) ≠ .Null → capV (L.mem s') (cslotAddr sl) = .Zombie p zt n →
    CapAlike (.Zombie p zt n) (capV (L.mem s) (cslotAddr sl)) →
    (∀ y, IsSlot th y → y ≠ cslotAddr sl → capV (L.mem s') y = capV (L.mem s) y) →
    MdbStep (L.mem s) G (L.mem s') G → W s' a σ' G

/-- The premises with `Rd` and `Rz` bundled. -/
structure DelHypsWRZ (W Wp : S → A → Fl4Spec.State Unit → MdbGhost → Prop)
    (Rd Rz : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop) (th : TypedHeap) : Prop where
  fin : FinObjHypWRcZ (L := L) arI W Rd Rz th
  triv : RdTrivHyp (L := L) W Rd th
  pp : PPHypDW (L := L) arI W Wp th
  post : PostDelHypW (L := L) arI W th
  zomb : ZombieHypWZ (L := L) (A := A) W Rz th
  swap : SwapHypW (L := L) (A := A) W th
  empty : EmptyHypWR (L := L) W Rd th

theorem FinObjHypWRc.z {W : S → A → Fl4Spec.State Unit → MdbGhost → Prop}
    {Rd : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop} {th : TypedHeap}
    (h : FinObjHypWRc (L := L) arI W Rd th) : FinObjHypWRcZ (L := L) arI W Rd RzT th := by
  intro s a σ G sl c hDS hW hA hc hk _
  refine WP.spec_mono (h s a σ G sl c hDS hW hA hc hk trivial) ?_
  rintro r ⟨h1, h2, h3, σ', G', h4, h5, h6, h7, h8, h9, h10⟩
  exact ⟨h1, h2, h3, σ', G', h4, h5, h6, h7, h8, h9, h10, trivial⟩

theorem ZombieHypW.z {W : S → A → Fl4Spec.State Unit → MdbGhost → Prop} {th : TypedHeap}
    (h : ZombieHypW (L := L) (A := A) W th) : ZombieHypWZ (L := L) (A := A) W RzT th :=
  fun s s' a σ σ' G sl p zt n hW _ => h s s' a σ σ' G sl p zt n hW

/-- **`DelHypsWR` is `DelHypsWRZ` at `Rz := True`.** -/
theorem DelHypsWR.toZ {W Wp : S → A → Fl4Spec.State Unit → MdbGhost → Prop}
    {Rd : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop} {th : TypedHeap}
    (h : DelHypsWR (L := L) arI W Wp Rd th) : DelHypsWRZ (L := L) arI W Wp Rd RzT th :=
  ⟨h.fin.z arI, h.triv, h.pp, h.post, h.zomb.z, h.swap, h.empty⟩

end

end

end Fl4Proofs.P3
