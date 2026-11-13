/-
P3 (DESIGN.md §9), CSpace: **`cdt::delete(slot, true)` refines l4v
`cap_delete`** (`rec_del (CTEDeleteCall slot True)`), scoped to the caps
whose finalisation is trivial: the slot is empty, or its cap finalises to
`(NullCap, NullCap)` without touching the state (`TrivKind`): untyped,
domain, IRQ control and scheduling control caps always; endpoint,
notification, reply, CNode, thread, scheduling context and IRQ handler caps
when they are not the final cap to their object (both FL4's
`is_final_capability` and the spec's `is_final_cap` say so). Then both
finalise in one round (no zombie, no preemption point) and empty the slot
with no cleanup (`empty_slot_refines`).

Spec side: `rec_del` is a least fixed point (`NonDet.lfp`); `lfp_two`
computes it at two points of a call path whose values do not depend on
other recursive calls (here `CTEDeleteCall` calling `FinaliseSlotCall`
once).
-/
import Fl4Proofs.P3.EmptyRefine
import Fl4Proofs.P3.CnodeCaps
import Fl4Proofs.P3.MdbFull
import Mathlib.Data.Set.Lattice.Order
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-! ## Least fixed points at a call path -/

section
open Fl4Spec

/-- The least fixed point of `F` at `i` and `j`, when `F` at `j` does not
depend on its argument and `F` at `i` depends (monotonically) only on the
argument at `j`. -/
theorem lfp_two {σ α ι : Type} (F : (ι → NonDet σ α) → ι → NonDet σ α) (i j : ι) (hij : i ≠ j) (s : σ)
    (Xi Xj : Set (α × σ) × Prop)
    (hj : ∀ f, F f j s = Xj) (hi : ∀ f, f j s = Xj → F f i s = Xi)
    (hmono : ∀ f, Xj ≤ f j s → Xi ≤ F f i s) :
    NonDet.lfp F i s = Xi ∧ NonDet.lfp F j s = Xj := by
  let S := {f : ι → σ → Set (α × σ) × Prop | ∀ k t, F f k t ≤ f k t}
  have hl : NonDet.lfp F = (sInf S : ι → σ → Set (α × σ) × Prop) := rfl
  -- an upper bound
  let fs : ι → NonDet σ α := fun k t =>
    if k = j ∧ t = s then Xj else if k = i ∧ t = s then Xi else ⊤
  have hfsj : fs j s = Xj := by simp [fs]
  have hfsi : fs i s = Xi := by simp [fs, hij]
  have hfs : (fs : ι → σ → Set (α × σ) × Prop) ∈ S := by
    intro k t
    by_cases h1 : k = j ∧ t = s
    · obtain ⟨rfl, rfl⟩ := h1; exact (hj fs).le.trans hfsj.ge
    · by_cases h2 : k = i ∧ t = s
      · obtain ⟨rfl, rfl⟩ := h2; exact (hi fs hfsj).le.trans hfsi.ge
      · show F fs k t ≤ (if k = j ∧ t = s then Xj else if k = i ∧ t = s then Xi else ⊤)
        simp only [h1, h2, ↓reduceIte]; exact le_top
  have hup : (sInf S : ι → σ → Set (α × σ) × Prop) ≤ fs := sInf_le hfs
  -- a lower bound
  let g : ι → σ → Set (α × σ) × Prop := fun k t =>
    if k = j ∧ t = s then Xj else if k = i ∧ t = s then Xi else ⊥
  have hlow : g ≤ (sInf S : ι → σ → Set (α × σ) × Prop) := by
    apply le_sInf
    intro f hf k t
    by_cases h1 : k = j ∧ t = s
    · obtain ⟨rfl, rfl⟩ := h1; simp only [g, and_self, ↓reduceIte]; exact (hj f).ge.trans (hf _ _)
    · by_cases h2 : k = i ∧ t = s
      · obtain ⟨rfl, rfl⟩ := h2
        have h1' : ¬ k = j := fun e => h1 ⟨e, rfl⟩
        simp only [g, h1', false_and, and_self, ↓reduceIte]
        exact le_trans (hmono f ((hj f).ge.trans (hf _ _))) (hf _ _)
      · simp only [g, h1, h2, ↓reduceIte]; exact bot_le
  rw [hl]
  constructor
  · apply le_antisymm
    · exact (hup i s).trans hfsi.le
    · have := hlow i s; simpa [g, hij] using this
  · apply le_antisymm
    · exact (hup j s).trans hfsj.le
    · have := hlow j s; simpa [g] using this

theorem nd_bind_mono_at {σ α β : Type} {m m' : NonDet σ α} {s : σ} (h : m s ≤ m' s) (f : α → NonDet σ β) :
    NonDet.bind m f s ≤ NonDet.bind m' f s := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun r ⟨x, hx, hr⟩ => ⟨x, h1 hx, hr⟩, ?_⟩
  rintro (h | ⟨x, hx, hr⟩)
  · exact Or.inl (h2 h)
  · exact Or.inr ⟨x, h1 hx, hr⟩

end

/-! ## The spec's trivial finalisation -/

/-- The caps whose finalisation is trivial: always, or when not final
(`fin` is FL4's `is_final_capability`, which must then agree with the
spec's `is_final_cap`). -/
def TrivKind (σ : Fl4Spec.State Unit) (c : capability.Cap) (fin : Bool) : Prop :=
  match c with
  | .Untyped .. | .Domain | .IrqControl | .SchedControl _ => True
  | .Endpoint .. | .Notification .. | .Reply .. | .CNode .. | .Thread _ | .SchedContext .. | .IrqHandler _ =>
      fin = false ∧ ¬ Fl4Spec.isFinalCap' (absCap c) σ
  | _ => False

section
variable {σ α β : Type}
theorem ndp_bind (a : α) (f : α → Fl4Spec.NonDet σ β) : Fl4Spec.NonDet.bind (Fl4Spec.NonDet.pure a) f = f a :=
  nd_pure_bind a f
theorem ndp_bind' (a : α) (f : α → Fl4Spec.NonDet σ β) : (Fl4Spec.NonDet.pure a >>= f) = f a :=
  nd_pure_bind a f
end

theorem finaliseCap_triv (σ : Fl4Spec.State Unit) (c : capability.Cap) (fin : Bool) (h : TrivKind σ c fin) :
    Fl4Spec.finaliseCap (Z := Unit) (absCap c) (decide (Fl4Spec.isFinalCap' (absCap c) σ)) σ =
      ({((.nullCap, .nullCap), σ)}, False) := by
  cases c <;> simp only [TrivKind] at h
  all_goals first
    | (simp only [absCap, Fl4Spec.finaliseCap]; rfl)
    | (obtain ⟨-, hf⟩ := h
       simp only [hf, decide_false]
       simp only [absCap, Fl4Spec.finaliseCap, Fl4Spec.NonDet.liftM, Fl4Spec.NonDet.when, Bool.false_eq_true,
         ↓reduceIte, ndp_bind, ndp_bind']
       rfl)

/-! ## `rec_del` on the trivial path -/

section
variable {σ ε α β : Type}

theorem run_liftE_st {m : Fl4Spec.NonDet σ α} {s s' : σ} {a : α} (h : m s = ({(a, s')}, False)) :
    (Fl4Spec.NonDetE.liftE (ε := ε) m).run s = ({(.ok a, s')}, False) := by
  unfold Fl4Spec.NonDetE.liftE
  rw [ExceptT.run_lift]
  show (m >>= _) s = _
  rw [nd_bind_one h]; rfl

theorem run_bind_ok_st {m : Fl4Spec.NonDetE σ ε α} {s s' : σ} {a : α} (h : m.run s = ({(.ok a, s')}, False))
    (f : α → Fl4Spec.NonDetE σ ε β) : (m >>= f).run s = (f a).run s' := by
  rw [ExceptT.run_bind, nd_bind_one h]

end

theorem absCap_eq_null {c : capability.Cap} : absCap c = .nullCap ↔ c = .Null := by
  cases c <;> simp [absCap]

/-- The spec's `finalise_slot` on an empty slot or a trivially finalised
cap: success, no cleanup, state unchanged (no recursive call). -/
theorem recDelF_fin (f : Fl4Spec.RecDelCall → Fl4Spec.PMonad Unit (Bool × Fl4Spec.Cap)) (sl : Fl4Spec.CslotPtr)
    (e : Bool) (σ : Fl4Spec.State Unit) {a : Fl4Spec.Cap}
    (hg : Fl4Spec.getCap (Z := Unit) sl σ = ({(a, σ)}, False))
    (ha : a = .nullCap ∨ ∃ c fin, a = absCap c ∧ c ≠ .Null ∧ TrivKind σ c fin) :
    (Fl4Spec.recDelF f (.finaliseSlotCall sl e)).run σ = ({(.ok (true, .nullCap), σ)}, False) := by
  unfold Fl4Spec.recDelF Fl4Spec.withoutPreemption
  rw [run_bind_ok (run_liftE hg)]
  rcases ha with rfl | ⟨c, fin, rfl, hcn, ht⟩
  · simp only [↓reduceIte]; rfl
  · have hn : absCap c ≠ .nullCap := fun h => hcn (absCap_eq_null.1 h)
    simp only [hn, ↓reduceIte]
    rw [run_bind_ok (run_liftE (m := Fl4Spec.isFinalCap (Z := Unit) (absCap c)) rfl)]
    rw [run_bind_ok (run_liftE (finaliseCap_triv σ c fin ht))]
    simp only [Fl4Spec.capRemoveable, ↓reduceIte]; rfl

/-- The spec's `cte_delete` round after a trivial `finalise_slot`: empty
the slot. -/
theorem recDelF_cte (f : Fl4Spec.RecDelCall → Fl4Spec.PMonad Unit (Bool × Fl4Spec.Cap)) (sl : Fl4Spec.CslotPtr)
    (σ σ' : Fl4Spec.State Unit)
    (hf : (f (.finaliseSlotCall sl true)).run σ = ({(.ok (true, .nullCap), σ)}, False))
    (he : Fl4Spec.emptySlot (Z := Unit) sl .nullCap σ = ({((), σ')}, False)) :
    (Fl4Spec.recDelF f (.cTEDeleteCall sl true)).run σ = ({(.ok Fl4Spec.undefined, σ')}, False) := by
  unfold Fl4Spec.recDelF Fl4Spec.withoutPreemption
  rw [run_bind_ok hf]
  simp only [true_or, Fl4Spec.NonDet.when, ↓reduceIte]
  rw [run_bind_ok_st (run_liftE_st he)]
  rfl

/-- **The spec's `cap_delete` on a trivially finalised slot** is
`empty_slot slot NullCap`. -/
theorem capDelete_triv (sl : Fl4Spec.CslotPtr) (σ σ' : Fl4Spec.State Unit) {a : Fl4Spec.Cap}
    (hg : Fl4Spec.getCap (Z := Unit) sl σ = ({(a, σ)}, False))
    (ha : a = .nullCap ∨ ∃ c fin, a = absCap c ∧ c ≠ .Null ∧ TrivKind σ c fin)
    (he : Fl4Spec.emptySlot (Z := Unit) sl .nullCap σ = ({((), σ')}, False)) :
    (Fl4Spec.capDelete (Z := Unit) sl).run σ = ({(.ok (), σ')}, False) := by
  let F : (Fl4Spec.RecDelCall → Fl4Spec.NonDet (Fl4Spec.State Unit) (Except Unit (Bool × Fl4Spec.Cap))) →
      Fl4Spec.RecDelCall → Fl4Spec.NonDet (Fl4Spec.State Unit) (Except Unit (Bool × Fl4Spec.Cap)) :=
    fun r c => Fl4Spec.recDelF r c
  let Xf : Set (Except Unit (Bool × Fl4Spec.Cap) × Fl4Spec.State Unit) × Prop :=
    ({(.ok (true, .nullCap), σ)}, False)
  let Xc : Set (Except Unit (Bool × Fl4Spec.Cap) × Fl4Spec.State Unit) × Prop :=
    ({(.ok Fl4Spec.undefined, σ')}, False)
  have hl := lfp_two F (.cTEDeleteCall sl true) (.finaliseSlotCall sl true) (by intro h; cases h) σ Xc Xf
    (fun f => recDelF_fin f sl true σ hg ha) (fun f hf => recDelF_cte f sl σ σ' hf he) (by
      intro f h
      let f0 : Fl4Spec.RecDelCall → Fl4Spec.PMonad Unit (Bool × Fl4Spec.Cap) := fun _ => ExceptT.mk (fun _ => Xf)
      have h0 : (Fl4Spec.recDelF f0 (.cTEDeleteCall sl true)).run σ = Xc := recDelF_cte f0 sl σ σ' rfl he
      show Xc ≤ (Fl4Spec.recDelF f (.cTEDeleteCall sl true)).run σ
      rw [← h0]
      unfold Fl4Spec.recDelF
      exact nd_bind_mono_at h _)
  have hr : (Fl4Spec.recDel (Z := Unit) (.cTEDeleteCall sl true)).run σ = Xc := hl.1
  unfold Fl4Spec.capDelete
  rw [run_bind_ok_st hr]; rfl

/-! ## FL4's trivial finalisation -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

theorem finalise_cap_triv (σ : Fl4Spec.State Unit) (s : S) (a : A) (c : capability.Cap) (fin : Bool)
    (h : TrivKind σ c fin) :
    objects.finalise_cap st arI s a c fin false = ok ((.Null, .Null), s, a) := by
  cases c <;> simp only [TrivKind] at h
  all_goals first
    | (obtain ⟨rfl, -⟩ := h
       simp [objects.finalise_cap, objects.finalise_cap_object])
    | simp [objects.finalise_cap, objects.finalise_cap_object]

/-- One round of `finalise_slot_immediate` on an empty or trivially
finalised slot: success, no cleanup, state unchanged. -/
theorem finalise_imm_triv (σ : Fl4Spec.State Unit) (s : S) (a : A) (slot : obj.Slot) (c : capability.Cap)
    (hc : capAt (L.mem s) slot = ok c)
    (ht : c = .Null ∨ ∃ fin, cdt.is_final_capability st s slot = ok fin ∧ TrivKind σ c fin) :
    cdt.finalise_slot_immediate st arI s a slot =
      ok (.Ok { success := true, cleanup := .Null }, s, a) := by
  unfold cdt.finalise_slot_immediate cdt.finalise_slot_immediate_loop
  rw [loop]
  have hf : layout.WALK_FUEL > 0#u64 := by simp [layout.WALK_FUEL, U64.rMax]
  obtain ⟨v, hv, -⟩ := spec_exists (U64.sub_spec (x := layout.WALK_FUEL) (y := 1#u64) (by simp [layout.WALK_FUEL, U64.rMax]))
  unfold cdt.finalise_slot_immediate_loop.body
  simp only [hf, ↓reduceIte, hv, bind_ok, slot_cap_eq, hc]
  rcases ht with rfl | ⟨fin, hfin, htk⟩
  · simp only [cap_is_null_null, bind_ok, ↓reduceIte]
  · have hcn : c ≠ .Null := by intro e; subst e; simp [TrivKind] at htk
    rw [cap_is_null_ne hcn]
    simp only [bind_ok, Bool.false_eq_true, ↓reduceIte, hfin, finalise_cap_triv arI σ s a c fin htk,
      uncurry_apply_pair, cdt.cap_removable]

theorem empty_slot_null (s : S) (a : A) (slot : obj.Slot) (hc : capAt (L.mem s) slot = ok .Null) (cl : capability.Cap) :
    cdt.empty_slot st arI s a slot cl = ok (s, a) := by
  unfold cdt.empty_slot
  simp only [slot_cap_eq, hc, bind_ok, cap_is_null_null, ↓reduceIte]

/-- **`delete(slot, true)` refines l4v `cap_delete slot`** for a CNode
slot that is empty or holds a trivially finalised cap (`TrivKind`): FL4
returns `Ok`, and the state is related to the spec's single outcome. -/
theorem delete_refines (th : TypedHeap) (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    {px : U64} {rx : Nat} (hpx : th px = some (.cnode rx)) {idx : List Bool} (hl : idx.length = rx)
    {c : capability.Cap} (hc : capAt (L.mem s) (cslotAddr (px.bv, idx)) = ok c)
    (ht : c = .Null ∨ ∃ fin, cdt.is_final_capability st s (cslotAddr (px.bv, idx)) = ok fin ∧ TrivKind σ c fin) :
    cdt.delete st arI s a (cslotAddr (px.bv, idx)) true ⦃ r => r.1 = .Ok () ∧
      ∃ σ' G', (Fl4Spec.capDelete (Z := Unit) (px.bv, idx)).run σ = ({(.ok (), σ')}, False) ∧
        StateRel th (L.mem r.2.1) σ' ∧ SlotsValid th (L.mem r.2.1) ∧ MdbLinks th (L.mem r.2.1) G' ∧
        CdtRel th (L.mem r.2.1) σ' G' ∧ MdbInv (L.mem r.2.1) G' ⦄ := by
  obtain ⟨c', a', hc', hca, hg⟩ := hR.slot_cap (Z := Unit) (sl := (px.bv, idx)) rfl (by rw [hl]; exact hpx)
  rw [hc] at hc'
  have : c' = c := by simpa using hc'.symm
  subst this
  rw [hca.abs] at hg
  unfold cdt.delete
  simp only [↓reduceIte]
  rw [finalise_imm_triv arI σ s a _ c' hc ht]
  simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch, uncurry_apply_pair]
  rcases ht with rfl | ⟨fin, hfin, htk⟩
  · -- empty slot: nothing changes
    rw [empty_slot_null arI s a _ hc]
    simp only [bind_ok, uncurry_apply_pair]
    rw [WP.spec_ok]
    have he : Fl4Spec.emptySlot (Z := Unit) (px.bv, idx) .nullCap σ = ({((), σ)}, False) := by
      unfold Fl4Spec.emptySlot
      rw [nd_bind_single hg]; simp [absCap]
    exact ⟨rfl, σ, G, capDelete_triv _ σ σ hg (Or.inl rfl) he, hR, hV, hM, hC, hI⟩
  · have hcn : c' ≠ .Null := by intro e; subst e; simp [TrivKind] at htk
    obtain ⟨⟨s2, a2⟩, he2, ha2, σ', G', hes, hR', hV', hM', hC', hI'⟩ :=
      spec_exists (empty_full (ar := arI) th s a σ G hR hV hP hM hC hI hpx hl hc hcn)
    simp only at ha2 hR' hV' hM' hC' hI'
    rw [he2]
    simp only [bind_ok, uncurry_apply_pair]
    rw [WP.spec_ok]
    exact ⟨rfl, σ', G', capDelete_triv _ σ σ' hg (Or.inr ⟨c', fin, rfl, hcn, htk⟩) hes, hR', hV', hM', hC', hI'⟩

end

end

end Fl4Proofs.P3
