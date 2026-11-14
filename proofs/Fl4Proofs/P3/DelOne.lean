/-
P3 (DESIGN.md §9), CSpace: **`cdt::delete_one` against l4v
`cap_delete_one`**, for a slot holding nothing or a notification cap (an
IRQ node slot): FL4's finality test (`FinalHyp`), the notification's
finalisation (`FinObjHyp`, the `fast_finalise` of the spec's notification
case) and `empty_slot` (`empty_step`).
-/
import Fl4Proofs.P3.DelPost
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
open Fl4Spec

theorem mem_liftM_inv {σ α β : Type} {f : α → β} {m : NonDet σ α} {s : σ} {y : β × σ}
    (h : y ∈ (NonDet.liftM f m s).1) : ∃ x, (x, y.2) ∈ (m s).1 ∧ y.1 = f x := by
  obtain ⟨x, hx, hy⟩ := h
  rw [Set.mem_singleton_iff.1 hy]; exact ⟨x.1, hx, rfl⟩

/-- The spec's notification finalisation is its `fast_finalise`. -/
theorem fastFinalise_of_finaliseCap {r b : ObjRef} {rs : CapRights} {fin : Bool} {σ σ' : State Unit} {y : Cap × Cap}
    (h : (y, σ') ∈ (finaliseCap (Z := Unit) (.notificationCap r b rs) fin σ).1) :
    ((), σ') ∈ (fastFinalise (Z := Unit) (.notificationCap r b rs) fin σ).1 := by
  obtain ⟨x, hx, -⟩ := mem_liftM_inv h
  cases x; exact hx

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

theorem finalise_cap_ntfn (s : S) (a : A) (p b : U64) (w r fin ex : Bool) :
    objects.finalise_cap st arI s a (.Notification p b w r) fin ex =
      objects.finalise_cap_object st arI s a (.Notification p b w r) fin := by
  simp [objects.finalise_cap]

/-- **`delete_one` refines `cap_delete_one`**, for a slot of the typed heap
holding nothing or a notification cap. -/
theorem delete_one_refines (th : TypedHeap) (hP : Placed th) (hF : FinalHyp (L := L) th)
    (hO : FinObjHyp (L := L) arI th) (hPD : PostDelHyp (L := L) arI th)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G)
    {sl : Fl4Spec.CslotPtr} (hA : AbsSlot th sl)
    (hk : capV (L.mem s) (cslotAddr sl) = .Null ∨
      ∃ p b w r, capV (L.mem s) (cslotAddr sl) = .Notification p b w r) :
    cdt.delete_one st arI s a (cslotAddr sl) ⦃ r =>
      ∃ σ' G', ((), σ') ∈ (Fl4Spec.capDeleteOne (Z := Unit) sl σ).1 ∧ DState (L := L) th r.1 σ' G' ∧
        MdbStep (L.mem s) G (L.mem r.1) G' ⦄ := by
  obtain ⟨c, ac, hc, hca, hg⟩ := hDS.1.1.abs_cap hA
  rw [hca.abs] at hg
  have hcv := capV_of_capAt hc
  unfold cdt.delete_one
  rw [slot_cap_eq, hc]
  simp only [bind_ok, cap_is_null_eq]
  rcases hk with hk | ⟨p, b, w, r, hk⟩
  · rw [hcv] at hk; subst hk
    simp only [isNullB, ↓reduceIte, WP.spec_ok]
    refine ⟨σ, G, ?_, hDS, MdbStep.refl hDS.1.2.2.1⟩
    unfold Fl4Spec.capDeleteOne
    refine mem_bind_nd (x := (absCap .Null, σ)) (by rw [hg]; rfl) ?_
    simp [absCap, Fl4Spec.NonDet.unless, Fl4Spec.NonDet.pure]
  · rw [hcv] at hk; subst hk
    have hcn : capability.Cap.Notification p b w r ≠ .Null := by simp
    simp only [isNullB_false hcn, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨bf, hbf, hbf2, -⟩ := hF s σ G sl _ hDS hA hc hcn
    have hNF : NeedsFin (.Notification p b w r) := Or.inl ⟨trivial, rfl⟩
    rw [hbf2 hNF] at hbf
    rw [hbf]; simp only [bind_ok]
    rw [← finalise_cap_ntfn arI s a p b w r _ false]
    apply WP.spec_bind (hO s a σ G sl _ hDS hA hc trivial)
    rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨hrem, hcl, -, σ1, G1, hmem, hDS1, -, -, hmO⟩
    simp only [uncurry_apply_pair]
    refine WP.spec_mono (empty_step arI th hP hPD s1 a1 σ1 G1 hDS1 hA .Null trivial trivial) ?_
    rintro ⟨s2, a2⟩ ⟨σ2, G2, hes, hDS2, -, -, -, -, -, hmE⟩
    refine ⟨σ2, G2, ?_, hDS2, hmO.trans hmE⟩
    unfold Fl4Spec.capDeleteOne
    refine mem_bind_nd (x := (absCap (.Notification p b w r), σ)) (by rw [hg]; rfl) ?_
    simp only [absCap, Fl4Spec.NonDet.unless, reduceCtorEq, ↓reduceIte]
    refine mem_bind_nd (x := (decide (Fl4Spec.isFinalCap' (absCap (.Notification p b w r)) σ), σ)) rfl ?_
    refine mem_bind_nd (x := ((), σ1)) (fastFinalise_of_finaliseCap hmem) ?_
    exact hes


/-- Finalising a notification cap leaves every slot's cap as it was (its
work is on TCBs, notifications and scheduling contexts). -/
def NtfnKeepHyp (th : TypedHeap) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (p b : U64) (w r fin : Bool),
    DState (L := L) th s σ G → AbsSlot th sl → capAt (L.mem s) (cslotAddr sl) = ok (.Notification p b w r) →
    objects.finalise_cap st arI s a (.Notification p b w r) fin false ⦃ res =>
      ∀ y, IsSlot th y → capV (L.mem res.2.1) y = capV (L.mem s) y ⦄

/-- `delete_one_refines`, with the slot emptied and the other slots' caps
kept. -/
theorem delete_one_keep (th : TypedHeap) (hP : Placed th) (hF : FinalHyp (L := L) th)
    (hO : FinObjHyp (L := L) arI th) (hPD : PostDelHyp (L := L) arI th) (hK : NtfnKeepHyp (L := L) arI th)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G)
    {sl : Fl4Spec.CslotPtr} (hA : AbsSlot th sl)
    (hk : capV (L.mem s) (cslotAddr sl) = .Null ∨
      ∃ p b w r, capV (L.mem s) (cslotAddr sl) = .Notification p b w r) :
    cdt.delete_one st arI s a (cslotAddr sl) ⦃ r =>
      (∃ σ' G', ((), σ') ∈ (Fl4Spec.capDeleteOne (Z := Unit) sl σ).1 ∧ DState (L := L) th r.1 σ' G' ∧
        MdbStep (L.mem s) G (L.mem r.1) G') ∧
      capV (L.mem r.1) (cslotAddr sl) = .Null ∧
      ∀ y, IsSlot th y → y ≠ cslotAddr sl → capV (L.mem r.1) y = capV (L.mem s) y ⦄ := by
  refine WP.spec_and (delete_one_refines arI th hP hF hO hPD s a σ G hDS hA hk) ?_
  obtain ⟨c, ac, hc, hca, hg⟩ := hDS.1.1.abs_cap hA
  have hcv := capV_of_capAt hc
  unfold cdt.delete_one
  rw [slot_cap_eq, hc]
  simp only [bind_ok, cap_is_null_eq]
  rcases hk with hk | ⟨p, b, w, r, hk⟩
  · rw [hcv] at hk; subst hk
    simp only [isNullB, ↓reduceIte, WP.spec_ok]
    exact ⟨hcv, fun _ _ _ => trivial⟩
  · rw [hcv] at hk; subst hk
    have hcn : capability.Cap.Notification p b w r ≠ .Null := by simp
    simp only [isNullB_false hcn, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨bf, hbf, hbf2, -⟩ := hF s σ G sl _ hDS hA hc hcn
    rw [hbf2 (Or.inl ⟨trivial, rfl⟩)] at hbf
    rw [hbf]; simp only [bind_ok]
    rw [← finalise_cap_ntfn arI s a p b w r _ false]
    apply WP.spec_bind (WP.spec_and (hO s a σ G sl _ hDS hA hc trivial) (hK s a σ G sl p b w r _ hDS hA hc))
    rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨⟨hrem, hcl, -, σ1, G1, hmem, hDS1, -, -, -⟩, hkeep⟩
    try simp only [uncurry_apply_pair]
    refine WP.spec_mono (empty_step arI th hP hPD s1 a1 σ1 G1 hDS1 hA .Null trivial trivial) ?_
    rintro ⟨s2, a2⟩ ⟨σ2, G2, -, -, hx2, hoth, -, -, -, -⟩
    refine ⟨hx2, fun y hy hyx => ?_⟩
    rw [hoth y hy hyx, hkeep y hy]

end

end

end Fl4Proofs.P3
