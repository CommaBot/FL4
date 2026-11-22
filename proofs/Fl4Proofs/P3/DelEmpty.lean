/-
P3 (DESIGN.md §9), CSpace: **`empty_slot` with a cleanup cap**, on both
sides: the work of the empty case, then `post_cap_deletion` (FL4's
`post_cap_deletion` is `PostDelHyp`), with `DelInv` and the measures.
-/
import Fl4Proofs.P3.DelDef
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-! ## The spec's `empty_slot` with a cleanup cap -/

section
open Fl4Spec

theorem emptySlot_cl {σ σ2 : State Unit} {slot : CslotPtr} {c : Cap} (cl : Cap)
    (hget : getCap (Z := Unit) slot σ = ({(c, σ)}, False)) (hcn : c ≠ .nullCap)
    (h2 : setCap (Z := Unit) .nullCap slot (emptySlotCdtState σ slot) = ({((), σ2)}, False)) :
    emptySlot (Z := Unit) slot cl σ = postCapDeletion (Z := Unit) cl σ2 := by
  unfold emptySlot
  show (getCap slot >>= _) σ = _
  rw [nd_bind_single hget]
  simp only [hcn, ↓reduceIte]
  show (NonDet.gets _ >>= _) σ = _
  rw [nd_bind_single (gets_eq _ σ)]
  show (NonDet.gets _ >>= _) σ = _
  rw [nd_bind_single (gets_eq _ σ)]
  show ((pure _ : NonDet (State Unit) _) >>= _) σ = _
  rw [nd_pure_bind]
  show (setCdt _ >>= _) σ = _
  rw [nd_bind_one (setCdt_eq _ σ)]
  show (doExtendedOp _ >>= _) _ = _
  rw [nd_bind_single (doExtendedOp_unit _ _)]
  show (setOriginal _ _ >>= _) _ = _
  rw [nd_bind_one (setOriginal_eq _ _ _)]
  show (setCap _ _ >>= _) (emptySlotCdtState σ slot) = _
  rw [nd_bind_one h2]

theorem emptySlot_null_cap {σ : State Unit} {slot : CslotPtr} (cl : Cap)
    (hget : getCap (Z := Unit) slot σ = ({(.nullCap, σ)}, False)) :
    emptySlot (Z := Unit) slot cl σ = ({((), σ)}, False) := by
  unfold emptySlot
  show (getCap slot >>= _) σ = _
  rw [nd_bind_single hget]
  simp only [↓reduceIte]
  rfl

end

theorem setCap_abs_det {th : TypedHeap} {mem : U64 → U64} {σ : Fl4Spec.State Unit} (hR : StateRel th mem σ)
    {sl : Fl4Spec.CslotPtr} (hs : AbsSlot th sl) (a : Fl4Spec.Cap) :
    ∃ σ', Fl4Spec.setCap (Z := Unit) a sl σ = ({((), σ')}, False) := by
  obtain ⟨p, h1, h2 | ⟨ht, i, hi, hidx⟩⟩ := hs
  · obtain ⟨o, idx⟩ := sl
    simp only at h1 h2; subst h1
    obtain ⟨cs, hk, hwf, -⟩ := hR.cnode p _ h2
    exact ⟨_, setCap_cnode a hk hwf rfl⟩
  · obtain ⟨o, idx⟩ := sl
    simp only at h1 hidx; subst h1 hidx
    obtain ⟨tcb, hk, -⟩ := hR.tcb p ht
    exact ⟨_, setCap_tcb a hk hi⟩

/-! ## FL4's `empty_slot` with a cleanup cap -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- `empty_slot`'s work before `post_cap_deletion`, on a slot with a cap. -/
def emptyPre (s : S) (slot : obj.Slot) : Result S := do
  let prev ← obj.Slot.prev st slot s
  let next ← obj.Slot.next st slot s
  let fb ← obj.Slot.first_badged st slot s
  let b1 ← obj.Slot.is_null prev
  let s1 ← if b1 then ok s else obj.Slot.set_next st prev s next
  let b2 ← obj.Slot.is_null next
  let s2 ← if b2 then ok s1 else do
      let s3 ← obj.Slot.set_prev st next s1 prev
      let nfb ← obj.Slot.first_badged st next s3
      if nfb then obj.Slot.set_first_badged st next s3 true
      else obj.Slot.set_first_badged st next s3 fb
  obj.Slot.clear st slot s2

theorem empty_slot_pre (s : S) (a : A) (slot : obj.Slot) (cl : capability.Cap) {c : capability.Cap}
    (hc : obj.Slot.cap st slot s = ok c) (hcn : c ≠ .Null) :
    cdt.empty_slot st arI s a slot cl =
      (do let s3 ← emptyPre (st := st) s slot; objects.post_cap_deletion st arI s3 a cl) := by
  unfold cdt.empty_slot emptyPre
  rw [hc]
  simp only [bind_ok, cap_is_null_ne hcn, Bool.false_eq_true, ↓reduceIte]
  simp only [Std.bind_assoc]

/-- `empty_slot` with a cleanup cap: the empty case, then `post_cap_deletion`. -/
theorem empty_slot_split (s : S) (a : A) (slot : obj.Slot) (cl : capability.Cap) {c : capability.Cap}
    (hc : obj.Slot.cap st slot s = ok c) (hcn : c ≠ .Null) :
    cdt.empty_slot st arI s a slot cl =
      (do let p ← cdt.empty_slot st arI s a slot .Null; objects.post_cap_deletion st arI p.1 p.2 cl) := by
  rw [empty_slot_pre arI s a slot cl hc hcn, empty_slot_pre arI s a slot .Null hc hcn]
  simp only [Std.bind_assoc]
  congr 1
  funext x
  show _ = (do let p ← ok (x, a); objects.post_cap_deletion st arI p.1 p.2 cl)
  rw [bind_tc_ok]

end

/-! ## `empty_slot` with `DelInv` and the measures -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- What emptying the slot `x` gives. -/
def EmptyPost (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr)
    (cl : capability.Cap) (r : S × A) : Prop :=
  ∃ σ' G', ((), σ') ∈ (Fl4Spec.emptySlot (Z := Unit) sl (absCap cl) σ).1 ∧ DState (L := L) th r.1 σ' G' ∧
    capV (L.mem r.1) (cslotAddr sl) = .Null ∧
    (∀ y, IsSlot th y → y ≠ cslotAddr sl → capV (L.mem r.1) y = capV (L.mem s) y) ∧
    psiD (L.mem r.1) G' ≤ psiD (L.mem s) G ∧ (nnS G').card ≤ (nnS G).card ∧
    (capV (L.mem s) (cslotAddr sl) ≠ .Null → (nnS G').card < (nnS G).card ∧ psiD (L.mem r.1) G' < psiD (L.mem s) G) ∧
    MdbStep (L.mem s) G (L.mem r.1) G'

/-- `EmptyPost` with `W` after. -/
def EmptyPostW (W : S → A → Fl4Spec.State Unit → MdbGhost → Prop) (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (cl : capability.Cap) (r : S × A) : Prop :=
  ∃ σ' G', ((), σ') ∈ (Fl4Spec.emptySlot (Z := Unit) sl (absCap cl) σ).1 ∧ DState (L := L) th r.1 σ' G' ∧
    capV (L.mem r.1) (cslotAddr sl) = .Null ∧
    (∀ y, IsSlot th y → y ≠ cslotAddr sl → capV (L.mem r.1) y = capV (L.mem s) y) ∧
    psiD (L.mem r.1) G' ≤ psiD (L.mem s) G ∧ (nnS G').card ≤ (nnS G).card ∧
    (capV (L.mem s) (cslotAddr sl) ≠ .Null → (nnS G').card < (nnS G).card ∧ psiD (L.mem r.1) G' < psiD (L.mem s) G) ∧
    MdbStep (L.mem s) G (L.mem r.1) G' ∧ W r.1 r.2 σ' G'

theorem DelInv.empty {th : TypedHeap} {mem mem' : U64 → U64} {G : MdbGhost} (hD : DelInv th mem)
    (hM : MdbLinks th mem G) {x : U64}
    (hcap : ∀ y, IsSlot th y → capAt mem' y = if y = x then ok .Null else capAt mem y)
    (hp0 : prevOf mem' x = 0#u64) (hn0 : nextOf mem' x = 0#u64)
    (hl : ∀ y, IsSlot th y → y ≠ x → y ∉ G.chains.flatten → prevOf mem' y = prevOf mem y ∧ nextOf mem' y = nextOf mem y) :
    DelInv th mem' := by
  have hcv : ∀ y, IsSlot th y → capV mem' y = if y = x then .Null else capV mem y := by
    intro y hy
    have := hcap y hy
    split_ifs at this ⊢
    · exact capV_of_capAt this
    · exact capV_of_capAt (this.trans (capAt_capV _ _))
  refine ⟨fun y hy p zt n h => ?_, fun y y' hy hy' hyy p zt n p' zt' n' h h' => ?_, fun y hy h => ?_⟩
  · rw [hcv y hy] at h; split_ifs at h; exact hD.zwf y hy p zt n h
  · rw [hcv y hy] at h; rw [hcv y' hy'] at h'
    split_ifs at h h'; exact hD.zu y y' hy hy' hyy p zt n p' zt' n' h h'
  · by_cases hyx : y = x
    · rw [hyx]; exact ⟨hp0, hn0⟩
    · rw [hcv y hy, if_neg hyx] at h
      have hym : y ∉ G.chains.flatten := fun hm => ((mem_nnS hM y).1 (List.mem_toFinset.2 hm)).2 h
      obtain ⟨e1, e2⟩ := hl y hy hyx hym
      rw [e1, e2]; exact hD.nc y hy h

/-- **`empty_slot slot cl`** for a slot of the typed heap and a cleanup cap
(the cleanup's premise only for a cleanup cap), the slot ready (`Rd`) when
not null. -/
theorem empty_stepWR' (W : S → A → Fl4Spec.State Unit → MdbGhost → Prop)
    (Rd : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop) (th : TypedHeap) (hP : Placed th)
    {cl : capability.Cap} (hPD : cl ≠ .Null → PostDelHypW (L := L) arI W th) (hE : EmptyHypWR (L := L) W Rd th)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G) (hW : W s a σ G)
    {sl : Fl4Spec.CslotPtr} (hA : AbsSlot th sl)
    (hRd : capV (L.mem s) (cslotAddr sl) ≠ .Null → Rd s a σ G (cslotAddr sl)) (hcl : CleanCap cl) (hclw : CapWf cl) :
    cdt.empty_slot st arI s a (cslotAddr sl) cl ⦃ r => EmptyPostW (L := L) W th s σ G sl cl r ⦄ := by
  obtain ⟨⟨hR, hV, hM, hC, hI⟩, hD, hFI⟩ := hDS
  have hxs := hA.isSlot
  obtain ⟨c, ac, hc, hca, hg⟩ := hR.abs_cap hA
  rw [hca.abs] at hg
  by_cases hcn : c = .Null
  · subst hcn
    rw [empty_slot_null arI s a _ hc, WP.spec_ok]
    refine ⟨σ, G, ?_, ⟨⟨hR, hV, hM, hC, hI⟩, hD, hFI⟩, capV_of_capAt hc, fun _ _ _ => rfl, le_refl _, le_refl _,
      fun h => absurd (capV_of_capAt hc) h, MdbStep.refl hM, hW⟩
    rw [emptySlot_null_cap _ hg]; rfl
  have hcan : absCap c ≠ .nullCap := fun h => hcn ((absCap_eq_null hca.1).1 h)
  have hsplit := empty_slot_split (st := st) arI s a (cslotAddr sl) cl (c := c) (by rw [slot_cap_eq]; exact hc) hcn
  rw [hsplit]
  have hxm0 : cslotAddr sl ∈ G.chains.flatten := (hM.members _).2 ⟨hxs, c, hc, hcn⟩
  apply WP.spec_bind (WP.spec_and (WP.spec_and (empty_full_abs (ar := arI) th s a σ G hR hV hP hM hC hI hA hc hcn)
    (empty_mstep (ar := arI) hP s a G hM hxm0 hc hcn)) (empty_null_frame arI hP s a hM hD hxs))
  rintro ⟨s1, a1⟩ ⟨⟨⟨ha1, σ1, G1, hes, hR1, hV1, hM1, hC1, hI1, hG1, hcap1, hp01, hn01, hl1⟩, hst1⟩, hF1, -⟩
  simp only at ha1; subst a1
  rw [← hG1] at hst1
  simp only at hes hR1 hV1 hM1 hC1 hI1 hcap1 hp01 hn01 hl1 ⊢
  have hD1 := hD.empty hM hcap1 hp01 hn01 hl1
  have hcv1 : ∀ y, IsSlot th y → capV (L.mem s1) y = if y = cslotAddr sl then .Null else capV (L.mem s) y := by
    intro y hy
    have := hcap1 y hy
    split_ifs at this ⊢
    · exact capV_of_capAt this
    · exact capV_of_capAt (this.trans (capAt_capV _ _))
  have hxm : cslotAddr sl ∈ nnS G := (mem_nnS hM _).2 ⟨hxs, by rw [capV_of_capAt hc]; exact hcn⟩
  have hxm1 : cslotAddr sl ∉ nnS G1 := by
    rw [mem_nnS hM1]; rintro ⟨-, h⟩; rw [hcv1 _ hxs, if_pos rfl] at h; exact h rfl
  have hnn : ∀ y, IsSlot th y → capV (L.mem s1) y ≠ .Null → capV (L.mem s) y ≠ .Null := by
    intro y hy h; rw [hcv1 y hy] at h; split_ifs at h; · exact absurd rfl h
    exact h
  have hmz : ∀ y, IsSlot th y → capV (L.mem s1) y ≠ .Null → ¬ HomeZ (L.mem s1) y → ¬ HomeZ (L.mem s) y := by
    intro y hy h hh hz; apply hh
    rw [hcv1 y hy] at h; split_ifs at h with hyx; · exact absurd rfl h
    obtain ⟨zt, n, e⟩ := hz; exact ⟨zt, n, by rw [hcv1 y hy, if_neg hyx, e]⟩
  have hps1 := psiD_le hM hM1 hnn hmz
  have hsub : nnS G1 ⊂ nnS G := by
    refine Finset.ssubset_iff_subset_ne.2 ⟨fun y hy => ?_, fun e => hxm1 (e ▸ hxm)⟩
    rw [mem_nnS hM1] at hy; rw [mem_nnS hM]; exact ⟨hy.1, hnn y hy.1 hy.2⟩
  have hcd := Finset.card_lt_card hsub
  have hpslt := psiD_lt_nn hM hM1 hnn hmz hxm hxm1
  have hx1 : capV (L.mem s1) (cslotAddr sl) = .Null := by rw [hcv1 _ hxs, if_pos rfl]
  have hoth : ∀ y, IsSlot th y → y ≠ cslotAddr sl → capV (L.mem s1) y = capV (L.mem s) y :=
    fun y hy hyx => by rw [hcv1 y hy, if_neg hyx]
  have hFI1 : FinInv th (L.mem s1) σ1 G1 := by
    refine ⟨hFI.kt.sub (ksub_of_eq (emptySlot_nks _ _) hes), ?_⟩
    subst hG1
    exact hFI.fm.remove hM _ hM1.tree.nodup (fun z hz hzx => hoth z ((hM.members z).1 hz).1 hzx)
  -- the spec's `empty_slot` with the cleanup cap
  obtain ⟨σ2, h2⟩ := setCap_abs_det (StateRel.of_kheap hR (σ' := emptySlotCdtState σ sl) rfl) hA .nullCap
  have he0 := emptySlot_eq hg hcan h2
  rw [hes] at he0
  have e : σ1 = σ2 := by simpa using he0
  subst e
  have hcl' := emptySlot_cl (absCap cl) hg hcan h2
  have hcvn : capV (L.mem s) (cslotAddr sl) ≠ .Null := by rw [capV_of_capAt hc]; exact hcn
  have hW1 : W s1 a σ1 G1 := hE s s1 a σ σ1 G G1 sl hW (hRd hcvn) ⟨⟨hR, hV, hM, hC, hI⟩, hD, hFI⟩
    ⟨⟨hR1, hV1, hM1, hC1, hI1⟩, hD1, hFI1⟩ hF1 (by rw [emptySlot_cl Fl4Spec.Cap.nullCap hg hcan h2]; rfl) hA hcvn hx1
    hoth hst1
  by_cases hcln : cl = .Null
  · subst hcln
    show (objects.post_cap_deletion st arI s1 a .Null) ⦃ _ ⦄
    rw [show objects.post_cap_deletion st arI s1 a .Null = ok (s1, a) from rfl, WP.spec_ok]
    refine ⟨σ1, G1, ?_, ⟨⟨hR1, hV1, hM1, hC1, hI1⟩, hD1, hFI1⟩, hx1, hoth, hps1, hcd.le, fun _ => ⟨hcd, hpslt⟩, hst1,
      hW1⟩
    rw [hcl']; rfl
  · refine WP.spec_mono (hPD hcln s1 a σ1 G1 cl ⟨⟨hR1, hV1, hM1, hC1, hI1⟩, hD1, hFI1⟩ hW1 hcl hcln hclw) ?_
    rintro ⟨s2, a2⟩ ⟨hS2, σ2, hpd, hCR2, hW2⟩
    simp only at hS2 hpd hCR2 hW2 ⊢
    refine ⟨σ2, G1, by rw [hcl']; exact hpd, ⟨hCR2, hD1.of_same hS2, hFI1.of_same hM1 hS2 (postCapDeletion_nks _ σ1 _ hpd)⟩, by rw [hS2.capV hxs]; exact hx1,
      fun y hy hyx => by rw [hS2.capV hy]; exact hoth y hy hyx, by rw [psiD_same hM1 hCR2.2.2.1 hS2]; exact hps1,
      hcd.le, fun _ => ⟨hcd, by rw [psiD_same hM1 hCR2.2.2.1 hS2]; exact hpslt⟩, hst1.same_right hM1 hS2, hW2⟩

/-- **`empty_slot slot cl`** for a slot of the typed heap and a cleanup cap
(the cleanup's premise only for a cleanup cap). -/
theorem empty_stepW' (W : S → A → Fl4Spec.State Unit → MdbGhost → Prop) (th : TypedHeap) (hP : Placed th)
    {cl : capability.Cap} (hPD : cl ≠ .Null → PostDelHypW (L := L) arI W th) (hSl : SlotHypW (L := L) (A := A) W th)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G) (hW : W s a σ G)
    {sl : Fl4Spec.CslotPtr} (hA : AbsSlot th sl) (hcl : CleanCap cl) (hclw : CapWf cl) :
    cdt.empty_slot st arI s a (cslotAddr sl) cl ⦃ r => EmptyPostW (L := L) W th s σ G sl cl r ⦄ :=
  empty_stepWR' arI W RdT th hP hPD hSl.empty s a σ G hDS hW hA (fun _ => trivial) hcl hclw

/-- **`empty_slot slot cl`** for a slot of the typed heap and a cleanup cap. -/
theorem empty_stepW (W : S → A → Fl4Spec.State Unit → MdbGhost → Prop) (th : TypedHeap) (hP : Placed th)
    (hPD : PostDelHypW (L := L) arI W th) (hSl : SlotHypW (L := L) (A := A) W th)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G) (hW : W s a σ G)
    {sl : Fl4Spec.CslotPtr} (hA : AbsSlot th sl) (cl : capability.Cap) (hcl : CleanCap cl) (hclw : CapWf cl) :
    cdt.empty_slot st arI s a (cslotAddr sl) cl ⦃ r => EmptyPostW (L := L) W th s σ G sl cl r ⦄ :=
  empty_stepW' arI W th hP (fun _ => hPD) hSl s a σ G hDS hW hA hcl hclw

/-- **`empty_slot slot cl`** for a slot of the typed heap and a cleanup cap
(`empty_stepW` at `W := True`). -/
theorem empty_step (th : TypedHeap) (hP : Placed th) (hPD : PostDelHyp (L := L) arI th)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G)
    {sl : Fl4Spec.CslotPtr} (hA : AbsSlot th sl) (cl : capability.Cap) (hcl : CleanCap cl) (hclw : CapWf cl) :
    cdt.empty_slot st arI s a (cslotAddr sl) cl ⦃ r => EmptyPost (L := L) th s σ G sl cl r ⦄ := by
  refine WP.spec_mono (empty_stepW arI WTrue th hP (hPD.w arI) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial) s a σ G hDS
    trivial hA cl hcl hclw) ?_
  rintro r ⟨σ', G', h1, h2, h3, h4, h5, h6, h7, h8, -⟩
  exact ⟨σ', G', h1, h2, h3, h4, h5, h6, h7, h8⟩

end

end

end Fl4Proofs.P3
