/-
P3 (issue #16, FL4 #71), VSpace FrameBatch: **the delete of a frame-cap slot
at `J` without `PPPlat`** (KENTRY-PLAN fb3l). XTopJointFbDelFrame's
`JAtZ.fbDelFrameJL` runs the deletion loop, whose preemption point needs
`PPPlat` — false (`PPPlat.false`), so the real tops (XTopJointKEntry13P/23P,
`JEntryGlobM`) never have it. A frame cap's delete is one round with no
preemption point (MachKeepG4d's `MKD.cdt_finalise_frame`), so the same post
holds from the round's steps alone. OPEN (scratch stub).
-/
import Fl4Proofs.P3.XTopJointFbDelFrame
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop}

set_option maxHeartbeats 8000000 in
/-- An unmapped frame cap's finalisation leaves the store as it is (at most a DMA retire). -/
theorem fin_frame_unmapped (hT : P0.ArchTotal arI) (s : S) (a : A) (p : U64) (sz : capability.FrameSize)
    (r : U64) (d e : Bool) (asd va : U64) (fin : Bool) :
    objects.finalise_cap st arI s a (.Frame p sz r d false e asd va) fin false ⦃ x => x.2.1 = s ⦄ := by
  unfold objects.finalise_cap objects.finalise_cap_object
  simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
  fbj_red
  split_ifs <;> first
    | exact (WP.spec_ok _).2 rfl
    | (simp only [bind_ok, WP.spec_ok])
    | exact WP.spec_bind (P0.objects.retire_dma_frame.p0 st arI s a p sz L.total hT) fun _ _ => (WP.spec_ok _).2 rfl
  all_goals first
    | exact (WP.spec_ok _).2 rfl
    | exact WP.spec_bind (P0.objects.retire_dma_frame.p0 st arI s a p sz L.total hT) fun _ _ => (WP.spec_ok _).2 rfl
    | rfl

set_option maxHeartbeats 8000000 in
/-- **A frame cap's finalisation keeps every slot's words** (`SlotsSame`): an unmapped frame's leaves
the store; a VSpace-mapped one's is XTopJointFinVs's `JAtZ.finVsJb`, an EPT-mapped one's
XTopJointFinVtJ's `JAtZ.frVtJ`. -/
theorem JAtZ.finFrameSS [Fl4Proofs.P1.PlainStore st] {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hDP : JDelParts (L := L) arI AR Z.th)
    (hT : P0.ArchTotal arI) (hDS : DState (L := L) Z.th s σ Z.G) {sl : Fl4Spec.CslotPtr} (hA : AbsSlot Z.th sl)
    {p : U64} {sz : capability.FrameSize} {r : U64} {d m e : Bool} {asd va : U64}
    (hc : capAt (L.mem s) (cslotAddr sl) = ok (.Frame p sz r d m e asd va)) (fin : Bool) :
    objects.finalise_cap st arI s a (.Frame p sz r d m e asd va) fin false ⦃ x =>
      SlotsSame Z.th (L.mem s) (L.mem x.2.1) ⦄ := by
  cases m
  · exact WP.spec_mono (fin_frame_unmapped arI hT s a p sz r d e asd va fin) fun x hx => by
      rw [hx]; exact SlotsSame.refl _ _
  · cases e
    · refine WP.spec_mono (J.finVsJb hDP.archRef (jVsApartHyp arI Z H Cs Ac Lst D s a σ rfl J) hDS hA hc rfl
        ⟨_, rfl⟩ fin (Or.inr ⟨p, sz, r, d, false, asd, va, rfl⟩)) ?_
      rintro x ⟨-, -, -, -, -, -, hSS, -⟩; exact hSS
    · refine WP.spec_mono (J.frVtJ hDP.archRef hDP.arKeep hDP.vt hDS hA hc (Or.inl ⟨p, sz, r, d, asd, va, rfl⟩) fin) ?_
      rintro x ⟨-, -, -, -, -, hSS, -⟩; exact hSS

set_option maxHeartbeats 8000000 in
/-- **The delete of a frame-cap slot at `J`, one round** (module docstring). OPEN. -/
theorem JAtZ.fbDelFrameJN [Fl4Proofs.P1.PlainStore st] {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hDP : JDelParts (L := L) arI AR Z.th) (hT : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hARI : ARIface arI AR)
    (hLv : LiveDN (L := L) Z.th H Cs Z.G s σ) (hns : Vs.NoSwitch σ) (hsg : SpecGlob σ) (hp0 : PPR0 σ)
    {sl : Fl4Spec.CslotPtr} (hA : AbsSlot Z.th sl) {c : capability.Cap}
    (hc : capAt (L.mem s) (cslotAddr sl) = ok c) {f : vspace.FrameCap} (hf : vspace.as_frame c = ok (some f)) :
    cdt.delete st arI s a (cslotAddr sl) true ⦃ r => r.1 = .Ok () ∧ ∃ (σ' : Fl4Spec.State Unit) (G' : MdbGhost)
      (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
      (.ok (), σ') ∈ ((Fl4Spec.capDelete (Z := Unit) sl).run σ).1 ∧
      JAtZ (L := L) arI AR (Z.mv G' V') H Cs Ac' Lst' D' r.2.1 r.2.2 σ' ∧
      LiveDN (L := L) Z.th H Cs G' r.2.1 σ' ∧ Vs.NoSwitch σ' ∧ SpecGlob σ' ∧ PPR0 σ' ∧ L.ksb r.2.1 = L.ksb s ∧
      CnSlotsKept (L := L) Z.th s r.2.1 ⦄ := by
  have hP : Placed Z.th := J.xtop.rel.1
  have hCR := J.xtop.rel.2.1
  have hDS : DState (L := L) Z.th s σ Z.G := ⟨hCR, J.del, J.xtop.rel.2.2.1⟩
  have hW : WJL (L := L) arI AR Z H Cs (L.ksb s) s a σ Z.G :=
    ⟨⟨(Z.P, Z.L4, Z.L3, Z.L2, Z.L1), Ac, Lst, D, J, rfl, hns, hsg, hp0⟩, hLv⟩
  have hmask : ∀ (a : A) (irq : U64) (b : Bool), ∃ a', arI.mask_irq a irq b = ok a' := fun a i m => by
    obtain ⟨a', h, -⟩ := spec_exists (hT.mask_irq a i m); exact ⟨a', h⟩
  have hfree : ∀ (a : A) (irq : U64), ∃ a', arI.irq_free a irq = ok a' := fun a i => by
    obtain ⟨a', h, -⟩ := spec_exists (hT.irq_free a i); exact ⟨a', h⟩
  have hFin := finJLZ (st := st) (L := L) arI hT hDP.archRef hDP.arKeep hDP.vt hDP.thr Z H Cs (L.ksb s) rfl
  have hTriv := rdTrivJLO (st := st) (L := L) (AR := AR) arI Z H Cs (L.ksb s) rfl
  have hPost := jPostDelHypL (st := st) (L := L) arI hARI.toMask hmask hfree Z H Cs (L.ksb s) rfl
  have hEmp := emptyHypJL (st := st) (L := L) (AR := AR) arI Z H Cs (L.ksb s) rfl
  have hF := finalHyp_full (L := L) Z.th hP
  have hcn : c ≠ .Null := by intro e; subst e; simp [vspace.as_frame] at hf
  have hfr : ∃ p sz r d m e asd va, c = .Frame p sz r d m e asd va := by
    cases c <;> simp [vspace.as_frame] at hf
    exact ⟨_, _, _, _, _, _, _, _, rfl⟩
  obtain ⟨fp, fsz, fr, fd, fm, fe, fasd, fva, rfl⟩ := hfr
  obtain ⟨c', ac, hc', hca, hg⟩ := hCR.1.abs_cap hA
  rw [hc] at hc'
  cases eq_of_ok_eq hc'
  rw [hca.abs] at hg
  have hcan : absCap (.Frame fp fsz fr fd fm fe fasd fva) ≠ .nullCap := fun h => hcn (absCap_eq_null.1 h)
  obtain ⟨bf, hbf1, hbf2, -⟩ := hF s σ Z.G sl _ hDS hA hc hcn
  -- the one round of `finalise_slot_immediate`
  have hround : cdt.finalise_slot_immediate st arI s a (cslotAddr sl) ⦃ x =>
      ∃ (fz : cdt.Finalised) (σ1 : Fl4Spec.State Unit) (G1 : MdbGhost), x.1 = .Ok fz ∧ CleanCap fz.cleanup ∧
        CapWf fz.cleanup ∧ RD (.finaliseSlotCall sl true) σ (.ok (true, absCap fz.cleanup), σ1) ∧
        DState (L := L) Z.th x.2.1 σ1 G1 ∧ WJL (L := L) arI AR Z H Cs (L.ksb s) x.2.1 x.2.2 σ1 G1 ∧
        (capV (L.mem x.2.1) (cslotAddr sl) ≠ .Null → RdLO (L := L) (A := A) Z.th H x.2.1 x.2.2 σ1 G1 (cslotAddr sl)) ∧
        SlotsSame Z.th (L.mem s) (L.mem x.2.1) ⦄ := by
    unfold cdt.finalise_slot_immediate cdt.finalise_slot_immediate_loop
    apply loop.spec_decr_nat (measure := fun y => y.2.2.val)
      (inv := fun y => y.1 = s ∧ y.2.1 = a ∧ 0 < y.2.2.val)
    · rintro ⟨s1, a1, fuel⟩ ⟨e1, e2, hfu⟩
      dsimp only at e1 e2 hfu ⊢
      subst e1 e2
      unfold cdt.finalise_slot_immediate_loop.body
      have hf0 : fuel > 0#u64 := by scalar_tac
      obtain ⟨fuel1, hv, -⟩ := spec_exists (U64.sub_spec (x := fuel) (y := 1#u64) (by scalar_tac))
      simp only [hf0, ↓reduceIte, hv, bind_ok, slot_cap_eq]
      rw [hc]; simp only [bind_ok]
      rw [cap_is_null_ne hcn]; simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
      rw [is_final_with_cap_eq _ _ _ hc, hbf1]; simp only [bind_ok]
      apply WP.spec_bind (WP.spec_and (fin_stepZ arI _ _ _ Z.th hFin hTriv hF hP s1 a1 σ Z.G hDS hW hA hc hcn bf hbf2)
        (J.finFrameSS arI hDP hT hDS hA hc bf))
      rintro ⟨⟨rem, cl⟩, s2, a2⟩ ⟨⟨σ1, G1, hmem, hDS1, -, -, hcl, hclw, -, hrem, -, hW1, hRd1, -, hZF⟩, hSS⟩
      try simp only [uncurry_apply_pair] at hmem hDS1 hcl hclw hrem hW1 hRd1 hZF ⊢
      try dsimp only at hmem hDS1 hcl hclw hrem hW1 hRd1 hZF ⊢
      rcases hrem with rfl | ⟨p, zt, n, rfl, -⟩
      · simp only [cdt.cap_removable, bind_ok, ↓reduceIte, WP.spec_ok]
        exact ⟨_, σ1, G1, rfl, hcl, hclw, rd_fin_removable hg hcan hmem trivial, hDS1, hW1,
          fun _ => hRd1 (Or.inl rfl), hSS⟩
      · exfalso
        obtain ⟨-, h | h⟩ := hZF rfl p zt n rfl
        · obtain ⟨q, hq⟩ := h; cases hq
        · obtain ⟨q, r0, gs, g, hq⟩ := h; cases hq
    · exact ⟨rfl, rfl, MKD.walk_fuel_pos⟩
  unfold cdt.delete
  simp only [↓reduceIte]
  apply WP.spec_bind hround
  rintro ⟨r, s1, a1⟩ ⟨fz, σ1, G1, hr, hcl, hclw, hrd, hDS1, hW1, hRd1, hSS⟩
  simp only at hr hDS1 hW1 hRd1 hSS ⊢
  subst hr
  simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  apply WP.spec_bind (empty_stepWR' arI (WJL (L := L) arI AR Z H Cs (L.ksb s)) (RdLO (L := L) (A := A) Z.th H) Z.th
    hP (fun _ => hPost) hEmp s1 a1 σ1 G1 hDS1 hW1 hA hRd1 hcl hclw)
  rintro ⟨s2, a2⟩ ⟨σ2, G2, hes, -, -, hoth2, -, -, -, -, hW2⟩
  simp only [uncurry_apply_pair] at hes hoth2 hW2 ⊢
  rw [WP.spec_ok]
  obtain ⟨v, hv⟩ := rd_cte_ok (σ2 := σ2) hrd (by simp only [true_or, Fl4Spec.NonDet.when, ↓reduceIte]; exact hes)
  obtain ⟨⟨V', Ac', Lst', D', J', hkb, hns', hsg', hp0'⟩, hLv'⟩ := hW2
  refine ⟨rfl, σ2, G2, V', Ac', Lst', D', capDelete_ok hv, J', hLv', hns', hsg', hp0', hkb, ?_⟩
  intro y hy q rq gq g' hyc
  have hne : y ≠ cslotAddr sl := by
    rintro rfl; rw [capV_of_capAt hc] at hyc; cases hyc
  rw [hoth2 y hy hne, hSS.capV hy]; exact hyc

end

end

end Fl4Proofs.P3
