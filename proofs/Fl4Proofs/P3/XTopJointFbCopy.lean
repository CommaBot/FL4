/-
P3 (issue #16, FL4 #71), VSpace FrameBatch: **one COPY_MAP entry at `J`** (KENTRY-PLAN fb3l):
`frame_batch_entry`'s COPY_MAP arm: the destination's lookup and `ensure_empty_slot`, the source's
lookup, the frame check, `mask_cap_rights` and `derive_cap`, `insert_with_cap` (`JAtZ.insDJ`), `batch_map`
against `fbMap`, and on its error `cdt.delete` of the fresh copy.

The two lookups' CNodes are reached from the batch's root caps (`bt.cnode`,
`bt.dest_cnode`, read from the extra-cap slots at the decode); the insert at
`J` needs each CNode named by a CNode cap held in a slot (`DestCap`), so
`fb_entry_copyJ` takes `hRt`: both root caps still held in slots at the
entry's state (the batch writes only frame caps over frame caps, a derived
frame cap into an empty slot, and empties frame-cap slots, so no CNode cap
moves; the loop must carry this).
-/
import Fl4Proofs.P3.XTopJointFbCopyIns
import Fl4Proofs.P3.XTopJointFbRemap
import Fl4Proofs.P3.SpecFbCopyRun
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop}

set_option maxHeartbeats 8000000 in
/-- **One COPY_MAP entry at `J`** (module docstring). -/
theorem fb_entry_copyJ [Fl4Proofs.P1.PlainStore st] (hA : ArchRefines arI AR) (hT : P0.ArchTotal arI)
    {σ : Fl4Spec.State Unit} {th0 : TypedHeap}
    {ct buf : U64} {args : List U64} {bt : vspace.Batch} {b : Fl4Spec.Fl4FrameBatchInvocation}
    (hDP : JDelParts (L := L) arI AR th0) (hnd : Fl4Spec.numDomains = 1) (hARI : ARIface arI AR)
    (C : FbCtx σ th0 args bt b) (hopC : bt.op = vspace.frame_batch.COPY_MAP)
    (x : S) (a : A) (τ : Fl4Spec.State Unit) (hM : FbMidJ (L := L) (AR := AR) arI σ th0 ct buf args x a τ)
    (hRt : (∃ y, IsSlot th0 y ∧ capV (L.mem x) y = bt.cnode) ∧ (∃ y, IsSlot th0 y ∧ capV (L.mem x) y = bt.dest_cnode))
    (w : Fl4Spec.Data × Fl4Spec.Data × Fl4Spec.Data) (w0 w1 w2 : U64)
    (hw0 : w0.bv = w.1) (hw1 : w1.bv = w.2.1) (hw2 : w2.bv = w.2.2) (df : Bool) :
    vspace.frame_batch_entry st arI x a bt w0 w1 w2 df ⦃ r =>
      FbEntryPost (L := L) (AR := AR) arI σ th0 ct buf args b w τ df r ∧ CnSlotsKept (L := L) th0 x r.2.1 ⦄ := by
  unfold FbEntryPost
  obtain ⟨p1, as1, op, depth, a1, cr, a2, dd, cn, dcn⟩ := bt
  obtain ⟨⟨Z1, H1, Cs1, Ac1, Lst1, D1, hth, hct, hbm, J, hLv⟩, hargs, hK, hns, hsg, hp0⟩ := id hM
  have hbop : b.op = .copyMap := C.hopC.1 hopC
  have hX := J.xtop
  obtain ⟨-, hCR, -, -, -, -, -⟩ := id hX.rel
  obtain ⟨hSt, hSV, -, -, -⟩ := id hCR
  have hcv : CapValid Z1.th cn := by rw [hth]; exact C.hcv
  have hdcv : CapValid Z1.th dcn := by rw [hth]; exact C.hdcv
  have hDP1 : JDelParts (L := L) arI AR Z1.th := by rw [hth]; exact hDP
  have hRt1 : (∃ y, IsSlot Z1.th y ∧ capV (L.mem x) y = cn) ∧ (∃ y, IsSlot Z1.th y ∧ capV (L.mem x) y = dcn) := by
    rw [hth]; exact hRt
  have hpos : as1.bv > 0 := by
    have : as1.val ≠ 0 := fun h => C.h0 (UScalar.eq_of_val_eq (by simpa using h))
    show 0 < as1.bv.toNat
    exact Nat.pos_of_ne_zero this
  unfold vspace.frame_batch_entry
  simp only at hopC ⊢
  rw [if_pos hopC]
  -- the destination's lookup
  rw [show cspace.lookup_target_slot st x dcn w1 depth = cspace.lookup_slot_for_cnode_op st x false dcn w1 depth
    from rfl]
  refine WP.spec_bind (lookup_slot_for_cnode_op_refines (Z := Unit) Z1.th x τ hSt hSV false dcn (absCap dcn)
    ⟨C.hdcw, rfl⟩ hdcv w1 depth) ?_
  rintro r1 ⟨e1, he1, hrel1⟩
  have hld : ExceptT.run (Fl4Spec.lookupTargetSlot (Z := Unit) b.destCnode (Fl4Spec.dataToCptr w.2.1) b.depth) τ =
      ({(e1, τ)}, False) := by rw [C.hbd, C.hdep, ← hw1]; exact he1
  cases r1
  case Err e =>
    cases e1 with
    | ok _ => exact hrel1.elim
    | error e' =>
      simp only [fbr_branch_err, bind_ok, fbr_fromResidual]
      refine (WP.spec_ok _).2 ⟨⟨τ, hM, Or.inr ⟨e, rfl, rfl, ?_⟩⟩, CnSlotsKept.refl _ _⟩
      have hmem := fbEntry_copy_destErr (w := w) hbop (by rw [hld]; exact Set.mem_singleton _)
      cases e with
      | Sys e2 => exact WP.spec_mono (fb_code (Or.inl (Or.inl hrel1))) fun c hc => by rw [hc]; exact hmem
      | _ => exact hrel1.elim
  rename_i dsl
  cases e1
  case error => exact hrel1.elim
  rename_i dsl'
  obtain ⟨rfl, pd, hpd1, hpd, hcrd⟩ := hrel1
  obtain ⟨da, idxd⟩ := dsl'
  simp only at hpd1 hpd
  subst hpd1
  have hdm : (.ok (pd.bv, idxd), τ) ∈ (ExceptT.run (Fl4Spec.lookupTargetSlot (Z := Unit) b.destCnode
      (Fl4Spec.dataToCptr w.2.1) b.depth) τ).1 := by rw [hld]; exact Set.mem_singleton _
  simp only [fbr_branch_ok, bind_ok]
  -- the destination must be empty
  unfold cdt.ensure_empty_slot
  rw [slot_cap_eq]
  obtain ⟨cd, ad, hcd, hcad, hgd⟩ := hSt.slot_cap (Z := Unit) (sl := (pd.bv, idxd)) (p := pd) rfl hpd
  rw [hcd, bind_ok]
  have hee := ensureEmpty_run (pd.bv, idxd) τ hgd
  by_cases hdn : cd = .Null
  swap
  · rw [cap_is_null_ne hdn]
    simp only [bind_ok, Bool.false_eq_true, ↓reduceIte, fbr_branch_err, fbr_fromResidual]
    refine (WP.spec_ok _).2 ⟨⟨τ, hM, Or.inr ⟨_, rfl, rfl, ?_⟩⟩, CnSlotsKept.refl _ _⟩
    have hadn : ad ≠ .nullCap := fun h => hdn ((hcad.null_iff).1 h)
    have hmem := fbEntry_copy_full (w := w) hbop hdm (by rw [hee, if_neg hadn]; exact Set.mem_singleton _)
    exact WP.spec_mono (fb_code (Or.inl (Or.inl (show SysErrRel (.Sys .DeleteFirst) .deleteFirst from trivial))))
      fun c hc => by rw [hc]; exact hmem
  subst hdn
  have hadn : ad = .nullCap := (hcad.null_iff).2 rfl
  have hem : (.ok (), τ) ∈ (ExceptT.run (Fl4Spec.ensureEmpty (Z := Unit) (pd.bv, idxd)) τ).1 := by
    rw [hee, if_pos hadn]; exact Set.mem_singleton _
  rw [cap_is_null_null]
  simp only [bind_ok, ↓reduceIte, fbr_branch_ok]
  -- the source's lookup
  rw [lookup_source_eq]
  refine WP.spec_bind (lookup_slot_for_cnode_op_refines (Z := Unit) Z1.th x τ hSt hSV true cn (absCap cn)
    ⟨C.hcw, rfl⟩ hcv w0 depth) ?_
  rintro r2 ⟨e2, he2, hrel2⟩
  have hls : ExceptT.run (Fl4Spec.lookupSourceSlot (Z := Unit) b.cnode (Fl4Spec.dataToCptr w.1) b.depth) τ =
      ({(e2, τ)}, False) := by rw [C.hbc, C.hdep, ← hw0]; exact he2
  cases r2
  case Err e =>
    cases e2 with
    | ok _ => exact hrel2.elim
    | error e' =>
      simp only [fbr_branch_err, bind_ok, fbr_fromResidual]
      refine (WP.spec_ok _).2 ⟨⟨τ, hM, Or.inr ⟨e, rfl, rfl, ?_⟩⟩, CnSlotsKept.refl _ _⟩
      have hmem := fbEntry_copy_srcErr (w := w) hbop hdm hem (by rw [hls]; exact Set.mem_singleton _)
      cases e with
      | Sys e3 => exact WP.spec_mono (fb_code (Or.inl (Or.inl hrel2))) fun c hc => by rw [hc]; exact hmem
      | _ => exact hrel2.elim
  rename_i ssl
  cases e2
  case error => exact hrel2.elim
  rename_i ssl'
  obtain ⟨rfl, ps, hps1, hps, hcrs⟩ := hrel2
  obtain ⟨sa, idxs⟩ := ssl'
  simp only at hps1 hps
  subst hps1
  have hsm : (.ok (ps.bv, idxs), τ) ∈ (ExceptT.run (Fl4Spec.lookupSourceSlot (Z := Unit) b.cnode
      (Fl4Spec.dataToCptr w.1) b.depth) τ).1 := by rw [hls]; exact Set.mem_singleton _
  simp only [fbr_branch_ok, bind_ok]
  -- the source's cap
  have hAs : AbsSlot Z1.th (ps.bv, idxs) := ⟨ps, rfl, Or.inl hps⟩
  have hAd : AbsSlot Z1.th (pd.bv, idxd) := ⟨pd, rfl, Or.inl hpd⟩
  rw [slot_cap_eq]
  obtain ⟨srcC, srcA, hsc, hsca, hgs⟩ := hSt.slot_cap (Z := Unit) (sl := (ps.bv, idxs)) (p := ps) rfl hps
  rw [hsc, bind_ok]
  have hgsm : (srcA, τ) ∈ (Fl4Spec.getCap (Z := Unit) (ps.bv, idxs) τ).1 := by rw [hgs]; exact Set.mem_singleton _
  obtain ⟨o, ho⟩ : ∃ o, vspace.as_frame srcC = ok o := by cases srcC <;> simp [vspace.as_frame]
  rw [ho, bind_ok]
  rcases o with _ | f
  · simp only [core.option.Option.is_none, ↓reduceIte, error.invalid_cap, bind_ok]
    refine (WP.spec_ok _).2 ⟨⟨τ, hM, Or.inr ⟨_, rfl, rfl, ?_⟩⟩, CnSlotsKept.refl _ _⟩
    have hmem := fbEntry_copy_notPage (w := w) hbop hdm hem hsm hgsm (by rw [hsca.abs]; exact fbc_notPage ho)
    exact WP.spec_mono (fb_code (Or.inl (Or.inr ⟨0#u64, rfl, rfl⟩))) fun c hc => by rw [hc]; exact hmem
  obtain ⟨p, sz, rt, d, m, ep, asid, va, rfl⟩ :
      ∃ p sz rt d m ep asid va, srcC = .Frame p sz rt d m ep asid va := by
    cases srcC <;> simp [vspace.as_frame] at ho
    exact ⟨_, _, _, _, _, _, _, _, rfl⟩
  simp only [core.option.Option.is_none, Bool.false_eq_true, ↓reduceIte]
  have hp : Fl4Spec.isPageCap srcA = true := by rw [hsca.abs]; rfl
  -- mask and derive
  rw [from_word_eq, bind_ok]
  obtain ⟨c1, hm, hw1', ha1, he1, hv1, -, -⟩ := mask_rel (rightsW cr) _ hsca.1
  rw [hm, bind_ok]
  obtain ⟨rt', rfl⟩ := fbc_mask_frame hm
  have hse : EncWf (capability.Cap.Frame p sz rt d m ep asid va) := by
    have h := hsc; rw [capAt_words] at h; exact decode_encWf h
  have hscv : CapValid Z1.th (capability.Cap.Frame p sz rt d m ep asid va) := SlotsValid.abs hSV hAs hsc
  obtain ⟨r4, hr4, r', hr', hdr⟩ := derive_rel (Z := Unit) x τ (cslotAddr (ps.bv, idxs)) (ps.bv, idxs) _ hw1'
    (he1 hse) (fun h => False.elim h)
  have hr4' : objects.derive_cap st x (cslotAddr (ps.bv, idxs)) (.Frame p sz rt' d m ep asid va) =
      ok (.Ok (.Frame p sz rt' d false false 0#u64 0#u64)) := rfl
  rw [hr4'] at hr4
  cases eq_of_ok_eq hr4
  cases r'
  case error => exact hdr.elim
  rename_i na
  obtain ⟨hwc, hna, hec, hvc, -⟩ := hdr
  subst hna
  rw [hr4', bind_ok]
  simp only [fbr_branch_ok, bind_ok]
  have hmask : Fl4Spec.maskCap (Fl4Spec.dataToRights b.capRights) srcA =
      absCap (.Frame p sz rt' d m ep asid va) := by rw [hsca.abs, ha1, rightsW_spec, C.hcr]
  have hdvm : (.ok (absCap (.Frame p sz rt' d false false 0#u64 0#u64)), τ) ∈
      (ExceptT.run (Fl4Spec.deriveCap (Z := Unit) (ps.bv, idxs) (Fl4Spec.maskCap (Fl4Spec.dataToRights b.capRights)
        srcA)) τ).1 := by
    rw [hmask, hr']; exact Set.mem_singleton _
  -- the insert
  rw [insert_with_cap_eq x _ _ _ _ hsc]
  have hDs := fbc_destCap hcrs hRt1.1
  have hDd := fbc_destCap hcrd hRt1.2
  refine WP.spec_bind (J.fbInsJ arI hLv hns hsg hp0 hps hpd rfl rfl hsc hcd hwc (hvc Z1.th (hv1 Z1.th hscv)) hec
    hDs hDd) ?_
  rintro s1 ⟨σ1, G1, hci, J1, hLv1, hns1, hsg1, hp01, hK1, hF1, hdc1, hcn1⟩
  have hcim : ((), σ1) ∈ (Fl4Spec.capInsert (Z := Unit) (absCap (.Frame p sz rt' d false false 0#u64 0#u64))
      (ps.bv, idxs) (pd.bv, idxd) τ).1 := by rw [hci]; rfl
  have hf1 : ExceptT.run (Fl4Spec.findVspaceForAsid (Z := Unit) as1.bv) σ1 = ({(.ok p1.bv, σ1)}, False) :=
    (hK.trans hK1).findVs hpos C.hf
  -- the map
  refine WP.spec_bind (WP.spec_and (JAtZ.batchMapJL arI hA J1 hLv1 hns1 hsg1 hp01 (pc := pd) hpd rfl C.h0 C.hasid hf1
    op depth a1 cr a2 dd cn dcn w2 b C.hbv C.hba C.hmr C.hat) (JAtZ.batchMapJX arI hA J1 (pc := pd) hpd rfl C.h0
    C.hasid hf1 op depth a1 cr a2 dd cn dcn w2 b C.hbv C.hba C.hmr C.hat)) ?_
  rintro ⟨r5, s2, a2'⟩ ⟨(⟨e5, e', h1, h2, h3, h4, h5⟩ | ⟨h1, τ2, hmem2, J2, hK2, hF2, hLv2, hns2, hsg2, hp02, -⟩), hXJ⟩
  · simp only at h1 h4 h5
    subst h1
    subst s2 a2'
    fbj_red
    simp only [core.result.Result.is_err, bind_ok, ↓reduceIte]
    have hc1 : capAt (L.mem s1) (cslotAddr (pd.bv, idxd)) = ok (.Frame p sz rt' d false false 0#u64 0#u64) := by
      rw [capAt_capV, hdc1]
    refine WP.spec_bind (JAtZ.fbDelFrameJN arI J1 hDP1 hT hnd hARI hLv1 hns1 hsg1 hp01 hAd hc1 rfl) ?_
    rintro ⟨r6, s3, a3⟩ ⟨-, σ3, G3, V3, Ac3, Lst3, D3, hdel, J3, hLv3, hns3, hsg3, hp03, -, hcn3⟩
    fbj_red
    -- the spec's cap at the destination after the insert, for `FbKeep` across the delete
    obtain ⟨c9, a9, hc9, hca9, hg9⟩ := (J1.xtop.rel.2.1.1).slot_cap (Z := Unit) (sl := (pd.bv, idxd)) (p := pd) rfl hpd
    rw [hc1] at hc9
    cases eq_of_ok_eq hc9
    obtain ⟨-, hcap9⟩ := SInvU.getCap_capAt (show (a9, σ1) ∈ (Fl4Spec.getCap (Z := Unit) (pd.bv, idxd) σ1).1 by
      rw [hg9]; exact Set.mem_singleton _)
    rw [hca9.abs] at hcap9
    obtain ⟨hKd, hum3⟩ := fbKeep_capDelete_frame hcap9 hdel
    refine (WP.spec_ok _).2 ⟨⟨σ3, FbMidJ.step arI (a := a) (H1 := H1) (Cs1 := Cs1) (Ac1 := Ac1) (Lst1 := Lst1)
      (D1 := D1) C.hal hth hct hbm hargs hK J3 rfl rfl rfl
      (fbc_foot_trans (Z' := Z1.mv G1 Z1.vs) rfl rfl hF1 (FbFootK.of_rel arI J1 J3 rfl rfl hKd hum3)) (hK1.trans hKd) hLv3 hns3 hsg3 hp03,
      Or.inr ⟨e5, rfl, rfl, ?_⟩⟩, by rw [← hth]; exact hcn1.trans hcn3⟩
    have hm3 : (.error e', σ1) ∈ (ExceptT.run (Fl4Spec.fbMap (Z := Unit) b (pd.bv, idxd) w.2.2) σ1).1 := by
      rw [← hw2, h3]; exact Set.mem_singleton _
    have hmem := fbEntry_copy_mapErr (w := w) hbop hdm hem hsm hgsm hp hdvm hcim hm3 hdel
    cases e5 with
    | Sys e6 =>
      have h2' : ErrRel (.Sys e6) e' ∨ (e6 = .AlignmentError ∧ e' = .alignmentError) := by
        rcases h2 with h | ⟨he6, rfl⟩
        · exact Or.inl h
        · cases he6; exact Or.inr ⟨rfl, rfl⟩
      exact WP.spec_mono (fb_code h2') fun c hc => by rw [hc]; exact hmem
    | _ => rcases h2 with (h | ⟨n, h, -⟩) | ⟨h, -⟩ <;> cases h
  · simp only at h1
    subst h1
    fbj_red
    simp only [core.result.Result.is_err, bind_ok, Bool.false_eq_true, ↓reduceIte]
    obtain hcn2 : CnSlotsKept (L := L) Z1.th s1 s2 := by
      rcases hXJ with ⟨e9, -, h9, -⟩ | ⟨-, -, -, -, -, -, -, -, -, -, hc9, -⟩
      · cases h9
      · exact hc9
    refine (WP.spec_ok _).2 ⟨⟨τ2, FbMidJ.step arI (a := a) (H1 := H1) (Cs1 := Cs1) (Ac1 := Ac1) (Lst1 := Lst1)
      (D1 := D1) C.hal hth hct hbm hargs hK J2 rfl rfl rfl (fbc_foot_trans (Z' := Z1.mv G1 Z1.vs) rfl rfl hF1 hF2) (hK1.trans hK2)
      hLv2 hns2 hsg2 hp02, Or.inl ⟨rfl, false, ?_, by simp⟩⟩, by rw [← hth]; exact hcn1.trans hcn2⟩
    exact fbEntry_copy_ok hbop hdm hem hsm hgsm hp hdvm hcim (by rw [← hw2]; exact hmem2)

end

end

end Fl4Proofs.P3
