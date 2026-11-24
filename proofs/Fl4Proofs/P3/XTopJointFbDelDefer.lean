/-
P3 (issue #16, FL4 #71), VSpace FrameBatch (KENTRY-PLAN fb3l): **a DELETE
entry's deferred unmap at `J`**: FL4's `unmap_page_unflushed` of a
VSpace-mapped non-device frame through the batch's root, the cleared frame
cap's `set_cap`, then `cdt.delete` of the slot, against the spec's
`unmapPageUnflushed`, `setCap` of the unmapped page cap and `cap_delete`.
Plan: FL4's `unmap_page` is `find_vspace_for_asid` (here the batch's root)
then the same body with `invalidate_page`, and `empty_slot` clears every
word of the slot, so the final memory is the non-deferred delete's
(XTopJointFbDelFrameN's `JAtZ.fbDelFrameJN`); the spec likewise, but for the
flush's machine state. Proved directly instead: VsFbUnmapU's `unmap_unflushed_rel` and the
cleared cap's `set_cap` (as VsFrameUnmapRel's `frame_unmap_rel` without the restart and the flush),
lifted to `JAtZ` as XTopJointFbMapJ's `JAtZ.batchMapJX` (`JAtZ.fbDeferStepJ`), then
XTopJointFbDelFrameN's `JAtZ.fbDelFrameJN` at the cleared cap.
-/
import Fl4Proofs.P3.XTopJointFbDelFrameN
import Fl4Proofs.P3.SpecFbKeepDel
import Fl4Proofs.P3.VsFbUnmapU
import Fl4Proofs.P3.XTopJointFbMapJL
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section Spec
open Fl4Spec

/-- **The spec's deferred unmap then the cleared cap's `setCap`** is a `VsSFr` step. -/
theorem vsSFr_defer {τ τu : State Unit} {pc : ObjRef} {r : Nat} {cs : CnodeContents} {idx : List Bool} {nc : Cap}
    (hshape : τu = τ ∨ ∃ q ao ao', τ.kheap q = some (.archObj ao) ∧ aaType ao' = aaType ao ∧
      aaType ao ≠ .aASIDPool ∧ τu = Notif.updK τ q (.archObj ao'))
    (hkc : τu.kheap pc = some (.cnode r cs)) (hwf : wellFormedCnodeN r cs) (hidx : idx.length = r) :
    VsSFr τ (setCnodeSlot τu pc r cs idx nc) := by
  have hwf' := wf_update nc hwf hidx
  rcases hshape with rfl | ⟨q, ao, ao', hq, ht, -, rfl⟩
  · refine ⟨fun o => ?_, fun o => ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl⟩
    · by_cases e : o = pc
      · subst e
        exact Or.inr (Or.inr (Or.inl ⟨r, cs, Function.update cs idx (some nc), hkc, by simp [setCnodeSlot]⟩))
      · exact Or.inl (by simp [setCnodeSlot, e])
    · by_cases e : o = pc
      · subst e; simp [setCnodeSlot, hkc, aType, hwf, hwf']
      · simp [setCnodeSlot, e]
  · have hpq : pc ≠ q := fun e => by subst e; simp [Notif.updK] at hkc
    have hkc0 : τ.kheap pc = some (.cnode r cs) := by
      rw [Notif.updK_kheap, Function.update_of_ne hpq] at hkc; exact hkc
    refine ⟨fun o => ?_, fun o => ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl⟩
    · by_cases e : o = pc
      · subst e
        exact Or.inr (Or.inr (Or.inl ⟨r, cs, Function.update cs idx (some nc), hkc0, by simp [setCnodeSlot]⟩))
      · by_cases e2 : o = q
        · subst e2
          exact Or.inr (Or.inl ⟨ao, ao', hq, by simp [setCnodeSlot, Notif.updK, e], ht⟩)
        · exact Or.inl (by simp [setCnodeSlot, Notif.updK, e, e2])
    · by_cases e : o = pc
      · subst e; simp [setCnodeSlot, hkc0, aType, hwf, hwf']
      · by_cases e2 : o = q
        · subst e2; simp [setCnodeSlot, Notif.updK, e, hq, aType, ht]
        · simp [setCnodeSlot, Notif.updK, e, e2]

/-- `FbKeep` of the deferred unmap and the cleared cap's `setCap`. -/
theorem fbKeep_defer {τ τu : State Unit} {pc : ObjRef} {r : Nat} {cs : CnodeContents} {idx : List Bool} {nc : Cap}
    (hshape : τu = τ ∨ ∃ q ao ao', τ.kheap q = some (.archObj ao) ∧ aaType ao' = aaType ao ∧
      aaType ao ≠ .aASIDPool ∧ τu = Notif.updK τ q (.archObj ao'))
    (hkc : τu.kheap pc = some (.cnode r cs)) : FbKeep τ (setCnodeSlot τu pc r cs idx nc) := by
  refine FbKeep.trans ?_ (Vs.fbk_cnode hkc idx nc)
  rcases hshape with rfl | ⟨q, ao, ao', hq, ht, hn, rfl⟩
  · exact FbKeep.refl _
  · exact Vs.fbk_arch hq hn ao' ht

/-- The caps after the deferred unmap and the `setCap` of a page cap: `CapPage`. -/
theorem capPage_defer {τ τu : State Unit} {pc : ObjRef} {r : Nat} {cs : CnodeContents} {idx : List Bool} {nc : Cap}
    (hshape : τu = τ ∨ ∃ q ao ao', τ.kheap q = some (.archObj ao) ∧ aaType ao' = aaType ao ∧
      aaType ao ≠ .aASIDPool ∧ τu = Notif.updK τ q (.archObj ao'))
    (hkc : τu.kheap pc = some (.cnode r cs)) (hwf : wellFormedCnodeN r cs) (hidx : idx.length = r)
    (hnc : IsPageCap nc) : Vs.CapPage τ (setCnodeSlot τu pc r cs idx nc) (pc, idx) := by
  rcases hshape with rfl | ⟨q, ao, ao', hq, -, -, rfl⟩
  · exact Vs.capPage_set hkc hwf hidx nc hnc (fun _ _ => rfl)
  · have hpq : pc ≠ q := fun e => by subst e; simp [Notif.updK] at hkc
    have hkc0 : τ.kheap pc = some (.cnode r cs) := by
      rw [Notif.updK_kheap, Function.update_of_ne hpq] at hkc; exact hkc
    refine Vs.capPage_set hkc0 hwf hidx nc hnc (fun o cref => ?_)
    by_cases e : o = pc
    · subst e; simp [setCnodeSlot, Notif.updK]
    · by_cases e2 : o = q
      · subst e2; simp [setCnodeSlot, Notif.updK, e, hq, capOpt]
      · simp [setCnodeSlot, Notif.updK, e, e2]

end Spec

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop}

set_option maxHeartbeats 8000000 in
/-- **The deferred unmap and the cleared cap's `set_cap` at `J`** (module docstring): `JAtZ` at the
same sets after, with the liveness facts, against `unmapPageUnflushed` and `setCap`. -/
theorem JAtZ.fbDeferStepJ [Fl4Proofs.P1.PlainStore st] {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {τ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a τ) (hA : ArchRefines arI AR)
    (hLv : LiveDN (L := L) Z.th H Cs Z.G s τ) (hns : Vs.NoSwitch τ) (hsg : SpecGlob τ) (hp0 : PPR0 τ)
    {pc : U64} {idx : List Bool} (hpc : Z.th pc = some (.cnode idx.length)) {p : U64} {sz : capability.FrameSize}
    {rt asd va : U64}
    (hc : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.Frame p sz rt false true false asd va))
    {root : U64} (hfv : ExceptT.run (Fl4Spec.findVspaceForAsid (Z := Unit) asd.bv) τ = ({(.ok root.bv, τ)}, False))
    {b2 : Bool} {sU s' : S}
    (hu : vspace.unmap_page_unflushed st s root sz va p = ok (b2, sU))
    (hs : obj.Slot.set_cap st (cslotAddr (pc.bv, idx)) sU (.Frame p sz rt false false false 0#u64 0#u64) = ok s') :
    ∃ τu σ' : Fl4Spec.State Unit,
      (b2, τu) ∈ (Fl4Spec.unmapPageUnflushed (Z := Unit) (frameSizeOf sz) root.bv va.bv p.bv τ).1 ∧
      ((), σ') ∈ (Fl4Spec.setCap (Z := Unit) (.archObjectCap (.pageCap false p.bv (vmRightsOf rt) .vmNoMap
        (frameSizeOf sz) none)) (pc.bv, idx) τu).1 ∧
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s' a σ' ∧ LiveDN (L := L) Z.th H Cs Z.G s' σ' ∧ Vs.NoSwitch σ' ∧
      SpecGlob σ' ∧ PPR0 σ' ∧ L.ksb s' = L.ksb s ∧ FbKeep τ σ' ∧
      σ'.machineState.underlyingMemory = τ.machineState.underlyingMemory ∧ CnSlotsKept (L := L) Z.th s s' ∧
      capAt (L.mem s') (cslotAddr (pc.bv, idx)) = ok (.Frame p sz rt false false false 0#u64 0#u64) := by
  set c : capability.Cap := .Frame p sz rt false true false asd va with hcf
  have hidx : idx.length = idx.length := rfl
  have hX := J.xtop
  obtain ⟨hS, hR, hPt, hPI, hCur⟩ := id hX.fin
  obtain ⟨hPl, hCR, hFI, hDR, hMO, hIA, -⟩ := id hX.rel
  obtain ⟨hSt, hSV, -, -, -⟩ := id hCR
  have hA0 : AbsSlot Z.th (pc.bv, idx) := ⟨pc, rfl, Or.inl hpc⟩
  have hxsl : IsSlot Z.th (cslotAddr (pc.bv, idx)) := hA0.isSlot
  have hcv0 : capV (L.mem s) (cslotAddr (pc.bv, idx)) = c := capV_of_capAt hc
  have hok : VCapOK Z.P Z.L4 Z.L3 Z.L2 Z.L1 c := by
    have h := J.vsc _ hxsl
    rw [hcv0] at h
    exact h.okTab trivial
  have hasd : asd ≠ 0#u64 := hok.1 rfl
  have hvu : UserV va := hok.2.2 rfl
  have hr1 : root ∈ Z.L4 := fb_root_L4 hR hPI hasd hfv
  have hHU : VsUnmapPageHyps st A arI Z.L3 Z.L2 Z.L1 (FootSR st (TopSR st Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1
      Z.N Z.T Z.C Z.E Z.R Z.B Z.c AR) s (VsFootW0 st Z.th Z.L4 Z.L3 Z.L2 Z.L1 s)) :=
    (vsUnmapPageHyps_top hA).foot (s0 := s) (W := VsFootW0 st Z.th Z.L4 Z.L3 Z.L2 Z.L1 s) (fun _ h => h)
  have hHF : VsFrameHyps st A arI Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (FootSR st (TopSR st Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1
      Z.N Z.T Z.C Z.E Z.R Z.B Z.c AR) s (VsFootW0 st Z.th Z.L4 Z.L3 Z.L2 Z.L1 s)) :=
    (vsFrameHyps_top hA).foot (s0 := s) (W := VsFootW0 st Z.th Z.L4 Z.L3 Z.L2 Z.L1 s) (fun _ h => h) hS.2.pl
  -- the deferred unmap
  have h1 := unmap_unflushed_rel (th := Z.th) (P := Z.P) (L4 := Z.L4) hHU s a τ hS.2.pl hS.2.pt hS.2.ps hS.2.vs hS.2.pv
    ⟨⟨hS, P1.WritesIn.refl _ _⟩, hSt, hSV, hR, hPt⟩ sz root va p hr1 hvu
  rw [hu, WP.spec_ok] at h1
  obtain ⟨τu, hmu, hshape, ⟨hSu, hStu, hSVu, hRu, hPtu⟩, hksu, hKu, hASu, hWu⟩ := h1
  dsimp only at hmu hSu hStu hSVu hRu hPtu hksu hWu
  -- the cleared cap's `set_cap`
  obtain ⟨cs, hkc, hwf, -⟩ := hSt.cnode pc _ hpc
  have hkcu : τu.kheap pc.bv = some (.cnode idx.length cs) := by
    rcases hshape with e | ⟨q, ao, ao', hq, -, -, e⟩
    · rw [e]; exact hkc
    · have hpq : pc.bv ≠ q := fun e' => by rw [e', hq] at hkc; cases hkc
      rw [e, Notif.updK_kheap, Function.update_of_ne hpq]; exact hkc
  obtain ⟨cS, aS, hcS, hcaS, hgS⟩ := hSt.slot_cap (Z := Unit) (sl := (pc.bv, idx)) (p := pc) rfl hpc
  rw [hc] at hcS; cases eq_of_ok_eq hcS
  have hfw : CapWf c := hcaS.1
  have hfe : EncWf c := by have h := hc; rw [capAt_words] at h; exact decode_encWf h
  have hfcv : CapValid Z.th c :=
    hSV.cnode pc _ hpc (blVal 0 idx) (blVal_lt idx) _
      (by rw [show slotAddr pc.bv (BitVec.ofNat 64 (blVal 0 idx)) = cslotAddr (pc.bv, idx) from
        (slotAddr_ofBl pc idx).symm]; exact hc)
  set nc : Fl4Spec.Cap := .archObjectCap (.pageCap false p.bv (vmRightsOf rt) .vmNoMap (frameSizeOf sz) none) with hnc
  have hca : CapRel (.Frame p sz rt false false false 0#u64 0#u64) nc := ⟨hfw, rfl⟩
  have hew : EncWf (.Frame p sz rt false false false 0#u64 0#u64) := ⟨hfe.1, hfe.2.1, by decide, by decide⟩
  have h2 := WP.spec_and (set_cap_refines Z.th sU τu hStu hSVu hS.2.pl hpc rfl _ _ hca (by exact hfcv) hew)
    (WP.spec_and (set_cap_spec (L := L) _ sU _) (set_cap_foot hS.2.pl hxsl sU _ hew))
  rw [hs, WP.spec_ok] at h2
  obtain ⟨⟨σ5, hsc, hSt', hSV', -, -, -, hfr5⟩, hs5, hF5, hcv5⟩ := h2
  have hsc' := hsc
  rw [setCap_cnode nc hkcu hwf rfl] at hsc
  have hσ5 : σ5 = setCnodeSlot τu pc.bv idx.length cs idx nc := by
    have := congrArg Prod.fst hsc
    simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at this
    exact this.symm
  subst hσ5
  set σ' := setCnodeSlot τu pc.bv idx.length cs idx nc with hσ'
  have hxs : IsSlotAt Z.th pc (blVal 0 idx) := Or.inl ⟨idx.length, hpc, blVal_lt idx⟩
  have hx0 : cslotAddr (pc.bv, idx) = slotOf pc (blVal 0 idx) := slotAddr_ofBl pc idx
  have hks5 : L.ksb s' = L.ksb sU := by rw [hs5]; simp
  have hks' : L.ksb s' = L.ksb s := hks5.trans hksu
  have hWs : P1.WritesIn st sU s' (SlotW Z.th) := by
    refine ⟨by rw [hs5]; simp, by rw [hs5]; simp, fun b hb hn => ?_⟩
    obtain ⟨h1, h2⟩ := ne_slot_words hS.2.pl hxs hn
    exact hfr5 b hb (by rw [hx0]; exact h1) (by rw [hx0]; exact h2)
  have hSRq := hHF.capStable _ _ a _ _ hSu hWs ⟨pc.bv, idx.length, cs, idx, nc, hkcu, rfl⟩
  have hR' : VsRel Z.P (L.mem s') (L.ksb s') σ' := by
    have hfrV : ∀ b, VsWrite Z.P (L.ksb s) b → L.mem s' b = L.mem sU b := by
      intro b hb
      obtain ⟨h1, h2⟩ := ne_slot_words hS.2.pl hxs (hS.2.sd b hb)
      exact hfr5 b (hb.aligned hS.2.vs) (by rw [hx0]; exact h1) (by rw [hx0]; exact h2)
    have hpools : ∀ q ∈ Z.P, σ'.kheap q.bv = τu.kheap q.bv := by
      intro q hq
      obtain ⟨g, hg, -⟩ := hRu.pool q hq
      have : q.bv ≠ pc.bv := kheap_ne hg hkcu (fun _ h1 h2 => by subst h1; cases h2)
      simp [hσ', setCnodeSlot, this]
    rw [hks5]; rw [hksu] at hRu ⊢
    exact hRu.frame hfrV rfl hpools
  have hPt' : PtRel Z.L4 Z.L3 Z.L2 Z.L1 (L.mem s') σ' := by
    refine hPtu.frame (fun b hb => ?_) (fun q hq => ?_)
    · obtain ⟨h1, h2⟩ := ne_slot_words hS.2.pl hxs (hS.2.ps b hb)
      exact hfr5 b (hb.aligned hS.2.pt) (by rw [hx0]; exact h1) (by rw [hx0]; exact h2)
    · obtain ⟨ao, hao⟩ := hPtu.arch hq
      have : q.bv ≠ pc.bv := kheap_ne hao hkcu (fun _ h1 h2 => by subst h1; cases h2)
      simp [hσ', setCnodeSlot, this]
  have hK : KFoot τ σ' := hKu.trans (KFoot.cnode hkcu hwf idx nc)
  have hSF : SlotFoot Z.th (L.mem s) (L.mem s') (cslotAddr (pc.bv, idx)) :=
    (SlotFoot.of_writes hS.2.pl hWu (fun b hb => hS.2.po b hb) _).trans hF5
  have hLk : VsLike (capV (L.mem s') (cslotAddr (pc.bv, idx))) c := by
    rw [hcv5]
    refine ⟨⟨rfl, rfl, rfl, rfl⟩, fun P L4 L3 L2 L1 h => ?_⟩
    rw [hcf] at h
    simp only [VCapOK] at h ⊢
    exact ⟨fun e => absurd e (by decide), h.2.1, fun e => absurd e (by decide)⟩
  have hnu0 : isUt c = false := rfl
  obtain ⟨hCR', hFI', hMO'⟩ := crelM_after hCR hFI hMO hc hSt' hSV' hSF hLk hK hnu0
  obtain ⟨hTS', hW0⟩ := id hSRq
  obtain ⟨⟨hSch', hEp', hNt', -⟩, -⟩ := id hTS'
  have hIpc' : IpcRel Z.N Z.T Z.E Z.R Z.B (L.mem s') σ' := IpcRel.of hNt' hEp' (sched_sc hSch')
  have F : VsSFr τ σ' := vsSFr_defer hshape hkcu hwf rfl
  -- the TCBs' state words and the action word, pinned
  have pinS : ∀ t, Z.th t = some .tcb → L.mem s' (P1.stA t) = L.mem s (P1.stA t) := by
    intro t ht
    have htT := J.thT t ht
    obtain ⟨y1, hk1, hR1⟩ := J.xtop.ipc.tcb t htT
    obtain ⟨y, hky, hRy⟩ := hIpc'.tcb t htT
    obtain ⟨y', hy', hc'⟩ := F.tcbF hk1
    rw [hky] at hy'; cases hy'
    have h1 : (L.mem s' (tStA t)).val = (L.mem s (tStA t)).val := by rw [hRy.st, hR1.st, hc'.st]
    rw [stA_tStA]; exact UScalar.eq_of_val_eq h1
  have pinA : L.mem s' (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) =
      L.mem s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) := by
    have a1 := J.xtop.fin.1.1.1.act
    have a2 := hSch'.act
    rw [F.act] at a2
    have e := ActRel.det a2 a1
    obtain ⟨Q, R, hcq, -⟩ := J.xtop.fin.1.1.1.lists
    unfold nodeW at e
    rw [P1.nodeAt_of_ksb hks', ← hcq.cur] at e
    exact e
  -- FL4's writes in `VsXW`
  have hW : P1.WritesIn st s s' (VsXW Z (L.ksb s) (cslotAddr (pc.bv, idx))) := by
    refine ⟨hks', hW0.2.1, fun b hb hn => ?_⟩
    have hslw : ∀ y, IsSlot Z.th y → ∀ k : U64, Off k → b = wordOf y k → L.mem s' b = L.mem s b := by
      intro y hy k hk e
      subst e
      obtain ⟨h16, h24, hne⟩ := hSF y hy
      rcases hk with rfl | rfl | rfl | rfl
      · by_cases ex : y = cslotAddr (pc.bv, idx)
        · exact (hn (Or.inr (Or.inl (by rw [wordOf_zero, ex])))).elim
        · rw [wordOf_zero]; exact (hne ex).1
      · by_cases ex : y = cslotAddr (pc.bv, idx)
        · exact (hn (Or.inr (Or.inr (by rw [ex])))).elim
        · exact (hne ex).2
      · exact h16
      · exact h24
    by_cases hb0 : VsFootW0 st Z.th Z.L4 Z.L3 Z.L2 Z.L1 s b
    · rcases hb0 with ⟨y, hy, e | e⟩ | ⟨y, k, hy, hk, e⟩ | hpt | ⟨t, ht, e⟩ | e
      · exact hslw y hy 0#u64 (Or.inl rfl) (by rw [wordOf_zero]; exact e)
      · exact hslw y hy 8#u64 (Or.inr (Or.inl rfl)) e
      · exact hslw y hy k hk e
      · exact (hn (Or.inl (Or.inl hpt))).elim
      · subst e; exact pinS t ht
      · subst e; exact pinA
    · exact hW0.2.2 b hb hb0
  -- the domain schedule's words (in `OObj`, so outside `VsXW`)
  have hD' : DomRel (L.mem s') (L.ksb s') σ' := by
    rw [hks']
    refine DomRel.frame hDR (fun o ho => ?_) F.dl F.dsi
    have ho' : o.val < 256 ∧ o.val % 8 = 0 := by
      simp only [domOffs, List.mem_cons, List.mem_nil_iff, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hal := ksW_al J.kern.ksbFit J.kern.ksbAl ho'.1 ho'.2
    have hv := ksW_val (kb := L.ksb s) (o := o) (by have := J.kern.ksbFit; omega)
    exact hW.mem_eq hal fun hb => hS.2.disj _ (Or.inr (Or.inl ⟨by omega, by omega, Or.inl (by omega)⟩))
      (vsxw_vobj hPl hS.2.vs hS.2.pt hxsl hb)
  have hFXT := vs_x_afterT hS hPI hCur hSRq hR' hPt' hCR' hFI' hMO' hK
  have hFXR := FinXT.toXR Z.G hX.esa hIA.dom hFXT hD'
  have hX' : XTopAt (L := L) AR Z s' a σ' := by
    obtain ⟨hFin, ⟨G0, hPl', -, -, hD, -, hIA', hSA⟩, hE⟩ := hFXR
    obtain ⟨⟨⟨hSch, hEp, hNt, -⟩, -⟩, -⟩ := id hFin
    exact ⟨hFin, ⟨hPl', hCR', hFI', hD, by rw [hks']; exact hMO', hIA', hSA⟩, IpcRel.of hNt hEp (sched_sc hSch), hE⟩
  -- the slots
  have hcap : ∀ y, IsSlot Z.th y → y ≠ cslotAddr (pc.bv, idx) → capV (L.mem s') y = capV (L.mem s) y := by
    intro y hy hne
    obtain ⟨-, -, h⟩ := hSF y hy
    unfold capV; rw [(h hne).1, (h hne).2]
  have Ap : VsApart (L := L) Z H Cs s := jVsApartHyp arI Z H Cs Ac Lst D s a τ rfl J
  have hvc : Vs.VsSlotsW Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.mem s') := by
    intro y hy
    by_cases e : y = cslotAddr (pc.bv, idx)
    · rw [e]
      exact (hLk.2 _ _ _ _ _ hok).toW
    · rw [hcap y hy e]; exact J.vsc y hy
  -- (int5, F1 stage 5 item 4) `VsNamed` after the leaf unmap and the cleared cap (`Vs.VsNamed.ofUnmapLeafF`)
  have hUL : Vs.UnmapLeafF (L.mem s') (cslotAddr (pc.bv, idx)) c τ σ' :=
    ⟨True.intro, by rw [hcv5]; exact True.intro,
      Vs.ArchShr.keep_right hASu (Vs.cnode_keep hkcu idx nc).1 (Vs.cnode_keep hkcu idx nc).2⟩
  have hvn : Z.vx = ∅ → Vs.VsNamed Z.th (L.mem s') (L.ksb s') := fun hvx => by
    have hR'' : Vs.VsRel Z.P (L.mem s') (L.ksb s) σ' := by rw [← hks']; exact hR'
    have h := (J.carry.vsNamed hvx).ofUnmapLeafF J.vsc J.xtop.fin.2.1 J.xtop.fin.2.2.1 J.xtop.fin.2.2.2.1
      hR'' hPt' hcv0 hSF hUL
    rw [hks']; exact h
  have J' := J.vsStepJ Ap hpc hidx hX' F hW hcap (by rw [hcv0]; exact hLk.1.1) (by rw [hcv0]; exact hLk.1.2.1)
    (by rw [hcv0]; exact hnu0) (by rw [hcv0]; exact hLk.1.2.2.2)
    (fun y hy => ⟨(hSF y hy).1, (hSF y hy).2.1⟩) hvc hvn
  have hsim : ∀ y, IsSlot Z.th y → LSim (capV (L.mem s') y) (capV (L.mem s) y) := by
    intro y hy
    by_cases e : y = cslotAddr (pc.bv, idx)
    · rw [e, hcv0]; exact LSim.of_shape hLk.1.1
    · rw [hcap y hy e]; exact LSim.rfl' _
  have h0 : ∃ a0, capOpt (τ.kheap pc.bv) idx = some a0 ∧ IsPageCap a0 :=
    ⟨aS, (getCap_set_iff τ pc.bv idx aS).1 (congrArg Prod.fst hgS), by rw [hcaS.abs]; trivial⟩
  -- the liveness facts
  have hdk : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s' := dbgKeep_of_writes J.blk hW fun b hb =>
    J.notDbg (fun p hp => J.vsxObjW Ap hpc hidx hb hp (fun z h => by cases h))
      (fun c hc => J.vsxNodeW hpc hidx hb hc)
  have hLv' := (LiveDN.simX J hLv J'.xtop rfl rfl rfl (fun p hp => J'.jcov.dead p (J.zD p hp)) F.idle hdk
    (fun sl h => by rw [F.orig] at h; exact h) hsim).1
  have hCP := capPage_defer (nc := nc) hshape hkcu hwf rfl trivial
  have hKs : FbKeep τ σ' := fbKeep_defer hshape hkcu
  have hCSK : CnSlotsKept (L := L) Z.th s s' := by
    intro y hy p' r' gs' g' hy'
    by_cases e : y = cslotAddr (pc.bv, idx)
    · rw [e, hcv0, hcf] at hy'; cases hy'
    · rw [hcap y hy e]; exact hy'
  have hum : σ'.machineState.underlyingMemory = τ.machineState.underlyingMemory := by
    rcases hshape with e | ⟨q, ao, ao', -, -, -, e⟩ <;> rw [hσ', e] <;> rfl
  refine ⟨τu, σ', hmu, by rw [hsc']; exact Set.mem_singleton _, J', hLv', fun u => by rw [F.act]; exact hns u,
    hsg.of_capPage hCP h0 F.irqN F.idle, hp0.of_ppk (PPK.of_fbKeep hKs), hks', hKs, hum, hCSK, ?_⟩
  rw [capAt_capV]; exact congrArg ok hcv5

set_option maxHeartbeats 8000000 in
/-- **The deferred unmap and the delete at `J`** (module docstring). -/
theorem JAtZ.fbDelDeferJ [Fl4Proofs.P1.PlainStore st] {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {τ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a τ)
    (hDP : JDelParts (L := L) arI AR Z.th) (hT : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hARI : ARIface arI AR)
    (hLv : LiveDN (L := L) Z.th H Cs Z.G s τ) (hns : Vs.NoSwitch τ) (hsg : SpecGlob τ) (hp0 : PPR0 τ)
    {sl : Fl4Spec.CslotPtr} (hA : AbsSlot Z.th sl) (hcn : ∃ pc, sl.1 = pc.bv ∧ Z.th pc = some (.cnode sl.2.length))
    {p : U64} {sz : capability.FrameSize} {rt asd va : U64}
    (hc : capAt (L.mem s) (cslotAddr sl) = ok (.Frame p sz rt false true false asd va))
    {root : U64} (hfv : ExceptT.run (Fl4Spec.findVspaceForAsid (Z := Unit) asd.bv) τ = ({(.ok root.bv, τ)}, False))
    {b2 : Bool} {sU sS : S}
    (hu : vspace.unmap_page_unflushed st s root sz va p = ok (b2, sU))
    (hs : obj.Slot.set_cap st (cslotAddr sl) sU (.Frame p sz rt false false false 0#u64 0#u64) = ok sS) :
    cdt.delete st arI sS a (cslotAddr sl) true ⦃ r => r.1 = .Ok () ∧
      ∃ (τu τs τ1 : Fl4Spec.State Unit) (G' : MdbGhost) (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64)
        (D' : Set U64),
      (b2, τu) ∈ (Fl4Spec.unmapPageUnflushed (Z := Unit) (frameSizeOf sz) root.bv va.bv p.bv τ).1 ∧
      ((), τs) ∈ (Fl4Spec.setCap (Z := Unit) (.archObjectCap (.pageCap false p.bv (vmRightsOf rt) .vmNoMap
        (frameSizeOf sz) none)) sl τu).1 ∧
      (.ok (), τ1) ∈ ((Fl4Spec.capDelete (Z := Unit) sl).run τs).1 ∧
      JAtZ (L := L) arI AR (Z.mv G' V') H Cs Ac' Lst' D' r.2.1 r.2.2 τ1 ∧
      LiveDN (L := L) Z.th H Cs G' r.2.1 τ1 ∧ Vs.NoSwitch τ1 ∧ SpecGlob τ1 ∧ PPR0 τ1 ∧ L.ksb r.2.1 = L.ksb s ∧
      FbKeep τ τ1 ∧ τ1.machineState.underlyingMemory = τ.machineState.underlyingMemory ∧
      CnSlotsKept (L := L) Z.th s r.2.1 ⦄ := by
  obtain ⟨pc, hpc1, hpc⟩ := hcn
  obtain ⟨sa, idx⟩ := sl
  simp only at hpc1 hpc
  subst hpc1
  obtain ⟨τu, τs, hmu, hms, J1, hLv1, hns1, hsg1, hp01, hks1, hK1, hum1, hCK1, hc1⟩ :=
    J.fbDeferStepJ arI hDP.archRef hLv hns hsg hp0 hpc hc hfv hu hs
  refine WP.spec_mono (JAtZ.fbDelFrameJN arI J1 hDP hT hnd hARI hLv1 hns1 hsg1 hp01 hA hc1 rfl) ?_
  rintro ⟨r0, s2, a2⟩ ⟨hr0, τ1, G', V', Ac', Lst', D', hd, J2, hLv2, hns2, hsg2, hp02, hks2, hCK2⟩
  obtain ⟨c9, a9, hc9, hca9, hg9⟩ := (J1.xtop.rel.2.1.1).slot_cap (Z := Unit) (sl := (pc.bv, idx)) (p := pc) rfl hpc
  rw [hc1] at hc9; cases eq_of_ok_eq hc9
  have hac9 : a9 = absCap (.Frame p sz rt false false false 0#u64 0#u64) := hca9.abs
  subst hac9
  have hcap9 := (SInvU.getCap_capAt (show (absCap (.Frame p sz rt false false false 0#u64 0#u64), τs) ∈
    (Fl4Spec.getCap (Z := Unit) (pc.bv, idx) τs).1 by rw [hg9]; exact Set.mem_singleton _)).2
  obtain ⟨hK2, hum2⟩ := fbKeep_capDelete_frame hcap9 hd
  exact ⟨hr0, τu, τs, τ1, G', V', Ac', Lst', D', hmu, hms, hd, J2, hLv2, hns2, hsg2, hp02, hks2.trans hks1,
    hK1.trans hK2, hum2.trans hum1, hCK1.trans hCK2⟩

end

end

end Fl4Proofs.P3
