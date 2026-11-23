/-
P3 (issue #16, FL4 #71), VSpace FrameBatch (KENTRY-PLAN fb3l): **FL4's `batch_map` at `J`**
against the spec's `fbMap`.

* `fb_root_L4`: the batch's root, named by the spec's `find_vspace_for_asid`, is a PML4 of the
  sets (FL4's `find_vspace_for_asid` at `VsRel`, `PoolsIn`).
* `vsxw_vobj`: a word of `VsXW` is a word of the VSpace objects (`VObj`), so no word of `OObj`
  (TopPlaced's `disj`: the IPC-buffer words, the kernel-global block's domain words).
* `JAtZ.batchMapJ`: from `JAtZ`, `batch_map` (XTopJointFbMapRel's `batch_map_rel` at
  `FootSR TopSR`, `vsFrameHyps_top`) has an `fbMap` outcome of the same kind; on success `JAtZ`
  after at the same sets (as XTopJointVsMap's `JAtZ.vsPostJ` without the restart: `FinXT`,
  `FinXR`, `XTopAt`, `VsSFr`, the writes in `VsXW`, `JAtZ.vsStepJ`), `FbKeep` and `FbFootK`
  (the TCBs' registers by `vsxObjW`, the buffer words by `vsxw_vobj`).
-/
import Fl4Proofs.P3.XTopJointFbMapRel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **The batch's root is a PML4 of the sets** (module docstring). -/
theorem fb_root_L4 {P L4 : Set U64} {s : S} {σ : Fl4Spec.State Unit} (hR : VsRel P (L.mem s) (L.ksb s) σ)
    (hPI : PoolsIn P L4 (L.mem s)) {as1 p1 : U64} (h0 : as1 ≠ 0#u64)
    (hf : ExceptT.run (Fl4Spec.findVspaceForAsid (Z := Unit) as1.bv) σ = ({(.ok p1.bv, σ)}, False)) : p1 ∈ L4 := by
  obtain ⟨r, -, h1, h2⟩ := spec_exists (WP.spec_and (find_vspace_for_asid_rel s σ hR as1 h0)
    (find_vspace_for_asid_L4 s σ hR hPI as1))
  rw [hf] at h1
  have e := congrArg Prod.fst h1
  simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, and_true] at e
  cases r with
  | Ok r1 =>
    simp only [fvRes, Except.ok.injEq] at e
    rw [P1.eq_of_bv e]; exact h2 r1 rfl
  | Err lf => simp [fvRes] at e

/-- **A word of `VsXW` is a word of the VSpace objects.** -/
theorem vsxw_vobj {Z : XSets} {kb : U64} (hP : Placed Z.th) (hVP : VsPlaced Z.P kb)
    (hPP : PtPlaced Z.L4 Z.L3 Z.L2 Z.L1) {x : U64} (hx : IsSlot Z.th x) {b : U64} (hb : VsXW Z kb x b) :
    VObj Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 kb b := by
  rcases hb with (⟨q, hq, i, hi, rfl⟩ | hb) | rfl | rfl
  · exact table_vobj hPP hq hi kb
  · exact vsWrite_vobj hVP hb
  · exact slotW_vobj hP ⟨b, hx, Or.inl rfl⟩ kb
  · exact slotW_vobj hP ⟨x, hx, Or.inr rfl⟩ kb

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 8000000 in
/-- **FL4's `batch_map` at `J`** (module docstring). -/
theorem JAtZ.batchMapJ [Fl4Proofs.P1.PlainStore st] (hA : ArchRefines arI AR) {s : S} {a : A}
    {τ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a τ)
    {pc : U64} {r : Nat} (hpc : Z.th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {p1 as1 : U64} (has1 : as1 ≠ 0#u64) (has2 : as1.val < 2 ^ 20)
    (hf : ExceptT.run (Fl4Spec.findVspaceForAsid (Z := Unit) as1.bv) τ = ({(.ok p1.bv, τ)}, False))
    (op depth a1 cr a2 : U64) (dd : Bool) (cn dcn : capability.Cap) (a0 : U64)
    (b : Fl4Spec.Fl4FrameBatchInvocation) (hbv : b.vspace = p1.bv) (hba : b.asid = as1.bv)
    (hbm : b.mapRights = a1.bv) (hbat : b.attr = a2.bv) :
    vspace.batch_map st arI s a (cslotAddr (pc.bv, idx)) ⟨p1, as1, op, depth, a1, cr, a2, dd, cn, dcn⟩ a0 ⦃ res =>
      (∃ e e', res.1 = .Err e ∧ MapErrRel e e' ∧
        ExceptT.run (Fl4Spec.fbMap (Z := Unit) b (pc.bv, idx) a0.bv) τ = ({(.error e', τ)}, False) ∧
        res.2.1 = s ∧ res.2.2 = a) ∨
      (res.1 = .Ok () ∧ ∃ τ1, ((.ok (), τ1) : Except Fl4Spec.SyscallError Unit × Fl4Spec.State Unit) ∈
          (ExceptT.run (Fl4Spec.fbMap (Z := Unit) b (pc.bv, idx) a0.bv) τ).1 ∧
        JAtZ (L := L) arI AR Z H Cs Ac Lst D res.2.1 res.2.2 τ1 ∧ FbKeep τ τ1 ∧ FbFootK (L := L) Z s res.2.1) ⦄ := by
  have hX := J.xtop
  obtain ⟨hS, hR, hPt, hPI, hCur⟩ := id hX.fin
  obtain ⟨hPl, hCR, hFI, hDR, hMO, hIA, -⟩ := id hX.rel
  obtain ⟨hSt, hSV, -, -, -⟩ := id hCR
  have hA0 : AbsSlot Z.th (pc.bv, idx) := ⟨pc, rfl, Or.inl (by simpa [hidx] using hpc)⟩
  have hxsl : IsSlot Z.th (cslotAddr (pc.bv, idx)) := hA0.isSlot
  obtain ⟨c, hc⟩ := capAt_total (L.mem s) (cslotAddr (pc.bv, idx))
  have hcv0 : capV (L.mem s) (cslotAddr (pc.bv, idx)) = c := capV_of_capAt hc
  have hnat : NativeCap c := by have h := J.ext.nat _ hxsl; rwa [hcv0] at h
  have hok : ∀ p sz rt d m e fa fv, c = .Frame p sz rt d m e fa fv → VCapOK Z.P Z.L4 Z.L3 Z.L2 Z.L1 c := by
    intro p sz rt d m e fa fv he
    have h := J.vsc _ hxsl
    rw [hcv0] at h
    subst he
    exact h.okTab trivial
  have hp1 : p1 ∈ Z.L4 := fb_root_L4 hR hPI has1 hf
  have hH : VsFrameHyps st A arI Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (FootSR st (TopSR st Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1
      Z.N Z.T Z.C Z.E Z.R Z.B Z.c AR) s (VsFootW0 st Z.th Z.L4 Z.L3 Z.L2 Z.L1 s)) :=
    (vsFrameHyps_top hA).foot (s0 := s) (W := VsFootW0 st Z.th Z.L4 Z.L3 Z.L2 Z.L1 s) (fun _ h => h) hS.2.pl
  have hHL : VsFrameHypsL st A arI Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (FootSR st (TopSR st Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1
      Z.N Z.T Z.C Z.E Z.R Z.B Z.c AR) s (VsFootW0 st Z.th Z.L4 Z.L3 Z.L2 Z.L1 s)) :=
    (vsFrameHypsL_top hA).foot (s0 := s) (W := VsFootW0 st Z.th Z.L4 Z.L3 Z.L2 Z.L1 s) (fun _ h => h) hS.2.pl
  refine WP.spec_mono (batch_map_rel hH hHL s a τ hS.2.pl hS.2.vs hS.2.sd hS.2.pt hS.2.ps hS.2.pv hS.2.po
    hSt hSV hR hPt ⟨hS, P1.WritesIn.refl _ _⟩ hpc hidx hc hok hnat hp1 has1 has2 hf op depth a1 cr a2 dd cn dcn a0
    b hbv hba hbm hbat) ?_
  rintro ⟨r0, s', a'⟩ (⟨e, e', h1, h2, h3, h4, h5⟩ | ⟨h1, σ', hmem, ⟨pi, hpi⟩, hSt', hSV', hR', hPt', hSRq, hSF, hLk,
    hK, hFK, cp, csz, crt, cd, cm, ce, cfa, cfv, hcf⟩)
  · exact Or.inl ⟨e, e', h1, h2, h3, h4, h5⟩
  try simp only at h1 hSt' hSV' hR' hPt' hSRq hSF hLk ⊢
  have hu : isUt c = false := by rw [hcf]; rfl
  obtain ⟨hCR', hFI', hMO'⟩ := crelM_after hCR hFI hMO hc hSt' hSV' hSF hLk hK hu
  obtain ⟨hTS', hW0⟩ := id hSRq
  have hks' : L.ksb s' = L.ksb s := hW0.1
  obtain ⟨⟨hSch', hEp', hNt', -⟩, -⟩ := id hTS'
  have hIpc' : IpcRel Z.N Z.T Z.E Z.R Z.B (L.mem s') σ' := IpcRel.of hNt' hEp' (sched_sc hSch')
  have F : VsSFr τ σ' := VsSFr.of_fk (fv_performPageInvocation pi) hpi
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
  have hX' : XTopAt (L := L) AR Z s' a' σ' := by
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
      exact (hLk.2 _ _ _ _ _ (hok _ _ _ _ _ _ _ _ hcf)).toW
    · rw [hcap y hy e]; exact J.vsc y hy
  have J' := J.vsStepJ Ap hpc hidx hX' F hW hcap (by rw [hcv0]; exact hLk.1.1) (by rw [hcv0]; exact hLk.1.2.1)
    (by rw [hcv0]; exact hu) (by rw [hcv0]; exact hLk.1.2.2.2)
    (fun y hy => ⟨(hSF y hy).1, (hSF y hy).2.1⟩) hvc
  refine Or.inr ⟨h1, σ', hmem, J', hFK, fun t ht g => ?_, fun wp hw => ?_⟩
  · have hta : P1.TcbAddr t := J.ip.e.tcb t ht
    have hr := regA_val hta (regIdx_lt g)
    have hrl := regIdx_lt g
    have hal := hta.align
    simp only [Nat.reducePow] at hal
    exact hW.mem_eq (by unfold P1.Aligned; rw [hr]; omega) fun hb => by
      rcases J.vsxObjW Ap hpc hidx hb (J.zH.1 t ht) (fun _ e => by cases e) with e | e <;>
        (try simp only [P1.HKind.bits, Nat.reducePow] at e) <;> omega
  · have hal : P1.Aligned wp.1 := (hS.2.ep.balign wp hw).1
    exact hW.mem_eq hal fun hb => hS.2.disj _
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨wp, hw, le_refl _, by omega⟩)))))))
      (vsxw_vobj hPl hS.2.vs hS.2.pt hxsl hb)

end

end

end Fl4Proofs.P3
