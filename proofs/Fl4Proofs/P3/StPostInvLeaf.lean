/-
P3 (line stpost, generation 8): **the frame-cap invocation's decode arms at stable ghosts**
(the leaves of StPostInvTop's route; scratch/stpost/gen_vspost.py generates `JAtZ.vsPostJSt`).

* `JAtZ.vsPostJSt`: XTopJointVsMap's `JAtZ.vsPostJ` verbatim with the post `JStab Z H Cs` (its two
  exits are `J` itself and `J'` from `vsStepJ`, both `JAtZ` at `Z`: a VSpace map, unmap or ASID
  assignment changes no set).
* **`decode_frameMapJSt`**: a small RAM frame cap (non-EPT) at the label `X86PageMap`: VsThX's
  `decode_invocation_frame_thX` (`hno` vacuous: the frame is small), `vsPostJSt`, `MR` by
  `XCapP.mr` with `MKD.decode_quiet` / `MachT.dec_quiet` (a Frame cap is quiet), never preempted.
* **`decode_cnodeCopyJSt`**: a CNode cap at `CNodeCopy` / `CNodeMint`: XTopCnode's
  `decode_invocation_cnode_copyXS` at `X := JStab Z H Cs` (the primitive steps by `Steps.jatZ`,
  ghosts `Z.mv G' V'`), canonical label (`cnode_canon`, `XCapP.lbl_congr`), never preempted
  (`cnode_noPre_of`), `MR` by `XCapP.mr` with `MKD.decode_cnode_nrd` / `MachT.dec_cnode_q`.

No premise added.
-/
import Fl4Proofs.P3.StPostInv
import Fl4Proofs.P3.StPostEv
import Fl4Proofs.P3.XTopJointKEntry38
import Fl4Proofs.P3.XTopJointVsMap
import Fl4Proofs.P3.XTopJointLiveCn
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section StInvVs
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 8000000 in
/-- (stpost) **`JAtZ.vsPostJ` at stable ghosts** (module docstring). -/
theorem JAtZ.vsPostJSt {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z]
    (hni : Entered σ)
    {ct : U64} (hct : sched.cur_thread st s = ok ct) {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    (hF : FinXR (L := L) AR Z s' a' σ')
    (hV : VsJPost (L := L) Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 Z.G s ar σ s' a' σ') :
    JStab (L := L) arI AR Z H Cs s' a' σ' := by
  rcases hV with ⟨rfl, rfl, rfl⟩ | ⟨hW0, ⟨pc, r, idx, c, hpc, hidx, hc0, hnu, hTI, hSF, hLk, hsp, hOp⟩, hCR', hFI', hMO'⟩
  · exact J.stab
  obtain ⟨s1, σ1, x1, -, hst1, hk, hcur, -, -, -, -, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  have hP := J.xtop.rel.1
  have htcb : Z.th ct = some .tcb := (J.xtop.curTcb hcur).1
  have hact := J.kern.act
  -- FL4's restart
  have hF2 : Frame2 (L := L) s s1 (P1.stA ct) (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) := by
    have h := set_thread_state_frame (L := L) s ct sched.TS_RESTART (stA_al hP htcb) hact.1
    rw [hs1, WP.spec_ok] at h; exact h
  have hSS1 : SlotsSame Z.th (L.mem s) (L.mem s1) := by
    have h := set_thread_state_slots (L := L) Z.th hP s ct sched.TS_RESTART htcb hact
    rw [hs1, WP.spec_ok] at h; exact h
  have hkc1 : L.ksb s1 = L.ksb s ∧ L.cpu s1 = L.cpu s := by
    have h := set_thread_state_cases (L := L) s ct sched.TS_RESTART
    rw [hs1, WP.spec_ok] at h
    rcases h with rfl | rfl <;> simp
  -- the spec's step and `XTopAt` after
  have F : VsSFr σ1 σ' := vsSFr_of_post hst1 hsp
  have hks' : L.ksb s' = L.ksb s := hW0.1
  have hX' : XTopAt (L := L) AR Z s' a' σ' := by
    obtain ⟨hFin, ⟨G0, hPl, -, -, hD, -, hIA, hSA⟩, hE⟩ := hF
    obtain ⟨⟨⟨hSch, hEp, hNt, -⟩, -⟩, -⟩ := id hFin
    exact ⟨hFin, ⟨hPl, hCR', hFI', hD, by rw [hks']; exact hMO', hIA, hSA⟩, IpcRel.of hNt hEp (sched_sc hSch), hE⟩
  -- the TCBs' state words and the action word, pinned
  have pinS : ∀ t, Z.th t = some .tcb → L.mem s' (P1.stA t) = L.mem s1 (P1.stA t) := by
    intro t ht
    have htT := J.thT t ht
    obtain ⟨y1, hk1, hR1⟩ := J1.xtop.ipc.tcb t htT
    obtain ⟨y, hky, hRy⟩ := hX'.ipc.tcb t htT
    obtain ⟨y', hy', hc⟩ := F.tcbF hk1
    rw [hky] at hy'; cases hy'
    have h1 : (L.mem s' (tStA t)).val = (L.mem s1 (tStA t)).val := by rw [hRy.st, hR1.st, hc.st]
    rw [stA_tStA]; exact UScalar.eq_of_val_eq h1
  have pinA : L.mem s' (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) =
      L.mem s1 (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) := by
    have a1 := J1.xtop.fin.1.1.1.act
    have a2 := hX'.fin.1.1.1.act
    rw [F.act] at a2
    have e := ActRel.det a2 a1
    obtain ⟨Q, R, hc, -⟩ := J.xtop.fin.1.1.1.lists
    unfold nodeW at e
    rw [P1.nodeAt_of_ksb hks', P1.nodeAt_of_ksb hkc1.1, ← hc.cur] at e
    exact e
  -- the slots
  have hSlot : ∀ y, IsSlot Z.th y → L.mem s' (wordOf y 16#u64) = L.mem s1 (wordOf y 16#u64) ∧
      L.mem s' (wordOf y 24#u64) = L.mem s1 (wordOf y 24#u64) ∧
      (y ≠ cslotAddr (pc.bv, idx) → L.mem s' y = L.mem s1 y ∧ L.mem s' (wordOf y 8#u64) = L.mem s1 (wordOf y 8#u64)) := by
    intro y hy
    obtain ⟨a0, a8, a16, a24⟩ := hSS1 y hy
    obtain ⟨b16, b24, bx⟩ := hSF y hy
    exact ⟨by rw [b16, a16], by rw [b24, a24], fun hne => ⟨by rw [(bx hne).1, a0], by rw [(bx hne).2, a8]⟩⟩
  -- FL4's writes after the restart
  have hW : P1.WritesIn st s1 s' (VsXW Z (L.ksb s1) (cslotAddr (pc.bv, idx))) := by
    refine ⟨hks'.trans hkc1.1.symm, hW0.2.1.trans hkc1.2.symm, fun b hb hn => ?_⟩
    have hslw : ∀ y, IsSlot Z.th y → ∀ k : U64, Off k → b = wordOf y k → L.mem s' b = L.mem s1 b := by
      intro y hy k hk e
      subst e
      obtain ⟨h16, h24, hne⟩ := hSlot y hy
      rcases hk with rfl | rfl | rfl | rfl
      · by_cases ex : y = cslotAddr (pc.bv, idx)
        · exact (hn (Or.inr (Or.inl (by rw [wordOf_zero, ex])))).elim
        · rw [wordOf_zero]; exact (hne ex).1
      · by_cases ex : y = cslotAddr (pc.bv, idx)
        · exact (hn (Or.inr (Or.inr (by rw [ex])))).elim
        · exact (hne ex).2
      · exact h16
      · exact h24
    by_cases hb0 : VsFootW st Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 s b
    · rcases hb0 with ⟨y, hy, e | e⟩ | ⟨y, k, hy, hk, e⟩ | hpt | hvw | ⟨t, ht, e⟩ | e
      · exact hslw y hy 0#u64 (Or.inl rfl) (by rw [wordOf_zero]; exact e)
      · exact hslw y hy 8#u64 (Or.inr (Or.inl rfl)) e
      · exact hslw y hy k hk e
      · exact (hn (Or.inl (Or.inl hpt))).elim
      · exact (hn (Or.inl (Or.inr (by rw [hkc1.1]; exact hvw)))).elim
      · subst e; exact pinS t ht
      · subst e; exact pinA
    · have e0 : L.mem s' b = L.mem s b := hW0.2.2 b hb hb0
      have e1 : L.mem s1 b = L.mem s b := hF2 b hb (fun e => hb0 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨ct, htcb, UScalar.eq_of_val_eq e⟩)))))) (fun e => hb0 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (UScalar.eq_of_val_eq e)))))))
      rw [e0, e1]
  -- the invoked slot's cap
  have hcv0 : capV (L.mem s) (cslotAddr (pc.bv, idx)) = c := capV_of_capAt hc0
  have hA : AbsSlot Z.th (pc.bv, idx) := ⟨pc, rfl, Or.inl (by simpa [hidx] using hpc)⟩
  have hcv1 : capV (L.mem s1) (cslotAddr (pc.bv, idx)) = c := by rw [hSS1.capV hA.isSlot]; exact hcv0
  have hcap : ∀ y, IsSlot Z.th y → y ≠ cslotAddr (pc.bv, idx) → capV (L.mem s') y = capV (L.mem s1) y := by
    intro y hy hne
    obtain ⟨-, -, h⟩ := hSlot y hy
    unfold capV; rw [(h hne).1, (h hne).2]
  have Ap : VsApart (L := L) Z H Cs s1 := jVsApartHyp arI Z H Cs Ac1 Lst1 D1 s1 ar σ1 rfl J1
  -- the VSpace caps placed: the invoked slot's new cap from its old one
  -- (`VsLike`, `JAtZ.vsc` and the post's `TabIn`), the other slots kept
  have hvc : Vs.VsSlotsW Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.mem s') := by
    intro y hy
    by_cases e : y = cslotAddr (pc.bv, idx)
    · rw [e]
      have hok : VCapOK Z.P Z.L4 Z.L3 Z.L2 Z.L1 c := by
        by_cases hn : c = .Null
        · subst hn; trivial
        · have hw := J.vsc _ hA.isSlot
          rw [capV_of_capAt hc0] at hw
          exact hw.okTab hTI
      exact (hLk.2 _ _ _ _ _ hok).toW
    · rw [hcap y hy e]; exact J1.vsc y hy
  -- (F1 stage 5, item 4) `VsNamed` after, from the op's fact at `J` (`Vs.VsNamed.ofOpF`)
  have hvn : Z.vx = ∅ → Vs.VsNamed Z.th (L.mem s') (L.ksb s') := fun hvx => by
    obtain ⟨hPl, ⟨-, -, hML, -, hMI⟩, hFI0, -⟩ := J.xtop.rel
    have hR' : Vs.VsRel Z.P (L.mem s') (L.ksb s) σ' := by rw [← hks']; exact hX'.fin.2.1
    have h := (J.carry.vsNamed hvx).ofOpF J.vsc J.xtop.fin.2.1 J.xtop.fin.2.2.1 J.xtop.fin.2.2.2.1 J.xtop.fin.1.2.pt
      hR' hX'.fin.2.2.1 hA.isSlot hcv0 hSF hOp (fun hf hk => by
        have hk' : Vs.VKey c ≠ none := by rw [← hcv0]; exact hk
        have hnz : NeedsFin c ∧ isZb c = false := by
          cases c <;> first | exact absurd rfl hk' | exact ⟨Or.inl ⟨trivial, rfl⟩, rfl⟩
        have hx0 : capV (L.mem s) (cslotAddr (pc.bv, idx)) ≠ .Null := fun e => hk (by rw [e]; rfl)
        exact Vs.huq_of_finF hPl hML hMI hFI0 ((hML.members _).2 ⟨hA.isSlot, _, capAt_capV _ _, hx0⟩)
          (by rw [hcv0]; exact hnz.1) (by rw [hcv0]; exact hnz.2) hf hk)
    rw [hks']; exact h
  have J' := J1.vsStepJ Ap hpc hidx hX' F hW hcap (by rw [hcv1]; exact hLk.1.1) (by rw [hcv1]; exact hLk.1.2.1)
    (by rw [hcv1]; exact hnu) (by rw [hcv1]; exact hLk.1.2.2.2)
    (fun y hy => ⟨(hSlot y hy).1, (hSlot y hy).2.1⟩) hvc hvn
  exact J'.stab

end StInvVs

section StInvDec
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

theorem lbl_map_ne_ept : fl4_abi.label.X86PageMap ≠ fl4_abi.label.X86PageMapEPT := by
  unfold fl4_abi.label.X86PageMap fl4_abi.label.X86PageMapEPT; decide
theorem lbl_map_ne_ds : fl4_abi.label.X86PageMap ≠ fl4_abi.label.X86PageDeriveSubframe := by
  unfold fl4_abi.label.X86PageMap fl4_abi.label.X86PageDeriveSubframe; decide
theorem lbl_map_ne_ga : fl4_abi.label.X86PageMap ≠ fl4_abi.label.X86PageGetAddress := by
  unfold fl4_abi.label.X86PageMap fl4_abi.label.X86PageGetAddress; decide
theorem lbl_map_ne_tac : fl4_abi.label.X86PageMap ≠ fl4_abi.label.X86PageTestAndClearAccessed := by
  unfold fl4_abi.label.X86PageMap fl4_abi.label.X86PageTestAndClearAccessed; decide

set_option maxHeartbeats 8000000 in
/-- (stpost) **A small RAM frame cap at `X86PageMap`, stable ghosts, `MR` after** (module docstring). -/
theorem decode_frameMapJSt [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z] (hni : Entered σ) (hRef : ArchRefines arI AR)
    (hA : P0.ArchTotal arI) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR) (hR : MR ar σ.machineState)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    {pc : U64} {r : Nat} (hpc : Z.th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {p rt asid va : U64} {m : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.Frame p .Small rt false m false asid va))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hex : JVsExtra (L := L) Z s extra excaps)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    XCapP (L := L) arI (JStabM (L := L) arI AR MR Z H Cs) (fun _ _ _ => False) s ar σ fl4_abi.label.X86PageMap
      length (cslotAddr (pc.bv, idx)) (.Frame p .Small rt false m false asid va) blk call don fp buf extra
      fl4_abi.label.X86PageMap.bv (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, htcb⟩ := J.ctTcb arI hct
  obtain ⟨-, hCR, hFI, hDR, hMO, hIA, -⟩ := hX.rel
  have hVC := J.vsc.caps J.xtop.rel.2.1.2.2.1
  have h := decode_invocation_frame_thX arI Z.th s ar σ Z.G hCR hFI J.ut hMO hRef hX.fin.1
    hX.fin.2.2.2.1 hX.fin.2.2.2.2 hX.fin.2.1 hX.fin.2.2.1 hVC fl4_abi.label.X86PageMap _
    (frame_label _ lbl_map_ne_ept) (getAddress_label _).2 length buf ct hct hcur htcb
    J.kern.act (J.curRun.run hni) args hlen hargs hpc hidx hcap (Or.inl trivial) (fun e => by cases e)
    extra excaps hex.hext hex.hxs blk call don fp ci buffer hDR hX.esa hIA.dom
  have hX1 : XCap (L := L) arI (JStab (L := L) arI AR Z H Cs) s ar σ fl4_abi.label.X86PageMap length
      (cslotAddr (pc.bv, idx)) (.Frame p .Small rt false m false asid va) blk call don fp buf extra
      fl4_abi.label.X86PageMap.bv (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer ct :=
    XCap.imp arI h fun _ _ _ h => J.vsPostJSt hni hct h.1 (h.2 lbl_map_ne_ds lbl_map_ne_ga lbl_map_ne_tac)
  have hq : QuietF (.Frame p .Small rt false m false asid va) := trivial
  exact XCapP.mr hM (XCap.toPN arI hX1 (specDec_noPreK (by trivial)))
    (MKD.decode_quiet L.total hA hKD hq hR (fun _ _ _ e => by cases e))
    (fun inv hd => MachT.dec_quiet fp _ _ ci _ (absCap _) excaps buffer (quietS_of hq) σ _ hd.1 inv rfl)

set_option maxHeartbeats 8000000 in
/-- (stpost) **A CNode cap at `CNodeCopy` / `CNodeMint`, stable ghosts, `MR` after** (module
docstring). -/
theorem decode_cnodeCopyJSt (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z] (hni : Entered σ) (hARI : ARIface arI AR)
    (hA : P0.ArchTotal arI) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR) (hR : MR ar σ.machineState)
    (hsg : SpecGlob σ)
    (lbl : U64) (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (sl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th sl) (p r gs g : U64)
    (hsc : capV (L.mem s) (cslotAddr sl) = .CNode p r gs g)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hex : ExtraRel2 Z.th (L.mem s) (exAt extra 0) (exAt extra 1) (excaps.map Prod.fst))
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    XCapP (L := L) arI (JStabM (L := L) arI AR MR Z H Cs) (fun _ _ _ => False) s ar σ lbl length (cslotAddr sl)
      (.CNode p r gs g) blk call don fp buf extra lbl.bv (args.map UScalar.bv) ci sl excaps buffer ct := by
  obtain ⟨sl', hl', hd⟩ := cnode_canon lbl
  have hcp : 28 ≤ lbl.val ∧ lbl.val ≤ 32 := by
    rcases hl with rfl | rfl <;> simp [fl4_abi.label.CNodeCopy, fl4_abi.label.CNodeMint]
  have hX := J.xtop
  obtain ⟨hcur, -⟩ := J.curEq hct
  obtain ⟨hwf, hcv⟩ := slot_cap_wf hX hAs hsc
  have hZB := J.zNoBlk hsg
  have hX0 : XCapP (L := L) arI (JStab (L := L) arI AR Z H Cs) (fun _ _ _ => False) s ar σ lbl length
      (cslotAddr sl) (.CNode p r gs g) blk call don fp buf extra sl' (args.map UScalar.bv) ci sl excaps buffer ct :=
    XCap.toPN arI (decode_invocation_cnode_copyXS arI s ar σ hX (J.curRun.run hni)
      (X := JStab (L := L) arI AR Z H Cs) J.stab
      (fun _ _ _ h => by
        obtain ⟨G', V', Ac', Lst', D', J', -⟩ := Steps.jatZ arI hARI.toMask (jStepHyps arI) h rfl J hZB
        exact ⟨G', V', Ac', Lst', D', J'⟩)
      (fun _ _ _ h => by
        obtain ⟨_, _, _, _, _, J'⟩ := h
        exact ⟨_, J'.xtop⟩) lbl hcp sl' hl'
      length buf ct hct args hlen hargs p r gs g hwf hcv ⟨cslotAddr sl, hAs.isSlot, hsc⟩ extra (exAt extra 0)
      (exAt extra 1) (exAt_idx0 extra) (exAt_idx1 extra) excaps hex J.kern.act hcur (cslotAddr sl) blk call don fp
      ci sl buffer) (cnode_noPre_of hl' (by omega))
  have hr : lbl ≠ fl4_abi.label.CNodeRevoke := fun e => by rw [e, lbl_revoke_val] at hcp; omega
  have hd' : lbl ≠ fl4_abi.label.CNodeDelete := fun e => by rw [e, lbl_delete_val] at hcp; omega
  have hsr : Fl4Spec.genInvocationType sl' ≠ .cnodeRevoke := by
    rw [hl']; unfold cnodeLabelOf
    split_ifs <;> first | (intro e; cases e; done) | (exfalso; omega)
  have hsd : Fl4Spec.genInvocationType sl' ≠ .cnodeDelete := by
    rw [hl']; unfold cnodeLabelOf
    split_ifs <;> first | (intro e; cases e; done) | (exfalso; omega)
  refine XCapP.lbl_congr arI (specDec_cnode p r gs g hd) ?_
  exact XCapP.mr hM hX0 (MKD.decode_cnode_nrd L.total hA hKD hr hd' hR)
    (fun inv hdc => MachT.dec_cnode_q fp sl' _ ci sl _ _ _ excaps buffer hsr hsd σ _ hdc.1 inv rfl)

end StInvDec

end

end Fl4Proofs.P3
