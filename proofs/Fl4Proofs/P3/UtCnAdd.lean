/-
P3 (DESIGN.md §9), untyped: **`XTopAt` across a retype that grows the typed
heap** (the no-reset retype of CNodes at `J`, handoff/utj.md "uttypes (line
ut29-)").

* `XTopAt.addStepT`: `XTopAt.addStepW` with the typed heap grown to `th'`
  (`ThX`: the window's new CNodes or TCBs) and FL4 writing the window's words
  (the new objects' zeroed slots); the window's words are none the relations
  read (`¬ OObj`), none of the VSpace's or `th`'s objects (`¬ VObj`) and miss
  the kernel-state block, so the placement facts move to `th'`
  (`TopPlaced.grow`, `IpcApart.grow`, `ScApart.grow`, `CurOK.grow`).
-/
import Fl4Proofs.P3.UtCnGrow
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P1

noncomputable section

section Add
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {σ σ' : Fl4Spec.State Unit} {W : Fl4Spec.ObjRef → Prop} {o : Fl4Spec.ObjRef → Fl4Spec.KernelObject}

set_option maxHeartbeats 4000000 in
/-- **`XTopAt` across fresh objects, a CNode-only step, writes to a window
and the typed heap grown over it** (`XTopAt.addStepW` at `th'`). -/
theorem XTopAt.addStepT {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s s' : S} {a : A}
    {σB : Fl4Spec.State Unit} {th' : TypedHeap} {Aw k w n us : Nat}
    (hX : XTopAt (L := L) AR Z s a σ) (hT : ThX Z.th th' Aw k w n us)
    (hks : ∀ kd, thKindN n us = some kd → objSize kd ≤ k) (hk0 : 0 < k) (hP' : Placed th')
    (hpos : ∀ q kd, Z.th q = some kd → 0 < objSize kd)
    (hw : P1.WritesIn st s s' (fun b => Sched.SlotWd Z.th b ∨ (Aw ≤ b.val ∧ b.val < Aw + w * k)))
    (hWin : ∀ b : U64, Aw ≤ b.val → b.val < Aw + w * k → ¬ OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b ∧
      ¬ VObj Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s) b)
    (hWk : Aw + w * k ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ Aw)
    (hA : Sched.SpecAdd σ σB W o) (ho : ∀ p, W p → ∀ x n, o p ≠ .schedContext x n)
    (hcn : CnK σB σ') (hkc : KeepC σB σ') {G' : MdbGhost} (hCR : CRel th' (L.mem s') σ' G')
    (hFI : FinInv th' (L.mem s') σ' G') (hMO : MdbOKV (L.ksb s) (L.mem s') G')
    (hTS : ∀ t, Z.th t = some .tcb → ∀ p asid, capAt (L.mem s') (slotOf t 1) = ok (.Pml4 p true asid) →
      capAt (L.mem s) (slotOf t 1) = ok (.Pml4 p true asid)) :
    XTopAt (L := L) AR { Z with th := th', G := G' } s' a σ' := by
  obtain ⟨⟨hS, hR, hPt, hPI, hCO⟩, ⟨hPl, -, -, hD, -, hIA, hSA⟩, -, hE⟩ := hX
  obtain ⟨hO, hms, har⟩ := ostep_of_cnk hcn hkc
  have hP := hS.2
  have hk : L.ksb s' = L.ksb s := hw.1
  have hSB := TopSR.specAdd hS hA ho
  have hz := hA.szKeep ho
  have hkW : ∀ b, P1.Aligned b → ¬ Sched.SlotWd Z.th b → ¬ (Aw ≤ b.val ∧ b.val < Aw + w * k) →
      L.mem s' b = L.mem s b :=
    fun b hb h1 h2 => hw.2.2 b hb (fun h => h.elim h1 h2)
  have hS' := TopSR.step (Rw := fun b => Aw ≤ b.val ∧ b.val < Aw + w * k) (Rg := fun _ => False) hSB hw.1 hw.2.1
    (fun b hb hv hr => hkW b hb (fun h => hv (slotWd_vobj hPl h)) hr)
    (fun b hb ho' => (hWin b hb.1 hb.2).1 (OObj.of_szKeep hz ho')) hO (fun _ h => h.elim)
    (fun wp _ => by rw [hms]) (fun h => by rw [har]; exact h)
  have hSz : Sched.SzKeep σ σ' := fun p x n hp => by
    obtain ⟨x1, h1⟩ := SzKeep.of_keepC hkc p x n hp
    exact hz p x1 n h1
  have har' : σ'.archState = σ.archState := har.trans hA.arch
  have hvw : ∀ b, VsWrite Z.P (L.ksb s) b → L.mem s' b = L.mem s b := fun b hb =>
    hkW b (hP.vo b hb).1 (fun h => slotWd_inObj hPl h (hP.vo b hb))
      (fun h => (hWin b h.1 h.2).2 (vsWrite_vobj hP.vs hb))
  have hcur : σ'.curThread = σ.curThread := hO.ct.trans hA.f.2.2.1
  have hkeep : ∀ q k, σ.kheap q = some k → (∀ r cs, k ≠ .cnode r cs) → σ'.kheap q = σ.kheap q := by
    intro q k hq hnc
    rcases hkc q with e | ⟨r, cs, cs', h1, -⟩
    · rw [e, hA.kold hq, hq]
    · rw [hA.kold hq] at h1; cases h1; exact absurd rfl (hnc r cs)
  have hab : Fl4Spec.AbstractState.domainList σ'.toAbstractState = σ.domainList ∧
      Fl4Spec.AbstractState.domainStartIndex σ'.toAbstractState = σ.domainStartIndex := by
    refine ⟨?_, ?_⟩
    · have e1 := congrArg Fl4Spec.AbstractState.domainList hcn.1
      have e2 := congrArg Fl4Spec.AbstractState.domainList hA.abs
      exact e1.trans e2
    · have e1 := congrArg Fl4Spec.AbstractState.domainStartIndex hcn.1
      have e2 := congrArg Fl4Spec.AbstractState.domainStartIndex hA.abs
      exact e1.trans e2
  -- the window's words at the state after (the base kept, SC sizes kept)
  have hWo' : ∀ b : U64, Aw ≤ b.val → b.val < Aw + w * k → ¬ OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ' b := by
    intro b h1 h2 hob
    refine (hWin b h1 h2).1 (OObj.of_szKeep hSz ?_)
    exact OObj.of_same (σ := σ') (σ' := σ') hk rfl hob
  have hWv' : ∀ b : U64, Aw ≤ b.val → b.val < Aw + w * k → ¬ VObj Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s') b := by
    intro b h1 h2; rw [hk]; exact (hWin b h1 h2).2
  have hWk' : Aw + w * k ≤ (L.ksb s').val ∨ (L.ksb s').val + 13568 ≤ Aw := by rw [hk]; exact hWk
  refine ⟨⟨⟨hS'.1, TopPlaced.grow hS'.2 hT hks hP' hWo' hWv' hWk'⟩, ?_, ?_, fun q hq lo hl => ?_, ?_⟩,
    ⟨hP', hCR, hFI, ?_, by rw [hk]; exact hMO,
    IpcApart.grow (σ := σ') (by rw [hk]; exact hIA) hT hks hP' hWo' hWk', ScApart.grow (s := s') (hSA.mono hSz) hT hks hP' hWo'⟩,
    IpcRel.of hS'.1.2.2.1 hS'.1.2.1 (sched_sc hS'.1.1), hE.mono hk hSz⟩
  · rw [hk]
    refine hR.frame hvw (by rw [har']) fun p hp => ?_
    obtain ⟨f, hf, -⟩ := hR.pool p hp
    exact hkeep _ _ hf (fun r cs e => by cases e)
  · refine hPt.frame (fun b hb => hkW b (hP.po b hb).1 (fun h => slotWd_inObj hPl h (hP.po b hb)) (fun h => ?_))
      fun q hq => ?_
    · obtain ⟨q, hq, i, hi, e⟩ := hb
      exact (hWin b h.1 h.2).2 (e ▸ table_vobj hP.pt hq hi _)
    rcases hq with hq | hq | hq | hq
    · obtain ⟨g, hg, -⟩ := hPt.l4 q hq; exact hkeep _ _ hg (fun r cs e => by cases e)
    · obtain ⟨g, hg, -⟩ := hPt.l3 q hq; exact hkeep _ _ hg (fun r cs e => by cases e)
    · obtain ⟨g, hg, -⟩ := hPt.l2 q hq; exact hkeep _ _ hg (fun r cs e => by cases e)
    · obtain ⟨g, hg, -⟩ := hPt.l1 q hq; exact hkeep _ _ hg (fun r cs e => by cases e)
  · have hwv : VsWrite Z.P (L.ksb s) (peA q lo) := Or.inr ⟨q, hq, lo, hl, rfl⟩
    rw [hvw _ hwv]; exact hPI q hq lo hl
  · obtain ⟨t, h1, h2, h3⟩ := hCO
    exact CurOK.grow ⟨t, h1.trans hcur.symm, h2, fun p asid hc => h3 p asid (hTS t h2 p asid hc)⟩ hT hk0 hpos
  · rw [hk]
    refine hD.frame (fun o ho => ?_) hab.1 hab.2
    have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by have := hP.vs.ksb_fit; omega
    have h8 := domOffs_lt' ho
    have hv := ksW_val (kb := L.ksb s) (o := o) (by omega)
    refine hkW _ (by unfold P1.Aligned; rw [hv]; have := hP.vs.ksb_al; omega) (fun h => ?_) (fun h => ?_)
    · obtain ⟨y, hy, g1, g2⟩ := slotWd_range hPl h
      exact hIA.ks _ (by rw [hv]; omega) (by rw [hv]; omega) (by rw [hv]; omega) y hy ⟨g1, g2⟩
    · rcases hWk with h' | h' <;> rw [hv] at h <;> omega

end Add

end

end Fl4Proofs.P3
