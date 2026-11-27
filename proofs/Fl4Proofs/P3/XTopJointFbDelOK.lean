/-
P3 (issue #16, FL4 #71), VSpace FrameBatch: **MachKeepG4d's `FbDelOK` at
every batch entry** (KENTRY-PLAN fb3m "To finish" (2), fb3l): from the loop's
invariant `FbMidJ` and the decode's `FbCtx`, the slot facts MachKeepG4d's
`MKD.vspace_frame_batch_entry` needs at the entry's state.

* `del`: the DELETE target found by `lookup_target_slot` is a CNode slot of
  the typed heap (Lookup's `lookup_slot_for_cnode_op_refines`), so writing
  the cleared frame cap (`EncWf` from the read frame's) and reading it back
  gives it (MoveRefine's `capAt_wrCap`).
* `cpy`: the COPY_MAP source holds a frame cap (an MDB member, `MdbLinks`),
  the destination is empty (`ensure_empty_slot` passed: no member), the
  derived cap is the masked frame with its mapping cleared (`EncWf`), so the
  insert leaves it in the destination (CnFrame's `insert_trace`).
-/
import Fl4Proofs.P3.XTopJointFbDefs
import Fl4Proofs.P3.MachKeepG4d
import Fl4Proofs.P3.MoveRefine
import Fl4Proofs.P3.CnFrame
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop}

/-- A slot `lookup_slot_for_cnode_op` returns from a related state is an abstract CNode slot. -/
theorem fb_lookup_abs {th : TypedHeap} {x : S} {τ : Fl4Spec.State Unit}
    (hSt : StateRel th (L.mem x) τ) (hSV : SlotsValid th (L.mem x)) (bb : Bool) (root : capability.Cap)
    (hw : CapWf root) (hv : CapValid th root) (cptr depth : U64) (val : obj.Slot)
    (he : cspace.lookup_slot_for_cnode_op st x bb root cptr depth = ok (.Ok val)) :
    ∃ sl, val = cslotAddr sl ∧ AbsSlot th sl := by
  have h := lookup_slot_for_cnode_op_refines (Z := Unit) th x τ hSt hSV bb root (absCap root) ⟨hw, rfl⟩ hv
    cptr depth
  rw [he, WP.spec_ok] at h
  obtain ⟨e, -, hr⟩ := h
  cases e with
  | error _ => simp only [SlotResRel] at hr
  | ok sl =>
    simp only [SlotResRel] at hr
    obtain ⟨rfl, p, hp1, hp, -⟩ := hr
    exact ⟨sl, rfl, p, hp1, Or.inl hp⟩

/-- `ensure_empty_slot` passed: the slot holds the null cap. -/
theorem fb_ensure_null {x : S} {val : obj.Slot} (h : cdt.ensure_empty_slot st x val = ok (.Ok ())) :
    capAt (L.mem x) val = ok .Null := by
  unfold cdt.ensure_empty_slot at h
  rw [slot_cap_eq] at h
  obtain ⟨cd, hcd⟩ := capAt_total (L.mem x) val
  rw [hcd, bind_ok] at h
  by_cases hn : cd = .Null
  · rw [hn] at hcd; exact hcd
  · rw [cap_is_null_ne hn, bind_ok] at h
    simp at h

set_option maxHeartbeats 8000000 in
/-- **`FbDelOK` at a batch entry from `FbMidJ`** (module docstring). -/
theorem FbMidJ.delOK {σ : Fl4Spec.State Unit} {th0 : TypedHeap} {ct buf : U64} {args : List U64}
    {bt : vspace.Batch} {b : Fl4Spec.Fl4FrameBatchInvocation} (C : FbCtx σ th0 args bt b)
    {x : S} {a : A} {τ : Fl4Spec.State Unit} (hM : FbMidJ (L := L) (AR := AR) arI σ th0 ct buf args x a τ)
    (w0 w1 : U64) : FbDelOK st x bt w0 w1 := by
  obtain ⟨⟨Z1, H1, Cs1, Ac1, Lst1, D1, hth, -, -, J, -⟩, -⟩ := hM
  have hP : Placed Z1.th := J.xtop.rel.1
  obtain ⟨hSt, hSV, hMl, -, -⟩ := J.xtop.rel.2.1
  have hcv : CapValid Z1.th bt.cnode := by rw [hth]; exact C.hcv
  have hdcv : CapValid Z1.th bt.dest_cnode := by rw [hth]; exact C.hdcv
  refine ⟨?_, ?_⟩
  · intro val hval c0 f hc0 hf s' s'' hs''
    obtain ⟨sl, rfl, hAs⟩ := fb_lookup_abs (τ := τ) hSt hSV false bt.cnode C.hcw hcv w0 bt.depth _ hval
    have hy := hAs.isSlot
    rw [slot_cap_eq] at hc0
    have he0 : EncWf c0 := by rw [capAt_words] at hc0; exact decode_encWf hc0
    cases c0 <;> simp [vspace.as_frame] at hf
    subst hf
    rename_i p sz r d m e asd va
    have hEw : EncWf (.Frame p sz r d false false 0#u64 0#u64) := ⟨he0.1, he0.2.1, by simp, by simp⟩
    have hs := set_cap_spec (L := L) (cslotAddr sl) s' (.Frame p sz r d false false 0#u64 0#u64)
    rw [hs'', WP.spec_ok] at hs
    rw [slot_cap_eq, hs]
    have h1 := capAt_wrCap (L := L) hP s' hy hEw hy
    rw [if_pos rfl] at h1
    exact h1
  · intro val val1 hval hee hval1 c0 m c f rt s' hc0 hf hm hd hins
    obtain ⟨dsl, rfl, hAd⟩ := fb_lookup_abs (τ := τ) hSt hSV false bt.dest_cnode C.hdcw hdcv w1 bt.depth _ hval
    obtain ⟨ssl, rfl, hAs⟩ := fb_lookup_abs (τ := τ) hSt hSV true bt.cnode C.hcw hcv w0 bt.depth _ hval1
    rw [slot_cap_eq] at hc0
    have hnull := fb_ensure_null (L := L) hee
    have hc0n : c0 ≠ .Null := by rintro rfl; simp [vspace.as_frame] at hf
    have hsrcm : cslotAddr ssl ∈ Z1.G.chains.flatten := (hMl.members _).2 ⟨hAs.isSlot, c0, hc0, hc0n⟩
    have hdnm : cslotAddr dsl ∉ Z1.G.chains.flatten := fun h => by
      obtain ⟨-, c1, h1, hn⟩ := (hMl.members _).1 h
      rw [hnull] at h1
      exact hn (eq_of_ok_eq h1).symm
    have he0 : EncWf c0 := by rw [capAt_words] at hc0; exact decode_encWf hc0
    have hcw0 : CapWf c0 := (slot_cap_wf J.xtop hAs (capV_of_capAt hc0)).1
    cases c0 <;> simp [vspace.as_frame] at hf
    rename_i p sz r d mm e asd va
    simp only [capability.mask_cap_rights] at hm
    obtain ⟨mv, hmv, -, hm3, -⟩ := vm_mask r hcw0 rt
    rw [hmv, bind_ok] at hm
    have hm' := eq_of_ok_eq hm
    subst hm'
    simp only [objects.derive_cap] at hd
    have hc := eq_of_ok_eq hd
    cases hc
    have hEc : EncWf (.Frame p sz mv d false false 0#u64 0#u64) := ⟨he0.1, by omega, by simp, by simp⟩
    rw [insert_with_cap_eq (L := L) x _ _ _ _ hc0] at hins
    have htr := Vs.insert_trace hP x Z1.G hMl hsrcm hAd.isSlot hdnm hc0 _ hEc
    rw [hins, WP.spec_ok] at htr
    rw [slot_cap_eq, capAt_capV, htr.2.2.1]

end

end

end Fl4Proofs.P3
