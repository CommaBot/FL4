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
flush's machine state (`JAtZ.arFrS`, `XTopAt.msAR'`). OPEN (scratch stub).
-/
import Fl4Proofs.P3.XTopJointFbDelFrameN
import Fl4Proofs.P3.SpecFbKeepDel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop}

set_option maxHeartbeats 8000000 in
/-- **The deferred unmap and the delete at `J`** (module docstring). OPEN. -/
theorem JAtZ.fbDelDeferJ [Fl4Proofs.P1.PlainStore st] {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {τ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a τ)
    (hDP : JDelParts (L := L) arI AR Z.th) (hT : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hARI : ARIface arI AR)
    (hLv : LiveDN (L := L) Z.th H Cs Z.G s τ) (hns : Vs.NoSwitch τ) (hsg : SpecGlob τ) (hp0 : PPR0 τ)
    {sl : Fl4Spec.CslotPtr} (hA : AbsSlot Z.th sl) {p : U64} {sz : capability.FrameSize} {rt asd va : U64}
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
  fail "FB3 OPEN: the deferred unmap at J (KENTRY-PLAN fb3l)"

end

end

end Fl4Proofs.P3
