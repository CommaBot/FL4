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
      LiveDN (L := L) Z.th H Cs G' r.2.1 σ' ∧ Vs.NoSwitch σ' ∧ SpecGlob σ' ∧ PPR0 σ' ∧ L.ksb r.2.1 = L.ksb s ⦄ := by
  fail "FB3 OPEN: the one-round frame delete at J (KENTRY-PLAN fb3l)"

end

end

end Fl4Proofs.P3
