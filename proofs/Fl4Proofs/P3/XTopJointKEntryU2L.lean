/-
P3 (issue #16, g5j): **`kernel_entry_reachU2L`** = m73's `kernel_entry_reachU2F`
without `LargeFrOK` [J] on its native-syscall clause.

`LargeFrOK` (XTopJointKEntry36E, `JFramePath.hno` for every MDB slot) is the
range fact `DeriveSubframe`'s MDB insertion reads (`InsFCtx.k2`: a cap that
sees a 4 KiB alias by `same_region_as` sees the large frame). g5j restricted it
(and `JFramePath.hno`, `InsFCtx.hno`, `SubRel.no` and the `hno` arguments
between them) to physical caps: a non-physical cap's `same_region_as` test
against a frame is false either way, and for a non-physical cap (range
`[0, 0]`) the old form asked the large frame's base to be nonzero, which no
carried fact states. In that form `LargeFrOK` is l4v's `caps_no_overlap`
for the large frame, which the joint invariant already carries: FL4's
`NoOverlap` (MdbStep, kept by every `MdbStep`), inside `MdbOKV` of
`RelTopB` (`JAtZ.xtop.rel`); `NoOverlap.hno` (MdbStepInv) is the instance.
So `LargeFrOK` is a theorem of every `JAtZ` (`JAtZ.largeFrOK`), and the
clause's `JAtZ` gives it.
-/
import Fl4Proofs.P3.XTopJointKEntryU2F
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- **`LargeFrOK` from `NoOverlap`** (any MDB satisfying FL4's `caps_no_overlap`). -/
theorem LargeFrOK.of_noOverlap {G : MdbGhost} {m : U64 → U64} (hN : NoOverlap m G) : LargeFrOK G m := by
  intro y hy p rt mp asid va hc x hx hp
  have h := NoOverlap.hno hN hy (by rw [hc]; rfl) x hx hp
  rw [hc] at h
  exact h

/-- **`LargeFrOK` at every `JAtZ`** (`NoOverlap` of `JAtZ.xtop.rel`'s `MdbOKV`). -/
theorem JAtZ.largeFrOK {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) : LargeFrOK Z.G (L.mem s) :=
  LargeFrOK.of_noOverlap J.xtop.rel.2.2.2.2.1.1.2.2

end

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

end

end Fl4Proofs.P3.SInvR.G5
