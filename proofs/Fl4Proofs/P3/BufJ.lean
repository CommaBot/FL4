/-
P3 (DESIGN.md §9), IPC: **the IPC-buffer facts at a `JAtZ` state**
(handoff/glob.md gl15): `IpcBufCapOK` (`JAtZ.bok`), `BufCover` (from `bok`
and `JAtZ.fcov`, `bufCover_of_frameCover`) and `BufPlaced`
(`JAtZ.bufPlacedJ`), the three facts JEntryGlob's ∀-state premises
`ipcBufOK` / `bufCover` / `bufPlaced` gave (XTopJointFault's `XferHZ`):
`JAtZ.xferH`.
-/
import Fl4Proofs.P3.BufInv
import Fl4Proofs.P3.XTopJointData
import Fl4Proofs.P3.BufAtJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section Cover
open Fl4Spec

end Cover

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **The IPC-buffer facts at a `JAtZ` state** (module docstring). -/
theorem JAtZ.xferH (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    Endp.IpcBufCapOK σ ∧ Endp.BufCover Z.T Z.B σ ∧ Vs.BufPlaced (L := L) Z.N Z.C Z.B Z.c s σ :=
  ⟨J.bok, bufCover_of_frameCover J.bok J.fcov, J.bufPlacedJ⟩

end

end

end Fl4Proofs.P3
