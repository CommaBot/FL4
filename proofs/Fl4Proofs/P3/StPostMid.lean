/-
P3 (line stpost, generation 3; trimmed in generation 5): **`JStabR`**, the stable-ghost post at
`JAtZR` (the receive's exit form, as `DispPostRM`'s `JAtZR`): `JStab` with `JAtZR`.

Generation 3 also stated here the ReplyRecv dispatch at stable ghosts under a [W] receive premise
(`JMidRecvHypSt`, `mid_invRecvReplyJSt`, `dispatch_replyRecvJSt`). Generation 4 discharged that
premise (StPostRecv's `mid_invRecvReplyJStF` / `dispatch_replyRecvJStF`, with `RRMidSt` FL4 facts
instead of the [W] premise); the superseded lemmas were removed in generation 5. No named premise.
-/
import Fl4Proofs.P3.StPostInv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section StMidA
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

/-- (stpost) **`JStab` at `JAtZR`** (module docstring). -/
def JStabR (arI : machine.Arch A) (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  ∃ (G : MdbGhost) (V : XVs) (Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    JAtZR (L := L) arI AR (Z.mv G V) H Cs Ac Lst D s a σ

end StMidA


end

end Fl4Proofs.P3
