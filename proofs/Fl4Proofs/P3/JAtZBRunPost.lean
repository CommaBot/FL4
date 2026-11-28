/-
P3 (line mmuAD, gen 28): **`set_thread_state Running` then `postpone` over `JAtZB`** (gen 27's "Next" item 2).

* **`JAtZB.runPostJ`**: P3/XTopJointRunPost's `JAtZ.runPostJ` copied over `JAtZB` (generator
  `scratch/mmu24_jatzb_gen.py runPostJ`; its 24 dependencies are already in P3/JAtZBWr / P3/JAtZBSched, so only
  the last decl is new). The proof reads `J.ext` nowhere (its one `ext` reader, `sc_frame`, is the gen-27 copy). The
  post is `JAtZB` (the generator renames only the binder; the conclusion was edited by hand).
  Proof verbatim.

What is **not** proved: the lift to `JAtZV` / `JAtZV2` (P3/JAtZBSched2's `JAtZV.ofBS` needs the spec step's
VCPU objects kept, sizes kept, no new `runningVM`: true for `stsAct (updK σ t (tcb {x with running}))` then
`postpone`, but the post only names σ7 through `Fl4Spec.postpone … = {((), σ7)}`; the kheap facts of `postpone`
are not stated anywhere yet), nor the footprint (`set_thread_state` + `postpone` words ⊆ `OObj`, VCPU words kept).

No named premise. No existing statement changed.

(mmuAD gen 42b18) Removed (the originals are stated over `JAtZB` in place, the `JAtZ` names their corollaries with
`ext` rebuilt): P3/XTopJointRunPost `runPostJ`.
-/
import Fl4Proofs.P3.JAtZBSched2
import Fl4Proofs.P3.XTopJointRunPost
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

end

end

end Fl4Proofs.P3
