/-
# P2 (line mmuAD, gen 10): **PageMap's read set is off the walker's words** (step 2 of the gen 9 plan)

PageMap's entry facts are stated at the layout `K.ptU` (`InvPmDec`: `K.toKLayout` with the PTE words added to the
user set; `region` and the kernel-state block do not depend on the user set). gen 7's declined-run device reads on
`IoRSR` (region-tagged words and the kernel-state block). **`ioRSR_ptU_notPWE`**: no `IoRSR (K.ptU)` word is a paging
word of the epoch — the leaves are user words of `K.ptU`, and every `PWE` word has region `.none` (`pwe_region`) and
lies outside the kernel-state block (`KsNoE` for the leaves, `PWE`'s own filter for the upper entries). So the
check of the gen 9 plan holds: no overlapping word.

No premise. New module; no existing statement changed.
-/
import Fl4Proofs.P2.E2EPU3e
import Fl4Proofs.P2.InvPmDec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV

noncomputable section

section io
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {K : KLayoutP} {E : U64 → U64}
  {Locks : S → U64 → Prop} {s : S}

/-- **No region-tagged read-set word of the PageMap layout is a paging word of the epoch** (module docstring). -/
theorem ioRSR_ptU_notPWE (hK : RegionOKP K) (hks : KsNoE (· ∈ K.ptes) K.toKLayoutV) {x : U64}
    (h : IoRSR st K.ptU Locks s x) : ¬ PWE K E x := by
  intro hp
  rcases h.2 with hr | ⟨o, ho, rfl⟩
  · exact hr (pwe_region hK hp)
  · rcases hp with hp | hp
    · exact hks o ho hp
    · exact hp.2.2.2.2 o ho rfl

end io

end
end Fl4Proofs.P2.E2EP
