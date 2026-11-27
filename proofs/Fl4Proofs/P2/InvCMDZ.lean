/-
# P2 (line slhuf, gen 14): the Copy / Mint target's zero first word at the entry

`cmDestZ_of`: at an entry with the user-write-stable `Q` (`InvQCMW`, P2/InvCMQ.lean), the plan's own `plan_with`
(`InvExW`) on the Copy / Mint label (`InvCMArm`) gives `plan_with_cmFZ`'s target with first word `0`; the cap of the
invoked slot and the target lookup are functions of the state, so this is `CMDestZ` (P2/InvCMAccZ.lean). No premise.
-/
import Fl4Proofs.P2.InvCMQ
import Fl4Proofs.P2.InvCMAccZ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1

section dz
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : OwnMap.KLayout} {μ : U64 → U64}
  {s : S}

/-- (slhuf gen 14) **`CMDestZ` at an `InvQCMW` entry** (module docstring). -/
theorem cmDestZ_of (hq : InvQCMW st Cs Ω Sg Ac Locks p K μ s) : CMDestZ st p s := by
  obtain ⟨⟨-, -, harm, -⟩, -, ⟨info, ei, hpw, -⟩⟩ := hq
  have hl := harm _ _ (cur_thread_ok s) ei
  obtain ⟨cp, cr, cg, cgb, dest, -, -, -, -, -, -, -, -, -, -, -, hcap, -, -, hlt, -, -, -, -, -, hz, -⟩ :=
    plan_with_cmFZ hl hpw
  intro cp' cr' cg' cgb' dest' hcap' hlt'
  rw [hcap] at hcap'
  have e := ok_inj_ff hcap'
  cases e
  rw [hlt] at hlt'
  have e' := ok_inj_ff hlt'
  cases e'
  exact hz

end dz

end Fl4Proofs.P2.PathObl
