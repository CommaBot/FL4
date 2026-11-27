/-
# P2 (integration int20): the unified family with the PageMap slot — `serializable_fl4_localU1P`

`serializable_fl4_localU1` (P2/E2EPU2.lean) is `serializable_fl4_localU1G` at
`LQ := (delPteSlot ⊕ invSlotU) ⊕ cmSlotU`. Line pte's PageMap slot (`pmPathsK`, P2/InvPmRoE.lean, the slot of
`serializable_fl4_localW11PRIPm3`) is a `PathsP (I64 × localinv.Plan)` family of `ownP` paths, and its start fact
`StartPmK` comes with `pm_hSFQK`, whose shape is exactly `serializable_fl4_localU1G`'s `hSFQ` (chain + `ptesR` epoch
data ⇒ `StartAt`, at `m := s.mem`). So no re-indexing is needed: the PageMap slot is one more `⊕` summand.

* **`StartInvU1P`**: U1's start facts (`StartInvU2`) on the left, `StartPmK` on the right;
* **`serializable_fl4_localU1P`**: `serializable_fl4_localU1G` at
  `LQ := ((delPteSlot ⊕ invSlotU) ⊕ cmSlotU) ⊕ pmPathsK B` — the eight W11 slots (PJ12 with `yb`), the mapped-frame
  Delete slot, the CNodeDelete slot, the Copy / Mint slot and the PageMap slot.

Premises: exactly `serializable_fl4_localU1`'s, plus the PageMap slot's `B : PmObl7` = [P] `cs` (the core set is
below 64) and [P] `lk` (the locks survive a user write), and its start fact `StartPmK` inside `ExecWPR`'s start
facts (as in `serializable_fl4_localW11PRIPm3`). **No [W]**; the only [J] is still iolay's `yb` (from U1D).

No new named premise. New module; no existing statement changes.
-/
import Fl4Proofs.P2.E2EPU2
import Fl4Proofs.P2.InvPmRoE
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld)
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg)

noncomputable section
open Classical

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **The four invocation summands' start facts** (`((delPte ⊕ CNodeDelete) ⊕ Copy/Mint) ⊕ PageMap`). -/
def StartInvU1P {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl7 st Cs Ω Sg Ac Locks)
    (Ch : S → Prop) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (q : SP) : ((InvArg S ⊕ InvArg S) ⊕ InvArg S) ⊕ (I64 × localinv.Plan) → Prop
  | .inl j => StartInvU2 st ar hA hm Ch K m hK hU c hs q j
  | .inr j => StartPmK hA hm B Ch K m hK hU c hs q j

end top

end
end Fl4Proofs.P2.E2EP
