/-
# P2 (line p3mc, gen 29): FL4 end to end without `VSafe9`

With U28 (P2/E2EPU28) every non-io start of the family is exempt: **`u28At_all`** — at every start index `i` with
`¬ IoIx i` and for every layout / core / locks / view / body, `U28At` holds (vmF, vmR, sl: their classes are all
starts; st: the target is homed (`StHAt`) or not (`StFhAt`); irq: `u24At_irq`; vx, vt: all; CNodeDelete, Copy /
Mint, PTE delete: all). So the exempt predicate is no premise at all, and the chain-level step need not mention
`VSafe9` [J]:

* `Fl4StepWPRV11` / `ExecWPRV11`: U10's step (`Fl4StepWPRV10`) whose `start` field's second arm is only "the armed
  program is the re-annotated body `annV k0`" — **no `VSafe9` [J]**, no exempt predicate;
* **`execWPRV10_of_11`**: an `ExecWPRV11` is an `ExecWPRV10` for any `FH` holding at every `NoV` start;
  **`execWPRV11_of_10`**: every `ExecWPRV10` is an `ExecWPRV11` (drop the `VSafe9` obligation);
* **`serializable_fl4_localV11`**: over U18's family with the invocation summands, `ExecWPRV11 … (¬ IoIx)
  StartV2C` ⇒ `RunAll` (through U28 at `FH := U28At` and `u28At_all`);
* **`serializable_fl4_localU28ofV11`**: U28's statement follows (so every earlier `serializable_fl4_localU*`
  statement over this family does too, through the `…of…` chain).

## Premises of `serializable_fl4_localV11` (exactly)
* the execution `h : ExecWPRV11 …`, whose steps carry: `arm` [P] (armed programs are pure glue); `start` [P] (the
  glue's start fact at `c`'s view, `StartV2C` [P] — the W11 slots' `StartU2C` records and the invocation slots'
  `StartInvU3` (`LkC`, `InvLkW →` `DelPteStart` / `InvStartU2` / `CMStartU2`, with their `DelPtePrem.lk` /
  `InvPremW.lk` [P]) — and, for a start whose armed program is the body itself, **`VSafe` [J] where `¬ IoIx`**);
  `serX` [P] / `serC` / `serG` [P] / `keep` (as U10);
* `P : LocPlat` [P], `hIoa : MRKeepIoapic` [P], `h0` (`Init`), `hA0` (`ArmInv`), `hB` (`SerExitW` [P] at the start),
  `hc0`, `hM0`, `hq` (`NoLoc`).
* **Removed vs `serializable_fl4_localU28`: `VSafe9` [J] (asked nowhere; the exempt predicate `U28At` is proved,
  `u28At_all`).** Nothing added.

No existing statement changed except the root import list.

Gen 56 (handoff p3mc §61) retired, with `ExecWPRV10–12` and the V15 stepping stones: `Fl4StepWPRV11`, `ExecWPRV11`,
`execWPRV10_of_11`, `serializable_fl4_localV11`.
-/
import Fl4Proofs.P2.E2EPU28
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY)
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath tr masksOf)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg NextH VEq Safe narrowSP)
open Fl4Proofs.P2.CoreView (view)

noncomputable section
open Classical

/-! ## The chain-level step without `VSafe9` -/

section exec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {ι : Type}

end exec

/-! ## Every non-io start is exempt -/

section all
variable {S : Type}

/-- **`U28At` holds at every non-io start** (module docstring). -/
theorem u28At_all (K : KLayoutP) (c : U64) (hs : U64 → Prop) (ρ : U64 → U64) (k0 : SP)
    (i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)) (hn : ¬ IoIx (S := S) i) :
    U28At (S := S) K c hs ρ k0 i := by
  have l24 : U24At (S := S) K c hs ρ k0 i → U28At (S := S) K c hs ρ k0 i :=
    fun h => Or.inl (Or.inl (Or.inl (Or.inl h)))
  have l16 : U16At (S := S) K c hs ρ k0 i → U24At (S := S) K c hs ρ k0 i :=
    fun h => Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h)))))))
  rcases i with ((j | j | j | j | j | j | (j | j)) | ((j | j) | j))
  · exact l24 (l16 (Or.inl (Or.inl trivial)))
  · exact l24 (l16 (Or.inl (Or.inr trivial)))
  · exact (hn trivial).elim
  · by_cases hT : ρ (fld j.target oAFFINITY) = c
    · exact l24 (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hT)))))))
    · exact l24 (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hT))))))))
  · exact l24 (u24At_irq K c hs ρ k0 j)
  · exact l24 (l16 (Or.inr trivial))
  · exact l24 (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr trivial))))))
  · exact l24 (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr trivial)))))
  · exact u28At_pte K c hs ρ k0 j
  · exact Or.inl (u27At_del K c hs ρ k0 j)
  · exact Or.inl (u27At_cm K c hs ρ k0 j)

end all

/-! ## The top without `VSafe9` -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

end top

end
end Fl4Proofs.P2.E2EP
