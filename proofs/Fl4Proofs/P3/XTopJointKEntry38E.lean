/-
P3 (DESIGN.md §9), invariant line g5d (KENTRY-PLAN g5d; g5c's handoff (1),
(3)): **`kernel_entryJ38E`** = `kernel_entryJ37E` without the entry premise
`FlagsRel`, and **`kernel_entry_reachIF`** = `kernel_entry_reachIP` without
its per-state `FlagsRel` premise.

`FlagsRel Z.T mem σ` (FL4's flags word `t+3456` gives the spec's
`tcb_flags`, l4v `tcb_relation`'s flags part) is now carried: g5d widened
`Sched.McpRel` (a field of `JAtZ`, `JRest`, `JAtZR`, `JAtZS`, kept by every
step) to relate the flags word with the MCP word (`flagsA`), its spec frame
`McpKeep` to keep `(tcb_mcpriority, tcb_flags)`, and every footprint lemma
that keeps the MCP word to keep the flags word too (`FinW` no longer admits
offset 3456; `KFoot.ne_flags`, `FinW.nf`, `JAtZ.cnW_nf`, the `*_keeps`
lemmas). The writers: SetFlags (`JAtZ.flagsWrJM`, `McpRel.setF`), SetMCP
(`McpRel.set`, flags word kept), the TCB retype (both words zero,
`McpRel.addT`, `w2f_zero`). So `FlagsRel` holds at every `JAtZ` state
(`FlagsRel.of_mcp`), across a syscall and across every event alike (every
`JAtZ` producer keeps `McpRel`).

`JReachIP`'s step never asked `FlagsRel`; with it a theorem of `JAtZ`,
`kernel_entry_reachIF` asks at a reachable state only `LargeFrOK` (and the
per-syscall `hflag`, `hK`, `hDM`, `hFin`, `hFast`) and its exits need
`SpecUtZ` to be reachable again (KENTRY-PLAN g5d for the two open carries).
-/
import Fl4Proofs.P3.XTopJointKEntry37E
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {MR : A → Fl4Spec.MachineState → Prop}

/-- **`FlagsRel` at every `JAtZ` state** (`McpRel`'s flags part). -/
theorem _root_.Fl4Proofs.P3.JAtZ.flagsRel {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) : FlagsRel Z.T (L.mem s) σ :=
  FlagsRel.of_mcp J.mcp

end

end

end Fl4Proofs.P3.SInvR.G5
