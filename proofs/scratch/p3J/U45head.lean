/-
P3 (line p3J, gen 13): **`kernel_entry_reachU45`** = `kernel_entry_reachU44` with the per-entry decode premise
`JDecMRLK … VtxK …` (D1 + D2) narrowed to `JDecMRLK … VtxU …` (D2 only).

* D1 (a Thread cap invoked at `TCBSetEPTRoot`, label 88) is a theorem (module P3JVtxMR,
  `jDecMRLK_ofVtxU`): the ported spec has no decode outcome there (`specDec_ept_noOk`), so `JPathM`'s
  `JVtxScope` leaf leaves only `XCapP`'s error branches (`XCapP.mrN`), and FL4's decode at label 88 ends in
  `Ok ()`, `Err Preempted` or with `MR` kept (`MKE.decode_thread_ept`: `remote_tcb_stall` is an `MRKeepD`
  field; the exposed `cdt.delete` ends only in `Ok ()` / `Err Preempted`, `MKE.cdt_delete_exp`). Uses only
  U44's global `hA : P0.ArchTotal` and `hKD : MRKeepD`.
* **`VtxU`** [scope]: an Untyped cap retyping a VT-x object type (14..18). D2 is unchanged: the VT-x
  retype's `MR` at the outcome (its reset path runs `preemption_point`s, which read the clock, on both
  sides; the native types' counterpart is `JUtResetHyp` / `JUtResetMR` [W]).

**Premise diff U44 → U45** (diffed, `scratch/p3J/U44stmt.txt` vs `U45stmt.txt`): the syscall clause's
`JDecMRLK (L := L) arI VtxK …` ↦ `JDecMRLK (L := L) arI VtxU …` (`VtxU ⊆ VtxK`, `vtxU_vtxK`: weaker).
Everything else, and the conclusion, verbatim. New premises: none. [W] 0.
**`kernel_entry_reachU44_of45`**: U44's statement verbatim (`JDecMRLK.mono vtxU_vtxK`).

Named premises: U44's (XTopJointKEntryU44), with the per-entry `JDecMRLK` [J] narrowed to `VtxU` (D2 [J]).
No sorry.
-/
import Fl4Proofs.P3.XTopJointKEntryU44
import Fl4Proofs.P3.P3JVtxMR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

