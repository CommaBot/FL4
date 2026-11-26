/-
P3 (line p3J, gen 14): **`kernel_entry_reachU46`** = `kernel_entry_reachU45` with the per-entry decode premise
`JDecMRLK … VtxU …` (D2) narrowed to `JDecMRLK … VtxR …`, and **`kernel_entry_reachU45nv`** = U45 without any
`JDecMRLK` premise on a platform reporting no virtualization (`NoVirt` [P]).

* (module P3JVtxR) FL4's decode of an Untyped cap whose first argument is a VT-x object type (14..18) is a
  non-preempted error with the arch state unchanged at every label but `UntypedRetype` (`illegal`, or, at
  `UntypedRetypeShared` with sharing on, `retype_shared`'s `shared_frame_spec` refusing sizes other than
  12 / 21), and at `UntypedRetype` too when `virtualization()` answers 0 (`InvalidArgument 0`,
  untyped.rs:43): `MKE.decode_untyped_vtx_err`. Then `XCapP.mrE` adds `MR` to `JPathM`'s `vtx` leaf.
  Uses only U45's global `hA : P0.ArchTotal` and the store's totality.
* **`VtxR`** [scope]: an Untyped cap at `UntypedRetype` with first argument in 14..18 (D2 proper: the VT-x
  retype with virtualization present). `jDecMRLK_ofVtxR : JDecMRLK VtxR → JDecMRLK VtxU`.
* **`NoVirt arI`** [P] (`∀ a, arI.virtualization a = ok 0#u64`, the existing `Arch` field; not implied by U45's
  premises: `P0.ArchTotal` gives only `ok _`). `jDecMRLK_vtxU_nv`. The jboot witness arch satisfies it
  (`noVirt_warI1`).

**Premise diff U45 → U46** (diffed, `scratch/p3J/U45stmt.txt` vs `U46stmt.txt`): the syscall clause's
`JDecMRLK (L := L) arI VtxU …` ↦ `JDecMRLK (L := L) arI VtxR …` (`VtxR ⊆ VtxU`, `vtxR_vtxU`: weaker). Everything
else verbatim. New premises: none. [W] 0. **`kernel_entry_reachU45_of46`**: U45's statement verbatim.

**Premise diff U45 → U45nv** (`U45nvstmt.txt`): + `(hNV : NoVirt arI)` [P] after `hCfg`; the syscall clause's
`JDecMRLK` antecedent removed entirely. Everything else verbatim.

Named premises: U45's (XTopJointKEntryU45), with the per-entry `JDecMRLK` [J] narrowed to `VtxR` (U46) or
removed under `NoVirt` [P] (U45nv). No sorry.
-/
import Fl4Proofs.P3.XTopJointKEntryU45
import Fl4Proofs.P3.P3JVtxR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

