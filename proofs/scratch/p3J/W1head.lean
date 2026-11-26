/-
P3 (line p3J, gen 5): **the jboot witness with one IOAPIC** — `kernel_entry_reachU38` / `U39` apply to the
witness platform with their start condition `IoaRel` met.

* **`warI1`**: jboot's witness arch `warI` (P2/WitPlat) with only `num_ioapics` / `ioapic_pins` changed: one
  IOAPIC (`num_ioapics = 1`) of 24 pins (`ioapic_pins i = 24` for `i < 1`, `0` otherwise, as FL4's
  `ioapic::pins`), i.e. FL4's x86_64 backend on a one-IOAPIC machine and the spec's `init_arch_state`
  (`x64_num_ioapics = 1`, `x64_ioapic_nirqs = ioapicIRQLines = 24`). `modelArch` / `warI` are not changed.
* **`jAtZ_w0I1`**, **`jReachU34_w0I1`**: jboot's start state at `warI1` (`ipiMR`). `JAtZ` names the arch only in
  `kern` (`JKern.tdx`, `TdxRel`: `tdx_active` / `dma_ram`, unchanged) and `utc` (`UtCapP3`, phantom); the other
  fields are jboot's, verbatim.
* **`u34_w0I1`**: every global premise of `kernel_entry_reachU34` at `wst` / `warI1` / `wAR` / `ipiMR` with
  `jReachU34_w0I1` (`u34_w0I`'s proof, renamed: no part of it reads the IOAPIC counts).
* **`warI1_ioaRel : IoaRel warI1 fInitASt`**; **`jReachU38_w0I1`**; **`u38_w0I1`**: every premise of
  `kernel_entry_reachU38` (= U34's global ones) with its start `jReachU38_w0I1`. Left: only the per-entry
  syscall / event [J]s in U38's conclusion antecedents (`KDispHypsKVU38`, `JDecMRLK`, `KFinAtR13`, `KFinEv13`).
* **`warI1_ioaMap : IoaMap warI1`** (U39's new global premise: `ioapic_map` / `ioapic_map_remapped` always answer
  `true`, as `modelArch`'s); **`u39_w0I1`**: every premise of `kernel_entry_reachU39` with its start.
* Contrast: **`warI_not_ioaRel : ¬ IoaRel warI fInitASt`** (`warI` answers 0 IOAPICs).

Named premises: **`OpaqueWK`** [P] (JBootU34: the opaque Fl4Spec constants) only. No [J], no [W].
Caveats (jboot's): idle-only boot, one core.
No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.JBootU34
import Fl4Proofs.P3.XTopJointKEntryU39
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.JBoot
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs

noncomputable section

/-- **The witness arch with one IOAPIC of 24 pins** (module docstring): `warI` with `num_ioapics` and
`ioapic_pins` set. -/
def warI1 : machine.Arch Fl4Spec.MachineState :=
  { warI with
    num_ioapics := fun _ => ok 1#u64
    ioapic_pins := fun _ i => ok (if i.val < 1 then 24#u64 else 0#u64) }

