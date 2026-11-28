/-
# P2 (line p3mc, gen 46): the re-base's interface — **`LocPlatC`**, the one thing the V15 trunk reads off the
platform, with an instance on the fixed platform (`MachPlatF` + `IpiF` + `IrqPlatK`) and no `irqOracle` fact

Handoff §51b (the collapse follow-up, first step). Every P2 top takes `P : LocPlat st arI AR MR` (P2/E2EVFl4W3:
`MachPlat` and `IrqPlatA` among its 15 fields), and `LocPlat` cannot hold at any `MR` that keeps the IPI vectors
126 / 127 masked unless the opaque `irqOracle` avoids them (P3/JBootIpi `ipi_forces_oracle`; `OpaqueH.ipi`,
P2/LocPlatModel). Inside the trunk, `P` is read **only** through `PathObl.chainOf_exists P` (P2/E2EVFl4W3:142: the
`loc_chain_all` call; every other field occurrence `P.ari … P.dr` of P2 is in that call or its three W9 / W13 /
U12a variants), i.e. through the proposition "every `JReachU17` exit has a P3 chain". `SerExitW P` uses it only
inside `Classical.choose`, whose proof argument is irrelevant. So:

* **`LocPlatC st arI AR MR`** (Prop): `nd : numDomains = 1` and `chain`: every `JReachU17` exit has a `ChainOf`
  (P2/E2EVFl4W3, base, platform-free).
* **`LocPlat.toC`** (the base platform gives it: `chainOf_exists`), **`LocPlatC.ofQ`** (the fixed platform
  `Fl4ProofsQ.P2.PathObl.LocPlat` — `LocPlat` with `mach : MachPlatT` = `MachPlatF ∧ IpiF` and `ia : IrqPlatK`,
  jboot gen 5's kernel-checked copy P2/WitU34Gen, an **existing** constant: no new transport — gives it by that
  copy's `chainOf_exists`).
* `chainCC`, **`SerExitC`**, `SerExitC.chainOf`; **`serExitW_iff_C`**: `SerExitW P K Ch ↔ SerExitC P.toC K Ch`
  (`Iff.rfl`: the two `Classical.choose` are over the same proposition), **`serExitQ_iff_C`**: the fixed platform's
  `Fl4ProofsQ.P2.E2EV.SerExitW P K Ch ↔ SerExitC (LocPlatC.ofQ P) K Ch` (`Iff.rfl`). So a trunk restated over
  `SerExitC` covers both platforms' serial exits with the same statements.
* **`locPlatC_wit`**: `LocPlatC wst warI wAR ipiMR` from `OpaqueWK` [P] only (jboot's witness platform,
  P2/WitU34 `wit_locPlatK`): **no `irqOracle` assumption** (`OpaqueWK` = `OpaqueH` without `ipi`; `MR = ipiMR`
  keeps 126 / 127 masked). `ipiMR` is not `LocPlat`-admissible without the oracle fact, so this instance is out of
  reach of every existing top; it is what the re-based V15 tops will take.
* `jReachU17_of_U40`: a U46-line exit (`JReachU40 = (JReachU17 ∧ IrqCarry) ∧ IoaRel`, P3/XTopJointKEntryU40) is a
  `JReachU17` exit, so `SerExitC`'s exits include every U46 exit (U46's `IrqCarry` / `IoaRel` are extra facts at
  the exit, not obligations on the chain).

What remains for the re-base (handoff §51b): restate the V15 trunk's `P : LocPlat` parameter as `P : LocPlatC`
(in place, the old statements one-line corollaries through `LocPlat.toC` and `serExitW_iff_C`); its bottom
(P2/E2EVFl4W3 `SerExitW`, P2/E2EPU6 / E2EPU7, the W4–W16 and U1–U5 files) is touched by the collapse PR, so that
step waits for it.

No named premise beyond `OpaqueWK` [P] (in `locPlatC_wit`); no existing statement changed (new module).

**Gen 54:** `LocPlatC`, `LocPlat.toC`, `chainCC`, `chainCC_spec`, `SerExitC`, `SerExitC.chainOf` and
`serExitW_iff_C` moved, unchanged, to P2/E2EVFl4W3 (the bottom of the V15 trunk, which is re-based onto them in
place); `LocPlatC.ofQ`, `jReachU17_of_U40`, `serExitQ_iff_C` and `locPlatC_wit` stay here. The slot obligations also
read two P3 facts at chain states (`ChainRun`, `ChainAct0`): the trunk's platform is `LocPlatCR` (P2/E2EPU12a), its
witness instance `locPlatCR_wit` (P2/V15PlatW).
-/
import Fl4Proofs.P2.WitU34
import Fl4Proofs.P2.E2EPV15AD
import Fl4Proofs.P3.XTopJointKEntryU40
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout)

noncomputable section
open Classical

section
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]
variable {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop) (MR : A3 → Fl4Spec.MachineState → Prop)

variable {st arI AR MR}

/-- **The fixed platform (`MachPlatT`, `IrqPlatK`) gives `LocPlatC`** (module docstring: jboot gen 5's existing
kernel-checked copy of `chainOf_exists`). -/
theorem LocPlatC.ofQ [Fl4Proofs.P1.PlainStore st] (P : Fl4ProofsQ.P2.PathObl.LocPlat st arI AR MR) :
    LocPlatC st arI AR MR :=
  ⟨P.nd, fun h => Fl4ProofsQ.P2.PathObl.chainOf_exists P h⟩

/-- **A U46-line exit is a `JReachU17` exit** (module docstring). -/
theorem jReachU17_of_U40 {σe : S} {a3 : A3} {τ : Fl4Spec.State Unit}
    (h : Fl4Proofs.P3.SInvR.G5.JReachU40 (L := L) arI AR MR σe a3 τ) :
    Fl4Proofs.P3.SInvR.G5.JReachU17 (L := L) arI AR MR σe a3 τ :=
  h.1.1

end

end
end Fl4Proofs.P2.PathObl

namespace Fl4Proofs.P2.E2EV
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV

noncomputable section
open Classical

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **The fixed platform's serial exits are `SerExitC`'s** (definitionally). -/
theorem serExitQ_iff_C (P : Fl4ProofsQ.P2.PathObl.LocPlat st arI AR MR) {K : KLayoutV} {Ch : S → Prop} :
    Fl4ProofsQ.P2.E2EV.SerExitW P K Ch ↔ SerExitC (LocPlatC.ofQ P) K Ch :=
  Iff.rfl

end

end
end Fl4Proofs.P2.E2EV

namespace Fl4Proofs.P2.Wit
open Fl4Proofs.P2.PathObl Fl4Proofs.P3 Fl4Proofs.P3.JBoot

/-- **`LocPlatC` on jboot's witness platform at `ipiMR`, from `OpaqueWK` [P] only — no `irqOracle` fact**
(module docstring). -/
theorem locPlatC_wit (O : OpaqueWK) : LocPlatC wst warI wAR ipiMR :=
  LocPlatC.ofQ (wit_locPlatK O)

end Fl4Proofs.P2.Wit
