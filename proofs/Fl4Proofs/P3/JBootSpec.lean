/-
P3 (line jboot, gen 1): **the spec-only start facts of `JReachU17` at `initASt`**.

`JReachU3.start` asks `SInvX σ`, `SInvIP σ`, `SInvUZ.UtPgR σ` of its spec state and `JReachU17` adds `GpmOutV`,
`IdleVtS` and `DevRangeS`. Boot lemmas existed for `SInvX` (`boot_sinvX`), `GpmOutV` (`boot_gpmOut`) and `IdleVtS`
(`boot_idleVtS`); this module adds the other three, all vacuous at `initASt` (it holds only null caps,
`SInvU.init_capAt`): **`boot_sinvIP`**, **`boot_utPgR`**, **`boot_devRangeS`**, and their conjunction with the
existing ones, **`boot_jReachSpec`**.

So the spec side of `JReachU17`'s start is jointly satisfiable. It does not give a `JReachU17` state:
`initASt` is not a `JAtZ` state (JBootInitA's `initASt_not_jAtZ`), so a P3 start state needs another spec boot
state, laid out as FL4's kernel-state block, for which these six facts are to be re-proved (handoff jboot.md).

No sorry; no premises. New module; no existing statement changed.
-/
import Fl4Proofs.P3.XTopJointKEntryU17
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.JBoot
open Fl4Spec Fl4Proofs.P3

noncomputable section

/-- A cap of `initASt` read through `capOpt` is null. -/
theorem init_capOpt {p : ObjRef} {cref : CnodeIndex} {c : Cap}
    (h : capOpt ((initASt (Z := Unit)).kheap p) cref = some c) : c = .nullCap :=
  SInvU.init_capAt ((SInvUZ.capAt_capOpt (initASt (Z := Unit)) (p, cref)).trans h)

/-- **`SInvIP` at boot** (no IO-port or untyped cap). -/
theorem boot_sinvIP : SInvR.G5.SInvIP (initASt (Z := Unit)) where
  ioP := fun _ _ _ hc => by cases SInvU.init_capAt hc
  ioN := fun _ _ _ _ _ _ hc _ _ => by cases SInvU.init_capAt hc
  utZ := fun _ _ _ _ hc => by cases SInvU.init_capAt hc

/-- **`UtPgR` at boot** (no untyped cap). -/
theorem boot_utPgR : SInvUZ.UtPgR (initASt (Z := Unit)) :=
  fun _ _ _ _ _ hc => by cases init_capOpt hc

/-- **`DevRangeS` at boot** (no untyped cap). -/
theorem boot_devRangeS : SInvDV.DevRangeS (initASt (Z := Unit)) :=
  fun _ _ _ _ _ hc => by cases init_capOpt hc

/-- **The spec part of `JReachU17`'s start, jointly, at `initASt`.** -/
theorem boot_jReachSpec :
    SInvR.G4.SInvX (initASt (Z := Unit)) ∧ SInvR.G5.SInvIP (initASt (Z := Unit)) ∧
      SInvUZ.UtPgR (initASt (Z := Unit)) ∧ SInvGp.GpmOutV (initASt (Z := Unit)) ∧
      SInvIV.IdleVtS (initASt (Z := Unit)) ∧ SInvDV.DevRangeS (initASt (Z := Unit)) :=
  ⟨SInvR.G4.boot_sinvX, boot_sinvIP, boot_utPgR, SInvGp.boot_gpmOut, SInvIV.boot_idleVtS, boot_devRangeS⟩

end

end Fl4Proofs.P3.JBoot
