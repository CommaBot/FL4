/-
P3 (line mmuAD, gen 35): **the badge-only notification write over `JAtZB`** — ScSignalJ's `JAtZ.signal_badge_post`
with `JAtZ` → `JAtZB` (the joint invariant without `JExt`), produced by `scratch/mmu32_jatzb_gen.py
signal_badge_post` and filtered to the declarations not yet stated over `JAtZB`: `JAtZB.deadP_nfr` (XTopJointFin),
`JAtZB.nwrite_notDbg` (LiveFrame), **`JAtZB.signal_badge_post`**. Edits: the post `JAtZ (Z.mv Z.G V')` → `JAtZB Z` (the original's witness is `Z.vs`, and `Z.mv Z.G Z.vs` is `Z` by structure eta, as gen 31's `reg_frameFZ`); the proofs are
the originals' (`JAtZB.cs_frameI` of P3/JAtZV3Sched takes the same arguments as `JAtZ.cs_frameI` here).

It is the common step of the notification writes the VM epoch needs: `send_signal`'s badge-only branches (incl.
the `RunningVM` thread whose VMEnter the signal does not complete, P3/JAtZV3SigVm) and `vcpu::check`'s bound
notification made idle (P3/JAtZV3Check). No premise; no existing statement changed.

(mmuAD gen 42b17) Copies removed (the originals are now stated over `JAtZB` in place): P3/LiveFrame `nwrite_notDbg`;
P3/XTopJointFin `deadP_nfr`.

(mmuAD gen 42b18) Removed (the originals are stated over `JAtZB` in place, the `JAtZ` names their corollaries with
`ext` rebuilt): P3/ScSignalJ `signal_badge_post`.
-/
import Fl4Proofs.P3.JAtZBFire
import Fl4Proofs.P3.ScSignalJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

end Fl4Proofs.P3
