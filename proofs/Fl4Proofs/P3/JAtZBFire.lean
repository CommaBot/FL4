/-
P3 (line mmuAD, gen 32): **FL4's TCB timers (`timer.fire`) over `JAtZB`** — ScFireJ's chain with `JAtZ` → `JAtZB`
(the joint invariant without `JExt`, the VM-epoch base of `JAtZV`/`JAtZV3`), produced by `scratch/mmu32_jatzb_gen.py`
(gen 24's generator with the gen 31 signature bug fixed: the signature now ends at the first `:=` outside brackets,
so `JAtZ.fireJ (hSig : SignalJHyp (L := L) …) … (J : JAtZ …)` is found) and the decls missing over `JAtZB` kept:
`JAtZB.otherTmOK`, `tw_word`, `tmw_word`, `tmw_obj`, `tmw_ne_tcb`, `tmw_ne_obj`, `tmw_ne_node`, `tmw_slots`,
`deadP_hstep`, `notDbg_tw`, `jcov_keepX`, `tmw_utc`, `tmw_step`, `reprogramJ`; by hand (same text, `JAtZ` → `JAtZB`):
**`SignalJHypB`**, **`FireInvB`**, **`fire_loopJB`**, then **`JAtZB.fireJ`**. Every post `JAtZ` → `JAtZB`.
Other edit: `JAtZB.tmw_step` calls `JAtZB.cs_frameK`, which has no `tVcpuA` (JExt) argument, so the original's
TCB-VCPU-word frame argument is dropped.

Named premise: **`SignalJHypB` [J]** — ScFireJ's `SignalJHyp` [J] with `JAtZ` → `JAtZB` (`send_signal` from a
`JAtZB` state at a notification of `N` against the spec's `sendSignal`, deterministic, `JAtZB` after at fresh VSpace
sets, domain time kept). Why it stays [J] (exactly): over `JAtZ`, ScSignalJ's `signalJHyp_of` reduces `SignalJHyp`
to `SignalRestJHyp` [J], the case of an idle notification whose bound thread is `RunningVM` — FL4's
`send_signal` then `remote_tcb_stall`s the thread (the VM exits on another core) while the spec's `sendSignal` only
sets the badge: the spec has no VM-exit-on-signal (Ext/VirtEntry: FL4 #80/#81/#85 and the signal exit are not yet
modelled, owned by the virt line), so no refinement is possible; the waking cases are proved over `JAtZ` only
(`signal_badge_post`, `signal_waitDJ`, `signal_boundDJ`, ScSignalDonJ), and their `JAtZB` copies (the same
generator method) are the next step, after which `SignalJHypB` reduces to `SignalRestJHypB` exactly as over `JAtZ`.
Not false on reachable states: it is the JAtZB-level statement of `SignalJHyp`, whose non-runningVM cases are
theorems over `JAtZ`. No existing statement changed.

(mmuAD gen 42b17) Copies removed (the originals are now stated over `JAtZB` in place): P3/DeadKeep `deadP_hstep`;
P3/LiveFrame `notDbg_tw`; P3/ScFireJ `jcov_keepX`, `tmw_ne_node`, `tmw_ne_obj`, `tmw_ne_tcb`, `tmw_obj`, `tmw_slots`,
`tmw_utc`, `tmw_word`, `tw_word`.

(mmuAD gen 42b18) Removed (the originals are stated over `JAtZB` in place, the `JAtZ` names their corollaries with
`ext` rebuilt): P3/XTopJoint `otherTmOK`; P3/ScFireJ `tmw_step`, `reprogramJ`. Moved to P3/ScFireJ (statements
unchanged): `SignalJHypB` [J], `FireInvB`, `fire_loopJB` (now `fire_loopE`'s instance at `E := True`), `JAtZB.fireJ`.
-/
import Fl4Proofs.P3.JAtZV3Sched
import Fl4Proofs.P3.ScFireJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

end Fl4Proofs.P3
