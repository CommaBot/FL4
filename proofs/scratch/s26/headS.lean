/-
P3 (issue #16, s26): **the performs of `ZD` (l4v `valid_untyped` for device
untyped caps) that the generated families leave out, but the untyped
perform** (spec side only; outside the `JAtZ` cone; SpecInvUtZS with the
device flag and the object half).

* ReadFPU (`invokeFl4Tcb`): the frame write is a machine operation, so
  both halves are plain frames (`zd_invokeFl4Tcb`, no decode fact).
* The arch performs but MakePool: the cap half as SpecInvUtZS (page / table
  maps write arch caps only), the object half by `ob_auto`
  (`ob_fl4ArchPerform_nc`).
* MakePool (`perform_asid_control_invocation`, `zd_makePool`): it detypes the
  parent untyped's 4K region, writes the parent back full and retypes one
  ASID pool at `frame`. With the decode's `MpOK` (the parent holds an
  untyped cap of exactly that region and has no CDT child) and SpecInvUtMp's
  `detype_PR` (the region misses every other untyped's free part, and a
  device cap whose region meets it is an ancestor whose region contains it:
  l4v `untyped_inc`), the pool lies in the used part of every device cap
  whose region it meets (`zd_fl4Arch`).
-/
import Fl4Proofs.P3.SpecInvDvX
import Fl4Proofs.P3.SpecInvUtP6
open Classical

namespace Fl4Proofs.P3.SInvDV
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvV Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 1000000

theorem dv_capAt_capOpt (σ : State Unit) (sl : CslotPtr) : SInvU.capAt σ sl = capOpt (σ.kheap sl.1) sl.2 := by
  unfold SInvU.capAt
  cases σ.kheap sl.1 with
  | none => rfl
  | some o => cases o <;> first | rfl | (simp only [SInvU.capView, capOpt]; split <;> rfl)

/-! ## The cap half of the arch performs (SpecInvUtZS) -/

