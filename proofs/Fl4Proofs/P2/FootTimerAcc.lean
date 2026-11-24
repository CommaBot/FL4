/-
# P2: what the local timer paths read (`PathObl.access` pieces)

The concurrency obligation (`P2/PathObl.lean`) bounds every access, reads included, by running the body on
the guarded store `guard st R W`. This module gives the pieces for the timer paths:

* accessor lemmas: an accessor on `guard st R W` is the accessor on `st` when its word is in `R`
  (`tdG`, `tlG`, `trG`, `nodeGetG`);
* `in_core_timer_tree` (proof in progress, `P2/FootTimerAccLoop.lean`, not imported): it reads only core `c`'s
  `TIMER_ROOT` and `TIMER_MIN` and the `TIMER_DEADLINE` / `TIMER_LEFT` / `TIMER_RIGHT` words of the keys of
  `c`'s tree (`TreeReads`; the null handle's words are in the set but never read: the stack holds keys
  only, `StackOK`). Never a word of `target` unless `target` is a key (DESIGN.md §7 "Timer ownership"):
  the search compares a popped node with `target` before reading it. Under P2/OwnMap's map (timer fields of
  an armed thread belong to the core of its tree, `TIMER_HEIGHT >> 8`) every one of these words is core
  `c`'s: the keys of `c`'s tree are armed with core bits `c` (`CoreTree.armed`, `CoreTree.core`), also those
  whose `AFFINITY` is another core.

## Reads of the timer paths against P2/OwnMap (analysis, module docstring of the report)

Recorded per read: core-owned / locked / gate-only. Those the proposed map would forbid:

1. `set_timer_target_ok` reads `target`'s `TIMER_DEADLINE` before it knows where `target` is armed. When
   `target` (affinity this core) is armed in another core `c'`'s tree the map gives that word to `c'`. No
   local path of `c'` writes it (they write deadlines only of threads with affinity `c'`: `fire`'s
   `plan_objects` and `TCB_SetTimer`'s `set_timer_target_ok` both check it), so it is benign; a map that
   gives `TIMER_DEADLINE` / `TIMER_BADGE` of a thread armed in `c'`'s tree to `c'` only when its affinity is
   `c'` (else to the gate) admits it and every write of the timer paths.
2. `may_run_here` / `current_ok` read the `CORE` word of a thread's SC before knowing it is this core's:
   the map gives SC words to the core in `SC.CORE`. `CORE` is written only under the gate
   (`SchedControl_Configure`, boot): the map should make it gate-only.
3. The timer interrupt reads the due thread's `STATE` (`plan_objects` re-run in the body, `fire_ok`,
   `send_signal`) also when that thread is blocked on an object it has not locked (`BlockedOnSend` on any
   endpoint, `BlockedOnNtfn` on another notification): the map gives `STATE` of a blocked thread to
   `lock<BLOCK_OBJ>`, and a local path holding that lock may dequeue and wake it concurrently. Benign in
   value (the paths only distinguish `BlockedOnRecv` / `RunningVM` / other, and the thread cannot become
   either beside the gate while it is not running here), but an unlocked read of a lock-owned word.
4. `release_due` / `awaken` / `set_next_interrupt` read the refill words of the SC of this core's
   release-queue head: core-owned only if that SC's `CORE` is this core. FL4 keeps a thread's affinity
   equal to its SC's core (`donate`, `SchedControl_Configure` migrate), but no P1 invariant states it: it
   belongs in `Pre`.
5. TCB cap slots read without a lock: the CTable root in `lookup_slot_locked` (glue), the VTable slot in
   `set_vm_root` (a switch after a wake), the timeout-handler slot in `end_timeslice`. The map gives cap
   slots to `lock<slot>`; a TCB's own slots are written only under the gate (no CSpace path reaches them),
   so they should be gate-only.
6. `plan_timer_irq` (glue, before the locks) reads the notification's `STATE` / `BOUND_TCB` and the
   thread's `STATE` / `BLOCK_OBJ` / `REPLY` unlocked; the body re-reads all of them under the locks
   (`plan_objects`, `same_plan`). `cspace_step` makes no store access; the lock calls are fl4-sync's
   (`lookup_slot_locked`), each slot locked before its cap is read.

No named premises.
-/
import Fl4Proofs.P2.FootTimerTree
import Fl4Proofs.P2.PathObl
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (guard guard_read)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R Wr : U64 → Prop}

/-! ## Accessors on the guarded store -/

theorem tdG {s : S} {y : U64} (h : R (tdA y)) :
    obj.Tcb.timer_deadline (guard st R Wr) y s = obj.Tcb.timer_deadline st y s := by
  unfold obj.Tcb.timer_deadline
  rw [eq_of_spec_fd layout.tcb.TIMER_DEADLINE.spec]
  simp only [bind_ok, lift]
  exact guard_read h

theorem tlG {s : S} {y : U64} (h : R (tlA y)) :
    obj.Tcb.timer_left (guard st R Wr) y s = obj.Tcb.timer_left st y s := by
  unfold obj.Tcb.timer_left
  rw [eq_of_spec_fd layout.tcb.TIMER_LEFT.spec]
  simp only [bind_ok, lift]
  exact guard_read h

theorem trG {s : S} {y : U64} (h : R (trA y)) :
    obj.Tcb.timer_right (guard st R Wr) y s = obj.Tcb.timer_right st y s := by
  unfold obj.Tcb.timer_right
  rw [eq_of_spec_fd layout.tcb.TIMER_RIGHT.spec]
  simp only [bind_ok, lift]
  exact guard_read h

theorem nodeGetG {s : S} {c o : U64} (h : R (L.nodeAt s c o)) :
    obj.node_get (guard st R Wr) s c o = obj.node_get st s c o := by
  unfold obj.node_get obj.node_base
  simp only [PathObl.guard_ks_base]
  rw [L.ks_base_eq]
  simp only [bind_ok, lift]
  rw [eq_of_spec_fd layout.ks.NODES.spec, eq_of_spec_fd layout.node.SIZE.spec]
  simp only [bind_ok]
  exact guard_read (by unfold LawfulStore.nodeAt at h; exact h)

end

end Fl4Proofs.P2
