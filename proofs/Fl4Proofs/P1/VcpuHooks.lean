/-
# #57's VCPU hooks on the x86_64 path (main 991586ba)

PR #57 (AArch64 EL2 virtualization) changed two shared functions the proofs
extract:

* `sched.suspend` calls `vcpu.cancel_run` first, which is `ok (s, a)` on
  x86_64: `suspend_eq_old` (SyscallGen) makes it the pre-#57 body
  `sched.suspend_old` outright.
* `syscall.finish` calls `vcpu.check st ar s a (cur_thread s)` after
  `activate_thread` (`finish_eq_old`, SyscallGen). `vcpu.check` returns at
  once unless the thread is `TS_RUNNING_VM` (`check_of_ne`); then it
  completes a pending VMEnter (the exit report, or the bound notification's
  badge). This module turns a triple / an equation about `finish_old` (the
  pre-#57 body) into one about `finish`, given that the current thread at
  `finish_old`'s end is not `TS_RUNNING_VM` (`finish_of_old`,
  `finish_ok_of_old`).

On a native-scope state (no thread `RunningVM`: P3's `NativeScope`, the
proofs' VT-x boundary) the obligation holds, so on the x86_64 native path
`finish` is the pre-#57 `finish`.
-/
import Fl4Proofs.P1.QueueSchedStep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type _} (ar : machine.Arch A)

/-- **`vcpu.check` is a no-op off `TS_RUNNING_VM`.** -/
theorem check_of_ne (s : S) (a : A) (t : obj.Tcb) (h : L.mem s (stA t) ≠ sched.TS_RUNNING_VM) :
    vcpu.check st ar s a t = ok (s, a) := by
  unfold vcpu.check obj.Tcb.state
  have hb : (L.mem s (core.num.U64.wrapping_add t layout.tcb.STATE) != sched.TS_RUNNING_VM) = true := by
    rw [bne_iff_ne]; exact h
  simp only [lift, bind_ok, LawfulStore.read_eq, hb, ↓reduceIte, if_true]

/-- `cur_thread` returns `curW`. -/
theorem cur_thread_ok (s : S) : sched.cur_thread st s = ok (L.curW s) := by
  have h := sched.cur_thread.spec (L := L) s
  revert h
  cases sched.cur_thread st s <;> simp [WP.spec_vis, WP.spec_div, WP.spec_ok]
  all_goals (intro h; rw [h]; rfl)

/-- **`finish` from the pre-#57 `finish`, as a triple**: the extra
obligation is that the current thread at `finish_old`'s end is not
`TS_RUNNING_VM`. -/
theorem finish_of_old {s : S} {a : A} {P : S × A → Prop}
    (h : syscall.finish_old st ar s a ⦃ r => P r ∧ L.mem r.1 (stA (L.curW r.1)) ≠ sched.TS_RUNNING_VM ⦄) :
    syscall.finish st ar s a ⦃ P ⦄ := by
  rw [finish_eq_old]
  refine WP.spec_bind h ?_
  rintro ⟨s1, a1⟩ ⟨hP, hn⟩
  show (do let t ← sched.cur_thread st s1; vcpu.check st ar s1 a1 t) ⦃ P ⦄
  rw [cur_thread_ok]; simp only [bind_ok]; rw [check_of_ne ar s1 a1 _ hn]
  exact (WP.spec_ok _).2 hP

/-- **`finish` from the pre-#57 `finish`, as an equation.** -/
theorem finish_ok_of_old {s s' : S} {a a' : A} (h : syscall.finish_old st ar s a = ok (s', a'))
    (hn : L.mem s' (stA (L.curW s')) ≠ sched.TS_RUNNING_VM) :
    syscall.finish st ar s a = ok (s', a') := by
  rw [finish_eq_old, h]
  simp only [bind_ok, uncurry_apply_pair, cur_thread_ok]
  rw [check_of_ne ar s' a' _ hn]

end
end Fl4Proofs.P1
