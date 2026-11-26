/-
# P1 (AArch64): `syscall.finish` without its `vcpu.check` tail

The AArch64 counterpart of x86_64's `Fl4Proofs.P1.VcpuHooks` (its `finish` half). AArch64 has no
`SyscallGen`, so the reference body `syscall.finish_old` (`schedule`, then `activate_thread`: x86_64
`SyscallGen.syscall.finish_old`, text identical) is defined here, and `finish_eq_old` is proved by
unfolding (x86_64 proves it in `SyscallGen`).

AArch64's `syscall.finish` (syscall.rs) ends with `vcpu.check (cur_thread)` like x86_64's. AArch64's
`vcpu.check` (arch/aarch64/vcpu.rs) also returns at once unless the thread is `TS_RUNNING_VM`
(`check_of_ne`); otherwise it completes an `ARMVCPURun` (stale `RUN_VCPU`, or the bound notification's
badge as an `INTERRUPT` stop). So a triple / an equation about `finish_old` gives one about `finish`
when the current thread at `finish_old`'s end is not `TS_RUNNING_VM` (`finish_of_old`,
`finish_ok_of_old`), as on x86_64.

`sched.suspend`'s `vcpu.cancel_run` hook (the other half of x86_64's VcpuHooks) is not the identity on
AArch64; it is handled in `QueueCancel` (`vcpu.cancel_run.idle`).

No premises.
-/
import Fl4ProofsA64.P1.QueueSchedStep
open Aeneas Aeneas.Std Result

namespace fl4_core_a64

/-- The body of `syscall.finish` without its `vcpu.check` tail (x86_64 `SyscallGen.syscall.finish_old`,
the pre-#57 body, same text). -/
def syscall.finish_old
  {S : Type _} {A : Type _} (machineStoreInst : machine.Store S)
  (machineArchInst : machine.Arch A) (s : S) (a : A) :
  Result (S × A)
  := do
  let (s1, a1) ← sched.schedule machineStoreInst machineArchInst s a
  sched.activate_thread machineStoreInst machineArchInst s1 a1

end fl4_core_a64

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {A : Type _} {st : machine.Store S} {ar : machine.Arch A}

/-- `finish` is `finish_old` followed by `vcpu.check (cur_thread)` (x86_64 `SyscallGen.finish_eq_old`). -/
theorem finish_eq_old (s : S) (a : A) :
    syscall.finish st ar s a = (do
      let (s2, a2) ← syscall.finish_old st ar s a
      let t ← sched.cur_thread st s2
      vcpu.check st ar s2 a2 t) := by
  unfold syscall.finish syscall.finish_old
  try simp only [Std.bind_assoc, bind_ok, uncurry_apply_pair]
  refine congrArg (Std.bind (sched.schedule st ar s a)) (funext fun r => ?_)
  obtain ⟨s1, a1⟩ := r
  first
    | rfl
    | (simp only [Std.bind_assoc, bind_ok, uncurry_apply_pair, Bool.false_eq_true, ↓reduceIte]; done)
    | (simp only [Std.bind_assoc, bind_ok, uncurry_apply_pair, Bool.false_eq_true, ↓reduceIte]; rfl)

end

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type _} (ar : machine.Arch A)

/-- **`vcpu.check` is a no-op off `TS_RUNNING_VM`** (AArch64 `vcpu::check`). -/
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

/-- **`finish` from `finish_old`, as a triple**: the extra obligation is that the current thread at
`finish_old`'s end is not `TS_RUNNING_VM`. -/
theorem finish_of_old {s : S} {a : A} {P : S × A → Prop}
    (h : syscall.finish_old st ar s a ⦃ r => P r ∧ L.mem r.1 (stA (L.curW r.1)) ≠ sched.TS_RUNNING_VM ⦄) :
    syscall.finish st ar s a ⦃ P ⦄ := by
  rw [finish_eq_old]
  refine WP.spec_bind h ?_
  rintro ⟨s1, a1⟩ ⟨hP, hn⟩
  show (do let t ← sched.cur_thread st s1; vcpu.check st ar s1 a1 t) ⦃ P ⦄
  rw [cur_thread_ok]; simp only [bind_ok]; rw [check_of_ne ar s1 a1 _ hn]
  exact (WP.spec_ok _).2 hP

/-- **`finish` from `finish_old`, as an equation.** -/
theorem finish_ok_of_old {s s' : S} {a a' : A} (h : syscall.finish_old st ar s a = ok (s', a'))
    (hn : L.mem s' (stA (L.curW s')) ≠ sched.TS_RUNNING_VM) :
    syscall.finish st ar s a = ok (s', a') := by
  rw [finish_eq_old, h]
  simp only [bind_ok, uncurry_apply_pair, cur_thread_ok]
  rw [check_of_ne ar s' a' _ hn]

end
end Fl4ProofsA64.P1
