/-
P3 (line p3J, gen 16): **the TRAP_SYSCALLS antecedent at the root-thread witness `w1`**.

`kernel_entry_reachU45nv`'s syscall clause takes, per entry, the fact that the current TCB's flags word (read
after the entry's `FAULT_IP` write) has no `TRAP_SYSCALLS` bit (`hfl`). At `w1` the current thread is the root
TCB `rT` (`curT_w1`), its flags word `rT + 3456` is zero in `img1`, and the `FAULT_IP` register word
`rT + 256 + 8·17` is another word: **`w1_hfl`** states `hfl` at `w1` for every written value.

At later entries `hfl` is not an invariant of the run: the root thread can set its own `TRAP_SYSCALLS` flag
with its thread cap (`TCBSetFlags`), after which a syscall instruction is a trap entry (the clause
`handle_trap_syscall`), not a syscall entry. So it stays the syscall clause's per-entry case condition, as in
U45nv (the combined theorem, P3JCkRun, keeps it there).

Named premises: none. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.JBootQ1Disp
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.JBootQ
open Fl4Proofs.P3.JBoot
open fl4_core Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit

theorem cur_w1 : sched.cur_thread wst w1 = ok rT := by
  rw [cur_thread_eq (L := wL)]
  exact congrArg ok curT_w1

theorem fip_val : (regA rT layout.reg.FAULT_IP).val = 18446744071562101128 := by
  unfold regA layout.tcb.REGS layout.reg.FAULT_IP; rfl

theorem tfl_val : (tFlagsWA rT).val = 18446744071562104192 := by
  unfold tFlagsWA; rfl

/-- **`hfl` at `w1`** (module docstring). -/
theorem w1_hfl : ∀ ct v, sched.cur_thread wst w1 = ok ct →
    obj.Tcb.flags wst ct (wL.wr w1 (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄ := by
  intro ct v h
  rw [cur_w1] at h
  obtain rfl := ok_inj_ff h
  rw [flags_eq (L := wL), WP.spec_ok]
  have hne : widx (regA rT layout.reg.FAULT_IP) ≠ widx (tFlagsWA rT) := by
    intro e
    have := congrArg Fin.val e
    simp only [widx, fip_val, tfl_val] at this
    omega
  have hm : wL.mem (wL.wr w1 (regA rT layout.reg.FAULT_IP) v) (tFlagsWA rT) = wL.mem w1 (tFlagsWA rT) := by
    show Function.update w1.w (widx (regA rT layout.reg.FAULT_IP)) v (widx (tFlagsWA rT)) = w1.w (widx (tFlagsWA rT))
    rw [Function.update_of_ne hne.symm]
  rw [hm, mem1_al tfl_val (by decide), show img1 18446744071562104192 = 0#u64 by img1z]
  unfold fl4_abi.consts.tcb_flag.TRAP_SYSCALLS
  rfl

end Fl4Proofs.P3.JBootQ
