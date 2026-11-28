/-
P3 (DESIGN.md §9), invariant line G4 (g4b, KENTRY-PLAN g4b): **`JDispMR` [W]
narrowed to the invoking syscalls.** The receiving syscalls (`SysRecv`,
`SysNBRecv`, `SysWait`, `SysNBWait`) and `SysYield` touch no machine field
`MR` reads on either side, so their `MR` completion holds with the same
outcome:

* FL4: `dispatch_recv_mr` / `dispatch_yield_mr`: `dispatch_syscall` reads two
  registers and runs `handle_recv` / `handle_yield`, whose arch operations
  keep `MR` at a fixed machine state (`MKD.syscall_handle_recv` /
  `MKD.syscall_handle_yield`, MachKeepF).
* spec: their branches are `withoutPreemption` of `handleRecv` / `handleYield`
  (`MachT.mtk_handleRecvG` / `mtk_handleYieldG`, MachFieldFamS): every outcome
  is ok and keeps the four machine fields.
* `JDispMR.of_keep`: those two facts give `JDispMR` (the related outcome
  itself has `MR`, by `MachPlat.frame`).

`JDispMRI` [W] = `JDispMR` asked only for `InvSys` / `MidSys` numbers
(Send / NBSend / Call and ReplyRecv / NBSendRecv / NBSendWait); `jDispMR_of`
gives `JDispMR` for every native syscall. NEW TOP `kernel_entryJ37` (=
`kernel_entryJ36` with `hDM : JDispMRI`) and `kernel_entry_reachMI`.
-/
import Fl4Proofs.P3.XTopJointKEntry36
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

/-- **`JDispMR` from an `MR`-keeping FL4 run and a spec branch that keeps the
machine fields and never fails** (module docstring). -/
theorem JDispMR.of_keep (hM : MachPlat arI MR) {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64}
    {c : Fl4Spec.Syscall}
    (hW : MR a σ.machineState → syscall.dispatch_syscall st arI s a n ⦃ r => MR r.2 σ.machineState ⦄)
    (hF : ∀ y ∈ ((Fl4Spec.fl4HandleSyscall (Z := Unit) true c).run σ).1,
      MachF.msF y.2 = MachF.msF σ ∧ y.1 = .ok ()) :
    JDispMR (L := L) arI AR MR s a σ n c := by
  intro hR
  refine WP.spec_mono (hW hR) ?_
  rintro r hMr ⟨y, hy, ⟨h1, h2, h3⟩ | ⟨h1, -⟩⟩
  · exact ⟨y, hy, Or.inl ⟨h1, h2, h3, msF_mr hM hMr (hF y hy).1⟩⟩
  · rw [(hF y hy).2] at h1; cases h1

/-- **FL4's receiving dispatch keeps `MR`** (module docstring). -/
theorem dispatch_recv_mr (hKD : MRKeepD arI MR) (hA : P0.ArchTotal arI) {s : S} {a : A} {n : I64}
    {bl cr : Bool} (hn : RecvSys n bl cr) {c0 : Fl4Spec.MachineState} (h : MR a c0) :
    syscall.dispatch_syscall st arI s a n ⦃ r => MR r.2 c0 ⦄ := by
  have hct := cur_thread_eq (L := L) s
  unfold syscall.dispatch_syscall
  rw [hct]; simp only [bind_ok]
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s _ layout.reg.CAP) ?_
  rintro c0' -
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s _ layout.reg.REPLY) ?_
  rintro c1 -
  rcases hn with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · rw [if_neg (show fl4_abi.syscall.SysRecv ≠ fl4_abi.syscall.SysSend by unfold fl4_abi.syscall.SysRecv fl4_abi.syscall.SysSend; decide)]
    rw [if_neg (show fl4_abi.syscall.SysRecv ≠ fl4_abi.syscall.SysNBSend by unfold fl4_abi.syscall.SysRecv fl4_abi.syscall.SysNBSend; decide)]
    rw [if_neg (show fl4_abi.syscall.SysRecv ≠ fl4_abi.syscall.SysCall by unfold fl4_abi.syscall.SysRecv fl4_abi.syscall.SysCall; decide)]
    rw [if_pos rfl]
    exact MKD.syscall_handle_recv L.total hA hKD h
  · rw [if_neg (show fl4_abi.syscall.SysNBRecv ≠ fl4_abi.syscall.SysSend by unfold fl4_abi.syscall.SysNBRecv fl4_abi.syscall.SysSend; decide)]
    rw [if_neg (show fl4_abi.syscall.SysNBRecv ≠ fl4_abi.syscall.SysNBSend by unfold fl4_abi.syscall.SysNBRecv fl4_abi.syscall.SysNBSend; decide)]
    rw [if_neg (show fl4_abi.syscall.SysNBRecv ≠ fl4_abi.syscall.SysCall by unfold fl4_abi.syscall.SysNBRecv fl4_abi.syscall.SysCall; decide)]
    rw [if_neg (show fl4_abi.syscall.SysNBRecv ≠ fl4_abi.syscall.SysRecv by unfold fl4_abi.syscall.SysNBRecv fl4_abi.syscall.SysRecv; decide)]
    rw [if_pos rfl]
    exact MKD.syscall_handle_recv L.total hA hKD h
  · rw [if_neg (show fl4_abi.syscall.SysWait ≠ fl4_abi.syscall.SysSend by unfold fl4_abi.syscall.SysWait fl4_abi.syscall.SysSend; decide)]
    rw [if_neg (show fl4_abi.syscall.SysWait ≠ fl4_abi.syscall.SysNBSend by unfold fl4_abi.syscall.SysWait fl4_abi.syscall.SysNBSend; decide)]
    rw [if_neg (show fl4_abi.syscall.SysWait ≠ fl4_abi.syscall.SysCall by unfold fl4_abi.syscall.SysWait fl4_abi.syscall.SysCall; decide)]
    rw [if_neg (show fl4_abi.syscall.SysWait ≠ fl4_abi.syscall.SysRecv by unfold fl4_abi.syscall.SysWait fl4_abi.syscall.SysRecv; decide)]
    rw [if_neg (show fl4_abi.syscall.SysWait ≠ fl4_abi.syscall.SysNBRecv by unfold fl4_abi.syscall.SysWait fl4_abi.syscall.SysNBRecv; decide)]
    rw [if_pos rfl]
    exact MKD.syscall_handle_recv L.total hA hKD h
  · rw [if_neg (show fl4_abi.syscall.SysNBWait ≠ fl4_abi.syscall.SysSend by unfold fl4_abi.syscall.SysNBWait fl4_abi.syscall.SysSend; decide)]
    rw [if_neg (show fl4_abi.syscall.SysNBWait ≠ fl4_abi.syscall.SysNBSend by unfold fl4_abi.syscall.SysNBWait fl4_abi.syscall.SysNBSend; decide)]
    rw [if_neg (show fl4_abi.syscall.SysNBWait ≠ fl4_abi.syscall.SysCall by unfold fl4_abi.syscall.SysNBWait fl4_abi.syscall.SysCall; decide)]
    rw [if_neg (show fl4_abi.syscall.SysNBWait ≠ fl4_abi.syscall.SysRecv by unfold fl4_abi.syscall.SysNBWait fl4_abi.syscall.SysRecv; decide)]
    rw [if_neg (show fl4_abi.syscall.SysNBWait ≠ fl4_abi.syscall.SysNBRecv by unfold fl4_abi.syscall.SysNBWait fl4_abi.syscall.SysNBRecv; decide)]
    rw [if_neg (show fl4_abi.syscall.SysNBWait ≠ fl4_abi.syscall.SysWait by unfold fl4_abi.syscall.SysNBWait fl4_abi.syscall.SysWait; decide)]
    rw [if_pos rfl]
    exact MKD.syscall_handle_recv L.total hA hKD h

/-- **FL4's yield dispatch keeps `MR`** (module docstring). -/
theorem dispatch_yield_mr (hKD : MRKeepD arI MR) (hA : P0.ArchTotal arI) {s : S} {a : A}
    {c0 : Fl4Spec.MachineState} (h : MR a c0) :
    syscall.dispatch_syscall st arI s a fl4_abi.syscall.SysYield ⦃ r => MR r.2 c0 ⦄ := by
  have hct := cur_thread_eq (L := L) s
  unfold syscall.dispatch_syscall
  rw [hct]; simp only [bind_ok]
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s _ layout.reg.CAP) ?_
  rintro c0' -
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s _ layout.reg.REPLY) ?_
  rintro c1 -
  rw [if_neg (show fl4_abi.syscall.SysYield ≠ fl4_abi.syscall.SysSend by unfold fl4_abi.syscall.SysYield fl4_abi.syscall.SysSend; decide)]
  rw [if_neg (show fl4_abi.syscall.SysYield ≠ fl4_abi.syscall.SysNBSend by unfold fl4_abi.syscall.SysYield fl4_abi.syscall.SysNBSend; decide)]
  rw [if_neg (show fl4_abi.syscall.SysYield ≠ fl4_abi.syscall.SysCall by unfold fl4_abi.syscall.SysYield fl4_abi.syscall.SysCall; decide)]
  rw [if_neg (show fl4_abi.syscall.SysYield ≠ fl4_abi.syscall.SysRecv by unfold fl4_abi.syscall.SysYield fl4_abi.syscall.SysRecv; decide)]
  rw [if_neg (show fl4_abi.syscall.SysYield ≠ fl4_abi.syscall.SysNBRecv by unfold fl4_abi.syscall.SysYield fl4_abi.syscall.SysNBRecv; decide)]
  rw [if_neg (show fl4_abi.syscall.SysYield ≠ fl4_abi.syscall.SysWait by unfold fl4_abi.syscall.SysYield fl4_abi.syscall.SysWait; decide)]
  rw [if_neg (show fl4_abi.syscall.SysYield ≠ fl4_abi.syscall.SysNBWait by unfold fl4_abi.syscall.SysYield fl4_abi.syscall.SysNBWait; decide)]
  rw [if_neg (show fl4_abi.syscall.SysYield ≠ fl4_abi.syscall.SysReplyRecv by unfold fl4_abi.syscall.SysYield fl4_abi.syscall.SysReplyRecv; decide)]
  rw [if_neg (show fl4_abi.syscall.SysYield ≠ fl4_abi.syscall.SysNBSendRecv by unfold fl4_abi.syscall.SysYield fl4_abi.syscall.SysNBSendRecv; decide)]
  rw [if_neg (show fl4_abi.syscall.SysYield ≠ fl4_abi.syscall.SysNBSendWait by unfold fl4_abi.syscall.SysYield fl4_abi.syscall.SysNBSendWait; decide)]
  rw [if_pos trivial]
  exact MKD.syscall_handle_yield L.total hA hKD h

end

end

end Fl4Proofs.P3
