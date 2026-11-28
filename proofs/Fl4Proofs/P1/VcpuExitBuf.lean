/-
# P1 (vexit gen 2): `handle_vcpu_exit` keeps `EntryInv`, the buffer placement carried

`syscall.handle_vcpu_exit.entry` (P1/VcpuExitInv) took the IPC-buffer placement
`BufAt` and the guard `G` of `check_budget` as premises at the run's
intermediate states, and the timeout faults as `TmoKG … G` (over every state
where `G` and the invariants hold). Here the run carries the buffer-lookup
frame `IbFr` from the entry state instead:

* `update_timestamp` writes two words of the current node (`FootB` over empty
  object sets, `footB0_fld`): every TCB word is kept, so the buffer lookups,
  the current thread's state and its VCPU word are the entry's;
* `vcpu.check`: `VckW.ibFr`;
* `check_budget`: `sched.check_budget.allGB` (this module), `QueueBudgetG`'s
  walk with the frame step `FootB` (no `IPC_BUFFER` word) and the timeout
  premise pinned to the check's start `s0` (`TmoGB s0 G`: at states reached
  from `s0` by `ChgW` writes, with `CurOK`), instantiated with `G := IbFr`
  from the check's start (`TmoIb`);
* `handle_interrupt`: `interrupt.handle_interrupt.ibx` (signal: `ibKeep_holds`;
  timer: node words; IPI: `reschedule_required.kwB`);
* `finish_old`: `sched.schedule.ibFr` (sib) and `activate_thread.tw` / `TW.ibFr`.

`IbKeep` is a theorem (`ibKeep_holds`), so it is no premise here.

**`syscall.handle_vcpu_exit.entryB`**: from `EntryInv` and `BufAt U` at the
entry state, the exit state satisfies `EntryInv`. Named premises:

* `hBA` [P] `BufAt U s` at the entry (the IPC-buffer placement; P3 facts);
* `hPd` [P] `PendAt U s` at the entry: a `TS_RUNNING_VM` current thread's bound
  VCPU `PENDING` word is in `U` (`vmpl`'s second half);
* `htk` [P] (only when not stalled) `TmoIb` at the state `check_budget` starts
  from: a timeout fault raised there (after `ChgW` writes, current thread
  schedulable) keeps `BXI` and every TCB's buffer-lookup words. Narrower than
  `TmoKG` (whose `Foot`-closed guard cannot give `CanBlock` of the current
  thread: `Foot` may make the idle thread current, P1/EntryVacuous);
* `hI` [P] (when an IRQ came) `IrqNtAt` after `vexit_pre`: the IRQ slots name
  heap notifications (`vcpu.check`'s `VckR` and the fault IPC's `CapW ∧ KG`
  words may reach the kernel-global block, so no frame keeps them here);
* `hPF` [P] `PendAt U` at the state `finish_old` leaves (the thread `schedule`
  picks; no P1 frame keeps the TCBs' VCPU words across the run, vk did that
  only in P2's `PrW`).

Discharged against `handle_vcpu_exit.entry`: `hGF`, `htmo` (replaced by the
pinned `htk`), `hUt` (all of it: `VmPl` after `update_timestamp` from
`hBA`/`hPd`, no guard), `hI`'s `BufAt`, `hF`'s `BufAt` and `finish_old`'s
`BufAt` half of `VmPl`, and `IK`.
-/
import Fl4Proofs.P1.VcpuExitInv
import Fl4Proofs.P1.SchedFootB
import Fl4Proofs.P2.EntryTail
import Fl4Proofs.P2.EntryIrq
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {A : Type _} {ar : machine.Arch A} {Ac : Set U64}
variable {U : Set U64}

/-! ## The budget check with a `FootB` frame (QueueBudgetG's walk) -/

/-- `finish_old` (`schedule`, `activate_thread`) keeps the buffer lookups. -/
theorem syscall.finish_old.ibx (hA : P0.ArchTotal ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hBA : BufAt st T Cs H Sg Scs Z U s) :
    syscall.finish_old st ar s a ⦃ s' _ => IbFr (L := L) T s s' ⦄ := by
  unfold syscall.finish_old
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hSg, hS⟩ := h
  refine WP.spec_bind (WP.spec_and
    (sched.schedule.entry hA (ibKeep_holds hA) hNt s a Q R h0 hB hS hX hSg hBA)
    (sched.schedule.ibFr hA (ibKeep_holds hA) hNt s a ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ hBA)) ?_
  rintro ⟨s1, a1⟩ ⟨E1, I1⟩
  have hq1 := E1.1.choose_spec.choose_spec
  exact WP.spec_mono (Fl4Proofs.P2.Stall.sched.activate_thread.tw hA s1 a1 (EntryInv.bxi E1).blk)
    fun r hr => by
      obtain ⟨s', a'⟩ := r
      exact I1.trans (Fl4Proofs.P2.Stall.TW.ibFr hq1 hq1.curT hr.1)

end

end Fl4Proofs.P1
