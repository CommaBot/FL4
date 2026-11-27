/-
P3 (issue #16, g7e): **`FT` (hence `FpuOwnOK`) at the handled-event states**
the finish bundles are asked at (spec side only): fo1's `kcall_fpuOwn` cut
after `handleE`, as XTopJointKEntry27S's `fo_front` for the syscall entry.

* `fo_handleE_of`: from the handler's `HKE` facts (`ILF []`, `NQ []`), every
  outcome of `handleE (fl4HandleEvent rep ev) preemptionPath` has `FT`
  (`fo_fl4CallKernel_of`'s first half, `fo_preemptionPath`).
* `kcall_fo_ev`: at a non-syscall event from the entry state (the current
  thread active, or idle for an interrupt).
* `kcall_fo_fip`: at a non-syscall, non-interrupt event after the FaultIP
  write of the current thread (`juf_auto` across `fl4SyscallFaultIP`).
-/
import Fl4Proofs.P3.XTopJointKEntry27S

open Classical

namespace Fl4Proofs.P3.SInvF
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 2000000

theorem fo_handleE_of {rep : Bool} {ev : Event} {P : State Unit → Prop}
    (h : HKE P (ILF []) (fl4HandleEvent (Z := Unit) rep ev)) (hN : HKE P (NQ []) (fl4HandleEvent (Z := Unit) rep ev))
    (σ : State Unit) (hσ : P σ) :
    ∀ y ∈ ((NonDetE.handleE (fl4HandleEvent (Z := Unit) rep ev) (fun _ => withoutPreemption preemptionPath)).run σ).1,
      FT y.2 := by
  intro y hy
  unfold NonDetE.handleE at hy
  obtain ⟨z, hz, hy⟩ := hy
  have hz' : FN [] z.2 := ⟨⟨(h σ hσ z hz).1, hN σ hσ z hz⟩, (h σ hσ z hz).2⟩
  obtain ⟨r, s⟩ := z
  cases r with
  | ok a => rw [Set.mem_singleton_iff.1 hy]; exact hz'.2
  | error e =>
    obtain ⟨w, hw, rfl⟩ := ft_mem_liftE (m := preemptionPath (Z := Unit)) hy
    exact (fo_preemptionPath s hz' w hw).2

/-- **`FT` at a non-syscall event's handled states** (module docstring). -/
theorem kcall_fo_ev (rep : Bool) (ev : Event) (hev : ∀ c, ev ≠ .syscallEvent c) {σ : State Unit}
    (ha : ∃ x, σ.kheap σ.curThread = some (.tcb x) ∧
      (activeSt x.tcbState ∨ (ev = .interrupt ∧ x.tcbState = .idleThreadState)))
    (hN : NtfnQB σ ∧ EpQB σ) (hU : UtInv3 σ) (h : IfLiveT σ) (hF : FT σ) :
    ∀ y ∈ ((NonDetE.handleE (fl4HandleEvent (Z := Unit) rep ev) (fun _ => withoutPreemption preemptionPath)).run σ).1,
      FT y.2 := by
  obtain ⟨x0, hx0, ha0⟩ := ha
  have hNQ : NQ [σ.curThread] σ := by
    refine nq_cons ((nq_nil_iff σ).2 hN) fun x hx => ?_
    rw [hx0] at hx; cases hx
    rcases ha0 with h1 | ⟨-, h1⟩
    · exact ok_of_active h1
    · rw [h1]; exact ⟨fun h => h, rfl⟩
  by_cases hint : ev = .interrupt
  · subst hint
    exact fo_handleE_of (P := fun s => FN [] s ∧ NQ [σ.curThread] s ∧ s.curThread = σ.curThread)
      (hk_pre (by simp only [fl4HandleEvent]; exact fo_handleEvent_int) fun _ h => h.1)
      (hk_pre (nq_fl4HandleEvent_other σ.curThread rep .interrupt fun c e => by cases e) fun _ h => h.2)
      σ ⟨⟨⟨(il_nil_iff σ).2 h, nq_weak_nil _ hNQ⟩, hF⟩, hNQ, rfl⟩
  have hact : activeSt x0.tcbState := by
    rcases ha0 with h1 | ⟨h1, -⟩
    · exact h1
    · exact absurd h1 hint
  have hL : IL [σ.curThread] σ := il_consT ((il_nil_iff σ).2 h) (h _ x0 hx0 (live_of_active hact))
  have hE : HKE (fun s => FN [σ.curThread] s ∧ s.curThread = σ.curThread) (ILF []) (fl4HandleEvent (Z := Unit) rep ev) := by
    rw [fl4HandleEvent_other rep ev hev]; exact fo_handleEvent_other σ.curThread ev hev hint
  exact fo_handleE_of (P := fun s => FN [σ.curThread] s ∧ NQ [σ.curThread] s ∧ s.curThread = σ.curThread)
    (hk_pre hE fun _ h => ⟨h.1, h.2.2⟩)
    (hk_pre (nq_fl4HandleEvent_other σ.curThread rep ev hev) fun _ h => h.2)
    σ ⟨⟨⟨hL, nq_weak_nil _ hNQ⟩, hF⟩, hNQ, rfl⟩

/-- **`FT` at a non-syscall event's handled states after the FaultIP write**
(module docstring). -/
theorem kcall_fo_fip (rep : Bool) (ev : Event) (hev : ∀ c, ev ≠ .syscallEvent c) (hint : ev ≠ .interrupt)
    {σ : State Unit} (ha : ∃ x, σ.kheap σ.curThread = some (.tcb x) ∧ activeSt x.tcbState)
    (hN : NtfnQB σ ∧ EpQB σ) (hU : UtInv3 σ) (h : IfLiveT σ) (hF : FT σ) :
    ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
    ∀ y ∈ ((NonDetE.handleE (fl4HandleEvent (Z := Unit) rep ev) (fun _ => withoutPreemption preemptionPath)).run w.2).1,
      FT y.2 := by
  obtain ⟨x0, hx0, ha0⟩ := ha
  have hNQ : NQ [σ.curThread] σ := nq_cons ((nq_nil_iff σ).2 hN) fun x hx => by
    rw [hx0] at hx; cases hx; exact ok_of_active ha0
  have hJ : JF σ.interruptIrqNode σ.curThread σ :=
    ⟨⟨il_consT ((il_nil_iff σ).2 h) (h _ x0 hx0 (live_of_active ha0)), hNQ, rfl, hU, rfl⟩, hF⟩
  intro w hw
  have hJw : JF σ.interruptIrqNode σ.curThread w.2 := by
    refine (?_ : IK (JF σ.interruptIrqNode σ.curThread) _) σ hJ w hw
    juf_auto
  have hE : HKE (fun s => FN [σ.curThread] s ∧ s.curThread = σ.curThread) (ILF []) (fl4HandleEvent (Z := Unit) rep ev) := by
    rw [fl4HandleEvent_other rep ev hev]; exact fo_handleEvent_other σ.curThread ev hev hint
  exact fo_handleE_of (P := fun s => FN [σ.curThread] s ∧ NQ [σ.curThread] s ∧ s.curThread = σ.curThread)
    (hk_pre hE fun _ h => ⟨h.1, h.2.2⟩)
    (hk_pre (nq_fl4HandleEvent_other σ.curThread rep ev hev) fun _ h => h.2)
    w.2 ⟨⟨⟨hJw.1.1, nq_weak_nil _ hJw.1.2.1⟩, hJw.2⟩, hJw.1.2.1, hJw.1.2.2.1⟩

end

end Fl4Proofs.P3.SInvF
