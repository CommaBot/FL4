/-
P3 (line p3J, gen 4): **the spec's IOAPIC counts are kept by every kernel entry** (spec side only,
outside the JAtZ cone): `IOX m := FK ioxV m` (SpecInvIoxF) for the whole syscall entry and every event.

No spec step writes `x64_num_ioapics` or `x64_ioapic_nirqs` (Fl4Spec's only `archState` writers set
`x64_irq_state`, `x64_asid_table`, `x64_current_fpu_owner`, `x64_current_cr3`, `x64_allocated_io_ports`;
`Init` sets the counts once), so SpecInvDomF / G / E's domain-list frame, copied onto `ioxV`
(SpecInvIoxF / G / E), extends to the pieces the domain-list frame leaves out (they write the domain list,
not the counts): the Domain invocation's perform (`ioxe_fl4PerformAll`), `next_domain` and `schedule`.
* `ioxe_syscall`: the `syscall` shell (Syscall_A `syscall`) keeps a projection when its five parts do.
* `ioxe_handleInvocationR`, `ioxe_fl4HandleSyscall`, `ioxe_fl4HandleEvent`, `iox_fl4CallKernel`,
  `iox_fl4KernelEntrySyscall`.
* Tops: `kentry_ioxV` (syscall entry), `kcall_ioxV` (every event), `fip_ioxV` (the FaultIP write),
  `budget_ioxV` (the budget front).
No premise; no sorry.
-/
import Fl4Proofs.P3.SpecInvIoxE
open Classical

namespace Fl4Proofs.P3.SInvIox
open Fl4Spec Fl4Proofs.P3.Vs

noncomputable section

set_option maxRecDepth 20000

/-- `iox_auto` with `split` and `dsimp only` (matches on the decode's tuples and the thread state). -/
macro "iox_auto2" : tactic => `(tactic| repeat' (first | iox_leaf | dk_step0 | split | (dsimp only) |
  iox_unfold))

/-- **The `syscall` shell keeps a projection when its parts do.** -/
theorem ioxe_syscall {α β γ : Type} {mF : FMonad Unit α} {hF : Fault → SMonad Unit γ}
    {mE : α → SEMonad Unit β} {hE : SyscallError → SMonad Unit γ} {mFin : β → PMonad Unit γ}
    (h1 : IOXE mF) (h2 : ∀ x, IOX (hF x)) (h3 : ∀ x, IOXE (mE x)) (h4 : ∀ x, IOX (hE x))
    (h5 : ∀ x, IOXE (mFin x)) : IOXE (syscall (Z := Unit) mF hF mE hE mFin) := by
  unfold syscall withoutPreemption
  refine dke_bind (dke_liftE h1) fun r => ?_
  cases r with
  | error f => exact dke_liftE (h2 f)
  | ok a =>
    refine dke_bind (dke_liftE (h3 a)) fun r => ?_
    cases r with
    | error e => exact dke_liftE (h4 e)
    | ok b => exact h5 b

set_option maxHeartbeats 8000000 in
/-- **Every perform keeps the counts** (the Domain invocation's too: it writes the domain list only). -/
theorem ioxe_fl4PerformAll (blk call don : Bool) (inv : Fl4Invocation) :
    IOXE (fl4PerformInvocation (Z := Unit) blk call don inv) := by
  cases inv with
  | invokeDomain d => simp only [fl4PerformInvocation]; iox_auto2
  | _ => exact ioxe_fl4Perform blk call don _ (fun d h => by cases h)
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact ioxe_fl4PerformAll _ _ _ _)

set_option maxHeartbeats 4000000 in
theorem iox_nextDomain : IOX (nextDomain (Z := Unit)) := by
  unfold nextDomain; iox_auto2
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_nextDomain)

set_option maxHeartbeats 4000000 in
theorem iox_scheduleChooseNewThread : IOX (scheduleChooseNewThread (Z := Unit)) := by
  unfold scheduleChooseNewThread; iox_auto2
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_scheduleChooseNewThread)

set_option maxHeartbeats 4000000 in
theorem iox_schedule : IOX (schedule (Z := Unit)) := by
  unfold schedule; iox_auto2
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_schedule)

set_option maxHeartbeats 8000000 in
/-- **The invocation keeps the counts.** -/
theorem ioxe_handleInvocationR (rep calling blocking don fp : Bool) (cptr : CapRef) :
    IOXE (fl4HandleInvocationR (Z := Unit) rep calling blocking don fp cptr) := by
  unfold fl4HandleInvocationR
  refine dke_bind (by iox_auto2) fun thread => dke_bind (by iox_auto2) fun info => ?_
  refine ioxe_syscall (by iox_auto2) (fun _ => by iox_auto2) (fun a => ?_) (fun _ => by iox_auto2)
    (fun _ => by iox_auto2)
  obtain ⟨sl, cap, ex, buf⟩ := a
  iox_auto2
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact ioxe_handleInvocationR _ _ _ _ _ _)

set_option maxHeartbeats 8000000 in
theorem ioxe_fl4HandleSyscall (rep : Bool) (c : Syscall) : IOXE (fl4HandleSyscall (Z := Unit) rep c) := by
  cases c <;> simp only [fl4HandleSyscall] <;> iox_auto2

set_option maxHeartbeats 4000000 in
theorem ioxe_fl4HandleEvent (rep : Bool) (ev : Event) : IOXE (fl4HandleEvent (Z := Unit) rep ev) := by
  by_cases h : ∃ c, ev = .syscallEvent c
  · obtain ⟨c, rfl⟩ := h
    simp only [fl4HandleEvent]
    exact dke_bind (by iox_auto2) fun _ => dke_bind (by iox_auto2) fun _ =>
      dke_whenE _ (ioxe_fl4HandleSyscall rep c)
  · rw [fl4HandleEvent_other rep ev fun c e => h ⟨c, e⟩]
    exact ioxe_handleEvent_other ev fun c e => h ⟨c, e⟩

theorem iox_fl4CallKernel (rep : Bool) (ev : Event) : IOX (fl4CallKernel (Z := Unit) rep ev) := by
  unfold fl4CallKernel
  refine dk_bind (dke_handleE (ioxe_fl4HandleEvent rep ev) fun _ => by iox_auto2) fun _ => ?_
  exact dk_bind iox_fl4Awaken fun _ => dk_bind iox_schedule fun _ => iox_activateThread

theorem iox_fl4KernelEntrySyscall (rep : Bool) (c : Syscall) : IOX (fl4KernelEntrySyscall (Z := Unit) rep c) := by
  unfold fl4KernelEntrySyscall
  exact dk_bind (dk_gets _) fun ct => dk_bind (iox_fl4SyscallFaultIP ct) fun _ => iox_fl4CallKernel rep _

/-! ## Tops -/

/-- **The counts across a whole syscall entry.** -/
theorem kentry_ioxV (rep : Bool) (c : Syscall) (σ : State Unit) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) rep c) σ).1, ioxV y.2 = ioxV σ :=
  iox_fl4KernelEntrySyscall rep c σ

/-- **The counts across every kernel event.** -/
theorem kcall_ioxV (rep : Bool) (ev : Event) (σ : State Unit) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, ioxV y.2 = ioxV σ :=
  iox_fl4CallKernel rep ev σ

/-- The counts across the FaultIP write. -/
theorem fip_ioxV (t : ObjRef) (σ : State Unit) : ∀ y ∈ (fl4SyscallFaultIP (Z := Unit) t σ).1, ioxV y.2 = ioxV σ :=
  iox_fl4SyscallFaultIP t σ

/-- The counts across the budget front. -/
theorem budget_ioxV (σ : State Unit) :
    ∀ y ∈ ((updateTimeStamp (Z := Unit) >>= fun _ => checkBudgetRestart (Z := Unit)) σ).1, ioxV y.2 = ioxV σ :=
  dk_bind iox_updateTimeStamp (fun _ => iox_checkBudgetRestart) σ

end

end Fl4Proofs.P3.SInvIox
