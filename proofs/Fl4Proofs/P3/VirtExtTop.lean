/-
P3x for virtualization (line virt, gen 6; proofs/VIRT-PLAN.md §10 "Remaining (R7)", top): **the exits of the
ported P3 tops transported to the extended spec** at `virtKind = none`, with `NR` carried along.

Every exit of the ported kernel-entry tops (U34 / U36I, XTopJointKEntryU36I: `syscall.handle_syscall … ⦃ r => ∃ σ',
((), σ') ∈ fl4KernelEntrySyscall true c σ ∧ … ⦄`, the events' `EvOut false ev σ σ'`) names a ported-spec outcome.
On an `NR` state off the routes, that outcome is an outcome of the extended spec (`fl4KernelEntrySyscallV`,
`fl4CallKernelV`) and is again `NR` (VirtNvK2), so the same FL4 run refines the extended spec and the next entry
is again in scope:

* `nr_fl4SyscallFaultIP`, `ScopeE` (the syscall entry's decode points, after the `FaultIP` write, off the
  routes), **`fl4KernelEntrySyscallV_eqNR`** (the extended syscall entry is the ported one), `nr_kentry`.
* **`kentryV_post`**: `m ⦃ r => ∃ σ', ported entry outcome ∧ P r σ' ⦄` ⇒ `m ⦃ r => ∃ σ', extended entry outcome
  ∧ P r σ' ∧ NR σ' ⦄` — applied to U36I's syscall clause (by `WP.spec_mono`) it is that clause against
  `fl4KernelEntrySyscallV`.
* `EvOutV`, **`evOutV_of`**, **`evV_post`**: the same for the interrupt and user-exception exits (non-syscall
  events, no scope needed).

Named premises:
* **`hvk : virtKind = .none` [S]** (route scope).
* **`hr : ScopeE c σ` [S]** (syscall exits only): the entry's decode points are off the three routes
  (`OffRouteS5`, VirtTcbOK). This is gen 5's `hr5` at the entry; on the on-route entries the extended spec
  answers with the route-B errors (`decOKV_thread88_noVirt`, `decOKV_frame60_noVirt`, `decOKV_untyped_vtxGate`
  with gen 2's [P] `hvirt`), which are decode-level posts not yet composed into a kernel-entry top: the ported
  tops relate FL4 to the *ported* outcome there, which differs from the extended one (the ported decoder accepts
  the VT-x retype that FL4 and the extended spec reject), so no transport exists for them.

No [J]/[P]/[W]. New file only.
-/
import Fl4Proofs.P3.VirtNvK2
import Fl4Proofs.P3.XTopJointKEntryEv
open Aeneas Aeneas.Std Result
open Classical

namespace Fl4Proofs.P3.VirtExtTop
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvTY Fl4Proofs.P3.VirtR7b Fl4Proofs.P3.VirtR7d Fl4Proofs.P3.VirtR7e
  Fl4Proofs.P3.VirtR7eK Fl4Proofs.P3.VirtTcbOK Fl4Proofs.P3.VirtNvK2

noncomputable section

theorem nr_fl4SyscallFaultIP (t : ObjRef) : SInv.IK NR (fl4SyscallFaultIP (Z := Unit) t) :=
  nr_of (SInvV.hv_fl4SyscallFaultIP t) (ty_fl4SyscallFaultIP t) (ns_fl4SyscallFaultIP t)

/-- **The syscall entry's scope** ([S], module docstring): every decode point after the `FaultIP` write is off
the three routes. -/
def ScopeE (c : Syscall) (σ : State Unit) : Prop :=
  ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1, ∀ t, EntryPt w.2 t → OffRouteS5 c t

/-- **The extended syscall entry is the ported one** on an `NR` state in scope. -/
theorem fl4KernelEntrySyscallV_eqNR (hvk : virtKind = .none) (onCore : ObjRef → Bool) (rep : Bool) (c : Syscall)
    {σ : State Unit} (hs : NR σ) (hr : ScopeE c σ) :
    fl4KernelEntrySyscallV (Z := Unit) onCore rep c σ = fl4KernelEntrySyscall rep c σ := by
  unfold fl4KernelEntrySyscallV fl4KernelEntrySyscall
  refine nd_bind_congr_on _ _ _ σ fun y hy => ?_
  simp only [NonDet.gets, Set.mem_singleton_iff] at hy
  subst hy
  refine nd_bind_congr_on _ _ _ σ fun w hw => ?_
  exact fl4CallKernelV_eqNR5 hvk onCore rep _ (nr_fl4SyscallFaultIP _ σ hs w hw)
    fun c' e t ht => by cases e; exact hr w hw t ht

/-- Every outcome of the ported syscall entry from an `NR` state in scope is `NR`. -/
theorem nr_kentry (hvk : virtKind = .none) {rep : Bool} {c : Syscall} {σ σ' : State Unit} (hs : NR σ)
    (hr : ScopeE c σ) (h : ((), σ') ∈ (fl4KernelEntrySyscall (Z := Unit) rep c σ).1) : NR σ' := by
  unfold fl4KernelEntrySyscall at h
  obtain ⟨y, hy, w, hw, hx⟩ := h
  simp only [NonDet.gets, Set.mem_singleton_iff] at hy
  subst hy
  exact nr_fl4CallKernel hvk rep _ (nr_fl4SyscallFaultIP _ σ hs w hw)
    (fun c' e t ht => by cases e; exact hr w hw t ht) _ hx

/-- **A ported-spec syscall exit is an extended-spec exit** (premises `hvk`, `hr` [S], module docstring). -/
theorem kentryV_post (hvk : virtKind = .none) (onCore : ObjRef → Bool) {α : Type} {m : Result α}
    {P : α → State Unit → Prop} {c : Syscall} {σ : State Unit} (hs : NR σ) (hr : ScopeE c σ)
    (h : m ⦃ r => ∃ σ', ((), σ') ∈ (fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧ P r σ' ⦄) :
    m ⦃ r => ∃ σ', ((), σ') ∈ (fl4KernelEntrySyscallV (Z := Unit) onCore true c σ).1 ∧ P r σ' ∧ NR σ' ⦄ := by
  refine WP.spec_mono h ?_
  intro r ⟨σ', h1, h2⟩
  refine ⟨σ', ?_, h2, nr_kentry hvk hs hr h1⟩
  rw [fl4KernelEntrySyscallV_eqNR hvk onCore true c hs hr]
  exact h1

/-- The extended counterpart of `EvOut false`. -/
def EvOutV (onCore : ObjRef → Bool) (ev : Event) (σ σ' : State Unit) : Prop :=
  ((), σ') ∈ (fl4CallKernelV (Z := Unit) onCore true ev σ).1

/-- **A ported-spec event exit (not a syscall) is an extended-spec exit**, and `NR` again. -/
theorem evOutV_of (hvk : virtKind = .none) (onCore : ObjRef → Bool) {ev : Event} {σ σ' : State Unit}
    (hev : ∀ c, ev ≠ .syscallEvent c) (hs : NR σ) (h : EvOut false ev σ σ') :
    EvOutV onCore ev σ σ' ∧ NR σ' := by
  have hr : ∀ c, ev = .syscallEvent c → ∀ t, EntryPt σ t → OffRouteS5 c t := fun c e => absurd e (hev c)
  refine ⟨?_, nr_fl4CallKernel hvk true ev hs hr _ h⟩
  show ((), σ') ∈ (fl4CallKernelV (Z := Unit) onCore true ev σ).1
  rw [fl4CallKernelV_eqNR5 hvk onCore true ev hs hr]
  exact h

theorem evV_post (hvk : virtKind = .none) (onCore : ObjRef → Bool) {α : Type} {m : Result α}
    {P : α → State Unit → Prop} {ev : Event} {σ : State Unit} (hev : ∀ c, ev ≠ .syscallEvent c) (hs : NR σ)
    (h : m ⦃ r => ∃ σ', EvOut false ev σ σ' ∧ P r σ' ⦄) :
    m ⦃ r => ∃ σ', EvOutV onCore ev σ σ' ∧ P r σ' ∧ NR σ' ⦄ := by
  refine WP.spec_mono h ?_
  intro r ⟨σ', h1, h2⟩
  obtain ⟨e1, e2⟩ := evOutV_of hvk onCore hev hs h1
  exact ⟨σ', e1, h2, e2⟩

end

end Fl4Proofs.P3.VirtExtTop
