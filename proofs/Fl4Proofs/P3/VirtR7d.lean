/-
P3x for virtualization, spec side (line virt, gen 3; proofs/VIRT-PLAN.md §10 "Remaining (R7)" (d)):
**without a `runningVM` thread the extended exit is the ported one**.

Spec: `Fl4Spec/Ext/VirtEntry` (`activateThreadV`, l4v `Tcb_A.activate_thread` with seL4's `RunningVM` case;
`vmCheck`, FL4 `vcpu::check`), `Fl4Spec/Ext/VirtKernel` (`fl4KernelExitV`, FL4 `kernel/entry.rs` `exit`), against
the ported l4v `Tcb_A.activate_thread` (`activateThread`) and the exit tail of `Ext/Entry`'s `fl4CallKernel`
(`fl4Awaken; schedule; activateThread`). Nothing of the port changes.

* `NoRunVM σ`: no TCB of `σ` is in `runningVM` (the R7 (d) state predicate). It is SpecInvNativeScopeF1's
  `NativeScopeS` (`noRunVM_iff`, definitional), so its preservation lemmas are the invA ones:
  `noRunVM_completeYieldTo`, `noRunVM_schedule`, `noRunVM_activateThread`, `noRunVM_fl4Awaken` and
  `noRunVM_fl4CallKernel` (every ported kernel event), `noRunVM_activateThreadV` (the extended activation).
* `activateThreadV_eq`: on a `NoRunVM` state `activateThreadV = activateThread` (outcome set and failure flag):
  the two agree up to the final `match` on the thread state, read after `completeYieldTo`, which keeps `NoRunVM`.
* `vmCheck_ctExit` / `activateThreadV_vmCheck`: every outcome of the ported `activateThread` is `CtExit`
  (SpecInvAllC: the current thread a `Running` or `IdleThreadState` TCB), where the exit's `vmCheck` of the
  current thread does nothing; so `activateThreadV; vmCheck ct` is `activateThread` on `NoRunVM` states.
* `exitTailV_eq`: `schedule; activateThreadV; vmCheck ct` is `schedule; activateThread` on `NoRunVM` states.
* `fl4KernelExitV_eq`: `fl4KernelExitV onCore` is the ported exit tail on a `NoRunVM` state whose extended timer
  step agrees with the ported one there (`haw`).

Premises (named hypotheses): `hn` (`NoRunVM`, the state fact of R7 (d)) and, for `fl4KernelExitV_eq` only, `haw`
(`fl4AwakenV onCore = fl4Awaken` at that state: the timer step's notification send is `sendSignalV`, R7 (a)'s
`sendSignalV_eq` at each fired timer; not composed here, an open item). No [J]/[P]/[W]; new file only.
-/
import Fl4Proofs.P3.VirtR7
import Fl4Proofs.P3.SpecInvNativeScope
import Fl4Proofs.P3.SpecInvAllC
open Classical

namespace Fl4Proofs.P3.VirtR7d
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

/-- **No thread is `runningVM`** (R7 (d)). -/
def NoRunVM (σ : State Unit) : Prop := ∀ p x, σ.kheap p = some (.tcb x) → x.tcbState ≠ .runningVM

/-- `NoRunVM` is invA's `NativeScopeS`. -/
theorem noRunVM_iff {σ : State Unit} : NoRunVM σ ↔ NativeScopeS σ := Iff.rfl

/-! ## Preservation -/

theorem noRunVM_completeYieldTo (t : ObjRef) : IK NoRunVM (completeYieldTo (Z := Unit) t) :=
  ns_completeYieldTo t

theorem noRunVM_schedule : IK NoRunVM (schedule (Z := Unit)) := ns_schedule

theorem noRunVM_activateThread : IK NoRunVM (activateThread (Z := Unit)) := ns_activateThread

theorem noRunVM_fl4Awaken : IK NoRunVM (fl4Awaken (Z := Unit)) := ns_fl4Awaken

theorem noRunVM_fl4CallKernel (rep : Bool) (ev : Event) : IK NoRunVM (fl4CallKernel (Z := Unit) rep ev) :=
  fun _ h y hy => kcall_nativeScope rep ev h y hy

/-! ## Generic -/

/-- A bind depends on the continuation only at the outcomes of the first computation. -/
theorem nd_bind_congr_on {σ α β : Type} (m : NonDet σ α) (k1 k2 : α → NonDet σ β) (s : σ)
    (h : ∀ x ∈ (m s).1, k1 x.1 x.2 = k2 x.1 x.2) : (m >>= k1) s = (m >>= k2) s := by
  rw [nd_bind_apply, nd_bind_apply]
  refine Prod.ext (Set.ext fun r => ?_) (propext ?_)
  · simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, hx, hr⟩; exact ⟨x, hx, by rw [← h x hx]; exact hr⟩
    · rintro ⟨x, hx, hr⟩; exact ⟨x, hx, by rw [h x hx]; exact hr⟩
  · constructor
    · rintro (h' | ⟨x, hx, h'⟩)
      · exact Or.inl h'
      · exact Or.inr ⟨x, hx, by rw [← h x hx]; exact h'⟩
    · rintro (h' | ⟨x, hx, h'⟩)
      · exact Or.inl h'
      · exact Or.inr ⟨x, hx, by rw [h x hx]; exact h'⟩

/-- A bind depends on the first computation only at the start state. -/
theorem nd_bind_eq_of {σ α β : Type} {m m' : NonDet σ α} {s : σ} (h : m s = m' s) (k : α → NonDet σ β) :
    (m >>= k) s = (m' >>= k) s := by
  rw [nd_bind_apply, nd_bind_apply, h]

/-! ## `activateThreadV` -/

/-- **R7 (d), the activation**: on a `NoRunVM` state `activateThreadV` is the ported `activateThread`. -/
theorem activateThreadV_eq {σ : State Unit} (hn : NoRunVM σ) :
    activateThreadV (Z := Unit) σ = activateThread σ := by
  unfold activateThreadV activateThread
  apply nd_bind_congr_on
  intro x hx
  rw [Set.mem_singleton_iff.1 hx]
  apply nd_bind_congr_on
  intro y hy
  unfold getTcbObjRef at hy
  obtain ⟨-, -, rfl⟩ := SInvQ.q1_mem_threadGet hy
  apply nd_bind_congr_on
  intro z hz
  have hz' : NoRunVM z.2 := ik_when _ (noRunVM_completeYieldTo _) σ hn z hz
  apply nd_bind_congr_on
  intro w hw
  unfold getThreadState at hw
  obtain ⟨x0, hk, rfl⟩ := SInvQ.q1_mem_threadGet hw
  have hst := hz' _ x0 hk
  dsimp only
  generalize x0.tcbState = st at hst ⊢
  cases st <;> first | rfl | exact absurd rfl hst

/-- `activateThreadV` keeps `NoRunVM`. -/
theorem noRunVM_activateThreadV : IK NoRunVM (activateThreadV (Z := Unit)) := by
  intro σ hn y hy
  rw [activateThreadV_eq hn] at hy
  exact noRunVM_activateThread σ hn y hy

/-! ## The exit's VCPU check -/

/-- The exit's `vmCheck` of the current thread does nothing at a `CtExit` state. -/
theorem vmCheck_ctExit {σ : State Unit} (h : SInvAll.CtExit σ) :
    (NonDet.gets (fun s : State Unit => s.curThread) >>= fun ct => vmCheck (Z := Unit) ct) σ =
      ({((), σ)}, False) := by
  obtain ⟨x, hk, hs⟩ := h
  rw [nd_bind_apply]
  have hv : vmCheck (Z := Unit) σ.curThread σ = ({((), σ)}, False) :=
    vmCheck_not_runningVM hk (by rcases hs with hs | hs <;> rw [hs] <;> exact fun h => by cases h)
  show ({r | ∃ x ∈ ({(σ.curThread, σ)} : Set (ObjRef × State Unit)), r ∈ (vmCheck x.1 x.2).1},
    False ∨ ∃ x ∈ ({(σ.curThread, σ)} : Set (ObjRef × State Unit)), (vmCheck x.1 x.2).2) = _
  simp only [Set.mem_singleton_iff, exists_eq_left, hv, false_or]
  rfl

/-- **R7 (d), the exit's VCPU check**: `activateThreadV; vmCheck ct` is `activateThread` on `NoRunVM`. -/
theorem activateThreadV_vmCheck {σ : State Unit} (hn : NoRunVM σ) :
    (activateThreadV (Z := Unit) >>= fun _ =>
      NonDet.gets (fun s : State Unit => s.curThread) >>= fun ct => vmCheck (Z := Unit) ct) σ =
      activateThread σ := by
  rw [nd_bind_eq_of (activateThreadV_eq hn)]
  refine VirtR7.nd_bind_pure_out _ _ σ fun y hy => ?_
  obtain ⟨⟨⟩, σ'⟩ := y
  exact vmCheck_ctExit (SInvAll.ctExit_activateThread σ _ hy)

/-- `schedule; activateThreadV; vmCheck ct` is the ported `schedule; activateThread` on `NoRunVM`. -/
theorem exitTailV_eq {σ : State Unit} (hn : NoRunVM σ) :
    (schedule (Z := Unit) >>= fun _ => activateThreadV (Z := Unit) >>= fun _ =>
      NonDet.gets (fun s : State Unit => s.curThread) >>= fun ct => vmCheck (Z := Unit) ct) σ =
      (schedule (Z := Unit) >>= fun _ => activateThread (Z := Unit)) σ :=
  nd_bind_congr_on _ _ _ σ fun y hy => activateThreadV_vmCheck (noRunVM_schedule σ hn y hy)

/-- **The extended exit is the ported exit tail** on a `NoRunVM` state whose extended timer step is the ported
one (`haw`, module docstring). -/
theorem fl4KernelExitV_eq (onCore : ObjRef → Bool) {σ : State Unit} (hn : NoRunVM σ)
    (haw : fl4AwakenV (Z := Unit) onCore σ = fl4Awaken σ) :
    fl4KernelExitV (Z := Unit) onCore σ =
      (fl4Awaken (Z := Unit) >>= fun _ => schedule (Z := Unit) >>= fun _ => activateThread (Z := Unit)) σ := by
  unfold fl4KernelExitV
  rw [nd_bind_eq_of haw]
  exact nd_bind_congr_on _ _ _ σ fun y hy => exitTailV_eq (noRunVM_fl4Awaken σ hn y hy)

end

end Fl4Proofs.P3.VirtR7d
