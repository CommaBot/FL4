/-
P3x for virtualization (line virt, gen 19, item 1, witness): **the NoRunVM V → F transport applies at a state with
a VCPU** — the state hypotheses of `evOutVF_of_V_nr` / `kentryVF_of_V_nr` / `evOutVTF_of_V_nr`'s first premise
(P3/VirtV3FNoRun) hold at p3J's root-thread state with a VCPU object added.

* `addVcpu σ v`: `σ` with a blank (unbound) VCPU object at `v` (the object a VCPU retype creates,
  `default_arch_object`); `addVcpu_noRunVM`, `addVcpu_at`, `addVcpu_unbound`.
* **`σv_nonvac`**: at `σv v := addVcpu JBootQ.σ1 v` (any `v`): `NoRunVM`, a VCPU at `v`, and no event is a
  VMEnter call (`NotVmEnter`, the current thread has no VCPU).
* **`σv_transport`**: so every exit of the `V` step from `σv v` (syscall or event) is one of FL4's step
  `fl4CallKernelVF onCore remoteCur`, for every `onCore`, `remoteCur`.

What this does **not** witness: `v3OutF_of_v3Out_nr`'s antecedent `V3Out` (the V-side top) at a VCPU state — no
V-side top holds at VCPU states yet (VirtV3FNoRun's docstring: `kernel_entry_reachV3` needs `hvk` and `NR`).
`σv v` is a spec state only; it is not claimed reachable.

No named premise. New file only; no existing statement changed.
-/
import Fl4Proofs.P3.VirtV3FNoRun
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtWit19
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P2.Wit Fl4Proofs.P3.VirtR7d Fl4Proofs.P3.VirtNoRunStep
  Fl4Proofs.P3.VirtV3FNoRun

noncomputable section

/-- `σ` with a blank VCPU object at `v`. -/
def addVcpu (σ : State Unit) (v : ObjRef) : State Unit :=
  { σ with kheap := Function.update σ.kheap v (some (.archObj (.vcpu VcpuState.blank))) }

theorem addVcpu_noRunVM {σ : State Unit} (h : NoRunVM σ) (v : ObjRef) : NoRunVM (addVcpu σ v) := by
  intro p x hk
  unfold addVcpu at hk
  by_cases e : p = v
  · subst e; simp at hk
  · simp only [Function.update_of_ne e] at hk; exact h p x hk

theorem addVcpu_at (σ : State Unit) (v : ObjRef) : vcpuAt (addVcpu σ v) v = some VcpuState.blank := by
  unfold vcpuAt addVcpu; simp

theorem addVcpu_unbound {σ : State Unit} (h : ∀ t, tcbVcpuOf σ t = none) (v t : ObjRef) :
    tcbVcpuOf (addVcpu σ v) t = none := by
  refine tcbVcpuOf_none.2 fun w st hw => ?_
  by_cases e : w = v
  · subst e; rw [addVcpu_at] at hw; cases hw; simp [VcpuState.blank]
  · have : vcpuAt (addVcpu σ v) w = vcpuAt σ w := by unfold vcpuAt addVcpu; simp [Function.update_of_ne e]
    rw [this] at hw; exact tcbVcpuOf_none.1 (h t) w st hw

/-- p3J's root-thread state with a VCPU at `v`. -/
def σv (v : ObjRef) : State Unit := addVcpu JBootQ.σ1 v

/-- **The transport's state hypotheses hold at a VCPU state.** -/
theorem σv_nonvac (v : ObjRef) :
    NoRunVM (σv v) ∧ vcpuAt (σv v) v = some VcpuState.blank ∧ ∀ ev, NotVmEnter ev (σv v) :=
  ⟨addVcpu_noRunVM VirtWit10.σ1Q_noRunVM v, addVcpu_at _ v, fun ev => notVmEnter_of_unbound
    (addVcpu_unbound (fun t => VirtVcpuRel.tcbVcpuOf_none_of_nr VirtWit10.nr_σ1Q t) v _) ev⟩

/-- **Every `V` exit from the VCPU state is an exit of FL4's step.** -/
theorem σv_transport (v : ObjRef) (onCore remoteCur : ObjRef → Bool) :
    (∀ ev σ', VirtExtTop.EvOutV onCore ev (σv v) σ' → VirtF13.EvOutVF onCore remoteCur ev (σv v) σ') ∧
    (∀ c σ', ((), σ') ∈ (fl4KernelEntrySyscallV (Z := Unit) onCore true c (σv v)).1 →
      ((), σ') ∈ (fl4KernelEntrySyscallVF (Z := Unit) onCore remoteCur true c (σv v)).1) :=
  ⟨fun ev _ h => evOutVF_of_V_nr onCore remoteCur (σv_nonvac v).1 ((σv_nonvac v).2.2 ev) h,
   fun _ _ h => kentryVF_of_V_nr onCore remoteCur (σv_nonvac v).1 h⟩

end

end Fl4Proofs.P3.VirtWit19
