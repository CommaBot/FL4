/-
P3x for virtualization (line virt, gen 15, item 3, first step): **beyond the `NR` epoch — the F and V VCPU
operations agree on every `NoRunVM` state, VCPUs allowed.**

Gen 13's top (`kernel_entry_reachV3F`, P3/VirtKEntryV3F) quantifies over `NR = NV ∧ NoRunVM` states: no
virtualization cap, no VCPU, no `runningVM` thread (and `hvk : virtKind = .none` [S] keeps it so). The next epoch
lets VCPUs and their caps exist (`virtKind ≠ .none`: VT-x retypes, SetTCB, the VCPU invocations) but still has no
thread in `runningVM` — the state before the first VMEnter, and every state between a VMEnter's completion and the
next one. The F ops (Ext/VirtReport, Ext/VirtKernelF: FL4's report) differ from the V ops only where a `runningVM`
thread is completed (`vmReportF` vs `vmReport`), in `vmEnterF` itself (#85, FL4 `enter`) and in `sendSignalVF`'s
`runningVM` branch. So on `NoRunVM` states, off VMEnter, F = V; this module proves the leaves:

* `getVcpu_state`, `noRunVM_setVcpu`, `noRunVM_vcpuUpdate`, **`noRunVM_vcpuDetach`** (the V detach keeps
  `NoRunVM`).
* **`vcpuDetachF_eq_nr`**: `NoRunVM σ ⇒ vcpuDetachF t σ = vcpuDetach t σ` (any `t`; gen 12's `vcpuDetachF_eq`
  needed `t` to be a TCB).
* **`associateVcpuTcbF_eq_nr`** (SetTCB), **`performVcpuInvocationF_eq_nr`**: every VCPU invocation of the F
  kernel is the V one on a `NoRunVM` state (VMEnter is not a `VcpuInvocation`: it is the `SysVMEnter` syscall).
* Not here: `finaliseCapVF = finaliseCapV` on `NoRunVM` states. Its two hooked arms are `vcpuDetachF_eq_nr` under a
  bind, but the case split over `Cap`/`ArchCap` (the unhooked arms closed by unfolding both matchers) hit a kernel
  deterministic timeout / 12 GB in gen 15's attempts; it needs the arms stated one by one (open item).
* With gen 13's `sendSignalVF_eq_nr` / VirtAwaken's `sendSignalV_eq_nr` (both need only `NoRunVM`), the F/V
  signal ops agree there too (`sendSignalVF_eq_V_nr`).

What is left for the F top beyond `NR` (analysis, handoff): (1) the F twins of the step-level `NR` lemmas with `NV`
dropped — VirtR7b/R7e's `NV` frames are exactly what stops VCPU objects; the `NoRunVM` frames (`ns_*`, VirtR7d)
already exist; (2) the VMEnter route itself (`vmEnterF`, the `SysVMEnter` syscall) which ends `NoRunVM`; then
`remoteCur` becomes a per-entry fact (FL4's `node::CUR_THREAD` table) and `vmCheckF` at the exit; (3) `hvk`
replaced by `virtKind`'s VT-x gate open, with gen 15's retype relation (P3/VirtRetypeInit) for the new objects.

No named premise; no [J]/[P]/[W]/[S]. New file only; no existing statement changed.
-/
import Fl4Proofs.P3.VirtF13
import Fl4Proofs.P3.VirtRetypeInit
open Classical

namespace Fl4Proofs.P3.VirtNoRunF
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.VirtR7d Fl4Proofs.P3.VirtReportEq

noncomputable section

theorem getVcpu_state {σ : State Unit} {v : ObjRef} {y : VcpuState × State Unit}
    (hy : y ∈ (getVcpu (Z := Unit) v σ).1) : y.2 = σ ∧ vcpuAt σ v = some y.1 := by
  unfold getVcpu at hy
  obtain ⟨z, hz, hy⟩ := hy
  unfold getObject NonDet.getsThe readObject at hz
  unfold vcpuAt
  cases h : σ.kheap v with
  | none => rw [h] at hz; exact hz.elim
  | some k =>
    rw [h] at hz
    obtain rfl := Set.mem_singleton_iff.1 hz
    revert hy
    cases k
    all_goals try (intro hy; exact False.elim hy)
    rename_i a
    cases a
    all_goals try (intro hy; exact False.elim hy)
    intro hy
    obtain rfl := Set.mem_singleton_iff.1 hy
    exact ⟨rfl, rfl⟩

theorem noRunVM_setVcpu {σ : State Unit} (hn : NoRunVM σ) {v : ObjRef} {st : VcpuState} {x : Unit × State Unit}
    (hx : x ∈ (setVcpu (Z := Unit) v st σ).1) : NoRunVM x.2 := by
  rw [VirtRetypeInit.setVcpu_out hx]
  intro p t hp
  by_cases e : p = v
  · subst e; simp at hp
  · simp only [Function.update_of_ne e] at hp
    exact hn p t hp

theorem noRunVM_vcpuUpdate {σ : State Unit} (hn : NoRunVM σ) {v : ObjRef} {f : VcpuState → VcpuState}
    {x : Unit × State Unit} (hx : x ∈ (vcpuUpdate (Z := Unit) v f σ).1) : NoRunVM x.2 := by
  obtain ⟨y, hy, hx⟩ := hx
  obtain ⟨e, -⟩ := getVcpu_state hy
  exact noRunVM_setVcpu (e ▸ hn) hx

theorem noRunVM_vcpuDetach {σ : State Unit} (hn : NoRunVM σ) {t : ObjRef} {x : Unit × State Unit}
    (hx : x ∈ (vcpuDetach (Z := Unit) t σ).1) : NoRunVM x.2 := by
  unfold vcpuDetach at hx
  rw [nd_bind_one (getTcbVcpu_eq σ t)] at hx
  cases hv : tcbVcpuOf σ t with
  | none =>
    rw [hv] at hx
    obtain rfl := Set.mem_singleton_iff.1 hx
    exact hn
  | some v =>
    rw [hv] at hx
    dsimp only at hx
    obtain ⟨z, hz, hx⟩ := hx
    obtain ⟨e2, xt, hk, e1⟩ := PPS.getThreadState_mem hz
    have hs : z.1 ≠ .runningVM := by rw [← e1]; exact hn _ _ hk
    dsimp only at hx
    unfold NonDet.when at hx
    rw [if_neg hs] at hx
    obtain ⟨w, hw, hx⟩ := hx
    obtain rfl := Set.mem_singleton_iff.1 hw
    exact noRunVM_vcpuUpdate (e2 ▸ hn) hx

/-- **`vcpuDetachF` is `vcpuDetach` on `NoRunVM` states** (any thread). -/
theorem vcpuDetachF_eq_nr {σ : State Unit} (hn : NoRunVM σ) (t : ObjRef) :
    vcpuDetachF (Z := Unit) t σ = vcpuDetach t σ := by
  unfold vcpuDetachF vcpuDetach
  rw [nd_bind_one (getTcbVcpu_eq σ t), nd_bind_one (getTcbVcpu_eq σ t)]
  cases tcbVcpuOf σ t with
  | none => rfl
  | some v =>
    dsimp only
    refine nd_bind_congr_on _ _ _ σ fun z hz => ?_
    obtain ⟨e2, xt, hk, e1⟩ := PPS.getThreadState_mem hz
    have hs : z.1 ≠ .runningVM := by rw [← e1]; exact hn _ _ hk
    try dsimp only
    unfold NonDet.when
    rw [if_neg hs, if_neg hs]

/-- **SetTCB's association, F = V on `NoRunVM` states.** -/
theorem associateVcpuTcbF_eq_nr {σ : State Unit} (hn : NoRunVM σ) (v t : ObjRef) :
    associateVcpuTcbF (Z := Unit) v t σ = associateVcpuTcb v t σ := by
  unfold associateVcpuTcbF associateVcpuTcb
  rw [nd_bind_eq_of (vcpuDetachF_eq_nr hn t)]
  refine nd_bind_congr_on _ _ _ σ fun y hy => ?_
  have hn1 := noRunVM_vcpuDetach hn hy
  refine nd_bind_congr_on _ _ _ y.2 fun z hz => ?_
  obtain ⟨e, -⟩ := getVcpu_state hz
  have hn2 : NoRunVM z.2 := e ▸ hn1
  try dsimp only
  cases z.1.tcb with
  | none => rfl
  | some old =>
    try dsimp only
    exact nd_bind_eq_of (vcpuDetachF_eq_nr hn2 old) _

/-- **Every VCPU invocation, F = V on `NoRunVM` states.** -/
theorem performVcpuInvocationF_eq_nr {σ : State Unit} (hn : NoRunVM σ) (i : VcpuInvocation) :
    performVcpuInvocationF (Z := Unit) i σ = performVcpuInvocation i σ := by
  cases i with
  | setTcb v t =>
    simp only [performVcpuInvocationF, performVcpuInvocation]
    exact nd_bind_eq_of (associateVcpuTcbF_eq_nr hn v t) _
  | _ => rfl

/-- The signal ops, F = V on `NoRunVM` states (gen 13 / gen 7 leaves). -/
theorem sendSignalVF_eq_V_nr (onCore remoteCur : ObjRef → Bool) {σ : State Unit} (hn : NoRunVM σ) (n : ObjRef)
    (b : Badge) : sendSignalVF (Z := Unit) onCore remoteCur n b σ = sendSignalV onCore n b σ :=
  (VirtF13.sendSignalVF_eq_nr onCore remoteCur hn n b).trans (VirtAwaken.sendSignalV_eq_nr onCore hn n b).symm

end
end Fl4Proofs.P3.VirtNoRunF
