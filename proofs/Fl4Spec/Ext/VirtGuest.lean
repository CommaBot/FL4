/-
FL4 differences (PORTING.md, "FL4 differences"): **x86 virtualization,
guest execution and the trusted layer's contract** (proofs/VIRT-PLAN.md
§7, §8, §10).

1. **Guest execution is a nondeterministic oracle**, as l4v's
   `do_user_op` (ADT_A) is for user code. While a thread is
   `runningVM`, one guest step (`GuestStep`) may change exactly: the
   guest-changed fields of that thread's VCPU (`VField.guestChanged`),
   its exit record (any value), and bytes of frames mapped writable under
   the thread's guest root (`GuestWritableByte` of `guestRootOf`). Nothing
   else changes: not the VCPU's binding, I/O bitmap or other fields, not
   another VCPU, not the ported state but those memory bytes (the
   isolation frame). It ends in an exit for the VMM (`pending`) or a host
   exit, possibly with a host interrupt the exit accepted.
   Guest-linear translations and TLBs are not modelled. GPA→HPA is exact:
   the step reads the guest tables of the state it runs in, so once an
   EPT unmap has returned no guest step on any core reaches the frame
   (FL4: `ept::invalidate` is synchronous on every core recorded in the
   root, `kernel/entry.rs` records the core under the serial gate before
   entry).
2. **The trusted hardware layer's contract** (`fl4-arch-x86_64` `vm::run`
   and its assembly) is the named premise shape `VmRunContract` [P]: the
   layer's effect, seen through a refinement relation, is a `GuestStep`;
   and its word-level frame `VmRunFrame` [P]: after a VM exit only the
   VCPU words of guest-changed fields, the exit area, the layer's cache
   words and the writable guest frames differ. No l4v counterpart beyond
   `do_user_op`'s `user_memory_update` frame (l4v trusts the machine).
3. **P3x for virtualization**: `NoVirtObjects`, the states with no VCPU
   and no guest table, and the statement shape `P3xVirt` (VIRT-PLAN.md
   §10; the theorems are in `Ext/VirtP3x`).

The ported modules are not changed.
-/
import Fl4Spec.Ext.VirtEpt

namespace Fl4Spec

noncomputable section
open Classical

/-- How a guest step ends, for the kernel (FL4 `vm::run`'s return value):
the host interrupt the exit accepted, if any (`none` also for VMM exits). -/
structure GuestOutcome where
  hostIrq : Option Irq

/-- The fields of a VCPU's table a guest step leaves alone: the
non-canonical places (unused) and every canonical field that is not
guest-changed. -/
def VcpuFrame (k : VirtKind) (vs vs' : VcpuState) : Prop :=
  vs'.tcb = vs.tcb ∧ vs'.ioDenied = vs.ioDenied ∧
  ∀ f, (f.canon k ≠ f ∨ f.guestChanged k = false) → vs'.fields f = vs.fields f

/-- **One guest step of thread `t`** (module docstring, 1; l4v ADT_A
`do_user_op` for guests). The heap changes only at the thread's VCPU
object (within `VcpuFrame`), the machine state only in memory bytes the
guest can write. -/
def GuestStep {Z : Type} (k : VirtKind) (t : ObjRef) (σ σ' : State Z) (o : GuestOutcome) : Prop :=
  ∃ (tcb : Tcb) (v : ObjRef) (vs vs' : VcpuState) (m' : Word64 → Word8),
    σ.kheap t = some (.tcb tcb) ∧ tcb.tcbState = .runningVM ∧
    tcbVcpuOf σ t = some v ∧ vcpuAt σ v = some vs ∧
    VcpuFrame k vs vs' ∧
    (o.hostIrq ≠ none → vs'.exit.pending = false) ∧
    σ' = { σ with kheap := Function.update σ.kheap v (some (.archObj (.vcpu vs'))),
                  machineState := { σ.machineState with underlyingMemory := m' } } ∧
    ∀ a, m' a ≠ σ.machineState.underlyingMemory a →
      GuestWritableByte σ (guestRootOf σ t) a

/-- **[P] The trusted layer's contract, abstract form** (module
docstring, 2). For any implementation state type `I`, relation `R` and
the layer's effect `run t s s' o` (one `vm::run` of thread `t`): a run
from a related state ends in a related state reached by one `GuestStep`
of the selected backend. -/
def VmRunContract {Z I : Type} (R : I → State Z → Prop)
    (run : ObjRef → I → I → GuestOutcome → Prop) : Prop :=
  ∀ t s s' o σ, R s σ → run t s s' o → ∃ σ', GuestStep virtKind t σ σ' o ∧ R s' σ'

/-- **[P] The trusted layer's contract, word-level frame** (module
docstring, 2): kernel memory `mem` before and `mem'` after a `vm::run`
differ only in the words of the VCPU's guest-changed fields
(`fieldWords`, the layout of the refinement), the exit area
(`exitWords`: FL4 `vcpu::EXIT`, `VALID`, `PENDING`, `CR2`, `REGS`, `MSRS`),
the layer's cache words (`cacheWords`: `SVM_CPU`, the VMCB ASID, clean
bits and the physical pointers it rewrites) and the writable guest
frames (`writable`). -/
def VmRunFrame (k : VirtKind) (fieldWords : VField → Set Word) (exitWords cacheWords writable : Set Word)
    (mem mem' : Word → Word) : Prop :=
  ∀ a, mem' a ≠ mem a →
    (∃ f, f.canon k = f ∧ f.guestChanged k = true ∧ a ∈ fieldWords f) ∨
    a ∈ exitWords ∨ a ∈ cacheWords ∨ a ∈ writable

/-- No virtualization object exists (module docstring, 3): the heap
holds no VCPU and no guest table (so no thread is bound to a VCPU). -/
def NoVirtObjects {Z : Type} (σ : State Z) : Prop :=
  ∀ p ao, σ.kheap p = some (.archObj ao) → (∀ st, ao ≠ .vcpu st) ∧ (∀ l es, ao ≠ .ept l es)

theorem NoVirtObjects.vcpuAt {Z : Type} {σ : State Z} (h : NoVirtObjects σ) (v : ObjRef) :
    vcpuAt σ v = none := by
  unfold Fl4Spec.vcpuAt
  split
  · rename_i st hk; exact absurd rfl ((h v _ hk).1 st)
  · rfl

theorem NoVirtObjects.tcbVcpuOf {Z : Type} {σ : State Z} (h : NoVirtObjects σ) (t : ObjRef) :
    tcbVcpuOf σ t = none :=
  tcbVcpuOf_none.2 fun v st hv => by rw [h.vcpuAt v] at hv; cases hv

/-- **The P3x statement shape for virtualization** (DESIGN.md §9, P3x;
VIRT-PLAN.md §10): on a state with no virtualization object, a step of
the extended kernel (`extStep`) is exactly a step of the ported one
(`portStep`). -/
def P3xVirt {Z : Type} (extStep portStep : State Z → State Z → Prop) : Prop :=
  ∀ σ, NoVirtObjects σ → ∀ σ', extStep σ σ' ↔ portStep σ σ'

/-- A guest step needs a VCPU: none happens without virtualization
objects. -/
theorem GuestStep.not_noVirt {Z : Type} {k : VirtKind} {t : ObjRef} {σ σ' : State Z}
    {o : GuestOutcome} (h : GuestStep k t σ σ' o) : ¬ NoVirtObjects σ := by
  obtain ⟨_, v, _, _, _, _, _, hv, _⟩ := h
  intro hn
  rw [hn.tcbVcpuOf] at hv
  cases hv

/-- The isolation frame: a guest step changes the heap only at the
thread's VCPU, and keeps that VCPU's binding. -/
theorem GuestStep.frame {Z : Type} {k : VirtKind} {t : ObjRef} {σ σ' : State Z}
    {o : GuestOutcome} (h : GuestStep k t σ σ' o) :
    ∃ v vs vs', tcbVcpuOf σ t = some v ∧ vcpuAt σ v = some vs ∧ vcpuAt σ' v = some vs' ∧
      vs'.tcb = vs.tcb ∧ ∀ p, p ≠ v → σ'.kheap p = σ.kheap p := by
  obtain ⟨_, v, vs, vs', _, _, _, hv, hvs, hfr, _, hσ, _⟩ := h
  refine ⟨v, vs, vs', hv, hvs, ?_, hfr.1, fun p hp => ?_⟩
  · subst hσ; simp [Fl4Spec.vcpuAt]
  · subst hσ; exact Function.update_of_ne hp _ _

end

end Fl4Spec
