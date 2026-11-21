/-
FL4 differences (PORTING.md, "FL4 differences"): **x86 virtualization,
P3x** (DESIGN.md §2 superset rule, §9 P3x; proofs/VIRT-PLAN.md §10).

P3x for virtualization says: with no VCPU or EPT object and no
virtualization cap, the extended kernel is the ported one. This module
states it precisely at the dispatcher and the hooks and proves those
parts; the kernel-level composition (through `rec_del`'s fixed point and
every ported operation's preservation of `NoVirtObjects`) is VIRT-PLAN.md
§11 R7.

1. **Decode** (`fl4DecodeInvocationV_base`, proved): off the
   virtualization routes (`VirtRoute`), the extended decoder is the ported
   one. The routes are VCPU and EPT caps (absent under `NoVirtCaps`), an
   EPT-mapped frame's map/unmap (absent), an ASID-pool assign of an EPT
   root (absent) — and three that exist without any virtualization object:
   label 60 (`X86PageMapEPT`) on a frame cap, label 88 (`TCBSetEPTRoot`) on
   a thread cap, and the VT-x retype gate of an untyped cap (when
   `virtKind = none`). On those three the extended kernel returns FL4's
   error (`TruncatedMessage`, `InvalidArgument 0`, `InvalidCapability 1`,
   ... as the checks fall), the ported one l4v's (`IllegalOperation` for
   the two unknown labels; the ported retype even creates the VT-x
   objects). These are the exact exceptions of P3x (VIRT-PLAN.md §10).
2. **Perform** (`fl4PerformInvocationV_base`, proved): every ported
   invocation but the four substituted ones (untyped, notification send,
   TCB, CNode) is performed by the ported code.
3. **Hooks** (proved): `finaliseCapV` is `finaliseCap` on every cap but the
   hooked ones (`finaliseCapV_eq`); on a state without virtualization
   objects `vcpuDetach` and a thread cap's hook do nothing
   (`vcpuDetach_noVirt`, `finaliseCapV_thread_noVirt`); `vmCheck` of a
   thread not `runningVM` does nothing (`vmCheck_not_runningVM`);
   `ioPortRevoke` does nothing with the owner adapter (`ioPortRevoke_eq`).

The ported modules are not changed.
-/
import Fl4Spec.Ext.VirtKernel

namespace Fl4Spec

noncomputable section
open Classical

/-- A capability of the virtualization extension: a VCPU cap, an EPT cap,
an EPT-mapped frame cap. -/
def IsVirtCap : Cap → Prop
  | .archObjectCap (.vcpuCap _) => True
  | .archObjectCap (.eptCap _ _ _) => True
  | .archObjectCap (.pageCap _ _ _ .vmEptMap _ _) => True
  | _ => False

/-- No object holds a virtualization cap. -/
def NoVirtCaps {Z : Type} (σ : State Z) : Prop :=
  ∀ p ko, σ.kheap p = some ko → ∀ c ∈ capsOf ko, ¬ IsVirtCap c

/-- The inputs on which the extended decoder leaves the ported one
(module docstring, 1). -/
def VirtRoute (firstPhase : Bool) (label : Data) (args : List Data) (cap : Cap)
    (excaps : List (Cap × CslotPtr)) : Prop :=
  match cap with
  | .archObjectCap (.vcpuCap _) => True
  | .archObjectCap (.eptCap _ _ _) => True
  | .archObjectCap (.pageCap _ _ _ mt _ m) =>
    dataToNat label = fl4PageMapEptLabel ∨
      (mt = .vmEptMap ∧ m.isSome ∧ invocationType label = .archInvocationLabel .x64PageMap) ∨
      (mt = .vmEptMap ∧ m.isSome ∧ invocationType label = .archInvocationLabel .x64PageUnmap)
  | .archObjectCap (.asidPoolCap _ _) =>
    invocationType label = .archInvocationLabel .x64ASIDPoolAssign ∧ startsWithEptRoot excaps = true
  | .threadCap _ => ¬ firstPhase ∧ dataToNat label = fl4SetEptRootLabel
  | .untypedCap _ _ _ _ => untypedVtxGate label args (excaps.map Prod.fst)
  | _ => False

/-- On a virtualization cap's own routes the cap is a virtualization cap
or the label is one of FL4's (60, 88) or the VT-x retype gate. -/
theorem VirtRoute.cases {firstPhase : Bool} {label : Data} {args : List Data} {cap : Cap}
    {excaps : List (Cap × CslotPtr)} (h : VirtRoute firstPhase label args cap excaps) :
    IsVirtCap cap ∨ (∃ x ∈ excaps.head?, IsVirtCap x.1) ∨ dataToNat label = fl4PageMapEptLabel ∨
      dataToNat label = fl4SetEptRootLabel ∨ untypedVtxGate label args (excaps.map Prod.fst) := by
  unfold VirtRoute at h
  split at h
  · exact Or.inl trivial
  · exact Or.inl trivial
  · rename_i mt _
    rcases h with h | ⟨hm, _⟩ | ⟨hm, _⟩
    · exact Or.inr (Or.inr (Or.inl h))
    · subst hm; exact Or.inl trivial
    · subst hm; exact Or.inl trivial
  · obtain ⟨_, he⟩ := h
    refine Or.inr (Or.inl ?_)
    match excaps, he with
    | (.archObjectCap (.eptCap _ 0 none), s) :: _, _ => exact ⟨_, rfl, trivial⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inl h.2)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · exact h.elim

section
variable {Z : Type} [StateExt Z]

/-- **P3x, decode** (module docstring, 1). -/
theorem fl4DecodeInvocationV_base (firstPhase : Bool) (label : Data) (args : List Data)
    (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr))
    (buffer : Option ObjRef) (h : ¬ VirtRoute firstPhase label args cap excaps) :
    fl4DecodeInvocationV (Z := Z) firstPhase label args capIndex slot cap excaps buffer =
      NonDetE.liftME Fl4InvocationV.base
        (fl4DecodeInvocation firstPhase label args capIndex slot cap excaps buffer) := by
  unfold fl4DecodeInvocationV
  cases cap with
  | archObjectCap a =>
    cases a with
    | vcpuCap _ => exact absurd trivial h
    | eptCap _ _ _ => exact absurd trivial h
    | pageCap dev p R mt sz m =>
      simp only [VirtRoute, not_or] at h
      obtain ⟨h1, h2, h3⟩ := h
      dsimp only
      rw [if_neg h1, if_neg h2, if_neg h3]
    | asidPoolCap p b =>
      simp only [VirtRoute] at h
      dsimp only
      rw [if_neg h]
    | _ => rfl
  | threadCap t =>
    simp only [VirtRoute] at h
    dsimp only
    rw [if_neg h]
  | untypedCap _ _ _ _ =>
    simp only [VirtRoute] at h
    dsimp only
    rw [if_neg h]
  | _ => rfl

/-- The ported invocations the extended kernel performs with substituted
operations (module docstring, 2). -/
def PerformSubst : Fl4Invocation → Prop
  | .invokeUntyped _ => True
  | .invokeNotification _ _ => True
  | .invokeTCB _ => True
  | .invokeCNode _ => True
  | _ => False

/-- **P3x, perform** (module docstring, 2). -/
theorem fl4PerformInvocationV_base (onCore : ObjRef → Bool) (block call canDonate : Bool)
    (i : Fl4Invocation) (h : ¬ PerformSubst i) :
    fl4PerformInvocationV (Z := Z) onCore block call canDonate (.base i) =
      fl4PerformInvocation block call canDonate i := by
  cases i with
  | invokeUntyped _ => exact absurd trivial h
  | invokeNotification _ _ => exact absurd trivial h
  | invokeTCB _ => exact absurd trivial h
  | invokeCNode _ => exact absurd trivial h
  | _ => rfl

/-- The caps `finaliseCapV` hooks. -/
def FinaliseHooked : Cap → Prop
  | .archObjectCap (.vcpuCap _) => True
  | .archObjectCap (.eptCap _ _ (some _)) => True
  | .archObjectCap (.pageCap _ _ _ .vmEptMap _ (some _)) => True
  | .archObjectCap (.ioPortCap _ _) => True
  | .threadCap _ => True
  | _ => False

/-- **P3x, finalisation of an unhooked cap**: the ported `finalise_cap`. -/
theorem finaliseCapV_eq (cap : Cap) (final : Bool) (h : ¬ FinaliseHooked cap) :
    finaliseCapV (Z := Z) cap final = finaliseCap cap final := by
  unfold finaliseCapV
  cases cap with
  | archObjectCap a =>
    cases a with
    | vcpuCap _ => exact absurd trivial h
    | eptCap _ _ m =>
      cases m with
      | none => rfl
      | some _ => exact absurd trivial h
    | pageCap _ _ _ mt _ m =>
      cases mt with
      | vmEptMap =>
        cases m with
        | none => rfl
        | some _ => exact absurd trivial h
      | _ => rfl
    | ioPortCap _ _ => exact absurd trivial h
    | _ => rfl
  | threadCap _ => exact absurd trivial h
  | _ => rfl

/-! ### Execution lemmas of the `NonDet` monad used below -/

/-- A bind whose first computation has the one outcome `(a, s)`. -/
theorem nd_bind_det {σ α β : Type} (m : NonDet σ α) (f : α → NonDet σ β) (s : σ) (a : α)
    (h : m s = ({(a, s)}, False)) : (m >>= f) s = f a s := by
  show NonDet.bind m f s = _
  unfold NonDet.bind
  rw [h]
  apply Prod.ext
  · ext r; simp
  · simp

/-- `vcpuDetach` does nothing without virtualization objects. -/
theorem vcpuDetach_noVirt {σ : State Z} (hn : NoVirtObjects σ) (t : ObjRef) :
    vcpuDetach (Z := Z) t σ = ({((), σ)}, False) := by
  unfold vcpuDetach
  rw [nd_bind_det _ _ σ none (by simp only [getTcbVcpu, NonDet.gets, hn.tcbVcpuOf])]
  rfl

/-- A thread cap's finalisation hook does nothing without virtualization
objects. -/
theorem finaliseCapV_thread_noVirt {σ : State Z} (hn : NoVirtObjects σ) (t : ObjRef) (final : Bool) :
    finaliseCapV (Z := Z) (.threadCap t) final σ = finaliseCap (.threadCap t) final σ := by
  show (NonDet.when final (vcpuDetach t) >>= fun _ => finaliseCap (.threadCap t) final) σ = _
  refine nd_bind_det _ _ σ () ?_
  cases final with
  | false => rfl
  | true => exact vcpuDetach_noVirt hn t

/-- `vmCheck` of a thread that is not `runningVM` does nothing. -/
theorem vmCheck_not_runningVM {σ : State Z} {t : ObjRef} {tcb : Tcb}
    (hk : σ.kheap t = some (.tcb tcb)) (hs : tcb.tcbState ≠ .runningVM) :
    vmCheck (Z := Z) t σ = ({((), σ)}, False) := by
  have hg : getThreadState (Z := Z) t σ = ({(tcb.tcbState, σ)}, False) := by
    unfold getThreadState threadGet
    rw [nd_bind_det _ _ σ tcb (by
      simp [NonDet.getsThe, getTcb, readObject, hk, NonDet.assertOpt, NonDet.pure])]
    rfl
  unfold vmCheck
  rw [nd_bind_det _ _ σ tcb.tcbState hg]
  unfold NonDet.when
  rw [if_neg hs]
  rfl

/-- With the owner adapter, revoking an I/O-port grant does nothing
(decision Q2; this lemma goes when the owner field arrives). -/
theorem ioPortRevoke_eq (c : ArchCap) : ioPortRevoke (Z := Z) c = NonDet.pure () := by
  unfold ioPortRevoke ioPortOwner
  rfl

end

end

end Fl4Spec
