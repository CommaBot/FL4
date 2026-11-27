/-
P3x for virtualization (line virt, gen 17, item 4): **`finaliseCapVF = finaliseCapV` on `NoRunVM` states, arm by
arm** (gen 15's open item; P3/VirtNoRunF's module docstring: the single Cap/ArchCap case split closing the unhooked
arms by unfolding both matchers hit a kernel deterministic timeout at 12 GB).

Here every arm is its own small theorem, and the top only dispatches to them (its proof term is a case tree of
lemma applications, no matcher is unfolded there):
* unhooked arms (`finF_null`, `finF_untyped`, …, `finF_tdx`; `finF_ept_none` / `finF_ept_some`, `finF_page_*`):
  `finaliseCapVF c f = finaliseCapV c f` for every state (both reduce to the same term);
* hooked arms (`finF_thread`, `finF_vcpu`): equal at a `NoRunVM` state, by `vcpuDetachF_eq_nr` under the bind
  (and, for the VCPU, at the state after `getVcpu`, which is the same state).
* **`finaliseCapVF_eq_nr`**: `NoRunVM σ ⇒ finaliseCapVF c f σ = finaliseCapV c f σ` for every cap.

Lean lesson (where gen 15's blowup came from): in the hooked arms a plain `rfl` on the `final = false` branch (or an
`exact` through `NonDet.when true`) makes the unifier compare `vcpuDetachF t` with `vcpuDetach t` argument-wise
before reducing the `if`, unfolding both detaches deeply (6–12 GB). Rewriting the `if`s first (`if_neg`/`if_pos`)
keeps every arm at a few seconds; the unhooked arms are cheap `rfl`s.

No named premise; no [J]/[P]/[W]. New file only; no existing statement changed.
-/
import Fl4Proofs.P3.VirtNoRunF
open Classical

namespace Fl4Proofs.P3.VirtFinNR
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.VirtR7d Fl4Proofs.P3.VirtReportEq Fl4Proofs.P3.VirtNoRunF

noncomputable section

/-! ## Unhooked arms -/

theorem finF_null (f : Bool) : finaliseCapVF (Z := Unit) .nullCap f = finaliseCapV .nullCap f := rfl
theorem finF_untyped (d : Bool) (r : ObjRef) (b i : Nat) (f : Bool) :
    finaliseCapVF (Z := Unit) (.untypedCap d r b i) f = finaliseCapV (.untypedCap d r b i) f := rfl
theorem finF_endpoint (r : ObjRef) (b : Badge) (ri : CapRights) (f : Bool) :
    finaliseCapVF (Z := Unit) (.endpointCap r b ri) f = finaliseCapV (.endpointCap r b ri) f := rfl
theorem finF_notification (r : ObjRef) (b : Badge) (ri : CapRights) (f : Bool) :
    finaliseCapVF (Z := Unit) (.notificationCap r b ri) f = finaliseCapV (.notificationCap r b ri) f := rfl
theorem finF_reply (r : ObjRef) (ri : CapRights) (f : Bool) :
    finaliseCapVF (Z := Unit) (.replyCap r ri) f = finaliseCapV (.replyCap r ri) f := rfl
theorem finF_cnode (r : ObjRef) (b : Nat) (g : List Bool) (f : Bool) :
    finaliseCapVF (Z := Unit) (.cnodeCap r b g) f = finaliseCapV (.cnodeCap r b g) f := rfl
theorem finF_domain (f : Bool) : finaliseCapVF (Z := Unit) .domainCap f = finaliseCapV .domainCap f := rfl
theorem finF_sc (r : ObjRef) (b : Nat) (f : Bool) :
    finaliseCapVF (Z := Unit) (.schedContextCap r b) f = finaliseCapV (.schedContextCap r b) f := rfl
theorem finF_schedControl (f : Bool) :
    finaliseCapVF (Z := Unit) .schedControlCap f = finaliseCapV .schedControlCap f := rfl
theorem finF_irqControl (f : Bool) :
    finaliseCapVF (Z := Unit) .irqControlCap f = finaliseCapV .irqControlCap f := rfl
theorem finF_irqHandler (q : Irq) (f : Bool) :
    finaliseCapVF (Z := Unit) (.irqHandlerCap q) f = finaliseCapV (.irqHandlerCap q) f := rfl
theorem finF_zombie (r : ObjRef) (b : Option Nat) (n : Nat) (f : Bool) :
    finaliseCapVF (Z := Unit) (.zombie r b n) f = finaliseCapV (.zombie r b n) f := rfl

theorem finF_ept_none (r : ObjRef) (l : Nat) (f : Bool) :
    finaliseCapVF (Z := Unit) (.archObjectCap (.eptCap r l none)) f =
      finaliseCapV (.archObjectCap (.eptCap r l none)) f := rfl
theorem finF_ept_some (r : ObjRef) (l : Nat) (a : Asid) (g : VSpaceRef) (f : Bool) :
    finaliseCapVF (Z := Unit) (.archObjectCap (.eptCap r l (some (a, g)))) f =
      finaliseCapV (.archObjectCap (.eptCap r l (some (a, g)))) f := rfl
theorem finF_asidPool (p : ObjRef) (b : Asid) (f : Bool) :
    finaliseCapVF (Z := Unit) (.archObjectCap (.asidPoolCap p b)) f =
      finaliseCapV (.archObjectCap (.asidPoolCap p b)) f := rfl
theorem finF_asidControl (f : Bool) :
    finaliseCapVF (Z := Unit) (.archObjectCap .asidControlCap) f = finaliseCapV (.archObjectCap .asidControlCap) f :=
  rfl
theorem finF_ioPort (a b : IoPort) (f : Bool) :
    finaliseCapVF (Z := Unit) (.archObjectCap (.ioPortCap a b)) f =
      finaliseCapV (.archObjectCap (.ioPortCap a b)) f := rfl
theorem finF_ioPortControl (f : Bool) :
    finaliseCapVF (Z := Unit) (.archObjectCap .ioPortControlCap) f =
      finaliseCapV (.archObjectCap .ioPortControlCap) f := rfl
theorem finF_page_none (d : Bool) (r : ObjRef) (ri : CapRights) (mt : VMMapType) (sz : VMPageSize) (f : Bool) :
    finaliseCapVF (Z := Unit) (.archObjectCap (.pageCap d r ri mt sz none)) f =
      finaliseCapV (.archObjectCap (.pageCap d r ri mt sz none)) f := by
  cases mt <;> rfl
theorem finF_page_some (d : Bool) (r : ObjRef) (ri : CapRights) (mt : VMMapType) (sz : VMPageSize) (a : Asid)
    (g : VSpaceRef) (f : Bool) :
    finaliseCapVF (Z := Unit) (.archObjectCap (.pageCap d r ri mt sz (some (a, g)))) f =
      finaliseCapV (.archObjectCap (.pageCap d r ri mt sz (some (a, g)))) f := by
  cases mt <;> rfl
theorem finF_pt (r : ObjRef) (m : Option (Asid × VSpaceRef)) (f : Bool) :
    finaliseCapVF (Z := Unit) (.archObjectCap (.pageTableCap r m)) f =
      finaliseCapV (.archObjectCap (.pageTableCap r m)) f := rfl
theorem finF_pd (r : ObjRef) (m : Option (Asid × VSpaceRef)) (f : Bool) :
    finaliseCapVF (Z := Unit) (.archObjectCap (.pageDirectoryCap r m)) f =
      finaliseCapV (.archObjectCap (.pageDirectoryCap r m)) f := rfl
theorem finF_pdpt (r : ObjRef) (m : Option (Asid × VSpaceRef)) (f : Bool) :
    finaliseCapVF (Z := Unit) (.archObjectCap (.pdPointerTableCap r m)) f =
      finaliseCapV (.archObjectCap (.pdPointerTableCap r m)) f := rfl
theorem finF_pml4 (r : ObjRef) (m : Option Asid) (f : Bool) :
    finaliseCapVF (Z := Unit) (.archObjectCap (.pml4Cap r m)) f =
      finaliseCapV (.archObjectCap (.pml4Cap r m)) f := rfl
theorem finF_tdx (f : Bool) :
    finaliseCapVF (Z := Unit) (.archObjectCap .tdxControlCap) f = finaliseCapV (.archObjectCap .tdxControlCap) f :=
  rfl

/-! ## Hooked arms -/

/-- **The thread arm** on a `NoRunVM` state. -/
theorem finF_thread {σ : State Unit} (hn : NoRunVM σ) (t : ObjRef) (f : Bool) :
    finaliseCapVF (Z := Unit) (.threadCap t) f σ = finaliseCapV (.threadCap t) f σ := by
  unfold finaliseCapVF finaliseCapV
  dsimp only
  unfold NonDet.when
  cases f
  · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
  · rw [if_pos rfl, if_pos rfl]
    exact nd_bind_eq_of (vcpuDetachF_eq_nr hn t) _

/-- **The VCPU arm** on a `NoRunVM` state. -/
theorem finF_vcpu {σ : State Unit} (hn : NoRunVM σ) (v : ObjRef) (f : Bool) :
    finaliseCapVF (Z := Unit) (.archObjectCap (.vcpuCap v)) f σ = finaliseCapV (.archObjectCap (.vcpuCap v)) f σ := by
  unfold finaliseCapVF finaliseCapV
  dsimp only
  cases f
  · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
  · rw [if_pos rfl, if_pos rfl]
    refine nd_bind_congr_on _ _ _ σ fun z hz => ?_
    obtain ⟨e, -⟩ := getVcpu_state hz
    have hn2 : NoRunVM z.2 := e ▸ hn
    try dsimp only
    cases z.1.tcb with
    | none => first | (dsimp only; done) | rfl
    | some t =>
      try dsimp only
      exact nd_bind_eq_of (vcpuDetachF_eq_nr hn2 t) _

/-! ## The top -/

/-- **`finaliseCapVF` is `finaliseCapV` on `NoRunVM` states** (every cap; arm by arm). -/
theorem finaliseCapVF_eq_nr {σ : State Unit} (hn : NoRunVM σ) (c : Cap) (f : Bool) :
    finaliseCapVF (Z := Unit) c f σ = finaliseCapV c f σ := by
  cases c with
  | nullCap => rw [finF_null]
  | untypedCap d r b i => rw [finF_untyped]
  | endpointCap r b ri => rw [finF_endpoint]
  | notificationCap r b ri => rw [finF_notification]
  | replyCap r ri => rw [finF_reply]
  | cnodeCap r b g => rw [finF_cnode]
  | threadCap t => exact finF_thread hn t f
  | domainCap => rw [finF_domain]
  | schedContextCap r b => rw [finF_sc]
  | schedControlCap => rw [finF_schedControl]
  | irqControlCap => rw [finF_irqControl]
  | irqHandlerCap q => rw [finF_irqHandler]
  | zombie r b n => rw [finF_zombie]
  | archObjectCap a =>
    cases a with
    | vcpuCap v => exact finF_vcpu hn v f
    | eptCap r l m =>
      rcases m with _ | ⟨a, g⟩
      · rw [finF_ept_none]
      · rw [finF_ept_some]
    | asidPoolCap p b => rw [finF_asidPool]
    | asidControlCap => rw [finF_asidControl]
    | ioPortCap a b => rw [finF_ioPort]
    | ioPortControlCap => rw [finF_ioPortControl]
    | pageCap d r ri mt sz m =>
      rcases m with _ | ⟨a, g⟩
      · rw [finF_page_none]
      · rw [finF_page_some]
    | pageTableCap r m => rw [finF_pt]
    | pageDirectoryCap r m => rw [finF_pd]
    | pdPointerTableCap r m => rw [finF_pdpt]
    | pml4Cap r m => rw [finF_pml4]
    | tdxControlCap => rw [finF_tdx]

end
end Fl4Proofs.P3.VirtFinNR
