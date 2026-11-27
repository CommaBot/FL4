/-
P3x for virtualization, spec side (line virt, gen 6; proofs/VIRT-PLAN.md §10, table row "NoVirt reachability"):
**the object-type half `NVV` (no VCPU object, VirtR7b) across the performs** — the members of the `TYK` family
(VirtTyK1..6) that create objects, and the perform dispatcher.

* `aType_default_nvt`: a default object of a non-VCPU, non-untyped type is not a VCPU.
* **`ty_retypeRegionWith`** / `ty_retypeRegion` (side condition: the type is not VCPU), registered as `ty_leaf`
  with the side condition closed by assumption or by computation.
* `ty_invokeUntypedWith`, `ty_invokeUntyped`, `ty_fl4InvokeUntyped` (retype type not VCPU),
  `ty_performAsidControlInvocation` (ASID pool), `ty_archPerformInvocation`, `ty_unmapPageUnflushed`,
  `ty_performFrameBatch` (SpecFbX's `ik_performFrameBatchW`), `ty_performTdxInvocation`,
  `ty_fl4ArchPerformInvocation`, `ty_invokeFl4Tcb`.
* **`ty_fl4Perform`**: `fl4PerformInvocation` keeps `TIn NVT` for every `InvNV` invocation (VirtNvInv).
* `ty_handleEvent_other`, `ty_fl4HandleEvent_other`: the non-syscall events.

No premises beyond the stated side conditions; no [J]/[P]/[W]/[S]. New file only.
-/
import Fl4Proofs.P3.VirtNvInv
import Fl4Proofs.P3.SpecFbX
open Classical

namespace Fl4Proofs.P3.VirtTyK7
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvTY Fl4Proofs.P3.VirtR7b
  Fl4Proofs.P3.VirtNvInv Fl4Proofs.P3.VirtInvOK

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

/-- A default object of a non-VCPU, non-untyped type is not a VCPU. -/
theorem aType_default_nvt {ty : ApiObjectType} (h : ty ≠ .archObject .vcpuObj) (hu : ty ≠ .untyped)
    (dev : Bool) (n : Nat) (d : Domain) : aType (defaultObject ty dev n d) ≠ .aArch .aVcpu := by
  cases ty with
  | untyped => exact absurd rfl hu
  | archObject a => cases a <;> cases dev <;> simp_all [defaultObject, defaultArchObject, aType, aaType]
  | capTableObject => simp only [defaultObject, aType]; split <;> simp
  | schedContextObject => simp only [defaultObject, aType]; split <;> simp
  | _ => simp [defaultObject, aType]

/-- A non-VT-x type is not the VCPU type. -/
theorem ne_vcpu_of_nvtx {t : ApiObjectType} (h : ¬ VtxTy t) : t ≠ .archObject .vcpuObj :=
  fun e => h (e ▸ vtxTy_vcpu)

/-- **`retype_region` keeps `TIn NVT`** for a non-VCPU type. -/
theorem ty_retypeRegionWith (bA : ApiObjectType → Nat → Nat) (ptr : ObjRef) (n oB : Nat) (ty : ApiObjectType)
    (dev : Bool) (h : ty ≠ .archObject .vcpuObj) : TYK NVT (retypeRegionWith (Z := Unit) bA ptr n oB ty dev) := by
  intro σ hσ y hy
  rcases (SInvU.retypeRegionWith_out hy).2 with e | ⟨hu, e⟩
  · rw [e]; exact hσ
  · rw [e]
    intro o ko ho
    simp only [SInvU.retKh] at ho
    split_ifs at ho
    · cases ho; exact aType_default_nvt h hu _ _ _
    · exact hσ _ _ ho

theorem ty_retypeRegion (ptr : ObjRef) (n oB : Nat) (ty : ApiObjectType) (dev : Bool)
    (h : ty ≠ .archObject .vcpuObj) : TYK NVT (retypeRegion (Z := Unit) ptr n oB ty dev) := by
  rw [← retypeRegionWith_objBitsApi]; exact ty_retypeRegionWith _ _ _ _ _ _ h

/-- The side condition of the retype leaves. -/
macro "nvt_side" : tactic => `(tactic| first | assumption | (intro h; cases h) | (simp; done))

macro_rules | `(tactic| ty_leaf) => `(tactic| ((with_reducible refine ty_retypeRegionWith _ _ _ _ _ _ ?_); nvt_side))
macro_rules | `(tactic| ty_leaf) => `(tactic| ((with_reducible refine ty_retypeRegion _ _ _ _ _ ?_); nvt_side))

/-! ## Untyped -/

theorem ty_invokeUntypedWith (bA : ApiObjectType → Nat → Nat) (ui : UntypedInvocation)
    (h : utType ui ≠ .archObject .vcpuObj) : TYKE NVT (invokeUntypedWith (Z := Unit) bA ui) := by
  obtain ⟨src, reset, base, rb, t, sz, slots, dev⟩ := ui
  simp only [utType] at h
  unfold invokeUntypedWith; ty_auto

theorem ty_invokeUntyped (ui : UntypedInvocation) (h : utType ui ≠ .archObject .vcpuObj) :
    TYKE NVT (invokeUntyped (Z := Unit) ui) := by
  rw [← invokeUntypedWith_objBitsApi]; exact ty_invokeUntypedWith _ _ h

theorem ty_fl4InvokeUntyped (ui : UntypedInvocation) (h : ¬ VtxTy (utType ui)) :
    TYKE NVT (fl4InvokeUntyped (Z := Unit) ui) :=
  ty_invokeUntypedWith _ _ (ne_vcpu_of_nvtx h)

/-! ## Arch performs -/

theorem ty_performAsidControlInvocation (iv : AsidControlInvocation) :
    TYK NVT (performAsidControlInvocation (Z := Unit) iv) := by
  cases iv; simp only [performAsidControlInvocation]; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_performAsidControlInvocation _)

theorem ty_archPerformInvocation (i : ArchInvocation) : TYKE NVT (archPerformInvocation (Z := Unit) i) := by
  unfold archPerformInvocation; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_archPerformInvocation _)

theorem ty_unmapPageUnflushed (sz : VMPageSize) (vs : ObjRef) (va : VSpaceRef) (p : ObjRef) :
    TYK NVT (unmapPageUnflushed (Z := Unit) sz vs va p) := by
  unfold unmapPageUnflushed; ty_auto

theorem ty_performFrameBatch (b : Fl4FrameBatchInvocation) : TYK NVT (performFrameBatch (Z := Unit) b) :=
  ik_performFrameBatchW b (fun _ _ _ _ => ty_capInsert _ _ _) (fun _ => ty_performPageInvocation _)
    (fun _ _ _ _ _ _ _ => ty_archFinaliseCap _ _) (fun _ => ty_emptySlot _ _)
    (fun _ _ _ _ => ty_unmapPageUnflushed _ _ _ _) (fun _ _ _ => ty_setCap _ _) (ty_flushAll _ _)
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_performFrameBatch _)

theorem ty_performTdxInvocation (i : Fl4TdxInvocation) : TYK NVT (performTdxInvocation (Z := Unit) i) := by
  cases i <;> simp only [performTdxInvocation, tdxStatus] <;> ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_performTdxInvocation _)

theorem ty_fl4ArchPerformInvocation (a : Fl4ArchInvocation) :
    TYKE NVT (fl4ArchPerformInvocation (Z := Unit) a) := by
  cases a <;> simp only [fl4ArchPerformInvocation] <;> ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_fl4ArchPerformInvocation _)

theorem ty_invokeFl4Tcb (i : Fl4TcbInvocation) : TYKE NVT (invokeFl4Tcb (Z := Unit) i) := by
  unfold invokeFl4Tcb; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_invokeFl4Tcb _)

/-! ## The perform dispatcher -/

/-- **`fl4PerformInvocation` keeps `TIn NVT`** for an `InvNV` invocation. -/
theorem ty_fl4Perform (blk call don : Bool) (inv : Fl4Invocation) (hi : InvNV inv) :
    TYKE NVT (fl4PerformInvocation (Z := Unit) blk call don inv) := by
  cases inv with
  | invokeUntyped ui =>
    simp only [fl4PerformInvocation]
    exact ike_bind (ty_fl4InvokeUntyped ui hi) fun _ => ike_returnOk _
  | _ => simp only [fl4PerformInvocation]; ty_auto

/-! ## The non-syscall events -/

set_option maxHeartbeats 4000000 in
theorem ty_handleEvent_other (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) :
    TYKE NVT (handleEvent (Z := Unit) ev) := by
  cases ev with
  | syscallEvent c => exact absurd rfl (h c)
  | _ => simp only [handleEvent]; ty_auto

theorem ty_fl4HandleEvent_other (rep : Bool) (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) :
    TYKE NVT (fl4HandleEvent (Z := Unit) rep ev) := by
  rw [fl4HandleEvent_other rep ev h]; exact ty_handleEvent_other ev h

end

end Fl4Proofs.P3.VirtTyK7
