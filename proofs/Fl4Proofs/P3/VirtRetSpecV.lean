/-
P3x for virtualization (line virt, gen 25, item 1, spec half): **the spec's VCPU retype keeps every VCPU off its new
objects** — every outcome of `fl4InvokeUntypedV (.retype … false … (.archObject .vcpuObj) …)` (Ext/VirtFinalise
l. 265) keeps `vcpuAt` at every reference that is not one of the new objects, and `setThreadState` keeps every
`vcpuAt`. With FL4's frame (P3/VirtRetFrameV) this keeps `VRelAt` for the VCPUs present before the retype.

* `vcOff l σ` (the spec's VCPUs off the list `l`); `FK vcF → FK (vcOff l)` (`fk_vcOff`).
* Pieces: `vc_getCap` (a read), `vo_regionHeap` (`retype_region`'s heap rewrites only `l`, UntypedLoop's
  `regionHeap` / `foldr_update_apply`), `vc_initArch` (nothing for a VCPU: `init_arch_objects` acts on PML4s only,
  Retype.lean l. 33), `vc_createCap` (`set_cdt`, the extended op, `set_original`, `set_cap`: kernel objects only
  through `set_cap`, VirtResetSpecV's `vc_setCap`), `vo_setObject` / `vo_mapMx_setVcpu` (the hook writes only
  references of `l`).
* **`vo_invokeV`**: `FKE (vcOff (regionPtrs rb n 32768))` of the whole VCPU invocation without reset, `n` the
  window length (the hook's addresses are `retypeAddrs … = regionPtrs rb n 32768`, VirtRetVcpuPre's
  `retypeAddrs_vcpu`).
* **`vc_setThreadState`**: `FK vcF (setThreadState t ts)` (a TCB `set_object`, then scheduler fields).
* **`vcpuAt_invokeV`**: every outcome, a reference not among the new objects: `vcpuAt` kept.

No [J]/[P]/[W] premise. New file only; no existing statement changed.
-/
import Fl4Proofs.P3.VirtResetSpecV
import Fl4Proofs.P3.VirtRetVcpuPre
open Classical

namespace Fl4Proofs.P3.VirtRetSpecV
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.Vs Fl4Proofs.P3.VirtInitWalk Fl4Proofs.P3.VirtResetSpecV Fl4Proofs.P3.VirtRetVcpuPre

noncomputable section

/-- The spec's VCPUs at every reference off `l`. -/
def vcOff (l : List ObjRef) (σ : State Unit) : ObjRef → Option VcpuState :=
  fun o => if o ∈ l then none else vcpuAt σ o

theorem fk_vcOff {α : Type} {m : NonDet (State Unit) α} (h : FK vcF m) (l : List ObjRef) : FK (vcOff l) m := by
  intro σ x hx
  have e := h σ x hx
  funext o
  unfold vcOff
  rw [show vcpuAt x.2 o = vcpuAt σ o from congrFun e o]

theorem vc_getCap (sl : CslotPtr) : FK vcF (getCap (Z := Unit) sl) := by
  obtain ⟨o, c⟩ := sl
  unfold getCap
  refine dk_bind (dk_getObject o) (fun obj => ?_)
  cases obj <;> simp only [] <;> dk_auto0

theorem vo_regionHeap (l : List ObjRef) (σ : State Unit) (ko : KernelObject) :
    vcOff l (regionHeap σ l ko) = vcOff l σ := by
  funext o
  unfold vcOff
  by_cases h : o ∈ l
  · simp only [if_pos h]
  · simp only [if_neg h]
    unfold vcpuAt regionHeap
    simp only [foldr_update_apply, if_neg h]

theorem vc_createCap (t : ApiObjectType) (b : Nat) (u : CslotPtr) (d : Bool) (x : CslotPtr × ObjRef) :
    FK vcF (createCap (Z := Unit) t b u d x) := by
  obtain ⟨dest, oref⟩ := x
  unfold createCap setCdt setOriginal
  exact dk_bind (dk_gets _) fun _ => dk_bind (dk_gets _) fun _ =>
    dk_bind (dk_get_put fun _ => rfl) fun _ =>
    dk_bind (vc_deo _) fun _ =>
    dk_bind (dk_bind (dk_gets _) fun _ => dk_modify fun _ => rfl) fun _ => vc_setCap _ _

/-- `set_object` at a reference of `l` keeps `vcOff l`. -/
theorem vo_setObject {l : List ObjRef} {p : ObjRef} (hp : p ∈ l) (o : KernelObject) :
    FK (vcOff l) (setObject (Z := Unit) p o) := by
  intro σ x ⟨y, hy, hx⟩
  obtain ⟨k, -, hyk⟩ : ∃ k, σ.kheap p = some k ∧ y = (k, σ) := by
    unfold getObject NonDet.getsThe readObject at hy
    cases h : σ.kheap p with
    | none => rw [h] at hy; exact hy.elim
    | some k => rw [h] at hy; exact ⟨k, rfl, Set.mem_singleton_iff.1 hy⟩
  subst hyk
  obtain ⟨z, hz, hx⟩ := hx
  obtain ⟨-, rfl⟩ := hz
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  funext o'
  unfold vcOff
  by_cases h : o' ∈ l
  · simp only [if_pos h]
  · have e : o' ≠ p := fun e => h (e ▸ hp)
    simp only [if_neg h]
    unfold vcpuAt
    simp only [Function.update_of_ne e]

theorem vo_mapMx_setVcpu {l : List ObjRef} (vs : VcpuState) :
    ∀ l' : List ObjRef, (∀ v ∈ l', v ∈ l) → FK (vcOff l) (NonDet.mapMx (fun v => setVcpu (Z := Unit) v vs) l')
  | [], _ => dk_pure' _
  | v :: l', h => dk_bind' (vo_setObject (h v List.mem_cons_self) _)
      fun _ => vo_mapMx_setVcpu vs l' fun w hw => h w (List.mem_cons_of_mem _ hw)

theorem vc_initArch (dev : Bool) (ptr : ObjRef) (n sz : Nat) (refs : List ObjRef) :
    FK vcF (initArchObjects (Z := Unit) (.archObject .vcpuObj) dev ptr n sz refs) := by
  unfold initArchObjects NonDet.when
  rw [if_neg (by simp)]
  exact dk_pure' _

/-- **The VCPU invocation without reset keeps every VCPU off its new objects** (module docstring). -/
theorem vo_invokeV (src : CslotPtr) (base rb : ObjRef) (us : Nat) (slots : List CslotPtr) (dev : Bool) :
    FKE (vcOff (regionPtrs rb slots.length 32768))
      (fl4InvokeUntypedV (Z := Unit) (.retype src false base rb (.archObject .vcpuObj) us slots dev)) := by
  unfold fl4InvokeUntypedV fl4InvokeUntyped invokeUntypedWith
  dsimp only
  refine dke_bind (dke_bind ?_ fun _ => ?_) fun _ => ?_
  · unfold NonDetE.whenE; rw [if_neg (by simp)]; exact dke_pure _
  · refine dke_liftE (dk_bind (fk_vcOff (vc_getCap _) _) fun _ => dk_bind (dk_pure _) fun _ =>
      dk_bind (dk_pure _) fun _ => dk_bind (fk_vcOff (vc_setCap _ _) _) fun _ => ?_)
    refine dk_bind ?_ fun _ => dk_bind (fk_vcOff (vc_initArch _ _ _ _ _) _) fun _ =>
      fk_vcOff (dk_mapMx (fun x => vc_createCap _ _ _ _ x) _) _
    intro σ x hx
    rw [retypeRegionWith_eq, if_pos (by simp)] at hx
    rw [Set.mem_singleton_iff.1 hx]
    exact vo_regionHeap _ σ _
  · refine dke_liftE ?_
    unfold NonDet.when
    rw [if_pos rfl, retypeAddrs_vcpu]
    exact vo_mapMx_setVcpu _ _ fun _ h => h

theorem vc_threadSet (f : Tcb → Tcb) (t : ObjRef) : FK vcF (threadSet (Z := Unit) f t) := by
  unfold threadSet
  exact dk_bind (dk_getsThe _) fun _ => vc_setObject _ _ (fun _ h => by cases h) (aType_tcb_ne _)

/-- **`setThreadState` keeps every VCPU.** -/
theorem vc_setThreadState (t : ObjRef) (ts : ThreadState) : FK vcF (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  refine dk_bind (vc_threadSet _ _) fun _ => ?_
  unfold setThreadStateAct setSchedulerAction
  dk_auto0

/-- **Every outcome of the VCPU invocation keeps `vcpuAt` off the new objects.** -/
theorem vcpuAt_invokeV (src : CslotPtr) (base rb : ObjRef) (us : Nat) (slots : List CslotPtr) (dev : Bool)
    {σ : State Unit} {y}
    (hy : y ∈ ((fl4InvokeUntypedV (Z := Unit) (.retype src false base rb (.archObject .vcpuObj) us slots dev)).run
      σ).1) {o : ObjRef} (ho : o ∉ regionPtrs rb slots.length 32768) : vcpuAt y.2 o = vcpuAt σ o := by
  have e := congrFun (vo_invokeV src base rb us slots dev σ y hy) o
  unfold vcOff at e
  simpa only [if_neg ho] using e

end
end Fl4Proofs.P3.VirtRetSpecV
