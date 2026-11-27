/-
P3 (line p3J, gen 21): **the heap-type invariant `KhWF` across the syscall entry from a `CKI` state** (spec side
only; outside the `JAtZ` cone), so `KhWF` is kept by every kernel entry of a `RunCK` run.

* The only heap writers, `retype_region` and `delete_objects`, are reached only from the untyped invocation and the
  ASID-control invocation (an arch invocation). From a `CKI` state the decode's carry `InvK` (P3JCkS) excludes both
  (`False` at untyped / arch invocations), so every perform the decode can return keeps `ktV`
  (`kqe_fl4Perform_ck`).
* `KP v σ := CKI σ ∧ ktV σ = v`: kept by every piece that keeps `CKI` (P3JCkW/X/S, `hv_auto`) and `ktV` (P3JKtG/E,
  `kq_auto`) (`kp_of`); the invocation shell **`kp_handleInvocationR`** (P3JCkS's `ck_handleInvocationR` with `KP`),
  the syscalls, **`kp_fl4KernelEntrySyscall`**, **`kp_fl4CallKernel`** (every event).
* Tops: **`kentry_khWF`** (`fl4KernelEntrySyscall`), **`kcall_khWF`** (`fl4CallKernel`, every event), both from
  `CKI ∧ KhWF`.

Named premises: none. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JKtTop
open Classical

namespace Fl4Proofs.P3.SInvKt
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvV Fl4Proofs.P3.SInvDom Fl4Proofs.P3.SInvIo
open Fl4Proofs.P3.SInvCk Fl4Proofs.P3.Vs

noncomputable section

set_option maxRecDepth 20000

/-- `CKI` and the heap's types fixed at `v`. -/
def KP (v : ObjRef → Option AType) (σ : State Unit) : Prop := CKI σ ∧ ktV σ = v

theorem kp_of {α : Type} {m : NonDet (State Unit) α} (h1 : IKH CKI m) (h2 : KQ m) (v : ObjRef → Option AType) :
    SInv.IK (KP v) m :=
  fun σ hσ x hx => ⟨h1 σ hσ.1 x hx, (h2 σ x hx).trans hσ.2⟩

theorem kpe_of {ε α : Type} {m : NonDetE (State Unit) ε α} (h1 : IKHE CKI m) (h2 : KQE m)
    (v : ObjRef → Option AType) : SInv.IKE (KP v) m :=
  kp_of h1 h2 v

macro "kp_t" : tactic => `(tactic| first
  | (exact kpe_of (by hv_auto) (by kq_auto) _)
  | (exact kp_of (by hv_auto) (by kq_auto) _))

set_option maxHeartbeats 16000000 in
/-- **Every perform the decode returns from a `CKI` state keeps the heap's types** (module docstring). -/
theorem kqe_fl4Perform_ck (blk call don : Bool) (inv : Fl4Invocation) (hc : InvK inv) :
    KQE (fl4PerformInvocation (Z := Unit) blk call don inv) := by
  cases inv with
  | invokeUntyped _ => exact hc.elim
  | invokeSchedControl _ => exact hc.elim
  | invokeIRQControl _ => exact hc.elim
  | invokeArchObject _ => exact hc.elim
  | _ => simp only [fl4PerformInvocation]; kq_auto

set_option maxHeartbeats 16000000 in
/-- **The invocation shell keeps `KP v`** (P3JCkS's `ck_handleInvocationR` with `KP v`). -/
theorem kp_handleInvocationR (v0 : ObjRef → Option AType) (rep calling blocking don fp : Bool) (cptr : CapRef) :
    SInv.IKE (ε := Unit) (KP v0) (fl4HandleInvocationR (Z := Unit) rep calling blocking don fp cptr) := by
  unfold fl4HandleInvocationR
  refine ike_bind (by kp_t) fun thread => ike_bind (by kp_t) fun info => ?_
  intro σ hs y hy
  have h1 : ∀ w ∈ ((ExceptT.run (do
       let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot (Z := Unit) thread cptr
       let buffer ← NonDetE.liftE <| lookupIpcBuffer false thread
       let extracaps ← lookupExtraCaps thread buffer info
       NonDetE.returnOk (slot, cap, extracaps, buffer))) σ).1, KP v0 w.2 :=
    fun w hw => (by kp_t : SInv.IKE (ε := Fault) (KP v0) _) σ hs w hw
  refine syscall_post' (I := KP v0) (Q := KP v0) h1 ?_ ?_ ?_ ?_ y hy
  · intro f s hs v hv; exact (by kp_t : SInv.IK (KP v0) _) s hs v hv
  · intro a s has w hw
    obtain ⟨sl, cap, ex, buf⟩ := a
    exact (by kp_t : SInv.IKE (KP v0) _) s (h1 _ has) w hw
  · intro e s hs v hv; exact (by kp_t : SInv.IK (KP v0) _) s hs v hv
  · intro a s b s' has hbs hI y hy
    obtain ⟨sl, cap, ex, buf⟩ := a
    have hcap : capOpt (s.kheap sl.1) sl.2 = some cap := okCap_front thread cptr info σ _ s has
    have hCs : CKI s := (h1 _ has).1
    have hk : KW cap := kw_of_slot hCs hcap
    have eE : hV s' = hV s := (by hv_auto : IKHE (fun x => hV x = hV s) _) s rfl _ hbs
    have hd : InvK b :=
      okdAt_bind (fun _ s1 _ => okd_fl4Decode_ck _ _ _ _ _ _ _ _ s hCs hk s1) b s' hbs eE
    have hP : SInv.IKE (ε := Unit) (KP v0) (fl4PerformInvocation (Z := Unit) blocking calling don b) :=
      kpe_of (ck_fl4Perform blocking calling don b hd) (kqe_fl4Perform_ck blocking calling don b hd) v0
    obtain ⟨z, hz, ⟨u, hu, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE_inv' hy
    · have hz1 : KP v0 z.2 := (by kp_t : SInv.IKE (ε := Unit) (KP v0)
        (withoutPreemption (Z := Unit) (setThreadState thread .restart))) s' hI z hz
      obtain ⟨r, s1⟩ := z
      simp only at hu; subst hu
      obtain ⟨z2, hz2, ⟨rp, hr, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE_inv' hy
      · obtain ⟨r2, s2⟩ := z2
        simp only at hr; subst hr
        have hs2 := hP s1 hz1 _ hz2
        exact (by kp_t : SInv.IKE (KP v0) _) s2 hs2 y hy
      · exact hP s1 hz1 _ hz2
    · exact (by kp_t : SInv.IKE (ε := Unit) (KP v0)
        (withoutPreemption (Z := Unit) (setThreadState thread .restart))) s' hI z hz

macro "kp_auto" : tactic => `(tactic| repeat' (first
  | (exact kp_handleInvocationR _ _ _ _ _ _ _)
  | (refine ike_bind ?_ fun _ => ?_)
  | kp_t))

set_option maxHeartbeats 16000000 in
theorem kpe_fl4HandleSyscall (v0 : ObjRef → Option AType) (rep : Bool) (c : Syscall) :
    SInv.IKE (ε := Unit) (KP v0) (fl4HandleSyscall (Z := Unit) rep c) := by
  cases c <;> simp only [fl4HandleSyscall] <;> kp_auto

set_option maxHeartbeats 8000000 in
theorem kpe_fl4HandleEvent (v0 : ObjRef → Option AType) (rep : Bool) (ev : Event) :
    SInv.IKE (ε := Unit) (KP v0) (fl4HandleEvent (Z := Unit) rep ev) := by
  by_cases h : ∃ c, ev = .syscallEvent c
  · obtain ⟨c, rfl⟩ := h
    simp only [fl4HandleEvent]
    refine ike_bind (by kp_t) fun _ => ike_bind (by kp_t) fun _ => ike_whenE _ (kpe_fl4HandleSyscall v0 rep c)
  · rw [fl4HandleEvent_other rep ev fun c e => h ⟨c, e⟩]
    exact kpe_of (ck_handleEvent_other ev fun c e => h ⟨c, e⟩) (kqe_handleEvent_other ev fun c e => h ⟨c, e⟩) v0

set_option maxHeartbeats 8000000 in
/-- **`fl4CallKernel` keeps `KP v`, for every event.** -/
theorem kp_fl4CallKernel (v0 : ObjRef → Option AType) (rep : Bool) (ev : Event) :
    SInv.IK (KP v0) (fl4CallKernel (Z := Unit) rep ev) := by
  unfold fl4CallKernel
  refine ik_bind (ike_handleE (kpe_fl4HandleEvent v0 rep ev) fun _ => by kp_t) fun _ => ?_
  exact ik_bind (kp_of (by hv_auto) kq_fl4Awaken v0) fun _ => ik_bind (kp_of (by hv_auto) kq_schedule v0) fun _ =>
    kp_of (by hv_auto) kq_activateThread v0

theorem kp_fl4KernelEntrySyscall (v0 : ObjRef → Option AType) (rep : Bool) (c : Syscall) :
    SInv.IK (KP v0) (fl4KernelEntrySyscall (Z := Unit) rep c) := by
  unfold fl4KernelEntrySyscall
  exact ik_bind (ik_gets _) fun ct => ik_bind (kp_of (by hv_auto) (kq_fl4SyscallFaultIP ct) v0) fun _ =>
    kp_fl4CallKernel v0 rep _

/-- **`KhWF` across the syscall entry from a `CKI` state.** -/
theorem kentry_khWF (rep : Bool) (c : Syscall) {σ : State Unit} (hC : CKI σ) (h : KhWF σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) rep c) σ).1, KhWF y.2 :=
  fun y hy => khWF_of_ktV (kp_fl4KernelEntrySyscall (ktV σ) rep c σ ⟨hC, rfl⟩ y hy).2 h

/-- **`KhWF` across `fl4CallKernel` from a `CKI` state, every event.** -/
theorem kcall_khWF (rep : Bool) (ev : Event) {σ : State Unit} (hC : CKI σ) (h : KhWF σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, KhWF y.2 :=
  fun y hy => khWF_of_ktV (kp_fl4CallKernel (ktV σ) rep ev σ ⟨hC, rfl⟩ y hy).2 h

end

end Fl4Proofs.P3.SInvKt
