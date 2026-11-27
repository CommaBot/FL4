/-
P3 (line p3J, gen 25): **"every SC is round-robin" (`RR`) across every kernel entry from a `CKI` state** (spec side
only; outside the `JAtZ` cone).

* `RR σ := rpV σ = fun _ => 0` (P3JRrF's `rpV`: every SC of the heap has period `0`, seL4's `is_round_robin`);
  `rr_period`.
* Only `refill_new` / `refill_update` write an SC's period (`sc_period_update`), reached only from
  `SchedControl_Configure`; from a `CKI` state the decode's carry `InvK` (P3JCkS) excludes the SchedControl
  invocation (and, as for gen 21's `KhWF`, the untyped and arch invocations whose retype / detype P3JRrG leaves
  out), so every perform the decode can return keeps `rpV` (`rqe_fl4Perform_ck`).
* `RP v σ := CKI σ ∧ rpV σ = v`: the shell **`rp_handleInvocationR`** (P3JKtSys's `kp_handleInvocationR` with `RP`),
  the syscalls, **`rp_fl4KernelEntrySyscall`**, **`rp_fl4CallKernel`** (every event); `schedule` (`rq_schedule`).
* Tops: **`kentry_rr`**, **`kcall_rr`** (`RR` at every outcome from `CKI ∧ RR`), **`rr_fInit`** (the spec boot state:
  its one SC, the idle SC, has `default_sched_context`'s period `0`).

Named premises: none. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JRrE
import Fl4Proofs.P3.P3JKtSys
open Classical

namespace Fl4Proofs.P3.SInvRr
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvV Fl4Proofs.P3.SInvDom Fl4Proofs.P3.SInvIo
open Fl4Proofs.P3.SInvCk Fl4Proofs.P3.Vs

noncomputable section

theorem rq_nextDomain : RQ (nextDomain (Z := Unit)) := by
  unfold nextDomain
  exact dk_bind (dk_modify fun _ => rfl) fun _ => rq_doExtendedOp _

macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_nextDomain)

set_option maxHeartbeats 4000000 in
theorem rq_scheduleChooseNewThread : RQ (scheduleChooseNewThread (Z := Unit)) := by
  unfold scheduleChooseNewThread; zq_auto
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_scheduleChooseNewThread)

set_option maxHeartbeats 4000000 in
theorem rq_schedule : RQ (schedule (Z := Unit)) := by
  unfold schedule; zq_auto
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_schedule)

set_option maxHeartbeats 4000000 in
/-- **`fl4CallKernel` keeps the heap's types at every non-syscall event.** -/
theorem rq_fl4CallKernel_other (rep : Bool) (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) :
    RQ (fl4CallKernel (Z := Unit) rep ev) := by
  unfold fl4CallKernel
  rw [fl4HandleEvent_other rep ev h]
  refine dk_bind (dke_handleE (rqe_handleEvent_other ev h) fun _ => by zq_auto) fun _ => ?_
  exact dk_bind rq_fl4Awaken fun _ => dk_bind rq_schedule fun _ => rq_activateThread


set_option maxRecDepth 20000

/-- `CKI` and the heap's types fixed at `v`. -/
def RP (v : ObjRef → Ticks) (σ : State Unit) : Prop := CKI σ ∧ rpV σ = v

theorem rp_of {α : Type} {m : NonDet (State Unit) α} (h1 : IKH CKI m) (h2 : RQ m) (v : ObjRef → Ticks) :
    SInv.IK (RP v) m :=
  fun σ hσ x hx => ⟨h1 σ hσ.1 x hx, (h2 σ x hx).trans hσ.2⟩

theorem rpe_of {ε α : Type} {m : NonDetE (State Unit) ε α} (h1 : IKHE CKI m) (h2 : RQE m)
    (v : ObjRef → Ticks) : SInv.IKE (RP v) m :=
  rp_of h1 h2 v

macro "rp_t" : tactic => `(tactic| first
  | (exact rpe_of (by hv_auto) (by zq_auto) _)
  | (exact rp_of (by hv_auto) (by zq_auto) _))

set_option maxHeartbeats 16000000 in
/-- **Every perform the decode returns from a `CKI` state keeps the heap's types** (module docstring). -/
theorem rqe_fl4Perform_ck (blk call don : Bool) (inv : Fl4Invocation) (hc : InvK inv) :
    RQE (fl4PerformInvocation (Z := Unit) blk call don inv) := by
  cases inv with
  | invokeUntyped _ => exact hc.elim
  | invokeSchedControl _ => exact hc.elim
  | invokeIRQControl _ => exact hc.elim
  | invokeArchObject _ => exact hc.elim
  | _ => simp only [fl4PerformInvocation]; zq_auto

set_option maxHeartbeats 16000000 in
/-- **The invocation shell keeps `RP v`** (P3JCkS's `ck_handleInvocationR` with `RP v`). -/
theorem rp_handleInvocationR (v0 : ObjRef → Ticks) (rep calling blocking don fp : Bool) (cptr : CapRef) :
    SInv.IKE (ε := Unit) (RP v0) (fl4HandleInvocationR (Z := Unit) rep calling blocking don fp cptr) := by
  unfold fl4HandleInvocationR
  refine ike_bind (by rp_t) fun thread => ike_bind (by rp_t) fun info => ?_
  intro σ hs y hy
  have h1 : ∀ w ∈ ((ExceptT.run (do
       let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot (Z := Unit) thread cptr
       let buffer ← NonDetE.liftE <| lookupIpcBuffer false thread
       let extracaps ← lookupExtraCaps thread buffer info
       NonDetE.returnOk (slot, cap, extracaps, buffer))) σ).1, RP v0 w.2 :=
    fun w hw => (by rp_t : SInv.IKE (ε := Fault) (RP v0) _) σ hs w hw
  refine syscall_post' (I := RP v0) (Q := RP v0) h1 ?_ ?_ ?_ ?_ y hy
  · intro f s hs v hv; exact (by rp_t : SInv.IK (RP v0) _) s hs v hv
  · intro a s has w hw
    obtain ⟨sl, cap, ex, buf⟩ := a
    exact (by rp_t : SInv.IKE (RP v0) _) s (h1 _ has) w hw
  · intro e s hs v hv; exact (by rp_t : SInv.IK (RP v0) _) s hs v hv
  · intro a s b s' has hbs hI y hy
    obtain ⟨sl, cap, ex, buf⟩ := a
    have hcap : capOpt (s.kheap sl.1) sl.2 = some cap := okCap_front thread cptr info σ _ s has
    have hCs : CKI s := (h1 _ has).1
    have hk : KW cap := kw_of_slot hCs hcap
    have eE : hV s' = hV s := (by hv_auto : IKHE (fun x => hV x = hV s) _) s rfl _ hbs
    have hd : InvK b :=
      okdAt_bind (fun _ s1 _ => okd_fl4Decode_ck _ _ _ _ _ _ _ _ s hCs hk s1) b s' hbs eE
    have hP : SInv.IKE (ε := Unit) (RP v0) (fl4PerformInvocation (Z := Unit) blocking calling don b) :=
      rpe_of (ck_fl4Perform blocking calling don b hd) (rqe_fl4Perform_ck blocking calling don b hd) v0
    obtain ⟨z, hz, ⟨u, hu, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE_inv' hy
    · have hz1 : RP v0 z.2 := (by rp_t : SInv.IKE (ε := Unit) (RP v0)
        (withoutPreemption (Z := Unit) (setThreadState thread .restart))) s' hI z hz
      obtain ⟨r, s1⟩ := z
      simp only at hu; subst hu
      obtain ⟨z2, hz2, ⟨rp, hr, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE_inv' hy
      · obtain ⟨r2, s2⟩ := z2
        simp only at hr; subst hr
        have hs2 := hP s1 hz1 _ hz2
        exact (by rp_t : SInv.IKE (RP v0) _) s2 hs2 y hy
      · exact hP s1 hz1 _ hz2
    · exact (by rp_t : SInv.IKE (ε := Unit) (RP v0)
        (withoutPreemption (Z := Unit) (setThreadState thread .restart))) s' hI z hz

macro "rp_auto" : tactic => `(tactic| repeat' (first
  | (exact rp_handleInvocationR _ _ _ _ _ _ _)
  | (refine ike_bind ?_ fun _ => ?_)
  | rp_t))

set_option maxHeartbeats 16000000 in
theorem rpe_fl4HandleSyscall (v0 : ObjRef → Ticks) (rep : Bool) (c : Syscall) :
    SInv.IKE (ε := Unit) (RP v0) (fl4HandleSyscall (Z := Unit) rep c) := by
  cases c <;> simp only [fl4HandleSyscall] <;> rp_auto

set_option maxHeartbeats 8000000 in
theorem rpe_fl4HandleEvent (v0 : ObjRef → Ticks) (rep : Bool) (ev : Event) :
    SInv.IKE (ε := Unit) (RP v0) (fl4HandleEvent (Z := Unit) rep ev) := by
  by_cases h : ∃ c, ev = .syscallEvent c
  · obtain ⟨c, rfl⟩ := h
    simp only [fl4HandleEvent]
    refine ike_bind (by rp_t) fun _ => ike_bind (by rp_t) fun _ => ike_whenE _ (rpe_fl4HandleSyscall v0 rep c)
  · rw [fl4HandleEvent_other rep ev fun c e => h ⟨c, e⟩]
    exact rpe_of (ck_handleEvent_other ev fun c e => h ⟨c, e⟩) (rqe_handleEvent_other ev fun c e => h ⟨c, e⟩) v0

set_option maxHeartbeats 8000000 in
/-- **`fl4CallKernel` keeps `RP v`, for every event.** -/
theorem rp_fl4CallKernel (v0 : ObjRef → Ticks) (rep : Bool) (ev : Event) :
    SInv.IK (RP v0) (fl4CallKernel (Z := Unit) rep ev) := by
  unfold fl4CallKernel
  refine ik_bind (ike_handleE (rpe_fl4HandleEvent v0 rep ev) fun _ => by rp_t) fun _ => ?_
  exact ik_bind (rp_of (by hv_auto) rq_fl4Awaken v0) fun _ => ik_bind (rp_of (by hv_auto) rq_schedule v0) fun _ =>
    rp_of (by hv_auto) rq_activateThread v0

theorem rp_fl4KernelEntrySyscall (v0 : ObjRef → Ticks) (rep : Bool) (c : Syscall) :
    SInv.IK (RP v0) (fl4KernelEntrySyscall (Z := Unit) rep c) := by
  unfold fl4KernelEntrySyscall
  exact ik_bind (ik_gets _) fun ct => ik_bind (rp_of (by hv_auto) (rq_fl4SyscallFaultIP ct) v0) fun _ =>
    rp_fl4CallKernel v0 rep _


/-- **Every SC of the heap is round-robin** (period `0`; seL4 `is_round_robin`). -/
def RR (σ : State Unit) : Prop := rpV σ = fun _ => 0

theorem rr_period {σ : State Unit} (h : RR σ) {p : ObjRef} {sc : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext sc n)) : sc.scPeriod = 0 := by
  have e := congrFun h p
  unfold rpV at e
  rw [hk] at e
  exact e

/-- **`RR` across the syscall entry from a `CKI` state.** -/
theorem kentry_rr (rep : Bool) (c : Syscall) {σ : State Unit} (hC : CKI σ) (h : RR σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) rep c) σ).1, RR y.2 :=
  fun y hy => (rp_fl4KernelEntrySyscall (rpV σ) rep c σ ⟨hC, rfl⟩ y hy).2.trans h

/-- **`RR` across `fl4CallKernel` from a `CKI` state, every event.** -/
theorem kcall_rr (rep : Bool) (ev : Event) {σ : State Unit} (hC : CKI σ) (h : RR σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, RR y.2 :=
  fun y hy => (rp_fl4CallKernel (rpV σ) rep ev σ ⟨hC, rfl⟩ y hy).2.trans h

/-- **The spec boot state is `RR`.** -/
theorem rr_fInit : RR Fl4Proofs.P3.JBootQ.fInitASt := by
  have hB := Fl4Proofs.P3.JBootQ.bootHeap_fInit
  funext o
  unfold rpV
  cases hk : Fl4Proofs.P3.JBootQ.fInitASt.kheap o with
  | none => rfl
  | some k =>
    have hk' : Fl4Proofs.P3.JBoot.fInitKheap o = some k := hk
    rcases hB.obj o k hk' with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hB.tcb] at hk'; cases hk'; rfl
    · rw [hB.sc] at hk'; cases hk'; rfl
    all_goals rfl

end

end Fl4Proofs.P3.SInvRr
