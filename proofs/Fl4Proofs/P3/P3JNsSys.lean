/-
P3 (p3J gen 24): **"no signal line" (`NoSig`) across every kernel entry from a `CKI` state** (spec side only;
outside the `JAtZ` cone).

* The syscalls, events and the FaultIP write above the invocation shell (irqfix's SpecInvIrqBound, renamed `GKB` ↦
  `GKN` by `scratch/p3J/genNs.py`), without the shell itself.
* `NP σ := CKI σ ∧ NoSig σ`: kept by every piece that keeps `CKI` (P3JCkW/X/S, `hv_auto`) and is `GKN`
  (P3JNsKit/Gen, `gkn_auto`) (`np_of`). The invocation shell **`np_handleInvocationR`** (P3JKtSys's
  `kp_handleInvocationR` with `NP`: the decode's carry `InvK` from the `CKI` state at the decode gives the perform's
  `GKN`, `gkn_fl4PerformInvocation`), the syscalls, **`np_fl4KernelEntrySyscall`**, **`np_fl4CallKernel`** (every
  event).
* Tops: **`kentry_noSig`**, **`kcall_noSig`**: `NoSig` at every outcome of a syscall entry / a kernel event from
  `CKI ∧ NoSig`. Why it matters: on a run that keeps `CKI` (no IRQ-control cap) no IRQ handler is ever issued, so
  `handle_interrupt` never takes its signal branch (P3JMcIrqF's `IrqSigFootJ` is then not needed).

Named premises: none. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JNsGen
import Fl4Proofs.P3.SpecInvValidIrqHandlersS
import Fl4Proofs.P3.P3JKtSys

open Classical

namespace Fl4Proofs.P3.SInvNs

section
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.Vs Fl4Proofs.P3.MachF Fl4Proofs.P3.MachT Fl4Proofs.P3.SInvV
open Fl4Proofs.P3.SInvDom

noncomputable section

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

theorem gkn_getCapReg (reg : Register) : GKN (getCapReg (Z := Unit) reg) := by
  unfold getCapReg; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_getCapReg)

theorem gkn_lookupReply  : GKNE (lookupReply (Z := Unit)) := by
  unfold lookupReply; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_lookupReply)

theorem gkn_getEndpoint (x0 : ObjRef) : GKN (getEndpoint (Z := Unit) x0) := by
  unfold getEndpoint; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_getEndpoint)

theorem gkn_getReply (x0 : ObjRef) : GKN (getReply (Z := Unit) x0) := by
  unfold getReply; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_getReply)

theorem gkn_getReplyTcb (r : ObjRef) : GKN (getReplyTcb (Z := Unit) r) := by
  unfold getReplyTcb; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_getReplyTcb)

theorem gkn_maybeReturnSc (ntfnPtr tcbPtr : ObjRef) : GKN (maybeReturnSc (Z := Unit) ntfnPtr tcbPtr) := by
  unfold maybeReturnSc; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_maybeReturnSc)

theorem gkn_setReplyObjRef (update : (Option ObjRef → Option ObjRef) → Reply → Reply) (ref : ObjRef) (new : Option ObjRef) : GKN (setReplyObjRef (Z := Unit) update ref new) := by
  unfold setReplyObjRef; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_setReplyObjRef)

theorem gkn_receiveIpcBlocked (isBlocking : Bool) (thread epptr : ObjRef) (reply : Option ObjRef) : GKN (receiveIpcBlocked (Z := Unit) isBlocking thread epptr reply) := by
  unfold receiveIpcBlocked; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_receiveIpcBlocked)

set_option maxHeartbeats 4000000 in
theorem gkn_receiveIpc (thread : ObjRef) (cap : Cap) (isBlocking : Bool) (replyCap : Cap) : GKN (receiveIpc (Z := Unit) thread cap isBlocking replyCap) := by
  unfold receiveIpc; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_receiveIpc)

theorem gkn_tcbNtfnAppend (tptr ntfnPtr : ObjRef) : GKN (tcbNtfnAppend (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnAppend; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_tcbNtfnAppend)

theorem gkn_receiveSignalBlocked (thread ntfnptr : ObjRef) (isBlocking : Bool) : GKN (receiveSignalBlocked (Z := Unit) thread ntfnptr isBlocking) := by
  unfold receiveSignalBlocked; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_receiveSignalBlocked)

theorem gkn_receiveSignal (thread : ObjRef) (cap : Cap) (isBlocking : Bool) : GKN (receiveSignal (Z := Unit) thread cap isBlocking) := by
  unfold receiveSignal; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_receiveSignal)

theorem gkn_handleRecv (isBlocking canReply : Bool) : GKN (handleRecv (Z := Unit) isBlocking canReply) := by
  unfold handleRecv; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_handleRecv)

theorem gkn_handleYield  : GKN (handleYield (Z := Unit)) := by
  unfold handleYield; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_handleYield)

theorem gkn_fl4SyscallFaultIP (thread : ObjRef) : GKN (fl4SyscallFaultIP (Z := Unit) thread) := by
  unfold fl4SyscallFaultIP; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_fl4SyscallFaultIP)

theorem gkn_handleReservedIrq (_irq : Irq) : GKN (handleReservedIrq (Z := Unit) _irq) := by
  unfold handleReservedIrq; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_handleReservedIrq)

theorem gkn_handleInterrupt (irq : Irq) : GKN (handleInterrupt (Z := Unit) irq) := by
  unfold handleInterrupt; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_handleInterrupt)

theorem gkn_handleSpuriousIrq  : GKN (handleSpuriousIrq (Z := Unit)) := by
  unfold handleSpuriousIrq; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_handleSpuriousIrq)

theorem gkn_maybeHandleInterrupt (inKernel : Bool) : GKN (maybeHandleInterrupt (Z := Unit) inKernel) := by
  unfold maybeHandleInterrupt; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_maybeHandleInterrupt)

theorem gkn_preemptionPath  : GKN (preemptionPath (Z := Unit)) := by
  unfold preemptionPath; gkn_auto
macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_preemptionPath)

/-- The VM fault handler (as SInvAllV's `gk_handleVmFault`): the fault address, a register read, a throw. -/
theorem gkn_handleVmFault (thread : ObjRef) (ft : VMFaultType) : GKNE (handleVmFault (Z := Unit) thread ft) := by
  cases ft <;> (unfold handleVmFault; gkn_auto)

macro_rules | `(tactic| gkn_leaf) => `(tactic| with_reducible apply gkn_handleVmFault)

theorem gkn_handleEvent_other (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) : GKNE (handleEvent (Z := Unit) ev) := by
  cases ev with
  | syscallEvent c => exact absurd rfl (h c)
  | _ => simp only [handleEvent]; gkn_auto


end

end

section
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvV Fl4Proofs.P3.SInvDom Fl4Proofs.P3.SInvIo
open Fl4Proofs.P3.SInvCk Fl4Proofs.P3.Vs

noncomputable section

set_option maxRecDepth 20000

/-- `CKI` and no signal line. -/
def NP (σ : State Unit) : Prop := CKI σ ∧ NoSig σ

theorem np_of {α : Type} {m : NonDet (State Unit) α} (h1 : IKH CKI m) (h2 : GKN m) : SInv.IK NP m :=
  fun σ hσ x hx => ⟨h1 σ hσ.1 x hx, h2 NoSig wln_noSig σ hσ.2 x hx⟩

theorem npe_of {ε α : Type} {m : NonDetE (State Unit) ε α} (h1 : IKHE CKI m) (h2 : GKNE m) : SInv.IKE NP m :=
  np_of h1 h2

macro "np_t" : tactic => `(tactic| first
  | (exact npe_of (by hv_auto) (by gkn_auto))
  | (exact np_of (by hv_auto) (by gkn_auto)))

set_option maxHeartbeats 16000000 in
/-- **The invocation shell keeps `NP`** (P3JKtSys's `kp_handleInvocationR` with `NP`). -/
theorem np_handleInvocationR (rep calling blocking don fp : Bool) (cptr : CapRef) :
    SInv.IKE (ε := Unit) NP (fl4HandleInvocationR (Z := Unit) rep calling blocking don fp cptr) := by
  unfold fl4HandleInvocationR
  refine ike_bind (by np_t) fun thread => ike_bind (by np_t) fun info => ?_
  intro σ hs y hy
  have h1 : ∀ w ∈ ((ExceptT.run (do
       let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot (Z := Unit) thread cptr
       let buffer ← NonDetE.liftE <| lookupIpcBuffer false thread
       let extracaps ← lookupExtraCaps thread buffer info
       NonDetE.returnOk (slot, cap, extracaps, buffer))) σ).1, NP w.2 :=
    fun w hw => (by np_t : SInv.IKE (ε := Fault) NP _) σ hs w hw
  refine syscall_post' (I := NP) (Q := NP) h1 ?_ ?_ ?_ ?_ y hy
  · intro f s hs v hv; exact (by np_t : SInv.IK NP _) s hs v hv
  · intro a s has w hw
    obtain ⟨sl, cap, ex, buf⟩ := a
    exact (by np_t : SInv.IKE NP _) s (h1 _ has) w hw
  · intro e s hs v hv; exact (by np_t : SInv.IK NP _) s hs v hv
  · intro a s b s' has hbs hI y hy
    obtain ⟨sl, cap, ex, buf⟩ := a
    have hcap : capOpt (s.kheap sl.1) sl.2 = some cap := okCap_front thread cptr info σ _ s has
    have hCs : CKI s := (h1 _ has).1
    have hk : KW cap := kw_of_slot hCs hcap
    have eE : hV s' = hV s := (by hv_auto : IKHE (fun x => hV x = hV s) _) s rfl _ hbs
    have hd : InvK b :=
      okdAt_bind (fun _ s1 _ => okd_fl4Decode_ck _ _ _ _ _ _ _ _ s hCs hk s1) b s' hbs eE
    have hP : SInv.IKE (ε := Unit) NP (fl4PerformInvocation (Z := Unit) blocking calling don b) :=
      npe_of (ck_fl4Perform blocking calling don b hd) (gkn_fl4PerformInvocation blocking calling don b hd)
    obtain ⟨z, hz, ⟨u, hu, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE_inv' hy
    · have hz1 : NP z.2 := (by np_t : SInv.IKE (ε := Unit) NP
        (withoutPreemption (Z := Unit) (setThreadState thread .restart))) s' hI z hz
      obtain ⟨r, s1⟩ := z
      simp only at hu; subst hu
      obtain ⟨z2, hz2, ⟨rp, hr, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE_inv' hy
      · obtain ⟨r2, s2⟩ := z2
        simp only at hr; subst hr
        have hs2 := hP s1 hz1 _ hz2
        exact (by np_t : SInv.IKE NP _) s2 hs2 y hy
      · exact hP s1 hz1 _ hz2
    · exact (by np_t : SInv.IKE (ε := Unit) NP
        (withoutPreemption (Z := Unit) (setThreadState thread .restart))) s' hI z hz

macro "np_auto" : tactic => `(tactic| repeat' (first
  | (exact np_handleInvocationR _ _ _ _ _ _)
  | (refine ike_bind ?_ fun _ => ?_)
  | np_t))

set_option maxHeartbeats 16000000 in
theorem npe_fl4HandleSyscall (rep : Bool) (c : Syscall) :
    SInv.IKE (ε := Unit) NP (fl4HandleSyscall (Z := Unit) rep c) := by
  cases c <;> simp only [fl4HandleSyscall] <;> np_auto

set_option maxHeartbeats 8000000 in
theorem npe_fl4HandleEvent (rep : Bool) (ev : Event) :
    SInv.IKE (ε := Unit) NP (fl4HandleEvent (Z := Unit) rep ev) := by
  by_cases h : ∃ c, ev = .syscallEvent c
  · obtain ⟨c, rfl⟩ := h
    simp only [fl4HandleEvent]
    refine ike_bind (by np_t) fun _ => ike_bind (by np_t) fun _ => ike_whenE _ (npe_fl4HandleSyscall rep c)
  · rw [fl4HandleEvent_other rep ev fun c e => h ⟨c, e⟩]
    exact npe_of (ck_handleEvent_other ev fun c e => h ⟨c, e⟩) (gkn_handleEvent_other ev fun c e => h ⟨c, e⟩)

set_option maxHeartbeats 8000000 in
/-- **`fl4CallKernel` keeps `NP`, for every event.** -/
theorem np_fl4CallKernel (rep : Bool) (ev : Event) : SInv.IK NP (fl4CallKernel (Z := Unit) rep ev) := by
  unfold fl4CallKernel
  refine ik_bind (ike_handleE (npe_fl4HandleEvent rep ev) fun _ => by np_t) fun _ => ?_
  exact ik_bind (np_of (by hv_auto) gkn_fl4Awaken) fun _ => ik_bind (np_of (by hv_auto) gkn_schedule) fun _ =>
    np_of (by hv_auto) gkn_activateThread

theorem np_fl4KernelEntrySyscall (rep : Bool) (c : Syscall) :
    SInv.IK NP (fl4KernelEntrySyscall (Z := Unit) rep c) := by
  unfold fl4KernelEntrySyscall
  exact ik_bind (ik_gets _) fun ct => ik_bind (np_of (by hv_auto) (gkn_fl4SyscallFaultIP ct)) fun _ =>
    np_fl4CallKernel rep _

/-- **`NoSig` across the syscall entry from a `CKI` state.** -/
theorem kentry_noSig (rep : Bool) (c : Syscall) {σ : State Unit} (hC : CKI σ) (h : NoSig σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) rep c) σ).1, NoSig y.2 :=
  fun y hy => (np_fl4KernelEntrySyscall rep c σ ⟨hC, h⟩ y hy).2

/-- **`NoSig` across `fl4CallKernel` from a `CKI` state, every event.** -/
theorem kcall_noSig (rep : Bool) (ev : Event) {σ : State Unit} (hC : CKI σ) (h : NoSig σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, NoSig y.2 :=
  fun y hy => (np_fl4CallKernel rep ev σ ⟨hC, h⟩ y hy).2

end

end

end Fl4Proofs.P3.SInvNs
