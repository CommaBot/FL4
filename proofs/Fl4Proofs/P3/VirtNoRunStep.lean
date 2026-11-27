/-
P3x for virtualization (line virt, gen 18, item 2): **FL4's step is the extended step on every `NoRunVM` state, off
VMEnter — VCPUs and virtualization caps allowed, no `NV`, no `hvk`.**

On top of P3/VirtNoRunDel (deletion, TCB, CNode, SetEPTRoot: F = V on `NoRunVM`) and gen 13 / gen 7's
`NoRunVM`-only leaves (`sendSignalVF_eq_V_nr`, `maybeHandleInterruptV(F)_eq`, `preemptionPathV(F)_eq`,
`fl4KernelExitV(F)_eq'`: both sides the ported op there):

* `NoRunVM` frames of the extended decode / perform / dispatch: `ns_decodeVcpuInvocation`, `ns_decodeEptInvocation`,
  `ns_decodePageMapEpt`, `ns_decodeEptAsidPoolAssign`, `ns_decodeSetEptRoot`, **`ns_fl4DecodeInvocationV`**,
  `ns_fl4InvokeUntypedV`, `ns_sendSignalV`, `ns_associateVcpuTcb`, `ns_performVcpuInvocation`,
  `ns_performEptInvocation`, **`ns_fl4PerformInvocationV`**, `ns_lookupPart`, **`ns_fl4HandleInvocationV`**,
  **`ns_fl4HandleSyscallV`**, `ns_preemptionPathV`.
* F = V: **`fl4PerformInvocationVF_eq_nr`** (every invocation), `syscall_congr_fin`, **`fl4HandleInvocationVF_eq_nr`**,
  **`fl4HandleSyscallVF_eq_nr`** (every syscall), **`fl4HandleEventVF_eq_nr`** (every event that is not a VMEnter
  call at the state: `NotVmEnter ev σ`; `gets_mem`), **`ns_fl4HandleEventV`** (the extended event keeps `NoRunVM` off VMEnter),
  **`fl4CallKernelVF_eq_nr`**, **`fl4KernelEntrySyscallVF_eq_nr`** (a syscall event is never a VMEnter call).

The VMEnter route (`unknownSyscall n` with `isVmEnterCall n σ`) is excluded by the hypothesis `NotVmEnter ev σ`
(a property of the event at the entry state, not a premise): there `vmEnter` (V) and `vmEnterF` (FL4's report)
differ by construction and the state leaves `NoRunVM`.

No named premise; no [J]/[P]/[W]/[S]. New file only; no existing statement changed.
-/
import Fl4Proofs.P3.VirtNoRunDel
open Classical

namespace Fl4Proofs.P3.VirtNoRunStep
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.VirtR7b Fl4Proofs.P3.VirtR7d Fl4Proofs.P3.VirtR7e
  Fl4Proofs.P3.VirtReportEq Fl4Proofs.P3.VirtNoRunF Fl4Proofs.P3.VirtFinNR Fl4Proofs.P3.VirtNoRunDel

noncomputable section

set_option maxHeartbeats 1000000

/-! ## `NoRunVM` frames: decode -/

theorem ns_decodeVcpuInvocation (label : Data) (args : List Data) (v : ObjRef) (ex : List (Cap × CslotPtr)) :
    SInv.NSKE (decodeVcpuInvocation (Z := Unit) label args v ex) := by
  unfold decodeVcpuInvocation; ns_auto

theorem ns_decodeEptInvocation (label : Data) (args : List Data) (slot : CslotPtr) (c : ArchCap)
    (ex : List (Cap × CslotPtr)) : SInv.NSKE (decodeEptInvocation (Z := Unit) label args slot c ex) := by
  unfold decodeEptInvocation; ns_auto

theorem ns_decodePageMapEpt (args : List Data) (slot : CslotPtr) (c : ArchCap) (ex : List (Cap × CslotPtr)) :
    SInv.NSKE (decodePageMapEpt (Z := Unit) args slot c ex) := by
  unfold decodePageMapEpt; ns_auto

theorem ns_decodeEptAsidPoolAssign (p : ObjRef) (b : Asid) (x : CslotPtr) :
    SInv.NSKE (decodeEptAsidPoolAssign (Z := Unit) p b x) := by
  unfold decodeEptAsidPoolAssign; ns_auto

theorem ns_decodeSetEptRoot (t : ObjRef) (ex : List (Cap × CslotPtr)) :
    SInv.NSKE (decodeSetEptRoot (Z := Unit) t ex) := by
  unfold decodeSetEptRoot; ns_auto

/-- **The extended decode keeps `NoRunVM`**. -/
theorem ns_fl4DecodeInvocationV (fp : Bool) (label : Data) (args : List Data) (ci : CapRef) (slot : CslotPtr)
    (cap : Cap) (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) :
    SInv.NSKE (fl4DecodeInvocationV (Z := Unit) fp label args ci slot cap ex buf) := by
  have hb : SInv.NSKE (NonDetE.liftME Fl4InvocationV.base
      (fl4DecodeInvocation (Z := Unit) fp label args ci slot cap ex buf)) :=
    ike_liftME _ (ns_fl4DecodeInvocation _ _ _ _ _ _ _ _)
  unfold fl4DecodeInvocationV
  split
  · exact ike_liftME _ (ns_decodeVcpuInvocation _ _ _ _)
  · exact ike_liftME _ (ns_decodeEptInvocation _ _ _ _ _)
  · split
    · exact ike_liftME _ (ns_decodePageMapEpt _ _ _ _)
    · split
      · exact ike_throw _
      · split
        · exact ike_returnOk _
        · exact hb
  · split
    · exact ike_liftME _ (ns_decodeEptAsidPoolAssign _ _ _)
    · exact hb
  · split
    · exact ike_liftME _ (ns_decodeSetEptRoot _ _)
    · exact hb
  · split
    · exact ike_throw _
    · exact hb
  · exact hb

/-! ## `NoRunVM` frames: perform and dispatch -/

theorem ns_fl4InvokeUntypedV (ui : UntypedInvocation) : SInv.NSKE (fl4InvokeUntypedV (Z := Unit) ui) := by
  unfold fl4InvokeUntypedV
  refine ike_bind (ns_invokeUntypedWith _ _) fun _ => ?_
  cases ui
  dsimp only
  exact ike_liftE (ik_when _ (ik_mapMx (fun v => ns_setVcpu v _) _))

theorem ns_sendSignalV (onCore : ObjRef → Bool) (n : ObjRef) (b : Badge) :
    SInv.NSK (sendSignalV (Z := Unit) onCore n b) := fun σ hn x hx => by
  have e : sendSignalV (Z := Unit) onCore n b σ = sendSignal n b σ := VirtAwaken.sendSignalV_eq_nr onCore hn n b
  rw [e] at hx
  exact ns_sendSignal n b σ hn x hx

theorem ns_associateVcpuTcb (v t : ObjRef) : SInv.NSK (associateVcpuTcb (Z := Unit) v t) := by
  unfold associateVcpuTcb; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_associateVcpuTcb _ _)

theorem ns_performVcpuInvocation (i : VcpuInvocation) : SInv.NSK (performVcpuInvocation (Z := Unit) i) := by
  cases i <;> (unfold performVcpuInvocation; ns_auto)

theorem ns_performEptInvocation (i : EptInvocation) : SInv.NSK (performEptInvocation (Z := Unit) i) := by
  cases i <;> (unfold performEptInvocation; ns_auto)

/-- **The extended perform keeps `NoRunVM`**. -/
theorem ns_fl4PerformInvocationV (onCore : ObjRef → Bool) (blk call don : Bool) (i : Fl4InvocationV) :
    SInv.NSKE (fl4PerformInvocationV (Z := Unit) onCore blk call don i) := by
  cases i with
  | base b =>
    cases b with
    | invokeUntyped ui =>
      exact ike_bind (ns_fl4InvokeUntypedV ui) fun _ => ike_returnOk _
    | invokeNotification ep badge =>
      exact ike_bind (ike_liftE (ns_sendSignalV onCore ep badge)) fun _ => ike_returnOk _
    | invokeTCB ti => exact ns_invokeTcbV ti
    | invokeCNode ci => exact ike_bind (ns_invokeCnodeV ci) fun _ => ike_returnOk _
    | _ => exact ns_fl4PerformInvocation _ _ _ _
  | vcpu vi => exact ike_liftE (ns_performVcpuInvocation vi)
  | ept ei => exact ike_liftE (ik_bind (ns_performEptInvocation ei) fun _ => ik_pure _)
  | setEptRoot si => exact ike_bind (ns_invokeSetEptRoot si) fun _ => ike_returnOk _

theorem ns_lookupPart (t : ObjRef) (cptr : CapRef) (info : MessageInfo) : IKE NativeScopeS (lookupPart t cptr info) :=
  ik_lookupPart t cptr info (ns_capFaultOnFailure _ _ _ (ns_lookupCapAndSlot _ _)) (ns_lookupIpcBuffer _ _)
    fun _ => ns_lookupExtraCaps _ _ _

/-- **The extended invocation keeps `NoRunVM`**. -/
theorem ns_fl4HandleInvocationV (onCore : ObjRef → Bool) (rep calling blocking don fp : Bool) (cptr : CapRef) :
    SInv.NSKE (fl4HandleInvocationV (Z := Unit) onCore rep calling blocking don fp cptr) := by
  unfold fl4HandleInvocationV syscall withoutPreemption
  refine ike_bind (ike_liftE (ik_gets _)) fun thread => ?_
  refine ike_bind (ike_liftE (ns_getMessageInfo _)) fun info => ?_
  refine ike_bind (ike_liftE (ns_lookupPart thread cptr info)) fun r => ?_
  rcases r with f | ⟨slot, cap, ex, buf⟩
  · exact ike_liftE (ik_when _ (ns_handleFault _ _))
  · dsimp only
    refine ike_bind (ike_liftE (ike_bind (ike_liftE (ns_getMrs _ _ _)) fun args =>
      ns_fl4DecodeInvocationV _ _ _ _ _ _ _ _)) fun r2 => ?_
    rcases r2 with e | oper
    · exact ike_liftE (ik_when _ (ns_fl4ReplyFromKernelError _ _ _))
    · dsimp only
      refine ike_bind (ike_liftE (ns_setThreadState _ _ (by decide))) fun _ => ?_
      refine ike_bind (ns_fl4PerformInvocationV onCore _ _ _ oper) fun reply => ?_
      ns_auto

/-- **Every extended syscall keeps `NoRunVM`**. -/
theorem ns_fl4HandleSyscallV (onCore : ObjRef → Bool) (rep : Bool) (c : Syscall) :
    SInv.NSKE (fl4HandleSyscallV (Z := Unit) onCore rep c) := by
  cases c <;> (unfold fl4HandleSyscallV withoutPreemption) <;>
    first
    | exact ike_bind (ike_liftE (ns_getCapReg _)) fun _ => ns_fl4HandleInvocationV _ _ _ _ _ _ _
    | exact ike_bind (ike_liftE (ns_getCapReg _)) fun _ =>
        ike_bind (ns_fl4HandleInvocationV _ _ _ _ _ _ _) fun _ => ike_liftE (ns_handleRecv _ _)
    | exact ike_liftE (ns_handleRecv _ _)
    | exact ike_liftE (ns_handleYield)

/-! ## F = V: perform, invocation, syscall -/

/-- **Every invocation, F = V on `NoRunVM` states**. -/
theorem fl4PerformInvocationVF_eq_nr (onCore remoteCur : ObjRef → Bool) (blk call don : Bool) (i : Fl4InvocationV)
    {s : State Unit} (hs : NoRunVM s) :
    ExceptT.run (fl4PerformInvocationVF (Z := Unit) onCore remoteCur blk call don i) s =
      ExceptT.run (fl4PerformInvocationV onCore blk call don i) s := by
  cases i with
  | base b =>
    cases b with
    | invokeUntyped ui => rfl
    | invokeNotification ep badge =>
      show ExceptT.run (withoutPreemption (sendSignalVF (Z := Unit) onCore remoteCur ep badge) >>= fun _ =>
          NonDetE.returnOk []) s = ExceptT.run (withoutPreemption (sendSignalV onCore ep badge) >>= fun _ =>
          NonDetE.returnOk []) s
      exact nde_bind_congr (run_liftE_congr (sendSignalVF_eq_V_nr onCore remoteCur hs ep badge)) fun _ _ _ => rfl
    | invokeTCB ti => exact invokeTcbVF_eq_nr ti hs
    | invokeCNode ci =>
      show ExceptT.run (invokeCnodeVF (Z := Unit) ci >>= fun _ => NonDetE.returnOk []) s =
        ExceptT.run (invokeCnodeV ci >>= fun _ => NonDetE.returnOk []) s
      exact nde_bind_congr (invokeCnodeVF_eq_nr ci hs) fun _ _ _ => rfl
    | _ => rfl
  | vcpu vi =>
    show ExceptT.run (NonDetE.liftE (ε := Unit) (performVcpuInvocationF (Z := Unit) vi)) s =
      ExceptT.run (NonDetE.liftE (performVcpuInvocation vi)) s
    exact run_liftE_congr (performVcpuInvocationF_eq_nr hs vi)
  | ept ei => rfl
  | setEptRoot si =>
    show ExceptT.run (invokeSetEptRootF (Z := Unit) si >>= fun _ => NonDetE.returnOk []) s =
      ExceptT.run (invokeSetEptRoot si >>= fun _ => NonDetE.returnOk []) s
    exact nde_bind_congr (invokeSetEptRootF_eq_nr si hs) fun _ _ _ => rfl

/-- `syscall` depends on its finalisation only at the decoded outcomes. -/
theorem syscall_congr_fin {α β γ : Type} (mF : FMonad Unit α) (hF : Fault → SMonad Unit γ)
    (mE : α → SEMonad Unit β) (hE : SyscallError → SMonad Unit γ) (fin fin' : β → PMonad Unit γ) {s : State Unit}
    (hfin : ∀ a t b u, ((Except.ok a : Except Fault α), t) ∈ (ExceptT.run mF s).1 →
      ((Except.ok b : Except SyscallError β), u) ∈ (ExceptT.run (mE a) t).1 →
      ExceptT.run (fin' b) u = ExceptT.run (fin b) u) :
    ExceptT.run (syscall mF hF mE hE fin') s = ExceptT.run (syscall mF hF mE hE fin) s := by
  unfold syscall
  refine nde_bind_congr rfl fun r t hr => ?_
  have hr' := mem_run_liftE' hr
  cases r with
  | error e => rfl
  | ok a =>
    dsimp only
    refine nde_bind_congr rfl fun r2 u hu => ?_
    have hu' := mem_run_liftE' hu
    cases r2 with
    | error e => rfl
    | ok b => exact hfin a t b u hr' hu'

/-- **The invocation, F = V on `NoRunVM` states** (any capability; no `OffRoute`). -/
theorem fl4HandleInvocationVF_eq_nr (onCore remoteCur : ObjRef → Bool) (rep calling blocking don fp : Bool)
    (cptr : CapRef) {s : State Unit} (hs : NoRunVM s) :
    ExceptT.run (fl4HandleInvocationVF (Z := Unit) onCore remoteCur rep calling blocking don fp cptr) s =
      ExceptT.run (fl4HandleInvocationV onCore rep calling blocking don fp cptr) s := by
  unfold fl4HandleInvocationVF fl4HandleInvocationV
  refine nde_bind_congr rfl fun thread s0 h0 => ?_
  have h0' := mem_run_liftE' h0
  simp only [NonDet.gets, Set.mem_singleton_iff, Prod.mk.injEq] at h0'
  obtain ⟨rfl, rfl⟩ := h0'
  refine nde_bind_congr rfl fun info s1 h1 => ?_
  have n1 : NoRunVM s1 := ns_getMessageInfo _ s0 hs _ (mem_run_liftE' h1)
  refine syscall_congr_fin _ _ _ _ _ _ fun a t b u ha hb => ?_
  obtain ⟨slot, cap, ex, buf⟩ := a
  have nt : NoRunVM t := ns_lookupPart _ cptr info s1 n1 _ ha
  have nu : NoRunVM u := (ike_bind (ike_liftE (ns_getMrs _ _ _)) fun args =>
    ns_fl4DecodeInvocationV _ _ _ _ _ _ _ _) t nt _ hb
  refine nde_bind_congr rfl fun _ v hv => ?_
  have nv : NoRunVM v := ns_setThreadState _ _ (by decide) u nu _ (mem_run_liftE' hv)
  exact nde_bind_congr (fl4PerformInvocationVF_eq_nr onCore remoteCur blocking calling don b nv) fun _ _ _ => rfl

/-- **Every syscall, F = V on `NoRunVM` states**. -/
theorem fl4HandleSyscallVF_eq_nr (onCore remoteCur : ObjRef → Bool) (rep : Bool) (c : Syscall) {s : State Unit}
    (hs : NoRunVM s) :
    ExceptT.run (fl4HandleSyscallVF (Z := Unit) onCore remoteCur rep c) s =
      ExceptT.run (fl4HandleSyscallV onCore rep c) s := by
  have h1 : ∀ (cr : Register) (k : CapRef → PMonad Unit Unit) (k' : CapRef → PMonad Unit Unit),
      (∀ x t, NoRunVM t → ExceptT.run (k x) t = ExceptT.run (k' x) t) →
      ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) cr) >>= k) s =
        ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) cr) >>= k') s := fun cr k k' hk =>
    nde_bind_congr rfl fun x t h => hk x t (ns_getCapReg _ s hs _ (mem_run_liftE' h))
  have hI := fun rep' a b c d cptr t (ht : NoRunVM t) =>
    fl4HandleInvocationVF_eq_nr onCore remoteCur rep' a b c d cptr ht
  cases c with
  | sysSend => unfold fl4HandleSyscallVF fl4HandleSyscallV; exact h1 _ _ _ fun x t ht => hI _ _ _ _ _ _ _ ht
  | sysNBSend => unfold fl4HandleSyscallVF fl4HandleSyscallV; exact h1 _ _ _ fun x t ht => hI _ _ _ _ _ _ _ ht
  | sysCall => unfold fl4HandleSyscallVF fl4HandleSyscallV; exact h1 _ _ _ fun x t ht => hI _ _ _ _ _ _ _ ht
  | sysReplyRecv =>
    unfold fl4HandleSyscallVF fl4HandleSyscallV withoutPreemption
    exact h1 _ _ _ fun x t ht => nde_bind_congr (hI _ _ _ _ _ _ _ ht) fun _ _ _ => rfl
  | sysNBSendRecv =>
    unfold fl4HandleSyscallVF fl4HandleSyscallV withoutPreemption
    exact h1 _ _ _ fun x t ht => nde_bind_congr (hI _ _ _ _ _ _ _ ht) fun _ _ _ => rfl
  | sysNBSendWait =>
    unfold fl4HandleSyscallVF fl4HandleSyscallV withoutPreemption
    exact h1 _ _ _ fun x t ht => nde_bind_congr (hI _ _ _ _ _ _ _ ht) fun _ _ _ => rfl
  | sysRecv => rfl
  | sysYield => rfl
  | sysWait => rfl
  | sysNBWait => rfl
  | sysNBRecv => rfl

/-! ## Events and the kernel call -/

/-- The event is not a VMEnter call at the state (the scope of the transport). -/
def NotVmEnter (ev : Event) (σ : State Unit) : Prop := ∀ n, ev = .unknownSyscall n → isVmEnterCall n σ = false

theorem gets_mem {α : Type} {g : State Unit → α} {s t : State Unit} {a : α} {ε : Type}
    (h : ((Except.ok a : Except ε α), t) ∈ (ExceptT.run (NonDetE.liftE (NonDet.gets g)) s).1) : a = g s ∧ t = s := by
  have h' := mem_run_liftE' h
  simp only [NonDet.gets, Set.mem_singleton_iff, Prod.mk.injEq] at h'
  exact h'

/-- **Every event off VMEnter, F = V on `NoRunVM` states**. -/
theorem fl4HandleEventVF_eq_nr (onCore remoteCur : ObjRef → Bool) (rep : Bool) (ev : Event) {s : State Unit}
    (hs : NoRunVM s) (hv : NotVmEnter ev s) :
    ExceptT.run (fl4HandleEventVF (Z := Unit) onCore remoteCur rep ev) s =
      ExceptT.run (fl4HandleEventV onCore rep ev) s := by
  cases ev with
  | syscallEvent c =>
    unfold fl4HandleEventVF fl4HandleEventV
    refine nde_bind_congr rfl fun _ t1 h1 => ?_
    have n1 : NoRunVM t1 := ns_updateTimeStamp s hs _ (mem_run_liftE' h1)
    refine nde_bind_congr rfl fun r t2 h2 => ?_
    have n2 : NoRunVM t2 := ns_checkBudgetRestart t1 n1 _ (mem_run_liftE' h2)
    unfold NonDetE.whenE
    by_cases hr : r = true
    · rw [if_pos hr, if_pos hr]; exact fl4HandleSyscallVF_eq_nr onCore remoteCur rep c n2
    · rw [if_neg hr, if_neg hr]
  | unknownSyscall n =>
    unfold fl4HandleEventVF fl4HandleEventV
    refine nde_bind_congr rfl fun vm t h => ?_
    obtain ⟨rfl, rfl⟩ := gets_mem h
    rw [hv n rfl, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
  | interrupt =>
    unfold fl4HandleEventVF fl4HandleEventV withoutPreemption
    refine run_liftE_congr ?_
    refine nd_bind_congr_on _ _ _ s fun y1 h1 => ?_
    have n1 : NoRunVM y1.2 := ns_updateTimeStamp s hs _ h1
    refine nd_bind_congr_on _ _ _ y1.2 fun y2 h2 => ?_
    have n2 : NoRunVM y2.2 := ns_checkBudget y1.2 n1 _ h2
    exact (VirtF13.maybeHandleInterruptVF_eq onCore remoteCur n2 false).trans
      (VirtAwaken.maybeHandleInterruptV_eq onCore n2 false).symm
  | _ => rfl

/-- **The extended event keeps `NoRunVM` off VMEnter**. -/
theorem ns_fl4HandleEventV (onCore : ObjRef → Bool) (rep : Bool) (ev : Event) {s : State Unit} (hs : NoRunVM s)
    (hv : NotVmEnter ev s) {x : Except Unit Unit × State Unit}
    (hx : x ∈ (ExceptT.run (fl4HandleEventV (Z := Unit) onCore rep ev) s).1) : NoRunVM x.2 := by
  cases ev with
  | syscallEvent c =>
    have h : SInv.NSKE (fl4HandleEventV (Z := Unit) onCore rep (.syscallEvent c)) := by
      unfold fl4HandleEventV
      exact ike_bind (ike_liftE ns_updateTimeStamp) fun _ =>
        ike_bind (ike_liftE ns_checkBudgetRestart) fun _ => ike_whenE _ (ns_fl4HandleSyscallV onCore rep c)
    exact h s hs x hx
  | unknownSyscall n =>
    unfold fl4HandleEventV at hx
    rw [ExceptT.run_bind] at hx
    obtain ⟨⟨r, t⟩, hr, hx⟩ := hx
    cases r with
    | error e =>
      simp only [ExceptT.bindCont] at hx
      obtain rfl := Set.mem_singleton_iff.1 hx
      exact (ike_liftE (ik_gets (P := NativeScopeS) (isVmEnterCall n))) s hs _ hr
    | ok vm =>
      obtain ⟨rfl, rfl⟩ := gets_mem hr
      simp only [ExceptT.bindCont] at hx
      rw [hv n rfl, if_neg Bool.false_ne_true] at hx
      exact ns_handleEvent _ _ hs x hx
  | interrupt =>
    have h : SInv.NSKE (fl4HandleEventV (Z := Unit) onCore rep .interrupt) := by
      unfold fl4HandleEventV withoutPreemption
      refine ike_liftE (ik_bind ns_updateTimeStamp fun _ => ik_bind ns_checkBudget fun _ => ?_)
      intro σ hn y hy
      rw [VirtAwaken.maybeHandleInterruptV_eq onCore hn false] at hy
      exact ns_maybeHandleInterrupt _ σ hn y hy
    exact h s hs x hx
  | _ => exact ns_handleEvent _ s hs x hx

theorem ns_preemptionPathV (onCore : ObjRef → Bool) : SInv.NSK (preemptionPathV (Z := Unit) onCore) :=
  fun σ hn y hy => by
    rw [VirtAwaken.preemptionPathV_eq onCore hn] at hy
    exact ns_preemptionPath σ hn y hy

/-- **FL4's kernel call is the extended one on every `NoRunVM` state, off VMEnter** (no `NV`, no `hvk`). -/
theorem fl4CallKernelVF_eq_nr (onCore remoteCur : ObjRef → Bool) (rep : Bool) (ev : Event) {s : State Unit}
    (hs : NoRunVM s) (hv : NotVmEnter ev s) :
    fl4CallKernelVF (Z := Unit) onCore remoteCur rep ev s = fl4CallKernelV onCore rep ev s := by
  unfold fl4CallKernelVF fl4CallKernelV
  have hH : ExceptT.run (NonDetE.handleE (fl4HandleEventVF (Z := Unit) onCore remoteCur rep ev)
        (fun _ => withoutPreemption (preemptionPathVF onCore remoteCur))) s =
      ExceptT.run (NonDetE.handleE (fl4HandleEventV (Z := Unit) onCore rep ev)
        (fun _ => withoutPreemption (preemptionPathV onCore))) s := by
    unfold NonDetE.handleE
    rw [ExceptT.run_mk, ExceptT.run_mk]
    refine (nd_bind_eq_of (fl4HandleEventVF_eq_nr onCore remoteCur rep ev hs hv) _).trans
      (nd_bind_congr_on _ _ _ s fun y hy => ?_)
    obtain ⟨r, u⟩ := y
    cases r with
    | ok a => rfl
    | error e =>
      have hu : NoRunVM u := ns_fl4HandleEventV onCore rep ev hs hv hy
      exact run_liftE_congr ((VirtF13.preemptionPathVF_eq onCore remoteCur hu).trans
        (VirtAwaken.preemptionPathV_eq onCore hu).symm)
  rw [nd_bind_eq_of hH]
  refine nd_bind_congr_on _ _ _ s fun y hy => ?_
  have hu : NoRunVM y.2 := by
    unfold NonDetE.handleE at hy
    rw [ExceptT.run_mk] at hy
    obtain ⟨⟨r, u⟩, hru, hy⟩ := hy
    have nu : NoRunVM u := ns_fl4HandleEventV onCore rep ev hs hv hru
    cases r with
    | ok a => obtain rfl := Set.mem_singleton_iff.1 hy; exact nu
    | error e => exact (ike_liftE (ε := Unit) (ns_preemptionPathV onCore)) u nu _ hy
  exact (VirtF13.fl4KernelExitVF_eq' onCore remoteCur hu).trans (VirtAwaken.fl4KernelExitV_eq' onCore hu).symm

/-- **FL4's syscall entry is the extended one on every `NoRunVM` state** (a syscall event is never VMEnter). -/
theorem fl4KernelEntrySyscallVF_eq_nr (onCore remoteCur : ObjRef → Bool) (rep : Bool) (c : Syscall)
    {s : State Unit} (hs : NoRunVM s) :
    fl4KernelEntrySyscallVF (Z := Unit) onCore remoteCur rep c s = fl4KernelEntrySyscallV onCore rep c s := by
  unfold fl4KernelEntrySyscallVF fl4KernelEntrySyscallV
  refine nd_bind_congr_on _ _ _ s fun y hy => ?_
  simp only [NonDet.gets, Set.mem_singleton_iff] at hy
  subst hy
  refine nd_bind_congr_on _ _ _ s fun w hw => ?_
  exact fl4CallKernelVF_eq_nr onCore remoteCur rep _ (ns_fl4SyscallFaultIP _ s hs w hw) fun n e => by cases e

end
end Fl4Proofs.P3.VirtNoRunStep
