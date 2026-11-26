theorem gkb_fl4HandleInvocationR (reportError : Bool) (calling blocking canDonate firstPhase : Bool) (cptr : CapRef) : GKBE (fl4HandleInvocationR (Z := Unit) reportError calling blocking canDonate firstPhase cptr) := by
  unfold fl4HandleInvocationR; gkb_auto
macro_rules | `(tactic| gkb_leaf) => `(tactic| with_reducible apply gkb_fl4HandleInvocationR)

theorem gkb_getCapReg (reg : Register) : GKB (getCapReg (Z := Unit) reg) := by
  unfold getCapReg; gkb_auto
macro_rules | `(tactic| gkb_leaf) => `(tactic| with_reducible apply gkb_getCapReg)

theorem gkb_lookupReply  : GKBE (lookupReply (Z := Unit)) := by
  unfold lookupReply; gkb_auto
macro_rules | `(tactic| gkb_leaf) => `(tactic| with_reducible apply gkb_lookupReply)

theorem gkb_getEndpoint (x0 : ObjRef) : GKB (getEndpoint (Z := Unit) x0) := by
  unfold getEndpoint; gkb_auto
macro_rules | `(tactic| gkb_leaf) => `(tactic| with_reducible apply gkb_getEndpoint)

theorem gkb_getReply (x0 : ObjRef) : GKB (getReply (Z := Unit) x0) := by
  unfold getReply; gkb_auto
macro_rules | `(tactic| gkb_leaf) => `(tactic| with_reducible apply gkb_getReply)

theorem gkb_getReplyTcb (r : ObjRef) : GKB (getReplyTcb (Z := Unit) r) := by
  unfold getReplyTcb; gkb_auto
macro_rules | `(tactic| gkb_leaf) => `(tactic| with_reducible apply gkb_getReplyTcb)

theorem gkb_maybeReturnSc (ntfnPtr tcbPtr : ObjRef) : GKB (maybeReturnSc (Z := Unit) ntfnPtr tcbPtr) := by
  unfold maybeReturnSc; gkb_auto
macro_rules | `(tactic| gkb_leaf) => `(tactic| with_reducible apply gkb_maybeReturnSc)

theorem gkb_setReplyObjRef (update : (Option ObjRef → Option ObjRef) → Reply → Reply) (ref : ObjRef) (new : Option ObjRef) : GKB (setReplyObjRef (Z := Unit) update ref new) := by
  unfold setReplyObjRef; gkb_auto
macro_rules | `(tactic| gkb_leaf) => `(tactic| with_reducible apply gkb_setReplyObjRef)

theorem gkb_receiveIpcBlocked (isBlocking : Bool) (thread epptr : ObjRef) (reply : Option ObjRef) : GKB (receiveIpcBlocked (Z := Unit) isBlocking thread epptr reply) := by
  unfold receiveIpcBlocked; gkb_auto
macro_rules | `(tactic| gkb_leaf) => `(tactic| with_reducible apply gkb_receiveIpcBlocked)

set_option maxHeartbeats 4000000 in
theorem gkb_receiveIpc (thread : ObjRef) (cap : Cap) (isBlocking : Bool) (replyCap : Cap) : GKB (receiveIpc (Z := Unit) thread cap isBlocking replyCap) := by
  unfold receiveIpc; gkb_auto
macro_rules | `(tactic| gkb_leaf) => `(tactic| with_reducible apply gkb_receiveIpc)

theorem gkb_tcbNtfnAppend (tptr ntfnPtr : ObjRef) : GKB (tcbNtfnAppend (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnAppend; gkb_auto
macro_rules | `(tactic| gkb_leaf) => `(tactic| with_reducible apply gkb_tcbNtfnAppend)

theorem gkb_receiveSignalBlocked (thread ntfnptr : ObjRef) (isBlocking : Bool) : GKB (receiveSignalBlocked (Z := Unit) thread ntfnptr isBlocking) := by
  unfold receiveSignalBlocked; gkb_auto
macro_rules | `(tactic| gkb_leaf) => `(tactic| with_reducible apply gkb_receiveSignalBlocked)

theorem gkb_receiveSignal (thread : ObjRef) (cap : Cap) (isBlocking : Bool) : GKB (receiveSignal (Z := Unit) thread cap isBlocking) := by
  unfold receiveSignal; gkb_auto
macro_rules | `(tactic| gkb_leaf) => `(tactic| with_reducible apply gkb_receiveSignal)

theorem gkb_handleRecv (isBlocking canReply : Bool) : GKB (handleRecv (Z := Unit) isBlocking canReply) := by
  unfold handleRecv; gkb_auto
macro_rules | `(tactic| gkb_leaf) => `(tactic| with_reducible apply gkb_handleRecv)

theorem gkb_handleYield  : GKB (handleYield (Z := Unit)) := by
  unfold handleYield; gkb_auto
macro_rules | `(tactic| gkb_leaf) => `(tactic| with_reducible apply gkb_handleYield)

theorem gkb_fl4HandleSyscall (rep : Bool) (x0 : Syscall) : GKBE (fl4HandleSyscall (Z := Unit) rep x0) := by
  unfold fl4HandleSyscall; gkb_auto
macro_rules | `(tactic| gkb_leaf) => `(tactic| with_reducible apply gkb_fl4HandleSyscall)

theorem gkb_fl4SyscallFaultIP (thread : ObjRef) : GKB (fl4SyscallFaultIP (Z := Unit) thread) := by
  unfold fl4SyscallFaultIP; gkb_auto
macro_rules | `(tactic| gkb_leaf) => `(tactic| with_reducible apply gkb_fl4SyscallFaultIP)

theorem gkb_handleReservedIrq (_irq : Irq) : GKB (handleReservedIrq (Z := Unit) _irq) := by
  unfold handleReservedIrq; gkb_auto
macro_rules | `(tactic| gkb_leaf) => `(tactic| with_reducible apply gkb_handleReservedIrq)

theorem gkb_handleInterrupt (irq : Irq) : GKB (handleInterrupt (Z := Unit) irq) := by
  unfold handleInterrupt; gkb_auto
macro_rules | `(tactic| gkb_leaf) => `(tactic| with_reducible apply gkb_handleInterrupt)

theorem gkb_handleSpuriousIrq  : GKB (handleSpuriousIrq (Z := Unit)) := by
  unfold handleSpuriousIrq; gkb_auto
macro_rules | `(tactic| gkb_leaf) => `(tactic| with_reducible apply gkb_handleSpuriousIrq)

theorem gkb_maybeHandleInterrupt (inKernel : Bool) : GKB (maybeHandleInterrupt (Z := Unit) inKernel) := by
  unfold maybeHandleInterrupt; gkb_auto
macro_rules | `(tactic| gkb_leaf) => `(tactic| with_reducible apply gkb_maybeHandleInterrupt)

theorem gkb_preemptionPath  : GKB (preemptionPath (Z := Unit)) := by
  unfold preemptionPath; gkb_auto
macro_rules | `(tactic| gkb_leaf) => `(tactic| with_reducible apply gkb_preemptionPath)

/-- The syscall event of FL4's `handle_event`. -/
theorem gkb_fl4HandleEvent_sys (rep : Bool) (c : Syscall) :
    GKBE (fl4HandleEvent (Z := Unit) rep (.syscallEvent c)) := by
  unfold fl4HandleEvent; gkb_auto

/-- The interrupt event (l4v's `handle_event Interrupt`). -/
theorem gkb_fl4HandleEvent_irq (rep : Bool) : GKBE (fl4HandleEvent (Z := Unit) rep .interrupt) := by
  unfold fl4HandleEvent handleEvent; gkb_auto

/-- FL4's `call_kernel` from the syscall event. -/
theorem gkb_fl4CallKernel_sys (rep : Bool) (c : Syscall) : GKB (fl4CallKernel (Z := Unit) rep (.syscallEvent c)) := by
  unfold fl4CallKernel
  exact gkb_bind (gkbe_handleE (gkb_fl4HandleEvent_sys rep c) fun _ => gkbe_withoutPreemption gkb_preemptionPath)
    fun _ => gkb_bind gkb_fl4Awaken fun _ => gkb_bind gkb_schedule fun _ => gkb_activateThread

/-- FL4's `call_kernel` from the interrupt event. -/
theorem gkb_fl4CallKernel_irq (rep : Bool) : GKB (fl4CallKernel (Z := Unit) rep .interrupt) := by
  unfold fl4CallKernel
  exact gkb_bind (gkbe_handleE (gkb_fl4HandleEvent_irq rep) fun _ => gkbe_withoutPreemption gkb_preemptionPath)
    fun _ => gkb_bind gkb_fl4Awaken fun _ => gkb_bind gkb_schedule fun _ => gkb_activateThread

/-- **The syscall entry keeps every `GKB` predicate.** -/
theorem gkb_fl4KernelEntrySyscall (rep : Bool) (c : Syscall) :
    GKB (fl4KernelEntrySyscall (Z := Unit) rep c) := by
  unfold fl4KernelEntrySyscall
  exact gkb_bind (gkb_gets _) fun ct => gkb_bind (gkb_fl4SyscallFaultIP ct) fun _ => gkb_fl4CallKernel_sys rep c

end

