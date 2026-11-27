/-
P3 (line irqfix, gen 2): **`IrqCapBound` (l4v `valid_cap` for IRQ handler caps) across every kernel entry**
(spec side only; outside the `JAtZ` cone).

* The decode's carry (l4v: `decode_irq_control_invocation` / `arch_decode_irq_control_invocation` return an
  issue only for a line their range check bounded): `okb_fl4ArchCheckIrq` (FL4's `arch_check_irq`: the ISA
  line `≤ 15`), `okb_decodeFl4IrqControl` (the ISA line `≤ 15`, the IOAPIC / MSI / remapped IOAPIC lines
  `preIrq + minUserIRQ ≤ maxUserIRQ = 123`), `okb_fl4Decode`: every decoded invocation is `InvB`.
* `gkb_syscallD`: the syscall shell when the perform needs a fact of the decode's result;
  `gkb_fl4HandleInvocationR`, then (invB's generated list, renamed) the syscalls, every event
  (`gkb_fl4CallKernel`: all six), the syscall entry.
* Tops: **`kentry_irqStB`**, **`kcall_irqStB`**, `fip_irqStB`, `budget_irqStB`, `evOut_irqStB`: `IrqStB` across
  the syscall entry, every `fl4CallKernel` event, the FaultIP write, the budget front, `EvOut`.
  **`kentry_irqCapBound`** / **`kcall_irqCapBound`**: `IrqCapBound` at every outcome, with
  `ValidIrqMasks ∧ ValidIrqHandlers ∧ IrqStB` at the start (`ValidIrqHandlers` by vih3's `kentry_vih` /
  `kirq_vih` / `vi_fl4CallKernel`). `IrqCapBound` alone is not proved inductive: its preservation goes
  through `IrqStB` (the IRQ states the handler caps point to).
No premises, no sorry.
-/
import Fl4Proofs.P3.SpecInvIrqBoundGen
import Fl4Proofs.P3.SpecInvValidIrqHandlersS

open Classical

namespace Fl4Proofs.P3.SInvIB
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.Vs Fl4Proofs.P3.MachF Fl4Proofs.P3.MachT Fl4Proofs.P3.SInvV
open Fl4Proofs.P3.SInvDom

noncomputable section

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

/-! ## The decode's bound -/

theorem irq_isa_le {w : Data} (h : w ≤ 15) : (ucast 8 w : Irq) ≤ maxIRQ := by
  have h1 : w.toNat ≤ 15 := h
  have h2 : (ucast 8 w : Irq).toNat = w.toNat % 256 := by
    simp only [ucast, BitVec.toNat_setWidth, Nat.reducePow]
  have h3 : maxIRQ.toNat = 125 := rfl
  rw [BitVec.le_def, h2, h3]
  omega

theorem irq_user_le {w : Data} (h : ¬ w > ucast 64 (maxUserIRQ - minUserIRQ)) :
    IRQ (ucast 8 w + minUserIRQ) ≤ maxIRQ := by
  have e : (ucast 64 (maxUserIRQ - minUserIRQ) : Data) = 107 := rfl
  rw [e] at h
  have h1 : w.toNat ≤ 107 := BitVec.not_lt.1 h
  have h3 : maxIRQ.toNat = 125 := rfl
  have h16 : (minUserIRQ : Irq).toNat = 16 := rfl
  rw [BitVec.le_def, h3]
  simp only [IRQ, ucast, BitVec.toNat_add, BitVec.toNat_setWidth, h16, Nat.reducePow]
  omega

/-- FL4's `arch_check_irq`: an `.ok` outcome has the line `≤ 15`. -/
theorem okb_fl4ArchCheckIrq (w : Data) (σ : State Unit) :
    OkDAt σ (fun _ (_ : Unit) => w ≤ 15) (fl4ArchCheckIrq (Z := Unit) w) := by
  unfold fl4ArchCheckIrq
  refine okdAt_bind fun n s _ => ?_
  split
  · intro a s' h
    unfold NonDetE.whenE at h
    split at h
    · have e := Set.mem_singleton_iff.1 h; simp at e
    · rename_i hc; exact BitVec.not_lt.1 hc
  · exact okdAt_throw _

macro "okb_walk" : tactic => `(tactic| repeat' (first
  | exact okdAt_throw _
  | exact okdAt_returnOk (irq_user_le (by assumption))
  | exact okdAt_returnOk (irq_isa_le (by assumption))
  | (refine okdAt_whenE_bind _ _ fun _ => ?_)
  | (refine okdAt_bind fun _ _ _ => ?_)
  | split
  | (dsimp only)))

set_option maxHeartbeats 4000000 in
/-- **FL4's IRQ control decode bounds the issued line.** -/
theorem okb_decodeFl4IrqControl (remapped : Bool) (label : Data) (args : List Data) (srcSlot : CslotPtr)
    (cps : List Cap) (σ : State Unit) :
    OkDAt σ (fun _ i => FIcB i) (decodeFl4IrqControl (Z := Unit) remapped label args srcSlot cps) := by
  unfold decodeFl4IrqControl
  split
  · unfold decodeIrqControlRemapped
    okb_walk
  · refine okdAt_liftME ?_
    unfold decodeIrqControlInvocationWith
    split
    · split
      · dsimp only
        refine okdAt_bind fun _ s h => ?_
        have hb := okb_fl4ArchCheckIrq _ σ _ s h
        okb_walk
      · exact okdAt_throw _
    · refine okdAt_liftME ?_
      unfold archDecodeIrqControlInvocation
      okb_walk

set_option maxHeartbeats 4000000 in
/-- **Every decoded invocation is `InvB`.** -/
theorem okb_fl4Decode (fp : Bool) (label : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr) (cap : Cap)
    (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) (σ : State Unit) :
    OkDAt σ (fun _ inv => InvB inv) (fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex buf) := by
  unfold fl4DecodeInvocation
  split
  all_goals try unfold fl4DecodeTcbInvocation
  all_goals repeat' (first
    | exact okdAt_throw _
    | exact okdAt_returnOk trivial
    | exact okdAt_liftME (okb_decodeFl4IrqControl _ _ _ _ _ _)
    | exact okdAt_liftME (fun _ _ _ => trivial)
    | (apply okdAt_ite)
    | (refine okdAt_bind fun _ _ _ => ?_)
    | split)

/-! ## The invocation shell -/

theorem gkbe_bind_dep {ε α γ : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε γ}
    {Q : α → Prop} (hm : GKBE m)
    (hq : ∀ σ a s, ((.ok a, s) : Except ε α × State Unit) ∈ (m.run σ).1 → Q a)
    (hg : ∀ a, Q a → GKBE (g a)) : GKBE (m >>= g) := by
  unfold GKBE; rw [ExceptT.run_bind]
  intro P L σ h x ⟨y, hy, hx⟩
  obtain ⟨r, s⟩ := y
  have hs : P s := hm P L σ h _ hy
  cases r with
  | ok a => exact hg a (hq σ a s hy) P L s hs x hx
  | error e => exact gkb_pure _ P L s hs x hx

/-- The syscall shell (invB's `gk_syscall`) when the perform needs a fact `Q` of the decode's result. -/
theorem gkb_syscallD {α β γ : Type} {mF : FMonad Unit α} {hF : Fault → SMonad Unit γ}
    {mE : α → SEMonad Unit β} {hE : SyscallError → SMonad Unit γ} {mFin : β → PMonad Unit γ} (Q : β → Prop)
    (h1 : GKBE mF) (h2 : ∀ f, GKB (hF f)) (h3 : ∀ a, GKBE (mE a))
    (hq : ∀ a σ b s, ((.ok b, s) : Except SyscallError β × State Unit) ∈ ((mE a).run σ).1 → Q b)
    (h4 : ∀ e, GKB (hE e)) (h5 : ∀ b, Q b → GKBE (mFin b)) : GKBE (syscall (Z := Unit) mF hF mE hE mFin) := by
  unfold syscall
  refine gkbe_bind (gkbe_withoutPreemption h1) fun r => ?_
  cases r with
  | error f => exact gkbe_withoutPreemption (h2 f)
  | ok a =>
    refine gkbe_bind_dep (Q := fun r => ∀ b, r = .ok b → Q b) (gkbe_withoutPreemption (h3 a)) ?_ fun r hr => ?_
    · intro σ r s h b e
      subst e
      unfold withoutPreemption at h
      obtain ⟨w, hw, e⟩ := mem_liftE_inv' h
      obtain ⟨r', s'⟩ := w
      simp only [Prod.mk.injEq, Except.ok.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact hq a σ b s hw
    · cases r with
      | error e => exact gkbe_withoutPreemption (h4 e)
      | ok b => exact h5 b (hr b rfl)

set_option maxHeartbeats 8000000 in
/-- **The invocation keeps every `GKB` predicate** (the decode's `InvB` carried to the perform). -/
theorem gkb_fl4HandleInvocationR (reportError : Bool) (calling blocking canDonate firstPhase : Bool)
    (cptr : CapRef) :
    GKBE (fl4HandleInvocationR (Z := Unit) reportError calling blocking canDonate firstPhase cptr) := by
  unfold fl4HandleInvocationR
  refine gkbe_bind (by gkb_auto) fun thread => gkbe_bind (by gkb_auto) fun info => ?_
  refine gkb_syscallD InvB (by gkb_auto) (fun _ => by gkb_auto) (fun _ => by gkb_auto) ?_ (fun _ => by gkb_auto) ?_
  · rintro ⟨sl, cap, ex, buf⟩ σ b s h
    try dsimp only at h
    exact okdAt_bind (fun _ s1 _ => okb_fl4Decode _ _ _ _ _ _ _ _ s1) b s h
  · intro oper hb
    exact gkbe_bind (by gkb_auto) fun _ =>
      gkbe_bind (gkb_fl4PerformInvocation _ _ _ _ hb) fun _ => by gkb_auto

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


/-! ## The events and the entry -/

/-- The VM fault handler (as SInvAllV's `gk_handleVmFault`): the fault address, a register read, a throw. -/
theorem gkb_handleVmFault (thread : ObjRef) (ft : VMFaultType) : GKBE (handleVmFault (Z := Unit) thread ft) := by
  cases ft <;> (unfold handleVmFault; gkb_auto)

macro_rules | `(tactic| gkb_leaf) => `(tactic| with_reducible apply gkb_handleVmFault)

theorem gkb_handleEvent_other (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) : GKBE (handleEvent (Z := Unit) ev) := by
  cases ev with
  | syscallEvent c => exact absurd rfl (h c)
  | _ => simp only [handleEvent]; gkb_auto

theorem gkb_fl4HandleEvent (rep : Bool) (ev : Event) : GKBE (fl4HandleEvent (Z := Unit) rep ev) := by
  by_cases h : ∃ c, ev = .syscallEvent c
  · obtain ⟨c, rfl⟩ := h
    exact gkb_fl4HandleEvent_sys rep c
  · rw [fl4HandleEvent_other rep ev fun c e => h ⟨c, e⟩]
    exact gkb_handleEvent_other ev fun c e => h ⟨c, e⟩

/-- **FL4's `call_kernel` keeps every `GKB` predicate, for every event.** -/
theorem gkb_fl4CallKernel (rep : Bool) (ev : Event) : GKB (fl4CallKernel (Z := Unit) rep ev) := by
  unfold fl4CallKernel
  exact gkb_bind (gkbe_handleE (gkb_fl4HandleEvent rep ev) fun _ => gkbe_withoutPreemption gkb_preemptionPath)
    fun _ => gkb_bind gkb_fl4Awaken fun _ => gkb_bind gkb_schedule fun _ => gkb_activateThread

/-- **The syscall entry keeps every `GKB` predicate.** -/
theorem gkb_fl4KernelEntrySyscall (rep : Bool) (c : Syscall) :
    GKB (fl4KernelEntrySyscall (Z := Unit) rep c) := by
  unfold fl4KernelEntrySyscall
  exact gkb_bind (gkb_gets _) fun ct => gkb_bind (gkb_fl4SyscallFaultIP ct) fun _ => gkb_fl4CallKernel rep _

/-- The budget front (`specBudget`: `update_time_stamp` then `check_budget_restart`). -/
theorem gkb_budget : GKB (updateTimeStamp (Z := Unit) >>= fun _ => checkBudgetRestart (Z := Unit)) := by
  gkb_auto

/-! ## Tops -/

/-- **`IrqStB` across a syscall entry.** -/
theorem kentry_irqStB (rep : Bool) (c : Syscall) {σ : State Unit} (h : IrqStB σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) rep c) σ).1, IrqStB y.2 :=
  gkb_fl4KernelEntrySyscall rep c _ wlb_irqStB σ h

/-- **`IrqStB` across every kernel event.** -/
theorem kcall_irqStB (rep : Bool) (ev : Event) {σ : State Unit} (h : IrqStB σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, IrqStB y.2 :=
  gkb_fl4CallKernel rep ev _ wlb_irqStB σ h

/-- `IrqStB` across the FaultIP write. -/
theorem fip_irqStB (t : ObjRef) {σ : State Unit} (h : IrqStB σ) :
    ∀ y ∈ (fl4SyscallFaultIP (Z := Unit) t σ).1, IrqStB y.2 :=
  gkb_fl4SyscallFaultIP t _ wlb_irqStB σ h

/-- `IrqStB` across the budget front. -/
theorem budget_irqStB {σ : State Unit} (h : IrqStB σ) :
    ∀ y ∈ ((updateTimeStamp (Z := Unit) >>= fun _ => checkBudgetRestart (Z := Unit)) σ).1, IrqStB y.2 :=
  gkb_budget _ wlb_irqStB σ h

/-- **`IrqCapBound` at every outcome of a syscall entry.** -/
theorem kentry_irqCapBound {c : Syscall} {σ : State Unit} (hm : ValidIrqMasks σ) (hh : ValidIrqHandlers σ)
    (hb : IrqStB σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, IrqCapBound y.2 ∧ IrqStB y.2 :=
  fun y hy => let e := kentry_irqStB true c hb y hy; ⟨irqCapBound_of (kentry_vih hm hh y hy) e, e⟩

/-- **`IrqCapBound` at every outcome of every kernel event.** -/
theorem kcall_irqCapBound (rep : Bool) (ev : Event) {σ : State Unit} (hm : ValidIrqMasks σ)
    (hh : ValidIrqHandlers σ) (hb : IrqStB σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, IrqCapBound y.2 ∧ IrqStB y.2 :=
  fun y hy => let e := kcall_irqStB rep ev hb y hy
    ⟨irqCapBound_of (vi_fl4CallKernel rep ev σ ⟨hm, hh, trivial⟩ y hy).2.1 e, e⟩

/-- `IrqCapBound` at boot (`initASt`). -/
theorem boot_irqCapBound : IrqCapBound (initASt (Z := Unit)) := irqCapBound_of boot_vih boot_irqStB

end

end Fl4Proofs.P3.SInvIB
