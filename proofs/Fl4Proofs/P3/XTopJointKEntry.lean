/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN.md sch7 (D), item 12):
**`kernel_entryJ`: FL4's `handle_syscall` for a native system call against
Fl4Spec's `fl4KernelEntrySyscall true c`** (Ext/Entry: the `FaultIP` write,
`fl4HandleEvent` (time stamp, budget check, FL4's dispatcher), the preemption
path, `fl4Awaken`, `schedule`, `activateThread`).

Composition (FL4 side in order):
* `FAULT_IP := NEXT_IP - 2` (M1): `reg_wr_irel` + `JAtZ.regWrJ`, spec side
  `fl4SyscallFaultIP_eq` (`faultIPSt`).
* the trap flag (M2, out of scope: `hflag` [S]) and the number range
  (`NativeSys.range`: the native numbers are in [SYSCALL_MIN, SYSCALL_MAX]).
* `budget_ok`: `JAtZ.budgetOkJ` (runs) with `JAtZ.budgetOkF` (stops, no
  timeout-fault send) or `JAtZ.budgetOkT` (stops, the timeout fault blocks the
  current thread) (`KBudget`).
* `dispatch_syscall` (`dispatch_allJ`): `dispatch_invokeJEPZJ` (Send/NBSend/
  Call, preemption to `PPQ`), `dispatch_recvJL` (Recv/NBRecv/Wait/NBWait),
  `dispatch_yieldJ` (Yield); ReplyRecv/NBSendRecv/NBSendWait: `KDispHyps.mid`
  [W] (M6: the receive at the mid state; sch7 (C) step 2 not done).
* `finish`: `jat_finishJ2` from the `JAtZ` after the dispatch or the stopping
  budget check (`KFinAt` at those states); after a preemption `KPreFinHyp`
  [W] (`after_invocation`'s post `PPQ` is `JHoleAt`/`XTopAt`, not `JAt`).

Spec side: `specFront c σ` (the `FaultIP` write then the handled event),
`mem_kentry` (an outcome of `specFront` then of `fl4Awaken; schedule;
activateThread` is an outcome of `fl4KernelEntrySyscall true c`),
`fail_kentry` (a failing preemption path fails the whole entry).

Premises at intermediate states are stated at the spec-reachable ones only
(`BudgetAt`, `specFront`, `PreemptedAt`), never at every `JAt` state.
-/
import Fl4Proofs.P3.XTopJointMidRun
import Fl4Proofs.P3.XTopJointSchedRF3
import Fl4Proofs.P3.XTopJointPreemptI
import Fl4Proofs.P3.XTopJointRecvIpcLink
import Fl4Proofs.P3.XTopJointYieldSys
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-! ## Spec side -/

section Spec
open Fl4Spec

theorem mem_bind_elim {σs α β : Type} {m : NonDet σs α} {f : α → NonDet σs β} {s : σs} {y : β × σs}
    (h : y ∈ ((m >>= f) s).1) : ∃ x ∈ (m s).1, y ∈ (f x.1 x.2).1 := h

theorem mem_handleE_ok {σs ε ε' α : Type} {m : NonDetE σs ε α} {h : ε → NonDetE σs ε' α} {s s' : σs} {a : α}
    (hx : (.ok a, s') ∈ (m.run s).1) :
    ((.ok a, s') : Except ε' α × σs) ∈ ((NonDetE.handleE m h).run s).1 :=
  mem_bind_nd (m := ExceptT.run m) (x := ((.ok a : Except ε α), s')) hx rfl

theorem mem_handleE_err {σs ε ε' α : Type} {m : NonDetE σs ε α} {h : ε → NonDetE σs ε' α} {s s' : σs} {e : ε}
    {y : Except ε' α × σs} (hx : (.error e, s') ∈ (m.run s).1) (hy : y ∈ ((h e).run s').1) :
    y ∈ ((NonDetE.handleE m h).run s).1 :=
  mem_bind_nd (m := ExceptT.run m) (x := ((.error e : Except ε α), s')) hx hy

/-- The spec's time stamp and budget check (`fl4HandleEvent`'s first two
statements, as `JAtZ.budgetOkJ` states them). -/
def specBudget (σ : State Unit) : Set (Bool × State Unit) × Prop :=
  (updateTimeStamp (Z := Unit) >>= fun _ => checkBudgetRestart) σ

/-- The `FaultIP` write then the handled event: what `fl4CallKernel` runs
before `fl4Awaken`. -/
def specFront (c : Syscall) (σ : State Unit) : Set (Except Unit Unit × State Unit) × Prop :=
  (fl4SyscallFaultIP (Z := Unit) σ.curThread >>= fun _ =>
    ExceptT.run (NonDetE.handleE (fl4HandleEvent true (.syscallEvent c))
      (fun _ => withoutPreemption preemptionPath))) σ

/-- The spec's `FaultIP` write as a state. -/
def faultIPSt (σ : State Unit) (t : ObjRef) (x : Tcb) : State Unit :=
  updK σ t (.tcb (setReg x .faultIP (x.tcbArch.tcbContext.userRegs .nextIP - 2)))

theorem fl4SyscallFaultIP_eq {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x)) :
    fl4SyscallFaultIP (Z := Unit) t σ = ({((), faultIPSt σ t x)}, False) := by
  unfold fl4SyscallFaultIP asUser
  show (NonDet.getsThe _ >>= _) σ = _
  rw [nd_bind_one (getTcb_eq hk)]
  show ((pure _ : NonDet (State Unit) UserContext) >>= _) σ = _
  rw [nd_pure_bind']
  show (NonDet.selectF _ >>= _) σ = _
  rw [nd_bind_one (show NonDet.selectF (σ := State Unit) ((NonDet.bind (getRegister nextInstructionRegister)
      fun n => setRegister faultRegister (n - 2)) (archTcbContextGet x.tcbArch)) σ =
      ({(((), ⟨(archTcbContextGet x.tcbArch).userFpuState,
        Function.update (archTcbContextGet x.tcbArch).userRegs .faultIP
          ((archTcbContextGet x.tcbArch).userRegs .nextIP - 2)⟩), σ)}, False) by
    simp only [NonDet.selectF, NonDet.bind, getRegister, setRegister, NonDet.gets, NonDet.modify,
      nextInstructionRegister, faultRegister]
    ext ⟨a, b⟩ <;> simp)]
  show ((pure _ : NonDet (State Unit) Tcb) >>= _) σ = _
  rw [nd_pure_bind']
  exact (nd_bind_one (setObject_eq (o' := KernelObject.tcb (setReg x .faultIP
    (x.tcbArch.tcbContext.userRegs .nextIP - 2))) hk rfl) _).trans rfl

/-- The handled event from a budget outcome. -/
theorem mem_fl4HandleEvent {σ0 σb : State Unit} {b : Bool} {c : Syscall}
    (hb : (b, σb) ∈ (specBudget σ0).1) {y : Except Unit Unit × State Unit}
    (hy : y ∈ ((NonDetE.whenE (b = true) (fl4HandleSyscall (Z := Unit) true c)).run σb).1) :
    y ∈ ((fl4HandleEvent (Z := Unit) true (.syscallEvent c)).run σ0).1 := by
  obtain ⟨u, hu, hr⟩ := mem_bind_elim hb
  unfold fl4HandleEvent
  exact mem_bindE_ok (mem_liftE hu) (mem_bindE_ok (mem_liftE hr) hy)

theorem mem_whenE_true {σs ε : Type} {m : NonDetE σs ε Unit} {s : σs} {y : Except ε Unit × σs}
    (h : y ∈ (m.run s).1) : y ∈ ((NonDetE.whenE (true = true) m).run s).1 := by
  unfold NonDetE.whenE; rw [if_pos rfl]; exact h

theorem mem_whenE_false {σs ε : Type} {m : NonDetE σs ε Unit} {s : σs} :
    ((.ok (), s) : Except ε Unit × σs) ∈ ((NonDetE.whenE (false = true) m).run s).1 := by
  unfold NonDetE.whenE; rw [if_neg (by decide)]; rfl

theorem mem_specFront {σ σ0 : State Unit} {c : Syscall} (hF : ((), σ0) ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1)
    {x : Except Unit Unit × State Unit}
    (hx : x ∈ ((NonDetE.handleE (fl4HandleEvent (Z := Unit) true (.syscallEvent c))
      (fun _ => withoutPreemption preemptionPath)).run σ0).1) : x ∈ (specFront c σ).1 :=
  mem_bind_nd hF hx

/-- **An outcome of `specFront` then of `fl4Awaken; schedule;
activateThread` is an outcome of the syscall entry.** -/
theorem mem_kentry {σ σ' : State Unit} {c : Syscall} {x : Except Unit Unit × State Unit}
    (hx : x ∈ (specFront c σ).1)
    (hT : ((), σ') ∈ ((fl4Awaken (Z := Unit) >>= fun _ => schedule >>= fun _ => activateThread) x.2).1) :
    ((), σ') ∈ (fl4KernelEntrySyscall (Z := Unit) true c σ).1 := by
  obtain ⟨u, hu, hh⟩ := mem_bind_elim hx
  unfold fl4KernelEntrySyscall fl4CallKernel
  exact mem_bind_nd (x := (σ.curThread, σ)) rfl (mem_bind_nd hu (mem_bind_nd hh hT))

end Spec

/-! ## Native system calls -/

/-- ReplyRecv / NBSendRecv / NBSendWait (invocation, then a receive). -/
def MidSys (n : I64) (c : Fl4Spec.Syscall) : Prop :=
  (n = fl4_abi.syscall.SysReplyRecv ∧ c = .sysReplyRecv) ∨
  (n = fl4_abi.syscall.SysNBSendRecv ∧ c = .sysNBSendRecv) ∨
  (n = fl4_abi.syscall.SysNBSendWait ∧ c = .sysNBSendWait)

/-- **FL4's native system call numbers and their spec `Syscall`** (M2: the
debug / TLS numbers and unknown numbers are out of scope). -/
def NativeSys (n : I64) (c : Fl4Spec.Syscall) : Prop :=
  (∃ call bl don, InvSys n call bl don ∧ c = invSysOf call bl) ∨
  (∃ bl cr, RecvSys n bl cr ∧ c = recvSysOf bl cr) ∨
  (n = fl4_abi.syscall.SysYield ∧ c = .sysYield) ∨ MidSys n c

theorem NativeSys.num {n : I64} {c : Fl4Spec.Syscall} (h : NativeSys n c) :
    n = fl4_abi.syscall.SysCall ∨ n = fl4_abi.syscall.SysReplyRecv ∨ n = fl4_abi.syscall.SysNBSendRecv ∨
    n = fl4_abi.syscall.SysNBSendWait ∨ n = fl4_abi.syscall.SysSend ∨ n = fl4_abi.syscall.SysNBSend ∨
    n = fl4_abi.syscall.SysRecv ∨ n = fl4_abi.syscall.SysNBRecv ∨ n = fl4_abi.syscall.SysWait ∨
    n = fl4_abi.syscall.SysNBWait ∨ n = fl4_abi.syscall.SysYield := by
  rcases h with ⟨_, _, _, h, -⟩ | ⟨_, _, h, -⟩ | ⟨h, -⟩ | h
  · rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
  · rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
  · simp [h]
  · rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]

/-- The native numbers are in `[SYSCALL_MIN, SYSCALL_MAX]`. -/
theorem NativeSys.range {n : I64} {c : Fl4Spec.Syscall} (h : NativeSys n c) :
    ¬ n < fl4_abi.syscall.SYSCALL_MIN ∧ ¬ n > fl4_abi.syscall.SYSCALL_MAX := by
  rcases h.num with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
    (simp only [fl4_abi.syscall.SYSCALL_MIN, fl4_abi.syscall.SYSCALL_MAX, fl4_abi.syscall.SysCall,
      fl4_abi.syscall.SysReplyRecv, fl4_abi.syscall.SysNBSendRecv, fl4_abi.syscall.SysNBSendWait,
      fl4_abi.syscall.SysSend, fl4_abi.syscall.SysNBSend, fl4_abi.syscall.SysRecv, fl4_abi.syscall.SysNBRecv,
      fl4_abi.syscall.SysWait, fl4_abi.syscall.SysNBWait, fl4_abi.syscall.SysYield]) <;> decide

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- The budget outcomes the spec reaches after the `FaultIP` write. -/
def BudgetAt (σ σb : Fl4Spec.State Unit) (b : Bool) : Prop :=
  ∃ σ0, ((), σ0) ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1 ∧ (b, σb) ∈ (specBudget σ0).1

/-- The preempted invocation outcomes the spec reaches. -/
def PreemptedAt (c : Fl4Spec.Syscall) (σ σ1 : Fl4Spec.State Unit) : Prop :=
  ∃ σb, BudgetAt σ σb true ∧ (.error (), σ1) ∈ ((Fl4Spec.fl4HandleSyscall (Z := Unit) true c).run σb).1

/-- **The budget-check premises at the entry state after the `FaultIP`
write** (`JAtZ.budgetOkJ` / `budgetOkF` / `budgetOkT`): the clock [P]
`NowAgree`, `CurInv` and `OffReady` [J] (ScEntryRd's `budget_ok_offReady`;
the write changes one register, which neither reads), and either no
timeout-fault send (`NoTmoSend`) or the premises of the blocking timeout
fault (`budgetOkT`: the current thread in no ready queue (l4v
`ct_not_in_q`), running or restarting, its endpoint handler can block it,
a non-round-robin SC). -/
structure KBudget (a : A) (σ0 : Fl4Spec.State Unit) : Prop where
  now : NowAgree arI a σ0
  cur : CurInv σ0
  off : OffReady σ0
  tmo : NoTmoSend σ0 ∨ ((∀ d p, σ0.curThread ∉ σ0.readyQueues d p) ∧ ∃ xt, σ0.kheap σ0.curThread = some (.tcb xt) ∧
    (xt.tcbState = .running ∨ xt.tcbState = .restart) ∧ ∃ (p bd : Fl4Spec.Word) (r : Fl4Spec.CapRights),
      xt.tcbTimeoutHandler = .endpointCap p bd r ∧
      (∀ x n, σ0.kheap σ0.curSc = some (.schedContext x n) → x.scPeriod ≠ 0) ∧
      (∀ xe, σ0.kheap p = some (.endpoint xe) → Endp.CanBlock false xe))

/-- What the entry ends in: the spec entry fails, or one of its outcomes is
related (`RJ`). -/
def KPost (AR : A → Fl4Spec.Cr3 → Prop) (c : Fl4Spec.Syscall) (σ : Fl4Spec.State Unit) (r : S × A) : Prop :=
  (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).2 ∨
  ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧ RJ (L := L) arI AR r.1 r.2 σ'

variable {arI}

end

end

end Fl4Proofs.P3
