/-
P3 (DESIGN.md §9), invariant line G1 (rd8j): **the shell's pieces outside the
JAtZ cone** (spec side only).

rd12b's SpecInvRd12bA / C import rd11's modules, which reach `JointAt`; the
pieces rd8j needs are restated here on top of SpecInvRd12bF (cone-free):
`scO` / `svOf` (`kz_sv`), `kz_trans`, `kz_curThread`, `kz_act`, `kz_cfS`,
`svs_kz`; the shell decomposition `invF` / `invE` / `invFin` / `invPost` with
`fl4HandleInvocationR_eq` (`rfl`), `kz_invF` / `kz_invE`; `mem_handleE_cases`;
`sendArgs` / `srArgs`.
-/
import Fl4Proofs.P3.SpecInvRd12bF
import Fl4Proofs.P3.SpecInvRd8hR
open Classical

namespace Fl4Proofs.P3.SInvR.B8j
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR

noncomputable section

set_option maxHeartbeats 1000000

/-! ## `KZ` facts -/

/-- The SC part of an object. -/
def scO : Option KernelObject → Option (SchedContext × Nat)
  | some (.schedContext y n) => some (y, n)
  | _ => none

theorem scAt_eq (σ : State Unit) (p : ObjRef) : SInvE.scAt σ p = scO (σ.kheap p) := by
  unfold SInvE.scAt scO
  generalize σ.kheap p = o
  rcases o with _ | o
  · rfl
  · cases o <;> rfl

/-- The scheduler view from the two views. -/
def svOf : Option (ThreadState × Option Fault × Option ObjRef) → Option (SchedContext × Nat) →
    Nat × Option ObjRef × List Refill × Nat × Option ObjRef × Nat
  | some (_, _, c), _ => (1, c, [], 0, none, 0)
  | none, some (y, n) => (2, none, y.scRefills, y.scRefillMax, y.scTcb, n)
  | none, none => (0, none, [], 0, none, 0)

theorem sv_eq_svOf (o : Option KernelObject) : SVK.sv o = svOf (B8c.tcbV o) (scO o) := by
  rcases o with _ | o
  · rfl
  · cases o <;> rfl

theorem kz_sv {σ0 s : State Unit} (h : A12b.KZ σ0 s) (p : ObjRef) : SVK.sv (s.kheap p) = SVK.sv (σ0.kheap p) := by
  unfold A12b.KZ A12b.KZv B8c.BKv A12b.CAv at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨⟨h1, h2, -⟩, -, -⟩ := h
  rw [sv_eq_svOf, sv_eq_svOf, congrFun h1 p, ← scAt_eq, ← scAt_eq, h2]

theorem kz_trans {σ0 s s' : State Unit} (h : A12b.KZ σ0 s) (h' : A12b.KZ s s') : A12b.KZ σ0 s' := by
  unfold A12b.KZ at *; rw [h', h]

theorem kz_act {σ0 s : State Unit} (h : A12b.KZ σ0 s) : s.schedulerAction = σ0.schedulerAction :=
  congrArg (fun p => p.2.2) h

theorem kz_time {σ0 s : State Unit} (h : A12b.KZ σ0 s) : s.curTime = σ0.curTime :=
  congrArg (fun p => p.1.2.2) h

theorem kz_cfS {σ0 s : State Unit} (h : A12b.KZ σ0 s) : cfS s = cfS σ0 :=
  congrArg (fun p => p.2.1) h

theorem kz_curThread {σ0 s : State Unit} (h : A12b.KZ σ0 s) : s.curThread = σ0.curThread :=
  congrArg (fun p => p.2.2.1) (kz_cfS h)

theorem svs_kz {σ0 s : State Unit} (h : A12b.KZ σ0 s) : SVK.SVS σ0 s :=
  ⟨fun p => kz_sv h p, kz_time h, Or.inl (kz_act h)⟩

/-! ## The shell's pieces (rd12b's, restated) -/

/-- The lookups (the `syscall` fault phase of `fl4HandleInvocationR`). -/
def invF (thread : ObjRef) (cptr : CapRef) (info : MessageInfo) :
    FMonad Unit (CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef) := do
  let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot thread cptr
  let buffer ← NonDetE.liftE <| lookupIpcBuffer false thread
  let extracaps ← lookupExtraCaps thread buffer info
  NonDetE.returnOk (slot, cap, extracaps, buffer)

/-- `get_mrs` and the decode (the error phase). -/
def invE (firstPhase : Bool) (cptr : CapRef) (thread : ObjRef) (info : MessageInfo) :
    CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef → SEMonad Unit Fl4Invocation :=
  fun (slot, cap, extracaps, buffer) => do
    let args ← NonDetE.liftE <| getMrs thread buffer info
    fl4DecodeInvocation firstPhase info.miLabel args cptr slot cap extracaps buffer

/-- The Restart write, the perform and its post (the finalise phase). -/
def invFin (calling blocking canDonate : Bool) (thread : ObjRef) : Fl4Invocation → PMonad Unit Unit :=
  fun oper => do
    withoutPreemption <| setThreadState thread .restart
    let reply ← fl4PerformInvocation blocking calling canDonate oper
    withoutPreemption <| do
        let state ← getThreadState thread
        match state with
        | .restart => do
          NonDet.when calling <|
            replyFromKernel thread (0, reply)
          setThreadState thread .running
        | _ => return ()

theorem fl4HandleInvocationR_eq (rep calling blocking canDonate firstPhase : Bool) (cptr : CapRef) :
    fl4HandleInvocationR (Z := Unit) rep calling blocking canDonate firstPhase cptr = (do
      let thread ← NonDetE.liftE <| NonDet.gets fun s : State Unit => s.curThread
      let info ← withoutPreemption <| getMessageInfo thread
      syscall (invF thread cptr info) (fun fault => NonDet.when blocking <| handleFault thread fault)
        (invE firstPhase cptr thread info)
        (fun err => NonDet.when calling <| fl4ReplyFromKernelError rep thread <| msgFromSyscallError err)
        (invFin calling blocking canDonate thread)) := rfl

/-- The Restart check, the kernel reply and the Running write after the perform. -/
def invPost (calling : Bool) (thread : ObjRef) (reply : List Data) : SMonad Unit Unit := do
  let state ← getThreadState thread
  match state with
  | .restart => do
    NonDet.when calling <|
      replyFromKernel thread (0, reply)
    setThreadState thread .running
  | _ => return ()

theorem kz_invF {V : State Unit} (t : ObjRef) (cptr : CapRef) (info : MessageInfo) :
    A12b.KZKE V (invF t cptr info) := by
  unfold invF; kz_auto

theorem kz_invE {V : State Unit} (fp : Bool) (cptr : CapRef) (t : ObjRef) (info : MessageInfo)
    (a : CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef) : A12b.KZKE V (invE fp cptr t info a) := by
  obtain ⟨sl, cap, ex, buf⟩ := a
  unfold invE; kz_auto

theorem mem_handleE_cases {α : Type} {m : NonDetE (State Unit) Unit α} {h : Unit → NonDetE (State Unit) Unit α}
    {s : State Unit} {y : Except Unit α × State Unit} (hy : y ∈ (ExceptT.run (NonDetE.handleE m h) s).1) :
    ∃ z ∈ (m.run s).1, (∃ a, z.1 = .ok a ∧ y = (.ok a, z.2)) ∨ (∃ e, z.1 = .error e ∧ y ∈ ((h e).run z.2).1) := by
  unfold NonDetE.handleE at hy
  rw [ExceptT.run_mk] at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨r, s'⟩ := z
  cases r with
  | ok a => exact ⟨_, hz, Or.inl ⟨a, rfl, Set.mem_singleton_iff.1 hy⟩⟩
  | error e => exact ⟨_, hz, Or.inr ⟨e, rfl, hy⟩⟩

/-- The register and flags of a send syscall. -/
def sendArgs : Syscall → Option (Register × Bool × Bool × Bool)
  | .sysSend => some (cap_register, false, true, false)
  | .sysNBSend => some (cap_register, false, false, false)
  | .sysCall => some (cap_register, true, true, true)
  | _ => none

/-- The register and receive flag of a send-receive syscall. -/
def srArgs : Syscall → Option (Register × Bool)
  | .sysReplyRecv => some (replyRegister, true)
  | .sysNBSendRecv => some (nbsendRecvDest, true)
  | .sysNBSendWait => some (replyRegister, false)
  | _ => none

end

end Fl4Proofs.P3.SInvR.B8j
