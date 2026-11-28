/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN sch13): **`kernel_entryJ8`: the
ReplyRecv / NBSendRecv / NBSendWait dispatch shell proved, the preemption path
without named premises, `KPreFinRestHypI` gone.**

* `MidSysR`: the three numbers with FL4's cap register, the spec's register
  and the receive's can-reply flag; `fl4HandleSyscall_mid` (the spec branch:
  the register read, `fl4HandleInvocationR true false false true true`, then
  `withoutPreemption (handleRecv true cr)`).
* `JMidRecvHyp` [W] (narrows `KDispHypsRI.mid`, which named the whole
  dispatch): only the receive after a successful first phase, at a `JMid`
  state (l4v `invs and ct_active`) that is an `.ok` outcome of the invocation
  from the dispatch state (on the path, not ∀ states). l4v
  `handle_recv_corres` at the mid state (`handleReplyRecv`'s second half).
  Removal: sch12 (2) (i)–(iii) (hnq/hvfh at the mid state by a frame, the
  receive leaves from `MidE` without `Entered`, the blocking leaves ending in
  `JAtZR` under a pending switch).
* `mid_invRecvJ` / `dispatch_midJ`: `handle_invocation_entryJ` with
  `HIPostMXP.mid` (`JMidPerfHyp` [W] as sch12, `MidEntry` from `Entered` and
  `JEntryAt.cnf` at the dispatch state, i.e. the entry's own [J] fact),
  `after_invocation`: `Ok` → the receive (`JMidRecvHyp`), `Err` → the
  preemption path (`hPre_ofZQI`, ending in `PPQJI`).
* `KDispHyps8` (`inv`, `recv` as before; `mid`: the entry facts JEntryGlob /
  JEntryAt / JPathAt for the mid invocation's flags and cap register, as
  `inv` has them, plus `JMidPerfHyp` and `JMidRecvHyp`), `dispatch_all8`
  (every dispatch ends in `DispPostR` with `PPQJI`), `kPreFinHypJI_of`
  (finish after every preempted dispatch: `PPQJI` has `JAt` after the path,
  so no `RestE` premise), `kernel_entryJ8` = `kernel_entryJ7` with `IrqPlat`
  for `IrqPlatI` (XTopJointIrqPlat), no `hRest` (kp17), no `hPR`
  (`KPreFinRestHypI` deleted: kp17's `RestE` holes end in `PPQJI`,
  XTopJointIrqZJ), `KDispHyps8` for `KDispHypsRI`.
-/
import Fl4Proofs.P3.XTopJointIrqZI
import Fl4Proofs.P3.ScChargeTR
import Fl4Proofs.P3.XTopJointPreemptQ
import Fl4Proofs.P3.XTopJointMidRunS
import Fl4Proofs.P3.XTopJointKEntry6
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-- ReplyRecv / NBSendRecv / NBSendWait with FL4's cap register `rg`, the
spec's register `sr` and the receive's can-reply flag `cr`. -/
def MidSysR (n : I64) (c : Fl4Spec.Syscall) (rg : U64) (sr : Fl4Spec.Register) (cr : Bool) : Prop :=
  (n = fl4_abi.syscall.SysReplyRecv ∧ c = .sysReplyRecv ∧ rg = layout.reg.REPLY ∧
    sr = Fl4Spec.replyRegister ∧ cr = true) ∨
  (n = fl4_abi.syscall.SysNBSendRecv ∧ c = .sysNBSendRecv ∧ rg = layout.reg.NBSEND_RECV_DEST ∧
    sr = Fl4Spec.nbsendRecvDest ∧ cr = true) ∨
  (n = fl4_abi.syscall.SysNBSendWait ∧ c = .sysNBSendWait ∧ rg = layout.reg.REPLY ∧
    sr = Fl4Spec.replyRegister ∧ cr = false)

theorem midSysR_of {n : I64} {c : Fl4Spec.Syscall} (h : MidSys n c) : ∃ rg sr cr, MidSysR n c rg sr cr := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨_, _, _, Or.inl ⟨h1, h2, rfl, rfl, rfl⟩⟩
  · exact ⟨_, _, _, Or.inr (Or.inl ⟨h1, h2, rfl, rfl, rfl⟩)⟩
  · exact ⟨_, _, _, Or.inr (Or.inr ⟨h1, h2, rfl, rfl, rfl⟩)⟩

theorem regIdx_nbsendRecvDest : regIdx Fl4Spec.nbsendRecvDest = layout.reg.NBSEND_RECV_DEST := by
  unfold layout.reg.NBSEND_RECV_DEST layout.reg.R13; rfl

theorem MidSysR.reg {n : I64} {c : Fl4Spec.Syscall} {rg : U64} {sr : Fl4Spec.Register} {cr : Bool}
    (h : MidSysR n c rg sr cr) : regIdx sr = rg := by
  rcases h with ⟨-, -, rfl, rfl, -⟩ | ⟨-, -, rfl, rfl, -⟩ | ⟨-, -, rfl, rfl, -⟩
  · exact regIdx_reply
  · exact regIdx_nbsendRecvDest
  · exact regIdx_reply

/-- The spec's mid syscall branch (`fl4HandleSyscall true`). -/
def DispMid (sr : Fl4Spec.Register) (cr : Bool) : Fl4Spec.PMonad Unit Unit := do
  let cptr ← Fl4Spec.withoutPreemption <| Fl4Spec.getCapReg (Z := Unit) sr
  Fl4Spec.fl4HandleInvocationR (Z := Unit) true false false true true cptr
  Fl4Spec.withoutPreemption <| Fl4Spec.handleRecv (Z := Unit) true cr

theorem fl4HandleSyscall_mid {n : I64} {c : Fl4Spec.Syscall} {rg : U64} {sr : Fl4Spec.Register} {cr : Bool}
    (h : MidSysR n c rg sr cr) : Fl4Spec.fl4HandleSyscall (Z := Unit) true c = DispMid sr cr := by
  rcases h with ⟨-, rfl, -, rfl, rfl⟩ | ⟨-, rfl, -, rfl, rfl⟩ | ⟨-, rfl, -, rfl, rfl⟩ <;> rfl

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **[W] The receive at the mid state** (module docstring): every `.ok`
outcome of the first-phase invocation from `σ`, at every `JMid` FL4 state
related to it. -/
def JMidRecvHyp (AR : A → Fl4Spec.Cr3 → Prop) (cptr : Fl4Spec.CapRef) (cr : Bool) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ y ∈ ((Fl4Spec.fl4HandleInvocationR (Z := Unit) true false false true true cptr).run σ).1, y.1 = .ok () →
    ∀ (s1 : S) (a1 : A), JMid (L := L) arI AR s1 a1 y.2 →
      syscall.handle_recv st arI s1 a1 true cr ⦃ r => ∃ z ∈ (Fl4Spec.handleRecv (Z := Unit) true cr y.2).1,
        RelTopM (L := L) r.1 z.2 ∧ ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
          JAtZR (L := L) arI AR Z H Cs Ac Lst D r.1 r.2 z.2 ∧ VxE Z ⦄

variable {arI}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

end

end

end Fl4Proofs.P3
