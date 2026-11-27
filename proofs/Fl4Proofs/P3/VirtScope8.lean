/-
P3x for virtualization (line virt, gen 8, item 1, spec half): **the route scope with the first-phase flag the
syscall actually uses.**

Gen 7's `VirtAgree.ScopeE6 c σ` [S] asks `OffRoute6 fp cptr t` for **every** `fp` at the cap register of the
syscall `c`. The spec runs `fl4HandleInvocationR … fp cptr` with one fixed `fp` per syscall (`fl4HandleSyscall`:
`false` for Send / NBSend / Call, `true` for ReplyRecv / NBSendRecv / NBSendWait). The other `fp` is never decoded,
and it is not harmless to ask it: a ReplyRecv whose reply register names a thread cap with label 88 is a `Route3`
point at `fp = false` (`threadCap _ => ¬ fp ∧ …`), where the ported decoder (`fl4DecodeTcbInvocation`, label 88
unknown) and the extended one (`decodeSetEptRoot`, e.g. `truncatedMessage` without an extra cap) need not agree,
while U36I's per-entry premise `KDispHypsKVU32.mid` only speaks about `fp = true`. So `ScopeE6` is **not** derivable
from the syscall clause's `hK` (gen 8 finding); this module narrows it to the flag the spec uses:

* `sysFp`, `OffRouteS8`, **`ScopeE8`** (`ScopeE6` with `fp := sysFp c`), `offRouteS8_of6`, `scopeE8_of6`
  (the gen 7 scope implies the new one, so nothing proved with `ScopeE6` is lost).
* The syscall-level half of VirtAgree's chain re-proved on `OffRouteS8` (the invocation-level lemmas
  `fl4HandleInvocationV_eqNR6`, `invoke_congr6(0)`, `nr_handleInvocationR6`, `nr_invoke6(0)` are reused, they take
  one `fp`): `fl4HandleSyscallV_eqNR8`, `fl4HandleEventV_syscall8`, `fl4HandleEventV_eqNR8`,
  **`fl4CallKernelV_eqNR8`**, `nr_fl4HandleSyscall8`, `nr_fl4HandleEvent8`, `nr_fl4CallKernel8`,
  **`fl4KernelEntrySyscallV_eqNR8`**, `nr_kentry8`, **`kentryV_post8`**.

Named premises: `hvk : virtKind = .none` [S] (as gen 5–7); `hr : ScopeE8 c σ` [S] (weaker than `ScopeE6`;
VirtScope8J derives it from U36I's syscall clause). No [J]/[P]/[W]. New file only.
-/
import Fl4Proofs.P3.VirtAgree
open Aeneas Aeneas.Std Result
open Classical

namespace Fl4Proofs.P3.VirtScope8
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvV Fl4Proofs.P3.SInvL Fl4Proofs.P3.SInvDom
  Fl4Proofs.P3.SInvTY Fl4Proofs.P3.VirtR7b Fl4Proofs.P3.VirtR7d Fl4Proofs.P3.VirtAwaken Fl4Proofs.P3.VirtR7e Fl4Proofs.P3.VirtR7eK
  Fl4Proofs.P3.VirtR7eK2 Fl4Proofs.P3.VirtNvTcb Fl4Proofs.P3.VirtNvcW Fl4Proofs.P3.VirtOffNv Fl4Proofs.P3.VirtInvOK
  Fl4Proofs.P3.VirtTcbOK Fl4Proofs.P3.VirtNvInv Fl4Proofs.P3.VirtNvK1 Fl4Proofs.P3.VirtTyK7 Fl4Proofs.P3.VirtNvK2
  Fl4Proofs.P3.VirtExtTop Fl4Proofs.P3.VirtAgree

noncomputable section

/-! ## The scope -/

/-- The first-phase flag `fl4HandleSyscall` passes to `fl4HandleInvocationR` (l4v `handle_send` / `handle_call`:
`False`; the reply / send phase of ReplyRecv, NBSendRecv, NBSendWait: `True`). -/
def sysFp : Syscall → Bool
  | .sysReplyRecv => true
  | .sysNBSendRecv => true
  | .sysNBSendWait => true
  | _ => false

/-- **`OffRouteS6` at the syscall's own first-phase flag.** -/
def OffRouteS8 (c : Syscall) (t : State Unit) : Prop :=
  ∀ reg, sysReg c = some reg → ∀ cptr t', (cptr, t') ∈ (getCapReg (Z := Unit) reg t).1 → OffRoute6 (sysFp c) cptr t'

/-- **The syscall entry's scope at the syscall's own flag** ([S], module docstring). -/
def ScopeE8 (c : Syscall) (σ : State Unit) : Prop :=
  ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1, ∀ t, EntryPt w.2 t → OffRouteS8 c t

theorem offRouteS8_of6 {c : Syscall} {t : State Unit} (h : OffRouteS6 c t) : OffRouteS8 c t :=
  fun reg hr cptr t' hm => h reg hr cptr t' hm _

/-- Gen 7's scope implies the new one. -/
theorem scopeE8_of6 {c : Syscall} {σ : State Unit} (h : ScopeE6 c σ) : ScopeE8 c σ :=
  fun w hw t ht => offRouteS8_of6 (h w hw t ht)

/-! ## The chain on the narrowed scope (VirtAgree's syscall-level half, `fp` fixed per syscall) -/

/-- **Every syscall of the extended kernel is the ported one** from an `NR` state in the fp-exact scope. -/
theorem fl4HandleSyscallV_eqNR8 (hvk : virtKind = .none) (onCore : ObjRef → Bool) (rep : Bool) (c : Syscall)
    {t : State Unit} (ht : NR t) (hoff : OffRouteS8 c t) :
    ExceptT.run (fl4HandleSyscallV (Z := Unit) onCore rep c) t = ExceptT.run (fl4HandleSyscall rep c) t := by
  cases c with
  | sysSend =>
    show ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) cap_register) >>= fun cptr =>
        fl4HandleInvocationV onCore rep false true false false cptr) t =
      ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) cap_register) >>= fun cptr =>
        fl4HandleInvocationR rep false true false false cptr) t
    exact invoke_congr60 hvk onCore rep false true false false cap_register ht fun cptr t' h => hoff _ rfl cptr t' h
  | sysNBSend =>
    show ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) cap_register) >>= fun cptr =>
        fl4HandleInvocationV onCore rep false false false false cptr) t =
      ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) cap_register) >>= fun cptr =>
        fl4HandleInvocationR rep false false false false cptr) t
    exact invoke_congr60 hvk onCore rep false false false false cap_register ht fun cptr t' h => hoff _ rfl cptr t' h
  | sysCall =>
    show ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) cap_register) >>= fun cptr =>
        fl4HandleInvocationV onCore rep true true true false cptr) t =
      ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) cap_register) >>= fun cptr =>
        fl4HandleInvocationR rep true true true false cptr) t
    exact invoke_congr60 hvk onCore rep true true true false cap_register ht fun cptr t' h => hoff _ rfl cptr t' h
  | sysReplyRecv =>
    show ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) replyRegister) >>= fun cptr =>
        fl4HandleInvocationV onCore rep false false true true cptr >>= fun _ => withoutPreemption (handleRecv (Z := Unit) true true)) t =
      ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) replyRegister) >>= fun cptr =>
        fl4HandleInvocationR rep false false true true cptr >>= fun _ => withoutPreemption (handleRecv (Z := Unit) true true)) t
    exact invoke_congr6 hvk onCore rep false false true true replyRegister (k := fun _ => withoutPreemption (handleRecv (Z := Unit) true true)) ht fun cptr t' h => hoff _ rfl cptr t' h
  | sysNBSendRecv =>
    show ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) nbsendRecvDest) >>= fun cptr =>
        fl4HandleInvocationV onCore rep false false true true cptr >>= fun _ => withoutPreemption (handleRecv (Z := Unit) true true)) t =
      ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) nbsendRecvDest) >>= fun cptr =>
        fl4HandleInvocationR rep false false true true cptr >>= fun _ => withoutPreemption (handleRecv (Z := Unit) true true)) t
    exact invoke_congr6 hvk onCore rep false false true true nbsendRecvDest (k := fun _ => withoutPreemption (handleRecv (Z := Unit) true true)) ht fun cptr t' h => hoff _ rfl cptr t' h
  | sysNBSendWait =>
    show ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) replyRegister) >>= fun cptr =>
        fl4HandleInvocationV onCore rep false false true true cptr >>= fun _ => withoutPreemption (handleRecv (Z := Unit) true false)) t =
      ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) replyRegister) >>= fun cptr =>
        fl4HandleInvocationR rep false false true true cptr >>= fun _ => withoutPreemption (handleRecv (Z := Unit) true false)) t
    exact invoke_congr6 hvk onCore rep false false true true replyRegister (k := fun _ => withoutPreemption (handleRecv (Z := Unit) true false)) ht fun cptr t' h => hoff _ rfl cptr t' h
  | sysRecv => rfl
  | sysYield => rfl
  | sysWait => rfl
  | sysNBWait => rfl
  | sysNBRecv => rfl

/-- The syscall event, fp-exact scope. -/
theorem fl4HandleEventV_syscall8 (hvk : virtKind = .none) (onCore : ObjRef → Bool) (rep : Bool) (c : Syscall)
    {σ : State Unit} (hs : NR σ) (hoff : ∀ t, EntryPt σ t → OffRouteS8 c t) :
    ExceptT.run (fl4HandleEventV (Z := Unit) onCore rep (.syscallEvent c)) σ =
      ExceptT.run (fl4HandleEvent rep (.syscallEvent c)) σ := by
  show ExceptT.run (NonDetE.liftE updateTimeStamp >>= fun _ => NonDetE.liftE checkBudgetRestart >>= fun restart =>
      NonDetE.whenE restart (fl4HandleSyscallV (Z := Unit) onCore rep c)) σ =
    ExceptT.run (NonDetE.liftE updateTimeStamp >>= fun _ => NonDetE.liftE checkBudgetRestart >>= fun restart =>
      NonDetE.whenE restart (fl4HandleSyscall (Z := Unit) rep c)) σ
  refine nde_bind_congr rfl fun _ t1 h1 => ?_
  have h1' := mem_run_liftE' h1
  refine nde_bind_congr rfl fun restart t h2 => ?_
  have h2' := mem_run_liftE' h2
  unfold NonDetE.whenE
  cases restart with
  | false => rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
  | true =>
    rw [if_pos rfl, if_pos rfl]
    have he : EntryPt σ t := ⟨t1, h1', h2'⟩
    have hnv : NV t := ⟨nvc_entryPt hs.1.1 he, ty_checkBudgetRestart t1 (ty_updateTimeStamp σ hs.1.2 _ h1') _ h2'⟩
    have hnr : NoRunVM t := ns_checkBudgetRestart t1 (ns_updateTimeStamp σ hs.2 _ h1') _ h2'
    exact fl4HandleSyscallV_eqNR8 hvk onCore rep c ⟨hnv, hnr⟩ (hoff t he)

theorem fl4HandleEventV_eqNR8 (hvk : virtKind = .none) (onCore : ObjRef → Bool) (rep : Bool) (ev : Event)
    {σ : State Unit} (hs : NR σ) (hoff : ∀ c, ev = .syscallEvent c → ∀ t, EntryPt σ t → OffRouteS8 c t) :
    ExceptT.run (fl4HandleEventV (Z := Unit) onCore rep ev) σ = ExceptT.run (fl4HandleEvent rep ev) σ := by
  cases ev with
  | syscallEvent c => exact fl4HandleEventV_syscall8 hvk onCore rep c hs (hoff c rfl)
  | unknownSyscall n => exact fl4HandleEventV_unknown_nvv onCore rep hs.1.2 n
  | interrupt => exact fl4HandleEventV_interrupt onCore rep hs.2
  | _ => rfl

/-- **R7 (e) with the fp-exact scope**: the extended kernel step is the ported one on an `NR` state (premises
`hvk`, `hoff` [S], module docstring). -/
theorem fl4CallKernelV_eqNR8 (hvk : virtKind = .none) (onCore : ObjRef → Bool) (rep : Bool) (ev : Event)
    {σ : State Unit} (hs : NR σ) (hoff : ∀ c, ev = .syscallEvent c → ∀ t, EntryPt σ t → OffRouteS8 c t) :
    fl4CallKernelV (Z := Unit) onCore rep ev σ = fl4CallKernel rep ev σ := by
  unfold fl4CallKernelV fl4CallKernel
  have hH : ExceptT.run (NonDetE.handleE (fl4HandleEventV (Z := Unit) onCore rep ev)
        (fun _ => withoutPreemption (preemptionPathV onCore))) σ =
      ExceptT.run (NonDetE.handleE (fl4HandleEvent (Z := Unit) rep ev)
        (fun _ => withoutPreemption preemptionPath)) σ := by
    unfold NonDetE.handleE
    rw [ExceptT.run_mk, ExceptT.run_mk]
    refine (nd_bind_eq_of (fl4HandleEventV_eqNR8 hvk onCore rep ev hs hoff) _).trans
      (nd_bind_congr_on _ _ _ σ fun y hy => ?_)
    obtain ⟨r, u⟩ := y
    cases r with
    | ok a => rfl
    | error e =>
      have hu : NoRunVM u := ns_fl4HandleEvent rep ev σ hs.2 _ hy
      exact run_liftE_congr (preemptionPathV_eq onCore hu)
  rw [nd_bind_eq_of hH]
  refine nd_bind_congr_on _ _ _ σ fun y hy => ?_
  have hu : NoRunVM y.2 := ike_handleE (ns_fl4HandleEvent rep ev) (fun _ => ike_liftE ns_preemptionPath) σ hs.2 _ hy
  exact fl4KernelExitV_eq' onCore hu

set_option maxHeartbeats 8000000 in
/-- **Every syscall keeps `NR`** in the fp-exact scope. -/
theorem nr_fl4HandleSyscall8 (hvk : virtKind = .none) (rep : Bool) (c : Syscall) {t : State Unit} (ht : NR t)
    (hoff : OffRouteS8 c t) : ∀ y ∈ (ExceptT.run (fl4HandleSyscall (Z := Unit) rep c) t).1, NR y.2 := by
  cases c with
  | sysSend =>
    show ∀ y ∈ (ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) cap_register) >>= fun cptr =>
        fl4HandleInvocationR rep false true false false cptr) t).1, NR y.2
    exact nr_invoke60 hvk rep false true false false cap_register ht fun cptr t' h => hoff _ rfl cptr t' h
  | sysNBSend =>
    show ∀ y ∈ (ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) cap_register) >>= fun cptr =>
        fl4HandleInvocationR rep false false false false cptr) t).1, NR y.2
    exact nr_invoke60 hvk rep false false false false cap_register ht fun cptr t' h => hoff _ rfl cptr t' h
  | sysCall =>
    show ∀ y ∈ (ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) cap_register) >>= fun cptr =>
        fl4HandleInvocationR rep true true true false cptr) t).1, NR y.2
    exact nr_invoke60 hvk rep true true true false cap_register ht fun cptr t' h => hoff _ rfl cptr t' h
  | sysReplyRecv =>
    show ∀ y ∈ (ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) replyRegister) >>= fun cptr =>
        fl4HandleInvocationR rep false false true true cptr >>= fun _ =>
          withoutPreemption (handleRecv (Z := Unit) true true)) t).1, NR y.2
    exact nr_invoke6 hvk rep false false true true replyRegister (nr_recvK true) ht
      fun cptr t' h => hoff _ rfl cptr t' h
  | sysNBSendRecv =>
    show ∀ y ∈ (ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) nbsendRecvDest) >>= fun cptr =>
        fl4HandleInvocationR rep false false true true cptr >>= fun _ =>
          withoutPreemption (handleRecv (Z := Unit) true true)) t).1, NR y.2
    exact nr_invoke6 hvk rep false false true true nbsendRecvDest (nr_recvK true) ht
      fun cptr t' h => hoff _ rfl cptr t' h
  | sysNBSendWait =>
    show ∀ y ∈ (ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) replyRegister) >>= fun cptr =>
        fl4HandleInvocationR rep false false true true cptr >>= fun _ =>
          withoutPreemption (handleRecv (Z := Unit) true false)) t).1, NR y.2
    exact nr_invoke6 hvk rep false false true true replyRegister (nr_recvK false) ht
      fun cptr t' h => hoff _ rfl cptr t' h
  | sysRecv => exact nr_recv true true t ht
  | sysWait => exact nr_recv true false t ht
  | sysNBWait => exact nr_recv false false t ht
  | sysNBRecv => exact nr_recv false true t ht
  | sysYield => exact SInv.ike_liftE (nr_of nvc_handleYield ty_handleYield ns_handleYield) t ht

set_option maxHeartbeats 4000000 in
/-- **Every event keeps `NR`** in the fp-exact scope. -/
theorem nr_fl4HandleEvent8 (hvk : virtKind = .none) (rep : Bool) (ev : Event) {σ : State Unit} (hs : NR σ)
    (hr6 : ∀ c, ev = .syscallEvent c → ∀ t, EntryPt σ t → OffRouteS8 c t) :
    ∀ y ∈ (ExceptT.run (fl4HandleEvent (Z := Unit) rep ev) σ).1, NR y.2 := by
  by_cases h : ∃ c, ev = .syscallEvent c
  · obtain ⟨c, rfl⟩ := h
    show ∀ y ∈ (ExceptT.run (NonDetE.liftE updateTimeStamp >>= fun _ => NonDetE.liftE checkBudgetRestart >>=
      fun restart => NonDetE.whenE restart (fl4HandleSyscall (Z := Unit) rep c)) σ).1, NR y.2
    refine post_bindE (fun _ t1 h1 => ?_) (fun e s h => (liftE_no_err h).elim)
    have h1' := mem_run_liftE' h1
    refine post_bindE (fun restart t h2 => ?_) (fun e s h => (liftE_no_err h).elim)
    have h2' := mem_run_liftE' h2
    have nt : NR t := nr_checkBudgetRestart t1 (nr_updateTimeStamp σ hs _ h1') _ h2'
    unfold NonDetE.whenE
    cases restart with
    | false => rw [if_neg Bool.false_ne_true]; exact (SInv.ike_returnOk (P := NR) ()) t nt
    | true =>
      rw [if_pos rfl]
      exact nr_fl4HandleSyscall8 hvk rep c nt (hr6 c rfl t ⟨t1, h1', h2'⟩)
  · have h' : ∀ c, ev ≠ .syscallEvent c := fun c e => h ⟨c, e⟩
    intro y hy
    have hn := ns_fl4HandleEvent rep ev σ hs.2 y hy
    have ht := ty_fl4HandleEvent_other rep ev h' σ hs.1.2 y hy
    rw [fl4HandleEvent_other rep ev h'] at hy
    exact ⟨⟨nvc_handleEvent_other ev h' σ hs.1.1 y hy, ht⟩, hn⟩

/-- **The ported kernel step keeps `NR`** in the fp-exact scope at `virtKind = none`. -/
theorem nr_fl4CallKernel8 (hvk : virtKind = .none) (rep : Bool) (ev : Event) {σ : State Unit} (hs : NR σ)
    (hr6 : ∀ c, ev = .syscallEvent c → ∀ t, EntryPt σ t → OffRouteS8 c t) :
    ∀ y ∈ (fl4CallKernel (Z := Unit) rep ev σ).1, NR y.2 := by
  unfold fl4CallKernel
  intro y ⟨z, hz, hy⟩
  have nz : NR z.2 := by
    unfold NonDetE.handleE at hz
    rw [ExceptT.run_mk] at hz
    obtain ⟨⟨r, u⟩, hw, hz⟩ := hz
    have nu : NR u := nr_fl4HandleEvent8 hvk rep ev hs hr6 _ hw
    cases r with
    | ok a =>
      obtain rfl := Set.mem_singleton_iff.1 hz
      exact nu
    | error e => exact (SInv.ike_liftE (P := NR) nr_preemptionPath) u nu z hz
  exact nr_kernelExit z.2 nz y hy

/-! ## The syscall entry -/

/-- **The extended syscall entry is the ported one** on an `NR` state in the fp-exact scope. -/
theorem fl4KernelEntrySyscallV_eqNR8 (hvk : virtKind = .none) (onCore : ObjRef → Bool) (rep : Bool) (c : Syscall)
    {σ : State Unit} (hs : NR σ) (hr : ScopeE8 c σ) :
    fl4KernelEntrySyscallV (Z := Unit) onCore rep c σ = fl4KernelEntrySyscall rep c σ := by
  unfold fl4KernelEntrySyscallV fl4KernelEntrySyscall
  refine nd_bind_congr_on _ _ _ σ fun y hy => ?_
  simp only [NonDet.gets, Set.mem_singleton_iff] at hy
  subst hy
  refine nd_bind_congr_on _ _ _ σ fun w hw => ?_
  exact fl4CallKernelV_eqNR8 hvk onCore rep _ (nr_fl4SyscallFaultIP _ σ hs w hw)
    fun c' e t ht => by cases e; exact hr w hw t ht

theorem nr_kentry8 (hvk : virtKind = .none) {rep : Bool} {c : Syscall} {σ σ' : State Unit} (hs : NR σ)
    (hr : ScopeE8 c σ) (h : ((), σ') ∈ (fl4KernelEntrySyscall (Z := Unit) rep c σ).1) : NR σ' := by
  unfold fl4KernelEntrySyscall at h
  obtain ⟨y, hy, w, hw, hx⟩ := h
  simp only [NonDet.gets, Set.mem_singleton_iff] at hy
  subst hy
  exact nr_fl4CallKernel8 hvk rep _ (nr_fl4SyscallFaultIP _ σ hs w hw)
    (fun c' e t ht => by cases e; exact hr w hw t ht) _ hx

/-- **A ported-spec syscall exit is an extended-spec exit** in the fp-exact scope (premises `hvk`, `hr` [S]). -/
theorem kentryV_post8 (hvk : virtKind = .none) (onCore : ObjRef → Bool) {α : Type} {m : Result α}
    {P : α → State Unit → Prop} {c : Syscall} {σ : State Unit} (hs : NR σ) (hr : ScopeE8 c σ)
    (h : m ⦃ r => ∃ σ', ((), σ') ∈ (fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧ P r σ' ⦄) :
    m ⦃ r => ∃ σ', ((), σ') ∈ (fl4KernelEntrySyscallV (Z := Unit) onCore true c σ).1 ∧ P r σ' ∧ NR σ' ⦄ := by
  refine WP.spec_mono h ?_
  intro r ⟨σ', h1, h2⟩
  refine ⟨σ', ?_, h2, nr_kentry8 hvk hs hr h1⟩
  rw [fl4KernelEntrySyscallV_eqNR8 hvk onCore true c hs hr]
  exact h1

end

end Fl4Proofs.P3.VirtScope8
