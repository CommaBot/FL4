/-
P3x for virtualization (line virt, gen 7, item 1; proofs/VIRT-PLAN.md §10 R7): **the route scope widened to the
on-route decode points where the two decoders agree.**

Gen 5/6's scope `OffRoute5` / `hr5` / `ScopeE` [S] (VirtTcbOK, VirtNvK2, VirtExtTop) excludes every decode point
on one of the three routes (`Route3`, VirtOffNv: label 60 on a frame cap, label 88 on a thread cap in the second
phase, the VT-x retype gate on an untyped cap). On an `NR` state the extended decoder answers every such point
with an error (route B: `decOKV_thread88_noVirt`, `decOKV_frame60_noVirt`, `decOKV_untyped_vtxGate`); where the
ported decoder answers it with the **same single error**, the two kernel steps still coincide (the error tail of
`fl4HandleInvocationR` / `fl4HandleInvocationV` is the same `msgFromSyscallError` reply). This module proves
that, so the scope shrinks to the on-route points where the decoders disagree:

* `ErrAgree` (both decoders: one outcome, the same error, state kept), `DecGood6` (`¬ Route3 ∨ ErrAgree`),
  `OffRoute6` / `OffRouteS6` / `ScopeE6` (gen 5/6's scope with `DecGood6` in place of `¬ Route3`),
  `offRoute6_of5`, `offRouteS6_of5`, `scopeE6_of` (the old scope implies the new one).
* `good_of_route3` (per decode point: gen 5's reduction ¬Route3 ⇒ ¬VirtRoute ∧ InvOK on NVC states).
* **`fl4HandleInvocationV_eqNR6`**, `invoke_congr6(0)`, `fl4HandleSyscallV_eqNR6`, `fl4HandleEventV_syscall6`,
  `fl4HandleEventV_eqNR6`, **`fl4CallKernelV_eqNR6`** (VirtR7e / VirtR7eK's chain with the wider scope).
* `nr_handleInvocationR6`, `nr_invoke6(0)`, `nr_fl4HandleSyscall6`, `nr_fl4HandleEvent6`, **`nr_fl4CallKernel6`**
  (VirtNvK2's NR preservation with the wider scope; at an `ErrAgree` point no invocation is decoded).
* **`fl4KernelEntrySyscallV_eqNR6`**, `nr_kentry6`, **`kentryV_post6`** (VirtExtTop's syscall exit transport).

Named premises:
* **`hvk : virtKind = .none` [S]** (as gen 5/6).
* **`hr6 : ScopeE6 c σ` [S]** (syscall exits only): every decode point of the entry is off the routes or its
  two decoders agree (`DecGood6`). Weaker than gen 6's `ScopeE` (`scopeE6_of`). What it still excludes is exactly
  the on-route points where the ported and the extended decoder differ; VirtAgreeDec shows FL4's own premise of
  U36I (the `XCapP` leaf at the invoked slot, against the ported decoder) is false there, i.e. at every on-route
  point where U36I's syscall clause says anything, `ErrAgree` holds.

No [J]/[P]/[W]. New file only.
-/
import Fl4Proofs.P3.VirtExtTop
open Aeneas Aeneas.Std Result
open Classical

namespace Fl4Proofs.P3.VirtAgree
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvV Fl4Proofs.P3.SInvL Fl4Proofs.P3.SInvDom
  Fl4Proofs.P3.SInvTY Fl4Proofs.P3.VirtR7b Fl4Proofs.P3.VirtR7d Fl4Proofs.P3.VirtAwaken Fl4Proofs.P3.VirtR7e Fl4Proofs.P3.VirtR7eK
  Fl4Proofs.P3.VirtR7eK2 Fl4Proofs.P3.VirtNvTcb Fl4Proofs.P3.VirtNvcW Fl4Proofs.P3.VirtOffNv Fl4Proofs.P3.VirtInvOK
  Fl4Proofs.P3.VirtTcbOK Fl4Proofs.P3.VirtNvInv Fl4Proofs.P3.VirtNvK1 Fl4Proofs.P3.VirtTyK7 Fl4Proofs.P3.VirtNvK2
  Fl4Proofs.P3.VirtExtTop

noncomputable section

/-! ## The scope -/

/-- **The two decoders agree on one error** at a decode point (module docstring). -/
def ErrAgree (fp : Bool) (cptr : CapRef) (info : MessageInfo)
    (a : CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef) (args : List Data) (u : State Unit) : Prop :=
  ∃ e, ExceptT.run (fl4DecodeInvocation (Z := Unit) fp info.miLabel args cptr a.1 a.2.1 a.2.2.1 a.2.2.2) u =
      ({(.error e, u)}, False) ∧
    ExceptT.run (fl4DecodeInvocationV (Z := Unit) fp info.miLabel args cptr a.1 a.2.1 a.2.2.1 a.2.2.2) u =
      ({(.error e, u)}, False)

/-- A decode point in the widened scope: off the three routes, or both decoders give the same error. -/
def DecGood6 (fp : Bool) (cptr : CapRef) (info : MessageInfo)
    (a : CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef) (args : List Data) (u : State Unit) : Prop :=
  ¬ Route3 fp info.miLabel args a.2.1 a.2.2.1 ∨ ErrAgree fp cptr info a args u

/-- **`OffRoute5` widened** (the [S] premise, module docstring). -/
def OffRoute6 (fp : Bool) (cptr : CapRef) (s : State Unit) : Prop :=
  ∀ info a args u, DecPt cptr s info a args u → DecGood6 fp cptr info a args u

def OffRouteS6 (c : Syscall) (t : State Unit) : Prop :=
  ∀ reg, sysReg c = some reg → ∀ cptr t', (cptr, t') ∈ (getCapReg (Z := Unit) reg t).1 → ∀ fp, OffRoute6 fp cptr t'

/-- **The syscall entry's widened scope** ([S], module docstring). -/
def ScopeE6 (c : Syscall) (σ : State Unit) : Prop :=
  ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1, ∀ t, EntryPt w.2 t → OffRouteS6 c t

theorem offRoute6_of5 {fp : Bool} {cptr : CapRef} {s : State Unit} (h : OffRoute5 fp cptr s) : OffRoute6 fp cptr s :=
  fun info a args u hd => Or.inl (h info a args u hd)

theorem offRouteS6_of5 {c : Syscall} {t : State Unit} (h : OffRouteS5 c t) : OffRouteS6 c t :=
  fun reg hr cptr t' hm fp => offRoute6_of5 (h reg hr cptr t' hm fp)

/-- Gen 6's scope implies the widened one. -/
theorem scopeE6_of {c : Syscall} {σ : State Unit} (h : ScopeE c σ) : ScopeE6 c σ :=
  fun w hw t ht => offRouteS6_of5 (h w hw t ht)

/-- Gen 5's per-point reduction: off the three routes on an `NVC` state, the point is off `VirtRoute` and every
decoded invocation is `InvOK`. -/
theorem good_of_route3 (hvk : virtKind = .none) {fp : Bool} {cptr : CapRef} {s : State Unit} (hs : NVC s)
    {info : MessageInfo} {a : CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef} {args : List Data}
    {u : State Unit} (hd : DecPt cptr s info a args u) (hr : ¬ Route3 fp info.miLabel args a.2.1 a.2.2.1) :
    ¬ VirtRoute fp info.miLabel args a.2.1 a.2.2.1 ∧
    ∀ i v, ((Except.ok i : Except SyscallError Fl4Invocation), v) ∈
      (ExceptT.run (fl4DecodeInvocation (Z := Unit) fp info.miLabel args cptr a.1 a.2.1 a.2.2.1 a.2.2.2) u).1 →
      InvOK i := by
  obtain ⟨s1, t, h1, ha, hu⟩ := hd
  have n1 : NVC s1 := hv_getMessageInfo (P := NVC) _ s hs _ h1
  obtain ⟨-, hc, he⟩ := okn_lookupPart n1 s.curThread cptr info s1 rfl a t ha
  refine ⟨fun hv => hr (route3_of_virtRoute hc he hv), fun i v hi => ?_⟩
  refine okd_fl4Decode_invOK hvk fp _ args cptr _ _ _ _ u (fun d p n f e => ?_)
    (fun _ _ => okd_fl4DecodeTcb_invOK _ _ _ _ _ _ u) i v hi
  intro hgate
  apply hr
  rw [e]
  exact hgate

/-! ## The extended step is the ported one -/

/-- **`fl4HandleInvocationV_eqNR` with the widened scope.** -/
theorem fl4HandleInvocationV_eqNR6 (hvk : virtKind = .none) (onCore : ObjRef → Bool)
    (rep calling blocking don fp : Bool) (cptr : CapRef) {s : State Unit} (hs : NR s) (hoff : OffRoute6 fp cptr s) :
    ExceptT.run (fl4HandleInvocationV (Z := Unit) onCore rep calling blocking don fp cptr) s =
      ExceptT.run (fl4HandleInvocationR rep calling blocking don fp cptr) s := by
  unfold fl4HandleInvocationV fl4HandleInvocationR
  refine nde_bind_congr rfl fun thread s0 h0 => ?_
  have h0' := mem_run_liftE' h0
  simp only [NonDet.gets, Set.mem_singleton_iff, Prod.mk.injEq] at h0'
  obtain ⟨rfl, rfl⟩ := h0'
  refine nde_bind_congr rfl fun info s1 h1 => ?_
  have h1' := mem_run_liftE' h1
  have n1 : NR s1 := nr_getMessageInfo _ _ hs _ h1'
  refine syscall_congrV _ _ _ _ _ _ _ Fl4InvocationV.base (fun a t ha => ?_) (fun a t b u ha hb => ?_)
  · obtain ⟨slot, cap, ex, buf⟩ := a
    dsimp only
    rw [run_liftME_bind]
    refine nde_bind_congr rfl fun args u hu => ?_
    have hu' := mem_run_liftE' hu
    have hd : DecPt cptr s0 info (slot, cap, ex, buf) args u := ⟨s1, t, h1', ha, hu'⟩
    rcases hoff info (slot, cap, ex, buf) args u hd with hr | ⟨e, hP, hV⟩
    · rw [fl4DecodeInvocationV_base _ _ _ _ _ _ _ _ (good_of_route3 hvk hs.1.1 hd hr).1]
    · dsimp only at hP hV
      rw [hV, run_liftME_err hP]
  · obtain ⟨slot, cap, ex, buf⟩ := a
    have nt : NR t := nr_lookupPart _ cptr info s1 n1 _ ha
    dsimp only at hb ⊢
    rw [ExceptT.run_bind] at hb
    obtain ⟨⟨r1, t2⟩, hr1, hb'⟩ := hb
    cases r1 with
    | error e =>
      exfalso
      simp only [ExceptT.bindCont] at hb'
      cases Set.mem_singleton_iff.1 hb'
    | ok args =>
      simp only [ExceptT.bindCont] at hb'
      have hr1' := mem_run_liftE' hr1
      have n2 : NR t2 := nr_getMrs _ _ _ t nt _ hr1'
      have hd : DecPt cptr s0 info (slot, cap, ex, buf) args t2 := ⟨s1, t, h1', ha, hr1'⟩
      rcases hoff info (slot, cap, ex, buf) args t2 hd with hr | ⟨e, hP, -⟩
      · have hInv := (good_of_route3 hvk hs.1.1 hd hr).2 b u hb'
        have nu : NR u := nr_fl4Decode _ _ _ _ _ _ _ _ t2 n2 _ hb'
        refine nde_bind_congr rfl fun _ v hv => ?_
        have nv : NR v := nr_setRestart _ u nu _ (mem_run_liftE' hv)
        exact nde_bind_congr (fl4PerformInvocationV_eqNR onCore blocking calling don b nv hInv) fun _ _ _ => rfl
      · exfalso
        have hb2 := hb'
        dsimp only at hP
        rw [hP] at hb2
        cases (Prod.mk.inj (Set.mem_singleton_iff.1 hb2)).1

theorem invoke_congr6 (hvk : virtKind = .none) (onCore : ObjRef → Bool) (rep calling blocking don fp : Bool)
    (reg : Register) {k : Unit → PMonad Unit Unit} {t : State Unit} (ht : NR t)
    (hoff : ∀ cptr t', (cptr, t') ∈ (getCapReg (Z := Unit) reg t).1 → OffRoute6 fp cptr t') :
    ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) reg) >>= fun cptr =>
        fl4HandleInvocationV onCore rep calling blocking don fp cptr >>= k) t =
      ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) reg) >>= fun cptr =>
        fl4HandleInvocationR rep calling blocking don fp cptr >>= k) t := by
  refine nde_bind_congr rfl fun cptr t' h => ?_
  have h' := mem_run_liftE' h
  exact nde_bind_congr (fl4HandleInvocationV_eqNR6 hvk onCore rep calling blocking don fp cptr
    (nr_getCapReg reg t ht _ h') (hoff cptr t' h')) fun _ _ _ => rfl

theorem invoke_congr60 (hvk : virtKind = .none) (onCore : ObjRef → Bool) (rep calling blocking don fp : Bool)
    (reg : Register) {t : State Unit} (ht : NR t)
    (hoff : ∀ cptr t', (cptr, t') ∈ (getCapReg (Z := Unit) reg t).1 → OffRoute6 fp cptr t') :
    ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) reg) >>= fun cptr =>
        fl4HandleInvocationV onCore rep calling blocking don fp cptr) t =
      ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) reg) >>= fun cptr =>
        fl4HandleInvocationR rep calling blocking don fp cptr) t := by
  refine nde_bind_congr rfl fun cptr t' h => ?_
  have h' := mem_run_liftE' h
  exact fl4HandleInvocationV_eqNR6 hvk onCore rep calling blocking don fp cptr
    (nr_getCapReg reg t ht _ h') (hoff cptr t' h')

/-- **Every syscall of the extended kernel is the ported one** from an `NR` state in the widened scope. -/
theorem fl4HandleSyscallV_eqNR6 (hvk : virtKind = .none) (onCore : ObjRef → Bool) (rep : Bool) (c : Syscall)
    {t : State Unit} (ht : NR t) (hoff : OffRouteS6 c t) :
    ExceptT.run (fl4HandleSyscallV (Z := Unit) onCore rep c) t = ExceptT.run (fl4HandleSyscall rep c) t := by
  cases c with
  | sysSend =>
    show ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) cap_register) >>= fun cptr =>
        fl4HandleInvocationV onCore rep false true false false cptr) t =
      ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) cap_register) >>= fun cptr =>
        fl4HandleInvocationR rep false true false false cptr) t
    exact invoke_congr60 hvk onCore rep false true false false cap_register ht fun cptr t' h => hoff _ rfl cptr t' h _
  | sysNBSend =>
    show ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) cap_register) >>= fun cptr =>
        fl4HandleInvocationV onCore rep false false false false cptr) t =
      ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) cap_register) >>= fun cptr =>
        fl4HandleInvocationR rep false false false false cptr) t
    exact invoke_congr60 hvk onCore rep false false false false cap_register ht fun cptr t' h => hoff _ rfl cptr t' h _
  | sysCall =>
    show ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) cap_register) >>= fun cptr =>
        fl4HandleInvocationV onCore rep true true true false cptr) t =
      ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) cap_register) >>= fun cptr =>
        fl4HandleInvocationR rep true true true false cptr) t
    exact invoke_congr60 hvk onCore rep true true true false cap_register ht fun cptr t' h => hoff _ rfl cptr t' h _
  | sysReplyRecv =>
    show ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) replyRegister) >>= fun cptr =>
        fl4HandleInvocationV onCore rep false false true true cptr >>= fun _ => withoutPreemption (handleRecv (Z := Unit) true true)) t =
      ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) replyRegister) >>= fun cptr =>
        fl4HandleInvocationR rep false false true true cptr >>= fun _ => withoutPreemption (handleRecv (Z := Unit) true true)) t
    exact invoke_congr6 hvk onCore rep false false true true replyRegister (k := fun _ => withoutPreemption (handleRecv (Z := Unit) true true)) ht fun cptr t' h => hoff _ rfl cptr t' h _
  | sysNBSendRecv =>
    show ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) nbsendRecvDest) >>= fun cptr =>
        fl4HandleInvocationV onCore rep false false true true cptr >>= fun _ => withoutPreemption (handleRecv (Z := Unit) true true)) t =
      ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) nbsendRecvDest) >>= fun cptr =>
        fl4HandleInvocationR rep false false true true cptr >>= fun _ => withoutPreemption (handleRecv (Z := Unit) true true)) t
    exact invoke_congr6 hvk onCore rep false false true true nbsendRecvDest (k := fun _ => withoutPreemption (handleRecv (Z := Unit) true true)) ht fun cptr t' h => hoff _ rfl cptr t' h _
  | sysNBSendWait =>
    show ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) replyRegister) >>= fun cptr =>
        fl4HandleInvocationV onCore rep false false true true cptr >>= fun _ => withoutPreemption (handleRecv (Z := Unit) true false)) t =
      ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) replyRegister) >>= fun cptr =>
        fl4HandleInvocationR rep false false true true cptr >>= fun _ => withoutPreemption (handleRecv (Z := Unit) true false)) t
    exact invoke_congr6 hvk onCore rep false false true true replyRegister (k := fun _ => withoutPreemption (handleRecv (Z := Unit) true false)) ht fun cptr t' h => hoff _ rfl cptr t' h _
  | sysRecv => rfl
  | sysYield => rfl
  | sysWait => rfl
  | sysNBWait => rfl
  | sysNBRecv => rfl

/-- The syscall event, widened scope. -/
theorem fl4HandleEventV_syscall6 (hvk : virtKind = .none) (onCore : ObjRef → Bool) (rep : Bool) (c : Syscall)
    {σ : State Unit} (hs : NR σ) (hoff : ∀ t, EntryPt σ t → OffRouteS6 c t) :
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
    exact fl4HandleSyscallV_eqNR6 hvk onCore rep c ⟨hnv, hnr⟩ (hoff t he)

theorem fl4HandleEventV_eqNR6 (hvk : virtKind = .none) (onCore : ObjRef → Bool) (rep : Bool) (ev : Event)
    {σ : State Unit} (hs : NR σ) (hoff : ∀ c, ev = .syscallEvent c → ∀ t, EntryPt σ t → OffRouteS6 c t) :
    ExceptT.run (fl4HandleEventV (Z := Unit) onCore rep ev) σ = ExceptT.run (fl4HandleEvent rep ev) σ := by
  cases ev with
  | syscallEvent c => exact fl4HandleEventV_syscall6 hvk onCore rep c hs (hoff c rfl)
  | unknownSyscall n => exact fl4HandleEventV_unknown_nvv onCore rep hs.1.2 n
  | interrupt => exact fl4HandleEventV_interrupt onCore rep hs.2
  | _ => rfl

/-- **R7 (e) with the widened scope**: the extended kernel step is the ported one on an `NR` state (premises
`hvk`, `hoff` [S], module docstring). -/
theorem fl4CallKernelV_eqNR6 (hvk : virtKind = .none) (onCore : ObjRef → Bool) (rep : Bool) (ev : Event)
    {σ : State Unit} (hs : NR σ) (hoff : ∀ c, ev = .syscallEvent c → ∀ t, EntryPt σ t → OffRouteS6 c t) :
    fl4CallKernelV (Z := Unit) onCore rep ev σ = fl4CallKernel rep ev σ := by
  unfold fl4CallKernelV fl4CallKernel
  have hH : ExceptT.run (NonDetE.handleE (fl4HandleEventV (Z := Unit) onCore rep ev)
        (fun _ => withoutPreemption (preemptionPathV onCore))) σ =
      ExceptT.run (NonDetE.handleE (fl4HandleEvent (Z := Unit) rep ev)
        (fun _ => withoutPreemption preemptionPath)) σ := by
    unfold NonDetE.handleE
    rw [ExceptT.run_mk, ExceptT.run_mk]
    refine (nd_bind_eq_of (fl4HandleEventV_eqNR6 hvk onCore rep ev hs hoff) _).trans
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

/-! ## `NR` is kept -/

set_option maxHeartbeats 8000000 in
/-- **`nr_handleInvocationR` with the widened scope** (at an `ErrAgree` point nothing is decoded). -/
theorem nr_handleInvocationR6 (hvk : virtKind = .none) (rep calling blocking don fp : Bool) (cptr : CapRef)
    (σ : State Unit) (hs : NR σ) (hoff : OffRoute6 fp cptr σ) :
    ∀ y ∈ (ExceptT.run (fl4HandleInvocationR (Z := Unit) rep calling blocking don fp cptr) σ).1, NR y.2 := by
  unfold fl4HandleInvocationR
  refine post_bindE (fun th s0 h0 => ?_) (fun e s h => (liftE_no_err h).elim)
  have h0' := mem_run_liftE' h0
  simp only [NonDet.gets, Set.mem_singleton_iff, Prod.mk.injEq] at h0'
  obtain ⟨e1, e2⟩ := h0'
  subst s0; subst th
  refine post_bindE (fun info s1 h1 => ?_) (fun e s h => (liftE_no_err h).elim)
  have h1' := mem_run_liftE' h1
  have n1 : NR s1 := nr_getMessageInfo _ _ hs _ h1'
  refine syscall_post' (I := NR) (Q := NR) (fun w hw => nr_lookupPart _ cptr info s1 n1 w hw) ?_ ?_ ?_ ?_
  · intro f s hs' v hv
    exact SInv.ik_when _ (nr_of (nvc_handleFault _ _) (ty_handleFault _ _) (ns_handleFault _ _)) s hs' v hv
  · intro a s has w hw
    obtain ⟨sl, cap, ex, buf⟩ := a
    have nt : NR s := nr_lookupPart _ cptr info s1 n1 _ has
    exact (SInv.ike_bind (SInv.ike_liftE (nr_getMrs _ _ _)) fun _ => nr_fl4Decode _ _ _ _ _ _ _ _) s nt w hw
  · intro e s hs' v hv
    exact SInv.ik_when _ (nr_of (SInvV.hv_fl4ReplyFromKernelError _ _ _) (ty_fl4ReplyFromKernelError _ _ _)
      (ns_fl4ReplyFromKernelError _ _ _)) s hs' v hv
  · intro a s b s' has hbs hI
    obtain ⟨sl, cap, ex, buf⟩ := a
    have nt : NR s := nr_lookupPart _ cptr info s1 n1 _ has
    have eE : hV s' = hV s := (by hv_auto : IKHE (ε := SyscallError) (fun x => hV x = hV s) (do
      let args ← NonDetE.liftE <| getMrs (Z := Unit) σ.curThread buf info
      fl4DecodeInvocation fp info.miLabel args cptr sl cap ex buf)) s rfl _ hbs
    have hcap : capOpt (s.kheap sl.1) sl.2 = some cap := okCap_front σ.curThread cptr info s1 _ s has
    rw [ExceptT.run_bind] at hbs
    obtain ⟨⟨r1, t2⟩, hr1, hb'⟩ := hbs
    cases r1 with
    | error e =>
      exfalso
      simp only [ExceptT.bindCont] at hb'
      cases Set.mem_singleton_iff.1 hb'
    | ok args =>
      simp only [ExceptT.bindCont] at hb'
      have hr1' := mem_run_liftE' hr1
      have n2 : NR t2 := nr_getMrs _ _ _ s nt _ hr1'
      rcases hoff info (sl, cap, ex, buf) args t2 ⟨s1, s, h1', has, hr1'⟩ with hr | ⟨e, hP, -⟩
      swap
      · exfalso
        have hb2 := hb'
        dsimp only at hP
        rw [hP] at hb2
        cases (Prod.mk.inj (Set.mem_singleton_iff.1 hb2)).1
      have hg : ∀ d p n f, cap = .untypedCap d p n f → ¬ untypedVtxGate info.miLabel args (ex.map Prod.fst) :=
        fun d p n f e hgate => hr (by subst e; exact hgate)
      have hInv : InvNV b := okd_fl4Decode_invNV hvk fp _ args cptr sl cap ex buf t2 n2.1.1 hg b s' hb'
      have hK := okd_fl4Decode_nvK1 fp info.miLabel args cptr sl cap ex buf t2 b s' hb'
      refine post_bindE (fun _ s2 h2 => ?_) (fun e s2 h2 => (liftE_no_err h2).elim)
      have h2' := mem_run_liftE' h2
      have n3 : NR s2 := nr_setRestart _ s' hI _ h2'
      have e3 : hV s2 = hV s' :=
        (SInvV.hv_setThreadState (P := fun x => hV x = hV s') _ _) s' rfl _ h2'
      have hU : UnmapOK s2 b := unmapOK_of_hV (e3.trans eE) (unmapOK_of hK.2 hcap)
      have hP : ∀ x ∈ (ExceptT.run (fl4PerformInvocation (Z := Unit) blocking calling don b) s2).1, NR x.2 :=
        fun x hx => ⟨⟨nvc_fl4Perform blocking calling don b s2 n3.1.1 hInv hK.1 hU x hx,
          ty_fl4Perform blocking calling don b hInv s2 n3.1.2 x hx⟩,
          ns_fl4PerformInvocation blocking calling don b s2 n3.2 x hx⟩
      refine post_bindE (fun rp s3 h3 => ?_) (fun e s3 h3 => hP _ h3)
      exact (nr_ofE (by hv_auto) (by ty_auto)
        (SInv.ike_liftE (SInv.ik_bind (ns_getThreadState _) fun st => by
          split
          · exact SInv.ik_bind (SInv.ik_when _ (ns_replyFromKernel _ _)) fun _ =>
              ns_setThreadState _ _ (by decide)
          · exact SInv.ik_pure _)) : SInv.IKE NR (withoutPreemption (do
        let state ← getThreadState (Z := Unit) σ.curThread
        match state with
        | .restart => do
          NonDet.when calling <| replyFromKernel σ.curThread (0, rp)
          setThreadState σ.curThread .running
        | _ => return ()))) s3 (hP _ h3)

theorem nr_invoke6 (hvk : virtKind = .none) (rep calling blocking don fp : Bool) (reg : Register)
    {k : Unit → PMonad Unit Unit} (hk : ∀ u, SInv.IKE NR (k u)) {t : State Unit} (ht : NR t)
    (hoff : ∀ cptr t', (cptr, t') ∈ (getCapReg (Z := Unit) reg t).1 → OffRoute6 fp cptr t') :
    ∀ y ∈ (ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) reg) >>= fun cptr =>
        fl4HandleInvocationR rep calling blocking don fp cptr >>= k) t).1, NR y.2 := by
  refine post_bindE (fun cptr t' h => ?_) (fun e s h => (liftE_no_err h).elim)
  have h' := mem_run_liftE' h
  have nt' := nr_getCapReg reg t ht _ h'
  exact post_bindE (fun _ u hu => hk _ u (nr_handleInvocationR6 hvk rep calling blocking don fp cptr t' nt'
    (hoff _ _ h') _ hu)) (fun e u hu => nr_handleInvocationR6 hvk rep calling blocking don fp cptr t' nt'
    (hoff _ _ h') _ hu)

theorem nr_invoke60 (hvk : virtKind = .none) (rep calling blocking don fp : Bool) (reg : Register)
    {t : State Unit} (ht : NR t)
    (hoff : ∀ cptr t', (cptr, t') ∈ (getCapReg (Z := Unit) reg t).1 → OffRoute6 fp cptr t') :
    ∀ y ∈ (ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) reg) >>= fun cptr =>
        fl4HandleInvocationR rep calling blocking don fp cptr) t).1, NR y.2 := by
  refine post_bindE (fun cptr t' h => ?_) (fun e s h => (liftE_no_err h).elim)
  have h' := mem_run_liftE' h
  exact nr_handleInvocationR6 hvk rep calling blocking don fp cptr t' (nr_getCapReg reg t ht _ h') (hoff _ _ h')

set_option maxHeartbeats 8000000 in
/-- **Every syscall keeps `NR`** in the widened scope. -/
theorem nr_fl4HandleSyscall6 (hvk : virtKind = .none) (rep : Bool) (c : Syscall) {t : State Unit} (ht : NR t)
    (hoff : OffRouteS6 c t) : ∀ y ∈ (ExceptT.run (fl4HandleSyscall (Z := Unit) rep c) t).1, NR y.2 := by
  cases c with
  | sysSend =>
    show ∀ y ∈ (ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) cap_register) >>= fun cptr =>
        fl4HandleInvocationR rep false true false false cptr) t).1, NR y.2
    exact nr_invoke60 hvk rep false true false false cap_register ht fun cptr t' h => hoff _ rfl cptr t' h _
  | sysNBSend =>
    show ∀ y ∈ (ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) cap_register) >>= fun cptr =>
        fl4HandleInvocationR rep false false false false cptr) t).1, NR y.2
    exact nr_invoke60 hvk rep false false false false cap_register ht fun cptr t' h => hoff _ rfl cptr t' h _
  | sysCall =>
    show ∀ y ∈ (ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) cap_register) >>= fun cptr =>
        fl4HandleInvocationR rep true true true false cptr) t).1, NR y.2
    exact nr_invoke60 hvk rep true true true false cap_register ht fun cptr t' h => hoff _ rfl cptr t' h _
  | sysReplyRecv =>
    show ∀ y ∈ (ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) replyRegister) >>= fun cptr =>
        fl4HandleInvocationR rep false false true true cptr >>= fun _ =>
          withoutPreemption (handleRecv (Z := Unit) true true)) t).1, NR y.2
    exact nr_invoke6 hvk rep false false true true replyRegister (nr_recvK true) ht
      fun cptr t' h => hoff _ rfl cptr t' h _
  | sysNBSendRecv =>
    show ∀ y ∈ (ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) nbsendRecvDest) >>= fun cptr =>
        fl4HandleInvocationR rep false false true true cptr >>= fun _ =>
          withoutPreemption (handleRecv (Z := Unit) true true)) t).1, NR y.2
    exact nr_invoke6 hvk rep false false true true nbsendRecvDest (nr_recvK true) ht
      fun cptr t' h => hoff _ rfl cptr t' h _
  | sysNBSendWait =>
    show ∀ y ∈ (ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) replyRegister) >>= fun cptr =>
        fl4HandleInvocationR rep false false true true cptr >>= fun _ =>
          withoutPreemption (handleRecv (Z := Unit) true false)) t).1, NR y.2
    exact nr_invoke6 hvk rep false false true true replyRegister (nr_recvK false) ht
      fun cptr t' h => hoff _ rfl cptr t' h _
  | sysRecv => exact nr_recv true true t ht
  | sysWait => exact nr_recv true false t ht
  | sysNBWait => exact nr_recv false false t ht
  | sysNBRecv => exact nr_recv false true t ht
  | sysYield => exact SInv.ike_liftE (nr_of nvc_handleYield ty_handleYield ns_handleYield) t ht

set_option maxHeartbeats 4000000 in
/-- **Every event keeps `NR`** in the widened scope. -/
theorem nr_fl4HandleEvent6 (hvk : virtKind = .none) (rep : Bool) (ev : Event) {σ : State Unit} (hs : NR σ)
    (hr6 : ∀ c, ev = .syscallEvent c → ∀ t, EntryPt σ t → OffRouteS6 c t) :
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
      exact nr_fl4HandleSyscall6 hvk rep c nt (hr6 c rfl t ⟨t1, h1', h2'⟩)
  · have h' : ∀ c, ev ≠ .syscallEvent c := fun c e => h ⟨c, e⟩
    intro y hy
    have hn := ns_fl4HandleEvent rep ev σ hs.2 y hy
    have ht := ty_fl4HandleEvent_other rep ev h' σ hs.1.2 y hy
    rw [fl4HandleEvent_other rep ev h'] at hy
    exact ⟨⟨nvc_handleEvent_other ev h' σ hs.1.1 y hy, ht⟩, hn⟩

/-- **The ported kernel step keeps `NR`** in the widened scope at `virtKind = none`. -/
theorem nr_fl4CallKernel6 (hvk : virtKind = .none) (rep : Bool) (ev : Event) {σ : State Unit} (hs : NR σ)
    (hr6 : ∀ c, ev = .syscallEvent c → ∀ t, EntryPt σ t → OffRouteS6 c t) :
    ∀ y ∈ (fl4CallKernel (Z := Unit) rep ev σ).1, NR y.2 := by
  unfold fl4CallKernel
  intro y ⟨z, hz, hy⟩
  have nz : NR z.2 := by
    unfold NonDetE.handleE at hz
    rw [ExceptT.run_mk] at hz
    obtain ⟨⟨r, u⟩, hw, hz⟩ := hz
    have nu : NR u := nr_fl4HandleEvent6 hvk rep ev hs hr6 _ hw
    cases r with
    | ok a =>
      obtain rfl := Set.mem_singleton_iff.1 hz
      exact nu
    | error e => exact (SInv.ike_liftE (P := NR) nr_preemptionPath) u nu z hz
  exact nr_kernelExit z.2 nz y hy

/-! ## The syscall entry -/

/-- **The extended syscall entry is the ported one** on an `NR` state in the widened scope. -/
theorem fl4KernelEntrySyscallV_eqNR6 (hvk : virtKind = .none) (onCore : ObjRef → Bool) (rep : Bool) (c : Syscall)
    {σ : State Unit} (hs : NR σ) (hr : ScopeE6 c σ) :
    fl4KernelEntrySyscallV (Z := Unit) onCore rep c σ = fl4KernelEntrySyscall rep c σ := by
  unfold fl4KernelEntrySyscallV fl4KernelEntrySyscall
  refine nd_bind_congr_on _ _ _ σ fun y hy => ?_
  simp only [NonDet.gets, Set.mem_singleton_iff] at hy
  subst hy
  refine nd_bind_congr_on _ _ _ σ fun w hw => ?_
  exact fl4CallKernelV_eqNR6 hvk onCore rep _ (nr_fl4SyscallFaultIP _ σ hs w hw)
    fun c' e t ht => by cases e; exact hr w hw t ht

theorem nr_kentry6 (hvk : virtKind = .none) {rep : Bool} {c : Syscall} {σ σ' : State Unit} (hs : NR σ)
    (hr : ScopeE6 c σ) (h : ((), σ') ∈ (fl4KernelEntrySyscall (Z := Unit) rep c σ).1) : NR σ' := by
  unfold fl4KernelEntrySyscall at h
  obtain ⟨y, hy, w, hw, hx⟩ := h
  simp only [NonDet.gets, Set.mem_singleton_iff] at hy
  subst hy
  exact nr_fl4CallKernel6 hvk rep _ (nr_fl4SyscallFaultIP _ σ hs w hw)
    (fun c' e t ht => by cases e; exact hr w hw t ht) _ hx

/-- **A ported-spec syscall exit is an extended-spec exit** in the widened scope (premises `hvk`, `hr` [S]). -/
theorem kentryV_post6 (hvk : virtKind = .none) (onCore : ObjRef → Bool) {α : Type} {m : Result α}
    {P : α → State Unit → Prop} {c : Syscall} {σ : State Unit} (hs : NR σ) (hr : ScopeE6 c σ)
    (h : m ⦃ r => ∃ σ', ((), σ') ∈ (fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧ P r σ' ⦄) :
    m ⦃ r => ∃ σ', ((), σ') ∈ (fl4KernelEntrySyscallV (Z := Unit) onCore true c σ).1 ∧ P r σ' ∧ NR σ' ⦄ := by
  refine WP.spec_mono h ?_
  intro r ⟨σ', h1, h2⟩
  refine ⟨σ', ?_, h2, nr_kentry6 hvk hs hr h1⟩
  rw [fl4KernelEntrySyscallV_eqNR6 hvk onCore true c hs hr]
  exact h1

end

end Fl4Proofs.P3.VirtAgree
