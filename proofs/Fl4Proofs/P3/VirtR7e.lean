/-
P3x for virtualization, spec side (line virt, gen 4; proofs/VIRT-PLAN.md §10 "Remaining (R7)" (e)):
**the extended invocation path is the ported one on `NV ∧ NoRunVM` states off the virtualization routes**.

Spec: `Fl4Spec/Ext/VirtDispatch` (`fl4PerformInvocationV`, `fl4HandleInvocationV`: `fl4HandleInvocationR` with
the extended dispatcher), against `Ext/Invocation`'s `fl4PerformInvocation` and `Ext/ReplyError`'s
`fl4HandleInvocationR`. Nothing of the port changes.

* `NR σ := NV σ ∧ NoRunVM σ` (VirtR7b, VirtR7d): no virtualization cap, no VCPU, no `runningVM` thread. The
  invocation path's ported prefix keeps it (`nr_*`: the generated frames `hv_*` for `NVC`, `ty_*` for `NVV`
  (VirtTyK1..K6), `ns_*` for `NoRunVM`).
* `InvOK i`: a ported invocation the extension substitutes in a way that needs a side condition is harmless: a
  retype is not to the VCPU type, a TCB invocation is `TcbCapsOK` (VirtNvTcb).
* **`fl4PerformInvocationV_eqNR`**: on an `NR` state the extended perform of `.base i` is the ported perform of
  `i`, for `InvOK i` (retype: R7 (c) `fl4InvokeUntypedV_run`; notification: `sendSignalV_eq_nr`; TCB:
  `invokeTcbV_eq`; CNode: `invokeCnodeV_eq`; the rest: `fl4PerformInvocationV_base`).
* `syscall_congrV`: l4v's `syscall` combinator with a decoder that is `liftME f` of another at the reached
  states, and finalisers that agree through `f`, is the same computation.
* **`fl4HandleInvocationV_eqNR`**: on an `NR` state the extended invocation is `fl4HandleInvocationR`, given
  `OffRoute` at its decode point.

**Named premise `hoff : OffRoute …` [S]** (scope): at every decode point the invocation path reaches from the
state (the looked-up cap, extra caps, the label and message words), the input is not on a `VirtRoute` (the
three virtualization routes that exist without virtualization objects: label 88 on a thread cap, label 60 on a
frame cap, the VT-x retype gate; the other `VirtRoute` cases need a virtualization cap in a slot, impossible on
`NV`), and every invocation the ported decoder returns there is `InvOK`. The three routes are covered against the
extended spec directly instead (route B: `decOKV_thread88_noVirt`, `decOKV_frame60_noVirt`,
`decOKV_untyped_vtxGate`). Not carried from the decoder here (open item): that on `NV` states `VirtRoute`
reduces to those three label/gate conditions, and that `InvOK` follows from the decoder (retype: off the gate the
ported type decode never yields the VCPU at `virtKind = none`; TCB: the vih3 `OkV` carry).

No [J]/[P]/[W]. New file only.
-/
import Fl4Proofs.P3.VirtAwaken
import Fl4Proofs.P3.VirtNvTcb
import Fl4Proofs.P3.VirtTyK6
open Classical

namespace Fl4Proofs.P3.VirtR7e
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvL Fl4Proofs.P3.SInvTY Fl4Proofs.P3.VirtR7b
  Fl4Proofs.P3.VirtR7d Fl4Proofs.P3.VirtAwaken Fl4Proofs.P3.VirtNvTcb

noncomputable section

set_option maxHeartbeats 4000000

/-! ## The invariant -/

/-- **No virtualization cap, no VCPU, no `runningVM` thread.** -/
def NR (σ : State Unit) : Prop := NV σ ∧ NoRunVM σ

theorem nr_of {α : Type} {m : NonDet (State Unit) α} (h1 : IK NVC m) (h2 : IK (TIn NVT) m) (h3 : IK NoRunVM m) :
    IK NR m :=
  fun s hs x hx => ⟨⟨h1 s hs.1.1 x hx, h2 s hs.1.2 x hx⟩, h3 s hs.2 x hx⟩

theorem nr_ofE {ε α : Type} {m : NonDetE (State Unit) ε α} (h1 : IKE NVC m) (h2 : IKE (TIn NVT) m)
    (h3 : IKE NoRunVM m) : IKE NR m :=
  nr_of h1 h2 h3

/-! ## The perform -/

/-- Ported invocations whose extended perform agrees on `NR` states (module docstring). -/
def InvOK : Fl4Invocation → Prop
  | .invokeUntyped (.retype _ _ _ _ t _ _ _) => t ≠ .archObject .vcpuObj
  | .invokeTCB i => TcbCapsOK i
  | _ => True

/-- **The extended perform is the ported one** on an `NR` state, for an `InvOK` invocation. -/
theorem fl4PerformInvocationV_eqNR (onCore : ObjRef → Bool) (blk call don : Bool) (i : Fl4Invocation)
    {s : State Unit} (hs : NR s) (hi : InvOK i) :
    ExceptT.run (fl4PerformInvocationV (Z := Unit) onCore blk call don (.base i)) s =
      ExceptT.run (fl4PerformInvocation blk call don i) s := by
  by_cases hp : PerformSubst i
  · cases i with
    | invokeUntyped ui =>
      obtain ⟨src, reset, base, rb, t, sz, slots, dev⟩ := ui
      show ExceptT.run (fl4InvokeUntypedV (Z := Unit) (.retype src reset base rb t sz slots dev) >>= fun _ =>
          NonDetE.returnOk []) s = ExceptT.run (fl4InvokeUntyped (.retype src reset base rb t sz slots dev) >>= fun _ =>
          NonDetE.returnOk []) s
      exact nde_bind_congr (VirtR7.fl4InvokeUntypedV_run src reset base rb t sz slots dev hi s) fun _ _ _ => rfl
    | invokeNotification ep b =>
      show ExceptT.run (withoutPreemption (sendSignalV (Z := Unit) onCore ep b) >>= fun _ =>
          NonDetE.returnOk []) s = ExceptT.run (withoutPreemption (sendSignal ep b) >>= fun _ =>
          NonDetE.returnOk []) s
      exact nde_bind_congr (run_liftE_congr (sendSignalV_eq_nr onCore hs.2 ep b)) fun _ _ _ => rfl
    | invokeTCB ti => exact invokeTcbV_eq ti hs.1 hi
    | invokeCNode ci =>
      show ExceptT.run (invokeCnodeV (Z := Unit) ci >>= fun _ => NonDetE.returnOk []) s =
        ExceptT.run (invokeCnode ci >>= fun _ => NonDetE.returnOk []) s
      exact nde_bind_congr (invokeCnodeV_eq ci hs.1) fun _ _ _ => rfl
    | _ => exact (hp : False).elim
  · rw [fl4PerformInvocationV_base onCore blk call don i hp]

/-! ## `syscall` -/

theorem nd_bind_assoc' {σ α β γ : Type} (m : NonDet σ α) (f : α → NonDet σ β) (g : β → NonDet σ γ) (s : σ) :
    ((m >>= f) >>= g) s = (m >>= fun x => f x >>= g) s := by
  simp only [nd_bind_apply]
  ext r
  · simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨y, ⟨x, hx, hy⟩, hr⟩; exact ⟨x, hx, y, hy, hr⟩
    · rintro ⟨x, hx, y, hy, hr⟩; exact ⟨y, ⟨x, hx, hy⟩, hr⟩
  · simp only [Set.mem_setOf_eq]
    constructor
    · rintro ((h | ⟨x, hx, h⟩) | ⟨y, ⟨x, hx, hy⟩, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨x, hx, Or.inl h⟩
      · exact Or.inr ⟨x, hx, Or.inr ⟨y, hy, h⟩⟩
    · rintro (h | ⟨x, hx, h | ⟨y, hy, h⟩⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr ⟨x, hx, h⟩)
      · exact Or.inr ⟨y, ⟨x, hx, hy⟩, h⟩

theorem run_liftE_eq {ε α : Type} (m : NonDet (State Unit) α) :
    ExceptT.run (NonDetE.liftE (ε := ε) m) = (m >>= fun a => pure (Except.ok a)) := rfl

/-- **`syscall` with a decoder that is `liftME f` of another** (module docstring). -/
theorem syscall_congrV {α β β' γ : Type} (mF : FMonad Unit α) (hF : Fault → SMonad Unit γ)
    (mE : α → SEMonad Unit β) (mE' : α → SEMonad Unit β') (hE : SyscallError → SMonad Unit γ)
    (fin : β → PMonad Unit γ) (fin' : β' → PMonad Unit γ) (f : β → β') {s : State Unit}
    (hd : ∀ a t, ((Except.ok a : Except Fault α), t) ∈ (ExceptT.run mF s).1 →
      ExceptT.run (mE' a) t = ExceptT.run (NonDetE.liftME f (mE a)) t)
    (hfin : ∀ a t b u, ((Except.ok a : Except Fault α), t) ∈ (ExceptT.run mF s).1 →
      ((Except.ok b : Except SyscallError β), u) ∈ (ExceptT.run (mE a) t).1 →
      ExceptT.run (fin' (f b)) u = ExceptT.run (fin b) u) :
    ExceptT.run (syscall mF hF mE' hE fin') s = ExceptT.run (syscall mF hF mE hE fin) s := by
  unfold syscall
  refine nde_bind_congr rfl fun r t hr => ?_
  have hr' := mem_run_liftE' hr
  cases r with
  | error e => rfl
  | ok a =>
    dsimp only
    rw [ExceptT.run_bind, ExceptT.run_bind]
    unfold withoutPreemption
    rw [run_liftE_eq, run_liftE_eq, nd_bind_assoc', nd_bind_assoc', nd_bind_eq_of (hd a t hr')]
    unfold NonDetE.liftME
    rw [ExceptT.run_bind, nd_bind_assoc']
    refine nd_bind_congr_on _ _ _ t fun y hy => ?_
    obtain ⟨r2, u⟩ := y
    cases r2 with
    | error e =>
      simp only [ExceptT.bindCont, nd_pure_bind] <;> rfl
    | ok b =>
      simp only [ExceptT.bindCont, nd_pure_bind, ExceptT.run_pure]
      exact hfin a t b u hr' hy

/-- `liftME` over a bind. -/
theorem run_liftME_bind {ε γ β β' : Type} (m : NonDetE (State Unit) ε γ) (k : γ → NonDetE (State Unit) ε β)
    (f : β → β') (t : State Unit) :
    ExceptT.run (NonDetE.liftME f (m >>= k)) t = ExceptT.run (m >>= fun x => NonDetE.liftME f (k x)) t := by
  unfold NonDetE.liftME
  simp only [ExceptT.run_bind]
  rw [nd_bind_assoc']
  refine nd_bind_congr_on _ _ _ t fun y _ => ?_
  obtain ⟨r, u⟩ := y
  cases r with
  | error e => simp only [ExceptT.bindCont, nd_pure_bind]
  | ok x => simp only [ExceptT.bindCont, ExceptT.run_bind]

/-! ## The invocation -/

/-- The lookup part of the invocation path (`fl4HandleInvocationR`'s first `syscall` argument). -/
def lookupPart (thread : ObjRef) (cptr : CapRef) (info : MessageInfo) :
    FMonad Unit (CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef) := do
  let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot thread cptr
  let buffer ← NonDetE.liftE <| lookupIpcBuffer false thread
  let extracaps ← lookupExtraCaps thread buffer info
  NonDetE.returnOk (slot, cap, extracaps, buffer)

/-- A decode point of the invocation path from `s`: the message info, the looked-up slot / cap / extra caps /
buffer, the message words and the decode state. -/
def DecPt (cptr : CapRef) (s : State Unit) (info : MessageInfo)
    (a : CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef) (args : List Data) (u : State Unit) : Prop :=
  ∃ s1 t, (info, s1) ∈ (getMessageInfo (Z := Unit) s.curThread s).1 ∧
    ((Except.ok a : Except Fault _), t) ∈ (ExceptT.run (lookupPart s.curThread cptr info) s1).1 ∧
    (args, u) ∈ (getMrs (Z := Unit) s.curThread a.2.2.2 info t).1

/-- **The invocation's decode points are off the virtualization routes** (the [S] premise, module docstring). -/
def OffRoute (fp : Bool) (cptr : CapRef) (s : State Unit) : Prop :=
  ∀ info a args u, DecPt cptr s info a args u →
    ¬ VirtRoute fp info.miLabel args a.2.1 a.2.2.1 ∧
    ∀ i v, ((Except.ok i : Except SyscallError Fl4Invocation), v) ∈
      (ExceptT.run (fl4DecodeInvocation (Z := Unit) fp info.miLabel args cptr a.1 a.2.1 a.2.2.1 a.2.2.2) u).1 →
      InvOK i

theorem nr_getMessageInfo (t : ObjRef) : IK NR (getMessageInfo (Z := Unit) t) :=
  nr_of (SInvV.hv_getMessageInfo (P := NVC) t) (ty_getMessageInfo t) (ns_getMessageInfo t)

theorem ik_lookupPart {P : State Unit → Prop} (t : ObjRef) (cptr : CapRef) (info : MessageInfo)
    (hc : IKE P (capFaultOnFailure (Z := Unit) (ofBl cptr) false (lookupCapAndSlot t cptr)))
    (hb : IK P (lookupIpcBuffer (Z := Unit) false t)) (he : ∀ b, IKE P (lookupExtraCaps (Z := Unit) t b info)) :
    IKE P (lookupPart t cptr info) := by
  unfold lookupPart
  refine ike_bind hc fun p => ?_
  obtain ⟨cap, slot⟩ := p
  exact ike_bind (ike_liftE hb) fun _ => ike_bind (he _) fun _ => ike_returnOk _

theorem nr_lookupPart (t : ObjRef) (cptr : CapRef) (info : MessageInfo) : IKE NR (lookupPart t cptr info) :=
  nr_ofE
    (ik_lookupPart t cptr info (SInvV.hv_capFaultOnFailure (P := NVC) _ _ _ (SInvV.hv_lookupCapAndSlot _ _))
      (SInvV.hv_lookupIpcBuffer _ _) fun _ => SInvV.hv_lookupExtraCaps _ _ _)
    (ik_lookupPart t cptr info (ty_capFaultOnFailure _ _ _ (ty_lookupCapAndSlot _ _))
      (ty_lookupIpcBuffer _ _) fun _ => ty_lookupExtraCaps _ _ _)
    (ik_lookupPart t cptr info (ns_capFaultOnFailure _ _ _ (ns_lookupCapAndSlot _ _))
      (ns_lookupIpcBuffer _ _) fun _ => ns_lookupExtraCaps _ _ _)

theorem nr_getMrs (t : ObjRef) (b : Option ObjRef) (info : MessageInfo) : IK NR (getMrs (Z := Unit) t b info) :=
  nr_of (SInvV.hv_getMrs (P := NVC) t b info) (ty_getMrs t b info) (ns_getMrs t b info)

theorem nr_fl4Decode (fp : Bool) (l : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr) (c : Cap)
    (ex : List (Cap × CslotPtr)) (b : Option ObjRef) : IKE NR (fl4DecodeInvocation (Z := Unit) fp l args ci sl c ex b) :=
  nr_ofE (SInvV.hv_fl4DecodeInvocation (P := NVC) fp l args ci sl c ex b) (ty_fl4DecodeInvocation fp l args ci sl c ex b)
    (ns_fl4DecodeInvocation fp l args ci sl c ex b)

theorem nr_setRestart (t : ObjRef) : IK NR (setThreadState (Z := Unit) t .restart) :=
  nr_of (SInvV.hv_setThreadState (P := NVC) t _) (ty_setThreadState t _) (ns_setThreadState t _ (by decide))

/-- **The extended invocation is `fl4HandleInvocationR`** on an `NR` state, off the virtualization routes
(`hoff` [S], module docstring). -/
theorem fl4HandleInvocationV_eqNR (onCore : ObjRef → Bool) (rep calling blocking don fp : Bool) (cptr : CapRef)
    {s : State Unit} (hs : NR s) (hoff : OffRoute fp cptr s) :
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
    rw [fl4DecodeInvocationV_base _ _ _ _ _ _ _ _
      (hoff info (slot, cap, ex, buf) args u ⟨s1, t, h1', ha, hu'⟩).1]
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
      have hInv := (hoff info (slot, cap, ex, buf) args t2 ⟨s1, t, h1', ha, hr1'⟩).2 b u hb'
      have nu : NR u := nr_fl4Decode _ _ _ _ _ _ _ _ t2 n2 _ hb'
      refine nde_bind_congr rfl fun _ v hv => ?_
      have nv : NR v := nr_setRestart _ u nu _ (mem_run_liftE' hv)
      exact nde_bind_congr (fl4PerformInvocationV_eqNR onCore blocking calling don b nv hInv) fun _ _ _ => rfl

end

end Fl4Proofs.P3.VirtR7e
