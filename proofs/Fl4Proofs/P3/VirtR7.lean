/-
P3x for virtualization, spec side (line virt, gen 2; proofs/VIRT-PLAN.md §10 "Remaining (R7)" (a), (c), (d)):
the extended operations are the ported ones where no thread runs a guest and no VCPU exists.

Spec: `Fl4Spec/Ext/VirtEntry` (`sendSignalV`, seL4 `sendSignal` with `CONFIG_VTX`, `src/object/notification.c`;
`isVmEnterCall`, FL4 `handle_unknown_syscall`'s `SysVMEnter` branch, `crates/fl4-core/src/syscall.rs`),
`Fl4Spec/Ext/VirtFinalise` (`fl4InvokeUntypedV`, FL4 `untyped.rs` + `arch/x86_64/objects.rs` `vcpu::init`),
against the ported l4v `Ipc_A.send_signal` (`sendSignal`) and `Retype_A.invoke_untyped` (`fl4InvokeUntyped`,
`Ext/Invocation`). Nothing of the port changes.

* (a) `sendSignalV_eq`: on a notification whose bound thread (if any) is a TCB not `runningVM`, `sendSignalV`
  is `sendSignal` (outcome for outcome, failure included).
* (c) `fl4InvokeUntypedV_run`: a retype to any type but the VCPU is the ported retype (`NonDet.when false`).
  With the generic `nde_bind_liftE_unit` (a NonDetE computation followed by `liftE (pure ())`).
* (d, part) `isVmEnterCall_noVirt`: without virtualization objects no unknown syscall is a VMEnter, so
  `fl4HandleEventV`'s unknown-syscall branch is the ported `handleEvent`. (`vmCheck` of a non-`runningVM` thread
  is `VirtP3x.vmCheck_not_runningVM`.)

Premises (named hypotheses): `hk` (the notification exists), `hb` (its bound thread is a TCB not `runningVM`:
on a NoVirt state no thread is `runningVM`, VIRT-PLAN §10 (d); an invariant fact to be supplied by the R7
composition), `h` (the retype type is not the VCPU), `hn` (`NoVirtObjects`). No [J]/[P]/[W]; new file only.
-/
import Fl4Proofs.P3.NtfnSpec
import Fl4Proofs.P3.Lookup
import Fl4Spec.Ext.VirtP3x
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtR7
open Fl4Spec Classical

noncomputable section

/-- **R7 (a)**: `sendSignalV = sendSignal` when the bound thread is not `runningVM` (module docstring). -/
theorem sendSignalV_eq (onCore : ObjRef → Bool) {σ : State Unit} {n : ObjRef} {x : Notification} (b : Badge)
    (hk : σ.kheap n = some (.notification x))
    (hb : ∀ t, x.ntfnBoundTcb = some t → ∃ tcb, σ.kheap t = some (.tcb tcb) ∧ tcb.tcbState ≠ .runningVM) :
    sendSignalV (Z := Unit) onCore n b σ = sendSignal n b σ := by
  unfold sendSignalV
  rw [Notif.nd_bind_one (Notif.getNotification_eq hk)]
  try dsimp only
  rcases ho : x.ntfnObj with _ | _ | _ <;> rcases hbt : x.ntfnBoundTcb with _ | t <;>
    (try rw [ho]) <;> (try rw [hbt])
  all_goals try (with_reducible rfl)
  obtain ⟨tcb, hkt, hs⟩ := hb t hbt
  show (getThreadState (Z := Unit) t >>= fun st =>
    if st = .runningVM ∧ onCore t = true then _ else sendSignal n b) σ = _
  rw [Notif.nd_bind_one (Notif.getThreadState_eq hkt)]
  simp only [hs, false_and, ↓reduceIte]

/-- A bind whose continuation returns each outcome of `m` unchanged. -/
theorem nd_bind_pure_out {σ α : Type} (m : NonDet σ α) (k : α → NonDet σ α) (s : σ)
    (hk : ∀ x ∈ (m s).1, k x.1 x.2 = ({x}, False)) : (m >>= k) s = m s := by
  rw [nd_bind_apply]
  refine Prod.ext (Set.ext fun r => ?_) (propext ?_)
  · simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, hx, hr⟩
      rw [hk x hx] at hr
      rw [Set.mem_singleton_iff.1 (hr : r ∈ ({x} : Set (α × σ)))]
      exact hx
    · intro hr
      refine ⟨r, hr, ?_⟩
      rw [hk r hr]
      exact Set.mem_singleton r
  · constructor
    · rintro (h | ⟨x, hx, h⟩)
      · exact h
      · rw [hk x hx] at h
        exact (h : False).elim
    · intro h
      exact Or.inl h

/-- A NonDetE computation followed by `liftE (pure ())` is the computation. -/
theorem nde_bind_liftE_unit {ε : Type} (m : NonDetE (State Unit) ε Unit) (s : State Unit) :
    (m >>= fun _ => NonDetE.liftE (NonDet.pure ())).run s = m.run s := by
  show NonDet.bind (m.run) (ExceptT.bindCont fun _ => NonDetE.liftE (NonDet.pure ())) s = m.run s
  refine nd_bind_pure_out _ _ s ?_
  rintro ⟨r, s'⟩ -
  cases r with
  | error e => rfl
  | ok u =>
    cases u
    show (Except.ok <$> NonDet.pure () : NonDet (State Unit) (Except ε Unit)) s' = _
    first
      | rfl
      | (show (NonDet.pure () >>= fun a => NonDet.pure (Except.ok a) : NonDet (State Unit) (Except ε Unit)) s' = _
         rw [nd_bind_single (show (NonDet.pure () : NonDet (State Unit) Unit) s' = ({((), s')}, False) from rfl)]
         rfl)

/-- **R7 (c)**: a retype to any type but the VCPU is the ported retype (module docstring). -/
theorem fl4InvokeUntypedV_run (src : CslotPtr) (reset : Bool) (base rb : ObjRef) (t : ApiObjectType) (sz : Nat)
    (slots : List CslotPtr) (dev : Bool) (h : t ≠ .archObject .vcpuObj) (σ : State Unit) :
    (fl4InvokeUntypedV (Z := Unit) (.retype src reset base rb t sz slots dev)).run σ =
      (fl4InvokeUntyped (.retype src reset base rb t sz slots dev)).run σ := by
  unfold fl4InvokeUntypedV
  simp only [NonDet.when, h, ↓reduceIte]
  exact nde_bind_liftE_unit _ σ

/-- **R7 (d), the VMEnter test**: without virtualization objects no unknown syscall is a VMEnter. -/
theorem isVmEnterCall_noVirt {σ : State Unit} (hn : NoVirtObjects σ) (num : Nat) :
    isVmEnterCall num σ = false := by
  unfold isVmEnterCall
  simp [hn.tcbVcpuOf]

/-- So `fl4HandleEventV`'s unknown-syscall branch is the ported `handleEvent` there. -/
theorem fl4HandleEventV_unknown_noVirt (onCore : ObjRef → Bool) (rep : Bool) {σ : State Unit}
    (hn : NoVirtObjects σ) (num : Nat) :
    (fl4HandleEventV (Z := Unit) onCore rep (.unknownSyscall num)).run σ =
      (handleEvent (Z := Unit) (.unknownSyscall num)).run σ := by
  unfold fl4HandleEventV
  rw [ExceptT.run_bind]
  have hg : (NonDetE.liftE (ε := Unit) (NonDet.gets (isVmEnterCall (Z := Unit) num))).run σ =
      ({(.ok false, σ)}, False) := by
    refine run_liftE ?_
    show ({(isVmEnterCall (Z := Unit) num σ, σ)}, False) = _
    rw [isVmEnterCall_noVirt hn num]
  rw [nd_bind_single hg]
  rfl

end

end Fl4Proofs.P3.VirtR7
