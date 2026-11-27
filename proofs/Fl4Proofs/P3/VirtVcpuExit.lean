/-
P3x for virtualization, spec side (line virt, gen 7 item 2; proofs/VIRT-PLAN.md §10 "Remaining (R7)"):
**the VM-exit entry `fl4VcpuExitV` on `NR` states** is a composition of ported operations, and keeps `NR`.

`fl4VcpuExitV onCore irq stalled` (Ext/VirtKernel, FL4 `handle_vcpu_exit`) is: unless stalled, `update_time_stamp`,
`vmCheck` of the current thread, `check_budget`; then the interrupt (`handleInterruptV`) if one is pending; then the
extended exit `fl4KernelExitV`. On a state with no `runningVM` thread whose current thread is a TCB, `vmCheck` is a
no-op (Ext/VirtP3x `vmCheck_not_runningVM`), `handleInterruptV` is `handleInterrupt` (VirtAwaken) and the exit is
the ported `fl4Awaken; schedule; activateThread` (VirtAwaken `fl4KernelExitV_eq'`).

* `CtTcb`, `ctTcb_updateTimeStamp`, `vmCheck_nr`, `exitPre_eq` (the pre-interrupt part).
* **`fl4VcpuExitV_eqNR`**: `fl4VcpuExitV onCore irq stalled σ` = the ported composition
  `unless stalled (update_time_stamp; check_budget); handle_interrupt?; fl4Awaken; schedule; activateThread`.
* **`nr_fl4VcpuExitV`**: every outcome of the VM-exit entry from such a state is `NR`.

Named premise:
* **`hct : CtTcb σ` [S]**: the current thread is a TCB at the VM-exit entry (l4v `cur_tcb`; without it the
  extended `vmCheck` reads a missing TCB and fails, while the ported composition has no such read). On FL4 the
  VM-exit entry is only reached from a thread that was running a guest, so an `NR` state is outside its real
  domain; the theorem says the extended entry adds nothing there.

No [J]/[P]/[W]. New file only.
-/
import Fl4Proofs.P3.VirtNvK2
open Classical

namespace Fl4Proofs.P3.VirtVcpuExit
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.VirtR7 Fl4Proofs.P3.VirtR7b Fl4Proofs.P3.VirtR7d Fl4Proofs.P3.VirtAwaken
  Fl4Proofs.P3.VirtR7e Fl4Proofs.P3.VirtNvK2 Fl4Proofs.P3.SInvTY

noncomputable section

/-- The current thread is a TCB. -/
def CtTcb (σ : State Unit) : Prop := ∃ x, σ.kheap σ.curThread = some (.tcb x)

theorem ctTcb_updateTimeStamp : SInv.IK CtTcb (updateTimeStamp (Z := Unit)) := by
  unfold updateTimeStamp
  refine SInv.ik_bind (SInv.ik_gets _) fun _ => SInv.ik_bind (SInv.ik_doMachineOp (fun _ _ h => h) _) fun _ => ?_
  refine SInv.ik_bind (SInv.ik_pure _) fun _ => SInv.ik_bind (SInv.ik_modify fun _ h => h) fun _ => ?_
  refine SInv.ik_bind (SInv.ik_modify fun _ h => h) fun _ => SInv.ik_bind (SInv.ik_gets _) fun _ => ?_
  exact SInv.ik_when _ (SInv.ik_ite _ (SInv.ik_modify fun _ h => h) (SInv.ik_modify fun _ h => h))

/-- `vmCheck` of the current thread is a no-op without a `runningVM` thread. -/
theorem vmCheck_nr {σ : State Unit} (hn : NoRunVM σ) (hc : CtTcb σ) :
    vmCheck (Z := Unit) σ.curThread σ = ({((), σ)}, False) := by
  obtain ⟨x, hk⟩ := hc
  exact vmCheck_not_runningVM hk (hn _ _ hk)

/-- The pre-interrupt part of the VM exit. -/
theorem exitPre_eq {σ : State Unit} (hn : NoRunVM σ) (hc : CtTcb σ) :
    (do
      updateTimeStamp (Z := Unit)
      let ct ← NonDet.gets fun s : State Unit => s.curThread
      vmCheck ct
      let _ ← checkBudget
      pure () : NonDet (State Unit) Unit) σ =
    (do
      updateTimeStamp (Z := Unit)
      let _ ← checkBudget
      pure () : NonDet (State Unit) Unit) σ := by
  refine nd_bind_congr_on _ _ _ σ fun y hy => ?_
  have hn' : NoRunVM y.2 := SInv.ns_updateTimeStamp σ hn y hy
  have hc' : CtTcb y.2 := ctTcb_updateTimeStamp σ hc y hy
  rw [nd_bind_single (show NonDet.gets (fun s : State Unit => s.curThread) y.2 = ({(y.2.curThread, y.2)}, False)
    from rfl)]
  rw [nd_bind_single (vmCheck_nr hn' hc')]

/-- **The VM-exit entry on an `NR` state is a composition of ported operations** (premise `hct` [S]). -/
theorem fl4VcpuExitV_eqNR (onCore : ObjRef → Bool) (irq : Option Irq) (stalled : Bool) {σ : State Unit}
    (hs : NR σ) (hct : CtTcb σ) :
    fl4VcpuExitV (Z := Unit) onCore irq stalled σ =
      (NonDet.unless stalled (do updateTimeStamp (Z := Unit); let _ ← checkBudget; pure ()) >>= fun _ =>
        (match irq with
          | some i => handleInterrupt (Z := Unit) i
          | none => pure ()) >>= fun _ =>
        fl4Awaken (Z := Unit) >>= fun _ => schedule (Z := Unit) >>= fun _ => activateThread (Z := Unit)) σ := by
  have hU : NonDet.unless stalled (do
        updateTimeStamp (Z := Unit)
        let ct ← NonDet.gets fun s : State Unit => s.curThread
        vmCheck ct
        let _ ← checkBudget
        pure ()) σ =
      NonDet.unless stalled (do updateTimeStamp (Z := Unit); let _ ← checkBudget; pure ()) σ := by
    cases stalled with
    | true => rfl
    | false => exact exitPre_eq hs.2 hct
  have hnU : SInv.IK NoRunVM (NonDet.unless stalled (do updateTimeStamp (Z := Unit); let _ ← checkBudget; pure ())) :=
    SInv.ik_unless _ (SInv.ik_bind SInv.ns_updateTimeStamp fun _ => SInv.ik_bind SInv.ns_checkBudget fun _ =>
      SInv.ik_pure _)
  cases irq with
  | some i =>
    unfold fl4VcpuExitV
    rw [nd_bind_eq_of hU]
    refine nd_bind_congr_on _ _ _ σ fun y hy => ?_
    have hn1 : NoRunVM y.2 := hnU σ hs.2 y hy
    dsimp only
    rw [nd_bind_eq_of (handleInterruptV_eq onCore hn1 i)]
    exact nd_bind_congr_on _ _ _ y.2 fun z hz =>
      fl4KernelExitV_eq' onCore (SInv.ns_handleInterrupt i y.2 hn1 z hz)
  | none =>
    unfold fl4VcpuExitV
    rw [nd_bind_eq_of hU]
    refine nd_bind_congr_on _ _ _ σ fun y hy => ?_
    have hn1 : NoRunVM y.2 := hnU σ hs.2 y hy
    first
      | exact fl4KernelExitV_eq' onCore hn1
      | (simp only [nd_pure_bind]; exact fl4KernelExitV_eq' onCore hn1)
      | (rw [nd_bind_single (rfl : (pure () : NonDet (State Unit) Unit) y.2 = ({((), y.2)}, False)),
            nd_bind_single (rfl : (pure () : NonDet (State Unit) Unit) y.2 = ({((), y.2)}, False))]
         exact fl4KernelExitV_eq' onCore hn1)

/-- **The VM-exit entry keeps `NR`** (premise `hct` [S]). -/
theorem nr_fl4VcpuExitV (onCore : ObjRef → Bool) (irq : Option Irq) (stalled : Bool) {σ : State Unit}
    (hs : NR σ) (hct : CtTcb σ) : ∀ y ∈ (fl4VcpuExitV (Z := Unit) onCore irq stalled σ).1, NR y.2 := by
  rw [fl4VcpuExitV_eqNR onCore irq stalled hs hct]
  have hcb : SInv.IK NR (checkBudget (Z := Unit)) :=
    nr_of Fl4Proofs.P3.VirtNvcW.nvc_checkBudget ty_checkBudget SInv.ns_checkBudget
  have hU : SInv.IK NR (NonDet.unless stalled (do updateTimeStamp (Z := Unit); let _ ← checkBudget; pure ())) :=
    SInv.ik_unless _ (SInv.ik_bind nr_updateTimeStamp fun _ => SInv.ik_bind hcb fun _ => SInv.ik_pure _)
  cases irq with
  | some i =>
    exact SInv.ik_bind hU (fun _ => SInv.ik_bind
      (nr_of (SInvV.hv_handleInterrupt i) (ty_handleInterrupt i) (SInv.ns_handleInterrupt i))
      fun _ => nr_kernelExit) σ hs
  | none => exact SInv.ik_bind hU (fun _ => SInv.ik_bind (SInv.ik_pure ()) fun _ => nr_kernelExit) σ hs

end

end Fl4Proofs.P3.VirtVcpuExit
