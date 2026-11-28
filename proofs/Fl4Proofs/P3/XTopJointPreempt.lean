/-
P3 (DESIGN.md §9): **the preemption path at `J`** (KENTRY-PLAN item 7):
FL4's `after_invocation (Err _)` (`mcs_preemption_point`, `take_pending_irq`,
`check_interrupt`) against the spec's `preemption_path`, from every `JAtPre`
state (XTopJointPPH's `jAtPre_hole`: a `JHole`).

* `JHole.msAr`: a `JHole` with another machine state (same memory) and an
  arch state keeping `AR` is a `JHole` (the IRQ check).
* `JHoleAt`: some `JHole` ends at the state (what the path keeps).
* `mem_pp_sched` / `mem_pp_charge` (spec): outcomes of `preemption_path`
  from an outcome of its budget part (`check_budget`, or `charge_budget
  consumed false` for an active SC) and of `maybe_handle_interrupt true`.
* `JHole.mcsPPJ`: `mcs_preemption_point` from a `JHole` under `PPCov`
  (`CurInv`, a non-idle current thread, no switch to it pending, `NoTmoSend`)
  or `PPCovT` (`JHole.checkBudgetT`'s case: an endpoint timeout handler on an
  idle or sending endpoint, non-RR SC, the current thread running or
  restarting, unqueued, no reschedule pending):
  schedulable → `check_budget` (`true`: nothing changes, `check_budgetT` /
  `checkBudget_suff`; `false`: `JHole.checkBudgetF` / `JHole.checkBudgetT`,
  the current thread's timeout fault blocking it), not schedulable →
  `charge_budget consumed false` (`JHole.chargeBudgetJ`; the SC is active:
  `CurInv.active`, `curSc ≠ idleSc`); the third FL4 branch (inactive SC) is
  unreachable under either.
* `IrqPlat` [P] (M4): FL4's `take_pending_irq` is the spec's
  `getActiveIRQ true` (an oracle of the spec's machine state; `NO_IRQ` ↔
  `none`, otherwise the same line number, not masked in the spec), keeping
  `AR`; one core: no IPI line is pending (`noIpi`); `ack_irq` keeps `AR`.
* `JIrqHyp` [W] (l4v `handle_interrupt_corres`): `handle_interrupt` of an
  unmasked line from a `JHoleAt` state refines `handle_interrupt` (or the
  spec fails: e.g. an inactive line, where FL4 masks it; l4v excludes it by
  `valid_irq_masks`, which `JHoleAt` does not carry), `XTopAt`
  after (not `JHoleAt`: a `JHole`'s spec state differs from its base only in
  the machine state and the time words, while the timer branch sets
  `reprogramTimer` and a signal changes the heap); the IPI lines 126/127
  excluded (`IrqPlat.noIpi`). Proved downstream: XTopJointIrq's
  `jIrqHyp_of` (the signal from a hole that is not `JAtZ` named there,
  `JIrqSigHyp` [W]).
* `JHole.afterInvJ`: `after_invocation (Err _)` from a `JHole` under `PPCov ∨ PPCovT`
  refines `preemption_path` (`PPQ`: the spec fails, or an outcome with
  `JHoleAt` after when no line is pending,
  `XTopAt` after `JIrqHyp` for a pending line).
* `JPreemptRestHyp` [W]: `hPre` at the `JHoleAt` states outside `PPCov ∨
  PPCovT` (a reschedule pending without `CurInv`, the idle thread current, a
  pending switch to the current thread, an endpoint timeout handler with a
  non-RR SC and waiting receivers / a reschedule pending / a queued or
  RUNNING_VM current thread).
* `hPre_of`: `invoke_afterJ`'s `hPre` for `Q := PPQ` from the platform facts
  [P], `JIrqHyp` [W] and `JPreemptRestHyp` [W]; `dispatch_invokeJP` /
  `dispatch_invokeJEP` are `dispatch_invokeJ` / `dispatch_invokeJE` with it
  (no `hPre`).
-/
import Fl4Proofs.P3.XTopJointPPH
import Fl4Proofs.P3.XTopJointBudgetT
import Fl4Proofs.P3.XTopJointDispatch
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section Spec
open Fl4Spec

/-- **An outcome of `preemption_path`, schedulable current thread**: an
outcome of `check_budget`, then of `maybe_handle_interrupt true`. -/
theorem mem_pp_sched {σ σ' : State Unit} {b : Bool} {y : Unit × State Unit}
    (hs : schedulable σ.curThread σ = true) (h1 : (b, σ') ∈ (checkBudget (Z := Unit) σ).1)
    (h2 : y ∈ (maybeHandleInterrupt (Z := Unit) true σ').1) : y ∈ (preemptionPath (Z := Unit) σ).1 := by
  unfold preemptionPath
  refine mem_bind_nd (x := (σ.curThread, σ)) rfl (mem_bind_nd (x := (schedulable σ.curThread σ, σ)) rfl ?_)
  show y ∈ ((if schedulable σ.curThread σ = true then (_ : SMonad Unit Unit) else _) σ).1
  rw [if_pos hs]
  exact mem_bind_nd h1 h2

/-- **An outcome of `preemption_path`, current thread not schedulable, active
current SC**: an outcome of `charge_budget consumed false`, then of
`maybe_handle_interrupt true`. -/
theorem mem_pp_charge {σ σ' : State Unit} {y : Unit × State Unit}
    (hs : schedulable σ.curThread σ = false)
    (hga : getScActive (Z := Unit) σ.curSc σ = ({(true, σ)}, False))
    (h1 : ((), σ') ∈ (chargeBudget (Z := Unit) σ.consumedTime false σ).1)
    (h2 : y ∈ (maybeHandleInterrupt (Z := Unit) true σ').1) : y ∈ (preemptionPath (Z := Unit) σ).1 := by
  unfold preemptionPath
  refine mem_bind_nd (x := (σ.curThread, σ)) rfl (mem_bind_nd (x := (schedulable σ.curThread σ, σ)) rfl ?_)
  show y ∈ ((if schedulable σ.curThread σ = true then (_ : SMonad Unit Unit) else _) σ).1
  rw [if_neg (by simp [hs])]
  refine mem_bind_nd (x := (σ.curSc, σ)) rfl (mem_bind_nd (x := (true, σ)) (by rw [hga]; rfl) ?_)
  show y ∈ ((if true = true then (_ : SMonad Unit Unit) else _) σ).1
  rw [if_pos rfl]
  exact mem_bind_nd (x := (σ.consumedTime, σ)) rfl (mem_bind_nd h1 h2)

theorem fail_pp_sched {σ σ' : State Unit} {b : Bool}
    (hs : schedulable σ.curThread σ = true) (h1 : (b, σ') ∈ (checkBudget (Z := Unit) σ).1)
    (h2 : (maybeHandleInterrupt (Z := Unit) true σ').2) : (preemptionPath (Z := Unit) σ).2 := by
  unfold preemptionPath
  refine Or.inr ⟨(σ.curThread, σ), rfl, Or.inr ⟨(schedulable σ.curThread σ, σ), rfl, ?_⟩⟩
  show ((if schedulable σ.curThread σ = true then (_ : SMonad Unit Unit) else _) σ).2
  rw [if_pos hs]
  exact Or.inr ⟨_, h1, h2⟩

theorem fail_pp_charge {σ σ' : State Unit}
    (hs : schedulable σ.curThread σ = false)
    (hga : getScActive (Z := Unit) σ.curSc σ = ({(true, σ)}, False))
    (h1 : ((), σ') ∈ (chargeBudget (Z := Unit) σ.consumedTime false σ).1)
    (h2 : (maybeHandleInterrupt (Z := Unit) true σ').2) : (preemptionPath (Z := Unit) σ).2 := by
  unfold preemptionPath
  refine Or.inr ⟨(σ.curThread, σ), rfl, Or.inr ⟨(schedulable σ.curThread σ, σ), rfl, ?_⟩⟩
  show ((if schedulable σ.curThread σ = true then (_ : SMonad Unit Unit) else _) σ).2
  rw [if_neg (by simp [hs])]
  refine Or.inr ⟨(σ.curSc, σ), rfl, Or.inr ⟨(true, σ), by rw [hga]; rfl, ?_⟩⟩
  show ((if true = true then (_ : SMonad Unit Unit) else _) σ).2
  rw [if_pos rfl]
  exact Or.inr ⟨(σ.consumedTime, σ), rfl, Or.inr ⟨_, h1, h2⟩⟩

theorem checkBudget_suff {σ : State Unit} (hnd : numDomains = 1)
    (hb : getScRefillSufficient (Z := Unit) σ.curSc σ.consumedTime σ = ({(true, σ)}, False)) :
    checkBudget (Z := Unit) σ = ({(true, σ)}, False) := by
  unfold checkBudget
  rw [nd_gets_bind, nd_gets_bind, nd_bind_one hb]
  have e : isCurDomainExpired σ = false := by simp [isCurDomainExpired, hnd]
  show (do let domExp ← NonDet.gets isCurDomainExpired; return !domExp) σ = _
  rw [nd_gets_bind, e]; rfl

/-- `maybe_handle_interrupt` with no pending line. -/
theorem mem_maybeHandle_none {σ σ' : State Unit}
    (h : doMachineOp (Z := Unit) (getActiveIRQ true) σ = ({(none, σ')}, False)) :
    ((), σ') ∈ (maybeHandleInterrupt (Z := Unit) true σ).1 := by
  unfold maybeHandleInterrupt
  exact mem_bind_nd (x := (none, σ')) (by rw [h]; rfl) rfl

/-- `maybe_handle_interrupt` with a pending line. -/
theorem mem_maybeHandle_some {σ σ' : State Unit} {i : Irq} {z : Unit × State Unit}
    (h : doMachineOp (Z := Unit) (getActiveIRQ true) σ = ({(some i, σ')}, False))
    (hz : z ∈ (handleInterrupt (Z := Unit) i σ').1) :
    z ∈ (maybeHandleInterrupt (Z := Unit) true σ).1 := by
  unfold maybeHandleInterrupt
  exact mem_bind_nd (x := (some i, σ')) (by rw [h]; rfl) hz

end Spec

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- **A `JHole` with another machine state and arch state** (module docstring). -/
theorem JHole.msAr {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (ms : Fl4Spec.MachineState) (a' : A)
    (hum : ms.underlyingMemory = σ.machineState.underlyingMemory)
    (hAR : AR a σ.archState.x64CurrentCr3 → AR a' σ.archState.x64CurrentCr3) :
    JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a' { σ with machineState := ms } := by
  have J := Hh.j0
  obtain ⟨ms0, t, c, hum0, e⟩ := Hh.spec
  have hX := Hh.xtop
  have hS := hX.fin.1.1.1
  have hR := hX.fin.1.1.2.2.1
  have hARh : AR a σ.archState.x64CurrentCr3 := hX.fin.1.1.2.2.2.2.2.2
  have hum' : ms.underlyingMemory = σ0.machineState.underlyingMemory := by
    rw [hum, e]; exact hum0
  have earch : σ.archState = σ0.archState := by rw [e]
  have hK : ScTKw (fun _ => False) σ0 { σ with machineState := ms } := by
    subst e
    exact ⟨fun p => OTK.refl _ _, hum', rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hS2 : SchedRel st Z.N Z.T Z.C Z.c s { σ with machineState := ms } :=
    hS.spec_congr rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hR2 : NtfnStateRel Z.N Z.T (L.mem s) { σ with machineState := ms } := ⟨hR.ntfn, hR.tcb⟩
  have hwT : P1.WritesIn st s0 s (TFoot st Z.T Z.N Z.C Z.c s0 σ0) := WritesIn.tfoot_of_kfoot Hh.ws
  have hX' : XTopAt (L := L) AR Z s a' { σ with machineState := ms } :=
    xtop_sc_step J.xtop J.ip J.nk hwT (ct := σ0.curThread) (hK.mono fun _ h => h.elim) hS2 hR2
      fun _ => by rw [← earch]; exact hAR hARh
  exact ⟨J, ⟨ms, t, c, hum', by rw [e]⟩, Hh.ws, hX', Hh.nsc, Hh.inv.congr rfl rfl rfl rfl,
    Hh.cur.imp id fun h => h.congr rfl rfl rfl rfl, Hh.act, Hh.blk, Hh.dbg, Hh.dbgK⟩

variable (arI) in
/-- (f6) **`JHoleAt` with no exempt slot at the hole's ghosts** (`VxE Z`): what the preemption
path carries (its outcomes become kernel exits, where `JAt` asks `VxE`). -/
def JHoleAtV (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s0 : S) (a0 : A)
    (σ0 : Fl4Spec.State Unit), JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ ∧ VxE Z

/-- **The cases of the preemption path proved here**: `CurInv`, the current
thread not idle, no switch to it pending, no timeout fault raisable. -/
def PPCov (σ : Fl4Spec.State Unit) : Prop :=
  CurInv σ ∧ σ.curThread ≠ σ.idleThread ∧ σ.schedulerAction ≠ .switchThread σ.curThread ∧ NoTmoSend σ

/-- **The endpoint-timeout-handler case of the preemption path proved here**
(`JHole.checkBudgetT`'s conditions): `CurInv`, the current thread not idle,
running or restarting, not queued, no reschedule pending, an endpoint cap as
its timeout handler on an idle or sending endpoint, a non-RR current SC. -/
def PPCovT (σ : Fl4Spec.State Unit) : Prop :=
  CurInv σ ∧ σ.curThread ≠ σ.idleThread ∧ σ.schedulerAction = .resumeCurThread ∧
    (∀ d p, σ.curThread ∉ σ.readyQueues d p) ∧
    (∀ x n, σ.kheap σ.curSc = some (.schedContext x n) → x.scPeriod ≠ 0) ∧
    ∃ (xt : Fl4Spec.Tcb) (p bd : Fl4Spec.Word) (r : Fl4Spec.CapRights),
      σ.kheap σ.curThread = some (.tcb xt) ∧ (xt.tcbState = .running ∨ xt.tcbState = .restart) ∧
      xt.tcbTimeoutHandler = .endpointCap p bd r ∧ ∀ xe, σ.kheap p = some (.endpoint xe) → Endp.CanBlock false xe

variable (arI) in
/-- **The platform's pending interrupt is the spec's** [P] (M4; module
docstring). -/
structure IrqPlat (AR : A → Fl4Spec.Cr3 → Prop) : Prop where
  take : ∀ (a : A) (σ : Fl4Spec.State Unit), arI.take_pending_irq a ⦃ r => ∃ irq ms,
    Fl4Spec.doMachineOp (Z := Unit) (Fl4Spec.getActiveIRQ true) σ = ({(irq, { σ with machineState := ms })}, False) ∧
    (r.1 = syscall.NO_IRQ ↔ irq = none) ∧
    (∀ i, irq = some i → r.1.val = i.toNat ∧ ms.irqMasks i = false) ∧
    ms.underlyingMemory = σ.machineState.underlyingMemory ⦄
  takeAR : ∀ a c, AR a c → arI.take_pending_irq a ⦃ r => AR r.2 c ⦄
  /-- One core (l4v's model is uniprocessor; seL4 C raises IPIs only under
  `ENABLE_SMP_SUPPORT`): no IPI line (`REMOTE_CALL_IPI` = 126,
  `RESCHEDULE_IPI` = 127 on x86_64) is ever pending. -/
  noIpi : ∀ a : A, arI.take_pending_irq a ⦃ r => r.1.val ≠ 126 ∧ r.1.val ≠ 127 ⦄
  /-- Acknowledging an interrupt keeps `AR` (the CR3 is not touched). -/
  ackAR : ∀ a i c, AR a c → arI.ack_irq a i ⦃ a' => AR a' c ⦄

variable (arI) in
/-- What the preemption path ends in: some outcome of the spec's
`preemption_path` from `σ1`, a `JHoleAt` state. -/
def PPQ (AR : A → Fl4Spec.Cr3 → Prop) (σ1 : Fl4Spec.State Unit) (r : S × A) : Prop :=
  (Fl4Spec.preemptionPath (Z := Unit) σ1).2 ∨ ∃ z ∈ (Fl4Spec.preemptionPath (Z := Unit) σ1).1,
    JHoleAtV (L := L) arI AR r.1 r.2 z.2 ∨ ∃ Z', XTopAt (L := L) AR Z' r.1 r.2 z.2

end

end

end Fl4Proofs.P3
