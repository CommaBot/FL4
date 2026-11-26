/-
P3x for virtualization, spec side (line virt, gen 4; proofs/VIRT-PLAN.md §10 "Remaining (R7)" (a), (d)):
**without a `runningVM` thread every extended notification send is the ported one**, so the extended timer
step, interrupt handling, preemption path and kernel exit are the ported ones.

Spec: `Fl4Spec/Ext/VirtEntry` (`sendSignalV`, seL4 `sendSignal` with `CONFIG_VTX`; `fl4TimerSignalV` /
`fl4TimerFireV` / `fl4AwakenV`, `Ext/Timer`'s TCB timer step with `sendSignalV`; `handleInterruptV` /
`maybeHandleInterruptV`, l4v `Interrupt_A.handle_interrupt` / `maybe_handle_interrupt` with `sendSignalV`),
`Fl4Spec/Ext/VirtKernel` (`preemptionPathV`, l4v `Syscall_A.preemption_path`; `fl4KernelExitV`, FL4
`kernel/entry.rs` `exit`), against the ported `Ipc_A.send_signal` (`sendSignal`), `Ext/Timer`'s `fl4Awaken`,
`handleInterrupt`, `maybeHandleInterrupt`, `preemptionPath`. Nothing of the port changes.

* `sendSignalV_eq_nr`: on a `NoRunVM` state (VirtR7d) `sendSignalV = sendSignal` for every notification and
  badge, with no further condition: R7 (a)'s `sendSignalV_eq` where the notification exists and its bound
  thread is a TCB; otherwise both read the same missing object (no outcome of `get_notification` /
  `get_thread_state`).
* `timerFireV_iff`, `timerFiresV_iff`: the extended timer chain is the ported one from a `NoRunVM` state
  (induction over `ReflTransGen`, `NoRunVM` kept along the ported chain by invA's `ns_fl4Awaken`).
* **`fl4AwakenV_eq`**: `fl4AwakenV onCore σ = fl4Awaken σ` on `NoRunVM` — this discharges gen 3's `haw`.
* **`fl4KernelExitV_eq'`**: `fl4KernelExitV onCore` is the ported exit tail `fl4Awaken; schedule;
  activateThread` on every `NoRunVM` state (VirtR7d's `fl4KernelExitV_eq` without `haw`).
* `handleInterruptV_eq`, `maybeHandleInterruptV_eq`, `preemptionPathV_eq`: the interrupt paths, on `NoRunVM`.

Premises: only the state fact `hn : NoRunVM σ`. No [J]/[P]/[W]/[S]; no open spec equation. New file only.
-/
import Fl4Proofs.P3.VirtR7d
import Fl4Proofs.P3.SpecInvViA
open Classical

namespace Fl4Proofs.P3.VirtAwaken
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.VirtR7d

noncomputable section

/-! ## Binds over `NoRunVM`-keeping heads -/

/-- A bind whose head keeps `NoRunVM` and whose continuations agree on `NoRunVM` states. -/
theorem bind_nr {α β : Type} {m : NonDet (State Unit) α} (hm : IK NoRunVM m) {k1 k2 : α → NonDet (State Unit) β}
    {σ : State Unit} (hσ : NoRunVM σ) (h : ∀ a s, NoRunVM s → k1 a s = k2 a s) : (m >>= k1) σ = (m >>= k2) σ :=
  nd_bind_congr_on _ _ _ σ fun x hx => h x.1 x.2 (hm σ hσ x hx)

/-! ## R7 (a) without side conditions -/

/-- **`sendSignalV = sendSignal` on every `NoRunVM` state** (module docstring). -/
theorem sendSignalV_eq_nr (onCore : ObjRef → Bool) {σ : State Unit} (hn : NoRunVM σ) (n : ObjRef) (b : Badge) :
    sendSignalV (Z := Unit) onCore n b σ = sendSignal n b σ := by
  by_cases hk : ∃ x, σ.kheap n = some (.notification x)
  · obtain ⟨x, hk⟩ := hk
    by_cases hb : ∀ t, x.ntfnBoundTcb = some t → ∃ tcb, σ.kheap t = some (.tcb tcb) ∧ tcb.tcbState ≠ .runningVM
    · exact VirtR7.sendSignalV_eq onCore b hk hb
    · push_neg at hb
      obtain ⟨t, hbt, hnt⟩ := hb
      have hg : ∀ y ∈ (getThreadState (Z := Unit) t σ).1, False := fun y hy => by
        unfold getThreadState at hy
        obtain ⟨x0, hk0, -⟩ := SInvQ.q1_mem_threadGet hy
        exact hn t x0 hk0 (hnt x0 hk0)
      unfold sendSignalV
      conv_rhs => unfold sendSignal
      rw [Notif.nd_bind_one (Notif.getNotification_eq hk), Notif.nd_bind_one (Notif.getNotification_eq hk)]
      rw [hbt]
      rcases ho : x.ntfnObj with _ | q | bd
      · exact nd_bind_congr_on _ _ _ σ fun y hy => (hg y hy).elim
      all_goals
        dsimp only
        unfold sendSignal
        rw [Notif.nd_bind_one (Notif.getNotification_eq hk)]
        rw [ho, hbt]
  · have hg : ∀ y ∈ (getNotification (Z := Unit) n σ).1, False := fun y hy =>
      hk ⟨y.1, (SInvI.mem_getSimpleKo hy).1⟩
    unfold sendSignalV
    conv_rhs => unfold sendSignal
    exact nd_bind_congr_on _ _ _ σ fun y hy => (hg y hy).elim

/-! ## The timer step -/

theorem timerSignalV_iff (onCore : ObjRef → Bool) {σ σ' : State Unit} (hn : NoRunVM σ) :
    fl4TimerSignalV (Z := Unit) onCore σ σ' ↔ fl4TimerSignal σ σ' := by
  unfold fl4TimerSignalV fl4TimerSignal
  simp only [sendSignalV_eq_nr onCore hn]

theorem timerFireV_iff (onCore : ObjRef → Bool) {σ σ' : State Unit} (hn : NoRunVM σ) :
    fl4TimerFireV (Z := Unit) onCore σ σ' ↔ fl4TimerFire σ σ' := by
  unfold fl4TimerFireV fl4TimerFire
  simp only [timerSignalV_iff onCore hn]

/-- The extended timer chain is the ported one from a `NoRunVM` state. -/
theorem timerFiresV_iff (onCore : ObjRef → Bool) {σ σ' : State Unit} (hn : NoRunVM σ) :
    Relation.ReflTransGen (fl4TimerFireV (Z := Unit) onCore) σ σ' ↔ fl4TimerFires σ σ' := by
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hst ih =>
      have hb := noRunVM_fl4Awaken σ hn ((), _) (mem_fl4Awaken.2 ih)
      exact ih.tail ((timerFireV_iff onCore hb).1 hst)
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail hab hst ih =>
      have hb := noRunVM_fl4Awaken σ hn ((), _) (mem_fl4Awaken.2 hab)
      exact ih.tail ((timerFireV_iff onCore hb).2 hst)

/-- **The extended timer step is the ported one** on a `NoRunVM` state (gen 3's `haw`). -/
theorem fl4AwakenV_eq (onCore : ObjRef → Bool) {σ : State Unit} (hn : NoRunVM σ) :
    fl4AwakenV (Z := Unit) onCore σ = fl4Awaken σ :=
  Prod.ext (Set.ext fun _ => timerFiresV_iff onCore hn) rfl

/-- **The extended exit is the ported exit tail** on every `NoRunVM` state (no `haw`). -/
theorem fl4KernelExitV_eq' (onCore : ObjRef → Bool) {σ : State Unit} (hn : NoRunVM σ) :
    fl4KernelExitV (Z := Unit) onCore σ =
      (fl4Awaken (Z := Unit) >>= fun _ => schedule (Z := Unit) >>= fun _ => activateThread (Z := Unit)) σ :=
  fl4KernelExitV_eq onCore hn (fl4AwakenV_eq onCore hn)

/-! ## Interrupts and the preemption path -/

theorem when_sendSignalV_eq (onCore : ObjRef → Bool) (c : Prop) [Decidable c] (n : ObjRef) (b : Badge)
    {σ : State Unit} (hn : NoRunVM σ) :
    NonDet.when c (sendSignalV (Z := Unit) onCore n b) σ = NonDet.when c (sendSignal n b) σ := by
  unfold NonDet.when
  by_cases h : c
  · rw [if_pos h, if_pos h]; exact sendSignalV_eq_nr onCore hn n b
  · rw [if_neg h, if_neg h]

theorem handleInterruptV_eq (onCore : ObjRef → Bool) {σ : State Unit} (hn : NoRunVM σ) (irq : Irq) :
    handleInterruptV (Z := Unit) onCore irq σ = handleInterrupt irq σ := by
  unfold handleInterruptV handleInterrupt
  by_cases hi : irq > maxIRQ
  · rw [if_pos hi, if_pos hi]
  · rw [if_neg hi, if_neg hi]
    refine bind_nr (ns_getIrqState irq) hn fun st s1 h1 => ?_
    cases st
    all_goals try rfl
    refine bind_nr (ns_getIrqSlot irq) h1 fun slot s2 h2 => ?_
    refine bind_nr (ns_getCap slot) h2 fun cap s3 h3 => ?_
    exact nd_bind_eq_of (when_sendSignalV_eq onCore _ _ _ h3) _

theorem maybeHandleInterruptV_eq (onCore : ObjRef → Bool) {σ : State Unit} (hn : NoRunVM σ) (ik : Bool) :
    maybeHandleInterruptV (Z := Unit) onCore ik σ = maybeHandleInterrupt ik σ := by
  unfold maybeHandleInterruptV maybeHandleInterrupt
  refine bind_nr (ik_doMachineOp (fun _ _ h => h) _) hn fun io s1 h1 => ?_
  cases io with
  | none => rfl
  | some irq => exact handleInterruptV_eq onCore h1 irq

theorem preemptionPathV_eq (onCore : ObjRef → Bool) {σ : State Unit} (hn : NoRunVM σ) :
    preemptionPathV (Z := Unit) onCore σ = preemptionPath σ := by
  unfold preemptionPathV preemptionPath
  refine bind_nr (ik_gets _) hn fun ct s1 h1 => ?_
  refine bind_nr (ik_gets _) h1 fun sch s2 h2 => ?_
  by_cases hs : sch = true
  · rw [if_pos hs, if_pos hs]
    exact bind_nr ns_checkBudget h2 fun _ s3 h3 => maybeHandleInterruptV_eq onCore h3 true
  · rw [if_neg hs, if_neg hs]
    refine bind_nr (ik_gets _) h2 fun csc s3 h3 => bind_nr (ns_getScActive _) h3 fun a s4 h4 => ?_
    by_cases ha : a = true
    · rw [if_pos ha, if_pos ha]
      exact bind_nr (ik_gets _) h4 fun _ s5 h5 =>
        bind_nr (ns_chargeBudget _ _) h5 fun _ s6 h6 => maybeHandleInterruptV_eq onCore h6 true
    · rw [if_neg ha, if_neg ha]
      exact bind_nr (ik_modify (g := fun s : State Unit => { s with consumedTime := 0 }) fun _ h => h) h4
        fun _ s5 h5 => maybeHandleInterruptV_eq onCore h5 true

end

end Fl4Proofs.P3.VirtAwaken
