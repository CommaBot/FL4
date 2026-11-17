/-
P3 (DESIGN.md §9), TCB invocations: **Resume on `IRel`** (`sched::restart`
against l4v `restart`): the steps; the leaf from `JAtZ` is IpcResumeJ's
`restart_tcb_irelS`/`resumeXLeafJD` (the former `restart_tcb_irel` and
`resumeXLeaf_of` are retired).

A stopped thread (`is_stopped_eq`: inactive or blocked, l4v's
`¬ runnable ∧ ¬ idle`): `cancel_ipc` (`cancel_ipc_irel`), `Restart`
(`set_thread_state_c`), the sporadic unblock check (`unblock_irel`), the
SC's resume (`resume_refines`, lifted by `tk_liftCW`), and the switch to it
if schedulable (`switch_top`). The spec reads the thread's SC before
`cancel_ipc`, FL4 after: IpcTscK's `TSK` (`cancel_ipc` and
`set_thread_state` keep it, and the ready queues, so the thread, not
runnable at the start, is in none, `Inv.rq`).
-/
import Fl4Proofs.P3.IpcSuspend
import Fl4Proofs.P3.IpcTscK
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- `is_stopped`: inactive or blocked (l4v `¬ runnable ∧ ¬ idle`). -/
theorem is_stopped_eq {s : S} {t : U64} {ts : Fl4Spec.ThreadState}
    (h : (L.mem s (P1.stA t)).val = tsCode ts) :
    sched.is_stopped st s t = ok (decide (¬ Fl4Spec.runnable ts = true ∧ ¬ Fl4Spec.idle ts)) := by
  have e : obj.Tcb.state st t s = ok (L.mem s (P1.stA t)) := by
    obtain ⟨v, hv, hv'⟩ := Sched.rrt_exists (P1.obj.Tcb.state.spec (st := st) s t); rw [hv, hv']
  unfold sched.is_stopped sched.is_blocked
  simp only [e, bind_ok]
  generalize L.mem s (P1.stA t) = w at h ⊢
  have ev : ∀ k : U64, (w = k ↔ w.val = k.val) := fun k => ⟨fun h => h ▸ rfl, fun h => UScalar.eq_of_val_eq h⟩
  unfold sched.TS_INACTIVE sched.TS_BLOCKED_ON_RECV sched.TS_BLOCKED_ON_SEND sched.TS_BLOCKED_ON_NTFN
    sched.TS_BLOCKED_ON_REPLY
  simp only [ev, h]
  cases ts <;> simp [tsCode, Fl4Spec.runnable, Fl4Spec.idle]

/-- The FL4 sporadic unblock of `restart`, as `unblock_sporadic`. -/
theorem restart_unblock_spec {s : S} {t : U64} {X : Type} {k : U64 → S → Result X} {P : S → Prop}
    {Q : X → Prop} (h : notification.unblock_sporadic st s t ⦃ P ⦄)
    (hk : ∀ s3, P s3 → k (L.mem s (scA t)) s3 ⦃ Q ⦄) :
    (do
      let i ← obj.Tcb.sc st t s
      let b1 ← sporadic.sc_sporadic st s i
      let s3 ← (if b1 then (do
          let s4 ← sched.cur_sc st s
          let b2 ← core.cmp.PartialEq.ne.trait_default obj.Sc.Insts.CoreCmpPartialEqSc i s4
          (if b2 then sporadic.unblock_check st s i else ok s))
        else ok s)
      k i s3) ⦃ Q ⦄ := by
  have e : obj.Tcb.sc st t s = ok (L.mem s (scA t)) := by
    obtain ⟨v, hv, hv'⟩ := Sched.rrt_exists (P1.obj.Tcb.sc.spec (st := st) s t); rw [hv, hv']
  unfold notification.unblock_sporadic at h
  rw [e] at h ⊢
  simp only [Std.bind_tc_ok, bind_ok] at h ⊢
  have := WP.spec_bind h hk
  simpa only [Std.bind_assoc_eq, Std.bind_assoc] using this

end

end

end Fl4Proofs.P3.Ipc

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

end

end

end Fl4Proofs.P3
