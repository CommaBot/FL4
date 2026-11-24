/-
P3 (int6, FL4 #80 / #85): **`send_signal` completes no VMEnter** at the
signals P3's wake proofs follow (`P1.NoVmSig`, under which
`send_signal.tinvF`'s footprint is the old `KW` / debug one): a notification
that is not idle, or one whose bound thread is blocked receiving.
-/
import Fl4Proofs.P3.IpcSignalBound
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- A notification that is not idle: no VMEnter completion. -/
theorem noVm_of_ntfn {s : S} {σ : Fl4Spec.State Unit} (hX : IRel st th cr N T C E R B c s σ) {n : U64}
    (hn : n ∈ N) {x : Fl4Spec.Notification} (hk : σ.kheap n.bv = some (.notification x))
    (ho : x.ntfnObj ≠ .idleNtfn) : P1.NoVmSig st n s := by
  have hx := hX.1.toN.at_ntfn hn hk
  refine Or.inl ?_
  rw [epState_eq]
  cases h : x.ntfnObj with
  | idleNtfn => exact absurd h ho
  | activeNtfn b => rw [stOf_active hx.obj h]; unfold obj.NTFN_ACTIVE obj.NTFN_IDLE; decide
  | waitingNtfn q => rw [stOf_waiting hx.obj h]; unfold obj.NTFN_WAITING obj.NTFN_IDLE; decide

/-- An idle notification whose bound thread is blocked receiving: no
VMEnter completion. -/
theorem noVm_of_recv {s : S} {σ : Fl4Spec.State Unit} (hX : IRel st th cr N T C E R B c s σ) {n : U64}
    (hn : n ∈ N) {x : Fl4Spec.Notification} (hk : σ.kheap n.bv = some (.notification x)) {t : U64}
    {tcb : Fl4Spec.Tcb} (hb : x.ntfnBoundTcb = some t.bv) (hkt : σ.kheap t.bv = some (.tcb tcb))
    (hrb : Fl4Spec.receiveBlocked tcb.tcbState = true) : P1.NoVmSig st n s := by
  have hR := hX.1
  have hx := hR.toN.at_ntfn hn hk
  obtain ⟨hb0, hbt⟩ := Notif.optRef_some (hx.bound ▸ hb)
  have hbt' : L.mem s (nBoundA n) = t := eq_of_bv hbt
  have hiT : t ∈ T := hbt' ▸ hx.bound_mem hb0
  have hy := hR.toN.at_tcb hiT hkt
  have hs3 : L.mem s (tStA t) = sched.TS_BLOCKED_ON_RECV := by
    have h3 := hy.st
    rw [tsVals.2.2.1]
    apply UScalar.eq_of_val_eq
    revert hrb h3
    cases tcb.tcbState <;> simp [tsCode, Fl4Spec.receiveBlocked]
  refine Or.inr ?_
  have e1 : P1.ntfnBtA n = nBoundA n := rfl
  have e2 : P1.stA t = tStA t := rfl
  rw [e1, hbt', e2, hs3]
  simp [sched.TS_BLOCKED_ON_RECV, sched.TS_RUNNING_VM]

end

end Fl4Proofs.P3.Ipc
