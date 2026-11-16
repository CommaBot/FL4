/-
P3 (DESIGN.md §9), IPC: **the notification proofs on the merged relation**,
the base: the narrowed hypotheses `IpcSchedHyps` and the TCB-word updates.

`IpcSchedHyps` is `SchedHyps` (NtfnSched.lean) with `IpcRel` (IpcRel.lean) in
place of `NtfnStateRel`: `SR` now stands for the subsystems that read no TCB
IPC field (scheduler queues and action, SCs, CSpace), so its `stable` fields
are sound for both the notification writes (`NWrite`, `NtfnStep`) and the
endpoint writes (`EWrite`, `EpStep`); `scheduleTcb` and `wakeTail` keep the
merged footprint `IFoot` and view `IKView`, `cancelIpc` the merged relation.

`scheduleTcb` assumes only the endpoint relation and the TCBs' SC words
(`ScRelM`), not all of `IpcRel`, so that it also serves the endpoint proofs'
`EpHyps` (IpcEpBase.lean). The Sc agent's `schedule_tcb_refines` is expected
to discharge it: it reads only the TCB's state code and its SC pointer.

`TcbRel.of_words`: the TCB relation after writes to its state, block-object
and register words (`Volatile`), from the spec TCB's new fields.
-/
import Fl4Proofs.P3.IpcRel
import Fl4Proofs.P3.NtfnSched
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp

noncomputable section

/-! ## The narrowed hypotheses -/

/-- The SC words of the TCBs: the part of `IpcRel` outside both subsystems'
relations. -/
def ScRelM {Z : Type} (T : Set U64) (m : U64 → U64) (σ : Fl4Spec.State Z) : Prop :=
  ∀ t ∈ T, ∃ x, σ.kheap t.bv = some (.tcb x) ∧ x.tcbSchedContext = optRef (m (scA t))

theorem ScRelM.of {Z : Type} {N T E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {m : U64 → U64}
    {σ : Fl4Spec.State Z} (h : IpcRel N T E R B m σ) : ScRelM T m σ :=
  fun t ht => let ⟨x, hk, hx⟩ := h.tcb t ht; ⟨x, hk, hx.sc⟩

theorem ScRelM.all {Z : Type} {T : Set U64} {m : U64 → U64} {σ : Fl4Spec.State Z} (h : ScRelM T m σ) :
    ∀ t ∈ T, ∀ x, σ.kheap t.bv = some (.tcb x) → x.tcbSchedContext = optRef (m (scA t)) := by
  intro t ht x hk
  obtain ⟨y, hy, e⟩ := h t ht
  rw [hk] at hy; injection hy with hy; injection hy with hy; subst hy; exact e

section Hyps
variable {S A : Type} (st : machine.Store S) (ar : machine.Arch A) [L : LawfulStore st]

/-- **What the IPC proofs assume of the other subsystems' relation `SR`**
(`SchedHyps` on the merged relation; see the module docstring). -/
structure IpcSchedHyps (N T E R : Set U64) (B : Set (U64 × Fl4Spec.Word)) (SR : S → Fl4Spec.State Unit → Prop) :
    Prop where
  stableN : ∀ s s' σ σ', SR s σ → WritesIn st s s' (NWrite N T) → NtfnStep σ σ' → NoBlock σ σ' → SR s' σ'
  stableE : ∀ s s' σ σ', SR s σ → WritesIn st s s' (EWrite T E R B) → EpStep σ σ' → SR s' σ'
  notQueued : ∀ s σ (t : U64) (x : Fl4Spec.Tcb), IpcRel N T E R B (L.mem s) σ → SR s σ →
    σ.kheap t.bv = some (.tcb x) →
    Fl4Spec.runnable x.tcbState = false → NotQueued σ t.bv
  block : ∀ s s' σ σ' (t : U64), SR s σ → NotQueued σ t.bv → RelIfBound σ t.bv →
    (∀ u, σ.schedulerAction = .switchThread u → u ≠ t.bv) → t.bv ≠ σ.idleThread →
    WritesIn st s s' (NWrite N T) → NtfnStep σ σ' →
    (∀ p x y, σ.kheap p = some (.tcb x) → σ'.kheap p = some (.tcb y) → p ≠ t.bv → y.tcbState = x.tcbState) →
    SR s' σ'
  scheduleTcb : ∀ s σ (t : U64), EpStateRel T E R B (L.mem s) σ → ScRelM T (L.mem s) σ → SR s σ → t ∈ T →
    sched.schedule_tcb st s t ⦃ s' => Agree (L.mem s) (L.mem s') (IFoot N T E R B) ∧ SR s' (stsAct σ t.bv) ⦄
  wakeTail : ∀ s (a : A) σ (t n : U64) (x : Fl4Spec.Tcb), IpcRel N T E R B (L.mem s) σ → SR s σ → t ∈ T →
    n ∈ N → σ.kheap t.bv = some (.tcb x) → x.tcbState = .running → NotQueued σ t.bv →
    rustWakeTail st ar s a t n ⦃ r => ¬ (specWakeTail t.bv n.bv σ).2 ∧ ∃ σ', ((), σ') ∈ (specWakeTail t.bv n.bv σ).1 ∧
      Agree (L.mem s) (L.mem r.1) (IFoot N T E R B) ∧ IKView σ σ' ∧ SR r.1 σ' ⦄
  cancelIpc : ∀ s (a : A) σ (t : U64) (x : Fl4Spec.Tcb), IpcRel N T E R B (L.mem s) σ → SR s σ → t ∈ T →
    σ.kheap t.bv = some (.tcb x) → Fl4Spec.receiveBlocked x.tcbState = true →
    ipc.cancel_ipc st ar s a t ⦃ r => ∃ σ' x', Fl4Spec.cancelIpc (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
      IpcRel N T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ∧ σ'.kheap t.bv = some (.tcb x') ∧ x'.tcbState = .inactive ∧
      RelIfBound σ' t.bv ⦄

end Hyps

/-! ## The TCB words the IPC code writes -/

section Words
open Fl4Spec

/-- The state, block-object and register words of the TCB at `t`. -/
def Volatile (t b : U64) : Prop :=
  b.val = t.val + 3328 ∨ b.val = t.val + 3336 ∨ (t.val + 256 ≤ b.val ∧ b.val < t.val + 448)

/-- The thread states without an endpoint payload (`BlockedOnSend`,
`BlockedOnReceive`, `BlockedOnReply`). -/
def NoEpPayload (ts : ThreadState) : Prop :=
  (∀ e d, ts ≠ .blockedOnSend e d) ∧ (∀ e r d, ts ≠ .blockedOnReceive e r d) ∧ (∀ r, ts ≠ .blockedOnReply r)

variable {R : Set U64} {m m' : U64 → U64} {t : U64}

/-- **The TCB relation after writes to `t`'s volatile words**: memory agrees
on `t`'s other words; the new state is coded, its block object stored, its
payload kept or absent, the registers stored; the other fields unchanged. -/
theorem TcbRel.of_words (ht : TcbAddr t) {x : Tcb} (h : TcbRel R m t x) (y : Tcb)
    (hA : ∀ b, Aligned b → TFI t b → ¬ Volatile t b → m' b = m b)
    (hst : (m' (tStA t)).val = tsCode y.tcbState)
    (hblkE : ∀ e, epBlocked y.tcbState = some e → (m' (tBlockA t)).bv = e)
    (hblkN : ∀ n, y.tcbState = .blockedOnNotification n → (m' (tBlockA t)).bv = n)
    (hpay : y.tcbState = x.tcbState ∨ NoEpPayload y.tcbState)
    (hregs : ∀ r, (m' (regA t (regIdx r))).bv = y.tcbArch.tcbContext.userRegs r)
    (hprio : y.tcbPriority = x.tcbPriority) (hfault : y.tcbFault = x.tcbFault)
    (hbound : y.tcbBoundNotification = x.tcbBoundNotification) (hsc : y.tcbSchedContext = x.tcbSchedContext) :
    TcbRel R m' t y := by
  have w : ∀ a, (Aligned a ∧ TF t a) → a.val - t.val ≥ 3344 → a.val ≤ t.val + 3448 → m' a = m a := by
    rintro a ⟨ha, hf⟩ h1 h2
    refine hA a ha (Or.inl hf) ?_
    unfold Volatile; have := hf.1; omega
  have e_badge := w _ (a_badge ht) (by rw [val_badge ht]; omega) (by rw [val_badge ht]; omega)
  have e_flags := w _ (a_flags ht) (by rw [val_flags ht]; omega) (by rw [val_flags ht]; omega)
  have e_reply := w _ (a_reply ht) (by rw [val_reply ht]; omega) (by rw [val_reply ht]; omega)
  have e_bound := w _ (a_bound ht) (by rw [val_bound ht]; omega) (by rw [val_bound ht]; omega)
  have e_fault := w _ (a_fault ht) (by rw [val_fault ht]; omega) (by rw [val_fault ht]; omega)
  have e_prio := w _ (a_prio ht) (by rw [val_prio ht]; omega) (le_of_eq (val_prio ht))
  have e_sc : m' (scA t) = m (scA t) := hA _ (scA_aligned ht) (Or.inr rfl) (by unfold Volatile; rw [scA_val ht]; omega)
  refine ⟨hst, hblkE, hblkN, ?_, ?_, ?_, hregs, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e d hs
    rcases hpay with e' | e'
    · rw [e'] at hs; rw [e_badge, e_flags]; exact h.send e d hs
    · exact absurd hs (e'.1 e d)
  · intro e r d hs
    rcases hpay with e' | e'
    · rw [e'] at hs; rw [e_reply]; exact h.recv e r d hs
    · exact absurd hs (e'.2.1 e r d)
  · intro r hs
    rcases hpay with e' | e'
    · rw [e'] at hs; rw [e_reply]; exact h.reply r hs
    · exact absurd hs (e'.2.2 r)
  · rw [e_prio, hprio]; exact h.prio
  · rw [e_fault, hfault]; exact h.fault0
  · rw [e_fault, hfault]; exact h.faultT
  · rw [e_bound, hbound]; exact h.bound
  · rw [hfault]
    exact h.faultR.congr e_fault
      (w _ (a_fw0 ht) (by rw [val_fw0 ht]; omega) (by rw [val_fw0 ht]; omega))
      (w _ (a_fw1 ht) (by rw [val_fw1 ht]; omega) (by rw [val_fw1 ht]; omega))
      (w _ (a_lf ht) (by rw [val_lf ht]; omega) (by rw [val_lf ht]; omega))
      (w _ (a_lf0 ht) (by rw [val_lf0 ht]; omega) (by rw [val_lf0 ht]; omega))
      (w _ (a_lf1 ht) (by rw [val_lf1 ht]; omega) (by rw [val_lf1 ht]; omega))
      (w _ (a_fw2 ht) (by rw [val_fw2 ht]; omega) (by rw [val_fw2 ht]; omega))
  · rw [e_sc, hsc]; exact h.sc

end Words

end

end Fl4Proofs.P3.Ipc
