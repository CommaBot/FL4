/-
P3 (DESIGN.md §9), endpoints: the interface to the other subsystems, and
setting a thread state.

As for notifications (NtfnSched.lean), the relation of the other subsystems
(scheduler state, scheduling contexts, notifications, CSpace, ...) is a
parameter `SR`, with explicit hypotheses `EpHyps`:

* `stable`: `SR` ignores what the endpoint code itself changes: FL4 words in
  `EWrite` and, in the spec, endpoints, the TCB of replies, the state and
  user context of TCBs and user memory (`EpStep`);
* `scheduleTcb`: `schedule_tcb t` refines `set_thread_state_act t` (whose
  single outcome is `stsAct`), keeping the footprint.

The scheduler tails of the transfers have their own hypotheses (`EpTailHyps`,
EpTail.lean), as does the IPC-buffer lookup (`EpBufHyps`, EpXfer.lean).

`set_thread_state_rel`: `set_thread_state t` (the state word, then
`schedule_tcb`) refines `set_thread_state t ts` for a thread in no endpoint
queue and a state `ts` that is `Inactive`, `Running` or `Restart`.
-/
import Fl4Proofs.P3.EpQueue
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Hyps
variable {S A : Type} (st : machine.Store S) (ar : machine.Arch A) [L : LawfulStore st]

/-- What the endpoint proofs assume of the other subsystems' relation `SR`. -/
structure EpHyps (T E R : Set U64) (B : Set (U64 × Fl4Spec.Word)) (SR : S → Fl4Spec.State Unit → Prop) : Prop where
  stable : ∀ s s' σ σ', SR s σ → WritesIn st s s' (EWrite T E R B) → EpStep σ σ' → SR s' σ'
  scheduleTcb : ∀ s σ (t : U64), EpStateRel T E R B (L.mem s) σ → SR s σ → t ∈ T →
    sched.schedule_tcb st s t ⦃ s' => FootEq T E R B (L.mem s) (L.mem s') ∧ SR s' (stsAct σ t.bv) ⦄

end Hyps

section
open Fl4Spec
variable {Z : Type}

theorem stsAct_ms (σ : State Z) (t : ObjRef) : (stsAct σ t).machineState = σ.machineState := by
  unfold stsAct; split_ifs <;> rfl

theorem KView.stsAct' (σ : State Z) (t : ObjRef) : KView σ (stsAct σ t) := by
  refine ⟨fun p x h => ?_, fun p x h => ⟨x, ?_, rfl⟩, fun p x h => ⟨x, ?_, rfl, rfl, rfl, rfl, rfl⟩, by rw [stsAct_ms]⟩ <;>
    rw [stsAct_kheap] <;> exact h

theorem tsCode_three {ts : ThreadState} (h : tsCode ts = 3) : ∃ e r d, ts = .blockedOnReceive e r d := by
  cases ts <;> simp [tsCode] at h ⊢
theorem tsCode_four {ts : ThreadState} (h : tsCode ts = 4) : ∃ e d, ts = .blockedOnSend e d := by
  cases ts <;> simp [tsCode] at h ⊢

end

section
variable {T E R : Set U64} {B : Set (U64 × Fl4Spec.Word)}

/-- A TCB whose state is not blocked on an endpoint is in no endpoint
queue. -/
theorem not_queued {m : U64 → U64} {σ : Fl4Spec.State Unit} (hR : EpStateRel T E R B m σ) {t : U64} (ht : t ∈ T)
    {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt)) (hc : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) :
    ∀ e ∈ E, ∀ z, σ.kheap e.bv = some (.endpoint z) → t.bv ∉ z.epQueue := by
  intro e he z hz hm
  obtain ⟨xs, -, hxs, hB⟩ := (show EpObjRel m T e z from by
    obtain ⟨z', hz', h'⟩ := hR.ep e he; rw [hz] at hz'; cases hz'; exact h').queue
  rw [hxs, List.mem_map] at hm
  obtain ⟨y, hy, ey⟩ := hm
  have : y = t := eq_of_bv ey
  subst this
  obtain ⟨x', hx', hrel⟩ := hR.tcb y ht
  rw [hkt] at hx'; cases hx'
  have := hrel.st
  rcases (hB y hy).2 with h | h <;> rw [h] at this
  · exact hc.1 this.symm
  · exact hc.2 this.symm

theorem EpStateRel.at_ep {m : U64 → U64} {σ : Fl4Spec.State Unit} (hR : EpStateRel T E R B m σ) {e : U64}
    (he : e ∈ E) {x : Fl4Spec.Endpoint} (hk : σ.kheap e.bv = some (.endpoint x)) : EpObjRel m T e x := by
  obtain ⟨y, hky, hy⟩ := hR.ep e he
  rw [hk] at hky; cases hky; exact hy

theorem EpStateRel.at_tcb {m : U64 → U64} {σ : Fl4Spec.State Unit} (hR : EpStateRel T E R B m σ) {t : U64}
    (ht : t ∈ T) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) : TcbRelE R m t x := by
  obtain ⟨y, hky, hy⟩ := hR.tcb t ht
  rw [hk] at hky; cases hky; exact hy

theorem EpStateRel.at_reply {m : U64 → U64} {σ : Fl4Spec.State Unit} (hR : EpStateRel T E R B m σ) {r : U64}
    (hr : r ∈ R) {x : Fl4Spec.Reply} (hk : σ.kheap r.bv = some (.reply x)) : x.replyTcb = optRef (m (rTcbA r)) := by
  obtain ⟨y, hky, hy⟩ := hR.reply r hr
  rw [hk] at hky; cases hky; exact hy

/-- A related TCB with a new state whose payload the relation ignores, from
memory that agrees on all of its fields but the state word. -/
theorem TcbRelE.with_state {m m' : U64 → U64} {t : U64} {x : Fl4Spec.Tcb} (ht : TcbAddr t)
    (h : TcbRelE R m t x) (ts : Fl4Spec.ThreadState) (hts : tsCode ts < 3)
    (hst : (m' (tStA t)).val = tsCode ts) (hA : Agree m m' (fun b => TF t b ∧ b.val ≠ (tStA t).val)) :
    TcbRelE R m' t { x with tcbState := ts } := by
  have g : ∀ {b}, Aligned b ∧ TF t b → b.val ≠ (tStA t).val → m' b = m b := fun hb hne => hA _ hb.1 ⟨hb.2, hne⟩
  have v := val_st ht
  refine ⟨hst, fun e he => ?_, fun e d he => ?_, fun e r d he => ?_, fun r he => ?_, fun r => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases ts <;> simp [tsCode, Fl4Spec.epBlocked] at hts he
  · subst he; simp [tsCode] at hts
  · subst he; simp [tsCode] at hts
  · subst he; simp [tsCode] at hts
  · rw [g (a_reg ht r) (by rw [regA_val ht (regIdx_lt r), v]; have := regIdx_lt r; omega)]; exact h.regs r
  · rw [g (a_prio ht) (by rw [val_prio ht, v]; omega)]; exact h.prio
  · rw [g (a_fault ht) (by rw [val_fault ht, v]; omega)]; exact h.fault0
  · rw [g (a_fault ht) (by rw [val_fault ht, v]; omega)]; exact h.faultT
  · rw [g (a_bound ht) (by rw [val_bound ht, v]; omega)]; exact h.bound
  · exact h.faultR.congr (g (a_fault ht) (by rw [val_fault ht, v]; omega)) (g (a_fw0 ht) (by rw [val_fw0 ht, v]; omega)) (g (a_fw1 ht) (by rw [val_fw1 ht, v]; omega)) (g (a_lf ht) (by rw [val_lf ht, v]; omega)) (g (a_lf0 ht) (by rw [val_lf0 ht, v]; omega)) (g (a_lf1 ht) (by rw [val_lf1 ht, v]; omega)) (g (a_fw2 ht) (by rw [val_fw2 ht, v]; omega))

theorem tf_ne_of {t a b : U64} (hb : ¬ TF t b) (ha : TF t a) : b.val ≠ a.val := fun e => hb (ha.of_val e)

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
  {SR : S → Fl4Spec.State Unit → Prop}

/-- Writing the state word of a TCB in no endpoint queue: related to the spec's
TCB with the new (unblocked) state. -/
theorem write_state_rel (hP : EPlaced T E R B) (s : S) (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ)
    {t : U64} (ht : t ∈ T) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x))
    (hq : ∀ e ∈ E, ∀ z, σ.kheap e.bv = some (.endpoint z) → t.bv ∉ z.epQueue)
    (ts : Fl4Spec.ThreadState) (hts : tsCode ts < 3) (code : U64) (hcode : code.val = tsCode ts) :
    EpStateRel T E R B (L.mem (L.wr s (tStA t) code)) (updK σ t.bv (.tcb { x with tcbState := ts })) ∧
      WritesIn st s (L.wr s (tStA t) code) (EWrite T E R B) ∧
      EpStep σ (updK σ t.bv (.tcb { x with tcbState := ts })) := by
  have hta := hP.tcb t ht
  have hx := hR.at_tcb ht hk
  have ha := a_st hta
  have hag := agree_wr (L := L) (s := s) (v := code) ha.1
  refine ⟨hR.upd_tcb hP ht _ (hag.mono fun b hb => tf_ne_of hb.2 ha.2) (Or.inl hq)
    (hx.with_state hta ts hts (by rw [rd_wr_eq ha.1]; exact hcode) (hag.mono fun b hb => hb.2)), ?_,
    EpStep.tcb hk ts x.tcbArch⟩
  refine (writesIn_wr ha.1).mono fun b hb => ?_
  subst hb
  refine Or.inr (Or.inr (Or.inl ⟨t, ht, Or.inl ⟨ha.2.1, ?_⟩⟩))
  rw [val_st hta]; unfold TWOffN; omega

/-- **`set_thread_state t ts`** for a thread in no endpoint queue and a state
that is `Inactive`, `Running` or `Restart`. -/
theorem set_thread_state_rel (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B) (s : S)
    (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ) {t : U64} (ht : t ∈ T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x))
    (hq : ∀ e ∈ E, ∀ z, σ.kheap e.bv = some (.endpoint z) → t.bv ∉ z.epQueue)
    (ts : Fl4Spec.ThreadState) (hts : tsCode ts < 3) (code : U64) (hcode : code.val = tsCode ts) :
    sched.set_thread_state st s t code ⦃ s' =>
      EpStateRel T E R B (L.mem s') (stsAct (updK σ t.bv (.tcb { x with tcbState := ts })) t.bv) ∧
      SR s' (stsAct (updK σ t.bv (.tcb { x with tcbState := ts })) t.bv) ⦄ := by
  unfold sched.set_thread_state
  step
  subst s1_post
  obtain ⟨hR1, hW1, hS1⟩ := write_state_rel hP s σ hR ht hk hq ts hts code hcode
  refine WP.spec_mono (hH.scheduleTcb _ _ t hR1 (hH.stable _ _ _ _ hSR hW1 hS1) ht) ?_
  rintro s2 ⟨hf, hS⟩
  exact ⟨hR1.frame hP hf (KView.stsAct' _ _), hS⟩

end

end

end

end Fl4Proofs.P3.Endp
