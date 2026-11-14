/-
P3 (DESIGN.md §9), endpoints: blocking on an endpoint, the queue part.

`ep_append_rel`: once a thread's state and block object say it is blocked on
the endpoint `e` (state word 4 for a send, 3 for a receive), FL4's
`ep_append` (`append_by_prio`) refines l4v `tcb_ep_append` (`tcb_append`,
equal on priority-sorted queues): the endpoint becomes `SendEP` /
`RecvEP` of the ordered insertion.

Extra hypotheses (as for notifications, NtfnBlock.lean): the queue is
sorted by priority (`PrioSorted`, a P1 invariant), and the thread was in no
queue.

`TcbRelE.restate`: a TCB's relation from its state part and memory that
agrees on the other fields.
-/
import Fl4Proofs.P3.EpSched
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {T E R : Set U64} {B : Set (U64 × Fl4Spec.Word)}

/-- The fields of a TCB the IPC state does not involve: registers, bound
notification, fault, priority. -/
def TStat (t b : U64) : Prop := TF t b ∧ (b.val < t.val + 3328 ∨ t.val + 3368 ≤ b.val)

/-- A TCB's relation, from its state part and memory that agrees on the
other fields. -/
theorem TcbRelE.restate {m m' : U64 → U64} {t : U64} {x x' : Fl4Spec.Tcb} (ht : TcbAddr t)
    (h : TcbRelE R m t x) (hA : Agree m m' (TStat t))
    (e1 : x'.tcbArch.tcbContext.userRegs = x.tcbArch.tcbContext.userRegs) (e2 : x'.tcbPriority = x.tcbPriority)
    (e3 : x'.tcbFault = x.tcbFault) (e4 : x'.tcbBoundNotification = x.tcbBoundNotification)
    (hst : (m' (tStA t)).val = tsCode x'.tcbState)
    (hblk : ∀ e, Fl4Spec.epBlocked x'.tcbState = some e → (m' (tBlockA t)).bv = e)
    (hsend : ∀ e d, x'.tcbState = .blockedOnSend e d → (m' (tBadgeA t)).bv = d.senderBadge ∧ m' (tFlagsA t) = flagsOf d)
    (hrecv : ∀ e r d, x'.tcbState = .blockedOnReceive e r d → optRef (m' (tReplyA t)) = r ∧
      (r ≠ none → m' (tReplyA t) ∈ R))
    (hrep : ∀ r, x'.tcbState = .blockedOnReply r → (m' (tReplyA t)).bv = r) :
    TcbRelE R m' t x' := by
  have g : ∀ {b}, Aligned b ∧ TF t b → (b.val < t.val + 3328 ∨ t.val + 3368 ≤ b.val) → m' b = m b :=
    fun hb hv => hA _ hb.1 ⟨hb.2, hv⟩
  refine ⟨hst, hblk, hsend, hrecv, hrep, fun r => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g (a_reg ht r) (by rw [regA_val ht (regIdx_lt r)]; have := regIdx_lt r; omega), e1]; exact h.regs r
  · rw [g (a_prio ht) (by rw [val_prio ht]; omega), e2]; exact h.prio
  · rw [g (a_fault ht) (by rw [val_fault ht]; omega), e3]; exact h.fault0
  · rw [g (a_fault ht) (by rw [val_fault ht]; omega), e3]; exact h.faultT
  · rw [g (a_bound ht) (by rw [val_bound ht]; omega), e4]; exact h.bound
  · rw [e3]; exact h.faultR.congr (g (a_fault ht) (by rw [val_fault ht]; omega)) (g (a_fw0 ht) (by rw [val_fw0 ht]; omega)) (g (a_fw1 ht) (by rw [val_fw1 ht]; omega)) (g (a_lf ht) (by rw [val_lf ht]; omega)) (g (a_lf0 ht) (by rw [val_lf0 ht]; omega)) (g (a_lf1 ht) (by rw [val_lf1 ht]; omega))

/-- The endpoints a thread can block on: idle, or already queued the same
way. -/
def CanBlock (isRecv : Bool) : Fl4Spec.Endpoint → Prop
  | .idleEP => True
  | .sendEP _ => isRecv = false
  | .recvEP _ => isRecv = true

theorem epIns_eq {x : Fl4Spec.Endpoint} {isRecv : Bool} (h : CanBlock isRecv x) (q : List Fl4Spec.ObjRef) :
    Fl4Spec.updateEpQueue x q isRecv = if isRecv then .recvEP q else .sendEP q := by
  cases x <;> cases isRecv <;> simp [CanBlock] at h <;> rfl

theorem stOf_canBlock {m : U64 → U64} {e : U64} {x : Fl4Spec.Endpoint} {isRecv : Bool} (h : EpObjRel m T e x)
    (hc : CanBlock isRecv x) : ∀ y ∈ x.epQueue, ∃ y', y = y'.bv ∧ QueuedOn m e (if isRecv then 3 else 4) y' := by
  intro y hy
  cases x with
  | idleEP => simp [Fl4Spec.Endpoint.epQueue] at hy
  | sendEP q =>
    simp only [CanBlock] at hc; subst hc
    obtain ⟨-, xs, -, rfl, -, h3⟩ := h
    simp only [Fl4Spec.Endpoint.epQueue, List.mem_map] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    exact ⟨y', rfl, h3 y' hy'⟩
  | recvEP q =>
    simp only [CanBlock] at hc; subst hc
    obtain ⟨-, xs, -, rfl, -, h3⟩ := h
    simp only [Fl4Spec.Endpoint.epQueue, List.mem_map] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    exact ⟨y', rfl, h3 y' hy'⟩

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
  {SR : S → Fl4Spec.State Unit → Prop}

theorem ep_state_vals : obj.EP_IDLE = 0#u64 ∧ obj.EP_SEND = 1#u64 ∧ obj.EP_RECV = 2#u64 := by
  unfold obj.EP_IDLE obj.EP_SEND obj.EP_RECV; exact ⟨rfl, rfl, rfl⟩

/-- **`ep_append`** of a thread blocked on `e` refines `tcb_ep_append`. -/
theorem ep_append_rel (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B) (s : S) (σ : Fl4Spec.State Unit)
    (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ) {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb}
    (hkt : σ.kheap t.bv = some (.tcb xt)) {e : U64} (he : e ∈ E) {x : Fl4Spec.Endpoint}
    (hk : σ.kheap e.bv = some (.endpoint x)) (isRecv : Bool) (hc : CanBlock isRecv x)
    (htq : t.bv ∉ x.epQueue)
    (htst : (L.mem s (tStA t)).val = if isRecv then 3 else 4) (htb : L.mem s (tBlockA t) = e)
    (hsort : ∀ xs, QueueRel (L.mem s) T .Ep (qOf (L.mem s) e) xs → PrioSorted (fun y => L.mem s (prioA y)) xs) :
    endpoint.ep_append st s e t (if isRecv then obj.EP_RECV else obj.EP_SEND) ⦃ s' =>
      ∃ σ', Fl4Spec.tcbEpAppend (Z := Unit) t.bv e.bv isRecv σ = ({((), σ')}, False) ∧
        EpStateRel T E R B (L.mem s') σ' ∧ SR s' σ' ⦄ := by
  have hx := hR.at_ep he hk
  have hxt := hR.at_tcb ht hkt
  obtain ⟨xs, hQ, hxs, hB⟩ := hx.queue
  have htxs : t ∉ xs := fun h => htq (by rw [hxs]; exact List.mem_map_of_mem h)
  have hsorted := hsort xs hQ
  refine WP.spec_mono (ep_append_full hP s he t _ xs hQ ht htxs) ?_
  rintro s' ⟨hA1, hA2, hA3, hA4⟩
  set ys := insPrio (fun y => L.mem s (prioA y)) (L.mem s (prioA t)) t xs
  -- the spec
  have hq : ∀ y ∈ x.epQueue, ∃ z, σ.kheap y = some (.tcb z) ∧ z.tcbPriority = prioOf σ y := by
    intro y hy
    rw [hxs] at hy
    obtain ⟨y', hy'x, rfl⟩ := List.mem_map.1 hy
    obtain ⟨z, hz, -⟩ := hR.tcb y' (hQ.mem y' hy'x)
    exact ⟨z, hz, by simp [prioOf, hz]⟩
  have hlist : specIns x.epQueue (prioOf σ) xt.tcbPriority t.bv = ys.map UScalar.bv := by
    rw [specIns, hxs, List.takeWhile_map, List.dropWhile_map]
    simp only [ys, insPrio_eq_sorted _ _ t xs hsorted, List.map_append, List.map_cons]
    have hc' : ∀ y ∈ xs, ((fun y => @decide (prioOf σ y ≥ xt.tcbPriority) (Classical.propDecidable _)) ∘
        UScalar.bv) y = (fun y => !decide (L.mem s (prioA t) > L.mem s (prioA y))) y := by
      intro y hy
      obtain ⟨z, hz, hzr⟩ := hR.tcb y (hQ.mem y hy)
      have hpz : prioOf σ y.bv = z.tcbPriority := by simp [prioOf, hz]
      simp only [Function.comp, hpz]
      convert (prio_ge_iff _ _ _ _ hxt.prio hzr.prio).symm using 2
    rw [takeWhile_congr' hc', dropWhile_congr' hc']
  refine ⟨_, by rw [tcbEpAppend_eq hk hkt (prioOf σ) hq, hlist], ?_, ?_⟩
  · -- the relation
    refine hR.upd_ep hP he _ (hA3.mono fun b ⟨h1, h2, h3⟩ => ⟨h2, fun ⟨w, hw, hl⟩ => h3 ⟨w, ?_, ?_, hl⟩⟩) ?_
    · rcases List.mem_cons.1 hw with rfl | hw
      · exact ht
      · exact hQ.mem w hw
    · rcases List.mem_cons.1 hw with rfl | hw
      · exact htb
      · exact (hB w hw).1
    rw [epIns_eq (show CanBlock isRecv x from hc)]
    have hmem : ∀ y ∈ ys, y = t ∨ y ∈ xs := fun y hy => mem_insPrio_sorted hsorted hy
    have hyT : ∀ y ∈ ys, y ∈ T := fun y hy => by
      rcases hmem y hy with rfl | hy'
      · exact ht
      · exact hQ.mem y hy'
    have hst : ∀ y ∈ ys, QueuedOn (L.mem s') e (if isRecv then 3 else 4) y := by
      intro y hy
      have hya := hP.tcb y (hyT y hy)
      have nst : ¬ EW e (tStA y) ∧ ¬ ∃ w ∈ t :: xs, TL w (tStA y) := by
        refine ⟨fun hw => ?_, fun ⟨w, hw, hl⟩ => ?_⟩
        · have := hP.et e he y (hyT y hy); unfold EW at hw; rw [val_st hya] at hw; omega
        · by_cases ew : w = y
          · subst ew; exact hl.not_tf (a_st hya).2
          · have hwT : w ∈ T := by
              rcases List.mem_cons.1 hw with rfl | hw
              · exact ht
              · exact hQ.mem w hw
            have := tcb_disj hP hwT (hyT y hy) (Ne.symm ew); unfold TL at hl; rw [val_st hya] at hl; omega
      have nbl : ¬ EW e (tBlockA y) ∧ ¬ ∃ w ∈ t :: xs, TL w (tBlockA y) := by
        refine ⟨fun hw => ?_, fun ⟨w, hw, hl⟩ => ?_⟩
        · have := hP.et e he y (hyT y hy); unfold EW at hw; rw [val_blk hya] at hw; omega
        · by_cases ew : w = y
          · subst ew; exact hl.not_tf (a_blk hya).2
          · have hwT : w ∈ T := by
              rcases List.mem_cons.1 hw with rfl | hw
              · exact ht
              · exact hQ.mem w hw
            have := tcb_disj hP hwT (hyT y hy) (Ne.symm ew); unfold TL at hl; rw [val_blk hya] at hl; omega
      rw [QueuedOn, hA3 _ (a_st hya).1 nst, hA3 _ (a_blk hya).1 nbl]
      rcases hmem y hy with rfl | hy'
      · exact ⟨htst, htb⟩
      · obtain ⟨y'', e1, hq''⟩ := stOf_canBlock hx hc y.bv (by rw [hxs]; exact List.mem_map_of_mem hy')
        have : y = y'' := eq_of_bv e1
        subst this
        exact hq''
    have hne : ys ≠ [] := insPrio_ne_nil hsorted
    cases isRecv with
    | true =>
      refine ⟨?_, ys, hne, rfl, hA1, fun y hy => by simpa using hst y hy⟩
      rw [hA2]; simp only [↓reduceIte, ep_state_vals]; decide
    | false =>
      refine ⟨?_, ys, hne, rfl, hA1, fun y hy => by simpa using hst y hy⟩
      rw [hA2]; simp only [Bool.false_eq_true, ↓reduceIte, ep_state_vals]; decide
  · exact hH.stable _ _ _ _ hSR hA4 (EpStep.ep hk)

end

end

end

end Fl4Proofs.P3.Endp
