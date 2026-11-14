/-
P1: `cancel_ipc` (ipc.rs; seL4 `cancelIPC`, MCS) keeps `SchedQueuesInv`.

A thread blocked on an endpoint or notification leaves the object's queue
(`ep_dequeue` / `ntfn_dequeue`; for a moment it is in the exception set `X`
of blocked threads outside their queue) and becomes inactive; the reply
object bookkeeping (`reply_unlink`, `reply_remove_tcb`) writes words of
reply objects and SCs, which are among the other objects' words `Ω`
(hypotheses `ReplyΩ`), and `clear_fault` writes a TCB field the invariant
does not read.
-/
import Fl4Proofs.P1.QueueSc
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64}
variable {Cs : Set U64}

/-! ## Addresses and small specs -/

def faultA (t : U64) : U64 := core.num.U64.wrapping_add t 3376#u64
def replyA (t : U64) : U64 := core.num.U64.wrapping_add t 3360#u64
def rTcbA (r : U64) : U64 := core.num.U64.wrapping_add r layout.reply.TCB
def rPrevA (r : U64) : U64 := core.num.U64.wrapping_add r layout.reply.PREV
def rNextA (r : U64) : U64 := core.num.U64.wrapping_add r layout.reply.NEXT
def scReplyA (sc : U64) : U64 := core.num.U64.wrapping_add sc layout.sc.REPLY

@[step] theorem obj.Tcb.set_fault_type.spec (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_fault_type st t s v ⦃ s' => s' = L.wr s (faultA t) v ⦄ := by
  unfold obj.Tcb.set_fault_type; step*; simp_all [faultA]
@[step] theorem obj.Tcb.reply_obj.spec (s : S) (t : obj.Tcb) :
    obj.Tcb.reply_obj st t s ⦃ v => v = L.mem s (replyA t) ⦄ := by
  unfold obj.Tcb.reply_obj; step*; simp_all [replyA]
@[step] theorem obj.Reply.set_tcb.spec (s : S) (r : obj.Reply) (v : U64) :
    obj.Reply.set_tcb st r s v ⦃ s' => s' = L.wr s (rTcbA r) v ⦄ := by
  unfold obj.Reply.set_tcb; step*; simp_all [rTcbA]
@[step] theorem obj.Reply.next.spec (s : S) (r : obj.Reply) :
    obj.Reply.next st r s ⦃ v => v = L.mem s (rNextA r) &&& ~~~1#u64 ⦄ := by
  unfold obj.Reply.next obj.Reply.next_raw; step*; simp_all [rNextA]
@[step] theorem obj.Reply.prev.spec (s : S) (r : obj.Reply) :
    obj.Reply.prev st r s ⦃ v => v = L.mem s (rPrevA r) &&& ~~~1#u64 ⦄ := by
  unfold obj.Reply.prev obj.Reply.prev_raw; step*; simp_all [rPrevA]
@[step] theorem obj.Reply.next_is_head.spec (s : S) (r : obj.Reply) :
    obj.Reply.next_is_head st r s ⦃ _ => True ⦄ := by
  unfold obj.Reply.next_is_head obj.Reply.next_raw; step*
@[step] theorem obj.Reply.set_prev.spec (s : S) (r : obj.Reply) (v : U64) :
    obj.Reply.set_prev st r s v ⦃ s' => ∃ w, s' = L.wr s (rPrevA r) w ⦄ := by
  unfold obj.Reply.set_prev obj.Reply.set_prev_raw; step*; subst_vars; exact ⟨_, rfl⟩
@[step] theorem obj.Reply.set_next.spec (s : S) (r : obj.Reply) (v : U64) (b : Bool) :
    obj.Reply.set_next st r s v b ⦃ s' => ∃ w, s' = L.wr s (rNextA r) w ⦄ := by
  unfold obj.Reply.set_next obj.Reply.set_next_raw; split <;> step* <;> subst_vars <;> exact ⟨_, rfl⟩
@[step] theorem obj.Sc.set_reply.spec (s : S) (sc : obj.Sc) (v : U64) :
    obj.Sc.set_reply st sc s v ⦃ s' => s' = L.wr s (scReplyA sc) v ⦄ := by
  unfold obj.Sc.set_reply; step*; simp_all [scReplyA]

theorem ts_inactive : sched.TS_INACTIVE = 0#u64 := by unfold sched.TS_INACTIVE; rfl
theorem ts_reply : sched.TS_BLOCKED_ON_REPLY = 5#u64 := by unfold sched.TS_BLOCKED_ON_REPLY; rfl

theorem not_blocked_inactive : ¬ Blocked sched.TS_INACTIVE := by
  obtain ⟨-, -, h3, h4, h6⟩ := ts_vals
  unfold Blocked; rw [h3, h4, h6, ts_inactive]; decide
theorem not_runnable_inactive : ¬ Runnable sched.TS_INACTIVE := by
  obtain ⟨h1, h2, -⟩ := ts_vals
  unfold Runnable; rw [h1, h2, ts_inactive]; decide
theorem not_blocked_reply : ¬ Blocked sched.TS_BLOCKED_ON_REPLY := by
  obtain ⟨-, -, h3, h4, h6⟩ := ts_vals
  unfold Blocked; rw [h3, h4, h6, ts_reply]; decide
theorem not_runnable_reply : ¬ Runnable sched.TS_BLOCKED_ON_REPLY := by
  obtain ⟨h1, h2, -⟩ := ts_vals
  unfold Runnable; rw [h1, h2, ts_reply]; decide
theorem not_runnable_of_blocked {v : U64} (h : Blocked v) : ¬ Runnable v := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := ts_vals
  unfold Blocked at h; unfold Runnable
  rw [h1, h2]; rw [h3, h4, h6] at h
  rcases h with rfl | rfl | rfl <;> decide

/-! ## Invariant helpers -/

theorem SchedQueuesInvX.congrX {X X' : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω X s Q R) (hX : ∀ y, y ∈ X ↔ y ∈ X') : SchedQueuesInvX st T Cs Ω X' s Q R := by
  have : X = X' := Set.ext hX
  subst this; exact h

/-- A thread that is not runnable is in no scheduler queue and no switch-to
candidate, so `set_thread_state` may give it any non-runnable state. -/
theorem hq_of_not_runnable {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {t v : U64}
    (h : SchedQueuesInvX st T Cs Ω X s Q R) (ht : t ∈ T) (hr : ¬ Runnable (L.mem s (stA t))) :
    (∀ c ∈ Cs, ∀ p : U64, p.val < 256 → t ∈ Q c p → Runnable v) ∧ (∀ c ∈ Cs, t ∈ R c → Runnable v) ∧
      (L.actionW s = t → Runnable v) :=
  ⟨fun c hc p hp hm => absurd (h.runQ c hc p hp t hm) hr, fun c hc hm => absurd (h.runR c hc t hm) hr,
   fun e => absurd (by have := (h.actOK (e ▸ ht)).1; rw [e] at this; exact this) hr⟩

/-- The fields of `t` other than its state, fault word and `Ep` links. -/
def KeepT (st : machine.Store S) [L : LawfulStore st] (t : U64) (s s' : S) : Prop :=
  ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3328 → K.val ≠ 3376 → K.val ≠ 3496 → K.val ≠ 3504 →
    L.mem s' (core.num.U64.wrapping_add t K) = L.mem s (core.num.U64.wrapping_add t K)

theorem KeepT.refl (t : U64) (s : S) : KeepT st t s s := fun _ _ _ _ _ _ _ => rfl
theorem KeepT.trans {t : U64} {s₁ s₂ s₃ : S} (h₁ : KeepT st t s₁ s₂) (h₂ : KeepT st t s₂ s₃) : KeepT st t s₁ s₃ :=
  fun K a b c d e f => (h₂ K a b c d e f).trans (h₁ K a b c d e f)

/-- After `set_thread_state t v`, `t`'s state is `v`, and its other fields
are kept. -/
theorem sched.set_thread_state.state {X : Set U64} (s : S) (t : obj.Tcb) (v : U64)
    (Q : U64 → U64 → List U64) (R : U64 → List U64) (h : SchedQueuesInvX st T Cs Ω X s Q R) (ht : t ∈ T) :
    sched.set_thread_state st s t v ⦃ s' => L.mem s' (stA t) = v ∧ KeepT st t s s' ⦄ := by
  have hta := h.tcbs t ht
  have hsa : Aligned (stA t) := by rw [stA_eq]; exact field_aligned hta (by simp) (by simp)
  have hN' := h.nodes _ h.cur
  unfold sched.set_thread_state sched.schedule_tcb
  step with obj.Tcb.set_state.spec as ⟨s1, s1_post⟩
  subst s1_post
  have e1 : L.mem (L.wr s (stA t) v) (stA t) = v := L.mem_wr_same hsa
  have k1 : KeepT st t s (L.wr s (stA t) v) := fun K hK hK8 h0 _ _ _ => by
    rw [stA_eq]
    exact L.mem_wr_ne (field_aligned hta (by simp) (by simp)) (field_aligned hta hK hK8)
      (fun e => field_ne hta hta (by simp) hK (fun _ => by simp; omega) (UScalar.eq_of_val_eq e))
  have kn : ∀ w : U64, KeepT st t (L.wr s (stA t) v)
      (L.wr (L.wr s (stA t) v) (L.nodeAt (L.wr s (stA t) v) (L.cpu (L.wr s (stA t) v)) layout.node.SCHED_ACTION) w) :=
    fun w K hK hK8 _ _ _ _ => by
      simp only [LawfulStore.cpu_wr, nodeAt_wr]
      exact L.mem_wr_ne (nodeAt_aligned hN' (by rw [act_val]; omega) (by rw [act_val])) (field_aligned hta hK hK8)
        (fun e => node_ne_field hN' (by rw [act_val]; omega) ht hta hK (UScalar.eq_of_val_eq e))
  step*
  all_goals first | exact ⟨e1, k1⟩ | skip
  subst_vars
  refine ⟨?_, k1.trans (kn _)⟩
  simp only [LawfulStore.cpu_wr, nodeAt_wr]
  rw [L.mem_wr_ne (nodeAt_aligned (h.nodes _ h.cur) (by rw [act_val]; omega) (by rw [act_val])) hsa]
  · exact e1
  · intro e; rw [stA_eq] at e
    exact node_ne_field hN' (by rw [act_val]; omega) ht hta (by simp) (UScalar.eq_of_val_eq e)

/-- `set_thread_state t INACTIVE` for a thread that is not runnable and in
no endpoint queue (or excepted). -/
theorem sts_inactive {X : Set U64} (s : S) (t : obj.Tcb) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInvX st T Cs Ω X s Q R) (ht : t ∈ T) (hr : ¬ Runnable (L.mem s (stA t)))
    (hx : t ∈ X ∨ ¬ Blocked (L.mem s (stA t))) :
    sched.set_thread_state st s t sched.TS_INACTIVE ⦃ s' =>
      SchedQueuesInvX st T Cs Ω {y | y ∈ X ∧ y ≠ t} s' Q R ∧ L.mem s' (stA t) = sched.TS_INACTIVE ∧
      KeepT st t s s' ⦄ :=
  WP.spec_and (sched.set_thread_state.inv s t _ Q R h ht not_blocked_inactive hx (hq_of_not_runnable h ht hr))
    (sched.set_thread_state.state s t _ Q R h ht)

/-- A write to a word of `Ω`. -/
theorem free_wr {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {a v : U64}
    (h : SchedQueuesInvX st T Cs Ω X s Q R) (ha : a ∈ Ω) : WritesIn st s (L.wr s a v) (L.Free s Ω Cs) :=
  (writesIn_wr (h.omega a ha).1).mono fun b hb => Or.inl (hb ▸ ha)

/-- Words of `Ω` are no TCB fields. -/
theorem omega_ne_field {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {a y K : U64}
    (h : SchedQueuesInvX st T Cs Ω X s Q R) (ha : a ∈ Ω) (hy : y ∈ T) (hK : K.val < 4096) :
    a ≠ core.num.U64.wrapping_add y K := fun e =>
  out_ne_field (h.omega a ha) hy (h.tcbs y hy) hK (congrArg UScalar.val e).symm

theorem mem_wr_omega {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {a b v : U64}
    (h : SchedQueuesInvX st T Cs Ω X s Q R) (ha : a ∈ Ω) {y K : U64} (hy : y ∈ T) (hK : K.val < 4096)
    (hK8 : K.val % 8 = 0) (hb : b = core.num.U64.wrapping_add y K) : L.mem (L.wr s a v) b = L.mem s b := by
  subst hb
  exact L.mem_wr_ne (h.omega a ha).1 (field_aligned (h.tcbs y hy) hK hK8)
    (fun e => omega_ne_field h ha hy hK (UScalar.eq_of_val_eq e))

/-! ## Endpoint and notification dequeue -/

theorem endpoint.ep_dequeue.foot (s : S) (ep : U64) (t : obj.Tcb) (xs : List U64)
    (hT : TcbPlaced T) (hE : EpPlaced T ep) (h : QueueRel (L.mem s) T .Ep (L.epQ s ep) xs) (ht : t ∈ xs) :
    endpoint.ep_dequeue st s ep t ⦃ s' => WritesIn st s s' (EpFoot xs ep) ⦄ := by
  unfold endpoint.ep_dequeue
  step*
  subst q_post
  refine WP.spec_bind (tcbqueue.remove.rel s .Ep _ t xs hT h ht) ?_
  rintro ⟨q1, s1⟩ h1
  simp only [WP.uncurry'_pair] at h1
  obtain ⟨-, hf1, -, -⟩ := h1
  step*
  all_goals subst_vars; exact reorder_foot_tail hE hf1.writesIn

theorem notification.ntfn_dequeue.foot (s : S) (n : U64) (t : obj.Tcb) (xs : List U64)
    (hT : TcbPlaced T) (hE : EpPlaced T n) (h : QueueRel (L.mem s) T .Ep (L.epQ s n) xs) (ht : t ∈ xs) :
    notification.ntfn_dequeue st s n t ⦃ s' => WritesIn st s s' (EpFoot xs n) ⦄ := by
  unfold notification.ntfn_dequeue
  step*
  subst q_post
  refine WP.spec_bind (tcbqueue.remove.rel s .Ep _ t xs hT h ht) ?_
  rintro ⟨q1, s1⟩ h1
  simp only [WP.uncurry'_pair] at h1
  obtain ⟨-, hf1, -, -⟩ := h1
  step*
  all_goals subst_vars; exact reorder_foot_tail hE hf1.writesIn

/-- What an endpoint footprint leaves alone: TCB fields other than the `Ep`
links, and the words of `Ω`. -/
theorem epfoot_keep {X : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    {E : Set U64} {EQ : U64 → List U64} {e : U64} {W : List U64}
    (h : SchedQueuesInvX st T Cs Ω X s Q R) (hEW : EpsWit st T Cs Ω X s E EQ) (he : e ∈ E)
    (hWT : ∀ w ∈ W, w ∈ T) (hw : WritesIn st s s' (EpFoot W e)) :
    (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 →
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
    (∀ a ∈ Ω, L.mem s' a = L.mem s a) := by
  have hT := h.tcbs
  obtain ⟨hE, -, -⟩ := hEW.1 e he
  have epv : ∀ (a : U64), (a = epHeadA e ∨ a = epTSA e) → a.val = e.val ∨ a.val = e.val + 8 := by
    rintro a (rfl | rfl)
    · exact Or.inl epHeadA_val
    · exact Or.inr (epTSA_val hE)
  refine ⟨fun y hy K hK hK8 h1 h2 => ?_, fun a ha => ?_⟩
  · refine hw.mem_eq (field_aligned (hT y hy) hK hK8) ?_
    rintro (⟨w, hw', e' | e'⟩ | e')
    · rw [nextA_eq'] at e'
      exact field_ne (hT y hy) (hT w (hWT w hw')) hK (by simp [nextOff]) (fun _ => by simp [nextOff]; exact h1) e'
    · rw [prevA_eq'] at e'
      exact field_ne (hT y hy) (hT w (hWT w hw')) hK (by simp [prevOff]) (fun _ => by simp [prevOff]; exact h2) e'
    · have hv := epv _ e'
      rw [field_val (hT y hy) hK] at hv
      have := hE.disj y hy
      omega
  · have ho := h.omega a ha
    refine hw.mem_eq ho.1 ?_
    rintro (⟨w, hw', e' | e'⟩ | e')
    · have := congrArg UScalar.val e'; rw [nextA_val (hT w (hWT w hw'))] at this
      have := ho.2.1 w (hWT w hw'); simp [nextOff] at *; omega
    · have := congrArg UScalar.val e'; rw [prevA_val (hT w (hWT w hw'))] at this
      have := ho.2.1 w (hWT w hw'); simp [prevOff] at *; omega
    · have hv := epv _ e'
      have := hEW.2.2.1 e he a ha
      omega

/-- seL4 `tcbEPDequeue` of a blocked thread from the object it is blocked
on: it leaves the queue and joins the exception set. -/
theorem dequeue_blocked_inv {X : Set U64} (s : S) (t : obj.Tcb) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInvX st T Cs Ω X s Q R) (ht : t ∈ T) (htX : t ∉ X) (hb : Blocked (L.mem s (stA t)))
    (deq : S → U64 → obj.Tcb → Result S)
    (hrel : ∀ (xs : List U64), EpPlaced T (L.mem s (blockA t)) →
      QueueRel (L.mem s) T .Ep (L.epQ s (L.mem s (blockA t))) xs → t ∈ xs →
      deq s (L.mem s (blockA t)) t ⦃ s' => QueueRel (L.mem s') T .Ep (L.epQ s' (L.mem s (blockA t))) (xs.erase t) ⦄)
    (hfoot : ∀ (xs : List U64), EpPlaced T (L.mem s (blockA t)) →
      QueueRel (L.mem s) T .Ep (L.epQ s (L.mem s (blockA t))) xs → t ∈ xs →
      deq s (L.mem s (blockA t)) t ⦃ s' => WritesIn st s s' (EpFoot xs (L.mem s (blockA t))) ⦄) :
    deq s (L.mem s (blockA t)) t ⦃ s' => SchedQueuesInvX st T Cs Ω {y | y ∈ X ∨ y = t} s' Q R ∧
      (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 →
        L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ a ∈ Ω, L.mem s' a = L.mem s a) ⦄ := by
  obtain ⟨E, EQ, hEW⟩ := h.eps
  obtain ⟨he, hmem⟩ := hEW.2.2.2.2 t ht htX hb
  obtain ⟨hE, -, hq⟩ := hEW.1 _ he
  refine WP.spec_mono (WP.spec_and (hrel _ hE hq hmem) (hfoot _ hE hq hmem)) ?_
  rintro s' ⟨hq', hw⟩
  have nd := hq.nodup
  have hWT : ∀ w ∈ EQ (L.mem s (blockA t)), w ∈ T := hq.mem
  refine ⟨inv_ep_step h hEW he hw hq' (fun y hy => List.mem_of_mem_erase hy) ?_ (fun y hy => Or.inl hy) ?_ ?_,
    epfoot_keep h hEW he hWT hw⟩
  · intro y hy hn
    by_cases e : y = t
    · exact Or.inr e
    · exact absurd ((List.mem_erase_of_ne e).2 hy) hn
  · rintro y (hy | rfl)
    · exact Or.inl hy
    · exact Or.inr hmem
  · intro y hy hyX
    rw [nd.mem_erase_iff] at hy
    rcases hyX with hyX | rfl
    · exact (hEW.2.2.2.1 _ he y hy.2).1 hyX
    · exact hy.1 rfl

theorem endpoint.ep_dequeue.inv {X : Set U64} (s : S) (t : obj.Tcb) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInvX st T Cs Ω X s Q R) (ht : t ∈ T) (htX : t ∉ X) (hb : Blocked (L.mem s (stA t))) :
    endpoint.ep_dequeue st s (L.mem s (blockA t)) t ⦃ s' => SchedQueuesInvX st T Cs Ω {y | y ∈ X ∨ y = t} s' Q R ∧
      (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 →
        L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ a ∈ Ω, L.mem s' a = L.mem s a) ⦄ :=
  dequeue_blocked_inv s t Q R h ht htX hb (endpoint.ep_dequeue st)
    (fun xs hE hq hm => WP.spec_mono (endpoint.ep_dequeue.rel s _ t xs h.tcbs hE hq hm) fun _ h' => h'.1)
    (fun xs hE hq hm => endpoint.ep_dequeue.foot s _ t xs h.tcbs hE hq hm)

theorem notification.ntfn_dequeue.inv {X : Set U64} (s : S) (t : obj.Tcb) (Q : U64 → U64 → List U64)
    (R : U64 → List U64)
    (h : SchedQueuesInvX st T Cs Ω X s Q R) (ht : t ∈ T) (htX : t ∉ X) (hb : Blocked (L.mem s (stA t))) :
    notification.ntfn_dequeue st s (L.mem s (blockA t)) t ⦃ s' =>
      SchedQueuesInvX st T Cs Ω {y | y ∈ X ∨ y = t} s' Q R ∧
      (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 →
        L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ a ∈ Ω, L.mem s' a = L.mem s a) ⦄ :=
  dequeue_blocked_inv s t Q R h ht htX hb (notification.ntfn_dequeue st)
    (fun xs hE hq hm => WP.spec_mono (notification.ntfn_dequeue.rel s _ t xs h.tcbs hE hq hm) fun _ h' => h'.1)
    (fun xs hE hq hm => notification.ntfn_dequeue.foot s _ t xs h.tcbs hE hq hm)

/-! ## Writes to `Ω` and to the fault field -/

theorem wr_omega {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {a v : U64}
    (h : SchedQueuesInvX st T Cs Ω X s Q R) (ha : a ∈ Ω) :
    SchedQueuesInvX st T Cs Ω X (L.wr s a v) Q R ∧
      ∀ y ∈ T, L.mem (L.wr s a v) (stA y) = L.mem s (stA y) :=
  ⟨inv_of_free h (free_wr h ha), fun y hy => mem_wr_omega h ha hy (by simp) (by simp) (stA_eq y)⟩

/-- `clear_fault` writes `t`'s fault word. -/
theorem faults.clear_fault.inv {X : Set U64} (s : S) (t : obj.Tcb) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInvX st T Cs Ω X s Q R) (ht : t ∈ T) :
    faults.clear_fault st s t ⦃ s' => SchedQueuesInvX st T Cs Ω X s' Q R ∧
      (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (y = t → K.val ≠ 3376) →
        L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ a ∈ Ω, L.mem s' a = L.mem s a) ∧ L.actionW s' = L.actionW s ⦄ := by
  unfold faults.clear_fault
  refine WP.spec_mono (obj.Tcb.set_fault_type.spec s t _) fun s' e => ?_
  subst e
  rw [show faultA t = core.num.U64.wrapping_add t 3376#u64 from rfl]
  have hT := h.tcbs
  have hta := hT t ht
  have ha : Aligned (core.num.U64.wrapping_add t 3376#u64) := field_aligned hta (by simp) (by simp)
  refine ⟨inv_wr_field h ht (K := 3376#u64) (by simp) (by simp) (by simp), fun y hy K hK hK8 hne => ?_,
    fun a ha' => ?_, ?_⟩
  · exact L.mem_wr_ne ha (field_aligned (hT y hy) hK hK8)
      (fun e => field_ne hta (hT y hy) (by simp) hK (fun e' => by subst e'; simpa using (hne rfl).symm)
        (UScalar.eq_of_val_eq e))
  · exact L.mem_wr_ne ha (h.omega a ha').1 (fun e => omega_ne_field h ha' ht (K := 3376#u64) (by simp)
      (UScalar.eq_of_val_eq e).symm)
  · unfold LawfulStore.actionW
    rw [L.cpu_wr]
    exact nodeword_wr_field (h.nodes _ h.cur) ht hta (K := 3376#u64) (by simp) (by simp) (by rw [act_val]; omega)
      (by rw [act_val])

theorem keep_omega {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {a v t : U64}
    (h : SchedQueuesInvX st T Cs Ω X s Q R) (ha : a ∈ Ω) (ht : t ∈ T) : KeepT st t s (L.wr s a v) :=
  fun _ hK hK8 _ _ _ _ => mem_wr_omega h ha ht hK hK8 rfl

/-- `reply_unlink`: the reply object forgets `t` (a word of `Ω`), and `t`
becomes inactive. -/
theorem ipc.reply_unlink.inv {X : Set U64} (s : S) (r : obj.Reply) (t : obj.Tcb) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (h : SchedQueuesInvX st T Cs Ω X s Q R) (ht : t ∈ T) (hr : rTcbA r ∈ Ω)
    (hnr : ¬ Runnable (L.mem s (stA t))) (hx : t ∈ X ∨ ¬ Blocked (L.mem s (stA t))) :
    ipc.reply_unlink st s r t ⦃ s' => SchedQueuesInvX st T Cs Ω {y | y ∈ X ∧ y ≠ t} s' Q R ∧
      L.mem s' (stA t) = sched.TS_INACTIVE ∧ KeepT st t s s' ⦄ := by
  unfold ipc.reply_unlink
  step with obj.Reply.set_tcb.spec as ⟨s1, s1_post⟩
  subst s1_post
  obtain ⟨h1, e1⟩ := wr_omega (v := 0#u64) h hr
  rw [← e1 t ht] at hnr hx
  exact WP.spec_mono (sts_inactive _ t Q R h1 ht hnr hx) fun s' ⟨h', e', k'⟩ =>
    ⟨h', e', (keep_omega h hr ht).trans k'⟩

/-- The reply-object words `reply_remove_tcb` writes are among `Ω`. -/
def ReplyΩ (st : machine.Store S) [L : LawfulStore st] (Ω : Set U64) (s : S) (t : U64) : Prop :=
  rTcbA (L.mem s (replyA t)) ∈ Ω ∧ rPrevA (L.mem s (replyA t)) ∈ Ω ∧ rNextA (L.mem s (replyA t)) ∈ Ω ∧
  (L.mem s (rNextA (L.mem s (replyA t))) &&& ~~~1#u64 ≠ 0#u64 →
    scReplyA (L.mem s (rNextA (L.mem s (replyA t))) &&& ~~~1#u64) ∈ Ω ∧
    rPrevA (L.mem s (rNextA (L.mem s (replyA t))) &&& ~~~1#u64) ∈ Ω) ∧
  (L.mem s (rPrevA (L.mem s (replyA t))) &&& ~~~1#u64 ≠ 0#u64 →
    rNextA (L.mem s (rPrevA (L.mem s (replyA t))) &&& ~~~1#u64) ∈ Ω)

/-- seL4 `reply_remove_tcb`. -/
theorem ipc.reply_remove_tcb.inv {X : Set U64} (s : S) (t : obj.Tcb) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (h : SchedQueuesInvX st T Cs Ω X s Q R) (ht : t ∈ T) (hR : ReplyΩ st Ω s t)
    (hnr : ¬ Runnable (L.mem s (stA t))) (hx : t ∈ X ∨ ¬ Blocked (L.mem s (stA t))) :
    ipc.reply_remove_tcb st s t ⦃ s' => SchedQueuesInvX st T Cs Ω {y | y ∈ X ∧ y ≠ t} s' Q R ∧
      L.mem s' (stA t) = sched.TS_INACTIVE ∧ KeepT st t s s' ⦄ := by
  obtain ⟨hr0, hr1, hr2, hn, hp⟩ := hR
  unfold ipc.reply_remove_tcb
  step with obj.Tcb.reply_obj.spec as ⟨i, i_post⟩
  step with obj.Reply.next.spec as ⟨next, next_post⟩
  step with obj.Reply.prev.spec as ⟨prev, prev_post⟩
  subst i_post next_post prev_post
  refine WP.spec_bind (Pₘ := fun s1 => SchedQueuesInvX st T Cs Ω X s1 Q R ∧
      L.mem s1 (stA t) = L.mem s (stA t) ∧ KeepT st t s s1) ?_ ?_
  · split
    · rename_i hne
      obtain ⟨hn1, hn2⟩ := hn (by simpa using hne)
      step with obj.Reply.next_is_head.spec as ⟨b⟩
      split
      · refine WP.spec_mono (obj.Sc.set_reply.spec s _ 0#u64) fun s1 e => ?_
        subst e; obtain ⟨h1, e1⟩ := wr_omega (v := 0#u64) h hn1; exact ⟨h1, e1 t ht, keep_omega h hn1 ht⟩
      · refine WP.spec_mono (obj.Reply.set_prev.spec s _ 0#u64) fun s1 ⟨w, e⟩ => ?_
        subst e; obtain ⟨h1, e1⟩ := wr_omega (v := w) h hn2; exact ⟨h1, e1 t ht, keep_omega h hn2 ht⟩
    · exact (WP.spec_ok _).2 ⟨h, rfl, KeepT.refl _ _⟩
  rintro s1 ⟨h1, e1, k1⟩
  refine WP.spec_bind (Pₘ := fun s2 => SchedQueuesInvX st T Cs Ω X s2 Q R ∧
      L.mem s2 (stA t) = L.mem s (stA t) ∧ KeepT st t s s2) ?_ ?_
  · split
    · rename_i hne
      refine WP.spec_mono (obj.Reply.set_next.spec s1 _ 0#u64 false) fun s2 ⟨w, e⟩ => ?_
      subst e; obtain ⟨h2, e2⟩ := wr_omega (v := w) h1 (hp (by simpa using hne))
      exact ⟨h2, (e2 t ht).trans e1, k1.trans (keep_omega h1 (hp (by simpa using hne)) ht)⟩
    · exact (WP.spec_ok _).2 ⟨h1, e1, k1⟩
  rintro s2 ⟨h2, e2, k2⟩
  refine WP.spec_bind (obj.Reply.set_prev.spec s2 _ 0#u64) ?_
  rintro s3 ⟨w3, rfl⟩
  obtain ⟨h3, e3⟩ := wr_omega (v := w3) h2 hr1
  refine WP.spec_bind (obj.Reply.set_next.spec _ _ 0#u64 false) ?_
  rintro s4 ⟨w4, rfl⟩
  obtain ⟨h4, e4⟩ := wr_omega (v := w4) h3 hr2
  have est : L.mem (L.wr (L.wr s2 (rPrevA (L.mem s (replyA t))) w3) (rNextA (L.mem s (replyA t))) w4) (stA t) =
      L.mem s (stA t) := (e4 t ht).trans ((e3 t ht).trans e2)
  rw [← est] at hnr hx
  exact WP.spec_mono (ipc.reply_unlink.inv _ _ t Q R h4 ht hr0 hnr hx) fun s' ⟨h', e', k'⟩ =>
    ⟨h', e', ((k2.trans (keep_omega h2 hr1 ht)).trans (keep_omega h3 hr2 ht)).trans k'⟩

/-- seL4 `cancelSignal`. -/
theorem notification.cancel_signal.inv {X : Set U64} (s : S) (t : obj.Tcb) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (h : SchedQueuesInvX st T Cs Ω X s Q R) (ht : t ∈ T) (htX : t ∉ X)
    (hb : Blocked (L.mem s (stA t))) :
    notification.cancel_signal st s t (L.mem s (blockA t)) ⦃ s' => SchedQueuesInvX st T Cs Ω X s' Q R ∧
      L.mem s' (stA t) = sched.TS_INACTIVE ∧ KeepT st t s s' ⦄ := by
  unfold notification.cancel_signal
  refine WP.spec_bind (notification.ntfn_dequeue.inv s t Q R h ht htX hb) ?_
  rintro s1 ⟨h1, f1, -⟩
  have e1 : L.mem s1 (stA t) = L.mem s (stA t) := by rw [stA_eq]; exact f1 t ht _ (by simp) (by simp) (by simp) (by simp)
  refine WP.spec_mono (sts_inactive s1 t Q R h1 ht (by rw [e1]; exact not_runnable_of_blocked hb)
    (Or.inl (Or.inr rfl))) fun s2 ⟨h2, e2, k2⟩ => ⟨h2.congrX fun y => ?_, e2,
      KeepT.trans (fun K a b _ _ c d => f1 t ht K a b c d) k2⟩
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hy | rfl, hne⟩
    · exact hy
    · exact absurd rfl hne
  · intro hy; exact ⟨Or.inl hy, fun e => htX (e ▸ hy)⟩

theorem ReplyΩ.transport {s s' : S} {t : U64} (hR : ReplyΩ st Ω s t) (hr : L.mem s' (replyA t) = L.mem s (replyA t))
    (ho : ∀ a ∈ Ω, L.mem s' a = L.mem s a) : ReplyΩ st Ω s' t := by
  obtain ⟨h0, h1, h2, hn, hp⟩ := hR
  unfold ReplyΩ
  rw [hr, ho _ h1, ho _ h2]
  exact ⟨h0, h1, h2, hn, hp⟩

theorem empty_congr {t : U64} : ∀ y, y ∈ {y : U64 | y ∈ (∅ : Set U64) ∧ y ≠ t} ↔ y ∈ (∅ : Set U64) := by
  intro y; simp

/-- After the endpoint dequeue: the exception set is at most `{t}`, and `t`
is not runnable. -/
def ExcT (X : Set U64) (t : U64) : Prop := ∀ y ∈ X, y = t

theorem ep_tail {X : Set U64} (s3 : S) (t : obj.Tcb) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h3 : SchedQueuesInvX st T Cs Ω X s3 Q R) (ht : t ∈ T) (hX : ExcT X t)
    (hnr : ¬ Runnable (L.mem s3 (stA t))) (hx : t ∈ X ∨ ¬ Blocked (L.mem s3 (stA t))) :
    sched.set_thread_state st s3 t sched.TS_INACTIVE ⦃ s' =>
      SchedQueuesInv st T Cs Ω s' Q R ∧ L.mem s' (stA t) = sched.TS_INACTIVE ∧ KeepT st t s3 s' ⦄ :=
  WP.spec_mono (sts_inactive s3 t Q R h3 ht hnr hx) fun s' ⟨h', e', k'⟩ => ⟨h'.congrX fun y => by
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_not]
    exact hX y, e', k'⟩

/-- The endpoint branch of `cancel_ipc` (blocked on send or receive). -/
theorem ep_branch {A : Type _} (a : A) (s1 : S) (t : obj.Tcb) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h1 : SchedQueuesInv st T Cs Ω s1 Q R) (ht : t ∈ T) (hb : Blocked (L.mem s1 (stA t))) (rcv : Prop)
    [Decidable rcv] (hrecv : rcv → L.mem s1 (replyA t) ≠ 0#u64 → rTcbA (L.mem s1 (replyA t)) ∈ Ω) :
    (do
      let ep ← obj.Tcb.block_obj st t s1
      let s2 ← endpoint.ep_dequeue st s1 ep t
      let s3 ← if rcv then do
          let i ← obj.Tcb.reply_obj st t s2
          if (i != 0#u64) = true then ipc.reply_unlink st s2 i t else ok s2
        else ok s2
      let s4 ← sched.set_thread_state st s3 t sched.TS_INACTIVE
      ok (s4, a)) ⦃ s' _ =>
      SchedQueuesInv st T Cs Ω s' Q R ∧ L.mem s' (stA t) = sched.TS_INACTIVE ∧ KeepT st t s1 s' ⦄ := by
  step with obj.Tcb.block_obj.spec as ⟨ep, ep_post⟩
  subst ep_post
  refine WP.spec_bind (endpoint.ep_dequeue.inv s1 t Q R h1 ht (by simp) hb) ?_
  rintro s2 ⟨h2, f2, o2⟩
  have e2 : L.mem s2 (stA t) = L.mem s1 (stA t) := by
    rw [stA_eq]; exact f2 t ht _ (by simp) (by simp) (by simp) (by simp)
  have r2 : L.mem s2 (replyA t) = L.mem s1 (replyA t) := f2 t ht _ (by simp) (by simp) (by simp) (by simp)
  have hX2 : ExcT {y | y ∈ (∅ : Set U64) ∨ y = t} t := fun y hy => by simpa using hy
  have hnr2 : ¬ Runnable (L.mem s2 (stA t)) := by rw [e2]; exact not_runnable_of_blocked hb
  have k2 : KeepT st t s1 s2 := fun K a b _ _ c d => f2 t ht K a b c d
  refine WP.spec_bind (Pₘ := fun s3 => ∃ X3, SchedQueuesInvX st T Cs Ω X3 s3 Q R ∧ ExcT X3 t ∧
      ¬ Runnable (L.mem s3 (stA t)) ∧ (t ∈ X3 ∨ ¬ Blocked (L.mem s3 (stA t))) ∧ KeepT st t s1 s3) ?_ ?_
  · split
    · rename_i hrc
      step with obj.Tcb.reply_obj.spec as ⟨i, i_post⟩
      split
      · rename_i hi
        have hi' : L.mem s1 (replyA t) ≠ 0#u64 := by rw [← r2, ← i_post]; simpa using hi
        have hr : rTcbA i ∈ Ω := by rw [i_post, r2]; exact hrecv hrc hi'
        refine WP.spec_mono (ipc.reply_unlink.inv s2 i t Q R h2 ht hr hnr2 (Or.inl (Or.inr rfl)))
          fun s3 ⟨h3, e3, k3⟩ => ⟨_, h3, fun y hy => ?_, by rw [e3]; exact not_runnable_inactive,
            Or.inr (by rw [e3]; exact not_blocked_inactive), k2.trans k3⟩
        obtain ⟨hy1, hy2⟩ := hy
        rcases hy1 with hy1 | hy1
        · exact absurd hy1 (Set.notMem_empty _)
        · exact absurd hy1 hy2
      · exact (WP.spec_ok _).2 ⟨_, h2, hX2, hnr2, Or.inl (Or.inr rfl), k2⟩
    · exact (WP.spec_ok _).2 ⟨_, h2, hX2, hnr2, Or.inl (Or.inr rfl), k2⟩
  rintro s3 ⟨X3, h3, hX3, hnr3, hx3, k3⟩
  refine WP.spec_bind (ep_tail s3 t Q R h3 ht hX3 hnr3 hx3) fun s4 ⟨h4, e4, k4⟩ => ?_
  simp only [WP.spec_ok, WP.uncurry'_pair]; exact ⟨h4, e4, k3.trans k4⟩

/-- seL4 `cancelIPC` (MCS) keeps the invariant.  Afterwards the thread is
not blocked: it is inactive, or (when it was not blocked) its state and the
scheduler action are as before. -/
theorem ipc.cancel_ipc.inv {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (t : obj.Tcb)
    (Q : U64 → U64 → List U64) (R : U64 → List U64) (h : SchedQueuesInv st T Cs Ω s Q R) (ht : t ∈ T)
    (hrecv : L.mem s (stA t) = sched.TS_BLOCKED_ON_RECV → L.mem s (replyA t) ≠ 0#u64 →
      rTcbA (L.mem s (replyA t)) ∈ Ω)
    (hreply : L.mem s (stA t) = sched.TS_BLOCKED_ON_REPLY → ReplyΩ st Ω s t) :
    ipc.cancel_ipc st ar s a t ⦃ s' _ => SchedQueuesInv st T Cs Ω s' Q R ∧ ¬ Blocked (L.mem s' (stA t)) ∧
      (L.mem s' (stA t) = sched.TS_INACTIVE ∨
        (L.mem s' (stA t) = L.mem s (stA t) ∧ L.actionW s' = L.actionW s)) ∧ KeepT st t s s' ⦄ := by
  unfold ipc.cancel_ipc
  refine WP.spec_bind (faults.clear_fault.inv s t Q R h ht) ?_
  rintro s1 ⟨h1, f1, o1, a1⟩
  have e1 : L.mem s1 (stA t) = L.mem s (stA t) := by
    rw [stA_eq]; exact f1 t ht _ (by simp) (by simp) (fun _ => by simp)
  have r1 : L.mem s1 (replyA t) = L.mem s (replyA t) := f1 t ht _ (by simp) (by simp) (fun _ => by simp)
  obtain ⟨-, -, hr3, hs4, hn6⟩ := ts_vals
  have k1 : KeepT st t s s1 := fun K a b _ c _ _ => f1 t ht K a b (fun _ => c)
  have done : ∀ s', SchedQueuesInv st T Cs Ω s' Q R ∧ L.mem s' (stA t) = sched.TS_INACTIVE ∧ KeepT st t s1 s' →
      SchedQueuesInv st T Cs Ω s' Q R ∧ ¬ Blocked (L.mem s' (stA t)) ∧
      (L.mem s' (stA t) = sched.TS_INACTIVE ∨
        (L.mem s' (stA t) = L.mem s (stA t) ∧ L.actionW s' = L.actionW s)) ∧ KeepT st t s s' :=
    fun s' ⟨h', e', k'⟩ => ⟨h', by rw [e']; exact not_blocked_inactive, Or.inl e', k1.trans k'⟩
  step with obj.Tcb.state.spec as ⟨stt, stt_post⟩
  split
  · rename_i hs
    have hb : Blocked (L.mem s1 (stA t)) := by rw [← stt_post, hs]; exact Or.inl rfl
    refine WP.spec_mono (ep_branch a s1 t Q R h1 ht hb (stt = sched.TS_BLOCKED_ON_RECV) ?_) ?_
    · intro hrc; rw [hs] at hrc; rw [hs4, hr3] at hrc; simp at hrc
    · rintro ⟨s4, a4⟩ h4; exact done s4 h4
  split
  · rename_i _ hs
    have hb : Blocked (L.mem s1 (stA t)) := by rw [← stt_post, hs]; exact Or.inr (Or.inl rfl)
    have hE := ep_branch a s1 t Q R h1 ht hb True
      (fun _ hi => by rw [r1] at hi ⊢; exact hrecv (by rw [← e1, ← stt_post, hs]) hi)
    simp only [↓reduceIte] at hE
    exact WP.spec_mono hE fun r h4 => by obtain ⟨s4, a4⟩ := r; exact done s4 h4
  split
  · rename_i _ _ hs
    have hb : Blocked (L.mem s1 (stA t)) := by rw [← stt_post, hs]; exact Or.inr (Or.inr rfl)
    step with obj.Tcb.block_obj.spec as ⟨i, i_post⟩
    subst i_post
    refine WP.spec_bind (notification.cancel_signal.inv s1 t Q R h1 ht (by simp) hb) ?_
    intro s2 h2; exact (WP.spec_ok _).2 (done s2 h2)
  split
  · rename_i _ _ _ hs
    have hR : ReplyΩ st Ω s1 t := (hreply (by rw [← e1, ← stt_post, hs])).transport r1 o1
    have hst : L.mem s1 (stA t) = sched.TS_BLOCKED_ON_REPLY := by rw [← stt_post, hs]
    refine WP.spec_bind (ipc.reply_remove_tcb.inv s1 t Q R h1 ht hR (by rw [hst]; exact not_runnable_reply)
      (Or.inr (by rw [hst]; exact not_blocked_reply))) ?_
    rintro s2 ⟨h2, e2, k2⟩
    exact (WP.spec_ok _).2 (done s2 ⟨h2.congrX empty_congr, e2, k2⟩)
  · rename_i h1' h2' h3' _
    simp only [WP.spec_ok, WP.uncurry'_pair]
    refine ⟨h1, ?_, Or.inr ⟨e1, a1⟩, k1⟩
    rw [← stt_post]
    rintro (e | e | e)
    · exact h1' e
    · exact h2' e
    · exact h3' e

/-! ## `suspend` -/

def yieldA (t : U64) : U64 := core.num.U64.wrapping_add t 3472#u64
def scYieldFromA (sc : U64) : U64 := core.num.U64.wrapping_add sc layout.sc.YIELD_FROM

@[step] theorem obj.Tcb.yield_to.spec (s : S) (t : obj.Tcb) :
    obj.Tcb.yield_to st t s ⦃ v => v = L.mem s (yieldA t) ⦄ := by
  unfold obj.Tcb.yield_to; step*; simp_all [yieldA]
@[step] theorem obj.Tcb.set_yield_to.spec (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_yield_to st t s v ⦃ s' => s' = L.wr s (yieldA t) v ⦄ := by
  unfold obj.Tcb.set_yield_to; step*; simp_all [yieldA]
@[step] theorem obj.Sc.set_yield_from.spec (s : S) (sc : obj.Sc) (v : U64) :
    obj.Sc.set_yield_from st sc s v ⦃ s' => s' = L.wr s (scYieldFromA sc) v ⦄ := by
  unfold obj.Sc.set_yield_from; step*; simp_all [scYieldFromA]
@[step] theorem obj.Tcb.reg.spec (s : S) (t : obj.Tcb) (r : U64) : obj.Tcb.reg st t s r ⦃ _ => True ⦄ := by
  unfold obj.Tcb.reg; step*
theorem obj.Tcb.set_reg.fault_ip (s : S) (t : obj.Tcb) (v : U64) (ht : TcbAddr t) :
    obj.Tcb.set_reg st t s layout.reg.FAULT_IP v ⦃ s' => s' = L.wr s (core.num.U64.wrapping_add t 392#u64) v ⦄ := by
  unfold obj.Tcb.set_reg
  step*
  subst_vars
  congr 1
  have := ht.fits
  apply UScalar.eq_of_val_eq
  simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits,
    layout.tcb.REGS, layout.reg.FAULT_IP]
  try omega

/-- A write to a field of `t` the invariant does not read. -/
theorem field_wr_keep {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {t K v : U64}
    (h : SchedQueuesInvX st T Cs Ω X s Q R) (ht : t ∈ T) (hK : K.val < 4096) (hK8 : K.val % 8 = 0)
    (hKn : K.val ≠ 3480 ∧ K.val ≠ 3488 ∧ K.val ≠ 3496 ∧ K.val ≠ 3504 ∧ K.val ≠ 3592 ∧ K.val ≠ 3520 ∧
      K.val ≠ 3448 ∧ K.val ≠ 3328 ∧ K.val ≠ 3336) :
    SchedQueuesInvX st T Cs Ω X (L.wr s (core.num.U64.wrapping_add t K) v) Q R ∧
      (∀ K' : U64, K'.val < 4096 → K'.val % 8 = 0 → K'.val ≠ K.val →
        L.mem (L.wr s (core.num.U64.wrapping_add t K) v) (core.num.U64.wrapping_add t K') =
          L.mem s (core.num.U64.wrapping_add t K')) ∧
      L.actionW (L.wr s (core.num.U64.wrapping_add t K) v) = L.actionW s := by
  have hta := h.tcbs t ht
  have ha := field_aligned hta hK hK8
  refine ⟨inv_wr_field h ht hK hK8 hKn, fun K' h1 h2 hne => ?_, ?_⟩
  · exact L.mem_wr_ne ha (field_aligned hta h1 h2)
      (fun e => field_ne hta hta hK h1 (fun _ => Ne.symm hne) (UScalar.eq_of_val_eq e))
  · unfold LawfulStore.actionW
    rw [L.cpu_wr]
    exact nodeword_wr_field (h.nodes _ h.cur) ht hta hK hK8 (by rw [act_val]; omega) (by rw [act_val])

/-- A queue footprint keeps the action word and `t`'s fields other than the
links and `IN_QUEUES`. -/
theorem qfoot_act {X : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {W : List U64}
    {c t : U64} {P : Nat → Prop} (h : SchedQueuesInvX st T Cs Ω X s Q R) (hW : ∀ w ∈ W, w ∈ T) (hc : c ∈ Cs)
    (ht : t ∈ T) (hP : ¬ P 16) (hw : WritesIn st s s' (L.QFoot s W c P t)) :
    L.actionW s' = L.actionW s := by
  unfold LawfulStore.actionW
  rw [hw.2.1]
  exact node_qfoot h.tcbs hW (h.nodes c hc) (h.nodes _ h.cur) ht hw (h.nodes _ h.cur) (by rw [act_val]; omega)
    (by rw [act_val]) (fun _ => by rw [act_val]; exact hP) (fun _ => by rw [act_val]; omega)

/-- seL4 `suspend` (MCS) keeps the invariant, for a thread that is not the
switch-to candidate (seL4 `scheduler_act_not t`): `set_thread_state` only
reschedules for the current thread, so suspending the candidate would leave
`schedule` switching to an inactive thread. -/
theorem sched.suspend.inv {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (t : obj.Tcb)
    (Q : U64 → U64 → List U64) (R : U64 → List U64) (h : SchedQueuesInv st T Cs Ω s Q R) (ht : t ∈ T)
    (hrecv : L.mem s (stA t) = sched.TS_BLOCKED_ON_RECV → L.mem s (replyA t) ≠ 0#u64 →
      rTcbA (L.mem s (replyA t)) ∈ Ω)
    (hreply : L.mem s (stA t) = sched.TS_BLOCKED_ON_REPLY → ReplyΩ st Ω s t)
    (hna : L.actionW s ≠ t)
    (hyield : L.mem s (yieldA t) ≠ 0#u64 → scYieldFromA (L.mem s (yieldA t)) ∈ Ω) :
    sched.suspend st ar s a t ⦃ s' _ => ∃ Q' R', SchedQueuesInv st T Cs Ω s' Q' R' ⦄ := by
  have hT := h.tcbs
  have hta := hT t ht
  unfold sched.suspend
  refine WP.spec_bind (ipc.cancel_ipc.inv s a t Q R h ht hrecv hreply) ?_
  rintro ⟨s1, a1⟩ ⟨h1, nb1, hst1, k1⟩
  try simp only [WP.uncurry'_pair]
  have na1 : L.actionW s1 ≠ t := by
    rcases hst1 with e | ⟨-, e⟩
    · intro ea
      have := (h1.actOK (ea ▸ ht)).1; rw [ea, e] at this; exact not_runnable_inactive this
    · rw [e]; exact hna
  have y1 : L.mem s1 (yieldA t) = L.mem s (yieldA t) := k1 _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  step with obj.Tcb.state.spec as ⟨i, i_post⟩
  -- the fault-IP copy
  refine WP.spec_bind (Pₘ := fun s2 => SchedQueuesInv st T Cs Ω s2 Q R ∧ ¬ Blocked (L.mem s2 (stA t)) ∧
      L.actionW s2 ≠ t ∧ L.mem s2 (yieldA t) = L.mem s (yieldA t)) ?_ ?_
  · split
    · step with obj.Tcb.reg.spec as ⟨ip⟩
      refine WP.spec_mono (obj.Tcb.set_reg.fault_ip s1 t ip hta) fun s2 e => ?_
      subst e
      obtain ⟨h2, f2, a2⟩ := field_wr_keep (K := 392#u64) (v := ip) h1 ht (by simp) (by simp) (by simp)
      refine ⟨h2, ?_, by rw [a2]; exact na1, by rw [← y1]; exact f2 _ (by simp) (by simp) (by simp)⟩
      rw [stA_eq, f2 _ (by simp) (by simp) (by simp), ← stA_eq]; exact nb1
    · exact (WP.spec_ok _).2 ⟨h1, nb1, na1, y1⟩
  rintro s2 ⟨h2, nb2, na2, y2⟩
  -- out of the ready queue
  have hc2 := h2.aff t ht
  have hp2 := h2.prio t ht
  have hW2 : ∀ w ∈ Q (L.mem s2 (affA t)) (L.mem s2 (prioA t)), w ∈ T := fun w hw => h2.memT hc2 hp2 hw
  refine WP.spec_bind (WP.spec_and (sched.dequeue.inv s2 t Q R h2 ht)
    (sched.dequeue.foot s2 t _ hT ht hp2 (h2.nodes _ hc2) (h2.nodes _ h2.cur) ((h2.ready _ hc2).1.rel _ hp2)
      (h2.queued t ht).1)) ?_
  rintro s3 ⟨h3, hw3, -⟩
  have a3 := qfoot_act h2 hW2 hc2 ht (by omega) hw3
  have f3 : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      (K.val ≠ 3480 ∧ K.val ≠ 3488 ∧ K.val ≠ 3496 ∧ K.val ≠ 3504) → K.val ≠ 3592 →
      L.mem s3 (core.num.U64.wrapping_add t K) = L.mem s2 (core.num.U64.wrapping_add t K) :=
    fun K a b c d => field_qfoot hT hW2 (h2.nodes _ hc2) (h2.nodes _ h2.cur) ht hw3 ht a b c (fun _ => d)
  set Q3 := (if (L.mem s2 (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64
       then Function.update Q (L.mem s2 (affA t)) (Function.update (Q (L.mem s2 (affA t))) (L.mem s2 (prioA t))
         ((Q (L.mem s2 (affA t)) (L.mem s2 (prioA t))).erase t)) else Q) with hQ3
  have nQ3 : ∀ c ∈ Cs, ∀ p : U64, p.val < 256 → t ∉ Q3 c p := by
    intro c hc p hp hm
    rw [hQ3] at hm
    split_ifs at hm with hf
    · rcases mem_upd2.1 hm with ⟨-, -, hm⟩ | ⟨hne, hm⟩
      · exact ((h2.ready _ hc2).1.rel _ hp2).nodup.not_mem_erase hm
      · obtain ⟨e1, e2⟩ := h2.inQ c hc p hp t hm
        exact hne ⟨e1.symm, e2.symm⟩
    · exact h2.notQ ht (not_not.1 hf) hc hp hm
  -- out of the release queue
  have hc3 := h3.aff t ht
  have hW3 : ∀ w ∈ R (L.mem s3 (affA t)), w ∈ T := fun w hw => h3.memTR hc3 hw
  refine WP.spec_bind (WP.spec_and (sched.release_remove.inv s3 t Q3 R h3 ht)
    (sched.release_remove.foot s3 t _ hT ht (h3.nodes _ hc3) (h3.nodes _ h3.cur) (h3.release _ hc3)
      (h3.released t ht).1)) ?_
  rintro s4 ⟨h4, hw4, -⟩
  have a4 := qfoot_act h3 hW3 hc3 ht (by unfold RelOffs; omega) hw4
  have f4 : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      (K.val ≠ 3480 ∧ K.val ≠ 3488 ∧ K.val ≠ 3496 ∧ K.val ≠ 3504) → K.val ≠ 3592 →
      L.mem s4 (core.num.U64.wrapping_add t K) = L.mem s3 (core.num.U64.wrapping_add t K) :=
    fun K a b c d => field_qfoot hT hW3 (h3.nodes _ hc3) (h3.nodes _ h3.cur) ht hw4 ht a b c (fun _ => d)
  set R4 := (if (L.mem s3 (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64
       then Function.update R (L.mem s3 (affA t)) ((R (L.mem s3 (affA t))).erase t) else R) with hR4
  have nR4 : ∀ c ∈ Cs, t ∉ R4 c := by
    intro c hc hm
    rw [hR4] at hm
    split_ifs at hm with hf
    · by_cases e : c = L.mem s3 (affA t)
      · subst e; rw [Function.update_self] at hm
        exact (h3.release _ hc3).nodup.not_mem_erase hm
      · rw [Function.update_of_ne e] at hm
        exact e (h3.inR c hc t hm).symm
    · exact h3.notR ht (not_not.1 hf) hc hm
  have st4 : L.mem s4 (stA t) = L.mem s2 (stA t) := by
    rw [stA_eq, f4 _ (by simp) (by simp) (by simp) (by simp), f3 _ (by simp) (by simp) (by simp) (by simp)]
  have y4 : L.mem s4 (yieldA t) = L.mem s (yieldA t) := by
    rw [← y2]; exact (f4 _ (by simp) (by simp) (by simp) (by simp)).trans (f3 _ (by simp) (by simp) (by simp) (by simp))
  have na4 : L.actionW s4 ≠ t := by rw [a4, a3]; exact na2
  -- `cancel_yield_to`
  unfold schedcontext.cancel_yield_to
  step with obj.Tcb.is_null.spec as ⟨b, b_post⟩
  have hb0 : b = false := by
    rw [b_post]; simp only [decide_eq_false_iff_not]; intro e; exact hta.ne0 (by rw [e]; rfl)
  subst hb0
  simp only [Bool.false_eq_true, ↓reduceIte]
  step with obj.Tcb.yield_to.spec as ⟨yt, yt_post⟩
  refine WP.spec_bind (Pₘ := fun s5 => SchedQueuesInv st T Cs Ω s5 Q3 R4 ∧ L.mem s5 (stA t) = L.mem s4 (stA t) ∧
      L.actionW s5 = L.actionW s4) ?_ ?_
  · split
    · rename_i hy
      have hyΩ : scYieldFromA yt ∈ Ω := by rw [yt_post, y4]; exact hyield (by rw [← y4, ← yt_post]; simpa using hy)
      step with obj.Sc.set_yield_from.spec as ⟨s5, s5_post⟩
      subst s5_post
      obtain ⟨h5, e5⟩ := wr_omega (v := 0#u64) h4 hyΩ
      have a5 : L.actionW (L.wr s4 (scYieldFromA yt) 0#u64) = L.actionW s4 := by
        unfold LawfulStore.actionW
        simp only [LawfulStore.cpu_wr, nodeAt_wr]
        exact L.mem_wr_ne (h4.omega _ hyΩ).1 (nodeAt_aligned (h4.nodes _ h4.cur) (by rw [act_val]; omega)
          (by rw [act_val])) (fun e => out_ne_node (h4.omega _ hyΩ) h4.cur (h4.nodes _ h4.cur)
            (by rw [act_val]; omega) e.symm)
      refine WP.spec_mono (obj.Tcb.set_yield_to.spec _ t 0#u64) fun s6 e => ?_
      subst e
      obtain ⟨h6, f6, a6⟩ := field_wr_keep (K := 3472#u64) (v := 0#u64) h5 ht (by simp) (by simp) (by simp)
      refine ⟨h6, ?_, a6.trans a5⟩
      rw [stA_eq, show yieldA t = core.num.U64.wrapping_add t 3472#u64 from rfl,
        f6 _ (by simp) (by simp) (by simp), ← stA_eq, e5 t ht]
    · exact (WP.spec_ok _).2 ⟨h4, rfl, rfl⟩
  rintro s5 ⟨h5, st5, a5⟩
  have hnr5 : ¬ Blocked (L.mem s5 (stA t)) := by rw [st5, st4]; exact nb2
  refine WP.spec_bind (sched.set_thread_state.inv s5 t _ Q3 R4 h5 ht not_blocked_inactive (Or.inr hnr5)
    ⟨fun c hc p hp hm => absurd hm (nQ3 c hc p hp), fun c hc hm => absurd hm (nR4 c hc),
     fun e => absurd e (by rw [a5]; exact na4)⟩) ?_
  intro s6 h6
  simp only [WP.spec_ok, WP.uncurry'_pair]
  exact ⟨Q3, R4, h6.congrX empty_congr⟩

end

end Fl4Proofs.P1

