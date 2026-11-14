/-
P1: the object-specific work of `finalise_cap` keeps the invariants (`BlkOK`,
which includes the timer-tree typing) and has a `KW` footprint, so it keeps
every cap slot.
-/
import Fl4Proofs.P1.QueueTimerSet
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}

theorem restart_ne : sched.TS_RESTART ≠ sched.TS_BLOCKED_ON_REPLY ∧ sched.TS_RESTART ≠ sched.TS_BLOCKED_ON_RECV :=
  ⟨runnable_ne_reply runnable_restart, runnable_ne_recv runnable_restart⟩

/-- The head of a nonempty queue and the next link. -/
theorem QueueRel.head_next {m : U64 → U64} {l : tcbqueue.Link} {q : tcbqueue.Queue} {t : U64} {ys : List U64}
    (h : QueueRel m T l q (t :: ys)) : m (nextA l t) = ys.headD 0#u64 := by
  have := h.seg; simp only [Seg_cons] at this; exact this.2.1

/-! ## `cancel_all_signals` -/

/-- One round of `cancel_all_signals`: the waiter at the head of `n`'s queue
is dequeued, restarted, unblocked and offered to the scheduler. -/
theorem cas_round {β : Type _} (s : S) (n t : U64) (fuel1 : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z s)
    (hH : H n = some .ntfn) (hst : L.epState s n = 1#u64) (hhd : (L.epQ s n).head = t) :
    (do
      let next ← tcbqueue.next_of st s .Ep t
      let s1 ← notification.ntfn_dequeue st s n t
      let s2 ← sched.set_thread_state st s1 t sched.TS_RESTART
      let s3 ← notification.unblock_sporadic st s2 t
      let s4 ← sched.possible_switch_to st s3 t
      ok (ControlFlow.cont (β := β) (s4, next, fuel1))) ⦃ r => ∃ s4 next, r = .cont (s4, next, fuel1) ∧
        BlkOK st T Cs Ω H Sg Rp Scs Nt Z s4 ∧ Foot st T Cs Sg Scs Z {n} s s4 ∧
        (next ≠ 0#u64 → L.epState s4 n = 1#u64 ∧ (L.epQ s4 n).head = next) ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hT := h0.tcbs
  obtain ⟨hdT, hbe, hds⟩ := ntfn_head h0 hH hst
  rw [hhd] at hdT hbe hds
  have hta := hT t hdT
  obtain ⟨E, EQ, hEW⟩ := h0.eps
  have heE : n ∈ E := (hEW.2.2.2.2.2.2.2.1 n).2 (Or.inr hH)
  obtain ⟨hE, -, hq⟩ := hEW.1 n heE
  have hne : EQ n ≠ [] := fun h0' => ((hEW.2.2.2.2.2.2.2.2.2.2 n heE h0').2 hH) hst
  obtain ⟨y, ys, hys⟩ := List.exists_cons_of_ne_nil hne
  have hy : y = t := by rw [← hhd, hq.head, hys]; rfl
  subst hy
  rw [hys] at hq
  have hnext := hq.head_next
  have hbl : Blocked (L.mem s (stA y)) := by rw [hds]; exact Or.inr (Or.inr rfl)
  obtain ⟨dq, dr, da⟩ := blocked_out h0 hdT (not_runnable_of_blocked hbl)
  unfold tcbqueue.next_of
  step with tcbqueue.next.spec as ⟨next, enext⟩
  have hdq := notification.ntfn_dequeue.inv s y Q R h0 hdT (by simp) hbl
  rw [hbe] at hdq
  refine WP.spec_bind (WP.spec_and hdq (WP.spec_and (notification.ntfn_dequeue.rel s n y _ hT hE hq
    List.mem_cons_self) (notification.ntfn_dequeue.foot s n y _ hT hE hq List.mem_cons_self))) ?_
  rintro s1 ⟨⟨h1, f1, o1, n1, k1, c1, nc1⟩, ⟨hq1, hst1⟩, w1⟩
  have hnd := hq.nodup
  have herase : (y :: ys).erase y = ys := List.erase_cons_head y ys
  rw [herase] at hq1 hst1
  have tm1 : TmFr st T Cs Nt s s1 := ⟨k1, fun y hy K a b c => f1 y hy K (by omega) c (by omega) (by omega),
    fun c hc o ho => nc1 c hc o (by omega) (by omega), fun n' hn' => o1 _ (hSg.sub _ (hX.1.ntB n' hn').2)⟩
  obtain ⟨hB1, hX1, hS1, hSg1, ea1, ec1, ei1⟩ := frame_bx h0 hB hX hS hSg f1 o1 n1 k1 tm1
  have st1 : L.mem s1 (stA y) = sched.TS_BLOCKED_ON_NTFN := by
    rw [stA_eq, f1 y hdT _ (by simp) (by simp) (by simp) (by simp), ← stA_eq]; exact hds
  have iq1 : L.mem s1 (inqA y) = L.mem s (inqA y) := by
    rw [inqA_eq]; exact f1 y hdT _ (by simp) (by simp) (by simp) (by simp)
  have fw1 : Foot st T Cs Sg Scs Z {n} s s1 := Foot.of w1 fun b hb => hb.kw hq.mem rfl
  obtain ⟨-, -, r3, -, r6⟩ := ts_vals
  refine WP.spec_bind (WP.spec_and (sts_all s1 y _ Q R h1 hB1 hX1 hS1 hSg1 hdT not_blocked_restart restart_ne
    (Or.inl (Or.inr rfl)) (hX1.noref hta (by rw [st1]; exact blocked_ne_reply (Or.inr (Or.inr rfl)))
      (by rw [st1, r3, r6]; decide))
    ⟨fun _ _ _ _ _ => runnable_restart, fun _ _ _ => runnable_restart, fun _ => runnable_restart⟩)
    (sched.set_thread_state.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) s1 y _ h1 hdT)) ?_
  rintro s2 ⟨⟨h2, hB2, hX2, hS2, hSg2, st2, k2⟩, fw2⟩
  have h2' : SchedQueuesInv st T Cs Ω H s2 Q R := h2.congrX empty_congr'
  refine WP.spec_bind (WP.spec_and (endpoint.unblock_sporadic.all s2 y h2' hB2 hX2 hS2 hSg2 hdT)
    (notification.unblock_sporadic.kw (Es := ∅) s2 y h2' hX2 hS2 hdT)) ?_
  rintro s3 ⟨⟨h3, hB3, hX3, hS3, hSg3, -, -, -, fk3, -⟩, fw3⟩
  have st3 : L.mem s3 (stA y) = sched.TS_RESTART := by
    rw [stA_eq, fk3 y hdT _ (by simp) (by simp), ← stA_eq]; exact st2
  refine WP.spec_bind (WP.spec_and (sched.possible_switch_to.sch (Sg := Sg) s3 y Q R h3 hB3 hSg3 hdT
    (by rw [st3]; exact runnable_restart))
    (sched.possible_switch_to.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) s3 y h3 hdT)) ?_
  rintro s4 ⟨⟨p4, -, -⟩, fw4⟩
  have f14 : Foot st T Cs Sg Scs Z ∅ s1 s4 := fw2.trans (fw3.trans fw4)
  obtain ⟨eh, et⟩ := f14.epQ h1 hX1.1 hSg1.sub (Or.inr hH)
  refine (WP.spec_ok _).2 ⟨s4, next, rfl, ⟨p4.inv, p4.bnd, hX3.fr p4.fr, hS3.fr p4.fr, hSg3.fr p4.fr⟩,
    fw1.trans (f14.mono (Set.empty_subset _)), fun hn0 => ?_⟩
  have hys0 : ys ≠ [] := fun e => hn0 (by rw [enext, hnext, e]; rfl)
  have es : L.epState s4 n = L.epState s1 n := by simp only [LawfulStore.epState, et]
  refine ⟨by rw [es, hst1, if_neg hys0, hst], ?_⟩
  rw [show (L.epQ s4 n).head = L.mem s4 (epHeadA n) from rfl, eh, show L.mem s1 (epHeadA n) = (L.epQ s1 n).head
    from rfl, hq1.head, enext, hnext]


/-- `reschedule_required` keeps `BlkOK`. -/
theorem sched.reschedule_required.blk (s : S) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z s) :
    sched.reschedule_required st s ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z s' ∧ Foot st T Cs Sg Scs Z ∅ s s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  refine WP.spec_mono (WP.spec_and (sched.reschedule_required.schX (Sg := Sg) s Q R h0 hB hSg)
    (sched.reschedule_required.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) s h0)) ?_
  rintro s' ⟨⟨⟨Q', R', h'⟩, hB', f, -⟩, fw⟩
  exact ⟨⟨⟨Q', R', h'⟩, hB', hX.fr f, hS.fr f, hSg.fr f⟩, fw⟩

theorem notification.cancel_all_signals_loop.blk (s0 s : S) (n t fuel : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z s)
    (hH : H n = some .ntfn) (hf : Foot st T Cs Sg Scs Z {n} s0 s)
    (ht : t ≠ 0#u64 → L.epState s n = 1#u64 ∧ (L.epQ s n).head = t) :
    notification.cancel_all_signals_loop st s n t fuel ⦃ s' =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z s' ∧ Foot st T Cs Sg Scs Z {n} s0 s' ⦄ := by
  unfold notification.cancel_all_signals_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.2.val)
    (inv := fun x => BlkOK st T Cs Ω H Sg Rp Scs Nt Z x.1 ∧ Foot st T Cs Sg Scs Z {n} s0 x.1 ∧
      (x.2.1 ≠ 0#u64 → L.epState x.1 n = 1#u64 ∧ (L.epQ x.1 n).head = x.2.1))
  · rintro ⟨s1, t1, f1⟩ ⟨hb1, hf1, ht1⟩
    simp only at hb1 hf1 ht1
    unfold notification.cancel_all_signals_loop.body
    step with obj.Tcb.is_null.spec as ⟨b, eb⟩
    split
    · exact (WP.spec_ok _).2 ⟨hb1, hf1⟩
    rename_i hb
    have ht0 : t1 ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    obtain ⟨hst1, hhd1⟩ := ht1 ht0
    split
    · rename_i hfuel
      step as ⟨fuel1, efuel⟩
      refine WP.spec_mono (cas_round (β := S) s1 n t1 fuel1 hb1 hH hst1 hhd1) ?_
      rintro r ⟨s4, next, rfl, hb4, hf4, hn4⟩
      exact ⟨hb4, hf1.trans hf4, hn4, by simp only; omega⟩
    · exact (WP.spec_ok _).2 ⟨hb1, hf1⟩
  · exact ⟨h, hf, ht⟩

/-- seL4 `cancelAllSignals`: every waiter is restarted. -/
theorem notification.cancel_all_signals.blk (s : S) (n : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z s)
    (hH : H n = some .ntfn) :
    notification.cancel_all_signals st s n ⦃ s' =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z s' ∧ Foot st T Cs Sg Scs Z {n} s s' ⦄ := by
  unfold notification.cancel_all_signals
  step with obj.Ntfn.state.spec as ⟨v, hv⟩
  split
  · exact (WP.spec_ok _).2 ⟨h, Foot.refl _⟩
  rename_i hw
  have hst : L.epState s n = 1#u64 := by
    rw [← hv]; have := hw; simp [obj.NTFN_WAITING] at this; exact UScalar.eq_of_val_eq (by simpa using this)
  step with notification.get_queue.spec as ⟨q, eq⟩
  subst eq
  refine WP.spec_bind (notification.cancel_all_signals_loop.blk s s n _ _ h hH (Foot.refl _)
    (fun _ => ⟨hst, rfl⟩)) ?_
  rintro s1 ⟨h1, f1⟩
  exact WP.spec_mono (sched.reschedule_required.blk s1 h1) fun s2 ⟨h2, f2⟩ =>
    ⟨h2, f1.trans (f2.mono (Set.empty_subset _))⟩



/-! ## `cancel_all_ipc` -/

/-- `restart_thread_if_no_fault` on a thread in no scheduler queue, the
switch-to candidate of no core, and named by no reply object. -/
theorem endpoint.restart_thread_if_no_fault.blk {X : Set U64} (s : S) (t : obj.Tcb) {Q : U64 → U64 → List U64}
    {R : U64 → List U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hXt : ∀ y ∈ X, y = t)
    (hB : BoundInv st T s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hS : SCsOK st T Ω Sg Scs Z s)
    (hSg : SgOK st Ω Sg s) (ht : t ∈ T) (hx : t ∈ X ∨ ¬ Blocked (L.mem s (stA t)))
    (hnoref : ∀ r ∈ Rp, L.mem s (rTcbA r) ≠ t)
    (hnQ : ∀ c ∈ Cs, ∀ p : U64, p.val < 256 → t ∉ Q c p) (hnR : ∀ c ∈ Cs, t ∉ R c) (hna : L.actionW s ≠ t) :
    endpoint.restart_thread_if_no_fault st s t ⦃ s' =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z s' ∧ Foot st T Cs Sg Scs Z ∅ s s' ⦄ := by
  have hq : ∀ v : U64, (∀ c ∈ Cs, ∀ p : U64, p.val < 256 → t ∈ Q c p → Runnable v) ∧
      (∀ c ∈ Cs, t ∈ R c → Runnable v) ∧ (L.actionW s = t → Runnable v) := fun v =>
    ⟨fun c hc p hp htq => absurd htq (hnQ c hc p hp), fun c hc htr => absurd htr (hnR c hc),
      fun e => absurd e hna⟩
  have cg : ∀ y, y ∈ {y : U64 | y ∈ X ∧ y ≠ t} ↔ y ∈ (∅ : Set U64) := fun y => by
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_not]; exact hXt y
  unfold endpoint.restart_thread_if_no_fault
  step with obj.Tcb.fault_type.any as ⟨i, _hi⟩
  split
  · refine WP.spec_bind (WP.spec_and (sts_all s t _ Q R h hB hX hS hSg ht not_blocked_restart restart_ne hx hnoref
      (hq _)) (sched.set_thread_state.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) s t _ h ht)) ?_
    rintro s1 ⟨⟨h1, hB1, hX1, hS1, hSg1, st1, -⟩, fw1⟩
    have h1' : SchedQueuesInv st T Cs Ω H s1 Q R := h1.congrX cg
    refine WP.spec_bind (WP.spec_and (endpoint.unblock_sporadic.all s1 t h1' hB1 hX1 hS1 hSg1 ht)
      (endpoint.unblock_sporadic.kw (Es := ∅) s1 t h1' hX1 hS1 ht)) ?_
    rintro s2 ⟨⟨h2, hB2, hX2, hS2, hSg2, -, -, -, fk2, -⟩, fw2⟩
    have st2 : L.mem s2 (stA t) = sched.TS_RESTART := by
      rw [stA_eq, fk2 t ht _ (by simp) (by simp), ← stA_eq]; exact st1
    refine WP.spec_mono (WP.spec_and (sched.possible_switch_to.sch (Sg := Sg) s2 t Q R h2 hB2 hSg2 ht
      (by rw [st2]; exact runnable_restart))
      (sched.possible_switch_to.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) s2 t h2 ht)) ?_
    rintro s3 ⟨⟨p3, -, -⟩, fw3⟩
    exact ⟨⟨p3.inv, p3.bnd, hX2.fr p3.fr, hS2.fr p3.fr, hSg2.fr p3.fr⟩, fw1.trans (fw2.trans fw3)⟩
  · refine WP.spec_mono (WP.spec_and (sts_all s t _ Q R h hB hX hS hSg ht not_blocked_inactive inactive_ne hx hnoref
      (hq _)) (sched.set_thread_state.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) s t _ h ht)) ?_
    rintro s1 ⟨⟨h1, hB1, hX1, hS1, hSg1, -, -⟩, fw1⟩
    exact ⟨⟨⟨Q, R, h1.congrX cg⟩, hB1, hX1, hS1, hSg1⟩, fw1⟩



/-- A non-idle endpoint is in the send or the receive state. -/
theorem ep_state12 {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {e : U64}
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hH : H e = some .ep) (hst : L.epState s e ≠ 0#u64) :
    L.epState s e = 1#u64 ∨ L.epState s e = 2#u64 := by
  obtain ⟨E, EQ, hEW⟩ := h.eps
  have he : e ∈ E := (hEW.2.2.2.2.2.2.2.1 e).2 (Or.inl hH)
  obtain ⟨k1, k2, -, -, k4, k5⟩ := hEW.2.2.2.2.2
  have hne : EQ e ≠ [] := fun h0 => hst ((k5 e he h0).1 hH)
  obtain ⟨y, ys, hys⟩ := List.exists_cons_of_ne_nil hne
  have hy : y ∈ EQ e := by rw [hys]; exact List.mem_cons_self
  obtain ⟨hE, -, hq⟩ := hEW.1 e he
  obtain ⟨-, hbe, hbl⟩ := hEW.2.2.2.1 e he y hy
  have hyT := hq.mem y hy
  obtain ⟨c1, c2, -⟩ := k4 e he y hy
  rcases hbl with hb | hb | hb
  · exact Or.inl (c1 hb)
  · exact Or.inr (c2 hb)
  · have := k2 y hyT (by simp) hb; rw [hbe, hH] at this; cases this

/-- One round of `cancel_all_ipc`: the waiter at the head of `ep`'s queue is
dequeued, its reply unlinked (if receiving) and restarted. -/
theorem cai_round {β : Type _} (s : S) (ep t : U64) (fuel1 : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z s)
    (hH : H ep = some .ep) (hst : L.epState s ep = 1#u64 ∨ L.epState s ep = 2#u64) (hhd : (L.epQ s ep).head = t) :
    (do
      let next ← tcbqueue.next_of st s .Ep t
      let s1 ← endpoint.ep_dequeue st s ep t
      let i ← obj.Tcb.state st t s1
      let s2 ← if i = sched.TS_BLOCKED_ON_RECV then do
          let i1 ← obj.Tcb.reply_obj st t s1
          if (i1 != 0#u64) = true then ipc.reply_unlink st s1 i1 t else ok s1
        else ok s1
      let s3 ← endpoint.restart_thread_if_no_fault st s2 t
      ok (ControlFlow.cont (β := β) (s3, next, fuel1))) ⦃ r => ∃ s3 next, r = .cont (s3, next, fuel1) ∧
        BlkOK st T Cs Ω H Sg Rp Scs Nt Z s3 ∧ Foot st T Cs Sg Scs Z {ep} s s3 ∧
        (next ≠ 0#u64 → (L.epState s3 ep = 1#u64 ∨ L.epState s3 ep = 2#u64) ∧ (L.epQ s3 ep).head = next) ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hT := h0.tcbs
  obtain ⟨hdT, hbe, hs1, hs2⟩ := ep_head h0 hH (w := L.epState s ep) hst rfl
  rw [hhd] at hdT hbe hs1 hs2
  have hta := hT t hdT
  obtain ⟨-, -, r3, r4, -⟩ := ts_vals
  have hsr : L.mem s (stA t) = sched.TS_BLOCKED_ON_SEND ∨ L.mem s (stA t) = sched.TS_BLOCKED_ON_RECV := by
    rcases hst with e | e
    · exact Or.inl (hs1 e)
    · exact Or.inr (hs2 e)
  have hbl : Blocked (L.mem s (stA t)) := by
    rcases hsr with e | e
    · rw [e]; exact Or.inl rfl
    · rw [e]; exact Or.inr (Or.inl rfl)
  have hnrun := not_runnable_of_blocked hbl
  obtain ⟨-, -, da⟩ := blocked_out h0 hdT hnrun
  have hnQ : ∀ c ∈ Cs, ∀ p : U64, p.val < 256 → t ∉ Q c p := fun c hc p hp htq => hnrun (h0.runQ c hc p hp t htq)
  have hnR : ∀ c ∈ Cs, t ∉ R c := fun c hc htr => hnrun (h0.runR c hc t htr)
  obtain ⟨E, EQ, hEW⟩ := h0.eps
  have heE : ep ∈ E := (hEW.2.2.2.2.2.2.2.1 ep).2 (Or.inl hH)
  obtain ⟨hE, -, hq⟩ := hEW.1 ep heE
  have hne : EQ ep ≠ [] := fun h0' => by
    have := (hEW.2.2.2.2.2.2.2.2.2.2 ep heE h0').1 hH
    rcases hst with e | e <;> rw [e] at this <;> exact absurd this (by decide)
  obtain ⟨y, ys, hys⟩ := List.exists_cons_of_ne_nil hne
  have hy : y = t := by rw [← hhd, hq.head, hys]; rfl
  subst hy
  rw [hys] at hq
  have hnext := hq.head_next
  unfold tcbqueue.next_of
  step with tcbqueue.next.spec as ⟨next, enext⟩
  have hdq := endpoint.ep_dequeue.inv s y Q R h0 hdT (by simp) hbl
  rw [hbe] at hdq
  refine WP.spec_bind (WP.spec_and hdq (WP.spec_and (endpoint.ep_dequeue.rel s ep y _ hT hE hq
    List.mem_cons_self) (endpoint.ep_dequeue.foot s ep y _ hT hE hq List.mem_cons_self))) ?_
  rintro s1 ⟨⟨h1, f1, o1, n1, k1, c1, nc1⟩, ⟨hq1, hst1⟩, w1⟩
  have herase : (y :: ys).erase y = ys := List.erase_cons_head y ys
  rw [herase] at hq1 hst1
  have tm1 : TmFr st T Cs Nt s s1 := ⟨k1, fun y hy K a b c => f1 y hy K (by omega) c (by omega) (by omega),
    fun c hc o ho => nc1 c hc o (by omega) (by omega), fun n' hn' => o1 _ (hSg.sub _ (hX.1.ntB n' hn').2)⟩
  obtain ⟨hB1, hX1, hS1, hSg1, ea1, ec1, ei1⟩ := frame_bx h0 hB hX hS hSg f1 o1 n1 k1 tm1
  have st1 : L.mem s1 (stA y) = L.mem s (stA y) := by
    rw [stA_eq]; exact f1 y hdT _ (by simp) (by simp) (by simp) (by simp)
  have rp1 : L.mem s1 (replyA y) = L.mem s (replyA y) := f1 y hdT _ (by simp) (by simp) (by simp) (by simp)
  have fw1 : Foot st T Cs Sg Scs Z {ep} s s1 := Foot.of w1 fun b hb => hb.kw hq.mem rfl
  have da1 : L.actionW s1 ≠ y := by rw [ea1]; exact da
  -- the rest of the round, from a state `s2` with a `KW ∅` footprint from `s1`
  have tail : ∀ (s2 : S), Foot st T Cs Sg Scs Z ∅ s1 s2 →
      endpoint.restart_thread_if_no_fault st s2 y ⦃ s' =>
        BlkOK st T Cs Ω H Sg Rp Scs Nt Z s' ∧ Foot st T Cs Sg Scs Z ∅ s2 s' ⦄ →
      (do
        let s3 ← endpoint.restart_thread_if_no_fault st s2 y
        ok (ControlFlow.cont (β := β) (s3, next, fuel1))) ⦃ r => ∃ s3 next', r = .cont (s3, next', fuel1) ∧
          BlkOK st T Cs Ω H Sg Rp Scs Nt Z s3 ∧ Foot st T Cs Sg Scs Z {ep} s s3 ∧
          (next' ≠ 0#u64 → (L.epState s3 ep = 1#u64 ∨ L.epState s3 ep = 2#u64) ∧ (L.epQ s3 ep).head = next') ⦄ := by
    intro s2 fw2 hr
    refine WP.spec_bind hr fun s3 ⟨hb3, fw3⟩ => ?_
    have f13 : Foot st T Cs Sg Scs Z ∅ s1 s3 := fw2.trans fw3
    obtain ⟨eh, et⟩ := f13.epQ h1 hX1.1 hSg1.sub (Or.inl hH)
    refine (WP.spec_ok _).2 ⟨s3, next, rfl, hb3, fw1.trans (f13.mono (Set.empty_subset _)), fun hn0 => ?_⟩
    have hys0 : ys ≠ [] := fun e => hn0 (by rw [enext, hnext, e]; rfl)
    have es : L.epState s3 ep = L.epState s1 ep := by simp only [LawfulStore.epState, et]
    refine ⟨by rw [es, hst1, if_neg hys0]; exact hst, ?_⟩
    rw [show (L.epQ s3 ep).head = L.mem s3 (epHeadA ep) from rfl, eh,
      show L.mem s1 (epHeadA ep) = (L.epQ s1 ep).head from rfl, hq1.head, enext, hnext]
  have cg1 : ∀ z ∈ {z : U64 | z ∈ (∅ : Set U64) ∨ z = y}, z = y := fun z hz => by simpa using hz
  step with obj.Tcb.state.spec as ⟨i, ei⟩
  split
  · rename_i hrecv
    step with obj.Tcb.reply_obj.spec as ⟨i1, ei1⟩
    split
    · rename_i hi1
      have hi10 : i1 ≠ 0#u64 := by simpa using hi1
      have hsr1 : L.mem s1 (stA y) = sched.TS_BLOCKED_ON_RECV := by rw [← ei, hrecv]
      obtain ⟨hr, hrt⟩ := hX1.2.1.recv y hdT hsr1 (by rw [← ei1]; exact hi10)
      rw [← ei1] at hr hrt
      refine WP.spec_bind (WP.spec_and (ipc.reply_unlink.inv s1 i1 y Q R h1 hdT hX1.1 hSg1.sub hr hrt
        (by rw [st1]; exact hnrun) (Or.inl (Or.inr rfl)))
        (ipc.reply_unlink.kw (Scs := Scs) (Es := ∅) s1 i1 y h1 hX1 hSg1.sub hr hdT)) ?_
      rintro s2 ⟨⟨h2, e2, k2, z2⟩, fw2⟩
      have hB2 := hB1.keepT h1 k2 (by rw [e2]; exact not_blocked_inactive)
      have hclr : ∀ r ∈ Rp, L.mem s1 (rTcbA r) = y → L.mem s2 (rTcbA r) = 0#u64 := by
        intro r hr' e
        obtain ⟨-, -, b2, -⟩ := hX1.2.1.back r hr' (by rw [e]; exact fun e0 => hta.ne0 (by rw [e0]; rfl))
        rw [e, ← ei1] at b2
        rw [← b2]; exact z2
      have hX2 := hX1.keepT k2 (by rw [e2]; exact inactive_ne) hclr
      have hS2 := hS1.keepT hX1 k2
      have hSg2 : SgOK st Ω Sg s2 := ⟨hSg1.sub, fun b hb => by rw [k2.ksb]; exact hSg1.ks b hb,
        fun o h1' h2' => by rw [k2.ksb]; exact hSg1.ksΩ o h1' h2'⟩
      have da2 : L.actionW s2 ≠ y := by
        rcases k2.act with e | e
        · rw [e]; exact da1
        · rw [e]; exact fun e' => notT_small hT (by simp) (e' ▸ hdT)
      refine tail s2 fw2 (endpoint.restart_thread_if_no_fault.blk s2 y h2 (fun z hz => ?_) hB2 hX2 hS2 hSg2 hdT
        (Or.inr (by rw [e2]; exact not_blocked_inactive))
        (hX2.noref hta (by rw [e2]; exact inactive_ne.1) (by rw [e2]; exact inactive_ne.2)) hnQ hnR da2)
      obtain ⟨hz1, hz2⟩ := hz
      exact absurd (cg1 z hz1) hz2
    · rename_i hi1
      have hz : i1 = 0#u64 := by apply UScalar.eq_of_val_eq; simpa using hi1
      have hi10 : L.mem s1 (replyA y) = 0#u64 := by rw [← ei1]; exact hz
      simp only [Aeneas.Std.bind_ok]
      exact tail s1 (Foot.refl _) (endpoint.restart_thread_if_no_fault.blk s1 y h1 cg1 hB1 hX1 hS1 hSg1 hdT
        (Or.inl (Or.inr rfl)) (hX1.noref0 hta hi10) hnQ hnR da1)
  · rename_i hnrecv
    have hsend : L.mem s1 (stA y) = sched.TS_BLOCKED_ON_SEND := by
      rcases hsr with e | e
      · rw [st1, e]
      · exact absurd (by rw [ei, st1, e]) hnrecv
    have nrp : sched.TS_BLOCKED_ON_SEND ≠ sched.TS_BLOCKED_ON_REPLY := by
      rw [r4]; unfold sched.TS_BLOCKED_ON_REPLY; decide
    have nrc : sched.TS_BLOCKED_ON_SEND ≠ sched.TS_BLOCKED_ON_RECV := by rw [r4, r3]; decide
    simp only [Aeneas.Std.bind_ok]
    exact tail s1 (Foot.refl _) (endpoint.restart_thread_if_no_fault.blk s1 y h1 cg1 hB1 hX1 hS1 hSg1 hdT
      (Or.inl (Or.inr rfl)) (hX1.noref hta (by rw [hsend]; exact nrp) (by rw [hsend]; exact nrc)) hnQ hnR da1)


theorem endpoint.cancel_all_ipc_loop.blk (s0 s : S) (ep t fuel : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z s)
    (hH : H ep = some .ep) (hf : Foot st T Cs Sg Scs Z {ep} s0 s)
    (ht : t ≠ 0#u64 → (L.epState s ep = 1#u64 ∨ L.epState s ep = 2#u64) ∧ (L.epQ s ep).head = t) :
    endpoint.cancel_all_ipc_loop st s ep t fuel ⦃ s' =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z s' ∧ Foot st T Cs Sg Scs Z {ep} s0 s' ⦄ := by
  unfold endpoint.cancel_all_ipc_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.2.val)
    (inv := fun x => BlkOK st T Cs Ω H Sg Rp Scs Nt Z x.1 ∧ Foot st T Cs Sg Scs Z {ep} s0 x.1 ∧
      (x.2.1 ≠ 0#u64 → (L.epState x.1 ep = 1#u64 ∨ L.epState x.1 ep = 2#u64) ∧ (L.epQ x.1 ep).head = x.2.1))
  · rintro ⟨s1, t1, f1⟩ ⟨hb1, hf1, ht1⟩
    simp only at hb1 hf1 ht1
    unfold endpoint.cancel_all_ipc_loop.body
    step with obj.Tcb.is_null.spec as ⟨b, eb⟩
    split
    · exact (WP.spec_ok _).2 ⟨hb1, hf1⟩
    rename_i hb
    have ht0 : t1 ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    obtain ⟨hst1, hhd1⟩ := ht1 ht0
    split
    · rename_i hfuel
      step as ⟨fuel1, efuel⟩
      refine WP.spec_mono (cai_round (β := S) s1 ep t1 fuel1 hb1 hH hst1 hhd1) ?_
      rintro r ⟨s4, next, rfl, hb4, hf4, hn4⟩
      exact ⟨hb4, hf1.trans hf4, hn4, by simp only; omega⟩
    · exact (WP.spec_ok _).2 ⟨hb1, hf1⟩
  · exact ⟨h, hf, ht⟩

/-- seL4 `cancelAllIPC`: every waiter is restarted (or made inactive, if it
has a fault). -/
theorem endpoint.cancel_all_ipc.blk (s : S) (ep : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z s)
    (hH : H ep = some .ep) :
    endpoint.cancel_all_ipc st s ep ⦃ s' =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z s' ∧ Foot st T Cs Sg Scs Z {ep} s s' ⦄ := by
  unfold endpoint.cancel_all_ipc
  step with obj.Ep.state.spec as ⟨v, hv⟩
  split
  · exact (WP.spec_ok _).2 ⟨h, Foot.refl _⟩
  rename_i hidle
  have hst : L.epState s ep ≠ 0#u64 := by
    rw [← hv]; intro e; exact hidle (by rw [e]; unfold obj.EP_IDLE; rfl)
  step with endpoint.get_queue.spec as ⟨q, eq⟩
  subst eq
  have hI := h
  obtain ⟨⟨Q, R, h0⟩, -⟩ := hI
  refine WP.spec_bind (endpoint.cancel_all_ipc_loop.blk s s ep _ _ h hH (Foot.refl _)
    (fun _ => ⟨ep_state12 h0 hH hst, rfl⟩)) ?_
  rintro s1 ⟨h1, f1⟩
  exact WP.spec_mono (sched.reschedule_required.blk s1 h1) fun s2 ⟨h2, f2⟩ =>
    ⟨h2, f1.trans (f2.mono (Set.empty_subset _))⟩



/-! ## The notification–SC binding -/

theorem obj.Sc.ntfn.val (s : S) (c : obj.Sc) : obj.Sc.ntfn st c s ⦃ v => v = L.mem s (scNtfnA c) ⦄ := by
  unfold obj.Sc.ntfn; step*; simp_all [scNtfnA]
theorem obj.Sc.set_ntfn.wr (s : S) (c : obj.Sc) (v : U64) :
    obj.Sc.set_ntfn st c s v ⦃ s' => s' = L.wr s (scNtfnA c) v ⦄ := by
  unfold obj.Sc.set_ntfn; step*; simp_all [scNtfnA]
theorem obj.Ntfn.set_sc.wr (s : S) (n : obj.Ntfn) (v : U64) :
    obj.Ntfn.set_sc st n s v ⦃ s' => s' = L.wr s (ntfnScA n) v ⦄ := by
  unfold obj.Ntfn.set_sc; step*; simp_all [ntfnScA]

/-- Clearing a notification's `SC` word. -/
theorem ntsc_zero_all {s : S} {n : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z s) (hn : n ∈ Nt) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z (L.wr s (ntfnScA n) 0#u64) ∧
      Foot st T Cs Sg Scs Z ∅ s (L.wr s (ntfnScA n) 0#u64) := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hO := hX.1
  have hP := hO.ntP n hn
  have av := ntfnScA_val hP
  have hm : ntfnScA n ∈ Ω := hSg.sub _ (hO.ntW n hn)
  obtain ⟨h1, hB1, hX1, hS1, hSg1, -⟩ := link_allT (w := 0#u64) h0 hB hX hS hSg hm
    (fun r hr => by rw [av, (rp_facts hO hr).2.1]; have := hO.ntORp n hn r hr; omega)
    (fun c hc => by
      obtain ⟨h128, e1, e2, e3, e4, e5, -⟩ := sc_facts hO hc
      rw [av, e1, e2, e3, e4, e5]; have := hO.ntOSc n hn c hc; omega)
    (fun r hr e => by rw [av, (rp_facts hO hr).2.2.2] at e; have := hO.ntORp n hn r hr; omega)
    (fun r hr e => by rw [av, (rp_facts hO hr).2.2.1] at e; have := hO.ntORp n hn r hr; omega)
    (fun _ _ _ h0 => absurd rfl h0) (fun _ _ _ h0 => absurd rfl h0) (fun _ _ _ => Tz.zero)
    (fun _ _ _ h0 => absurd rfl h0)
  exact ⟨⟨⟨Q, R, h1⟩, hB1, hX1, hS1, hSg1⟩, foot_wr (h0.omega _ hm).1 (kw_sg (hO.ntW n hn))⟩

/-- Clearing an SC's `NTFN` word. -/
theorem scn_zero_all {s : S} {c : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z s) (hc : c ∈ Scs) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z (L.wr s (scNtfnA c) 0#u64) ∧
      Foot st T Cs Sg Scs Z ∅ s (L.wr s (scNtfnA c) 0#u64) := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hO := hX.1
  obtain ⟨hP, hz⟩ := hO.sc c hc
  have av := scNtfnA_val hP hz
  obtain ⟨h128, -⟩ := sc_facts hO hc
  have hm : scNtfnA c ∈ Ω := hSg.sub _ (hO.snW c hc)
  obtain ⟨h1, hB1, hX1, hS1, hSg1, -⟩ := link_allT (w := 0#u64) h0 hB hX hS hSg hm
    (fun r hr => by rw [av, (rp_facts hO hr).2.1]; have := hO.rpSc r hr c hc; omega)
    (fun c' hc' => by
      obtain ⟨h128', e1, e2, e3, e4, e5, -⟩ := sc_facts hO hc'
      rw [av, e1, e2, e3, e4, e5]
      by_cases e : c = c'
      · subst e; omega
      · have := hO.scDisj c hc c' hc' e; omega)
    (fun r hr e => by rw [av, (rp_facts hO hr).2.2.2] at e; have := hO.rpSc r hr c hc; omega)
    (fun r hr e => by rw [av, (rp_facts hO hr).2.2.1] at e; have := hO.rpSc r hr c hc; omega)
    (fun _ _ _ h0 => absurd rfl h0) (fun _ _ _ h0 => absurd rfl h0) (fun _ _ _ => Tz.zero)
    (fun _ _ _ h0 => absurd rfl h0)
  exact ⟨⟨⟨Q, R, h1⟩, hB1, hX1, hS1, hSg1⟩, foot_wr (h0.omega _ hm).1 (kw_sg (hO.snW c hc))⟩

/-- `unbind_ntfn` (seL4 `schedContext_unbindNtfn`). -/
theorem schedcontext.unbind_ntfn.blk (s : S) (c : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z s)
    (hc : c ≠ 0#u64 → c ∈ Scs) :
    schedcontext.unbind_ntfn st s c ⦃ s' =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z s' ∧ Foot st T Cs Sg Scs Z ∅ s s' ⦄ := by
  unfold schedcontext.unbind_ntfn
  step with obj.Sc.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 ⟨h, Foot.refl _⟩
  rename_i hb
  have hcS : c ∈ Scs := hc (fun e => hb (by rw [eb, e]; rfl))
  step with obj.Sc.ntfn.val as ⟨j, ej⟩
  split
  · rename_i hj
    have hjN : j ∈ Nt := by rw [ej]; exact h.2.2.1.2.2.scn c hcS (by rw [← ej]; simpa using hj)
    refine WP.spec_bind (obj.Ntfn.set_sc.wr s j 0#u64) fun s1 e1 => ?_
    subst e1
    obtain ⟨h1, f1⟩ := ntsc_zero_all h hjN
    refine WP.spec_mono (obj.Sc.set_ntfn.wr _ c 0#u64) fun s2 e2 => ?_
    subst e2
    obtain ⟨h2, f2⟩ := scn_zero_all h1 hcS
    exact ⟨h2, f1.trans f2⟩
  · exact (WP.spec_ok _).2 ⟨h, Foot.refl _⟩

/-- `maybe_unbind_ntfn` (seL4 `schedContext_maybeUnbindNtfn`). -/
theorem schedcontext.maybe_unbind_ntfn.blk (s : S) (n : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z s)
    (hn : n ∈ Nt) :
    schedcontext.maybe_unbind_ntfn st s n ⦃ s' =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z s' ∧ Foot st T Cs Sg Scs Z ∅ s s' ⦄ := by
  unfold schedcontext.maybe_unbind_ntfn
  step with obj.Ntfn.sc.val as ⟨i, ei⟩
  step with obj.Sc.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 ⟨h, Foot.refl _⟩
  · exact schedcontext.unbind_ntfn.blk s i h fun h0 => by rw [ei]; exact h.2.2.1.2.2.nsc n hn (by rw [← ei]; exact h0)



/-- `unbind_maybe_notification`, with its footprint. -/
theorem notification.unbind_maybe_notification.blkF (s : S) (n : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z s)
    (hn : n ∈ Nt) :
    notification.unbind_maybe_notification st s n ⦃ s' =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z s' ∧ Foot st T Cs Sg Scs Z ∅ s s' ⦄ := by
  unfold notification.unbind_maybe_notification
  refine WP.spec_bind (obj.Ntfn.bound_tcb.val s n) fun i ei => ?_
  refine WP.spec_bind (obj.Tcb.is_null.spec i) fun b eb => ?_
  subst eb
  split
  · exact (WP.spec_ok _).2 ⟨h, Foot.refl _⟩
  · rename_i hb
    have hiT : i ∈ T := by
      rcases (show Tz T i by rw [ei]; exact h.2.2.1.2.2.ntb n hn) with e | e
      · exact absurd (by simp [e]) hb
      · exact e
    have hT := h.1.choose_spec.choose_spec.tcbs
    have hm : ntfnBtA n ∈ Sg := (h.2.2.1.1.ntB n hn).2
    refine WP.spec_bind (obj.Ntfn.set_bound_tcb.wr s n 0#u64) fun s1 e1 => ?_
    subst e1
    have h1 := ntbt_all h hn Tz.zero
    have f1 : Foot st T Cs Sg Scs Z ∅ s (L.wr s (ntfnBtA n) 0#u64) :=
      foot_wr (h.1.choose_spec.choose_spec.omega _ (h.2.2.2.2.sub _ hm)).1 (kw_sg hm)
    refine WP.spec_mono (obj.Tcb.set_bound_ntfn.wr _ i 0#u64) fun s2 e2 => ?_
    subst e2
    exact ⟨bnd_all h1 hiT fun h0 => absurd rfl h0,
      f1.trans (foot_field (K := 3368#u64) hT hiT (by simp) (by simp) (by simp) (by simp))⟩

/-! ## `finalise_cap` of an endpoint or a notification -/

/-- `finalise_cap` of an endpoint cap: `cancel_all_ipc` when final. -/
theorem fin_endpoint.blk {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (ep b0 b1 b2 b3 b4 : _)
    (fin : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z s) (hH : H ep = some .ep) :
    objects.finalise_cap_object st ar s a (.Endpoint ep b0 b1 b2 b3 b4) fin ⦃ r =>
      r.1 = (.Null, .Null) ∧ r.2.2 = a ∧
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z r.2.1 ∧ Foot st T Cs Sg Scs Z {ep} s r.2.1 ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  split
  · refine WP.spec_bind (endpoint.cancel_all_ipc.blk s ep h hH) fun s1 ⟨h1, f1⟩ => ?_
    exact (WP.spec_ok _).2 ⟨rfl, rfl, h1, f1⟩
  · exact (WP.spec_ok _).2 ⟨rfl, rfl, h, Foot.refl _⟩

/-- `finalise_cap` of a notification cap: the SC unbinding, the TCB
unbinding and `cancel_all_signals` when final. -/
theorem fin_ntfn.blk {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (n b0 b1 b2 : _)
    (fin : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z s) (hn : n ∈ Nt) (hH : H n = some .ntfn) :
    objects.finalise_cap_object st ar s a (.Notification n b0 b1 b2) fin ⦃ r =>
      r.1 = (.Null, .Null) ∧ r.2.2 = a ∧
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z r.2.1 ∧ Foot st T Cs Sg Scs Z {n} s r.2.1 ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  split
  · refine WP.spec_bind (schedcontext.maybe_unbind_ntfn.blk s n h hn) fun s1 ⟨h1, f1⟩ => ?_
    refine WP.spec_bind (notification.unbind_maybe_notification.blkF s1 n h1 hn) fun s2 ⟨h2, f2⟩ => ?_
    refine WP.spec_bind (notification.cancel_all_signals.blk s2 n h2 hH) fun s3 ⟨h3, f3⟩ => ?_
    exact (WP.spec_ok _).2 ⟨rfl, rfl, h3, (f1.trans f2).mono (Set.empty_subset _) |>.trans f3⟩
  · exact (WP.spec_ok _).2 ⟨rfl, rfl, h, Foot.refl _⟩


end

end Fl4Proofs.P1
