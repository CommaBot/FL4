/-
P1 (aarch64): **[J] `R.FinRvAt` discharged for the endpoint, notification and IRQ-handler kinds**; what stays named
is the narrower [J] `R.FinRvRest` (reply, SC, thread, VCPU, Stage-2 and device-frame kinds).

QueueDelRv's [J] `R.FinRvAt` says the finalisation of a `FinRvKind` cap, from a `Cur0` state of the deletion where
`RunVcpuInv` holds, ends in a `RunVcpuInv` state. Proved here:
* **Notification** (`fin_ntfn_obj.rvi`): `maybe_unbind_ntfn` / `unbind_maybe_notification` write an SC word, a
  notification word and a thread's `BOUND_NTFN` (3368): `RvSt` (`*.rvst`); `cancel_all_signals` restarts the
  waiters, each `TS_BLOCKED_ON_NTFN`, hence (`RunVcpuInv.blocked`) running no VCPU: `set_thread_state` keeps
  `RunVcpuInv` (`RunVcpuInv.keepT`), `unblock_sporadic` / `possible_switch_to` / `reschedule_required` keep every
  `STATE` and `RUN_VCPU` word (their TCB-field frames at 3328 / 3672) — `cas_round.rvi`, the loop, `.rvi`.
* **Endpoint** (`fin_endpoint.rvi`): `cancel_all_ipc` likewise (QueueDeleteRv's `RvW` text, carrying
  `RunVcpuInv`): each waiter is `TS_BLOCKED_ON_SEND` / `_RECV`, so runs no VCPU; `reply_unlink` sets it
  `INACTIVE`, `restart_thread_if_no_fault` sets it `RESTART` / `INACTIVE` (`.rvi`).
* **IRQ handler** (`finRv_irq`): `deleting_irq_handler` = the notification kind on the handler slot's cap, then
  `R.cdt.empty_slot.cur0` (proved over `Cur0R`, QueueDelRv) — uses the `rv`-free placement `R.DelPlaceAt`.
* `finRvAt_of` (`R.DelPlaceAt` + [J] `FinRvRest` ⇒ `FinRvAt`), `FinGapsAt2` / `FinGaps2` (`arch` unchanged, `rv`
  narrowed), `delGaps_of_gaps2`, **`decGap_cnode_rv2`**, **`decGap_thread2`**.

Named premises: **[J] `R.FinRvRest`** (new, strictly narrower than [J] `R.FinRvAt`, which it replaces in the `2`
forms): the same Hoare triple for the reply, SC, thread, VCPU, Stage-2 and device-frame kinds only. The `arch`
gap (`W7.FinGapsAt.arch`) and the placements ([P] `R.DelPlaceAt`) are unchanged. No existing statement changed.
-/
import Fl4ProofsA64.P1.QueueDecTcbRv
import Fl4ProofsA64.P1.QueueDeleteRv
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}

theorem schedcontext.unbind_ntfn.rvst (s : S) (c : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hc : c ≠ 0#u64 → c ∈ Scs) :
    schedcontext.unbind_ntfn st s c ⦃ s' => RvSt st T s s' ⦄ := by
  unfold schedcontext.unbind_ntfn
  step with obj.Sc.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 (RvSt.refl _)
  rename_i hb
  have hc0 : c ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
  have hcS : c ∈ Scs := hc hc0
  step with obj.Sc.ntfn.val as ⟨j, ej⟩
  split
  · rename_i hj
    have hjN : j ∈ Nt := by rw [ej]; exact h.2.2.1.2.2.scn c hcS (by rw [← ej]; simpa using hj)
    refine WP.spec_bind (obj.Ntfn.set_sc.wr s j 0#u64) fun s1 e1 => ?_
    subst e1
    have h1 := (ntsc_zero_all h hjN).1
    refine WP.spec_mono (obj.Sc.set_ntfn.wr _ c 0#u64) fun s2 e2 => ?_
    subst e2
    have hO := h.2.2.1.1
    have h0 := h.1.choose_spec.choose_spec
    have hm : scNtfnA c ∈ Ω := h.2.2.2.2.sub _ (hO.snW c hcS)
    have hmj : ntfnScA j ∈ Ω := h.2.2.2.2.sub _ (hO.ntW j hjN)
    have q1 := h1.1.choose_spec.choose_spec
    exact RvSt.trans (RvSt.wr_out h0.tcbs (h0.omega _ hmj)) (RvSt.wr_out h0.tcbs (q1.omega _ hm))
  · exact (WP.spec_ok _).2 (RvSt.refl _)

theorem schedcontext.maybe_unbind_ntfn.rvst (s : S) (n : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hn : n ∈ Nt) :
    schedcontext.maybe_unbind_ntfn st s n ⦃ s' => RvSt st T s s' ⦄ := by
  unfold schedcontext.maybe_unbind_ntfn
  step with obj.Ntfn.sc.val as ⟨i, ei⟩
  step with obj.Sc.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 (RvSt.refl _)
  · exact schedcontext.unbind_ntfn.rvst s i h fun h0 => by
      rw [ei]; exact (h.2.2.1.2.2.nsc n hn (by rw [← ei]; exact h0)).1

theorem notification.unbind_maybe_notification.rvst (s : S) (n : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hn : n ∈ Nt) :
    notification.unbind_maybe_notification st s n ⦃ s' => RvSt st T s s' ⦄ := by
  unfold notification.unbind_maybe_notification
  refine WP.spec_bind (obj.Ntfn.bound_tcb.val s n) fun i ei => ?_
  refine WP.spec_bind (obj.Tcb.is_null.spec i) fun b eb => ?_
  subst eb
  split
  · exact (WP.spec_ok _).2 (RvSt.refl _)
  · rename_i hb
    have hiT : i ∈ T := by
      rcases (show Tz T i by rw [ei]; exact h.2.2.1.2.2.ntb n hn) with e | e
      · exact absurd (by simp [e]) hb
      · exact e
    have h0 := h.1.choose_spec.choose_spec
    have hT := h0.tcbs
    have hm : ntfnBtA n ∈ Sg := (h.2.2.1.1.ntB n hn).2
    have hmO : ntfnBtA n ∈ Ω := h.2.2.2.2.sub _ hm
    refine WP.spec_bind (obj.Ntfn.set_bound_tcb.wr s n 0#u64) fun s1 e1 => ?_
    subst e1
    have q1 := (ntbt_all h hn Tz.zero).1.choose_spec.choose_spec
    refine WP.spec_mono (obj.Tcb.set_bound_ntfn.wr _ i 0#u64) fun s2 e2 => ?_
    subst e2
    have hN1 := q1.nodes _ q1.cur
    exact RvSt.trans (RvSt.wr_out hT (h0.omega _ hmO))
      (RvSt.wr_field (K := 3368#u64) hT hiT (by simp) (by simp) (by simp) (by simp))

theorem cas_round.rvi {β : Type _} (s : S) (n t : U64) (fuel1 : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hH : H n = some .ntfn) (hst : L.epState s n = 1#u64) (hhd : (L.epQ s n).head = t)
    (hRV : RunVcpuInv st T s) :
    (do
      let next ← tcbqueue.next_of st s .Ep t
      let s1 ← notification.ntfn_dequeue st s n t
      let s2 ← sched.set_thread_state st s1 t sched.TS_RESTART
      let s3 ← notification.unblock_sporadic st s2 t
      let s4 ← sched.possible_switch_to st s3 t
      ok (ControlFlow.cont (β := β) (s4, next, fuel1))) ⦃ r => ∃ s4 next, r = .cont (s4, next, fuel1) ∧
        RunVcpuInv st T s4 ⦄ := by
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
  have hyA := hB.sact y hdT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hbl))))))
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
  have tm1 : TmFr st T Cs Nt s s1 := TmFr.mk0 ⟨k1, fun y hy K a b c => f1 y hy K (by omega) c (by omega) (by omega),
    fun c hc o ho => nc1 c hc o (by omega) (by omega), fun n' hn' => o1 _ (hSg.sub _ (hX.1.ntB n' hn').2)⟩
  obtain ⟨hB1, hX1, hS1, hSg1, ea1, ec1, ei1⟩ := frame_bx h0 hB hX hS hSg f1 o1 n1 k1 tm1
  have st1 : L.mem s1 (stA y) = sched.TS_BLOCKED_ON_NTFN := by
    rw [stA_eq, f1 y hdT _ (by simp) (by simp) (by simp) (by simp), ← stA_eq]; exact hds
  have iq1 : L.mem s1 (inqA y) = L.mem s (inqA y) := by
    rw [inqA_eq]; exact f1 y hdT _ (by simp) (by simp) (by simp) (by simp)
  have fw1 : Foot st T Cs Sg Scs Z {n} s s1 := Foot.of w1 fun b hb => hb.kw hq.mem rfl
  obtain ⟨-, -, r3, -, r6⟩ := ts_vals
  have RV1 : RunVcpuInv st T s1 := hRV.rvSt fun z hz =>
    ⟨by rw [stA_eq]; exact f1 z hz _ (by simp) (by simp) (by simp) (by simp),
      f1 z hz 3672#u64 (by simp) (by simp) (by simp) (by simp)⟩
  have hz1 : L.mem s1 (runVcpuA y) = 0#u64 := RV1.blocked hdT (by rw [st1]; exact Or.inr (Or.inr rfl))
  refine WP.spec_bind (sts_all s1 y _ Q R h1 hB1 hX1 hS1 hSg1 hdT not_blocked_restart restart_ne
    (Or.inl (Or.inr rfl)) (hX1.noref hta (by rw [st1]; exact blocked_ne_reply (Or.inr (Or.inr rfl)))
      (by rw [st1, r3, r6]; decide))
    ⟨fun _ _ _ _ _ => runnable_restart, fun _ _ _ => runnable_restart, fun _ => runnable_restart⟩) ?_
  rintro s2 ⟨h2, hB2, hX2, hS2, hSg2, st2, k2⟩
  have RV2 := RV1.keepT k2 (Or.inr hz1)
  have h2' : SchedQueuesInv st T Cs Ω H s2 Q R := h2.congrX empty_congr'
  refine WP.spec_bind (endpoint.unblock_sporadic.all s2 y h2' hB2 hX2 hS2 hSg2 hdT) ?_
  rintro s3 ⟨h3, hB3, hX3, hS3, hSg3, -, -, -, fk3, -⟩
  have RV3 : RunVcpuInv st T s3 := RV2.rvSt fun z hz =>
    ⟨by rw [stA_eq]; exact fk3 z hz _ (by simp) (by simp), fk3 z hz 3672#u64 (by simp) (by simp)⟩
  refine WP.spec_bind (WP.spec_and
    (sched.possible_switch_to.fld (Sg := Sg) s3 y h3 hB3 hSg3 hdT (K := 3328#u64) (by simp) (by simp) (by simp) (by simp))
    (sched.possible_switch_to.fld (Sg := Sg) s3 y h3 hB3 hSg3 hdT (K := 3672#u64) (by simp) (by simp) (by simp) (by simp))) ?_
  rintro s4 ⟨f4a, f4b⟩
  exact (WP.spec_ok _).2 ⟨s4, next, rfl, RV3.rvSt fun z hz => ⟨by rw [stA_eq]; exact f4a z hz, f4b z hz⟩⟩

theorem notification.cancel_all_signals_loop.rvi (s : S) (n t fuel : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hH : H n = some .ntfn) (hf : RunVcpuInv st T s)
    (ht : t ≠ 0#u64 → L.epState s n = 1#u64 ∧ (L.epQ s n).head = t) :
    notification.cancel_all_signals_loop st s n t fuel ⦃ s' => RunVcpuInv st T s' ⦄ := by
  unfold notification.cancel_all_signals_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.2.val)
    (inv := fun x => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac x.1 ∧ RunVcpuInv st T x.1 ∧
      (x.2.1 ≠ 0#u64 → L.epState x.1 n = 1#u64 ∧ (L.epQ x.1 n).head = x.2.1))
  · rintro ⟨s1, t1, f1⟩ ⟨hb1, hf1, ht1⟩
    simp only at hb1 hf1 ht1
    unfold notification.cancel_all_signals_loop.body
    step with obj.Tcb.is_null.spec as ⟨b, eb⟩
    split
    · exact (WP.spec_ok _).2 hf1
    rename_i hb
    have ht0 : t1 ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    obtain ⟨hst1, hhd1⟩ := ht1 ht0
    split
    · rename_i hfuel
      step as ⟨fuel1, efuel⟩
      refine WP.spec_mono (WP.spec_and (cas_round (β := S) s1 n t1 fuel1 hb1 hH hst1 hhd1)
        (cas_round.rvi (β := S) s1 n t1 fuel1 hb1 hH hst1 hhd1 hf1)) ?_
      rintro r ⟨⟨s4, next, rfl, hb4, -, hn4⟩, ⟨s4', next', e', hc4⟩⟩
      simp only [ControlFlow.cont.injEq, Prod.mk.injEq] at e'
      obtain ⟨rfl, rfl, -⟩ := e'
      exact ⟨hb4, hc4, hn4, by simp only; omega⟩
    · exact (WP.spec_ok _).2 hf1
  · exact ⟨h, hf, ht⟩

theorem notification.cancel_all_signals.rvi (s : S) (n : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hRV : RunVcpuInv st T s)
    (hH : H n = some .ntfn) :
    notification.cancel_all_signals st s n ⦃ s' => RunVcpuInv st T s' ⦄ := by
  unfold notification.cancel_all_signals
  step with obj.Ntfn.state.spec as ⟨v, hv⟩
  split
  · exact (WP.spec_ok _).2 hRV
  rename_i hw
  have hst : L.epState s n = 1#u64 := by
    rw [← hv]; have := hw; simp [obj.NTFN_WAITING] at this; exact UScalar.eq_of_val_eq (by simpa using this)
  step with notification.get_queue.spec as ⟨q, eq⟩
  subst eq
  refine WP.spec_bind (WP.spec_and (notification.cancel_all_signals_loop.blk s s n _ _ h hH (Foot.refl _)
    (fun _ => ⟨hst, rfl⟩)) (notification.cancel_all_signals_loop.rvi s n _ _ h hH hRV
    (fun _ => ⟨hst, rfl⟩))) ?_
  rintro s1 ⟨⟨h1, -⟩, c1⟩
  obtain ⟨⟨Q1, R1, q1⟩, hB1, hX1, hS1, hSg1⟩ := h1
  refine WP.spec_mono (WP.spec_and
    (sched.reschedule_required.fldX (K := 3328#u64) s1 Q1 R1 q1 hB1 hSg1 (by simp) (by simp) (by simp) (by simp))
    (sched.reschedule_required.fldX (K := 3672#u64) s1 Q1 R1 q1 hB1 hSg1 (by simp) (by simp) (by simp) (by simp))) ?_
  rintro s2 ⟨f2a, f2b⟩
  exact c1.rvSt fun z hz => ⟨by rw [stA_eq]; exact f2a z hz, f2b z hz⟩

theorem endpoint.restart_thread_if_no_fault.rvi {X : Set U64} (s : S) (t : obj.Tcb) {Q : U64 → U64 → List U64}
    {R : U64 → List U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hXt : ∀ y ∈ X, y = t)
    (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hS : SCsOK st T Ω Sg Scs Z Ac s)
    (hSg : SgOK st Ω Sg s) (ht : t ∈ T) (hx : t ∈ X ∨ ¬ Blocked (L.mem s (stA t)))
    (hnoref : ∀ r ∈ Rp, L.mem s (rTcbA r) ≠ t)
    (hnQ : ∀ c ∈ Cs, ∀ p : U64, p.val < 256 → t ∉ Q c p) (hnR : ∀ c ∈ Cs, t ∉ R c) (hna : L.actionW s ≠ t)
    (hRV : RunVcpuInv st T s) (hz : L.mem s (runVcpuA t) = 0#u64) :
    endpoint.restart_thread_if_no_fault st s t ⦃ s' => RunVcpuInv st T s' ⦄ := by
  have hq : ∀ v : U64, (∀ c ∈ Cs, ∀ p : U64, p.val < 256 → t ∈ Q c p → Runnable v) ∧
      (∀ c ∈ Cs, t ∈ R c → Runnable v) ∧ (L.actionW s = t → Runnable v) := fun v =>
    ⟨fun c hc p hp htq => absurd htq (hnQ c hc p hp), fun c hc htr => absurd htr (hnR c hc),
      fun e => absurd e hna⟩
  have cg : ∀ y, y ∈ {y : U64 | y ∈ X ∧ y ≠ t} ↔ y ∈ (∅ : Set U64) := fun y => by
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_not]; exact hXt y
  unfold endpoint.restart_thread_if_no_fault
  step with obj.Tcb.fault_type.any as ⟨i, _hi⟩
  split
  · refine WP.spec_bind (sts_all s t _ Q R h hB hX hS hSg ht not_blocked_restart restart_ne hx hnoref (hq _)) ?_
    rintro s1 ⟨h1, hB1, hX1, hS1, hSg1, -, k1⟩
    have RV1 := hRV.keepT k1 (Or.inr hz)
    have h1' : SchedQueuesInv st T Cs Ω H s1 Q R := h1.congrX cg
    refine WP.spec_bind (endpoint.unblock_sporadic.all s1 t h1' hB1 hX1 hS1 hSg1 ht) ?_
    rintro s2 ⟨h2, hB2, -, -, hSg2, -, -, -, fk2, -⟩
    have RV2 : RunVcpuInv st T s2 := RV1.rvSt fun z hz =>
      ⟨by rw [stA_eq]; exact fk2 z hz _ (by simp) (by simp), fk2 z hz 3672#u64 (by simp) (by simp)⟩
    refine WP.spec_mono (WP.spec_and
      (sched.possible_switch_to.fld (Sg := Sg) s2 t h2 hB2 hSg2 ht (K := 3328#u64) (by simp) (by simp) (by simp) (by simp))
      (sched.possible_switch_to.fld (Sg := Sg) s2 t h2 hB2 hSg2 ht (K := 3672#u64) (by simp) (by simp) (by simp) (by simp))) ?_
    rintro s3 ⟨f3a, f3b⟩
    exact RV2.rvSt fun z hz => ⟨by rw [stA_eq]; exact f3a z hz, f3b z hz⟩
  · refine WP.spec_mono (sts_all s t _ Q R h hB hX hS hSg ht not_blocked_inactive inactive_ne hx hnoref
      (hq _)) ?_
    rintro s1 ⟨-, -, -, -, -, -, k1⟩
    exact hRV.keepT k1 (Or.inr hz)

theorem cai_round.rvi {β : Type _} (s : S) (ep t : U64) (fuel1 : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hH : H ep = some .ep) (hst : L.epState s ep = 1#u64 ∨ L.epState s ep = 2#u64) (hhd : (L.epQ s ep).head = t)
    (hRV : RunVcpuInv st T s) :
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
        RunVcpuInv st T s3 ⦄ := by
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
  unfold tcbqueue.next_of
  step with tcbqueue.next.spec as ⟨next, enext⟩
  have hdq := endpoint.ep_dequeue.inv s y Q R h0 hdT (by simp) hbl
  rw [hbe] at hdq
  refine WP.spec_bind hdq ?_
  rintro s1 ⟨h1, f1, o1, n1, k1, c1, nc1⟩
  have tm1 : TmFr st T Cs Nt s s1 := TmFr.mk0 ⟨k1, fun y hy K a b c => f1 y hy K (by omega) c (by omega) (by omega),
    fun c hc o ho => nc1 c hc o (by omega) (by omega), fun n' hn' => o1 _ (hSg.sub _ (hX.1.ntB n' hn').2)⟩
  obtain ⟨hB1, hX1, hS1, hSg1, ea1, -, -⟩ := frame_bx h0 hB hX hS hSg f1 o1 n1 k1 tm1
  have R1 : RvW st T s s1 := fun z hz => f1 z hz 3672#u64 (by simp) (by simp) (by simp) (by simp)
  have st1 : L.mem s1 (stA y) = L.mem s (stA y) := by
    rw [stA_eq]; exact f1 y hdT _ (by simp) (by simp) (by simp) (by simp)
  have da1 : L.actionW s1 ≠ y := by rw [ea1]; exact da
  have RV1 : RunVcpuInv st T s1 := hRV.rvSt fun z hz => ⟨by rw [stA_eq]; exact f1 z hz _ (by simp) (by simp) (by simp) (by simp), R1 z hz⟩
  have hz1 : L.mem s1 (runVcpuA y) = 0#u64 := (R1 y hdT).trans (hRV.blocked hdT hbl)
  have tail : ∀ (s2 : S),
      endpoint.restart_thread_if_no_fault st s2 y ⦃ s' => RunVcpuInv st T s' ⦄ →
      (do
        let s3 ← endpoint.restart_thread_if_no_fault st s2 y
        ok (ControlFlow.cont (β := β) (s3, next, fuel1))) ⦃ r => ∃ s3 next', r = .cont (s3, next', fuel1) ∧
          RunVcpuInv st T s3 ⦄ := by
    intro s2 hr
    exact WP.spec_bind hr fun s3 R3 => (WP.spec_ok _).2 ⟨s3, next, rfl, R3⟩
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
      refine WP.spec_bind (ipc.reply_unlink.inv s1 i1 y Q R h1 hdT hX1.1 hSg1.sub hr hrt
        (by rw [st1]; exact hnrun) (Or.inl (Or.inr rfl))) ?_
      rintro s2 ⟨h2, e2, k2, z2⟩
      have hB2 := hB1.keepT h1 k2 (by rw [e2]; exact not_blocked_inactive) (by rw [e2]; exact inactive_ne.1)
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
      refine tail s2 (endpoint.restart_thread_if_no_fault.rvi s2 y h2 (fun z hz => ?_)
        hB2 hX2 hS2 hSg2 hdT (Or.inr (by rw [e2]; exact not_blocked_inactive))
        (hX2.noref hta (by rw [e2]; exact inactive_ne.1) (by rw [e2]; exact inactive_ne.2)) hnQ hnR da2
        (RV1.keepT k2 (Or.inr hz1)) ((RvW.of_keepT k2 y hdT).trans hz1))
      obtain ⟨hz1, hz2⟩ := hz
      exact absurd (cg1 z hz1) hz2
    · rename_i hi1
      have hz : i1 = 0#u64 := by apply UScalar.eq_of_val_eq; simpa using hi1
      have hi10 : L.mem s1 (replyA y) = 0#u64 := by rw [← ei1]; exact hz
      simp only [Aeneas.Std.bind_ok]
      exact tail s1 (endpoint.restart_thread_if_no_fault.rvi s1 y h1 cg1 hB1 hX1 hS1 hSg1 hdT
        (Or.inl (Or.inr rfl)) (hX1.noref0 hta hi10) hnQ hnR da1 RV1 hz1)
  · rename_i hnrecv
    have hsend : L.mem s1 (stA y) = sched.TS_BLOCKED_ON_SEND := by
      rcases hsr with e | e
      · rw [st1, e]
      · exact absurd (by rw [ei, st1, e]) hnrecv
    have nrp : sched.TS_BLOCKED_ON_SEND ≠ sched.TS_BLOCKED_ON_REPLY := by
      rw [r4]; unfold sched.TS_BLOCKED_ON_REPLY; decide
    have nrc : sched.TS_BLOCKED_ON_SEND ≠ sched.TS_BLOCKED_ON_RECV := by rw [r4, r3]; decide
    simp only [Aeneas.Std.bind_ok]
    exact tail s1 (endpoint.restart_thread_if_no_fault.rvi s1 y h1 cg1 hB1 hX1 hS1 hSg1 hdT
      (Or.inl (Or.inr rfl)) (hX1.noref hta (by rw [hsend]; exact nrp) (by rw [hsend]; exact nrc)) hnQ hnR da1 RV1 hz1)

theorem endpoint.cancel_all_ipc_loop.rvi (s0 s : S) (ep t fuel : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hH : H ep = some .ep) (hf : Foot st T Cs Sg Scs Z {ep} s0 s) (hF : CaiFr st T Scs 0#u64 s0 s)
    (hR : RunVcpuInv st T s)
    (ht : t ≠ 0#u64 → (L.epState s ep = 1#u64 ∨ L.epState s ep = 2#u64) ∧ (L.epQ s ep).head = t) :
    endpoint.cancel_all_ipc_loop st s ep t fuel ⦃ s' =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ Foot st T Cs Sg Scs Z {ep} s0 s' ∧ CaiFr st T Scs 0#u64 s0 s' ∧
      RunVcpuInv st T s' ⦄ := by
  unfold endpoint.cancel_all_ipc_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.2.val)
    (inv := fun x => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac x.1 ∧ Foot st T Cs Sg Scs Z {ep} s0 x.1 ∧
      CaiFr st T Scs 0#u64 s0 x.1 ∧ RunVcpuInv st T x.1 ∧
      (x.2.1 ≠ 0#u64 → (L.epState x.1 ep = 1#u64 ∨ L.epState x.1 ep = 2#u64) ∧ (L.epQ x.1 ep).head = x.2.1))
  · rintro ⟨s1, t1, f1⟩ ⟨hb1, hf1, hF1, hR1, ht1⟩
    simp only at hb1 hf1 hF1 hR1 ht1
    unfold endpoint.cancel_all_ipc_loop.body
    step with obj.Tcb.is_null.spec as ⟨b, eb⟩
    split
    · exact (WP.spec_ok _).2 ⟨hb1, hf1, hF1, hR1⟩
    rename_i hb
    have ht0 : t1 ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    obtain ⟨hst1, hhd1⟩ := ht1 ht0
    split
    · rename_i hfuel
      step as ⟨fuel1, efuel⟩
      refine WP.spec_mono (WP.spec_and (cai_round.fr (β := S) s1 ep t1 fuel1 hb1 hH hst1 hhd1)
        (cai_round.rvi (β := S) s1 ep t1 fuel1 hb1 hH hst1 hhd1 hR1)) ?_
      rintro r ⟨⟨s4, next, rfl, hb4, hf4, hn4, hF4⟩, ⟨s4', next', e', hR4⟩⟩
      injection e' with e'
      simp only [Prod.mk.injEq] at e'
      obtain ⟨rfl, -, -⟩ := e'
      exact ⟨hb4, hf1.trans hf4, hF1.trans hb1.1.choose_spec.choose_spec.tcbs hF4, hR4, hn4,
        by simp only; omega⟩
    · exact (WP.spec_ok _).2 ⟨hb1, hf1, hF1, hR1⟩
  · exact ⟨h, hf, hF, hR, ht⟩


theorem endpoint.cancel_all_ipc.rvi (s : S) (ep : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hRV : RunVcpuInv st T s)
    (hH : H ep = some .ep) :
    endpoint.cancel_all_ipc st s ep ⦃ s' => RunVcpuInv st T s' ⦄ := by
  unfold endpoint.cancel_all_ipc
  step with obj.Ep.state.spec as ⟨v, hv⟩
  split
  · exact (WP.spec_ok _).2 hRV
  rename_i hidle
  have hst : L.epState s ep ≠ 0#u64 := by
    rw [← hv]; intro e; exact hidle (by rw [e]; unfold obj.EP_IDLE; rfl)
  step with endpoint.get_queue.spec as ⟨q, eq⟩
  subst eq
  have hI := h
  obtain ⟨⟨Q, R, h0⟩, -⟩ := hI
  refine WP.spec_bind (endpoint.cancel_all_ipc_loop.rvi s s ep _ _ h hH (Foot.refl _) (CaiFr.refl _ _)
    hRV (fun _ => ⟨ep_state12 h0 hH hst, rfl⟩)) ?_
  rintro s1 ⟨h1, -, -, R1⟩
  obtain ⟨⟨Q1, R1', q1⟩, hB1, -, -, hSg1⟩ := h1
  refine WP.spec_mono (WP.spec_and
    (sched.reschedule_required.fldX (K := 3328#u64) s1 Q1 R1' q1 hB1 hSg1 (by simp) (by simp) (by simp) (by simp))
    (sched.reschedule_required.fldX (K := 3672#u64) s1 Q1 R1' q1 hB1 hSg1 (by simp) (by simp) (by simp) (by simp))) ?_
  rintro s2 ⟨f2a, f2b⟩
  exact R1.rvSt fun z hz => ⟨by rw [stA_eq]; exact f2a z hz, f2b z hz⟩

theorem fin_endpoint.rvi {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (ep b0 b1 b2 b3 b4 : _)
    (fin : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hH : H ep = some .ep) (hRV : RunVcpuInv st T s) :
    objects.finalise_cap_object st ar s a (.Endpoint ep b0 b1 b2 b3 b4) fin ⦃ r => RunVcpuInv st T r.2.1 ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  split
  · exact WP.spec_bind (endpoint.cancel_all_ipc.rvi s ep h hRV hH) fun s1 R1 => (WP.spec_ok _).2 R1
  · exact (WP.spec_ok _).2 hRV

/-- **The notification object's finalisation keeps [J] `RunVcpuInv`.** -/
theorem fin_ntfn_obj.rvi {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (n b0 : U64) (b1 b2 : Bool)
    (fin : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hn : n ∈ Nt) (hH : H n = some .ntfn)
    (hRV : RunVcpuInv st T s) :
    objects.finalise_cap_object st ar s a (.Notification n b0 b1 b2) fin ⦃ r => RunVcpuInv st T r.2.1 ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  split
  · refine WP.spec_bind (WP.spec_and (schedcontext.maybe_unbind_ntfn.blk s n h hn)
      (schedcontext.maybe_unbind_ntfn.rvst s n h hn)) ?_
    rintro s1 ⟨⟨h1, _⟩, r1⟩
    refine WP.spec_bind (WP.spec_and (notification.unbind_maybe_notification.blkF s1 n h1 hn)
      (notification.unbind_maybe_notification.rvst s1 n h1 hn)) ?_
    rintro s2 ⟨⟨h2, _⟩, r2⟩
    exact WP.spec_bind (notification.cancel_all_signals.rvi s2 n h2 ((hRV.rvSt r1).rvSt r2) hH)
      fun s3 r3 => (WP.spec_ok _).2 r3
  · exact (WP.spec_ok _).2 hRV

namespace W7
namespace R

/-- The endpoint kind keeps [J] `RunVcpuInv`. -/
theorem finRv_ep {A : Type _} {ar : machine.Arch A} {s0 s : S} {a : A} {ep b0 b1 b2 b3 b4 : _} {fin : Bool}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hRV : RunVcpuInv st T s)
    (hc : DelCapOK T Ω Sg H Rp Nt (.Endpoint ep b0 b1 b2 b3 b4)) :
    objects.finalise_cap st ar s a (.Endpoint ep b0 b1 b2 b3 b4) fin false ⦃ r => RunVcpuInv st T r.2.1 ⦄ := by
  have hH := hc.1.1 ep b0 b1 b2 b3 b4 rfl
  obtain ⟨Ac', hb⟩ := h.bxi
  rw [fin_cap_eq_obj (by simp)]
  exact fin_endpoint.rvi s a ep b0 b1 b2 b3 b4 fin hb.blk hH hRV

/-- The notification kind keeps [J] `RunVcpuInv`. -/
theorem finRv_ntfn {A : Type _} {ar : machine.Arch A} {s0 s : S} {a : A} {n b0 : U64} {b1 b2 : Bool} {fin : Bool}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hRV : RunVcpuInv st T s)
    (hc : DelCapOK T Ω Sg H Rp Nt (.Notification n b0 b1 b2)) :
    objects.finalise_cap st ar s a (.Notification n b0 b1 b2) fin false ⦃ r => RunVcpuInv st T r.2.1 ⦄ := by
  obtain ⟨hn, hH⟩ := hc.1.2.1 n b0 b1 b2 rfl
  obtain ⟨Ac', hb⟩ := h.bxi
  rw [fin_cap_eq_obj (by simp)]
  exact fin_ntfn_obj.rvi s a n b0 b1 b2 fin hb.blk hn hH hRV

set_option maxHeartbeats 1000000 in
/-- The IRQ-handler kind keeps [J] `RunVcpuInv` (the handler slot's notification cap, then `empty_slot` over
`Cur0R`), from the `rv`-free placement. -/
theorem finRv_irq {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop} {s0 s : S}
    (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) {a : A} {irq : U64} {fin : Bool}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hRV : RunVcpuInv st T s)
    (hc : DelCapOK T Ω Sg H Rp Nt (.IrqHandler irq)) :
    objects.finalise_cap st ar s a (.IrqHandler irq) fin false ⦃ r => RunVcpuInv st T r.2.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hi := hc.2.1 irq rfl
  obtain ⟨Ac', hb⟩ := h.bxi
  unfold objects.finalise_cap
  simp only [bind_ok]
  refine WP.spec_bind (Pₘ := fun r : S × A => RunVcpuInv st T r.1) ?_ ?_
  · split
    · unfold interrupt.deleting_irq_handler
      refine WP.spec_bind (interrupt.irq_slot.val s irq) fun isl eisl => ?_
      subst eisl
      have hW := slotW_to7 (irq_slotW hb hi)
      unfold cdt.delete_one
      refine WP.spec_bind (WP.spec_and (P.irq Ac' s irq h.fr hb hi) (P.cap Ac' s _ h.fr hb hW)) fun c ⟨hc', hcd⟩ => ?_
      refine WP.spec_bind (P0.capability.Cap.is_null.p0 c) fun bn _ => ?_
      split
      · exact (WP.spec_ok _).2 hRV
      refine WP.spec_bind (P0.cdt.is_final_capability_with_cap.p0 st s _ c hS) fun f _ => ?_
      rcases hc' with rfl | ⟨n, b0, b1, b2, rfl⟩
      · simp [objects.finalise_cap_object]
        exact WP.spec_mono (cdt.empty_slot.cur0 hA P ⟨h, hRV⟩ hW DelCapOK.null) fun r hr => hr.2
      · obtain ⟨hn, hH⟩ := hcd.1.1.2.1 n b0 b1 b2 rfl
        refine WP.spec_bind (WP.spec_and (fin_ntfn_obj.cur0 (ar := ar) (a := a) (fin := f) (b0 := b0) (b1 := b1)
          (b2 := b2) h hn hH) (fin_ntfn_obj.rvi (ar := ar) s a n b0 b1 b2 f hb.blk hn hH hRV)) ?_
        rintro ⟨_, s1, a1⟩ ⟨⟨_, h1⟩, r1⟩
        exact WP.spec_mono (cdt.empty_slot.cur0 hA P ⟨h1, r1⟩ hW DelCapOK.null) fun r hr => hr.2
    · exact (WP.spec_ok _).2 hRV
  rintro ⟨s1, a1⟩ h1
  simp only at h1 ⊢
  unfold objects.finalise_cap_object
  dsimp only
  split
  · exact (WP.spec_ok _).2 h1
  · exact (WP.spec_ok _).2 h1

/-- The kinds whose `RunVcpuInv` preservation is still named ([J] `FinRvRest`). -/
def FinRvRestKind (c : capability.Cap) : Prop :=
  (∃ x1 x2, c = .Reply x1 x2) ∨ (∃ x1 x2, c = .SchedContext x1 x2) ∨ (∃ x1, c = .Thread x1) ∨
  (∃ x1, c = .Vcpu x1) ∨ (∃ x1 x2 x3 x4 x5, c = .Ept x1 x2 x3 x4 x5) ∨
  (∃ x1 x2 x3 x4 x5 x6 x7, c = .Frame x1 x2 x3 x4 x5 true x6 x7)

/-- **[J] (a64) `FinRvRest`**: [J] `FinRvAt` narrowed to the reply, SC, thread, VCPU, Stage-2 and device-frame
kinds (`FinRvRestKind`): their finalisation, from a `Cur0` state of the deletion where `RunVcpuInv` holds, ends in
a `RunVcpuInv` state. The endpoint, notification and IRQ-handler kinds are proved (`finRv_ep`, `finRv_ntfn`,
`finRv_irq`). -/
def FinRvRest (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A) (T Cs Ω : Set U64)
    (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (s0 : S) : Prop :=
  ∀ (Ac : Set U64) (s : S) (a : A) (c : capability.Cap) (fin : Bool),
    Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s → RunVcpuInv st T s → DelCapOK T Ω Sg H Rp Nt c → FinPl st Scs s c →
    FinRvRestKind c → objects.finalise_cap st ar s a c fin false ⦃ r => RunVcpuInv st T r.2.1 ⦄

/-- **[J] `FinRvAt` from the `rv`-free placement and [J] `FinRvRest`.** -/
theorem finRvAt_of {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop} {s0 : S}
    (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) (G : FinRvRest st ar T Cs Ω H Sg Rp Scs Nt Z s0) :
    FinRvAt st ar T Cs Ω H Sg Rp Scs Nt Z s0 := by
  intro Ac s a c fin h hRV hc hpl hk
  rcases hk with ⟨x1, x2, x3, x4, x5, x6, rfl⟩ | ⟨x1, x2, x3, x4, rfl⟩ | hk | hk | hk | ⟨x1, rfl⟩ | hk | hk | hk
  · exact finRv_ep h hRV hc
  · exact finRv_ntfn h hRV hc
  · exact G Ac s a _ fin h hRV hc hpl (Or.inl hk)
  · exact G Ac s a _ fin h hRV hc hpl (Or.inr (Or.inl hk))
  · exact G Ac s a _ fin h hRV hc hpl (Or.inr (Or.inr (Or.inl hk)))
  · exact finRv_irq hA P h hRV hc
  · exact G Ac s a _ fin h hRV hc hpl (Or.inr (Or.inr (Or.inr (Or.inl hk))))
  · exact G Ac s a _ fin h hRV hc hpl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hk)))))
  · exact G Ac s a _ fin h hRV hc hpl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hk)))))

/-- The finalisation gaps with `rv` narrowed: the existing `arch` gap and **[J] `FinRvRest`**. -/
structure FinGapsAt2 (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (s0 : S) : Prop where
  arch : W7.FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z (fun c => (∃ x1, c = .Vcpu x1) ∨
    (∃ x1 x2 x3 x4 x5, c = .Ept x1 x2 x3 x4 x5) ∨
    (∃ x1 x2 x3 x4 x5 x6 x7, c = .Frame x1 x2 x3 x4 x5 true x6 x7)) s0
  /-- **[J] (a64)** `FinRvRest` (above). -/
  rv : FinRvRest st ar T Cs Ω H Sg Rp Scs Nt Z s0

/-- `FinGapsAt2` at every decode start reached from a `P3Ok` entry. -/
def FinGaps2 (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (P3Ok : S → Prop) : Prop :=
  ∀ s0, EntAt st P3Ok s0 → FinGapsAt2 st ar T Cs Ω H Sg Rp Scs Nt Z s0

theorem FinGapsAt2.toAt {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop} {s0 : S}
    (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) (G : FinGapsAt2 st ar T Cs Ω H Sg Rp Scs Nt Z s0) :
    FinGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0 :=
  ⟨G.arch, finRvAt_of hA P G.rv⟩

/-- **`R.DelGaps`** from `R.DelPlace` and `FinGaps2` (no [J] `DelPlaceAt.rv`, [J] `FinRvRest` only). -/
theorem delGaps_of_gaps2 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    (P : DelPlace st T Cs Ω H Sg Rp Scs Nt Z V P3Ok) (G : FinGaps2 st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok) :
    DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok :=
  fun s0 hE => delGaps_of hA (P s0 hE) ((G s0 hE).toAt hA (P s0 hE))

/-- The `CNode` family's decode gap from `FinGaps2`. -/
theorem decGap_cnode_rv2 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    (C : CdtHyps2 st T Cs Ω H Sg Rp Scs Nt Z P3Ok) (P : DelPlace st T Cs Ω H Sg Rp Scs Nt Z V P3Ok)
    (G : FinGaps2 st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok) : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .cnode :=
  decGap_cnode2 hA C (delGaps_of_gaps2 hA P G)

/-- The thread family's decode gap from `FinGaps2` (QueueDecTcbRv's `decGap_thread`). -/
theorem decGap_thread2 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    (Y : SspHyps st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (P : TcbPlace st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (Pd : DelPlace st T Cs Ω H Sg Rp Scs Nt Z V P3Ok) (G : FinGaps2 st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok)
    (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok) (TP : TcbPlace7 st T Cs Ω H Sg Rp Scs Nt Z P3Ok) :
    DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .thread :=
  decGap_thread hA Y P E (delGaps_of_gaps2 hA Pd G) C TP

end R
end W7

end

end Fl4ProofsA64.P1
