/-
P1: a final cap's `finalise_cap` leaves the object *dead*, read by nothing
P1 tracks (the per-kind facts behind P3's `FinDeadHyp`, ScPlaceDead):

* endpoint: `cancel_all_ipc` leaves it idle (`fin_cap_ep.dead`);
* notification: the SC and TCB unbindings null its `SC` and `BOUND_TCB`
  words, and `cancel_all_signals` leaves it not waiting; the later steps
  keep both words (`NtKeep`) (`fin_cap_ntfn.dead`);
* reply: its `TCB` word ends null: `reply_remove` (through `reply_pop`) ends
  with `reply_unlink`; `cancel_ipc` clears every reply naming the thread; the
  remaining case contradicts `back` (`fin_cap_reply.dead`);
* SC: its `TCB`, `REPLY` and `NTFN` words end null (`fin_cap_sc.dead`).

The loops of `cancel_all_ipc` and `cancel_all_signals` run on `WALK_FUEL`;
they never run out, since each round unblocks the queue head for good (a
thread's state is kept, or becomes `Restart`/`Inactive`, `CaiFr.st`), so the
count of blocked threads (`blkN`, at most `2^64 - 1`) bounds the rounds
left.  The round, `reply_pop`/`reply_remove` and `fin_sc` lemmas are P1's
(`cai_round.fr`, `cas_round`, `ipc.reply_pop.blk`, `ipc.reply_remove.blk`,
`fin_sc.blk`) with the extra post threaded through.
-/
import Fl4Proofs.P1.QueueFinCap
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-! ## Counting the blocked threads -/

section blk
open Classical

/-- The number of blocked threads of `T`. -/
noncomputable def blkN (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s : S) : Nat :=
  ((Finset.Icc 1 (2 ^ 64 - 1)).filter (fun n => ∃ z ∈ T, z.val = n ∧ Blocked (L.mem s (stA z)))).card

theorem blkN_le (s : S) : blkN st T s ≤ 2 ^ 64 - 1 := by
  unfold blkN
  refine (Finset.card_filter_le _ _).trans ?_
  simp

theorem blkN_pos {s : S} {t : U64} (ht : t ∈ T) (h0 : t ≠ 0#u64) (hb : Blocked (L.mem s (stA t))) :
    0 < blkN st T s := by
  unfold blkN
  refine Finset.card_pos.2 ⟨t.val, Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨?_, ?_⟩, t, ht, rfl, hb⟩⟩
  · have : t.val ≠ 0 := fun e => h0 (UScalar.eq_of_val_eq (by simpa using e))
    omega
  · have := t.hBounds; simp at this; omega

theorem blkN_lt {s s' : S} {t : U64} (hmono : ∀ z ∈ T, Blocked (L.mem s' (stA z)) → Blocked (L.mem s (stA z)))
    (ht : t ∈ T) (h0 : t ≠ 0#u64) (hb : Blocked (L.mem s (stA t))) (hb' : ¬ Blocked (L.mem s' (stA t))) :
    blkN st T s' < blkN st T s := by
  unfold blkN
  refine Finset.card_lt_card ⟨fun n hn => ?_, fun hsub => ?_⟩
  · obtain ⟨hn, z, hz, e, hbz⟩ := Finset.mem_filter.1 hn
    exact Finset.mem_filter.2 ⟨hn, z, hz, e, hmono z hz hbz⟩
  · have hm : t.val ∈ (Finset.Icc 1 (2 ^ 64 - 1)).filter
        (fun n => ∃ z ∈ T, z.val = n ∧ Blocked (L.mem s (stA z))) := by
      refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨?_, ?_⟩, t, ht, rfl, hb⟩
      · have : t.val ≠ 0 := fun e => h0 (UScalar.eq_of_val_eq (by simpa using e))
        omega
      · have := t.hBounds; simp at this; omega
    obtain ⟨-, z, -, e, hbz⟩ := Finset.mem_filter.1 (hsub hm)
    have : z = t := UScalar.eq_of_val_eq e
    subst this
    exact hb' hbz

end blk

/-- Along a `CaiFr` step a blocked thread was blocked before. -/
theorem CaiFr.blocked {x : U64} {s s' : S} (F : CaiFr st T Scs x s s') :
    ∀ z ∈ T, Blocked (L.mem s' (stA z)) → Blocked (L.mem s (stA z)) := by
  intro z hz hb
  rcases F.st z hz with e | e | e
  · rwa [← e]
  · rw [e] at hb; exact absurd hb not_blocked_restart
  · rw [e] at hb; exact absurd hb not_blocked_inactive

/-! ## `cancel_all_ipc` -/

/-- `restart_thread_if_no_fault` leaves the thread `Restart` or `Inactive`. -/
theorem endpoint.restart_thread_if_no_fault.stD {X : Set U64} (s : S) (t : obj.Tcb) {Q : U64 → U64 → List U64}
    {R : U64 → List U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hXt : ∀ y ∈ X, y = t)
    (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hS : SCsOK st T Ω Sg Scs Z Ac s)
    (hSg : SgOK st Ω Sg s) (ht : t ∈ T) (hx : t ∈ X ∨ ¬ Blocked (L.mem s (stA t)))
    (hnoref : ∀ r ∈ Rp, L.mem s (rTcbA r) ≠ t)
    (hnQ : ∀ c ∈ Cs, ∀ p : U64, p.val < 256 → t ∉ Q c p) (hnR : ∀ c ∈ Cs, t ∉ R c) (hna : L.actionW s ≠ t)
    (htA : L.mem s (scA t) ≠ 0#u64 → L.mem s (scA t) ∈ Ac) :
    endpoint.restart_thread_if_no_fault st s t ⦃ s' =>
      L.mem s' (stA t) = sched.TS_RESTART ∨ L.mem s' (stA t) = sched.TS_INACTIVE ⦄ := by
  have hq : ∀ v : U64, (∀ c ∈ Cs, ∀ p : U64, p.val < 256 → t ∈ Q c p → Runnable v) ∧
      (∀ c ∈ Cs, t ∈ R c → Runnable v) ∧ (L.actionW s = t → Runnable v) := fun v =>
    ⟨fun c hc p hp htq => absurd htq (hnQ c hc p hp), fun c hc htr => absurd htr (hnR c hc),
      fun e => absurd e hna⟩
  have cg : ∀ y, y ∈ {y : U64 | y ∈ X ∧ y ≠ t} ↔ y ∈ (∅ : Set U64) := fun y => by
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_not]; exact hXt y
  unfold endpoint.restart_thread_if_no_fault
  step with obj.Tcb.fault_type.any as ⟨i⟩
  split
  · refine WP.spec_bind (sts_all s t _ Q R h hB hX hS hSg ht not_blocked_restart restart_ne hx hnoref (hq _)) ?_
    rintro s1 ⟨h1, hB1, hX1, hS1, hSg1, st1, k1⟩
    have h1' : SchedQueuesInv st T Cs Ω H s1 Q R := h1.congrX cg
    refine WP.spec_bind (endpoint.unblock_sporadic.all s1 t h1' hB1 hX1 hS1 hSg1 ht) ?_
    rintro s2 ⟨h2, hB2, hX2, hS2, hSg2, ea2, ec2, ei2, fk2, -⟩
    have st2 : L.mem s2 (stA t) = sched.TS_RESTART := by
      rw [stA_eq, fk2 t ht _ (by simp) (by simp), ← stA_eq]; exact st1
    have esc2 : L.mem s2 (scA t) = L.mem s (scA t) := by
      rw [scA_eq, fk2 t ht _ (by simp) (by simp), ← scA_eq, k1.scf ht]
    refine WP.spec_mono (sched.possible_switch_to.sch (Sg := Sg) s2 t Q R h2 hB2 hSg2 ht
      (by rw [st2]; exact runnable_restart) (by rw [esc2]; exact htA)) ?_
    rintro s3 ⟨p3, -, -⟩
    exact Or.inl (by rw [p3.fr.st t ht]; exact st2)
  · refine WP.spec_mono (sts_all s t _ Q R h hB hX hS hSg ht not_blocked_inactive inactive_ne hx hnoref
      (hq _)) ?_
    rintro s1 ⟨-, -, -, -, -, st1, -⟩
    exact Or.inr st1

theorem endpoint.restart_thread_if_no_fault.bfD {X : Set U64} (s : S) (t : obj.Tcb) {Q : U64 → U64 → List U64}
    {R : U64 → List U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hXt : ∀ y ∈ X, y = t)
    (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hS : SCsOK st T Ω Sg Scs Z Ac s)
    (hSg : SgOK st Ω Sg s) (ht : t ∈ T) (hx : t ∈ X ∨ ¬ Blocked (L.mem s (stA t)))
    (hnoref : ∀ r ∈ Rp, L.mem s (rTcbA r) ≠ t)
    (hnQ : ∀ c ∈ Cs, ∀ p : U64, p.val < 256 → t ∉ Q c p) (hnR : ∀ c ∈ Cs, t ∉ R c) (hna : L.actionW s ≠ t)
    (htA : L.mem s (scA t) ≠ 0#u64 → L.mem s (scA t) ∈ Ac) :
    endpoint.restart_thread_if_no_fault st s t ⦃ s' =>
      ((BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ Foot st T Cs Sg Scs Z ∅ s s') ∧ CaiFr st T Scs t s s') ∧
      ¬ Blocked (L.mem s' (stA t)) ⦄ :=
  WP.spec_mono (WP.spec_and (endpoint.restart_thread_if_no_fault.bf s t h hXt hB hX hS hSg ht hx hnoref hnQ hnR hna htA)
    (endpoint.restart_thread_if_no_fault.stD s t h hXt hB hX hS hSg ht hx hnoref hnQ hnR hna htA))
    fun _ ⟨a, e⟩ => ⟨a, by rcases e with e | e <;> rw [e]; exacts [not_blocked_restart, not_blocked_inactive]⟩

/-- `cai_round.fr`, with the round's head left unblocked and the endpoint idle
once the queue is empty. -/
theorem cai_round.dead {β : Type _} (s : S) (ep t : U64) (fuel1 : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
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
        BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s3 ∧ Foot st T Cs Sg Scs Z {ep} s s3 ∧
        (next ≠ 0#u64 → (L.epState s3 ep = 1#u64 ∨ L.epState s3 ep = 2#u64) ∧ (L.epQ s3 ep).head = next) ∧
        CaiFr st T Scs 0#u64 s s3 ∧ (next = 0#u64 → L.epState s3 ep = 0#u64) ∧ ¬ Blocked (L.mem s3 (stA t)) ⦄ := by
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
  have F1 : CaiFr st T Scs y s s1 := CaiFr.of_fields k1 ec1 ei1 ea1
    (fun z hz => by rw [scA_eq]; exact f1 z hz _ (by simp) (by simp) (by simp) (by simp))
    (fun z hz => by rw [stA_eq]; exact f1 z hz _ (by simp) (by simp) (by simp) (by simp))
    (fun z hz => by rw [inqA_eq]; exact f1 z hz _ (by simp) (by simp) (by simp) (by simp))
    (fun c hc => o1 _ (hSg.sub _ (hX.1.fixW c hc).1))
  have st1 : L.mem s1 (stA y) = L.mem s (stA y) := by
    rw [stA_eq]; exact f1 y hdT _ (by simp) (by simp) (by simp) (by simp)
  have rp1 : L.mem s1 (replyA y) = L.mem s (replyA y) := f1 y hdT _ (by simp) (by simp) (by simp) (by simp)
  have fw1 : Foot st T Cs Sg Scs Z {ep} s s1 := Foot.of w1 fun b hb => hb.kw hq.mem rfl
  have da1 : L.actionW s1 ≠ y := by rw [ea1]; exact da
  have hyA1 : L.mem s1 (scA y) ≠ 0#u64 → L.mem s1 (scA y) ∈ Ac := by
    have esc1 : L.mem s1 (scA y) = L.mem s (scA y) := by
      rw [scA_eq]; exact f1 y hdT _ (by simp) (by simp) (by simp) (by simp)
    rw [esc1]; exact hB.sact y hdT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hbl))))))
  -- the rest of the round, from a state `s2` with a `KW ∅` footprint from `s1`
  have tail : ∀ (s2 : S), Foot st T Cs Sg Scs Z ∅ s1 s2 → CaiFr st T Scs y s s2 →
      endpoint.restart_thread_if_no_fault st s2 y ⦃ s' =>
        ((BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ Foot st T Cs Sg Scs Z ∅ s2 s') ∧ CaiFr st T Scs y s2 s') ∧
          ¬ Blocked (L.mem s' (stA y)) ⦄ →
      (do
        let s3 ← endpoint.restart_thread_if_no_fault st s2 y
        ok (ControlFlow.cont (β := β) (s3, next, fuel1))) ⦃ r => ∃ s3 next', r = .cont (s3, next', fuel1) ∧
          BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s3 ∧ Foot st T Cs Sg Scs Z {ep} s s3 ∧
          (next' ≠ 0#u64 → (L.epState s3 ep = 1#u64 ∨ L.epState s3 ep = 2#u64) ∧ (L.epQ s3 ep).head = next') ∧
          CaiFr st T Scs 0#u64 s s3 ∧ (next' = 0#u64 → L.epState s3 ep = 0#u64) ∧ ¬ Blocked (L.mem s3 (stA y)) ⦄ := by
    intro s2 fw2 F2 hr
    refine WP.spec_bind hr fun s3 ⟨⟨⟨hb3, fw3⟩, F3⟩, hn3⟩ => ?_
    have f13 : Foot st T Cs Sg Scs Z ∅ s1 s3 := fw2.trans fw3
    obtain ⟨eh, et⟩ := f13.epQ h1 hX1.1 hSg1.sub (Or.inl hH)
    have es : L.epState s3 ep = L.epState s1 ep := by simp only [LawfulStore.epState, et]
    refine (WP.spec_ok _).2 ⟨s3, next, rfl, hb3, fw1.trans (f13.mono (Set.empty_subset _)), fun hn0 => ?_,
      (F2.trans hT F3).close hdT (fun _ => hbl) _, fun hn0 => ?_, hn3⟩
    rotate_left
    · rw [es, hst1]
      cases ys with
      | nil => rfl
      | cons z zs =>
        exfalso
        have hz : next = z := by rw [enext, hnext]; rfl
        exact hq1.ne0 hT z (by simp) (hz ▸ hn0)
    have hys0 : ys ≠ [] := fun e => hn0 (by rw [enext, hnext, e]; rfl)
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
      refine tail s2 fw2 (F1.trans hT (CaiFr.of_keepT k2 (Or.inr e2))) (endpoint.restart_thread_if_no_fault.bfD s2 y h2 (fun z hz => ?_) hB2 hX2 hS2 hSg2 hdT
        (Or.inr (by rw [e2]; exact not_blocked_inactive))
        (hX2.noref hta (by rw [e2]; exact inactive_ne.1) (by rw [e2]; exact inactive_ne.2)) hnQ hnR da2
        (by rw [k2.scf hdT]; exact hyA1))
      obtain ⟨hz1, hz2⟩ := hz
      exact absurd (cg1 z hz1) hz2
    · rename_i hi1
      have hz : i1 = 0#u64 := by apply UScalar.eq_of_val_eq; simpa using hi1
      have hi10 : L.mem s1 (replyA y) = 0#u64 := by rw [← ei1]; exact hz
      simp only [Aeneas.Std.bind_ok]
      exact tail s1 (Foot.refl _) F1 (endpoint.restart_thread_if_no_fault.bfD s1 y h1 cg1 hB1 hX1 hS1 hSg1 hdT
        (Or.inl (Or.inr rfl)) (hX1.noref0 hta hi10) hnQ hnR da1 hyA1)
  · rename_i hnrecv
    have hsend : L.mem s1 (stA y) = sched.TS_BLOCKED_ON_SEND := by
      rcases hsr with e | e
      · rw [st1, e]
      · exact absurd (by rw [ei, st1, e]) hnrecv
    have nrp : sched.TS_BLOCKED_ON_SEND ≠ sched.TS_BLOCKED_ON_REPLY := by
      rw [r4]; unfold sched.TS_BLOCKED_ON_REPLY; decide
    have nrc : sched.TS_BLOCKED_ON_SEND ≠ sched.TS_BLOCKED_ON_RECV := by rw [r4, r3]; decide
    simp only [Aeneas.Std.bind_ok]
    exact tail s1 (Foot.refl _) F1 (endpoint.restart_thread_if_no_fault.bfD s1 y h1 cg1 hB1 hX1 hS1 hSg1 hdT
      (Or.inl (Or.inr rfl)) (hX1.noref hta (by rw [hsend]; exact nrp) (by rw [hsend]; exact nrc)) hnQ hnR da1 hyA1)


/-- The loop of `cancel_all_ipc` ends with the endpoint idle. -/
theorem endpoint.cancel_all_ipc_loop.dead (s : S) (ep t fuel : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hH : H ep = some .ep)
    (ht : t ≠ 0#u64 → (L.epState s ep = 1#u64 ∨ L.epState s ep = 2#u64) ∧ (L.epQ s ep).head = t)
    (ht0 : t = 0#u64 → L.epState s ep = 0#u64) (hμ : blkN st T s ≤ fuel.val) :
    endpoint.cancel_all_ipc_loop st s ep t fuel ⦃ s' =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ L.epState s' ep = 0#u64 ⦄ := by
  unfold endpoint.cancel_all_ipc_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.2.val)
    (inv := fun x => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac x.1 ∧
      (x.2.1 ≠ 0#u64 → (L.epState x.1 ep = 1#u64 ∨ L.epState x.1 ep = 2#u64) ∧ (L.epQ x.1 ep).head = x.2.1) ∧
      (x.2.1 = 0#u64 → L.epState x.1 ep = 0#u64) ∧ blkN st T x.1 ≤ x.2.2.val)
  · rintro ⟨s1, t1, f1⟩ ⟨hb1, ht1, hz1, hμ1⟩
    simp only at hb1 ht1 hz1 hμ1
    unfold endpoint.cancel_all_ipc_loop.body
    step with obj.Tcb.is_null.spec as ⟨b, eb⟩
    split
    · rename_i hb
      refine (WP.spec_ok _).2 ⟨hb1, hz1 ?_⟩
      by_contra hne
      have : b = false := by rw [eb]; simpa using hne
      rw [this] at hb; exact absurd hb (by decide)
    rename_i hb
    have ht0 : t1 ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    obtain ⟨hst1, hhd1⟩ := ht1 ht0
    have hbl : t1 ∈ T ∧ Blocked (L.mem s1 (stA t1)) := by
      obtain ⟨⟨Q, R, h0⟩, -⟩ := hb1
      obtain ⟨hdT, -, hs1, hs2⟩ := ep_head h0 hH (w := L.epState s1 ep) hst1 rfl
      rw [hhd1] at hdT hs1 hs2
      refine ⟨hdT, ?_⟩
      rcases hst1 with e | e
      · rw [hs1 e]; exact Or.inl rfl
      · rw [hs2 e]; exact Or.inr (Or.inl rfl)
    split
    · rename_i hfuel
      step as ⟨fuel1, efuel⟩
      refine WP.spec_mono (cai_round.dead (β := S) s1 ep t1 fuel1 hb1 hH hst1 hhd1) ?_
      rintro r ⟨s4, next, rfl, hb4, -, hn4, hF4, hz4, hu4⟩
      have hlt := blkN_lt hF4.blocked hbl.1 ht0 hbl.2 hu4
      exact ⟨hb4, hn4, hz4, by simp only; scalar_tac, by simp only; scalar_tac⟩
    · rename_i hfuel
      exfalso
      have hp := blkN_pos (st := st) hbl.1 ht0 hbl.2
      have : f1.val = 0 := by scalar_tac
      omega
  · exact ⟨h, ht, ht0, hμ⟩


/-- **`cancel_all_ipc` leaves the endpoint idle.** -/
theorem endpoint.cancel_all_ipc.dead (s : S) (ep : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hH : H ep = some .ep) :
    endpoint.cancel_all_ipc st s ep ⦃ s' => L.epState s' ep = 0#u64 ⦄ := by
  unfold endpoint.cancel_all_ipc
  step with obj.Ep.state.spec as ⟨v, hv⟩
  split
  · rename_i hid
    refine (WP.spec_ok _).2 ?_
    rw [← hv, hid]; unfold obj.EP_IDLE; rfl
  rename_i hidle
  have hst : L.epState s ep ≠ 0#u64 := by
    rw [← hv]; intro e; exact hidle (by rw [e]; unfold obj.EP_IDLE; rfl)
  step with endpoint.get_queue.spec as ⟨q, eq⟩
  subst eq
  obtain ⟨⟨Q, R, h0⟩, -⟩ := id h
  have h12 := ep_state12 h0 hH hst
  refine WP.spec_bind (endpoint.cancel_all_ipc_loop.dead s ep _ _ h hH (fun _ => ⟨h12, rfl⟩)
    (fun e => absurd (e ▸ (ep_head h0 hH h12 rfl).1) fun hm => (h0.tcbs _ hm).ne0 (by rfl))
    (by have := blkN_le (st := st) (T := T) s; rw [walk_fuel_val]; omega)) ?_
  rintro s1 ⟨h1, e1⟩
  obtain ⟨⟨Q1, R1, q1⟩, hB1, hX1, hS1, hSg1⟩ := h1
  refine WP.spec_mono (sched.reschedule_required.blk s1 ⟨⟨Q1, R1, q1⟩, hB1, hX1, hS1, hSg1⟩) fun s2 ⟨_, f2⟩ => ?_
  obtain ⟨-, et⟩ := (f2 : Foot st T Cs Sg Scs Z ∅ s1 s2).epQ q1 hX1.1 hSg1.sub (Or.inl hH)
  have : L.epState s2 ep = L.epState s1 ep := by simp only [LawfulStore.epState, et]
  rw [this, e1]

/-- **Endpoint**: a final cap's `finalise_cap` leaves the endpoint idle. -/
theorem fin_cap_ep.dead {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (ep : U64) (b0 b1 b2 b3 b4 : _)
    (ex : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hH : H ep = some .ep) :
    objects.finalise_cap st ar s a (.Endpoint ep b0 b1 b2 b3 b4) true ex ⦃ r => L.epState r.2.1 ep = 0#u64 ⦄ := by
  rw [fin_cap_eq_obj (by simp)]
  unfold objects.finalise_cap_object
  dsimp only
  simp only [ite_true]
  exact WP.spec_bind (endpoint.cancel_all_ipc.dead s ep h hH) fun s1 e1 => (WP.spec_ok _).2 e1


/-! ## Notifications -/

/-- The notifications' `BOUND_TCB` and `SC` words are kept. -/
def NtKeep (st : machine.Store S) [L : LawfulStore st] (Nt : Set U64) (s s' : S) : Prop :=
  ∀ n ∈ Nt, L.mem s' (ntfnBtA n) = L.mem s (ntfnBtA n) ∧ L.mem s' (ntfnScA n) = L.mem s (ntfnScA n)

theorem NtKeep.refl (s : S) : NtKeep st Nt s s := fun _ _ => ⟨rfl, rfl⟩
theorem NtKeep.trans {s₁ s₂ s₃ : S} (h₁ : NtKeep st Nt s₁ s₂) (h₂ : NtKeep st Nt s₂ s₃) : NtKeep st Nt s₁ s₃ :=
  fun n hn => ⟨(h₂ n hn).1.trans (h₁ n hn).1, (h₂ n hn).2.trans (h₁ n hn).2⟩

theorem NtKeep.of_omega {s s' : S} (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (h : ∀ a ∈ Ω, L.mem s' a = L.mem s a) : NtKeep st Nt s s' :=
  fun n hn => ⟨h _ (hsub _ (hO.ntB n hn).2), h _ (hsub _ (hO.ntW n hn))⟩

theorem NtKeep.of_sig {s s' : S} (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (h : ∀ a ∈ Sg, L.mem s' a = L.mem s a) :
    NtKeep st Nt s s' :=
  fun n hn => ⟨h _ (hO.ntB n hn).2, h _ (hO.ntW n hn)⟩

section q
variable {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}

/-- `notification.unblock_sporadic` writes only an SC's refills and the
`REPROGRAM` word: the notifications' words are kept. -/
theorem notification.unblock_sporadic.ntw (s : S) (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R)
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hS : SCsOK st T Ω Sg Scs Z Ac s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (ht : t ∈ T) :
    notification.unblock_sporadic st s t ⦃ s' => NtKeep st Nt s s' ⦄ := by
  unfold notification.unblock_sporadic
  step with obj.Tcb.sc.spec as ⟨i, i_post⟩
  step with sporadic.sc_sporadic.spec as ⟨b1, b1_post⟩
  split
  · rename_i hb1
    obtain ⟨hi0, hsp⟩ := b1_post hb1
    have hbt : L.mem s (scA t) ≠ 0#u64 := by rw [← i_post]; exact hi0
    obtain ⟨hiS, -, -⟩ := hX.2.2.bound t ht hbt
    rw [← i_post] at hiS
    have hW : RefillsWF st s i (Z i) := hS.wf hiS (hS.spor i hiS hsp)
    have hSCin : SCin st s Ω i (Z i) := ⟨hW, hX.1.scW i hiS⟩
    step with sched.cur_sc.spec as ⟨c4, _⟩
    step with sc_ne.spec as ⟨b2⟩
    split
    · have hN' := h.nodes _ h.cur
      have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
      have aR : Aligned (L.nodeA s layout.node.REPROGRAM) := nodeAt_aligned hN' (by rw [rp]; omega) (by rw [rp])
      have oR : Outside (L.nodeA s layout.node.REPROGRAM) i (Z i) :=
        hSCin.node_out h.omega h.cur hN' (by rw [rp]; omega) (by rw [rp])
      refine WP.spec_mono (sporadic.unblock_check.fr hW ⟨aR, oR⟩) fun s3 w3 n hn => ?_
      have hO := hX.1
      have hP := hO.ntP n hn
      have dj := hO.ntOSc n hn i hiS
      have key : ∀ a ∈ Ω, (a.val = n.val + 24 ∨ a.val = n.val + 32) → L.mem s3 a = L.mem s a := by
        intro a ha hv
        refine w3.mem_eq (h.omega _ ha).1 ?_
        rintro (⟨h1, h2⟩ | e)
        · omega
        · exact out_ne_node (h.omega _ ha) h.cur hN' (o := layout.node.REPROGRAM) (by rw [rp]; omega)
            (by rw [e]; rfl)
      exact ⟨key _ (hsub _ (hO.ntB n hn).2) (Or.inl (ntfnBtA_val hP)),
        key _ (hsub _ (hO.ntW n hn)) (Or.inr (ntfnScA_val hP))⟩
    · exact (WP.spec_ok _).2 (NtKeep.refl _)
  · exact (WP.spec_ok _).2 (NtKeep.refl _)

end q

/-- `maybe_unbind_ntfn` leaves the notification's `SC` word null. -/
theorem schedcontext.maybe_unbind_ntfn.dead (s : S) (n : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hn : n ∈ Nt) :
    schedcontext.maybe_unbind_ntfn st s n ⦃ s' => L.mem s' (ntfnScA n) = 0#u64 ⦄ := by
  have hn0 : n ≠ 0#u64 := h.2.2.1.1.nt0 n hn
  unfold schedcontext.maybe_unbind_ntfn
  step with obj.Ntfn.sc.val as ⟨i, ei⟩
  step with obj.Sc.is_null.spec as ⟨b, eb⟩
  split
  · rename_i hb
    refine (WP.spec_ok _).2 ?_
    rw [← ei]; rw [eb] at hb; simpa using hb
  rename_i hb
  have hi0 : i ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
  have hX := h.2.2.1
  have hO := hX.1
  have h0 := h.1.choose_spec.choose_spec
  obtain ⟨hiS, hback⟩ := hX.2.2.nsc n hn (by rw [← ei]; exact hi0)
  rw [← ei] at hiS hback
  unfold schedcontext.unbind_ntfn
  step with obj.Sc.is_null.spec as ⟨b', eb'⟩
  split
  · rename_i hb'
    exfalso; rw [eb'] at hb'; exact hi0 (by simpa using hb')
  step with obj.Sc.ntfn.val as ⟨j, ej⟩
  rw [hback] at ej
  subst ej
  split
  · refine WP.spec_bind (obj.Ntfn.set_sc.wr s j 0#u64) fun s1 e1 => ?_
    subst e1
    refine WP.spec_mono (obj.Sc.set_ntfn.wr _ i 0#u64) fun s2 e2 => ?_
    subst e2
    obtain ⟨hP, hz⟩ := hO.sc i hiS
    obtain ⟨h128, -⟩ := sc_facts hO hiS
    have hm : scNtfnA i ∈ Ω := h.2.2.2.2.sub _ (hO.snW i hiS)
    have dj := hO.ntOSc j hn i hiS
    rw [L.mem_wr_ne (h0.omega _ hm).1 (hO.ntAl j hn) (by
      rw [scNtfnA_val hP hz, ntfnScA_val (hO.ntP j hn)]; omega)]
    exact L.mem_wr_same (hO.ntAl j hn)
  · rename_i hj
    exfalso; exact hn0 (UScalar.eq_of_val_eq (by simpa using hj))

/-- `unbind_maybe_notification` leaves the notification's `BOUND_TCB` word
null and keeps its `SC` word. -/
theorem notification.unbind_maybe_notification.dead (s : S) (n : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hn : n ∈ Nt) :
    notification.unbind_maybe_notification st s n ⦃ s' =>
      L.mem s' (ntfnBtA n) = 0#u64 ∧ L.mem s' (ntfnScA n) = L.mem s (ntfnScA n) ⦄ := by
  unfold notification.unbind_maybe_notification
  refine WP.spec_bind (obj.Ntfn.bound_tcb.val s n) fun i ei => ?_
  refine WP.spec_bind (obj.Tcb.is_null.spec i) fun b eb => ?_
  subst eb
  split
  · rename_i hb
    exact (WP.spec_ok _).2 ⟨by rw [← ei]; simpa using hb, rfl⟩
  · rename_i hb
    have hiT : i ∈ T := by
      rcases (show Tz T i by rw [ei]; exact h.2.2.1.2.2.ntb n hn) with e | e
      · exact absurd (by simp [e]) hb
      · exact e
    have hO := h.2.2.1.1
    have h0 := h.1.choose_spec.choose_spec
    have hT := h0.tcbs
    have hmB : ntfnBtA n ∈ Ω := h.2.2.2.2.sub _ (hO.ntB n hn).2
    have hmS : ntfnScA n ∈ Ω := h.2.2.2.2.sub _ (hO.ntW n hn)
    have hP := hO.ntP n hn
    refine WP.spec_bind (obj.Ntfn.set_bound_tcb.wr s n 0#u64) fun s1 e1 => ?_
    subst e1
    refine WP.spec_mono (obj.Tcb.set_bound_ntfn.wr _ i 0#u64) fun s2 e2 => ?_
    subst e2
    have fa : Aligned (boundA i) := field_aligned (hT i hiT) (K := 3368#u64) (by simp) (by simp)
    refine ⟨?_, ?_⟩
    · rw [L.mem_wr_ne fa (h0.omega _ hmB).1 (out_ne_field (h0.omega _ hmB) hiT (hT i hiT) (K := 3368#u64) (by simp))]
      exact L.mem_wr_same (h0.omega _ hmB).1
    · rw [L.mem_wr_ne fa (h0.omega _ hmS).1 (out_ne_field (h0.omega _ hmS) hiT (hT i hiT) (K := 3368#u64) (by simp)),
        L.mem_wr_ne (h0.omega _ hmB).1 (h0.omega _ hmS).1 (by rw [ntfnBtA_val hP, ntfnScA_val hP]; omega)]

/-- `cas_round`, with the notifications' words kept, the other threads'
states kept, the head left `Restart`, and the notification idle once the
queue is empty. -/
theorem cas_round.dead {β : Type _} (s : S) (n t : U64) (fuel1 : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hH : H n = some .ntfn) (hst : L.epState s n = 1#u64) (hhd : (L.epQ s n).head = t) :
    (do
      let next ← tcbqueue.next_of st s .Ep t
      let s1 ← notification.ntfn_dequeue st s n t
      let s2 ← sched.set_thread_state st s1 t sched.TS_RESTART
      let s3 ← notification.unblock_sporadic st s2 t
      let s4 ← sched.possible_switch_to st s3 t
      ok (ControlFlow.cont (β := β) (s4, next, fuel1))) ⦃ r => ∃ s4 next, r = .cont (s4, next, fuel1) ∧
        BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s4 ∧ Foot st T Cs Sg Scs Z {n} s s4 ∧
        (next ≠ 0#u64 → L.epState s4 n = 1#u64 ∧ (L.epQ s4 n).head = next) ∧
        (next = 0#u64 → L.epState s4 n = 0#u64) ∧ NtKeep st Nt s s4 ∧
        (∀ z ∈ T, z ≠ t → L.mem s4 (stA z) = L.mem s (stA z)) ∧ L.mem s4 (stA t) = sched.TS_RESTART ⦄ := by
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
    (WP.spec_and (notification.unblock_sporadic.kw (Es := ∅) s2 y h2' hX2 hS2 hdT)
      (notification.unblock_sporadic.ntw s2 y h2' hX2 hS2 hSg2.sub hdT))) ?_
  rintro s3 ⟨⟨h3, hB3, hX3, hS3, hSg3, -, -, -, fk3, -⟩, fw3, nk3⟩
  have st3 : L.mem s3 (stA y) = sched.TS_RESTART := by
    rw [stA_eq, fk3 y hdT _ (by simp) (by simp), ← stA_eq]; exact st2
  have esc3 : L.mem s3 (scA y) = L.mem s (scA y) := by
    rw [scA_eq, fk3 y hdT _ (by simp) (by simp), ← scA_eq, k2.scf hdT, scA_eq,
      f1 y hdT _ (by simp) (by simp) (by simp) (by simp)]
  refine WP.spec_bind (WP.spec_and (sched.possible_switch_to.sch (Sg := Sg) s3 y Q R h3 hB3 hSg3 hdT
    (by rw [st3]; exact runnable_restart) (by rw [esc3]; exact hyA))
    (sched.possible_switch_to.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) s3 y h3 hdT)) ?_
  rintro s4 ⟨⟨p4, -, -⟩, fw4⟩
  have f14 : Foot st T Cs Sg Scs Z ∅ s1 s4 := fw2.trans (fw3.trans fw4)
  obtain ⟨eh, et⟩ := f14.epQ h1 hX1.1 hSg1.sub (Or.inr hH)
  have es : L.epState s4 n = L.epState s1 n := by simp only [LawfulStore.epState, et]
  have nk : NtKeep st Nt s s4 :=
    ((NtKeep.of_omega hX.1 hSg.sub o1).trans (fun n' hn' => ⟨k2.ntb n' hn', k2.nsc n' hn'⟩)).trans
      (nk3.trans (NtKeep.of_sig hX3.1 p4.fr.sig))
  have hzs : ∀ z ∈ T, z ≠ y → L.mem s4 (stA z) = L.mem s (stA z) := by
    intro z hz hzy
    rw [p4.fr.st z hz, stA_eq, fk3 z hz _ (by simp) (by simp),
      k2.fld z hz _ (by simp) (by simp) (by simp) (by simp) (fun e => absurd e hzy),
      f1 z hz _ (by simp) (by simp) (by simp) (by simp)]
  refine (WP.spec_ok _).2 ⟨s4, next, rfl, ⟨p4.inv, p4.bnd, hX3.fr p4.fr, hS3.fr p4.fr, hSg3.fr p4.fr⟩,
    fw1.trans (f14.mono (Set.empty_subset _)), fun hn0 => ?_, fun hn0 => ?_, nk, hzs, by rw [p4.fr.st y hdT]; exact st3⟩
  rotate_left
  · rw [es, hst1]
    cases ys with
    | nil => rfl
    | cons z zs =>
      exfalso
      have hz : next = z := by rw [enext, hnext]; rfl
      exact hq1.ne0 hT z (by simp) (hz ▸ hn0)
  have hys0 : ys ≠ [] := fun e => hn0 (by rw [enext, hnext, e]; rfl)
  refine ⟨by rw [es, hst1, if_neg hys0, hst], ?_⟩
  rw [show (L.epQ s4 n).head = L.mem s4 (epHeadA n) from rfl, eh, show L.mem s1 (epHeadA n) = (L.epQ s1 n).head
    from rfl, hq1.head, enext, hnext]


theorem notification.cancel_all_signals_loop.dead (s0 s : S) (n t fuel : U64)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hH : H n = some .ntfn) (hk : NtKeep st Nt s0 s)
    (ht : t ≠ 0#u64 → L.epState s n = 1#u64 ∧ (L.epQ s n).head = t)
    (ht0 : t = 0#u64 → L.epState s n = 0#u64) (hμ : blkN st T s ≤ fuel.val) :
    notification.cancel_all_signals_loop st s n t fuel ⦃ s' =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ NtKeep st Nt s0 s' ∧ L.epState s' n = 0#u64 ⦄ := by
  unfold notification.cancel_all_signals_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.2.val)
    (inv := fun x => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac x.1 ∧ NtKeep st Nt s0 x.1 ∧
      (x.2.1 ≠ 0#u64 → L.epState x.1 n = 1#u64 ∧ (L.epQ x.1 n).head = x.2.1) ∧
      (x.2.1 = 0#u64 → L.epState x.1 n = 0#u64) ∧ blkN st T x.1 ≤ x.2.2.val)
  · rintro ⟨s1, t1, f1⟩ ⟨hb1, hk1, ht1, hz1, hμ1⟩
    simp only at hb1 hk1 ht1 hz1 hμ1
    unfold notification.cancel_all_signals_loop.body
    step with obj.Tcb.is_null.spec as ⟨b, eb⟩
    split
    · rename_i hb
      refine (WP.spec_ok _).2 ⟨hb1, hk1, hz1 ?_⟩
      rw [eb] at hb; simpa using hb
    rename_i hb
    have ht0 : t1 ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    obtain ⟨hst1, hhd1⟩ := ht1 ht0
    have hbl : t1 ∈ T ∧ Blocked (L.mem s1 (stA t1)) := by
      obtain ⟨⟨Q, R, h0⟩, -⟩ := hb1
      obtain ⟨hdT, -, hds⟩ := ntfn_head h0 hH hst1
      rw [hhd1] at hdT hds
      exact ⟨hdT, by rw [hds]; exact Or.inr (Or.inr rfl)⟩
    split
    · rename_i hfuel
      step as ⟨fuel1, efuel⟩
      refine WP.spec_mono (cas_round.dead (β := S) s1 n t1 fuel1 hb1 hH hst1 hhd1) ?_
      rintro r ⟨s4, next, rfl, hb4, -, hn4, hz4, hk4, hzs, hy4⟩
      have hmono : ∀ z ∈ T, Blocked (L.mem s4 (stA z)) → Blocked (L.mem s1 (stA z)) := by
        intro z hz hbz
        by_cases e : z = t1
        · subst e; rw [hy4] at hbz; exact absurd hbz not_blocked_restart
        · rwa [← hzs z hz e]
      have hlt := blkN_lt hmono hbl.1 ht0 hbl.2 (by rw [hy4]; exact not_blocked_restart)
      exact ⟨hb4, hk1.trans hk4, hn4, hz4, by simp only; scalar_tac, by simp only; scalar_tac⟩
    · rename_i hfuel
      exfalso
      have hp := blkN_pos (st := st) hbl.1 ht0 hbl.2
      have : f1.val = 0 := by scalar_tac
      omega
  · exact ⟨h, hk, ht, ht0, hμ⟩

/-- **`cancel_all_signals` leaves the notification not waiting**, and keeps
the notifications' `BOUND_TCB` and `SC` words. -/
theorem notification.cancel_all_signals.dead (s : S) (n : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hH : H n = some .ntfn) :
    notification.cancel_all_signals st s n ⦃ s' => L.epState s' n ≠ 1#u64 ∧ NtKeep st Nt s s' ⦄ := by
  unfold notification.cancel_all_signals
  step with obj.Ntfn.state.spec as ⟨v, hv⟩
  split
  · rename_i hw
    refine (WP.spec_ok _).2 ⟨?_, NtKeep.refl _⟩
    rw [← hv]; intro e; simp [e, obj.NTFN_WAITING] at hw
  rename_i hw
  have hst : L.epState s n = 1#u64 := by
    rw [← hv]; have := hw; simp [obj.NTFN_WAITING] at this; exact UScalar.eq_of_val_eq (by simpa using this)
  step with notification.get_queue.spec as ⟨q, eq⟩
  subst eq
  obtain ⟨⟨Q, R, h0⟩, -⟩ := id h
  refine WP.spec_bind (notification.cancel_all_signals_loop.dead s s n _ _ h hH (NtKeep.refl _)
    (fun _ => ⟨hst, rfl⟩)
    (fun e => absurd (e ▸ (ntfn_head h0 hH hst).1) fun hm => (h0.tcbs _ hm).ne0 (by rfl))
    (by have := blkN_le (st := st) (T := T) s; rw [walk_fuel_val]; omega)) ?_
  rintro s1 ⟨h1, k1, e1⟩
  obtain ⟨⟨Q1, R1, q1⟩, hB1, hX1, hS1, hSg1⟩ := h1
  refine WP.spec_mono (WP.spec_and (sched.reschedule_required.blk s1 ⟨⟨Q1, R1, q1⟩, hB1, hX1, hS1, hSg1⟩)
    (sched.reschedule_required.schX s1 Q1 R1 q1 hB1 hSg1)) fun s2 ⟨⟨_, f2⟩, _, _, p2, _⟩ => ?_
  obtain ⟨-, et⟩ := (f2 : Foot st T Cs Sg Scs Z ∅ s1 s2).epQ q1 hX1.1 hSg1.sub (Or.inr hH)
  have : L.epState s2 n = L.epState s1 n := by simp only [LawfulStore.epState, et]
  refine ⟨by rw [this, e1]; decide, k1.trans (NtKeep.of_sig hX1.1 p2.sig)⟩

/-- **Notification**: a final cap's `finalise_cap` leaves the notification
unbound (null `BOUND_TCB` and `SC` words) and not waiting. -/
theorem fin_cap_ntfn.dead {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (n : U64) (b0 b1 b2 : _)
    (ex : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hn : n ∈ Nt) (hH : H n = some .ntfn) :
    objects.finalise_cap st ar s a (.Notification n b0 b1 b2) true ex ⦃ r =>
      L.epState r.2.1 n ≠ 1#u64 ∧ L.mem r.2.1 (ntfnBtA n) = 0#u64 ∧ L.mem r.2.1 (ntfnScA n) = 0#u64 ⦄ := by
  rw [fin_cap_eq_obj (by simp)]
  unfold objects.finalise_cap_object
  dsimp only
  simp only [ite_true]
  refine WP.spec_bind (WP.spec_and (schedcontext.maybe_unbind_ntfn.blk s n h hn)
    (schedcontext.maybe_unbind_ntfn.dead s n h hn)) fun s1 ⟨⟨h1, _⟩, e1⟩ => ?_
  refine WP.spec_bind (WP.spec_and (notification.unbind_maybe_notification.blkF s1 n h1 hn)
    (notification.unbind_maybe_notification.dead s1 n h1 hn)) fun s2 ⟨⟨h2, _⟩, e2, e2'⟩ => ?_
  refine WP.spec_bind (notification.cancel_all_signals.dead s2 n h2 hH) fun s3 ⟨e3, k3⟩ => ?_
  exact (WP.spec_ok _).2 ⟨e3, by rw [(k3 n hn).1, e2], by rw [(k3 n hn).2, e2', e1]⟩

/-! ## Replies -/

section rp
variable {Es : Set U64}

/-- `ipc.reply_pop.blk`, with the reply's `TCB` word cleared. -/
theorem ipc.reply_pop.blkZ {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (r t : U64)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hr : r ∈ Rp) (ht : t ∈ T) (hrt : L.mem s (rTcbA r) = t)
    (hst : L.mem s (stA t) = sched.TS_BLOCKED_ON_REPLY)
    (hb : headBit (L.mem s (rNextA r)) = true) (hn0 : L.mem s (rNextA r) &&& ~~~1#u64 ≠ 0#u64) :
    ipc.reply_pop st ar s a r t ⦃ res => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac res.1 ∧
      L.mem res.1 (stA t) = sched.TS_INACTIVE ∧ Foot st T Cs Sg Scs Z Es s res.1 ∧ L.mem res.1 (rTcbA r) = 0#u64 ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hO := hX.1
  have hsub := hSg.sub
  obtain ⟨hrΩ, hcΩ⟩ := objs_omega hO hsub
  have rr : ∀ r' ∈ Rp, r'.val % 32 = 0 := fun r' hr' => (hO.rp r' hr').1
  obtain ⟨-, -, rp8, rn16⟩ := rp_facts hO hr
  obtain ⟨c, hc⟩ : ∃ c, L.mem s (rNextA r) &&& ~~~1#u64 = c := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p, L.mem s (rPrevA r) &&& ~~~1#u64 = p := ⟨_, rfl⟩
  rw [hc] at hn0
  have hcS : c ∈ Scs := by rw [← hc]; exact (hX.2.1.next r hr (by rw [hc]; exact hn0)).1 hb
  have hcr : L.mem s (scReplyA c) = r := by rw [← hc]; exact hX.2.1.head r hr hb (by rw [hc]; exact hn0)
  have hcA : c ∈ Ac := hS.rep c hcS (by rw [hcr]; exact hO.rp0 r hr)
  have hci : L.mem s (scTcbA c) ≠ L.idleW s := fun e => hO.rp0 r hr (hcr.symm.trans (hX.2.1.idle c hcS e))
  have hpR : p ≠ 0#u64 → p ∈ Rp := fun h0' => by rw [← hp]; exact hX.2.1.prev r hr (by rw [hp]; exact h0')
  have ht0 : t ≠ 0#u64 := fun e0 => (h0.tcbs t ht).ne0 (by rw [e0]; rfl)
  have hrp : L.mem s (replyA t) = r := by
    obtain ⟨-, -, b2, -⟩ := hX.2.1.back r hr (by rw [hrt]; exact ht0)
    rw [hrt] at b2; exact b2
  have hscR : (scReplyA c).val = c.val + 32 := (sc_facts hO hcS).2.2.2.2.2.2.1
  have hscT : (scTcbA c).val = c.val + 24 := (sc_facts hO hcS).2.1
  have hcm : scReplyA c ∈ Ω := hsub _ (hO.repW c hcS)
  have hal : ∀ b ∈ Ω, Aligned b := fun b hb => (h0.omega b hb).1
  unfold ipc.reply_pop
  step with obj.Reply.next.spec as ⟨nx, enx⟩
  step with obj.Reply.prev.spec as ⟨pv, epv⟩
  refine WP.spec_bind (obj.Reply.next_raw.val s r) fun raw eraw => ?_
  rw [hc] at enx; rw [hp] at epv
  subst nx pv raw
  step with obj.Sc.set_reply.spec as ⟨s1, e1⟩
  subst e1
  obtain ⟨h1, hB1, hX1, hS1, hSg1, a1, i1, f1, o1⟩ :=
    screp_wrR (w := p) h0 hB hX.xr hS hSg hcS (fun hp0 => ⟨hpR hp0, hcA, hci⟩)
  have G1 : Foot st T Cs Sg Scs Z Es s (L.wr s (scReplyA c) p) := foot_sgw (hal _ hcm) (hO.repW c hcS)
  -- the new head takes `r`'s `NEXT` word
  refine WP.spec_bind (Pₘ := fun s2 => SchedQueuesInv st T Cs Ω H s2 Q R ∧ BoundInv st T Ac s2 ∧
      XInvR st T Cs Ω Sg Rp Scs Nt Z s2 ∧ SCsOK st T Ω Sg Scs Z Ac s2 ∧ SgOK st Ω Sg s2 ∧
      L.actionW s2 = L.actionW s ∧ L.idleW s2 = L.idleW s ∧
      (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
        L.mem s2 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ b ∈ Ω, (scReplyA c).val ≠ b.val → (p ≠ 0#u64 → (rNextA p).val ≠ b.val) → L.mem s2 b = L.mem s b) ∧
      L.mem s2 (scReplyA c) = p ∧ (p ≠ 0#u64 → L.mem s2 (rNextA p) = L.mem s (rNextA r)) ∧
      Foot st T Cs Sg Scs Z Es s s2) ?_ ?_
  · split
    · rename_i hp0
      have hp0' : p ≠ 0#u64 := by simpa using hp0
      have hpR' := hpR hp0'
      refine WP.spec_mono (obj.Reply.set_next_raw.val _ p _) fun s2 e2 => ?_
      subst e2
      obtain ⟨-, -, pp8, pn16⟩ := rp_facts hO hpR'
      obtain ⟨h2, hB2, hX2, hS2, hSg2, a2, i2, f2, o2⟩ := rword_wrR (w := L.mem s (rNextA r)) h1 hB1 hX1 hS1 hSg1
        hpR' (Or.inr rfl) (fun _ h0' => hX.2.1.next r hr h0')
        (fun e => absurd (congrArg UScalar.val e) (by rw [pp8, pn16]; omega))
      have hpn : (rNextA p).val ≠ (scReplyA c).val := rword_ne_screp hO hpR' (by omega) c hcS
      refine ⟨h2, hB2, hX2, hS2, hSg2, a2.trans a1, i2.trans i1, fun y hy K h1' h2' => (f2 y hy K h1' h2').trans
        (f1 y hy K h1' h2'), fun b hb n1 n2 => (o2 b hb (n2 hp0')).trans (o1 b hb n1), ?_,
        fun _ => L.mem_wr_same (hal _ (hrΩ p hpR').2.2), G1.trans (foot_sgw (hal _ (hrΩ p hpR').2.2) (hO.nextW hpR'))⟩
      rw [o2 _ hcm hpn]; exact L.mem_wr_same (hal _ hcm)
    · rename_i hp0
      have hp0' : p = 0#u64 := UScalar.eq_of_val_eq (by simpa using hp0)
      exact (WP.spec_ok _).2 ⟨h1, hB1, hX1, hS1, hSg1, a1, i1, f1, fun b hb n1 _ => o1 b hb n1,
        L.mem_wr_same (hal _ hcm), fun h' => absurd hp0' h', G1⟩
  intro s2 ⟨h2, hB2, hX2, hS2, hSg2, a2, i2, f2, o2, r2, n2, G2⟩
  -- `r`'s `NEXT` word is cleared: `RHead` again
  refine WP.spec_bind (obj.Reply.set_next.val0 s2 r 0#u64) fun s3 e3 => ?_
  rw [zero_link] at e3
  subst e3
  obtain ⟨h3, hB3, hX3, hS3, hSg3, a3, i3, f3, o3⟩ := rword_wrR (w := 0#u64) h2 hB2 hX2 hS2 hSg2 hr (Or.inr rfl)
    (fun _ h0' => absurd zero_or_masked h0') (fun e => by
      exfalso; have h' := congrArg (fun x : U64 => x.val) e; rw [rp8, rn16] at h'; omega)
  have hd : RHead st Rp (L.wr s2 (rNextA r) 0#u64) := by
    intro r' hr' hb' h0'
    by_cases e : r' = r
    · subst e; rw [L.mem_wr_same (hal _ (hrΩ r' hr').2.2)] at h0'; exact absurd zero_or_masked h0'
    have nrr : (rNextA r).val ≠ (rNextA r').val := by
      rw [rn16, rNextA_val (hO.rp r' hr')]; have := rr r' hr'; have := rr r hr
      have : r.val ≠ r'.val := fun e' => e (UScalar.eq_of_val_eq e').symm
      omega
    rw [o3 _ (hrΩ r' hr').2.2 nrr] at hb' h0' ⊢
    by_cases ep : p ≠ 0#u64 ∧ r' = p
    · obtain ⟨hp0, rfl⟩ := ep
      rw [n2 hp0] at hb' h0' ⊢
      rw [hc, o3 _ hcm (rword_ne_screp hO hr (by omega) c hcS), r2]
    · have e2 : L.mem s2 (rNextA r') = L.mem s (rNextA r') := o2 _ (hrΩ r' hr').2.2
        (fun e' => rword_ne_screp hO hr' (by rw [rNextA_val (hO.rp r' hr')]; omega) c hcS e'.symm)
        (fun hp0 e' => ep ⟨hp0, by
          apply UScalar.eq_of_val_eq
          rw [rNextA_val (hO.rp p (hpR hp0)), rNextA_val (hO.rp r' hr')] at e'
          have := rr r' hr'; have := rr p (hpR hp0); omega⟩)
      rw [e2] at hb' h0' ⊢
      have hc'S := (hX.2.1.next r' hr' h0').1 hb'
      have hhd := hX.2.1.head r' hr' hb' h0'
      have hne : L.mem s (rNextA r') &&& ~~~1#u64 ≠ c := fun e' => by rw [e', hcr] at hhd; exact e hhd.symm
      have hsc' := (sc_facts hO hc'S).2.2.2.2.2.2.1
      have nsc : (scReplyA c).val ≠ (scReplyA (L.mem s (rNextA r') &&& ~~~1#u64)).val := by
        rw [hscR, hsc']
        have := hO.scDisj c hcS _ hc'S (Ne.symm hne); have := (sc_facts hO hc'S).1; have := (sc_facts hO hcS).1
        omega
      have hm' := hsub _ (hO.repW _ hc'S)
      rw [o3 _ hm' (rword_ne_screp hO hr (by omega) _ hc'S), o2 _ hm' nsc
        (fun hp0 => rword_ne_screp hO (hpR hp0) (by rw [rNextA_val (hO.rp p (hpR hp0))]; omega) _ hc'S)]
      exact hhd
  have hX3' := hX3.x hd
  have G3 : Foot st T Cs Sg Scs Z Es s (L.wr s2 (rNextA r) 0#u64) :=
    G2.trans (foot_sgw (hal _ (hrΩ r hr).2.2) (hO.nextW hr))
  -- facts at `s3`
  have F3 : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem (L.wr s2 (rNextA r) 0#u64) (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y hy K h1' h2' => (f3 y hy K h1' h2').trans (f2 y hy K h1' h2')
  have hst3 : L.mem (L.wr s2 (rNextA r) 0#u64) (stA t) = sched.TS_BLOCKED_ON_REPLY := by
    rw [stA_eq, F3 t ht _ (by simp) (by simp), ← stA_eq]; exact hst
  have hrp3 : L.mem (L.wr s2 (rNextA r) 0#u64) (replyA t) = r := by
    exact (F3 t ht 3360#u64 (by simp) (by simp)).trans hrp
  have tc3 : L.mem (L.wr s2 (rNextA r) 0#u64) (scTcbA c) = L.mem s (scTcbA c) := by
    have hm := (hcΩ c hcS).1
    rw [o3 _ hm (rword_ne_sc hO hr (by omega) c hcS).1, o2 _ hm (by rw [hscR, hscT]; omega)
      (fun hp0 => (rword_ne_sc hO (hpR hp0) (by rw [rNextA_val (hO.rp p (hpR hp0))]; omega) c hcS).1)]
  -- the donation back to `t`
  step with obj.Tcb.sc.spec as ⟨i, ei⟩
  have hk3 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s2 (rNextA r) 0#u64) := ⟨⟨Q, R, h3⟩, hB3, hX3', hS3, hSg3⟩
  refine WP.spec_bind (Pₘ := fun res : S × A => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac res.1 ∧
      L.mem res.1 (stA t) = sched.TS_BLOCKED_ON_REPLY ∧ L.mem res.1 (replyA t) = r ∧
      Foot st T Cs Sg Scs Z Es (L.wr s2 (rNextA r) 0#u64) res.1) ?_ ?_
  · split
    · rename_i hi0
      have hsc0 : L.mem (L.wr s2 (rNextA r) 0#u64) (scA t) = 0#u64 := by rw [← ei]; exact hi0
      obtain ⟨dq, dr, da⟩ := blocked_out h3 ht (by rw [hst3]; exact not_runnable_reply)
      by_cases hf0 : L.mem (L.wr s2 (rNextA r) 0#u64) (scTcbA c) = 0#u64
      · refine WP.spec_mono (WP.spec_and (schedcontext.donate.unbound hA (X := ∅) _ a c t Q R h3 hB3 hX3' hS3 hSg3 ht dq dr
          hcS hn0 hf0 (hX3'.2.2.core c hcS) (fun _ => hcA) hsc0
          (fun e => hB3.idleNB (by rw [e, hst3]; exact Or.inr rfl)))
          (schedcontext.donate.kw (Es := Es) hA _ a c t hk3 hcS ht)) ?_
        rintro ⟨s4, a4⟩ ⟨⟨hk, st4, rp4, -, -⟩, fk⟩
        exact ⟨hk, by rw [st4 t ht]; exact hst3, by rw [rp4 t ht]; exact hrp3, fk⟩
      · have hfT := hX3'.2.2.yt.1 c hcS hf0
        have hscf := hX3'.2.2.tsc c hcS hn0 hf0
        refine WP.spec_mono (WP.spec_and (schedcontext.donate.gen hA _ a c t _ Q R h3 hB3 hX3' hS3 hSg3 hfT hscf hn0
          ?_ ht hsc0 dq dr da ?_ hcA (fun e => hB3.idleNB (by rw [e, hst3]; exact Or.inr rfl)))
          (schedcontext.donate.kw (Es := Es) hA _ a c t hk3 hcS ht)) ?_
        · rw [i3, i2, tc3]; exact fun e => hci e.symm
        · intro e; rw [← e, hsc0] at hscf; exact hn0 hscf.symm
        · rintro ⟨s4, a4⟩ ⟨⟨hk, st4, rp4, -⟩, fk⟩
          exact ⟨hk, by rw [st4 t ht]; exact hst3, by rw [rp4 t ht]; exact hrp3, fk⟩
    · exact (WP.spec_ok _).2 ⟨hk3, hst3, hrp3, Foot.refl _⟩
  rintro ⟨s4, a4⟩ ⟨hk4, st4, rp4, G4⟩
  dsimp only at hk4 st4 rp4 G4 ⊢
  refine WP.spec_bind (obj.Reply.set_prev.val s4 r 0#u64) fun s5 e5 => ?_
  rw [zero_or_masked] at e5
  subst e5
  obtain ⟨hk5, -, -, f5, -⟩ := rprev_wr_all hk4 hr (fun h0' => absurd zero_or_masked h0')
  have hst5 : L.mem (L.wr s4 (rPrevA r) 0#u64) (stA t) = sched.TS_BLOCKED_ON_REPLY := by
    rw [stA_eq, f5 t ht _ (by simp) (by simp), ← stA_eq]; exact st4
  have hrp5 : L.mem (L.wr s4 (rPrevA r) 0#u64) (replyA t) = r := by
    exact (f5 t ht 3360#u64 (by simp) (by simp)).trans rp4
  have hrt5 := (hk5.2.2.1.2.1.reply t ht hst5).2
  rw [hrp5] at hrt5
  have G5 : Foot st T Cs Sg Scs Z Es s4 (L.wr s4 (rPrevA r) 0#u64) :=
    foot_sgw (hal _ (hrΩ r hr).2.1) (hO.prevW hr)
  refine WP.spec_bind (ipc.reply_unlink.blk (Es := Es) _ r t hk5 hr ht hrt5 hst5) ?_
  rintro s6 ⟨h6, e6, -, z6, G6⟩
  exact (WP.spec_ok _).2 ⟨h6, e6, G3.trans (G4.trans (G5.trans G6)), z6⟩

/-- seL4 `reply_remove`: a stack head is popped (`reply_pop`); otherwise the
reply leaves the middle of its stack (its neighbours' links to it are
cleared) or is on no stack.  Then `t` (blocked on the reply) becomes
inactive. -/
theorem ipc.reply_remove.blkZ {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (r t : U64)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hr : r ∈ Rp) (ht : t ∈ T) (hrt : L.mem s (rTcbA r) = t)
    (hst : L.mem s (stA t) = sched.TS_BLOCKED_ON_REPLY) :
    ipc.reply_remove st ar s a r t ⦃ res => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac res.1 ∧
      L.mem res.1 (stA t) = sched.TS_INACTIVE ∧ Foot st T Cs Sg Scs Z Es s res.1 ∧ L.mem res.1 (rTcbA r) = 0#u64 ⦄ := by
  have hX := h.2.2.1
  have hO := hX.1
  have ht0 : t ≠ 0#u64 := fun e0 => (h.1.choose_spec.choose_spec.tcbs t ht).ne0 (by rw [e0]; rfl)
  have hrp : L.mem s (replyA t) = r := by
    obtain ⟨-, -, b2, -⟩ := hX.2.1.back r hr (by rw [hrt]; exact ht0)
    rw [hrt] at b2; exact b2
  -- the unlinking writes keep `BlkOK` and `t`'s fields
  have W : ∀ {s₁ : S} {r' a' : U64}, BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s₁ →
      L.mem s₁ (stA t) = sched.TS_BLOCKED_ON_REPLY → L.mem s₁ (replyA t) = r → r' ∈ Rp →
      (a' = rPrevA r' ∨ a' = rNextA r') →
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s₁ a' 0#u64) ∧
        L.mem (L.wr s₁ a' 0#u64) (stA t) = sched.TS_BLOCKED_ON_REPLY ∧ L.mem (L.wr s₁ a' 0#u64) (replyA t) = r ∧
        Foot st T Cs Sg Scs Z Es s₁ (L.wr s₁ a' 0#u64) :=
    fun h₁ e₁ e₂ hr' ha' => by
      obtain ⟨k, f⟩ := rword_wr0_all h₁ hr' ha'
      refine ⟨k, by rw [stA_eq, f t ht _ (by simp) (by simp), ← stA_eq]; exact e₁,
        (f t ht 3360#u64 (by simp) (by simp)).trans e₂, ?_⟩
      rcases ha' with rfl | rfl
      · exact foot_sgw (rp_aligned hO hr').2.1 (hO.prevW hr')
      · exact foot_sgw (rp_aligned hO hr').2.2 (hO.nextW hr')
  have tail : ∀ s₂ : S, BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s₂ →
      L.mem s₂ (stA t) = sched.TS_BLOCKED_ON_REPLY → L.mem s₂ (replyA t) = r →
      (do
        let s3 ← obj.Reply.set_prev st r s₂ 0#u64
        let s4 ← obj.Reply.set_next st r s3 0#u64 false
        let s5 ← ipc.reply_unlink st s4 r t
        ok (s5, a)) ⦃ res => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac res.1 ∧
          L.mem res.1 (stA t) = sched.TS_INACTIVE ∧ Foot st T Cs Sg Scs Z Es s₂ res.1 ∧ L.mem res.1 (rTcbA r) = 0#u64 ⦄ := by
    intro s₂ h₂ e₂ r₂
    refine WP.spec_bind (obj.Reply.set_prev.val s₂ r 0#u64) fun s3 e3 => ?_
    rw [zero_or_masked] at e3; subst e3
    obtain ⟨h3, e3, r3, g3⟩ := W h₂ e₂ r₂ hr (Or.inl rfl)
    refine WP.spec_bind (obj.Reply.set_next.val0 _ r 0#u64) fun s4 e4 => ?_
    rw [zero_link] at e4; subst e4
    obtain ⟨h4, e4, r4, g4⟩ := W h3 e3 r3 hr (Or.inr rfl)
    have hrt4 := (h4.2.2.1.2.1.reply t ht e4).2
    rw [r4] at hrt4
    refine WP.spec_bind (ipc.reply_unlink.blk (Es := Es) _ r t h4 hr ht hrt4 e4) ?_
    rintro s5 ⟨h5, e5, -, z5, g5⟩
    exact (WP.spec_ok _).2 ⟨h5, e5, g3.trans (g4.trans g5), z5⟩
  unfold ipc.reply_remove
  step with obj.Reply.next.spec as ⟨nx, enx⟩
  step with obj.Reply.prev.spec as ⟨pv, epv⟩
  subst nx pv
  have hpR : L.mem s (rPrevA r) &&& ~~~1#u64 ≠ 0#u64 → L.mem s (rPrevA r) &&& ~~~1#u64 ∈ Rp := hX.2.1.prev r hr
  -- the prev neighbour's `NEXT` word, then the tail
  have P : ∀ s₁ : S, BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s₁ →
      L.mem s₁ (stA t) = sched.TS_BLOCKED_ON_REPLY → L.mem s₁ (replyA t) = r →
      (do
        let s2 ← if (L.mem s (rPrevA r) &&& ~~~1#u64) != 0#u64
          then obj.Reply.set_next st (L.mem s (rPrevA r) &&& ~~~1#u64) s₁ 0#u64 false else ok s₁
        let s3 ← obj.Reply.set_prev st r s2 0#u64
        let s4 ← obj.Reply.set_next st r s3 0#u64 false
        let s5 ← ipc.reply_unlink st s4 r t
        ok (s5, a)) ⦃ res => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac res.1 ∧
          L.mem res.1 (stA t) = sched.TS_INACTIVE ∧ Foot st T Cs Sg Scs Z Es s₁ res.1 ∧ L.mem res.1 (rTcbA r) = 0#u64 ⦄ := by
    intro s₁ h₁ e₁ r₁
    split
    · rename_i hp0
      refine WP.spec_bind (obj.Reply.set_next.val0 s₁ _ 0#u64) fun s2 e2 => ?_
      rw [zero_link] at e2; subst e2
      obtain ⟨h2, e2, r2, g2⟩ := W h₁ e₁ r₁ (hpR (by simpa using hp0)) (Or.inr rfl)
      exact WP.spec_mono (tail _ h2 e2 r2) fun r hr => ⟨hr.1, hr.2.1, g2.trans hr.2.2.1, hr.2.2.2⟩
    · simp only [Aeneas.Std.bind_ok]; exact tail s₁ h₁ e₁ r₁
  split
  · rename_i hn0
    have hn0' : L.mem s (rNextA r) &&& ~~~1#u64 ≠ 0#u64 := by simpa using hn0
    step with obj.Reply.next_is_head.spec as ⟨b, eb⟩
    split
    · rename_i hb
      have hb' : headBit (L.mem s (rNextA r)) = true := by rw [← eb]; exact hb
      exact ipc.reply_pop.blkZ hA s a r t h hr ht hrt hst hb' hn0'
    · rename_i hb
      have hb' : headBit (L.mem s (rNextA r)) = false := by rw [← eb]; simpa using hb
      have hnR := (hX.2.1.next r hr hn0').2 hb'
      refine WP.spec_bind (obj.Reply.set_prev.val s _ 0#u64) fun s1 e1 => ?_
      rw [zero_or_masked] at e1; subst e1
      obtain ⟨h1, e1, r1, g1⟩ := W h hst hrp hnR (Or.inl rfl)
      exact WP.spec_mono (P _ h1 e1 r1) fun r hr => ⟨hr.1, hr.2.1, g1.trans hr.2.2.1, hr.2.2.2⟩
  · rename_i hn0
    simp only [Aeneas.Std.bind_ok]
    exact P s h hst hrp



/-- **Reply**: a final cap's `finalise_cap` leaves the reply's `TCB` word null. -/
theorem fin_cap_reply.dead {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (p : U64)
    (x ex : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hp : p ∈ Rp) :
    objects.finalise_cap st ar s a (.Reply p x) true ex ⦃ r => L.mem r.2.1 (rTcbA p) = 0#u64 ⦄ := by
  rw [fin_cap_eq_obj (by simp)]
  unfold objects.finalise_cap_object
  dsimp only
  simp only [ite_true]
  refine WP.spec_bind (obj.Reply.tcb.blk s p) fun i ei => ?_
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  split
  · rename_i hb
    refine (WP.spec_ok _).2 ?_
    rw [← ei]; rw [eb] at hb; simpa using hb
  rename_i hb
  have hi0 : i ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
  have hX := h.2.2.1
  obtain ⟨-, hiT, -, hst⟩ := hX.2.1.back p hp (by rw [← ei]; exact hi0)
  rw [← ei] at hiT hst
  step with obj.Tcb.state.spec as ⟨v, ev⟩
  split
  · rename_i hv
    refine WP.spec_bind (ipc.reply_remove.blkZ (Es := EH H) hA s a p i h hp hiT ei.symm (by rw [← ev, hv])) ?_
    rintro ⟨s1, a1⟩ ⟨-, -, -, z1⟩
    exact (WP.spec_ok _).2 z1
  split
  · obtain ⟨⟨Q, R, h0⟩, hB, -, hS, hSg⟩ := h
    refine WP.spec_bind (ipc.cancel_ipc.all s a i Q R h0 hiT hB hX hSg.sub) ?_
    rintro ⟨s1, a1⟩ ⟨-, -, -, -, -, -, -, z1⟩
    exact (WP.spec_ok _).2 (z1 p hp ei.symm)
  · rename_i hv1 hv2
    exfalso
    rcases hst with e | e
    · exact hv1 (by rw [ev, e])
    · exact hv2 (by rw [ev, e])

end rp

/-! ## Scheduling contexts -/

/-- `fin_sc.blk`, with the SC's `TCB`, `REPLY` and `NTFN` words null at the end. -/
theorem fin_sc.dead {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (p x : U64)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hp : p ∈ Scs) (hp0 : p ≠ 0#u64)
    (hna : L.mem s (scTcbA p) ≠ 0#u64 → L.actionW s ≠ L.mem s (scTcbA p))
    (hidle : L.mem s (scTcbA p) ≠ 0#u64 → L.idleW s ≠ L.mem s (scTcbA p)) :
    objects.finalise_cap_object st ar s a (.SchedContext p x) true ⦃ r =>
      L.mem r.2.1 (scTcbA p) = 0#u64 ∧ L.mem r.2.1 (scReplyA p) = 0#u64 ∧ L.mem r.2.1 (scNtfnA p) = 0#u64 ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  simp only [ite_true]
  refine WP.spec_bind (schedcontext.unbind_all_tcbs.blk hA s a p h hp hp0 hna hidle) ?_
  rintro ⟨s1, a1⟩ ⟨h1, f1, -, -, t1, c1⟩
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (schedcontext.unbind_ntfn.blk s1 p h1 fun _ => hp) fun s2 ⟨h2, f2, t2, c2, n2⟩ => ?_
  refine WP.spec_bind (schedcontext.unbind_reply.blk s2 p p h2 (fun _ => hp) hp) fun s3 ⟨h3, f3, k3, r3⟩ => ?_
  refine WP.spec_bind (obj.Sc.yield_from.val s3 p) fun yf eyf => ?_
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧
      Foot st T Cs Sg Scs Z ∅ s3 r.1 ∧ SKeep st p s3 r.1) ?_ ?_
  · split
    · exact (WP.spec_ok _).2 ⟨h3, Foot.refl _, SKeep.refl _ _⟩
    · refine WP.spec_mono (schedcontext.complete_yield_to.blkS hA s3 a1 yf p h3 (fun hy0 => by
        rw [eyf]; exact h3.2.2.1.2.2.yt.2.2 p hp (by rw [← eyf]; exact hy0)) hp) ?_
      rintro ⟨s4, a4⟩ ⟨h4, f4, -, k4⟩
      exact ⟨h4, f4, k4⟩
  rintro ⟨s4, a2⟩ ⟨h4, f4, k4⟩
  try simp only [WP.uncurry'_pair]
  have t4 : L.mem s4 (scTcbA p) = 0#u64 := by rw [k4.1, k3.1, t2, t1]
  have n4 : L.mem s4 (scNtfnA p) = 0#u64 := by rw [k4.2.1, k3.2.1, n2 hp0]
  have r4 : L.mem s4 (scReplyA p) = 0#u64 := k4.2.2.2 (r3 hp0)
  have hO4 := h4.2.2.1.1
  obtain ⟨hPp, hzp⟩ := hO4.sc p hp
  obtain ⟨h8, -, -⟩ := sc_lo hPp hzp
  obtain ⟨-, e24, -, -, -, -, e32, -⟩ := sc_facts hO4 hp
  have e40 := scNtfnA_val hPp hzp
  have mxv := maxA_val hPp hzp
  have hsv : layout.sc.SPORADIC.val = 64 := by simp [layout.sc.SPORADIC]
  have av : (core.num.U64.wrapping_add p layout.sc.SPORADIC).val = p.val + 64 := by
    rw [sc_word_val hPp hzp (by rw [hsv]; omega), hsv]
  have hal : Aligned (core.num.U64.wrapping_add p layout.sc.SPORADIC) := by unfold Aligned; rw [av]; omega
  have ham := (maxA_facts hO4 hp).1
  refine WP.spec_bind (obj.Sc.set_refill_max.spec s4 p 0#u64) fun s5 e5 => ?_
  subst e5
  refine WP.spec_bind (obj.Sc.set_sporadic.wr _ p 0#u64) fun s6 e6 => ?_
  subst e6
  have key : ∀ b : U64, (b.val = p.val + 24 ∨ b.val = p.val + 32 ∨ b.val = p.val + 40) →
      L.mem (L.wr (L.wr s4 (maxA p) 0#u64) (core.num.U64.wrapping_add p layout.sc.SPORADIC) 0#u64) b =
        L.mem s4 b := fun b hv => by
    have hb : Aligned b := by unfold Aligned; omega
    rw [L.mem_wr_ne hal hb (by rw [av]; omega), L.mem_wr_ne ham hb (by rw [mxv]; omega)]
  exact (WP.spec_ok _).2 ⟨by rw [key _ (Or.inl e24), t4], by rw [key _ (Or.inr (Or.inl e32)), r4],
    by rw [key _ (Or.inr (Or.inr e40)), n4]⟩

/-- **Scheduling context**: a final cap's `finalise_cap` leaves the SC's
`TCB`, `REPLY` and `NTFN` words null. -/
theorem fin_cap_sc.dead {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (p x : U64)
    (ex : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hp : p ∈ Scs) (hp0 : p ≠ 0#u64)
    (hna : L.mem s (scTcbA p) ≠ 0#u64 → L.actionW s ≠ L.mem s (scTcbA p))
    (hidle : L.mem s (scTcbA p) ≠ 0#u64 → L.idleW s ≠ L.mem s (scTcbA p)) :
    objects.finalise_cap st ar s a (.SchedContext p x) true ex ⦃ r =>
      L.mem r.2.1 (scTcbA p) = 0#u64 ∧ L.mem r.2.1 (scReplyA p) = 0#u64 ∧ L.mem r.2.1 (scNtfnA p) = 0#u64 ⦄ := by
  rw [fin_cap_eq_obj (by simp)]
  exact fin_sc.dead hA s a p x h hp hp0 hna hidle

end
end Fl4Proofs.P1
