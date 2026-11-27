-- AArch64 port of Fl4Proofs.P1.QueueFinCur (proofs/scratch/a64/port.py): the x86_64 text, re-checked
-- over Fl4CoreA64. Edits beyond the renaming are marked `-- a64:`.
/-
P1: the current-thread frames of the finalisations (`CurF`): the current
thread and the current SC word are kept, the current thread's `SC` field is
kept or cleared, and the scheduler action is kept or `CHOOSE_NEW`.  They are
proved as separate lemmas (`.csc` for the current SC word, which `CaiFr`
does not carry) and combined with the invariant lemmas by `spec_and`.

a64 (AArch64 port): the AArch64 donation (`donate_tail.frame`, `donate.unbound` / `.gen` / `.idle`) needs
the receiver to run no VCPU (its `migrate_tcb` would flush a running VCPU). So `schedcontext.donate.curR`
takes `hrv` (the receiver's `RUN_VCPU` 0, carried over the stall, the queue removals, the `SC` clear and
`reschedule_required`), `ipc.reply_pop.curR` / `ipc.reply_remove.curR` take `hrvt` (the replier's
`RUN_VCPU` 0; it is `TS_BLOCKED_ON_REPLY`), and `finGap_reply` (now from `DelPlaceAt`, a `FinGapAt`)
gets them from **[J] `DelPlaceAt.rv`** (`RunVcpuInv` along the deletion, QueueDelFin) by
`RunVcpuInv.zero`, and feeds `RunVcpuInv` to `fin_reply.blk`. IRQ node at ks + 43232, kernel-global area
223488. Named premises: [J] `RunVcpuInv` (as `DelPlaceAt.rv`); nothing else new.
-/
import Fl4ProofsA64.P1.QueueDelFin
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-! ## The current SC word across `cancel_all_ipc` -/

theorem endpoint.unblock_sporadic.csc {X : Set U64} (s : S) (t : obj.Tcb) {Q : U64 → U64 → List U64}
    {R : U64 → List U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R)
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hS : SCsOK st T Ω Sg Scs Z Ac s) (ht : t ∈ T) :
    endpoint.unblock_sporadic st s t ⦃ s' => L.cscW s' = L.cscW s ⦄ := by
  unfold endpoint.unblock_sporadic
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
      refine WP.spec_mono (sporadic.unblock_check.fr hW ⟨aR, oR⟩) fun s3 w3 => ?_
      have kn : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 56 →
          L.mem s3 (L.nodeA s o) = L.mem s (L.nodeA s o) := fun o ho h8 h56 => by
        refine w3.mem_eq (nodeAt_aligned hN' ho h8) ?_
        rintro (hh | hh)
        · have hm := hX.1.scW i hiS _ (nodeAt_aligned hN' ho h8) hh.inSC
          exact out_ne_node (h.omega _ hm) h.cur hN' ho rfl
        · have := congrArg UScalar.val hh
          simp only [LawfulStore.nodeA] at this
          rw [nodeAt_val hN' ho, nodeAt_val hN' (by rw [rp]; omega), rp] at this; omega
      unfold LawfulStore.cscW
      rw [cscW_eq w3.1 w3.2.1]
      exact kn _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
    · exact (WP.spec_ok _).2 rfl
  · exact (WP.spec_ok _).2 rfl

theorem endpoint.restart_thread_if_no_fault.csc {X : Set U64} (s : S) (t : obj.Tcb) {Q : U64 → U64 → List U64}
    {R : U64 → List U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hXt : ∀ y ∈ X, y = t)
    (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hS : SCsOK st T Ω Sg Scs Z Ac s)
    (hSg : SgOK st Ω Sg s) (ht : t ∈ T) (hx : t ∈ X ∨ ¬ Blocked (L.mem s (stA t)))
    (hnoref : ∀ r ∈ Rp, L.mem s (rTcbA r) ≠ t)
    (hnQ : ∀ c ∈ Cs, ∀ p : U64, p.val < 256 → t ∉ Q c p) (hnR : ∀ c ∈ Cs, t ∉ R c) (hna : L.actionW s ≠ t)
    (htA : L.mem s (scA t) ≠ 0#u64 → L.mem s (scA t) ∈ Ac) :
    endpoint.restart_thread_if_no_fault st s t ⦃ s' => L.cscW s' = L.cscW s ⦄ := by
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
    rintro s1 ⟨h1, hB1, hX1, hS1, hSg1, st1, k1⟩
    have h1' : SchedQueuesInv st T Cs Ω H s1 Q R := h1.congrX cg
    refine WP.spec_bind (WP.spec_and (endpoint.unblock_sporadic.all s1 t h1' hB1 hX1 hS1 hSg1 ht)
      (endpoint.unblock_sporadic.csc s1 t h1' hX1 hS1 ht)) ?_
    rintro s2 ⟨⟨h2, hB2, hX2, hS2, hSg2, -, -, -, fk2, -⟩, cs2⟩
    have st2 : L.mem s2 (stA t) = sched.TS_RESTART := by
      rw [stA_eq, fk2 t ht _ (by simp) (by simp), ← stA_eq]; exact st1
    have esc2 : L.mem s2 (scA t) = L.mem s (scA t) := by
      rw [scA_eq, fk2 t ht _ (by simp) (by simp), ← scA_eq, k1.scf ht]
    refine WP.spec_mono (sched.possible_switch_to.sch (Sg := Sg) s2 t Q R h2 hB2 hSg2 ht
      (by rw [st2]; exact runnable_restart) (by rw [esc2]; exact htA)) ?_
    rintro s3 ⟨p3, -, -⟩
    rw [p3.fr.csc, cs2, k1.cscW]
  · refine WP.spec_mono (sts_all s t _ Q R h hB hX hS hSg ht not_blocked_inactive inactive_ne hx hnoref
      (hq _)) ?_
    rintro s1 ⟨-, -, -, -, -, -, k1⟩
    exact k1.cscW

theorem cai_round.csc {β : Type _} (s : S) (ep t : U64) (fuel1 : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
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
        L.cscW s3 = L.cscW s ⦄ := by
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
  have tm1 : TmFr st T Cs Nt s s1 := TmFr.mk0 ⟨k1, fun y hy K a b c => f1 y hy K (by omega) c (by omega) (by omega),
    fun c hc o ho => nc1 c hc o (by omega) (by omega), fun n' hn' => o1 _ (hSg.sub _ (hX.1.ntB n' hn').2)⟩
  obtain ⟨hB1, hX1, hS1, hSg1, ea1, ec1, ei1⟩ := frame_bx h0 hB hX hS hSg f1 o1 n1 k1 tm1
  have F1 : L.cscW s1 = L.cscW s := n1 _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
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
  have tail : ∀ (s2 : S), Foot st T Cs Sg Scs Z ∅ s1 s2 → L.cscW s2 = L.cscW s →
      endpoint.restart_thread_if_no_fault st s2 y ⦃ s' =>
        (BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ Foot st T Cs Sg Scs Z ∅ s2 s') ∧ L.cscW s' = L.cscW s2 ⦄ →
      (do
        let s3 ← endpoint.restart_thread_if_no_fault st s2 y
        ok (ControlFlow.cont (β := β) (s3, next, fuel1))) ⦃ r => ∃ s3 next', r = .cont (s3, next', fuel1) ∧
          BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s3 ∧ Foot st T Cs Sg Scs Z {ep} s s3 ∧
          (next' ≠ 0#u64 → (L.epState s3 ep = 1#u64 ∨ L.epState s3 ep = 2#u64) ∧ (L.epQ s3 ep).head = next') ∧
          L.cscW s3 = L.cscW s ⦄ := by
    intro s2 fw2 F2 hr
    refine WP.spec_bind hr fun s3 ⟨⟨hb3, fw3⟩, F3⟩ => ?_
    have f13 : Foot st T Cs Sg Scs Z ∅ s1 s3 := fw2.trans fw3
    obtain ⟨eh, et⟩ := f13.epQ h1 hX1.1 hSg1.sub (Or.inl hH)
    refine (WP.spec_ok _).2 ⟨s3, next, rfl, hb3, fw1.trans (f13.mono (Set.empty_subset _)), fun hn0 => ?_,
      F3.trans F2⟩
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
      have cg2 : ∀ z ∈ {y_1 | y_1 ∈ {z : U64 | z ∈ (∅ : Set U64) ∨ z = y} ∧ y_1 ≠ y}, z = y := fun z hz => by
        obtain ⟨hz1, hz2⟩ := hz
        exact absurd (cg1 z hz1) hz2
      refine tail s2 fw2 (k2.cscW.trans F1) (WP.spec_and
        (endpoint.restart_thread_if_no_fault.blk s2 y h2 cg2 hB2 hX2 hS2 hSg2 hdT
          (Or.inr (by rw [e2]; exact not_blocked_inactive))
          (hX2.noref hta (by rw [e2]; exact inactive_ne.1) (by rw [e2]; exact inactive_ne.2)) hnQ hnR da2
          (by rw [k2.scf hdT]; exact hyA1))
        (endpoint.restart_thread_if_no_fault.csc s2 y h2 cg2 hB2 hX2 hS2 hSg2 hdT
          (Or.inr (by rw [e2]; exact not_blocked_inactive))
          (hX2.noref hta (by rw [e2]; exact inactive_ne.1) (by rw [e2]; exact inactive_ne.2)) hnQ hnR da2
          (by rw [k2.scf hdT]; exact hyA1)))
    · rename_i hi1
      have hz : i1 = 0#u64 := by apply UScalar.eq_of_val_eq; simpa using hi1
      have hi10 : L.mem s1 (replyA y) = 0#u64 := by rw [← ei1]; exact hz
      simp only [Aeneas.Std.bind_ok]
      exact tail s1 (Foot.refl _) F1 (WP.spec_and
        (endpoint.restart_thread_if_no_fault.blk s1 y h1 cg1 hB1 hX1 hS1 hSg1 hdT
          (Or.inl (Or.inr rfl)) (hX1.noref0 hta hi10) hnQ hnR da1 hyA1)
        (endpoint.restart_thread_if_no_fault.csc s1 y h1 cg1 hB1 hX1 hS1 hSg1 hdT
          (Or.inl (Or.inr rfl)) (hX1.noref0 hta hi10) hnQ hnR da1 hyA1))
  · rename_i hnrecv
    have hsend : L.mem s1 (stA y) = sched.TS_BLOCKED_ON_SEND := by
      rcases hsr with e | e
      · rw [st1, e]
      · exact absurd (by rw [ei, st1, e]) hnrecv
    have nrp : sched.TS_BLOCKED_ON_SEND ≠ sched.TS_BLOCKED_ON_REPLY := by
      rw [r4]; unfold sched.TS_BLOCKED_ON_REPLY; decide
    have nrc : sched.TS_BLOCKED_ON_SEND ≠ sched.TS_BLOCKED_ON_RECV := by rw [r4, r3]; decide
    simp only [Aeneas.Std.bind_ok]
    exact tail s1 (Foot.refl _) F1 (WP.spec_and
      (endpoint.restart_thread_if_no_fault.blk s1 y h1 cg1 hB1 hX1 hS1 hSg1 hdT
        (Or.inl (Or.inr rfl)) (hX1.noref hta (by rw [hsend]; exact nrp) (by rw [hsend]; exact nrc)) hnQ hnR da1 hyA1)
      (endpoint.restart_thread_if_no_fault.csc s1 y h1 cg1 hB1 hX1 hS1 hSg1 hdT
        (Or.inl (Or.inr rfl)) (hX1.noref hta (by rw [hsend]; exact nrp) (by rw [hsend]; exact nrc)) hnQ hnR da1 hyA1))


theorem endpoint.cancel_all_ipc_loop.csc (s0 s : S) (ep t fuel : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hH : H ep = some .ep) (hf : Foot st T Cs Sg Scs Z {ep} s0 s) (hF : L.cscW s = L.cscW s0)
    (ht : t ≠ 0#u64 → (L.epState s ep = 1#u64 ∨ L.epState s ep = 2#u64) ∧ (L.epQ s ep).head = t) :
    endpoint.cancel_all_ipc_loop st s ep t fuel ⦃ s' =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ Foot st T Cs Sg Scs Z {ep} s0 s' ∧ L.cscW s' = L.cscW s0 ⦄ := by
  unfold endpoint.cancel_all_ipc_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.2.val)
    (inv := fun x => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac x.1 ∧ Foot st T Cs Sg Scs Z {ep} s0 x.1 ∧
      L.cscW x.1 = L.cscW s0 ∧
      (x.2.1 ≠ 0#u64 → (L.epState x.1 ep = 1#u64 ∨ L.epState x.1 ep = 2#u64) ∧ (L.epQ x.1 ep).head = x.2.1))
  · rintro ⟨s1, t1, f1⟩ ⟨hb1, hf1, hF1, ht1⟩
    simp only at hb1 hf1 hF1 ht1
    unfold endpoint.cancel_all_ipc_loop.body
    step with obj.Tcb.is_null.spec as ⟨b, eb⟩
    split
    · exact (WP.spec_ok _).2 ⟨hb1, hf1, hF1⟩
    rename_i hb
    have ht0 : t1 ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    obtain ⟨hst1, hhd1⟩ := ht1 ht0
    split
    · rename_i hfuel
      step as ⟨fuel1, efuel⟩
      refine WP.spec_mono (cai_round.csc (β := S) s1 ep t1 fuel1 hb1 hH hst1 hhd1) ?_
      rintro r ⟨s4, next, rfl, hb4, hf4, hn4, hF4⟩
      exact ⟨hb4, hf1.trans hf4, hF4.trans hF1, hn4, by simp only; omega⟩
    · exact (WP.spec_ok _).2 ⟨hb1, hf1, hF1⟩
  · exact ⟨h, hf, hF, ht⟩

/-- **seL4 `cancelAllIPC` with its scheduling frame** (`CaiFr`); the
scheduler action ends kept or `CHOOSE_NEW`. -/
theorem endpoint.cancel_all_ipc.csc (s : S) (ep : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hH : H ep = some .ep) :
    endpoint.cancel_all_ipc st s ep ⦃ s' =>
      L.cscW s' = L.cscW s ⦄ := by
  unfold endpoint.cancel_all_ipc
  step with obj.Ep.state.spec as ⟨v, hv⟩
  split
  · exact (WP.spec_ok _).2 rfl
  rename_i hidle
  have hst : L.epState s ep ≠ 0#u64 := by
    rw [← hv]; intro e; exact hidle (by rw [e]; unfold obj.EP_IDLE; rfl)
  step with endpoint.get_queue.spec as ⟨q, eq⟩
  subst eq
  have hI := h
  obtain ⟨⟨Q, R, h0⟩, -⟩ := hI
  refine WP.spec_bind (endpoint.cancel_all_ipc_loop.csc s s ep _ _ h hH (Foot.refl _) rfl
    (fun _ => ⟨ep_state12 h0 hH hst, rfl⟩)) ?_
  rintro s1 ⟨h1, f1, F1⟩
  obtain ⟨⟨Q1, R1, q1⟩, hB1, hX1, hS1, hSg1⟩ := h1
  refine WP.spec_mono (sched.reschedule_required.schX s1 Q1 R1 q1 hB1 hSg1) fun s2 ⟨_, _, p2, _⟩ => ?_
  rw [p2.csc, F1]

/-! ## The endpoint kind -/

/-- The current thread is not blocked in a `Cur0` state. -/
theorem Cur0.nb {s0 s : S} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) :
    ¬ BlockedR (L.mem s (stA (L.curW s))) := by
  obtain ⟨-, -, -, ec, -, -, -, nb, -⟩ := h
  rw [ec]; exact nb

/-- `Cur0` from a step with the invariants, the current thread, the current
SC word and every thread's `SC` field kept, and the action kept or
`CHOOSE_NEW`. -/
theorem Cur0.step {s0 s s' : S} {Ac' : Set U64} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s)
    (hb : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac' s') (ec : L.curW s' = L.curW s) (ecs : L.cscW s' = L.cscW s)
    (esc : L.mem s' (scA (L.curW s)) = L.mem s (scA (L.curW s)) ∨ L.mem s' (scA (L.curW s)) = 0#u64)
    (ea : L.actionW s' = L.actionW s ∨ L.actionW s' = 1#u64)
    (est : ¬ BlockedR (L.mem s (stA (L.curW s))) → ¬ BlockedR (L.mem s' (stA (L.curW s))))
    (hw : WritesIn st s s' (Cur0W st T Cs Ω H Sg Scs Z s)) :
    Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' := by
  refine Cur0.mk h (BlkOK.bxi hb) ec ecs esc ea (Or.inr (est h.nb)) hw

/-- **The endpoint kind's finalisation** (`FinGaps.ep`). -/
theorem finGap_ep {A : Type _} {ar : machine.Arch A} :
    FinGap st ar T Cs Ω H Sg Rp Scs Nt Z fun c => ∃ x1 x2 x3 x4 x5 x6, c = .Endpoint x1 x2 x3 x4 x5 x6 := by
  intro Ac s0 s a c fin h hc _ ⟨ep, b0, b1, b2, b3, b4, e⟩
  subst e
  have hH := hc.1.1 ep b0 b1 b2 b3 b4 rfl
  obtain ⟨Ac', hb⟩ := h.bxi
  rw [fin_cap_eq_obj (by simp)]
  have hct : L.curW s ∈ T := hb.1.choose_spec.choose_spec.curT
  have CS : objects.finalise_cap_object st ar s a (.Endpoint ep b0 b1 b2 b3 b4) fin ⦃ r =>
      L.cscW r.2.1 = L.cscW s ⦄ := by
    unfold objects.finalise_cap_object
    dsimp only
    split
    · exact WP.spec_bind (endpoint.cancel_all_ipc.csc s ep hb.blk hH) fun s1 e1 => (WP.spec_ok _).2 e1
    · exact (WP.spec_ok _).2 rfl
  refine WP.spec_mono (WP.spec_and (fin_endpoint.fr (ar := ar) s a ep b0 b1 b2 b3 b4 fin hb.blk hH) CS) ?_
  rintro ⟨⟨r1, r2⟩, s', a'⟩ ⟨⟨e, -, hb', f', F, ea⟩, ecs⟩
  simp only at e hb' f' F ea ecs ⊢
  cases e
  refine ⟨h.step hb' F.cur ecs (Or.inl (F.sc _ hct)) ea (fun hnb => ?_)
    (Foot.cur0w f' fun x hx => by rw [Set.mem_singleton_iff.1 hx]; exact Or.inl hH), DelCapOK.null, DelCapOK.null⟩
  rcases F.st _ hct with e | e | e
  · rw [e]; exact hnb
  · rw [e]; exact nbr_restart
  · rw [e]; exact fun hb => hb.elim not_blocked_inactive inactive_ne.1

/-! ## The notification kind -/

/-- The current-thread frame: the current thread, the current SC word and
every thread's `SC` field kept, and no thread becomes blocked. -/
def CurF (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s s' : S) : Prop :=
  L.curW s' = L.curW s ∧ L.cscW s' = L.cscW s ∧ (∀ z ∈ T, L.mem s' (scA z) = L.mem s (scA z)) ∧
    ∀ z ∈ T, ¬ BlockedR (L.mem s (stA z)) → ¬ BlockedR (L.mem s' (stA z))

theorem CurF.refl (s : S) : CurF st T s s := ⟨rfl, rfl, fun _ _ => rfl, fun _ _ h => h⟩

theorem CurF.trans {s₁ s₂ s₃ : S} (h₁ : CurF st T s₁ s₂) (h₂ : CurF st T s₂ s₃) : CurF st T s₁ s₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, fun z hz => (h₂.2.2.1 z hz).trans (h₁.2.2.1 z hz),
    fun z hz hb => h₂.2.2.2 z hz (h₁.2.2.2 z hz hb)⟩

/-- A write outside the objects' TCBs and nodes (in `Ω`). -/
theorem curF_wr_out {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {a v : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ha : a ∈ Ω) : CurF st T s (L.wr s a v) := by
  have ho := h.omega a ha
  have hN := h.nodes _ h.cur
  have hT := h.tcbs
  refine ⟨?_, cscW_wr_out h ha, fun z hz => ?_, fun z hz hb => ?_⟩
  · unfold LawfulStore.curW; rw [nodeAt_wr, L.cpu_wr]
    exact L.mem_wr_ne ho.1 (nodeAt_aligned hN (by rw [curth0]; omega) (by rw [curth0]))
      (fun e => out_ne_node ho h.cur hN (by rw [curth0]; omega) e.symm)
  · rw [scA_eq]
    exact L.mem_wr_ne ho.1 (field_aligned (hT z hz) (by simp) (by simp))
      (fun e => out_ne_field ho hz (hT z hz) (by simp) e.symm)
  · rw [stA_eq, L.mem_wr_ne ho.1 (field_aligned (hT z hz) (by simp) (by simp))
      (fun e => out_ne_field ho hz (hT z hz) (by simp) e.symm), ← stA_eq]; exact hb

/-- A TCB field write other than the `SC` field. -/
theorem curF_wr_field {s : S} {y K v : U64} (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s)) (hy : y ∈ T)
    (hK : K.val < 4096) (hK8 : K.val % 8 = 0) (hKs : K.val ≠ 3464) (hKt : K.val ≠ 3328) :
    CurF st T s (L.wr s (core.num.U64.wrapping_add y K) v) := by
  refine ⟨?_, cscW_wr_field hT hN hy hK hK8, fun z hz => ?_, fun z hz hb => ?_⟩
  · unfold LawfulStore.curW; rw [nodeAt_wr, L.cpu_wr]
    exact L.mem_wr_ne (field_aligned (hT y hy) hK hK8) (nodeAt_aligned hN (by rw [curth0]; omega) (by rw [curth0]))
      (fun e => node_ne_field hN (by rw [curth0]; omega) hy (hT y hy) hK (UScalar.eq_of_val_eq e).symm)
  · rw [scA_eq]
    exact L.mem_wr_ne (field_aligned (hT y hy) hK hK8) (field_aligned (hT z hz) (by simp) (by simp))
      (fun e => field_ne (hT y hy) (hT z hz) hK (by simp) (fun _ => by simp; omega) (UScalar.eq_of_val_eq e))
  · rw [stA_eq, L.mem_wr_ne (field_aligned (hT y hy) hK hK8) (field_aligned (hT z hz) (by simp) (by simp))
      (fun e => field_ne (hT y hy) (hT z hz) hK (by simp) (fun _ => by simp; omega) (UScalar.eq_of_val_eq e)),
      ← stA_eq]; exact hb

theorem cas_round.curF {β : Type _} (s : S) (n t : U64) (fuel1 : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hH : H n = some .ntfn) (hst : L.epState s n = 1#u64) (hhd : (L.epQ s n).head = t) :
    (do
      let next ← tcbqueue.next_of st s .Ep t
      let s1 ← notification.ntfn_dequeue st s n t
      let s2 ← sched.set_thread_state st s1 t sched.TS_RESTART
      let s3 ← notification.unblock_sporadic st s2 t
      let s4 ← sched.possible_switch_to st s3 t
      ok (ControlFlow.cont (β := β) (s4, next, fuel1))) ⦃ r => ∃ s4 next, r = .cont (s4, next, fuel1) ∧
        CurF st T s s4 ⦄ := by
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
  refine WP.spec_bind (WP.spec_and (sts_all s1 y _ Q R h1 hB1 hX1 hS1 hSg1 hdT not_blocked_restart restart_ne
    (Or.inl (Or.inr rfl)) (hX1.noref hta (by rw [st1]; exact blocked_ne_reply (Or.inr (Or.inr rfl)))
      (by rw [st1, r3, r6]; decide))
    ⟨fun _ _ _ _ _ => runnable_restart, fun _ _ _ => runnable_restart, fun _ => runnable_restart⟩)
    (sched.set_thread_state.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) s1 y _ h1 hdT)) ?_
  rintro s2 ⟨⟨h2, hB2, hX2, hS2, hSg2, st2, k2⟩, fw2⟩
  have h2' : SchedQueuesInv st T Cs Ω H s2 Q R := h2.congrX empty_congr'
  refine WP.spec_bind (WP.spec_and (endpoint.unblock_sporadic.all s2 y h2' hB2 hX2 hS2 hSg2 hdT)
    (endpoint.unblock_sporadic.csc s2 y h2' hX2 hS2 hdT)) ?_
  rintro s3 ⟨⟨h3, hB3, hX3, hS3, hSg3, -, ec3, -, fk3, -⟩, cs3⟩
  have st3 : L.mem s3 (stA y) = sched.TS_RESTART := by
    rw [stA_eq, fk3 y hdT _ (by simp) (by simp), ← stA_eq]; exact st2
  have esc3 : L.mem s3 (scA y) = L.mem s (scA y) := by
    rw [scA_eq, fk3 y hdT _ (by simp) (by simp), ← scA_eq, k2.scf hdT, scA_eq,
      f1 y hdT _ (by simp) (by simp) (by simp) (by simp)]
  refine WP.spec_bind (WP.spec_and (sched.possible_switch_to.sch (Sg := Sg) s3 y Q R h3 hB3 hSg3 hdT
    (by rw [st3]; exact runnable_restart) (by rw [esc3]; exact hyA))
    (sched.possible_switch_to.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) s3 y h3 hdT)) ?_
  rintro s4 ⟨⟨p4, ec4, kp4⟩, -⟩
  have c1 : CurF st T s s1 := ⟨by unfold LawfulStore.curW; exact n1 _ (by rw [curth0]; omega) (by rw [curth0]),
    n1 _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]),
    fun z hz => by rw [scA_eq]; exact f1 z hz _ (by simp) (by simp) (by simp) (by simp),
    fun z hz hb => by rw [stA_eq, f1 z hz _ (by simp) (by simp) (by simp) (by simp), ← stA_eq]; exact hb⟩
  have c2 : CurF st T s1 s2 := ⟨k2.curW, k2.cscW, fun z hz => k2.scf hz, fun z hz hb => by
    by_cases e : z = y
    · subst e; rw [st2]; exact nbr_restart
    · rw [stA_eq, k2.fld z hz _ (by simp) (by simp) (by simp) (by simp) (fun e' => absurd e' e), ← stA_eq]
      exact hb⟩
  have c3 : CurF st T s2 s3 := ⟨ec3, cs3, fun z hz => by rw [scA_eq]; exact fk3 z hz _ (by simp) (by simp),
    fun z hz hb => by rw [stA_eq, fk3 z hz _ (by simp) (by simp), ← stA_eq]; exact hb⟩
  have c4 : CurF st T s3 s4 := ⟨ec4, p4.fr.csc, p4.fr.sc, fun z hz hb => by rw [kp4.1 z hz]; exact hb⟩
  exact (WP.spec_ok _).2 ⟨s4, next, rfl, ((c1.trans c2).trans c3).trans c4⟩

theorem act_wr_out {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {a v : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ha : a ∈ Ω) : L.actionW (L.wr s a v) = L.actionW s := by
  have ho := h.omega a ha
  have hN := h.nodes _ h.cur
  unfold LawfulStore.actionW; rw [nodeAt_wr, L.cpu_wr]
  exact L.mem_wr_ne ho.1 (nodeAt_aligned hN (by rw [act_val]; omega) (by rw [act_val]))
    (fun e => out_ne_node ho h.cur hN (by rw [act_val]; omega) e.symm)

theorem act_wr_fld {s : S} {y K v : U64} (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s)) (hy : y ∈ T)
    (hK : K.val < 4096) (hK8 : K.val % 8 = 0) :
    L.actionW (L.wr s (core.num.U64.wrapping_add y K) v) = L.actionW s := by
  unfold LawfulStore.actionW; rw [nodeAt_wr, L.cpu_wr]
  exact L.mem_wr_ne (field_aligned (hT y hy) hK hK8) (nodeAt_aligned hN (by rw [act_val]; omega) (by rw [act_val]))
    (fun e => node_ne_field hN (by rw [act_val]; omega) hy (hT y hy) hK (UScalar.eq_of_val_eq e).symm)

/-- `CurF` with the scheduler action kept. -/
def CurFA (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s s' : S) : Prop :=
  CurF st T s s' ∧ L.actionW s' = L.actionW s

theorem CurFA.refl (s : S) : CurFA st T s s := ⟨CurF.refl s, rfl⟩
theorem CurFA.trans {s₁ s₂ s₃ : S} (h₁ : CurFA st T s₁ s₂) (h₂ : CurFA st T s₂ s₃) : CurFA st T s₁ s₃ :=
  ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩

theorem schedcontext.unbind_ntfn.cura (s : S) (c : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hc : c ≠ 0#u64 → c ∈ Scs) :
    schedcontext.unbind_ntfn st s c ⦃ s' => CurFA st T s s' ⦄ := by
  unfold schedcontext.unbind_ntfn
  step with obj.Sc.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 (CurFA.refl _)
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
    exact (CurFA.trans ⟨curF_wr_out h0 hmj, act_wr_out h0 hmj⟩ ⟨curF_wr_out q1 hm, act_wr_out q1 hm⟩)
  · exact (WP.spec_ok _).2 (CurFA.refl _)

theorem schedcontext.maybe_unbind_ntfn.cura (s : S) (n : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hn : n ∈ Nt) :
    schedcontext.maybe_unbind_ntfn st s n ⦃ s' => CurFA st T s s' ⦄ := by
  unfold schedcontext.maybe_unbind_ntfn
  step with obj.Ntfn.sc.val as ⟨i, ei⟩
  step with obj.Sc.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 (CurFA.refl _)
  · exact schedcontext.unbind_ntfn.cura s i h fun h0 => by
      rw [ei]; exact (h.2.2.1.2.2.nsc n hn (by rw [← ei]; exact h0)).1

theorem notification.unbind_maybe_notification.cura (s : S) (n : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hn : n ∈ Nt) :
    notification.unbind_maybe_notification st s n ⦃ s' => CurFA st T s s' ⦄ := by
  unfold notification.unbind_maybe_notification
  refine WP.spec_bind (obj.Ntfn.bound_tcb.val s n) fun i ei => ?_
  refine WP.spec_bind (obj.Tcb.is_null.spec i) fun b eb => ?_
  subst eb
  split
  · exact (WP.spec_ok _).2 (CurFA.refl _)
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
    exact CurFA.trans ⟨curF_wr_out h0 hmO, act_wr_out h0 hmO⟩
      ⟨curF_wr_field (K := 3368#u64) hT hN1 hiT (by simp) (by simp) (by simp) (by simp),
        act_wr_fld (K := 3368#u64) hT hN1 hiT (by simp) (by simp)⟩

theorem notification.cancel_all_signals_loop.curF (s0 s : S) (n t fuel : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hH : H n = some .ntfn) (hf : CurF st T s0 s)
    (ht : t ≠ 0#u64 → L.epState s n = 1#u64 ∧ (L.epQ s n).head = t) :
    notification.cancel_all_signals_loop st s n t fuel ⦃ s' => CurF st T s0 s' ⦄ := by
  unfold notification.cancel_all_signals_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.2.val)
    (inv := fun x => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac x.1 ∧ CurF st T s0 x.1 ∧
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
        (cas_round.curF (β := S) s1 n t1 fuel1 hb1 hH hst1 hhd1)) ?_
      rintro r ⟨⟨s4, next, rfl, hb4, -, hn4⟩, ⟨s4', next', e', hc4⟩⟩
      simp only [ControlFlow.cont.injEq, Prod.mk.injEq] at e'
      obtain ⟨rfl, rfl, -⟩ := e'
      exact ⟨hb4, hf1.trans hc4, hn4, by simp only; omega⟩
    · exact (WP.spec_ok _).2 hf1
  · exact ⟨h, hf, ht⟩

theorem notification.cancel_all_signals.curF (s : S) (n : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hH : H n = some .ntfn) :
    notification.cancel_all_signals st s n ⦃ s' => CurF st T s s' ∧
      (L.actionW s' = L.actionW s ∨ L.actionW s' = 1#u64) ⦄ := by
  unfold notification.cancel_all_signals
  step with obj.Ntfn.state.spec as ⟨v, hv⟩
  split
  · exact (WP.spec_ok _).2 ⟨CurF.refl _, Or.inl rfl⟩
  rename_i hw
  have hst : L.epState s n = 1#u64 := by
    rw [← hv]; have := hw; simp [obj.NTFN_WAITING] at this; exact UScalar.eq_of_val_eq (by simpa using this)
  step with notification.get_queue.spec as ⟨q, eq⟩
  subst eq
  refine WP.spec_bind (WP.spec_and (notification.cancel_all_signals_loop.blk s s n _ _ h hH (Foot.refl _)
    (fun _ => ⟨hst, rfl⟩)) (notification.cancel_all_signals_loop.curF s s n _ _ h hH (CurF.refl _)
    (fun _ => ⟨hst, rfl⟩))) ?_
  rintro s1 ⟨⟨h1, -⟩, c1⟩
  obtain ⟨⟨Q1, R1, q1⟩, hB1, hX1, hS1, hSg1⟩ := h1
  refine WP.spec_mono (sched.reschedule_required.schX s1 Q1 R1 q1 hB1 hSg1)
    fun s2 ⟨_, _, p2, ea2, ec2, kp2, _⟩ => ?_
  exact ⟨c1.trans ⟨ec2, p2.csc, p2.sc, fun z hz hb => by rw [kp2.1 z hz]; exact hb⟩, Or.inr ea2⟩

/-- The notification object's finalisation from a `Cur0` state. -/
theorem fin_ntfn_obj.cur0 {A : Type _} {ar : machine.Arch A} {s0 s : S} {a : A} {n b0 : U64} {b1 b2 : Bool}
    {fin : Bool} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hn : n ∈ Nt) (hH : H n = some .ntfn) :
    objects.finalise_cap_object st ar s a (.Notification n b0 b1 b2) fin ⦃ r =>
      r.1 = (.Null, .Null) ∧ Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ⦄ := by
  obtain ⟨Ac', hb⟩ := h.bxi
  have hct : L.curW s ∈ T := hb.1.choose_spec.choose_spec.curT
  have CS : objects.finalise_cap_object st ar s a (.Notification n b0 b1 b2) fin ⦃ r =>
      CurF st T s r.2.1 ∧ (L.actionW r.2.1 = L.actionW s ∨ L.actionW r.2.1 = 1#u64) ⦄ := by
    unfold objects.finalise_cap_object
    dsimp only
    split
    · refine WP.spec_bind (WP.spec_and (schedcontext.maybe_unbind_ntfn.blk s n hb.blk hn)
        (schedcontext.maybe_unbind_ntfn.cura s n hb.blk hn)) fun s1 ⟨⟨h1, _⟩, c1⟩ => ?_
      refine WP.spec_bind (WP.spec_and (notification.unbind_maybe_notification.blkF s1 n h1 hn)
        (notification.unbind_maybe_notification.cura s1 n h1 hn)) fun s2 ⟨⟨h2, _⟩, c2⟩ => ?_
      refine WP.spec_bind (notification.cancel_all_signals.curF s2 n h2 hH) fun s3 ⟨c3, a3⟩ => ?_
      have c12 := c1.trans c2
      refine (WP.spec_ok _).2 ⟨c12.1.trans c3, ?_⟩
      rcases a3 with e | e
      · exact Or.inl (e.trans c12.2)
      · exact Or.inr e
    · exact (WP.spec_ok _).2 ⟨CurF.refl _, Or.inl rfl⟩
  refine WP.spec_mono (WP.spec_and (fin_ntfn.blk (ar := ar) s a n b0 b1 b2 fin hb.blk hn hH) CS) ?_
  rintro ⟨⟨r1, r2⟩, s', a'⟩ ⟨⟨e, -, hb', f'⟩, ⟨ec, ecs, esc, enb⟩, ea⟩
  simp only at e hb' f' ec ecs esc enb ea ⊢
  exact ⟨e, h.step hb' ec ecs (Or.inl (esc _ hct)) ea (enb _ hct)
    (Foot.cur0w f' fun x hx => by rw [Set.mem_singleton_iff.1 hx]; exact Or.inr hH)⟩

/-- **The notification kind's finalisation** (`FinGaps.ntfn`). -/
theorem finGap_ntfn {A : Type _} {ar : machine.Arch A} :
    FinGap st ar T Cs Ω H Sg Rp Scs Nt Z fun c => ∃ x1 x2 x3 x4, c = .Notification x1 x2 x3 x4 := by
  intro Ac s0 s a c fin h hc _ ⟨n, b0, b1, b2, e⟩
  subst e
  obtain ⟨hn, hH⟩ := hc.1.2.1 n b0 b1 b2 rfl
  rw [fin_cap_eq_obj (by simp)]
  refine WP.spec_mono (fin_ntfn_obj.cur0 (ar := ar) (b0 := b0) (b1 := b1) (b2 := b2) h hn hH) ?_
  rintro ⟨⟨r1, r2⟩, s', a'⟩ ⟨e, h'⟩
  simp only at e h' ⊢
  cases e
  exact ⟨h', DelCapOK.null, DelCapOK.null⟩

/-! ## The IRQ handler kind -/

theorem irq_slotW {s : S} {i : U64} (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hi : i.val < 128) :
    SlotW T Ω Sg (irqSlotA (L.ksb s) i) := by
  have q := h.1.choose_spec.choose_spec
  have hSg := h.2.2.2.1
  have e : ∀ o : U64, o.val < 32 → core.num.U64.wrapping_add (irqSlotA (L.ksb s) i) o =
      core.num.U64.wrapping_add (L.ksb s) (core.num.U64.wrapping_add 43232#u64  -- a64: 1248->43232
        (core.num.U64.wrapping_add (core.num.U64.wrapping_mul i 32#u64) o)) := fun o ho => by
    apply UScalar.eq_of_val_eq
    simp [irqSlotA, core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def,
      U64.numBits]
    omega
  have hv : ∀ o : U64, o.val < 32 → (core.num.U64.wrapping_add 43232#u64  -- a64: 1248->43232
      (core.num.U64.wrapping_add (core.num.U64.wrapping_mul i 32#u64) o)).val = 43232 + 32 * i.val + o.val :=  -- a64: 1248->43232
    fun o ho => by
      simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]
      omega
  refine ⟨?_, fun o ho h8 => ?_⟩
  · have := e 0#u64 (by simp)
    have h0 : core.num.U64.wrapping_add (irqSlotA (L.ksb s) i) 0#u64 = irqSlotA (L.ksb s) i := by
      apply UScalar.eq_of_val_eq; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
    rw [← h0, this]
    exact ks_aligned q (by rw [hv 0#u64 (by simp)]; simp; omega) (by rw [hv 0#u64 (by simp)]; simp; omega)
  · rw [e o ho]
    have hl : (core.num.U64.wrapping_add 43232#u64  -- a64: 1248->43232
        (core.num.U64.wrapping_add (core.num.U64.wrapping_mul i 32#u64) o)).val < 223488 := by rw [hv o ho]; omega  -- a64: 13568->223488
    have h8' : (core.num.U64.wrapping_add 43232#u64  -- a64: 1248->43232
        (core.num.U64.wrapping_add (core.num.U64.wrapping_mul i 32#u64) o)).val % 8 = 0 := by rw [hv o ho]; omega
    exact Or.inr ⟨hSg.ksΩ _ hl h8', fun hb' => by
      have := hSg.ks _ hb'; rw [ks_val q hl] at this; omega⟩

/-- **The IRQ handler kind's finalisation** (`FinGaps.irq`), from `DelPlace`. -/
theorem finGap_irq {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s0 : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) :
    FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z (fun c => ∃ x1, c = .IrqHandler x1) s0 := by
  have hS : P0.StoreTotal st := L.total
  intro Ac s a c fin h hc _ ⟨irq, e⟩
  subst e
  have hi := hc.2.1 irq rfl
  obtain ⟨Ac', hb⟩ := h.bxi
  unfold objects.finalise_cap
  simp only [bind_ok]
  refine WP.spec_bind (Pₘ := fun r : S × A => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1) ?_ ?_
  · split
    · unfold interrupt.deleting_irq_handler
      refine WP.spec_bind (interrupt.irq_slot.val s irq) fun isl eisl => ?_
      subst eisl
      have hW := irq_slotW hb hi
      unfold cdt.delete_one
      refine WP.spec_bind (WP.spec_and (P.irq Ac' s irq h.fr hb hi) (P.cap Ac' s _ h.fr hb hW)) fun c ⟨hc', hcd⟩ => ?_
      refine WP.spec_bind (P0.capability.Cap.is_null.p0 c) fun bn _ => ?_
      split
      · exact (WP.spec_ok _).2 h
      refine WP.spec_bind (P0.cdt.is_final_capability_with_cap.p0 st s _ c hS) fun f _ => ?_
      rcases hc' with rfl | ⟨n, b0, b1, b2, rfl⟩
      · simp [objects.finalise_cap_object]
        exact cdt.empty_slot.cur0 hA P h hW DelCapOK.null
      · obtain ⟨hn, hH⟩ := hcd.1.1.2.1 n b0 b1 b2 rfl
        refine WP.spec_bind (fin_ntfn_obj.cur0 (ar := ar) (a := a) (fin := f) (b0 := b0) (b1 := b1) (b2 := b2) h hn hH) ?_
        rintro ⟨_, s1, a1⟩ ⟨-, h1⟩
        exact cdt.empty_slot.cur0 hA P h1 hW DelCapOK.null
    · exact (WP.spec_ok _).2 h
  rintro ⟨s1, a1⟩ h1
  simp only at h1 ⊢
  unfold objects.finalise_cap_object
  dsimp only
  split
  · exact (WP.spec_ok _).2 ⟨h1, DelCapOK.null, hc⟩
  · exact (WP.spec_ok _).2 ⟨h1, DelCapOK.null, DelCapOK.null⟩

/-! ## The reply kind -/

/-- The frame of the reply kind for the thread `c` (the current thread): the
current thread and SC word kept, `c`'s `SC` field kept or cleared, the
action kept or `CHOOSE_NEW`, `c` not becoming blocked. -/
def CurR (st : machine.Store S) [L : LawfulStore st] (c : U64) (s s' : S) : Prop :=
  L.curW s' = L.curW s ∧ L.cscW s' = L.cscW s ∧
    (L.mem s' (scA c) = L.mem s (scA c) ∨ L.mem s' (scA c) = 0#u64) ∧
    (L.actionW s' = L.actionW s ∨ L.actionW s' = 1#u64) ∧
    (¬ BlockedR (L.mem s (stA c)) → ¬ BlockedR (L.mem s' (stA c)))

theorem CurR.refl (c : U64) (s : S) : CurR st c s s := ⟨rfl, rfl, Or.inl rfl, Or.inl rfl, id⟩

theorem CurR.trans {c : U64} {s₁ s₂ s₃ : S} (h₁ : CurR st c s₁ s₂) (h₂ : CurR st c s₂ s₃) : CurR st c s₁ s₃ := by
  obtain ⟨c1, s1, k1, a1, n1⟩ := h₁
  obtain ⟨c2, s2, k2, a2, n2⟩ := h₂
  refine ⟨c2.trans c1, s2.trans s1, ?_, ?_, fun h => n2 (n1 h)⟩
  · rcases k2 with e | e
    · rw [e]; exact k1
    · exact Or.inr e
  · rcases a2 with e | e
    · rw [e]; exact a1
    · exact Or.inr e

theorem CurR.of_curF {c : U64} {s s' : S} (hc : c ∈ T) (h : CurF st T s s')
    (ea : L.actionW s' = L.actionW s ∨ L.actionW s' = 1#u64) : CurR st c s s' :=
  ⟨h.1, h.2.1, Or.inl (h.2.2.1 c hc), ea, h.2.2.2 c hc⟩

theorem CurR.of_fr {c : U64} {s s' : S} (hc : c ∈ T) (f : Fr st T Sg s s') (ec : L.curW s' = L.curW s)
    (ea : L.actionW s' = L.actionW s ∨ L.actionW s' = 1#u64) : CurR st c s s' :=
  ⟨ec, f.csc, Or.inl (f.sc c hc), ea, fun h => by rw [f.st c hc]; exact h⟩

/-- A TCB field write of `y` other than `c`'s state; `c`'s `SC` field is
kept unless the write clears it. -/
theorem curR_wr_field {c : U64} {s : S} {y K v : U64} (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s))
    (hy : y ∈ T) (hc : c ∈ T) (hK : K.val < 4096) (hK8 : K.val % 8 = 0) (hKt : y = c → K.val ≠ 3328)
    (hKs : y = c → K.val = 3464 → v = 0#u64) :
    CurR st c s (L.wr s (core.num.U64.wrapping_add y K) v) := by
  have an := ani_field (v := v) hT hN hy hK hK8
  refine ⟨an.2.2, cscW_wr_field hT hN hy hK hK8, ?_, Or.inl an.1, fun hb => ?_⟩
  · by_cases e : y = c ∧ K.val = 3464
    · obtain ⟨rfl, hk⟩ := e
      have hK' : K = 3464#u64 := UScalar.eq_of_val_eq (by simp [hk])
      subst hK'
      right; rw [scA_eq, L.mem_wr_same (field_aligned (hT y hy) hK hK8)]; exact hKs rfl hk
    · left; rw [scA_eq]
      exact L.mem_wr_ne (field_aligned (hT y hy) hK hK8) (field_aligned (hT c hc) (by simp) (by simp))
        (fun e' => field_ne (hT y hy) (hT c hc) hK (by simp) (fun e'' => fun hk => e ⟨e'', by simpa using hk⟩)
          (UScalar.eq_of_val_eq e'))
  · rw [stA_eq, L.mem_wr_ne (field_aligned (hT y hy) hK hK8) (field_aligned (hT c hc) (by simp) (by simp))
      (fun e' => field_ne (hT y hy) (hT c hc) hK (by simp) (fun e'' => by simpa using hKt e'')
        (UScalar.eq_of_val_eq e')), ← stA_eq]; exact hb

theorem curR_wr_out {c : U64} {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {a v : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hc : c ∈ T) (ha : a ∈ Ω) : CurR st c s (L.wr s a v) :=
  CurR.of_curF hc (curF_wr_out h ha) (Or.inl (act_wr_out h ha))

/-- `reschedule_required`'s frame from the queues' invariant alone. -/
theorem sched.reschedule_required.curR {c : U64} {X : Set U64} (s : S) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hS : SgOK st Ω Sg s) (hc : c ∈ T) :
    sched.reschedule_required st s ⦃ s' => CurR st c s s' ⦄ := by
  unfold sched.reschedule_required
  step with sched.action.spec as ⟨act, act_post⟩
  refine WP.spec_bind (Pₘ := fun s1 => (∃ Q1 R1, SchedQueuesInvX st T Cs Ω H X s1 Q1 R1) ∧ CurR st c s s1)
    ?_ ?_
  · split
    · split
      · rename_i h1 h2
        have hT : act ∈ T := by
          rcases h.action with e | e | e
          · rw [← act_post] at e; exfalso; rw [e, resume_val] at h1; simp at h1
          · rw [← act_post] at e; exfalso; rw [e, choose_val] at h2; simp at h2
          · rw [← act_post] at e; exact e
        have hrun : Runnable (L.mem s (stA act)) := by
          have := (h.actOK (act_post ▸ hT)).1; rw [← act_post] at this; exact this
        step with sched.is_schedulable.spec as ⟨b, hb⟩
        split
        · have hc' := h.aff act hT
          have hp := h.prio act hT
          refine WP.spec_mono (WP.spec_and (sched.enqueue.inv s act Q R h hT (fun _ => hb ‹_›) (fun _ => hrun))
            (sched.enqueue.foot s act _ h.tcbs hT hp (h.nodes _ hc') (h.nodes _ h.cur) ((h.ready _ hc').1.rel _ hp)
              (fun h0 => h.notQ hT h0 hc' hp))) fun s1 hh => ?_
          obtain ⟨h1', hw, -⟩ := hh
          have hW : ∀ w ∈ act :: Q (L.mem s (affA act)) (L.mem s (prioA act)), w ∈ T := by
            intro w hw; rcases List.mem_cons.1 hw with rfl | hw
            · exact hT
            · exact h.memT hc' hp hw
          obtain ⟨fr, -, ea, ec, -⟩ := qfoot_keep h hS hW hc' hT p128 hw
          exact ⟨⟨_, _, h1'⟩, CurR.of_fr hc fr ec (Or.inl ea)⟩
        · exact (WP.spec_ok _).2 ⟨⟨Q, R, h⟩, CurR.refl _ _⟩
      · exact (WP.spec_ok _).2 ⟨⟨Q, R, h⟩, CurR.refl _ _⟩
    · exact (WP.spec_ok _).2 ⟨⟨Q, R, h⟩, CurR.refl _ _⟩
  · rintro s1 ⟨⟨Q1, R1, h1⟩, c1⟩
    refine WP.spec_mono (sched.set_action.spec s1 _) fun s2 e => ?_
    subst e
    have hT1 := h1.tcbs
    have hN1 := h1.nodes _ h1.cur
    have aA : Aligned (L.nodeAt s1 (L.cpu s1) layout.node.SCHED_ACTION) :=
      nodeAt_aligned hN1 (by rw [act_val]; omega) (by rw [act_val])
    have nf : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
        L.mem (L.wr s1 (L.nodeAt s1 (L.cpu s1) layout.node.SCHED_ACTION) sched.ACTION_CHOOSE_NEW)
          (core.num.U64.wrapping_add c K) = L.mem s1 (core.num.U64.wrapping_add c K) := fun K hK hK8 =>
      L.mem_wr_ne aA (field_aligned (hT1 c hc) hK hK8)
        (fun e => node_ne_field hN1 (by rw [act_val]; omega) hc (hT1 c hc) hK (UScalar.eq_of_val_eq e))
    refine c1.trans ⟨?_, ?_, Or.inl (by rw [scA_eq]; exact nf _ (by simp) (by simp)), Or.inr ?_,
      fun hb => by rw [stA_eq, nf _ (by simp) (by simp), ← stA_eq]; exact hb⟩
    · exact rd_cur_node h1 (by rw [act_val]; omega) (by rw [act_val]) (by rw [curth0]; omega) (by rw [curth0])
        (by rw [act_val, curth0]; omega)
    · unfold LawfulStore.cscW LawfulStore.nodeA
      exact rd_cur_node h1 (by rw [act_val]; omega) (by rw [act_val]) (by simp [layout.node.CUR_SC])
        (by simp [layout.node.CUR_SC]) (by rw [act_val]; simp [layout.node.CUR_SC])
    · unfold LawfulStore.actionW
      simp only [LawfulStore.cpu_wr, nodeAt_wr]
      rw [L.mem_wr_same aA]; simp [choose_val]

/-- **`donate`'s frame** for a thread `c` other than the receiver. -/
theorem schedcontext.donate.curR {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (sc dst c : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hsc : sc ∈ Scs) (hdst : dst ∈ T) (hc : c ∈ T)
    (hne : dst ≠ c)
    (hrv : L.mem s (runVcpuA dst) = 0#u64) :  -- a64: the receiver runs no VCPU
    schedcontext.donate st ar s a sc dst ⦃ s' _ => CurR st c s s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hT := h0.tcbs
  have hO := hX.1
  have hsub := hSg.sub
  have hm : scTcbA sc ∈ Ω := hSg.sub _ (hO.fixW sc hsc).1
  have hcO : scCoreA sc ∈ Ω := ((objs_omega hO hsub).2 sc hsc).2.1
  have hcSg : scCoreA sc ∈ Sg := (hO.fixW sc hsc).2
  unfold schedcontext.donate
  step with obj.Sc.tcb.spec as ⟨i, ei⟩
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => (∃ Q1 R1, SchedQueuesInv st T Cs Ω H r.1 Q1 R1) ∧
      SgOK st Ω Sg r.1 ∧ CurR st c s r.1 ∧ DbgTz st T Cs r.1 ∧
      L.mem r.1 (scCoreA sc) = L.mem s (scCoreA sc) ∧
      L.mem r.1 (runVcpuA dst) = L.mem s (runVcpuA dst)) ?_ ?_  -- a64
  · split
    · exact (WP.spec_ok _).2 ⟨⟨Q, R, h0⟩, hSg, CurR.refl _ _, hX.dbg, rfl, rfl⟩
    rename_i hb
    have hi0 : i ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    have hiT : i ∈ T := by rw [ei]; exact hX.2.2.yt.1 sc hsc (by rw [← ei]; exact hi0)
    refine WP.spec_bind (smp.remote_tcb_stall.all hA s a i h0 hB hX hS hSg) ?_
    rintro ⟨s2, a2⟩ ⟨h2, -, hX2, -, hSg2, ea2, ec2, -, ecs2, fk2, o2⟩
    try simp only [WP.uncurry'_pair]
    have C2 : CurR st c s s2 := ⟨ec2, ecs2, Or.inl (by rw [scA_eq]; exact fk2 c hc _ (by simp) (by simp)),
      Or.inl ea2, fun hb => by rw [stA_eq, fk2 c hc _ (by simp) (by simp), ← stA_eq]; exact hb⟩
    have D2 := hX2.dbg
    have c2 : L.mem s2 (scCoreA sc) = L.mem s (scCoreA sc) := o2 _ hcO
    have rv2 : L.mem s2 (runVcpuA dst) = L.mem s (runVcpuA dst) := fk2 dst hdst 3672#u64 (by simp) (by simp)  -- a64
    have hc2 := h2.aff i hiT
    have hp2 := h2.prio i hiT
    refine WP.spec_bind (WP.spec_and (sched.dequeue.inv s2 i Q R h2 hiT)
      (sched.dequeue.foot s2 i _ hT hiT hp2 (h2.nodes _ hc2) (h2.nodes _ h2.cur) ((h2.ready _ hc2).1.rel _ hp2)
        (h2.queued i hiT).1)) fun s3 hh3 => ?_
    obtain ⟨h3, hw3, -⟩ := hh3
    have hW2 : ∀ w ∈ Q (L.mem s2 (affA i)) (L.mem s2 (prioA i)), w ∈ T := fun w hw => h2.memT hc2 hp2 hw
    obtain ⟨fr3, -, ea3, ec3, -⟩ := qfoot_keep (Sg := Sg) h2 hSg2 hW2 hc2 hiT p128 hw3
    have C3 := C2.trans (CurR.of_fr hc fr3 ec3 (Or.inl ea3))
    have D3 := DbgTz.of_fr fr3 h2.nodes D2
    have c3 : L.mem s3 (scCoreA sc) = L.mem s (scCoreA sc) := (fr3.sig _ hcSg).trans c2
    have rv3 : L.mem s3 (runVcpuA dst) = L.mem s (runVcpuA dst) :=  -- a64
      (field_qfoot hT hW2 (h2.nodes _ hc2) (h2.nodes _ h2.cur) hiT hw3 hdst (K := 3672#u64) (by simp) (by simp)
        (by simp) (fun _ => by simp)).trans rv2
    have hSg3 : SgOK st Ω Sg s3 := hSg2.ksb' hw3.1
    have hc3 := h3.aff i hiT
    refine WP.spec_bind (WP.spec_and (sched.release_remove.inv s3 i _ R h3 hiT)
      (sched.release_remove.foot s3 i _ hT hiT (h3.nodes _ hc3) (h3.nodes _ h3.cur) (h3.release _ hc3)
        (h3.released i hiT).1)) fun s4 hh4 => ?_
    obtain ⟨h4, hw4, -⟩ := hh4
    have hW3 : ∀ w ∈ R (L.mem s3 (affA i)), w ∈ T := fun w hw => h3.memTR hc3 hw
    obtain ⟨fr4, -, ea4, ec4, -⟩ := qfoot_keep (Sg := Sg) h3 hSg3 hW3 hc3 hiT prel hw4
    have C4 := C3.trans (CurR.of_fr hc fr4 ec4 (Or.inl ea4))
    have D4 := DbgTz.of_fr fr4 h3.nodes D3
    have c4 : L.mem s4 (scCoreA sc) = L.mem s (scCoreA sc) := (fr4.sig _ hcSg).trans c3
    have rv4 : L.mem s4 (runVcpuA dst) = L.mem s (runVcpuA dst) :=  -- a64
      (field_qfoot hT hW3 (h3.nodes _ hc3) (h3.nodes _ h3.cur) hiT hw4 hdst (K := 3672#u64) (by simp) (by simp)
        (by simp) (fun _ => by simp)).trans rv3
    have hSg4 : SgOK st Ω Sg s4 := hSg3.ksb' hw4.1
    step with obj.Tcb.set_sc.wr as ⟨s5, e5⟩
    subst e5
    obtain ⟨h5, -, -⟩ := field_wr_keep (K := 3464#u64) (v := 0#u64) h4 hiT (by simp) (by simp) (by simp)
    have C5 := C4.trans (curR_wr_field (K := 3464#u64) (v := 0#u64) hT (h4.nodes _ h4.cur) hiT hc (by simp) (by simp)
      (fun _ => by simp) (fun _ _ => rfl))
    have hSg5 : SgOK st Ω Sg (L.wr s4 (core.num.U64.wrapping_add i 3464#u64) 0#u64) := hSg4.ksb' (L.ksb_wr _ _ _)
    have hfa : Aligned (core.num.U64.wrapping_add i 3464#u64) := field_aligned (hT i hiT) (by simp) (by simp)
    have D5 : DbgTz st T Cs (L.wr s4 (core.num.U64.wrapping_add i 3464#u64) 0#u64) :=
      DbgTz.wr_out hT h4.nodes hfa (notDbgW_field hT h4.nodes hiT (by simp) (by simp)) D4
    have hco4 := h4.omega _ hcO
    have c5 : L.mem (L.wr s4 (core.num.U64.wrapping_add i 3464#u64) 0#u64) (scCoreA sc) = L.mem s (scCoreA sc) :=
      (L.mem_wr_ne hfa hco4.1 (out_ne_field hco4 hiT (hT i hiT) (by simp))).trans c4
    have rv5 : L.mem (L.wr s4 (core.num.U64.wrapping_add i 3464#u64) 0#u64) (runVcpuA dst) =
        L.mem s (runVcpuA dst) :=  -- a64: the `SC` clear is another field
      (L.mem_wr_ne hfa (field_aligned (hT dst hdst) (by simp) (by simp))
        (fun e => field_ne (hT i hiT) (hT dst hdst) (by simp) (by simp) (fun _ => by simp)
          (UScalar.eq_of_val_eq e))).trans rv4
    step with sched.cur_thread.spec as ⟨t1, _⟩
    step with tcb_eq.blk as ⟨b1, _⟩
    refine WP.spec_bind (Pₘ := fun s6 => (∃ Q1 R1, SchedQueuesInv st T Cs Ω H s6 Q1 R1) ∧ SgOK st Ω Sg s6 ∧
        CurR st c s s6 ∧ DbgTz st T Cs s6 ∧ L.mem s6 (scCoreA sc) = L.mem s (scCoreA sc) ∧
        L.mem s6 (runVcpuA dst) = L.mem s (runVcpuA dst)) ?_
      fun s6 h6 => (WP.spec_ok _).2 h6
    have RR' : sched.reschedule_required st (L.wr s4 (core.num.U64.wrapping_add i 3464#u64) 0#u64) ⦃ s6 =>
        (∃ Q1 R1, SchedQueuesInv st T Cs Ω H s6 Q1 R1) ∧ SgOK st Ω Sg s6 ∧ CurR st c s s6 ∧
        DbgTz st T Cs s6 ∧ L.mem s6 (scCoreA sc) = L.mem s (scCoreA sc) ∧
        L.mem s6 (runVcpuA dst) = L.mem s (runVcpuA dst) ⦄ :=
      WP.spec_mono (WP.spec_and (WP.spec_and (WP.spec_and (sched.reschedule_required.kw (Sg := ∅) (Scs := ∅) (Z := Z)
        (Es := ∅) _ h5) (sched.reschedule_required.inv _ _ _ h5)) (sched.reschedule_required.curR _ _ _ h5 hSg5 hc))
        (sched.reschedule_required.rv0 _ h5))
        fun s6 ⟨⟨⟨f6, ⟨Q6, h6⟩, _, _⟩, i6⟩, r6⟩ => ⟨⟨_, _, h6⟩, hSg5.ksb' f6.1, C5.trans i6, Foot0.dbg hT h5.nodes f6 D5,
          (Foot0.out hT h5.nodes f6 (h5.omega _ hcO)).trans c5, (r6 dst hdst).trans rv5⟩
    split
    · exact RR'
    · step with sched.action.spec as ⟨ac, _⟩
      split
      · exact RR'
      · exact (WP.spec_ok _).2 ⟨⟨_, _, h5⟩, hSg5, C5, D5, c5, rv5⟩
  rintro ⟨s1, a1⟩ ⟨⟨Q1, R1, h1⟩, hSg1, i1, D1, c1, rv1⟩
  try simp only [WP.uncurry'_pair]
  refine WP.spec_mono (donate_tail.frame hA s1 a1 sc dst h1 D1 hO.ksb hsub hsc hdst
    (by rw [c1]; exact hX.2.2.core sc hsc) (rv1.trans hrv)) ?_
  rintro ⟨s', a'⟩ ⟨w, -⟩
  try simp only [WP.uncurry'_pair] at w ⊢
  obtain ⟨ec, -, ea, ecs, fk⟩ := donW_keeps hT h1.nodes h1.cur (h1.omega _ hm) hdst w
  have k : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3576 → K.val ≠ 3584 →
      L.mem s' (core.num.U64.wrapping_add c K) = L.mem s1 (core.num.U64.wrapping_add c K) :=
    fun K h1 h2 h3 h4 => fk c hc K h1 h2 h3 h4 (fun e => absurd e.symm hne)
  exact i1.trans ⟨ec, ecs, Or.inl (by rw [scA_eq]; exact k _ (by simp) (by simp) (by simp) (by simp)),
    Or.inl ea, fun hb => by rw [stA_eq, k _ (by simp) (by simp) (by simp) (by simp), ← stA_eq]; exact hb⟩


/-- `KeepT t` for a thread `u` other than `t`. -/
theorem curR_keepT {u t : U64} {s s' : S} (hu : u ∈ T) (hne : t ≠ u) (k : KeepT st T Cs Rp Scs Nt t s s') :
    CurR st u s s' :=
  ⟨k.curW, k.cscW, Or.inl (k.scf hu), k.act, fun hb => by
    rw [stA_eq, k.fld u hu _ (by simp) (by simp) (by simp) (by simp) (fun e => absurd e.symm hne), ← stA_eq]; exact hb⟩

theorem ipc.reply_pop.curR {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (r t u : U64)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hr : r ∈ Rp) (ht : t ∈ T) (hrt : L.mem s (rTcbA r) = t)
    (hst : L.mem s (stA t) = sched.TS_BLOCKED_ON_REPLY)
    (hb : headBit (L.mem s (rNextA r)) = true) (hn0 : L.mem s (rNextA r) &&& ~~~1#u64 ≠ 0#u64)
    (hu : u ∈ T) (hne : t ≠ u)
    (hrvt : L.mem s (runVcpuA t) = 0#u64) :  -- a64: the replier runs no VCPU (the donation's `hrv`)
    ipc.reply_pop st ar s a r t ⦃ res => CurR st u s res.1 ⦄ := by
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
  have G1 : Foot st T Cs Sg Scs Z ∅ s (L.wr s (scReplyA c) p) := foot_sgw (hal _ hcm) (hO.repW c hcS)
  have C1 : CurR st u s (L.wr s (scReplyA c) p) := curR_wr_out h0 hu hcm
  -- the new head takes `r`'s `NEXT` word
  refine WP.spec_bind (Pₘ := fun s2 => SchedQueuesInv st T Cs Ω H s2 Q R ∧ BoundInv st T Ac s2 ∧
      XInvR st T Cs Ω Sg Rp Scs Nt Z s2 ∧ SCsOK st T Ω Sg Scs Z Ac s2 ∧ SgOK st Ω Sg s2 ∧
      L.actionW s2 = L.actionW s ∧ L.idleW s2 = L.idleW s ∧
      (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
        L.mem s2 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ b ∈ Ω, (scReplyA c).val ≠ b.val → (p ≠ 0#u64 → (rNextA p).val ≠ b.val) → L.mem s2 b = L.mem s b) ∧
      L.mem s2 (scReplyA c) = p ∧ (p ≠ 0#u64 → L.mem s2 (rNextA p) = L.mem s (rNextA r)) ∧
      Foot st T Cs Sg Scs Z ∅ s s2 ∧ CurR st u s s2) ?_ ?_
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
        fun _ => L.mem_wr_same (hal _ (hrΩ p hpR').2.2), G1.trans (foot_sgw (hal _ (hrΩ p hpR').2.2) (hO.nextW hpR')),
        C1.trans (curR_wr_out h1 hu (hrΩ p hpR').2.2)⟩
      rw [o2 _ hcm hpn]; exact L.mem_wr_same (hal _ hcm)
    · rename_i hp0
      have hp0' : p = 0#u64 := UScalar.eq_of_val_eq (by simpa using hp0)
      exact (WP.spec_ok _).2 ⟨h1, hB1, hX1, hS1, hSg1, a1, i1, f1, fun b hb n1 _ => o1 b hb n1,
        L.mem_wr_same (hal _ hcm), fun h' => absurd hp0' h', G1, C1⟩
  intro s2 ⟨h2, hB2, hX2, hS2, hSg2, a2, i2, f2, o2, r2, n2, G2, C2⟩
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
  have C3 : CurR st u s (L.wr s2 (rNextA r) 0#u64) := C2.trans (curR_wr_out h2 hu (hrΩ r hr).2.2)
  have G3 : Foot st T Cs Sg Scs Z ∅ s (L.wr s2 (rNextA r) 0#u64) :=
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
  have rvt3 : L.mem (L.wr s2 (rNextA r) 0#u64) (runVcpuA t) = 0#u64 :=  -- a64
    (F3 t ht 3672#u64 (by simp) (by simp)).trans hrvt
  -- the donation back to `t`
  step with obj.Tcb.sc.spec as ⟨i, ei⟩
  have hk3 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s2 (rNextA r) 0#u64) := ⟨⟨Q, R, h3⟩, hB3, hX3', hS3, hSg3⟩
  have scs : L.mem s (scA t) ≠ 0#u64 → L.mem s (scA t) ∈ Ac := fun h0' =>
    hB.sact t ht (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hst)))))) h0'
  refine WP.spec_bind (Pₘ := fun res : S × A => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac res.1 ∧
      L.mem res.1 (stA t) = sched.TS_BLOCKED_ON_REPLY ∧ L.mem res.1 (replyA t) = r ∧
      FootD st T Cs Sg Scs Z ∅ (L.wr s2 (rNextA r) 0#u64) res.1 ∧
      (L.mem res.1 (scA t) ≠ 0#u64 → L.mem res.1 (scA t) ∈ Ac) ∧
      L.idleW res.1 = L.idleW (L.wr s2 (rNextA r) 0#u64) ∧ CurR st u s res.1) ?_ ?_
  · split
    · rename_i hi0
      have hsc0 : L.mem (L.wr s2 (rNextA r) 0#u64) (scA t) = 0#u64 := by rw [← ei]; exact hi0
      obtain ⟨dq, dr, da⟩ := blocked_out h3 ht (by rw [hst3]; exact not_runnable_reply)
      by_cases hf0 : L.mem (L.wr s2 (rNextA r) 0#u64) (scTcbA c) = 0#u64
      · refine WP.spec_mono (WP.spec_and (WP.spec_and (schedcontext.donate.unbound hA (X := ∅) _ a c t Q R h3 hB3 hX3' hS3 hSg3 ht dq dr
          hcS hn0 hf0 (hX3'.2.2.core c hcS) (fun _ => hcA) hsc0
          (fun e => hB3.idleNB (by rw [e, hst3]; exact Or.inr rfl)) rvt3)
          (schedcontext.donate.kw (Es := ∅) hA _ a c t hk3 hcS ht rvt3))
          (WP.spec_and (schedcontext.donate.idle hA _ a c t hk3 hcS ht rvt3)
            (schedcontext.donate.curR hA _ a c t u hk3 hcS ht hu hne rvt3))) ?_
        rintro ⟨s4, a4⟩ ⟨⟨⟨hk, st4, rp4, -, sc4, -, -⟩, fk⟩, id4, cu4⟩
        exact ⟨hk, by rw [st4 t ht]; exact hst3, by rw [rp4 t ht]; exact hrp3, fk, fun _ => by rw [sc4]; exact hcA, id4,
          C3.trans cu4⟩
      · have hfT := hX3'.2.2.yt.1 c hcS hf0
        have hscf := hX3'.2.2.tsc c hcS hn0 hf0
        refine WP.spec_mono (WP.spec_and (WP.spec_and (schedcontext.donate.gen hA _ a c t _ Q R h3 hB3 hX3' hS3 hSg3 hfT hscf hn0
          ?_ ht hsc0 dq dr da ?_ hcA (fun e => hB3.idleNB (by rw [e, hst3]; exact Or.inr rfl)) rvt3)
          (schedcontext.donate.kw (Es := ∅) hA _ a c t hk3 hcS ht rvt3))
          (WP.spec_and (schedcontext.donate.idle hA _ a c t hk3 hcS ht rvt3)
            (schedcontext.donate.curR hA _ a c t u hk3 hcS ht hu hne rvt3))) ?_
        · rw [i3, i2, tc3]; exact fun e => hci e.symm
        · intro e; rw [← e, hsc0] at hscf; exact hn0 hscf.symm
        · rintro ⟨s4, a4⟩ ⟨⟨⟨hk, st4, rp4, sc4⟩, fk⟩, id4, cu4⟩
          exact ⟨hk, by rw [st4 t ht]; exact hst3, by rw [rp4 t ht]; exact hrp3, fk, fun _ => by rw [sc4]; exact hcA, id4,
            C3.trans cu4⟩
    · exact (WP.spec_ok _).2 ⟨hk3, hst3, hrp3, WritesIn.refl _ _, by
        have e3 : L.mem (L.wr s2 (rNextA r) 0#u64) (scA t) = L.mem s (scA t) := by
          rw [scA_eq]; exact F3 t ht _ (by simp) (by simp)
        rw [e3]; exact scs, rfl, C3⟩
  rintro ⟨s4, a4⟩ ⟨hk4, st4, rp4, G4, sc4, id4, C4⟩
  try simp only [WP.uncurry'_pair]
  dsimp only at hk4 st4 rp4 G4 C4 ⊢
  refine WP.spec_bind (obj.Reply.set_prev.val s4 r 0#u64) fun s5 e5 => ?_
  rw [zero_or_masked] at e5
  subst e5
  have C5 : CurR st u s (L.wr s4 (rPrevA r) 0#u64) :=
    C4.trans (curR_wr_out hk4.1.choose_spec.choose_spec hu (hrΩ r hr).2.1)
  obtain ⟨hk5, -, id5, f5, -⟩ := rprev_wr_all hk4 hr (fun h0' => absurd zero_or_masked h0')
  have hst5 : L.mem (L.wr s4 (rPrevA r) 0#u64) (stA t) = sched.TS_BLOCKED_ON_REPLY := by
    rw [stA_eq, f5 t ht _ (by simp) (by simp), ← stA_eq]; exact st4
  have hrp5 : L.mem (L.wr s4 (rPrevA r) 0#u64) (replyA t) = r := by
    exact (f5 t ht 3360#u64 (by simp) (by simp)).trans rp4
  have hrt5 := (hk5.2.2.1.2.1.reply t ht hst5).2
  rw [hrp5] at hrt5
  have G5 : Foot st T Cs Sg Scs Z ∅ s4 (L.wr s4 (rPrevA r) 0#u64) :=
    foot_sgw (hal _ (hrΩ r hr).2.1) (hO.prevW hr)
  have sc5 : L.mem (L.wr s4 (rPrevA r) 0#u64) (scA t) = L.mem s4 (scA t) := by
    rw [scA_eq]; exact f5 t ht _ (by simp) (by simp)
  refine WP.spec_bind (ipc.reply_unlink.blk (Es := ∅) _ r t hk5 hr ht hrt5 hst5) ?_
  rintro s6 ⟨h6, e6, k6, -, G6⟩
  exact (WP.spec_ok _).2 (C5.trans (curR_keepT hu hne k6))

/-- **`reply_remove`'s frame** for a thread `u` other than the replier. -/
theorem ipc.reply_remove.curR {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (r t u : U64)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hr : r ∈ Rp) (ht : t ∈ T) (hrt : L.mem s (rTcbA r) = t)
    (hst : L.mem s (stA t) = sched.TS_BLOCKED_ON_REPLY) (hu : u ∈ T) (hne : t ≠ u)
    (hrvt : L.mem s (runVcpuA t) = 0#u64) :  -- a64: as `ipc.reply_pop.curR`
    ipc.reply_remove st ar s a r t ⦃ res => CurR st u s res.1 ⦄ := by
  have hX := h.2.2.1
  have hO := hX.1
  have ht0 : t ≠ 0#u64 := fun e0 => (h.1.choose_spec.choose_spec.tcbs t ht).ne0 (by rw [e0]; rfl)
  have hrp : L.mem s (replyA t) = r := by
    obtain ⟨-, -, b2, -⟩ := hX.2.1.back r hr (by rw [hrt]; exact ht0)
    rw [hrt] at b2; exact b2
  have W : ∀ {s₁ : S} {r' a' : U64}, BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s₁ →
      L.mem s₁ (stA t) = sched.TS_BLOCKED_ON_REPLY → L.mem s₁ (replyA t) = r → r' ∈ Rp →
      (a' = rPrevA r' ∨ a' = rNextA r') →
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s₁ a' 0#u64) ∧
        L.mem (L.wr s₁ a' 0#u64) (stA t) = sched.TS_BLOCKED_ON_REPLY ∧ L.mem (L.wr s₁ a' 0#u64) (replyA t) = r ∧
        CurR st u s₁ (L.wr s₁ a' 0#u64) :=
    fun {s₁ r' a'} h₁ e₁ e₂ hr' ha' => by
      obtain ⟨k, f⟩ := rword_wr0_all h₁ hr' ha'
      have hO₁ := h₁.2.2.1.1
      have hm : a' ∈ Ω := by
        rcases ha' with rfl | rfl
        · exact h₁.2.2.2.2.sub _ (hO₁.prevW hr')
        · exact h₁.2.2.2.2.sub _ (hO₁.nextW hr')
      exact ⟨k, by rw [stA_eq, f t ht _ (by simp) (by simp), ← stA_eq]; exact e₁,
        (f t ht 3360#u64 (by simp) (by simp)).trans e₂, curR_wr_out h₁.1.choose_spec.choose_spec hu hm⟩
  have tail : ∀ s₂ : S, BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s₂ →
      L.mem s₂ (stA t) = sched.TS_BLOCKED_ON_REPLY → L.mem s₂ (replyA t) = r →
      (do
        let s3 ← obj.Reply.set_prev st r s₂ 0#u64
        let s4 ← obj.Reply.set_next st r s3 0#u64 false
        let s5 ← ipc.reply_unlink st s4 r t
        ok (s5, a)) ⦃ res => CurR st u s₂ res.1 ⦄ := by
    intro s₂ h₂ e₂ r₂
    refine WP.spec_bind (obj.Reply.set_prev.val s₂ r 0#u64) fun s3 e3 => ?_
    rw [zero_or_masked] at e3; subst e3
    obtain ⟨h3, e3, r3, c3⟩ := W h₂ e₂ r₂ hr (Or.inl rfl)
    refine WP.spec_bind (obj.Reply.set_next.val0 _ r 0#u64) fun s4 e4 => ?_
    rw [zero_link] at e4; subst e4
    obtain ⟨h4, e4, r4, c4⟩ := W h3 e3 r3 hr (Or.inr rfl)
    have hrt4 := (h4.2.2.1.2.1.reply t ht e4).2
    rw [r4] at hrt4
    refine WP.spec_bind (ipc.reply_unlink.blk (Es := ∅) _ r t h4 hr ht hrt4 e4) ?_
    rintro s5 ⟨-, -, k5, -, -⟩
    exact (WP.spec_ok _).2 ((c3.trans c4).trans (curR_keepT hu hne k5))
  unfold ipc.reply_remove
  step with obj.Reply.next.spec as ⟨nx, enx⟩
  step with obj.Reply.prev.spec as ⟨pv, epv⟩
  subst nx pv
  have hpR : L.mem s (rPrevA r) &&& ~~~1#u64 ≠ 0#u64 → L.mem s (rPrevA r) &&& ~~~1#u64 ∈ Rp := hX.2.1.prev r hr
  have P : ∀ s₁ : S, BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s₁ →
      L.mem s₁ (stA t) = sched.TS_BLOCKED_ON_REPLY → L.mem s₁ (replyA t) = r →
      (do
        let s2 ← if (L.mem s (rPrevA r) &&& ~~~1#u64) != 0#u64
          then obj.Reply.set_next st (L.mem s (rPrevA r) &&& ~~~1#u64) s₁ 0#u64 false else ok s₁
        let s3 ← obj.Reply.set_prev st r s2 0#u64
        let s4 ← obj.Reply.set_next st r s3 0#u64 false
        let s5 ← ipc.reply_unlink st s4 r t
        ok (s5, a)) ⦃ res => CurR st u s₁ res.1 ⦄ := by
    intro s₁ h₁ e₁ r₁
    split
    · rename_i hp0
      refine WP.spec_bind (obj.Reply.set_next.val0 s₁ _ 0#u64) fun s2 e2 => ?_
      rw [zero_link] at e2; subst e2
      obtain ⟨h2, e2, r2, c2⟩ := W h₁ e₁ r₁ (hpR (by simpa using hp0)) (Or.inr rfl)
      exact WP.spec_mono (tail _ h2 e2 r2) fun r hr => c2.trans hr
    · simp only [Aeneas.Std.bind_ok]; exact tail s₁ h₁ e₁ r₁
  split
  · rename_i hn0
    have hn0' : L.mem s (rNextA r) &&& ~~~1#u64 ≠ 0#u64 := by simpa using hn0
    step with obj.Reply.next_is_head.spec as ⟨b, eb⟩
    split
    · rename_i hb
      have hb' : headBit (L.mem s (rNextA r)) = true := by rw [← eb]; exact hb
      exact ipc.reply_pop.curR hA s a r t u h hr ht hrt hst hb' hn0' hu hne hrvt
    · rename_i hb
      have hb' : headBit (L.mem s (rNextA r)) = false := by rw [← eb]; simpa using hb
      have hnR := (hX.2.1.next r hr hn0').2 hb'
      refine WP.spec_bind (obj.Reply.set_prev.val s _ 0#u64) fun s1 e1 => ?_
      rw [zero_or_masked] at e1; subst e1
      obtain ⟨h1, e1, r1, c1⟩ := W h hst hrp hnR (Or.inl rfl)
      exact WP.spec_mono (P _ h1 e1 r1) fun r hr => c1.trans hr
  · rename_i hn0
    simp only [Aeneas.Std.bind_ok]
    exact P s h hst hrp

/-- **The reply kind's finalisation** (`FinGaps.reply`). a64: from `DelPlaceAt` (its [J] `rv`, `RunVcpuInv`
along the deletion), so a `FinGapAt` at the deletion's start. -/
theorem finGap_reply {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop} {s0 : S}
    (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) :
    FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z (fun c => ∃ x1 x2, c = .Reply x1 x2) s0 := by
  intro Ac s a c fin h hc _ ⟨p, x, e⟩
  subst e
  have hp := hc.1.2.2 p x rfl
  obtain ⟨Ac', hb⟩ := h.bxi
  have hRV : RunVcpuInv st T s := P.rv Ac' s h.fr hb  -- a64: [J]
  have hb' := hb.blk
  have hct : L.curW s ∈ T := hb.1.choose_spec.choose_spec.curT
  have hnb := h.nb
  rw [fin_cap_eq_obj (by simp)]
  have CS : objects.finalise_cap_object st ar s a (.Reply p x) fin ⦃ r => CurR st (L.curW s) s r.2.1 ⦄ := by
    unfold objects.finalise_cap_object
    dsimp only
    split
    swap
    · exact (WP.spec_ok _).2 (CurR.refl _ _)
    refine WP.spec_bind (obj.Reply.tcb.blk s p) fun i ei => ?_
    step with obj.Tcb.is_null.spec as ⟨b, eb⟩
    split
    · exact (WP.spec_ok _).2 (CurR.refl _ _)
    rename_i hbn
    have hi0 : i ≠ 0#u64 := fun e => hbn (by rw [eb, e]; rfl)
    have hX := hb'.2.2.1
    obtain ⟨-, hiT, -, -⟩ := hX.2.1.back p hp (by rw [← ei]; exact hi0)
    rw [← ei] at hiT
    step with obj.Tcb.state.spec as ⟨v, ev⟩
    split
    · rename_i hv
      have hst : L.mem s (stA i) = sched.TS_BLOCKED_ON_REPLY := by rw [← ev, hv]
      have hne : i ≠ L.curW s := fun e => hnb (by rw [← e, hst]; exact Or.inr rfl)
      refine WP.spec_bind (ipc.reply_remove.curR hA s a p i _ hb' hp hiT ei.symm hst hct hne
        (hRV.zero hiT fun e => not_runnable_reply (by rw [← hst, e]; exact Or.inr (Or.inr rfl)))) ?_
      rintro ⟨s1, a1⟩ c1
      exact (WP.spec_ok _).2 c1
    split
    · rename_i _ hv
      obtain ⟨⟨Q, R, h0⟩, hB, -, hS, hSg⟩ := hb'
      refine WP.spec_bind (ipc.cancel_ipc.all s a i Q R h0 hiT hB hX hSg.sub) ?_
      rintro ⟨s1, a1⟩ ⟨-, -, -, hnb1, hnr1, -, k1, -⟩
      refine (WP.spec_ok _).2 ⟨k1.curW, k1.cscW, Or.inl (k1.scf hct), k1.act, fun hb0 => ?_⟩
      by_cases e : i = L.curW s
      · rw [← e]; exact fun h' => h'.elim hnb1 hnr1
      · rw [stA_eq, k1.fld _ hct _ (by simp) (by simp) (by simp) (by simp) (fun e' => absurd e'.symm e),
          ← stA_eq]; exact hb0
    · exact (WP.spec_ok _).2 (CurR.refl _ _)
  refine WP.spec_mono (WP.spec_and (fin_reply.blk hA s a p x fin hb' hp hRV) CS) ?_
  rintro ⟨⟨r1, r2⟩, s', a'⟩ ⟨⟨e, hb2, f2⟩, ec, ecs, esc, ea, enb⟩
  simp only at e hb2 f2 ec ecs esc ea enb ⊢
  cases e
  exact ⟨Cur0.mk h (BlkOK.bxi hb2) ec ecs esc ea (Or.inr (enb hnb)) (FootD.cur0w f2 le_rfl), DelCapOK.null,
    DelCapOK.null⟩

end

end Fl4ProofsA64.P1
