/-
P3 (p3J gen 37): **a notification cap's finalisation in `KWN ∅ False`** (P1 QueueFinal's `fin_ntfn.blk` walk
mirrored at `Kp = ∅`, `Nd = False`, `Es = EH H`, as gen 31's P3JRecvFtN mirrored `cancel_ipc`). P2-level, namespace
`Fl4Proofs.P1`, FL4 only.

P1's `fin_cap_ntfn.slots` gives a `Foot` (`KW`) footprint. `KW` allows every core's node words but `88`, in
particular other cores' `IDLE_THREAD` / `IDLE_SC` (offsets 8 / 32), which `Mc.ProjW` excludes. Here every step of
the finalisation (FL4 `objects.rs` `finalise_cap_object`, the `Notification` arm: `maybe_unbind_ntfn`,
`unbind_maybe_notification`, `cancel_all_signals` — `notification.rs` l.194-202 for the loop) is shown in `KWN ∅
False` (no node identity word written), so P3JMcKwN's `kwN_projW` applies:

* `schedcontext.unbind_ntfn.kwN0`, `schedcontext.maybe_unbind_ntfn.kwN0`,
  `notification.unbind_maybe_notification.kwN0`: `Sg` words (`footN0_sgw`) and the TCB's bound-notification field
  (P2's `footN_field`).
* `cas_roundN0` (P1's `cas_round` with the `FootN` conjunct: the dequeue by P2's `EpFoot.kwN`, the restart by
  `set_thread_state.kwNP`, `unblock_sporadic.kwN`, `possible_switch_to.kwN`),
  `notification.cancel_all_signals_loop.kwN0`, `notification.cancel_all_signals.kwN0` (`reschedule_required.kwN`).
* **`fin_ntfn.kwN0`**, **`fin_cap_ntfn.kwN0`**.

`AcK` is vacuous at `Kp = ∅`. No premise; no sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JRecvFtN
import Fl4Proofs.P1.QueueFinCap
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P2.Stall

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}
variable {Ac : Set U64} {Es : Set U64}

/-- (p3J gen 37) `unbind_ntfn` in `KWN ∅ False` (P1 `unbind_ntfn.blk`). -/
theorem schedcontext.unbind_ntfn.kwN0 (s : S) (c : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hc : c ≠ 0#u64 → c ∈ Scs) :
    schedcontext.unbind_ntfn st s c ⦃ s' => FootN st ∅ False T Cs Sg Scs Z Es s s' ⦄ := by
  unfold schedcontext.unbind_ntfn
  step with obj.Sc.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 (FootN.refl _)
  rename_i hb
  have hc0 : c ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
  have hcS : c ∈ Scs := hc hc0
  step with obj.Sc.ntfn.val as ⟨j, ej⟩
  split
  · rename_i hj
    have hjN : j ∈ Nt := by rw [ej]; exact h.2.2.1.2.2.scn c hcS (by rw [← ej]; simpa using hj)
    have hO := h.2.2.1.1
    have h0 := h.1.choose_spec.choose_spec
    have hsub := h.2.2.2.2.sub
    refine WP.spec_bind (obj.Ntfn.set_sc.wr s j 0#u64) fun s1 e1 => ?_
    subst e1
    refine WP.spec_mono (obj.Sc.set_ntfn.wr _ c 0#u64) fun s2 e2 => ?_
    subst e2
    exact (footN0_sgw h0 hsub rfl rfl (h0.omega _ (hsub _ (hO.ntW j hjN))).1 (hO.ntW j hjN)).trans
      (footN0_sgw h0 hsub (by rw [L.ksb_wr]) (by rw [L.cpu_wr]) (h0.omega _ (hsub _ (hO.snW c hcS))).1 (hO.snW c hcS))
  · exact (WP.spec_ok _).2 (FootN.refl _)

/-- (p3J gen 37) `maybe_unbind_ntfn` in `KWN ∅ False`. -/
theorem schedcontext.maybe_unbind_ntfn.kwN0 (s : S) (n : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hn : n ∈ Nt) :
    schedcontext.maybe_unbind_ntfn st s n ⦃ s' => FootN st ∅ False T Cs Sg Scs Z Es s s' ⦄ := by
  unfold schedcontext.maybe_unbind_ntfn
  step with obj.Ntfn.sc.val as ⟨i, ei⟩
  step with obj.Sc.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 (FootN.refl _)
  · exact schedcontext.unbind_ntfn.kwN0 s i h fun h0 => by
      rw [ei]; exact (h.2.2.1.2.2.nsc n hn (by rw [← ei]; exact h0)).1

/-- (p3J gen 37) `unbind_maybe_notification` in `KWN ∅ False`. -/
theorem notification.unbind_maybe_notification.kwN0 (s : S) (n : U64)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hn : n ∈ Nt) :
    notification.unbind_maybe_notification st s n ⦃ s' => FootN st ∅ False T Cs Sg Scs Z Es s s' ⦄ := by
  unfold notification.unbind_maybe_notification
  refine WP.spec_bind (obj.Ntfn.bound_tcb.val s n) fun i ei => ?_
  refine WP.spec_bind (obj.Tcb.is_null.spec i) fun b eb => ?_
  subst eb
  split
  · exact (WP.spec_ok _).2 (FootN.refl _)
  · rename_i hb
    have hiT : i ∈ T := by
      rcases (show Tz T i by rw [ei]; exact h.2.2.1.2.2.ntb n hn) with e | e
      · exact absurd (by simp [e]) hb
      · exact e
    have h0 := h.1.choose_spec.choose_spec
    have hT := h0.tcbs
    have hsub := h.2.2.2.2.sub
    have hm : ntfnBtA n ∈ Sg := (h.2.2.1.1.ntB n hn).2
    refine WP.spec_bind (obj.Ntfn.set_bound_tcb.wr s n 0#u64) fun s1 e1 => ?_
    subst e1
    refine WP.spec_mono (obj.Tcb.set_bound_ntfn.wr _ i 0#u64) fun s2 e2 => ?_
    subst e2
    exact (footN0_sgw h0 hsub rfl rfl (h0.omega _ (hsub _ hm)).1 hm).trans
      (footN_field (K := 3368#u64) hT (fun c hc => (h0.nodes c hc).ksb (L.ksb_wr _ _ _))
        (by rw [L.cpu_wr]; exact h0.cur) hiT (by simp) (by simp) (by simp) (by simp))

set_option maxHeartbeats 4000000 in
/-- (p3J gen 37) **P1's `cas_round` with its `KWN ∅ False` footprint** (module docstring). -/
theorem cas_roundN0 {β : Type _} (s : S) (n t : U64) (fuel1 : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hH : H n = some .ntfn) (hst : L.epState s n = 1#u64) (hhd : (L.epQ s n).head = t) :
    (do
      let next ← tcbqueue.next_of st s .Ep t
      let s1 ← notification.ntfn_dequeue st s n t
      let s2 ← sched.set_thread_state st s1 t sched.TS_RESTART
      let s3 ← notification.unblock_sporadic st s2 t
      let s4 ← sched.possible_switch_to st s3 t
      ok (ControlFlow.cont (β := β) (s4, next, fuel1))) ⦃ r => ∃ s4 next, r = .cont (s4, next, fuel1) ∧
        BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s4 ∧ FootN st ∅ False T Cs Sg Scs Z (EH H) s s4 ∧
        (next ≠ 0#u64 → L.epState s4 n = 1#u64 ∧ (L.epQ s4 n).head = next) ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hT := h0.tcbs
  obtain ⟨hdT, hbe, hds⟩ := ntfn_head h0 hH hst
  rw [hhd] at hdT hbe hds
  have hta := hT t hdT
  obtain ⟨E, EQ, hEW⟩ := h0.eps
  have heE : n ∈ E := (hEW.2.2.2.2.2.2.2.1 n).2 (Or.inr hH)
  obtain ⟨hE, hEN, hq⟩ := hEW.1 n heE
  have hEΩ := hEW.2.2.1 n heE
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
  have F1 : FootN st ∅ False T Cs Sg Scs Z (EH H) s s1 :=
    FootN.of' w1 (fun b _ hb => EpFoot.kwN hT h0.nodes hq.mem (Or.inr hH) hE hEN hEΩ (hdrΩ_of hX hSg.sub) hb)
      (AcK.of_eq (EpFoot.act hT h0.nodes h0.cur hq.mem hE hEN w1))
  have hnd := hq.nodup
  have herase : (y :: ys).erase y = ys := List.erase_cons_head y ys
  rw [herase] at hq1 hst1
  have tm1 : TmFr st T Cs Nt s s1 := TmFr.mk0 ⟨k1, fun y hy K a b c => f1 y hy K (by omega) c (by omega) (by omega),
    fun c hc o ho => nc1 c hc o (by omega) (by omega), fun n' hn' => o1 _ (hSg.sub _ (hX.1.ntB n' hn').2)⟩
  obtain ⟨hB1, hX1, hS1, hSg1, ea1, ec1, ei1⟩ := frame_bx h0 hB hX hS hSg f1 o1 n1 k1 tm1
  have st1 : L.mem s1 (stA y) = sched.TS_BLOCKED_ON_NTFN := by
    rw [stA_eq, f1 y hdT _ (by simp) (by simp) (by simp) (by simp), ← stA_eq]; exact hds
  have fw1 : Foot st T Cs Sg Scs Z {n} s s1 := Foot.of w1 fun b hb => hb.kw hq.mem rfl
  obtain ⟨-, -, r3, -, r6⟩ := ts_vals
  refine WP.spec_bind (WP.spec_and (WP.spec_and (sts_all s1 y _ Q R h1 hB1 hX1 hS1 hSg1 hdT not_blocked_restart
    restart_ne (Or.inl (Or.inr rfl)) (hX1.noref hta (by rw [st1]; exact blocked_ne_reply (Or.inr (Or.inr rfl)))
      (by rw [st1, r3, r6]; decide))
    ⟨fun _ _ _ _ _ => runnable_restart, fun _ _ _ => runnable_restart, fun _ => runnable_restart⟩)
    (sched.set_thread_state.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) s1 y _ h1 hdT))
    (sched.set_thread_state.kwNP (Sg := Sg) (Kp := ∅) (Nd := False) (Scs := Scs) (Z := Z) (Es := EH H) s1 y _ hT
      h1.nodes h1.cur hdT (Set.notMem_empty _))) ?_
  rintro s2 ⟨⟨⟨h2, hB2, hX2, hS2, hSg2, st2, k2⟩, fw2⟩, F2⟩
  have h2' : SchedQueuesInv st T Cs Ω H s2 Q R := h2.congrX empty_congr'
  refine WP.spec_bind (WP.spec_and (WP.spec_and (endpoint.unblock_sporadic.all s2 y h2' hB2 hX2 hS2 hSg2 hdT)
    (notification.unblock_sporadic.kw (Es := ∅) s2 y h2' hX2 hS2 hdT))
    (notification.unblock_sporadic.kwN (Kp := ∅) (Nd := False) (Es := EH H) s2 y h2' hX2 hS2 hdT)) ?_
  rintro s3 ⟨⟨⟨h3, hB3, hX3, hS3, hSg3, -, -, -, fk3, -⟩, fw3⟩, F3⟩
  have st3 : L.mem s3 (stA y) = sched.TS_RESTART := by
    rw [stA_eq, fk3 y hdT _ (by simp) (by simp), ← stA_eq]; exact st2
  have esc3 : L.mem s3 (scA y) = L.mem s (scA y) := by
    rw [scA_eq, fk3 y hdT _ (by simp) (by simp), ← scA_eq, k2.scf hdT, scA_eq,
      f1 y hdT _ (by simp) (by simp) (by simp) (by simp)]
  refine WP.spec_bind (WP.spec_and (WP.spec_and (sched.possible_switch_to.sch (Sg := Sg) s3 y Q R h3 hB3 hSg3 hdT
    (by rw [st3]; exact runnable_restart) (by rw [esc3]; exact hyA))
    (sched.possible_switch_to.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) s3 y h3 hdT))
    (sched.possible_switch_to.kwN (Sg := Sg) (Kp := ∅) (Nd := False) (Scs := Scs) (Z := Z) (Es := EH H) s3 y h3 hdT
      (Set.notMem_empty _) (fun _ => Set.notMem_empty _))) ?_
  rintro s4 ⟨⟨⟨p4, -, -⟩, fw4⟩, F4⟩
  have f14 : Foot st T Cs Sg Scs Z ∅ s1 s4 := fw2.trans (fw3.trans fw4)
  obtain ⟨eh, et⟩ := f14.epQ h1 hX1.1 hSg1.sub (Or.inr hH)
  refine (WP.spec_ok _).2 ⟨s4, next, rfl, ⟨p4.inv, p4.bnd, hX3.fr p4.fr, hS3.fr p4.fr, hSg3.fr p4.fr⟩,
    F1.trans (F2.trans (F3.trans F4)), fun hn0 => ?_⟩
  have hys0 : ys ≠ [] := fun e => hn0 (by rw [enext, hnext, e]; rfl)
  have es : L.epState s4 n = L.epState s1 n := by simp only [LawfulStore.epState, et]
  refine ⟨by rw [es, hst1, if_neg hys0, hst], ?_⟩
  rw [show (L.epQ s4 n).head = L.mem s4 (epHeadA n) from rfl, eh, show L.mem s1 (epHeadA n) = (L.epQ s1 n).head
    from rfl, hq1.head, enext, hnext]

/-- (p3J gen 37) The `cancel_all_signals` loop in `KWN ∅ False` (P1 `cancel_all_signals_loop.blk`). -/
theorem notification.cancel_all_signals_loop.kwN0 (s0 s : S) (n t fuel : U64)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hH : H n = some .ntfn)
    (hf : FootN st ∅ False T Cs Sg Scs Z (EH H) s0 s)
    (ht : t ≠ 0#u64 → L.epState s n = 1#u64 ∧ (L.epQ s n).head = t) :
    notification.cancel_all_signals_loop st s n t fuel ⦃ s' =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ FootN st ∅ False T Cs Sg Scs Z (EH H) s0 s' ⦄ := by
  unfold notification.cancel_all_signals_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.2.val)
    (inv := fun x => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac x.1 ∧ FootN st ∅ False T Cs Sg Scs Z (EH H) s0 x.1 ∧
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
      refine WP.spec_mono (cas_roundN0 (β := S) s1 n t1 fuel1 hb1 hH hst1 hhd1) ?_
      rintro r ⟨s4, next, rfl, hb4, hf4, hn4⟩
      exact ⟨hb4, hf1.trans hf4, hn4, by simp only; omega⟩
    · exact (WP.spec_ok _).2 ⟨hb1, hf1⟩
  · exact ⟨h, hf, ht⟩

/-- (p3J gen 37) `cancel_all_signals` in `KWN ∅ False` (P1 `cancel_all_signals.blk`). -/
theorem notification.cancel_all_signals.kwN0 (s : S) (n : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hH : H n = some .ntfn) :
    notification.cancel_all_signals st s n ⦃ s' => FootN st ∅ False T Cs Sg Scs Z (EH H) s s' ⦄ := by
  unfold notification.cancel_all_signals
  step with obj.Ntfn.state.spec as ⟨v, hv⟩
  split
  · exact (WP.spec_ok _).2 (FootN.refl _)
  rename_i hw
  have hst : L.epState s n = 1#u64 := by
    rw [← hv]; have := hw; simp [obj.NTFN_WAITING] at this; exact UScalar.eq_of_val_eq (by simpa using this)
  step with notification.get_queue.spec as ⟨q, eq⟩
  subst eq
  refine WP.spec_bind (notification.cancel_all_signals_loop.kwN0 s s n _ _ h hH (FootN.refl _)
    (fun _ => ⟨hst, rfl⟩)) ?_
  rintro s1 ⟨h1, f1⟩
  exact WP.spec_mono (sched.reschedule_required.kwN (Kp := ∅) (Nd := False) (Sg := Sg) (Scs := Scs) (Z := Z)
    (Es := EH H) s1 h1.1.choose_spec.choose_spec (fun _ => Set.notMem_empty _)) fun s2 f2 => f1.trans f2

/-- (p3J gen 37) **A notification cap's object finalisation in `KWN ∅ False`** (P1 `fin_ntfn.blk`). -/
theorem fin_ntfn.kwN0 {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (n b0 b1 b2 : _)
    (fin : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hn : n ∈ Nt) (hH : H n = some .ntfn) :
    objects.finalise_cap_object st ar s a (.Notification n b0 b1 b2) fin ⦃ r =>
      FootN st ∅ False T Cs Sg Scs Z (EH H) s r.2.1 ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  split
  · refine WP.spec_bind (WP.spec_and (schedcontext.maybe_unbind_ntfn.blk s n h hn)
      (schedcontext.maybe_unbind_ntfn.kwN0 (Es := EH H) s n h hn)) ?_
    rintro s1 ⟨⟨h1, -⟩, f1⟩
    refine WP.spec_bind (WP.spec_and (notification.unbind_maybe_notification.blkF s1 n h1 hn)
      (notification.unbind_maybe_notification.kwN0 (Es := EH H) s1 n h1 hn)) ?_
    rintro s2 ⟨⟨h2, -⟩, f2⟩
    refine WP.spec_bind (notification.cancel_all_signals.kwN0 s2 n h2 hH) fun s3 f3 => ?_
    exact (WP.spec_ok _).2 (f1.trans (f2.trans f3))
  · exact (WP.spec_ok _).2 (FootN.refl _)

/-- (p3J gen 37) **`finalise_cap` of a notification cap in `KWN ∅ False`** (module docstring). -/
theorem fin_cap_ntfn.kwN0 {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (n : U64) (b0 b1 b2 : _)
    (fin ex : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hn : n ∈ Nt) (hH : H n = some .ntfn) :
    objects.finalise_cap st ar s a (.Notification n b0 b1 b2) fin ex ⦃ r =>
      FootN st ∅ False T Cs Sg Scs Z (EH H) s r.2.1 ⦄ := by
  rw [fin_cap_eq_obj (by simp)]
  exact fin_ntfn.kwN0 s a n b0 b1 b2 fin h hn hH

end

end Fl4Proofs.P1
