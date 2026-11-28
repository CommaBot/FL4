/-
P3 (p3J gen 42): **an endpoint cap's finalisation in `KWN ∅ False`, hence inside `ProjW`** — bucket 3's first
per-kind finaliser footprint after the notification one (gen 37, P3JNtfnFt). P1 QueueFinal's `cai_round` /
`cancel_all_ipc_loop.blk` / `cancel_all_ipc.blk` / `fin_endpoint.blk` walk mirrored at `Kp = ∅`, `Nd = False`,
`Es = EH H` (as P3JCbsFt mirrored `cancel_badged_sends`). FL4 `objects.rs` `finalise_cap_object`, the `Endpoint` arm
(`cancel_all_ipc` when final; `endpoint.rs` `cancel_all_ipc`: the queue walk, `ep_dequeue`, the receiver's
`reply_unlink`, `restart_thread_if_no_fault`, then `reschedule_required`).

* `cai_roundN0` (proof text of `cai_round` with the `FootN` conjunct threaded: the dequeue by P2's `EpFoot.kwN` /
  `EpFoot.act`, `reply_unlink` by P2's `ipc.reply_unlink.kwN`, the restart by P3JCbsFt's
  `restart_thread_if_no_fault.kwN0`), `endpoint.cancel_all_ipc_loop.kwN0`, **`endpoint.cancel_all_ipc.kwN0`**
  (`reschedule_required.kwN`).
* **`fin_endpoint.kwN0`**, **`fin_cap_ep.kwN0`** (`fin_cap_eq_obj`).
* P3: **`JAtZ.caiProjW`**, **`JAtZ.finEpProjW`**: at a `JAtZ` state, for an endpoint of `Z.E`, these write only
  `ProjW H Cs s` (P3JMcKwN's `kwN_projW`).

`AcK` is vacuous at `Kp = ∅`. No premise; no sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JThFpuR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P2.Stall

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}
variable {Ac : Set U64}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 42) **P1's `cai_round` with its `KWN ∅ False` footprint** (module docstring). -/
theorem cai_roundN0 {β : Type _} (s : S) (ep t : U64) (fuel1 : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
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
        BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s3 ∧ Foot st T Cs Sg Scs Z {ep} s s3 ∧ FootN st ∅ False T Cs Sg Scs Z (EH H) s s3 ∧
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
  obtain ⟨hE, hEN, hq⟩ := hEW.1 ep heE
  have hEΩ := hEW.2.2.1 ep heE
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
  have st1 : L.mem s1 (stA y) = L.mem s (stA y) := by
    rw [stA_eq]; exact f1 y hdT _ (by simp) (by simp) (by simp) (by simp)
  have rp1 : L.mem s1 (replyA y) = L.mem s (replyA y) := f1 y hdT _ (by simp) (by simp) (by simp) (by simp)
  have fw1 : Foot st T Cs Sg Scs Z {ep} s s1 := Foot.of w1 fun b hb => hb.kw hq.mem rfl
  have F1 : FootN st ∅ False T Cs Sg Scs Z (EH H) s s1 :=
    FootN.of' w1 (fun b _ hb => EpFoot.kwN hT h0.nodes hq.mem (Or.inl hH) hE hEN hEΩ (hdrΩ_of hX hSg.sub) hb)
      (AcK.of_eq (EpFoot.act hT h0.nodes h0.cur hq.mem hE hEN w1))
  have da1 : L.actionW s1 ≠ y := by rw [ea1]; exact da
  have hyA1 : L.mem s1 (scA y) ≠ 0#u64 → L.mem s1 (scA y) ∈ Ac := by
    have esc1 : L.mem s1 (scA y) = L.mem s (scA y) := by
      rw [scA_eq]; exact f1 y hdT _ (by simp) (by simp) (by simp) (by simp)
    rw [esc1]; exact hB.sact y hdT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hbl))))))
  -- the rest of the round, from a state `s2` with a `KW ∅` footprint from `s1`
  have tail : ∀ (s2 : S), Foot st T Cs Sg Scs Z ∅ s1 s2 → FootN st ∅ False T Cs Sg Scs Z (EH H) s1 s2 →
      endpoint.restart_thread_if_no_fault st s2 y ⦃ s' =>
        BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ Foot st T Cs Sg Scs Z ∅ s2 s' ⦄ →
      endpoint.restart_thread_if_no_fault st s2 y ⦃ s' => FootN st ∅ False T Cs Sg Scs Z (EH H) s2 s' ⦄ →
      (do
        let s3 ← endpoint.restart_thread_if_no_fault st s2 y
        ok (ControlFlow.cont (β := β) (s3, next, fuel1))) ⦃ r => ∃ s3 next', r = .cont (s3, next', fuel1) ∧
          BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s3 ∧ Foot st T Cs Sg Scs Z {ep} s s3 ∧ FootN st ∅ False T Cs Sg Scs Z (EH H) s s3 ∧
          (next' ≠ 0#u64 → (L.epState s3 ep = 1#u64 ∨ L.epState s3 ep = 2#u64) ∧ (L.epQ s3 ep).head = next') ⦄ := by
    intro s2 fw2 F2 hr hrN
    refine WP.spec_bind (WP.spec_and hr hrN) fun s3 ⟨⟨hb3, fw3⟩, F3⟩ => ?_
    have f13 : Foot st T Cs Sg Scs Z ∅ s1 s3 := fw2.trans fw3
    obtain ⟨eh, et⟩ := f13.epQ h1 hX1.1 hSg1.sub (Or.inl hH)
    refine (WP.spec_ok _).2 ⟨s3, next, rfl, hb3, fw1.trans (f13.mono (Set.empty_subset _)),
      F1.trans (F2.trans F3), fun hn0 => ?_⟩
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
      refine WP.spec_bind (WP.spec_and (WP.spec_and (ipc.reply_unlink.inv s1 i1 y Q R h1 hdT hX1.1 hSg1.sub hr hrt
        (by rw [st1]; exact hnrun) (Or.inl (Or.inr rfl)))
        (ipc.reply_unlink.kw (Scs := Scs) (Es := ∅) s1 i1 y h1 hX1 hSg1.sub hr hdT))
        (ipc.reply_unlink.kwN (Kp := ∅) (Nd := False) (Es := EH H) s1 i1 y h1 hX1 hSg1.sub hr hdT
          (Set.notMem_empty _))) ?_
      rintro s2 ⟨⟨⟨h2, e2, k2, z2⟩, fw2⟩, F2⟩
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
      exact tail s2 fw2 F2 (endpoint.restart_thread_if_no_fault.blk s2 y h2 (fun z hz => by obtain ⟨hz1, hz2⟩ := hz; exact absurd (cg1 z hz1) hz2) hB2 hX2 hS2 hSg2 hdT
        (Or.inr (by rw [e2]; exact not_blocked_inactive))
        (hX2.noref hta (by rw [e2]; exact inactive_ne.1) (by rw [e2]; exact inactive_ne.2)) hnQ hnR da2
        (by rw [k2.scf hdT]; exact hyA1))
        (endpoint.restart_thread_if_no_fault.kwN0 s2 y h2 (fun z hz => by obtain ⟨hz1, hz2⟩ := hz; exact absurd (cg1 z hz1) hz2) hB2 hX2 hS2 hSg2 hdT
        (Or.inr (by rw [e2]; exact not_blocked_inactive))
        (hX2.noref hta (by rw [e2]; exact inactive_ne.1) (by rw [e2]; exact inactive_ne.2)) hnQ hnR da2)
    · rename_i hi1
      have hz : i1 = 0#u64 := by apply UScalar.eq_of_val_eq; simpa using hi1
      have hi10 : L.mem s1 (replyA y) = 0#u64 := by rw [← ei1]; exact hz
      simp only [Aeneas.Std.bind_ok]
      exact tail s1 (Foot.refl _) (FootN.refl _) (endpoint.restart_thread_if_no_fault.blk s1 y h1 cg1 hB1 hX1 hS1
        hSg1 hdT (Or.inl (Or.inr rfl)) (hX1.noref0 hta hi10) hnQ hnR da1 hyA1)
        (endpoint.restart_thread_if_no_fault.kwN0 s1 y h1 cg1 hB1 hX1 hS1 hSg1 hdT
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
    exact tail s1 (Foot.refl _) (FootN.refl _) (endpoint.restart_thread_if_no_fault.blk s1 y h1 cg1 hB1 hX1 hS1
      hSg1 hdT (Or.inl (Or.inr rfl)) (hX1.noref hta (by rw [hsend]; exact nrp) (by rw [hsend]; exact nrc)) hnQ hnR da1
      hyA1)
      (endpoint.restart_thread_if_no_fault.kwN0 s1 y h1 cg1 hB1 hX1 hS1 hSg1 hdT
      (Or.inl (Or.inr rfl)) (hX1.noref hta (by rw [hsend]; exact nrp) (by rw [hsend]; exact nrc)) hnQ hnR da1)

set_option maxHeartbeats 4000000 in
/-- (p3J gen 42) The `cancel_all_ipc` loop in `KWN ∅ False` (P1 `cancel_all_ipc_loop.blk`). -/
theorem endpoint.cancel_all_ipc_loop.kwN0 (s0 s : S) (ep t fuel : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hH : H ep = some .ep) (hf : FootN st ∅ False T Cs Sg Scs Z (EH H) s0 s)
    (ht : t ≠ 0#u64 → (L.epState s ep = 1#u64 ∨ L.epState s ep = 2#u64) ∧ (L.epQ s ep).head = t) :
    endpoint.cancel_all_ipc_loop st s ep t fuel ⦃ s' =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ FootN st ∅ False T Cs Sg Scs Z (EH H) s0 s' ⦄ := by
  unfold endpoint.cancel_all_ipc_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.2.val)
    (inv := fun x => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac x.1 ∧ FootN st ∅ False T Cs Sg Scs Z (EH H) s0 x.1 ∧
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
      refine WP.spec_mono (cai_roundN0 (β := S) s1 ep t1 fuel1 hb1 hH hst1 hhd1) ?_
      rintro r ⟨s4, next, rfl, hb4, -, hf4, hn4⟩
      exact ⟨hb4, hf1.trans hf4, hn4, by simp only; omega⟩
    · exact (WP.spec_ok _).2 ⟨hb1, hf1⟩
  · exact ⟨h, hf, ht⟩

/-- (p3J gen 42) **`cancel_all_ipc` in `KWN ∅ False`** (P1 `cancel_all_ipc.blk`). -/
theorem endpoint.cancel_all_ipc.kwN0 (s : S) (ep : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hH : H ep = some .ep) :
    endpoint.cancel_all_ipc st s ep ⦃ s' => FootN st ∅ False T Cs Sg Scs Z (EH H) s s' ⦄ := by
  unfold endpoint.cancel_all_ipc
  step with obj.Ep.state.spec as ⟨v, hv⟩
  split
  · exact (WP.spec_ok _).2 (FootN.refl _)
  rename_i hidle
  have hst : L.epState s ep ≠ 0#u64 := by
    rw [← hv]; intro e; exact hidle (by rw [e]; unfold obj.EP_IDLE; rfl)
  step with endpoint.get_queue.spec as ⟨q, eq⟩
  subst eq
  have hI := h
  obtain ⟨⟨Q, R, h0⟩, -⟩ := hI
  refine WP.spec_bind (endpoint.cancel_all_ipc_loop.kwN0 s s ep _ _ h hH (FootN.refl _)
    (fun _ => ⟨ep_state12 h0 hH hst, rfl⟩)) ?_
  rintro s1 ⟨h1, f1⟩
  exact WP.spec_mono (sched.reschedule_required.kwN (Kp := ∅) (Nd := False) (Sg := Sg) (Scs := Scs) (Z := Z)
    (Es := EH H) s1 h1.1.choose_spec.choose_spec (fun _ => Set.notMem_empty _)) fun s2 f2 => f1.trans f2

/-- (p3J gen 42) **An endpoint cap's object finalisation in `KWN ∅ False`** (P1 `fin_endpoint.blk`). -/
theorem fin_endpoint.kwN0 {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (ep b0 b1 b2 b3 b4 : _)
    (fin : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hH : H ep = some .ep) :
    objects.finalise_cap_object st ar s a (.Endpoint ep b0 b1 b2 b3 b4) fin ⦃ r =>
      FootN st ∅ False T Cs Sg Scs Z (EH H) s r.2.1 ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  split
  · exact WP.spec_bind (endpoint.cancel_all_ipc.kwN0 s ep h hH) fun s1 f1 => (WP.spec_ok _).2 f1
  · exact (WP.spec_ok _).2 (FootN.refl _)

/-- (p3J gen 42) **`finalise_cap` of an endpoint cap in `KWN ∅ False`** (module docstring). -/
theorem fin_cap_ep.kwN0 {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (ep : U64) (b0 b1 b2 b3 b4 : _)
    (fin ex : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hH : H ep = some .ep) :
    objects.finalise_cap st ar s a (.Endpoint ep b0 b1 b2 b3 b4) fin ex ⦃ r =>
      FootN st ∅ False T Cs Sg Scs Z (EH H) s r.2.1 ⦄ := by
  rw [fin_cap_eq_obj (by simp)]
  exact fin_endpoint.kwN0 s a ep b0 b1 b2 b3 b4 fin h hH

end

end Fl4Proofs.P1

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- (p3J gen 42) **`cancel_all_ipc` at a `JAtZ` state writes only `ProjW`** (module docstring). -/
theorem JAtZ.caiProjW {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {e : U64} (he : e ∈ Z.E) :
    endpoint.cancel_all_ipc st s e ⦃ s' => P1.WritesIn st s s' (Mc.ProjW (L := L) H Cs s) ⦄ := by
  have h0 := J.blk.1.choose_spec.choose_spec
  exact WP.spec_mono (P1.endpoint.cancel_all_ipc.kwN0 s e J.blk (J.zH.2.1 e he)) fun _ F =>
    (P1.WritesA.w F).mono fun _ hb => Mc.kwN_projW J.kern.heap h0.nodes hb

/-- (p3J gen 42) **`finalise_cap` of an endpoint cap of `Z.E` at a `JAtZ` state writes only `ProjW`** (module
docstring). -/
theorem JAtZ.finEpProjW {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {e : U64} (he : e ∈ Z.E) (b0 b1 b2 b3 b4 : _) (fin ex : Bool) :
    objects.finalise_cap st arI s a (.Endpoint e b0 b1 b2 b3 b4) fin ex ⦃ r =>
      P1.WritesIn st s r.2.1 (Mc.ProjW (L := L) H Cs s) ⦄ := by
  have h0 := J.blk.1.choose_spec.choose_spec
  exact WP.spec_mono (P1.fin_cap_ep.kwN0 s a e b0 b1 b2 b3 b4 fin ex J.blk (J.zH.2.1 e he)) fun _ F =>
    (P1.WritesA.w F).mono fun _ hb => Mc.kwN_projW J.kern.heap h0.nodes hb

end

end Fl4Proofs.P3
