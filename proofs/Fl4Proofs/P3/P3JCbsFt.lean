/-
P3 (p3J gen 39): **`cancel_badged_sends` in `KWN ∅ False`, hence inside `ProjW`** (P1 QueueCbs's
`cancel_badged_sends_loop.blk` walk mirrored at `Kp = ∅`, `Nd = False`, `Es = EH H`, as gen 37's P3JNtfnFt mirrored
`cancel_all_signals`). FL4 only.

P1's `cancel_badged_sends.blkF` gives a `Foot` (`KW`) footprint, which allows other cores' node identity words
(`IDLE_THREAD` / `IDLE_SC`, offsets 8 / 32) that `Mc.ProjW` excludes. Here every step (FL4 `endpoint.rs`
`cancel_badged_sends`: the send-queue walk, `ep_dequeue`, `restart_thread_if_no_fault`, then
`reschedule_required`) is shown in `KWN ∅ False`:

* `endpoint.restart_thread_if_no_fault.kwN0` (`set_thread_state.kwNP`, `endpoint.unblock_sporadic.kwN`,
  `possible_switch_to.kwN`; the faulted branch `set_thread_state.kwNP` alone).
* `endpoint.cancel_badged_sends_loop.kwN0` (the loop's invariant `BlkOK ∧ FootN ∧ CbsAt`; the dequeue by P2's
  `EpFoot.kwN` / `EpFoot.act`), **`endpoint.cancel_badged_sends.kwN0`** (`reschedule_required.kwN`).
* **`JAtZ.cbsProjW`** (P3): at a `JAtZ` state, `cancel_badged_sends` of an endpoint of `Z.E` writes only
  `ProjW H Cs s` (P3JMcKwN's `kwN_projW`).

`AcK` / `ActOut` are vacuous at `Kp = ∅`. No premise; no sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JCnCp
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P2.Stall

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}
variable {Ac : Set U64}

/-- (p3J gen 39) `restart_thread_if_no_fault` in `KWN ∅ False` (P1 `restart_thread_if_no_fault.blk`). -/
theorem endpoint.restart_thread_if_no_fault.kwN0 {X : Set U64} (s : S) (t : obj.Tcb) {Q : U64 → U64 → List U64}
    {R : U64 → List U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hXt : ∀ y ∈ X, y = t)
    (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hS : SCsOK st T Ω Sg Scs Z Ac s)
    (hSg : SgOK st Ω Sg s) (ht : t ∈ T) (hx : t ∈ X ∨ ¬ Blocked (L.mem s (stA t)))
    (hnoref : ∀ r ∈ Rp, L.mem s (rTcbA r) ≠ t)
    (hnQ : ∀ c ∈ Cs, ∀ p : U64, p.val < 256 → t ∉ Q c p) (hnR : ∀ c ∈ Cs, t ∉ R c) (hna : L.actionW s ≠ t) :
    endpoint.restart_thread_if_no_fault st s t ⦃ s' => FootN st ∅ False T Cs Sg Scs Z (EH H) s s' ⦄ := by
  have hq : ∀ v : U64, (∀ c ∈ Cs, ∀ p : U64, p.val < 256 → t ∈ Q c p → Runnable v) ∧
      (∀ c ∈ Cs, t ∈ R c → Runnable v) ∧ (L.actionW s = t → Runnable v) := fun v =>
    ⟨fun c hc p hp htq => absurd htq (hnQ c hc p hp), fun c hc htr => absurd htr (hnR c hc),
      fun e => absurd e hna⟩
  have cg : ∀ y, y ∈ {y : U64 | y ∈ X ∧ y ≠ t} ↔ y ∈ (∅ : Set U64) := fun y => by
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_not]; exact hXt y
  have hT := h.tcbs
  unfold endpoint.restart_thread_if_no_fault
  step with obj.Tcb.fault_type.any as ⟨i, _hi⟩
  split
  · refine WP.spec_bind (WP.spec_and (sts_all s t _ Q R h hB hX hS hSg ht not_blocked_restart restart_ne hx hnoref
      (hq _)) (sched.set_thread_state.kwNP (Sg := Sg) (Kp := ∅) (Nd := False) (Scs := Scs) (Z := Z)
        (Es := EH H) s t _ hT h.nodes h.cur ht (Set.notMem_empty _))) ?_
    rintro s1 ⟨⟨h1, hB1, hX1, hS1, hSg1, -, -⟩, F1⟩
    have h1' : SchedQueuesInv st T Cs Ω H s1 Q R := h1.congrX cg
    refine WP.spec_bind (WP.spec_and (endpoint.unblock_sporadic.all s1 t h1' hB1 hX1 hS1 hSg1 ht)
      (endpoint.unblock_sporadic.kwN (Kp := ∅) (Nd := False) (Es := EH H) s1 t h1' hX1 hS1 ht)) ?_
    rintro s2 ⟨⟨h2, -, -, -, -, -, -, -, -, -⟩, F2⟩
    exact WP.spec_mono (sched.possible_switch_to.kwN (Sg := Sg) (Kp := ∅) (Nd := False) (Scs := Scs) (Z := Z)
      (Es := EH H) s2 t h2 ht (Set.notMem_empty _) (fun _ => Set.notMem_empty _)) fun s3 F3 => F1.trans (F2.trans F3)
  · exact sched.set_thread_state.kwNP (Sg := Sg) (Kp := ∅) (Nd := False) (Scs := Scs) (Z := Z)
      (Es := EH H) s t _ hT h.nodes h.cur ht (Set.notMem_empty _)

set_option maxHeartbeats 4000000 in
/-- (p3J gen 39) The `cancel_badged_sends` loop in `KWN ∅ False` (P1 `cancel_badged_sends_loop.blk`). -/
theorem endpoint.cancel_badged_sends_loop.kwN0 (s0 s : S) (ep badge t fuel : U64)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hH : H ep = some .ep)
    (hf : FootN st ∅ False T Cs Sg Scs Z (EH H) s0 s) (ht : CbsAt st T ep s t) :
    endpoint.cancel_badged_sends_loop st s ep badge t fuel ⦃ s' =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ FootN st ∅ False T Cs Sg Scs Z (EH H) s0 s' ⦄ := by
  have hST : P0.StoreTotal st := L.total
  unfold endpoint.cancel_badged_sends_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.2.val)
    (inv := fun x => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac x.1 ∧ FootN st ∅ False T Cs Sg Scs Z (EH H) s0 x.1 ∧
      CbsAt st T ep x.1 x.2.1)
  · rintro ⟨s1, y, f1⟩ ⟨hb1, hf1, ht1⟩
    simp only at hb1 hf1 ht1
    unfold endpoint.cancel_badged_sends_loop.body
    step with obj.Tcb.is_null.spec as ⟨b, eb⟩
    split
    · exact (WP.spec_ok _).2 ⟨hb1, hf1⟩
    rename_i hb
    have hy0 : y ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    obtain ⟨hdT, hbe, hsend⟩ := ht1 hy0
    split
    swap
    · exact (WP.spec_ok _).2 ⟨hb1, hf1⟩
    rename_i hfuel
    step as ⟨fuel1, efuel⟩
    obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := hb1
    have hT := h0.tcbs
    have hta := hT y hdT
    obtain ⟨E, EQ, w1, w2, w5, w3, w4, ty⟩ := h0.eps
    have hbl : Blocked (L.mem s1 (stA y)) := by rw [hsend]; exact Or.inl rfl
    obtain ⟨heE, hyQ⟩ := w4 y hdT (by simp) hbl
    rw [hbe] at heE hyQ
    obtain ⟨hE, hEN, hq⟩ := w1 ep heE
    have hEΩ := w5 ep heE
    unfold tcbqueue.next_of
    step with tcbqueue.next.spec as ⟨next, enext⟩
    have hnext : next = 0#u64 ∨ (next ∈ EQ ep ∧ next ≠ y) := by
      rw [enext]; exact seg_next hq.seg hq.nodup hyQ
    have hN1 : CbsAt st T ep s1 next := fun hn0 => by
      rcases hnext with e | ⟨hm, -⟩
      · exact absurd e hn0
      obtain ⟨-, hbn, -⟩ := w3 ep heE next hm
      exact ⟨hq.mem next hm, hbn, by rw [ty.2.2.2.1 ep heE next hm y hyQ, hsend]⟩
    step with P0.obj.Tcb.block_badge.p0 st y s1 hST as ⟨i⟩
    split
    swap
    · exact (WP.spec_ok _).2 ⟨⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩, hf1, hN1, by simp only; omega⟩
    have hnrun := not_runnable_of_blocked hbl
    obtain ⟨-, -, da⟩ := blocked_out h0 hdT hnrun
    have hnQ : ∀ c ∈ Cs, ∀ p : U64, p.val < 256 → y ∉ Q c p := fun c hc p hp htq => hnrun (h0.runQ c hc p hp y htq)
    have hnR : ∀ c ∈ Cs, y ∉ R c := fun c hc htr => hnrun (h0.runR c hc y htr)
    have hdq := endpoint.ep_dequeue.inv s1 y Q R h0 hdT (by simp) hbl
    rw [hbe] at hdq
    refine WP.spec_bind (WP.spec_and hdq (endpoint.ep_dequeue.foot s1 ep y _ hT hE hq hyQ)) ?_
    rintro s2 ⟨⟨h2, f2, o2, n2, k2, c2, nc2⟩, w2'⟩
    have F2 : FootN st ∅ False T Cs Sg Scs Z (EH H) s1 s2 :=
      FootN.of' w2' (fun b _ hb => EpFoot.kwN hT h0.nodes hq.mem (Or.inl hH) hE hEN hEΩ (hdrΩ_of hX hSg.sub) hb)
        (AcK.of_eq (EpFoot.act hT h0.nodes h0.cur hq.mem hE hEN w2'))
    have tm2 : TmFr st T Cs Nt s1 s2 := TmFr.mk0 ⟨k2, fun y hy K a b c => f2 y hy K (by omega) c (by omega) (by omega),
      fun c hc o ho => nc2 c hc o (by omega) (by omega), fun n' hn' => o2 _ (hSg.sub _ (hX.1.ntB n' hn').2)⟩
    obtain ⟨hB2, hX2, hS2, hSg2, ea2, -, -⟩ := frame_bx h0 hB hX hS hSg f2 o2 n2 k2 tm2
    have st2 : L.mem s2 (stA y) = L.mem s1 (stA y) := by
      rw [stA_eq]; exact f2 y hdT _ (by simp) (by simp) (by simp) (by simp)
    have da2 : L.actionW s2 ≠ y := by rw [ea2]; exact da
    have hyA2 : L.mem s2 (scA y) ≠ 0#u64 → L.mem s2 (scA y) ∈ Ac := by
      have esc2 : L.mem s2 (scA y) = L.mem s1 (scA y) := by
        rw [scA_eq]; exact f2 y hdT _ (by simp) (by simp) (by simp) (by simp)
      rw [esc2]; exact hB.sact y hdT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hbl))))))
    have cg1 : ∀ z ∈ {z : U64 | z ∈ (∅ : Set U64) ∨ z = y}, z = y := fun z hz => by simpa using hz
    obtain ⟨-, -, r3, r4, -⟩ := ts_vals
    have nrp : sched.TS_BLOCKED_ON_SEND ≠ sched.TS_BLOCKED_ON_REPLY := by
      rw [r4]; unfold sched.TS_BLOCKED_ON_REPLY; decide
    have nrc : sched.TS_BLOCKED_ON_SEND ≠ sched.TS_BLOCKED_ON_RECV := by rw [r4, r3]; decide
    have hsend2 : L.mem s2 (stA y) = sched.TS_BLOCKED_ON_SEND := by rw [st2, hsend]
    refine WP.spec_bind (WP.spec_and (WP.spec_and
      (endpoint.restart_thread_if_no_fault.blk s2 y h2 cg1 hB2 hX2 hS2 hSg2 hdT (Or.inl (Or.inr rfl))
        (hX2.noref hta (by rw [hsend2]; exact nrp) (by rw [hsend2]; exact nrc)) hnQ hnR da2 hyA2)
      (endpoint.restart_thread_if_no_fault.oth s2 y h2 cg1 hB2 hX2 hS2 hSg2 hdT (Or.inl (Or.inr rfl))
        (hX2.noref hta (by rw [hsend2]; exact nrp) (by rw [hsend2]; exact nrc)) hnQ hnR da2 hyA2))
      (endpoint.restart_thread_if_no_fault.kwN0 s2 y h2 cg1 hB2 hX2 hS2 hSg2 hdT (Or.inl (Or.inr rfl))
        (hX2.noref hta (by rw [hsend2]; exact nrp) (by rw [hsend2]; exact nrc)) hnQ hnR da2)) ?_
    rintro s3 ⟨⟨⟨h3, -⟩, oth3⟩, F3⟩
    refine (WP.spec_ok _).2 ⟨h3, hf1.trans (F2.trans F3), fun hn0 => ?_, by simp only; omega⟩
    obtain ⟨hnT, hnb, hns⟩ := hN1 hn0
    have hny : next ≠ y := by
      rcases hnext with e | ⟨-, hne⟩
      · exact absurd e hn0
      · exact hne
    obtain ⟨o1, o2'⟩ := oth3 next hnT hny
    refine ⟨hnT, ?_, ?_⟩
    · rw [o2', blockA_eq, f2 next hnT _ (by simp) (by simp) (by simp) (by simp), ← blockA_eq]; exact hnb
    · rw [o1, stA_eq, f2 next hnT _ (by simp) (by simp) (by simp) (by simp), ← stA_eq]; exact hns
  · exact ⟨h, hf, ht⟩

/-- (p3J gen 39) **`cancel_badged_sends` in `KWN ∅ False`** (P1 `cancel_badged_sends.blkF`). -/
theorem endpoint.cancel_badged_sends.kwN0 (s : S) (ep badge : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hH : H ep = some .ep) :
    endpoint.cancel_badged_sends st s ep badge ⦃ s' => FootN st ∅ False T Cs Sg Scs Z (EH H) s s' ⦄ := by
  unfold endpoint.cancel_badged_sends
  step with obj.Ep.state.spec as ⟨v, hv⟩
  split
  · exact (WP.spec_ok _).2 (FootN.refl _)
  rename_i hsend
  have hst : L.epState s ep = 1#u64 := by
    rw [← hv]; apply UScalar.eq_of_val_eq; simpa [obj.EP_SEND] using hsend
  step with endpoint.get_queue.spec as ⟨q, eq⟩
  subst eq
  obtain ⟨hd, hbe, hs1, -⟩ := ep_head h.1.choose_spec.choose_spec hH (w := 1#u64) (Or.inl rfl) hst
  refine WP.spec_bind (endpoint.cancel_badged_sends_loop.kwN0 s s ep badge _ _ h hH (FootN.refl _)
    (fun _ => ⟨hd, hbe, hs1 rfl⟩)) ?_
  rintro s1 ⟨h1, f1⟩
  exact WP.spec_mono (sched.reschedule_required.kwN (Kp := ∅) (Nd := False) (Sg := Sg) (Scs := Scs) (Z := Z)
    (Es := EH H) s1 h1.1.choose_spec.choose_spec (fun _ => Set.notMem_empty _)) fun s2 f2 => f1.trans f2

end

end Fl4Proofs.P1

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- (p3J gen 39) **`cancel_badged_sends` at a `JAtZ` state writes only `ProjW`** (module docstring). -/
theorem JAtZ.cbsProjW {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {e : U64} (b : U64) (he : e ∈ Z.E) :
    endpoint.cancel_badged_sends st s e b ⦃ s' => P1.WritesIn st s s' (Mc.ProjW (L := L) H Cs s) ⦄ := by
  have hpH : H e = some .ep := J.zH.2.1 e he
  have h0 := J.blk.1.choose_spec.choose_spec
  exact WP.spec_mono (P1.endpoint.cancel_badged_sends.kwN0 s e b J.blk hpH) fun _ F =>
    (P1.WritesA.w F).mono fun _ hb => Mc.kwN_projW J.kern.heap h0.nodes hb

end

end Fl4Proofs.P3
