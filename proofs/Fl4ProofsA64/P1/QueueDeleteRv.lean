/-
# P1 (AArch64): the fault-handler install keeps every `RUN_VCPU` word (discharging [J] `hinstR`)

AArch64's `tcb.thread_control_sched.blk` (QueueBind), `blkC` (QueueCaiFr) and `blkE` (QueueDelete) take
the named premise [J] `hinstR`: the fault-handler `install_tcb_cap` keeps the target's `RUN_VCPU` word
(TCB + 3672). This module proves it from the same hypotheses x86_64's `QueueDelete` takes for the install
(`hroot`, `hcap`: the old fault-handler cap is null or an endpoint cap; `hslot`: `empty_slot` and
`still_valid`'s `insert` write only cap-slot words), which are unchanged here (same names, same
statements, untagged caller obligations as in x86_64's `QueueDelete`):

* `RvW T s s'`: every thread's `RUN_VCPU` word is kept;
* `endpoint.restart_thread_if_no_fault.rv`, `cai_round.rv`, `endpoint.cancel_all_ipc_loop.rv`,
  **`endpoint.cancel_all_ipc.rv`**: none of `cancel_all_ipc`'s writes (endpoint dequeue, reply unlink,
  `set_thread_state`, `unblock_sporadic`, `possible_switch_to`, `reschedule_required`) touches a
  `RUN_VCPU` word (their TCB-field frames at K = 3672);
* `fin_endpoint.rv`, `cdt.finalise_slot_immediate.rv`, `cdt.delete.rv`, **`tcb.install_tcb_cap.rv`**:
  through the delete chain; the slot writes are cap-slot words (`blk_of_capw`'s field frame, K ≥ 192);
* the `_d` forms without `hinstR`: **`tcb.thread_control_sched.blk_d`** (QueueBind's `blk`, with
  `hroot` / `hcap` / `hslot` in place of `hinstR`), `tcb.thread_control_sched.blkC_d`,
  `tcb.thread_control_sched.blkE_d`. The existing statements are unchanged.

Premises: none new. `hrv` stays a caller-level precondition, as in QueueBind.
-/
import Fl4ProofsA64.P1.QueueDelete
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-- Every thread's `RUN_VCPU` word is kept. -/
def RvW (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s s' : S) : Prop :=
  ∀ y ∈ T, L.mem s' (runVcpuA y) = L.mem s (runVcpuA y)

theorem RvW.refl (s : S) : RvW st T s s := fun _ _ => rfl

theorem RvW.trans {s₁ s₂ s₃ : S} (h₁ : RvW st T s₁ s₂) (h₂ : RvW st T s₂ s₃) : RvW st T s₁ s₃ :=
  fun y hy => (h₂ y hy).trans (h₁ y hy)

theorem RvW.of_keepT {t : U64} {s s' : S} (k : KeepT st T Cs Rp Scs Nt t s s') : RvW st T s s' :=
  fun y hy => k.fld y hy 3672#u64 (by simp) (by simp) (by simp) (by simp) (fun _ => ⟨by simp, by simp⟩)

/-- Cap-slot writes keep every `RUN_VCPU` word. -/
theorem RvW.of_capw {s s' : S} {B : U64 → Prop} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hw : WritesIn st s s' B) (hB : ∀ b, B b → CapW T Ω Sg b) : RvW st T s s' := by
  obtain ⟨-, -, -, -, -, fld, -, -⟩ := blk_of_capw h hw hB
  exact fun y hy => fld y hy 3672#u64 (by simp) (by simp) (by simp)

/-! ## `cancel_all_ipc` -/

theorem endpoint.restart_thread_if_no_fault.rv {X : Set U64} (s : S) (t : obj.Tcb) {Q : U64 → U64 → List U64}
    {R : U64 → List U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hXt : ∀ y ∈ X, y = t)
    (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hS : SCsOK st T Ω Sg Scs Z Ac s)
    (hSg : SgOK st Ω Sg s) (ht : t ∈ T) (hx : t ∈ X ∨ ¬ Blocked (L.mem s (stA t)))
    (hnoref : ∀ r ∈ Rp, L.mem s (rTcbA r) ≠ t)
    (hnQ : ∀ c ∈ Cs, ∀ p : U64, p.val < 256 → t ∉ Q c p) (hnR : ∀ c ∈ Cs, t ∉ R c) (hna : L.actionW s ≠ t) :
    endpoint.restart_thread_if_no_fault st s t ⦃ s' => RvW st T s s' ⦄ := by
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
    have h1' : SchedQueuesInv st T Cs Ω H s1 Q R := h1.congrX cg
    refine WP.spec_bind (endpoint.unblock_sporadic.all s1 t h1' hB1 hX1 hS1 hSg1 ht) ?_
    rintro s2 ⟨h2, hB2, -, -, hSg2, -, -, -, fk2, -⟩
    refine WP.spec_mono (sched.possible_switch_to.fld (Sg := Sg) s2 t h2 hB2 hSg2 ht (K := 3672#u64)
      (by simp) (by simp) (by simp) (by simp)) ?_
    intro s3 f3 y hy
    exact (f3 y hy).trans ((fk2 y hy 3672#u64 (by simp) (by simp)).trans (RvW.of_keepT k1 y hy))
  · refine WP.spec_mono (sts_all s t _ Q R h hB hX hS hSg ht not_blocked_inactive inactive_ne hx hnoref
      (hq _)) ?_
    rintro s1 ⟨-, -, -, -, -, -, k1⟩
    exact RvW.of_keepT k1

theorem cai_round.rv {β : Type _} (s : S) (ep t : U64) (fuel1 : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
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
        RvW st T s s3 ⦄ := by
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
  have tail : ∀ (s2 : S), RvW st T s s2 →
      endpoint.restart_thread_if_no_fault st s2 y ⦃ s' => RvW st T s2 s' ⦄ →
      (do
        let s3 ← endpoint.restart_thread_if_no_fault st s2 y
        ok (ControlFlow.cont (β := β) (s3, next, fuel1))) ⦃ r => ∃ s3 next', r = .cont (s3, next', fuel1) ∧
          RvW st T s s3 ⦄ := by
    intro s2 R2 hr
    exact WP.spec_bind hr fun s3 R3 => (WP.spec_ok _).2 ⟨s3, next, rfl, R2.trans R3⟩
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
      refine tail s2 (R1.trans (RvW.of_keepT k2)) (endpoint.restart_thread_if_no_fault.rv s2 y h2 (fun z hz => ?_)
        hB2 hX2 hS2 hSg2 hdT (Or.inr (by rw [e2]; exact not_blocked_inactive))
        (hX2.noref hta (by rw [e2]; exact inactive_ne.1) (by rw [e2]; exact inactive_ne.2)) hnQ hnR da2)
      obtain ⟨hz1, hz2⟩ := hz
      exact absurd (cg1 z hz1) hz2
    · rename_i hi1
      have hz : i1 = 0#u64 := by apply UScalar.eq_of_val_eq; simpa using hi1
      have hi10 : L.mem s1 (replyA y) = 0#u64 := by rw [← ei1]; exact hz
      simp only [Aeneas.Std.bind_ok]
      exact tail s1 R1 (endpoint.restart_thread_if_no_fault.rv s1 y h1 cg1 hB1 hX1 hS1 hSg1 hdT
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
    exact tail s1 R1 (endpoint.restart_thread_if_no_fault.rv s1 y h1 cg1 hB1 hX1 hS1 hSg1 hdT
      (Or.inl (Or.inr rfl)) (hX1.noref hta (by rw [hsend]; exact nrp) (by rw [hsend]; exact nrc)) hnQ hnR da1)

theorem endpoint.cancel_all_ipc_loop.rv (s0 s : S) (ep t fuel : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hH : H ep = some .ep) (hf : Foot st T Cs Sg Scs Z {ep} s0 s) (hF : CaiFr st T Scs 0#u64 s0 s)
    (hR : RvW st T s0 s)
    (ht : t ≠ 0#u64 → (L.epState s ep = 1#u64 ∨ L.epState s ep = 2#u64) ∧ (L.epQ s ep).head = t) :
    endpoint.cancel_all_ipc_loop st s ep t fuel ⦃ s' =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ Foot st T Cs Sg Scs Z {ep} s0 s' ∧ CaiFr st T Scs 0#u64 s0 s' ∧
      RvW st T s0 s' ⦄ := by
  unfold endpoint.cancel_all_ipc_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.2.val)
    (inv := fun x => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac x.1 ∧ Foot st T Cs Sg Scs Z {ep} s0 x.1 ∧
      CaiFr st T Scs 0#u64 s0 x.1 ∧ RvW st T s0 x.1 ∧
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
        (cai_round.rv (β := S) s1 ep t1 fuel1 hb1 hH hst1 hhd1)) ?_
      rintro r ⟨⟨s4, next, rfl, hb4, hf4, hn4, hF4⟩, ⟨s4', next', e', hR4⟩⟩
      injection e' with e'
      simp only [Prod.mk.injEq] at e'
      obtain ⟨rfl, -, -⟩ := e'
      exact ⟨hb4, hf1.trans hf4, hF1.trans hb1.1.choose_spec.choose_spec.tcbs hF4, hR1.trans hR4, hn4,
        by simp only; omega⟩
    · exact (WP.spec_ok _).2 ⟨hb1, hf1, hF1, hR1⟩
  · exact ⟨h, hf, hF, hR, ht⟩

/-- **seL4 `cancelAllIPC` keeps every `RUN_VCPU` word.** -/
theorem endpoint.cancel_all_ipc.rv (s : S) (ep : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hH : H ep = some .ep) :
    endpoint.cancel_all_ipc st s ep ⦃ s' => RvW st T s s' ⦄ := by
  unfold endpoint.cancel_all_ipc
  step with obj.Ep.state.spec as ⟨v, hv⟩
  split
  · exact (WP.spec_ok _).2 (RvW.refl _)
  rename_i hidle
  have hst : L.epState s ep ≠ 0#u64 := by
    rw [← hv]; intro e; exact hidle (by rw [e]; unfold obj.EP_IDLE; rfl)
  step with endpoint.get_queue.spec as ⟨q, eq⟩
  subst eq
  have hI := h
  obtain ⟨⟨Q, R, h0⟩, -⟩ := hI
  refine WP.spec_bind (endpoint.cancel_all_ipc_loop.rv s s ep _ _ h hH (Foot.refl _) (CaiFr.refl _ _)
    (RvW.refl _) (fun _ => ⟨ep_state12 h0 hH hst, rfl⟩)) ?_
  rintro s1 ⟨h1, -, -, R1⟩
  obtain ⟨⟨Q1, R1', q1⟩, hB1, -, -, hSg1⟩ := h1
  refine WP.spec_mono (sched.reschedule_required.fldX s1 Q1 R1' q1 hB1 hSg1 (K := 3672#u64)
    (by simp) (by simp) (by simp) (by simp)) fun s2 f2 y hy => (f2 y hy).trans (R1 y hy)

theorem fin_endpoint.rv {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (ep b0 b1 b2 b3 b4 : _)
    (fin : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hH : H ep = some .ep) :
    objects.finalise_cap_object st ar s a (.Endpoint ep b0 b1 b2 b3 b4) fin ⦃ r => RvW st T s r.2.1 ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  split
  · exact WP.spec_bind (endpoint.cancel_all_ipc.rv s ep h hH) fun s1 R1 => (WP.spec_ok _).2 R1
  · exact (WP.spec_ok _).2 (RvW.refl _)

/-! ## The delete chain -/

/-- `finalise_slot_immediate` of a null or endpoint cap keeps every `RUN_VCPU` word. -/
theorem cdt.finalise_slot_immediate.rv {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (slot : obj.Slot)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hcap : obj.Slot.cap st slot s ⦃ c => NullOrEp H c ⦄) :
    cdt.finalise_slot_immediate st ar s a slot ⦃ r => RvW st T s r.2.1 ⦄ := by
  unfold cdt.finalise_slot_immediate cdt.finalise_slot_immediate_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.2.val) (inv := fun x => x.1 = s ∧ x.2.1 = a)
  · rintro ⟨s1, a1, f⟩ ⟨e1, e2⟩
    simp only at e1 e2
    subst e1 e2
    dsimp only
    unfold cdt.finalise_slot_immediate_loop.body
    split
    · rename_i hfuel
      step as ⟨fuel1, hf1⟩
      refine WP.spec_bind hcap fun c hc => ?_
      rcases hc with rfl | ⟨ep, b0, b1, b2, b3, b4, rfl, hH⟩
      · simp only [capability.Cap.is_null, bind_ok, if_true, WP.spec_ok]
        exact RvW.refl _
      · simp only [capability.Cap.is_null, bind_ok, Bool.false_eq_true, ite_false]
        refine WP.spec_bind (P0.cdt.is_final_capability_with_cap.p0 st s1 slot
          (.Endpoint ep b0 b1 b2 b3 b4) L.total) fun fin _ => ?_
        unfold objects.finalise_cap
        simp only [bind_ok]
        refine WP.spec_bind (WP.spec_and (fin_endpoint.fr (ar := ar) s1 a1 ep b0 b1 b2 b3 b4 fin h hH)
          (fin_endpoint.rv (ar := ar) s1 a1 ep b0 b1 b2 b3 b4 fin h hH)) ?_
        rintro ⟨⟨rem, cl⟩, s2, a2⟩ ⟨⟨e1, -, -⟩, R2⟩
        simp only [Prod.mk.injEq] at e1
        obtain ⟨rfl, rfl⟩ := e1
        simp only [uncurry_apply_pair, WP.uncurry'_pair, cdt.cap_removable, bind_ok, if_true, WP.spec_ok]
        exact R2
    · simp only [WP.spec_ok]
      exact RvW.refl _
  · exact ⟨rfl, rfl⟩

/-- `cdt::delete` (exposed) of a slot holding a null or endpoint cap keeps every `RUN_VCPU` word, when
`empty_slot` writes only cap-slot words (`hes`, as in `cdt.delete.ep`). -/
theorem cdt.delete.rv {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (slot : obj.Slot)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hcap : obj.Slot.cap st slot s ⦃ c => NullOrEp H c ⦄)
    {P : S → Prop}
    (hes : ∀ (s1 : S) (a1 : A), (∀ b, Aligned b → CapW T Ω Sg b → L.mem s1 b = L.mem s b) →
      cdt.empty_slot st ar s1 a1 slot .Null ⦃ r => WritesIn st s1 r.1 (CapW T Ω Sg) ∧ P r.1 ⦄) :
    cdt.delete st ar s a slot true ⦃ r => RvW st T s r.2.1 ⦄ := by
  unfold cdt.delete
  simp only [if_true]
  refine WP.spec_bind (WP.spec_and (cdt.finalise_slot_immediate.ep (ar := ar) s a slot h hcap)
    (cdt.finalise_slot_immediate.rv (ar := ar) s a slot h hcap)) ?_
  rintro ⟨r, s1, a1⟩ ⟨⟨h1, f1, -, -, hcl⟩, R1⟩
  simp only [uncurry_apply_pair, WP.uncurry'_pair] at hcl R1 ⊢
  cases r with
  | Ok v =>
    have hv := hcl v rfl
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, hv]
    refine WP.spec_bind (hes s1 a1 (foot_keeps_capw h f1)) ?_
    rintro ⟨s2, a2⟩ ⟨w2, -⟩
    simp only [uncurry_apply_pair, WP.uncurry'_pair, WP.spec_ok]
    exact R1.trans (RvW.of_capw h1 w2 (fun b hb => hb))
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_ok]
    refine WP.spec_bind (Pₘ := fun r1 => ∃ v, r1 = core.result.Result.Err v)
      (WP.spec_bind (Pₘ := fun _ => True) ((WP.spec_ok _).2 trivial) fun v _ => (WP.spec_ok _).2 ⟨v, rfl⟩) ?_
    rintro r1 ⟨v, rfl⟩
    exact (WP.spec_ok _).2 R1

/-- **`install_tcb_cap` over a slot holding a null or endpoint cap keeps every `RUN_VCPU` word** (the
hypotheses of x86_64's `tcb.install_tcb_cap.cai`, unchanged). -/
theorem tcb.install_tcb_cap.rv {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (target : obj.Tcb)
    (slot : obj.Slot) (index : U64) (new_cap : capability.Cap) (src : obj.Slot) (root : U64)
    (hroot : obj.Tcb.slot target index = ok root) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hcap : obj.Slot.cap st root s ⦃ c => NullOrEp H c ⦄)
    (hslot : ∀ (s1 : S) (a1 : A), (∀ b, Aligned b → CapW T Ω Sg b → L.mem s1 b = L.mem s b) →
      cdt.empty_slot st ar s1 a1 root .Null ⦃ r => WritesIn st s1 r.1 (CapW T Ω Sg) ∧
        tcb.still_valid st r.1 target slot new_cap src ⦃ b1 => b1 = true →
          cdt.insert st r.1 new_cap src root ⦃ s3 => WritesIn st r.1 s3 (CapW T Ω Sg) ⦄ ⦄ ⦄) :
    tcb.install_tcb_cap st ar s a target slot index new_cap src ⦃ r => RvW st T s r.2.1 ⦄ := by
  unfold tcb.install_tcb_cap
  rw [hroot]
  simp only [bind_ok]
  refine WP.spec_bind (WP.spec_and (cdt.delete.ep (ar := ar) s a root h hcap
    (P := fun s2 => tcb.still_valid st s2 target slot new_cap src ⦃ b1 => b1 = true →
      cdt.insert st s2 new_cap src root ⦃ s3 => WritesIn st s2 s3 (CapW T Ω Sg) ⦄ ⦄) hslot)
    (cdt.delete.rv (ar := ar) s a root h hcap
    (P := fun s2 => tcb.still_valid st s2 target slot new_cap src ⦃ b1 => b1 = true →
      cdt.insert st s2 new_cap src root ⦃ s3 => WritesIn st s2 s3 (CapW T Ω Sg) ⦄ ⦄) hslot)) ?_
  rintro ⟨r, s2, a2⟩ ⟨⟨h2, -, -, hP⟩, R2⟩
  simp only [uncurry_apply_pair, WP.uncurry'_pair] at hP R2 ⊢
  cases r with
  | Ok u =>
    have hins := hP (by cases u; rfl)
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    refine WP.spec_bind (Pₘ := fun _ => True)
      (by unfold capability.Cap.is_null; split <;> exact (WP.spec_ok _).2 trivial) fun b _ => ?_
    split
    · exact (WP.spec_ok _).2 R2
    · refine WP.spec_bind hins fun b1 hb1 => ?_
      split
      · rename_i e
        refine WP.spec_bind (hb1 e) fun s3 w3 => ?_
        exact (WP.spec_ok _).2 (R2.trans (RvW.of_capw h2 w3 (fun b hb => hb)))
      · exact (WP.spec_ok _).2 R2
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_ok]
    refine WP.spec_bind (Pₘ := fun _ => True)
      (WP.spec_bind (Pₘ := fun _ => True) ((WP.spec_ok _).2 trivial) fun _ _ => (WP.spec_ok _).2 trivial) ?_
    intro _ _
    exact (WP.spec_ok _).2 R2

/-- [J] `hinstR`'s statement, from `install_tcb_cap.rv` at the target. -/
theorem tcb.install_tcb_cap.rvT {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (target : obj.Tcb)
    (slot : obj.Slot) (new_cap : capability.Cap) (src : obj.Slot) (root : U64) (ht : target ∈ T)
    (hroot : obj.Tcb.slot target layout.tcb.SLOT_FAULT_HANDLER = ok root) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hcap : obj.Slot.cap st root s ⦃ c => NullOrEp H c ⦄)
    (hslot : ∀ (s1 : S) (a1 : A), (∀ b, Aligned b → CapW T Ω Sg b → L.mem s1 b = L.mem s b) →
      cdt.empty_slot st ar s1 a1 root .Null ⦃ r => WritesIn st s1 r.1 (CapW T Ω Sg) ∧
        tcb.still_valid st r.1 target slot new_cap src ⦃ b1 => b1 = true →
          cdt.insert st r.1 new_cap src root ⦃ s3 => WritesIn st r.1 s3 (CapW T Ω Sg) ⦄ ⦄ ⦄) :
    tcb.install_tcb_cap st ar s a target slot layout.tcb.SLOT_FAULT_HANDLER new_cap src ⦃ r =>
      L.mem r.2.1 (runVcpuA target) = L.mem s (runVcpuA target) ⦄ :=
  WP.spec_mono (tcb.install_tcb_cap.rv s a target slot _ new_cap src root hroot h hcap hslot) fun r R => R target ht

/-! ## The `_d` forms: `thread_control_sched` without [J] `hinstR` -/

/-- **AArch64's `tcb.thread_control_sched.blk` without [J] `hinstR`**: the premise is discharged by
`install_tcb_cap.rvT` from the install hypotheses of x86_64's `QueueDelete` (`hroot`, `hcap`, `hslot`). -/
theorem tcb.thread_control_sched.blk_d {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (target : obj.Tcb) (slot : obj.Slot) (fh : capability.Cap × obj.Slot) (mcp prio : U64) (sc : obj.Sc)
    (flags : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : target ∈ T)
    (hinst : tcb.install_tcb_cap st ar s a target slot layout.tcb.SLOT_FAULT_HANDLER fh.1 fh.2 ⦃ r =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1 ∧ PFr st T Sg s r.2.1 ∧ L.curW r.2.1 = L.curW s ∧
      ((L.mem r.2.1 (inqA target) &&& sched.Q_RELEASE) ≠ 0#u64 →
        (L.mem s (inqA target) &&& sched.Q_RELEASE) ≠ 0#u64) ⦄)
    (hprio : (flags &&& tcb.SCHED_UPDATE_PRIO) ≠ 0#u64 → prio.val < 256 ∧ (target = L.curW s →
      (L.mem s (inqA target) &&& sched.Q_RELEASE) = 0#u64 ∧ L.mem s (scA target) ≠ 0#u64 ∧
        L.mem s (scA target) ∈ Ac))
    (hbind : (flags &&& tcb.SCHED_UPDATE_SC) ≠ 0#u64 → sc ≠ 0#u64 → sc ∈ Scs ∧ L.mem s (scA target) = 0#u64 ∧
      L.mem s (scTcbA sc) = 0#u64 ∧ (BlockedR (L.mem s (stA target)) → sc ∈ Ac))
    (hunb : (flags &&& tcb.SCHED_UPDATE_SC) ≠ 0#u64 → sc = 0#u64 → L.actionW s ≠ target ∧ L.idleW s ≠ target)
    (hrv : (flags &&& tcb.SCHED_UPDATE_SC) ≠ 0#u64 → sc ≠ 0#u64 → L.mem s (runVcpuA target) = 0#u64)
    (root : U64) (hroot : obj.Tcb.slot target layout.tcb.SLOT_FAULT_HANDLER = ok root)
    (hcap : obj.Slot.cap st root s ⦃ c => NullOrEp H c ⦄)
    (hslot : ∀ (s1 : S) (a1 : A), (∀ b, Aligned b → CapW T Ω Sg b → L.mem s1 b = L.mem s b) →
      cdt.empty_slot st ar s1 a1 root .Null ⦃ r => WritesIn st s1 r.1 (CapW T Ω Sg) ∧
        tcb.still_valid st r.1 target slot fh.1 fh.2 ⦃ b1 => b1 = true →
          cdt.insert st r.1 fh.1 fh.2 root ⦃ s3 => WritesIn st r.1 s3 (CapW T Ω Sg) ⦄ ⦄ ⦄) :
    tcb.thread_control_sched st ar s a target slot fh mcp prio sc flags ⦃ r =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1 ⦄ :=
  tcb.thread_control_sched.blk hA s a target slot fh mcp prio sc flags h ht hinst hprio hbind hunb hrv
    (tcb.install_tcb_cap.rvT s a target slot fh.1 fh.2 root ht hroot h hcap hslot)

/-- AArch64's `tcb.thread_control_sched.blkC` without [J] `hinstR`. -/
theorem tcb.thread_control_sched.blkC_d {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (target : obj.Tcb) (slot : obj.Slot) (fh : capability.Cap × obj.Slot) (mcp prio : U64) (sc : obj.Sc)
    (flags : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : target ∈ T)
    (hinst : tcb.install_tcb_cap st ar s a target slot layout.tcb.SLOT_FAULT_HANDLER fh.1 fh.2 ⦃ r =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1 ∧ CaiFr st T Scs 0#u64 s r.2.1 ∧
      (L.actionW r.2.1 = L.actionW s ∨ L.actionW r.2.1 = 1#u64) ⦄)
    (hprio : (flags &&& tcb.SCHED_UPDATE_PRIO) ≠ 0#u64 → prio.val < 256 ∧ (target = L.curW s →
      (L.mem s (inqA target) &&& sched.Q_RELEASE) = 0#u64 ∧ L.mem s (scA target) ≠ 0#u64 ∧
        L.mem s (scA target) ∈ Ac))
    (hbind : (flags &&& tcb.SCHED_UPDATE_SC) ≠ 0#u64 → sc ≠ 0#u64 → sc ∈ Scs ∧ L.mem s (scA target) = 0#u64 ∧
      L.mem s (scTcbA sc) = 0#u64 ∧ (BlockedR (L.mem s (stA target)) → sc ∈ Ac))
    (hunb : (flags &&& tcb.SCHED_UPDATE_SC) ≠ 0#u64 → sc = 0#u64 → L.actionW s ≠ target ∧ L.idleW s ≠ target)
    (hrv : (flags &&& tcb.SCHED_UPDATE_SC) ≠ 0#u64 → sc ≠ 0#u64 → L.mem s (runVcpuA target) = 0#u64)
    (root : U64) (hroot : obj.Tcb.slot target layout.tcb.SLOT_FAULT_HANDLER = ok root)
    (hcap : obj.Slot.cap st root s ⦃ c => NullOrEp H c ⦄)
    (hslot : ∀ (s1 : S) (a1 : A), (∀ b, Aligned b → CapW T Ω Sg b → L.mem s1 b = L.mem s b) →
      cdt.empty_slot st ar s1 a1 root .Null ⦃ r => WritesIn st s1 r.1 (CapW T Ω Sg) ∧
        tcb.still_valid st r.1 target slot fh.1 fh.2 ⦃ b1 => b1 = true →
          cdt.insert st r.1 fh.1 fh.2 root ⦃ s3 => WritesIn st r.1 s3 (CapW T Ω Sg) ⦄ ⦄ ⦄) :
    tcb.thread_control_sched st ar s a target slot fh mcp prio sc flags ⦃ r =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1 ⦄ :=
  tcb.thread_control_sched.blkC hA s a target slot fh mcp prio sc flags h ht hinst hprio hbind hunb hrv
    (tcb.install_tcb_cap.rvT s a target slot fh.1 fh.2 root ht hroot h hcap hslot)

/-- AArch64's `tcb.thread_control_sched.blkE` without [J] `hinstR` (x86_64's `blkE` hypotheses plus the
caller-level `hrv`). -/
theorem tcb.thread_control_sched.blkE_d {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (target : obj.Tcb) (slot : obj.Slot) (fh : capability.Cap × obj.Slot) (mcp prio : U64) (sc : obj.Sc)
    (flags : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : target ∈ T) (root : U64)
    (hroot : obj.Tcb.slot target layout.tcb.SLOT_FAULT_HANDLER = ok root)
    (hcap : obj.Slot.cap st root s ⦃ c => NullOrEp H c ⦄)
    (hslot : ∀ (s1 : S) (a1 : A), (∀ b, Aligned b → CapW T Ω Sg b → L.mem s1 b = L.mem s b) →
      cdt.empty_slot st ar s1 a1 root .Null ⦃ r => WritesIn st s1 r.1 (CapW T Ω Sg) ∧
        tcb.still_valid st r.1 target slot fh.1 fh.2 ⦃ b1 => b1 = true →
          cdt.insert st r.1 fh.1 fh.2 root ⦃ s3 => WritesIn st r.1 s3 (CapW T Ω Sg) ⦄ ⦄ ⦄)
    (hprio : (flags &&& tcb.SCHED_UPDATE_PRIO) ≠ 0#u64 → prio.val < 256 ∧ (target = L.curW s →
      (L.mem s (inqA target) &&& sched.Q_RELEASE) = 0#u64 ∧ L.mem s (scA target) ≠ 0#u64 ∧
        L.mem s (scA target) ∈ Ac))
    (hbind : (flags &&& tcb.SCHED_UPDATE_SC) ≠ 0#u64 → sc ≠ 0#u64 → sc ∈ Scs ∧ L.mem s (scA target) = 0#u64 ∧
      L.mem s (scTcbA sc) = 0#u64 ∧ (BlockedR (L.mem s (stA target)) → sc ∈ Ac))
    (hunb : (flags &&& tcb.SCHED_UPDATE_SC) ≠ 0#u64 → sc = 0#u64 → L.actionW s ≠ target ∧ L.idleW s ≠ target)
    (hrv : (flags &&& tcb.SCHED_UPDATE_SC) ≠ 0#u64 → sc ≠ 0#u64 → L.mem s (runVcpuA target) = 0#u64) :
    tcb.thread_control_sched st ar s a target slot fh mcp prio sc flags ⦃ r =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1 ⦄ :=
  tcb.thread_control_sched.blkE hA s a target slot fh mcp prio sc flags h ht root hroot hcap hslot hprio hbind hunb
    hrv (tcb.install_tcb_cap.rvT s a target slot fh.1 fh.2 root ht hroot h hcap hslot)

end

end Fl4ProofsA64.P1
