/-
P1: callers of the queue operations keep `SchedQueuesInv`:
`reschedule_required`, `possible_switch_to`, `set_priority` (the
dequeue / set priority / enqueue pattern of seL4 `setPriority`), and
`append` (`tcbSchedAppend`, used by `schedule`).
-/
import Fl4Proofs.P1.QueueSchedInv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

def stA (t : U64) : U64 := core.num.U64.wrapping_add t layout.tcb.STATE

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64}

/-! ## Specs of the small helpers -/

@[step] theorem obj.Tcb.state.spec (s : S) (t : obj.Tcb) :
    obj.Tcb.state st t s ⦃ v => v = L.mem s (stA t) ⦄ := by
  unfold obj.Tcb.state; step*; simp_all [stA]

@[step] theorem obj.Sc.is_null.spec (sc : obj.Sc) : obj.Sc.is_null sc ⦃ b => b = decide (sc = 0#u64) ⦄ := by
  unfold obj.Sc.is_null; simp

@[step] theorem sched.action.spec (s : S) : sched.action st s ⦃ v => v = L.actionW s ⦄ := by
  unfold sched.action; step*; simp_all [LawfulStore.actionW]

@[step] theorem sched.set_action.spec (s : S) (v : U64) :
    sched.set_action st s v ⦃ s' => s' = L.wr s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) v ⦄ := by
  unfold sched.set_action; step*; simp_all

@[step] theorem sched.cur_thread.spec (s : S) :
    sched.cur_thread st s ⦃ v => v = L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) ⦄ := by
  unfold sched.cur_thread; step*; simp_all

@[step] theorem obj.Tcb.set_prio.spec (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_prio st t s v ⦃ s' => s' = L.wr s (prioA t) v ⦄ := by
  unfold obj.Tcb.set_prio; step*; simp_all [prioA]

/-- `is_schedulable` only says yes for a thread outside the release queue. -/
@[step] theorem sched.is_schedulable.spec (s : S) (t : obj.Tcb) :
    sched.is_schedulable st s t ⦃ b => b = true → (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64 ⦄ := by
  unfold sched.is_schedulable sched.is_runnable sporadic.sc_active
  step
  split <;> simp only [bind_ok] <;> step* <;> simp_all

/-! ## TCB fields as addresses -/

theorem field_val {y K : U64} (hy : TcbAddr y) (hK : K.val < 4096) :
    (core.num.U64.wrapping_add y K).val = y.val + K.val := by
  have := hy.fits
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega

/-- Two TCB fields are different words unless they are the same field of the
same TCB. -/
theorem field_ne {x y K1 K2 : U64} (hx : TcbAddr x) (hy : TcbAddr y) (h1 : K1.val < 4096) (h2 : K2.val < 4096)
    (hne : x = y → K1.val ≠ K2.val) : core.num.U64.wrapping_add x K1 ≠ core.num.U64.wrapping_add y K2 := by
  intro e
  have hv := congrArg UScalar.val e
  rw [field_val hx h1, field_val hy h2] at hv
  have := hx.align; have := hy.align
  by_cases hxy : x = y
  · subst hxy; exact hne rfl (by omega)
  · have : x.val ≠ y.val := fun e' => hxy (UScalar.eq_of_val_eq e')
    omega

theorem node_ne_field {s : S} {c o y K : U64} (hN : NodePlaced st T s c) (ho : o.val < 4288) (hy : y ∈ T)
    (hya : TcbAddr y) (hK : K.val < 4096) : L.nodeAt s c o ≠ core.num.U64.wrapping_add y K := by
  intro e
  have hv := congrArg UScalar.val e
  rw [field_val hya hK] at hv
  have := nodeAt_out hN ho hy; omega

theorem nextA_eq' (l : tcbqueue.Link) (y : U64) : nextA l y = core.num.U64.wrapping_add y (nextOff l) := rfl
theorem prevA_eq' (l : tcbqueue.Link) (y : U64) : prevA l y = core.num.U64.wrapping_add y (prevOff l) := rfl

/-! ## Writes away from the queues -/

/-- A write to a node word below the release queue (`SCHED_ACTION`,
`REPROGRAM`, ...) keeps the invariant, if the action stays valid. -/
theorem inv_wr_node_low {Cs : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    {c0 o v : U64} (h : SchedQueuesInv st T Cs s Q R) (hc0 : c0 ∈ Cs) (ho : o.val < 64) (h8 : o.val % 8 = 0)
    (hact : L.actionW (L.wr s (L.nodeAt s c0 o) v) = 0#u64 ∨ L.actionW (L.wr s (L.nodeAt s c0 o) v) = 1#u64 ∨
      L.actionW (L.wr s (L.nodeAt s c0 o) v) ∈ T) :
    SchedQueuesInv st T Cs (L.wr s (L.nodeAt s c0 o) v) Q R := by
  have hT := h.tcbs
  have hN0 := h.nodes c0 hc0
  have ha := nodeAt_aligned hN0 (by omega) h8 (off := o)
  have fld : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem (L.wr s (L.nodeAt s c0 o) v) (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y hy K hK hK8 => L.mem_wr_ne ha (field_aligned (hT y hy) hK hK8)
      (fun e => node_ne_field hN0 (by omega) hy (hT y hy) hK (UScalar.eq_of_val_eq e))
  refine inv_of_agree h (L.ksb_wr _ _ _) (L.cpu_wr _ _ _) (fun y hy => ⟨?_, ?_⟩) (fun c hc o' h1 h2 h3 => ?_)
    (fun y hy => fld y hy _ (by simp) (by simp)) (fun y hy => fld y hy _ (by simp) (by simp))
    (fun y hy => Or.inl (fld y hy _ (by simp) (by simp))) hact
  · rw [nextA_eq']; exact fld y hy _ (by cases tcbqueue.Link.Sched <;> simp [nextOff]) (by simp [nextOff])
  · rw [prevA_eq']; exact fld y hy _ (by simp [prevOff]) (by simp [prevOff])
  · by_cases e : c0 = c
    · subst e
      rw [rd_node_wr_node hN0 (by omega) h1 h8 h2, if_neg (by omega)]
    · exact rd_node_wr_node_cpu (h.nodes c hc) hN0 (by omega) h1 h8 h2 e

/-- Setting the priority of a thread in no ready queue keeps the invariant. -/
theorem inv_wr_prio {Cs : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {t v : U64}
    (h : SchedQueuesInv st T Cs s Q R) (ht : t ∈ T) (h0 : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64)
    (hv : v.val < 256) : SchedQueuesInv st T Cs (L.wr s (prioA t) v) Q R := by
  have hT := h.tcbs
  have hta := hT t ht
  have ha : Aligned (prioA t) := field_aligned hta (by simp) (by simp)
  have fld : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (y = t → K.val ≠ 3448) →
      L.mem (L.wr s (prioA t) v) (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y hy K hK hK8 hne => L.mem_wr_ne ha (field_aligned (hT y hy) hK hK8)
      (fun e => field_ne hta (hT y hy) (by simp) hK (fun e' => by subst e'; exact fun h => hne rfl h.symm)
        (UScalar.eq_of_val_eq e))
  refine inv_of_agree h (L.ksb_wr _ _ _) (L.cpu_wr _ _ _) (fun y hy => ⟨?_, ?_⟩) (fun c hc o' h1 h2 h3 => ?_)
    (fun y hy => fld y hy _ (by simp) (by simp) (fun _ => by simp))
    (fun y hy => fld y hy _ (by simp) (by simp) (fun _ => by simp)) (fun y hy => ?_) ?_
  · rw [nextA_eq']; exact fld y hy _ (by simp [nextOff]) (by simp [nextOff]) (fun _ => by simp [nextOff])
  · rw [prevA_eq']; exact fld y hy _ (by simp [prevOff]) (by simp [prevOff]) (fun _ => by simp [prevOff])
  · exact L.mem_wr_ne ha (nodeAt_aligned (h.nodes c hc) h1 h2)
      (fun e => node_ne_field (h.nodes c hc) h1 ht hta (by simp) (UScalar.eq_of_val_eq e).symm)
  · by_cases e : y = t
    · subst e; right; exact ⟨h0, by rw [L.mem_wr_same ha]; exact hv⟩
    · left; exact fld y hy _ (by simp) (by simp) (fun e' => absurd e' e)
  · have hN' := h.nodes _ h.cur
    have e : L.actionW (L.wr s (prioA t) v) = L.actionW s := by
      unfold LawfulStore.actionW
      simp only [LawfulStore.cpu_wr, nodeAt_wr]
      exact L.mem_wr_ne ha (nodeAt_aligned hN' (by rw [act_val]; omega) (by rw [act_val]))
        (fun e => node_ne_field hN' (by rw [act_val]; omega) ht hta (by simp) (UScalar.eq_of_val_eq e).symm)
    rw [e]; exact h.action

/-- `set_action` with a valid action keeps the invariant. -/
theorem inv_set_action {Cs : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {v : U64}
    (h : SchedQueuesInv st T Cs s Q R) (hv : v = 0#u64 ∨ v = 1#u64 ∨ v ∈ T) :
    SchedQueuesInv st T Cs (L.wr s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) v) Q R ∧
      L.actionW (L.wr s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) v) = v := by
  have hN' := h.nodes _ h.cur
  have e : L.actionW (L.wr s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) v) = v := by
    unfold LawfulStore.actionW
    simp only [LawfulStore.cpu_wr, nodeAt_wr]
    exact L.mem_wr_same (nodeAt_aligned hN' (by rw [act_val]; omega) (by rw [act_val]))
  exact ⟨inv_wr_node_low h h.cur (by rw [act_val]; omega) (by rw [act_val]) (by rw [e]; exact hv), e⟩

theorem resume_val : sched.ACTION_RESUME_CURRENT = 0#u64 := by unfold sched.ACTION_RESUME_CURRENT; rfl
theorem choose_val : sched.ACTION_CHOOSE_NEW = 1#u64 := by unfold sched.ACTION_CHOOSE_NEW; rfl

/-! ## `reschedule_required`, `possible_switch_to` -/

/-- seL4 `rescheduleRequired` keeps the invariant (release queues
unchanged) and leaves the action choose-new. -/
theorem sched.reschedule_required.inv {Cs : Set U64} (s : S) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs s Q R) :
    sched.reschedule_required st s ⦃ s' => (∃ Q', SchedQueuesInv st T Cs s' Q' R) ∧
      L.actionW s' = 1#u64 ⦄ := by
  unfold sched.reschedule_required
  step as ⟨act, act_post⟩
  have hpart : (if (act != sched.ACTION_RESUME_CURRENT) = true then
      if (act != sched.ACTION_CHOOSE_NEW) = true then do
        let b ← sched.is_schedulable st s act
        if b = true then sched.enqueue st s act else ok s
      else ok s
    else ok s) ⦃ s1 => ∃ Q', SchedQueuesInv st T Cs s1 Q' R ⦄ := by
    split
    · split
      · rename_i h1 h2
        have hT : act ∈ T := by
          rcases h.action with e | e | e
          · rw [← act_post] at e; exfalso; rw [e, resume_val] at h1; simp at h1
          · rw [← act_post] at e; exfalso; rw [e, choose_val] at h2; simp at h2
          · rw [← act_post] at e; exact e
        step as ⟨b, hb⟩
        split
        · exact WP.spec_mono (sched.enqueue.inv s act Q R h hT (fun _ => hb ‹_›)) fun s1 h1 => ⟨_, h1⟩
        · simp only [WP.spec_ok]; exact ⟨Q, h⟩
      · simp only [WP.spec_ok]; exact ⟨Q, h⟩
    · simp only [WP.spec_ok]; exact ⟨Q, h⟩
  refine WP.spec_bind hpart ?_
  rintro s1 ⟨Q', h1⟩
  step as ⟨s2, s2_post⟩
  subst s2_post
  rw [choose_val]
  obtain ⟨h2, e⟩ := inv_set_action (v := 1#u64) h1 (Or.inr (Or.inl rfl))
  exact ⟨⟨Q', h2⟩, e⟩

/-- seL4 `possibleSwitchTo` keeps the invariant (release queues
unchanged). -/
theorem sched.possible_switch_to.inv {Cs : Set U64} (s : S) (t : obj.Tcb) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (h : SchedQueuesInv st T Cs s Q R) (ht : t ∈ T) :
    sched.possible_switch_to st s t ⦃ s' => ∃ Q', SchedQueuesInv st T Cs s' Q' R ⦄ := by
  have enq : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64 → ∀ s1 Q1, SchedQueuesInv st T Cs s1 Q1 R →
      sched.enqueue st s1 t ⦃ s' => ∃ Q', SchedQueuesInv st T Cs s' Q' R ⦄ := by
    intro hr0 s1 Q1 h1
    have hr1 : (L.mem s1 (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by
      by_contra hc
      exact h.notR ht hr0 (h1.aff t ht) ((h1.released t ht).1 hc)
    exact WP.spec_mono (sched.enqueue.inv s1 t Q1 R h1 ht (fun _ => hr1)) fun s' h' => ⟨_, h'⟩
  unfold sched.possible_switch_to sched.cur_domain
  step*
  all_goals try (have hr0 : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64 := not_not.1 (fun hc => ‹¬b = true› (by rw [b_post]; exact decide_eq_true hc)))
  all_goals try exact enq hr0 s Q h
  · refine WP.spec_bind (sched.reschedule_required.inv s Q R h) ?_
    rintro s1 ⟨⟨Q1, h1⟩, -⟩
    exact enq hr0 s1 Q1 h1
  · subst s'_post
    exact ⟨Q, (inv_set_action h (Or.inr (Or.inr ht))).1⟩

/-! ## Endpoint and notification reordering, seen from the scheduler -/

/-- The footprint of `reorder_ep` / `reorder_ntfn`: the `Ep` links of the
queue and the object's two words. -/
def EpFoot (W : List U64) (ep : U64) (b : U64) : Prop := LinkOf .Ep W b ∨ b = epHeadA ep ∨ b = epTSA ep

theorem LinkOf.mono {l : tcbqueue.Link} {W W' : List U64} {b : U64} (h : LinkOf l W b) (hW : W ⊆ W') :
    LinkOf l W' b := by
  obtain ⟨w, hw, e⟩ := h; exact ⟨w, hW hw, e⟩

theorem reorder_foot_tail {s s2 : S} {ep : U64} {q : tcbqueue.Queue} {state : U64} {W : List U64}
    (hE : EpPlaced T ep) (h2 : WritesIn st s s2 (LinkOf .Ep W)) :
    WritesIn st s (L.wr (L.wr s2 (epHeadA ep) q.head) (epTSA ep) ((q.end &&& ~~~3#u64) ||| (state &&& 3#u64)))
      (EpFoot W ep) := by
  obtain ⟨ah, at'⟩ := ep_aligned hE
  exact ((h2.trans (writesIn_wr ah)).trans (writesIn_wr at')).mono fun b hb => by
    rcases hb with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

theorem endpoint.reorder_ep.foot (s : S) (ep : U64) (t : obj.Tcb) (xs : List U64)
    (hT : TcbPlaced T) (hE : EpPlaced T ep) (h : QueueRel (L.mem s) T .Ep (L.epQ s ep) xs) (ht : t ∈ xs) :
    endpoint.reorder_ep st s ep t ⦃ s' => WritesIn st s s' (EpFoot xs ep) ⦄ := by
  unfold endpoint.reorder_ep
  step*
  subst q_post
  refine WP.spec_bind (tcbqueue.remove.rel s .Ep _ t xs hT h ht) ?_
  rintro ⟨q1, s1⟩ h1
  simp only [WP.uncurry'_pair] at h1
  obtain ⟨hr1, hf1, -, -⟩ := h1
  refine WP.spec_bind (tcbqueue.append_by_prio.rel s1 .Ep q1 t _ hT hr1 (h.mem t ht) h.nodup.not_mem_erase) ?_
  rintro ⟨q2, s2⟩ h2
  simp only [WP.uncurry'_pair] at h2
  obtain ⟨-, hf2⟩ := h2
  have w := hf1.writesIn.trans hf2.writesIn
  step*
  subst_vars
  refine reorder_foot_tail hE (w.mono fun b hb => ?_)
  rcases hb with hb | hb
  · exact hb
  · exact hb.mono (fun y hy => by
      rcases List.mem_cons.1 hy with rfl | hy
      · exact ht
      · exact List.mem_of_mem_erase hy)

theorem notification.reorder_ntfn.foot (s : S) (ep : U64) (t : obj.Tcb) (xs : List U64)
    (hT : TcbPlaced T) (hE : EpPlaced T ep) (h : QueueRel (L.mem s) T .Ep (L.epQ s ep) xs) (ht : t ∈ xs) :
    notification.reorder_ntfn st s ep t ⦃ s' => WritesIn st s s' (EpFoot xs ep) ⦄ := by
  unfold notification.reorder_ntfn
  step*
  subst q_post
  refine WP.spec_bind (tcbqueue.remove.rel s .Ep _ t xs hT h ht) ?_
  rintro ⟨q1, s1⟩ h1
  simp only [WP.uncurry'_pair] at h1
  obtain ⟨hr1, hf1, -, -⟩ := h1
  refine WP.spec_bind (tcbqueue.append_by_prio.rel s1 .Ep q1 t _ hT hr1 (h.mem t ht) h.nodup.not_mem_erase) ?_
  rintro ⟨q2, s2⟩ h2
  simp only [WP.uncurry'_pair] at h2
  obtain ⟨-, hf2⟩ := h2
  have w := hf1.writesIn.trans hf2.writesIn
  step*
  subst_vars
  refine reorder_foot_tail hE (w.mono fun b hb => ?_)
  rcases hb with hb | hb
  · exact hb
  · exact hb.mono (fun y hy => by
      rcases List.mem_cons.1 hy with rfl | hy
      · exact ht
      · exact List.mem_of_mem_erase hy)

/-- An endpoint (or notification) outside the nodes of `Cs`. -/
def EpOutNodes (st : machine.Store S) [L : LawfulStore st] (Cs : Set U64) (s : S) (ep : U64) : Prop :=
  ∀ c ∈ Cs, ep.val + 16 ≤ L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ ep.val

/-- Changes to endpoint queues leave the scheduler queues alone. -/
theorem inv_epfoot {Cs : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    {W : List U64} {ep : U64} (h : SchedQueuesInv st T Cs s Q R) (hWT : ∀ w ∈ W, w ∈ T) (hE : EpPlaced T ep)
    (hEN : EpOutNodes st Cs s ep) (hw : WritesIn st s s' (EpFoot W ep)) : SchedQueuesInv st T Cs s' Q R := by
  have hT := h.tcbs
  have epv : ∀ a, a = epHeadA ep ∨ a = epTSA ep → a.val = ep.val ∨ a.val = ep.val + 8 := by
    rintro a (rfl | rfl)
    · exact Or.inl epHeadA_val
    · exact Or.inr (epTSA_val hE)
  -- TCB fields of `T` other than `Ep` links are outside the footprint.
  have fld : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 →
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := by
    intro y hy K hK hK8 h1 h2
    refine hw.mem_eq (field_aligned (hT y hy) hK hK8) ?_
    rintro (⟨w, hw', e | e⟩ | e)
    · rw [nextA_eq'] at e
      exact field_ne (hT y hy) (hT w (hWT w hw')) hK (by simp [nextOff]) (fun _ => by simp [nextOff]; exact h1) e
    · rw [prevA_eq'] at e
      exact field_ne (hT y hy) (hT w (hWT w hw')) hK (by simp [prevOff]) (fun _ => by simp [prevOff]; exact h2) e
    · have hv := epv _ e
      rw [field_val (hT y hy) hK] at hv
      have := hE.disj y hy
      omega
  have nod : ∀ c ∈ Cs, ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o) := by
    intro c hc o ho h8
    have hN := h.nodes c hc
    refine hw.mem_eq (nodeAt_aligned hN ho h8) ?_
    rintro (⟨w, hw', e | e⟩ | e)
    · exact nodeAt_ne_nextA hN ho (hWT w hw') (hT w (hWT w hw')) _ e
    · exact nodeAt_ne_prevA hN ho (hWT w hw') (hT w (hWT w hw')) _ e
    · have hv := epv _ e
      rw [nodeAt_val hN ho] at hv
      have := hEN c hc
      omega
  refine inv_of_agree h hw.1 hw.2.1 (fun y hy => ⟨?_, ?_⟩) (fun c hc o h1 h2 _ => nod c hc o h1 h2)
    (fun y hy => fld y hy _ (by simp) (by simp) (by simp) (by simp))
    (fun y hy => fld y hy _ (by simp) (by simp) (by simp) (by simp))
    (fun y hy => Or.inl (fld y hy _ (by simp) (by simp) (by simp) (by simp))) ?_
  · rw [nextA_eq']; exact fld y hy _ (by simp [nextOff]) (by simp [nextOff]) (by simp [nextOff]) (by simp [nextOff])
  · rw [prevA_eq']; exact fld y hy _ (by simp [prevOff]) (by simp [prevOff]) (by simp [prevOff]) (by simp [prevOff])
  · have e : L.actionW s' = L.actionW s := by
      unfold LawfulStore.actionW
      rw [hw.2.1, nodeAt_of_ksb hw.1]
      exact nod _ h.cur _ (by rw [act_val]; omega) (by rw [act_val])
    rw [e]; exact h.action

/-! ## `set_priority` -/

def blockA (t : U64) : U64 := core.num.U64.wrapping_add t 3336#u64

@[step] theorem obj.Tcb.block_obj.spec (s : S) (t : obj.Tcb) :
    obj.Tcb.block_obj st t s ⦃ v => v = L.mem s (blockA t) ⦄ := by
  unfold obj.Tcb.block_obj; step*; simp_all [blockA]

/-- Dequeue, set the priority, enqueue, reschedule: the running-thread path
of seL4 `setPriority`. -/
theorem dpe_path {Cs : Set U64} (s : S) (t : obj.Tcb) (prio : U64) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (h : SchedQueuesInv st T Cs s Q R) (ht : t ∈ T) (hv : prio.val < 256)
    (hnr : ∀ c ∈ Cs, t ∉ R c) :
    (do
      let s1 ← sched.dequeue st s t
      let s2 ← obj.Tcb.set_prio st t s1 prio
      let s3 ← sched.enqueue st s2 t
      sched.reschedule_required st s3) ⦃ s' => ∃ Q', SchedQueuesInv st T Cs s' Q' R ⦄ := by
  refine WP.spec_bind (sched.dequeue.inv s t Q R h ht) ?_
  intro s1 h1
  -- `t` is in no ready queue now.
  have hout : ∀ c ∈ Cs, ∀ p : U64, p.val < 256 → t ∉ (if (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64
      then Function.update Q (L.mem s (affA t)) (Function.update (Q (L.mem s (affA t))) (L.mem s (prioA t))
        ((Q (L.mem s (affA t)) (L.mem s (prioA t))).erase t)) else Q) c p := by
    intro c hc p hp hm
    split at hm
    · rcases mem_upd2.1 hm with ⟨rfl, rfl, hm'⟩ | ⟨hne, hm'⟩
      · exact ((h.ready _ hc).1.rel _ hp).nodup.not_mem_erase hm'
      · exact hne ⟨(h.inQ c hc p hp t hm').1.symm, (h.inQ c hc p hp t hm').2.symm⟩
    · exact h.notQ ht (not_not.1 ‹_›) hc hp hm
  have hq1 : (L.mem s1 (inqA t) &&& sched.Q_QUEUED) = 0#u64 := by
    by_contra hc
    exact hout _ (h1.aff t ht) _ (h1.prio t ht) ((h1.queued t ht).1 hc)
  step as ⟨s2, s2_post⟩
  subst s2_post
  have h2 := inv_wr_prio h1 ht hq1 hv
  have hr2 : (L.mem (L.wr s1 (prioA t) prio) (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by
    by_contra hc
    exact hnr _ (h2.aff t ht) ((h2.released t ht).1 hc)
  refine WP.spec_bind (sched.enqueue.inv _ t _ R h2 ht (fun _ => hr2)) ?_
  intro s3 h3
  exact WP.spec_mono (sched.reschedule_required.inv s3 _ R h3) fun s' h' => h'.1

/-- The thread's endpoint (or notification) queue, as `set_priority` needs it. -/
def BlockedOK (st : machine.Store S) [L : LawfulStore st] (T Cs : Set U64) (s : S) (t : U64) : Prop :=
  ∃ xs, QueueRel (L.mem s) T .Ep (L.epQ s (L.mem s (blockA t))) xs ∧ t ∈ xs ∧
    EpPlaced T (L.mem s (blockA t)) ∧ EpOutNodes st Cs s (L.mem s (blockA t))

theorem blocked_prio {Cs : Set U64} {s : S} {t prio : U64} (hT : TcbPlaced T) (ht : t ∈ T)
    (hb : BlockedOK st T Cs s t) : BlockedOK st T Cs (L.wr s (prioA t) prio) t ∧
      L.mem (L.wr s (prioA t) prio) (blockA t) = L.mem s (blockA t) := by
  have hta := hT t ht
  have ha : Aligned (prioA t) := field_aligned hta (by simp) (by simp)
  have hbl : L.mem (L.wr s (prioA t) prio) (blockA t) = L.mem s (blockA t) :=
    L.mem_wr_ne ha (field_aligned hta (by simp) (by simp))
      (fun e => field_ne hta hta (by simp) (by simp) (fun _ => by simp) (UScalar.eq_of_val_eq e))
  obtain ⟨xs, hq, htx, hE, hEN⟩ := hb
  refine ⟨⟨xs, ?_, htx, hbl ▸ hE, ?_⟩, hbl⟩
  · rw [hbl]
    have hne : ∀ a, a = epHeadA (L.mem s (blockA t)) ∨ a = epTSA (L.mem s (blockA t)) →
        L.mem (L.wr s (prioA t) prio) a = L.mem s a := by
      rintro a ha'
      have hav : a.val = (L.mem s (blockA t)).val ∨ a.val = (L.mem s (blockA t)).val + 8 := by
        rcases ha' with rfl | rfl
        · exact Or.inl epHeadA_val
        · exact Or.inr (epTSA_val hE)
      have hal : Aligned a := by
        rcases ha' with rfl | rfl
        · exact (ep_aligned hE).1
        · exact (ep_aligned hE).2
      refine L.mem_wr_ne ha hal fun e => ?_
      rw [prioA_eq, field_val hta (by simp)] at e
      have := hE.disj t ht
      have : (3448#u64).val = 3448 := rfl
      omega
    have e : L.epQ (L.wr s (prioA t) prio) (L.mem s (blockA t)) = L.epQ s (L.mem s (blockA t)) := by
      simp only [LawfulStore.epQ, hne _ (Or.inl rfl), hne _ (Or.inr rfl)]
    rw [e]
    exact hq.wr_out hT ha fun y hy => ⟨fun e => field_ne hta (hq.addr hT y hy) (by simp) (by simp [nextOff])
      (fun _ => by simp [nextOff]) (e.trans (nextA_eq' _ _)),
      fun e => field_ne hta (hq.addr hT y hy) (by simp) (by simp [prevOff])
      (fun _ => by simp [prevOff]) (e.trans (prevA_eq' _ _))⟩
  · rw [hbl]; simpa [EpOutNodes, LawfulStore.nodeBase] using hEN

/-- `reorder_ep` after setting the priority of a blocked thread. -/
theorem blocked_path_ep {Cs : Set U64} (s : S) (t : obj.Tcb) (prio : U64) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (h : SchedQueuesInv st T Cs s Q R) (ht : t ∈ T) (hv : prio.val < 256)
    (hq0 : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64) (hb : BlockedOK st T Cs s t) :
    (do
      let s1 ← obj.Tcb.set_prio st t s prio
      let i ← obj.Tcb.block_obj st t s1
      endpoint.reorder_ep st s1 i t) ⦃ s' => ∃ Q', SchedQueuesInv st T Cs s' Q' R ⦄ := by
  have hT := h.tcbs
  step as ⟨s1, s1_post⟩
  subst s1_post
  have h1 := inv_wr_prio h ht hq0 hv
  obtain ⟨⟨xs, hq, htx, hE, hEN⟩, -⟩ := blocked_prio (prio := prio) hT ht hb
  step as ⟨i, i_post⟩
  subst i_post
  exact WP.spec_mono (endpoint.reorder_ep.foot _ _ t xs hT hE hq htx) fun s' hw => ⟨Q, inv_epfoot h1 hq.mem hE hEN hw⟩

/-- `reorder_ntfn` after setting the priority of a blocked thread. -/
theorem blocked_path_ntfn {Cs : Set U64} (s : S) (t : obj.Tcb) (prio : U64) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (h : SchedQueuesInv st T Cs s Q R) (ht : t ∈ T) (hv : prio.val < 256)
    (hq0 : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64) (hb : BlockedOK st T Cs s t) :
    (do
      let s1 ← obj.Tcb.set_prio st t s prio
      let i ← obj.Tcb.block_obj st t s1
      notification.reorder_ntfn st s1 i t) ⦃ s' => ∃ Q', SchedQueuesInv st T Cs s' Q' R ⦄ := by
  have hT := h.tcbs
  step as ⟨s1, s1_post⟩
  subst s1_post
  have h1 := inv_wr_prio h ht hq0 hv
  obtain ⟨⟨xs, hq, htx, hE, hEN⟩, -⟩ := blocked_prio (prio := prio) hT ht hb
  step as ⟨i, i_post⟩
  subst i_post
  exact WP.spec_mono (notification.reorder_ntfn.foot _ _ t xs hT hE hq htx) fun s' hw =>
    ⟨Q, inv_epfoot h1 hq.mem hE hEN hw⟩

/-- The running-thread path of `set_priority`. -/
theorem running_path {Cs : Set U64} (s : S) (t : obj.Tcb) (prio : U64) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (h : SchedQueuesInv st T Cs s Q R) (ht : t ∈ T) (hv : prio.val < 256)
    (hcur : t = L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) →
      (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64) :
    (do
      let b ← sched.queued st s t
      if b = true then do
        let s1 ← sched.dequeue st s t
        let s2 ← obj.Tcb.set_prio st t s1 prio
        let s3 ← sched.enqueue st s2 t
        sched.reschedule_required st s3
      else do
        let t1 ← sched.cur_thread st s
        let b1 ← obj.Tcb.Insts.CoreCmpPartialEqTcb.eq t t1
        if b1 = true then do
          let s1 ← sched.dequeue st s t
          let s2 ← obj.Tcb.set_prio st t s1 prio
          let s3 ← sched.enqueue st s2 t
          sched.reschedule_required st s3
        else obj.Tcb.set_prio st t s prio) ⦃ s' => ∃ Q', SchedQueuesInv st T Cs s' Q' R ⦄ := by
  step as ⟨b, b_post⟩
  split
  · have hq1 : (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64 := by
      intro hc; have := ‹b = true›; rw [b_post] at this; exact of_decide_eq_true this hc
    have htq := (h.queued t ht).1 hq1
    exact dpe_path s t prio Q R h ht hv fun c hc => h.QR (h.aff t ht) (h.prio t ht) htq hc
  · have hq0 : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 :=
      not_not.1 fun hc => ‹¬b = true› (by rw [b_post]; exact decide_eq_true hc)
    step as ⟨t1, t1_post⟩
    step as ⟨b1, b1_post⟩
    split
    · have e : t = t1 := by simpa [b1_post] using ‹b1 = true›
      have hr0 := hcur (e.trans t1_post)
      exact dpe_path s t prio Q R h ht hv fun c hc => h.notR ht hr0 hc
    · step as ⟨s1, s1_post⟩
      subst s1_post
      exact ⟨Q, inv_wr_prio h ht hq0 hv⟩

theorem ts_vals : sched.TS_RUNNING = 1#u64 ∧ sched.TS_RESTART = 2#u64 ∧ sched.TS_BLOCKED_ON_RECV = 3#u64 ∧
    sched.TS_BLOCKED_ON_SEND = 4#u64 ∧ sched.TS_BLOCKED_ON_NTFN = 6#u64 := by
  unfold sched.TS_RUNNING sched.TS_RESTART sched.TS_BLOCKED_ON_RECV sched.TS_BLOCKED_ON_SEND sched.TS_BLOCKED_ON_NTFN
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- seL4 `setPriority` (MCS) keeps the invariant (release queues unchanged),
given what seL4 knows of the thread: a thread that is not running is in no
ready queue; the current thread is in no release queue; a thread blocked on
an endpoint or notification is in its (well formed) queue. -/
theorem sched.set_priority.inv {Cs : Set U64} (s : S) (t : obj.Tcb) (prio : U64) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (h : SchedQueuesInv st T Cs s Q R) (ht : t ∈ T) (hv : prio.val < 256)
    (hcur : t = L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) →
      (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64)
    (hblk : L.mem s (stA t) ≠ sched.TS_RUNNING → L.mem s (stA t) ≠ sched.TS_RESTART →
      (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64)
    (hep : L.mem s (stA t) = sched.TS_BLOCKED_ON_RECV ∨ L.mem s (stA t) = sched.TS_BLOCKED_ON_SEND ∨
      L.mem s (stA t) = sched.TS_BLOCKED_ON_NTFN → BlockedOK st T Cs s t) :
    sched.set_priority st s t prio ⦃ s' => ∃ Q', SchedQueuesInv st T Cs s' Q' R ⦄ := by
  obtain ⟨r1, r2, r3, r4, r5⟩ := ts_vals
  unfold sched.set_priority
  step as ⟨sv, sv_post⟩
  subst sv_post
  split
  · exact running_path s t prio Q R h ht hv hcur
  · split
    · exact running_path s t prio Q R h ht hv hcur
    · have hq0 := hblk ‹_› ‹_›
      split
      · exact blocked_path_ep s t prio Q R h ht hv hq0 (hep (Or.inl ‹_›))
      · split
        · exact blocked_path_ep s t prio Q R h ht hv hq0 (hep (Or.inr (Or.inl ‹_›)))
        · split
          · exact blocked_path_ntfn s t prio Q R h ht hv hq0 (hep (Or.inr (Or.inr ‹_›)))
          · step as ⟨s1, s1_post⟩
            subst s1_post
            exact ⟨Q, inv_wr_prio h ht hq0 hv⟩

/-! ## `append` (`tcbSchedAppend`) -/

/-- The part of `append` after the bitmap update. -/
theorem append_tail (s1 : S) (t c p off : U64) (q : tcbqueue.Queue) (Q : U64 → List U64)
    (hT : TcbPlaced T) (ht : t ∈ T) (hp : p.val < 256)
    (hR : ReadyRel st T s1 c Q) (hB : BitmapOK st s1 c (fun p' => p' = p ∨ Q p' ≠ []))
    (hN : NodePlaced st T s1 c) (hN' : NodePlaced st T s1 (L.cpu s1))
    (hnot : ∀ p' : U64, p'.val < 256 → t ∉ Q p')
    (hoff : off = rqOff p) (hoff8 : core.num.U64.wrapping_add off 8#u64 = rqTailOff p)
    (hq : q = L.rqQ s1 c p) :
    (do
      let (q1, s2) ← tcbqueue.append st s1 tcbqueue.Link.Sched q t
      let s3 ← sched.q_set st s2 c off q1
      let s4 ← sched.set_flag st s3 t sched.Q_QUEUED true
      smp.remote_queue_update st s4 t) ⦃ s' =>
    ReadyQueues st T s' c (Function.update Q p (Q p ++ [t])) ⦄ := by
  have hta : TcbAddr t := hT t ht
  refine WP.spec_bind (tcbqueue.append.rel s1 .Sched q t (Q p) hT (hq ▸ hR.rel p hp) ht (hnot p hp)) ?_
  rintro ⟨q1, s2⟩ h2
  simp only [WP.uncurry'_pair] at h2
  obtain ⟨hr2, hf2⟩ := h2
  have hW : ∀ w ∈ t :: Q p, w ∈ T := by
    intro w hw; rcases List.mem_cons.1 hw with rfl | hw
    · exact ht
    · exact (hR.rel p hp).mem w hw
  have hN2 : NodePlaced st T s2 c := hN.framed hf2
  have hcpu2 : L.cpu s2 = L.cpu s1 := hf2.2.1
  have hN2' : NodePlaced st T s2 (L.cpu s2) := by rw [hcpu2]; exact hN'.framed hf2
  have hv12 := views_framed hT hN hW hf2
  step as ⟨s3, s3_post⟩
  step as ⟨s4, s4_post⟩
  subst hoff; rw [hoff8] at s3_post
  obtain ⟨e3p, e3o, e3l1, e3l2, hl3, hN3⟩ := q_set_views q1 hT hN2 hp
  rw [← s3_post] at e3p e3o e3l1 e3l2 hl3 hN3
  have hN3' : NodePlaced st T s3 (L.cpu s3) := by
    rw [s3_post]; simp only [LawfulStore.cpu_wr]; exact hN2'.wr.wr
  refine WP.spec_mono (smp.remote_queue_update.spec s4 t) ?_
  intro s5 h5
  have hN4 : NodePlaced st T s4 c := by rw [s4_post]; exact hN3.wr
  have hN4' : NodePlaced st T s4 (L.cpu s4) := by rw [s4_post]; simp only [LawfulStore.cpu_wr]; exact hN3'.wr
  have hv34 : ViewsEq st s3 s4 c := by rw [s4_post]; exact views_wr_inq hN3 ht hta
  have hl34 : LinksEq st T s3 s4 := by rw [s4_post]; exact links_wr_inq hT hta
  obtain ⟨hv45, hl45, -⟩ := remote.views hT hN4 hN4' h5
  have hv35 := hv34.trans hv45
  have hl35 := hl34.trans hl45
  have hrq5 : L.rqQ s5 c p = q1 := by rw [hv35.1 p hp, e3p]
  refine ⟨?_, ?_⟩
  · refine hR.update hT hp ?_ ?_ ?_ ?_
    · intro p' hp' hne
      rw [hv35.1 p' hp', e3o p' hp' hne, hv12.1 p' hp']
    · intro p' hp' hne y hy
      have hyT : y ∈ T := (hR.rel p' hp').mem y hy
      have hyW : y ∉ t :: Q p := by
        intro hy'; rcases List.mem_cons.1 hy' with rfl | hy'
        · exact hnot p' hp' hy
        · exact hR.disj p p' hp hp' (Ne.symm hne) y hy' hy
      have hWa : ∀ w ∈ t :: Q p, TcbAddr w := fun w hw => hT w (hW w hw)
      have h12n := hf2.2.2.next_eq hWa (hT y hyT) (l' := .Sched) (fun _ => hyW)
      have h12p := hf2.2.2.prev_eq hWa (hT y hyT) (l' := .Sched) (fun _ => hyW)
      exact ⟨((hl35 y hyT .Sched).1.trans (hl3 y hyT .Sched).1).trans h12n,
        ((hl35 y hyT .Sched).2.trans (hl3 y hyT .Sched).2).trans h12p⟩
    · rw [hrq5]; exact (hr2.links hl3).links hl35
    · intro p' hp' hne x hx hx'
      rcases List.mem_append.1 hx with hx | hx
      · exact hR.disj p p' hp hp' (Ne.symm hne) x hx hx'
      · simp only [List.mem_singleton] at hx; subst hx; exact hnot p' hp' hx'
  · have hB5 : BitmapOK st s5 c (fun p' => p' = p ∨ Q p' ≠ []) := by
      refine hB.agree ?_ ?_
      · rw [hv35.2.1, e3l1, hv12.2.1]
      · intro g hg; rw [hv35.2.2 g hg, e3l2 g hg, hv12.2.2 g hg]
    refine hB5.congr fun p' _ => ?_
    by_cases e : p' = p
    · subst e; simp
    · simp [e]

/-- seL4 `tcbSchedAppend`: like `enqueue`, at the end of the queue. -/
theorem sched.append.ready (s : S) (t : obj.Tcb) (Q : U64 → List U64) (hT : TcbPlaced T) (ht : t ∈ T)
    (hp : (L.mem s (prioA t)).val < 256)
    (hN : NodePlaced st T s (L.mem s (affA t))) (hN' : NodePlaced st T s (L.cpu s))
    (h : ReadyQueues st T s (L.mem s (affA t)) Q)
    (hq : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 → ∀ p : U64, p.val < 256 → t ∉ Q p) :
    sched.append st s t ⦃ s' => ReadyQueues st T s' (L.mem s (affA t))
      (if (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64 then Q
       else Function.update Q (L.mem s (prioA t)) (Q (L.mem s (prioA t)) ++ [t])) ⦄ := by
  have hta : TcbAddr t := hT t ht
  unfold sched.append
  step*
  have hq0 : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 := by
    by_contra hc; exact ‹¬b = true› (by rw [b_post]; exact decide_eq_true hc)
  simp only [hq0, ne_eq, not_true_eq_false, if_false]
  subst cpu_post prio_post off_post
  have hqq : q = L.rqQ s (L.mem s (affA t)) (L.mem s (prioA t)) := by
    rw [q_post, off_post1]; rfl
  by_cases hb1 : b1 = true
  · rw [ite_cond_eq_true _ _ (eq_true hb1)]
    refine WP.spec_bind (sched.add_to_bitmap.spec s _ dom _ hp) ?_
    rintro s1 ⟨v1, v2, rfl, hv1, hv2⟩
    have hg : (L.mem s (prioA t)).val / 64 < 4 := by omega
    have hN1 : NodePlaced st T (L.wr s (L.nodeAt s (L.mem s (affA t)) l1Off) v1) (L.mem s (affA t)) := hN.wr
    have hA2 : L.nodeAt s (L.mem s (affA t)) (l2Off ((L.mem s (prioA t)).val / 64)) =
        L.nodeAt (L.wr s (L.nodeAt s (L.mem s (affA t)) l1Off) v1) (L.mem s (affA t))
          (l2Off ((L.mem s (prioA t)).val / 64)) := by simp
    have hrq : ∀ p' : U64, p'.val < 256 → L.rqQ (L.wr (L.wr s (L.nodeAt s (L.mem s (affA t)) l1Off) v1)
        (L.nodeAt s (L.mem s (affA t)) (l2Off ((L.mem s (prioA t)).val / 64))) v2) (L.mem s (affA t)) p' =
        L.rqQ s (L.mem s (affA t)) p' := by
      intro p' hp'
      rw [hA2, rqQ_wr_node hN1 (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega) hp',
        rqQ_wr_node hN (by rw [l1Off_val]; omega) (by rw [l1Off_val]) hp', l2Off_val hg, l1Off_val,
        if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have hlk := (links_wr_node (v := v1) hT hN (by rw [l1Off_val]; omega) (by rw [l1Off_val])).trans
      (links_wr_node (v := v2) hT hN1 (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega))
    rw [← hA2] at hlk
    have hv2' : ∀ i, v2.bv.getLsbD i = ((L.l2W s (L.mem s (affA t)) ((L.mem s (prioA t)).val / 64)).bv.getLsbD i ||
        decide (i = (L.mem s (prioA t)).val % 64)) := by
      intro i; rw [hv2]
      unfold LawfulStore.l2W
      rw [rd_node_wr_node hN (by rw [l1Off_val]; omega) (by rw [l2Off_val hg]; omega) (by rw [l1Off_val])
        (by rw [l2Off_val hg]; omega), if_neg (by rw [l1Off_val, l2Off_val hg]; omega)]
    have hempty : Q (L.mem s (prioA t)) = [] :=
      ((h.1.rel _ hp).empty_iff hT).1 (by rw [← hqq]; simpa [b1_post] using hb1)
    apply append_tail _ t _ _ _ q Q hT ht hp
    · exact h.1.agree hrq fun p' hp' y hy => hlk y ((h.1.rel p' hp').mem y hy) _
    · exact BitmapOK.add hN hp h.2 hv1 hv2'
    · exact hN1.wr
    · simp only [LawfulStore.cpu_wr]; exact hN'.wr.wr
    · exact hq hq0
    · rfl
    · exact off_post1
    · rw [hrq _ hp, hqq]
  · rw [ite_cond_eq_false _ _ (eq_false hb1)]
    simp only [bind_ok]
    have hne : Q (L.mem s (prioA t)) ≠ [] := by
      rw [Ne, ← (h.1.rel _ hp).empty_iff hT, ← hqq]; simpa [b1_post] using hb1
    apply append_tail _ t _ _ _ q Q hT ht hp h.1 _ hN hN' (hq hq0) rfl off_post1 hqq
    refine h.2.congr fun p' _ => ?_
    by_cases e : p' = L.mem s (prioA t)
    · subst e; simp [hne]
    · simp [e]


attribute [local step] smp.remote_queue_update.spec

theorem append_foot_tail (s s1 : S) (t c p off : U64) (q : tcbqueue.Queue) (xs : List U64)
    (hT : TcbPlaced T) (ht : t ∈ T) (hp : p.val < 256) (hN : NodePlaced st T s c)
    (hN' : NodePlaced st T s (L.cpu s)) (h1 : WritesIn st s s1 (L.NodeOf s c (128 ≤ ·)))
    (hr : QueueRel (L.mem s1) T .Sched q xs) (hn : t ∉ xs)
    (hoff : off = rqOff p) (hoff8 : core.num.U64.wrapping_add off 8#u64 = rqTailOff p) :
    (do
      let (q1, s2) ← tcbqueue.append st s1 tcbqueue.Link.Sched q t
      let s3 ← sched.q_set st s2 c off q1
      let s4 ← sched.set_flag st s3 t sched.Q_QUEUED true
      smp.remote_queue_update st s4 t) ⦃ s' =>
    WritesIn st s s' (L.QFoot s (t :: xs) c (128 ≤ ·) t) ∧
      L.mem s' (inqA t) = L.mem s (inqA t) ||| sched.Q_QUEUED ⦄ := by
  have hta : TcbAddr t := hT t ht
  have hW : ∀ w ∈ t :: xs, w ∈ T := by
    intro w hw; rcases List.mem_cons.1 hw with rfl | hw
    · exact ht
    · exact hr.mem w hw
  refine WP.spec_bind (tcbqueue.append.rel s1 .Sched q t xs hT hr ht hn) ?_
  rintro ⟨q1, s2⟩ h2
  simp only [WP.uncurry'_pair] at h2
  obtain ⟨-, hf2⟩ := h2
  have w12 := hf2.writesIn
  have w02 := h1.trans w12
  step as ⟨s3, s3_post⟩
  have w23 : WritesIn st s2 s3 (L.NodeOf s c (128 ≤ ·)) := by
    subst hoff
    rw [s3_post, nodeAt_of_ksb w02.1, nodeAt_of_ksb w02.1, hoff8]
    exact ((writesIn_node (P := (128 ≤ ·)) hN (by rw [rqOff_val hp]; omega) (by rw [rqOff_val hp]; omega)
      (by rw [rqOff_val hp]; omega)).trans (writesIn_node (P := (128 ≤ ·)) hN (by rw [rqTailOff_val hp]; omega)
      (by rw [rqTailOff_val hp]; omega) (by rw [rqTailOff_val hp]; omega))).mono fun b hb => by
        rcases hb with hb | hb <;> exact hb
  have w03 := w02.trans w23
  step as ⟨s4, s4_post⟩
  simp only [ite_true] at s4_post
  have w34 : WritesIn st s3 s4 (· = inqA t) := by rw [s4_post]; exact writesIn_inq hta
  have w04 := w03.trans w34
  refine WP.spec_mono (smp.remote_queue_update.spec s4 t) ?_
  intro s5 h5
  have w45 := remote_writesIn hN' w04.1 w04.2.1 h5
  refine ⟨(w04.trans w45).mono fun b hb => ?_, ?_⟩
  · simp only [LawfulStore.QFoot]; tauto
  · have ni := inq_not_link_node (W := t :: xs) (Q := (· = 120)) hT hW hN' ht
    have ni' := inq_not_link_node (W := t :: xs) (Q := (128 ≤ ·)) hT hW hN ht
    rw [w45.mem_eq (inqA_aligned hta) ni.2, s4_post, L.mem_wr_same (inqA_aligned hta),
      w03.mem_eq (inqA_aligned hta) (by rintro (((h | h) | h)) <;> [exact ni'.2 h; exact ni'.1 h; exact ni'.2 h])]

/-- The footprint of `append`, as for `enqueue`. -/
theorem sched.append.foot (s : S) (t : obj.Tcb) (xs : List U64) (hT : TcbPlaced T) (ht : t ∈ T)
    (hp : (L.mem s (prioA t)).val < 256)
    (hN : NodePlaced st T s (L.mem s (affA t))) (hN' : NodePlaced st T s (L.cpu s))
    (hr : QueueRel (L.mem s) T .Sched (L.rqQ s (L.mem s (affA t)) (L.mem s (prioA t))) xs)
    (hq : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 → t ∉ xs) :
    sched.append st s t ⦃ s' => WritesIn st s s' (L.QFoot s (t :: xs) (L.mem s (affA t)) (128 ≤ ·) t) ∧
      L.mem s' (inqA t) = if (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64 then L.mem s (inqA t)
        else L.mem s (inqA t) ||| sched.Q_QUEUED ⦄ := by
  unfold sched.append
  step*
  · have hq1 : (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64 := by
      intro hc; have := ‹b = true›; rw [b_post] at this; exact of_decide_eq_true this hc
    simp only [ne_eq, hq1, not_false_eq_true, if_true]
    exact ⟨WritesIn.refl _ _, by trivial⟩
  have hq0 : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 := by
    by_contra hc; exact ‹¬b = true› (by rw [b_post]; exact decide_eq_true hc)
  simp only [hq0, ne_eq, not_true_eq_false, if_false]
  subst cpu_post prio_post off_post
  have hqq : q = L.rqQ s (L.mem s (affA t)) (L.mem s (prioA t)) := by
    rw [q_post, off_post1]; rfl
  by_cases hb1 : b1 = true
  · rw [ite_cond_eq_true _ _ (eq_true hb1)]
    refine WP.spec_bind (sched.add_to_bitmap.spec s _ dom _ hp) ?_
    rintro s1 ⟨v1, v2, rfl, -, -⟩
    have hg : (L.mem s (prioA t)).val / 64 < 4 := by omega
    have w1 : WritesIn st s (L.wr (L.wr s (L.nodeAt s (L.mem s (affA t)) l1Off) v1)
        (L.nodeAt s (L.mem s (affA t)) (l2Off ((L.mem s (prioA t)).val / 64))) v2)
        (L.NodeOf s (L.mem s (affA t)) (128 ≤ ·)) :=
      ((writesIn_node (P := (128 ≤ ·)) hN (by simp [l1Off_val]) (by simp [l1Off_val]) (by simp [l1Off_val])).trans
        (writesIn_node (P := (128 ≤ ·)) hN (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega)
          (by rw [l2Off_val hg]; omega))).mono fun b hb => by rcases hb with hb | hb <;> exact hb
    have hN1 : NodePlaced st T (L.wr s (L.nodeAt s (L.mem s (affA t)) l1Off) v1) (L.mem s (affA t)) := hN.wr
    have hr1 := (hr.wr_node (v := v1) hT hN (by rw [l1Off_val]; omega) (by rw [l1Off_val])).wr_node (v := v2)
      hT hN1 (off := l2Off ((L.mem s (prioA t)).val / 64)) (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega)
    rw [show L.nodeAt (L.wr s (L.nodeAt s (L.mem s (affA t)) l1Off) v1) (L.mem s (affA t))
      (l2Off ((L.mem s (prioA t)).val / 64)) = L.nodeAt s (L.mem s (affA t)) (l2Off ((L.mem s (prioA t)).val / 64))
      by simp] at hr1
    exact append_foot_tail s _ t _ _ _ q xs hT ht hp hN hN' w1 (hqq ▸ hr1) (hq hq0) rfl off_post1
  · rw [ite_cond_eq_false _ _ (eq_false hb1)]
    simp only [bind_ok]
    exact append_foot_tail s s t _ _ _ q xs hT ht hp hN hN' (WritesIn.refl _ _) (hqq ▸ hr) (hq hq0) rfl off_post1


/-- `tcbSchedAppend` preserves the invariant, as `enqueue` does. -/
theorem sched.append.inv {Cs : Set U64} (s : S) (t : obj.Tcb) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs s Q R) (ht : t ∈ T)
    (hr : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 → (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64) :
    sched.append st s t ⦃ s' => SchedQueuesInv st T Cs s'
      (if (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64 then Q
       else Function.update Q (L.mem s (affA t)) (Function.update (Q (L.mem s (affA t))) (L.mem s (prioA t))
         (Q (L.mem s (affA t)) (L.mem s (prioA t)) ++ [t]))) R ⦄ := by
  have hT := h.tcbs
  have hc := h.aff t ht
  have hp := h.prio t ht
  have hN := h.nodes _ hc
  have hN' := h.nodes _ h.cur
  have hR1 := h.ready _ hc
  have h1 := sched.append.ready s t _ hT ht hp hN hN' hR1 (fun h0 p hp => h.notQ ht h0 hc hp)
  have h2 := sched.append.foot s t _ hT ht hp hN hN' (hR1.1.rel _ hp) (fun h0 => h.notQ ht h0 hc hp)
  refine WP.spec_mono (WP.spec_and h1 h2) ?_
  rintro s' ⟨hRc, hw, hinq⟩
  by_cases hqd : (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64
  · rw [if_pos hqd] at hRc hinq ⊢
    have htq := (h.queued t ht).1 hqd
    have := inv_ready_step (W := t :: Q _ _) (xs' := Q (L.mem s (affA t)) (L.mem s (prioA t))) (tIn := True)
      h ht rfl rfl (fun w hw => List.mem_cons.1 hw)
      (fun _ c' hc' hm => h.QR hc hp htq hc' hm) hw (by rw [Function.update_eq_self]; exact hRc)
      (fun y => by by_cases e : y = t <;> simp [e, htq]) (by rw [hinq]; simpa using hqd) (by rw [hinq])
      (fun _ => h.QR hc hp htq hc)
    simpa [Function.update_eq_self] using this
  · have hq0 : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 := not_not.1 hqd
    rw [if_neg hqd] at hRc hinq ⊢
    have htq := h.notQ ht hq0 hc hp
    exact inv_ready_step (W := t :: Q _ _) (tIn := True) h ht rfl rfl (fun w hw => List.mem_cons.1 hw)
      (fun _ c' hc' => h.notR ht (hr hq0) hc') hw hRc
      (fun y => by by_cases e : y = t <;> simp [e])
      (by rw [hinq, or_qq_qq]; simpa using qq_ne) (by rw [hinq, or_qq_qr])
      (fun _ => h.notR ht (hr hq0) hc)


/-! ## `postpone` -/

def scTcbA (sc : U64) : U64 := core.num.U64.wrapping_add sc layout.sc.TCB
def scCoreA (sc : U64) : U64 := core.num.U64.wrapping_add sc layout.sc.CORE

@[step] theorem obj.Sc.tcb.spec (s : S) (sc : obj.Sc) : obj.Sc.tcb st sc s ⦃ v => v = L.mem s (scTcbA sc) ⦄ := by
  unfold obj.Sc.tcb; step*; simp_all [scTcbA]
@[step] theorem obj.Sc.cpu.spec (s : S) (sc : obj.Sc) : obj.Sc.cpu st sc s ⦃ v => v = L.mem s (scCoreA sc) ⦄ := by
  unfold obj.Sc.cpu; step*; simp_all [scCoreA]

theorem OutsideObjs.ksb {Cs : Set U64} {s s' : S} {a : U64} (h : OutsideObjs st T Cs s a)
    (hk : L.ksb s' = L.ksb s) : OutsideObjs st T Cs s' a := by
  have e : ∀ c, L.nodeBase s' c = L.nodeBase s c := fun c => by simp [LawfulStore.nodeBase, hk]
  exact ⟨h.1, h.2.1, fun c hc => by rw [e]; exact h.2.2 c hc⟩

/-- After `dequeue`, the thread is in no ready queue. -/
theorem notQ_after_dequeue {Cs : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {t : U64}
    (h : SchedQueuesInv st T Cs s Q R) (ht : t ∈ T) :
    ∀ c ∈ Cs, ∀ p : U64, p.val < 256 → t ∉ (if (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64
      then Function.update Q (L.mem s (affA t)) (Function.update (Q (L.mem s (affA t))) (L.mem s (prioA t))
        ((Q (L.mem s (affA t)) (L.mem s (prioA t))).erase t)) else Q) c p := by
  intro c hc p hp hm
  split at hm
  · rcases mem_upd2.1 hm with ⟨rfl, rfl, hm'⟩ | ⟨hne, hm'⟩
    · exact ((h.ready _ hc).1.rel _ hp).nodup.not_mem_erase hm'
    · exact hne ⟨(h.inQ c hc p hp t hm').1.symm, (h.inQ c hc p hp t hm').2.symm⟩
  · exact h.notQ ht (not_not.1 ‹_›) hc hp hm

/-- seL4 `postpone`: the SC's thread moves from its ready queue to its
core's release queue, and the SC's core is told to reprogram its timer. The
thread must not be in a release queue already, and the SC's `CORE` word must
name a core and lie outside the TCBs and nodes. -/
theorem sched.postpone.inv {Cs : Set U64} (s : S) (sc : obj.Sc) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (h : SchedQueuesInv st T Cs s Q R) (ht : L.mem s (scTcbA sc) ∈ T)
    (hr0 : (L.mem s (inqA (L.mem s (scTcbA sc))) &&& sched.Q_RELEASE) = 0#u64)
    (hcore : OutsideObjs st T Cs s (scCoreA sc)) (hcs : L.mem s (scCoreA sc) ∈ Cs) :
    sched.postpone st s sc ⦃ s' => ∃ Q' R', SchedQueuesInv st T Cs s' Q' R' ⦄ := by
  unfold sched.postpone
  step as ⟨t, t_post⟩
  subst t_post
  set t := L.mem s (scTcbA sc) with ht_def
  have hT := h.tcbs
  have hc := h.aff t ht
  have hp := h.prio t ht
  have hN := h.nodes _ hc
  have hN' := h.nodes _ h.cur
  have hR1 := h.ready _ hc
  have hmemq := (h.queued t ht).1
  refine WP.spec_bind (WP.spec_and (sched.dequeue.inv s t Q R h ht)
    (sched.dequeue.foot s t _ hT ht hp hN hN' (hR1.1.rel _ hp) hmemq)) ?_
  rintro s1 ⟨h1, hw1, -⟩
  have hW1 : ∀ w ∈ Q (L.mem s (affA t)) (L.mem s (prioA t)), w ∈ T := fun w hw => h.memT hc hp hw
  have core1 : L.mem s1 (scCoreA sc) = L.mem s (scCoreA sc) :=
    hw1.mem_eq hcore.1 (qfoot_out hT hW1 hN hN' ht hc h.cur hcore)
  have hq1 : (L.mem s1 (inqA t) &&& sched.Q_QUEUED) = 0#u64 := by
    by_contra hcn
    exact notQ_after_dequeue h ht _ (h1.aff t ht) _ (h1.prio t ht) ((h1.queued t ht).1 hcn)
  have hr1 : (L.mem s1 (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by
    by_contra hcn
    exact h.notR ht hr0 (h1.aff t ht) ((h1.released t ht).1 hcn)
  have hT1 := h1.tcbs
  have hc1 := h1.aff t ht
  have hN1 := h1.nodes _ hc1
  have hN1' := h1.nodes _ h1.cur
  refine WP.spec_bind (WP.spec_and (sched.release_enqueue.inv s1 t _ R h1 ht hq1 hr1)
    (sched.release_enqueue.foot s1 t _ hT1 ht (h1.notR ht hr1 hc1) hN1 hN1' (h1.release _ hc1))) ?_
  rintro s2 ⟨h2, hw2, -⟩
  have hW2 : ∀ w ∈ t :: R (L.mem s1 (affA t)), w ∈ T := by
    intro w hw; rcases List.mem_cons.1 hw with rfl | hw
    · exact ht
    · exact h1.memTR hc1 hw
  have core2 : L.mem s2 (scCoreA sc) = L.mem s (scCoreA sc) :=
    (hw2.mem_eq hcore.1 (qfoot_out hT1 hW2 hN1 hN1' ht hc1 h1.cur (hcore.ksb hw1.1))).trans core1
  step as ⟨cpu, cpu_post⟩
  rw [core2] at cpu_post
  subst cpu_post
  step as ⟨s3, s3_post⟩
  subst s3_post
  refine ⟨_, _, inv_wr_node_low h2 hcs (by rw [repr_val]; omega) (by rw [repr_val]) ?_⟩
  have hN2 := h2.nodes _ hcs
  have hN2' := h2.nodes _ h2.cur
  have e : L.actionW (L.wr s2 (L.nodeAt s2 (L.mem s (scCoreA sc)) layout.node.REPROGRAM) 1#u64) = L.actionW s2 := by
    unfold LawfulStore.actionW
    simp only [LawfulStore.cpu_wr, nodeAt_wr]
    by_cases hcc : L.mem s (scCoreA sc) = L.cpu s2
    · rw [hcc, rd_node_wr_node hN2' (by rw [repr_val]; omega) (by rw [act_val]; omega) (by rw [repr_val])
        (by rw [act_val]), if_neg (by rw [repr_val, act_val]; omega)]
    · exact rd_node_wr_node_cpu hN2' hN2 (by rw [repr_val]; omega) (by rw [act_val]; omega) (by rw [repr_val])
        (by rw [act_val]) hcc
  rw [e]; exact h2.action

/-! ## `set_thread_state` -/

/-- A write to a TCB field the queues do not read keeps the invariant. -/
theorem inv_wr_field {Cs : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {t K v : U64}
    (h : SchedQueuesInv st T Cs s Q R) (ht : t ∈ T) (hK : K.val < 4096) (hK8 : K.val % 8 = 0)
    (hKn : K.val ≠ 3480 ∧ K.val ≠ 3488 ∧ K.val ≠ 3496 ∧ K.val ≠ 3504 ∧ K.val ≠ 3592 ∧ K.val ≠ 3520 ∧
      K.val ≠ 3448) :
    SchedQueuesInv st T Cs (L.wr s (core.num.U64.wrapping_add t K) v) Q R := by
  have hT := h.tcbs
  have hta := hT t ht
  have ha : Aligned (core.num.U64.wrapping_add t K) := field_aligned hta hK hK8
  have fld : ∀ y ∈ T, ∀ K' : U64, K'.val < 4096 → K'.val % 8 = 0 → (y = t → K.val ≠ K'.val) →
      L.mem (L.wr s (core.num.U64.wrapping_add t K) v) (core.num.U64.wrapping_add y K') =
        L.mem s (core.num.U64.wrapping_add y K') :=
    fun y hy K' h1 h2 hne => L.mem_wr_ne ha (field_aligned (hT y hy) h1 h2)
      (fun e => field_ne hta (hT y hy) hK h1 (fun e' => hne e'.symm) (UScalar.eq_of_val_eq e))
  obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := hKn
  refine inv_of_agree h (L.ksb_wr _ _ _) (L.cpu_wr _ _ _) (fun y hy => ⟨?_, ?_⟩) (fun c hc o' h1 h2 _ => ?_)
    (fun y hy => fld y hy _ (by simp) (by simp) (fun _ => by simpa using k5))
    (fun y hy => fld y hy _ (by simp) (by simp) (fun _ => by simpa using k6))
    (fun y hy => Or.inl (fld y hy _ (by simp) (by simp) (fun _ => by simpa using k7))) ?_
  · rw [nextA_eq']; exact fld y hy _ (by simp [nextOff]) (by simp [nextOff]) (fun _ => by simpa [nextOff] using k1)
  · rw [prevA_eq']; exact fld y hy _ (by simp [prevOff]) (by simp [prevOff]) (fun _ => by simpa [prevOff] using k2)
  · exact L.mem_wr_ne ha (nodeAt_aligned (h.nodes c hc) h1 h2)
      (fun e => node_ne_field (h.nodes c hc) h1 ht hta hK (UScalar.eq_of_val_eq e).symm)
  · have hN' := h.nodes _ h.cur
    have e : L.actionW (L.wr s (core.num.U64.wrapping_add t K) v) = L.actionW s := by
      unfold LawfulStore.actionW
      simp only [LawfulStore.cpu_wr, nodeAt_wr]
      exact L.mem_wr_ne ha (nodeAt_aligned hN' (by rw [act_val]; omega) (by rw [act_val]))
        (fun e => node_ne_field hN' (by rw [act_val]; omega) ht hta hK (UScalar.eq_of_val_eq e).symm)
    rw [e]; exact h.action

@[step] theorem obj.Tcb.set_state.spec (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_state st t s v ⦃ s' => s' = L.wr s (stA t) v ⦄ := by
  unfold obj.Tcb.set_state; step*; simp_all [stA]

theorem stA_eq (t : U64) : stA t = core.num.U64.wrapping_add t 3328#u64 := by
  unfold stA layout.tcb.STATE layout.tcb.F; rfl

/-- seL4 `setThreadState` (with `scheduleTCB`) keeps the invariant: it only
writes the state and, maybe, the action (choose-new). -/
theorem sched.set_thread_state.inv {Cs : Set U64} (s : S) (t : obj.Tcb) (v : U64) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (h : SchedQueuesInv st T Cs s Q R) (ht : t ∈ T) :
    sched.set_thread_state st s t v ⦃ s' => SchedQueuesInv st T Cs s' Q R ⦄ := by
  unfold sched.set_thread_state sched.schedule_tcb
  step as ⟨s1, s1_post⟩
  subst s1_post
  have h1 : SchedQueuesInv st T Cs (L.wr s (stA t) v) Q R := by
    rw [stA_eq]; exact inv_wr_field h ht (by simp) (by simp) (by simp)
  step*
  all_goals first | exact h1 | skip
  subst_vars
  rw [choose_val]
  exact (inv_set_action h1 (Or.inr (Or.inl rfl))).1

/-! ## `awaken`'s loop -/

/-- The loop of seL4 `awaken`: while the head of the current core's release
queue is ready, it leaves the release queue and `possible_switch_to` puts it
in a ready queue. The invariant holds throughout. -/
theorem sched.awaken_loop.inv {Cs : Set U64} (s : S) (fuel : U64) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (h : SchedQueuesInv st T Cs s Q R) :
    sched.awaken_loop st s fuel ⦃ s' => ∃ Q' R', SchedQueuesInv st T Cs s' Q' R' ⦄ := by
  unfold sched.awaken_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.val) (inv := fun x => ∃ Q' R', SchedQueuesInv st T Cs x.1 Q' R')
  · rintro ⟨s1, fu⟩ ⟨Q1, R1, h1⟩
    unfold sched.awaken_loop.body
    step*
    all_goals try exact ⟨Q1, R1, h1⟩
    -- the head of the release queue
    have hR := h1.release _ h1.cur
    have hhead : i1 = (L.relQ s1 (L.cpu s1)).head := by subst_vars; rfl
    have hne : i1 ≠ 0#u64 := by simpa [b_post] using ‹¬b = true›
    have hmem : i1 ∈ R1 (L.cpu s1) := by
      rw [hhead, hR.head] at hne ⊢
      cases hR' : R1 (L.cpu s1) with
      | nil => rw [hR'] at hne; exact absurd rfl hne
      | cons x xs => simp
    have hT1 : i1 ∈ T := h1.memTR h1.cur hmem
    refine WP.spec_bind (sched.release_remove.inv s1 i1 Q1 R1 h1 hT1) ?_
    intro s2 h2
    refine WP.spec_bind (sched.possible_switch_to.inv s2 i1 _ _ h2 hT1) ?_
    rintro s3 ⟨Q3, h3⟩
    simp only [WP.spec_ok]
    exact ⟨⟨Q3, _, h3⟩, by omega⟩
  · exact ⟨Q, R, h⟩

end

end Fl4Proofs.P1
