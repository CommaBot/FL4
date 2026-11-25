/-
# P2 (p2lf): the run of `schedule`'s switch block (real store)

At the post-`awaken` state `Y` whose action is the woken thread `w`, the real `schedSw` re-queues the current thread
`ct` if it is schedulable, then switches to `w` or queues `w` and chooses the head of the highest ready queue.

* `swn_tcb` / `swn_node` / `swn_ks` / `swn_out`: the words outside `SWN` (thread words other than the ready links
  and the queue flags, node words other than 0 / 16 / 120 / ≥ 128, kernel-global words, words outside the objects).
* `schedSwB_cases`: every run of `schedSwB` is a `switch_to_thread` of the action thread, or its `append` /
  `enqueue`, `set_action CHOOSE_NEW` and `schedule_choose_new_thread`.
* `grow_enq` / `grow_app` / `enq_ne` / `app_ne`: P1's ghost update of an `enqueue` / `append` in `Grow`'s shape.
* **`schedSw_run`**: the run writes in `SWN st T Y`, keeps `SchedQueuesInv`, and its new current thread is `ct`,
  `w` or the head of the highest non-empty ready queue of `Y` (the head `top_ok` checked).

No named premises.
-/
import Fl4Proofs.P2.FootTimerFireSy0
import Fl4Proofs.P2.FootTimerFireSw
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

section frames
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T Cs Ω : Set U64} {H : Heap}

theorem swn_tcb {Y : S} (hT : TcbPlaced T) (hN : NodePlaced st T Y (L.cpu Y)) {y K : U64} (hy : y ∈ T)
    (hK : K.val < 4096) (h1 : K.val ≠ 3480) (h2 : K.val ≠ 3488) (h3 : K.val ≠ 3592) :
    ¬ SWN st T Y (core.num.U64.wrapping_add y K) := by
  rintro (⟨z, hz, e | e | e⟩ | ⟨o, -, ho, -, e⟩)
  · rw [nextA_eq'] at e
    exact field_ne (hT y hy) (hT z hz) hK (by simp [nextOff]) (fun _ => by simp [nextOff]; omega) e
  · rw [prevA_eq'] at e
    exact field_ne (hT y hy) (hT z hz) hK (by simp [prevOff]) (fun _ => by simp [prevOff]; omega) e
  · rw [inqA_eq] at e
    exact field_ne (hT y hy) (hT z hz) hK (by simp) (fun _ => by simp; omega) e
  · exact node_ne_field hN ho hy (hT y hy) hK e.symm

theorem swn_node {Y : S} (hT : TcbPlaced T) (hN : NodePlaced st T Y (L.cpu Y)) {o : U64} (ho : o.val < 4288)
    (h0 : o.val ≠ 0) (h16 : o.val ≠ 16) (h120 : o.val ≠ 120) (h128 : o.val < 128) :
    ¬ SWN st T Y (L.nodeAt Y (L.cpu Y) o) := by
  rintro (⟨z, hz, e | e | e⟩ | ⟨o', hP, ho', -, e⟩)
  · rw [nextA_eq'] at e; refine node_ne_field hN ho hz (hT z hz) ?_ e; simp [nextOff]
  · rw [prevA_eq'] at e; refine node_ne_field hN ho hz (hT z hz) ?_ e; simp [prevOff]
  · rw [inqA_eq] at e; refine node_ne_field hN ho hz (hT z hz) ?_ e; simp
  · exact nodeAt_ne hN ho ho' (by rcases hP with h | h | h | h <;> omega) e

theorem swn_out {Y : S} (hT : TcbPlaced T) (hN : NodePlaced st T Y (L.cpu Y)) (hcC : L.cpu Y ∈ Cs) {b : U64}
    (hb : OutsideObjs st T Cs Y b) : ¬ SWN st T Y b := by
  rintro (⟨z, hz, e | e | e⟩ | ⟨o', -, ho', -, e⟩) <;> subst e
  · exact out_ne_field hb hz (hT z hz) (K := nextOff .Sched) (by simp [nextOff]) rfl
  · exact out_ne_field hb hz (hT z hz) (K := prevOff .Sched) (by simp [prevOff]) rfl
  · exact out_ne_field hb hz (hT z hz) (K := 3592#u64) (by simp) rfl
  · exact out_ne_node hb hcC hN ho' rfl

variable {Q : U64 → U64 → List U64} {Rq : U64 → List U64}

theorem swn_ks {Y : S} (h : SchedQueuesInv st T Cs Ω H Y Q Rq) {o : U64} (ho : o.val < 13568) :
    ¬ SWN st T Y (core.num.U64.wrapping_add (L.ksb Y) o) := by
  rintro (⟨z, hz, e | e | e⟩ | ⟨o', -, ho', -, e⟩)
  · rw [nextA_eq'] at e; exact ks_ne_tcb h ho hz (by simp [nextOff]) e
  · rw [prevA_eq'] at e; exact ks_ne_tcb h ho hz (by simp [prevOff]) e
  · rw [inqA_eq] at e; exact ks_ne_tcb h ho hz (by simp) e
  · exact ks_ne_node (h.nodes _ h.cur) ho ho' e

end frames

section ghost

theorem grow_enq {Q0 : U64 → List U64} {Q1 : U64 → U64 → List U64} {c a b t p af : U64} {qd : Prop}
    [Decidable qd] (hg : Grow Q0 (Q1 c) a b) (hx : t = a ∨ t = b) (hc : af = c) :
    Grow Q0 ((if qd then Q1 else Function.update Q1 af (Function.update (Q1 af) p (t :: Q1 af p))) c) a b := by
  by_cases h : qd
  · rw [if_pos h]; exact hg
  · rw [if_neg h]; subst hc; rw [Function.update_self]; exact hg.pre hx

theorem grow_app {Q0 : U64 → List U64} {Q1 : U64 → U64 → List U64} {c a b t p af : U64} {qd : Prop}
    [Decidable qd] (hg : Grow Q0 (Q1 c) a b) (hx : t = a ∨ t = b) (hc : af = c) :
    Grow Q0 ((if qd then Q1 else Function.update Q1 af (Function.update (Q1 af) p (Q1 af p ++ [t]))) c) a b := by
  by_cases h : qd
  · rw [if_pos h]; exact hg
  · rw [if_neg h]; subst hc; rw [Function.update_self]; exact hg.app hx

theorem enq_ne {Q1 : U64 → U64 → List U64} {c t p af : U64} {qd : Prop} [Decidable qd] (hc : af = c)
    (hq : qd → t ∈ Q1 af p) :
    (if qd then Q1 else Function.update Q1 af (Function.update (Q1 af) p (t :: Q1 af p))) c p ≠ [] := by
  by_cases h : qd
  · rw [if_pos h]; subst hc; exact List.ne_nil_of_mem (hq h)
  · rw [if_neg h]; subst hc; simp

theorem app_ne {Q1 : U64 → U64 → List U64} {c t p af : U64} {qd : Prop} [Decidable qd] (hc : af = c)
    (hq : qd → t ∈ Q1 af p) :
    (if qd then Q1 else Function.update Q1 af (Function.update (Q1 af) p (Q1 af p ++ [t]))) c p ≠ [] := by
  by_cases h : qd
  · rw [if_pos h]; subst hc; exact List.ne_nil_of_mem (hq h)
  · rw [if_neg h]; subst hc; simp

theorem headD_of_head? {l : List U64} {x : U64} (h : l.head? = some x) : l.headD 0#u64 = x := by
  cases l with
  | nil => simp at h
  | cons y ys => simp at h; simp [h]

theorem headD_of_head?_eq {l l' : List U64} (h : l.head? = l'.head?) : l.headD 0#u64 = l'.headD 0#u64 := by
  cases l <;> cases l' <;> simp_all

theorem pick_cases {Q0 Q5 : U64 → List U64} {ct w h' x : U64} (hg : Grow Q0 Q5 ct w) (hh' : h'.val < 256)
    (hne' : Q5 h' ≠ []) (hmax' : ∀ p : U64, p.val < 256 → Q5 p ≠ [] → p.val ≤ h'.val)
    (hx : x = (Q5 h').headD 0#u64) :
    x = ct ∨ x = w ∨ ∃ h : U64, h.val < 256 ∧ Q0 h ≠ [] ∧ (∀ p : U64, p.val < 256 → Q0 p ≠ [] → p.val ≤ h.val) ∧
      x = (Q0 h).headD 0#u64 := by
  rcases pick_top (fun p hp => (hg p hp).1) (fun p hp => (hg p hp).2) hh' hne' hmax' with e | e | ⟨hq, e, top⟩
  · exact Or.inl (hx.trans (headD_of_head? e))
  · exact Or.inr (Or.inl (hx.trans (headD_of_head? e)))
  · exact Or.inr (Or.inr ⟨h', hh', hq, top, hx.trans (headD_of_head?_eq e)⟩)

end ghost

/-- **Every run of `schedSwB`** (module docstring). -/
theorem schedSwB_cases {S : Type _} {A : Type _} (M : machine.Store S) (ar : machine.Arch A) (s4 : S) (a1 : A)
    (act : U64) (was : Bool) {X : S} {a' : A} (e : schedSwB M ar s4 a1 act was = ok (X, a')) :
    sched.switch_to_thread M ar s4 a1 act = ok (X, a') ∨
    (do
        let s5 ← sched.append M s4 act
        let s6 ← sched.set_action M s5 sched.ACTION_CHOOSE_NEW
        sched.schedule_choose_new_thread M ar s6 a1) = ok (X, a') ∨
    (do
        let s5 ← sched.enqueue M s4 act
        let s6 ← sched.set_action M s5 sched.ACTION_CHOOSE_NEW
        sched.schedule_choose_new_thread M ar s6 a1) = ok (X, a') := by
  unfold schedSwB at e
  obtain ⟨_, -, e⟩ := bind_eq_ok e
  obtain ⟨_, -, e⟩ := bind_eq_ok e
  obtain ⟨_, -, e⟩ := bind_eq_ok e
  obtain ⟨_, -, e⟩ := bind_eq_ok e
  split at e
  · obtain ⟨_, -, e⟩ := bind_eq_ok e
    obtain ⟨_, -, e⟩ := bind_eq_ok e
    obtain ⟨_, -, e⟩ := bind_eq_ok e
    split at e
    · split at e
      · obtain ⟨_, -, e⟩ := bind_eq_ok e
        split at e
        · exact Or.inr (Or.inl e)
        · exact Or.inl e
      · exact Or.inl e
    · exact Or.inr (Or.inr e)
  · split at e
    · obtain ⟨_, -, e⟩ := bind_eq_ok e
      obtain ⟨_, -, e⟩ := bind_eq_ok e
      split at e
      · exact Or.inr (Or.inl e)
      · exact Or.inl e
    · exact Or.inl e

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T Cs Ω : Set U64} {H : Heap}
variable {Q : U64 → U64 → List U64} {Rq : U64 → List U64}

/-- The choose path after the woken thread is queued: `set_action`, `schedule_choose_new_thread` (domain time
left), `choose_thread` = `switch_to_thread` of the head of the highest queue. -/
theorem choose_run {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {Y Z5 : S} (a : A)
    {Q5 : U64 → U64 → List U64} {Q0 : U64 → List U64} {ct w p0 : U64}
    (h5 : SchedQueuesInv st T Cs Ω H Z5 Q5 Rq) (hW5 : WritesIn st Y Z5 (SWN st T Y))
    (hq : SchedQueuesInv st T Cs Ω H Y Q Rq)
    (hdt : L.mem Y (core.num.U64.wrapping_add (L.ksb Y) layout.ks.DOMAIN_TIME) ≠ 0#u64)
    (hg : Grow Q0 (Q5 (L.cpu Y)) ct w) (hp0 : p0.val < 256) (hne0 : Q5 (L.cpu Y) p0 ≠ [])
    {X : S} {a' : A}
    (e : (do
        let s6 ← sched.set_action st Z5 sched.ACTION_CHOOSE_NEW
        sched.schedule_choose_new_thread st ar s6 a) = ok (X, a')) :
    WritesIn st Y X (SWN st T Y) ∧ (∃ Q', SchedQueuesInv st T Cs Ω H X Q' Rq) ∧
      ∃ h' : U64, h'.val < 256 ∧ Q5 (L.cpu Y) h' ≠ [] ∧
        (∀ p : U64, p.val < 256 → Q5 (L.cpu Y) p ≠ [] → p.val ≤ h'.val) ∧
        L.curW X = (Q5 (L.cpu Y) h').headD 0#u64 := by
  obtain ⟨s6, e6, e⟩ := bind_eq_ok e
  have hs6 := setact_step Z5 sched.ACTION_CHOOSE_NEW h5 (Or.inr (Or.inl choose_val))
    (fun h => by have := (h5.tcbs _ h).align; simp [sched.ACTION_CHOOSE_NEW] at this)
  rw [e6, WP.spec_ok] at hs6
  obtain ⟨w6, h6, -⟩ := hs6
  have W6 := swn_trans hW5 w6
  have k6 : L.ksb s6 = L.ksb Y := W6.1
  have c6 : L.cpu s6 = L.cpu Y := W6.2.1
  have hd6 : L.mem s6 (core.num.U64.wrapping_add (L.ksb s6) layout.ks.DOMAIN_TIME) ≠ 0#u64 := by
    rw [k6, W6.mem_eq (ks_aligned (hq.nodes _ hq.cur) (by simp [layout.ks.DOMAIN_TIME])
      (by simp [layout.ks.DOMAIN_TIME])) (swn_ks hq (by simp [layout.ks.DOMAIN_TIME]))]
    exact hdt
  unfold sched.schedule_choose_new_thread at e
  rw [domain_time_eq] at e
  simp only [bind_ok] at e
  rw [if_neg hd6] at e
  simp only [bind_ok] at e
  have hN6 : NodePlaced st T s6 (L.cpu s6) := h6.nodes _ h6.cur
  have hR6 := h6.ready _ h6.cur
  rw [c6] at hR6
  rw [← c6] at hR6
  obtain ⟨h', hh', hne', hmax', -, -, -, hch⟩ := choose_head ar hN6 hR6 (p0 := p0) hp0 (by rw [c6]; exact hne0)
  rw [hch a] at e
  rw [c6] at hne' hmax' hch e
  have hmem := headD_mem hne' 0#u64
  have hdT : (Q5 (L.cpu Y) h').headD 0#u64 ∈ T := h6.memT h6.cur hh' (by rw [c6]; exact hmem)
  have hda : L.mem s6 (affA ((Q5 (L.cpu Y) h').headD 0#u64)) = L.cpu s6 :=
    (h6.inQ _ h6.cur h' hh' _ (by rw [c6]; exact hmem)).1
  have hsw := switch_step hA s6 a _ h6 hdT hda
  rw [e, WP.spec_ok] at hsw
  obtain ⟨w7, hQ7, hc7⟩ := hsw
  exact ⟨swn_trans W6 w7, hQ7, h', hh', hne', hmax', hc7⟩

set_option maxHeartbeats 4000000 in
/-- **The run of the switch block** (module docstring). -/
theorem schedSw_run {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (Y : S) (a : A) {w : U64}
    (hq : SchedQueuesInv st T Cs Ω H Y Q Rq) (hw : w ∈ T) (hwa : L.mem Y (affA w) = L.cpu Y)
    (hact : L.actionW Y = w) (hca : L.curW Y ∈ T → L.mem Y (affA (L.curW Y)) = L.cpu Y)
    (hdt : L.mem Y (core.num.U64.wrapping_add (L.ksb Y) layout.ks.DOMAIN_TIME) ≠ 0#u64)
    {X : S} {a' : A} (e : schedSw st ar Y a w = ok (X, a')) :
    WritesIn st Y X (SWN st T Y) ∧ (∃ Q', SchedQueuesInv st T Cs Ω H X Q' Rq) ∧
      (L.curW X = L.curW Y ∨ L.curW X = w ∨
        ∃ h : U64, h.val < 256 ∧ Q (L.cpu Y) h ≠ [] ∧
          (∀ p : U64, p.val < 256 → Q (L.cpu Y) p ≠ [] → p.val ≤ h.val) ∧
          L.curW X = (Q (L.cpu Y) h).headD 0#u64) := by
  have hT := hq.tcbs
  have hN := hq.nodes _ hq.cur
  have hcn : w ≠ sched.ACTION_CHOOSE_NEW := fun h => by
    have := (hT w hw).align; rw [h] at this; simp [sched.ACTION_CHOOSE_NEW] at this
  have hwR : ∀ c ∈ Cs, w ∉ Rq c := fun c hc => by
    have := (hq.actOK (by rw [hact]; exact hw)).2 c hc; rwa [hact] at this
  have hwrun : Runnable (L.mem Y (stA w)) := by have := (hq.actOK (by rw [hact]; exact hw)).1; rwa [hact] at this
  rw [schedSw_eq, cur_thread_ok] at e
  simp only [bind_ok] at e
  obtain ⟨was, hwas, e⟩ := bind_eq_ok e
  obtain ⟨s4, h4, e⟩ := bind_eq_ok e
  rw [if_neg hcn] at e
  -- the re-queue of the current thread
  obtain ⟨Q4, hq4, W4, hg4⟩ : ∃ Q4, SchedQueuesInv st T Cs Ω H s4 Q4 Rq ∧ WritesIn st Y s4 (SWN st T Y) ∧
      Grow (Q (L.cpu Y)) (Q4 (L.cpu Y)) (L.curW Y) w := by
    by_cases hb : was = true
    · subst hb
      rw [if_pos rfl] at h4
      have hs := sched.is_schedulable.spec' (L := L) Y (L.curW Y)
      rw [hwas, WP.spec_ok] at hs
      obtain ⟨hrun, -, hrel, -⟩ := hs rfl
      have hct : L.curW Y ∈ T := hq.curT
      have he := enq_step Y (L.curW Y) hq hct (hca hct) (fun _ => hrel) (fun _ => hrun)
      rw [h4, WP.spec_ok] at he
      exact ⟨_, he.2, he.1, grow_enq (Grow.refl _ _ _) (Or.inl rfl) (hca hct)⟩
    · rw [if_neg hb] at h4
      obtain rfl := ok_inj_ff h4
      exact ⟨Q, hq, WritesIn.refl _ _, Grow.refl _ _ _⟩
  have k4 : L.ksb s4 = L.ksb Y := W4.1
  have c4 : L.cpu s4 = L.cpu Y := W4.2.1
  have hT4 : ∀ {K : U64}, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3480 → K.val ≠ 3488 → K.val ≠ 3592 →
      L.mem s4 (core.num.U64.wrapping_add w K) = L.mem Y (core.num.U64.wrapping_add w K) := fun hK h8 h1 h2 h3 =>
    W4.mem_eq (field_aligned (hT w hw) hK h8) (swn_tcb hT hN hw hK h1 h2 h3)
  have ha4 : L.mem s4 (affA w) = L.cpu Y := by
    unfold affA; rw [hT4 (by simp) (by simp) (by simp) (by simp) (by simp)]; exact hwa
  have hr4 : (L.mem s4 (inqA w) &&& sched.Q_RELEASE) = 0#u64 := by
    by_contra h
    exact hwR _ (hq4.aff w hw) ((hq4.released w hw).1 h)
  have hrun4 : Runnable (L.mem s4 (stA w)) := by
    rw [stA_eq, hT4 (by simp) (by simp) (by simp) (by simp) (by simp), ← stA_eq]; exact hwrun
  have hp4 := hq4.prio w hw
  have hcur : ∀ {Z : S}, L.curW Z = w → L.curW Z = L.curW Y ∨ L.curW Z = w ∨
      ∃ h : U64, h.val < 256 ∧ Q (L.cpu Y) h ≠ [] ∧
        (∀ p : U64, p.val < 256 → Q (L.cpu Y) p ≠ [] → p.val ≤ h.val) ∧
        L.curW Z = (Q (L.cpu Y) h).headD 0#u64 := fun h => Or.inr (Or.inl h)
  rcases schedSwB_cases st ar s4 a w was e with e | e | e
  · have hsw := switch_step hA s4 a w hq4 hw (by rw [ha4, c4])
    rw [e, WP.spec_ok] at hsw
    obtain ⟨w5, hQ5, hc5⟩ := hsw
    exact ⟨swn_trans W4 w5, hQ5, hcur hc5⟩
  · obtain ⟨s5, e5, e⟩ := bind_eq_ok e
    have h5 := app_step s4 w hq4 hw (by rw [ha4, c4]) (fun _ => hr4) (fun _ => hrun4)
    rw [e5, WP.spec_ok] at h5
    obtain ⟨W5, hq5⟩ := h5
    obtain ⟨W6, hQ6, h', hh', hne', hmax', hc6⟩ := choose_run hA a hq5 (swn_trans W4 W5) hq hdt
      (grow_app hg4 (Or.inr rfl) ha4) hp4 (app_ne ha4 (fun hd => (hq4.queued w hw).1 hd)) e
    exact ⟨W6, hQ6, pick_cases (grow_app hg4 (Or.inr rfl) ha4) hh' hne' hmax' hc6⟩
  · obtain ⟨s5, e5, e⟩ := bind_eq_ok e
    have h5 := enq_step s4 w hq4 hw (by rw [ha4, c4]) (fun _ => hr4) (fun _ => hrun4)
    rw [e5, WP.spec_ok] at h5
    obtain ⟨W5, hq5⟩ := h5
    obtain ⟨W6, hQ6, h', hh', hne', hmax', hc6⟩ := choose_run hA a hq5 (swn_trans W4 W5) hq hdt
      (grow_enq hg4 (Or.inr rfl) ha4) hp4 (enq_ne ha4 (fun hd => (hq4.queued w hw).1 hd)) e
    exact ⟨W6, hQ6, pick_cases (grow_enq hg4 (Or.inr rfl) ha4) hh' hne' hmax' hc6⟩

end main

end Fl4Proofs.P2
