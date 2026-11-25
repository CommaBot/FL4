/-
# P2 (p2lf): what `schedule`'s switch block writes, step by step (real store)

The block `schedSw` (action = a woken thread) re-queues the current thread, queues the woken one (`enqueue` /
`append`), sets the action, and `switch_to_thread`s (`set_vm_root` changes no word, `dequeue`, `CUR_THREAD`).

* `SWN st T Y`: the words those steps may write, from `Y`: the ready-queue links and queue flags of the threads, and
  this core's node words `CUR_THREAD` (0), `SCHED_ACTION` (16), `IPI_PENDING` (120) and the ready queues / bitmaps
  (offsets ≥ 128) — every other node word (`CUR_SC`, `RELEASE_HEAD`, `TIMER_MIN`, …) is kept.
* `qfoot_swn`: P1's queue footprint `QFoot` of a queue of this core lies in `SWN`; `swn_trans`.
* `Grow` (with `Grow.refl` / `.pre` / `.app`): the ghost ready queues after prepends / appends of two threads,
  in the shape `pick_top` takes.
* `enq_step` / `app_step` / `deq_step` / `setact_step` / `setcur_step` / `switch_step`: each step on a thread of
  this core keeps P1's `SchedQueuesInv` (the ghost queues as P1's `.inv` lemmas update them) and writes in `SWN`.

No named premises.
-/
import Fl4Proofs.P2.FootTimerFireSx
import Fl4Proofs.P2.FootTimerFirePk
import Fl4Proofs.P2.FootTimerIrqCh
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T Cs Ω : Set U64} {H : Heap}

/-- The words `schedSw` may write, from `Y` (module docstring). -/
def SWN (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (Y : S) (b : U64) : Prop :=
  (∃ y ∈ T, b = nextA .Sched y ∨ b = prevA .Sched y ∨ b = inqA y) ∨
    L.NodeOf Y (L.cpu Y) (fun o => o = 0 ∨ o = 16 ∨ o = 120 ∨ 128 ≤ o) b

theorem SWN.ksb {Y Z : S} {b : U64} (hk : L.ksb Z = L.ksb Y) (hc : L.cpu Z = L.cpu Y) (h : SWN st T Z b) :
    SWN st T Y b := by
  rcases h with h | ⟨o, ho, h1, h2, e⟩
  · exact Or.inl h
  · exact Or.inr ⟨o, ho, h1, h2, by rw [e, hc, nodeAt_of_ksb hk]⟩

theorem swn_trans {Y Z X : S} (h₁ : WritesIn st Y Z (SWN st T Y)) (h₂ : WritesIn st Z X (SWN st T Z)) :
    WritesIn st Y X (SWN st T Y) :=
  (h₁.trans h₂).mono fun _ hb => hb.elim id (SWN.ksb h₁.1 h₁.2.1)

theorem qfoot_swn {s : S} {W : List U64} {c t b : U64} (hW : ∀ w ∈ W, w ∈ T) (hc : c = L.cpu s) (ht : t ∈ T)
    (h : L.QFoot s W c (128 ≤ ·) t b) : SWN st T s b := by
  rcases h with ⟨w, hw, e | e⟩ | ⟨o, ho, ho1, ho2, e⟩ | e | ⟨o, ho, ho1, ho2, e⟩
  · exact Or.inl ⟨w, hW w hw, Or.inl e⟩
  · exact Or.inl ⟨w, hW w hw, Or.inr (Or.inl e)⟩
  · exact Or.inr ⟨o, Or.inr (Or.inr (Or.inr ho)), ho1, ho2, by rw [e, hc]⟩
  · exact Or.inl ⟨t, ht, Or.inr (Or.inr e)⟩
  · exact Or.inr ⟨o, Or.inr (Or.inr (Or.inl ho)), ho1, ho2, e⟩

variable {Q : U64 → U64 → List U64} {Rq : U64 → List U64}

/-- `enqueue` of a thread of this core. -/
theorem enq_step (Z : S) (t : U64) (h : SchedQueuesInv st T Cs Ω H Z Q Rq) (ht : t ∈ T)
    (ha : L.mem Z (affA t) = L.cpu Z)
    (hr : (L.mem Z (inqA t) &&& sched.Q_QUEUED) = 0#u64 → (L.mem Z (inqA t) &&& sched.Q_RELEASE) = 0#u64)
    (hrun : (L.mem Z (inqA t) &&& sched.Q_QUEUED) = 0#u64 → Runnable (L.mem Z (stA t))) :
    sched.enqueue st Z t ⦃ Z' => WritesIn st Z Z' (SWN st T Z) ∧ SchedQueuesInv st T Cs Ω H Z'
      (if (L.mem Z (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64 then Q
       else Function.update Q (L.mem Z (affA t)) (Function.update (Q (L.mem Z (affA t))) (L.mem Z (prioA t))
         (t :: Q (L.mem Z (affA t)) (L.mem Z (prioA t))))) Rq ⦄ := by
  have hc := h.aff t ht
  have hp := h.prio t ht
  have hR1 := h.ready _ hc
  refine WP.spec_mono (WP.spec_and (sched.enqueue.inv Z t Q Rq h ht hr hrun)
    (sched.enqueue.foot Z t _ h.tcbs ht hp (h.nodes _ hc) (h.nodes _ h.cur) (hR1.1.rel _ hp)
      (fun h0 => h.notQ ht h0 hc hp))) ?_
  rintro Z' ⟨hi, hw, -⟩
  refine ⟨hw.mono fun b hb => qfoot_swn (fun w hw => ?_) ha ht hb, hi⟩
  rcases List.mem_cons.1 hw with rfl | hw
  · exact ht
  · exact (hR1.1.rel _ hp).mem w hw

/-- `append` of a thread of this core. -/
theorem app_step (Z : S) (t : U64) (h : SchedQueuesInv st T Cs Ω H Z Q Rq) (ht : t ∈ T)
    (ha : L.mem Z (affA t) = L.cpu Z)
    (hr : (L.mem Z (inqA t) &&& sched.Q_QUEUED) = 0#u64 → (L.mem Z (inqA t) &&& sched.Q_RELEASE) = 0#u64)
    (hrun : (L.mem Z (inqA t) &&& sched.Q_QUEUED) = 0#u64 → Runnable (L.mem Z (stA t))) :
    sched.append st Z t ⦃ Z' => WritesIn st Z Z' (SWN st T Z) ∧ SchedQueuesInv st T Cs Ω H Z'
      (if (L.mem Z (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64 then Q
       else Function.update Q (L.mem Z (affA t)) (Function.update (Q (L.mem Z (affA t))) (L.mem Z (prioA t))
         (Q (L.mem Z (affA t)) (L.mem Z (prioA t)) ++ [t]))) Rq ⦄ := by
  have hc := h.aff t ht
  have hp := h.prio t ht
  have hR1 := h.ready _ hc
  refine WP.spec_mono (WP.spec_and (sched.append.inv Z t Q Rq h ht hr hrun)
    (sched.append.foot Z t _ h.tcbs ht hp (h.nodes _ hc) (h.nodes _ h.cur) (hR1.1.rel _ hp)
      (fun h0 => h.notQ ht h0 hc hp))) ?_
  rintro Z' ⟨hi, hw, -⟩
  refine ⟨hw.mono fun b hb => qfoot_swn (fun w hw => ?_) ha ht hb, hi⟩
  rcases List.mem_cons.1 hw with rfl | hw
  · exact ht
  · exact (hR1.1.rel _ hp).mem w hw

/-- `dequeue` of a thread of this core. -/
theorem deq_step (Z : S) (t : U64) (h : SchedQueuesInv st T Cs Ω H Z Q Rq) (ht : t ∈ T)
    (ha : L.mem Z (affA t) = L.cpu Z) :
    sched.dequeue st Z t ⦃ Z' => WritesIn st Z Z' (SWN st T Z) ∧ SchedQueuesInv st T Cs Ω H Z'
      (if (L.mem Z (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64
       then Function.update Q (L.mem Z (affA t)) (Function.update (Q (L.mem Z (affA t))) (L.mem Z (prioA t))
         ((Q (L.mem Z (affA t)) (L.mem Z (prioA t))).erase t)) else Q) Rq ⦄ := by
  have hc := h.aff t ht
  have hp := h.prio t ht
  have hR1 := h.ready _ hc
  refine WP.spec_mono (WP.spec_and (sched.dequeue.inv Z t Q Rq h ht)
    (sched.dequeue.foot Z t _ h.tcbs ht hp (h.nodes _ hc) (h.nodes _ h.cur) (hR1.1.rel _ hp)
      (h.queued t ht).1)) ?_
  rintro Z' ⟨hi, hw, -⟩
  exact ⟨hw.mono fun b hb => qfoot_swn (fun w hw => (hR1.1.rel _ hp).mem w hw) ha ht hb, hi⟩

/-- `set_action` with a value the invariant admits. -/
theorem setact_step (Z : S) (v : U64) (h : SchedQueuesInv st T Cs Ω H Z Q Rq) (hv : v = 0#u64 ∨ v = 1#u64 ∨ v ∈ T)
    (hv2 : v ∈ T → Runnable (L.mem Z (stA v)) ∧ ∀ c ∈ Cs, v ∉ Rq c) :
    sched.set_action st Z v ⦃ Z' => WritesIn st Z Z' (SWN st T Z) ∧ SchedQueuesInv st T Cs Ω H Z' Q Rq ∧
      L.actionW Z' = v ⦄ := by
  refine WP.spec_mono (sched.set_action.spec Z v) fun Z' e => ?_
  subst e
  have hN := h.nodes _ h.cur
  obtain ⟨h1, h2⟩ := inv_set_action h hv hv2
  refine ⟨(writesIn_wr (nodeAt_aligned hN (by rw [act_val]; omega) (by rw [act_val]))).mono fun b e => ?_, h1, h2⟩
  exact Or.inr ⟨_, Or.inr (Or.inl (by rw [act_val])), by rw [act_val]; omega, by rw [act_val], e⟩

/-- `set_cur_thread` of a thread. -/
theorem setcur_step (Z : S) (t : U64) (h : SchedQueuesInv st T Cs Ω H Z Q Rq) (ht : t ∈ T) :
    sched.set_cur_thread st Z t ⦃ Z' => WritesIn st Z Z' (SWN st T Z) ∧ SchedQueuesInv st T Cs Ω H Z' Q Rq ∧
      L.curW Z' = t ∧ L.actionW Z' = L.actionW Z ⦄ := by
  refine WP.spec_mono (sched.set_cur_thread.spec Z t) fun Z' e => ?_
  subst e
  have hN := h.nodes _ h.cur
  have aC : Aligned (L.nodeAt Z (L.cpu Z) layout.node.CUR_THREAD) :=
    nodeAt_aligned hN (by rw [curth_val]; omega) (by rw [curth_val])
  refine ⟨(writesIn_wr aC).mono fun b e => ?_, inv_set_cur h ht, ?_, ?_⟩
  · exact Or.inr ⟨_, Or.inl (by rw [curth_val]), by rw [curth_val]; omega, by rw [curth_val], e⟩
  · unfold LawfulStore.curW
    simp only [LawfulStore.cpu_wr, nodeAt_wr]
    exact L.mem_wr_same aC
  · unfold LawfulStore.actionW
    simp only [LawfulStore.cpu_wr, nodeAt_wr]
    exact mem_wr_ne' aC (nodeAt_aligned hN (by rw [act_val]; omega) (by rw [act_val]))
      (nodeAt_ne hN (by rw [curth_val]; omega) (by rw [act_val]; omega) (by rw [curth_val, act_val]; omega))

/-- **`switch_to_thread t`** for a thread of this core: `set_vm_root` keeps the state, `dequeue`, `CUR_THREAD`. -/
theorem switch_step {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (Z : S) (a : A) (t : U64)
    (h : SchedQueuesInv st T Cs Ω H Z Q Rq) (ht : t ∈ T) (ha : L.mem Z (affA t) = L.cpu Z) :
    sched.switch_to_thread st ar Z a t ⦃ X _ => WritesIn st Z X (SWN st T Z) ∧
      (∃ Q', SchedQueuesInv st T Cs Ω H X Q' Rq) ∧ L.curW X = t ⦄ := by
  unfold sched.switch_to_thread
  refine WP.spec_bind (set_vm_root_same hA Z a t) ?_
  rintro ⟨Z1, a1⟩ e
  simp only [WP.uncurry'_pair] at e
  subst e
  refine WP.spec_bind (deq_step Z1 t h ht ha) ?_
  rintro Z2 ⟨w2, h2⟩
  refine WP.spec_bind (setcur_step Z2 t h2 ht) ?_
  rintro X ⟨w3, h3, ec, -⟩
  simp only [WP.spec_ok, WP.uncurry'_pair]
  exact ⟨swn_trans w2 w3, ⟨_, h3⟩, ec⟩

/-- The ghost ready queues of this core after the switch block's re-queues `Q'`, against those at `Y` (`Q`):
no non-empty queue empties, and a non-empty queue is the old one, has `a` or `b` at its head, or kept a non-empty
queue's head (`pick_top`'s premises). -/
def Grow (Q Q' : U64 → List U64) (a b : U64) : Prop :=
  ∀ p : U64, p.val < 256 → (Q p ≠ [] → Q' p ≠ []) ∧ (Q' p ≠ [] → Q' p = Q p ∨ (Q' p).head? = some a ∨
    (Q' p).head? = some b ∨ (Q p ≠ [] ∧ (Q' p).head? = (Q p).head?))

theorem Grow.refl (Q : U64 → List U64) (a b : U64) : Grow Q Q a b := fun _ _ => ⟨id, fun _ => Or.inl rfl⟩

theorem Grow.pre {Q Q1 : U64 → List U64} {a b x p0 : U64} (hg : Grow Q Q1 a b) (hx : x = a ∨ x = b) :
    Grow Q (Function.update Q1 p0 (x :: Q1 p0)) a b := by
  intro p hp
  by_cases e : p = p0
  · subst e
    simp only [Function.update_self]
    refine ⟨fun _ => List.cons_ne_nil _ _, fun _ => ?_⟩
    rcases hx with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  · simp only [Function.update_of_ne e]
    exact hg p hp

theorem Grow.app {Q Q1 : U64 → List U64} {a b x p0 : U64} (hg : Grow Q Q1 a b) (hx : x = a ∨ x = b) :
    Grow Q (Function.update Q1 p0 (Q1 p0 ++ [x])) a b := by
  intro p hp
  by_cases e : p = p0
  · subst e
    simp only [Function.update_self]
    refine ⟨fun _ => by simp, fun _ => ?_⟩
    by_cases h1 : Q1 p = []
    · rw [h1]
      rcases hx with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    · obtain ⟨y, ys, ey⟩ := List.exists_cons_of_ne_nil h1
      have hh : (Q1 p ++ [x]).head? = (Q1 p).head? := by rw [ey]; rfl
      rw [hh]
      rcases (hg p hp).2 h1 with e1 | e1 | e1 | ⟨e1, e2⟩
      · refine Or.inr (Or.inr (Or.inr ⟨?_, by rw [e1]⟩))
        rw [← e1]; exact h1
      · exact Or.inr (Or.inl e1)
      · exact Or.inr (Or.inr (Or.inl e1))
      · exact Or.inr (Or.inr (Or.inr ⟨e1, e2⟩))
  · simp only [Function.update_of_ne e]
    exact hg p hp

end

end Fl4Proofs.P2
