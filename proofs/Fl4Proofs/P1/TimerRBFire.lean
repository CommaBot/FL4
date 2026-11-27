/-
P1 (jc6d, TIMER-RB-PLAN stage 8, fire part): `timer::fire` keeps `TimerRB`.  Each round reads the current
core's `TIMER_MIN` (a key of its tree, so a TCB, or null), removes it (`timer.remove.rb`), signals its bound
notification and writes the current core's `REPROGRAM` word (not a timer word).  `send_signal`'s timer frame
is a named premise here [P] (`hsig`: it writes no timer word of `T` and no `TIMER_ROOT`/`TIMER_MIN` word, keeps
the key-space base and the current core); the queue proofs carry it internally as `TmFr` (QueueSignal) but
do not export it for every branch (#63's `RunningVM` paths), see TIMER-RB-PLAN §11.
-/
import Fl4Proofs.P1.TimerRBRmv
import Fl4Proofs.P1.QueueFire
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T Cs : Set U64}

/-- The loop invariant of `fire`: `TimerRB`, the cores' nodes placed, the current core one of `Cs`. -/
abbrev FireInv (st : machine.Store S) [L : LawfulStore st] (T Cs : Set U64) (s : S) : Prop :=
  TimerRB st T Cs s ∧ (∀ c ∈ Cs, NodePlaced st T s c) ∧ L.cpu s ∈ Cs

/-- [P] `send_signal` leaves the timer words alone. -/
abbrev SigTimerFrame {A : Type _} (st : machine.Store S) [L : LawfulStore st] (ar : machine.Arch A)
    (T Cs : Set U64) : Prop :=
  ∀ (s1 : S) (a1 : A) (n bd : U64), FireInv st T Cs s1 →
    notification.send_signal st ar s1 a1 n bd ⦃ s' _ => TAgree st T Cs s1 s' ∧ L.ksb s' = L.ksb s1 ∧
      L.cpu s' = L.cpu s1 ⦄

theorem FireInv.of_agree {s s' : S} (h : FireInv st T Cs s) (e : TAgree st T Cs s s') (ek : L.ksb s' = L.ksb s)
    (ec : L.cpu s' = L.cpu s) : FireInv st T Cs s' := by
  refine ⟨h.1.congr e, fun c hc => ?_, by rw [ec]; exact h.2.2⟩
  have eb : L.nodeBase s' c = L.nodeBase s c := by simp [LawfulStore.nodeBase, ek]
  exact ⟨by rw [eb]; exact (h.2.1 c hc).align, by rw [eb]; exact (h.2.1 c hc).fits, by rw [eb]; exact (h.2.1 c hc).disj⟩

/-- The current core's `REPROGRAM` write keeps `FireInv`. -/
theorem FireInv.reprogram {s : S} {v : U64} (hT : TcbPlaced T) (h : FireInv st T Cs s) :
    FireInv st T Cs (L.wr s (L.nodeAt s (L.cpu s) layout.node.REPROGRAM) v) := by
  have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
  have hoP : layout.node.REPROGRAM.val < 4288 := by rw [rp]; simp
  have hN := h.2.1 _ h.2.2
  have w : WritesIn st s (L.wr s (L.nodeAt s (L.cpu s) layout.node.REPROGRAM) v)
      (· = L.nodeAt s (L.cpu s) layout.node.REPROGRAM) := writesIn_wr (nodeAt_aligned hN hoP (by rw [rp]))
  have hA : ∀ b, b = L.nodeAt s (L.cpu s) layout.node.REPROGRAM → ¬ TW st T Cs s b := by
    rintro b rfl (⟨y, hy, K, h1, h2, e⟩ | ⟨c', hc', o, ho, e⟩)
    · exact node_ne_tz hT hN hoP (Tz.of_mem hy) (by omega) (congrArg UScalar.val e)
    · exact node_ne_node hN (h.2.1 c' hc') hoP (by rcases ho with h' | h' <;> omega)
        (fun _ => by rcases ho with h' | h' <;> omega) (congrArg UScalar.val e)
  exact FireInv.of_agree h (TAgree.of_writesIn w hT h.2.1 hA) (L.ksb_wr _ _ _) (L.cpu_wr _ _ _)

/-- **`fire`'s loop keeps `TimerRB`** (given `send_signal`'s timer frame). -/
theorem timer.fire_loop.rb {A : Type _} {ar : machine.Arch A} (hT : TcbPlaced T) (hsig : SigTimerFrame st ar T Cs)
    (s : S) (a : A) (now i : U64) (h : FireInv st T Cs s) :
    timer.fire_loop st ar s a now i ⦃ s' _ => FireInv st T Cs s' ⦄ := by
  unfold timer.fire_loop
  apply loop.spec_decr_nat (measure := fun x => 32 - x.2.2.val) (inv := fun x => FireInv st T Cs x.1)
  · rintro ⟨s1, a1, i1⟩ h1
    simp only at h1
    unfold timer.fire_loop.body
    dsimp only
    split
    · rename_i hi
      have hi32 : i1.val < 32 := by simpa using hi
      step with LawfulStore.cur_cpu_spec as ⟨c, ec⟩
      step with obj.node_get.spec as ⟨t, et⟩
      step with obj.Tcb.is_null.spec as ⟨b, eb⟩
      split
      · exact (WP.spec_ok _).2 h1
      rename_i hb
      have ht0 : t ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
      have htT : t ∈ T := by
        have := (h1.1.root_tz h1.2.2).2
        rw [← ec] at this; rw [← et] at this
        rcases this with e | e
        · exact absurd e ht0
        · exact e
      step with obj.Tcb.timer_deadline.val as ⟨d, ed⟩
      split
      · exact (WP.spec_ok _).2 h1
      step with obj.Tcb.timer_badge.val as ⟨bd, ebd⟩
      refine WP.spec_bind (timer.remove.rb s1 t hT htT h1.1 h1.2.1) fun s2 h2 => ?_
      obtain ⟨hR2, -, hN2, hw2⟩ := h2
      have ec2 : L.cpu s2 = L.cpu s1 := by
        rcases hw2 with ⟨-, rfl⟩ | ⟨c', -, W, -, -, w⟩
        · rfl
        · exact w.2.1
      have h2 : FireInv st T Cs s2 := ⟨hR2, hN2, by rw [ec2]; exact h1.2.2⟩
      step with obj.Tcb.bound_ntfn.val as ⟨n, en⟩
      refine WP.spec_bind (Pₘ := fun r : S × A => FireInv st T Cs r.1) ?_ ?_
      · split
        · exact WP.spec_mono (hsig s2 a1 n bd h2) fun r hr => by
            obtain ⟨s', a'⟩ := r
            exact h2.of_agree hr.1 hr.2.1 hr.2.2
        · exact (WP.spec_ok _).2 h2
      rintro ⟨s3, a3⟩ h3
      simp only at h3
      try simp only [WP.uncurry'_pair]
      step with LawfulStore.cur_cpu_spec as ⟨c3, ec3⟩
      step with obj.node_set.spec as ⟨s4, es4⟩
      step as ⟨i4, ei4⟩
      have hlt : 32 - i4.val < 32 - i1.val := by omega
      try simp only [WP.spec_ok]
      subst es4 ec3
      have hF := FireInv.reprogram (v := 1#u64) hT h3
      exact ⟨hF.1, hF.2.1, hF.2.2, hlt⟩
    · exact (WP.spec_ok _).2 h1
  · exact h

/-- **`timer::fire` keeps `TimerRB`** (stage 8, fire part), given `send_signal`'s timer frame [P]. -/
theorem timer.fire.rb {A : Type _} {ar : machine.Arch A} (hT : TcbPlaced T) (hsig : SigTimerFrame st ar T Cs)
    (s : S) (a : A) (h : FireInv st T Cs s) :
    timer.fire st ar s a ⦃ s' _ => FireInv st T Cs s' ⦄ := by
  unfold timer.fire
  refine WP.spec_bind (L.cur_cpu_spec s) fun c _ => ?_
  refine WP.spec_bind (obj.node_get.spec s c _) fun now _ => ?_
  exact timer.fire_loop.rb hT hsig s a now 0#u64 h

end

end Fl4Proofs.P1
