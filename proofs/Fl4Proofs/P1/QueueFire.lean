/-
P1: `timer::fire` keeps `TInv` (the IPC invariants, the timer-tree typing and
the notifications' bound-TCB typing), so `schedule` keeps the queue
invariant with `fire` proved rather than assumed.
-/
import Fl4Proofs.P1.QueueSignal
import Fl4Proofs.P1.QueueSchedule
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}


/-- The current core's `REPROGRAM` word. -/
theorem reprogram.tinv {s : S} {v : U64} (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    TInv st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s (L.nodeAt s (L.cpu s) layout.node.REPROGRAM) v) := by
  have hI := h
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
  have hw : WritesIn st s (L.wr s (L.nodeAt s (L.cpu s) layout.node.REPROGRAM) v) (L.Free s Ω Cs) :=
    free_node_write rfl h0.cur (h0.nodes _ h0.cur) (by simp [rp, LowFree])
  have f := fr_node (Sg := Sg) (v := v) h0 hSg h0.cur (by rw [rp]; omega) (by rw [rp]) (fun _ => by rw [rp]; omega)
    ⟨by rw [rp]; omega, by rw [rp]; omega⟩
  exact hI.of_tmfr ⟨⟨Q, R, inv_of_free h0 hw⟩, hB.free h0 hw, hX.fr f, hS.fr f, hSg.fr f⟩
    (TmFr.of_fr f hX.1 h0.nodes)

theorem bne_ne {n : U64} (h : (n != 0#u64) = true) : n ≠ 0#u64 := by simpa using h

/-- The loop of `timer::fire`: each round takes the earliest timer of the
current core, if due, out of the tree and signals its thread's bound
notification. -/
theorem timer.fire_loop.tinv {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A) (now i : U64) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    timer.fire_loop st ar s a now i ⦃ s' _ => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  unfold timer.fire_loop
  apply loop.spec_decr_nat (measure := fun x => 32 - x.2.2.val)
    (inv := fun x => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac x.1)
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
      have hI1 := h1
      obtain ⟨⟨Q1, R1, h1q⟩, -, hX1, -, -⟩ := h1
      have hTm1 := hX1.2.2.tm
      have htT : t ∈ T := by
        have := hTm1.min _ h1q.cur
        rw [← ec] at this; rw [← et] at this
        rcases this with e | e
        · exact absurd e ht0
        · exact e
      step with obj.Tcb.timer_deadline.val as ⟨d, ed⟩
      split
      · exact (WP.spec_ok _).2 hI1
      step with obj.Tcb.timer_badge.val as ⟨bd, ebd⟩
      refine WP.spec_bind (timer.remove.tinv s1 t hI1 htT) fun s2 h2 => ?_
      step with obj.Tcb.bound_ntfn.val as ⟨n, en⟩
      refine WP.spec_bind (Pₘ := fun r : S × A => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac r.1) ?_ ?_
      · split
        · rename_i hn0
          have hn0' : L.mem s2 (boundA t) ≠ 0#u64 := by rw [← en]; exact bne_ne hn0
          have hn : n ∈ Nt := by rw [en]; exact h2.2.2.1.2.2.bnd t htT hn0'
          exact WP.spec_mono (notification.send_signal.tinv hA s2 a1 n bd h2 hn (hNt n hn)) fun r hr => by
            obtain ⟨s', a'⟩ := r; simpa using hr
        · exact (WP.spec_ok _).2 h2
      rintro ⟨s3, a3⟩ h3
      simp only at h3
      try simp only [WP.uncurry'_pair]
      step with LawfulStore.cur_cpu_spec as ⟨c3, ec3⟩
      step with obj.node_set.spec as ⟨s4, es4⟩
      step as ⟨i4, ei4⟩
      try simp only [WP.spec_ok]
      subst es4 ec3
      exact ⟨reprogram.tinv h3, by omega⟩
    · exact (WP.spec_ok _).2 h1
  · exact h

/-- seL4 MCS `fireTimers` (l4h): `timer::fire` keeps `TInv`. -/
theorem timer.fire.tinv {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    timer.fire st ar s a ⦃ s' _ => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  unfold timer.fire
  refine WP.spec_bind (L.cur_cpu_spec s) fun c _ => ?_
  refine WP.spec_bind (obj.node_get.spec s c _) fun now _ => ?_
  exact timer.fire_loop.tinv hA hNt s a now 0#u64 h

/-- seL4 `schedule` keeps the queue invariant (and `BoundInv`, `XInv`,
`SCsOK`), with `timer::fire` proved: from `TInv`, the frame words being
outside the kernel area (`SgOK`), and `Nt` being the heap's notifications. -/
theorem sched.schedule.tinv {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hS : SCsOK st T Ω Sg Scs Z Ac s)
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hSg : SgOK st Ω Sg s) :
    sched.schedule st ar s a ⦃ s' _ => (∃ Q' R', SchedQueuesInv st T Cs Ω H s' Q' R') ∧ BoundInv st T Ac s' ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧ SCsOK st T Ω Sg Scs Z Ac s' ∧ TimerOK st T Cs s' ⦄ := by
  refine WP.spec_mono (sched.schedule.inv hA s a Q R h hB hS hX
    (WP.spec_mono (timer.fire.tinv hA hNt s a (BlkOK.tinv ⟨⟨Q, R, h⟩, hB, hX, hS, hSg⟩)) fun r hr => by
      obtain ⟨s', a'⟩ := r
      simp only [WP.uncurry'_pair] at hr ⊢
      exact ⟨hr.1, hr.2.1, hr.2.2.2.1, hr.2.2.1⟩)) fun r hr => ?_
  obtain ⟨s', a'⟩ := r
  simp only [WP.uncurry'_pair] at hr ⊢
  exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, hr.2.2.1.2.2.tm⟩

end

end Fl4Proofs.P1
