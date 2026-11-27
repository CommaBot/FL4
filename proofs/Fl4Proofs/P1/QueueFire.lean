/-
P1: `timer::fire` keeps `TInv` (the IPC invariants, the timer-tree typing and
the notifications' bound-TCB typing), so `schedule` keeps the queue
invariant with `fire` proved rather than assumed.

(int6) Since #80 / #85 a signal may write a VMEnter caller's IPC buffer: the
loop carries the buffer placement `BufAt` along the buffer-lookup frame
`IbFr` (`IbKeep`, deferred to par/a6f's `ibKeep_holds`).
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
  have f := fr_node (Sg := Sg) (hi8 := fun _ => by simp [layout.node.SCHED_ACTION, layout.node.REPROGRAM, layout.node.CUR_THREAD]) (v := v) h0 hSg h0.cur (by rw [rp]; omega) (by rw [rp]) (fun _ => by rw [rp]; omega)
    ⟨by rw [rp]; omega, by rw [rp]; omega⟩
  exact hI.of_tmfr ⟨⟨Q, R, inv_of_free h0 hw⟩, hB.free h0 hw, hX.fr f, hS.fr f, hSg.fr f⟩
    (TmFr.of_fr f hX.1 h0.nodes)

theorem bne_ne {n : U64} (h : (n != 0#u64) = true) : n ≠ 0#u64 := by simpa using h

/-- The loop of `timer::fire`: each round takes the earliest timer of the
current core, if due, out of the tree and signals its thread's bound
notification. -/
theorem timer.fire_loop.tinv {U : Set U64} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A) (now i : U64)
    (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hBA : BufAt st T Cs H Sg Scs Z U s) :
    timer.fire_loop st ar s a now i ⦃ s' _ => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ IbFr (L := L) T s s' ⦄ := by
  obtain ⟨IKr, IKs, IKp⟩ := IK T Cs Ω H Sg Rp Scs Nt Z Ac U
  unfold timer.fire_loop
  apply loop.spec_decr_nat (measure := fun x => 32 - x.2.2.val)
    (inv := fun x => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac x.1 ∧ IbFr (L := L) T s x.1)
  · rintro ⟨s1, a1, i1⟩ ⟨h1, f1⟩
    simp only at h1 f1
    unfold timer.fire_loop.body
    dsimp only
    split
    · rename_i hi
      have hi32 : i1.val < 32 := by simpa using hi
      step with LawfulStore.cur_cpu_spec as ⟨c, ec⟩
      step with obj.node_get.spec as ⟨t, et⟩
      step with obj.Tcb.is_null.spec as ⟨b, eb⟩
      split
      · exact (WP.spec_ok _).2 ⟨h1, f1⟩
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
      · exact (WP.spec_ok _).2 ⟨hI1, f1⟩
      step with obj.Tcb.timer_badge.val as ⟨bd, ebd⟩
      refine WP.spec_bind (WP.spec_and (timer.remove.tinv s1 t hI1 htT) (IKr s1 t hI1 htT)) fun s2 hh2 => ?_
      obtain ⟨h2, f2⟩ := hh2
      have f12 := f1.trans f2
      step with obj.Tcb.bound_ntfn.val as ⟨n, en⟩
      refine WP.spec_bind (Pₘ := fun r : S × A => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧ IbFr (L := L) T s r.1)
        ?_ ?_
      · split
        · rename_i hn0
          have hn0' : L.mem s2 (boundA t) ≠ 0#u64 := by rw [← en]; exact bne_ne hn0
          have hn : n ∈ Nt := by rw [en]; exact h2.2.2.1.2.2.bnd t htT hn0'
          have hb2 := hBA.of_fr f12
          exact WP.spec_mono (WP.spec_and (notification.send_signal.tinv hA s2 a1 n bd h2 hn (hNt n hn) hb2.1 hb2.2)
            (IKs s2 a1 n bd h2 hn (hNt n hn) hb2)) fun r hr => by
            obtain ⟨s', a'⟩ := r; simp only [WP.uncurry'_pair] at hr ⊢; exact ⟨hr.1, f12.trans hr.2⟩
        · exact (WP.spec_ok _).2 ⟨h2, f12⟩
      rintro ⟨s3, a3⟩ ⟨h3, f3⟩
      simp only at h3 f3
      try simp only [WP.uncurry'_pair]
      step with LawfulStore.cur_cpu_spec as ⟨c3, ec3⟩
      step with obj.node_set.spec as ⟨s4, es4⟩
      step as ⟨i4, ei4⟩
      try simp only [WP.spec_ok]
      subst es4 ec3
      exact ⟨reprogram.tinv h3, f3.trans (IKp s3 1#u64 h3), by omega⟩
    · exact (WP.spec_ok _).2 ⟨h1, f1⟩
  · exact ⟨h, IbFr.refl s⟩

/-- seL4 MCS `fireTimers` (l4h): `timer::fire` keeps `TInv`. -/
theorem timer.fire.tinv {U : Set U64} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hBA : BufAt st T Cs H Sg Scs Z U s) :
    timer.fire st ar s a ⦃ s' _ => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ IbFr (L := L) T s s' ⦄ := by
  unfold timer.fire
  refine WP.spec_bind (L.cur_cpu_spec s) fun c _ => ?_
  refine WP.spec_bind (obj.node_get.spec s c _) fun now _ => ?_
  exact timer.fire_loop.tinv hA IK hNt s a now 0#u64 h hBA

/-- seL4 `schedule` keeps the queue invariant (and `BoundInv`, `XInv`,
`SCsOK`), with `timer::fire` proved: from `TInv`, the frame words being
outside the kernel area (`SgOK`), and `Nt` being the heap's notifications. -/
theorem sched.schedule.tinv {U : Set U64} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A) (Q : U64 → U64 → List U64)
    (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hS : SCsOK st T Ω Sg Scs Z Ac s)
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hSg : SgOK st Ω Sg s) (hBA : BufAt st T Cs H Sg Scs Z U s) :
    sched.schedule st ar s a ⦃ s' _ => (∃ Q' R', SchedQueuesInv st T Cs Ω H s' Q' R') ∧ BoundInv st T Ac s' ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧ SCsOK st T Ω Sg Scs Z Ac s' ∧ TimerOK st T Cs s' ∧ L.cscW s' ∈ Ac ∧
      L.actionW s' = 0#u64 ∧ L.cscW s' = L.mem s' (scA (L.curW s')) ⦄ := by
  refine WP.spec_mono (sched.schedule.inv hA s a Q R h hB hS hX
    (WP.spec_mono (timer.fire.tinv hA IK hNt s a (BlkOK.tinv ⟨⟨Q, R, h⟩, hB, hX, hS, hSg⟩) hBA) fun r hr => by
      obtain ⟨s', a'⟩ := r
      simp only [WP.uncurry'_pair] at hr ⊢
      exact ⟨hr.1.1, hr.1.2.1, hr.1.2.2.2.1, hr.1.2.2.1⟩)) fun r hr => ?_
  obtain ⟨s', a'⟩ := r
  simp only [WP.uncurry'_pair] at hr ⊢
  exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.1.2.2.tm, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2⟩

/-- The invariants at every kernel entry (`handle_syscall`,
`handle_interrupt_entry`, the fault entries): every kernel exit goes through
`schedule`, which switches onto the current thread's SC (active) and sets
the action to resume, so besides the invariants the current SC is active, it
is the current thread's, and the current thread is not the switch-to
candidate (what `check_budget` at the entry needs).  Inside an entry only the
time-commit and preemption paths charge it after an invocation, and those
check `sc_active` (or a schedulable current thread on it,
`mcs_preemption_point.all`). -/
def EntryInv (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64)
    (Z : U64 → Nat) (Ac : Set U64) (s : S) : Prop :=
  (∃ Q R, SchedQueuesInv st T Cs Ω H s Q R) ∧ BoundInv st T Ac s ∧ XInv st T Cs Ω Sg Rp Scs Nt Z s ∧
    SCsOK st T Ω Sg Scs Z Ac s ∧ TimerOK st T Cs s ∧ L.cscW s ∈ Ac ∧ L.actionW s ≠ L.curW s ∧
    (L.mem s (scA (L.curW s)) ≠ 0#u64 → L.cscW s = L.mem s (scA (L.curW s)))

/-- `schedule` (the end of every kernel entry) establishes `EntryInv`. -/
theorem sched.schedule.entry {U : Set U64} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A) (Q : U64 → U64 → List U64)
    (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hS : SCsOK st T Ω Sg Scs Z Ac s)
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hSg : SgOK st Ω Sg s) (hBA : BufAt st T Cs H Sg Scs Z U s) :
    sched.schedule st ar s a ⦃ s' _ => EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ :=
  WP.spec_mono (sched.schedule.tinv hA IK hNt s a Q R h hB hS hX hSg hBA) fun r hr => by
    obtain ⟨s', a'⟩ := r
    simp only [WP.uncurry'_pair] at hr ⊢
    obtain ⟨⟨Q', R', h'⟩, hB', hX', hS', hT', hA', ha', hc'⟩ := hr
    refine ⟨⟨Q', R', h'⟩, hB', hX', hS', hT', hA', fun e => ?_, fun _ => hc'⟩
    rw [ha'] at e
    have e' := e.symm
    unfold LawfulStore.curW at e'
    exact (h'.tcbs _ h'.curT).ne0 (by rw [e']; rfl)

end

end Fl4Proofs.P1
