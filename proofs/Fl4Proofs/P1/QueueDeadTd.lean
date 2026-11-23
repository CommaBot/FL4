/-
P1: **a final thread cap's finalisation leaves the thread's timer deadline
word null** (`fin_cap_thread.td0`, for P3's `DeadX`: a dead TCB is not
armed).

The steps of `fin_thread.dead` (QueueDead), with the deadline word
`TIMER_DEADLINE` (`tdA`, offset 3528) tracked: `timer.remove` nulls it
(`timer.remove.rb`), and every later step keeps it:

* `unbind_tcb` (`schedcontext.unbind_tcb.tdK`: the reschedule, `dequeue` and
  `release_remove` are `Fr` frames, which keep the timer fields; then the
  thread's `SC` word and the SC's `TCB` word);
* `complete_yield_to` (`YW` writes: `Ω` words, register words and
  `YIELD_TO`, `yw_td`);
* `suspend` (`sched.suspend.all`'s `TmFr`);
* `debug_remove` (`objects.debug_remove.x`'s `TmFr`);
* `fpu_release` and the slot address read write nothing.
-/
import Fl4Proofs.P1.QueueDead
import Fl4Proofs.P1.QueueYield
import Fl4Proofs.P1.QueueTimerR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-- `YW` writes keep every thread's deadline word. -/
theorem yw_td {X : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hw : WritesIn st s s' (YW T Ω)) :
    ∀ y ∈ T, L.mem s' (tdA y) = L.mem s (tdA y) := by
  have hT := h.tcbs
  have K : ∀ y ∈ T, ∀ K0 : U64, K0.val < 4096 → K0.val % 8 = 0 → K0.val = 3528 →
      L.mem s' (core.num.U64.wrapping_add y K0) = L.mem s (core.num.U64.wrapping_add y K0) := by
    intro y hy K0 h1 h2 h3
    refine hw.mem_eq (field_aligned (hT y hy) h1 h2) fun hb => ?_
    rcases hb with hm | ⟨z, hz, K, hK, -, e⟩
    · exact out_ne_field (h.omega _ hm) hy (hT y hy) h1 rfl
    · exact field_ne (hT y hy) (hT z hz) h1 (by omega) (fun _ => by omega) e
  intro y hy
  show L.mem s' (core.num.U64.wrapping_add y 3528#u64) = L.mem s (core.num.U64.wrapping_add y 3528#u64)
  exact K y hy 3528#u64 (by simp) (by simp) (by simp)

/-- **`unbind_tcb` keeps every thread's deadline word** (the steps of
`schedcontext.unbind_tcb.dead`: `Fr` frames, then the thread's `SC` word
and the SC's `TCB` word). -/
theorem schedcontext.unbind_tcb.tdK (s : S) (sc : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hsc : sc ∈ Scs) (hsc0 : sc ≠ 0#u64) (hna : L.mem s (scTcbA sc) ≠ 0#u64 → L.actionW s ≠ L.mem s (scTcbA sc))
    (hidle : L.mem s (scTcbA sc) ≠ 0#u64 → L.idleW s ≠ L.mem s (scTcbA sc)) :
    schedcontext.unbind_tcb st s sc ⦃ s' => ∀ y ∈ T, L.mem s' (tdA y) = L.mem s (tdA y) ⦄ := by
  unfold schedcontext.unbind_tcb
  step with obj.Sc.tcb.spec as ⟨t, et⟩
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 fun _ _ => rfl
  rename_i hb
  have ht0 : t ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
  have htT : t ∈ T := by rw [et]; exact h.2.2.1.2.2.yt.1 sc hsc (by rw [← et]; exact ht0)
  have hna0 : L.actionW s ≠ t := by rw [et]; exact hna (by rw [← et]; exact ht0)
  have hid0 : L.idleW s ≠ t := by rw [et]; exact hidle (by rw [← et]; exact ht0)
  step with sched.cur_thread.spec as ⟨t1, et1⟩
  step with tcb_eq.blk as ⟨b1, eb1⟩
  -- the reschedule, when `t` is current
  refine WP.spec_bind (Pₘ := fun s1 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s1 ∧ Foot st T Cs Sg Scs Z ∅ s s1 ∧
      L.actionW s1 ≠ t ∧ (L.curW s1 = t → L.actionW s1 ≠ 0#u64) ∧ L.idleW s1 = L.idleW s ∧
      L.mem s1 (scTcbA sc) = L.mem s (scTcbA sc) ∧ (L.actionW s1 = L.actionW s ∨ L.actionW s1 = 1#u64) ∧
      L.cscW s1 = L.cscW s ∧ ∀ y ∈ T, L.mem s1 (tdA y) = L.mem s (tdA y)) ?_ ?_
  · split
    · rename_i hbt
      obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
      refine WP.spec_mono (WP.spec_and (sched.reschedule_required.schX (Sg := Sg) s Q R h0 hB hSg)
        (sched.reschedule_required.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) s h0)) ?_
      rintro s1 ⟨⟨⟨Q1, R1, h1⟩, hB1, f1, ea1, ec1, -, ei1, -⟩, fw1⟩
      refine ⟨⟨⟨Q1, R1, h1⟩, hB1, hX.fr f1, hS.fr f1, hSg.fr f1⟩, fw1, ?_, fun _ => by rw [ea1]; simp, ei1,
        f1.sig _ (hX.1.fixW sc hsc).1, Or.inr ea1, f1.csc,
        fun y hy => f1.tmr y hy 3528#u64 (by simp) (by simp) (by simp)⟩
      rw [ea1]; exact fun e => notT_small h0.tcbs (by simp) (e ▸ htT)
    · rename_i hbt
      have hne : t ≠ t1 := fun e => hbt (by rw [eb1, decide_eq_true_eq]; exact e)
      exact (WP.spec_ok _).2 ⟨h, Foot.refl _, hna0, fun e => absurd (by rw [et1]; exact e.symm) hne, rfl, rfl,
        Or.inl rfl, rfl, fun _ _ => rfl⟩
  rintro s1 ⟨⟨⟨Q1, R1, h1⟩, hB1, hX1, hS1, hSg1⟩, fw1, na1, cr1, ei1, sc1, ac1, cs1, bd1⟩
  -- dequeue
  have hc1 := h1.aff t htT
  have hp1 := h1.prio t htT
  refine WP.spec_bind (WP.spec_and (WP.spec_and (sched.dequeue.sch (Sg := Sg) s1 t Q1 R1 h1 hB1 hSg1 htT)
    (sched.dequeue.foot s1 t _ h1.tcbs htT hp1 (h1.nodes _ hc1) (h1.nodes _ h1.cur) ((h1.ready _ hc1).1.rel _ hp1)
      (h1.queued t htT).1)) (sched.dequeue.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) s1 t h1 htT)) ?_
  rintro s2 ⟨⟨⟨⟨⟨Q2, R2, h2⟩, hB2, f2⟩, ea2, ec2⟩, hw2, iq2⟩, fw2⟩
  have hc2 := h2.aff t htT
  refine WP.spec_bind (WP.spec_and (WP.spec_and (sched.release_remove.sch (Sg := Sg) s2 t Q2 R2 h2 hB2
      (hSg1.fr f2) htT)
    (sched.release_remove.foot s2 t _ h2.tcbs htT (h2.nodes _ hc2) (h2.nodes _ h2.cur) (h2.release _ hc2)
      (h2.released t htT).1)) (sched.release_remove.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) s2 t h2 htT)) ?_
  rintro s3 ⟨⟨⟨⟨⟨Q3, R3, h3⟩, hB3, f3⟩, ea3, ec3, -⟩, hw3, iq3⟩, fw3⟩
  have hX3 := (hX1.fr f2).fr f3
  have hSg3 := (hSg1.fr f2).fr f3
  refine WP.spec_bind (obj.Tcb.set_sc.wr s3 t 0#u64) fun s4 e4 => ?_
  subst e4
  refine WP.spec_mono (obj.Sc.set_tcb.wr _ sc 0#u64) fun s5 e5 => ?_
  subst e5
  intro y hy
  have hm : scTcbA sc ∈ Ω := hSg3.sub _ (hX3.1.fixW sc hsc).1
  have hT := h3.tcbs
  have hty : Aligned (tdA y) := field_aligned (hT y hy) (K := 3528#u64) (by simp) (by simp)
  rw [L.mem_wr_ne (h3.omega _ hm).1 hty (fun e => out_ne_field (h3.omega _ hm) hy (hT y hy) (K := 3528#u64) (by simp)
      e.symm),
    L.mem_wr_ne (scA_aligned (hT t htT)) hty (fun e => field_ne (hT t htT) (hT y hy) (K1 := 3464#u64) (K2 := 3528#u64)
      (by simp) (by simp) (fun _ => by simp) (by rw [← scA_eq]; exact UScalar.eq_of_val_eq e)),
    show tdA y = core.num.U64.wrapping_add y 3528#u64 from rfl, f3.tmr y hy 3528#u64 (by simp) (by simp) (by simp),
    f2.tmr y hy 3528#u64 (by simp) (by simp) (by simp)]
  exact bd1 y hy

/-- **`finalise_cap_object` of a final thread cap leaves the thread's
deadline word null** (module docstring). -/
theorem fin_thread.td0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (p : U64)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hp : p ∈ T) (hna : L.actionW s ≠ p)
    (hidle : L.idleW s ≠ p)
    (hv0 : L.mem s (core.num.U64.wrapping_add p 3664#u64) = 0#u64) :
    objects.finalise_cap_object st ar s a (.Thread p) true ⦃ r => L.mem r.2.1 (tdA p) = 0#u64 ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  simp only [ite_true]
  have hStart := h
  obtain ⟨⟨Q0, R0, hq0⟩, hb0, hx0, hs0, hg0⟩ := hStart
  refine WP.spec_bind (WP.spec_and (smp.remote_tcb_stall.blk hA s a p h)
    (smp.remote_tcb_stall.all hA s a p hq0 hb0 hx0 hs0 hg0)) ?_
  rintro ⟨s1, a1⟩ ⟨⟨h1, f1, ea1, -, ei1⟩, _, _, _, _, _, _, _, _, _, keep, _⟩
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (vcpu.detach_none ar s1 a1 p (by
    rw [keep p hp 3664#u64 (by simp) (by simp)]; exact hv0)) ?_
  intro r hr
  subst r
  try dsimp only
  refine WP.spec_bind (notification.unbind_notification.blkF s1 p h1 hp) fun s2 ⟨h2, f2, n2⟩ => ?_
  refine WP.spec_bind (WP.spec_and (timer.remove.tf (s0 := s2) s2 p (TF.start h2) hp)
    (timer.remove.rb s2 p (TInv.tcbs h2) hp (TInv.rb h2) (TInv.nodes h2))) fun s3 ⟨⟨h3, f3, n3, _⟩, _, td3, _⟩ => ?_
  have ea3 : L.actionW s3 = L.actionW s := by rw [n3.1, n2.1, ea1]
  have ei3 : L.idleW s3 = L.idleW s := by rw [n3.2.1, n2.2.1, ei1]
  step with obj.Tcb.sc.spec as ⟨i, ei⟩
  step with obj.Sc.is_null.spec as ⟨b, eb⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧
      L.actionW r.1 ≠ p ∧ L.mem r.1 (tdA p) = 0#u64) ?_ ?_
  · split
    · exact (WP.spec_ok _).2 ⟨h3, by rw [ea3]; exact hna, td3⟩
    rename_i hb
    have hi0 : i ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    obtain ⟨hiS, hit, -⟩ := h3.2.2.1.2.2.bound p hp (by rw [← ei]; exact hi0)
    rw [← ei] at hiS hit
    refine WP.spec_bind (WP.spec_and
      (schedcontext.unbind_tcb.blk s3 i h3 hiS hi0 (fun _ => by rw [hit, ea3]; exact hna)
        (fun _ => by rw [hit, ei3]; exact hidle))
      (schedcontext.unbind_tcb.tdK s3 i h3 hiS hi0 (fun _ => by rw [hit, ea3]; exact hna)
        (fun _ => by rw [hit, ei3]; exact hidle))) fun s5 ⟨hh5, k5⟩ => ?_
    obtain ⟨h5, -, ea5, -⟩ := hh5
    have na5 : L.actionW s5 ≠ p := by
      rcases ea5 with e | e
      · rw [e, ea3]; exact hna
      · rw [e]; exact fun e' => notT_small h5.1.choose_spec.choose_spec.tcbs (by simp) (e' ▸ hp)
    have td5 : L.mem s5 (tdA p) = 0#u64 := (k5 p hp).trans td3
    step with obj.Sc.yield_from.val as ⟨y, ey⟩
    step with obj.Tcb.is_null.spec as ⟨b1, eb1⟩
    split
    · exact (WP.spec_ok _).2 ⟨h5, na5, td5⟩
    · have hiS5 : i ∈ Scs := hiS
      have hy : y ≠ 0#u64 → y ∈ T := fun hy0 => by
        rw [ey]; exact h5.2.2.1.2.2.yt.2.2 i hiS5 (by rw [← ey]; exact hy0)
      refine WP.spec_mono (WP.spec_and (schedcontext.complete_yield_to.blk hA s5 a1 y h5 hy)
        (schedcontext.complete_yield_to.yw hA s5 a1 y h5 hy)) ?_
      rintro ⟨s6, a6⟩ ⟨⟨h6, -, n6⟩, w6⟩
      exact ⟨h6, by rw [n6.1]; exact na5, (yw_td h5.1.choose_spec.choose_spec w6 p hp).trans td5⟩
  rintro ⟨s4, a2⟩ ⟨h4, na4, td4⟩
  try simp only [WP.uncurry'_pair]
  have h4' := h4
  obtain ⟨⟨Q4, R4, hq4⟩, hb4, hx4, hs4, hg4⟩ := h4'
  refine WP.spec_bind (WP.spec_and (sched.suspend.blk s4 a2 p h4 hp na4)
    (sched.suspend.all s4 a2 p Q4 R4 hq4 hp hb4 hx4 hg4 hs4 na4 (hx4.2.2.yt.2.1 p hp))) ?_
  rintro ⟨s5, a3⟩ ⟨⟨h5, -⟩, _, _, _, _, _, _, tm5⟩
  try simp only [WP.uncurry'_pair]
  have td5 : L.mem s5 (tdA p) = 0#u64 := (tm5.2.1 p hp 3528#u64 (by simp) (by simp) (by simp)).trans td4
  refine WP.spec_bind (objects.debug_remove.x (X := ∅) s5 p h5 hp) fun s6 ⟨_, tm6, _⟩ => ?_
  have td6 : L.mem s6 (tdA p) = 0#u64 := (tm6.2.1 p hp 3528#u64 (by simp) (by simp) (by simp)).trans td5
  refine WP.spec_bind (hA.fpu_release a3 p) fun a4 _ => ?_
  refine WP.spec_bind (P0.obj.Tcb.slot.p0 p _) fun s7 _ => ?_
  exact (WP.spec_ok _).2 td6

/-- **Thread**: a final cap's `finalise_cap` leaves the thread's deadline
word null (`fin_thread.td0`). -/
theorem fin_cap_thread.td0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (p : U64)
    (ex : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hp : p ∈ T) (hna : L.actionW s ≠ p)
    (hidle : L.idleW s ≠ p) (hv0 : L.mem s (core.num.U64.wrapping_add p 3664#u64) = 0#u64) :
    objects.finalise_cap st ar s a (.Thread p) true ex ⦃ r => L.mem r.2.1 (tdA p) = 0#u64 ⦄ := by
  rw [fin_cap_eq_obj (by simp)]
  exact fin_thread.td0 hA s a p h hp hna hidle hv0

end
end Fl4Proofs.P1
