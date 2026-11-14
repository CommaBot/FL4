/-
P1: footprints (`Foot`, writes inside `KW`) of the scheduler operations the
P3 side calls, beyond those of `QueueFoot` (`enqueue`, `dequeue`,
`release_remove`, `set_action`, `schedule_tcb`, `set_thread_state`,
`reschedule_required`, `possible_switch_to`, `reply_unlink`): `donate`,
`release_enqueue`, and the Reply branch of `finalise_cap` with its
footprint.
-/
import Fl4Proofs.P1.QueueReply
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Es : Set U64}

theorem sched.release_enqueue.kw {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} (s : S)
    (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T)
    (hr0 : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64) :
    sched.release_enqueue st s t ⦃ s' => Foot st T Cs Sg Scs Z Es s s' ⦄ := by
  have hc := h.aff t ht
  refine WP.spec_mono (sched.release_enqueue.foot s t _ h.tcbs ht (h.notR ht hr0 hc) (h.nodes _ hc) (h.nodes _ h.cur)
    (h.release _ hc)) fun s' hh => Foot.of hh.1 fun b hb => hb.kw ?_ hc h.cur ht
      (fun o ho => by unfold RelOffs at ho; omega)
  intro w hw
  rcases List.mem_cons.1 hw with rfl | hw
  · exact ht
  · exact (h.release _ hc).mem w hw

/-- **The footprint of `donate`**: the donor's queue and SC words, the SC's
`TCB` word, the receiver's `SC` and affinity fields and the scheduler's
node words. -/
theorem schedcontext.donate.kw {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (sc dst : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hsc : sc ∈ Scs) (hdst : dst ∈ T) :
    schedcontext.donate st ar s a sc dst ⦃ s' _ => Foot st T Cs Sg Scs Z Es s s' ⦄ := by
  have hT := h.1.choose_spec.choose_spec.tcbs
  have hX := h.2.2.1
  have hO := hX.1
  have hsub := h.2.2.2.2.sub
  have hal : Aligned (scTcbA sc) := by
    obtain ⟨hP, hz⟩ := hO.sc sc hsc
    have := (sc_lo hP hz).1
    unfold Aligned; rw [scTcbA_val hP hz]; omega
  unfold schedcontext.donate
  step with obj.Sc.tcb.spec as ⟨i, ei⟩
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => Foot st T Cs Sg Scs Z Es s r.1) ?_ ?_
  · split
    · exact (WP.spec_ok _).2 (Foot.refl _)
    rename_i hb
    have hi0 : i ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    have hiT : i ∈ T := by rw [ei]; exact hX.2.2.yt.1 sc hsc (by rw [← ei]; exact hi0)
    refine WP.spec_bind (smp.remote_tcb_stall.blk hA s a i h) ?_
    rintro ⟨s2, a2⟩ ⟨h2, f2, -, -, -⟩
    try simp only [WP.uncurry'_pair]
    obtain ⟨⟨Q2, R2, q2⟩, hB2, -, -, hSg2⟩ := h2
    refine WP.spec_bind (WP.spec_and (sched.dequeue.sch (Sg := Sg) s2 i Q2 R2 q2 hB2 hSg2 hiT)
      (sched.dequeue.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) s2 i q2 hiT)) fun s3 hh3 => ?_
    obtain ⟨⟨⟨⟨Q3, R3, q3⟩, hB3, fr3⟩, -, -⟩, f3⟩ := hh3
    refine WP.spec_bind (WP.spec_and (sched.release_remove.sch (Sg := Sg) s3 i Q3 R3 q3 hB3 (hSg2.fr fr3) hiT)
      (sched.release_remove.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) s3 i q3 hiT)) fun s4 hh4 => ?_
    obtain ⟨⟨⟨⟨Q4, R4, q4⟩, -, -⟩, -, -, -⟩, f4⟩ := hh4
    step with obj.Tcb.set_sc.wr as ⟨s5, e5⟩
    subst e5
    have q5 := inv_wr_field (K := 3464#u64) (v := 0#u64) q4 hiT (by simp) (by simp) (by simp)
    have f5 : Foot st T Cs Sg Scs Z Es s4 (L.wr s4 (scA i) 0#u64) := by
      rw [scA_eq]; exact foot_field hT hiT (by simp) (by simp) (by simp) (by simp)
    have f05 : Foot st T Cs Sg Scs Z Es s (L.wr s4 (scA i) 0#u64) :=
      ((f2.mono (Set.empty_subset _)).trans f3).trans (f4.trans f5)
    step with sched.cur_thread.spec as ⟨t1, et1⟩
    step with tcb_eq.blk as ⟨b1, eb1⟩
    refine WP.spec_bind (Pₘ := fun s6 => Foot st T Cs Sg Scs Z Es (L.wr s4 (scA i) 0#u64) s6) ?_
      fun s6 f6 => (WP.spec_ok _).2 (f05.trans f6)
    split
    · exact sched.reschedule_required.kw _ q5
    · step with sched.action.spec as ⟨i1, ei1⟩
      split
      · exact sched.reschedule_required.kw _ q5
      · exact (WP.spec_ok _).2 (Foot.refl _)
  rintro ⟨s1, a1⟩ f1
  try simp only [WP.uncurry'_pair]
  step with obj.Sc.set_tcb.wr as ⟨s2, e2⟩
  subst e2
  have f2 : Foot st T Cs Sg Scs Z Es s1 (L.wr s1 (scTcbA sc) dst) := foot_wr hal (kw_sg (hO.fixW sc hsc).1)
  step with obj.Tcb.set_sc.wr as ⟨s3, e3⟩
  subst e3
  have f3 : Foot st T Cs Sg Scs Z Es (L.wr s1 (scTcbA sc) dst) (L.wr (L.wr s1 (scTcbA sc) dst) (scA dst) sc) := by
    rw [scA_eq]; exact foot_field hT hdst (by simp) (by simp) (by simp) (by simp)
  step with obj.Sc.cpu.spec as ⟨cpu, ecpu⟩
  unfold smp.migrate_tcb
  step with obj.Tcb.affinity.spec as ⟨af, eaf⟩
  refine WP.spec_bind (Pₘ := fun r : A × obj.Tcb => r.2 = dst) ?_ ?_
  · split
    · refine WP.spec_bind (hA.fpu_flush a1 dst) fun a2 _ => ?_
      refine WP.spec_bind (hA.fpu_release a2 dst) fun a3 _ => ?_
      exact (WP.spec_ok _).2 rfl
    · exact (WP.spec_ok _).2 rfl
  rintro ⟨a2, t2⟩ e2
  simp only at e2
  subst t2
  try simp only [WP.uncurry'_pair]
  step with obj.Tcb.set_affinity.wr as ⟨s4, e4⟩
  subst e4
  have f4 : Foot st T Cs Sg Scs Z Es (L.wr (L.wr s1 (scTcbA sc) dst) (scA dst) sc)
      (L.wr (L.wr (L.wr s1 (scTcbA sc) dst) (scA dst) sc) (affA dst) cpu) := by
    rw [affA_eq]; exact foot_field hT hdst (by simp) (by simp) (by simp) (by simp)
  have := f1.trans (f2.trans (f3.trans f4))
  simpa using this

end

end Fl4Proofs.P1
