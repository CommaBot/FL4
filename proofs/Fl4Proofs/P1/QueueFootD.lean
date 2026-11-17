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
`TCB` word, the receiver's `SC` and affinity fields, the scheduler's node
words, and the debug-list words (the receiver may change core, `FootD`). -/
theorem schedcontext.donate.kw {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (sc dst : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hsc : sc ∈ Scs) (hdst : dst ∈ T) :
    schedcontext.donate st ar s a sc dst ⦃ s' _ => FootD st T Cs Sg Scs Z Es s s' ⦄ := by
  have h0 := h.1.choose_spec.choose_spec
  have hT := h0.tcbs
  have hX := h.2.2.1
  have hO := hX.1
  have hsub := h.2.2.2.2.sub
  have hcO : scCoreA sc ∈ Ω := ((objs_omega hO hsub).2 sc hsc).2.1
  have hm : scTcbA sc ∈ Ω := ((objs_omega hO hsub).2 sc hsc).1
  unfold schedcontext.donate
  step with obj.Sc.tcb.spec as ⟨i, ei⟩
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => Foot st T Cs ∅ ∅ Z ∅ s r.1 ∧
      ∃ Q1 R1, SchedQueuesInv st T Cs Ω H r.1 Q1 R1) ?_ ?_
  · split
    · exact (WP.spec_ok _).2 ⟨Foot.refl _, h.1⟩
    rename_i hb
    have hi0 : i ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    have hiT : i ∈ T := by rw [ei]; exact hX.2.2.yt.1 sc hsc (by rw [← ei]; exact hi0)
    refine WP.spec_bind (WP.spec_and (smp.remote_tcb_stall.blk hA s a i h) (smp.remote_tcb_stall.spec hA s a i)) ?_
    rintro ⟨s2, a2⟩ ⟨⟨h2, -, -, -, -⟩, hs2⟩
    try simp only [WP.uncurry'_pair] at hs2 ⊢
    have f2 : Foot st T Cs ∅ ∅ Z ∅ s s2 := by
      rcases hs2 with rfl | ⟨v, rfl⟩
      · exact Foot.refl _
      · exact foot_node (h0.nodes _ h0.cur) h0.cur (by rw [ipi_val]; omega) (by rw [ipi_val]) (by rw [ipi_val]; omega)
    obtain ⟨⟨Q2, R2, q2⟩, hB2, -, -, hSg2⟩ := h2
    refine WP.spec_bind (WP.spec_and (sched.dequeue.sch (Sg := Sg) s2 i Q2 R2 q2 hB2 hSg2 hiT)
      (sched.dequeue.kw (Sg := ∅) (Scs := ∅) (Z := Z) (Es := ∅) s2 i q2 hiT)) fun s3 hh3 => ?_
    obtain ⟨⟨⟨⟨Q3, R3, q3⟩, hB3, fr3⟩, -, -⟩, f3⟩ := hh3
    refine WP.spec_bind (WP.spec_and (sched.release_remove.sch (Sg := Sg) s3 i Q3 R3 q3 hB3 (hSg2.fr fr3) hiT)
      (sched.release_remove.kw (Sg := ∅) (Scs := ∅) (Z := Z) (Es := ∅) s3 i q3 hiT)) fun s4 hh4 => ?_
    obtain ⟨⟨⟨⟨Q4, R4, q4⟩, -, -⟩, -, -, -⟩, f4⟩ := hh4
    step with obj.Tcb.set_sc.wr as ⟨s5, e5⟩
    subst e5
    have q5 := inv_wr_field (K := 3464#u64) (v := 0#u64) q4 hiT (by simp) (by simp) (by simp)
    have f5 : Foot st T Cs ∅ ∅ Z ∅ s4 (L.wr s4 (scA i) 0#u64) := by
      rw [scA_eq]; exact foot_field hT hiT (by simp) (by simp) (by simp) (by simp)
    have f05 : Foot st T Cs ∅ ∅ Z ∅ s (L.wr s4 (scA i) 0#u64) := (f2.trans f3).trans (f4.trans f5)
    step with sched.cur_thread.spec as ⟨t1, et1⟩
    step with tcb_eq.blk as ⟨b1, eb1⟩
    refine WP.spec_bind (Pₘ := fun s6 => Foot st T Cs ∅ ∅ Z ∅ (L.wr s4 (scA i) 0#u64) s6 ∧
        ∃ Q1 R1, SchedQueuesInv st T Cs Ω H s6 Q1 R1) ?_
      fun s6 ⟨f6, q6⟩ => (WP.spec_ok _).2 ⟨f05.trans f6, q6⟩
    have RR : sched.reschedule_required st (L.wr s4 (scA i) 0#u64) ⦃ s6 =>
        Foot st T Cs ∅ ∅ Z ∅ (L.wr s4 (scA i) 0#u64) s6 ∧ ∃ Q1 R1, SchedQueuesInv st T Cs Ω H s6 Q1 R1 ⦄ :=
      WP.spec_mono (WP.spec_and (sched.reschedule_required.kw _ q5) (sched.reschedule_required.inv _ _ _ q5))
        fun s6 ⟨f6, ⟨Q6, h6⟩, _, _⟩ => ⟨f6, _, _, h6⟩
    split
    · exact RR
    · step with sched.action.spec as ⟨i1, ei1⟩
      split
      · exact RR
      · exact (WP.spec_ok _).2 ⟨Foot.refl _, _, _, q5⟩
  rintro ⟨s1, a1⟩ ⟨f1, Q1, R1, h1⟩
  try simp only [WP.uncurry'_pair]
  have D1 : DbgTz st T Cs s1 := Foot0.dbg hT h0.nodes f1 hX.dbg
  have c1 : L.mem s1 (scCoreA sc) = L.mem s (scCoreA sc) := Foot0.out hT h0.nodes f1 (h0.omega _ hcO)
  refine WP.spec_mono (donate_tail.frame hA s1 a1 sc dst h1 D1 hO.ksb hsub hsc hdst
    (by rw [c1]; exact hX.2.2.core sc hsc)) ?_
  rintro ⟨s', a'⟩ w
  try simp only [WP.uncurry'_pair] at w ⊢
  refine (Foot.of0 (Sg := Sg) (Scs := Scs) (Es := Es) f1).d.trans (w.mono fun b hb => ?_)
  rcases hb with rfl | rfl | rfl | hb
  · exact Or.inl (kw_sg (hO.fixW sc hsc).1)
  · exact Or.inl (by rw [scA_eq]; exact kw_field hdst (by simp) (by simp) (by simp))
  · exact Or.inl (by rw [affA_eq]; exact kw_field hdst (by simp) (by simp) (by simp))
  · exact Or.inr hb

end

end Fl4Proofs.P1
