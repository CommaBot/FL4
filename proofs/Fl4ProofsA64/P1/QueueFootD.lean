-- AArch64 port of Fl4Proofs.P1.QueueFootD (proofs/scratch/a64/port.py): the x86_64 text, re-checked
-- over Fl4CoreA64. Edits beyond the renaming are marked `-- a64:`.
/-
P1: footprints (`Foot`, writes inside `KW`) of the scheduler operations the
P3 side calls, beyond those of `QueueFoot` (`enqueue`, `dequeue`,
`release_remove`, `set_action`, `schedule_tcb`, `set_thread_state`,
`reschedule_required`, `possible_switch_to`, `reply_unlink`): `donate`,
`release_enqueue`, and the Reply branch of `finalise_cap` with its
footprint.

a64: the `donate` footprints take `hrv` (the receiver runs no VCPU; AArch64 `migrate_tcb`, `donate_tail.frame`),
carried over `donate`'s first half (two-word stall `remote_tcb_stall.ipi` / `.all`, `dequeue` / `release_remove`
by `field_qfoot`, the `SC` write, `reschedule_required.rv0`). No named premises.
-/
import Fl4ProofsA64.P1.QueueReply
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Es : Set U64}

theorem sched.release_enqueue.kwB {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} (s : S)
    (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T)
    (hr0 : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64) :
    sched.release_enqueue st s t ⦃ s' => FootB st T Cs Sg Scs Z Es s s' ⦄ := by
  have hc := h.aff t ht
  refine WP.spec_mono (sched.release_enqueue.foot s t _ h.tcbs ht (h.notR ht hr0 hc) (h.nodes _ hc) (h.nodes _ h.cur)
    (h.release _ hc)) fun s' hh => FootB.of hh.1 fun b hb => hb.kwB ?_ hc h.cur ht
      (fun o ho => by unfold RelOffs at ho; omega)
  intro w hw
  rcases List.mem_cons.1 hw with rfl | hw
  · exact ht
  · exact (h.release _ hc).mem w hw

theorem sched.release_enqueue.kw {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} (s : S)
    (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T)
    (hr0 : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64) :
    sched.release_enqueue st s t ⦃ s' => Foot st T Cs Sg Scs Z Es s s' ⦄ :=
  WP.spec_mono (sched.release_enqueue.kwB s t h ht hr0) (fun _ f => f.foot)

/-- **The footprint of `donate`**: the donor's queue and SC words, the SC's
`TCB` word, the receiver's `SC` and affinity fields, the scheduler's node
words, and the debug-list words (the receiver may change core, `FootD`). -/
theorem schedcontext.donate.kwCB {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (sc dst : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hsc : sc ∈ Scs) (hdst : dst ∈ T)
    (hrv : L.mem s (runVcpuA dst) = 0#u64) :
    schedcontext.donate st ar s a sc dst ⦃ s' _ => FootDB st T Cs Sg Scs Z Es s s' ∧
      (L.mem s (scTcbA sc) = 0#u64 → L.mem s (affA dst) = L.mem s (scCoreA sc) →
        FootB st T Cs Sg Scs Z Es s s') ⦄ := by
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
  have hdta := hT dst hdst
  refine WP.spec_bind (Pₘ := fun r : S × A => FootB st T Cs ∅ ∅ Z ∅ s r.1 ∧
      (L.mem s (scTcbA sc) = 0#u64 → r.1 = s) ∧ (∃ Q1 R1, SchedQueuesInv st T Cs Ω H r.1 Q1 R1) ∧
      L.mem r.1 (runVcpuA dst) = L.mem s (runVcpuA dst)) ?_ ?_
  · split
    · exact (WP.spec_ok _).2 ⟨FootB.refl _, fun _ => rfl, h.1, rfl⟩
    rename_i hb
    have hi0 : i ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    have hiT : i ∈ T := by rw [ei]; exact hX.2.2.yt.1 sc hsc (by rw [← ei]; exact hi0)
    -- a64: the two-word stall (`remote_tcb_stall.ipi`); `.all` keeps every TCB field
    obtain ⟨⟨Q0, R0, q0⟩, hB0, hX0, hS0, hSg0⟩ := h
    refine WP.spec_bind (WP.spec_and (WP.spec_and (smp.remote_tcb_stall.blk hA s a i ⟨⟨Q0, R0, q0⟩, hB0, hX0, hS0, hSg0⟩)
      (smp.remote_tcb_stall.ipi hA s a i)) (smp.remote_tcb_stall.all hA s a i q0 hB0 hX0 hS0 hSg0)) ?_
    rintro ⟨s2, a2⟩ ⟨⟨⟨h2, -, -, -, -⟩, hs2⟩, ⟨-, -, -, -, -, -, -, -, -, k2, -⟩⟩
    try simp only [WP.uncurry'_pair] at hs2 k2 ⊢
    have fIpi : ∀ {u u' : S}, NodePlaced st T u (L.cpu u) → L.cpu u ∈ Cs → IpiW st u u' →
        FootB st T Cs ∅ ∅ Z ∅ u u' ∧ L.ksb u' = L.ksb u ∧ L.cpu u' = L.cpu u := by
      intro u u' hN hc e
      rcases e with rfl | ⟨o, v, ho, rfl⟩
      · exact ⟨FootB.refl _, rfl, rfl⟩
      · refine ⟨?_, L.ksb_wr _ _ _, by rw [LawfulStore.cpu_wr]⟩
        rcases ho with ho | ho
        · exact footB_node hN hc (by rw [ho]; omega) (by rw [ho]) (by rw [ho]; omega)
        · exact footB_node hN hc (by rw [ho]; omega) (by rw [ho]) (by rw [ho]; omega)
    obtain ⟨s1', e1', e2'⟩ := hs2
    obtain ⟨g1, kk1, cc1⟩ := fIpi (h0.nodes _ h0.cur) h0.cur e1'
    obtain ⟨g2, -, -⟩ := fIpi (by rw [cc1]; exact (h0.nodes _ h0.cur).ksb kk1) (by rw [cc1]; exact h0.cur) e2'
    have f2 : FootB st T Cs ∅ ∅ Z ∅ s s2 := g1.trans g2
    have rv2 : L.mem s2 (runVcpuA dst) = L.mem s (runVcpuA dst) := k2 dst hdst 3672#u64 (by simp) (by simp)
    obtain ⟨⟨Q2, R2, q2⟩, hB2, -, -, hSg2⟩ := h2
    have hc2 := q2.aff i hiT
    have hp2 := q2.prio i hiT
    refine WP.spec_bind (WP.spec_and (WP.spec_and (sched.dequeue.sch (Sg := Sg) s2 i Q2 R2 q2 hB2 hSg2 hiT)
      (sched.dequeue.kwB (Sg := ∅) (Scs := ∅) (Z := Z) (Es := ∅) s2 i q2 hiT))
      (sched.dequeue.foot s2 i _ q2.tcbs hiT hp2 (q2.nodes _ hc2) (q2.nodes _ q2.cur) ((q2.ready _ hc2).1.rel _ hp2)
        (q2.queued i hiT).1)) fun s3 hh3 => ?_
    obtain ⟨⟨⟨⟨⟨Q3, R3, q3⟩, hB3, fr3⟩, -, -⟩, f3⟩, hw3, -⟩ := hh3
    have hW3 : ∀ w ∈ Q2 (L.mem s2 (affA i)) (L.mem s2 (prioA i)), w ∈ T := fun w hw => q2.memT hc2 hp2 hw
    have rv3 : L.mem s3 (runVcpuA dst) = L.mem s (runVcpuA dst) :=
      (field_qfoot q2.tcbs hW3 (q2.nodes _ hc2) (q2.nodes _ q2.cur) hiT hw3 hdst (K := 3672#u64) (by simp) (by simp)
        (by simp) (fun _ => by simp)).trans rv2
    have hc3 := q3.aff i hiT
    refine WP.spec_bind (WP.spec_and (WP.spec_and (sched.release_remove.sch (Sg := Sg) s3 i Q3 R3 q3 hB3 (hSg2.fr fr3) hiT)
      (sched.release_remove.kwB (Sg := ∅) (Scs := ∅) (Z := Z) (Es := ∅) s3 i q3 hiT))
      (sched.release_remove.foot s3 i _ q3.tcbs hiT (q3.nodes _ hc3) (q3.nodes _ q3.cur) (q3.release _ hc3)
        (q3.released i hiT).1)) fun s4 hh4 => ?_
    obtain ⟨⟨⟨⟨⟨Q4, R4, q4⟩, -, -⟩, -, -, -⟩, f4⟩, hw4, -⟩ := hh4
    have hW4 : ∀ w ∈ R3 (L.mem s3 (affA i)), w ∈ T := fun w hw => q3.memTR hc3 hw
    have rv4 : L.mem s4 (runVcpuA dst) = L.mem s (runVcpuA dst) :=
      (field_qfoot q3.tcbs hW4 (q3.nodes _ hc3) (q3.nodes _ q3.cur) hiT hw4 hdst (K := 3672#u64) (by simp) (by simp)
        (by simp) (fun _ => by simp)).trans rv3
    step with obj.Tcb.set_sc.wr as ⟨s5, e5⟩
    subst e5
    have rv5 : L.mem (L.wr s4 (scA i) 0#u64) (runVcpuA dst) = L.mem s (runVcpuA dst) := by
      rw [scA_eq]
      exact ((RvSt.wr_field (st := st) (s := s4) (v := 0#u64) hT hiT (K := 3464#u64) (by simp) (by simp) (by simp) (by simp)
        dst hdst).2).trans rv4
    have q5 := inv_wr_field (K := 3464#u64) (v := 0#u64) q4 hiT (by simp) (by simp) (by simp)
    have f5 : FootB st T Cs ∅ ∅ Z ∅ s4 (L.wr s4 (scA i) 0#u64) := by
      rw [scA_eq]; exact footB_field hT hiT (by simp) (by simp) (by simp) (by simp)
    have f05 : FootB st T Cs ∅ ∅ Z ∅ s (L.wr s4 (scA i) 0#u64) := (f2.trans f3).trans (f4.trans f5)
    step with sched.cur_thread.spec as ⟨t1, et1⟩
    step with tcb_eq.blk as ⟨b1, eb1⟩
    refine WP.spec_bind (Pₘ := fun s6 => FootB st T Cs ∅ ∅ Z ∅ (L.wr s4 (scA i) 0#u64) s6 ∧
        (∃ Q1 R1, SchedQueuesInv st T Cs Ω H s6 Q1 R1) ∧
        L.mem s6 (runVcpuA dst) = L.mem (L.wr s4 (scA i) 0#u64) (runVcpuA dst)) ?_
      fun s6 ⟨f6, q6, r6⟩ => (WP.spec_ok _).2 ⟨f05.trans f6, fun h0 => absurd (ei.trans h0) hi0, q6, r6.trans rv5⟩
    have RR : sched.reschedule_required st (L.wr s4 (scA i) 0#u64) ⦃ s6 =>
        FootB st T Cs ∅ ∅ Z ∅ (L.wr s4 (scA i) 0#u64) s6 ∧ (∃ Q1 R1, SchedQueuesInv st T Cs Ω H s6 Q1 R1) ∧
        L.mem s6 (runVcpuA dst) = L.mem (L.wr s4 (scA i) 0#u64) (runVcpuA dst) ⦄ :=
      WP.spec_mono (WP.spec_and (WP.spec_and (sched.reschedule_required.kwB _ q5) (sched.reschedule_required.inv _ _ _ q5))
        (sched.reschedule_required.rv0 _ q5))
        fun s6 ⟨⟨f6, ⟨Q6, h6⟩, _, _⟩, r6⟩ => ⟨f6, ⟨_, _, h6⟩, r6 dst hdst⟩
    split
    · exact RR
    · step with sched.action.spec as ⟨i1, ei1⟩
      split
      · exact RR
      · exact (WP.spec_ok _).2 ⟨FootB.refl _, ⟨_, _, q5⟩, rfl⟩
  rintro ⟨s1, a1⟩ ⟨f1, hs1, ⟨Q1, R1, h1⟩, rv1⟩
  try simp only [WP.uncurry'_pair]
  have D1 : DbgTz st T Cs s1 := Foot0.dbg hT h0.nodes f1.foot hX.dbg
  have c1 : L.mem s1 (scCoreA sc) = L.mem s (scCoreA sc) := Foot0.out hT h0.nodes f1.foot (h0.omega _ hcO)
  refine WP.spec_mono (donate_tail.frame hA s1 a1 sc dst h1 D1 hO.ksb hsub hsc hdst
    (by rw [c1]; exact hX.2.2.core sc hsc) (rv1.trans hrv)) ?_
  rintro ⟨s', a'⟩ ⟨w, wq⟩
  try simp only [WP.uncurry'_pair] at w wq ⊢
  refine ⟨(FootB.of0 (Sg := Sg) (Scs := Scs) (Es := Es) f1).d.trans (w.mono fun b hb => ?_), fun h0 he => ?_⟩
  · rcases hb with rfl | rfl | rfl | hb
    · exact Or.inl (kwB_sg (hO.fixW sc hsc).1)
    · exact Or.inl (by rw [scA_eq]; exact kwB_field hdst (by simp) (by simp) (by simp))
    · exact Or.inl (by rw [affA_eq]; exact kwB_field hdst (by simp) (by simp) (by simp))
    · exact Or.inr hb
  · have e1 : s1 = s := hs1 h0
    subst e1
    refine (wq he).mono fun b hb => ?_
    rcases hb with rfl | rfl
    · exact kwB_sg (hO.fixW sc hsc).1
    · rw [scA_eq]; exact kwB_field hdst (by simp) (by simp) (by simp)

theorem schedcontext.donate.kwC {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (sc dst : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hsc : sc ∈ Scs) (hdst : dst ∈ T)
    (hrv : L.mem s (runVcpuA dst) = 0#u64) :
    schedcontext.donate st ar s a sc dst ⦃ s' _ => FootD st T Cs Sg Scs Z Es s s' ∧
      (L.mem s (scTcbA sc) = 0#u64 → L.mem s (affA dst) = L.mem s (scCoreA sc) →
        Foot st T Cs Sg Scs Z Es s s') ⦄ :=
  WP.spec_mono (schedcontext.donate.kwCB (Es := Es) hA s a sc dst h hsc hdst hrv) fun r hr => by
    obtain ⟨s', a'⟩ := r
    simp only [WP.uncurry'_pair] at hr ⊢
    exact ⟨hr.1.footD, fun h1 h2 => (hr.2 h1 h2).foot⟩

/-- `schedcontext.donate.kwCB`'s footprint alone. -/
theorem schedcontext.donate.kwB {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (sc dst : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hsc : sc ∈ Scs) (hdst : dst ∈ T)
    (hrv : L.mem s (runVcpuA dst) = 0#u64) :
    schedcontext.donate st ar s a sc dst ⦃ s' _ => FootDB st T Cs Sg Scs Z Es s s' ⦄ :=
  WP.spec_mono (schedcontext.donate.kwCB (Es := Es) hA s a sc dst h hsc hdst hrv) fun r hr => by
    obtain ⟨s', a'⟩ := r; exact hr.1

/-- `schedcontext.donate.kwC`'s footprint alone. -/
theorem schedcontext.donate.kw {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (sc dst : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hsc : sc ∈ Scs) (hdst : dst ∈ T)
    (hrv : L.mem s (runVcpuA dst) = 0#u64) :
    schedcontext.donate st ar s a sc dst ⦃ s' _ => FootD st T Cs Sg Scs Z Es s s' ⦄ :=
  WP.spec_mono (schedcontext.donate.kwC (Es := Es) hA s a sc dst h hsc hdst hrv) fun r hr => by
    obtain ⟨s', a'⟩ := r; exact hr.1

end

end Fl4ProofsA64.P1
