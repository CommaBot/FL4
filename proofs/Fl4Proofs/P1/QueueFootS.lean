/-
P1: footprints (`Foot`, writes inside `KW`) of `schedule` and `timer::fire`
and of the operations below them: `postpone`, `resume`,
`maybe_donate_sched_context`, `send_signal`, the fire loop, `awaken`,
`choose_thread`, `switch_to_thread`, `switch_sched_context` and the timer
reprogramming.  The word set is `KW` with the heap's endpoints and
notifications as the queue objects (`EH H`): the TCB fields past the cap
slots (but the debug links), the node words (but the debug list head), the
frame words `Sg` (reply objects, SC `TCB`/`CORE`/`REPLY` words, the
notifications' frame words), the SC objects, and the endpoint and
notification queue words.
-/
import Fl4Proofs.P1.QueueFootD
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Es : Set U64}

/-- **The footprint of `postpone`**: the thread's ready and release queue
links, its cores' queue heads, and the SC core's `REPROGRAM` word. -/
theorem sched.postpone.kwB (s : S) (sc : obj.Sc) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (h : SchedQueuesInv st T Cs Ω H s Q R) (ht : L.mem s (scTcbA sc) ∈ T)
    (hr0 : (L.mem s (inqA (L.mem s (scTcbA sc))) &&& sched.Q_RELEASE) = 0#u64)
    (hcore : OutsideObjs st T Cs s (scCoreA sc)) (hcs : L.mem s (scCoreA sc) ∈ Cs) :
    sched.postpone st s sc ⦃ s' => FootB st T Cs Sg Scs Z Es s s' ⦄ := by
  unfold sched.postpone
  step with obj.Sc.tcb.spec as ⟨t, t_post⟩
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
  have F1 : FootB st T Cs Sg Scs Z Es s s1 :=
    FootB.of hw1 fun b hb => hb.kwB hW1 hc h.cur ht (fun o ho => by omega)
  have core1 : L.mem s1 (scCoreA sc) = L.mem s (scCoreA sc) :=
    hw1.mem_eq hcore.1 (qfoot_out hT hW1 hN hN' ht hc h.cur hcore)
  have hr1 : (L.mem s1 (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by
    by_contra hcn
    exact h.notR ht hr0 (h1.aff t ht) ((h1.released t ht).1 hcn)
  have hT1 := h1.tcbs
  have hc1 := h1.aff t ht
  have hN1 := h1.nodes _ hc1
  have hN1' := h1.nodes _ h1.cur
  refine WP.spec_bind (sched.release_enqueue.foot s1 t _ hT1 ht (h1.notR ht hr1 hc1) hN1 hN1'
    (h1.release _ hc1)) ?_
  rintro s2 ⟨hw2, -⟩
  have hW2 : ∀ w ∈ t :: R (L.mem s1 (affA t)), w ∈ T := by
    intro w hw; rcases List.mem_cons.1 hw with rfl | hw
    · exact ht
    · exact h1.memTR hc1 hw
  have F2 : FootB st T Cs Sg Scs Z Es s1 s2 :=
    FootB.of hw2 fun b hb => hb.kwB hW2 hc1 h1.cur ht (fun o ho => by unfold RelOffs at ho; omega)
  have core2 : L.mem s2 (scCoreA sc) = L.mem s (scCoreA sc) :=
    (hw2.mem_eq hcore.1 (qfoot_out hT1 hW2 hN1 hN1' ht hc1 h1.cur (hcore.ksb hw1.1))).trans core1
  step with obj.Sc.cpu.spec as ⟨cpu, cpu_post⟩
  rw [core2] at cpu_post
  subst cpu_post
  step with sched.set_reprogram_on.spec as ⟨s3, s3_post⟩
  subst s3_post
  have hN2 : NodePlaced st T s2 (L.mem s (scCoreA sc)) := (h.nodes _ hcs).ksb (hw2.1.trans hw1.1)
  have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
  exact (F1.trans F2).trans (footB_node hN2 hcs (by rw [rp]; omega) (by rw [rp]) (by rw [rp]; omega))

theorem sched.postpone.kw (s : S) (sc : obj.Sc) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (h : SchedQueuesInv st T Cs Ω H s Q R) (ht : L.mem s (scTcbA sc) ∈ T)
    (hr0 : (L.mem s (inqA (L.mem s (scTcbA sc))) &&& sched.Q_RELEASE) = 0#u64)
    (hcore : OutsideObjs st T Cs s (scCoreA sc)) (hcs : L.mem s (scCoreA sc) ∈ Cs) :
    sched.postpone st s sc ⦃ s' => Foot st T Cs Sg Scs Z Es s s' ⦄ :=
  WP.spec_mono (sched.postpone.kwB s sc Q R h ht hr0 hcore hcs) (fun _ f => f.foot)

/-- **The footprint of `resume`**: a `postpone` of the SC's thread when it
is not ready. -/
theorem schedcontext.resume.kwB {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (sc : obj.Sc) (Q : U64 → U64 → List U64) (R : U64 → List U64) (h : SchedQueuesInv st T Cs Ω H s Q R)
    (hsc : sc ≠ 0#u64 → L.mem s (scTcbA sc) ≠ 0#u64 →
      L.mem s (scTcbA sc) ∈ T ∧ OutsideObjs st T Cs s (scCoreA sc) ∧ L.mem s (scCoreA sc) ∈ Cs ∧
        L.actionW s ≠ L.mem s (scTcbA sc)) :
    schedcontext.resume st ar s a sc ⦃ s' _ => FootB st T Cs Sg Scs Z Es s s' ⦄ := by
  unfold schedcontext.resume
  step with obj.Sc.is_null.spec as ⟨b, b_post⟩
  split
  · simp only [WP.spec_ok, WP.uncurry'_pair]; exact FootB.refl _
  rename_i hb
  have hsc0 : sc ≠ 0#u64 := by simpa [b_post] using hb
  step with obj.Sc.tcb.spec as ⟨i, i_post⟩
  step with obj.Tcb.is_null.spec as ⟨b1, b1_post⟩
  split
  · simp only [WP.spec_ok, WP.uncurry'_pair]; exact FootB.refl _
  rename_i hb1
  have hi0 : L.mem s (scTcbA sc) ≠ 0#u64 := by rw [← i_post]; simpa [b1_post] using hb1
  obtain ⟨hiT, hcore, hcs, -⟩ := hsc hsc0 hi0
  step with sched.is_schedulable.spec' as ⟨b2, b2_post⟩
  split
  · rename_i hb2
    obtain ⟨-, -, hr0, -⟩ := b2_post hb2
    rw [i_post] at hr0
    have post := sched.postpone.kwB (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) s sc Q R h hiT hr0 hcore hcs
    step with sporadic.ready.spec as ⟨b3⟩
    split
    · step with sporadic.sufficient.ok (st := st) hA as ⟨b4⟩
      split
      · simp only [WP.spec_ok, WP.uncurry'_pair]; exact FootB.refl _
      · exact WP.spec_bind post fun s1 h1 => by simpa using h1
    · exact WP.spec_bind post fun s1 h1 => by simpa using h1
  · simp only [WP.spec_ok, WP.uncurry'_pair]; exact FootB.refl _

theorem schedcontext.resume.kw {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (sc : obj.Sc) (Q : U64 → U64 → List U64) (R : U64 → List U64) (h : SchedQueuesInv st T Cs Ω H s Q R)
    (hsc : sc ≠ 0#u64 → L.mem s (scTcbA sc) ≠ 0#u64 →
      L.mem s (scTcbA sc) ∈ T ∧ OutsideObjs st T Cs s (scCoreA sc) ∧ L.mem s (scCoreA sc) ∈ Cs ∧
        L.actionW s ≠ L.mem s (scTcbA sc)) :
    schedcontext.resume st ar s a sc ⦃ s' _ => Foot st T Cs Sg Scs Z Es s s' ⦄ :=
  WP.spec_mono (schedcontext.resume.kwB hA s a sc Q R h hsc) (fun r f => by obtain ⟨_, _⟩ := r; simp only [WP.uncurry'_pair] at f ⊢; exact f.foot)

/-- **The threads all sit on the core of the notification `n`'s SC** (when
`n` has one): a donation of that SC then moves no thread across cores, so the
debug lists stay as they are and the footprint is `Foot` (not `FootD`). -/
def DonCore (st : machine.Store S) [L : LawfulStore st] (T Scs : Set U64) (n : U64) (s : S) : Prop :=
  ∀ x ∈ Scs, x ≠ 0#u64 → L.mem s (ntfnScA n) = x → ∀ y ∈ T, L.mem s (affA y) = L.mem s (scCoreA x)

theorem DonCore.keep {n : U64} {s s' : S} (h : DonCore st T Scs n s)
    (hn : L.mem s' (ntfnScA n) = L.mem s (ntfnScA n)) (ha : ∀ y ∈ T, L.mem s' (affA y) = L.mem s (affA y))
    (hc : ∀ x ∈ Scs, L.mem s' (scCoreA x) = L.mem s (scCoreA x)) : DonCore st T Scs n s' :=
  fun x hx h0 e y hy => by rw [ha y hy, hc x hx]; exact h x hx h0 (hn.symm.trans e) y hy

theorem DonCore.keepT0 {n t : U64} {s s' : S} (hn : n ∈ Nt) (h : DonCore st T Scs n s)
    (k : KeepT0 st T Cs Rp Scs Nt t s s') : DonCore st T Scs n s' :=
  h.keep (k.nsc n hn)
    (fun y hy => by
      rw [affA_eq]; exact k.fld y hy _ (by simp) (by simp) (by simp) (by simp) (fun _ => ⟨by simp, by simp⟩))
    (fun x hx => (k.fix x hx).2.1)

/-- `maybe_donate_sched_context` with its footprint (`donate`, then
`resume`); `Foot` when the threads sit on the SC's core (`DonCore`). -/
theorem notification.maybe_donate_sched_context.tinvFK {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (s : S) (a : A) (t n : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (ht : t ∈ T)
    (htq : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64) (htr : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64)
    (hta' : L.actionW s ≠ t) (hti : L.idleW s ≠ t)
    (hns : L.mem s (ntfnScA n) ≠ 0#u64 → L.mem s (scTcbA (L.mem s (ntfnScA n))) = 0#u64 →
      L.mem s (scA t) = 0#u64 → L.mem s (ntfnScA n) ∈ Scs ∧ L.mem s (scCoreA (L.mem s (ntfnScA n))) ∈ Cs ∧
        (Sch st s t → L.mem s (ntfnScA n) ∈ Ac)) :
    notification.maybe_donate_sched_context st ar s a t n ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      TmFr st T Cs Nt s s' ∧ FootDB st T Cs Sg Scs Z Es s s' ∧
      (DonCore st T Scs n s → FootB st T Cs Sg Scs Z Es s s') ⦄ := by
  have ok0 : (ok (s, a) : Result (S × A)) ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      TmFr st T Cs Nt s s' ∧ FootDB st T Cs Sg Scs Z Es s s' ∧
      (DonCore st T Scs n s → FootB st T Cs Sg Scs Z Es s s') ⦄ :=
    (WP.spec_ok _).2 ⟨⟨⟨Q, R, h⟩, hB, hX, hS, hSg⟩, TmFr.refl (L := L) _, FootB.d (FootB.refl _), fun _ => FootB.refl _⟩
  unfold notification.maybe_donate_sched_context
  step with obj.Tcb.sc.spec as ⟨i, ei⟩
  split
  · rename_i hi
    step with obj.Ntfn.sc.val as ⟨i1, ei1⟩
    step with obj.Sc.is_null.spec as ⟨b, eb⟩
    split
    · exact ok0
    rename_i hb
    have hi10 : i1 ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    step with obj.Sc.tcb.spec as ⟨i2, ei2⟩
    split
    · rename_i hi2
      have htc0 : L.mem s (scTcbA i1) = 0#u64 := by rw [← ei2, hi2]
      obtain ⟨hS1, hcore1, hin1⟩ := hns (by rw [← ei1]; exact hi10) (by rw [← ei1]; exact htc0) (by rw [← ei, hi])
      rw [← ei1] at hS1 hin1 hcore1
      refine WP.spec_bind (WP.spec_and (schedcontext.donate.unbound hA s a i1 t Q R h hB hX hS hSg ht htq htr hS1
        hi10 htc0 hcore1 hin1 (by rw [← ei, hi]) hti)
        (schedcontext.donate.kwCB (Es := Es) hA s a i1 t ⟨⟨Q, R, h⟩, hB, hX, hS, hSg⟩ hS1 ht)) ?_
      rintro ⟨s4, a4⟩ ⟨⟨⟨⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4⟩, -, -, tm4, sc4, tc4, ea4⟩, f4, f4c⟩
      try simp only [WP.uncurry'_pair]
      have hsc : i1 ≠ 0#u64 → L.mem s4 (scTcbA i1) ≠ 0#u64 →
          L.mem s4 (scTcbA i1) ∈ T ∧ OutsideObjs st T Cs s4 (scCoreA i1) ∧ L.mem s4 (scCoreA i1) ∈ Cs ∧
            L.actionW s4 ≠ L.mem s4 (scTcbA i1) := fun _ _ => by
        obtain ⟨-, -, hc4⟩ := hX4.2.2.bound t ht (by rw [sc4]; exact hi10)
        rw [sc4] at hc4
        rw [tc4]
        exact ⟨ht, h4.omega _ ((objs_omega hX4.1 hSg4.sub).2 i1 hS1).2.1, hc4, by rw [ea4]; exact hta'⟩
      try simp only [uncurry_apply_pair]
      refine WP.spec_mono (WP.spec_and (schedcontext.resume.all hA s4 a4 i1 Q4 R4 h4 hB4 hX4 hSg4 hS4 hsc)
        (schedcontext.resume.kwB (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) hA s4 a4 i1 Q4 R4 h4 hsc)) ?_
      rintro ⟨s5, a5⟩ ⟨⟨Q5, R5, h5, hB5, hX5, hSg5, f5⟩, k5⟩
      exact ⟨⟨⟨Q5, R5, h5⟩, hB5, hX5, hS4.fr f5, hSg5⟩, tm4.trans (TmFr.of_fr f5 hX4.1 h4.nodes), f4.trans (FootB.d k5),
        fun hD => (f4c htc0 (hD i1 hS1 hi10 ei1.symm t ht)).trans k5⟩
    · exact ok0
  · exact ok0

theorem notification.maybe_donate_sched_context.tinvF {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (s : S) (a : A) (t n : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (ht : t ∈ T)
    (htq : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64) (htr : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64)
    (hta' : L.actionW s ≠ t) (hti : L.idleW s ≠ t)
    (hns : L.mem s (ntfnScA n) ≠ 0#u64 → L.mem s (scTcbA (L.mem s (ntfnScA n))) = 0#u64 →
      L.mem s (scA t) = 0#u64 → L.mem s (ntfnScA n) ∈ Scs ∧ L.mem s (scCoreA (L.mem s (ntfnScA n))) ∈ Cs ∧
        (Sch st s t → L.mem s (ntfnScA n) ∈ Ac)) :
    notification.maybe_donate_sched_context st ar s a t n ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      TmFr st T Cs Nt s s' ∧ FootD st T Cs Sg Scs Z Es s s' ∧
      (DonCore st T Scs n s → Foot st T Cs Sg Scs Z Es s s') ⦄ :=
  WP.spec_mono (notification.maybe_donate_sched_context.tinvFK (Es := Es) hA s a t n Q R h hB hX hS hSg ht htq htr hta' hti hns) fun r hr => by
    obtain ⟨s', a'⟩ := r
    simp only [WP.uncurry'_pair] at hr ⊢
    exact ⟨hr.1, hr.2.1, hr.2.2.1.footD, fun hD => (hr.2.2.2 hD).foot⟩

theorem signal_tail.FK {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s2 : S) (a1 : A) (dst n badge : U64)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h2 : SchedQueuesInv st T Cs Ω H s2 Q R) (hB2 : BoundInv st T Ac s2) (hX2 : XInv st T Cs Ω Sg Rp Scs Nt Z s2)
    (hS2 : SCsOK st T Ω Sg Scs Z Ac s2) (hSg2 : SgOK st Ω Sg s2) (hd : dst ∈ T) (hn : n ∈ Nt)
    (dq : (L.mem s2 (inqA dst) &&& sched.Q_QUEUED) = 0#u64) (dr : (L.mem s2 (inqA dst) &&& sched.Q_RELEASE) = 0#u64)
    (da : L.actionW s2 ≠ dst) (di : L.idleW s2 ≠ dst) (dR : ¬ BlockedR (L.mem s2 (stA dst))) :
    (do
      let s3 ← obj.Tcb.set_reg st dst s2 layout.reg.BADGE badge
      let (s4, a2) ← notification.maybe_donate_sched_context st ar s3 a1 dst n
      let b1 ← sched.is_schedulable st s4 dst
      let s5 ← if b1 then sched.possible_switch_to st s4 dst else ok s4
      let s6 ← notification.unblock_sporadic st s5 dst
      ok (s6, a2)) ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ TmFr st T Cs Nt s2 s' ∧
        FootDB st T Cs Sg Scs Z Es s2 s' ∧ (DonCore st T Scs n s2 → FootB st T Cs Sg Scs Z Es s2 s') ⦄ := by
  have hT := h2.tcbs
  have hta := hT dst hd
  have hfa : Aligned (core.num.U64.wrapping_add dst 256#u64) := field_aligned hta (by simp) (by simp)
  have sg3 : ∀ b ∈ Sg, L.mem (L.wr s2 (core.num.U64.wrapping_add dst 256#u64) badge) b = L.mem s2 b := fun b hb =>
    L.mem_wr_ne hfa (h2.omega _ (hSg2.sub _ hb)).1 (out_ne_field (h2.omega _ (hSg2.sub _ hb)) hd hta (by simp))
  have dc3 : DonCore st T Scs n s2 → DonCore st T Scs n (L.wr s2 (core.num.U64.wrapping_add dst 256#u64) badge) :=
    fun hD => hD.keep (sg3 _ (hX2.1.ntW n hn))
      (fun y hy => by
        rw [affA_eq]
        exact L.mem_wr_ne hfa (field_aligned (hT y hy) (by simp) (by simp))
          (fun e => field_ne (K1 := 256#u64) (K2 := 3520#u64) hta (hT y hy) (by simp) (by simp) (fun _ => by simp)
            (UScalar.eq_of_val_eq e)))
      (fun x hx => sg3 _ (hX2.1.fixW x hx).2)
  refine WP.spec_bind (obj.Tcb.set_reg.badge s2 dst badge hta) fun s3 e3 => ?_
  subst e3
  obtain ⟨h3, hB3, hX3, hS3, hSg3⟩ := badge_all (v := badge) h2 hB2 hX2 hS2 hSg2 hd
  have F3 : FootB st T Cs Sg Scs Z Es s2 (L.wr s2 (core.num.U64.wrapping_add dst 256#u64) badge) :=
    footB_field hT hd (by simp) (by simp) (by simp) (by simp)
  have tm3 : TmFr st T Cs Nt s2 (L.wr s2 (core.num.U64.wrapping_add dst 256#u64) badge) :=
    TmFr.wr hT h2.nodes hX2.1 (field_aligned hta (by simp) (by simp))
      (notTmW_field hT h2.nodes (fun n hn => h2.omega _ (hSg2.sub _ (hX2.1.ntB n hn).2)) hd (by simp) (by simp))
  have iq3 : L.mem (L.wr s2 (core.num.U64.wrapping_add dst 256#u64) badge) (inqA dst) = L.mem s2 (inqA dst) := by
    rw [inqA_eq]
    exact L.mem_wr_ne (field_aligned hta (by simp) (by simp)) (field_aligned hta (by simp) (by simp))
      (fun e => field_ne (K1 := 256#u64) (K2 := 3592#u64) hta hta (by simp) (by simp) (fun _ => by simp)
        (UScalar.eq_of_val_eq e))
  have ea3 : L.actionW (L.wr s2 (core.num.U64.wrapping_add dst 256#u64) badge) = L.actionW s2 :=
    act_wr_field (h2.nodes _ h2.cur) hd hta rfl (by simp) (by simp)
  have ei3 : L.idleW (L.wr s2 (core.num.U64.wrapping_add dst 256#u64) badge) = L.idleW s2 := by
    unfold LawfulStore.idleW; rw [LawfulStore.cpu_wr, nodeAt_wr]
    exact L.mem_wr_ne (field_aligned hta (by simp) (by simp))
      (nodeAt_aligned (h2.nodes _ h2.cur) (by rw [idle8]; omega) (by rw [idle8]))
      (fun e => node_ne_field (K := 256#u64) (h2.nodes _ h2.cur) (by rw [idle8]; omega) hd hta (by simp)
        (UScalar.eq_of_val_eq e).symm)
  have sc3 : L.mem (L.wr s2 (core.num.U64.wrapping_add dst 256#u64) badge) (scA dst) = L.mem s2 (scA dst) := by
    rw [scA_eq]
    exact L.mem_wr_ne (field_aligned hta (by simp) (by simp)) (field_aligned hta (by simp) (by simp))
      (fun e => field_ne (K1 := 256#u64) (K2 := 3464#u64) hta hta (by simp) (by simp) (fun _ => by simp)
        (UScalar.eq_of_val_eq e))
  have hsA3 : L.mem (L.wr s2 (core.num.U64.wrapping_add dst 256#u64) badge) (scA dst) = 0#u64 →
      ¬ Sch st (L.wr s2 (core.num.U64.wrapping_add dst 256#u64) badge) dst := fun h0 hS => by
    rw [sc3] at h0
    rcases Sch.wr_field h2 hd (by simp) (by simp) (by simp) hd hS with e | e | e | e | ⟨e1, e2⟩ | e
    · exact e dq
    · exact e dr
    · exact da e
    · exact di e
    · exact hB2.resume e1 (by rw [e2]; exact h0)
    · exact dR e
  refine WP.spec_bind (notification.maybe_donate_sched_context.tinvFK (Es := Es) hA _ a1 dst n Q R h3 hB3 hX3 hS3 hSg3 hd
    (by rw [iq3]; exact dq) (by rw [iq3]; exact dr) (by rw [ea3]; exact da) (by rw [ei3]; exact di)
    (ntfn_sc_ok hX3 hn hsA3)) ?_
  rintro ⟨s4, a2⟩ ⟨⟨⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4⟩, tm4, F4, F4c⟩
  try simp only [WP.uncurry'_pair]
  step with sched.is_schedulable.spec' as ⟨b1, hb1⟩
  refine WP.spec_bind (Pₘ := fun s5 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s5 ∧ TmFr st T Cs Nt s4 s5 ∧
      FootB st T Cs Sg Scs Z Es s4 s5) ?_ ?_
  · split
    · rename_i hb
      refine WP.spec_mono (WP.spec_and (sched.possible_switch_to.sch s4 dst Q4 R4 h4 hB4 hSg4 hd (hb1 hb).1
        (fun _ => (hS4.act _ (hX4.2.2.bound dst hd (hb1 hb).2.1).1).2 (hb1 hb).2.2.2))
        (sched.possible_switch_to.kwB (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) s4 dst h4 hd)) fun s5 hh => ?_
      obtain ⟨⟨p5, -, -⟩, k5⟩ := hh
      exact ⟨⟨p5.inv, p5.bnd, hX4.fr p5.fr, hS4.fr p5.fr, hSg4.fr p5.fr⟩, TmFr.of_fr p5.fr hX4.1 h4.nodes, k5⟩
    · exact (WP.spec_ok _).2 ⟨⟨⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4⟩, TmFr.refl (L := L) _, FootB.refl _⟩
  rintro s5 ⟨⟨⟨Q5, R5, h5⟩, hB5, hX5, hS5, hSg5⟩, tm5, F5⟩
  refine WP.spec_bind (WP.spec_and (WP.spec_and (endpoint.unblock_sporadic.all s5 dst h5 hB5 hX5 hS5 hSg5 hd)
    (endpoint.unblock_sporadic.tmfr s5 dst h5 hX5 hS5 hSg5 hd))
    (endpoint.unblock_sporadic.kwB (Es := Es) s5 dst h5 hX5 hS5 hd)) ?_
  rintro s6 ⟨⟨⟨h6, hB6, hX6, hS6, hSg6, -⟩, tm6⟩, F6⟩
  exact (WP.spec_ok _).2 ⟨⟨⟨Q5, R5, h6⟩, hB6, hX6, hS6, hSg6⟩, tm3.trans (tm4.trans (tm5.trans tm6)),
    (FootB.d F3).trans (F4.trans (FootB.d (F5.trans F6))), fun hD => F3.trans ((F4c (dc3 hD)).trans (F5.trans F6))⟩

theorem signal_tail.F {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s2 : S) (a1 : A) (dst n badge : U64)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h2 : SchedQueuesInv st T Cs Ω H s2 Q R) (hB2 : BoundInv st T Ac s2) (hX2 : XInv st T Cs Ω Sg Rp Scs Nt Z s2)
    (hS2 : SCsOK st T Ω Sg Scs Z Ac s2) (hSg2 : SgOK st Ω Sg s2) (hd : dst ∈ T) (hn : n ∈ Nt)
    (dq : (L.mem s2 (inqA dst) &&& sched.Q_QUEUED) = 0#u64) (dr : (L.mem s2 (inqA dst) &&& sched.Q_RELEASE) = 0#u64)
    (da : L.actionW s2 ≠ dst) (di : L.idleW s2 ≠ dst) (dR : ¬ BlockedR (L.mem s2 (stA dst))) :
    (do
      let s3 ← obj.Tcb.set_reg st dst s2 layout.reg.BADGE badge
      let (s4, a2) ← notification.maybe_donate_sched_context st ar s3 a1 dst n
      let b1 ← sched.is_schedulable st s4 dst
      let s5 ← if b1 then sched.possible_switch_to st s4 dst else ok s4
      let s6 ← notification.unblock_sporadic st s5 dst
      ok (s6, a2)) ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ TmFr st T Cs Nt s2 s' ∧
        FootD st T Cs Sg Scs Z Es s2 s' ∧ (DonCore st T Scs n s2 → Foot st T Cs Sg Scs Z Es s2 s') ⦄ :=
  WP.spec_mono (signal_tail.FK (Es := Es) hA s2 a1 dst n badge Q R h2 hB2 hX2 hS2 hSg2 hd hn dq dr da di dR) fun r hr => by
    obtain ⟨s', a'⟩ := r
    simp only [WP.uncurry'_pair] at hr ⊢
    exact ⟨hr.1, hr.2.1, hr.2.2.1.footD, fun hD => (hr.2.2.2 hD).foot⟩

/-! ## #63: the same-core `RunningVM` completion, with its footprint -/

/-- A TCB register write: the invariants, the state word, the footprint and
`DonCore`. -/
theorem reg_allFK {s : S} {t K v n : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T) (hn : n ∈ Nt)
    (hK : 256 ≤ K.val ∧ K.val < 3328) (hK8 : K.val % 8 = 0) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s (core.num.U64.wrapping_add t K) v) ∧
      L.mem (L.wr s (core.num.U64.wrapping_add t K) v) (stA t) = L.mem s (stA t) ∧
      FootB st T Cs Sg Scs Z Es s (L.wr s (core.num.U64.wrapping_add t K) v) ∧
      (DonCore st T Scs n s → DonCore st T Scs n (L.wr s (core.num.U64.wrapping_add t K) v)) := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hT := h0.tcbs
  have hta := hT t ht
  obtain ⟨hb, est⟩ := reg_all h0 hB hX hS hSg ht hK hK8 (v := v)
  have hfa : Aligned (core.num.U64.wrapping_add t K) := field_aligned hta (by omega) hK8
  have sg : ∀ b ∈ Sg, L.mem (L.wr s (core.num.U64.wrapping_add t K) v) b = L.mem s b := fun b hb =>
    L.mem_wr_ne hfa (h0.omega _ (hSg.sub _ hb)).1 (out_ne_field (h0.omega _ (hSg.sub _ hb)) ht hta (by omega))
  refine ⟨hb, est, footB_field hT ht (by omega) (by omega) hK8 (by refine ⟨?_, ?_, ?_⟩ <;> omega), fun hD => ?_⟩
  exact hD.keep (sg _ (hX.1.ntW n hn))
    (fun y hy => by
      rw [affA_eq]
      exact L.mem_wr_ne hfa (field_aligned (hT y hy) (by simp) (by simp))
        (fun e => field_ne (K1 := K) (K2 := 3520#u64) hta (hT y hy) (by omega) (by simp)
          (fun _ => by first | omega | (simp; omega) | simp) (UScalar.eq_of_val_eq e)))
    (fun x hx => sg _ (hX.1.fixW x hx).2)

theorem reg_allF {s : S} {t K v n : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T) (hn : n ∈ Nt)
    (hK : 256 ≤ K.val ∧ K.val < 3328) (hK8 : K.val % 8 = 0) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s (core.num.U64.wrapping_add t K) v) ∧
      L.mem (L.wr s (core.num.U64.wrapping_add t K) v) (stA t) = L.mem s (stA t) ∧
      Foot st T Cs Sg Scs Z Es s (L.wr s (core.num.U64.wrapping_add t K) v) ∧
      (DonCore st T Scs n s → DonCore st T Scs n (L.wr s (core.num.U64.wrapping_add t K) v)) :=
  let r := reg_allFK (Es := Es) h ht hn hK hK8 (v := v)
  ⟨r.1, r.2.1, r.2.2.1.foot, r.2.2.2⟩

theorem obj.Tcb.set_reg.blkFK (s : S) {t r v n : U64} (hr : r.val < 384) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (ht : t ∈ T) (hn : n ∈ Nt) :
    obj.Tcb.set_reg st t s r v ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ L.mem s' (stA t) = L.mem s (stA t) ∧
      FootB st T Cs Sg Scs Z Es s s' ∧ (DonCore st T Scs n s → DonCore st T Scs n s') ⦄ := by
  refine WP.spec_mono (obj.Tcb.set_reg.wrK s t r v (h.1.choose_spec.choose_spec.tcbs t ht) hr) ?_
  rintro s1 ⟨K, hK, rfl⟩
  exact reg_allFK h ht hn (by omega) (by omega)

theorem obj.Tcb.set_reg.blkF (s : S) {t r v n : U64} (hr : r.val < 384) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (ht : t ∈ T) (hn : n ∈ Nt) :
    obj.Tcb.set_reg st t s r v ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ L.mem s' (stA t) = L.mem s (stA t) ∧
      Foot st T Cs Sg Scs Z Es s s' ∧ (DonCore st T Scs n s → DonCore st T Scs n s') ⦄ :=
  WP.spec_mono (obj.Tcb.set_reg.blkFK (Es := Es) s hr h ht hn) fun _ hr => ⟨hr.1, hr.2.1, hr.2.2.1.foot, hr.2.2.2⟩

theorem msg.set_mr.blkFK (s : S) {t buf i v n : U64} (hi : i.val < 3) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (ht : t ∈ T) (hn : n ∈ Nt) :
    msg.set_mr st s t buf i v ⦃ r => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2 ∧ L.mem r.2 (stA t) = L.mem s (stA t) ∧
      FootB st T Cs Sg Scs Z Es s r.2 ∧ (DonCore st T Scs n s → DonCore st T Scs n r.2) ⦄ := by
  unfold msg.set_mr
  have hlt : i < msg.N_MSG_REGISTERS := by simp only [msg.N_MSG_REGISTERS]; scalar_tac
  rw [if_pos hlt]
  refine WP.spec_bind (Pₘ := fun r => r.val < 384) ?_ fun r hr => ?_
  · unfold msg.msg_register
    split
    · exact (WP.spec_ok _).2 (by simp [layout.reg.R10])
    split
    · exact (WP.spec_ok _).2 (by simp [layout.reg.R8])
    split
    · exact (WP.spec_ok _).2 (by simp [layout.reg.R9])
    · exact (WP.spec_ok _).2 (by simp [layout.reg.R15])
  refine WP.spec_bind (obj.Tcb.set_reg.blkFK (Es := Es) s hr h ht hn) fun s1 h1 => ?_
  simp only [lift, bind_ok]
  exact (WP.spec_ok _).2 h1

theorem msg.set_mr.blkF (s : S) {t buf i v n : U64} (hi : i.val < 3) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (ht : t ∈ T) (hn : n ∈ Nt) :
    msg.set_mr st s t buf i v ⦃ r => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2 ∧ L.mem r.2 (stA t) = L.mem s (stA t) ∧
      Foot st T Cs Sg Scs Z Es s r.2 ∧ (DonCore st T Scs n s → DonCore st T Scs n r.2) ⦄ :=
  WP.spec_mono (msg.set_mr.blkFK (Es := Es) s hi h ht hn) fun _ hr => ⟨hr.1, hr.2.1, hr.2.2.1.foot, hr.2.2.2⟩

set_option maxHeartbeats 4000000 in
/-- `vcpu.report.blk` with the footprint and `DonCore`. -/
theorem vcpu.report.blkF {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (t n badge : U64)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T) (hn : n ∈ Nt)
    (hvm : L.mem s (stA t) = sched.TS_RUNNING_VM)
    (hc : L.mem s (core.num.U64.wrapping_add t 3664#u64) ≠ 0#u64 →
      L.mem s (core.num.U64.wrapping_add (L.mem s (core.num.U64.wrapping_add t 3664#u64)) vcpu.PENDING) = 0#u64) :
    vcpu.report st ar s a t badge ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      L.mem s' (stA t) = sched.TS_RUNNING ∧ Foot st T Cs Sg Scs Z Es s s' ∧
      (DonCore st T Scs n s → DonCore st T Scs n s') ⦄ := by
  have hS0 : P0.StoreTotal st := L.total
  unfold vcpu.report vcpu.bound
  step as ⟨o, ho⟩
  simp only [lift, bind_ok]
  refine WP.spec_bind (LawfulStore.read_spec s _) fun v ev => ?_
  subst ho
  refine WP.spec_bind (Pₘ := fun p => p = false) ?_ fun pending hp => ?_
  · split
    · rename_i hv
      unfold vcpu.get
      simp only [lift, bind_ok]
      refine WP.spec_bind (LawfulStore.read_spec s _) fun i ei => ?_
      have hv0 : v ≠ 0#u64 := by simpa using hv
      have : i = 0#u64 := by rw [ei, ev]; exact hc (by rw [← ev]; exact hv0)
      exact (WP.spec_ok _).2 (by simp [this])
    · exact (WP.spec_ok _).2 rfl
  subst hp
  refine WP.spec_bind (Fl4Proofs.P0.msg.lookup_ipc_buffer.p0 st s true t hS0) fun b _ => ?_
  rw [if_neg Bool.false_ne_true]
  refine WP.spec_bind (hA.virtualization a) fun i _ => ?_
  refine WP.spec_bind (Pₘ := fun _ => True) ?_ ?_
  · repeat' (first
      | exact (WP.spec_ok _).2 trivial
      | exact Fl4Proofs.P0.vcpu.get.p0 _ _ _ _ hS0
      | exact Fl4Proofs.P0.vcpu.read_vmcs.p0 _ _ _ _ hS0
      | split
      | (step as ⟨_, _⟩)
      | refine WP.spec_bind (Fl4Proofs.P0.vcpu.get.p0 _ _ _ _ hS0) fun _ _ => ?_
      | refine WP.spec_bind (Fl4Proofs.P0.vcpu.read_vmcs.p0 _ _ _ _ hS0) fun _ _ => ?_)
  rintro ⟨ip, ctl, intr⟩ -
  try dsimp only
  refine WP.spec_bind (msg.set_mr.blkF (Es := Es) s (by simp) h ht hn) ?_
  rintro ⟨_, s1⟩ ⟨h1, e1, F1, D1⟩
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (msg.set_mr.blkF (Es := Es) s1 (by simp) h1 ht hn) ?_
  rintro ⟨_, s2⟩ ⟨h2, e2, F2, D2⟩
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (msg.set_mr.blkF (Es := Es) s2 (by simp) h2 ht hn) ?_
  rintro ⟨_, s3⟩ ⟨h3, e3, F3, D3⟩
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (obj.Tcb.set_reg.blkF (Es := Es) s3 (by simp [layout.reg.MSG_INFO, layout.reg.RSI]) h3 ht hn)
    fun s4 ⟨h4, e4, F4, D4⟩ => ?_
  refine WP.spec_bind (obj.Tcb.set_reg.blkF (Es := Es) s4 (by simp [layout.reg.BADGE, layout.reg.RDI]) h4 ht hn)
    fun s5 ⟨h5, e5, F5, D5⟩ => ?_
  obtain ⟨⟨Q5, R5, q5⟩, hB5, hX5, hS5, hSg5⟩ := h5
  have st5 : L.mem s5 (stA t) = sched.TS_RUNNING_VM := by rw [e5, e4, e3, e2, e1, hvm]
  refine WP.spec_mono (WP.spec_and (sts_all s5 t _ Q5 R5 q5 hB5 hX5 hS5 hSg5 ht not_blocked_running running_ne
    (Or.inr (by rw [st5]; exact not_blocked_vm))
    (hX5.noref (q5.tcbs t ht) (by rw [st5]; exact runnable_ne_reply (Or.inr (Or.inr rfl)))
      (by rw [st5]; exact runnable_ne_recv (Or.inr (Or.inr rfl))))
    ⟨fun _ _ _ _ _ => runnable_running, fun _ _ _ => runnable_running, fun _ => runnable_running⟩)
    (sched.set_thread_state.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) s5 t _ q5 ht)) ?_
  rintro s6 ⟨⟨q6, hB6, hX6, hS6, hSg6, st6, k6⟩, F6⟩
  exact ⟨⟨⟨Q5, R5, q6.congrX empty_congr⟩, hB6, hX6, hS6, hSg6⟩, st6,
    F1.trans (F2.trans (F3.trans (F4.trans (F5.trans F6)))),
    fun hD => (D5 (D4 (D3 (D2 (D1 hD))))).keepT0 hn k6.toKeepT0⟩

/-- `maybe_donate_sched_context.tinvF` on a thread that may be queued (as
`maybe_donate_sched_context.tinvB`). -/
theorem notification.maybe_donate_sched_context.tinvFBK {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (s : S) (a : A) (t n : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (ht : t ∈ T)
    (hns : L.mem s (ntfnScA n) ≠ 0#u64 → L.mem s (scTcbA (L.mem s (ntfnScA n))) = 0#u64 →
      L.mem s (scA t) = 0#u64 → L.mem s (ntfnScA n) ∈ Scs ∧ L.mem s (scCoreA (L.mem s (ntfnScA n))) ∈ Cs ∧
        (Sch st s t → L.mem s (ntfnScA n) ∈ Ac)) :
    notification.maybe_donate_sched_context st ar s a t n ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      TmFr st T Cs Nt s s' ∧ FootDB st T Cs Sg Scs Z Es s s' ∧
      (DonCore st T Scs n s → FootB st T Cs Sg Scs Z Es s s') ⦄ := by
  by_cases h0 : L.mem s (scA t) = 0#u64
  · refine notification.maybe_donate_sched_context.tinvFK hA s a t n Q R h hB hX hS hSg ht ?_ ?_ ?_ ?_ hns
    · by_contra hq; exact hB.q t ht hq h0
    · by_contra hq; exact hB.r t ht hq h0
    · intro e; exact hB.act (by rw [e]; exact ht) (by rw [e]; exact h0)
    · intro e; exact hB.idle (by rw [e]; exact h0)
  · unfold notification.maybe_donate_sched_context
    step with obj.Tcb.sc.spec as ⟨i, ei⟩
    rw [if_neg (by rw [ei]; exact h0)]
    exact (WP.spec_ok _).2 ⟨⟨⟨Q, R, h⟩, hB, hX, hS, hSg⟩, TmFr.refl (L := L) _, FootB.d (FootB.refl _),
      fun _ => FootB.refl _⟩

theorem notification.maybe_donate_sched_context.tinvFB {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (s : S) (a : A) (t n : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (ht : t ∈ T)
    (hns : L.mem s (ntfnScA n) ≠ 0#u64 → L.mem s (scTcbA (L.mem s (ntfnScA n))) = 0#u64 →
      L.mem s (scA t) = 0#u64 → L.mem s (ntfnScA n) ∈ Scs ∧ L.mem s (scCoreA (L.mem s (ntfnScA n))) ∈ Cs ∧
        (Sch st s t → L.mem s (ntfnScA n) ∈ Ac)) :
    notification.maybe_donate_sched_context st ar s a t n ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      TmFr st T Cs Nt s s' ∧ FootD st T Cs Sg Scs Z Es s s' ∧
      (DonCore st T Scs n s → Foot st T Cs Sg Scs Z Es s s') ⦄ :=
  WP.spec_mono (notification.maybe_donate_sched_context.tinvFBK (Es := Es) hA s a t n Q R h hB hX hS hSg ht hns) fun r hr => by
    obtain ⟨s', a'⟩ := r
    simp only [WP.uncurry'_pair] at hr ⊢
    exact ⟨hr.1, hr.2.1, hr.2.2.1.footD, fun hD => (hr.2.2.2 hD).foot⟩

/-- `signal_vm` with the footprint. -/
theorem signal_vmF {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s1 : S) (a : A) (i n : U64)
    (h1 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s1) (hiT : i ∈ T) (hn : n ∈ Nt)
    (st1 : L.mem s1 (stA i) = sched.TS_RUNNING) :
    (do
      let (s2, a1) ← notification.maybe_donate_sched_context st ar s1 a i n
      let b2 ← sched.is_schedulable st s2 i
      let s3 ← if b2 = true then sched.possible_switch_to st s2 i else ok s2
      let i4 ← obj.Tcb.sc st i s3
      let b3 ← obj.Sc.is_null i4
      if b3 = true then ok (s3, a1)
      else do
        let b4 ← sporadic.sc_active st s3 i4
        if b4 = true then do
          let i5 ← obj.Ntfn.sc st n s3
          if i4 = i5 then do
            let b5 ← sporadic.sc_sporadic st s3 i4
            if b5 = true then do
              let s4 ← sched.cur_sc st s3
              let b6 ← core.cmp.PartialEq.ne.trait_default obj.Sc.Insts.CoreCmpPartialEqSc i4 s4
              if b6 = true then do
                let s5 ← sporadic.unblock_check st s3 i4
                ok (s5, a1)
              else ok (s3, a1)
            else ok (s3, a1)
          else ok (s3, a1)
        else ok (s3, a1)) ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ FootD st T Cs Sg Scs Z Es s1 s' ∧
          (DonCore st T Scs n s1 → Foot st T Cs Sg Scs Z Es s1 s') ⦄ := by
  obtain ⟨⟨Q1, R1, q1⟩, hB1, hX1, hS1, hSg1⟩ := h1
  have hsA1 : L.mem s1 (scA i) = 0#u64 → ¬ Sch st s1 i := fun h0 hS => by
    rcases hS with e | e | e | e | ⟨e1, e2⟩ | e
    · exact hB1.q i hiT e h0
    · exact hB1.r i hiT e h0
    · exact hB1.act (by rw [e]; exact hiT) (by rw [e]; exact h0)
    · exact hB1.idle (by rw [e]; exact h0)
    · exact hB1.resume e1 (by rw [e2]; exact h0)
    · rw [st1] at e
      rcases e with e | e
      · exact not_blocked_running e
      · exact running_ne.1 e
  refine WP.spec_bind (notification.maybe_donate_sched_context.tinvFB (Es := Es) hA s1 a i n Q1 R1 q1 hB1 hX1 hS1
    hSg1 hiT (ntfn_sc_ok hX1 hn hsA1)) ?_
  rintro ⟨s2, a1⟩ ⟨⟨⟨Q2, R2, q2⟩, hB2, hX2, hS2, hSg2⟩, -, F2, F2c⟩
  try simp only [WP.uncurry'_pair]
  step with sched.is_schedulable.spec' as ⟨b2, hb2⟩
  refine WP.spec_bind (Pₘ := fun s3 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s3 ∧ Foot st T Cs Sg Scs Z Es s2 s3) ?_ ?_
  · split
    · rename_i hb
      refine WP.spec_mono (WP.spec_and (sched.possible_switch_to.sch s2 i Q2 R2 q2 hB2 hSg2 hiT (hb2 hb).1
        (fun _ => (hS2.act _ (hX2.2.2.bound i hiT (hb2 hb).2.1).1).2 (hb2 hb).2.2.2))
        (sched.possible_switch_to.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) s2 i q2 hiT)) fun s3 hh => ?_
      obtain ⟨⟨p3, -, -⟩, k3⟩ := hh
      exact ⟨⟨p3.inv, p3.bnd, hX2.fr p3.fr, hS2.fr p3.fr, hSg2.fr p3.fr⟩, k3⟩
    · exact (WP.spec_ok _).2 ⟨⟨⟨Q2, R2, q2⟩, hB2, hX2, hS2, hSg2⟩, Foot.refl _⟩
  rintro s3 ⟨⟨⟨Q3, R3, q3⟩, hB3, hX3, hS3, hSg3⟩, F3⟩
  have ok3 : (ok (s3, a1) : Result (S × A)) ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      FootD st T Cs Sg Scs Z Es s1 s' ∧ (DonCore st T Scs n s1 → Foot st T Cs Sg Scs Z Es s1 s') ⦄ :=
    (WP.spec_ok _).2 ⟨⟨⟨Q3, R3, q3⟩, hB3, hX3, hS3, hSg3⟩, F2.trans (Foot.d F3), fun hD => (F2c hD).trans F3⟩
  step with obj.Tcb.sc.spec as ⟨i4, ei4⟩
  step with obj.Sc.is_null.spec as ⟨b3, _hb3⟩
  refine sig_if _ _ _ _ (fun _ => ok3) (fun _ => ?_)
  refine WP.spec_bind (sporadic.sc_active.spec s3 i4) fun b4 _ => ?_
  refine sig_if _ _ _ _ (fun _ => ?_) (fun _ => ok3)
  refine WP.spec_bind (obj.Ntfn.sc.any s3 n) fun i5 _ => ?_
  refine sig_if _ _ _ _ (fun _ => ?_) (fun _ => ok3)
  step with sporadic.sc_sporadic.spec as ⟨b5, eb5⟩
  refine sig_if _ _ _ _ (fun hb5 => ?_) (fun _ => ok3)
  step with sched.cur_sc.spec as ⟨c4, _⟩
  step with sc_ne.spec as ⟨b6⟩
  refine sig_if _ _ _ _ (fun _ => ?_) (fun _ => ok3)
  have hi4S : i4 ∈ Scs := (hX3.2.2.bound i hiT (by rw [← ei4]; exact (eb5 hb5).1)).1 |> fun h => by
    rw [← ei4] at h; exact h
  have hiA : i4 ∈ Ac := hS3.spor i4 hi4S (eb5 hb5).2
  have hW : RefillsWF st s3 i4 (Z i4) := hS3.wf hi4S hiA
  have hSCin : SCin st s3 Ω i4 (Z i4) := ⟨hW, hX3.1.scW i4 hi4S⟩
  have hN' := q3.nodes _ q3.cur
  have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
  have aR : Aligned (L.nodeA s3 layout.node.REPROGRAM) := nodeAt_aligned hN' (by rw [rp]; omega) (by rw [rp])
  have oR : Outside (L.nodeA s3 layout.node.REPROGRAM) i4 (Z i4) :=
    hSCin.node_out q3.omega q3.cur hN' (by rw [rp]; omega) (by rw [rp])
  refine WP.spec_bind (WP.spec_and (sporadic.unblock_check.all s3 i i4 q3 hB3 hX3 hS3 hSg3 hiT ei4 (eb5 hb5).1 hiA)
    (sporadic.unblock_check.fr hW ⟨aR, oR⟩)) fun s5 ⟨hh, w5⟩ => ?_
  have F5 : Foot st T Cs Sg Scs Z Es s3 s5 := Foot.of w5 fun b hb => by
    rcases hb with hb | rfl
    · exact hb.kw hi4S
    · exact kw_node q3.cur (by rw [rp]; omega) (by rw [rp]; omega)
  obtain ⟨q5, hB5, hX5, hS5, hSg5, -⟩ := hh
  exact (WP.spec_ok _).2 ⟨⟨⟨Q3, R3, q5⟩, hB5, hX5, hS5, hSg5⟩, F2.trans (Foot.d (F3.trans F5)),
    fun hD => (F2c hD).trans (F3.trans F5)⟩

theorem notification.send_signal.tinvF {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (s : S) (a : A) (n badge : U64) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hn : n ∈ Nt)
    (hH : H n = some .ntfn) :
    notification.send_signal st ar s a n badge ⦃ s' _ => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      FootD st T Cs Sg Scs Z (EH H) s s' ∧ (DonCore st T Scs n s → Foot st T Cs Sg Scs Z (EH H) s s') ⦄ := by
  have hI := h
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hTm := hX.2.2.tm
  have hNb := hX.2.2.ntb
  have hT := h0.tcbs
  obtain ⟨E, EQ, hEW⟩ := h0.eps
  have he : n ∈ E := (hEW.2.2.2.2.2.2.2.1 n).2 (Or.inr hH)
  obtain ⟨hE, -, -⟩ := hEW.1 n he
  have hnE : n ∈ EH H := Or.inr hH
  have saF : notification.set_active st s n badge ⦃ s' => Foot st T Cs Sg Scs Z (EH H) s s' ⦄ := by
    unfold notification.set_active
    refine WP.spec_bind (obj.Ntfn.set_state.val s n _) fun s1 e1 => ?_
    subst e1
    refine WP.spec_mono (obj.Ntfn.set_badge.wr _ n badge) fun s2 e2 => ?_
    subst e2
    have hbm := hSg.sub _ (hX.1.ntB n hn).1
    exact (foot_wr (ep_aligned hE).2 (kw_ep hnE (Or.inr rfl))).trans
      (foot_wr ((h0.omega _ hbm).1) (kw_sg (hX.1.ntB n hn).1))
  have act : ∀ (s1 : S), notification.set_active st s n badge ⦃ s' => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ →
      (do let s1 ← notification.set_active st s n badge; ok (s1, a)) ⦃ s' _ => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
        Foot st T Cs Sg Scs Z (EH H) s s' ⦄ :=
    fun _ hsa => WP.spec_bind (WP.spec_and hsa saF) fun s1 h1 => (WP.spec_ok _).2 h1
  unfold notification.send_signal
  step with obj.Ntfn.state.spec as ⟨v, hv⟩
  refine sig_if _ _ _ _ (fun hidl => ?_) (fun hnidl => ?_)
  · -- an idle notification
    have hst0 : L.epState s n ≠ 1#u64 := by rw [← hv, hidl]; unfold obj.NTFN_IDLE; decide
    have sa := notification.set_active.tinv s n badge hI hn hH hst0
    step with obj.Ntfn.bound_tcb.val as ⟨i, ei⟩
    step with obj.Tcb.is_null.spec as ⟨b, eb⟩
    refine sig_if _ _ _ _ (fun hb => ?_) (fun hb => ?_)
    · rw [if_pos hb]
      refine WP.spec_bind (WP.spec_and sa saF) fun s1 ⟨h1, F1⟩ => ?_
      rw [if_pos hb]
      exact (WP.spec_ok _).2 ⟨h1, Foot.d F1, fun _ => F1⟩
    have hi0 : i ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    have hiT : i ∈ T := by
      rcases hNb n hn with e | e
      · rw [← ei] at e; exact absurd e hi0
      · rw [← ei] at e; exact e
    have hta := hT i hiT
    step with obj.Tcb.state.spec as ⟨i1, ei1⟩
    refine sig_if _ _ _ _ (fun hrecv => ?_) (fun hnrecv => ?_)
    · have hst : L.mem s (stA i) = sched.TS_BLOCKED_ON_RECV := by rw [← ei1, hrecv]
      have hbl : Blocked (L.mem s (stA i)) := by rw [hst]; exact Or.inr (Or.inl rfl)
      obtain ⟨dq, dr, da⟩ := blocked_out h0 hiT (not_runnable_of_blocked hbl)
      refine WP.spec_bind (WP.spec_and (ipc.cancel_ipc.all s a i Q R h0 hiT hB hX hSg.sub)
        (ipc.cancel_ipc.kw s a i h0 hiT hX.1 hSg.sub (fun hs => by
          obtain ⟨h1, h2⟩ := hX.2.1.reply i hiT hs
          exact ⟨h1, h2, hX.2.1.next _ h1, hX.2.1.prev _ h1⟩) (fun hs h0' => (hX.2.1.recv i hiT hs h0').1))) ?_
      rintro ⟨s1, a1⟩ ⟨⟨h1, hB1, hX1, nb1, nr1, -, k1, -⟩, F1⟩
      try simp only [WP.uncurry'_pair]
      have hS1 := hS.keepT hX k1
      have hSg1 : SgOK st Ω Sg s1 := ⟨hSg.sub, fun b hb => by rw [k1.ksb]; exact hSg.ks b hb,
        fun o h1' h2' => by rw [k1.ksb]; exact hSg.ksΩ o h1' h2'⟩
      have dq1 : (L.mem s1 (inqA i) &&& sched.Q_QUEUED) = 0#u64 := by rw [k1.inqf hiT]; exact dq
      have dr1 : (L.mem s1 (inqA i) &&& sched.Q_RELEASE) = 0#u64 := by rw [k1.inqf hiT]; exact dr
      have da1 : L.actionW s1 ≠ i := by
        rcases k1.act with e | e
        · rw [e]; exact da
        · rw [e]; exact fun e' => notT_small hT (by simp) (e' ▸ hiT)
      refine WP.spec_bind (WP.spec_and (sts_all s1 i _ Q R h1 hB1 hX1 hS1 hSg1 hiT not_blocked_running running_ne
        (Or.inr nb1) (hX1.noref hta nr1 (fun e => nb1 (by rw [e]; exact Or.inr (Or.inl rfl))))
        ⟨fun _ _ _ _ _ => runnable_running, fun _ _ _ => runnable_running, fun _ => runnable_running⟩)
        (sched.set_thread_state.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s1 i _ h1 hiT)) ?_
      rintro s2 ⟨⟨h2, hB2, hX2, hS2, hSg2, st2, k2⟩, F2⟩
      have h2' : SchedQueuesInv st T Cs Ω H s2 Q R := h2.congrX empty_congr
      have dq2 : (L.mem s2 (inqA i) &&& sched.Q_QUEUED) = 0#u64 := by rw [k2.inqf hiT]; exact dq1
      have dr2 : (L.mem s2 (inqA i) &&& sched.Q_RELEASE) = 0#u64 := by rw [k2.inqf hiT]; exact dr1
      have da2 : L.actionW s2 ≠ i := by
        rcases k2.act with e | e
        · rw [e]; exact da1
        · rw [e]; exact fun e' => notT_small hT (by simp) (e' ▸ hiT)
      refine WP.spec_mono (signal_tail.F (Es := EH H) hA s2 a1 i n badge Q R h2' hB2 hX2 hS2 hSg2 hiT hn dq2 dr2 da2
        (fun e => hB.idleNB (by rw [← k1.idleW, ← k2.idleW, e]; exact Or.inl hbl))
        (by rw [st2]; rintro (hb | hb); exact not_blocked_running hb; exact running_ne.1 hb)) ?_
      rintro ⟨s', a'⟩ ⟨hb', tm', F', F'c⟩
      exact ⟨hI.of_tmfr hb' ((TmFr.of_keepT k1).trans ((TmFr.of_keepT k2).trans tm')), (Foot.d (F1.trans F2)).trans F',
        fun hD => F1.trans (F2.trans (F'c ((hD.keepT0 hn k1.toKeepT0).keepT0 hn k2.toKeepT0)))⟩
    · -- not receiving: #63's same-core `RunningVM` completion, else active
      have OLD : (do
          let s1 ← notification.set_active st s n badge
          if b = true then ok (s1, a)
          else do
            let i2 ← obj.Tcb.state st i s1
            if i2 = sched.TS_RUNNING_VM then smp.remote_tcb_stall st ar s1 a i else ok (s1, a))
          ⦃ s' _ => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ FootD st T Cs Sg Scs Z (EH H) s s' ∧
            (DonCore st T Scs n s → Foot st T Cs Sg Scs Z (EH H) s s') ⦄ := by
        refine WP.spec_bind (WP.spec_and sa saF) fun s1 ⟨h1, F1⟩ => ?_
        rw [if_neg hb]
        step with obj.Tcb.state.spec
        split
        · exact WP.spec_mono (smp.remote_tcb_stall.blk hA s1 a i h1)
            fun r ⟨h2, F2, _⟩ => ⟨h2, Foot.d (F1.trans (F2.mono (Set.empty_subset _))),
              fun _ => F1.trans (F2.mono (Set.empty_subset _))⟩
        · exact (WP.spec_ok _).2 ⟨h1, Foot.d F1, fun _ => F1⟩
      rw [if_neg hb]
      refine sig_if _ _ _ _ (fun hvm => ?_) (fun _ => OLD)
      step with obj.Tcb.affinity.spec as ⟨i2, _hi2⟩
      step with LawfulStore.cur_cpu_spec as ⟨i3, _hi3⟩
      refine sig_if _ _ _ _ (fun _ => ?_) (fun _ => OLD)
      refine WP.spec_bind (vcpu.signal_completes.blk s i) fun b1 hb1 => ?_
      refine sig_if _ _ _ _ (fun hb1t => ?_) (fun _ => OLD)
      have hvmS : L.mem s (stA i) = sched.TS_RUNNING_VM := by rw [← ei1]; exact hvm
      refine WP.spec_bind (vcpu.report.blkF (Es := EH H) hA s a i n badge hI hiT hn hvmS (hb1 hb1t)) ?_
      rintro s1 ⟨h1, st1, F1, D1⟩
      refine WP.spec_mono (signal_vmF (Es := EH H) hA s1 a i n h1 hiT hn st1) ?_
      rintro ⟨s', a'⟩ ⟨hb', F', F'c⟩
      exact ⟨hb', (Foot.d F1).trans F', fun hD => F1.trans (F'c (D1 hD))⟩
  · split
    · -- a waiting notification
      rename_i hwait
      have hst1 : L.epState s n = 1#u64 := by rw [← hv, hwait]; unfold obj.NTFN_WAITING; rfl
      obtain ⟨hdT, hbe, hds⟩ := ntfn_head h0 hH hst1
      step with notification.get_queue.spec as ⟨q, eq⟩
      subst eq
      set hd := (L.epQ s n).head with hhd
      have hta := hT hd hdT
      have hbl : Blocked (L.mem s (stA hd)) := by rw [hds]; exact Or.inr (Or.inr rfl)
      obtain ⟨dq, dr, da⟩ := blocked_out h0 hdT (not_runnable_of_blocked hbl)
      have hdq := WP.spec_and (notification.ntfn_dequeue.inv s hd Q R h0 hdT (by simp) hbl)
        (dequeue_blocked_kw (Sg := Sg) (Scs := Scs) (Z := Z) s hd h0 hdT (by simp) hbl (notification.ntfn_dequeue st)
          fun xs hE' hq hm => notification.ntfn_dequeue.foot s _ hd xs hT hE' hq hm)
      rw [hbe] at hdq
      refine WP.spec_bind hdq ?_
      rintro s1 ⟨⟨h1, f1, o1, n1, k1, c1, nc1⟩, F1⟩
      have tm1 : TmFr st T Cs Nt s s1 := TmFr.mk0 ⟨k1, fun y hy K a b c => f1 y hy K (by omega) c (by omega) (by omega),
        fun c hc o ho => nc1 c hc o (by omega) (by omega), fun n' hn' => o1 _ (hSg.sub _ (hX.1.ntB n' hn').2)⟩
      obtain ⟨hB1, hX1, hS1, hSg1, ea1, ec1, ei1⟩ := frame_bx h0 hB hX hS hSg f1 o1 n1 k1 tm1
      have st1 : L.mem s1 (stA hd) = sched.TS_BLOCKED_ON_NTFN := by
        rw [stA_eq, f1 hd hdT _ (by simp) (by simp) (by simp) (by simp), ← stA_eq]; exact hds
      have iq1 : L.mem s1 (inqA hd) = L.mem s (inqA hd) := by
        rw [inqA_eq]; exact f1 hd hdT _ (by simp) (by simp) (by simp) (by simp)
      obtain ⟨-, -, r3, -, r6⟩ := ts_vals
      refine WP.spec_bind (WP.spec_and (sts_all s1 hd _ Q R h1 hB1 hX1 hS1 hSg1 hdT not_blocked_running running_ne
        (Or.inl (Or.inr rfl)) (hX1.noref hta (by rw [st1]; exact blocked_ne_reply (Or.inr (Or.inr rfl)))
          (by rw [st1, r3, r6]; decide))
        ⟨fun _ _ _ _ _ => runnable_running, fun _ _ _ => runnable_running, fun _ => runnable_running⟩)
        (sched.set_thread_state.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s1 hd _ h1 hdT)) ?_
      rintro s2 ⟨⟨h2, hB2, hX2, hS2, hSg2, st2, k2⟩, F2⟩
      have h2' : SchedQueuesInv st T Cs Ω H s2 Q R := h2.congrX empty_congr'
      have dq2 : (L.mem s2 (inqA hd) &&& sched.Q_QUEUED) = 0#u64 := by rw [k2.inqf hdT, iq1]; exact dq
      have dr2 : (L.mem s2 (inqA hd) &&& sched.Q_RELEASE) = 0#u64 := by rw [k2.inqf hdT, iq1]; exact dr
      have da2 : L.actionW s2 ≠ hd := by
        rcases k2.act with e | e
        · rw [e, ea1]; exact da
        · rw [e]; exact fun e' => notT_small hT (by simp) (e' ▸ hdT)
      refine WP.spec_mono (signal_tail.F (Es := EH H) hA s2 a hd n badge Q R h2' hB2 hX2 hS2 hSg2 hdT hn dq2 dr2 da2
        (fun e => hB.idleNB (by rw [← ei1, ← k2.idleW, e]; exact Or.inl hbl))
        (by rw [st2]; rintro (hb | hb); exact not_blocked_running hb; exact running_ne.1 hb)) ?_
      rintro ⟨s', a'⟩ ⟨hb', tm', F', F'c⟩
      have dc1 : DonCore st T Scs n s → DonCore st T Scs n s1 := fun hD =>
        hD.keep (o1 _ (hSg.sub _ (hX.1.ntW n hn)))
          (fun y hy => by rw [affA_eq]; exact f1 y hy _ (by simp) (by simp) (by simp) (by simp))
          (fun x hx => o1 _ (hSg.sub _ (hX.1.fixW x hx).2))
      exact ⟨hI.of_tmfr hb' (tm1.trans ((TmFr.of_keepT k2).trans tm')), (Foot.d (F1.trans F2)).trans F',
        fun hD => F1.trans (F2.trans (F'c ((dc1 hD).keepT0 hn k2.toKeepT0)))⟩
    · -- an active notification
      step with obj.Ntfn.badge.val as ⟨i, ei⟩
      simp only [lift, Aeneas.Std.bind_ok]
      refine WP.spec_bind (obj.Ntfn.set_badge.wr s n _) fun s1 e1 => ?_
      subst e1
      obtain ⟨b1, tm1⟩ := ntfn_badge_all (v := i ||| badge)
        (⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) hn
      exact (WP.spec_ok _).2 ⟨hI.of_tmfr b1 tm1, Foot.d (foot_wr ((h0.omega _ (hSg.sub _ (hX.1.ntB n hn).1)).1)
        (kw_sg (hX.1.ntB n hn).1)), fun _ => foot_wr ((h0.omega _ (hSg.sub _ (hX.1.ntB n hn).1)).1)
        (kw_sg (hX.1.ntB n hn).1)⟩



theorem timer.fire_loop.tinvF {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A) (now i : U64) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    timer.fire_loop st ar s a now i ⦃ s' _ => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      FootD st T Cs Sg Scs Z (EH H) s s' ⦄ := by
  unfold timer.fire_loop
  apply loop.spec_decr_nat (measure := fun x => 32 - x.2.2.val)
    (inv := fun x => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac x.1 ∧ FootD st T Cs Sg Scs Z (EH H) s x.1)
  · rintro ⟨s1, a1, i1⟩ ⟨h1, F1⟩
    simp only at h1 F1
    unfold timer.fire_loop.body
    dsimp only
    split
    · rename_i hi
      have hi32 : i1.val < 32 := by simpa using hi
      step with LawfulStore.cur_cpu_spec as ⟨c, ec⟩
      step with obj.node_get.spec as ⟨t, et⟩
      step with obj.Tcb.is_null.spec as ⟨b, eb⟩
      split
      · exact (WP.spec_ok _).2 ⟨h1, F1⟩
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
      · exact (WP.spec_ok _).2 ⟨hI1, F1⟩
      step with obj.Tcb.timer_badge.val as ⟨bd, ebd⟩
      refine WP.spec_bind (timer.remove.tf (s0 := s1) s1 t (TF.start hI1) htT) ?_
      rintro s2 ⟨h2, f2, -⟩
      have F2 : FootD st T Cs Sg Scs Z (EH H) s s2 := F1.trans (Foot.d (f2.mono (Set.empty_subset _)))
      step with obj.Tcb.bound_ntfn.val as ⟨n, en⟩
      refine WP.spec_bind (Pₘ := fun r : S × A => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧
          FootD st T Cs Sg Scs Z (EH H) s r.1) ?_ ?_
      · split
        · rename_i hn0
          have hn0' : L.mem s2 (boundA t) ≠ 0#u64 := by rw [← en]; exact bne_ne hn0
          have hn : n ∈ Nt := by rw [en]; exact h2.2.2.1.2.2.bnd t htT hn0'
          exact WP.spec_mono (notification.send_signal.tinvF hA s2 a1 n bd h2 hn (hNt n hn)) fun r hr => by
            obtain ⟨s', a'⟩ := r; simp only [WP.uncurry'_pair] at hr; exact ⟨hr.1, F2.trans hr.2.1⟩
        · exact (WP.spec_ok _).2 ⟨h2, F2⟩
      rintro ⟨s3, a3⟩ ⟨h3, F3⟩
      simp only at h3 F3
      try simp only [WP.uncurry'_pair]
      step with LawfulStore.cur_cpu_spec as ⟨c3, ec3⟩
      step with obj.node_set.spec as ⟨s4, es4⟩
      step as ⟨i4, ei4⟩
      try simp only [WP.spec_ok]
      subst es4 ec3
      have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
      have hc3 := h3.1.choose_spec.choose_spec.cur
      exact ⟨reprogram.tinv h3, F3.trans (Foot.d (foot_node (h3.1.choose_spec.choose_spec.nodes _ hc3) hc3
        (by rw [rp]; omega) (by rw [rp]) (by rw [rp]; omega))), by omega⟩
    · exact (WP.spec_ok _).2 ⟨h1, F1⟩
  · exact ⟨h, Foot.d (Foot.refl _)⟩

/-- seL4 MCS `fireTimers` (l4h): `timer::fire` keeps `TInv`. -/
theorem timer.fire.tinvF {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    timer.fire st ar s a ⦃ s' _ => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ FootD st T Cs Sg Scs Z (EH H) s s' ⦄ := by
  unfold timer.fire
  refine WP.spec_bind (L.cur_cpu_spec s) fun c _ => ?_
  refine WP.spec_bind (obj.node_get.spec s c _) fun now _ => ?_
  exact timer.fire_loop.tinvF hA hNt s a now 0#u64 h


/-! ## `schedule`'s word set -/

/-- The words `schedule` (and `timer::fire` under it) writes: `KW` with the
heap's endpoints and notifications, and the kernel-global area (the domain
schedule words `next_domain` writes). The timers' signals before it may also
write the debug lists (`FootD`: `migrate_tcb` when a signal donates an SC of
another core); `sched.schedule.sfoot` splits the two. -/
def SchedW (st : machine.Store S) [L : LawfulStore st] (T Cs Sg Scs : Set U64) (Z : U64 → Nat) (H : Heap)
    (s0 : S) (b : U64) : Prop :=
  KW st T Cs Sg Scs Z (EH H) s0 b ∨ ∃ o : U64, o.val < 13568 ∧ b = core.num.U64.wrapping_add (L.ksb s0) o

/-- A footprint inside `SchedW`. -/
abbrev SFoot (st : machine.Store S) [L : LawfulStore st] (T Cs Sg Scs : Set U64) (Z : U64 → Nat) (H : Heap)
    (s s' : S) : Prop :=
  WritesIn st s s' (SchedW st T Cs Sg Scs Z H s)

theorem SchedW.ksb {s0 s1 : S} {b : U64} (hk : L.ksb s1 = L.ksb s0) (h : SchedW st T Cs Sg Scs Z H s1 b) :
    SchedW st T Cs Sg Scs Z H s0 b := by
  rcases h with h | ⟨o, ho, e⟩
  · exact Or.inl (KW.ksb hk h)
  · exact Or.inr ⟨o, ho, by rw [e, hk]⟩

theorem SFoot.refl (s : S) : SFoot st T Cs Sg Scs Z H s s := WritesIn.refl _ _

theorem SFoot.trans {s₁ s₂ s₃ : S} (h₁ : SFoot st T Cs Sg Scs Z H s₁ s₂) (h₂ : SFoot st T Cs Sg Scs Z H s₂ s₃) :
    SFoot st T Cs Sg Scs Z H s₁ s₃ :=
  WritesIn.mono (WritesIn.trans h₁ h₂) fun b hb => Or.elim hb id fun hb => SchedW.ksb h₁.1 hb

theorem Foot.sfoot {s s' : S} (h : Foot st T Cs Sg Scs Z (EH H) s s') : SFoot st T Cs Sg Scs Z H s s' :=
  WritesIn.mono h fun _ hb => Or.inl hb

theorem SFoot.foot {s₁ s₂ s₃ : S} (h₁ : SFoot st T Cs Sg Scs Z H s₁ s₂)
    (h₂ : Foot st T Cs Sg Scs Z (EH H) s₂ s₃) : SFoot st T Cs Sg Scs Z H s₁ s₃ := h₁.trans h₂.sfoot

theorem sched.append.kw {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} (s : S) (t : obj.Tcb)
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) :
    sched.append st s t ⦃ s' => Foot st T Cs Sg Scs Z Es s s' ⦄ := by
  have hc := h.aff t ht
  have hp := h.prio t ht
  have hR1 := h.ready _ hc
  refine WP.spec_mono (sched.append.foot s t _ h.tcbs ht hp (h.nodes _ hc) (h.nodes _ h.cur) (hR1.1.rel _ hp)
    (fun h0 => h.notQ ht h0 hc hp)) fun s' hh => Foot.of hh.1 fun b hb => hb.kw ?_ hc h.cur ht (fun o ho => by omega)
  intro w hw
  rcases List.mem_cons.1 hw with rfl | hw
  · exact ht
  · exact (hR1.1.rel _ hp).mem w hw

theorem sched.set_cur_thread.kw (s : S) (t : obj.Tcb) (hN : NodePlaced st T s (L.cpu s)) (hc : L.cpu s ∈ Cs) :
    sched.set_cur_thread st s t ⦃ s' => Foot st T Cs Sg Scs Z Es s s' ⦄ :=
  WP.spec_mono (sched.set_cur_thread.spec s t) fun s' e => by
    subst e; exact foot_node hN hc (by rw [curth0]; omega) (by rw [curth0]) (by rw [curth0]; omega)

theorem sched.switch_to_thread.kw {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (t : obj.Tcb) {Q : U64 → U64 → List U64} {R : U64 → List U64} (h : SchedQueuesInv st T Cs Ω H s Q R)
    (ht : t ∈ T) : sched.switch_to_thread st ar s a t ⦃ s' _ => Foot st T Cs Sg Scs Z Es s s' ⦄ := by
  unfold sched.switch_to_thread
  refine WP.spec_bind (set_vm_root_same hA s a t) ?_
  rintro ⟨s1, a1⟩ e
  simp only [WP.uncurry'_pair] at e
  subst e
  refine WP.spec_bind (sched.dequeue.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) s1 t h ht) ?_
  intro s2 f2
  refine WP.spec_bind (sched.set_cur_thread.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) s2 t
    (f2.curN (h.nodes _ h.cur)) (by rw [f2.2.1]; exact h.cur)) ?_
  intro s3 f3
  simp only [WP.spec_ok, WP.uncurry'_pair]
  exact f2.trans f3

theorem sched.choose_thread.kw {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    {Q : U64 → U64 → List U64} {R : U64 → List U64} (h : SchedQueuesInv st T Cs Ω H s Q R) :
    sched.choose_thread st ar s a ⦃ s' _ => Foot st T Cs Sg Scs Z Es s s' ⦄ := by
  unfold sched.choose_thread
  simp only [layout.NUM_DOMAINS, fl4_abi.config.NUM_DOMAINS]
  rw [ite_cond_eq_false _ _ (by simp)]
  simp only [bind_ok]
  step with LawfulStore.cur_cpu_spec as ⟨cpu, cpu_post⟩
  subst cpu_post
  unfold sched.bitmap_dom
  simp only [layout.NUM_DOMAINS, fl4_abi.config.NUM_DOMAINS]
  rw [ite_cond_eq_false _ _ (by simp)]
  simp only [bind_ok]
  step with l1_off_zero as ⟨i1, i1_post⟩
  subst i1_post
  step with obj.node_get.spec as ⟨i2, i2_post⟩
  split
  · have hne : L.l1W s (L.cpu s) ≠ 0#u64 := by
      rw [show L.l1W s (L.cpu s) = i2 from i2_post.symm]; simpa using ‹(i2 != 0#u64) = true›
    refine WP.spec_bind (sched.highest_prio.spec s 0#u64 _ (h.nodes _ h.cur) (h.ready _ h.cur).2 hne) ?_
    rintro p ⟨hp, hpne, -⟩
    step with sched.rq_head_off.spec as ⟨off, off_post, off_post1⟩
    step with sched.q_get.spec as ⟨q, q_post⟩
    have hq : q = L.rqQ s (L.cpu s) p := by rw [q_post, off_post1, off_post]; rfl
    have hrel := (h.ready _ h.cur).1.rel p hp
    have hmem : q.head ∈ Q (L.cpu s) p := by rw [hq, hrel.head]; exact headD_mem hpne _
    have htT : q.head ∈ T := hrel.mem _ hmem
    exact sched.switch_to_thread.kw hA s a q.head h htT
  · unfold sched.switch_to_idle_thread
    step with sched.idle_thread.spec' as ⟨idle, idle_post⟩
    refine WP.spec_bind (set_kernel_vm_root_same (st := st) hA s a) ?_
    rintro ⟨s1, a1⟩ e
    simp only [WP.uncurry'_pair] at e
    subst s1
    refine WP.spec_bind (sched.set_cur_thread.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) s idle
      (h.nodes _ h.cur) h.cur) ?_
    intro s2 f2
    simp only [WP.spec_ok, WP.uncurry'_pair]
    exact f2

/-- One write to the kernel-global area. -/
theorem sfoot_ks {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) {o v : U64} (ho : o.val < 13568) (h8 : o.val % 8 = 0) :
    SFoot st T Cs Sg Scs Z H s (L.wr s (core.num.U64.wrapping_add (L.ksb s) o) v) :=
  (writesIn_wr (ks_aligned h ho h8)).mono fun b hb => Or.inr ⟨o, ho, hb⟩

theorem sched.next_domain.sfoot (s : S) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hS : SgOK st Ω Sg s) :
    sched.next_domain st s ⦃ s' => SFoot st T Cs Sg Scs Z H s s' ⦄ := by
  unfold sched.next_domain
  step with obj.ks_get.spec as ⟨i, _⟩
  step as ⟨idx, _⟩
  have hST : P0.StoreTotal st := L.total
  refine WP.spec_bind (Pₘ := fun _ => True) (by split <;> step*) fun idx1 _ => ?_
  refine WP.spec_bind (WP.spec_and (ks_set.sch s Q R h hB hS (o := layout.ks.DOM_SCHED_IDX) (v := idx1)
    (by simp [layout.ks.DOM_SCHED_IDX]) (by simp [layout.ks.DOM_SCHED_IDX])) (obj.ks_set.spec s _ idx1)) ?_
  rintro s1 ⟨⟨⟨h1, hB1, f1⟩, -, -⟩, e1⟩
  have F1 : SFoot st T Cs Sg Scs Z H s s1 := by
    rw [e1]; exact sfoot_ks h (by simp [layout.ks.DOM_SCHED_IDX]) (by simp [layout.ks.DOM_SCHED_IDX])
  refine WP.spec_bind (WP.spec_and (sched.set_reprogram.sch s1 Q R h1 hB1 (hS.fr f1))
    (sched.set_reprogram.spec s1)) ?_
  rintro s2 ⟨⟨⟨h2, hB2, f2⟩, -, -⟩, e2⟩
  have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
  have F2 : SFoot st T Cs Sg Scs Z H s1 s2 := by
    rw [e2]
    exact (foot_node (Es := EH H) (h1.nodes _ h1.cur) h1.cur (by rw [rp]; omega) (by rw [rp]) (by rw [rp]; omega)).sfoot
  refine WP.spec_bind (WP.spec_and (ks_set.sch s2 Q R h2 hB2 ((hS.fr f1).fr f2) (o := layout.ks.WORK_UNITS) (v := 0#u64)
    (by simp [layout.ks.WORK_UNITS]) (by simp [layout.ks.WORK_UNITS])) (obj.ks_set.spec s2 _ 0#u64)) ?_
  rintro s3 ⟨⟨⟨h3, hB3, f3⟩, -, -⟩, e3⟩
  have F3 : SFoot st T Cs Sg Scs Z H s2 s3 := by
    rw [e3]; exact sfoot_ks h2 (by simp [layout.ks.WORK_UNITS]) (by simp [layout.ks.WORK_UNITS])
  have hS3 := ((hS.fr f1).fr f2).fr f3
  step with sched.dom_sched_domain.spec as ⟨d⟩
  step with sched.dom_sched_duration.spec as ⟨t⟩
  refine WP.spec_bind (WP.spec_and (ks_set.sch s3 Q R h3 hB3 hS3 (o := layout.ks.CUR_DOMAIN) (v := d)
    (by simp [layout.ks.CUR_DOMAIN]) (by simp [layout.ks.CUR_DOMAIN])) (obj.ks_set.spec s3 _ d)) ?_
  rintro s4 ⟨⟨⟨h4, -, -⟩, -, -⟩, e4⟩
  have F4 : SFoot st T Cs Sg Scs Z H s3 s4 := by
    rw [e4]; exact sfoot_ks h3 (by simp [layout.ks.CUR_DOMAIN]) (by simp [layout.ks.CUR_DOMAIN])
  refine WP.spec_mono (obj.ks_set.spec s4 _ t) ?_
  intro s5 e5
  have F5 : SFoot st T Cs Sg Scs Z H s4 s5 := by
    rw [e5]; exact sfoot_ks h4 (by simp [layout.ks.DOMAIN_TIME]) (by simp [layout.ks.DOMAIN_TIME])
  exact F1.trans (F2.trans (F3.trans (F4.trans F5)))

theorem sched.schedule_choose_new_thread.sfoot {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (s : S) (a : A) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hS : SgOK st Ω Sg s) :
    sched.schedule_choose_new_thread st ar s a ⦃ s' _ => SFoot st T Cs Sg Scs Z H s s' ⦄ := by
  unfold sched.schedule_choose_new_thread
  step with sched.domain_time.spec as ⟨i⟩
  refine WP.spec_bind (Pₘ := fun s1 => (∃ Q R, SchedQueuesInv st T Cs Ω H s1 Q R) ∧
      SFoot st T Cs Sg Scs Z H s s1) ?_ ?_
  · split
    · exact WP.spec_mono (WP.spec_and (sched.next_domain.sch s Q R h hB hS)
        (sched.next_domain.sfoot (Scs := Scs) (Z := Z) s Q R h hB hS)) fun s1 hh => ⟨hh.1.1.inv, hh.2⟩
    · exact (WP.spec_ok _).2 ⟨⟨Q, R, h⟩, SFoot.refl _⟩
  rintro s1 ⟨⟨Q1, R1, h1⟩, f1⟩
  exact WP.spec_mono (sched.choose_thread.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) hA s1 a h1)
    fun r hr => by obtain ⟨s', a'⟩ := r; exact f1.foot (by simpa using hr)

theorem cand_choose.sfoot {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (act : obj.Tcb)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hS : SCsOK st T Ω Sg Scs Z Ac s)
    (hact : L.actionW s = act) (hT : act ∈ T) (app : Bool) :
    (do
      let s5 ← if app then sched.append st s act else sched.enqueue st s act
      let s6 ← sched.set_action st s5 sched.ACTION_CHOOSE_NEW
      sched.schedule_choose_new_thread st ar s6 a) ⦃ s' _ => SFoot st T Cs Sg Scs Z H s s' ⦄ := by
  have hok := h.actOK (hact ▸ hT)
  rw [hact] at hok
  have hr : (L.mem s (inqA act) &&& sched.Q_RELEASE) = 0#u64 := by
    by_contra hc
    exact hok.2 _ (h.aff act hT) ((h.released act hT).1 hc)
  have hbd : L.mem s (scA act) ≠ 0#u64 := by have := hB.act (hact ▸ hT); rw [hact] at this; exact this
  refine WP.spec_bind (Pₘ := fun s5 => Post st T Cs Ω H Sg Ac s s5 ∧ Foot st T Cs Sg Scs Z (EH H) s s5) ?_ ?_
  · split
    · exact WP.spec_mono (WP.spec_and (sched.append.sch s act Q R h hB hS.sg hT (fun _ => hr) (fun _ => hok.1)
        (fun _ => hbd) (fun _ => by have := hB.actA (hact ▸ hT); rwa [hact] at this))
        (sched.append.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s act h hT)) fun s5 h5 => ⟨h5.1.1, h5.2⟩
    · exact WP.spec_mono (WP.spec_and (sched.enqueue.sch s act Q R h hB hS.sg hT (fun _ => hr) (fun _ => hok.1)
        (fun _ => hbd) (fun _ => by have := hB.actA (hact ▸ hT); rwa [hact] at this))
        (sched.enqueue.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s act h hT)) fun s5 h5 => ⟨h5.1.1, h5.2⟩
  rintro s5 ⟨⟨⟨Q5, R5, h5⟩, hB5, f5⟩, F5⟩
  rw [choose_val]
  refine WP.spec_bind (WP.spec_and (sched.set_action.sch s5 1#u64 Q5 R5 h5 hB5 (hS.fr f5).sg (Or.inr (Or.inl rfl))
    (fun hT => absurd hT (one_notT h)) (fun hT => absurd hT (one_notT h)) (fun e => by simp at e)
    (fun hT => absurd hT (one_notT h)))
    (sched.set_action.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s5 1#u64 (h5.nodes _ h5.cur) h5.cur)) ?_
  rintro s6 ⟨⟨⟨⟨Q6, R6, h6⟩, hB6, f6⟩, -, -, -⟩, F6⟩
  exact WP.spec_mono (sched.schedule_choose_new_thread.sfoot (Scs := Scs) (Z := Z) hA s6 a Q6 R6 h6 hB6
    ((hS.fr f5).fr f6).sg) fun r hr => by
      obtain ⟨s', a'⟩ := r; exact (F5.sfoot.foot F6).trans (by simpa using hr)

theorem sched.awaken_loop.kw (s : S) (fuel : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hS : SgOK st Ω Sg s) :
    sched.awaken_loop st s fuel ⦃ s' => Foot st T Cs Sg Scs Z Es s s' ⦄ := by
  unfold sched.awaken_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.val)
    (inv := fun x => Post st T Cs Ω H Sg Ac s x.1 ∧ Foot st T Cs Sg Scs Z Es s x.1)
  · rintro ⟨s1, fu⟩ ⟨⟨⟨Q1, R1, h1⟩, hB1, f1⟩, F1⟩
    have hS1 := hS.fr f1
    unfold sched.awaken_loop.body
    dsimp only
    split
    swap
    · simp only [WP.spec_ok]; exact F1
    step as ⟨fuel1, efuel⟩
    step with LawfulStore.cur_cpu_spec as ⟨i, ei⟩
    step with obj.node_get.spec as ⟨i1, ei1⟩
    step with obj.Tcb.is_null.spec as ⟨b, b_post⟩
    split
    · simp only [WP.spec_ok]; exact F1
    step with obj.Tcb.sc.spec as ⟨i2, _⟩
    step with sporadic.ready.spec as ⟨b1⟩
    split
    swap
    · simp only [WP.spec_ok]; exact F1
    have hR := h1.release _ h1.cur
    have hhead : i1 = (L.relQ s1 (L.cpu s1)).head := by subst_vars; rfl
    have hne : i1 ≠ 0#u64 := by simpa [b_post] using ‹¬b = true›
    have hmem : i1 ∈ R1 (L.cpu s1) := by
      rw [hhead, hR.head] at hne ⊢
      cases hR' : R1 (L.cpu s1) with
      | nil => rw [hR'] at hne; exact absurd rfl hne
      | cons x xs => simp
    have hT1 : i1 ∈ T := h1.memTR h1.cur hmem
    refine WP.spec_bind (WP.spec_and (sched.release_remove.sch s1 i1 Q1 R1 h1 hB1 hS1 hT1)
      (sched.release_remove.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) s1 i1 h1 hT1)) ?_
    rintro s2 ⟨⟨⟨⟨Q2, R2, h2⟩, hB2, f2⟩, -, -, hst2⟩, F2⟩
    have hrun : Runnable (L.mem s2 (stA i1)) := by
      rw [hst2 i1 hT1]; exact h1.runR _ h1.cur i1 hmem
    have hrel : (L.mem s1 (inqA i1) &&& sched.Q_RELEASE) ≠ 0#u64 := (h1.released i1 hT1).2 (by rw [h1.inR _ h1.cur i1 hmem]; exact hmem)
    refine WP.spec_bind (WP.spec_and (sched.possible_switch_to.sch s2 i1 Q2 R2 h2 hB2 (hS1.fr f2) hT1 hrun (fun h0 => by
      rw [f2.sc i1 hT1] at h0 ⊢; exact hB1.sact i1 hT1 (Or.inr (Or.inl hrel)) h0))
      (sched.possible_switch_to.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) s2 i1 h2 hT1)) ?_
    rintro s3 ⟨⟨⟨hi3, hB3, f3⟩, -, -⟩, F3⟩
    simp only [WP.spec_ok]
    exact ⟨⟨hi3, hB3, f1.trans (f2.trans f3)⟩, F1.trans (F2.trans F3), by omega⟩
  · exact ⟨⟨⟨Q, R, h⟩, hB, Fr.refl _ _⟩, Foot.refl _⟩

theorem sched.schedule.sfoot {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    sched.schedule st ar s a ⦃ s' _ => ∃ rf : S × A, timer.fire st ar s a = ok rf ∧
      FootD st T Cs Sg Scs Z (EH H) s rf.1 ∧ SFoot st T Cs Sg Scs Z H rf.1 s' ⦄ := by
  unfold sched.schedule sched.awaken
  -- `awaken`
  refine WP.spec_bind (Pₘ := fun r => Good st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧ ∃ rf : S × A,
      timer.fire st ar s a = ok rf ∧ FootD st T Cs Sg Scs Z (EH H) s rf.1 ∧ SFoot st T Cs Sg Scs Z H rf.1 r.1) ?_ ?_
  · refine WP.spec_bind (spec_eq' (timer.fire.tinvF hA hNt s a h.tinv)) ?_
    rintro ⟨s1, a1⟩ ⟨hf1, ⟨⟨Q1, R1, h1⟩, hB1, hX1, hS1, hSg1⟩, F1⟩
    try simp only [WP.uncurry'_pair]
    refine WP.spec_bind (WP.spec_and (sched.awaken_loop.sch s1 _ Q1 R1 h1 hB1 hS1.sg)
      (sched.awaken_loop.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s1 _ Q1 R1 h1 hB1 hS1.sg)) ?_
    rintro s2 ⟨⟨P2, -⟩, F2⟩
    exact (WP.spec_ok _).2 ⟨P2.good hS1 hX1, (s1, a1), hf1, F1, F2.sfoot⟩
  rintro ⟨s1, a1⟩ ⟨⟨⟨Q1, R1, h1⟩, hB1, hS1, hX1⟩, rf, hrf, Fd, F1⟩
  -- `check_domain_time` does nothing with one domain
  unfold sched.check_domain_time sched.is_cur_domain_expired
  simp only [layout.NUM_DOMAINS, fl4_abi.config.NUM_DOMAINS]
  have hnd : ¬ ((1#u64) > (1#u64)) := by simp
  simp only [hnd, ↓reduceIte, bind_ok, Bool.false_eq_true]
  step with sched.action.spec as ⟨act, act_post⟩
  -- the action
  refine WP.spec_bind (Pₘ := fun r => Good st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧ L.mem r.1 (scA (L.curW r.1)) ≠ 0#u64 ∧
      L.mem r.1 (scA (L.curW r.1)) ∈ Ac ∧ SFoot st T Cs Sg Scs Z H s1 r.1) ?_ ?_
  · split
    · rename_i hnr
      step with sched.cur_thread.spec as ⟨ct, ct_post⟩
      have hctT : ct ∈ T := by rw [ct_post]; exact h1.curT
      step with sched.is_schedulable.spec' as ⟨wr, wr_post⟩
      refine WP.spec_bind (Pₘ := fun s4 => Post st T Cs Ω H Sg Ac s1 s4 ∧ L.actionW s4 = L.actionW s1 ∧
          Foot st T Cs Sg Scs Z (EH H) s1 s4) ?_ ?_
      · split
        · exact WP.spec_mono (WP.spec_and (sched.enqueue.sch s1 ct Q1 R1 h1 hB1 hS1.sg hctT (fun _ => (wr_post ‹_›).2.2.1)
            (fun _ => (wr_post ‹_›).1) (fun _ => (wr_post ‹_›).2.1)
            (fun _ => (hS1.act _ (hX1.2.2.bound _ hctT (wr_post ‹_›).2.1).1).2 (wr_post ‹_›).2.2.2))
            (sched.enqueue.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s1 ct h1 hctT))
            fun s4 h4 => ⟨h4.1.1, h4.1.2.1, h4.2⟩
        · exact (WP.spec_ok _).2 ⟨⟨⟨Q1, R1, h1⟩, hB1, Fr.refl _ _⟩, rfl, Foot.refl _⟩
      rintro s4 ⟨⟨⟨Q4, R4, h4⟩, hB4, f4⟩, ea4, F4⟩
      have hS4 := hS1.fr f4
      have hX4 := hX1.fr f4
      have hact4 : L.actionW s4 = act := ea4.trans act_post.symm
      split
      · exact WP.spec_mono (WP.spec_and (sched.schedule_choose_new_thread.sch hA s4 a1 Q4 R4 h4 hB4 hS4 hX4)
          (sched.schedule_choose_new_thread.sfoot (Scs := Scs) (Z := Z) hA s4 a1 Q4 R4 h4 hB4 hS4.sg)) fun r hr => by
            obtain ⟨s', a'⟩ := r
            simp only [WP.uncurry'_pair] at hr ⊢
            exact ⟨hr.1.1, hr.1.2.1, hr.1.2.2, F4.sfoot.trans hr.2⟩
      rename_i hnc
      have hT : act ∈ T := by
        rcases h4.action with e | e | e
        · exfalso; rw [hact4] at e; rw [e, resume_val] at hnr; simp at hnr
        · exfalso; rw [hact4] at e; rw [e, choose_val] at hnc; simp at hnc
        · rw [hact4] at e; exact e
      have hbd : L.mem s4 (scA act) ≠ 0#u64 := by have := hB4.act (hact4 ▸ hT); rw [hact4] at this; exact this
      have L1 := WP.spec_and (cand_choose hA s4 a1 act Q4 R4 h4 hB4 hS4 hX4 hact4 hT true)
        (cand_choose.sfoot (Scs := Scs) (Z := Z) hA s4 a1 act Q4 R4 h4 hB4 hS4 hact4 hT true)
      have L3 := WP.spec_and (cand_choose hA s4 a1 act Q4 R4 h4 hB4 hS4 hX4 hact4 hT false)
        (cand_choose.sfoot (Scs := Scs) (Z := Z) hA s4 a1 act Q4 R4 h4 hB4 hS4 hact4 hT false)
      simp only [↓reduceIte, Bool.false_eq_true] at L1 L3
      replace L1 := WP.spec_mono L1 (P₁ := WP.uncurry' fun s' _ => Good st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
          L.mem s' (scA (L.curW s')) ≠ 0#u64 ∧ L.mem s' (scA (L.curW s')) ∈ Ac ∧ SFoot st T Cs Sg Scs Z H s1 s')
        fun r hr => by
          obtain ⟨s', a'⟩ := r
          simp only [WP.uncurry'_pair] at hr ⊢
          exact ⟨hr.1.1, hr.1.2.1, hr.1.2.2, F4.sfoot.trans hr.2⟩
      replace L3 := WP.spec_mono L3 (P₁ := WP.uncurry' fun s' _ => Good st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
          L.mem s' (scA (L.curW s')) ≠ 0#u64 ∧ L.mem s' (scA (L.curW s')) ∈ Ac ∧ SFoot st T Cs Sg Scs Z H s1 s')
        fun r hr => by
          obtain ⟨s', a'⟩ := r
          simp only [WP.uncurry'_pair] at hr ⊢
          exact ⟨hr.1.1, hr.1.2.1, hr.1.2.2, F4.sfoot.trans hr.2⟩
      have L2 : sched.switch_to_thread st ar s4 a1 act ⦃ s' _ => Good st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
          L.mem s' (scA (L.curW s')) ≠ 0#u64 ∧ L.mem s' (scA (L.curW s')) ∈ Ac ∧ SFoot st T Cs Sg Scs Z H s1 s' ⦄ :=
        WP.spec_mono (WP.spec_and (sched.switch_to_thread.sch hA s4 a1 act Q4 R4 h4 hB4 hS4.sg hT hbd
          (by have := hB4.actA (hact4 ▸ hT); rwa [hact4] at this))
          (sched.switch_to_thread.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) hA s4 a1 act h4 hT)) fun r hr => by
          obtain ⟨s', a'⟩ := r
          simp only [WP.uncurry'_pair] at hr ⊢
          exact ⟨hr.1.1.good hS4 hX4, by rw [hr.1.2.1, hr.1.1.fr.sc act hT]; exact hbd, by
            rw [hr.1.2.1, hr.1.1.fr.sc act hT]; have := hB4.actA (hact4 ▸ hT); rwa [hact4] at this,
            (F4.trans hr.2).sfoot⟩
      step with sched.cur_thread.spec as ⟨ct1, _⟩
      step with sched.idle_thread.spec' as ⟨t, _⟩
      step with tcb_eq.spec as ⟨b⟩
      refine WP.spec_bind (Pₘ := fun _ => True) ?_ fun fastfail _ => ?_
      · split
        · simp
        · step with obj.Tcb.prio.spec as ⟨i, _⟩
          step with obj.Tcb.prio.spec as ⟨i1, _⟩
          split <;> simp
      split
      · step with sched.cur_domain.spec' as ⟨i⟩
        step with obj.Tcb.prio.spec as ⟨i1, _⟩
        step with sched.is_highest_prio.ok s4 Q4 R4 h4 as ⟨b1⟩
        split
        · split
          · step with obj.Tcb.prio.spec as ⟨i2, _⟩
            split
            · exact L1
            · exact L2
          · exact L2
        · exact L3
      · split
        · step with obj.Tcb.prio.spec as ⟨i, _⟩
          step with obj.Tcb.prio.spec as ⟨i1, _⟩
          split
          · exact L1
          · exact L2
        · exact L2
    · rename_i hr0
      have e0 : L.actionW s1 = 0#u64 := by
        rw [← act_post]; rw [resume_val] at hr0
        apply UScalar.eq_of_val_eq; simpa using hr0
      exact (WP.spec_ok _).2 ⟨⟨⟨Q1, R1, h1⟩, hB1, hS1, hX1⟩, hB1.resume e0, hB1.curA h1.curT e0, SFoot.refl _⟩
  rintro ⟨s3, a2⟩ ⟨⟨⟨Q3, R3, h3⟩, hB3, hS3, hX3⟩, hcb1, hcb2, F3⟩
  have hcb := And.intro hcb1 hcb2
  try simp only [WP.uncurry'_pair]
  -- resume, then switch the SC
  rw [resume_val]
  refine WP.spec_bind (WP.spec_and (sched.set_action.sch s3 0#u64 Q3 R3 h3 hB3 hS3.sg (Or.inl rfl)
    (fun hT => absurd hT (notT_small h3.tcbs (by simp))) (fun hT => absurd hT (notT_small h3.tcbs (by simp)))
    (fun _ => hcb) (fun hT => absurd hT (notT_small h3.tcbs (by simp))))
    (sched.set_action.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s3 0#u64 (h3.nodes _ h3.cur) h3.cur)) ?_
  rintro s4 ⟨⟨P4, ea4, -, -⟩, F4⟩
  obtain ⟨⟨Q4, R4, h4⟩, hB4, hS4, hX4⟩ := P4.good hS3 hX3
  have hcT := h4.curT
  have hb4 : L.mem s4 (scA (L.curW s4)) ≠ 0#u64 := hB4.resume ea4
  have hO4 := hX4.1
  have hsub4 := hS4.sub
  have hts : L.mem s4 (scA (L.curW s4)) ∈ Scs := (hX4.2.2.bound _ hcT hb4).1
  have hcs : L.cscW s4 ∈ Scs := hX4.2.2.cur
  obtain ⟨hPc, hzc⟩ := hO4.sc _ hcs
  obtain ⟨h8c, h128c, -⟩ := sc_lo hPc hzc
  have hvc := sc_word_val hPc hzc (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
  have hcv : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
  have hcq : SCq st s4 Ω (L.cscW s4) (Z (L.cscW s4)) := by
    obtain ⟨a1, a2, a3⟩ := maxA_facts hO4 hcs
    exact ⟨(hS4.all _ hcs).1, fun b hb hi => hsub4 _ ((hS4.all _ hcs).2.2 b hb hi),
      ⟨⟨by rw [hvc]; omega, by rw [hvc, hcv]; omega⟩, by unfold Aligned; rw [hvc, hcv]; omega⟩, ⟨a2, a3⟩, a1⟩
  have htin : SCin st s4 Ω (L.mem s4 (scA (L.curW s4))) (Z (L.mem s4 (scA (L.curW s4)))) :=
    (hS4.scin hts (hB4.curA hcT ea4)).mono hsub4
  have hN4 := h4.nodes _ h4.cur
  refine WP.spec_bind (WP.spec_and (sched.switch_sched_context.free hA s4 a2 (zt := Z (L.mem s4 (scA (L.curW s4))))
    (zc := Z (L.cscW s4)) h4.cur hN4 h4.omega hcq
    (fun hne => ⟨htin, hS4.disj _ hcT hb4 hne⟩))
    (sched.switch_sched_context.fp hA s4 a2 (zt := Z (L.mem s4 (scA (L.curW s4))))
      (zc := Z (L.cscW s4))
      (B := SchedW st T Cs Sg Scs Z H s4) h4.cur hN4 h4.omega
      hcq (fun hne => ⟨htin, hS4.disj _ hcT hb4 hne⟩)
      (Or.inl (kw_node h4.cur (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])))
      (Or.inl (kw_node h4.cur (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])))
      (Or.inl (kw_node h4.cur (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])))
      (fun _ b _ hr => Or.inl (kw_sc hts hr.inSC))
      (fun b _ hr => by
        rcases hr with hr | rfl
        · exact Or.inl (kw_sc hcs hr.inSC)
        · exact Or.inl (kw_sc hcs (show InSC (L.cscW s4) (Z (L.cscW s4))
            (core.num.U64.wrapping_add (L.cscW s4) layout.sc.CONSUMED) from
            ⟨by rw [hvc]; omega, by rw [hvc, hcv]; omega⟩))))) ?_
  rintro ⟨s5, a3⟩ ⟨w5, w5', -, -, -⟩
  simp only [WP.uncurry'_pair] at w5 w5' ⊢
  have h5 := (free_step h4 hB4 w5).1
  step with LawfulStore.cur_cpu_spec as ⟨c, c_post⟩
  step with obj.node_get.spec as ⟨i, _⟩
  refine WP.spec_bind (Pₘ := fun r => SchedQueuesInv st T Cs Ω H r.1 Q4 R4 ∧ SFoot st T Cs Sg Scs Z H s5 r.1) ?_ ?_
  · split
    · have hB5 := (free_step h4 hB4 w5).2
      refine WP.spec_bind (WP.spec_and (sched.set_next_interrupt.free (Ω := Ω) hA s5 a3 h5.cur (h5.nodes _ h5.cur))
        (sched.set_next_interrupt.fp hA s5 a3 (B := SchedW st T Cs Sg Scs Z H s5) (h5.nodes _ h5.cur)
          (Or.inl (kw_node h5.cur (by simp [layout.node.ARMED]) (by simp [layout.node.ARMED]))))) ?_
      rintro ⟨s7, a5⟩ ⟨w7, w7'⟩
      simp only [WP.uncurry'_pair] at w7 w7' ⊢
      have h7 := free_step h5 hB5 w7
      step with obj.node_set.spec as ⟨s8, s8_post⟩
      try simp only [WP.spec_ok]
      have w8 : WritesIn st s5 s8 (L.Free s5 Ω Cs) := by
        rw [s8_post, c_post]
        exact w7.free_trans (free_node_write w7.1 h5.cur (h5.nodes _ h5.cur)
          (by simp [layout.node.REPROGRAM, LowFree]))
      have hN7 : NodePlaced st T s7 (L.cpu s7) := by rw [w7.2.1]; exact (h5.nodes _ h5.cur).ksb w7.1
      have F8 : SFoot st T Cs Sg Scs Z H s7 s8 := by
        rw [s8_post, c_post, ← w7.2.1]
        exact (foot_node (Es := EH H) hN7 (by rw [w7.2.1]; exact h5.cur) (by simp [layout.node.REPROGRAM])
          (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])).sfoot
      exact ⟨(free_step h5 hB5 w8).1, w7'.trans F8 |>.mono fun b hb => Or.elim hb id fun hb => SchedW.ksb w7'.1 hb⟩
    · exact (WP.spec_ok _).2 ⟨h5, SFoot.refl _⟩
  rintro ⟨s6, a4⟩ ⟨h6, F6⟩
  try simp only [WP.uncurry'_pair]
  exact WP.spec_mono (smp.send_pending.fp hA s6 a4 (B := SchedW st T Cs Sg Scs Z H s6) (h6.nodes _ h6.cur)
      (Or.inl (kw_node h6.cur (by simp [layout.node.IPI_PENDING]) (by simp [layout.node.IPI_PENDING])))) fun r w => by
    obtain ⟨s', a'⟩ := r
    simp only [WP.uncurry'_pair] at w ⊢
    exact ⟨rf, hrf, Fd, F1.trans (F3.trans ((F4.sfoot.trans w5').trans (F6.trans w)))⟩

/-- **The footprint of `timer::fire`** (`KW` with the heap's endpoints and
notifications). -/
theorem timer.fire.kw {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    timer.fire st ar s a ⦃ s' _ => FootD st T Cs Sg Scs Z (EH H) s s' ⦄ :=
  WP.spec_mono (timer.fire.tinvF hA hNt s a h.tinv) fun r hr => by
    obtain ⟨s', a'⟩ := r; simp only [WP.uncurry'_pair] at hr ⊢; exact hr.2

/-- **The footprint of `schedule`**: the timers' (`FootD`: `KW` and the debug
lists), then the words of `SchedW`. -/
theorem sched.schedule.kw {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    sched.schedule st ar s a ⦃ s' _ => ∃ rf : S × A, timer.fire st ar s a = ok rf ∧
      FootD st T Cs Sg Scs Z (EH H) s rf.1 ∧ WritesIn st rf.1 s' (SchedW st T Cs Sg Scs Z H rf.1) ⦄ :=
  sched.schedule.sfoot hA hNt s a h

end

end Fl4Proofs.P1
