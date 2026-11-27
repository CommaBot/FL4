/-
P1 (AArch64 only): `STATE` / `RUN_VCPU` frames, and `timer::fire` without [J] `RvKeep`.

`RvSt T s s'`: every thread's `STATE` and `RUN_VCPU` words are kept, so [J] `RunVcpuInv` moves along
(`RunVcpuInv.rvSt`). Frames proved here:
* `timer.remove.rvst` / `.rvi`: `timer.remove` writes only TCB timer fields and node timer words (`TKeep`).
* `sched.enqueue.fld`, `sched.possible_switch_to.fld`, `sched.postpone.fld`, `schedcontext.resume.fld`: the
  queue code keeps every TCB field outside the queue links and the `IN_QUEUE` word (`field_qfoot`).
* `schedcontext.donate.rv0`: the second half of `donate` writes the SC's `TCB` word, the donee's `SC` and
  `AFFINITY` words and debug-list words (`donate_tail.frame`, `donW_keeps`).
* `notification.maybe_donate_sched_context.rvst`, `signal_tail.rv`, `notification.set_active.rvst`,
  `notification.kick_guest.rvi`.
* **`notification.send_signal.rvi`**: `send_signal` of a notification (`H n = some .ntfn`) keeps [J]
  `RunVcpuInv`. No path writes a `RUN_VCPU` word, and the only `STATE` write makes a thread that is blocked on
  receive or on the notification running; such a thread runs no VCPU (`RunVcpuInv.blocked`). The
  `TS_RUNNING_VM` bound thread is only kicked (`remote_tcb_stall`, IPI words).

`QueueFire`'s [J] `RvKeep` is not derivable in its stated form: its `send_signal` half quantifies over every
`n ∈ Nt` without `H n = some .ntfn`. `TInv` ties the notification queues to the heap `H`, not to `Nt`, so for
an `n ∈ Nt` that the heap does not type as a notification, with state word `NTFN_WAITING`, nothing constrains the
"head" waiter: it may be a `TS_RUNNING_VM` thread with `RUN_VCPU ≠ 0`, which `send_signal` makes running.
Its `timer.remove` half is `timer.remove.rvi`. `timer::fire`'s loop has `hNt` (`Nt` are notifications), so
the variants `timer.fire_loop.tinv_rv`, `timer.fire.tinv_rv`, `sched.schedule.tinv_rv` and
`sched.schedule.entry_rv` take no `RvKeep`.

Named premises used (none new): [J] `IbKeep` (`QueueSignal`, as in `QueueFire`) and [J] `RunVcpuInv` at the
entry state (`hRV`, see `RunVcpu`).
-/
import Fl4ProofsA64.P1.QueueTimerSet
import Fl4ProofsA64.P1.RunVcpuRecv
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-! ## The `STATE` / `RUN_VCPU` frame -/

/-- Every thread's `STATE` and `RUN_VCPU` words are kept. -/
def RvSt (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s s' : S) : Prop :=
  ∀ y ∈ T, L.mem s' (stA y) = L.mem s (stA y) ∧ L.mem s' (runVcpuA y) = L.mem s (runVcpuA y)

theorem RvSt.refl (s : S) : RvSt st T s s := fun _ _ => ⟨rfl, rfl⟩

theorem RvSt.trans {s₁ s₂ s₃ : S} (h₁ : RvSt st T s₁ s₂) (h₂ : RvSt st T s₂ s₃) : RvSt st T s₁ s₃ :=
  fun y hy => ⟨(h₂ y hy).1.trans (h₁ y hy).1, (h₂ y hy).2.trans (h₁ y hy).2⟩

/-- [J] `RunVcpuInv` moves along an `RvSt` step. -/
theorem RunVcpuInv.rvSt {s s' : S} (hRV : RunVcpuInv st T s) (f : RvSt st T s s') : RunVcpuInv st T s' :=
  hRV.keep (fun y hy => (f y hy).1) (fun y hy => (f y hy).2)

/-- From a frame of the TCB fields outside the endpoint links. -/
theorem RvSt.of_fld {s s' : S}
    (hf : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 →
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) : RvSt st T s s' :=
  fun y hy => ⟨by rw [stA_eq]; exact hf y hy _ (by simp) (by simp) (by simp) (by simp),
    hf y hy 3672#u64 (by simp) (by simp) (by simp) (by simp)⟩

/-- A write of a TCB field other than `STATE` and `RUN_VCPU`. -/
theorem RvSt.wr_field {s : S} {t K v : U64} (hT : TcbPlaced T) (ht : t ∈ T) (hK : K.val < 4096)
    (hK8 : K.val % 8 = 0) (h1 : K.val ≠ 3328) (h2 : K.val ≠ 3672) :
    RvSt st T s (L.wr s (core.num.U64.wrapping_add t K) v) := fun y hy =>
  ⟨by rw [stA_eq]
      exact L.mem_wr_ne (field_aligned (hT t ht) hK hK8) (field_aligned (K := 3328#u64) (hT y hy) (by simp) (by simp))
        (fun e => field_ne (K2 := 3328#u64) (hT t ht) (hT y hy) hK (by simp) (fun _ => by simpa using h1)
          (UScalar.eq_of_val_eq e)),
    L.mem_wr_ne (field_aligned (hT t ht) hK hK8) (field_aligned (K := 3672#u64) (hT y hy) (by simp) (by simp))
      (fun e => field_ne (K2 := 3672#u64) (hT t ht) (hT y hy) hK (by simp) (fun _ => by simpa using h2)
        (UScalar.eq_of_val_eq e))⟩

/-- A write of a word outside the objects (e.g. a word of `Ω`). -/
theorem RvSt.wr_out {s : S} {a v : U64} (hT : TcbPlaced T) (ha : OutsideObjs st T Cs s a) :
    RvSt st T s (L.wr s a v) := fun y hy =>
  ⟨by rw [stA_eq]
      exact L.mem_wr_ne ha.1 (field_aligned (K := 3328#u64) (hT y hy) (by simp) (by simp))
        (fun e => out_ne_field (K := 3328#u64) ha hy (hT y hy) (by simp) e.symm),
    L.mem_wr_ne ha.1 (field_aligned (K := 3672#u64) (hT y hy) (by simp) (by simp))
      (fun e => out_ne_field (K := 3672#u64) ha hy (hT y hy) (by simp) e.symm)⟩

/-! ## `timer.remove` (the `timer.remove` half of `RvKeep`) -/

theorem timer.remove.rvst (s : S) (t : U64) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T) :
    timer.remove st s t ⦃ s' => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ RvSt st T s s' ⦄ :=
  WP.spec_mono (timer.remove.tf (s0 := s) s t (TF.start h) ht) fun _ h' => ⟨h'.1, fun y hy =>
    ⟨by rw [stA_eq]; exact h'.2.2.2.1 y hy _ (by simp) (by simp) (Or.inl (by simp)),
     h'.2.2.2.1 y hy 3672#u64 (by simp) (by simp) (Or.inr (by simp))⟩⟩

/-- `timer.remove` keeps [J] `RunVcpuInv`. -/
theorem timer.remove.rvi (s : S) (t : U64) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hRV : RunVcpuInv st T s) (ht : t ∈ T) : timer.remove st s t ⦃ s' => RunVcpuInv st T s' ⦄ :=
  WP.spec_mono (timer.remove.rvst s t h ht) fun _ h' => hRV.rvSt h'.2

/-! ## The queue code -/

theorem sched.enqueue.fld {X : Set U64} (s : S) (t : obj.Tcb) {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) {K : U64} (hK : K.val < 4096) (hK8 : K.val % 8 = 0)
    (hKl : K.val ≠ 3480 ∧ K.val ≠ 3488 ∧ K.val ≠ 3496 ∧ K.val ≠ 3504) (hKq : K.val ≠ 3592) :
    sched.enqueue st s t ⦃ s' => ∀ y ∈ T,
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) ⦄ := by
  have hc := h.aff t ht
  have hp := h.prio t ht
  refine WP.spec_mono (sched.enqueue.foot s t _ h.tcbs ht hp (h.nodes _ hc) (h.nodes _ h.cur)
    ((h.ready _ hc).1.rel _ hp) (fun h0 => h.notQ ht h0 hc hp)) fun s1 hh => ?_
  have hW : ∀ w ∈ t :: Q (L.mem s (affA t)) (L.mem s (prioA t)), w ∈ T := by
    intro w hw; rcases List.mem_cons.1 hw with rfl | hw
    · exact ht
    · exact h.memT hc hp hw
  exact fun y hy => field_qfoot h.tcbs hW (h.nodes _ hc) (h.nodes _ h.cur) ht hh.1 hy hK hK8 hKl (fun _ => hKq)

theorem sched.possible_switch_to.fld {X : Set U64} (s : S) (t : obj.Tcb) {Q : U64 → U64 → List U64}
    {R : U64 → List U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T Ac s) (hSg : SgOK st Ω Sg s)
    (ht : t ∈ T) {K : U64} (hK : K.val < 4096) (hK8 : K.val % 8 = 0)
    (hKl : K.val ≠ 3480 ∧ K.val ≠ 3488 ∧ K.val ≠ 3496 ∧ K.val ≠ 3504) (hKq : K.val ≠ 3592) :
    sched.possible_switch_to st s t ⦃ s' => ∀ y ∈ T,
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) ⦄ := by
  have hST : P0.StoreTotal st := L.total
  unfold sched.possible_switch_to sched.cur_domain
  step as ⟨i, ei⟩
  split
  · exact (WP.spec_ok _).2 fun _ _ => rfl
  step as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 fun _ _ => rfl
  step as ⟨i1, ei1⟩
  step as ⟨i2, ei2⟩
  split
  · exact sched.enqueue.fld s t h ht hK hK8 hKl hKq
  step as ⟨i3, ei3⟩
  step as ⟨i4, ei4⟩
  split
  · exact sched.enqueue.fld s t h ht hK hK8 hKl hKq
  step as ⟨i5, ei5⟩
  split
  · refine WP.spec_bind (WP.spec_and (sched.reschedule_required.schX s Q R h hB hSg)
      (sched.reschedule_required.fldX s Q R h hB hSg hK hK8 hKl hKq)) ?_
    rintro s1 ⟨⟨⟨Q1, R1, h1⟩, -⟩, f1⟩
    exact WP.spec_mono (sched.enqueue.fld s1 t h1 ht hK hK8 hKl hKq) fun s2 f2 y hy => (f2 y hy).trans (f1 y hy)
  · refine WP.spec_mono (sched.set_action.spec s _) fun s' e => ?_
    subst e
    intro y hy
    exact field_wr_node h h.cur (by rw [act_val]; omega) (by rw [act_val]) hy hK hK8

theorem sched.postpone.fld (s : S) (sc : obj.Sc) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (ht : L.mem s (scTcbA sc) ∈ T)
    (hr0 : (L.mem s (inqA (L.mem s (scTcbA sc))) &&& sched.Q_RELEASE) = 0#u64)
    (hcore : OutsideObjs st T Cs s (scCoreA sc)) (hcs : L.mem s (scCoreA sc) ∈ Cs)
    {K : U64} (hK : K.val < 4096) (hK8 : K.val % 8 = 0)
    (hKl : K.val ≠ 3480 ∧ K.val ≠ 3488 ∧ K.val ≠ 3496 ∧ K.val ≠ 3504) (hKq : K.val ≠ 3592) :
    sched.postpone st s sc ⦃ s' => ∀ y ∈ T,
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) ⦄ := by
  unfold sched.postpone
  step with obj.Sc.tcb.spec as ⟨t, t_post⟩
  subst t_post
  set t := L.mem s (scTcbA sc) with ht_def
  have hT := h.tcbs
  have hc := h.aff t ht
  have hp := h.prio t ht
  have hN := h.nodes _ hc
  have hN' := h.nodes _ h.cur
  refine WP.spec_bind (WP.spec_and (sched.dequeue.inv s t Q R h ht)
    (sched.dequeue.foot s t _ hT ht hp hN hN' ((h.ready _ hc).1.rel _ hp) (h.queued t ht).1)) ?_
  rintro s1 ⟨h1, hw1, -⟩
  have hW1 : ∀ w ∈ Q (L.mem s (affA t)) (L.mem s (prioA t)), w ∈ T := fun w hw => h.memT hc hp hw
  have f1 : ∀ y ∈ T, L.mem s1 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y hy => field_qfoot hT hW1 hN hN' ht hw1 hy hK hK8 hKl (fun _ => hKq)
  have core1 : L.mem s1 (scCoreA sc) = L.mem s (scCoreA sc) :=
    hw1.mem_eq hcore.1 (qfoot_out hT hW1 hN hN' ht hc h.cur hcore)
  have hr1 : (L.mem s1 (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by
    by_contra hcn
    exact h.notR ht hr0 (h1.aff t ht) ((h1.released t ht).1 hcn)
  have hT1 := h1.tcbs
  have hc1 := h1.aff t ht
  have hN1 := h1.nodes _ hc1
  have hN1' := h1.nodes _ h1.cur
  refine WP.spec_bind (sched.release_enqueue.foot s1 t _ hT1 ht (h1.notR ht hr1 hc1) hN1 hN1' (h1.release _ hc1)) ?_
  rintro s2 ⟨hw2, -⟩
  have hW2 : ∀ w ∈ t :: R (L.mem s1 (affA t)), w ∈ T := by
    intro w hw; rcases List.mem_cons.1 hw with rfl | hw
    · exact ht
    · exact h1.memTR hc1 hw
  have f2 : ∀ y ∈ T, L.mem s2 (core.num.U64.wrapping_add y K) = L.mem s1 (core.num.U64.wrapping_add y K) :=
    fun y hy => field_qfoot hT1 hW2 hN1 hN1' ht hw2 hy hK hK8 hKl (fun _ => hKq)
  have core2 : L.mem s2 (scCoreA sc) = L.mem s (scCoreA sc) :=
    (hw2.mem_eq hcore.1 (qfoot_out hT1 hW2 hN1 hN1' ht hc1 h1.cur (hcore.ksb hw1.1))).trans core1
  step with obj.Sc.cpu.spec as ⟨cpu, cpu_post⟩
  rw [core2] at cpu_post
  subst cpu_post
  refine WP.spec_mono (sched.set_reprogram_on.spec s2 _) fun s3 e3 => ?_
  subst e3
  have hN2 : NodePlaced st T s2 (L.mem s (scCoreA sc)) := (h.nodes _ hcs).ksb (hw2.1.trans hw1.1)
  intro y hy
  rw [L.mem_wr_ne (nodeAt_aligned hN2 (by rw [repr_val]; omega) (by rw [repr_val])) (field_aligned (hT y hy) hK hK8)
    (fun e => node_ne_field hN2 (by rw [repr_val]; omega) hy (hT y hy) hK (UScalar.eq_of_val_eq e))]
  exact (f2 y hy).trans (f1 y hy)

theorem schedcontext.resume.fld {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (sc : obj.Sc) (Q : U64 → U64 → List U64) (R : U64 → List U64) (h : SchedQueuesInv st T Cs Ω H s Q R)
    (hsc : sc ≠ 0#u64 → L.mem s (scTcbA sc) ≠ 0#u64 →
      L.mem s (scTcbA sc) ∈ T ∧ OutsideObjs st T Cs s (scCoreA sc) ∧ L.mem s (scCoreA sc) ∈ Cs ∧
        L.actionW s ≠ L.mem s (scTcbA sc))
    {K : U64} (hK : K.val < 4096) (hK8 : K.val % 8 = 0)
    (hKl : K.val ≠ 3480 ∧ K.val ≠ 3488 ∧ K.val ≠ 3496 ∧ K.val ≠ 3504) (hKq : K.val ≠ 3592) :
    schedcontext.resume st ar s a sc ⦃ s' _ => ∀ y ∈ T,
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) ⦄ := by
  unfold schedcontext.resume
  step with obj.Sc.is_null.spec as ⟨b, b_post⟩
  split
  · exact (WP.spec_ok _).2 fun _ _ => rfl
  rename_i hb
  have hsc0 : sc ≠ 0#u64 := by simpa [b_post] using hb
  step with obj.Sc.tcb.spec as ⟨i, i_post⟩
  step with obj.Tcb.is_null.spec as ⟨b1, b1_post⟩
  split
  · exact (WP.spec_ok _).2 fun _ _ => rfl
  rename_i hb1
  have hi0 : L.mem s (scTcbA sc) ≠ 0#u64 := by rw [← i_post]; simpa [b1_post] using hb1
  obtain ⟨hiT, hcore, hcs, -⟩ := hsc hsc0 hi0
  step with sched.is_schedulable.spec' as ⟨b2, b2_post⟩
  split
  · rename_i hb2
    obtain ⟨-, -, hr0, -⟩ := b2_post hb2
    rw [i_post] at hr0
    have post := sched.postpone.fld s sc Q R h hiT hr0 hcore hcs hK hK8 hKl hKq
    step with sporadic.ready.spec as ⟨b3⟩
    split
    · step with sporadic.sufficient.ok (st := st) hA as ⟨b4⟩
      split
      · exact (WP.spec_ok _).2 fun _ _ => rfl
      · exact WP.spec_bind post fun s1 h1 => by simp only [WP.spec_ok, WP.uncurry'_pair]; exact h1
    · exact WP.spec_bind post fun s1 h1 => by simp only [WP.spec_ok, WP.uncurry'_pair]; exact h1
  · exact (WP.spec_ok _).2 fun _ _ => rfl

/-! ## Donation -/

/-- `donate` of an SC bound to no thread to `dst` (running no VCPU) keeps every `STATE` and `RUN_VCPU` word. -/
theorem schedcontext.donate.rv0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {X : Set U64}
    (s : S) (a : A) (sc dst : U64) {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hSg : SgOK st Ω Sg s)
    (hdst : dst ∈ T) (hsc : sc ∈ Scs) (htc0 : L.mem s (scTcbA sc) = 0#u64) (hcore : L.mem s (scCoreA sc) ∈ Cs)
    (hrv : L.mem s (runVcpuA dst) = 0#u64) :
    schedcontext.donate st ar s a sc dst ⦃ s' _ => RvSt st T s s' ⦄ := by
  have hm : scTcbA sc ∈ Ω := hSg.sub _ (hX.1.fixW sc hsc).1
  unfold schedcontext.donate
  step with obj.Sc.tcb.spec as ⟨i, ei⟩
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  split
  · try simp only [Aeneas.Std.bind_ok]
    refine WP.spec_mono (donate_tail.frame hA s a sc dst h (XInv.dbg hX) hX.1 hSg.sub hsc hdst hcore hrv)
      fun r hr => ?_
    obtain ⟨s', a'⟩ := r
    simp only [WP.uncurry'_pair] at hr ⊢
    have kk := (donW_keeps h.tcbs h.nodes h.cur (h.omega _ hm) hdst hr.1).2.2.2.2
    refine fun y hy => ⟨?_, kk y hy 3672#u64 (by simp) (by simp) (by simp) (by simp) (fun _ => ⟨by simp, by simp⟩)⟩
    rw [stA_eq]
    exact kk y hy _ (by simp) (by simp) (by simp) (by simp) (fun _ => ⟨by simp, by simp⟩)
  · rename_i hb; exfalso; exact hb (by rw [eb, ei, htc0]; rfl)

theorem notification.maybe_donate_sched_context.rvst {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (s : S) (a : A) (t n : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (ht : t ∈ T)
    (htq : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64) (htr : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64)
    (hta' : L.actionW s ≠ t) (hti : L.idleW s ≠ t)
    (hns : L.mem s (ntfnScA n) ≠ 0#u64 → L.mem s (scTcbA (L.mem s (ntfnScA n))) = 0#u64 →
      L.mem s (scA t) = 0#u64 → L.mem s (ntfnScA n) ∈ Scs ∧ L.mem s (scCoreA (L.mem s (ntfnScA n))) ∈ Cs ∧
        (Sch st s t → L.mem s (ntfnScA n) ∈ Ac))
    (hrv : L.mem s (runVcpuA t) = 0#u64) :
    notification.maybe_donate_sched_context st ar s a t n ⦃ s' _ => RvSt st T s s' ⦄ := by
  have ok0 : (ok (s, a) : Result (S × A)) ⦃ s' _ => RvSt st T s s' ⦄ := (WP.spec_ok _).2 (RvSt.refl s)
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
        hi10 htc0 hcore1 hin1 (by rw [← ei, hi]) hti hrv)
        (schedcontext.donate.rv0 hA s a i1 t h hX hSg ht hS1 htc0 hcore1 hrv)) ?_
      rintro ⟨s4, a4⟩ ⟨⟨⟨⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4⟩, -, -, -, sc4, tc4, ea4⟩, r4⟩
      try simp only [WP.uncurry'_pair]
      have hsc4 : i1 ≠ 0#u64 → L.mem s4 (scTcbA i1) ≠ 0#u64 →
          L.mem s4 (scTcbA i1) ∈ T ∧ OutsideObjs st T Cs s4 (scCoreA i1) ∧ L.mem s4 (scCoreA i1) ∈ Cs ∧
            L.actionW s4 ≠ L.mem s4 (scTcbA i1) := fun _ _ => by
        obtain ⟨-, -, hc4⟩ := hX4.2.2.bound t ht (by rw [sc4]; exact hi10)
        rw [sc4] at hc4
        rw [tc4]
        exact ⟨ht, h4.omega _ ((objs_omega hX4.1 hSg4.sub).2 i1 hS1).2.1, hc4, by rw [ea4]; exact hta'⟩
      refine WP.spec_mono (WP.spec_and (schedcontext.resume.all hA s4 a4 i1 Q4 R4 h4 hB4 hX4 hSg4 hS4 hsc4)
        (schedcontext.resume.fld hA s4 a4 i1 Q4 R4 h4 hsc4 (K := 3672#u64) (by simp) (by simp) (by simp)
          (by simp))) ?_
      rintro ⟨s5, a5⟩ ⟨⟨Q5, R5, -, -, -, -, f5⟩, g5⟩
      try simp only [WP.uncurry'_pair]
      exact r4.trans fun y hy => ⟨f5.st y hy, g5 y hy⟩
    · exact ok0
  · exact ok0

/-! ## `send_signal` -/

/-- `signal_tail` keeps every `STATE` and `RUN_VCPU` word. -/
theorem signal_tail.rv {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s2 : S) (a1 : A)
    (dst n badge : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h2 : SchedQueuesInv st T Cs Ω H s2 Q R) (hB2 : BoundInv st T Ac s2) (hX2 : XInv st T Cs Ω Sg Rp Scs Nt Z s2)
    (hS2 : SCsOK st T Ω Sg Scs Z Ac s2) (hSg2 : SgOK st Ω Sg s2) (hd : dst ∈ T) (hn : n ∈ Nt)
    (dq : (L.mem s2 (inqA dst) &&& sched.Q_QUEUED) = 0#u64) (dr : (L.mem s2 (inqA dst) &&& sched.Q_RELEASE) = 0#u64)
    (da : L.actionW s2 ≠ dst) (di : L.idleW s2 ≠ dst) (dR : ¬ BlockedR (L.mem s2 (stA dst)))
    (hrv : L.mem s2 (runVcpuA dst) = 0#u64) :
    (do
      let s3 ← obj.Tcb.set_reg st dst s2 layout.reg.BADGE badge
      let (s4, a2) ← notification.maybe_donate_sched_context st ar s3 a1 dst n
      let b1 ← sched.is_schedulable st s4 dst
      let s5 ← if b1 then sched.possible_switch_to st s4 dst else ok s4
      let s6 ← notification.unblock_sporadic st s5 dst
      ok (s6, a2)) ⦃ s' _ => RvSt st T s2 s' ⦄ := by
  have hT := h2.tcbs
  have hta := hT dst hd
  refine WP.spec_bind (obj.Tcb.set_reg.badge s2 dst badge hta) fun s3 e3 => ?_
  subst e3
  obtain ⟨h3, hB3, hX3, hS3, hSg3⟩ := badge_all (v := badge) h2 hB2 hX2 hS2 hSg2 hd
  have rv3 : RvSt st T s2 (L.wr s2 (core.num.U64.wrapping_add dst 256#u64) badge) :=
    RvSt.wr_field hT hd (by simp) (by simp) (by simp) (by simp)
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
  have hrv3 : L.mem (L.wr s2 (core.num.U64.wrapping_add dst 256#u64) badge) (runVcpuA dst) = 0#u64 := by
    rw [(rv3 dst hd).2]; exact hrv
  refine WP.spec_bind (WP.spec_and
    (notification.maybe_donate_sched_context.tinv hA _ a1 dst n Q R h3 hB3 hX3 hS3 hSg3 hd
      (by rw [iq3]; exact dq) (by rw [iq3]; exact dr) (by rw [ea3]; exact da) (by rw [ei3]; exact di)
      (ntfn_sc_ok hX3 hn hsA3) hrv3)
    (notification.maybe_donate_sched_context.rvst hA _ a1 dst n Q R h3 hB3 hX3 hS3 hSg3 hd
      (by rw [iq3]; exact dq) (by rw [iq3]; exact dr) (by rw [ea3]; exact da) (by rw [ei3]; exact di)
      (ntfn_sc_ok hX3 hn hsA3) hrv3)) ?_
  rintro ⟨s4, a2⟩ ⟨⟨⟨⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4⟩, -⟩, r4⟩
  try simp only [WP.uncurry'_pair]
  step with sched.is_schedulable.spec' as ⟨b1, hb1⟩
  refine WP.spec_bind (Pₘ := fun s5 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s5 ∧ RvSt st T s4 s5) ?_ ?_
  · split
    · rename_i hb
      refine WP.spec_mono (WP.spec_and (sched.possible_switch_to.sch s4 dst Q4 R4 h4 hB4 hSg4 hd (hb1 hb).1
        (fun _ => (hS4.act _ (hX4.2.2.bound dst hd (hb1 hb).2.1).1).2 (hb1 hb).2.2.2))
        (sched.possible_switch_to.fld s4 dst h4 hB4 hSg4 hd (K := 3672#u64) (by simp) (by simp) (by simp)
          (by simp))) fun s5 hh => ?_
      obtain ⟨⟨p5, -, -⟩, g5⟩ := hh
      exact ⟨⟨p5.inv, p5.bnd, hX4.fr p5.fr, hS4.fr p5.fr, hSg4.fr p5.fr⟩, fun y hy => ⟨p5.fr.st y hy, g5 y hy⟩⟩
    · exact (WP.spec_ok _).2 ⟨⟨⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4⟩, RvSt.refl _⟩
  rintro s5 ⟨⟨⟨Q5, R5, h5⟩, hB5, hX5, hS5, hSg5⟩, r5⟩
  refine WP.spec_bind (endpoint.unblock_sporadic.all s5 dst h5 hB5 hX5 hS5 hSg5 hd) ?_
  rintro s6 ⟨-, -, -, -, -, -, -, -, k6, -⟩
  exact (WP.spec_ok _).2 (rv3.trans (r4.trans (r5.trans (RvSt.of_fld fun y hy K k1 k2 _ _ => k6 y hy K k1 k2))))

/-- `set_active` keeps every `STATE` and `RUN_VCPU` word (it writes two notification words). -/
theorem notification.set_active.rvst (s : S) (n badge : U64) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hn : n ∈ Nt) (hH : H n = some .ntfn) (hst : L.epState s n ≠ 1#u64) :
    notification.set_active st s n badge ⦃ s' => RvSt st T s s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  unfold notification.set_active
  refine WP.spec_bind (obj.Ntfn.set_state.val s n _) fun s1 e1 => ?_
  subst e1
  obtain ⟨h1, -, hX1, -, hSg1, f1, -⟩ :=
    ntfn_state_all (w := obj.NTFN_ACTIVE) h0 hB hX hS hSg hH hst (Or.inr ntfn_active_and)
  refine WP.spec_mono (obj.Ntfn.set_badge.wr _ n badge) fun s2 e2 => ?_
  subst e2
  exact (RvSt.of_fld f1).trans (RvSt.wr_out h1.tcbs (h1.omega _ (hSg1.sub _ (hX1.1.ntB n hn).1)))

/-- `kick_guest` (AArch64: `remote_tcb_stall`, IPI words only) keeps [J] `RunVcpuInv`. -/
theorem notification.kick_guest.rvi {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (t : obj.Tcb) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hRV : RunVcpuInv st T s) :
    notification.kick_guest st ar s a t ⦃ s' _ => RunVcpuInv st T s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  unfold notification.kick_guest
  refine WP.spec_mono (smp.remote_tcb_stall.all hA s a t h0 hB hX hS hSg) fun r hh => ?_
  obtain ⟨s', a'⟩ := r
  simp only [WP.uncurry'_pair] at hh ⊢
  obtain ⟨-, -, -, -, -, -, -, -, -, kf, -⟩ := hh
  exact hRV.rvSt (RvSt.of_fld fun y hy K k1 k2 _ _ => kf y hy K k1 k2)

/-- **`send_signal` keeps [J] `RunVcpuInv`** (for a notification `n`, `H n = some .ntfn`): no step writes a
`RUN_VCPU` word, and the woken thread (blocked on receive or on `n`) runs no VCPU. -/
theorem notification.send_signal.rvi {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (s : S) (a : A) (n badge : U64) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hn : n ∈ Nt)
    (hH : H n = some .ntfn) (hRV : RunVcpuInv st T s) :
    notification.send_signal st ar s a n badge ⦃ s' _ => RunVcpuInv st T s' ⦄ := by
  have hI := h
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hNb := hX.2.2.ntb
  have hT := h0.tcbs
  unfold notification.send_signal
  step with obj.Ntfn.state.spec as ⟨v, hv⟩
  refine sig_if _ _ _ _ (fun hidl => ?_) (fun hnidl => ?_)
  · -- an idle notification
    have hst0 : L.epState s n ≠ 1#u64 := by rw [← hv, hidl]; unfold obj.NTFN_IDLE; decide
    have sa := WP.spec_and (notification.set_active.tinv s n badge hI hn hH hst0)
      (notification.set_active.rvst s n badge hI hn hH hst0)
    step with obj.Ntfn.bound_tcb.val as ⟨i, ei⟩
    step with obj.Tcb.is_null.spec as ⟨b, eb⟩
    have OLD : (do
        let s1 ← notification.set_active st s n badge
        if b = true then ok (s1, a)
        else do
          let i2 ← obj.Tcb.state st i s1
          if i2 = sched.TS_RUNNING_VM then notification.kick_guest st ar s1 a i else ok (s1, a))
        ⦃ s' _ => RunVcpuInv st T s' ⦄ := by
      refine WP.spec_bind sa fun s1 hh1 => ?_
      have hR1 := hRV.rvSt hh1.2
      refine sig_if _ _ _ _ (fun _ => (WP.spec_ok _).2 hR1) (fun _ => ?_)
      step with obj.Tcb.state.spec
      refine sig_if _ _ _ _ (fun _ => ?_) (fun _ => (WP.spec_ok _).2 hR1)
      exact notification.kick_guest.rvi hA s1 a i hh1.1 hR1
    by_cases hb : b = true
    · rw [if_pos hb, if_pos hb]
      refine WP.spec_bind sa fun s1 hh1 => ?_
      rw [if_pos hb]
      exact (WP.spec_ok _).2 (hRV.rvSt hh1.2)
    rw [if_neg hb]
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
      have hiv : L.mem s (runVcpuA i) = 0#u64 := hRV.blocked hiT hbl
      obtain ⟨dq, dr, da⟩ := blocked_out h0 hiT (not_runnable_of_blocked hbl)
      refine WP.spec_bind (ipc.cancel_ipc.all s a i Q R h0 hiT hB hX hSg.sub) ?_
      rintro ⟨s1, a1⟩ ⟨h1, hB1, hX1, nb1, nr1, -, k1, -⟩
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
      have rv1 : L.mem s1 (runVcpuA i) = 0#u64 :=
        (k1.fld i hiT 3672#u64 (by simp) (by simp) (by simp) (by simp) (fun _ => ⟨by simp, by simp⟩)).trans hiv
      have R1 : RunVcpuInv st T s1 :=
        hRV.keep' (fun y hy => k1.fld y hy 3672#u64 (by simp) (by simp) (by simp) (by simp)
          (fun _ => ⟨by simp, by simp⟩)) fun y hy => by
          by_cases hyi : y = i
          · subst hyi; exact Or.inr hiv
          · exact Or.inl (k1.stf hy hyi)
      refine WP.spec_bind (sts_all s1 i _ Q R h1 hB1 hX1 hS1 hSg1 hiT not_blocked_running running_ne
        (Or.inr nb1) (hX1.noref hta nr1 (fun e => nb1 (by rw [e]; exact Or.inr (Or.inl rfl))))
        ⟨fun _ _ _ _ _ => runnable_running, fun _ _ _ => runnable_running, fun _ => runnable_running⟩) ?_
      rintro s2 ⟨h2, hB2, hX2, hS2, hSg2, st2, k2⟩
      have h2' : SchedQueuesInv st T Cs Ω H s2 Q R := h2.congrX empty_congr
      have dq2 : (L.mem s2 (inqA i) &&& sched.Q_QUEUED) = 0#u64 := by rw [k2.inqf hiT]; exact dq1
      have dr2 : (L.mem s2 (inqA i) &&& sched.Q_RELEASE) = 0#u64 := by rw [k2.inqf hiT]; exact dr1
      have da2 : L.actionW s2 ≠ i := by
        rcases k2.act with e | e
        · rw [e]; exact da1
        · rw [e]; exact fun e' => notT_small hT (by simp) (e' ▸ hiT)
      have rv2 : L.mem s2 (runVcpuA i) = 0#u64 :=
        (k2.fld i hiT 3672#u64 (by simp) (by simp) (by simp) (by simp) (fun _ => ⟨by simp, by simp⟩)).trans rv1
      have R2 : RunVcpuInv st T s2 :=
        R1.keep' (fun y hy => k2.fld y hy 3672#u64 (by simp) (by simp) (by simp) (by simp)
          (fun _ => ⟨by simp, by simp⟩)) fun y hy => by
          by_cases hyi : y = i
          · subst hyi; exact Or.inr rv1
          · exact Or.inl (k2.stf hy hyi)
      refine WP.spec_mono (signal_tail.rv hA s2 a1 i n badge Q R h2' hB2 hX2 hS2 hSg2 hiT hn dq2 dr2 da2
        (fun e => hB.idleNB (by rw [← k1.idleW, ← k2.idleW, e]; exact Or.inl hbl))
        (by rw [st2]; rintro (hb | hb); exact not_blocked_running hb; exact running_ne.1 hb) rv2) ?_
      rintro ⟨s', a'⟩ r'
      exact R2.rvSt r'
    · -- not receiving: the `RunningVM` branch (dead on AArch64) or active (and kicked)
      rw [if_neg hb]
      refine sig_if _ _ _ _ (fun hvm => ?_) (fun _ => OLD)
      refine WP.spec_bind (vcpu.signal_completes.never_spec s i) fun b1 hb1 => ?_
      refine sig_if _ _ _ _ (fun hb1t => by simp [hb1] at hb1t) (fun _ => OLD)
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
      have hdq := notification.ntfn_dequeue.inv s hd Q R h0 hdT (by simp) hbl
      rw [hbe] at hdq
      refine WP.spec_bind hdq ?_
      rintro s1 ⟨h1, f1, o1, n1, k1, c1, nc1⟩
      have tm1 : TmFr st T Cs Nt s s1 := TmFr.mk0 ⟨k1, fun y hy K a b c => f1 y hy K (by omega) c (by omega) (by omega),
        fun c hc o ho => nc1 c hc o (by omega) (by omega), fun n' hn' => o1 _ (hSg.sub _ (hX.1.ntB n' hn').2)⟩
      obtain ⟨hB1, hX1, hS1, hSg1, ea1, ec1, ei1⟩ := frame_bx h0 hB hX hS hSg f1 o1 n1 k1 tm1
      have R1 : RunVcpuInv st T s1 := hRV.rvSt (RvSt.of_fld f1)
      have st1 : L.mem s1 (stA hd) = sched.TS_BLOCKED_ON_NTFN := by
        rw [stA_eq, f1 hd hdT _ (by simp) (by simp) (by simp) (by simp), ← stA_eq]; exact hds
      have iq1 : L.mem s1 (inqA hd) = L.mem s (inqA hd) := by
        rw [inqA_eq]; exact f1 hd hdT _ (by simp) (by simp) (by simp) (by simp)
      have rv1 : L.mem s1 (runVcpuA hd) = 0#u64 :=
        (f1 hd hdT 3672#u64 (by simp) (by simp) (by simp) (by simp)).trans (hRV.blocked hdT hbl)
      obtain ⟨-, -, r3, -, r6⟩ := ts_vals
      refine WP.spec_bind (sts_all s1 hd _ Q R h1 hB1 hX1 hS1 hSg1 hdT not_blocked_running running_ne
        (Or.inl (Or.inr rfl)) (hX1.noref hta (by rw [st1]; exact blocked_ne_reply (Or.inr (Or.inr rfl)))
          (by rw [st1, r3, r6]; decide))
        ⟨fun _ _ _ _ _ => runnable_running, fun _ _ _ => runnable_running, fun _ => runnable_running⟩) ?_
      rintro s2 ⟨h2, hB2, hX2, hS2, hSg2, st2, k2⟩
      have h2' : SchedQueuesInv st T Cs Ω H s2 Q R := h2.congrX empty_congr'
      have dq2 : (L.mem s2 (inqA hd) &&& sched.Q_QUEUED) = 0#u64 := by rw [k2.inqf hdT, iq1]; exact dq
      have dr2 : (L.mem s2 (inqA hd) &&& sched.Q_RELEASE) = 0#u64 := by rw [k2.inqf hdT, iq1]; exact dr
      have da2 : L.actionW s2 ≠ hd := by
        rcases k2.act with e | e
        · rw [e, ea1]; exact da
        · rw [e]; exact fun e' => notT_small hT (by simp) (e' ▸ hdT)
      have rv2 : L.mem s2 (runVcpuA hd) = 0#u64 :=
        (k2.fld hd hdT 3672#u64 (by simp) (by simp) (by simp) (by simp) (fun _ => ⟨by simp, by simp⟩)).trans rv1
      have R2 : RunVcpuInv st T s2 :=
        R1.keep' (fun y hy => k2.fld y hy 3672#u64 (by simp) (by simp) (by simp) (by simp)
          (fun _ => ⟨by simp, by simp⟩)) fun y hy => by
          by_cases hyi : y = hd
          · rw [hyi]; exact Or.inr rv1
          · exact Or.inl (k2.stf hy hyi)
      refine WP.spec_mono (signal_tail.rv hA s2 a hd n badge Q R h2' hB2 hX2 hS2 hSg2 hdT hn dq2 dr2 da2
        (fun e => hB.idleNB (by rw [← ei1, ← k2.idleW, e]; exact Or.inl hbl))
        (by rw [st2]; rintro (hb | hb); exact not_blocked_running hb; exact running_ne.1 hb) rv2) ?_
      rintro ⟨s', a'⟩ r'
      exact R2.rvSt r'
    · -- an active notification
      step with obj.Ntfn.badge.val as ⟨i, ei⟩
      simp only [lift, Aeneas.Std.bind_ok]
      refine WP.spec_bind (obj.Ntfn.set_badge.wr s n _) fun s1 e1 => ?_
      subst e1
      exact (WP.spec_ok _).2 (hRV.rvSt (RvSt.wr_out hT (h0.omega _ (hSg.sub _ (hX.1.ntB n hn).1))))

/-! ## `timer::fire` without `RvKeep` -/

/-- `timer.fire_loop.tinv` with [J] `RvKeep` discharged (`timer.remove.rvi`, `send_signal.rvi`; the loop's
notifications are typed by `hNt`). -/
theorem timer.fire_loop.tinv_rv {U : Set U64} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A) (now i : U64)
    (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hBA : BufAt st T Cs H Sg Scs Z U s) (hRV : RunVcpuInv st T s) :
    timer.fire_loop st ar s a now i ⦃ s' _ => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ IbFr (L := L) T s s' ∧
      RunVcpuInv st T s' ⦄ := by
  obtain ⟨IKr, IKs, IKp⟩ := IK T Cs Ω H Sg Rp Scs Nt Z Ac U
  unfold timer.fire_loop
  apply loop.spec_decr_nat (measure := fun x => 32 - x.2.2.val)
    (inv := fun x => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac x.1 ∧ IbFr (L := L) T s x.1 ∧ RunVcpuInv st T x.1)
  · rintro ⟨s1, a1, i1⟩ ⟨h1, f1, r1⟩
    simp only at h1 f1 r1
    unfold timer.fire_loop.body
    dsimp only
    split
    · rename_i hi
      have hi32 : i1.val < 32 := by simpa using hi
      step with LawfulStore.cur_cpu_spec as ⟨c, ec⟩
      step with obj.node_get.spec as ⟨t, et⟩
      step with obj.Tcb.is_null.spec as ⟨b, eb⟩
      split
      · exact (WP.spec_ok _).2 ⟨h1, f1, r1⟩
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
      · exact (WP.spec_ok _).2 ⟨hI1, f1, r1⟩
      step with obj.Tcb.timer_badge.val as ⟨bd, ebd⟩
      refine WP.spec_bind (WP.spec_and (WP.spec_and (timer.remove.tinv s1 t hI1 htT) (IKr s1 t hI1 htT))
        (timer.remove.rvi s1 t hI1 r1 htT)) fun s2 hh2 => ?_
      obtain ⟨⟨h2, f2⟩, r2⟩ := hh2
      have f12 := f1.trans f2
      step with obj.Tcb.bound_ntfn.val as ⟨n, en⟩
      refine WP.spec_bind (Pₘ := fun r : S × A => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧ IbFr (L := L) T s r.1 ∧
          RunVcpuInv st T r.1)
        ?_ ?_
      · split
        · rename_i hn0
          have hn0' : L.mem s2 (boundA t) ≠ 0#u64 := by rw [← en]; exact bne_ne hn0
          have hn : n ∈ Nt := by rw [en]; exact h2.2.2.1.2.2.bnd t htT hn0'
          have hb2 := hBA.of_fr f12
          exact WP.spec_mono (WP.spec_and (WP.spec_and
            (notification.send_signal.tinv hA s2 a1 n bd h2 hn (hNt n hn) hb2.1 hb2.2 r2)
            (IKs s2 a1 n bd h2 hn (hNt n hn) hb2)) (notification.send_signal.rvi hA s2 a1 n bd h2 hn (hNt n hn) r2))
            fun r hr => by
            obtain ⟨s', a'⟩ := r; simp only [WP.uncurry'_pair] at hr ⊢; exact ⟨hr.1.1, f12.trans hr.1.2, hr.2⟩
        · exact (WP.spec_ok _).2 ⟨h2, f12, r2⟩
      rintro ⟨s3, a3⟩ ⟨h3, f3, r3⟩
      simp only at h3 f3 r3
      try simp only [WP.uncurry'_pair]
      step with LawfulStore.cur_cpu_spec as ⟨c3, ec3⟩
      step with obj.node_set.spec as ⟨s4, es4⟩
      step as ⟨i4, ei4⟩
      try simp only [WP.spec_ok]
      subst es4 ec3
      exact ⟨reprogram.tinv h3, f3.trans (IKp s3 1#u64 h3), reprogram.rvi h3 r3, by omega⟩
    · exact (WP.spec_ok _).2 ⟨h1, f1, r1⟩
  · exact ⟨h, IbFr.refl s, hRV⟩

/-- `timer.fire.tinv` without [J] `RvKeep`. -/
theorem timer.fire.tinv_rv {U : Set U64} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A)
    (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hBA : BufAt st T Cs H Sg Scs Z U s) (hRV : RunVcpuInv st T s) :
    timer.fire st ar s a ⦃ s' _ => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ IbFr (L := L) T s s' ∧
      RunVcpuInv st T s' ⦄ := by
  unfold timer.fire
  refine WP.spec_bind (L.cur_cpu_spec s) fun c _ => ?_
  refine WP.spec_bind (obj.node_get.spec s c _) fun now _ => ?_
  exact timer.fire_loop.tinv_rv hA IK hNt s a now 0#u64 h hBA hRV

/-- `sched.schedule.tinv` without [J] `RvKeep`. -/
theorem sched.schedule.tinv_rv {U : Set U64} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hS : SCsOK st T Ω Sg Scs Z Ac s)
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hSg : SgOK st Ω Sg s) (hBA : BufAt st T Cs H Sg Scs Z U s)
    (hRV : RunVcpuInv st T s) :
    sched.schedule st ar s a ⦃ s' _ => (∃ Q' R', SchedQueuesInv st T Cs Ω H s' Q' R') ∧ BoundInv st T Ac s' ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧ SCsOK st T Ω Sg Scs Z Ac s' ∧ TimerOK st T Cs s' ∧ L.cscW s' ∈ Ac ∧
      L.actionW s' = 0#u64 ∧ L.cscW s' = L.mem s' (scA (L.curW s')) ⦄ := by
  refine WP.spec_mono (sched.schedule.inv hA s a Q R h hB hS hX
    (WP.spec_mono (timer.fire.tinv_rv hA IK hNt s a (BlkOK.tinv ⟨⟨Q, R, h⟩, hB, hX, hS, hSg⟩) hBA hRV)
      fun r hr => by
      obtain ⟨s', a'⟩ := r
      simp only [WP.uncurry'_pair] at hr ⊢
      exact ⟨hr.1.1, hr.1.2.1, hr.1.2.2.2.1, hr.1.2.2.1⟩)) fun r hr => ?_
  obtain ⟨s', a'⟩ := r
  simp only [WP.uncurry'_pair] at hr ⊢
  exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.1.2.2.tm, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2⟩

/-- `sched.schedule.entry` without [J] `RvKeep`. -/
theorem sched.schedule.entry_rv {U : Set U64} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hS : SCsOK st T Ω Sg Scs Z Ac s)
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hSg : SgOK st Ω Sg s) (hBA : BufAt st T Cs H Sg Scs Z U s)
    (hRV : RunVcpuInv st T s) :
    sched.schedule st ar s a ⦃ s' _ => EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ :=
  WP.spec_mono (sched.schedule.tinv_rv hA IK hNt s a Q R h hB hS hX hSg hBA hRV) fun r hr => by
    obtain ⟨s', a'⟩ := r
    simp only [WP.uncurry'_pair] at hr ⊢
    obtain ⟨⟨Q', R', h'⟩, hB', hX', hS', hT', hA', ha', hc'⟩ := hr
    refine ⟨⟨Q', R', h'⟩, hB', hX', hS', hT', hA', fun e => ?_, fun _ => hc'⟩
    rw [ha'] at e
    have e' := e.symm
    unfold LawfulStore.curW at e'
    exact (h'.tcbs _ h'.curT).ne0 (by rw [e']; rfl)

end

end Fl4ProofsA64.P1
