/-
P1 (aarch64): **[J] `W7.R.FinRvRest` discharged for the SchedContext and Thread kinds**; what stays named is the
narrower **[J] `W7.R.FinRvRest3`** (reply, VCPU, Stage-2 and device-frame kinds).

QueueFinRv's [J] `FinRvRest` says the finalisation of a `FinRvRestKind` cap, from a `Cur0` state of the deletion
where `RunVcpuInv` holds, ends in a `RunVcpuInv` state. Proved here:
* **SchedContext** (`fin_sc.rvst`): no step writes a `STATE` or `RUN_VCPU` word. `unbind_all_tcbs` is the stall
  (it keeps every TCB field, `remote_tcb_stall.all`) and `unbind_tcb` (`unbind_tcb.blkR`'s `RvSt`);
  `unbind_ntfn.rvst` (QueueFinRv); `unbind_reply.rvst` (a reply `NEXT` word and the SC's `REPLY` word, words of
  `Ω`); `complete_yield_to.rvst` (QueueFinal); the `REFILL_MAX` / `SPORADIC` clears (words of `Ω`).
* **Thread** (`fin_thread.rvi`): the stall keeps every TCB field; `vcpu::detach` of a native TCB writes the run
  VCPU's `RUN_CALLER` user word and clears `RUN_VCPU p` (`vcpu.detach.w7`), after which `p` runs no VCPU and
  every other `STATE` / `RUN_VCPU` word is kept (`RunVcpuInv.detach7`); `finThrRest.rvi`: the `RvSt` frames of
  `unbind_notification`, `timer.remove`, `unbind_tcb`, `complete_yield_to`, then **`sched.suspend.rvi`**
  (`cancel_ipc` is a `KeepT p` step, the `FAULT_IP` copy a TCB field, `dequeue` / `release_remove` write queue
  links only (`field_qfoot`), `cancel_yield_to` a word of `Ω` and `YIELD_TO`, and `set_thread_state p INACTIVE`
  with `RUN_VCPU p = 0`: `RunVcpuInv.keepT`), and **`objects.debug_remove.rvst`** (debug-list words only).
  Uses the [P] `rcw` field of the `rv`-free placement `R.DelPlaceAt` (unchanged).
* `finRvRest_of3` (`R.DelPlaceAt` + [J] `FinRvRest3` ⇒ [J] `FinRvRest`), `FinGapsAt3` / `FinGaps3`,
  `FinGapsAt3.to2`, `delGaps_of_gaps3`, **`decGap_cnode_rv3`**, **`decGap_thread3`**.

Named premises: **[J] `W7.R.FinRvRest3`** (new, strictly narrower than [J] `W7.R.FinRvRest`, which it replaces in
the `3` forms): the same Hoare triple for the reply, VCPU, Stage-2 and device-frame kinds only. The `arch` gap
(`W7.FinGapsAt.arch`) and the placements ([P] `R.DelPlaceAt`, its `rcw` included) are unchanged. No existing
statement changed.
-/
import Fl4ProofsA64.P1.QueueFinRv
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}

/-! ## The SC kind -/

theorem schedcontext.unbind_reply.rvst (s : S) (c : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hc : c ≠ 0#u64 → c ∈ Scs) :
    schedcontext.unbind_reply st s c ⦃ s' => RvSt st T s s' ⦄ := by
  unfold schedcontext.unbind_reply
  step with obj.Sc.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 (RvSt.refl _)
  rename_i hb
  have hcS : c ∈ Scs := hc (fun e => hb (by rw [eb, e]; rfl))
  refine WP.spec_bind (obj.Sc.reply.val s c) fun i ei => ?_
  split
  · rename_i hi
    have hiR : i ∈ Rp := by rw [ei]; exact h.2.2.1.2.1.screp c hcS (by rw [← ei]; simpa using hi)
    refine WP.spec_bind (obj.Reply.set_next.val0 s i 0#u64) fun s1 e1 => ?_
    rw [zero_link] at e1
    subst e1
    obtain ⟨h1, -⟩ := rnext_zero_all h hiR
    refine WP.spec_mono (obj.Sc.set_reply.spec _ c 0#u64) fun s2 e2 => ?_
    subst e2
    have hO := h.2.2.1.1
    have hsub := h.2.2.2.2.sub
    have q0 := h.1.choose_spec.choose_spec
    have q1 := h1.1.choose_spec.choose_spec
    exact (RvSt.wr_out q0.tcbs (q0.omega _ (hsub _ (hO.nextW hiR)))).trans
      (RvSt.wr_out q1.tcbs (q1.omega _ (hsub _ (hO.repW c hcS))))
  · exact (WP.spec_ok _).2 (RvSt.refl _)

theorem schedcontext.unbind_all_tcbs.rvst {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (p : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hp : p ∈ Scs) (hp0 : p ≠ 0#u64)
    (hna : L.mem s (scTcbA p) ≠ 0#u64 → L.actionW s ≠ L.mem s (scTcbA p))
    (hidle : L.mem s (scTcbA p) ≠ 0#u64 → L.idleW s ≠ L.mem s (scTcbA p)) :
    schedcontext.unbind_all_tcbs st ar s a p ⦃ s' _ => RvSt st T s s' ⦄ := by
  obtain ⟨⟨Q0, R0, hq0⟩, hb0, hx0, hs0, hg0⟩ := id h
  unfold schedcontext.unbind_all_tcbs
  step with obj.Sc.tcb.spec as ⟨i, ei⟩
  split
  · refine WP.spec_bind (WP.spec_and (smp.remote_tcb_stall.blkS hA s a i p h hp)
      (smp.remote_tcb_stall.all hA s a i hq0 hb0 hx0 hs0 hg0)) ?_
    rintro ⟨s1, a1⟩ ⟨⟨h1, f1, ea1, ei1, k1⟩, _, _, _, _, _, _, _, _, _, keep, _⟩
    try simp only [WP.uncurry'_pair]
    have r1 : RvSt st T s s1 := fun y hy =>
      ⟨by rw [stA_eq]; exact keep y hy _ (by simp) (by simp), keep y hy 3672#u64 (by simp) (by simp)⟩
    refine WP.spec_bind (schedcontext.unbind_tcb.blkR s1 p h1 hp hp0 (fun h0 => by
        rw [k1.1] at h0 ⊢; rw [ea1]; exact hna h0)
      (fun h0 => by rw [k1.1] at h0 ⊢; rw [ei1]; exact hidle h0)) fun s2 hh2 => ?_
    obtain ⟨-, -, -, -, -, -, r2⟩ := hh2
    exact (WP.spec_ok _).2 (r1.trans r2)
  · exact (WP.spec_ok _).2 (RvSt.refl _)

/-- **The SC kind keeps every `STATE` and `RUN_VCPU` word.** -/
theorem fin_sc.rvst {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (p x : U64)
    (fin : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hp : p ∈ Scs) (hp0 : p ≠ 0#u64)
    (hna : L.mem s (scTcbA p) ≠ 0#u64 → L.actionW s ≠ L.mem s (scTcbA p))
    (hidle : L.mem s (scTcbA p) ≠ 0#u64 → L.idleW s ≠ L.mem s (scTcbA p)) :
    objects.finalise_cap_object st ar s a (.SchedContext p x) fin ⦃ r => RvSt st T s r.2.1 ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  split
  swap
  · exact (WP.spec_ok _).2 (RvSt.refl _)
  refine WP.spec_bind (WP.spec_and (schedcontext.unbind_all_tcbs.blk hA s a p h hp hp0 hna hidle)
    (schedcontext.unbind_all_tcbs.rvst hA s a p h hp hp0 hna hidle)) ?_
  rintro ⟨s1, a1⟩ ⟨⟨h1, -⟩, c1⟩
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (WP.spec_and (schedcontext.unbind_ntfn.blk s1 p h1 fun _ => hp)
    (schedcontext.unbind_ntfn.rvst s1 p h1 fun _ => hp)) fun s2 ⟨⟨h2, _⟩, c2⟩ => ?_
  refine WP.spec_bind (WP.spec_and (schedcontext.unbind_reply.blk s2 p p h2 (fun _ => hp) hp)
    (schedcontext.unbind_reply.rvst s2 p h2 (fun _ => hp))) fun s3 ⟨⟨h3, _⟩, c3⟩ => ?_
  have c13 := (c1.trans c2).trans c3
  refine WP.spec_bind (obj.Sc.yield_from.val s3 p) fun yf eyf => ?_
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧ RvSt st T s r.1) ?_ ?_
  · split
    · exact (WP.spec_ok _).2 ⟨h3, c13⟩
    · have hy : yf ≠ 0#u64 → yf ∈ T := fun hy0 => by
        rw [eyf]; exact h3.2.2.1.2.2.yt.2.2 p hp (by rw [← eyf]; exact hy0)
      refine WP.spec_mono (WP.spec_and (schedcontext.complete_yield_to.blk hA s3 a1 yf h3 hy)
        (schedcontext.complete_yield_to.rvst hA s3 a1 yf h3 hy)) ?_
      rintro ⟨s4, a4⟩ ⟨⟨h4, -⟩, c4⟩
      exact ⟨h4, c13.trans c4⟩
  rintro ⟨s4, a2⟩ ⟨h4, c4⟩
  try simp only [WP.uncurry'_pair]
  have q4 := h4.1.choose_spec.choose_spec
  have hO4 := h4.2.2.1.1
  have hsub4 := h4.2.2.2.2.sub
  refine WP.spec_bind (obj.Sc.set_refill_max.spec s4 p 0#u64) fun s5 e5 => ?_
  subst e5
  have q5 := (omega_wr (v := 0#u64) q4 (hsub4 _ (hO4.mxW p hp))).1
  refine WP.spec_bind (obj.Sc.set_sporadic.wr _ p 0#u64) fun s6 e6 => ?_
  subst e6
  exact (WP.spec_ok _).2 ((c4.trans (RvSt.wr_out q4.tcbs (q4.omega _ (hsub4 _ (hO4.mxW p hp))))).trans
    (RvSt.wr_out q5.tcbs (q5.omega _ (spor_omega hO4 hp))))

/-! ## The thread kind -/

/-- `debug_remove` writes debug-list words only: every `STATE` and `RUN_VCPU` word is kept. -/
theorem objects.debug_remove.rvst (s : S) (t : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T) :
    objects.debug_remove st s t ⦃ s' => RvSt st T s s' ⦄ := by
  have h0 := h.1.choose_spec.choose_spec
  have hT := h0.tcbs
  refine WP.spec_mono (objects.debug_remove.frame s t hT h0.nodes (XInv.dbg h.2.2.1) (h0.aff t ht) ht)
    fun s' hh => ?_
  have w := hh.1
  have nd : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3576 → K.val ≠ 3584 →
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := by
    intro y hy K hK hK8 h1 h2
    refine w.2.2 _ (field_aligned (hT y hy) hK hK8) ?_
    rintro (⟨y', hy', e | e⟩ | ⟨c, hc, e⟩)
    · exact field_ne (hT y hy) (hT y' hy') hK (by simp) (fun _ => by simpa using h1) e
    · exact field_ne (hT y hy) (hT y' hy') hK (by simp) (fun _ => by simpa using h2) e
    · exact node_ne_field (h0.nodes _ hc) (by rw [debug_val]; omega) hy (hT y hy) hK e.symm
  exact fun y hy => ⟨by rw [stA_eq]; exact nd y hy _ (by simp) (by simp) (by simp) (by simp),
    nd y hy 3672#u64 (by simp) (by simp) (by simp) (by simp)⟩

/-- **`suspend` of a thread running no VCPU keeps [J] `RunVcpuInv`** (`sched.suspend.keepF`'s text). -/
theorem sched.suspend.rvi {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (t : obj.Tcb)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T)
    (hrv : L.mem s (runVcpuA t) = 0#u64) (hRV : RunVcpuInv st T s) :
    sched.suspend st ar s a t ⦃ s' _ => RunVcpuInv st T s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hsub := hSg.sub
  have hT := h0.tcbs
  have hta := hT t ht
  obtain ⟨hO, hR, hE⟩ := hX
  have mv : ∀ {s₁ s₂ : S}, (RunVcpuInv st T s₁ ∧ L.mem s₁ (runVcpuA t) = 0#u64) → RvSt st T s₁ s₂ →
      RunVcpuInv st T s₂ ∧ L.mem s₂ (runVcpuA t) = 0#u64 :=
    fun hh f => ⟨hh.1.rvSt f, (f t ht).2.trans hh.2⟩
  unfold sched.suspend
  refine WP.spec_bind (vcpu.cancel_run.idle s a t hrv) ?_
  rintro ⟨s0, a0⟩ ⟨e0, e1⟩
  subst s0; subst a0
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (ipc.cancel_ipc.all s a t Q R h0 ht hB ⟨hO, hR, hE⟩ hsub) ?_
  rintro ⟨s1, a1⟩ ⟨h1, -, hX1, -, -, -, k1, -⟩
  try simp only [WP.uncurry'_pair]
  have R1 : RunVcpuInv st T s1 ∧ L.mem s1 (runVcpuA t) = 0#u64 :=
    ⟨hRV.keepT k1 (Or.inr hrv),
      (k1.fld t ht 3672#u64 (by simp) (by simp) (by simp) (by simp) (fun _ => ⟨by simp, by simp⟩)).trans hrv⟩
  have F1 : L.mem s1 (yieldA t) = L.mem s (yieldA t) :=
    k1.fld t ht 3472#u64 (by simp) (by simp) (by simp) (by simp) (fun _ => ⟨by simp, by simp⟩)
  step with obj.Tcb.state.spec as ⟨i, i_post⟩
  refine WP.spec_bind (Pₘ := fun s2 => SchedQueuesInv st T Cs Ω H s2 Q R ∧
      L.mem s2 (yieldA t) = L.mem s (yieldA t) ∧
      (RunVcpuInv st T s2 ∧ L.mem s2 (runVcpuA t) = 0#u64)) ?_ ?_
  · split
    · step with obj.Tcb.reg.spec as ⟨ip⟩
      refine WP.spec_mono (obj.Tcb.set_reg.fault_ip s1 t ip hta) fun s2 e => ?_
      subst e
      obtain ⟨h2, f2, -⟩ := field_wr_keep (K := 528#u64) (v := ip) h1 ht (by simp) (by simp) (by simp)
      exact ⟨h2, (f2 3472#u64 (by simp) (by simp) (by simp)).trans F1,
        mv R1 (RvSt.wr_field hT ht (by simp) (by simp) (by simp) (by simp))⟩
    · exact (WP.spec_ok _).2 ⟨h1, F1, R1⟩
  rintro s2 ⟨h2, F2, R2⟩
  have hc2 := h2.aff t ht
  have hp2 := h2.prio t ht
  have hW2 : ∀ w ∈ Q (L.mem s2 (affA t)) (L.mem s2 (prioA t)), w ∈ T := fun w hw => h2.memT hc2 hp2 hw
  refine WP.spec_bind (WP.spec_and (sched.dequeue.inv s2 t Q R h2 ht)
    (sched.dequeue.foot s2 t _ hT ht hp2 (h2.nodes _ hc2) (h2.nodes _ h2.cur) ((h2.ready _ hc2).1.rel _ hp2)
      (h2.queued t ht).1)) ?_
  rintro s3 ⟨h3, hw3, -⟩
  have F3 : L.mem s3 (yieldA t) = L.mem s (yieldA t) :=
    (field_qfoot hT hW2 (h2.nodes _ hc2) (h2.nodes _ h2.cur) ht hw3 ht (K := 3472#u64) (by simp) (by simp)
      (by simp) (fun _ => by simp)).trans F2
  have q3 : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      (K.val ≠ 3480 ∧ K.val ≠ 3488 ∧ K.val ≠ 3496 ∧ K.val ≠ 3504) → K.val ≠ 3592 →
      L.mem s3 (core.num.U64.wrapping_add y K) = L.mem s2 (core.num.U64.wrapping_add y K) :=
    fun y hy K a b c d => field_qfoot hT hW2 (h2.nodes _ hc2) (h2.nodes _ h2.cur) ht hw3 hy a b c (fun _ => d)
  have R3 := mv R2 fun y hy =>
    ⟨by rw [stA_eq]; exact q3 y hy _ (by simp) (by simp) (by simp) (by simp),
     q3 y hy 3672#u64 (by simp) (by simp) (by simp) (by simp)⟩
  have hc3 := h3.aff t ht
  have hW3 : ∀ w ∈ R (L.mem s3 (affA t)), w ∈ T := fun w hw => h3.memTR hc3 hw
  refine WP.spec_bind (WP.spec_and (sched.release_remove.inv s3 t _ R h3 ht)
    (sched.release_remove.foot s3 t _ hT ht (h3.nodes _ hc3) (h3.nodes _ h3.cur) (h3.release _ hc3)
      (h3.released t ht).1)) ?_
  rintro s4 ⟨h4, hw4, -⟩
  have F4 : L.mem s4 (yieldA t) = L.mem s (yieldA t) :=
    (field_qfoot hT hW3 (h3.nodes _ hc3) (h3.nodes _ h3.cur) ht hw4 ht (K := 3472#u64) (by simp) (by simp)
      (by simp) (fun _ => by simp)).trans F3
  have q4 : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      (K.val ≠ 3480 ∧ K.val ≠ 3488 ∧ K.val ≠ 3496 ∧ K.val ≠ 3504) → K.val ≠ 3592 →
      L.mem s4 (core.num.U64.wrapping_add y K) = L.mem s3 (core.num.U64.wrapping_add y K) :=
    fun y hy K a b c d => field_qfoot hT hW3 (h3.nodes _ hc3) (h3.nodes _ h3.cur) ht hw4 hy a b c (fun _ => d)
  have R4 := mv R3 fun y hy =>
    ⟨by rw [stA_eq]; exact q4 y hy _ (by simp) (by simp) (by simp) (by simp),
     q4 y hy 3672#u64 (by simp) (by simp) (by simp) (by simp)⟩
  refine WP.spec_bind (Pₘ := fun s5 => ∃ Q5 R5, SchedQueuesInv st T Cs Ω H s5 Q5 R5 ∧
      (RunVcpuInv st T s5 ∧ L.mem s5 (runVcpuA t) = 0#u64)) ?_ ?_
  · unfold schedcontext.cancel_yield_to
    step with obj.Tcb.is_null.spec as ⟨b, b_post⟩
    split
    · rename_i hb
      have e0 : t = 0#u64 := by rw [b_post] at hb; simpa using hb
      exact absurd (show t.val = 0 by rw [e0]; rfl) hta.ne0
    step with obj.Tcb.yield_to.spec as ⟨yt, yt_post⟩
    split
    · rename_i _ hy
      have hyS : yt ∈ Scs := by
        rw [yt_post, F4]; exact hE.yt.2.1 t ht (by rw [← F4, ← yt_post]; simpa using hy)
      step with obj.Sc.set_yield_from.spec as ⟨s5, s5_post⟩
      subst s5_post
      have hm := hsub _ (hO.syW yt hyS)
      obtain ⟨h5, -, -⟩ := omega_wr (v := 0#u64) h4 hm
      refine WP.spec_mono (obj.Tcb.set_yield_to.spec _ t 0#u64) fun s6 e => ?_
      subst e
      obtain ⟨h6, -, -⟩ := field_wr_keep (K := 3472#u64) (v := 0#u64) h5 ht (by simp) (by simp) (by simp)
      refine ⟨_, _, h6, ?_⟩
      try rw [show yieldA t = core.num.U64.wrapping_add t 3472#u64 from rfl]
      exact mv (mv R4 (RvSt.wr_out hT (h4.omega _ hm)))
        (RvSt.wr_field hT ht (by simp) (by simp) (by simp) (by simp))
    · exact (WP.spec_ok _).2 ⟨_, _, h4, R4⟩
  rintro s5 ⟨Q5, R5, h5, R5'⟩
  refine WP.spec_bind (sched.set_thread_state.state s5 t sched.TS_INACTIVE Q5 R5 h5 ht hO.ksb hsub) ?_
  rintro s6 ⟨-, k6⟩
  exact (WP.spec_ok _).2 (R5'.1.keepT k6 (Or.inr R5'.2))

/-- After `vcpu.detach.w7`: `RUN_VCPU p` is 0 and every other `STATE` / `RUN_VCPU` word is kept. -/
theorem RunVcpuInv.detach7 {s s' : S} {p : U64} (hRV : RunVcpuInv st T s) (rv : L.mem s' (runVcpuA p) = 0#u64)
    (fl : ∀ y ∈ T, ∀ K : U64, 3328 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → (y = p → K.val ≠ 3672) →
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) :
    RunVcpuInv st T s' := by
  intro y hy hne
  by_cases e : y = p
  · subst e; exact absurd rv hne
  · have e1 : L.mem s' (runVcpuA y) = L.mem s (runVcpuA y) :=
      fl y hy 3672#u64 (by simp) (by simp) (by simp) (fun h => absurd h e)
    have e2 : L.mem s' (stA y) = L.mem s (stA y) := by
      rw [stA_eq]; exact fl y hy _ (by simp) (by simp) (by simp) (fun _ => by simp)
    rw [e2]; exact hRV y hy (by rw [← e1]; exact hne)

/-- `finThrRest` (from a state where `p` runs no VCPU) keeps [J] `RunVcpuInv`. -/
theorem finThrRest.rvi {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s1 : S) (a1 : A) (p : U64)
    (h1 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s1) (hp : p ∈ T) (hna : L.actionW s1 ≠ p)
    (hidle : L.idleW s1 ≠ p) (rv1 : L.mem s1 (runVcpuA p) = 0#u64) (hRV : RunVcpuInv st T s1) :
    finThrRest st ar s1 a1 p ⦃ r => RunVcpuInv st T r.2.1 ⦄ := by
  unfold finThrRest
  refine WP.spec_bind (WP.spec_and (notification.unbind_notification.blkF s1 p h1 hp)
    (notification.unbind_notification.rvst s1 p h1 hp)) fun s2 hh2 => ?_
  obtain ⟨⟨h2, f2, n2⟩, r2⟩ := hh2
  refine WP.spec_bind (timer.remove.tf (s0 := s2) s2 p (TF.start h2) hp) fun s3 ⟨h3, f3, n3, k3, _⟩ => ?_
  have r3 : RvSt st T s2 s3 := fun y hy =>
    ⟨by rw [stA_eq]; exact k3 y hy _ (by simp) (by simp) (Or.inl (by simp)),
     k3 y hy 3672#u64 (by simp) (by simp) (Or.inr (by simp))⟩
  have rv3 : L.mem s3 (runVcpuA p) = 0#u64 := (r3 p hp).2.trans ((r2 p hp).2.trans rv1)
  have ea3 : L.actionW s3 = L.actionW s1 := by rw [n3.1, n2.1]
  have ei3 : L.idleW s3 = L.idleW s1 := by rw [n3.2.1, n2.2.1]
  have r13 : RvSt st T s1 s3 := r2.trans r3
  step with obj.Tcb.sc.spec as ⟨i, ei⟩
  step with obj.Sc.is_null.spec as ⟨b, eb⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧
      L.actionW r.1 ≠ p ∧ L.mem r.1 (runVcpuA p) = 0#u64 ∧ RvSt st T s1 r.1) ?_ ?_
  · split
    · exact (WP.spec_ok _).2 ⟨h3, by rw [ea3]; exact hna, rv3, r13⟩
    rename_i hb
    have hi0 : i ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    obtain ⟨hiS, hit, -⟩ := h3.2.2.1.2.2.bound p hp (by rw [← ei]; exact hi0)
    rw [← ei] at hiS hit
    refine WP.spec_bind (schedcontext.unbind_tcb.blkR s3 i h3 hiS hi0 (fun _ => by rw [hit, ea3]; exact hna)
      (fun _ => by rw [hit, ei3]; exact hidle)) fun s5 hh5 => ?_
    obtain ⟨h5, f5, ea5, -, -, -, r5⟩ := hh5
    have rv5 : L.mem s5 (runVcpuA p) = 0#u64 := (r5 p hp).2.trans rv3
    have na5 : L.actionW s5 ≠ p := by
      rcases ea5 with e | e
      · rw [e, ea3]; exact hna
      · rw [e]; exact fun e' => notT_small h5.1.choose_spec.choose_spec.tcbs (by simp) (e' ▸ hp)
    step with obj.Sc.yield_from.val as ⟨y, ey⟩
    step with obj.Tcb.is_null.spec as ⟨b1, eb1⟩
    split
    · exact (WP.spec_ok _).2 ⟨h5, na5, rv5, r13.trans r5⟩
    · have hiS5 : i ∈ Scs := hiS
      have hyy : y ≠ 0#u64 → y ∈ T := fun hy0 => by
        rw [ey]; exact h5.2.2.1.2.2.yt.2.2 i hiS5 (by rw [← ey]; exact hy0)
      refine WP.spec_mono (WP.spec_and (schedcontext.complete_yield_to.blk hA s5 a1 y h5 hyy)
        (schedcontext.complete_yield_to.rvst hA s5 a1 y h5 hyy)) ?_
      rintro ⟨s6, a6⟩ ⟨⟨h6, f6, n6⟩, r6⟩
      exact ⟨h6, by rw [n6.1]; exact na5, (r6 p hp).2.trans rv5, (r13.trans r5).trans r6⟩
  rintro ⟨s4, a2⟩ ⟨h4, na4, rv4, r4⟩
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (WP.spec_and (sched.suspend.blk s4 a2 p h4 hp na4 rv4)
    (sched.suspend.rvi s4 a2 p h4 hp rv4 (hRV.rvSt r4))) ?_
  rintro ⟨s5, a3⟩ ⟨⟨h5, -⟩, R5⟩
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (objects.debug_remove.rvst s5 p h5 hp) fun s6 r6 => ?_
  refine WP.spec_bind (hA.fpu_release a3 p) fun a4 _ => ?_
  refine WP.spec_bind (P0.obj.Tcb.slot.p0 p _) fun s7 _ => ?_
  exact (WP.spec_ok _).2 (R5.rvSt r6)

/-- **`finalise_cap` of a thread cap on AArch64 keeps [J] `RunVcpuInv`** (an `ARMVCPURun` possibly in flight;
its `RUN_CALLER` word a user word, `hrc`). -/
theorem fin_thread.rvi {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (p : U64)
    (fin : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hp : p ∈ T) (hna : L.actionW s ≠ p)
    (hidle : L.idleW s ≠ p)
    (hv0 : L.mem s (core.num.U64.wrapping_add p 3664#u64) = 0#u64)
    (hrc : L.mem s (runVcpuA p) ≠ 0#u64 →
      UserW st T Cs Ω H s (core.num.U64.wrapping_add (L.mem s (runVcpuA p)) vcpu.RUN_CALLER))
    (hRV : RunVcpuInv st T s) :
    objects.finalise_cap_object st ar s a (.Thread p) fin ⦃ r => RunVcpuInv st T r.2.1 ⦄ := by
  cases fin
  · unfold objects.finalise_cap_object
    dsimp only
    split
    · rename_i hf; exact absurd hf (by simp)
    · exact (WP.spec_ok _).2 hRV
  rw [fin_thread_split]
  have hStart := h
  obtain ⟨⟨Q0, R0, hq0⟩, hb0, hx0, hs0, hg0⟩ := hStart
  refine WP.spec_bind (WP.spec_and (smp.remote_tcb_stall.blk hA s a p h)
    (smp.remote_tcb_stall.all hA s a p hq0 hb0 hx0 hs0 hg0)) ?_
  rintro ⟨s1, a1⟩ ⟨⟨h1, f1, ea1, -, ei1⟩, _, _, _, _, _, _, _, _, _, keep, _⟩
  try simp only [WP.uncurry'_pair]
  have hv1 : L.mem s1 (core.num.U64.wrapping_add p 3664#u64) = 0#u64 := by
    rw [keep p hp 3664#u64 (by simp) (by simp)]; exact hv0
  have erv : L.mem s1 (runVcpuA p) = L.mem s (runVcpuA p) := keep p hp 3672#u64 (by simp) (by simp)
  have hrc1 : L.mem s1 (runVcpuA p) ≠ 0#u64 →
      UserW st T Cs Ω H s1 (core.num.U64.wrapping_add (L.mem s1 (runVcpuA p)) vcpu.RUN_CALLER) := fun h0 => by
    rw [erv] at h0 ⊢
    obtain ⟨u1, u2, u3⟩ := hrc h0
    exact ⟨u1.ksb f1.1, u2, u3⟩
  have R1 : RunVcpuInv st T s1 := hRV.rvSt fun y hy =>
    ⟨by rw [stA_eq]; exact keep y hy _ (by simp) (by simp), keep y hy 3672#u64 (by simp) (by simp)⟩
  refine WP.spec_bind (vcpu.detach.w7 s1 a1 p h1 hp hv1 hrc1) ?_
  rintro ⟨s2, a2⟩ ⟨-, h2, rv2, -, an2, -, fl2⟩
  dsimp only at h2 rv2 an2 fl2
  try simp only [WP.uncurry'_pair]
  exact finThrRest.rvi hA s2 a2 p h2 hp (by rw [an2.1, ea1]; exact hna) (by rw [an2.2.1, ei1]; exact hidle) rv2
    (R1.detach7 rv2 fl2)

namespace W7
namespace R

/-- The SC kind keeps [J] `RunVcpuInv`. -/
theorem finRv_sc {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s0 s : S} {a : A} {p x : U64}
    {fin : Bool} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hRV : RunVcpuInv st T s)
    (hpl : FinPl st Scs s (.SchedContext p x)) :
    objects.finalise_cap st ar s a (.SchedContext p x) fin false ⦃ r => RunVcpuInv st T r.2.1 ⦄ := by
  obtain ⟨hpS, hp0, hid⟩ := hpl.2 p x rfl
  obtain ⟨Ac', hb⟩ := h.bxi
  have hna : L.mem s (scTcbA p) ≠ 0#u64 → L.actionW s ≠ L.mem s (scTcbA p) := fun h0 =>
    h.na _ (hb.2.2.1.2.2.yt.1 p hpS h0)
  rw [fin_cap_eq_obj (by simp)]
  exact WP.spec_mono (fin_sc.rvst hA s a p x fin hb.blk hpS hp0 hna hid) fun r hr => hRV.rvSt hr

/-- The thread kind keeps [J] `RunVcpuInv`, from the `rv`-free placement (its [P] `rcw`). -/
theorem finRv_thread {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop} {s0 s : S}
    (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) {a : A} {p : U64} {fin : Bool}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hRV : RunVcpuInv st T s)
    (hc : DelCapOK T Ω Sg H Rp Nt (.Thread p)) (hpl : FinPl st Scs s (.Thread p)) :
    objects.finalise_cap st ar s a (.Thread p) fin false ⦃ r => RunVcpuInv st T r.2.1 ⦄ := by
  have hp := hc.2.2.2.2.2 p rfl
  obtain ⟨hid, hv0⟩ := hpl.1 p rfl
  obtain ⟨Ac', hb⟩ := h.bxi
  have hna := h.na p hp
  have hrc := P.rcw Ac' s p h.fr hb hp
  rw [fin_cap_eq_obj (by simp)]
  exact fin_thread.rvi hA s a p fin hb.blk hp hna (Ne.symm hid) hv0 hrc hRV

/-- The kinds whose `RunVcpuInv` preservation is still named ([J] `FinRvRest3`). -/
def FinRvRestKind3 (c : capability.Cap) : Prop :=
  (∃ x1 x2, c = .Reply x1 x2) ∨ (∃ x1, c = .Vcpu x1) ∨ (∃ x1 x2 x3 x4 x5, c = .Ept x1 x2 x3 x4 x5) ∨
  (∃ x1 x2 x3 x4 x5 x6 x7, c = .Frame x1 x2 x3 x4 x5 true x6 x7)

/-- **[J] (a64) `FinRvRest3`**: [J] `FinRvRest` narrowed to the reply, VCPU, Stage-2 and device-frame kinds
(`FinRvRestKind3`): their finalisation, from a `Cur0` state of the deletion where `RunVcpuInv` holds, ends in a
`RunVcpuInv` state. The SC and thread kinds are proved (`finRv_sc`, `finRv_thread`). -/
def FinRvRest3 (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A) (T Cs Ω : Set U64)
    (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (s0 : S) : Prop :=
  ∀ (Ac : Set U64) (s : S) (a : A) (c : capability.Cap) (fin : Bool),
    Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s → RunVcpuInv st T s → DelCapOK T Ω Sg H Rp Nt c → FinPl st Scs s c →
    FinRvRestKind3 c → objects.finalise_cap st ar s a c fin false ⦃ r => RunVcpuInv st T r.2.1 ⦄

/-- **[J] `FinRvRest` from the `rv`-free placement and [J] `FinRvRest3`.** -/
theorem finRvRest_of3 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop} {s0 : S}
    (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) (G : FinRvRest3 st ar T Cs Ω H Sg Rp Scs Nt Z s0) :
    FinRvRest st ar T Cs Ω H Sg Rp Scs Nt Z s0 := by
  intro Ac s a c fin h hRV hc hpl hk
  rcases hk with hk | ⟨p, x, rfl⟩ | ⟨p, rfl⟩ | hk | hk | hk
  · exact G Ac s a _ fin h hRV hc hpl (Or.inl hk)
  · exact finRv_sc hA h hRV hpl
  · exact finRv_thread hA P h hRV hc hpl
  · exact G Ac s a _ fin h hRV hc hpl (Or.inr (Or.inl hk))
  · exact G Ac s a _ fin h hRV hc hpl (Or.inr (Or.inr (Or.inl hk)))
  · exact G Ac s a _ fin h hRV hc hpl (Or.inr (Or.inr (Or.inr hk)))

/-- The finalisation gaps with `rv` narrowed again: the existing `arch` gap and **[J] `FinRvRest3`**. -/
structure FinGapsAt3 (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (s0 : S) : Prop where
  arch : W7.FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z (fun c => (∃ x1, c = .Vcpu x1) ∨
    (∃ x1 x2 x3 x4 x5, c = .Ept x1 x2 x3 x4 x5) ∨
    (∃ x1 x2 x3 x4 x5 x6 x7, c = .Frame x1 x2 x3 x4 x5 true x6 x7)) s0
  /-- **[J] (a64)** `FinRvRest3` (above). -/
  rv : FinRvRest3 st ar T Cs Ω H Sg Rp Scs Nt Z s0

/-- `FinGapsAt3` at every decode start reached from a `P3Ok` entry. -/
def FinGaps3 (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (P3Ok : S → Prop) : Prop :=
  ∀ s0, EntAt st P3Ok s0 → FinGapsAt3 st ar T Cs Ω H Sg Rp Scs Nt Z s0

theorem FinGapsAt3.to2 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop} {s0 : S}
    (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) (G : FinGapsAt3 st ar T Cs Ω H Sg Rp Scs Nt Z s0) :
    FinGapsAt2 st ar T Cs Ω H Sg Rp Scs Nt Z s0 :=
  ⟨G.arch, finRvRest_of3 hA P G.rv⟩

/-- `FinGaps2` from `R.DelPlace` and `FinGaps3`. -/
theorem finGaps2_of3 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    (P : DelPlace st T Cs Ω H Sg Rp Scs Nt Z V P3Ok) (G : FinGaps3 st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok) :
    FinGaps2 st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok :=
  fun s0 hE => (G s0 hE).to2 hA (P s0 hE)

/-- **`R.DelGaps`** from `R.DelPlace` and `FinGaps3` ([J] `FinRvRest3` only). -/
theorem delGaps_of_gaps3 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    (P : DelPlace st T Cs Ω H Sg Rp Scs Nt Z V P3Ok) (G : FinGaps3 st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok) :
    DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok :=
  delGaps_of_gaps2 hA P (finGaps2_of3 hA P G)

/-- The `CNode` family's decode gap from `FinGaps3`. -/
theorem decGap_cnode_rv3 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    (C : CdtHyps2 st T Cs Ω H Sg Rp Scs Nt Z P3Ok) (P : DelPlace st T Cs Ω H Sg Rp Scs Nt Z V P3Ok)
    (G : FinGaps3 st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok) : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .cnode :=
  decGap_cnode_rv2 hA C P (finGaps2_of3 hA P G)

/-- The thread family's decode gap from `FinGaps3`. -/
theorem decGap_thread3 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    (Y : SspHyps st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (P : TcbPlace st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (Pd : DelPlace st T Cs Ω H Sg Rp Scs Nt Z V P3Ok) (G : FinGaps3 st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok)
    (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok) (TP : TcbPlace7 st T Cs Ω H Sg Rp Scs Nt Z P3Ok) :
    DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .thread :=
  decGap_thread2 hA Y P E Pd (finGaps2_of3 hA Pd G) C TP

end R
end W7

end

end Fl4ProofsA64.P1
