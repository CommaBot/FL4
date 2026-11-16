/-
P1: **SchedContext `YieldTo`** (`schedcontext.yield_to` after the caller's
restart) keeps the invariants: `ScYieldGap` (QueueDecSc) discharged
(`scYieldGap_holds`).

* `YW` writes (the SC words, a thread's registers and `YIELD_TO`): what
  `complete_yield_to` and `set_consumed` write; they keep every thread's
  `SC`, `BOUND_NTFN`, `STATE` and `IN_QUEUES` fields (`yw_keep`).
* `resume`, with the scheduler action, the current thread and the other
  threads' `IN_QUEUES` words kept (`resume.allF`).
* the yield links set (`yield_set_all`), and `yield_switches` (re-queue
  the SC's thread, or switch: link the caller to the SC, queue both,
  reschedule).
-/
import Fl4Proofs.P1.QueueDecSc
import Fl4Proofs.P1.QueueFinFr
import Fl4Proofs.P1.QueueFinSc
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}
variable {A : Type _} {ar : machine.Arch A}

/-! ## The `YW` writes -/

/-- An `Ω` word, a register word or the `YIELD_TO` word of a thread. -/
def YW (T Ω : Set U64) (b : U64) : Prop :=
  b ∈ Ω ∨ ∃ y ∈ T, ∃ K : U64, ((256 ≤ K.val ∧ K.val < 3328) ∨ K.val = 3472) ∧ K.val % 8 = 0 ∧
    b = core.num.U64.wrapping_add y K

theorem yw_trans {s₁ s₂ s₃ : S} (h₁ : WritesIn st s₁ s₂ (YW T Ω)) (h₂ : WritesIn st s₂ s₃ (YW T Ω)) :
    WritesIn st s₁ s₃ (YW T Ω) := (h₁.trans h₂).mono fun _ hb => hb.elim id id

/-- `YW` writes keep every thread's `SC`, `BOUND_NTFN`, `STATE` and
`IN_QUEUES` fields. -/
theorem yw_keep {X : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hw : WritesIn st s s' (YW T Ω)) :
    ∀ y ∈ T, L.mem s' (scA y) = L.mem s (scA y) ∧ L.mem s' (boundA y) = L.mem s (boundA y) ∧
      L.mem s' (stA y) = L.mem s (stA y) ∧ L.mem s' (inqA y) = L.mem s (inqA y) := by
  have hT := h.tcbs
  have K : ∀ y ∈ T, ∀ K0 : U64, K0.val < 4096 → K0.val % 8 = 0 →
      (K0.val = 3464 ∨ K0.val = 3368 ∨ K0.val = 3328 ∨ K0.val = 3592) →
      L.mem s' (core.num.U64.wrapping_add y K0) = L.mem s (core.num.U64.wrapping_add y K0) := by
    intro y hy K0 h1 h2 h3
    refine hw.mem_eq (field_aligned (hT y hy) h1 h2) fun hb => ?_
    rcases hb with hm | ⟨z, hz, K, hK, -, e⟩
    · exact out_ne_field (h.omega _ hm) hy (hT y hy) h1 rfl
    · exact field_ne (hT y hy) (hT z hz) h1 (by omega) (fun _ => by omega) e
  intro y hy
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [scA_eq]; exact K y hy _ (by simp) (by simp) (by simp)
  · exact K y hy 3368#u64 (by simp) (by simp) (by simp)
  · rw [stA_eq]; exact K y hy _ (by simp) (by simp) (by simp)
  · rw [inqA_eq]; exact K y hy _ (by simp) (by simp) (by simp)

theorem reg_yw {s : S} {t r v : U64} (hT : TcbPlaced T) (ht : t ∈ T) (hr : r.val < 384) :
    obj.Tcb.set_reg st t s r v ⦃ s' => WritesIn st s s' (YW T Ω) ⦄ :=
  WP.spec_mono (obj.Tcb.set_reg.wrK s t r v (hT t ht) hr) fun s' ⟨K, hK, e⟩ => by
    subst e
    exact (writesIn_wr (field_aligned (hT t ht) (by omega) (by omega))).mono fun b e =>
      Or.inr ⟨t, ht, K, Or.inl ⟨by omega, by omega⟩, by omega, e⟩

theorem sc_word_yw {s : S} {c o : U64} (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hc : c ∈ Scs) (ho : o.val < 128)
    (h8 : o.val % 8 = 0) : Aligned (core.num.U64.wrapping_add c o) ∧ YW T Ω (core.num.U64.wrapping_add c o) := by
  obtain ⟨hP, hz⟩ := hO.sc c hc
  obtain ⟨c8, c128, cfit⟩ := sc_lo hP hz
  have hv : (core.num.U64.wrapping_add c o).val = c.val + o.val := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  have ha : Aligned (core.num.U64.wrapping_add c o) := by unfold Aligned; rw [hv]; omega
  exact ⟨ha, Or.inl (hO.scW c hc _ ha ⟨by rw [hv]; omega, by rw [hv]; omega⟩)⟩

theorem schedcontext.update_consumed.yw {s : S} {a : A} {c : U64} (hA : P0.ArchTotal ar)
    (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hc : c ∈ Scs) :
    schedcontext.update_consumed st ar s a c ⦃ r => WritesIn st s r.2 (YW T Ω) ⦄ := by
  obtain ⟨ha, hw⟩ := sc_word_yw (T := T) (o := layout.sc.CONSUMED) hO hc (by simp [layout.sc.CONSUMED])
    (by simp [layout.sc.CONSUMED])
  unfold schedcontext.update_consumed
  step with obj.Sc.consumed.spec as ⟨x, _hx⟩
  split
  · step as ⟨y, hy⟩
    refine WP.spec_bind (obj.Sc.set_consumed.spec' s c y) fun s1 e1 => ?_
    subst e1
    exact WP.spec_bind (hA.ticks_to_us a _) fun i _ =>
      (WP.spec_ok _).2 ((writesIn_wr ha).mono fun b e => by rw [e]; exact hw)
  · refine WP.spec_bind (obj.Sc.set_consumed.spec' s c 0#u64) fun s1 e1 => ?_
    subst e1
    exact WP.spec_bind (hA.ticks_to_us a _) fun i _ =>
      (WP.spec_ok _).2 ((writesIn_wr ha).mono fun b e => by rw [e]; exact hw)

theorem schedcontext.set_consumed.yw (hA : P0.ArchTotal ar) (s : S) (a : A) (c t : U64) (wm : Bool)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hc : c ∈ Scs) (ht : t ∈ T) :
    schedcontext.set_consumed st ar s a c t wm ⦃ s' => WritesIn st s s' (YW T Ω) ⦄ := by
  have hT := h.1.choose_spec.choose_spec.tcbs
  unfold schedcontext.set_consumed
  refine WP.spec_bind (schedcontext.update_consumed.yw (T := T) hA h.2.2.1.1 hc) ?_
  rintro ⟨x, s1⟩ w1
  simp only at w1
  try simp only [WP.uncurry'_pair]
  split
  · refine WP.spec_bind (P0.msg.lookup_ipc_buffer.p0 st s1 true t L.total) fun buf _ => ?_
    refine WP.spec_bind (reg_yw (Ω := Ω) (r := layout.reg.BADGE) hT ht (by simp [layout.reg.BADGE, layout.reg.RDI]))
      fun s2 w2 => ?_
    unfold msg.set_mr
    simp only [show (0#u64 < msg.N_MSG_REGISTERS) = True from by simp [msg.N_MSG_REGISTERS], if_true]
    simp only [msg.msg_register, if_true, Aeneas.Std.bind_ok]
    refine WP.spec_bind (Pₘ := fun r : U64 × S => WritesIn st s2 r.2 (YW T Ω)) ?_ ?_
    · refine WP.spec_bind (reg_yw (Ω := Ω) (r := layout.reg.R10) hT ht (by simp [layout.reg.R10])) fun s3 hh => ?_
      simp only [lift, Aeneas.Std.bind_ok, WP.spec_ok]; exact hh
    rintro ⟨len, s3⟩ w3
    simp only at w3
    try simp only [WP.uncurry'_pair]
    unfold msginfo.MessageInfo.new msg.set_msg_info
    simp only [Aeneas.Std.bind_ok]
    refine WP.spec_bind (P0.msginfo.MessageInfo.to_word.p0 _) fun w _ => ?_
    exact WP.spec_mono (reg_yw (Ω := Ω) (r := layout.reg.MSG_INFO) hT ht (by simp [layout.reg.MSG_INFO, layout.reg.RSI]))
      fun s4 w4 => yw_trans w1 (yw_trans w2 (yw_trans w3 w4))
  · exact (WP.spec_ok _).2 w1

theorem schedcontext.cancel_yield_to.yw (s : S) (t : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T) :
    schedcontext.cancel_yield_to st s t ⦃ s' => WritesIn st s s' (YW T Ω) ⦄ := by
  have hT := h.1.choose_spec.choose_spec.tcbs
  have h0 := h.1.choose_spec.choose_spec
  unfold schedcontext.cancel_yield_to
  step with obj.Tcb.is_null.spec as ⟨b, _⟩
  split
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  step with obj.Tcb.yield_to.spec as ⟨i, ei⟩
  split
  · rename_i hi
    have hiS : i ∈ Scs := by rw [ei]; exact h.2.2.1.2.2.yt.2.1 t ht (by rw [← ei]; simpa using hi)
    have hm : scYieldFromA i ∈ Ω := h.2.2.2.2.sub _ (h.2.2.1.1.syW i hiS)
    step with obj.Sc.set_yield_from.spec as ⟨s1, e1⟩
    subst e1
    step with obj.Tcb.set_yield_to.spec as ⟨s2, e2⟩
    subst e2
    have w1 := (writesIn_wr (st := st) (s := s) (v := 0#u64) (h0.omega _ hm).1).mono fun b e => (by rw [e]; exact Or.inl hm : YW T Ω b)
    have w2 := (writesIn_wr (st := st) (s := L.wr s (scYieldFromA i) 0#u64) (v := 0#u64)
      (field_aligned (K := 3472#u64) (hT t ht) (by simp) (by simp))).mono
      fun b e => (Or.inr ⟨t, ht, 3472#u64, Or.inr (by simp), by simp, e⟩ : YW T Ω b)
    exact yw_trans w1 w2
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)

theorem schedcontext.complete_yield_to.yw (hA : P0.ArchTotal ar) (s : S) (a : A) (y : U64)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hy : y ≠ 0#u64 → y ∈ T) :
    schedcontext.complete_yield_to st ar s a y ⦃ r => WritesIn st s r.1 (YW T Ω) ⦄ := by
  unfold schedcontext.complete_yield_to
  step with obj.Tcb.is_null.spec as ⟨b, b_post⟩
  split
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  rename_i hb
  have hyT : y ∈ T := hy (fun e => hb (by rw [b_post, e]; rfl))
  step with obj.Tcb.yield_to.spec as ⟨i, ei⟩
  split
  · rename_i hi
    have hiS : i ∈ Scs := by rw [ei]; exact h.2.2.1.2.2.yt.2.1 y hyT (by rw [← ei]; simpa using hi)
    refine WP.spec_bind (WP.spec_and (schedcontext.set_consumed.blk hA s a i y true h hiS hyT)
      (schedcontext.set_consumed.yw hA s a i y true h hiS hyT)) fun s1 ⟨⟨h1, _, _⟩, w1⟩ => ?_
    refine WP.spec_bind (schedcontext.cancel_yield_to.yw s1 y h1 hyT) fun s2 w2 => ?_
    exact (WP.spec_ok _).2 (yw_trans w1 w2)
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)

/-! ## `resume`, framed -/

/-- `sched.postpone.all`, with the other threads' `IN_QUEUES` words kept. -/
theorem sched.postpone.allF (s : S) (sc : obj.Sc) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (h : SchedQueuesInv st T Cs Ω H s Q R) (ht : L.mem s (scTcbA sc) ∈ T)
    (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hSg : SgOK st Ω Sg s)
    (hr0 : (L.mem s (inqA (L.mem s (scTcbA sc))) &&& sched.Q_RELEASE) = 0#u64)
    (hcore : OutsideObjs st T Cs s (scCoreA sc)) (hcs : L.mem s (scCoreA sc) ∈ Cs)
    (hrun : Runnable (L.mem s (stA (L.mem s (scTcbA sc))))) (hna : L.actionW s ≠ L.mem s (scTcbA sc))
    (hbd : L.mem s (scA (L.mem s (scTcbA sc))) ≠ 0#u64) (hba : L.mem s (scA (L.mem s (scTcbA sc))) ∈ Ac) :
    sched.postpone st s sc ⦃ s' => ∃ Q' R', SchedQueuesInv st T Cs Ω H s' Q' R' ∧ BoundInv st T Ac s' ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧ SgOK st Ω Sg s' ∧ Fr st T Sg s s' ∧
      L.actionW s' = L.actionW s ∧ L.curW s' = L.curW s ∧
      ∀ y ∈ T, y ≠ L.mem s (scTcbA sc) → L.mem s' (inqA y) = L.mem s (inqA y) ⦄ := by
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
  rintro s1 ⟨h1, hw1, hinq1⟩
  have hW1 : ∀ w ∈ Q (L.mem s (affA t)) (L.mem s (prioA t)), w ∈ T := fun w hw => h.memT hc hp hw
  obtain ⟨hB1, hX1, fr1, ea1, ec1, -⟩ := bx_qfoot h hB hX hSg hW1 hc ht p128 hw1
    (fun hf => by rw [hinq1] at hf; split_ifs at hf with e
                  · rw [andn_qq_qq] at hf; exact absurd rfl hf
                  · exact Or.inl hf)
    (fun hf => by rw [hinq1] at hf; split_ifs at hf with e
                  · rw [andn_qq_qr] at hf; exact Or.inr (Or.inl hf)
                  · exact Or.inr (Or.inl hf))
  have hSg1 := hSg.fr fr1
  obtain ⟨-, iq1, -, -, -⟩ := qfoot_keep (Sg := Sg) h hSg hW1 hc ht p128 hw1
  have core1 : L.mem s1 (scCoreA sc) = L.mem s (scCoreA sc) :=
    hw1.mem_eq hcore.1 (qfoot_out hT hW1 hN hN' ht hc h.cur hcore)
  have hq1 : (L.mem s1 (inqA t) &&& sched.Q_QUEUED) = 0#u64 := by
    by_contra hcn
    exact notQ_after_dequeue h ht _ (h1.aff t ht) _ (h1.prio t ht) ((h1.queued t ht).1 hcn)
  have hr1 : (L.mem s1 (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by
    by_contra hcn
    exact h.notR ht hr0 (h1.aff t ht) ((h1.released t ht).1 hcn)
  have hT1 := h1.tcbs
  have hc1 := h1.aff t ht
  have hN1 := h1.nodes _ hc1
  have hN1' := h1.nodes _ h1.cur
  obtain ⟨hsb1, -, -⟩ := ext_qfoot hT hW1 hN hN' ht hc h.cur hw1
  refine WP.spec_bind (WP.spec_and (sched.release_enqueue.inv s1 t _ R h1 ht hq1 hr1
      (by rw [(hsb1 t ht).1]; exact hrun) (by rw [ea1]; exact hna))
    (sched.release_enqueue.foot s1 t _ hT1 ht (h1.notR ht hr1 hc1) hN1 hN1' (h1.release _ hc1))) ?_
  rintro s2 ⟨h2, hw2, hinq2⟩
  have hW2 : ∀ w ∈ t :: R (L.mem s1 (affA t)), w ∈ T := by
    intro w hw; rcases List.mem_cons.1 hw with rfl | hw
    · exact ht
    · exact h1.memTR hc1 hw
  obtain ⟨hB2, hX2, fr2, ea2, ec2, -⟩ := bx_qfoot h1 hB1 hX1 hSg1 hW2 hc1 ht prel hw2
    (fun hf => by rw [hinq2, or_qr_qq] at hf; exact Or.inl hf)
    (fun _ => Or.inr (Or.inr ⟨by rw [fr1.sc t ht]; exact hbd, by rw [fr1.sc t ht]; exact hba⟩))
  have hSg2 := hSg1.fr fr2
  obtain ⟨-, iq2, -, -, -⟩ := qfoot_keep (Sg := Sg) h1 hSg1 hW2 hc1 ht prel hw2
  have core2 : L.mem s2 (scCoreA sc) = L.mem s (scCoreA sc) :=
    (hw2.mem_eq hcore.1 (qfoot_out hT1 hW2 hN1 hN1' ht hc1 h1.cur (hcore.ksb hw1.1))).trans core1
  step with obj.Sc.cpu.spec as ⟨cpu, cpu_post⟩
  rw [core2] at cpu_post
  subst cpu_post
  step with sched.set_reprogram_on.spec as ⟨s3, s3_post⟩
  subst s3_post
  have hN2 := h2.nodes _ hcs
  have hN2' := h2.nodes _ h2.cur
  have e : L.actionW (L.wr s2 (L.nodeAt s2 (L.mem s (scCoreA sc)) layout.node.REPROGRAM) 1#u64) = L.actionW s2 := by
    unfold LawfulStore.actionW
    simp only [LawfulStore.cpu_wr, nodeAt_wr]
    by_cases hcc : L.mem s (scCoreA sc) = L.cpu s2
    · rw [hcc, rd_node_wr_node hN2' (by rw [repr_val]; omega) (by rw [act_val]; omega) (by rw [repr_val])
        (by rw [act_val]), if_neg (by rw [repr_val, act_val]; omega)]
    · exact rd_node_wr_node_cpu hN2' hN2 (by rw [repr_val]; omega) (by rw [act_val]; omega) (by rw [repr_val])
        (by rw [act_val]) hcc
  have o0 := nodeword_other (v := 1#u64) h2 hcs h2.cur (o := layout.node.REPROGRAM) (o' := layout.node.CUR_THREAD)
    (by rw [repr_val]; omega) (by rw [repr_val]) (by rw [curth0]; omega) (by rw [curth0])
    (fun _ => by rw [repr_val, curth0]; omega)
  have o8 := nodeword_other (v := 1#u64) h2 hcs h2.cur (o := layout.node.REPROGRAM) (o' := layout.node.IDLE_THREAD)
    (by rw [repr_val]; omega) (by rw [repr_val]) (by rw [idle8]; omega) (by rw [idle8])
    (fun _ => by rw [repr_val, idle8]; omega)
  obtain ⟨hB3, hX3⟩ := bx_wr (v := 1#u64) h2 hB2 hX2 (nodeAt_aligned hN2 (by rw [repr_val]; omega) (by rw [repr_val]))
    (not_prot_node h2 hX2.1 hSg2.sub hcs (by rw [repr_val]; omega))
    (fun y hy => ⟨fun e' => node_ne_field hN2 (by rw [repr_val]; omega) hy (h2.tcbs y hy) (K := 3464#u64)
        (by decide) (by rw [scA_eq] at e'; exact UScalar.eq_of_val_eq e'),
      fun e' => node_ne_field hN2 (by rw [repr_val]; omega) hy (h2.tcbs y hy) (K := 3592#u64)
        (by decide) (by rw [inqA_eq] at e'; exact UScalar.eq_of_val_eq e')⟩)
    (fun o ho e' => by
      by_cases hcc : L.mem s (scCoreA sc) = L.cpu s2
      · rw [hcc, nodeAt_val hN2' (by rw [repr_val]; omega), nodeAt_val hN2' (by omega), repr_val] at e'; omega
      · exact nodeAt_ne_cpu hN2 hN2' (by rw [repr_val]; omega) (by omega) hcc (UScalar.eq_of_val_eq e'))
    (hX2.tn_node h2 hSg2.sub hcs (by rw [repr_val]; omega) (by rw [repr_val]) (by rw [repr_val]; omega))
  refine ⟨_, _, inv_wr_node_low h2 hcs (by rw [repr_val]; omega) (by rw [repr_val]; omega) (by rw [repr_val])
    (by rw [e]; exact h2.action) (by rw [e]; exact h2.actOK) (by rw [o0]; exact h2.curT) (by rw [o8]; exact h2.idleT),
    hB3, hX3, ⟨hSg2.sub, fun b hb => by rw [L.ksb_wr]; exact hSg2.ks b hb,
      fun o h1' h2' => by rw [L.ksb_wr]; exact hSg2.ksΩ o h1' h2'⟩,
    fr1.trans (fr2.trans (fr_node (hi8 := fun _ => by simp [layout.node.SCHED_ACTION, layout.node.REPROGRAM, layout.node.CUR_THREAD]) h2 hSg2 hcs (by rw [repr_val]; omega) (by rw [repr_val])
      (fun _ => by rw [repr_val]; omega) ⟨by rw [repr_val]; omega, by rw [repr_val]; omega⟩)),
    e.trans (ea2.trans ea1), by
      have := ec2.trans ec1
      unfold LawfulStore.curW at this ⊢
      simp only [LawfulStore.cpu_wr, nodeAt_wr]
      rw [o0]; exact this, fun y hy hyt => ?_⟩
  rw [inqA_eq, L.mem_wr_ne (nodeAt_aligned hN2 (by rw [repr_val]; omega) (by rw [repr_val]))
    (field_aligned (h2.tcbs y hy) (K := 3592#u64) (by simp) (by simp))
    (fun e' => node_ne_field hN2 (by rw [repr_val]; omega) hy (h2.tcbs y hy) (K := 3592#u64) (by simp)
      (UScalar.eq_of_val_eq e')), ← inqA_eq, iq2 y hy hyt, iq1 y hy hyt]


/-- `schedcontext.resume.all`, with the scheduler action, the current thread,
`SCsOK` and the other threads' `IN_QUEUES` words kept. -/
theorem schedcontext.resume.allF (hA : P0.ArchTotal ar) (s : S) (a : A) (sc : obj.Sc)
    (Q : U64 → U64 → List U64) (R : U64 → List U64) (h : SchedQueuesInv st T Cs Ω H s Q R)
    (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hSg : SgOK st Ω Sg s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s)
    (hsc : sc ≠ 0#u64 → L.mem s (scTcbA sc) ≠ 0#u64 →
      L.mem s (scTcbA sc) ∈ T ∧ OutsideObjs st T Cs s (scCoreA sc) ∧ L.mem s (scCoreA sc) ∈ Cs ∧
        L.actionW s ≠ L.mem s (scTcbA sc)) :
    schedcontext.resume st ar s a sc ⦃ s' _ => ∃ Q' R', SchedQueuesInv st T Cs Ω H s' Q' R' ∧
      BoundInv st T Ac s' ∧ XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧ SgOK st Ω Sg s' ∧ Fr st T Sg s s' ∧
      L.actionW s' = L.actionW s ∧ L.curW s' = L.curW s ∧
      ∀ y ∈ T, y ≠ L.mem s (scTcbA sc) → L.mem s' (inqA y) = L.mem s (inqA y) ⦄ := by
  unfold schedcontext.resume
  step with obj.Sc.is_null.spec as ⟨b, b_post⟩
  split
  · simp only [WP.spec_ok, WP.uncurry'_pair]; exact ⟨Q, R, h, hB, hX, hSg, Fr.refl _ _, by simp, by simp, fun _ _ _ => by simp⟩
  rename_i hb
  have hsc0 : sc ≠ 0#u64 := by simpa [b_post] using hb
  step with obj.Sc.tcb.spec as ⟨i, i_post⟩
  step with obj.Tcb.is_null.spec as ⟨b1, b1_post⟩
  split
  · simp only [WP.spec_ok, WP.uncurry'_pair]; exact ⟨Q, R, h, hB, hX, hSg, Fr.refl _ _, by simp, by simp, fun _ _ _ => by simp⟩
  rename_i hb1
  have hi0 : L.mem s (scTcbA sc) ≠ 0#u64 := by rw [← i_post]; simpa [b1_post] using hb1
  obtain ⟨hiT, hcore, hcs, hna⟩ := hsc hsc0 hi0
  step with sched.is_schedulable.spec' as ⟨b2, b2_post⟩
  split
  · rename_i hb2
    obtain ⟨hrun, hbd, hr0, hmx⟩ := b2_post hb2
    rw [i_post] at hrun hr0 hbd hmx
    have hba : L.mem s (scA (L.mem s (scTcbA sc))) ∈ Ac :=
      (hS.act _ (hX.2.2.bound _ hiT hbd).1).2 hmx
    have post := sched.postpone.allF s sc Q R h hiT hB hX hSg hr0 hcore hcs hrun hna hbd hba
    step with sporadic.ready.spec as ⟨b3⟩
    split
    · step with sporadic.sufficient.ok (st := st) hA as ⟨b4⟩
      split
      · simp only [WP.spec_ok, WP.uncurry'_pair]; exact ⟨Q, R, h, hB, hX, hSg, Fr.refl _ _, by simp, by simp, fun _ _ _ => by simp⟩
      · exact WP.spec_bind post fun s1 h1 => by
          obtain ⟨Q', R', a1, a2, a3, a4, a5, a6, a7, a8⟩ := h1
          have h1' : ∃ Q' R', SchedQueuesInv st T Cs Ω H s1 Q' R' ∧ BoundInv st T Ac s1 ∧
              XInv st T Cs Ω Sg Rp Scs Nt Z s1 ∧ SgOK st Ω Sg s1 ∧ Fr st T Sg s s1 ∧ L.actionW s1 = L.actionW s ∧
              L.curW s1 = L.curW s ∧ ∀ y ∈ T, y ≠ L.mem s (scTcbA sc) → L.mem s1 (inqA y) = L.mem s (inqA y) :=
            ⟨Q', R', a1, a2, a3, a4, a5, a6, a7, a8⟩
          simpa using h1'
    · exact WP.spec_bind post fun s1 h1 => by
        obtain ⟨Q', R', a1, a2, a3, a4, a5, a6, a7, a8⟩ := h1
        have h1' : ∃ Q' R', SchedQueuesInv st T Cs Ω H s1 Q' R' ∧ BoundInv st T Ac s1 ∧
            XInv st T Cs Ω Sg Rp Scs Nt Z s1 ∧ SgOK st Ω Sg s1 ∧ Fr st T Sg s s1 ∧ L.actionW s1 = L.actionW s ∧
            L.curW s1 = L.curW s ∧ ∀ y ∈ T, y ≠ L.mem s (scTcbA sc) → L.mem s1 (inqA y) = L.mem s (inqA y) :=
          ⟨Q', R', a1, a2, a3, a4, a5, a6, a7, a8⟩
        simpa using h1'
  · simp only [WP.spec_ok, WP.uncurry'_pair]; exact ⟨Q, R, h, hB, hX, hSg, Fr.refl _ _, by simp, by simp, fun _ _ _ => by simp⟩


/-! ## The yield links -/

/-- `XInv.wr_yield0` for any value typed as the yield links require. -/
theorem XInv.wr_yieldV {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {a : U64}
    {v : U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (ha : Aligned a)
    (hA : AvoidX st T Rp Scs Nt s a)
    (htn : TimerOK st T Cs (L.wr s a v) ∧ NtbOK st T Nt (L.wr s a v))
    (hvy : ∀ u ∈ T, a.val = (yieldA u).val → v ≠ 0#u64 → v ∈ Scs)
    (hvf : ∀ c ∈ Scs, a.val = (scYieldFromA c).val → v ≠ 0#u64 → v ∈ T) :
    XInv st T Cs Ω Sg Rp Scs Nt Z (L.wr s a v) := by
  obtain ⟨hR, hC, hU, hN, hcs, hid⟩ := hA
  have hO := hX.1
  have hT := h.tcbs
  have k : ∀ b, Aligned b → a.val ≠ b.val → L.mem (L.wr s a v) b = L.mem s b := fun b hb hne =>
    L.mem_wr_ne ha hb hne
  have alP : ∀ b, Prot T Rp Scs Nt b → Aligned b := fun b hb => hO.aligned hT hb
  refine hX.keep' (fun r hr => ⟨k _ (alP _ (Or.inl ⟨r, hr, Or.inl rfl⟩)) (hR r hr).1,
      k _ (alP _ (Or.inl ⟨r, hr, Or.inr (Or.inl rfl)⟩)) (hR r hr).2.1,
      k _ (alP _ (Or.inl ⟨r, hr, Or.inr (Or.inr rfl)⟩)) (hR r hr).2.2⟩)
    (fun c hc => ⟨k _ (alP _ (Or.inr (Or.inl ⟨c, hc, Or.inl rfl⟩))) (hC c hc).1,
      k _ (alP _ (Or.inr (Or.inl ⟨c, hc, Or.inr (Or.inl rfl)⟩))) (hC c hc).2.1⟩)
    (fun u hu => k _ (alP _ (Or.inr (Or.inr (Or.inl ⟨u, hu, Or.inl rfl⟩)))) (hU u hu).1)
    (fun u hu => k _ (alP _ (Or.inr (Or.inr (Or.inl ⟨u, hu, Or.inr (Or.inl rfl)⟩)))) (hU u hu).2.1)
    (fun u hu => k _ (alP _ (Or.inr (Or.inr (Or.inl ⟨u, hu, Or.inr (Or.inr (Or.inl rfl))⟩)))) (hU u hu).2.2.1)
    ?_ (fun c hc => k _ (alP _ (Or.inr (Or.inl ⟨c, hc, Or.inr (Or.inr (Or.inl rfl))⟩))) (hC c hc).2.2.1)
    (fun u hu => by
      rw [k _ (alP _ (Or.inr (Or.inr (Or.inl ⟨u, hu, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩)))) (hU u hu).2.2.2]
      exact hX.2.2.bnd u hu)
    (fun n hn => k _ (hO.ntAl n hn) (hN n hn)) htn
    (fun c hc => k _ (alP _ (Or.inr (Or.inl ⟨c, hc, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩))) (hC c hc).2.2.2.1)
    ⟨fun c hc => by
      rw [k _ (alP _ (Or.inr (Or.inl ⟨c, hc, Or.inl rfl⟩))) (hC c hc).1]; exact hX.2.2.yt.1 c hc,
     fun u hu h0 => by
      have hb := alP _ (Or.inr (Or.inr (Or.inl ⟨u, hu, Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩)))
      rw [L.mem_wr_val ha hb] at h0 ⊢
      split
      · rename_i e; rw [if_pos e] at h0; exact hvy u hu e h0
      · rename_i e; rw [if_neg e] at h0; exact hX.2.2.yt.2.1 u hu h0,
     fun c hc h0 => by
      have hb := alP _ (Or.inr (Or.inl ⟨c, hc, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩))
      rw [L.mem_wr_val ha hb] at h0 ⊢
      split
      · rename_i e; rw [if_pos e] at h0; exact hvf c hc e h0
      · rename_i e; rw [if_neg e] at h0; exact hX.2.2.yt.2.2 c hc h0⟩
    (fun c hc => k _ (alP _ (Or.inr (Or.inl ⟨c, hc, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))⟩)))
      (hC c hc).2.2.2.2) ?_
  · unfold LawfulStore.cscW; rw [nodeA_wr]
    rw [k (L.nodeA s layout.node.CUR_SC) (nodeAt_aligned (h.nodes _ h.cur) (by simp [layout.node.CUR_SC])
      (by simp [layout.node.CUR_SC])) hcs]
    exact hX.2.2.cur
  · unfold LawfulStore.idleW; rw [LawfulStore.cpu_wr, nodeAt_wr]
    exact k _ (nodeAt_aligned (h.nodes _ h.cur) (by simp [layout.node.IDLE_THREAD])
      (by simp [layout.node.IDLE_THREAD])) hid

/-- **Setting the yield links** (`ct` yields to the SC `c`) keeps `BlkOK`
and every thread's `SC`, `STATE` and `IN_QUEUES` fields. -/
theorem yield_link.blk {s : S} {t c : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T)
    (hc : c ∈ Scs) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr (L.wr s (yieldA t) c) (scYieldFromA c) t) ∧
      ∀ y ∈ T, L.mem (L.wr (L.wr s (yieldA t) c) (scYieldFromA c) t) (scA y) = L.mem s (scA y) ∧
        L.mem (L.wr (L.wr s (yieldA t) c) (scYieldFromA c) t) (stA y) = L.mem s (stA y) ∧
        L.mem (L.wr (L.wr s (yieldA t) c) (scYieldFromA c) t) (inqA y) = L.mem s (inqA y) := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hT := h0.tcbs
  have hta := hT t ht
  have hO := hX.1
  have hsub := hSg.sub
  -- the `YIELD_TO` word
  have hya : Aligned (yieldA t) := field_aligned (K := 3472#u64) hta (by simp) (by simp)
  have fne : ∀ u ∈ T, ∀ K : U64, K.val < 4096 → K.val ≠ 3472 →
      (yieldA t).val ≠ (core.num.U64.wrapping_add u K).val :=
    fun u hu K hK hne e => field_ne (K1 := 3472#u64) hta (hT u hu) (by simp) hK (fun _ => by simp; omega)
      (UScalar.eq_of_val_eq e)
  have h1 : SchedQueuesInv st T Cs Ω H (L.wr s (yieldA t) c) Q R :=
    inv_wr_field (K := 3472#u64) h0 ht (by simp) (by simp) (by simp)
  obtain ⟨hB1, -⟩ := bnd_wr (v := c) h0 hB hya
    (fun y hy => ⟨by rw [scA_eq]; exact fne y hy _ (by simp) (by simp),
      by rw [inqA_eq]; exact fne y hy _ (by simp) (by simp)⟩)
    (fun o ho' e => node_ne_field (h0.nodes _ h0.cur) (by omega) ht hta (K := 3472#u64) (by simp)
      (UScalar.eq_of_val_eq e).symm)
    (fun y hy => by rw [stA_eq]; exact fne _ hy _ (by simp) (by simp))
  have hX1 := XInv.wr_yieldV (v := c) h0 hX hya (avoidX_yieldA h0 hX hsub ht)
    (hX.tn_field (v := c) h0 hsub ht (K := 3472#u64) (by simp) (by simp) (by simp))
    (fun _ _ _ _ => hc)
    (fun c' hc' e _ => absurd e (out_ne_field (h0.omega _ (hsub _ (hO.syW c' hc'))) ht hta (K := 3472#u64) (by simp)))
  have hS1 := SCsOK.field (K := 3472#u64) (v := c) h0 hS hX ht (by simp) (by simp) (by simp)
  have hSg1 : SgOK st Ω Sg (L.wr s (yieldA t) c) :=
    ⟨hSg.sub, fun b hb => by rw [L.ksb_wr]; exact hSg.ks b hb, fun o h1' h2' => by rw [L.ksb_wr]; exact hSg.ksΩ o h1' h2'⟩
  have k1 : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3472 →
      L.mem (L.wr s (yieldA t) c) (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y hy K hK hK8 hne => L.mem_wr_ne hya (field_aligned (hT y hy) hK hK8) (fne y hy K hK hne)
  -- the `YIELD_FROM` word
  set s1 := L.wr s (yieldA t) c with hs1
  have hm : scYieldFromA c ∈ Ω := hsub _ (hO.syW c hc)
  have ho := h1.omega _ hm
  obtain ⟨-, -, -, -, -, -, -, e56⟩ := sc_facts hO hc
  obtain ⟨-, -, -, -, -, -, e32, -⟩ := sc_facts hO hc
  have hO1 := hX1.1
  have h2 : SchedQueuesInv st T Cs Ω H (L.wr s1 (scYieldFromA c) t) Q R :=
    inv_of_free h1 ((writesIn_wr (v := t) ho.1).mono fun b hb => hb ▸ Or.inl hm)
  have tmA : TmFr st T Cs Nt s1 (L.wr s1 (scYieldFromA c) t) :=
    TmFr.wr hT h1.nodes hO1 ho.1 (notTmW_omega hT h1.nodes ho
      (fun n hn e => by
        rw [show scYieldFromA c = core.num.U64.wrapping_add c layout.sc.YIELD_FROM from rfl, e56,
          ntfnBtA_val (hO.ntP n hn)] at e
        have := hO.ntOSc n hn c hc; have := (sc_facts hO hc).1; omega))
  obtain ⟨hB2, -⟩ := bnd_wr (v := t) h1 hB1 ho.1
    (fun y hy => ⟨by rw [scA_eq]; exact (out_ne_field ho hy (hT y hy) (by simp)).symm,
      by rw [inqA_eq]; exact (out_ne_field ho hy (hT y hy) (by simp)).symm⟩)
    (fun o ho' => (out_ne_node ho h1.cur (h1.nodes _ h1.cur) (by omega)).symm)
    (fun y hy => by rw [stA_eq]; exact (out_ne_field ho hy (hT y hy) (by simp)).symm)
  have hX2 := XInv.wr_yieldV (v := t) h1 hX1 ho.1 (avoidX_scYield h1 hX1 hsub hc) (hX1.tn tmA)
    (fun u hu e _ => absurd e.symm (out_ne_field ho hu (hT u hu) (K := 3472#u64) (by simp)))
    (fun _ _ _ _ => ht)
  have hS2 := SCsOK.scword (v := t) h1 hS1 hX1 hc (Or.inr rfl) (fun e _ => absurd (congrArg UScalar.val e) (by
    rw [e32, e56]; omega))
  refine ⟨⟨⟨Q, R, h2⟩, hB2, hX2, hS2,
    ⟨hSg.sub, fun b hb => by rw [L.ksb_wr]; exact hSg1.ks b hb, fun o h1' h2' => by rw [L.ksb_wr]; exact hSg1.ksΩ o h1' h2'⟩⟩,
    fun y hy => ?_⟩
  have k2 : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3472 →
      L.mem (L.wr s1 (scYieldFromA c) t) (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun K hK hK8 hne => by
      rw [L.mem_wr_ne ho.1 (field_aligned (hT y hy) hK hK8) (out_ne_field ho hy (hT y hy) hK).symm]
      exact k1 y hy K hK hK8 hne
  exact ⟨by rw [scA_eq]; exact k2 _ (by simp) (by simp) (by simp), by rw [stA_eq]; exact k2 _ (by simp) (by simp) (by simp),
    by rw [inqA_eq]; exact k2 _ (by simp) (by simp) (by simp)⟩

/-! ## Re-queueing -/

/-- `dequeue` keeps `BlkOK`; the thread leaves its ready queue, keeps its
release flag, and the other threads keep their `IN_QUEUES` words. -/
theorem sched.dequeue.blkY (s : S) (t : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T) :
    sched.dequeue st s t ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      (L.mem s' (inqA t) &&& sched.Q_QUEUED) = 0#u64 ∧
      ((L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64 → (L.mem s' (inqA t) &&& sched.Q_RELEASE) = 0#u64) ∧
      ∀ y ∈ T, L.mem s' (stA y) = L.mem s (stA y) ∧ L.mem s' (scA y) = L.mem s (scA y) ∧
        (y ≠ t → L.mem s' (inqA y) = L.mem s (inqA y)) ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hT := h0.tcbs
  have hc := h0.aff t ht
  have hp := h0.prio t ht
  have hN := h0.nodes _ hc
  have hN' := h0.nodes _ h0.cur
  have hR1 := h0.ready _ hc
  have hmemq := (h0.queued t ht).1
  refine WP.spec_mono (WP.spec_and (sched.dequeue.inv s t Q R h0 ht)
    (sched.dequeue.foot s t _ hT ht hp hN hN' (hR1.1.rel _ hp) hmemq)) ?_
  rintro s1 ⟨h1, hw1, hinq1⟩
  have hW1 : ∀ w ∈ Q (L.mem s (affA t)) (L.mem s (prioA t)), w ∈ T := fun w hw => h0.memT hc hp hw
  obtain ⟨hB1, hX1, fr1, -, -, -⟩ := bx_qfoot h0 hB hX hSg hW1 hc ht p128 hw1
    (fun hf => by rw [hinq1] at hf; split_ifs at hf with e
                  · rw [andn_qq_qq] at hf; exact absurd rfl hf
                  · exact Or.inl hf)
    (fun hf => by rw [hinq1] at hf; split_ifs at hf with e
                  · rw [andn_qq_qr] at hf; exact Or.inr (Or.inl hf)
                  · exact Or.inr (Or.inl hf))
  obtain ⟨-, iq1, -, -, -⟩ := qfoot_keep (Sg := Sg) h0 hSg hW1 hc ht p128 hw1
  have hq1 : (L.mem s1 (inqA t) &&& sched.Q_QUEUED) = 0#u64 := by
    by_contra hcn
    exact notQ_after_dequeue h0 ht _ (h1.aff t ht) _ (h1.prio t ht) ((h1.queued t ht).1 hcn)
  refine ⟨⟨⟨_, R, h1⟩, hB1, hX1, hS.fr fr1, hSg.fr fr1⟩, hq1, fun hr0 => ?_,
    fun y hy => ⟨fr1.st y hy, fr1.sc y hy, iq1 y hy⟩⟩
  rw [hinq1]; split_ifs
  · rw [andn_qq_qr]; exact hr0
  · exact hr0

/-- `enqueue` of a runnable thread with an active SC, out of every release
queue, keeps `BlkOK`. -/
theorem sched.enqueue.blkY (s : S) (t : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T)
    (hrun : Runnable (L.mem s (stA t))) (hbd : L.mem s (scA t) ≠ 0#u64) (hba : L.mem s (scA t) ∈ Ac)
    (hr : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64) :
    sched.enqueue st s t ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      ∀ y ∈ T, L.mem s' (stA y) = L.mem s (stA y) ∧ L.mem s' (scA y) = L.mem s (scA y) ∧
        (y ≠ t → L.mem s' (inqA y) = L.mem s (inqA y)) ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  refine WP.spec_mono (sched.enqueue.schX (Sg := Sg) s t Q R h0 hB hSg ht (fun _ => hr) (fun _ => hrun)
    (fun _ => hbd) (fun _ => hba)) ?_
  rintro s' ⟨⟨Q', R', h'⟩, hB', f, -, -, -, -, iq⟩
  exact ⟨⟨⟨Q', R', h'⟩, hB', hX.fr f, hS.fr f, hSg.fr f⟩, fun y hy => ⟨f.st y hy, f.sc y hy, iq y hy⟩⟩

/-! ## `yield_switches` -/

/-- **`yield_switches`** keeps `BlkOK`: the SC's thread re-queued, or the
caller linked to the SC and both queued (then a reschedule); when it does
not switch, the caller's state is kept. -/
theorem schedcontext.yield_switches.blkY (s : S) (sc ct : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hsc : sc ∈ Scs) (hct : ct ∈ T) (hi0 : L.mem s (scTcbA sc) ≠ 0#u64) (hne : L.mem s (scTcbA sc) ≠ ct)
    (hrun : Runnable (L.mem s (stA ct))) (hbd : L.mem s (scA ct) ≠ 0#u64) (hba : L.mem s (scA ct) ∈ Ac)
    (hr : (L.mem s (inqA ct) &&& sched.Q_RELEASE) = 0#u64) :
    schedcontext.yield_switches st s sc ct ⦃ r => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2 ∧
      (r.1 = false → L.mem r.2 (stA ct) = L.mem s (stA ct)) ⦄ := by
  unfold schedcontext.yield_switches
  step with obj.Sc.tcb.spec as ⟨i, ei⟩
  have hiT : i ∈ T := by rw [ei]; exact h.2.2.1.2.2.yt.1 sc hsc hi0
  have hic : i ≠ ct := by rw [ei]; exact hne
  step with sched.is_schedulable.spec' as ⟨b, hb⟩
  split
  · rename_i hbt
    obtain ⟨hrun_i, hbd_i, hr_i, hmx⟩ := hb hbt
    have hba_i : L.mem s (scA i) ∈ Ac := (h.2.2.2.1.act _ (h.2.2.1.2.2.bound i hiT hbd_i).1).2 hmx
    have rq : (do
        let s1 ← sched.dequeue st s i
        let s2 ← sched.enqueue st s1 i
        ok (false, s2)) ⦃ r => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2 ∧
          (r.1 = false → L.mem r.2 (stA ct) = L.mem s (stA ct)) ⦄ := by
      refine WP.spec_bind (sched.dequeue.blkY s i h hiT) fun s1 ⟨h1, _, r1, k1⟩ => ?_
      refine WP.spec_bind (sched.enqueue.blkY s1 i h1 hiT (by rw [(k1 i hiT).1]; exact hrun_i)
        (by rw [(k1 i hiT).2.1]; exact hbd_i) (by rw [(k1 i hiT).2.1]; exact hba_i) (r1 hr_i)) fun s2 ⟨h2, k2⟩ => ?_
      exact (WP.spec_ok _).2 ⟨h2, fun _ => (k2 ct hct).1.trans (k1 ct hct).1⟩
    step with obj.Sc.cpu.spec as ⟨i1, _⟩
    step with LawfulStore.cur_cpu_spec as ⟨i2, _⟩
    split
    · exact rq
    step with obj.Tcb.prio.spec as ⟨i3, _⟩
    step with obj.Tcb.prio.spec as ⟨i4, _⟩
    split
    · exact rq
    -- the switch
    refine WP.spec_bind (obj.Tcb.set_yield_to.spec s ct sc) fun s1 e1 => ?_
    subst e1
    refine WP.spec_bind (obj.Sc.set_yield_from.spec _ sc ct) fun s2 e2 => ?_
    subst e2
    obtain ⟨h2, k2⟩ := yield_link.blk h hct hsc
    refine WP.spec_bind (sched.dequeue.blkY _ i h2 hiT) fun s3 ⟨h3, _, r3, k3⟩ => ?_
    refine WP.spec_bind (sched.enqueue.blkY s3 ct h3 hct
      (by rw [(k3 ct hct).1, (k2 ct hct).2.1]; exact hrun)
      (by rw [(k3 ct hct).2.1, (k2 ct hct).1]; exact hbd)
      (by rw [(k3 ct hct).2.1, (k2 ct hct).1]; exact hba)
      (by rw [(k3 ct hct).2.2 (Ne.symm hic), (k2 ct hct).2.2]; exact hr)) fun s4 ⟨h4, k4⟩ => ?_
    refine WP.spec_bind (sched.enqueue.blkY s4 i h4 hiT
      (by rw [(k4 i hiT).1, (k3 i hiT).1, (k2 i hiT).2.1]; exact hrun_i)
      (by rw [(k4 i hiT).2.1, (k3 i hiT).2.1, (k2 i hiT).1]; exact hbd_i)
      (by rw [(k4 i hiT).2.1, (k3 i hiT).2.1, (k2 i hiT).1]; exact hba_i)
      (by rw [(k4 i hiT).2.2 hic]; exact r3 (by rw [(k2 i hiT).2.2]; exact hr_i))) fun s5 ⟨h5, _⟩ => ?_
    refine WP.spec_bind (sched.reschedule_required.blk s5 h5) fun s6 ⟨h6, _⟩ => ?_
    exact (WP.spec_ok _).2 ⟨h6, fun e => absurd e (by simp)⟩
  · exact (WP.spec_ok _).2 ⟨h, fun _ => rfl⟩

/-! ## `yield_to` -/

/-- **The YieldTo gap holds** (`ScYieldGap`). -/
theorem scYieldGap_holds (hA : P0.ArchTotal ar) (U : Set U64) : ScYieldGap st ar T Cs Ω H Sg Rp Scs Nt Z U := by
  intro Ac s a sc call hx _ hsc _ hst hi0 hne _ hact hbd hba hnr
  have h := hx.blk
  obtain ⟨⟨Q0, R0, h00⟩, -, -, -, -⟩ := id h
  have hT := h00.tcbs
  have hct : L.curW s ∈ T := h00.curT
  set ct := L.curW s with hctdef
  unfold schedcontext.yield_to
  step with obj.Sc.yield_from.val as ⟨yf, eyf⟩
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧
      L.actionW r.1 = L.actionW s ∧ L.curW r.1 = L.curW s ∧
      (∀ y ∈ T, L.mem r.1 (scA y) = L.mem s (scA y) ∧ L.mem r.1 (stA y) = L.mem s (stA y) ∧
        L.mem r.1 (inqA y) = L.mem s (inqA y)) ∧ L.mem r.1 (scTcbA sc) = L.mem s (scTcbA sc)) ?_ ?_
  · split
    · exact (WP.spec_ok _).2 ⟨h, rfl, rfl, fun _ _ => ⟨rfl, rfl, rfl⟩, rfl⟩
    · have hy : yf ≠ 0#u64 → yf ∈ T := fun hy0 => by
        rw [eyf]; exact h.2.2.1.2.2.yt.2.2 sc hsc (by rw [← eyf]; exact hy0)
      refine WP.spec_mono (WP.spec_and (schedcontext.complete_yield_to.blkS hA s a yf sc h hy hsc)
        (schedcontext.complete_yield_to.yw hA s a yf h hy)) ?_
      rintro ⟨s1, a1⟩ ⟨⟨h1, -, n1, k1⟩, w1⟩
      have kk := yw_keep h00 w1
      exact ⟨h1, n1.1, n1.2.2, fun y hy => ⟨(kk y hy).1, (kk y hy).2.2.1, (kk y hy).2.2.2⟩, k1.1⟩
  rintro ⟨s1, a1⟩ ⟨h1, ea1, ec1, k1, t1⟩
  try simp only [WP.uncurry'_pair]
  obtain ⟨⟨Q1, R1, h01⟩, hB1, hX1, hS1, hSg1⟩ := h1
  have hO1 := hX1.1
  have hiT : L.mem s1 (scTcbA sc) ∈ T := hX1.2.2.yt.1 sc hsc (by rw [t1]; exact hi0)
  have hsc' : sc ≠ 0#u64 → L.mem s1 (scTcbA sc) ≠ 0#u64 →
      L.mem s1 (scTcbA sc) ∈ T ∧ OutsideObjs st T Cs s1 (scCoreA sc) ∧ L.mem s1 (scCoreA sc) ∈ Cs ∧
        L.actionW s1 ≠ L.mem s1 (scTcbA sc) := fun _ _ =>
    ⟨hiT, h01.omega _ (hSg1.sub _ (hO1.fixW sc hsc).2), hX1.2.2.core sc hsc, fun e => by
      rw [ea1] at e
      rcases hact with e0 | e0 <;> rw [e0] at e <;> exact notT_small h01.tcbs (by rw [← e]; simp) hiT⟩
  refine WP.spec_bind (schedcontext.resume.allF hA s1 a1 sc Q1 R1 h01 hB1 hX1 hSg1 hS1 hsc') ?_
  rintro ⟨s2, a2⟩ ⟨Q2, R2, h02, hB2, hX2, hSg2, fr2, ea2, ec2, iq2⟩
  try simp only [WP.uncurry'_pair]
  have h2 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s2 := ⟨⟨Q2, R2, h02⟩, hB2, hX2, hS1.fr fr2, hSg2⟩
  step with sched.cur_thread.spec as ⟨ct', ect'⟩
  have hc' : ct' = ct := by
    have : L.curW s2 = L.curW s := ec2.trans ec1
    rw [ect']; exact this
  subst hc'
  have t2 : L.mem s2 (scTcbA sc) = L.mem s (scTcbA sc) := (fr2.sig _ (hO1.fixW sc hsc).1).trans t1
  have hnei : ct ≠ L.mem s1 (scTcbA sc) := fun e => hne (by rw [← t1, ← e])
  refine WP.spec_bind (schedcontext.yield_switches.blkY s2 sc ct h2 hsc hct (by rw [t2]; exact hi0)
    (by rw [t2]; exact hne)
    (by rw [fr2.st ct hct, (k1 ct hct).2.1, hst]; exact runnable_restart)
    (by rw [fr2.sc ct hct, (k1 ct hct).1]; exact hbd)
    (by rw [fr2.sc ct hct, (k1 ct hct).1]; exact hba)
    (by rw [iq2 ct hct hnei, (k1 ct hct).2.2]; exact hnr)) ?_
  rintro ⟨b1, s3⟩ ⟨h3, hk3⟩
  simp only at h3 hk3
  cases b1
  · try simp only [Bool.false_eq_true, ↓reduceIte]
    have st3 : L.mem s3 (stA ct) = sched.TS_RESTART := by
      rw [hk3 rfl, fr2.st ct hct, (k1 ct hct).2.1, hst]
    refine WP.spec_bind (WP.spec_and (schedcontext.set_consumed.blk hA s3 a2 sc ct call h3 hsc hct)
      (schedcontext.set_consumed.yw hA s3 a2 sc ct call h3 hsc hct)) fun s4 ⟨⟨h4, _, _⟩, w4⟩ => ?_
    have st4 : L.mem s4 (stA ct) = sched.TS_RESTART := by
      rw [(yw_keep h3.1.choose_spec.choose_spec w4 ct hct).2.2.1]; exact st3
    refine WP.spec_bind (sched.set_thread_state.running_bxi h4.bxi hct st4) fun s5 h5 => ?_
    exact (WP.spec_ok _).2 ⟨Ac, h5⟩
  · try simp only [↓reduceIte]
    exact (WP.spec_ok _).2 ⟨Ac, h3.bxi⟩

end
end Fl4Proofs.P1
