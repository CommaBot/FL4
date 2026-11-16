/-
P1: the current-thread frames (`CurR`) of the thread kind's finalisation:
`suspend`, `unbind_notification`, `timer.remove`, `unbind_tcb`,
`complete_yield_to` and `debug_remove`, for any thread `u` (the current
thread, which the finalised thread may be).
-/
import Fl4Proofs.P1.QueueTimerC
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-- `KeepT t` for any `u`, given `t`'s state not blocked when `u = t`. -/
theorem curR_keepT' {u t : U64} {s s' : S} (hu : u ∈ T) (k : KeepT st T Cs Rp Scs Nt t s s')
    (hst : u = t → ¬ BlockedR (L.mem s' (stA t))) : CurR st u s s' := by
  refine ⟨k.curW, k.cscW, Or.inl (k.scf hu), k.act, fun hb => ?_⟩
  by_cases e : u = t
  · have := hst e; subst e; exact this
  · rw [stA_eq, k.fld u hu _ (by simp) (by simp) (by simp) (by simp) (fun e' => absurd e' e), ← stA_eq]; exact hb

theorem sched.suspend.curR {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (t u : obj.Tcb)
    (Q : U64 → U64 → List U64) (R : U64 → List U64) (h : SchedQueuesInv st T Cs Ω H s Q R) (ht : t ∈ T)
    (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hSg : SgOK st Ω Sg s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hna : L.actionW s ≠ t)
    (hyield : L.mem s (yieldA t) ≠ 0#u64 → L.mem s (yieldA t) ∈ Scs) (hu : u ∈ T) :
    sched.suspend st ar s a t ⦃ s' _ => CurR st u s s' ⦄ := by
  have hT := h.tcbs
  have hta := hT t ht
  have hsub := hSg.sub
  unfold sched.suspend
  refine WP.spec_bind (ipc.cancel_ipc.all s a t Q R h ht hB hX hsub) ?_
  rintro ⟨s1, a1⟩ ⟨h1, hB1, hX1, nb1, nr1, hst1, k1, -⟩
  try simp only [WP.uncurry'_pair]
  have c1 : CurR st u s s1 := curR_keepT' hu k1 fun e => by subst e; exact fun hb => hb.elim nb1 nr1
  have hSg1 : SgOK st Ω Sg s1 := ⟨hSg.sub, fun b hb => by rw [k1.ksb]; exact hSg.ks b hb,
    fun o h1' h2' => by rw [k1.ksb]; exact hSg.ksΩ o h1' h2'⟩
  have na1 : L.actionW s1 ≠ t := by
    rcases hst1 with e | ⟨-, e⟩
    · intro ea
      have := (h1.actOK (ea ▸ ht)).1; rw [ea, e] at this; exact not_runnable_inactive this
    · rw [e]; exact hna
  have y1 : L.mem s1 (yieldA t) = L.mem s (yieldA t) :=
    k1.fld t ht _ (by simp) (by simp) (by simp) (by simp) (fun _ => ⟨by simp, by simp⟩)
  have hS1 := hS.keepT hX k1
  have tm1 : TmFr st T Cs Nt s s1 := TmFr.of_keepT k1
  step with obj.Tcb.state.spec as ⟨i, i_post⟩
  -- the fault-IP copy
  refine WP.spec_bind (Pₘ := fun s2 => SchedQueuesInv st T Cs Ω H s2 Q R ∧ ¬ Blocked (L.mem s2 (stA t)) ∧
      L.actionW s2 ≠ t ∧ L.mem s2 (yieldA t) = L.mem s (yieldA t) ∧ BoundInv st T Ac s2 ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z s2 ∧ SgOK st Ω Sg s2 ∧ SCsOK st T Ω Sg Scs Z Ac s2 ∧
      L.mem s2 (stA t) ≠ sched.TS_BLOCKED_ON_REPLY ∧ TmFr st T Cs Nt s s2 ∧ CurR st u s s2) ?_ ?_
  · split
    · step with obj.Tcb.reg.spec as ⟨ip⟩
      refine WP.spec_mono (obj.Tcb.set_reg.fault_ip s1 t ip hta) fun s2 e => ?_
      subst e
      obtain ⟨h2, f2, a2⟩ := field_wr_keep (K := 392#u64) (v := ip) h1 ht (by simp) (by simp) (by simp)
      obtain ⟨hB2, hX2⟩ := bx_field (K := 392#u64) (v := ip) h1 hB1 hX1 hsub ht (by simp) (by simp) (by simp) (by simp)
      refine ⟨h2, ?_, by rw [a2]; exact na1, by rw [← y1]; exact f2 _ (by simp) (by simp) (by simp), hB2, hX2,
        ⟨hSg.sub, fun b hb => by rw [L.ksb_wr]; exact hSg1.ks b hb, fun o h1' h2' => by
          rw [L.ksb_wr]; exact hSg1.ksΩ o h1' h2'⟩, SCsOK.field (K := 392#u64) h1 hS1 hX1 ht (by simp) (by simp) (by simp), ?_,
        tm1.trans (TmFr.wr hT h1.nodes hX1.1 (field_aligned hta (by simp) (by simp))
          (notTmW_field hT h1.nodes (fun n hn => h1.omega _ (hsub _ (hX1.1.ntB n hn).2)) ht (by simp) (by simp))),
        c1.trans (curR_wr_field (K := 392#u64) hT (h1.nodes _ h1.cur) ht hu (by simp) (by simp) (fun _ => by simp)
          (fun _ h => by simp at h))⟩
      · rw [stA_eq, f2 _ (by simp) (by simp) (by simp), ← stA_eq]; exact nb1
      · rw [stA_eq, f2 _ (by simp) (by simp) (by simp), ← stA_eq]; exact nr1
    · exact (WP.spec_ok _).2 ⟨h1, nb1, na1, y1, hB1, hX1, hSg1, hS1, nr1, tm1, c1⟩
  rintro s2 ⟨h2, nb2, na2, y2, hB2, hX2, hSg2, hS2, nr2, tm2, c2⟩
  -- out of the ready queue
  have hc2 := h2.aff t ht
  have hp2 := h2.prio t ht
  have hW2 : ∀ w ∈ Q (L.mem s2 (affA t)) (L.mem s2 (prioA t)), w ∈ T := fun w hw => h2.memT hc2 hp2 hw
  refine WP.spec_bind (WP.spec_and (sched.dequeue.inv s2 t Q R h2 ht)
    (sched.dequeue.foot s2 t _ hT ht hp2 (h2.nodes _ hc2) (h2.nodes _ h2.cur) ((h2.ready _ hc2).1.rel _ hp2)
      (h2.queued t ht).1)) ?_
  rintro s3 ⟨h3, hw3, hinq3⟩
  obtain ⟨hB3, hX3, fr3, -⟩ := bx_qfoot h2 hB2 hX2 hSg2 hW2 hc2 ht p128 hw3
    (fun hf => by rw [hinq3] at hf; split_ifs at hf with e
                  · rw [andn_qq_qq] at hf; exact absurd rfl hf
                  · exact Or.inl hf)
    (fun hf => by rw [hinq3] at hf; split_ifs at hf with e
                  · rw [andn_qq_qr] at hf; exact Or.inr (Or.inl hf)
                  · exact Or.inr (Or.inl hf))
  have hSg3 := hSg2.fr fr3
  have c3 : CurR st u s s3 := by
    obtain ⟨fr3', -, ea3', ec3', -⟩ := qfoot_keep h2 hSg2 hW2 hc2 ht p128 hw3
    exact c2.trans (CurR.of_fr hu fr3' ec3' (Or.inl ea3'))
  have hS3 := hS2.fr fr3
  have tm3 : TmFr st T Cs Nt s s3 := tm2.trans (TmFr.of_fr fr3 hX2.1 h2.nodes)
  have a3 := qfoot_act h2 hW2 hc2 ht (by omega) hw3
  have f3 : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      (K.val ≠ 3480 ∧ K.val ≠ 3488 ∧ K.val ≠ 3496 ∧ K.val ≠ 3504) → K.val ≠ 3592 →
      L.mem s3 (core.num.U64.wrapping_add t K) = L.mem s2 (core.num.U64.wrapping_add t K) :=
    fun K a b c d => field_qfoot hT hW2 (h2.nodes _ hc2) (h2.nodes _ h2.cur) ht hw3 ht a b c (fun _ => d)
  set Q3 := (if (L.mem s2 (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64
       then Function.update Q (L.mem s2 (affA t)) (Function.update (Q (L.mem s2 (affA t))) (L.mem s2 (prioA t))
         ((Q (L.mem s2 (affA t)) (L.mem s2 (prioA t))).erase t)) else Q) with hQ3
  have nQ3 : ∀ c ∈ Cs, ∀ p : U64, p.val < 256 → t ∉ Q3 c p := by
    intro c hc p hp hm
    rw [hQ3] at hm
    split_ifs at hm with hf
    · rcases mem_upd2.1 hm with ⟨-, -, hm⟩ | ⟨hne, hm⟩
      · exact ((h2.ready _ hc2).1.rel _ hp2).nodup.not_mem_erase hm
      · obtain ⟨e1, e2⟩ := h2.inQ c hc p hp t hm
        exact hne ⟨e1.symm, e2.symm⟩
    · exact h2.notQ ht (not_not.1 hf) hc hp hm
  -- out of the release queue
  have hc3 := h3.aff t ht
  have hW3 : ∀ w ∈ R (L.mem s3 (affA t)), w ∈ T := fun w hw => h3.memTR hc3 hw
  refine WP.spec_bind (WP.spec_and (sched.release_remove.inv s3 t Q3 R h3 ht)
    (sched.release_remove.foot s3 t _ hT ht (h3.nodes _ hc3) (h3.nodes _ h3.cur) (h3.release _ hc3)
      (h3.released t ht).1)) ?_
  rintro s4 ⟨h4, hw4, hinq4⟩
  obtain ⟨hB4, hX4, fr4, -⟩ := bx_qfoot h3 hB3 hX3 hSg3 hW3 hc3 ht prel hw4
    (fun hf => by rw [hinq4] at hf; split_ifs at hf with e
                  · rw [andn_qr_qq] at hf; exact Or.inl hf
                  · exact Or.inl hf)
    (fun hf => by rw [hinq4] at hf; split_ifs at hf with e
                  · rw [andn_qr_qr] at hf; exact absurd rfl hf
                  · exact Or.inr (Or.inl hf))
  have hSg4 := hSg3.fr fr4
  have c4 : CurR st u s s4 := by
    obtain ⟨fr4', -, ea4', ec4', -⟩ := qfoot_keep h3 hSg3 hW3 hc3 ht prel hw4
    exact c3.trans (CurR.of_fr hu fr4' ec4' (Or.inl ea4'))
  have hS4 := hS3.fr fr4
  have tm4 : TmFr st T Cs Nt s s4 := tm3.trans (TmFr.of_fr fr4 hX3.1 h3.nodes)
  have a4 := qfoot_act h3 hW3 hc3 ht (by unfold RelOffs; omega) hw4
  have f4 : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      (K.val ≠ 3480 ∧ K.val ≠ 3488 ∧ K.val ≠ 3496 ∧ K.val ≠ 3504) → K.val ≠ 3592 →
      L.mem s4 (core.num.U64.wrapping_add t K) = L.mem s3 (core.num.U64.wrapping_add t K) :=
    fun K a b c d => field_qfoot hT hW3 (h3.nodes _ hc3) (h3.nodes _ h3.cur) ht hw4 ht a b c (fun _ => d)
  set R4 := (if (L.mem s3 (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64
       then Function.update R (L.mem s3 (affA t)) ((R (L.mem s3 (affA t))).erase t) else R) with hR4
  have nR4 : ∀ c ∈ Cs, t ∉ R4 c := by
    intro c hc hm
    rw [hR4] at hm
    split_ifs at hm with hf
    · by_cases e : c = L.mem s3 (affA t)
      · subst e; rw [Function.update_self] at hm
        exact (h3.release _ hc3).nodup.not_mem_erase hm
      · rw [Function.update_of_ne e] at hm
        exact e (h3.inR c hc t hm).symm
    · exact h3.notR ht (not_not.1 hf) hc hm
  have st4 : L.mem s4 (stA t) = L.mem s2 (stA t) := by
    rw [stA_eq, f4 _ (by simp) (by simp) (by simp) (by simp), f3 _ (by simp) (by simp) (by simp) (by simp)]
  have y4 : L.mem s4 (yieldA t) = L.mem s (yieldA t) := by
    rw [← y2]; exact (f4 _ (by simp) (by simp) (by simp) (by simp)).trans (f3 _ (by simp) (by simp) (by simp) (by simp))
  have na4 : L.actionW s4 ≠ t := by rw [a4, a3]; exact na2
  -- `cancel_yield_to`
  unfold schedcontext.cancel_yield_to
  step with obj.Tcb.is_null.spec as ⟨b, b_post⟩
  have hb0 : b = false := by
    rw [b_post]; simp only [decide_eq_false_iff_not]; intro e; exact hta.ne0 (by rw [e]; rfl)
  subst hb0
  simp only [Bool.false_eq_true, ↓reduceIte]
  step with obj.Tcb.yield_to.spec as ⟨yt, yt_post⟩
  refine WP.spec_bind (Pₘ := fun s5 => SchedQueuesInv st T Cs Ω H s5 Q3 R4 ∧ L.mem s5 (stA t) = L.mem s4 (stA t) ∧
      L.actionW s5 = L.actionW s4 ∧ BoundInv st T Ac s5 ∧ XInv st T Cs Ω Sg Rp Scs Nt Z s5 ∧ L.ksb s5 = L.ksb s4 ∧
      SCsOK st T Ω Sg Scs Z Ac s5 ∧ TmFr st T Cs Nt s4 s5 ∧ CurR st u s4 s5) ?_ ?_
  · split
    · rename_i hy
      have hyS : yt ∈ Scs := by rw [yt_post, y4]; exact hyield (by rw [← y4, ← yt_post]; simpa using hy)
      have hyΩ : scYieldFromA yt ∈ Ω := scword_omega hX4.1 hyS (Or.inr rfl)
      step with obj.Sc.set_yield_from.spec as ⟨s5, s5_post⟩
      subst s5_post
      obtain ⟨h5, e5⟩ := wr_omega (v := 0#u64) h4 hyΩ
      have ho := h4.omega _ hyΩ
      obtain ⟨-, -, -, -, -, -, -, e56⟩ := sc_facts hX4.1 hyS
      obtain ⟨fr1, fr2⟩ := scword_facts hX4.1 hyS (Or.inr e56)
      have tmA : TmFr st T Cs Nt s4 (L.wr s4 (scYieldFromA yt) 0#u64) :=
        TmFr.wr hT h4.nodes hX4.1 ho.1 (notTmW_omega hT h4.nodes ho
          (fun n hn e => by
            rw [show scYieldFromA yt = core.num.U64.wrapping_add yt layout.sc.YIELD_FROM from rfl, e56,
              ntfnBtA_val (hX4.1.ntP n hn)] at e
            have := hX4.1.ntOSc n hn yt hyS; have := (sc_facts hX4.1 hyS).1; omega))
      obtain ⟨hB5, -⟩ := bnd_wr (v := 0#u64) h4 hB4 ho.1
        (fun y hy => ⟨by rw [scA_eq]; exact (out_ne_field ho hy (hT y hy) (by simp)).symm,
          by rw [inqA_eq]; exact (out_ne_field ho hy (hT y hy) (by simp)).symm⟩)
        (fun o ho' => (out_ne_node ho h4.cur (h4.nodes _ h4.cur) (by omega)).symm)
        (fun y hy => by rw [stA_eq]; exact (out_ne_field ho hy (hT y hy) (by simp)).symm)
      have hX5 := XInv.wr_yield0 h4 hX4 ho.1 (avoidX_scYield h4 hX4 hsub hyS) (hX4.tn tmA)
      have a5 : L.actionW (L.wr s4 (scYieldFromA yt) 0#u64) = L.actionW s4 := by
        unfold LawfulStore.actionW
        simp only [LawfulStore.cpu_wr, nodeAt_wr]
        exact L.mem_wr_ne (h4.omega _ hyΩ).1 (nodeAt_aligned (h4.nodes _ h4.cur) (by rw [act_val]; omega)
          (by rw [act_val])) (fun e => out_ne_node (h4.omega _ hyΩ) h4.cur (h4.nodes _ h4.cur)
            (by rw [act_val]; omega) e.symm)
      refine WP.spec_mono (obj.Tcb.set_yield_to.spec _ t 0#u64) fun s6 e => ?_
      subst e
      obtain ⟨h6, f6, a6⟩ := field_wr_keep (K := 3472#u64) (v := 0#u64) h5 ht (by simp) (by simp) (by simp)
      have hya5 : Aligned (yieldA t) := field_aligned (K := 3472#u64) hta (by simp) (by simp)
      have fne : ∀ u ∈ T, ∀ K : U64, K.val < 4096 → K.val ≠ 3472 →
          (yieldA t).val ≠ (core.num.U64.wrapping_add u K).val :=
        fun u hu K hK hne e => field_ne (K1 := 3472#u64) hta (h5.tcbs u hu) (by simp) hK (fun _ => by simp; omega)
          (UScalar.eq_of_val_eq e)
      obtain ⟨hB6, -⟩ := bnd_wr (v := 0#u64) h5 hB5 hya5
        (fun y hy => ⟨by rw [scA_eq]; exact fne y hy _ (by simp) (by simp),
          by rw [inqA_eq]; exact fne y hy _ (by simp) (by simp)⟩)
        (fun o ho' e => node_ne_field (h5.nodes _ h5.cur) (by omega) ht hta (K := 3472#u64) (by simp)
          (UScalar.eq_of_val_eq e).symm)
        (fun y hy => by rw [stA_eq]; exact fne _ hy _ (by simp) (by simp))
      have hX6 := XInv.wr_yield0 h5 hX5 hya5 (avoidX_yieldA h5 hX5 hsub ht)
        (hX5.tn_field (v := 0#u64) h5 hsub ht (K := 3472#u64) (by simp) (by simp) (by simp))
      have hS5 := SCsOK.scword (v := 0#u64) h4 hS4 hX4 hyS (Or.inr rfl) (fun _ h0 => absurd rfl h0)
      have tmB : TmFr st T Cs Nt (L.wr s4 (scYieldFromA yt) 0#u64)
          (L.wr (L.wr s4 (scYieldFromA yt) 0#u64) (yieldA t) 0#u64) :=
        TmFr.wr hT h5.nodes hX5.1 (field_aligned (K := 3472#u64) hta (by simp) (by simp))
          (notTmW_field (K := 3472#u64) hT h5.nodes (fun n hn => h5.omega _ (hsub _ (hX5.1.ntB n hn).2)) ht
            (by simp) (by simp))
      refine ⟨h6, ?_, a6.trans a5, hB6, hX6, by simp only [L.ksb_wr],
        SCsOK.field (K := 3472#u64) h5 hS5 hX5 ht (by simp) (by simp) (by simp), tmA.trans tmB,
        (curR_wr_out h4 hu hyΩ).trans (curR_wr_field (K := 3472#u64) hT (h5.nodes _ h5.cur) ht hu (by simp) (by simp)
          (fun _ => by simp) (fun _ h => by simp at h))⟩
      rw [stA_eq, show yieldA t = core.num.U64.wrapping_add t 3472#u64 from rfl,
        f6 _ (by simp) (by simp) (by simp), ← stA_eq, e5 t ht]
    · exact (WP.spec_ok _).2 ⟨h4, rfl, rfl, hB4, hX4, rfl, hS4, TmFr.refl (L := L) _, CurR.refl _ _⟩
  rintro s5 ⟨h5, st5, a5, hB5, hX5, k5, hS5, tm5, c5⟩
  have hnr5 : ¬ Blocked (L.mem s5 (stA t)) := by rw [st5, st4]; exact nb2
  have hrp5 : L.mem s5 (stA t) ≠ sched.TS_BLOCKED_ON_REPLY := by rw [st5, st4]; exact nr2
  refine WP.spec_bind (WP.spec_and (sched.set_thread_state.inv s5 t _ Q3 R4 h5 ht not_blocked_inactive (Or.inr hnr5)
    ⟨fun c hc p hp hm => absurd hm (nQ3 c hc p hp), fun c hc hm => absurd hm (nR4 c hc),
     fun e => absurd e (by rw [a5]; exact na4)⟩) (sched.set_thread_state.state s5 t _ Q3 R4 h5 ht hX5.1 hsub)) ?_
  rintro s6 ⟨h6, e6, k6⟩
  simp only [WP.spec_ok, WP.uncurry'_pair]
  exact (c4.trans c5).trans (curR_keepT' hu k6 fun e => by
    subst e; rw [e6]; exact fun hb => hb.elim not_blocked_inactive inactive_ne.1)

/-- Writes of `CSW` words. -/
theorem curR_of_csw {u : U64} {X : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    {B : U64 → Prop} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hw : WritesIn st s s' B)
    (hB : ∀ b, B b → CSW T Ω b) (hu : u ∈ T) : CurR st u s s' := by
  have hT := h.tcbs
  have hN := h.nodes _ h.cur
  obtain ⟨ecs, esc⟩ := cs_of_writes h hw hB
  have nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem s' (L.nodeAt s' (L.cpu s') o) = L.mem s (L.nodeAt s (L.cpu s) o) := fun o ho h8 => by
    rw [hw.2.1, nodeAt_of_ksb hw.1]
    refine hw.mem_eq (nodeAt_aligned hN ho h8) fun hb => ?_
    rcases hB _ hb with hm | ⟨z, hz, K, hK, -, -, -, -, e⟩
    · exact out_ne_node (h.omega _ hm) h.cur hN ho rfl
    · exact node_ne_field hN ho hz (hT z hz) hK e
  refine ⟨nd _ (by rw [curth0]; omega) (by rw [curth0]), ecs, Or.inl (esc u hu),
    Or.inl (nd _ (by rw [act_val]; omega) (by rw [act_val])), fun hb => ?_⟩
  rw [stA_eq] at hb ⊢
  rw [hw.mem_eq (field_aligned (hT u hu) (by simp) (by simp)) fun hb' => ?_]
  · exact hb
  rcases hB _ hb' with hm | ⟨z, hz, K, hK, -, -, -, hK3, e⟩
  · exact out_ne_field (h.omega _ hm) hu (hT u hu) (by simp) rfl
  · exact field_ne (hT u hu) (hT z hz) (by simp) hK (fun _ => by simp; omega) e

theorem schedcontext.complete_yield_to.curR {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S)
    (a : A) (y u : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hy : y ≠ 0#u64 → y ∈ T) (hu : u ∈ T) :
    schedcontext.complete_yield_to st ar s a y ⦃ s' _ => CurR st u s s' ⦄ :=
  WP.spec_mono (schedcontext.complete_yield_to.cs hA s a y h hy) fun r w => by
    obtain ⟨s', a'⟩ := r
    exact curR_of_csw h.1.choose_spec.choose_spec w (fun _ hb => hb) hu

theorem notification.unbind_notification.curR (s : S) (t u : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (ht : t ∈ T) (hu : u ∈ T) :
    notification.unbind_notification st s t ⦃ s' => CurR st u s s' ⦄ := by
  unfold notification.unbind_notification
  refine WP.spec_bind (obj.Tcb.bound_ntfn.val s t) fun i ei => ?_
  split
  · rename_i hi
    have hi0 : L.mem s (boundA t) ≠ 0#u64 := by rw [← ei]; simpa using hi
    have hin : i ∈ Nt := by rw [ei]; exact h.2.2.1.2.2.bnd t ht hi0
    have h0 := h.1.choose_spec.choose_spec
    have hm : ntfnBtA i ∈ Ω := h.2.2.2.2.sub _ (h.2.2.1.1.ntB i hin).2
    refine WP.spec_bind (obj.Ntfn.set_bound_tcb.wr s i 0#u64) fun s1 e1 => ?_
    subst e1
    have q1 := (ntbt_all h hin Tz.zero).1.choose_spec.choose_spec
    refine WP.spec_mono (obj.Tcb.set_bound_ntfn.wr _ t 0#u64) fun s2 e2 => ?_
    subst e2
    exact (curR_wr_out h0 hu hm).trans (curR_wr_field (K := 3368#u64) h0.tcbs (q1.nodes _ q1.cur) ht hu
      (by simp) (by simp) (fun _ => by simp) (fun _ h => by simp at h))
  · exact (WP.spec_ok _).2 (CurR.refl _ _)

theorem timer.remove.curR (s : S) (t u : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T)
    (hu : u ∈ T) : timer.remove st s t ⦃ s' => CurR st u s s' ⦄ :=
  WP.spec_mono (timer.remove.tf2 (s0 := s) s t (TF2.start h) ht) fun s' ⟨⟨_, _, an, tk⟩, ecs⟩ =>
    ⟨an.2.2, ecs, Or.inl (by rw [scA_eq]; exact tk u hu _ (by simp) (by simp) (by simp)),
      Or.inl an.1, fun hb => by rw [stA_eq, tk u hu _ (by simp) (by simp) (by simp), ← stA_eq]; exact hb⟩

theorem schedcontext.unbind_tcb.curR (s : S) (sc u : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hsc : sc ∈ Scs) (hsc0 : sc ≠ 0#u64) (hna : L.mem s (scTcbA sc) ≠ 0#u64 → L.actionW s ≠ L.mem s (scTcbA sc))
    (hidle : L.mem s (scTcbA sc) ≠ 0#u64 → L.idleW s ≠ L.mem s (scTcbA sc)) (hu : u ∈ T) :
    schedcontext.unbind_tcb st s sc ⦃ s' => CurR st u s s' ⦄ := by
  unfold schedcontext.unbind_tcb
  step with obj.Sc.tcb.spec as ⟨t, et⟩
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  split
  · rename_i hb
    exact (WP.spec_ok _).2 (CurR.refl _ _)
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
      L.cscW s1 = L.cscW s ∧ CurR st u s s1) ?_ ?_
  · split
    · rename_i hbt
      obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
      refine WP.spec_mono (WP.spec_and (sched.reschedule_required.schX (Sg := Sg) s Q R h0 hB hSg)
        (sched.reschedule_required.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) s h0)) ?_
      rintro s1 ⟨⟨⟨Q1, R1, h1⟩, hB1, f1, ea1, ec1, -, ei1, -⟩, fw1⟩
      refine ⟨⟨⟨Q1, R1, h1⟩, hB1, hX.fr f1, hS.fr f1, hSg.fr f1⟩, fw1, ?_, fun _ => by rw [ea1]; simp, ei1,
        f1.sig _ (hX.1.fixW sc hsc).1, Or.inr ea1, f1.csc, CurR.of_fr hu f1 ec1 (Or.inr ea1)⟩
      rw [ea1]; exact fun e => notT_small h0.tcbs (by simp) (e ▸ htT)
    · rename_i hbt
      have hne : t ≠ t1 := fun e => hbt (by rw [eb1, decide_eq_true_eq]; exact e)
      exact (WP.spec_ok _).2 ⟨h, Foot.refl _, hna0, fun e => absurd (by rw [et1]; exact e.symm) hne, rfl, rfl,
        Or.inl rfl, rfl, CurR.refl _ _⟩
  rintro s1 ⟨⟨⟨Q1, R1, h1⟩, hB1, hX1, hS1, hSg1⟩, fw1, na1, cr1, ei1, sc1, ac1, cs1, c1⟩
  -- dequeue
  have hc1 := h1.aff t htT
  have hp1 := h1.prio t htT
  refine WP.spec_bind (WP.spec_and (WP.spec_and (sched.dequeue.sch (Sg := Sg) s1 t Q1 R1 h1 hB1 hSg1 htT)
    (sched.dequeue.foot s1 t _ h1.tcbs htT hp1 (h1.nodes _ hc1) (h1.nodes _ h1.cur) ((h1.ready _ hc1).1.rel _ hp1)
      (h1.queued t htT).1)) (sched.dequeue.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) s1 t h1 htT)) ?_
  rintro s2 ⟨⟨⟨⟨⟨Q2, R2, h2⟩, hB2, f2⟩, ea2, ec2⟩, hw2, iq2⟩, fw2⟩
  have hW1 : ∀ w ∈ Q1 (L.mem s1 (affA t)) (L.mem s1 (prioA t)), w ∈ T := fun w hw => h1.memT hc1 hp1 hw
  obtain ⟨-, -, -, -, ei2⟩ := qfoot_keep (Sg := Sg) h1 hSg1 hW1 hc1 htT p128 hw2
  have c2 := c1.trans (CurR.of_fr hu f2 ec2 (Or.inl ea2))
  have hc2 := h2.aff t htT
  refine WP.spec_bind (WP.spec_and (WP.spec_and (sched.release_remove.sch (Sg := Sg) s2 t Q2 R2 h2 hB2
      (hSg1.fr f2) htT)
    (sched.release_remove.foot s2 t _ h2.tcbs htT (h2.nodes _ hc2) (h2.nodes _ h2.cur) (h2.release _ hc2)
      (h2.released t htT).1)) (sched.release_remove.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) s2 t h2 htT)) ?_
  rintro s3 ⟨⟨⟨⟨⟨Q3, R3, h3⟩, hB3, f3⟩, ea3, ec3, -⟩, hw3, iq3⟩, fw3⟩
  have c3 := c2.trans (CurR.of_fr hu f3 ec3 (Or.inl ea3))
  have hX3 := (hX1.fr f2).fr f3
  have hS3 := (hS1.fr f2).fr f3
  have hSg3 := (hSg1.fr f2).fr f3
  have hW3 : ∀ w ∈ R2 (L.mem s2 (affA t)), w ∈ T := fun w hw => h2.memTR hc2 hw
  -- `t` is in no queue now
  have iq3' : L.mem s3 (inqA t) = (if (L.mem s2 (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64
      then L.mem s2 (inqA t) &&& ~~~sched.Q_RELEASE else L.mem s2 (inqA t)) := iq3
  have q2 : (L.mem s2 (inqA t) &&& sched.Q_QUEUED) = 0#u64 := by
    rw [iq2]; split_ifs with e
    · exact andn_qq_qq _
    · exact not_not.1 e
  have qq3 : (L.mem s3 (inqA t) &&& sched.Q_QUEUED) = 0#u64 := by
    rw [iq3']; split_ifs
    · rw [andn_qr_qq]; exact q2
    · exact q2
  have qr3 : (L.mem s3 (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by
    rw [iq3']
    split_ifs with e
    · exact andn_qr_qr _
    · exact not_not.1 e
  have na3 : L.actionW s3 ≠ t := by rw [ea3, ea2]; exact na1
  obtain ⟨-, -, -, -, ei3⟩ := qfoot_keep (Sg := Sg) h2 (hSg1.fr f2) hW3 hc2 htT prel hw3
  have id3 : L.idleW s3 ≠ t := by rw [ei3, ei2, ei1]; exact hid0
  have tc3 : L.mem s3 (scTcbA sc) = t := by
    rw [f3.sig _ (hX1.1.fixW sc hsc).1, f2.sig _ (hX1.1.fixW sc hsc).1, sc1, ← et]
  refine WP.spec_bind (obj.Tcb.set_sc.wr s3 t 0#u64) fun s4 e4 => ?_
  subst e4
  have c4 := c3.trans (curR_wr_field (K := 3464#u64) (v := 0#u64) h3.tcbs (h3.nodes _ h3.cur) htT hu (by simp)
    (by simp) (fun _ => by simp) (fun _ _ => rfl))
  obtain ⟨k1, kB, -, k3, ktx, k4, k5, ka, kc, ki, -, -, kΩ, ks0⟩ :=
    clear_sc_state h3 hB3 hX3 hS3 hSg3 htT ⟨qq3, qr3⟩ id3
  have hB4 := kB na3 (fun e => by rw [ka, ea3, ea2]; exact cr1 (by rw [← ec2, ← ec3, ← kc]; exact e))
  have ktx' : TScX st Scs sc (L.wr s3 (scA t) 0#u64) := by
    have e : L.mem s3 (scA t) = sc := by
      have := hX3.2.2.tsc sc hsc hsc0 (by rw [tc3]; exact fun e0 => (h3.tcbs t htT).ne0 (by rw [e0]; rfl))
      rwa [tc3] at this
    rw [e] at ktx; exact ktx
  have tc4 : L.mem (L.wr s3 (scA t) 0#u64) (scTcbA sc) = t := by
    rw [kΩ _ (hSg3.sub _ (hX3.1.fixW sc hsc).1)]; exact tc3
  have fw4 : Foot st T Cs Sg Scs Z ∅ s3 (L.wr s3 (scA t) 0#u64) := by
    rw [scA_eq]; exact foot_field h3.tcbs htT (by simp) (by simp) (by simp) (by simp)
  refine WP.spec_mono (obj.Sc.set_tcb.wr _ sc 0#u64) fun s5 e5 => ?_
  subst e5
  exact c4.trans (curR_wr_out k1 hu (hSg3.sub _ (hX3.1.fixW sc hsc).1))

/-- A node word other than the current core's current-thread, action and
current-SC words. -/
theorem curR_wr_node {u : U64} {s : S} {c o v : U64} (hT : TcbPlaced T) (hN : NodePlaced st T s c)
    (hN' : NodePlaced st T s (L.cpu s)) (hu : u ∈ T) (ho : o.val < 4288) (h8 : o.val % 8 = 0)
    (hne : c = L.cpu s → o.val ≠ 0 ∧ o.val ≠ 16 ∧ o.val ≠ 24) :
    CurR st u s (L.wr s (L.nodeAt s c o) v) := by
  have ha := nodeAt_aligned hN ho h8
  have nn : ∀ o' : U64, (o'.val = 0 ∨ o'.val = 16 ∨ o'.val = 24) →
      L.mem (L.wr s (L.nodeAt s c o) v) (L.nodeAt s (L.cpu s) o') = L.mem s (L.nodeAt s (L.cpu s) o') :=
    fun o' ho' => L.mem_wr_ne ha (nodeAt_aligned hN' (by omega) (by omega))
      (node_ne_node hN hN' ho (by omega) (fun e => by have := hne e; omega))
  have nf : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem (L.wr s (L.nodeAt s c o) v) (core.num.U64.wrapping_add u K) = L.mem s (core.num.U64.wrapping_add u K) :=
    fun K hK hK8 => L.mem_wr_ne ha (field_aligned (hT u hu) hK hK8)
      (fun e => node_ne_field hN ho hu (hT u hu) hK (UScalar.eq_of_val_eq e))
  refine ⟨?_, ?_, Or.inl (by rw [scA_eq]; exact nf _ (by simp) (by simp)), Or.inl ?_,
    fun hb => by rw [stA_eq, nf _ (by simp) (by simp), ← stA_eq]; exact hb⟩
  · unfold LawfulStore.curW; rw [nodeAt_wr, L.cpu_wr]; exact nn _ (by rw [curth0]; simp)
  · unfold LawfulStore.cscW LawfulStore.nodeA; rw [nodeAt_wr, L.cpu_wr]
    exact nn _ (by simp [layout.node.CUR_SC])
  · unfold LawfulStore.actionW; rw [nodeAt_wr, L.cpu_wr]; exact nn _ (by rw [act_val]; simp)

theorem objects.debug_remove.curR (s : S) (t u : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T)
    (hu : u ∈ T) : objects.debug_remove st s t ⦃ s' => CurR st u s s' ⦄ := by
  have hc : L.mem s (affA t) ∈ Cs := h.1.choose_spec.choose_spec.aff t ht
  have hTm := h.2.2.1.2.2.tm
  have h0 := h.1.choose_spec.choose_spec
  have hT := h0.tcbs
  unfold objects.debug_remove
  step with obj.Tcb.affinity.spec as ⟨cpu, ecpu⟩
  step with obj.node_get.spec as ⟨hd, ehd⟩
  step with obj.Tcb.debug_next.val as ⟨nx, enx⟩
  step with obj.Tcb.debug_prev.val as ⟨pv, epv⟩
  have hcpu : cpu ∈ Cs := by rw [ecpu]; exact hc
  have tnx : Tz T nx := by rw [enx]; exact hTm.dn t ht
  have tpv : Tz T pv := by rw [epv]; exact hTm.dp t ht
  refine WP.spec_bind (Pₘ := fun s1 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s1 ∧ CurR st u s s1) ?_ ?_
  · split
    · exact WP.spec_mono (obj.node_set.spec s cpu _ nx) fun s1 e => by
        subst e
        exact ⟨(dbgN_all h hcpu tnx).1, curR_wr_node hT (h0.nodes _ hcpu) (h0.nodes _ h0.cur) hu
          (by rw [debug_val]; omega) (by rw [debug_val]) (fun _ => by rw [debug_val]; omega)⟩
    · split
      · rename_i _ hp
        have hpT : pv ∈ T := tpv.ne0 (by simpa using hp)
        exact WP.spec_mono (obj.Tcb.set_debug_next.wr s pv nx) fun s1 e => by
          subst e
          exact ⟨(dbg_next_all h hpT tnx).1, curR_wr_field (K := 3576#u64) hT (h0.nodes _ h0.cur) hpT hu
            (by simp) (by simp) (fun _ => by simp) (fun _ h => by simp at h)⟩
      · exact (WP.spec_ok _).2 ⟨h, CurR.refl _ _⟩
  intro s1 ⟨h1, c1⟩
  have q1 := h1.1.choose_spec.choose_spec
  refine WP.spec_bind (Pₘ := fun s2 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s2 ∧ CurR st u s s2) ?_ ?_
  · split
    · rename_i hn
      have hnT : nx ∈ T := tnx.ne0 (by simpa using hn)
      exact WP.spec_mono (obj.Tcb.set_debug_prev.wr s1 nx pv) fun s2 e => by
        subst e
        exact ⟨(dbg_prev_all h1 hnT tpv).1, c1.trans (curR_wr_field (K := 3584#u64) hT (q1.nodes _ q1.cur) hnT hu
          (by simp) (by simp) (fun _ => by simp) (fun _ h => by simp at h))⟩
    · exact (WP.spec_ok _).2 ⟨h1, c1⟩
  intro s2 ⟨h2, c2⟩
  have q2 := h2.1.choose_spec.choose_spec
  refine WP.spec_bind (obj.Tcb.set_debug_prev.wr s2 t 0#u64) fun s3 e3 => ?_
  subst e3
  have h3 := (dbg_prev_all h2 ht Tz.zero).1
  have q3 := h3.1.choose_spec.choose_spec
  refine WP.spec_mono (obj.Tcb.set_debug_next.wr _ t 0#u64) fun s4 e4 => ?_
  subst e4
  exact (c2.trans (curR_wr_field (K := 3584#u64) hT (q2.nodes _ q2.cur) ht hu (by simp) (by simp) (fun _ => by simp)
    (fun _ h => by simp at h))).trans (curR_wr_field (K := 3576#u64) hT (q3.nodes _ q3.cur) ht hu (by simp) (by simp)
      (fun _ => by simp) (fun _ h => by simp at h))

/-- **The thread kind's frame**, for any thread `u`. -/
theorem fin_thread.curR {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (p u : U64)
    (fin : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hp : p ∈ T) (hna : L.actionW s ≠ p)
    (hidle : L.idleW s ≠ p)
    (hv0 : L.mem s (core.num.U64.wrapping_add p 3664#u64) = 0#u64) (hu : u ∈ T) :
    objects.finalise_cap_object st ar s a (.Thread p) fin ⦃ r => CurR st u s r.2.1 ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  split
  swap
  · exact (WP.spec_ok _).2 (CurR.refl _ _)
  have hStart := h
  obtain ⟨⟨Q0, R0, hq0⟩, hb0, hx0, hs0, hg0⟩ := hStart
  refine WP.spec_bind (WP.spec_and (smp.remote_tcb_stall.blk hA s a p h)
    (smp.remote_tcb_stall.all hA s a p hq0 hb0 hx0 hs0 hg0)) ?_
  rintro ⟨s1, a1⟩ ⟨⟨h1, f1, ea1, -, ei1⟩, _, _, _, _, _, ea1', ec1', _, ecs1, keep, _⟩
  try simp only [WP.uncurry'_pair]
  have c1 : CurR st u s s1 := ⟨ec1', ecs1, Or.inl (by rw [scA_eq]; exact keep u hu _ (by simp) (by simp)),
    Or.inl ea1', fun hb => by rw [stA_eq, keep u hu _ (by simp) (by simp), ← stA_eq]; exact hb⟩
  refine WP.spec_bind (vcpu.detach_none ar s1 a1 p (by
    rw [keep p hp 3664#u64 (by simp) (by simp)]; exact hv0)) ?_
  intro r hr
  subst r
  try dsimp only
  refine WP.spec_bind (WP.spec_and (notification.unbind_notification.blkF s1 p h1 hp)
    (notification.unbind_notification.curR s1 p u h1 hp hu)) fun s2 ⟨⟨h2, f2, n2⟩, c2⟩ => ?_
  refine WP.spec_bind (WP.spec_and (timer.remove.tf (s0 := s2) s2 p (TF.start h2) hp)
    (timer.remove.curR s2 p u h2 hp hu)) fun s3 ⟨⟨h3, f3, n3, k3⟩, c3⟩ => ?_
  have ea3 : L.actionW s3 = L.actionW s := by rw [n3.1, n2.1, ea1]
  have ei3 : L.idleW s3 = L.idleW s := by rw [n3.2.1, n2.2.1, ei1]
  have c13 := (c1.trans c2).trans c3
  step with obj.Tcb.sc.spec as ⟨i, ei⟩
  step with obj.Sc.is_null.spec as ⟨b, eb⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧
      L.actionW r.1 ≠ p ∧ CurR st u s r.1) ?_ ?_
  · split
    · exact (WP.spec_ok _).2 ⟨h3, by rw [ea3]; exact hna, c13⟩
    rename_i hb
    have hi0 : i ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    obtain ⟨hiS, hit, -⟩ := h3.2.2.1.2.2.bound p hp (by rw [← ei]; exact hi0)
    rw [← ei] at hiS hit
    refine WP.spec_bind (WP.spec_and (schedcontext.unbind_tcb.blk s3 i h3 hiS hi0
      (fun _ => by rw [hit, ea3]; exact hna) (fun _ => by rw [hit, ei3]; exact hidle))
      (schedcontext.unbind_tcb.curR s3 i u h3 hiS hi0 (fun _ => by rw [hit, ea3]; exact hna)
        (fun _ => by rw [hit, ei3]; exact hidle) hu)) fun s5 ⟨hh5, c5⟩ => ?_
    obtain ⟨h5, f5, ea5, _⟩ := hh5
    have na5 : L.actionW s5 ≠ p := by
      rcases ea5 with e | e
      · rw [e, ea3]; exact hna
      · rw [e]; exact fun e' => notT_small h5.1.choose_spec.choose_spec.tcbs (by simp) (e' ▸ hp)
    step with obj.Sc.yield_from.val as ⟨y, ey⟩
    step with obj.Tcb.is_null.spec as ⟨b1, eb1⟩
    split
    · exact (WP.spec_ok _).2 ⟨h5, na5, c13.trans c5⟩
    · have hiS5 : i ∈ Scs := hiS
      have hy : y ≠ 0#u64 → y ∈ T := fun hy0 => by
        rw [ey]; exact h5.2.2.1.2.2.yt.2.2 i hiS5 (by rw [← ey]; exact hy0)
      refine WP.spec_mono (WP.spec_and (schedcontext.complete_yield_to.blk hA s5 a1 y h5 hy)
        (schedcontext.complete_yield_to.curR hA s5 a1 y u h5 hy hu)) ?_
      rintro ⟨s6, a6⟩ ⟨⟨h6, f6, n6⟩, c6⟩
      exact ⟨h6, by rw [n6.1]; exact na5, (c13.trans c5).trans c6⟩
  rintro ⟨s4, a2⟩ ⟨h4, na4, c4⟩
  try simp only [WP.uncurry'_pair]
  obtain ⟨⟨Q, R, q4⟩, hB4, hX4, hS4, hSg4⟩ := id h4
  refine WP.spec_bind (WP.spec_and (sched.suspend.blk s4 a2 p h4 hp na4)
    (sched.suspend.curR s4 a2 p u Q R q4 hp hB4 hX4 hSg4 hS4 na4 (hX4.2.2.yt.2.1 p hp) hu)) ?_
  rintro ⟨s5, a3⟩ ⟨⟨h5, f5⟩, c5⟩
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (objects.debug_remove.curR s5 p u h5 hp hu) fun s6 c6 => ?_
  refine WP.spec_bind (hA.fpu_release a3 p) fun a4 _ => ?_
  refine WP.spec_bind (P0.obj.Tcb.slot.p0 p _) fun s7 _ => ?_
  exact (WP.spec_ok _).2 ((c4.trans c5).trans c6)

/-! ## The SC kind -/

theorem schedcontext.unbind_reply.curR (s : S) (c u : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hc : c ≠ 0#u64 → c ∈ Scs) (hu : u ∈ T) :
    schedcontext.unbind_reply st s c ⦃ s' => CurR st u s s' ⦄ := by
  unfold schedcontext.unbind_reply
  step with obj.Sc.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 (CurR.refl _ _)
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
    exact (curR_wr_out h.1.choose_spec.choose_spec hu (hsub _ (hO.nextW hiR))).trans
      (curR_wr_out h1.1.choose_spec.choose_spec hu (hsub _ (hO.repW c hcS)))
  · exact (WP.spec_ok _).2 (CurR.refl _ _)

theorem schedcontext.unbind_all_tcbs.curR {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (p u : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hp : p ∈ Scs) (hp0 : p ≠ 0#u64)
    (hna : L.mem s (scTcbA p) ≠ 0#u64 → L.actionW s ≠ L.mem s (scTcbA p))
    (hidle : L.mem s (scTcbA p) ≠ 0#u64 → L.idleW s ≠ L.mem s (scTcbA p)) (hu : u ∈ T) :
    schedcontext.unbind_all_tcbs st ar s a p ⦃ s' _ => CurR st u s s' ⦄ := by
  obtain ⟨⟨Q0, R0, hq0⟩, hb0, hx0, hs0, hg0⟩ := id h
  unfold schedcontext.unbind_all_tcbs
  step with obj.Sc.tcb.spec as ⟨i, ei⟩
  split
  · refine WP.spec_bind (WP.spec_and (smp.remote_tcb_stall.blkS hA s a i p h hp)
      (smp.remote_tcb_stall.all hA s a i hq0 hb0 hx0 hs0 hg0)) ?_
    rintro ⟨s1, a1⟩ ⟨⟨h1, f1, ea1, ei1, k1⟩, _, _, _, _, _, ea1', ec1', _, ecs1, keep, _⟩
    try simp only [WP.uncurry'_pair]
    have c1 : CurR st u s s1 := ⟨ec1', ecs1, Or.inl (by rw [scA_eq]; exact keep u hu _ (by simp) (by simp)),
      Or.inl ea1', fun hb => by rw [stA_eq, keep u hu _ (by simp) (by simp), ← stA_eq]; exact hb⟩
    refine WP.spec_bind (schedcontext.unbind_tcb.curR s1 p u h1 hp hp0 (fun h0 => by
        rw [k1.1] at h0 ⊢; rw [ea1]; exact hna h0)
      (fun h0 => by rw [k1.1] at h0 ⊢; rw [ei1]; exact hidle h0) hu) fun s2 c2 => ?_
    exact (WP.spec_ok _).2 (c1.trans c2)
  · exact (WP.spec_ok _).2 (CurR.refl _ _)

/-- **The SC kind's frame**, for any thread `u`. -/
theorem fin_sc.curR {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (p x u : U64)
    (fin : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hp : p ∈ Scs) (hp0 : p ≠ 0#u64)
    (hna : L.mem s (scTcbA p) ≠ 0#u64 → L.actionW s ≠ L.mem s (scTcbA p))
    (hidle : L.mem s (scTcbA p) ≠ 0#u64 → L.idleW s ≠ L.mem s (scTcbA p)) (hu : u ∈ T) :
    objects.finalise_cap_object st ar s a (.SchedContext p x) fin ⦃ r => CurR st u s r.2.1 ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  split
  swap
  · exact (WP.spec_ok _).2 (CurR.refl _ _)
  refine WP.spec_bind (WP.spec_and (schedcontext.unbind_all_tcbs.blk hA s a p h hp hp0 hna hidle)
    (schedcontext.unbind_all_tcbs.curR hA s a p u h hp hp0 hna hidle hu)) ?_
  rintro ⟨s1, a1⟩ ⟨⟨h1, -⟩, c1⟩
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (WP.spec_and (schedcontext.unbind_ntfn.blk s1 p h1 fun _ => hp)
    (schedcontext.unbind_ntfn.cura s1 p h1 fun _ => hp)) fun s2 ⟨⟨h2, _⟩, c2⟩ => ?_
  refine WP.spec_bind (WP.spec_and (schedcontext.unbind_reply.blk s2 p p h2 (fun _ => hp) hp)
    (schedcontext.unbind_reply.curR s2 p u h2 (fun _ => hp) hu)) fun s3 ⟨⟨h3, _⟩, c3⟩ => ?_
  have c13 := (c1.trans (CurR.of_curF hu c2.1 (Or.inl c2.2))).trans c3
  refine WP.spec_bind (obj.Sc.yield_from.val s3 p) fun yf eyf => ?_
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧ CurR st u s r.1) ?_ ?_
  · split
    · exact (WP.spec_ok _).2 ⟨h3, c13⟩
    · have hy : yf ≠ 0#u64 → yf ∈ T := fun hy0 => by
        rw [eyf]; exact h3.2.2.1.2.2.yt.2.2 p hp (by rw [← eyf]; exact hy0)
      refine WP.spec_mono (WP.spec_and (schedcontext.complete_yield_to.blk hA s3 a1 yf h3 hy)
        (schedcontext.complete_yield_to.curR hA s3 a1 yf u h3 hy hu)) ?_
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
  exact (WP.spec_ok _).2 ((c4.trans (curR_wr_out q4 hu (hsub4 _ (hO4.mxW p hp)))).trans
    (curR_wr_out q5 hu (spor_omega hO4 hp)))

/-! ## The thread and SC kinds' finalisations -/

theorem Cur0.na {s0 s : S} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) : ∀ y ∈ T, L.actionW s ≠ y := by
  obtain ⟨-, -, -, -, -, -, na, -⟩ := h; exact na

theorem tcb_slotIdxW {Ω Sg : Set U64} {t i : U64} (hT : TcbPlaced T) (ht : t ∈ T) (hi : i.val < 6) :
    SlotW T Ω Sg (slotIdx t i) := by
  have ha := hT t ht
  have := ha.align; have := ha.fits
  refine ⟨?_, fun o ho h8 => Or.inl ⟨t, ht, core.num.U64.wrapping_add (core.num.U64.wrapping_mul i 32#u64) o, ?_, ?_⟩⟩
  · simp [slotIdx, Aligned, core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def,
      U64.numBits]
    omega
  · simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]; omega
  · apply UScalar.eq_of_val_eq
    simp [slotIdx, core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]
    omega

theorem tcb_zombieOK {Ω Sg : Set U64} {p : U64} (hT : TcbPlaced T) (hp : p ∈ T) :
    DelCapOK T Ω Sg H Rp Nt (.Zombie p capability.ZOMBIE_TCB 6#u64) := by
  have h0 : slotIdx p 0#u64 = p := by
    apply UScalar.eq_of_val_eq
    simp [slotIdx, core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, fun p' t' n e => ?_, ?_⟩ <;> try (intros; simp_all; done)
  simp only [capability.Cap.Zombie.injEq] at e
  obtain ⟨rfl, rfl, rfl⟩ := e
  exact ⟨h0 ▸ tcb_slotIdxW hT hp (by simp), fun i hi => tcb_slotIdxW hT hp (by simpa using hi)⟩

/-- **The thread kind's finalisation** (`FinGaps.thread`). -/
theorem finGap_thread {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) :
    FinGap st ar T Cs Ω H Sg Rp Scs Nt Z fun c => ∃ x1, c = .Thread x1 := by
  intro Ac s0 s a c fin h hc hpl ⟨p, e⟩
  subst e
  have hp := hc.2.2.2.2.2 p rfl
  obtain ⟨hid, hv0⟩ := hpl.1 p rfl
  obtain ⟨Ac', hb⟩ := h.bxi
  have hb' := hb.blk
  have hT := hb.1.choose_spec.choose_spec.tcbs
  have hct : L.curW s ∈ T := hb.1.choose_spec.choose_spec.curT
  have hna := h.na p hp
  rw [fin_cap_eq_obj (by simp)]
  refine WP.spec_mono (WP.spec_and (WP.spec_and (fin_thread.rem hA s a p fin)
    (fin_thread.blk hA s a p fin hb' hp hna (Ne.symm hid) hv0))
    (fin_thread.curR hA s a p (L.curW s) fin hb' hp hna (Ne.symm hid) hv0 hct)) ?_
  rintro ⟨⟨r1, r2⟩, s', a'⟩ ⟨⟨e, hb2, -⟩, ec, ecs, esc, ea, enb⟩
  simp only at e hb2 ec ecs esc ea enb ⊢
  refine ⟨Cur0.mk h (BlkOK.bxi hb2) ec ecs esc ea (Or.inr (enb h.nb)), ?_, ?_⟩
  · simp only [Prod.mk.injEq] at e
    rw [e.1]; split
    · exact tcb_zombieOK hT hp
    · exact DelCapOK.null
  · simp only [Prod.mk.injEq] at e
    rw [e.2]; exact DelCapOK.null

/-- **The SC kind's finalisation** (`FinGaps.sc`). -/
theorem finGap_sc {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) :
    FinGap st ar T Cs Ω H Sg Rp Scs Nt Z fun c => ∃ x1 x2, c = .SchedContext x1 x2 := by
  intro Ac s0 s a c fin h hc hpl ⟨p, x, e⟩
  subst e
  obtain ⟨hpS, hp0, hid⟩ := hpl.2 p x rfl
  obtain ⟨Ac', hb⟩ := h.bxi
  have hb' := hb.blk
  have hct : L.curW s ∈ T := hb.1.choose_spec.choose_spec.curT
  have hna : L.mem s (scTcbA p) ≠ 0#u64 → L.actionW s ≠ L.mem s (scTcbA p) := fun h0 =>
    h.na _ (hb.2.2.1.2.2.yt.1 p hpS h0)
  rw [fin_cap_eq_obj (by simp)]
  refine WP.spec_mono (WP.spec_and (WP.spec_and (fin_sc.rem hA s a p x fin)
    (fin_sc.blk hA s a p x fin hb' hpS hp0 hna hid))
    (fin_sc.curR hA s a p x (L.curW s) fin hb' hpS hp0 hna hid hct)) ?_
  rintro ⟨⟨r1, r2⟩, s', a'⟩ ⟨⟨e, Ac2, -, hb2, -⟩, ec, ecs, esc, ea, enb⟩
  simp only at e hb2 ec ecs esc ea enb ⊢
  cases e
  exact ⟨Cur0.mk h (BlkOK.bxi hb2) ec ecs esc ea (Or.inr (enb h.nb)), DelCapOK.null, DelCapOK.null⟩

/-! ## The kinds still named -/

/-- The finalisations P1 does not prove, one shape (`FinGap`): the
VCPU/EPT/I/O-port kinds (with EPT frames). -/
structure FinGaps (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) : Prop where
  arch : FinGap st ar T Cs Ω H Sg Rp Scs Nt Z fun c => (∃ x1, c = .Vcpu x1) ∨
    (∃ x1 x2 x3 x4 x5, c = .Ept x1 x2 x3 x4 x5) ∨ (∃ x1 x2 x3, c = .IoPort x1 x2 x3) ∨
    (∃ x1 x2 x3 x4 x5 x6 x7, c = .Frame x1 x2 x3 x4 x5 true x6 x7)

/-- `FinGaps` with the proved kinds gives every kind (`FinKinds`). -/
theorem FinGaps.kinds {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    (P : DelPlace st T Cs Ω H Sg Rp Scs Nt Z V) (G : FinGaps st ar T Cs Ω H Sg Rp Scs Nt Z) :
    FinKinds st ar T Cs Ω H Sg Rp Scs Nt Z :=
  ⟨finGap_ep, finGap_ntfn, finGap_reply hA, finGap_sc hA, finGap_thread hA, finGap_irq hA P, G.arch⟩

end

end Fl4Proofs.P1
