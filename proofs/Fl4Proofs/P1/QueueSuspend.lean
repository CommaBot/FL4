/-
P1: `suspend` (seL4 `suspend`, MCS) keeps the queue invariant together with
`BoundInv` (the threads the scheduler can make current are bound) and
`XInv` (reply objects and SCs).
-/
import Fl4Proofs.P1.QueueObjs
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64}
variable {Cs Sg Rp Scs : Set U64} {Z : U64 → Nat}

/-- A write away from the words `BoundInv` and `XInv` read. -/
theorem bx_wr {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {a v : U64}
    (h : SchedQueuesInvX st T Cs Ω X s Q R) (hB : BoundInv st T s) (hX : XInv st T Cs Ω Sg Rp Scs Z s)
    (ha : Aligned a) (hP : ¬ Prot T Rp Scs a) (hsi : ∀ y ∈ T, a.val ≠ (scA y).val ∧ a.val ≠ (inqA y).val)
    (hn : ∀ o : U64, (o.val = 0 ∨ o.val = 8 ∨ o.val = 16 ∨ o.val = 24) → a.val ≠ (L.nodeAt s (L.cpu s) o).val) :
    BoundInv st T (L.wr s a v) ∧ XInv st T Cs Ω Sg Rp Scs Z (L.wr s a v) := by
  have hN' := h.nodes _ h.cur
  have nd : ∀ o : U64, (o.val = 0 ∨ o.val = 8 ∨ o.val = 16 ∨ o.val = 24) →
      L.mem (L.wr s a v) (L.nodeAt (L.wr s a v) (L.cpu (L.wr s a v)) o) = L.mem s (L.nodeAt s (L.cpu s) o) :=
    fun o ho => by
      simp only [LawfulStore.cpu_wr, nodeAt_wr]
      exact L.mem_wr_ne ha (nodeAt_aligned hN' (by omega) (by omega)) (hn o ho)
  have hsc : ∀ y ∈ T, L.mem (L.wr s a v) (scA y) = L.mem s (scA y) := fun y hy =>
    L.mem_wr_ne ha (scA_aligned (h.tcbs y hy)) (hsi y hy).1
  have hiq : ∀ y ∈ T, L.mem (L.wr s a v) (inqA y) = L.mem s (inqA y) := fun y hy =>
    L.mem_wr_ne ha (by rw [inqA_eq]; exact field_aligned (h.tcbs y hy) (by simp) (by simp)) (hsi y hy).2
  have ea : L.actionW (L.wr s a v) = L.actionW s := by
    unfold LawfulStore.actionW; exact nd _ (by rw [act_val]; omega)
  have ec : L.curW (L.wr s a v) = L.curW s := by unfold LawfulStore.curW; exact nd _ (by rw [curth0]; omega)
  have ei : L.idleW (L.wr s a v) = L.idleW s := by unfold LawfulStore.idleW; exact nd _ (by rw [idle8]; omega)
  refine ⟨hB.mk' hsc (fun y hy hf => Or.inl (by rw [← hiq y hy]; exact hf))
    (fun y hy hf => Or.inr (Or.inl (by rw [← hiq y hy]; exact hf))) (fun haT => ?_)
    (by rw [ei]; exact ⟨h.idleT, hB.idle⟩) (fun h0 => ?_), ?_⟩
  · rw [ea] at haT ⊢; exact ⟨haT, hB.act haT⟩
  · rw [ea] at h0; rw [ec]; exact ⟨h.curT, hB.resume h0⟩
  · refine hX.writes h.tcbs (writesIn_wr (v := v) ha) (fun b hb => hb ▸ hP) ?_
    unfold LawfulStore.cscW LawfulStore.nodeA
    rw [nd _ (by simp [layout.node.CUR_SC])]; exact hX.2.2.cur

/-- A TCB field other than the SC, reply, state and `IN_QUEUES` fields. -/
theorem bx_field {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {y K v : U64}
    (h : SchedQueuesInvX st T Cs Ω X s Q R) (hB : BoundInv st T s) (hX : XInv st T Cs Ω Sg Rp Scs Z s)
    (hsub : ∀ b ∈ Sg, b ∈ Ω) (hy : y ∈ T) (hK : K.val < 4096) (hK8 : K.val % 8 = 0)
    (hKn : K.val ≠ 3464 ∧ K.val ≠ 3360 ∧ K.val ≠ 3328 ∧ K.val ≠ 3592) :
    BoundInv st T (L.wr s (core.num.U64.wrapping_add y K) v) ∧
      XInv st T Cs Ω Sg Rp Scs Z (L.wr s (core.num.U64.wrapping_add y K) v) := by
  have hya := h.tcbs y hy
  have hN' := h.nodes _ h.cur
  refine bx_wr h hB hX (field_aligned hya hK hK8) ?_ (fun y' hy' => ⟨?_, ?_⟩) (fun o ho => ?_)
  · intro hp
    rcases hX.1.prot_cases hsub hp with hm | ⟨t', ht', K', hK', e⟩
    · exact out_ne_field (h.omega _ hm) hy hya hK rfl
    · rcases hp with ⟨r, hr, e'⟩ | ⟨c, hc, e'⟩ | ⟨u, hu, e'⟩
      · have hm : core.num.U64.wrapping_add y K ∈ Ω := by
          rcases e' with e' | e' | e' <;> rw [e']
          · exact hsub _ (hX.1.tcbW hr)
          · exact hsub _ (hX.1.prevW hr)
          · exact hsub _ (hX.1.nextW hr)
        exact out_ne_field (h.omega _ hm) hy hya hK rfl
      · have hm : core.num.U64.wrapping_add y K ∈ Ω := by
          rcases e' with e' | e' <;> rw [e']
          · exact hsub _ (hX.1.fixW c hc).1
          · exact hsub _ (hX.1.fixW c hc).2
        exact out_ne_field (h.omega _ hm) hy hya hK rfl
      · rcases e' with e' | e' | e'
        · rw [scA_eq] at e'
          exact field_ne hya (h.tcbs u hu) hK (by simp) (fun _ => by simp; omega) e'
        · exact field_ne hya (h.tcbs u hu) hK (by simp) (fun _ => by simp; omega) e'
        · rw [stA_eq] at e'
          exact field_ne hya (h.tcbs u hu) hK (by simp) (fun _ => by simp; omega) e'
  · rw [scA_eq]
    exact fun e => field_ne hya (h.tcbs y' hy') hK (by simp) (fun _ => by simp; omega) (UScalar.eq_of_val_eq e)
  · rw [inqA_eq]
    exact fun e => field_ne hya (h.tcbs y' hy') hK (by simp) (fun _ => by simp; omega) (UScalar.eq_of_val_eq e)
  · exact fun e => node_ne_field hN' (by omega) hy hya hK (UScalar.eq_of_val_eq e).symm

/-- A queue step on `t` that only clears `t`'s flags. -/
theorem bx_qfoot {X : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {W : List U64}
    {c t : U64} {P : Nat → Prop} (h : SchedQueuesInvX st T Cs Ω X s Q R) (hB : BoundInv st T s)
    (hX : XInv st T Cs Ω Sg Rp Scs Z s) (hSg : SgOK st Ω Sg s) (hW : ∀ w ∈ W, w ∈ T) (hc : c ∈ Cs) (ht : t ∈ T)
    (hP : ∀ o, P o → o ≠ 0 ∧ o ≠ 8 ∧ o ≠ 16 ∧ o ≠ 24) (hw : WritesIn st s s' (L.QFoot s W c P t))
    (hq : (L.mem s' (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64 →
      (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64 ∨ (L.mem s (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64 ∨
        L.mem s (scA t) ≠ 0#u64)
    (hr : (L.mem s' (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64 →
      (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64 ∨ (L.mem s (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64 ∨
        L.mem s (scA t) ≠ 0#u64) :
    BoundInv st T s' ∧ XInv st T Cs Ω Sg Rp Scs Z s' ∧ Fr st T Sg s s' ∧ L.actionW s' = L.actionW s ∧
      L.curW s' = L.curW s ∧ ∀ y ∈ T, y ≠ t → L.mem s' (inqA y) = L.mem s (inqA y) := by
  obtain ⟨f, hi, ea, ec, ei⟩ := qfoot_keep h hSg hW hc ht hP hw
  exact ⟨hB.qstep h f.sc hi ea ec ei hq hr, hX.fr f, f, ea, ec, hi⟩

/-- seL4 `suspend` (MCS) keeps the queue invariant, `BoundInv` and `XInv`,
for a thread that is not the switch-to candidate; the yield-to SC of the
thread, if any, is an SC object. -/
theorem sched.suspend.all {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (t : obj.Tcb)
    (Q : U64 → U64 → List U64) (R : U64 → List U64) (h : SchedQueuesInv st T Cs Ω s Q R) (ht : t ∈ T)
    (hB : BoundInv st T s) (hX : XInv st T Cs Ω Sg Rp Scs Z s) (hSg : SgOK st Ω Sg s)
    (hna : L.actionW s ≠ t)
    (hyield : L.mem s (yieldA t) ≠ 0#u64 → L.mem s (yieldA t) ∈ Scs) :
    sched.suspend st ar s a t ⦃ s' _ => ∃ Q' R', SchedQueuesInv st T Cs Ω s' Q' R' ∧ BoundInv st T s' ∧
      XInv st T Cs Ω Sg Rp Scs Z s' ⦄ := by
  have hT := h.tcbs
  have hta := hT t ht
  have hsub := hSg.sub
  unfold sched.suspend
  refine WP.spec_bind (ipc.cancel_ipc.all s a t Q R h ht hB hX hsub) ?_
  rintro ⟨s1, a1⟩ ⟨h1, hB1, hX1, nb1, hst1, k1⟩
  try simp only [WP.uncurry'_pair]
  have hSg1 : SgOK st Ω Sg s1 := ⟨hSg.sub, fun b hb => by rw [k1.ksb]; exact hSg.ks b hb,
    fun o h1' h2' => by rw [k1.ksb]; exact hSg.ksΩ o h1' h2'⟩
  have na1 : L.actionW s1 ≠ t := by
    rcases hst1 with e | ⟨-, e⟩
    · intro ea
      have := (h1.actOK (ea ▸ ht)).1; rw [ea, e] at this; exact not_runnable_inactive this
    · rw [e]; exact hna
  have y1 : L.mem s1 (yieldA t) = L.mem s (yieldA t) :=
    k1.fld t ht _ (by simp) (by simp) (by simp) (by simp) (fun _ => ⟨by simp, by simp⟩)
  step with obj.Tcb.state.spec as ⟨i, i_post⟩
  -- the fault-IP copy
  refine WP.spec_bind (Pₘ := fun s2 => SchedQueuesInv st T Cs Ω s2 Q R ∧ ¬ Blocked (L.mem s2 (stA t)) ∧
      L.actionW s2 ≠ t ∧ L.mem s2 (yieldA t) = L.mem s (yieldA t) ∧ BoundInv st T s2 ∧
      XInv st T Cs Ω Sg Rp Scs Z s2 ∧ SgOK st Ω Sg s2) ?_ ?_
  · split
    · step with obj.Tcb.reg.spec as ⟨ip⟩
      refine WP.spec_mono (obj.Tcb.set_reg.fault_ip s1 t ip hta) fun s2 e => ?_
      subst e
      obtain ⟨h2, f2, a2⟩ := field_wr_keep (K := 392#u64) (v := ip) h1 ht (by simp) (by simp) (by simp)
      obtain ⟨hB2, hX2⟩ := bx_field (K := 392#u64) (v := ip) h1 hB1 hX1 hsub ht (by simp) (by simp) (by simp)
      refine ⟨h2, ?_, by rw [a2]; exact na1, by rw [← y1]; exact f2 _ (by simp) (by simp) (by simp), hB2, hX2,
        ⟨hSg.sub, fun b hb => by rw [L.ksb_wr]; exact hSg1.ks b hb, fun o h1' h2' => by
          rw [L.ksb_wr]; exact hSg1.ksΩ o h1' h2'⟩⟩
      rw [stA_eq, f2 _ (by simp) (by simp) (by simp), ← stA_eq]; exact nb1
    · exact (WP.spec_ok _).2 ⟨h1, nb1, na1, y1, hB1, hX1, hSg1⟩
  rintro s2 ⟨h2, nb2, na2, y2, hB2, hX2, hSg2⟩
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
  refine WP.spec_bind (Pₘ := fun s5 => SchedQueuesInv st T Cs Ω s5 Q3 R4 ∧ L.mem s5 (stA t) = L.mem s4 (stA t) ∧
      L.actionW s5 = L.actionW s4 ∧ BoundInv st T s5 ∧ XInv st T Cs Ω Sg Rp Scs Z s5 ∧ L.ksb s5 = L.ksb s4) ?_ ?_
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
      obtain ⟨hB5, hX5⟩ := bx_wr (v := 0#u64) h4 hB4 hX4 ho.1 (by
          rintro (⟨r, hr, e'⟩ | ⟨c, hc, e'⟩ | ⟨u, hu, e'⟩)
          · rcases e' with e' | e' | e' <;> have := congrArg UScalar.val e'
            · exact (fr1 r hr).1 this
            · exact (fr1 r hr).2.1 this
            · exact (fr1 r hr).2.2 this
          · rcases e' with e' | e' <;> have := congrArg UScalar.val e'
            · exact (fr2 c hc).1 this
            · exact (fr2 c hc).2.1 this
          · rcases e' with e' | e' | e'
            · rw [scA_eq] at e'; exact out_ne_field ho hu (hT u hu) (by simp) (congrArg UScalar.val e').symm
            · exact out_ne_field ho hu (hT u hu) (by simp) (congrArg UScalar.val e').symm
            · rw [stA_eq] at e'; exact out_ne_field ho hu (hT u hu) (by simp) (congrArg UScalar.val e').symm)
        (fun y hy => ⟨by rw [scA_eq]; exact (out_ne_field ho hy (hT y hy) (by simp)).symm,
          by rw [inqA_eq]; exact (out_ne_field ho hy (hT y hy) (by simp)).symm⟩)
        (fun o ho' => (out_ne_node ho h4.cur (h4.nodes _ h4.cur) (by omega)).symm)
      have a5 : L.actionW (L.wr s4 (scYieldFromA yt) 0#u64) = L.actionW s4 := by
        unfold LawfulStore.actionW
        simp only [LawfulStore.cpu_wr, nodeAt_wr]
        exact L.mem_wr_ne (h4.omega _ hyΩ).1 (nodeAt_aligned (h4.nodes _ h4.cur) (by rw [act_val]; omega)
          (by rw [act_val])) (fun e => out_ne_node (h4.omega _ hyΩ) h4.cur (h4.nodes _ h4.cur)
            (by rw [act_val]; omega) e.symm)
      refine WP.spec_mono (obj.Tcb.set_yield_to.spec _ t 0#u64) fun s6 e => ?_
      subst e
      obtain ⟨h6, f6, a6⟩ := field_wr_keep (K := 3472#u64) (v := 0#u64) h5 ht (by simp) (by simp) (by simp)
      obtain ⟨hB6, hX6⟩ := bx_field (K := 3472#u64) (v := 0#u64) h5 hB5 hX5 hsub ht (by simp) (by simp)
        (by simp)
      refine ⟨h6, ?_, a6.trans a5, hB6, hX6, by simp only [L.ksb_wr]⟩
      rw [stA_eq, show yieldA t = core.num.U64.wrapping_add t 3472#u64 from rfl,
        f6 _ (by simp) (by simp) (by simp), ← stA_eq, e5 t ht]
    · exact (WP.spec_ok _).2 ⟨h4, rfl, rfl, hB4, hX4, rfl⟩
  rintro s5 ⟨h5, st5, a5, hB5, hX5, k5⟩
  have hnr5 : ¬ Blocked (L.mem s5 (stA t)) := by rw [st5, st4]; exact nb2
  refine WP.spec_bind (WP.spec_and (sched.set_thread_state.inv s5 t _ Q3 R4 h5 ht not_blocked_inactive (Or.inr hnr5)
    ⟨fun c hc p hp hm => absurd hm (nQ3 c hc p hp), fun c hc hm => absurd hm (nR4 c hc),
     fun e => absurd e (by rw [a5]; exact na4)⟩) (sched.set_thread_state.state s5 t _ Q3 R4 h5 ht hX5.1 hsub)) ?_
  rintro s6 ⟨h6, e6, k6⟩
  simp only [WP.spec_ok, WP.uncurry'_pair]
  have nrr : sched.TS_INACTIVE ≠ sched.TS_BLOCKED_ON_REPLY ∧ sched.TS_INACTIVE ≠ sched.TS_BLOCKED_ON_RECV := by
    obtain ⟨-, -, h3', -⟩ := ts_vals
    rw [ts_inactive, ts_reply, h3']; decide
  exact ⟨Q3, R4, h6.congrX empty_congr, hB5.keepT h5 k6, hX5.keepT k6 (by rw [e6]; exact nrr)⟩

end

end Fl4Proofs.P1
