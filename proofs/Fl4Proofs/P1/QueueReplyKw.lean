/-
P1: **`reply_remove`'s writes inside `KW`** (no debug-list word written)
when the caller sits on the core of the SC it may get back
(`ipc.reply_remove.kwA`). `ipc.reply_remove.blk` gives only `FootD`: the
donation back (`schedcontext.donate`) ends with `migrate_tcb`, which moves
the caller between the cores' debug lists when its affinity differs from
the SC's core. When they agree it writes no debug-list word
(`donate_tail.frame`); the donation's first half (the old holder's stall,
dequeue, release-queue removal, `SC` clear and `reschedule_required`) keeps
the caller's affinity (`sched.reschedule_required.aff`, `aff_qfoot`), so the
condition at the start carries to the tail (`schedcontext.donate.kwA`).
-/
import Fl4Proofs.P1.QueueReplyPop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Es : Set U64}

/-- `reschedule_required` keeps the TCBs' affinity fields. -/
theorem sched.reschedule_required.aff {X : Set U64} (s : S) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) {y : U64} (hy : y ∈ T) :
    sched.reschedule_required st s ⦃ s' => L.mem s' (affA y) = L.mem s (affA y) ⦄ := by
  unfold sched.reschedule_required
  step with sched.action.spec as ⟨act, act_post⟩
  refine WP.spec_bind (Pₘ := fun s1 => (∃ Q1 R1, SchedQueuesInvX st T Cs Ω H X s1 Q1 R1) ∧
    L.mem s1 (affA y) = L.mem s (affA y)) ?_ ?_
  · split
    · split
      · rename_i h1 h2
        have hT : act ∈ T := by
          rcases h.action with e | e | e
          · rw [← act_post] at e; exfalso; rw [e, resume_val] at h1; simp at h1
          · rw [← act_post] at e; exfalso; rw [e, choose_val] at h2; simp at h2
          · rw [← act_post] at e; exact e
        have hrun : Runnable (L.mem s (stA act)) := by
          have := (h.actOK (act_post ▸ hT)).1; rw [← act_post] at this; exact this
        step with sched.is_schedulable.spec as ⟨b, hb⟩
        split
        · have hc := h.aff act hT
          have hp := h.prio act hT
          refine WP.spec_mono (WP.spec_and (sched.enqueue.inv s act Q R h hT (fun _ => hb ‹_›) (fun _ => hrun))
            (sched.enqueue.foot s act _ h.tcbs hT hp (h.nodes _ hc) (h.nodes _ h.cur) ((h.ready _ hc).1.rel _ hp)
              (fun h0 => h.notQ hT h0 hc hp))) fun s1 hh => ?_
          obtain ⟨h1', hw, -⟩ := hh
          have hW : ∀ w ∈ act :: Q (L.mem s (affA act)) (L.mem s (prioA act)), w ∈ T := by
            intro w hw; rcases List.mem_cons.1 hw with rfl | hw
            · exact hT
            · exact h.memT hc hp hw
          exact ⟨⟨_, _, h1'⟩, aff_qfoot h.tcbs hW (h.nodes _ hc) (h.nodes _ h.cur) hT hw hy⟩
        · exact (WP.spec_ok _).2 ⟨⟨Q, R, h⟩, rfl⟩
      · exact (WP.spec_ok _).2 ⟨⟨Q, R, h⟩, rfl⟩
    · exact (WP.spec_ok _).2 ⟨⟨Q, R, h⟩, rfl⟩
  · rintro s1 ⟨⟨Q1, R1, h1⟩, i1⟩
    refine WP.spec_mono (sched.set_action.spec s1 _) fun s2 e => ?_
    subst e
    rw [← i1]
    exact L.mem_wr_ne (nodeAt_aligned (h1.nodes _ h1.cur) (by rw [act_val]; omega) (by rw [act_val]))
      (by rw [affA_eq]; exact field_aligned (h1.tcbs y hy) (by simp) (by simp))
      (fun e => node_ne_field (h1.nodes _ h1.cur) (by rw [act_val]; omega) hy (h1.tcbs y hy) (K := 3520#u64)
        (by simp) (UScalar.eq_of_val_eq e))

/-- **`donate`'s writes inside `KW`** when the receiver sits on the SC's core
(module docstring; `schedcontext.donate.kwC` for any SC holder). -/
theorem schedcontext.donate.kwA {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (sc dst : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hsc : sc ∈ Scs) (hdst : dst ∈ T) :
    schedcontext.donate st ar s a sc dst ⦃ s' _ =>
      L.mem s (affA dst) = L.mem s (scCoreA sc) → Foot st T Cs Sg Scs Z Es s s' ⦄ := by
  have h0 := h.1.choose_spec.choose_spec
  have hT := h0.tcbs
  have hX := h.2.2.1
  have hO := hX.1
  have hsub := h.2.2.2.2.sub
  have hcO : scCoreA sc ∈ Ω := ((objs_omega hO hsub).2 sc hsc).2.1
  have hdA : Aligned (affA dst) := by rw [affA_eq]; exact field_aligned (hT dst hdst) (by simp) (by simp)
  unfold schedcontext.donate
  step with obj.Sc.tcb.spec as ⟨i, ei⟩
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => Foot st T Cs ∅ ∅ Z ∅ s r.1 ∧
      L.mem r.1 (affA dst) = L.mem s (affA dst) ∧ ∃ Q1 R1, SchedQueuesInv st T Cs Ω H r.1 Q1 R1) ?_ ?_
  · split
    · exact (WP.spec_ok _).2 ⟨Foot.refl _, rfl, h.1⟩
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
    have g2 : L.mem s2 (affA dst) = L.mem s (affA dst) := by
      rcases hs2 with rfl | ⟨v, rfl⟩
      · rfl
      · exact L.mem_wr_ne (nodeAt_aligned (h0.nodes _ h0.cur) (by rw [ipi_val]; omega) (by rw [ipi_val])) hdA
          (fun e => node_ne_field (h0.nodes _ h0.cur) (by rw [ipi_val]; omega) hdst (hT dst hdst) (K := 3520#u64)
            (by simp) (UScalar.eq_of_val_eq e))
    obtain ⟨⟨Q2, R2, q2⟩, hB2, -, -, hSg2⟩ := h2
    have hc2 := q2.aff i hiT
    have hp2 := q2.prio i hiT
    refine WP.spec_bind (WP.spec_and (WP.spec_and (sched.dequeue.sch (Sg := Sg) s2 i Q2 R2 q2 hB2 hSg2 hiT)
      (sched.dequeue.kw (Sg := ∅) (Scs := ∅) (Z := Z) (Es := ∅) s2 i q2 hiT))
      (sched.dequeue.foot s2 i _ hT hiT hp2 (q2.nodes _ hc2) (q2.nodes _ q2.cur) ((q2.ready _ hc2).1.rel _ hp2)
        (q2.queued i hiT).1)) fun s3 hh3 => ?_
    obtain ⟨⟨⟨⟨⟨Q3, R3, q3⟩, hB3, fr3⟩, -, -⟩, f3⟩, hw3, -⟩ := hh3
    have g3 : L.mem s3 (affA dst) = L.mem s2 (affA dst) :=
      aff_qfoot hT (fun w hw => q2.memT hc2 hp2 hw) (q2.nodes _ hc2) (q2.nodes _ q2.cur) hiT hw3 hdst
    have hc3 := q3.aff i hiT
    refine WP.spec_bind (WP.spec_and (WP.spec_and (sched.release_remove.sch (Sg := Sg) s3 i Q3 R3 q3 hB3
      (hSg2.fr fr3) hiT) (sched.release_remove.kw (Sg := ∅) (Scs := ∅) (Z := Z) (Es := ∅) s3 i q3 hiT))
      (sched.release_remove.foot s3 i _ hT hiT (q3.nodes _ hc3) (q3.nodes _ q3.cur) (q3.release _ hc3)
        (q3.released i hiT).1)) fun s4 hh4 => ?_
    obtain ⟨⟨⟨⟨⟨Q4, R4, q4⟩, -, -⟩, -, -, -⟩, f4⟩, hw4, -⟩ := hh4
    have g4 : L.mem s4 (affA dst) = L.mem s3 (affA dst) :=
      aff_qfoot hT (fun w hw => q3.memTR hc3 hw) (q3.nodes _ hc3) (q3.nodes _ q3.cur) hiT hw4 hdst
    step with obj.Tcb.set_sc.wr as ⟨s5, e5⟩
    subst e5
    have q5 := inv_wr_field (K := 3464#u64) (v := 0#u64) q4 hiT (by simp) (by simp) (by simp)
    have f5 : Foot st T Cs ∅ ∅ Z ∅ s4 (L.wr s4 (scA i) 0#u64) := by
      rw [scA_eq]; exact foot_field hT hiT (by simp) (by simp) (by simp) (by simp)
    have g5 : L.mem (L.wr s4 (scA i) 0#u64) (affA dst) = L.mem s4 (affA dst) := by
      rw [scA_eq]
      exact L.mem_wr_ne (field_aligned (hT i hiT) (by simp) (by simp)) hdA
        (fun e => field_ne (K1 := 3464#u64) (K2 := 3520#u64) (hT i hiT) (hT dst hdst) (by simp) (by simp)
          (fun _ => by simp) (UScalar.eq_of_val_eq e))
    have f05 : Foot st T Cs ∅ ∅ Z ∅ s (L.wr s4 (scA i) 0#u64) := (f2.trans f3).trans (f4.trans f5)
    have g05 : L.mem (L.wr s4 (scA i) 0#u64) (affA dst) = L.mem s (affA dst) := g5.trans (g4.trans (g3.trans g2))
    step with sched.cur_thread.spec as ⟨t1, et1⟩
    step with tcb_eq.blk as ⟨b1, eb1⟩
    refine WP.spec_bind (Pₘ := fun s6 => Foot st T Cs ∅ ∅ Z ∅ (L.wr s4 (scA i) 0#u64) s6 ∧
        L.mem s6 (affA dst) = L.mem (L.wr s4 (scA i) 0#u64) (affA dst) ∧
        ∃ Q1 R1, SchedQueuesInv st T Cs Ω H s6 Q1 R1) ?_
      fun s6 ⟨f6, g6, q6⟩ => (WP.spec_ok _).2 ⟨f05.trans f6, g6.trans g05, q6⟩
    have RR : sched.reschedule_required st (L.wr s4 (scA i) 0#u64) ⦃ s6 =>
        Foot st T Cs ∅ ∅ Z ∅ (L.wr s4 (scA i) 0#u64) s6 ∧
        L.mem s6 (affA dst) = L.mem (L.wr s4 (scA i) 0#u64) (affA dst) ∧
        ∃ Q1 R1, SchedQueuesInv st T Cs Ω H s6 Q1 R1 ⦄ :=
      WP.spec_mono (WP.spec_and (WP.spec_and (sched.reschedule_required.kw (Sg := ∅) (Scs := ∅) (Z := Z) (Es := ∅)
        _ q5) (sched.reschedule_required.inv _ _ _ q5)) (sched.reschedule_required.aff _ _ _ q5 hdst))
        fun s6 ⟨⟨f6, ⟨Q6, h6⟩, _, _⟩, g6⟩ => ⟨f6, g6, _, _, h6⟩
    split
    · exact RR
    · step with sched.action.spec as ⟨i1, ei1⟩
      split
      · exact RR
      · exact (WP.spec_ok _).2 ⟨Foot.refl _, rfl, _, _, q5⟩
  rintro ⟨s1, a1⟩ ⟨f1, g1, Q1, R1, h1⟩
  try simp only [WP.uncurry'_pair]
  have D1 : DbgTz st T Cs s1 := Foot0.dbg hT h0.nodes f1 hX.dbg
  have c1 : L.mem s1 (scCoreA sc) = L.mem s (scCoreA sc) := Foot0.out hT h0.nodes f1 (h0.omega _ hcO)
  refine WP.spec_mono (donate_tail.frame hA s1 a1 sc dst h1 D1 hO.ksb hsub hsc hdst
    (by rw [c1]; exact hX.2.2.core sc hsc)) ?_
  rintro ⟨s', a'⟩ ⟨-, wq⟩
  try simp only [WP.uncurry'_pair] at wq ⊢
  intro he
  refine (Foot.of0 (Sg := Sg) (Scs := Scs) (Es := Es) f1).trans ((wq (by rw [g1, c1]; exact he)).mono fun b hb => ?_)
  rcases hb with rfl | rfl
  · exact kw_sg (hO.fixW sc hsc).1
  · rw [scA_eq]; exact kw_field hdst (by simp) (by simp) (by simp)

/-- `ipc.reply_pop.blk`'s footprint inside `KW` when the caller `t` sits on
the core of the popped head's SC (`hdc`): the donation back moves no thread
across cores (`schedcontext.donate.kwA`).

seL4 `reply_remove` of a stack head (`reply_pop`): the SC `c` that the
head `r` names gets `r`'s `prev` as its new head, which takes over `r`'s
`NEXT` word; `r`'s links are cleared; `c` goes back to `t` if `t` has no
SC; `t` becomes inactive. -/
theorem ipc.reply_pop.kwA {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (r t : U64)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hr : r ∈ Rp) (ht : t ∈ T) (hrt : L.mem s (rTcbA r) = t)
    (hst : L.mem s (stA t) = sched.TS_BLOCKED_ON_REPLY)
    (hb : headBit (L.mem s (rNextA r)) = true) (hn0 : L.mem s (rNextA r) &&& ~~~1#u64 ≠ 0#u64)
    (hdc : L.mem s (affA t) = L.mem s (scCoreA (L.mem s (rNextA r) &&& ~~~1#u64))) :
    ipc.reply_pop st ar s a r t ⦃ res => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac res.1 ∧
      L.mem res.1 (stA t) = sched.TS_INACTIVE ∧ Foot st T Cs Sg Scs Z Es s res.1 ∧
      (L.mem res.1 (scA t) ≠ 0#u64 → L.mem res.1 (scA t) ∈ Ac) ∧ L.idleW res.1 = L.idleW s ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hO := hX.1
  have hsub := hSg.sub
  obtain ⟨hrΩ, hcΩ⟩ := objs_omega hO hsub
  have rr : ∀ r' ∈ Rp, r'.val % 32 = 0 := fun r' hr' => (hO.rp r' hr').1
  obtain ⟨-, -, rp8, rn16⟩ := rp_facts hO hr
  obtain ⟨c, hc⟩ : ∃ c, L.mem s (rNextA r) &&& ~~~1#u64 = c := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p, L.mem s (rPrevA r) &&& ~~~1#u64 = p := ⟨_, rfl⟩
  rw [hc] at hn0
  have hcS : c ∈ Scs := by rw [← hc]; exact (hX.2.1.next r hr (by rw [hc]; exact hn0)).1 hb
  have hcr : L.mem s (scReplyA c) = r := by rw [← hc]; exact hX.2.1.head r hr hb (by rw [hc]; exact hn0)
  have hcA : c ∈ Ac := hS.rep c hcS (by rw [hcr]; exact hO.rp0 r hr)
  have hci : L.mem s (scTcbA c) ≠ L.idleW s := fun e => hO.rp0 r hr (hcr.symm.trans (hX.2.1.idle c hcS e))
  have hpR : p ≠ 0#u64 → p ∈ Rp := fun h0' => by rw [← hp]; exact hX.2.1.prev r hr (by rw [hp]; exact h0')
  have ht0 : t ≠ 0#u64 := fun e0 => (h0.tcbs t ht).ne0 (by rw [e0]; rfl)
  have hrp : L.mem s (replyA t) = r := by
    obtain ⟨-, -, b2, -⟩ := hX.2.1.back r hr (by rw [hrt]; exact ht0)
    rw [hrt] at b2; exact b2
  have hscR : (scReplyA c).val = c.val + 32 := (sc_facts hO hcS).2.2.2.2.2.2.1
  have hscT : (scTcbA c).val = c.val + 24 := (sc_facts hO hcS).2.1
  have hcm : scReplyA c ∈ Ω := hsub _ (hO.repW c hcS)
  have hal : ∀ b ∈ Ω, Aligned b := fun b hb => (h0.omega b hb).1
  unfold ipc.reply_pop
  step with obj.Reply.next.spec as ⟨nx, enx⟩
  step with obj.Reply.prev.spec as ⟨pv, epv⟩
  refine WP.spec_bind (obj.Reply.next_raw.val s r) fun raw eraw => ?_
  rw [hc] at enx; rw [hp] at epv
  subst nx pv raw
  step with obj.Sc.set_reply.spec as ⟨s1, e1⟩
  subst e1
  obtain ⟨h1, hB1, hX1, hS1, hSg1, a1, i1, f1, o1⟩ :=
    screp_wrR (w := p) h0 hB hX.xr hS hSg hcS (fun hp0 => ⟨hpR hp0, hcA, hci⟩)
  have G1 : Foot st T Cs Sg Scs Z Es s (L.wr s (scReplyA c) p) := foot_sgw (hal _ hcm) (hO.repW c hcS)
  -- the new head takes `r`'s `NEXT` word
  refine WP.spec_bind (Pₘ := fun s2 => SchedQueuesInv st T Cs Ω H s2 Q R ∧ BoundInv st T Ac s2 ∧
      XInvR st T Cs Ω Sg Rp Scs Nt Z s2 ∧ SCsOK st T Ω Sg Scs Z Ac s2 ∧ SgOK st Ω Sg s2 ∧
      L.actionW s2 = L.actionW s ∧ L.idleW s2 = L.idleW s ∧
      (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
        L.mem s2 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ b ∈ Ω, (scReplyA c).val ≠ b.val → (p ≠ 0#u64 → (rNextA p).val ≠ b.val) → L.mem s2 b = L.mem s b) ∧
      L.mem s2 (scReplyA c) = p ∧ (p ≠ 0#u64 → L.mem s2 (rNextA p) = L.mem s (rNextA r)) ∧
      Foot st T Cs Sg Scs Z Es s s2) ?_ ?_
  · split
    · rename_i hp0
      have hp0' : p ≠ 0#u64 := by simpa using hp0
      have hpR' := hpR hp0'
      refine WP.spec_mono (obj.Reply.set_next_raw.val _ p _) fun s2 e2 => ?_
      subst e2
      obtain ⟨-, -, pp8, pn16⟩ := rp_facts hO hpR'
      obtain ⟨h2, hB2, hX2, hS2, hSg2, a2, i2, f2, o2⟩ := rword_wrR (w := L.mem s (rNextA r)) h1 hB1 hX1 hS1 hSg1
        hpR' (Or.inr rfl) (fun _ h0' => hX.2.1.next r hr h0')
        (fun e => absurd (congrArg UScalar.val e) (by rw [pp8, pn16]; omega))
      have hpn : (rNextA p).val ≠ (scReplyA c).val := rword_ne_screp hO hpR' (by omega) c hcS
      refine ⟨h2, hB2, hX2, hS2, hSg2, a2.trans a1, i2.trans i1, fun y hy K h1' h2' => (f2 y hy K h1' h2').trans
        (f1 y hy K h1' h2'), fun b hb n1 n2 => (o2 b hb (n2 hp0')).trans (o1 b hb n1), ?_,
        fun _ => L.mem_wr_same (hal _ (hrΩ p hpR').2.2), G1.trans (foot_sgw (hal _ (hrΩ p hpR').2.2) (hO.nextW hpR'))⟩
      rw [o2 _ hcm hpn]; exact L.mem_wr_same (hal _ hcm)
    · rename_i hp0
      have hp0' : p = 0#u64 := UScalar.eq_of_val_eq (by simpa using hp0)
      exact (WP.spec_ok _).2 ⟨h1, hB1, hX1, hS1, hSg1, a1, i1, f1, fun b hb n1 _ => o1 b hb n1,
        L.mem_wr_same (hal _ hcm), fun h' => absurd hp0' h', G1⟩
  intro s2 ⟨h2, hB2, hX2, hS2, hSg2, a2, i2, f2, o2, r2, n2, G2⟩
  -- `r`'s `NEXT` word is cleared: `RHead` again
  refine WP.spec_bind (obj.Reply.set_next.val0 s2 r 0#u64) fun s3 e3 => ?_
  rw [zero_link] at e3
  subst e3
  obtain ⟨h3, hB3, hX3, hS3, hSg3, a3, i3, f3, o3⟩ := rword_wrR (w := 0#u64) h2 hB2 hX2 hS2 hSg2 hr (Or.inr rfl)
    (fun _ h0' => absurd zero_or_masked h0') (fun e => by
      exfalso; have h' := congrArg (fun x : U64 => x.val) e; rw [rp8, rn16] at h'; omega)
  have hd : RHead st Rp (L.wr s2 (rNextA r) 0#u64) := by
    intro r' hr' hb' h0'
    by_cases e : r' = r
    · subst e; rw [L.mem_wr_same (hal _ (hrΩ r' hr').2.2)] at h0'; exact absurd zero_or_masked h0'
    have nrr : (rNextA r).val ≠ (rNextA r').val := by
      rw [rn16, rNextA_val (hO.rp r' hr')]; have := rr r' hr'; have := rr r hr
      have : r.val ≠ r'.val := fun e' => e (UScalar.eq_of_val_eq e').symm
      omega
    rw [o3 _ (hrΩ r' hr').2.2 nrr] at hb' h0' ⊢
    by_cases ep : p ≠ 0#u64 ∧ r' = p
    · obtain ⟨hp0, rfl⟩ := ep
      rw [n2 hp0] at hb' h0' ⊢
      rw [hc, o3 _ hcm (rword_ne_screp hO hr (by omega) c hcS), r2]
    · have e2 : L.mem s2 (rNextA r') = L.mem s (rNextA r') := o2 _ (hrΩ r' hr').2.2
        (fun e' => rword_ne_screp hO hr' (by rw [rNextA_val (hO.rp r' hr')]; omega) c hcS e'.symm)
        (fun hp0 e' => ep ⟨hp0, by
          apply UScalar.eq_of_val_eq
          rw [rNextA_val (hO.rp p (hpR hp0)), rNextA_val (hO.rp r' hr')] at e'
          have := rr r' hr'; have := rr p (hpR hp0); omega⟩)
      rw [e2] at hb' h0' ⊢
      have hc'S := (hX.2.1.next r' hr' h0').1 hb'
      have hhd := hX.2.1.head r' hr' hb' h0'
      have hne : L.mem s (rNextA r') &&& ~~~1#u64 ≠ c := fun e' => by rw [e', hcr] at hhd; exact e hhd.symm
      have hsc' := (sc_facts hO hc'S).2.2.2.2.2.2.1
      have nsc : (scReplyA c).val ≠ (scReplyA (L.mem s (rNextA r') &&& ~~~1#u64)).val := by
        rw [hscR, hsc']
        have := hO.scDisj c hcS _ hc'S (Ne.symm hne); have := (sc_facts hO hc'S).1; have := (sc_facts hO hcS).1
        omega
      have hm' := hsub _ (hO.repW _ hc'S)
      rw [o3 _ hm' (rword_ne_screp hO hr (by omega) _ hc'S), o2 _ hm' nsc
        (fun hp0 => rword_ne_screp hO (hpR hp0) (by rw [rNextA_val (hO.rp p (hpR hp0))]; omega) _ hc'S)]
      exact hhd
  have hX3' := hX3.x hd
  have G3 : Foot st T Cs Sg Scs Z Es s (L.wr s2 (rNextA r) 0#u64) :=
    G2.trans (foot_sgw (hal _ (hrΩ r hr).2.2) (hO.nextW hr))
  -- facts at `s3`
  have F3 : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem (L.wr s2 (rNextA r) 0#u64) (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y hy K h1' h2' => (f3 y hy K h1' h2').trans (f2 y hy K h1' h2')
  have hst3 : L.mem (L.wr s2 (rNextA r) 0#u64) (stA t) = sched.TS_BLOCKED_ON_REPLY := by
    rw [stA_eq, F3 t ht _ (by simp) (by simp), ← stA_eq]; exact hst
  have hrp3 : L.mem (L.wr s2 (rNextA r) 0#u64) (replyA t) = r := by
    exact (F3 t ht 3360#u64 (by simp) (by simp)).trans hrp
  have tc3 : L.mem (L.wr s2 (rNextA r) 0#u64) (scTcbA c) = L.mem s (scTcbA c) := by
    have hm := (hcΩ c hcS).1
    rw [o3 _ hm (rword_ne_sc hO hr (by omega) c hcS).1, o2 _ hm (by rw [hscR, hscT]; omega)
      (fun hp0 => (rword_ne_sc hO (hpR hp0) (by rw [rNextA_val (hO.rp p (hpR hp0))]; omega) c hcS).1)]
  have hdc3 : L.mem (L.wr s2 (rNextA r) 0#u64) (affA t) = L.mem (L.wr s2 (rNextA r) 0#u64) (scCoreA c) := by
    have hm := (hcΩ c hcS).2.1
    have hscC : (scCoreA c).val = c.val + 16 := (sc_facts hO hcS).2.2.1
    rw [show L.mem (L.wr s2 (rNextA r) 0#u64) (affA t) = L.mem s (affA t) from F3 t ht 3520#u64 (by simp) (by simp),
      hdc, hc, o3 _ hm (rword_ne_sc hO hr (by omega) c hcS).2.1, o2 _ hm (by rw [hscR, hscC]; omega)
      (fun hp0 => (rword_ne_sc hO (hpR hp0) (by rw [rNextA_val (hO.rp p (hpR hp0))]; omega) c hcS).2.1)]
  -- the donation back to `t`
  step with obj.Tcb.sc.spec as ⟨i, ei⟩
  have hk3 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s2 (rNextA r) 0#u64) := ⟨⟨Q, R, h3⟩, hB3, hX3', hS3, hSg3⟩
  have scs : L.mem s (scA t) ≠ 0#u64 → L.mem s (scA t) ∈ Ac := fun h0' =>
    hB.sact t ht (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hst)))))) h0'
  refine WP.spec_bind (Pₘ := fun res : S × A => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac res.1 ∧
      L.mem res.1 (stA t) = sched.TS_BLOCKED_ON_REPLY ∧ L.mem res.1 (replyA t) = r ∧
      Foot st T Cs Sg Scs Z Es (L.wr s2 (rNextA r) 0#u64) res.1 ∧
      (L.mem res.1 (scA t) ≠ 0#u64 → L.mem res.1 (scA t) ∈ Ac) ∧
      L.idleW res.1 = L.idleW (L.wr s2 (rNextA r) 0#u64)) ?_ ?_
  · split
    · rename_i hi0
      have hsc0 : L.mem (L.wr s2 (rNextA r) 0#u64) (scA t) = 0#u64 := by rw [← ei]; exact hi0
      obtain ⟨dq, dr, da⟩ := blocked_out h3 ht (by rw [hst3]; exact not_runnable_reply)
      by_cases hf0 : L.mem (L.wr s2 (rNextA r) 0#u64) (scTcbA c) = 0#u64
      · refine WP.spec_mono (WP.spec_and (WP.spec_and (schedcontext.donate.unbound hA (X := ∅) _ a c t Q R h3 hB3 hX3' hS3 hSg3 ht dq dr
          hcS hn0 hf0 (hX3'.2.2.core c hcS) (fun _ => hcA) hsc0
          (fun e => hB3.idleNB (by rw [e, hst3]; exact Or.inr rfl)))
          (schedcontext.donate.kwA (Es := Es) hA _ a c t hk3 hcS ht)) (schedcontext.donate.idle hA _ a c t hk3 hcS ht)) ?_
        rintro ⟨s4, a4⟩ ⟨⟨⟨hk, st4, rp4, -, sc4, -, -⟩, fk⟩, id4⟩
        exact ⟨hk, by rw [st4 t ht]; exact hst3, by rw [rp4 t ht]; exact hrp3, fk hdc3, fun _ => by rw [sc4]; exact hcA, id4⟩
      · have hfT := hX3'.2.2.yt.1 c hcS hf0
        have hscf := hX3'.2.2.tsc c hcS hn0 hf0
        refine WP.spec_mono (WP.spec_and (WP.spec_and (schedcontext.donate.gen hA _ a c t _ Q R h3 hB3 hX3' hS3 hSg3 hfT hscf hn0
          ?_ ht hsc0 dq dr da ?_ hcA (fun e => hB3.idleNB (by rw [e, hst3]; exact Or.inr rfl)))
          (schedcontext.donate.kwA (Es := Es) hA _ a c t hk3 hcS ht)) (schedcontext.donate.idle hA _ a c t hk3 hcS ht)) ?_
        · rw [i3, i2, tc3]; exact fun e => hci e.symm
        · intro e; rw [← e, hsc0] at hscf; exact hn0 hscf.symm
        · rintro ⟨s4, a4⟩ ⟨⟨⟨hk, st4, rp4, sc4⟩, fk⟩, id4⟩
          exact ⟨hk, by rw [st4 t ht]; exact hst3, by rw [rp4 t ht]; exact hrp3, fk hdc3, fun _ => by rw [sc4]; exact hcA, id4⟩
    · exact (WP.spec_ok _).2 ⟨hk3, hst3, hrp3, WritesIn.refl _ _, by
        have e3 : L.mem (L.wr s2 (rNextA r) 0#u64) (scA t) = L.mem s (scA t) := by
          rw [scA_eq]; exact F3 t ht _ (by simp) (by simp)
        rw [e3]; exact scs, rfl⟩
  rintro ⟨s4, a4⟩ ⟨hk4, st4, rp4, G4, sc4, id4⟩
  try simp only [WP.uncurry'_pair]
  dsimp only at hk4 st4 rp4 G4 ⊢
  refine WP.spec_bind (obj.Reply.set_prev.val s4 r 0#u64) fun s5 e5 => ?_
  rw [zero_or_masked] at e5
  subst e5
  obtain ⟨hk5, -, id5, f5, -⟩ := rprev_wr_all hk4 hr (fun h0' => absurd zero_or_masked h0')
  have hst5 : L.mem (L.wr s4 (rPrevA r) 0#u64) (stA t) = sched.TS_BLOCKED_ON_REPLY := by
    rw [stA_eq, f5 t ht _ (by simp) (by simp), ← stA_eq]; exact st4
  have hrp5 : L.mem (L.wr s4 (rPrevA r) 0#u64) (replyA t) = r := by
    exact (f5 t ht 3360#u64 (by simp) (by simp)).trans rp4
  have hrt5 := (hk5.2.2.1.2.1.reply t ht hst5).2
  rw [hrp5] at hrt5
  have G5 : Foot st T Cs Sg Scs Z Es s4 (L.wr s4 (rPrevA r) 0#u64) :=
    foot_sgw (hal _ (hrΩ r hr).2.1) (hO.prevW hr)
  have sc5 : L.mem (L.wr s4 (rPrevA r) 0#u64) (scA t) = L.mem s4 (scA t) := by
    rw [scA_eq]; exact f5 t ht _ (by simp) (by simp)
  refine WP.spec_bind (ipc.reply_unlink.blk (Es := Es) _ r t hk5 hr ht hrt5 hst5) ?_
  rintro s6 ⟨h6, e6, k6, -, G6⟩
  exact (WP.spec_ok _).2 ⟨h6, e6, G3.trans (G4.trans (G5.trans G6)), by
    rw [k6.scf ht, sc5]; exact sc4, by rw [k6.idleW, id5, id4, i3, i2]⟩



/-- `ipc.reply_remove.blk`'s footprint inside `KW` (no debug-list word
written) when the caller sits on the core of the reply's SC, if the reply
heads a stack (`hdc`).

seL4 `reply_remove`: a stack head is popped (`reply_pop`); otherwise the
reply leaves the middle of its stack (its neighbours' links to it are
cleared) or is on no stack.  Then `t` (blocked on the reply) becomes
inactive. -/
theorem ipc.reply_remove.kwA {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (r t : U64)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hr : r ∈ Rp) (ht : t ∈ T) (hrt : L.mem s (rTcbA r) = t)
    (hst : L.mem s (stA t) = sched.TS_BLOCKED_ON_REPLY)
    (hdc : headBit (L.mem s (rNextA r)) = true →
      L.mem s (affA t) = L.mem s (scCoreA (L.mem s (rNextA r) &&& ~~~1#u64))) :
    ipc.reply_remove st ar s a r t ⦃ res => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac res.1 ∧
      L.mem res.1 (stA t) = sched.TS_INACTIVE ∧ Foot st T Cs Sg Scs Z Es s res.1 ∧
      (L.mem res.1 (scA t) ≠ 0#u64 → L.mem res.1 (scA t) ∈ Ac) ∧ L.idleW res.1 = L.idleW s ⦄ := by
  have scs : L.mem s (scA t) ≠ 0#u64 → L.mem s (scA t) ∈ Ac := fun h0' =>
    h.2.1.sact t ht (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hst)))))) h0'
  have hX := h.2.2.1
  have hO := hX.1
  have ht0 : t ≠ 0#u64 := fun e0 => (h.1.choose_spec.choose_spec.tcbs t ht).ne0 (by rw [e0]; rfl)
  have hrp : L.mem s (replyA t) = r := by
    obtain ⟨-, -, b2, -⟩ := hX.2.1.back r hr (by rw [hrt]; exact ht0)
    rw [hrt] at b2; exact b2
  -- the unlinking writes keep `BlkOK` and `t`'s fields
  have W : ∀ {s₁ : S} {r' a' : U64}, BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s₁ →
      L.mem s₁ (stA t) = sched.TS_BLOCKED_ON_REPLY → L.mem s₁ (replyA t) = r → r' ∈ Rp →
      (a' = rPrevA r' ∨ a' = rNextA r') →
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s₁ a' 0#u64) ∧
        L.mem (L.wr s₁ a' 0#u64) (stA t) = sched.TS_BLOCKED_ON_REPLY ∧ L.mem (L.wr s₁ a' 0#u64) (replyA t) = r ∧
        Foot st T Cs Sg Scs Z Es s₁ (L.wr s₁ a' 0#u64) ∧ L.mem (L.wr s₁ a' 0#u64) (scA t) = L.mem s₁ (scA t) ∧
        L.idleW (L.wr s₁ a' 0#u64) = L.idleW s₁ :=
    fun h₁ e₁ e₂ hr' ha' => by
      obtain ⟨k, f⟩ := rword_wr0_all h₁ hr' ha'
      have hO₁ := h₁.2.2.1.1
      refine ⟨k, by rw [stA_eq, f t ht _ (by simp) (by simp), ← stA_eq]; exact e₁,
        (f t ht 3360#u64 (by simp) (by simp)).trans e₂, ?_, by rw [scA_eq]; exact f t ht _ (by simp) (by simp),
        idleW_wr_out h₁.1.choose_spec.choose_spec (by
          rcases ha' with rfl | rfl
          · exact h₁.2.2.2.2.sub _ (hO₁.prevW hr')
          · exact h₁.2.2.2.2.sub _ (hO₁.nextW hr'))⟩
      rcases ha' with rfl | rfl
      · exact foot_sgw (rp_aligned hO hr').2.1 (hO.prevW hr')
      · exact foot_sgw (rp_aligned hO hr').2.2 (hO.nextW hr')
  have tail : ∀ s₂ : S, BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s₂ →
      L.mem s₂ (stA t) = sched.TS_BLOCKED_ON_REPLY → L.mem s₂ (replyA t) = r →
      L.mem s₂ (scA t) = L.mem s (scA t) →
      (do
        let s3 ← obj.Reply.set_prev st r s₂ 0#u64
        let s4 ← obj.Reply.set_next st r s3 0#u64 false
        let s5 ← ipc.reply_unlink st s4 r t
        ok (s5, a)) ⦃ res => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac res.1 ∧
          L.mem res.1 (stA t) = sched.TS_INACTIVE ∧ Foot st T Cs Sg Scs Z Es s₂ res.1 ∧
          (L.mem res.1 (scA t) ≠ 0#u64 → L.mem res.1 (scA t) ∈ Ac) ∧ L.idleW res.1 = L.idleW s₂ ⦄ := by
    intro s₂ h₂ e₂ r₂ c₂
    refine WP.spec_bind (obj.Reply.set_prev.val s₂ r 0#u64) fun s3 e3 => ?_
    rw [zero_or_masked] at e3; subst e3
    obtain ⟨h3, e3, r3, g3, c3, i3⟩ := W h₂ e₂ r₂ hr (Or.inl rfl)
    refine WP.spec_bind (obj.Reply.set_next.val0 _ r 0#u64) fun s4 e4 => ?_
    rw [zero_link] at e4; subst e4
    obtain ⟨h4, e4, r4, g4, c4, i4⟩ := W h3 e3 r3 hr (Or.inr rfl)
    have hrt4 := (h4.2.2.1.2.1.reply t ht e4).2
    rw [r4] at hrt4
    refine WP.spec_bind (ipc.reply_unlink.blk (Es := Es) _ r t h4 hr ht hrt4 e4) ?_
    rintro s5 ⟨h5, e5, k5, -, g5⟩
    exact (WP.spec_ok _).2 ⟨h5, e5, g3.trans (g4.trans g5), by rw [k5.scf ht, c4, c3, c₂]; exact scs,
      by rw [k5.idleW, i4, i3]⟩
  unfold ipc.reply_remove
  step with obj.Reply.next.spec as ⟨nx, enx⟩
  step with obj.Reply.prev.spec as ⟨pv, epv⟩
  subst nx pv
  have hpR : L.mem s (rPrevA r) &&& ~~~1#u64 ≠ 0#u64 → L.mem s (rPrevA r) &&& ~~~1#u64 ∈ Rp := hX.2.1.prev r hr
  -- the prev neighbour's `NEXT` word, then the tail
  have P : ∀ s₁ : S, BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s₁ →
      L.mem s₁ (stA t) = sched.TS_BLOCKED_ON_REPLY → L.mem s₁ (replyA t) = r →
      L.mem s₁ (scA t) = L.mem s (scA t) →
      (do
        let s2 ← if (L.mem s (rPrevA r) &&& ~~~1#u64) != 0#u64
          then obj.Reply.set_next st (L.mem s (rPrevA r) &&& ~~~1#u64) s₁ 0#u64 false else ok s₁
        let s3 ← obj.Reply.set_prev st r s2 0#u64
        let s4 ← obj.Reply.set_next st r s3 0#u64 false
        let s5 ← ipc.reply_unlink st s4 r t
        ok (s5, a)) ⦃ res => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac res.1 ∧
          L.mem res.1 (stA t) = sched.TS_INACTIVE ∧ Foot st T Cs Sg Scs Z Es s₁ res.1 ∧
          (L.mem res.1 (scA t) ≠ 0#u64 → L.mem res.1 (scA t) ∈ Ac) ∧ L.idleW res.1 = L.idleW s₁ ⦄ := by
    intro s₁ h₁ e₁ r₁ c₁
    split
    · rename_i hp0
      refine WP.spec_bind (obj.Reply.set_next.val0 s₁ _ 0#u64) fun s2 e2 => ?_
      rw [zero_link] at e2; subst e2
      obtain ⟨h2, e2, r2, g2, c2, i2⟩ := W h₁ e₁ r₁ (hpR (by simpa using hp0)) (Or.inr rfl)
      exact WP.spec_mono (tail _ h2 e2 r2 (c2.trans c₁)) fun r hr =>
        ⟨hr.1, hr.2.1, g2.trans hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.trans i2⟩
    · simp only [Aeneas.Std.bind_ok]; exact tail s₁ h₁ e₁ r₁ c₁
  split
  · rename_i hn0
    have hn0' : L.mem s (rNextA r) &&& ~~~1#u64 ≠ 0#u64 := by simpa using hn0
    step with obj.Reply.next_is_head.spec as ⟨b, eb⟩
    split
    · rename_i hb
      have hb' : headBit (L.mem s (rNextA r)) = true := by rw [← eb]; exact hb
      exact ipc.reply_pop.kwA hA s a r t h hr ht hrt hst hb' hn0' (hdc hb')
    · rename_i hb
      have hb' : headBit (L.mem s (rNextA r)) = false := by rw [← eb]; simpa using hb
      have hnR := (hX.2.1.next r hr hn0').2 hb'
      refine WP.spec_bind (obj.Reply.set_prev.val s _ 0#u64) fun s1 e1 => ?_
      rw [zero_or_masked] at e1; subst e1
      obtain ⟨h1, e1, r1, g1, c1, i1⟩ := W h hst hrp hnR (Or.inl rfl)
      exact WP.spec_mono (P _ h1 e1 r1 c1) fun r hr =>
        ⟨hr.1, hr.2.1, (g1.trans hr.2.2.1), hr.2.2.2.1, hr.2.2.2.2.trans i1⟩
  · rename_i hn0
    simp only [Aeneas.Std.bind_ok]
    exact WP.spec_mono (P s h hst hrp rfl) fun r hr => ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2⟩

end

end Fl4Proofs.P1
