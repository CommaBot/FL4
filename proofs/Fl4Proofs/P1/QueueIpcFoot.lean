/-
P1: the footprints of `send_ipc` and `do_reply_transfer` (`IpcFoot`): the
words of `KW`, the receiver's user context and IPC buffer (`XferFoot`), and
cap-slot words apart from the first 256 bytes of the kernel-global block
(`KG`, a granted cap's receive slot and CDT neighbours).
-/
import Fl4Proofs.P1.QueueXferFoot
import Fl4Proofs.P1.QueueFootD
import Fl4Proofs.P1.QueueReplyX
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

/-- The words `send_ipc` and `do_reply_transfer` may write, from `s0`. -/
def IpcW {S : Type _} (st : machine.Store S) [L : LawfulStore st] (T Cs Ω Sg Scs : Set U64) (Z : U64 → Nat)
    (Es U : Set U64) (s0 : S) (b : U64) : Prop :=
  KW st T Cs Sg Scs Z Es s0 b ∨ XferFoot T U b ∨ (CapW T Ω Sg b ∧ KG (L.ksb s0) b)

/-- A footprint inside `IpcW`. -/
abbrev IpcFoot {S : Type _} (st : machine.Store S) [L : LawfulStore st] (T Cs Ω Sg Scs : Set U64) (Z : U64 → Nat)
    (Es U : Set U64) (s s' : S) : Prop :=
  WritesIn st s s' (IpcW st T Cs Ω Sg Scs Z Es U s)

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {Es U : Set U64}

theorem IpcFoot.refl (s : S) : IpcFoot st T Cs Ω Sg Scs Z Es U s s := WritesIn.refl _ _

theorem IpcW.ksb {s0 s1 : S} {b : U64} (hk : L.ksb s1 = L.ksb s0) (h : IpcW st T Cs Ω Sg Scs Z Es U s1 b) :
    IpcW st T Cs Ω Sg Scs Z Es U s0 b := by
  rcases h with h | h | ⟨h1, h2⟩
  · exact Or.inl (KW.ksb hk h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨h1, by rw [← hk]; exact h2⟩)

theorem IpcFoot.trans {s₁ s₂ s₃ : S} (h₁ : IpcFoot st T Cs Ω Sg Scs Z Es U s₁ s₂)
    (h₂ : IpcFoot st T Cs Ω Sg Scs Z Es U s₂ s₃) : IpcFoot st T Cs Ω Sg Scs Z Es U s₁ s₃ :=
  WritesIn.mono (WritesIn.trans h₁ h₂) fun b hb => Or.elim hb id fun hb => IpcW.ksb h₁.1 hb

theorem Foot.ipc {s s' : S} (h : Foot st T Cs Sg Scs Z Es s s') : IpcFoot st T Cs Ω Sg Scs Z Es U s s' :=
  ⟨h.1, h.2.1, fun b hb hn => h.2.2 b hb fun hk => hn (Or.inl hk)⟩

theorem XferW.ipc {s s' : S} (h : WritesIn st s s' (XferW T U Ω Sg Scs Z (L.ksb s))) :
    IpcFoot st T Cs Ω Sg Scs Z Es U s s' :=
  h.mono fun b hb => by
    rcases hb with hb | hb | ⟨c, hc, hin⟩
    · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr hb)
    · exact Or.inl (kw_sc hc hin)

/-! ## `set_blocked_on_reply` and `donate` -/

section kw
variable {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}

theorem sched.set_blocked_on_reply.kw (s : S) (t r : U64) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) :
    sched.set_blocked_on_reply st s t r ⦃ s' => Foot st T Cs Sg Scs Z Es s s' ⦄ := by
  have hT := h.tcbs
  unfold sched.set_blocked_on_reply
  step with obj.Tcb.set_state.spec as ⟨s1, e1⟩
  step with obj.Tcb.set_reply_obj.wr as ⟨s2, e2⟩
  subst e1 e2
  have f1 : Foot st T Cs Sg Scs Z Es s (L.wr s (stA t) sched.TS_BLOCKED_ON_REPLY) := by
    rw [stA_eq]; exact foot_field hT ht (by simp) (by simp) (by simp) (by simp)
  have f2 : Foot st T Cs Sg Scs Z Es (L.wr s (stA t) sched.TS_BLOCKED_ON_REPLY)
      (L.wr (L.wr s (stA t) sched.TS_BLOCKED_ON_REPLY) (replyA t) r) :=
    foot_field (K := 3360#u64) hT ht (by simp) (by simp) (by simp) (by simp)
  have hN : NodePlaced st T (L.wr (L.wr s (stA t) sched.TS_BLOCKED_ON_REPLY) (replyA t) r)
      (L.cpu (L.wr (L.wr s (stA t) sched.TS_BLOCKED_ON_REPLY) (replyA t) r)) := by
    simp only [LawfulStore.cpu_wr]; exact ((h.nodes _ h.cur).ksb (L.ksb_wr _ _ _)).ksb (L.ksb_wr _ _ _)
  exact WP.spec_mono (sched.schedule_tcb.kw _ t hN (by simp only [LawfulStore.cpu_wr]; exact h.cur))
    fun s3 f3 => f1.trans (f2.trans f3)

set_option maxHeartbeats 1000000 in
/-- **`donate`'s footprint** from the queue invariant alone, when the SC's
thread (if any) is in no ready or release queue. -/
theorem schedcontext.donate.kwI {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (sc dst : U64) (h : SchedQueuesInvX st T Cs Ω H X s Q R) {s0 : S} (hO : ObjsOK st Ω Sg Rp Scs Nt Z s0)
    (hsc : sc ∈ Scs) (hdst : dst ∈ T)
    (hi : L.mem s (scTcbA sc) ≠ 0#u64 → L.mem s (scTcbA sc) ∈ T ∧
      (L.mem s (inqA (L.mem s (scTcbA sc))) &&& sched.Q_QUEUED) = 0#u64 ∧
      (L.mem s (inqA (L.mem s (scTcbA sc))) &&& sched.Q_RELEASE) = 0#u64) :
    schedcontext.donate st ar s a sc dst ⦃ s' _ => Foot st T Cs Sg Scs Z Es s s' ⦄ := by
  have hT := h.tcbs
  have hN' := h.nodes _ h.cur
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
    obtain ⟨hiT, hiq, hir⟩ := hi (by rw [← ei]; exact hi0)
    rw [← ei] at hiT hiq hir
    refine WP.spec_bind (smp.remote_tcb_stall.spec hA s a i) ?_
    rintro ⟨s2, a2⟩ hs2
    try simp only [WP.uncurry'_pair] at hs2 ⊢
    -- the stall writes at most `IPI_PENDING`
    have hst : SchedQueuesInvX st T Cs Ω H X s2 Q R ∧ Foot st T Cs Sg Scs Z Es s s2 ∧
        L.mem s2 (inqA i) = L.mem s (inqA i) := by
      rcases hs2 with rfl | ⟨v, rfl⟩
      · exact ⟨h, Foot.refl _, rfl⟩
      · refine ⟨inv_of_free h (free_node_write rfl h.cur hN' (by rw [ipi_val]; unfold LowFree; omega)),
          foot_node hN' h.cur (by rw [ipi_val]; omega) (by rw [ipi_val]) (by rw [ipi_val]; omega), ?_⟩
        rw [inqA_eq]; exact field_wr_node h h.cur (by rw [ipi_val]; omega) (by rw [ipi_val]) hiT (by simp) (by simp)
    obtain ⟨q2, f2, iq2⟩ := hst
    refine WP.spec_bind (sched.dequeue.noop s2 i (by rw [iq2]; exact hiq)) fun s3 e3 => ?_
    subst s3
    refine WP.spec_bind (sched.release_remove.noop s2 i (by rw [iq2]; exact hir)) fun s4 e4 => ?_
    subst s4
    step with obj.Tcb.set_sc.wr as ⟨s5, e5⟩
    subst e5
    have q5 := inv_wr_field (K := 3464#u64) (v := 0#u64) q2 hiT (by simp) (by simp) (by simp)
    have f5 : Foot st T Cs Sg Scs Z Es s2 (L.wr s2 (scA i) 0#u64) := by
      rw [scA_eq]; exact foot_field hT hiT (by simp) (by simp) (by simp) (by simp)
    have f05 : Foot st T Cs Sg Scs Z Es s (L.wr s2 (scA i) 0#u64) := f2.trans f5
    step with sched.cur_thread.spec as ⟨t1, et1⟩
    step with tcb_eq.blk as ⟨b1, eb1⟩
    refine WP.spec_bind (Pₘ := fun s6 => Foot st T Cs Sg Scs Z Es (L.wr s2 (scA i) 0#u64) s6) ?_
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

set_option maxHeartbeats 4000000 in
/-- **`reply_push`'s footprint**, under `reply_push.ipc`'s hypotheses. -/
theorem ipc.reply_push.kw {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (caller callee r : U64) (can_donate : Bool)
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hXc : ExcT X caller)
    (hx : caller ∈ X ∨ ¬ Blocked (L.mem s (stA caller)))
    (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s)
    (hcl : caller ∈ T) (hcq : (L.mem s (inqA caller) &&& sched.Q_QUEUED) = 0#u64)
    (hcr : (L.mem s (inqA caller) &&& sched.Q_RELEASE) = 0#u64) (hca : L.actionW s ≠ caller)
    (hci : L.idleW s ≠ caller)
    (hcold : L.mem s (stA caller) ≠ sched.TS_BLOCKED_ON_REPLY ∧ L.mem s (stA caller) ≠ sched.TS_BLOCKED_ON_RECV)
    (hr : r ∈ Rp) (hr00 : r ≠ 0#u64) (hr0 : L.mem s (rTcbA r) = 0#u64) (hce : callee ∈ T)
    (hcA : L.mem s (scA caller) ≠ 0#u64 → L.mem s (scA caller) ∈ Ac) :
    ipc.reply_push st ar s a caller callee r can_donate ⦃ s' _ => Foot st T Cs Sg Scs Z Es s s' ⦄ := by
  have hT := h.tcbs
  have hO := hX.1
  have hsub := hSg.sub
  obtain ⟨hrΩ, hcΩ⟩ := objs_omega hO hsub
  obtain ⟨r32, rt0, rp8, rn16⟩ := rp_facts hO hr
  unfold ipc.reply_push
  step with obj.Tcb.sc.spec as ⟨i, ei⟩
  step with obj.Reply.set_tcb.spec as ⟨s1, e1⟩
  subst e1
  have f1 : Foot st T Cs Sg Scs Z Es s (L.wr s (rTcbA r) caller) :=
    foot_wr (h.omega _ (hrΩ r hr).1).1 (kw_sg (hO.tcbW hr))
  have q1 := (omega_wr (v := caller) h (hrΩ r hr).1).1
  refine WP.spec_bind (WP.spec_and (sched.set_blocked_on_reply.ipc s caller r Q R h hXc hx hB hX hS hSg hcl hcq hcr
    hca hci hcold hr hr00 hr0 hcA)
    (sched.set_blocked_on_reply.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) _ caller r q1 hcl)) ?_
  rintro s2 ⟨⟨h2, hB2, hX2, hS2, hSg2, f2', o2, -, -, -, -⟩, f2⟩
  have f02 := f1.trans f2
  step with obj.Sc.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 f02
  rename_i hb
  have hi0 : i ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
  have hci0 : L.mem s (scA caller) ≠ 0#u64 := by rw [← ei]; exact hi0
  obtain ⟨hiS, hitc, -⟩ := hX.2.2.bound caller hcl hci0
  rw [← ei] at hiS hitc
  obtain ⟨h128, tv, -, -, -, -, rv, -⟩ := sc_facts hO hiS
  have hti : (scTcbA i).val ≠ (rTcbA r).val := by
    rw [tv, rt0]; have := hO.rpSc r hr i hiS; omega
  have hal : Aligned (scTcbA i) := (h.omega _ (hcΩ i hiS).1).1
  have tc2 : L.mem s2 (scTcbA i) = caller := by
    rw [o2 _ (hcΩ i hiS).1 (fun e => hti (congrArg UScalar.val e))]
    exact hitc
  -- what the reply and SC writes keep
  let P : S → Prop := fun s' => SchedQueuesInvX st T Cs Ω H ∅ s' Q R ∧ Foot st T Cs Sg Scs Z Es s s' ∧
    (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s2 (core.num.U64.wrapping_add y K)) ∧
    L.mem s' (scTcbA i) = caller
  have W : ∀ (s' : S) (b v : U64), P s' → b ∈ Sg → (scTcbA i).val ≠ b.val → P (L.wr s' b v) := by
    intro s' b v ⟨q, f, k, c⟩ hb hne
    obtain ⟨q', -, k'⟩ := omega_wr (v := v) q (hsub b hb)
    have hba := (q.omega _ (hsub b hb)).1
    exact ⟨q', f.trans (foot_wr hba (kw_sg hb)), fun y hy K h1 h2 => (k' y hy K h1 h2).trans (k y hy K h1 h2),
      by rw [L.mem_wr_ne hba hal (Ne.symm hne)]; exact c⟩
  have P2 : P s2 := ⟨h2, f02, fun _ _ _ _ _ => rfl, tc2⟩
  step with obj.Tcb.sc.spec as ⟨i1, ei1⟩
  split
  · split
    · step with obj.Sc.reply.val as ⟨i2, ei2⟩
      have hi2 : i2 ≠ 0#u64 → i2 ∈ Rp := fun h0 => by rw [ei2] at h0 ⊢; exact hX2.2.1.screp i hiS h0
      refine WP.spec_bind (Pₘ := P) ?_ fun s3 p3 => ?_
      · split
        · rename_i hne
          have h0 : i2 ≠ 0#u64 := by simpa using hne
          have hp := hi2 h0
          refine WP.spec_mono (obj.Reply.set_next.val0 s2 i2 r) fun s3 e3 => ?_
          subst e3
          obtain ⟨-, -, -, n16⟩ := rp_facts hO hp
          exact W _ _ _ P2 (hO.nextW hp) (by rw [tv, n16]; have := hO.rpSc i2 hp i hiS; omega)
        · exact (WP.spec_ok _).2 P2
      refine WP.spec_bind (obj.Reply.set_prev.val s3 r i2) fun s4 e4 => ?_
      subst e4
      have p4 := W _ _ (i2 &&& ~~~1#u64) p3 (hO.prevW hr) (by rw [tv, rp8]; have := hO.rpSc r hr i hiS; omega)
      refine WP.spec_bind (obj.Sc.set_reply.spec _ i r) fun s5 e5 => ?_
      subst e5
      have p5 := W _ _ r p4 (hO.repW i hiS) (by rw [tv, rv]; omega)
      refine WP.spec_bind (obj.Reply.set_next.val1 _ r i) fun s6 e6 => ?_
      subst e6
      have p6 := W _ _ ((i &&& ~~~1#u64) ||| 1#u64) p5 (hO.nextW hr)
        (by rw [tv, rn16]; have := hO.rpSc r hr i hiS; omega)
      obtain ⟨q6, f6, k6, c6⟩ := p6
      have iq : ∀ s', (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
          L.mem s' (core.num.U64.wrapping_add y K) = L.mem s2 (core.num.U64.wrapping_add y K)) →
          L.mem s' (inqA caller) = L.mem s (inqA caller) := fun s' k => by
        rw [inqA_eq, k caller hcl _ (by simp) (by simp)]
        exact f2' caller hcl _ (by simp) (by simp) (fun _ => ⟨by simp, by simp, by simp, by simp, by simp⟩)
      refine WP.spec_mono (schedcontext.donate.kwI (Es := Es) hA _ a i callee q6 hO hiS hce fun _ => ?_)
        fun r' f' => f6.trans f'
      rw [c6]
      exact ⟨hcl, by rw [iq _ k6]; exact hcq, by rw [iq _ k6]; exact hcr⟩
    · exact (WP.spec_ok _).2 f02
  · exact (WP.spec_ok _).2 f02

/-- A `BlkFoot` step from `s` (no reply object) inside `KW`. -/
theorem blkfoot_foot {s s' : S} {t : U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T)
    (w : WritesIn st s s' (BlkFoot st s t 0#u64)) : Foot st T Cs Sg Scs Z Es s s' :=
  Foot.of w fun b hb => by
    rcases hb with ⟨K, hK, rfl⟩ | rfl | ⟨h0, -⟩
    · exact kw_field ht (by omega) (by omega) (by omega)
    · exact kw_node h.cur (by rw [act_val]; omega) (by rw [act_val]; omega)
    · exact absurd rfl h0

set_option maxHeartbeats 4000000 in
/-- **The blocking send's footprint.** -/
theorem send_block.foot {A : Type _} (s : S) (a : A) (t e badge : U64) (can_grant can_grant_reply do_call : Bool)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hc : CanBlock st T Ac s t) (hH : H e = some .ep) :
    (do
      let s1 ← obj.Tcb.set_state st t s sched.TS_BLOCKED_ON_SEND
      let s2 ← obj.Tcb.set_block_obj st t s1 e
      let s3 ← obj.Tcb.set_block_badge st t s2 badge
      let i ← if can_grant then ok endpoint.FLAG_GRANT else ok 0#u64
      let i1 ← if can_grant_reply then ok endpoint.FLAG_GRANT_REPLY else ok 0#u64
      let i2 ← lift (i ||| i1)
      let i3 ← if do_call then ok endpoint.FLAG_CALL else ok 0#u64
      let f ← lift (i2 ||| i3)
      let s4 ← obj.Tcb.set_block_flags st t s3 f
      let s5 ← sched.schedule_tcb st s4 t
      let s6 ← endpoint.ep_append st s5 e t obj.EP_SEND
      ok (s6, a)) ⦃ s' _ => Foot st T Cs Sg Scs Z (EH H) s s' ⦄ := by
  have ht := hc.mem
  have hta := h.tcbs t ht
  have hN := h.nodes _ h.cur
  step with obj.Tcb.set_state.spec as ⟨s1, e1⟩
  step with obj.Tcb.set_block_obj.wr as ⟨s2, e2⟩
  step with obj.Tcb.set_block_badge.wr as ⟨s3, e3⟩
  have h1 : SchedQueuesInvX st T Cs Ω H {y | y ∈ (∅ : Set U64) ∨ y = t} s1 Q R := by
    rw [e1]; exact blk_set_state h hc
  have h2 : SchedQueuesInvX st T Cs Ω H {y | y ∈ (∅ : Set U64) ∨ y = t} s2 Q R := by
    rw [e2]; exact inv_wr_fieldX (K := 3336#u64) h1 ht (Or.inr rfl) (by simp) (by simp) (by simp)
  have h3 : SchedQueuesInvX st T Cs Ω H {y | y ∈ (∅ : Set U64) ∨ y = t} s3 Q R := by
    rw [e3]; exact inv_wr_fieldX (K := 3344#u64) h2 ht (Or.inr rfl) (by simp) (by simp) (by simp)
  rw [stA_eq] at e1
  have w1 : WritesIn st s s1 (BlkFoot st s t 0#u64) := by
    rw [e1]; exact blk_wr_field (K := 3328#u64) hta (WritesIn.refl _ _) (by simp)
  have w3 : WritesIn st s s3 (BlkFoot st s t 0#u64) := by
    rw [e3, e2]; exact blk_wr_field hta (blk_wr_field hta w1 (by simp)) (by simp)
  have key : ∀ f : U64, (do
      let s4 ← obj.Tcb.set_block_flags st t s3 f
      let s5 ← sched.schedule_tcb st s4 t
      let s6 ← endpoint.ep_append st s5 e t obj.EP_SEND
      ok (s6, a)) ⦃ s' _ => Foot st T Cs Sg Scs Z (EH H) s s' ⦄ := by
    intro f
    step with obj.Tcb.set_block_flags.wr as ⟨s4, e4⟩
    have h4 : SchedQueuesInvX st T Cs Ω H {y | y ∈ (∅ : Set U64) ∨ y = t} s4 Q R := by
      rw [e4]; exact inv_wr_fieldX (K := 3352#u64) h3 ht (Or.inr rfl) (by simp) (by simp) (by simp)
    have w4 : WritesIn st s s4 (BlkFoot st s t 0#u64) := by rw [e4]; exact blk_wr_field hta w3 (by simp)
    have v4 : L.mem s4 (stA t) = sched.TS_BLOCKED_ON_SEND := by
      rw [e4, fld_wr_ne' hta rfl (stA_eq t) (by simp) (by simp) (by simp) (by simp) (by simp),
        e3, fld_wr_ne' hta rfl (stA_eq t) (by simp) (by simp) (by simp) (by simp) (by simp),
        e2, fld_wr_ne' hta (blockA_eq t) (stA_eq t) (by simp) (by simp) (by simp) (by simp) (by simp), e1, stA_eq]
      exact L.mem_wr_same (field_aligned hta (by simp) (by simp))
    have a4 : L.actionW s4 = L.actionW s := by
      rw [e4, act_wr_field (h3.nodes _ h3.cur) ht hta rfl (by simp) (by simp),
        e3, act_wr_field (h2.nodes _ h2.cur) ht hta rfl (by simp) (by simp),
        e2, act_wr_field (h1.nodes _ h1.cur) ht hta (blockA_eq t) (by simp) (by simp),
        e1, act_wr_field hN ht hta rfl (by simp) (by simp)]
    refine WP.spec_bind (sched.schedule_tcb.blk s4 t h4 (by rw [v4]; exact blocked_not_runnable (Or.inl rfl))) ?_
    rintro s5 ⟨h5, e5, -⟩
    obtain ⟨w5, -, -, -, -, -⟩ := blk_sched h4 ht w4 a4 e5
    obtain ⟨E, EQ, hEW⟩ := h.eps
    have heE : e ∈ E := (hEW.2.2.2.2.2.2.2.1 e).2 (Or.inl hH)
    obtain ⟨hE, -, hq⟩ := hEW.1 e heE
    obtain ⟨kf, -, -, ke⟩ := blkfoot_keep h hEW ht (fun h0 => absurd rfl h0) w5
    have hqe : L.epQ s5 e = L.epQ s e := by simp only [LawfulStore.epQ, (ke e heE).1, (ke e heE).2]
    have hq5 : QueueRel (L.mem s5) T .Ep (L.epQ s5 e) (EQ e) :=
      ⟨hq.nodup, hq.mem, by rw [hqe]; exact hq.head, by rw [hqe]; exact hq.last, hq.seg.congr fun y hy =>
        ⟨kf y (hq.mem y hy) (prevOff .Ep) (by simp [prevOff]) (by simp [prevOff]) (fun _ => by simp [prevOff]),
         kf y (hq.mem y hy) (nextOff .Ep) (by simp [nextOff]) (by simp [nextOff]) (fun _ => by simp [nextOff])⟩⟩
    have hn : t ∉ EQ e := fun hm => hc.nb (hEW.2.2.2.1 e heE t hm).2.2
    refine WP.spec_bind (endpoint.ep_append.foot s5 e t obj.EP_SEND (EQ e) h.tcbs hE hq5 ht hn) fun s6 w6 => ?_
    refine (WP.spec_ok _).2 ((blkfoot_foot h ht w5).trans (Foot.of w6 fun b hb => hb.kw ?_ (Or.inl hH)))
    intro w hw
    rcases List.mem_cons.1 hw with rfl | hw
    · exact ht
    · exact hq.mem w hw
  cases can_grant <;> cases can_grant_reply <;> cases do_call <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Aeneas.Std.bind_ok, lift] <;> exact key _

/-- **`send_ipc`'s footprint on an idle or sending endpoint.** -/
theorem endpoint.send_ipc.blockFoot {A : Type _} (ar : machine.Arch A) (s : S) (a : A) (blocking do_call : Bool)
    (badge : U64) (can_grant can_grant_reply can_donate : Bool) (t e : U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hc : blocking = true → CanBlock st T Ac s t)
    (hH : H e = some .ep) (hst0 : L.epState s e = 0#u64 ∨ L.epState s e = 1#u64) :
    endpoint.send_ipc st ar s a blocking do_call badge can_grant can_grant_reply can_donate t e
      ⦃ s' _ => Foot st T Cs Sg Scs Z (EH H) s s' ⦄ := by
  unfold endpoint.send_ipc
  step with obj.Ep.state.spec as ⟨v, hv⟩
  split
  · split
    · exact send_block.foot s a t e badge can_grant can_grant_reply do_call h (hc ‹_›) hH
    · simp only [WP.spec_ok, WP.uncurry'_pair]; exact Foot.refl _
  · split
    · split
      · exact send_block.foot s a t e badge can_grant can_grant_reply do_call h (hc ‹_›) hH
      · simp only [WP.spec_ok, WP.uncurry'_pair]; exact Foot.refl _
    · exfalso
      rename_i h1 h2
      rw [ep_idle_val] at h1; rw [ep_send_val'] at h2
      rcases hst0 with e0 | e0 <;> rw [← hv] at e0 <;> contradiction

end kw

/-- `send_tail`'s footprint. -/
theorem send_tail.foot {X : Set U64} (s4 : S) {A : Type _} (a1 : A) (hd : U64) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (h4 : SchedQueuesInvX st T Cs Ω H X s4 Q R) (hB4 : BoundInv st T Ac s4)
    (hX4 : XInv st T Cs Ω Sg Rp Scs Nt Z s4) (hS4 : SCsOK st T Ω Sg Scs Z Ac s4) (hSg4 : SgOK st Ω Sg s4) (hdT : hd ∈ T)
    (hXc : ExcT X hd) (hx : hd ∈ X ∨ ¬ Blocked (L.mem s4 (stA hd))) (hnr : ∀ r ∈ Rp, L.mem s4 (rTcbA r) ≠ hd)
    (hdA : L.mem s4 (scA hd) ≠ 0#u64 → L.mem s4 (scA hd) ∈ Ac) :
    (do
      let s5 ← sched.set_thread_state st s4 hd sched.TS_RUNNING
      let s6 ← endpoint.unblock_sporadic st s5 hd
      let s7 ← sched.possible_switch_to st s6 hd
      ok (s7, a1)) ⦃ s' _ => Foot st T Cs Sg Scs Z Es s4 s' ⦄ := by
  refine WP.spec_bind (WP.spec_and (sts_all s4 hd _ Q R h4 hB4 hX4 hS4 hSg4 hdT not_blocked_running running_ne hx hnr
    ⟨fun _ _ _ _ _ => runnable_running, fun _ _ _ => runnable_running, fun _ => runnable_running⟩)
    (sched.set_thread_state.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) s4 hd _ h4 hdT)) fun s5 hh' => ?_
  obtain ⟨hh, f5⟩ := hh'
  obtain ⟨h5, hB5, hX5, hS5, hSg5, e5, k5⟩ := hh
  have h5' := h5.congrX (excT_congr hXc)
  refine WP.spec_bind (WP.spec_and (endpoint.unblock_sporadic.all s5 hd h5' hB5 hX5 hS5 hSg5 hdT)
    (endpoint.unblock_sporadic.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) s5 hd h5' hX5 hS5 hdT)) fun s6 hh' => ?_
  obtain ⟨hh, f6⟩ := hh'
  obtain ⟨h6, -⟩ := hh
  refine WP.spec_bind (sched.possible_switch_to.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) s6 hd h6 hdT)
    fun s7 f7 => (WP.spec_ok _).2 (f5.trans (f6.trans f7))

set_option maxHeartbeats 8000000 in
/-- **`send_ipc`'s footprint**: under `send_ipc.ipc`'s hypotheses, with the
transfer's footprint (`XferFootOK`) and `RS` after the receiver's dequeue
(a `KW` step from `s`), `send_ipc` writes only `IpcW` words. -/
theorem endpoint.send_ipc.foot {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {U : Set U64}
    (hxf : XferOK st ar T Cs Ω H Sg Rp Scs Nt Z U) {RS : S → S → Prop} (hxw : XferFootOK st ar T Cs Ω H Sg Rp Scs Nt Z U RS) (s : S) (a : A) (blocking do_call : Bool)
    (badge : U64) (can_grant can_grant_reply can_donate : Bool) (t e : U64)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (hU : UserOK st T Cs Ω H U s)
    (hc : CanBlock st T Ac s t) (hdon : can_donate = true → L.mem s (scA t) ≠ 0#u64)
    (hH : H e = some .ep) (hRSK : ∀ s0 s1 s2 : S, RS s0 s1 → WritesIn st s1 s2 (KW st T Cs Sg Scs Z (EH H) s1) → RS s2 s2)
    (hRS0 : RS s s) :
    endpoint.send_ipc st ar s a blocking do_call badge can_grant can_grant_reply can_donate t e
      ⦃ s' _ => IpcFoot st T Cs Ω Sg Scs Z (EH H) U s s' ⦄ := by
  have hidle := hc.ni
  have hT := h.tcbs
  have ht := hc.mem
  have hta := hT t ht
  rcases ep_state3 h hH with e0 | e0 | e0
  · exact WP.spec_mono (endpoint.send_ipc.blockFoot (Sg := Sg) (Scs := Scs) (Z := Z) ar s a blocking do_call badge
      can_grant can_grant_reply can_donate t e h (fun _ => hc) hH (Or.inl e0)) fun r hh => by
        obtain ⟨s', a'⟩ := r; simp only [WP.uncurry'_pair] at hh ⊢; exact Foot.ipc hh
  · exact WP.spec_mono (endpoint.send_ipc.blockFoot (Sg := Sg) (Scs := Scs) (Z := Z) ar s a blocking do_call badge
      can_grant can_grant_reply can_donate t e h (fun _ => hc) hH (Or.inr e0)) fun r hh => by
        obtain ⟨s', a'⟩ := r; simp only [WP.uncurry'_pair] at hh ⊢; exact Foot.ipc hh
  -- a receiving endpoint
  obtain ⟨hdT, hbe, -, hds⟩ := ep_head h hH (Or.inr rfl) e0
  have hds := hds rfl
  set hd := (L.epQ s e).head with hhd
  have hdt : hd ≠ t := fun e' => hc.nb (by rw [← e', hds]; exact Or.inr (Or.inl rfl))
  have hdi : L.idleW s ≠ hd := fun e' => hB.idleNB (by rw [e', hds]; exact Or.inl (Or.inr (Or.inl rfl)))
  have hdta := hT hd hdT
  unfold endpoint.send_ipc
  step with obj.Ep.state.spec as ⟨v, hv⟩
  have hv2 : v = 2#u64 := hv.trans e0
  rw [hv2]
  simp only [ep_idle_val, ep_send_val', show ¬ ((2#u64) = 0#u64) from by decide,
    show ¬ ((2#u64) = 1#u64) from by decide, ↓reduceIte]
  have hsub := hSg.sub
  step with endpoint.get_queue.spec as ⟨q, eq⟩
  subst eq
  have hdq := endpoint.ep_dequeue.inv s hd Q R h hdT (by simp) (Or.inr (Or.inl hds))
  rw [hbe] at hdq
  obtain ⟨E0, EQ0, hEW0⟩ := h.eps
  have heE0 : e ∈ E0 := (hEW0.2.2.2.2.2.2.2.1 e).2 (Or.inl hH)
  obtain ⟨hE0, -, hq0⟩ := hEW0.1 e heE0
  have hdm : hd ∈ EQ0 e := by
    have := hEW0.2.2.2.2.1 hd hdT (by simp) (Or.inr (Or.inl hds)); rw [hbe] at this; exact this.2
  refine WP.spec_bind (WP.spec_and hdq (endpoint.ep_dequeue.foot s e hd (EQ0 e) hT hE0 hq0 hdm)) ?_
  rintro s1 ⟨⟨h1, f1, o1, n1, k1, c1, nc1⟩, w1⟩
  have F1 : Foot st T Cs Sg Scs Z (EH H) s s1 := Foot.of w1 fun b hb => hb.kw hq0.mem (Or.inl hH)
  obtain ⟨hB1, hX1, hS1, hSg1, ea1, ec1, ei1⟩ := frame_bx h hB hX hS hSg f1 o1 n1 k1
    ⟨k1, fun y hy K a b c => f1 y hy K (by omega) c (by omega) (by omega),
      fun c hc o ho => nc1 c hc o (by omega) (by omega), fun n' hn' => o1 _ (hSg.sub _ (hX.1.ntB n' hn').2)⟩
  refine WP.spec_bind (WP.spec_and (hxf _ _ _ _ s1 a t e badge can_grant hd ht hdT h1 hB1 hX1 hS1 hSg1 (hU.ksb k1))
    (hxw _ _ _ _ s1 a t e badge can_grant hd ht hdT h1 hB1 hX1 hS1 hSg1 (hU.ksb k1) (hRSK s s s1 hRS0 F1))) ?_
  rintro s2 ⟨⟨h2, hB2, hX2, hS2, hSg2, ea2, ec2, ei2, ecs2, f2, o2, -⟩, w2, -⟩
  have F2 : IpcFoot st T Cs Ω Sg Scs Z (EH H) U s s2 := (Foot.ipc F1).trans (XferW.ipc w2)
  have F : ∀ y ∈ T, ∀ K : U64, 3328 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 →
      L.mem s2 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y hy K h0 hK hK8 h1' h2' => (f2 y hy K h0 hK hK8).trans (f1 y hy K hK hK8 h1' h2')
  have Fst : ∀ y ∈ T, L.mem s2 (stA y) = L.mem s (stA y) := fun y hy => by
    rw [stA_eq]; exact F y hy _ (by simp) (by simp) (by simp) (by simp) (by simp)
  have Frp : ∀ y ∈ T, L.mem s2 (replyA y) = L.mem s (replyA y) := fun y hy =>
    F y hy _ (by simp) (by simp) (by simp) (by simp) (by simp)
  have Fiq : ∀ y ∈ T, L.mem s2 (inqA y) = L.mem s (inqA y) := fun y hy => by
    rw [inqA_eq]; exact F y hy _ (by simp) (by simp) (by simp) (by simp) (by simp)
  have Fsc : ∀ y ∈ T, L.mem s2 (scA y) = L.mem s (scA y) := fun y hy => by
    rw [scA_eq]; exact F y hy _ (by simp) (by simp) (by simp) (by simp) (by simp)
  have ea2' : L.actionW s2 = L.actionW s := ea2.trans ea1
  have ei2' : L.idleW s2 = L.idleW s := ei2.trans ei1
  step with obj.Tcb.reply_obj.spec as ⟨i, ei⟩
  have hds2 : L.mem s2 (stA hd) = sched.TS_BLOCKED_ON_RECV := (Fst hd hdT).trans hds
  -- the reply object leaves the receiver
  refine WP.spec_bind (Pₘ := fun s3 => ∃ X3 : Set U64, SchedQueuesInvX st T Cs Ω H X3 s3 Q R ∧ BoundInv st T Ac s3 ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z s3 ∧ SCsOK st T Ω Sg Scs Z Ac s3 ∧ SgOK st Ω Sg s3 ∧ ExcT X3 hd ∧
      (hd ∈ X3 ∨ ¬ Blocked (L.mem s3 (stA hd))) ∧ ¬ Runnable (L.mem s3 (stA hd)) ∧
      (hd ∈ X3 → L.mem s3 (replyA hd) = 0#u64) ∧ (hd ∉ X3 → L.mem s3 (stA hd) = sched.TS_INACTIVE) ∧
      ((i != 0#u64) = true → hd ∉ X3 ∧ i ∈ Rp ∧ L.mem s3 (rTcbA i) = 0#u64) ∧
      L.mem s3 (stA t) = L.mem s (stA t) ∧ L.mem s3 (inqA t) = L.mem s (inqA t) ∧
      L.mem s3 (scA t) = L.mem s (scA t) ∧ L.actionW s3 ≠ t ∧ L.idleW s3 = L.idleW s ∧
      L.mem s3 (scA hd) = L.mem s (scA hd) ∧ IpcFoot st T Cs Ω Sg Scs Z (EH H) U s s3) ?_ ?_
  · split
    · rename_i hi
      have hi0 : i ≠ 0#u64 := by simpa using hi
      obtain ⟨hiR, hit⟩ := hX2.2.1.recv hd hdT hds2 (by rw [← ei]; exact hi0)
      rw [← ei] at hiR hit
      refine WP.spec_mono (WP.spec_and (ipc.reply_unlink.inv s2 i hd Q R h2 hdT hX2.1 hsub hiR hit
        (by rw [hds2]; exact blocked_not_runnable (Or.inr (Or.inl rfl))) (Or.inl (Or.inr rfl)))
        (ipc.reply_unlink.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s2 i hd h2 hX2 hsub hiR hdT)) fun s3 hh' => ?_
      obtain ⟨hh, fu⟩ := hh'
      obtain ⟨h3, e3, k3, z3⟩ := hh
      have hclr : ∀ r ∈ Rp, L.mem s2 (rTcbA r) = hd → L.mem s3 (rTcbA r) = 0#u64 := by
        intro r hr er
        obtain ⟨-, -, b2, -⟩ := hX2.2.1.back r hr (by rw [er]; exact fun e0 => hdta.ne0 (by rw [e0]; rfl))
        rw [er, ← ei] at b2; rw [← b2]; exact z3
      refine ⟨_, h3, hB2.keepT h2 k3 (by rw [e3]; exact not_blocked_inactive) (by rw [e3]; exact inactive_ne.1),
        hX2.keepT k3 (by rw [e3]; exact inactive_ne) hclr, hS2.keepT hX2 k3,
        ⟨hsub, fun b hb => by rw [k3.ksb]; exact hSg2.ks b hb, fun o h1' h2' => by rw [k3.ksb]; exact hSg2.ksΩ o h1' h2'⟩,
        fun y hy => ?_, Or.inr (by rw [e3]; exact not_blocked_inactive), by rw [e3]; exact not_runnable_inactive,
        fun hm => absurd rfl hm.2, fun _ => e3, fun _ => ⟨fun hm => hm.2 rfl, hiR, z3⟩,
        (k3.stf ht (Ne.symm hdt)).trans (Fst t ht), (k3.inqf ht).trans (Fiq t ht), (k3.scf ht).trans (Fsc t ht),
        ?_, k3.idleW.trans ei2', (k3.scf hdT).trans (Fsc hd hdT), F2.trans (Foot.ipc fu)⟩
      · obtain ⟨hy1, hy2⟩ := hy
        rcases hy1 with hy1 | hy1
        · exact absurd hy1 (Set.notMem_empty _)
        · exact absurd hy1 hy2
      · rcases k3.act with e' | e'
        · rw [e', ea2']; exact hc.na
        · rw [e']; exact fun e2 => notT_small hT (by simp) (e2 ▸ ht)
    · rename_i hi
      have hi0 : i = 0#u64 := by simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hi; exact hi
      refine (WP.spec_ok _).2 ⟨_, h2, hB2, hX2, hS2, hSg2, fun y hy => by simpa using hy, Or.inl (Or.inr rfl),
        by rw [hds2]; exact blocked_not_runnable (Or.inr (Or.inl rfl)), fun _ => by rw [← ei, hi0],
        fun hm => absurd (Or.inr rfl) hm, fun hi' => absurd hi0 (by simpa using hi'),
        Fst t ht, Fiq t ht, Fsc t ht, by rw [ea2']; exact hc.na, ei2', Fsc hd hdT, F2⟩
  rintro s3 ⟨X3, h3, hB3, hX3, hS3, hSg3, hXc3, hx3, hnr3, hz3, hin3, hpu3, st3, iq3, sc3, na3, ei3, shd3, F3⟩
  have hdA3 : L.mem s3 (scA hd) ≠ 0#u64 → L.mem s3 (scA hd) ∈ Ac := fun h0 => by
    rw [shd3] at h0 ⊢
    exact hB.sact hd hdT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [hds]; exact Or.inr (Or.inl rfl))))))))
      h0
  have htA3 : L.mem s3 (scA t) ≠ 0#u64 → L.mem s3 (scA t) ∈ Ac := fun h0 => by
    rw [sc3] at h0 ⊢; exact hc.ac h0
  have htq3 : (L.mem s3 (inqA t) &&& sched.Q_QUEUED) = 0#u64 := by rw [iq3]; exact hc.nq
  have htr3 : (L.mem s3 (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by rw [iq3]; exact hc.nr
  have hnb3 : ¬ Blocked (L.mem s3 (stA t)) := by rw [st3]; exact hc.nb
  have hnrp3 : L.mem s3 (stA t) ≠ sched.TS_BLOCKED_ON_REPLY := by rw [st3]; exact hc.nrp
  have hcold3 : L.mem s3 (stA t) ≠ sched.TS_BLOCKED_ON_REPLY ∧ L.mem s3 (stA t) ≠ sched.TS_BLOCKED_ON_RECV :=
    ⟨hnrp3, fun e' => hnb3 (Or.inr (Or.inl e'))⟩
  obtain ⟨dq, dr, da⟩ := blocked_out h3 hdT hnr3
  have hidle3 : L.idleW s3 ≠ t := by rw [ei3]; exact hidle
  have hnt3 : ∀ r ∈ Rp, L.mem s3 (rTcbA r) ≠ t := hX3.noref hta hcold3.1 hcold3.2
  have hnd3 : ∀ r ∈ Rp, L.mem s3 (rTcbA r) ≠ hd := by
    by_cases hm : hd ∈ X3
    · exact hX3.noref0 hdta (hz3 hm)
    · have e' := hin3 hm
      exact hX3.noref hdta (by rw [e']; exact inactive_ne.1) (by rw [e']; exact inactive_ne.2)
  refine WP.spec_bind (Pₘ := fun r : S × A => ∃ X4 : Set U64, (∃ Q4 R4, SchedQueuesInvX st T Cs Ω H X4 r.1 Q4 R4) ∧
      BoundInv st T Ac r.1 ∧ XInv st T Cs Ω Sg Rp Scs Nt Z r.1 ∧ SCsOK st T Ω Sg Scs Z Ac r.1 ∧ SgOK st Ω Sg r.1 ∧
      ExcT X4 hd ∧ (hd ∈ X4 ∨ ¬ Blocked (L.mem r.1 (stA hd))) ∧ (∀ r' ∈ Rp, L.mem r.1 (rTcbA r') ≠ hd) ∧
      (L.mem r.1 (scA hd) ≠ 0#u64 → L.mem r.1 (scA hd) ∈ Ac) ∧
      Foot st T Cs Sg Scs Z (EH H) s3 r.1) ?_ ?_
  rotate_left
  · rintro ⟨s4, a1⟩ ⟨X4, ⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4, hXc4, hx4, hnr4, hdA4, f4⟩
    try simp only [WP.uncurry'_pair]
    refine WP.spec_mono (send_tail.foot (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s4 a1 hd Q4 R4 h4 hB4 hX4 hS4
      hSg4 hdT hXc4 hx4 hnr4 hdA4) fun r hr => ?_
    obtain ⟨s', a'⟩ := r
    simp only [WP.uncurry'_pair] at hr ⊢
    exact F3.trans (Foot.ipc (f4.trans hr))
  have Ppush : ∀ cd : Bool, (i != 0#u64) = true → ipc.reply_push st ar s3 a t hd i cd ⦃ r => ∃ X4 : Set U64,
      (∃ Q4 R4, SchedQueuesInvX st T Cs Ω H X4 r.1 Q4 R4) ∧
      BoundInv st T Ac r.1 ∧ XInv st T Cs Ω Sg Rp Scs Nt Z r.1 ∧ SCsOK st T Ω Sg Scs Z Ac r.1 ∧ SgOK st Ω Sg r.1 ∧
      ExcT X4 hd ∧ (hd ∈ X4 ∨ ¬ Blocked (L.mem r.1 (stA hd))) ∧ (∀ r' ∈ Rp, L.mem r.1 (rTcbA r') ≠ hd) ∧
      (L.mem r.1 (scA hd) ≠ 0#u64 → L.mem r.1 (scA hd) ∈ Ac) ∧
      Foot st T Cs Sg Scs Z (EH H) s3 r.1 ⦄ := by
    intro cd hi
    obtain ⟨hdX, hiR, hiz⟩ := hpu3 hi
    have hi0 : i ≠ 0#u64 := by simpa using hi
    refine WP.spec_mono (WP.spec_and (ipc.reply_push.ipc hA s3 a t hd i cd Q R h3
      (fun y hy => absurd (hXc3 y hy ▸ hy) hdX) (Or.inr hnb3) hB3 hX3 hS3 hSg3 ht htq3 htr3 na3 hidle3 hcold3
      hiR hi0 hiz hdT hdt dq dr da (by rw [ei3]; exact hdi) htA3)
      (ipc.reply_push.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) hA s3 a t hd i cd h3
      (fun y hy => absurd (hXc3 y hy ▸ hy) hdX) (Or.inr hnb3) hB3 hX3 hS3 hSg3 ht htq3 htr3 na3 hidle3 hcold3
      hiR hi0 hiz hdT htA3)) fun r hh' => ?_
    obtain ⟨s4, a4⟩ := r
    simp only [WP.uncurry'_pair] at hh'
    obtain ⟨hh, fk⟩ := hh'
    obtain ⟨⟨⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4⟩, st4, sc4⟩ := hh
    have e4 : L.mem s4 (stA hd) = sched.TS_INACTIVE := (st4 hd hdT hdt).trans (hin3 hdX)
    exact ⟨∅, ⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4, fun y hy => absurd hy (Set.notMem_empty _),
      Or.inr (by rw [e4]; exact not_blocked_inactive),
      hX4.noref hdta (by rw [e4]; exact inactive_ne.1) (by rw [e4]; exact inactive_ne.2), fun h0 => by
        rcases sc4 with e | e
        · rw [e] at h0 ⊢; exact hdA3 h0
        · rw [e] at h0 ⊢; exact htA3 h0, fk⟩
  have Pinact : (do
      let s5 ← sched.set_thread_state st s3 t sched.TS_INACTIVE
      ok (s5, a)) ⦃ r => ∃ X4 : Set U64, (∃ Q4 R4, SchedQueuesInvX st T Cs Ω H X4 r.1 Q4 R4) ∧
      BoundInv st T Ac r.1 ∧ XInv st T Cs Ω Sg Rp Scs Nt Z r.1 ∧ SCsOK st T Ω Sg Scs Z Ac r.1 ∧ SgOK st Ω Sg r.1 ∧
      ExcT X4 hd ∧ (hd ∈ X4 ∨ ¬ Blocked (L.mem r.1 (stA hd))) ∧ (∀ r' ∈ Rp, L.mem r.1 (rTcbA r') ≠ hd) ∧
      (L.mem r.1 (scA hd) ≠ 0#u64 → L.mem r.1 (scA hd) ∈ Ac) ∧
      Foot st T Cs Sg Scs Z (EH H) s3 r.1 ⦄ := by
    refine WP.spec_bind (WP.spec_and (sts_all s3 t _ Q R h3 hB3 hX3 hS3 hSg3 ht not_blocked_inactive inactive_ne (Or.inr hnb3)
      hnt3 ⟨fun c hc' p hp hm => absurd hm (h3.notQ ht htq3 hc' hp), fun c hc' hm => absurd hm (h3.notR ht htr3 hc'),
        fun e' => absurd e' na3⟩)
      (sched.set_thread_state.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s3 t _ h3 ht)) fun s4 hh' => ?_
    obtain ⟨hh, fk⟩ := hh'
    obtain ⟨h4, hB4, hX4, hS4, hSg4, -, k4⟩ := hh
    refine (WP.spec_ok _).2 ⟨{y | y ∈ X3 ∧ y ≠ t}, ⟨Q, R, h4⟩, hB4, hX4, hS4, hSg4,
      fun y hy => hXc3 y hy.1, ?_, fun r hr => ?_, fun h0 => by rw [k4.scf hdT] at h0 ⊢; exact hdA3 h0, fk⟩
    · rcases hx3 with hm | hnb
      · exact Or.inl ⟨hm, hdt⟩
      · exact Or.inr (by rw [k4.stf hdT hdt]; exact hnb)
    · rcases k4.rtcb r hr with e' | ⟨-, e'⟩
      · rw [e']; exact hnd3 r hr
      · rw [e']; exact fun e2 => hdta.ne0 (by rw [← e2]; rfl)
  have Pok : (ok (s3, a) : Result (S × A)) ⦃ r => ∃ X4 : Set U64, (∃ Q4 R4, SchedQueuesInvX st T Cs Ω H X4 r.1 Q4 R4) ∧
      BoundInv st T Ac r.1 ∧ XInv st T Cs Ω Sg Rp Scs Nt Z r.1 ∧ SCsOK st T Ω Sg Scs Z Ac r.1 ∧ SgOK st Ω Sg r.1 ∧
      ExcT X4 hd ∧ (hd ∈ X4 ∨ ¬ Blocked (L.mem r.1 (stA hd))) ∧ (∀ r' ∈ Rp, L.mem r.1 (rTcbA r') ≠ hd) ∧
      (L.mem r.1 (scA hd) ≠ 0#u64 → L.mem r.1 (scA hd) ∈ Ac) ∧
      Foot st T Cs Sg Scs Z (EH H) s3 r.1 ⦄ :=
    (WP.spec_ok _).2 ⟨X3, ⟨Q, R, h3⟩, hB3, hX3, hS3, hSg3, hXc3, hx3, hnd3, hdA3, Foot.refl _⟩
  have Pdon : can_donate = true → (do
      let i2 ← obj.Tcb.sc st hd s3
      if i2 = 0#u64 then do
          let i3 ← obj.Tcb.sc st t s3
          schedcontext.donate st ar s3 a i3 hd
        else ok (s3, a)) ⦃ r => ∃ X4 : Set U64, (∃ Q4 R4, SchedQueuesInvX st T Cs Ω H X4 r.1 Q4 R4) ∧
      BoundInv st T Ac r.1 ∧ XInv st T Cs Ω Sg Rp Scs Nt Z r.1 ∧ SCsOK st T Ω Sg Scs Z Ac r.1 ∧ SgOK st Ω Sg r.1 ∧
      ExcT X4 hd ∧ (hd ∈ X4 ∨ ¬ Blocked (L.mem r.1 (stA hd))) ∧ (∀ r' ∈ Rp, L.mem r.1 (rTcbA r') ≠ hd) ∧
      (L.mem r.1 (scA hd) ≠ 0#u64 → L.mem r.1 (scA hd) ∈ Ac) ∧
      Foot st T Cs Sg Scs Z (EH H) s3 r.1 ⦄ := by
    intro hcd
    step with obj.Tcb.sc.spec as ⟨i2, ei2⟩
    split
    · rename_i hi2
      step with obj.Tcb.sc.spec as ⟨i3, ei3'⟩
      have hsc0 : L.mem s3 (scA t) ≠ 0#u64 := by rw [sc3]; exact hdon hcd
      obtain ⟨hiS, hitc, -⟩ := hX3.2.2.bound t ht hsc0
      rw [← ei3'] at hiS hitc
      refine WP.spec_mono (WP.spec_and (schedcontext.donate.ipc hA s3 a i3 hd t Q R h3 hB3 hX3 hS3 hSg3 ht ei3'.symm
        (by rw [ei3', sc3]; exact hdon hcd) ⟨htq3, htr3, na3⟩ hidle3 hdT (by rw [← ei2, hi2]) dq dr da hdt
        (by rw [ei3']; exact htA3 (by rw [sc3]; exact hdon hcd)) (by rw [ei3]; exact hdi))
        (schedcontext.donate.kwI (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) hA s3 a i3 hd h3 hX3.1 hiS hdT
          fun _ => by rw [hitc]; exact ⟨ht, htq3, htr3⟩))
        fun r hh' => ?_
      obtain ⟨s4, a4⟩ := r
      simp only [WP.uncurry'_pair] at hh'
      obtain ⟨hh, fk⟩ := hh'
      obtain ⟨⟨⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4⟩, st4, rp4, sd4⟩ := hh
      refine ⟨X3, ⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4, hXc3, ?_, ?_,
        fun _ => by rw [sd4, ei3']; exact htA3 (by rw [sc3]; exact hdon hcd), fk⟩
      · rcases hx3 with hm | hnb
        · exact Or.inl hm
        · exact Or.inr (by rw [st4 hd hdT]; exact hnb)
      · by_cases hm : hd ∈ X3
        · exact hX4.noref0 hdta (by rw [rp4 hd hdT]; exact hz3 hm)
        · have e' : L.mem s4 (stA hd) = sched.TS_INACTIVE := (st4 hd hdT).trans (hin3 hm)
          exact hX4.noref hdta (by rw [e']; exact inactive_ne.1) (by rw [e']; exact inactive_ne.2)
    · exact Pok
  split
  · repeat' split
    all_goals first
      | exact Pinact
      | exact Ppush _ (by assumption)
  · step with obj.Tcb.fault_type.any as ⟨i1, _⟩
    repeat' split
    all_goals first
      | exact Pinact
      | exact Ppush _ (by assumption)
      | exact Pdon (by assumption)
      | exact Pok



/-! ## `handle_fault_reply` writes only the receiver's registers -/

theorem obj.Tcb.set_reg.rg {s : S} {t r v : U64} (hT : TcbPlaced T) (ht : t ∈ T) (hr : r.val < 384) :
    obj.Tcb.set_reg st t s r v ⦃ s' => WritesIn st s s' (XferRegW T ∅) ⦄ :=
  WP.spec_mono (obj.Tcb.set_reg.wrK s t r v (hT t ht) hr) fun s' ⟨K, hK, e⟩ => by
    subst e
    exact (writesIn_wr (field_aligned (hT t ht) (by omega) (by omega))).mono fun b e =>
      Or.inl ⟨t, ht, K, by omega, by omega, by omega, e⟩

theorem obj.Tcb.set_debug_reg.rg {s : S} {t i v : U64} (hT : TcbPlaced T) (ht : t ∈ T) (hi : i.val < 8) :
    obj.Tcb.set_debug_reg st t s i v ⦃ s' => WritesIn st s s' (XferRegW T ∅) ⦄ := by
  unfold obj.Tcb.set_debug_reg
  simp only [lift, bind_ok]
  refine WP.spec_mono (LawfulStore.write_spec s _ v) fun s' e => ?_
  subst e
  have hta := hT t ht
  let K : U64 := ⟨BitVec.ofNat 64 (448 + 8 * i.val)⟩
  have hK : K.val = 448 + 8 * i.val := by
    show (BitVec.ofNat 64 (448 + 8 * i.val)).toNat = _
    simp; omega
  have ea : core.num.U64.wrapping_add (core.num.U64.wrapping_add t layout.tcb.DEBUG)
      (core.num.U64.wrapping_mul i 8#u64) = core.num.U64.wrapping_add t K := by
    apply UScalar.eq_of_val_eq
    rw [field_val hta (by omega)]
    have := hta.fits
    simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits,
      layout.tcb.DEBUG] at ⊢
    omega
  rw [ea]
  exact (writesIn_wr (field_aligned hta (by omega) (by omega))).mono fun b e =>
    Or.inl ⟨t, ht, K, by omega, by omega, by omega, e⟩

theorem rg_trans {s1 s2 s3 : S} (h1 : WritesIn st s1 s2 (XferRegW T ∅)) (h2 : WritesIn st s2 s3 (XferRegW T ∅)) :
    WritesIn st s1 s3 (XferRegW T ∅) := (h1.trans h2).mono fun _ hb => hb.elim id id

theorem faults.copy_mrs_fault_reply_loop0.rg {s0 s : S} {snd rcv : U64} {regs : Slice U64} {n i : Usize}
    (hT : TcbPlaced T) (hr : rcv ∈ T) (hR : ∀ x ∈ regs.val, x.val < 384) (h : WritesIn st s0 s (XferRegW T ∅)) :
    faults.copy_mrs_fault_reply_loop0 st s snd rcv regs n i ⦃ r => WritesIn st s0 r.1 (XferRegW T ∅) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold faults.copy_mrs_fault_reply_loop0
  apply loop.spec_decr_nat (measure := fun y => n.val - y.2.val)
    (inv := fun y => WritesIn st s0 y.1 (XferRegW T ∅))
  · rintro ⟨s1, j⟩ h1
    simp only at h1
    dsimp only
    unfold faults.copy_mrs_fault_reply_loop0.body
    dsimp only
    split
    · rename_i hjn
      split
      · rename_i hj
        have hj' : j.val < regs.val.length := by simpa using hj
        simp only [lift, bind_ok]
        split
        · refine WP.spec_bind (Slice.index_usize_spec regs j hj') fun rg hrg => ?_
          have hrg' : rg.val < 384 := hR rg (hrg ▸ List.getElem_mem hj')
          refine WP.spec_bind (msg.msg_register.lt _) fun i4 _ => ?_
          refine WP.spec_bind (P0.obj.Tcb.reg.p0 st snd s1 i4 hS) fun v _ => ?_
          refine WP.spec_bind (P0.regs.sanitise.p0 rg v) fun v5 _ => ?_
          refine WP.spec_bind (obj.Tcb.set_reg.rg (v := v5) (s := s1) hT hr hrg') fun s2 w2 => ?_
          step as ⟨j2, hj2⟩
          refine ⟨rg_trans h1 w2, ?_⟩
          have : j.val < n.val := by simpa using hjn
          omega
        · exact (WP.spec_ok _).2 h1
      · exact (WP.spec_ok _).2 h1
    · exact (WP.spec_ok _).2 h1
  · exact h

theorem faults.copy_mrs_fault_reply_loop1.rg {s0 s : S} {rcv buf : U64} {regs : Slice U64} {n i : Usize}
    (hT : TcbPlaced T) (hr : rcv ∈ T) (hR : ∀ x ∈ regs.val, x.val < 384) (h : WritesIn st s0 s (XferRegW T ∅)) :
    faults.copy_mrs_fault_reply_loop1 st s rcv regs n i buf ⦃ s' => WritesIn st s0 s' (XferRegW T ∅) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold faults.copy_mrs_fault_reply_loop1
  apply loop.spec_decr_nat (measure := fun y => n.val - y.2.val)
    (inv := fun y => WritesIn st s0 y.1 (XferRegW T ∅))
  · rintro ⟨s1, j⟩ h1
    simp only at h1
    dsimp only
    unfold faults.copy_mrs_fault_reply_loop1.body
    dsimp only
    split
    · rename_i hjn
      split
      · rename_i hj
        have hj' : j.val < regs.val.length := by simpa using hj
        refine WP.spec_bind (Slice.index_usize_spec regs j hj') fun rg hrg => ?_
        have hrg' : rg.val < 384 := hR rg (hrg ▸ List.getElem_mem hj')
        simp only [lift, bind_ok]
        refine WP.spec_bind (P0.msg.buf_get.p0 st s1 buf _ hS) fun v _ => ?_
        refine WP.spec_bind (P0.regs.sanitise.p0 rg v) fun v5 _ => ?_
        refine WP.spec_bind (obj.Tcb.set_reg.rg (v := v5) (s := s1) hT hr hrg') fun s2 w2 => ?_
        step as ⟨j2, hj2⟩
        refine ⟨rg_trans h1 w2, ?_⟩
        have : j.val < n.val := by simpa using hjn
        omega
      · exact (WP.spec_ok _).2 h1
    · exact (WP.spec_ok _).2 h1
  · exact h

theorem faults.copy_mrs_fault_reply.rg {s : S} {snd rcv len : U64} {regs : Slice U64}
    (hT : TcbPlaced T) (hr : rcv ∈ T) (hR : ∀ x ∈ regs.val, x.val < 384) :
    faults.copy_mrs_fault_reply st s snd rcv regs len ⦃ s' => WritesIn st s s' (XferRegW T ∅) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold faults.copy_mrs_fault_reply
  simp only [lift, bind_ok]
  refine WP.spec_bind (Pₘ := fun _ => True) (by split <;> exact (WP.spec_ok _).2 trivial) fun n _ => ?_
  refine WP.spec_bind (faults.copy_mrs_fault_reply_loop0.rg (snd := snd) (n := n) (i := 0#usize) hT hr hR
    (WritesIn.refl s _)) ?_
  rintro ⟨s1, i2⟩ w1
  simp only at w1
  try simp only [WP.uncurry'_pair]
  try simp only [uncurry_apply_pair]
  split
  · refine WP.spec_bind (P0.msg.lookup_ipc_buffer.p0 st s1 false snd hS) fun buf _ => ?_
    split
    · exact faults.copy_mrs_fault_reply_loop1.rg hT hr hR w1
    · exact (WP.spec_ok _).2 w1
  · exact (WP.spec_ok _).2 w1

theorem debug.configure_single_stepping.rg {A : Type _} {ar : machine.Arch A} {s : S} {a : A} {t bp n : U64}
    {rep : Bool} (hT : TcbPlaced T) (ht : t ∈ T) :
    debug.configure_single_stepping st ar s a t bp n rep ⦃ r => WritesIn st s r.2.1 (XferRegW T ∅) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold debug.configure_single_stepping
  refine WP.spec_bind (Pₘ := fun s1 => WritesIn st s s1 (XferRegW T ∅)) ?_ fun s1 w1 => ?_
  · split
    · refine WP.spec_bind (obj.Tcb.set_debug_reg.rg (s := s) (v := 0#u64) hT ht (by simp [debug.SS_ENABLED]))
        fun s2 w2 => ?_
      refine WP.spec_bind (P0.obj.Tcb.reg.p0 st t s2 _ hS) fun i _ => ?_
      unfold debug.EFLAGS_TF
      step as ⟨i1, _⟩
      simp only [lift, bind_ok]
      exact WP.spec_mono (obj.Tcb.set_reg.rg (s := s2) hT ht (by simp [layout.reg.FLAGS])) fun s3 w3 =>
        rg_trans w2 w3
    · exact obj.Tcb.set_debug_reg.rg hT ht (by simp [debug.SS_ENABLED])
  refine WP.spec_bind (obj.Tcb.set_debug_reg.rg (s := s1) (v := n) hT ht (by simp [debug.SS_COUNT])) fun s2 w2 => ?_
  exact (WP.spec_ok _).2 (rg_trans w1 w2)

theorem faults.handle_fault_reply.rg {A : Type _} {ar : machine.Arch A} {s : S} {a : A} {rcv snd : U64}
    (hT : TcbPlaced T) (hr : rcv ∈ T) :
    faults.handle_fault_reply st ar s a rcv snd ⦃ r => WritesIn st s r.2.1 (XferRegW T ∅) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold faults.handle_fault_reply
  refine WP.spec_bind (P0.msg.msg_info.p0 st s snd hS) fun tag _ => ?_
  refine WP.spec_bind (P0.obj.Tcb.fault_type.p0 st rcv s hS) fun ty _ => ?_
  have C : ∀ (regs : Slice U64), (∀ x ∈ regs.val, x.val < 384) →
      (do
        let s2 ← faults.copy_mrs_fault_reply st s snd rcv regs tag.length
        ok (decide (tag.label = 0#u64), s2, a)) ⦃ r => WritesIn st s r.2.1 (XferRegW T ∅) ⦄ := fun regs hR =>
    WP.spec_bind (faults.copy_mrs_fault_reply.rg hT hr hR) fun s2 w2 => (WP.spec_ok _).2 w2
  split
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  split
  · simp only [lift, bind_ok]
    exact C _ (by simp [faults.SYSCALL_MESSAGE, Aeneas.Std.Array.make, Aeneas.Std.Array.to_slice, layout.reg.RAX,
      layout.reg.RBX, layout.reg.RCX, layout.reg.RDX, layout.reg.RSI, layout.reg.RDI, layout.reg.RBP, layout.reg.R8,
      layout.reg.R9, layout.reg.R10, layout.reg.R11, layout.reg.R12, layout.reg.R13, layout.reg.R14, layout.reg.R15,
      layout.reg.FAULT_IP, layout.reg.RSP, layout.reg.FLAGS])
  split
  · simp only [lift, bind_ok]
    exact C _ (by simp [faults.EXCEPTION_MESSAGE, Aeneas.Std.Array.make, Aeneas.Std.Array.to_slice,
      layout.reg.FAULT_IP, layout.reg.RSP, layout.reg.FLAGS])
  split
  · simp only [lift, bind_ok]
    exact C _ (by simp [faults.TIMEOUT_REPLY_MESSAGE, Aeneas.Std.Array.make, Aeneas.Std.Array.to_slice,
      layout.reg.RAX, layout.reg.RBX, layout.reg.RCX, layout.reg.RDX, layout.reg.RSI, layout.reg.RDI, layout.reg.RBP,
      layout.reg.R8, layout.reg.R9, layout.reg.R10, layout.reg.R11, layout.reg.R12, layout.reg.R13, layout.reg.R14,
      layout.reg.R15, layout.reg.FAULT_IP, layout.reg.RSP, layout.reg.FLAGS, layout.reg.TLS_BASE])
  split
  · refine WP.spec_bind (P0.obj.Tcb.fault_w0.p0 st rcv s hS) fun w0 _ => ?_
    split
    · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
    refine WP.spec_bind (Pₘ := fun _ => True) (by
      split
      · exact (WP.spec_ok _).2 trivial
      · exact WP.spec_bind (msg.msg_register.lt _) fun _ _ => WP.spec_mono (P0.obj.Tcb.reg.p0 st snd s _ hS)
          fun _ _ => trivial) fun ni _ => ?_
    refine WP.spec_bind (debug.configure_single_stepping.rg (s := s) (a := a) (bp := 0#u64) (n := ni) (rep := true)
      hT hr) ?_
    rintro ⟨b, s1, a1⟩ w1
    try simp only [WP.uncurry'_pair]
    exact (WP.spec_ok _).2 w1
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)

/-! ## Field and state writes from `BXI` -/


/-- `send_ipc.foot` from `BlkOK` (P3's `SendIpcFootP1` shape, with the
widened footprint). -/
theorem endpoint.send_ipc.footB {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {U : Set U64}
    (hxf : XferOK st ar T Cs Ω H Sg Rp Scs Nt Z U) {RS : S → S → Prop} (hxw : XferFootOK st ar T Cs Ω H Sg Rp Scs Nt Z U RS)
    (s : S) (a : A) (blocking do_call : Bool) (badge : U64) (can_grant can_grant_reply can_donate : Bool) (t e : U64)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hU : UserOK st T Cs Ω H U s)
    (hc : CanBlock st T Ac s t) (hdon : can_donate = true → L.mem s (scA t) ≠ 0#u64)
    (hH : H e = some .ep) (hRSK : ∀ s0 s1 s2 : S, RS s0 s1 → WritesIn st s1 s2 (KW st T Cs Sg Scs Z (EH H) s1) → RS s2 s2)
    (hRS0 : RS s s) :
    endpoint.send_ipc st ar s a blocking do_call badge can_grant can_grant_reply can_donate t e
      ⦃ s' _ => IpcFoot st T Cs Ω Sg Scs Z (EH H) U s s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  exact endpoint.send_ipc.foot hA hxf hxw s a blocking do_call badge can_grant can_grant_reply can_donate t e Q R
    h0 hB hX hS hSg hU hc hdon hH hRSK hRS0

theorem faults.set_fault.kw (s : S) (t : obj.Tcb) (f : error.Fault) (hT : TcbPlaced T) (ht : t ∈ T) :
    faults.set_fault st s t f ⦃ s' => Foot st T Cs Sg Scs Z Es s s' ⦄ := by
  have W : ∀ {s₁ : S} (K v : U64), Foot st T Cs Sg Scs Z Es s s₁ → 3376 ≤ K.val → K.val < 3432 →
      K.val % 8 = 0 → Foot st T Cs Sg Scs Z Es s (L.wr s₁ (core.num.U64.wrapping_add t K) v) :=
    fun K v e h1 h2 h3 => e.trans (foot_field hT ht (by omega) (by omega) h3 (by omega))
  unfold faults.set_fault
  refine WP.spec_bind (Pₘ := fun r : S × U64 × U64 × U64 × U64 => Foot st T Cs Sg Scs Z Es s r.1) ?_ ?_
  · split
    all_goals first | exact (WP.spec_ok _).2 (Foot.refl s) | skip
    · refine WP.spec_bind (P0.error.LookupFault.encode.p0 _) ?_
      rintro ⟨lt, l0, l1⟩ -
      try simp only [uncurry_apply_pair]
      refine WP.spec_bind (obj.Tcb.set_lf_type.wr s t lt) fun s2 e2 => ?_
      subst e2
      have h2 := W (s₁ := s) 3408#u64 lt (Foot.refl s) (by simp) (by simp) (by simp)
      refine WP.spec_bind (obj.Tcb.set_lf_w0.wr _ t l0) fun s3 e3 => ?_
      subst e3
      have h3 := W 3416#u64 l0 h2 (by simp) (by simp) (by simp)
      refine WP.spec_bind (obj.Tcb.set_lf_w1.wr _ t l1) fun s4 e4 => ?_
      subst e4
      have h4 := W 3424#u64 l1 h3 (by simp) (by simp) (by simp)
      refine WP.spec_bind (Pₘ := fun _ : U64 => True) ?_ fun i _ => (WP.spec_ok _).2 h4
      split <;> exact (WP.spec_ok _).2 trivial
    · refine WP.spec_bind (Pₘ := fun _ : U64 => True) ?_ fun i _ =>
        (WP.spec_ok _).2 (Foot.refl s)
      split <;> exact (WP.spec_ok _).2 trivial
  · rintro ⟨s1, ty, w0, w1, w2⟩ hh
    try simp only [uncurry_apply_pair]
    simp only at hh
    refine WP.spec_bind (obj.Tcb.set_fault_type.spec s1 t ty) fun s2 e2 => ?_
    subst e2
    have h2 := W (s₁ := s1) 3376#u64 ty hh (by simp) (by simp) (by simp)
    refine WP.spec_bind (obj.Tcb.set_fault_w0.wr _ t w0) fun s3 e3 => ?_
    subst e3
    have h3 := W 3384#u64 w0 h2 (by simp) (by simp) (by simp)
    refine WP.spec_bind (obj.Tcb.set_fault_w1.wr _ t w1) fun s4 e4 => ?_
    subst e4
    have h4 := W 3392#u64 w1 h3 (by simp) (by simp) (by simp)
    exact WP.spec_mono (obj.Tcb.set_fault_w2.wr _ t w2) fun s5 e5 => by
      subst e5; exact W 3400#u64 w2 h4 (by simp) (by simp) (by simp)

theorem sporadic.unblock_check.kw {X : Set U64} (s : S) (t i : U64) {Q : U64 → U64 → List U64}
    {R : U64 → List U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T Ac s)
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (ht : t ∈ T)
    (i_post : i = L.mem s (scA t)) (hi0 : i ≠ 0#u64) (hiA : i ∈ Ac) :
    sporadic.unblock_check st s i ⦃ s' => Foot st T Cs Sg Scs Z Es s s' ⦄ := by
  have hT := h.tcbs
  have hsub := hSg.sub
  have hbt : L.mem s (scA t) ≠ 0#u64 := by rw [← i_post]; exact hi0
  obtain ⟨hiS, -, -⟩ := hX.2.2.bound t ht hbt
  rw [← i_post] at hiS
  have hW : RefillsWF st s i (Z i) := hS.wf hiS hiA
  have hSCin : SCin st s Ω i (Z i) := ⟨hW, hX.1.scW i hiS⟩
  have hN' := h.nodes _ h.cur
  have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
  have aR : Aligned (L.nodeA s layout.node.REPROGRAM) := nodeAt_aligned hN' (by rw [rp]; omega) (by rw [rp])
  have oR : Outside (L.nodeA s layout.node.REPROGRAM) i (Z i) :=
    hSCin.node_out h.omega h.cur hN' (by rw [rp]; omega) (by rw [rp])
  exact WP.spec_mono (sporadic.unblock_check.fr hW ⟨aR, oR⟩) fun s3 w => Foot.of w fun b hb => by
    rcases hb with hb | rfl
    · exact InRing.kw hiS hb
    · unfold LawfulStore.nodeA; exact kw_node h.cur (by rw [rp]; omega) (by rw [rp]; omega)

set_option maxHeartbeats 4000000 in
theorem faults.handle_timeout.foot {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {U : Set U64}
    (hxf : XferOK st ar T Cs Ω H Sg Rp Scs Nt Z U) {RS : S → S → Prop}
    (hxw : XferFootOK st ar T Cs Ω H Sg Rp Scs Nt Z U RS) {Ac : Set U64} (s : S) (a : A) (t : obj.Tcb) (f : error.Fault)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hU : UserOK st T Cs Ω H U s) (hc : CanBlock st T Ac s t)
    (hcap : obj.Tcb.slot t layout.tcb.SLOT_TIMEOUT_HANDLER ⦃ sl =>
      obj.Slot.cap st sl s ⦃ c => CapTyped H Rp Nt c ⦄ ⦄)
    (hRSK : ∀ s0 s1 s2 : S, RS s0 s1 → WritesIn st s1 s2 (KW st T Cs Sg Scs Z (EH H) s1) → RS s2 s2)
    (hRS0 : RS s s) :
    faults.handle_timeout st ar s a t f ⦃ s' _ => IpcFoot st T Cs Ω Sg Scs Z (EH H) U s s' ⦄ := by
  have ht := hc.mem
  unfold faults.handle_timeout
  refine WP.spec_bind hcap fun sl hsl => ?_
  refine WP.spec_bind hsl fun c hct => ?_
  unfold faults.send_fault_ipc
  refine WP.spec_bind (Pₘ := fun r : Bool × S × A => IpcFoot st T Cs Ω Sg Scs Z (EH H) U s r.2.1) ?_ ?_
  · split
    all_goals first | exact (WP.spec_ok _).2 (IpcFoot.refl s) | skip
    rename_i p b x y g gr
    have hpH := hct.1 p b x y g gr rfl
    refine WP.spec_bind (WP.spec_and (faults.set_fault.blk s t f h ht hU hc)
      (faults.set_fault.kw (Cs := Cs) (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s t f h.1.choose_spec.choose_spec.tcbs ht)) ?_
    rintro s1 ⟨⟨h1, hU1, hc1⟩, F1⟩
    obtain ⟨⟨Q1, R1, q1⟩, hB1, hX1, hS1, hSg1⟩ := h1
    refine WP.spec_bind (endpoint.send_ipc.foot hA hxf hxw s1 a true false b g gr false t p Q1 R1 q1 hB1 hX1 hS1 hSg1
      hU1 hc1 (fun e => by cases e) hpH hRSK (hRSK s s s1 hRS0 F1)) ?_
    rintro ⟨s2, a1⟩ h2
    exact (WP.spec_ok _).2 ((Foot.ipc F1).trans (by simpa using h2))
  · rintro ⟨x, s2, a2⟩ h2
    exact (WP.spec_ok _).2 h2


theorem RTail.postponeK {s : S} {i : U64} (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (r : RTail st T Ac s i)
    (hi0 : L.mem s (scA i) ≠ 0#u64) :
    sched.postpone st s (L.mem s (scA i)) ⦃ s' => Foot st T Cs Sg Scs Z Es s s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hSg, hS⟩ := h
  obtain ⟨hcS, htc, hcc⟩ := hX.2.2.bound i r.mem hi0
  have hm : scCoreA (L.mem s (scA i)) ∈ Ω := hSg.sub _ (hX.1.fixW _ hcS).2
  exact sched.postpone.kw s _ Q R h0 (by rw [htc]; exact r.mem) (by rw [htc]; exact r.nr) (h0.omega _ hm) hcc

set_option maxHeartbeats 4000000 in
theorem reply_tail.foot {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U) {RS : S → S → Prop}
    (hxw : XferFootOK st ar T Cs Ω H Sg Rp Scs Nt Z U RS)
    (tmoAny : ∀ (Ac : Set U64) (s : S) (t : U64), BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → t ∈ T →
      obj.Tcb.slot t layout.tcb.SLOT_TIMEOUT_HANDLER ⦃ sl => obj.Slot.cap st sl s ⦃ c => CapTyped H Rp Nt c ⦄ ⦄)
    {s3 : S} {a2 : A} {i ft : U64}
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s3) (r : RTail st T Ac s3 i) (hU : UserOK st T Cs Ω H U s3)
    (hRSK : ∀ s0 s1 s2 : S, RS s0 s1 → WritesIn st s1 s2 (KW st T Cs Sg Scs Z (EH H) s1) → RS s2 s2)
    (hRS0 : RS s3 s3) :
    (do
      let i3 ← obj.Tcb.sc st i s3
      let b2 ← obj.Sc.is_null i3
      if b2 then ok (s3, a2)
      else
        let b3 ← sched.is_runnable st s3 i
        if b3 then
          let b4 ← sporadic.ready st s3 i3
          if b4 then
            let b5 ← sporadic.sufficient st ar s3 a2 i3 0#u64
            if b5 then
              let s4 ← sched.possible_switch_to st s3 i
              ok (s4, a2)
            else
              let b6 ← faults.valid_timeout_handler st s3 i
              if b6 then
                if ft != fl4_abi.consts.fault.Timeout then
                  let badge ← obj.Sc.badge st i3 s3
                  faults.handle_timeout st ar s3 a2 i (error.Fault.Timeout badge)
                else
                  let s4 ← sched.postpone st s3 i3
                  ok (s4, a2)
              else
                let s4 ← sched.postpone st s3 i3
                ok (s4, a2)
          else
            let b5 ← faults.valid_timeout_handler st s3 i
            if b5 then
              if ft != fl4_abi.consts.fault.Timeout then
                let badge ← obj.Sc.badge st i3 s3
                faults.handle_timeout st ar s3 a2 i (error.Fault.Timeout badge)
              else
                let s4 ← sched.postpone st s3 i3
                ok (s4, a2)
            else
              let s4 ← sched.postpone st s3 i3
              ok (s4, a2)
        else ok (s3, a2)) ⦃ s' _ => IpcFoot st T Cs Ω Sg Scs Z (EH H) U s3 s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  step with obj.Tcb.sc.spec as ⟨i3, ei3⟩
  step with obj.Sc.is_null.spec as ⟨b2, eb2⟩
  split
  · exact (WP.spec_ok _).2 (IpcFoot.refl _)
  rename_i hb2
  have hi0 : L.mem s3 (scA i) ≠ 0#u64 := fun e => hb2 (by rw [eb2, ei3, e]; rfl)
  subst ei3
  refine WP.spec_bind (sched.is_runnable.spec' s3 i) fun b3 hb3 => ?_
  split
  swap
  · exact (WP.spec_ok _).2 (IpcFoot.refl _)
  rename_i hb3t
  have hrun := hb3 hb3t
  have PP : (do
      let s4 ← sched.postpone st s3 (L.mem s3 (scA i))
      ok (s4, a2)) ⦃ s' _ => IpcFoot st T Cs Ω Sg Scs Z (EH H) U s3 s' ⦄ :=
    WP.spec_bind (r.postponeK (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) h hi0) fun s4 h4 => (WP.spec_ok _).2 (Foot.ipc h4)
  have TO : ∀ badge : U64, faults.handle_timeout st ar s3 a2 i (error.Fault.Timeout badge) ⦃ s' _ =>
      IpcFoot st T Cs Ω Sg Scs Z (EH H) U s3 s' ⦄ := fun badge => faults.handle_timeout.foot hA (xferOK_of hA E) hxw s3 a2 i _ h.blk hU r.cb (tmoAny Ac s3 i h r.mem) hRSK hRS0
  have VT : (do
      let b6 ← faults.valid_timeout_handler st s3 i
      if b6 then
        if ft != fl4_abi.consts.fault.Timeout then
          let badge ← obj.Sc.badge st (L.mem s3 (scA i)) s3
          faults.handle_timeout st ar s3 a2 i (error.Fault.Timeout badge)
        else
          let s4 ← sched.postpone st s3 (L.mem s3 (scA i))
          ok (s4, a2)
      else
        let s4 ← sched.postpone st s3 (L.mem s3 (scA i))
        ok (s4, a2)) ⦃ s' _ => IpcFoot st T Cs Ω Sg Scs Z (EH H) U s3 s' ⦄ := by
    refine WP.spec_bind (P0.faults.valid_timeout_handler.p0 st s3 i hS) fun b6 _ => ?_
    split
    · split
      · exact WP.spec_bind (P0.obj.Sc.badge.p0 st _ s3 hS) fun badge _ => TO badge
      · exact PP
    · exact PP
  refine WP.spec_bind (sporadic.ready.spec s3 _) fun b4 _ => ?_
  split
  · refine WP.spec_bind (sporadic.sufficient.ok hA s3 a2 _ 0#u64) fun b5 _ => ?_
    split
    · exact WP.spec_bind (sched.possible_switch_to.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s3 i
      h.1.choose_spec.choose_spec r.mem) fun s4 h4 => (WP.spec_ok _).2 (Foot.ipc h4)
    · exact VT
  · exact VT

set_option maxHeartbeats 4000000 in
/-- **`do_reply_transfer`** (seL4 `doReplyTransfer`) keeps the invariants. -/
theorem ipc.do_reply_transfer.foot {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U) {RS : S → S → Prop}
    (hxw : XferFootOK st ar T Cs Ω H Sg Rp Scs Nt Z U RS)
    (tmoAny : ∀ (Ac : Set U64) (s : S) (t : U64), BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → t ∈ T →
      obj.Tcb.slot t layout.tcb.SLOT_TIMEOUT_HANDLER ⦃ sl => obj.Slot.cap st sl s ⦃ c => CapTyped H Rp Nt c ⦄ ⦄)
    (userOK : ∀ (Ac : Set U64) (s : S), BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → UserOK st T Cs Ω H U s)
    (s : S) (a : A) (ct r : U64) (grant : Bool) (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hr : r ∈ Rp)
    (hct : ct ∈ T)
    (hRSK : ∀ s0 s1 s2 : S, RS s0 s1 → WritesIn st s1 s2 (KW st T Cs Sg Scs Z (EH H) s1) → RS s2 s2)
    (hRS0 : RS s s) :
    ipc.do_reply_transfer st ar s a ct r grant ⦃ s' _ => IpcFoot st T Cs Ω Sg Scs Z (EH H) U s s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hT := h.1.choose_spec.choose_spec.tcbs
  unfold ipc.do_reply_transfer
  refine WP.spec_bind (obj.Reply.tcb.blk s r) fun i ei => ?_
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 (IpcFoot.refl _)
  rename_i hb
  have hi0 : i ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
  obtain ⟨-, hiT, -, -⟩ := h.2.2.1.2.1.back r hr (by rw [← ei]; exact hi0)
  rw [← ei] at hiT
  step with obj.Tcb.state.spec as ⟨v, ev⟩
  split
  · exact (WP.spec_ok _).2 (IpcFoot.refl _)
  rename_i hv
  have hst : L.mem s (stA i) = sched.TS_BLOCKED_ON_REPLY := by
    rw [← ev]; apply UScalar.eq_of_val_eq; simpa [sched.TS_BLOCKED_ON_REPLY] using hv
  have hni : L.idleW s ≠ i := fun e => h.2.1.idleNB (by rw [e, hst]; exact Or.inr rfl)
  refine WP.spec_bind (ipc.reply_remove.blk (Es := EH H) hA s a r i h.blk hr hiT ei.symm hst) ?_
  rintro ⟨s3, a2⟩ ⟨h3b, st3, F3, sca3, id3⟩
  try simp only [WP.uncurry'_pair]
  have h3 := BlkOK.bxi h3b
  obtain ⟨dq3, dr3, da3⟩ := blocked_out h3.1.choose_spec.choose_spec hiT (by rw [st3]; exact not_runnable_inactive)
  have R3 : RPre st T Ac s3 i := ⟨hiT, st3, dq3, dr3, da3, by rw [id3]; exact hni, sca3⟩
  -- the SC's refills
  step with obj.Tcb.sc.spec as ⟨i2, ei2⟩
  refine WP.spec_bind (sporadic.sc_sporadic.spec s3 i2) fun b1 hb1 => ?_
  refine WP.spec_bind (Pₘ := fun s4 => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s4 ∧ RPre st T Ac s4 i ∧
    Foot st T Cs Sg Scs Z (EH H) s s4) ?_ ?_
  · split
    · rename_i hb1t
      have hi20 := (hb1 hb1t).1
      step with obj.Sc.cpu.spec as ⟨cpu, _⟩
      step with obj.node_get.spec as ⟨cs, _⟩
      split
      · obtain ⟨⟨Q, R, q3⟩, hB3, hX3, hSg3, hS3⟩ := h3
        refine WP.spec_mono (WP.spec_and (sporadic.unblock_check.all s3 i i2 q3 hB3 hX3 hS3 hSg3 hiT ei2 hi20
          (by rw [ei2]; exact sca3 (by rw [← ei2]; exact hi20)))
          (sporadic.unblock_check.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s3 i i2 q3 hB3 hX3 hS3 hSg3 hiT ei2
            hi20 (by rw [ei2]; exact sca3 (by rw [← ei2]; exact hi20)))) ?_
        rintro s4 ⟨⟨q4, hB4, hX4, hS4, hSg4, ea4, -, ei4, f4, -⟩, fu⟩
        refine ⟨⟨⟨Q, R, q4⟩, hB4, hX4, hSg4, hS4⟩, R3.keep ?_ ?_ ?_ ea4 ei4, F3.trans fu⟩
        · rw [stA_eq]; exact f4 i hiT _ (by simp) (by simp)
        · rw [inqA_eq]; exact f4 i hiT _ (by simp) (by simp)
        · rw [scA_eq]; exact f4 i hiT _ (by simp) (by simp)
      · exact (WP.spec_ok _).2 ⟨h3, R3, F3⟩
    · exact (WP.spec_ok _).2 ⟨h3, R3, F3⟩
  rintro s4 ⟨h4, R4, F4⟩
  refine WP.spec_bind (P0.obj.Tcb.fault_type.p0 st i s4 hS) fun ft _ => ?_
  refine WP.spec_bind (Pₘ := fun r : S × A => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧ RTail st T Ac r.1 i ∧
    IpcFoot st T Cs Ω Sg Scs Z (EH H) U s r.1 ∧ RS r.1 r.1) ?_ ?_
  · split
    · -- the message
      obtain ⟨⟨Q, R, q4⟩, hB4, hX4, hSg4, hS4⟩ := h4
      refine WP.spec_bind (WP.spec_and (xferOK_of hA E Ac ∅ Q R s4 a2 ct 0#u64 0#u64 grant i hct hiT q4 hB4 hX4 hS4 hSg4
        (userOK Ac s4 ⟨⟨Q, R, q4⟩, hB4, hX4, hSg4, hS4⟩))
        (hxw Ac ∅ Q R s4 a2 ct 0#u64 0#u64 grant i hct hiT q4 hB4 hX4 hS4 hSg4
        (userOK Ac s4 ⟨⟨Q, R, q4⟩, hB4, hX4, hSg4, hS4⟩) (hRSK s s s4 hRS0 F4))) ?_
      rintro s5 ⟨⟨q5, hB5, hX5, hS5, hSg5, ea5, -, ei5, -, f5, -, -⟩, w5, r5⟩
      have h5 : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s5 := ⟨⟨Q, R, q5⟩, hB5, hX5, hSg5, hS5⟩
      have R5 : RPre st T Ac s5 i := R4.keep (by rw [stA_eq]; exact f5 i hiT _ (by simp) (by simp) (by simp))
        (by rw [inqA_eq]; exact f5 i hiT _ (by simp) (by simp) (by simp))
        (by rw [scA_eq]; exact f5 i hiT _ (by simp) (by simp) (by simp)) ea5 ei5
      refine WP.spec_bind (WP.spec_and (R5.set h5 not_blocked_running running_ne)
        (sched.set_thread_state.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s5 i _ q5 hiT)) fun s6 h6 => ?_
      exact (WP.spec_ok _).2 ⟨h6.1.1, h6.1.2, (Foot.ipc F4).trans ((XferW.ipc w5).trans (Foot.ipc h6.2)),
        hRSK s4 s5 _ r5 h6.2⟩
    · -- the fault reply
      refine WP.spec_bind (WP.spec_and (faults.handle_fault_reply.rf (s := s4) (a := a2) (snd := ct) hT hiT)
        (faults.handle_fault_reply.rg (s := s4) (a := a2) (snd := ct) hT hiT)) ?_
      rintro ⟨rs, s5, a3⟩ ⟨w5, g5⟩
      try simp only [WP.uncurry'_pair]
      obtain ⟨⟨Q, R, q4⟩, hB4, hX4, hSg4, hS4⟩ := h4
      obtain ⟨q5, hB5, hX5, hS5, hSg5, ea5, -, ei5, -, f5, -⟩ :=
        xfer_all (U := ∅) q4 hB4 hX4 hS4 hSg4 (fun b hb => absurd hb (by simp)) w5
      have h5 : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s5 := ⟨⟨Q, R, q5⟩, hB5, hX5, hSg5, hS5⟩
      have R5 : RPre st T Ac s5 i := R4.keep (by rw [stA_eq]; exact f5 i hiT _ (by simp) (by simp) (by simp))
        (by rw [inqA_eq]; exact f5 i hiT _ (by simp) (by simp) (by simp))
        (by rw [scA_eq]; exact f5 i hiT _ (by simp) (by simp) (by simp)) ea5 ei5
      unfold faults.clear_fault
      refine WP.spec_bind (obj.Tcb.set_fault_type.spec s5 i _) fun s6 e6 => ?_
      subst e6
      have h6 := bxi_field (K := 3376#u64) (v := fl4_abi.consts.fault.NullFault) h5 hiT (by simp) (by simp)
        (by simp) (by simp)
      have hN5 := h5.1.choose_spec.choose_spec.nodes _ h5.1.choose_spec.choose_spec.cur
      have n6 := ani_field (K := 3376#u64) (v := fl4_abi.consts.fault.NullFault) hT hN5 hiT (by simp) (by simp)
      have fw : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3376 →
          L.mem (L.wr s5 (faultA i) fl4_abi.consts.fault.NullFault) (core.num.U64.wrapping_add i K) =
            L.mem s5 (core.num.U64.wrapping_add i K) := fun K a1 a2 a3 =>
        L.mem_wr_ne (field_aligned (K := 3376#u64) (hT i hiT) (by simp) (by simp)) (field_aligned (hT i hiT) a1 a2)
          (fun e => field_ne (K1 := 3376#u64) (hT i hiT) (hT i hiT) (by simp) a1 (fun _ => by simp; omega)
            (UScalar.eq_of_val_eq e))
      have R6 : RPre st T Ac (L.wr s5 (faultA i) fl4_abi.consts.fault.NullFault) i :=
        R5.keep (by rw [stA_eq]; exact fw _ (by simp) (by simp) (by simp))
          (by rw [inqA_eq]; exact fw _ (by simp) (by simp) (by simp))
          (by rw [scA_eq]; exact fw _ (by simp) (by simp) (by simp)) n6.1 n6.2.1
      have W5 : IpcFoot st T Cs Ω Sg Scs Z (EH H) U s4 s5 := w5.mono fun b hb => by
        rcases hb with hb | hb
        · exact Or.inr (Or.inl (Or.inl hb))
        · exact absurd hb (Set.notMem_empty _)
      have F6 : Foot st T Cs Sg Scs Z (EH H) s5 (L.wr s5 (faultA i) fl4_abi.consts.fault.NullFault) :=
        foot_field (K := 3376#u64) hT hiT (by simp) (by simp) (by simp) (by simp)
      have q6 := h6.1.choose_spec.choose_spec
      have G5 : Foot st T Cs Sg Scs Z (EH H) s4 s5 := Foot.of g5 fun b hb => by
        rcases hb with ⟨y, hy, K, h1, h2, -, rfl⟩ | hb
        · exact kw_field hy (by omega) (by omega) (by omega)
        · exact absurd hb (Set.notMem_empty _)
      have RS4 : RS s4 s4 := hRSK s s s4 hRS0 F4
      split
      · refine WP.spec_bind (WP.spec_and (R6.set h6 not_blocked_restart restart_ne)
          (sched.set_thread_state.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) _ i _ q6 hiT)) fun s7 h7 => ?_
        exact (WP.spec_ok _).2 ⟨h7.1.1, h7.1.2,
          (Foot.ipc F4).trans (W5.trans ((Foot.ipc F6).trans (Foot.ipc h7.2))),
          hRSK s4 s4 _ RS4 (G5.trans (F6.trans h7.2))⟩
      · refine WP.spec_bind (WP.spec_and (R6.set h6 not_blocked_inactive inactive_ne)
          (sched.set_thread_state.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) _ i _ q6 hiT)) fun s7 h7 => ?_
        exact (WP.spec_ok _).2 ⟨h7.1.1, h7.1.2,
          (Foot.ipc F4).trans (W5.trans ((Foot.ipc F6).trans (Foot.ipc h7.2))),
          hRSK s4 s4 _ RS4 (G5.trans (F6.trans h7.2))⟩
  rintro ⟨s6, a6⟩ ⟨h6, r6, F6, RS6⟩
  try simp only [WP.uncurry'_pair]
  refine WP.spec_mono (reply_tail.foot hA E hxw tmoAny h6 r6 (userOK Ac s6 h6) hRSK RS6)
    fun r hr => ?_
  obtain ⟨s', a'⟩ := r
  simp only [WP.uncurry'_pair] at hr ⊢
  exact F6.trans hr


end

end Fl4Proofs.P1
