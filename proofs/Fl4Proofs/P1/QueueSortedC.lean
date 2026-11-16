/-
P1: `cancel_ipc` keeps the IPC queues sorted (`ipc.cancel_ipc.sorted`).
Besides the dequeue (`ep_dequeue.sorted`, `ntfn_dequeue.sorted`) it writes
only frame words, node words and TCB fields other than the priority and the
`Ep` links (`SFt`), which keep `EpSorted` (`EpSorted.sft`).
-/
import Fl4Proofs.P1.QueueSorted
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

/-- Words no IPC queue reads: frame words, TCB fields other than the
priority and the `Ep` links, node words. -/
def SafeK {S : Type _} (st : machine.Store S) [L : LawfulStore st] (T Cs Sg : Set U64) (s : S) (b : U64) : Prop :=
  b ∈ Sg ∨ (∃ y ∈ T, ∃ K : U64, K.val < 4096 ∧ K.val ≠ 3448 ∧ K.val ≠ 3496 ∧ K.val ≠ 3504 ∧
    b = core.num.U64.wrapping_add y K) ∨ (∃ c ∈ Cs, ∃ o : U64, o.val < 4288 ∧ b = L.nodeAt s c o)

abbrev SFt {S : Type _} (st : machine.Store S) [L : LawfulStore st] (T Cs Sg : Set U64) (s s' : S) : Prop :=
  WritesIn st s s' (SafeK st T Cs Sg s)

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

theorem SafeK.ksb {s0 s1 : S} {b : U64} (hk : L.ksb s1 = L.ksb s0) (h : SafeK st T Cs Sg s1 b) :
    SafeK st T Cs Sg s0 b := by
  rcases h with h | h | ⟨c, hc, o, ho, e⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨c, hc, o, ho, by rw [e, nodeAt_of_ksb hk]⟩)

theorem SFt.refl (s : S) : SFt st T Cs Sg s s := WritesIn.refl _ _

theorem SFt.trans {s₁ s₂ s₃ : S} (h₁ : SFt st T Cs Sg s₁ s₂) (h₂ : SFt st T Cs Sg s₂ s₃) : SFt st T Cs Sg s₁ s₃ :=
  WritesIn.mono (WritesIn.trans h₁ h₂) fun b hb => Or.elim hb id fun hb => SafeK.ksb h₁.1 hb

theorem SFt.curN {s s' : S} (f : SFt st T Cs Sg s s') (hN : NodePlaced st T s (L.cpu s)) :
    NodePlaced st T s' (L.cpu s') := by rw [f.2.1]; exact hN.ksb f.1

theorem sfoot_wr {s : S} {a v : U64} (ha : Aligned a) (hk : SafeK st T Cs Sg s a) : SFt st T Cs Sg s (L.wr s a v) :=
  (writesIn_wr ha).mono fun b hb => hb ▸ hk

theorem sfoot_sgw {s : S} {a v : U64} (ha : Aligned a) (hm : a ∈ Sg) : SFt st T Cs Sg s (L.wr s a v) :=
  sfoot_wr ha (Or.inl hm)

theorem sfoot_field {s : S} {y K v : U64} (hT : TcbPlaced T) (hy : y ∈ T) (_hK : 192 ≤ K.val) (hK' : K.val < 4096)
    (hK8 : K.val % 8 = 0) (hKd : K.val ≠ 3448 ∧ K.val ≠ 3496 ∧ K.val ≠ 3504) :
    SFt st T Cs Sg s (L.wr s (core.num.U64.wrapping_add y K) v) :=
  sfoot_wr (field_aligned (hT y hy) hK' hK8) (Or.inr (Or.inl ⟨y, hy, K, hK', hKd.1, hKd.2.1, hKd.2.2, rfl⟩))

theorem sfoot_node {s : S} {c o v : U64} (hN : NodePlaced st T s c) (hc : c ∈ Cs) (ho : o.val < 4288)
    (h8 : o.val % 8 = 0) (_h88 : o.val ≠ 88) : SFt st T Cs Sg s (L.wr s (L.nodeAt s c o) v) :=
  sfoot_wr (nodeAt_aligned hN ho h8) (Or.inr (Or.inr ⟨c, hc, o, ho, rfl⟩))

/-- **A safe step keeps the queues sorted**, the placement from a state `s0`
with the same kernel base. -/
theorem EpSorted.sft {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {s0 s s' : S}
    (h : SchedQueuesInvX st T Cs Ω H X s0 Q R) (hsub : ∀ b ∈ Sg, b ∈ Ω) (hk : L.ksb s = L.ksb s0)
    (hS : EpSorted st T H s) (w : SFt st T Cs Sg s s') : EpSorted st T H s' := by
  have hT := h.tcbs
  obtain ⟨E, EQ, hEW⟩ := h.eps
  have hne : ∀ e, (H e = some .ep ∨ H e = some .ntfn) → ∀ b, SafeK st T Cs Sg s b →
      b ≠ epHeadA e ∧ b ≠ epTSA e := fun e he b hb => by
    have heE := (hEW.2.2.2.2.2.2.2.1 e).2 he
    obtain ⟨hE, hON, -⟩ := hEW.1 e heE
    have hv1 := epHeadA_val (ep := e)
    have hv2 := epTSA_val hE
    have key : b.val ≠ e.val ∧ b.val ≠ e.val + 8 := by
      rcases hb with hb | ⟨y, hy, K, hK, -, -, -, rfl⟩ | ⟨c, hc, o, ho, rfl⟩
      · have := hEW.2.2.1 e heE b (hsub b hb); omega
      · rw [field_val (hT y hy) hK]; have := hE.disj y hy; omega
      · have hN : NodePlaced st T s c := (h.nodes c hc).ksb hk
        rw [nodeAt_val hN ho]
        have h1 := hON.1 c hc
        simp only [LawfulStore.nodeBase, hk] at h1 ⊢
        omega
    exact ⟨fun e' => by have := congrArg UScalar.val e'; rw [hv1] at this; exact key.1 this,
      fun e' => by have := congrArg UScalar.val e'; rw [hv2] at this; exact key.2 this⟩
  refine EpSorted.keep (u := 0#u64) hS (fun e he => ?_) (NoEp.of hT w fun b hb y hy K hK => ?_)
    (fun e he xs hx hm => hx.ne0 hT _ hm rfl)
  · have heE := (hEW.2.2.2.2.2.2.2.1 e).2 he
    obtain ⟨hE, -, -⟩ := hEW.1 e heE
    have k1 := w.mem_eq (ep_aligned hE).1 fun hb => (hne e he _ hb).1 rfl
    have k2 := w.mem_eq (ep_aligned hE).2 fun hb => (hne e he _ hb).2 rfl
    simp only [LawfulStore.epQ, k1, k2]
  · have hK' := epK_val hK
    rcases hb with hb | ⟨y', hy', K', hK1, h1, h2, h3, rfl⟩ | ⟨c, hc, o, ho, rfl⟩
    · exact fun e => out_ne_field (h.omega _ (hsub b hb)) hy (hT y hy) (by omega) (congrArg UScalar.val e).symm
    · exact field_ne (hT y' hy') (hT y hy) hK1 (by omega) fun _ => by omega
    · exact node_ne_field ((h.nodes c hc).ksb hk) ho hy (hT y hy) (by omega)

theorem sched.set_action.sf (s : S) (v : U64) (hN : NodePlaced st T s (L.cpu s)) (hc : L.cpu s ∈ Cs) :
    sched.set_action st s v ⦃ s' => SFt st T Cs Sg s s' ⦄ :=
  WP.spec_mono (sched.set_action.spec s v) fun s' e => by
    subst e; exact sfoot_node hN hc (by rw [act_val]; omega) (by rw [act_val]) (by rw [act_val]; omega)

theorem sched.schedule_tcb.sf (s : S) (t : obj.Tcb) (hN : NodePlaced st T s (L.cpu s)) (hc : L.cpu s ∈ Cs) :
    sched.schedule_tcb st s t ⦃ s' => SFt st T Cs Sg s s' ⦄ := by
  unfold sched.schedule_tcb
  step with sched.cur_thread.spec as ⟨t1, e1⟩
  step with tcb_eq.blk as ⟨b, eb⟩
  split
  · step with sched.action.spec as ⟨i, ei⟩
    split
    · step with sched.is_schedulable.spec as ⟨b1, eb1⟩
      split
      · exact (WP.spec_ok _).2 (SFt.refl _)
      · exact sched.set_action.sf s _ hN hc
    · exact (WP.spec_ok _).2 (SFt.refl _)
  · exact (WP.spec_ok _).2 (SFt.refl _)

theorem sched.set_thread_state.sf (s : S) (t : obj.Tcb) (v : U64) (hT : TcbPlaced T)
    (hN : NodePlaced st T s (L.cpu s)) (hc : L.cpu s ∈ Cs) (ht : t ∈ T) :
    sched.set_thread_state st s t v ⦃ s' => SFt st T Cs Sg s s' ⦄ := by
  unfold sched.set_thread_state
  refine WP.spec_bind (obj.Tcb.set_state.spec s t v) fun s1 e1 => ?_
  subst e1
  refine WP.spec_mono (sched.schedule_tcb.sf (Sg := Sg) _ t
    (by rw [LawfulStore.cpu_wr]; exact hN.ksb (L.ksb_wr _ _ _)) (by rw [LawfulStore.cpu_wr]; exact hc)) fun s2 f2 => ?_
  have f1 : SFt st T Cs Sg s (L.wr s (stA t) v) := by
    rw [stA_eq]; exact sfoot_field hT ht (by simp) (by simp) (by simp) (by simp)
  exact f1.trans f2

theorem ipc.reply_unlink.sf (s : S) (r t : U64) (hT : TcbPlaced T)
    (hN : NodePlaced st T s (L.cpu s)) (hc : L.cpu s ∈ Cs) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hr : r ∈ Rp)
    (ht : t ∈ T) : ipc.reply_unlink st s r t ⦃ s' => SFt st T Cs Sg s s' ⦄ := by
  unfold ipc.reply_unlink
  refine WP.spec_bind (obj.Reply.set_tcb.spec s r 0#u64) fun s1 e1 => ?_
  subst e1
  have f1 : SFt st T Cs Sg s (L.wr s (rTcbA r) 0#u64) := sfoot_sgw (rp_aligned hO hr).1 (hO.tcbW hr)
  exact WP.spec_mono (sched.set_thread_state.sf _ t _ hT (f1.curN hN) (by rw [f1.2.1]; exact hc) ht)
    fun s2 f2 => f1.trans f2

/-- `reply_remove_tcb`. -/
theorem ipc.reply_remove_tcb.sf (s : S) (t : obj.Tcb) (hT : TcbPlaced T)
    (hN : NodePlaced st T s (L.cpu s)) (hc : L.cpu s ∈ Cs) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s)
    (hR : ReplyT st Rp Scs s t) (ht : t ∈ T) :
    ipc.reply_remove_tcb st s t ⦃ s' => SFt st T Cs Sg s s' ⦄ := by
  obtain ⟨hi, -, hn, hp⟩ := hR
  unfold ipc.reply_remove_tcb
  step with obj.Tcb.reply_obj.spec as ⟨i, ei⟩
  step with obj.Reply.next.spec as ⟨next, enext⟩
  step with obj.Reply.prev.spec as ⟨prev, eprev⟩
  rw [← ei] at hi hn hp
  rw [← enext] at hn
  rw [← eprev] at hp
  refine WP.spec_bind (Pₘ := fun s1 => SFt st T Cs Sg s s1) ?_ ?_
  · split
    · rename_i hne
      have hn0 : next ≠ 0#u64 := by simpa using hne
      step with obj.Reply.next_is_head.spec as ⟨b, eb⟩
      split
      · rename_i hb
        have hS := (hn hn0).1 (by rw [← eb]; exact hb)
        exact WP.spec_mono (obj.Sc.set_reply.spec s next 0#u64) fun s1 e1 => by
          subst e1; exact sfoot_sgw (screp_aligned hO hS) (hO.repW _ hS)
      · rename_i hb
        have hRp := (hn hn0).2 (by rw [← eb]; simpa using hb)
        exact WP.spec_mono (obj.Reply.set_prev.spec s next 0#u64) fun s1 hs1 => by
          obtain ⟨w, e1, -⟩ := hs1; subst e1; exact sfoot_sgw (rp_aligned hO hRp).2.1 (hO.prevW hRp)
    · exact (WP.spec_ok _).2 (SFt.refl _)
  intro s1 f1
  refine WP.spec_bind (Pₘ := fun s2 => SFt st T Cs Sg s s2) ?_ ?_
  · split
    · rename_i hne
      have hRp := hp (by simpa using hne)
      exact WP.spec_mono (obj.Reply.set_next.spec s1 prev 0#u64) fun s2 hs2 => by
        obtain ⟨w, e2, -⟩ := hs2; subst e2; exact f1.trans (sfoot_sgw (rp_aligned hO hRp).2.2 (hO.nextW hRp))
    · exact (WP.spec_ok _).2 f1
  intro s2 f2
  refine WP.spec_bind (obj.Reply.set_prev.spec s2 i 0#u64) fun s3 hs3 => ?_
  obtain ⟨w3, e3, -⟩ := hs3
  subst e3
  refine WP.spec_bind (obj.Reply.set_next.spec _ i 0#u64) fun s4 hs4 => ?_
  obtain ⟨w4, e4, -⟩ := hs4
  subst e4
  have f4 := (f2.trans (sfoot_sgw (v := w3) (rp_aligned hO hi).2.1 (hO.prevW hi))).trans
    (sfoot_sgw (v := w4) (rp_aligned hO hi).2.2 (hO.nextW hi))
  exact WP.spec_mono (ipc.reply_unlink.sf _ i t hT (f4.curN hN) (by rw [f4.2.1]; exact hc) hO.ksb hi ht)
    fun s5 f5 => f4.trans f5


/-- The endpoint branch of `cancel_ipc` keeps the queues sorted. -/
theorem ep_branch.sorted {A : Type _} (a : A) (s1 : S) (t : obj.Tcb) {Q : U64 → U64 → List U64}
    {R : U64 → List U64} (h1 : SchedQueuesInv st T Cs Ω H s1 Q R) (ht : t ∈ T) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s1)
    (hsub : ∀ b ∈ Sg, b ∈ Ω) (hb : Blocked (L.mem s1 (stA t))) (rcv : Prop)
    [Decidable rcv] (hrecv : rcv → L.mem s1 (replyA t) ≠ 0#u64 → L.mem s1 (replyA t) ∈ Rp)
    (hS1 : EpSorted st T H s1) :
    (do
      let ep ← obj.Tcb.block_obj st t s1
      let s2 ← endpoint.ep_dequeue st s1 ep t
      let s3 ← if rcv then do
          let i ← obj.Tcb.reply_obj st t s2
          if (i != 0#u64) = true then ipc.reply_unlink st s2 i t else ok s2
        else ok s2
      let s4 ← sched.set_thread_state st s3 t sched.TS_INACTIVE
      ok (s4, a)) ⦃ s' _ => EpSorted st T H s' ⦄ := by
  have hT := h1.tcbs
  obtain ⟨E1, EQ1, hW1⟩ := h1.eps
  obtain ⟨he, hm⟩ := hW1.2.2.2.2.1 t ht (by simp) hb
  obtain ⟨hE, -, hq⟩ := hW1.1 _ he
  step with obj.Tcb.block_obj.spec as ⟨ep, ep_post⟩
  subst ep_post
  refine WP.spec_bind (WP.spec_and (WP.spec_and (endpoint.ep_dequeue.sorted hT hS1 hW1 he hm)
    (endpoint.ep_dequeue.foot s1 _ t _ hT hE hq hm)) (endpoint.ep_dequeue.inv s1 t Q R h1 ht (by simp) hb)) ?_
  rintro s2 ⟨⟨hS2, w2⟩, -, f2, o2, -, -, -, -⟩
  have hN1 := h1.nodes _ h1.cur
  have hN2 : NodePlaced st T s2 (L.cpu s2) := by rw [w2.2.1]; exact hN1.ksb w2.1
  have hc2 : L.cpu s2 ∈ Cs := by rw [w2.2.1]; exact h1.cur
  refine WP.spec_bind (Pₘ := fun s3 => SFt st T Cs Sg s2 s3) ?_ ?_
  · split
    · step with obj.Tcb.reply_obj.spec as ⟨i, i_post⟩
      split
      · rename_i hrc hi
        have r2 : L.mem s2 (replyA t) = L.mem s1 (replyA t) := f2 t ht _ (by simp) (by simp) (by simp) (by simp)
        have hr := hrecv hrc (by rw [← r2, ← i_post]; simpa using hi)
        rw [← r2, ← i_post] at hr
        exact ipc.reply_unlink.sf s2 i t hT hN2 hc2 hO.ksb hr ht
      · exact (WP.spec_ok _).2 (SFt.refl _)
    · exact (WP.spec_ok _).2 (SFt.refl _)
  intro s3 w3
  refine WP.spec_bind (sched.set_thread_state.sf (Sg := Sg) s3 t _ hT (w3.curN hN2) (by rw [w3.2.1]; exact hc2) ht)
    fun s4 w4 => ?_
  exact (WP.spec_ok _).2 (EpSorted.sft (Sg := Sg) h1 hsub w2.1 hS2 (w3.trans w4))

/-- `cancel_signal` keeps the queues sorted. -/
theorem notification.cancel_signal.sorted (s1 : S) (t : obj.Tcb) {Q : U64 → U64 → List U64}
    {R : U64 → List U64} (h1 : SchedQueuesInv st T Cs Ω H s1 Q R) (ht : t ∈ T)
    (hsub : ∀ b ∈ Sg, b ∈ Ω) (hb : Blocked (L.mem s1 (stA t))) (hS1 : EpSorted st T H s1) :
    notification.cancel_signal st s1 t (L.mem s1 (blockA t)) ⦃ s' => EpSorted st T H s' ⦄ := by
  have hT := h1.tcbs
  obtain ⟨E1, EQ1, hW1⟩ := h1.eps
  obtain ⟨he, hm⟩ := hW1.2.2.2.2.1 t ht (by simp) hb
  obtain ⟨hE, -, hq⟩ := hW1.1 _ he
  unfold notification.cancel_signal
  refine WP.spec_bind (WP.spec_and (notification.ntfn_dequeue.sorted hT hS1 hW1 he hm)
    (notification.ntfn_dequeue.foot s1 _ t _ hT hE hq hm)) ?_
  rintro s2 ⟨hS2, w2⟩
  have hN2 : NodePlaced st T s2 (L.cpu s2) := by rw [w2.2.1]; exact (h1.nodes _ h1.cur).ksb w2.1
  exact WP.spec_mono (sched.set_thread_state.sf (Sg := Sg) s2 t _ hT hN2 (by rw [w2.2.1]; exact h1.cur) ht)
    fun s3 w3 => EpSorted.sft (Sg := Sg) h1 hsub w2.1 hS2 w3

/-- **seL4 `cancelIPC` keeps the IPC queues sorted**, under
`cancel_ipc.inv`'s hypotheses. -/
theorem ipc.cancel_ipc.sorted {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (t : obj.Tcb)
    (Q : U64 → U64 → List U64) (R : U64 → List U64) (h : SchedQueuesInv st T Cs Ω H s Q R) (ht : t ∈ T)
    (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (hrecv : L.mem s (stA t) = sched.TS_BLOCKED_ON_RECV → L.mem s (replyA t) ≠ 0#u64 →
      L.mem s (replyA t) ∈ Rp ∧ L.mem s (rTcbA (L.mem s (replyA t))) = t)
    (hreply : L.mem s (stA t) = sched.TS_BLOCKED_ON_REPLY → ReplyT st Rp Scs s t)
    (hS : EpSorted st T H s) :
    ipc.cancel_ipc st ar s a t ⦃ s' _ => EpSorted st T H s' ⦄ := by
  have hT := h.tcbs
  unfold ipc.cancel_ipc
  have cf : faults.clear_fault st s t ⦃ s1 => SFt st T Cs Sg s s1 ⦄ := by
    unfold faults.clear_fault
    exact WP.spec_mono (obj.Tcb.set_fault_type.spec s t _) fun s1 e => by
      subst e; exact sfoot_field (K := 3376#u64) hT ht (by simp) (by simp) (by simp) (by simp)
  refine WP.spec_bind (WP.spec_and (faults.clear_fault.inv s t Q R h ht hO hsub) cf) ?_
  rintro s1 ⟨⟨h1, f1, o1, -, -⟩, w1⟩
  have hS1 : EpSorted st T H s1 := EpSorted.sft h hsub rfl hS w1
  have e1 : L.mem s1 (stA t) = L.mem s (stA t) := by
    rw [stA_eq]; exact f1 t ht _ (by simp) (by simp) (fun _ => by simp)
  have r1 : L.mem s1 (replyA t) = L.mem s (replyA t) := f1 t ht _ (by simp) (by simp) (fun _ => by simp)
  have g1 : ∀ b ∈ Sg, L.mem s1 b = L.mem s b := fun b hb => o1 b (hsub b hb)
  have hO1 : ObjsOK st Ω Sg Rp Scs Nt Z s1 := hO.ksb
  step with obj.Tcb.state.spec as ⟨stt, stt_post⟩
  split
  · rename_i hs
    have hb : Blocked (L.mem s1 (stA t)) := by rw [← stt_post, hs]; exact Or.inl rfl
    exact ep_branch.sorted a s1 t h1 ht hO1 hsub hb (stt = sched.TS_BLOCKED_ON_RECV)
      (fun hrc => by rw [hs] at hrc; obtain ⟨-, -, hr3, hs4, -⟩ := ts_vals; rw [hs4, hr3] at hrc; simp at hrc) hS1
  split
  · rename_i _ hs
    have hb : Blocked (L.mem s1 (stA t)) := by rw [← stt_post, hs]; exact Or.inr (Or.inl rfl)
    have hE := ep_branch.sorted a s1 t h1 ht hO1 hsub hb True
      (fun _ hi => by
        rw [r1] at hi ⊢
        exact (hrecv (by rw [← e1, ← stt_post, hs]) hi).1) hS1
    simp only [↓reduceIte] at hE
    exact hE
  split
  · rename_i _ _ hs
    have hb : Blocked (L.mem s1 (stA t)) := by rw [← stt_post, hs]; exact Or.inr (Or.inr rfl)
    step with obj.Tcb.block_obj.spec as ⟨i, i_post⟩
    subst i_post
    exact WP.spec_bind (notification.cancel_signal.sorted s1 t h1 ht hsub hb hS1) fun s2 h2 => (WP.spec_ok _).2 h2
  split
  · rename_i _ _ _ hs
    have hR : ReplyT st Rp Scs s1 t := (hreply (by rw [← e1, ← stt_post, hs])).transport hO r1 g1
    refine WP.spec_bind (ipc.reply_remove_tcb.sf s1 t hT (h1.nodes _ h1.cur) h1.cur hO1 hR ht) fun s2 w2 => ?_
    exact (WP.spec_ok _).2 (EpSorted.sft h1 hsub rfl hS1 w2)
  · exact (WP.spec_ok _).2 hS1

end

end Fl4Proofs.P1
