/-
P3 (p3J gen 31): **the endpoint receive's steps in `KWN`** (P1's `take_reply.kw`, `cancel_ipc.kw`,
`reply_remove_tcb.kw`, EntryXG's `wait_for_sender.kw` and `receive_from_sender.xg` mirrored at `Kp = ∅`,
`Nd = False`, as P2 FootN4 / FootN8 mirrored `send_block` / `cancel_ipc` of a receive-blocked thread and gen 28's
P3JRecvN `ntfn_block`). P2-level, namespace `Fl4Proofs.P1`, FL4 only.

* `footN0_sgw`: a write of a `Sg` word (an `Ω` word outside the nodes) at a state with the entry's key-space base and
  core is a `FootN ∅ False` step (`notIdW_out`, `actionW_out` from the placement at the entry).
* `ipc.reply_remove_tcb.kwN0` (every write a reply / SC reply-link word, then `reply_unlink`'s `Reply.set_tcb` and
  P2's `set_thread_state.kwNP`), **`ipc.cancel_ipc.kwN0`** (all four blocked states: the endpoint dequeue by P2's
  `EpFoot.kwN`, the notification dequeue likewise, the reply case by `reply_remove_tcb.kwN0`),
  **`endpoint.take_reply.kwN0`**.
* `ep_append_kwN0`, **`endpoint.wait_for_sender.footN0`** (the blocking receive: state / block / reply fields by
  P2's `blkfoot_footN`, the reply object's `TCB` word by `footN0_sgw`, the append; the polling one: `BADGE`).
* **`endpoint.receive_from_sender.footNB`**: the dequeue (`EpFoot.kwN`), the transfer from a `BufK` state (P3JFltX's
  `do_ipc_transfer.nbX`, P2's `XferWC.ipcN` at `U = ∅`), `unblock_sporadic.kwN`, `reply_push.kwN`,
  `set_thread_state.kwN`, `possible_switch_to.kwN`: an `IpcFootN ∅ False … ∅` footprint.

`AcK` is vacuous at `Kp = ∅`. No premise; no sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JRecvN
import Fl4Proofs.P3.P3JFltX
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P2.Stall

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}
variable {A : Type} {ar : machine.Arch A} {Ac : Set U64} {Es : Set U64}

/-- A `Sg` word written at a state with the entry's base and core: a `FootN ∅ False` step. -/
theorem footN0_sgw {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {s0 s : S}
    (h : SchedQueuesInvX st T Cs Ω H X s0 Q R) (hsub : ∀ b ∈ Sg, b ∈ Ω) (hk : L.ksb s = L.ksb s0)
    (hcp : L.cpu s = L.cpu s0) {a v : U64} (ha : Aligned a) (hm : a ∈ Sg) :
    FootN st ∅ False T Cs Sg Scs Z Es s (L.wr s a v) := by
  have NP : ∀ c ∈ Cs, NodePlaced st T s c := fun c hc => (h.nodes c hc).ksb hk
  have ho : OutsideObjs st T Cs s a := (h.omega a (hsub a hm)).ksb hk
  exact footN_wr ha ⟨kw_sg hm, notIdW_out NP ho (fun h => h.elim)⟩
    (actionW_out NP (by rw [hcp]; exact h.cur) ho)

set_option maxHeartbeats 4000000 in
/-- `reply_remove_tcb` in `KWN ∅ False` (P1 `reply_remove_tcb.kw`). -/
theorem ipc.reply_remove_tcb.kwN0 {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} (s : S)
    (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s)
    (hsub : ∀ b ∈ Sg, b ∈ Ω) (hR : ReplyT st Rp Scs s t) (ht : t ∈ T) :
    ipc.reply_remove_tcb st s t ⦃ s' => FootN st ∅ False T Cs Sg Scs Z Es s s' ⦄ := by
  have hT := h.tcbs
  obtain ⟨hi, -, hn, hp⟩ := hR
  unfold ipc.reply_remove_tcb
  step with obj.Tcb.reply_obj.spec as ⟨i, ei⟩
  step with obj.Reply.next.spec as ⟨next, enext⟩
  step with obj.Reply.prev.spec as ⟨prev, eprev⟩
  rw [← ei] at hi hn hp
  rw [← enext] at hn
  rw [← eprev] at hp
  refine WP.spec_bind (Pₘ := fun s1 => FootN st ∅ False T Cs Sg Scs Z Es s s1) ?_ ?_
  · split
    · rename_i hne
      have hn0 : next ≠ 0#u64 := by simpa using hne
      step with obj.Reply.next_is_head.spec as ⟨b, eb⟩
      split
      · rename_i hb
        have hS := (hn hn0).1 (by rw [← eb]; exact hb)
        exact WP.spec_mono (obj.Sc.set_reply.spec s next 0#u64) fun s1 e1 => by
          subst e1; exact footN0_sgw h hsub rfl rfl (screp_aligned hO hS) (hO.repW _ hS)
      · rename_i hb
        have hRp := (hn hn0).2 (by rw [← eb]; simpa using hb)
        exact WP.spec_mono (obj.Reply.set_prev.spec s next 0#u64) fun s1 hs1 => by
          obtain ⟨w, e1, -⟩ := hs1; subst e1
          exact footN0_sgw h hsub rfl rfl (rp_aligned hO hRp).2.1 (hO.prevW hRp)
    · exact (WP.spec_ok _).2 (FootN.refl _)
  intro s1 f1
  refine WP.spec_bind (Pₘ := fun s2 => FootN st ∅ False T Cs Sg Scs Z Es s s2) ?_ ?_
  · split
    · rename_i hne
      have hRp := hp (by simpa using hne)
      exact WP.spec_mono (obj.Reply.set_next.spec s1 prev 0#u64) fun s2 hs2 => by
        obtain ⟨w, e2, -⟩ := hs2; subst e2
        exact f1.trans (footN0_sgw h hsub f1.1 f1.2.1 (rp_aligned hO hRp).2.2 (hO.nextW hRp))
    · exact (WP.spec_ok _).2 f1
  intro s2 f2
  refine WP.spec_bind (obj.Reply.set_prev.spec s2 i 0#u64) fun s3 hs3 => ?_
  obtain ⟨w3, e3, -⟩ := hs3
  subst e3
  have f3 := f2.trans (footN0_sgw (v := w3) h hsub f2.1 f2.2.1 (rp_aligned hO hi).2.1 (hO.prevW hi))
  refine WP.spec_bind (obj.Reply.set_next.spec _ i 0#u64) fun s4 hs4 => ?_
  obtain ⟨w4, e4, -⟩ := hs4
  subst e4
  have f4 := f3.trans (footN0_sgw (v := w4) h hsub f3.1 f3.2.1 (rp_aligned hO hi).2.2 (hO.nextW hi))
  unfold ipc.reply_unlink
  refine WP.spec_bind (obj.Reply.set_tcb.spec _ i 0#u64) fun s5 e5 => ?_
  subst e5
  have f5 := f4.trans (footN0_sgw (v := 0#u64) h hsub f4.1 f4.2.1 (rp_aligned hO hi).1 (hO.tcbW hi))
  exact WP.spec_mono (sched.set_thread_state.kwNP (Sg := Sg) (Kp := ∅) (Nd := False) (Scs := Scs) (Z := Z) (Es := Es)
    _ t _ hT (fun c hc => (h.nodes c hc).ksb f5.1) (by rw [f5.2.1]; exact h.cur) ht (Set.notMem_empty t))
    fun s6 f6 => f5.trans f6

set_option maxHeartbeats 4000000 in
/-- **`cancel_ipc` in `KWN ∅ False`** (P1 `cancel_ipc.kw`; module docstring). -/
theorem ipc.cancel_ipc.kwN0 (s : S) (a : A) (t : obj.Tcb)
    {Q : U64 → U64 → List U64} {R : U64 → List U64} (h : SchedQueuesInv st T Cs Ω H s Q R) (ht : t ∈ T)
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (hreply : L.mem s (stA t) = sched.TS_BLOCKED_ON_REPLY → ReplyT st Rp Scs s t)
    (hrecv : L.mem s (stA t) = sched.TS_BLOCKED_ON_RECV → L.mem s (replyA t) ≠ 0#u64 → L.mem s (replyA t) ∈ Rp) :
    ipc.cancel_ipc st ar s a t ⦃ s' _ => FootN st ∅ False T Cs Sg Scs Z (EH H) s s' ⦄ := by
  have hT := h.tcbs
  have hO := hX.1
  unfold ipc.cancel_ipc
  refine WP.spec_bind (WP.spec_and (faults.clear_fault.inv s t Q R h ht hO hsub)
    (WP.spec_mono (obj.Tcb.set_fault_type.spec s t _) fun s' e => e)) ?_
  rintro s1 ⟨⟨h1, f1, o1, -, -⟩, e1⟩
  have F1 : FootN st ∅ False T Cs Sg Scs Z (EH H) s s1 := by
    rw [e1]; exact footN_field (K := 3376#u64) hT h.nodes h.cur ht (by simp) (by simp) (by simp) (by simp)
  have st1 : L.mem s1 (stA t) = L.mem s (stA t) := by
    rw [stA_eq]; exact f1 t ht _ (by simp) (by simp) (fun _ => by simp)
  have rp1 : L.mem s1 (replyA t) = L.mem s (replyA t) := f1 t ht _ (by simp) (by simp) (fun _ => by simp)
  -- the endpoint branch, from `s1`
  have epb : Blocked (L.mem s1 (stA t)) → ∀ rcv : Prop, ∀ _ : Decidable rcv,
      (rcv → L.mem s1 (stA t) = sched.TS_BLOCKED_ON_RECV) →
      (do
        let ep ← obj.Tcb.block_obj st t s1
        let s2 ← endpoint.ep_dequeue st s1 ep t
        let s3 ← if rcv then do
            let i ← obj.Tcb.reply_obj st t s2
            if (i != 0#u64) = true then ipc.reply_unlink st s2 i t else ok s2
          else ok s2
        let s4 ← sched.set_thread_state st s3 t sched.TS_INACTIVE
        ok (s4, a)) ⦃ s' _ => FootN st ∅ False T Cs Sg Scs Z (EH H) s s' ⦄ := by
    intro hb rcv _ hrcv1
    step with obj.Tcb.block_obj.spec as ⟨ep, ep_post⟩
    subst ep_post
    obtain ⟨E, EQ, hEW⟩ := h1.eps
    obtain ⟨he, hmem⟩ := hEW.2.2.2.2.1 t ht (by simp) hb
    obtain ⟨hE, hEN, hq⟩ := hEW.1 _ he
    have hH : L.mem s1 (blockA t) ∈ EH H := (hEW.2.2.2.2.2.2.2.1 _).1 he
    refine WP.spec_bind (WP.spec_and (endpoint.ep_dequeue.inv s1 t Q R h1 ht (by simp) hb)
      (endpoint.ep_dequeue.foot s1 _ t _ hT hE hq hmem)) ?_
    rintro s2 ⟨⟨h2, f2, -⟩, w2⟩
    have F2 : FootN st ∅ False T Cs Sg Scs Z (EH H) s1 s2 :=
      FootN.of' w2 (fun b _ hb => EpFoot.kwN hT h1.nodes hq.mem hH hE hEN (hEW.2.2.1 _ he) (hdrΩ_of hX hsub) hb)
        acK_empty
    refine WP.spec_bind (Pₘ := fun s3 => FootN st ∅ False T Cs Sg Scs Z (EH H) s s3) ?_ ?_
    · split
      · step with obj.Tcb.reply_obj.spec as ⟨i, ei⟩
        split
        · rename_i hrc hi
          have hi0 : i ≠ 0#u64 := by simpa using hi
          have rp2 : L.mem s2 (replyA t) = L.mem s (replyA t) :=
            (f2 t ht _ (by simp) (by simp) (by simp) (by simp)).trans rp1
          have hiR : i ∈ Rp := by
            rw [ei, rp2]; exact hrecv (by rw [← st1]; exact hrcv1 hrc) (by rw [← rp2, ← ei]; exact hi0)
          exact WP.spec_mono (ipc.reply_unlink.kwNO (Sg := Sg) (Kp := ∅) (Nd := False) (Scs := Scs) (Z := Z)
            (Es := EH H) s2 i t h2 hO.ksb hsub hiR ht (Set.notMem_empty t)) fun s3 f3 => F1.trans (F2.trans f3)
        · exact (WP.spec_ok _).2 (F1.trans F2)
      · exact (WP.spec_ok _).2 (F1.trans F2)
    intro s3 f3
    refine WP.spec_bind (sched.set_thread_state.kwNP (Sg := Sg) (Kp := ∅) (Nd := False) (Scs := Scs) (Z := Z)
      (Es := EH H) s3 t _ hT (fun c hc => (h.nodes c hc).ksb f3.1) (by rw [f3.2.1]; exact h.cur) ht
      (Set.notMem_empty t)) fun s4 f4 => ?_
    exact (WP.spec_ok _).2 (f3.trans f4)
  obtain ⟨-, -, r3, r4, r6⟩ := ts_vals
  step with obj.Tcb.state.spec as ⟨v, ev⟩
  split
  · rename_i hsd
    exact epb (by rw [← ev, hsd]; exact Or.inl rfl) _ _ (fun e => by rw [← ev]; exact e)
  split
  · rename_i _ hrv
    have := epb (by rw [← ev, hrv]; exact Or.inr (Or.inl rfl)) True instDecidableTrue
      (fun _ => by rw [← ev]; exact hrv)
    simp only [ite_true] at this
    exact this
  split
  · rename_i _ _ hnt
    have hb : Blocked (L.mem s1 (stA t)) := by rw [← ev, hnt]; exact Or.inr (Or.inr rfl)
    step with obj.Tcb.block_obj.spec as ⟨n, en⟩
    subst en
    refine WP.spec_bind (Pₘ := fun s3 => FootN st ∅ False T Cs Sg Scs Z (EH H) s s3) ?_
      (fun s3 f3 => (WP.spec_ok _).2 f3)
    unfold notification.cancel_signal
    obtain ⟨E, EQ, hEW⟩ := h1.eps
    obtain ⟨he, hmem⟩ := hEW.2.2.2.2.1 t ht (by simp) hb
    obtain ⟨hE, hEN, hq⟩ := hEW.1 _ he
    have hH : L.mem s1 (blockA t) ∈ EH H := (hEW.2.2.2.2.2.2.2.1 _).1 he
    refine WP.spec_bind (notification.ntfn_dequeue.foot s1 _ t _ hT hE hq hmem) fun s2 w2 => ?_
    have F2 : FootN st ∅ False T Cs Sg Scs Z (EH H) s1 s2 :=
      FootN.of' w2 (fun b _ hb => EpFoot.kwN hT h1.nodes hq.mem hH hE hEN (hEW.2.2.1 _ he) (hdrΩ_of hX hsub) hb)
        acK_empty
    exact WP.spec_mono (sched.set_thread_state.kwNP (Sg := Sg) (Kp := ∅) (Nd := False) (Scs := Scs) (Z := Z)
      (Es := EH H) s2 t _ hT (fun c hc => (h1.nodes c hc).ksb F2.1) (by rw [F2.2.1]; exact h1.cur) ht
      (Set.notMem_empty t)) fun s3 f3 => F1.trans (F2.trans f3)
  split
  · rename_i _ _ _ hrp
    have hR1 : ReplyT st Rp Scs s1 t :=
      (hreply (by rw [← st1, ← ev, hrp])).transport hO rp1 (fun b hb => o1 b (hsub b hb))
    refine WP.spec_bind (ipc.reply_remove_tcb.kwN0 (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s1 t h1 hO.ksb hsub
      hR1 ht) fun s2 f2 => ?_
    exact (WP.spec_ok _).2 (F1.trans f2)
  · exact (WP.spec_ok _).2 F1

set_option maxHeartbeats 4000000 in
/-- **`take_reply` in `KWN ∅ False`** (P1 `take_reply.kw`). -/
theorem endpoint.take_reply.kwN0 (s : S) (a : A) (t : U64) (cap : capability.Cap)
    {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hSg : SgOK st Ω Sg s)
    (hcap : ∀ p g, cap = .Reply p g → p ∈ Rp) :
    endpoint.take_reply st ar s a t cap ⦃ r => FootN st ∅ False T Cs Sg Scs Z (EH H) s r.2.1 ⦄ := by
  unfold endpoint.take_reply
  split
  case h_5 p g =>
    have hp := hcap p g rfl
    step with obj.Reply.tcb.blk as ⟨i, ei⟩
    step with obj.Tcb.is_null.spec as ⟨b, eb⟩
    split
    · exact (WP.spec_ok _).2 (FootN.refl s)
    rename_i hb
    have hi0 : i ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    step with tcb_ne.blk as ⟨b1, eb1⟩
    split
    · obtain ⟨-, hiT, -, -⟩ := hX.2.1.back p hp (by rw [← ei]; exact hi0)
      rw [← ei] at hiT
      refine WP.spec_bind (ipc.cancel_ipc.kwN0 s a i h hiT hX hSg.sub (fun hs => by
          obtain ⟨h1, h2⟩ := hX.2.1.reply i hiT hs
          exact ⟨h1, h2, hX.2.1.next _ h1, hX.2.1.prev _ h1⟩) (fun hs h0' => (hX.2.1.recv i hiT hs h0').1)) ?_
      rintro ⟨s1, a1⟩ f1
      exact (WP.spec_ok _).2 (by simpa using f1)
    · exact (WP.spec_ok _).2 (FootN.refl s)
  all_goals exact (WP.spec_ok _).2 (FootN.refl s)

/-- `ep_append` of a thread being blocked in `KWN ∅ False` (P1 `ep_append_kw`). -/
theorem ep_append_kwN0 {s : S} {e t state : U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H {y | y ∈ (∅ : Set U64) ∨ y = t} s Q R) (ht : t ∈ T) (hH : H e = some .ep)
    (hHΩ : HdrΩ False Ω Scs) :
    endpoint.ep_append st s e t state ⦃ s' => FootN st ∅ False T Cs Sg Scs Z (EH H) s s' ⦄ := by
  obtain ⟨E5, EQ5, hEW5⟩ := h.eps
  have he5 : e ∈ E5 := (hEW5.2.2.2.2.2.2.2.1 e).2 (Or.inl hH)
  obtain ⟨hE5, hEN5, hq5⟩ := hEW5.1 e he5
  have htn : t ∉ EQ5 e := fun hm => (hEW5.2.2.2.1 e he5 t hm).1 (Or.inr rfl)
  have hW : ∀ w ∈ t :: EQ5 e, w ∈ T := by
    intro w hw
    rcases List.mem_cons.1 hw with rfl | hw
    · exact ht
    · exact hq5.mem w hw
  refine WP.spec_mono (endpoint.ep_append.foot s e t state (EQ5 e) h.tcbs hE5 hq5 ht htn) fun s' w => ?_
  exact FootN.of' w (fun b _ hb => EpFoot.kwN (Sg := Sg) (Kp := ∅) (Nd := False) (Scs := Scs) (Z := Z)
    (Es := EH H) h.tcbs h.nodes hW (Or.inl hH) hE5 hEN5 (hEW5.2.2.1 e he5) hHΩ hb) acK_empty

set_option maxHeartbeats 4000000 in
/-- **`wait_for_sender` in `KWN ∅ False`** (EntryXG's `wait_for_sender.kw`; module docstring). -/
theorem endpoint.wait_for_sender.footN0 (s : S) (t e : U64) (blocking : Bool) (reply : U64)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hSg : SgOK st Ω Sg s)
    (ht : t ∈ T) (hc : blocking = true → CanBlock st T Ac s t) (hH : H e = some .ep)
    (hr : reply ≠ 0#u64 → reply ∈ Rp) :
    endpoint.wait_for_sender st s t e blocking reply ⦃ s' => FootN st ∅ False T Cs Sg Scs Z (EH H) s s' ⦄ := by
  have hta := h.tcbs t ht
  have hN := h.nodes _ h.cur
  have hrs : reply ≠ 0#u64 → rTcbA reply ∈ Sg := fun h0 => hX.1.tcbW (hr h0)
  have hHΩ : HdrΩ False Ω Scs := hdrΩ_of hX hSg.sub
  unfold endpoint.wait_for_sender
  split
  · have hc := hc ‹_›
    step with obj.Tcb.set_state.spec as ⟨s1, e1⟩
    step with obj.Tcb.set_block_obj.wr as ⟨s2, e2⟩
    step with obj.Tcb.set_reply_obj.wr as ⟨s3, e3⟩
    have h1 : SchedQueuesInvX st T Cs Ω H {y | y ∈ (∅ : Set U64) ∨ y = t} s1 Q R := by
      rw [e1]; exact blk_set_state h hc
    have h2 : SchedQueuesInvX st T Cs Ω H {y | y ∈ (∅ : Set U64) ∨ y = t} s2 Q R := by
      rw [e2]; exact inv_wr_fieldX (K := 3336#u64) h1 ht (Or.inr rfl) (by simp) (by simp) (by simp)
    have h3 : SchedQueuesInvX st T Cs Ω H {y | y ∈ (∅ : Set U64) ∨ y = t} s3 Q R := by
      rw [e3]; exact inv_wr_fieldX (K := 3360#u64) h2 ht (Or.inr rfl) (by simp) (by simp) (by simp)
    rw [stA_eq] at e1
    have w3 : WritesIn st s s3 (BlkFoot st s t 0#u64) := by
      rw [e3, e2, e1]
      exact blk_wr_field (K := 3360#u64) hta (blk_wr_field hta (blk_wr_field hta (WritesIn.refl _ _) (by simp))
        (by simp)) (by simp)
    have v3 : L.mem s3 (stA t) = sched.TS_BLOCKED_ON_RECV := by
      rw [e3, fld_wr_ne' (K := 3360#u64) (a := replyA t) hta rfl (stA_eq t) (by simp) (by simp) (by simp) (by simp)
        (by simp), e2, fld_wr_ne' hta (blockA_eq t) (stA_eq t) (by simp) (by simp) (by simp) (by simp) (by simp),
        e1, stA_eq]
      exact L.mem_wr_same (field_aligned hta (by simp) (by simp))
    have a3 : L.actionW s3 = L.actionW s := by
      rw [e3, act_wr_field (K := 3360#u64) (a := replyA t) (h2.nodes _ h2.cur) ht hta rfl (by simp) (by simp),
        e2, act_wr_field (h1.nodes _ h1.cur) ht hta (blockA_eq t) (by simp) (by simp),
        e1, act_wr_field hN ht hta rfl (by simp) (by simp)]
    refine WP.spec_bind (sched.schedule_tcb.blk s3 t h3 (by rw [v3]; exact blocked_not_runnable (Or.inr (Or.inl rfl))))
      ?_
    rintro s4 ⟨h4, e4, -⟩
    obtain ⟨w4, -, -, -, -, -⟩ := blk_sched h3 ht w3 a3 e4
    have F4 : FootN st ∅ False T Cs Sg Scs Z (EH H) s s4 := blkfoot_footN h ht (Set.notMem_empty _) w4 acK_empty
    split
    · rename_i hne
      have h0 : reply ≠ 0#u64 := by simpa using hne
      have hm : rTcbA reply ∈ Ω := hSg.sub _ (hrs h0)
      step with obj.Reply.set_tcb.spec as ⟨s6, e6⟩
      try simp only [Aeneas.Std.bind_ok]
      obtain ⟨h6, -, -⟩ := omega_wr (v := t) h4 hm
      rw [← e6] at h6
      have F6 : FootN st ∅ False T Cs Sg Scs Z (EH H) s s6 := by
        rw [e6]; exact F4.trans (footN0_sgw h4 hSg.sub rfl rfl (h4.omega _ hm).1 (hrs h0))
      exact WP.spec_mono (ep_append_kwN0 (Sg := Sg) (Scs := Scs) (Z := Z) h6 ht hH hHΩ) fun s' f => F6.trans f
    · try simp only [Aeneas.Std.bind_ok]
      exact WP.spec_mono (ep_append_kwN0 (Sg := Sg) (Scs := Scs) (Z := Z) h4 ht hH hHΩ) fun s' f => F4.trans f
  · refine WP.spec_mono (obj.Tcb.set_reg.badge s t 0#u64 hta) fun s' e' => ?_
    subst e'
    exact footN_field (K := 256#u64) h.tcbs h.nodes h.cur ht (by simp) (by simp) (by simp) (by simp)


set_option maxHeartbeats 8000000 in
/-- **`receive_from_sender` from a `BufK` state writes only `IpcWN … ∅` words** (module docstring). -/
theorem endpoint.receive_from_sender.footNB (hA : P0.ArchTotal ar) {sE : S}
    (hN : NoBufCap (L := L) T sE) (hP : BufApart (L := L) T Cs Sg Scs Z (EH H) sE) (s : S) (a : A)
    (thread e reply : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (hc : CanBlock st T Ac s thread)
    (hH : H e = some .ep) (hst : L.epState s e ≠ 0#u64 ∧ L.epState s e ≠ 2#u64)
    (hr : reply ≠ 0#u64 → reply ∈ Rp ∧ (L.mem s (rTcbA reply) = 0#u64 ∨ L.mem s (rTcbA reply) = thread))
    (hK0 : BufK (L := L) T sE s) :
    endpoint.receive_from_sender st ar s a thread e reply ⦃ s' _ =>
      IpcFootN st ∅ False T Cs Ω Sg Scs Z (EH H) ∅ s s' ⦄ := by
  have hT := h.tcbs
  have ht := hc.mem
  have hst1 : L.epState s e = 1#u64 := by
    rcases ep_state3 h hH with e0 | e0 | e0
    · exact absurd e0 hst.1
    · exact e0
    · exact absurd e0 hst.2
  obtain ⟨hdT, hbe, hds, -⟩ := ep_head h hH (Or.inl rfl) hst1
  have hds := hds rfl
  set hd := (L.epQ s e).head with hhd
  have hdt : hd ≠ thread := fun e' => hc.nb (by rw [← e', hds]; exact Or.inl rfl)
  have hdi : L.idleW s ≠ hd := fun e' => hB.idleNB (by rw [e', hds]; exact Or.inl (Or.inl rfl))
  have hr' : reply ≠ 0#u64 → reply ∈ Rp ∧ L.mem s (rTcbA reply) = 0#u64 := fun h0 => by
    obtain ⟨h1, h2⟩ := hr h0
    refine ⟨h1, h2.resolve_right fun e' => hX.noref (hT _ ht) hc.nrp (fun e2 => hc.nb (Or.inr (Or.inl e2))) _ h1 e'⟩
  unfold endpoint.receive_from_sender
  step with endpoint.get_queue.spec as ⟨q, eq⟩
  subst eq
  have hdq := endpoint.ep_dequeue.inv s hd Q R h hdT (by simp) (Or.inl hds)
  rw [hbe] at hdq
  obtain ⟨E0, EQ0, hEW0⟩ := h.eps
  have heE0 : e ∈ E0 := (hEW0.2.2.2.2.2.2.2.1 e).2 (Or.inl hH)
  obtain ⟨hE0, hEN0, hq0⟩ := hEW0.1 e heE0
  have hdm : hd ∈ EQ0 e := by
    have := hEW0.2.2.2.2.1 hd hdT (by simp) (Or.inl hds); rw [hbe] at this; exact this.2
  refine WP.spec_bind (WP.spec_and hdq (endpoint.ep_dequeue.foot s e hd (EQ0 e) hT hE0 hq0 hdm)) ?_
  rintro s1 ⟨⟨h1, f1, o1, n1, k1, c1, nc1⟩, w1⟩
  have F1 : FootN st ∅ False T Cs Sg Scs Z (EH H) s s1 :=
    FootN.of' w1 (fun b _ hb => EpFoot.kwN hT h.nodes hq0.mem (Or.inl hH) hE0 hEN0 (hEW0.2.2.1 e heE0)
      (hdrΩ_of hX hSg.sub) hb) acK_empty
  obtain ⟨hB1, hX1, hS1, hSg1, ea1, ec1, ei1⟩ := frame_bx h hB hX hS hSg f1 o1 n1 k1
    (TmFr.mk0 ⟨k1, fun y hy K a b c => f1 y hy K (by omega) c (by omega) (by omega),
      fun c hc o ho => nc1 c hc o (by omega) (by omega), fun n' hn' => o1 _ (hSg.sub _ (hX.1.ntB n' hn').2)⟩)
  have hU1 : UserOK st T Cs Ω H ∅ s1 := fun b hb => absurd hb (Set.notMem_empty b)
  step with obj.Tcb.block_badge.any as ⟨badge, _⟩
  step with obj.Tcb.block_flags.any as ⟨flags, _⟩
  simp only [lift, Aeneas.Std.bind_ok]
  refine WP.spec_bind (ipc.do_ipc_transfer.nbX hA hN hP hdT ht ⟨h1, hB1, hX1, hS1, hSg1, hU1⟩
    (bufK_kw hP hK0 F1.foot)) ?_
  rintro s2 hx2
  obtain ⟨⟨h2, hB2, hX2, hS2, hSg2, -⟩, ⟨ea2, ec2, ei2, ecs2, f2, o2, -⟩, w2, -⟩ := hx2
  have F2 : IpcFootN st ∅ False T Cs Ω Sg Scs Z (EH H) ∅ s1 s2 := XferWC.ipcN h1 hX1 hU1 hSg.sub w2
  refine WP.spec_bind (WP.spec_and (endpoint.unblock_sporadic.all s2 hd h2 hB2 hX2 hS2 hSg2 hdT)
    (endpoint.unblock_sporadic.kwN (Kp := ∅) (Nd := False) (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H)
      s2 hd h2 hX2 hS2 hdT)) ?_
  rintro s3 ⟨⟨h3, hB3, hX3, hS3, hSg3, ea3, ec3, ei3, f3, r3⟩, F3⟩
  have G3 : IpcFootN st ∅ False T Cs Ω Sg Scs Z (EH H) ∅ s s3 := (FootN.ipc F1).trans (F2.trans (FootN.ipc F3))
  step with obj.Tcb.fault_type.any as ⟨ftype, _⟩
  have F : ∀ y ∈ T, ∀ K : U64, 3328 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 →
      L.mem s3 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y hy K h0 hK hK8 h1 h2' => (f3 y hy K hK hK8).trans ((f2 y hy K h0 hK hK8).trans (f1 y hy K hK hK8 h1 h2'))
  have st3 : ∀ y ∈ T, L.mem s3 (stA y) = L.mem s (stA y) := fun y hy => by
    rw [stA_eq]; exact F y hy _ (by simp) (by simp) (by simp) (by simp) (by simp)
  have ei : L.idleW s3 = L.idleW s := ei3.trans (ei2.trans ei1)
  have hds3 : L.mem s3 (stA hd) = sched.TS_BLOCKED_ON_SEND := (st3 hd hdT).trans hds
  obtain ⟨dq, dr, da⟩ := blocked_out h3 hdT (by rw [hds3]; exact blocked_not_runnable (Or.inl rfl))
  have hXc : ExcT {y | y ∈ (∅ : Set U64) ∨ y = hd} hd := fun y hy => by simpa using hy
  have hx3 : hd ∈ {y | y ∈ (∅ : Set U64) ∨ y = hd} := Or.inr rfl
  have rt3 : ∀ r ∈ Rp, L.mem s3 (rTcbA r) = L.mem s (rTcbA r) := fun r hr0 =>
    (r3 r hr0).trans ((o2 r hr0).trans (o1 _ (hSg.sub _ (hX.1.tcbW hr0))))
  have sc3 : L.mem s3 (scA hd) = L.mem s (scA hd) := by
    rw [scA_eq]; exact F hd hdT _ (by simp) (by simp) (by simp) (by simp) (by simp)
  have hdA : L.mem s3 (scA hd) ≠ 0#u64 → L.mem s3 (scA hd) ∈ Ac := fun h0 => by
    rw [sc3] at h0 ⊢
    exact hB.sact hd hdT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [hds]; exact Or.inl rfl)))))))
      h0
  have E1 : ∀ cd : Bool, reply ≠ 0#u64 → ipc.reply_push st ar s3 a hd thread reply cd ⦃ s' _ =>
      IpcFootN st ∅ False T Cs Ω Sg Scs Z (EH H) ∅ s s' ⦄ := fun cd h0 =>
    WP.spec_mono (ipc.reply_push.kwN (Sg := Sg) (Kp := ∅) (Nd := False) (Scs := Scs) (Z := Z) (Es := EH H) hA s3 a
      hd thread reply cd h3 hXc (Or.inl hx3) hB3 hX3 hS3 hSg3 hdT dq dr da
      (by rw [ei]; exact hdi) (by rw [hds3]; exact send_ne) (hr' h0).1 h0 (by rw [rt3 _ (hr' h0).1]; exact (hr' h0).2)
      ht hdA (Set.notMem_empty _) (fun _ h => h) actOut_empty)
      fun r hh => by obtain ⟨s', a'⟩ := r; simp only [WP.uncurry'_pair] at hh ⊢; exact G3.trans (FootDN.ipc hh)
  have E1' : reply ≠ 0#u64 → (do
      let i3 ← obj.Tcb.sc st hd s3
      let can_donate ← if (i3 != 0#u64) = true then ok (ftype != fl4_abi.consts.fault.Timeout) else ok false
      ipc.reply_push st ar s3 a hd thread reply can_donate) ⦃ s' _ =>
        IpcFootN st ∅ False T Cs Ω Sg Scs Z (EH H) ∅ s s' ⦄ := by
    intro h0
    step with obj.Tcb.sc.spec as ⟨i3, _⟩
    split <;> (try simp only [Aeneas.Std.bind_ok]) <;> exact E1 _ h0
  have E2 : (do
      let s4 ← sched.set_thread_state st s3 hd sched.TS_INACTIVE
      ok (s4, a)) ⦃ s' _ => IpcFootN st ∅ False T Cs Ω Sg Scs Z (EH H) ∅ s s' ⦄ := by
    refine WP.spec_bind (sched.set_thread_state.kwN (Sg := Sg) (Kp := ∅) (Nd := False) (Scs := Scs) (Z := Z)
      (Es := EH H) s3 hd _ h3 hdT (Set.notMem_empty _)) fun s4 f4 => ?_
    exact (WP.spec_ok _).2 (G3.trans (FootN.ipc f4))
  have E3 : (do
      let s4 ← sched.set_thread_state st s3 hd sched.TS_RUNNING
      let s5 ← sched.possible_switch_to st s4 hd
      ok (s5, a)) ⦃ s' _ => IpcFootN st ∅ False T Cs Ω Sg Scs Z (EH H) ∅ s s' ⦄ := by
    refine WP.spec_bind (WP.spec_and (sts_all s3 hd _ Q R h3 hB3 hX3 hS3 hSg3 hdT not_blocked_running running_ne
      (Or.inl hx3) (hX3.noref (h3.tcbs _ hdT) (by rw [hds3]; exact send_ne.1) (by rw [hds3]; exact send_ne.2))
      ⟨fun _ _ _ _ _ => runnable_running, fun _ _ _ => runnable_running,
        fun _ => runnable_running⟩)
      (sched.set_thread_state.kwN (Sg := Sg) (Kp := ∅) (Nd := False) (Scs := Scs) (Z := Z) (Es := EH H)
        s3 hd _ h3 hdT (Set.notMem_empty _))) fun s4 hh => ?_
    obtain ⟨⟨h4, -⟩, f4⟩ := hh
    have h4' := h4.congrX empty_congr'
    refine WP.spec_bind (sched.possible_switch_to.kwN (Sg := Sg) (Kp := ∅) (Nd := False) (Scs := Scs) (Z := Z)
      (Es := EH H) s4 hd h4' hdT (Set.notMem_empty _) actOut_empty) fun s5 f5 => ?_
    exact (WP.spec_ok _).2 ((G3.trans (FootN.ipc f4)).trans (FootN.ipc f5))
  repeat' split
  all_goals first
    | exact E2
    | exact E3
    | (rename_i hh; exact E1' (by simpa using hh))

end

end Fl4Proofs.P1
