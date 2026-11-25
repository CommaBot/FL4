/-
P2 (tmofr, part A): **the timeout fault's message transfer and its step
footprints without the `IPC_BUFFER` word**.

* The timeout-fault transfer (`ipc.do_ipc_transfer.tmo`), walked, not taken as
  a premise: when the sender's `FAULT_TYPE` word holds `Timeout`,
  `do_ipc_transfer` takes the fault branch and `set_mrs_fault` its `Timeout`
  branch, which writes only message *registers* (`MR0`, `MR1` < 4 =
  `N_MSG_REGISTERS`), the receiver's `MSG_INFO` and `BADGE` registers, and the
  sender's SC `CONSUMED` word (`TmoXW`). No cap is transferred (no cap-slot
  clause, unlike `XferWC`) and no IPC-buffer word is written, so the walk
  runs over P1's `XSFC` with no user words (`U = ∅`) and needs neither
  `XferOKRS` [J] nor `XferFootOKC` [J] nor any buffer fact.
* `KWB` (`KW` without the `IPC_BUFFER` word 3512) step footprints the timeout
  fault's `send_ipc` needs and P1 did not have: `set_fault.kwB`,
  `set_fault.ftmo` (a `Timeout` fault's `FAULT_TYPE` word), `set_blocked_on_reply.kwB`,
  `reply_push.kwB0` (no donation), `send_tail.footB`, `blkfoot_footB`,
  `send_block.footB`, `send_ipc.blockFootB`.

No premise.
-/
import Fl4Proofs.P2.FootN5
import Fl4Proofs.P1.QueueFootS
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {Es : Set U64}
variable {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}

/-! ## `KWB` step footprints -/

/-- `set_fault` writes only `t`'s fault and lookup-failure words (`KWB`). -/
theorem faults.set_fault.kwB (s : S) (t : obj.Tcb) (f : error.Fault) (hT : TcbPlaced T) (ht : t ∈ T) :
    faults.set_fault st s t f ⦃ s' => FootB st T Cs Sg Scs Z Es s s' ⦄ := by
  have W : ∀ {s₁ : S} (K v : U64), FootB st T Cs Sg Scs Z Es s s₁ → 3376 ≤ K.val → K.val < 3432 →
      K.val % 8 = 0 → FootB st T Cs Sg Scs Z Es s (L.wr s₁ (core.num.U64.wrapping_add t K) v) :=
    fun K v e h1 h2 h3 => e.trans (footB_field hT ht (by omega) (by omega) h3 ⟨by omega, by omega, by omega⟩)
  unfold faults.set_fault
  refine WP.spec_bind (Pₘ := fun r : S × U64 × U64 × U64 × U64 => FootB st T Cs Sg Scs Z Es s r.1) ?_ ?_
  · split
    all_goals first | exact (WP.spec_ok _).2 (FootB.refl s) | skip
    · refine WP.spec_bind (P0.error.LookupFault.encode.p0 _) ?_
      rintro ⟨lt, l0, l1⟩ -
      try simp only [uncurry_apply_pair]
      refine WP.spec_bind (obj.Tcb.set_lf_type.wr s t lt) fun s2 e2 => ?_
      subst e2
      have h2 := W (s₁ := s) 3408#u64 lt (FootB.refl s) (by simp) (by simp) (by simp)
      refine WP.spec_bind (obj.Tcb.set_lf_w0.wr _ t l0) fun s3 e3 => ?_
      subst e3
      have h3 := W 3416#u64 l0 h2 (by simp) (by simp) (by simp)
      refine WP.spec_bind (obj.Tcb.set_lf_w1.wr _ t l1) fun s4 e4 => ?_
      subst e4
      have h4 := W 3424#u64 l1 h3 (by simp) (by simp) (by simp)
      refine WP.spec_bind (Pₘ := fun _ : U64 => True) ?_ fun i _ => (WP.spec_ok _).2 h4
      split <;> exact (WP.spec_ok _).2 trivial
    · refine WP.spec_bind (Pₘ := fun _ : U64 => True) ?_ fun i _ =>
        (WP.spec_ok _).2 (FootB.refl s)
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

/-- A `Timeout` fault leaves `Timeout` in the thread's `FAULT_TYPE` word. -/
theorem faults.set_fault.ftmo (s : S) (t : obj.Tcb) (b : U64) (hta : TcbAddr t) :
    faults.set_fault st s t (error.Fault.Timeout b) ⦃ s' =>
      L.mem s' (faultA t) = fl4_abi.consts.fault.Timeout ⦄ := by
  unfold faults.set_fault
  simp only [bind_ok]
  refine WP.spec_bind (obj.Tcb.set_fault_type.spec s t _) fun s2 e2 => ?_
  subst e2
  refine WP.spec_bind (obj.Tcb.set_fault_w0.wr _ t b) fun s3 e3 => ?_
  subst e3
  refine WP.spec_bind (obj.Tcb.set_fault_w1.wr _ t _) fun s4 e4 => ?_
  subst e4
  refine WP.spec_mono (obj.Tcb.set_fault_w2.wr _ t _) fun s5 e5 => ?_
  subst e5
  unfold faultA
  rw [fld_wr_ne' hta rfl rfl (by simp) (by simp) (by simp) (by simp) (by simp),
    fld_wr_ne' hta rfl rfl (by simp) (by simp) (by simp) (by simp) (by simp),
    fld_wr_ne' hta rfl rfl (by simp) (by simp) (by simp) (by simp) (by simp)]
  exact L.mem_wr_same (field_aligned hta (by simp) (by simp))

/-- `fault_type` reads the `FAULT_TYPE` word. -/
theorem obj.Tcb.fault_type.fa (s : S) (t : obj.Tcb) :
    obj.Tcb.fault_type st t s ⦃ v => v = L.mem s (faultA t) ⦄ := by
  unfold obj.Tcb.fault_type; step*; simp_all [faultA]

theorem sched.set_blocked_on_reply.kwB (s : S) (t r : U64) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) :
    sched.set_blocked_on_reply st s t r ⦃ s' => FootB st T Cs Sg Scs Z Es s s' ⦄ := by
  have hT := h.tcbs
  unfold sched.set_blocked_on_reply
  step with obj.Tcb.set_state.spec as ⟨s1, e1⟩
  step with obj.Tcb.set_reply_obj.wr as ⟨s2, e2⟩
  subst e1 e2
  have f1 : FootB st T Cs Sg Scs Z Es s (L.wr s (stA t) sched.TS_BLOCKED_ON_REPLY) := by
    rw [stA_eq]; exact footB_field hT ht (by simp) (by simp) (by simp) ⟨by simp, by simp, by simp⟩
  have f2 : FootB st T Cs Sg Scs Z Es (L.wr s (stA t) sched.TS_BLOCKED_ON_REPLY)
      (L.wr (L.wr s (stA t) sched.TS_BLOCKED_ON_REPLY) (replyA t) r) :=
    footB_field (K := 3360#u64) hT ht (by simp) (by simp) (by simp) ⟨by simp, by simp, by simp⟩
  have hN : NodePlaced st T (L.wr (L.wr s (stA t) sched.TS_BLOCKED_ON_REPLY) (replyA t) r)
      (L.cpu (L.wr (L.wr s (stA t) sched.TS_BLOCKED_ON_REPLY) (replyA t) r)) := by
    simp only [LawfulStore.cpu_wr]; exact ((h.nodes _ h.cur).ksb (L.ksb_wr _ _ _)).ksb (L.ksb_wr _ _ _)
  exact WP.spec_mono (sched.schedule_tcb.kwB _ t hN (by simp only [LawfulStore.cpu_wr]; exact h.cur))
    fun s3 f3 => f1.trans (f2.trans f3)

/-- **`reply_push` without donation** writes `KWB` words: the reply's `TCB`
word and the caller's state and reply words. -/
theorem ipc.reply_push.kwB0 {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (caller callee r : U64)
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (hcl : caller ∈ T) (hr : r ∈ Rp) :
    ipc.reply_push st ar s a caller callee r false ⦃ s' _ => FootB st T Cs Sg Scs Z Es s s' ⦄ := by
  obtain ⟨hrΩ, -⟩ := objs_omega hO hsub
  unfold ipc.reply_push
  step with obj.Tcb.sc.spec as ⟨i, ei⟩
  step with obj.Reply.set_tcb.spec as ⟨s1, e1⟩
  subst e1
  have f1 : FootB st T Cs Sg Scs Z Es s (L.wr s (rTcbA r) caller) :=
    footB_wr (h.omega _ (hrΩ r hr).1).1 (kwB_sg (hO.tcbW hr))
  have q1 := (omega_wr (v := caller) h (hrΩ r hr).1).1
  refine WP.spec_bind (sched.set_blocked_on_reply.kwB (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) _ caller r q1 hcl)
    fun s2 f2 => ?_
  have f02 := f1.trans f2
  simp only [Bool.false_eq_true, ↓reduceIte]
  step with obj.Sc.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 f02
  · step with obj.Tcb.sc.spec as ⟨i1, ei1⟩
    first | exact f02 | exact (WP.spec_ok _).2 f02 | (split <;> exact (WP.spec_ok _).2 f02)

/-- `send_tail`'s footprint in `KWB`. -/
theorem send_tail.footB (s4 : S) {A : Type _} (a1 : A) (hd : U64)
    (h4 : SchedQueuesInvX st T Cs Ω H X s4 Q R) (hB4 : BoundInv st T Ac s4)
    (hX4 : XInv st T Cs Ω Sg Rp Scs Nt Z s4) (hS4 : SCsOK st T Ω Sg Scs Z Ac s4) (hSg4 : SgOK st Ω Sg s4) (hdT : hd ∈ T)
    (hXc : ExcT X hd) (hx : hd ∈ X ∨ ¬ Blocked (L.mem s4 (stA hd))) (hnr : ∀ r ∈ Rp, L.mem s4 (rTcbA r) ≠ hd) :
    (do
      let s5 ← sched.set_thread_state st s4 hd sched.TS_RUNNING
      let s6 ← endpoint.unblock_sporadic st s5 hd
      let s7 ← sched.possible_switch_to st s6 hd
      ok (s7, a1)) ⦃ s' _ => FootB st T Cs Sg Scs Z Es s4 s' ⦄ := by
  refine WP.spec_bind (WP.spec_and (sts_all s4 hd _ Q R h4 hB4 hX4 hS4 hSg4 hdT not_blocked_running running_ne hx hnr
    ⟨fun _ _ _ _ _ => runnable_running, fun _ _ _ => runnable_running, fun _ => runnable_running⟩)
    (sched.set_thread_state.kwB (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) s4 hd _ h4 hdT)) fun s5 hh' => ?_
  obtain ⟨hh, f5⟩ := hh'
  obtain ⟨h5, hB5, hX5, hS5, hSg5, e5, k5⟩ := hh
  have h5' := h5.congrX (excT_congr hXc)
  refine WP.spec_bind (WP.spec_and (endpoint.unblock_sporadic.all s5 hd h5' hB5 hX5 hS5 hSg5 hdT)
    (endpoint.unblock_sporadic.kwB (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) s5 hd h5' hX5 hS5 hdT)) fun s6 hh' => ?_
  obtain ⟨hh, f6⟩ := hh'
  obtain ⟨h6, -⟩ := hh
  refine WP.spec_bind (sched.possible_switch_to.kwB (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) s6 hd h6 hdT)
    fun s7 f7 => (WP.spec_ok _).2 (f5.trans (f6.trans f7))

/-- A `BlkFoot` step from `s` (no reply object) inside `KWB`. -/
theorem blkfoot_footB {s s' : S} {t : U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T)
    (w : WritesIn st s s' (BlkFoot st s t 0#u64)) : FootB st T Cs Sg Scs Z Es s s' :=
  FootB.of w fun b hb => by
    rcases hb with ⟨K, hK, rfl⟩ | rfl | ⟨h0, -⟩
    · exact kwB_field ht (by omega) (by omega) ⟨by omega, by omega, by omega⟩
    · exact kwB_node h.cur (by rw [act_val]; omega) (by rw [act_val]; omega)
    · exact absurd rfl h0

set_option maxHeartbeats 4000000 in
/-- **The blocking send's footprint** in `KWB`. -/
theorem send_block.footB {A : Type _} (s : S) (a : A) (t e badge : U64) (can_grant can_grant_reply do_call : Bool)
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
      ok (s6, a)) ⦃ s' _ => FootB st T Cs Sg Scs Z (EH H) s s' ⦄ := by
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
      ok (s6, a)) ⦃ s' _ => FootB st T Cs Sg Scs Z (EH H) s s' ⦄ := by
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
    have hW : ∀ w ∈ t :: EQ e, w ∈ T := by
      intro w hw
      rcases List.mem_cons.1 hw with rfl | hw
      · exact ht
      · exact hq.mem w hw
    refine WP.spec_bind (endpoint.ep_append.foot s5 e t obj.EP_SEND (EQ e) h.tcbs hE hq5 ht hn) fun s6 w6 => ?_
    exact (WP.spec_ok _).2 ((blkfoot_footB h ht w5).trans (FootB.of w6 fun b hb => EpFoot.kwB hW (Or.inl hH) hb))
  cases can_grant <;> cases can_grant_reply <;> cases do_call <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Aeneas.Std.bind_ok, lift] <;> exact key _

/-- **`send_ipc`'s footprint on an idle or sending endpoint** in `KWB`. -/
theorem endpoint.send_ipc.blockFootB {A : Type _} (ar : machine.Arch A) (s : S) (a : A) (blocking do_call : Bool)
    (badge : U64) (can_grant can_grant_reply can_donate : Bool) (t e : U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hc : blocking = true → CanBlock st T Ac s t)
    (hH : H e = some .ep) (hst0 : L.epState s e = 0#u64 ∨ L.epState s e = 1#u64) :
    endpoint.send_ipc st ar s a blocking do_call badge can_grant can_grant_reply can_donate t e
      ⦃ s' _ => FootB st T Cs Sg Scs Z (EH H) s s' ⦄ := by
  unfold endpoint.send_ipc
  step with obj.Ep.state.spec as ⟨v, hv⟩
  split
  · split
    · exact send_block.footB s a t e badge can_grant can_grant_reply do_call h (hc ‹_›) hH
    · simp only [WP.spec_ok, WP.uncurry'_pair]; exact FootB.refl _
  · split
    · split
      · exact send_block.footB s a t e badge can_grant can_grant_reply do_call h (hc ‹_›) hH
      · simp only [WP.spec_ok, WP.uncurry'_pair]; exact FootB.refl _
    · exfalso
      rename_i h1 h2
      rw [ep_idle_val] at h1; rw [ep_send_val'] at h2
      rcases hst0 with e0 | e0 <;> rw [← hv] at e0 <;> contradiction

/-! ## The timeout fault's message transfer -/

/-- The words a timeout fault's message transfer writes: the receiver's
register words (TCB offsets in `[256, 3328)`) and SC `CONSUMED` words. -/
abbrev TmoXW (T Scs : Set U64) (b : U64) : Prop := XferRegW T ∅ b ∨ XferConsW Scs b

variable {RS : S → S → Prop}

/-- A `set_mr` of a message register (`i < N_MSG_REGISTERS = 4`): a register write. -/
theorem msg.set_mr.tmo {s0 s : S} {y buf i v : U64}
    (h : XSFC st T Cs Ω H Sg Rp Scs Nt Z ∅ RS Ac X Q R s0 s) (hy : y ∈ T) (hi : i.val < 4) :
    msg.set_mr st s y buf i v ⦃ r => XSFC st T Cs Ω H Sg Rp Scs Nt Z ∅ RS Ac X Q R s0 r.2 ∧
      r.1 = core.num.U64.wrapping_add i 1#u64 ⦄ := by
  unfold msg.set_mr
  have hlt : i < msg.N_MSG_REGISTERS := by
    simp only [msg.N_MSG_REGISTERS]; scalar_tac
  rw [if_pos hlt]
  have hreg : ∀ j, msg.msg_register j ⦃ r => r.val < 384 ⦄ := fun j => by
    unfold msg.msg_register
    split; · simp [layout.reg.R10]
    split; · simp [layout.reg.R8]
    split; · simp [layout.reg.R9]
    simp [layout.reg.R15]
  refine WP.spec_bind (hreg i) fun r hr => ?_
  refine WP.spec_bind (obj.Tcb.set_reg.xsfc (v := v) h hy hr) fun s1 h1 => ?_
  simp only [lift, bind_ok]
  exact (WP.spec_ok _).2 ⟨h1, rfl⟩

/-- **`set_mrs_fault` of a `Timeout` fault**: register writes and the
sender's SC `CONSUMED` word. -/
theorem faults.set_mrs_fault.tmo {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s : S} {a : A}
    {snd rcv buf : U64} (h : XSFC st T Cs Ω H Sg Rp Scs Nt Z ∅ RS Ac X Q R s s) (hs : snd ∈ T) (hr : rcv ∈ T)
    (hft : L.mem s (faultA snd) = fl4_abi.consts.fault.Timeout) :
    faults.set_mrs_fault st ar s a snd rcv buf ⦃ r => XSFC st T Cs Ω H Sg Rp Scs Nt Z ∅ RS Ac X Q R s r.2 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold faults.set_mrs_fault
  refine WP.spec_bind (obj.Tcb.fault_type.fa s snd) fun ty ety => ?_
  rw [hft] at ety
  subst ety
  refine WP.spec_bind (P0.obj.Tcb.fault_w0.p0 st snd s hS) fun w0 _ => ?_
  refine WP.spec_bind (P0.obj.Tcb.fault_w1.p0 st snd s hS) fun w1 _ => ?_
  refine WP.spec_bind (P0.obj.Tcb.fault_w2.p0 st snd s hS) fun w2 _ => ?_
  refine WP.spec_bind (P0.obj.Tcb.reg.p0 st snd s _ hS) fun pc _ => ?_
  have n1 : ¬ (fl4_abi.consts.fault.Timeout = fl4_abi.consts.fault.CapFault) := by
    unfold fl4_abi.consts.fault.Timeout fl4_abi.consts.fault.CapFault; decide
  have n2 : ¬ (fl4_abi.consts.fault.Timeout = fl4_abi.consts.fault.UnknownSyscall) := by
    unfold fl4_abi.consts.fault.Timeout fl4_abi.consts.fault.UnknownSyscall; decide
  have n3 : ¬ (fl4_abi.consts.fault.Timeout = fl4_abi.consts.fault.UserException) := by
    unfold fl4_abi.consts.fault.Timeout fl4_abi.consts.fault.UserException; decide
  rw [if_neg n1, if_neg n2, if_neg n3, if_pos rfl]
  step with obj.Tcb.sc.spec as ⟨c, hc⟩
  simp only [obj.Sc.is_null, bind_ok]
  split
  · exact WP.spec_mono (msg.set_mr.tmo h hr (by simp)) fun _ hr' => hr'.1
  rename_i hne
  have hc0 : L.mem s (scA snd) ≠ 0#u64 := by rw [← hc]; simpa using hne
  have hcS : c ∈ Scs := hc ▸ (h.1.2.2.1.2.2.bound snd hs hc0).1
  refine WP.spec_bind (schedcontext.update_consumed.xsfc hA h hcS) ?_
  rintro ⟨cons, s1⟩ h1
  simp only at h1
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (msg.set_mr.tmo h1 hr (by simp)) ?_
  rintro ⟨len, s2⟩ ⟨h2, hl2⟩
  simp only at h2 hl2
  try simp only [WP.uncurry'_pair]
  subst hl2
  exact WP.spec_mono (msg.set_mr.tmo h2 hr
    (by simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits])) fun _ hr' => hr'.1

theorem ipc.do_fault_transfer.tmo {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s : S} {a : A}
    {badge snd rcv rb : U64} (h : XSFC st T Cs Ω H Sg Rp Scs Nt Z ∅ RS Ac X Q R s s) (hs : snd ∈ T) (hr : rcv ∈ T)
    (hft : L.mem s (faultA snd) = fl4_abi.consts.fault.Timeout) :
    ipc.do_fault_transfer st ar s a badge snd rcv rb ⦃ s' => XSFC st T Cs Ω H Sg Rp Scs Nt Z ∅ RS Ac X Q R s s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold ipc.do_fault_transfer
  refine WP.spec_bind (faults.set_mrs_fault.tmo hA h hs hr hft) ?_
  rintro ⟨sent, s1⟩ h1
  simp only at h1
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (P0.obj.Tcb.fault_type.p0 st snd s1 hS) fun ft _ => ?_
  refine WP.spec_bind (P0.msginfo.MessageInfo.new.p0 _ _ _ _) fun mi _ => ?_
  refine WP.spec_bind (Pₘ := fun s3 => XSFC st T Cs Ω H Sg Rp Scs Nt Z ∅ RS Ac X Q R s s3) ?_
    fun s3 h3 => obj.Tcb.set_reg.xsfc h3 hr (by simp [layout.reg.BADGE, layout.reg.RDI])
  unfold msg.set_msg_info
  exact WP.spec_bind (P0.msginfo.MessageInfo.to_word.p0 _) fun w _ =>
    obj.Tcb.set_reg.xsfc (v := w) h1 hr (by simp [layout.reg.MSG_INFO, layout.reg.RSI])

/-- **The timeout fault's message transfer** (walked, no premise): from a
sender whose `FAULT_TYPE` word holds `Timeout`, `do_ipc_transfer` keeps the
transfer invariants (`XI` with no user words), the frame `XferFr`, and writes
only `TmoXW` words (receiver registers, SC `CONSUMED` words). -/
theorem ipc.do_ipc_transfer.tmo {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s : S} {a : A}
    {snd ep badge : U64} {grant : Bool} {rcv : U64}
    (h : XI st T Cs Ω H Sg Rp Scs Nt Z ∅ Ac X Q R s) (hs : snd ∈ T) (hr : rcv ∈ T)
    (hft : L.mem s (faultA snd) = fl4_abi.consts.fault.Timeout) :
    ipc.do_ipc_transfer st ar s a snd ep badge grant rcv ⦃ s' =>
      XI st T Cs Ω H Sg Rp Scs Nt Z ∅ Ac X Q R s' ∧ XferFr st T Rp s s' ∧ WritesIn st s s' (TmoXW T Scs) ⦄ := by
  have hP : P0.StoreTotal st := L.total
  have h0 : XSFC st T Cs Ω H Sg Rp Scs Nt Z ∅ (fun s0 s1 => WritesIn st s0 s1 (TmoXW T Scs)) Ac X Q R s s :=
    ⟨h, XferFr.refl s, WritesIn.refl s _, WritesIn.refl s _,
      fun s1 s2 r w => (r.trans w).mono fun _ hb => hb.elim id id⟩
  refine WP.spec_mono (P₀ := fun s' => XSFC st T Cs Ω H Sg Rp Scs Nt Z ∅
    (fun s0 s1 => WritesIn st s0 s1 (TmoXW T Scs)) Ac X Q R s s') ?_ fun s' h' => ⟨h'.1, h'.2.1, h'.2.2.2.1⟩
  unfold ipc.do_ipc_transfer
  refine WP.spec_bind (P0.msg.lookup_ipc_buffer.p0 st s true rcv hP) fun rb _ => ?_
  refine WP.spec_bind (obj.Tcb.fault_type.fa s snd) fun ft eft => ?_
  have hne : ¬ (ft = fl4_abi.consts.fault.NullFault) := by
    rw [eft, hft]; unfold fl4_abi.consts.fault.Timeout fl4_abi.consts.fault.NullFault; decide
  rw [if_neg hne]
  exact ipc.do_fault_transfer.tmo hA h0 hs hr hft


/-! ## `send_ipc` of a timeout fault -/

/-- **`send_ipc` of a sender whose `FAULT_TYPE` word holds `Timeout` keeps
`BlkOK`** (P1 `send_ipc.ipc`, with its `XferOK` premise replaced by the walked
timeout transfer `do_ipc_transfer.tmo`; no `UserOK`). -/
theorem endpoint.send_ipc.ipcTmo {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (s : S) (a : A) (blocking do_call : Bool)
    (badge : U64) (can_grant can_grant_reply can_donate : Bool) (t e : U64)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s)
    (hc : CanBlock st T Ac s t) (hdon : can_donate = true → L.mem s (scA t) ≠ 0#u64)
    (hH : H e = some .ep) (hft : L.mem s (faultA t) = fl4_abi.consts.fault.Timeout) :
    endpoint.send_ipc st ar s a blocking do_call badge can_grant can_grant_reply can_donate t e
      ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  have hidle := hc.ni
  have hT := h.tcbs
  have ht := hc.mem
  have hta := hT t ht
  rcases ep_state3 h hH with e0 | e0 | e0
  · exact WP.spec_mono (endpoint.send_ipc.block ar s a blocking do_call badge can_grant can_grant_reply can_donate
      t e Q R h hB hX hS hSg (fun _ => hc) hH (Or.inl e0)) fun r hh => by
        obtain ⟨s', a'⟩ := r; simp only [WP.uncurry'_pair] at hh ⊢; exact ⟨⟨Q, R, hh.1⟩, hh.2⟩
  · exact WP.spec_mono (endpoint.send_ipc.block ar s a blocking do_call badge can_grant can_grant_reply can_donate
      t e Q R h hB hX hS hSg (fun _ => hc) hH (Or.inr e0)) fun r hh => by
        obtain ⟨s', a'⟩ := r; simp only [WP.uncurry'_pair] at hh ⊢; exact ⟨⟨Q, R, hh.1⟩, hh.2⟩
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
  refine WP.spec_bind (spec_eq' hdq) ?_
  rintro s1 ⟨eq1, h1, f1, o1, n1, k1, c1, nc1⟩
  obtain ⟨hB1, hX1, hS1, hSg1, ea1, ec1, ei1⟩ := frame_bx h hB hX hS hSg f1 o1 n1 k1
    (TmFr.mk0 ⟨k1, fun y hy K a b c => f1 y hy K (by omega) c (by omega) (by omega),
      fun c hc o ho => nc1 c hc o (by omega) (by omega), fun n' hn' => o1 _ (hSg.sub _ (hX.1.ntB n' hn').2)⟩)
  have hft1 : L.mem s1 (faultA t) = fl4_abi.consts.fault.Timeout :=
    (f1 t ht 3376#u64 (by simp) (by simp) (by simp) (by simp)).trans hft
  refine WP.spec_bind (ipc.do_ipc_transfer.tmo (ep := e) (badge := badge) (grant := can_grant) (a := a)
      hA (⟨h1, hB1, hX1, hS1, hSg1, fun _ hb => absurd hb (Set.notMem_empty _)⟩ :
        XI st T Cs Ω H Sg Rp Scs Nt Z ∅ Ac _ Q R s1) ht hdT hft1) ?_
  rintro s2 ⟨⟨h2, hB2, hX2, hS2, hSg2, -⟩, ⟨ea2, ec2, ei2, ecs2, f2, o2, -⟩, -⟩
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
      L.mem s3 (scA hd) = L.mem s (scA hd)) ?_ ?_
  · split
    · rename_i hi
      have hi0 : i ≠ 0#u64 := by simpa using hi
      obtain ⟨hiR, hit⟩ := hX2.2.1.recv hd hdT hds2 (by rw [← ei]; exact hi0)
      rw [← ei] at hiR hit
      refine WP.spec_mono (ipc.reply_unlink.inv s2 i hd Q R h2 hdT hX2.1 hsub hiR hit
        (by rw [hds2]; exact blocked_not_runnable (Or.inr (Or.inl rfl))) (Or.inl (Or.inr rfl))) fun s3 hh => ?_
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
        ?_, k3.idleW.trans ei2', (k3.scf hdT).trans (Fsc hd hdT)⟩
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
        Fst t ht, Fiq t ht, Fsc t ht, by rw [ea2']; exact hc.na, ei2', Fsc hd hdT⟩
  rintro s3 ⟨X3, h3, hB3, hX3, hS3, hSg3, hXc3, hx3, hnr3, hz3, hin3, hpu3, st3, iq3, sc3, na3, ei3, shd3⟩
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
      (L.mem r.1 (scA hd) ≠ 0#u64 → L.mem r.1 (scA hd) ∈ Ac)) ?_ ?_
  rotate_left
  · rintro ⟨s4, a1⟩ ⟨X4, ⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4, hXc4, hx4, hnr4, hdA4⟩
    try simp only [WP.uncurry'_pair]
    exact send_tail s4 a1 hd Q4 R4 h4 hB4 hX4 hS4 hSg4 hdT hXc4 hx4 hnr4 hdA4
  have Ppush : ∀ cd : Bool, (i != 0#u64) = true → ipc.reply_push st ar s3 a t hd i cd ⦃ r => ∃ X4 : Set U64,
      (∃ Q4 R4, SchedQueuesInvX st T Cs Ω H X4 r.1 Q4 R4) ∧
      BoundInv st T Ac r.1 ∧ XInv st T Cs Ω Sg Rp Scs Nt Z r.1 ∧ SCsOK st T Ω Sg Scs Z Ac r.1 ∧ SgOK st Ω Sg r.1 ∧
      ExcT X4 hd ∧ (hd ∈ X4 ∨ ¬ Blocked (L.mem r.1 (stA hd))) ∧ (∀ r' ∈ Rp, L.mem r.1 (rTcbA r') ≠ hd) ∧
      (L.mem r.1 (scA hd) ≠ 0#u64 → L.mem r.1 (scA hd) ∈ Ac) ⦄ := by
    intro cd hi
    obtain ⟨hdX, hiR, hiz⟩ := hpu3 hi
    have hi0 : i ≠ 0#u64 := by simpa using hi
    refine WP.spec_mono (ipc.reply_push.ipc hA s3 a t hd i cd Q R h3
      (fun y hy => absurd (hXc3 y hy ▸ hy) hdX) (Or.inr hnb3) hB3 hX3 hS3 hSg3 ht htq3 htr3 na3 hidle3 hcold3
      hiR hi0 hiz hdT hdt dq dr da (by rw [ei3]; exact hdi) htA3) fun r hh => ?_
    obtain ⟨s4, a4⟩ := r
    simp only [WP.uncurry'_pair] at hh
    obtain ⟨⟨⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4⟩, st4, sc4⟩ := hh
    have e4 : L.mem s4 (stA hd) = sched.TS_INACTIVE := (st4 hd hdT hdt).trans (hin3 hdX)
    exact ⟨∅, ⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4, fun y hy => absurd hy (Set.notMem_empty _),
      Or.inr (by rw [e4]; exact not_blocked_inactive),
      hX4.noref hdta (by rw [e4]; exact inactive_ne.1) (by rw [e4]; exact inactive_ne.2), fun h0 => by
        rcases sc4 with e | e
        · rw [e] at h0 ⊢; exact hdA3 h0
        · rw [e] at h0 ⊢; exact htA3 h0⟩
  have Pinact : (do
      let s5 ← sched.set_thread_state st s3 t sched.TS_INACTIVE
      ok (s5, a)) ⦃ r => ∃ X4 : Set U64, (∃ Q4 R4, SchedQueuesInvX st T Cs Ω H X4 r.1 Q4 R4) ∧
      BoundInv st T Ac r.1 ∧ XInv st T Cs Ω Sg Rp Scs Nt Z r.1 ∧ SCsOK st T Ω Sg Scs Z Ac r.1 ∧ SgOK st Ω Sg r.1 ∧
      ExcT X4 hd ∧ (hd ∈ X4 ∨ ¬ Blocked (L.mem r.1 (stA hd))) ∧ (∀ r' ∈ Rp, L.mem r.1 (rTcbA r') ≠ hd) ∧
      (L.mem r.1 (scA hd) ≠ 0#u64 → L.mem r.1 (scA hd) ∈ Ac) ⦄ := by
    refine WP.spec_bind (sts_all s3 t _ Q R h3 hB3 hX3 hS3 hSg3 ht not_blocked_inactive inactive_ne (Or.inr hnb3)
      hnt3 ⟨fun c hc' p hp hm => absurd hm (h3.notQ ht htq3 hc' hp), fun c hc' hm => absurd hm (h3.notR ht htr3 hc'),
        fun e' => absurd e' na3⟩) fun s4 hh => ?_
    obtain ⟨h4, hB4, hX4, hS4, hSg4, -, k4⟩ := hh
    refine (WP.spec_ok _).2 ⟨{y | y ∈ X3 ∧ y ≠ t}, ⟨Q, R, h4⟩, hB4, hX4, hS4, hSg4,
      fun y hy => hXc3 y hy.1, ?_, fun r hr => ?_, fun h0 => by rw [k4.scf hdT] at h0 ⊢; exact hdA3 h0⟩
    · rcases hx3 with hm | hnb
      · exact Or.inl ⟨hm, hdt⟩
      · exact Or.inr (by rw [k4.stf hdT hdt]; exact hnb)
    · rcases k4.rtcb r hr with e' | ⟨-, e'⟩
      · rw [e']; exact hnd3 r hr
      · rw [e']; exact fun e2 => hdta.ne0 (by rw [← e2]; rfl)
  have Pok : (ok (s3, a) : Result (S × A)) ⦃ r => ∃ X4 : Set U64, (∃ Q4 R4, SchedQueuesInvX st T Cs Ω H X4 r.1 Q4 R4) ∧
      BoundInv st T Ac r.1 ∧ XInv st T Cs Ω Sg Rp Scs Nt Z r.1 ∧ SCsOK st T Ω Sg Scs Z Ac r.1 ∧ SgOK st Ω Sg r.1 ∧
      ExcT X4 hd ∧ (hd ∈ X4 ∨ ¬ Blocked (L.mem r.1 (stA hd))) ∧ (∀ r' ∈ Rp, L.mem r.1 (rTcbA r') ≠ hd) ∧
      (L.mem r.1 (scA hd) ≠ 0#u64 → L.mem r.1 (scA hd) ∈ Ac) ⦄ :=
    (WP.spec_ok _).2 ⟨X3, ⟨Q, R, h3⟩, hB3, hX3, hS3, hSg3, hXc3, hx3, hnd3, hdA3⟩
  have Pdon : can_donate = true → (do
      let i2 ← obj.Tcb.sc st hd s3
      if i2 = 0#u64 then do
          let i3 ← obj.Tcb.sc st t s3
          schedcontext.donate st ar s3 a i3 hd
        else ok (s3, a)) ⦃ r => ∃ X4 : Set U64, (∃ Q4 R4, SchedQueuesInvX st T Cs Ω H X4 r.1 Q4 R4) ∧
      BoundInv st T Ac r.1 ∧ XInv st T Cs Ω Sg Rp Scs Nt Z r.1 ∧ SCsOK st T Ω Sg Scs Z Ac r.1 ∧ SgOK st Ω Sg r.1 ∧
      ExcT X4 hd ∧ (hd ∈ X4 ∨ ¬ Blocked (L.mem r.1 (stA hd))) ∧ (∀ r' ∈ Rp, L.mem r.1 (rTcbA r') ≠ hd) ∧
      (L.mem r.1 (scA hd) ≠ 0#u64 → L.mem r.1 (scA hd) ∈ Ac) ⦄ := by
    intro hcd
    step with obj.Tcb.sc.spec as ⟨i2, ei2⟩
    split
    · rename_i hi2
      step with obj.Tcb.sc.spec as ⟨i3, ei3'⟩
      refine WP.spec_mono (schedcontext.donate.ipc hA s3 a i3 hd t Q R h3 hB3 hX3 hS3 hSg3 ht ei3'.symm
        (by rw [ei3', sc3]; exact hdon hcd) ⟨htq3, htr3, na3⟩ hidle3 hdT (by rw [← ei2, hi2]) dq dr da hdt
        (by rw [ei3']; exact htA3 (by rw [sc3]; exact hdon hcd)) (by rw [ei3]; exact hdi))
        fun r hh => ?_
      obtain ⟨s4, a4⟩ := r
      simp only [WP.uncurry'_pair] at hh
      obtain ⟨⟨⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4⟩, st4, rp4, sd4⟩ := hh
      refine ⟨X3, ⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4, hXc3, ?_, ?_,
        fun _ => by rw [sd4, ei3']; exact htA3 (by rw [sc3]; exact hdon hcd)⟩
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

/-! ## `complete_signal` -/

/-- The timeout transfer's words are no node identity or protected words, and
it keeps the action (`XferWC.ipcN` for `TmoXW`). -/
theorem TmoXW.ipcN {Kp : Set U64} {Nd : Prop} {s s' : S} (h : SchedQueuesInvX st T Cs Ω H X s Q R)
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (w : WritesIn st s s' (TmoXW T Scs)) :
    WritesA st T Kp s s' (fun b => TmoXW T Scs b ∧ ¬ IdW st Kp Nd T Cs Scs s b) := by
  have hO := hX.1
  have hN := h.nodes _ h.cur
  have hact : L.actionW s' = L.actionW s := by
    refine actionW_of w hN ?_
    have e16 : layout.node.SCHED_ACTION.val = 16 := act_val
    rintro ((⟨y, hy, K, -, hK, -, e⟩ | hu) | ⟨c, hc, e⟩)
    · exact node_ne_field hN (by omega) hy (h.tcbs y hy) (by omega) e
    · exact absurd hu (Set.notMem_empty _)
    · exact notAct_omega h (hO.scW c hc _ (act_aligned hN) (e ▸ (consW_in hO hc).2))
  refine ⟨w.1, w.2.1, fun b hb hn => w.2.2 b hb fun hx => hn ⟨hx, ?_⟩, AcK.of_eq hact⟩
  rcases hx with (⟨y, hy, K, -, hK, -, e⟩ | hu) | ⟨c, hc, e⟩
  · subst e; exact notIdW_field h.tcbs h.nodes hy (by omega)
  · exact absurd hu (Set.notMem_empty _)
  · subst e
    exact notIdW_out h.nodes (h.omega _ (hO.scW c hc _ hb (consW_in hO hc).2)) fun _ c' hc' => cons_ne_hdr hO hc hc'


variable {Kp : Set U64} {Nd : Prop}

set_option maxHeartbeats 4000000 in
/-- **A property the timeout fault's `send_ipc` keeps** (P2 `send_ipc.footPN`
without a donation, with the walked timeout transfer in place of `XferOKRS`):
`Pst` holds at the start, is kept by steps that are both `KWN` (`FootDN`) and
`KWB` (`FootDB`) steps (`hPK`), and by the transfer's `TmoXW` writes (`hxP`). -/
theorem endpoint.send_ipc.frTmo {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (s : S) (a : A) (blocking do_call : Bool)
    (badge : U64) (can_grant can_grant_reply can_donate : Bool) (t e : U64)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s)
    (hc : CanBlock st T Ac s t) (hdon : can_donate = true → L.mem s (scA t) ≠ 0#u64)
    (hH : H e = some .ep) (hft : L.mem s (faultA t) = fl4_abi.consts.fault.Timeout) (hcd0 : can_donate = false)
    (hKt : t ∉ Kp) (hKB : ∀ y ∈ Kp, ¬ Blocked (L.mem s (stA y))) (hdK : can_donate = true → ¬ Nd) (hKa : ActOut st T Kp s) (Pst : S → Prop)
    (hPK : ∀ s1 s2 : S, Pst s1 → FootDN st Kp Nd T Cs Sg Scs Z (EH H) s1 s2 → FootDB st T Cs Sg Scs Z (EH H) s1 s2 →
      Pst s2) (hP0 : Pst s)
    (hxP : ∀ s1 s2 : S, Pst s1 → WritesA st T Kp s1 s2 (fun b => TmoXW T Scs b ∧ ¬ IdW st Kp Nd T Cs Scs s1 b) →
      Pst s2) :
    endpoint.send_ipc st ar s a blocking do_call badge can_grant can_grant_reply can_donate t e
      ⦃ s' _ => Pst s' ⦄ := by
  subst hcd0
  have hidle := hc.ni
  have hT := h.tcbs
  have ht := hc.mem
  have hta := hT t ht
  rcases ep_state3 h hH with e0 | e0 | e0
  · exact WP.spec_mono (WP.spec_and (endpoint.send_ipc.blockFootN (Sg := Sg) (Kp := Kp) (Nd := Nd) (Scs := Scs) (Z := Z) ar s a blocking do_call badge
      can_grant can_grant_reply false t e h (fun _ => hc) hH (Or.inl e0) hKt (hdrΩ_of hX hSg.sub))
      (endpoint.send_ipc.blockFootB (Sg := Sg) (Scs := Scs) (Z := Z) ar s a blocking do_call badge
        can_grant can_grant_reply false t e h (fun _ => hc) hH (Or.inl e0))) fun r hh => by
        obtain ⟨s', a'⟩ := r; simp only [WP.uncurry'_pair] at hh ⊢; exact hPK _ _ hP0 hh.1.d hh.2.d
  · exact WP.spec_mono (WP.spec_and (endpoint.send_ipc.blockFootN (Sg := Sg) (Kp := Kp) (Nd := Nd) (Scs := Scs) (Z := Z) ar s a blocking do_call badge
      can_grant can_grant_reply false t e h (fun _ => hc) hH (Or.inr e0) hKt (hdrΩ_of hX hSg.sub))
      (endpoint.send_ipc.blockFootB (Sg := Sg) (Scs := Scs) (Z := Z) ar s a blocking do_call badge
        can_grant can_grant_reply false t e h (fun _ => hc) hH (Or.inr e0))) fun r hh => by
        obtain ⟨s', a'⟩ := r; simp only [WP.uncurry'_pair] at hh ⊢; exact hPK _ _ hP0 hh.1.d hh.2.d
  -- a receiving endpoint
  obtain ⟨hdT, hbe, -, hds⟩ := ep_head h hH (Or.inr rfl) e0
  have hds := hds rfl
  set hd := (L.epQ s e).head with hhd
  have hdt : hd ≠ t := fun e' => hc.nb (by rw [← e', hds]; exact Or.inr (Or.inl rfl))
  have hdi : L.idleW s ≠ hd := fun e' => hB.idleNB (by rw [e', hds]; exact Or.inl (Or.inr (Or.inl rfl)))
  have hKd : hd ∉ Kp := fun hk => hKB hd hk (by rw [hds]; exact Or.inr (Or.inl rfl))
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
  obtain ⟨hE0, hEN0, hq0⟩ := hEW0.1 e heE0
  have hdm : hd ∈ EQ0 e := by
    have := hEW0.2.2.2.2.1 hd hdT (by simp) (Or.inr (Or.inl hds)); rw [hbe] at this; exact this.2
  refine WP.spec_bind (WP.spec_and hdq (endpoint.ep_dequeue.foot s e hd (EQ0 e) hT hE0 hq0 hdm)) ?_
  rintro s1 ⟨⟨h1, f1, o1, n1, k1, c1, nc1⟩, w1⟩
  have F1 : FootN st Kp Nd T Cs Sg Scs Z (EH H) s s1 :=
    FootN.of' w1 (hk := AcK.of_eq (EpFoot.act hT h.nodes h.cur hq0.mem hE0 hEN0 w1)) fun b _ hb => EpFoot.kwN hT h.nodes hq0.mem (Or.inl hH) hE0 hEN0 (hEW0.2.2.1 e heE0) (hdrΩ_of hX hSg.sub) hb
  have B1 : FootDB st T Cs Sg Scs Z (EH H) s s1 :=
    FootB.d (w1.mono fun b hb => EpFoot.kwB (Sg := Sg) (Scs := Scs) (Z := Z) (Cs := Cs) hq0.mem (Or.inl hH) hb)
  have P1 : Pst s1 := hPK s s1 hP0 F1.d B1
  obtain ⟨hB1, hX1, hS1, hSg1, ea1, ec1, ei1⟩ := frame_bx h hB hX hS hSg f1 o1 n1 k1
    (TmFr.mk0 ⟨k1, fun y hy K a b c => f1 y hy K (by omega) c (by omega) (by omega),
      fun c hc o ho => nc1 c hc o (by omega) (by omega), fun n' hn' => o1 _ (hSg.sub _ (hX.1.ntB n' hn').2)⟩)
  have hft1 : L.mem s1 (faultA t) = fl4_abi.consts.fault.Timeout :=
    (f1 t ht 3376#u64 (by simp) (by simp) (by simp) (by simp)).trans hft
  refine WP.spec_bind (ipc.do_ipc_transfer.tmo (ep := e) (badge := badge) (grant := can_grant) (a := a)
      hA (⟨h1, hB1, hX1, hS1, hSg1, fun _ hb => absurd hb (Set.notMem_empty _)⟩ :
        XI st T Cs Ω H Sg Rp Scs Nt Z ∅ Ac _ Q R s1) ht hdT hft1) ?_
  rintro s2 ⟨⟨h2, hB2, hX2, hS2, hSg2, -⟩, ⟨ea2, ec2, ei2, ecs2, f2, o2, -⟩, w2⟩
  have F2 : Pst s2 := hxP s1 s2 P1 (TmoXW.ipcN h1 hX1 w2)
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
  have Ka2 : ActOut st T Kp s2 := hKa.step (AcK.of_eq ea2')
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
      L.mem s3 (scA hd) = L.mem s (scA hd) ∧ Pst s3 ∧ ActOut st T Kp s3) ?_ ?_
  · split
    · rename_i hi
      have hi0 : i ≠ 0#u64 := by simpa using hi
      obtain ⟨hiR, hit⟩ := hX2.2.1.recv hd hdT hds2 (by rw [← ei]; exact hi0)
      rw [← ei] at hiR hit
      refine WP.spec_mono (WP.spec_and (ipc.reply_unlink.inv s2 i hd Q R h2 hdT hX2.1 hsub hiR hit
        (by rw [hds2]; exact blocked_not_runnable (Or.inr (Or.inl rfl))) (Or.inl (Or.inr rfl)))
        (WP.spec_and (ipc.reply_unlink.kwN (Sg := Sg) (Kp := Kp) (Nd := Nd) (Scs := Scs) (Z := Z) (Es := EH H) s2 i hd h2 hX2 hsub hiR hdT hKd)
          (ipc.reply_unlink.kwB (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s2 i hd h2 hX2 hsub hiR hdT))) fun s3 hh' => ?_
      obtain ⟨hh, fu, fb⟩ := hh'
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
        ?_, k3.idleW.trans ei2', (k3.scf hdT).trans (Fsc hd hdT), hPK _ _ F2 fu.d fb.d, fu.out Ka2⟩
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
        Fst t ht, Fiq t ht, Fsc t ht, by rw [ea2']; exact hc.na, ei2', Fsc hd hdT, F2, Ka2⟩
  rintro s3 ⟨X3, h3, hB3, hX3, hS3, hSg3, hXc3, hx3, hnr3, hz3, hin3, hpu3, st3, iq3, sc3, na3, ei3, shd3, F3, Ka3⟩
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
      FootDN st Kp Nd T Cs Sg Scs Z (EH H) s3 r.1 ∧ FootDB st T Cs Sg Scs Z (EH H) s3 r.1) ?_ ?_
  rotate_left
  · rintro ⟨s4, a1⟩ ⟨X4, ⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4, hXc4, hx4, hnr4, hdA4, f4, g4⟩
    try simp only [WP.uncurry'_pair]
    refine WP.spec_mono (WP.spec_and (send_tail.footN (Sg := Sg) (Kp := Kp) (Nd := Nd) (Scs := Scs) (Z := Z) (Es := EH H) s4 a1 hd Q4 R4 h4 hB4 hX4 hS4
      hSg4 hdT hXc4 hx4 hnr4 hdA4 hKd (f4.out Ka3))
      (send_tail.footB (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s4 a1 hd h4 hB4 hX4 hS4 hSg4 hdT hXc4 hx4 hnr4))
      fun r hr => ?_
    obtain ⟨s', a'⟩ := r
    simp only [WP.uncurry'_pair] at hr ⊢
    exact hPK _ _ F3 (f4.trans hr.1.d) (g4.trans hr.2.d)
  have Ppush : (i != 0#u64) = true → ipc.reply_push st ar s3 a t hd i false ⦃ r => ∃ X4 : Set U64,
      (∃ Q4 R4, SchedQueuesInvX st T Cs Ω H X4 r.1 Q4 R4) ∧
      BoundInv st T Ac r.1 ∧ XInv st T Cs Ω Sg Rp Scs Nt Z r.1 ∧ SCsOK st T Ω Sg Scs Z Ac r.1 ∧ SgOK st Ω Sg r.1 ∧
      ExcT X4 hd ∧ (hd ∈ X4 ∨ ¬ Blocked (L.mem r.1 (stA hd))) ∧ (∀ r' ∈ Rp, L.mem r.1 (rTcbA r') ≠ hd) ∧
      (L.mem r.1 (scA hd) ≠ 0#u64 → L.mem r.1 (scA hd) ∈ Ac) ∧
      FootDN st Kp Nd T Cs Sg Scs Z (EH H) s3 r.1 ∧ FootDB st T Cs Sg Scs Z (EH H) s3 r.1 ⦄ := by
    intro hi
    obtain ⟨hdX, hiR, hiz⟩ := hpu3 hi
    have hi0 : i ≠ 0#u64 := by simpa using hi
    refine WP.spec_mono (WP.spec_and (ipc.reply_push.ipc hA s3 a t hd i false Q R h3
      (fun y hy => absurd (hXc3 y hy ▸ hy) hdX) (Or.inr hnb3) hB3 hX3 hS3 hSg3 ht htq3 htr3 na3 hidle3 hcold3
      hiR hi0 hiz hdT hdt dq dr da (by rw [ei3]; exact hdi) htA3)
      (WP.spec_and (ipc.reply_push.kwN (Sg := Sg) (Kp := Kp) (Nd := Nd) (Scs := Scs) (Z := Z) (Es := EH H) hA s3 a t hd i false h3
      (fun y hy => absurd (hXc3 y hy ▸ hy) hdX) (Or.inr hnb3) hB3 hX3 hS3 hSg3 ht htq3 htr3 na3 hidle3 hcold3
      hiR hi0 hiz hdT htA3 hKt hdK Ka3)
      (ipc.reply_push.kwB0 (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s3 a t hd i h3 hX3.1 hSg3.sub ht hiR))) fun r hh' => ?_
    obtain ⟨s4, a4⟩ := r
    simp only [WP.uncurry'_pair] at hh'
    obtain ⟨hh, fk, fb⟩ := hh'
    obtain ⟨⟨⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4⟩, st4, sc4⟩ := hh
    have e4 : L.mem s4 (stA hd) = sched.TS_INACTIVE := (st4 hd hdT hdt).trans (hin3 hdX)
    exact ⟨∅, ⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4, fun y hy => absurd hy (Set.notMem_empty _),
      Or.inr (by rw [e4]; exact not_blocked_inactive),
      hX4.noref hdta (by rw [e4]; exact inactive_ne.1) (by rw [e4]; exact inactive_ne.2), fun h0 => by
        rcases sc4 with e | e
        · rw [e] at h0 ⊢; exact hdA3 h0
        · rw [e] at h0 ⊢; exact htA3 h0, fk, fb.d⟩
  have Pinact : (do
      let s5 ← sched.set_thread_state st s3 t sched.TS_INACTIVE
      ok (s5, a)) ⦃ r => ∃ X4 : Set U64, (∃ Q4 R4, SchedQueuesInvX st T Cs Ω H X4 r.1 Q4 R4) ∧
      BoundInv st T Ac r.1 ∧ XInv st T Cs Ω Sg Rp Scs Nt Z r.1 ∧ SCsOK st T Ω Sg Scs Z Ac r.1 ∧ SgOK st Ω Sg r.1 ∧
      ExcT X4 hd ∧ (hd ∈ X4 ∨ ¬ Blocked (L.mem r.1 (stA hd))) ∧ (∀ r' ∈ Rp, L.mem r.1 (rTcbA r') ≠ hd) ∧
      (L.mem r.1 (scA hd) ≠ 0#u64 → L.mem r.1 (scA hd) ∈ Ac) ∧
      FootDN st Kp Nd T Cs Sg Scs Z (EH H) s3 r.1 ∧ FootDB st T Cs Sg Scs Z (EH H) s3 r.1 ⦄ := by
    refine WP.spec_bind (WP.spec_and (sts_all s3 t _ Q R h3 hB3 hX3 hS3 hSg3 ht not_blocked_inactive inactive_ne (Or.inr hnb3)
      hnt3 ⟨fun c hc' p hp hm => absurd hm (h3.notQ ht htq3 hc' hp), fun c hc' hm => absurd hm (h3.notR ht htr3 hc'),
        fun e' => absurd e' na3⟩)
      (WP.spec_and (sched.set_thread_state.kwN (Sg := Sg) (Kp := Kp) (Nd := Nd) (Scs := Scs) (Z := Z) (Es := EH H) s3 t _ h3 ht hKt)
        (sched.set_thread_state.kwB (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s3 t _ h3 ht))) fun s4 hh' => ?_
    obtain ⟨hh, fk, fb⟩ := hh'
    obtain ⟨h4, hB4, hX4, hS4, hSg4, -, k4⟩ := hh
    refine (WP.spec_ok _).2 ⟨{y | y ∈ X3 ∧ y ≠ t}, ⟨Q, R, h4⟩, hB4, hX4, hS4, hSg4,
      fun y hy => hXc3 y hy.1, ?_, fun r hr => ?_, fun h0 => by rw [k4.scf hdT] at h0 ⊢; exact hdA3 h0, fk.d, fb.d⟩
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
      FootDN st Kp Nd T Cs Sg Scs Z (EH H) s3 r.1 ∧ FootDB st T Cs Sg Scs Z (EH H) s3 r.1 ⦄ :=
    (WP.spec_ok _).2 ⟨X3, ⟨Q, R, h3⟩, hB3, hX3, hS3, hSg3, hXc3, hx3, hnd3, hdA3, FootDN.refl _, WritesIn.refl _ _⟩
  have Pdon : false = true → (do
      let i2 ← obj.Tcb.sc st hd s3
      if i2 = 0#u64 then do
          let i3 ← obj.Tcb.sc st t s3
          schedcontext.donate st ar s3 a i3 hd
        else ok (s3, a)) ⦃ r => ∃ X4 : Set U64, (∃ Q4 R4, SchedQueuesInvX st T Cs Ω H X4 r.1 Q4 R4) ∧
      BoundInv st T Ac r.1 ∧ XInv st T Cs Ω Sg Rp Scs Nt Z r.1 ∧ SCsOK st T Ω Sg Scs Z Ac r.1 ∧ SgOK st Ω Sg r.1 ∧
      ExcT X4 hd ∧ (hd ∈ X4 ∨ ¬ Blocked (L.mem r.1 (stA hd))) ∧ (∀ r' ∈ Rp, L.mem r.1 (rTcbA r') ≠ hd) ∧
      (L.mem r.1 (scA hd) ≠ 0#u64 → L.mem r.1 (scA hd) ∈ Ac) ∧
      FootDN st Kp Nd T Cs Sg Scs Z (EH H) s3 r.1 ∧ FootDB st T Cs Sg Scs Z (EH H) s3 r.1 ⦄ := by
    intro hcd; exact absurd hcd (by decide)
  split
  · repeat' split
    all_goals first
      | exact Pinact
      | exact Ppush (by assumption)
  · step with obj.Tcb.fault_type.any as ⟨i1, _⟩
    repeat' split
    all_goals first
      | exact Pinact
      | exact Ppush (by assumption)
      | exact Pdon (by assumption)
      | exact Pok


/-! ## The timeout fault's footprint -/

/-- **The words a timeout fault writes**, from `s0`: `KWB` words (no
`IPC_BUFFER` word), debug-list words and the transfer's `TmoXW` words (no
cap-slot word, no user word), none a node identity or protected word. -/
def TmoFW (st : machine.Store S) [L : LawfulStore st] (Kp : Set U64) (Nd : Prop) (T Cs Sg Scs : Set U64)
    (Z : U64 → Nat) (Es : Set U64) (s0 : S) (b : U64) : Prop :=
  (KWB st T Cs Sg Scs Z Es s0 b ∨ DbgW st T Cs s0 b ∨ TmoXW T Scs b) ∧ ¬ IdW st Kp Nd T Cs Scs s0 b

/-- A footprint inside `TmoFW`. -/
abbrev FootT (st : machine.Store S) [L : LawfulStore st] (Kp : Set U64) (Nd : Prop) (T Cs Sg Scs : Set U64)
    (Z : U64 → Nat) (Es : Set U64) (s s' : S) : Prop :=
  WritesA st T Kp s s' (TmoFW st Kp Nd T Cs Sg Scs Z Es s)

theorem FootT.refl (s : S) : FootT st Kp Nd T Cs Sg Scs Z Es s s := WritesA.refl _ _

theorem FootT.trans {s₁ s₂ s₃ : S} (h₁ : FootT st Kp Nd T Cs Sg Scs Z Es s₁ s₂)
    (h₂ : FootT st Kp Nd T Cs Sg Scs Z Es s₂ s₃) : FootT st Kp Nd T Cs Sg Scs Z Es s₁ s₃ :=
  WritesA.mono (WritesA.trans h₁ h₂) fun b hb => by
    rcases hb with hb | ⟨hb, hn⟩
    · exact hb
    · refine ⟨?_, notIdW_ksb h₁.1.symm h₁.2.1.symm hn⟩
      rcases hb with hb | hb | hb
      · exact Or.inl (KWB.ksb h₁.1 hb)
      · exact Or.inr (Or.inl (DbgW.ksb h₁.1 hb))
      · exact Or.inr (Or.inr hb)

/-- A step that is both a `KWN` (`FootDN`) and a `KWB` (`FootDB`) step. -/
theorem FootT.of_db {s s' : S} (fn : FootDN st Kp Nd T Cs Sg Scs Z Es s s') (fb : FootDB st T Cs Sg Scs Z Es s s') :
    FootT st Kp Nd T Cs Sg Scs Z Es s s' :=
  WritesA.mono ((WritesIn.and fn.w fb).a fn.ac) fun _ hb =>
    ⟨hb.2.elim Or.inl fun d => Or.inr (Or.inl d), hb.1.2⟩

/-- The timeout transfer's step. -/
theorem FootT.of_xw {s s' : S}
    (w : WritesA st T Kp s s' (fun b => TmoXW T Scs b ∧ ¬ IdW st Kp Nd T Cs Scs s b)) :
    FootT st Kp Nd T Cs Sg Scs Z Es s s' :=
  WritesA.mono w fun _ hb => ⟨Or.inr (Or.inr hb.1), hb.2⟩

/-- **The timeout fault keeps `BlkOK` and writes only `TmoFW` words**
(`faults.handle_timeout` with a `Timeout` fault, walked: `set_fault`, then
`send_ipc` with no call and no donation, whose transfer is the fault-only
`do_ipc_transfer.tmo`). Premises: the thread can block (`CanBlock`), its
timeout handler cap typed (`hcap`), and the exclusion layer of P2's
`handle_timeout.footN` (`Kp`). No transfer premise. -/
theorem faults.handle_timeout.tmoFr {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (t : obj.Tcb) (b : U64)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hc : CanBlock st T Ac s t)
    (hcap : obj.Tcb.slot t layout.tcb.SLOT_TIMEOUT_HANDLER ⦃ sl =>
      obj.Slot.cap st sl s ⦃ c => CapTyped H Rp Nt c ⦄ ⦄)
    (hKt : t ∉ Kp) (hKT : ∀ y ∈ Kp, y ∈ T) (hKB : ∀ y ∈ Kp, ¬ Blocked (L.mem s (stA y)))
    (hKa : ActOut st T Kp s) :
    faults.handle_timeout st ar s a t (error.Fault.Timeout b) ⦃ s' _ =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ FootT st Kp Nd T Cs Sg Scs Z (EH H) s s' ⦄ := by
  have ht := hc.mem
  have hU0 : UserOK st T Cs Ω H ∅ s := fun _ hb => absurd hb (Set.notMem_empty _)
  unfold faults.handle_timeout
  refine WP.spec_bind hcap fun sl hsl => ?_
  refine WP.spec_bind hsl fun c hct => ?_
  unfold faults.send_fault_ipc
  refine WP.spec_bind (Pₘ := fun r : Bool × S × A => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1 ∧
      FootT st Kp Nd T Cs Sg Scs Z (EH H) s r.2.1) ?_ ?_
  · split
    all_goals first | exact (WP.spec_ok _).2 ⟨h, FootT.refl s⟩ | skip
    rename_i p bd x y g gr
    have hpH := hct.1 p bd x y g gr rfl
    have q0 := h.1.choose_spec.choose_spec
    refine WP.spec_bind (WP.spec_and (WP.spec_and (faults.set_fault.blk s t _ h ht hU0 hc)
      (faults.set_fault.kwN (Cs := Cs) (Sg := Sg) (Kp := Kp) (Nd := Nd) (Scs := Scs) (Z := Z) (Es := EH H) s t _
        q0.tcbs q0.nodes q0.cur ht))
      (WP.spec_and (faults.set_fault.kwB (Cs := Cs) (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s t _ q0.tcbs ht)
        (faults.set_fault.ftmo s t b (q0.tcbs t ht)))) ?_
    rintro s1 ⟨⟨⟨h1, -, hc1⟩, F1⟩, B1, ft1⟩
    have T1 : FootT st Kp Nd T Cs Sg Scs Z (EH H) s s1 := FootT.of_db F1.d B1.d
    obtain ⟨⟨Q1, R1, q1⟩, hB1, hX1, hS1, hSg1⟩ := h1
    have hKB1 : ∀ y ∈ Kp, ¬ Blocked (L.mem s1 (stA y)) := fun y hy => by
      rw [IpcFootN.stK (Ω := Ω) (U := (∅ : Set U64)) (Es := EH H) (FootN.ipc F1) q0.tcbs (hKT y hy) hy]
      exact hKB y hy
    refine WP.spec_bind (WP.spec_and
      (endpoint.send_ipc.ipcTmo hA s1 a true false bd g gr false t p Q1 R1 q1 hB1 hX1 hS1 hSg1 hc1
        (fun e => by cases e) hpH ft1)
      (endpoint.send_ipc.frTmo (Kp := Kp) (Nd := Nd) hA s1 a true false bd g gr false t p Q1 R1 q1 hB1 hX1 hS1
        hSg1 hc1 (fun e => by cases e) hpH ft1 rfl hKt hKB1 (fun e => by cases e) (F1.out hKa)
        (FootT st Kp Nd T Cs Sg Scs Z (EH H) s1) (fun _ _ p fn fb => p.trans (FootT.of_db fn fb)) (FootT.refl s1)
        (fun _ _ p w => p.trans (FootT.of_xw w)))) ?_
    rintro ⟨s2, a1⟩ h2
    simp only [WP.uncurry'_pair] at h2
    exact (WP.spec_ok _).2 ⟨h2.1, T1.trans h2.2⟩
  · rintro ⟨x, s2, a2⟩ h2
    exact (WP.spec_ok _).2 h2

end

end Fl4Proofs.P1
