/-
P1 (aarch64, gen 35): **the idle-thread word across the Zombie loop's steps** — the fact the gen-34 loop could not
carry (§38): a thread cap inside a covered slot is finalised (final) only if the thread is not the idle thread *at
that state*, and the idle word `IDLE_THREAD` (node offset 8, layout.rs:100) is a node word inside every `KW` /
`KWc` footprint (their node clause leaves out offset 88 only). FL4 writes `IDLE_THREAD` only at boot
(boot.rs:695; arch/aarch64/vcpu.rs:1410 is in its test module); no finaliser writes it.

**Why not a `FootCfg` instance.** `KWc`'s node clause is fixed (`o ≠ 88`) and `FootCfg` has no node-offset field;
adding one would change an existing statement (QueueFootCfg). Instead each function proves its *exact node frame*
for offset 8 directly — `L.idleW s' = L.idleW s` — from the per-step frames the existing proofs already carry
(`Fr.idle`, `KeepT.idleW`, `CaiFr.idle`, `UbF.idle`, `ANI`, `frame_bx`, `unblock_sporadic.all`,
`reschedule_required.schX`, `reply_remove.blk`, `WritesIn.dbg_idle`) and two write lemmas:

* `idleW_wr_fld` (a TCB field write), QueueFinal's `idleW_wr_out` (a word outside TCBs / nodes);
* the notification finaliser: `schedcontext.unbind_ntfn.idl`, `maybe_unbind_ntfn.idl`,
  `notification.unbind_maybe_notification.idl`, `cas_round.idl`, `cancel_all_signals_loop.idl`,
  `cancel_all_signals.idl`, **`fin_ntfn.idl`**; the endpoint finaliser by QueueCaiFr's `fin_endpoint.fr`;
* the reply finaliser **`fin_reply.idl`** (`reply_remove.blk`'s idle conjunct, `cancel_ipc.all`'s `KeepT`);
* the thread finaliser: **`sched.suspend.idl`** (QueueFinThr's `suspend.curR` walk with the idle word for `CurR`),
  **`finThrRest.idl`** (QueueFinThr7's `finThrRest.blk` walk; `debug_remove` by `WritesIn.dbg_idle`).

No named premise; new definitions and theorems only.
-/
import Fl4ProofsA64.P1.QueueZombieN
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-! ## Write lemmas -/

/-- A TCB field write keeps the idle-thread word. -/
theorem idleW_wr_fld {s : S} {y K v : U64} (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s)) (hy : y ∈ T)
    (hK : K.val < 4096) (hK8 : K.val % 8 = 0) :
    L.idleW (L.wr s (core.num.U64.wrapping_add y K) v) = L.idleW s := by
  unfold LawfulStore.idleW; rw [nodeAt_wr, L.cpu_wr]
  exact L.mem_wr_ne (field_aligned (hT y hy) hK hK8) (nodeAt_aligned hN (by rw [idle8]; omega) (by rw [idle8]))
    (fun e => node_ne_field hN (by rw [idle8]; omega) hy (hT y hy) hK (UScalar.eq_of_val_eq e).symm)

/-! ## The notification finaliser -/

theorem schedcontext.unbind_ntfn.idl (s : S) (c : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hc : c ≠ 0#u64 → c ∈ Scs) :
    schedcontext.unbind_ntfn st s c ⦃ s' => L.idleW s' = L.idleW s ⦄ := by
  unfold schedcontext.unbind_ntfn
  step with obj.Sc.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 rfl
  rename_i hb
  have hc0 : c ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
  have hcS : c ∈ Scs := hc hc0
  step with obj.Sc.ntfn.val as ⟨j, ej⟩
  split
  · rename_i hj
    have hjN : j ∈ Nt := by rw [ej]; exact h.2.2.1.2.2.scn c hcS (by rw [← ej]; simpa using hj)
    refine WP.spec_bind (obj.Ntfn.set_sc.wr s j 0#u64) fun s1 e1 => ?_
    subst e1
    have h1 := (ntsc_zero_all h hjN).1
    refine WP.spec_mono (obj.Sc.set_ntfn.wr _ c 0#u64) fun s2 e2 => ?_
    subst e2
    have hO := h.2.2.1.1
    have h0 := h.1.choose_spec.choose_spec
    have hm : scNtfnA c ∈ Ω := h.2.2.2.2.sub _ (hO.snW c hcS)
    have hmj : ntfnScA j ∈ Ω := h.2.2.2.2.sub _ (hO.ntW j hjN)
    have q1 := h1.1.choose_spec.choose_spec
    exact (idleW_wr_out q1 hm).trans (idleW_wr_out h0 hmj)
  · exact (WP.spec_ok _).2 rfl

theorem schedcontext.maybe_unbind_ntfn.idl (s : S) (n : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hn : n ∈ Nt) :
    schedcontext.maybe_unbind_ntfn st s n ⦃ s' => L.idleW s' = L.idleW s ⦄ := by
  unfold schedcontext.maybe_unbind_ntfn
  step with obj.Ntfn.sc.val as ⟨i, ei⟩
  step with obj.Sc.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 rfl
  · exact schedcontext.unbind_ntfn.idl s i h fun h0 => by
      rw [ei]; exact (h.2.2.1.2.2.nsc n hn (by rw [← ei]; exact h0)).1

theorem notification.unbind_maybe_notification.idl (s : S) (n : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hn : n ∈ Nt) :
    notification.unbind_maybe_notification st s n ⦃ s' => L.idleW s' = L.idleW s ⦄ := by
  unfold notification.unbind_maybe_notification
  refine WP.spec_bind (obj.Ntfn.bound_tcb.val s n) fun i ei => ?_
  refine WP.spec_bind (obj.Tcb.is_null.spec i) fun b eb => ?_
  subst eb
  split
  · exact (WP.spec_ok _).2 rfl
  · rename_i hb
    have hiT : i ∈ T := by
      rcases (show Tz T i by rw [ei]; exact h.2.2.1.2.2.ntb n hn) with e | e
      · exact absurd (by simp [e]) hb
      · exact e
    have h0 := h.1.choose_spec.choose_spec
    have hT := h0.tcbs
    have hm : ntfnBtA n ∈ Sg := (h.2.2.1.1.ntB n hn).2
    have hmO : ntfnBtA n ∈ Ω := h.2.2.2.2.sub _ hm
    refine WP.spec_bind (obj.Ntfn.set_bound_tcb.wr s n 0#u64) fun s1 e1 => ?_
    subst e1
    have q1 := (ntbt_all h hn Tz.zero).1.choose_spec.choose_spec
    refine WP.spec_mono (obj.Tcb.set_bound_ntfn.wr _ i 0#u64) fun s2 e2 => ?_
    subst e2
    have hN1 := q1.nodes _ q1.cur
    exact (idleW_wr_fld (K := 3368#u64) hT hN1 hiT (by simp) (by simp)).trans (idleW_wr_out h0 hmO)

theorem cas_round.idl {β : Type _} (s : S) (n t : U64) (fuel1 : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hH : H n = some .ntfn) (hst : L.epState s n = 1#u64) (hhd : (L.epQ s n).head = t) :
    (do
      let next ← tcbqueue.next_of st s .Ep t
      let s1 ← notification.ntfn_dequeue st s n t
      let s2 ← sched.set_thread_state st s1 t sched.TS_RESTART
      let s3 ← notification.unblock_sporadic st s2 t
      let s4 ← sched.possible_switch_to st s3 t
      ok (ControlFlow.cont (β := β) (s4, next, fuel1))) ⦃ r => ∃ s4 next, r = .cont (s4, next, fuel1) ∧
        L.idleW s4 = L.idleW s ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hT := h0.tcbs
  obtain ⟨hdT, hbe, hds⟩ := ntfn_head h0 hH hst
  rw [hhd] at hdT hbe hds
  have hta := hT t hdT
  obtain ⟨E, EQ, hEW⟩ := h0.eps
  have heE : n ∈ E := (hEW.2.2.2.2.2.2.2.1 n).2 (Or.inr hH)
  obtain ⟨hE, -, hq⟩ := hEW.1 n heE
  have hne : EQ n ≠ [] := fun h0' => ((hEW.2.2.2.2.2.2.2.2.2.2 n heE h0').2 hH) hst
  obtain ⟨y, ys, hys⟩ := List.exists_cons_of_ne_nil hne
  have hy : y = t := by rw [← hhd, hq.head, hys]; rfl
  subst hy
  rw [hys] at hq
  have hnext := hq.head_next
  have hbl : Blocked (L.mem s (stA y)) := by rw [hds]; exact Or.inr (Or.inr rfl)
  obtain ⟨dq, dr, da⟩ := blocked_out h0 hdT (not_runnable_of_blocked hbl)
  have hyA := hB.sact y hdT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hbl))))))
  unfold tcbqueue.next_of
  step with tcbqueue.next.spec as ⟨next, enext⟩
  have hdq := notification.ntfn_dequeue.inv s y Q R h0 hdT (by simp) hbl
  rw [hbe] at hdq
  refine WP.spec_bind (WP.spec_and hdq (WP.spec_and (notification.ntfn_dequeue.rel s n y _ hT hE hq
    List.mem_cons_self) (notification.ntfn_dequeue.foot s n y _ hT hE hq List.mem_cons_self))) ?_
  rintro s1 ⟨⟨h1, f1, o1, n1, k1, c1, nc1⟩, ⟨hq1, hst1⟩, w1⟩
  have hnd := hq.nodup
  have herase : (y :: ys).erase y = ys := List.erase_cons_head y ys
  rw [herase] at hq1 hst1
  have tm1 : TmFr st T Cs Nt s s1 := TmFr.mk0 ⟨k1, fun y hy K a b c => f1 y hy K (by omega) c (by omega) (by omega),
    fun c hc o ho => nc1 c hc o (by omega) (by omega), fun n' hn' => o1 _ (hSg.sub _ (hX.1.ntB n' hn').2)⟩
  obtain ⟨hB1, hX1, hS1, hSg1, -, -, ei1⟩ := frame_bx h0 hB hX hS hSg f1 o1 n1 k1 tm1
  have st1 : L.mem s1 (stA y) = sched.TS_BLOCKED_ON_NTFN := by
    rw [stA_eq, f1 y hdT _ (by simp) (by simp) (by simp) (by simp), ← stA_eq]; exact hds
  have iq1 : L.mem s1 (inqA y) = L.mem s (inqA y) := by
    rw [inqA_eq]; exact f1 y hdT _ (by simp) (by simp) (by simp) (by simp)
  have fw1 : Foot st T Cs Sg Scs Z {n} s s1 := Foot.of w1 fun b hb => hb.kw hq.mem rfl
  obtain ⟨-, -, r3, -, r6⟩ := ts_vals
  refine WP.spec_bind (WP.spec_and (sts_all s1 y _ Q R h1 hB1 hX1 hS1 hSg1 hdT not_blocked_restart restart_ne
    (Or.inl (Or.inr rfl)) (hX1.noref hta (by rw [st1]; exact blocked_ne_reply (Or.inr (Or.inr rfl)))
      (by rw [st1, r3, r6]; decide))
    ⟨fun _ _ _ _ _ => runnable_restart, fun _ _ _ => runnable_restart, fun _ => runnable_restart⟩)
    (sched.set_thread_state.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) s1 y _ h1 hdT)) ?_
  rintro s2 ⟨⟨h2, hB2, hX2, hS2, hSg2, st2, k2⟩, fw2⟩
  have h2' : SchedQueuesInv st T Cs Ω H s2 Q R := h2.congrX empty_congr'
  refine WP.spec_bind (endpoint.unblock_sporadic.all s2 y h2' hB2 hX2 hS2 hSg2 hdT) ?_
  rintro s3 ⟨h3, hB3, hX3, hS3, hSg3, -, -, i3, fk3, -⟩
  have st3 : L.mem s3 (stA y) = sched.TS_RESTART := by
    rw [stA_eq, fk3 y hdT _ (by simp) (by simp), ← stA_eq]; exact st2
  have esc3 : L.mem s3 (scA y) = L.mem s (scA y) := by
    rw [scA_eq, fk3 y hdT _ (by simp) (by simp), ← scA_eq, k2.scf hdT, scA_eq,
      f1 y hdT _ (by simp) (by simp) (by simp) (by simp)]
  refine WP.spec_bind (WP.spec_and (sched.possible_switch_to.sch (Sg := Sg) s3 y Q R h3 hB3 hSg3 hdT
    (by rw [st3]; exact runnable_restart) (by rw [esc3]; exact hyA))
    (sched.possible_switch_to.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) s3 y h3 hdT)) ?_
  rintro s4 ⟨⟨p4, -, -⟩, -⟩
  exact (WP.spec_ok _).2 ⟨s4, next, rfl, p4.fr.idle.trans (i3.trans (k2.idleW.trans ei1))⟩

theorem notification.cancel_all_signals_loop.idl (s0 s : S) (n t fuel : U64)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hH : H n = some .ntfn) (hf : L.idleW s = L.idleW s0)
    (ht : t ≠ 0#u64 → L.epState s n = 1#u64 ∧ (L.epQ s n).head = t) :
    notification.cancel_all_signals_loop st s n t fuel ⦃ s' => L.idleW s' = L.idleW s0 ⦄ := by
  unfold notification.cancel_all_signals_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.2.val)
    (inv := fun x => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac x.1 ∧ L.idleW x.1 = L.idleW s0 ∧
      (x.2.1 ≠ 0#u64 → L.epState x.1 n = 1#u64 ∧ (L.epQ x.1 n).head = x.2.1))
  · rintro ⟨s1, t1, f1⟩ ⟨hb1, hf1, ht1⟩
    simp only at hb1 hf1 ht1
    unfold notification.cancel_all_signals_loop.body
    step with obj.Tcb.is_null.spec as ⟨b, eb⟩
    split
    · exact (WP.spec_ok _).2 hf1
    rename_i hb
    have ht0 : t1 ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    obtain ⟨hst1, hhd1⟩ := ht1 ht0
    split
    · rename_i hfuel
      step as ⟨fuel1, efuel⟩
      refine WP.spec_mono (WP.spec_and (cas_round (β := S) s1 n t1 fuel1 hb1 hH hst1 hhd1)
        (cas_round.idl (β := S) s1 n t1 fuel1 hb1 hH hst1 hhd1)) ?_
      rintro r ⟨⟨s4, next, rfl, hb4, -, hn4⟩, ⟨s4', next', e', hc4⟩⟩
      simp only [ControlFlow.cont.injEq, Prod.mk.injEq] at e'
      obtain ⟨rfl, rfl, -⟩ := e'
      exact ⟨hb4, hc4.trans hf1, hn4, by simp only; omega⟩
    · exact (WP.spec_ok _).2 hf1
  · exact ⟨h, hf, ht⟩

theorem notification.cancel_all_signals.idl (s : S) (n : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hH : H n = some .ntfn) :
    notification.cancel_all_signals st s n ⦃ s' => L.idleW s' = L.idleW s ⦄ := by
  unfold notification.cancel_all_signals
  step with obj.Ntfn.state.spec as ⟨v, hv⟩
  split
  · exact (WP.spec_ok _).2 rfl
  rename_i hw
  have hst : L.epState s n = 1#u64 := by
    rw [← hv]; have := hw; simp [obj.NTFN_WAITING] at this; exact UScalar.eq_of_val_eq (by simpa using this)
  step with notification.get_queue.spec as ⟨q, eq⟩
  subst eq
  refine WP.spec_bind (WP.spec_and (notification.cancel_all_signals_loop.blk s s n _ _ h hH (Foot.refl _)
    (fun _ => ⟨hst, rfl⟩)) (notification.cancel_all_signals_loop.idl s s n _ _ h hH rfl
    (fun _ => ⟨hst, rfl⟩))) ?_
  rintro s1 ⟨⟨h1, -⟩, c1⟩
  obtain ⟨⟨Q1, R1, q1⟩, hB1, hX1, hS1, hSg1⟩ := h1
  refine WP.spec_mono (sched.reschedule_required.schX s1 Q1 R1 q1 hB1 hSg1)
    fun s2 ⟨_, _, _, _, _, _, i2, _⟩ => ?_
  exact i2.trans c1

/-- **The notification finaliser keeps the idle-thread word** (any finality). -/
theorem fin_ntfn.idl {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (n b0 : U64) (b1 b2 : Bool)
    (fin : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hn : n ∈ Nt) (hH : H n = some .ntfn) :
    objects.finalise_cap_object st ar s a (.Notification n b0 b1 b2) fin ⦃ r => L.idleW r.2.1 = L.idleW s ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  split
  · refine WP.spec_bind (WP.spec_and (schedcontext.maybe_unbind_ntfn.blk s n h hn)
      (schedcontext.maybe_unbind_ntfn.idl s n h hn)) fun s1 ⟨⟨h1, _⟩, i1⟩ => ?_
    refine WP.spec_bind (WP.spec_and (notification.unbind_maybe_notification.blkF s1 n h1 hn)
      (notification.unbind_maybe_notification.idl s1 n h1 hn)) fun s2 ⟨⟨h2, _⟩, i2⟩ => ?_
    refine WP.spec_bind (notification.cancel_all_signals.idl s2 n h2 hH) fun s3 i3 => ?_
    exact (WP.spec_ok _).2 (i3.trans (i2.trans i1))
  · exact (WP.spec_ok _).2 rfl

/-! ## The reply finaliser -/

/-- **The reply finaliser keeps the idle-thread word** (QueueReplyPop's `fin_reply.blk` walk). -/
theorem fin_reply.idl {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (p : U64)
    (x : Bool) (fin : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hp : p ∈ Rp)
    (hRV : RunVcpuInv st T s) :
    objects.finalise_cap_object st ar s a (.Reply p x) fin ⦃ r => L.idleW r.2.1 = L.idleW s ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  split
  swap
  · exact (WP.spec_ok _).2 rfl
  refine WP.spec_bind (obj.Reply.tcb.blk s p) fun i ei => ?_
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 rfl
  rename_i hb
  have hi0 : i ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
  have hX := h.2.2.1
  obtain ⟨-, hiT, -, -⟩ := hX.2.1.back p hp (by rw [← ei]; exact hi0)
  rw [← ei] at hiT
  step with obj.Tcb.state.spec as ⟨v, ev⟩
  split
  · rename_i hv
    refine WP.spec_bind (ipc.reply_remove.blk (Es := EH H) hA s a p i h hp hiT ei.symm (by rw [← ev, hv]) hRV) ?_
    rintro ⟨s1, a1⟩ ⟨-, -, -, -, i1⟩
    exact (WP.spec_ok _).2 i1
  split
  · obtain ⟨⟨Q, R, h0⟩, hB, -, hS, hSg⟩ := h
    refine WP.spec_bind (ipc.cancel_ipc.all s a i Q R h0 hiT hB hX hSg.sub) ?_
    rintro ⟨s1, a1⟩ ⟨-, -, -, -, -, -, k1, -⟩
    exact (WP.spec_ok _).2 k1.idleW
  · exact (WP.spec_ok _).2 rfl

/-! ## The thread finaliser -/

/-- **`suspend` keeps the idle-thread word** (QueueFinThr's `suspend.curR` walk). -/
theorem sched.suspend.idl {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (t : obj.Tcb)
    (Q : U64 → U64 → List U64) (R : U64 → List U64) (h : SchedQueuesInv st T Cs Ω H s Q R) (ht : t ∈ T)
    (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hSg : SgOK st Ω Sg s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hna : L.actionW s ≠ t)
    (hyield : L.mem s (yieldA t) ≠ 0#u64 → L.mem s (yieldA t) ∈ Scs)
    (hrv : L.mem s (runVcpuA t) = 0#u64) :  -- a64: `t` runs no VCPU (as `sched.suspend.blk`)
    sched.suspend st ar s a t ⦃ s' _ => L.idleW s' = L.idleW s ⦄ := by
  have hT := h.tcbs
  have hta := hT t ht
  have hsub := hSg.sub
  -- a64: x86_64 rewrites with SyscallGen's `suspend_eq_old`; here `cancel_run` is stepped over (`hrv`).
  unfold sched.suspend
  refine WP.spec_bind (vcpu.cancel_run.idle s a t hrv) ?_
  rintro ⟨s0, a0⟩ ⟨e0, e1⟩
  subst s0; subst a0
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (ipc.cancel_ipc.all s a t Q R h ht hB hX hsub) ?_
  rintro ⟨s1, a1⟩ ⟨h1, hB1, hX1, nb1, nr1, hst1, k1, -⟩
  try simp only [WP.uncurry'_pair]
  have c1 : L.idleW s1 = L.idleW s := k1.idleW
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
      L.mem s2 (stA t) ≠ sched.TS_BLOCKED_ON_REPLY ∧ TmFr st T Cs Nt s s2 ∧ L.idleW s2 = L.idleW s) ?_ ?_
  · split
    · step with obj.Tcb.reg.spec as ⟨ip⟩
      refine WP.spec_mono (obj.Tcb.set_reg.fault_ip s1 t ip hta) fun s2 e => ?_
      subst e
      obtain ⟨h2, f2, a2⟩ := field_wr_keep (K := 528#u64) (v := ip) h1 ht (by simp) (by simp) (by simp)
      obtain ⟨hB2, hX2⟩ := bx_field (K := 528#u64) (v := ip) h1 hB1 hX1 hsub ht (by simp) (by simp) (by simp) (by simp)
      refine ⟨h2, ?_, by rw [a2]; exact na1, by rw [← y1]; exact f2 _ (by simp) (by simp) (by simp), hB2, hX2,
        ⟨hSg.sub, fun b hb => by rw [L.ksb_wr]; exact hSg1.ks b hb, fun o h1' h2' => by
          rw [L.ksb_wr]; exact hSg1.ksΩ o h1' h2'⟩, SCsOK.field (K := 528#u64) h1 hS1 hX1 ht (by simp) (by simp) (by simp), ?_,
        tm1.trans (TmFr.wr hT h1.nodes hX1.1 (field_aligned hta (by simp) (by simp))
          (notTmW_field hT h1.nodes (fun n hn => h1.omega _ (hsub _ (hX1.1.ntB n hn).2)) ht (by simp) (by simp))),
        (idleW_wr_fld (K := 528#u64) hT (h1.nodes _ h1.cur) ht (by simp) (by simp)).trans c1⟩
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
  have c3 : L.idleW s3 = L.idleW s := by
    obtain ⟨fr3', -, -, -, -⟩ := qfoot_keep h2 hSg2 hW2 hc2 ht p128 hw3
    exact fr3'.idle.trans c2
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
  have c4 : L.idleW s4 = L.idleW s := by
    obtain ⟨fr4', -, -, -, -⟩ := qfoot_keep h3 hSg3 hW3 hc3 ht prel hw4
    exact fr4'.idle.trans c3
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
      SCsOK st T Ω Sg Scs Z Ac s5 ∧ TmFr st T Cs Nt s4 s5 ∧ L.idleW s5 = L.idleW s4) ?_ ?_
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
        (idleW_wr_fld (K := 3472#u64) hT (h5.nodes _ h5.cur) ht (by simp) (by simp)).trans (idleW_wr_out h4 hyΩ)⟩
      rw [stA_eq, show yieldA t = core.num.U64.wrapping_add t 3472#u64 from rfl,
        f6 _ (by simp) (by simp) (by simp), ← stA_eq, e5 t ht]
    · exact (WP.spec_ok _).2 ⟨h4, rfl, rfl, hB4, hX4, rfl, hS4, TmFr.refl (L := L) _, rfl⟩
  rintro s5 ⟨h5, st5, a5, hB5, hX5, k5, hS5, tm5, c5⟩
  have hnr5 : ¬ Blocked (L.mem s5 (stA t)) := by rw [st5, st4]; exact nb2
  have hrp5 : L.mem s5 (stA t) ≠ sched.TS_BLOCKED_ON_REPLY := by rw [st5, st4]; exact nr2
  refine WP.spec_bind (WP.spec_and (sched.set_thread_state.inv s5 t _ Q3 R4 h5 ht not_blocked_inactive (Or.inr hnr5)
    ⟨fun c hc p hp hm => absurd hm (nQ3 c hc p hp), fun c hc hm => absurd hm (nR4 c hc),
     fun e => absurd e (by rw [a5]; exact na4)⟩) (sched.set_thread_state.state s5 t _ Q3 R4 h5 ht hX5.1 hsub)) ?_
  rintro s6 ⟨h6, e6, k6⟩
  simp only [WP.spec_ok, WP.uncurry'_pair]
  exact k6.idleW.trans (c5.trans c4)

/-- **The thread finaliser after `detach` keeps the idle-thread word** (QueueFinThr7's `finThrRest.blk` walk). -/
theorem finThrRest.idl {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s1 : S) (a1 : A) (p : U64)
    (h1 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s1) (hp : p ∈ T) (hna : L.actionW s1 ≠ p)
    (hidle : L.idleW s1 ≠ p) (rv1 : L.mem s1 (runVcpuA p) = 0#u64) :
    finThrRest st ar s1 a1 p ⦃ r => L.idleW r.2.1 = L.idleW s1 ⦄ := by
  unfold finThrRest
  refine WP.spec_bind (WP.spec_and (notification.unbind_notification.blkF s1 p h1 hp)
    (notification.unbind_notification.rvst s1 p h1 hp)) fun s2 hh2 => ?_
  obtain ⟨⟨h2, f2, n2⟩, r2⟩ := hh2
  refine WP.spec_bind (timer.remove.tf (s0 := s2) s2 p (TF.start h2) hp) fun s3 ⟨h3, f3, n3, k3, _⟩ => ?_
  have rv3 : L.mem s3 (runVcpuA p) = 0#u64 :=
    (k3 p hp 3672#u64 (by simp) (by simp) (Or.inr (by simp))).trans ((r2 p hp).2.trans rv1)
  have ea3 : L.actionW s3 = L.actionW s1 := by rw [n3.1, n2.1]
  have ei3 : L.idleW s3 = L.idleW s1 := by rw [n3.2.1, n2.2.1]
  step with obj.Tcb.sc.spec as ⟨i, ei⟩
  step with obj.Sc.is_null.spec as ⟨b, eb⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧
      L.idleW r.1 = L.idleW s1 ∧ L.actionW r.1 ≠ p ∧ L.mem r.1 (runVcpuA p) = 0#u64) ?_ ?_
  · split
    · exact (WP.spec_ok _).2 ⟨h3, ei3, by rw [ea3]; exact hna, rv3⟩
    rename_i hb
    have hi0 : i ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    obtain ⟨hiS, hit, -⟩ := h3.2.2.1.2.2.bound p hp (by rw [← ei]; exact hi0)
    rw [← ei] at hiS hit
    refine WP.spec_bind (schedcontext.unbind_tcb.blkR s3 i h3 hiS hi0 (fun _ => by rw [hit, ea3]; exact hna)
      (fun _ => by rw [hit, ei3]; exact hidle)) fun s5 hh5 => ?_
    obtain ⟨h5, -, ea5, i5, -, -, r5⟩ := hh5
    have rv5 : L.mem s5 (runVcpuA p) = 0#u64 := (r5 p hp).2.trans rv3
    have na5 : L.actionW s5 ≠ p := by
      rcases ea5 with e | e
      · rw [e, ea3]; exact hna
      · rw [e]; exact fun e' => notT_small h5.1.choose_spec.choose_spec.tcbs (by simp) (e' ▸ hp)
    step with obj.Sc.yield_from.val as ⟨y, ey⟩
    step with obj.Tcb.is_null.spec as ⟨b1, eb1⟩
    split
    · exact (WP.spec_ok _).2 ⟨h5, i5.trans ei3, na5, rv5⟩
    · have hiS5 : i ∈ Scs := hiS
      have hyy : y ≠ 0#u64 → y ∈ T := fun hy0 => by
        rw [ey]; exact h5.2.2.1.2.2.yt.2.2 i hiS5 (by rw [← ey]; exact hy0)
      refine WP.spec_mono (WP.spec_and (schedcontext.complete_yield_to.blk hA s5 a1 y h5 hyy)
        (schedcontext.complete_yield_to.rvst hA s5 a1 y h5 hyy)) ?_
      rintro ⟨s6, a6⟩ ⟨⟨h6, -, n6⟩, r6⟩
      exact ⟨h6, n6.2.1.trans (i5.trans ei3), by rw [n6.1]; exact na5, (r6 p hp).2.trans rv5⟩
  rintro ⟨s4, a2⟩ ⟨h4, i4, na4, rv4⟩
  try simp only [WP.uncurry'_pair]
  obtain ⟨⟨Q, R, q4⟩, hB4, hX4, hS4, hSg4⟩ := id h4
  refine WP.spec_bind (WP.spec_and (sched.suspend.blk s4 a2 p h4 hp na4 rv4)
    (sched.suspend.idl s4 a2 p Q R q4 hp hB4 hX4 hSg4 hS4 na4 (hX4.2.2.yt.2.1 p hp) rv4)) ?_
  rintro ⟨s5, a3⟩ ⟨⟨h5, -⟩, i5⟩
  try simp only [WP.uncurry'_pair]
  have q5 := h5.1.choose_spec.choose_spec
  refine WP.spec_bind (objects.debug_remove.x (X := ∅) s5 p h5 hp) fun s6 hr6 => ?_
  have i6 : L.idleW s6 = L.idleW s5 := WritesIn.dbg_idle q5.tcbs q5.nodes q5.cur hr6.2.2
  refine WP.spec_bind (hA.fpu_release a3 p) fun a4 _ => ?_
  refine WP.spec_bind (P0.obj.Tcb.slot.p0 p _) fun s7 _ => ?_
  exact (WP.spec_ok _).2 (i6.trans (i5.trans i4))

end

end Fl4ProofsA64.P1
