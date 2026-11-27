/-
P1 (jc6d7, TIMER-RB-PLAN §12 step 1): `notification.send_signal` leaves the timer words alone (`TmFr`, hence
`TAgree`), on every branch, #63's `RunningVM` paths included; so `timer::fire` keeps `TimerRB` with no
premise on `send_signal` (`timer.fire.rb'`, beside `timer.fire.rb`).  The frame needs `TInv` at the signal
(the notification and its bound TCB are typed objects), so `fire`'s loop carries `TimerRB ∧ TInv`.
-/
import Fl4Proofs.P1.TimerRBFire
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}

/-- A write of a TCB word below the timer fields keeps `TmFr`. -/
theorem TmFr.reg {s : S} {y K v : U64} (hT : TcbPlaced T) (hN : ∀ c ∈ Cs, NodePlaced st T s c)
    (hΩ : ∀ n ∈ Nt, OutsideObjs st T Cs s (ntfnBtA n)) (hy : y ∈ T) (hK : K.val < 3528) (h8 : K.val % 8 = 0) :
    TmFr st T Cs Nt s (L.wr s (core.num.U64.wrapping_add y K) v) := by
  have hya := hT y hy
  have ha : Aligned (core.num.U64.wrapping_add y K) := field_aligned hya (by omega) h8
  refine TmFr.mk0 ⟨L.ksb_wr _ _ _, fun y' hy' K' h1 h2 h3 => ?_, fun c hc o ho => ?_,
    fun n hn => L.mem_wr_ne ha (hΩ n hn).1 (out_ne_field (hΩ n hn) hy hya (by omega))⟩
  · exact L.mem_wr_ne ha (field_aligned (hT y' hy') (by omega) h3)
      (fun e => field_ne hya (hT y' hy') (by omega) (by omega) (fun _ => by omega) (UScalar.eq_of_val_eq e))
  · exact L.mem_wr_ne ha (nodeAt_aligned (hN c hc) (by omega) (by omega))
      (fun e => node_ne_field (hN c hc) (by omega) hy hya (by omega) (UScalar.eq_of_val_eq e).symm)

theorem BlkOK.ntOut {s : S} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    ∀ n ∈ Nt, OutsideObjs st T Cs s (ntfnBtA n) := by
  obtain ⟨⟨Q, R, h0⟩, -, hX, -, hSg⟩ := h
  exact fun n hn => h0.omega _ (hSg.sub _ (hX.1.ntB n hn).2)

/-- `set_reg` with its timer frame. -/
theorem obj.Tcb.set_reg.tm (s : S) {t r v : U64} (hr : r.val < 384) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (ht : t ∈ T) :
    obj.Tcb.set_reg st t s r v ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      L.mem s' (stA t) = L.mem s (stA t) ∧ TmFr st T Cs Nt s s' ⦄ := by
  have hΩ := h.ntOut
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  refine WP.spec_mono (obj.Tcb.set_reg.wrS s t r v (h0.tcbs t ht) hr) ?_
  rintro s1 ⟨K, hK, rfl⟩
  obtain ⟨b, e⟩ := reg_all (v := v) h0 hB hX hS hSg ht (K := K) (by omega) (by omega)
  exact ⟨b, e, TmFr.reg h0.tcbs h0.nodes hΩ ht (by omega) (by omega)⟩

/-- `set_mr` (first three message registers) with its timer frame. -/
theorem msg.set_mr.tm (s : S) {t buf i v : U64} (hi : i.val < 3) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (ht : t ∈ T) :
    msg.set_mr st s t buf i v ⦃ r => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2 ∧ L.mem r.2 (stA t) = L.mem s (stA t) ∧
      TmFr st T Cs Nt s r.2 ⦄ := by
  unfold msg.set_mr
  have hlt : i < msg.N_MSG_REGISTERS := by simp only [msg.N_MSG_REGISTERS]; scalar_tac
  rw [if_pos hlt]
  refine WP.spec_bind (Pₘ := fun r => r.val < 384) ?_ fun r hr => ?_
  · unfold msg.msg_register
    split
    · exact (WP.spec_ok _).2 (by simp [layout.reg.R10])
    split
    · exact (WP.spec_ok _).2 (by simp [layout.reg.R8])
    split
    · exact (WP.spec_ok _).2 (by simp [layout.reg.R9])
    · exact (WP.spec_ok _).2 (by simp [layout.reg.R15])
  refine WP.spec_bind (obj.Tcb.set_reg.tm s hr h ht) fun s1 h1 => ?_
  simp only [lift, bind_ok]
  exact (WP.spec_ok _).2 h1

set_option maxHeartbeats 4000000 in
/-- `vcpu.report.blk` with the timer frame (int6: from `vcpu.report.xf`). -/
theorem vcpu.report.tm {U : Set U64} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (t badge : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T)
    (hvm : L.mem s (stA t) = sched.TS_RUNNING_VM)
    (hc : L.mem s (core.num.U64.wrapping_add t 3664#u64) ≠ 0#u64 →
      L.mem s (core.num.U64.wrapping_add (L.mem s (core.num.U64.wrapping_add t 3664#u64)) vcpu.PENDING) = 0#u64)
    (hU : ∀ b ∈ U, UsrW st T Cs H Sg Scs Z s b) (hbuf : msg.lookup_ipc_buffer st s true t ⦃ b => BufOK U b ⦄) :
    vcpu.report st ar s a t badge ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      L.mem s' (stA t) = sched.TS_RUNNING ∧ TmFr st T Cs Nt s s' ⦄ := by
  refine WP.spec_mono (vcpu.report.xf hA s a t badge h ht hvm hc hU hbuf) ?_
  rintro s' ⟨s5, h5, st5, w5, e⟩
  have tm5 := RepW.tmfr h hU ht w5
  obtain ⟨⟨Q5, R5, q5⟩, hB5, hX5, hS5, hSg5⟩ := h5
  have hst := sts_all s5 t _ Q5 R5 q5 hB5 hX5 hS5 hSg5 ht not_blocked_running running_ne
    (Or.inr (by rw [st5]; exact not_blocked_vm))
    (hX5.noref (q5.tcbs t ht) (by rw [st5]; exact runnable_ne_reply (Or.inr (Or.inr rfl)))
      (by rw [st5]; exact runnable_ne_recv (Or.inr (Or.inr rfl))))
    ⟨fun _ _ _ _ _ => runnable_running, fun _ _ _ => runnable_running, fun _ => runnable_running⟩
  rw [e, WP.spec_ok] at hst
  obtain ⟨q6, hB6, hX6, hS6, hSg6, st6, k6⟩ := hst
  exact ⟨⟨⟨Q5, R5, q6.congrX empty_congr⟩, hB6, hX6, hS6, hSg6⟩, st6, tm5.trans (TmFr.of_keepT k6)⟩

/-- `remote_tcb_stall` writes at most the current core's `IPI_PENDING` word. -/
theorem smp.remote_tcb_stall.tm {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (t : obj.Tcb) {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hSg : SgOK st Ω Sg s) :
    smp.remote_tcb_stall st ar s a t ⦃ s' _ => TmFr st T Cs Nt s s' ⦄ := by
  refine WP.spec_mono (smp.remote_tcb_stall.spec hA s a t) fun r hr => ?_
  obtain ⟨s', a'⟩ := r
  simp only [WP.uncurry'_pair] at hr ⊢
  rcases hr with rfl | ⟨v, rfl⟩
  · exact TmFr.refl (L := L) _
  · have ip : layout.node.IPI_PENDING.val = 120 := by simp [layout.node.IPI_PENDING]
    exact TmFr.of_fr (fr_node (Sg := Sg) (v := v) h hSg h.cur (by rw [ip]; omega) (by rw [ip])
      (fun _ => by rw [ip]; omega) (by rw [ip]; omega) (fun _ => by rw [ip]; omega)) hX.1 h.nodes

/-- `unblock_check` writes the SC's refill ring and the current `REPROGRAM` word only. -/
theorem sporadic.unblock_check.tm {X : Set U64} (s : S) (t i : U64) {Q : U64 → U64 → List U64}
    {R : U64 → List U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R)
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (ht : t ∈ T)
    (i_post : i = L.mem s (scA t)) (hi0 : i ≠ 0#u64) (hiA : i ∈ Ac) :
    sporadic.unblock_check st s i ⦃ s' => TmFr st T Cs Nt s s' ⦄ := by
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
  exact WP.spec_mono (sporadic.unblock_check.fr hW ⟨aR, oR⟩) fun s3 w3 => TmFr.of_ring h hX hSg.sub hiS w3

/-- `signal_vm` with the timer frame. -/
theorem signal_vm.tm {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s1 : S) (a : A) (i n : U64)
    (h1 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s1) (hiT : i ∈ T) (hn : n ∈ Nt)
    (st1 : L.mem s1 (stA i) = sched.TS_RUNNING) :
    (do
      let (s2, a1) ← notification.maybe_donate_sched_context st ar s1 a i n
      let b2 ← sched.is_schedulable st s2 i
      let s3 ← if b2 = true then sched.possible_switch_to st s2 i else ok s2
      let i4 ← obj.Tcb.sc st i s3
      let b3 ← obj.Sc.is_null i4
      if b3 = true then ok (s3, a1)
      else do
        let b4 ← sporadic.sc_active st s3 i4
        if b4 = true then do
          let i5 ← obj.Ntfn.sc st n s3
          if i4 = i5 then do
            let b5 ← sporadic.sc_sporadic st s3 i4
            if b5 = true then do
              let s4 ← sched.cur_sc st s3
              let b6 ← core.cmp.PartialEq.ne.trait_default obj.Sc.Insts.CoreCmpPartialEqSc i4 s4
              if b6 = true then do
                let b7 ← sched.in_release_queue st s3 i
                if b7 = true then ok (s3, a1)
                else do
                  let s5 ← sporadic.unblock_check st s3 i4
                  ok (s5, a1)
              else ok (s3, a1)
            else ok (s3, a1)
          else ok (s3, a1)
        else ok (s3, a1)) ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ TmFr st T Cs Nt s1 s' ⦄ := by
  obtain ⟨⟨Q1, R1, q1⟩, hB1, hX1, hS1, hSg1⟩ := h1
  have hsA1 : L.mem s1 (scA i) = 0#u64 → ¬ Sch st s1 i := fun h0 hS => by
    rcases hS with e | e | e | e | ⟨e1, e2⟩ | e
    · exact hB1.q i hiT e h0
    · exact hB1.r i hiT e h0
    · exact hB1.act (by rw [e]; exact hiT) (by rw [e]; exact h0)
    · exact hB1.idle (by rw [e]; exact h0)
    · exact hB1.resume e1 (by rw [e2]; exact h0)
    · rw [st1] at e
      rcases e with e | e
      · exact not_blocked_running e
      · exact running_ne.1 e
  refine WP.spec_bind (notification.maybe_donate_sched_context.tinvB hA s1 a i n Q1 R1 q1 hB1 hX1 hS1 hSg1 hiT
    (ntfn_sc_ok hX1 hn hsA1)) ?_
  rintro ⟨s2, a1⟩ ⟨⟨⟨Q2, R2, q2⟩, hB2, hX2, hS2, hSg2⟩, tm2⟩
  try simp only [WP.uncurry'_pair]
  step with sched.is_schedulable.spec' as ⟨b2, hb2⟩
  refine WP.spec_bind (Pₘ := fun s3 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s3 ∧ TmFr st T Cs Nt s1 s3) ?_ ?_
  · split
    · rename_i hb
      refine WP.spec_mono (sched.possible_switch_to.sch s2 i Q2 R2 q2 hB2 hSg2 hiT (hb2 hb).1
        (fun _ => (hS2.act _ (hX2.2.2.bound i hiT (hb2 hb).2.1).1).2 (hb2 hb).2.2.2)) fun s3 hh => ?_
      obtain ⟨p3, -, -⟩ := hh
      exact ⟨⟨p3.inv, p3.bnd, hX2.fr p3.fr, hS2.fr p3.fr, hSg2.fr p3.fr⟩,
        tm2.trans (TmFr.of_fr p3.fr hX2.1 q2.nodes)⟩
    · exact (WP.spec_ok _).2 ⟨⟨⟨Q2, R2, q2⟩, hB2, hX2, hS2, hSg2⟩, tm2⟩
  rintro s3 ⟨⟨⟨Q3, R3, q3⟩, hB3, hX3, hS3, hSg3⟩, tm3⟩
  have ok3 : (ok (s3, a1) : Result (S × A)) ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      TmFr st T Cs Nt s1 s' ⦄ :=
    (WP.spec_ok _).2 ⟨⟨⟨Q3, R3, q3⟩, hB3, hX3, hS3, hSg3⟩, tm3⟩
  step with obj.Tcb.sc.spec as ⟨i4, ei4⟩
  step with obj.Sc.is_null.spec as ⟨b3, _hb3⟩
  refine sig_if _ _ _ _ (fun _ => ok3) (fun _ => ?_)
  refine WP.spec_bind (sporadic.sc_active.spec s3 i4) fun b4 _ => ?_
  refine sig_if _ _ _ _ (fun _ => ?_) (fun _ => ok3)
  refine WP.spec_bind (obj.Ntfn.sc.any s3 n) fun i5 _ => ?_
  refine sig_if _ _ _ _ (fun _ => ?_) (fun _ => ok3)
  step with sporadic.sc_sporadic.spec as ⟨b5, eb5⟩
  refine sig_if _ _ _ _ (fun hb5 => ?_) (fun _ => ok3)
  step with sched.cur_sc.spec as ⟨c4, _⟩
  step with sc_ne.spec as ⟨b6⟩
  refine sig_if _ _ _ _ (fun _ => ?_) (fun _ => ok3)
  refine WP.spec_bind (sched.in_release_queue.spec s3 i) fun b7 _ => ?_
  refine sig_if _ _ _ _ (fun _ => ok3) (fun _ => ?_)
  have hi4S : i4 ∈ Scs := (hX3.2.2.bound i hiT (by rw [← ei4]; exact (eb5 hb5).1)).1 |> fun h => by
    rw [← ei4] at h; exact h
  refine WP.spec_bind (WP.spec_and (sporadic.unblock_check.all s3 i i4 q3 hB3 hX3 hS3 hSg3 hiT ei4 (eb5 hb5).1
    (hS3.spor i4 hi4S (eb5 hb5).2)) (sporadic.unblock_check.tm s3 i i4 q3 hX3 hS3 hSg3 hiT ei4 (eb5 hb5).1
    (hS3.spor i4 hi4S (eb5 hb5).2))) fun s5 hh => ?_
  obtain ⟨⟨q5, hB5, hX5, hS5, hSg5, -⟩, tm5⟩ := hh
  exact (WP.spec_ok _).2 ⟨⟨⟨Q3, R3, q5⟩, hB5, hX5, hS5, hSg5⟩, tm3.trans tm5⟩

/-- `set_active` with the timer frame. -/
theorem notification.set_active.tm (s : S) (n badge : U64) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hn : n ∈ Nt) (hH : H n = some .ntfn) (hst : L.epState s n ≠ 1#u64) :
    notification.set_active st s n badge ⦃ s' => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ TmFr st T Cs Nt s s' ⦄ := by
  have hI := h
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  unfold notification.set_active
  refine WP.spec_bind (obj.Ntfn.set_state.val s n _) fun s1 e1 => ?_
  subst e1
  obtain ⟨h1, hB1, hX1, hS1, hSg1, -, -, -, -, -, tm1⟩ :=
    ntfn_state_all (w := obj.NTFN_ACTIVE) h0 hB hX hS hSg hH hst (Or.inr ntfn_active_and)
  refine WP.spec_mono (obj.Ntfn.set_badge.wr _ n badge) fun s2 e2 => ?_
  subst e2
  obtain ⟨b2, tm2⟩ := ntfn_badge_all (v := badge) (⟨⟨Q, R, h1⟩, hB1, hX1, hS1, hSg1⟩ : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac _) hn
  exact ⟨hI.of_tmfr b2 (tm1.trans tm2), tm1.trans tm2⟩

/-- **`send_signal` leaves the timer words alone** (`TmFr`), with `TInv` kept (as
`notification.send_signal.tinv`). -/
theorem notification.send_signal.tm {U : Set U64} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (s : S) (a : A) (n badge : U64) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hn : n ∈ Nt)
    (hH : H n = some .ntfn) (hU : ∀ b ∈ U, UsrW st T Cs H Sg Scs Z s b)
    (hbuf : ∀ y ∈ T, msg.lookup_ipc_buffer st s true y ⦃ b => BufOK U b ⦄) :
    notification.send_signal st ar s a n badge ⦃ s' _ => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      TmFr st T Cs Nt s s' ⦄ := by
  have hI := h
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hNb := hX.2.2.ntb
  have hT := h0.tcbs
  unfold notification.send_signal
  step with obj.Ntfn.state.spec as ⟨v, hv⟩
  refine sig_if _ _ _ _ (fun hidl => ?_) (fun hnidl => ?_)
  · -- an idle notification
    have hst0 : L.epState s n ≠ 1#u64 := by rw [← hv, hidl]; unfold obj.NTFN_IDLE; decide
    have sa := notification.set_active.tm s n badge hI hn hH hst0
    step with obj.Ntfn.bound_tcb.val as ⟨i, ei⟩
    step with obj.Tcb.is_null.spec as ⟨b, eb⟩
    -- the notification made active, then (#85) a `TS_RUNNING_VM` thread kicked (no write)
    have OLD : (do
        let s1 ← notification.set_active st s n badge
        if b = true then ok (s1, a)
        else do
          let i2 ← obj.Tcb.state st i s1
          if i2 = sched.TS_RUNNING_VM then notification.kick_guest st ar s1 a i else ok (s1, a))
        ⦃ s' _ => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ TmFr st T Cs Nt s s' ⦄ := by
      refine WP.spec_bind sa fun s1 h1 => ?_
      refine sig_if _ _ _ _ (fun _ => (WP.spec_ok _).2 h1) (fun _ => ?_)
      step with obj.Tcb.state.spec
      refine sig_if _ _ _ _ (fun _ => ?_) (fun _ => (WP.spec_ok _).2 h1)
      refine WP.spec_mono (notification.kick_guest.same hA s1 a i) fun r hr => ?_
      obtain ⟨s', a'⟩ := r
      simp only at hr
      subst hr
      exact h1
    by_cases hb : b = true
    · rw [if_pos hb, if_pos hb]
      refine WP.spec_bind sa fun s1 h1 => ?_
      rw [if_pos hb]
      exact (WP.spec_ok _).2 h1
    rw [if_neg hb]
    have hi0 : i ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    have hiT : i ∈ T := by
      rcases hNb n hn with e | e
      · rw [← ei] at e; exact absurd e hi0
      · rw [← ei] at e; exact e
    have hta := hT i hiT
    step with obj.Tcb.state.spec as ⟨i1, ei1⟩
    refine sig_if _ _ _ _ (fun hrecv => ?_) (fun hnrecv => ?_)
    · have hst : L.mem s (stA i) = sched.TS_BLOCKED_ON_RECV := by rw [← ei1, hrecv]
      have hbl : Blocked (L.mem s (stA i)) := by rw [hst]; exact Or.inr (Or.inl rfl)
      obtain ⟨dq, dr, da⟩ := blocked_out h0 hiT (not_runnable_of_blocked hbl)
      refine WP.spec_bind (ipc.cancel_ipc.all s a i Q R h0 hiT hB hX hSg.sub) ?_
      rintro ⟨s1, a1⟩ ⟨h1, hB1, hX1, nb1, nr1, -, k1, -⟩
      try simp only [WP.uncurry'_pair]
      have hS1 := hS.keepT hX k1
      have hSg1 : SgOK st Ω Sg s1 := ⟨hSg.sub, fun b hb => by rw [k1.ksb]; exact hSg.ks b hb,
        fun o h1' h2' => by rw [k1.ksb]; exact hSg.ksΩ o h1' h2'⟩
      have dq1 : (L.mem s1 (inqA i) &&& sched.Q_QUEUED) = 0#u64 := by rw [k1.inqf hiT]; exact dq
      have dr1 : (L.mem s1 (inqA i) &&& sched.Q_RELEASE) = 0#u64 := by rw [k1.inqf hiT]; exact dr
      have da1 : L.actionW s1 ≠ i := by
        rcases k1.act with e | e
        · rw [e]; exact da
        · rw [e]; exact fun e' => notT_small hT (by simp) (e' ▸ hiT)
      refine WP.spec_bind (sts_all s1 i _ Q R h1 hB1 hX1 hS1 hSg1 hiT not_blocked_running running_ne
        (Or.inr nb1) (hX1.noref hta nr1 (fun e => nb1 (by rw [e]; exact Or.inr (Or.inl rfl))))
        ⟨fun _ _ _ _ _ => runnable_running, fun _ _ _ => runnable_running, fun _ => runnable_running⟩) ?_
      rintro s2 ⟨h2, hB2, hX2, hS2, hSg2, st2, k2⟩
      have h2' : SchedQueuesInv st T Cs Ω H s2 Q R := h2.congrX empty_congr
      have dq2 : (L.mem s2 (inqA i) &&& sched.Q_QUEUED) = 0#u64 := by rw [k2.inqf hiT]; exact dq1
      have dr2 : (L.mem s2 (inqA i) &&& sched.Q_RELEASE) = 0#u64 := by rw [k2.inqf hiT]; exact dr1
      have da2 : L.actionW s2 ≠ i := by
        rcases k2.act with e | e
        · rw [e]; exact da1
        · rw [e]; exact fun e' => notT_small hT (by simp) (e' ▸ hiT)
      refine WP.spec_mono (signal_tail hA s2 a1 i n badge Q R h2' hB2 hX2 hS2 hSg2 hiT hn dq2 dr2 da2
        (fun e => hB.idleNB (by rw [← k1.idleW, ← k2.idleW, e]; exact Or.inl hbl))
        (by rw [st2]; rintro (hb | hb); exact not_blocked_running hb; exact running_ne.1 hb)) ?_
      rintro ⟨s', a'⟩ ⟨hb', tm'⟩
      have tm := (TmFr.of_keepT k1).trans ((TmFr.of_keepT k2).trans tm')
      exact ⟨hI.of_tmfr hb' tm, tm⟩
    · -- not receiving: (#63 / #85) the `RunningVM` completion, else active (and kicked)
      rw [if_neg hb]
      refine sig_if _ _ _ _ (fun hvm => ?_) (fun _ => OLD)
      refine WP.spec_bind (vcpu.signal_completes.blk s i) fun b1 hb1 => ?_
      refine sig_if _ _ _ _ (fun hb1t => ?_) (fun _ => OLD)
      have hvmS : L.mem s (stA i) = sched.TS_RUNNING_VM := by rw [← ei1]; exact hvm
      refine WP.spec_bind (vcpu.report.tm hA s a i badge hI hiT hvmS (hb1 hb1t) hU (hbuf i hiT)) ?_
      rintro s1 ⟨h1, st1, tm1⟩
      refine WP.spec_mono (signal_vm.tm hA s1 a i n h1 hiT hn st1) ?_
      rintro ⟨s', a'⟩ ⟨hb', tm'⟩
      exact ⟨hb', tm1.trans tm'⟩
  · split
    · -- a waiting notification
      rename_i hwait
      have hst1 : L.epState s n = 1#u64 := by rw [← hv, hwait]; unfold obj.NTFN_WAITING; rfl
      obtain ⟨hdT, hbe, hds⟩ := ntfn_head h0 hH hst1
      step with notification.get_queue.spec as ⟨q, eq⟩
      subst eq
      set hd := (L.epQ s n).head with hhd
      have hta := hT hd hdT
      have hbl : Blocked (L.mem s (stA hd)) := by rw [hds]; exact Or.inr (Or.inr rfl)
      obtain ⟨dq, dr, da⟩ := blocked_out h0 hdT (not_runnable_of_blocked hbl)
      have hdq := notification.ntfn_dequeue.inv s hd Q R h0 hdT (by simp) hbl
      rw [hbe] at hdq
      refine WP.spec_bind hdq ?_
      rintro s1 ⟨h1, f1, o1, n1, k1, c1, nc1⟩
      have tm1 : TmFr st T Cs Nt s s1 := TmFr.mk0 ⟨k1, fun y hy K a b c => f1 y hy K (by omega) c (by omega) (by omega),
        fun c hc o ho => nc1 c hc o (by omega) (by omega), fun n' hn' => o1 _ (hSg.sub _ (hX.1.ntB n' hn').2)⟩
      obtain ⟨hB1, hX1, hS1, hSg1, ea1, ec1, ei1⟩ := frame_bx h0 hB hX hS hSg f1 o1 n1 k1 tm1
      have st1 : L.mem s1 (stA hd) = sched.TS_BLOCKED_ON_NTFN := by
        rw [stA_eq, f1 hd hdT _ (by simp) (by simp) (by simp) (by simp), ← stA_eq]; exact hds
      have iq1 : L.mem s1 (inqA hd) = L.mem s (inqA hd) := by
        rw [inqA_eq]; exact f1 hd hdT _ (by simp) (by simp) (by simp) (by simp)
      obtain ⟨-, -, r3, -, r6⟩ := ts_vals
      refine WP.spec_bind (sts_all s1 hd _ Q R h1 hB1 hX1 hS1 hSg1 hdT not_blocked_running running_ne
        (Or.inl (Or.inr rfl)) (hX1.noref hta (by rw [st1]; exact blocked_ne_reply (Or.inr (Or.inr rfl)))
          (by rw [st1, r3, r6]; decide))
        ⟨fun _ _ _ _ _ => runnable_running, fun _ _ _ => runnable_running, fun _ => runnable_running⟩) ?_
      rintro s2 ⟨h2, hB2, hX2, hS2, hSg2, st2, k2⟩
      have h2' : SchedQueuesInv st T Cs Ω H s2 Q R := h2.congrX empty_congr'
      have dq2 : (L.mem s2 (inqA hd) &&& sched.Q_QUEUED) = 0#u64 := by rw [k2.inqf hdT, iq1]; exact dq
      have dr2 : (L.mem s2 (inqA hd) &&& sched.Q_RELEASE) = 0#u64 := by rw [k2.inqf hdT, iq1]; exact dr
      have da2 : L.actionW s2 ≠ hd := by
        rcases k2.act with e | e
        · rw [e, ea1]; exact da
        · rw [e]; exact fun e' => notT_small hT (by simp) (e' ▸ hdT)
      refine WP.spec_mono (signal_tail hA s2 a hd n badge Q R h2' hB2 hX2 hS2 hSg2 hdT hn dq2 dr2 da2
        (fun e => hB.idleNB (by rw [← ei1, ← k2.idleW, e]; exact Or.inl hbl))
        (by rw [st2]; rintro (hb | hb); exact not_blocked_running hb; exact running_ne.1 hb)) ?_
      rintro ⟨s', a'⟩ ⟨hb', tm'⟩
      have tm := tm1.trans ((TmFr.of_keepT k2).trans tm')
      exact ⟨hI.of_tmfr hb' tm, tm⟩
    · -- an active notification
      step with obj.Ntfn.badge.val as ⟨i, ei⟩
      simp only [lift, Aeneas.Std.bind_ok]
      refine WP.spec_bind (obj.Ntfn.set_badge.wr s n _) fun s1 e1 => ?_
      subst e1
      obtain ⟨b1, tm1⟩ := ntfn_badge_all (v := i ||| badge)
        (⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) hn
      exact (WP.spec_ok _).2 ⟨hI.of_tmfr b1 tm1, tm1⟩

/-- **`SigTimerFrame` from `TInv`**: on a `TInv` state, signalling a notification of `Nt` keeps `TInv` and
the timer words (`TAgree`) and the key-space base. -/
theorem notification.send_signal.tagree {U : Set U64} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (s : S) (a : A) (n badge : U64) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hn : n ∈ Nt)
    (hH : H n = some .ntfn) (hU : ∀ b ∈ U, UsrW st T Cs H Sg Scs Z s b)
    (hbuf : ∀ y ∈ T, msg.lookup_ipc_buffer st s true y ⦃ b => BufOK U b ⦄) :
    notification.send_signal st ar s a n badge ⦃ s' _ => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      TAgree st T Cs s s' ∧ L.ksb s' = L.ksb s ⦄ :=
  WP.spec_mono (notification.send_signal.tm hA s a n badge h hn hH hU hbuf) fun r hr => by
    obtain ⟨s', a'⟩ := r
    exact ⟨hr.1, TAgree.of_tmfr hr.2, hr.2.1⟩

/-- `TimerRB` with `TInv` gives `fire`'s loop invariant. -/
theorem TInv.fireInv {s : S} (hR : TimerRB st T Cs s) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    FireInv st T Cs s := by
  obtain ⟨⟨Q, R, h0⟩, -⟩ := h
  exact ⟨hR, h0.nodes, h0.cur⟩

/-- **`fire`'s loop keeps `TimerRB` and `TInv`** (no premise on `send_signal`). -/
theorem timer.fire_loop.rb' {U : Set U64} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A) (now i : U64) (hR : TimerRB st T Cs s)
    (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hBA : BufAt st T Cs H Sg Scs Z U s) :
    timer.fire_loop st ar s a now i ⦃ s' _ => TimerRB st T Cs s' ∧ TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  have hT : TcbPlaced T := by obtain ⟨⟨Q, R, h0⟩, -⟩ := h; exact h0.tcbs
  obtain ⟨IKr, IKs, IKp⟩ := IK T Cs Ω H Sg Rp Scs Nt Z Ac U
  unfold timer.fire_loop
  refine WP.spec_mono (P₀ := fun r : S × A => TimerRB st T Cs r.1 ∧ TInv st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧
    IbFr (L := L) T s r.1) ?_ fun r hr => by obtain ⟨s', a'⟩ := r; exact ⟨hr.1, hr.2.1⟩
  apply loop.spec_decr_nat (measure := fun x => 32 - x.2.2.val)
    (inv := fun x => TimerRB st T Cs x.1 ∧ TInv st T Cs Ω H Sg Rp Scs Nt Z Ac x.1 ∧ IbFr (L := L) T s x.1)
  · rintro ⟨s1, a1, i1⟩ ⟨hR1, hI1, f1⟩
    try simp only at f1
    try simp only
    have h1 : FireInv st T Cs s1 := hI1.fireInv hR1
    unfold timer.fire_loop.body
    try dsimp only
    split
    · rename_i hi
      have hi32 : i1.val < 32 := by simpa using hi
      step with LawfulStore.cur_cpu_spec as ⟨c, ec⟩
      step with obj.node_get.spec as ⟨t, et⟩
      step with obj.Tcb.is_null.spec as ⟨b, eb⟩
      split
      · exact (WP.spec_ok _).2 ⟨hR1, hI1, f1⟩
      rename_i hb
      have ht0 : t ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
      have htT : t ∈ T := by
        have := (h1.1.root_tz h1.2.2).2
        rw [← ec] at this; rw [← et] at this
        rcases this with e | e
        · exact absurd e ht0
        · exact e
      step with obj.Tcb.timer_deadline.val as ⟨d, ed⟩
      split
      · exact (WP.spec_ok _).2 ⟨hR1, hI1, f1⟩
      step with obj.Tcb.timer_badge.val as ⟨bd, ebd⟩
      refine WP.spec_bind (WP.spec_and (WP.spec_and (timer.remove.rb s1 t hT htT h1.1 h1.2.1)
        (timer.remove.tinv s1 t hI1 htT)) (IKr s1 t hI1 htT)) fun s2 h2 => ?_
      obtain ⟨⟨⟨hR2, -, -, -⟩, hI2⟩, g2⟩ := h2
      have f12 := f1.trans g2
      step with obj.Tcb.bound_ntfn.val as ⟨n, en⟩
      refine WP.spec_bind (Pₘ := fun r : S × A => TimerRB st T Cs r.1 ∧ TInv st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧
        IbFr (L := L) T s r.1) ?_ ?_
      · split
        · rename_i hn0
          have hn0' : L.mem s2 (boundA t) ≠ 0#u64 := by rw [← en]; exact bne_ne hn0
          have hn : n ∈ Nt := by rw [en]; exact hI2.2.2.1.2.2.bnd t htT hn0'
          have hb2 := hBA.of_fr f12
          exact WP.spec_mono (WP.spec_and (notification.send_signal.tagree hA s2 a1 n bd hI2 hn (hNt n hn) hb2.1 hb2.2)
            (IKs s2 a1 n bd hI2 hn (hNt n hn) hb2)) fun r hr => by
            obtain ⟨s', a'⟩ := r
            simp only [WP.uncurry'_pair] at hr
            exact ⟨hR2.congr hr.1.2.1, hr.1.1, f12.trans hr.2⟩
        · exact (WP.spec_ok _).2 ⟨hR2, hI2, f12⟩
      rintro ⟨s3, a3⟩ ⟨hR3, hI3, f3⟩
      try simp only [WP.uncurry'_pair]
      step with LawfulStore.cur_cpu_spec as ⟨c3, ec3⟩
      step with obj.node_set.spec as ⟨s4, es4⟩
      step as ⟨i4, ei4⟩
      have hlt : 32 - i4.val < 32 - i1.val := by omega
      try simp only [WP.spec_ok]
      subst es4 ec3
      exact ⟨(FireInv.reprogram (v := 1#u64) hT (hI3.fireInv hR3)).1, reprogram.tinv hI3,
        f3.trans (IKp s3 1#u64 hI3), hlt⟩
    · exact (WP.spec_ok _).2 ⟨hR1, hI1, f1⟩
  · exact ⟨hR, h, IbFr.refl s⟩

/-- **`timer::fire` keeps `TimerRB`** (stage 8, fire part) together with `TInv`; unlike `timer.fire.rb` no
premise on `send_signal` (its timer frame is `notification.send_signal.tagree`). -/
theorem timer.fire.rb' {U : Set U64} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A) (hR : TimerRB st T Cs s)
    (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hBA : BufAt st T Cs H Sg Scs Z U s) :
    timer.fire st ar s a ⦃ s' _ => TimerRB st T Cs s' ∧ TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  unfold timer.fire
  refine WP.spec_bind (L.cur_cpu_spec s) fun c _ => ?_
  refine WP.spec_bind (obj.node_get.spec s c _) fun now _ => ?_
  exact timer.fire_loop.rb' hA IK hNt s a now 0#u64 hR h hBA

end

end Fl4Proofs.P1
