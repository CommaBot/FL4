/-
# P2 (line slhuf, gen 8): `Once` of an accepted ReplyRecv run at its entry state

Discharges `SlRROnce` (P2/SlOnce.lean). The accepted run of `PathObl.R.fastpath.reply_recv_found` is walked on
`guard st R W` (`R`, `W` without user words; at the syscall entry `SlRS s ∧ NU K` / `SlWS s ∧ NU K`, from
`RrAccNB`, P2/SlOnceR1.lean), except the fault reply's buffer loop (`hfr_once`, P2/SlOnceL.lean):

* the checks, step by step (each guard lemma as in `fastpath.reply_recv_found.guard`'s checks), declines ending at
  once; the 12 copies of the tail reached through the `Reply.next`, bound-notification and `fastfail` arms;
* the tail (`rrTailT`, one lemma for all copies): `set_state`, `reply_remove`, `sc_sporadic`, the SC block, then
  `hfr_once`; after it `clear_fault` and the end (`endT`: `rrEnd`'s writes and `switch_to`) on the guard by
  `endT_eq` + `rrEnd.guard`, the switch's facts (`hswG`) restated for every state the fault reply reaches
  (`WritesIn X3 X4 (XferRegW {u} ∅)`); the state facts are `fastpath.reply_recv_found.guard`'s
  (P2/AccessFastRR.lean), at `R` / `W`.

* **`rr_acc_once`**, **`sl_rr_once`** (`SlRROnce` at every layout), **`sl_hro2`**, **`sl_pathsKC7`**,
  `sl_pathsKC7_startAt` (`sl_pathsKC6` with `hRR` discharged; premises `hSt`, `hA`, `hm`, `a0`, `hCs` [P], `hKD` [P]).
-/
import Fl4Proofs.P2.SlOnceR1
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap Fl4Proofs.P0.Consts
open Fl4Proofs.P2.E2E (Once)

/-- The end of an accepted ReplyRecv fast path as a tree (`rrEnd`'s writes and the switch). -/
noncomputable def endT (t : obj.Tcb) (rptr ep_ptr : Std.U64) (i1 : obj.Tcb) (v : Std.U64) : SProg Bool := do
  let _ ← PathObl.R.obj.Tcb.set_state i1 v
  let _ ← PathObl.R.sched.set_action i1
  let _ ← PathObl.R.obj.Tcb.set_state t sched.TS_RUNNING
  let _ ← PathObl.R.obj.Tcb.set_block_obj t ep_ptr
  let _ ← PathObl.R.obj.Tcb.set_state t sched.TS_BLOCKED_ON_RECV
  let _ ← PathObl.R.obj.Tcb.set_reply_obj t rptr
  let _ ← PathObl.R.obj.Reply.set_tcb rptr t
  let _ ← PathObl.R.obj.Tcb.set_ep_next t 0#u64
  let _ ← PathObl.R.obj.Tcb.set_ep_prev t 0#u64
  let _ ← PathObl.R.obj.Ep.set_queue ep_ptr t t obj.EP_RECV
  let _ ← PathObl.R.fastpath.switch_to i1
  pure (true)

/-- The write part of an accepted ReplyRecv fast path as a tree (`rrTail`; each copy in
`PathObl.R.fastpath.reply_recv_found` is this one up to `SProg.blk`). -/
noncomputable def rrTailT (t : obj.Tcb) (rptr ep_ptr : Std.U64) (i1 : obj.Tcb) (i5 : Std.U64) : SProg Bool := do
  let _ ← PathObl.R.obj.Tcb.set_state t sched.TS_RESTART
  let _ ← PathObl.R.ipc.reply_remove rptr i1
  let b9 ← PathObl.R.sporadic.sc_sporadic i5
  let _ ← (
      if b9 then do
        do
          let i13 ← PathObl.R.obj.Sc.cpu i5
          let i14 ← PathObl.R.obj.node_get i13 layout.node.CUR_SC
          if i5 != i14 then do
            PathObl.R.sporadic.unblock_check i5
          else do
            pure (())
      else do
        pure (()))
  let restart ← PathObl.R.faults.handle_fault_reply i1 t
  let _ ← PathObl.R.faults.clear_fault i1
  if restart then endT t rptr ep_ptr i1 sched.TS_RESTART else endT t rptr ep_ptr i1 sched.TS_INACTIVE

theorem endT_nz (t : obj.Tcb) (rptr ep_ptr : Std.U64) (i1 : obj.Tcb) (v : Std.U64) :
    NoZero (endT t rptr ep_ptr i1 v) := by
  unfold endT
  nz_walk

section
variable {S : Type} {A : Type} (mS : machine.Store S) (mA : machine.Arch A)

theorem endT_eq (t : obj.Tcb) (rptr ep_ptr : Std.U64) (i1 : obj.Tcb) (v : Std.U64) (sS : S) (aA : A) :
    interp mS mA (endT t rptr ep_ptr i1 v) sS aA =
      (rrEnd mS mA v sS aA t rptr ep_ptr i1 >>= fun r => ok (r.1, r.2.1, r.2.2)) := by
  unfold endT
  simp only [reif_simps, rrEnd]
  reif_loop

end

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A) {R W Rd User : U64 → Prop}


set_option hygiene false in
/-- `rr_acc_once`: a guarded check step `p` read at `X0` with the guard rewrite `g`. -/
local macro "rr_gs" eq:ident g:term : tactic => `(tactic| (
    refine once_gstep hR0 hW0 (by nz_walk) ht (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
    · rw [$eq:ident] at h1 ⊢
      rw [($g)]
      exact h1
    replace ht := hk
    rw [$eq:ident] at h1))

set_option hygiene false in
local macro "rr_dec" c:term : tactic => `(tactic| (
    by_cases hc : $c
    · rw [if_pos hc]; simp only [Once]
    rw [if_neg hc] at ht ⊢))

set_option hygiene false in
local macro "rr_fft" : tactic => `(tactic| (
    first | rw [if_pos rfl] at ht ⊢ | rw [if_pos trivial] at ht ⊢
    rr_gs PathObl.R.sched.cur_domain_eq (sched.cur_domain.guard (gS := PathObl.guard st R W) X0 K.cd)
    obtain ⟨i11, -, rfl⟩ := bind_shape h1
    try dsimp only at ht ⊢
    rr_gs PathObl.R.obj.Tcb.prio_eq (obj.Tcb.prio.guard (gS := PathObl.guard st R W) u X0 K.uPr)
    obtain ⟨i12, -, rfl⟩ := bind_shape h1
    try dsimp only at ht ⊢
    rr_gs PathObl.R.sched.is_highest_prio_eq (sched.is_highest_prio.guard (gS := PathObl.guard st R W) X0 i11 _ hBm)
    obtain ⟨b8, -, rfl⟩ := bind_shape h1
    try dsimp only at ht ⊢
    by_cases hb8 : b8 = true
    swap
    · rw [if_neg hb8]; simp only [Once]
    rw [if_pos hb8] at ht ⊢
    exact tailOnce Wd ht))

set_option hygiene false in
local macro "rr_fff" : tactic => `(tactic| (
    first | rw [if_neg Bool.false_ne_true] at ht ⊢ | rw [if_neg not_false] at ht ⊢
    exact tailOnce Wd ht))

set_option hygiene false in
local macro "rr_ep" : tactic => `(tactic| (
    rr_gs PathObl.R.obj.Ep.state_eq (obj.Ep.state.guard (gS := PathObl.guard st R W) ep X0 K.eTS)
    obtain ⟨i10, -, rfl⟩ := bind_shape h1
    try dsimp only at ht ⊢
    rr_dec ((i10 != obj.EP_IDLE) = true)
    rr_gs PathObl.R.sched.idle_thread_eq (sched.idle_thread.guard (gS := PathObl.guard st R W) X0
      (K.nd _ (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD])).1)
    obtain ⟨t1, -, rfl⟩ := bind_shape h1
    try dsimp only at ht ⊢
    refine once_liftR ht (fun b7 _ ht => ?_)
    unfold SProg.blk at ht ⊢
    refine once_ite ht (fun _ ht => ?_) (fun _ ht => ?_)
    · simp only [SProg.sbind] at ht ⊢
      rr_fft
    · rw [SProg.sbind_assoc] at ht ⊢
      rr_gs PathObl.R.obj.Tcb.prio_eq (obj.Tcb.prio.guard (gS := PathObl.guard st R W) u X0 K.uPr)
      obtain ⟨j1, -, rfl⟩ := bind_shape h1
      try dsimp only at ht ⊢
      rw [SProg.sbind_assoc] at ht ⊢
      rr_gs PathObl.R.obj.Tcb.prio_eq (obj.Tcb.prio.guard (gS := PathObl.guard st R W) t X0 K.tPr)
      obtain ⟨j2, -, rfl⟩ := bind_shape h1
      try dsimp only at ht ⊢
      refine once_ite ht (fun _ ht => ?_) (fun _ ht => ?_)
      · simp only [SProg.sbind] at ht ⊢
        rr_fft
      · simp only [SProg.sbind] at ht ⊢
        rr_fff))

set_option hygiene false in
local macro "rr_rest" : tactic => `(tactic| (
    rr_gs PathObl.R.obj.Tcb.sc_eq (obj.Tcb.sc.guard (gS := PathObl.guard st R W) u X0 K.uSc)
    obtain ⟨i5, ei5, rfl⟩ := bind_shape h1
    obtain rfl : usc = i5 := ok_inj_ff (ecs.symm.trans ei5)
    try dsimp only at ht ⊢
    refine once_liftR ht (fun b3 _ ht => ?_)
    rr_dec (b3 = true)
    rr_gs PathObl.R.fastpath.schedulable_here_eq (fastpath.schedulable_here.guard (gS := PathObl.guard st R W) X0 u
      (K.nd _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).1
      (K.nd _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])).1
      (K.nd _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])).1
      K.tm hrs K.dt K.cd K.uAf K.uDo K.uSc K.uIq)
    obtain ⟨b4, -, rfl⟩ := bind_shape h1
    try dsimp only at ht ⊢
    by_cases hb4 : b4 = true
    swap
    · rw [if_neg hb4]; simp only [Once]
    rw [if_pos hb4] at ht ⊢
    rr_gs PathObl.R.sporadic.ready_eq (sporadic.ready.guard (gS := PathObl.guard st R W) X0 usc K.uHd
      (K.nd _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).1)
    obtain ⟨b5, -, rfl⟩ := bind_shape h1
    try dsimp only at ht ⊢
    by_cases hb5 : b5 = true
    swap
    · rw [if_neg hb5]; simp only [Once]
    rw [if_pos hb5] at ht ⊢
    rr_gs PathObl.R.sporadic.sufficient_eq (sporadic.sufficient.guard (gS := PathObl.guard st R W) ar X0 a usc 0#u64 K.uHd)
    obtain ⟨b6, -, rfl⟩ := bind_shape h1
    try dsimp only at ht ⊢
    by_cases hb6 : b6 = true
    swap
    · rw [if_neg hb6]; simp only [Once]
    rw [if_pos hb6] at ht ⊢
    rr_gs PathObl.R.obj.Tcb.bound_ntfn_eq (obj.Tcb.bound_ntfn.guard (gS := PathObl.guard st R W) t X0 K.tBn)
    obtain ⟨i6, e6, rfl⟩ := bind_shape h1
    try dsimp only at ht ⊢
    by_cases h6 : (i6 != 0#u64) = true
    · rw [if_pos h6] at ht ⊢
      rr_gs PathObl.R.obj.Ntfn.state_eq (obj.Ntfn.state.guard (gS := PathObl.guard st R W) i6 X0 (K.ntf i6 e6 h6).1)
      obtain ⟨i7, -, rfl⟩ := bind_shape h1
      try dsimp only at ht ⊢
      rr_dec (i7 = obj.NTFN_ACTIVE)
      rr_gs PathObl.R.obj.Ntfn.sc_eq (obj.Ntfn.sc.guard (gS := PathObl.guard st R W) i6 X0 (K.ntf i6 e6 h6).2)
      obtain ⟨i8, -, rfl⟩ := bind_shape h1
      try dsimp only at ht ⊢
      by_cases h8 : (i8 != 0#u64) = true
      · rw [if_pos h8] at ht ⊢
        rr_gs PathObl.R.obj.Tcb.sc_eq (obj.Tcb.sc.guard (gS := PathObl.guard st R W) t X0 K.tSc)
        obtain ⟨i9, -, rfl⟩ := bind_shape h1
        try dsimp only at ht ⊢
        rr_dec (i8 = i9)
        rr_ep
      · rw [if_neg h8] at ht ⊢
        rr_ep
    · rw [if_neg h6] at ht ⊢
      rr_ep))

set_option hygiene false in
local macro "rr_checks" : tactic => `(tactic| (
    rr_gs PathObl.R.sched.action_eq (sched.action.guard (gS := PathObl.guard st R W) X0
      (K.nd _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])).1)
    obtain ⟨i, -, rfl⟩ := bind_shape h1
    try dsimp only at ht ⊢
    rr_dec ((i != sched.ACTION_RESUME_CURRENT) = true)
    rr_gs PathObl.R.sched.is_schedulable_eq (sched.is_schedulable.guard (gS := PathObl.guard st R W) X0 t K.tSt K.tSc
      K.tMx K.tIq)
    obtain ⟨b, -, rfl⟩ := bind_shape h1
    try dsimp only at ht ⊢
    by_cases hb : b = true
    swap
    · rw [if_neg hb]; simp only [Once]
    rw [if_pos hb] at ht ⊢
    rr_gs PathObl.R.msg.msg_info_eq (msg.msg_info.guard (gS := PathObl.guard st R W) X0 t K.tMi)
    obtain ⟨info, -, rfl⟩ := bind_shape h1
    try dsimp only at ht ⊢
    rr_dec ((info.extra_caps != 0#u64) = true)
    rr_dec ((info.label != 0#u64) = true)
    rr_gs PathObl.R.obj.Reply.tcb_eq (obj.Reply.tcb.guard (gS := PathObl.guard st R W) rptr X0 K.rRt)
    obtain ⟨i1, ei1, rfl⟩ := bind_shape h1
    obtain rfl : u = i1 := ok_inj_ff (ecu.symm.trans ei1)
    try dsimp only at ht ⊢
    refine once_liftR ht (fun b1 _ ht => ?_)
    rr_dec (b1 = true)
    rr_gs PathObl.R.obj.Tcb.state_eq (obj.Tcb.state.guard (gS := PathObl.guard st R W) u X0 K.uSt)
    obtain ⟨i2, -, rfl⟩ := bind_shape h1
    try dsimp only at ht ⊢
    rr_dec ((i2 != sched.TS_BLOCKED_ON_REPLY) = true)
    rr_gs PathObl.R.obj.Tcb.fault_type_eq (obj.Tcb.fault_type.guard (gS := PathObl.guard st R W) u X0 K.uFt.1)
    obtain ⟨i3, -, rfl⟩ := bind_shape h1
    try dsimp only at ht ⊢
    rr_dec ((i3 != fl4_abi.consts.fault.UnknownSyscall) = true)
    rr_gs PathObl.R.obj.Reply.next_eq (obj.Reply.next.guard (gS := PathObl.guard st R W) X0 rptr K.rNx)
    obtain ⟨i4, -, rfl⟩ := bind_shape h1
    try dsimp only at ht ⊢
    by_cases hi4 : (i4 != 0#u64) = true
    · rw [if_pos hi4] at ht ⊢
      rr_gs PathObl.R.obj.Reply.next_is_head_eq (obj.Reply.next_is_head.guard (gS := PathObl.guard st R W) X0 rptr K.rNx)
      obtain ⟨b2, -, rfl⟩ := bind_shape h1
      try dsimp only at ht ⊢
      rr_dec (b2 = true)
      rr_rest
    · rw [if_neg hi4] at ht ⊢
      rr_rest))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- **`Once` of an accepted ReplyRecv fast path** on `guard st R W` (`R`, `W` without user words) but the fault
reply's buffer words (module docstring). The hypotheses are `fastpath.reply_recv_found.guard`'s, with `RrAccNB`
(no buffer words) for `RrAcc`. -/
theorem rr_acc_once {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
    (hR0 : ∀ q, R q → Rd q ∧ ¬ User q) (hW0 : ∀ q, W q → ¬ User q)
    (hA : P0.ArchTotal ar) {X0 : S} {a : A} {t : obj.Tcb} {rptr ep : U64}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac X0)
    (hP : ∀ u usc, RRChecks st ar X0 a t rptr ep u usc →
      RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z X0 t rptr ep u usc)
    (hrz : L.mem X0 (rNextA rptr) &&& ~~~1#u64 = 0#u64 ∧ L.mem X0 (rPrevA rptr) &&& ~~~1#u64 = 0#u64)
    (hy0 : ∀ u usc, RRChecks st ar X0 a t rptr ep u usc → L.mem X0 (yieldA u) = 0#u64)
    (hAs : AsidOff (L := L) Ω Sg X0)
    (hRW : ∀ u usc, RRChecks st ar X0 a t rptr ep u usc → RrAccNB (L := L) Z R W X0 t rptr ep u usc)
    (hSW : ∀ u usc, RRChecks st ar X0 a t rptr ep u usc → RrSW (L := L) (PathObl.guard st R W) t ep u)
    {sF : S} {aF : A} (h : fastpath.reply_recv_found st ar X0 a t rptr ep = ok (true, sF, aF))
    (ht : interp st ar (PathObl.R.fastpath.reply_recv_found t rptr ep) X0 a = ok (true, sF, aF)) (Wd : Set U64) :
    Once st ar Rd User Wd ∅ (PathObl.R.fastpath.reply_recv_found t rptr ep) X0 a := by
  obtain ⟨u, usc, C, hrt⟩ := reply_recv_found_acc st ar h
  have P := hP u usc C
  have hyu := hy0 u usc C
  obtain ⟨⟨Q, RQ, hSQ⟩, hB, hX, hSg, hS⟩ := hI
  have hX0 : ScExtra0 st T Cs Scs Nt X0 := hX.2.2.toScExtra0
  have hO := hX.1
  have hT := P.hT
  have ht' := hT t P.ht
  have hu' := hT u P.hu
  have hN := P.hN
  have hcC := P.hcC
  have hΩ := P.hΩ
  obtain ⟨bh, hbh, hbt⟩ := C.here
  subst hbt
  have HF := here_facts (L := L) hbh
  -- `t` runnable
  obtain ⟨b0, hsch0, hb0⟩ := C.sch
  subst hb0
  have hsp := sched.is_schedulable.spec' (L := L) X0 t
  rw [hsch0, WP.spec_ok] at hsp
  obtain ⟨hrun0, -, -, -⟩ := hsp rfl
  have tnb : ¬ SlBlk st X0 t := by
    intro hb; unfold SlBlk at hb; unfold Runnable at hrun0
    rcases hb with e | e | e <;> rw [e] at hrun0 <;> revert hrun0 <;>
      simp [sched.TS_BLOCKED_ON_RECV, sched.TS_BLOCKED_ON_SEND, sched.TS_BLOCKED_ON_NTFN, sched.TS_RUNNING,
        sched.TS_RESTART, sched.TS_RUNNING_VM]
  have tOn : SlOn st T X0 t := ⟨P.ht, Or.inr P.hcur.symm⟩
  have uOn : SlOn st T X0 u := slOn_aff P.hu HF.aff
  have rp := hO.rp rptr P.hrR
  have vPv := rPrevA_val rp
  have vNx := rNextA_val rp
  have vRt := rTcbA_val0 rptr
  obtain ⟨vEh, vEt⟩ := sl_ep_vals P.hE
  -- `RrW` words are footprint words
  have sub : ∀ b, RrW (L := L) Z X0 t u rptr ep usc b → FootSl st T Z X0 ep rptr b := by
    rintro b ((⟨K, hK, rfl⟩ | ⟨K, h1, h2, rfl⟩ | rfl | rfl | rfl | rfl | rfl | rfl) | hb | rfl)
    · exact FootSl.tcb (slTcb_at' tOn (by omega) (by omega) tnb)
    · exact FootSl.tcb (slTcb_at uOn (by omega) (by omega) (by omega))
    · exact FootSl.lk (Or.inr ⟨by omega, by omega⟩)
    · exact FootSl.lk (Or.inr ⟨by omega, by omega⟩)
    · exact FootSl.lk slLk_rtcb
    · exact FootSl.node (slNode_at (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]))
    · exact FootSl.lk (slLk_ep P.hE).1
    · exact FootSl.lk (slLk_ep P.hE).2
    · exact FootSl.sc (slSc_ring (Or.inr ⟨u, uOn, P.husc, P.hsc0⟩) hb)
    · exact FootSl.node (slNode_at (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM]))
  -- the run's words, one by one
  let RW := RrW (L := L) Z X0 t u rptr ep usc
  let N := RrN (L := L) X0 t u rptr ep
  have rT : ∀ K : U64, (K.val = 3328 ∨ K.val = 3336 ∨ K.val = 3360 ∨ K.val = 3496 ∨ K.val = 3504) →
      N (core.num.U64.wrapping_add t K) := fun K hK => Or.inl ⟨K, hK, rfl⟩
  have rU : ∀ K : U64, 256 ≤ K.val → K.val ≤ 3376 → N (core.num.U64.wrapping_add u K) := fun K h1 h2 =>
    Or.inr (Or.inl ⟨K, h1, h2, rfl⟩)
  have rPv : N (rPrevA rptr) := Or.inr (Or.inr (Or.inl rfl))
  have rNx : N (rNextA rptr) := Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  have rRt : N (rTcbA rptr) := Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have rAc : N (L.nodeAt X0 (L.cpu X0) layout.node.SCHED_ACTION) := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have rEh : N (epHeadA ep) := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have rEt : N (epTSA ep) := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
  have scΩ : ∀ b, Aligned b → InSC usc (Z usc) b → b ∈ Ω := fun b hb hin => P.hSg.sub _ (P.scSg b hb hin)
  have rpΩ : ∀ b, (b = rPrevA rptr ∨ b = rNextA rptr ∨ b = rTcbA rptr) → b ∈ Ω := by
    rintro b (rfl | rfl | rfl)
    · exact P.hSg.sub _ (P.rpS _ ⟨rptr, P.hrR, Or.inl rfl⟩)
    · exact P.hSg.sub _ (P.rpS _ ⟨rptr, P.hrR, Or.inr rfl⟩)
    · exact P.hSg.sub _ P.rtS
  -- what `N` / `RW` miss: TCB words, node words, `Ω` words
  have tN : ∀ y K : U64, y ∈ T → K.val < 4096 → K.val % 8 = 0 →
      (y = t → K.val ≠ 3328 ∧ K.val ≠ 3336 ∧ K.val ≠ 3360 ∧ K.val ≠ 3496 ∧ K.val ≠ 3504) →
      (y = u → 3376 < K.val) → ¬ RW (core.num.U64.wrapping_add y K) := by
    intro y K hy hK h8 ht hu hw
    have hy' := hT y hy
    have vb := field_val hy' hK
    have om : ∀ b ∈ Ω, b ≠ core.num.U64.wrapping_add y K := fun b hb => P.omg_tcb hb hy hK
    rcases hw with (⟨K', hK', e⟩ | ⟨K', h1, h2, e⟩ | e | e | e | e | e | e) | hb | e
    · by_cases hyt : y = t
      · subst hyt; have := ht rfl; have e' := congrArg UScalar.val e
        rw [vb, field_val ht' (by omega)] at e'; omega
      · exact field_ne hy' ht' hK (by omega) (fun h => absurd h hyt) e
    · by_cases hyu : y = u
      · subst hyu; have := hu rfl; have e' := congrArg UScalar.val e
        rw [vb, field_val hu' (by omega)] at e'; omega
      · exact field_ne hy' hu' hK (by omega) (fun h => absurd h hyu) e
    · exact om _ (rpΩ _ (Or.inl rfl)) e.symm
    · exact om _ (rpΩ _ (Or.inr (Or.inl rfl))) e.symm
    · exact om _ (rpΩ _ (Or.inr (Or.inr rfl))) e.symm
    · exact P.tcb_node hy hK (by simp [layout.node.SCHED_ACTION]) e
    · have := P.hE.disj y hy; have e' := congrArg UScalar.val e; rw [vb, vEh] at e'; omega
    · have := P.hE.disj y hy; have e' := congrArg UScalar.val e; rw [vb, vEt] at e'; omega
    · exact om _ (scΩ _ (field_aligned hy' hK h8) hb.inSC) rfl
    · exact P.tcb_node hy hK (by simp [layout.node.REPROGRAM]) e
  have nN : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 16 → o.val ≠ 56 →
      ¬ RW (L.nodeAt X0 (L.cpu X0) o) := by
    intro o ho h8 h16 h56 hw
    have vo := nodeAt_val hN ho
    have aO := nodeAt_aligned hN ho h8
    have hEN := P.hEN.1 _ hcC
    rcases hw with (⟨K', hK', e⟩ | ⟨K', h1, h2, e⟩ | e | e | e | e | e | e) | hb | e
    · exact P.tcb_node P.ht (by omega) ho e.symm
    · exact P.tcb_node P.hu (by omega) ho e.symm
    · exact P.omg_node (rpΩ _ (Or.inl rfl)) ho e.symm
    · exact P.omg_node (rpΩ _ (Or.inr (Or.inl rfl))) ho e.symm
    · exact P.omg_node (rpΩ _ (Or.inr (Or.inr rfl))) ho e.symm
    · exact nodeAt_ne hN ho (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]; omega) e
    · have e' := congrArg UScalar.val e; rw [vo, vEh] at e'; omega
    · have e' := congrArg UScalar.val e; rw [vo, vEt] at e'; omega
    · exact P.omg_node (scΩ _ aO hb.inSC) ho rfl
    · exact nodeAt_ne hN ho (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM]; omega) e
  have oN : ∀ b ∈ Ω, b ≠ rPrevA rptr → b ≠ rNextA rptr → b ≠ rTcbA rptr → ¬ N b := by
    intro b hb n1 n2 n3 hw
    rcases hw with ⟨K', hK', e⟩ | ⟨K', h1, h2, e⟩ | e | e | e | e | e | e
    · exact P.omg_tcb hb P.ht (by omega) e
    · exact P.omg_tcb hb P.hu (by omega) e
    · exact n1 e
    · exact n2 e
    · exact n3 e
    · exact P.omg_node hb (by simp [layout.node.SCHED_ACTION]) e
    · have := P.hEΩ b hb; have e' := congrArg UScalar.val e; rw [vEh] at e'; omega
    · have := P.hEΩ b hb; have e' := congrArg UScalar.val e; rw [vEt] at e'; omega
  have oW : ∀ b ∈ Ω, b ≠ rPrevA rptr → b ≠ rNextA rptr → b ≠ rTcbA rptr → ¬ InRing usc (Z usc) b →
      ¬ RW b := by
    intro b hb n1 n2 n3 n4 hw
    rcases hw with hw | hw | e
    · exact oN b hb n1 n2 n3 hw
    · exact n4 hw
    · exact P.omg_node hb (by simp [layout.node.REPROGRAM]) e
  -- an SC word is no reply word
  have scRp : ∀ c ∈ Scs, ∀ b, InSC c (Z c) b → b ≠ rPrevA rptr ∧ b ≠ rNextA rptr ∧ b ≠ rTcbA rptr := by
    intro c hc b hin
    have := hO.rpSc rptr P.hrR c hc
    unfold InSC at hin
    refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩ <;> have e' := congrArg UScalar.val e <;> omega
  /- The run. -/
  unfold rrTail at hrt
  obtain ⟨X1, e1, h⟩ := bind_eq_ok hrt
  obtain ⟨⟨X2, a1⟩, e2, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨b9, hb9r, h⟩ := bind_eq_ok h
  obtain ⟨X3, e3, h⟩ := bind_eq_ok h
  have hX1 : X1 = L.wr X0 (stA t) sched.TS_RESTART := by
    have := obj.Tcb.set_state.spec (L := L) X0 t sched.TS_RESTART; rw [e1, WP.spec_ok] at this; exact this
  have aSt := P.aS P.ht
  have aSu := P.aS P.hu
  obtain ⟨aPv, aNx⟩ := P.rpA rptr P.hrR
  have aRt : Aligned (rTcbA rptr) := (hΩ _ (rpΩ _ (Or.inr (Or.inr rfl)))).1
  have nSt : ∀ b ∈ Ω, stA t ≠ b := fun b hb e => P.omg_tcb hb P.ht (K := 3328#u64) (by simp) (by rw [← e, stA_eq])
  have ernx : L.mem X1 (rNextA rptr) &&& ~~~1#u64 = 0#u64 := by
    rw [hX1, mem_wr_ne' aSt aNx (nSt _ (rpΩ _ (Or.inr (Or.inl rfl))))]; exact hrz.1
  have erpv : L.mem X1 (rPrevA rptr) &&& ~~~1#u64 = 0#u64 := by
    rw [hX1, mem_wr_ne' aSt aPv (nSt _ (rpΩ _ (Or.inl rfl)))]; exact hrz.2
  have hn1 : obj.Reply.next st rptr X1 = ok 0#u64 := by
    rw [eq_of_spec_fd (obj.Reply.next.spec (L := L) X1 rptr), ernx]
  have k1 : L.ksb X1 = L.ksb X0 := by rw [hX1]; simp
  have c1 : L.cpu X1 = L.cpu X0 := by rw [hX1]; simp
  have cA : Aligned (L.nodeAt X0 (L.cpu X0) layout.node.CUR_THREAD) :=
    nodeAt_aligned hN (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
  have hTS : rTcbA rptr ≠ stA u := by
    rw [stA_eq]; exact P.omg_tcb (rpΩ _ (Or.inr (Or.inr rfl))) P.hu (by decide)
  obtain ⟨-, w12, -⟩ := rr_remove_foot ar (Rp := ({rptr} : Set U64)) (s := X1) (Or.inl ⟨0#u64, hn1, by simp⟩)
    (fun h' _ => absurd ernx h') (fun h' => absurd erpv h')
    (fun r' hr' => by rw [Set.mem_singleton_iff] at hr'; rw [hr']; exact ⟨aPv, aNx⟩)
    (Set.mem_singleton _) aRt aSu hTS (fun X w => by
      show L.mem X (L.nodeAt X (L.cpu X) layout.node.CUR_THREAD) ≠ u
      have ho : layout.node.CUR_THREAD.val < 4288 := by simp [layout.node.CUR_THREAD]
      rw [w.2.1, nodeAt_of_ksb w.1, c1, nodeAt_of_ksb k1, w.mem_eq cA ?_, hX1, mem_wr_ne' aSt cA ?_]
      · rw [show L.mem X0 (L.nodeAt X0 (L.cpu X0) layout.node.CUR_THREAD) = t from P.hcur]
        exact fun e => P.hut e.symm
      · rw [stA_eq]; exact P.tcb_node P.ht (K := 3328#u64) (by decide) ho
      · intro hF
        rcases hF with hR | e | e
        · obtain ⟨r', hr', e⟩ := hR
          have hr'' : r' = rptr := hr'
          rw [hr''] at e
          rcases e with e | e
          · exact P.omg_node (rpΩ _ (Or.inl rfl)) ho e.symm
          · exact P.omg_node (rpΩ _ (Or.inr (Or.inl rfl))) ho e.symm
        · exact P.omg_node (rpΩ _ (Or.inr (Or.inr rfl))) ho e.symm
        · rw [stA_eq] at e; exact P.tcb_node P.hu (K := 3328#u64) (by decide) ho e.symm) e2
  have w01 : WritesIn st X0 X1 N := sl_wr1 hX1 aSt (by rw [stA_eq]; exact rT _ (by simp))
  have w12' : WritesIn st X1 X2 N := w12.mono fun b hb => by
    rcases hb with hR | e | e
    · obtain ⟨r', hr', e⟩ := hR
      have hr'' : r' = rptr := hr'
      rw [hr''] at e
      rcases e with e | e
      · rw [e]; exact rPv
      · rw [e]; exact rNx
    · rw [e]; exact rRt
    · rw [e, stA_eq]; exact rU _ (by simp) (by simp)
  have w02 : WritesIn st X0 X2 N := w01.trans1 w12'
  -- `unblock_check` on `u`'s SC
  have hW2 : RefillsWF st X2 usc (Z usc) := P.hWF.agree fun b hb hin => by
    obtain ⟨n1, n2, n3⟩ := scRp usc P.hcS b hin
    exact w02.mem_eq hb (oN b (scΩ b hb hin) n1 n2 n3)
  have eN2 : L.nodeA X2 layout.node.REPROGRAM = L.nodeAt X0 (L.cpu X0) layout.node.REPROGRAM := by
    unfold LawfulStore.nodeA; rw [w02.2.1, nodeAt_of_ksb w02.1]
  have hrep : Aligned (L.nodeA X2 layout.node.REPROGRAM) ∧
      Outside (L.nodeA X2 layout.node.REPROGRAM) usc (Z usc) := by
    rw [eN2]
    exact ⟨nodeAt_aligned hN (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM]),
      node_out_place scΩ hΩ hcC hN (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])⟩
  have key : X3 = X2 ∨ sporadic.unblock_check st X2 usc = ok X3 := by
    split at e3
    · obtain ⟨i13, -, e3⟩ := bind_eq_ok e3
      obtain ⟨i14, -, e3⟩ := bind_eq_ok e3
      split at e3
      · exact Or.inr e3
      · exact Or.inl (ok_inj_ff e3).symm
    · exact Or.inl (ok_inj_ff e3).symm
  have w23 : WritesIn st X2 X3 RW ∧ RefillsWF st X3 usc (Z usc) := by
    rcases key with rfl | e3'
    · exact ⟨WritesIn.refl _ _, hW2⟩
    · have hf := sporadic.unblock_check.fr hW2 hrep
      have hw := sporadic.unblock_check.wf hW2 hrep
      rw [e3', WP.spec_ok] at hf hw
      refine ⟨hf.mono fun b hb => ?_, hw⟩
      rcases hb with hb | rfl
      · exact Or.inr (Or.inl hb)
      · rw [eN2]; exact Or.inr (Or.inr rfl)
  obtain ⟨w23, hW3⟩ := w23
  have w03 : WritesIn st X0 X3 RW := ((w02.mono fun _ h => Or.inl h).trans w23).mono fun _ hb => hb.elim id id
  have K := hRW u usc C
  have SW := hSW u usc C
  -- `u`'s fault word up to `X3`
  have aFu : Aligned (faultA u) := field_aligned (K := 3376#u64) hu' (by simp) (by simp)
  have hty0 : L.mem X0 (faultA u) = fl4_abi.consts.fault.UnknownSyscall := by
    obtain ⟨i, hi, hi'⟩ := C.uft
    rw [fault_type_ok] at hi
    have := ok_inj_ff hi
    simp only [bne_iff_ne, ne_eq, not_not] at hi'
    rw [this, hi']
  have hty3 : L.mem X3 (faultA u) = fl4_abi.consts.fault.UnknownSyscall := by
    have m1 : L.mem X1 (faultA u) = L.mem X0 (faultA u) := by
      rw [hX1, mem_wr_ne' aSt aFu (by
        rw [stA_eq]; exact field_ne ht' hu' (by simp) (by simp) (fun e => absurd e.symm P.hut))]
    have m2 : L.mem X2 (faultA u) = L.mem X1 (faultA u) := by
      refine w12.mem_eq aFu fun hb => ?_
      rcases hb with hR | e | e
      · obtain ⟨r', hr', e⟩ := hR
        have hr'' : r' = rptr := hr'
        rw [hr''] at e
        rcases e with e | e
        · exact P.omg_tcb (rpΩ _ (Or.inl rfl)) P.hu (K := 3376#u64) (by simp) e.symm
        · exact P.omg_tcb (rpΩ _ (Or.inr (Or.inl rfl))) P.hu (K := 3376#u64) (by simp) e.symm
      · exact P.omg_tcb (rpΩ _ (Or.inr (Or.inr rfl))) P.hu (K := 3376#u64) (by simp) e.symm
      · rw [stA_eq] at e
        exact field_ne hu' hu' (K1 := 3376#u64) (K2 := 3328#u64) (by simp) (by simp) (fun _ => by simp) e
    have m3 : L.mem X3 (faultA u) = L.mem X2 (faultA u) := by
      rcases key with rfl | e3'
      · rfl
      · have hf := sporadic.unblock_check.fr hW2 hrep
        rw [e3', WP.spec_ok] at hf
        refine hf.mem_eq aFu fun hb => ?_
        rcases hb with hb | e
        · exact P.omg_tcb (scΩ _ aFu hb.inSC) P.hu (K := 3376#u64) (by simp) rfl
        · rw [eN2] at e
          exact P.tcb_node P.hu (K := 3376#u64) (by simp) (by simp [layout.node.REPROGRAM]) e
    rw [m3, m2, m1, hty0]
  have hrs : L.mem X0 (rhA (L := L) X0) ≠ 0#u64 → R (scA (L.mem X0 (rhA (L := L) X0))) ∧
      RdHead (L := L) R X0 (L.mem X0 (scA (L.mem X0 (rhA (L := L) X0)))) := fun h0 =>
    ⟨(K.rh h0).1, (K.rh h0).2.2⟩
  have hBm : RdBitmap (L := L) R X0 :=
    ⟨(K.nd _ (by simp [l1Off]) (by simp [l1Off])).1, fun inv hinv => (K.nd _ (by simp; omega) (by simp <;> omega)).1⟩
  -- the end, from every state the fault reply reaches
  have endOnce : ∀ (X4 X5 : S) (b : Bool), WritesIn st X3 X4 (XferRegW ({u} : Set U64) ∅) →
      faults.clear_fault st X4 u = ok X5 → ∀ (r'' : Bool × S × A),
      interp st ar (if b = true then endT t rptr ep u sched.TS_RESTART else endT t rptr ep u sched.TS_INACTIVE)
        X5 a1 = ok r'' → ∀ Wd T0, Once st ar Rd User Wd T0
      (if b = true then endT t rptr ep u sched.TS_RESTART else endT t rptr ep u sched.TS_INACTIVE) X5 a1 := by
    intro X4 X5 b wX e5 r'' hE Wd T0
    -- the fault reply, `clear_fault`
    have hTu : TcbPlaced ({u} : Set U64) := fun y hy => by rw [Set.mem_singleton_iff] at hy; rw [hy]; exact hu'
    have w34 : WritesIn st X3 X4 N := by
      refine wX.mono fun b hb => ?_
      rcases hb with ⟨y, hy, K, h1, h2, -, rfl⟩ | hb
      · rw [Set.mem_singleton_iff] at hy; rw [hy]; exact rU K h1 (by omega)
      · simp at hb
    have hX5 : X5 = L.wr X4 (faultA u) fl4_abi.consts.fault.NullFault := by
      unfold faults.clear_fault at e5
      have := obj.Tcb.set_fault_type.spec (L := L) X4 u fl4_abi.consts.fault.NullFault
      rw [e5, WP.spec_ok] at this; exact this
    have w45 : WritesIn st X4 X5 N :=
      sl_wr1 hX5 (field_aligned (K := 3376#u64) hu' (by simp) (by simp)) (rU 3376#u64 (by simp) (by simp))
    have w05 : WritesIn st X0 X5 RW := (w03.trans ((w34.trans1 w45).mono fun _ h => Or.inl h)).mono
      fun _ hb => hb.elim id id
    have eNA5 : ∀ Y : S, L.ksb Y = L.ksb X5 → L.cpu Y = L.cpu X5 →
        L.nodeAt Y (L.cpu Y) layout.node.SCHED_ACTION = L.nodeAt X0 (L.cpu X0) layout.node.SCHED_ACTION := by
      intro Y hk hc; rw [hc, nodeAt_of_ksb hk, w05.2.1, nodeAt_of_ksb w05.1]
    have aAc : Aligned (L.nodeAt X0 (L.cpu X0) layout.node.SCHED_ACTION) :=
      nodeAt_aligned hN (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
    have aBl : Aligned (blockA t) := field_aligned (K := 3336#u64) ht' (by simp) (by simp)
    have aRp : Aligned (replyA t) := field_aligned (K := 3360#u64) ht' (by simp) (by simp)
    have aEn : Aligned (nextA .Ep t) := nextA_aligned ht' .Ep
    have aEp : Aligned (prevA .Ep t) := prevA_aligned ht' .Ep
    obtain ⟨aEh, aEt⟩ := ep_aligned P.hE
    /- The guarded run. -/
    have K := hRW u usc C
    have SW := hSW u usc C
    have hcs : L.cscW X0 ∈ Scs := hX0.cur
    -- the release head: in `T`, its SC among `Scs` and active
    have rhF : L.mem X0 (rhA (L := L) X0) ≠ 0#u64 → L.mem X0 (rhA (L := L) X0) ∈ T ∧
        L.mem X0 (scA (L.mem X0 (rhA (L := L) X0))) ∈ Scs ∧ L.mem X0 (scA (L.mem X0 (rhA (L := L) X0))) ∈ Ac := by
      intro h0
      have hq := hSQ.release _ hcC
      have hhd : (L.relQ X0 (L.cpu X0)).head = (RQ (L.cpu X0)).headD 0#u64 := hq.head
      cases hl : RQ (L.cpu X0) with
      | nil => rw [hl] at hhd; exact absurd hhd h0
      | cons y ys =>
        rw [hl] at hhd
        have e : L.mem X0 (rhA (L := L) X0) = y := hhd
        have hyR : y ∈ RQ (L.cpu X0) := by rw [hl]; simp
        have hyT := hq.mem y hyR
        have haf := hSQ.inR _ hcC y hyR
        have hfl : (L.mem X0 (inqA y) &&& sched.Q_RELEASE) ≠ 0#u64 := (hSQ.released y hyT).2 (by rw [haf]; exact hyR)
        have hs0 := hB.r y hyT hfl
        rw [e]
        exact ⟨hyT, (hX0.bound y hyT hs0).1, hB.sact y hyT (Or.inr (Or.inl hfl)) hs0⟩
    -- the switch, from any state `rrEnd`'s writes reach
    have hswG : ∀ X15, WritesIn st X5 X15 (RrN5 (L := L) X5 t u rptr ep) →
        fastpath.switch_to (PathObl.guard st R W) ar X15 a1 u = fastpath.switch_to st ar X15 a1 u := by
      intro X15 w515'
      have w515 : WritesIn st X5 X15 N := w515'.mono fun b hb => by
        rcases hb with e | e | e | e | e | e | e | e | e | e
        · rw [e, stA_eq]; exact rU _ (by simp) (by simp)
        · rw [e, eNA5 X5 rfl rfl]; exact rAc
        · rw [e, stA_eq]; exact rT _ (by simp)
        · rw [e]; exact rT 3336#u64 (by simp)
        · rw [e]; exact rT 3360#u64 (by simp)
        · rw [e]; exact rRt
        · rw [e]; exact rT 3496#u64 (by simp)
        · rw [e]; exact rT 3504#u64 (by simp)
        · rw [e]; exact rEh
        · rw [e]; exact rEt
      have w015 : WritesIn st X0 X15 RW := (w05.trans (w515.mono fun _ h => Or.inl h)).mono fun _ hb => hb.elim id id
      have w315 : WritesIn st X3 X15 N := (w34.trans1 w45).trans1 w515
      have k15 := w015.1
      have c15 := w015.2.1
      -- facts at `X15` for the switch
      have escY : L.mem X15 (scA u) = usc := by
        rw [scA_eq, w015.mem_eq (field_aligned hu' (by simp) (by simp))
          (tN u 3464#u64 P.hu (by simp) (by simp) (fun e => absurd e P.hut) (fun _ => by simp))]
        exact P.husc
      have eyY : L.mem X15 (yieldA u) = 0#u64 := by
        rw [show yieldA u = core.num.U64.wrapping_add u 3472#u64 from rfl,
          w015.mem_eq (field_aligned hu' (by simp) (by simp))
          (tN u 3472#u64 P.hu (by simp) (by simp) (fun e => absurd e P.hut) (fun _ => by simp))]
        exact hyu
      have ecY : L.cscW X15 = L.cscW X0 := by
        unfold LawfulStore.cscW LawfulStore.nodeA
        rw [c15, nodeAt_of_ksb k15]
        exact w015.mem_eq (nodeAt_aligned hN (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]))
          (nN _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
            (by simp [layout.node.CUR_SC]))
      have hW15 : RefillsWF st X15 usc (Z usc) := hW3.agree fun b hb hin => by
        obtain ⟨n1, n2, n3⟩ := scRp usc P.hcS b hin
        exact w315.mem_eq hb (oN b (scΩ b hb hin) n1 n2 n3)
      have hcs : L.cscW X0 ∈ Scs := hX0.cur
      have hcq0 : SCq st X0 Ω (L.cscW X0) (Z (L.cscW X0)) := by
        obtain ⟨hP, hz⟩ := hO.sc _ hcs
        obtain ⟨h8, h128, -⟩ := sc_lo hP hz
        have hv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
        have hcv : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
        obtain ⟨a1, a2, a3⟩ := maxA_facts hO hcs
        exact ⟨(hS.all _ hcs).1, fun b hb hi => hS.sub _ ((hS.all _ hcs).2.2 b hb hi),
          ⟨⟨by rw [hv]; omega, by rw [hv, hcv]; omega⟩, by unfold Aligned; rw [hv, hcv]; omega⟩, ⟨a2, a3⟩, a1⟩
      have hcY : SCq st X15 Ω (L.cscW X15) (Z (L.cscW X15)) := by
        rw [ecY]
        refine ⟨fun hm => ?_, hcq0.2.1, hcq0.2.2⟩
        by_cases hcd : L.cscW X0 = usc
        · rw [hcd]; exact hW15
        · have agC : ∀ b, Aligned b → InSC (L.cscW X0) (Z (L.cscW X0)) b → L.mem X15 b = L.mem X0 b := by
            intro b hb hin
            obtain ⟨n1, n2, n3⟩ := scRp _ hcs b hin
            refine w015.mem_eq hb (oW b (hcq0.2.1 b hb hin) n1 n2 n3 fun hR => ?_)
            have := hO.scDisj _ hcs _ P.hcS hcd
            unfold InSC at hin; unfold InRing at hR; omega
          have em : L.rmax X15 (L.cscW X0) = L.rmax X0 (L.cscW X0) := by
            obtain ⟨a1, a2, a3⟩ := maxA_facts hO hcs
            exact agC _ a1 ⟨a2, a3⟩
          exact (hcq0.1 (em ▸ hm)).agree agC
      have htY : L.mem X15 (scA u) ≠ L.cscW X15 → SCin st X15 Ω (L.mem X15 (scA u)) (Z (L.mem X15 (scA u))) ∧
          ∀ b, InSC (L.mem X15 (scA u)) (Z (L.mem X15 (scA u))) b → Outside b (L.cscW X15) (Z (L.cscW X15)) := by
        rw [escY, ecY]
        intro hne
        refine ⟨⟨hW15, scΩ⟩, fun b hin => ?_⟩
        have := hO.scDisj _ P.hcS _ hcs hne
        unfold InSC at hin; unfold Outside; omega
      have P15 : TailPld (L := L) T Cs Ω X15 u :=
        (⟨hT, P.hu, hN, hcC, hΩ⟩ : TailPld (L := L) T Cs Ω X0 u).ksb k15 c15
      have nd15 : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 16 → o.val ≠ 56 →
          L.mem X15 (L.nodeAt X0 (L.cpu X0) o) = L.mem X0 (L.nodeAt X0 (L.cpu X0) o) := fun o h1 h2 h3 h4 =>
        w015.mem_eq (nodeAt_aligned hN h1 h2) (nN o h1 h2 h3 h4)
      have eN15 : ∀ o, L.nodeAt X15 (L.cpu X15) o = L.nodeAt X0 (L.cpu X0) o := fun o => by
        rw [c15, nodeAt_of_ksb k15]
      have hrhY : L.mem X15 (rhA (L := L) X15) = L.mem X0 (rhA (L := L) X0) := by
        show L.mem X15 (L.nodeAt X15 (L.cpu X15) _) = _
        rw [eN15]
        exact nd15 _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
          (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      have htmY : L.mem X15 (tmA (L := L) X15) = L.mem X0 (tmA (L := L) X0) := by
        show L.mem X15 (L.nodeAt X15 (L.cpu X15) _) = _
        rw [eN15]
        exact nd15 _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
          (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      have scY : ∀ q ∈ Scs, q ≠ usc → ∀ b, Aligned b → InSC q (Z q) b → L.mem X15 b = L.mem X0 b := by
        intro q hq hne b hb hin
        obtain ⟨n1, n2, n3⟩ := scRp q hq b hin
        refine w015.mem_eq hb (oW b (hS.sub _ ((hS.all _ hq).2.2 b hb hin)) n1 n2 n3 fun hR => ?_)
        have := hO.scDisj _ hq _ P.hcS hne
        unfold InSC at hin; unfold InRing at hR; omega
      have hrhG : L.mem X15 (rhA (L := L) X15) ≠ 0#u64 → L.mem X15 (rhA (L := L) X15) ∈ T ∧
          R (scA (L.mem X15 (rhA (L := L) X15))) ∧
          ∃ zq, SCin st X15 Ω (L.mem X15 (scA (L.mem X15 (rhA (L := L) X15)))) zq ∧
            (∀ b, Aligned b → InSC (L.mem X15 (scA (L.mem X15 (rhA (L := L) X15)))) zq b → R b) ∧
            (L.mem X15 (scA (L.mem X15 (rhA (L := L) X15))) ≠ L.cscW X15 →
              ∀ b, InSC (L.mem X15 (scA (L.mem X15 (rhA (L := L) X15)))) zq b →
                Outside b (L.cscW X15) (Z (L.cscW X15))) ∧
            (L.mem X15 (scA (L.mem X15 (rhA (L := L) X15))) ≠ L.mem X15 (scA u) → L.mem X15 (scA u) ≠ L.cscW X15 →
              ∀ b, InSC (L.mem X15 (scA (L.mem X15 (rhA (L := L) X15)))) zq b →
                Outside b (L.mem X15 (scA u)) (Z (L.mem X15 (scA u)))) := by
        rw [hrhY]
        intro h0
        obtain ⟨hyT, hqS, hqA⟩ := rhF h0
        obtain ⟨kr1, kr2, -⟩ := K.rh h0
        have esY : L.mem X15 (scA (L.mem X0 (rhA (L := L) X0))) = L.mem X0 (scA (L.mem X0 (rhA (L := L) X0))) := by
          rw [scA_eq]
          refine w015.mem_eq (field_aligned (hT _ hyT) (by simp) (by simp)) (tN _ 3464#u64 hyT (by simp) (by simp) ?_ ?_)
          · intro _; simp
          · intro _; simp
        rw [esY, escY, ecY]
        generalize L.mem X0 (scA (L.mem X0 (rhA (L := L) X0))) = q at hqS hqA kr2 ⊢
        refine ⟨hyT, kr1, Z q, ⟨?_, fun b hb hin => hS.sub _ ((hS.all _ hqS).2.2 b hb hin)⟩, kr2, ?_, ?_⟩
        · by_cases hqd : q = usc
          · rw [hqd]; exact hW15
          · exact ((hS.all _ hqS).1 ((hS.act _ hqS).1 hqA)).agree (scY q hqS hqd)
        · intro hne b hin
          have := hO.scDisj _ hqS _ hcs hne
          unfold InSC at hin; unfold Outside; omega
        · intro hne _ b hin
          have := hO.scDisj _ hqS _ P.hcS hne
          unfold InSC at hin; unfold Outside; omega
      have htmG : L.mem X15 (tmA (L := L) X15) ≠ 0#u64 → L.mem X15 (tmA (L := L) X15) ∈ T ∧
          R (core.num.U64.wrapping_add (L.mem X15 (tmA (L := L) X15)) 3528#u64) := by
        rw [htmY]
        intro h0
        exact ⟨P.hTM.resolve_left h0, K.tm h0⟩
      have keepA : ∀ b ∈ Ω, b ∉ Sg → L.mem X15 b = L.mem X0 b := fun b hb hs =>
        w015.mem_eq (hΩ b hb).1 (oW b hb (fun e => hs (e ▸ P.rpS _ ⟨rptr, P.hrR, Or.inl rfl⟩))
          (fun e => hs (e ▸ P.rpS _ ⟨rptr, P.hrR, Or.inr rfl⟩)) (fun e => hs (e ▸ P.rtS))
          (fun hR => hs (P.scSg b (hΩ b hb).1 hR.inSC)))
      have hRV : RdVm (L := L) R X15 u := by
        refine ⟨K.uVt.1, K.uVt.2, ?_, ?_⟩
        · show R (core.num.U64.wrapping_add (L.ksb X15) _); rw [k15]; exact K.kr
        · refine fun hi hhi => ?_
          have aT := hAs hi hhi
          rw [k15, keepA _ aT.1 aT.2.1]
          exact K.tab hi hhi
      have hactY : L.mem X15 (scA u) = L.cscW X15 → L.rmax X15 (L.cscW X15) ≠ 0#u64 := by
        intro e
        rw [← e, escY]
        intro h0
        have hm := hW15.min_le
        rw [h0] at hm
        simp [sporadic.MIN_REFILLS] at hm
      have hNdY : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeA X15 o) ∧ W (L.nodeA X15 o) := fun o ho h8 => by
        show R (L.nodeAt X15 (L.cpu X15) o) ∧ W (L.nodeAt X15 (L.cpu X15) o)
        rw [eN15]; exact K.nd o ho h8
      exact fastpath.switch_to.guard hA X15 a1 P15 hcY htY hactY eyY hrhG htmG hRV hNdY
        (by rw [k15]; exact K.dt) (by rw [ecY]; exact K.csc) (fun _ => by rw [escY]; exact K.uscA)
        K.uSc K.uYt K.uSt K.uFi (K.uReg _ (by simp [layout.reg.NEXT_IP])) SW.uN K.uIq
    have aAc5 : Aligned (L.nodeAt X5 (L.cpu X5) layout.node.SCHED_ACTION) := by rw [eNA5 X5 rfl rfl]; exact aAc
    have wAc5 : W (L.nodeAt X5 (L.cpu X5) layout.node.SCHED_ACTION) := by
      rw [eNA5 X5 rfl rfl]; exact (K.nd _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])).2
    cases b
    · rw [if_neg Bool.false_ne_true] at hE ⊢
      have hg : interp (PathObl.guard st R W) ar (endT t rptr ep u sched.TS_INACTIVE) X5 a1 = ok r'' := by
        rw [endT_eq] at hE ⊢
        rw [rrEnd.guard ar _ X5 a1 t rptr ep u aSu aAc5 aSt aBl aRp aRt aEn aEp aEh aEt SW.uI wAc5 SW.tN SW.bl SW.tB
          K.wRp K.wRt K.wEn K.wEp K.wEh K.wEt hswG]
        exact hE
      exact once_monoR (fun q hq => (hR0 q hq).1) _ Wd T0 T0 X5 a1
        (once_of_guardG (fun q hq => (hR0 q hq).2) _ (endT_nz _ _ _ _ _) Wd T0 X5 a1 r'' hg) subset_rfl
    · rw [if_pos rfl] at hE ⊢
      have hg : interp (PathObl.guard st R W) ar (endT t rptr ep u sched.TS_RESTART) X5 a1 = ok r'' := by
        rw [endT_eq] at hE ⊢
        rw [rrEnd.guard ar _ X5 a1 t rptr ep u aSu aAc5 aSt aBl aRp aRt aEn aEp aEh aEt SW.uR wAc5 SW.tN SW.bl SW.tB
          K.wRp K.wRt K.wEn K.wEp K.wEh K.wEt hswG]
        exact hE
      exact once_monoR (fun q hq => (hR0 q hq).1) _ Wd T0 T0 X5 a1
        (once_of_guardG (fun q hq => (hR0 q hq).2) _ (endT_nz _ _ _ _ _) Wd T0 X5 a1 r'' hg) subset_rfl
  -- after the SC block: the fault reply, then the end
  have afterBlk : ∀ Wd, interp st ar ((PathObl.R.faults.handle_fault_reply u t).sbind fun restart =>
        (PathObl.R.faults.clear_fault u).sbind fun _ =>
          if restart = true then endT t rptr ep u sched.TS_RESTART else endT t rptr ep u sched.TS_INACTIVE)
        X3 a1 = ok (true, sF, aF) →
      Once st ar Rd User Wd ∅ ((PathObl.R.faults.handle_fault_reply u t).sbind fun restart =>
        (PathObl.R.faults.clear_fault u).sbind fun _ =>
          if restart = true then endT t rptr ep u sched.TS_RESTART else endT t rptr ep u sched.TS_INACTIVE) X3 a1 := by
    intro Wd hh
    refine hfr_once hR0 hu' (fun r hr => hW0 _ (K.uReg r hr)) K.tMi K.uFt.1 K.tReg K.tBuf hty3 _ hh ?_ Wd
    intro s1 b wX h' Wd' T'
    try dsimp only at h' ⊢
    refine once_gstep hR0 hW0 (PathObl.R.faults.clear_fault_nz _) h' (fun r h1 => ?_) (fun r h1 hk Wd'' _ => ?_)
    · rw [PathObl.R.faults.clear_fault_eq] at h1 ⊢
      rw [faults.clear_fault.guard (gS := PathObl.guard st R W) s1 u K.uFt.2]
      exact h1
    rw [PathObl.R.faults.clear_fault_eq] at h1
    obtain ⟨X5, e5, rfl⟩ := bind_shape h1
    try dsimp only at hk ⊢
    exact endOnce s1 X5 b wX e5 _ hk Wd'' T'
  -- the tail
  have hn1 : NodeSt (L := L) R W X1 := by
    refine ⟨?_, ?_, ?_⟩ <;> rw [c1, nodeAt_of_ksb k1]
    · exact (K.nd _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])).1
    · exact (K.nd _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])).1
    · exact (K.nd _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])).2
  have aSc : Aligned (scA u) := field_aligned hu' (by simp) (by simp)
  have hrem : ipc.reply_remove (PathObl.guard st R W) ar X1 a rptr u = ipc.reply_remove st ar X1 a rptr u :=
    ipc.reply_remove.guardZV ar X1 a rptr u ⟨ernx, erpv⟩ K.rNx K.rPv K.wNx K.wPv hn1 K.wRt SW.uI K.uSt K.uSc
      aPv aNx aRt aSu (fun X hX => by
        rw [hX.mem_eq aSc ?_, hX1, mem_wr_ne' aSt aSc (by
          rw [stA_eq]; exact field_ne ht' hu' (by simp) (by simp) (fun e => absurd e.symm P.hut)), P.husc]
        · exact K.uMx
        · rintro (e | e | e | e)
          · exact P.omg_tcb (rpΩ _ (Or.inl rfl)) P.hu (K := 3464#u64) (by simp) e.symm
          · exact P.omg_tcb (rpΩ _ (Or.inr (Or.inl rfl))) P.hu (K := 3464#u64) (by simp) e.symm
          · exact P.omg_tcb (rpΩ _ (Or.inr (Or.inr rfl))) P.hu (K := 3464#u64) (by simp) e.symm
          · rw [stA_eq] at e
            exact field_ne hu' hu' (K1 := 3464#u64) (K2 := 3328#u64) (by simp) (by simp) (fun _ => by simp) e)
      K.uIq
  have aCo : Aligned (core.num.U64.wrapping_add usc layout.sc.CORE) ∧
      InSC usc (Z usc) (core.num.U64.wrapping_add usc layout.sc.CORE) := by
    obtain ⟨hP', hz⟩ := hO.sc _ P.hcS
    obtain ⟨h8, h128, -⟩ := sc_lo hP' hz
    have hv := sc_word_val hP' hz (o := layout.sc.CORE) (by simp [layout.sc.CORE])
    have hcv : layout.sc.CORE.val = 16 := by simp [layout.sc.CORE]
    exact ⟨by unfold Aligned; rw [hv, hcv]; omega, ⟨by rw [hv]; omega, by rw [hv, hcv]; omega⟩⟩
  have tailOnce : ∀ Wd, interp st ar (rrTailT t rptr ep u usc) X0 a = ok (true, sF, aF) →
      Once st ar Rd User Wd ∅ (rrTailT t rptr ep u usc) X0 a := by
    intro Wd ht
    unfold rrTailT at ht ⊢
    simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret] at ht ⊢
    refine once_gstep hR0 hW0 (PathObl.R.obj.Tcb.set_state_nz _ _) ht (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
    · rw [PathObl.R.obj.Tcb.set_state_eq] at h1 ⊢
      rw [obj.Tcb.set_state.guardV t X0 _ SW.tR]
      exact h1
    replace ht := hk
    rw [PathObl.R.obj.Tcb.set_state_eq] at h1
    obtain ⟨Y1, ey1, rfl⟩ := bind_shape h1
    obtain rfl : X1 = Y1 := ok_inj_ff (e1.symm.trans ey1)
    try dsimp only at ht ⊢
    refine once_gstep hR0 hW0 (PathObl.R.ipc.reply_remove_nz _ _) ht (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
    · rw [PathObl.R.ipc.reply_remove_eq] at h1 ⊢
      rw [hrem]
      exact h1
    replace ht := hk
    rw [PathObl.R.ipc.reply_remove_eq] at h1
    obtain ⟨⟨Y2, b2⟩, ey2, rfl⟩ := bind_shape h1
    obtain ⟨rfl, rfl⟩ : X2 = Y2 ∧ a1 = b2 := Prod.mk.inj (ok_inj_ff (e2.symm.trans ey2))
    try dsimp only at ht ⊢
    refine once_gstep hR0 hW0 (PathObl.R.sporadic.sc_sporadic_nz _) ht (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
    · rw [PathObl.R.sporadic.sc_sporadic_eq] at h1 ⊢
      rw [sporadic.sc_sporadic.guard (gS := PathObl.guard st R W) X2 usc (fun _ => K.spo)]
      exact h1
    replace ht := hk
    rw [PathObl.R.sporadic.sc_sporadic_eq] at h1
    obtain ⟨c9, ec9, rfl⟩ := bind_shape h1
    obtain rfl : b9 = c9 := ok_inj_ff (hb9r.symm.trans ec9)
    try dsimp only at ht ⊢
    by_cases hb : b9 = true
    · rw [if_pos hb] at ht ⊢ e3
      rw [SProg.sbind_assoc] at ht ⊢
      refine once_gstep hR0 hW0 (PathObl.R.obj.Sc.cpu_nz _) ht (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
      · rw [PathObl.R.obj.Sc.cpu_eq] at h1 ⊢
        rw [obj.Sc.cpu.guard (gS := PathObl.guard st R W) usc X2 K.cor]
        exact h1
      replace ht := hk
      rw [PathObl.R.obj.Sc.cpu_eq] at h1
      obtain ⟨i13, hi13, rfl⟩ := bind_shape h1
      try dsimp only at ht ⊢
      have ei : i13 = L.mem X0 (core.num.U64.wrapping_add usc layout.sc.CORE) := by
        have hi13' := hi13
        unfold obj.Sc.cpu at hi13'
        simp only [lift, bind_ok, L.read_eq] at hi13'
        rw [← ok_inj_ff hi13']
        obtain ⟨n1, n2, n3⟩ := scRp usc P.hcS _ aCo.2
        exact w02.mem_eq aCo.1 (oN _ (scΩ _ aCo.1 aCo.2) n1 n2 n3)
      rw [SProg.sbind_assoc] at ht ⊢
      refine once_gstep hR0 hW0 (PathObl.R.obj.node_get_nz _ _) ht (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
      · rw [PathObl.R.obj.node_get_eq] at h1 ⊢
        rw [obj.node_get.guard (gS := PathObl.guard st R W) X2 i13 _
          (by rw [nodeAt_of_ksb w02.1, ei]; exact K.ccs)]
        exact h1
      replace ht := hk
      rw [PathObl.R.obj.node_get_eq] at h1
      obtain ⟨i14, hi14, rfl⟩ := bind_shape h1
      try dsimp only at ht ⊢
      rw [hi13] at e3
      simp only [bind_ok, bind_tc_ok] at e3
      rw [hi14] at e3
      simp only [bind_ok, bind_tc_ok] at e3
      refine once_ite ht (fun hne ht => ?_) (fun hne ht => ?_)
      · rw [if_pos hne] at e3
        refine once_gstep hR0 hW0 (PathObl.R.sporadic.unblock_check_nz _) ht (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
        · rw [PathObl.R.sporadic.unblock_check_eq] at h1 ⊢
          rw [sporadic.unblock_check.guardS (gS := PathObl.guard st R W) K.uscA hW2 hrep
            (by show R (L.nodeAt X2 (L.cpu X2) _); rw [w02.2.1, nodeAt_of_ksb w02.1];
                exact (K.nd _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).1)
            (by rw [eN2]; exact (K.nd _ (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])).2)]
          exact h1
        rw [PathObl.R.sporadic.unblock_check_eq] at h1
        obtain ⟨Y3, ey3, rfl⟩ := bind_shape h1
        obtain rfl : X3 = Y3 := ok_inj_ff (e3.symm.trans ey3)
        try dsimp only at hk ⊢
        exact afterBlk Wd hk
      · rw [if_neg hne] at e3
        simp only [SProg.sbind] at ht ⊢
        obtain rfl : X2 = X3 := ok_inj_ff e3
        exact afterBlk Wd ht
    · rw [if_neg hb] at ht ⊢ e3
      simp only [SProg.sbind] at ht ⊢
      obtain rfl : X2 = X3 := ok_inj_ff e3
      exact afterBlk Wd ht
  -- the checks
  have ecu := C.tcb
  have ecs := C.sc
  unfold PathObl.R.fastpath.reply_recv_found at ht ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret] at ht ⊢
  rr_checks


end

end Fl4Proofs.P2.PathObl
