/-
# P2: the guarded-store lemma for the ReplyRecv fast path

`fastpath.reply_recv_found.guard`: an accepted `fastpath.reply_recv_found X0 a
t rptr ep` runs on `guard st R W` as on `st` when `R` / `W` hold `RrAcc` (the
words the run reads and writes, as functions of the entry state `X0`, the
reply's thread `u` and its SC `usc`).

* `rrEnd`: the run after `clear_fault` (the receiver made Restart / Inactive,
  the action, the caller blocked on the endpoint, the switch), and
  `rrEnd.guard`: its writes are address-only, and the switch is handed a
  state that differs from its start only at `RrN5` words.
* **`fastpath.reply_recv_found.guard`**: the checks rewritten leaf by leaf
  (both `Reply.next` arms, the three bound-notification arms, both
  `fastfail` arms), then `rrTail` on the guarded store: `reply_remove` with
  no neighbours (`reply_remove.guardZ`, fl4-sync's `hrz`), `u`'s SC (its
  `CORE` word and that core's `CUR_SC`, `unblock_check`), the fault reply
  (`t`'s buffer as looked up at the entry state), `clear_fault`, `rrEnd`, and
  the switch to `u` (`fastpath.switch_to.guard`, its hypotheses from
  `sl_rr_foot`'s facts at the pre-switch state and, for the release head, from
  P1's `SchedQueuesInv` / `BoundInv` / `SCsOK`; the timer-min thread from
  `RRPl.hTM`).

Premises of `fastpath.reply_recv_found.guard`: `sl_rr_foot`'s `hy0` [J] (the
receiver yields to no SC) and fl4-sync's `hrz` (its check that the reply
object has no neighbours), and P1's `AsidOff` [J] (`P1/FastFinInv.lean`).
The `STATE` / `BLOCK_OBJ` writes are leaf hypotheses of the store (`RrSW`:
for `guard st R W` from `W`, for the ownership check from `P2/MoveSyscall.lean`);
the caller's `BLOCK_OBJ` is written before its `STATE := BLOCKED_ON_RECV`
(the kernel's order since the write-order swap).
-/
import Fl4Proofs.P2.AccessFastFault
import Fl4Proofs.P2.FootSlRR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts

section
variable {S : Type} {A : Type}

/-- The end of an accepted ReplyRecv fast path (`rrTail` after `clear_fault`,
either restart flag: the receiver's state `v`). -/
def rrEnd (st : machine.Store S) (ar : machine.Arch A) (v : U64) (s5 : S) (a2 : A) (t : obj.Tcb)
    (rptr ep_ptr i1 : U64) : Result (Bool × S × A) := do
  let s6 ← obj.Tcb.set_state st i1 s5 v
  let s7 ← sched.set_action st s6 i1
  let s8 ← obj.Tcb.set_state st t s7 sched.TS_RUNNING
  let s9 ← obj.Tcb.set_block_obj st t s8 ep_ptr
  let s10 ← obj.Tcb.set_state st t s9 sched.TS_BLOCKED_ON_RECV
  let s11 ← obj.Tcb.set_reply_obj st t s10 rptr
  let s12 ← obj.Reply.set_tcb st rptr s11 t
  let s13 ← obj.Tcb.set_ep_next st t s12 0#u64
  let s14 ← obj.Tcb.set_ep_prev st t s13 0#u64
  let s15 ← obj.Ep.set_queue st ep_ptr s14 t t obj.EP_RECV
  let (s16, a3) ← fastpath.switch_to st ar s15 a2 i1
  ok (true, s16, a3)

variable {st : machine.Store S} {R W : U64 → Prop} {gS : machine.Store S} [GRd gS st R] [GWr gS st W] [L : LawfulStore st] (ar : machine.Arch A)

/-- The words `rrEnd` writes before the switch. -/
def RrN5 (X5 : S) (t u rptr ep : U64) (b : U64) : Prop :=
  b = stA u ∨ b = L.nodeAt X5 (L.cpu X5) layout.node.SCHED_ACTION ∨ b = stA t ∨ b = blockA t ∨
    b = replyA t ∨ b = rTcbA rptr ∨ b = nextA .Ep t ∨ b = prevA .Ep t ∨ b = epHeadA ep ∨ b = epTSA ep

/-- **`rrEnd` on the guarded store.** -/
theorem rrEnd.guard (v : U64) (X5 : S) (a2 : A) (t : obj.Tcb) (rptr ep u : U64)
    (aSu : Aligned (stA u)) (aAc : Aligned (L.nodeAt X5 (L.cpu X5) layout.node.SCHED_ACTION))
    (aSt : Aligned (stA t)) (aBl : Aligned (blockA t)) (aRp : Aligned (replyA t)) (aRt : Aligned (rTcbA rptr))
    (aEn : Aligned (nextA .Ep t)) (aEp : Aligned (prevA .Ep t)) (aEh : Aligned (epHeadA ep))
    (aEt : Aligned (epTSA ep))
    (wSu : SWr gS st u v) (wAc : W (L.nodeAt X5 (L.cpu X5) layout.node.SCHED_ACTION))
    (wSt : SWr gS st t sched.TS_RUNNING)
    (wBl : ∀ X : S, gS.write X (blockA t) ep = st.write X (blockA t) ep)
    (wSR : ∀ X : S, L.mem X (blockA t) = ep →
      gS.write X (stA t) sched.TS_BLOCKED_ON_RECV = st.write X (stA t) sched.TS_BLOCKED_ON_RECV)
    (wRp : W (replyA t)) (wRt : W (rTcbA rptr)) (wEn : W (nextA .Ep t))
    (wEp : W (prevA .Ep t)) (wEh : W (epHeadA ep)) (wEt : W (epTSA ep))
    (hsw : ∀ X15, WritesIn st X5 X15 (RrN5 (L := L) X5 t u rptr ep) →
      fastpath.switch_to gS ar X15 a2 u = fastpath.switch_to st ar X15 a2 u) :
    rrEnd gS ar v X5 a2 t rptr ep u = rrEnd st ar v X5 a2 t rptr ep u := by
  have eN : ∀ (X : S) (b w : U64), L.nodeAt (L.wr X b w) (L.cpu (L.wr X b w)) layout.node.SCHED_ACTION =
      L.nodeAt X (L.cpu X) layout.node.SCHED_ACTION := fun X b w => by
    rw [LawfulStore.cpu_wr, nodeAt_of_ksb (L.ksb_wr _ _ _)]
  unfold rrEnd
  rw [obj.Tcb.set_state.guardV u X5 v wSu, eq_of_spec_fd (obj.Tcb.set_state.spec (L := L) X5 u v)]
  simp only [bind_ok]
  rw [sched.set_action.guard _ u (by rw [eN]; exact wAc), eq_of_spec_fd (sched.set_action.spec (L := L) _ u)]
  simp only [bind_ok]
  rw [obj.Tcb.set_state.guardV t _ _ wSt, eq_of_spec_fd (obj.Tcb.set_state.spec (L := L) _ t sched.TS_RUNNING)]
  simp only [bind_ok]
  rw [obj.Tcb.set_block_obj.guardAt t _ _ (wBl _), eq_of_spec_fd (obj.Tcb.set_block_obj.wr (L := L) _ t ep)]
  simp only [bind_ok]
  rw [obj.Tcb.set_state.guardAt t _ _ (wSR _ (by rw [L.mem_wr _ _ _ _ aBl aBl, if_pos rfl])),
    eq_of_spec_fd (obj.Tcb.set_state.spec (L := L) _ t sched.TS_BLOCKED_ON_RECV)]
  simp only [bind_ok]
  rw [obj.Tcb.set_reply_obj.guard t _ _ wRp, eq_of_spec_fd (obj.Tcb.set_reply_obj.wr (L := L) _ t rptr)]
  simp only [bind_ok]
  rw [obj.Reply.set_tcb.guard rptr _ _ wRt, eq_of_spec_fd (obj.Reply.set_tcb.spec (L := L) _ rptr t)]
  simp only [bind_ok]
  rw [obj.Tcb.set_ep_next.guard t _ _ wEn, obj.Tcb.set_ep_next.ok]
  simp only [bind_ok]
  rw [obj.Tcb.set_ep_prev.guard t _ _ wEp, obj.Tcb.set_ep_prev.ok]
  simp only [bind_ok]
  rw [obj.Ep.set_queue.guard ep _ _ _ _ wEh wEt, obj.Ep.set_queue.ok]
  simp only [bind_ok]
  unfold epW
  rw [hsw]
  have b1 : ∀ {X Y : S} {ad w : U64}, Y = L.wr X ad w → Aligned ad → RrN5 (L := L) X5 t u rptr ep ad →
      WritesIn st X Y (RrN5 (L := L) X5 t u rptr ep) := fun e ha hb => sl_wr1 e ha hb
  refine (((((((((((b1 rfl aSu (Or.inl rfl)).trans1 (b1 rfl (by rw [eN]; exact aAc)
    (Or.inr (Or.inl (by rw [eN]))))).trans1 (b1 rfl aSt (Or.inr (Or.inr (Or.inl rfl))))).trans1
    (b1 rfl aBl (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))).trans1
    (b1 rfl aSt (Or.inr (Or.inr (Or.inl rfl))))).trans1
    (b1 rfl aRp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))).trans1
    (b1 rfl aRt (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))).trans1
    (b1 rfl aEn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))).trans1
    (b1 rfl aEp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))).trans1
    (b1 rfl aEh (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))).trans1
    (b1 rfl aEt (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))))))

theorem obj.Ntfn.state.guard (n : obj.Ntfn) (s : S)
    (h : R (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE)) :
    obj.Ntfn.state gS n s = obj.Ntfn.state st n s := by
  unfold obj.Ntfn.state; rw [obj.Ntfn.tail_state.guard n s h]

/-- **What an accepted ReplyRecv fast path accesses** (at its entry state
`X0`, with the reply's thread `u` and its SC `usc`): the words `R` / `W` must
hold for `fastpath.reply_recv_found.guard`. -/
structure RrAcc (Z : U64 → Nat) (R W : U64 → Prop) (X0 : S) (t rptr ep u usc : U64) : Prop where
  nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt X0 (L.cpu X0) o) ∧ W (L.nodeAt X0 (L.cpu X0) o)
  dt : R (core.num.U64.wrapping_add (L.ksb X0) layout.ks.DOMAIN_TIME)
  cd : R (core.num.U64.wrapping_add (L.ksb X0) layout.ks.CUR_DOMAIN)
  kr : R (krA (L := L) X0)
  tab : RdTab (L := L) R X0
  /-- The caller `t`. -/
  tSt : R (stA t)
  tSc : R (scA t)
  tMx : R (maxA (L.mem X0 (scA t)))
  tIq : R (inqA t)
  tMi : R (regA t layout.reg.MSG_INFO)
  tBn : R (core.num.U64.wrapping_add t 3368#u64)
  tPr : R (prioA t)
  tReg : Regs R t
  tBuf : RdBuf R t
  tBw : ∀ buf, msg.lookup_ipc_buffer st X0 false t = ok buf → BufW R buf
  ntf : ∀ n, obj.Tcb.bound_ntfn st t X0 = ok n → (n != 0#u64) = true →
    R (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE) ∧ R (core.num.U64.wrapping_add n layout.ntfn.SC)
  wRp : W (replyA t)
  wEn : W (nextA .Ep t)
  wEp : W (prevA .Ep t)
  /-- The reply object. -/
  rRt : R (rTcbA rptr)
  rNx : R (rNextA rptr)
  rPv : R (rPrevA rptr)
  wNx : W (rNextA rptr)
  wPv : W (rPrevA rptr)
  wRt : W (rTcbA rptr)
  /-- The receiver `u`. -/
  uSt : R (stA u)
  uFt : R (core.num.U64.wrapping_add u 3376#u64) ∧ W (core.num.U64.wrapping_add u 3376#u64)
  uSc : R (scA u)
  uPr : R (prioA u)
  uAf : R (affA u)
  uDo : R (core.num.U64.wrapping_add u 3432#u64)
  uIq : R (inqA u)
  uMx : R (maxA usc)
  uReg : Regs W u
  uYt : R (yieldA u)
  uFi : R (regA u layout.reg.FAULT_IP)
  uVt : R (vtA u) ∧ R (core.num.U64.wrapping_add (vtA u) 8#u64)
  /-- The endpoint. -/
  eTS : R (epTSA ep)
  wEh : W (epHeadA ep)
  wEt : W (epTSA ep)
  /-- `u`'s SC (read whole, ring and `CONSUMED` written; its core's `CUR_SC`)
  and the current SC. -/
  spo : R (sporA usc)
  cor : R (core.num.U64.wrapping_add usc layout.sc.CORE)
  ccs : R (L.nodeAt X0 (L.mem X0 (core.num.U64.wrapping_add usc layout.sc.CORE)) layout.node.CUR_SC)
  uHd : RdHead (L := L) R X0 usc
  uscA : ScAcc R W usc (Z usc)
  csc : ScAcc R W (L.cscW X0) (Z (L.cscW X0))
  tm : L.mem X0 (tmA (L := L) X0) ≠ 0#u64 → R (core.num.U64.wrapping_add (L.mem X0 (tmA (L := L) X0)) 3528#u64)
  rh : L.mem X0 (rhA (L := L) X0) ≠ 0#u64 → R (scA (L.mem X0 (rhA (L := L) X0))) ∧
    (∀ b, Aligned b → InSC (L.mem X0 (scA (L.mem X0 (rhA (L := L) X0)))) (Z (L.mem X0 (scA (L.mem X0 (rhA (L := L) X0))))) b →
      R b) ∧
    RdHead (L := L) R X0 (L.mem X0 (scA (L.mem X0 (rhA (L := L) X0))))

/-- **The `STATE` / `BLOCK_OBJ` writes of an accepted ReplyRecv fast path**
(leaf hypotheses whose values matter, `P2/GSt.lean`): the caller `t` made
Restart, Running and, once its `BLOCK_OBJ` is the endpoint `ep`, blocked on
receive; the receiver `u` made Inactive (`reply_unlink`), Restart / Inactive and
Running (`switch_to`). -/
structure RrSW (gS : machine.Store S) (t ep u : U64) : Prop where
  tR : SWr gS st t sched.TS_RESTART
  tN : SWr gS st t sched.TS_RUNNING
  tB : ∀ X : S, L.mem X (blockA t) = ep →
    gS.write X (stA t) sched.TS_BLOCKED_ON_RECV = st.write X (stA t) sched.TS_BLOCKED_ON_RECV
  bl : ∀ X : S, gS.write X (blockA t) ep = st.write X (blockA t) ep
  uI : SWr gS st u sched.TS_INACTIVE
  uR : SWr gS st u sched.TS_RESTART
  uN : SWr gS st u sched.TS_RUNNING

set_option maxHeartbeats 8000000 in
/-- **The accepted ReplyRecv fast path on the guarded store** (`acc` for the
ReplyRecv arm): with `R` / `W` holding `RrAcc` for the checks' `u` / `usc`,
under `sl_rr_foot`'s hypotheses (fl4-sync's `hrz`; `hy0` [J] there) and P1's
`AsidOff` [J]. -/
theorem fastpath.reply_recv_found.guard {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
    (hA : P0.ArchTotal ar) {X0 : S} {a : A} {t : obj.Tcb} {rptr ep : U64}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac X0)
    (hP : ∀ u usc, RRChecks st ar X0 a t rptr ep u usc →
      RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z X0 t rptr ep u usc)
    (hrz : L.mem X0 (rNextA rptr) &&& ~~~1#u64 = 0#u64 ∧ L.mem X0 (rPrevA rptr) &&& ~~~1#u64 = 0#u64)
    (hy0 : ∀ u usc, RRChecks st ar X0 a t rptr ep u usc → L.mem X0 (yieldA u) = 0#u64)
    (hAs : AsidOff (L := L) Ω Sg X0)
    (hRW : ∀ u usc, RRChecks st ar X0 a t rptr ep u usc → RrAcc (L := L) Z R W X0 t rptr ep u usc)
    (hSW : ∀ u usc, RRChecks st ar X0 a t rptr ep u usc → RrSW (L := L) gS t ep u)
    {sF : S} {aF : A} (h : fastpath.reply_recv_found st ar X0 a t rptr ep = ok (true, sF, aF)) :
    fastpath.reply_recv_found gS ar X0 a t rptr ep =
      fastpath.reply_recv_found st ar X0 a t rptr ep := by
  rw [h]
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
  obtain ⟨⟨restart, X4, a2⟩, e4, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨X5, e5, h⟩ := bind_eq_ok h
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
  -- the fault reply, `clear_fault`
  have hTu : TcbPlaced ({u} : Set U64) := fun y hy => by rw [Set.mem_singleton_iff] at hy; rw [hy]; exact hu'
  have w34 : WritesIn st X3 X4 N := by
    have := faults.handle_fault_reply.rg (st := st) (L := L) (ar := ar) (s := X3) (a := a1) (snd := t) hTu (Set.mem_singleton u)
    rw [e4, WP.spec_ok] at this
    refine this.mono fun b hb => ?_
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
      fastpath.switch_to gS ar X15 a2 u = fastpath.switch_to st ar X15 a2 u := by
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
    exact fastpath.switch_to.guard hA X15 a2 P15 hcY htY hactY eyY hrhG htmG hRV hNdY
      (by rw [k15]; exact K.dt) (by rw [ecY]; exact K.csc) (fun _ => by rw [escY]; exact K.uscA)
      K.uSc K.uYt K.uSt K.uFi (K.uReg _ (by simp [layout.reg.NEXT_IP])) SW.uN K.uIq
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
  -- `t`'s buffer, where `handle_fault_reply` looks it up
  have hbw : ∀ X : S, WritesIn st X3 X (XferRegW ({u} : Set U64) ∅) →
      ∀ buf, msg.lookup_ipc_buffer st X false t = ok buf → BufW R buf := by
    intro X hX buf hb
    apply K.tBw
    rw [← hb]
    have kt : ∀ K' : U64, K'.val < 4096 → K'.val % 8 = 0 → (K'.val ≠ 3328 ∧ K'.val ≠ 3336 ∧ K'.val ≠ 3360 ∧
        K'.val ≠ 3496 ∧ K'.val ≠ 3504) → (K'.val < 256 ∨ 3328 ≤ K'.val) →
        L.mem X (core.num.U64.wrapping_add t K') = L.mem X0 (core.num.U64.wrapping_add t K') := by
      intro K' h1 h2 h3 h4
      have aK := field_aligned ht' h1 h2
      rw [hX.mem_eq aK ?_]
      · exact w03.mem_eq aK (tN t K' P.ht h1 h2 (fun _ => h3) (fun e => absurd e.symm P.hut))
      · rintro (⟨y, hy, K, k1, k2, -, e⟩ | ⟨-, hb', -⟩)
        · rw [Set.mem_singleton_iff] at hy; subst hy
          exact field_ne ht' hu' h1 (by omega) (fun e' => absurd e'.symm P.hut) e
    have e72 : core.num.U64.wrapping_add (sbA t) 8#u64 = core.num.U64.wrapping_add t 72#u64 := by
      apply UScalar.eq_of_val_eq
      rw [field_val ht' (by simp), core.num.U64.wrapping_add_val_eq, sbA_val ht']
      have := ht'.fits
      simp [U64.size_def, U64.numBits]
      omega
    symm
    refine lookup_buf_agreeB false (kt 3512#u64 (by simp) (by simp) (by simp) (by simp)) ?_ ?_
    · rw [sbA_field ht']; exact kt 64#u64 (by simp) (by simp) (by simp) (by simp)
    · rw [e72]; exact kt 72#u64 (by simp) (by simp) (by simp) (by simp)
  have tailEq : rrTail gS ar X0 a t rptr ep u usc = rrTail st ar X0 a t rptr ep u usc := by
    unfold rrTail
    rw [obj.Tcb.set_state.guardV t X0 _ SW.tR, e1]; simp only [bind_ok]
    have hn1 : NodeSt (L := L) R W X1 := by
      refine ⟨?_, ?_, ?_⟩ <;> rw [c1, nodeAt_of_ksb k1]
      · exact (K.nd _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])).1
      · exact (K.nd _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])).1
      · exact (K.nd _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])).2
    have aSc : Aligned (scA u) := field_aligned hu' (by simp) (by simp)
    rw [ipc.reply_remove.guardZV ar X1 a rptr u ⟨ernx, erpv⟩ K.rNx K.rPv K.wNx K.wPv hn1 K.wRt SW.uI K.uSt K.uSc
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
      K.uIq, e2]
    simp only [bind_ok, uncurry_apply_pair]
    rw [sporadic.sc_sporadic.guard X2 usc (fun _ => K.spo), hb9r]; simp only [bind_ok]
    refine bind_guard_congr ?_ fun X3' h3' => ?_
    · by_cases hb : b9 = true
      · rw [if_pos hb, if_pos hb, obj.Sc.cpu.guard usc X2 K.cor]
        refine bind_guard_congr rfl fun i13 hi13 => ?_
        have aCo : Aligned (core.num.U64.wrapping_add usc layout.sc.CORE) ∧
            InSC usc (Z usc) (core.num.U64.wrapping_add usc layout.sc.CORE) := by
          obtain ⟨hP', hz⟩ := hO.sc _ P.hcS
          obtain ⟨h8, h128, -⟩ := sc_lo hP' hz
          have hv := sc_word_val hP' hz (o := layout.sc.CORE) (by simp [layout.sc.CORE])
          have hcv : layout.sc.CORE.val = 16 := by simp [layout.sc.CORE]
          exact ⟨by unfold Aligned; rw [hv, hcv]; omega, ⟨by rw [hv]; omega, by rw [hv, hcv]; omega⟩⟩
        have ei : i13 = L.mem X0 (core.num.U64.wrapping_add usc layout.sc.CORE) := by
          unfold obj.Sc.cpu at hi13
          simp only [lift, bind_ok, L.read_eq] at hi13
          rw [← ok_inj_ff hi13]
          obtain ⟨n1, n2, n3⟩ := scRp usc P.hcS _ aCo.2
          exact w02.mem_eq aCo.1 (oN _ (scΩ _ aCo.1 aCo.2) n1 n2 n3)
        rw [obj.node_get.guard X2 i13 _ (by rw [nodeAt_of_ksb w02.1, ei]; exact K.ccs)]
        refine bind_guard_congr rfl fun i14 _ => ?_
        by_cases hne : (usc != i14) = true
        · rw [if_pos hne, if_pos hne, sporadic.unblock_check.guardS K.uscA hW2 hrep
            (by show R (L.nodeAt X2 (L.cpu X2) _); rw [w02.2.1, nodeAt_of_ksb w02.1];
                exact (K.nd _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).1)
            (by rw [eN2]; exact (K.nd _ (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])).2)]
        · rw [if_neg hne, if_neg hne]
      · rw [if_neg hb, if_neg hb]
    rw [e3] at h3'
    cases ok_inj_ff h3'
    rw [faults.handle_fault_reply.guardU ar X3 a1 u t hty3 K.tMi K.uFt.1 K.tReg K.uReg K.tBuf hu' hbw, e4]
    simp only [bind_ok, uncurry_apply_pair]
    rw [faults.clear_fault.guard X4 u K.uFt.2, e5]
    simp only [bind_ok]
    have aAc5 : Aligned (L.nodeAt X5 (L.cpu X5) layout.node.SCHED_ACTION) := by rw [eNA5 X5 rfl rfl]; exact aAc
    have wAc5 : W (L.nodeAt X5 (L.cpu X5) layout.node.SCHED_ACTION) := by
      rw [eNA5 X5 rfl rfl]; exact (K.nd _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])).2
    by_cases hr : restart = true
    · rw [if_pos hr, if_pos hr]
      exact rrEnd.guard ar _ X5 a2 t rptr ep u aSu aAc5 aSt aBl aRp aRt aEn aEp aEh aEt SW.uR wAc5 SW.tN SW.bl SW.tB
        K.wRp K.wRt K.wEn K.wEp K.wEh K.wEt hswG
    · rw [if_neg hr, if_neg hr]
      exact rrEnd.guard ar _ X5 a2 t rptr ep u aSu aAc5 aSt aBl aRp aRt aEn aEp aEh aEt SW.uI wAc5 SW.tN SW.bl SW.tB
        K.wRp K.wRt K.wEn K.wEp K.wEh K.wEt hswG
  /- The checks. -/
  have hrs : L.mem X0 (rhA (L := L) X0) ≠ 0#u64 → R (scA (L.mem X0 (rhA (L := L) X0))) ∧
      RdHead (L := L) R X0 (L.mem X0 (scA (L.mem X0 (rhA (L := L) X0)))) := fun h0 =>
    ⟨(K.rh h0).1, (K.rh h0).2.2⟩
  have hBm : RdBitmap (L := L) R X0 :=
    ⟨(K.nd _ (by simp [l1Off]) (by simp [l1Off])).1, fun inv hinv => (K.nd _ (by simp; omega) (by simp <;> omega)).1⟩
  unfold fastpath.reply_recv_found
  obtain ⟨i0, ha0, hna⟩ := C.act
  rw [sched.action.guard X0 (K.nd _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])).1, ha0]; simp only [bind_ok]
  rw [if_neg hna]
  obtain ⟨b0, hs0, hb0⟩ := C.sch
  rw [sched.is_schedulable.guard X0 t K.tSt K.tSc K.tMx K.tIq, hs0]; simp only [bind_ok]
  rw [if_pos hb0]
  obtain ⟨info, hi, hi1, hi2⟩ := C.info
  rw [msg.msg_info.guard X0 t K.tMi, hi]; simp only [bind_ok]
  rw [if_neg hi1, if_neg hi2]
  rw [obj.Reply.tcb.guard rptr X0 K.rRt, C.tcb]; simp only [bind_ok]
  obtain ⟨bn, hbn, hbn'⟩ := C.u0
  rw [hbn]; simp only [bind_ok]; rw [if_neg hbn']
  obtain ⟨ist, hist, hist'⟩ := C.ust
  rw [obj.Tcb.state.guard u X0 K.uSt, hist]; simp only [bind_ok]; rw [if_neg hist']
  obtain ⟨ift, hift, hift'⟩ := C.uft
  rw [obj.Tcb.fault_type.guard u X0 K.uFt.1, hift]; simp only [bind_ok]; rw [if_neg hift']
  rw [obj.Reply.next.guard X0 rptr K.rNx]
  rcases C.nxt with ⟨i4, hn4, hn4'⟩ | ⟨i4, hn4, hn4', bh, hbh, hbh'⟩
  on_goal 1 => rw [hn4]; simp only [bind_ok]; rw [if_neg hn4']
  on_goal 2 =>
    rw [hn4]; simp only [bind_ok]; rw [if_pos hn4', obj.Reply.next_is_head.guard X0 rptr K.rNx, hbh]
    simp only [bind_ok]; rw [if_neg hbh']
  all_goals
    rw [obj.Tcb.sc.guard u X0 K.uSc, C.sc]; simp only [bind_ok]
    obtain ⟨b3, hb3, hb3'⟩ := C.sc0
    rw [hb3]; simp only [bind_ok]; rw [if_neg hb3']
    obtain ⟨b6, hb6, hb6'⟩ := C.here
    rw [fastpath.schedulable_here.guard X0 u (K.nd _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).1
      (K.nd _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])).1 (K.nd _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])).1
      K.tm hrs K.dt K.cd K.uAf K.uDo K.uSc K.uIq, hb6]
    simp only [bind_ok]
    rw [if_pos hb6']
    obtain ⟨b4, hb4, hb4'⟩ := C.rdy
    rw [sporadic.ready.guard X0 usc K.uHd (K.nd _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).1, hb4]; simp only [bind_ok]
    rw [if_pos hb4']
    obtain ⟨b5, hb5, hb5'⟩ := C.suf
    rw [sporadic.sufficient.guard ar X0 a usc 0#u64 K.uHd, hb5]; simp only [bind_ok]
    rw [if_pos hb5']
    rw [obj.Tcb.bound_ntfn.guard t X0 K.tBn]
    rcases C.ntfn with ⟨i6, h6, h6'⟩ | ⟨i6, h6, h6', i7, h7, h7', i8, h8, h8'⟩
    on_goal 1 => rw [h6]; simp only [bind_ok]; rw [if_neg h6']
    on_goal 2 =>
      rw [h6]; simp only [bind_ok]
      rw [if_pos h6', obj.Ntfn.state.guard i6 X0 (K.ntf i6 h6 h6').1, h7]; simp only [bind_ok]
      rw [if_neg h7', obj.Ntfn.sc.guard i6 X0 (K.ntf i6 h6 h6').2, h8]; simp only [bind_ok]
      rcases h8' with h8' | ⟨h8a, i9, h9, h9'⟩
      on_goal 1 => rw [if_neg h8']
      on_goal 2 => rw [if_pos h8a, obj.Tcb.sc.guard t X0 K.tSc, h9]; simp only [bind_ok]; rw [if_neg h9']
    all_goals
      obtain ⟨i10, h10, h10'⟩ := C.ep
      rw [obj.Ep.state.guard ep X0 K.eTS, h10]; simp only [bind_ok]; rw [if_neg h10']
      obtain ⟨t1, b7, ff, e71, e72, e73, hff⟩ := C.hp
      rw [sched.idle_thread.guard X0 (K.nd _ (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD])).1, e71]; simp only [bind_ok]
      rw [e72]; simp only [bind_ok]
      by_cases hb7 : b7 = true
      on_goal 1 =>
        rw [if_pos hb7] at e73 ⊢
        cases ok_inj_ff e73
        simp only [bind_ok]
      on_goal 2 =>
        rw [if_neg hb7] at e73 ⊢
        rw [obj.Tcb.prio.guard u X0 K.uPr, obj.Tcb.prio.guard t X0 K.tPr]
        obtain ⟨j1, hj1, e'⟩ := bind_eq_ok e73
        obtain ⟨j2, hj2, e''⟩ := bind_eq_ok e'
        rw [hj1]; simp only [bind_ok]; rw [hj2]; simp only [bind_ok]
        by_cases hlt : j1 < j2
        on_goal 1 => rw [if_pos hlt] at e'' ⊢; cases ok_inj_ff e''; simp only [bind_ok]
        on_goal 2 => rw [if_neg hlt] at e'' ⊢; cases ok_inj_ff e''; simp only [bind_ok]
      all_goals
        rcases hff with hff | ⟨hff, i11, i12, b8, h11, h12, h13, hb8⟩
        · first
            | exact absurd rfl hff
            | (simp only [Bool.false_eq_true, ↓reduceIte]; exact tailEq.trans hrt)
        · first
            | exact (Bool.false_ne_true hff).elim
            | (simp only [↓reduceIte]
               rw [sched.cur_domain.guard X0 K.cd, h11]; simp only [bind_ok]
               first
                 | (rw [obj.Tcb.prio.guard u X0 K.uPr, h12]; simp only [bind_ok])
                 | (rw [hj1] at h12; cases ok_inj_ff h12)
               rw [sched.is_highest_prio.guard X0 i11 _ hBm, h13]; simp only [bind_ok]
               rw [if_pos hb8]; exact tailEq.trans hrt)

end

end Fl4Proofs.P2.PathObl
