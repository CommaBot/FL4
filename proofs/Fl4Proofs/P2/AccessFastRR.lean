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

No premises.
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
  let s9 ← obj.Tcb.set_state st t s8 sched.TS_BLOCKED_ON_RECV
  let s10 ← obj.Tcb.set_block_obj st t s9 ep_ptr
  let s11 ← obj.Tcb.set_reply_obj st t s10 rptr
  let s12 ← obj.Reply.set_tcb st rptr s11 t
  let s13 ← obj.Tcb.set_ep_next st t s12 0#u64
  let s14 ← obj.Tcb.set_ep_prev st t s13 0#u64
  let s15 ← obj.Ep.set_queue st ep_ptr s14 t t obj.EP_RECV
  let (s16, a3) ← fastpath.switch_to st ar s15 a2 i1
  ok (true, s16, a3)

variable {st : machine.Store S} {R W : U64 → Prop} [L : LawfulStore st] (ar : machine.Arch A)

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
    (wSu : W (stA u)) (wAc : W (L.nodeAt X5 (L.cpu X5) layout.node.SCHED_ACTION)) (wSt : W (stA t))
    (wBl : W (blockA t)) (wRp : W (replyA t)) (wRt : W (rTcbA rptr)) (wEn : W (nextA .Ep t))
    (wEp : W (prevA .Ep t)) (wEh : W (epHeadA ep)) (wEt : W (epTSA ep))
    (hsw : ∀ X15, WritesIn st X5 X15 (RrN5 (L := L) X5 t u rptr ep) →
      fastpath.switch_to (guard st R W) ar X15 a2 u = fastpath.switch_to st ar X15 a2 u) :
    rrEnd (guard st R W) ar v X5 a2 t rptr ep u = rrEnd st ar v X5 a2 t rptr ep u := by
  have eN : ∀ (X : S) (b w : U64), L.nodeAt (L.wr X b w) (L.cpu (L.wr X b w)) layout.node.SCHED_ACTION =
      L.nodeAt X (L.cpu X) layout.node.SCHED_ACTION := fun X b w => by
    rw [LawfulStore.cpu_wr, nodeAt_of_ksb (L.ksb_wr _ _ _)]
  unfold rrEnd
  rw [obj.Tcb.set_state.guard u X5 v wSu, eq_of_spec_fd (obj.Tcb.set_state.spec (L := L) X5 u v)]
  simp only [bind_ok]
  rw [sched.set_action.guard _ u (by rw [eN]; exact wAc), eq_of_spec_fd (sched.set_action.spec (L := L) _ u)]
  simp only [bind_ok]
  rw [obj.Tcb.set_state.guard t _ _ wSt, eq_of_spec_fd (obj.Tcb.set_state.spec (L := L) _ t sched.TS_RUNNING)]
  simp only [bind_ok]
  rw [obj.Tcb.set_state.guard t _ _ wSt,
    eq_of_spec_fd (obj.Tcb.set_state.spec (L := L) _ t sched.TS_BLOCKED_ON_RECV)]
  simp only [bind_ok]
  rw [obj.Tcb.set_block_obj.guard t _ _ wBl, eq_of_spec_fd (obj.Tcb.set_block_obj.wr (L := L) _ t ep)]
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
    (b1 rfl aSt (Or.inr (Or.inr (Or.inl rfl))))).trans1
    (b1 rfl aBl (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))).trans1
    (b1 rfl aRp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))).trans1
    (b1 rfl aRt (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))).trans1
    (b1 rfl aEn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))).trans1
    (b1 rfl aEp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))).trans1
    (b1 rfl aEh (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))).trans1
    (b1 rfl aEt (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))))))

end

end Fl4Proofs.P2.PathObl
