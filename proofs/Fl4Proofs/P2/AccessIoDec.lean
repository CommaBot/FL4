/-
# P2: guarded-store lemma for `ioport.invocation_ok` (line p2io)

Split from `P2/AccessIo.lean` (elaboration memory).

* `ioport.invocation_ok.guard`, run-relative: the CSpace walk, the found slot,
  the IPC buffer word and slot, register `R10`;
* `ioport.decode.guard` on an I/O port cap, through `decode_ioport_eq` (the arm
  alone, by `rfl`) and the two tails `ioInTail.guard` / `ioOutTail.guard`.
  (Kernel cost: closing `(if false = true then X else Y) = (if … then X' else Y)`
  by `rfl` makes the kernel compare `X` with `X'` argument-wise before it
  reduces `ite`, unfolding the guarded and real stores; rewrite with `if_neg`.)

Premises: none.
-/
import Fl4Proofs.P2.AccessIo
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1

section
variable {S : Type} {st : machine.Store S} {R W : U64 → Prop} [L : LawfulStore st]

theorem zero_lt_nmr : (0#u64 : U64) < msg.N_MSG_REGISTERS := by rw [n_msg_regs]; decide

theorem one_lt_nmr : (1#u64 : U64) < msg.N_MSG_REGISTERS := by rw [n_msg_regs]; decide

/-- **`ioport.invocation_ok`**, run-relative: the CSpace walk (`lookup_slot`'s
hypotheses), the found slot, the IPC buffer word and slot, register `R10`. -/
theorem ioport.invocation_ok.guard {s : S} {t cptr : U64} {info : msginfo.MessageInfo} {b : Bool}
  (C : U64 → Prop) {sl : U64}
  (hsl : obj.Tcb.slot t layout.tcb.SLOT_CTABLE = ok sl)
  (hR0 : R sl) (hR8 : R (core.num.U64.wrapping_add sl 8#u64))
  (hRc : ∀ p off p' r' gs' g', C p → obj.Slot.cap st (cnSlot p off) s = ok (.CNode p' r' gs' g') →
    R (cnSlot p off) ∧ R (core.num.U64.wrapping_add (cnSlot p off) 8#u64))
  (hcl : ∀ p off p' r' gs' g', C p → obj.Slot.cap st (cnSlot p off) s = ok (.CNode p' r' gs' g') → C p')
  (hroot : ∀ p r gs g, obj.Slot.cap st sl s = ok (.CNode p r gs g) → C p)
  (hRf : ∀ x, cspace.lookup_slot st s t cptr = ok (.Ok x) →
    R x.slot ∧ R (core.num.U64.wrapping_add x.slot 8#u64))
  (hib : R (core.num.U64.wrapping_add t 3512#u64))
  (hbs : ∀ bsl, obj.Tcb.slot t layout.tcb.SLOT_BUFFER = ok bsl →
    R bsl ∧ R (core.num.U64.wrapping_add bsl 8#u64))
  (hr10 : R (regA t layout.reg.R10))
  (h : ioport.invocation_ok st s t cptr info = ok b) :
  ioport.invocation_ok (PathObl.guard st R W) s t cptr info = ok b := by
  have n0 := zero_lt_nmr
  unfold ioport.invocation_ok at h ⊢
  revert h
  refine tr_bind_same (fun size _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  refine tr_bind (fun res hres _ => cspace.lookup_slot.guard C hsl hR0 hR8 hRc hcl hroot
    (fun x e => hRf x (e ▸ hres)) hres) (fun res hres => ?_)
  cases res with
  | Err e => exact fun h => h
  | Ok r1 =>
    obtain ⟨h0, h8⟩ := hRf r1 hres
    dsimp only
    rw [obj.Slot.cap.guard _ s h0 h8]
    refine tr_bind_same (fun c _ => ?_)
    cases c <;> try exact fun h => h
    obtain ⟨bsl, hbsl⟩ := buffer_slot_ok t
    rw [msg.lookup_ipc_buffer.guard s false t hbsl hib (hbs bsl hbsl).1 (hbs bsl hbsl).2]
    have e : ∀ bf, msg.syscall_arg (PathObl.guard st R W) s t bf 0#u64 = msg.syscall_arg st s t bf 0#u64 :=
      fun bf => msg.syscall_arg.guard_lt s t bf 0#u64 n0
        (fun r hr => by rw [msg_register_zero] at hr; cases ok_inj_ff hr; exact hr10)
    simp only [e]
    exact fun h => h

/-! ## `ioport.decode` on an I/O port cap

`ioport.decode` is one 27-arm match on the cap. Unfolding it in a proof puts
every arm (and its auxiliary matcher) in the goal; the kernel then rechecks
those terms at each rewrite step. Instead `decode_ioport_eq` states, by `rfl`,
the I/O port arm alone as `ioArm`, whose two port tails are `ioInTail` /
`ioOutTail`; each is guarded separately. -/

/-- The in-port tail of the I/O port arm, after the `allowed` check. -/
def ioInTail {A : Type} (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A)
    (ct port size : U64) (call : Bool) : Result ((core.result.Result Unit error.Exc) × S × A) := do
  let s1 ← sched.set_thread_state m s ct sched.TS_RESTART
  let (v, a1) ← ar.port_in a port size
  let s2 ←
    if call
    then
      do
      let b ← msg.lookup_ipc_buffer m s1 true ct
      let s3 ← obj.Tcb.set_reg m ct s1 layout.reg.BADGE 0#u64
      let (n, s4) ← msg.set_mr m s3 ct b 0#u64 v
      let mi ← msginfo.MessageInfo.new 0#u64 0#u64 0#u64 n
      msg.set_msg_info m s4 ct mi
    else ok s1
  let s3 ← sched.set_thread_state m s2 ct sched.TS_RUNNING
  ok (core.result.Result.Ok (), s3, a1)

/-- The out-port tail of the I/O port arm, after the `allowed` check. -/
def ioOutTail {A : Type} (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A)
    (ct port size raw : U64) : Result ((core.result.Result Unit error.Exc) × S × A) := do
  let data ←
    if size = 1#u64
    then ok (raw &&& 255#u64)
    else
      if size = 2#u64
      then ok (raw &&& 65535#u64)
      else ok (raw &&& 4294967295#u64)
  let s1 ← sched.set_thread_state m s ct sched.TS_RESTART
  let a1 ← ar.port_out a port size data
  ok (core.result.Result.Ok (), s1, a1)

/-- The I/O port arm of `ioport.decode`, tails folded. -/
def ioArm {A : Type} (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A) (lbl length : U64)
    (first last : U64) (buf : U64) (call : Bool) : Result ((core.result.Result Unit error.Exc) × S × A) := do
  let ct ← sched.cur_thread m s
  let size ← ioport.port_size lbl
  if size = 0#u64
  then let r ← error.illegal Unit
       ok (r, s, a)
  else
    let is_in ← ioport.is_port_in lbl
    if is_in
    then
      if length < 1#u64
      then let r ← error.truncated Unit
           ok (r, s, a)
      else
        let i ← msg.syscall_arg m s ct buf 0#u64
        let port ← lift (i &&& 65535#u64)
        let r ← ioport.allowed first last port size
        let cf ← core.result.Result.Insts.CoreOpsTry.branch r
        match cf with
        | core.ops.control_flow.ControlFlow.Continue _ => ioInTail m ar s a ct port size call
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r1 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame error.Exc) residual
          ok (r1, s, a)
    else
      if length < 2#u64
      then let r ← error.truncated Unit
           ok (r, s, a)
      else
        let i ← msg.syscall_arg m s ct buf 0#u64
        let port ← lift (i &&& 65535#u64)
        let raw ← msg.syscall_arg m s ct buf 1#u64
        let r ← ioport.allowed first last port size
        let cf ← core.result.Result.Insts.CoreOpsTry.branch r
        match cf with
        | core.ops.control_flow.ControlFlow.Continue _ => ioOutTail m ar s a ct port size raw
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r1 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame error.Exc) residual
          ok (r1, s, a)

theorem decode_ioport_eq {A : Type} (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A)
    (lbl length first last x : U64) (call : Bool) (buf : U64) :
    ioport.decode m ar s a lbl length (.IoPort first last x) call buf =
      ioArm m ar s a lbl length first last buf call := rfl

theorem ioOutTail.guard {A : Type} (ar : machine.Arch A) {s : S} (a : A) {ct : U64} (port size raw : U64)
    (hn : NodeSt (L := L) R W s) (hi : IoRd (L := L) R W s ct) :
    ioOutTail (PathObl.guard st R W) ar s a ct port size raw = ioOutTail st ar s a ct port size raw := by
  unfold ioOutTail
  refine bind_guard_congr rfl (fun data _ => ?_)
  rw [sts_io hn hi]

theorem ioInTail.guard {A : Type} (ar : machine.Arch A) {s : S} (a : A) {ct : U64} (port size : U64)
    (call : Bool) (hn : NodeSt (L := L) R W s) (hda : ActDisj (L := L) s ct) (hi : IoRd (L := L) R W s ct) :
    ioInTail (PathObl.guard st R W) ar s a ct port size call = ioInTail st ar s a ct port size call := by
  unfold ioInTail
  rw [sts_io hn hi]
  refine bind_guard_congr rfl (fun s1 hs1 => ?_)
  obtain ⟨hi1, hn1, -⟩ := sts_keep hi hn hda hs1
  refine bind_guard_congr rfl (fun va _ => ?_)
  obtain ⟨v, a1⟩ := va
  simp only [Aeneas.Std.uncurry_apply_pair]
  obtain ⟨sl, hsl⟩ := buffer_slot_ok ct
  have rB := lt384 (r := layout.reg.BADGE) (Or.inr (Or.inr (Or.inl rfl)))
  have rM := lt384 (r := layout.reg.MSG_INFO) (Or.inr (Or.inr (Or.inr rfl)))
  have rR := lt384 (r := layout.reg.R10) (Or.inl rfl)
  refine bind_guard_congr ?_ (fun s2 hs2 => ?_)
  · cases call
    · -- not `rfl`: the kernel would compare the two `then` branches (guarded vs real
      -- store) argument-wise before reducing `ite`, unfolding both stores deeply
      rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
    · rw [if_pos rfl, if_pos rfl]
      rw [msg.lookup_ipc_buffer.guard s1 true _ hsl hi1.ib (hi1.bs sl hsl).1 (hi1.bs sl hsl).2]
      refine bind_guard_congr rfl (fun b _ => ?_)
      rw [obj.Tcb.set_reg.guard _ s1 _ _ (hi1.regW _ rB), set_reg_ok']
      simp only [bind_ok]
      rw [msg.set_mr.guard0 _ _ b v (hi1.regW _ rR)]
      refine bind_guard_congr rfl (fun ns _ => ?_)
      obtain ⟨n, s4⟩ := ns
      simp only [Aeneas.Std.uncurry_apply_pair]
      refine bind_guard_congr rfl (fun mi _ => ?_)
      exact msg.set_msg_info.guard s4 _ mi (hi1.regW _ rM)
  · have k2 : IoRd (L := L) R W s2 ct ∧ NodeSt (L := L) R W s2 := by
      cases call
      · rw [if_neg Bool.false_ne_true] at hs2
        cases ok_inj_ff hs2; exact ⟨hi1, hn1⟩
      · rw [if_pos rfl] at hs2
        obtain ⟨b, -, hs2⟩ := bind_eq_ok hs2
        rw [set_reg_ok'] at hs2; simp only [bind_ok] at hs2
        rw [set_mr0_ok] at hs2; simp only [bind_ok, Aeneas.Std.uncurry_apply_pair] at hs2
        obtain ⟨mi, -, hs2⟩ := bind_eq_ok hs2
        unfold msg.set_msg_info at hs2
        obtain ⟨w, -, hs2⟩ := bind_eq_ok hs2
        rw [set_reg_ok'] at hs2
        cases ok_inj_ff hs2
        exact ⟨((hi1.wr_reg rB).wr_reg rR).wr_reg rM, hn1.wr.wr.wr⟩
    rw [sts_io k2.2 k2.1]

/-- **`ioport.decode`** on an I/O port cap: the current thread's registers,
state, SC/release-queue words, IPC buffer word and slot (`IoRd`) and the node's
`CUR_THREAD` / `SCHED_ACTION` words (`NodeSt`, `ActDisj`). -/
theorem ioport.decode.guard {A : Type} (ar : machine.Arch A) (s : S) (a : A) (lbl length : U64)
    (first last x : U64) (call : Bool) (buf : U64)
    (hn : NodeSt (L := L) R W s) (hda : ActDisj (L := L) s (L.curW s)) (hi : IoRd (L := L) R W s (L.curW s)) :
    ioport.decode (PathObl.guard st R W) ar s a lbl length (.IoPort first last x) call buf =
      ioport.decode st ar s a lbl length (.IoPort first last x) call buf := by
  have r10 := hi.regR _ (lt384 (Or.inl rfl))
  have r8 := hi.regR _ (lt384 (Or.inr (Or.inl rfl)))
  have e0 : ∀ bf, msg.syscall_arg (PathObl.guard st R W) s (L.curW s) bf 0#u64 =
      msg.syscall_arg st s (L.curW s) bf 0#u64 := fun bf =>
    msg.syscall_arg.guard_lt s _ bf 0#u64 zero_lt_nmr
      (fun r hr => by rw [msg_register_zero] at hr; cases ok_inj_ff hr; exact r10)
  have e1 : ∀ bf, msg.syscall_arg (PathObl.guard st R W) s (L.curW s) bf 1#u64 =
      msg.syscall_arg st s (L.curW s) bf 1#u64 := fun bf =>
    msg.syscall_arg.guard_lt s _ bf 1#u64 one_lt_nmr
      (fun r hr => by rw [msg_register_one] at hr; cases ok_inj_ff hr; exact r8)
  have ei : ∀ port size call, ioInTail (PathObl.guard st R W) ar s a (L.curW s) port size call =
      ioInTail st ar s a (L.curW s) port size call := fun port size call =>
    ioInTail.guard ar a port size call hn hda hi
  have eo : ∀ port size raw, ioOutTail (PathObl.guard st R W) ar s a (L.curW s) port size raw =
      ioOutTail st ar s a (L.curW s) port size raw := fun port size raw =>
    ioOutTail.guard ar a port size raw hn hi
  rw [decode_ioport_eq, decode_ioport_eq]
  unfold ioArm
  rw [sched.cur_thread.guard s hn.1, cur_thread_ok s]
  simp only [bind_ok, e0, e1, ei, eo]

end

end Fl4Proofs.P2.PathObl
