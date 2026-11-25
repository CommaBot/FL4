/-
# P2: guarded-store lemma for `handle_invocation` on the I/O port run (line p2io)

`syscall.handle_ioport_local` runs `handle_invocation` only after
`ioport.invocation_ok` passed at the same state, with no extra caps. That run
is narrow: the CSpace lookup finds an I/O port cap, the extra-cap lookup reads
nothing, and `ioport.decode` cannot fail (it repeats `invocation_ok`'s checks
on the same words), so `reply_error` (which writes the user IPC buffer) is
never entered.

* `inv_true`: what a passing `invocation_ok` fixes (the found slot, the cap,
  the buffer, the length, the port size and direction, the `allowed` check);
* `decode_inv_ioport_eq`: `decode_invocation` on an I/O port cap is
  `ioport.decode` (by `rfl`, the 27-arm match not unfolded in a proof);
* `ioArm_fst`: under `inv_true`'s facts the decode answers `Ok`;
* `ioArm_keep`: the decode's writes keep `IoRd` / `NodeSt` / `ActDisj`;
* `extra_zero_ok`: no extra caps: the lookup answers `Ok`;
* `syscall.handle_invocation.guard_io`, run-relative: the guarded run ends as
  the real one, and answers `Ok`; `syscall.after_invocation.guard_ok`.

Premises: none.
-/
import Fl4Proofs.P2.AccessIoDec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1

section
variable {S : Type} {st : machine.Store S} {R W : U64 → Prop} [L : LawfulStore st]

/-- The `length` `handle_invocation` / `invocation_ok` compute. -/
abbrev ioLen (info : msginfo.MessageInfo) (buf : U64) : Result U64 :=
  if info.length > msg.N_MSG_REGISTERS
  then if buf = 0#u64 then ok msg.N_MSG_REGISTERS else ok info.length
  else ok info.length

/-- **A passing `invocation_ok`**: its lookup, cap, buffer, length, port size
and direction, and the `allowed` check on the port it reads. -/
theorem inv_true {s : S} {t cptr : U64} {info : msginfo.MessageInfo}
    (h : ioport.invocation_ok st s t cptr info = ok true) :
    ∃ r1 f l x buf len size b i1,
      cspace.lookup_slot st s t cptr = ok (.Ok r1) ∧
      obj.Slot.cap st r1.slot s = ok (.IoPort f l x) ∧
      msg.lookup_ipc_buffer st s false t = ok buf ∧ ioLen info buf = ok len ∧
      ioport.port_size info.label = ok size ∧ size ≠ 0#u64 ∧
      ioport.is_port_in info.label = ok b ∧ ¬ len < (if b then 1#u64 else 2#u64) ∧
      msg.syscall_arg st s t buf 0#u64 = ok i1 ∧
      ioport.allowed f l (i1 &&& 65535#u64) size = ok (.Ok ()) := by
  unfold ioport.invocation_ok at h
  obtain ⟨size, hsz, h⟩ := bind_eq_ok h
  by_cases hz : size = 0#u64
  · rw [if_pos hz] at h; cases ok_inj_ff h
  rw [if_neg hz] at h
  obtain ⟨res, hres, h⟩ := bind_eq_ok h
  cases res with
  | Err e => cases ok_inj_ff h
  | Ok r1 =>
    dsimp only at h
    split at h
    · cases ok_inj_ff h
    obtain ⟨c, hc, h⟩ := bind_eq_ok h
    cases c <;> try cases ok_inj_ff h
    rename_i f l x
    obtain ⟨buf, hbuf, h⟩ := bind_eq_ok h
    obtain ⟨len, hlen, h⟩ := bind_eq_ok h
    obtain ⟨b, hb, h⟩ := bind_eq_ok h
    obtain ⟨i, hi, h⟩ := bind_eq_ok h
    have hi' : i = if b then 1#u64 else 2#u64 := by
      cases b
      · rw [if_neg Bool.false_ne_true] at hi ⊢; exact (ok_inj_ff hi).symm
      · rw [if_pos rfl] at hi ⊢; exact (ok_inj_ff hi).symm
    subst hi'
    by_cases hl : len < (if b then 1#u64 else 2#u64)
    · rw [if_pos hl] at h; cases ok_inj_ff h
    rw [if_neg hl] at h
    obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
    simp only [lift, bind_ok] at h
    obtain ⟨r2, hr2, h⟩ := bind_eq_ok h
    cases r2 with
    | Err e => simp [core.result.Result.is_ok] at h
    | Ok u =>
      cases u
      exact ⟨r1, f, l, x, buf, len, size, b, i1, hres, hc, hbuf, hlen, hsz, hz, hb, hl, hi1, hr2⟩

/-- `decode_invocation` on an I/O port cap. -/
theorem decode_inv_ioport_eq {A : Type} (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A)
    (lbl length : U64) (slot : obj.Slot) (first last x : U64) (block call cd fp : Bool) (buf : U64)
    (extra : Array obj.Slot 3#usize) :
    syscall.decode_invocation m ar s a lbl length slot (.IoPort first last x) block call cd fp buf extra =
      Std.bind (sched.cur_thread m s) (fun _ =>
        ioport.decode m ar s a lbl length (.IoPort first last x) call buf) := rfl

theorem ioInTail_fst {A : Type} (ar : machine.Arch A) {s : S} {a : A} {ct port size : U64} {call : Bool}
    {y : (core.result.Result Unit error.Exc) × S × A}
    (h : ioInTail st ar s a ct port size call = ok y) : y.1 = .Ok () := by
  unfold ioInTail at h
  obtain ⟨s1, -, h⟩ := bind_eq_ok h
  obtain ⟨⟨v, a1⟩, -, h⟩ := bind_eq_ok h
  try simp only [Aeneas.Std.uncurry_apply_pair] at h
  obtain ⟨s2, -, h⟩ := bind_eq_ok h
  obtain ⟨s3, -, h⟩ := bind_eq_ok h
  rw [← ok_inj_ff h]

theorem ioOutTail_fst {A : Type} (ar : machine.Arch A) {s : S} {a : A} {ct port size raw : U64}
    {y : (core.result.Result Unit error.Exc) × S × A}
    (h : ioOutTail st ar s a ct port size raw = ok y) : y.1 = .Ok () := by
  unfold ioOutTail at h
  obtain ⟨d, -, h⟩ := bind_eq_ok h
  obtain ⟨s1, -, h⟩ := bind_eq_ok h
  obtain ⟨a1, -, h⟩ := bind_eq_ok h
  rw [← ok_inj_ff h]

theorem branch_ok_unit :
    core.result.Result.Insts.CoreOpsTry.branch (core.result.Result.Ok () : core.result.Result Unit error.Exc) =
      ok (core.ops.control_flow.ControlFlow.Continue ()) := by
  simp [core.result.Result.Insts.CoreOpsTry.branch]

/-- **The decode answers `Ok`** under `invocation_ok`'s facts at the same state. -/
theorem ioArm_fst {A : Type} (ar : machine.Arch A) {s : S} {a : A} {lbl len f l buf size i1 : U64}
    {b call : Bool} {y : (core.result.Result Unit error.Exc) × S × A}
    (hsz : ioport.port_size lbl = ok size) (hz : size ≠ 0#u64) (hb : ioport.is_port_in lbl = ok b)
    (hl : ¬ len < (if b then 1#u64 else 2#u64))
    (hi1 : msg.syscall_arg st s (L.curW s) buf 0#u64 = ok i1)
    (hal : ioport.allowed f l (i1 &&& 65535#u64) size = ok (.Ok ()))
    (h : ioArm st ar s a lbl len f l buf call = ok y) : y.1 = .Ok () := by
  have e0 := hi1
  unfold ioArm at h
  rw [cur_thread_ok] at h
  simp only [bind_ok] at h
  rw [hsz] at h; simp only [bind_ok] at h
  rw [if_neg hz] at h
  rw [hb] at h; simp only [bind_ok] at h
  cases b
  · rw [if_neg Bool.false_ne_true] at h hl
    rw [if_neg hl] at h
    rw [e0] at h; simp only [lift, bind_ok] at h
    obtain ⟨raw, -, h⟩ := bind_eq_ok h
    rw [hal] at h; simp only [bind_ok] at h
    rw [branch_ok_unit] at h; simp only [bind_ok] at h
    exact ioOutTail_fst ar h
  · rw [if_pos rfl] at h hl
    rw [if_neg hl] at h
    rw [e0] at h; simp only [lift, bind_ok] at h
    rw [hal] at h; simp only [bind_ok] at h
    rw [branch_ok_unit] at h; simp only [bind_ok] at h
    exact ioInTail_fst ar h

/-- The three facts the decode's writes keep. -/
abbrev IoK (R W : U64 → Prop) (s : S) (t : U64) : Prop :=
  IoRd (L := L) R W s t ∧ NodeSt (L := L) R W s ∧ ActDisj (L := L) s t

theorem ioInTail_keep {A : Type} (ar : machine.Arch A) {s : S} {a : A} {ct port size : U64} {call : Bool}
    {y : (core.result.Result Unit error.Exc) × S × A} (hk : IoK (L := L) R W s ct)
    (h : ioInTail st ar s a ct port size call = ok y) : IoK (L := L) R W y.2.1 ct := by
  obtain ⟨hi, hn, hda⟩ := hk
  unfold ioInTail at h
  obtain ⟨s1, hs1, h⟩ := bind_eq_ok h
  obtain ⟨hi1, hn1, hda1⟩ := sts_keep hi hn hda hs1
  obtain ⟨⟨v, a1⟩, -, h⟩ := bind_eq_ok h
  try simp only [Aeneas.Std.uncurry_apply_pair] at h
  obtain ⟨s2, hs2, h⟩ := bind_eq_ok h
  have rB := lt384 (r := layout.reg.BADGE) (Or.inr (Or.inr (Or.inl rfl)))
  have rM := lt384 (r := layout.reg.MSG_INFO) (Or.inr (Or.inr (Or.inr rfl)))
  have rR := lt384 (r := layout.reg.R10) (Or.inl rfl)
  have k2 : IoK (L := L) R W s2 ct := by
    cases call
    · rw [if_neg Bool.false_ne_true] at hs2
      cases ok_inj_ff hs2; exact ⟨hi1, hn1, hda1⟩
    · rw [if_pos rfl] at hs2
      obtain ⟨b, -, hs2⟩ := bind_eq_ok hs2
      rw [set_reg_ok'] at hs2; simp only [bind_ok] at hs2
      rw [set_mr0_ok] at hs2; simp only [bind_ok, Aeneas.Std.uncurry_apply_pair] at hs2
      obtain ⟨mi, -, hs2⟩ := bind_eq_ok hs2
      unfold msg.set_msg_info at hs2
      obtain ⟨w, -, hs2⟩ := bind_eq_ok hs2
      rw [set_reg_ok'] at hs2
      cases ok_inj_ff hs2
      exact ⟨((hi1.wr_reg rB).wr_reg rR).wr_reg rM, hn1.wr.wr.wr, ActDisj.wr (ActDisj.wr (ActDisj.wr hda1))⟩
  obtain ⟨s3, hs3, h⟩ := bind_eq_ok h
  rw [← ok_inj_ff h]
  exact sts_keep k2.1 k2.2.1 k2.2.2 hs3

theorem ioOutTail_keep {A : Type} (ar : machine.Arch A) {s : S} {a : A} {ct port size raw : U64}
    {y : (core.result.Result Unit error.Exc) × S × A} (hk : IoK (L := L) R W s ct)
    (h : ioOutTail st ar s a ct port size raw = ok y) : IoK (L := L) R W y.2.1 ct := by
  unfold ioOutTail at h
  obtain ⟨d, -, h⟩ := bind_eq_ok h
  obtain ⟨s1, hs1, h⟩ := bind_eq_ok h
  obtain ⟨a1, -, h⟩ := bind_eq_ok h
  rw [← ok_inj_ff h]
  exact sts_keep hk.1 hk.2.1 hk.2.2 hs1

/-- **The decode's writes keep `IoK`.** -/
theorem ioArm_keep {A : Type} (ar : machine.Arch A) {s : S} {a : A} {lbl len f l buf : U64} {call : Bool}
    {y : (core.result.Result Unit error.Exc) × S × A} (hk : IoK (L := L) R W s (L.curW s))
    (h : ioArm st ar s a lbl len f l buf call = ok y) : IoK (L := L) R W y.2.1 (L.curW s) := by
  unfold ioArm at h
  rw [cur_thread_ok] at h
  simp only [bind_ok] at h
  obtain ⟨size, -, h⟩ := bind_eq_ok h
  split at h
  · obtain ⟨r, -, h⟩ := bind_eq_ok h; rw [← ok_inj_ff h]; exact hk
  obtain ⟨b, -, h⟩ := bind_eq_ok h
  split at h
  · split at h
    · obtain ⟨r, -, h⟩ := bind_eq_ok h; rw [← ok_inj_ff h]; exact hk
    obtain ⟨i, -, h⟩ := bind_eq_ok h
    simp only [lift, bind_ok] at h
    obtain ⟨r, -, h⟩ := bind_eq_ok h
    obtain ⟨cf, -, h⟩ := bind_eq_ok h
    split at h
    · exact ioInTail_keep ar hk h
    · obtain ⟨r, -, h⟩ := bind_eq_ok h; rw [← ok_inj_ff h]; exact hk
  · split at h
    · obtain ⟨r, -, h⟩ := bind_eq_ok h; rw [← ok_inj_ff h]; exact hk
    obtain ⟨i, -, h⟩ := bind_eq_ok h
    simp only [lift, bind_ok] at h
    obtain ⟨raw, -, h⟩ := bind_eq_ok h
    obtain ⟨r, -, h⟩ := bind_eq_ok h
    obtain ⟨cf, -, h⟩ := bind_eq_ok h
    split at h
    · exact ioOutTail_keep ar hk h
    · obtain ⟨r, -, h⟩ := bind_eq_ok h; rw [← ok_inj_ff h]; exact hk

/-- No extra caps: the lookup answers `Ok`. -/
theorem extra_zero_ok (s : S) (t buf : U64) (info : msginfo.MessageInfo) (h0 : info.extra_caps = 0#u64) :
    ipc.lookup_extra_caps st s t buf info = ok (.Ok ipc.NO_EXTRA_CAPS) := by
  unfold ipc.lookup_extra_caps
  split_ifs
  · rfl
  · rw [h0]
    unfold ipc.lookup_extra_caps_loop
    rw [loop]
    have e : ipc.lookup_extra_caps_loop.body st s t buf 0#u64 ipc.NO_EXTRA_CAPS 0#u64 =
        ok (ControlFlow.done (.Ok ipc.NO_EXTRA_CAPS)) := by
      unfold ipc.lookup_extra_caps_loop.body
      simp
    simp only [e, bind_ok]

/-- **`handle_invocation` on the I/O port run**, run-relative: after a passing
`invocation_ok` at the same state with no extra caps, the guarded run ends as
the real one, and it answers `Ok`. Reads: the node's `CUR_THREAD`, the current
thread's `MSG_INFO` and the words of `invocation_ok.guard` (the CSpace walk,
the found slot), and `IoK` (the decode's and the restart tail's words). -/
theorem syscall.handle_invocation.guard_io {A : Type} (ar : machine.Arch A) {s : S} {a : A}
    {cptr : U64} {info : msginfo.MessageInfo} {call blocking cd fp : Bool}
    {y : (core.result.Result Unit error.Exc) × S × A} (C : U64 → Prop) {sl : U64}
    (hct : R (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD))
    (hmi : msg.msg_info st s (L.curW s) = ok info) (hRmi : R (regA (L.curW s) layout.reg.MSG_INFO))
    (hx : info.extra_caps = 0#u64)
    (hinv : ioport.invocation_ok st s (L.curW s) cptr info = ok true)
    (hsl : obj.Tcb.slot (L.curW s) layout.tcb.SLOT_CTABLE = ok sl)
    (hR0 : R sl) (hR8 : R (core.num.U64.wrapping_add sl 8#u64))
    (hRc : ∀ p off p' r' gs' g', C p → obj.Slot.cap st (cnSlot p off) s = ok (.CNode p' r' gs' g') →
      R (cnSlot p off) ∧ R (core.num.U64.wrapping_add (cnSlot p off) 8#u64))
    (hcl : ∀ p off p' r' gs' g', C p → obj.Slot.cap st (cnSlot p off) s = ok (.CNode p' r' gs' g') → C p')
    (hroot : ∀ p r gs g, obj.Slot.cap st sl s = ok (.CNode p r gs g) → C p)
    (hRf : ∀ x, cspace.lookup_slot st s (L.curW s) cptr = ok (.Ok x) →
      R x.slot ∧ R (core.num.U64.wrapping_add x.slot 8#u64))
    (hk : IoK (L := L) R W s (L.curW s))
    (h : syscall.handle_invocation st ar s a call blocking cd fp cptr = ok y) :
    syscall.handle_invocation (PathObl.guard st R W) ar s a call blocking cd fp cptr = ok y ∧
      y.1 = .Ok () := by
  obtain ⟨r1, f, l, x, buf, len, size, b, i1, hres, hc, hbuf, hlen, hsz, hz, hb, hl, hi1, hal⟩ :=
    inv_true hinv
  have hlen' : (if info.length > msg.N_MSG_REGISTERS
      then (if buf = 0#u64 then ok msg.N_MSG_REGISTERS else ok info.length)
      else ok info.length) = ok len := hlen
  have rB := lt384 (r := layout.reg.BADGE) (Or.inr (Or.inr (Or.inl rfl)))
  have rM := lt384 (r := layout.reg.MSG_INFO) (Or.inr (Or.inr (Or.inr rfl)))
  obtain ⟨h0, h8⟩ := hRf r1 hres
  obtain ⟨bsl, hbsl⟩ := buffer_slot_ok (L.curW s)
  unfold syscall.handle_invocation at h ⊢
  rw [cur_thread_ok] at h
  rw [sched.cur_thread.guard s hct, cur_thread_ok]
  simp only [bind_ok, bind_tc_ok] at h ⊢
  rw [hmi] at h
  rw [msg.msg_info.guard s _ hRmi, hmi]
  simp only [bind_ok, bind_tc_ok] at h ⊢
  rw [hres] at h
  rw [cspace.lookup_slot.guard C hsl hR0 hR8 hRc hcl hroot (fun x e => hRf x (e ▸ hres)) hres]
  simp only [bind_ok, bind_tc_ok] at h ⊢
  rw [hc] at h
  rw [obj.Slot.cap.guard _ s h0 h8, hc]
  simp only [bind_ok, bind_tc_ok] at h ⊢
  rw [hbuf] at h
  rw [msg.lookup_ipc_buffer.guard s false _ hbsl hk.1.ib (hk.1.bs bsl hbsl).1 (hk.1.bs bsl hbsl).2, hbuf]
  simp only [bind_ok, bind_tc_ok] at h ⊢
  rw [extra_zero_ok s _ buf info hx] at h
  rw [ipc.lookup_extra_caps.guard_zero s _ buf info hx, extra_zero_ok (st := st) s _ buf info hx]
  simp only [bind_ok, bind_tc_ok] at h ⊢
  rw [hlen'] at h
  rw [hlen']
  simp only [bind_ok, bind_tc_ok] at h ⊢
  rw [decode_inv_ioport_eq] at h
  rw [decode_inv_ioport_eq]
  rw [cur_thread_ok] at h
  rw [sched.cur_thread.guard s hct, cur_thread_ok]
  simp only [bind_ok, bind_tc_ok] at h ⊢
  rw [ioport.decode.guard ar s a _ _ f l x call buf hk.2.1 hk.2.2 hk.1]
  obtain ⟨⟨r3, s1, a1⟩, hd, h⟩ := bind_eq_ok h
  rw [hd]
  rw [decode_ioport_eq] at hd
  have e3 : r3 = .Ok () := ioArm_fst ar hsz hz hb hl hi1 hal hd
  have k1 := ioArm_keep ar hk hd
  simp only at k1
  subst e3
  simp only [bind_ok, bind_tc_ok] at h ⊢
  try simp only [Aeneas.Std.uncurry_apply_pair] at h ⊢
  have hy : y.1 = .Ok () := by
    obtain ⟨i, -, h⟩ := bind_eq_ok h
    split at h
    · obtain ⟨s2, -, h⟩ := bind_eq_ok h
      obtain ⟨s3, -, h⟩ := bind_eq_ok h
      rw [← ok_inj_ff h]
    · rw [← ok_inj_ff h]
  refine ⟨?_, hy⟩
  rw [obj.Tcb.state.guard _ s1 k1.1.stR]
  revert h
  refine tr_bind_same (fun i _ => ?_)
  refine tr_ite (fun _ => ?_) (fun _ h => h)
  refine tr_bind (fun s2 hs2 _ => ?_) (fun s2 hs2 => ?_)
  · cases call
    · rw [if_neg Bool.false_ne_true] at hs2 ⊢; exact hs2
    · rw [if_pos rfl] at hs2 ⊢
      rw [msg.reply_success_empty.guard s1 _ (k1.1.regW _ rB) (k1.1.regW _ rM)]
      exact hs2
  · have k2 : IoK (L := L) R W s2 (L.curW s) := by
      cases call
      · rw [if_neg Bool.false_ne_true] at hs2
        cases ok_inj_ff hs2; exact k1
      · rw [if_pos rfl] at hs2
        unfold msg.reply_success_empty at hs2
        rw [set_reg_ok'] at hs2; simp only [bind_ok] at hs2
        obtain ⟨mi, -, hs2⟩ := bind_eq_ok hs2
        unfold msg.set_msg_info at hs2
        obtain ⟨w, -, hs2⟩ := bind_eq_ok hs2
        rw [set_reg_ok'] at hs2
        cases ok_inj_ff hs2
        exact ⟨(k1.1.wr_reg rB).wr_reg rM, k1.2.1.wr.wr, ActDisj.wr (ActDisj.wr k1.2.2)⟩
    rw [sts_io k2.2.1 k2.1]
    exact fun h => h

/-- `after_invocation` of an `Ok` invocation: no access, on any store. -/
theorem syscall.after_invocation.ok_eq {A : Type} (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A) :
    syscall.after_invocation m ar s a (.Ok ()) = ok (true, s, a) := rfl

end

end Fl4Proofs.P2.PathObl
