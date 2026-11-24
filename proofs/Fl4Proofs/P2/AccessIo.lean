/-
# P2: guarded-store lemmas for the I/O port invocation (line p2io)

As `P2/AccessCSpace.lean` / `P2/AccessSched.lean`, for `PathObl.acc` of
`handle_ioport_local`: on `guard st R W` a callee answers as on `st`, given
the words it reads and writes. Hypotheses are stated at the callee's entry
state with P1's addresses (`stA`, `scA`, `maxA`, `inqA`, `regA`, node words);
a hypothesis may name a word a given run does not touch.

* thread state: `sched.is_runnable`, `sporadic.sc_active`,
  `sched.is_schedulable`, `sched.schedule_tcb` (the node's `CUR_THREAD` and
  `SCHED_ACTION`), `sched.set_thread_state`;
* replies: `msg.set_msg_info`, `msg.set_mr` (message register 0),
  `msg.reply_success_empty`, `msg.syscall_arg` below `N_MSG_REGISTERS`;
* `IoRd` / `NodeSt` / `ActDisj`: the current thread's and node words the
  I/O port arm touches, kept by its writes (`sts_keep`, `IoRd.wr_reg`);
  `ioport.decode.guard` and `ioport.invocation_ok.guard` are in
  `P2/AccessIoDec.lean`.

Premises: none.
-/
import Fl4Proofs.P2.AccessCSpace
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1

section
variable {S : Type} {st : machine.Store S} {R W : U64 → Prop} {gS : machine.Store S} [GRd gS st R] [GWr gS st W] [L : LawfulStore st]

theorem state_ok' (s : S) (t : U64) : obj.Tcb.state st t s = ok (L.mem s (stA t)) := by
  unfold obj.Tcb.state stA; simp only [lift, bind_ok, L.read_eq]

theorem set_state_ok' (s : S) (t v : U64) : obj.Tcb.set_state st t s v = ok (L.wr s (stA t) v) := by
  unfold obj.Tcb.set_state stA; simp only [lift, bind_ok, L.write_eq]

theorem set_reg_ok' (s : S) (t r v : U64) : obj.Tcb.set_reg st t s r v = ok (L.wr s (regA t r) v) := by
  unfold obj.Tcb.set_reg regA; simp only [lift, bind_ok, L.write_eq]

/-- A write keeps the node's addresses. -/
theorem nd_wr (s : S) (a v o : U64) :
    L.nodeAt (L.wr s a v) (L.cpu (L.wr s a v)) o = L.nodeAt s (L.cpu s) o := by
  rw [LawfulStore.cpu_wr, nodeAt_of_ksb (L.ksb_wr _ _ _)]

/-- Two different words of one TCB. -/
theorem tcb_wr_other {s : S} {t K1 K2 v : U64} (hT : TcbAddr t) (h1 : K1.val < 4096) (h18 : K1.val % 8 = 0)
    (h2 : K2.val < 4096) (h28 : K2.val % 8 = 0) (hne : K1.val ≠ K2.val) :
    L.mem (L.wr s (core.num.U64.wrapping_add t K1) v) (core.num.U64.wrapping_add t K2) =
      L.mem s (core.num.U64.wrapping_add t K2) := by
  refine mem_wr_ne' (field_aligned hT h1 h18) (field_aligned hT h2 h28) (fun e => hne ?_)
  have := congrArg UScalar.val e
  rw [tcb_wadd_val hT h1, tcb_wadd_val hT h2] at this
  omega

/-- A register write keeps the SC word. -/
theorem reg_wr_sc {s : S} {t r v : U64} (hT : TcbAddr t) (hr : r.val < 384) :
    L.mem (L.wr s (regA t r) v) (scA t) = L.mem s (scA t) := by
  obtain ⟨K, hK, e⟩ := regA_eq hT hr
  rw [e]; unfold scA
  exact tcb_wr_other hT (by omega) (by omega) (by simp) (by simp) (by simp; omega)

/-- A state write keeps the SC word. -/
theorem st_wr_sc {s : S} {t v : U64} (hT : TcbAddr t) : L.mem (L.wr s (stA t) v) (scA t) = L.mem s (scA t) := by
  unfold stA scA
  exact tcb_wr_other hT (by simp [layout.tcb.STATE]) (by simp [layout.tcb.STATE]) (by simp) (by simp)
    (by simp [layout.tcb.STATE])

theorem sched.is_runnable.guard (s : S) (t : obj.Tcb) (h : R (stA t)) :
    sched.is_runnable gS s t = sched.is_runnable st s t := by
  unfold sched.is_runnable; rw [obj.Tcb.state.guard t s h]

theorem sporadic.sc_active.guard (s : S) (sc : obj.Sc) (h : R (maxA sc)) :
    sporadic.sc_active gS s sc = sporadic.sc_active st s sc := by
  unfold sporadic.sc_active; rw [obj.Sc.refill_max.guard sc s h]

theorem sched.is_schedulable.guard (s : S) (t : obj.Tcb) (h1 : R (stA t)) (h2 : R (scA t))
    (h3 : R (maxA (L.mem s (scA t)))) (h4 : R (inqA t)) :
    sched.is_schedulable gS s t = sched.is_schedulable st s t := by
  unfold sched.is_schedulable
  rw [sched.is_runnable.guard s t h1, obj.Tcb.sc.guard t s h2, tcb_sc_ok s t]
  simp only [bind_ok]
  rw [sporadic.sc_active.guard s _ h3, sched.in_release_queue.guard s t h4]

/-- The words `schedule_tcb t` touches besides `t`'s (`TcbRd`). -/
def NodeSt (R W : U64 → Prop) (s : S) : Prop :=
  R (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) ∧ R (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) ∧
    W (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION)

theorem NodeSt.wr {s : S} {a v : U64} (h : NodeSt (L := L) R W s) : NodeSt (L := L) R W (L.wr s a v) := by
  unfold NodeSt; simp only [nd_wr]; exact h

theorem sched.schedule_tcb.guard (s : S) (t : obj.Tcb) (hn : NodeSt (L := L) R W s)
    (h1 : R (stA t)) (h2 : R (scA t)) (h3 : R (maxA (L.mem s (scA t)))) (h4 : R (inqA t)) :
    sched.schedule_tcb gS s t = sched.schedule_tcb st s t := by
  obtain ⟨hc, ha, hwa⟩ := hn
  unfold sched.schedule_tcb
  rw [sched.cur_thread.guard s hc, sched.action.guard s ha, sched.is_schedulable.guard s t h1 h2 h3 h4,
    sched.set_action.guard s _ hwa]

theorem sched.set_thread_state.guard (s : S) (t : obj.Tcb) (v : U64) (hn : NodeSt (L := L) R W s)
    (hw : W (stA t)) (h1 : R (stA t)) (h2 : R (scA t))
    (h3 : R (maxA (L.mem (L.wr s (stA t) v) (scA t)))) (h4 : R (inqA t)) :
    sched.set_thread_state gS s t v = sched.set_thread_state st s t v := by
  unfold sched.set_thread_state
  rw [obj.Tcb.set_state.guard t s v hw, set_state_ok' s t v]
  simp only [bind_ok]
  exact sched.schedule_tcb.guard (L.wr s (stA t) v) t hn.wr h1 h2 h3 h4

/-! ## Replies -/

theorem msg.set_msg_info.guard (s : S) (t : obj.Tcb) (m : msginfo.MessageInfo)
    (h : W (regA t layout.reg.MSG_INFO)) :
    msg.set_msg_info gS s t m = msg.set_msg_info st s t m := by
  unfold msg.set_msg_info
  have e : ∀ v, obj.Tcb.set_reg gS t s layout.reg.MSG_INFO v =
      obj.Tcb.set_reg st t s layout.reg.MSG_INFO v := fun v => obj.Tcb.set_reg.guard t s _ v h
  simp only [e]

theorem n_msg_regs : msg.N_MSG_REGISTERS = 4#u64 := by unfold msg.N_MSG_REGISTERS; rfl

theorem msg_register_zero : msg.msg_register 0#u64 = ok layout.reg.R10 := by
  unfold msg.msg_register; simp

theorem msg_register_one : msg.msg_register 1#u64 = ok layout.reg.R8 := by
  unfold msg.msg_register; simp

theorem msg.set_mr.guard0 (s : S) (t : obj.Tcb) (buf v : U64) (h : W (regA t layout.reg.R10)) :
    msg.set_mr gS s t buf 0#u64 v = msg.set_mr st s t buf 0#u64 v := by
  have h0 : (0#u64 : U64) < msg.N_MSG_REGISTERS := by rw [n_msg_regs]; decide
  unfold msg.set_mr
  simp only [if_pos h0, msg_register_zero, bind_ok]
  rw [obj.Tcb.set_reg.guard t s _ v h]

theorem msg.reply_success_empty.guard (s : S) (t : obj.Tcb) (h1 : W (regA t layout.reg.BADGE))
    (h2 : W (regA t layout.reg.MSG_INFO)) :
    msg.reply_success_empty gS s t = msg.reply_success_empty st s t := by
  unfold msg.reply_success_empty
  rw [obj.Tcb.set_reg.guard t s _ _ h1, set_reg_ok' s t]
  simp only [bind_ok]
  have e : ∀ m, msg.set_msg_info gS (L.wr s (regA t layout.reg.BADGE) 0#u64) t m =
      msg.set_msg_info st (L.wr s (regA t layout.reg.BADGE) 0#u64) t m :=
    fun m => msg.set_msg_info.guard _ t m h2
  simp only [e]

theorem msg.syscall_arg.guard_lt (s : S) (t : obj.Tcb) (buf i : U64) (hi : i < msg.N_MSG_REGISTERS)
    (hreg : ∀ r, msg.msg_register i = ok r → R (regA t r)) :
    msg.syscall_arg gS s t buf i = msg.syscall_arg st s t buf i := by
  unfold msg.syscall_arg
  simp only [if_pos hi]
  obtain ⟨r, hr⟩ := msg_register_ok i
  rw [hr]; simp only [bind_ok]
  exact obj.Tcb.reg.guard t s r (hreg r hr)

/-! ## `ioport.decode` -/

/-- The current thread's words `ioport.decode` reads and writes. -/
structure IoRd (R W : U64 → Prop) (s : S) (t : U64) : Prop where
  tcb : TcbAddr t
  regR : ∀ r : U64, r.val < 384 → R (regA t r)
  regW : ∀ r : U64, r.val < 384 → W (regA t r)
  stR : R (stA t)
  stW : W (stA t)
  sc : R (scA t)
  max : R (maxA (L.mem s (scA t)))
  inq : R (inqA t)
  ib : R (core.num.U64.wrapping_add t 3512#u64)
  bs : ∀ sl, obj.Tcb.slot t layout.tcb.SLOT_BUFFER = ok sl → R sl ∧ R (core.num.U64.wrapping_add sl 8#u64)

theorem IoRd.wr_st {s : S} {t v : U64} (h : IoRd (L := L) R W s t) : IoRd (L := L) R W (L.wr s (stA t) v) t :=
  { h with max := by rw [st_wr_sc h.tcb]; exact h.max }

theorem IoRd.wr_reg {s : S} {t r v : U64} (h : IoRd (L := L) R W s t) (hr : r.val < 384) :
    IoRd (L := L) R W (L.wr s (regA t r) v) t :=
  { h with max := by rw [reg_wr_sc h.tcb hr]; exact h.max }

theorem lt384 {r : U64} (h : r = layout.reg.R10 ∨ r = layout.reg.R8 ∨ r = layout.reg.BADGE ∨
    r = layout.reg.MSG_INFO) : r.val < 384 := by
  rcases h with rfl | rfl | rfl | rfl <;>
    simp [layout.reg.R10, layout.reg.R8, layout.reg.BADGE, layout.reg.MSG_INFO]

/-- `set_thread_state` at a state the `IoRd`/`NodeSt` facts hold. -/
theorem sts_io {s : S} {t v : U64} (hn : NodeSt (L := L) R W s) (hi : IoRd (L := L) R W s t) :
    sched.set_thread_state gS s t v = sched.set_thread_state st s t v :=
  sched.set_thread_state.guard s t v hn hi.stW hi.stR hi.sc (hi.wr_st (v := v)).max hi.inq

/-- `set_thread_state`'s writes keep `IoRd` / `NodeSt`. -/
theorem sts_keep {s s1 : S} {t v : U64} (hi : IoRd (L := L) R W s t) (hn : NodeSt (L := L) R W s)
    (hda : Aligned (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) ∧
      L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION ≠ scA t)
    (h : sched.set_thread_state st s t v = ok s1) :
    IoRd (L := L) R W s1 t ∧ NodeSt (L := L) R W s1 ∧
      (Aligned (L.nodeAt s1 (L.cpu s1) layout.node.SCHED_ACTION) ∧
        L.nodeAt s1 (L.cpu s1) layout.node.SCHED_ACTION ≠ scA t) := by
  unfold sched.set_thread_state at h
  rw [set_state_ok' s t v] at h; simp only [bind_ok] at h
  unfold sched.schedule_tcb at h
  have h1 := hi.wr_st (v := v)
  have h2 := hn.wr (a := stA t) (v := v)
  have h3 : Aligned (L.nodeAt (L.wr s (stA t) v) (L.cpu (L.wr s (stA t) v)) layout.node.SCHED_ACTION) ∧
      L.nodeAt (L.wr s (stA t) v) (L.cpu (L.wr s (stA t) v)) layout.node.SCHED_ACTION ≠ scA t := by
    rw [nd_wr]; exact hda
  revert h
  generalize L.wr s (stA t) v = s0 at h1 h2 h3
  intro h
  obtain ⟨c, -, h⟩ := bind_eq_ok h
  obtain ⟨b0, -, h⟩ := bind_eq_ok h
  split at h
  · obtain ⟨i, -, h⟩ := bind_eq_ok h
    split at h
    · obtain ⟨b, -, h⟩ := bind_eq_ok h
      split at h
      · rw [← ok_inj_ff h]; exact ⟨h1, h2, h3⟩
      · unfold sched.set_action at h
        simp only [gst_cur_cpu, L.cur_cpu_eq, bind_ok] at h
        rw [eq_ok_of_spec (obj.node_set.spec (L := L) s0 _ _ _)] at h
        rw [← ok_inj_ff h]
        refine ⟨{ h1 with max := ?_ }, h2.wr, by rw [nd_wr]; exact h3⟩
        rw [mem_wr_ne' (b := scA t) h3.1 (field_aligned h1.tcb (by simp) (by simp)) h3.2]; exact h1.max
    · rw [← ok_inj_ff h]; exact ⟨h1, h2, h3⟩
  · rw [← ok_inj_ff h]; exact ⟨h1, h2, h3⟩

theorem set_mr0_ok (s : S) (t buf v : U64) :
    msg.set_mr st s t buf 0#u64 v = ok (1#u64, L.wr s (regA t layout.reg.R10) v) := by
  have h0 : (0#u64 : U64) < msg.N_MSG_REGISTERS := by rw [n_msg_regs]; decide
  unfold msg.set_mr
  simp only [if_pos h0, msg_register_zero, bind_ok, set_reg_ok', lift]
  rfl

/-- The action word is not the SC word, at every state with the same node. -/
abbrev ActDisj (s : S) (t : U64) : Prop :=
  Aligned (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) ∧ L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION ≠ scA t

theorem ActDisj.wr {s : S} {t a v : U64} (h : ActDisj (L := L) s t) : ActDisj (L := L) (L.wr s a v) t := by
  unfold ActDisj; rw [nd_wr]; exact h


end

end Fl4Proofs.P2.PathObl
