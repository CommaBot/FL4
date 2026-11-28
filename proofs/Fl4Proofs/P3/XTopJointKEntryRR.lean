/-
P3 (issue #16, m66 (R-d)): **`kernel_entryJ33R` / `kernel_entryJ34R`**, the
newest tops with the ReplyRecv fast-path premise `hFast : FastRR` [P] (a
"the fast path keeps `KPost`" premise) replaced by the general path's reads
along an accepted ReplyRecv run, `hRP : P1.RRPreAt` (P1 FastRRSame).

* `FastAcc.of_rrpre`: with the trap flag clear after the `FAULT_IP` write and
  the native number `SysReplyRecv`, an accepted run of `handle_syscall_fast`
  is a run of `fastpath.reply_recv` from the real dispatch state, and by
  `P1.rr_same` / `P1.syscall_rr_general` the general path ends in the same
  state, so `P1.FastAcc` holds for every `P` (equality, under `StoreExt` [P]).
  (`FastRR` itself quantifies over a dispatch state with an arbitrary
  `FAULT_IP` value, `KFrontB`'s `v`, so it is not provable by equality with the
  general run; the tops therefore bypass it.)
* `kernel_entryJ33R`: `kernel_entryJ33` with `hFast` replaced by `hRP`;
  `kernel_entryJ34R`: the same without `hLv` (`J.live`). J33 / J34 kept.
-/
import Fl4Proofs.P3.XTopJointKEntry33
import Fl4Proofs.P1.FastRRSame
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {MR : A → Fl4Spec.MachineState → Prop}

/-- `P1.FastAcc` on the ReplyRecv route (module docstring; `hSX : StoreExt` [P] for `P1.rr_same`). -/
theorem FastAcc.of_rrpre (hSX : P1.StoreExt st) {s : S} {a : A} {n : I64} {P : S × A → Prop}
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hr : ¬ n < fl4_abi.syscall.SYSCALL_MIN ∧ ¬ n > fl4_abi.syscall.SYSCALL_MAX)
    (hrr : n = fl4_abi.syscall.SysReplyRecv) (h : P1.RRPreAt (L := L) arI s a) :
    P1.FastAcc st arI s a n P := by
  intro hg s' a' e
  unfold syscall.handle_syscall_fast syscall.syscall at e
  have hct := cur_thread_eq (L := L) s
  generalize L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) = ct at hct
  rw [hct] at e; simp only [bind_tc_eq, bind_ok] at e
  obtain ⟨nx, hnx, -⟩ := spec_exists (Endp.obj.Tcb.reg.spec (L := L) s ct layout.reg.NEXT_IP)
  rw [hnx] at e; simp only [lift, bind_tc_eq, bind_ok] at e
  obtain ⟨s1, hs1, rfl⟩ := spec_exists (Endp.obj.Tcb.set_reg.spec (L := L) s ct layout.reg.FAULT_IP
    (core.num.U64.wrapping_sub nx 2#u64))
  rw [hs1] at e; simp only [bind_tc_eq, bind_ok] at e
  obtain ⟨f, hf, hf0⟩ := spec_exists (hflag ct (core.num.U64.wrapping_sub nx 2#u64) hct)
  rw [hf] at e; simp only [bind_tc_eq, bind_ok, hf0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at e
  simp only [if_neg hr.1, if_neg hr.2] at e
  have e' := P1.spec_of_eq_fd e
  clear e
  obtain ⟨⟨b, s2, a1⟩, eb, e'⟩ := P1.spec_bind_inv e'
  try simp only [uncurry_apply_pair] at e'
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte] at e'
    obtain ⟨_, -, e'⟩ := P1.spec_bind_inv e'
    try simp only [P1.uncurry_eta_fd] at e'
    rw [WP.spec_ok] at e'
    simp at e'
  simp only [↓reduceIte, if_pos hrr] at e'
  obtain ⟨⟨b1, s3, a2⟩, er, e'⟩ := P1.spec_bind_inv e'
  try simp only [uncurry_apply_pair] at e'
  cases b1
  · simp only [Bool.false_eq_true, ↓reduceIte] at e'
    obtain ⟨_, -, e'⟩ := P1.spec_bind_inv e'
    try simp only [P1.uncurry_eta_fd] at e'
    obtain ⟨_, -, e'⟩ := P1.spec_bind_inv e'
    try simp only [P1.uncurry_eta_fd] at e'
    rw [WP.spec_ok] at e'
    simp at e'
  simp only [↓reduceIte, WP.spec_ok, Prod.mk.injEq, true_and] at e'
  rw [← e'.1, ← e'.2]
  subst hrr
  obtain ⟨X, a'', hd, hfin⟩ := P1.rr_same arI hSX er (h ct nx _ s2 a1 hct hnx hs1 eb)
  have hs := P1.syscall_rr_general arI hct hnx hs1 hf (by simp [hf0]) hr.1 hr.2 eb hd hfin
  unfold syscall.handle_syscall_general at hg
  rw [hs] at hg; simp only [bind_ok, uncurry_apply_pair, WP.spec_ok] at hg
  exact hg

end

end

end Fl4Proofs.P3
