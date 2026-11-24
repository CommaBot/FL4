/-
# P2 (line p2sl): `handle_syscall_local` on the guarded store (accepted runs)

**`syscall.handle_syscall_local.guard_acc`**: an accepted run of the syscall
entry beside the gate runs on `guard st R W` as on `st` when `R` / `W` hold

* `PreAcc R W s`: the prefix's words at the entry state `s` (the node, the
  current thread's `FLAGS` and `NEXT_IP` read, its `FAULT_IP` written), and
  the current SC's head refill at the prefix's end state `X` (`sufficient`);
* for the trap arm (`fastpath.fault`), `FltAcc` at `X` of the checks'
  objects; for the ReplyRecv arm (`fastpath.reply_recv_found`), `RrAcc` at
  `X` of the checks' objects.

The prefix (`cur_thread`, `flags`, `NEXT_IP` → `FAULT_IP`,
`update_timestamp`, `cur_sc`, `consumed`, `sufficient`) is rewritten leaf by
leaf; the arms by `fastpath.fault.guard` / `fastpath.reply_recv_found.guard`.

Premises (those of the two arm lemmas, at the prefix's end state `X`, as
`sl_trap_foot` / `sl_rr_entry_foot` state them):

* `hy0` [J]: the handler (trap arm) / the reply's thread (ReplyRecv arm)
  yields to no SC;
* `AsidOff` [J] (`P1/FastFinInv.lean`);
* `hrz`: fl4-sync's check that the reply object has no neighbours
  (`local_syscall`'s `found` check; ReplyRecv arm only).
-/
import Fl4Proofs.P2.AccessFastRR
import Fl4Proofs.P2.FootSlEntry
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts

section
variable {S : Type} {st : machine.Store S} {R W : U64 → Prop} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)

/-- The prefix's words at the entry state `s`. -/
structure PreAcc (R W : U64 → Prop) (s : S) : Prop where
  nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s (L.cpu s) o) ∧ W (L.nodeAt s (L.cpu s) o)
  fl : R (core.num.U64.wrapping_add (L.curW s) 3456#u64)
  nx : R (regA (L.curW s) layout.reg.NEXT_IP)
  fi : W (regA (L.curW s) layout.reg.FAULT_IP)

variable (st) in
/-- The current thread traps its syscalls (flags read at the entry). -/
def SlTrap (s : S) : Prop :=
  ∃ f, obj.Tcb.flags st (L.curW s) s = ok f ∧ (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true

/-- The prefix up to `sufficient`, on the guarded store: given the real run's
values. -/
theorem sl_pre.guard {T : Set U64} (hA : P0.ArchTotal ar) {s s1 s2 : S} {a a1 : A} {nx csc : U64}
    (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s)) (hcT : L.curW s ∈ T)
    (hpre : PreAcc (L := L) R W s)
    (enx : obj.Tcb.reg st (L.curW s) s layout.reg.NEXT_IP = ok nx)
    (es1 : obj.Tcb.set_reg st (L.curW s) s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1)
    (eu : sched.update_timestamp st ar s1 a = ok (s2, a1))
    (hhd : RdHead (L := L) R s2 csc) :
    obj.Tcb.reg (guard st R W) (L.curW s) s layout.reg.NEXT_IP = ok nx ∧
    obj.Tcb.set_reg (guard st R W) (L.curW s) s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1 ∧
    sched.update_timestamp (guard st R W) ar s1 a = ok (s2, a1) ∧
    sched.cur_sc (guard st R W) s2 = sched.cur_sc st s2 ∧
    sched.consumed (guard st R W) s2 = sched.consumed st s2 ∧
    ∀ c, sporadic.sufficient (guard st R W) ar s2 a1 csc c = sporadic.sufficient st ar s2 a1 csc c := by
  have hP : LocalPre (st := st) ar s a (s2, a1) := ⟨_, nx, s1, cur_thread_ok s, enx, es1, eu⟩
  obtain ⟨hk2, hc2, -⟩ := sl_pre_agree (Cs := ∅) ar hA hT hN hcT hP
  have e1 := set_fip_wr (hT _ hcT) es1
  have hk1 : L.ksb s1 = L.ksb s := by rw [e1, L.ksb_wr]
  have hc1 : L.cpu s1 = L.cpu s := by rw [e1, L.cpu_wr]
  have nd1 : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      R (L.nodeAt s1 (L.cpu s1) o) ∧ W (L.nodeAt s1 (L.cpu s1) o) := fun o h1 h2 => by
    rw [hc1, nodeAt_of_ksb hk1]; exact hpre.nd o h1 h2
  have nd2 : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s2 (L.cpu s2) o) := fun o h1 h2 => by
    rw [hc2, nodeAt_of_ksb hk2]; exact (hpre.nd o h1 h2).1
  have hct := nd1 layout.node.CUR_TIME (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
  have hcn := nd1 layout.node.CONSUMED (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
  refine ⟨?_, ?_, ?_, ?_, ?_, fun c => sporadic.sufficient.guard ar s2 a1 csc c hhd⟩
  · rw [obj.Tcb.reg.guard _ _ _ hpre.nx, enx]
  · rw [obj.Tcb.set_reg.guard _ _ _ _ hpre.fi, es1]
  · rw [sched.update_timestamp.guard ar s1 a hct.1 hct.2 hcn.1 hcn.2, eu]
  · exact sched.cur_sc.guard s2 (nd2 _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]))
  · exact sched.consumed.guard s2 (nd2 _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]))

set_option maxHeartbeats 4000000 in
/-- **The accepted syscall entry on the guarded store** (`acc` of
`handle_syscall_local`). Module docstring for the premises. -/
theorem syscall.handle_syscall_local.guard_acc {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap}
    {Z : U64 → Nat} (hA : P0.ArchTotal ar) {s s' : S} {a a' : A} {n : I64} {found : U64 × U64}
    (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s)) (hcT : L.curW s ∈ T)
    (hpre : PreAcc (L := L) R W s)
    (hhd : ∀ X a1 csc, LocalPre (st := st) ar s a (X, a1) → sched.cur_sc st X = ok csc →
      RdHead (L := L) R X csc)
    (hI : ∀ X a1, LocalPre (st := st) ar s a (X, a1) → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac X)
    (hAs : ∀ X a1, LocalPre (st := st) ar s a (X, a1) → AsidOff (L := L) Ω Sg X)
    -- the trap arm
    (hrecv : SlTrap st s → ∀ X a1, LocalPre (st := st) ar s a (X, a1) → ∀ {ptr badge dest r : U64},
      FaultChecks st X (L.curW s) ptr badge dest r → L.mem X (stA dest) = sched.TS_BLOCKED_ON_RECV)
    (hF : SlTrap st s → ∀ X a1, LocalPre (st := st) ar s a (X, a1) →
      FaultEntAt (L := L) T Cs Ω U Sg Rp X (L.curW s))
    (hy0f : SlTrap st s → ∀ X a1, LocalPre (st := st) ar s a (X, a1) → ∀ {ptr badge dest r : U64},
      FaultChecks st X (L.curW s) ptr badge dest r → L.mem X (yieldA dest) = 0#u64)
    (hTm : SlTrap st s → ∀ X a1, LocalPre (st := st) ar s a (X, a1) → TimerOK st T Cs X)
    (hRWf : SlTrap st s → ∀ X a1, LocalPre (st := st) ar s a (X, a1) → ∀ {ptr badge dest r : U64},
      FaultChecks st X (L.curW s) ptr badge dest r → FltAcc (L := L) Z R W X (L.curW s) ptr dest r)
    -- the ReplyRecv arm
    (hPl : ¬ SlTrap st s → ∀ X a1, LocalPre (st := st) ar s a (X, a1) → ∀ u usc,
      RRChecks st ar X a1 (L.curW s) found.1 found.2 u usc →
      RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z X (L.curW s) found.1 found.2 u usc)
    (hrz : ¬ SlTrap st s → ∀ X a1, LocalPre (st := st) ar s a (X, a1) →
      L.mem X (rNextA found.1) &&& ~~~1#u64 = 0#u64 ∧ L.mem X (rPrevA found.1) &&& ~~~1#u64 = 0#u64)
    (hy0r : ¬ SlTrap st s → ∀ X a1, LocalPre (st := st) ar s a (X, a1) → ∀ u usc,
      RRChecks st ar X a1 (L.curW s) found.1 found.2 u usc → L.mem X (yieldA u) = 0#u64)
    (hRWr : ¬ SlTrap st s → ∀ X a1, LocalPre (st := st) ar s a (X, a1) → ∀ u usc,
      RRChecks st ar X a1 (L.curW s) found.1 found.2 u usc →
      RrAcc (L := L) Z R W X (L.curW s) found.1 found.2 u usc)
    (h : syscall.handle_syscall_local st ar s a n found = ok (true, s', a')) :
    syscall.handle_syscall_local (guard st R W) ar s a n found = ok (true, s', a') := by
  have ht' := hT _ hcT
  obtain ⟨rp, ep⟩ := found
  unfold syscall.handle_syscall_local at h ⊢
  try simp only [lift, bind_ok] at h ⊢
  obtain ⟨t, et, h⟩ := bind_eq_ok h
  have et' : t = L.curW s := by rw [cur_thread_ok] at et; exact (ok_inj_ff et).symm
  subst et'
  rw [sched.cur_thread.guard s (hpre.nd _ (by simp [layout.node.CUR_THREAD])
    (by simp [layout.node.CUR_THREAD])).1, et]
  simp only [bind_ok, bind_tc_ok]
  obtain ⟨i, ei, h⟩ := bind_eq_ok h
  rw [obj.Tcb.flags.guard _ _ hpre.fl, ei]
  simp only [bind_ok, bind_tc_ok]
  try simp only [lift, bind_ok] at h ⊢
  rw [num_domains_ne_one_false] at h ⊢
  simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
  by_cases hf : (i &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true
  · have hS : SlTrap st s := ⟨i, ei, hf⟩
    rw [if_pos hf] at h ⊢
    obtain ⟨nx, enx, h⟩ := bind_eq_ok h
    obtain ⟨s1, es1, h⟩ := bind_eq_ok h
    obtain ⟨⟨s2, a1⟩, eu, h⟩ := bind_eq_ok h
    try simp only [uncurry_apply_pair] at h
    obtain ⟨csc, ecsc, h⟩ := bind_eq_ok h
    obtain ⟨c, ec, h⟩ := bind_eq_ok h
    obtain ⟨b, eb, h⟩ := bind_eq_ok h
    have hP : LocalPre (st := st) ar s a (s2, a1) := ⟨_, nx, s1, cur_thread_ok s, enx, es1, eu⟩
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := sl_pre.guard ar hA hT hN hcT hpre enx es1 eu (hhd _ _ _ hP ecsc)
    rw [g1]; simp only [bind_ok, bind_tc_ok]
    rw [g2]; simp only [bind_ok, bind_tc_ok]
    rw [g3]; simp only [bind_ok, bind_tc_ok, uncurry_apply_pair]
    rw [g4, ecsc]; simp only [bind_ok, bind_tc_ok]
    rw [g5, ec]; simp only [bind_ok, bind_tc_ok]
    rw [g6, eb]; simp only [bind_ok, bind_tc_ok]
    cases b
    · simp at h
    simp only [↓reduceIte, if_pos hf] at h ⊢
    try simp only [lift, bind_ok] at h ⊢
    rw [fastpath.fault.guard ar hA (hI _ _ hP) (hrecv hS _ _ hP) (hF hS _ _ hP) (hy0f hS _ _ hP)
      (hTm hS _ _ hP) (hAs _ _ hP) (hRWf hS _ _ hP) h]
    exact h
  · have hS : ¬ SlTrap st s := fun ⟨f, ef, hf'⟩ => hf (by rw [ok_inj_ff (ei.symm.trans ef)]; exact hf')
    rw [if_neg hf] at h ⊢
    by_cases hn : (n != fl4_abi.syscall.SysReplyRecv) = true
    · rw [if_pos hn] at h; simp at h
    rw [if_neg hn] at h ⊢
    obtain ⟨nx, enx, h⟩ := bind_eq_ok h
    obtain ⟨s1, es1, h⟩ := bind_eq_ok h
    obtain ⟨⟨s2, a1⟩, eu, h⟩ := bind_eq_ok h
    try simp only [uncurry_apply_pair] at h
    obtain ⟨csc, ecsc, h⟩ := bind_eq_ok h
    obtain ⟨c, ec, h⟩ := bind_eq_ok h
    obtain ⟨b, eb, h⟩ := bind_eq_ok h
    have hP : LocalPre (st := st) ar s a (s2, a1) := ⟨_, nx, s1, cur_thread_ok s, enx, es1, eu⟩
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := sl_pre.guard ar hA hT hN hcT hpre enx es1 eu (hhd _ _ _ hP ecsc)
    rw [g1]; simp only [bind_ok, bind_tc_ok]
    rw [g2]; simp only [bind_ok, bind_tc_ok]
    rw [g3]; simp only [bind_ok, bind_tc_ok, uncurry_apply_pair]
    rw [g4, ecsc]; simp only [bind_ok, bind_tc_ok]
    rw [g5, ec]; simp only [bind_ok, bind_tc_ok]
    rw [g6, eb]; simp only [bind_ok, bind_tc_ok]
    cases b
    · simp at h
    simp only [↓reduceIte, if_neg hf] at h ⊢
    rw [fastpath.reply_recv_found.guard ar hA (hI _ _ hP) (hPl hS _ _ hP) (hrz hS _ _ hP) (hy0r hS _ _ hP)
      (hAs _ _ hP) (hRWr hS _ _ hP) h]
    exact h

end

end Fl4Proofs.P2.PathObl
