/-
# A declined local entry, then the general entry (FL4 #71 / PR #66, line lcd: decline route (c))

fl4-sync runs a syscall or a VM fault first beside its serial gate
(`syscall.handle_syscall_local`, `handle_reply_recv_vm_local`,
`handle_ioport_local`, `handle_invocation_local`, `handle_vm_fault_local`); one
that returns `false` leaves the entry to the general path (`handle_syscall`,
`handle_vm_fault`), run from the state it declined at.

* Decline shapes: a declined syscall-type entry returned the entry state, or
  the entry state after its prefix `LocalPre` (the current thread's `FAULT_IP`
  from `NEXT_IP`, as `syscall` writes it, then one `update_timestamp`), and
  then the number is in the native range or the thread traps its syscalls
  (`RoT`): `syscall_local_decline`, `rr_vm_local_decline`,
  `ioport_local_decline`, `invocation_local_decline`. (The VM entry:
  FastVm's `vm_local_decline`, exactly one `update_timestamp`.) The read-only
  checks and the fast paths' declines (FastDecline, FastVm) write nothing.
* `syscall_pre_same` / `handle_syscall_pre_same`: from the prefix's result
  `(s', a')` the general entry runs as from `(s, a')`, the entry state with
  the Arch value the prefix left: `syscall` writes the same `FAULT_IP` again
  (the word already holds it), reads the same current thread, `NEXT_IP` and
  flags (the prefix's three writes miss them), and its own `update_timestamp`
  from `utW X n1` equals the one from `X` (`budget_ok_utW`, FastVmDecline's
  `utW_twice`: two updates are the later one). `vm_pre_same`: the same for
  `handle_vm_fault`.
* `ut_now`: the prefix's clock reading (`ar.now a = ok (n1, a')`), which P3
  relates to one consumed oracle reading of the spec (`Fl4Spec.fl4ClockTick`).
-/
import Fl4Proofs.P1.FastVmLocal
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

/-- FastDecline's goal-directed walk (binds, `if`s, `match`es) without unfolding calls. -/
syntax "decl_walk" : tactic
macro_rules
  | `(tactic| decl_walk) => `(tactic| repeat' (first
      | (with_reducible_and_instances refine spec_bind_imp (fun _ => ?_)
         try simp only [uncurry_eta_fd])
      | (with_reducible_and_instances refine spec_bind_imp' (fun _ => ?_)
         try simp only [uncurry_eta_fd])
      | (with_reducible refine spec_ite_imp (fun _ => ?_) (fun _ => ?_))
      | split))

/-- A leaf of `decl_walk` on a declined run: a `false` exit at the walked
state, a `true` exit (impossible), or a fast path's decline. -/
syntax "decl_leaf" : tactic
macro_rules
  | `(tactic| decl_leaf) => `(tactic| (intro h'; first
      | (rw [WP.spec_ok] at h'
         exact ⟨(congrArg (fun r => r.2.1) h').symm, (congrArg (fun r => r.2.2) h').symm⟩)
      | (rw [WP.spec_ok] at h'; simp at h')
      | (with_reducible exact fault_decline _ _ (eq_of_spec_fd h'))
      | (with_reducible exact reply_recv_found_decline _ _ (eq_of_spec_fd h'))
      | (with_reducible exact reply_recv_vm_found_decline _ _ (eq_of_spec_fd h'))
      | (with_reducible exact vm_fault_decline _ _ (eq_of_spec_fd h'))))

/-- The native syscall range: ReplyRecv. -/
theorem rng_rr : ¬ fl4_abi.syscall.SysReplyRecv < fl4_abi.syscall.SYSCALL_MIN ∧
    ¬ fl4_abi.syscall.SysReplyRecv > fl4_abi.syscall.SYSCALL_MAX := by
  constructor
  · unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SYSCALL_MIN
    first | decide | simp | (simp [IScalar.lt_equiv]) | (simp [IScalar.lt_equiv]; omega)
  · unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SYSCALL_MAX
    first | decide | simp | (simp [IScalar.lt_equiv]) | (simp [IScalar.lt_equiv]; omega)

/-- The native syscall range: Call. -/
theorem rng_call : ¬ fl4_abi.syscall.SysCall < fl4_abi.syscall.SYSCALL_MIN ∧
    ¬ fl4_abi.syscall.SysCall > fl4_abi.syscall.SYSCALL_MAX := by
  constructor
  · unfold fl4_abi.syscall.SysCall fl4_abi.syscall.SYSCALL_MIN
    first | decide | simp | (simp [IScalar.lt_equiv]) | (simp [IScalar.lt_equiv]; omega)
  · unfold fl4_abi.syscall.SysCall fl4_abi.syscall.SYSCALL_MAX
    first | decide | simp | (simp [IScalar.lt_equiv]) | (simp [IScalar.lt_equiv]; omega)

/-- The native syscall range: Send. -/
theorem rng_send : ¬ fl4_abi.syscall.SysSend < fl4_abi.syscall.SYSCALL_MIN ∧
    ¬ fl4_abi.syscall.SysSend > fl4_abi.syscall.SYSCALL_MAX := by
  constructor
  · unfold fl4_abi.syscall.SysSend fl4_abi.syscall.SYSCALL_MIN
    first | decide | simp | (simp [IScalar.lt_equiv]) | (simp [IScalar.lt_equiv]; omega)
  · unfold fl4_abi.syscall.SysSend fl4_abi.syscall.SYSCALL_MAX
    first | decide | simp | (simp [IScalar.lt_equiv]) | (simp [IScalar.lt_equiv]; omega)

section
variable {S : Type _} {A : Type _} {st : machine.Store S} (ar : machine.Arch A)

/-- **The prefix a syscall-type local entry writes before it declines**: the
current thread's `FAULT_IP` from its `NEXT_IP` (as `syscall` writes it), then
one `update_timestamp`, ending at `r`. -/
def LocalPre (s : S) (a : A) (r : S × A) : Prop :=
  ∃ t nx s1, sched.cur_thread st s = ok t ∧ obj.Tcb.reg st t s layout.reg.NEXT_IP = ok nx ∧
    obj.Tcb.set_reg st t s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1 ∧
    sched.update_timestamp st ar s1 a = ok r

variable (st) in
/-- **The general entry takes no unknown-syscall branch it would not take at
the entry**: the number is in the native range, or the current thread traps
its syscalls (flags read at the entry state). -/
def RoT (s : S) (n : I64) : Prop :=
  (¬ n < fl4_abi.syscall.SYSCALL_MIN ∧ ¬ n > fl4_abi.syscall.SYSCALL_MAX) ∨
    ∃ t f, sched.cur_thread st s = ok t ∧ obj.Tcb.flags st t s = ok f ∧
      (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true

set_option maxHeartbeats 4000000 in
/-- **A declined `handle_syscall_local`**: the entry state, or the prefix
(trapped, or ReplyRecv). -/
theorem syscall_local_decline {s s' : S} {a a' : A} {n : I64} {found : U64 × U64}
    (h : syscall.handle_syscall_local st ar s a n found = ok (false, s', a')) :
    (s' = s ∧ a' = a) ∨ (LocalPre (st := st) ar s a (s', a') ∧ RoT st s n) := by
  unfold syscall.handle_syscall_local at h
  try simp only [lift, bind_ok] at h
  obtain ⟨t, et, h⟩ := bind_eq_ok h
  obtain ⟨i, ei, h⟩ := bind_eq_ok h
  rw [num_domains_ne_one_false] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  by_cases c1 : (i &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true
  · rw [if_pos c1] at h
    right
    obtain ⟨nx, enx, h⟩ := bind_eq_ok h
    obtain ⟨s1, es1, h⟩ := bind_eq_ok h
    obtain ⟨⟨s2, a1⟩, eu, h⟩ := bind_eq_ok h
    try simp only [uncurry_apply_pair] at h
    obtain ⟨e1, e2⟩ : s' = s2 ∧ a' = a1 := by
      have h' := spec_of_eq_fd h
      clear h
      revert h'
      decl_walk
      all_goals decl_leaf
    subst e1 e2
    exact ⟨⟨t, nx, s1, et, enx, es1, eu⟩, Or.inr ⟨t, i, et, ei, c1⟩⟩
  · rw [if_neg c1] at h
    by_cases c2 : (n != fl4_abi.syscall.SysReplyRecv) = true
    · rw [if_pos c2] at h
      left
      have e := ok_inj_ff h
      simp only [Prod.mk.injEq, true_and] at e
      exact ⟨e.1.symm, e.2.symm⟩
    · rw [if_neg c2] at h
      right
      have hn : n = fl4_abi.syscall.SysReplyRecv := by simp only [bne_iff_ne, ne_eq, not_not] at c2; exact c2
      obtain ⟨nx, enx, h⟩ := bind_eq_ok h
      obtain ⟨s1, es1, h⟩ := bind_eq_ok h
      obtain ⟨⟨s2, a1⟩, eu, h⟩ := bind_eq_ok h
      try simp only [uncurry_apply_pair] at h
      obtain ⟨e1, e2⟩ : s' = s2 ∧ a' = a1 := by
        have h' := spec_of_eq_fd h
        clear h
        revert h'
        decl_walk
        all_goals decl_leaf
      subst e1 e2
      subst hn
      exact ⟨⟨t, nx, s1, et, enx, es1, eu⟩, Or.inl rng_rr⟩

set_option maxHeartbeats 4000000 in
/-- **A declined `handle_reply_recv_vm_local`**: the entry state, or the prefix. -/
theorem rr_vm_local_decline {s s' : S} {a a' : A} {found : U64 × U64}
    (h : syscall.handle_reply_recv_vm_local st ar s a found = ok (false, s', a')) :
    (s' = s ∧ a' = a) ∨
      (LocalPre (st := st) ar s a (s', a') ∧ RoT st s fl4_abi.syscall.SysReplyRecv) := by
  unfold syscall.handle_reply_recv_vm_local at h
  try simp only [lift, bind_ok] at h
  obtain ⟨t, et, h⟩ := bind_eq_ok h
  rw [num_domains_ne_one_false] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨i, -, h⟩ := bind_eq_ok h
  by_cases c1 : (i &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true
  · rw [if_pos c1] at h
    left
    have e := ok_inj_ff h
    simp only [Prod.mk.injEq, true_and] at e
    exact ⟨e.1.symm, e.2.symm⟩
  · rw [if_neg c1] at h
    right
    obtain ⟨nx, enx, h⟩ := bind_eq_ok h
    obtain ⟨s1, es1, h⟩ := bind_eq_ok h
    obtain ⟨⟨s2, a1⟩, eu, h⟩ := bind_eq_ok h
    try simp only [uncurry_apply_pair] at h
    obtain ⟨e1, e2⟩ : s' = s2 ∧ a' = a1 := by
      have h' := spec_of_eq_fd h
      clear h
      revert h'
      decl_walk
      all_goals decl_leaf
    subst e1 e2
    exact ⟨⟨t, nx, s1, et, enx, es1, eu⟩, Or.inl rng_rr⟩

set_option maxHeartbeats 8000000 in
/-- **A declined `handle_ioport_local`**: the entry state, or the prefix (Call
or Send). -/
theorem ioport_local_decline {s s' : S} {a a' : A} {n : I64}
    (h : syscall.handle_ioport_local st ar s a n = ok (false, s', a')) :
    (s' = s ∧ a' = a) ∨ (LocalPre (st := st) ar s a (s', a') ∧ RoT st s n) := by
  unfold syscall.handle_ioport_local at h
  try simp only [lift, bind_ok] at h
  obtain ⟨t, et, h⟩ := bind_eq_ok h
  obtain ⟨info, -, h⟩ := bind_eq_ok h
  rw [num_domains_ne_one_false] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨i, -, h⟩ := bind_eq_ok h
  by_cases c1 : (i &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true
  · rw [if_pos c1] at h
    left
    have e := ok_inj_ff h
    simp only [Prod.mk.injEq, true_and] at e
    exact ⟨e.1.symm, e.2.symm⟩
  · rw [if_neg c1] at h
    by_cases c2 : (n != fl4_abi.syscall.SysCall) = true
    · rw [if_pos c2] at h
      by_cases c3 : (n != fl4_abi.syscall.SysSend) = true
      · rw [if_pos c3] at h
        left
        have e := ok_inj_ff h
        simp only [Prod.mk.injEq, true_and] at e
        exact ⟨e.1.symm, e.2.symm⟩
      · rw [if_neg c3] at h
        have hn : n = fl4_abi.syscall.SysSend := by simp only [bne_iff_ne, ne_eq, not_not] at c3; exact c3
        obtain ⟨b, -, h⟩ := bind_eq_ok h
        cases b
        · simp only [Bool.false_eq_true, ↓reduceIte] at h
          left
          have e := ok_inj_ff h
          simp only [Prod.mk.injEq, true_and] at e
          exact ⟨e.1.symm, e.2.symm⟩
        · simp only [↓reduceIte] at h
          right
          obtain ⟨nx, enx, h⟩ := bind_eq_ok h
          obtain ⟨s1, es1, h⟩ := bind_eq_ok h
          obtain ⟨⟨s2, a1⟩, eu, h⟩ := bind_eq_ok h
          try simp only [uncurry_apply_pair] at h
          obtain ⟨e1, e2⟩ : s' = s2 ∧ a' = a1 := by
            have h' := spec_of_eq_fd h
            clear h
            revert h'
            decl_walk
            all_goals decl_leaf
          subst e1 e2
          subst hn
          exact ⟨⟨t, nx, s1, et, enx, es1, eu⟩, Or.inl rng_send⟩
    · rw [if_neg c2] at h
      have hn : n = fl4_abi.syscall.SysCall := by simp only [bne_iff_ne, ne_eq, not_not] at c2; exact c2
      obtain ⟨b, -, h⟩ := bind_eq_ok h
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte] at h
        left
        have e := ok_inj_ff h
        simp only [Prod.mk.injEq, true_and] at e
        exact ⟨e.1.symm, e.2.symm⟩
      · simp only [↓reduceIte] at h
        right
        obtain ⟨nx, enx, h⟩ := bind_eq_ok h
        obtain ⟨s1, es1, h⟩ := bind_eq_ok h
        obtain ⟨⟨s2, a1⟩, eu, h⟩ := bind_eq_ok h
        try simp only [uncurry_apply_pair] at h
        obtain ⟨e1, e2⟩ : s' = s2 ∧ a' = a1 := by
          have h' := spec_of_eq_fd h
          clear h
          revert h'
          decl_walk
          all_goals decl_leaf
        subst e1 e2
        subst hn
        exact ⟨⟨t, nx, s1, et, enx, es1, eu⟩, Or.inl rng_call⟩

set_option maxHeartbeats 8000000 in
/-- **A declined `handle_invocation_local`**: the entry state, or the prefix
(Call). -/
theorem invocation_local_decline {s s' : S} {a a' : A} {n : I64} {p : localinv.Plan}
    (h : syscall.handle_invocation_local st ar s a n p = ok (false, s', a')) :
    (s' = s ∧ a' = a) ∨ (LocalPre (st := st) ar s a (s', a') ∧ RoT st s n) := by
  unfold syscall.handle_invocation_local at h
  try simp only [lift, bind_ok] at h
  obtain ⟨t, et, h⟩ := bind_eq_ok h
  obtain ⟨info, -, h⟩ := bind_eq_ok h
  rw [num_domains_ne_one_false] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨i, -, h⟩ := bind_eq_ok h
  by_cases c1 : (i &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true
  · rw [if_pos c1] at h
    left
    have e := ok_inj_ff h
    simp only [Prod.mk.injEq, true_and] at e
    exact ⟨e.1.symm, e.2.symm⟩
  · rw [if_neg c1] at h
    by_cases c2 : (n != fl4_abi.syscall.SysCall) = true
    · rw [if_pos c2] at h
      left
      have e := ok_inj_ff h
      simp only [Prod.mk.injEq, true_and] at e
      exact ⟨e.1.symm, e.2.symm⟩
    · rw [if_neg c2] at h
      have hn : n = fl4_abi.syscall.SysCall := by simp only [bne_iff_ne, ne_eq, not_not] at c2; exact c2
      obtain ⟨b, -, h⟩ := bind_eq_ok h
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte] at h
        left
        have e := ok_inj_ff h
        simp only [Prod.mk.injEq, true_and] at e
        exact ⟨e.1.symm, e.2.symm⟩
      · simp only [↓reduceIte] at h
        right
        obtain ⟨nx, enx, h⟩ := bind_eq_ok h
        obtain ⟨s1, es1, h⟩ := bind_eq_ok h
        obtain ⟨⟨s2, a1⟩, eu, h⟩ := bind_eq_ok h
        try simp only [uncurry_apply_pair] at h
        obtain ⟨e1, e2⟩ : s' = s2 ∧ a' = a1 := by
          have h' := spec_of_eq_fd h
          clear h
          revert h'
          decl_walk
          all_goals decl_leaf
        subst e1 e2
        subst hn
        exact ⟨⟨t, nx, s1, et, enx, es1, eu⟩, Or.inl rng_call⟩

end

section
variable {S : Type _} {A : Type _} {st : machine.Store S} (ar : machine.Arch A) [L : LawfulStore st]

/-- The flags word read. -/
theorem flags_ok (s : S) (t : U64) :
    obj.Tcb.flags st t s = ok (L.mem s (core.num.U64.wrapping_add t 3456#u64)) := by
  unfold obj.Tcb.flags
  rw [eq_of_spec_fd layout.tcb.FLAGS.spec]
  simp only [bind_ok, lift, L.read_eq]

/-- The placement facts the prefix lemmas read, from `BXI`. -/
theorem BXI.tcbNode {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s : S}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    TcbPlaced T ∧ NodePlaced st T s (L.cpu s) ∧ L.curW s ∈ T := by
  obtain ⟨⟨Q, R, hSQ⟩, -, -, -, -⟩ := hI
  exact ⟨hSQ.tcbs, hSQ.nodes _ hSQ.cur, hSQ.curT⟩

theorem utW_ksb (X : S) (n : U64) : L.ksb (utW (L := L) X n) = L.ksb X := by
  unfold utW; simp

theorem utW_cpu (X : S) (n : U64) : L.cpu (utW (L := L) X n) = L.cpu X := by
  unfold utW; simp

/-- `update_timestamp`'s two writes miss every other aligned word. -/
theorem utW_mem {T : Set U64} {X : S} (hN : NodePlaced st T X (L.cpu X)) (n : U64) {b : U64} (hb : Aligned b)
    (h1 : b ≠ ctA (L := L) X) (h2 : b ≠ cnA (L := L) X) : L.mem (utW (L := L) X n) b = L.mem X b := by
  obtain ⟨hct, hcn, -⟩ := ct_cn hN
  unfold utW
  rw [mem_wr_ne' hcn hb (Ne.symm h2), mem_wr_ne' hct hb (Ne.symm h1)]

theorem utW_placed {T : Set U64} {X : S} (hN : NodePlaced st T X (L.cpu X)) (n : U64) :
    NodePlaced st T (utW (L := L) X n) (L.cpu (utW (L := L) X n)) := by
  rw [utW_cpu]; unfold utW; exact hN.wr.wr

/-- **`budget_ok` after a timestamp update is `budget_ok`** (one domain, under
`StoreExt`): its own update supersedes the earlier one (`utW_twice`). -/
theorem budget_ok_utW (hX : StoreExt st) (hA : P0.ArchTotal ar) {T : Set U64} {X : S}
    (hN : NodePlaced st T X (L.cpu X)) (n1 : U64) (a' : A) :
    syscall.budget_ok st ar (utW (L := L) X n1) a' = syscall.budget_ok st ar X a' := by
  obtain ⟨⟨n2, b2⟩, hn, -⟩ := spec_ex_fd (hA.now a')
  unfold syscall.budget_ok
  rw [update_timestamp_ok ar (utW_placed hN n1) hn, update_timestamp_ok ar hN hn, utW_twice hX hN]

/-- **The prefix's clock reading**: a timestamp update ending at `r` read the
clock value `n1` with `ar.now a = ok (n1, r.2)` and wrote `utW X n1`. -/
theorem ut_now (hA : P0.ArchTotal ar) {T : Set U64} {X : S} {a : A} {r : S × A}
    (hN : NodePlaced st T X (L.cpu X)) (h : sched.update_timestamp st ar X a = ok r) :
    ∃ n1, ar.now a = ok (n1, r.2) ∧ r.1 = utW (L := L) X n1 := by
  obtain ⟨⟨n1, b1⟩, hn, -⟩ := spec_ex_fd (hA.now a)
  rw [update_timestamp_ok ar hN hn] at h
  have e := ok_inj_ff h
  subst e
  exact ⟨n1, hn, rfl⟩

end

end Fl4Proofs.P1
