/-
# The I/O port entry beside the serial gate, accepted (KENTRY-PLAN lci)

`syscall.handle_ioport_local` (fl4-sync's `local_syscall`, an I/O port
invocation by `SysCall` / `SysSend`) where it returns `true`: it has run the
general path's own prefix (`FAULT_IP` write, `update_timestamp`), read-only
checks (`action`, `yield_to`, `extra_caps`, `ioport.invocation_ok`,
`sporadic.sufficient`, `fastpath.schedulable_here`), then
`handle_invocation call true call false cptr`, `after_invocation`, `finish`.

* `prefix_cur_keep`: the `FAULT_IP` write and a passing `budget_ok`
  (`CUR_TIME` / `CONSUMED`) keep the current-thread word (the first half of
  `rr_prefix_keep`, without the `reply_caps` part);
* `syscall_inv_same`: `syscall … true` for `SysCall` / `SysSend` with the
  trap flag clear and `budget_ok` passing is `dispatch_syscall`'s
  `handle_invocation` / `after_invocation` arm and `finish`, with exactly the
  arguments the local entry passes (`SysSend`: `false true false false`;
  `SysCall`: `true true true false`) and the `CAP` register read at the
  post-`budget_ok` state;
* `ioport_local_same`: an accepted `handle_ioport_local` ends where
  `syscall.handle_syscall` ends (the local `sufficient` at the post-update
  state makes `budget_ok` pass without writing: `check_budget_restart_suf`);
  the remaining local checks only narrow when it runs. Inputs: `BXI` at the
  entry state (placement, for the current-thread word) and the top's flag fact
  (the general entry reads the flags after the `FAULT_IP` write);
* `ioport_local_triple`: every postcondition of the general entry holds on the
  `true` results.
-/
import Fl4Proofs.P1.FastVmLocal
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {A : Type _} {st : machine.Store S} (ar : machine.Arch A) [L : LawfulStore st]

/-- **The syscall prefix keeps the current thread**: the `FAULT_IP` write
and a passing `budget_ok` (`update_timestamp`'s `CUR_TIME` / `CONSUMED`)
miss the current-thread word. -/
theorem prefix_cur_keep {T : Set U64} {s s1 s2 : S} {a a2 : A} {t v : U64}
    (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s))
    (et : sched.cur_thread st s = ok t) (htT : t ∈ T)
    (es1 : obj.Tcb.set_reg st t s layout.reg.FAULT_IP v = ok s1)
    (hb : syscall.budget_ok st ar s1 a = ok (true, s2, a2)) (hA : P0.ArchTotal ar) :
    sched.cur_thread st s2 = ok t := by
  have ht' := hT t htT
  obtain ⟨hct, hcn, -⟩ := ct_cn hN
  have hW1 := obj.Tcb.set_reg.wrK (L := L) s t layout.reg.FAULT_IP v ht' (by simp [layout.reg.FAULT_IP])
  rw [es1, WP.spec_ok] at hW1
  obtain ⟨KF, hKF, e1⟩ := hW1
  have hKF' : KF.val = 392 := by rw [hKF]; simp [layout.reg.FAULT_IP]
  have aF : Aligned (core.num.U64.wrapping_add t KF) := field_aligned ht' (by omega) (by omega)
  have hu := budget_ok_true ar hb
  obtain ⟨⟨n, b2⟩, hn, -⟩ := spec_ex_fd (hA.now a)
  have hN1 : NodePlaced st T s1 (L.cpu s1) := by rw [e1, LawfulStore.cpu_wr]; exact hN.wr
  rw [update_timestamp_ok ar hN1 hn] at hu
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (ok_inj_ff hu)
  have ec : ctA (L := L) s1 = ctA (L := L) s := by rw [e1, ctA_wr]
  have en : cnA (L := L) s1 = cnA (L := L) s := by rw [e1, cnA_wr]
  have hW : WritesIn st s (utW (L := L) s1 n)
      (fun b => b = core.num.U64.wrapping_add t KF ∨ b = ctA (L := L) s ∨ b = cnA (L := L) s) := by
    refine ⟨?_, ?_, fun b hb hn' => ?_⟩
    · unfold utW; rw [e1]; simp only [L.ksb_wr]
    · unfold utW; rw [e1]; simp only [LawfulStore.cpu_wr]
    · unfold utW
      rw [ec, en, mem_wr_ne' hcn hb (fun e => hn' (Or.inr (Or.inr e.symm))),
        mem_wr_ne' hct hb (fun e => hn' (Or.inr (Or.inl e.symm))), e1,
        mem_wr_ne' aF hb (fun e => hn' (Or.inl e.symm))]
  have vb := nodeAt_val hN (off := layout.node.CUR_TIME) (by simp [layout.node.CUR_TIME])
  have vn := nodeAt_val hN (off := layout.node.CONSUMED) (by simp [layout.node.CONSUMED])
  have nd := hN.disj t htT
  have na := hN.align
  have tvF := tcb_wadd_val ht' (o := KF) (by omega)
  have vC := nodeAt_val hN (off := layout.node.CUR_THREAD) (by simp [layout.node.CUR_THREAD])
  have aC : Aligned (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) :=
    nodeAt_aligned hN (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
  have eC : L.nodeAt (utW (L := L) s1 n) (L.cpu (utW (L := L) s1 n)) layout.node.CUR_THREAD =
      L.nodeAt s (L.cpu s) layout.node.CUR_THREAD := by
    rw [hW.2.1, nodeAt_of_ksb hW.1]
  have hm : L.mem (utW (L := L) s1 n) (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) =
      L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) := by
    refine hW.mem_eq aC ?_
    rintro (e | e | e) <;> (have e' := congrArg UScalar.val e)
    · rw [vC, tvF] at e'; simp [layout.node.CUR_THREAD] at e'; omega
    · unfold ctA at e'; rw [vC, vb] at e'; simp [layout.node.CUR_THREAD, layout.node.CUR_TIME] at e'
    · unfold cnA at e'; rw [vC, vn] at e'; simp [layout.node.CUR_THREAD, layout.node.CONSUMED] at e'
  rw [cur_thread_ok] at et ⊢
  rw [← ok_inj_ff et]
  unfold LawfulStore.curW; rw [eC, hm]

/-- **`syscall … true` for an invocation (`SysCall` / `SysSend`)** with the
trap flag clear and `budget_ok` passing: `dispatch_syscall`'s
`handle_invocation` / `after_invocation` arm, with the local entry's
arguments, then `finish`. -/
theorem syscall_inv_same {s s1 s2 s3 s4 s5 : S} {a a1 a2 a3 a4 : A} {t nx i1 cptr : U64} {number : I64}
    {r : core.result.Result Unit error.Exc} {x : Bool}
    (hn : number = fl4_abi.syscall.SysCall ∨ number = fl4_abi.syscall.SysSend)
    (et : sched.cur_thread st s = ok t) (enx : obj.Tcb.reg st t s layout.reg.NEXT_IP = ok nx)
    (es1 : obj.Tcb.set_reg st t s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1)
    (ef : obj.Tcb.flags st t s1 = ok i1)
    (c1 : ¬ (i1 &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true)
    (eb : syscall.budget_ok st ar s1 a = ok (true, s2, a1))
    (et2 : sched.cur_thread st s2 = ok t) (ecp : obj.Tcb.reg st t s2 layout.reg.CAP = ok cptr)
    (ehi : syscall.handle_invocation st ar s2 a1 (decide (number = fl4_abi.syscall.SysCall)) true
      (decide (number = fl4_abi.syscall.SysCall)) false cptr = ok (r, s3, a2))
    (eai : syscall.after_invocation st ar s3 a2 r = ok (x, s4, a3))
    (efi : syscall.finish st ar s4 a3 = ok (s5, a4)) :
    syscall.handle_syscall st ar s a number = ok (s5, a4) := by
  have n15 : fl4_abi.syscall.SysCall ≠ fl4_abi.syscall.SysSend := by
    unfold fl4_abi.syscall.SysCall fl4_abi.syscall.SysSend; decide
  have n16 : fl4_abi.syscall.SysCall ≠ fl4_abi.syscall.SysNBSend := by
    unfold fl4_abi.syscall.SysCall fl4_abi.syscall.SysNBSend; decide
  have hd : syscall.dispatch_syscall st ar s2 a1 number = ok (s4, a3) := by
    unfold syscall.dispatch_syscall
    rw [et2]; simp only [bind_ok]
    rw [ecp]; simp only [bind_ok]
    rw [reg_ok]; simp only [bind_ok]
    rcases hn with rfl | rfl
    · rw [decide_eq_true (rfl : fl4_abi.syscall.SysCall = fl4_abi.syscall.SysCall)] at ehi
      rw [if_neg n15, if_neg n16, if_pos rfl]
      rw [ehi]; simp only [bind_ok, uncurry_apply_pair]
      try dsimp only
      rw [eai]
      try simp only [bind_ok, uncurry_apply_pair]
      try rfl
    · rw [decide_eq_false (Ne.symm n15)] at ehi
      rw [if_pos rfl]
      rw [ehi]; simp only [bind_ok, uncurry_apply_pair]
      try dsimp only
      rw [eai]
      try simp only [bind_ok, uncurry_apply_pair]
      try rfl
  have c2 : ¬ number < fl4_abi.syscall.SYSCALL_MIN := by
    rcases hn with rfl | rfl
    · unfold fl4_abi.syscall.SysCall fl4_abi.syscall.SYSCALL_MIN
      first | decide | simp | (simp [IScalar.lt_equiv]) | (simp [IScalar.lt_equiv]; omega)
    · unfold fl4_abi.syscall.SysSend fl4_abi.syscall.SYSCALL_MIN
      first | decide | simp | (simp [IScalar.lt_equiv]) | (simp [IScalar.lt_equiv]; omega)
  have c3 : ¬ number > fl4_abi.syscall.SYSCALL_MAX := by
    rcases hn with rfl | rfl
    · unfold fl4_abi.syscall.SysCall fl4_abi.syscall.SYSCALL_MAX
      first | decide | simp | (simp [IScalar.lt_equiv]) | (simp [IScalar.lt_equiv]; omega)
    · unfold fl4_abi.syscall.SysSend fl4_abi.syscall.SYSCALL_MAX
      first | decide | simp | (simp [IScalar.lt_equiv]) | (simp [IScalar.lt_equiv]; omega)
  have c4 : ¬ number = fl4_abi.syscall.SysReplyRecv := by
    rcases hn with rfl | rfl
    · unfold fl4_abi.syscall.SysCall fl4_abi.syscall.SysReplyRecv; decide
    · unfold fl4_abi.syscall.SysSend fl4_abi.syscall.SysReplyRecv; decide
  unfold syscall.handle_syscall syscall.syscall
  rw [et]; simp only [bind_ok]
  rw [enx]; simp only [lift, bind_ok]
  rw [es1]; simp only [bind_ok]
  rw [ef]; simp only [lift, bind_ok, if_neg c1, if_neg c2, if_neg c3]
  rw [eb]; simp only [bind_ok, uncurry_apply_pair, ↓reduceIte, if_true, eq_self_iff_true]
  rw [if_neg c4]
  rw [hd]; simp only [bind_ok, uncurry_apply_pair]
  rw [efi]; simp only [bind_ok, uncurry_apply_pair]

/-- **`ioport_local_same`: the I/O port entry beside the serial gate, where
it ran, is the general entry** `syscall.handle_syscall` (module docstring). -/
theorem ioport_local_same (hA : P0.ArchTotal ar) {T Cs Sg : Set U64} {s s' : S} {a a' : A} {number : I64}
    {Ω Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hflag : ∀ t v, sched.cur_thread st s = ok t → obj.Tcb.flags st t (L.wr s (regA t layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (h : syscall.handle_ioport_local st ar s a number = ok (true, s', a')) :
    syscall.handle_syscall st ar s a number = ok (s', a') := by
  obtain ⟨⟨Q, R, hSQ⟩, -, -, -, -⟩ := hI
  have hT : TcbPlaced T := hSQ.tcbs
  have hcC : L.cpu s ∈ Cs := hSQ.cur
  have hN : NodePlaced st T s (L.cpu s) := hSQ.nodes _ hcC
  have hcT : L.curW s ∈ T := hSQ.curT
  unfold syscall.handle_ioport_local at h
  try simp only [lift, bind_ok] at h
  obtain ⟨t, et, h⟩ := bind_eq_ok h
  obtain ⟨info, -, h⟩ := bind_eq_ok h
  rw [num_domains_ne_one_false] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨i, -, h⟩ := bind_eq_ok h
  by_cases c1 : (i &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true
  · rw [if_pos c1] at h; simp at h
  rw [if_neg c1] at h
  -- the number: `SysCall` or `SysSend`
  have hn : number = fl4_abi.syscall.SysCall ∨ number = fl4_abi.syscall.SysSend := by
    by_cases hc : (number != fl4_abi.syscall.SysCall) = true
    · rw [if_pos hc] at h
      by_cases hs : (number != fl4_abi.syscall.SysSend) = true
      · rw [if_pos hs] at h; simp at h
      · simp only [bne_iff_ne, ne_eq, not_not] at hs; exact Or.inr hs
    · simp only [bne_iff_ne, ne_eq, not_not] at hc; exact Or.inl hc
  by_cases hc : (number != fl4_abi.syscall.SysCall) = true
  on_goal 2 => rw [if_neg hc] at h
  on_goal 1 =>
    rw [if_pos hc] at h
    by_cases hs : (number != fl4_abi.syscall.SysSend) = true
    on_goal 1 => rw [if_pos hs] at h; simp at h
    rw [if_neg hs] at h
  all_goals
    obtain ⟨b, -, h⟩ := bind_eq_ok h
    cases b
    · simp at h
    simp only [↓reduceIte] at h
    obtain ⟨nx, enx, h⟩ := bind_eq_ok h
    obtain ⟨s1, es1, h⟩ := bind_eq_ok h
    obtain ⟨⟨s2, a1⟩, eu, h⟩ := bind_eq_ok h
    try simp only [uncurry_apply_pair] at h
    try dsimp only at h
    obtain ⟨cptr, ecp, h⟩ := bind_eq_ok h
    obtain ⟨csc, ecsc, h⟩ := bind_eq_ok h
    obtain ⟨i3, -, h⟩ := bind_eq_ok h
    by_cases g3 : (i3 != sched.ACTION_RESUME_CURRENT) = true
    · rw [if_pos g3] at h; simp at h
    rw [if_neg g3] at h
    obtain ⟨i4, -, h⟩ := bind_eq_ok h
    by_cases g4 : (i4 != 0#u64) = true
    · rw [if_pos g4] at h; simp at h
    rw [if_neg g4] at h
    by_cases g5 : (info.extra_caps != 0#u64) = true
    · rw [if_pos g5] at h; simp at h
    rw [if_neg g5] at h
    obtain ⟨b1, -, h⟩ := bind_eq_ok h
    cases b1
    · simp at h
    simp only [↓reduceIte] at h
    obtain ⟨c, ec, h⟩ := bind_eq_ok h
    obtain ⟨b2, eb, h⟩ := bind_eq_ok h
    cases b2
    · simp at h
    simp only [↓reduceIte] at h
    obtain ⟨b3, -, h⟩ := bind_eq_ok h
    cases b3
    · simp at h
    simp only [↓reduceIte] at h
    obtain ⟨⟨r, s3, a2⟩, ehi, h⟩ := bind_eq_ok h
    try simp only [uncurry_apply_pair] at h
    try dsimp only at h
    obtain ⟨⟨x, s4, a3⟩, eai, h⟩ := bind_eq_ok h
    try simp only [uncurry_apply_pair] at h
    try dsimp only at h
    obtain ⟨⟨s5, a4⟩, efi, h⟩ := bind_eq_ok h
    try simp only [uncurry_apply_pair] at h
    have e5 := ok_inj_ff h
    simp only [Prod.mk.injEq, true_and] at e5
    obtain ⟨rfl, rfl⟩ := e5
    have hb : syscall.budget_ok st ar s1 a = ok (true, s2, a1) := by
      unfold syscall.budget_ok
      rw [eu]; simp only [bind_ok, uncurry_apply_pair]
      exact check_budget_restart_suf ar ecsc ec eb
    have htT : t ∈ T := by
      rw [cur_thread_ok] at et; rw [← ok_inj_ff et]; exact hcT
    have et2 := prefix_cur_keep ar hT hN et htT es1 hb hA
    -- the flags word at the `FAULT_IP`-written state: trap clear (the top's fact)
    have hs1 : s1 = L.wr s (regA t layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx 2#u64) := by
      have hW1 := obj.Tcb.set_reg.wrK (L := L) s t layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64)
        (hT t htT) (by simp [layout.reg.FAULT_IP])
      rw [es1, WP.spec_ok] at hW1
      obtain ⟨K, hK, e1⟩ := hW1
      obtain ⟨K', hK', eK'⟩ := regA_eq (hT t htT) (r := layout.reg.FAULT_IP) (by simp [layout.reg.FAULT_IP])
      rw [e1, eK']; congr 2; apply UScalar.eq_of_val_eq; rw [hK, hK']
    have hfl := hflag t (core.num.U64.wrapping_sub nx 2#u64) et
    rw [← hs1] at hfl
    obtain ⟨fl, efl, hfl0⟩ := spec_ex_fd hfl
    have c1' : ¬ (fl &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true := by
      rw [hfl0]; simp
    exact syscall_inv_same ar hn et enx es1 efl c1' hb et2 ecp ehi eai efi

/-- **The I/O port local entry where it ran: the general entry's
postconditions** (on the `true` results). -/
theorem ioport_local_triple (hA : P0.ArchTotal ar) {T Cs Sg : Set U64} {s : S} {a : A} {number : I64}
    {P : S × A → Prop}
    {Ω Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hflag : ∀ t v, sched.cur_thread st s = ok t → obj.Tcb.flags st t (L.wr s (regA t layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hG : syscall.handle_syscall st ar s a number ⦃ P ⦄) :
    syscall.handle_ioport_local st ar s a number ⦃ r => r.1 = true → P (r.2.1, r.2.2) ⦄ := by
  obtain ⟨⟨b, s', a'⟩, e, -⟩ := spec_ex_fd (P0.syscall.handle_ioport_local.p0 st ar s a number L.total hA)
  rw [e, WP.spec_ok]
  intro hb
  simp only at hb
  subst hb
  have hs := ioport_local_same ar hA hI hflag e
  rw [hs, WP.spec_ok] at hG
  exact hG

end

end Fl4Proofs.P1
