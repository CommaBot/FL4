/-
# The x86 `SysVMEnter` beside the serial gate (FL4 #104, line lvm)

`localvm.handle_vm_enter_local` (fl4-sync's `local_vm_syscall` for `SysVMEnter`):

* `vm_enter_local_same`: an accepted run ends where `syscall.handle_syscall …
  SysVMEnter` ends. The general entry is `syscall` with an unknown number
  (`SysVMEnter < SYSCALL_MIN`, `lvm_vmenter_lt_min`). It runs the same `FAULT_IP`
  write and then `handle_unknown_syscall`, where `debug_syscall` declines without
  writes (`lvm_debug_vmenter`) and `SysVMEnter` is not `SysSetTLSBase`. Its VMEnter
  case then reads `virtualization` at the entry's Arch value, which is the value the
  local check read, since `debug_syscall` returns it unchanged. It reads the current
  thread, its flags and its bound VCPU at the `FAULT_IP`-written state, where they
  hold what the local entry read (the write misses them). `budget_ok` is the local
  `update_timestamp` followed by a `check_budget_restart` that passes without writing
  (`check_budget_restart_suf`: the local entry checked `sufficient` at that state).
  Then `vcpu.enter` and `finish`, as the local entry runs them.
* `vm_enter_local_decline`: a declined run returned the entry state, or the prefix
  (`LocalPre`) with the number `SysVMEnter`.
* `vm_enter_local_triple`: every postcondition of the general entry holds on the
  accepted results.

**No named premise.** The [P] premise planned for this piece ("`virtualization` is
unchanged across `now`") is not needed: the general VMEnter path reads
`virtualization` before its `budget_ok`, at the same Arch value as the local check.
Hypotheses: `TcbPlaced`, `NodePlaced` at the entry state and the current thread
placed (P1 facts of `BXI`, `BXI.tcbNode`), Arch totality.

Not here: the decline's `pre_same` (the general entry from the prefix's state equals
the one from the entry state). `FastLocalDecline.syscall_pre_same` covers only
`RoT` numbers, which `SysVMEnter` is not: `handoff/lvm.md`.

P1 invariant: the P1 top leaves `SysVMEnter` out (`P3Place.vmchk`), so these
results move to the local entry whatever P1 later proves for the general one.
-/
import Fl4Proofs.P1.LocalVmExit
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

/-- `SysVMEnter` is below the native syscall range. -/
theorem lvm_vmenter_lt_min : fl4_abi.syscall.SysVMEnter < fl4_abi.syscall.SYSCALL_MIN := by
  unfold fl4_abi.syscall.SysVMEnter fl4_abi.syscall.SYSCALL_MIN
  first | decide | (simp [IScalar.lt_equiv]) | (simp [IScalar.lt_equiv]; omega)

theorem lvm_vmenter_ne_putc : ¬ fl4_abi.syscall.SysVMEnter = fl4_abi.syscall.SysDebugPutChar := by
  unfold fl4_abi.syscall.SysVMEnter fl4_abi.syscall.SysDebugPutChar; decide
theorem lvm_vmenter_ne_dump : ¬ fl4_abi.syscall.SysVMEnter = fl4_abi.syscall.SysDebugDumpScheduler := by
  unfold fl4_abi.syscall.SysVMEnter fl4_abi.syscall.SysDebugDumpScheduler; decide
theorem lvm_vmenter_ne_tls : ¬ fl4_abi.syscall.SysVMEnter = fl4_abi.syscall.SysSetTLSBase := by
  unfold fl4_abi.syscall.SysVMEnter fl4_abi.syscall.SysSetTLSBase; decide
theorem lvm_vmenter_ne_halt : ¬ fl4_abi.syscall.SysVMEnter = fl4_abi.syscall.SysDebugHalt := by
  unfold fl4_abi.syscall.SysVMEnter fl4_abi.syscall.SysDebugHalt; decide
theorem lvm_vmenter_ne_snap : ¬ fl4_abi.syscall.SysVMEnter = fl4_abi.syscall.SysDebugSnapshot := by
  unfold fl4_abi.syscall.SysVMEnter fl4_abi.syscall.SysDebugSnapshot; decide
theorem lvm_vmenter_ne_capid : ¬ fl4_abi.syscall.SysVMEnter = fl4_abi.syscall.SysDebugCapIdentify := by
  unfold fl4_abi.syscall.SysVMEnter fl4_abi.syscall.SysDebugCapIdentify; decide
theorem lvm_vmenter_ne_name : ¬ fl4_abi.syscall.SysVMEnter = fl4_abi.syscall.SysDebugNameThread := by
  unfold fl4_abi.syscall.SysVMEnter fl4_abi.syscall.SysDebugNameThread; decide
theorem lvm_vmenter_ne_aff : ¬ fl4_abi.syscall.SysVMEnter = fl4_abi.syscall.SysDebugGetThreadAffinity := by
  unfold fl4_abi.syscall.SysVMEnter fl4_abi.syscall.SysDebugGetThreadAffinity; decide
theorem lvm_vmenter_ne_ipi : ¬ fl4_abi.syscall.SysVMEnter = fl4_abi.syscall.SysDebugSendIPI := by
  unfold fl4_abi.syscall.SysVMEnter fl4_abi.syscall.SysDebugSendIPI; decide

section
variable {S : Type _} {A : Type _} {st : machine.Store S} (ar : machine.Arch A)

/-- **`debug_syscall` declines `SysVMEnter` without writes.** -/
theorem lvm_debug_vmenter (s : S) (a : A) (t : obj.Tcb) :
    syscall.debug_syscall st ar s a t fl4_abi.syscall.SysVMEnter = ok (false, s, a) := by
  unfold syscall.debug_syscall
  simp only [lvm_vmenter_ne_halt, lvm_vmenter_ne_snap, lvm_vmenter_ne_capid, lvm_vmenter_ne_name,
    lvm_vmenter_ne_aff, lvm_vmenter_ne_ipi, fl4_abi.config.ENABLE_SMP_SUPPORT, ↓reduceIte, if_false]

set_option maxHeartbeats 8000000 in
/-- **A declined `handle_vm_enter_local`**: the entry state, or the prefix
(`LocalPre`) of a `SysVMEnter`. -/
theorem vm_enter_local_decline {s s' : S} {a a' : A} {number : I64} {v n : U64}
    (h : localvm.handle_vm_enter_local st ar s a number v n = ok (false, s', a')) :
    (s' = s ∧ a' = a) ∨ (LocalPre (st := st) ar s a (s', a') ∧ number = fl4_abi.syscall.SysVMEnter) := by
  have fin : ∀ {x y : S} {u w : A}, (ok (false, x, u) : Result (Bool × S × A)) = ok (false, y, w) →
      y = x ∧ w = u := by
    intro x y u w e
    have e := ok_inj_ff e
    simp only [Prod.mk.injEq, true_and] at e
    exact ⟨e.1.symm, e.2.symm⟩
  unfold localvm.handle_vm_enter_local at h
  try simp only [lift, bind_ok] at h
  obtain ⟨t, et, h⟩ := bind_eq_ok h
  obtain ⟨cpu, -, h⟩ := bind_eq_ok h
  rw [num_domains_ne_one_false] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  by_cases cn : (number != fl4_abi.syscall.SysVMEnter) = true
  · rw [if_pos cn] at h; exact Or.inl (fin h)
  rw [if_neg cn] at h
  have hn : number = fl4_abi.syscall.SysVMEnter := by simp only [bne_iff_ne, ne_eq, not_not] at cn; exact cn
  obtain ⟨i, -, h⟩ := bind_eq_ok h
  by_cases c1 : (i &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true
  · rw [if_pos c1] at h; exact Or.inl (fin h)
  rw [if_neg c1] at h
  obtain ⟨i2, -, h⟩ := bind_eq_ok h
  by_cases c2 : i2 = 0#u64
  · rw [if_pos c2] at h; exact Or.inl (fin h)
  rw [if_neg c2] at h
  by_cases c3 : v = 0#u64
  · rw [if_pos c3] at h; exact Or.inl (fin h)
  rw [if_neg c3] at h
  obtain ⟨i3, -, h⟩ := bind_eq_ok h
  by_cases c4 : (i3 != v) = true
  · rw [if_pos c4] at h; exact Or.inl (fin h)
  rw [if_neg c4] at h
  obtain ⟨i4, -, h⟩ := bind_eq_ok h
  by_cases c5 : (i4 != n) = true
  · rw [if_pos c5] at h; exact Or.inl (fin h)
  rw [if_neg c5] at h
  obtain ⟨b, -, h⟩ := bind_eq_ok h
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte] at h; exact Or.inl (fin h)
  simp only [↓reduceIte] at h
  obtain ⟨csc, -, h⟩ := bind_eq_ok h
  obtain ⟨b1, -, h⟩ := bind_eq_ok h
  cases b1
  · simp only [Bool.false_eq_true, ↓reduceIte] at h; exact Or.inl (fin h)
  simp only [↓reduceIte] at h
  obtain ⟨i5, -, h⟩ := bind_eq_ok h
  by_cases c6 : (i5 != sched.TS_RUNNING) = true
  · rw [if_pos c6] at h; exact Or.inl (fin h)
  rw [if_neg c6] at h
  obtain ⟨b2, -, h⟩ := bind_eq_ok h
  cases b2
  · simp only [Bool.false_eq_true, ↓reduceIte] at h; exact Or.inl (fin h)
  simp only [↓reduceIte] at h
  obtain ⟨b3, -, h⟩ := bind_eq_ok h
  cases b3
  · simp only [Bool.false_eq_true, ↓reduceIte] at h; exact Or.inl (fin h)
  simp only [↓reduceIte] at h
  right
  obtain ⟨⟨s2, a1⟩, epre, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨e1, e2⟩ : s' = s2 ∧ a' = a1 := by
    have h' := spec_of_eq_fd h
    clear h
    revert h'
    decl_walk
    all_goals decl_leaf
  subst e1 e2
  unfold localvm.syscall_prefix at epre
  try simp only [lift, bind_ok] at epre
  obtain ⟨nx, enx, epre⟩ := bind_eq_ok epre
  obtain ⟨s1, es1, eu⟩ := bind_eq_ok epre
  try rw [insn_len_eq] at es1
  exact ⟨⟨t, nx, s1, et, enx, es1, eu⟩, hn⟩

variable [L : LawfulStore st]

set_option maxHeartbeats 8000000 in
/-- **`vm_enter_local_same`: a `SysVMEnter` beside the serial gate, where it ran,
is the general entry** `syscall.handle_syscall … SysVMEnter` (module docstring). -/
theorem vm_enter_local_same (hA : P0.ArchTotal ar) {T : Set U64} {s s' : S} {a a' : A} {number : I64}
    {v n : U64} (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s)) (hcT : L.curW s ∈ T)
    (h : localvm.handle_vm_enter_local st ar s a number v n = ok (true, s', a')) :
    syscall.handle_syscall st ar s a number = ok (s', a') := by
  unfold localvm.handle_vm_enter_local at h
  try simp only [lift, bind_ok] at h
  obtain ⟨t, et, h⟩ := bind_eq_ok h
  obtain ⟨cpu, -, h⟩ := bind_eq_ok h
  rw [num_domains_ne_one_false] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  by_cases cn : (number != fl4_abi.syscall.SysVMEnter) = true
  · rw [if_pos cn] at h; simp at h
  rw [if_neg cn] at h
  have hn : number = fl4_abi.syscall.SysVMEnter := by simp only [bne_iff_ne, ne_eq, not_not] at cn; exact cn
  obtain ⟨i, ei, h⟩ := bind_eq_ok h
  by_cases c1 : (i &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true
  · rw [if_pos c1] at h; simp at h
  rw [if_neg c1] at h
  obtain ⟨i2, ev, h⟩ := bind_eq_ok h
  by_cases c2 : i2 = 0#u64
  · rw [if_pos c2] at h; simp at h
  rw [if_neg c2] at h
  by_cases c3 : v = 0#u64
  · rw [if_pos c3] at h; simp at h
  rw [if_neg c3] at h
  obtain ⟨i3, eb3, h⟩ := bind_eq_ok h
  by_cases c4 : (i3 != v) = true
  · rw [if_pos c4] at h; simp at h
  rw [if_neg c4] at h
  have hi3 : i3 = v := by simp only [bne_iff_ne, ne_eq, not_not] at c4; exact c4
  obtain ⟨i4, -, h⟩ := bind_eq_ok h
  by_cases c5 : (i4 != n) = true
  · rw [if_pos c5] at h; simp at h
  rw [if_neg c5] at h
  obtain ⟨b, -, h⟩ := bind_eq_ok h
  cases b
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨csc, ecsc, h⟩ := bind_eq_ok h
  obtain ⟨b1, -, h⟩ := bind_eq_ok h
  cases b1
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨i5, -, h⟩ := bind_eq_ok h
  by_cases c6 : (i5 != sched.TS_RUNNING) = true
  · rw [if_pos c6] at h; simp at h
  rw [if_neg c6] at h
  obtain ⟨b2, -, h⟩ := bind_eq_ok h
  cases b2
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨b3, -, h⟩ := bind_eq_ok h
  cases b3
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨⟨s2, a1⟩, epre, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨now, -, h⟩ := bind_eq_ok h
  obtain ⟨i6, ecns, h⟩ := bind_eq_ok h
  obtain ⟨b4, eb4, h⟩ := bind_eq_ok h
  cases b4
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨b5, -, h⟩ := bind_eq_ok h
  cases b5
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨⟨x, s3, a3⟩, ecbr, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  try dsimp only at h
  obtain ⟨⟨s4, a4⟩, eent, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨⟨s5, a5⟩, efin, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  have e := ok_inj_ff h
  simp only [Prod.mk.injEq, true_and] at e
  obtain ⟨rfl, rfl⟩ := e
  -- the prefix
  unfold localvm.syscall_prefix at epre
  try simp only [lift, bind_ok] at epre
  obtain ⟨nx, enx, epre⟩ := bind_eq_ok epre
  obtain ⟨s1, es1, eu⟩ := bind_eq_ok epre
  try rw [insn_len_eq] at es1
  have htT : t ∈ T := by rw [cur_thread_ok] at et; rw [← ok_inj_ff et]; exact hcT
  have ht' := hT t htT
  obtain ⟨KF, hKF, hW⟩ := lt_prefix ar hT hN htT es1 eu hA
  -- the `FAULT_IP`-written state `s1`
  have hW1 := obj.Tcb.set_reg.wrK (L := L) s t layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) ht'
    (by simp [layout.reg.FAULT_IP])
  rw [es1, WP.spec_ok] at hW1
  obtain ⟨K1, hK1, e1⟩ := hW1
  have hK1' : K1.val = 392 := by rw [hK1]; simp [layout.reg.FAULT_IP]
  have aF : Aligned (core.num.U64.wrapping_add t K1) := field_aligned ht' (by omega) (by omega)
  have wK : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 392 →
      L.mem s1 (core.num.U64.wrapping_add t K) = L.mem s (core.num.U64.wrapping_add t K) := by
    intro K hK h8 hne
    rw [e1]
    exact mem_wr_ne' aF (field_aligned ht' hK h8) (tcb_word_ne ht' ht' (by omega) hK (fun _ => by omega))
  have et1 : sched.cur_thread st s1 = ok t := by
    rw [cur_thread_ok] at et ⊢
    rw [← ok_inj_ff et]
    have aC : Aligned (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) :=
      nodeAt_aligned hN (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
    unfold LawfulStore.curW
    rw [e1, LawfulStore.cpu_wr, nodeAt_of_ksb (L.ksb_wr _ _ _)]
    congr 1
    exact mem_wr_ne' aF aC (tcb_node_ne hN htT ht' (by omega) (by simp [layout.node.CUR_THREAD]))
  have efl : obj.Tcb.flags st t s1 = ok i := by
    rw [flags_ok] at ei ⊢
    rw [wK 3456#u64 (by simp) (by simp) (by simp)]
    exact ei
  have ebd : vcpu.bound st s1 t = ok i3 := by
    rw [eq_of_spec_fd (vcpu.bound.spec (L := L) s1 t), wK 3664#u64 (by simp) (by simp) (by simp),
      ← eq_of_spec_fd (vcpu.bound.spec (L := L) s t)]
    exact eb3
  -- `cur_sc` at the updated state
  have ecsc2 : sched.cur_sc st s2 = ok csc := by
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) s)] at ecsc
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) s2), ← ok_inj_ff ecsc]
    have aC : Aligned (L.nodeAt s (L.cpu s) layout.node.CUR_SC) :=
      nodeAt_aligned hN (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
    have eA : L.nodeA s2 layout.node.CUR_SC = L.nodeA s layout.node.CUR_SC := by
      unfold LawfulStore.nodeA; rw [hW.2.1, nodeAt_of_ksb hW.1]
    rw [eA]
    unfold LawfulStore.nodeA
    refine congrArg ok (hW.mem_eq aC ?_)
    have vS := nodeAt_val hN (off := layout.node.CUR_SC) (by simp [layout.node.CUR_SC])
    have vb := nodeAt_val hN (off := layout.node.CUR_TIME) (by simp [layout.node.CUR_TIME])
    have vn := nodeAt_val hN (off := layout.node.CONSUMED) (by simp [layout.node.CONSUMED])
    rintro (e | e | e)
    · exact tcb_node_ne hN htT ht' (by omega) (by simp [layout.node.CUR_SC]) e.symm
    · have e' := congrArg UScalar.val e; unfold ctA at e'; rw [vS, vb] at e'
      simp [layout.node.CUR_SC, layout.node.CUR_TIME] at e'
    · have e' := congrArg UScalar.val e; unfold cnA at e'; rw [vS, vn] at e'
      simp [layout.node.CUR_SC, layout.node.CONSUMED] at e'
  have hcb := check_budget_restart_suf ar ecsc2 ecns eb4
  rw [hcb] at ecbr
  have e3 := ok_inj_ff ecbr
  simp only [Prod.mk.injEq] at e3
  obtain ⟨-, rfl, rfl⟩ := e3
  have hb : syscall.budget_ok st ar s1 a = ok (true, s2, a1) := by
    unfold syscall.budget_ok
    rw [eu]; simp only [bind_ok, uncurry_apply_pair]
    exact hcb
  have c2' : (i2 != 0#u64) = true := by rw [bne_iff_ne]; exact c2
  have c3' : (i3 != 0#u64) = true := by rw [bne_iff_ne, hi3]; exact c3
  -- the general run
  rw [hn]
  unfold syscall.handle_syscall syscall.syscall
  rw [et]; simp only [bind_ok]
  rw [enx]; simp only [lift, bind_ok]
  rw [es1]; simp only [bind_ok]
  rw [efl]; simp only [lift, bind_ok, if_neg c1, if_pos lvm_vmenter_lt_min]
  unfold syscall.handle_unknown_syscall
  rw [et1]
  simp only [bind_ok, fl4_abi.config.PRINTING, fl4_abi.config.DEBUG_BUILD, fl4_abi.config.SET_TLS_BASE_SELF,
    ↓reduceIte, lvm_vmenter_ne_putc, lvm_vmenter_ne_dump, if_false]
  rw [lvm_debug_vmenter]
  simp only [bind_ok, uncurry_apply_pair, Bool.false_eq_true, ↓reduceIte, lvm_vmenter_ne_tls, if_false,
    eq_self_iff_true, if_true]
  rw [ev]; simp only [bind_ok, c2', ↓reduceIte, if_true]
  rw [ebd]; simp only [bind_ok, c3', ↓reduceIte, if_true]
  rw [hb]; simp only [bind_ok, uncurry_apply_pair, ↓reduceIte, if_true]
  rw [eent]; simp only [bind_ok, uncurry_apply_pair]
  rw [← localvm_finish_eq, efin]
  try simp only [bind_ok, uncurry_apply_pair]

/-- **The `SysVMEnter` local entry where it ran: the general entry's
postconditions** (on the `true` results). -/
theorem vm_enter_local_triple (hA : P0.ArchTotal ar) {T : Set U64} {s : S} {a : A} {number : I64}
    {v n : U64} (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s)) (hcT : L.curW s ∈ T)
    {P : S × A → Prop} (hG : syscall.handle_syscall st ar s a number ⦃ P ⦄) :
    localvm.handle_vm_enter_local st ar s a number v n ⦃ r => r.1 = true → P (r.2.1, r.2.2) ⦄ := by
  obtain ⟨⟨b, s', a'⟩, e, -⟩ :=
    spec_ex_fd (P0.localvm.handle_vm_enter_local.p0 st ar s a number v n L.total hA)
  rw [e, WP.spec_ok]
  intro hb
  simp only at hb
  subst hb
  have hs := vm_enter_local_same ar hA hT hN hcT e
  rw [hs, WP.spec_ok] at hG
  exact hG

end

end Fl4Proofs.P1
