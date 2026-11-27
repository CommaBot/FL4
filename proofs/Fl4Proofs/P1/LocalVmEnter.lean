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

* `vm_enter_pre_same` / `vm_enter_handle_pre_same`: after a decline's prefix
  (`LocalPre`) the general entry runs as from the entry state with the Arch value
  the prefix left. `FastLocalDecline.syscall_pre_same` covers only `RoT` numbers,
  which `SysVMEnter` is not; this is its copy with the unknown-syscall branch
  finished (`debug_syscall` declines at both states, `virtualization` at the same
  Arch value, the bound VCPU word missed by the prefix, `budget_ok_utW`). Needs
  `StoreExt` [P], as `syscall_pre_same` does.

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

set_option maxHeartbeats 8000000 in
/-- **`vm_enter_pre_same`: after the prefix of a declined `SysVMEnter` the
general `syscall` runs as from the entry state** with the Arch value the prefix
left. `FastLocalDecline.syscall_pre_same` with its last branch replaced: the
number is below the native range (`lvm_vmenter_lt_min`), so an untrapped run
takes `handle_unknown_syscall`, which reads the current thread (kept), declines
`debug_syscall` without writes (`lvm_debug_vmenter`), reads `virtualization`
at the same Arch value and the bound VCPU word (offset 3664, missed by the
prefix), and then runs `budget_ok` / `unknown_syscall_fault`, which do not see
the prefix's timestamp update (`budget_ok_utW`). -/
theorem vm_enter_pre_same (hX : StoreExt st) (hA : P0.ArchTotal ar) {T : Set U64} (hT : TcbPlaced T) {s : S}
    (hN : NodePlaced st T s (L.cpu s)) (hcT : L.curW s ∈ T) {a : A} {r : S × A}
    (hP : LocalPre (st := st) ar s a r) (f : Bool) :
    syscall.syscall st ar r.1 r.2 fl4_abi.syscall.SysVMEnter f =
      syscall.syscall st ar s r.2 fl4_abi.syscall.SysVMEnter f := by
  obtain ⟨rs, ra⟩ := r
  obtain ⟨t, nx, s1, et, enx, es1, eu⟩ := hP
  dsimp only
  have htT : t ∈ T := by rw [cur_thread_ok] at et; rw [← ok_inj_ff et]; exact hcT
  have ht' := hT t htT
  -- the `FAULT_IP` write
  have hW1 := obj.Tcb.set_reg.wrK (L := L) s t layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) ht'
    (by simp [layout.reg.FAULT_IP])
  rw [es1, WP.spec_ok] at hW1
  obtain ⟨KF, hKF, e1⟩ := hW1
  have hKF' : KF.val = 392 := by rw [hKF]; simp [layout.reg.FAULT_IP]
  have aF : Aligned (core.num.U64.wrapping_add t KF) := field_aligned ht' (by omega) (by omega)
  have tvF := tcb_wadd_val ht' (o := KF) (by omega)
  have hN1 : NodePlaced st T s1 (L.cpu s1) := by rw [e1, LawfulStore.cpu_wr]; exact hN.wr
  obtain ⟨n1, -, er⟩ := ut_now ar hA hN1 eu
  dsimp only at er
  subst er
  have ec1 : ctA (L := L) s1 = ctA (L := L) s := by rw [e1, ctA_wr]
  have en1 : cnA (L := L) s1 = cnA (L := L) s := by rw [e1, cnA_wr]
  have vb := nodeAt_val hN (off := layout.node.CUR_TIME) (by simp [layout.node.CUR_TIME])
  have vn := nodeAt_val hN (off := layout.node.CONSUMED) (by simp [layout.node.CONSUMED])
  have nd := hN.disj t htT
  have twC : ∀ K : U64, K.val < 4096 → core.num.U64.wrapping_add t K ≠ ctA (L := L) s := by
    intro K hK e
    have tvK := tcb_wadd_val ht' (o := K) hK
    have e' := congrArg UScalar.val e
    unfold ctA at e'; rw [vb, tvK] at e'; simp [layout.node.CUR_TIME] at e'; omega
  have twN : ∀ K : U64, K.val < 4096 → core.num.U64.wrapping_add t K ≠ cnA (L := L) s := by
    intro K hK e
    have tvK := tcb_wadd_val ht' (o := K) hK
    have e' := congrArg UScalar.val e
    unfold cnA at e'; rw [vn, tvK] at e'; simp [layout.node.CONSUMED] at e'; omega
  have hU : ∀ b, Aligned b → b ≠ ctA (L := L) s → b ≠ cnA (L := L) s → b ≠ core.num.U64.wrapping_add t KF →
      L.mem (utW (L := L) s1 n1) b = L.mem s b := by
    intro b hb h1 h2 h3
    rw [utW_mem hN1 n1 hb (by rw [ec1]; exact h1) (by rw [en1]; exact h2), e1, mem_wr_ne' aF hb (Ne.symm h3)]
  have hU1 : ∀ b, Aligned b → b ≠ ctA (L := L) s → b ≠ cnA (L := L) s →
      L.mem (utW (L := L) s1 n1) b = L.mem s1 b := by
    intro b hb h1 h2
    exact utW_mem hN1 n1 hb (by rw [ec1]; exact h1) (by rw [en1]; exact h2)
  have hcU : L.cpu (utW (L := L) s1 n1) = L.cpu s := by rw [utW_cpu, e1, LawfulStore.cpu_wr]
  have hkU : L.ksb (utW (L := L) s1 n1) = L.ksb s := by rw [utW_ksb, e1, LawfulStore.ksb_wr]
  have vC := nodeAt_val hN (off := layout.node.CUR_THREAD) (by simp [layout.node.CUR_THREAD])
  have aC : Aligned (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) :=
    nodeAt_aligned hN (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
  -- (1) the current thread, at both states
  have hct1 : sched.cur_thread st (utW (L := L) s1 n1) = ok t := by
    rw [cur_thread_ok] at et ⊢
    rw [← ok_inj_ff et]
    unfold LawfulStore.curW
    rw [hcU, nodeAt_of_ksb hkU]
    congr 1
    refine hU _ aC ?_ ?_ ?_
    · intro e; have e' := congrArg UScalar.val e
      unfold ctA at e'; rw [vC, vb] at e'; simp [layout.node.CUR_THREAD, layout.node.CUR_TIME] at e'
    · intro e; have e' := congrArg UScalar.val e
      unfold cnA at e'; rw [vC, vn] at e'; simp [layout.node.CUR_THREAD, layout.node.CONSUMED] at e'
    · intro e; have e' := congrArg UScalar.val e
      rw [vC, tvF] at e'; simp [layout.node.CUR_THREAD] at e'; omega
  have et1 : sched.cur_thread st s1 = ok t := by
    rw [cur_thread_ok] at et ⊢
    rw [← ok_inj_ff et]
    unfold LawfulStore.curW
    rw [e1, LawfulStore.cpu_wr, nodeAt_of_ksb (L.ksb_wr _ _ _)]
    congr 1
    exact mem_wr_ne' aF aC (tcb_node_ne hN htT ht' (by omega) (by simp [layout.node.CUR_THREAD]))
  -- (2) `NEXT_IP`
  obtain ⟨KN, hKN, eKN⟩ := regA_eq ht' (r := layout.reg.NEXT_IP) (by simp [layout.reg.NEXT_IP])
  have hKN' : KN.val = 368 := by rw [hKN]; simp [layout.reg.NEXT_IP]
  have aN : Aligned (core.num.U64.wrapping_add t KN) := field_aligned ht' (by omega) (by omega)
  have tvN := tcb_wadd_val ht' (o := KN) (by omega)
  have hreg1 : obj.Tcb.reg st t (utW (L := L) s1 n1) layout.reg.NEXT_IP = ok nx := by
    rw [reg_ok] at enx ⊢
    rw [← ok_inj_ff enx, eKN]
    congr 1
    refine hU _ aN (twC KN (by omega)) (twN KN (by omega)) ?_
    intro e; have e' := congrArg UScalar.val e; rw [tvN, tvF] at e'; omega
  -- (3) the `FAULT_IP` write again: the word holds the value already
  have hset1 : obj.Tcb.set_reg st t (utW (L := L) s1 n1) layout.reg.FAULT_IP
      (core.num.U64.wrapping_sub nx 2#u64) = ok (utW (L := L) s1 n1) := by
    have hW2 := obj.Tcb.set_reg.wrK (L := L) (utW (L := L) s1 n1) t layout.reg.FAULT_IP
      (core.num.U64.wrapping_sub nx 2#u64) ht' (by simp [layout.reg.FAULT_IP])
    obtain ⟨x, ex, K2, hK2, exK⟩ := spec_ex_fd hW2
    rw [ex, exK]
    have eK : K2 = KF := UScalar.eq_of_val_eq (by rw [hK2, hKF])
    rw [eK]
    have hv : L.mem (utW (L := L) s1 n1) (core.num.U64.wrapping_add t KF) = core.num.U64.wrapping_sub nx 2#u64 := by
      rw [hU1 _ aF (twC KF (by omega)) (twN KF (by omega)), e1, LawfulStore.mem_wr_same aF]
    rw [← hv, wr_mem hX _ aF]
  -- (4) the flags word
  have aFl : Aligned (core.num.U64.wrapping_add t 3456#u64) :=
    field_aligned ht' (by simp) (by simp)
  have hfl1 : L.mem (utW (L := L) s1 n1) (core.num.U64.wrapping_add t 3456#u64) =
      L.mem s1 (core.num.U64.wrapping_add t 3456#u64) :=
    hU1 _ aFl (twC _ (by simp)) (twN _ (by simp))
  -- (5) the timestamp update supersedes the prefix's
  have hb1 : ∀ a', syscall.budget_ok st ar (utW (L := L) s1 n1) a' = syscall.budget_ok st ar s1 a' :=
    fun a' => budget_ok_utW ar hX hA hN1 n1 a'
  have husf : ∀ a' m g, syscall.unknown_syscall_fault st ar (utW (L := L) s1 n1) a' m g =
      syscall.unknown_syscall_fault st ar s1 a' m g := by
    intro a' m g
    unfold syscall.unknown_syscall_fault
    rw [hb1]
  -- (6) the bound VCPU word
  have ebd : vcpu.bound st (utW (L := L) s1 n1) t = vcpu.bound st s1 t := by
    rw [eq_of_spec_fd (vcpu.bound.spec (L := L) (utW (L := L) s1 n1) t), eq_of_spec_fd (vcpu.bound.spec (L := L) s1 t),
      hU1 _ (field_aligned ht' (by simp) (by simp)) (twC _ (by simp)) (twN _ (by simp))]
  -- (7) the VMEnter case of `handle_unknown_syscall`
  have huk : ∀ a' g, syscall.handle_unknown_syscall st ar (utW (L := L) s1 n1) a' fl4_abi.syscall.SysVMEnter g =
      syscall.handle_unknown_syscall st ar s1 a' fl4_abi.syscall.SysVMEnter g := by
    intro a' g
    unfold syscall.handle_unknown_syscall
    rw [hct1, et1]
    simp only [bind_ok, fl4_abi.config.PRINTING, fl4_abi.config.DEBUG_BUILD, fl4_abi.config.SET_TLS_BASE_SELF,
      ↓reduceIte, lvm_vmenter_ne_putc, lvm_vmenter_ne_dump, if_false]
    rw [lvm_debug_vmenter, lvm_debug_vmenter]
    simp only [bind_ok, uncurry_apply_pair, Bool.false_eq_true, ↓reduceIte, lvm_vmenter_ne_tls, if_false,
      eq_self_iff_true, if_true]
    simp only [ebd, hb1, husf]
  unfold syscall.syscall
  rw [hct1, et]
  simp only [bind_ok]
  rw [hreg1, enx]
  simp only [lift, bind_ok]
  rw [hset1, es1]
  simp only [bind_ok]
  rw [flags_ok, flags_ok, hfl1]
  simp only [lift, bind_ok]
  rw [husf]
  by_cases c1 : (L.mem s1 (core.num.U64.wrapping_add t 3456#u64) &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS !=
      0#u64) = true
  · simp only [if_pos c1]
  · simp only [if_neg c1, if_pos lvm_vmenter_lt_min]
    exact huk _ _

/-- `vm_enter_pre_same` for `handle_syscall`: fl4-sync's general fallback after
a declined local `SysVMEnter` (`vm_enter_local_decline`'s `LocalPre` arm). -/
theorem vm_enter_handle_pre_same (hX : StoreExt st) (hA : P0.ArchTotal ar) {T : Set U64} (hT : TcbPlaced T) {s : S}
    (hN : NodePlaced st T s (L.cpu s)) (hcT : L.curW s ∈ T) {a : A} {r : S × A}
    (hP : LocalPre (st := st) ar s a r) :
    syscall.handle_syscall st ar r.1 r.2 fl4_abi.syscall.SysVMEnter =
      syscall.handle_syscall st ar s r.2 fl4_abi.syscall.SysVMEnter := by
  unfold syscall.handle_syscall
  rw [vm_enter_pre_same ar hX hA hT hN hcT hP true]

end

end Fl4Proofs.P1
