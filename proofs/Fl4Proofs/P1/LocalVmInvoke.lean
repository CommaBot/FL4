/-
# The x86 VCPU state invocations beside the serial gate (FL4 #104, line lvm)

`localvm.handle_vcpu_invocation_local` (fl4-sync's `local_vm_syscall` for a
`SysCall` / `SysSend` whose label is one of the eight VCPU state labels,
`localvm.is_vcpu_state_label`):

* `lvm_decode_np` (`P1/LocalVmDecNP`): `vcpu.decode` never returns `Err Preempted`.
  (A `Fault` or `Lookup` error would be harmless: the general `handle_invocation`
  and the local reply arm both drop it.)
* `vcpu_invocation_local_same`: an accepted run ends where `syscall.handle_syscall
  … number` ends (`number` is `SysCall` or `SysSend`). The general path: the same
  `FAULT_IP` write and `update_timestamp` (`lt_prefix`, `inv_prefix`); flags read
  at the `FAULT_IP`-written state (the write misses them); `budget_ok` passes
  without writing (`check_budget_restart_suf`); `dispatch_syscall`'s Call / Send
  arm; `handle_invocation` reads the same message info, finds fl4-sync's slot
  (premise `hL`, as `set_timer_local_same`'s) holding `Vcpu v`, the same IPC buffer and no extra caps (the
  local entry read both at the same state); `decode_invocation`'s `Vcpu` arm is
  the same `vcpu.decode` call; the reply arms agree on every result but
  `Err Preempted` (`lvm_decode_np`); `after_invocation` passes; `finish`
  (`localvm_finish_eq`).
* `vcpu_invocation_local_decline`: a declined run returned the entry state, or
  the prefix (`LocalPre`) with `RoT` (the number is `SysCall` / `SysSend`), so
  `FastLocalDecline.handle_syscall_pre_same` applies as is.
* `vcpu_invocation_local_triple`: every postcondition of the general entry holds
  on the accepted results; `vcpu_invocation_local_entry`: the same from the P1
  top's form (`∀ number ≠ SysVMEnter, handle_syscall … ⦃ Q ⦄`, the first
  conjunct of `kernel_entry.entry_of*` and of P3's `kernel_entry_entryInvU29`).
  So this path's P1 invariant is the general entry's, which the P1 top proves
  through `EntryHyps.inv` = `syscall.handle_invocation.inv` with the `vcpu`
  decode gap (`QueueDecVcpu.decGap_vcpu`): nothing VCPU-specific is left.

**Named premise.** `hL` [J] (fl4-sync's contract, as in `set_timer_local_same`):
the general CSpace lookup of the `CAP` register finds the slot fl4-sync passed
(`lookup_slot_locked` resolved it with the same walk, its slots locked), and that
slot holds `Vcpu v` (fl4-sync passes `v` from the cap it found; the local entry
re-checks it, but the derived `PartialEq` on caps has no P0/P1 meaning lemma). Other
hypotheses: `BXI` and `CnOff` at the entry state (P1 facts of `EntryInv`, as in
`set_timer_local_same`), Arch totality. No premise on `vcpu.stall`,
`vcpu_sync` or `virtualization`: both runs make the same `vcpu.decode` call.
-/
import Fl4Proofs.P1.LocalVmDecNP
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {A : Type _} {st : machine.Store S} (ar : machine.Arch A)

/-- The local entry's two number tests, when one of them passes, run the same body. -/
theorem lvm_ite2 {α : Type _} {c1 c2 : Prop} [Decidable c1] [Decidable c2] {X B : α} (h : ¬ (c1 ∧ c2)) :
    (if c1 then (if c2 then X else B) else B) = B := by
  by_cases h1 : c1
  · rw [if_pos h1, if_neg (fun h2 => h ⟨h1, h2⟩)]
  · rw [if_neg h1]

theorem lvm_num_nc {number : I64}
    (h : number = fl4_abi.syscall.SysCall ∨ number = fl4_abi.syscall.SysSend) :
    ¬ ((number != fl4_abi.syscall.SysCall) = true ∧ (number != fl4_abi.syscall.SysSend) = true) := by
  rintro ⟨h1, h2⟩
  rcases h with rfl | rfl
  · simp at h1
  · simp at h2

set_option maxHeartbeats 8000000 in
/-- **A declined `handle_vcpu_invocation_local`**: the entry state, or the
prefix (`LocalPre`) of a `SysCall` / `SysSend` (`RoT`: in the native range). -/
theorem vcpu_invocation_local_decline {s s' : S} {a a' : A} {number : I64} {slot : obj.Slot} {v : U64}
    (h : localvm.handle_vcpu_invocation_local st ar s a number slot v = ok (false, s', a')) :
    (s' = s ∧ a' = a) ∨ (LocalPre (st := st) ar s a (s', a') ∧ RoT st s number) := by
  have fin : ∀ {x y : S} {u w : A}, (ok (false, x, u) : Result (Bool × S × A)) = ok (false, y, w) →
      y = x ∧ w = u := by
    intro x y u w e
    have e := ok_inj_ff e
    simp only [Prod.mk.injEq, true_and] at e
    exact ⟨e.1.symm, e.2.symm⟩
  unfold localvm.handle_vcpu_invocation_local at h
  try simp only [lift, bind_ok] at h
  obtain ⟨t, et, h⟩ := bind_eq_ok h
  obtain ⟨cpu, -, h⟩ := bind_eq_ok h
  obtain ⟨info, -, h⟩ := bind_eq_ok h
  rw [num_domains_ne_one_false] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨i, -, h⟩ := bind_eq_ok h
  by_cases c1 : (i &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true
  · rw [if_pos c1] at h; exact Or.inl (fin h)
  rw [if_neg c1] at h
  by_cases hnum : number = fl4_abi.syscall.SysCall ∨ number = fl4_abi.syscall.SysSend
  swap
  · have cn : (number != fl4_abi.syscall.SysCall) = true := by
      simp only [bne_iff_ne, ne_eq]; exact fun e => hnum (Or.inl e)
    have cs : (number != fl4_abi.syscall.SysSend) = true := by
      simp only [bne_iff_ne, ne_eq]; exact fun e => hnum (Or.inr e)
    rw [if_pos cn, if_pos cs] at h; exact Or.inl (fin h)
  rw [lvm_ite2 (lvm_num_nc hnum)] at h
  obtain ⟨b, -, h⟩ := bind_eq_ok h
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte] at h; exact Or.inl (fin h)
  simp only [↓reduceIte] at h
  by_cases c3 : (info.extra_caps != 0#u64) = true
  · rw [if_pos c3] at h; exact Or.inl (fin h)
  rw [if_neg c3] at h
  obtain ⟨i2, -, h⟩ := bind_eq_ok h
  by_cases c4 : i2 = 0#u64
  · rw [if_pos c4] at h; exact Or.inl (fin h)
  rw [if_neg c4] at h
  by_cases c5 : v = 0#u64
  · rw [if_pos c5] at h; exact Or.inl (fin h)
  rw [if_neg c5] at h
  obtain ⟨c, -, h⟩ := bind_eq_ok h
  obtain ⟨b1, -, h⟩ := bind_eq_ok h
  cases b1
  swap
  · simp only [↓reduceIte] at h; exact Or.inl (fin h)
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨i3, -, h⟩ := bind_eq_ok h
  by_cases c6 : (i3 != t) = true
  · rw [if_pos c6] at h; exact Or.inl (fin h)
  rw [if_neg c6] at h
  obtain ⟨i4, -, h⟩ := bind_eq_ok h
  by_cases c7 : (i4 != v) = true
  · rw [if_pos c7] at h; exact Or.inl (fin h)
  rw [if_neg c7] at h
  obtain ⟨csc, -, h⟩ := bind_eq_ok h
  obtain ⟨b2, -, h⟩ := bind_eq_ok h
  cases b2
  · simp only [Bool.false_eq_true, ↓reduceIte] at h; exact Or.inl (fin h)
  simp only [↓reduceIte] at h
  obtain ⟨i5, -, h⟩ := bind_eq_ok h
  by_cases c8 : (i5 != sched.TS_RUNNING) = true
  · rw [if_pos c8] at h; exact Or.inl (fin h)
  rw [if_neg c8] at h
  obtain ⟨b3, -, h⟩ := bind_eq_ok h
  cases b3
  · simp only [Bool.false_eq_true, ↓reduceIte] at h; exact Or.inl (fin h)
  simp only [↓reduceIte] at h
  obtain ⟨b4, -, h⟩ := bind_eq_ok h
  cases b4
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
  refine ⟨⟨t, nx, s1, et, enx, es1, eu⟩, Or.inl ?_⟩
  rcases hnum with rfl | rfl
  · exact rng_call
  · exact rng_send

variable [L : LawfulStore st]

set_option hygiene false in
/-- The common end of `vcpu_invocation_local_same'`'s reply arms: `after_invocation`
on `Ok`, then `finish`. -/
local macro "lvm_inv_fin" : tactic => `(tactic| (
  unfold syscall.after_invocation
  simp only [bind_ok, uncurry_apply_pair]
  rw [← localvm_finish_eq, efin]
  try simp only [bind_ok, uncurry_apply_pair]))

set_option maxHeartbeats 32000000 in
/-- `vcpu_invocation_local_same` with the number it ran for. -/
theorem vcpu_invocation_local_same' (hA : P0.ArchTotal ar) {T Cs Sg : Set U64} {s s' : S} {a a' : A}
    {number : I64} {slot : obj.Slot} {v : U64} {Ω Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hCn : ∀ t, sched.cur_thread st s = ok t → CnOff (L := L) T Cs Sg s t)
    (hL : ∀ t, sched.cur_thread st s = ok t → ∃ r : cspace.Resolved,
      cspace.lookup_slot st s t (L.mem s (regA t layout.reg.CAP)) = ok (core.result.Result.Ok r) ∧
      r.slot = slot ∧ obj.Slot.cap st slot s = ok (capability.Cap.Vcpu v))
    (h : localvm.handle_vcpu_invocation_local st ar s a number slot v = ok (true, s', a')) :
    (number = fl4_abi.syscall.SysCall ∨ number = fl4_abi.syscall.SysSend) ∧
      syscall.handle_syscall st ar s a number = ok (s', a') := by
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced T := h0.tcbs
  have hcC : L.cpu s ∈ Cs := h0.cur
  have hN : NodePlaced st T s (L.cpu s) := h0.nodes _ hcC
  have hcT : L.curW s ∈ T := h0.curT
  unfold localvm.handle_vcpu_invocation_local at h
  try simp only [lift, bind_ok] at h
  obtain ⟨t, et, h⟩ := bind_eq_ok h
  obtain ⟨cpu, -, h⟩ := bind_eq_ok h
  obtain ⟨info, ei, h⟩ := bind_eq_ok h
  rw [num_domains_ne_one_false] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨i, ei0, h⟩ := bind_eq_ok h
  by_cases c1 : (i &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true
  · rw [if_pos c1] at h; simp at h
  rw [if_neg c1] at h
  have hnum : number = fl4_abi.syscall.SysCall ∨ number = fl4_abi.syscall.SysSend := by
    by_cases cn : (number != fl4_abi.syscall.SysCall) = true
    · by_cases cs : (number != fl4_abi.syscall.SysSend) = true
      · rw [if_pos cn, if_pos cs] at h; simp at h
      · exact Or.inr (by simp only [bne_iff_ne, ne_eq, not_not] at cs; exact cs)
    · exact Or.inl (by simp only [bne_iff_ne, ne_eq, not_not] at cn; exact cn)
  rw [lvm_ite2 (lvm_num_nc hnum)] at h
  refine ⟨hnum, ?_⟩
  obtain ⟨b, -, h⟩ := bind_eq_ok h
  cases b
  · simp at h
  simp only [↓reduceIte] at h
  by_cases c3 : (info.extra_caps != 0#u64) = true
  · rw [if_pos c3] at h; simp at h
  rw [if_neg c3] at h
  have hx0 : info.extra_caps = 0#u64 := by simp only [bne_iff_ne, ne_eq, not_not] at c3; exact c3
  obtain ⟨i2, -, h⟩ := bind_eq_ok h
  by_cases c4 : i2 = 0#u64
  · rw [if_pos c4] at h; simp at h
  rw [if_neg c4] at h
  by_cases c5 : v = 0#u64
  · rw [if_pos c5] at h; simp at h
  rw [if_neg c5] at h
  obtain ⟨c, -, h⟩ := bind_eq_ok h
  obtain ⟨b1, -, h⟩ := bind_eq_ok h
  cases b1
  swap
  · simp at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨i3, -, h⟩ := bind_eq_ok h
  by_cases c6 : (i3 != t) = true
  · rw [if_pos c6] at h; simp at h
  rw [if_neg c6] at h
  obtain ⟨i4, -, h⟩ := bind_eq_ok h
  by_cases c7 : (i4 != v) = true
  · rw [if_pos c7] at h; simp at h
  rw [if_neg c7] at h
  obtain ⟨csc, ecsc, h⟩ := bind_eq_ok h
  obtain ⟨b2, -, h⟩ := bind_eq_ok h
  cases b2
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨i5, -, h⟩ := bind_eq_ok h
  by_cases c8 : (i5 != sched.TS_RUNNING) = true
  · rw [if_pos c8] at h; simp at h
  rw [if_neg c8] at h
  obtain ⟨b3, -, h⟩ := bind_eq_ok h
  cases b3
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨b4, -, h⟩ := bind_eq_ok h
  cases b4
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨⟨s2, a1⟩, epre, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨now, -, h⟩ := bind_eq_ok h
  obtain ⟨i6, ecns, h⟩ := bind_eq_ok h
  obtain ⟨b5, eb5, h⟩ := bind_eq_ok h
  cases b5
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨b6, -, h⟩ := bind_eq_ok h
  cases b6
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨buf, ebuf, h⟩ := bind_eq_ok h
  obtain ⟨rx, erx, h⟩ := bind_eq_ok h
  rcases rx with ex | ef
  swap
  · simp at h
  try dsimp only at h
  obtain ⟨len, elen, h⟩ := bind_eq_ok h
  obtain ⟨⟨r1, s3, a3⟩, edec, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨⟨s4, a4⟩, etail, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨⟨s5, a5⟩, efin, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  have e := ok_inj_ff h
  simp only [Prod.mk.injEq, true_and] at e
  obtain ⟨rfl, rfl⟩ := e
  -- the decode does not preempt
  have hnp := lvm_decode_np ar edec
  -- the prefix
  unfold localvm.syscall_prefix at epre
  try simp only [lift, bind_ok] at epre
  obtain ⟨nx, enx, epre⟩ := bind_eq_ok epre
  obtain ⟨s1, es1, eu⟩ := bind_eq_ok epre
  try rw [insn_len_eq] at es1
  have htT : t ∈ T := by rw [cur_thread_ok] at et; rw [← ok_inj_ff et]; exact hcT
  have ht' := hT t htT
  obtain ⟨et2, tK, oK⟩ := inv_prefix ar hT hN hcC et htT es1 eu hA
  obtain ⟨KF, hKF, hW⟩ := lt_prefix ar hT hN htT es1 eu hA
  -- the `FAULT_IP`-written state `s1`: the flags word is kept
  have hW1 := obj.Tcb.set_reg.wrK (L := L) s t layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) ht'
    (by simp [layout.reg.FAULT_IP])
  rw [es1, WP.spec_ok] at hW1
  obtain ⟨K1, hK1, e1⟩ := hW1
  have hK1' : K1.val = 392 := by rw [hK1]; simp [layout.reg.FAULT_IP]
  have aF : Aligned (core.num.U64.wrapping_add t K1) := field_aligned ht' (by omega) (by omega)
  have efl : obj.Tcb.flags st t s1 = ok i := by
    rw [flags_ok] at ei0 ⊢
    rw [e1]
    rw [mem_wr_ne' aF (field_aligned ht' (by simp) (by simp))
      (tcb_word_ne ht' ht' (by omega) (by simp) (fun _ => by simp; omega))]
    exact ei0
  -- `cur_sc` at the dispatch state
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
  have hcb := check_budget_restart_suf ar ecsc2 ecns eb5
  have hb : syscall.budget_ok st ar s1 a = ok (true, s2, a1) := by
    unfold syscall.budget_ok
    rw [eu]; simp only [bind_ok, uncurry_apply_pair]
    exact hcb
  -- the reads of `handle_invocation` at the dispatch state
  have ei2' : msg.msg_info st s2 t = ok info := by
    unfold msg.msg_info at ei ⊢
    rw [reg_keepK ht' (r := layout.reg.MSG_INFO) (by simp) (by simp) tK]; exact ei
  have ecap2 : obj.Tcb.reg st t s2 layout.reg.CAP = ok (L.mem s (regA t layout.reg.CAP)) := by
    rw [reg_keepK ht' (r := layout.reg.CAP) (by simp) (by simp) tK, reg_ok]
  obtain ⟨r, er0, hrs, ec⟩ := hL t et
  have er2 := lookup_slot_keep ht' (hCn t et) tK oK er0
  have ecr2 : obj.Slot.cap st r.slot s2 = ok (capability.Cap.Vcpu v) := by
    rw [found_cap_keep (hCn t et) oK er0, hrs]; exact ec
  have nRRc : ¬ fl4_abi.syscall.SysCall = fl4_abi.syscall.SysReplyRecv := by
    unfold fl4_abi.syscall.SysCall fl4_abi.syscall.SysReplyRecv; decide
  have nRRs : ¬ fl4_abi.syscall.SysSend = fl4_abi.syscall.SysReplyRecv := by
    unfold fl4_abi.syscall.SysSend fl4_abi.syscall.SysReplyRecv; decide
  have n15 : ¬ fl4_abi.syscall.SysCall = fl4_abi.syscall.SysSend := by
    unfold fl4_abi.syscall.SysCall fl4_abi.syscall.SysSend; decide
  have n16 : ¬ fl4_abi.syscall.SysCall = fl4_abi.syscall.SysNBSend := by
    unfold fl4_abi.syscall.SysCall fl4_abi.syscall.SysNBSend; decide
  have nSC : ¬ fl4_abi.syscall.SysSend = fl4_abi.syscall.SysCall := fun e => n15 e.symm
  rcases hnum with rfl | rfl
  -- the call flag the local entry passed
  all_goals first
    | rw [show decide (fl4_abi.syscall.SysCall = fl4_abi.syscall.SysCall) = true from decide_eq_true rfl] at edec
    | rw [show decide (fl4_abi.syscall.SysSend = fl4_abi.syscall.SysCall) = false from decide_eq_false nSC] at edec
  all_goals
    -- the general run
    unfold syscall.handle_syscall syscall.syscall
    rw [et]; simp only [bind_ok]
    rw [enx]; simp only [lift, bind_ok]
    rw [es1]; simp only [bind_ok]
    rw [efl]
    simp only [lift, bind_ok, if_neg c1, rng_call.1, rng_call.2, rng_send.1, rng_send.2, ↓reduceIte, if_false]
    rw [hb]
    simp only [bind_ok, uncurry_apply_pair, ↓reduceIte, if_true, eq_self_iff_true, nRRc, nRRs, if_false]
    unfold syscall.dispatch_syscall
    rw [et2]; simp only [bind_ok]
    rw [ecap2]; simp only [bind_ok]
    rw [reg_ok]; simp only [bind_ok]
    simp only [n15, n16, nSC, ↓reduceIte, if_true, if_false, eq_self_iff_true]
    unfold syscall.handle_invocation
    rw [et2]; simp only [bind_ok]
    rw [ei2']; simp only [bind_ok]
    rw [er2]; simp only [bind_ok]
    rw [ecr2]; simp only [bind_ok]
    rw [ebuf]; simp only [bind_ok]
    rw [erx]; simp only [bind_ok]
    rw [elen]; simp only [bind_ok]
    unfold syscall.decode_invocation
    rw [et2]; simp only [bind_ok]
    rw [edec]; simp only [bind_ok, uncurry_apply_pair]
    -- the reply arms
    rcases r1 with _ | (f | l | e2 | _)
    · -- `Ok`
      obtain ⟨i7, ei7, etail⟩ := bind_eq_ok etail
      rw [ei7]; simp only [bind_ok]
      by_cases cR : i7 = sched.TS_RESTART
      · rw [if_pos cR] at etail ⊢
        try simp only [nSC, ↓reduceIte, if_true, if_false, eq_self_iff_true, bind_ok, Bool.false_eq_true]
          at etail ⊢
        repeat (obtain ⟨x, ex', etail⟩ := bind_eq_ok etail; rw [ex']; simp only [bind_ok])
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (ok_inj_ff etail)
        simp only [bind_ok, uncurry_apply_pair]
        lvm_inv_fin
      · rw [if_neg cR] at etail ⊢
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (ok_inj_ff etail)
        simp only [bind_ok, uncurry_apply_pair]
        lvm_inv_fin
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (ok_inj_ff etail)
      simp only [bind_ok, uncurry_apply_pair]
      lvm_inv_fin
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (ok_inj_ff etail)
      simp only [bind_ok, uncurry_apply_pair]
      lvm_inv_fin
    · try simp only [nSC, ↓reduceIte, if_true, if_false, eq_self_iff_true, bind_ok, Bool.false_eq_true]
        at etail ⊢
      repeat (obtain ⟨x, ex', etail⟩ := bind_eq_ok etail; rw [ex']; simp only [bind_ok])
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (ok_inj_ff etail)
      simp only [bind_ok, uncurry_apply_pair]
      lvm_inv_fin
    · exact absurd rfl hnp

/-- **`vcpu_invocation_local_same`: a VCPU state invocation beside the serial
gate, where it ran, is the general entry** `syscall.handle_syscall … number`
(module docstring). `hL` [J]: fl4-sync's contract (`lookup_slot_locked` found
`slot`, holding `Vcpu v`, with the general lookup's walk). -/
theorem vcpu_invocation_local_same (hA : P0.ArchTotal ar) {T Cs Sg : Set U64} {s s' : S} {a a' : A}
    {number : I64} {slot : obj.Slot} {v : U64} {Ω Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hCn : ∀ t, sched.cur_thread st s = ok t → CnOff (L := L) T Cs Sg s t)
    (hL : ∀ t, sched.cur_thread st s = ok t → ∃ r : cspace.Resolved,
      cspace.lookup_slot st s t (L.mem s (regA t layout.reg.CAP)) = ok (core.result.Result.Ok r) ∧
      r.slot = slot ∧ obj.Slot.cap st slot s = ok (capability.Cap.Vcpu v))
    (h : localvm.handle_vcpu_invocation_local st ar s a number slot v = ok (true, s', a')) :
    syscall.handle_syscall st ar s a number = ok (s', a') :=
  (vcpu_invocation_local_same' ar hA hI hCn hL h).2

/-- **The VCPU state invocation local entry where it ran: the general entry's
postconditions** (on the `true` results). -/
theorem vcpu_invocation_local_triple (hA : P0.ArchTotal ar) {T Cs Sg : Set U64} {s : S} {a : A}
    {number : I64} {slot : obj.Slot} {v : U64} {Ω Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
    {P : S × A → Prop}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hCn : ∀ t, sched.cur_thread st s = ok t → CnOff (L := L) T Cs Sg s t)
    (hL : ∀ t, sched.cur_thread st s = ok t → ∃ r : cspace.Resolved,
      cspace.lookup_slot st s t (L.mem s (regA t layout.reg.CAP)) = ok (core.result.Result.Ok r) ∧
      r.slot = slot ∧ obj.Slot.cap st slot s = ok (capability.Cap.Vcpu v))
    (hG : syscall.handle_syscall st ar s a number ⦃ P ⦄) :
    localvm.handle_vcpu_invocation_local st ar s a number slot v ⦃ r => r.1 = true → P (r.2.1, r.2.2) ⦄ := by
  obtain ⟨⟨b, s', a'⟩, e, -⟩ :=
    spec_ex_fd (P0.localvm.handle_vcpu_invocation_local.p0 st ar s a number slot v L.total hA)
  rw [e, WP.spec_ok]
  intro hb
  simp only at hb
  subst hb
  have hs := vcpu_invocation_local_same ar hA hI hCn hL e
  rw [hs, WP.spec_ok] at hG
  exact hG

/-- **The P1 invariant of the VCPU state invocation local entry, from the P1
top's form**: whatever the top proves for every native entry
(`∀ number ≠ SysVMEnter, handle_syscall … ⦃ s' _ => Q s' ⦄`, e.g. `EntryInv`
over some admissible tuple: the first conjunct of `kernel_entry.entry_of*`,
P3's `kernel_entry_entryInvU29`), the accepted local runs satisfy. The local
entry runs only for `SysCall` / `SysSend`. -/
theorem vcpu_invocation_local_entry (hA : P0.ArchTotal ar) {T Cs Sg : Set U64} {s : S} {a : A}
    {number : I64} {slot : obj.Slot} {v : U64} {Ω Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
    {Q : S → Prop}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hCn : ∀ t, sched.cur_thread st s = ok t → CnOff (L := L) T Cs Sg s t)
    (hL : ∀ t, sched.cur_thread st s = ok t → ∃ r : cspace.Resolved,
      cspace.lookup_slot st s t (L.mem s (regA t layout.reg.CAP)) = ok (core.result.Result.Ok r) ∧
      r.slot = slot ∧ obj.Slot.cap st slot s = ok (capability.Cap.Vcpu v))
    (hTop : ∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter →
      syscall.handle_syscall st ar s a number ⦃ s' _ => Q s' ⦄) :
    localvm.handle_vcpu_invocation_local st ar s a number slot v ⦃ r => r.1 = true → Q r.2.1 ⦄ := by
  obtain ⟨⟨b, s', a'⟩, e, -⟩ :=
    spec_ex_fd (P0.localvm.handle_vcpu_invocation_local.p0 st ar s a number slot v L.total hA)
  rw [e, WP.spec_ok]
  intro hb
  simp only at hb
  subst hb
  obtain ⟨hnum, hs⟩ := vcpu_invocation_local_same' ar hA hI hCn hL e
  have hne : number ≠ fl4_abi.syscall.SysVMEnter := by
    rcases hnum with rfl | rfl
    · unfold fl4_abi.syscall.SysCall fl4_abi.syscall.SysVMEnter; decide
    · unfold fl4_abi.syscall.SysSend fl4_abi.syscall.SysVMEnter; decide
  have hG := hTop number hne
  rw [hs, WP.spec_ok] at hG
  exact hG

end

end Fl4Proofs.P1
