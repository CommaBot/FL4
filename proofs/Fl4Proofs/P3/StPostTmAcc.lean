/-
P3 (line stpost, generation 6): **an accepted `TCB_SetTimer` run's dispatch-state facts**
(`P1.set_timer_local_acc`; split from StPostTmTop, whose module docstring describes the route).

An accepted `localtimer.handle_set_timer_local … n target` has number `SysCall`, and at the general
entry's dispatch state (after its `FAULT_IP` write and passing `budget_ok`) the current thread is
unchanged, the `CAP` lookup finds fl4-sync's `Thread target` slot (`hL`, carried by
`lookup_slot_keep` / `found_cap_keep`), the message info's label is `TCBSetTimer` (the message-info
register survives the prefix: `reg_keepK`), and `remote_tcb_stall` of the target stalls nothing
(`stall_none`). `set_timer_local_same`'s walk, stopped at the budget check. No premise added.
-/
import Fl4Proofs.P1.LocalTimer
import Fl4Proofs.P1.FastIoLocal
import Fl4Proofs.P1.FastSysLocal
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {A : Type _} {st : machine.Store S} (ar : machine.Arch A) [L : LawfulStore st]

set_option maxHeartbeats 16000000 in
/-- (stpost) **An accepted `TCB_SetTimer` run beside the gate: its number, and the cap, label and
target affinity at its dispatch state** (module docstring; `set_timer_local_same`'s walk). -/
theorem set_timer_local_acc (hA : P0.ArchTotal ar) {T Cs Sg : Set U64} {s s' : S} {a a' : A} {n : I64}
    {target : U64} {Ω Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hCn : ∀ t, sched.cur_thread st s = ok t → CnOff (L := L) T Cs Sg s t)
    (hL : ∀ t, sched.cur_thread st s = ok t → ∃ r : cspace.Resolved,
      cspace.lookup_slot st s t (L.mem s (regA t layout.reg.CAP)) = ok (core.result.Result.Ok r) ∧
      obj.Slot.cap st r.slot s = ok (capability.Cap.Thread target))
    (htg : target ∈ T)
    (h : localtimer.handle_set_timer_local st ar s a n target = ok (true, s', a')) :
    n = fl4_abi.syscall.SysCall ∧
    ∀ ct nx s2 a2, sched.cur_thread st s = ok ct → obj.Tcb.reg st ct s layout.reg.NEXT_IP = ok nx →
      syscall.budget_ok st ar (L.wr s (regA ct layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx 2#u64)) a =
        ok (true, s2, a2) →
      sched.cur_thread st s2 = ok ct ∧ ∃ found : cspace.Resolved,
        cspace.lookup_slot st s2 ct (L.mem s2 (regA ct layout.reg.CAP)) = ok (.Ok found) ∧
        obj.Slot.cap st found.slot s2 = ok (.Thread target) ∧
        (∀ info, msg.msg_info st s2 ct = ok info → info.label = fl4_abi.label.TCBSetTimer) ∧
        smp.remote_tcb_stall st ar s2 a2 target = ok (s2, a2) := by
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced T := h0.tcbs
  have hcC : L.cpu s ∈ Cs := h0.cur
  have hN : NodePlaced st T s (L.cpu s) := h0.nodes _ hcC
  have hcT : L.curW s ∈ T := h0.curT
  unfold localtimer.handle_set_timer_local at h
  try simp only [lift, bind_ok] at h
  obtain ⟨t, et, h⟩ := bind_eq_ok h
  obtain ⟨cpu, ecpu, h⟩ := bind_eq_ok h
  rw [L.cur_cpu_eq] at ecpu
  have hcpu : cpu = L.cpu s := (ok_inj_ff ecpu).symm
  subst hcpu
  obtain ⟨info, ei, h⟩ := bind_eq_ok h
  rw [num_domains_ne_one_false] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  by_cases cn : (n != fl4_abi.syscall.SysCall) = true
  · rw [if_pos cn] at h; simp at h
  rw [if_neg cn] at h
  have hn : n = fl4_abi.syscall.SysCall := by simp only [bne_iff_ne, ne_eq, not_not] at cn; exact cn
  refine ⟨hn, fun ct nx0 s2g a2g hct hnx hb2 => ?_⟩
  obtain ⟨i, -, h⟩ := bind_eq_ok h
  by_cases c1 : (i &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true
  · rw [if_pos c1] at h; simp at h
  rw [if_neg c1] at h
  by_cases c2 : (info.label != fl4_abi.label.TCBSetTimer) = true
  · rw [if_pos c2] at h; simp at h
  rw [if_neg c2] at h
  have hlbl : info.label = fl4_abi.label.TCBSetTimer := by
    simp only [bne_iff_ne, ne_eq, not_not] at c2; exact c2
  by_cases c3 : (info.extra_caps != 0#u64) = true
  · rw [if_pos c3] at h; simp at h
  rw [if_neg c3] at h
  by_cases c4 : info.length < 2#u64
  · rw [if_pos c4] at h; simp at h
  rw [if_neg c4] at h
  obtain ⟨csc, ecsc, h⟩ := bind_eq_ok h
  obtain ⟨b, eb, h⟩ := bind_eq_ok h
  cases b
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨b1, -, h⟩ := bind_eq_ok h
  cases b1
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨i2, ei2, h⟩ := bind_eq_ok h
  by_cases c5 : (i2 != sched.TS_RUNNING) = true
  · rw [if_pos c5] at h; simp at h
  rw [if_neg c5] at h
  obtain ⟨b2, -, h⟩ := bind_eq_ok h
  cases b2
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨b3, -, h⟩ := bind_eq_ok h
  cases b3
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨nx, enx, h⟩ := bind_eq_ok h
  obtain ⟨s1, es1, h⟩ := bind_eq_ok h
  try rw [insn_len_eq] at es1
  obtain ⟨⟨s2, a1⟩, eu, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨now, -, h⟩ := bind_eq_ok h
  obtain ⟨dl, edl, h⟩ := bind_eq_ok h
  obtain ⟨bd, ebd, h⟩ := bind_eq_ok h
  obtain ⟨cns, ecns, h⟩ := bind_eq_ok h
  obtain ⟨b4, eb4, h⟩ := bind_eq_ok h
  cases b4
  · simp at h
  -- the prefix
  have htT : t ∈ T := by
    rw [cur_thread_ok] at et; rw [← ok_inj_ff et]; exact hcT
  have ht' := hT t htT
  obtain ⟨et2, tK, oK⟩ := inv_prefix ar hT hN hcC et htT es1 eu hA
  obtain ⟨KF, hKF, hW⟩ := lt_prefix ar hT hN htT es1 eu hA
  have uK : ∀ {u K : U64}, u ∈ T → K.val < 4096 → K.val % 8 = 0 → (u = t → K.val ≠ 392) →
      L.mem s2 (core.num.U64.wrapping_add u K) = L.mem s (core.num.U64.wrapping_add u K) :=
    fun huT hK h8 hne => lt_tcbK hKF hT hN htT hW huT hK h8 hne
  -- cur_sc at the dispatch state
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
  have hb : syscall.budget_ok st ar s1 a = ok (true, s2, a1) := by
    unfold syscall.budget_ok
    rw [eu]; simp only [bind_ok, uncurry_apply_pair]
    exact check_budget_restart_suf ar ecsc2 ecns eb4
  -- the general prefix is this one
  have e1 : ct = t := ok_inj_ff (hct.symm.trans et)
  subst e1
  have e2 : nx0 = nx := ok_inj_ff (hnx.symm.trans enx)
  subst e2
  have hs1 := set_fip_wr ht' es1
  rw [← hs1, hb] at hb2
  have e3 := ok_inj_ff hb2
  simp only [Prod.mk.injEq] at e3
  obtain ⟨-, rfl, rfl⟩ := e3
  -- the reads of `handle_invocation` at the dispatch state
  have ei2' : msg.msg_info st s2 ct = ok info := by
    unfold msg.msg_info at ei ⊢
    rw [reg_keepK ht' (r := layout.reg.MSG_INFO) (by simp) (by simp) tK]; exact ei
  have ecap2 : obj.Tcb.reg st ct s2 layout.reg.CAP = ok (L.mem s (regA ct layout.reg.CAP)) := by
    rw [reg_keepK ht' (r := layout.reg.CAP) (by simp) (by simp) tK, reg_ok]
  rw [reg_ok] at ecap2
  have ecap2' := ok_inj_ff ecap2
  obtain ⟨r, er, ecr⟩ := hL ct et
  have er2 := lookup_slot_keep ht' (hCn ct et) tK oK er
  have ecr2 : obj.Slot.cap st r.slot s2 = ok (capability.Cap.Thread target) := by
    rw [found_cap_keep (hCn ct et) oK er]; exact ecr
  -- the stall: `target` is this core's
  have haff : L.mem s (affA target) = L.cpu s := by
    unfold localtimer.set_timer_target_ok at eb
    obtain ⟨ia, eia, eb⟩ := bind_eq_ok eb
    by_cases ca : (ia != L.cpu s) = true
    · rw [if_pos ca] at eb; simp at eb
    · simp only [bne_iff_ne, ne_eq, not_not] at ca
      rw [aff_ok] at eia; rw [ok_inj_ff eia]; exact ca
  have haff2 : L.mem s2 (affA target) = L.cpu s2 := by
    rw [hW.2.1]
    have e : affA target = core.num.U64.wrapping_add target 3520#u64 := rfl
    rw [e, uK htg (by simp) (by simp) (fun _ => by simp), ← e, haff]
  refine ⟨et2, r, ?_, ecr2, fun info' hi => ?_, stall_none (st := st) (L := L) ar _ _ target haff2⟩
  · rw [ecap2']; exact er2
  · rw [ei2'] at hi; rw [← ok_inj_ff hi]; exact hlbl

end

end Fl4Proofs.P1
