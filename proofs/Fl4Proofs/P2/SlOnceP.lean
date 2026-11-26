/-
# P2 (line slhuf, gen 7): `Once` through the syscall entry's prefix

`sl_pre_once`: the tree `R.syscall.handle_syscall_local n (rp, ep)` from a state `x` makes no racy read up to
an arm (current thread, flags, `NEXT_IP`, the `FAULT_IP` write, `update_timestamp`, `cur_sc`, `consumed`,
`sufficient`), given the prefix's words on a guard `R0` / `W0` without user words (`PreDec`, as
`sl_pre_dec`), and reduces `Once` to `Once` of the arm the flags choose (`fastpath.fault` on a trapping
thread, `fastpath.reply_recv_found` otherwise) at the prefix state, for any written-word set and the empty
touched set.

No premises.
-/
import Fl4Proofs.P2.SlOnceN
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap Fl4Proofs.P0.Consts
open Fl4Proofs.P2.E2E (Once)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} {ar : machine.Arch A} {Rd User : U64 → Prop}

set_option hygiene false in
/-- The prefix walk of `sl_pre_once` (both arms). -/
local macro "sl_pre_walk" : tactic => `(tactic| (
    -- NEXT_IP
    refine once_gstep (W0 := W0) hR0 hW0 (R.obj.Tcb.reg_nz _ _) h (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
    · rw [R.obj.Tcb.reg_eq] at h1 ⊢
      rw [obj.Tcb.reg.guard (gS := PathObl.guard st R0 W0) _ x _ hp.nx]
      exact h1
    replace h := hk
    rw [R.obj.Tcb.reg_eq] at h1
    obtain ⟨nx, enx, rfl⟩ := bind_shape h1
    dsimp only at h ⊢
    -- FAULT_IP
    refine once_gstep (W0 := W0) hR0 hW0 (R.obj.Tcb.set_reg_nz _ _ _) h (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
    · rw [R.obj.Tcb.set_reg_eq] at h1 ⊢
      rw [obj.Tcb.set_reg.guard (gS := PathObl.guard st R0 W0) _ x _ _ hp.fi]
      exact h1
    replace h := hk
    rw [R.obj.Tcb.set_reg_eq] at h1
    obtain ⟨s1, es1, rfl⟩ := bind_shape h1
    dsimp only at h ⊢
    have e1 := set_fip_wr ht' es1
    have hk1 : L.ksb s1 = L.ksb x := by rw [e1, L.ksb_wr]
    have hc1 : L.cpu s1 = L.cpu x := by rw [e1, LawfulStore.cpu_wr]
    have n1 : ∀ o, L.nodeAt s1 (L.cpu s1) o = L.nodeAt x (L.cpu x) o := fun o => by rw [hc1, nodeAt_of_ksb hk1]
    -- update_timestamp
    refine once_gstep (W0 := W0) hR0 hW0 R.sched.update_timestamp_nz h (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
    · rw [R.sched.update_timestamp_eq] at h1 ⊢
      have rct : R0 (ctA (L := L) s1) := by
        show R0 (L.nodeAt s1 (L.cpu s1) layout.node.CUR_TIME)
        rw [n1]; exact hp.nd _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
      have rcn : R0 (cnA (L := L) s1) := by
        show R0 (L.nodeAt s1 (L.cpu s1) layout.node.CONSUMED)
        rw [n1]; exact hp.nd _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
      have wct : W0 (ctA (L := L) s1) := by
        show W0 (L.nodeAt s1 (L.cpu s1) layout.node.CUR_TIME)
        rw [n1]; exact hp.ct
      have wcn : W0 (cnA (L := L) s1) := by
        show W0 (L.nodeAt s1 (L.cpu s1) layout.node.CONSUMED)
        rw [n1]; exact hp.cn
      rw [sched.update_timestamp.guard (gS := PathObl.guard st R0 W0) ar s1 a rct wct rcn wcn]
      exact h1
    replace h := hk
    rw [R.sched.update_timestamp_eq] at h1
    obtain ⟨⟨X, a1⟩, eu, rfl⟩ := bind_shape h1
    dsimp only at h ⊢
    have LP : LocalPre (st := st) ar x a (X, a1) := ⟨_, nx, s1, cur_thread_ok x, enx, es1, eu⟩
    obtain ⟨hk2, hc2, -⟩ := sl_pre_agree (Cs := ∅) ar hA hT hN hcT LP
    have nd2 : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R0 (L.nodeAt X (L.cpu X) o) := fun o h1 h2 => by
      rw [hc2, nodeAt_of_ksb hk2]; exact hp.nd o h1 h2
    -- cur_sc
    refine once_gstep (W0 := W0) hR0 hW0 R.sched.cur_sc_nz h (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
    · rw [R.sched.cur_sc_eq] at h1 ⊢
      rw [sched.cur_sc.guard (gS := PathObl.guard st R0 W0) X (nd2 _ (by simp [layout.node.CUR_SC])
        (by simp [layout.node.CUR_SC]))]
      exact h1
    replace h := hk
    rw [R.sched.cur_sc_eq] at h1
    obtain ⟨csc, ecsc, rfl⟩ := bind_shape h1
    dsimp only at h ⊢
    -- consumed
    refine once_gstep (W0 := W0) hR0 hW0 R.sched.consumed_nz h (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
    · rw [R.sched.consumed_eq] at h1 ⊢
      rw [sched.consumed.guard (gS := PathObl.guard st R0 W0) X (nd2 _ (by simp [layout.node.CONSUMED])
        (by simp [layout.node.CONSUMED]))]
      exact h1
    replace h := hk
    rw [R.sched.consumed_eq] at h1
    obtain ⟨i3, -, rfl⟩ := bind_shape h1
    dsimp only at h ⊢
    -- sufficient
    refine once_gstep (W0 := W0) hR0 hW0 (R.sporadic.sufficient_nz _ _) h (fun r h1 => ?_)
      (fun r h1 hk Wd _ => ?_)
    · rw [R.sporadic.sufficient_eq] at h1 ⊢
      rw [sporadic.sufficient.guard (gS := PathObl.guard st R0 W0) ar X a1 csc i3 (hhd X a1 csc LP ecsc)]
      exact h1
    replace h := hk
    rw [R.sporadic.sufficient_eq] at h1
    obtain ⟨b, -, rfl⟩ := bind_shape h1
    dsimp only at h ⊢
    by_cases hb : b = true
    swap
    · rw [if_neg hb]; simp only [Once]
    rw [if_pos hb] at h ⊢
    first
      | (rw [if_pos hi1] at h ⊢; exact hfa (htr hi1) X a1 _ _ LP h Wd)
      | (rw [if_neg hi1] at h ⊢; exact hra (hntr hi1) X a1 _ LP h Wd)
))

set_option maxHeartbeats 4000000 in
/-- **`Once` through the syscall entry's prefix** (module docstring). -/
theorem sl_pre_once {R0 W0 : U64 → Prop} (hR0 : ∀ q, R0 q → Rd q ∧ ¬ User q) (hW0 : ∀ q, W0 q → ¬ User q)
    (hA : P0.ArchTotal ar) {T : Set U64} {x : S} {a : A} {n : I64} {rp ep : U64}
    (hT : TcbPlaced T) (hN : NodePlaced st T x (L.cpu x)) (hcT : L.curW x ∈ T)
    (hp : PreDec (L := L) R0 W0 x)
    (hhd : ∀ X a1 csc, LocalPre (st := st) ar x a (X, a1) → sched.cur_sc st X = ok csc →
      RdHead (L := L) R0 X csc)
    {r' : Bool × S × A} (h : interp st ar (R.syscall.handle_syscall_local n (rp, ep)) x a = ok r')
    (hfa : SlTrap st x → ∀ X a1 a2 n', LocalPre (st := st) ar x a (X, a1) →
      interp st ar (R.fastpath.fault (L.curW x) n') X a2 = ok r' →
      ∀ Wd, Once st ar Rd User Wd ∅ (R.fastpath.fault (L.curW x) n') X a2)
    (hra : ¬ SlTrap st x → ∀ X a1 a2, LocalPre (st := st) ar x a (X, a1) →
      interp st ar (R.fastpath.reply_recv_found (L.curW x) rp ep) X a2 = ok r' →
      ∀ Wd, Once st ar Rd User Wd ∅ (R.fastpath.reply_recv_found (L.curW x) rp ep) X a2) :
    Once st ar Rd User ∅ ∅ (R.syscall.handle_syscall_local n (rp, ep)) x a := by
  have ht' := hT _ hcT
  unfold R.syscall.handle_syscall_local at h ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc] at h ⊢
  -- cur_thread
  refine once_gstep (W0 := W0) hR0 hW0 R.sched.cur_thread_nz h (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
  · rw [R.sched.cur_thread_eq] at h1 ⊢
    rw [sched.cur_thread.guard (gS := PathObl.guard st R0 W0) x
      (hp.nd _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD]))]
    exact h1
  replace h := hk
  rw [R.sched.cur_thread_eq] at h1
  obtain ⟨t, et, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  rw [cur_thread_ok] at et
  have et' : t = L.curW x := (ok_inj_ff et).symm
  subst et'
  -- flags
  refine once_gstep (W0 := W0) hR0 hW0 (R.obj.Tcb.flags_nz _) h (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
  · rw [R.obj.Tcb.flags_eq] at h1 ⊢
    rw [obj.Tcb.flags.guard (gS := PathObl.guard st R0 W0) _ x hp.fl]
    exact h1
  replace h := hk
  rw [R.obj.Tcb.flags_eq] at h1
  obtain ⟨i, ei, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  simp only [SProg.sbind] at h ⊢
  have htr : ((i &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) != 0#u64) = true → SlTrap st x :=
    fun h' => ⟨i, ei, h'⟩
  have hntr : ¬ ((i &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) != 0#u64) = true → ¬ SlTrap st x :=
    fun h' ⟨f, ef, hf'⟩ => h' (by rw [ok_inj_ff (ei.symm.trans ef)]; exact hf')
  by_cases hd : (layout.NUM_DOMAINS != 1#u64) = true
  · rw [if_pos hd]; simp only [Once]
  rw [if_neg hd] at h ⊢
  by_cases hi1 : ((i &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) != 0#u64) = true
  · rw [if_pos hi1] at h ⊢
    sl_pre_walk
  · rw [if_neg hi1] at h ⊢
    by_cases hnum : (n != fl4_abi.syscall.SysReplyRecv) = true
    · rw [if_pos hnum]; simp only [Once]
    rw [if_neg hnum] at h ⊢
    sl_pre_walk

end

end Fl4Proofs.P2.PathObl
