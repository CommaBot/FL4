/-
# P2 (line pte, generation 16): `Once` of an accepted PageMap run at its entry (`roA`, fourth part)

**`pm_entOnce`**: the walk of `R.invBodyPmG` from a `PmPreG` entry of an accepted run, for the read set `PmRSU s`
and the user words `K.user` — invj's / slhuf's `invU_entOnce` (P2/InvURoTr.lean, its script copied) at the layout
`ptU K` (every prefix read is an `IoRS (ptU K) s` word, so a `PmRSU s` word off `K.user`: `pmRSU_ioRS`), the
seen and slot words by gen 12's `pm_seen` / `pm_slotRS`, and the decode onward by `pm_decOnce`
(P2/InvPmRoC.lean). The prefix of `R.invBodyPmG` / `R.invTailPmG` is `R.invBodyG` / `R.invTailG`'s.

No named premise. New module; no existing statement changes.
-/
import Fl4Proofs.P2.InvPmRoC
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField NullOrFrame TcbSlot)
open Fl4Proofs.P2.E2E (Once ReadOnce)

noncomputable section

section walk
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayoutP} {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}
variable {A : Type} {ar : machine.Arch A}

/-- **`Once` of an accepted PageMap run at its entry** (module docstring). -/
theorem pm_entOnce (hA : P0.ArchTotal ar) {number : I64} {p : localinv.Plan} {μ : U64 → U64} :
    ∀ s (a : A) r, PmPreG st Cs Ω Sg Ac Locks p K μ s →
      (∃ s1 a1, syscall.handle_invocation_local st ar s a number p = ok (true, s1, a1)) →
      interp st ar (R.invBodyPmG number p) s a = ok r →
      Once st ar (PmRSU st K Locks s) (· ∈ K.user) ∅ ∅ (R.invBodyPmG number p) s a := by
  intro s a r hE hac h
  obtain ⟨sA, aA, h0⟩ := hac
  have hG := hE.1.2.2
  have hJ := hE.1.1
  have hq := hE.1.2.1
  have P := hq.1.1.1.ptU hG
  have hR0 : ∀ q, IoRS (st := st) K.ptU Locks s q → PmRSU st K Locks s q ∧ q ∉ K.user :=
    fun q hq => ⟨pmRSU_ioRS hG hq, fun hu => hq.2.1 (Or.inl hu)⟩
  have hW0 : ∀ q, IoRS (st := st) K.ptU Locks s q → q ∉ K.user := fun q hq hu => hq.2.1 (Or.inl hu)
  obtain ⟨-, -, -, -, -, -, hsl, -, -, -⟩ := pm_core hq
  obtain ⟨-, hf⟩ := P.lay.slot8 _ hsl
  have r0 : IoRS (st := st) K.ptU Locks s p.slot := by
    have := pm_slotRS hJ hq P (o := 0#u64) (by simp) (by simp)
    rwa [wadd_zero hf] at this
  have r8 := pm_slotRS hJ hq P (o := 8#u64) (by simp) (by simp)
  have nC := (P.nd (Locks := Locks) layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD])
    (by simp [layout.node.CUR_THREAD])).1
  unfold R.invBodyPmG at h ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- the current thread
  refine once_gstep hR0 hW0 (R.sched.cur_thread_nz) h (fun r h1 => ?_) (fun r h1 hk Wd1 _ => ?_)
  · rw [R.sched.cur_thread_eq] at h1 ⊢
    rw [sched.cur_thread.guard (gS := PathObl.guard st (IoRS (st := st) K.ptU Locks s) (IoRS (st := st) K.ptU Locks s)) s nC]
    exact h1
  replace h := hk
  rw [R.sched.cur_thread_eq] at h1
  obtain ⟨t, et, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  rw [cur_thread_ok] at et
  have et' : t = L.curW s := (ok_inj_ff et).symm
  subst et'
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `MSG_INFO`
  refine once_gstep hR0 hW0 (R.msg.msg_info_nz _) h (fun r h1 => ?_) (fun r h1 hk Wd2 _ => ?_)
  · rw [R.msg.msg_info_eq] at h1 ⊢
    rw [msg.msg_info.guard (gS := PathObl.guard st (IoRS (st := st) K.ptU Locks s) (IoRS (st := st) K.ptU Locks s)) s _
      (P.reg (Locks := Locks) (by simp [layout.reg.MSG_INFO])).1]
    exact h1
  replace h := hk
  rw [R.msg.msg_info_eq] at h1
  obtain ⟨info, emi, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  refine once_ite0 h (fun _ _ => by simp only [Once]) (fun _ h => ?_)
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- the flags
  refine once_gstep hR0 hW0 (R.obj.Tcb.flags_nz _) h (fun r h1 => ?_) (fun r h1 hk Wd3 _ => ?_)
  · rw [R.obj.Tcb.flags_eq] at h1 ⊢
    rw [obj.Tcb.flags.guard (gS := PathObl.guard st (IoRS (st := st) K.ptU Locks s) (IoRS (st := st) K.ptU Locks s)) _ s
      (P.home (Locks := Locks) (off := 3456#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField])).1]
    exact h1
  replace h := hk
  rw [R.obj.Tcb.flags_eq] at h1
  obtain ⟨i, -, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine once_ite0 h (fun _ _ => by simp only [Once]) (fun _ h => ?_)
  refine once_ite0 h (fun _ _ => by simp only [Once]) (fun _ h => ?_)
  -- the tail
  unfold R.invTailPmG at h ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine once_liftR h (fun b _ h => ?_)
  cases b
  · rw [if_neg Bool.false_ne_true]; simp only [Once]
  rw [if_pos rfl] at h ⊢
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `NEXT_IP`
  refine once_gstep hR0 hW0 (R.obj.Tcb.reg_nz _ _) h (fun r h1 => ?_) (fun r h1 hk Wd4 _ => ?_)
  · rw [R.obj.Tcb.reg_eq] at h1 ⊢
    rw [obj.Tcb.reg.guard (gS := PathObl.guard st (IoRS (st := st) K.ptU Locks s) (IoRS (st := st) K.ptU Locks s)) _ s _
      (P.reg (Locks := Locks) (by simp [layout.reg.NEXT_IP])).1]
    exact h1
  replace h := hk
  rw [R.obj.Tcb.reg_eq] at h1
  obtain ⟨nx, enx, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- the `FAULT_IP` write
  refine once_gstep hR0 hW0 (R.obj.Tcb.set_reg_nz _ _ _) h (fun r h1 => ?_) (fun r h1 hk Wd5 _ => ?_)
  · rw [R.obj.Tcb.set_reg_eq] at h1 ⊢
    rw [obj.Tcb.set_reg.guard (gS := PathObl.guard st (IoRS (st := st) K.ptU Locks s) (IoRS (st := st) K.ptU Locks s)) _ s
      _ _ (P.reg (Locks := Locks) (by simp [layout.reg.FAULT_IP])).1]
    exact h1
  replace h := hk
  rw [R.obj.Tcb.set_reg_eq] at h1
  obtain ⟨x1, es1, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  have ex1 : x1 = L.wr s (regA (L.curW s) layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx 2#u64) := by
    rw [set_reg_ok'] at es1; exact (ok_inj_ff es1).symm
  have hNx1 : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      IoRS (st := st) K.ptU Locks s (L.nodeAt x1 (L.cpu x1) o) := fun o h1 h2 => by
    rw [ex1, LawfulStore.cpu_wr, nodeAt_of_ksb (L.ksb_wr _ _ _)]; exact (P.nd (Locks := Locks) o h1 h2).1
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `update_timestamp`
  have hct : IoRS (st := st) K.ptU Locks s (ctA (L := L) x1) := by
    show IoRS (st := st) K.ptU Locks s (L.nodeAt x1 (L.cpu x1) layout.node.CUR_TIME)
    exact hNx1 _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
  have hcn : IoRS (st := st) K.ptU Locks s (cnA (L := L) x1) := by
    show IoRS (st := st) K.ptU Locks s (L.nodeAt x1 (L.cpu x1) layout.node.CONSUMED)
    exact hNx1 _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
  refine once_gstep hR0 hW0 (R.sched.update_timestamp_nz) h (fun r h1 => ?_) (fun r h1 hk Wd6 _ => ?_)
  · rw [R.sched.update_timestamp_eq] at h1 ⊢
    rw [sched.update_timestamp.guard (gS := PathObl.guard st (IoRS (st := st) K.ptU Locks s) (IoRS (st := st) K.ptU Locks s))
      ar x1 a hct hct hcn hcn]
    exact h1
  replace h := hk
  rw [R.sched.update_timestamp_eq] at h1
  obtain ⟨⟨x2, a1⟩, eu, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  have M := invCM_hmid (Locks := Locks) hA P h0 info nx x1 x2 a1 emi enx es1 eu
  have nd2 : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      IoRS (st := st) K.ptU Locks s (L.nodeAt x2 (L.cpu x2) o) := fun o h1 h2 => by
    rw [M.c, nodeAt_of_ksb M.k]; exact (P.nd (Locks := Locks) o h1 h2).1
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `cur_sc`
  refine once_gstep hR0 hW0 (R.sched.cur_sc_nz) h (fun r h1 => ?_) (fun r h1 hk Wd7 _ => ?_)
  · rw [R.sched.cur_sc_eq] at h1 ⊢
    rw [sched.cur_sc.guard (gS := PathObl.guard st (IoRS (st := st) K.ptU Locks s) (IoRS (st := st) K.ptU Locks s)) x2
      (nd2 _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]))]
    exact h1
  replace h := hk
  rw [R.sched.cur_sc_eq] at h1
  obtain ⟨csc, ecs, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  have ec : csc = L.cscW x2 := by
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) _)] at ecs; exact (ok_inj_ff ecs).symm
  subst ec
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `action`
  refine once_gstep hR0 hW0 (R.sched.action_nz) h (fun r h1 => ?_) (fun r h1 hk Wd8 _ => ?_)
  · rw [R.sched.action_eq] at h1 ⊢
    rw [sched.action.guard (gS := PathObl.guard st (IoRS (st := st) K.ptU Locks s) (IoRS (st := st) K.ptU Locks s)) x2
      (nd2 _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]))]
    exact h1
  replace h := hk
  rw [R.sched.action_eq] at h1
  obtain ⟨i3, ei3, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  refine once_ite0 h (fun _ _ => by simp only [Once]) (fun hi3 h => ?_)
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `yield_to`
  refine once_gstep hR0 hW0 (R.obj.Tcb.yield_to_nz _) h (fun r h1 => ?_) (fun r h1 hk Wd9 _ => ?_)
  · rw [R.obj.Tcb.yield_to_eq] at h1 ⊢
    rw [obj.Tcb.yield_to.guard (gS := PathObl.guard st (IoRS (st := st) K.ptU Locks s) (IoRS (st := st) K.ptU Locks s)) _ x2
      M.yld]
    exact h1
  replace h := hk
  rw [R.obj.Tcb.yield_to_eq] at h1
  obtain ⟨i4, ei4, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  refine once_ite0 h (fun _ _ => by simp only [Once]) (fun hi4 h => ?_)
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `consumed`, `sufficient`
  refine once_gstep hR0 hW0 (R.sched.consumed_nz) h (fun r h1 => ?_) (fun r h1 hk Wd10 _ => ?_)
  · rw [R.sched.consumed_eq] at h1 ⊢
    rw [sched.consumed.guard (gS := PathObl.guard st (IoRS (st := st) K.ptU Locks s) (IoRS (st := st) K.ptU Locks s)) x2
      (nd2 _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]))]
    exact h1
  replace h := hk
  rw [R.sched.consumed_eq] at h1
  obtain ⟨i5, -, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine once_gstep hR0 hW0 (R.sporadic.sufficient_nz _ _) h (fun r h1 => ?_) (fun r h1 hk Wd11 _ => ?_)
  · rw [R.sporadic.sufficient_eq] at h1 ⊢
    rw [sporadic.sufficient.guard (gS := PathObl.guard st (IoRS (st := st) K.ptU Locks s) (IoRS (st := st) K.ptU Locks s))
      ar x2 a1 _ i5 M.rh]
    exact h1
  replace h := hk
  rw [R.sporadic.sufficient_eq] at h1
  obtain ⟨b1, -, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  refine once_ite0 h (fun _ h => ?_) (fun _ _ => by simp only [Once])
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `schedulable_here`
  have htm : IoRS (st := st) K.ptU Locks s (tmA (L := L) x2) := by
    show IoRS (st := st) K.ptU Locks s (L.nodeAt x2 (L.cpu x2) layout.node.TIMER_MIN)
    exact nd2 _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
  have hrh : IoRS (st := st) K.ptU Locks s (rhA (L := L) x2) := by
    show IoRS (st := st) K.ptU Locks s (L.nodeAt x2 (L.cpu x2) layout.node.RELEASE_HEAD)
    exact nd2 _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
  have hct2 : IoRS (st := st) K.ptU Locks s (ctA (L := L) x2) := by
    show IoRS (st := st) K.ptU Locks s (L.nodeAt x2 (L.cpu x2) layout.node.CUR_TIME)
    exact nd2 _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
  refine once_gstep hR0 hW0 (R.fastpath.schedulable_here_nz _) h (fun r h1 => ?_) (fun r h1 hk Wd12 _ => ?_)
  · rw [R.fastpath.schedulable_here_eq] at h1 ⊢
    rw [fastpath.schedulable_here.guard (gS := PathObl.guard st (IoRS (st := st) K.ptU Locks s)
      (IoRS (st := st) K.ptU Locks s)) x2 _ hct2 htm hrh M.td M.rs M.dt M.cd M.af M.dom M.sc M.inq]
    exact h1
  replace h := hk
  rw [R.fastpath.schedulable_here_eq] at h1
  obtain ⟨b2, eb2, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  refine once_ite0 h (fun hb2 h => ?_) (fun _ _ => by simp only [Once])
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `still_holds`
  refine once_gstep hR0 hW0 (R.localinv.Plan.still_holds_nz _) h (fun r h1 => ?_) (fun r h1 hk Wd13 _ => ?_)
  · rw [R.localinv.Plan.still_holds_eq] at h1 ⊢
    rw [still_holds_guard p x2 (fun w hw => pm_seen hJ hq P w hw)]
    exact h1
  replace h := hk
  rw [R.localinv.Plan.still_holds_eq] at h1
  obtain ⟨b3, eb3, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  refine once_ite0 h (fun hb3 h => ?_) (fun _ _ => by simp only [Once])
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- the IPC buffer
  obtain ⟨bsl, hbsl⟩ := buffer_slot_ok (L.curW s)
  refine once_gstep hR0 hW0 (R.msg.lookup_ipc_buffer_nz _ _) h (fun r h1 => ?_) (fun r h1 hk Wd14 _ => ?_)
  · rw [R.msg.lookup_ipc_buffer_eq] at h1 ⊢
    rw [msg.lookup_ipc_buffer.guard (gS := PathObl.guard st (IoRS (st := st) K.ptU Locks s) (IoRS (st := st) K.ptU Locks s))
      x2 false (L.curW s) hbsl M.ib (M.bs _ hbsl).1 (M.bs _ hbsl).2]
    exact h1
  replace h := hk
  rw [R.msg.lookup_ipc_buffer_eq] at h1
  obtain ⟨buf, ebuf, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  -- the length
  simp only [SProg.blk, ite_ret, SProg.sbind] at h ⊢
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- the invoked slot's cap
  refine once_gstep hR0 hW0 (R.obj.Slot.cap_nz _) h (fun r h1 => ?_) (fun r h1 hk Wd15 _ => ?_)
  · rw [R.obj.Slot.cap_eq] at h1 ⊢
    rw [obj.Slot.cap.guard (gS := PathObl.guard st (IoRS (st := st) K.ptU Locks s) (IoRS (st := st) K.ptU Locks s))
      p.slot x2 r0 r8]
    exact h1
  rw [R.obj.Slot.cap_eq] at h1
  obtain ⟨cap, ecap, rfl⟩ := bind_shape h1
  have hR := hk
  dsimp only at hR ⊢
  -- the decode onward
  simp only [bne_iff_ne, ne_eq, not_not] at hi3 hi4
  rw [hi3] at ei3
  rw [hi4] at ei4
  rw [hb2] at eb2
  rw [hb3] at eb3
  exact pm_decOnce hA hE ⟨sA, aA, h0⟩ emi ⟨enx, es1, eu, ei3, ei4, eb2, eb3⟩ ecap hR Wd15

end walk

end
end Fl4Proofs.P2.E2EP
