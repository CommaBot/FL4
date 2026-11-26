/-
# P2 (line mmuAD, gen 7): **`InsT` of an accepted invocation run at its entry, up to the decode**

slhuf gen 10's `InvCMOnce.invCM_entOnce` walks `R.invBodyG` from the entry to the decode (`invCMRest`) for `Once`.
Here the same walk for `E2EADQ.InsT` (`MmuADStep.insT_gstep` per call, on `guard st (IoRSR s) (IoWS s)`):
current thread, `MSG_INFO`, flags, the label check, `NEXT_IP`, the `FAULT_IP` write, `update_timestamp`, `cur_sc`,
`action`, `yield_to`, `consumed`, `sufficient`, `schedulable_here`, `still_holds`, the IPC buffer lookup, the
length, the invoked slot's cap. Every word read is an `IoRSR s` word and every word written an `IoWS s` word
(`IoPre.*R`, `IoPre.midR`), so for any `G` disjoint from both (`hG`) the walk costs nothing and `InsT` reduces to
`InsT` of `invCMRest` at the post-check state (`hdo`).

* `insT_hmidR`: `invCM_hmid` over `IoRSR` (`IoPre.midR`);
* **`insT_entR`**: the walk.

No premise: `hG`, `hSeen`, `hps`, `hdo` are hypotheses. No existing statement changed.
-/
import Fl4Proofs.P2.MmuADStep
import Fl4Proofs.P2.InvCMOnce
import Fl4Proofs.P2.InvDelPteAccR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField oAFFINITY)
open Fl4Proofs.P2.E2E (InsT)

section walk
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {Locks : S → U64 → Prop}
variable {A : Type} {ar : machine.Arch A}

/-- **The post-prefix facts of an accepted run** (`InvMid` for `IoRSR s`). -/
theorem insT_hmidR (hA : P0.ArchTotal ar) {number : I64} {p : localinv.Plan} {s s' : S} {a a' : A}
    (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (h : syscall.handle_invocation_local st ar s a number p = ok (true, s', a')) :
    ∀ info nx s1 s2 a1, msg.msg_info st s (L.curW s) = ok info →
      obj.Tcb.reg st (L.curW s) s layout.reg.NEXT_IP = ok nx →
      obj.Tcb.set_reg st (L.curW s) s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1 →
      sched.update_timestamp st ar s1 a = ok (s2, a1) →
      InvMid (L := L) (IoRSR st K Locks s) s s2 (L.curW s) := by
  obtain ⟨info, -, -, -, ht⟩ := handle_inv_inv h
  obtain ⟨nx0, s10, s20, a10, -, -, es10, eu0, -, -, -, hh0, -⟩ := invTail_inv ht
  have hsc2 := (here_facts hh0).sc
  have w := prefix_writes ar hA P.tp P.np P.cT es10 eu0
  have e1 : L.mem s20 (scA (L.curW s)) = L.mem s (scA (L.curW s)) :=
    w.2.2 _ (field_aligned P.tA (by simp) (by simp)) (preW_tcb P.tA P.np P.cT (K := 3464#u64) (by simp) (by simp))
  have hsc0 : L.mem s (scA (L.curW s)) = L.cscW s := (P.hcsc (by rw [← e1]; exact hsc2)).symm
  obtain ⟨C, hroot, hcl, hC⟩ := P.walk
  obtain ⟨⟨Q, Rq, hq⟩, hbd, ⟨hO, -, hX⟩, -, hS⟩ := P.bxi
  have hd : ∀ {c : U64}, c ∈ Scs → OutsideObjs st T Cs s (headA c) := fun {c} hc => by
    obtain ⟨hP, hz⟩ := hO.sc _ hc
    obtain ⟨h8, h128, -⟩ := sc_lo hP hz
    have hh := headA_val' hP hz
    exact hq.omega _ (hS.sub _ ((hS.all _ hc).2.2 _ (by unfold Aligned; omega) ⟨by omega, by omega⟩))
  intro info nx s1 s2 a1 emi enx es1 eu
  have M2 := io_hmid' (a := a) ar hA hq.tcbs (hq.nodes _ hq.cur) hq.cur hq.curT
    (P.midR (Locks := Locks) (P.ioWr (Locks := Locks)) hroot hcl (fun p r m y hp hm => (hC p r m y hp hm).1) hsc0)
    (fun p r m y hp hm => (hC p r m y hp hm).2) (fun x hx => (P.fin x hx).2) (hd hX.cur)
    (fun h0 => ⟨(bxi_rh P.bxi h0).1, hd (bxi_rh P.bxi h0).2.1⟩) info nx _ s2 a1 emi enx es1 eu
  exact ⟨M2.k, M2.c, M2.cur, M2.yld, M2.rh, M2.td, M2.rs, M2.dt, M2.cd, M2.af, M2.dom, M2.iok.1.sc, M2.iok.1.inq,
    M2.iok.1.ib, M2.iok.1.bs⟩

set_option maxHeartbeats 8000000 in
/-- **`InsT` of an accepted run at its entry, up to the decode** (module docstring). -/
theorem insT_entR (hA : P0.ArchTotal ar) {number : I64} {p : localinv.Plan} {P : S → Prop}
    {G : U64 → Prop} {Q : U64 → U64 → Prop} {NP User : U64 → Prop}
    (hPE : ∀ s, P s → IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hG : ∀ s, P s → ∀ q, (IoRSR st K Locks s q ∨ IoWS (st := st) K Locks s q) → ¬ G q)
    (hSeen : ∀ s, P s → ∀ x, SeenW p x → IoRSR st K Locks s x)
    (hps : ∀ s, P s → IoRSR st K Locks s p.slot ∧ IoRSR st K Locks s (core.num.U64.wrapping_add p.slot 8#u64))
    (hdo : ∀ s (a : A) info nx s1 s2 a1 buf length cap (r' : Bool × S × A), P s →
      (∃ s' a', syscall.handle_invocation_local st ar s a number p = ok (true, s', a')) →
      msg.msg_info st s (L.curW s) = ok info → InvChk st ar s a (L.curW s) p nx s1 s2 a1 →
      msg.lookup_ipc_buffer st s2 false (L.curW s) = ok buf → obj.Slot.cap st p.slot s2 = ok cap →
      (if info.length > msg.N_MSG_REGISTERS then (if buf = 0#u64 then ok msg.N_MSG_REGISTERS else ok info.length)
        else ok info.length) = ok length →
      interp st ar (invCMRest (L.curW s) info p buf length cap) s2 a1 = ok r' →
      InsT st ar G Q NP User (invCMRest (L.curW s) info p buf length cap) s2 a1) :
    ∀ s (a : A) r, P s → (∃ s1 a1, syscall.handle_invocation_local st ar s a number p = ok (true, s1, a1)) →
      interp st ar (R.invBodyG number p) s a = ok r → InsT st ar G Q NP User (R.invBodyG number p) s a := by
  intro s a r hE hac h
  obtain ⟨sA, aA, h0⟩ := hac
  have P := hPE s hE
  have hR0 : ∀ q, IoRSR st K Locks s q → ¬ G q := fun q hq => hG s hE q (Or.inl hq)
  have hW0 : ∀ q, IoWS (st := st) K Locks s q → ¬ G q := fun q hq => hG s hE q (Or.inr hq)
  have nC := (P.ndR (Locks := Locks) layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD])
    (by simp [layout.node.CUR_THREAD])).1
  unfold R.invBodyG at h ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- the current thread
  refine insT_gstep hR0 hW0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
  · rw [R.sched.cur_thread_eq] at h1 ⊢
    rw [sched.cur_thread.guard (gS := PathObl.guard st (IoRSR st K Locks s) (IoWS (st := st) K Locks s)) s nC]
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
  refine insT_gstep hR0 hW0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
  · rw [R.msg.msg_info_eq] at h1 ⊢
    rw [msg.msg_info.guard (gS := PathObl.guard st (IoRSR st K Locks s) (IoWS (st := st) K Locks s)) s _
      (P.regR (Locks := Locks) (by simp [layout.reg.MSG_INFO])).1]
    exact h1
  replace h := hk
  rw [R.msg.msg_info_eq] at h1
  obtain ⟨info, emi, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  refine insT_ite h (fun _ _ => by simp only [InsT]) (fun _ h => ?_)
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- the flags
  refine insT_gstep hR0 hW0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
  · rw [R.obj.Tcb.flags_eq] at h1 ⊢
    rw [obj.Tcb.flags.guard (gS := PathObl.guard st (IoRSR st K Locks s) (IoWS (st := st) K Locks s)) _ s
      (P.homeR (Locks := Locks) (off := 3456#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField])).1]
    exact h1
  replace h := hk
  rw [R.obj.Tcb.flags_eq] at h1
  obtain ⟨i, -, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine insT_ite h (fun _ _ => by simp only [InsT]) (fun _ h => ?_)
  refine insT_ite h (fun _ _ => by simp only [InsT]) (fun _ h => ?_)
  -- the tail
  unfold R.invTailG at h ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine insT_liftR h (fun b _ h => ?_)
  cases b
  · rw [if_neg Bool.false_ne_true]; simp only [InsT]
  rw [if_pos rfl] at h ⊢
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `NEXT_IP`
  refine insT_gstep hR0 hW0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
  · rw [R.obj.Tcb.reg_eq] at h1 ⊢
    rw [obj.Tcb.reg.guard (gS := PathObl.guard st (IoRSR st K Locks s) (IoWS (st := st) K Locks s)) _ s _
      (P.regR (Locks := Locks) (by simp [layout.reg.NEXT_IP])).1]
    exact h1
  replace h := hk
  rw [R.obj.Tcb.reg_eq] at h1
  obtain ⟨nx, enx, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- the `FAULT_IP` write
  refine insT_gstep hR0 hW0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
  · rw [R.obj.Tcb.set_reg_eq] at h1 ⊢
    rw [obj.Tcb.set_reg.guard (gS := PathObl.guard st (IoRSR st K Locks s) (IoWS (st := st) K Locks s)) _ s
      _ _ (P.regR (Locks := Locks) (by simp [layout.reg.FAULT_IP])).2]
    exact h1
  replace h := hk
  rw [R.obj.Tcb.set_reg_eq] at h1
  obtain ⟨x1, es1, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  have ex1 : x1 = L.wr s (regA (L.curW s) layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx 2#u64) := by
    rw [set_reg_ok'] at es1; exact (ok_inj_ff es1).symm
  have hNx1 : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      IoRSR st K Locks s (L.nodeAt x1 (L.cpu x1) o) ∧ IoWS (st := st) K Locks s (L.nodeAt x1 (L.cpu x1) o) :=
    fun o h1 h2 => by
      rw [ex1, LawfulStore.cpu_wr, nodeAt_of_ksb (L.ksb_wr _ _ _)]; exact P.ndR (Locks := Locks) o h1 h2
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `update_timestamp`
  have hct := hNx1 layout.node.CUR_TIME (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
  have hcn := hNx1 layout.node.CONSUMED (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
  refine insT_gstep hR0 hW0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
  · rw [R.sched.update_timestamp_eq] at h1 ⊢
    rw [sched.update_timestamp.guard (gS := PathObl.guard st (IoRSR st K Locks s) (IoWS (st := st) K Locks s))
      ar x1 a hct.1 hct.2 hcn.1 hcn.2]
    exact h1
  replace h := hk
  rw [R.sched.update_timestamp_eq] at h1
  obtain ⟨⟨x2, a1⟩, eu, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  have M := insT_hmidR (Locks := Locks) hA P h0 info nx x1 x2 a1 emi enx es1 eu
  have nd2 : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      IoRSR st K Locks s (L.nodeAt x2 (L.cpu x2) o) := fun o h1 h2 => by
    rw [M.c, nodeAt_of_ksb M.k]; exact (P.ndR (Locks := Locks) o h1 h2).1
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `cur_sc`
  refine insT_gstep hR0 hW0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
  · rw [R.sched.cur_sc_eq] at h1 ⊢
    rw [sched.cur_sc.guard (gS := PathObl.guard st (IoRSR st K Locks s) (IoWS (st := st) K Locks s)) x2
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
  refine insT_gstep hR0 hW0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
  · rw [R.sched.action_eq] at h1 ⊢
    rw [sched.action.guard (gS := PathObl.guard st (IoRSR st K Locks s) (IoWS (st := st) K Locks s)) x2
      (nd2 _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]))]
    exact h1
  replace h := hk
  rw [R.sched.action_eq] at h1
  obtain ⟨i3, ei3, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  refine insT_ite h (fun _ _ => by simp only [InsT]) (fun hi3 h => ?_)
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `yield_to`
  refine insT_gstep hR0 hW0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
  · rw [R.obj.Tcb.yield_to_eq] at h1 ⊢
    rw [obj.Tcb.yield_to.guard (gS := PathObl.guard st (IoRSR st K Locks s) (IoWS (st := st) K Locks s)) _ x2
      M.yld]
    exact h1
  replace h := hk
  rw [R.obj.Tcb.yield_to_eq] at h1
  obtain ⟨i4, ei4, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  refine insT_ite h (fun _ _ => by simp only [InsT]) (fun hi4 h => ?_)
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `consumed`, `sufficient`
  refine insT_gstep hR0 hW0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
  · rw [R.sched.consumed_eq] at h1 ⊢
    rw [sched.consumed.guard (gS := PathObl.guard st (IoRSR st K Locks s) (IoWS (st := st) K Locks s)) x2
      (nd2 _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]))]
    exact h1
  replace h := hk
  rw [R.sched.consumed_eq] at h1
  obtain ⟨i5, -, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine insT_gstep hR0 hW0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
  · rw [R.sporadic.sufficient_eq] at h1 ⊢
    rw [sporadic.sufficient.guard (gS := PathObl.guard st (IoRSR st K Locks s) (IoWS (st := st) K Locks s))
      ar x2 a1 _ i5 M.rh]
    exact h1
  replace h := hk
  rw [R.sporadic.sufficient_eq] at h1
  obtain ⟨b1, -, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  refine insT_ite h (fun _ h => ?_) (fun _ _ => by simp only [InsT])
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `schedulable_here`
  have htm : IoRSR st K Locks s (tmA (L := L) x2) := by
    show IoRSR st K Locks s (L.nodeAt x2 (L.cpu x2) layout.node.TIMER_MIN)
    exact nd2 _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
  have hrh : IoRSR st K Locks s (rhA (L := L) x2) := by
    show IoRSR st K Locks s (L.nodeAt x2 (L.cpu x2) layout.node.RELEASE_HEAD)
    exact nd2 _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
  have hct2 : IoRSR st K Locks s (ctA (L := L) x2) := by
    show IoRSR st K Locks s (L.nodeAt x2 (L.cpu x2) layout.node.CUR_TIME)
    exact nd2 _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
  refine insT_gstep hR0 hW0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
  · rw [R.fastpath.schedulable_here_eq] at h1 ⊢
    rw [fastpath.schedulable_here.guard (gS := PathObl.guard st (IoRSR st K Locks s)
      (IoWS (st := st) K Locks s)) x2 _ hct2 htm hrh M.td M.rs M.dt M.cd M.af M.dom M.sc M.inq]
    exact h1
  replace h := hk
  rw [R.fastpath.schedulable_here_eq] at h1
  obtain ⟨b2, eb2, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  refine insT_ite h (fun hb2 h => ?_) (fun _ _ => by simp only [InsT])
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `still_holds`
  refine insT_gstep hR0 hW0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
  · rw [R.localinv.Plan.still_holds_eq] at h1 ⊢
    rw [still_holds_guard p x2 (fun w hw => hSeen s hE w hw)]
    exact h1
  replace h := hk
  rw [R.localinv.Plan.still_holds_eq] at h1
  obtain ⟨b3, eb3, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  refine insT_ite h (fun hb3 h => ?_) (fun _ _ => by simp only [InsT])
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- the IPC buffer
  obtain ⟨bsl, hbsl⟩ := buffer_slot_ok (L.curW s)
  refine insT_gstep hR0 hW0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
  · rw [R.msg.lookup_ipc_buffer_eq] at h1 ⊢
    rw [msg.lookup_ipc_buffer.guard (gS := PathObl.guard st (IoRSR st K Locks s) (IoWS (st := st) K Locks s))
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
  refine insT_gstep hR0 hW0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
  · rw [R.obj.Slot.cap_eq] at h1 ⊢
    rw [obj.Slot.cap.guard (gS := PathObl.guard st (IoRSR st K Locks s) (IoWS (st := st) K Locks s))
      p.slot x2 (hps s hE).1 (hps s hE).2]
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
  exact hdo s a info nx x1 x2 a1 buf _ cap _ hE ⟨sA, aA, h0⟩ emi ⟨enx, es1, eu, ei3, ei4, eb2, eb3⟩ ebuf ecap
    (by split <;> (try split) <;> rfl) hR

end walk

end Fl4Proofs.P2.PathObl
