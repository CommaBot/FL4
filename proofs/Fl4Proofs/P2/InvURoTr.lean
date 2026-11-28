/-
# P2 (line invj, generation 2): ReadOnce of accepted truncated Deletes (`InvURoTrW` discharged)

The uncut CNodeDelete path (`inv_pathsKFU2`, P2/InvJ.lean) had one [W] left, `InvURoTrW`: ReadOnce, over the
user-word read set `InvCMRS`, of accepted runs with `length < 2` (`¬ InvLen`). Here it is proved for the tree
`R.invBodyG number p`:

* **entry walk**: slhuf gen 10's `invCM_entOnce` (P2/InvCMOnce.lean, from `par/slhuf3` via int/j18) copied as
  `invU_entOnce`, its decode-onward premise `InvUDecOnceW` = slhuf's `InvCMDecOnceW` plus the hypothesis that
  `info.length < 2` gives `length < 2` (`len_trunc`: the length is `info.length` when `info.length ≤ 4`);
* **the truncated rest** (`invU_decOnce`, `InvUDecOnceW` at `Pre ∧ ¬ InvLen`), on `guard st (IoRS s) (IoWS s)`
  (no user word, `IoPre.ioWS_nu`):
  - `R.decCNG` reads only the current thread (`decCNG_trunc`: `cnode.decode` stops at `length < 2` on any store);
  - `R.invPostG` → `R.syscall.reply_error … TruncatedMessage` (**`invU_replyOnce`**): the receiver's buffer lookup,
    `BADGE`, `error_mrs` (no access), then, for a set buffer, the **one user read** (word 7,
    `DEBUG_MESSAGE_START + 1`; racy, read from the empty touched set) and its write, then `MSG_INFO`;
  - `after_invocation (Ok ())` (no access) and `finish` (**`invU_tailOnce`**: `syscall.finish.guard_resume` with
    stpost's `FinOK` after the truncated block, `truncFin8`, at the state the reply reached);
* **`invURoTrW_of`**: `Once` at the entry (`invU_entOnce`) carried to every alternative by `once_agreeJ` over the
  accepted run on `guard st (InvCMRS s) (InvCMWS s)` (`InvUAccW`: stpost's `invUAccW_of2` + `invBlkUW2_of8`);
* **`inv_pathsKFU3`**: `inv_pathsKFU2` with `htr := invURoTrW_of`. Premises: `hA`, [P] `hm`, [J] `hIw`, [P] `hlk`.
  **`inv_pathsKFU4`**: `hIw` from iolay's `ioPre_wr_hIw` (P2/E2EVFl4W9.lean). Premises: `hA`, [P] `hm`,
  [P] `hCs` (the core set below 64: P3's `JKern.csLt` at the top, `IoPremW9.hCs`), [P] `hlk`.
  **`inv_pathsKF4`**: `inv_pathsKF3` likewise.

No existing statement changes; no `kernel_entry_reach*` is touched.
-/
import Fl4Proofs.P2.InvJ
import Fl4Proofs.P2.InvCMOnce
import Fl4Proofs.P2.E2EVFl4W9
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField oAFFINITY)
open Fl4Proofs.P2.E2E (Once ReadOnce)

/-! ## The decode-onward premise with the length link -/

section prem
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **`Once` of an accepted run from the decode on**, slhuf's `InvCMDecOnceW` with one more hypothesis: a message
length below 2 gives a decode length below 2 (the tree's `length` is the length clamp of `info.length`). -/
def InvUDecOnceW (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A) (number : I64)
    (p : localinv.Plan) (K : KLayout) (Locks : S → U64 → Prop) (P : S → Prop) : Prop :=
  ∀ s (a : A) info nx s1 s2 a1 buf length cap (r' : Bool × S × A), P s →
    (∃ s' a', syscall.handle_invocation_local st ar s a number p = ok (true, s', a')) →
    msg.msg_info st s (L.curW s) = ok info → InvChk st ar s a (L.curW s) p nx s1 s2 a1 →
    msg.lookup_ipc_buffer st s2 false (L.curW s) = ok buf → obj.Slot.cap st p.slot s2 = ok cap →
    (info.length < 2#u64 → length < 2#u64) →
    interp st ar (invCMRest (L.curW s) info p buf length cap) s2 a1 = ok r' →
    ∀ Wd, Once st ar (InvCMRS (st := st) K Locks s) (· ∈ K.user) Wd ∅ (invCMRest (L.curW s) info p buf length cap)
      s2 a1

/-- The length clamp keeps a message length below 2. -/
theorem len_trunc {info : msginfo.MessageInfo} {buf : U64} (h : info.length < 2#u64) :
    (if info.length > msg.N_MSG_REGISTERS then (if buf = 0#u64 then msg.N_MSG_REGISTERS else info.length)
      else info.length) < 2#u64 := by
  have hN : msg.N_MSG_REGISTERS.val = 4 := by simp [msg.N_MSG_REGISTERS]
  have h2 : info.length.val < 2 := by have := h; scalar_tac
  rw [if_neg]
  · exact h
  · intro hc
    have : msg.N_MSG_REGISTERS.val < info.length.val := hc
    omega

end prem

/-! ## The entry walk (slhuf's `invCM_entOnce`, the decode-onward premise with the length link) -/

section walk
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {Locks : S → U64 → Prop}
variable {A : Type} {ar : machine.Arch A}

/-- **`ReadOnce` of an accepted run at its entry, up to the decode** (module docstring): the walk of
`R.invBodyG` from the entry (slhuf gen 10's `invCM_entOnce`, copied); `hdo` the decode onward (`InvUDecOnceW`). -/
theorem invU_entOnce (hA : P0.ArchTotal ar) {number : I64} {p : localinv.Plan} {P : S → Prop}
    (hPE : ∀ s, P s → IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hSeen : ∀ s, P s → ∀ x, SeenW p x → IoRS (st := st) K Locks s x)
    (hps : ∀ s, P s → IoRS (st := st) K Locks s p.slot ∧
      IoRS (st := st) K Locks s (core.num.U64.wrapping_add p.slot 8#u64))
    (hdo : InvUDecOnceW st ar number p K Locks P) :
    InvCMRoEntW st ar number p K Locks (R.invBodyG number p) P := by
  intro s a r hE hac h
  obtain ⟨sA, aA, h0⟩ := hac
  have P := hPE s hE
  have hR0 : ∀ q, IoRS (st := st) K Locks s q → InvCMRS (st := st) K Locks s q ∧ q ∉ K.user :=
    fun q hq => ⟨ioRS_cm hq, hq.2.1⟩
  have hW0 : ∀ q, IoRS (st := st) K Locks s q → q ∉ K.user := fun q hq => hq.2.1
  have nC := (P.nd (Locks := Locks) layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD])
    (by simp [layout.node.CUR_THREAD])).1
  unfold R.invBodyG at h ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- the current thread
  refine once_gstep hR0 hW0 (R.sched.cur_thread_nz) h (fun r h1 => ?_) (fun r h1 hk Wd1 _ => ?_)
  · rw [R.sched.cur_thread_eq] at h1 ⊢
    rw [sched.cur_thread.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s)) s nC]
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
    rw [msg.msg_info.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s)) s _
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
    rw [obj.Tcb.flags.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s)) _ s
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
  unfold R.invTailG at h ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine once_liftR h (fun b _ h => ?_)
  cases b
  · rw [if_neg Bool.false_ne_true]; simp only [Once]
  rw [if_pos rfl] at h ⊢
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `NEXT_IP`
  refine once_gstep hR0 hW0 (R.obj.Tcb.reg_nz _ _) h (fun r h1 => ?_) (fun r h1 hk Wd4 _ => ?_)
  · rw [R.obj.Tcb.reg_eq] at h1 ⊢
    rw [obj.Tcb.reg.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s)) _ s _
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
    rw [obj.Tcb.set_reg.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s)) _ s
      _ _ (P.reg (Locks := Locks) (by simp [layout.reg.FAULT_IP])).1]
    exact h1
  replace h := hk
  rw [R.obj.Tcb.set_reg_eq] at h1
  obtain ⟨x1, es1, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  have ex1 : x1 = L.wr s (regA (L.curW s) layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx 2#u64) := by
    rw [set_reg_ok'] at es1; exact (ok_inj_ff es1).symm
  have hNx1 : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      IoRS (st := st) K Locks s (L.nodeAt x1 (L.cpu x1) o) := fun o h1 h2 => by
    rw [ex1, LawfulStore.cpu_wr, nodeAt_of_ksb (L.ksb_wr _ _ _)]; exact (P.nd (Locks := Locks) o h1 h2).1
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `update_timestamp`
  have hct : IoRS (st := st) K Locks s (ctA (L := L) x1) := by
    show IoRS (st := st) K Locks s (L.nodeAt x1 (L.cpu x1) layout.node.CUR_TIME)
    exact hNx1 _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
  have hcn : IoRS (st := st) K Locks s (cnA (L := L) x1) := by
    show IoRS (st := st) K Locks s (L.nodeAt x1 (L.cpu x1) layout.node.CONSUMED)
    exact hNx1 _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
  refine once_gstep hR0 hW0 (R.sched.update_timestamp_nz) h (fun r h1 => ?_) (fun r h1 hk Wd6 _ => ?_)
  · rw [R.sched.update_timestamp_eq] at h1 ⊢
    rw [sched.update_timestamp.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s))
      ar x1 a hct hct hcn hcn]
    exact h1
  replace h := hk
  rw [R.sched.update_timestamp_eq] at h1
  obtain ⟨⟨x2, a1⟩, eu, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  have M := invCM_hmid (Locks := Locks) hA P h0 info nx x1 x2 a1 emi enx es1 eu
  have nd2 : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      IoRS (st := st) K Locks s (L.nodeAt x2 (L.cpu x2) o) := fun o h1 h2 => by
    rw [M.c, nodeAt_of_ksb M.k]; exact (P.nd (Locks := Locks) o h1 h2).1
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `cur_sc`
  refine once_gstep hR0 hW0 (R.sched.cur_sc_nz) h (fun r h1 => ?_) (fun r h1 hk Wd7 _ => ?_)
  · rw [R.sched.cur_sc_eq] at h1 ⊢
    rw [sched.cur_sc.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s)) x2
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
    rw [sched.action.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s)) x2
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
    rw [obj.Tcb.yield_to.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s)) _ x2
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
    rw [sched.consumed.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s)) x2
      (nd2 _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]))]
    exact h1
  replace h := hk
  rw [R.sched.consumed_eq] at h1
  obtain ⟨i5, -, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine once_gstep hR0 hW0 (R.sporadic.sufficient_nz _ _) h (fun r h1 => ?_) (fun r h1 hk Wd11 _ => ?_)
  · rw [R.sporadic.sufficient_eq] at h1 ⊢
    rw [sporadic.sufficient.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s))
      ar x2 a1 _ i5 M.rh]
    exact h1
  replace h := hk
  rw [R.sporadic.sufficient_eq] at h1
  obtain ⟨b1, -, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  refine once_ite0 h (fun _ h => ?_) (fun _ _ => by simp only [Once])
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `schedulable_here`
  have htm : IoRS (st := st) K Locks s (tmA (L := L) x2) := by
    show IoRS (st := st) K Locks s (L.nodeAt x2 (L.cpu x2) layout.node.TIMER_MIN)
    exact nd2 _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
  have hrh : IoRS (st := st) K Locks s (rhA (L := L) x2) := by
    show IoRS (st := st) K Locks s (L.nodeAt x2 (L.cpu x2) layout.node.RELEASE_HEAD)
    exact nd2 _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
  have hct2 : IoRS (st := st) K Locks s (ctA (L := L) x2) := by
    show IoRS (st := st) K Locks s (L.nodeAt x2 (L.cpu x2) layout.node.CUR_TIME)
    exact nd2 _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
  refine once_gstep hR0 hW0 (R.fastpath.schedulable_here_nz _) h (fun r h1 => ?_) (fun r h1 hk Wd12 _ => ?_)
  · rw [R.fastpath.schedulable_here_eq] at h1 ⊢
    rw [fastpath.schedulable_here.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s)
      (IoRS (st := st) K Locks s)) x2 _ hct2 htm hrh M.td M.rs M.dt M.cd M.af M.dom M.sc M.inq]
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
    rw [still_holds_guard p x2 (fun w hw => hSeen s hE w hw)]
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
    rw [msg.lookup_ipc_buffer.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s))
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
    rw [obj.Slot.cap.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s))
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
  exact hdo s a info nx x1 x2 a1 buf _ cap _ hE ⟨sA, aA, h0⟩ emi ⟨enx, es1, eu, ei3, ei4, eb2, eb3⟩ ebuf ecap (fun hl => len_trunc hl) hR Wd15
end walk

/-! ## The truncated rest -/

section rest
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}
variable {A : Type} {ar : machine.Arch A}

/-- A word an accepted run may write is no user word (user words are in no region, so the gate's). -/
theorem IoPre.ioWS_nu {T Rp Scs Nt : Set U64} {H : Heap} {Z : U64 → Nat} {s : S}
    (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) {q : U64} (hq : IoWS (st := st) K Locks s q) : q ∉ K.user := by
  intro hu
  have hn := P.user_none ⟨hq.1, hu⟩
  have hp := hq.2
  unfold WPerm at hp
  rw [own_none hn] at hp
  exact hp

/-- **After the truncated reply: `after_invocation (Ok ())` and `finish`** read only `IoRS s` words
(`syscall.finish.guard_resume` with `truncFin8`'s `FinOK` at the reply's end state). -/
theorem invU_tailOnce (hA : P0.ArchTotal ar) {s s2 x5 : S} {a a1 : A} {p : localinv.Plan} {nx : U64} {s1 : S}
    {length : U64} {cp cr cg cgb : U64} {r' : Bool × S × A}
    (P : IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (hcs : obj.Slot.cap st p.slot s = ok (.CNode cp cr cg cgb)) (hsl : p.slot ∈ K.slots)
    (hbuf : InvBufJ8 st K s) (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1)
    (hcap : obj.Slot.cap st p.slot s2 = ok (.CNode cp cr cg cgb)) (hlen : length < 2#u64)
    (er : syscall.reply_error st s2 (L.curW s) .TruncatedMessage = ok x5)
    (h : interp st ar ((R.syscall.after_invocation (.Ok ())).sbind fun _ =>
      R.syscall.finish.sbind fun _ => SProg.ret true) x5 a1 = ok r')
    (Wd T : Set U64) :
    Once st ar (InvCMRS (st := st) K Locks s) (· ∈ K.user) Wd T ((R.syscall.after_invocation (.Ok ())).sbind fun _ =>
      R.syscall.finish.sbind fun _ => SProg.ret true) x5 a1 := by
  have hy : syscall.decode_invocation st ar s2 a1 fl4_abi.label.CNodeDelete length p.slot (.CNode cp cr cg cgb)
      true true true false 0#u64 p.extra = ok (.Err (.Sys .TruncatedMessage), s2, a1) := by
    rw [decode_cnode_eq ar, cnode_decode_trunc ar st hlen]
  have hz : invRep st (L.curW s) s2 a1 (.Err (.Sys .TruncatedMessage)) = ok (x5, a1, .Ok ()) := by
    unfold invRep
    simp only [er, bind_ok, uncurry_apply_pair]
    try rfl
  obtain ⟨-, F⟩ := truncFin8 (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoWS (st := st) K Locks s))
    (W := IoWS (st := st) K Locks s) hA P P.ioWr (SWr.of_W P.stw.2) hcs hsl hbuf C hcap hlen hy hz
  unfold R.syscall.after_invocation at h ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine once_gstep (R0 := IoRS (st := st) K Locks s) (W0 := IoWS (st := st) K Locks s)
    (fun q hq => ⟨ioRS_cm hq, hq.2.1⟩) (fun q hq => P.ioWS_nu hq) R.syscall.finish_nz h (fun r h1 => ?_)
    (fun _ _ _ _ _ => by simp only [Once])
  rw [R.syscall.finish_eq] at h1 ⊢
  rw [syscall.finish.guard_resume ar x5 a1 (nd_at (fun o h1 h2 => P.nd (Locks := Locks) o h1 h2) F.k F.c) F.nd F.td
    F.rs F.ha F.hsw F.hfr F.hact F.hvc]
  exact h1

/-- **`reply_error TruncatedMessage` read once** (module docstring): every read but word 7 of the receiver's buffer is
an `IoRS s` word; that one user word is read from the empty touched set, then written. The continuation `k` is
handed the state the reply reached. -/
theorem invU_replyOnce {s s2 : S} {a1 : A} {Y : Type} {k : Unit → SProg Y} {r' : Y × S × A}
    {T Rp Scs Nt : Set U64} {H : Heap} {Z : U64 → Nat}
    (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) (M : InvMid (L := L) (IoRS (st := st) K Locks s) s s2 (L.curW s))
    (hTail : ∀ x5 Wd' T', syscall.reply_error st s2 (L.curW s) .TruncatedMessage = ok x5 →
      interp st ar (k ()) x5 a1 = ok r' →
      Once st ar (InvCMRS (st := st) K Locks s) (· ∈ K.user) Wd' T' (k ()) x5 a1)
    (h : interp st ar ((R.syscall.reply_error (L.curW s) .TruncatedMessage).sbind k) s2 a1 = ok r')
    (Wd : Set U64) :
    Once st ar (InvCMRS (st := st) K Locks s) (· ∈ K.user) Wd ∅
      ((R.syscall.reply_error (L.curW s) .TruncatedMessage).sbind k) s2 a1 := by
  have hR0 : ∀ q, IoRS (st := st) K Locks s q → InvCMRS (st := st) K Locks s q ∧ q ∉ K.user :=
    fun q hq => ⟨ioRS_cm hq, hq.2.1⟩
  have hW0 : ∀ q, IoWS (st := st) K Locks s q → q ∉ K.user := fun q hq => P.ioWS_nu hq
  unfold R.syscall.reply_error at h ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- the receiver's buffer
  obtain ⟨bsl, hbsl⟩ := buffer_slot_ok (L.curW s)
  refine once_gstep hR0 hW0 (R.msg.lookup_ipc_buffer_nz _ _) h (fun r h1 => ?_) (fun r h1 hk Wd1 _ => ?_)
  · rw [R.msg.lookup_ipc_buffer_eq] at h1 ⊢
    rw [msg.lookup_ipc_buffer.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoWS (st := st) K Locks s))
      s2 true (L.curW s) hbsl M.ib (M.bs _ hbsl).1 (M.bs _ hbsl).2]
    exact h1
  rw [R.msg.lookup_ipc_buffer_eq] at h1
  obtain ⟨b, eb, rfl⟩ := bind_shape h1
  replace h := hk
  dsimp only at h ⊢
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `BADGE`
  refine once_gstep hR0 hW0 (R.obj.Tcb.set_reg_nz _ _ _) h (fun r h1 => ?_) (fun r h1 hk Wd2 _ => ?_)
  · rw [R.obj.Tcb.set_reg_eq] at h1 ⊢
    rw [obj.Tcb.set_reg.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoWS (st := st) K Locks s)) _ s2
      _ _ (P.reg (Locks := Locks) (by simp [layout.reg.BADGE])).2]
    exact h1
  rw [R.obj.Tcb.set_reg_eq] at h1
  obtain ⟨x3, es3, rfl⟩ := bind_shape h1
  replace h := hk
  dsimp only at h ⊢
  -- `error_mrs` (no access) and the buffer word
  unfold R.syscall.error_mrs at h ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind, SProg.blk,
    fl4_abi.config.KERNEL_INVOCATION_REPORT_ERROR_IPC, ↓reduceIte] at h ⊢
  refine once_ite h (fun hb0 h => ?_) (fun hb0 h => ?_)
  · simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
    refine once_liftR h (fun i ei h => ?_)
    unfold R.msg.buf_get at h ⊢
    simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind, SProg.read] at h ⊢
    simp only [interp] at h
    obtain ⟨w, hv, h⟩ := bok.mp h
    simp only [Once]
    refine ⟨fun _ => Set.notMem_empty _, fun w' hw' => ?_⟩
    rw [hv] at hw'
    obtain rfl := ok_inj_ff hw'
    unfold R.msg.buf_set at h ⊢
    simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind, SProg.write] at h ⊢
    simp only [interp] at h
    obtain ⟨s4, hs4, h⟩ := bok.mp h
    simp only [Once]
    intro s4' hs4'
    rw [hs4] at hs4'
    obtain rfl := ok_inj_ff hs4'
    refine once_liftR h (fun c ec h => ?_)
    refine once_liftR h (fun mi emi h => ?_)
    refine once_gstep hR0 hW0 (R.msg.set_msg_info_nz _ _) h (fun r h1 => ?_) (fun r h1 hk Wd5 _ => ?_)
    · rw [R.msg.set_msg_info_eq] at h1 ⊢
      rw [msg.set_msg_info.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoWS (st := st) K Locks s)) _ _ _
        (P.reg (Locks := Locks) (by simp [layout.reg.MSG_INFO])).2]
      exact h1
    rw [R.msg.set_msg_info_eq] at h1
    obtain ⟨x5, es5, rfl⟩ := bind_shape h1
    dsimp only at hk ⊢
    refine hTail x5 _ _ ?_ hk
    unfold syscall.reply_error msg.buf_get msg.buf_set
    simp only [eb, es3, error_mrs_trunc, bind_ok, lift, uncurry_apply_pair,
      fl4_abi.config.KERNEL_INVOCATION_REPORT_ERROR_IPC, ↓reduceIte, hb0, ei, ec, hv, hs4, emi, es5]
  · refine once_liftR h (fun c ec h => ?_)
    refine once_liftR h (fun mi emi h => ?_)
    refine once_gstep hR0 hW0 (R.msg.set_msg_info_nz _ _) h (fun r h1 => ?_) (fun r h1 hk Wd5 _ => ?_)
    · rw [R.msg.set_msg_info_eq] at h1 ⊢
      rw [msg.set_msg_info.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoWS (st := st) K Locks s)) _ _ _
        (P.reg (Locks := Locks) (by simp [layout.reg.MSG_INFO])).2]
      exact h1
    rw [R.msg.set_msg_info_eq] at h1
    obtain ⟨x5, es5, rfl⟩ := bind_shape h1
    dsimp only at hk ⊢
    refine hTail x5 _ _ ?_ hk
    unfold syscall.reply_error
    simp only [eb, es3, error_mrs_trunc, bind_ok, lift, uncurry_apply_pair,
      fl4_abi.config.KERNEL_INVOCATION_REPORT_ERROR_IPC, ↓reduceIte, hb0, ec, Bool.false_eq_true, emi, es5]

/-- (invj gen 2) **The decode onward of an accepted truncated Delete reads once** (`InvUDecOnceW` at
`Pre ∧ ¬ InvLen`; module docstring). No premise. -/
theorem invU_decOnce (hA : P0.ArchTotal ar) {number : I64} {p : localinv.Plan} {m0 : U64 → U64} :
    InvUDecOnceW st ar number p K Locks
      (fun s => (SlJAt (L := L) K s ∧ InvQF st Cs Ω Sg Ac Locks p K m0 s) ∧ ¬ InvLen st s) := by
  intro s a info nx s1 s2 a1 buf length cap r' hE hac emi C ebuf ecap hlen h Wd
  obtain ⟨⟨hJ, hqf⟩, hnL⟩ := hE
  obtain ⟨sA, aA, h0⟩ := hac
  have P := hqf.1.1.1
  obtain ⟨cp, cr, cg, cgb, -, -, -, -, -, -, -, hcs, hsl, -⟩ := del_core hqf
  have hlbl : info.label = fl4_abi.label.CNodeDelete := (hqf.1.2.2.1 _ info (cur_thread_ok s) emi).1
  have hil : info.length < 2#u64 := by
    by_contra hc
    apply hnL
    intro t info' ht hi'
    have et : t = L.curW s := ok_inj_ff (ht.symm.trans (cur_thread_ok s))
    subst et
    rw [emi] at hi'
    have ei : info = info' := ok_inj_ff hi'
    subst ei
    have : ¬ info.length.val < 2 := fun h' => hc (by scalar_tac)
    omega
  have hlen' := hlen hil
  have enx := C.1
  have es1 := C.2.1
  have eu := C.2.2.1
  have hL : Slot8 K := fun q hq => P.lay.slot8 q hq
  have w0 := prefix_writes ar hA P.tp P.np P.cT es1 eu
  have ag : ∀ b, SlotW K b → Aligned b → L.mem s2 b = L.mem s b := fun b hs hb => by
    obtain ⟨q, hq, hbq⟩ := hs
    exact P.slot_keep w0 hq hbq hb
  have ecap0 := ecap
  rw [cap_agree hL hsl ag, hcs] at ecap0
  have hcap' : cap = .CNode cp cr cg cgb := (ok_inj_ff ecap0).symm
  subst hcap'
  have M := invCM_hmid (Locks := Locks) hA P h0 info nx s1 s2 a1 emi enx es1 eu
  have hctR : IoRS (st := st) K Locks s (L.nodeAt s2 (L.cpu s2) layout.node.CUR_THREAD) := by
    rw [M.c, nodeAt_of_ksb M.k]
    exact (P.nd (Locks := Locks) layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD])
      (by simp [layout.node.CUR_THREAD])).1
  have edec : ∀ m : machine.Store S, sched.cur_thread m s2 = sched.cur_thread st s2 →
      decCNG m ar s2 a1 fl4_abi.label.CNodeDelete length p.slot (.CNode cp cr cg cgb) true true true false buf
        p.extra = ok (.Err (.Sys .TruncatedMessage), s2, a1) := by
    intro m hm
    unfold decCNG
    rw [hm, cur_thread_ok]
    simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
    exact cnode_decode_trunc ar m hlen'
  unfold invCMRest at h ⊢
  rw [hlbl] at h ⊢
  refine once_gstep (R0 := IoRS (st := st) K Locks s) (W0 := IoWS (st := st) K Locks s)
    (fun q hq => ⟨ioRS_cm hq, hq.2.1⟩) (fun q hq => P.ioWS_nu hq) (R.decCNG_nz _ _ _ _ _ _ _ _ _ _) h
    (fun r h1 => ?_) (fun r h1 hk Wd1 _ => ?_)
  · rw [R.decCNG_eq] at h1 ⊢
    rw [edec _ (sched.cur_thread.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s)
      (IoWS (st := st) K Locks s)) s2 hctR)]
    rw [edec st rfl] at h1
    exact h1
  rw [R.decCNG_eq] at h1
  obtain ⟨r0, er0, rfl⟩ := bind_shape h1
  rw [edec st rfl] at er0
  obtain rfl := ok_inj_ff er0
  dsimp only at hk ⊢
  unfold R.invPostG at hk ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind, SProg.blk] at hk ⊢
  exact invU_replyOnce P M (fun x5 Wd' T' er hk' =>
    invU_tailOnce hA P hcs hsl (invBufJ8_of hJ) C ecap hlen' er hk' Wd' T') hk Wd1

end rest

/-! ## `InvURoTrW` and the paths -/

section ro
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}
variable {A : Type}

/-- (invj gen 2) **`InvURoTrW` discharged** for the tree `R.invBodyG number p` at `Pre := SlJAt K ∧ InvQF`: `Once` at
the entry (`invU_entOnce` + `invU_decOnce`), carried to the alternatives by `once_agreeJ` over the accepted run on
`guard st (InvCMRS s) (InvCMWS s)` (`invUAccW_of2` + `invBlkUW2_of8`). No premise beyond `hA`, [P] `hm`. -/
theorem invURoTrW_of {ar : machine.Arch A} (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) {number : I64}
    {p : localinv.Plan} (K : KLayout) (m : U64 → U64) :
    InvURoTrW st ar number p K Locks m (R.invBodyG number p)
      (fun s => SlJAt (L := L) K s ∧ InvQF st Cs Ω Sg Ac Locks p K m s) := by
  intro s s' a r hE hL hac Al _
  have hacc : InvUAccW st ar number p K Locks (fun s => SlJAt (L := L) K s ∧ InvQF st Cs Ω Sg Ac Locks p K m s) :=
    invUAccW_of2 hA (fun _ h => h.2.1.1.1)
      (fun s h => invSeen_of (fun K _ s hJ _ => hz_of K s hJ) K m s h.1 h.2)
      (fun s h => invPs_of K m s h.1 h.2)
      (invBlkUW2_of8 hA (invVsJ_of (fun _ h => h.1)) (invCdtJ_of (fun _ h => h.1)) (hz_of K)
        (fun s hJ _ => invBufJ8_of hJ))
  have hSC := invSlotCNK_of (Q := InvQF st Cs Ω Sg Ac Locks p) (fun _ _ _ _ hq => hq) K m
  have hp := inv_isProgOn (Locks := Locks) (m0 := m) hA
    (P := fun s => SlJAt (L := L) K s ∧ InvQF st Cs Ω Sg Ac Locks p K m s) (fun _ h => h.2.1.1.1) hSC
    (inv_isProg S number p)
  obtain ⟨s1, a1, h0⟩ := hac
  have hg := hacc s a s1 a1 hE h0
  rw [inv_hp hp (Narrow.guard _ _ _) (AltOf.pre hE) a] at hg
  have h0' : interp st ar (R.invBodyG number p) s a = ok (true, s1, a1) := by
    rw [← inv_hp hp (Narrow.self st) (AltOf.pre hE) a]; exact h0
  have hent := invU_entOnce (Locks := Locks) hA
    (P := fun s => (SlJAt (L := L) K s ∧ InvQF st Cs Ω Sg Ac Locks p K m s) ∧ ¬ InvLen st s)
    (fun _ h => h.1.2.1.1.1) (fun s h => invSeen_of (fun K _ s hJ _ => hz_of K s hJ) K m s h.1.1 h.1.2)
    (fun s h => invPs_of K m s h.1.1 h.1.2) (invU_decOnce (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) hA)
    s a _ ⟨hE, hL⟩ ⟨s1, a1, h0⟩ h0'
  exact once_agreeJ hm (fun w hw => hw.1) (fun w hw => hw.1) _ (inv_noZero number p) s s' a _ ∅ ∅ Al.ksb Al.cpu
    Al.masks Al.read hg hent

end ro

section paths
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}
variable {A : Type}

/-- (invj gen 2) **`inv_pathsKF3` with `hIw` from `ioPre_wr_hIw`** (the `length ≥ 2` path, `Q := InvQL`). Premises:
`hA`, [P] `hm`, [P] `hCs`, [P] `hlk`. -/
noncomputable def inv_pathsKF4 (ar : machine.Arch A) (hA : P0.ArchTotal ar) (number : I64) (p : localinv.Plan)
    (hm : E2E.MasksWr st) (hCs : ∀ c ∈ Cs, c.val < 64)
    (hlk : ∀ K s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s) :
    E2E.Paths Unit :=
  inv_pathsKF3 (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (Locks := Locks) ar hA number p hm
    (ioPre_wr_hIw (Ω := Ω) (Sg := Sg) (Ac := Ac) hCs) hlk

end paths

end Fl4Proofs.P2.PathObl
