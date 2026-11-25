/-
# P2: the accepted VM-fault local path on the guarded store (line p2e, VM paths)

`syscall.handle_vm_fault_local.guard_acc`: an accepted run of the VM-fault
local path (`true`) on any store `gS` answering as `st` on the words it reads (`GRd gS st R`)
and writes (`GWr gS st W`), with the three `STATE` writes whose values matter a hypothesis of
their own (`SWr`), ends exactly as the real run (`PathObl.guard st R W` for `acc`, p2sl's checked
store `gd` for `move`). The run is
P1's decomposition (`P1/FastVm.lean`, `vm_fault_acc`): the prefix
(`update_timestamp`, the budget check), the fast path's checks
(`FaultChecks`), the writes up to the handler `Running` (`vmPre14`) and
`faultTail3` (the handler's SC, its scheduler links, `switch_to`).

* `fastFaultG_checks`: on any store, passing checks make the fast path its
  tail `faultTailG`; `FaultChecks.guard`: the checks pass on the guarded store
  when they read inside `R`;
* `faultTailG_split`: `faultTailG` is `vmPre14` then `faultTail3`;
  `vmPre14.guard`: the guarded `vmPre14` is the real one (`set_fault`, the
  dequeue, the fault message, `reply_push`'s words; `VmPreRW`);
* `faultTail3.guard`: the tail, given `unblock_check` and `switch_to` agree on
  the real run's states;
* `syscall.handle_vm_fault_local.guard_acc`: the whole path from these
  (`VmMid`: the facts after the prefix).

The endpoint and `sc_sporadic` leaves are p2sl's (`P2/AccessFastFault.lean`).
Generic over the Arch instance. Premises: none (the hypotheses are the
run-relative sets, discharged in the VM-fault obligation).
-/
import Fl4Proofs.P2.AccessIoPath
import Fl4Proofs.P2.AccessFastFault
import Fl4Proofs.P2.AccessVm
import Fl4Proofs.P1.FastVm
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts

/-! ## Passing checks, on any store -/

section
variable {S : Type}

/-- **On any store, passing checks make the fault fast path its tail.** -/
theorem fastFaultG_checks {A : Type} (m : machine.Store S) (ar : machine.Arch A) {s : S} {a : A}
    {t : obj.Tcb} {f : error.Fault} {ty ptr badge dest r : U64} (C : FaultChecks m s t ptr badge dest r) :
    fastFaultG m ar s a t f ty = faultTailG m ar s a t f ty ptr badge dest r := by
  obtain ⟨hact, ⟨sl, x, y, g, gr, hsl, hcap, hg⟩, hep, hhd, hrp, hr0, hhere, ⟨d, p, hd, hp, hhi⟩⟩ := C
  unfold fastFaultG
  rw [hact]; simp only [bind_ok, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rw [hsl]; simp only [bind_ok]
  rw [hcap]; simp only [bind_ok]
  cases g <;> cases gr <;> simp only [Bool.false_eq_true, or_self] at hg
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hep]; simp only [bind_ok, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    rw [hhd]; simp only [bind_ok]
    rw [hrp]; simp only [bind_ok, if_neg hr0]
    rw [hhere]; simp only [bind_ok, ↓reduceIte]
    rw [hd]; simp only [bind_ok]
    rw [hp]; simp only [bind_ok]
    simp only [hhi, bind_ok, ↓reduceIte]
    rfl

end

section
variable {S : Type} {st : machine.Store S} {R W : U64 → Prop} {gS : machine.Store S} [GRd gS st R] [GWr gS st W]
  [L : LawfulStore st]

/-! ## Leaf lemmas -/

/-- The four words `set_fault` writes for a fault. -/
def FaultWr (W : U64 → Prop) (t : U64) : Prop :=
  W (faultA t) ∧ W (core.num.U64.wrapping_add t 3384#u64) ∧ W (core.num.U64.wrapping_add t 3392#u64) ∧
    W (core.num.U64.wrapping_add t 3400#u64)

theorem faults.set_fault.guard_vm (s : S) (t : obj.Tcb) (w0 w1 : U64) (ins : Bool) (h : FaultWr W t) :
    faults.set_fault gS s t (error.Fault.VmFault w0 w1 ins) =
      faults.set_fault st s t (error.Fault.VmFault w0 w1 ins) := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  unfold faults.set_fault
  cases ins <;> simp only [Bool.false_eq_true, ↓reduceIte, bind_ok]
  all_goals
    simp only [uncurry_apply_pair]
    rw [obj.Tcb.set_fault_type.guard (gS := gS) t s _ h0]
    refine bind_guard_congr rfl (fun s2 _ => ?_)
    rw [obj.Tcb.set_fault_w0.guard (gS := gS) t s2 _ h1]
    refine bind_guard_congr rfl (fun s3 _ => ?_)
    rw [obj.Tcb.set_fault_w1.guard (gS := gS) t s3 _ h2]
    refine bind_guard_congr rfl (fun s4 _ => ?_)
    rw [obj.Tcb.set_fault_w2.guard (gS := gS) t s4 _ h3]

theorem msg.set_mr.guard_reg (s : S) (t : obj.Tcb) (buf i v : U64) (hi : i < msg.N_MSG_REGISTERS)
    (h : ∀ r, msg.msg_register i = ok r → W (regA t r)) :
    msg.set_mr gS s t buf i v = msg.set_mr st s t buf i v := by
  unfold msg.set_mr
  simp only [if_pos hi]
  refine bind_guard_congr rfl (fun r hr => ?_)
  rw [obj.Tcb.set_reg.guard (gS := gS) t s r v (h r hr)]

/-- The words `set_mrs_fault` reads and writes for a VM fault from `snd` to
`rcv`. -/
structure MrsVm (R W : U64 → Prop) (snd rcv : U64) : Prop where
  ft : R (core.num.U64.wrapping_add snd 3376#u64)
  w0 : R (core.num.U64.wrapping_add snd 3384#u64)
  w1 : R (core.num.U64.wrapping_add snd 3392#u64)
  w2 : R (core.num.U64.wrapping_add snd 3400#u64)
  ip : R (regA snd layout.reg.FAULT_IP)
  mr : ∀ i : U64, i.val < 4 → ∀ r, msg.msg_register i = ok r → W (regA rcv r)

theorem n_msg_lt {i : U64} (h : i.val < 4) : i < msg.N_MSG_REGISTERS := by
  rw [n_msg_regs]; scalar_tac

theorem faults.set_mrs_fault.guard_vm {A : Type} (ar : machine.Arch A) (s : S) (a : A) (snd rcv buf : U64)
    (hty : obj.Tcb.fault_type st snd s = ok fl4_abi.consts.fault.VMFault) (h : MrsVm R W snd rcv) :
    faults.set_mrs_fault gS ar s a snd rcv buf = faults.set_mrs_fault st ar s a snd rcv buf := by
  unfold faults.set_mrs_fault
  rw [obj.Tcb.fault_type.guard (gS := gS) snd s h.ft, hty]
  simp only [bind_ok]
  rw [obj.Tcb.fault_w0.guard (gS := gS) snd s h.w0]
  refine bind_guard_congr rfl (fun w0 _ => ?_)
  rw [obj.Tcb.fault_w1.guard (gS := gS) snd s h.w1]
  refine bind_guard_congr rfl (fun w1 _ => ?_)
  rw [obj.Tcb.fault_w2.guard (gS := gS) snd s h.w2]
  refine bind_guard_congr rfl (fun w2 _ => ?_)
  rw [obj.Tcb.reg.guard (gS := gS) snd s _ h.ip]
  refine bind_guard_congr rfl (fun pc _ => ?_)
  have e1 : fl4_abi.consts.fault.VMFault ≠ fl4_abi.consts.fault.CapFault := by
    simp [fl4_abi.consts.fault.VMFault, fl4_abi.consts.fault.CapFault]
  have e2 : fl4_abi.consts.fault.VMFault ≠ fl4_abi.consts.fault.UnknownSyscall := by
    simp [fl4_abi.consts.fault.VMFault, fl4_abi.consts.fault.UnknownSyscall]
  have e3 : fl4_abi.consts.fault.VMFault ≠ fl4_abi.consts.fault.UserException := by
    simp [fl4_abi.consts.fault.VMFault, fl4_abi.consts.fault.UserException]
  have e4 : fl4_abi.consts.fault.VMFault ≠ fl4_abi.consts.fault.Timeout := by
    simp [fl4_abi.consts.fault.VMFault, fl4_abi.consts.fault.Timeout]
  have e5 : fl4_abi.consts.fault.VMFault ≠ fl4_abi.consts.fault.DebugException := by
    simp [fl4_abi.consts.fault.VMFault, fl4_abi.consts.fault.DebugException]
  simp only [if_neg e1, if_neg e2, if_neg e3, if_neg e4, if_neg e5, ↓reduceIte]
  rw [msg.set_mr.guard_reg (gS := gS) s rcv buf 0#u64 pc (n_msg_lt (by decide)) (h.mr 0#u64 (by decide))]
  refine bind_guard_congr rfl (fun x1 _ => ?_)
  obtain ⟨_, s1⟩ := x1
  simp only [uncurry_apply_pair]
  rw [msg.set_mr.guard_reg (gS := gS) s1 rcv buf 1#u64 w0 (n_msg_lt (by decide)) (h.mr 1#u64 (by decide))]
  refine bind_guard_congr rfl (fun x2 _ => ?_)
  obtain ⟨_, s2⟩ := x2
  simp only [uncurry_apply_pair]
  rw [msg.set_mr.guard_reg (gS := gS) s2 rcv buf 2#u64 w2 (n_msg_lt (by decide)) (h.mr 2#u64 (by decide))]
  refine bind_guard_congr rfl (fun x3 _ => ?_)
  obtain ⟨_, s3⟩ := x3
  simp only [uncurry_apply_pair]
  rw [msg.set_mr.guard_reg (gS := gS) s3 rcv buf 3#u64 w1 (n_msg_lt (by decide)) (h.mr 3#u64 (by decide))]

/-! ## The checks -/

/-- **The fast path's checks on the guarded store**, from the real checks and
the words they read. -/
theorem FaultChecks.guard {s : S} {t : obj.Tcb} {ptr badge dest r : U64}
    (C : FaultChecks st s t ptr badge dest r)
    (hact : R (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hsl : ∀ sl, obj.Tcb.slot t layout.tcb.SLOT_FAULT_HANDLER = ok sl → R sl ∧ R (core.num.U64.wrapping_add sl 8#u64))
    (hts : R (core.num.U64.wrapping_add ptr layout.ep.TAIL_STATE))
    (hhd : R (core.num.U64.wrapping_add ptr layout.ep.HEAD))
    (hrp : R (core.num.U64.wrapping_add dest 3360#u64))
    (hhere : fastpath.schedulable_here gS s dest = fastpath.schedulable_here st s dest)
    (hcd : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN))
    (hpr : R (core.num.U64.wrapping_add dest 3448#u64))
    (hbm : RdBitmap (L := L) R s) :
    FaultChecks gS s t ptr badge dest r := by
  obtain ⟨hA, ⟨sl, x, y, g, gr, hS, hcap, hg⟩, hep, hh, hrep, hr0, hhe, ⟨d, p, hd, hp, hhi⟩⟩ := C
  refine ⟨?_, ⟨sl, x, y, g, gr, hS, ?_, hg⟩, ?_, ?_, ?_, hr0, ?_, ⟨d, p, ?_, ?_, ?_⟩⟩
  · rw [sched.action.guard (gS := gS) s hact]; exact hA
  · rw [obj.Slot.cap.guard (gS := gS) sl s (hsl sl hS).1 (hsl sl hS).2]; exact hcap
  · rw [obj.Ep.state.guard (gS := gS) ptr s hts]; exact hep
  · rw [obj.Ep.head.guard (gS := gS) ptr s hhd]; exact hh
  · rw [obj.Tcb.reply_obj.guard (gS := gS) dest s hrp]; exact hrep
  · rw [hhere]; exact hhe
  · rw [sched.cur_domain.guard (gS := gS) s hcd]; exact hd
  · rw [obj.Tcb.prio.guard (gS := gS) dest s hpr]; exact hp
  · rw [sched.is_highest_prio.guard (gS := gS) s d p hbm]; exact hhi

/-! ## The writes up to the handler running -/

/-- `faultTailG` up to the handler made `Running` (the state `faultTail3`
starts from). -/
def vmPre14 {A : Type} (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A) (t : obj.Tcb)
    (f : error.Fault) (ty ptr badge i2 i3 : U64) : Result S := do
  let s2 ← faults.set_fault m s t f
  let tail ← obj.Ep.tail m ptr s2
  let s3 ←
    if tail = i2
    then obj.Ep.set_queue m ptr s2 0#u64 0#u64 obj.EP_IDLE
    else
      do
      let i6 ← obj.Tcb.ep_next m i2 s2
      let s4 ← obj.Tcb.set_ep_prev m i6 s2 0#u64
      obj.Ep.set_queue m ptr s4 i6 tail obj.EP_RECV
  let s4 ← obj.Tcb.set_ep_next m i2 s3 0#u64
  let s5 ← obj.Tcb.set_ep_prev m i2 s4 0#u64
  let recv_buf ← msg.lookup_ipc_buffer m s5 true i2
  let (sent, s6) ← faults.set_mrs_fault m ar s5 a t i2 recv_buf
  let mi ← msginfo.MessageInfo.new ty 0#u64 0#u64 sent
  let s7 ← msg.set_msg_info m s6 i2 mi
  let s8 ← obj.Tcb.set_reg m i2 s7 layout.reg.BADGE badge
  let s9 ← obj.Reply.set_tcb m i3 s8 0#u64
  let s10 ← obj.Tcb.set_state m i2 s9 sched.TS_INACTIVE
  let s11 ← obj.Reply.set_tcb m i3 s10 t
  let s12 ← obj.Tcb.set_state m t s11 sched.TS_BLOCKED_ON_REPLY
  let s13 ← obj.Tcb.set_reply_obj m t s12 i3
  obj.Tcb.set_state m i2 s13 sched.TS_RUNNING

theorem faultTailG_split {A : Type} (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A) (t : obj.Tcb)
    (f : error.Fault) (ty ptr badge i2 i3 : U64) :
    faultTailG m ar s a t f ty ptr badge i2 i3 =
      (do let s14 ← vmPre14 m ar s a t f ty ptr badge i2 i3; faultTail3 m ar s14 a i2) := by
  unfold faultTailG vmPre14 faultTail3
  simp only [Std.bind_assoc]
  iterate 7 (congr 1; funext _)
  rename_i x
  obtain ⟨sent, s6⟩ := x
  simp only [uncurry_apply_pair, Std.bind_assoc]

/-- The words `vmPre14` reads and writes (`t` the faulting thread, `ptr` the
endpoint, `dest` its head, `r` the handler's reply object). The link `EP_PREV`
of the thread after `dest`, and the fault type `set_mrs_fault` reads, are
stated at the real run's states. -/
structure VmPreRW {A : Type} (R W : U64 → Prop) (ar : machine.Arch A) (s : S) (a : A) (t : obj.Tcb)
    (f : error.Fault) (ptr dest r : U64) : Prop where
  fw : FaultWr W t
  ts : R (core.num.U64.wrapping_add ptr layout.ep.TAIL_STATE)
  wh : W (core.num.U64.wrapping_add ptr layout.ep.HEAD)
  wt : W (core.num.U64.wrapping_add ptr layout.ep.TAIL_STATE)
  nx : R (core.num.U64.wrapping_add dest 3496#u64)
  pv : ∀ s2 tl i6, faults.set_fault st s t f = ok s2 → obj.Ep.tail st ptr s2 = ok tl → tl ≠ dest →
    obj.Tcb.ep_next st dest s2 = ok i6 → W (core.num.U64.wrapping_add i6 3504#u64)
  dn : W (core.num.U64.wrapping_add dest 3496#u64)
  dp : W (core.num.U64.wrapping_add dest 3504#u64)
  ib : R (core.num.U64.wrapping_add dest 3512#u64)
  bs : ∃ sl, obj.Tcb.slot dest layout.tcb.SLOT_BUFFER = ok sl ∧ R sl ∧ R (core.num.U64.wrapping_add sl 8#u64)
  ty : ∀ s2 tl s3 s4 s5, faults.set_fault st s t f = ok s2 → obj.Ep.tail st ptr s2 = ok tl →
    (if tl = dest then obj.Ep.set_queue st ptr s2 0#u64 0#u64 obj.EP_IDLE
     else do
      let i6 ← obj.Tcb.ep_next st dest s2
      let s4 ← obj.Tcb.set_ep_prev st i6 s2 0#u64
      obj.Ep.set_queue st ptr s4 i6 tl obj.EP_RECV) = ok s3 →
    obj.Tcb.set_ep_next st dest s3 0#u64 = ok s4 → obj.Tcb.set_ep_prev st dest s4 0#u64 = ok s5 →
    obj.Tcb.fault_type st t s5 = ok fl4_abi.consts.fault.VMFault
  mrs : MrsVm R W t dest
  mi : W (regA dest layout.reg.MSG_INFO)
  bd : W (regA dest layout.reg.BADGE)
  rt : W (core.num.U64.wrapping_add r layout.reply.TCB)
  ro : W (core.num.U64.wrapping_add t 3360#u64)

/-- **`vmPre14` on the guarded store is the real one.** -/
theorem vmPre14.guard {A : Type} (ar : machine.Arch A) (s : S) (a : A) (t : obj.Tcb) (w0 w1 : U64) (ins : Bool)
    (ty ptr badge dest r : U64) (H : VmPreRW (st := st) R W ar s a t (error.Fault.VmFault w0 w1 ins) ptr dest r)
    (hsd : ∀ v, (v = sched.TS_INACTIVE ∨ v = sched.TS_RUNNING) → SWr gS st dest v)
    (hst : SWr gS st t sched.TS_BLOCKED_ON_REPLY) :
    vmPre14 gS ar s a t (error.Fault.VmFault w0 w1 ins) ty ptr badge dest r =
      vmPre14 st ar s a t (error.Fault.VmFault w0 w1 ins) ty ptr badge dest r := by
  unfold vmPre14
  rw [faults.set_fault.guard_vm (gS := gS) s t w0 w1 ins H.fw]
  refine bind_guard_congr rfl (fun s2 e2 => ?_)
  rw [obj.Ep.tail.guard (gS := gS) ptr s2 H.ts]
  refine bind_guard_congr rfl (fun tl etl => ?_)
  refine bind_guard_congr ?_ (fun s3 e3 => ?_)
  · by_cases hc : tl = dest
    · rw [if_pos hc, if_pos hc]; exact obj.Ep.set_queue.guard (gS := gS) ptr s2 _ _ _ H.wh H.wt
    · rw [if_neg hc, if_neg hc]
      rw [obj.Tcb.ep_next.guard (gS := gS) dest s2 H.nx]
      refine bind_guard_congr rfl (fun i6 e6 => ?_)
      rw [obj.Tcb.set_ep_prev.guard (gS := gS) i6 s2 _ (H.pv s2 tl i6 e2 etl hc e6)]
      refine bind_guard_congr rfl (fun s4 _ => ?_)
      exact obj.Ep.set_queue.guard (gS := gS) ptr s4 _ _ _ H.wh H.wt
  rw [obj.Tcb.set_ep_next.guard (gS := gS) dest s3 _ H.dn]
  refine bind_guard_congr rfl (fun s4 e4 => ?_)
  rw [obj.Tcb.set_ep_prev.guard (gS := gS) dest s4 _ H.dp]
  refine bind_guard_congr rfl (fun s5 e5 => ?_)
  obtain ⟨sl, hsl, hR0, hR8⟩ := H.bs
  rw [msg.lookup_ipc_buffer.guard (gS := gS) s5 true dest hsl H.ib hR0 hR8]
  refine bind_guard_congr rfl (fun rb _ => ?_)
  rw [faults.set_mrs_fault.guard_vm (gS := gS) ar s5 a t dest rb (H.ty s2 tl s3 s4 s5 e2 etl e3 e4 e5) H.mrs]
  refine bind_guard_congr rfl (fun x6 _ => ?_)
  obtain ⟨sent, s6⟩ := x6
  simp only [uncurry_apply_pair]
  refine bind_guard_congr rfl (fun mi _ => ?_)
  rw [msg.set_msg_info.guard (gS := gS) s6 dest mi H.mi]
  refine bind_guard_congr rfl (fun s7 _ => ?_)
  rw [obj.Tcb.set_reg.guard (gS := gS) dest s7 _ _ H.bd]
  refine bind_guard_congr rfl (fun s8 _ => ?_)
  rw [obj.Reply.set_tcb.guard (gS := gS) r s8 _ H.rt]
  refine bind_guard_congr rfl (fun s9 _ => ?_)
  rw [obj.Tcb.set_state.guardV dest s9 _ (hsd _ (Or.inl rfl))]
  refine bind_guard_congr rfl (fun s10 _ => ?_)
  rw [obj.Reply.set_tcb.guard (gS := gS) r s10 _ H.rt]
  refine bind_guard_congr rfl (fun s11 _ => ?_)
  rw [obj.Tcb.set_state.guardV t s11 _ hst]
  refine bind_guard_congr rfl (fun s12 _ => ?_)
  rw [obj.Tcb.set_reply_obj.guard (gS := gS) t s12 _ H.ro]
  refine bind_guard_congr rfl (fun s13 _ => ?_)
  rw [obj.Tcb.set_state.guardV dest s13 _ (hsd _ (Or.inr rfl))]

/-! ## From the handler running -/

/-- **`faultTail3` on the guarded store** (transfer of an accepted run), given
`unblock_check` and `switch_to` agree on the real run's states. -/
theorem faultTail3.guard {A : Type} (ar : machine.Arch A) {s14 s' : S} {a a' : A} {dest : U64}
    (hsc : R (core.num.U64.wrapping_add dest 3464#u64))
    (hsp : ∀ dsc, obj.Tcb.sc st dest s14 = ok dsc → dsc ≠ 0#u64 →
      R (core.num.U64.wrapping_add dsc layout.sc.SPORADIC))
    (hcs : R (L.nodeAt s14 (L.cpu s14) layout.node.CUR_SC))
    (hub : ∀ dsc, obj.Tcb.sc st dest s14 = ok dsc → sporadic.sc_sporadic st s14 dsc = ok true →
      sporadic.unblock_check gS s14 dsc = sporadic.unblock_check st s14 dsc)
    (hsn : W (core.num.U64.wrapping_add dest 3480#u64)) (hspv : W (core.num.U64.wrapping_add dest 3488#u64))
    (hsw : ∀ dsc b2 s15 s16 s17, obj.Tcb.sc st dest s14 = ok dsc → sporadic.sc_sporadic st s14 dsc = ok b2 →
      (if b2 then (do
        let c ← sched.cur_sc st s14
        let b3 ← core.cmp.PartialEq.ne.trait_default obj.Sc.Insts.CoreCmpPartialEqSc dsc c
        if b3 then sporadic.unblock_check st s14 dsc else ok s14) else ok s14) = ok s15 →
      obj.Tcb.set_sched_next st dest s15 0#u64 = ok s16 → obj.Tcb.set_sched_prev st dest s16 0#u64 = ok s17 →
      fastpath.switch_to gS ar s17 a dest = fastpath.switch_to st ar s17 a dest)
    (h : faultTail3 st ar s14 a dest = ok (true, s', a')) :
    faultTail3 gS ar s14 a dest = ok (true, s', a') := by
  unfold faultTail3 at h ⊢
  revert h
  refine tr_bind (fun x hx _ => by rw [obj.Tcb.sc.guard (gS := gS) dest s14 hsc]; exact hx) (fun dsc edsc => ?_)
  refine tr_bind (fun x hx _ => by rw [sporadic.sc_sporadic.guard (gS := gS) s14 dsc (hsp dsc edsc)]; exact hx)
    (fun b2 eb2 => ?_)
  refine tr_bind (fun s15 h15 _ => ?_) (fun s15 e15 => ?_)
  · by_cases hb : b2 = true
    · subst hb
      rw [if_pos rfl] at h15 ⊢
      rw [sched.cur_sc.guard (gS := gS) s14 hcs]
      revert h15
      refine tr_bind_same (fun c _ => ?_)
      refine tr_bind_same (fun b3 _ => ?_)
      exact tr_ite (fun _ h => by rw [hub dsc edsc eb2]; exact h) (fun _ h => h)
    · rw [if_neg hb] at h15 ⊢; exact h15
  · refine tr_bind (fun x hx _ => by rw [obj.Tcb.set_sched_next.guard (gS := gS) dest s15 _ hsn]; exact hx) (fun s16 e16 => ?_)
    refine tr_bind (fun x hx _ => by rw [obj.Tcb.set_sched_prev.guard (gS := gS) dest s16 _ hspv]; exact hx)
      (fun s17 e17 => ?_)
    exact tr_bind (fun x hx _ => by rw [hsw dsc b2 s15 s16 s17 edsc eb2 e15 e16 e17]; exact hx) (fun _ _ h => h)

/-! ## The path -/

/-- The facts after the prefix that the guarded fast path needs: its checks
pass on the guarded store, `vmPre14` agrees, and so does the accepted tail. -/
structure VmMid {A : Type} (gS : machine.Store S) (ar : machine.Arch A) (s1 : S) (a1 : A) (t : obj.Tcb)
    (f : error.Fault) (ptr badge dest r : U64) (s' : S) (a' : A) : Prop where
  chk : FaultChecks gS s1 t ptr badge dest r
  pre : vmPre14 gS ar s1 a1 t f fl4_abi.consts.fault.VMFault ptr badge dest r =
    vmPre14 st ar s1 a1 t f fl4_abi.consts.fault.VMFault ptr badge dest r
  tail : ∀ s14, vmPre14 st ar s1 a1 t f fl4_abi.consts.fault.VMFault ptr badge dest r = ok s14 →
    faultTail3 st ar s14 a1 dest = ok (true, s', a') → faultTail3 gS ar s14 a1 dest = ok (true, s', a')

theorem fastpath_vm.vm_fault.guard_acc {A : Type} (ar : machine.Arch A) {s s' : S} {a a' : A} {t : obj.Tcb}
    {f : error.Fault}
    (hmid : ∀ ptr badge dest r, FaultChecks st s t ptr badge dest r →
      VmMid (st := st) gS ar s a t f ptr badge dest r s' a')
    (h : fastpath_vm.vm_fault st ar s a t f = ok (true, s', a')) :
    fastpath_vm.vm_fault gS ar s a t f = ok (true, s', a') := by
  obtain ⟨ptr, badge, dest, r, C, hT⟩ := vm_fault_acc st ar h
  have M := hmid ptr badge dest r C
  show fastFaultG gS ar s a t f fl4_abi.consts.fault.VMFault = _
  rw [fastFaultG_checks _ ar M.chk, faultTailG_split, M.pre]
  rw [faultTailG_split] at hT
  obtain ⟨s14, e14, h3⟩ := bind_eq_ok hT
  rw [e14]; simp only [bind_ok]
  exact M.tail s14 e14 h3

/-- **The accepted VM-fault local path on the guarded store** ends exactly as
the real run: the prefix's node words and the current SC's head refill
(`update_timestamp`, `sufficient`), then `VmMid` after it. -/
theorem syscall.handle_vm_fault_local.guard_acc {A : Type} (ar : machine.Arch A) {s s' : S} {a a' : A}
    {addr code : U64}
    (hct : R (ctA (L := L) s)) (hwct : W (ctA (L := L) s)) (hcn : R (cnA (L := L) s)) (hwcn : W (cnA (L := L) s))
    (hcsc : ∀ s1 a1, sched.update_timestamp st ar s a = ok (s1, a1) →
      R (L.nodeAt s1 (L.cpu s1) layout.node.CUR_SC) ∧ R (L.nodeAt s1 (L.cpu s1) layout.node.CONSUMED) ∧
      R (L.nodeAt s1 (L.cpu s1) layout.node.CUR_THREAD))
    (hsuf : ∀ s1 a1 csc, sched.update_timestamp st ar s a = ok (s1, a1) → sched.cur_sc st s1 = ok csc →
      RdHead (L := L) R s1 csc)
    (hmid : ∀ s1 a1 t i2 f, sched.update_timestamp st ar s a = ok (s1, a1) → sched.cur_thread st s1 = ok t →
      vspace.vm_fault addr code (i2 != 0#u64) = ok f →
      ∀ ptr badge dest r, FaultChecks st s1 t ptr badge dest r →
        VmMid (st := st) gS ar s1 a1 t f ptr badge dest r s' a')
    (h : syscall.handle_vm_fault_local st ar s a addr code = ok (true, s', a')) :
    syscall.handle_vm_fault_local gS ar s a addr code = ok (true, s', a') := by
  unfold syscall.handle_vm_fault_local at h ⊢
  revert h
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  refine tr_bind (fun x hx _ => by rw [sched.update_timestamp.guard (gS := gS) ar s a hct hwct hcn hwcn]; exact hx)
    (fun x eu => ?_)
  obtain ⟨s1, a1⟩ := x
  simp only [uncurry_apply_pair]
  obtain ⟨h1, h2, h3⟩ := hcsc s1 a1 eu
  rw [sched.cur_sc.guard (gS := gS) s1 h1]
  refine tr_bind_same (fun csc ecsc => ?_)
  rw [sched.consumed.guard (gS := gS) s1 h2]
  refine tr_bind_same (fun u _ => ?_)
  rw [sporadic.sufficient.guard (gS := gS) ar s1 a1 csc u (hsuf s1 a1 csc eu ecsc)]
  refine tr_bind_same (fun b _ => ?_)
  refine tr_ite (fun _ => ?_) (fun _ h => h)
  rw [sched.cur_thread.guard (gS := gS) s1 h3]
  refine tr_bind_same (fun t et => ?_)
  refine tr_bind_same (fun _ _ => ?_)
  refine tr_bind_same (fun i2 _ => ?_)
  refine tr_bind_same (fun f ef => ?_)
  exact fastpath_vm.vm_fault.guard_acc (gS := gS) ar (fun ptr badge dest r C => hmid s1 a1 t i2 f eu et ef ptr badge dest r C)

end

end Fl4Proofs.P2.PathObl
