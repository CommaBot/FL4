/-
# P2 (line p3mc, gen 13): the VM ReplyRecv body at a store state whose receiver is another core's

At core `c`'s view every thread looks homed on `c`; the real memory may say that the receiver `u` (the reply object's
`TCB`) is homed on another core. U9's certificate (`ViewSafeReal.safe_tr_of_states`) runs at a store state `x`
carrying the real values, which agrees with the view's entry only on a read set. This module gives the run at such an
`x` from facts stated at `x` itself, for **any** read set:

* `RrDR0`: `RrDR` (P2/AccessVmRRD) without its receiver clauses; `RrDR.to0`, `RrDR0.and`, `RrDR0.alt`, and
  **`RrDR.ofOff`** (the receiver's gate words in the set and its `AFFINITY` off the core give the whole `RrDR`);
* **`rr_fh_not_acc`**: if the receiver is off the core at `x`'s dispatch state, `x`'s run is not accepted
  (acceptance needs `schedulable_here u`, P1's `here_facts`);
* **`rr_fh_once`**: `RrOnce.rr_once_alt`'s walk at such an `x`, `Once` for any read set `Ro` holding the guard set:
  one read of `u`'s `STATE`, one of its `FAULT_TYPE`, then `schedulable_here u` answers `false` on `u`'s `AFFINITY`.

The declined run itself on a guarded store is `rr_local_guard_dec` (generic). No premise: every fact about the state
is a hypothesis. No existing statement changed.
-/
import Fl4Proofs.P2.RrOnce
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts
open Fl4Proofs.P2.OwnMap (KLayout fld own GateField TimerField GField RegionOK oAFFINITY)
open Fl4Proofs.P2.E2E (Once ReadOnce)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} {ar : machine.Arch A}

/-- **`RrDR` without the receiver's clauses.** -/
structure RrDR0 (R : U64 → Prop) (X : S) (t rptr ep : U64) : Prop where
  nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt X (L.cpu X) o)
  dt : R (core.num.U64.wrapping_add (L.ksb X) layout.ks.DOMAIN_TIME)
  cd : R (core.num.U64.wrapping_add (L.ksb X) layout.ks.CUR_DOMAIN)
  tm : L.mem X (tmA (L := L) X) ≠ 0#u64 → R (core.num.U64.wrapping_add (L.mem X (tmA (L := L) X)) 3528#u64)
  rh : L.mem X (rhA (L := L) X) ≠ 0#u64 → R (scA (L.mem X (rhA (L := L) X))) ∧
    RdHead (L := L) R X (L.mem X (scA (L.mem X (rhA (L := L) X))))
  tSt : R (stA t)
  tSc : R (scA t)
  tMx : L.mem X (scA t) ≠ 0#u64 → R (maxA (L.mem X (scA t)))
  tIq : R (inqA t)
  tMi : R (regA t layout.reg.MSG_INFO)
  tBn : R (boundA t)
  tPr : R (prioA t)
  ntf : L.mem X (boundA t) ≠ 0#u64 →
    R (core.num.U64.wrapping_add (L.mem X (boundA t)) layout.ntfn.TAIL_STATE) ∧
    R (core.num.U64.wrapping_add (L.mem X (boundA t)) layout.ntfn.SC)
  rRt : R (rTcbA rptr)
  rNx : R (rNextA rptr)
  eTS : R (epTSA ep)

theorem RrDR.to0 {R : U64 → Prop} {X : S} {t rptr ep : U64} (D : RrDR (L := L) R X t rptr ep) :
    RrDR0 (L := L) R X t rptr ep :=
  ⟨D.nd, D.dt, D.cd, D.tm, D.rh, D.tSt, D.tSc, D.tMx, D.tIq, D.tMi, D.tBn, D.tPr, D.ntf, D.rRt, D.rNx, D.eTS⟩

theorem RrDR0.and {R1 R2 : U64 → Prop} {X : S} {t rptr ep : U64} (D1 : RrDR0 (L := L) R1 X t rptr ep)
    (D2 : RrDR0 (L := L) R2 X t rptr ep) : RrDR0 (L := L) (fun b => R1 b ∧ R2 b) X t rptr ep where
  nd o h1 h2 := ⟨D1.nd o h1 h2, D2.nd o h1 h2⟩
  dt := ⟨D1.dt, D2.dt⟩
  cd := ⟨D1.cd, D2.cd⟩
  tm h := ⟨D1.tm h, D2.tm h⟩
  rh h := ⟨⟨(D1.rh h).1, (D2.rh h).1⟩, ⟨(D1.rh h).2.1, (D2.rh h).2.1⟩, ⟨(D1.rh h).2.2.1, (D2.rh h).2.2.1⟩,
    ⟨(D1.rh h).2.2.2, (D2.rh h).2.2.2⟩⟩
  tSt := ⟨D1.tSt, D2.tSt⟩
  tSc := ⟨D1.tSc, D2.tSc⟩
  tMx h := ⟨D1.tMx h, D2.tMx h⟩
  tIq := ⟨D1.tIq, D2.tIq⟩
  tMi := ⟨D1.tMi, D2.tMi⟩
  tBn := ⟨D1.tBn, D2.tBn⟩
  tPr := ⟨D1.tPr, D2.tPr⟩
  ntf h := ⟨⟨(D1.ntf h).1, (D2.ntf h).1⟩, ⟨(D1.ntf h).2, (D2.ntf h).2⟩⟩
  rRt := ⟨D1.rRt, D2.rRt⟩
  rNx := ⟨D1.rNx, D2.rNx⟩
  eTS := ⟨D1.eTS, D2.eTS⟩

/-- **`RrDR0` at a state agreeing on `R`.** -/
theorem RrDR0.alt {R R' : U64 → Prop} {X y : S} {t rptr ep : U64} (D : RrDR0 (L := L) R X t rptr ep)
    (G : Ag st R X y) (hRR : ∀ b, R b → R' b) : RrDR0 (L := L) R' y t rptr ep := by
  have etm : L.mem y (tmA (L := L) y) = L.mem X (tmA (L := L) X) := by
    show L.mem y (L.nodeAt y (L.cpu y) layout.node.TIMER_MIN) = L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN)
    rw [G.node]; exact G.m _ (D.nd _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]))
  have erh : L.mem y (rhA (L := L) y) = L.mem X (rhA (L := L) X) := by
    show L.mem y (L.nodeAt y (L.cpu y) layout.node.RELEASE_HEAD) =
      L.mem X (L.nodeAt X (L.cpu X) layout.node.RELEASE_HEAD)
    rw [G.node]; exact G.m _ (D.nd _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]))
  refine ⟨fun o ho h8 => by rw [G.node]; exact hRR _ (D.nd o ho h8), by rw [G.k]; exact hRR _ D.dt,
    by rw [G.k]; exact hRR _ D.cd, fun h0 => by rw [etm] at h0 ⊢; exact hRR _ (D.tm h0), fun h0 => ?_,
    hRR _ D.tSt, hRR _ D.tSc, fun h0 => ?_, hRR _ D.tIq, hRR _ D.tMi, hRR _ D.tBn, hRR _ D.tPr, fun h0 => ?_,
    hRR _ D.rRt, hRR _ D.rNx, hRR _ D.eTS⟩
  · rw [erh] at h0 ⊢
    obtain ⟨h1, h2⟩ := D.rh h0
    rw [G.m _ h1]
    have h3 := G.rdHead h2
    refine ⟨hRR _ h1, ?_⟩
    unfold RdHead at h3 ⊢
    exact ⟨hRR _ h3.1, hRR _ h3.2.1, hRR _ h3.2.2⟩
  · rw [G.m _ D.tSc] at h0 ⊢; exact hRR _ (D.tMx h0)
  · rw [G.m _ D.tBn] at h0 ⊢; exact ⟨hRR _ (D.ntf h0).1, hRR _ (D.ntf h0).2⟩

/-- **`RrDR` from `RrDR0` when the receiver is off the core** (its gate words in `R`). -/
theorem RrDR.ofOff {R : U64 → Prop} {X : S} {t rptr ep : U64} (D : RrDR0 (L := L) R X t rptr ep)
    (hG : ∀ u, L.mem X (rTcbA rptr) = u → u ≠ 0#u64 →
      R (scA u) ∧ R (affA u) ∧ R (core.num.U64.wrapping_add u 3432#u64) ∧ R (prioA u))
    (hoff : ∀ u, L.mem X (rTcbA rptr) = u → u ≠ 0#u64 → L.mem X (affA u) ≠ L.cpu X) :
    RrDR (L := L) R X t rptr ep :=
  ⟨D.nd, D.dt, D.cd, D.tm, D.rh, D.tSt, D.tSc, D.tMx, D.tIq, D.tMi, D.tBn, D.tPr, D.ntf, D.rRt, D.rNx, D.eTS, hG,
    fun u hu hu0 haff => absurd haff (hoff u hu hu0), fun u hu hu0 haff _ _ => absurd haff (hoff u hu hu0)⟩

/-- The receiver off the core at every dispatch state of `x`. -/
def RrOff (st : machine.Store S) [L : LawfulStore st] (ar : machine.Arch A) (x : S) (a : A) (rptr : U64) : Prop :=
  ∀ v X2 a2, sched.update_timestamp st ar (L.wr x (regA (L.curW x) layout.reg.FAULT_IP) v) a = ok (X2, a2) →
    ∀ u, L.mem X2 (rTcbA rptr) = u → u ≠ 0#u64 → L.mem X2 (affA u) ≠ L.cpu X2

set_option maxHeartbeats 1000000 in
/-- **A state whose receiver is off the core is not accepted** (module docstring). -/
theorem rr_fh_not_acc {x : S} {a : A} {rptr ep : U64} (hoff : RrOff st ar x a rptr) {z : S} {b : A}
    (h' : syscall.handle_reply_recv_vm_local st ar x a (rptr, ep) = ok (true, z, b)) : False := by
  unfold syscall.handle_reply_recv_vm_local at h'
  rw [cur_thread_ok] at h'
  simp only [bind_ok] at h'
  rw [if_neg vm_nd_ne] at h'
  obtain ⟨i, -, h'⟩ := bind_eq_ok h'
  obtain ⟨i1, -, h'⟩ := bind_eq_ok h'
  by_cases hf : (i1 != 0#u64) = true
  · rw [if_pos hf] at h'; exact Bool.false_ne_true (congrArg Prod.fst (ok_inj_ff h'))
  rw [if_neg hf] at h'
  obtain ⟨nx, -, h'⟩ := bind_eq_ok h'
  obtain ⟨v, -, h'⟩ := bind_eq_ok h'
  rw [set_reg_ok'] at h'
  simp only [bind_ok] at h'
  obtain ⟨⟨x2, a1'⟩, eu', h'⟩ := bind_eq_ok h'
  simp only [uncurry_apply_pair] at h'
  obtain ⟨csc', -, h'⟩ := bind_eq_ok h'
  obtain ⟨u', -, h'⟩ := bind_eq_ok h'
  obtain ⟨bb', -, h'⟩ := bind_eq_ok h'
  by_cases hb : bb' = true
  swap
  · rw [if_neg hb] at h'; exact Bool.false_ne_true (congrArg Prod.fst (ok_inj_ff h'))
  rw [if_pos hb] at h'
  obtain ⟨u0, usc0, C', -⟩ := reply_recv_vm_found_acc st ar h'
  have hu : L.mem x2 (rTcbA rptr) = u0 := by
    have e := C'.tcb
    rw [eq_of_spec_fd (obj.Reply.tcb.blk (L := L) x2 rptr)] at e; exact ok_inj_ff e
  have hu0 : u0 ≠ 0#u64 := by
    obtain ⟨b0, hb0, hb0'⟩ := C'.u0
    rw [is_null_ok] at hb0
    obtain rfl := ok_inj_ff hb0
    simpa using hb0'
  obtain ⟨bh, hbh, hbt⟩ := C'.here
  subst hbt
  exact hoff v x2 a1' eu' u0 hu hu0 (here_facts (L := L) hbh).aff

set_option maxHeartbeats 4000000 in
/-- **The run at a state whose receiver is off the core reads each racy word once** (module docstring). -/
theorem rr_fh_once {Rd Ro User : U64 → Prop} (hR0 : ∀ q, Rd q → Ro q ∧ ¬ User q) {x : S} {a : A} {rptr ep : U64}
    (nC : Rd (L.nodeAt x (L.cpu x) layout.node.CUR_THREAD)) (hct : Rd (ctA (L := L) x)) (hcn : Rd (cnA (L := L) x))
    (rF : Rd (regA (L.curW x) layout.reg.FAULT_IP)) (rNI : Rd (regA (L.curW x) layout.reg.NEXT_IP))
    (rFl : Rd (core.num.U64.wrapping_add (L.curW x) 3456#u64))
    (hmid : ∀ v X2 a2,
      sched.update_timestamp st ar (L.wr x (regA (L.curW x) layout.reg.FAULT_IP) v) a = ok (X2, a2) →
      (∀ o : U64, o.val < 4288 → o.val % 8 = 0 → Rd (L.nodeAt X2 (L.cpu X2) o)) ∧
        RdHead (L := L) Rd X2 (L.cscW X2) ∧ RrDR (L := L) Rd X2 (L.curW x) rptr ep ∧
        ∀ u, L.mem X2 (rTcbA rptr) = u → u ≠ 0#u64 → L.mem X2 (affA u) ≠ L.cpu X2)
    {r' : Bool × S × A}
    (h' : interp st ar (R.syscall.handle_reply_recv_vm_local (rptr, ep)) x a = ok r') :
    Once st ar Ro User ∅ ∅ (R.syscall.handle_reply_recv_vm_local (rptr, ep)) x a := by
  have hU : ∀ q, Rd q → ¬ User q := fun q hq => (hR0 q hq).2
  unfold R.syscall.handle_reply_recv_vm_local at h' ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret] at h' ⊢
  -- cur_thread
  refine once_step hR0 hU (R.sched.cur_thread_nz) h' (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
  · rw [R.sched.cur_thread_eq] at h1 ⊢
    rw [sched.cur_thread.guard (gS := PathObl.guard st (Rd) (Rd)) x
      nC]
    exact h1
  replace h2 := hk
  rw [R.sched.cur_thread_eq] at h1
  obtain ⟨t, et, rfl⟩ := bind_shape h1
  try dsimp only at h2 ⊢
  rw [cur_thread_ok] at et
  have et' : t = L.curW x := (ok_inj_ff et).symm
  subst et'
  by_cases hd : (layout.NUM_DOMAINS != 1#u64) = true
  · rw [if_pos hd]; simp only [Once]
  rw [if_neg hd] at h2 ⊢
  -- flags
  refine once_step hR0 hU (R.obj.Tcb.flags_nz _) h2 (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
  · rw [R.obj.Tcb.flags_eq] at h1 ⊢
    rw [obj.Tcb.flags.guard (gS := PathObl.guard st (Rd) (Rd))
      (L.curW x) x rFl]
    exact h1
  replace h2 := hk
  rw [R.obj.Tcb.flags_eq] at h1
  obtain ⟨i, -, rfl⟩ := bind_shape h1
  try dsimp only at h2 ⊢
  try simp only [SProg.sbind] at h2 ⊢
  split
  · simp only [Once]
  rename_i hi
  rw [if_neg hi] at h2
  -- `NEXT_IP`
  refine once_step hR0 hU (R.obj.Tcb.reg_nz _ _) h2 (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
  · rw [R.obj.Tcb.reg_eq] at h1 ⊢
    rw [obj.Tcb.reg.guard (gS := PathObl.guard st (Rd) (Rd))
      (L.curW x) x _ rNI]
    exact h1
  replace h2 := hk
  rw [R.obj.Tcb.reg_eq] at h1
  obtain ⟨nx, -, rfl⟩ := bind_shape h1
  try dsimp only at h2 ⊢
  try simp only [SProg.sbind] at h2 ⊢
  -- the `FAULT_IP` write
  refine once_step hR0 hU (R.obj.Tcb.set_reg_nz _ _ _) h2 (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
  · rw [R.obj.Tcb.set_reg_eq] at h1 ⊢
    rw [obj.Tcb.set_reg.guard (gS := PathObl.guard st (Rd) (Rd))
      (L.curW x) x _ _ rF]
    exact h1
  replace h2 := hk
  rw [R.obj.Tcb.set_reg_eq] at h1
  obtain ⟨x1, ex1, rfl⟩ := bind_shape h1
  try dsimp only at h2 ⊢
  rw [set_reg_ok'] at ex1
  obtain rfl := ok_inj_ff ex1
  -- update_timestamp
  refine once_step hR0 hU (R.sched.update_timestamp_nz) h2 (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
  · rw [R.sched.update_timestamp_eq] at h1 ⊢
    rw [sched.update_timestamp.guard (gS := PathObl.guard st (Rd)
      (Rd)) ar _ a (by rw [ctA_wr]; exact hct) (by rw [ctA_wr]; exact hct)
      (by rw [cnA_wr]; exact hcn) (by rw [cnA_wr]; exact hcn)]
    exact h1
  replace h2 := hk
  rw [R.sched.update_timestamp_eq] at h1
  obtain ⟨⟨X2, a2⟩, eu', rfl⟩ := bind_shape h1
  try dsimp only at h2 ⊢
  obtain ⟨nd2, hs2, D, hoff⟩ := hmid _ X2 a2 eu'
  -- cur_sc
  refine once_step hR0 hU (R.sched.cur_sc_nz) h2 (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
  · rw [R.sched.cur_sc_eq] at h1 ⊢
    rw [sched.cur_sc.guard (gS := PathObl.guard st (Rd) (Rd)) X2
      (nd2 _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]))]
    exact h1
  replace h2 := hk
  rw [R.sched.cur_sc_eq] at h1
  obtain ⟨csc, ecs, rfl⟩ := bind_shape h1
  try dsimp only at h2 ⊢
  have ec : csc = L.cscW X2 := by
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) _)] at ecs; exact (ok_inj_ff ecs).symm
  subst ec
  -- consumed
  refine once_step hR0 hU (R.sched.consumed_nz) h2 (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
  · rw [R.sched.consumed_eq] at h1 ⊢
    rw [sched.consumed.guard (gS := PathObl.guard st (Rd) (Rd)) X2
      (nd2 _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]))]
    exact h1
  replace h2 := hk
  rw [R.sched.consumed_eq] at h1
  obtain ⟨cu, -, rfl⟩ := bind_shape h1
  try dsimp only at h2 ⊢
  -- sufficient
  refine once_step hR0 hU (R.sporadic.sufficient_nz _ _) h2 (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
  · rw [R.sporadic.sufficient_eq] at h1 ⊢
    rw [sporadic.sufficient.guard (gS := PathObl.guard st (Rd) (Rd))
      ar X2 a2 (L.cscW X2) cu hs2]
    exact h1
  replace h2 := hk
  rw [R.sporadic.sufficient_eq] at h1
  obtain ⟨⟨b, a3⟩, -, rfl⟩ := bind_shape h1
  try dsimp only at h2 ⊢
  all_goals (first
    | (rw [if_neg Bool.false_ne_true]; simp only [Once]; done)
    | (rw [if_pos rfl] at h2 ⊢))
  -- the fast path
  unfold R.fastpath_vm.reply_recv_vm_found at h2 ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret] at h2 ⊢
  -- action
  refine once_step hR0 hU (R.sched.action_nz) h2 (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
  · rw [R.sched.action_eq] at h1 ⊢
    rw [sched.action.guard (gS := PathObl.guard st (Rd) (Rd)) X2
      (nd2 _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]))]
    exact h1
  replace h2 := hk
  rw [R.sched.action_eq] at h1
  obtain ⟨ia, -, rfl⟩ := bind_shape h1
  try dsimp only at h2 ⊢
  by_cases hia : (ia != sched.ACTION_RESUME_CURRENT) = true
  · rw [if_pos hia]; simp only [Once]
  rw [if_neg hia] at h2 ⊢
  -- is_schedulable
  refine once_step hR0 hU (R.sched.is_schedulable_nz _) h2 (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
  · rw [R.sched.is_schedulable_eq] at h1 ⊢
    rw [is_sched_guardC (gS := PathObl.guard st (Rd) (Rd)) X2
      (L.curW x) D.tSt D.tSc D.tMx D.tIq]
    exact h1
  replace h2 := hk
  rw [R.sched.is_schedulable_eq] at h1
  obtain ⟨bs, -, rfl⟩ := bind_shape h1
  try dsimp only at h2 ⊢
  by_cases hbs : bs = true
  swap
  · rw [if_neg hbs]; simp only [Once]
  rw [if_pos hbs] at h2 ⊢
  -- msg_info
  refine once_step hR0 hU (R.msg.msg_info_nz _) h2 (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
  · rw [R.msg.msg_info_eq] at h1 ⊢
    rw [msg.msg_info.guard (gS := PathObl.guard st (Rd) (Rd)) X2
      (L.curW x) D.tMi]
    exact h1
  replace h2 := hk
  rw [R.msg.msg_info_eq] at h1
  obtain ⟨info, -, rfl⟩ := bind_shape h1
  try dsimp only at h2 ⊢
  by_cases hx1 : (info.extra_caps != 0#u64) = true
  · rw [if_pos hx1]; simp only [Once]
  rw [if_neg hx1] at h2 ⊢
  by_cases hx2 : (info.label != 0#u64) = true
  · rw [if_pos hx2]; simp only [Once]
  rw [if_neg hx2] at h2 ⊢
  -- the receiver
  refine once_step hR0 hU (R.obj.Reply.tcb_nz _) h2 (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
  · rw [R.obj.Reply.tcb_eq] at h1 ⊢
    rw [obj.Reply.tcb.guard (gS := PathObl.guard st (Rd) (Rd))
      rptr X2 D.rRt]
    exact h1
  replace h2 := hk
  rw [R.obj.Reply.tcb_eq] at h1
  obtain ⟨u, eu, rfl⟩ := bind_shape h1
  try dsimp only at h2 ⊢
  have hu : L.mem X2 (rTcbA rptr) = u := by
    rw [eq_of_spec_fd (obj.Reply.tcb.blk (L := L) X2 rptr)] at eu; exact ok_inj_ff eu
  -- `is_null`
  refine once_step hR0 hU (NoZero.liftR _) h2 (fun r h1 => by rw [interp_liftR_store _ st]; exact h1)
    (fun r h1 hk Wd _ => ?_)
  replace h2 := hk
  obtain ⟨b1, x2, a4⟩ := r
  obtain ⟨eb1, e1, e2⟩ := interp_liftR_ok h1
  dsimp only at e1 e2 eb1
  subst x2 a4
  try dsimp only at h2 ⊢
  rw [is_null_ok] at eb1
  obtain rfl := ok_inj_ff eb1
  by_cases hb1 : decide (u = 0#u64) = true
  · rw [if_pos hb1]; simp only [Once]
  rw [if_neg hb1] at h2 ⊢
  have hu0' : u ≠ 0#u64 := by simpa using hb1
  have haffX : L.mem X2 (affA u) ≠ L.cpu X2 := hoff u hu hu0'
  obtain ⟨gSc, gAf, -, -⟩ := D.uG u hu hu0'
  -- the first racy read: `u.STATE`
  unfold R.obj.Tcb.state at h2 ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind, SProg.read] at h2 ⊢
  simp only [interp] at h2
  obtain ⟨v0, hv0, h2⟩ := bok.mp h2
  simp only [Once]
  refine ⟨fun _ => Set.notMem_empty _, fun v hv => ?_⟩
  rw [hv0] at hv
  obtain rfl := ok_inj_ff hv
  try dsimp only at h2 ⊢
  by_cases hst : (v0 != sched.TS_BLOCKED_ON_REPLY) = true
  · rw [if_pos hst]; simp only [Once]
  rw [if_neg hst] at h2 ⊢
  -- the second racy read: `u.FAULT_TYPE`
  unfold R.obj.Tcb.fault_type at h2 ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc] at h2 ⊢
  refine once_step hR0 hU (NoZero.liftR _) h2 (fun r h1 => by rw [interp_liftR_store _ st]; exact h1)
    (fun r h1 hk Wd _ => ?_)
  replace h2 := hk
  obtain ⟨fi, x2, a4⟩ := r
  obtain ⟨efi, e1, e2⟩ := interp_liftR_ok h1
  dsimp only at e1 e2 efi
  subst x2 a4
  rw [eq_ok_of_spec Fl4Proofs.P0.Consts.layout.tcb.FAULT_TYPE.spec] at efi
  obtain rfl := ok_inj_ff efi
  try dsimp only at h2 ⊢
  simp only [SProg.sbind, SProg.read] at h2 ⊢
  simp only [interp] at h2
  obtain ⟨v1, hv1, h2⟩ := bok.mp h2
  simp only [Once]
  refine ⟨fun _ hq => ?_, fun v hv => ?_⟩
  · unfold E2E.tch at hq
    split_ifs at hq
    · rcases hq with hq | hq
      · exact ft_ne_st u hq
      · exact hq
    · exact hq
  rw [hv1] at hv
  obtain rfl := ok_inj_ff hv
  try dsimp only at h2 ⊢
  by_cases hft : (v1 != fl4_abi.consts.fault.VMFault) = true
  · rw [if_pos hft]; simp only [Once]
  rw [if_neg hft] at h2 ⊢
  -- `Reply.next`
  refine once_step hR0 hU (R.obj.Reply.next_nz _) h2 (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
  · rw [R.obj.Reply.next_eq] at h1 ⊢
    rw [obj.Reply.next.guard (gS := PathObl.guard st (Rd) (Rd))
      X2 rptr D.rNx]
    exact h1
  replace h2 := hk
  rw [R.obj.Reply.next_eq] at h1
  obtain ⟨i4, -, rfl⟩ := bind_shape h1
  try dsimp only at h2 ⊢
  by_cases h4 : (i4 != 0#u64) = true
  on_goal 2 => rw [if_neg h4] at h2 ⊢
  on_goal 1 =>
    rw [if_pos h4] at h2 ⊢
    refine once_step hR0 hU (R.obj.Reply.next_is_head_nz _) h2 (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
    · rw [R.obj.Reply.next_is_head_eq] at h1 ⊢
      rw [obj.Reply.next_is_head.guard (gS := PathObl.guard st (Rd)
        (Rd)) X2 rptr D.rNx]
      exact h1
    replace h2 := hk
    rw [R.obj.Reply.next_is_head_eq] at h1
    obtain ⟨b2, -, rfl⟩ := bind_shape h1
    try dsimp only at h2 ⊢
    by_cases hb2 : b2 = true
    · rw [if_pos hb2]; simp only [Once]
    rw [if_neg hb2] at h2 ⊢
  all_goals
    refine once_step hR0 hU (R.obj.Tcb.sc_nz _) h2 (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
    · rw [R.obj.Tcb.sc_eq] at h1 ⊢
      rw [obj.Tcb.sc.guard (gS := PathObl.guard st (Rd) (Rd))
        u X2 gSc]
      exact h1
    replace h2 := hk
    rw [R.obj.Tcb.sc_eq] at h1
    obtain ⟨usc, -, rfl⟩ := bind_shape h1
    try dsimp only at h2 ⊢
    refine once_step hR0 hU (NoZero.liftR _) h2 (fun r h1 => by rw [interp_liftR_store _ st]; exact h1)
      (fun r h1 hk Wd _ => ?_)
    replace h2 := hk
    obtain ⟨b3, x2, a4⟩ := r
    obtain ⟨-, e1, e2⟩ := interp_liftR_ok h1
    dsimp only at e1 e2
    subst x2 a4
    try dsimp only at h2 ⊢
    by_cases hb3 : b3 = true
    · rw [if_pos hb3]; simp only [Once]
    rw [if_neg hb3] at h2 ⊢
    -- `schedulable_here u` answers `false`
    refine once_step hR0 hU (R.fastpath.schedulable_here_nz _) h2 (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
    · rw [R.fastpath.schedulable_here_eq] at h1 ⊢
      rw [vm_here_guard (gS := PathObl.guard st (Rd) (Rd)) X2 u
        (nd2 _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))
        (nd2 _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]))
        (nd2 _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]))
        D.tm D.rh D.dt D.cd gAf (fun hl => absurd hl haffX)]
      exact h1
    replace h2 := hk
    rw [R.fastpath.schedulable_here_eq] at h1
    obtain ⟨bh, ebh, rfl⟩ := bind_shape h1
    have hfalse : bh = false := by
      cases bh
      · rfl
      · exact absurd (here_facts (L := L) ebh).aff haffX
    subst hfalse
    try dsimp only at h2 ⊢
    rw [if_neg Bool.false_ne_true]
    simp only [Once]


end

end Fl4Proofs.P2.PathObl
