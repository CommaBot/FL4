/-
P3 (line mmuAD, gen 34): **the spec outcome of `vmReportF`** (step 4 of gen 33's plan toward `ReportJ3`), in the
form FL4's `vcpu::report` reaches it: the message state `jMrSt` (P3/XTopJointFault), optionally `PENDING`
cleared, message info and badge registers, FaultIP := NextIP, then `Running`.

* `v3_vmFaultIpNext_eq`: `vmFaultIpNext t` (FL4 #81) is one register update (XTopJointKEntry's
  `fl4SyscallFaultIP_eq` without the `- 2`).
* `v3_sched_setReg`, **`v3_stsAct_setReg`**: a register update of `t` commutes with `set_thread_state`'s
  `stsAct` (the schedulability of `t` reads its state, SC and the release queue, not its registers) — FL4 writes
  FaultIP before the state, the spec after.
* `repTail σ2 t x1 mi bd`: the state after the message info `mi`, the badge `bd`, `Running` and FaultIP :=
  NextIP (spec order), from `σ2` whose `t` is `x1`; **`v3_vmReportF_none`** / **`v3_vmReportF_some`**:
  `vmReportF t badge σ = {((), repTail …)}` without / with a bound VCPU (`repMrs`/`repR` name the pure part).

No named premise. No existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3MrJ
import Fl4Proofs.P3.VirtReportEq
import Fl4Proofs.P3.JAtZBDetach
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open Fl4Spec Classical Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp

noncomputable section

theorem v3_vmFaultIpNext_eq {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x)) :
    vmFaultIpNext (Z := Unit) t σ =
      ({((), updK σ t (.tcb (setReg x .faultIP (x.tcbArch.tcbContext.userRegs .nextIP))))}, False) := by
  unfold vmFaultIpNext asUser
  show (NonDet.getsThe _ >>= _) σ = _
  rw [nd_bind_one (getTcb_eq hk)]
  show ((pure _ : NonDet (State Unit) UserContext) >>= _) σ = _
  rw [nd_pure_bind']
  show (NonDet.selectF _ >>= _) σ = _
  rw [nd_bind_one (show NonDet.selectF (σ := State Unit) ((NonDet.bind (getRegister nextInstructionRegister)
      fun n => setRegister faultRegister n) (archTcbContextGet x.tcbArch)) σ =
      ({(((), ⟨(archTcbContextGet x.tcbArch).userFpuState,
        Function.update (archTcbContextGet x.tcbArch).userRegs .faultIP
          ((archTcbContextGet x.tcbArch).userRegs .nextIP)⟩), σ)}, False) by
    simp only [NonDet.selectF, NonDet.bind, getRegister, setRegister, NonDet.gets, NonDet.modify,
      nextInstructionRegister, faultRegister]
    ext ⟨a, b⟩ <;> simp)]
  show ((pure _ : NonDet (State Unit) Tcb) >>= _) σ = _
  rw [nd_pure_bind']
  exact (nd_bind_one (setObject_eq (o' := KernelObject.tcb (setReg x .faultIP
    (x.tcbArch.tcbContext.userRegs .nextIP))) hk rfl) _).trans rfl

theorem v3_optMap_congr {α β γ : Type} {f f' : α → Option β} {g : β → Option γ} {t : α} (h : f t = f' t) :
    optMap f g t = optMap f' g t := by
  unfold optMap; rw [h]

/-- The schedulability of `t` does not read its registers. -/
theorem v3_sched_setReg (σ : State Unit) (t : ObjRef) (y : Tcb) (r : Register) (n : Word) :
    schedulable t (updK σ t (.tcb (setReg y r n))) = schedulable t (updK σ t (.tcb y)) := by
  have hsc : ∀ p, scsOf (updK σ t (.tcb (setReg y r n))) p = scsOf (updK σ t (.tcb y)) p := by
    intro p
    by_cases hp : p = t
    · subst hp; simp [scsOfKh, optMap, updK, scOf]
    · simp [scsOfKh, optMap, updK, hp]
  have htc : optMapSome (tcbsOf (updK σ t (.tcb (setReg y r n)))) Tcb.tcbState t =
      optMapSome (tcbsOf (updK σ t (.tcb y))) Tcb.tcbState t := by
    simp [optMapSome, tcbsOfKh, optMap, updK, tcbOf, setReg]
  have hts : optMap (tcbsOf (updK σ t (.tcb (setReg y r n)))) Tcb.tcbSchedContext t =
      optMap (tcbsOf (updK σ t (.tcb y))) Tcb.tcbSchedContext t := by
    simp [tcbsOfKh, optMap, updK, tcbOf, setReg]
  unfold schedulable
  apply decide_eq_decide.2
  have hfun : scsOf (updK σ t (.tcb (setReg y r n))) = scsOf (updK σ t (.tcb y)) := funext hsc
  have e2 : optMap (optMap (tcbsOf (updK σ t (.tcb (setReg y r n)))) Tcb.tcbSchedContext)
      (scsOf (updK σ t (.tcb (setReg y r n)))) t =
      optMap (optMap (tcbsOf (updK σ t (.tcb y))) Tcb.tcbSchedContext) (scsOf (updK σ t (.tcb y))) t := by
    rw [hfun]; exact v3_optMap_congr hts
  unfold optPred
  rw [htc, e2]
  rfl

/-- **A register update of `t` commutes with `stsAct`** (module docstring). -/
theorem v3_stsAct_setReg (σ : State Unit) (t : ObjRef) (y : Tcb) (r : Register) (n : Word) :
    updK (stsAct (updK σ t (.tcb y)) t) t (.tcb (setReg y r n)) = stsAct (updK σ t (.tcb (setReg y r n))) t := by
  unfold stsAct
  rw [v3_sched_setReg]
  have e1 : (updK σ t (.tcb (setReg y r n))).curThread = (updK σ t (.tcb y)).curThread := rfl
  have e2 : (updK σ t (.tcb (setReg y r n))).schedulerAction = (updK σ t (.tcb y)).schedulerAction := rfl
  rw [e1, e2]
  by_cases c : t = (updK σ t (.tcb y)).curThread ∧ (updK σ t (.tcb y)).schedulerAction = .resumeCurThread ∧
      ¬ schedulable t (updK σ t (.tcb y)) = true
  · rw [if_pos c, if_pos c]
    simp only [updK, Function.update_idem]
  · rw [if_neg c, if_neg c]
    simp only [updK, Function.update_idem]

/-- The state after the message info `mi`, the badge `bd`, `Running` and FaultIP := NextIP (spec order). -/
def repTail (σ2 : State Unit) (t : ObjRef) (x1 : Tcb) (mi bd : Word) : State Unit :=
  updK (stsAct (updK (updK (updK σ2 t (.tcb (setReg x1 msg_info_register mi))) t
      (.tcb (setReg (setReg x1 msg_info_register mi) badge_register bd))) t
      (.tcb { setReg (setReg x1 msg_info_register mi) badge_register bd with tcbState := .running })) t) t
    (.tcb (setReg { setReg (setReg x1 msg_info_register mi) badge_register bd with tcbState := .running } .faultIP
      ((setReg (setReg x1 msg_info_register mi) badge_register bd).tcbArch.tcbContext.userRegs .nextIP)))

/-- FL4's `full_reply` on the spec side. -/
abbrev repFull (x : Tcb) : Bool := decide (x.tcbArch.tcbContext.userRegs msg_info_register = 30)

/-- The pure report (`vmenterReportF`) of `t` (TCB `x`) with VCPU state `sto`. -/
abbrev repR (x : Tcb) (sto : Option VcpuState) (badge : Word) : VmenterResultF :=
  vmenterReportF virtKind sto (repFull x) badge

theorem v3_setMrs_j {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (pb : Option ObjRef) (ms : List Word)
    (hal : ∀ p, pb = some p → ∀ q ∈ mrPairs ms, (bufAddr p q.1).toNat % 8 = 0 ∧ inUserFrame (bufAddr p q.1) σ) :
    ∃ n, setMrs (Z := Unit) t pb ms σ = ({(n, jMrSt σ t x pb ms)}, False) := by
  cases pb with
  | none => exact ⟨_, setMrs_eqN hk ms⟩
  | some p => exact ⟨_, setMrs_eq hk p ms (hal p rfl)⟩

/-- The spec's TCB after the message (`withRegs`). -/
abbrev repX (x : Tcb) (ms : List Word) : Tcb := withRegs x (mrRegs x.tcbArch.tcbContext.userRegs ms)

set_option maxHeartbeats 4000000 in
theorem v3_repTail_run {σ2 : State Unit} {t : ObjRef} {x1 : Tcb} (hk : σ2.kheap t = some (.tcb x1)) (mi bd : Word) :
    (do
      asUser (Z := Unit) t (setRegister msg_info_register mi)
      asUser t (setRegister badge_register bd)
      setThreadState t .running
      vmFaultIpNext t) σ2 = ({((), repTail σ2 t x1 mi bd)}, False) := by
  rw [nd_bind_one (asUser_setRegister_eq _ _ hk)]
  rw [nd_bind_one (asUser_setRegister_eq _ _ (by simp [updK] : (updK σ2 t (.tcb (setReg x1 msg_info_register mi))).kheap t =
    some (.tcb (setReg x1 msg_info_register mi))))]
  rw [nd_bind_one (Notif.setThreadState_eq Fl4Spec.ThreadState.running (by simp [updK] :
    (updK (updK σ2 t (.tcb (setReg x1 msg_info_register mi))) t
      (.tcb (setReg (setReg x1 msg_info_register mi) badge_register bd))).kheap t =
      some (.tcb (setReg (setReg x1 msg_info_register mi) badge_register bd))))]
  rw [v3_vmFaultIpNext_eq (x := { setReg (setReg x1 msg_info_register mi) badge_register bd with tcbState := .running })
    (by rw [stsAct_kheap]; simp [updK])]
  rfl

set_option maxHeartbeats 4000000 in
/-- **`vmReportF` of a thread without VCPU** (module docstring). -/
theorem v3_vmReportF_none {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (hvo : tcbVcpuOf σ t = none) (badge : Word)
    (hal : ∀ p, ipcBufOf true x = some p → ∀ q ∈ mrPairs (repR x none badge).mrs,
      (bufAddr p q.1).toNat % 8 = 0 ∧ inUserFrame (bufAddr p q.1) σ) :
    vmReportF (Z := Unit) t badge σ = ({((), repTail (jMrSt σ t x (ipcBufOf true x) (repR x none badge).mrs) t
      (repX x (repR x none badge).mrs) (repR x none badge).msgInfo (repR x none badge).badge)}, False) := by
  unfold vmReportF
  rw [nd_bind_one (VirtReportEq.getTcbVcpu_eq σ t), hvo]
  dsimp only
  rw [nd_pure_bind', nd_bind_one (VirtReportEq.vmFullReply_eq hk), nd_pure_bind',
    nd_bind_one (lookupIpcBuffer_eq hk true)]
  obtain ⟨n, hn⟩ := v3_setMrs_j hk (ipcBufOf true x) (repR x none badge).mrs hal
  rw [nd_bind_one hn]
  try dsimp only
  try rw [nd_pure_bind']
  exact v3_repTail_run (jMrSt_rcv _ _ _ _ _) _ _

set_option maxHeartbeats 4000000 in
/-- **`vmReportF` of a thread with VCPU `v`** (module docstring): `PENDING` cleared when the result says so. -/
theorem v3_vmReportF_some {σ : State Unit} {t v : ObjRef} {x : Tcb} {vs : VcpuState}
    (hk : σ.kheap t = some (.tcb x)) (hvo : tcbVcpuOf σ t = some v)
    (hkv : σ.kheap v = some (.archObj (.vcpu vs))) (badge : Word)
    (hal : ∀ p, ipcBufOf true x = some p → ∀ q ∈ mrPairs (repR x (some vs) badge).mrs,
      (bufAddr p q.1).toNat % 8 = 0 ∧ inUserFrame (bufAddr p q.1) σ) :
    vmReportF (Z := Unit) t badge σ = ({((), repTail
      (if (repR x (some vs) badge).clearPending then
        updK (jMrSt σ t x (ipcBufOf true x) (repR x (some vs) badge).mrs) v (.archObj (.vcpu vs.reported))
      else jMrSt σ t x (ipcBufOf true x) (repR x (some vs) badge).mrs) t
      (repX x (repR x (some vs) badge).mrs) (repR x (some vs) badge).msgInfo (repR x (some vs) badge).badge)},
      False) := by
  have hvt : v ≠ t := fun e => by rw [e, hk] at hkv; cases hkv
  unfold vmReportF
  rw [nd_bind_one (VirtReportEq.getTcbVcpu_eq σ t), hvo]
  dsimp only
  rw [nd_bind_one (zv_getVcpu_eq hkv), nd_pure_bind', nd_bind_one (VirtReportEq.vmFullReply_eq hk),
    nd_pure_bind', nd_bind_one (lookupIpcBuffer_eq hk true)]
  obtain ⟨n, hn⟩ := v3_setMrs_j hk (ipcBufOf true x) (repR x (some vs) badge).mrs hal
  rw [nd_bind_one hn]
  have hkv1 : (jMrSt σ t x (ipcBufOf true x) (repR x (some vs) badge).mrs).kheap v =
      some (.archObj (.vcpu vs)) := by rw [jMrSt_other _ _ _ _ _ hvt]; exact hkv
  have hkt1 := jMrSt_rcv σ t x (ipcBufOf true x) (repR x (some vs) badge).mrs
  cases hc : (repR x (some vs) badge).clearPending with
  | true =>
    have hc' : (vmenterReportF virtKind (some vs) (decide (x.tcbArch.tcbContext.userRegs msg_info_register = 30))
      badge).clearPending = true := hc
    simp only [hc, hc', ↓reduceIte]
    rw [nd_bind_one (zv_vcpuUpdate_eq hkv1 _)]
    exact v3_repTail_run (by simp only [updK_kheap]; rw [Function.update_of_ne (Ne.symm hvt)]; exact hkt1) _ _
  | false =>
    have hc' : (vmenterReportF virtKind (some vs) (decide (x.tcbArch.tcbContext.userRegs msg_info_register = 30))
      badge).clearPending = false := hc
    simp only [hc, hc', ↓reduceIte, Bool.false_eq_true]
    try rw [nd_pure_bind']
    exact v3_repTail_run hkt1 _ _

end

end Fl4Proofs.P3
