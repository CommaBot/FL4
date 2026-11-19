/-
P3 (DESIGN.md §9): **the IPC caps' leaves at `J`** (XTopJointEntry's
`JPath` for the Endpoint, Notification and Reply caps): the caller's
restart, then FL4's `send_signal` / `do_reply_transfer` / `send_ipc`,
against the spec's, from `JAtZ` at the invocation to `JAt` after.

* `notifLeafJ`: the caller's restart at `J` (`JAtZ.restartJ`), the cap's
  notification one of `N` (`JAtZ.slotN`), then ScSignalJ's `SignalJHyp`
  (`signalJHyp_of`: from `SignalRestJHyp` [J], the bound thread
  `RunningVM`, VT-x; the platform's `MIN_BUDGET`
  [P]).
* `replyLeafJ`: the restart, then `replyXferJ`: `do_reply_transfer` at `J`
  where nothing happens (no thread on the reply, or one not blocked on it)
  and `reply_remove` (`JAtZ.replyRemoveJD`, the dead set kept, the receiver
  `Inactive`), then `replyRestNoScJ` for a receiver without SC or fault,
  the transfer `XferOK` (XTopJointFault: a replier without a fault and no
  granted caps, or a faulted replier but for a timeout fault with an SC)
  (`ReplyRestNoSc`: no sporadic test, `JAtZ.xferAnyJ` with no endpoint and
  badge 0, `JAtZ.runIJ` with `RelIfBound` vacuous, no tail),
  `replyRestSwJ` for a released SC (`JAtZ.switchJ`),
  `replyRestPostJ` for an active SC that is not released and no
  valid timeout handler (`Running` and the tail's `postpone` as one step,
  `JAtZ.runPostJ`); all three after the sporadic unblock test
  (`JAtZ.replyUnblockJ`, XTopJointUnblock; `fl4ReplyRest_eq` splits FL4's
  code there), their cases read at the state after it; the other cases
  named (`JReplyRestHyp` [W]). `hZ`: JEntryGlob's `ipcBufOK`,
  `bufCover`, `bufPlaced` [J].
* `sendLeafJ`: the restart, then `sendXferJ`: `send_ipc` at `J` where
  nothing happens (a non-blocking send to an endpoint without receivers),
  the blocking send and the send to a receiver named (`JSendRestHyp` [W]).
-/
import Fl4Proofs.P3.XTopJointTcb
import Fl4Proofs.P3.ScSignalJ
import Fl4Proofs.P3.JProducers
import Fl4Proofs.P3.IpcReply
import Fl4Proofs.P3.XTopJointXfer
import Fl4Proofs.P3.XTopJointFault
import Fl4Proofs.P3.XTopJointRunI
import Fl4Proofs.P3.XTopJointSwitch
import Fl4Proofs.P3.XTopJointRunPost
import Fl4Proofs.P3.XTopJointUnblock
import Fl4Proofs.P3.AllDom
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- The caller's restart in the spec is deterministic. -/
theorem restart_out_eq {σ σ1 σ2 : Fl4Spec.State Unit}
    (h1 : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (h2 : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ2)}, False)) : σ1 = σ2 := by
  have e := (Prod.mk.inj (h1.symm.trans h2)).1
  exact congrArg Prod.snd (Set.singleton_eq_singleton_iff.1 e)

set_option maxHeartbeats 4000000 in
/-- **The notification cap's leaf at `J`** (module docstring). -/
theorem notifLeafJ (hAT : P0.ArchTotal arI) (hW : SignalRestJHyp (L := L) arI AR H Cs)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    {s : S} {ar : A} {σ σ1 : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) {ct : U64} (hct : sched.cur_thread st s = ok ct)
    {sl : Fl4Spec.CslotPtr} (hA : AbsSlot Z.th sl) {p b : U64} {w r : Bool}
    (hc : capAt (L.mem s) (cslotAddr sl) = ok (.Notification p b w r))
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False)) :
    XLeaf (L := L) (JAt (L := L) arI AR) s ar σ (do
        let s1 ← sched.set_thread_state st s ct sched.TS_RESTART
        let (s2, a1) ← notification.send_signal st arI s1 ar p b
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a1))
      (Fl4Spec.sendSignal (Z := Unit) p.bv b.bv σ1) := by
  intro _
  have hpN := (J.slotN hA hc).1
  obtain ⟨s1, σ1', x, -, hst1, -, -, -, -, -, -, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  obtain rfl := restart_out_eq hst1 hst
  rw [hs1]
  simp only [bind_ok]
  refine WP.spec_bind (signalJHyp_of hAT hW hmb Z Ac1 Lst1 D1 s1 ar σ1' p b J1 hpN) ?_
  rintro ⟨s2, a1⟩ ⟨σ', V', Ac', Lst', D', hsp, -, J'⟩
  apply (WP.spec_ok _).2
  refine ⟨rfl, ((), σ'), by rw [hsp]; exact Set.mem_singleton _, J'.xtop.relTop, _, _, _, _, _, _, J'⟩


variable (st arI) in
/-- FL4's `do_reply_transfer` after `reply_remove` (the receiver `i` was
blocked on the reply): the sporadic unblock test, the transfer and
`Running` or the fault reply, then the tail. -/
def fl4ReplyRest (s1 : S) (a1 : A) (sender i : U64) (grant : Bool) : Result (S × A) := do
  let i2 ← obj.Tcb.sc st i s1
  let b1 ← sporadic.sc_sporadic st s1 i2
  let s2 ←
    if b1
    then
      do
      let i3 ← obj.Sc.cpu st i2 s1
      let i4 ← obj.node_get st s1 i3 layout.node.CUR_SC
      if i2 != i4
      then sporadic.unblock_check st s1 i2
      else ok s1
    else ok s1
  let fault_type ← obj.Tcb.fault_type st i s2
  let (s3, a2) ←
    if fault_type = fl4_abi.consts.fault.NullFault
    then
      do
      let s4 ←
        ipc.do_ipc_transfer st arI s2 a1 sender
          0#u64 0#u64 grant i
      let s5 ←
        sched.set_thread_state st s4 i sched.TS_RUNNING
      ok (s5, a1)
    else
      do
      let (restart, s4, a3) ←
        faults.handle_fault_reply st arI s2 a1 i
          sender
      let s5 ← faults.clear_fault st s4 i
      if restart
      then
        let s6 ←
          sched.set_thread_state st s5 i sched.TS_RESTART
        ok (s6, a3)
      else
        let s6 ←
          sched.set_thread_state st s5 i sched.TS_INACTIVE
        ok (s6, a3)
  let i3 ← obj.Tcb.sc st i s3
  let b2 ← obj.Sc.is_null i3
  if b2
  then ok (s3, a2)
  else
    let b3 ← sched.is_runnable st s3 i
    if b3
    then
      let b4 ← sporadic.ready st s3 i3
      if b4
      then
        let b5 ←
          sporadic.sufficient st arI s3 a2 i3
            0#u64
        if b5
        then
          let s4 ← sched.possible_switch_to st s3 i
          ok (s4, a2)
        else
          let b6 ← faults.valid_timeout_handler st s3 i
          if b6
          then
            if fault_type != fl4_abi.consts.fault.Timeout
            then
              let badge ← obj.Sc.badge st i3 s3
              faults.handle_timeout st arI s3 a2
                i (error.Fault.Timeout badge)
            else
              let s4 ← sched.postpone st s3 i3
              ok (s4, a2)
          else let s4 ← sched.postpone st s3 i3
               ok (s4, a2)
      else
        let b5 ← faults.valid_timeout_handler st s3 i
        if b5
        then
          if fault_type != fl4_abi.consts.fault.Timeout
          then
            let badge ← obj.Sc.badge st i3 s3
            faults.handle_timeout st arI s3 a2 i
              (error.Fault.Timeout badge)
          else let s4 ← sched.postpone st s3 i3
               ok (s4, a2)
        else let s4 ← sched.postpone st s3 i3
             ok (s4, a2)
    else ok (s3, a2)

variable (st arI) in
/-- `fl4ReplyRest` after the sporadic unblock test (`s2`). -/
def fl4ReplyRest2 (s2 : S) (a1 : A) (sender i : U64) (grant : Bool) : Result (S × A) := do
  let fault_type ← obj.Tcb.fault_type st i s2
  let (s3, a2) ←
    if fault_type = fl4_abi.consts.fault.NullFault
    then
      do
      let s4 ←
        ipc.do_ipc_transfer st arI s2 a1 sender
          0#u64 0#u64 grant i
      let s5 ←
        sched.set_thread_state st s4 i sched.TS_RUNNING
      ok (s5, a1)
    else
      do
      let (restart, s4, a3) ←
        faults.handle_fault_reply st arI s2 a1 i
          sender
      let s5 ← faults.clear_fault st s4 i
      if restart
      then
        let s6 ←
          sched.set_thread_state st s5 i sched.TS_RESTART
        ok (s6, a3)
      else
        let s6 ←
          sched.set_thread_state st s5 i sched.TS_INACTIVE
        ok (s6, a3)
  let i3 ← obj.Tcb.sc st i s3
  let b2 ← obj.Sc.is_null i3
  if b2
  then ok (s3, a2)
  else
    let b3 ← sched.is_runnable st s3 i
    if b3
    then
      let b4 ← sporadic.ready st s3 i3
      if b4
      then
        let b5 ←
          sporadic.sufficient st arI s3 a2 i3
            0#u64
        if b5
        then
          let s4 ← sched.possible_switch_to st s3 i
          ok (s4, a2)
        else
          let b6 ← faults.valid_timeout_handler st s3 i
          if b6
          then
            if fault_type != fl4_abi.consts.fault.Timeout
            then
              let badge ← obj.Sc.badge st i3 s3
              faults.handle_timeout st arI s3 a2
                i (error.Fault.Timeout badge)
            else
              let s4 ← sched.postpone st s3 i3
              ok (s4, a2)
          else let s4 ← sched.postpone st s3 i3
               ok (s4, a2)
      else
        let b5 ← faults.valid_timeout_handler st s3 i
        if b5
        then
          if fault_type != fl4_abi.consts.fault.Timeout
          then
            let badge ← obj.Sc.badge st i3 s3
            faults.handle_timeout st arI s3 a2 i
              (error.Fault.Timeout badge)
          else let s4 ← sched.postpone st s3 i3
               ok (s4, a2)
        else let s4 ← sched.postpone st s3 i3
             ok (s4, a2)
    else ok (s3, a2)

theorem fl4ReplyRest_eq (s1 : S) (a1 : A) (sender i : U64) (grant : Bool) :
    fl4ReplyRest st arI s1 a1 sender i grant = (do
      let i2 ← obj.Tcb.sc st i s1
      let b1 ← sporadic.sc_sporadic st s1 i2
      let s2 ←
        if b1
        then
          do
          let i3 ← obj.Sc.cpu st i2 s1
          let i4 ← obj.node_get st s1 i3 layout.node.CUR_SC
          if i2 != i4
          then sporadic.unblock_check st s1 i2
          else ok s1
        else ok s1
      fl4ReplyRest2 st arI s2 a1 sender i grant) := rfl

/-- The case of the rest of `do_reply_transfer` proved at `J`
(`replyRestNoScJ`), after `reply_remove` (`σ2`): the receiver `i` has no SC
and no fault, and the transfer from the replier `ct` is `XferOK` (no
fault and no granted caps: no grant, no send buffer, or no extra caps; or a
fault but a timeout fault with an SC). -/
def ReplyRestNoSc (σ2 : Fl4Spec.State Unit) (ct i : U64) (g : Bool) : Prop :=
  ∃ xs xi, σ2.kheap ct.bv = some (.tcb xs) ∧ σ2.kheap i.bv = some (.tcb xi) ∧ xi.tcbSchedContext = none ∧
    xi.tcbFault = none ∧ XferOK xs g

set_option maxHeartbeats 8000000 in
/-- **The rest of `do_reply_transfer` at `J`, for `ReplyRestNoSc`**: FL4's
SC word of the receiver is 0 (`SchedSpec.tcb`), so no sporadic test and no
tail; its fault word 0 (`fault0`), so the transfer (`JAtZ.xferAnyJ`, no
endpoint, badge 0) and `Running` (`JAtZ.runIJ`, `RelIfBound` with no SC);
the spec's outcome by `mem_doReplyTransfer` (unblock test on no SC the
identity, `specReplyTail_skip`). -/
theorem replyRestNoScJ
    (hZ : ∀ (Z' : XSets) (s' : S) (a' : A) σ', Z'.th = Z.th → XTopAt (L := L) AR Z' s' a' σ' →
      Endp.IpcBufCapOK σ' ∧ Endp.BufCover Z'.T Z'.B σ' ∧ Vs.BufPlaced (L := L) Z'.N Z'.C Z'.B Z'.c s' σ')
    {s2 : S} {ar : A} {σ1 σ0 σ2 : Fl4Spec.State Unit} (J2 : JAtZ (L := L) arI AR Z H Cs Ac Lst D s2 ar σ2)
    {ct i p : U64} (g : Bool) (hne : ct ≠ i) (hiD : i ∉ D)
    {xr : Fl4Spec.Reply} (hkr : σ1.kheap p.bv = some (.reply xr)) (hrep : xr.replyTcb = some i.bv)
    {x : Fl4Spec.Tcb} (hkx : σ1.kheap i.bv = some (.tcb x)) (hst : x.tcbState = .blockedOnReply p.bv)
    (hrm : Fl4Spec.replyRemove (Z := Unit) i.bv p.bv σ1 = ({((), σ0)}, False))
    (hub : (Fl4Spec.getTcbObjRef (Z := Unit) Fl4Spec.Tcb.tcbSchedContext i.bv >>=
      Fl4Spec.ifSporadicCurScTestRefillUnblockCheck) σ0 = ({((), σ2)}, False))
    (hin : ∃ x', σ2.kheap i.bv = some (.tcb x') ∧ x'.tcbState = .inactive)
    (hC : ReplyRestNoSc σ2 ct i g) :
    fl4ReplyRest2 st arI s2 ar ct i g ⦃ res => ∃ z ∈ (Fl4Spec.doReplyTransfer (Z := Unit) ct.bv p.bv g σ1).1,
      JAt (L := L) arI AR res.1 res.2 z.2 ⦄ := by
  obtain ⟨xs, xi, hks, hki, hnsc, hfi, hok⟩ := hC
  obtain ⟨xi', hki', hin⟩ := hin
  rw [hki] at hki'; cases hki'
  have hI := J2.xtop.irelK J2.ks J2.buf
  have hiT : i ∈ Z.T := by
    obtain ⟨t, ht, h⟩ := J2.obj.tcb _ xi hki
    rw [Sched.bv_inj h] at ht; exact ht
  have hcT : ct ∈ Z.T := by
    obtain ⟨t, ht, h⟩ := J2.obj.tcb _ xs hks
    rw [Sched.bv_inj h] at ht; exact ht
  obtain ⟨Q, R0, hc, hsp⟩ := J2.xtop.fin.1.1.1.lists
  obtain ⟨x0, hk0, -, -, hscw, -⟩ := hsp.tcb i hiT
  rw [hki] at hk0; cases hk0
  obtain ⟨x0', hk0', hTR⟩ := hI.1.tcb i hiT
  rw [hki] at hk0'; cases hk0'
  unfold fl4ReplyRest2
  step with Fl4Proofs.P3.Endp.obj.Tcb.fault_type.spec as ⟨ft, hft⟩
  have hft0 : ft = 0#u64 := by rw [hft]; exact hTR.fault0.2 hfi
  rw [if_pos (by rw [hft0]; unfold fl4_abi.consts.fault.NullFault; rfl)]
  have e0 : U64.bv 0#u64 = (0 : Fl4Spec.Word) := rfl
  refine WP.spec_bind (Pₘ := fun res => res.2 = ar ∧ ∃ (σ3 : Fl4Spec.State Unit) (x3 : Fl4Spec.Tcb) (V : XVs)
      (Lst' : U64 → List U64),
      Fl4Spec.doIpcTransfer (Z := Unit) ct.bv none 0 g i.bv σ2 = ({((), σ3)}, False) ∧
      σ3.kheap i.bv = some (.tcb x3) ∧ x3.tcbSchedContext = none ∧
      JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst' D res.1 ar
        (stsAct (updK σ3 i.bv (.tcb { x3 with tcbState := .running })) i.bv)) ?_ ?_
  · refine WP.spec_bind (J2.xferAnyJ hZ hcT hiT hne hks hki hok none 0#u64 0#u64) ?_
    rintro s4 ⟨σ3, htr, -, ⟨x3, hk3, hx3⟩, V, J3⟩
    rw [e0] at htr
    have hs3 : x3.tcbState = .inactive := (congrArg Fl4Spec.Tcb.tcbState hx3).trans hin
    have hsc3 : x3.tcbSchedContext = none := (congrArg Fl4Spec.Tcb.tcbSchedContext hx3).trans hnsc
    refine WP.spec_bind (J3.runIJ hiT hiD hk3 hs3 (relIfBound_noSc hk3 hsc3)) ?_
    rintro s5 ⟨Lst', J5⟩
    exact (WP.spec_ok _).2 ⟨rfl, σ3, x3, V, Lst', htr, hk3, hsc3, J5⟩
  rintro ⟨s5, a2⟩ ⟨ha, σ3, x3, V, Lst', htr, hk3, hsc3, J5⟩
  simp only at ha
  subst ha
  set σ5 := stsAct (updK σ3 i.bv (.tcb { x3 with tcbState := .running })) i.bv with hσ5
  have hk5 : σ5.kheap i.bv = some (.tcb { x3 with tcbState := .running }) := by
    rw [hσ5, stsAct_kheap]; simp [updK]
  obtain ⟨Q5, R5, hc5, hsp5⟩ := J5.xtop.fin.1.1.1.lists
  obtain ⟨x5, hk5', -, -, hscw5, -⟩ := hsp5.tcb i hiT
  rw [hk5] at hk5'; cases hk5'
  step with Fl4Proofs.P1.obj.Tcb.sc.spec as ⟨i3, hi3⟩
  have h3 : i3 = 0#u64 := by
    by_contra h
    have e := hscw5
    rw [← hi3, Notif.optRef_ne h] at e
    rw [hsc3] at e
    cases e
  step with Fl4Proofs.P3.Sched.obj.Sc.is_null.spec' as ⟨b2, hb2⟩
  rw [hb2, if_pos (by simp [h3]), WP.spec_ok]
  have hz1 : ((), σ5) ∈ ((Fl4Spec.doIpcTransfer (Z := Unit) ct.bv none 0 g i.bv >>= fun _ =>
      Fl4Spec.setThreadState i.bv .running) σ2).1 := by
    rw [nd_bind_one htr, Notif.setThreadState_eq _ hk3]; rfl
  have hz : ((), σ5) ∈ (specReplyTail i.bv xi.tcbFault σ5).1 := by
    rw [specReplyTail_skip hk5 (Or.inl hsc3)]; rfl
  exact ⟨((), σ5), mem_doReplyTransfer hkr hrep hkx hst g hrm hub hki (Or.inl ⟨hfi, hz1⟩) hz,
    _, _, _, _, _, _, J5⟩

/-- The second case of the rest of `do_reply_transfer` proved at `J`
(`replyRestSwJ`), after `reply_remove` (`σ2`): the receiver `i` has an
active SC `sp` that is released (ready and sufficient), no
fault; the transfer `XferOK`. -/
def ReplyRestSw (σ2 : Fl4Spec.State Unit) (ct i : U64) (g : Bool) : Prop :=
  ∃ xs xi sp y n, σ2.kheap ct.bv = some (.tcb xs) ∧ σ2.kheap i.bv = some (.tcb xi) ∧
    xi.tcbSchedContext = some sp ∧ σ2.kheap sp = some (.schedContext y n) ∧
    Fl4Spec.scActive y = true ∧ Fl4Spec.refillReady σ2.curTime (Fl4Spec.refillHd y) = true ∧
    Fl4Spec.refillSufficient 0 (Fl4Spec.refillHd y) = true ∧
    xi.tcbFault = none ∧ XferOK xs g

set_option maxHeartbeats 16000000 in
/-- **The rest of `do_reply_transfer` at `J`, for `ReplyRestSw`**: the
sporadic unblock test done (`σ0` to `σ2`), the transfer (`JAtZ.xferAnyJ`), `Running` (`JAtZ.runIJ`, the SC
released: `RelIfBound`), then the tail's tests true (`ready_refines`,
`sufficient_refines`, MIN_BUDGET `hmb` [P]) and `possible_switch_to`
(`JAtZ.switchJ`). -/
theorem replyRestSwJ (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hZ : ∀ (Z' : XSets) (s' : S) (a' : A) σ', Z'.th = Z.th → XTopAt (L := L) AR Z' s' a' σ' →
      Endp.IpcBufCapOK σ' ∧ Endp.BufCover Z'.T Z'.B σ' ∧ Vs.BufPlaced (L := L) Z'.N Z'.C Z'.B Z'.c s' σ')
    {s2 : S} {ar : A} {σ1 σ0 σ2 : Fl4Spec.State Unit} (J2 : JAtZ (L := L) arI AR Z H Cs Ac Lst D s2 ar σ2)
    {ct i p : U64} (g : Bool) (hne : ct ≠ i) (hiD : i ∉ D) (hct2 : σ2.curThread = ct.bv)
    {xr : Fl4Spec.Reply} (hkr : σ1.kheap p.bv = some (.reply xr)) (hrep : xr.replyTcb = some i.bv)
    {x : Fl4Spec.Tcb} (hkx : σ1.kheap i.bv = some (.tcb x)) (hst : x.tcbState = .blockedOnReply p.bv)
    (hrm : Fl4Spec.replyRemove (Z := Unit) i.bv p.bv σ1 = ({((), σ0)}, False))
    (hub : (Fl4Spec.getTcbObjRef (Z := Unit) Fl4Spec.Tcb.tcbSchedContext i.bv >>=
      Fl4Spec.ifSporadicCurScTestRefillUnblockCheck) σ0 = ({((), σ2)}, False))
    (hin : ∃ x', σ2.kheap i.bv = some (.tcb x') ∧ x'.tcbState = .inactive)
    (hC : ReplyRestSw σ2 ct i g) :
    fl4ReplyRest2 st arI s2 ar ct i g ⦃ res => ∃ z ∈ (Fl4Spec.doReplyTransfer (Z := Unit) ct.bv p.bv g σ1).1,
      JAt (L := L) arI AR res.1 res.2 z.2 ⦄ := by
  obtain ⟨xs, xi, sp, y, n, hks, hki, hxsc, hky, hya, hrdy, hsuf, hfi, hok⟩ := hC
  obtain ⟨xi', hki', hin⟩ := hin
  rw [hki] at hki'; cases hki'
  have hI := J2.xtop.irelK J2.ks J2.buf
  have hiT : i ∈ Z.T := by
    obtain ⟨t, ht, h⟩ := J2.obj.tcb _ xi hki
    rw [Sched.bv_inj h] at ht; exact ht
  have hcT : ct ∈ Z.T := by
    obtain ⟨t, ht, h⟩ := J2.obj.tcb _ xs hks
    rw [Sched.bv_inj h] at ht; exact ht
  have hnr2 : i.bv ∉ σ2.releaseQueue := fun hm => by
    obtain ⟨x', -, -, -, h1, -, h3, -⟩ := J2.inv.rel _ hm
    rw [hki] at h1; cases h1; rw [hin] at h3; cases h3
  obtain ⟨Q, R0, hc, hsp⟩ := J2.xtop.fin.1.1.1.lists
  obtain ⟨x0, hk0, -, -, hscw, -⟩ := hsp.tcb i hiT
  rw [hki] at hk0; cases hk0
  obtain ⟨x0', hk0', hTR⟩ := hI.1.tcb i hiT
  rw [hki] at hk0'; cases hk0'
  unfold fl4ReplyRest2
  obtain ⟨i2, hi2⟩ : ∃ i2 : U64, i2 = L.mem s2 (P1.scA i) := ⟨_, rfl⟩
  rw [← hi2] at hscw
  have h0 : i2 ≠ 0#u64 := by
    intro e; rw [e, optRef_zero, hxsc] at hscw; cases hscw
  have esp : sp = i2.bv := by rw [Notif.optRef_ne h0, hxsc] at hscw; exact Option.some.inj hscw
  subst esp
  have hi2C : i2 ∈ Z.C := by rw [hi2]; exact hsp.scMem i hiT (by rw [← hi2]; exact h0)
  obtain ⟨y', n', hky', hy⟩ := hsp.scs i2 hi2C
  rw [hky] at hky'; cases hky'
  step with Fl4Proofs.P3.Endp.obj.Tcb.fault_type.spec as ⟨ft, hft⟩
  have hft0 : ft = 0#u64 := by rw [hft]; exact hTR.fault0.2 hfi
  rw [if_pos (by rw [hft0]; unfold fl4_abi.consts.fault.NullFault; rfl)]
  have e0 : U64.bv 0#u64 = (0 : Fl4Spec.Word) := rfl
  refine WP.spec_bind (Pₘ := fun res => res.2 = ar ∧ ∃ (σ3 : Fl4Spec.State Unit) (x3 : Fl4Spec.Tcb) (V : XVs)
      (Lst' : U64 → List U64),
      Fl4Spec.doIpcTransfer (Z := Unit) ct.bv none 0 g i.bv σ2 = ({((), σ3)}, False) ∧
      σ3.kheap i.bv = some (.tcb x3) ∧ x3.tcbSchedContext = some i2.bv ∧ x3.tcbFault = none ∧
      (∀ q, q ≠ i.bv → σ3.kheap q = σ2.kheap q) ∧
      JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst' D res.1 ar
        (stsAct (updK σ3 i.bv (.tcb { x3 with tcbState := .running })) i.bv)) ?_ ?_
  · refine WP.spec_bind (J2.xferAnyJ hZ hcT hiT hne hks hki hok none 0#u64 0#u64) ?_
    rintro s4 ⟨σ3, htr, hkp3, ⟨x3, hk3, hx3⟩, V, J3⟩
    rw [e0] at htr
    have mem3 : ((), σ3) ∈ (Fl4Spec.doIpcTransfer (Z := Unit) ct.bv none 0 g i.bv σ2).1 := by
      rw [htr]; exact Set.mem_singleton _
    have hs3 : x3.tcbState = .inactive := (congrArg Fl4Spec.Tcb.tcbState hx3).trans hin
    have hsc3 : x3.tcbSchedContext = some i2.bv := (congrArg Fl4Spec.Tcb.tcbSchedContext hx3).trans hxsc
    have hf3 : x3.tcbFault = none := (congrArg Fl4Spec.Tcb.tcbFault hx3).trans hfi
    have hti : i2.bv ≠ i.bv := fun e => by rw [e, hki] at hky; cases hky
    have hky3 : σ3.kheap i2.bv = some (.schedContext y n) := by rw [hkp3 _ hti]; exact hky
    have htm3 : σ3.curTime = σ2.curTime := (SVK.sv_doIpcTransfer' _ _ _ _ _ σ2 _ mem3).2.1
    have hrel : RelIfBound σ3 i.bv := by
      intro x' scp y' n' h1 h2 h3 _ _
      rw [hk3] at h1; cases h1; rw [hsc3] at h2; cases h2; rw [hky3] at h3; cases h3
      exact ⟨by rw [htm3]; exact hrdy, hsuf⟩
    refine WP.spec_bind (J3.runIJ hiT hiD hk3 hs3 hrel) ?_
    rintro s5 ⟨Lst', J5⟩
    exact (WP.spec_ok _).2 ⟨rfl, σ3, x3, V, Lst', htr, hk3, hsc3, hf3, hkp3, J5⟩
  rintro ⟨s5, a2⟩ ⟨ha, σ3, x3, V, Lst', htr, hk3, hsc3, hf3, hkp3, J5⟩
  simp only at ha
  subst ha
  have mem3 : ((), σ3) ∈ (Fl4Spec.doIpcTransfer (Z := Unit) ct.bv none 0 g i.bv σ2).1 := by
    rw [htr]; exact Set.mem_singleton _
  set x5 : Fl4Spec.Tcb := { x3 with tcbState := .running } with hx5
  set σ4 := updK σ3 i.bv (.tcb x5) with hσ4
  set σ5 := stsAct σ4 i.bv with hσ5
  have hrec : σ5 = { σ4 with schedulerAction := σ5.schedulerAction } := stsAct_rec σ4 i.bv
  have hk5 : σ5.kheap i.bv = some (.tcb x5) := by rw [hσ5, stsAct_kheap]; simp [hσ4, updK]
  have hti : i2.bv ≠ i.bv := fun e => by rw [e, hki] at hky; cases hky
  have hky5 : σ5.kheap i2.bv = some (.schedContext y n) := by
    rw [hσ5, stsAct_kheap, hσ4]; simp only [updK, Function.update_of_ne hti]; rw [hkp3 _ hti]; exact hky
  have htm5 : σ5.curTime = σ2.curTime := by
    rw [hrec]; exact (SVK.sv_doIpcTransfer' _ _ _ _ _ σ2 _ mem3).2.1
  have hct5 : σ5.curThread = ct.bv := by
    rw [hrec]; show σ3.curThread = _; rw [(dk_doIpcTransfer' _ _ _ _ _).ct mem3, hct2]
  have hnr5 : i.bv ∉ σ5.releaseQueue := fun hm => by
    rw [hrec] at hm
    exact hnr2 (RelQ.rq_doIpcTransfer' _ _ _ _ _ σ2 _ mem3 _ hm)
  have hsch : Fl4Spec.schedulable i.bv σ5 = true := schedulable_of hk5 hsc3 rfl hky5 hya hnr5
  have hti5 : i.bv ≠ σ5.idleThread := by
    intro e
    obtain ⟨yi, h1, -, h3, -⟩ := J5.act.2
    rw [← e, hk5] at h1; cases h1; cases h3
  have htc5 : i.bv ≠ σ5.curThread := by
    rw [hct5]; intro e; exact hne (P1.eq_of_bv e).symm
  obtain ⟨Q5, R5, hc5, hsp5⟩ := J5.xtop.fin.1.1.1.lists
  obtain ⟨x6, hk6, -, -, hscw5, -⟩ := hsp5.tcb i hiT
  rw [hk5] at hk6; cases hk6
  obtain ⟨x6', hk6', hTR5⟩ := (J5.xtop.irelK J5.ks J5.buf).1.tcb i hiT
  rw [hk5] at hk6'; cases hk6'
  step with Fl4Proofs.P1.obj.Tcb.sc.spec as ⟨i3, hi3⟩
  rw [← hi3] at hscw5
  have h3 : i3 ≠ 0#u64 := by
    intro e; rw [e, optRef_zero] at hscw5; rw [hsc3] at hscw5; cases hscw5
  have e3 : i3 = i2 := by
    rw [Notif.optRef_ne h3] at hscw5; rw [hsc3] at hscw5
    exact P1.eq_of_bv (Option.some.inj hscw5).symm
  subst e3
  step with Fl4Proofs.P3.Sched.obj.Sc.is_null.spec' as ⟨b2, hb2⟩
  rw [hb2, if_neg (by simp [h3])]
  refine WP.spec_bind (Fl4Proofs.P3.Sched.is_runnable_spec s5 i) ?_
  rintro b3 rfl
  have hrw : L.mem s5 (tStA i) = sched.TS_RUNNING := by
    apply UScalar.eq_of_val_eq; rw [hTR5.st]; unfold sched.TS_RUNNING; rfl
  rw [if_pos (by simp [hrw])]
  have hS5 := J5.xtop.fin.1.1.1
  have hne5 : y.scRefills ≠ [] := J5.inv.ne _ y n hky5 hya
  refine WP.spec_bind (Fl4Proofs.P3.Sched.ready_refines s5 σ5 hS5 hi2C hky5 hya) ?_
  rintro b4 hb4
  rw [Fl4Proofs.P3.Sched.getScRefillReady_eq hky5 hne5] at hb4
  have hb4' : b4 = Fl4Spec.refillReady σ5.curTime (Fl4Spec.refillHd y) := by
    have := congrArg (fun q => (b4, σ5) ∈ q.1) hb4; simpa using this.symm
  rw [if_pos (by rw [hb4', htm5]; exact hrdy)]
  refine WP.spec_bind (Fl4Proofs.P3.Sched.sufficient_refines s5 _ σ5 hS5 hi2C hky5 hya 0#u64 (hmb _)) ?_
  rintro b5 hb5
  rw [Fl4Proofs.P3.Sched.getScRefillSufficient_eq hky5 hne5] at hb5
  have hb5' : b5 = Fl4Spec.refillSufficient (U64.bv 0#u64) (Fl4Spec.refillHd y) := by
    have := congrArg (fun q => (b5, σ5) ∈ q.1) hb5; simpa using this.symm
  rw [if_pos (by rw [hb5', e0]; exact hsuf)]
  refine WP.spec_bind (J5.switchJ hiT hti5 htc5 hsch) ?_
  rintro s6 ⟨σ6, hps, Lst6, J6⟩
  apply (WP.spec_ok _).2
  have hz1 : ((), σ5) ∈ ((Fl4Spec.doIpcTransfer (Z := Unit) ct.bv none 0 g i.bv >>= fun _ =>
      Fl4Spec.setThreadState i.bv .running) σ2).1 := by
    rw [nd_bind_one htr, Notif.setThreadState_eq _ hk3]; rfl
  have hz : ((), σ6) ∈ (specReplyTail i.bv xi.tcbFault σ5).1 := by
    rw [specReplyTail_run hk5 hsc3 rfl hky5, if_pos ⟨by rw [htm5]; exact hrdy, hsuf⟩, hps]
    exact Set.mem_singleton _
  exact ⟨((), σ6), mem_doReplyTransfer hkr hrep hkx hst g hrm hub hki (Or.inl ⟨hfi, hz1⟩) hz,
    _, _, _, _, _, _, J6⟩

/-- The third case of the rest of `do_reply_transfer` proved at `J`
(`replyRestPostJ`), after `reply_remove` (`σ2`): the receiver `i` has an
active SC `sp` that is not released (not ready or not
sufficient) and no valid timeout handler, no fault; the transfer `XferOK`.
The tail then postpones the SC. -/
def ReplyRestPost (σ2 : Fl4Spec.State Unit) (ct i : U64) (g : Bool) : Prop :=
  ∃ xs xi sp y n, σ2.kheap ct.bv = some (.tcb xs) ∧ σ2.kheap i.bv = some (.tcb xi) ∧
    xi.tcbSchedContext = some sp ∧ σ2.kheap sp = some (.schedContext y n) ∧
    Fl4Spec.scActive y = true ∧ ¬ (Fl4Spec.refillReady σ2.curTime (Fl4Spec.refillHd y) = true ∧
      Fl4Spec.refillSufficient 0 (Fl4Spec.refillHd y) = true) ∧
    Fl4Spec.isEpCap xi.tcbTimeoutHandler = false ∧
    xi.tcbFault = none ∧ XferOK xs g

set_option maxHeartbeats 16000000 in
/-- **The rest of `do_reply_transfer` at `J`, for `ReplyRestPost`**: the
sporadic unblock test done, the transfer (`JAtZ.xferAnyJ`), then `Running` and the
tail's `postpone` as one step (`JAtZ.runPostJ`): the tail's reads at the
state between (its SC, runnable, the ready and sufficient tests not both
true, no valid timeout handler: `valid_timeout_handler_rel`) on `XTopAt`
there. -/
theorem replyRestPostJ (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hZ : ∀ (Z' : XSets) (s' : S) (a' : A) σ', Z'.th = Z.th → XTopAt (L := L) AR Z' s' a' σ' →
      Endp.IpcBufCapOK σ' ∧ Endp.BufCover Z'.T Z'.B σ' ∧ Vs.BufPlaced (L := L) Z'.N Z'.C Z'.B Z'.c s' σ')
    {s2 : S} {ar : A} {σ1 σ0 σ2 : Fl4Spec.State Unit} (J2 : JAtZ (L := L) arI AR Z H Cs Ac Lst D s2 ar σ2)
    {ct i p : U64} (g : Bool) (hne : ct ≠ i) (hiD : i ∉ D) (hct2 : σ2.curThread = ct.bv)
    {xr : Fl4Spec.Reply} (hkr : σ1.kheap p.bv = some (.reply xr)) (hrep : xr.replyTcb = some i.bv)
    {x : Fl4Spec.Tcb} (hkx : σ1.kheap i.bv = some (.tcb x)) (hst : x.tcbState = .blockedOnReply p.bv)
    (hrm : Fl4Spec.replyRemove (Z := Unit) i.bv p.bv σ1 = ({((), σ0)}, False))
    (hub : (Fl4Spec.getTcbObjRef (Z := Unit) Fl4Spec.Tcb.tcbSchedContext i.bv >>=
      Fl4Spec.ifSporadicCurScTestRefillUnblockCheck) σ0 = ({((), σ2)}, False))
    (hin : ∃ x', σ2.kheap i.bv = some (.tcb x') ∧ x'.tcbState = .inactive)
    (hC : ReplyRestPost σ2 ct i g) :
    fl4ReplyRest2 st arI s2 ar ct i g ⦃ res => ∃ z ∈ (Fl4Spec.doReplyTransfer (Z := Unit) ct.bv p.bv g σ1).1,
      JAt (L := L) arI AR res.1 res.2 z.2 ⦄ := by
  obtain ⟨xs, xi, sp, y, n, hks, hki, hxsc, hky, hya, hnrel, hvt, hfi, hok⟩ := hC
  obtain ⟨xi', hki', hin⟩ := hin
  rw [hki] at hki'; cases hki'
  have hI := J2.xtop.irelK J2.ks J2.buf
  have hiT : i ∈ Z.T := by
    obtain ⟨t, ht, h⟩ := J2.obj.tcb _ xi hki
    rw [Sched.bv_inj h] at ht; exact ht
  have hcT : ct ∈ Z.T := by
    obtain ⟨t, ht, h⟩ := J2.obj.tcb _ xs hks
    rw [Sched.bv_inj h] at ht; exact ht
  obtain ⟨Q, R0, hc, hsp⟩ := J2.xtop.fin.1.1.1.lists
  obtain ⟨x0, hk0, -, -, hscw, -⟩ := hsp.tcb i hiT
  rw [hki] at hk0; cases hk0
  obtain ⟨x0', hk0', hTR⟩ := hI.1.tcb i hiT
  rw [hki] at hk0'; cases hk0'
  unfold fl4ReplyRest2
  obtain ⟨i2, hi2⟩ : ∃ i2 : U64, i2 = L.mem s2 (P1.scA i) := ⟨_, rfl⟩
  rw [← hi2] at hscw
  have h0 : i2 ≠ 0#u64 := by
    intro e; rw [e, optRef_zero, hxsc] at hscw; cases hscw
  have esp : sp = i2.bv := by rw [Notif.optRef_ne h0, hxsc] at hscw; exact Option.some.inj hscw
  subst esp
  have hi2C : i2 ∈ Z.C := by rw [hi2]; exact hsp.scMem i hiT (by rw [← hi2]; exact h0)
  obtain ⟨y', n', hky', hy⟩ := hsp.scs i2 hi2C
  rw [hky] at hky'; cases hky'
  step with Fl4Proofs.P3.Endp.obj.Tcb.fault_type.spec as ⟨ft, hft⟩
  have hft0 : ft = 0#u64 := by rw [hft]; exact hTR.fault0.2 hfi
  rw [if_pos (by rw [hft0]; unfold fl4_abi.consts.fault.NullFault; rfl)]
  have e0 : U64.bv 0#u64 = (0 : Fl4Spec.Word) := rfl
  have hti : i2.bv ≠ i.bv := fun e => by rw [e, hki] at hky; cases hky
  refine WP.spec_bind (Pₘ := fun res => res.2 = ar ∧ ∃ (σ3 : Fl4Spec.State Unit) (x3 : Fl4Spec.Tcb) (V : XVs),
      Fl4Spec.doIpcTransfer (Z := Unit) ct.bv none 0 g i.bv σ2 = ({((), σ3)}, False) ∧
      σ3.kheap i.bv = some (.tcb x3) ∧ x3.tcbSchedContext = some i2.bv ∧ x3.tcbFault = none ∧
      x3.tcbTimeoutHandler = xi.tcbTimeoutHandler ∧
      (∀ q, q ≠ i.bv → σ3.kheap q = σ2.kheap q) ∧
      XTopAt (L := L) AR (Z.mv Z.G V) res.1 ar
        (stsAct (updK σ3 i.bv (.tcb { x3 with tcbState := .running })) i.bv) ∧
      sched.postpone st res.1 i2 ⦃ s7 => ∃ σ7, Fl4Spec.postpone (Z := Unit) i2.bv
          (stsAct (updK σ3 i.bv (.tcb { x3 with tcbState := .running })) i.bv) = ({((), σ7)}, False) ∧
        ∃ Lst' : U64 → List U64, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst' D s7 ar σ7 ⦄) ?_ ?_
  · refine WP.spec_bind (J2.xferAnyJ hZ hcT hiT hne hks hki hok none 0#u64 0#u64) ?_
    rintro s4 ⟨σ3, htr, hkp3, ⟨x3, hk3, hx3⟩, V, J3⟩
    rw [e0] at htr
    have mem3 : ((), σ3) ∈ (Fl4Spec.doIpcTransfer (Z := Unit) ct.bv none 0 g i.bv σ2).1 := by
      rw [htr]; exact Set.mem_singleton _
    have hs3 : x3.tcbState = .inactive := (congrArg Fl4Spec.Tcb.tcbState hx3).trans hin
    have hsc3 : x3.tcbSchedContext = some i2.bv := (congrArg Fl4Spec.Tcb.tcbSchedContext hx3).trans hxsc
    have hf3 : x3.tcbFault = none := (congrArg Fl4Spec.Tcb.tcbFault hx3).trans hfi
    have hth3 : x3.tcbTimeoutHandler = xi.tcbTimeoutHandler := (congrArg Fl4Spec.Tcb.tcbTimeoutHandler hx3).trans rfl
    have hky3 : σ3.kheap i2.bv = some (.schedContext y n) := by rw [hkp3 _ hti]; exact hky
    have htm3 : σ3.curTime = σ2.curTime := (SVK.sv_doIpcTransfer' _ _ _ _ _ σ2 _ mem3).2.1
    have hct3 : i.bv ≠ σ3.curThread := by
      rw [(dk_doIpcTransfer' _ _ _ _ _).ct mem3, hct2]; intro e; exact hne (P1.eq_of_bv e).symm
    refine WP.spec_bind (J3.runPostJ hiT hiD hk3 hs3 hct3 hi2C hsc3 hky3 hya (by rw [htm3]; exact hnrel)) ?_
    rintro s5 ⟨hX5, -, hpost⟩
    exact (WP.spec_ok _).2 ⟨rfl, σ3, x3, V, htr, hk3, hsc3, hf3, hth3, hkp3, hX5, hpost⟩
  rintro ⟨s5, a2⟩ ⟨ha, σ3, x3, V, htr, hk3, hsc3, hf3, hth3, hkp3, hX5, hpost⟩
  simp only at ha
  subst ha
  have mem3 : ((), σ3) ∈ (Fl4Spec.doIpcTransfer (Z := Unit) ct.bv none 0 g i.bv σ2).1 := by
    rw [htr]; exact Set.mem_singleton _
  set x5 : Fl4Spec.Tcb := { x3 with tcbState := .running } with hx5
  set σ4 := updK σ3 i.bv (.tcb x5) with hσ4
  set σ5 := stsAct σ4 i.bv with hσ5
  have hrec : σ5 = { σ4 with schedulerAction := σ5.schedulerAction } := stsAct_rec σ4 i.bv
  have hk5 : σ5.kheap i.bv = some (.tcb x5) := by rw [hσ5, stsAct_kheap]; simp [hσ4, updK]
  have hky5 : σ5.kheap i2.bv = some (.schedContext y n) := by
    rw [hσ5, stsAct_kheap, hσ4]; simp only [updK, Function.update_of_ne hti]; rw [hkp3 _ hti]; exact hky
  have htm5 : σ5.curTime = σ2.curTime := by
    rw [hrec]; exact (SVK.sv_doIpcTransfer' _ _ _ _ _ σ2 _ mem3).2.1
  have hS5 := hX5.fin.1.1.1
  obtain ⟨Q5, R5, hc5, hsp5⟩ := hS5.lists
  obtain ⟨x6, hk6, -, -, hscw5, -⟩ := hsp5.tcb i hiT
  rw [hk5] at hk6; cases hk6
  obtain ⟨x6', hk6', hTR5⟩ := hX5.ipc.tcb i hiT
  rw [hk5] at hk6'; cases hk6'
  step with Fl4Proofs.P1.obj.Tcb.sc.spec as ⟨i3, hi3⟩
  rw [← hi3] at hscw5
  have h3 : i3 ≠ 0#u64 := by
    intro e; rw [e, optRef_zero] at hscw5; rw [hsc3] at hscw5; cases hscw5
  have e3 : i3 = i2 := by
    rw [Notif.optRef_ne h3] at hscw5; rw [hsc3] at hscw5
    exact P1.eq_of_bv (Option.some.inj hscw5).symm
  subst e3
  step with Fl4Proofs.P3.Sched.obj.Sc.is_null.spec' as ⟨b2, hb2⟩
  rw [hb2, if_neg (by simp [h3])]
  refine WP.spec_bind (Fl4Proofs.P3.Sched.is_runnable_spec s5 i) ?_
  rintro b3 rfl
  have hrw : L.mem s5 (tStA i) = sched.TS_RUNNING := by
    apply UScalar.eq_of_val_eq; rw [hTR5.st]; unfold sched.TS_RUNNING; rfl
  rw [if_pos (by simp [hrw])]
  have hne5 : y.scRefills ≠ [] := J2.inv.ne _ y n hky hya
  -- the spec's outcome
  have hz1 : ((), σ5) ∈ ((Fl4Spec.doIpcTransfer (Z := Unit) ct.bv none 0 g i.bv >>= fun _ =>
      Fl4Spec.setThreadState i.bv .running) σ2).1 := by
    rw [nd_bind_one htr, Notif.setThreadState_eq _ hk3]; rfl
  have hvt5 : Fl4Spec.isEpCap x5.tcbTimeoutHandler = false := by
    show Fl4Spec.isEpCap x3.tcbTimeoutHandler = false; rw [hth3]; exact hvt
  -- the timeout branch: no valid handler, so `postpone`
  have tmo : fl4ReplyTmo st arI i ft i3 s5 a2 ⦃ res => ∃ z ∈ (Fl4Spec.doReplyTransfer (Z := Unit) ct.bv p.bv g σ1).1,
      JAt (L := L) arI AR res.1 res.2 z.2 ⦄ := by
    unfold fl4ReplyTmo
    refine WP.spec_bind (valid_timeout_handler_rel s5 σ5 hX5.rel.2.1.1 (hX5.rel.tcbT hk5)) ?_
    rintro b5 ⟨-, x', hkx', hb5⟩
    rw [hk5] at hkx'; cases hkx'
    rw [if_neg (by rw [hb5, hvt5]; simp)]
    refine WP.spec_bind hpost ?_
    rintro s7 ⟨σ7, hpp, Lst7, J7⟩
    apply (WP.spec_ok _).2
    have hz : ((), σ7) ∈ (specReplyTail i.bv xi.tcbFault σ5).1 := by
      rw [specReplyTail_run hk5 hsc3 rfl hky5, if_neg (by rw [htm5]; exact hnrel)]
      unfold specReplyTmo
      rw [nd_bind_one (getTcb_eq hk5), if_neg (fun h => by rw [hvt5] at h; exact Bool.false_ne_true h.1), hpp]
      exact Set.mem_singleton _
    exact ⟨((), σ7), mem_doReplyTransfer hkr hrep hkx hst g hrm hub hki (Or.inl ⟨hfi, hz1⟩) hz,
      _, _, _, _, _, _, J7⟩
  unfold fl4ReplyTmo at tmo
  refine WP.spec_bind (Fl4Proofs.P3.Sched.ready_refines s5 σ5 hS5 hi2C hky5 hya) ?_
  rintro b4 hb4
  rw [Fl4Proofs.P3.Sched.getScRefillReady_eq hky5 hne5] at hb4
  have hb4' : b4 = Fl4Spec.refillReady σ5.curTime (Fl4Spec.refillHd y) := by
    have := congrArg (fun q => (b4, σ5) ∈ q.1) hb4; simpa using this.symm
  by_cases hr4 : b4 = true
  · rw [if_pos hr4]
    refine WP.spec_bind (Fl4Proofs.P3.Sched.sufficient_refines s5 _ σ5 hS5 hi2C hky5 hya 0#u64 (hmb _)) ?_
    rintro b5 hb5
    rw [Fl4Proofs.P3.Sched.getScRefillSufficient_eq hky5 hne5] at hb5
    have hb5' : b5 = Fl4Spec.refillSufficient (U64.bv 0#u64) (Fl4Spec.refillHd y) := by
      have := congrArg (fun q => (b5, σ5) ∈ q.1) hb5; simpa using this.symm
    have hr5 : ¬ b5 = true := fun h => hnrel ⟨by rw [← htm5, ← hb4']; exact hr4, by rw [← e0, ← hb5']; exact h⟩
    rw [if_neg hr5]
    exact tmo
  · rw [if_neg hr4]
    exact tmo

variable (arI) in
/-- **[W] The reply cap's transfer after `reply_remove` and the sporadic
unblock test, at `J`** (`replyLeafJ`): from the caller's restart (`s1`,
`σ1`) and a receiver `i` blocked on the reply `p`, `reply_remove` (`σ2`) and
the spec's unblock test (`σ3`; FL4's at `J` by `JAtZ.replyUnblockJ`), FL4's
rest of `do_reply_transfer` (`fl4ReplyRest2`) from a `JAt` state at `σ3`
ends at `JAt` with an outcome of the spec's `do_reply_transfer` from `σ1`,
outside `ReplyRestNoSc` (`replyRestNoScJ`: no SC and no fault on the
receiver, the transfer `XferOK`), `ReplyRestSw` (`replyRestSwJ`: the
receiver's SC active and released, then `possible_switch_to`) and
`ReplyRestPost` (`replyRestPostJ`: the SC active, not released, no valid
timeout handler, `Running` and `postpone` as one step). The restart, the
reply's thread, the branches where nothing happens, `reply_remove`
(`JAtZ.replyRemoveJD`) and the unblock test are proved, and an SC bound to
the receiver is active (given: `remove_act` from `BlockedScActive` before
`reply_remove`, the unblock test keeping `REFILL_MAX`; so no case with a
bound inactive SC is left). What is left are J
steps with an `IRel` proof but none at `J` (IpcReply's
`do_reply_transfer_top`): with an SC not released and a valid timeout
handler, `Running` together with `handle_timeout` (`ReplyHyps.tmo`: a fault
send); `do_ipc_transfer` with granted caps (`ReplyHyps.grantXfer`) or from
a replier with a timeout fault and an SC (`do_fault_transfer` is at `J`,
XTopJointFault's `JAtZ.xferFaultJ`, but needs the platform's `ticks_to_us`
[P], not in JEntryGlob); the fault reply
(`ReplyHyps.faultReply`). l4v: `do_reply_transfer_invs` /
`do_reply_transfer_corres`. -/
def JReplyRestHyp (AR : A → Fl4Spec.Cr3 → Prop) (s1 : S) (ar : A) (σ1 : Fl4Spec.State Unit) (ct p : U64) (g : Bool) :
    Prop :=
  ∀ (i : U64) (x : Fl4Spec.Tcb) (s2 : S) (σ2 : Fl4Spec.State Unit) (s3 : S) (σ3 : Fl4Spec.State Unit),
    L.mem s1 (rTcbA p) = i → σ1.kheap i.bv = some (.tcb x) → x.tcbState = .blockedOnReply p.bv →
    ipc.reply_remove st arI s1 ar p i = ok (s2, ar) →
    Fl4Spec.replyRemove (Z := Unit) i.bv p.bv σ1 = ({((), σ2)}, False) →
    (Fl4Spec.getTcbObjRef (Z := Unit) Fl4Spec.Tcb.tcbSchedContext i.bv >>=
      Fl4Spec.ifSporadicCurScTestRefillUnblockCheck) σ2 = ({((), σ3)}, False) →
    JAt (L := L) arI AR s3 ar σ3 →
    (∀ q y n, σ3.kheap q = some (.schedContext y n) → y.scTcb = some i.bv → Fl4Spec.scActive y = true) →
    ¬ ReplyRestNoSc σ3 ct i g → ¬ ReplyRestSw σ3 ct i g →
    ¬ ReplyRestPost σ3 ct i g →
    fl4ReplyRest2 st arI s3 ar ct i g ⦃ res => ∃ z ∈ (Fl4Spec.doReplyTransfer (Z := Unit) ct.bv p.bv g σ1).1,
      JAt (L := L) arI AR res.1 res.2 z.2 ⦄

set_option maxHeartbeats 8000000 in
/-- **`do_reply_transfer` at `J`** but for `JReplyRestHyp`: no thread on the
reply, or a thread not blocked on it, nothing happens on either side; a
thread blocked on it, `reply_remove` at `J` (`JAtZ.replyRemoveJD`), then
`replyRestNoScJ` or `JReplyRestHyp`. -/
theorem replyXferJ (hAT : P0.ArchTotal arI)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hZ : ∀ (Z' : XSets) (s' : S) (a' : A) σ', Z'.th = Z.th → XTopAt (L := L) AR Z' s' a' σ' →
      Endp.IpcBufCapOK σ' ∧ Endp.BufCover Z'.T Z'.B σ' ∧ Vs.BufPlaced (L := L) Z'.N Z'.C Z'.B Z'.c s' σ')
    {s1 : S} {ar : A} {σ1 : Fl4Spec.State Unit}
    (J1 : JAtZ (L := L) arI AR Z H Cs Ac Lst D s1 ar σ1) {ct p : U64} (hp : p ∈ Z.R) (g : Bool)
    (hcs : σ1.curThread = ct.bv ∧ ∃ xc, σ1.kheap ct.bv = some (.tcb xc) ∧ xc.tcbState = .restart)
    (hR : JReplyRestHyp (L := L) arI AR s1 ar σ1 ct p g) :
    ipc.do_reply_transfer st arI s1 ar ct p g ⦃ res =>
      ∃ z ∈ (Fl4Spec.doReplyTransfer (Z := Unit) ct.bv p.bv g σ1).1, JAt (L := L) arI AR res.1 res.2 z.2 ⦄ := by
  have hJ1 : JAt (L := L) arI AR s1 ar σ1 := ⟨_, _, _, _, _, _, J1⟩
  have hI := J1.xtop.irelK J1.ks J1.buf
  obtain ⟨xr, hkr, hxr⟩ := hI.1.reply p hp
  unfold ipc.do_reply_transfer
  step with Fl4Proofs.P3.Endp.obj.Reply.tcb.spec as ⟨i, hi⟩
  step with Fl4Proofs.P1.obj.Tcb.is_null.spec as ⟨b, hb⟩
  by_cases h0 : i = 0#u64
  · rw [hb, if_pos (by simp [h0]), WP.spec_ok]
    exact ⟨((), σ1), by rw [doReplyTransfer_none hkr (by rw [hxr, ← hi, h0, optRef_zero])]; rfl, hJ1⟩
  rw [hb, if_neg (by simp [h0])]
  have hrep : xr.replyTcb = some i.bv := by rw [hxr, ← hi, Notif.optRef_ne h0]
  obtain ⟨x, hkx, hxs⟩ := J1.sv.replyTcb p.bv xr i.bv hkr hrep
  have hiT : i ∈ Z.T := by
    obtain ⟨t, ht, h⟩ := J1.obj.tcb _ x hkx
    rw [Sched.bv_inj h] at ht; exact ht
  obtain ⟨x0, hk0, hTR⟩ := hI.1.tcb i hiT
  rw [hkx] at hk0; cases hk0
  step with Fl4Proofs.P3.Notif.obj.Tcb.state.spec as ⟨i1, hi1⟩
  rcases hxs with hst | ⟨ep, d, hst⟩
  swap
  · -- receiving with the reply: nothing happens
    have hne : (i1 != sched.TS_BLOCKED_ON_REPLY) = true := by
      have h := hTR.st
      rw [hst] at h
      rw [hi1]
      have : L.mem s1 (tStA i) ≠ sched.TS_BLOCKED_ON_REPLY := by
        intro e; rw [e] at h; unfold sched.TS_BLOCKED_ON_REPLY at h; simp [tsCode] at h
      simpa using this
    rw [if_pos hne, WP.spec_ok]
    refine ⟨((), σ1), ?_, hJ1⟩
    rw [doReplyTransfer_notReply hkr hrep hkx (by rw [hst]; intro r' h; cases h)]; rfl
  have hne : (i1 != sched.TS_BLOCKED_ON_REPLY) = false := by
    have h := hTR.st
    rw [hst] at h
    rw [hi1]
    have : L.mem s1 (tStA i) = sched.TS_BLOCKED_ON_REPLY := by
      apply UScalar.eq_of_val_eq; rw [h]; unfold sched.TS_BLOCKED_ON_REPLY; rfl
    simp [this]
  rw [if_neg (by rw [hne]; simp)]
  have hiD : i ∉ D := fun h => J1.notDead hiT hkx (by rw [hst]; simp [tsCode]) i h rfl
  have hne : ct ≠ i := by
    rintro rfl
    obtain ⟨xc, hkc, hcr⟩ := hcs.2
    rw [hkc] at hkx; cases hkx; rw [hcr] at hst; cases hst
  obtain ⟨⟨s2, a2⟩, hrr, hpost⟩ := spec_exists (J1.replyRemoveJD hAT hp hiT hkx hst)
  obtain ⟨ea, σ2, V', Ac', Lst', D', hrm, J2, -, -, hDD, hin, hact⟩ := hpost
  simp only at ea
  subst ea
  subst hDD
  rw [hrr]
  simp only [bind_ok]
  have hct2 : σ2.curThread = ct.bv := by
    rw [(Vs.dk_replyRemove' i.bv p.bv).ct (x := ((), σ2)) (by rw [hrm]; exact Set.mem_singleton _)]
    exact hcs.1
  obtain ⟨xi0, hki0, hin0⟩ := hin
  suffices key : fl4ReplyRest st arI s2 a2 ct i g ⦃ res => ∃ z ∈ (Fl4Spec.doReplyTransfer (Z := Unit) ct.bv p.bv g σ1).1,
      JAt (L := L) arI AR res.1 res.2 z.2 ⦄ from key
  rw [fl4ReplyRest_eq]
  refine J2.replyUnblockJ hiT hki0 hin0 (fun s3 => fl4ReplyRest2 st arI s3 a2 ct i g) _ ?_
  intro s3 σ3 Lst3 hub J3 htk hct3 hscK
  -- the receiver's SC is active (`replyRemoveJD`'s `remove_act`, kept by the unblock test)
  have hact3 : ∀ q y n, σ3.kheap q = some (.schedContext y n) → y.scTcb = some i.bv →
      Fl4Spec.scActive y = true := by
    intro q y n hq hyt
    obtain ⟨y0, hq0, hm, htc⟩ := hscK q y n hq
    have h0 := hact q y0 n hq0 (htc.symm.trans hyt)
    show Fl4Spec.activeSc y.scRefillMax = true
    rw [hm]; exact h0
  have hin3 : ∃ x', σ3.kheap i.bv = some (.tcb x') ∧ x'.tcbState = .inactive := ⟨xi0, htk _ _ hki0, hin0⟩
  have hct3' : σ3.curThread = ct.bv := hct3.trans hct2
  by_cases hC : ReplyRestNoSc σ3 ct i g
  · exact replyRestNoScJ (Z := Z.mv Z.G V') hZ J3 g hne hiD hkr hrep hkx hst hrm hub hin3 hC
  by_cases hC2 : ReplyRestSw σ3 ct i g
  · exact replyRestSwJ (Z := Z.mv Z.G V') hmb hZ J3 g hne hiD hct3' hkr hrep hkx hst hrm hub hin3 hC2
  by_cases hC3 : ReplyRestPost σ3 ct i g
  · exact replyRestPostJ (Z := Z.mv Z.G V') hmb hZ J3 g hne hiD hct3' hkr hrep hkx hst hrm hub hin3 hC3
  exact hR i x s2 σ2 s3 σ3 hi.symm hkx hst hrr hrm hub ⟨_, _, _, _, _, _, J3⟩ hact3 hC hC2 hC3

set_option maxHeartbeats 4000000 in
/-- **The reply cap's leaf at `J`** but for `JReplyRestHyp` (`replyXferJ`
after the caller's restart, `JAtZ.restartJ`; the cap's reply in `R`,
`JAtZ.slotR`). -/
theorem replyLeafJ (hAT : P0.ArchTotal arI)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hZ : ∀ (Z' : XSets) (s' : S) (a' : A) σ', Z'.th = Z.th → XTopAt (L := L) AR Z' s' a' σ' →
      Endp.IpcBufCapOK σ' ∧ Endp.BufCover Z'.T Z'.B σ' ∧ Vs.BufPlaced (L := L) Z'.N Z'.C Z'.B Z'.c s' σ')
    {s : S} {ar : A} {σ σ1 : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) {ct : U64} (hct : sched.cur_thread st s = ok ct)
    {sl : Fl4Spec.CslotPtr} (hA : AbsSlot Z.th sl) {p : U64} {g : Bool}
    (hc : capAt (L.mem s) (cslotAddr sl) = ok (.Reply p g))
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (hR : ∀ s1 σ1', sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1')}, False) →
      JReplyRestHyp (L := L) arI AR s1 ar σ1' ct p g) :
    XLeaf (L := L) (JAt (L := L) arI AR) s ar σ (do
        let s1 ← sched.set_thread_state st s ct sched.TS_RESTART
        let (s2, a1) ← ipc.do_reply_transfer st arI s1 ar ct p g
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a1))
      (Fl4Spec.doReplyTransfer (Z := Unit) σ1.curThread p.bv g σ1) := by
  intro _
  have hpR := J.slotR hA hc
  obtain ⟨s1, σ1', x, -, hst1, -, hcur, hσe, -, -, hcur1, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  obtain rfl := restart_out_eq hst1 hst
  have hc1 : σ1'.curThread = ct.bv := hcur1.trans hcur
  have hcs : σ1'.curThread = ct.bv ∧ ∃ xc, σ1'.kheap ct.bv = some (.tcb xc) ∧ xc.tcbState = .restart :=
    ⟨hc1, { x with tcbState := .restart }, by rw [hσe, stsAct_kheap]; simp [updK], rfl⟩
  rw [hs1]
  simp only [bind_ok]
  rw [hc1]
  refine WP.spec_bind (replyXferJ hAT hmb hZ J1 hpR g hcs (hR s1 σ1' hs1 hst1)) ?_
  rintro ⟨s2, a2⟩ ⟨z, hz, Z', H', Cs', Ac', Lst', D', J'⟩
  apply (WP.spec_ok _).2
  exact ⟨rfl, z, hz, J'.xtop.relTop, Z', H', Cs', Ac', Lst', D', J'⟩


variable (arI) in
/-- **[W] The endpoint cap's `send_ipc` at `J` where it blocks or meets a
receiver** (`sendLeafJ`): after the caller's restart (`s1`, `σ1`), a
blocking send, or one to an endpoint with receivers, ends at `JAt` with an
outcome of the spec's `send_ipc`. The restart and a non-blocking send to an
endpoint without receivers (nothing happens, `send_ipc_noblock`) are proved.
What is left has an `IRel` proof (IpcLeaves's `send_ipc_top`: the block,
`send_ipc_blockI`; the receiver's dequeue, `do_ipc_transfer`, the reply
push or the caller's block, the SC donation and the switch,
`send_ipc_recvG` / `send_ipc_callX_gen`, `SendRest`) but no J frame. l4v:
`send_ipc_invs` / `send_ipc_corres`. -/
def JSendRestHyp (AR : A → Fl4Spec.Cr3 → Prop) (s1 : S) (ar : A) (σ1 : Fl4Spec.State Unit)
    (blk call : Bool) (b : U64) (g gr don : Bool) (ct p : U64) : Prop :=
  ∀ x : Fl4Spec.Endpoint, σ1.kheap p.bv = some (.endpoint x) → (blk = true ∨ ¬ CanBlock false x) →
    endpoint.send_ipc st arI s1 ar blk call b g gr don ct p ⦃ r =>
      ∃ z ∈ (Fl4Spec.sendIpc (Z := Unit) blk call b.bv g gr don ct.bv p.bv σ1).1, JAt (L := L) arI AR r.1 r.2 z.2 ⦄

set_option maxHeartbeats 4000000 in
/-- **`send_ipc` at `J`** but for `JSendRestHyp` (a non-blocking send to an
endpoint without receivers: nothing happens on either side). -/
theorem sendXferJ {s1 : S} {ar : A} {σ1 : Fl4Spec.State Unit}
    (J1 : JAtZ (L := L) arI AR Z H Cs Ac Lst D s1 ar σ1) {ct p : U64} (hp : p ∈ Z.E)
    (blk call : Bool) (b : U64) (g gr don : Bool)
    (hR : JSendRestHyp (L := L) arI AR s1 ar σ1 blk call b g gr don ct p) :
    endpoint.send_ipc st arI s1 ar blk call b g gr don ct p ⦃ r =>
      ∃ z ∈ (Fl4Spec.sendIpc (Z := Unit) blk call b.bv g gr don ct.bv p.bv σ1).1, JAt (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  have hJ1 : JAt (L := L) arI AR s1 ar σ1 := ⟨_, _, _, _, _, _, J1⟩
  have hI := J1.xtop.irelK J1.ks J1.buf
  obtain ⟨x, hk, -⟩ := hI.1.ep p hp
  by_cases hnb : blk = false ∧ CanBlock false x
  · obtain ⟨rfl, hc⟩ := hnb
    refine WP.spec_mono (send_ipc_noblock (ar := arI) s1 ar σ1 hI.1.toE hp hk hc call b g gr don ct) ?_
    rintro r ⟨rfl, h2⟩
    exact ⟨((), σ1), by rw [h2]; exact Set.mem_singleton _, hJ1⟩
  refine hR x hk ?_
  cases blk
  · exact Or.inr fun h => hnb ⟨rfl, h⟩
  · exact Or.inl rfl

set_option maxHeartbeats 4000000 in
/-- **The endpoint cap's leaf at `J`** but for `JSendRestHyp` (`sendXferJ`
after the caller's restart, `JAtZ.restartJ`; the cap's endpoint in `E`,
`JAtZ.slotE`). -/
theorem sendLeafJ {s : S} {ar : A} {σ σ1 : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) {ct : U64} (hct : sched.cur_thread st s = ok ct)
    {sl : Fl4Spec.CslotPtr} (hA : AbsSlot Z.th sl) {p b : U64} {x1 x2 x3 x4 : Bool}
    (hc : capAt (L.mem s) (cslotAddr sl) = ok (.Endpoint p b x1 x2 x3 x4))
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (blk call : Bool) (g gr don : Bool)
    (hR : ∀ s1 σ1', sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1')}, False) →
      JSendRestHyp (L := L) arI AR s1 ar σ1' blk call b g gr don ct p) :
    XLeaf (L := L) (JAt (L := L) arI AR) s ar σ (do
        let s1 ← sched.set_thread_state st s ct sched.TS_RESTART
        let (s2, a1) ← endpoint.send_ipc st arI s1 ar blk call b g gr don ct p
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a1))
      (Fl4Spec.sendIpc (Z := Unit) blk call b.bv g gr don σ1.curThread p.bv σ1) := by
  intro _
  have hpE := J.slotE hA hc
  obtain ⟨s1, σ1', x, -, hst1, -, hcur, -, -, -, hcur1, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  obtain rfl := restart_out_eq hst1 hst
  have hc1 : σ1'.curThread = ct.bv := hcur1.trans hcur
  rw [hs1]
  simp only [bind_ok]
  rw [hc1]
  refine WP.spec_bind (sendXferJ J1 hpE blk call b g gr don (hR s1 σ1' hs1 hst1)) ?_
  rintro ⟨s2, a2⟩ ⟨z, hz, Z', H', Cs', Ac', Lst', D', J'⟩
  apply (WP.spec_ok _).2
  exact ⟨rfl, z, hz, J'.xtop.relTop, Z', H', Cs', Ac', Lst', D', J'⟩

end

end

end Fl4Proofs.P3
