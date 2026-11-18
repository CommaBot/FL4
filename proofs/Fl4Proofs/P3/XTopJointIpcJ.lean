/-
P3 (DESIGN.md §9): **the IPC caps' leaves at `J`** (XTopJointEntry's
`JPath` for the Endpoint, Notification and Reply caps): the caller's
restart, then FL4's `send_signal` / `do_reply_transfer` / `send_ipc`,
against the spec's, from `JAtZ` at the invocation to `JAt` after.

* `notifLeafJ`: the caller's restart at `J` (`JAtZ.restartJ`), the cap's
  notification one of `N` (`JAtZ.slotN`), then ScSignalJ's `SignalJHyp`
  (`signalJHyp_of`: from `SignalRestJHyp` [J], the bound thread
  `RunningVM`, VT-x; `RecvReplyLinksHyp` [J]; the platform's `MIN_BUDGET`
  [P]).
* `replyLeafJ`: the restart, then `replyXferJ`: `do_reply_transfer` at `J`
  where nothing happens (no thread on the reply, or one not blocked on it)
  and `reply_remove` (`JAtZ.replyRemoveJ`), the rest after it named
  (`JReplyRestHyp` [W]).
-/
import Fl4Proofs.P3.XTopJointTcb
import Fl4Proofs.P3.ScSignalJ
import Fl4Proofs.P3.JProducers
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
    (hRR : RecvReplyLinksHyp (L := L) arI AR H Cs)
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
  refine WP.spec_bind (signalJHyp_of hAT hW hRR hmb Z Ac1 Lst1 D1 s1 ar σ1' p b J1 hpN) ?_
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

variable (arI) in
/-- **[W] The reply cap's transfer after `reply_remove`, at `J`** (`replyLeafJ`):
from the caller's restart (`s1`, `σ1`) and a receiver `i` blocked on the reply
`p`, FL4's rest of `do_reply_transfer` after `reply_remove` (`fl4ReplyRest`)
ends at `JAt` with an outcome of the spec's `do_reply_transfer` from `σ1`.
The restart, the reply's thread, the branches where nothing happens and
`reply_remove` (`JAtZ.replyRemoveJ`) are proved. What is left are J steps
with an `IRel` proof but none at `J` (IpcReply's `do_reply_transfer_top`):
the sporadic unblock test (`ReplyHyps.unblock`), `do_ipc_transfer` with no
endpoint (`reply_xfer_top`, `ReplyHyps.grantXfer`) and `Running` of the
inactive receiver, the fault reply (`ReplyHyps.faultReply`), the tail
(`reply_tail_top`: `possible_switch_to`, `ReplyHyps.tmo`). l4v:
`do_reply_transfer_invs` / `do_reply_transfer_corres`. -/
def JReplyRestHyp (AR : A → Fl4Spec.Cr3 → Prop) (s1 : S) (ar : A) (σ1 : Fl4Spec.State Unit) (ct p : U64) (g : Bool) :
    Prop :=
  ∀ (i : U64) (x : Fl4Spec.Tcb) (s2 : S) (σ2 : Fl4Spec.State Unit),
    L.mem s1 (rTcbA p) = i → σ1.kheap i.bv = some (.tcb x) → x.tcbState = .blockedOnReply p.bv →
    ipc.reply_remove st arI s1 ar p i = ok (s2, ar) →
    Fl4Spec.replyRemove (Z := Unit) i.bv p.bv σ1 = ({((), σ2)}, False) →
    JAt (L := L) arI AR s2 ar σ2 →
    fl4ReplyRest st arI s2 ar ct i g ⦃ res => ∃ z ∈ (Fl4Spec.doReplyTransfer (Z := Unit) ct.bv p.bv g σ1).1,
      JAt (L := L) arI AR res.1 res.2 z.2 ⦄

set_option maxHeartbeats 8000000 in
/-- **`do_reply_transfer` at `J`** but for `JReplyRestHyp`: no thread on the
reply, or a thread not blocked on it, nothing happens on either side; a
thread blocked on it, `reply_remove` at `J` (`JAtZ.replyRemoveJ`), then
`JReplyRestHyp`. -/
theorem replyXferJ (hAT : P0.ArchTotal arI) {s1 : S} {ar : A} {σ1 : Fl4Spec.State Unit}
    (J1 : JAtZ (L := L) arI AR Z H Cs Ac Lst D s1 ar σ1) {ct p : U64} (hp : p ∈ Z.R) (g : Bool)
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
  obtain ⟨⟨s2, a2⟩, hrr, hpost⟩ := spec_exists (J1.replyRemoveJ hAT hp hiT hkx hst)
  obtain ⟨ea, σ2, V', Ac', Lst', D', hrm, J2, -, -⟩ := hpost
  simp only at ea
  subst ea
  rw [hrr]
  simp only [bind_ok]
  exact hR i x s2 σ2 hi.symm hkx hst hrr hrm ⟨_, _, _, _, _, _, J2⟩

set_option maxHeartbeats 4000000 in
/-- **The reply cap's leaf at `J`** but for `JReplyRestHyp` (`replyXferJ`
after the caller's restart, `JAtZ.restartJ`; the cap's reply in `R`,
`JAtZ.slotR`). -/
theorem replyLeafJ (hAT : P0.ArchTotal arI)
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
  obtain ⟨s1, σ1', x, -, hst1, -, hcur, -, -, -, hcur1, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  obtain rfl := restart_out_eq hst1 hst
  have hc1 : σ1'.curThread = ct.bv := hcur1.trans hcur
  rw [hs1]
  simp only [bind_ok]
  rw [hc1]
  refine WP.spec_bind (replyXferJ hAT J1 hpR g (hR s1 σ1' hs1 hst1)) ?_
  rintro ⟨s2, a2⟩ ⟨z, hz, Z', H', Cs', Ac', Lst', D', J'⟩
  apply (WP.spec_ok _).2
  exact ⟨rfl, z, hz, J'.xtop.relTop, Z', H', Cs', Ac', Lst', D', J'⟩


end

end

end Fl4Proofs.P3
