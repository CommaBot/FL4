/-
P3 (DESIGN.md §9), IPC: **`do_reply_transfer`** (ipc.rs) against l4v
`do_reply_transfer` (Ipc_A), on `IRel` (`IpcRel ∧ SRT … SRE`),
`do_reply_transfer_top`:

* no thread on the reply, or a thread receiving with it (not
  `BlockedOnReply`): nothing happens on either side;
* a thread blocked on the reply (`SchedValid.replyTcb`): `reply_remove`, the
  sporadic unblock test, then without a fault the transfer from the replier
  (`endpoint = none`, badge 0; `reply_xfer_top`) and `Running`, with a fault
  the fault reply; then the tail (`reply_tail_top`: no SC or not runnable,
  nothing; ready and sufficient, `possible_switch_to`).
* `reply_tail_inv`, `decode_reply_top`: the reply-cap invocation
  (`set_thread_state Restart` then `do_reply_transfer`) for
  `handle_invocation_refinesMX`.

Named (`ReplyHyps`): `remove` (the call stack lives in the SC relation),
`unblock` (the sporadic test), `faultReply`, `grantXfer` (caps transferred
with no endpoint), `tmo` (the timeout branch of the tail: the
timeout-handler test, `handle_timeout`, `postpone`).
-/
import Fl4Proofs.P3.IpcLeaves
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Ipc

noncomputable section

section Spec
open Fl4Spec

/-- The tail of l4v `do_reply_transfer` after the transfer or the fault
reply, for the receiver and its fault. -/
def specReplyTail (receiver : ObjRef) (fault : Option Fault) : SMonad Unit Unit := do
  let scOpt ← getTcbObjRef Tcb.tcbSchedContext receiver
  let state ← getThreadState receiver
  NonDet.when (scOpt ≠ none ∧ runnable state) <| do
    let scPtr ← NonDet.assertOpt scOpt
    let sc ← getSchedContext scPtr
    let curtime ← NonDet.gets fun s : State Unit => s.curTime
    if refillReady curtime (refillHd sc) ∧ refillSufficient 0 (refillHd sc)
    then possibleSwitchTo receiver
    else do
      let tcb ← NonDet.getsThe (getTcb receiver)
      if isEpCap tcb.tcbTimeoutHandler ∧
         ¬(fault.elim false isTimeoutFault = true)
      then handleTimeout receiver (.timeout sc.scBadge)
      else postpone scPtr

/-- The fault reply of l4v `do_reply_transfer`. -/
def specFaultReply (sender receiver : ObjRef) (f : Fault) : SMonad Unit Unit := do
  let mi ← getMessageInfo sender
  let buf ← lookupIpcBuffer false sender
  let mrs ← getMrs sender buf mi
  let restart ← handleFaultReply f receiver mi.miLabel mrs
  threadSet (fun tcb => { tcb with tcbFault := none }) receiver
  setThreadState receiver (if restart then .restart else .inactive)

theorem nd_bind_assoc_fun {σ' α β γ : Type} (m : NonDet σ' α) (f : α → NonDet σ' β) (g : β → NonDet σ' γ) :
    ((m >>= f) >>= g) = (m >>= fun a => f a >>= g) := by
  funext s; exact Fl4Proofs.P3.Sched.nd_bind_assoc' m f g s

theorem doReplyTransfer_none {σ : State Unit} {snd r : ObjRef} {xr : Reply} (hkr : σ.kheap r = some (.reply xr))
    (h : xr.replyTcb = none) (g : Bool) : doReplyTransfer (Z := Unit) snd r g σ = ({((), σ)}, False) := by
  unfold doReplyTransfer
  rw [nd_bind_one (getReplyTcb_eq hkr), h]; rfl

theorem doReplyTransfer_notReply {σ : State Unit} {snd r t : ObjRef} {xr : Reply} (hkr : σ.kheap r = some (.reply xr))
    (h : xr.replyTcb = some t) {x : Tcb} (hkt : σ.kheap t = some (.tcb x)) (hs : ∀ r', x.tcbState ≠ .blockedOnReply r')
    (g : Bool) : doReplyTransfer (Z := Unit) snd r g σ = ({((), σ)}, False) := by
  unfold doReplyTransfer
  rw [nd_bind_one (getReplyTcb_eq hkr), h]
  show (getThreadState t >>= _) σ = _
  rw [nd_bind_one (getThreadState_eq hkt)]
  cases e : x.tcbState <;> first | rfl | exact absurd e (hs _)

/-- An outcome of l4v `do_reply_transfer` to a thread blocked on the reply,
from the outcomes of its steps. -/
theorem mem_doReplyTransfer {σ : State Unit} {snd r t : ObjRef} {xr : Reply} (hkr : σ.kheap r = some (.reply xr))
    (h : xr.replyTcb = some t) {x : Tcb} (hkt : σ.kheap t = some (.tcb x)) (hs : x.tcbState = .blockedOnReply r)
    (g : Bool) {σ1 σ2 : State Unit} (h1 : replyRemove (Z := Unit) t r σ = ({((), σ1)}, False))
    (h2 : (getTcbObjRef (Z := Unit) Tcb.tcbSchedContext t >>= ifSporadicCurScTestRefillUnblockCheck) σ1 =
      ({((), σ2)}, False))
    {x2 : Tcb} (hkt2 : σ2.kheap t = some (.tcb x2)) {z1 z : Unit × State Unit}
    (hbr : (x2.tcbFault = none ∧ z1 ∈ ((doIpcTransfer (Z := Unit) snd none 0 g t >>= fun _ =>
        setThreadState t .running) σ2).1) ∨ (∃ f, x2.tcbFault = some f ∧ z1 ∈ (specFaultReply snd t f σ2).1))
    (hz : z ∈ (specReplyTail t x2.tcbFault z1.2).1) :
    z ∈ (doReplyTransfer (Z := Unit) snd r g σ).1 := by
  unfold doReplyTransfer
  rw [nd_bind_one (getReplyTcb_eq hkr), h]
  show z ∈ ((getThreadState t >>= _) σ).1
  rw [nd_bind_one (getThreadState_eq hkt), hs]
  dsimp only
  rw [nd_bind_one (assert_true rfl σ), nd_bind_one h1, nd_bind_assoc, nd_bind_one h2,
    nd_bind_one (threadGet_eq _ hkt2)]
  rcases hbr with ⟨hf, hz1⟩ | ⟨f, hf, hz1⟩
  · rw [hf]
    have := mem_bind_nd (f := fun _ => specReplyTail t none) hz1 (by rw [hf] at hz; exact hz)
    rw [nd_bind_assoc_fun] at this
    exact this
  · rw [hf]
    have := mem_bind_nd (f := fun _ => specReplyTail t (some f)) hz1 (by rw [hf] at hz; exact hz)
    simp only [specFaultReply, nd_bind_assoc_fun] at this
    exact this

/-- The timeout branch of the reply tail. -/
def specReplyTmo (receiver : ObjRef) (fault : Option Fault) (sc : SchedContext) (scPtr : ObjRef) :
    SMonad Unit Unit := do
  let tcb ← NonDet.getsThe (getTcb receiver)
  if isEpCap tcb.tcbTimeoutHandler ∧
     ¬(fault.elim false isTimeoutFault = true)
  then handleTimeout receiver (.timeout sc.scBadge)
  else postpone scPtr

theorem specReplyTail_skip {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (h : x.tcbSchedContext = none ∨ runnable x.tcbState = false) (f : Option Fault) :
    specReplyTail t f σ = ({((), σ)}, False) := by
  unfold specReplyTail
  rw [nd_bind_one (getTcbObjRef_eq _ hk), nd_bind_one (getThreadState_eq hk)]
  unfold NonDet.when
  rw [if_neg (by rcases h with h | h <;> simp [h])]; rfl

theorem specReplyTail_run {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    {p : ObjRef} (hp : x.tcbSchedContext = some p) (hr : runnable x.tcbState = true) {y : SchedContext} {n : Nat}
    (hky : σ.kheap p = some (.schedContext y n)) (f : Option Fault) :
    specReplyTail t f σ = (if refillReady σ.curTime (refillHd y) ∧ refillSufficient 0 (refillHd y)
      then possibleSwitchTo t else specReplyTmo t f y p) σ := by
  unfold specReplyTail
  rw [nd_bind_one (getTcbObjRef_eq _ hk), nd_bind_one (getThreadState_eq hk)]
  unfold NonDet.when
  rw [if_pos (by simp [hp, hr]), hp]
  show (NonDet.pure p >>= _) σ = _
  rw [nd_bind_one (show (NonDet.pure p : NonDet (State Unit) ObjRef) σ = ({(p, σ)}, False) from rfl),
    nd_bind_one (Fl4Proofs.P3.Sched.getSchedContext_eq hky), nd_gets_bind]
  rfl

end Spec

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st] {N T C E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {c : U64}

variable (st ar) in
/-- FL4's fault reply (`do_reply_transfer`'s faulted branch). -/
def fl4FaultReply (s : S) (a : A) (i sender : obj.Tcb) : Result (S × A) := do
  let (restart, s4, a3) ← faults.handle_fault_reply st ar s a i sender
  let s5 ← faults.clear_fault st s4 i
  if restart
  then
    let s6 ← sched.set_thread_state st s5 i sched.TS_RESTART
    ok (s6, a3)
  else
    let s6 ← sched.set_thread_state st s5 i sched.TS_INACTIVE
    ok (s6, a3)

variable (st ar) in
/-- FL4's tail of `do_reply_transfer`. -/
def fl4ReplyTail (i : obj.Tcb) (fault_type : U64) (s3 : S) (a2 : A) : Result (S × A) := do
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
          sporadic.sufficient st ar s3 a2 i3
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
              faults.handle_timeout st ar s3 a2
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
            faults.handle_timeout st ar s3 a2 i
              (error.Fault.Timeout badge)
          else let s4 ← sched.postpone st s3 i3
               ok (s4, a2)
        else let s4 ← sched.postpone st s3 i3
             ok (s4, a2)
    else ok (s3, a2)

variable (st ar) in
/-- FL4's timeout branch of the reply tail (not ready or not sufficient). -/
def fl4ReplyTmo (i : obj.Tcb) (fault_type i3 : U64) (s3 : S) (a2 : A) : Result (S × A) := do
  let b5 ← faults.valid_timeout_handler st s3 i
  if b5
  then
    if fault_type != fl4_abi.consts.fault.Timeout
    then
      let badge ← obj.Sc.badge st i3 s3
      faults.handle_timeout st ar s3 a2 i
        (error.Fault.Timeout badge)
    else let s4 ← sched.postpone st s3 i3
         ok (s4, a2)
  else let s4 ← sched.postpone st s3 i3
       ok (s4, a2)

variable (st ar N T C E R B c) in
/-- **The named steps of `do_reply_transfer`** on `IRel` (see the module
docstring). -/
structure ReplyHyps : Prop where
  remove : ∀ s (a : A) σ (r t : U64) (x : Fl4Spec.Tcb), IRel st N T C E R B c s σ → r ∈ R → t ∈ T →
    σ.kheap t.bv = some (.tcb x) → x.tcbState = .blockedOnReply r.bv →
    ipc.reply_remove st ar s a r t ⦃ res => res.2 = a ∧ ∃ σ' x',
      Fl4Spec.replyRemove (Z := Unit) t.bv r.bv σ = ({((), σ')}, False) ∧ IRel st N T C E R B c res.1 σ' ∧
      σ'.kheap t.bv = some (.tcb x') ∧ x'.tcbState = .inactive ∧ x'.tcbFault = x.tcbFault ∧
      ∀ p y, p ≠ t.bv → σ.kheap p = some (.tcb y) → ∃ y', σ'.kheap p = some (.tcb y') ∧
        y'.tcbFault = y.tcbFault ∧ y'.tcbState = y.tcbState ⦄
  unblock : ∀ s σ (t : U64) (x : Fl4Spec.Tcb) (k : S → Result (S × A)) (P : S × A → Prop),
    IRel st N T C E R B c s σ → t ∈ T → σ.kheap t.bv = some (.tcb x) →
    (∀ s' σ', (Fl4Spec.getTcbObjRef (Z := Unit) Fl4Spec.Tcb.tcbSchedContext t.bv >>=
        Fl4Spec.ifSporadicCurScTestRefillUnblockCheck) σ = ({((), σ')}, False) → IRel st N T C E R B c s' σ' →
      (∀ p y, σ.kheap p = some (.tcb y) → σ'.kheap p = some (.tcb y)) → k s' ⦃ P ⦄) →
    (do
      let i2 ← obj.Tcb.sc st t s
      let b1 ← sporadic.sc_sporadic st s i2
      let s2 ←
        if b1
        then
          do
          let i3 ← obj.Sc.cpu st i2 s
          let i4 ← obj.node_get st s i3 layout.node.CUR_SC
          if i2 != i4
          then sporadic.unblock_check st s i2
          else ok s
        else ok s
      k s2) ⦃ P ⦄
  faultReply : ∀ s (a : A) σ (t snd : U64) (x : Fl4Spec.Tcb) (f : Fl4Spec.Fault), IRel st N T C E R B c s σ →
    t ∈ T → snd ∈ T → t ≠ snd → σ.kheap t.bv = some (.tcb x) → x.tcbFault = some f → x.tcbState = .inactive →
    fl4FaultReply st ar s a t snd ⦃ res => ∃ z ∈ (specFaultReply snd.bv t.bv f σ).1,
      IRel st N T C E R B c res.1 z.2 ⦄
  /-- The transfer with a grant and extra caps into a receive buffer with no
  endpoint (`transfer_caps` with `endpoint = none`). -/
  grantXfer : ∀ s (a : A) σ (snd rcv : U64) (xs xr : Fl4Spec.Tcb) (rp : Fl4Spec.ObjRef),
    IRel st N T C E R B c s σ → snd ∈ T → rcv ∈ T → snd ≠ rcv → σ.kheap snd.bv = some (.tcb xs) →
    σ.kheap rcv.bv = some (.tcb xr) → xs.tcbFault = none → ipcBufOf true xr = some rp →
    ipc.do_ipc_transfer st ar s a snd 0#u64 0#u64 true rcv ⦃ s' => ∃ σ',
      Fl4Spec.doIpcTransfer (Z := Unit) snd.bv none 0 true rcv.bv σ = ({((), σ')}, False) ∧
      IRel st N T C E R B c s' σ' ∧ ∃ x', σ'.kheap rcv.bv = some (.tcb x') ∧ x'.tcbState = xr.tcbState ⦄
  /-- The timeout branch of the tail: the timeout-handler test, `handle_timeout`
  and `postpone`. -/
  tmo : ∀ s (a : A) σ (t sc ft : U64) (fault : Option Fl4Spec.Fault) (y : Fl4Spec.SchedContext) (n : Nat),
    IRel st N T C E R B c s σ → t ∈ T → sc ∈ C → σ.kheap sc.bv = some (.schedContext y n) →
    ∀ x : Fl4Spec.Tcb, σ.kheap t.bv = some (.tcb x) → Fl4Spec.runnable x.tcbState = true →
    x.tcbSchedContext = some sc.bv → (ft = 0#u64 ↔ fault = none) → (ft = 5#u64 ↔ ∃ b, fault = some (.timeout b)) →
    fl4ReplyTmo st ar t ft sc s a ⦃ res => ∃ z ∈ (specReplyTmo t.bv fault y sc.bv σ).1,
      IRel st N T C E R B c res.1 z.2 ⦄



set_option maxHeartbeats 8000000 in
/-- **The tail of `do_reply_transfer`** (`ReplyHyps.tail`): no SC or not
runnable, nothing; ready and sufficient, `possible_switch_to`
(`IpcEpTailHyps.switchTo`); otherwise the timeout branch (`htmo`, named:
the timeout-handler test, `handle_timeout` and `postpone`). The platform's
`MIN_BUDGET` is `hmb`. -/
theorem reply_tail_top (hTl : IpcEpTailHyps st A N T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hP0 : IPlaced N T E R B)
    (hmb : ∀ a : A, sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (htmo : ∀ s (a : A) σ (t sc ft : U64) (fault : Option Fl4Spec.Fault) (y : Fl4Spec.SchedContext) (n : Nat),
      IRel st N T C E R B c s σ → t ∈ T → sc ∈ C → σ.kheap sc.bv = some (.schedContext y n) →
      ∀ x : Fl4Spec.Tcb, σ.kheap t.bv = some (.tcb x) → Fl4Spec.runnable x.tcbState = true →
      x.tcbSchedContext = some sc.bv → (ft = 0#u64 ↔ fault = none) → (ft = 5#u64 ↔ ∃ b, fault = some (.timeout b)) →
      fl4ReplyTmo st ar t ft sc s a ⦃ res => ∃ z ∈ (specReplyTmo t.bv fault y sc.bv σ).1,
        IRel st N T C E R B c res.1 z.2 ⦄) :
    ∀ s (a : A) σ (t ft : U64) (fault : Option Fl4Spec.Fault), IRel st N T C E R B c s σ → t ∈ T →
    (ft = 0#u64 ↔ fault = none) → (ft = 5#u64 ↔ ∃ b, fault = some (.timeout b)) →
    fl4ReplyTail st ar t ft s a ⦃ res => ∃ z ∈ (specReplyTail t.bv fault σ).1, IRel st N T C E R B c res.1 z.2 ⦄ := by
  intro s a σ t ft fault hX ht hf0 hf5
  obtain ⟨hIR, hSRT⟩ := hX
  have hS := hSRT.2.1
  obtain ⟨Q, R0, hc, hsp⟩ := hS.lists
  obtain ⟨x, hk, -, -, hscw, -⟩ := hsp.tcb t ht
  obtain ⟨x0, hk0, hTR⟩ := hIR.tcb t ht
  rw [hk] at hk0; cases hk0
  unfold fl4ReplyTail
  step with Fl4Proofs.P1.obj.Tcb.sc.spec as ⟨i3, hi3⟩
  step with Fl4Proofs.P3.Sched.obj.Sc.is_null.spec' as ⟨b2, hb2⟩
  by_cases h0 : i3 = 0#u64
  · rw [hb2, if_pos (by simp [h0]), WP.spec_ok]
    refine ⟨((), σ), ?_, hIR, hSRT⟩
    rw [specReplyTail_skip hk (Or.inl (by rw [hscw, ← hi3, h0, optRef_zero]))]; rfl
  rw [hb2, if_neg (by simp [h0])]
  refine WP.spec_bind (Fl4Proofs.P3.Sched.is_runnable_spec s t) ?_
  rintro b3 rfl
  have hrun : decide (L.mem s (tStA t) = sched.TS_RUNNING ∨ L.mem s (tStA t) = sched.TS_RESTART ∨
      L.mem s (tStA t) = sched.TS_RUNNING_VM) = Fl4Spec.runnable x.tcbState := by
    have hw := hTR.st
    generalize L.mem s (tStA t) = w at hw ⊢
    have e : ∀ k : U64, (w = k ↔ w.val = k.val) := fun k => ⟨fun h => h ▸ rfl, fun h => UScalar.eq_of_val_eq h⟩
    unfold sched.TS_RUNNING sched.TS_RESTART sched.TS_RUNNING_VM
    simp only [e, hw]
    cases x.tcbState <;> simp [tsCode, Fl4Spec.runnable]
  rw [hrun]
  by_cases hrn : Fl4Spec.runnable x.tcbState = true
  swap
  · rw [if_neg hrn, WP.spec_ok]
    refine ⟨((), σ), ?_, hIR, hSRT⟩
    rw [specReplyTail_skip hk (Or.inr (by simpa using hrn))]; rfl
  rw [if_pos hrn]
  have hi3C : i3 ∈ C := by rw [hi3]; exact hsp.scMem t ht (by rw [← hi3]; exact h0)
  obtain ⟨y, n, hky, hy⟩ := hsp.scs i3 hi3C
  have hW := hy.wf
  have hne : y.scRefills ≠ [] := by rw [hy.refills]; exact Fl4Proofs.P3.Sched.refills_ne hW
  have hxsc : x.tcbSchedContext = some i3.bv := by rw [hscw, ← hi3, optRef_ne h0]
  have hspec := specReplyTail_run hk hxsc hrn hky fault
  refine WP.spec_bind (Fl4Proofs.P3.Sched.ready_refines s σ hS hi3C hky) ?_
  rintro b4 hb4
  rw [Fl4Proofs.P3.Sched.getScRefillReady_eq hky hne] at hb4
  have hb4' : b4 = Fl4Spec.refillReady σ.curTime (Fl4Spec.refillHd y) := by
    have := congrArg (fun q => (b4, σ) ∈ q.1) hb4; simpa using this.symm
  by_cases hrd : b4 = true
  · rw [if_pos hrd]
    refine WP.spec_bind (Fl4Proofs.P3.Sched.sufficient_refines s a σ hS hi3C hky 0#u64 (hmb a)) ?_
    rintro b5 hb5
    rw [Fl4Proofs.P3.Sched.getScRefillSufficient_eq hky hne] at hb5
    have hb5' : b5 = Fl4Spec.refillSufficient 0 (Fl4Spec.refillHd y) := by
      have := congrArg (fun q => (b5, σ) ∈ q.1) hb5; simpa using this.symm
    by_cases hsf : b5 = true
    · rw [if_pos hsf]
      refine WP.spec_mono (hTl.switchTo s a σ t hIR hSRT ht) ?_
      rintro _ ⟨-, -, σ', hm, hf, hv, hS'⟩
      refine ⟨((), σ'), ?_, hIR.frame hP0 hf hv, hS'⟩
      rw [hspec, if_pos ⟨hb4' ▸ hrd, hb5' ▸ hsf⟩]; exact hm
    · rw [if_neg hsf]
      refine WP.spec_mono (htmo s a σ t i3 ft fault y n ⟨hIR, hSRT⟩ ht hi3C hky x hk hrn hxsc hf0 hf5) ?_
      rintro _ ⟨z, hz, hXz⟩
      refine ⟨z, ?_, hXz⟩
      rw [hspec, if_neg (fun h => hsf (hb5' ▸ h.2))]; exact hz
  · rw [if_neg hrd]
    refine WP.spec_mono (htmo s a σ t i3 ft fault y n ⟨hIR, hSRT⟩ ht hi3C hky x hk hrn hxsc hf0 hf5) ?_
    rintro _ ⟨z, hz, hXz⟩
    refine ⟨z, ?_, hXz⟩
    rw [hspec, if_neg (fun h => hrd (hb4' ▸ h.1))]; exact hz

set_option maxHeartbeats 4000000 in
/-- **The transfer of `do_reply_transfer`** (no endpoint, badge 0) on
`IRel`, from a replier without a fault. -/
theorem reply_xfer_top (hH : IpcSchedHyps st ar N T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hBf : EpBufHyps st T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hBm : EpBufMapHyps st T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hP0 : IPlaced N T E R B) (hRH : ReplyHyps st ar N T C E R B c)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hX : IRel st N T C E R B c s σ)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr)) (hf : xs.tcbFault = none)
    (g : Bool) :
    ipc.do_ipc_transfer st ar s a snd 0#u64 0#u64 g rcv ⦃ s' => ∃ σ',
      Fl4Spec.doIpcTransfer (Z := Unit) snd.bv none 0 g rcv.bv σ = ({((), σ')}, False) ∧
      IRel st N T C E R B c s' σ' ∧ ∃ x', σ'.kheap rcv.bv = some (.tcb x') ∧ x'.tcbState = xr.tcbState ⦄ := by
  obtain ⟨hIR, hSRT⟩ := hX
  have hSB := IpcRel.toSRN hIR hSRT
  cases hrb : ipcBufOf true xr with
  | none =>
    exact WP.spec_mono (do_ipc_transfer_regsT hH hBf hBm hP0 hP0.e s a σ hIR.toE hSB hs hr hne hks hkr hf hrb 0#u64
      0#u64 g none) fun _ ⟨h1, h2, h3, _⟩ => ⟨_, h1, IpcRel.ofSRN h2 h3, xferTcb xr xs 0#u64.bv, by simp,
        xferTcb_state _ _ _⟩
  | some rp =>
    by_cases hcaps : g = false ∨ ipcBufOf false xs = none ∨
      Fl4Spec.unat (Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miExtraCaps = 0
    · exact WP.spec_mono (do_ipc_transfer_buf (ar := ar) (hH.epHyps hP0) hBf.srs hBm.srs hP0.e s a σ hIR.toE hSB.1
        hs hr hne hks hkr hf hrb 0#u64 0#u64 g hcaps none) fun _ ⟨σ', h1, h2, h3, h4, h5, x', h6, h7⟩ =>
          ⟨σ', h1, IpcRel.ofSRN h2 ⟨h3, ntfn_lift_rcv hP0.toC hIR.toN h2 hr h4 h5 hkr h6 h7⟩, x', h6, h7⟩
    · have hg : g = true := by cases g <;> simp_all
      subst hg
      exact hRH.grantXfer s a σ snd rcv xs xr rp ⟨hIR, hSRT⟩ hs hr hne hks hkr hf hrb




set_option maxHeartbeats 16000000 in
/-- **FL4's `do_reply_transfer` refines l4v `do_reply_transfer`** on `IRel`
(see the module docstring), for a replier without a fault, running or
restarting. -/
theorem do_reply_transfer_top (hH : IpcSchedHyps st ar N T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hBf : EpBufHyps st T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hBm : EpBufMapHyps st T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hP0 : IPlaced N T E R B) (hRH : ReplyHyps st ar N T C E R B c)
    (hTl : IpcEpTailHyps st A N T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hmb : ∀ a : A, sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hX : IRel st N T C E R B c s σ)
    (hV : Sched.SchedValid σ) (hO : Sched.ObjCover N T E R C σ)
    {ct : U64} (hct : ct ∈ T) {xc : Fl4Spec.Tcb} (hkc : σ.kheap ct.bv = some (.tcb xc))
    (hcf : xc.tcbFault = none) (hcs : tsCode xc.tcbState < 3) {r : U64} (hr : r ∈ R) (g : Bool) :
    ipc.do_reply_transfer st ar s a ct r g ⦃ res =>
      ∃ z ∈ (Fl4Spec.doReplyTransfer (Z := Unit) ct.bv r.bv g σ).1, IRel st N T C E R B c res.1 z.2 ⦄ := by
  obtain ⟨hIR, hSRT⟩ := hX
  obtain ⟨xr, hkr, hxr⟩ := hIR.reply r hr
  unfold ipc.do_reply_transfer
  step with Fl4Proofs.P3.Endp.obj.Reply.tcb.spec as ⟨i, hi⟩
  step with Fl4Proofs.P1.obj.Tcb.is_null.spec as ⟨b, hb⟩
  by_cases h0 : i = 0#u64
  · rw [hb, if_pos (by simp [h0]), WP.spec_ok]
    refine ⟨((), σ), ?_, hIR, hSRT⟩
    rw [doReplyTransfer_none hkr (by rw [hxr, ← hi, h0, optRef_zero])]; rfl
  rw [hb, if_neg (by simp [h0])]
  have hrep : xr.replyTcb = some i.bv := by rw [hxr, ← hi, optRef_ne h0]
  obtain ⟨x, hkx, hxs⟩ := hV.replyTcb r.bv xr i.bv hkr hrep
  have hiT : i ∈ T := by
    obtain ⟨t, ht, h⟩ := hO.tcb _ x hkx
    rw [Sched.bv_inj h] at ht; exact ht
  obtain ⟨x0, hk0, hTR⟩ := hIR.tcb i hiT
  rw [hkx] at hk0; cases hk0
  step with Fl4Proofs.P3.Notif.obj.Tcb.state.spec as ⟨i1, hi1⟩
  rcases hxs with hst | ⟨ep, d, hst⟩
  swap
  · -- receiving with the reply: nothing happens
    have hne : (i1 != sched.TS_BLOCKED_ON_REPLY) = true := by
      have h := hTR.st
      rw [hst] at h
      rw [hi1]
      have : L.mem s (tStA i) ≠ sched.TS_BLOCKED_ON_REPLY := by
        intro e; rw [e] at h; unfold sched.TS_BLOCKED_ON_REPLY at h; simp [tsCode] at h
      simpa using this
    rw [if_pos hne, WP.spec_ok]
    refine ⟨((), σ), ?_, hIR, hSRT⟩
    rw [doReplyTransfer_notReply hkr hrep hkx (by rw [hst]; intro r' h; cases h)]; rfl
  have hne : (i1 != sched.TS_BLOCKED_ON_REPLY) = false := by
    have h := hTR.st
    rw [hst] at h
    rw [hi1]
    have : L.mem s (tStA i) = sched.TS_BLOCKED_ON_REPLY := by
      apply UScalar.eq_of_val_eq; rw [h]; unfold sched.TS_BLOCKED_ON_REPLY; rfl
    simp [this]
  rw [if_neg (by rw [hne]; simp)]
  have hit : i ≠ ct := by
    rintro rfl; rw [hkc] at hkx; cases hkx; rw [hst] at hcs; simp [tsCode] at hcs
  refine WP.spec_bind (hRH.remove s a σ r i x ⟨hIR, hSRT⟩ hr hiT hkx hst) ?_
  rintro ⟨s1, a1⟩ ⟨-, σ1, x1, hrm, hX1, hkx1, hx1s, hx1f, hoth1⟩
  obtain ⟨xc1, hkc1, hxc1f, hxc1s⟩ := hoth1 ct.bv xc (fun e => hit (P1.eq_of_bv e).symm) hkc
  refine hRH.unblock s1 σ1 i x1 _ _ hX1 hiT hkx1 ?_
  intro s2 σ2 hub hX2 hpres
  have hkx2 := hpres _ _ hkx1
  have hkc2 := hpres _ _ hkc1
  obtain ⟨hIR2, hSRT2⟩ := hX2
  obtain ⟨x2', hk2', hTR2⟩ := hIR2.tcb i hiT
  rw [hkx2] at hk2'; cases hk2'
  step with Fl4Proofs.P3.Endp.obj.Tcb.fault_type.spec as ⟨ft, hft⟩
  have hft0 : ft = 0#u64 ↔ x1.tcbFault = none := by rw [hft]; exact hTR2.fault0
  have hft5 : ft = 5#u64 ↔ ∃ b, x1.tcbFault = some (.timeout b) := by rw [hft]; exact hTR2.faultT
  refine WP.spec_bind (Pₘ := fun res => ∃ z1 : Unit × Fl4Spec.State Unit,
    ((x1.tcbFault = none ∧ z1 ∈ ((Fl4Spec.doIpcTransfer (Z := Unit) ct.bv none 0 g i.bv >>= fun _ =>
        Fl4Spec.setThreadState i.bv .running) σ2).1) ∨
      (∃ f, x1.tcbFault = some f ∧ z1 ∈ (specFaultReply ct.bv i.bv f σ2).1)) ∧
    IRel st N T C E R B c res.1 z1.2) ?_ ?_
  · by_cases hf : x1.tcbFault = none
    · rw [if_pos (by rw [hft0.2 hf]; unfold fl4_abi.consts.fault.NullFault; rfl)]
      refine WP.spec_bind (reply_xfer_top hH hBf hBm hP0 hRH s2 a1 σ2 ⟨hIR2, hSRT2⟩ hct hiT (Ne.symm hit) hkc2 hkx2
        (hxc1f.trans hcf) g) ?_
      rintro s4 ⟨σ4, htr, hX4, x4, hkx4, hx4s⟩
      have hsteps := IpcSchedHyps.stepsG (A := A) hH hBf hBm hP0
      obtain ⟨x4', hk4', hTR4⟩ := hX4.1.tcb i hiT
      rw [hkx4] at hk4'; cases hk4'
      have hst4 : x4.tcbState = .inactive := by rw [hx4s, hx1s]
      have hq := IpcRel.not_ep_queued hX4.1 (t := i) (by rw [hTR4.st, hst4]; decide)
      have hcode : sched.TS_RUNNING.val = tsCode .running := by unfold sched.TS_RUNNING; rfl
      refine WP.spec_bind (hsteps.sts hP0.e s4 σ4 hX4.1.toE (IpcRel.toSRN hX4.1 hX4.2) hiT hkx4 hq
        (show tsCode x4.tcbState ≠ 6 by rw [hst4]; decide) .running (by decide) sched.TS_RUNNING hcode) ?_
      rintro s5 ⟨hE5, hS5⟩
      apply (WP.spec_ok _).2
      refine ⟨((), stsAct (updK σ4 i.bv (.tcb { x4 with tcbState := .running })) i.bv), Or.inl ⟨hf, ?_⟩,
        IpcRel.ofSRN hE5 hS5⟩
      rw [nd_bind_one htr, Notif.setThreadState_eq _ hkx4]; rfl
    · obtain ⟨f, hf'⟩ := Option.ne_none_iff_exists'.1 hf
      rw [if_neg (by rw [hft]; unfold fl4_abi.consts.fault.NullFault; intro h; exact hf (hTR2.fault0.1 h))]
      exact WP.spec_mono (hRH.faultReply s2 a1 σ2 i ct x1 f ⟨hIR2, hSRT2⟩ hiT hct hit hkx2 hf' hx1s)
        fun _ ⟨z1, hz1, hX3⟩ => ⟨z1, Or.inr ⟨f, hf', hz1⟩, hX3⟩
  · rintro ⟨s3, a2⟩ ⟨z1, hbr, hX3⟩
    exact WP.spec_mono (reply_tail_top hTl hP0 hmb hRH.tmo s3 a2 z1.2 i ft x1.tcbFault hX3 hiT hft0 hft5)
      fun _ ⟨z, hz, hXz⟩ =>
      ⟨z, mem_doReplyTransfer hkr hrep hkx hst g hrm hub hkx2 hbr hz, hXz⟩


set_option maxHeartbeats 4000000 in
/-- **The reply tail of a reply invocation** (`hrep` of `decode_replyDMX`):
`set_thread_state Restart` then `do_reply_transfer`, on `IRel`. -/
theorem reply_tail_inv (hH : IpcSchedHyps st ar N T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hBf : EpBufHyps st T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hBm : EpBufMapHyps st T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hP0 : IPlaced N T E R B) (hRH : ReplyHyps st ar N T C E R B c)
    (hTl : IpcEpTailHyps st A N T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hmb : ∀ a : A, sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hSV : ∀ s' σ', IRel st N T C E R B c s' σ' → Sched.SchedValid σ')
    (hOC : ∀ s' σ', IRel st N T C E R B c s' σ' → Sched.ObjCover N T E R C σ')
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hX : IRel st N T C E R B c s σ)
    {ct : U64} (hct : ct ∈ T) (hcur : σ.curThread = ct.bv) {xt : Fl4Spec.Tcb} (hkt : σ.kheap ct.bv = some (.tcb xt))
    (hrun : tsCode xt.tcbState < 3) (hft : xt.tcbFault = none)
    {σ1 : Fl4Spec.State Unit} (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    {p : U64} (hp : p ∈ R) (g : Bool) :
    (do
      let s1 ← sched.set_thread_state st s ct sched.TS_RESTART
      let (s2, a1) ← ipc.do_reply_transfer st ar s1 a ct p g
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a1)) ⦃ r => r.1 = .Ok () ∧
      ∃ z ∈ (Fl4Spec.doReplyTransfer (Z := Unit) σ1.curThread p.bv g σ1).1,
        RelTopM (L := L) r.2.1 z.2 ∧ IRel st N T C E R B c r.2.1 z.2 ⦄ := by
  obtain ⟨hIR, hSRT⟩ := hX
  have hSB := IpcRel.toSRN hIR hSRT
  have hsteps := IpcSchedHyps.stepsG (A := A) hH hBf hBm hP0
  obtain ⟨xt0, hk0, hTR⟩ := hIR.tcb ct hct
  rw [hkt] at hk0; cases hk0
  have hq := IpcRel.not_ep_queued hIR (t := ct) (by rw [hTR.st]; omega)
  have hcode : sched.TS_RESTART.val = tsCode .restart := by unfold sched.TS_RESTART; rfl
  refine WP.spec_bind (hsteps.sts hP0.e s σ hIR.toE hSB hct hkt hq (show tsCode xt.tcbState ≠ 6 by omega) .restart
    (by decide) sched.TS_RESTART hcode) ?_
  rintro s1 ⟨hE1, hS1⟩
  rw [hcur, Notif.setThreadState_eq .restart hkt] at hst
  have hσ1 : σ1 = stsAct (updK σ ct.bv (.tcb { xt with tcbState := .restart })) ct.bv := by
    have := congrArg (fun q => ((), σ1) ∈ q.1) hst
    simp only [Set.mem_singleton_iff, Prod.mk.injEq, true_and] at this
    simpa using this.symm
  subst hσ1
  obtain ⟨hIR1, hSRT1⟩ := IpcRel.ofSRN hE1 hS1
  have hX1 : IRel st N T C E R B c s1 _ := ⟨hIR1, hSRT1⟩
  have hkt1 : (stsAct (updK σ ct.bv (.tcb { xt with tcbState := .restart })) ct.bv).kheap ct.bv =
      some (.tcb { xt with tcbState := .restart }) := by rw [stsAct_kheap]; simp
  have hc1 : (stsAct (updK σ ct.bv (.tcb { xt with tcbState := .restart })) ct.bv).curThread = ct.bv := by
    unfold stsAct; split_ifs <;> exact hcur
  refine WP.spec_bind (do_reply_transfer_top hH hBf hBm hP0 hRH hTl hmb s1 a _ hX1 (hSV _ _ hX1) (hOC _ _ hX1) hct hkt1
    hft (by simp [tsCode]) hp g) ?_
  rintro ⟨s2, a1⟩ ⟨z, hz, hIR2, hSRT2⟩
  apply (WP.spec_ok _).2
  exact ⟨rfl, z, by rw [hc1]; exact hz, (SRT.relTop ⟨hIR2, hSRT2⟩).1, hIR2, hSRT2⟩

end

end

end Fl4Proofs.P3.Endp

namespace Fl4Proofs.P3
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : P1.LawfulStore st] {N T C E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- A reply of the spec's heap is one of the relation's. -/
theorem memR_of_cover {σ : Fl4Spec.State Unit} (hO : Sched.ObjCover N T E R C σ) {p : U64}
    (hp : ∃ x, σ.kheap p.bv = some (.reply x)) : p ∈ R := by
  obtain ⟨x, hk⟩ := hp
  obtain ⟨r, hr, h⟩ := hO.reply _ x hk
  rw [Sched.bv_inj h] at hr; exact hr

/-- **A reply cap for `handle_invocation_refinesMX`**, with `X := IRel`:
`decode_replyDMX` with `reply_tail_inv`. -/
theorem decode_reply_top (hH : IpcSchedHyps st ar N T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hBf : EpBufHyps st T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hBm : EpBufMapHyps st T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hP0 : IPlaced N T E R B) (hRH : ReplyHyps st ar N T C E R B c)
    (hTl : IpcEpTailHyps st A N T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hmb : ∀ a : A, sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hSV : ∀ s' σ', IRel st N T C E R B c s' σ' → Sched.SchedValid σ')
    (hOC : ∀ s' σ', IRel st N T C E R B c s' σ' → Sched.ObjCover N T E R C σ')
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hX : IRel st N T C E R B c s σ)
    (lbl length slot : U64) (p : U64) (g : Bool) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hcT : ct ∈ T) (hcur : σ.curThread = ct.bv) {xt : Fl4Spec.Tcb} (hkt : σ.kheap ct.bv = some (.tcb xt))
    (hrun : tsCode xt.tcbState < 3) (hft : xt.tcbFault = none) (hp : p ∈ R) :
    DecOKDMX (L := L) ar (fun s _ σ => IRel st N T C E R B c s σ) s a σ lbl length slot (.Reply p g)
      blk call don fp buf extra slbl args ci sl excaps buffer := by
  obtain ⟨σ1, hst⟩ : ∃ σ1, Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) := by
    rw [hcur, Notif.setThreadState_eq .restart hkt]; exact ⟨_, rfl⟩
  exact decode_replyDMX ar _ s a σ lbl length slot p g blk call don fp buf extra slbl args ci sl excaps buffer ct hct
    hst (reply_tail_inv hH hBf hBm hP0 hRH hTl hmb hSV hOC s a σ hX hcT hcur hkt hrun hft hst hp g)

end

end

end Fl4Proofs.P3
