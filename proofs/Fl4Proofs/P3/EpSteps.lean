/-
P3 (DESIGN.md §9), endpoints: **the step lemmas of the endpoint theorems,
bundled** (`EpSteps`), so that the endpoint theorems can be stated once and
instantiated for the endpoint relation alone and for the combined relation.

`EpSteps st A ar T E R B SR NS` states the steps the transfer theorems are
built from (dequeue, the two transfers, reply link / unlink / push, setting a
thread state) for an abstract `SR`, as in their lemmas; the threads whose
state is set must satisfy `NS` on their spec state, and `NS` holds of every
state but `BlockedOnNotification` (`ns_ep`).

* `EpHyps.steps`: the instance for `SR` itself (`NS` = anything), from the
  lemmas;
* `CombHyps.steps`: the instance for `SRN N T SR := SR ∧ NtfnStateRel N T`
  with `NS ts := tsCode ts ≠ 6`, i.e. the notification relation carried
  along every step;
* `CombTailHyps`: the scheduler tails, keeping the notification footprint
  and view too; `CombTailHyps.tailN` gives the tails for `SRN`.
-/
import Fl4Proofs.P3.EpComb
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Defs
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]

/-- The step lemmas (see the module docstring). -/
structure EpSteps (A : Type) (ar : machine.Arch A) (T E R : Set U64) (B : Set (U64 × Fl4Spec.Word))
    (SR : S → Fl4Spec.State Unit → Prop) (NS : Fl4Spec.ThreadState → Prop) : Prop where
  ns_ep : ∀ ts, tsCode ts ≠ 6 → NS ts
  deq : ∀ (hP : EPlaced T E R B) (s : S) (σ : Fl4Spec.State Unit)
    (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ) {e : U64} (he : e ∈ E) {x : Fl4Spec.Endpoint}
    (hk : σ.kheap e.bv = some (.endpoint x)) {d : U64} (hd : d.bv ∈ x.epQueue),
    endpoint.ep_dequeue st s e d ⦃ s' =>
      Fl4Spec.tcbEpDequeue (Z := Unit) d.bv e.bv σ = ({((), updK σ e.bv (.endpoint (epDeq x d.bv)))}, False) ∧
      EpStateRel T E R B (L.mem s') (updK σ e.bv (.endpoint (epDeq x d.bv))) ∧
      SR s' (updK σ e.bv (.endpoint (epDeq x d.bv))) ∧
      Agree (L.mem s) (L.mem s') (AllTF T) ⦄
  xregs : ∀ (hP : EPlaced T E R B)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr)) (hf : xs.tcbFault = none)
    (hrb : ipcBufOf true xr = none) (ep badge : U64) (grant : Bool)
    (hcaps : grant = false ∨ ipcBufOf false xs = none ∨
      Fl4Spec.unat (Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miExtraCaps = 0),
    ipc.do_ipc_transfer st ar s a snd ep badge grant rcv ⦃ s' =>
      Fl4Spec.doIpcTransfer (Z := Unit) snd.bv (some ep.bv) badge.bv grant rcv.bv σ =
        ({((), updK σ rcv.bv (.tcb (xferTcb xr xs badge.bv)))}, False) ∧
      EpStateRel T E R B (L.mem s') (updK σ rcv.bv (.tcb (xferTcb xr xs badge.bv))) ∧
      SR s' (updK σ rcv.bv (.tcb (xferTcb xr xs badge.bv))) ∧
      Agree (L.mem s) (L.mem s') (fun b => ¬ RcvReg rcv b) ⦄
  xbuf : ∀ (hP : EPlaced T E R B)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr)) (hf : xs.tcbFault = none)
    {rp : Fl4Spec.ObjRef} (hrb : ipcBufOf true xr = some rp) (ep badge : U64) (grant : Bool)
    (hcaps : grant = false ∨ ipcBufOf false xs = none ∨
      Fl4Spec.unat (Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miExtraCaps = 0),
    ipc.do_ipc_transfer st ar s a snd ep badge grant rcv ⦃ s' => ∃ σ',
      Fl4Spec.doIpcTransfer (Z := Unit) snd.bv (some ep.bv) badge.bv grant rcv.bv σ = ({((), σ')}, False) ∧
      EpStateRel T E R B (L.mem s') σ' ∧ SR s' σ' ∧
      Agree (L.mem s) (L.mem s') (fun b => ¬ RcvReg rcv b ∧ ¬ BufW B b) ∧
      (∀ p, p ≠ rcv.bv → σ'.kheap p = σ.kheap p) ∧
      ∃ x', σ'.kheap rcv.bv = some (.tcb x') ∧ x'.tcbState = xr.tcbState ⦄
  link : ∀ (hP : EPlaced T E R B) (s : S) (σ : Fl4Spec.State Unit)
    (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ) {r : U64} (hr : r ∈ R) {xr : Fl4Spec.Reply}
    (hkr : σ.kheap r.bv = some (.reply xr)) {t : U64} (ht : TcbAddr t),
    Fl4Spec.setReplyObjRef (Z := Unit) Fl4Spec.replyTcbUpdate r.bv (some t.bv) σ =
      ({((), updK σ r.bv (.reply { xr with replyTcb := some t.bv }))}, False) ∧
    EpStateRel T E R B (L.mem (L.wr s (rTcbA r) t)) (updK σ r.bv (.reply { xr with replyTcb := some t.bv })) ∧
    SR (L.wr s (rTcbA r) t) (updK σ r.bv (.reply { xr with replyTcb := some t.bv })) ∧
    Agree (L.mem s) (L.mem (L.wr s (rTcbA r) t)) (fun b => b.val ≠ r.val)
  unlink : ∀ (hP : EPlaced T E R B) (s : S) (σ : Fl4Spec.State Unit)
    (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ) {t : U64} (ht : t ∈ T) {x : Fl4Spec.Tcb}
    (hk : σ.kheap t.bv = some (.tcb x)) {e' : Fl4Spec.ObjRef} {dd : Fl4Spec.ReceiverPayload} {r : U64}
    (hst : x.tcbState = .blockedOnReceive e' (some r.bv) dd) (hr : r ∈ R) {xr : Fl4Spec.Reply}
    (hkr : σ.kheap r.bv = some (.reply xr)) (hback : xr.replyTcb = some t.bv)
    (hq : ∀ e ∈ E, ∀ z, σ.kheap e.bv = some (.endpoint z) → t.bv ∉ z.epQueue),
    ipc.reply_unlink st s r t ⦃ s' =>
      Fl4Spec.replyUnlinkTcb (Z := Unit) t.bv r.bv σ =
        ({((), stsAct (updK (updK σ r.bv (.reply { xr with replyTcb := none })) t.bv
          (.tcb { x with tcbState := .inactive })) t.bv)}, False) ∧
      EpStateRel T E R B (L.mem s') (stsAct (updK (updK σ r.bv (.reply { xr with replyTcb := none })) t.bv
          (.tcb { x with tcbState := .inactive })) t.bv) ∧
      SR s' (stsAct (updK (updK σ r.bv (.reply { xr with replyTcb := none })) t.bv
          (.tcb { x with tcbState := .inactive })) t.bv) ⦄
  sts : ∀ (hP : EPlaced T E R B) (s : S)
    (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ) {t : U64} (ht : t ∈ T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x))
    (hq : ∀ e ∈ E, ∀ z, σ.kheap e.bv = some (.endpoint z) → t.bv ∉ z.epQueue) (hns : NS x.tcbState)
    (ts : Fl4Spec.ThreadState) (hts : tsCode ts < 3) (code : U64) (hcode : code.val = tsCode ts),
    sched.set_thread_state st s t code ⦃ s' =>
      EpStateRel T E R B (L.mem s') (stsAct (updK σ t.bv (.tcb { x with tcbState := ts })) t.bv) ∧
      SR s' (stsAct (updK σ t.bv (.tcb { x with tcbState := ts })) t.bv) ⦄
  push : ∀ (hP : EPlaced T E R B) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ) {t d : U64} (ht : t ∈ T)
    {xt xd : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt)) (hkd : σ.kheap d.bv = some (.tcb xd))
    (hq : ∀ e ∈ E, ∀ z, σ.kheap e.bv = some (.endpoint z) → t.bv ∉ z.epQueue) (hns : NS xt.tcbState)
    {r : U64} (hr : r ∈ R) {xr : Fl4Spec.Reply} (hkr : σ.kheap r.bv = some (.reply xr)),
    ipc.reply_push st ar s a t d r false ⦃ res => res.2 = a ∧
      Fl4Spec.replyPush (Z := Unit) t.bv d.bv r.bv false σ =
        ({((), stsAct (updK (updK σ r.bv (.reply { xr with replyTcb := some t.bv })) t.bv
          (.tcb { xt with tcbState := .blockedOnReply r.bv })) t.bv)}, False) ∧
      EpStateRel T E R B (L.mem res.1) (stsAct (updK (updK σ r.bv (.reply { xr with replyTcb := some t.bv })) t.bv
          (.tcb { xt with tcbState := .blockedOnReply r.bv })) t.bv) ∧
      SR res.1 (stsAct (updK (updK σ r.bv (.reply { xr with replyTcb := some t.bv })) t.bv
          (.tcb { xt with tcbState := .blockedOnReply r.bv })) t.bv) ⦄

/-- `SR` together with the notification relation. -/
def SRN (N T : Set U64) (SR : S → Fl4Spec.State Unit → Prop) (s : S) (σ : Fl4Spec.State Unit) : Prop :=
  SR s σ ∧ NtfnStateRel N T (L.mem s) σ

/-- The tail post-condition, keeping the notification footprint and view. -/
def TailPostN (N T E R : Set U64) (B : Set (U64 × Fl4Spec.Word)) (SR : S → Fl4Spec.State Unit → Prop)
    (s : S) (σ : Fl4Spec.State Unit) (m : Fl4Spec.SMonad Unit Unit) (s' : S) : Prop :=
  ¬ (m σ).2 ∧ ∃ σ', ((), σ') ∈ (m σ).1 ∧ FootEq T E R B (L.mem s) (L.mem s') ∧ KView σ σ' ∧
    Notif.FootEq N T (L.mem s) (L.mem s') ∧ Notif.KView σ σ' ∧ SR s' σ'

/-- The scheduler tails (`EpTailHyps`), keeping the notification footprint
and view too. -/
structure CombTailHyps (A : Type) (N T E R : Set U64) (B : Set (U64 × Fl4Spec.Word))
    (SR : S → Fl4Spec.State Unit → Prop) : Prop where
  wakeTail : ∀ s (a : A) σ (t : U64), EpStateRel T E R B (L.mem s) σ → SR s σ → t ∈ T →
    (do
      let s1 ← endpoint.unblock_sporadic st s t
      let s2 ← sched.possible_switch_to st s1 t
      ok (s2, a)) ⦃ r => r.2 = a ∧ TailPostN st N T E R B SR s σ (specWakeTailE t.bv) r.1 ⦄
  sporadicAssert : ∀ s σ (t : U64), EpStateRel T E R B (L.mem s) σ → SR s σ → t ∈ T →
    endpoint.unblock_sporadic st s t ⦃ s' => ∃ σ', specSporadicAssert t.bv σ = ({((), σ')}, False) ∧
      FootEq T E R B (L.mem s) (L.mem s') ∧ KView σ σ' ∧
      Notif.FootEq N T (L.mem s) (L.mem s') ∧ Notif.KView σ σ' ∧ SR s' σ' ⦄
  switchTo : ∀ s (a : A) σ (t : U64), EpStateRel T E R B (L.mem s) σ → SR s σ → t ∈ T →
    (do
      let s1 ← sched.possible_switch_to st s t
      ok (s1, a)) ⦃ r => r.2 = a ∧ TailPostN st N T E R B SR s σ (Fl4Spec.possibleSwitchTo t.bv) r.1 ⦄

end Defs

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st] {N T E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {SR : S → Fl4Spec.State Unit → Prop}

/-- **The step lemmas for the endpoint relation.** -/
theorem EpHyps.steps (hH : EpHyps st T E R B SR) (hBf : EpBufHyps st T E R B SR)
    (hBm : EpBufMapHyps st T E R B SR) (NS : Fl4Spec.ThreadState → Prop) (hNS : ∀ ts, tsCode ts ≠ 6 → NS ts) :
    EpSteps st A ar T E R B SR NS where
  ns_ep := hNS
  deq hP s σ hR hSR _ he _ hk _ hd := ep_dequeue_rel hH hP s σ hR hSR he hk hd
  xregs hP s a σ hR hSR _ _ hs hr hne _ _ hks hkr hf hrb ep badge grant hcaps :=
    do_ipc_transfer_regs hH hBf hP s a σ hR hSR hs hr hne hks hkr hf hrb ep badge grant hcaps
  xbuf hP s a σ hR hSR _ _ hs hr hne _ _ hks hkr hf _ hrb ep badge grant hcaps :=
    do_ipc_transfer_buf hH hBf hBm hP s a σ hR hSR hs hr hne hks hkr hf hrb ep badge grant hcaps
  link hP s σ hR hSR _ hr _ hkr _ ht := reply_link_rel hH hP s σ hR hSR hr hkr ht
  unlink hP s σ hR hSR _ ht _ hk _ _ _ hst hr _ hkr hback hq :=
    reply_unlink_rel hH hP s σ hR hSR ht hk hst hr hkr hback hq
  sts hP s σ hR hSR _ ht _ hk hq _ ts hts code hcode := set_thread_state_rel hH hP s σ hR hSR ht hk hq ts hts code hcode
  push hP s a σ hR hSR _ _ ht _ _ hkt hkd hq _ _ hr _ hkr := reply_push_rel hH hP s a σ hR hSR ht hkt hkd hq hr hkr

/-- The SC hypotheses for `SRN`. -/
theorem EpScHyps.srn (h : EpScHyps st T E R B SR) : EpScHyps st T E R B (SRN st N T SR) :=
  ⟨fun s σ t x hS hk ht => h.scRel s σ t x hS.1 hk ht, h.sporadicSc⟩

/-- The tails for `SRN`. -/
theorem CombTailHyps.tailN (h : CombTailHyps st A N T E R B SR) (hP : CPlaced N T E R B) :
    EpTailHyps st A T E R B (SRN st N T SR) :=
  ⟨fun s a σ t hR hS ht => WP.spec_mono (h.wakeTail s a σ t hR hS.1 ht) fun _ ⟨h1, h2, σ', h3, h4, h5, h6, h7, h8⟩ =>
      ⟨h1, h2, σ', h3, h4, h5, h8, hS.2.frame hP.n h6 h7⟩,
   fun s σ t hR hS ht => WP.spec_mono (h.sporadicAssert s σ t hR hS.1 ht) fun _ ⟨σ', h1, h2, h3, h4, h5, h6⟩ =>
      ⟨σ', h1, h2, h3, h6, hS.2.frame hP.n h4 h5⟩,
   fun s a σ t hR hS ht => WP.spec_mono (h.switchTo s a σ t hR hS.1 ht) fun _ ⟨h1, h2, σ', h3, h4, h5, h6, h7, h8⟩ =>
      ⟨h1, h2, σ', h3, h4, h5, h8, hS.2.frame hP.n h6 h7⟩⟩

end

end

end Fl4Proofs.P3.Endp
