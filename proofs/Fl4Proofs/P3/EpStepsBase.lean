/-
P3 (DESIGN.md §9), endpoints: **the step lemmas of the transfer theorems,
bundled** (`EpSteps`, and `EpStepsBuf` with the transfer into a receive
buffer), so that the transfer theorems are proved once (`X_gen`, in their
files) and instantiated for the endpoint relation alone (`EpHyps.steps`,
`EpHyps.stepsBuf`: the theorems `X`) and for the combined relation
(`CombHyps.steps`, EpStepsN: the theorems `X_comb`, EpCombIpc).

The fields state the steps for an abstract `SR`, as in their lemmas; the
threads whose state is set must satisfy `NS` on their spec state, and `NS`
holds of every state but `BlockedOnNotification` (`ns_ep`).
-/
import Fl4Proofs.P3.EpXferBuf2
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Defs
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]

/-- What a transfer step keeps of the spec's heap: every object but the
receiver's TCB, or a CNode of the same size (a cap transferred into a
receive slot). -/
def KeepNC (σ σ' : Fl4Spec.State Unit) (rcv : Fl4Spec.ObjRef) : Prop :=
  ∀ p, p ≠ rcv → σ'.kheap p = σ.kheap p ∨
    ∃ r cs cs', σ.kheap p = some (.cnode r cs) ∧ σ'.kheap p = some (.cnode r cs')

theorem KeepNC.of_eq {σ σ' : Fl4Spec.State Unit} {rcv : Fl4Spec.ObjRef}
    (h : ∀ p, p ≠ rcv → σ'.kheap p = σ.kheap p) : KeepNC σ σ' rcv := fun p hp => Or.inl (h p hp)

theorem KeepNC.fwd {σ σ' : Fl4Spec.State Unit} {rcv : Fl4Spec.ObjRef} (h : KeepNC σ σ' rcv)
    {p : Fl4Spec.ObjRef} (hp : p ≠ rcv) {o : Fl4Spec.KernelObject} (hk : σ.kheap p = some o)
    (ho : ∀ r cs, o ≠ .cnode r cs) : σ'.kheap p = some o := by
  rcases h p hp with e | ⟨r, cs, cs', h1, -⟩
  · rw [e, hk]
  · rw [hk] at h1; cases h1; exact absurd rfl (ho r cs)

theorem KeepNC.bwd {σ σ' : Fl4Spec.State Unit} {rcv : Fl4Spec.ObjRef} (h : KeepNC σ σ' rcv)
    {p : Fl4Spec.ObjRef} (hp : p ≠ rcv) {o : Fl4Spec.KernelObject} (hk : σ'.kheap p = some o)
    (ho : ∀ r cs, o ≠ .cnode r cs) : σ.kheap p = some o := by
  rcases h p hp with e | ⟨r, cs, cs', -, h2⟩
  · rw [← e, hk]
  · rw [hk] at h2; cases h2; exact absurd rfl (ho r cs')

/-- The step lemmas (see the module docstring). `GC` says whether the
transfers may carry caps (a grant with extra caps): when it does not hold,
the transfers carry none (`hcaps`). -/
structure EpSteps (A : Type) (ar : machine.Arch A) (T E R : Set U64) (B : Set (U64 × Fl4Spec.Word))
    (SR : S → Fl4Spec.State Unit → Prop) (NS : Fl4Spec.ThreadState → Prop) (GC : Prop) : Prop where
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
    (hcaps : GC ∨ grant = false ∨ ipcBufOf false xs = none ∨
      Fl4Spec.unat (Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miExtraCaps = 0),
    ipc.do_ipc_transfer st ar s a snd ep badge grant rcv ⦃ s' =>
      Fl4Spec.doIpcTransfer (Z := Unit) snd.bv (some ep.bv) badge.bv grant rcv.bv σ =
        ({((), updK σ rcv.bv (.tcb (xferTcb xr xs badge.bv)))}, False) ∧
      EpStateRel T E R B (L.mem s') (updK σ rcv.bv (.tcb (xferTcb xr xs badge.bv))) ∧
      SR s' (updK σ rcv.bv (.tcb (xferTcb xr xs badge.bv))) ∧
      Agree (L.mem s) (L.mem s') (fun b => ¬ RcvReg rcv b) ⦄
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

/-- The step lemmas with the transfer into a receive buffer. -/
structure EpStepsBuf (A : Type) (ar : machine.Arch A) (T E R : Set U64) (B : Set (U64 × Fl4Spec.Word))
    (SR : S → Fl4Spec.State Unit → Prop) (NS : Fl4Spec.ThreadState → Prop) (GC : Prop) : Prop
    extends EpSteps st A ar T E R B SR NS GC where
  xbuf : ∀ (hP : EPlaced T E R B)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr)) (hf : xs.tcbFault = none)
    {rp : Fl4Spec.ObjRef} (hrb : ipcBufOf true xr = some rp) (ep badge : U64) (grant : Bool)
    (hcaps : GC ∨ grant = false ∨ ipcBufOf false xs = none ∨
      Fl4Spec.unat (Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miExtraCaps = 0),
    ipc.do_ipc_transfer st ar s a snd ep badge grant rcv ⦃ s' => ∃ σ',
      Fl4Spec.doIpcTransfer (Z := Unit) snd.bv (some ep.bv) badge.bv grant rcv.bv σ = ({((), σ')}, False) ∧
      EpStateRel T E R B (L.mem s') σ' ∧ SR s' σ' ∧
      Agree (L.mem s) (L.mem s') (fun b => AllTF T b ∧ ¬ RcvReg rcv b ∧ ¬ BufW B b) ∧
      KeepNC σ σ' rcv.bv ∧
      ∃ x', σ'.kheap rcv.bv = some (.tcb x') ∧ x'.tcbState = xr.tcbState ⦄

end Defs

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st] {T E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {SR : S → Fl4Spec.State Unit → Prop}

/-- **The step lemmas for the endpoint relation.** -/
theorem EpHyps.steps (hH : EpHyps st T E R B SR) (hBf : EpBufHyps st T E R B SR)
    (NS : Fl4Spec.ThreadState → Prop) (hNS : ∀ ts, tsCode ts ≠ 6 → NS ts) :
    EpSteps st A ar T E R B SR NS False where
  ns_ep := hNS
  deq hP s σ hR hSR _ he _ hk _ hd := ep_dequeue_rel hH hP s σ hR hSR he hk hd
  xregs hP s a σ hR hSR _ _ hs hr hne _ _ hks hkr hf hrb ep badge grant hcaps :=
    do_ipc_transfer_regs hH hBf hP s a σ hR hSR hs hr hne hks hkr hf hrb ep badge grant (hcaps.resolve_left id)
  link hP s σ hR hSR _ hr _ hkr _ ht := reply_link_rel hH hP s σ hR hSR hr hkr ht
  unlink hP s σ hR hSR _ ht _ hk _ _ _ hst hr _ hkr hback hq :=
    reply_unlink_rel hH hP s σ hR hSR ht hk hst hr hkr hback hq
  sts hP s σ hR hSR _ ht _ hk hq _ ts hts code hcode := set_thread_state_rel hH hP s σ hR hSR ht hk hq ts hts code hcode
  push hP s a σ hR hSR _ _ ht _ _ hkt hkd hq _ _ hr _ hkr := reply_push_rel hH hP s a σ hR hSR ht hkt hkd hq hr hkr

/-- **The step lemmas for the endpoint relation**, with the buffer transfer. -/
theorem EpHyps.stepsBuf (hH : EpHyps st T E R B SR) (hBf : EpBufHyps st T E R B SR)
    (hBm : EpBufMapHyps st T E R B SR) (NS : Fl4Spec.ThreadState → Prop) (hNS : ∀ ts, tsCode ts ≠ 6 → NS ts) :
    EpStepsBuf st A ar T E R B SR NS False where
  toEpSteps := EpHyps.steps hH hBf NS hNS
  xbuf hP s a σ hR hSR _ _ hs hr hne _ _ hks hkr hf _ hrb ep badge grant hcaps :=
    WP.spec_mono (do_ipc_transfer_buf hH hBf hBm hP s a σ hR hSR hs hr hne hks hkr hf hrb ep badge grant
      (hcaps.resolve_left id)) fun _ ⟨σ', h1, h2, h3, h4, h5, h6⟩ =>
      ⟨σ', h1, h2, h3, h4.mono fun _ h => h.2, KeepNC.of_eq h5, h6⟩

end

end

end Fl4Proofs.P3.Endp
