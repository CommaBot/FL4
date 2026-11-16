/-
P3 (DESIGN.md §9), IPC: **`reply_remove` on `IRel`** (`ReplyHyps.remove`),
its IPC half.

* `reply_unlink_irel`: `reply_unlink` of a thread blocked on the reply
  (`reply_remove`'s last step, l4v `reply_unlink_tcb`) refines on `IRel`:
  IpcCancel's `reply_unlink_c` for `SRT … SRE` (`ipcCore_top`), the thread in
  no endpoint queue from its state.

The reply path's spec facts, reduced to l4v invariants (named, for the final
fold):
* `TmoCapsValid`: l4v `valid_cap` for the TCBs' timeout-handler caps that are
  endpoint caps (`ep_at`), the one valid-caps fact; with `ObjCover` it gives
  `epE` (`epE_of`).
* `postponeOK_of`: `PostponeOK` from the Sc proofs' `Inv` (l4v
  `valid_release_q`, `sorted_release_q`, `sym_refs` of the SC links) and the
  thread not released; `not_released_of`: a thread that is not runnable is
  not released, by `Inv.rel` (l4v `valid_release_q`: release-queue members
  are runnable). Across the reply this is needed at the state before the
  receiver's restart, where it is blocked on the reply, with the release
  queue unchanged by the restart.
-/
import Fl4Proofs.P3.IpcDonate
import Fl4Proofs.P3.ScCallRemove
import Fl4Proofs.P3.ScCallUnlink
import Fl4Proofs.P3.ScRemoveKeep
open Aeneas Aeneas.Std Result


/-! ## The spec's call-stack part of `reply_remove` changes only scheduling fields -/

namespace Fl4Proofs.P3.Sched
open Fl4Spec

noncomputable section

theorem nkt_replyRemoveSc (t r : ObjRef) : NKT (replyRemoveSc t r) := by
  unfold replyRemoveSc replyUnlinkSc getTcbObjRef getReply getSimpleKo
  repeat' (first | exact nkt_schedContextDonate _ _ | nkt_step | (unfold NonDet.when; split) | split)

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

section Unlink
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- The spec's state after `reply_unlink_tcb`. -/
def unlinkSt (σ : Fl4Spec.State Unit) (t r : Fl4Spec.ObjRef) (x : Fl4Spec.Tcb) (xr : Fl4Spec.Reply) :
    Fl4Spec.State Unit :=
  stsAct (updK (updK σ r (.reply { xr with replyTcb := none })) t (.tcb { x with tcbState := .inactive })) t

/-- **`reply_unlink` of a thread blocked on the reply, on `IRel`.** -/
theorem reply_unlink_irel (hP0 : IPlaced N T E R B) (s : S) (σ : Fl4Spec.State Unit)
    (hX : IRel st th cr N T C E R B c s σ) {t : U64} (ht : t ∈ T) {x : Fl4Spec.Tcb}
    (hk : σ.kheap t.bv = some (.tcb x)) {r : U64} (hst : x.tcbState = .blockedOnReply r.bv) (hr : r ∈ R)
    {xr : Fl4Spec.Reply} (hkr : σ.kheap r.bv = some (.reply xr)) (hback : xr.replyTcb = some t.bv) :
    ipc.reply_unlink st s r t ⦃ s' =>
      Fl4Spec.replyUnlinkTcb (Z := Unit) t.bv r.bv σ = ({((), unlinkSt σ t.bv r.bv x xr)}, False) ∧
      IRel st th cr N T C E R B c s' (unlinkSt σ t.bv r.bv x xr) ⦄ := by
  obtain ⟨hIR, hSRT⟩ := hX
  have hP := hP0.e
  have hH := ipcCore_top (st := st) (th := th) (cr := cr) (N := N) (C := C) (c := c) hP
  have hSR := IpcRel.toSRN hIR hSRT
  have hR := hIR.toE
  obtain ⟨x0, hk0, hTR⟩ := hIR.tcb t ht
  rw [hk] at hk0; cases hk0
  have hq := IpcRel.not_ep_queued hIR (t := t) (by rw [hTR.st, hst]; simp [tsCode])
  obtain ⟨e1, hR1, hS1, hA1⟩ := reply_write_rel (hH.epHyps hP0) hP s σ hR hSR.1 hr hkr 0#u64
  have hN1 := ntfn_reply_write hP0.toC hSR.2 hr hA1 hkr { xr with replyTcb := optRef 0#u64 }
  rw [optRef_zero] at e1 hR1 hS1 hN1
  have hrt : r.bv ≠ t.bv := kheap_ne hkr hk (fun _ h1 h2 => by subst h1; cases h2)
  have hk1 : (updK σ r.bv (.reply { xr with replyTcb := none })).kheap t.bv = some (.tcb x) := by
    simp [Ne.symm hrt, hk]
  have hq1 : ∀ e ∈ E, ∀ z, (updK σ r.bv (.reply { xr with replyTcb := none })).kheap e.bv = some (.endpoint z) →
      t.bv ∉ z.epQueue := by
    intro e he z hz
    have hre : r.bv ≠ e.bv := by
      intro h; rw [← h] at hz; simp at hz
    exact hq e he z (by simpa [Ne.symm hre] using hz)
  unfold ipc.reply_unlink
  step as ⟨s1, hs1⟩
  subst hs1
  refine WP.spec_mono (set_thread_state_c hH hP0 hP _ _ hR1 ⟨hS1, hN1⟩ ht hk1 hq1 (by rw [hst]; simp [tsCode])
    .inactive (by simp [tsCode]) sched.TS_INACTIVE (by unfold sched.TS_INACTIVE; rfl)) ?_
  rintro s2 ⟨hR2, hS2⟩
  refine ⟨?_, IpcRel.ofSRN hR2 hS2⟩
  unfold Fl4Spec.replyUnlinkTcb
  rw [nd_bind_one (getReply_eq hkr), nd_bind_one (assert_true hback σ), nd_bind_one (getThreadState_eq hk),
    nd_bind_one (assert_true (Or.inl hst) σ), nd_bind_one e1, Notif.setThreadState_eq _ hk1]
  rfl

end Unlink


/-! ## The reply path's spec facts -/

section Facts
open Fl4Spec

/-- l4v `valid_cap` of an endpoint cap: the object is an endpoint. -/
def EpCapValid (σ : State Unit) (cap : Cap) : Prop :=
  ∀ p bd r, cap = .endpointCap p bd r → ∃ z, σ.kheap p = some (.endpoint z)

/-- **The valid-caps fact** (l4v `valid_objs`' `valid_cap`, for endpoint
caps): every TCB's timeout-handler cap. -/
def TmoCapsValid (σ : State Unit) : Prop :=
  ∀ t x, σ.kheap t = some (.tcb x) → EpCapValid σ x.tcbTimeoutHandler

/-- **`epE` from `ObjCover` and `TmoCapsValid`.** -/
theorem epE_of {N T E R C : Set U64} {σ : State Unit} (hO : Sched.ObjCover N T E R C σ) (hV : TmoCapsValid σ)
    {t : U64} {x : Tcb} (hk : σ.kheap t.bv = some (.tcb x)) {p bd : Word} {r : CapRights}
    (hh : x.tcbTimeoutHandler = .endpointCap p bd r) : ∀ e : U64, e.bv = p → e ∈ E := by
  intro e he
  obtain ⟨z, hz⟩ := hV _ x hk p bd r hh
  obtain ⟨e', he', h'⟩ := hO.ep _ z hz
  have : e = e' := Sched.bv_inj (h'.trans he.symm).symm
  rw [this]; exact he'

/-- **A thread that is not runnable is not released** (`Inv.rel`). -/
theorem not_released_of {σ : State Unit} (hI : Inv σ) {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (hnr : runnable x.tcbState = false) : t ∉ σ.releaseQueue := fun hm => by
  obtain ⟨x', _, _, _, h1, -, h3, -⟩ := hI.rel t hm
  rw [hk] at h1; cases h1; rw [hnr] at h3; cases h3

/-- **`PostponeOK` from `Inv`** and the thread not released. -/
theorem postponeOK_of {σ : State Unit} (hI : Inv σ) {t sc : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (hsc : x.tcbSchedContext = some sc) {y : SchedContext} {n : Nat} (hky : σ.kheap sc = some (.schedContext y n))
    (hnr : t ∉ σ.releaseQueue) : PostponeOK σ t y := by
  refine ⟨hI.relOK, hnr, ?_⟩
  · obtain ⟨y', n', h1, h2⟩ := hI.back t x sc hk hsc
    rw [hky] at h1; cases h1; exact h2

end Facts


/-! ## `reply_remove` on `IRel` -/

section Remove
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- **A scheduling step with call-stack writes keeps `IRel`**: `tk_lift` by
the Sc proofs' `xtop_sc_stepCW`. -/
theorem tk_liftCW (hP0 : IPlaced N T E R B) {s s' : S} {σ σ' : Fl4Spec.State Unit} {ct : Fl4Spec.ObjRef}
    (hX : IRel st th cr N T C E R B c s σ)
    (hW : WritesIn st s s' (fun b => TFoot st T N C c s σ b ∨ CallW' R C b)) (hK : ScTKw (fun p => p = ct) σ σ')
    (hS' : SchedRel st N T C c s' σ') (hN' : NtfnStateRel N T (L.mem s') σ') :
    IRel st th cr N T C E R B c s' σ' := by
  obtain ⟨⟨Z, hth, hN, hT, hC, hE, hR, hB, hc, hZ⟩, hKA⟩ :=
    IRel.xtop (A := Unit) (AR := fun _ c' => c' = cr) (a := ()) hX rfl
  subst hth hN hT hC hE hR hB hc
  have hX' := xtop_sc_stepCW (a' := ()) hZ hP0 (fun n hn => by have := hKA.ntfn n hn; omega)
    (fun r hr => by have := hKA.rep r hr; omega) hW hK hS' hN' id
  have hks : L.ksb s' = L.ksb s := hW.1
  have hcr : σ'.archState.x64CurrentCr3 = cr := hX'.fin.1.1.2.2.2.2.2.2
  have := XTopAt.irelK hX' (by rw [hks]; exact hKA)
  rw [hcr] at this
  exact this

/-- The spec's `reply_remove`: its SC part (`replyRemoveSc`), then
`reply_unlink_tcb`. -/
theorem replyRemove_split {σ σ5 : Fl4Spec.State Unit} {t r : Fl4Spec.ObjRef} {xr : Fl4Spec.Reply}
    (hkr : σ.kheap r = some (.reply xr)) (hrt : xr.replyTcb = some t)
    (hsp : replyRemoveSc t r σ = ({((), σ5)}, False)) {X : Set (Unit × Fl4Spec.State Unit) × Prop}
    (hul : Fl4Spec.replyUnlinkTcb (Z := Unit) t r σ5 = X) :
    Fl4Spec.replyRemove (Z := Unit) t r σ = X := by
  unfold replyRemoveSc at hsp
  rw [nd_gets_bind] at hsp
  unfold Fl4Spec.replyRemove
  rw [nd_bind_one (Fl4Proofs.P3.Endp.getReply_eq hkr)]
  have hass : (Fl4Spec.NonDet.assert (xr.replyTcb = some t) : Fl4Spec.SMonad Unit Unit) σ = ({((), σ)}, False) := by
    show (({x | xr.replyTcb = some t ∧ x = ((), σ)}, ¬ xr.replyTcb = some t) :
      Set (Unit × Fl4Spec.State Unit) × Prop) = ({((), σ)}, False)
    simp [hrt]
  rw [nd_bind_one hass, nd_gets_bind]
  cases hw : Fl4Spec.scWithReply r σ with
  | none =>
    rw [hw] at hsp
    have e := (nd_pure_one hsp).1
    subst e
    exact hul
  | some p =>
    rw [hw] at hsp
    dsimp only at hsp ⊢
    simp only [← nd_assoc_f]
    rw [nd_bind_one hsp]
    exact hul

/-- **What `reply_remove` needs beyond `IRel`** (the Sc proofs' call-stack
relation and invariants, l4v `valid_objs`, `valid_sched`, `sym_refs`): the
call-stack relation `CallRel` and the replies' placement `RPlaced`, `NSC`
and `Inv`, the SCs nonzero and covered, the reply linked back to the thread,
and `reply_remove_refines`' `hdon` and `hrel`. -/
def RemoveOK (st : machine.Store S) [L : LawfulStore st] (N T C R : Set U64) (c : U64) (s : S)
    (σ : Fl4Spec.State Unit) (r t : U64) : Prop :=
  ∃ Lst : U64 → List U64, CallRel (L.mem s) R C σ Lst ∧ RPlaced st N T C R c s σ ∧ NSC N C σ ∧ Inv σ ∧
    (∀ q ∈ C, q ≠ 0#u64) ∧ (∀ p y n, σ.kheap p = some (.schedContext y n) → ∃ q ∈ C, q.bv = p) ∧
    (∀ xr, σ.kheap r.bv = some (.reply xr) → xr.replyTcb = some t.bv) ∧
    ∀ xt, σ.kheap t.bv = some (.tcb xt) →
      (∀ sc ∈ C, ∀ y n, σ.kheap sc.bv = some (.schedContext y n) → (Lst sc).head? = some r →
        xt.tcbSchedContext = none → ∃ f, f ∈ T ∧ y.scTcb = some f.bv ∧ f ≠ t) ∧
      (∀ sc ∈ C, ∀ y n, σ.kheap sc.bv = some (.schedContext y n) → (Lst sc).head? = some r →
        xt.tcbSchedContext = none → inClass xt.tcbState → Fl4Spec.scActive y = true → released σ y)

/-- **The receiver's SCs are active after `reply_remove`**, from [J]
(`BlockedScActive`) before it: an SC then bound to the receiver was bound to
it before (the receiver is blocked on the reply) or is the reply's SC, with a
nonempty call stack (`replyRemoveSc_sck`). -/
theorem remove_act {σ σ5 σ' : Fl4Spec.State Unit} (hJ : BlockedScActive σ) {t r : Fl4Spec.ObjRef}
    {x : Fl4Spec.Tcb} (hk : σ.kheap t = some (.tcb x)) (hst : x.tcbState = .blockedOnReply r)
    (hsp : replyRemoveSc t r σ = ({((), σ5)}, False))
    (h5 : ∀ p y n, σ'.kheap p = some (.schedContext y n) → σ5.kheap p = some (.schedContext y n)) :
    ∀ p y n, σ'.kheap p = some (.schedContext y n) → y.scTcb = some t → Fl4Spec.scActive y = true := by
  intro p y n hp hyt
  obtain ⟨y0, hy0, hm, htc⟩ := replyRemoveSc_sck hsp p y n (h5 p y n hp)
  have ha0 : Fl4Spec.scActive y0 = true := by
    rcases htc with e | ⟨hne, -⟩
    · exact hJ.tcb p y0 n t x hy0 (by rw [← e]; exact hyt) hk (by rw [hst]; rfl)
    · exact hJ.replies p y0 n hy0 hne
  simpa [Fl4Spec.scActive, hm] using ha0

set_option maxHeartbeats 4000000 in
/-- **`reply_remove` on `IRel`** (`ReplyHyps.remove`): the call-stack part
(`reply_remove_refines`) lifted by `tk_liftCW` (the spec's step `ScTKw` by
`nkt_replyRemoveSc`), then `reply_unlink_irel`. Named: `RemoveOK`. -/
theorem remove_top (hP0 : IPlaced N T E R B)
    (hD : ∀ s σ (r t : U64), IRel st th cr N T C E R B c s σ → r ∈ R → t ∈ T → RemoveOK st N T C R c s σ r t)
    (hJ : ∀ s σ, IRel st th cr N T C E R B c s σ → BlockedScActive σ) :
    ∀ s (a : A) σ (r t : U64) (x : Fl4Spec.Tcb), IRel st th cr N T C E R B c s σ → r ∈ R → t ∈ T →
      σ.kheap t.bv = some (.tcb x) → x.tcbState = .blockedOnReply r.bv →
      ipc.reply_remove st ar s a r t ⦃ res => res.2 = a ∧ ∃ σ' x',
        Fl4Spec.replyRemove (Z := Unit) t.bv r.bv σ = ({((), σ')}, False) ∧ IRel st th cr N T C E R B c res.1 σ' ∧
        σ'.kheap t.bv = some (.tcb x') ∧ x'.tcbState = .inactive ∧ x'.tcbFault = x.tcbFault ∧
        (∀ p y n, σ'.kheap p = some (.schedContext y n) → y.scTcb = some t.bv → Fl4Spec.scActive y = true) ∧
        ∀ p y, p ≠ t.bv → σ.kheap p = some (.tcb y) → ∃ y', σ'.kheap p = some (.tcb y') ∧
          y'.tcbFault = y.tcbFault ∧ y'.tcbState = y.tcbState ⦄ := by
  intro s a σ r t x hX hr ht hk hst
  obtain ⟨Lst, hCR, hRP, hN, hI, hC0, hSCs, hback, hx⟩ := hD s σ r t hX hr ht
  obtain ⟨hdon, hrel⟩ := hx x hk
  obtain ⟨xr, hkr, -⟩ := hX.1.toE.reply r hr
  have hrt := hback xr hkr
  refine reply_remove_refines s a σ hX.2.2.1 hX.1.toN hN hI hCR hRP hC0 hSCs hr ht hk hdon hrel _ ?_
  intro s5 σ5 Lst5 h1 h2 h3 h4 h5 h6 h7 huf hcs hsp hw5
  have hK : ScTKw (fun p => p = σ.curThread) σ σ5 :=
    ScTKw.ofFalse (NKT.of_eq (nkt_replyRemoveSc t.bv r.bv) hsp)
  have hX5 := tk_liftCW hP0 hX (hw5.mono fun b hb => hb.elim (fun h => Or.inl (Or.inl h)) Or.inr) hK h1 h2
  obtain ⟨xr5, hkr5, er5⟩ := huf.1 _ xr hkr
  obtain ⟨xt5, hkt5, et5⟩ := huf.2 _ x hk
  refine WP.spec_mono (reply_unlink_irel hP0 s5 σ5 hX5 ht hkt5 (by rw [et5]; exact hst) hr hkr5 (er5.trans hrt)) ?_
  rintro s6 ⟨hul, hX6⟩
  obtain ⟨y5, hy5, hso5, -⟩ := hK.tcb hk
  rw [hkt5] at hy5; cases hy5
  have hrt' : r.bv ≠ t.bv := kheap_ne hkr hk (fun _ h1 h2 => by subst h1; cases h2)
  refine ⟨rfl, _, { xt5 with tcbState := .inactive }, replyRemove_split hkr hrt hsp hul, hX6,
    by simp [unlinkSt, stsAct_kheap, updK], rfl, by rw [hso5],
    remove_act (hJ s σ hX) hk hst hsp (fun p y n hp => by
      have hpr : p ≠ r.bv := by rintro rfl; simp [unlinkSt, stsAct_kheap, updK, hrt'] at hp
      have hpt : p ≠ t.bv := by rintro rfl; simp [unlinkSt, stsAct_kheap, updK] at hp
      simpa [unlinkSt, stsAct_kheap, updK, hpr, hpt] using hp), fun p y hp hy => ?_⟩
  obtain ⟨y', hy', hso, -⟩ := hK.tcb hy
  obtain ⟨y'', hy'', es⟩ := huf.2 _ y hy
  rw [hy'] at hy''; cases hy''
  have hpr : p ≠ r.bv := fun e => by rw [e, hkr] at hy; cases hy
  refine ⟨y', by simp [unlinkSt, stsAct_kheap, updK, hp, hpr, hy'], by rw [hso], es⟩

end Remove

end

end Fl4Proofs.P3.Ipc
