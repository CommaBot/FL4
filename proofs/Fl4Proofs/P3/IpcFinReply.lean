/-
P3 (DESIGN.md §9), IPC: **a reply cap's finalisation on `IRel`, the slots
kept** (`XFinHyps.reply`).

* `ipcCore_topF`: the IPC core's relation with the frame since `s0`
  (`IFrame`) carried: the endpoint writes and `schedule_tcb` write words of
  the other objects. Every lemma over an `IpcCore` then keeps the frame.
* `callW'_oobj`, `remove_topF`: `remove_top` (`reply_remove` on `IRel`) with
  the frame.
* `xFinReply_of`: **`XFinHyps.ep`**'s reply analogue: the reply's thread,
  blocked on the reply (`reply_remove`) or on a receive with the reply
  (`cancel_ipc`); at `Z.mv Z.G V'` (`XTopAt.irel_same`), the spec's
  finalisation keeping the caps (`finReply_nkc`). Named (`ReplyFinPre`, at
  the `XTopAt` states): `BufWordRel`, the IPC placement, `RemoveOK` and
  `BlockedScActive` at the `IRel` states (as `remove_top`), `SchedValid`,
  `ObjCover` and `Inv` (for `cancel_ipc`), the reply's thread blocked on it
  (l4v `sym_refs`), the reply caps' objects among `Z.R`.
-/
import Fl4Proofs.P3.IpcCancelAllIpc
import Fl4Proofs.P3.IpcJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched Classical

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- **The IPC core with the frame since `s0`** (module docstring). -/
theorem ipcCore_topF (hP : EPlaced T E R B) (s0 : S) :
    IpcCore st N T E R B (fun s σ => SRT st th cr N T C E R B c (SRE st N T C E R B c) s σ ∧
      IFrame (L := L) th s0 s) where
  stableE s s' σ σ' h hW hK :=
    ⟨(ipcCore_top (st := st) (th := th) (cr := cr) (N := N) (C := C) (c := c) hP).stableE s s' σ σ' h.1 hW hK,
      h.2.trans (SRT.iframe_of h.1 hW fun b hb => iwords_oobj (EWrite.iwords hb))⟩
  scheduleTcb s σ t hR hM h ht :=
    WP.spec_mono (WP.spec_and
      ((ipcCore_top (st := st) (th := th) (cr := cr) (N := N) (C := C) (c := c) hP).scheduleTcb s σ t hR hM h.1 ht)
      (schedule_tcb_sfoot h.1.2.1 (WritesIn.refl _ _) t)) fun _ ⟨⟨hf, hS'⟩, hw⟩ =>
      ⟨hf, hS', h.2.trans (SRT.iframe_of h.1 hw fun b hb => tfoot_oobj h.1.2.1 (Or.inl (KFoot.of_sfoot hb)))⟩

/-- **The call-stack words are words of the other objects.** -/
theorem callW'_oobj (hP0 : IPlaced N T E R B) {s : S} {σ : Fl4Spec.State Unit} (hS : SchedRel st N T C c s σ)
    {b : U64} (h : CallW' R C b) : Vs.OObj st N T C E R B c s σ b := by
  have hP := hP0.e
  rcases h with ⟨r, hr, e⟩ | ⟨q, hq, rfl⟩
  · have hrA := hP.rep r hr
    have hA' : r.val % 32 = 0 ∧ r ≠ 0#u64 ∧ r.val + 32 ≤ 2 ^ 64 :=
      ⟨hrA.1, fun e => hrA.2.1 (by rw [e]; rfl), hrA.2.2⟩
    have hv : b.val = r.val + 16 ∨ b.val = r.val + 8 := by
      rcases e with rfl | rfl
      · exact Or.inl (rNextA_val hA')
      · exact Or.inr (rPrevA_val hA')
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, hr, by omega, by omega⟩))))
  · obtain ⟨Q, R0, hc, hs⟩ := hS.lists
    obtain ⟨-, hvq, hsz⟩ := sc_reply_word hS hq
    obtain ⟨x, n, hk, -⟩ := hs.scs q hq
    have hobj : Sched.ScObj q n (scReplyA q) := by have := hsz x n hk; unfold Sched.ScObj; rw [hvq]; omega
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, hq, x, n, hk, hobj⟩))))))

set_option maxHeartbeats 4000000 in
/-- `remove_top` with the frame (`IFrame`). -/
theorem remove_topF (hP0 : IPlaced N T E R B)
    (hD : ∀ s σ (r t : U64), IRel st th cr N T C E R B c s σ → r ∈ R → t ∈ T → RemoveOK st N T C R c s σ r t)
    (hJ : ∀ s σ, IRel st th cr N T C E R B c s σ → BlockedScActive σ) :
    ∀ s (a : A) σ (r t : U64) (x : Fl4Spec.Tcb), IRel st th cr N T C E R B c s σ → r ∈ R → t ∈ T →
      σ.kheap t.bv = some (.tcb x) → x.tcbState = .blockedOnReply r.bv →
      ipc.reply_remove st ar s a r t ⦃ res => res.2 = a ∧ ∃ σ' x',
        Fl4Spec.replyRemove (Z := Unit) t.bv r.bv σ = ({((), σ')}, False) ∧ IRel st th cr N T C E R B c res.1 σ' ∧
        σ'.kheap t.bv = some (.tcb x') ∧ x'.tcbState = .inactive ∧ x'.tcbFault = x.tcbFault ∧
        (∀ p y n, σ'.kheap p = some (.schedContext y n) → y.scTcb = some t.bv → Fl4Spec.scActive y = true) ∧
        (∀ p y, p ≠ t.bv → σ.kheap p = some (.tcb y) → ∃ y', σ'.kheap p = some (.tcb y') ∧
          y'.tcbFault = y.tcbFault ∧ y'.tcbState = y.tcbState) ∧ IFrame (L := L) th s res.1 ⦄ := by
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
  have hF5 : IFrame (L := L) th s s5 := IRel.iframe_of hX hw5 fun b hb =>
    hb.elim (fun h => tfoot_oobj hX.2.2.1 (Or.inl h)) (fun h => callW'_oobj hP0 hX.2.2.1 h)
  refine WP.spec_mono (WP.spec_and (reply_unlink_irel hP0 s5 σ5 hX5 ht hkt5 (by rw [et5]; exact hst) hr hkr5
    (er5.trans hrt)) (reply_unlink_iframe hP0 hX5 ht hr hkr5)) ?_
  rintro s6 ⟨⟨hul, hX6⟩, hF6⟩
  obtain ⟨y5, hy5, hso5, -⟩ := hK.tcb hk
  rw [hkt5] at hy5; cases hy5
  have hrt' : r.bv ≠ t.bv := kheap_ne hkr hk (fun _ h1 h2 => by subst h1; cases h2)
  refine ⟨rfl, _, { xt5 with tcbState := .inactive }, replyRemove_split hkr hrt hsp hul, hX6,
    by simp [unlinkSt, stsAct_kheap, updK], rfl, by rw [hso5],
    remove_act (hJ s σ hX) hk hst hsp (fun p y n hp => by
      have hpr : p ≠ r.bv := by rintro rfl; simp [unlinkSt, stsAct_kheap, updK, hrt'] at hp
      have hpt : p ≠ t.bv := by rintro rfl; simp [unlinkSt, stsAct_kheap, updK] at hp
      simpa [unlinkSt, stsAct_kheap, updK, hpr, hpt] using hp), fun p y hp hy => ?_, hF5.trans hF6⟩
  obtain ⟨y', hy', hso, -⟩ := hK.tcb hy
  obtain ⟨y'', hy'', es⟩ := huf.2 _ y hy
  rw [hy'] at hy''; cases hy''
  have hpr : p ≠ r.bv := fun e => by rw [e, hkr] at hy; cases hy
  refine ⟨y', by simp [unlinkSt, stsAct_kheap, updK, hp, hpr, hy'], by rw [hso], es⟩

end

end

end Fl4Proofs.P3.Ipc

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section Spec
open Fl4Spec

/-- The spec's reply finalisation, a reply with no thread. -/
theorem finReply_mem_none {σ : State Unit} {r : ObjRef} {R : CapRights} {xr : Reply}
    (hkr : σ.kheap r = some (.reply xr)) (htp : xr.replyTcb = none) :
    ((Cap.nullCap, Cap.nullCap), σ) ∈ (finaliseCap (Z := Unit) (.replyCap r R) true σ).1 := by
  unfold finaliseCap NonDet.liftM NonDet.when
  simp only [↓reduceIte]
  refine mem_bind_nd (x := ((), σ)) ?_ (Set.mem_singleton _)
  refine mem_bind_nd (x := (none, σ)) ?_ (Set.mem_singleton _)
  show _ ∈ (NonDet.liftM Reply.replyTcb (getReply r) σ).1
  unfold NonDet.liftM
  exact mem_bind_nd (x := (xr, σ)) (by rw [getReply_eq hkr]; rfl) (by rw [htp]; rfl)

/-- The spec's reply finalisation, the reply's thread in state `ts`. -/
theorem finReply_mem_some {σ σ3 : State Unit} {r : ObjRef} {R : CapRights} {xr : Reply}
    (hkr : σ.kheap r = some (.reply xr)) {tp : ObjRef} (htp : xr.replyTcb = some tp) {xt : Tcb}
    (hkt : σ.kheap tp = some (.tcb xt))
    (h : ((), σ3) ∈ ((match xt.tcbState with
      | .blockedOnReply r' => replyRemove (Z := Unit) tp r'
      | _ => cancelIpc tp) σ).1) :
    ((Cap.nullCap, Cap.nullCap), σ3) ∈ (finaliseCap (Z := Unit) (.replyCap r R) true σ).1 := by
  unfold finaliseCap NonDet.liftM NonDet.when
  simp only [↓reduceIte]
  refine mem_bind_nd (x := ((), σ3)) ?_ (Set.mem_singleton _)
  refine mem_bind_nd (x := (some tp, σ)) ?_ ?_
  · show _ ∈ (NonDet.liftM Reply.replyTcb (getReply r) σ).1
    unfold NonDet.liftM
    exact mem_bind_nd (x := (xr, σ)) (by rw [getReply_eq hkr]; rfl) (by rw [htp]; rfl)
  · refine mem_bind_nd (x := (xt.tcbState, σ)) (by rw [getThreadState_eq hkt]; rfl) ?_
    cases hs : xt.tcbState <;> rw [hs] at h <;> exact h

end Spec

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

theorem finWork_reply {p : U64} {g : Bool} {fb : Bool} (h : FinWork (.Reply p g) fb) : fb = true := by
  unfold FinWork at h
  rcases h with ⟨hb | ⟨f, l, o, e, -⟩, -⟩ | ⟨p, sz, r, d, ep, asid, va, e⟩
  · exact hb
  · cases e
  · cases e

/-- **What a reply cap's finalisation at `XTop` reads** (module docstring). -/
def ReplyFinPre (Z : XSets) (s : S) (σ : Fl4Spec.State Unit) : Prop :=
  BufWordRel Z.T (L.mem s) σ ∧ IPlaced Z.N Z.T Z.E Z.R Z.B ∧
  (∀ s' σ' (r t : U64), IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ' → r ∈ Z.R →
    t ∈ Z.T → RemoveOK st Z.N Z.T Z.C Z.R Z.c s' σ' r t) ∧
  (∀ s' σ', IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ' → BlockedScActive σ') ∧
  SchedValid σ ∧ ObjCover Z.N Z.T Z.E Z.R Z.C σ ∧ Inv σ ∧
  (∀ r ∈ Z.R, ∀ xr t, σ.kheap r.bv = some (.reply xr) → xr.replyTcb = some t →
    ∃ xt, σ.kheap t = some (.tcb xt) ∧
      (xt.tcbState = .blockedOnReply r.bv ∨ ∃ e d, xt.tcbState = .blockedOnReceive e (some r.bv) d)) ∧
  ∀ sl p g, AbsSlot Z.th sl → capAt (L.mem s) (cslotAddr sl) = ok (.Reply p g) → p ∈ Z.R

set_option maxHeartbeats 8000000 in
/-- **`XFinHyps.reply` holds** (module docstring). -/
theorem xFinReply_of {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap}
    (hpre : ∀ (Z : XSets) s a σ, Z.th = th → XTopAt (L := L) AR Z s a σ → ReplyFinPre (L := L) Z s σ) :
    XFinAt (L := L) arI FinReplyK AR th := by
  intro Z s a σ sl c hth hX hK hTh ⟨p, g, hc0⟩ hDS hA hc hk hw
  subst hth hc0
  obtain ⟨hBW, hP0, hD, hJ, hSV, hOC, hInv, hlink, hpR⟩ := hpre Z s a σ rfl hX
  have hp := hpR sl p g hA hc
  have hP := hP0.e
  have hfin := finWork_reply hw
  set fin := decide (Fl4Spec.isFinalCap' (absCap (.Reply p g)) σ) with hfd
  have hI := hX.irelK hK hBW
  have hAR : AR a σ.archState.x64CurrentCr3 := hX.fin.1.1.2.2.2.2.2.2
  obtain ⟨xr, hkr, hxr⟩ := hI.1.toE.reply p hp
  -- the post from the spec's outcome, `IRel` and the frame
  have fin3 : ∀ (s3 : S) (σ3 : Fl4Spec.State Unit),
      ((absCap capability.Cap.Null, absCap capability.Cap.Null), σ3) ∈
        (Fl4Spec.finaliseCap (Z := Unit) (absCap (.Reply p g)) fin σ).1 →
      IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s3 σ3 → IFrame (L := L) Z.th s s3 →
      FinXPost (L := L) AR Z s σ sl (.Reply p g) ((.Null, .Null), s3, a) := by
    intro s3 σ3 hmem hI3 hk3
    have hck := finReply_nkc p.bv _ fin σ _ hmem
    obtain ⟨V', hX3⟩ := XTopAt.irel_same hX hI3 hAR hk3.1 hck.cdt hck.orig hck.ks hk3.2
    exact ⟨rfl, trivial, trivial, σ3, Z.G, hmem, DState.of_same hDS hk3.1 hX3.rel.2.1 hck.ks,
      by rw [hk3.1.capV hA.isSlot]; exact capV_of_capAt hc, fun y hy _ => Or.inl (hk3.1.capV hy),
      MdbStep.of_same hDS.1.2.2.1 hk3.1, ⟨V', hX3⟩, hk3.2⟩
  have hfc : objects.finalise_cap st arI s a (.Reply p g) fin false =
      objects.finalise_cap_object st arI s a (.Reply p g) fin := by
    simp [objects.finalise_cap]
  rw [hfc]
  unfold objects.finalise_cap_object
  simp only [hfin, ↓reduceIte]
  step with Endp.obj.Reply.tcb.spec as ⟨i, hi⟩
  step with obj.Tcb.is_null.spec as ⟨b0, hb0⟩
  by_cases h0 : i = 0#u64
  · have hb : b0 = true := by rw [hb0, h0]; rfl
    simp only [hb, ↓reduceIte, WP.spec_ok]
    refine fin3 s σ ?_ hI (IFrame.refl _ _)
    rw [hfin]
    exact finReply_mem_none hkr (by rw [hxr, ← hi, h0, Notif.optRef_zero])
  have hb : b0 = false := by rw [hb0]; simp [h0]
  simp only [hb, Bool.false_eq_true, ↓reduceIte]
  have htp : xr.replyTcb = some i.bv := by rw [hxr, ← hi, Notif.optRef_ne h0]
  obtain ⟨xt, hkt, hst⟩ := hlink p hp xr i.bv hkr htp
  obtain ⟨t', ht', et⟩ := hOC.tcb _ xt hkt
  have e' : t' = i := P1.eq_of_bv et
  subst e'
  have hTRE := hI.1.toE.at_tcb ht' hkt
  step with Fl4Proofs.P1.obj.Tcb.state.spec as ⟨w, hw⟩
  have hv : w.val = tsCode xt.tcbState := by rw [hw, P1.stA_eq, ← tStA_eq]; exact hTRE.st
  have e5 : sched.TS_BLOCKED_ON_REPLY = 5#u64 := by unfold sched.TS_BLOCKED_ON_REPLY; rfl
  rcases hst with hs | ⟨e, d, hs⟩
  · have heq : w = sched.TS_BLOCKED_ON_REPLY := UScalar.eq_of_val_eq (by rw [hv, hs, e5]; rfl)
    simp only [heq, ↓reduceIte]
    refine WP.spec_bind (remove_topF hP0 (fun s' σ' r t h hr ht => hD s' σ' r t h hr ht)
      (fun s' σ' h => hJ s' σ' h) s a σ p t' xt hI hp ht' hkt hs) ?_
    rintro ⟨s1, a1⟩ ⟨rfl, σ1, x1, he1, hI1, -, -, -, -, -, hF1⟩
    show (ok ((capability.Cap.Null, capability.Cap.Null), s1, a1)) ⦃ _ ⦄
    rw [WP.spec_ok]
    refine fin3 s1 σ1 ?_ hI1 hF1
    rw [hfin]
    refine finReply_mem_some hkr htp hkt ?_
    rw [hs]; show ((), σ1) ∈ (Fl4Spec.replyRemove t'.bv p.bv σ).1
    rw [he1]; exact Set.mem_singleton _
  · have hne : w ≠ sched.TS_BLOCKED_ON_REPLY := fun h => by rw [h, e5, hs] at hv; simp [tsCode] at hv
    have heq : w = sched.TS_BLOCKED_ON_RECV := UScalar.eq_of_val_eq (by rw [hv, hs, tsVals.2.2.1]; rfl)
    have hRR : sched.TS_BLOCKED_ON_RECV ≠ sched.TS_BLOCKED_ON_REPLY := by rw [e5, tsVals.2.2.1]; decide
    simp only [heq, hRR, ↓reduceIte]
    have hrb : Fl4Spec.receiveBlocked xt.tcbState = true := by rw [hs]; rfl
    have hF : ∀ s0 σ0 (t : U64) (x : Fl4Spec.Tcb),
        (SRT st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c
          (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c) s0 σ0 ∧ IFrame (L := L) Z.th s s0) → t ∈ Z.T →
        σ0.kheap t.bv = some (.tcb x) →
        (SRT st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c
          (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c) (L.wr s0 (tFaultA t) 0#u64)
          (updK σ0 t.bv (.tcb { x with tcbFault := none })) ∧ IFrame (L := L) Z.th s (L.wr s0 (tFaultA t) 0#u64)) := by
      intro s0 σ0 t x h ht hk0
      have hta := hP.tcb t ht
      refine ⟨fault_clear_top h.1 ht hk0, h.2.trans (SRT.iframe_of h.1 (writesIn_wr (a_fault hta).1) fun b hb => ?_)⟩
      subst hb
      exact Or.inr (Or.inr (Or.inl ⟨t, ht, by rw [val_fault hta]; omega, by rw [val_fault hta]; omega⟩))
    refine WP.spec_bind (cancel_ipc_recvI (ipcCore_topF hP s) hF hP0 s a σ hI.1 ⟨hI.2, IFrame.refl _ _⟩ ht' hkt hrb
      (cancelRecvHyp_of hI.1.toE hSV hOC hInv ht' hkt hrb)) ?_
    rintro ⟨s1, a1⟩ ⟨rfl, σ1, x1, he1, hR1, hS1, -, -, -⟩
    show (ok ((capability.Cap.Null, capability.Cap.Null), s1, a1)) ⦃ _ ⦄
    rw [WP.spec_ok]
    refine fin3 s1 σ1 ?_ ⟨hR1, hS1.1⟩ hS1.2
    rw [hfin]
    refine finReply_mem_some hkr htp hkt ?_
    rw [hs]; show ((), σ1) ∈ (Fl4Spec.cancelIpc t'.bv σ).1
    rw [he1]; exact Set.mem_singleton _

end

end

end Fl4Proofs.P3
