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
