/-
P3 (DESIGN.md §9), IPC: **`send_ipc` to a waiting receiver with SC
donation on `IRel`** (`SendRest`).

* `donNC_irel`: the non-call donation step of `send_ipc` (FL4: the sender's
  SC to a receiver without one, `schedcontext::donate`; l4v
  `sched_context_donate`), by the Sc proofs' `donate_bound_refines` (the
  sender's SC is bound to the sender) lifted by `tk_lift`, the spec's step
  `ScTKw` by `nkt_schedContextDonate`.
* `sendRest_of`: `SendRest` from EpSendD's `send_ipc_recvD_gen`,
  `send_ipc_recv_bufD_gen` (non-call), EpSendX's
  `send_ipc_call_inactiveX_gen` (a call without reply or grant, where the
  donation flag plays no part); named: the call with a reply and a grant
  (`reply_push`'s donation, `hPush`) and the donation facts (`DonNCOK`).
* `ipcVsFrame_endpointD`: IpcXTop's `ipcVsFrame_endpoint` with `SendRest`
  by `sendRest_of`.
-/
import Fl4Proofs.P3.EpSendD
import Fl4Proofs.P3.IpcDonate
import Fl4Proofs.P3.ScDonateB
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

section Don
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- **What the non-call donation needs beyond `IRel`** (l4v `valid_sched`,
the Sc proofs' `NSC` and `Inv`): the sender (the current thread) has an SC,
and a receiver in its class gets a released SC (`donate_bound_refines`'
`hrel`). -/
def DonNCOK (st : machine.Store S) [L : LawfulStore st] (N C : Set U64) (s : S) (σ : Fl4Spec.State Unit)
    (t d : U64) : Prop :=
  L.mem s (scA t) ≠ 0#u64 ∧ NSC N C σ ∧ Inv σ ∧
    ∀ y n, σ.kheap (L.mem s (scA t)).bv = some (.schedContext y n) → ∀ x, σ.kheap d.bv = some (.tcb x) →
      inClass x.tcbState → Fl4Spec.scActive y = true → released σ y

set_option maxHeartbeats 4000000 in
/-- **The non-call donation step of `send_ipc` on `IRel`.** -/
theorem donNC_irel (hP0 : IPlaced N T E R B) (a : A) {t d : U64} (ht : t ∈ T) (hd : d ∈ T) (htd : t ≠ d)
    {xt : Fl4Spec.Tcb}
    (hDN : ∀ s σ, IRel st th cr N T C E R B c s σ → DonNCOK st N C s σ t d) :
    ∀ (s3 : S) (σ3 : Fl4Spec.State Unit) (x3 : Fl4Spec.Tcb), EpStateRel T E R B (L.mem s3) σ3 →
      SRN st N T (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c))) s3 σ3 →
      σ3.kheap t.bv = some (.tcb xt) → σ3.kheap d.bv = some (.tcb x3) → tsCode x3.tcbState ≠ 6 →
      (∀ e'' ∈ E, ∀ z, σ3.kheap e''.bv = some (.endpoint z) → d.bv ∉ z.epQueue) →
      (do
        let i2 ← obj.Tcb.sc st d s3
        if i2 = 0#u64 then
          let i3 ← obj.Tcb.sc st t s3
          schedcontext.donate st ar s3 a i3 d
        else ok (s3, a)) ⦃ r => r.2 = a ∧ ∃ σ4 x4,
        Fl4Spec.NonDet.when (x3.tcbSchedContext = none) (do
          let threadSc ← Fl4Spec.getTcbObjRef Fl4Spec.Tcb.tcbSchedContext t.bv
          Fl4Spec.schedContextDonate (Z := Unit) (Fl4Spec.the threadSc) d.bv) σ3 = ({((), σ4)}, False) ∧
        EpStateRel T E R B (L.mem r.1) σ4 ∧
        SRN st N T (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c))) r.1 σ4 ∧
        σ4.kheap d.bv = some (.tcb x4) ∧ tsCode x4.tcbState ≠ 6 ∧
        (∀ e'' ∈ E, ∀ z, σ4.kheap e''.bv = some (.endpoint z) → d.bv ∉ z.epQueue) ⦄ := by
  intro s3 σ3 x3 hR3 hS3 hkt hkd hns hq
  have hX : IRel st th cr N T C E R B c s3 σ3 := IpcRel.ofSRN hR3 hS3
  have hSM := ScRelM.of hX.1
  obtain ⟨xd', hkd', hdsc⟩ := hSM d hd
  rw [hkd] at hkd'; cases hkd'
  step with Fl4Proofs.P1.obj.Tcb.sc.spec as ⟨i2, hi2⟩
  subst hi2
  by_cases h0 : L.mem s3 (scA d) = 0#u64
  swap
  · rw [if_neg h0, WP.spec_ok]
    have hne : x3.tcbSchedContext ≠ none := by rw [hdsc, Notif.optRef_ne h0]; simp
    refine ⟨rfl, σ3, x3, ?_, hR3, hS3, hkd, hns, hq⟩
    rw [nd_when_false hne]; rfl
  rw [if_pos h0]
  obtain ⟨hsc0, hNSC, hInv, hrel⟩ := hDN s3 σ3 hX
  step with Fl4Proofs.P1.obj.Tcb.sc.spec as ⟨i3, hi3⟩
  subst hi3
  set sc := L.mem s3 (scA t) with hscdef
  have hS := hX.2.2.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hscC := hs.scMem t ht hsc0
  obtain ⟨y, n, hky, hy⟩ := hs.scs sc hscC
  obtain ⟨xt', hkt', htsc⟩ := hSM t ht
  rw [hkt] at hkt'; cases hkt'
  have hxtsc : xt.tcbSchedContext = some sc.bv := by rw [htsc, Notif.optRef_ne hsc0]
  obtain ⟨y', n', hky', hyt⟩ := hInv.back t.bv xt sc.bv hkt hxtsc
  rw [hky] at hky'; cases hky'
  have hx30 : x3.tcbSchedContext = none := by rw [hdsc, h0, optRef_zero]
  refine WP.spec_mono (donate_bound_refines s3 a σ3 hS hX.1.toN hNSC hInv hscC hsc0 hky ht hyt hkt hd hkd hx30 htd
    (hrel y n hky x3 hkd)) ?_
  rintro ⟨s4, a4⟩ ⟨σ', hdon, ha, hS', hN', -, -, hW, hksc, hko, hkf, hkd', -, -, -⟩
  simp only at ha hS' hN' hW hko hkf hkd' ⊢
  have hK : ScTKw (fun p => p = σ3.curThread) σ3 σ' :=
    ScTKw.ofFalse (NKT.of_eq (nkt_schedContextDonate sc.bv d.bv) hdon)
  have hI' := tk_lift hP0 hX (hW.mono fun b hb => hb.elim (fun h => Or.inl (Or.inl h))
    (fun h => Or.inl (Or.inr (Or.inr (h ▸ sw_hdr hS hscC (K := 24#u64) (by simp) (by simp) (by decide)))))) hK hS' hN'
  refine ⟨ha, σ', { x3 with tcbSchedContext := some sc.bv }, ?_, hI'.1.toE, IpcRel.toSRN hI'.1 hI'.2, hkd',
    by simpa using hns, fun e'' he'' z hz => ?_⟩
  · simp only [Fl4Spec.NonDet.when, hx30, ↓reduceIte]
    show (Fl4Spec.getTcbObjRef Fl4Spec.Tcb.tcbSchedContext t.bv >>= _) σ3 = _
    rw [nd_bind_one (getTcbObjRef_eq _ hkt), hxtsc]
    exact hdon
  · have h1 : e''.bv ≠ sc.bv := fun e => by rw [e, hksc] at hz; cases hz
    have h2 : e''.bv ≠ t.bv := fun e => by rw [e, hkf] at hz; cases hz
    have h3 : e''.bv ≠ d.bv := fun e => by rw [e, hkd'] at hz; cases hz
    rw [hko _ h1 h2 h3] at hz
    exact hq e'' he'' z hz

end Don


/-! ## `SendRest` -/

section Rest
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- **What `sendRest_of` does not cover**: a call with a reply and a grant
that donates (`reply_push … true`: `bind_sc_reply`, `sched_context_donate`). -/
def SendPushRest (st : machine.Store S) [L : LawfulStore st] (ar : machine.Arch A)
    (Rel : S → Fl4Spec.State Unit → Prop) (s : S) (a : A) (σ : Fl4Spec.State Unit) (blk : Bool) (badge : U64)
    (g gr : Bool) (t e : U64) : Prop :=
  ∀ (d : U64) q xd, σ.kheap e.bv = some (.endpoint (.recvEP (d.bv :: q))) → σ.kheap d.bv = some (.tcb xd) →
    (g = true ∨ gr = true) → (∀ e' rep dd, xd.tcbState = .blockedOnReceive e' rep dd → rep ≠ none) →
    endpoint.send_ipc st ar s a blk true badge g gr true t e ⦃ r => r.2 = a ∧
      ∃ z ∈ (Fl4Spec.sendIpc (Z := Unit) blk true badge.bv g gr true t.bv e.bv σ).1, Rel r.1 z.2 ⦄

set_option maxHeartbeats 4000000 in
/-- **`SendRest` on `IRel`** (module docstring). -/
theorem sendRest_of (hH : IpcSchedHyps st ar N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hBf : EpBufHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hBm : EpBufMapHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hTl : IpcEpTailHyps st A N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hP : IPlaced N T E R B)
    (hDN : ∀ (t d : U64) s σ, IRel st th cr N T C E R B c s σ → t ∈ T → d ∈ T → DonNCOK st N C s σ t d)
    {e : U64} (he : e ∈ E) (a : A) (blk call : Bool) (badge : U64) (g gr don : Bool) (t : U64)
    (hPush : ∀ s σ, IRel st th cr N T C E R B c s σ →
      SendPushRest st ar (IRel st th cr N T C E R B c) s a σ blk badge g gr t e) :
    ∀ s σ, IRel st th cr N T C E R B c s σ →
      SendRest st ar (IRel st th cr N T C E R B c) T s a σ blk call badge g gr don t e := by
  intro s σ hX d q xd hk hd hkd hdon ht xt hkt hnb hns hft hV
  subst hdon
  obtain ⟨hR, hSR⟩ := hX
  have hback := hback_of hV hkd
  have hXs := IpcSchedHyps.stepsG (A := A) hH hBf hBm hP
  have hSB := IpcRel.toSRN hR hSR
  have hEP := hR.toE.at_ep he hk
  obtain ⟨-, xs, -, hq, hQ, hQO⟩ := hEP
  obtain ⟨xt0, hkt0, hTRt⟩ := hR.tcb t ht
  rw [hkt] at hkt0; cases hkt0
  have hdx : d ∈ xs := by
    have : d.bv ∈ xs.map UScalar.bv := by rw [← hq]; simp
    obtain ⟨z, hz, ez⟩ := List.mem_map.1 this
    rw [← eq_of_bv ez]; exact hz
  have htd : t ≠ d := by
    rintro rfl
    exact hnb.1 (hTRt.st.symm.trans (hQO t hdx).1)
  have cv : ∀ {cl : Bool} (r : S × A), (r.2 = a ∧ ¬ (Fl4Spec.sendIpc (Z := Unit) blk cl badge.bv g gr true t.bv
      e.bv σ).2 ∧ ∃ σ', ((), σ') ∈ (Fl4Spec.sendIpc (Z := Unit) blk cl badge.bv g gr true t.bv e.bv σ).1 ∧
      EpStateRel T E R B (L.mem r.1) σ' ∧
      SRN st N T (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c))) r.1 σ') →
      r.2 = a ∧ ∃ z ∈ (Fl4Spec.sendIpc (Z := Unit) blk cl badge.bv g gr true t.bv e.bv σ).1,
        IRel st th cr N T C E R B c r.1 z.2 :=
    fun _ ⟨h1, _, σ', h2, h3, h4⟩ => ⟨h1, ((), σ'), h2, IpcRel.ofSRN h3 h4⟩
  have hD := donNC_irel (st := st) (ar := ar) (th := th) (cr := cr) (N := N) (E := E) (R := R) (B := B) (c := c)
    hP a ht hd htd (xt := xt) (fun s' σ' hX' => hDN t d s' σ' hX' ht hd)
  cases call
  · cases hrb : ipcBufOf true xd with
    | none =>
      exact WP.spec_mono (send_ipc_recvD_gen hXs.toEpSteps (hTl.tail hP) hP.e s a σ hR.toE hSB ht hkt hnb hft he hk
        hkd hrb badge g gr (Or.inl trivial) hback hD blk) cv
    | some rp =>
      exact WP.spec_mono (send_ipc_recv_bufD_gen hXs (hTl.tail hP) hP.e s a σ hR.toE hSB ht hkt hnb hft he hk
        hkd hrb badge g gr (Or.inl trivial) hback hD blk) cv
  · have hXf := fun s1 σ1 => xferX_top (st := st) (xt := xd) hH hBf hBm hP ht hd htd
      (fun b h => by rw [hft] at h; cases h) a e g s1 σ1 badge
    by_cases hgg : g = true ∨ gr = true
    · by_cases hrp : ∀ e' rep dd, xd.tcbState = .blockedOnReceive e' rep dd → rep ≠ none
      · exact hPush s σ ⟨hR, hSR⟩ d q xd hk hkd hgg hrp
      · refine WP.spec_mono (send_ipc_call_inactiveX_gen (don := true) hXs.toEpSteps (hTl.tail hP) hP.e s a σ
          hR.toE hSB ht hkt hnb hns he hk hkd badge g gr hXf hback (Or.inr ?_) blk) cv
        intro e' rep dd hs
        by_contra hn
        refine hrp fun e'' rep' dd' hs' => ?_
        rw [hs] at hs'; cases hs'; exact hn
    · refine WP.spec_mono (send_ipc_call_inactiveX_gen (don := true) hXs.toEpSteps (hTl.tail hP) hP.e s a σ
        hR.toE hSB ht hkt hnb hns he hk hkd badge g gr hXf hback (Or.inl ?_) blk) cv
      cases g <;> cases gr <;> simp_all

end Rest

end

end Fl4Proofs.P3.Ipc

namespace Fl4Proofs.P3
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`IpcVsFrame` for an endpoint cap with the send right**, the donating
sends by `sendRest_of`. Named at `Z`: `IpcZ`, `SchedValid` and `QSorted` on
`IRel`, the endpoint in `Z.E`, `DonNCOK` and `SendPushRest`; the arch
relation by `ARKeep`. -/
theorem ipcVsFrame_endpointD {AR : A → Fl4Spec.Cr3 → Prop} {s : S} {a : A} {σ σ1 : Fl4Spec.State Unit}
    {ct : U64} (hcur : σ.curThread = ct.bv) {xt : Fl4Spec.Tcb} (hkt : σ.kheap ct.bv = some (.tcb xt))
    (hrun : tsCode xt.tcbState < 3) (hft : xt.tcbFault = none)
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (blk call don : Bool) (p b : U64) (rv g gr : Bool)
    (hZ : ∀ Z : XSets, XTopAt (L := L) AR Z s a σ → IpcZ (L := L) arI σ.archState.x64CurrentCr3 s ct Z ∧
      (∀ s' σ', IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ' → Sched.SchedValid σ') ∧
      (∀ s' σ', IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ' → QSorted st Z.T Z.E s') ∧
      p ∈ Z.E ∧
      (∀ (t d : U64) s' σ', IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ' → t ∈ Z.T →
        d ∈ Z.T → DonNCOK st Z.N Z.C s' σ' t d) ∧
      (∀ s' σ', IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ' →
        SendPushRest st arI (IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c) s' a σ' blk b g gr
          ct p))
    (hS : P0.StoreTotal st) (hA : P0.ArchTotal arI) (hK : ARKeep arI AR) :
    IpcVsFrame (L := L) arI AR s a σ σ1 ct blk call don (.Endpoint p b true rv g gr) :=
  ipcVsFrame_endpoint arI hcur hkt hrun hft hst blk call don p b rv g gr (fun Z hX =>
    let ⟨hz, hSV, hso, hp, hDN, hPush⟩ := hZ Z hX
    ⟨hz, hSV, hso, hp, sendRest_of hz.H hz.Bf hz.Bm hz.Tl hz.P hDN hp a blk call b g gr don ct hPush⟩) hS hA hK

end

end Fl4Proofs.P3
