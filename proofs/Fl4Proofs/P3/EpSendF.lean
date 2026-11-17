/-
P3 (DESIGN.md §9), endpoints: **a faulted sender's `send_ipc` to a waiting
receiver** (`call = false`, a fault set: the branch l4v takes on
`call ∨ fault ≠ none`), over an abstract transfer (`hXf`):
`send_ipc_callF_gen`, `send_ipc_call_inactiveF_gen`, the counterparts of
EpSendX's call lemmas (FL4 reads the fault word where the call flag is
false).
-/
import Fl4Proofs.P3.EpSendX
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

theorem sendIpc_callF_eq {σ : State Unit} {t e d : ObjRef} {q : List ObjRef}
    (hk : σ.kheap e = some (.endpoint (.recvEP (d :: q)))) {xd : Tcb} (hkd : σ.kheap d = some (.tcb xd))
    (hde : d ≠ e) {e' r : ObjRef} {dd : ReceiverPayload}
    (hst : xd.tcbState = .blockedOnReceive e' (some r) dd) (blk : Bool) (badge : Badge) (g gr : Bool)
    (hg : g = true ∨ gr = true) {σ2 σ3 σ4 : State Unit}
    (hT : doIpcTransfer (Z := Unit) t (some e) badge g d (updK σ e (.endpoint (epDeq (.recvEP (d :: q)) d))) =
      ({((), σ2)}, False))
    (hU : NonDet.maybeM (replyUnlinkTcb (Z := Unit) d) (some r) σ2 = ({((), σ3)}, False))
    {xt3 x3 : Tcb} (hkt3 : σ3.kheap t = some (.tcb xt3)) (hkd3 : σ3.kheap d = some (.tcb x3))
    (hPush : replyPush (Z := Unit) t d r false σ3 = ({((), σ4)}, False)) {x4 : Tcb}
    (hkd4 : σ4.kheap d = some (.tcb x4)) (hf3 : xt3.tcbFault ≠ none) :
    sendIpc (Z := Unit) blk false badge g gr false t e σ =
      specWakeTailE d (stsAct (updK σ4 d (.tcb { x4 with tcbState := .running })) d) := by
  have hkd1 : (updK σ e (.endpoint (epDeq (.recvEP (d :: q)) d))).kheap d = some (.tcb xd) := by
    simp [hde, hkd]
  unfold sendIpc
  rw [nd_bind_one (getEndpoint_eq hk)]
  cases blk <;> dsimp only <;>
  · rw [nd_bind_one (tcbEpDequeue_eq hk (by simp [Endpoint.epQueue])), nd_bind_one (getThreadState_eq hkd1), hst]
    dsimp only
    rw [nd_pure_bind', nd_bind_one hT, nd_bind_one hU, nd_bind_one (getTcbObjRef_eq _ hkd3),
      nd_bind_one (threadGet_eq _ hkt3)]
    have hg' : (g = true ∨ gr = true) ∧ (some r : Option ObjRef) ≠ none := ⟨hg, by simp⟩
    have hc : (false = true ∨ xt3.tcbFault ≠ none) := Or.inr hf3
    simp only [hc, ↓reduceIte, hg', the]
    rw [if_pos ⟨trivial, by simp⟩]
    rw [nd_bind_one hPush, nd_bind_one (setThreadState_eq _ hkd4)]
    rfl

theorem sendIpc_callInactiveF_eq {σ : State Unit} {t e d : ObjRef} {q : List ObjRef}
    (hk : σ.kheap e = some (.endpoint (.recvEP (d :: q)))) {xd : Tcb} (hkd : σ.kheap d = some (.tcb xd))
    (hde : d ≠ e) (htd : t ≠ d) {e' : ObjRef} {rep : Option ObjRef} {dd : ReceiverPayload}
    (hst : xd.tcbState = .blockedOnReceive e' rep dd) (blk : Bool) (badge : Badge) (g gr : Bool)
    (hcond : ¬ ((g = true ∨ gr = true) ∧ rep ≠ none)) {σ2 σ3 : State Unit}
    (hT : doIpcTransfer (Z := Unit) t (some e) badge g d (updK σ e (.endpoint (epDeq (.recvEP (d :: q)) d))) =
      ({((), σ2)}, False))
    (hU : NonDet.maybeM (replyUnlinkTcb (Z := Unit) d) rep σ2 = ({((), σ3)}, False))
    {xt3 x3 : Tcb} (hkt3 : σ3.kheap t = some (.tcb xt3)) (hkd3 : σ3.kheap d = some (.tcb x3)) (hf3 : xt3.tcbFault ≠ none) :
    sendIpc (Z := Unit) blk false badge g gr false t e σ =
      specWakeTailE d (stsAct (updK (stsAct (updK σ3 t (.tcb { xt3 with tcbState := .inactive })) t) d
        (.tcb { x3 with tcbState := .running })) d) := by
  have hkd1 : (updK σ e (.endpoint (epDeq (.recvEP (d :: q)) d))).kheap d = some (.tcb xd) := by
    simp [hde, hkd]
  have hkd3' : (stsAct (updK σ3 t (.tcb { xt3 with tcbState := .inactive })) t).kheap d = some (.tcb x3) := by
    rw [stsAct_kheap]; simp [Ne.symm htd, hkd3]
  unfold sendIpc
  rw [nd_bind_one (getEndpoint_eq hk)]
  cases blk <;> dsimp only <;>
  · rw [nd_bind_one (tcbEpDequeue_eq hk (by simp [Endpoint.epQueue])), nd_bind_one (getThreadState_eq hkd1), hst]
    dsimp only
    rw [nd_pure_bind', nd_bind_one hT, nd_bind_one hU, nd_bind_one (getTcbObjRef_eq _ hkd3),
      nd_bind_one (threadGet_eq _ hkt3)]
    have hc : (false = true ∨ xt3.tcbFault ≠ none) := Or.inr hf3
    simp only [hc, ↓reduceIte]
    rw [if_neg hcond, nd_bind_one (setThreadState_eq _ hkt3), nd_bind_one (setThreadState_eq _ hkd3')]
    rfl

end Spec

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st] {T E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {SR : S → Fl4Spec.State Unit → Prop}

theorem send_ipc_callF_gen {NS : Fl4Spec.ThreadState → Prop} {GC : Prop} (hX : EpSteps st A ar T E R B SR NS GC) (hTl : EpTailHyps st A T E R B SR)
    (hP : EPlaced T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ)
    (hSR : SR s σ) {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) (hns : NS xt.tcbState) (hft : xt.tcbFault ≠ none)
    {e d : U64} (he : e ∈ E) {q : List Fl4Spec.ObjRef} (hk : σ.kheap e.bv = some (.endpoint (.recvEP (d.bv :: q))))
    {xd : Fl4Spec.Tcb} (hkd : σ.kheap d.bv = some (.tcb xd))
    (badge : U64) (g gr : Bool)
    (hXf : ∀ (s1 : S) (σ1 : Fl4Spec.State Unit), EpStateRel T E R B (L.mem s1) σ1 → SR s1 σ1 →
      σ1.kheap t.bv = some (.tcb xt) → σ1.kheap d.bv = some (.tcb xd) →
      ipc.do_ipc_transfer st ar s1 a t e badge g d ⦃ s' => XferPost (L := L) T E R B SR s1 σ1 t d e badge g xd s' ⦄)
    (hback : ∀ e' r dd xr, xd.tcbState = .blockedOnReceive e' (some r) dd → σ.kheap r = some (.reply xr) →
      xr.replyTcb = some d.bv)
    (hg : g = true ∨ gr = true)
    (hrp0 : ∀ e' rep dd, xd.tcbState = .blockedOnReceive e' rep dd → rep ≠ none)
    (hTO : SVK.TailOK σ) (blk : Bool) :
    endpoint.send_ipc st ar s a blk false badge g gr false t e ⦃ r => r.2 = a ∧
      ¬ (Fl4Spec.sendIpc (Z := Unit) blk false badge.bv g gr false t.bv e.bv σ).2 ∧
      ∃ σ', ((), σ') ∈ (Fl4Spec.sendIpc (Z := Unit) blk false badge.bv g gr false t.bv e.bv σ).1 ∧
        EpStateRel T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ := by
  have hx := hR.at_ep he hk
  have hxt := hR.at_tcb ht hkt
  obtain ⟨hst2, xs, hxs0, hq, hQ, hB⟩ := hx
  obtain ⟨d', xs', rfl⟩ := List.exists_cons_of_ne_nil hxs0
  simp only [List.map_cons, List.cons.injEq] at hq
  obtain ⟨hd', hq'⟩ := hq
  have hdd : d' = d := eq_of_bv hd'.symm
  subst hdd
  have hdT : d' ∈ T := hQ.mem d' (by simp)
  have hda := hP.tcb d' hdT
  have hxd := hR.at_tcb hdT hkd
  have hd3 : (L.mem s (tStA d')).val = 3 := (hB d' (by simp)).1
  have hdb : L.mem s (tBlockA d') = e := (hB d' (by simp)).2
  -- the receiver's state
  obtain ⟨e', rep, dd, hstd⟩ := tsCode_three (hxd.st.symm.trans hd3)
  have he' : e' = e.bv := by
    have := hxd.blk e' (by rw [hstd]; rfl); rw [hdb] at this; exact this.symm
  subst he'
  obtain ⟨hrep, hrepR⟩ := hxd.recv _ _ _ hstd
  have htd : t ≠ d' := by
    intro h; subst h; exact hnb.1 (hxt.st.symm.trans hd3)
  have hde : d'.bv ≠ e.bv := kheap_ne hkd hk (fun _ h1 h2 => by subst h1; cases h2)
  have hte : t.bv ≠ e.bv := kheap_ne hkt hk (fun _ h1 h2 => by subst h1; cases h2)
  -- FL4
  unfold endpoint.send_ipc
  step as ⟨st0, hst0⟩
  rw [hst0, epState_eq, hst2]
  rw [if_neg (by rw [ep_state_vals.1]; decide), if_neg (by rw [ep_state_vals.2.1]; decide)]
  step as ⟨q0, hq0⟩
  have hhead : q0.head = d' := by rw [hq0, epQ_eq]; exact hQ.head
  rw [hhead]
  -- the dequeue
  refine WP.spec_bind (hX.deq hP s σ hR hSR he hk (d := d') (by simp [Fl4Spec.Endpoint.epQueue])) ?_
  rintro s1 ⟨e1, hR1, hS1, hA1⟩
  set σ1 := updK σ e.bv (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv))
  have hkt1 : σ1.kheap t.bv = some (.tcb xt) := by simp [σ1, hte, hkt]
  have hkd1 : σ1.kheap d'.bv = some (.tcb xd) := by simp [σ1, hde, hkd]
  -- the transfer
  refine WP.spec_bind (hXf s1 σ1 hR1 hS1 hkt1 hkd1) ?_
  rintro s2 ⟨σ2, e2, hR2, hS2, hA2, hk2o, x2, hkd2, hx2st⟩
  have htd' : t.bv ≠ d'.bv := bv_inj htd
  have hkt2 : σ2.kheap t.bv = some (.tcb xt) := hk2o.fwd htd' hkt1 (fun _ _ e => by cases e)
  have hst2' : x2.tcbState = .blockedOnReceive e.bv rep dd := by rw [hx2st, hstd]
  -- `d'` is in no endpoint queue from `σ1` on
  have hk1e : σ1.kheap e.bv = some (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) := by simp [σ1]
  have hdb1 : L.mem s1 (tBlockA d') = e := by
    rw [hA1 _ (a_blk hda).1 ⟨d', hdT, (a_blk hda).2⟩, hdb]
  have hq1 := dequeued_not_queued hR1 he hdb1 hk1e (epDeq_not_mem _)
  have hq2 : ∀ e'' ∈ E, ∀ z, σ2.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue := by
    intro e'' he'' z hz
    have hne : d'.bv ≠ e''.bv := by intro h; rw [← h, hkd2] at hz; cases hz
    exact hq1 e'' he'' z (hk2o.bwd (Ne.symm hne) hz (fun _ _ e => by cases e))
  -- the reply word
  have hrw : L.mem s2 (tReplyA d') = L.mem s (tReplyA d') := by
    rw [hA2 _ (a_reply hda).1 ⟨⟨d', hdT, (a_reply hda).2⟩, ?_, ?_⟩, hA1 _ (a_reply hda).1 ⟨d', hdT, (a_reply hda).2⟩]
    · rintro ⟨r', hr'⟩
      rw [val_reply hda, regA_val hda (regIdx_lt r')] at hr'; have := regIdx_lt r'; omega
    · rintro ⟨wp, hw, he'⟩
      have := hP.bt wp hw d' hdT
      have := congrArg UScalar.val he'
      rw [val_reply hda] at this; omega
  step as ⟨i, hi⟩
  rw [hi, hrw]
  have hg' := hg
  cases hrp : rep with
  | none => exact absurd hrp (hrp0 _ _ _ hstd)
  | some r =>
  rw [hrp] at hrep hrepR hst2' hstd
  obtain ⟨hw0, hwr⟩ := optRef_some hrep
  have hwR := hrepR (by simp)
  have hne0 : (L.mem s (tReplyA d') != 0#u64) = true := by simp [hw0]
  simp only [hne0, Bool.false_eq_true, ↓reduceIte]
  set w := L.mem s (tReplyA d') with hwdef
  subst hwr
  obtain ⟨xr, hkr, -⟩ := hR.reply w hwR
  have hwe : w.bv ≠ e.bv := kheap_ne hkr hk (fun _ h1 h2 => by subst h1; cases h2)
  have hwd : w.bv ≠ d'.bv := kheap_ne hkr hkd (fun _ h1 h2 => by subst h1; cases h2)
  have hwt : w.bv ≠ t.bv := kheap_ne hkr hkt (fun _ h1 h2 => by subst h1; cases h2)
  have hkr2 : σ2.kheap w.bv = some (.reply xr) := hk2o.fwd hwd (by simp [σ1, hwe, hkr]) (fun _ _ e => by cases e)
  have hb' := hback e.bv w.bv dd xr hstd hkr
  refine WP.spec_bind (hX.unlink hP s2 σ2 hR2 hS2 hdT hkd2 hst2' hwR hkr2 hb' hq2) ?_
  rintro s3 ⟨e3, hR3, hS3⟩
  set x3 : Fl4Spec.Tcb := { x2 with tcbState := .inactive }
  set σ3 := stsAct (updK (updK σ2 w.bv (.reply { xr with replyTcb := none })) d'.bv (.tcb x3)) d'.bv
  have hkt3 : σ3.kheap t.bv = some (.tcb xt) := by rw [stsAct_kheap]; simp [htd', hwt.symm, hkt2]
  have hkd3 : σ3.kheap d'.bv = some (.tcb x3) := by rw [stsAct_kheap]; simp
  have hkr3 : σ3.kheap w.bv = some (.reply { xr with replyTcb := none }) := by
    rw [stsAct_kheap]; simp [hwd]
  have hq3 : ∀ e'' ∈ E, ∀ z, σ3.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue := by
    intro e'' he'' z hz
    rw [stsAct_kheap] at hz
    have hne : d'.bv ≠ e''.bv := by intro h; rw [← h] at hz; simp at hz
    have hne' : w.bv ≠ e''.bv := by intro h; rw [← h] at hz; simp [hwd] at hz
    exact hq2 e'' he'' z (by simpa [Ne.symm hne, Ne.symm hne'] using hz)
  have hqt3 := not_queued hR3 ht hkt3 hnb
  have hfw : (L.mem s3 (tFaultA t) != fl4_abi.consts.fault.NullFault) = true := by
    have h := (hR3.at_tcb ht hkt3).fault0
    unfold fl4_abi.consts.fault.NullFault
    simpa using fun e => hft (h.1 e)
  step with Fl4Proofs.P3.Endp.obj.Tcb.fault_type.spec as ⟨ft, hftv⟩
  rw [hftv]
  simp only [hfw, ↓reduceIte]
  have hpush := hX.push hP s3 a σ3 hR3 hS3 ht hkt3 hkd3 hqt3 hns hwR hkr3
  rcases hg with hg | hg
  · subst hg
    simp only [↓reduceIte]
    refine WP.spec_bind hpush ?_
    rintro ⟨s4, a4⟩ ⟨ha4, hP4, hR4, hS4⟩
    simp only at ha4
    subst ha4
    set σ4 := stsAct (updK (updK σ3 w.bv (.reply { ({ xr with replyTcb := none } : Fl4Spec.Reply) with
      replyTcb := some t.bv })) t.bv
      (.tcb { xt with tcbState := .blockedOnReply w.bv })) t.bv
    have h43 : ∀ p, p ≠ t.bv → p ≠ w.bv → σ4.kheap p = σ3.kheap p := by
      intro p h1 h2
      rw [stsAct_kheap, updK_kheap, Function.update_of_ne h1, updK_kheap, Function.update_of_ne h2]
    have hkd4 : σ4.kheap d'.bv = some (.tcb x3) := (h43 _ htd'.symm hwd.symm).trans hkd3
    have hq4 : ∀ e'' ∈ E, ∀ z, σ4.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue := by
      intro e'' he'' z hz
      have hne : e''.bv ≠ t.bv := by intro h; rw [h] at hz; rw [stsAct_kheap] at hz; simp at hz
      have hne' : e''.bv ≠ w.bv := by
        intro h; rw [h, stsAct_kheap] at hz; simp [hwt] at hz
      exact hq3 e'' he'' z ((h43 _ hne hne').symm.trans hz)
    refine WP.spec_bind (hX.sts hP s4 σ4 hR4 hS4 hdT hkd4 hq4 (hX.ns_ep _ (by simp [x3, tsCode])) .running (by simp [tsCode])
      sched.TS_RUNNING (by unfold sched.TS_RUNNING; rfl)) ?_
    rintro s5 ⟨hR5, hS5⟩
    have hspec := sendIpc_callF_eq hk hkd hde (by rw [hstd]) blk badge.bv _ _ hg' e2 e3 hkt3 hkd3 hP4 hkd4 hft
      (t := t.bv)
    rw [hspec]
    refine WP.spec_mono (hTl.wakeTail s5 _ _ d' hR5 hS5 hdT
      (wake_call hTO hk hkd (by rw [hstd]; rfl) e2
        (by first | exact SVK.SVM.of_eq (SVK.sv_replyUnlinkTcb _ _) e3 | exact SVK.SVM.of_eq (SVK.sv_maybeM (fun r => SVK.sv_replyUnlinkTcb _ r) _) e3)
        hkt3 hkd3 hP4 hkd4)) ?_
    rintro ⟨s7, a7⟩ ⟨ha7, hnf, σ', hm, hf, hv, hS'⟩
    exact ⟨ha7, hnf, σ', hm, hR5.frame hP hf hv, hS'⟩
  · cases g with
    | true =>
      simp only [↓reduceIte]
      refine WP.spec_bind hpush ?_
      rintro ⟨s4, a4⟩ ⟨ha4, hP4, hR4, hS4⟩
      simp only at ha4
      subst ha4
      set σ4 := stsAct (updK (updK σ3 w.bv (.reply { ({ xr with replyTcb := none } : Fl4Spec.Reply) with
      replyTcb := some t.bv })) t.bv
        (.tcb { xt with tcbState := .blockedOnReply w.bv })) t.bv
      have h43 : ∀ p, p ≠ t.bv → p ≠ w.bv → σ4.kheap p = σ3.kheap p := by
        intro p h1 h2
        rw [stsAct_kheap, updK_kheap, Function.update_of_ne h1, updK_kheap, Function.update_of_ne h2]
      have hkd4 : σ4.kheap d'.bv = some (.tcb x3) := (h43 _ htd'.symm hwd.symm).trans hkd3
      have hq4 : ∀ e'' ∈ E, ∀ z, σ4.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue := by
        intro e'' he'' z hz
        have hne : e''.bv ≠ t.bv := by intro h; rw [h] at hz; rw [stsAct_kheap] at hz; simp at hz
        have hne' : e''.bv ≠ w.bv := by
          intro h; rw [h, stsAct_kheap] at hz; simp [hwt] at hz
        exact hq3 e'' he'' z ((h43 _ hne hne').symm.trans hz)
      refine WP.spec_bind (hX.sts hP s4 σ4 hR4 hS4 hdT hkd4 hq4 (hX.ns_ep _ (by simp [x3, tsCode])) .running (by simp [tsCode])
        sched.TS_RUNNING (by unfold sched.TS_RUNNING; rfl)) ?_
      rintro s5 ⟨hR5, hS5⟩
      have hspec := sendIpc_callF_eq hk hkd hde (by rw [hstd]) blk badge.bv _ _ hg' e2 e3 hkt3 hkd3 hP4 hkd4 hft
        (t := t.bv)
      rw [hspec]
      refine WP.spec_mono (hTl.wakeTail s5 _ _ d' hR5 hS5 hdT
      (wake_call hTO hk hkd (by rw [hstd]; rfl) e2
        (by first | exact SVK.SVM.of_eq (SVK.sv_replyUnlinkTcb _ _) e3 | exact SVK.SVM.of_eq (SVK.sv_maybeM (fun r => SVK.sv_replyUnlinkTcb _ r) _) e3)
        hkt3 hkd3 hP4 hkd4)) ?_
      rintro ⟨s7, a7⟩ ⟨ha7, hnf, σ', hm, hf, hv, hS'⟩
      exact ⟨ha7, hnf, σ', hm, hR5.frame hP hf hv, hS'⟩

    | false =>
      subst hg
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine WP.spec_bind hpush ?_
      rintro ⟨s4, a4⟩ ⟨ha4, hP4, hR4, hS4⟩
      simp only at ha4
      subst ha4
      set σ4 := stsAct (updK (updK σ3 w.bv (.reply { ({ xr with replyTcb := none } : Fl4Spec.Reply) with
      replyTcb := some t.bv })) t.bv
        (.tcb { xt with tcbState := .blockedOnReply w.bv })) t.bv
      have h43 : ∀ p, p ≠ t.bv → p ≠ w.bv → σ4.kheap p = σ3.kheap p := by
        intro p h1 h2
        rw [stsAct_kheap, updK_kheap, Function.update_of_ne h1, updK_kheap, Function.update_of_ne h2]
      have hkd4 : σ4.kheap d'.bv = some (.tcb x3) := (h43 _ htd'.symm hwd.symm).trans hkd3
      have hq4 : ∀ e'' ∈ E, ∀ z, σ4.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue := by
        intro e'' he'' z hz
        have hne : e''.bv ≠ t.bv := by intro h; rw [h] at hz; rw [stsAct_kheap] at hz; simp at hz
        have hne' : e''.bv ≠ w.bv := by
          intro h; rw [h, stsAct_kheap] at hz; simp [hwt] at hz
        exact hq3 e'' he'' z ((h43 _ hne hne').symm.trans hz)
      refine WP.spec_bind (hX.sts hP s4 σ4 hR4 hS4 hdT hkd4 hq4 (hX.ns_ep _ (by simp [x3, tsCode])) .running (by simp [tsCode])
        sched.TS_RUNNING (by unfold sched.TS_RUNNING; rfl)) ?_
      rintro s5 ⟨hR5, hS5⟩
      have hspec := sendIpc_callF_eq hk hkd hde (by rw [hstd]) blk badge.bv _ _ hg' e2 e3 hkt3 hkd3 hP4 hkd4 hft
        (t := t.bv)
      rw [hspec]
      refine WP.spec_mono (hTl.wakeTail s5 _ _ d' hR5 hS5 hdT
      (wake_call hTO hk hkd (by rw [hstd]; rfl) e2
        (by first | exact SVK.SVM.of_eq (SVK.sv_replyUnlinkTcb _ _) e3 | exact SVK.SVM.of_eq (SVK.sv_maybeM (fun r => SVK.sv_replyUnlinkTcb _ r) _) e3)
        hkt3 hkd3 hP4 hkd4)) ?_
      rintro ⟨s7, a7⟩ ⟨ha7, hnf, σ', hm, hf, hv, hS'⟩
      exact ⟨ha7, hnf, σ', hm, hR5.frame hP hf hv, hS'⟩

theorem send_ipc_call_inactiveF_gen {NS : Fl4Spec.ThreadState → Prop} {GC : Prop} (hX : EpSteps st A ar T E R B SR NS GC) (hTl : EpTailHyps st A T E R B SR)
    (hP : EPlaced T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ)
    (hSR : SR s σ) {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) (hns : NS xt.tcbState) (hft : xt.tcbFault ≠ none)
    {e d : U64} (he : e ∈ E) {q : List Fl4Spec.ObjRef} (hk : σ.kheap e.bv = some (.endpoint (.recvEP (d.bv :: q))))
    {xd : Fl4Spec.Tcb} (hkd : σ.kheap d.bv = some (.tcb xd))
    (badge : U64) (g gr : Bool)
    (hXf : ∀ (s1 : S) (σ1 : Fl4Spec.State Unit), EpStateRel T E R B (L.mem s1) σ1 → SR s1 σ1 →
      σ1.kheap t.bv = some (.tcb xt) → σ1.kheap d.bv = some (.tcb xd) →
      ipc.do_ipc_transfer st ar s1 a t e badge g d ⦃ s' => XferPost (L := L) T E R B SR s1 σ1 t d e badge g xd s' ⦄)
    (hback : ∀ e' r dd xr, xd.tcbState = .blockedOnReceive e' (some r) dd → σ.kheap r = some (.reply xr) →
      xr.replyTcb = some d.bv)
    (hno : (g = false ∧ gr = false) ∨ ∀ e' rep dd, xd.tcbState = .blockedOnReceive e' rep dd → rep = none)
    (hTO : SVK.TailOK σ) (blk : Bool) :
    endpoint.send_ipc st ar s a blk false badge g gr false t e ⦃ r => r.2 = a ∧
      ¬ (Fl4Spec.sendIpc (Z := Unit) blk false badge.bv g gr false t.bv e.bv σ).2 ∧
      ∃ σ', ((), σ') ∈ (Fl4Spec.sendIpc (Z := Unit) blk false badge.bv g gr false t.bv e.bv σ).1 ∧
        EpStateRel T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ := by
  have hx := hR.at_ep he hk
  have hxt := hR.at_tcb ht hkt
  obtain ⟨hst2, xs, hxs0, hq, hQ, hB⟩ := hx
  obtain ⟨d', xs', rfl⟩ := List.exists_cons_of_ne_nil hxs0
  simp only [List.map_cons, List.cons.injEq] at hq
  obtain ⟨hd', hq'⟩ := hq
  have hdd : d' = d := eq_of_bv hd'.symm
  subst hdd
  have hdT : d' ∈ T := hQ.mem d' (by simp)
  have hda := hP.tcb d' hdT
  have hxd := hR.at_tcb hdT hkd
  have hd3 : (L.mem s (tStA d')).val = 3 := (hB d' (by simp)).1
  have hdb : L.mem s (tBlockA d') = e := (hB d' (by simp)).2
  -- the receiver's state
  obtain ⟨e', rep, dd, hstd⟩ := tsCode_three (hxd.st.symm.trans hd3)
  have he' : e' = e.bv := by
    have := hxd.blk e' (by rw [hstd]; rfl); rw [hdb] at this; exact this.symm
  subst he'
  obtain ⟨hrep, hrepR⟩ := hxd.recv _ _ _ hstd
  have htd : t ≠ d' := by
    intro h; subst h; exact hnb.1 (hxt.st.symm.trans hd3)
  have hde : d'.bv ≠ e.bv := kheap_ne hkd hk (fun _ h1 h2 => by subst h1; cases h2)
  have hte : t.bv ≠ e.bv := kheap_ne hkt hk (fun _ h1 h2 => by subst h1; cases h2)
  -- FL4
  unfold endpoint.send_ipc
  step as ⟨st0, hst0⟩
  rw [hst0, epState_eq, hst2]
  rw [if_neg (by rw [ep_state_vals.1]; decide), if_neg (by rw [ep_state_vals.2.1]; decide)]
  step as ⟨q0, hq0⟩
  have hhead : q0.head = d' := by rw [hq0, epQ_eq]; exact hQ.head
  rw [hhead]
  -- the dequeue
  refine WP.spec_bind (hX.deq hP s σ hR hSR he hk (d := d') (by simp [Fl4Spec.Endpoint.epQueue])) ?_
  rintro s1 ⟨e1, hR1, hS1, hA1⟩
  set σ1 := updK σ e.bv (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv))
  have hkt1 : σ1.kheap t.bv = some (.tcb xt) := by simp [σ1, hte, hkt]
  have hkd1 : σ1.kheap d'.bv = some (.tcb xd) := by simp [σ1, hde, hkd]
  -- the transfer
  refine WP.spec_bind (hXf s1 σ1 hR1 hS1 hkt1 hkd1) ?_
  rintro s2 ⟨σ2, e2, hR2, hS2, hA2, hk2o, x2, hkd2, hx2st⟩
  have htd' : t.bv ≠ d'.bv := bv_inj htd
  have hkt2 : σ2.kheap t.bv = some (.tcb xt) := hk2o.fwd htd' hkt1 (fun _ _ e => by cases e)
  have hst2' : x2.tcbState = .blockedOnReceive e.bv rep dd := by rw [hx2st, hstd]
  -- `d'` is in no endpoint queue from `σ1` on
  have hk1e : σ1.kheap e.bv = some (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) := by simp [σ1]
  have hdb1 : L.mem s1 (tBlockA d') = e := by
    rw [hA1 _ (a_blk hda).1 ⟨d', hdT, (a_blk hda).2⟩, hdb]
  have hq1 := dequeued_not_queued hR1 he hdb1 hk1e (epDeq_not_mem _)
  have hq2 : ∀ e'' ∈ E, ∀ z, σ2.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue := by
    intro e'' he'' z hz
    have hne : d'.bv ≠ e''.bv := by intro h; rw [← h, hkd2] at hz; cases hz
    exact hq1 e'' he'' z (hk2o.bwd (Ne.symm hne) hz (fun _ _ e => by cases e))
  -- the reply word
  have hrw : L.mem s2 (tReplyA d') = L.mem s (tReplyA d') := by
    rw [hA2 _ (a_reply hda).1 ⟨⟨d', hdT, (a_reply hda).2⟩, ?_, ?_⟩, hA1 _ (a_reply hda).1 ⟨d', hdT, (a_reply hda).2⟩]
    · rintro ⟨r', hr'⟩
      rw [val_reply hda, regA_val hda (regIdx_lt r')] at hr'; have := regIdx_lt r'; omega
    · rintro ⟨wp, hw, he'⟩
      have := hP.bt wp hw d' hdT
      have := congrArg UScalar.val he'
      rw [val_reply hda] at this; omega
  step as ⟨i, hi⟩
  rw [hi, hrw]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hcond : ¬ ((g = true ∨ gr = true) ∧ rep ≠ none) := by
    rintro ⟨h1, h2⟩
    rcases hno with ⟨rfl, rfl⟩ | h
    · simp at h1
    · exact h2 (h _ _ _ hstd)
  refine WP.spec_bind (Pₘ := fun s3 => ∃ σ3 x3, EpStateRel T E R B (L.mem s3) σ3 ∧ SR s3 σ3 ∧
      Fl4Spec.NonDet.maybeM (Fl4Spec.replyUnlinkTcb (Z := Unit) d'.bv) rep σ2 = ({((), σ3)}, False) ∧
      σ3.kheap t.bv = some (.tcb xt) ∧ σ3.kheap d'.bv = some (.tcb x3) ∧ tsCode x3.tcbState ≠ 6 ∧
      (∀ e'' ∈ E, ∀ z, σ3.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue)) ?_ ?_
  · cases hrp : rep with
    | none =>
      rw [hrp] at hrep
      have h0 := optRef_none hrep
      simp only [h0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      exact ⟨σ2, _, hR2, hS2, rfl, hkt2, hkd2, by rw [hst2']; simp [tsCode], hq2⟩
    | some r =>
      rw [hrp] at hrep hrepR hst2'
      obtain ⟨hw0, hwr⟩ := optRef_some hrep
      have hwR := hrepR (by simp)
      have hne0 : (L.mem s (tReplyA d') != 0#u64) = true := by simp [hw0]
      simp only [hne0, ↓reduceIte]
      set w := L.mem s (tReplyA d') with hwdef
      subst hwr
      obtain ⟨xr, hkr, -⟩ := hR.reply w hwR
      have hwe : w.bv ≠ e.bv := kheap_ne hkr hk (fun _ h1 h2 => by subst h1; cases h2)
      have hwd : w.bv ≠ d'.bv := kheap_ne hkr hkd (fun _ h1 h2 => by subst h1; cases h2)
      have hwt : w.bv ≠ t.bv := kheap_ne hkr hkt (fun _ h1 h2 => by subst h1; cases h2)
      have hkr2 : σ2.kheap w.bv = some (.reply xr) := hk2o.fwd hwd (by simp [σ1, hwe, hkr]) (fun _ _ e => by cases e)
      have hb' := hback e.bv w.bv dd xr (by rw [hstd, hrp]) hkr
      refine WP.spec_mono (hX.unlink hP s2 σ2 hR2 hS2 hdT hkd2 hst2' hwR hkr2 hb' hq2) ?_
      rintro s3 ⟨e3, hR3, hS3⟩
      refine ⟨_, { x2 with tcbState := .inactive }, hR3, hS3, e3, ?_, ?_, ?_, ?_⟩
      · rw [stsAct_kheap]; simp [htd', hwt.symm, hkt2]
      · rw [stsAct_kheap]; simp
      · simp [tsCode]
      · intro e'' he'' z hz
        rw [stsAct_kheap] at hz
        have hne : d'.bv ≠ e''.bv := by intro h; rw [← h] at hz; simp at hz
        have hne' : w.bv ≠ e''.bv := by intro h; rw [← h] at hz; simp [hwd] at hz
        exact hq2 e'' he'' z (by simpa [Ne.symm hne, Ne.symm hne'] using hz)
  · rintro s3 ⟨σ3, x3, hR3, hS3, hU, hkt3, hkd3, hns3, hq3⟩
    have hfw : (L.mem s3 (tFaultA t) != fl4_abi.consts.fault.NullFault) = true := by
      have h := (hR3.at_tcb ht hkt3).fault0
      unfold fl4_abi.consts.fault.NullFault
      simpa using fun e => hft (h.1 e)
    step with Fl4Proofs.P3.Endp.obj.Tcb.fault_type.spec as ⟨ft, hftv⟩
    rw [hftv]
    simp only [hfw, ↓reduceIte]
    have hqt3 := not_queued hR3 ht hkt3 hnb
    rcases hno with ⟨rfl, rfl⟩ | hnone
    · simp only [Bool.false_eq_true, ↓reduceIte, ite_self]
      refine WP.spec_bind (Pₘ := fun x => x.2 = a ∧
        EpStateRel T E R B (L.mem x.1) (stsAct (updK σ3 t.bv (.tcb { xt with tcbState := .inactive })) t.bv) ∧
        SR x.1 (stsAct (updK σ3 t.bv (.tcb { xt with tcbState := .inactive })) t.bv)) ?_ ?_
      · refine WP.spec_bind (hX.sts hP s3 σ3 hR3 hS3 ht hkt3 hqt3 hns .inactive (by simp [tsCode])
          sched.TS_INACTIVE (by unfold sched.TS_INACTIVE; rfl)) ?_
        rintro s5 ⟨h1, h2⟩
        simp only [WP.spec_ok]
        exact ⟨trivial, h1, h2⟩
      rintro ⟨s4, a4⟩ ⟨ha4, hR4, hS4⟩
      simp only at ha4
      subst ha4
      set σ4 := stsAct (updK σ3 t.bv (.tcb { xt with tcbState := .inactive })) t.bv
      have hkd4 : σ4.kheap d'.bv = some (.tcb x3) := by rw [stsAct_kheap]; simp [Ne.symm htd', hkd3]
      have hq4 : ∀ e'' ∈ E, ∀ z, σ4.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue := by
        intro e'' he'' z hz
        have hne : e''.bv ≠ t.bv := by intro h; rw [h] at hz; rw [stsAct_kheap] at hz; simp at hz
        refine hq3 e'' he'' z ?_
        rw [← hz, stsAct_kheap, updK_kheap, Function.update_of_ne hne]
      refine WP.spec_bind (hX.sts hP s4 σ4 hR4 hS4 hdT hkd4 hq4 (hX.ns_ep _ hns3) .running (by simp [tsCode])
        sched.TS_RUNNING (by unfold sched.TS_RUNNING; rfl)) ?_
      rintro s5 ⟨hR5, hS5⟩
      have hspec := sendIpc_callInactiveF_eq hk hkd hde htd' hstd blk badge.bv _ _ hcond e2 hU hkt3 hkd3 hft (t := t.bv)
      rw [hspec]
      refine WP.spec_mono (hTl.wakeTail s5 _ _ d' hR5 hS5 hdT
      (wake_callInactive hTO hk hkd (by rw [hstd]; rfl) htd' e2 hU hkt3 hkd3)) ?_
      rintro ⟨s7, a7⟩ ⟨ha7, hnf, σ', hm, hf, hv, hS'⟩
      exact ⟨ha7, hnf, σ', hm, hR5.frame hP hf hv, hS'⟩

    · have h0 : L.mem s (tReplyA d') = 0#u64 := optRef_none (by rw [hrep]; exact hnone _ _ _ hstd)
      simp only [h0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      refine WP.spec_bind (Pₘ := fun x => x.2 = a ∧
        EpStateRel T E R B (L.mem x.1) (stsAct (updK σ3 t.bv (.tcb { xt with tcbState := .inactive })) t.bv) ∧
        SR x.1 (stsAct (updK σ3 t.bv (.tcb { xt with tcbState := .inactive })) t.bv)) ?_ ?_
      · refine WP.spec_bind (hX.sts hP s3 σ3 hR3 hS3 ht hkt3 hqt3 hns .inactive (by simp [tsCode])
          sched.TS_INACTIVE (by unfold sched.TS_INACTIVE; rfl)) ?_
        rintro s5 ⟨h1, h2⟩
        simp only [WP.spec_ok]
        exact ⟨trivial, h1, h2⟩
      rintro ⟨s4, a4⟩ ⟨ha4, hR4, hS4⟩
      simp only at ha4
      subst ha4
      set σ4 := stsAct (updK σ3 t.bv (.tcb { xt with tcbState := .inactive })) t.bv
      have hkd4 : σ4.kheap d'.bv = some (.tcb x3) := by rw [stsAct_kheap]; simp [Ne.symm htd', hkd3]
      have hq4 : ∀ e'' ∈ E, ∀ z, σ4.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue := by
        intro e'' he'' z hz
        have hne : e''.bv ≠ t.bv := by intro h; rw [h] at hz; rw [stsAct_kheap] at hz; simp at hz
        refine hq3 e'' he'' z ?_
        rw [← hz, stsAct_kheap, updK_kheap, Function.update_of_ne hne]
      refine WP.spec_bind (hX.sts hP s4 σ4 hR4 hS4 hdT hkd4 hq4 (hX.ns_ep _ hns3) .running (by simp [tsCode])
        sched.TS_RUNNING (by unfold sched.TS_RUNNING; rfl)) ?_
      rintro s5 ⟨hR5, hS5⟩
      have hspec := sendIpc_callInactiveF_eq hk hkd hde htd' hstd blk badge.bv _ _ hcond e2 hU hkt3 hkd3 hft (t := t.bv)
      rw [hspec]
      refine WP.spec_mono (hTl.wakeTail s5 _ _ d' hR5 hS5 hdT
      (wake_callInactive hTO hk hkd (by rw [hstd]; rfl) htd' e2 hU hkt3 hkd3)) ?_
      rintro ⟨s7, a7⟩ ⟨ha7, hnf, σ', hm, hf, hv, hS'⟩
      exact ⟨ha7, hnf, σ', hm, hR5.frame hP hf hv, hS'⟩

end

end

end Fl4Proofs.P3.Endp
