/-
P3 (line mmuAD, gen 42a2): **the donating fault send at `JAtZV3`** — P3/JAtZV3FaultRecv's [W] `ZvFaultPDHyp`
discharged (`zvFaultPDHyp_of`), and the VCPU-cap step with no fault premise left (`JAtZV3.vcpuHandleJ4`).

* **Copies over `JAtZB`** (generator `scratch/mmu32_jatzb_gen.py pushDonJ stsIJ`, widened as in P3/JAtZV3FaultRecvB,
  filtered to the declarations not yet over `JAtZB`): from P3/XTopJointRemove `JAtZB.rmW_of`, `rmX_tcb`, `rmW_keeps`,
  `rmW_scOut`, `rmW_irq`, `rmW_nv`, `rmW_ntd`, `rmW_utc`; from P3/XTopJointSendDon `scOwned_not_dead`; from
  P3/XTopJointPushDon `stackHead`; from
  P3/XTopJointFinScReply **`sc_frameS`** (its one `JAtZ.ext` use, the `ext` entry `J.ext.ss hSS hv`, dropped: the
  result is `JAtZB`) and `sc_kernW`; **`JAtZB.pushDonJ`** (P3/XTopJointPushDon; post adds FL4's `RmW` footprint and
  the spec frame `ScTKw (fun _ => False)`, both `have`s of its proof) and **`JAtZB.stsIJ`** (P3/XTopJointStsI; post
  adds the `TFoot` footprint, as gen 42a2's `JAtZB.stsCurJ`). Otherwise verbatim (bare `nodeW` written `Sched.nodeW`, the gen-24 trap). Heartbeats 4M (sources 1M–32M).
* **`JAtZB.rmW_nh`** (an `RmW` word is not the VCPU-list head word), **`zvk_tk`** (`ZvK` from `ScTKw (fun _ => False)`:
  `zv_tk` + `zv_tk_v`).
* **`JAtZV3.pushDonJ3`** (`ofBSK` with `RmW.oobj`, `rmW_nh`, `rmW_nv`, `zvk_tk`), **`JAtZV3.stsIJ3`** (`ofBSK` with
  the `TFoot` facts and `zvk_upd`: the new state has code < 3, not `runningVM`).
* **`JAtZV3.sendFaultPDJ3`**: P3/XTopJointFaultRecv's `JAtZ.sendFaultPDJ` over `J3.z2.zv.base`, the receive-buffer
  rebase by `JAtZV3.bufRebaseX3`, the push's wake lifted by `JAtZV3.ofCnW` (`zvk_dwfr`, `zvk_pushSt`), the donation by
  `JAtZV3.pushDonJ3`, the receiver `Running` by `JAtZV3.stsIJ3`, the tail by `JAtZV3.sendTailJ3`.
* **`zvFaultPDHyp_of`**: `ZvFaultPDHyp` from `P0.ArchTotal`. **`JAtZV3.vcpuHandleJ4`**: P3/JAtZV3FaultRecv's
  `JAtZV3.vcpuHandleJ3` without `ZvFaultPDHyp`.

Premise diff: [W] `ZvFaultPDHyp` (this gen) discharged; gen 41's [W] `ZvFaultHyp` is now a theorem
(`zvFaultHyp_of3` + `zvFaultPDHyp_of`) from [J] `ZvEntry` and [J] `ZvVfh`. No existing statement changed.

(mmuAD gen 42b17) Copies removed (the originals are now stated over `JAtZB` in place): P3/XTopJointPushDon
`stackHead`; P3/XTopJointRemove `rmW_irq`, `rmW_keeps`, `rmW_ntd`, `rmW_nv`, `rmW_of`, `rmW_scOut`, `rmW_utc`,
`rmX_tcb`; P3/XTopJointSendDon `scOwned_not_dead`.

(mmuAD gen 42b17, second pass) Copies removed (originals generalised in place): P3/XTopJointFinScReply `sc_kernW`.

(mmuAD gen 42b18) Removed (the originals are stated over `JAtZB` in place, the `JAtZ` names their corollaries with
`ext` rebuilt): P3/XTopJointFinScReply `sc_frameS`; P3/XTopJointStsI `stsIJ`; P3/XTopJointPushDon `pushDonJ`.
-/
import Fl4Proofs.P3.JAtZV3FaultRecv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

section
open Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Ipc

/-- **An `RmW` word is not the VCPU-list head word** (module docstring). -/
theorem JAtZB.rmW_nh (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {b : U64}
    (h : RmW (st := st) Z.T Z.N Z.C Z.R Z.c s σ b) : b ≠ P1.vHeadA st s := by
  rcases h with hf | ⟨r, hr, h1, h2⟩ | ⟨sc, hsc, x, n, hk, hso⟩
  · exact J.finW_nh hf
  · intro e
    subst e
    have hvh : (P1.vHeadA st s).val = (L.ksb s).val + 80 := vHead_val J.kern.ksbFit
    have d := J.kern.hks r _ (J.zH.2.2.1 r hr) (fun _ h => by cases h)
    simp only [P1.HKind.bits, Nat.reducePow] at d
    omega
  · intro e
    subst e
    have hvh : (P1.vHeadA st s).val = (L.ksb s).val + 80 := vHead_val J.kern.ksbFit
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    have hH := (hJ.sc sc x n (J.c0 sc hsc) hk).2
    have d := J.kern.hks sc _ hH (fun _ h => by cases h)
    simp only [P1.HKind.bits, Nat.reducePow] at d
    unfold Sched.ScObj at hso
    omega

end

end

/-- `ZvK` of an SC-code spec step (module docstring). -/
theorem zvk_tk {σ σ' : Fl4Spec.State Unit} (h : Sched.ScTKw (fun _ => False) σ σ') : ZvK σ σ' :=
  ⟨(zv_tk h).1, (zv_tk h).2.1, (zv_tk h).2.2, zv_tk_v h⟩

section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc
  Fl4Proofs.P3.Sched
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

set_option maxHeartbeats 4000000 in
/-- **The reply-push donation at `JAtZV3`** (module docstring). -/
theorem JAtZV3.pushDonJ3 (hAT : P0.ArchTotal arI) (J3 : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ)
    {t d w sc : U64} (ht : t ∈ Z.T) (hd : d ∈ Z.T) (hw : w ∈ Z.R) (hsC : sc ∈ Z.C) (htd : t ≠ d)
    {xt xd : Fl4Spec.Tcb} {xw : Fl4Spec.Reply} {y : Fl4Spec.SchedContext} {n : Nat}
    (hkt : σ.kheap t.bv = some (.tcb xt)) (hkd : σ.kheap d.bv = some (.tcb xd))
    (hkw : σ.kheap w.bv = some (.reply xw)) (hky : σ.kheap sc.bv = some (.schedContext y n))
    (hst : xt.tcbState = .blockedOnReply w.bv) (hxt : xt.tcbSchedContext = some sc.bv) (hyt : y.scTcb = some t.bv)
    (hxd : xd.tcbSchedContext = none) (hsd : xd.tcbState = .inactive) (hwt : xw.replyTcb = some t.bv)
    (hct : σ.curThread = t.bv) (hcsc : σ.curSc = sc.bv) (hcn : σ.schedulerAction = .chooseNewThread)
    (hnqt : NotQueued σ t.bv) (hnqd : NotQueued σ d.bv) (hya : Fl4Spec.scActive y = true)
    (hdet : Detached Z.C Lst w) (hn0 : L.mem s (rNextA w) = 0#u64) (hp0 : L.mem s (rPrevA w) = 0#u64)
    (hdD : ∀ q ∈ D, q.bv ≠ d.bv) :
    (do
      let i2 ← obj.Sc.reply st sc s
      let s3 ← if i2 != 0#u64 then obj.Reply.set_next st i2 s w false else ok s
      let s4 ← obj.Reply.set_prev st w s3 i2
      let s5 ← obj.Sc.set_reply st sc s4 w
      let s6 ← obj.Reply.set_next st w s5 sc true
      schedcontext.donate st arI s6 a sc d) ⦃ res => res.2 = a ∧
        (do
          Fl4Spec.bindScReply (Z := Unit) sc.bv w.bv
          Fl4Spec.schedContextDonate (Z := Unit) sc.bv d.bv) σ =
          ({((), pdSt σ t.bv d.bv sc.bv w.bv xt xd xw y n)}, False) ∧
        ∃ Lst', JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst' D res.1 a (pdSt σ t.bv d.bv sc.bv w.bv xt xd xw y n) ⦄ := by
  have B := J3.z2.zv.base
  have hS := B.xtop.fin.1.1.1
  refine WP.spec_mono (B.pushDonJ hAT ht hd hw hsC htd hkt hkd hkw hky hst hxt hyt hxd hsd hwt hct hcsc hcn hnqt hnqd hya hdet hn0 hp0 hdD) ?_
  rintro ⟨s', a'⟩ ⟨ha, hsp, Lst', B', hwR, hK⟩
  exact ⟨ha, hsp, Lst', J3.ofBSK B' hwR (fun b hb => RmW.oobj hS hb) (fun b hb => B.rmW_nh hb)
    (B.vkeep_of hwR fun b hb => B.rmW_nv hb) (zvk_tk hK)⟩

set_option maxHeartbeats 4000000 in
/-- **`set_thread_state` of a TCB from `Inactive` at `JAtZV3`** (module docstring). -/
theorem JAtZV3.stsIJ3 (J3 : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T) (htD : t ∉ D)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hrs : x.tcbState = .inactive)
    (ts : Fl4Spec.ThreadState) (hts : tsCode ts < 3) (v : U64) (hv : v.val = tsCode ts)
    (hrel : inClass ts → RelIfBound σ t.bv)
    (hB : sched.set_thread_state st s t v ⦃ s' => P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H
      (P1.Heap.frame H) (P1.Heap.replies H) (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s' ∧
      P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s s' ⦄) :
    sched.set_thread_state st s t v ⦃ s6 => ∃ (Lst' : U64 → List U64),
      JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst' D s6 a
        (stsAct (updK σ t.bv (.tcb { x with tcbState := ts })) t.bv) ⦄ := by
  have B := J3.z2.zv.base
  have hS := B.xtop.fin.1.1.1
  refine WP.spec_mono (B.stsIJ ht htD hk hrs ts hts v hv hrel hB) ?_
  rintro s6 ⟨Lst', B', hW⟩
  refine ⟨Lst', J3.ofBSK B' hW (fun b hb => tfoot_oobj hS hb) (fun b hb => B.tfoot_nh hb)
    (VKeep.of_tfoot hS B.thT hW) ?_⟩
  refine (zvk_upd (o' := .tcb { x with tcbState := ts }) hk rfl (fun _ e => by cases e) (fun _ e => by cases e)
    fun y e hy => ?_).trans
    (ZvK.of_kheap (Notif.stsAct_kheap _ _))
  simp only [Fl4Spec.KernelObject.tcb.injEq] at e
  subst e
  have hy' : ts = .runningVM := hy
  subst hy'
  exact absurd hts (by decide)

set_option maxHeartbeats 4000000 in
/-- **A cap-faulted sender's `send_ipc` to a waiting receiver at `JAtZV3` that pushes a reply and donates the
sender's SC** (P3/XTopJointFaultRecv's `JAtZ.sendFaultPDJ`; module docstring). -/
theorem JAtZV3.sendFaultPDJ3 (hAT : P0.ArchTotal arI) (J3 : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hrn : Fl4Spec.runnable xt.tcbState = true) {cf : Fl4Spec.ObjRef} {rp : Bool} {lf : Fl4Spec.LookupFailure}
    (hft : xt.tcbFault = some (.capFault cf rp lf)) (hct : σ.curThread = t.bv)
    (hres : σ.schedulerAction = .resumeCurThread) (hti : σ.curThread ≠ σ.idleThread)
    (hnq : ∀ dm p, t.bv ∉ σ.readyQueues dm p)
    {e d : U64} (he : e ∈ Z.E) {q : List Fl4Spec.ObjRef}
    (hk : σ.kheap e.bv = some (.endpoint (.recvEP (d.bv :: q))))
    (blk : Bool) (badge : U64) (g gr : Bool)
    (hg : g = true ∨ gr = true)
    (hrepn : ∀ xd, σ.kheap d.bv = some (.tcb xd) → ∀ e' rep dd, xd.tcbState = .blockedOnReceive e' rep dd → rep ≠ none)
    (hxdn : ∀ xd, σ.kheap d.bv = some (.tcb xd) → xd.tcbSchedContext = none) :
    endpoint.send_ipc st arI s a blk false badge g gr true t e ⦃ r =>
      ∃ z ∈ (Fl4Spec.sendIpc (Z := Unit) blk false badge.bv g gr true t.bv e.bv σ).1,
        ZvPost (L := L) arI V X AR r.1 r.2 z.2 ⦄ := by
  have J := J3.z2.zv.base
  have hI := J.xtop.irelK J.ks J.buf
  have hP0 := J.ip
  have hP := hP0.e
  have hH := ipcCore_top (st := st) (th := Z.th) (cr := σ.archState.x64CurrentCr3) (N := Z.N) (C := Z.C)
    (c := Z.c) hP
  have hR := hI.1.toE
  have hS0 := IpcRel.toSRN hI.1 hI.2
  have hTe : Z.T = P1.Heap.tcbs H := J.tcbs_eq.1
  have hRe : Z.R = P1.Heap.replies H := J.tcbs_eq.2
  have hx := hR.at_ep he hk
  have hxt := hR.at_tcb ht hkt
  obtain ⟨hst2, xs, hxs0, hq, hQ, hB⟩ := hx
  obtain ⟨d', xs', rfl⟩ := List.exists_cons_of_ne_nil hxs0
  simp only [List.map_cons, List.cons.injEq] at hq
  obtain ⟨hd', hq'⟩ := hq
  have hdd : d' = d := eq_of_bv hd'.symm
  subst hdd
  have hdT : d' ∈ Z.T := hQ.mem d' (by simp)
  have hda := hP.tcb d' hdT
  obtain ⟨xd, hkd, -⟩ := hI.1.tcb d' hdT
  have hxd := hR.at_tcb hdT hkd
  have hd3 : (L.mem s (tStA d')).val = 3 := (hB d' (by simp)).1
  have hdb : L.mem s (tBlockA d') = e := (hB d' (by simp)).2
  obtain ⟨e', rep, dd, hstd⟩ := tsCode_three (hxd.st.symm.trans hd3)
  have he' : e' = e.bv := by
    have := hxd.blk e' (by rw [hstd]; rfl); rw [hdb] at this; exact this.symm
  subst he'
  obtain ⟨hrep, hrepR⟩ := hxd.recv _ _ _ hstd
  have hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4 := by have := runnable_code hrn; omega
  have htd : t ≠ d' := by intro h; subst h; exact hnb.1 (hxt.st.symm.trans hd3)
  have hde : d'.bv ≠ e.bv := kheap_ne hkd hk (fun _ h1 h2 => by subst h1; cases h2)
  have hte : t.bv ≠ e.bv := kheap_ne hkt hk (fun _ h1 h2 => by subst h1; cases h2)
  have htd' : t.bv ≠ d'.bv := bv_ne htd
  have hdc : d'.bv ≠ σ.curThread := by rw [hct]; exact Ne.symm htd'
  -- P1's facts at the start
  obtain ⟨⟨Q0, R0, h0⟩, hB0, hX0, hSc0, hSg0⟩ := J.blk
  have hdH : d' ∈ P1.Heap.tcbs H := J.zH.1 d' hdT
  have hHe : H e = some .ep := J.zH.2.1 e he
  have hTP : P1.TcbPlaced (P1.Heap.tcbs H) := h0.tcbs
  have hdta := hTP d' hdH
  have hsub := hSg0.sub
  have hds : L.mem s (P1.stA d') = sched.TS_BLOCKED_ON_RECV := by
    rw [stA_tStA, tsVals.2.2.1]; exact UScalar.eq_of_val_eq hd3
  have hbe : L.mem s (P1.blockA d') = e := by rw [P1.blockA_eq, ← tBlockA_eq]; exact hdb
  have hdq := P1.endpoint.ep_dequeue.inv s d' Q0 R0 h0 hdH (by simp) (Or.inr (Or.inl hds))
  rw [hbe] at hdq
  obtain ⟨E0, EQ0, hEW0⟩ := h0.eps
  have heE0 : e ∈ E0 := (hEW0.2.2.2.2.2.2.2.1 e).2 (Or.inl hHe)
  obtain ⟨hE0, -, hq0'⟩ := hEW0.1 e heE0
  have hdm : d' ∈ EQ0 e := by
    have := hEW0.2.2.2.2.1 d' hdH (by simp) (Or.inr (Or.inl hds)); rw [hbe] at this; exact this.2
  have pf := P1.endpoint.ep_dequeue.foot s e d' (EQ0 e) hTP hE0 hq0' hdm
  -- FL4: the endpoint's state and queue
  unfold endpoint.send_ipc
  refine WP.spec_bind (Fl4Proofs.P1.obj.Ep.state.spec s e) ?_
  rintro _ rfl
  rw [epState_eq, hst2]
  rw [if_neg (by rw [ep_state_vals.1]; decide), if_neg (by rw [ep_state_vals.2.1]; decide)]
  refine WP.spec_bind (Fl4Proofs.P1.endpoint.get_queue.spec s e) ?_
  rintro _ rfl
  have hhead : (L.epQ s e).head = d' := by rw [epQ_eq]; exact hQ.head
  rw [hhead]
  -- the dequeue
  refine WP.spec_bind (WP.spec_and (WP.spec_and (ep_dequeue_c hH hP0 hP s σ hR hS0 he hk (d := d')
      (by simp [Fl4Spec.Endpoint.epQueue])) (ep_dequeue_full hP s he d' _ hQ (by simp)))
    (WP.spec_and hdq pf)) ?_
  rintro s1 ⟨⟨⟨-, hR1, hS1, hA1⟩, -, -, hQA, hWE, -, -⟩, ⟨h1, f1, o1, n1, k1, c1, nc1⟩, w1⟩
  set σ1 := Notif.updK σ e.bv (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) with hσ1
  have hW1a : P1.WritesIn st s s1 (fun b => EW e b ∨ ∃ w ∈ (d' :: xs'), TL w b) :=
    ⟨hWE.1, hWE.2.1, fun b hb hn => hQA b hb ⟨fun h => hn (Or.inl h), fun h => hn (Or.inr h)⟩⟩
  have hW1 : P1.WritesIn st s s1 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ) := hW1a.mono fun b hb => by
    rcases hb with h | ⟨w, hw, h | h⟩
    · exact Or.inr (Or.inl ⟨e, he, h⟩)
    · exact Or.inl (Or.inr ⟨w, hQ.mem w hw, 3496, by omega, by omega, by omega, by omega, by omega, h⟩)
    · exact Or.inl (Or.inr ⟨w, hQ.mem w hw, 3504, by omega, by omega, by omega, by omega, by omega, h⟩)
  have F1 : P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s s1 :=
    P1.Foot.of w1 fun b hb => hb.kw hq0'.mem (Or.inl hHe)
  obtain ⟨hB1, hX1, hS1', hSg1, -, -, -⟩ := P1.frame_bx h0 hB0 hX0 hSc0 hSg0 f1 o1 n1 k1
    (P1.TmFr.mk0 ⟨k1, fun y hy K a b c => f1 y hy K (by omega) c (by omega) (by omega),
      fun c hc o ho => nc1 c hc o (by omega) (by omega), fun n' hn' => o1 _ (hSg0.sub _ (hX0.1.ntB n' hn').2)⟩)
  have hkt1 : σ1.kheap t.bv = some (.tcb xt) := by simp [σ1, hte, hkt]
  have hkd1 : σ1.kheap d'.bv = some (.tcb xd) := by simp [σ1, hde, hkd]
  have hk1e : σ1.kheap e.bv = some (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) := by simp [σ1]
  have hdb1 : L.mem s1 (tBlockA d') = e := by
    rw [hA1 _ (a_blk hda).1 ⟨d', hdT, (a_blk hda).2⟩, hdb]
  have hq1 := dequeued_not_queued hR1 he hdb1 hk1e (epDeq_not_mem _)
  have Fr1 : CFr e.bv d'.bv σ σ1 := CFr.upd hk (Or.inr (Or.inr (Or.inl ⟨_, _, rfl, rfl,
    by rw [epDeq_queue']; unfold Fl4Spec.removeAll; exact List.filter_sublist,
    by simp [Fl4Spec.Endpoint.epQueue]⟩)))
  have IK1 : IK d'.bv σ σ1 := IK.updOther (o' := .endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) hk (fun o0 h => by
    rcases h with rfl | rfl <;> exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h)⟩)
  have SK1 : Ipc.SKeep σ σ1 := Ipc.SKeep.updK (p := e.bv) (o := .endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) (fun y h => by cases h) (fun _ _ h => by cases h)
  have hOK1 : Endp.IpcBufCapOK σ1 := ipcBufCapOK_epStep (J.xferH).1 (EpStep.ep hk)
  -- the transfer
  have hdth : Z.th d' = some .tcb := by
    obtain ⟨⟨⟨G0, hB0'⟩, -⟩, -⟩ := hS0.1.1
    exact Ipc.RelTopB.tcbT hB0' hkd
  have hUd := J.rbufU hdT hdth hkd
  refine WP.spec_bind (xferFaultStepJ hP0 hP (hH.epHyps hP0) s1 a σ1 hR1 hS1 hOK1
    (bufCover_epStep (J.xferH).2.1 (EpStep.ep hk)) ht hdT htd hkt1 hkd1 hft e badge g
    hTP hdH h1 hB1 hX1 hS1' hSg1 (fun b hb => ⟨(hUd b hb).1.ksb hW1.1, (hUd b hb).2⟩)) ?_
  rintro s2 ⟨x2, um2, e2, hx2, hR2, hS2, hA2, w2, h2, hB2, hX2, hS2'', hSg2, f2⟩
  set σ2 := Notif.updK (Endp.setUm σ1 um2) d'.bv (.tcb x2) with hσ2
  have hkd2 : σ2.kheap d'.bv = some (.tcb x2) := by simp [σ2]
  have hkt2 : σ2.kheap t.bv = some (.tcb xt) := by simp [σ2, htd', hkt1]
  have hst2' : x2.tcbState = .blockedOnReceive e.bv rep dd := by rw [hx2]; exact hstd
  have hxsc : x2.tcbSchedContext = xd.tcbSchedContext := by rw [hx2]
  have hN2 := ntfn_lift_rcv hP0.toC hS1.2 hR2 hdT hA2 (fun p hp => by simp [σ2, hp])
    hkd1 hkd2 (by rw [hx2])
  have hS2' : SRN st Z.N Z.T (SRS st Z.T (SRT st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c
      (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c))) s2 σ2 := ⟨hS2.1, hN2⟩
  have hk1e2 : σ2.kheap e.bv = some (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) := by
    simp [σ2, Ne.symm hde, hk1e]
  have hq2 : ∀ e'' ∈ Z.E, ∀ z, σ2.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue := by
    intro e'' he'' z hz
    have hne : d'.bv ≠ e''.bv := by intro h; rw [← h, hkd2] at hz; cases hz
    exact hq1 e'' he'' z (by simpa [σ2, Ne.symm hne] using hz)
  have hrw : L.mem s2 (tReplyA d') = L.mem s (tReplyA d') := by
    rw [hA2 _ (a_reply hda).1 ⟨?_, ?_⟩, hA1 _ (a_reply hda).1 ⟨d', hdT, (a_reply hda).2⟩]
    · rintro ⟨r', hr'⟩
      rw [val_reply hda, regA_val hda (regIdx_lt r')] at hr'; have := regIdx_lt r'; omega
    · rintro ⟨wp, hwp, e'⟩
      have h1' := hP.bt wp hwp d' hdT
      have h2' := val_reply hda
      rw [← e'] at h1'; omega
  have hW2 : P1.WritesIn st s s2 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ b ∨ RcvBufW xd b) :=
    (hW1.mono fun b hb => Or.inl hb).trans1 (w2.mono fun b hb => by
    rcases hb with (⟨y, hy, K, h1', h2', -, eb⟩ | hb) | hb
    · have hyT : y ∈ Z.T := by rw [hTe]; exact hy
      refine Or.inl (Or.inl (Or.inr ⟨y, hyT, K.val, h1', by omega, by omega, by omega, by omega, ?_⟩))
      rw [eb]; exact tfield_val (hP.tcb y hyT) (by omega)
    · exact absurd hb (Set.notMem_empty _)
    · exact Or.inr hb)
  have F2 : P1.WritesIn st s1 s2 (fun b => P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
      (P1.Heap.scBits H) (P1.EH H) s1 b ∨ RcvBufW xd b) :=
    w2.mono fun b hb => by
      rcases hb with (⟨y, hy, K, h1', h2', h3', eb⟩ | hb) | hb
      · exact Or.inl (Or.inl ⟨y, hy, K, by omega, by omega, by omega, by omega, eb⟩)
      · exact absurd hb (Set.notMem_empty _)
      · exact Or.inr hb
  have Fr2 : CFr e.bv d'.bv σ σ2 := (Fr1.trans (CFr.um _ _ σ1 um2)).trans (CFr.upd (σ := Endp.setUm σ1 um2) hkd1
    (Or.inl ⟨xd, xd.tcbState, xd.tcbBoundNotification, xd.tcbFault, x2.tcbArch, rfl, by rw [hx2],
    Or.inr ⟨Or.inl rfl, rfl, Or.inl ⟨_, _, _, hstd⟩, Or.inr (Or.inr rfl)⟩⟩))
  have IK2 : IK d'.bv σ σ2 := IK1.trans ((IK.um _ σ1 um2).trans (IK.updSelf (σ := Endp.setUm σ1 um2) hkd1 hxsc))
  have SK2 : Ipc.SKeep σ σ2 := SK1.trans ((Fl4Proofs.P3.SKeep.um σ1 um2).trans (Ipc.SKeep.updK (σ := Endp.setUm σ1 um2) (p := d'.bv)
    (o := .tcb x2) (fun y h => ⟨xd, hkd1, by cases h; exact hxsc.symm⟩) (fun _ _ h => by cases h)))
  have hks2 : L.ksb s2 = L.ksb s := hW2.1
  have Fst2 : L.mem s2 (P1.stA d') = L.mem s (P1.stA d') := by
    rw [P1.stA_eq]
    exact (f2 d' hdH _ (by simp) (by simp) (by simp)).trans (f1 d' hdH _ (by simp) (by simp) (by simp) (by simp))
  have hds2 : L.mem s2 (P1.stA d') = sched.TS_BLOCKED_ON_RECV := Fst2.trans hds
  -- the reply object
  obtain ⟨r, hrp⟩ := Option.ne_none_iff_exists'.1 (hrepn xd hkd _ _ _ hstd)
  subst hrp
  obtain ⟨hw0, hwr⟩ := Notif.optRef_some hrep
  have hwR := hrepR (by simp)
  refine WP.spec_bind (Endp.obj.Tcb.reply_obj.spec s2 d') ?_
  rintro _ rfl
  rw [hrw]
  have hne0 : (L.mem s (tReplyA d') != 0#u64) = true := by simp [hw0]
  simp only [hne0, ↓reduceIte, Bool.false_eq_true, eq_self_iff_true, if_true]
  set w := L.mem s (tReplyA d') with hwdef
  subst hwr
  obtain ⟨xr, hkr, -⟩ := hR.reply w hwR
  have hwe : w.bv ≠ e.bv := kheap_ne hkr hk (fun _ h1 h2 => by subst h1; cases h2)
  have hwd : w.bv ≠ d'.bv := kheap_ne hkr hkd (fun _ h1 h2 => by subst h1; cases h2)
  have hwt : w.bv ≠ t.bv := kheap_ne hkr hkt (fun _ h1 h2 => by subst h1; cases h2)
  have hkr2 : σ2.kheap w.bv = some (.reply xr) := by simp [σ2, σ1, hwe, hwd, hkr]
  have hb' : xr.replyTcb = some d'.bv := hback_of J.sv hkd e.bv w.bv dd xr (by rw [hstd]) hkr
  have hX2' := IpcRel.ofSRN hR2 hS2'
  have hrA : L.mem s2 (P1.replyA d') = w := by show L.mem s2 (tReplyA d') = w; rw [hrw]
  obtain ⟨hiR, hit⟩ := hX2.2.1.recv d' hdH hds2 (by rw [hrA]; exact hw0)
  rw [hrA] at hiR hit
  refine WP.spec_bind (WP.spec_and (WP.spec_and (reply_unlink_c hH hP0 hP s2 σ2 hR2 hS2' hdT hkd2 hst2' hwR hkr2
      hb' hq2) (reply_unlink_cn hP0 hX2' hdT hwR hkr2))
    (WP.spec_and (P1.ipc.reply_unlink.inv s2 w d' Q0 R0 h2 hdH hX2.1 hsub hiR hit
        (by rw [hds2]; exact P1.blocked_not_runnable (Or.inr (Or.inl rfl))) (Or.inl (Or.inr rfl)))
      (P1.ipc.reply_unlink.kw (Sg := P1.Heap.frame H) (Scs := P1.Heap.scs H) (Z := P1.Heap.scBits H)
        (Es := P1.EH H) s2 w d' h2 hX2 hsub hiR hdH))) ?_
  rintro s3 ⟨⟨⟨e3, hR3, hS3⟩, hW3⟩, ⟨h3, e3', k3, z3⟩, fu3⟩
  have hclr : ∀ r ∈ P1.Heap.replies H, L.mem s2 (P1.rTcbA r) = d' → L.mem s3 (P1.rTcbA r) = 0#u64 := by
    intro r hr er
    obtain ⟨-, -, b2, -⟩ := hX2.2.1.back r hr (by rw [er]; exact fun e0 => hdta.ne0 (by rw [e0]; rfl))
    rw [er, hrA] at b2; rw [← b2]; exact z3
  set x3 : Fl4Spec.Tcb := { x2 with tcbState := .inactive } with hx3
  set xr3 : Fl4Spec.Reply := { xr with replyTcb := none } with hxr3
  set σ3a := Notif.updK σ2 w.bv (.reply xr3) with hσ3a
  have hkd3a : σ3a.kheap d'.bv = some (.tcb (x2)) := by simp [σ3a, Ne.symm hwd, hkd2]
  have hct3a : d'.bv ≠ (Notif.updK σ3a d'.bv (.tcb x3)).curThread := hdc
  have e3s : Notif.stsAct (Notif.updK σ3a d'.bv (.tcb x3)) d'.bv = Notif.updK σ3a d'.bv (.tcb x3) :=
    stsAct_ne hct3a
  set σ3 := Notif.stsAct (Notif.updK σ3a d'.bv (.tcb x3)) d'.bv with hσ3
  have hU : Fl4Spec.NonDet.maybeM (Fl4Spec.replyUnlinkTcb (Z := Unit) d'.bv) (some w.bv) σ2 =
      ({((), σ3)}, False) := e3
  have hW3' : P1.WritesIn st s s3 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ b ∨ RcvBufW xd b) :=
    hW2.trans1 (hW3.mono fun b hb => Or.inl (cnW_back hks2 (SzKeepC.of Fr2.szKeep) hb))
  have hkt3 : σ3.kheap t.bv = some (.tcb xt) := by rw [stsAct_kheap]; simp [σ3a, htd', hwt.symm, hkt2]
  have hkd3 : σ3.kheap d'.bv = some (.tcb x3) := by rw [stsAct_kheap]; simp
  have hkr3 : σ3.kheap w.bv = some (.reply xr3) := by rw [stsAct_kheap]; simp [σ3a, hwd]
  have hq3 : ∀ e'' ∈ Z.E, ∀ z, σ3.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue := by
    intro e'' he'' z hz
    rw [stsAct_kheap] at hz
    have hne : d'.bv ≠ e''.bv := by intro h; rw [← h] at hz; simp at hz
    have hne' : w.bv ≠ e''.bv := by intro h; rw [← h] at hz; simp [σ3a, hwd] at hz
    exact hq2 e'' he'' z (by simpa [σ3a, Ne.symm hne, Ne.symm hne'] using hz)
  have Fr3 : CFr e.bv d'.bv σ σ3 := (Fr2.trans (CFr.upd hkr2 (Or.inr (Or.inr (Or.inr ⟨xr, rfl, rfl, hb'⟩))))).trans
    (CFr.stsIn hkd3a (Or.inl ⟨_, _, _, hst2'⟩))
  have IK3 : IK d'.bv σ σ3 := by
    have IK3a : IK d'.bv σ σ3a := IK2.trans (IK.updOther (o' := .reply xr3) hkr2 (fun o0 h => by
      rcases h with rfl | rfl <;> exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h)⟩))
    have IK3b : IK d'.bv σ (Notif.updK σ3a d'.bv (.tcb x3)) := IK3a.trans (IK.updSelf (y := x3) hkd3a rfl)
    exact IK3b.trans (IK.sts _ _ _)
  have SK3 : Ipc.SKeep σ σ3 :=
    ((SK2.trans (Ipc.SKeep.updK (p := w.bv) (o := .reply xr3) (fun y h => by cases h) (fun _ _ h => by cases h))).trans
      (Ipc.SKeep.updK (p := d'.bv) (o := .tcb x3) (fun y h => ⟨_, hkd3a, by cases h; rfl⟩) (fun _ _ h => by cases h))).trans
      (Ipc.SKeep.stsAct _ _)
  have hct3 : σ3.curThread = σ.curThread := by rw [e3s]; rfl
  have hact3 : σ3.schedulerAction = σ.schedulerAction := by rw [e3s]; rfl
  have hsc3 : x3.tcbSchedContext = xd.tcbSchedContext := by simp [x3, hxsc]
  have hB3 := hB2.keepT h2 k3 (by rw [e3']; exact P1.not_blocked_inactive) (by rw [e3']; exact P1.inactive_ne.1)
  have hX3 := hX2.keepT k3 (by rw [e3']; exact P1.inactive_ne) hclr
  have hS3' := hS2''.keepT hX2 k3
  have hSg3 : P1.SgOK st (P1.Heap.omega H) (P1.Heap.frame H) s3 :=
    ⟨hsub, fun b hb => by rw [k3.ksb]; exact hSg2.ks b hb, fun o h1' h2' => by rw [k3.ksb]; exact hSg2.ksΩ o h1' h2'⟩
  have hnr3 : ∀ r ∈ P1.Heap.replies H, L.mem s3 (P1.rTcbA r) ≠ d' :=
    hX3.noref hdta (by rw [e3']; exact P1.inactive_ne.1) (by rw [e3']; exact P1.inactive_ne.2)
  have F3 := footW_trans (footW_trans (footW_of F1) F2) (footW_of fu3)
  have hxt3 := hR3.at_tcb ht hkt3
  have hty3 : L.mem s3 (tFaultA t) = fl4_abi.consts.fault.CapFault := by
    have hfr := hxt3.faultR
    unfold FaultRel at hfr; rw [hft] at hfr; rw [hfr.1]; unfold fl4_abi.consts.fault.CapFault; rfl
  have hks3 : L.ksb s3 = L.ksb s := hW3'.1
  -- the caller's and the receiver's words at `s3`
  have hCI : CurInv σ := J.cur.resolve_left (by rw [hres]; intro h; cases h)
  have hnrT : t.bv ∉ σ.releaseQueue := by rw [← hct]; exact hCI.notRel
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  have hw3 : (L.mem s3 (P1.stA t)).val = tsCode xt.tcbState := by
    rw [P1.stA_eq, ← tStA_eq, hxt3.st]
  obtain ⟨hnbt3, hnrp3⟩ := P1.run_word (w := L.mem s3 (P1.stA t)) (by rw [hw3]; exact runnable_code hrn)
  have hX3' := IpcRel.ofSRN hR3 hS3
  have hSR3 : SchedRel st Z.N Z.T Z.C Z.c s3 σ3 := hX3'.2.2.1
  obtain ⟨Q3, R3', hcq3, hs3⟩ := hSR3.lists
  have hSM := ScRelM.of hX3'.1
  have hnqD : NotQueued σ d'.bv := by
    refine ⟨fun dm p hm => ?_, fun hm => ?_⟩
    · obtain ⟨x, -, -, -, hkx, -, hrx, -, -⟩ := J.inv.rq dm p _ hm
      rw [hkd] at hkx; cases hkx; rw [hstd] at hrx; cases hrx
    · obtain ⟨x, -, -, -, hkx, -, hrx, -, -⟩ := J.inv.rel _ hm
      rw [hkd] at hkx; cases hkx; rw [hstd] at hrx; cases hrx
  have hnqT3 : NotQueued σ3 t.bv := ⟨by rw [IK3.2.1]; exact hnq, by rw [IK3.2.2.1]; exact hnrT⟩
  have hnqD3 : NotQueued σ3 d'.bv := ⟨by rw [IK3.2.1]; exact hnqD.1, by rw [IK3.2.2.1]; exact hnqD.2⟩
  have bits3 : ∀ u ∈ Z.T, NotQueued σ3 u.bv →
      (L.mem s3 (P1.inqA u) &&& sched.Q_QUEUED) = 0#u64 ∧ (L.mem s3 (P1.inqA u) &&& sched.Q_RELEASE) = 0#u64 := by
    intro u hu hnu
    refine ⟨Classical.byContradiction fun h => ?_, Classical.byContradiction fun h => ?_⟩
    · have hm := (hcq3.queued u hu).1 h
      apply hnu.1 0 (specPrio (L.mem s3 (P1.prioA u)))
      rw [hs3.rq _ (hcq3.prio u hu)]
      exact List.mem_map_of_mem hm
    · have hm := (hcq3.released u hu).1 h
      apply hnu.2
      rw [hs3.rel]
      exact List.mem_map_of_mem hm
  obtain ⟨hqbT, hrbT⟩ := bits3 t ht hnqT3
  obtain ⟨hqbD, hrbD⟩ := bits3 d' hdT hnqD3
  have ha0 : L.actionW s3 = 0#u64 := by
    have h := hSR3.act
    rw [hact3, hres] at h
    unfold P1.LawfulStore.actionW; rw [hcq3.cur]; exact h
  have hna3 : ∀ u ∈ Z.T, L.actionW s3 ≠ u := fun u hu h' => by
    rw [ha0] at h'; exact (hcq3.tcbs u hu).ne0 (by rw [← h']; rfl)
  have hcw3 : L.curW s3 = t := by
    have h : (Sched.nodeW st s3 Z.c layout.node.CUR_THREAD).bv = t.bv := by rw [← hs3.curThread, hct3, hct]
    unfold P1.LawfulStore.curW; rw [hcq3.cur]; exact P1.eq_of_bv h
  have hidl3 : σ3.idleThread = σ.idleThread := Fr3.sk.idle
  have hiw3 : ∀ u ∈ Z.T, u.bv ≠ σ.idleThread → L.idleW s3 ≠ u := fun u hu hne h' => by
    apply hne
    rw [← hidl3, hs3.idleTh]
    unfold P1.LawfulStore.idleW at h'; rw [hcq3.cur] at h'
    exact congrArg _ (show Sched.nodeW st s3 Z.c layout.node.IDLE_THREAD = u from h').symm
  have hit : t.bv ≠ σ.idleThread := by rw [← hct]; exact hti
  have hid : d'.bv ≠ σ.idleThread := by
    intro h
    obtain ⟨x, hkx, -, hxs, -⟩ := J.act.2
    rw [← h, hkd] at hkx; cases hkx; rw [hstd] at hxs; cases hxs
  have hcA : L.mem s3 (P1.scA t) ≠ 0#u64 → L.mem s3 (P1.scA t) ∈ Ac := fun h0 =>
    hB3.sact t htH (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ha0, hcw3⟩))))) h0
  have hwH : w ∈ P1.Heap.replies H := hRe ▸ hwR
  have hw00 : w ≠ 0#u64 := (J.rp.align w hwR).2.1
  have hqt3 := Endp.not_queued hR3 ht hkt3 hnb
  -- the caller's SC, donated
  obtain ⟨xc, hkc, hcs, -⟩ := hCI.tcb
  rw [hct, hkt] at hkc; cases hkc
  obtain ⟨y, n, hky0⟩ := hCI.sc
  have hya : Fl4Spec.scActive y = true := hCI.active (J.curSc_ne_idle hCI hti) y n hky0
  obtain ⟨sc, hsC, esc⟩ := J.obj.sc _ y n hky0
  rw [← esc] at hky0 hcs
  obtain ⟨y1, n1, hky1, hyt⟩ := J.inv.back _ _ _ hkt hcs
  rw [hky0] at hky1; cases hky1
  have hrelσ : Fl4Spec.scActive y = true → released σ y := fun ha =>
    J.inv.rd t.bv xt hkt (Or.inl hrn) xt sc.bv y n hkt hcs hky0 ha hnrT
  have hse : sc.bv ≠ e.bv := kheap_ne hky0 hk (fun _ h1 h2 => by subst h1; cases h2)
  have hsd : sc.bv ≠ d'.bv := kheap_ne hky0 hkd (fun _ h1 h2 => by subst h1; cases h2)
  have hsw : sc.bv ≠ w.bv := kheap_ne hky0 hkr (fun _ h1 h2 => by subst h1; cases h2)
  have hst : sc.bv ≠ t.bv := kheap_ne hky0 hkt (fun _ h1 h2 => by subst h1; cases h2)
  have hky2 : σ2.kheap sc.bv = some (.schedContext y n) := by simp [σ2, σ1, hsd, hse, hky0]
  have hky3 : σ3.kheap sc.bv = some (.schedContext y n) := by rw [stsAct_kheap]; simp [σ3a, hsd, hsw, hky2]
  have hsw3 : L.mem s3 (P1.scA t) = sc := by
    obtain ⟨x', hk', -, -, hscw, -⟩ := hs3.tcb t ht
    rw [hkt3] at hk'; cases hk'
    exact optRef_some_eq (hscw.symm.trans hcs)
  have hxdn3 : x3.tcbSchedContext = none := by rw [hsc3]; exact hxdn xd hkd
  -- the J state after the block
  have hcD : ∀ q ∈ D, q.bv ≠ t.bv := J.notDead ht hkt (by have := runnable_code hrn; omega)
  have htD := J.not_dead_of_st hdT hkd (by rw [hstd]; simp [tsCode])
  have hwD : ∀ q0 ∈ D, q0.bv ≠ w.bv := fun q0 hq0 e0 => by
    have hqw : q0 = w := P1.eq_of_bv e0
    rw [hqw] at hq0
    have d1 : L.mem s (Endp.rTcbA w) = 0#u64 := (J.jcov.dead w hq0).2.2.2.1 hwH
    obtain ⟨xr', hkr', hxr'⟩ := hR.reply w hwR
    rw [hkr] at hkr'; cases hkr'
    rw [hb', d1, optRef_zero] at hxr'
    cases hxr'
  have hRR : ∀ q' ∈ Z.R, ∀ xr, σ.kheap q'.bv = some (.reply xr) → xr.replyTcb = some d'.bv →
      Detached Z.C Lst q' ∧ L.mem s (rNextA q') = 0#u64 ∧ L.mem s (rPrevA q') = 0#u64 :=
    fun q' hq'' xr hx' hxt' => J.recvReplyB q' hq'' xr d'.bv xd hx' hxt' hkd
      (by rw [hstd]; rfl)
  have hrib3 : RelIfBound σ3 d'.bv :=
    Ipc.RelIfBound.of_keep (J.inv.rd d'.bv xd hkd (Or.inr (Or.inr (Or.inr ⟨_, _, _, hstd⟩)))) SK3
  have I3 : Inv σ3 := ((J.inv.toBut d'.bv).ik hnqD IK3).1.inv fun _ _ _ => hrib3
  have hscA3 : ∀ p y n, σ3.kheap p = some (.schedContext y n) → y.scTcb = some t.bv →
      Fl4Spec.scActive y = true := by
    intro p y n hp hyt
    have hp0 : σ.kheap p = some (.schedContext y n) := SK3.2.2.2 _ _ _ hp
    obtain ⟨q, hqC, eq⟩ := J.obj.sc p y n hp0
    subst eq
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    have hq0 := J.c0 q hqC
    have hqS : q ∈ P1.Heap.scs H := ⟨_, (hJ.sc q y n hq0 hp0).2⟩
    have hS := J.xtop.fin.1.1.1
    obtain ⟨u, -, -, xu, hku, hxs⟩ := scBack_of hS J.blk.2.2.1 J.tcbs_eq.1.symm hqC hqS hq0 hp0 hyt
    rw [hkt] at hku; cases hku
    have e1 : σ.curSc = q.bv := by rw [← esc]; exact Option.some.inj (hcs.symm.trans hxs)
    rw [← e1] at hp0
    exact hCI.active (J.curSc_ne_idle hCI hti) y n hp0
  set xtP : Fl4Spec.Tcb := { xt with tcbState := .blockedOnReply w.bv } with hxtP
  set xwP : Fl4Spec.Reply := { xr3 with replyTcb := some t.bv } with hxwP
  set σP := pushSt σ3 t.bv w.bv xr3 xt with hσP
  set σD := pdSt σP t.bv d'.bv sc.bv w.bv xtP x3 xwP y n with hσD
  have hktP : σP.kheap t.bv = some (.tcb xtP) := ps_kt
  have hkwP : σP.kheap w.bv = some (.reply xwP) := ps_kw hwt
  have hkdP : σP.kheap d'.bv = some (.tcb x3) := by rw [ps_ko (Ne.symm htd') (Ne.symm hwd)]; exact hkd3
  have hkyP : σP.kheap sc.bv = some (.schedContext y n) := by rw [ps_ko hst hsw]; exact hky3
  have hcnP : σP.schedulerAction = .chooseNewThread := ps_act (by rw [hct3, hct]) (by rw [hact3, hres])
  have hnsw : ∀ u, σP.schedulerAction ≠ .switchThread u := fun u e0 => by rw [hcnP] at e0; cases e0
  have hctP : σP.curThread = t.bv :=
    (ps_skD (σ := σ3) (t := t.bv) (w := w.bv) (xr := xr3) (xt := xt)).ct.trans (hct3.trans hct)
  have hcscP : σP.curSc = sc.bv :=
    (ps_skD (σ := σ3) (t := t.bv) (w := w.bv) (xr := xr3) (xt := xt)).csc.trans (Fr3.sk.csc.trans esc.symm)
  have hnqtP : NotQueued σP t.bv := ⟨by rw [ps_rq]; exact hnqT3.1, by rw [ps_rel]; exact hnqT3.2⟩
  have hnqdP : NotQueued σP d'.bv := ⟨by rw [ps_rq]; exact hnqD3.1, by rw [ps_rel]; exact hnqD3.2⟩
  have hhP := J.stackHead hsC hky0 (hRR w hwR xr hkr hb').1
  have hhP' : ∀ h l, y.scReplies = h :: l → h ≠ sc.bv ∧ h ≠ w.bv ∧ ∃ x, σP.kheap h = some (.reply x) := by
    intro h l hr
    obtain ⟨h1, h2, x, hx⟩ := hhP h l hr
    refine ⟨h1, h2, x, ?_⟩
    have ht' : h ≠ t.bv := fun e0 => by rw [e0, hkt] at hx; cases hx
    have hd' : h ≠ d'.bv := fun e0 => by rw [e0, hkd] at hx; cases hx
    have he' : h ≠ e.bv := fun e0 => by rw [e0, hk] at hx; cases hx
    rw [ps_ko ht' h2, stsAct_kheap]
    simp [σ3a, hd', h2, σ2, σ1, he', hx]
  have hpdE := pd_eq hktP hkdP hkyP hkwP (Ne.symm hsw) hhP' hyt htd' hst hsd hwt hwd
    hctP.symm hnqtP hnsw
  have hpushE : Fl4Spec.replyPush (Z := Unit) t.bv d'.bv w.bv true σ3 = ({((), σD)}, False) := by
    rw [replyPush_don_eq hkt3 hkd3 hkr3 hwt hcs hxdn3]; exact hpdE
  have hns3 : tsCode xt.tcbState ≠ 6 := by have := runnable_code hrn; omega
  -- the push: link and block (`J` again), then the donation at `J`
  have hPush : ipc.reply_push st arI s3 a t d' w true ⦃ r => r.2 = a ∧ ∃ σ',
      Fl4Spec.replyPush (Z := Unit) t.bv d'.bv w.bv true σ3 = ({((), σ')}, False) ∧
      (σ' = σD → ∃ (Lst' : U64 → List U64), JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst' D r.1 a σ') ⦄ := by
    refine reply_push_iC (don := true) (P := fun s' σ' => σ' = σD → ∃ (Lst' : U64 → List U64),
        JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst' D s' a σ')
      hH hP0 hP s3 a σ3 hR3 hS3 ht hkt3 hkd3 hqt3 hns3 hwR hkr3 (fun _ => hdT) (fun s' _ _ e0 => ?_) ?_
    · exfalso
      have h1 : σD.kheap t.bv = some (.tcb xtP) := by rw [← e0]; exact hktP
      have h2 : σD.kheap t.bv = some (.tcb { xtP with tcbSchedContext := none }) :=
        @dn_kt (bdSt σP sc.bv w.bv y n xwP) t.bv d'.bv sc.bv xtP x3 { y with scReplies := w.bv :: y.scReplies } n
          htd' hst
      rw [h2] at h1
      have h3 : ({ xtP with tcbSchedContext := none } : Fl4Spec.Tcb) = xtP := by
        injection h1 with h1; injection h1
      have h4 : (none : Option Fl4Spec.ObjRef) = some sc.bv := (congrArg Fl4Spec.Tcb.tcbSchedContext h3).trans hcs
      cases h4
    · intro _ s4 hsb hR4 hS4 _ _ _ _
      rw [hsw3]
      have hsb' : sched.set_blocked_on_reply st (L.wr s3 (P1.rTcbA w) t) t w = ok s4 := hsb
      -- FL4's words and P1 at the block
      have hw1 : P1.WritesIn st s3 (L.wr s3 (P1.rTcbA w) t) (fun b => b.val = w.val) := by
        obtain ⟨-, -, -, hA1⟩ := reply_write_rel (hH.epHyps hP0) hP s3 σ3 hR3 hS3.1 hwR hkr3 t
        exact ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun b hb hn => hA1 b hb hn⟩
      have hW4 : P1.WritesIn st s3 s4 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s3 σ3) := by
        have h := set_blocked_on_reply_cn (N := Z.N) (C := Z.C) (E := Z.E) hP hSR3 ht hwR hw1
        rw [hsb', WP.spec_ok] at h; exact h
      have hW4' : P1.WritesIn st s s4 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ b ∨ RcvBufW xd b) :=
        hW3'.trans1 (hW4.mono fun b hb => Or.inl (cnW_back hks3 (SzKeepC.of Fr3.szKeep) hb))
      have hb4 := P1.sched.set_blocked_on_reply.ipc s3 t w Q0 R0 h3 (fun y hy => by
          obtain ⟨hy1, hy2⟩ := hy
          rcases hy1 with hy1 | hy1
          · exact absurd hy1 (Set.notMem_empty _)
          · exact absurd hy1 hy2) (Or.inr hnbt3) hB3 hX3 hS3' hSg3 htH hqbT hrbT
        (hna3 t ht) (hiw3 t ht hit) ⟨hnrp3, fun e0 => hnbt3 (Or.inr (Or.inl e0))⟩ hwH hw00 z3 hcA
      rw [hsb', WP.spec_ok] at hb4
      obtain ⟨h4, hB4, hX4, hS4', hSg4, -, -, -, -, -, -⟩ := hb4
      have hO3 := hX3.1
      obtain ⟨hrΩ3, -⟩ := P1.objs_omega hO3 hSg3.sub
      have f1 : P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H)
          s3 (L.wr s3 (P1.rTcbA w) t) :=
        P1.foot_wr (h3.omega _ (hrΩ3 w hwH).1).1 (P1.kw_sg (hO3.tcbW hwH))
      have q1 := (P1.omega_wr (v := t) h3 (hrΩ3 w hwH).1).1
      have f4 := P1.sched.set_blocked_on_reply.kw (Sg := P1.Heap.frame H) (Scs := P1.Heap.scs H)
        (Z := P1.Heap.scBits H) (Es := P1.EH H) _ t w q1 htH
      rw [hsb', WP.spec_ok] at f4
      have hfoot4 : P1.WritesIn st s s4 (fun b => P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
          (P1.Heap.scBits H) (P1.EH H) s b ∨ RcvBufW xd b) :=
        footW_trans (footW_trans F3 (footW_of f1)) (footW_of f4)
      have hIR4 := IpcRel.ofSRN hR4 hS4
      obtain ⟨su, umu, Ju3, hWu, hFu, -, -⟩ := J3.bufRebaseX3 hdT hdth hkd hW4' hfoot4
      have Ju := Ju3.z2.zv.base
      have hIu := Ju.xtop.irelK Ju.ks Ju.buf
      have hRRu : ∀ q' ∈ Z.R, ∀ xr, (Endp.setUm σ umu).kheap q'.bv = some (.reply xr) → xr.replyTcb = some d'.bv →
          Detached Z.C Lst q' ∧ L.mem su (rNextA q') = 0#u64 ∧ L.mem su (rPrevA q') = 0#u64 :=
        fun q' hq'' xr hx' hxt' => Ju.recvReplyB q' hq'' xr d'.bv xd hx'
          hxt' hkd (by rw [hstd]; rfl)
      have hF4 : IFrame (L := L) Z.th su s4 := IRel.iframe_of hIu hWu fun b hb => CnW.oobj hIu.2.2.1 hb
      have hblk4 : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
          (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s4 := ⟨⟨Q0, R0, h4⟩, hB4, hX4, hS4', hSg4⟩
      have I4 : Inv σP := ps_inv hkt3 hkr3 hwt I3 hnqT3.1 hnqT3.2
      have B4 : BlockedScActive σP := ps_bsa hkt3 hkr3 hwt hscA3 (Fr3.bsa J.bsa)
      have hidT3 : σ3.idleThread ≠ t.bv := by rw [Fr3.sk.idle, ← hct]; exact fun e0 => hti e0.symm
      have hAI4 : ActIdle σP :=
        ⟨fun u hu => (by rw [hcnP] at hu; cases hu), ps_idleOK hkt3 hkr3 hwt hidT3 (Fr3.idleOK J.act.2)⟩
      have hkq : ∀ q ∈ D, σP.kheap q.bv = σ3.kheap q.bv := fun q hq => ps_ko (hcD q hq) (hwD q hq)
      have ho : ∀ {q : Fl4Spec.ObjRef} {o : Fl4Spec.KernelObject}, (∀ x, o ≠ .tcb x) → (∀ x, o ≠ .reply x) →
          (σP.kheap q = some o ↔ σ3.kheap q = some o) := fun h1 h2 => ps_oth hkt3 hkr3 hwt h1 h2
      have J4B := Ju.wake_postGR hIR4 hF4 hWu hblk4 hFu (DWFr.ofUm (DWFr.ofCFr Fr3) umu) ps_skD
        (ps_ksub hkt3 hkr3 hwt) (ps_szKeep hkt3 hkr3 hwt) (ps_ykeep hkt3 hkr3 hwt) (ps_mcpKeep hkt3 hkr3 hwt)
        (ps_bufKeep hkt3 hkr3 hwt) (fun d _ h => ps_recvB hkt3 hkr3 hwt h) (ps_ksz hkt3 hkr3 hwt)
        (ps_kback hkt3 hkr3 hwt) (ps_ipcFr hkt3 hkr3 hwt) (ps_ck hkt3 hkr3 hwt) (fun d _ h => ps_free hkt3 hkr3 hwt h)
        (fun q ao h => (ho (fun _ e => by cases e) (fun _ e => by cases e)).2 h) hkq
        I4 B4 hAI4 (Or.inl hcnP) (Or.inl (by rw [hcnP]; intro h; cases h))
        (ps_own hkt3 hkr3 hwt ((DWFr.ofCFr Fr3).own ⟨d', hdT, rfl⟩ J.own))
        (ps_off hkt3 hkr3 hwt ((DWFr.ofCFr Fr3).off J.off)) (ps_nsc hkt3 hkr3 hwt ((DWFr.ofCFr Fr3).nsc J.nsc))
        (ps_isorted hkt3 hkr3 hwt ((DWFr.ofCFr Fr3).isorted J.isorted)) hRRu htD
      have J4 := Ju3.ofCnW J4B hWu ((zvk_dwfr (DWFr.ofUm (DWFr.ofCFr Fr3) umu)).trans
        (zvk_pushSt hkr3 hkt3 (fun e0 => hwt e0.symm)))
      -- the reply's links at the block
      obtain ⟨hdet, hn0, hp0⟩ := hRRu w hwR xr hkr hb'
      obtain ⟨-, -, -, -, k4⟩ := Ju.cnW_keeps hWu
      refine WP.spec_mono (J4.pushDonJ3 hAT ht hdT hwR hsC htd hktP hkdP hkwP hkyP rfl hcs hyt hxdn3 rfl rfl
        hctP hcscP hcnP hnqtP hnqdP hya hdet (by rw [(k4 w hwR).2]; exact hn0) (by rw [(k4 w hwR).1]; exact hp0)
        htD) ?_
      rintro ⟨s5, a5⟩ ⟨ha5, hsp5, Lst5, J5⟩
      simp only at ha5
      subst a5
      exact ⟨rfl, _, hsp5, fun _ => ⟨Lst5, J5⟩⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => r.2 = a ∧ ∃ σ',
      Fl4Spec.replyPush (Z := Unit) t.bv d'.bv w.bv true σ3 = ({((), σ')}, False) ∧
      (σ' = σD → ∃ (Lst' : U64 → List U64), JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst' D r.1 a σ'))
    ?_ ?_
  · refine WP.spec_bind (Endp.obj.Tcb.fault_type.spec s3 t) ?_
    rintro i1 rfl
    rw [hty3, if_pos (by unfold fl4_abi.consts.fault.CapFault fl4_abi.consts.fault.NullFault; decide)]
    rcases hg with rfl | rfl
    · simp only [Bool.false_eq_true, ↓reduceIte, eq_self_iff_true, if_true]; exact hPush
    · cases g <;> simp only [Bool.false_eq_true, ↓reduceIte, eq_self_iff_true, if_true] <;> exact hPush
  rintro ⟨s5, a5⟩ ⟨ha5, σ5', hpush, hPσ⟩
  simp only at ha5 hpush hPσ ⊢
  subst a5
  try dsimp only
  have e5 : σ5' = σD := by
    have h := hpush.symm.trans hpushE
    exact congrArg Prod.snd (Set.singleton_injective (congrArg Prod.fst h))
  obtain ⟨Lst5, J5⟩ := hPσ e5
  have J5B := J5.z2.zv.base
  subst e5
  -- the receiver runs (`Inactive` with the donated SC)
  set x4 : Fl4Spec.Tcb := { x3 with tcbSchedContext := some sc.bv } with hx4
  have hk5 : σD.kheap d'.bv = some (.tcb x4) := @pd_kd σP t.bv d'.bv sc.bv w.bv xtP x3 xwP y n
  have hst5 : L.mem s5 (P1.stA d') = sched.TS_INACTIVE := by
    have h := ((J5B.xtop.irelK J5B.ks J5B.buf).1.toN.at_tcb hdT hk5).st
    rw [stA_tStA, P1.ts_inactive]
    exact UScalar.eq_of_val_eq (by rw [h]; rfl)
  have htmD : σD.curTime = σ.curTime := (@pd_tm σP t.bv d'.bv sc.bv w.bv xtP x3 xwP y n).trans
    ((ps_skD (σ := σ3) (t := t.bv) (w := w.bv) (xr := xr3) (xt := xt)).tm.trans SK3.2.1)
  have hkpD : σD.kheap sc.bv = some (.schedContext { { y with scReplies := w.bv :: y.scReplies } with
      scTcb := some d'.bv } n) :=
    @dn_kp (bdSt σP sc.bv w.bv y n xwP) t.bv d'.bv sc.bv xtP x3 { y with scReplies := w.bv :: y.scReplies } n hsd
  have hrelD : RelIfBound σD d'.bv := by
    intro x' scp y' n' hx' hsc' hky' ha' _
    rw [hk5] at hx'; cases hx'
    simp only [x4, Option.some.injEq] at hsc'
    subst hsc'
    rw [hkpD] at hky'
    cases hky'
    have := hrelσ hya
    unfold released at this ⊢
    rw [htmD]; exact this
  refine WP.spec_bind (J5.stsIJ3 hdT (fun h => htD d' h rfl) hk5 rfl .running (by simp [tsCode]) sched.TS_RUNNING
    (by unfold sched.TS_RUNNING; rfl) (fun _ => hrelD)
    (P1.sched.set_thread_state.running_blkI (Es := P1.EH H) s5 d' J5B.blk hdH hst5)) ?_
  rintro s6 ⟨Lst6, J6⟩
  set x6 : Fl4Spec.Tcb := { x4 with tcbState := .running } with hx6
  have hdcD : d'.bv ≠ σD.curThread := by
    rw [show σD.curThread = t.bv from (@pd_ct σP t.bv d'.bv sc.bv w.bv xtP x3 xwP y n).trans hctP]
    exact Ne.symm htd'
  have e6 : stsAct (updK σD d'.bv (.tcb x6)) d'.bv = updK σD d'.bv (.tcb x6) := stsAct_ne hdcD
  have hk6 : (stsAct (updK σD d'.bv (.tcb x6)) d'.bv).kheap d'.bv = some (.tcb x6) := by
    rw [e6]; simp [updK]
  have hnr6 : d'.bv ∉ (stsAct (updK σD d'.bv (.tcb x6)) d'.bv).releaseQueue := by
    rw [e6]
    show d'.bv ∉ σD.releaseQueue
    rw [show σD.releaseQueue = σ.releaseQueue from (@pd_rel σP t.bv d'.bv sc.bv w.bv xtP x3 xwP y n).trans
      ((@ps_rel σ3 t.bv w.bv xr3 xt).trans SK3.1)]
    exact hnqD.2
  have hact6 : ∀ p y' n', x6.tcbSchedContext = some p →
      (stsAct (updK σD d'.bv (.tcb x6)) d'.bv).kheap p = some (.schedContext y' n') → Fl4Spec.scActive y' = true := by
    intro p y' n' hp hy'
    simp only [x6, x4, Option.some.injEq] at hp
    subst hp
    rw [e6] at hy'
    simp only [updK_kheap, Function.update_of_ne hsd] at hy'
    rw [hkpD] at hy'
    cases hy'
    exact hya
  have hti6 : d'.bv ≠ (stsAct (updK σD d'.bv (.tcb x6)) d'.bv).idleThread := by
    rw [e6]
    show d'.bv ≠ σD.idleThread
    rw [show σD.idleThread = σ.idleThread from (@pd_idle σP t.bv d'.bv sc.bv w.bv xtP x3 xwP y n).trans
      ((ps_skD (σ := σ3) (t := t.bv) (w := w.bv) (xr := xr3) (xt := xt)).idle.trans Fr3.sk.idle)]
    exact hid
  have htc6 : d'.bv ≠ (stsAct (updK σD d'.bv (.tcb x6)) d'.bv).curThread := by
    rw [e6]; exact hdcD
  have hspec := sendIpc_faultPush_eq (don := true) hk hkd hde hstd blk badge.bv g gr hg e2 hU hkt3 hkd3 hpushE hk5 (by rw [hft]; simp)
    (t := t.bv)
  refine WP.spec_mono (J6.sendTailJ3 hdT hk6 rfl hnr6 hact6 hti6 htc6) ?_
  rintro ⟨s7, a7⟩ ⟨ha7, σ7, h7, Lst7, J7⟩
  simp only at ha7
  subst ha7
  exact ⟨((), σ7), by rw [hspec, h7]; exact Set.mem_singleton _, ⟨_, _, _, _, _, _, J7⟩⟩

/-- **[W] `ZvFaultPDHyp` discharged** (module docstring). -/
theorem zvFaultPDHyp_of (hAT : P0.ArchTotal arI) : ZvFaultPDHyp (L := L) arI V X AR := by
  intro _ _ _ _ _ _ _ _ _ J3 _ ht _ hkt hrn _ _ _ hft hct hres hti hnq _ _ he _ hk blk badge g gr hg hrepn hxdn
  exact J3.sendFaultPDJ3 hAT ht hkt hrn hft hct hres hti hnq he hk blk badge g gr hg hrepn hxdn

set_option maxHeartbeats 4000000 in
/-- **The `fl4HandleInvocationVF` step for a VCPU cap at `JAtZV3` with no fault-handler premise** (module
docstring; P3/JAtZV3FaultRecv's `JAtZV3.vcpuHandleJ3` with `zvFaultPDHyp_of`). -/
theorem JAtZV3.vcpuHandleJ4 (hK : ARKeep arI AR) (hSy : ZvSyncKeep arI AR)
    (hVA : ZvVirtAgree arI) (hCap : ∀ a', VirtSanEq.CapAgree arI a') (hAT : P0.ArchTotal arI)
    (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (onCore remoteCur : Fl4Spec.ObjRef → Bool)
    (is_call blocking can_donate first_phase : Bool) (cptr : U64)
    {ct : U64} (hct : sched.cur_thread st s = ok ct)
    {info : msginfo.MessageInfo} (hinfo : msg.msg_info st s ct = ok info)
    {mi : Fl4Spec.MessageInfo} (hmi : Fl4Spec.getMessageInfo (Z := Unit) ct.bv σ = ({(mi, σ)}, False))
    {buf : U64} (hbuf : msg.lookup_ipc_buffer st s false ct = ok buf)
    {buffer : Option Fl4Spec.ObjRef}
    (hbuffer : Fl4Spec.lookupIpcBuffer (Z := Unit) false ct.bv σ = ({(buffer, σ)}, False))
    {r2 : core.result.Result (Aeneas.Std.Array obj.Slot 3#usize) error.Fault}
    (hr2 : ipc.lookup_extra_caps st s ct buf info = ok r2)
    {er : Except Fl4Spec.Fault (List (Fl4Spec.Cap × Fl4Spec.CslotPtr))}
    (her : (Fl4Spec.lookupExtraCaps (Z := Unit) ct.bv buffer mi).run σ = ({(er, σ)}, False))
    (hrr : (∃ e exs, r2 = .Ok e ∧ er = .ok exs ∧
        (info.label = fl4_abi.label.X86VCPUEnableIOPort → IoFreshEx (L.mem s) e)) ∨
      (∃ f f', r2 = .Err f ∧ er = .error f'))
    {args : List Fl4Spec.Data} (hmrs : Fl4Spec.getMrs (Z := Unit) ct.bv buffer mi σ = ({(args, σ)}, False))
    (hent : blocking = true → ZvEntry σ ∧ ZvVfh σ)
    (hVc : ∀ r1, cspace.lookup_slot st s ct cptr = ok (.Ok r1) → ∃ p, capV (L.mem s) r1.slot = .Vcpu p)
    (hrun : ZvCtRun σ ct) :
    syscall.handle_invocation st arI s a is_call blocking can_donate first_phase cptr ⦃ res =>
      ∃ y ∈ ((Fl4Spec.fl4HandleInvocationVF (Z := Unit) onCore remoteCur true is_call blocking can_donate first_phase
          (Fl4Spec.toBl cptr.bv)).run σ).1,
        res.1 = .Ok () ∧ y.1 = .ok () ∧ ZvPost (L := L) arI V X AR res.2.1 res.2.2 y.2 ⦄ :=
  J.vcpuHandleJ3 hK hSy hVA hCap hAT (zvFaultPDHyp_of hAT) onCore remoteCur is_call blocking can_donate first_phase
    cptr hct hinfo hmi hbuf hbuffer hr2 her hrr hmrs hent hVc hrun

end

end

end Fl4Proofs.P3
