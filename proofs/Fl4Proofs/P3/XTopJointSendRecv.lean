/-
P3 (DESIGN.md §9), IPC: **`send_ipc` to a waiting receiver at `J`** (toward
XTopJointIpcJ's `JSendRestHyp`).

* `JAtZ.unblockRJ`: XTopJointUnblock's `JAtZ.unblockJ` for an SC whose
  bound thread is in no release queue (not only an `Inactive` one), with the
  frame facts of `refill_unblock_check` (`unblock_result`).
* `JAtZ.sendUnblockJ`: FL4's `unblock_sporadic` (the SC word, the sporadic
  flag, the current SC) of a thread in no release queue against the spec's
  `ifSporadicCurScTestRefillUnblockCheck` of its SC, from `JAtZ` to `JAtZ`.
* `JAtZ.sendSwitchJ`: `possible_switch_to` of a runnable thread in no
  release queue whose SC (if any) is active: `JAtZ.switchJ` (schedulable),
  or nothing on either side without an SC.
* `JAtZ.sendTailJ`: the receiver's tail of `send_ipc` (`unblock_sporadic`,
  `possible_switch_to`) against `specWakeTailE`.
-/
import Fl4Proofs.P3.XTopJointIpcJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section SpecD
open Fl4Spec

/-- The spec's `send_ipc` to a waiting receiver `d` (non-call, the sender
without a fault), a donation asked only where `d` has an SC (so none
happens): `sendIpc_recv_eq` for any `canDonate`. -/
theorem sendIpc_recv_eqD {σ : State Unit} {t e d : ObjRef} {q : List ObjRef}
    (hk : σ.kheap e = some (.endpoint (.recvEP (d :: q)))) {xd : Tcb} (hkd : σ.kheap d = some (.tcb xd))
    (hde : d ≠ e) {e' : ObjRef} {rep : Option ObjRef} {dd : ReceiverPayload}
    (hst : xd.tcbState = .blockedOnReceive e' rep dd) (blk : Bool) (badge : Badge) (g gr don : Bool)
    {σ2 σ3 : State Unit}
    (hT : doIpcTransfer (Z := Unit) t (some e) badge g d (updK σ e (.endpoint (epDeq (.recvEP (d :: q)) d))) =
      ({((), σ2)}, False))
    (hU : NonDet.maybeM (replyUnlinkTcb (Z := Unit) d) rep σ2 = ({((), σ3)}, False))
    {xt3 x3 : Tcb} (hkt3 : σ3.kheap t = some (.tcb xt3)) (hf3 : xt3.tcbFault = none)
    (hkd3 : σ3.kheap d = some (.tcb x3)) (hdon : don = false ∨ x3.tcbSchedContext ≠ none) :
    sendIpc (Z := Unit) blk false badge g gr don t e σ =
      specWakeTailE d (stsAct (updK σ3 d (.tcb { x3 with tcbState := .running })) d) := by
  have hkd1 : (updK σ e (.endpoint (epDeq (.recvEP (d :: q)) d))).kheap d = some (.tcb xd) := by
    simp [hde, hkd]
  have hnd : ¬ (don = true ∧ x3.tcbSchedContext = none) := by
    rintro ⟨h1, h2⟩
    rcases hdon with h | h
    · rw [h] at h1; cases h1
    · exact h h2
  unfold sendIpc
  rw [nd_bind_one (getEndpoint_eq hk)]
  cases blk <;> dsimp only <;>
  · rw [nd_bind_one (tcbEpDequeue_eq hk (by simp [Endpoint.epQueue])), nd_bind_one (getThreadState_eq hkd1), hst]
    dsimp only
    rw [nd_pure_bind', nd_bind_one hT, nd_bind_one hU, nd_bind_one (getTcbObjRef_eq _ hkd3),
      nd_bind_one (threadGet_eq _ hkt3), hf3]
    simp only [Bool.false_eq_true, ne_eq, not_true_eq_false, or_self, ↓reduceIte]
    rw [nd_when_false_bind (by exact hnd), nd_bind_one (Notif.setThreadState_eq _ hkd3)]
    rfl

end SpecD

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 16000000 in
/-- **`unblock_check` at `J`, the SC's thread in no release queue** (module
docstring). -/
theorem JAtZ.unblockRJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hnr : t.bv ∉ σ.releaseQueue)
    {p : U64} (hp : p ∈ Z.C) (hxsc : x.tcbSchedContext = some p.bv) (hpc : p.bv ≠ σ.curSc)
    {y : Fl4Spec.SchedContext} {n : Nat} (hky : σ.kheap p.bv = some (.schedContext y n))
    (hya : Fl4Spec.scActive y = true) :
    sporadic.unblock_check st s p ⦃ s' => ∃ σ', Fl4Spec.refillUnblockCheck (Z := Unit) p.bv σ = ({((), σ')}, False) ∧
      (∀ q, q ≠ p.bv → σ'.kheap q = σ.kheap q) ∧ σ'.curThread = σ.curThread ∧
      σ'.idleThread = σ.idleThread ∧ σ'.releaseQueue = σ.releaseQueue ∧
      (∃ z, σ'.kheap p.bv = some (.schedContext z n) ∧ z.scRefillMax = y.scRefillMax ∧ z.scTcb = y.scTcb) ∧
      ∃ Lst' : U64 → List U64, JAtZ (L := L) arI AR Z H Cs Ac Lst' D s' a σ' ⦄ := by
  have hX := J.xtop
  have hS := hX.fin.1.1.1
  have hR : NtfnStateRel Z.N Z.T (L.mem s) σ := hX.fin.1.1.2.2.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  obtain ⟨xt, hkt, -, -, hsct, -⟩ := hs.tcb t ht
  rw [hk] at hkt; cases hkt
  have h0 : L.mem s (scA t) ≠ 0#u64 := (Notif.optRef_some (hsct.symm.trans hxsc)).1
  have hst : L.mem s (scA t) = p := P1.eq_of_bv (Notif.optRef_some (hsct.symm.trans hxsc)).2
  obtain ⟨y', n', hky', hy'⟩ := hs.scs p hp
  rw [hky] at hky'; cases hky'
  have hmx : (L.rmax s p).val ≠ 0 := hy'.rmax_ne hya
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  obtain ⟨⟨Q1, R1, hq1⟩, hB, hXi, hSc, hSg⟩ := J.blk
  obtain ⟨hiS, -, -⟩ := hXi.2.2.bound t htH h0
  rw [hst] at hiS
  have hiA : p ∈ Ac := (hSc.act _ hiS).2 (fun e => hmx (by rw [e]; rfl))
  have hp0 : p ≠ 0#u64 := fun e => h0 (by rw [hst]; exact e)
  refine WP.spec_mono (WP.spec_and (WP.spec_and (WP.spec_and (unblock_check_refines s σ hS hp hmx)
    (unblock_check_kfoot hS hp hmx))
    (Fl4Proofs.P1.sporadic.unblock_check.all s t p hq1 hB hXi hSc hSg htH hst.symm hp0 hiA))
    (Fl4Proofs.P1.sporadic.unblock_check.kw (Es := P1.EH H) s t p hq1 hB hXi hSc hSg htH hst.symm hp0 hiA)) ?_
  rintro s' ⟨⟨⟨⟨σ', he, hfe, hkv, hS'⟩, hw⟩, hq2, hB2, hX2, hS2, hSg2, -⟩, hfoot⟩
  have mem : ((), σ') ∈ (Fl4Spec.refillUnblockCheck (Z := Unit) p.bv σ).1 := by rw [he]; exact Set.mem_singleton _
  have hne : y.scRefills ≠ [] := J.inv.ne _ y n hky hya
  have hF : (∀ q, q ≠ p.bv → σ'.kheap q = σ.kheap q) ∧ σ'.curThread = σ.curThread ∧ σ'.curSc = σ.curSc ∧
      σ'.curTime = σ.curTime ∧ σ'.consumedTime = σ.consumedTime ∧ σ'.releaseQueue = σ.releaseQueue ∧
      σ'.idleThread = σ.idleThread ∧ σ'.schedulerAction = σ.schedulerAction ∧
      ∃ z, σ'.kheap p.bv = some (.schedContext z n) ∧ z.scRefillMax = y.scRefillMax ∧ z.scTcb = y.scTcb := by
    rcases unblock_result hky hne mem with ⟨rfl, -⟩ | ⟨z, rfl, -, -, hz, -⟩
    · exact ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, y, hky, rfl, rfl⟩
    · exact ⟨fun q hq => by simp [updK, hq], rfl, rfl, rfl, rfl, rfl, rfl, rfl, z, by simp [updK],
        by rw [hz], by rw [hz]⟩
  obtain ⟨hkp, e_ct, e_csc, e_tm, e_cons, e_rel, e_idle, e_act, z, hkz, hzm, hzt⟩ := hF
  refine ⟨σ', he, hkp, e_ct, e_idle, e_rel, ⟨z, hkz, hzm, hzt⟩, ?_⟩
  -- the spec frame
  have hK0 : ScTKw (fun _ => False) σ σ' := nkt_refillUnblockCheck p.bv σ _ mem
  have hK : ScTKw (fun q => q = t.bv) σ σ' := hK0.ofFalse
  have hL : LK (fun _ => False) σ σ' := lkm_refillUnblockCheck p.bv σ _ mem
  have hFK : FK σ σ' := ⟨e_csc, e_idle, hK0.isc⟩
  have hsok : SOK (true, true) σ σ' := pres_refillUnblockCheck (f := (true, true)) p.bv σ _ mem
  have hBK : BK σ σ' := bkm_of (nkt_refillUnblockCheck _) (MaxK.mk_refillUnblockCheck' _) σ _ mem
  have hwT := WritesIn.tfoot_of_kfoot hw
  have hR' : NtfnStateRel Z.N Z.T (L.mem s') σ' := hR.frame hS.placed hfe hkv
  have hX' : XTopAt (L := L) AR Z s' a σ' := xtop_sc_step hX J.ip J.nk hwT hK hS' hR' id
  have hN' : NSC Z.N Z.C σ' := nsc_of_lk J.nsc hK hL
  -- the invariant: the only thread bound to `p` is `t`, in no release queue
  have hI' : Inv σ' := by
    refine J.inv.unblock hky hne (fun _ _ u hu xu hku hsu => ?_) mem
    obtain ⟨y1, n1, hk1, hyt1⟩ := J.inv.back u xu p.bv hku hsu
    obtain ⟨y2, n2, hk2, hyt2⟩ := J.inv.back t.bv x p.bv hk hxsc
    rw [hk1] at hk2; cases hk2
    have hut : u = t.bv := Option.some.inj (hyt1.symm.trans hyt2)
    subst hut
    exact hnr hu
  obtain ⟨-, hY', hM', ⟨Lst', hCR', hRF'⟩, hRP', -⟩ :=
    ScAll.of_k hS J.rp J.yld J.mcp J.call J.rfree ⟨⟨hS', hR', hN', hI'⟩, hw, hsok⟩
  have hkcs : σ'.kheap σ'.curSc = σ.kheap σ.curSc := by rw [e_csc]; exact hkp _ (Ne.symm hpc)
  have htk : ∀ q xq, σ'.kheap q = some (.tcb xq) → σ.kheap q = some (.tcb xq) := by
    intro q xq h
    by_cases e : q = p.bv
    · rw [e, hkz] at h; cases h
    · rwa [hkp q e] at h
  have htk' : ∀ q xq, σ.kheap q = some (.tcb xq) → σ'.kheap q = some (.tcb xq) := by
    intro q xq h
    by_cases e : q = p.bv
    · rw [e, hky] at h; cases h
    · rwa [hkp q e]
  have hC' : σ'.schedulerAction = .chooseNewThread ∨ CurInv σ' := by
    rcases J.cur with e | hC
    · left; rw [e_act]; exact e
    · right
      obtain ⟨xc, hkc, hcs, hnb⟩ := hC.tcb
      refine ⟨⟨xc, by rw [e_ct]; exact htk' _ _ hkc, by rw [e_csc]; exact hcs, hnb⟩, ?_, ?_, ?_⟩
      · rw [hkcs]; exact hC.sc
      · intro hne' y2 n2 hy; rw [hkcs] at hy; rw [e_csc, hK0.isc] at hne'; exact hC.active hne' y2 n2 hy
      · rw [e_ct, e_rel]; exact hC.notRel
  have hown' : CurOwnW Z.T Z.C σ' := by
    rcases J.own with ⟨u, hu, xu, hku, hxs, hown, hnr'⟩ | ⟨hcs, hun⟩
    · exact Or.inl ⟨u, hu, xu, htk' _ _ hku, by rw [e_csc]; exact hxs,
        fun y1 n1 hy => hown y1 n1 (by rw [← hkcs]; exact hy), by rw [e_cons, e_rel]; exact hnr'⟩
    · exact Or.inr ⟨by rw [e_csc]; exact hcs, fun y1 n1 hy => hun y1 n1 (by rw [← hkcs]; exact hy)⟩
  have hoff : OffOK σ' := by
    intro h0' y1 n1 hy ha
    rw [e_cons] at h0' ⊢; rw [e_tm]; rw [hkcs] at hy; rw [e_csc, hK0.isc] at ha
    exact J.off h0' y1 n1 hy ha
  have hAI : ActIdle σ' := J.act.unblock hky hne mem
  have hcr : CurRunM σ' := by
    rcases J.curRun with h | h
    · left; rw [e_act]; exact h
    · right
      rcases h with h | h
      · left; intro y1 hy; rw [e_ct] at hy; exact h y1 (htk _ _ hy)
      · right; rw [e_ct, e_idle]; exact h
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := fun q hq =>
    J.deadP_sc_stepQ hX' hwT hK0 (fun _ hp => hp.elim) hL hFK hAI.1 hY' ((hsok.ykeep rfl).dk q.bv) (fun h => h) (J.jcov.dead q hq)
  have hDbg := J.kw_dbg hfoot
  exact ⟨Lst', J.sc_frame hwT hK hX' hCR' hRF' hY' hM' (J.sc_buf hwT hK) hRP' (J.sc_apart hwT hK)
    (J.sc_jpl hwT hK (J.idleW_keep hX'.fin.1.1.1 hFK.2.1 hFK.2.2).2) (J.sc_jcov hwT hdead (fun q hq hn => absurd hq hn) (J.idleW_keep hX'.fin.1.1.1 hFK.2.1 hFK.2.2))
    (J.sc_kern hwT hK hFK hX' hDbg fun _ h => h) (J.sc_utc hwT hK hDbg) hN' hI' hC' hown' hoff hAI
    (J.bsa.bk hBK hsok) hcr ⟨⟨Q1, R1, hq2⟩, hB2, hX2, hS2, hSg2⟩⟩

/-- What `sendUnblockJ` keeps of the spec's state. -/
def UnblockKeep (σ σ' : Fl4Spec.State Unit) : Prop :=
  (∀ q xq, σ.kheap q = some (.tcb xq) → σ'.kheap q = some (.tcb xq)) ∧ σ'.curThread = σ.curThread ∧
    σ'.idleThread = σ.idleThread ∧ σ'.releaseQueue = σ.releaseQueue ∧
    (∀ q y n, σ'.kheap q = some (.schedContext y n) → ∃ y0, σ.kheap q = some (.schedContext y0 n) ∧
      y.scRefillMax = y0.scRefillMax ∧ y.scTcb = y0.scTcb)

set_option maxHeartbeats 8000000 in
/-- **`unblock_sporadic` at `J`** (module docstring). -/
theorem JAtZ.sendUnblockJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hnr : t.bv ∉ σ.releaseQueue) :
    endpoint.unblock_sporadic st s t ⦃ s' => ∃ (σ' : Fl4Spec.State Unit) (Lst' : U64 → List U64),
      Fl4Spec.ifSporadicCurScTestRefillUnblockCheck (Z := Unit) x.tcbSchedContext σ = ({((), σ')}, False) ∧
      JAtZ (L := L) arI AR Z H Cs Ac Lst' D s' a σ' ∧ UnblockKeep σ σ' ⦄ := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc0, hs⟩ := hS.lists
  obtain ⟨xt, hkt, -, -, hsct, -⟩ := hs.tcb t ht
  rw [hk] at hkt; cases hkt
  have skip : Fl4Spec.ifSporadicCurScTestRefillUnblockCheck (Z := Unit) (optRef (L.mem s (scA t))) σ =
      ({((), σ)}, False) → ∃ (σ' : Fl4Spec.State Unit) (Lst' : U64 → List U64),
        Fl4Spec.ifSporadicCurScTestRefillUnblockCheck (Z := Unit) x.tcbSchedContext σ = ({((), σ')}, False) ∧
        JAtZ (L := L) arI AR Z H Cs Ac Lst' D s a σ' ∧ UnblockKeep σ σ' := fun h =>
    ⟨σ, Lst, by rw [hsct]; exact h, J, fun _ _ h => h, rfl, rfl, rfl, fun _ y _ h => ⟨y, h, rfl, rfl⟩⟩
  unfold endpoint.unblock_sporadic
  step with Fl4Proofs.P1.obj.Tcb.sc.spec as ⟨i2, hi2⟩
  step with sporadic.sc_sporadic.spec' as ⟨b, b_post⟩
  subst hi2
  by_cases h0 : L.mem s (scA t) = 0#u64
  · have hb : b = false := by rw [b_post]; simp [h0]
    simp only [hb, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact skip (by rw [h0, optRef_zero]; rfl)
  have hscC := hs.scMem t ht h0
  obtain ⟨y, n, hky, hy⟩ := hs.scs _ hscC
  have hsp : (y.scSporadic = true) ↔ L.mem s (scW (L.mem s (scA t)) 64#u64) ≠ 0#u64 := by
    rw [hy.sporadic]; simp
  have hif : Fl4Spec.ifSporadicCurScTestRefillUnblockCheck (Z := Unit) (optRef (L.mem s (scA t))) σ =
      (if y.scSporadic = true ∧ (L.mem s (scA t)).bv ≠ σ.curSc then
        Fl4Spec.refillUnblockCheck (L.mem s (scA t)).bv σ else ({((), σ)}, False)) := by
    rw [Notif.optRef_ne h0]
    unfold Fl4Spec.ifSporadicCurScTestRefillUnblockCheck Fl4Spec.ifCondRefillUnblockCheck
    simp only [Fl4Spec.NonDet.maybeM]
    rw [nd_bind_one (getSchedContext_eq hky), nd_gets_bind, nd_pure_bind']
    simp only [Fl4Spec.NonDet.when]
    by_cases e : y.scSporadic = true ∧ (L.mem s (scA t)).bv ≠ σ.curSc
    · simp only [e, ne_eq, not_false_eq_true, forall_const, and_self, ↓reduceIte, Option.some.injEq,
        Bool.false_eq_true, IsEmpty.forall_iff]
    · simp only [ne_eq, forall_const, ↓reduceIte, Option.some.injEq]
      rw [ite_f (c := y.scSporadic = true ∧ ¬ (L.mem s (scA t)).bv = σ.curSc) (by simpa only [ne_eq] using e),
        ite_f (c := y.scSporadic = true ∧ ¬ (L.mem s (scA t)).bv = σ.curSc) (by simpa only [ne_eq] using e)]
      rfl
  by_cases hsp' : L.mem s (scW (L.mem s (scA t)) 64#u64) ≠ 0#u64
  swap
  · have hb : b = false := by rw [b_post]; simp [h0]; simpa using hsp'
    simp only [hb, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact skip (by rw [hif, ite_f (fun h => hsp' (hsp.1 h.1))])
  have hb : b = true := by rw [b_post]; simp [h0, hsp']
  simp only [hb, ↓reduceIte]
  step with sched.cur_sc.spec' as ⟨s1, s1_post⟩
  rw [sc_ne_eq]
  simp only [bind_ok]
  rw [s1_post, hc0.cur]
  by_cases e : L.mem s (scA t) = nodeW st s Z.c layout.node.CUR_SC
  · simp only [e, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact skip (by rw [hif, ite_f]; rw [e, ← hs.curSc]; simp)
  · simp only [e, ne_eq, not_false_eq_true, decide_true, ↓reduceIte]
    have hpc : (L.mem s (scA t)).bv ≠ σ.curSc := by rw [hs.curSc]; exact bv_ne e
    have hxsc : x.tcbSchedContext = some (L.mem s (scA t)).bv := by
      rw [hsct, Notif.optRef_ne h0]
    have hya : Fl4Spec.scActive y = true := hy.active_of_rmax (hy.spor hsp')
    refine WP.spec_mono (J.unblockRJ ht hk hnr hscC hxsc hpc hky hya) ?_
    rintro s' ⟨σ', he, hkp, hct, hid, hrl, ⟨z, hkz, hzm, hzt⟩, Lst', J'⟩
    refine ⟨σ', Lst', ?_, J', fun q xq hq => ?_, hct, hid, hrl, fun q y' n' hq => ?_⟩
    · rw [hsct, hif, ite_t ⟨hsp.2 hsp', hpc⟩, he]
    · by_cases eq : q = (L.mem s (scA t)).bv
      · rw [eq, hky] at hq; cases hq
      · rw [hkp q eq]; exact hq
    · by_cases eq : q = (L.mem s (scA t)).bv
      · rw [eq, hkz] at hq; cases hq
        exact ⟨y, by rw [eq]; exact hky, hzm, hzt⟩
      · rw [hkp q eq] at hq; exact ⟨y', hq, rfl, rfl⟩

set_option maxHeartbeats 4000000 in
/-- **`possible_switch_to` at `J`** of a runnable thread in no release queue
with an active SC or none (module docstring). -/
theorem JAtZ.sendSwitchJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hrun : Fl4Spec.runnable x.tcbState = true)
    (hnr : t.bv ∉ σ.releaseQueue)
    (hact : ∀ p y n, x.tcbSchedContext = some p → σ.kheap p = some (.schedContext y n) → Fl4Spec.scActive y = true)
    (hti : t.bv ≠ σ.idleThread) (htc : t.bv ≠ σ.curThread) :
    sched.possible_switch_to st s t ⦃ s' => ∃ σ', Fl4Spec.possibleSwitchTo (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
      ∃ Lst' : U64 → List U64, JAtZ (L := L) arI AR Z H Cs Ac Lst' D s' a σ' ⦄ := by
  cases hsc : x.tcbSchedContext with
  | some p =>
    obtain ⟨y, n, hky, -⟩ := J.inv.back _ _ _ hk hsc
    exact J.switchJ ht hti htc (schedulable_of hk hsc hrun hky (hact p y n hsc hky) hnr)
  | none =>
    have hS := J.xtop.fin.1.1.1
    obtain ⟨Q, R0, hc0, hs⟩ := hS.lists
    obtain ⟨xt, hkt, -, -, hsct, -⟩ := hs.tcb t ht
    rw [hk] at hkt; cases hkt
    have h0 : L.mem s (scA t) = 0#u64 := by
      by_contra h0
      rw [Notif.optRef_ne h0] at hsct
      rw [hsc] at hsct; cases hsct
    unfold sched.possible_switch_to
    step with Fl4Proofs.P1.obj.Tcb.sc.spec as ⟨i, hi⟩
    rw [hi, h0]
    simp only [↓reduceIte, WP.spec_ok]
    refine ⟨σ, ?_, Lst, J⟩
    unfold Fl4Spec.possibleSwitchTo Fl4Spec.getTcbObjRef
    rw [nd_bind_one (threadGet_eq _ hk)]
    simp only [hsc, nd_gets_bind]
    rw [nd_when_false (by simp)]
    rfl

set_option maxHeartbeats 4000000 in
/-- **The receiver's tail of `send_ipc` at `J`** (module docstring). -/
theorem JAtZ.sendTailJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hrun : Fl4Spec.runnable x.tcbState = true)
    (hnr : t.bv ∉ σ.releaseQueue)
    (hact : ∀ p y n, x.tcbSchedContext = some p → σ.kheap p = some (.schedContext y n) → Fl4Spec.scActive y = true)
    (hti : t.bv ≠ σ.idleThread) (htc : t.bv ≠ σ.curThread) :
    (do
      let s6 ← endpoint.unblock_sporadic st s t
      let s7 ← sched.possible_switch_to st s6 t
      ok (s7, a)) ⦃ r => r.2 = a ∧ ∃ σ', Endp.specWakeTailE t.bv σ = ({((), σ')}, False) ∧
        ∃ Lst' : U64 → List U64, JAtZ (L := L) arI AR Z H Cs Ac Lst' D r.1 a σ' ⦄ := by
  refine WP.spec_bind (J.sendUnblockJ ht hk hnr) ?_
  rintro s6 ⟨σ6, Lst6, hU, J6, hkt6, hct6, hid6, hrl6, hsc6⟩
  have hk6 := hkt6 _ _ hk
  have hact6 : ∀ p y n, x.tcbSchedContext = some p → σ6.kheap p = some (.schedContext y n) →
      Fl4Spec.scActive y = true := by
    intro p y n hp hy
    obtain ⟨y0, hy0, hm, -⟩ := hsc6 p y n hy
    have := hact p y0 n hp hy0
    simp only [Fl4Spec.scActive] at this ⊢
    rw [hm]; exact this
  refine WP.spec_bind (J6.sendSwitchJ ht hk6 hrun (by rw [hrl6]; exact hnr) hact6 (by rw [hid6]; exact hti)
    (by rw [hct6]; exact htc)) ?_
  rintro s7 ⟨σ7, h7, Lst7, J7⟩
  refine (WP.spec_ok _).2 ⟨rfl, σ7, ?_, Lst7, J7⟩
  unfold Endp.specWakeTailE Fl4Spec.getTcbObjRef
  rw [nd_bind_one (threadGet_eq _ hk), nd_bind_one hU, h7]


/-! ## The transfer's frame helpers -/

theorem ipcBufCapOK_epStep {σ σ' : Fl4Spec.State Unit} (h : Endp.IpcBufCapOK σ) (hs : EpStep σ σ') :
    Endp.IpcBufCapOK σ' := by
  intro t x' hx' dev p R mt vms md hf hR
  obtain ⟨-, -, hk⟩ := hs
  have hx : ∃ x, σ.kheap t = some (.tcb x) ∧ x.tcbIpcframe = x'.tcbIpcframe ∧ x.tcbIpcBuffer = x'.tcbIpcBuffer := by
    rcases hk t with e | ⟨a, b, h1, h2⟩ | ⟨a, b, h1, h2, -⟩ | ⟨a, b, h1, h2, e⟩
    · exact ⟨x', by rw [← e]; exact hx', rfl, rfl⟩
    · rw [hx'] at h2; cases h2
    · rw [hx'] at h2; cases h2
    · have hb : x' = b := by rw [hx'] at h2; exact Fl4Spec.KernelObject.tcb.inj (Option.some.inj h2)
      subst hb
      exact ⟨a, h1, by rw [e], by rw [e]⟩
  obtain ⟨x, hx, e1, e2⟩ := hx
  obtain ⟨h1, h2, h3, h4, h5⟩ := h t x hx dev p R mt vms md (by rw [e1]; exact hf) hR
  refine ⟨h1, h2, ?_, by rw [← e2]; exact h4, h5⟩
  rcases hk p with e | ⟨a, b, h1', -⟩ | ⟨a, b, h1', -, -⟩ | ⟨a, b, h1', -, -⟩
  · rw [e]; exact h3
  · rw [h3] at h1'; cases h1'
  · rw [h3] at h1'; cases h1'
  · rw [h3] at h1'; cases h1'

theorem ipcBufCapOK_of_kheap {σ σ' : Fl4Spec.State Unit} (h : Endp.IpcBufCapOK σ) (hk : σ'.kheap = σ.kheap) :
    Endp.IpcBufCapOK σ' := by
  unfold Endp.IpcBufCapOK at *; rw [hk]; exact h

/-- `EpHyps` with `IpcBufCapOK` carried along (an `EpStep` keeps the TCBs'
buffer fields and the data pages). -/
theorem epHyps_buf {T E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {SR : S → Fl4Spec.State Unit → Prop}
    (hH : EpHyps st T E R B SR) : EpHyps st T E R B (fun s σ => SR s σ ∧ Endp.IpcBufCapOK σ) :=
  ⟨fun s s' σ σ' h hw hs => ⟨hH.stable s s' σ σ' h.1 hw hs, ipcBufCapOK_epStep h.2 hs⟩,
   fun s σ t hR hS ht => WP.spec_mono (hH.scheduleTcb s σ t hR hS.1 ht) fun _ ⟨h1, h2⟩ =>
     ⟨h1, h2, ipcBufCapOK_of_kheap hS.2 (stsAct_kheap σ t.bv)⟩⟩

/-- `EpBufHyps` for `SRS (SRT … SRE)` with `IpcBufCapOK` carried along. -/
theorem epBufHyps_buf {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)}
    {c : U64} :
    EpBufHyps st T E R B (fun s σ => SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c)) s σ ∧
      Endp.IpcBufCapOK σ) :=
  ⟨fun s σ t x b _ hS _ hk => by
    obtain ⟨⟨G, hB⟩, -⟩ := hS.1.1.1
    exact lookup_buf_rel s σ hB.2.1.1 hB.2.1.2.1 (Ipc.RelTopB.tcbT hB hk) hk hS.2 b⟩

theorem copy_mrs_loop0_rg {T : Set U64} (hT : P1.TcbPlaced T) {s0 s : S} {snd rcv n i : U64} (hr : rcv ∈ T)
    (h : P1.WritesIn st s0 s (XferRegW T ∅)) :
    msg.copy_mrs_loop0 st s snd rcv n i ⦃ r => P1.WritesIn st s0 r.1 (XferRegW T ∅) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold msg.copy_mrs_loop0
  apply loop.spec_decr_nat (measure := fun y => 4 - y.2.val)
    (inv := fun y => P1.WritesIn st s0 y.1 (XferRegW T ∅))
  · rintro ⟨s1, i1⟩ h1
    simp only at h1
    dsimp only
    unfold msg.copy_mrs_loop0.body
    split
    · split
      · rename_i _ hi
        have hi' : i1.val < 4 := by simpa [msg.N_MSG_REGISTERS] using hi
        refine WP.spec_bind (msg.msg_register.lt i1) fun rg hrg => ?_
        refine WP.spec_bind (P0.obj.Tcb.reg.p0 st snd s1 rg hS) fun v _ => ?_
        refine WP.spec_bind (obj.Tcb.set_reg.rg (v := v) (s := s1) hT hr hrg) fun s2 w2 => ?_
        step as ⟨i2, hi2⟩
        exact ⟨rg_trans h1 w2, by first | omega | (dsimp only; omega)⟩
      · exact (WP.spec_ok _).2 h1
    · exact (WP.spec_ok _).2 h1
  · exact h

/-- **`do_ipc_transfer`'s footprint, a receiver without a buffer and a sender
without a fault**: the receiver's registers only. -/
theorem do_ipc_transfer_rg {T : Set U64} (hT : P1.TcbPlaced T) {snd rcv : U64} (hr : rcv ∈ T) (s : S) (a : A)
    (ep badge : U64) (grant : Bool)
    (hb : msg.lookup_ipc_buffer st s true rcv ⦃ w => w = 0#u64 ⦄) (hf : L.mem s (tFaultA snd) = 0#u64) :
    ipc.do_ipc_transfer st arI s a snd ep badge grant rcv ⦃ s' => P1.WritesIn st s s' (XferRegW T ∅) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold ipc.do_ipc_transfer
  refine WP.spec_bind hb ?_
  rintro rb rfl
  refine WP.spec_bind (obj.Tcb.fault_type.spec s snd) ?_
  rintro ft rfl
  rw [hf, if_pos (by unfold fl4_abi.consts.fault.NullFault; rfl)]
  refine WP.spec_bind (P0.msg.lookup_ipc_buffer.p0 st s false snd hS) fun sb _ => ?_
  unfold ipc.do_normal_transfer
  refine WP.spec_bind (P0.msg.msg_info.p0 st s snd hS) fun tag _ => ?_
  refine WP.spec_bind (Pₘ := fun _ => True) ?_ fun extra _ => ?_
  · split
    · refine WP.spec_bind (P0.ipc.lookup_extra_caps.p0 st s snd sb tag hS) fun r _ => ?_
      rcases r with e | _ <;> exact (WP.spec_ok _).2 trivial
    · exact (WP.spec_ok _).2 trivial
  refine WP.spec_bind (Pₘ := fun r : U64 × S => P1.WritesIn st s r.2 (XferRegW T ∅)) ?_ ?_
  · unfold msg.copy_mrs
    refine WP.spec_bind (copy_mrs_loop0_rg hT hr (P1.WritesIn.refl s _)) ?_
    rintro ⟨s1, i⟩ h1
    first | exact (WP.spec_ok _).2 h1 | (simp only [↓reduceIte, WP.spec_ok]; exact h1) | (simp; exact h1)
  rintro ⟨n, s1⟩ h1
  simp only at h1
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (Pₘ := fun r : msginfo.MessageInfo × S => P1.WritesIn st s r.2 (XferRegW T ∅)) ?_ ?_
  · unfold ipc.transfer_caps
    refine WP.spec_bind (P0.msginfo.MessageInfo.new.p0 _ _ _ _) fun out _ => ?_
    step as ⟨sl0, hsl0⟩
    step as ⟨b, hb0⟩
    split <;> first | exact (WP.spec_ok _).2 h1 | (rw [if_pos rfl]; exact (WP.spec_ok _).2 h1)
  rintro ⟨out2, s2⟩ h2
  simp only at h2
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (Pₘ := fun s3 => P1.WritesIn st s s3 (XferRegW T ∅)) ?_
    fun s3 h3 => WP.spec_mono (obj.Tcb.set_reg.rg (s := s3) (v := badge) hT hr
      (by simp [layout.reg.BADGE, layout.reg.RDI])) fun s4 w4 => rg_trans h3 w4
  unfold msg.set_msg_info
  exact WP.spec_bind (P0.msginfo.MessageInfo.to_word.p0 _) fun w _ =>
    WP.spec_mono (obj.Tcb.set_reg.rg (v := w) (s := s2) hT hr (by simp [layout.reg.MSG_INFO, layout.reg.RSI]))
      fun s4 w4 => rg_trans h2 w4

/-- `CnW` back to an earlier state with the same kernel base and SC sizes. -/
theorem cnW_back {T N C E R : Set U64} {c : U64} {s s' : S} {σ σ' : Fl4Spec.State Unit} (hk : L.ksb s' = L.ksb s)
    (hz : SzKeepC C σ σ') {b : U64} (h : CnW (st := st) T N C E R c s' σ' b) : CnW (st := st) T N C E R c s σ b :=
  h.elim (fun h => Or.inl (FinW.back hk hz h)) Or.inr

/-- A thread other than the current one set: no reschedule. -/
theorem stsAct_ne {σ : Fl4Spec.State Unit} {t : Fl4Spec.ObjRef} (h : t ≠ σ.curThread) : Notif.stsAct σ t = σ := by
  unfold Notif.stsAct; rw [if_neg (fun h' => h h'.1)]

/-- A bound receive-blocked or inactive thread set `Running`. -/
theorem CFr.stsRun {r t : Fl4Spec.ObjRef} {σ : Fl4Spec.State Unit} {y : Fl4Spec.Tcb} (hk : σ.kheap t = some (.tcb y))
    (hrb : RbIn y.tcbState) :
    CFr r t σ (Notif.stsAct (Notif.updK σ t (.tcb { y with tcbState := .running })) t) :=
  (CFr.upd hk (Or.inl ⟨y, .running, y.tcbBoundNotification, y.tcbFault, y.tcbArch, rfl, rfl,
    Or.inr ⟨Or.inl rfl, rfl, hrb, Or.inr (Or.inl rfl)⟩⟩)).trans (CFr.sts _ _ _ _)

/-- `IK t` across an update of `t`'s own TCB keeping its SC. -/
theorem IK.updSelf {t : Fl4Spec.ObjRef} {σ : Fl4Spec.State Unit} {x y : Fl4Spec.Tcb} (hk : σ.kheap t = some (.tcb x))
    (h1 : y.tcbSchedContext = x.tcbSchedContext) : IK t σ (Notif.updK σ t (.tcb y)) :=
  IK.upd hk ⟨fun x' e => by cases e; exact ⟨y, rfl, h1, fun h => absurd rfl h, fun h => absurd rfl h⟩, fun _ _ e => (by cases e),
    fun _ e => (by cases e), fun _ _ => ⟨x, rfl⟩, fun _ _ e => (by cases e), fun _ e => by cases e⟩

/-- `IK t` across an update of an endpoint or a reply. -/
theorem IK.updOther {t p : Fl4Spec.ObjRef} {σ : Fl4Spec.State Unit} {o o' : Fl4Spec.KernelObject}
    (hk : σ.kheap p = some o)
    (ho : ∀ o0, o0 = o ∨ o0 = o' → (∀ x, o0 ≠ .tcb x) ∧ (∀ y n, o0 ≠ .schedContext y n) ∧ (∀ x, o0 ≠ .notification x)) :
    IK t σ (Notif.updK σ p o') :=
  IK.upd hk (IKObj.other ho)

theorem IK.sts (t : Fl4Spec.ObjRef) (σ : Fl4Spec.State Unit) (u : Fl4Spec.ObjRef) : IK t σ (Notif.stsAct σ u) :=
  IK.of_eq (stsAct_kheap σ u) (by unfold Notif.stsAct; split <;> rfl) (by unfold Notif.stsAct; split <;> rfl)
    (by unfold Notif.stsAct; split <;> rfl)


theorem xferTcb_eqA (xr xs : Fl4Spec.Tcb) (b : Fl4Spec.Badge) :
    xferTcb xr xs b = { xr with tcbArch := (xferTcb xr xs b).tcbArch } := by
  simp only [Endp.xferTcb]; rw [Endp.copyRegsTcb_other]; rfl

set_option maxHeartbeats 64000000 in
/-- **`send_ipc` to a waiting receiver at `J`, without a call, a donation
(`can_donate` only toward a receiver with an SC, `hdon`: then neither side
donates), a fault, a receive buffer or granted caps** (module docstring): FL4's dequeue,
transfer, reply unlink and `Running` on `IRel` with the footprint `CnW`
(`ep_dequeue_c`, `do_ipc_transfer_regs` with `IpcBufCapOK` carried,
`reply_unlink_c`, `set_thread_state_c`), P1's `BlkOK` through the
receiver's hole (`ep_dequeue.inv`, `xfer_all`, `reply_unlink.inv`,
`sts_all`) and its footprint `KW`, the spec's frame `CFr` (the receiver
woken as a cancelled receive: its TCB from receive-blocked to `Running`
with a new user context, the endpoint's queue shrunk, its reply unbound),
`Inv` by `InvBut.ik`; `JAtZ` by ScSignalDonJ's `JAtZ.wake_postD`; then the
tail `JAtZ.sendTailJ`; the spec's outcome `sendIpc_recv_eqD`. -/
theorem JAtZ.sendRecvJ0 (hZ : XferHZ L AR Z) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hrs : xt.tcbState = .restart) (hft : xt.tcbFault = none) (hct : σ.curThread = t.bv)
    {e d : U64} (he : e ∈ Z.E) {q : List Fl4Spec.ObjRef}
    (hk : σ.kheap e.bv = some (.endpoint (.recvEP (d.bv :: q))))
    (hrb : ∀ xd, σ.kheap d.bv = some (.tcb xd) → Endp.ipcBufOf true xd = none)
    (blk : Bool) (badge : U64) (g gr don : Bool)
    (hcaps : g = false ∨ Endp.ipcBufOf false xt = none ∨
      Fl4Spec.unat (Fl4Spec.dataToMessageInfo (xt.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miExtraCaps = 0)
    (hdon : don = false ∨ ∀ xd, σ.kheap d.bv = some (.tcb xd) → xd.tcbSchedContext ≠ none) :
    endpoint.send_ipc st arI s a blk false badge g gr don t e ⦃ r =>
      ∃ z ∈ (Fl4Spec.sendIpc (Z := Unit) blk false badge.bv g gr don t.bv e.bv σ).1,
        JAt (L := L) arI AR r.1 r.2 z.2 ⦄ := by
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
  have hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4 := by rw [hrs]; decide
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
  have SK1 : SKeep σ σ1 := SKeep.updK (p := e.bv) (o := .endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) (fun y h => by cases h) (fun _ _ h => by cases h)
  have hOK1 : Endp.IpcBufCapOK σ1 := ipcBufCapOK_epStep (hZ Z s a σ rfl J.xtop).1 (EpStep.ep hk)
  -- the transfer
  have hHB := epHyps_buf (hH.epHyps hP0)
  have hBf := epBufHyps_buf (st := st) (th := Z.th) (cr := σ.archState.x64CurrentCr3) (N := Z.N) (T := Z.T)
    (C := Z.C) (E := Z.E) (R := Z.R) (B := Z.B) (c := Z.c)
  have hlk : msg.lookup_ipc_buffer st s1 true d' ⦃ w => w = 0#u64 ⦄ :=
    WP.spec_mono (hBf.lookup s1 σ1 d' xd true hR1 ⟨hS1.1, hOK1⟩ hdT hkd1) fun w hw => hw.2 (hrb xd hkd)
  have hf1 : L.mem s1 (tFaultA t) = 0#u64 := (hR1.at_tcb ht hkt1).fault0.2 hft
  refine WP.spec_bind (WP.spec_and (do_ipc_transfer_regs hHB hBf hP s1 a σ1 hR1 ⟨hS1.1, hOK1⟩ ht hdT htd hkt1
    hkd1 hft (hrb xd hkd) e badge g hcaps) (do_ipc_transfer_rg (arI := arI) hTP hdH s1 a e badge g hlk hf1)) ?_
  rintro s2 ⟨⟨e2, hR2, hS2, hA2⟩, w2⟩
  set σ2 := Notif.updK σ1 d'.bv (.tcb (xferTcb xd xt badge.bv)) with hσ2
  have hkd2 : σ2.kheap d'.bv = some (.tcb (xferTcb xd xt badge.bv)) := by simp [σ2]
  have hkt2 : σ2.kheap t.bv = some (.tcb xt) := by simp [σ2, htd', hkt1]
  have hst2' : (xferTcb xd xt badge.bv).tcbState = .blockedOnReceive e.bv rep dd := by rw [xferTcb_state, hstd]
  have hxsc : (xferTcb xd xt badge.bv).tcbSchedContext = xd.tcbSchedContext := by rw [xferTcb_eqA]
  have hN2 := ntfn_lift_rcv hP0.toC hS1.2 hR2 hdT (hA2.mono fun _ h => h.1) (fun p hp => by simp [σ2, hp])
    hkd1 hkd2 (xferTcb_state _ _ _)
  have hS2' : SRN st Z.N Z.T (SRS st Z.T (SRT st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c
      (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c))) s2 σ2 := ⟨hS2.1, hN2⟩
  have hk1e2 : σ2.kheap e.bv = some (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) := by
    simp [σ2, Ne.symm hde, hk1e]
  have hq2 : ∀ e'' ∈ Z.E, ∀ z, σ2.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue := by
    intro e'' he'' z hz
    have hne : d'.bv ≠ e''.bv := by intro h; rw [← h, hkd2] at hz; cases hz
    exact hq1 e'' he'' z (by simpa [σ2, Ne.symm hne] using hz)
  have hrw : L.mem s2 (tReplyA d') = L.mem s (tReplyA d') := by
    rw [hA2 _ (a_reply hda).1 ?_, hA1 _ (a_reply hda).1 ⟨d', hdT, (a_reply hda).2⟩]
    rintro ⟨r', hr'⟩
    rw [val_reply hda, regA_val hda (regIdx_lt r')] at hr'; have := regIdx_lt r'; omega
  have hW2 : P1.WritesIn st s s2 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ) := hW1.trans1 (w2.mono fun b hb => by
    rcases hb with ⟨y, hy, K, h1', h2', -, eb⟩ | hb
    · have hyT : y ∈ Z.T := by rw [hTe]; exact hy
      refine Or.inl (Or.inr ⟨y, hyT, K.val, h1', by omega, by omega, by omega, by omega, ?_⟩)
      rw [eb]; exact tfield_val (hP.tcb y hyT) (by omega)
    · exact absurd hb (Set.notMem_empty _))
  have hU0 : P1.UserOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H ∅ s1 := fun b hb => absurd hb (Set.notMem_empty _)
  obtain ⟨h2, hB2, hX2, hS2'', hSg2, -, -, -, -, f2, -⟩ :=
    P1.xfer_all h1 hB1 hX1 hS1' hSg1 hU0 (w2.mono fun b hb => P1.XferRegW.foot hb)
  have F2 : P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s1 s2 :=
    w2.mono fun b hb => by
      rcases hb with ⟨y, hy, K, h1', h2', h3', eb⟩ | hb
      · exact Or.inl ⟨y, hy, K, by omega, by omega, by omega, by omega, eb⟩
      · exact absurd hb (Set.notMem_empty _)
  have Fr2 : CFr e.bv d'.bv σ σ2 := Fr1.trans (CFr.upd hkd1 (Or.inl ⟨xd, xd.tcbState, xd.tcbBoundNotification,
    xd.tcbFault, (xferTcb xd xt badge.bv).tcbArch, rfl, by rw [xferTcb_eqA],
    Or.inr ⟨Or.inl rfl, rfl, Or.inl ⟨_, _, _, hstd⟩, Or.inr (Or.inr rfl)⟩⟩))
  have IK2 : IK d'.bv σ σ2 := IK1.trans (IK.updSelf hkd1 hxsc)
  have SK2 : SKeep σ σ2 := SK1.trans (SKeep.updK (p := d'.bv) (o := .tcb (xferTcb xd xt badge.bv)) (fun y h => ⟨xd, hkd1, by cases h; exact hxsc.symm⟩)
    (fun _ _ h => by cases h))
  have hks2 : L.ksb s2 = L.ksb s := hW2.1
  have Fst2 : L.mem s2 (P1.stA d') = L.mem s (P1.stA d') := by
    rw [P1.stA_eq]
    exact (f2 d' hdH _ (by simp) (by simp) (by simp)).trans (f1 d' hdH _ (by simp) (by simp) (by simp) (by simp))
  have hds2 : L.mem s2 (P1.stA d') = sched.TS_BLOCKED_ON_RECV := Fst2.trans hds
  -- the reply object
  refine WP.spec_bind (Endp.obj.Tcb.reply_obj.spec s2 d') ?_
  rintro _ rfl
  rw [hrw]
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine WP.spec_bind (Pₘ := fun s3 => ∃ σ3 x3 X3,
      Fl4Spec.NonDet.maybeM (Fl4Spec.replyUnlinkTcb (Z := Unit) d'.bv) rep σ2 = ({((), σ3)}, False) ∧
      EpStateRel Z.T Z.E Z.R Z.B (L.mem s3) σ3 ∧
      SRN st Z.N Z.T (SRS st Z.T (SRT st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c
        (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c))) s3 σ3 ∧
      σ3.kheap t.bv = some (.tcb xt) ∧ σ3.kheap d'.bv = some (.tcb x3) ∧ RbIn x3.tcbState ∧
      tsCode x3.tcbState ≠ 6 ∧ x3.tcbSchedContext = xd.tcbSchedContext ∧
      (∀ e'' ∈ Z.E, ∀ z, σ3.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue) ∧
      P1.WritesIn st s s3 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ) ∧
      P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s s3 ∧
      CFr e.bv d'.bv σ σ3 ∧ IK d'.bv σ σ3 ∧ SKeep σ σ3 ∧ σ3.curThread = σ.curThread ∧
      σ3.schedulerAction = σ.schedulerAction ∧
      P1.SchedQueuesInvX st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H X3 s3 Q0 R0 ∧
      P1.BoundInv st (P1.Heap.tcbs H) Ac s3 ∧
      P1.XInv st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) (P1.Heap.frame H) (P1.Heap.replies H) (P1.Heap.scs H)
        (P1.Heap.ntfns H) (P1.Heap.scBits H) s3 ∧
      P1.SCsOK st (P1.Heap.tcbs H) (P1.Heap.omega H) (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) Ac s3 ∧
      P1.SgOK st (P1.Heap.omega H) (P1.Heap.frame H) s3 ∧ P1.ExcT X3 d' ∧
      (d' ∈ X3 ∨ ¬ P1.Blocked (L.mem s3 (P1.stA d'))) ∧
      (∀ r ∈ P1.Heap.replies H, L.mem s3 (P1.rTcbA r) ≠ d')) ?_ ?_
  · cases hrp : rep with
    | none =>
      rw [hrp] at hrep
      have h00 := optRef_none hrep
      simp only [h00, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      have hrA : L.mem s2 (P1.replyA d') = 0#u64 := by
        show L.mem s2 (tReplyA d') = 0#u64; rw [hrw]; exact h00
      exact ⟨σ2, xferTcb xd xt badge.bv, _, rfl, hR2, hS2', hkt2, hkd2, Or.inl ⟨_, _, _, hst2'⟩,
        by rw [hst2']; simp [tsCode], hxsc, hq2, hW2, F1.trans F2, Fr2, IK2, SK2, rfl, rfl, h2, hB2, hX2, hS2'',
        hSg2, fun y hy => by simpa using hy, Or.inl (Or.inr rfl), hX2.noref0 hdta hrA⟩
    | some r =>
      rw [hrp] at hrep hrepR hst2'
      obtain ⟨hw0, hwr⟩ := Notif.optRef_some hrep
      have hwR := hrepR (by simp)
      have hne0 : (L.mem s (tReplyA d') != 0#u64) = true := by simp [hw0]
      simp only [hne0, ↓reduceIte]
      set w := L.mem s (tReplyA d') with hwdef
      subst hwr
      obtain ⟨xr, hkr, -⟩ := hR.reply w hwR
      have hwe : w.bv ≠ e.bv := kheap_ne hkr hk (fun _ h1 h2 => by subst h1; cases h2)
      have hwd : w.bv ≠ d'.bv := kheap_ne hkr hkd (fun _ h1 h2 => by subst h1; cases h2)
      have hwt : w.bv ≠ t.bv := kheap_ne hkr hkt (fun _ h1 h2 => by subst h1; cases h2)
      have hkr2 : σ2.kheap w.bv = some (.reply xr) := by simp [σ2, σ1, hwe, hwd, hkr]
      have hb' : xr.replyTcb = some d'.bv := hback_of J.sv hkd e.bv w.bv dd xr (by rw [hstd, hrp]) hkr
      have hX2' := IpcRel.ofSRN hR2 hS2'
      have hrA : L.mem s2 (P1.replyA d') = w := by show L.mem s2 (tReplyA d') = w; rw [hrw]
      obtain ⟨hiR, hit⟩ := hX2.2.1.recv d' hdH hds2 (by rw [hrA]; exact hw0)
      rw [hrA] at hiR hit
      refine WP.spec_mono (WP.spec_and (WP.spec_and (reply_unlink_c hH hP0 hP s2 σ2 hR2 hS2' hdT hkd2 hst2' hwR hkr2
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
      set x3 : Fl4Spec.Tcb := { xferTcb xd xt badge.bv with tcbState := .inactive } with hx3
      set σ3a := Notif.updK σ2 w.bv (.reply { xr with replyTcb := none }) with hσ3a
      have hkd3a : σ3a.kheap d'.bv = some (.tcb (xferTcb xd xt badge.bv)) := by simp [σ3a, Ne.symm hwd, hkd2]
      have hct3a : d'.bv ≠ (Notif.updK σ3a d'.bv (.tcb x3)).curThread := hdc
      have e3s : Notif.stsAct (Notif.updK σ3a d'.bv (.tcb x3)) d'.bv = Notif.updK σ3a d'.bv (.tcb x3) :=
        stsAct_ne hct3a
      have hW3' : P1.WritesIn st s s3 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ) :=
        hW2.trans1 (hW3.mono fun b hb => cnW_back hks2 (SzKeepC.of Fr2.szKeep) hb)
      refine ⟨_, x3, _, e3, hR3, hS3, ?_, ?_, Or.inr rfl, by simp [x3, tsCode], by simp [x3, hxsc], ?_, hW3',
        (F1.trans F2).trans fu3, ?_, ?_, ?_, ?_, ?_, h3,
        hB2.keepT h2 k3 (by rw [e3']; exact P1.not_blocked_inactive) (by rw [e3']; exact P1.inactive_ne.1),
        hX2.keepT k3 (by rw [e3']; exact P1.inactive_ne) hclr, hS2''.keepT hX2 k3,
        ⟨hsub, fun b hb => by rw [k3.ksb]; exact hSg2.ks b hb, fun o h1' h2' => by rw [k3.ksb]; exact hSg2.ksΩ o h1' h2'⟩,
        fun y hy => ?_, Or.inr (by rw [e3']; exact P1.not_blocked_inactive),
        (hX2.keepT k3 (by rw [e3']; exact P1.inactive_ne) hclr).noref hdta (by rw [e3']; exact P1.inactive_ne.1)
          (by rw [e3']; exact P1.inactive_ne.2)⟩
      · rw [stsAct_kheap]; simp [σ3a, htd', hwt.symm, hkt2]
      · rw [stsAct_kheap]; simp
      · intro e'' he'' z hz
        rw [stsAct_kheap] at hz
        have hne : d'.bv ≠ e''.bv := by intro h; rw [← h] at hz; simp at hz
        have hne' : w.bv ≠ e''.bv := by intro h; rw [← h] at hz; simp [σ3a, hwd] at hz
        exact hq2 e'' he'' z (by simpa [σ3a, Ne.symm hne, Ne.symm hne'] using hz)
      · exact (Fr2.trans (CFr.upd hkr2 (Or.inr (Or.inr (Or.inr ⟨xr, rfl, rfl, hb'⟩))))).trans
          (CFr.stsIn hkd3a (Or.inl ⟨_, _, _, hst2'⟩))
      · have IK3a : IK d'.bv σ σ3a := IK2.trans (IK.updOther (o' := .reply { xr with replyTcb := none }) hkr2 (fun o0 h => by
          rcases h with rfl | rfl <;> exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h)⟩))
        have IK3b : IK d'.bv σ (Notif.updK σ3a d'.bv (.tcb x3)) := IK3a.trans (IK.updSelf (y := x3) hkd3a rfl)
        exact IK3b.trans (IK.sts _ _ _)
      · exact ((SK2.trans (SKeep.updK (p := w.bv) (o := .reply { xr with replyTcb := none }) (fun y h => by cases h) (fun _ _ h => by cases h))).trans
          (SKeep.updK (p := d'.bv) (o := .tcb x3) (fun y h => ⟨_, hkd3a, by cases h; rfl⟩) (fun _ _ h => by cases h))).trans (SKeep.stsAct _ _)
      · rw [e3s]; rfl
      · rw [e3s]; rfl
      · obtain ⟨hy1, hy2⟩ := hy
        rcases hy1 with hy1 | hy1
        · exact absurd hy1 (Set.notMem_empty _)
        · exact absurd hy1 hy2
  rintro s3 ⟨σ3, x3, X3, hU, hR3, hS3, hkt3, hkd3, hrb3, hns3, hsc3, hq3, hW3, F3, Fr3, IK3, SK3, hct3, hact3,
    h3, hB3, hX3, hS3', hSg3, hXc3, hx3, hnr3⟩
  have hxt3 := hR3.at_tcb ht hkt3
  refine WP.spec_bind (Pₘ := fun r : S × A => r = (s3, a)) ?_ ?_
  · refine WP.spec_bind (Endp.obj.Tcb.fault_type.spec s3 t) ?_
    rintro i1 hi1
    have hf0 : i1 = fl4_abi.consts.fault.NullFault := by
      rw [hi1, hxt3.fault0.2 hft]; unfold fl4_abi.consts.fault.NullFault; rfl
    simp only [hf0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    cases don with
    | false => exact (WP.spec_ok _).2 rfl
    | true =>
      rw [if_pos rfl]
      step with Fl4Proofs.P1.obj.Tcb.sc.spec as ⟨i2, hi2⟩
      have hne : i2 ≠ 0#u64 := by
        obtain ⟨Q3, R3', -, hs3⟩ := hS3.1.1.2.1.lists
        obtain ⟨x3', hk3', -, -, hsc', -⟩ := hs3.tcb d' hdT
        rw [hkd3] at hk3'; cases hk3'
        intro h0
        rw [hi2] at h0
        rw [h0, optRef_zero, hsc3] at hsc'
        rcases hdon with h | h
        · cases h
        · exact h xd hkd hsc'
      rw [if_neg hne]
      exact (WP.spec_ok _).2 rfl
  rintro _ rfl
  try dsimp only
  -- the receiver runs
  refine WP.spec_bind (WP.spec_and (WP.spec_and (set_thread_state_c hH hP0 hP s3 σ3 hR3 hS3 hdT hkd3 hq3 hns3
      .running (by simp [tsCode]) sched.TS_RUNNING (by unfold sched.TS_RUNNING; rfl))
      (set_thread_state_sfoot (IpcRel.ofSRN hR3 hS3).2.2.1 hdT sched.TS_RUNNING))
    (WP.spec_and (P1.sts_all s3 d' _ Q0 R0 h3 hB3 hX3 hS3' hSg3 hdH P1.not_blocked_running P1.running_ne hx3 hnr3
        ⟨fun _ _ _ _ _ => P1.runnable_running, fun _ _ _ => P1.runnable_running, fun _ => P1.runnable_running⟩)
      (P1.sched.set_thread_state.kw (Sg := P1.Heap.frame H) (Scs := P1.Heap.scs H) (Z := P1.Heap.scBits H)
        (Es := P1.EH H) s3 d' sched.TS_RUNNING h3 hdH))) ?_
  rintro s5 ⟨⟨⟨hR5, hS5⟩, hW5⟩, ⟨h5, hB5, hX5, hS5', hSg5, -, -⟩, fu5⟩
  set x5 : Fl4Spec.Tcb := { x3 with tcbState := .running } with hx5
  set σ5 := Notif.stsAct (Notif.updK σ3 d'.bv (.tcb x5)) d'.bv with hσ5
  have hks3 : L.ksb s3 = L.ksb s := hW3.1
  have hIR := IpcRel.ofSRN hR5 hS5
  have hW5' : P1.WritesIn st s s5 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ) :=
    hW3.trans1 (hW5.mono fun b hb => Or.inl (Or.inl (KFoot.of_sfoot ((SFoot.ksb hks3).1 hb))))
  have hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s5 :=
    ⟨⟨Q0, R0, h5.congrX (P1.excT_congr hXc3)⟩, hB5, hX5, hS5', hSg5⟩
  have hfoot := F3.trans fu5
  have Fr5 : CFr e.bv d'.bv σ σ5 := Fr3.trans (CFr.stsRun hkd3 hrb3)
  have IK5a : IK d'.bv σ (Notif.updK σ3 d'.bv (.tcb x5)) := IK3.trans (IK.updSelf (y := x5) hkd3 rfl)
  have IK5 : IK d'.bv σ σ5 := IK5a.trans (IK.sts _ _ _)
  have SK5 : SKeep σ σ5 := (SK3.trans (SKeep.updK (p := d'.bv) (o := .tcb x5) (fun y h => ⟨x3, hkd3, by cases h; rfl⟩)
    (fun _ _ h => by cases h))).trans (SKeep.stsAct _ _)
  have hnqD : NotQueued σ d'.bv := by
    refine ⟨fun dm p hm => ?_, fun hm => ?_⟩
    · obtain ⟨x, -, -, -, hkx, -, hrx, -, -⟩ := J.inv.rq dm p _ hm
      rw [hkd] at hkx; cases hkx; rw [hstd] at hrx; cases hrx
    · obtain ⟨x, -, -, -, hkx, -, hrx, -, -⟩ := J.inv.rel _ hm
      rw [hkd] at hkx; cases hkx; rw [hstd] at hrx; cases hrx
  have hrib : RelIfBound σ5 d'.bv :=
    Ipc.RelIfBound.of_keep (J.inv.rd d'.bv xd hkd (Or.inr (Or.inr (Or.inr ⟨_, _, _, hstd⟩)))) SK5
  have I5 : Inv σ5 := ((J.inv.toBut d'.bv).ik hnqD IK5).1.inv fun _ _ _ => hrib
  have act5 : σ5.schedulerAction = σ.schedulerAction := by
    rw [hσ5, stsAct_ne (by show d'.bv ≠ σ3.curThread; rw [hct3]; exact hdc)]; exact hact3
  have hAI5 : ActIdle σ5 := ⟨fun u hu => Fr5.sched (J.act.1 u (by rw [← act5]; exact hu)), Fr5.idleOK J.act.2⟩
  have hcur5 : σ5.schedulerAction = .chooseNewThread ∨ CurInv σ5 :=
    J.cur.imp (fun e0 => by rw [act5]; exact e0) Fr5.curInv
  have hrun5 : CurRunM σ5 := J.curRun.of_cn Fr5.curRunW (Or.inr act5)
  have htD := J.not_dead_of_st hdT hkd (by rw [hstd]; simp [tsCode])
  have hRR : ∀ q' ∈ Z.R, ∀ xr, σ.kheap q'.bv = some (.reply xr) → xr.replyTcb = some d'.bv →
      Detached Z.C Lst q' ∧ L.mem s (rNextA q') = 0#u64 ∧ L.mem s (rPrevA q') = 0#u64 :=
    fun q' hq'' xr hx' hxt' => recvReplyHyp_holds Z Ac Lst D s _ σ J q' hq'' xr d'.bv xd hx' hxt' hkd
      (by rw [hstd]; rfl)
  have hF : IFrame (L := L) Z.th s s5 := IRel.iframe_of hI hW5' fun b hb => CnW.oobj hI.2.2.1 hb
  obtain ⟨V', J5⟩ := J.wake_postD hIR hF hW5' hblk hfoot (DWFr.ofCFr Fr5) I5 (Fr5.bsa J.bsa) hAI5 hcur5 hrun5
    hRR htD ⟨d', hdT, rfl⟩
  -- the tail
  have hk5 : σ5.kheap d'.bv = some (.tcb x5) := by rw [hσ5, stsAct_kheap]; simp
  have hnr5 : d'.bv ∉ σ5.releaseQueue := by rw [SK5.1]; exact hnqD.2
  have hact5 : ∀ p y n, x5.tcbSchedContext = some p → σ5.kheap p = some (.schedContext y n) →
      Fl4Spec.scActive y = true := by
    intro p y n hp hy
    have hy0 := SK5.2.2.2 p y n hy
    have hp' : xd.tcbSchedContext = some p := by rw [← hsc3]; exact hp
    obtain ⟨y', n', hky', hyt⟩ := J.inv.back _ _ _ hkd hp'
    rw [hy0] at hky'; cases hky'
    exact J.bsa.tcb p y n d'.bv xd hy0 hyt hkd (by rw [hstd]; rfl)
  have hti5 : d'.bv ≠ σ5.idleThread := by
    rw [Fr5.sk.idle]
    intro h
    obtain ⟨x, hkx, -, hxs, -⟩ := J.act.2
    rw [← h, hkd] at hkx; cases hkx; rw [hstd] at hxs; cases hxs
  have htc5 : d'.bv ≠ σ5.curThread := by rw [Fr5.sk.ct]; exact hdc
  have hdon3 : don = false ∨ x3.tcbSchedContext ≠ none := hdon.imp_right fun h => by
    rw [hsc3]; exact h xd hkd
  have hspec := sendIpc_recv_eqD hk hkd hde hstd blk badge.bv g gr don e2 hU hkt3 hft hkd3 hdon3 (t := t.bv)
  refine WP.spec_mono (J5.sendTailJ hdT hk5 rfl hnr5 hact5 hti5 htc5) ?_
  rintro ⟨s7, a7⟩ ⟨ha7, σ7, h7, Lst7, J7⟩
  simp only at ha7
  subst ha7
  exact ⟨((), σ7), by rw [hspec, h7]; exact Set.mem_singleton _, ⟨_, _, _, _, _, _, J7⟩⟩

end

end

end Fl4Proofs.P3
