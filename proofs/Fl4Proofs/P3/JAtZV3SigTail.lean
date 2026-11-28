/-
P3 (line mmuAD, gen 42a): **gen 35's [J] `SigVmTailJ3` after FL4 #114, narrowed to the donation case** —
the tail of `send_signal`'s RunningVM-completing branch (after `vcpu::report`) at `JAtZV3`, against the extended
spec's `sigVmTailS` now that `sendSignalVF` skips the sporadic `refillUnblockCheck` for a thread in the release
queue (Fl4Spec/Ext/VirtReport, FL4 #114: fl4-core notification.rs l. 106-120 `&& !sched::in_release_queue(s, t)`).

Gen 36 found `SigVmTailJ3` false as stated (P3/SigVmTailFalse: `refillUnblockCheck` of a release-queued thread's
ready sporadic SC unsorts the release queue). With #114 on both sides that shape no longer arises: FL4 reads
`in_release_queue t` (`TCB.IN_QUEUES & Q_RELEASE`), the spec `inReleaseQueue t` (`t ∈ releaseQueue`), related by
`SchedCore.released` / `SchedSpec.rel` (`mem_map_bv`), and both skip the check.

* Splitting: `sigVmRestF` / `sigVmSporF` (FL4's tail after `maybe_donate_sched_context`, verbatim from
  P3/JAtZV3SigComp's `sigVmTailF`; `sigVmTailF_eq`), `sigVmRestS` / `sigVmSporS` (the spec's after `maybeDonateSc`,
  verbatim from `sigVmTailS`; `sigVmTailS_eq`).
* Spec side: `stl_getScActive`, `stl_gnor`, `stl_gsor`, `stl_spor_none`, `stl_spor_some` (the sporadic part in
  closed form), `stl_mds_some` / `stl_mds_nn` / `stl_mds_bound` (`maybeDonateSc` donates nothing: the thread has an
  SC, the notification none, or its SC is bound).
* **`JAtZB.unblockJR`**: P3/XTopJointUnblock's `JAtZ.unblockJ` over `JAtZB` with the thread's `Inactive` state
  replaced by `t ∉ releaseQueue` (its only use: the thread bound to `p` is in no release queue, for `Inv.unblock`),
  and the post extended by the domain time, `ScTKw` and FL4's `TFoot` writes (for `JAtZV3.ofTK`). Its source runs
  under `maxHeartbeats 16000000`; the copy elaborates under 4000000.
* **`JAtZV3.sigSporJ`**: FL4's sporadic part (`sc` word, `is_null`, `sc_active`, the notification's SC word,
  `sc_sporadic`, `CUR_SC`, `in_release_queue`, `unblock_check`) refines `sigVmSporS` from any `JAtZV3` state with
  `t ∈ T`, `n ∈ N`; `JAtZV3` after by `unblockJR` + `JAtZV3.ofTK`.
* **`JAtZV3.sigRestJ`**: `is_schedulable` (`schedulable_eq`) and `possible_switch_to` (`JAtZV3.switchJc`, the thread
  may be current; domain time by `pst_q`'s `QOnly`) then `sigSporJ`.
* **`SigVmDonJ3`** [J] (below): the donation case of `maybe_donate_sched_context` only.
* **`sigVmTailJ3_of`**: `SigVmDonJ3 → SigVmTailJ3` — the non-donating cases of `maybe_donate_sched_context` are
  computed (`ok (s, a)`, the spec's `maybeDonateSc` = `{((), σ)}`), the donating case is `SigVmDonJ3`, then
  `sigRestJ`.
* **`JAtZV3.signalVmJ2`**: gen 35's `JAtZV3.signalVmJ` with `SigVmDonJ3` in place of `SigVmTailJ3`.

Premise diff: `SigVmTailJ3` [J] (gen 35) is now derived from the narrower **`SigVmDonJ3`** [J]; nothing else.
No existing statement changed by this module.
-/
import Fl4Proofs.P3.JAtZV3SigVm
import Fl4Proofs.P3.JAtZV3SwitchC
import Fl4Proofs.P3.XTopJointUnblock
import Fl4Proofs.P3.XTopJointPP
import Fl4Proofs.P3.IpcFinNtfnInv
import Fl4Proofs.P3.SchedValidLinks
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-! ## Splitting the two tails -/

section
variable {S : Type} {A : Type}

/-- FL4's sporadic check of `send_signal`'s RunningVM tail (verbatim from `sigVmTailF`, after the switch). -/
def sigVmSporF (st : machine.Store S) (s3 : S) (a1 : A) (i : obj.Tcb) (n_ptr : U64) : Result (S × A) := do
  let i2 ← obj.Tcb.sc st i s3
  let b3 ← obj.Sc.is_null i2
  if b3
  then ok (s3, a1)
  else
    let b4 ← sporadic.sc_active st s3 i2
    if b4
    then
      let i3 ← obj.Ntfn.sc st n_ptr s3
      if i2 = i3
      then
        let b5 ← sporadic.sc_sporadic st s3 i2
        if b5
        then
          let s4 ← sched.cur_sc st s3
          let b6 ← core.cmp.PartialEq.ne.trait_default obj.Sc.Insts.CoreCmpPartialEqSc i2 s4
          if b6
          then
            let b7 ← sched.in_release_queue st s3 i
            if b7
            then ok (s3, a1)
            else
              let s5 ← sporadic.unblock_check st s3 i2
              ok (s5, a1)
          else ok (s3, a1)
        else ok (s3, a1)
      else ok (s3, a1)
    else ok (s3, a1)

/-- FL4's tail after `maybe_donate_sched_context` (verbatim from `sigVmTailF`). -/
def sigVmRestF (st : machine.Store S) (s2 : S) (a1 : A) (i : obj.Tcb) (n_ptr : U64) : Result (S × A) := do
  let b2 ← sched.is_schedulable st s2 i
  let s3 ← if b2 then sched.possible_switch_to st s2 i else ok s2
  sigVmSporF st s3 a1 i n_ptr

theorem sigVmTailF_eq (st : machine.Store S) (arI : machine.Arch A) (s1 : S) (a : A) (i : obj.Tcb) (n_ptr : U64) :
    sigVmTailF st arI s1 a i n_ptr = (do
      let (s2, a1) ← notification.maybe_donate_sched_context st arI s1 a i n_ptr
      sigVmRestF st s2 a1 i n_ptr) := rfl

end

section
open Fl4Spec Classical Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp

/-- The spec's sporadic check of `sigVmTailS` (verbatim). -/
def sigVmSporS (ntfnptr tcb : ObjRef) : SMonad Unit Unit := do
  let scOpt ← getTcbObjRef Tcb.tcbSchedContext tcb
  NonDet.maybeM (fun scp => do
      let active ← getScActive scp
      NonDet.when active <| do
        let sc ← getSchedContext scp
        let ntfnScp ← getNtfnObjRef Notification.ntfnSc ntfnptr
        let curScPtr ← NonDet.gets fun s : State Unit => s.curSc
        let inRq ← NonDet.gets (inReleaseQueue tcb)
        NonDet.when (scOpt = ntfnScp ∧ sc.scSporadic ∧ scp ≠ curScPtr ∧ inRq = false) <| refillUnblockCheck scp)
    scOpt

/-- The spec's tail after `maybeDonateSc` (verbatim from `sigVmTailS`). -/
def sigVmRestS (ntfnptr tcb : ObjRef) : SMonad Unit Unit := do
  let sched ← NonDet.gets (schedulable tcb)
  NonDet.when sched <| possibleSwitchTo tcb
  sigVmSporS ntfnptr tcb

theorem sigVmTailS_eq (n t : ObjRef) : sigVmTailS n t = (maybeDonateSc t n >>= fun _ => sigVmRestS n t) := rfl

theorem stl_getScActive {σ : State Unit} {p : ObjRef} {yc : SchedContext} {k : Nat}
    (hk : σ.kheap p = some (.schedContext yc k)) : getScActive (Z := Unit) p σ = ({(scActive yc, σ)}, False) := by
  unfold getScActive NonDet.getsThe; rw [readScActive_eq' hk]; rfl

theorem stl_gnor {σ : State Unit} {n : ObjRef} {y : Notification} (f : Notification → Option ObjRef)
    (hk : σ.kheap n = some (.notification y)) : getNtfnObjRef (Z := Unit) f n σ = ({(f y, σ)}, False) := by
  show (getNotification n >>= fun sc => pure (f sc)) σ = _
  rw [nd_bind_one (getNotification_eq hk)]; rfl

theorem stl_gsor {σ : State Unit} {p : ObjRef} {yc : SchedContext} {k : Nat} (f : SchedContext → Option ObjRef)
    (hk : σ.kheap p = some (.schedContext yc k)) : getScObjRef (Z := Unit) f p σ = ({(f yc, σ)}, False) := by
  unfold getScObjRef; rw [nd_bind_one (Sched.getSchedContext_eq hk)]; rfl

theorem stl_spor_none {σ : State Unit} {t n : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (hx : x.tcbSchedContext = none) : sigVmSporS n t σ = ({((), σ)}, False) := by
  unfold sigVmSporS getTcbObjRef
  rw [nd_bind_one (threadGet_eq _ hk), hx]; rfl

/-- The sporadic check in closed form (module docstring). -/
theorem stl_spor_some {σ : State Unit} {t n p : ObjRef} {x : Tcb} {yc : SchedContext} {k : Nat} {y : Notification}
    (hk : σ.kheap t = some (.tcb x)) (hx : x.tcbSchedContext = some p) (hkp : σ.kheap p = some (.schedContext yc k))
    (hkn : σ.kheap n = some (.notification y)) :
    sigVmSporS n t σ = if scActive yc = true then
      (if x.tcbSchedContext = y.ntfnSc ∧ yc.scSporadic = true ∧ p ≠ σ.curSc ∧ inReleaseQueue t σ = false then
        refillUnblockCheck p σ else ({((), σ)}, False)) else ({((), σ)}, False) := by
  unfold sigVmSporS getTcbObjRef
  rw [nd_bind_one (threadGet_eq _ hk), hx]
  simp only [NonDet.maybeM]
  rw [nd_bind_one (stl_getScActive hkp)]
  try dsimp only
  unfold NonDet.when
  by_cases ha : scActive yc = true
  · simp only [if_pos ha]
    rw [nd_bind_one (Sched.getSchedContext_eq hkp), nd_bind_one (stl_gnor _ hkn), nd_gets_bind, nd_gets_bind]
    try dsimp only
    split_ifs <;> rfl
  · simp only [if_neg ha]; rfl

theorem stl_mds_some {σ : State Unit} {t n : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (hx : x.tcbSchedContext ≠ none) : maybeDonateSc (Z := Unit) t n σ = ({((), σ)}, False) := by
  unfold maybeDonateSc getTcbObjRef
  rw [nd_bind_one (threadGet_eq _ hk)]
  try dsimp only
  unfold NonDet.when
  rw [if_neg hx]; rfl

theorem stl_mds_nn {σ : State Unit} {t n : ObjRef} {x : Tcb} {y : Notification} (hk : σ.kheap t = some (.tcb x))
    (hx : x.tcbSchedContext = none) (hkn : σ.kheap n = some (.notification y)) (hy : y.ntfnSc = none) :
    maybeDonateSc (Z := Unit) t n σ = ({((), σ)}, False) := by
  unfold maybeDonateSc getTcbObjRef
  rw [nd_bind_one (threadGet_eq _ hk)]
  try dsimp only
  unfold NonDet.when
  rw [if_pos hx]
  show (getNtfnObjRef Notification.ntfnSc n >>= _) σ = _
  rw [nd_bind_one (stl_gnor _ hkn), hy]; rfl

theorem stl_mds_bound {σ : State Unit} {t n p : ObjRef} {x : Tcb} {y : Notification} {yc : SchedContext} {k : Nat}
    (hk : σ.kheap t = some (.tcb x)) (hx : x.tcbSchedContext = none) (hkn : σ.kheap n = some (.notification y))
    (hy : y.ntfnSc = some p) (hkp : σ.kheap p = some (.schedContext yc k)) (hyt : yc.scTcb ≠ none) :
    maybeDonateSc (Z := Unit) t n σ = ({((), σ)}, False) := by
  unfold maybeDonateSc getTcbObjRef
  rw [nd_bind_one (threadGet_eq _ hk)]
  try dsimp only
  unfold NonDet.when
  rw [if_pos hx]
  show (getNtfnObjRef Notification.ntfnSc n >>= _) σ = _
  rw [nd_bind_one (stl_gnor _ hkn), hy]
  simp only [NonDet.maybeM]
  rw [nd_bind_one (stl_gsor _ hkp)]
  try dsimp only
  rw [if_neg hyt]; rfl

end

/-! ## `unblock_check` of a thread in no release queue, at `JAtZB` -/

section
open Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 4000000 in
/-- **`unblock_check` at `JAtZB` for a thread in no release queue** (module docstring; P3/XTopJointUnblock's
`JAtZ.unblockJ` with `t ∉ releaseQueue` for `Inactive`, the post extended). -/
theorem JAtZB.unblockJR (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hnq : t.bv ∉ σ.releaseQueue)
    {p : U64} (hp : p ∈ Z.C) (hxsc : x.tcbSchedContext = some p.bv) (hpc : p.bv ≠ σ.curSc)
    {y : Fl4Spec.SchedContext} {n : Nat} (hky : σ.kheap p.bv = some (.schedContext y n))
    (hya : Fl4Spec.scActive y = true) :
    sporadic.unblock_check st s p ⦃ s' => ∃ σ', Fl4Spec.refillUnblockCheck (Z := Unit) p.bv σ = ({((), σ')}, False) ∧
      (∀ q, q ≠ p.bv → σ'.kheap q = σ.kheap q) ∧ σ'.domainTime = σ.domainTime ∧
      ScTKw (fun _ => False) σ σ' ∧ P1.WritesIn st s s' (TFoot st Z.T Z.N Z.C Z.c s σ) ∧
      ∃ Lst' : U64 → List U64, JAtZB (L := L) arI AR Z H Cs Ac Lst' D s' a σ' ⦄ := by
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
      ∃ z, σ'.kheap p.bv = some (.schedContext z n) := by
    rcases unblock_result hky hne mem with ⟨rfl, -⟩ | ⟨z, rfl, -, -, -, -⟩
    · exact ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, y, hky⟩
    · exact ⟨fun q hq => by simp [updK, hq], rfl, rfl, rfl, rfl, rfl, rfl, rfl, z, by simp [updK]⟩
  obtain ⟨hkp, e_ct, e_csc, e_tm, e_cons, e_rel, e_idle, e_act, z, hkz⟩ := hF
  have e_dt : σ'.domainTime = σ.domainTime := by
    rcases unblock_result hky hne mem with ⟨rfl, -⟩ | ⟨z, rfl, -⟩
    · rfl
    · rfl
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
  -- the invariant: the only thread bound to `p` is `t`, `Inactive`, so in no release queue
  have hI' : Inv σ' := by
    refine J.inv.unblock hky hne (fun _ _ u hu xu hku hsu => ?_) mem
    obtain ⟨y1, n1, hk1, hyt1⟩ := J.inv.back u xu p.bv hku hsu
    obtain ⟨y2, n2, hk2, hyt2⟩ := J.inv.back t.bv x p.bv hk hxsc
    rw [hk1] at hk2; cases hk2
    have hut : u = t.bv := Option.some.inj (hyt1.symm.trans hyt2)
    subst hut
    exact hnq hu
  obtain ⟨-, hY', hM', ⟨Lst', hCR', hRF'⟩, hRP', -⟩ :=
    ScAll.of_k hS J.rp J.yld J.mcp J.call J.rfree ⟨⟨hS', hR', hN', hI'⟩, hw, hsok⟩
  -- the current thread's facts: only the SC at `p ≠ curSc` changes
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
    rcases J.own with ⟨u, hu, xu, hku, hxs, hown, hnr⟩ | ⟨hcs, hun⟩
    · exact Or.inl ⟨u, hu, xu, htk' _ _ hku, by rw [e_csc]; exact hxs,
        fun y1 n1 hy => hown y1 n1 (by rw [← hkcs]; exact hy), by rw [e_cons, e_rel]; exact hnr⟩
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
  have hKd := J.kw_dbgKeep hfoot
  exact ⟨σ', he, hkp, e_dt, hK0, hwT, Lst', J.sc_frame hwT hK hX' hCR' hRF' hY' hM' (J.sc_buf hwT hK) hRP' (J.sc_apart hwT hK)
    (J.sc_jpl hwT hK (J.idleW_keep hX'.fin.1.1.1 hFK.2.1 hFK.2.2).2) (J.sc_jcov hwT hdead (fun q hq hn => absurd hq hn) (J.idleW_keep hX'.fin.1.1.1 hFK.2.1 hFK.2.2) hKd subset_rfl)
    (J.sc_kern hwT hK hFK hX' hDbg fun _ h => h) (J.sc_utc hwT hK hDbg) hN' hI' hC' hown' hoff hAI
    (J.bsa.bk hBK hsok) hcr ⟨⟨Q1, R1, hq2⟩, hB2, hX2, hS2, hSg2⟩ hKd (J.idleW_keep hX'.fin.1.1.1 hFK.2.1 hFK.2.2).1 J.zD⟩

/-! ## The tail at `JAtZV3` -/

variable {V X : Set U64}

set_option maxHeartbeats 4000000 in
/-- **FL4's sporadic check refines `sigVmSporS` at `JAtZV3`** (module docstring). -/
theorem JAtZV3.sigSporJ (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {t n : U64} (ht : t ∈ Z.T)
    (hn : n ∈ Z.N) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) {y : Fl4Spec.Notification}
    (hkn : σ.kheap n.bv = some (.notification y)) :
    sigVmSporF st s a t n ⦃ r => ∃ (σ' : Fl4Spec.State Unit) (Lst' : U64 → List U64),
      sigVmSporS n.bv t.bv σ = ({((), σ')}, False) ∧ σ'.domainTime = σ.domainTime ∧
      JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst' D r.1 r.2 σ' ⦄ := by
  have B := J.z2.zv.base
  have hS := B.xtop.fin.1.1.1
  have hR : NtfnStateRel Z.N Z.T (L.mem s) σ := B.xtop.fin.1.1.2.2.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  obtain ⟨xt, hkt, -, -, hsct, -⟩ := hs.tcb t ht
  rw [hk] at hkt; cases hkt
  obtain ⟨y', hkn', hyr⟩ := hR.ntfn n hn
  rw [hkn] at hkn'; cases hkn'
  have hysc := hyr.sc
  unfold sigVmSporF
  refine WP.spec_bind (Fl4Proofs.P1.obj.Tcb.sc.spec s t) fun i2 hi2 => ?_
  subst hi2
  refine WP.spec_bind (Sched.obj.Sc.is_null.spec' _) fun b3 hb3 => ?_
  by_cases h0 : L.mem s (scA t) = 0#u64
  · obtain rfl : b3 = true := by rw [hb3]; exact decide_eq_true h0
    rw [if_pos rfl]
    exact (WP.spec_ok _).2 ⟨σ, Lst, stl_spor_none hk (by rw [hsct, h0, Notif.optRef_zero]), rfl, J⟩
  obtain rfl : b3 = false := by rw [hb3]; exact decide_eq_false h0
  rw [if_neg Bool.false_ne_true]
  have hscC : L.mem s (scA t) ∈ Z.C := hs.scMem t ht h0
  obtain ⟨yc, k, hky, hy⟩ := hs.scs _ hscC
  have hxsc : x.tcbSchedContext = some (L.mem s (scA t)).bv := by rw [hsct, Notif.optRef_ne h0]
  have hSp := stl_spor_some (n := n.bv) hk hxsc hky hkn
  refine WP.spec_bind (Sched.sporadic.sc_active.spec' s _) fun b4 hb4 => ?_
  by_cases ha : Fl4Spec.scActive yc = true
  swap
  · obtain rfl : b4 = false := by
      rw [hb4]; refine decide_eq_false fun h => ha (hy.active_of_rmax ?_)
      have := P1.gt_iff_val.1 h; simp at this; omega
    rw [if_neg Bool.false_ne_true]
    exact (WP.spec_ok _).2 ⟨σ, Lst, by rw [hSp, if_neg ha], rfl, J⟩
  obtain rfl : b4 = true := by
    rw [hb4]; refine decide_eq_true (P1.gt_iff_val.2 ?_)
    have := hy.rmax_ne ha; simp; omega
  rw [if_pos rfl]
  rw [if_pos ha] at hSp
  refine WP.spec_bind (Notif.obj.Ntfn.sc.spec s n) fun i3 hi3 => ?_
  subst hi3
  by_cases heq : L.mem s (scA t) = L.mem s (nScA n)
  swap
  · rw [if_neg heq]
    refine (WP.spec_ok _).2 ⟨σ, Lst, ?_, rfl, J⟩
    rw [hSp, if_neg]
    rintro ⟨h1, -⟩
    rw [hxsc, hysc] at h1
    exact heq (P1.eq_of_bv (Notif.optRef_some h1.symm).2).symm
  rw [if_pos heq]
  have hcond1 : x.tcbSchedContext = y.ntfnSc := by rw [hxsc, hysc, ← heq, Notif.optRef_ne h0]
  refine WP.spec_bind (Sched.sporadic.sc_sporadic.spec' s _) fun b5 hb5 => ?_
  have hsp : yc.scSporadic = true ↔ L.mem s (scW (L.mem s (scA t)) 64#u64) ≠ 0#u64 := by
    rw [hy.sporadic]; simp
  by_cases hsw : L.mem s (scW (L.mem s (scA t)) 64#u64) ≠ 0#u64
  swap
  · obtain rfl : b5 = false := by rw [hb5]; exact decide_eq_false fun h => hsw h.2
    rw [if_neg Bool.false_ne_true]
    exact (WP.spec_ok _).2 ⟨σ, Lst, by rw [hSp, if_neg fun h => hsw (hsp.1 h.2.1)], rfl, J⟩
  obtain rfl : b5 = true := by rw [hb5]; exact decide_eq_true ⟨h0, hsw⟩
  rw [if_pos rfl]
  refine WP.spec_bind (Sched.sched.cur_sc.spec' s) fun s4 hs4 => ?_
  rw [hc.cur] at hs4
  subst hs4
  rw [Sched.sc_ne_eq, bind_ok]
  by_cases hcur : L.mem s (scA t) = Sched.nodeW st s Z.c layout.node.CUR_SC
  · rw [if_neg fun h => absurd hcur (of_decide_eq_true h)]
    exact (WP.spec_ok _).2 ⟨σ, Lst, by rw [hSp, if_neg fun h => h.2.2.1 (by rw [hs.curSc, hcur])], rfl, J⟩
  rw [if_pos (decide_eq_true hcur)]
  have hpc : (L.mem s (scA t)).bv ≠ σ.curSc := by rw [hs.curSc]; exact Sched.bv_ne hcur
  refine WP.spec_bind (Fl4Proofs.P1.sched.in_release_queue.spec s t) fun b7 hb7 => ?_
  have hrq : t.bv ∈ σ.releaseQueue ↔ (L.mem s (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64 := by
    rw [hs.rel, Sched.mem_map_bv]; exact (hc.released t ht).symm
  by_cases hin : (L.mem s (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64
  · obtain rfl : b7 = true := by rw [hb7]; exact decide_eq_true hin
    rw [if_pos rfl]
    refine (WP.spec_ok _).2 ⟨σ, Lst, ?_, rfl, J⟩
    rw [hSp, if_neg]
    intro h
    have h4 := h.2.2.2
    simp [Fl4Spec.inReleaseQueue, hrq.2 hin] at h4
  obtain rfl : b7 = false := by rw [hb7]; exact decide_eq_false hin
  rw [if_neg Bool.false_ne_true]
  have hnq : t.bv ∉ σ.releaseQueue := fun h => hin (hrq.1 h)
  refine WP.spec_bind (B.unblockJR ht hk hnq hscC hxsc hpc hky ha) ?_
  rintro s5 ⟨σ5, he5, -, hdt5, hK5, hW5, Lst5, B5⟩
  refine (WP.spec_ok _).2 ⟨σ5, Lst5, ?_, hdt5, J.ofTK B5 hW5 hK5⟩
  rw [hSp, if_pos ⟨hcond1, hsp.2 hsw, hpc, by simp [Fl4Spec.inReleaseQueue, hnq]⟩, he5]

set_option maxHeartbeats 4000000 in
/-- **FL4's tail after `maybe_donate_sched_context` refines `sigVmRestS` at `JAtZV3`** (module docstring). -/
theorem JAtZV3.sigRestJ (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {t n : U64} (ht : t ∈ Z.T)
    (hn : n ∈ Z.N) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) {y : Fl4Spec.Notification}
    (hkn : σ.kheap n.bv = some (.notification y)) :
    sigVmRestF st s a t n ⦃ r => ∃ (σ' : Fl4Spec.State Unit) (Lst' : U64 → List U64),
      sigVmRestS n.bv t.bv σ = ({((), σ')}, False) ∧ σ'.domainTime = σ.domainTime ∧
      JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst' D r.1 r.2 σ' ⦄ := by
  have B := J.z2.zv.base
  have hS := B.xtop.fin.1.1.1
  have hR : NtfnStateRel Z.N Z.T (L.mem s) σ := B.xtop.fin.1.1.2.2.1
  unfold sigVmRestF
  refine WP.spec_bind (Sched.sched.is_schedulable.spec' s t) fun b2 hb2 => ?_
  have hsch : b2 = Fl4Spec.schedulable t.bv σ := hb2.trans (Sched.schedulable_eq hR hS ht)
  cases hsv : Fl4Spec.schedulable t.bv σ with
  | false =>
    rw [hsch, hsv, if_neg Bool.false_ne_true, bind_ok]
    refine WP.spec_mono (J.sigSporJ ht hn hk hkn) ?_
    rintro r ⟨σ', Lst', h1, h2, J'⟩
    refine ⟨σ', Lst', ?_, h2, J'⟩
    unfold sigVmRestS
    rw [nd_gets_bind, hsv]
    unfold Fl4Spec.NonDet.when
    rw [if_neg Bool.false_ne_true]
    exact (nd_bind_one (m := (Fl4Spec.NonDet.pure () : Fl4Spec.NonDet (Fl4Spec.State Unit) Unit)) rfl _).trans h1
  | true =>
    rw [hsch, hsv, if_pos rfl]
    refine WP.spec_bind (J.switchJc ht hsv) ?_
    rintro s3 ⟨σ3, he3, Lst3, J3⟩
    obtain ⟨σq, heq, rq, act, hq⟩ := Sched.pst_q hk B.inv.actReady
    have e3 : σ3 = σq := by
      have h := congrArg Prod.fst (he3.symm.trans heq)
      simpa only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] using h
    have hk3 : σ3.kheap t.bv = some (.tcb x) := by rw [e3, hq]; exact hk
    have hkn3 : σ3.kheap n.bv = some (.notification y) := by rw [e3, hq]; exact hkn
    have hdt3 : σ3.domainTime = σ.domainTime := by rw [e3, hq]
    refine WP.spec_mono (J3.sigSporJ ht hn hk3 hkn3) ?_
    rintro r ⟨σ', Lst', h1, h2, J'⟩
    refine ⟨σ', Lst', ?_, h2.trans hdt3, J'⟩
    unfold sigVmRestS
    rw [nd_gets_bind, hsv]
    unfold Fl4Spec.NonDet.when
    rw [if_pos rfl, nd_bind_one he3]
    exact h1

end

/-! ## The narrowed premise and the old one derived -/

/-- **[J] The donation case of the RunningVM tail** (module docstring): from a `JAtZV3` state where `t` (a TCB of
the typed heap) is `running` with no SC and `n ∈ N` is idle, bound to `t`, with an SC `p` bound to no thread, FL4's
`maybe_donate_sched_context t n` (`schedcontext::donate` then `schedcontext::resume`, notification.rs l. 48-56)
refines the spec's `maybeDonateSc t n` (`schedContextDonate` then `schedContextResume`), deterministically, domain
time kept, `JAtZV3` after. Why not proved: the donation machinery is proved at `JAtZ` only — for a blocked donee
(P3/ScSignalDonJ `wake_postD` over IpcSignalDon's `donate_irelF`) and for the running current thread at a
`chooseNewThread` mid state (P3/XTopJointRecvSigDonD `JAtZ.recvSigDonJN`, whose proof is generic in the donee);
none of it over `JAtZB` / `JAtZV3`. Not false as far as checked: those proofs relate exactly these FL4 and spec
calls for a donee with no SC in no queue (here `Inv.rq`: a thread with no SC is in no ready queue; it is in no
release queue by `Inv.rel`), the donation touches no VCPU object and no TCB's VCPU word (only the TCB's SC word,
the SC's thread word, the release queue), and it needs the platform's `MIN_BUDGET` as `maybe_donate_refines` does
([P], `sporadic.min_budget`). -/
def SigVmDonJ3 {S : Type} (st : machine.Store S) [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
    (V X : Set U64) (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (D : Set U64) : Prop :=
  ∀ (Ac : Set U64) (Lst : U64 → List U64) (s1 : S) (a : A) (σr : Fl4Spec.State Unit) (t n : U64),
    JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s1 a σr → Z.th t = some .tcb → n ∈ Z.N →
    (∃ x, σr.kheap t.bv = some (.tcb x) ∧ x.tcbState = .running ∧ x.tcbSchedContext = none) →
    (∃ y p yc k, σr.kheap n.bv = some (.notification y) ∧ y.ntfnObj = .idleNtfn ∧ y.ntfnBoundTcb = some t.bv ∧
      y.ntfnSc = some p ∧ σr.kheap p = some (.schedContext yc k) ∧ yc.scTcb = none) →
    notification.maybe_donate_sched_context st arI s1 a t n ⦃ r => ∃ (σ' : Fl4Spec.State Unit) (Ac' : Set U64)
      (Lst' : U64 → List U64), Fl4Spec.maybeDonateSc (Z := Unit) t.bv n.bv σr = ({((), σ')}, False) ∧
      σ'.domainTime = σr.domainTime ∧ JAtZV3 (L := L) arI V X AR Z H Cs Ac' Lst' D r.1 r.2 σ' ⦄

section
open Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

set_option maxHeartbeats 4000000 in
/-- **Gen 35's [J] `SigVmTailJ3` from the narrower `SigVmDonJ3`** (module docstring). -/
theorem sigVmTailJ3_of (hDn : SigVmDonJ3 st arI V X AR Z H Cs D) : SigVmTailJ3 st arI V X AR Z H Cs D := by
  intro Ac Lst s1 a σr t n J hth hn hrun hntf
  obtain ⟨x, hk, hxr⟩ := hrun
  obtain ⟨y, hkn, hidle, hb⟩ := hntf
  have B := J.z2.zv.base
  have ht : t ∈ Z.T := B.thT t hth
  have hS := B.xtop.fin.1.1.1
  have hR : NtfnStateRel Z.N Z.T (L.mem s1) σr := B.xtop.fin.1.1.2.2.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  obtain ⟨xt, hkt, -, -, hsct, -⟩ := hs.tcb t ht
  rw [hk] at hkt; cases hkt
  obtain ⟨y', hkn', hyr⟩ := hR.ntfn n hn
  rw [hkn] at hkn'; cases hkn'
  have hysc := hyr.sc
  have rest : ∀ (s2 : S) (a2 : A) (σ2 : Fl4Spec.State Unit) (Ac2 : Set U64) (Lst2 : U64 → List U64),
      Fl4Spec.maybeDonateSc (Z := Unit) t.bv n.bv σr = ({((), σ2)}, False) → σ2.domainTime = σr.domainTime →
      JAtZV3 (L := L) arI V X AR Z H Cs Ac2 Lst2 D s2 a2 σ2 →
      sigVmRestF st s2 a2 t n ⦃ r => ∃ (σ' : Fl4Spec.State Unit) (Ac' : Set U64) (Lst' : U64 → List U64),
        sigVmTailS n.bv t.bv σr = ({((), σ')}, False) ∧ σ'.domainTime = σr.domainTime ∧
        JAtZV3 (L := L) arI V X AR Z H Cs Ac' Lst' D r.1 r.2 σ' ⦄ := by
    intro s2 a2 σ2 Ac2 Lst2 he2 hdt2 J2
    have B2 := J2.z2.zv.base
    obtain ⟨Q2, R2, hc2, hs2⟩ := B2.xtop.fin.1.1.1.lists
    obtain ⟨x2, hk2, -⟩ := hs2.tcb t ht
    have hR2 : NtfnStateRel Z.N Z.T (L.mem s2) σ2 := B2.xtop.fin.1.1.2.2.1
    obtain ⟨y2, hkn2, -⟩ := hR2.ntfn n hn
    refine WP.spec_mono (J2.sigRestJ ht hn hk2 hkn2) ?_
    rintro r ⟨σ', Lst', h1, h2, J'⟩
    exact ⟨σ', Ac2, Lst', by rw [sigVmTailS_eq, nd_bind_one he2]; exact h1, h2.trans hdt2, J'⟩
  rw [sigVmTailF_eq]
  by_cases hdon : L.mem s1 (scA t) = 0#u64 ∧ L.mem s1 (nScA n) ≠ 0#u64 ∧
      L.mem s1 (scTcbA (L.mem s1 (nScA n))) = 0#u64
  · obtain ⟨h0, h1, h2⟩ := hdon
    have hysc' : y.ntfnSc = some (L.mem s1 (nScA n)).bv := by rw [hysc, Notif.optRef_ne h1]
    obtain ⟨c, hcC, hcb⟩ := B.nsc n hn y _ hkn hysc'
    have hc' : c = L.mem s1 (nScA n) := P1.eq_of_bv hcb
    subst hc'
    obtain ⟨yc, k, hky, hy⟩ := hs.scs _ hcC
    have hyt : yc.scTcb = none := by rw [hy.tcb, Sched.scW_tcb, h2, Notif.optRef_zero]
    refine WP.spec_bind (hDn Ac Lst s1 a σr t n J hth hn ⟨x, hk, hxr, by rw [hsct, h0, Notif.optRef_zero]⟩
      ⟨y, _, yc, k, hkn, hidle, hb, hysc', hky, hyt⟩) ?_
    rintro ⟨s2, a2⟩ ⟨σ2, Ac2, Lst2, he2, hdt2, J2⟩
    exact rest s2 a2 σ2 Ac2 Lst2 he2 hdt2 J2
  have hmd : notification.maybe_donate_sched_context st arI s1 a t n = ok (s1, a) := by
    unfold notification.maybe_donate_sched_context
    rw [spec_eq_ok (Fl4Proofs.P1.obj.Tcb.sc.spec s1 t), bind_ok]
    by_cases h0 : L.mem s1 (scA t) = 0#u64
    · rw [if_pos h0, spec_eq_ok (Notif.obj.Ntfn.sc.spec s1 n), bind_ok, spec_eq_ok (Sched.obj.Sc.is_null.spec' _),
        bind_ok]
      by_cases h1 : L.mem s1 (nScA n) = 0#u64
      · rw [if_pos (decide_eq_true h1)]
      · rw [if_neg (show ¬ (decide (L.mem s1 (nScA n) = 0#u64) = true) from fun h => h1 (of_decide_eq_true h)),
          spec_eq_ok (Fl4Proofs.P1.obj.Sc.tcb.spec s1 _), bind_ok, if_neg (fun e => hdon ⟨h0, h1, e⟩)]
    · rw [if_neg h0]
  have hsp : Fl4Spec.maybeDonateSc (Z := Unit) t.bv n.bv σr = ({((), σr)}, False) := by
    by_cases h0 : L.mem s1 (scA t) = 0#u64
    · have hx0 : x.tcbSchedContext = none := by rw [hsct, h0, Notif.optRef_zero]
      by_cases h1 : L.mem s1 (nScA n) = 0#u64
      · exact stl_mds_nn hk hx0 hkn (by rw [hysc, h1, Notif.optRef_zero])
      · have h2 : L.mem s1 (scTcbA (L.mem s1 (nScA n))) ≠ 0#u64 := fun e => hdon ⟨h0, h1, e⟩
        have hysc' : y.ntfnSc = some (L.mem s1 (nScA n)).bv := by rw [hysc, Notif.optRef_ne h1]
        obtain ⟨c, hcC, hcb⟩ := B.nsc n hn y _ hkn hysc'
        have hc' : c = L.mem s1 (nScA n) := P1.eq_of_bv hcb
        subst hc'
        obtain ⟨yc, k, hky, hy⟩ := hs.scs _ hcC
        exact stl_mds_bound hk hx0 hkn hysc' hky (by rw [hy.tcb, Sched.scW_tcb, Notif.optRef_ne h2]; simp)
    · exact stl_mds_some hk (by rw [hsct, Notif.optRef_ne h0]; simp)
  rw [hmd, bind_ok]
  exact rest s1 a σr Ac Lst hsp rfl J

set_option maxHeartbeats 4000000 in
/-- **Gen 35's `JAtZV3.signalVmJ` with `SigVmDonJ3` for `SigVmTailJ3`** (module docstring). -/
theorem JAtZV3.signalVmJ2 (hAT : P0.ArchTotal arI) (hVA : ZvVirtAgree arI) (hK : ARKeep arI AR)
    (hDn : SigVmDonJ3 st arI V X AR Z H Cs D)
    (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {n : U64} (hn : n ∈ Z.N)
    {x : Fl4Spec.Notification} (hk : σ.kheap n.bv = some (.notification x)) (hidle : x.ntfnObj = .idleNtfn)
    {t : U64} (hb : x.ntfnBoundTcb = some t.bv) {y : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb y))
    (hrs : y.tcbState = .runningVM) (badge : U64) :
    notification.send_signal st arI s a n badge ⦃ r =>
      ∃ (σ' : Fl4Spec.State Unit) (Ac' : Set U64) (Lst' : U64 → List U64),
        Fl4Spec.sendSignalVF (Z := Unit) (v3OnCore st s) (v3RemCur st s) n.bv badge.bv σ = ({((), σ')}, False) ∧
        σ'.domainTime = σ.domainTime ∧ JAtZV3 (L := L) arI V X AR Z H Cs Ac' Lst' D r.1 r.2 σ' ⦄ :=
  J.signalVmJ hAT hVA hK (sigVmTailJ3_of hDn) hn hk hidle hb hkt hrs badge

end

end

end Fl4Proofs.P3
