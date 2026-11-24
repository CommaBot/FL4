/-
P3 (DESIGN.md §9), scheduling contexts: **SchedContext Unbind at `J`**
(`decode_invocation_sched_context_unbindJ`), proved at `J` directly (no
`XTop` producer of its own is needed: `JAtZ` carries `XTop`).

FL4's Unbind branch: the decode's prefix (the SC's thread read, the remote
stall a no-op, `hback`), the check that the SC is not bound to the caller
(l4v `decode_sched_context_invocation`'s `whenE (sc_tcb = Some ct)`, the
spec's `IllegalOperation` with the state unchanged), then
`set_thread_state Restart` of the caller (`JAtZ.restartJ`) and
`unbind_all_tcbs`, `unbind_ntfn`, `unbind_reply` of the SC
(`JAtZ.unbindAllJ`, `JAtZ.unbindNtfnJ`, `JAtZ.unbindReplyJ`), against the
spec's `set_thread_state Restart` and `invoke_sched_context`'s Unbind.

The mid-entry facts are the steps' own (`JAtZ` after each): unbinding a
thread that is the current one asks for a reschedule
(`JAtZ.unbindTcbJ`), and the current SC left without its thread is allowed
by `JAtZ` (XTopJointFinSc's module docstring). What `unbind_all_tcbs`
reads of the scheduler words (the SC's thread neither the action word nor
the idle word, `JAtZ.scWordsNS`) holds because the caller's restart leaves
no switch pending (`Entered` at the start) and the SC's thread holds the
SC, not the idle SC.
-/
import Fl4Proofs.P3.ScJointStep
import Fl4Proofs.P3.XTopJointTcb
import Fl4Proofs.P3.XTopJointFinSc
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- **An SC's thread word, as `unbind_all_tcbs` reads it**, with no switch
pending: the SC's thread (one of `Z.T` holding it, `scBack_of`) is not the
action word (`JAtZ.words_of_spec`) and not the idle word (the idle thread
holds the idle SC, `ActIdle`). -/
theorem JAtZ.scWordsNS {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {p : U64} (hpC : p ∈ Z.C) (hp0 : p ≠ 0#u64)
    (hpi : p.bv ≠ σ.idleSc) (hns : ∀ u, σ.schedulerAction = .switchThread u → False) :
    (L.mem s (P1.scTcbA p) ≠ 0#u64 → L.actionW s ≠ L.mem s (P1.scTcbA p)) ∧
      (L.mem s (P1.scTcbA p) ≠ 0#u64 → L.idleW s ≠ L.mem s (P1.scTcbA p)) := by
  have hw : L.mem s (P1.scTcbA p) ≠ 0#u64 →
      L.actionW s ≠ L.mem s (P1.scTcbA p) ∧ L.idleW s ≠ L.mem s (P1.scTcbA p) := by
    intro h0
    obtain ⟨Q, R, hc', hs⟩ := J.xtop.fin.1.1.1.lists
    obtain ⟨y, n, hk, hx⟩ := hs.scs p hpC
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    have hpS : p ∈ P1.Heap.scs H := ⟨_, (hJ.sc p y n hp0 hk).2⟩
    have hf : y.scTcb = some (L.mem s (P1.scTcbA p)).bv := by
      rw [hx.tcb, ← scTcbA_eq, Notif.optRef_ne h0]
    obtain ⟨u, huT, hu, x, hkx, hxs⟩ := scBack_of J.xtop.fin.1.1.1 J.blk.2.2.1 J.tcbs_eq.1.symm hpC hpS hp0 hk hf
    have hu' : u = L.mem s (P1.scTcbA p) := P1.eq_of_bv hu
    subst hu'
    refine J.words_of_spec huT (fun v e => (hns v e).elim) fun e => ?_
    obtain ⟨xi, hki, hsci, -⟩ := J.act.2
    rw [← e, hkx] at hki
    cases hki
    rw [hxs] at hsci
    exact hpi (Option.some.inj hsci)
  exact ⟨fun h => (hw h).1, fun h => (hw h).2⟩

set_option maxHeartbeats 8000000 in
/-- **Unbind's invocation at `J`** (module docstring): the caller's
restart (`JAtZ.restartJ`), then `unbind_all_tcbs`, `unbind_ntfn` and
`unbind_reply` of the SC at `J`; the spec's restart and Unbind. -/
theorem JAtZ.scUnbindJ {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) {sc : U64} (hsc : sc ∈ Z.C) (hpi : sc.bv ≠ σ.idleSc) :
    (do
      let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
      let (s3, a2) ← schedcontext.unbind_all_tcbs st arI s2 a sc
      let s4 ← schedcontext.unbind_ntfn st s3 sc
      let s5 ← schedcontext.unbind_reply st s4 sc
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s5, a2)) ⦃ res =>
      res.1 = .Ok () ∧ ∃ σ0 σ' : Fl4Spec.State Unit,
        Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ0)}, False) ∧
        Fl4Spec.invokeSchedContext (Z := Unit) (.invokeSchedContextUnbind sc.bv) σ0 = ({([], σ')}, False) ∧
        ∃ (Z' : XSets) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
          JAtZ (L := L) arI AR Z' H Cs Ac' Lst' D' res.2.1 res.2.2 σ' ⦄ := by
  obtain ⟨s1, σ1, x, -, he0, -, hcur, -, hns, -, -, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  rw [hs1]; simp only [bind_ok]
  have hp0 : sc ≠ 0#u64 := J1.c0 sc hsc
  have hpi1 : sc.bv ≠ σ1.idleSc := by
    rw [((pres_setThreadState (f := (true, true)) _ _).of_eq he0).isc]; exact hpi
  obtain ⟨hna, hidle⟩ := J1.scWordsNS hsc hp0 hpi1 hns
  refine WP.spec_bind (JAtZ.unbindAllJ arI J1 hsc hp0 hpi1 hna hidle) ?_
  rintro ⟨s2, a2⟩ ⟨σ2, he2, V2, Ac2, Lst2, D2, J2⟩
  refine WP.spec_bind (JAtZ.unbindNtfnJ arI J2 hsc hp0) ?_
  rintro s3 ⟨σ3, he3, V3, Ac3, Lst3, D3, J3⟩
  refine WP.spec_bind (JAtZ.unbindReplyJ arI J3 hsc hp0) ?_
  rintro s4 ⟨σ4, he4, V4, Ac4, Lst4, D4, J4⟩
  rw [WP.spec_ok]
  refine ⟨rfl, σ1, σ4, by rw [← hcur]; exact he0, ?_, _, Ac4, Lst4, D4, J4⟩
  show (Fl4Spec.schedContextUnbindAllTcbs sc.bv >>= _) σ1 = _
  rw [nd_bind_one he2, nd_bind_one he3, nd_bind_one he4]; rfl

set_option maxHeartbeats 8000000 in
/-- **The SchedContext cap's Unbind, `XCap` at `JAt`** (module docstring):
the fast-path flag's decode error and the caller-bound check's
`IllegalOperation` with `JAt` at the start; else the spec's decode, restart
and Unbind with `JAtZ` after (`JAtZ.scUnbindJ`). Premises: the front end's
label (`hlbl` [W], as every SC label's); the SC's facts are `JAtZ.scCtxCap`'s. -/
theorem decode_invocation_sched_context_unbindJ (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] (hni : Entered σ)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = scLabelOf lbl)
    (l42 : lbl = fl4_abi.label.SchedContextUnbind)
    {sc : U64} (sb : U64) (hsc : sc ∈ Z.C) (hpi : sc.bv ≠ σ.idleSc)
    (hback : L.mem s (scW sc 24#u64) ≠ 0#u64 →
      L.mem s (scW sc 24#u64) ∈ Z.T ∧ L.mem s (P1.scA (L.mem s (scW sc 24#u64))) = sc ∧
      (L.mem s (scW sc 24#u64)).bv ≠ σ.idleThread)
    {ct : U64} (hct : sched.cur_thread st s = ok ct)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (length slot buf : U64) (blk call don fp : Bool) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (JAt (L := L) arI AR) s a σ lbl length slot (.SchedContext sc sb) blk call don fp buf extra
      slbl args ci sl excaps buffer ct := by
  left
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R', hc, hs⟩ := hS.lists
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hct' : ct = nodeW st s Z.c layout.node.CUR_THREAD := by
    have h := sched.cur_thread.spec' (L := L) s
    rw [hct, WP.spec_ok, hc.cur] at h; exact h
  have hctT : ct ∈ Z.T := hct' ▸ hc.curT
  have hct0 : ct ≠ 0#u64 := fun e => (hc.tcbs ct hctT).ne0 (by rw [e]; rfl)
  obtain ⟨y, n, hk, hx⟩ := hs.scs sc hsc
  have hg : Fl4Spec.genInvocationType slbl = .schedContextUnbind := by
    rw [hlbl, l42]; unfold scLabelOf; simp
  have hpre : (Fl4Spec.decodeSchedContextInvocation (Z := Unit) slbl sc.bv (excaps.map Prod.fst)).run σ = (do
      let scx ← Fl4Spec.NonDetE.liftE <| Fl4Spec.getSchedContext sc.bv
      let ctPtr ← Fl4Spec.NonDetE.liftE <| Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curThread
      Fl4Spec.NonDetE.whenE (scx.scTcb = some ctPtr) <| Fl4Spec.NonDetE.throwError .illegalOperation
      Fl4Spec.NonDetE.returnOk <| .invokeSchedContextUnbind sc.bv :
        Fl4Spec.SEMonad Unit Fl4Spec.SchedContextInvocation).run σ := by
    unfold Fl4Spec.decodeSchedContextInvocation; rw [hg]
  rw [lE_bind (getSchedContext_eq hk), lE_bind (show Fl4Spec.NonDet.gets (fun s : Fl4Spec.State Unit => s.curThread) σ =
    ({(σ.curThread, σ)}, False) from rfl), hcur] at hpre
  unfold DecOKDMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  swap
  · simp only [↓reduceIte, WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, _, _, _, _, _, _, J, inferInstance⟩
  simp only [Bool.false_eq_true, ↓reduceIte]
  unfold schedcontext.decode
  step with P1.obj.Sc.tcb.spec as ⟨i, hi⟩
  rw [scTcbA_eq] at hi
  subst hi
  refine WP.spec_bind (show _ ⦃ r => r = (s, a) ⦄ from ?_) ?_
  · by_cases h0 : L.mem s (scW sc 24#u64) = 0#u64
    · have : (L.mem s (scW sc 24#u64) != 0#u64) = false := by simp [h0]
      simp only [this, Bool.false_eq_true, ↓reduceIte]; exact (WP.spec_ok _).mpr rfl
    · have : (L.mem s (scW sc 24#u64) != 0#u64) = true := by simp [h0]
      simp only [this, ↓reduceIte]; exact remote_tcb_stall_id (ar := arI) a hS (hback h0).1
  intro r hr
  subst hr
  show (sched.cur_thread st s >>= _) ⦃ _ ⦄
  rw [hct, bind_tc_ok]
  have l44 : lbl ≠ fl4_abi.label.SchedContextConsumed := lbl_ne l42 (by simp)
  have l41 : lbl ≠ fl4_abi.label.SchedContextBind := lbl_ne l42 (by simp)
  have l43 : lbl ≠ fl4_abi.label.SchedContextUnbindObject := lbl_ne l42 (by simp)
  rw [ite_eq_right l44, ite_eq_right l41, ite_eq_right l43, ite_eq_left l42]
  step with P1.obj.Sc.tcb.spec as ⟨i1, hi1⟩
  rw [scTcbA_eq] at hi1
  subst hi1
  by_cases he : L.mem s (scW sc 24#u64) = ct
  · rw [ite_eq_left he]
    refine illegal_ok s a _ (Or.inl ⟨_, rfl, rfl, ⟨.illegalOperation, ?_, Or.inl trivial⟩, _, _, _, _, _, _, J, inferInstance⟩)
    exact run_liftME_err (by
      rw [hpre]; exact wE_pos (by rw [hx.tcb]; exact (bv_optRef_some hct0).2 he) _ _ σ)
  rw [ite_eq_right he]
  have hrun : (Fl4Spec.decodeSchedContextInvocation (Z := Unit) slbl sc.bv (excaps.map Prod.fst)).run σ =
      ({(.ok (.invokeSchedContextUnbind sc.bv), σ)}, False) := by
    rw [hpre, wE_neg (fun h => he ((bv_optRef_some hct0).1 (hx.tcb ▸ h)))]; rfl
  refine WP.spec_mono (JAtZ.scUnbindJ J hni hct hsc hpi) ?_
  rintro r ⟨h1, σ0, σ', he0, he1, Z', Ac', Lst', D', J'⟩
  obtain ⟨hPl, hCR, hFI, hD, hMO, -, -⟩ := J'.xtop.rel
  exact Or.inr ⟨.invokeSchedContext (.invokeSchedContextUnbind sc.bv), DecOut.of_eq (run_liftME_ok hrun), σ0,
    by rw [hcur]; exact he0, (.ok [], σ'),
    mem_liftE (ε := Unit) (m := Fl4Spec.invokeSchedContext (Z := Unit) (.invokeSchedContextUnbind sc.bv)) (s := σ0)
      (x := ([], σ')) (by rw [he1]; exact Set.mem_singleton _),
    ⟨Z'.th, Z'.G, Or.inl ⟨h1, rfl⟩, hPl, hCR, hFI, hD, hMO⟩, ⟨_, _, _, _, _, _, J', inferInstance⟩⟩

end

end

end Fl4Proofs.P3
