/-
P3 (line mmuAD, gen 35): **`vcpu::check` at `JAtZV3`, paired with `vmCheckF`** (Fl4Spec/Ext/VirtReport: the VCPU
check as FL4 does it).

* Spec side: `v3_tcbVcpuOf_some`, `v3_repTail_cur`, `v3_jMrSt_cur`, **`JAtZV3.repCur`** (the spec's report keeps
  the current thread: P3/JAtZV3RepSpec's explicit outcomes, the buffer alignment from `BufCover`, as gen 34's
  `reportJ3M`); the outcomes of `vmCheckF` of a `runningVM` thread: `v3_vmCheckF_pend` (pending exit:
  `vmReportF t 0`), `v3_vmCheckF_act` (no pending exit (`NoPend`), active bound notification: made idle,
  `vmReportF t b`, no switch since `t` is current), `v3_vmCheckF_noact` (no pending exit, no active notification
  (`NoAct`): `when (no VCPU) (vmReportF t 0)`).
* **`JAtZV3.checkNP`**: FL4's no-pending-exit tail (bound notification read, `NTFN_ACTIVE` test, badge read,
  `set_state(NTFN_IDLE)` = P3/JAtZV3Ntfn's `ntfnIdle`, `report` = gen 34's `reportJ3`), verbatim in both places
  `vcpu.check` has it.
* **`JAtZV3.checkJ`**: the extracted `vcpu.check t` from `JAtZV3`, for the current thread (`σ.curThread = t`,
  the only caller: FL4 checks the current thread before entering it; `vmCheckF`'s `possibleSwitchTo` of a
  non-current thread is then skipped, as its docstring says) and a TCB of the typed heap: one outcome
  `vmCheckF t σ = {((), σ')}` and `JAtZV3` after, arch state unchanged.

Premises: [P] `ZvVirtAgree arI`, `P0.ArchTotal arI` (gen 34's, through `reportJ3`). Scope: `hcur`. No [J]; no
existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3Ntfn
import Fl4Proofs.P3.JAtZV3ReportJ3
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

section
open Fl4Spec Classical Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp

theorem v3_tcbVcpuOf_some {σ : State Unit} {t v : ObjRef} (h : tcbVcpuOf σ t = some v) :
    ∃ vs, σ.kheap v = some (.archObj (.vcpu vs)) := by
  unfold tcbVcpuOf at h
  split at h
  · rename_i hex
    cases h
    obtain ⟨st, h1, -⟩ := Classical.choose_spec hex
    exact ⟨st, VirtReportEq.kheap_of_vcpuAt h1⟩
  · cases h

theorem v3_repTail_cur (σ2 : State Unit) (t : ObjRef) (x1 : Tcb) (mi bd : Word) :
    (repTail σ2 t x1 mi bd).curThread = σ2.curThread := by
  unfold repTail
  show (stsAct _ t).curThread = _
  unfold stsAct
  split <;> rfl

theorem v3_jMrSt_cur (σ : State Unit) (t : ObjRef) (x : Tcb) (pb : Option ObjRef) (ms : List Word) :
    (jMrSt σ t x pb ms).curThread = σ.curThread := by
  cases pb <;> rfl

theorem v3_out_eq {α : Type} {A B : α} (h : (({A}, False) : Set α × Prop) = ({B}, False)) : A = B :=
  Set.singleton_injective (Prod.mk.inj h).1

/-- A `runningVM` thread with a pending exit: `vmCheckF t = vmReportF t 0`. -/
theorem v3_vmCheckF_pend {σ : State Unit} {t v : ObjRef} {x : Tcb} {vs : VcpuState}
    (hk : σ.kheap t = some (.tcb x)) (hs : x.tcbState = .runningVM) (hvo : tcbVcpuOf σ t = some v)
    (hkv : σ.kheap v = some (.archObj (.vcpu vs))) (hp : vs.exit.pending = true) :
    vmCheckF (Z := Unit) t σ = vmReportF t 0 σ := by
  unfold vmCheckF
  rw [nd_bind_one (getThreadState_eq hk)]
  unfold NonDet.when
  rw [if_pos hs, nd_bind_one (VirtReportEq.getTcbVcpu_eq σ t), hvo]
  dsimp only
  rw [nd_bind_one (zv_getVcpu_eq hkv), nd_pure_bind', hp]
  rfl

/-- No pending exit (no VCPU, or a VCPU without one): `pending` reads `false`. -/
def NoPend (σ : State Unit) (t : ObjRef) : Prop :=
  tcbVcpuOf σ t = none ∨ ∃ v vs, tcbVcpuOf σ t = some v ∧ σ.kheap v = some (.archObj (.vcpu vs)) ∧
    vs.exit.pending = false

/-- No pending exit, the bound notification active with badge `b`: made idle, `vmReportF t b`, no switch for the
current thread. -/
theorem v3_vmCheckF_act {σ : State Unit} {t n : ObjRef} {x : Tcb} {y : Notification} {b : Badge}
    (hk : σ.kheap t = some (.tcb x)) (hs : x.tcbState = .runningVM) (hnp : NoPend σ t)
    (hbn : x.tcbBoundNotification = some n) (hkn : σ.kheap n = some (.notification y))
    (hy : y.ntfnObj = .activeNtfn b) {σr : State Unit}
    (hr : vmReportF (Z := Unit) t b (updK σ n (.notification (ntfnObjUpdate (fun _ => .idleNtfn) y))) =
      ({((), σr)}, False)) (hcur : σr.curThread = t) :
    vmCheckF (Z := Unit) t σ = ({((), σr)}, False) := by
  unfold vmCheckF
  rw [nd_bind_one (getThreadState_eq hk)]
  unfold NonDet.when
  rw [if_pos hs, nd_bind_one (VirtReportEq.getTcbVcpu_eq σ t)]
  rcases hnp with hvo | ⟨v, vs, hvo, hkv, hp⟩
  · rw [hvo]
    dsimp only
    rw [nd_pure_bind', if_neg Bool.false_ne_true, nd_bind_one (getTcbObjRef_eq _ hk), hbn]
    dsimp only
    rw [nd_bind_one (getNotification_eq hkn), nd_pure_bind', hy]
    dsimp only
    rw [nd_bind_one (setNotification_eq _ hkn), nd_bind_one hr, nd_gets_bind, hcur, if_neg (by simp)]
    rfl
  · rw [hvo]
    dsimp only
    rw [nd_bind_one (zv_getVcpu_eq hkv), nd_pure_bind', hp, if_neg Bool.false_ne_true,
      nd_bind_one (getTcbObjRef_eq _ hk), hbn]
    dsimp only
    rw [nd_bind_one (getNotification_eq hkn), nd_pure_bind', hy]
    dsimp only
    rw [nd_bind_one (setNotification_eq _ hkn), nd_bind_one hr, nd_gets_bind, hcur, if_neg (by simp)]
    rfl

/-- The bound notification is not active (or there is none). -/
def NoAct (σ : State Unit) (x : Tcb) : Prop :=
  x.tcbBoundNotification = none ∨ ∃ n y, x.tcbBoundNotification = some n ∧ σ.kheap n = some (.notification y) ∧
    ∀ b, y.ntfnObj ≠ .activeNtfn b

theorem v3_vmCheckF_noact {σ : State Unit} {t : ObjRef} {x : Tcb}
    (hk : σ.kheap t = some (.tcb x)) (hs : x.tcbState = .runningVM) (hnp : NoPend σ t) (hna : NoAct σ x) :
    vmCheckF (Z := Unit) t σ = NonDet.when (tcbVcpuOf σ t = none) (vmReportF t 0) σ := by
  have tail : ∀ (vo : Option ObjRef), (do
      let nOpt ← getTcbObjRef Tcb.tcbBoundNotification t
      let nb ← match nOpt with
        | some n => do
          let ntfn ← getNotification n
          pure (match ntfn.ntfnObj with
            | .activeNtfn b => some (n, ntfn, b)
            | _ => none)
        | none => pure none
      match nb with
      | some (n, ntfn, b) => do
        setNotification n <| ntfnObjUpdate (fun _ => .idleNtfn) ntfn
        vmReportF t b
        let cur ← NonDet.gets fun s : State Unit => s.curThread
        NonDet.when (t ≠ cur) <| possibleSwitchTo t
      | none => NonDet.when (vo = none) <| vmReportF t 0 : NonDet (State Unit) Unit) σ =
        NonDet.when (vo = none) (vmReportF t 0) σ := by
    intro vo
    rw [nd_bind_one (getTcbObjRef_eq _ hk)]
    rcases hna with hbn | ⟨n, y, hbn, hkn, hy⟩
    · rw [hbn]
      dsimp only
      rw [nd_pure_bind']
    · rw [hbn]
      dsimp only
      rw [nd_bind_one (getNotification_eq hkn), nd_pure_bind']
      cases ho : y.ntfnObj with
      | activeNtfn b => exact absurd ho (hy b)
      | idleNtfn => rfl
      | waitingNtfn l => rfl
  unfold vmCheckF
  rw [nd_bind_one (getThreadState_eq hk)]
  unfold NonDet.when
  rw [if_pos hs, nd_bind_one (VirtReportEq.getTcbVcpu_eq σ t)]
  rcases hnp with hvo | ⟨v, vs, hvo, hkv, hp⟩
  · rw [hvo]
    dsimp only
    rw [nd_pure_bind', if_neg Bool.false_ne_true]
    exact tail none
  · rw [hvo]
    dsimp only
    rw [nd_bind_one (zv_getVcpu_eq hkv), nd_pure_bind', hp, if_neg Bool.false_ne_true]
    exact tail (some v)

end

section
open Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

set_option maxHeartbeats 4000000 in
/-- **The spec's report keeps the current thread** (module docstring). -/
theorem JAtZV3.repCur (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {t : U64}
    (ht : Z.th t = some .tcb) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) {b : Fl4Spec.Word}
    {σr : Fl4Spec.State Unit} (hr : Fl4Spec.vmReportF (Z := Unit) t.bv b σ = ({((), σr)}, False)) :
    σr.curThread = σ.curThread := by
  have B := J.z2.zv.base
  have htT := B.thT t ht
  have hOK := B.bok
  have hBC := bufCover_of_frameCover (T := Z.T) B.bok B.fcov
  have hEP := B.xtop.fin.1.2.ep
  have halG : ∀ ms : List Fl4Spec.Word, ∀ p, Endp.ipcBufOf true x = some p → ∀ q ∈ Endp.mrPairs ms,
      (Endp.bufAddr p q.1).toNat % 8 = 0 ∧ Fl4Spec.inUserFrame (Endp.bufAddr p q.1) σ := by
    intro ms p hp q hq
    have := (List.of_mem_zip hq).1
    simp at this
    have hm : Endp.BufMap Z.B ({ bv := p } : U64) p := hBC t htT x true p hk hp { bv := p } rfl
    exact ⟨Endp.bufAddr_aligned hEP hm _, buf_frame_of_ok hOK hk hp _ (by omega)⟩
  cases hvo : Fl4Spec.tcbVcpuOf σ t.bv with
  | none =>
    rw [v3_vmReportF_none hk hvo b (halG _)] at hr
    have e := congrArg Prod.snd (v3_out_eq hr)
    dsimp only at e
    rw [← e, v3_repTail_cur, v3_jMrSt_cur]
  | some v =>
    obtain ⟨vs, hkv⟩ := v3_tcbVcpuOf_some hvo
    rw [v3_vmReportF_some hk hvo hkv b (halG _)] at hr
    have e := congrArg Prod.snd (v3_out_eq hr)
    dsimp only at e
    rw [← e, v3_repTail_cur]
    split
    · show (jMrSt σ t.bv x _ _).curThread = _
      exact v3_jMrSt_cur _ _ _ _ _
    · exact v3_jMrSt_cur _ _ _ _ _

set_option maxHeartbeats 8000000 in
/-- **`vcpu::check`'s tail without a pending exit** (module docstring). `v` is FL4's TCB VCPU word. -/
theorem JAtZV3.checkNP (hA : P0.ArchTotal arI) (hVA : ZvVirtAgree arI)
    (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : Z.th t = some .tcb)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hrs : x.tcbState = .runningVM)
    (hcur : σ.curThread = t.bv) (hnp : NoPend σ t.bv) {v : U64}
    (hv0 : v = 0#u64 ↔ Fl4Spec.tcbVcpuOf σ t.bv = none) :
    (do
      let i1 ← obj.Tcb.bound_ntfn st t s
      if i1 != 0#u64
      then
        let i2 ← obj.Ntfn.state st i1 s
        if i2 = obj.NTFN_ACTIVE
        then
          let badge ← obj.Ntfn.badge st i1 s
          let s1 ← obj.Ntfn.set_state st i1 s obj.NTFN_IDLE
          let s2 ← vcpu.report st arI s1 a t badge
          ok (s2, a)
        else
          if v = 0#u64
          then
            let s1 ← vcpu.report st arI s a t 0#u64
            ok (s1, a)
          else ok (s, a)
      else
        if v = 0#u64
        then
          let s1 ← vcpu.report st arI s a t 0#u64
          ok (s1, a)
        else ok (s, a)) ⦃ r => ∃ (σ' : Fl4Spec.State Unit) (Ac' : Set U64) (Lst' : U64 → List U64),
          Fl4Spec.vmCheckF (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
          JAtZV3 (L := L) arI V X AR Z H Cs Ac' Lst' D r.1 r.2 σ' ∧ r.2 = a ⦄ := by
  have B := J.z2.zv.base
  have htT := B.thT t ht
  have hI := B.xtop.irelK B.ks B.buf
  obtain ⟨x', hk', hR⟩ := B.xtop.ipc.tcb t htT
  rw [hk] at hk'; cases hk'
  have hbnd : x.tcbBoundNotification = optRef (L.mem s (P1.boundA t)) := hR.bound
  -- the report of `t` with badge 0 from `σ` (no active notification)
  have REP0 : NoAct σ x → Fl4Spec.tcbVcpuOf σ t.bv = none →
      (do
        let s1 ← vcpu.report st arI s a t 0#u64
        ok (s1, a)) ⦃ r => ∃ (σ' : Fl4Spec.State Unit) (Ac' : Set U64) (Lst' : U64 → List U64),
          Fl4Spec.vmCheckF (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
          JAtZV3 (L := L) arI V X AR Z H Cs Ac' Lst' D r.1 r.2 σ' ∧ r.2 = a ⦄ := by
    intro hna hvo
    refine WP.spec_bind (J.reportJ3 hA hVA ht ⟨x, hk, hrs⟩ 0#u64) ?_
    rintro s1 ⟨σr, Ac', Lst', hr, J1, -, -⟩
    refine (WP.spec_ok _).2 ⟨σr, Ac', Lst', ?_, J1, rfl⟩
    rw [v3_vmCheckF_noact hk hrs hnp hna]
    unfold Fl4Spec.NonDet.when
    rw [if_pos hvo]
    exact hr
  have KEEP : NoAct σ x → Fl4Spec.tcbVcpuOf σ t.bv ≠ none →
      (ok (s, a) : Result (S × A)) ⦃ r => ∃ (σ' : Fl4Spec.State Unit) (Ac' : Set U64) (Lst' : U64 → List U64),
          Fl4Spec.vmCheckF (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
          JAtZV3 (L := L) arI V X AR Z H Cs Ac' Lst' D r.1 r.2 σ' ∧ r.2 = a ⦄ := by
    intro hna hvo
    refine (WP.spec_ok _).2 ⟨σ, Ac, Lst, ?_, J, rfl⟩
    rw [v3_vmCheckF_noact hk hrs hnp hna]
    unfold Fl4Spec.NonDet.when
    rw [if_neg hvo]
    rfl
  have NOACT : NoAct σ x →
      (if v = 0#u64
        then do
          let s1 ← vcpu.report st arI s a t 0#u64
          ok (s1, a)
        else ok (s, a)) ⦃ r => ∃ (σ' : Fl4Spec.State Unit) (Ac' : Set U64) (Lst' : U64 → List U64),
          Fl4Spec.vmCheckF (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
          JAtZV3 (L := L) arI V X AR Z H Cs Ac' Lst' D r.1 r.2 σ' ∧ r.2 = a ⦄ := by
    intro hna
    by_cases e : v = 0#u64
    · rw [if_pos e]; exact REP0 hna (hv0.1 e)
    · rw [if_neg e]; exact KEEP hna fun h => e (hv0.2 h)
  refine WP.spec_bind (P1.obj.Tcb.bound_ntfn.val s t) fun i1 ei1 => ?_
  by_cases hn0 : i1 = 0#u64
  · rw [if_neg (by simp [hn0])]
    refine NOACT (Or.inl ?_)
    rw [hbnd, ← ei1, hn0, Notif.optRef_zero]
  rw [if_pos (by simp [hn0])]
  -- the bound notification
  have hnH : i1 ∈ P1.Heap.ntfns H := by
    obtain ⟨-, -, hX, -, -⟩ := B.blk
    rw [ei1]
    exact hX.2.2.bnd t (B.zH.1 t htT) (by rw [← ei1]; exact hn0)
  have hnN : i1 ∈ Z.N := B.hset.2.1 i1 hnH
  obtain ⟨y, hkn, -⟩ := B.xtop.ipc.toN.ntfn i1 hnN
  have hx := hI.1.toN.at_ntfn hnN hkn
  have hbn : x.tcbBoundNotification = some i1.bv := by rw [hbnd, ← ei1, Notif.optRef_ne hn0]
  refine WP.spec_bind (P1.obj.Ntfn.state.spec s i1) fun i2 ei2 => ?_
  rw [epState_eq] at ei2
  cases ho : y.ntfnObj with
  | activeNtfn b0 =>
    have hst : i2 = obj.NTFN_ACTIVE := by rw [ei2]; exact stOf_active hx.obj ho
    rw [if_pos hst]
    have hb0 : (L.mem s (nBadgeA i1)).bv = b0 := by
      have := hx.obj; rw [ho] at this; exact this.2.2
    refine WP.spec_bind (Notif.obj.Ntfn.badge.spec s i1) fun bd ebd => ?_
    subst ebd
    refine WP.spec_bind (J.ntfnIdle hnN hkn ho) fun s1 J1 => ?_
    have hnt : i1.bv ≠ t.bv := by intro e; rw [e, hk] at hkn; cases hkn
    have hk1 : (updK σ i1.bv (.notification (Fl4Spec.ntfnObjUpdate (fun _ => .idleNtfn) y))).kheap t.bv =
        some (.tcb x) := by simp [updK, hnt.symm, hk]
    refine WP.spec_bind (J1.reportJ3 hA hVA ht ⟨x, hk1, hrs⟩ (L.mem s (nBadgeA i1)))
      ?_
    rintro s2 ⟨σr, Ac', Lst', hr, J2, -, -⟩
    refine (WP.spec_ok _).2 ⟨σr, Ac', Lst', ?_, J2, rfl⟩
    rw [hb0] at hr
    exact v3_vmCheckF_act hk hrs hnp hbn hkn ho hr ((J1.repCur ht hk1 hr).trans hcur)
  | idleNtfn =>
    have hst : i2 ≠ obj.NTFN_ACTIVE := by
      rw [ei2, stOf_idle hx.obj ho]; unfold obj.NTFN_ACTIVE obj.NTFN_IDLE; decide
    rw [if_neg hst]
    exact NOACT (Or.inr ⟨i1.bv, y, hbn, hkn, fun b e => by rw [ho] at e; cases e⟩)
  | waitingNtfn l =>
    have hst : i2 ≠ obj.NTFN_ACTIVE := by
      rw [ei2, stOf_waiting hx.obj ho]; unfold obj.NTFN_ACTIVE obj.NTFN_WAITING; decide
    rw [if_neg hst]
    exact NOACT (Or.inr ⟨i1.bv, y, hbn, hkn, fun b e => by rw [ho] at e; cases e⟩)

set_option maxHeartbeats 8000000 in
/-- **`vcpu::check` of the current thread at `JAtZV3`, paired with `vmCheckF`** (module docstring). -/
theorem JAtZV3.checkJ (hA : P0.ArchTotal arI) (hVA : ZvVirtAgree arI)
    (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : Z.th t = some .tcb)
    (hcur : σ.curThread = t.bv) :
    vcpu.check st arI s a t ⦃ r => ∃ (σ' : Fl4Spec.State Unit) (Ac' : Set U64) (Lst' : U64 → List U64),
      Fl4Spec.vmCheckF (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
      JAtZV3 (L := L) arI V X AR Z H Cs Ac' Lst' D r.1 r.2 σ' ∧ r.2 = a ⦄ := by
  have Jz := J.z2.zv
  have B := Jz.base
  have hO := J.vo
  obtain ⟨x, hk, hwst⟩ := B.specTcb ht
  unfold vcpu.check
  refine WP.spec_bind (P1.obj.Tcb.state.spec s t) fun i ei => ?_
  by_cases hrs : x.tcbState = .runningVM
  swap
  · have hne : (i != sched.TS_RUNNING_VM) = true := by
      rw [ei]
      have h8 : L.mem s (P1.stA t) ≠ 8#u64 := by
        intro e
        have := congrArg UScalar.val e
        rw [hwst] at this
        revert hrs this
        cases x.tcbState <;> simp [Notif.tsCode]
      simpa [sched.TS_RUNNING_VM] using h8
    rw [if_pos hne]
    exact (WP.spec_ok _).2 ⟨σ, Ac, Lst, VirtReportEq.vmCheckF_not_runningVM hk hrs, J, rfl⟩
  have h8 : L.mem s (P1.stA t) = 8#u64 := by
    apply UScalar.eq_of_val_eq
    rw [hwst, hrs]
    simp [Notif.tsCode]
  rw [if_neg (by rw [ei, h8]; simp [sched.TS_RUNNING_VM])]
  refine WP.spec_bind (v3_bound s t) fun v ev' => ?_
  by_cases hv0 : v = 0#u64
  · have h0 : L.mem s (tVcpuA t) = 0#u64 := ev'.symm.trans hv0
    have hTV : Fl4Spec.tcbVcpuOf σ t.bv = none := zv_tcbVcpuOf_none fun w ws hw hwt => by
      obtain ⟨u, hu, -, h1, -⟩ := J.z2.specBound hO ht hw hwt
      exact Jz.extv.nz u hu (h1.symm.trans h0)
    rw [if_neg (by simp [hv0])]
    exact J.checkNP hA hVA ht hk hrs hcur (Or.inl hTV) ⟨fun _ => hTV, fun _ => hv0⟩
  · have hne0 : L.mem s (tVcpuA t) ≠ 0#u64 := fun h => hv0 (ev'.trans h)
    obtain ⟨hvV, hvt⟩ := (Jz.extv.bnd t ht).resolve_left hne0
    rw [← ev'] at hvV hvt
    obtain ⟨vs, hkv, hbv⟩ := J.z2.vb v hvV
    have hvs : Fl4Spec.VcpuState.tcb vs = some t.bv := by
      rcases hbv with ⟨-, h0⟩ | ⟨t', -, h1, h2⟩
      · have e : t = 0#u64 := hvt.symm.trans h0
        subst e
        exact absurd ht (B.detPl Jz.vm).h0
      · have e : t' = t := h2.symm.trans hvt
        rw [h1, e]
    have hTV : Fl4Spec.tcbVcpuOf σ t.bv = some v.bv := zv_tcbVcpuOf_eq hkv hvs fun w ws hw hwt => by
      obtain ⟨u, hu, rfl, h1, -⟩ := J.z2.specBound hO ht hw hwt
      rw [← h1, ← ev']
    rw [if_pos (by simp [hv0]), v3_get_eq, bind_ok]
    have hpd := J.rdPend hvV hkv
    by_cases hp : vs.exit.pending = true
    · rw [if_pos (by rw [hpd, hp])]
      refine WP.spec_bind (J.reportJ3 hA hVA ht ⟨x, hk, hrs⟩ 0#u64) ?_
      rintro s1 ⟨σr, Ac', Lst', hr, J1, -, -⟩
      refine (WP.spec_ok _).2 ⟨σr, Ac', Lst', ?_, J1, rfl⟩
      rw [v3_vmCheckF_pend hk hrs hTV hkv hp]
      exact hr
    · have hp' : vs.exit.pending = false := by simpa using hp
      rw [if_neg (by rw [hpd, hp']; simp)]
      exact J.checkNP hA hVA ht hk hrs hcur (Or.inr ⟨v.bv, vs, hTV, hkv, hp'⟩)
        ⟨fun e => absurd e hv0, fun e => by rw [hTV] at e; cases e⟩

end

end

end Fl4Proofs.P3
