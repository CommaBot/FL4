/-
P3 (line mmuAD, gen 35): **pieces of `send_signal` for a `RunningVM` bound thread at `JAtZV3`**, against the
extended spec's `sendSignalVF` (Fl4Spec/Ext/VirtReport: on x86 FL4's `send_signal` is `sendSignalVF`, virt gen 14).

* `v3OnCore st s`, `v3RemCur st s`: the two oracles of `sendSignalVF` read off FL4's state (the thread's affinity is the
  executing core; the thread is the current thread of its own core: `CUR_THREAD` of its affinity's node).
* Spec side: `v3_sigComp_none` / `v3_sigComp_some` (`vmSignalCompletes`, deterministic), `v3_ssVF_nc` (the signal
  does not complete the VMEnter: `sendSignalVF` = the ported `sendSignal`), `sigVmTailS` (the spec's tail after
  `vmReportF`: donation, switch, sporadic check, verbatim from `sendSignalVF`), `v3_ssVF_comp` (it completes:
  `sendSignalVF` = `vmReportF` then `sigVmTailS`), `v3_stsAct_kheap`, `v3_repTail_kh` / `v3_repTail_kt`,
  **`JAtZV3.repKh`** (the spec's report changes only the thread, its VCPU and memory; the thread ends `running`).
* FL4 side: `sigVmTailF` (FL4's tail after `vcpu::report`, verbatim from the extracted `send_signal`),
  **`JAtZV3.sigCompR`** (FL4's `vcpu.signal_completes t` = the spec's `vmSignalCompletes (v3OnCore st s) (v3RemCur st s)
  t`), `v3_kick` (`kick_guest` writes nothing and keeps `AR`, by `ARKeep.send_reschedule`).

No premise beyond those named in each statement ([P] `ARKeep`); no existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3Check
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

section
variable {S : Type}

/-- `sendSignalVF`'s `onCore`, read off FL4's state: the thread's affinity is the executing core. -/
def v3OnCore (st : machine.Store S) [L : P1.LawfulStore st] (s : S) (t : Fl4Spec.ObjRef) : Bool := decide (L.mem s (P1.affA ({ bv := t } : U64)) = L.cpu s)

/-- `sendSignalVF`'s `remoteCur`, read off FL4's state: the thread is the current thread of its own core. -/
def v3RemCur (st : machine.Store S) [L : P1.LawfulStore st] (s : S) (t : Fl4Spec.ObjRef) : Bool :=
  decide (L.mem s (L.nodeAt s (L.mem s (P1.affA ({ bv := t } : U64))) layout.node.CUR_THREAD) = ({ bv := t } : U64))

end

section
open Fl4Spec Classical Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp

theorem v3_sigComp_none {σ : State Unit} {t : ObjRef} (on rc : ObjRef → Bool) (hvo : tcbVcpuOf σ t = none) :
    vmSignalCompletes (Z := Unit) on rc t σ = ({(false, σ)}, False) := by
  unfold vmSignalCompletes
  rw [nd_bind_one (VirtReportEq.getTcbVcpu_eq σ t), hvo]
  rfl

theorem v3_sigComp_some {σ : State Unit} {t v : ObjRef} {x : Tcb} {vs : VcpuState} (on rc : ObjRef → Bool)
    (hk : σ.kheap t = some (.tcb x)) (hvo : tcbVcpuOf σ t = some v)
    (hkv : σ.kheap v = some (.archObj (.vcpu vs))) :
    vmSignalCompletes (Z := Unit) on rc t σ = ({(decide (vs.exit.pending = false ∧ (on t = true ∨
      (decide (x.tcbArch.tcbContext.userRegs msg_info_register = 30) = true ∧ rc t = false))), σ)}, False) := by
  unfold vmSignalCompletes
  rw [nd_bind_one (VirtReportEq.getTcbVcpu_eq σ t), hvo]
  dsimp only
  rw [nd_bind_one (zv_getVcpu_eq hkv), nd_bind_one (VirtReportEq.vmFullReply_eq hk)]
  rfl

/-- The signal does not complete the VMEnter: `sendSignalVF` is the ported `sendSignal`. -/
theorem v3_ssVF_nc {σ : State Unit} {n t : ObjRef} {x : Notification} {y : Tcb} {c : Bool}
    (on rc : ObjRef → Bool) (b : Badge)
    (hk : σ.kheap n = some (.notification x)) (hidle : x.ntfnObj = .idleNtfn) (hb : x.ntfnBoundTcb = some t)
    (hkt : σ.kheap t = some (.tcb y)) (hc : vmSignalCompletes (Z := Unit) on rc t σ = ({(c, σ)}, False))
    (hnc : ¬ (y.tcbState = .runningVM ∧ c = true)) :
    sendSignalVF (Z := Unit) on rc n b σ = sendSignal n b σ := by
  unfold sendSignalVF
  rw [nd_bind_one (getNotification_eq hk), hidle, hb]
  dsimp only
  rw [nd_bind_one (getThreadState_eq hkt), nd_bind_one hc, if_neg hnc]

/-- The spec's tail of `sendSignalVF` after `vmReportF` (verbatim). -/
def sigVmTailS (ntfnptr tcb : ObjRef) : SMonad Unit Unit := do
  maybeDonateSc tcb ntfnptr
  let sched ← NonDet.gets (schedulable tcb)
  NonDet.when sched <| possibleSwitchTo tcb
  let scOpt ← getTcbObjRef Tcb.tcbSchedContext tcb
  NonDet.maybeM (fun scp => do
      let active ← getScActive scp
      NonDet.when active <| do
        let sc ← getSchedContext scp
        let ntfnScp ← getNtfnObjRef Notification.ntfnSc ntfnptr
        let curScPtr ← NonDet.gets fun s : State Unit => s.curSc
        NonDet.when (scOpt = ntfnScp ∧ sc.scSporadic ∧ scp ≠ curScPtr) <| refillUnblockCheck scp)
    scOpt

/-- The signal completes the VMEnter: `sendSignalVF` is `vmReportF` then `sigVmTailS`. -/
theorem v3_ssVF_comp {σ σr : State Unit} {n t : ObjRef} {x : Notification} {y : Tcb}
    (on rc : ObjRef → Bool) (b : Badge)
    (hk : σ.kheap n = some (.notification x)) (hidle : x.ntfnObj = .idleNtfn) (hb : x.ntfnBoundTcb = some t)
    (hkt : σ.kheap t = some (.tcb y)) (hc : vmSignalCompletes (Z := Unit) on rc t σ = ({(true, σ)}, False))
    (hrs : y.tcbState = .runningVM) (hr : vmReportF (Z := Unit) t b σ = ({((), σr)}, False)) :
    sendSignalVF (Z := Unit) on rc n b σ = sigVmTailS n t σr := by
  unfold sendSignalVF
  rw [nd_bind_one (getNotification_eq hk), hidle, hb]
  dsimp only
  rw [nd_bind_one (getThreadState_eq hkt), nd_bind_one hc, if_pos ⟨hrs, rfl⟩, nd_bind_one hr]
  rfl

theorem v3_stsAct_kheap (σ : State Unit) (t : ObjRef) : (stsAct σ t).kheap = σ.kheap := by
  unfold stsAct; split <;> rfl

theorem v3_repTail_kh (σ2 : State Unit) (t : ObjRef) (x1 : Tcb) (mi bd : Word) {o : ObjRef} (ho : o ≠ t) :
    (repTail σ2 t x1 mi bd).kheap o = σ2.kheap o := by
  unfold repTail
  simp only [updK_kheap, Function.update_of_ne ho, v3_stsAct_kheap]

theorem v3_repTail_kt (σ2 : State Unit) (t : ObjRef) (x1 : Tcb) (mi bd : Word) :
    ∃ y, (repTail σ2 t x1 mi bd).kheap t = some (.tcb y) ∧ y.tcbState = .running := by
  unfold repTail
  simp only [updK_kheap, Function.update_self]
  exact ⟨_, rfl, rfl⟩

theorem v3_repTail_dt (σ2 : State Unit) (t : ObjRef) (x1 : Tcb) (mi bd : Word) :
    (repTail σ2 t x1 mi bd).domainTime = σ2.domainTime := by
  unfold repTail
  show (stsAct _ t).domainTime = _
  unfold stsAct
  split <;> rfl

theorem v3_jMrSt_dt (σ : State Unit) (t : ObjRef) (x : Tcb) (pb : Option ObjRef) (ms : List Word) :
    (jMrSt σ t x pb ms).domainTime = σ.domainTime := by
  cases pb <;> rfl

theorem v3_jMrSt_kh (σ : State Unit) (t : ObjRef) (x : Tcb) (pb : Option ObjRef) (ms : List Word) {o : ObjRef}
    (ho : o ≠ t) : (jMrSt σ t x pb ms).kheap o = σ.kheap o := by
  cases pb with
  | none => simp only [jMrSt, mrStateN, updK_kheap, Function.update_of_ne ho]
  | some p =>
    simp only [jMrSt, mrState]
    show (updK σ t _).kheap o = _
    simp only [updK_kheap, Function.update_of_ne ho]

end

section
open Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

set_option maxHeartbeats 4000000 in
/-- **The spec's report changes only the thread and a VCPU object; the thread ends `running`** (module docstring). -/
theorem JAtZV3.repKh (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {t : U64}
    (ht : Z.th t = some .tcb) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) {b : Fl4Spec.Word}
    {σr : Fl4Spec.State Unit} (hr : Fl4Spec.vmReportF (Z := Unit) t.bv b σ = ({((), σr)}, False)) :
    (∀ o, o ≠ t.bv → (∀ vs, σ.kheap o ≠ some (.archObj (.vcpu vs))) → σr.kheap o = σ.kheap o) ∧
    (∃ y, σr.kheap t.bv = some (.tcb y) ∧ y.tcbState = .running) ∧ σr.domainTime = σ.domainTime := by
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
    rw [← e]
    exact ⟨fun o ho _ => by rw [v3_repTail_kh _ _ _ _ _ ho, v3_jMrSt_kh _ _ _ _ _ ho], v3_repTail_kt _ _ _ _ _,
      by rw [v3_repTail_dt, v3_jMrSt_dt]⟩
  | some v =>
    obtain ⟨vs, hkv⟩ := v3_tcbVcpuOf_some hvo
    rw [v3_vmReportF_some hk hvo hkv b (halG _)] at hr
    have e := congrArg Prod.snd (v3_out_eq hr)
    dsimp only at e
    rw [← e]
    refine ⟨fun o ho hnv => ?_, v3_repTail_kt _ _ _ _ _, ?_⟩
    swap
    · rw [v3_repTail_dt]
      split
      · show (jMrSt σ t.bv x _ _).domainTime = _
        exact v3_jMrSt_dt _ _ _ _ _
      · exact v3_jMrSt_dt _ _ _ _ _
    rw [v3_repTail_kh _ _ _ _ _ ho]
    have hov : o ≠ v := fun e => hnv vs (by rw [e]; exact hkv)
    split
    · simp only [updK_kheap, Function.update_of_ne hov]
      exact v3_jMrSt_kh _ _ _ _ _ ho
    · exact v3_jMrSt_kh _ _ _ _ _ ho

/-- FL4's tail of `send_signal` after `vcpu::report` (verbatim from the extracted `send_signal`; since FL4 #114 the
sporadic `unblock_check` is skipped for a thread in the release queue, `sched.in_release_queue`). -/
def sigVmTailF (st : machine.Store S) (arI : machine.Arch A) (s1 : S) (a : A) (i : obj.Tcb) (n_ptr : U64) :
    Result (S × A) := do
  let (s2, a1) ← notification.maybe_donate_sched_context st arI s1 a i n_ptr
  let b2 ← sched.is_schedulable st s2 i
  let s3 ← if b2 then sched.possible_switch_to st s2 i else ok s2
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

/-- `kick_guest` writes nothing and keeps `AR` (`ARKeep.send_reschedule`). -/
theorem v3_kick (hAT : P0.ArchTotal arI) (hK : ARKeep arI AR) {c : Fl4Spec.Cr3} (s : S) (a : A) (t : obj.Tcb)
    (h : AR a c) : notification.kick_guest st arI s a t ⦃ r => r.1 = s ∧ AR r.2 c ⦄ := by
  have hS0 : P0.StoreTotal st := L.total
  unfold notification.kick_guest
  refine WP.spec_bind (P1.obj.Tcb.affinity.spec (st := st) s t) fun cpu _ => ?_
  refine WP.spec_bind (P1.LawfulStore.cur_cpu_spec (st := st) s) fun c' _ => ?_
  split
  · refine WP.spec_bind (P1.obj.node_get.spec (st := st) s _ _) fun _ _ => ?_
    split
    · simp only [lift, bind_ok]
      refine WP.spec_bind (Pₘ := fun _ => True) (by p0_auto) fun _ _ => ?_
      exact WP.spec_bind (hK.send_reschedule _ _ _ h) fun a' ha' => (WP.spec_ok _).2 ⟨rfl, ha'⟩
    · exact (WP.spec_ok _).2 ⟨rfl, h⟩
  · exact (WP.spec_ok _).2 ⟨rfl, h⟩

set_option maxHeartbeats 8000000 in
/-- **FL4's `signal_completes` is the spec's `vmSignalCompletes` with the oracles read off FL4's state** (module
docstring). -/
theorem JAtZV3.sigCompR (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {t : U64}
    (ht : Z.th t = some .tcb) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) :
    vcpu.signal_completes st s t ⦃ b =>
      Fl4Spec.vmSignalCompletes (Z := Unit) (v3OnCore st s) (v3RemCur st s) t.bv σ = ({(b, σ)}, False) ⦄ := by
  have Jz := J.z2.zv
  have B := Jz.base
  have hO := J.vo
  have htT := B.thT t ht
  unfold vcpu.signal_completes
  refine WP.spec_bind (v3_bound s t) fun v ev' => ?_
  refine WP.spec_bind (P1.obj.Tcb.affinity.spec s t) fun cpu ecpu => ?_
  by_cases hv0 : v = 0#u64
  · have h0 : L.mem s (tVcpuA t) = 0#u64 := ev'.symm.trans hv0
    have hTV : Fl4Spec.tcbVcpuOf σ t.bv = none := zv_tcbVcpuOf_none fun w ws hw hwt => by
      obtain ⟨u, hu, -, h1, -⟩ := J.z2.specBound hO ht hw hwt
      exact Jz.extv.nz u hu (h1.symm.trans h0)
    rw [if_neg (by simp [hv0])]
    exact (WP.spec_ok _).2 (v3_sigComp_none _ _ hTV)
  have hne0 : L.mem s (tVcpuA t) ≠ 0#u64 := fun h => hv0 (ev'.trans h)
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
  have hS := v3_sigComp_some (v3OnCore st s) (v3RemCur st s) hk hTV hkv
  rw [if_pos (by simp [hv0]), v3_get_eq, bind_ok]
  have hpd := J.rdPend hvV hkv
  by_cases hp : vs.exit.pending = true
  · have hi : ¬ L.mem s (core.num.U64.wrapping_add v vcpu.PENDING) = 0#u64 := by
      intro e; rw [e, hp] at hpd; simp at hpd
    rw [if_neg hi]
    refine (WP.spec_ok _).2 ?_
    rw [hS]
    simp [hp]
  have hp' : vs.exit.pending = false := by simpa using hp
  have hi : L.mem s (core.num.U64.wrapping_add v vcpu.PENDING) = 0#u64 := by
    by_contra e
    have : (L.mem s (core.num.U64.wrapping_add v vcpu.PENDING) != 0#u64) = true := by simpa using e
    rw [hpd, hp'] at this; cases this
  rw [if_pos hi]
  refine WP.spec_bind (P1.LawfulStore.cur_cpu_spec s) fun c ec => ?_
  have hon : v3OnCore st s t.bv = decide (cpu = c) := by
    unfold v3OnCore; rw [ecpu, ec]; try rfl
  by_cases hcc : cpu = c
  · rw [if_pos hcc]
    refine (WP.spec_ok _).2 ?_
    rw [hS]
    simp [hp', hon, hcc]
  rw [if_neg hcc]
  refine WP.spec_bind (v3_full_reply J htT hk) fun full hfull => ?_
  subst hfull
  cases hf : Fl4Proofs.P3.repFull x with
  | false =>
    rw [if_neg Bool.false_ne_true]
    refine (WP.spec_ok _).2 ?_
    rw [hS]
    have hf' : decide (x.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register = 30) = false := hf
    have hf2 := of_decide_eq_false hf'
    simp [hp', hon, hcc, hf2]
    try exact fun h => absurd h hf2
  | true =>
    rw [if_pos rfl]
    refine WP.spec_bind (P1.obj.node_get.spec s cpu _) fun i2 ei2 => ?_
    refine (WP.spec_ok _).2 ?_
    have hf' : decide (x.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register = 30) = true := hf
    have hrc0 : v3RemCur st s t.bv = decide (i2 = t) := by
      unfold v3RemCur; rw [ei2, ecpu]; try rfl
    have key : decide (vs.exit.pending = false ∧ (v3OnCore st s t.bv = true ∨
        (decide (x.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register = 30) = true ∧
          v3RemCur st s t.bv = false))) = (i2 != t) := by
      rw [hp', hon, hf', hrc0, decide_eq_false hcc]
      by_cases e : i2 = t
      · subst e; simp
      · rw [decide_eq_false e, show (i2 != t) = true from bne_iff_ne.mpr e]; decide
    rw [hS, key]

end

end

end Fl4Proofs.P3
