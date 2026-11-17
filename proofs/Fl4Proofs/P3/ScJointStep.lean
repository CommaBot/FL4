/-
P3 (DESIGN.md §9), scheduling contexts: **the SC family's step on `JAt`**
(the first family-level preservation theorem): `JAtZ` before the decode of
an SC cap ⇒ `XTop` and `JAtZ` after (`sched_controlJ_step`).

From the producer's post: `XTopAt` (`xtop_sc_step`), the scheduler and
notification relations, `NSC`, `Inv` (`decode_configure_refines`), the call
stacks, yield, MCP and reply placement (`ScAll.of_k`), `BlockedScActive`
(`bsa_configure`, the decoded `REFILL_MAX` from `retP_configureDec`); the
fields no SC step touches by `JAtZ.sc_frame`; `CurRun` (`curRun_sc_step`);
the buffer words, slots apart, `JPlaced`, `JKern`, the untyped caps' facts
and `JCovD` (ScJointRest: `JAtZ.sc_buf`, `sc_apart`, `sc_jpl`, `sc_kern`,
`sc_utc`, `sc_jcov`; the current SC kept by `FK`, ScFieldKeep). The dead
set: the step cuts links only (ScLinkKeep) outside Bind's SC and new thread
or notification, so the dead stay dead (`deadP_sc_step`); Bind's pair leaves
the dead set, covered by its caps (`cover_cap`: the invoked SC cap's slot,
the extra cap's slot; premises `hslot`, `hslotS`, `hsb`, `hssz`, `hx0S`, the
decode site's cap lookup and `valid_cap`).

The mid-entry facts (`CurInv` unless a reschedule is pending, `CurOwn`
under one, `OffOK`, `ActIdle`): the restart keeps them (`restart_mid`; the
entry action `resume_cur_thread`, premise `hres`), and the invocation is a
`MidK` step (ScMidKeep: Bind, UnbindObject, YieldTo, the decodes'
checks `rdp_decode*Pre` and `hback` placing the SC's thread off the current
and idle ones) or, for Configure of an SC other than the current one, a
`MidKn` step (its `possible_switch_to`; `ActIdle` then from
`decode_configure_refinesA`, premise `hpi`).

Configure of the current SC (bound to the current thread) is a `MidKW` step
ending with the consumed time cleared and a reschedule pending
(`mkw_configureCur`, ScMidCur), hence `MidA`.

Named per-op premise (`hRest`, at the decode's post, over its spec run,
`ScStepP1`): P1-supplied, the node-0 `DEBUG_TCBS` word kept and `BlkOK`.
-/
import Fl4Proofs.P3.ScJointRest
import Fl4Proofs.P3.ScBsaOps
import Fl4Proofs.P3.ScDeadStep
import Fl4Proofs.P3.ScMidKeep
import Fl4Proofs.P3.ScMidCur
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

/-- **The P1-supplied part of an SC step** (the node-0 `DEBUG_TCBS` word kept,
`BlkOK` after). -/
def ScStepP1 (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s s' : S) : Prop :=
  ∃ (Ac' : Set U64),
    L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) ∧
    P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac' s'

theorem retP_bind_never {α β : Type} {P : β → Prop} {m : Fl4Spec.SEMonad Unit α} {f : α → Fl4Spec.SEMonad Unit β}
    (hm : RetP (fun _ => False) m) : RetP P (m >>= f) := by
  intro σ x hx v hv
  rw [ExceptT.run_bind] at hx
  obtain ⟨⟨e, σ'⟩, he, hx⟩ := hx
  cases e with
  | error e => rw [Set.mem_singleton_iff.1 hx] at hv; cases hv
  | ok a => exact (hm σ _ he a rfl).elim

/-- Bind's decoded cap is the first extra cap. -/
theorem retP_bindHead (sc : Fl4Spec.ObjRef) (excaps : List Fl4Spec.Cap) :
    RetP (fun v => ∃ a rest, excaps = a :: rest ∧ v = .invokeSchedContextBind sc a)
      (Fl4Spec.decodeSchedContextBind (Z := Unit) sc excaps) := by
  unfold Fl4Spec.decodeSchedContextBind
  cases excaps with
  | nil =>
    refine retP_bind_never ?_
    unfold Fl4Spec.NonDetE.whenE; rw [if_pos List.length_nil]; exact retP_throw _
  | cons a rest =>
    refine retP_bind _ fun _ => ?_
    rw [retOk_bind]
    simp only [List.head?_cons]
    repeat (first | exact retP_pure ⟨_, _, rfl, rfl⟩ | exact retP_throw _ | (refine retP_bind _ fun _ => ?_) | split | (dsimp only))

/-- **`CurRun` after an SC step**: the restart makes the current thread
runnable, and the invocation (`ScTKw (·=False)`) keeps every TCB state and
the current thread. -/
theorem curRun_sc_step {σ σ0 σ' : Fl4Spec.State Unit} {t : Fl4Spec.ObjRef} {x : Fl4Spec.Tcb}
    (hkc : σ.kheap t = some (.tcb x)) (hct : σ.curThread = t)
    (he0 : Fl4Spec.setThreadState (Z := Unit) t .restart σ = ({((), σ0)}, False))
    (hK1 : ScTKw (fun _ => False) σ0 σ') : CurRun σ' := by
  have hσ0 := the_result (Fl4Proofs.P3.Notif.setThreadState_eq .restart hkc) he0
  have hk0 : σ0.kheap t = some (.tcb { x with tcbState := .restart }) := by
    rw [hσ0, stsAct_kheap]; simp [updK]
  have hc0 : σ0.curThread = t := by
    rw [hσ0]; unfold stsAct; split_ifs <;> exact hct
  intro y hy
  obtain ⟨y', hy', -, hs⟩ := hK1.tcb hk0
  rw [hK1.ct, hc0, hy'] at hy; cases hy
  rcases hs with e | ⟨h, -⟩
  · rw [e]; rfl
  · exact h.elim

set_option maxHeartbeats 2000000 in
/-- **The SchedControl cap on `JAt`, `JAt` after** (module docstring). -/
theorem sched_controlJ_step {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : σ.curThread ≠ σ.idleThread) (hres : σ.schedulerAction = .resumeCurThread)
    (htm : TimeAgree arI) (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) (hmsg : MsgOK st Z.N Z.T Z.C Z.c)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .schedControlConfigureFlags ↔
      lbl = fl4_abi.label.SchedControlConfigureFlags)
    (cpu length buf ct : U64) (hcpu : cpu = Z.c) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel Z.th (L.mem s) x0 (excaps.map Prod.fst))
    (hsb : ∀ p sb, capAt (L.mem s) x0 = ok (.SchedContext p sb) → sb.val < 64)
    (hsc : ∀ p sb, capAt (L.mem s) x0 = ok (.SchedContext p sb) → p ∈ Z.C ∧ p ≠ 0#u64 ∧
      ∃ x, σ.kheap p.bv = some (.schedContext x (sb.val - Fl4Spec.minSchedContextBits)) ∧
        ∀ t : U64, x.scTcb = some t.bv →
          t ∈ Z.T ∧ ∃ xt, σ.kheap t.bv = some (.tcb xt) ∧ xt.tcbSchedContext = some p.bv)
    (hpi : ∀ p sb, capAt (L.mem s) x0 = ok (.SchedContext p sb) → p.bv ≠ Fl4Spec.idleScPtr)
    (slot : U64) (blk call don fp : Bool)
    (hArch : syscall.decode_invocation st arI s a lbl length slot (.SchedControl cpu) blk call don fp buf extra
      ⦃ r => ∀ c, AR a c → AR r.2.2 c ⦄)
    (hRest : syscall.decode_invocation st arI s a lbl length slot (.SchedControl cpu) blk call don fp buf extra
      ⦃ r => r.1 = .Ok () → ∀ σ' inv σ1,
        (Fl4Spec.decodeSchedControlInvocationFlags (Z := Unit) slbl (args.map UScalar.bv) (excaps.map Prod.fst)).run σ =
          ({(.ok inv, σ)}, False) →
        Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) →
        Fl4Spec.invokeSchedControlConfigureFlags (Z := Unit) inv σ1 = ({((), σ')}, False) →
        ScStepP1 (L := L) Z H Cs s r.2.1 ⦄) :
    syscall.decode_invocation st arI s a lbl length slot (.SchedControl cpu) blk call don fp buf extra
      ⦃ r => ∃ (σ' : Fl4Spec.State Unit) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' r.2.1 r.2.2 σ' ⦄ := by
  have hX := J.xtop
  have hS := hX.fin.1.1.1
  have hR := hX.fin.1.1.2.2.1
  obtain ⟨hcur, xc, hkc, hrun⟩ := J.curRunnable hni hct
  have hC := J.curInv (by rw [hres]; simp)
  have key : syscall.decode_invocation st arI s a lbl length slot (.SchedControl cpu) blk call don fp buf extra
      ⦃ res => (fp = true ∧ res = (.Err (.Sys (.InvalidCapability 0#u64)), s, a)) ∨
        (fp = false ∧ Sched.CPost σ (Fl4Spec.decodeSchedControlInvocationFlags (Z := Unit) slbl (args.map UScalar.bv)
          (excaps.map Prod.fst)) s a
        (fun inv res => ∃ σ1 σ', Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) ∧
          Fl4Spec.invokeSchedControlConfigureFlags (Z := Unit) inv σ1 = ({((), σ')}, False) ∧
          res.1 = .Ok () ∧ SchedRel st Z.N Z.T Z.C Z.c res.2.1 σ' ∧ NtfnStateRel Z.N Z.T (L.mem res.2.1) σ' ∧
          NSC Z.N Z.C σ' ∧ Inv σ' ∧ P1.WritesIn st s res.2.1 (KFoot st Z.T Z.N Z.C Z.c s σ) ∧
          (σ1.schedulerAction = .resumeCurThread → IdleOK σ1 →
            (∀ p sb, capAt (L.mem s) x0 = ok (.SchedContext p sb) → p.bv ≠ Fl4Spec.idleScPtr) → ActIdle σ')) res) ⦄ := by
    unfold syscall.decode_invocation
    rw [hct]; simp only [bind_ok]
    cases fp
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact WP.spec_mono (decode_configure_refinesA htm Z.th s a σ hS hR J.nsc J.inv hC J.off lbl slbl hlbl cpu
        length buf ct hcpu hct args hlen hargs extra x0 hx0 _ hex hsb hsc hkc hrun) fun r h => Or.inr ⟨by trivial, h⟩
    · simp only [↓reduceIte, WP.spec_ok]
      exact Or.inl ⟨by trivial, by trivial⟩
  refine WP.spec_mono (WP.spec_and hArch (WP.spec_and key hRest)) ?_
  rintro ⟨r0, s', a'⟩ ⟨hA, hq, hRst⟩
  rcases hq with ⟨rfl, he⟩ | ⟨rfl, hq⟩
  · cases he; exact ⟨σ, Ac, Lst, D, J⟩
  rcases hq with ⟨e, e', he, -, -⟩ | ⟨inv, hdec, σ1, σ', he1, he2, hr1, hS', hR', hN', hI', hw, hAc⟩
  · cases he; exact ⟨σ, Ac, Lst, D, J⟩
  have hm1 : ((), σ1) ∈ (Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ).1 := by rw [he1]; exact Set.mem_singleton _
  have hm2 : ((), σ') ∈ (Fl4Spec.invokeSchedControlConfigureFlags (Z := Unit) inv σ1).1 := by
    rw [he2]; exact Set.mem_singleton _
  have hK : ScTKw (fun p => p = ct.bv) σ σ' :=
    (tk_setThreadState hkc (ipcFree_of_runnable hrun) ipcFree_restart _ hm1).trans
      ((nkt_invokeSchedControlConfigureFlags inv σ1 ((), σ') hm2).mono fun _ h => h.elim)
  have hX' : XTopAt (L := L) AR Z s' a' σ' :=
    xtop_sc_step hX J.ip J.nk (WritesIn.tfoot_of_kfoot hw) hK hS' hR' fun h => hA _ h
  have hSOK : SOK (true, true) σ σ' :=
    (pres_setThreadState (f := (true, true)) _ _ σ _ hm1).trans
      (pres_invokeSchedControlConfigureFlags (true, true) _ σ1 _ hm2)
  obtain ⟨-, hY', hM', ⟨Lst', hCR', hRF'⟩, hRP', -⟩ :=
    ScAll.of_k hS J.rp J.yld J.mcp J.call J.rfree ⟨⟨hS', hR', hN', hI'⟩, hw, hSOK⟩
  obtain ⟨Ac', hDbg, hBlk'⟩ := hRst hr1 σ' inv σ1 hdec he1 he2
  obtain ⟨a0, rest, hex', q, sz, rfl, b, per, k, badge, flag, rfl⟩ :=
    (rdp_decodeCfgHead slbl (args.map UScalar.bv) (excaps.map Prod.fst) σ _ (by rw [hdec]; exact Set.mem_singleton _)).2
      _ rfl
  have hB' : BlockedScActive σ' := bsa_configure J.bsa (hcur ▸ hkc) hrun (hcur ▸ hm1) hm2
  -- the configured SC is the extra cap's
  obtain ⟨p, sb, hcap, hpq⟩ : ∃ p sb, capAt (L.mem s) x0 = ok (.SchedContext p sb) ∧ p.bv = q := by
    rcases hex with ⟨-, he⟩ | ⟨-, c, a1, rest', hc, hCR, -, he⟩
    · rw [he] at hex'; cases hex'
    rw [he] at hex'
    injection hex' with ha
    have hCa := hCR.abs
    rw [ha] at hCa
    cases c <;> simp only [absCap, reduceCtorEq, Fl4Spec.Cap.schedContextCap.injEq] at hCa
    exact ⟨_, _, hc, hCa.1.symm⟩
  -- the mid-entry facts: the restart keeps them; Configure of another SC is `MidKn`
  have hcs : Fl4Spec.schedulable σ.curThread σ = true := ct_schedulable hC J.act J.inv (hcur ▸ hkc) hrun
  obtain ⟨hres1, hC1, hO1, hA1, hI1⟩ := restart_mid hcur hkc (hcur ▸ hcs) hres hC J.off J.act J.inv
  have hσ1 := the_result (Fl4Proofs.P3.Notif.setThreadState_eq .restart hkc) he1
  rw [← hσ1] at hres1 hC1 hO1 hA1 hI1
  have hAI' : ActIdle σ' := hAc hres1 hA1.2 hpi
  have hctT : ct ∈ Z.T := J.thT ct (J.kern.curT ▸ by rw [show L.curW s = ct from P1.eq_of_bv (by rw [← J.kern.cur, hcur])])
  have hf1 := stsAct_fields (Fl4Proofs.P3.Notif.updK σ ct.bv (.tcb { xc with tcbState := .restart })) ct.bv
  have hct1 : σ1.curThread = ct.bv := by rw [hσ1, hf1.2.1]; exact hcur
  have hcs1 : σ1.curSc = σ.curSc := by rw [hσ1, hf1.2.2.1]; rfl
  have hid1 : σ1.idleThread = σ.idleThread := by
    rw [hσ1]; unfold Fl4Proofs.P3.Notif.stsAct; split_ifs <;> rfl
  obtain ⟨hC', hOw', hO'⟩ : MidA Z.T σ' := by
    obtain ⟨hpC, -, x, hkx, hbnd⟩ := hsc p sb hcap
    have hpc : p.bv ≠ ct.bv := fun e => by rw [e, hkc] at hkx; cases hkx
    have hkx1 : σ1.kheap p.bv = some (.schedContext x (sb.val - Fl4Spec.minSchedContextBits)) := by
      rw [hσ1, (stsAct_fields _ _).1]; simp [Fl4Proofs.P3.Notif.updK, hpc, hkx]
    obtain ⟨xt, hkt, hxs, -⟩ := hC.tcb
    by_cases hq : q = σ.curSc
    · -- the current SC, bound to the current thread: `commit_time`, a reschedule
      obtain ⟨y1, n1, hy1, hy1t⟩ := J.inv.back _ xt σ.curSc hkt hxs
      rw [← hq, ← hpq, hkx] at hy1; cases hy1
      have hci : σ1.curThread ≠ σ1.idleThread := by
        rw [hct1, hid1, ← hcur]; intro e
        obtain ⟨xi, hki, -, hti, -⟩ := J.act.2
        rw [← e, hkt] at hki; cases hki
        rw [hcur, hkc] at hkt; cases hkt; rw [hti] at hrun; cases hrun
      obtain ⟨kW, h0, hcn⟩ := mkw_configureCur (b := b) (per := per) (mr := k + Fl4Spec.MIN_REFILLS) (badge := badge)
        (flag := flag) (hpq ▸ hkx1) (by rw [hcs1]; exact hq) (by rw [hy1t, hct1, hcur]) hci
        (by simp [Fl4Spec.activeSc, Fl4Spec.MIN_REFILLS]) _ hm2
      exact kW.midA h0 hcn hC1 hI1 ⟨ct, hctT, hct1.symm⟩
    have ht : ∀ t, x.scTcb = some t → t ≠ σ1.idleThread ∧ t ≠ σ1.curThread := by
      intro t ht
      obtain ⟨-, xt', hkt', hxt'⟩ := hbnd ⟨t⟩ ht
      have hkt2 : σ.kheap t = some (.tcb xt') := hkt'
      refine ⟨fun e => ?_, fun e => ?_⟩
      · rw [hid1] at e
        obtain ⟨xi, hki, hsi, -⟩ := J.act.2
        rw [e, hki] at hkt2; cases hkt2; rw [hsi] at hxt'
        exact hpi p sb hcap (Option.some.inj hxt').symm
      · rw [hct1, ← hcur] at e
        rw [e, hkt] at hkt2; cases hkt2; rw [hxs] at hxt'
        exact hq (by rw [← hpq]; exact (Option.some.inj hxt').symm)
    have hK1 := mkn_configure (b := b) (per := per) (mr := k + Fl4Spec.MIN_REFILLS) (badge := badge) (flag := flag)
      (hpq ▸ hkx1) (by rw [hcs1]; exact hq) ht (by simp [Fl4Spec.activeSc, Fl4Spec.MIN_REFILLS])
      _ hm2
    exact hK1.mid3 hC1 hO1 hI1 ⟨ct, hctT, hct1.symm⟩
  have hF : FK σ σ' := ((fk_setThreadState _ _).of_eq he1).trans ((fk_invokeSchedControlConfigureFlags _).of_eq he2)
  have hwT := WritesIn.tfoot_of_kfoot hw
  -- the dead set: Configure cuts links only
  have hL : LK (fun _ => False) σ σ' := (lkm_setThreadState _ _ σ _ hm1).trans (lkm_configure _ σ1 _ hm2)
  have hP : ∀ p x, p = ct.bv → σ.kheap p = some (.tcb x) → Fl4Spec.runnable x.tcbState = true := by
    rintro p x rfl hk; rw [hkc] at hk; cases hk; exact hrun
  have hDead : ∀ q ∈ D, DeadP (L := L) H s' q := fun q hq =>
    J.deadP_sc_step hX' hwT hK hP hL hF hAI'.1 (fun h => h) (J.jcov.dead q hq)
  have hCR'' : CurRun σ' := curRun_sc_step hkc hcur he1 (NKT.of_eq (nkt_invokeSchedControlConfigureFlags _) he2)
  exact ⟨σ', Ac', Lst', D, J.sc_frame hwT hK hX' hCR' hRF' hY' hM' (J.sc_buf hwT hK) hRP' (J.sc_apart hwT hK)
    (J.sc_jpl hwT hK) (J.sc_jcov hwT hDead fun q hq hn => absurd hq hn) (J.sc_kern hwT hK hF hX' hDbg fun _ h => h)
    (J.sc_utc hwT hK hDbg) hN' hI' hC' (Or.inl (hC'.elim hOw' (curOwn_of_curInv hX'.fin.1.1.1 hI'))) hO' hAI' hB' (Or.inl hCR'') hBlk'⟩


set_option maxHeartbeats 4000000 in
/-- **The SchedContext cap on `JAt`** for Bind, UnbindObject and a YieldTo
from an SC yielded to by none: when the invocation returns no data, `JAt`
after (`XTop` by `xtop_sc_step`, the relations by `ScAll`, `BlockedScActive`
by `bk_invokeSchedContext` with Bind's decode check, `rdp_decodeBind`); a
YieldTo returning at once has replied (its `XTop` the reply leaf's, the
second disjunct). Named per-op premise `hRest` (module docstring). -/
theorem sched_contextJ_step {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hres : σ.schedulerAction = .resumeCurThread)
    (htm : TimeAgree arI) (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) (hmsg : MsgOK st Z.N Z.T Z.C Z.c)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = scLabelOf lbl)
    {sc : U64} (sb : U64) (hsc : sc ∈ Z.C) (hpi : sc.bv ≠ Fl4Spec.idleScPtr)
    (hl : lbl = fl4_abi.label.SchedContextBind ∨ lbl = fl4_abi.label.SchedContextUnbindObject ∨
      (lbl = fl4_abi.label.SchedContextYieldTo ∧ L.mem s (P1.scYieldFromA sc) = 0#u64))
    (hback : L.mem s (scW sc 24#u64) ≠ 0#u64 →
      L.mem s (scW sc 24#u64) ∈ Z.T ∧ L.mem s (P1.scA (L.mem s (scW sc 24#u64))) = sc ∧
      (L.mem s (scW sc 24#u64)).bv ≠ σ.idleThread)
    (hbn : ∀ y n, σ.kheap sc.bv = some (.schedContext y n) → ∀ m : U64, y.scNtfn = some m.bv → m ∈ Z.N)
    {ct : U64} (hct : sched.cur_thread st s = ok ct) (hcs : Fl4Spec.schedulable ct.bv σ = true)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel Z.th (L.mem s) x0 (excaps.map Prod.fst))
    (hcapT : ∀ p, capAt (L.mem s) x0 = ok (.Thread p) → p ∈ Z.T)
    (hcapN : ∀ p b w r, capAt (L.mem s) x0 = ok (.Notification p b w r) → p ∈ Z.N ∧ p ≠ 0#u64)
    (length slot buf : U64) (blk call don fp : Bool)
    (hslot : capAt (L.mem s) slot = ok (.SchedContext sc sb)) (hslotS : IsSlot Z.th slot) (hsb : sb.val < 64)
    (hssz : ∀ y n, σ.kheap sc.bv = some (.schedContext y n) → n + Fl4Spec.minSchedContextBits = sb.val)
    (hx0S : x0 ≠ 0#u64 → IsSlot Z.th x0)
    (hArch : syscall.decode_invocation st arI s a lbl length slot (.SchedContext sc sb) blk call don fp buf extra
      ⦃ r => ∀ c, AR a c → AR r.2.2 c ⦄)
    (hRest : syscall.decode_invocation st arI s a lbl length slot (.SchedContext sc sb) blk call don fp buf extra
      ⦃ r => r.1 = .Ok () → ∀ σ1, (∃ inv σ0,
        (Fl4Spec.decodeSchedContextInvocation (Z := Unit) slbl sc.bv (excaps.map Prod.fst)).run σ = ({(.ok inv, σ)}, False) ∧
        Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ0)}, False) ∧
        Fl4Spec.invokeSchedContext (Z := Unit) inv σ0 = ({([], σ1)}, False)) →
        ScStepP1 (L := L) Z H Cs s r.2.1 ⦄) :
    syscall.decode_invocation st arI s a lbl length slot (.SchedContext sc sb) blk call don fp buf extra
      ⦃ r => (∃ (σ' : Fl4Spec.State Unit) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
          JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' r.2.1 r.2.2 σ') ∨
        (r.1 = .Ok () ∧ ∃ inv σ0 data σ1,
          (Fl4Spec.decodeSchedContextInvocation (Z := Unit) slbl sc.bv (excaps.map Prod.fst)).run σ =
            ({(.ok inv, σ)}, False) ∧
          Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ0)}, False) ∧
          Fl4Spec.invokeSchedContext (Z := Unit) inv σ0 = ({(data, σ1)}, False)) ⦄ := by
  have hX := J.xtop
  have hS := hX.fin.1.1.1
  have hR := hX.fin.1.1.2.2.1
  obtain ⟨Q, R', hc, hs⟩ := hS.lists
  have hct' : ct = nodeW st s Z.c layout.node.CUR_THREAD := by
    have h := sched.cur_thread.spec' (L := L) s
    rw [hct, WP.spec_ok, hc.cur] at h; exact h
  have hcur : σ.curThread = ct.bv := by rw [hs.curThread, hct']
  obtain ⟨xc, -, -, -, hkc, -, hrunc, -⟩ := schedulable_inv hcs
  have hctT : ct ∈ Z.T := hct' ▸ hc.curT
  have key : syscall.decode_invocation st arI s a lbl length slot (.SchedContext sc sb) blk call don fp buf extra
      ⦃ res => (fp = true ∧ res = (.Err (.Sys (.InvalidCapability 0#u64)), s, a)) ∨
        (fp = false ∧ Sched.CPost σ (Fl4Spec.decodeSchedContextInvocation (Z := Unit) slbl sc.bv (excaps.map Prod.fst)) s a
          (ScQ (fun s' σ' => ScAll (st := st) Z.N Z.T Z.C Z.R Z.c s σ s' σ' ∧
            ScFine (st := st) Z.N Z.T Z.C Z.c lbl sc ct s σ s' σ') σ ct call) res) ⦄ := by
    unfold syscall.decode_invocation
    rw [hct]; simp only [bind_ok]
    cases fp
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact WP.spec_mono (sc_decode_refines htm Z.th s a σ hS hR J.nsc J.inv J.yld J.act J.mcp J.c0 J.call J.rp
        J.rfree lbl slbl hlbl hsc hpi hback hbn hct hcs call extra x0 hx0 _ hex hcapT hcapN hmb hmax htu hmsg)
        fun r h => Or.inr ⟨by trivial, h⟩
    · simp only [↓reduceIte, WP.spec_ok]
      exact Or.inl ⟨by trivial, by trivial⟩
  refine WP.spec_mono (WP.spec_and hArch (WP.spec_and key hRest)) ?_
  rintro ⟨r0, s', a'⟩ ⟨hA2, hq, hRst⟩
  rcases hq with ⟨rfl, he⟩ | ⟨rfl, hq⟩
  · cases he; exact Or.inl ⟨σ, Ac, Lst, D, J⟩
  rcases hq with ⟨e, e', he, -, -⟩ | ⟨inv, hrun, hr1, σ0, data, σ1, σ2, he0, he1, hcase, hall, hfine⟩
  · cases he; exact Or.inl ⟨σ, Ac, Lst, D, J⟩
  rcases hcase with ⟨hd, hσ⟩ | -
  swap
  · exact Or.inr ⟨hr1, inv, σ0, data, σ1, hrun, he0, he1⟩
  left
  subst hd; subst hσ
  have hm0 : ((), σ0) ∈ (Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ).1 := by rw [he0]; exact Set.mem_singleton _
  have hm1 : (([] : List Fl4Spec.Data), σ2) ∈ (Fl4Spec.invokeSchedContext (Z := Unit) inv σ0).1 := by
    rw [he1]; exact Set.mem_singleton _
  have hσ0 := the_result (Fl4Proofs.P3.Notif.setThreadState_eq .restart hkc) he0
  have hko : ∀ q, q ≠ ct.bv → σ0.kheap q = σ.kheap q := fun q hq => by
    rw [hσ0, stsAct_kheap]; simp [updK, hq]
  have hkc0 : σ0.kheap ct.bv = some (.tcb { xc with tcbState := .restart }) := by
    rw [hσ0, stsAct_kheap]; simp [updK]
  have hK0 : ScTKw (fun p => p = ct.bv) σ σ0 := tk_setThreadState hkc (ipcFree_of_runnable hrunc) ipcFree_restart _ hm0
  -- the invocation's shape, and Bind's decode check
  have hshape : ((∃ q cap, inv = .invokeSchedContextBind q cap) ∨ (∃ q cap, inv = .invokeSchedContextUnbindObject q cap) ∨
      (∃ q x n, inv = .invokeSchedContextYieldTo q ∧ σ0.kheap q = some (.schedContext x n) ∧ x.scYieldFrom = none)) ∧
      ∀ q t, inv = .invokeSchedContextBind q (.threadCap t) → ScBindOK q t σ := by
    rcases hl with l | l | ⟨l, hy0⟩
    · have hg : Fl4Spec.genInvocationType slbl = .schedContextBind := by rw [hlbl, l]; unfold scLabelOf; simp
      simp only [Fl4Spec.decodeSchedContextInvocation, hg] at hrun
      obtain ⟨cap, rfl⟩ := (retP_bindDec _ _).of_run hrun
      refine ⟨Or.inl ⟨_, _, rfl⟩, fun q t e => ?_⟩
      have := ((rdp_decodeBind _ _ σ _ (by rw [hrun]; exact Set.mem_singleton _)).2 _ rfl) t
      cases e; exact this rfl
    · have hg : Fl4Spec.genInvocationType slbl = .schedContextUnbindObject := by
        rw [hlbl, l]; unfold scLabelOf; simp
      simp only [Fl4Spec.decodeSchedContextInvocation, hg] at hrun
      obtain ⟨cap, rfl⟩ := (retP_unbindObjDec _ _).of_run hrun
      exact ⟨Or.inr (Or.inl ⟨_, _, rfl⟩), fun q t e => by cases e⟩
    · have hg : Fl4Spec.genInvocationType slbl = .schedContextYieldTo := by rw [hlbl, l]; unfold scLabelOf; simp
      simp only [Fl4Spec.decodeSchedContextInvocation, hg] at hrun
      have e := (retP_yieldToDec _).of_run hrun
      obtain ⟨x, n, hk, hx⟩ := hs.scs sc hsc
      have hyf : x.scYieldFrom = none := by rw [hx.yieldFrom, ← scYieldFromA_eq, hy0, optRef_zero]
      have hpc : sc.bv ≠ ct.bv := fun e => by rw [e, hkc] at hk; cases hk
      exact ⟨Or.inr (Or.inr ⟨_, x, n, e, by rw [hko _ hpc]; exact hk, hyf⟩), fun q t e' => by rw [e] at e'; cases e'⟩
  obtain ⟨hshape, hbind⟩ := hshape
  have hK1 : ScTKw (fun _ => False) σ0 σ2 := tk_invokeSchedContext hshape _ hm1
  -- FL4's writes
  have hW : P1.WritesIn st s s' (TFoot st Z.T Z.N Z.C Z.c s σ) := by
    rcases hl with l | l | ⟨l, hy0⟩
    · exact hfine.1 (Or.inl l)
    · exact hfine.1 (Or.inr l)
    · obtain ⟨y, hky, -, hy⟩ := hK1.tcb hkc0
      exact hfine.2 l hy0 y hky (hy.elim id fun h => h.1.elim)
  have hX' : XTopAt (L := L) AR Z s' a' σ2 :=
    xtop_sc_step hX J.ip J.nk hW (hK0.trans (hK1.mono fun _ h => h.elim)) hall.1.1 hall.1.2.1 fun h => hA2 _ h
  obtain ⟨⟨-, -, hN', hI'⟩, hY', hM', ⟨Lst', hCR', hRF'⟩, hRP', -⟩ := hall
  -- `BlockedScActive`
  have hKb0 := bk_restart (hcur ▸ hkc) hrunc (hcur ▸ hm0)
  have hB0 := J.bsa.bk hKb0 (f1 := true) (pres_setThreadState (f := (true, true)) _ _ σ _ hm0)
  have hinv : (∃ q cap, inv = .invokeSchedContextBind q cap) ∨ (∃ q cap, inv = .invokeSchedContextUnbindObject q cap) ∨
      (∃ q, inv = .invokeSchedContextYieldTo q) := by
    rcases hshape with h | h | ⟨q, -, -, e, -⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨q, e⟩)
  have hB' : BlockedScActive σ2 := by
    have hu : decide (∀ p, inv ≠ .invokeSchedContextUnbind p) = true := by
      rcases hinv with ⟨q, cap, rfl⟩ | ⟨q, cap, rfl⟩ | ⟨q, rfl⟩ <;> simp
    exact hB0.bk (bk_invokeSchedContext hm1 hK1 hinv fun q t e => (hbind q t e).bk hKb0)
      (f1 := decide (∀ p, inv ≠ .invokeSchedContextYieldTo p))
      ((pres_invokeSchedContext inv σ0 _ hm1).weaken (f' := (decide (∀ p, inv ≠ .invokeSchedContextYieldTo p), true))
        id (fun _ => hu))
  obtain ⟨Ac', hDbg, hBlk'⟩ := hRst hr1 σ2 ⟨inv, σ0, hrun, he0, he1⟩
  -- the mid-entry facts: the restart keeps them, the invocation is a `MidK` step
  have hC := J.curInv (by rw [hres]; simp)
  obtain ⟨hres0, hC0, hO0, hA0, hI0⟩ := restart_mid hcur hkc hcs hres hC J.off J.act J.inv
  rw [← hσ0] at hres0 hC0 hO0 hA0 hI0
  have hf0 := stsAct_fields (Fl4Proofs.P3.Notif.updK σ ct.bv (.tcb { xc with tcbState := .restart })) ct.bv
  have hct0 : σ0.curThread = ct.bv := by rw [hσ0, hf0.2.1]; exact hcur
  have hcs0 : σ0.curSc = σ.curSc := by rw [hσ0, hf0.2.2.1]; rfl
  have hid0 : σ0.idleThread = σ.idleThread := by
    rw [hσ0]; unfold Fl4Proofs.P3.Notif.stsAct; split_ifs <;> rfl
  -- the current SC's thread is the current thread
  obtain ⟨xt, hkt, hxs, -⟩ := hC.tcb
  obtain ⟨ycs, ncs, hkcs, hycs⟩ := J.inv.back _ xt σ.curSc hkt hxs
  -- the SC's bound thread (if any) is not idle (`hback`)
  have hnid : ∀ y n t, σ.kheap sc.bv = some (.schedContext y n) → y.scTcb = some t → t ≠ σ.idleThread := by
    intro y n t hy ht
    obtain ⟨x, n', hk, hx⟩ := hs.scs sc hsc
    rw [hk] at hy; cases hy
    rw [hx.tcb] at ht
    obtain ⟨h0, rfl⟩ := Sched.optRef_some ht
    exact (hback h0).2.2
  have hpc : sc.bv ≠ ct.bv := fun e => by
    obtain ⟨x, n', hk, -⟩ := hs.scs sc hsc; rw [e, hkc] at hk; cases hk
  have hMid : MidK σ0 σ2 := by
    rcases hl with l | l | ⟨l, -⟩
    · have hg : Fl4Spec.genInvocationType slbl = .schedContextBind := by rw [hlbl, l]; unfold scLabelOf; simp
      simp only [Fl4Spec.decodeSchedContextInvocation, hg] at hrun
      have hpre := (rdp_decodeBindPre _ _ σ _ (by rw [hrun]; exact Set.mem_singleton _)).2 _ rfl
      obtain ⟨cap, rfl⟩ := (retP_bindDec _ _).of_run hrun
      cases cap
      case threadCap t =>
        obtain ⟨⟨y, n, hy, hyt⟩, xt0, hkt0, hxt0⟩ := hpre t rfl
        have hP : BindPre sc.bv t σ0 := by
          refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
          · rw [hcs0] at e; rw [e, hkcs] at hy; cases hy; rw [hycs] at hyt; cases hyt
          · rw [hct0, ← hcur] at e; rw [e, hkt] at hkt0; cases hkt0; rw [hxs] at hxt0; cases hxt0
          · rw [hid0] at e
            obtain ⟨xi, hki, hsi, -⟩ := J.act.2
            rw [e, hki] at hkt0; cases hkt0; rw [hsi] at hxt0; cases hxt0
        exact (mka_bind_ret (mka_schedContextBindTcb _ _) _) σ0 hP _ hm1
      case notificationCap n b r =>
        exact (mka_bind_ret (mka_schedContextBindNtfn _ _) _) σ0 trivial _ hm1
      all_goals exact (mka_fail (P := fun _ => True)) σ0 trivial _ hm1
    · have hg : Fl4Spec.genInvocationType slbl = .schedContextUnbindObject := by
        rw [hlbl, l]; unfold scLabelOf; simp
      simp only [Fl4Spec.decodeSchedContextInvocation, hg] at hrun
      have hpre := (rdp_decodeUnbindObjPre _ _ σ _ (by rw [hrun]; exact Set.mem_singleton _)).2 _ rfl
      obtain ⟨cap, rfl⟩ := (retP_unbindObjDec _ _).of_run hrun
      cases cap
      case threadCap t =>
        obtain ⟨⟨y, n, hy, hyt⟩, htc⟩ := hpre t rfl
        have hP : sc.bv ≠ σ0.curSc ∧ ∀ y' n' t', σ0.kheap sc.bv = some (.schedContext y' n') → y'.scTcb = some t' →
            t' ≠ σ0.curThread ∧ t' ≠ σ0.idleThread := by
          refine ⟨fun e => ?_, fun y' n' t' hy' ht' => ?_⟩
          · rw [hcs0] at e; rw [e, hkcs] at hy; cases hy; rw [hycs] at hyt; cases hyt; exact htc rfl
          · rw [hko _ hpc, hy] at hy'; cases hy'; rw [hyt] at ht'; cases ht'
            rw [hct0, ← hcur, hid0]; exact ⟨htc, hnid y n t hy hyt⟩
        exact (mka_bind_ret (mka_schedContextUnbindTcb _) _) σ0 hP _ hm1
      case notificationCap n b r =>
        exact (mka_bind_ret (mka_schedContextUnbindNtfn _) _) σ0 trivial _ hm1
      all_goals exact (mka_fail (P := fun _ => True)) σ0 trivial _ hm1
    · have hg : Fl4Spec.genInvocationType slbl = .schedContextYieldTo := by rw [hlbl, l]; unfold scLabelOf; simp
      simp only [Fl4Spec.decodeSchedContextInvocation, hg] at hrun
      obtain ⟨y, n, t, hy, hyt, htc⟩ := (rdp_decodeYieldToPre _ σ _ (by rw [hrun]; exact Set.mem_singleton _)).2 _ rfl
      rw [(retP_yieldToDec _).of_run hrun] at hm1
      rcases hshape with ⟨q, cap, e⟩ | ⟨q, cap, e⟩ | ⟨q, x, n', e, hk0, hyf⟩
      · rw [(retP_yieldToDec _).of_run hrun] at e; cases e
      · rw [(retP_yieldToDec _).of_run hrun] at e; cases e
      · rw [(retP_yieldToDec _).of_run hrun] at e; cases e
        rw [hko _ hpc, hy] at hk0; cases hk0
        exact mka_schedContextYieldTo (by rw [hko _ hpc]; exact hy) hyf (fun t' ht' => by
          rw [hyt] at ht'; cases ht'; rw [hct0, ← hcur, hid0]; exact ⟨hnid y n t hy hyt, htc⟩) _ hm1
  obtain ⟨hC', hOw', hO', hAI'⟩ := hMid.mid (T := Z.T) hres0 hC0 hO0 hA0 hI0 ⟨ct, hctT, hct0.symm⟩
  have hF : FK σ σ2 := ((fk_setThreadState _ _).of_eq he0).trans (fk_invokeSchedContext hshape _ hm1)
  have hCR'' : CurRun σ2 := curRun_sc_step hkc hcur he0 hK1
  have hKt := hK0.trans (hK1.mono fun _ h => h.elim)
  -- the dead set: the step cuts links only outside Bind's pair, which is covered (its caps)
  have hL : LK (invLinkW inv) σ σ2 := (lkm_setThreadState _ _ σ _ hm0).trans (lk_invokeSchedContext hshape _ hm1)
  have hP : ∀ p x, p = ct.bv → σ.kheap p = some (.tcb x) → Fl4Spec.runnable x.tcbState = true := by
    rintro p x rfl hk; rw [hkc] at hk; cases hk; exact hrunc
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hH := J.kern.heap
  have scCov : (∀ k, Z.th sc = some k → Covered (L.mem s') Z.G sc.val (sc.val + max (objSize k) 1)) ∧
      (∀ k, H sc = some k → Covered (L.mem s') Z.G sc.val (sc.val + 2 ^ k.bits)) := by
    obtain ⟨x, n, hk, -⟩ := hs.scs sc hsc
    have hHs := (hJ.sc sc x n (J.c0 sc hsc) hk).2
    have hsz := hssz x n hk
    have hfit := hH.fits sc _ hHs
    simp only [P1.HKind.bits] at hfit
    rw [hsz] at hfit
    refine J.cover_cap hW hslotS hslot (fun h => by cases h) (ok_inj (phys_eq _).symm) rfl
      (range_sc sc sb hsb hfit) fun k hk' => ?_
    rw [hHs] at hk'; cases hk'
    exact ⟨by simp only [P1.HKind.bits]; omega, fun z h => by cases h⟩
  have hcovW : ∀ q ∈ D, invLinkW inv q.bv →
      (∀ k, Z.th q = some k → Covered (L.mem s') Z.G q.val (q.val + max (objSize k) 1)) ∧
      (∀ k, H q = some k → Covered (L.mem s') Z.G q.val (q.val + 2 ^ k.bits)) := by
    intro q _ hqW
    rcases hl with l | l | ⟨l, -⟩
    · have hg : Fl4Spec.genInvocationType slbl = .schedContextBind := by rw [hlbl, l]; unfold scLabelOf; simp
      simp only [Fl4Spec.decodeSchedContextInvocation, hg] at hrun
      obtain ⟨a0, rest, hex', rfl⟩ := (retP_bindHead _ _).of_run hrun
      rcases hex with ⟨-, he⟩ | ⟨hx0n, c, a1, rest', hc, hCR, hCV, he⟩
      · rw [he] at hex'; cases hex'
      rw [he] at hex'
      injection hex' with ha
      subst ha
      have hCa := hCR.abs
      have hxS := hx0S hx0n
      have hqsc : q.bv = sc.bv → q = sc := fun e => bv_inj e
      cases a1 with
      | threadCap t =>
        rcases hqW with e | e
        · rw [hqsc e]; exact scCov
        · cases c <;> simp only [absCap, reduceCtorEq, Fl4Spec.Cap.threadCap.injEq] at hCa
          rename_i p
          have hq : q = p := bv_inj (e.trans hCa)
          subst hq
          have hHp : H q = some .tcb := (hJ.tcb q).1 hCV
          have hfit := hH.fits q _ hHp
          simp only [P1.HKind.bits] at hfit
          refine J.cover_cap hW hxS hc (fun h => by cases h) (ok_inj (phys_eq _).symm) rfl (range_thread q hfit)
            fun k hk' => ?_
          rw [hHp] at hk'; cases hk'
          exact ⟨by simp only [P1.HKind.bits]; omega, fun z h => by cases h⟩
      | notificationCap n b r =>
        rcases hqW with e | e
        · rw [hqsc e]; exact scCov
        · cases c <;> simp only [absCap, reduceCtorEq, Fl4Spec.Cap.notificationCap.injEq] at hCa
          rename_i p b' x1 x2
          have hq : q = p := bv_inj (e.trans hCa.1)
          subst hq
          have hty := hJ.typed x0 hxS
          rw [capV_of_capAt hc] at hty
          have hHp : H q = some .ntfn := (hty.2.1 q b' x1 x2 rfl).2
          have hfit := hH.fits q _ hHp
          simp only [P1.HKind.bits] at hfit
          refine J.cover_cap hW hxS hc (fun h => by cases h) (ok_inj (phys_eq _).symm) rfl
            (range_ntfn q b' x1 x2 hfit) fun k hk' => ?_
          rw [hHp] at hk'; cases hk'
          exact ⟨by simp only [P1.HKind.bits]; omega, fun z h => by cases h⟩
      | _ => exact hqW.elim
    · have hg : Fl4Spec.genInvocationType slbl = .schedContextUnbindObject := by
        rw [hlbl, l]; unfold scLabelOf; simp
      simp only [Fl4Spec.decodeSchedContextInvocation, hg] at hrun
      obtain ⟨cap, rfl⟩ := (retP_unbindObjDec _ _).of_run hrun
      exact hqW.elim
    · have hg : Fl4Spec.genInvocationType slbl = .schedContextYieldTo := by rw [hlbl, l]; unfold scLabelOf; simp
      simp only [Fl4Spec.decodeSchedContextInvocation, hg] at hrun
      rw [(retP_yieldToDec _).of_run hrun] at hqW
      exact hqW.elim
  have hDead : ∀ q ∈ {q | q ∈ D ∧ ¬ invLinkW inv q.bv}, DeadP (L := L) H s' q := fun q hq =>
    J.deadP_sc_step hX' hW hKt hP hL hF hAI'.1 hq.2 (J.jcov.dead q hq.1)
  have hCov : ∀ q ∈ D, q ∉ {q | q ∈ D ∧ ¬ invLinkW inv q.bv} →
      (∀ k, Z.th q = some k → Covered (L.mem s') Z.G q.val (q.val + max (objSize k) 1)) ∧
      (∀ k, H q = some k → Covered (L.mem s') Z.G q.val (q.val + 2 ^ k.bits)) := fun q hq hn =>
    hcovW q hq (by_contra fun h => hn ⟨hq, h⟩)
  exact ⟨σ2, Ac', Lst', _, J.sc_frame hW hKt hX' hCR' hRF' hY' hM' (J.sc_buf hW hKt) hRP' (J.sc_apart hW hKt)
    (J.sc_jpl hW hKt) (J.sc_jcov hW hDead hCov) (J.sc_kern hW hKt hF hX' hDbg fun _ h => h.1)
    (J.sc_utc hW hKt hDbg) hN' hI' hC' (Or.inl (hC'.elim hOw' (curOwn_of_curInv hX'.fin.1.1.1 hI'))) hO' hAI' hB' (Or.inl hCR'') hBlk'⟩

end

end

end Fl4Proofs.P3
