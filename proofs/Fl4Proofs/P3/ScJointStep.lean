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
`sc_utc`, `sc_jcov`; the current SC kept by `FK`, ScFieldKeep).

Named per-op premise (`hRest`, at the decode's post, over its spec run,
`ScStepRest`): the current-thread, offset and switch-thread invariants and
the current SC's owner under a pending reschedule (a),
`SchedValid` (b, a rebuild), the dead set after (`hDead`, P3's, to prove),
and P1-supplied: the node-0 `DEBUG_TCBS` word kept and `BlkOK`.
-/
import Fl4Proofs.P3.ScJointRest
import Fl4Proofs.P3.ScBsaOps
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

/-- **The fields an SC step still owes** (the module docstring's named
premise), at the post `(s', σ')` of a step from `s` with the dead set `D`:
the current-thread, offset and switch-thread invariants and the current
SC's owner under a pending reschedule (a); `SchedValid`
(b); the dead set after, `D' ⊆ D` dead, the rest of `D` covered (`hDead`,
P3's, to prove); the node-0 `DEBUG_TCBS` word kept and `BlkOK` (P1-supplied). -/
def ScStepRest (arI : machine.Arch A) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s s' : S)
    (σ' : Fl4Spec.State Unit) : Prop :=
  ∃ (Ac' D' : Set U64), (σ'.schedulerAction = .chooseNewThread ∨ CurInv σ') ∧
    (σ'.schedulerAction = .chooseNewThread → CurOwn Z.T σ') ∧ OffOK σ' ∧ ActIdle σ' ∧ SchedValid σ' ∧
    -- `hDead` (P3)
    (D' ⊆ D ∧ (∀ q ∈ D', DeadP (L := L) H s' q) ∧
      ∀ q ∈ D, q ∉ D' →
        (∀ k, Z.th q = some k → Covered (L.mem s') Z.G q.val (q.val + max (objSize k) 1)) ∧
        (∀ k, H q = some k → Covered (L.mem s') Z.G q.val (q.val + 2 ^ k.bits))) ∧
    -- P1-supplied: the node-0 `DEBUG_TCBS` word kept, `BlkOK`
    L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) ∧
    P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac' s'

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
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hres : σ.schedulerAction ≠ .chooseNewThread)
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
    (slot : U64) (blk call don fp : Bool)
    (hArch : syscall.decode_invocation st arI s a lbl length slot (.SchedControl cpu) blk call don fp buf extra
      ⦃ r => ∀ c, AR a c → AR r.2.2 c ⦄)
    (hRest : syscall.decode_invocation st arI s a lbl length slot (.SchedControl cpu) blk call don fp buf extra
      ⦃ r => r.1 = .Ok () → ∀ σ', (∃ inv σ1,
        (Fl4Spec.decodeSchedControlInvocationFlags (Z := Unit) slbl (args.map UScalar.bv) (excaps.map Prod.fst)).run σ =
          ({(.ok inv, σ)}, False) ∧
        Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) ∧
        Fl4Spec.invokeSchedControlConfigureFlags (Z := Unit) inv σ1 = ({((), σ')}, False)) →
        ScStepRest (L := L) arI Z H Cs D s r.2.1 σ' ⦄) :
    syscall.decode_invocation st arI s a lbl length slot (.SchedControl cpu) blk call don fp buf extra
      ⦃ r => ∃ (σ' : Fl4Spec.State Unit) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' r.2.1 r.2.2 σ' ⦄ := by
  have hX := J.xtop
  have hS := hX.fin.1.1.1
  have hR := hX.fin.1.1.2.2.1
  obtain ⟨hcur, xc, hkc, hrun⟩ := J.curRunnable hct
  have key : syscall.decode_invocation st arI s a lbl length slot (.SchedControl cpu) blk call don fp buf extra
      ⦃ res => (fp = true ∧ res = (.Err (.Sys (.InvalidCapability 0#u64)), s, a)) ∨
        (fp = false ∧ Sched.CPost σ (Fl4Spec.decodeSchedControlInvocationFlags (Z := Unit) slbl (args.map UScalar.bv)
          (excaps.map Prod.fst)) s a
        (fun inv res => ∃ σ1 σ', Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) ∧
          Fl4Spec.invokeSchedControlConfigureFlags (Z := Unit) inv σ1 = ({((), σ')}, False) ∧
          res.1 = .Ok () ∧ SchedRel st Z.N Z.T Z.C Z.c res.2.1 σ' ∧ NtfnStateRel Z.N Z.T (L.mem res.2.1) σ' ∧
          NSC Z.N Z.C σ' ∧ Inv σ' ∧ P1.WritesIn st s res.2.1 (KFoot st Z.T Z.N Z.C Z.c s σ)) res) ⦄ := by
    unfold syscall.decode_invocation
    rw [hct]; simp only [bind_ok]
    cases fp
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact WP.spec_mono (decode_configure_refines htm Z.th s a σ hS hR J.nsc J.inv (J.curInv hres) J.off lbl slbl hlbl cpu
        length buf ct hcpu hct args hlen hargs extra x0 hx0 _ hex hsb hsc hkc hrun) fun r h => Or.inr ⟨by trivial, h⟩
    · simp only [↓reduceIte, WP.spec_ok]
      exact Or.inl ⟨by trivial, by trivial⟩
  refine WP.spec_mono (WP.spec_and hArch (WP.spec_and key hRest)) ?_
  rintro ⟨r0, s', a'⟩ ⟨hA, hq, hRst⟩
  rcases hq with ⟨rfl, he⟩ | ⟨rfl, hq⟩
  · cases he; exact ⟨σ, Ac, Lst, D, J⟩
  rcases hq with ⟨e, e', he, -, -⟩ | ⟨inv, hdec, σ1, σ', he1, he2, hr1, hS', hR', hN', hI', hw⟩
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
  obtain ⟨p, b, per, k, badge, flag, rfl⟩ :=
    retP_configureDec slbl (args.map UScalar.bv) (excaps.map Prod.fst) σ _ (by rw [hdec]; exact Set.mem_singleton _)
      _ rfl
  have hB' : BlockedScActive σ' := bsa_configure J.bsa (hcur ▸ hkc) hrun (hcur ▸ hm1) hm2
  obtain ⟨Ac', D', hC', hOw', hO', hAI', hSV', ⟨hDD, hDead, hCov⟩, hDbg, hBlk'⟩ :=
    hRst hr1 σ' ⟨_, σ1, hdec, he1, he2⟩
  have hF : FK σ σ' := ((fk_setThreadState _ _).of_eq he1).trans ((fk_invokeSchedControlConfigureFlags _).of_eq he2)
  have hCR'' : CurRun σ' := curRun_sc_step hkc hcur he1 (NKT.of_eq (nkt_invokeSchedControlConfigureFlags _) he2)
  have hwT := WritesIn.tfoot_of_kfoot hw
  exact ⟨σ', Ac', Lst', D', J.sc_frame hwT hK hX' hCR' hRF' hY' hM' (J.sc_buf hwT hK) hRP' (J.sc_apart hwT hK)
    (J.sc_jpl hwT hK) (J.sc_jcov hwT hDead hCov) (J.sc_kern hwT hK hF hX' hDbg hDD)
    (J.sc_utc hwT hK hDbg) hN' hI' hC' (hC'.elim hOw' (curOwn_of_curInv hX'.fin.1.1.1 hI')) hO' hAI' hB' hSV' hCR'' hBlk'⟩

set_option maxHeartbeats 4000000 in
/-- **The SchedContext cap on `JAt`** for Bind, UnbindObject and a YieldTo
from an SC yielded to by none: when the invocation returns no data, `JAt`
after (`XTop` by `xtop_sc_step`, the relations by `ScAll`, `BlockedScActive`
by `bk_invokeSchedContext` with Bind's decode check, `rdp_decodeBind`); a
YieldTo returning at once has replied (its `XTop` the reply leaf's, the
second disjunct). Named per-op premise `hRest` (module docstring). -/
theorem sched_contextJ_step {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hres : σ.schedulerAction ≠ .chooseNewThread)
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
    (hArch : syscall.decode_invocation st arI s a lbl length slot (.SchedContext sc sb) blk call don fp buf extra
      ⦃ r => ∀ c, AR a c → AR r.2.2 c ⦄)
    (hRest : syscall.decode_invocation st arI s a lbl length slot (.SchedContext sc sb) blk call don fp buf extra
      ⦃ r => r.1 = .Ok () → ∀ σ1, (∃ inv σ0,
        (Fl4Spec.decodeSchedContextInvocation (Z := Unit) slbl sc.bv (excaps.map Prod.fst)).run σ = ({(.ok inv, σ)}, False) ∧
        Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ0)}, False) ∧
        Fl4Spec.invokeSchedContext (Z := Unit) inv σ0 = ({([], σ1)}, False)) →
        ScStepRest (L := L) arI Z H Cs D s r.2.1 σ1 ⦄) :
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
  obtain ⟨Ac', D', hC', hOw', hO', hAI', hSV', ⟨hDD, hDead, hCov⟩, hDbg, hBlk'⟩ :=
    hRst hr1 σ2 ⟨inv, σ0, hrun, he0, he1⟩
  have hF : FK σ σ2 := ((fk_setThreadState _ _).of_eq he0).trans (fk_invokeSchedContext hshape _ hm1)
  have hCR'' : CurRun σ2 := curRun_sc_step hkc hcur he0 hK1
  have hKt := hK0.trans (hK1.mono fun _ h => h.elim)
  exact ⟨σ2, Ac', Lst', D', J.sc_frame hW hKt hX' hCR' hRF' hY' hM' (J.sc_buf hW hKt) hRP' (J.sc_apart hW hKt)
    (J.sc_jpl hW hKt) (J.sc_jcov hW hDead hCov) (J.sc_kern hW hKt hF hX' hDbg hDD)
    (J.sc_utc hW hKt hDbg) hN' hI' hC' (hC'.elim hOw' (curOwn_of_curInv hX'.fin.1.1.1 hI')) hO' hAI' hB' hSV' hCR'' hBlk'⟩

end

end

end Fl4Proofs.P3
