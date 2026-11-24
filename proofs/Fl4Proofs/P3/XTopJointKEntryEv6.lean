/-
P3 (DESIGN.md §9), invariant line G4 (g4i, KENTRY-PLAN g4i; g4g's handoff (9)):
**an interrupt that arrives while the idle thread runs**, at `J`.

The interrupt entry's budget check (`update_timestamp; check_budget`) was
proved (`JAtZ.utCheckB`) for a non-idle running thread. In the idle thread
the current SC is the idle SC (`ValidIdle` / `IdleOK`: the idle TCB's SC is
`idleSc`, and `CurInv` the current thread's SC is the current SC); when the
idle SC's head is insufficient, both sides charge it as l4v
`charge_budget` / FL4 `charge_budget` do for the idle SC: no refill and no
SC write (`curSc = idleSc`), the consumed time reset, and the idle thread is
not schedulable (`idleThreadState`), so neither `end_timeslice` runs:

* `chargeHead_idle`, `schedulable_idle`, `chargeBudget_idle` (spec), and
  `charge_budget_idle` (FL4, at `SchedRel`): both charges are the consumed
  reset alone, for either `can_timeout_fault`;
* `JHole.chargeBudgetJ0`: ScChargeH's `JHole.chargeBudgetJ` without
  `ct ≠ idle` (that premise only gave the current SC's activity; the idle SC
  is active by its refill max, `ScRel.idle`);
* `JHole.chargeBudgetIJ` / `JHole.checkBudgetFI`: the charge and the
  insufficient `check_budget` in the idle thread at `J`;
* `JAtZ.utCheckBI`: `JAtZ.utCheckB` for `ct = idle`, the scheduler action
  resumed (in place of `Entered`); the sufficient branch is unchanged;
* `jEvRef_irqI`: g4f's `jEvRef_irq` in the idle thread; `jEvRef_irqA`: the
  interrupt entry from any current thread (no `ct ≠ idle`).
-/
import Fl4Proofs.P3.XTopJointKEntryEv5
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

/-- The charge's head does nothing on the idle SC. -/
theorem chargeHead_idle (u : Ticks) {σ : State Unit} (hcs : σ.curSc = σ.idleSc) :
    chargeHead u σ = ({((), σ)}, False) := by
  unfold chargeHead
  rw [nd_gets_bind, nd_gets_bind]
  unfold Fl4Spec.NonDet.when
  rw [if_neg (by simp [hcs])]
  rfl

/-- The idle thread is not schedulable. -/
theorem schedulable_idle {σ : State Unit} (hIO : IdleOK σ) (hct : σ.curThread = σ.idleThread) (c : Ticks) :
    schedulable σ.curThread { σ with consumedTime := c } = false := by
  obtain ⟨x, hk, -, hst, -⟩ := hIO
  cases hb : schedulable σ.curThread { σ with consumedTime := c }
  · rfl
  · exfalso
    obtain ⟨x', scp, y, n, hk', -, hr, -⟩ := schedulable_inv hb
    have hk'' : σ.kheap σ.curThread = some (.tcb x') := hk'
    rw [hct, hk] at hk''
    cases hk''
    rw [hst] at hr
    exact absurd hr (by first | decide | simp [Fl4Spec.runnable])

/-- **`chargeBudget` in the idle thread** is the consumed-time reset (either
`canTimeout`). -/
theorem chargeBudget_idle (u : Ticks) (tf : Bool) {σ : State Unit} (hcs : σ.curSc = σ.idleSc)
    (hIO : IdleOK σ) (hct : σ.curThread = σ.idleThread) :
    chargeBudget (Z := Unit) u tf σ = ({((), { σ with consumedTime := 0 })}, False) := by
  rw [chargeBudget_eq, nd_bind_one (chargeHead_idle u hcs), chargeTail_eq tf σ rfl, schedulable_idle hIO hct]
  simp only [Bool.false_eq_true, ↓reduceIte]

end Spec

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- **FL4's `charge_budget` in the idle thread** is the node's `CONSUMED`
reset (either `can_timeout_fault`). -/
theorem charge_budget_idle {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ)
    (hcsi : (nodeW st s c layout.node.CUR_SC).bv = σ.idleSc) (hct : σ.curThread = σ.idleThread)
    (hIO : IdleOK σ) (used : U64) (tf : Bool) :
    sched.charge_budget st ar s a used tf = ok (L.wr s (L.nodeAt s c layout.node.CONSUMED) 0#u64, a) := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hctT : nodeW st s c layout.node.CUR_THREAD ∈ T := hc.curT
  obtain ⟨v1, hv1, ev1⟩ := spec_exists (sched.cur_sc.spec' (L := L) s)
  obtain ⟨v2, hv2, ev2⟩ := spec_exists (sched.idle_sc.spec' (L := L) s)
  rw [hc.cur] at ev1 ev2
  subst ev1 ev2
  unfold sched.charge_budget
  rw [hv1, hv2]
  simp only [bind_ok]
  rw [sc_ne_eq]
  have hn : ¬ (nodeW st s c layout.node.CUR_SC ≠ nodeW st s c layout.node.IDLE_SC) := fun h =>
    h (eq_of_bv (hcsi.trans hS.idle.symm))
  have hn' : decide (nodeW st s c layout.node.CUR_SC ≠ nodeW st s c layout.node.IDLE_SC) = false :=
    decide_eq_false hn
  simp only [bind_ok, hn', Bool.false_eq_true, ↓reduceIte]
  obtain ⟨s3, hs3e, hs3⟩ := spec_exists (sched.set_consumed.spec' (L := L) s 0#u64)
  rw [hc.cur] at hs3
  subst hs3
  rw [hs3e]
  simp only [bind_ok]
  obtain ⟨hS3, hf3, -⟩ := hS.set_node_consumed 0#u64
  have e1 : nodeW st (L.wr s (L.nodeAt s c layout.node.CONSUMED) 0#u64) c layout.node.CUR_THREAD =
      nodeW st s c layout.node.CUR_THREAD :=
    eq_of_bv (by rw [← hS3.lists.choose_spec.choose_spec.2.curThread]; exact hs.curThread)
  have hc3 := hS3.lists.choose_spec.choose_spec.1.cur
  obtain ⟨v3, hv3, ev3⟩ := spec_exists (sched.cur_thread.spec' (L := L)
    (L.wr s (L.nodeAt s c layout.node.CONSUMED) 0#u64))
  rw [hc3, e1] at ev3
  subst ev3
  rw [hv3]
  simp only [bind_ok]
  have hR3 : NtfnStateRel N T (L.mem (L.wr s (L.nodeAt s c layout.node.CONSUMED) 0#u64))
      { σ with consumedTime := (0#u64).bv } :=
    Notif.NtfnStateRel.frame hR hS.placed hf3 ⟨fun _ _ h => h, fun _ x h => ⟨x, h, rfl, rfl, rfl⟩⟩
  obtain ⟨b1, hb1e, hb1⟩ := spec_exists (sched.is_schedulable.spec' (L := L)
    (L.wr s (L.nodeAt s c layout.node.CONSUMED) 0#u64) (nodeW st s c layout.node.CUR_THREAD))
  rw [schedulable_eq hR3 hS3 hctT, ← hs.curThread, schedulable_idle hIO hct] at hb1
  rw [hb1e, hb1]
  simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]

end

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 32000000 in
/-- **`JHole.chargeBudgetJ` without `ct ≠ idle`** (g4i: the idle SC is active by its refill max, `ScRel.idle`): ScChargeJ's `JAtZ.chargeBudgetJ` at the state after
`update_timestamp`, where `OffOK` need not hold. -/
theorem JHole.chargeBudgetJ0 {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hAT : P0.ArchTotal arI)
    (hC : CurInv σ)
    (hnsw : σ.schedulerAction ≠ .switchThread σ.curThread)
    (hmrt : sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄) (used : U64) :
    sched.charge_budget st arI s a used false ⦃ r => r.2 = a ∧ ∃ σ',
      Fl4Spec.chargeBudget (Z := Unit) used.bv false σ = ({((), σ')}, False) ∧ ScTKw (fun _ => False) σ σ' ∧
      ∃ Lst' : U64 → List U64, JAtZ (L := L) arI AR Z H Cs Ac Lst' D r.1 a σ' ⦄ := by
  have J := Hh.j0
  obtain ⟨hK0, hsok0, hlk0, hfk0, ekh, -, -, -, earch, -, hcrσ, hbsaσ⟩ := Hh.sfacts
  have hP0 := J.ip
  have hS0 := J.xtop.fin.1.1.1
  have hS := Hh.xtop.fin.1.1.1
  have hR := Hh.xtop.fin.1.1.2.2.1
  have hARs := Hh.xtop.fin.1.1.2.2.2.2.2.2
  have hT : TcbPlaced Z.T := hP0.e.tcb
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  obtain ⟨hscC, hsc0, htw, hts, hact, hnr, hnb⟩ := CurInv.facts hS Hh.inv hC
  have hct : nodeW st s Z.c layout.node.CUR_THREAD ∈ Z.T := hc.curT
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hthc : Z.th (nodeW st s Z.c layout.node.CUR_THREAD) = some .tcb := (hJ.tcb _).2 (J.zH.1 _ hct)
  have ecur : L.curW s = nodeW st s Z.c layout.node.CUR_THREAD := by
    show L.mem s (L.nodeAt s (L.cpu s) _) = _; rw [hc.cur]; rfl
  have ecsc : L.cscW s = nodeW st s Z.c layout.node.CUR_SC := by
    show L.mem s (L.nodeAt s (L.cpu s) _) = _; rw [hc.cur]; rfl
  obtain ⟨xt, hkt, hxs, hnbt⟩ := hC.tcb
  have hpc : (nodeW st s Z.c layout.node.CUR_SC).bv = σ.curSc := hs.curSc.symm
  obtain ⟨x, n, hk, hx⟩ := hs.scs _ hscC
  have hxa : Fl4Spec.scActive x = true := by
    by_cases hi : (nodeW st s Z.c layout.node.CUR_SC).bv = σ.idleSc
    · exact hx.active_of_rmax (hx.idle hi)
    · exact hact hi x n hk
  have hscS : nodeW st s Z.c layout.node.CUR_SC ∈ P1.Heap.scs H :=
    ⟨_, (hJ.sc _ x n hsc0 (by rw [← ekh]; exact hk)).2⟩
  have hcA : L.cscW s ∈ Ac := by
    rw [ecsc]; exact (Hh.blk.2.2.2.1.act _ hscS).2 (fun e => hx.rmax_ne hxa (by rw [e]; rfl))
  have hne : σ.curThread ≠ (nodeW st s Z.c layout.node.CUR_SC).bv := fun e => by
    rw [e, hk] at hkt; cases hkt
  obtain ⟨⟨Q1, R1, h1⟩, hB1, hX1, hS1, hSg1⟩ := Hh.blk
  have hcsc1 : L.mem s (scA (L.curW s)) ≠ 0#u64 → L.cscW s = L.mem s (scA (L.curW s)) := fun _ => by
    rw [ecur, ecsc, hts]
  have hna : L.actionW s ≠ L.curW s := by
    rw [ecur]; exact actionW_ne_of hS hct (by rw [← hs.curThread]; exact hnsw)
  have hval : ∀ (s' : S) (σ' : Fl4Spec.State Unit), SchedRel st Z.N Z.T Z.C Z.c s' σ' →
      TmoKeep st (nodeW st s Z.c layout.node.CUR_THREAD) s σ s' σ' →
      faults.valid_timeout_handler st s' (nodeW st s Z.c layout.node.CUR_THREAD) ⦃ b =>
        Fl4Spec.isValidTimeoutHandler (Z := Unit) (nodeW st s Z.c layout.node.CUR_THREAD).bv σ' =
          ({(b, σ')}, False) ⦄ :=
    fun s' σ' _ hK => hval_of_rel Hh.xtop.rel.1 Hh.xtop.rel.2.1.1 hthc s' σ' hK
  refine WP.spec_mono (WP.spec_and (charge_budget_refinesF (ar := arI) s a σ hAT hS hR Hh.nsc Hh.inv hscC hsc0
    htw hts hS.idle hact hnr hnb hmrt hmb hval used)
    (P1.sched.charge_budget.allF (G := fun s' => P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H)
      (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s s') hAT s a used Q1 R1 h1 hB1 hX1 hSg1 hS1 hcsc1 hna hcA
      (fun _ _ g1 g2 => g1.trans g2) (P1.WritesIn.refl _ _))) ?_
  rintro ⟨s', a'⟩ ⟨⟨σ', hsp, hS', hI', hR', hN', hact', hcons, hAI, hWK, hra, σ2, hH, ht2⟩, hP1⟩
  try simp only [WP.uncurry'_pair] at hP1
  obtain ⟨hbx, hfoot⟩ := hP1
  have mem0 : ((), σ') ∈ (Fl4Spec.chargeBudget (Z := Unit) used.bv false σ).1 := by
    rw [hsp]; exact Set.mem_singleton _
  refine ⟨hra, σ', hsp, nkt_chargeBudgetF _ σ _ mem0, ?_⟩
  have mem : ((), σ') ∈ (Fl4Spec.chargeBudget (Z := Unit) used.bv false σ).1 := by
    rw [hsp]; exact Set.mem_singleton _
  have hK : ScTKw (fun _ => False) σ σ' := nkt_chargeBudgetF _ σ _ mem
  have hsok : SOK (true, true) σ σ' := pres_chargeBudgetF _ _ σ _ mem
  have hlk : LK (fun _ => False) σ σ' := lkm_chargeBudgetF _ _ σ _ mem
  have hfk : FK σ σ' := fk_chargeBudgetF _ σ _ mem
  have ek : σ'.kheap = σ2.kheap := kh_chargeTailF σ2 ((), σ') (by rw [ht2]; exact Set.mem_singleton _)
  obtain ⟨-, -, -, -, -, -, -, -, hfr2, hsck2⟩ := hH
  have hkp : ∀ q, q ≠ (nodeW st s Z.c layout.node.CUR_SC).bv → σ'.kheap q = σ.kheap q := fun q hq => by
    rw [ek]; exact hfr2 q hq
  obtain ⟨y, hky, hyt, hym⟩ := hsck2 x n hk
  have hky' : σ'.kheap (nodeW st s Z.c layout.node.CUR_SC).bv = some (.schedContext y n) := by rw [ek]; exact hky
  have hya : Fl4Spec.scActive y = true := by simp only [Fl4Spec.scActive, hym]; exact hxa
  -- the composite step from the base
  have hKc : ScTKw (fun _ => False) σ0 σ' := hK0.trans hK
  have hsokc : SOK (true, true) σ0 σ' := hsok0.trans hsok
  have hlkc : LK (fun _ => False) σ0 σ' := hlk0.trans hlk
  have hfkc : FK σ0 σ' := hfk0.trans hfk
  have hWK0 : P1.WritesIn st s0 s' (KFoot st Z.T Z.N Z.C Z.c s0 σ0) :=
    WritesIn.kfoot_trans Hh.ws (fun sc _ x1 n1 h => ⟨x1, by rw [← ekh]; exact h⟩) hWK
  have hW : P1.WritesIn st s0 s' (TFoot st Z.T Z.N Z.C Z.c s0 σ0) := WritesIn.tfoot_of_kfoot hWK0
  have hX' : XTopAt (L := L) AR Z s' a σ' :=
    xtop_sc_step (ct := σ0.curThread) J.xtop hP0 J.nk hW hKc.ofFalse hS' hR' fun _ => by rw [← earch]; exact hARs
  have hY : YieldRel Z.T Z.C (L.mem s') σ' :=
    J.yld.frame (fun y1 hy1 => hWK0.mem_eq (yieldA_aligned hT hy1) fun hb => hb.ne_yield hS0 hy1 rfl)
      (hsokc.ykeep rfl)
  obtain ⟨-, hY', hM', ⟨Lst', hCR', hRF'⟩, hRP', -⟩ :=
    ScAll.of_tr hS0 J.rp J.mcp J.call J.rfree ⟨hS', hR', hN', hI'⟩ hY (hW.mono fun _ h => Or.inl h) hsokc rfl
  have hAI' := hAI Hh.act
  have eN : L.nodeAt s 0#u64 layout.node.DEBUG_TCBS = L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS :=
    P1.nodeAt_of_ksb Hh.ws.1 _ _
  have hDbg : L.mem s' (L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS) =
      L.mem s0 (L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS) := by
    rw [← Hh.dbg]
    exact hfoot.mem_eq J.kern.dwAl fun hk => P1.dbg0_not_schedW Hh.blk J.kern.cs0 (Or.inl (by rw [eN]; exact hk))
  have hidW := J.idleW_keep hS' hfkc.2.1 hfkc.2.2
  have hblk' : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s' :=
    ⟨hbx.1, hbx.2.1, hbx.2.2.1, hbx.2.2.2.2, hbx.2.2.2.1⟩
  have hcur' : σ'.schedulerAction = .chooseNewThread ∨ CurInv σ' := by
    rcases hact' with e | hH'
    · exact Or.inl e
    · right
      obtain ⟨hcs, hcc, hrq, -, -, -, -, -, -, -⟩ := hH'
      refine ⟨⟨xt, by rw [hcc, hkp _ hne]; exact hkt, by rw [hcs]; exact hxs, hnbt⟩,
        ⟨y, n, by rw [hcs, ← hpc]; exact hky'⟩, fun _ y1 n1 hy1 => ?_, by rw [hcc, hrq]; exact hC.notRel⟩
      rw [hcs, ← hpc, hky'] at hy1; cases hy1; exact hya
  have hown' : CurOwnW Z.T Z.C σ' := by
    obtain ⟨u, hu, xu, hku, hxu, hou, -⟩ := curOwn_of_curInv hS Hh.inv hC
    have hup : u.bv ≠ (nodeW st s Z.c layout.node.CUR_SC).bv := fun e => by rw [e, hk] at hku; cases hku
    refine Or.inl ⟨u, hu, xu, by rw [hkp _ hup]; exact hku, by rw [hfk.1]; exact hxu, fun y1 n1 hy1 => ?_,
      fun h0 => absurd h0 (by rw [hcons]; decide)⟩
    rw [hfk.1, ← hpc, hky'] at hy1; cases hy1
    rw [hyt]; exact hou x n (by rw [← hpc]; exact hk)
  have hoff : OffOK σ' := fun h0 => absurd h0 (by rw [hcons]; decide)
  have hcr : CurRunM σ' := by
    rcases hact' with e | hH'
    · exact Or.inl (act_cn_nr e)
    · obtain ⟨-, hcc, -, hac, -, hid, -, -, -, -⟩ := hH'
      rcases hcrσ with h | h
      · exact Or.inl (by rw [hac]; exact h)
      · right
        rcases h with h | h
        · left; intro y1 hy1; rw [hcc, hkp _ hne] at hy1; exact h y1 hy1
        · right; rw [hcc, hid]; exact h
  have hbsa : BlockedScActive σ' := by
    refine hbsaσ.back (fun q y1 n1 hq ha => ?_) (fun t x1 hx1 hq => ?_)
    · by_cases e : q = (nodeW st s Z.c layout.node.CUR_SC).bv
      · rw [e, hky'] at hq; cases hq; rw [hya] at ha; cases ha
      · exact ⟨y1, by rw [← hkp q e]; exact hq, ha, fun _ h => h, id⟩
    · have e : t ≠ (nodeW st s Z.c layout.node.CUR_SC).bv := fun e => by rw [e, hky'] at hx1; cases hx1
      exact ⟨x1, by rw [← hkp t e]; exact hx1, hq⟩
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := fun q hq =>
    J.deadP_sc_stepQ hX' hW hKc (fun _ h => h.elim) hlkc hfkc hAI'.1 hY' ((hsokc.ykeep rfl).dk q.bv) (fun h => h)
      (J.jcov.dead q hq)
  have hKd : P1.DbgKeep st (P1.Heap.tcbs H) Cs s0 s' :=
    (Hh.dbgK.trans (P1.Foot.dbgKeep Hh.blk (by first | exact fun _ h => h | exact Set.empty_subset _) hfoot))
  exact ⟨Lst', J.sc_frame hW hKc hX' hCR' hRF' hY' hM' (J.sc_buf hW hKc) hRP' (J.sc_apart hW hKc)
    (J.sc_jpl hW hKc hidW.2) (J.sc_jcov hW hdead (fun q hq hn => absurd hq hn) hidW hKd subset_rfl)
    (J.sc_kern hW hKc hfkc hX' hDbg fun _ h => h) (J.sc_utc hW hKc hDbg) hN' hI' hcur' hown' hoff hAI' hbsa hcr
    hblk' hKd
    hidW.1 J.zD⟩



/-- In the idle thread the current SC is the idle SC (`CurInv` and `IdleOK`). -/
theorem JHole.curSc_idle {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hC : CurInv σ)
    (hid : σ.curThread = σ.idleThread) : σ.curSc = σ.idleSc := by
  obtain ⟨xt, hkt, hxs, -⟩ := hC.tcb
  obtain ⟨x, hk, hx, -, -⟩ := Hh.act.2
  rw [hid, hk] at hkt
  cases hkt
  exact Option.some.inj (hxs.symm.trans hx)

set_option maxHeartbeats 8000000 in
/-- **`charge_budget` with `can_timeout_fault = true` in the idle thread** from a
`JHole` (module docstring): the charge with `false` (`JHole.chargeBudgetJ0`),
both sides' flags irrelevant (`charge_budget_idle`, `chargeBudget_idle`). -/
theorem JHole.chargeBudgetIJ {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hAT : P0.ArchTotal arI)
    (hC : CurInv σ) (hid : σ.curThread = σ.idleThread)
    (hnsw : σ.schedulerAction ≠ .switchThread σ.curThread)
    (hmrt : sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄) (used : U64) :
    sched.charge_budget st arI s a used true ⦃ r => r.2 = a ∧ ∃ σ',
      Fl4Spec.chargeBudget (Z := Unit) used.bv true σ = ({((), σ')}, False) ∧ ScTKw (fun _ => False) σ σ' ∧
      ∃ Lst' : U64 → List U64, JAtZ (L := L) arI AR Z H Cs Ac Lst' D r.1 a σ' ⦄ := by
  have hS := Hh.xtop.fin.1.1.1
  have hR := Hh.xtop.fin.1.1.2.2.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hcs := Hh.curSc_idle hC hid
  have hcsi : (nodeW st s Z.c layout.node.CUR_SC).bv = σ.idleSc := by rw [← hs.curSc]; exact hcs
  have hIO : IdleOK σ := Hh.act.2
  rw [charge_budget_idle (ar := arI) s a σ hS hR hcsi hid hIO used true,
    ← charge_budget_idle (ar := arI) s a σ hS hR hcsi hid hIO used false]
  refine WP.spec_mono (Hh.chargeBudgetJ0 hAT hC hnsw hmrt hmb used) ?_
  rintro r ⟨h1, σ', h2, h3, h4⟩
  refine ⟨h1, σ', ?_, h3, h4⟩
  rw [chargeBudget_idle used.bv true hcs hIO hid]
  rw [chargeBudget_idle used.bv false hcs hIO hid] at h2
  exact h2

set_option maxHeartbeats 8000000 in
/-- **`check_budget` charging from a `JHole` for the idle thread** (`JHole.checkBudgetF` with `ct = idle`
in place of `ct ≠ idle` and `NoTmoSend`: the idle thread is never schedulable, so no timeout fault). -/
theorem JHole.checkBudgetFI {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hAT : P0.ArchTotal arI)
    (hC : CurInv σ) (hid : σ.curThread = σ.idleThread)
    (hnsw : σ.schedulerAction ≠ .switchThread σ.curThread)
    (hmrt : sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄) :
    sched.check_budget st arI s a ⦃ r => r.1 = false → r.2.2 = a ∧ ∃ σ',
      Fl4Spec.checkBudget (Z := Unit) σ = ({(false, σ')}, False) ∧ ScTKw (fun _ => False) σ σ' ∧
      ∃ Lst' : U64 → List U64, JAtZ (L := L) arI AR Z H Cs Ac Lst' D r.2.1 a σ' ⦄ := by
  have hS := Hh.xtop.fin.1.1.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨hscC, -, -, -, hact, -, -⟩ := CurInv.facts hS Hh.inv hC
  obtain ⟨x, n, hk, hx⟩ := hs.scs _ hscC
  unfold sched.check_budget
  step with sched.cur_sc.spec' as ⟨sc', hsc'⟩
  step with sched.consumed.spec' as ⟨cn, hcn⟩
  rw [hc.cur] at hsc' hcn
  subst hsc' hcn
  have hax : Fl4Spec.scActive x = true := by
    by_cases hi : (nodeW st s Z.c layout.node.CUR_SC).bv = σ.idleSc
    · exact hx.active_of_rmax (hx.idle hi)
    · exact hact hi x n hk
  refine WP.spec_bind (sufficient_refines s a σ hS hscC hk hax _ hmb) ?_
  intro b hb
  by_cases hbt : b = true
  · rw [if_pos hbt, is_cur_domain_expired_eq]
    simp only [bind_ok]
    refine (WP.spec_ok _).2 ?_
    intro h; exact absurd h (by simp)
  · rw [if_neg hbt]
    have hbf : b = false := by simpa using hbt
    subst hbf
    refine WP.spec_bind (Hh.chargeBudgetIJ hAT hC hid hnsw hmrt hmb (nodeW st s Z.c layout.node.CONSUMED)) ?_
    rintro ⟨s1, a1⟩ ⟨ha1, σ', h1, hK, J'⟩
    refine (WP.spec_ok _).2 fun _ => ⟨ha1, σ', ?_, hK, J'⟩
    have hb' : Fl4Spec.getScRefillSufficient (Z := Unit) σ.curSc σ.consumedTime σ = ({(false, σ)}, False) := by
      rw [hs.curSc, hs.consumed]; exact hb
    have h1' : Fl4Spec.chargeBudget (Z := Unit) σ.consumedTime true σ = ({((), σ')}, False) := by
      rw [hs.consumed]; exact h1
    unfold Fl4Spec.checkBudget
    rw [nd_gets_bind, nd_gets_bind, Notif.nd_bind_one hb']
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [nd_gets_bind, Notif.nd_bind_one h1']
    rfl

set_option maxHeartbeats 16000000 in
/-- **`update_timestamp; check_budget` at an entry state of the idle thread** (`JAtZ.utCheckB` with
`ct = idle` and a resumed scheduler action in place of `Entered`). -/
theorem JAtZ.utCheckBI {s : S} {a : A} {σ0 : Fl4Spec.State Unit}
    (J0 : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ0) [VxE Z] (hres0 : σ0.schedulerAction = .resumeCurThread)
    (hid0 : σ0.curThread = σ0.idleThread) (hBu : KBudgetB arI a σ0) (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    (do let (s1, a1) ← sched.update_timestamp st arI s a; sched.check_budget st arI s1 a1) ⦃ r =>
      ∃ z ∈ ((Fl4Spec.updateTimeStamp (Z := Unit) >>= fun _ => Fl4Spec.checkBudget) σ0).1, z.1 = r.1 ∧
        ∃ (Z' : XSets) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
          JAtZ (L := L) arI AR Z' H Cs Ac' Lst' D' r.2.1 r.2.2 z.2 ∧ VxE Z' ⦄ := by
  have hnow := hBu.now
  have hS := J0.xtop.fin.1.1.1
  have hR := J0.xtop.fin.1.1.2.2.1
  have hnow' : arI.now a ⦃ r => ∃ ms, Fl4Spec.doMachineOp (Z := Unit) Fl4Spec.getCurrentTime σ0 =
      ({(r.1.bv, { σ0 with machineState := ms })}, False) ∧ σ0.curTime ≤ r.1.bv ⦄ :=
    WP.spec_mono hnow fun _ ⟨ms, h1, h2, _⟩ => ⟨ms, h1, h2⟩
  refine WP.spec_bind (WP.spec_and (WP.spec_and (J0.timestampJ arI hAK hA hnd hnow) (J0.timestampJH hAK hA hnd hnow))
    (update_timestamp_refines s a σ0 hS hR J0.nsc hnd hnow')) ?_
  rintro ⟨s1, a1⟩ ⟨⟨⟨σ1, h1, -, -, -, -, -, hum1, hO1, hJ1⟩, ⟨σ1', h1', -, -, -, -, -, hum1', -, hH⟩⟩,
    ⟨σ1'', h1'', hS1, -, -, hI1, hC1, -, -⟩⟩
  have e1 : σ1 = σ1' := congrArg Prod.snd (Set.singleton_eq_singleton_iff.1 (Prod.mk.inj (h1.symm.trans h1')).1)
  have e2 : σ1 = σ1'' := congrArg Prod.snd (Set.singleton_eq_singleton_iff.1 (Prod.mk.inj (h1.symm.trans h1'')).1)
  subst e1 e2
  have hsp0 : ∀ y, y ∈ (Fl4Spec.checkBudget (Z := Unit) σ1).1 →
      y ∈ ((Fl4Spec.updateTimeStamp (Z := Unit) >>= fun _ => Fl4Spec.checkBudget) σ0).1 := by
    intro y hy; rw [Notif.nd_bind_one h1]; exact hy
  have Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s a σ0 s1 a1 σ1 := hH σ1.machineState a1 hum1' id
  have hI1 := hI1 J0.inv
  have hC1 := hC1 hBu.cur
  obtain ⟨hscC, -, -, -, hact, -, -⟩ := CurInv.facts hS1 hI1 hC1
  obtain ⟨-, -, -, -, ekh, ect, eact, eidle, -, -, -, -⟩ := Hh.sfacts
  obtain ⟨ms1, tm1, cn1, -, eσ1⟩ := Hh.spec
  have erq : σ1.readyQueues = σ0.readyQueues := by rw [eσ1]
  have ecs : σ1.curSc = σ0.curSc := by rw [eσ1]
  have hres1 : σ1.schedulerAction = .resumeCurThread := eact.trans hres0
  have hCH : CurInv σ1 := Hh.cur.resolve_left (by rw [hres1]; exact fun h => by cases h)
  have hid1 : σ1.curThread = σ1.idleThread := by rw [ect, eidle]; exact hid0
  have hnsw1 : σ1.schedulerAction ≠ .switchThread σ1.curThread := by rw [hres1]; exact fun h => by cases h
  -- the charge (the head is insufficient)
  have hFalse : sched.check_budget st arI s1 a1 ⦃ r => r.1 = false →
      ∃ z ∈ (Fl4Spec.checkBudget (Z := Unit) σ1).1, z.1 = false ∧
        ∃ (Z' : XSets) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
          JAtZ (L := L) arI AR Z' H Cs Ac' Lst' D' r.2.1 r.2.2 z.2 ∧ VxE Z' ⦄ := by
    refine WP.spec_mono (Hh.checkBudgetFI hA hCH hid1 hnsw1 (hmrt a1) (hmb a1)) ?_
    rintro ⟨rb, s2, a2⟩ hB hf
    obtain ⟨ea, σ2, hcb, -, Lst2, J2⟩ := hB hf
    simp only at ea J2
    subst ea
    exact ⟨(false, σ2), by rw [hcb]; exact Set.mem_singleton _, rfl, Z, Ac, Lst2, D, J2, inferInstance⟩
  refine WP.spec_mono (WP.spec_and (check_budgetT hA s1 a1 σ1 hS1 hscC hact (hmb a1)) hFalse) ?_
  rintro ⟨rb, s2, a2⟩ ⟨hT, hF⟩
  cases rb with
  | false =>
    obtain ⟨z, hz, hz1, Z', Ac', Lst', D', J', _⟩ := hF rfl
    exact ⟨z, hsp0 z hz, hz1, Z', Ac', Lst', D', J', inferInstance⟩
  | true =>
    obtain ⟨e, hb, hsuf⟩ := hT rfl
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
    have hOR1 : OffReady σ1 := hO1 hBu.off
    have hOK : OffOK σ1 := hOR1.ok hsuf
    have hOw : CurOwnW Z.T Z.C σ1 := Or.inl (curOwn_of_curInv hS1 hI1 hC1)
    obtain ⟨-, hJ⟩ := hJ1 σ1.machineState _ hum1 id
    obtain ⟨Ac', Lst', D', J'⟩ := hJ hOK hOw
    exact ⟨(true, σ1), hsp0 _ (by rw [checkBudget_suff hnd hb]; exact Set.mem_singleton _), rfl, Z, Ac', Lst', D', J', inferInstance⟩


end

/-! ## The interrupt entry in the idle thread -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

open Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvF in
set_option maxHeartbeats 16000000 in
/-- **The interrupt entry in the idle thread** (`jEvRef_irq` with `ct = idle` in place of `ct ≠ idle`:
`JAtZ.utCheckBI` for the budget check; the scheduler action resumed by `SInvX`'s `SInvCR`). -/
theorem jEvRef_irqI {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a a' : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] (hX : SInvX σ) (hid : σ.curThread = σ.idleThread)
    {w : U64} (hI : IrqHw AR MR a a' σ w)
    (hFin : ∀ x ∈ ((Fl4Spec.NonDetE.handleE (Fl4Spec.fl4HandleEvent (Z := Unit) true .interrupt)
        (fun _ => Fl4Spec.withoutPreemption Fl4Spec.preemptionPath)).run σ).1,
      ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a'' : A),
        KFrontI (st := st) arI s a' w s' a'' → JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a'' x.2 →
        KFinAtR31 (L := L) arI AR Z' H' Cs' s' a'' x.2)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.handle_interrupt_entry st arI s a' w ⦃ r =>
      ∃ σ', EvOut false .interrupt σ σ' ∧ RJM (L := L) arI AR MR r.1 r.2 σ' ⦄ := by
  obtain ⟨i, hgl, hwi⟩ := hI.line
  have hres : σ.schedulerAction = .resumeCurThread := hX.cr.2
  have hS := hX.sb
  have hNS : NativeScope σ := hS.1.1.ns
  have hMK := hKD.toK
  obtain ⟨Lst0, J0⟩ := J.msArJ σ.machineState a' rfl (hI.ar _)
  have J0' : JAtZ (L := L) arI AR Z H Cs Ac Lst0 D s a' σ := J0
  have hC : CurInv σ := J.cur.resolve_left (by rw [hres]; intro e; cases e)
  have hBu : KBudgetB arI a' σ := ⟨nowAgree_gai hM hI.mr hS.1.1.vmt, hC, hX.offReady, Or.inr hX.ctQ⟩
  -- the FPU-owner fact at the event's outcomes
  obtain ⟨x0, hx0, ha0⟩ := (SInvAll.SInvB.entryJEv (ev := .interrupt) hS (fun h => absurd rfl h)).ctAct
  have hNQ : NQ [σ.curThread] σ := nq_cons ((nq_nil_iff σ).2 ⟨hS.1.1.nq, hS.1.1.epq⟩) fun x hx => by
    rw [hx0] at hx; cases hx
    rcases ha0 with h1 | ⟨-, h1⟩
    · exact ok_of_active h1
    · rw [h1]; exact ⟨fun h => h, rfl⟩
  have hFN : FN [] σ := ⟨⟨(il_nil_iff σ).2 hS.1.1.live, nq_weak_nil _ hNQ⟩, hS.1.1.ft⟩
  rw [handle_interrupt_entry_eq]
  refine WP.spec_bind (spec_and_eq (WP.spec_and (J0'.utCheckBI hres hid hBu hARI.toARKeep hA hnd hmrt hmb hmax htu)
    (ut_cb_mr hM hMK hA hI.mr s)) fun _ h => h) ?_
  rintro ⟨b, s2, a2⟩ ⟨⟨⟨z, hz, -, Z2, Ac2, Lst2, D2, J2, _⟩, hM2⟩, heq1⟩
  -- the spec state after the budget check, then after the IRQ read
  have hE := Sched.updateTimeStamp_eq' hnd (doMachineOp_single (getCurrentTime_eq σ.machineState))
  have hz0 := hz
  obtain ⟨⟨u, σu⟩, hu, h2⟩ := hz0
  rw [hE] at hu
  have eu : σu = _ := congrArg Prod.snd (Set.mem_singleton_iff.1 hu)
  have hms : σu.machineState = gctState σ.machineState := by rw [eu]
  have his : σu.interruptStates = σ.interruptStates := by rw [eu]
  have hk := MachF.mfk_checkBudget σu _ h2
  have hVu : ValidIrqMasks σu := by
    intro j hj; rw [hms]; exact hS.1.1.vim j (his ▸ hj)
  have hV2 : ValidIrqMasks z.2 := msF_vim hVu hk
  have hk' := hk
  simp only [MachF.msF, Prod.mk.injEq] at hk'
  obtain ⟨k1, k2, k3, k4, -⟩ := hk'
  have hgl2 : gaiLine false z.2.machineState = some i := by
    rw [gaiLine_congr (ms := σ.machineState) (by rw [k1, hms]; rfl) (by rw [k2, hms]; rfl)]; exact hgl
  set σ3 : Fl4Spec.State Unit := { z.2 with machineState := gaiState z.2.machineState } with hσ3
  have hga : Fl4Spec.doMachineOp (Z := Unit) (Fl4Spec.getActiveIRQ false) z.2 = ({(some i, σ3)}, False) := by
    rw [doMachineOp_single (getActiveIRQ_eq false z.2.machineState), hgl2]
  have hR3 : MR a2 σ3.machineState := hM.frame a2 _ _ hM2
    (by show z.2.machineState.irqMasks = _; rw [k1, hms]; rfl)
    (by show z.2.machineState.irqState + 1 = _; rw [k2, hms]; rfl)
    (by show z.2.machineState.timeState = _; rw [k3, hms]; rfl)
    (by show z.2.machineState.lastMachineTime = _; rw [k4, hms]; rfl)
  obtain ⟨Lst3, J3⟩ := J2.msArJ (gaiState z.2.machineState) a2 rfl id
  have hN2 : NativeScope z.2 := ik_bind ns_updateTimeStamp (fun _ => ns_checkBudget) σ hNS z hz
  have hN3 : NativeScope σ3 := SInvN.ns_of_kheap rfl hN2
  have hact3 : σ3.interruptStates i ≠ .irqInactive := by
    intro hin
    have h1 := hV2 i hin
    rw [gaiLine_unmasked hgl2] at h1
    cases h1
  refine WP.spec_bind (spec_and_eq (J3.handleIrqJIM hARI hA hIA hM hMK hmb hN3 hR3 w i hwi hI.lt hI.n126 hI.n127)
    fun _ h => h) ?_
  rintro ⟨s3, a3⟩ ⟨hP, heq2⟩
  rcases hP with hin | ⟨z', hz', ⟨Z3, H3, Cs3, Ac3, Lst4, D3, J4, _⟩, hM3⟩
  · exact absurd hin hact3
  have hEv := mem_irqEv hz hga hz'
  have hx := mem_handleE_ok (h := fun _ => Fl4Spec.withoutPreemption (Z := Unit) Fl4Spec.preemptionPath) hEv
  have hN4 : NativeScope z'.2 := ns_handleEvent .interrupt σ hNS _ hEv
  have hfo : FpuOwnOK z'.2 := fpuOwnOK_of_ft (fo_handleEvent_int σ hFN _ hEv).2
  have hfr : KFrontI (st := st) arI s a' w s3 a3 := by
    unfold KFrontI; rw [heq1]; simp only [bind_ok]; exact heq2
  have F := ((hFin _ hx Z3 H3 Cs3 Ac3 Lst4 D3 s3 a3 hfr J4.toR).to27).toR hfo
  exact WP.spec_mono (jat_finishJRNM s3 a3 z'.2 J4.toR hN4 F.hd hnd hA F.vt hmb F.arch F.archNd F.fo F.sni F.send hT
    F.tail hmax htu hM hKD hM3) fun r ⟨σ', hmem, hRJ, hM'⟩ => ⟨σ', mem_kcall hx hmem, hRJ, hM'⟩


set_option maxHeartbeats 8000000 in
/-- **The interrupt entry from any current thread** (`jEvRef_irq` without
`ct ≠ idle`): `jEvRef_irq` for a non-idle thread, `jEvRef_irqI` for the idle
thread. -/
theorem jEvRef_irqA {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a a' : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] (hX : SInvX σ)
    {w : U64} (hI : IrqHw AR MR a a' σ w)
    (hFin : ∀ x ∈ ((Fl4Spec.NonDetE.handleE (Fl4Spec.fl4HandleEvent (Z := Unit) true .interrupt)
        (fun _ => Fl4Spec.withoutPreemption Fl4Spec.preemptionPath)).run σ).1,
      ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a'' : A),
        KFrontI (st := st) arI s a' w s' a'' → JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a'' x.2 →
        KFinAtR31 (L := L) arI AR Z' H' Cs' s' a'' x.2)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.handle_interrupt_entry st arI s a' w ⦃ r =>
      ∃ σ', EvOut false .interrupt σ σ' ∧ RJM (L := L) arI AR MR r.1 r.2 σ' ⦄ := by
  by_cases hct : σ.curThread = σ.idleThread
  · exact jEvRef_irqI J hX hct hI hFin hARI hA hnd hM hKD hIA hmrt hmb hT hmax htu
  · exact jEvRef_irq J hX hct hI hFin hARI hA hnd hM hKD hIA hmrt hmb hT hmax htu

end

end

end Fl4Proofs.P3
