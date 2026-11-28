/-
P3 (p3J gen 45): **the deletion loop's preempted state at stable ghosts, part 1: the hole and the MCS preemption
point** (item 3 of gen 44's plan, the `MidXP` preempted outcome).

A preempted deletion step stops in FL4's `preemption_point` returning `Preempted` (XTopJointDelR's `WJP`: the
pre-state is a `JAtZ (Z.mv G V) H Cs` state). The caller's `after_invocation (Err Preempted)` then runs
`mcs_preemption_point` and `check_interrupt`. The non-stable chain (XTopJointMRHole's `hPre_ofZQIMN`) builds
its exits with the hole's `Z`, `H`, `Cs` but states them as `JAt` (existential); here the same steps are stated
at the hole's sets (`JStab Z H Cs`), which is what P3JMidInv's `MidXP` needs.

* `msF_mrC`: `MR` moves along a spec step keeping `msF` (`MachPlatC.frame`).
* **`JAtZ.ppJHC`**: XTopJointMRPP's `JAtZ.ppJHM` over P3JDelMT's `MachPlatC` (the platform reads it uses are
  `now`, `irqPending`, `frame`); the one statement for `MachPlatC` users (the `MachPlat` original can be re-pointed
  to it in the proof collapse).
* **`JAtZ.preHoleC`**: from a `JAtZ` pre-state with `NoSwitch`, `PPR0`, `MR`, `ValidMachineTime`,
  `ValidIrqMasks` and a preempting `preemption_point`, the hole facts (XTopJointMRHole's `jAtPreMV_holeQ` at a
  fixed `JAtZ`, so the hole keeps the pre-state's `Z`, `H`, `Cs`).
* **`JHole.mcsStK`** / **`JHole.mcsSt`**: `mcs_preemption_point` from a hole whose spec state is `RR` (P3JRrSys:
  every SC round-robin), at the hole's `Z`, `H`, `Cs` (`JStab`), with `msF` kept (then `MR`, `ValidIrqMasks`)
  and `NativeScope` and `CKI` kept (P3JCkW's `ck_chargeBudget` / `ck_checkBudget`). Under `RR` the current SC has period `0`, so `NoTmoSend` holds and, with `CurInv`,
  the hole is `PPCov` (the endpoint-timeout case `PPCovT` and XTopJointMRHole's rest case
  `jPreemptRestHypEQ_ofIM` need a period `≠ 0`: vacuous). Three branches, each the non-stable proof with the
  stable post: `PPCov` (XTopJointMRPath2's `mcsPPJZMF`, its `PPCov` arm), `PPCovI` (XTopJointPreemptI's
  `mcsPPJI`), neither (XTopJointPreemptM's `mcsPPJU`).

No premise; no sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JDelMT
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

theorem msF_mrC {A : Type} {arI : machine.Arch A} {MR : A → Fl4Spec.MachineState → Prop} (hM : MachPlatC arI MR)
    {a : A} {σ σ' : Fl4Spec.State Unit} (hR : MR a σ.machineState) (h : MachF.msF σ' = MachF.msF σ) :
    MR a σ'.machineState := by
  simp only [MachF.msF, Prod.mk.injEq] at h
  exact hM.frame a _ _ hR h.1 h.2.1 h.2.2.1 h.2.2.2.1

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 45) **XTopJointMRPP's `ppJHM` over `MachPlatC`** (module docstring): every spec `error` outcome of
the preemption point is a `JHole` at the pre-state's sets, with `MR` and `ValidMachineTime`. -/
theorem JAtZ.ppJHC {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatC arI MR) (hPA : PPPlatA arI AR)
    (hR : MR a σ.machineState) (hV : ValidMachineTime σ) :
    sched.preemption_point st arI s a ⦃ r => r.1 = .Err .Preempted → ∀ σ',
      (.error (), σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1 →
      ∃ (s0 : S) (Ac0 : Set U64) (Lst0 : U64 → List U64),
        JHole (L := L) arI AR Z H Cs Ac0 Lst0 D s0 a σ r.2.1 r.2.2 σ' ∧
        MR r.2.2 σ'.machineState ∧ ValidMachineTime σ' ⦄ := by
  unfold sched.preemption_point
  step with obj.ks_get.spec as ⟨i, _⟩
  step as ⟨w, _⟩
  step with obj.ks_set.spec as ⟨s1, e1⟩
  subst e1
  obtain ⟨Ac1, Lst1, J1⟩ := J.workUnitsJD arI w
  split
  swap
  · rw [WP.spec_ok]; intro h; cases h
  step with obj.ks_set.spec as ⟨s2, e2⟩
  subst e2
  obtain ⟨Ac2, Lst2, J2⟩ := J1.workUnitsJD arI 0#u64
  have hS0 := J2.xtop.fin.1.1.1
  have hscC0 := cursc_in hS0 J2.own
  refine WP.spec_bind (WP.spec_and (J2.timestampJH hAK hA hnd (hM.nowAgree hR hV)) (update_timestamp_mrC hM hR _)) ?_
  rintro ⟨s3, a1⟩ ⟨⟨σ1, hE1, hk1, hcs1, hrq1, hct1, har1, hum1, -, hK⟩, hR1⟩
  have hσ1m := the_result (Sched.updateTimeStamp_eq' hnd (doMachineOp_single (getCurrentTime_eq σ.machineState))) hE1
  have hR1' : MR a1 σ1.machineState := by rw [hσ1m]; exact hR1
  have hV1 : ValidMachineTime σ1 := by rw [hσ1m]; exact validMachineTime_gct σ
  have hX1 := (hK σ1.machineState a1 hum1 id).xtop
  have hAR1 : AR a1 σ.archState.x64CurrentCr3 := by
    have h := hX1.fin.1.1.2.2.2.2.2.2
    rw [show ({ σ1 with machineState := σ1.machineState } : Fl4Spec.State Unit).archState = σ.archState from har1] at h
    exact h
  obtain ⟨⟨b2, a2⟩, hip, ⟨irq, ms, hIq, hiff, hum, hR2, hlm⟩, hAR2⟩ :=
    spec_exists (WP.spec_and (hM.irqAtE hR1') (hPA.irqAR a1 _ hAR1))
  have hum' : ms.underlyingMemory = σ.machineState.underlyingMemory := hum.trans hum1
  have hV2 : ValidMachineTime { σ1 with machineState := ms } := by
    show σ1.curTime ≤ ms.lastMachineTime ∧ Fl4Spec.unat ms.lastMachineTime ≤ timeCap
    rw [hlm]; exact hV1
  set σ2 : Fl4Spec.State Unit := { σ1 with machineState := ms } with hσ2
  have hX2 := (hK ms a1 hum' id).xtop
  have hS2 := hX2.fin.1.1.1
  obtain ⟨Q, R0, hc, hs⟩ := hS2.lists
  obtain ⟨Q0, R00, hc0, hs0⟩ := hS0.lists
  have hfin : ∀ σ', (.error (), σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1 → σ' = σ2 :=
    fun σ' h => pp_err_eq hE1 hIq _ h rfl
  -- FL4's IRQ read (first, in C's and the spec's order)
  refine WP.spec_bind (Pₘ := fun q => q = (b2, a2)) (by rw [hip, WP.spec_ok]) ?_
  rintro ⟨b2', a2'⟩ he
  cases he
  try dsimp only
  -- FL4's reads
  step with sched.cur_sc.spec' as ⟨sc, hsc⟩
  step with sched.consumed.spec' as ⟨cv, hcv⟩
  step with sporadic.sc_active.spec' as ⟨b, hb⟩
  rw [hc.cur] at hsc hcv
  subst hsc hcv
  have hscC : nodeW st s3 Z.c layout.node.CUR_SC ∈ Z.C := by
    have e : (nodeW st s3 Z.c layout.node.CUR_SC).bv =
        (nodeW st (L.wr (L.wr s (core.num.U64.wrapping_add (L.ksb s) layout.ks.WORK_UNITS) w)
          (core.num.U64.wrapping_add
            (L.ksb (L.wr s (core.num.U64.wrapping_add (L.ksb s) layout.ks.WORK_UNITS) w))
            layout.ks.WORK_UNITS) 0#u64) Z.c layout.node.CUR_SC).bv := by
      rw [← hs.curSc, ← hs0.curSc]; exact hcs1
    rw [P1.eq_of_bv e]; exact hscC0
  obtain ⟨x, n, hkx, hx⟩ := hs.scs _ hscC
  have hkx' : σ2.kheap σ2.curSc = some (.schedContext x n) := by rw [hs.curSc]; exact hkx
  have hab : b = Fl4Spec.scActive x := by
    rw [hb]; show _ = decide (0 < x.scRefillMax); apply decide_eq_decide.2; rw [← hx.max]; rfl
  subst hab
  rw [is_cur_domain_expired_eq]
  -- every preempted outcome ends at `(s3, a2)`, the spec's at `σ2`
  have hErr : (ok ((core.result.Result.Err error.Exc.Preempted : core.result.Result Unit error.Exc), s3, a2) :
      Result ((core.result.Result Unit error.Exc) × S × A)) ⦃ r =>
      r.1 = .Err .Preempted → ∀ σ', (.error (), σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1 →
      ∃ (s0 : S) (Ac0 : Set U64) (Lst0 : U64 → List U64),
        JHole (L := L) arI AR Z H Cs Ac0 Lst0 D s0 a σ r.2.1 r.2.2 σ' ∧
        MR r.2.2 σ'.machineState ∧ ValidMachineTime σ' ⦄ := by
    rw [WP.spec_ok]
    intro _ σ' hσ'
    rw [hfin σ' hσ']
    exact ⟨_, Ac2, Lst2, hK _ a2 hum' (fun _ => hAR2), hR2, hV2⟩
  have hOk : (ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s3, a2) :
      Result ((core.result.Result Unit error.Exc) × S × A)) ⦃ r =>
      r.1 = .Err .Preempted → ∀ σ', (.error (), σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1 →
      ∃ (s0 : S) (Ac0 : Set U64) (Lst0 : U64 → List U64),
        JHole (L := L) arI AR Z H Cs Ac0 Lst0 D s0 a σ r.2.1 r.2.2 σ' ∧
        MR r.2.2 σ'.machineState ∧ ValidMachineTime σ' ⦄ := by
    rw [WP.spec_ok]; intro h; cases h
  cases hact : Fl4Spec.scActive x
  · simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, ite_self]
    exact hErr
  simp only [↓reduceIte]
  refine WP.spec_bind (sufficient_refines s3 a2 σ2 hS2 hscC hkx hact _ (hPA.minBudget a2)) ?_
  intro ok1 _
  simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
  split
  · exact hErr
  split
  · exact hOk
  · exact hErr

set_option maxHeartbeats 4000000 in
/-- (p3J gen 45) **The hole after a preempting preemption point from a fixed `JAtZ`** (module docstring;
XTopJointMRHole's `jAtPreMV_holeQ` with the pre-state's sets kept). -/
theorem JAtZ.preHoleC {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0) (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatC arI MR) (hPA : PPPlatA arI AR)
    (hns0 : Vs.NoSwitch σ0) (hp00 : PPR0 σ0) (hR0 : MR a0 σ0.machineState) (hV0 : ValidMachineTime σ0)
    (hI0 : ValidIrqMasks σ0)
    (hpp : sched.preemption_point st arI s0 a0 = ok (.Err .Preempted, s, a))
    (hσ : (.error (), σ) ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ0).1) :
    ∃ (s1 : S) (Ac1 : Set U64) (Lst1 : U64 → List U64),
      JHole (L := L) arI AR Z H Cs Ac1 Lst1 D s1 a0 σ0 s a σ ∧ TShift σ0 σ ∧
      σ.curThread ≠ σ.idleThread ∧ Vs.NoSwitch σ ∧ CurScFree σ ∧ CtOK σ ∧ Chg σ ∧ CtNQ σ ∧
      MR a σ.machineState ∧ ValidMachineTime σ ∧ ValidIrqMasks σ := by
  have h := J.ppJHC hAK hA hnd hM hPA hR0 hV0
  rw [hpp, WP.spec_ok] at h
  obtain ⟨s1, Ac1, Lst1, Hh, hR', hV'⟩ := h rfl σ hσ
  have hE := Sched.updateTimeStamp_eq' hnd (doMachineOp_single (getCurrentTime_eq σ0.machineState))
  have e : σ = _ := pp_err_eq hE (doMachineOp_single (getActiveIRQ_eq true _)) _ hσ rfl
  subst e
  have h0 : CurScFree σ0 := curScFree_of J.inv J.own hp00
  exact ⟨s1, Ac1, Lst1, Hh, ⟨vmt_le_gct hV0, rfl⟩, hp00.1.1, hns0, fun u xt hu hs => h0 u xt hu hs, hp00.1.2.2.1,
    hp00.1.2.2.2.1, hp00.1.2.2.2.2, hR', hV', fun i hi => hI0 i hi⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 45) **XTopJointMRPath2's `mcsPPJZMF`, `PPCov` arm, at the hole's sets.** -/
theorem JHole.mcsCovSt [VxE Z] {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hT : TShift σ0 σ) (hAT : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1)
    (hmrt : sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hcov : PPCov σ) :
    syscall.mcs_preemption_point st arI s a ⦃ r => ∃ σ',
      (∀ y, y ∈ (Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').1 → y ∈ (Fl4Spec.preemptionPath (Z := Unit) σ).1) ∧
      ((Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').2 → (Fl4Spec.preemptionPath (Z := Unit) σ).2) ∧
      JStab (L := L) arI AR Z H Cs r.1 r.2 σ' ∧ MachF.msF σ' = MachF.msF σ ∧ (NativeScope σ → NativeScope σ') ∧
      (SInvCk.CKI σ → SInvCk.CKI σ') ⦄ := by
  obtain ⟨hC, hni, hnsw, hnt⟩ := hcov
  have hS := Hh.xtop.fin.1.1.1
  have hR := Hh.xtop.fin.1.1.2.2.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨hscC, -, -, -, hact, -, -⟩ := CurInv.facts hS Hh.inv hC
  have hid := curSc_ne_idleSc_of Hh.inv Hh.act hC hni
  unfold syscall.mcs_preemption_point
  step with sched.cur_thread.spec' as ⟨ct, hct⟩
  step with Sched.sched.is_schedulable.spec' as ⟨b, hb⟩
  rw [hc.cur] at hct
  subst hct
  rw [schedulable_eq hR hS hc.curT] at hb
  have ect : σ.curThread = (nodeW st s Z.c layout.node.CUR_THREAD).bv := hs.curThread
  subst hb
  cases hsch : Fl4Spec.schedulable (nodeW st s Z.c layout.node.CUR_THREAD).bv σ
  · simp only [Bool.false_eq_true, ↓reduceIte]
    step with sched.cur_sc.spec' as ⟨sc, hsc⟩
    step with sporadic.sc_active.spec' as ⟨b1, hb1⟩
    rw [hc.cur] at hsc
    subst hsc
    obtain ⟨x, n, hkx, hx⟩ := hs.scs _ hscC
    have hab : b1 = Fl4Spec.scActive x := by
      rw [hb1]; show _ = decide (0 < x.scRefillMax); apply decide_eq_decide.2; rw [← hx.max]; rfl
    have hax : Fl4Spec.scActive x = true := hact (by rw [← hs.curSc]; exact hid) x n hkx
    rw [hab, hax]
    simp only [↓reduceIte]
    step with sched.consumed.spec' as ⟨cv, hcv⟩
    rw [hc.cur] at hcv
    subst hcv
    refine WP.spec_mono (Hh.chargeBudgetJ hAT hC hni hnsw hmrt hmb _) ?_
    rintro ⟨s', a'⟩ ⟨ha, σ', h1, -, Lst', J'⟩
    simp only at ha
    subst a'
    have hkx' : σ.kheap σ.curSc = some (.schedContext x n) := by rw [hs.curSc]; exact hkx
    have hga : Fl4Spec.getScActive (Z := Unit) σ.curSc σ = ({(true, σ)}, False) := by
      unfold Fl4Spec.getScActive Fl4Spec.NonDet.getsThe; rw [readScActive_eq' hkx', hax]; rfl
    have h1' : Fl4Spec.chargeBudget (Z := Unit) σ.consumedTime false σ = ({((), σ')}, False) := by
      rw [hs.consumed]; exact h1
    have hs' : Fl4Spec.schedulable σ.curThread σ = false := by rw [ect]; exact hsch
    refine ⟨σ', ?_, ?_, J'.stab, MachF.mfk_chargeBudget _ _ σ ((), σ') (by rw [h1']; rfl),
        fun hN => SInv.ns_chargeBudget _ _ σ hN ((), σ') (by rw [h1']; rfl),
        fun hC0 => SInvCk.ck_chargeBudget _ _ σ hC0 ((), σ') (by rw [h1']; rfl)⟩
    · exact fun y hy => mem_pp_charge hs' hga (by rw [h1']; rfl) hy
    · exact fun hy => fail_pp_charge hs' hga (by rw [h1']; rfl) hy
  · simp only [↓reduceIte]
    have hs' : Fl4Spec.schedulable σ.curThread σ = true := by rw [ect]; exact hsch
    have hFT : sched.check_budget st arI s a ⦃ res => res.1 = false → ∃ σ',
        (∀ y, y ∈ (Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').1 →
          y ∈ (Fl4Spec.preemptionPath (Z := Unit) σ).1) ∧
        ((Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').2 → (Fl4Spec.preemptionPath (Z := Unit) σ).2) ∧
        JStab (L := L) arI AR Z H Cs res.2.1 res.2.2 σ' ∧ MachF.msF σ' = MachF.msF σ ∧ (NativeScope σ → NativeScope σ') ∧
      (SInvCk.CKI σ → SInvCk.CKI σ') ⦄ := by
      refine WP.spec_mono (Hh.checkBudgetF hAT hC hni hnsw hmrt hmb hnt) ?_
      rintro ⟨r, s', a'⟩ hF hr
      obtain ⟨ha, σ', h1, -, Lst', J'⟩ := hF hr
      simp only at ha
      subst a'
      exact ⟨σ', fun y hy => mem_pp_sched hs' (by rw [h1]; rfl) hy,
        fun hy => fail_pp_sched hs' (by rw [h1]; rfl) hy, J'.stab,
        MachF.mfk_checkBudget σ (_, σ') (by rw [h1]; rfl),
        fun hN => SInv.ns_checkBudget σ hN (_, σ') (by rw [h1]; rfl),
        fun hC0 => SInvCk.ck_checkBudget σ hC0 (_, σ') (by rw [h1]; rfl)⟩
    refine WP.spec_bind (WP.spec_and (check_budgetT hAT s a σ hS hscC hact hmb) hFT) ?_
    rintro ⟨r, s', a'⟩ ⟨hT', hF⟩
    refine (WP.spec_ok _).2 ?_
    cases r
    · exact hF rfl
    · obtain ⟨e, hsuf, hsufH⟩ := hT' rfl
      simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      have hO := Hh.offOK_suff hT hC hni hs' hsufH
      obtain ⟨Lst', J'⟩ := Hh.toJ hO (Or.inl (curOwn_of_curInv hS Hh.inv hC))
      exact ⟨σ, fun y hy => mem_pp_sched hs' (by rw [checkBudget_suff hnd hsuf]; rfl) hy,
        fun hy => fail_pp_sched hs' (by rw [checkBudget_suff hnd hsuf]; rfl) hy, J'.stab, rfl, fun hN => hN, fun hC0 => hC0⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 45) **XTopJointPreemptI's `mcsPPJI` at the hole's sets** (inactive current SC). -/
theorem JHole.mcsInactSt {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) [VxE Z] (hcov : PPCovI σ) :
    syscall.mcs_preemption_point st arI s a ⦃ r => ∃ σ',
      (∀ y, y ∈ (Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').1 → y ∈ (Fl4Spec.preemptionPath (Z := Unit) σ).1) ∧
      ((Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').2 → (Fl4Spec.preemptionPath (Z := Unit) σ).2) ∧
      JStab (L := L) arI AR Z H Cs r.1 r.2 σ' ∧ MachF.msF σ' = MachF.msF σ ∧ (NativeScope σ → NativeScope σ') ∧
      (SInvCk.CKI σ → SInvCk.CKI σ') ⦄ := by
  obtain ⟨hsch, hin⟩ := hcov
  have J := Hh.j0
  have hS := Hh.xtop.fin.1.1.1
  have hR := Hh.xtop.fin.1.1.2.2.1
  have hS0 := J.xtop.fin.1.1.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨Q0, R00, hc0, hs0⟩ := hS0.lists
  obtain ⟨-, -, -, -, hk, hct, -, -, -, hrq, -, -⟩ := Hh.sfacts
  obtain ⟨ms, t, c, hum, e⟩ := Hh.spec
  have hcs : σ.curSc = σ0.curSc := by rw [e]
  have hks : L.ksb s = L.ksb s0 := Hh.ws.1
  have hcpu : L.cpu s = L.cpu s0 := Hh.ws.2.1
  -- the current SC is one of `Z.C` (the base's `CurOwnW`)
  have hscC : nodeW st s Z.c layout.node.CUR_SC ∈ Z.C := by
    have e1 : (nodeW st s Z.c layout.node.CUR_SC).bv = (nodeW st s0 Z.c layout.node.CUR_SC).bv := by
      rw [← hs.curSc, ← hs0.curSc]; exact hcs
    rw [P1.eq_of_bv e1]; exact cursc_in hS0 J.own
  unfold syscall.mcs_preemption_point
  step with sched.cur_thread.spec' as ⟨ct, hct'⟩
  step with Sched.sched.is_schedulable.spec' as ⟨b, hb⟩
  rw [hc.cur] at hct'
  subst hct'
  rw [schedulable_eq hR hS hc.curT] at hb
  have ect : σ.curThread = (nodeW st s Z.c layout.node.CUR_THREAD).bv := hs.curThread
  subst hb
  rw [← ect, hsch]
  simp only [Bool.false_eq_true, ↓reduceIte]
  step with sched.cur_sc.spec' as ⟨sc, hsc⟩
  step with sporadic.sc_active.spec' as ⟨b1, hb1⟩
  rw [hc.cur] at hsc
  subst hsc
  obtain ⟨x, n, hkx, hx⟩ := hs.scs _ hscC
  have hab : b1 = Fl4Spec.scActive x := by
    rw [hb1]; show _ = decide (0 < x.scRefillMax); apply decide_eq_decide.2; rw [← hx.max]; rfl
  have hkx' : σ.kheap σ.curSc = some (.schedContext x n) := by rw [hs.curSc]; exact hkx
  have hax : Fl4Spec.scActive x = false := hin x n hkx'
  rw [hab, hax]
  simp only [Bool.false_eq_true, ↓reduceIte]
  step with P1.LawfulStore.cur_cpu_spec as ⟨cc, ecc⟩
  step with P1.obj.node_set.spec as ⟨s2, es2⟩
  subst es2 ecc
  rw [hc.cur]
  have hga : Fl4Spec.getScActive (Z := Unit) σ.curSc σ = ({(false, σ)}, False) := by
    unfold Fl4Spec.getScActive Fl4Spec.NonDet.getsThe; rw [readScActive_eq' hkx', hax]; rfl
  have hs' : Fl4Spec.schedulable σ.curThread σ = false := hsch
  -- FL4's write and the relations
  obtain ⟨hS2, hF2, -⟩ := hS.set_node_consumed 0#u64
  have e0 : U64.bv 0#u64 = (0 : BitVec 64) := by first | rfl | decide | simp
  rw [e0] at hS2
  have hS2' : SchedRel st Z.N Z.T Z.C Z.c (L.wr s (L.nodeAt s Z.c layout.node.CONSUMED) 0#u64) (cons0 σ) := hS2
  have hR2 : NtfnStateRel Z.N Z.T (L.mem (L.wr s (L.nodeAt s Z.c layout.node.CONSUMED) 0#u64)) (cons0 σ) :=
    hR.frame hS.placed hF2 (KView.refl σ)
  have hcC : Z.c ∈ Cs := hc0.cur ▸ J.kern.cpuCs
  have hN0 : P1.NodePlaced st Z.T s0 Z.c := by
    rw [J.tcbs_eq.1]; exact P1.TInv.nodes J.blk Z.c hcC
  have hN : P1.NodePlaced st Z.T s Z.c := by
    rw [J.tcbs_eq.1]; exact P1.TInv.nodes Hh.blk Z.c hcC
  have eA : L.nodeAt s Z.c layout.node.CONSUMED = L.nodeAt s0 Z.c layout.node.CONSUMED :=
    nodeAt_ksb hks _ _
  have hw1 : P1.WritesIn st s (L.wr s (L.nodeAt s Z.c layout.node.CONSUMED) 0#u64)
      (· = L.nodeAt s Z.c layout.node.CONSUMED) :=
    P1.writesIn_wr (P1.nodeAt_aligned hN (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]))
  have hnb : ∀ o : U64, o.val < 4288 → L.nodeBase s0 Z.c ≤ (L.nodeAt s0 Z.c o).val ∧
      (L.nodeAt s0 Z.c o).val < L.nodeBase s0 Z.c + 4288 := fun o ho => by
    rw [P1.nodeAt_val hN0 ho]; omega
  have hwK : P1.WritesIn st s0 (L.wr s (L.nodeAt s Z.c layout.node.CONSUMED) 0#u64) (KFoot st Z.T Z.N Z.C Z.c s0 σ0) :=
    (Hh.ws.trans hw1).mono fun b hb => by
      rcases hb with hb | rfl
      · exact hb
      · rw [eA]; exact Or.inl (Or.inr (hnb _ (by simp [layout.node.CONSUMED])))
  have hwT : P1.WritesIn st s0 (L.wr s (L.nodeAt s Z.c layout.node.CONSUMED) 0#u64) (TFoot st Z.T Z.N Z.C Z.c s0 σ0) := WritesIn.tfoot_of_kfoot hwK
  have eσ' : cons0 σ = { σ0 with machineState := ms, curTime := t, consumedTime := 0 } := by rw [e]
  have hK : ScTKw (fun _ => False) σ0 (cons0 σ) := by
    rw [eσ']; exact ⟨fun p => OTK.refl _ _, hum, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hARh : AR a σ.archState.x64CurrentCr3 := Hh.xtop.fin.1.1.2.2.2.2.2.2
  have earch : σ.archState = σ0.archState := by rw [e]
  have hX2 : XTopAt (L := L) AR Z (L.wr s (L.nodeAt s Z.c layout.node.CONSUMED) 0#u64) a (cons0 σ) :=
    xtop_sc_step J.xtop J.ip J.nk hwT (ct := σ0.curThread) (hK.mono fun _ h => h.elim) hS2' hR2
      fun _ => by rw [← earch]; exact hARh
  -- P1
  obtain ⟨⟨Q1, R1, h1⟩, hB1, hX1, hS1, hSg1⟩ := Hh.blk
  have hbx := P1.consumed0_bxi h1 hB1 hX1 hSg1 hS1
  rw [hc.cur] at hbx
  have hblk' : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac
      (L.wr s (L.nodeAt s Z.c layout.node.CONSUMED) 0#u64) :=
    ⟨hbx.1, hbx.2.1, hbx.2.2.1, hbx.2.2.2.2, hbx.2.2.2.1⟩
  -- the debug word
  have hDbg : L.mem (L.wr s (L.nodeAt s Z.c layout.node.CONSUMED) 0#u64) (L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS) =
      L.mem s0 (L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS) := by
    rw [← Hh.dbg]
    have hN00 : P1.NodePlaced st Z.T s0 0#u64 := by rw [J.tcbs_eq.1]; exact P1.TInv.nodes J.blk _ J.kern.cs0
    have hd := P1.nodeAt_val hN00 (off := layout.node.DEBUG_TCBS) (by simp [layout.node.DEBUG_TCBS])
    have h2 := P1.nodeAt_val hN0 (off := layout.node.CONSUMED) (by simp [layout.node.CONSUMED])
    have hnb' : ∀ c, L.nodeBase s0 c = (L.ksb s0).val + 13568 + c.val * 4288 := fun _ => rfl
    refine hw1.mem_eq J.kern.dwAl fun hb => ?_
    rw [eA] at hb
    rw [hnb'] at hd h2
    have := congrArg UScalar.val hb
    rw [hd, h2] at this; simp [layout.node.DEBUG_TCBS, layout.node.CONSUMED] at this; omega
  have Hh2 : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0
      (L.wr s (L.nodeAt s Z.c layout.node.CONSUMED) 0#u64) a (cons0 σ) :=
    ⟨J, ⟨ms, t, 0, hum, eσ'⟩, hwK, hX2, Hh.nsc, Hh.inv.congr rfl rfl rfl rfl,
      Hh.cur.imp id fun h => h.congr rfl rfl rfl rfl, Hh.act, hblk', hDbg,
        Hh.dbgK_node (by obtain ⟨Q, R0, hc, -⟩ := J.xtop.fin.1.1.1.lists; exact hc.cur ▸ J.kern.cpuCs)
          (Or.inr rfl) hw1⟩
  have hO : OffOK (cons0 σ) := fun h0 => absurd h0 (by show ¬ (0 : BitVec 64) < 0; decide)
  have hOw : CurOwnW Z.T Z.C (cons0 σ) := by
    rcases J.own with ⟨u, hu, xt, hk1, hxs, hb', -⟩ | ⟨⟨c', hc', hcv'⟩, h2⟩
    · refine Or.inl ⟨u, hu, xt, ?_, ?_, fun y m hy => hb' y m ?_,
        fun h0 => absurd h0 (by show ¬ (0 : BitVec 64) < 0; decide)⟩
      · show σ.kheap u.bv = _; rw [hk]; exact hk1
      · show _ = some σ.curSc; rw [hcs]; exact hxs
      · rw [← hk, ← hcs]; exact hy
    · exact Or.inr ⟨⟨c', hc', hcv'.trans hcs.symm⟩, fun y m hy => h2 y m (by rw [← hk, ← hcs]; exact hy)⟩
  obtain ⟨Lst', J'⟩ := Hh2.toJ hO hOw
  exact ⟨cons0 σ, fun y hy => mem_pp_inact hs' hga hy, fun hy => fail_pp_inact hs' hga hy, J'.stab, rfl, fun hN => hN, fun hC0 => hC0⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 45) **XTopJointPreemptM's `mcsPPJU` at the hole's sets** (no `CurInv`, active current SC). -/
theorem JHole.mcsUSt [VxE Z] {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hAT : P0.ArchTotal arI)
    (hmrt : sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hnc : ¬ CurInv σ) (hct : CtOK σ) (hf : CurScFree σ) (hg : Chg σ)
    (hsch : Fl4Spec.schedulable σ.curThread σ = false) (hin : ¬ PPCovI σ) :
    syscall.mcs_preemption_point st arI s a ⦃ r => ∃ σ',
      (∀ y, y ∈ (Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').1 → y ∈ (Fl4Spec.preemptionPath (Z := Unit) σ).1) ∧
      ((Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').2 → (Fl4Spec.preemptionPath (Z := Unit) σ).2) ∧
      JStab (L := L) arI AR Z H Cs r.1 r.2 σ' ∧ MachF.msF σ' = MachF.msF σ ∧ (NativeScope σ → NativeScope σ') ∧
      (SInvCk.CKI σ → SInvCk.CKI σ') ⦄ := by
  have hax : ∀ x n, σ.kheap σ.curSc = some (.schedContext x n) → Fl4Spec.scActive x = true := fun x n h => by
    cases e : Fl4Spec.scActive x with
    | true => rfl
    | false => exact (hin ⟨hsch, fun x' n' h' => by rw [h] at h'; cases h'; exact e⟩).elim
  have hS := Hh.xtop.fin.1.1.1
  have hR := Hh.xtop.fin.1.1.2.2.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hscC := Hh.curSc_in
  unfold syscall.mcs_preemption_point
  step with sched.cur_thread.spec' as ⟨ct, hct'⟩
  step with Sched.sched.is_schedulable.spec' as ⟨b, hb⟩
  rw [hc.cur] at hct'
  subst hct'
  rw [schedulable_eq hR hS hc.curT] at hb
  have ect : σ.curThread = (nodeW st s Z.c layout.node.CUR_THREAD).bv := hs.curThread
  subst hb
  rw [← ect, hsch]
  simp only [Bool.false_eq_true, ↓reduceIte]
  step with sched.cur_sc.spec' as ⟨sc, hsc⟩
  step with sporadic.sc_active.spec' as ⟨b1, hb1⟩
  rw [hc.cur] at hsc
  subst hsc
  obtain ⟨x, n, hkx, hx⟩ := hs.scs _ hscC
  have hab : b1 = Fl4Spec.scActive x := by
    rw [hb1]; show _ = decide (0 < x.scRefillMax); apply decide_eq_decide.2; rw [← hx.max]; rfl
  have hkx' : σ.kheap σ.curSc = some (.schedContext x n) := by rw [hs.curSc]; exact hkx
  have hax' : Fl4Spec.scActive x = true := hax x n hkx'
  rw [hab, hax']
  simp only [↓reduceIte]
  step with sched.consumed.spec' as ⟨cv, hcv⟩
  rw [hc.cur] at hcv
  subst hcv
  refine WP.spec_mono (Hh.chargeBudgetUJ hAT hnc hsch hct hf hg hax hmrt hmb _) ?_
  rintro ⟨s', a'⟩ ⟨ha, σ', h1, -, Lst', J'⟩
  simp only at ha
  subst a'
  have hga : Fl4Spec.getScActive (Z := Unit) σ.curSc σ = ({(true, σ)}, False) := by
    unfold Fl4Spec.getScActive Fl4Spec.NonDet.getsThe; rw [readScActive_eq' hkx', hax']; rfl
  have h1' : Fl4Spec.chargeBudget (Z := Unit) σ.consumedTime false σ = ({((), σ')}, False) := by
    rw [hs.consumed]; exact h1
  exact ⟨σ', fun y hy => mem_pp_charge hsch hga (by rw [h1']; rfl) hy,
    fun hy => fail_pp_charge hsch hga (by rw [h1']; rfl) hy, J'.stab, MachF.mfk_chargeBudget _ _ σ ((), σ') (by rw [h1']; rfl),
    fun hN => SInv.ns_chargeBudget _ _ σ hN ((), σ') (by rw [h1']; rfl),
    fun hC0 => SInvCk.ck_chargeBudget _ _ σ hC0 ((), σ') (by rw [h1']; rfl)⟩

/-- (p3J gen 45) **The MCS preemption point from a round-robin hole, at the hole's sets** (module docstring). -/
theorem JHole.mcsStK [VxE Z] {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hT : TShift σ0 σ) (hAT : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1)
    (hmrt : sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hni : σ.curThread ≠ σ.idleThread) (hns : Vs.NoSwitch σ) (hf : CurScFree σ) (hct : CtOK σ) (hg : Chg σ)
    (hRR : SInvRr.RR σ) :
    syscall.mcs_preemption_point st arI s a ⦃ r => ∃ σ',
      (∀ y, y ∈ (Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').1 → y ∈ (Fl4Spec.preemptionPath (Z := Unit) σ).1) ∧
      ((Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').2 → (Fl4Spec.preemptionPath (Z := Unit) σ).2) ∧
      JStab (L := L) arI AR Z H Cs r.1 r.2 σ' ∧ MachF.msF σ' = MachF.msF σ ∧ (NativeScope σ → NativeScope σ') ∧
      (SInvCk.CKI σ → SInvCk.CKI σ') ⦄ := by
  by_cases hC : CurInv σ
  · exact Hh.mcsCovSt hT hAT hnd hmrt hmb ⟨hC, hni, hns σ.curThread, Or.inr fun x n hk => SInvRr.rr_period hRR hk⟩
  by_cases hi : PPCovI σ
  · exact Hh.mcsInactSt hi
  have hsch : Fl4Spec.schedulable σ.curThread σ = false := by
    cases e : Fl4Spec.schedulable σ.curThread σ with
    | false => rfl
    | true => exact absurd (curInv_of_sched hct e) hC
  exact Hh.mcsUSt hAT hmrt hmb hC hct hf hg hsch hi

/-- (p3J gen 45) **`mcsStK` with `MR` and `ValidIrqMasks` after** (module docstring). -/
theorem JHole.mcsSt [VxE Z] {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hT : TShift σ0 σ) (hAT : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1)
    (hmrt : sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hni : σ.curThread ≠ σ.idleThread) (hns : Vs.NoSwitch σ) (hf : CurScFree σ) (hct : CtOK σ) (hg : Chg σ)
    (hRR : SInvRr.RR σ) (hM : MachPlatC arI MR) (hK : MRKeep arI MR) (hR : MR a σ.machineState)
    (hV : ValidIrqMasks σ) :
    syscall.mcs_preemption_point st arI s a ⦃ r => ∃ σ',
      (∀ y, y ∈ (Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').1 → y ∈ (Fl4Spec.preemptionPath (Z := Unit) σ).1) ∧
      ((Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').2 → (Fl4Spec.preemptionPath (Z := Unit) σ).2) ∧
      JStab (L := L) arI AR Z H Cs r.1 r.2 σ' ∧ MR r.2 σ'.machineState ∧ ValidIrqMasks σ' ∧
      (NativeScope σ → NativeScope σ') ∧ (SInvCk.CKI σ → SInvCk.CKI σ') ⦄ :=
  WP.spec_mono (WP.spec_and (Hh.mcsStK hT hAT hnd hmrt hmb hni hns hf hct hg hRR)
    (MK.syscall_mcs_preemption_point L.total hAT hK hR))
    fun _ ⟨⟨σ', h1, h2, hJ, hF, hNs, hCk⟩, hR'⟩ => ⟨σ', h1, h2, hJ, msF_mrC hM hR' hF, msF_vim hV hF, hNs, hCk⟩

end

end

end Fl4Proofs.P3
