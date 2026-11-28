/-
P3 (line stpost): **the unknown-syscall entry at `J` with the stable-ghost post**.

`jEvRef_sysU` (XTopJointKEntryEv5) ends in `RJM` only (ghosts existential). Every step of its
run keeps the typed heap, the buffer words, the heap `H` and the core set `Cs` of the entry's
`JAtZ`: the FaultIP write (`fip_pre`, at `Z.mv Z.G V0`), `budget_ok` (`budgetOkJ` at `Z`;
`budgetOkF` at `Z`, `budgetOkT` / `budgetOkTR` at `Z.mv Z.G V`), `handle_fault`
(StPostFault's `JAtZ.faultHypJZGSt`) and `finish` (`jat_finishJRN`'s last conjunct). Here:

* `JStab.mv`: `JStab` at `Z.mv G V` is `JStab` at `Z`.
* `JAtZ.budgetOkBSt`: `budgetOkB`'s budget-stop outcome at `JStab Z H Cs`.
* `jat_finishJRNMSt`: `jat_finishJRNM` with `JStab Z H Cs` at the same outcome.
* `JFltHypSt`, `jFltHyp_unkSt`: `JFltHyp` with the post `JStab Z H Cs` (no premise: the
  unknown-syscall instance by `faultHypJZGSt`).
* `jEvRef_fltSt`, `jEvRef_sysUSt`: `jEvRef_flt` / `jEvRef_sysU` (same premises) with
  `JStab Z H Cs` beside `RJM` at the same spec outcome.
-/
import Fl4Proofs.P3.StPostFault
import Fl4Proofs.P3.XTopJointKEntryEv5
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- `JStab` at `Z.mv G V` is `JStab` at `Z` (only `G` and the VSpace sets differ). -/
theorem JStab.mv {G : MdbGhost} {V : XVs} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : JStab (L := L) arI AR (Z.mv G V) H Cs s a σ) : JStab (L := L) arI AR Z H Cs s a σ := by
  obtain ⟨G', V', Ac', Lst', D', J'⟩ := h
  exact ⟨G', V', Ac', Lst', D', J'⟩

/-- `JAtZ` at `Z` is `JStab` at `Z`. -/
theorem JAtZ.stab {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    JStab (L := L) arI AR Z H Cs s a σ :=
  ⟨Z.G, Z.vs, Ac, Lst, D, J⟩

set_option maxHeartbeats 16000000 in
/-- **`budgetOkB`'s budget-stop outcome at stable ghosts** (module docstring; the same case
split, `budgetOkF` at `Z`, `budgetOkT` / `budgetOkTR` at `Z.mv Z.G V`). -/
theorem JAtZ.budgetOkBSt {s : S} {a : A} {σ0 : Fl4Spec.State Unit}
    (J0 : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ0) [VxE Z] (hni0 : Entered σ0) (hBu : KBudgetB arI a σ0)
    (hNS0 : NativeScope σ0) (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.budget_ok st arI s a ⦃ r => r.1 = false → ∃ z ∈ (specBudget σ0).1, z.1 = false ∧
      JStab (L := L) arI AR Z H Cs r.2.1 r.2.2 z.2 ⦄ := by
  have hF : ∀ hnt : NoTmoSend σ0, syscall.budget_ok st arI s a ⦃ r => r.1 = false →
      ∃ z ∈ (specBudget σ0).1, z.1 = false ∧ JStab (L := L) arI AR Z H Cs r.2.1 r.2.2 z.2 ⦄ := fun hnt =>
    WP.spec_mono (J0.budgetOkF hAK hA hnd hBu.now hni0 hBu.cur hmrt hmb hnt) fun r h2 hf => by
      obtain ⟨σ', he, Ac', Lst', D', J'⟩ := h2 hf
      refine ⟨(false, σ'), ?_, rfl, J'.stab⟩
      unfold specBudget
      rw [he]; exact Set.mem_singleton _
  rcases hBu.tmo with hnt | hnq
  · exact hF hnt
  by_cases hnt : NoTmoSend σ0
  · exact hF hnt
  unfold NoTmoSend at hnt
  push_neg at hnt
  obtain ⟨⟨xt, hkt, hep⟩, ⟨y, m, hky, hy⟩⟩ := hnt
  have hper : ∀ x n, σ0.kheap σ0.curSc = some (.schedContext x n) → x.scPeriod ≠ 0 := fun x n h => by
    rw [hky] at h; cases h; exact hy
  obtain ⟨p, bd, rr, hth⟩ : ∃ p bd rr, xt.tcbTimeoutHandler = .endpointCap p bd rr := by
    revert hep; cases xt.tcbTimeoutHandler <;> simp [Fl4Spec.isEpCap]
  have hrr : xt.tcbState = .running ∨ xt.tcbState = .restart := by
    have hrun := J0.curRun.run hni0 xt hkt
    have hvm := hNS0 _ xt hkt
    revert hrun hvm; cases xt.tcbState <;> simp [Fl4Spec.runnable]
  by_cases hkl : ∃ l, σ0.kheap p = some (.endpoint (.recvEP l))
  · exact WP.spec_mono (J0.budgetOkTR hAK hA hnd hBu.now hni0 hBu.cur hmrt hmb hmax htu hnq hkt hrr hth hper hkl)
      fun r h2 hf => by
        obtain ⟨z, hz, hz1, V, Ac', Lst', D', J'⟩ := h2 hf
        exact ⟨z, hz, hz1, Z.G, V, Ac', Lst', D', J'⟩
  · have hcb : ∀ xe, σ0.kheap p = some (.endpoint xe) → Endp.CanBlock false xe := fun xe h => by
      cases xe with
      | idleEP => trivial
      | sendEP q => rfl
      | recvEP q => exact absurd ⟨q, h⟩ hkl
    exact WP.spec_mono (J0.budgetOkT hAK hA hnd hBu.now hni0 hBu.cur hmrt hmb hnq hkt hrr hth hper hcb)
      fun r h2 hf => by
        obtain ⟨z, hz, hz1, V, Ac', Lst', D', J'⟩ := h2 hf
        exact ⟨z, hz, hz1, Z.G, V, Ac', Lst', D', J'⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **`jat_finishJRNM` with the stable ghosts at the same outcome** (`jat_finishJRN`'s last
conjunct, which `jat_finishJRNM` drops). -/
theorem jat_finishJRNMSt {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] (hN : NativeScope σ)
    (hd : σ.domainTime ≠ 0 ∨ NdOK (L := L) s σ)
    (hnd : Fl4Spec.numDomains = 1) (hAT : P0.ArchTotal arI)
    (hVt : ∀ (V1 : XVs) (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit) (Ac1 : Set U64) (Lst1 : U64 → List U64)
      (D1 : Set U64), JAtZR (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 s1 a1 σ1 → ∀ t ∈ Z.T,
        Z.th t = some .tcb ∧ ∀ p asid, capAt (L.mem s1) (slotOf t 1) = ok (.Pml4 p true asid) → asid ≠ 0#u64)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hA : ArchSwF st arI Z.N Z.T Z.C Z.c) (hAN : ArchNdF st Z.N Z.T Z.C Z.c) (hFO : FinRootI arI AR σ)
    (hsni : SniHyp st arI Z.N Z.T Z.C Z.c) (hsend : SendHyp st arI Z.N Z.T Z.C Z.c) (hT : TimeAgree arI)
    (hTail : sched.schedule st arI s a ⦃ r => ∀ (rf : S × A) σ1 σ' (D1 : Set U64), Fires σ σ1 →
      timer.fire st arI s a = ok rf →
      ((∃ (V1 : XVs) (Ac1 : Set U64) (Lst1 : U64 → List U64) (D2 : Set U64),
        JAtZR (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D2 rf.1 rf.2 σ1) ∨
       ∃ (V1 : XVs) (Ac1 : Set U64) (Lst1 : U64 → List U64) (D2 : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D2 rf.1 rf.2 σ1) →
      Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) →
      P1.WritesIn st rf.1 r.1 (KFootN st Z.T Z.N Z.C Z.c rf.1 σ1) →
      SchedRel st Z.N Z.T Z.C Z.c r.1 σ' → Inv σ' → CurInv σ' → ActIdle σ' →
      SchTailHypsR AR Z H D1 r.1 r.2 σ' ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hM : MachPlat arI MR) (hKD : MRKeepD arI MR) (hR : MR a σ.machineState) :
    syscall.finish st arI s a ⦃ r => ∃ σ',
      ((), σ') ∈ ((Fl4Spec.fl4Awaken (Z := Unit) >>= fun _ => Fl4Spec.schedule >>= fun _ => Fl4Spec.activateThread) σ).1 ∧
      RJ (L := L) arI AR r.1 r.2 σ' ∧ MR r.2 σ'.machineState ∧ JStab (L := L) arI AR Z H Cs r.1 r.2 σ' ⦄ := by
  refine WP.spec_mono (WP.spec_and (jat_finishJRN s a σ J hN hd hnd hAT hVt hmb hA hAN hFO hsni hsend hT hTail hmax
    htu) (MKD.syscall_finish L.total hAT hKD hR)) ?_
  rintro r ⟨⟨_, σ', _, _, hmem, hRJ, V', Ac', Lst', D', J'⟩, hMR⟩
  exact ⟨σ', hmem, hRJ, msF_mr hM hMR (congrArg Prod.fst (MachT.mtk_finish hmem)), Z.G, V', Ac', Lst', D', J'⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

variable (arI) in
/-- **`JFltHyp` with the stable-ghost post** (module docstring): FL4's branch `B` from the
budget-checked `JAtZ Z H Cs` ends in `JStab Z H Cs` and `MR` at an outcome of `G`. -/
def JFltHypSt (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (Z : XSets) (H : P1.Heap)
    (Cs : Set U64) (B : S → A → Result (S × A)) (G : Fl4Spec.SMonad Unit Unit) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop :=
  ∀ (σb : Fl4Spec.State Unit) (s1 : S) (a1 : A) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
    (true, σb) ∈ (specBudget σ).1 → syscall.budget_ok st arI s a = ok (true, s1, a1) →
    JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' s1 a1 σb → MR a1 σb.machineState →
    B s1 a1 ⦃ r => ∃ z ∈ (G σb).1, JStab (L := L) arI AR Z H Cs r.1 r.2 z.2 ∧ MR r.2 z.2.machineState ⦄

set_option maxHeartbeats 8000000 in
/-- **`JFltHypSt` of the unknown-syscall fault** (`jFltHyp_unk` by `faultHypJZGSt`). -/
theorem jFltHyp_unkSt (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR)
    (hA : P0.ArchTotal arI) {Z : XSets} [VxE Z] {H : P1.Heap} {Cs : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hX : SInvX σ) (hct : σ.curThread ≠ σ.idleThread) (num : U64) :
    JFltHypSt (L := L) arI AR MR Z H Cs (brK (st := st) (arI := arI) num) (brKS num.val) s a σ := by
  intro σb s1 a1 Ac' Lst' D' hb _ J1 hM1
  obtain ⟨hni1, hnq1, hvfh1, -, -, -⟩ := budget_true_facts hnd hX hct hb
  obtain ⟨ct, hct1, -⟩ := spec_exists (sched.cur_thread.spec' (L := L) s1)
  have hcur : σb.curThread = ct.bv := (J1.curEq hct1).1
  have hf : FaultCorrG (.UnknownSyscall num) (.unknownSyscallException num.bv) := Or.inr (Or.inl ⟨num, rfl, rfl⟩)
  show (do let t ← sched.cur_thread st s1; faults.handle_fault st arI s1 a1 t (.UnknownSyscall num)) ⦃ _ ⦄
  rw [hct1, bind_ok]
  refine WP.spec_mono (WP.spec_and (J1.faultHypJZGSt hA hni1 hct1 hnq1 hvfh1 hf)
    (MKD.faults_handle_fault L.total hA hKD hM1)) ?_
  rintro r ⟨⟨z, hz, -, hJ'⟩, hMr⟩
  refine ⟨z, ?_, hJ', msF_mr hM hMr (MachF.mfk_handleFaultG4 _ _ σb z hz)⟩
  have e1 : (BitVec.ofNat 64 num.val : BitVec 64) = num.bv := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt num.bv.isLt
  have hz' : z ∈ (Fl4Spec.handleFault (Z := Unit) σb.curThread
      (.unknownSyscallException (BitVec.ofNat 64 num.val)) σb).1 := by
    rw [hcur, e1]; exact hz
  exact mem_bind_nd (x := (σb.curThread, σb)) rfl hz'

open Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvF in
set_option maxHeartbeats 16000000 in
/-- **`jEvRef_flt` with the stable ghosts** (module docstring): the same run, `JFltHypSt` for
the fault branch, `JStab Z H Cs` beside `RJM` at the same outcome. -/
theorem jEvRef_fltSt {ev : Fl4Spec.Event} {G : Fl4Spec.SMonad Unit Unit} {B : S → A → Result (S × A)}
    (hev : Fl4Spec.handleEvent (Z := Unit) ev = Fl4Spec.withoutPreemption (do
      Fl4Spec.updateTimeStamp; let restart ← Fl4Spec.checkBudgetRestart; Fl4Spec.NonDet.when restart G))
    (hsc : ∀ c, ev ≠ .syscallEvent c) (hin : ev ≠ .interrupt)
    {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] (hX : SInvX σ) (hct : σ.curThread ≠ σ.idleThread)
    (hR : MR a σ.machineState) (hB : JFltHypSt (L := L) arI AR MR Z H Cs B G s a σ)
    (hFin : ∀ x ∈ ((Fl4Spec.NonDetE.handleE (Fl4Spec.fl4HandleEvent (Z := Unit) true ev)
        (fun _ => Fl4Spec.withoutPreemption Fl4Spec.preemptionPath)).run σ).1,
      ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A),
        KFrontF2 (st := st) arI B s a s' a' → JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR31 (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    (do let (b, s1, a1) ← syscall.budget_ok st arI s a
        let (s2, a2) ← if b then B s1 a1 else ok (s1, a1)
        syscall.finish st arI s2 a2) ⦃ r =>
      ∃ σ', EvOut false ev σ σ' ∧ RJM (L := L) arI AR MR r.1 r.2 σ' ∧ JStab (L := L) arI AR Z H Cs r.1 r.2 σ' ⦄ := by
  have hni := hX.entered hct
  have hS := hX.sb
  have hNS : NativeScope σ := hS.1.1.ns
  have hMK := hKD.toK
  have hC : CurInv σ := J.cur.resolve_left (by rw [hni.2]; intro e; cases e)
  have hBu : KBudgetB arI a σ := ⟨hM.nowAgree hR hS.1.1.vmt, hC, hX.offReady, Or.inr hX.ctQ⟩
  obtain ⟨x0, hx0, ha0⟩ := (SInvAll.SInvB.entryJ hS hct).ctAct
  have hNQ : NQ [σ.curThread] σ := nq_cons ((nq_nil_iff σ).2 ⟨hS.1.1.nq, hS.1.1.epq⟩) fun x hx => by
    rw [hx0] at hx; cases hx; exact ok_of_active ha0
  have hL : IL [σ.curThread] σ := il_consT ((il_nil_iff σ).2 hS.1.1.live) (hS.1.1.live _ x0 hx0 (live_of_active ha0))
  have hFo : ∀ y ∈ ((Fl4Spec.handleEvent (Z := Unit) ev).run σ).1, FpuOwnOK y.2 := fun y hy =>
    fpuOwnOK_of_ft (fo_handleEvent_other σ.curThread ev hsc hin σ ⟨⟨⟨hL, nq_weak_nil _ hNQ⟩, hS.1.1.ft⟩, rfl⟩ y hy).2
  have fin : ∀ (s2 : S) (a2 : A) (y : Fl4Spec.State Unit),
      ((.ok (), y) : Except Unit Unit × Fl4Spec.State Unit) ∈ ((Fl4Spec.handleEvent (Z := Unit) ev).run σ).1 →
      KFrontF2 (st := st) arI B s a s2 a2 → JStab (L := L) arI AR Z H Cs s2 a2 y → MR a2 y.machineState →
      syscall.finish st arI s2 a2 ⦃ r => ∃ σ', EvOut false ev σ σ' ∧ RJM (L := L) arI AR MR r.1 r.2 σ' ∧
        JStab (L := L) arI AR Z H Cs r.1 r.2 σ' ⦄ := by
    rintro s2 a2 y hE hfr ⟨G', V', Ac', Lst', D', J'⟩ hMy
    have hE' : ((.ok (), y) : Except Unit Unit × Fl4Spec.State Unit) ∈
        ((Fl4Spec.fl4HandleEvent (Z := Unit) true ev).run σ).1 := by
      rw [Fl4Spec.fl4HandleEvent_other true ev hsc]; exact hE
    have hx := mem_handleE_ok (h := fun _ => Fl4Spec.withoutPreemption (Z := Unit) Fl4Spec.preemptionPath) hE'
    have F := ((hFin _ hx (Z.mv G' V') H Cs Ac' Lst' D' s2 a2 hfr J'.toR).to27).toR (hFo _ hE)
    exact WP.spec_mono (jat_finishJRNMSt s2 a2 y J'.toR (ns_handleEvent ev σ hNS _ hE) F.hd hnd hA F.vt hmb F.arch
      F.archNd F.fo F.sni F.send hT F.tail hmax htu hM hKD hMy)
      fun r ⟨σ', hmem, hRJ, hM', hSt⟩ => ⟨σ', mem_kcall hx hmem, ⟨hRJ, hM'⟩, hSt.mv⟩
  refine WP.spec_bind (spec_and_eq (WP.spec_and (WP.spec_and (J.budgetOkB hni hBu hNS hARI.toARKeep hA hnd hmrt hmb
    hmax htu) (J.budgetOkBSt hni hBu hNS hARI.toARKeep hA hnd hmrt hmb hmax htu))
    (budget_ok_mr hM hMK hA hR s)) fun _ h => h) ?_
  rintro ⟨b, s1, a1⟩ ⟨⟨⟨⟨hTr, -⟩, hFa⟩, hM1⟩, heq⟩
  cases b with
  | false =>
    obtain ⟨⟨b', σb⟩, hz, hz1, hJ'⟩ := hFa rfl
    simp only at hz1; subst hz1
    have hMb := (budget_mr_at hM hnd hz hM1 hS.1.1.vim).1
    have hE : ((.ok (), σb) : Except Unit Unit × Fl4Spec.State Unit) ∈ ((Fl4Spec.handleEvent (Z := Unit) ev).run σ).1 := by
      rw [hev]
      obtain ⟨u, hu, hc⟩ := mem_bind_elim hz
      exact mem_liftE (x := ((), σb)) (mem_bind_nd hu (mem_bind_nd hc (mem_when_false (by simp) _ σb)))
    have hfr : KFrontF2 (st := st) arI B s a s1 a1 := by
      unfold KFrontF2; rw [heq, bind_ok]; rfl
    show (do let (s2, a2) ← (if false = true then B s1 a1 else ok (s1, a1)); syscall.finish st arI s2 a2) ⦃ _ ⦄
    rw [if_neg (by decide)]
    simp only [bind_ok]
    exact fin s1 a1 σb hE hfr hJ' hMb
  | true =>
    obtain ⟨σb, he, -, -, -, -, -, -, -, Ac', Lst', D', J'⟩ := hTr rfl
    have hb : (true, σb) ∈ (specBudget σ).1 := by unfold specBudget; rw [he]; exact Set.mem_singleton _
    have hMb := (budget_mr_at hM hnd hb hM1 hS.1.1.vim).1
    show (do let (s2, a2) ← (if true = true then B s1 a1 else ok (s1, a1)); syscall.finish st arI s2 a2) ⦃ _ ⦄
    rw [if_pos rfl]
    refine WP.spec_bind (spec_and_eq (hB σb s1 a1 Ac' Lst' D' hb heq J' hMb) fun _ h => h) ?_
    rintro ⟨s2, a2⟩ ⟨⟨z', hz', hJ', hM2⟩, heq2⟩
    have hE : ((.ok (), z'.2) : Except Unit Unit × Fl4Spec.State Unit) ∈
        ((Fl4Spec.handleEvent (Z := Unit) ev).run σ).1 := by
      rw [hev]
      obtain ⟨u, hu, hc⟩ := mem_bind_elim hb
      refine mem_liftE (x := z') (mem_bind_nd hu (mem_bind_nd hc ?_))
      show z' ∈ (Fl4Spec.NonDet.when (true = true) G σb).1
      unfold Fl4Spec.NonDet.when; rw [if_pos rfl]; exact hz'
    have hfr : KFrontF2 (st := st) arI B s a s2 a2 := by
      unfold KFrontF2; rw [heq]; simp only [bind_ok, ↓reduceIte]; exact heq2
    exact fin s2 a2 z'.2 hE hfr hJ' hM2

open Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvF in
set_option maxHeartbeats 16000000 in
/-- **`jEvRef_sysU` with the stable ghosts** (module docstring; same premises). -/
theorem jEvRef_sysUSt (hnd : Fl4Spec.numDomains = 1) {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} (n : I64)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] (hX : SInvX σ) (hct0 : σ.curThread ≠ σ.idleThread)
    (hR : MR a σ.machineState)
    (hU : UnkSys (L := L) n s) (hD : NoDbgSys (L := L) arI n s a)
    (hSX : P1.StoreExt st) (hFF : P1.FastFaultOK (L := L) arI s a n)
    (hFin : ∀ ev, KEvSpec (.sysU n) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      KFinEv (L := L) arI AR ev (KFrontSysU (st := st) arI n s a) w.2)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.handle_syscall st arI s a n ⦃ r => ∃ ev σ', KEvSpec (.sysU n) true ev ∧ EvOut true ev σ σ' ∧
      RJM (L := L) arI AR MR r.1 r.2 σ' ∧ JStab (L := L) arI AR Z H Cs r.1 r.2 σ' ⦄ := by
  rw [handle_syscall_unk_eq hA hSX hFF hU]
  have hct := cur_thread_eq (L := L) s
  generalize L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) = ct at hct
  obtain ⟨x, hk', hcur, V0, J0⟩ := fip_pre J hct
  generalize hs0 : L.wr s (regA ct layout.reg.FAULT_IP)
    (core.num.U64.wrapping_sub (L.mem s (regA ct layout.reg.NEXT_IP)) 2#u64) = s0 at J0
  have hF : ((), faultIPSt σ σ.curThread x) ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1 := by
    rw [fl4SyscallFaultIP_eq hk']; exact Set.mem_singleton _
  have hX0 : SInvX (faultIPSt σ σ.curThread x) := sinvX_fip hX _ hF
  have hct1 : (faultIPSt σ σ.curThread x).curThread ≠ (faultIPSt σ σ.curThread x).idleThread := hct0
  have hR0 : MR a (faultIPSt σ σ.curThread x).machineState := hR
  have hFin0 := fun ev hev => hFin ev hev _ hF
  -- the current thread after the FaultIP write
  have hct0' : sched.cur_thread st s0 = ok ct := by
    have h0 := cur_thread_eq (L := L) s0
    generalize L.mem s0 (L.nodeAt s0 (L.cpu s0) layout.node.CUR_THREAD) = ct' at h0
    have e0 : (faultIPSt σ σ.curThread x).curThread = ct'.bv := (J0.curEq h0).1
    have e1 : ct' = ct := UScalar.eq_of_val_eq (by
      show ct'.bv.toNat = ct.bv.toNat
      rw [← e0, ← hcur]; rfl)
    rw [h0, e1]
  -- the general path's fault branch at the FaultIP state
  have hUSF : syscall.unknown_syscall_fault st arI s0 a (IScalar.hcast .U64 n) false ⦃ r =>
      ∃ ev σ', KEvSpec (.sysU n) true ev ∧ EvOut true ev σ σ' ∧
        RJM (L := L) arI AR MR r.2.1 r.2.2 σ' ∧
        JStab (L := L) arI AR Z H Cs r.2.1 r.2.2 σ' ⦄ := by
    have hE := jEvRef_fltSt (ev := .unknownSyscall (IScalar.hcast .U64 n).val)
      (G := brKS (IScalar.hcast .U64 n).val) (B := brK (st := st) (arI := arI) (IScalar.hcast .U64 n))
      rfl (fun _ h => by cases h) (fun h => by cases h) J0 hX0 hct1 hR0
      (jFltHyp_unkSt hnd hM hKD hA hX0 hct1 (IScalar.hcast .U64 n))
      (fun x hx Z' H' Cs' Ac' Lst' D' s' a' hfr J' => hFin0 _ (KEvSpec.sysU n _) x hx Z' H' Cs' Ac' Lst' D' s' a'
        ⟨ct, _, hct, by rw [hs0]; exact hfr⟩ J')
      hARI hA hnd hM hKD hmrt hmb hT hmax htu
    refine WP.spec_mono (usf_spec s0 a (IScalar.hcast .U64 n) hE) ?_
    rintro r ⟨σ', hO, hRJ, hSt⟩
    exact ⟨_, σ', KEvSpec.sysU n _, ⟨((), faultIPSt σ σ.curThread x), hF, hO⟩, hRJ, hSt.mv⟩
  suffices hG : syscall.syscall st arI s a n false ⦃ r => ∃ ev σ', KEvSpec (.sysU n) true ev ∧
      EvOut true ev σ σ' ∧ RJM (L := L) arI AR MR r.2.1 r.2.2 σ' ∧
        JStab (L := L) arI AR Z H Cs r.2.1 r.2.2 σ' ⦄ by
    unfold syscall.handle_syscall_general
    refine WP.spec_bind hG ?_
    rintro ⟨b, s', a'⟩ h
    first
      | exact (WP.spec_ok _).2 h
      | (simp only [uncurry_apply_pair, WP.spec_ok]; exact h)
  unfold syscall.syscall
  rw [hct, bind_ok]
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s ct layout.reg.NEXT_IP) ?_
  rintro nx rfl
  simp only [lift, bind_ok]
  refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s ct layout.reg.FAULT_IP _) ?_
  rintro s1 rfl
  rw [hs0]
  obtain ⟨fl, hfl, -⟩ := spec_exists (Fl4Proofs.P0.obj.Tcb.flags.p0 st ct s0 L.total)
  rw [hfl, bind_ok]
  try simp only [lift, bind_ok]
  by_cases htr : (fl &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true
  · rw [if_pos htr]
    try simp only [lift, bind_ok]
    exact hUSF
  rw [if_neg htr]
  have hrange : n < fl4_abi.syscall.SYSCALL_MIN ∨ n > fl4_abi.syscall.SYSCALL_MAX := by
    rcases hU with hu | hu | hu
    · exact Or.inl hu
    · exact Or.inr hu
    · exfalso
      have h0 := hu ct (core.num.U64.wrapping_sub (L.mem s (regA ct layout.reg.NEXT_IP)) 2#u64) hct
      rw [hs0, hfl, WP.spec_ok] at h0
      exact h0 (by by_contra hne; exact htr (bne_iff_ne.2 hne))
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, dv⟩ := hD
  have hv : n = fl4_abi.syscall.SysVMEnter → arI.virtualization a = ok 0#u64 ∨
      ∀ t, sched.cur_thread st s0 = ok t → vcpu.bound st s0 t = ok 0#u64 := fun hn => by
    rcases dv hn with h0 | h0
    · exact Or.inl h0
    · refine Or.inr fun t ht => ?_
      have e : t = ct := by
        have h1 : sched.cur_thread st s0 ⦃ v => v = ct ⦄ := by rw [hct0']; exact (WP.spec_ok _).2 rfl
        rw [ht, WP.spec_ok] at h1; exact h1
      subst e
      rw [← hs0]; exact h0 t _ hct
  have hH := handle_unknown_syscall_nd arI hA s0 a n false d1 d2 d3 d4 d5 d6 d7 d8 d9 hv
  by_cases hlt : n < fl4_abi.syscall.SYSCALL_MIN
  · rw [if_pos hlt, hH]; exact hUSF
  · rw [if_neg hlt, if_pos (hrange.resolve_left hlt), hH]; exact hUSF

end

end

end Fl4Proofs.P3
