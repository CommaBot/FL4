/-
P3 (p3J gen 19): **the user-exception, VM-fault and unknown-syscall entries at given ghosts, stable, on U41's finish
record** (stage A; stages Q / K in P3JStEvQ / P3JStEvK, as P3JStIrq for the interrupt).

* `jFltHyp_userSt`: XTopJointKEntryEv3's `jFltHyp_user` with the post `JStab Z H Cs` (StPostEv's `JFltHypSt`; the
  fault by StPostFault's `JAtZ.faultHypJZGSt`, as StPostVmTop's `jFltHyp_vmfSt`).
* **`user_entryStU41`** / **`vmf_entryStU41`**: from `JReachU17` and a given `JAtZ Z H Cs` (with `VxE Z`), under
  the clause's case conditions (non-idle, `UserHw` / `VmfHw` [P]) and `hFin : KFinEv41` (+ `FpuImplDet`), the
  general `handle_user_exception` / `handle_vm_fault` ends at an `EvOut false …` outcome that is `JReachU17` **and**
  `JStab Z H Cs`. StPostEv's `jEvRef_fltSt` with `jFltHyp_userSt` / `jFltHyp_vmfSt`; the record down U41 `to13`,
  U13 `to11`, U11 `to8`, U8 `to`, U5 `to` (StPostVmTop's chain); `JReachU17` by `JReachU3.user` / `.vmf`.
  (StPostVmTop's `kernel_entry_vmf_localSt17` is the gated form of the second.)
* **`sysU_entryStU41`**: the same for the unknown syscall (StPostTop's `kernel_entry_sysU_localSt` without the
  local gate): StPostEv's `jEvRef_sysUSt`, `FastFaultOK` by `JAtZ.fastFaultOK`.

Premises: StPostVmTop's / StPostTop's platform facts, the clause conditions and the per-entry `KFinEv41`
(discharged at the top, P3JStEvTop, as U43); no new premise. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JStIrq
import Fl4Proofs.P3.StPostVmTop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 8000000 in
/-- (p3J gen 19) **`JFltHypSt` of the user-exception entry** (`jFltHyp_user` by `faultHypJZGSt`). -/
theorem jFltHyp_userSt (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR)
    (hA : P0.ArchTotal arI) {Z : XSets} [VxE Z] {H : P1.Heap} {Cs : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hX : SInvX σ) (hct : σ.curThread ≠ σ.idleThread) (n c : U64) (hU : UserHw n c) :
    JFltHypSt (L := L) arI AR MR Z H Cs (brU (st := st) arI n c) (brUS n c) s a σ := by
  intro σb s1 a1 Ac' Lst' D' hb _ J1 hM1
  obtain ⟨hni1, hnq1, hvfh1, -, -, -⟩ := budget_true_facts hnd hX hct hb
  obtain ⟨ct, hct1, -⟩ := spec_exists (sched.cur_thread.spec' (L := L) s1)
  have hcur : σb.curThread = ct.bv := (J1.curEq hct1).1
  have hf : FaultCorrG (.UserException n c) (.userException n.bv c.bv) := Or.inr (Or.inr (Or.inl ⟨n, c, rfl, rfl⟩))
  show (do let t ← sched.cur_thread st s1; faults.handle_fault st arI s1 a1 t (.UserException n c)) ⦃ _ ⦄
  rw [hct1, bind_ok]
  refine WP.spec_mono (WP.spec_and (J1.faultHypJZGSt hA hni1 hct1 hnq1 hvfh1 hf)
    (MKD.faults_handle_fault L.total hA hKD hM1)) ?_
  rintro r ⟨⟨z, hz, -, hJ'⟩, hMr⟩
  refine ⟨z, ?_, hJ', msF_mr hM hMr (MachF.mfk_handleFaultG4 _ _ σb z hz)⟩
  have e1 : n.bv &&& (Fl4Spec.mask 32 : BitVec 64) = n.bv := and_mask_lt n.bv (by decide) hU.1
  have e2 : c.bv &&& (Fl4Spec.mask 28 : BitVec 64) = c.bv := and_mask_lt c.bv (by decide) hU.2
  have hz' : z ∈ (Fl4Spec.handleFault (Z := Unit) σb.curThread
      (.userException (n.bv &&& Fl4Spec.mask 32) (c.bv &&& Fl4Spec.mask 28)) σb).1 := by
    rw [hcur, e1, e2]; exact hz
  exact mem_bind_nd (x := (σb.curThread, σb)) rfl hz'

end

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 8000000 in
/-- (p3J gen 19) **The user-exception entry at given ghosts, stable** (module docstring). -/
theorem user_entryStU41 [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR)
    (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hDR : SetDlDetR (A := A) MR) (hFpu : FpuImplDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s a σ)
    {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z]
    (n c : U64) (hct : σ.curThread ≠ σ.idleThread) (hU : UserHw n c)
    (hFin41 : KFinEv41 (L := L) arI AR (.userLevelFault n.bv c.bv)
      (KFrontF2 (st := st) arI (brU (st := st) arI n c) s a) σ) :
    syscall.handle_user_exception st arI s a n c ⦃ r =>
      ∃ σ', EvOut false (.userLevelFault n.bv c.bv) σ σ' ∧
        JReachU17 (L := L) arI AR MR r.1 r.2 σ' ∧ JStab (L := L) arI AR Z H Cs r.1 r.2 σ' ⦄ := by
  have hFin := hFin41.to13 hFpu
  obtain ⟨hJ3, hGp, hIv, hDv⟩ := hJ
  obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, hR, -, -, -⟩ := jreach_invU3 hnd hJ3
  have hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄ := hPA.minBudget
  have hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄ :=
    fun a => hT.mrt a
  have hD : SetDlDet := setDlDet_of arI hM hDR hR
  have hARK := hARI.toARKeep
  have hS := hX.sb
  have hU3 := sinvX_ut3 hX
  have hSg : SInvG.SpecGlobS σ := sinvX_sg hX
  have hF8 : KFinEv8 (L := L) arI AR (.userLevelFault n.bv c.bv)
      (KFrontF2 (st := st) arI (brU (st := st) arI n c) s a) σ :=
    (hFin.to11 (SInvIV.handleE_idleVtS true (.userLevelFault n.bv c.bv) hSg (sinvX_idleOut hX) hU3 hIv)).to8 hnd
      (sinvX_dom hX)
  have hFin' : KFinEv (L := L) arI AR (.userLevelFault n.bv c.bv)
      (KFrontF2 (st := st) arI (brU (st := st) arI n c) s a) σ :=
    (hF8.to hnd hA hARK hRef hD hT (fun x hx o e => SInvF.fpuOwnOK_of_ft
      (SInvF.kcall_fo_ev true _ (fun c e => by cases e)
        (SInvAll.SInvB.entryJEv hS (fun _ => hct)).ctAct ⟨hS.1.1.nq, hS.1.1.epq⟩ hS.1.1.ut
        hS.1.1.live hS.1.1.ft x hx) o e)).to hA hD
  have hG : syscall.handle_user_exception st arI s a n c ⦃ r =>
      ∃ σ', EvOut false (.userLevelFault n.bv c.bv) σ σ' ∧
      RJM (L := L) arI AR MR r.1 r.2 σ' ∧ JStab (L := L) arI AR Z H Cs r.1 r.2 σ' ⦄ :=
    jEvRef_fltSt (ev := .userLevelFault n.bv c.bv) (G := brUS n c) (B := brU (st := st) arI n c) rfl
      (fun _ h => by cases h) (fun h => by cases h) J hX hct hR (jFltHyp_userSt hnd hM hKD hA hX hct n c hU) hFin'
      hARI hA hnd hM hKD hmrt hmb hT hmax htu
  refine WP.spec_mono (spec_and_eq hG fun _ h => h) ?_
  rintro ⟨s', a'⟩ ⟨⟨σ', hO, hRJM, hSt⟩, hrun⟩
  exact ⟨σ', hO, ⟨JReachU3.user n c hJ3 hct hU hrun hO hRJM,
    SInvGp.kcall_gpmOut true _ hSg hU3 hGp _ hO, evOut_idleVtS hX hIv hO,
    SInvDV.kcall_devRange true _ hU3 hDv _ hO⟩, hSt⟩

set_option maxHeartbeats 8000000 in
/-- (p3J gen 19) **The VM-fault entry at given ghosts, stable** (module docstring). -/
theorem vmf_entryStU41 [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR)
    (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hDR : SetDlDetR (A := A) MR) (hFpu : FpuImplDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s a σ)
    {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z]
    (ad c : U64) (ft : Fl4Spec.VMFaultType) (hct : σ.curThread ≠ σ.idleThread) (hV : VmfHw ad c ft σ)
    (hFin41 : KFinEv41 (L := L) arI AR (.vmFaultEvent ft) (KFrontF2 (st := st) arI (brV (st := st) arI ad c) s a) σ) :
    syscall.handle_vm_fault st arI s a ad c ⦃ r =>
      ∃ σ', EvOut false (.vmFaultEvent ft) σ σ' ∧
        JReachU17 (L := L) arI AR MR r.1 r.2 σ' ∧ JStab (L := L) arI AR Z H Cs r.1 r.2 σ' ⦄ := by
  have hFin := hFin41.to13 hFpu
  obtain ⟨hJ3, hGp, hIv, hDv⟩ := hJ
  obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, hR, -, -, -⟩ := jreach_invU3 hnd hJ3
  have hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄ := hPA.minBudget
  have hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄ :=
    fun a => hT.mrt a
  have hD : SetDlDet := setDlDet_of arI hM hDR hR
  have hARK := hARI.toARKeep
  have hS := hX.sb
  have hU3 := sinvX_ut3 hX
  have hSg : SInvG.SpecGlobS σ := sinvX_sg hX
  have hF8 : KFinEv8 (L := L) arI AR (.vmFaultEvent ft) (KFrontF2 (st := st) arI (brV (st := st) arI ad c) s a) σ :=
    (hFin.to11 (SInvIV.handleE_idleVtS true (.vmFaultEvent ft) hSg (sinvX_idleOut hX) hU3 hIv)).to8 hnd
      (sinvX_dom hX)
  have hFin' : KFinEv (L := L) arI AR (.vmFaultEvent ft) (KFrontF2 (st := st) arI (brV (st := st) arI ad c) s a) σ :=
    (hF8.to hnd hA hARK hRef hD hT (fun x hx o e => SInvF.fpuOwnOK_of_ft
      (SInvF.kcall_fo_ev true _ (fun c e => by cases e)
        (SInvAll.SInvB.entryJEv hS (fun _ => hct)).ctAct ⟨hS.1.1.nq, hS.1.1.epq⟩ hS.1.1.ut
        hS.1.1.live hS.1.1.ft x hx) o e)).to hA hD
  have hG : syscall.handle_vm_fault st arI s a ad c ⦃ r => ∃ σ', EvOut false (.vmFaultEvent ft) σ σ' ∧
      RJM (L := L) arI AR MR r.1 r.2 σ' ∧ JStab (L := L) arI AR Z H Cs r.1 r.2 σ' ⦄ :=
    jEvRef_fltSt (ev := .vmFaultEvent ft) (G := brVS ft) (B := brV (st := st) arI ad c) rfl (fun _ h => by cases h)
      (fun h => by cases h) J hX hct hR (jFltHyp_vmfSt hnd hM hKD hA hX hct ad c ft hV) hFin' hARI hA hnd hM hKD
      hmrt hmb hT hmax htu
  refine WP.spec_mono (spec_and_eq hG fun _ h => h) ?_
  rintro ⟨s', a'⟩ ⟨⟨σ', hO, hRJM, hSt⟩, hrun⟩
  exact ⟨σ', hO, ⟨JReachU3.vmf ad c ft hJ3 hct hV hrun hO hRJM,
    SInvGp.kcall_gpmOut true _ hSg hU3 hGp _ hO, evOut_idleVtS hX hIv hO,
    SInvDV.kcall_devRange true _ hU3 hDv _ hO⟩, hSt⟩

set_option maxHeartbeats 8000000 in
/-- (p3J gen 19) **The unknown-syscall entry at given ghosts, stable** (module docstring). -/
theorem sysU_entryStU41 [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR)
    (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR) (hFpu : FpuImplDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s a σ)
    {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z]
    (n : I64) (hct : σ.curThread ≠ σ.idleThread) (hU : UnkSys (L := L) n s)
    (hND : NoDbgSys (L := L) arI n s a)
    (hFin41 : ∀ ev, KEvSpec (.sysU n) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      KFinEv41 (L := L) arI AR ev (KFrontSysU (st := st) arI n s a) w.2) :
    syscall.handle_syscall st arI s a n ⦃ r =>
      ∃ ev σ', KEvSpec (.sysU n) true ev ∧ EvOut true ev σ σ' ∧
        JReachU17 (L := L) arI AR MR r.1 r.2 σ' ∧ JStab (L := L) arI AR Z H Cs r.1 r.2 σ' ⦄ := by
  have hFin : ∀ ev, KEvSpec (.sysU n) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      KFinEv13 (L := L) arI AR ev (KFrontSysU (st := st) arI n s a) w.2 := fun ev he w hw =>
    (hFin41 ev he w hw).to13 hFpu
  obtain ⟨hJ3, hGp, hIv, hDv⟩ := hJ
  obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, hR, -, -, -⟩ := jreach_invU3 hnd hJ3
  have hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄ := hPA.minBudget
  have hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄ :=
    fun a => hT.mrt a
  have hD : SetDlDet := setDlDet_of arI hM hDR hR
  have hARK := hARI.toARKeep
  have hS := hX.sb
  have hU3 := sinvX_ut3 hX
  have hSg : SInvG.SpecGlobS σ := sinvX_sg hX
  have hFF := J.fastFaultOK (hX.entered hct) hR hX.sb hX.ctQ (fun _ _ => offReady_faultIPSt hX.offReady)
    hARI hA hnd hM hmrt hmb hmax htu n
  have hFin' : ∀ ev, KEvSpec (.sysU n) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      KFinEv (L := L) arI AR ev (KFrontSysU (st := st) arI n s a) w.2 := fun ev he w hw =>
    ((((hFin ev he w hw).to11 (fun x hx => SInvIV.front_idleVtS σ.curThread true ev hSg (sinvX_idleOut hX) hU3 hIv
        x ⟨w, hw, hx⟩)).to8 hnd
      (SInvDom.dp_of_dl (SInvDom.dl_fl4SyscallFaultIP σ.curThread) σ w (sinvX_dom hX) hw)).to hnd hA hARK hRef hD hT
      (fun x hx o e => SInvF.fpuOwnOK_of_ft
        (SInvF.kcall_fo_fip true _ he.not_sys (by cases he <;> intro e <;> cases e)
          (SInvAll.SInvB.entryJ hS hct).ctAct ⟨hS.1.1.nq, hS.1.1.epq⟩ hS.1.1.ut hS.1.1.live hS.1.1.ft w hw x hx)
        o e)).to hA hD
  have hG := jEvRef_sysUSt hnd n J hX hct hR hU hND hSX hFF hFin' hARI hA hM hKD hmrt hmb hT hmax htu
  refine WP.spec_mono (spec_and_eq hG fun _ h => h) ?_
  rintro ⟨s', a'⟩ ⟨⟨ev, σ', hK, hO, hRJM, hSt⟩, hrun⟩
  have hO' : EvOut true ev σ σ' := hO
  obtain ⟨w, hw, hy⟩ := hO
  exact ⟨ev, σ', hK, hO',
    ⟨JReachU3.sysU n ev hJ3 hct hU hND hK hrun hO' hRJM,
      SInvGp.fipEv_gpmOut true ev hSg hU3 hGp hw _ hy, evOut_idleVtS hX hIv hO',
      SInvDV.fip_kcall_devRange _ true ev hU3 hDv w hw _ hy⟩, hSt⟩

end

end

end Fl4Proofs.P3.SInvR.G5
