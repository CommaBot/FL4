/-
P3 (line stpost, generation 9): **the accepted VM-fault entry beside the gate at stable ghosts**
(`syscall.handle_vm_fault_local`, U29Vm's first clause; StPostTop's route for the unknown syscall).

`handle_vm_fault_local … ad c` (fl4-sync's local page-fault entry), where it returns `true`, is the
general VM-fault entry `handle_vm_fault` (P1 `vm_local_triple`, with `P1.VmFaultOK` from
`JAtZ.vmFaultOK`): `budget_ok`, FL4's branch `brV ad c` (the fault from the address and error code,
then `handle_fault`), `finish`. Every step keeps the stable ghosts:

* `jFltHyp_vmfSt`: XTopJointKEntryEv3's `jFltHyp_vmf` with the post `JStab Z H Cs` (StPostEv's
  `JFltHypSt`; the fault by StPostFault's `JAtZ.faultHypJZGSt`, as `jFltHyp_unkSt`), under the same
  hardware agreement `VmfHw` [P] as the U29 clause's input.
* **`kernel_entry_vmf_localSt17`**: from `JReachU17` and given `JAtZ Z H Cs` (with `VxE Z`), under U29Vm's
  VM-fault clause inputs (`hct`, `hV : VmfHw`, `hFin : KFinEv13`), an accepted run ends at an
  `EvOut false (.vmFaultEvent ft)` outcome that is `JReachU17` **and** `JStab Z H Cs`. StPostEv's
  `jEvRef_fltSt` with `jFltHyp_vmfSt`; `hFin` to `KFinEv` as StPostIrqTop (U13 `to11` with
  `handleE_idleVtS`, U11 `to8`, U8 `to` with `kcall_fo_ev`, U5 `to`); `JReachU17` by `JReachU3.vmf` and
  `kcall_gpmOut` / `evOut_idleVtS` / `kcall_devRange`.

Premises: a subset of U29's platform facts (StPostTop's list); `VmfHw` [P] is the clause's own input.
No new premise.
-/
import Fl4Proofs.P3.StPostTop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 8000000 in
/-- (stpost) **`JFltHypSt` of the VM-fault entry** (`jFltHyp_vmf` by `faultHypJZGSt`). -/
theorem jFltHyp_vmfSt (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR)
    (hA : P0.ArchTotal arI) {Z : XSets} [VxE Z] {H : P1.Heap} {Cs : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hX : SInvX σ) (hct : σ.curThread ≠ σ.idleThread) (ad c : U64) (ft : Fl4Spec.VMFaultType)
    (hV : VmfHw ad c ft σ) :
    JFltHypSt (L := L) arI AR MR Z H Cs (brV (st := st) arI ad c) (brVS ft) s a σ := by
  intro σb s1 a1 Ac' Lst' D' hb _ J1 hM1
  obtain ⟨hni1, hnq1, hvfh1, ekc, ect, ems⟩ := budget_true_facts hnd hX hct hb
  obtain ⟨x0, hx0, -⟩ := (SInvAll.SInvB.entryJ hX.sb hct).ctAct
  have hkb : σb.kheap σb.curThread = some (.tcb x0) := by rw [ekc]; exact hx0
  obtain ⟨ct, hct1, -⟩ := spec_exists (sched.cur_thread.spec' (L := L) s1)
  have hcur : σb.curThread = ct.bv := (J1.curEq hct1).1
  show (do
      let t ← sched.cur_thread st s1
      let i ← c >>> 4#i32
      let i1 ← lift (i &&& 1#u64)
      let f ← vspace.vm_fault ad c (i1 != 0#u64)
      faults.handle_fault st arI s1 a1 t f) ⦃ _ ⦄
  rw [hct1, bind_ok, shr_eq c 4#i32 (by decide) (by decide), bind_ok]
  simp only [lift, bind_ok, vspace.vm_fault]
  generalize hins : (((⟨c.bv >>> (4#i32 : I32).toNat⟩ : U64) &&& 1#u64) != 0#u64) = ins
  have hii := (ins_iff c).trans hV.kind.symm
  rw [hins] at hii
  have hf : FaultCorrG (.VmFault ad c ins) (.archFault (.vmFault ad.bv [(if ins then 1#u64 else 0#u64).bv, c.bv])) :=
    Or.inr (Or.inr (Or.inr ⟨ad, c, ins, rfl, rfl⟩))
  refine WP.spec_mono (WP.spec_and (J1.faultHypJZGSt hA hni1 hct1 hnq1 hvfh1 hf)
    (MKD.faults_handle_fault L.total hA hKD hM1)) ?_
  rintro r ⟨⟨z, hz, -, hJ'⟩, hMr⟩
  refine ⟨z, ?_, hJ', msF_mr hM hMr (MachF.mfk_handleFaultG4 _ _ σb z hz)⟩
  have hb0 : (if ins then 1#u64 else 0#u64).bv = ftBit ft := by
    cases ft <;> cases ins
    · rfl
    · exact absurd (hii.1 rfl) (by intro h; cases h)
    · exact absurd (hii.2 rfl) (by intro h; cases h)
    · rfl
  have he := handleVmFault_err hkb ft hb0
  have e5 : x0.tcbArch.tcbContext.userRegs .errorRegister &&& (Fl4Spec.mask 5 : BitVec 64) = c.bv := by
    rw [hV.err x0 hx0]; exact and_mask_lt c.bv (by decide) hV.lt
  rw [e5, ems, hV.addr] at he
  have hz' : z ∈ (Fl4Spec.NonDetE.catch (Fl4Spec.handleVmFault (Z := Unit) σb.curThread ft)
      (Fl4Spec.handleFault σb.curThread) σb).1 :=
    mem_catch_err he (by rw [hcur]; exact hz)
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
/-- (stpost) **The accepted VM-fault entry beside the gate at given ghosts, stable** (module
docstring). -/
theorem kernel_entry_vmf_localSt17 [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR)
    (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s a σ)
    {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z]
    (ad c : U64) (ft : Fl4Spec.VMFaultType) (hct : σ.curThread ≠ σ.idleThread) (hV : VmfHw ad c ft σ)
    (hFin : KFinEv13 (L := L) arI AR (.vmFaultEvent ft) (KFrontF2 (st := st) arI (brV (st := st) arI ad c) s a) σ) :
    syscall.handle_vm_fault_local st arI s a ad c ⦃ r => r.1 = true →
      ∃ σ', EvOut false (.vmFaultEvent ft) σ σ' ∧
        JReachU17 (L := L) arI AR MR r.2.1 r.2.2 σ' ∧ JStab (L := L) arI AR Z H Cs r.2.1 r.2.2 σ' ⦄ := by
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
  refine P1.vm_local_triple (P := fun r : S × A => ∃ σ', EvOut false (.vmFaultEvent ft) σ σ' ∧
    JReachU17 (L := L) arI AR MR r.1 r.2 σ' ∧ JStab (L := L) arI AR Z H Cs r.1 r.2 σ') arI hSX hA
    (J.vmFaultOK (hX.entered hct) hR hX.sb hX.ctQ hX.offReady hARI hA hnd hM hmrt hmb hmax htu) ?_
  refine WP.spec_mono (spec_and_eq hG fun _ h => h) ?_
  rintro ⟨s', a'⟩ ⟨⟨σ', hO, hRJM, hSt⟩, hrun⟩
  exact ⟨σ', hO, ⟨JReachU3.vmf ad c ft hJ3 hct hV hrun hO hRJM,
    SInvGp.kcall_gpmOut true _ hSg hU3 hGp _ hO, evOut_idleVtS hX hIv hO,
    SInvDV.kcall_devRange true _ hU3 hDv _ hO⟩, hSt⟩

end

end

end Fl4Proofs.P3.SInvR.G5
