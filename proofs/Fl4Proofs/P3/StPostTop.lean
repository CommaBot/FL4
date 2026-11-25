/-
P3 (line stpost): **the accepted trapped syscall beside the gate, with the stable ghosts**.

`kernel_entry_reachU29S`'s unknown-syscall clause (P1 `syscall_local_same`: an accepted
`handle_syscall_local` of a `TRAP_SYSCALLS` thread *is* `handle_syscall`, which runs the
unknown-syscall fault entry) at *given* ghosts: from any `JAtZ Z H Cs …` (with `VxE Z`) at a
`JReachU17` state, under that clause's inputs verbatim, an accepted run ends at a spec outcome
that is `JReachU17` **and** `JStab Z H Cs` (`JAtZ (Z.mv G V) H Cs …`).

* `sysU_inputs`: the clause's `KFinEv13` input to `jEvRef_sysU`'s `KFinEv` (U13's `to11` with
  `front_idleVtS`, U11's `to8` with `DomListOK` after the FaultIP write, U8's `to` with the
  FPU-owner fact, U5's `to31`), and `FastFaultOK` by `JAtZ.fastFaultOK` (U2F), at the given
  ghosts.
* `kernel_entry_sysU_localSt`: StPostEv's `jEvRef_sysUSt` at the given ghosts, carried to
  `handle_syscall_local` by P1 `syscall_local_triple`; `JReachU17` at the same outcome by
  `JReachU3.sysU` (the run itself) and the three spec facts (`fipEv_gpmOut`, `evOut_idleVtS`,
  `fip_kcall_devRange`), as U12 / U13 / U17 carry them.

Premises: the U29 tops' (a subset); no new premise.
-/
import Fl4Proofs.P3.StPostEv
import Fl4Proofs.P3.XTopJointKEntryU29S
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 8000000 in
/-- **The accepted trapped syscall at given ghosts, stable** (module docstring). -/
theorem kernel_entry_sysU_localSt [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR)
    (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s a σ)
    {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z]
    (n : I64) (found : U64 × U64) (hct : σ.curThread ≠ σ.idleThread) (hU : UnkSys (L := L) n s)
    (hND : NoDbgSys (L := L) arI n s a)
    (hFin : ∀ ev, KEvSpec (.sysU n) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      KFinEv13 (L := L) arI AR ev (KFrontSysU (st := st) arI n s a) w.2) :
    syscall.handle_syscall_local st arI s a n found ⦃ r => r.1 = true →
      ∃ ev σ', KEvSpec (.sysU n) true ev ∧ EvOut true ev σ σ' ∧
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
  refine P1.syscall_local_triple (P := fun r : S × A => ∃ ev σ', KEvSpec (.sysU n) true ev ∧ EvOut true ev σ σ' ∧
    JReachU17 (L := L) arI AR MR r.1 r.2 σ' ∧ JStab (L := L) arI AR Z H Cs r.1 r.2 σ') arI hA J.bxi (fun _ et => J.cnOff et) (P1.found_vacuous J.bxi hU) ?_
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
