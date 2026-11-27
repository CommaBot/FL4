/-
P3 (p3J gen 19): **the general interrupt entry at given ghosts, stable, on U41's finish record** (stage A of
the stable-ghost interrupt chain; stages Q / K transport it as U33 / U42 transport U32 / U41).

StPostIrqTop's `kernel_entry_irq_localSt17` runs StPostIrqEv's `jEvRef_irqASt` (the general
`syscall.handle_interrupt_entry`) at given ghosts and wraps it in the local-timer gate. Here the same run
without the gate, with U41's per-entry finish premise in place of U17's:

* **`irq_entryStU41`**: from `JReachU17` and a given `JAtZ Z H Cs` (with `VxE Z`), under U29's interrupt-clause
  platform facts, `IrqHw` and `hFin : KFinEv41` at `KFrontI s a1 w` (+ `FpuImplDet`, which turns it into
  U13's `KFinEv13` by `KFinEv41.to13`), `handle_interrupt_entry … w` ends at an `EvOut false .interrupt`
  outcome that is `JReachU17` **and** `JStab Z H Cs` (`JAtZ (Z.mv G V) H Cs …`).

Premises: StPostIrqTop's (`hARI hA hnd hM hKD hPA hIA hT hmax htu hRef hDR`), `IrqHw` [P] and the per-entry
`KFinEv41` (discharged at the top, P3JStIrqTop, as U43 discharges it); no new premise. No sorry. New module; no
existing statement changed.
-/
import Fl4Proofs.P3.StPostIrqTop
import Fl4Proofs.P3.XTopJointKEntryU41
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 8000000 in
/-- (p3J gen 19) **The general interrupt entry at given ghosts, stable** (module docstring). -/
theorem irq_entryStU41 [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop}
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR) (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hDR : SetDlDetR (A := A) MR) (hFpu : FpuImplDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s a σ)
    {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z]
    (w : U64) (a1 : A) (hI : IrqHw AR MR a a1 σ w)
    (hFin41 : KFinEv41 (L := L) arI AR .interrupt (KFrontI (st := st) arI s a1 w) σ) :
    syscall.handle_interrupt_entry st arI s a1 w ⦃ r =>
      ∃ σ', EvOut false .interrupt σ σ' ∧
        JReachU17 (L := L) arI AR MR r.1 r.2 σ' ∧ JStab (L := L) arI AR Z H Cs r.1 r.2 σ' ⦄ := by
  have hFin : KFinEv13 (L := L) arI AR .interrupt (KFrontI (st := st) arI s a1 w) σ := hFin41.to13 hFpu
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
  have hF8 : KFinEv8 (L := L) arI AR .interrupt (KFrontI (st := st) arI s a1 w) σ :=
    (hFin.to11 (SInvIV.handleE_idleVtS true .interrupt hSg (sinvX_idleOut hX) hU3 hIv)).to8 hnd (sinvX_dom hX)
  have hFin' : KFinEv (L := L) arI AR .interrupt (KFrontI (st := st) arI s a1 w) σ :=
    (hF8.to hnd hA hARK hRef hD hT (fun x hx o e => SInvF.fpuOwnOK_of_ft
      (SInvF.kcall_fo_ev true _ (fun c e => by cases e)
        (SInvAll.SInvB.entryJEv hS (fun h => absurd rfl h)).ctAct ⟨hS.1.1.nq, hS.1.1.epq⟩ hS.1.1.ut
        hS.1.1.live hS.1.1.ft x hx) o e)).to hA hD
  have hG := jEvRef_irqASt J hX hI hFin' hARI hA hnd hM hKD hIA hmrt hmb hT hmax htu
  refine WP.spec_mono (spec_and_eq hG fun _ h => h) ?_
  rintro ⟨s', a'⟩ ⟨⟨σ', hO, hRJM, hSt⟩, hrun⟩
  exact ⟨σ', hO, ⟨JReachU3.irq w hJ3 hI hrun hO hRJM,
    SInvGp.kcall_gpmOut true .interrupt hSg hU3 hGp _ hO, evOut_idleVtS hX hIv hO,
    SInvDV.kcall_devRange true _ hU3 hDv _ hO⟩, hSt⟩

end

end

end Fl4Proofs.P3.SInvR.G5
