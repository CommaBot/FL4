/-
# P2 (line mmuAD, gen 4): **`ExecU3b` is an `ARunR`** — the U3b top reduced to the per-slot `InsA` obligation

`MmuADEpoch.ExecU3b` is FL4's execution with the U2 glue, the VCPU hardware and the page walker's A/D writes to
every paging word of the current epoch (`PWE K E`, leaves in any lock state and the upper-level entries).
`SerialADR.serializable_safeR` serializes an `ARunR`. This module maps one onto the other:

* **`execU3b_aRunR`**: an `ExecU3b` execution is an `ARunR ADEq NotPresent` one with word set `PWE K E`, carrying
  `RegionOKP K`, `UserOKP K`, `MapsP K s`, `SerExitW` and `EpochJ K E s` (`MmuADEpoch`). Core steps: `SafeStep`
  from `LocalPath.safe` as in `E2EPU3.exec_safeRunPA`; a serial step is preceded by `ARunR.regate` to the new
  epoch's `PWE K' s'.mem` (the gate is closed, so no local path is in progress, and no body starts at it); the
  epoch invariant by `epochJ_keep` / `epochJ_ser` / `epochJ_mmu`; A/D writes are `ADWr`s (`adWr_pwe`).
  The started bodies' `InsA` is the hypothesis **`hIns`**: at every start in an epoch state, the body `LocalPath`
  `i` starts is run-relatively insensitive to the epoch's paging words.
* **`serializable_U3b_of`**: hence `RunAll s.log s0.mem s.mem` at every quiescent `ExecU3b` state.
* **`serializable_fl4_localU3b_of`**: the same for U2's family and glue (`serializable_fl4_localU3`'s premises),
  with `hIns` as an explicit hypothesis. `hIns` is the per-slot work left (handoff, gen 4): `E2EAD.LocalPath.insA`
  discharges it for a slot whose store runs from every alternative touch no paging word of the epoch; the walks of
  delPte / CNodeDelete read paging words masked and need the masked form of that bridge.

No [W], no new [J]; the only [P] is `MmuAD` (P2/MmuADWalk.lean). `hIns` is a hypothesis of a reduction theorem, not
a premise of a top. No existing statement changed.
-/
import Fl4Proofs.P2.MmuADEpoch
import Fl4Proofs.P2.SerialADR
import Fl4Proofs.P2.E2EPU3
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg HwWr allowed_of_sinv InsA ARunR
  aRunR_inv serializable_safeR)
open Fl4Proofs.P2.MmuAD (MmuAD ADEq NotPresent adEq_equiv)

noncomputable section
open Classical

section exec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {ι : Type}

/-- **An `ExecU3b` execution is an `ARunR` one** (module docstring). -/
theorem execU3b_aRunR {LP : PathsP ι}
    {SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop}
    (hSF : ∀ (Ch : S → Prop) (K : KLayoutP) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K) c hs q i,
      (∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) →
      (∃ s1 : Cfg U64 U64 U64 U64, (K.vcpus = ∅ ∧ K.ptes = ptesR K s1.mem) ∧ ∀ x, GateW K x → s.mem x = s1.mem x) →
      SF Ch K s.mem hK hU c hs q i → StartAt (LP i K s.mem hK hU) c hs s.mem q)
    (hIns : ∀ (K : KLayoutP) (E : U64 → U64) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K)
      (c : U64) (hs : U64 → Prop) (q : SP) (i : ι), EpochJ K E s → MapsP K s →
      StartAt (LP i K s.mem hK hU) c hs s.mem q → InsA (PWE K E) ADEq NotPresent s.own s.cls s.ko c hs s.mem q)
    (P : LocPlat st arI AR MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} {E : U64 → U64} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0) (h : ExecU3b LP SF P s0 K0 Ch0 s K Ch E) :
    ARunR ADEq NotPresent s0 s (PWE K E) ∧ RegionOKP K ∧ UserOKP K ∧ MapsP K s ∧
      SerExitW P K.toKLayoutV Ch ∧ EpochJ K E s := by
  obtain ⟨hK0, hU0⟩ := okP_R hB hc0
  induction h with
  | refl => exact ⟨.refl _, hK0, hU0, hM0, hB, epochJ_ser hc0⟩
  | @step s1 s1' K1 K1' Ch1 Ch1' c1 E1 _ hS g ih =>
    obtain ⟨hR, hK, hU, hM, hX, J⟩ := ih
    obtain ⟨⟨H, I⟩, -, hSI, -⟩ := aRunR_inv adEq_equiv h0 hA0 hR
    have hst : ∀ p0 k W, s1.ph c1 = .loc p0 (.start k) W →
        ∃ i, StartAt (LP i K1 s1.mem hK hU) c1 (fun l => s1.lk l = some c1) s1.mem k := by
      intro p0 k W hph
      obtain ⟨i, hi⟩ := g.start p0 k W hph hK hU
      exact ⟨i, hSF _ _ s1 _ _ _ _ _ i hX.chainOf (epoch_start J) hi⟩
    have hok : Fl4Proofs.P2.Serial.SafeStep s1 c1 s1' := by
      refine ⟨g.arm, fun p0 k W hph => ?_⟩
      obtain ⟨i, hP⟩ := hst p0 k W hph
      rw [hM.own, hM.cls, hM.ko]
      exact (LP i K1 s1.mem hK hU).safe (moveHeldP hK) (ownDepP hK hU) hP
    by_cases hs : SerStep s1 c1
    · rw [if_pos hs]
      have hnl := I.inv.clo hs.1
      have hR' := ARunR.regate (PWE K1' s1'.mem) hR hs.1
      have hK' := okP_R (g.serX hs) (g.serC hs)
      refine ⟨.step hR' hS hok (fun p0 k W hph => absurd (by rw [hph]; trivial) (hnl c1)), hK'.1, hK'.2,
        g.serG hs, g.serX hs, epochJ_ser (g.serC hs)⟩
    · rw [if_neg hs]
      obtain ⟨eK, eC⟩ := g.keep hs
      subst eK eC
      have hal := allowed_of_sinv hSI c1
      refine ⟨.step hR hS hok (fun p0 k W hph => ?_), hK, hU, maps_stepP hK hM hal hS hs, hX,
        epochJ_keep J (fun x hx => step_gate_keep hM hal hS hs hx)⟩
      obtain ⟨i, hP⟩ := hst p0 k W hph
      exact hIns _ _ _ hK hU _ _ _ i J hM hP
  | hw _ hH ih =>
    obtain ⟨hR, hK, hU, hM, hX, J⟩ := ih
    exact ⟨.hw hR (hH.hwWr hK hM), hK, hU, maps_hwP hK hM hH, hX,
      epochJ_keep J (fun x hx => hw_gate_keep hK hM hH hx)⟩
  | mmu _ hH ih =>
    obtain ⟨hR, hK, hU, hM, hX, J⟩ := ih
    exact ⟨.ad hR (adWr_pwe hK hM hH), hK, hU, maps_pwe hK hM hH, hX, epochJ_mmu J hH⟩

/-- **Every quiescent `ExecU3b` state is serial** given `hIns` (module docstring). -/
theorem serializable_U3b_of {LP : PathsP ι}
    {SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop}
    (hSF : ∀ (Ch : S → Prop) (K : KLayoutP) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K) c hs q i,
      (∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) →
      (∃ s1 : Cfg U64 U64 U64 U64, (K.vcpus = ∅ ∧ K.ptes = ptesR K s1.mem) ∧ ∀ x, GateW K x → s.mem x = s1.mem x) →
      SF Ch K s.mem hK hU c hs q i → StartAt (LP i K s.mem hK hU) c hs s.mem q)
    (hIns : ∀ (K : KLayoutP) (E : U64 → U64) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K)
      (c : U64) (hs : U64 → Prop) (q : SP) (i : ι), EpochJ K E s → MapsP K s →
      StartAt (LP i K s.mem hK hU) c hs s.mem q → InsA (PWE K E) ADEq NotPresent s.own s.cls s.ko c hs s.mem q)
    (P : LocPlat st arI AR MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} {E : U64 → U64} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0) (h : ExecU3b LP SF P s0 K0 Ch0 s K Ch E) (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_safeR adEq_equiv h0 hA0 (execU3b_aRunR hSF hIns P h0 hA0 hB hc0 hM0 h).1 hq

end exec

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- The U2 family (`serializable_fl4_localU3`'s). -/
abbrev famU2 :=
  PathsP.sum (fl4LocW11JA st ar hA (masksWr_plain st) L.total a0)
    (PathsP.sum (PathsP.sum (delPteSlot st ar hA (masksWr_plain st)) (invSlotU st ar hA (masksWr_plain st)))
      (cmSlotU st ar hA (masksWr_plain st)))

/-- **FL4 end to end with A/D writes to every paging word of the epoch, given the per-slot `hIns`**:
`serializable_fl4_localU3`'s premises over `ExecU3b`; `hIns` is the open per-slot obligation (module docstring). -/
theorem serializable_fl4_localU3b_of (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    (hIns : ∀ (K : KLayoutP) (E : U64 → U64) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K)
      (c : U64) (hs : U64 → Prop) (q : SP) i, EpochJ K E s → MapsP K s →
      StartAt (famU2 st ar hA a0 i K s.mem hK hU) c hs s.mem q →
      InsA (PWE K E) ADEq NotPresent s.own s.cls s.ko c hs s.mem q)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} {E : U64 → U64} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecU3b (famU2 st ar hA a0) (StartV2 st ar hA a0 arI AR MR) P s0 K0 Ch0 s K Ch E)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  refine serializable_U3b_of ?_ hIns P h0 hA0 hB hc0 hM0 h hq
  intro Ch K s hK hU c hs q i hC hE hsf
  have nv : K.vcpus = ∅ := by
    obtain ⟨_, ⟨nv, _⟩, _⟩ := hE
    exact nv
  rcases i with i | ((j | j) | j)
  · exact startAt_U st ar hA (masksWr_plain st) L.total a0 P hIoa hC hE (startU_of_U2 st ar hA a0 hC nv hsf)
  · exact delPteStart_at st ar hA (masksWr_plain st) hC hE (hsf.2 fun _ s b v _ _ _ => hsf.1.wr s b v)
  · exact invStartU2_at st ar hA (masksWr_plain st) hC hE (hsf.2 fun _ s b v _ _ _ => hsf.1.wr s b v)
  · exact cmStartU2_at st ar hA (masksWr_plain st) hC hE (hsf.2 fun _ s b v _ _ _ => hsf.1.wr s b v)

end top

end
end Fl4Proofs.P2.E2EP
