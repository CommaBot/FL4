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
import Fl4Proofs.P2.E2EAD
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

/-- **Owners ignore the paging words of an epoch** (they decide no owner: leaves `pte_nondec`, upper entries
region `.none`). -/
theorem pwe_own {K : KLayoutP} (hK : RegionOKP K) {E : U64 → U64} :
    ∀ m m' : U64 → U64, (∀ x, ¬ PWE K E x → m x = m' x) → ownP K m = ownP K m' :=
  fun _ _ h => ownP_congr hK fun d hd => h d fun hp =>
    OwnMap.nondec_of_region hK.base.base (Or.inr (Or.inr (Or.inr (Or.inl (pwe_region hK hp))))) hd

/-- **One slot's share of `hIns`** from its store runs touching no paging word of the epoch
(`E2EAD.LocalPath.insA`). -/
theorem insA_of_noG {LP : PathsP ι} {i : ι} {K : KLayoutP} {E : U64 → U64} {s : Cfg U64 U64 U64 U64}
    {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {hs : U64 → Prop} {q : SP} (hM : MapsP K s)
    (hNG : ∀ s1 s2 a, (LP i K s.mem hK hU).Pre s1 →
      @Alt _ (LP i K s.mem hK hU).st (LP i K s.mem hK hU).L ((LP i K s.mem hK hU).RS s1)
        (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout s.mem) (· ∈ K.user) s1 s2 →
      Within (LP i K s.mem hK hU).st (LP i K s.mem hK hU).ar (fun b => ¬ PWE K E b)
        (fun b => b ∈ K.user ∨ ¬ PWE K E b) (LP i K s.mem hK hU).p s2 a)
    (h : StartAt (LP i K s.mem hK hU) c hs s.mem q) :
    InsA (PWE K E) ADEq NotPresent s.own s.cls s.ko c hs s.mem q := by
  rw [hM.own, hM.cls, hM.ko]
  exact (LP i K s.mem hK hU).insA (moveHeldP hK) (ownDepP hK hU) (pwe_own hK) hNG h

end exec

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

end top

end
end Fl4Proofs.P2.E2EP
