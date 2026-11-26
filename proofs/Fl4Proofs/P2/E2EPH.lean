/-
P2 (line glue, gen 1): **end to end with rule 8, start facts at the serial-prefix memory** (`serializable_e2ePH`),
beside `E2EP.serializable_e2eP` (unchanged).

`Fl4StepP.start` asks `StartAt (LP i K s.mem …) c hs s.mem k`: a store state agreeing with the **physical** memory
at the start, which other cores' bodies in progress may have left where no kernel invariant holds (audU F1).
Here an execution carries Serial's serial-prefix memory `H` as a ghost index (`SerialH.NextH`), and the start is
asked at `H`:

* `Fl4StepPH.start`: `∃ i, StartAt (LP i K H hK hU) c hs H k` (the path at the history's memory, the store state
  agreeing with `H` on aligned kernel words). Every other field is `Fl4StepP`'s.
* `ExecPH LP s0 K0 s K H`: `ExecP` with the ghost (`NextH` per core step, the same write per hardware step).
* **`exec_safeRunPH`**: an `ExecPH` is an `XSafeRunH`: at a start, `SerialH.veq_start` gives the core's view
  `VEq H s.mem`, `LocalPath.safeH` the body's `Safe` at `s.mem`. `ko_congrP` identifies the path's class owners at
  `H` with the configuration's (they are read off `AFFINITY` words, the gate's: `ownP_aff_gate`, and `H` is the
  memory on every gate word, `SerialH.xsafeRunH_agree`). `MoveHeld` is `moveHeldP`; a hardware write moves no owner
  at any memory (`ownP_upd_nondec`).
* **`serializable_e2ePH`**: where an `ExecPH` reaches a state with no local path in progress, memory is the serial
  run of the completed entries (`serializable_e2eP`'s conclusion).

Premises: those of `serializable_e2eP` with `start` [P] at `H`. No existing statement changed.
-/
import Fl4Proofs.P2.E2EP
import Fl4Proofs.P2.E2EH
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.PathObl Fl4Proofs.P2.E2E Fl4Proofs.P2.OwnMapV Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Step Init ArmInv NoLoc RunAll PureGlue Allowed Held HwWr hwCfg
  VEq NextH SafeStepH XSafeRunH serializable_safeXH xsafeRunH_inv xsafeRunH_agree allowed_of_sinv)

noncomputable section
open Classical

section ko
variable {K : KLayoutP}

/-- **A TCB's `AFFINITY` word is the gate's under `ownP`.** -/
theorem ownP_aff_gate (hK : RegionOKP K) {t b : U64} (hr : OwnMap.region K.toKLayout b = .tcb t)
    (m : U64 → U64) : ownP K m (OwnMap.fld t OwnMap.oAFFINITY) = .gate := by
  have ht := hK.base.base.tcbOf t b hr
  have h1 := (hK.base.base.tcb t ht OwnMap.oAFFINITY (Or.inl rfl)).1
  have hp : OwnMap.fld t OwnMap.oAFFINITY ∉ K.ptes := by
    intro hp; rw [hK.none _ hp] at h1; cases h1
  have hv : ¬ ∃ w, InVcpu K.toKLayoutV w (OwnMap.fld t OwnMap.oAFFINITY) := by
    rintro ⟨w, hw⟩; rw [hK.base.none w _ hw] at h1; cases h1
  rw [ownP_off hp, ownV_off hv]
  exact OwnMap.own_aff_gate hK.base.base ht m

/-- **Class owners agree between memories agreeing on the gate's words.** -/
theorem ko_congrP (hK : RegionOKP K) {m m' : U64 → U64} (h : ∀ y, ownP K m y = .gate → m' y = m y) :
    OwnMap.ko K.toKLayout m' = OwnMap.ko K.toKLayout m := by
  funext b
  unfold OwnMap.ko
  cases hr : OwnMap.region K.toKLayout b with
  | tcb t => simp only [h _ (ownP_aff_gate hK hr m)]
  | _ => rfl

end ko

/-! ## Steps and executions with the serial-prefix memory -/

/-- **A step of FL4 with rule 8, the start at the history** (module docstring): `Fl4StepP` with `start` [P] asked
at the ghost memory `H`. -/
structure Fl4StepPH {ι : Type} (LP : PathsP ι) (s : Cfg U64 U64 U64 U64) (K : KLayoutP) (H : U64 → U64)
    (c : U64) (s' : Cfg U64 U64 U64 U64) (K' : KLayoutP) : Prop where
  arm : ∀ p, s'.ph c = .arm p → PureGlue p
  start : ∀ p0 k W, s.ph c = .loc p0 (.start k) W → ∀ (hK : RegionOKP K) (hU : UserOKP K),
    ∃ i, StartAt (LP i K H hK hU) c (fun l => s.lk l = some c) H k
  ser : SerStep s c → RegionOKP K' ∧ UserOKP K' ∧ MapsP K' s'
  keep : ¬ SerStep s c → K' = K

/-- **An execution of FL4 with rules 7 and 8 and its serial-prefix memory** `H` (ghost, `NextH`). -/
inductive ExecPH {ι : Type} (LP : PathsP ι) (s0 : Cfg U64 U64 U64 U64) (K0 : KLayoutP) :
    Cfg U64 U64 U64 U64 → KLayoutP → (U64 → U64) → Prop
  | refl : ExecPH LP s0 K0 s0 K0 s0.mem
  | step {s s' : Cfg U64 U64 U64 U64} {K K' : KLayoutP} {H : U64 → U64} {c : U64} :
      ExecPH LP s0 K0 s K H → Step s c s' → Fl4StepPH LP s K H c s' K' →
      ExecPH LP s0 K0 s' K' (NextH s c s' H)
  | hw {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {H : U64 → U64} {v a x : U64} :
      ExecPH LP s0 K0 s K H → HwStepP K s v a x → ExecPH LP s0 K0 (hwCfg s a x) K (Function.update H a x)

section exec

theorem exec_safeRunPH {ι : Type} {LP : PathsP ι} {s0 s : Cfg U64 U64 U64 U64}
    {K0 K : KLayoutP} {H : U64 → U64} (h0 : Init s0) (hA0 : ArmInv s0) (hK0 : RegionOKP K0)
    (hU0 : UserOKP K0) (hM0 : MapsP K0 s0) (h : ExecPH LP s0 K0 s K H) :
    XSafeRunH s0 s H ∧ RegionOKP K ∧ UserOKP K ∧ MapsP K s := by
  induction h with
  | refl => exact ⟨.refl, hK0, hU0, hM0⟩
  | @step s s' K K' H c _ hst hF ih =>
    obtain ⟨hr, hK, hU, hM⟩ := ih
    obtain ⟨-, -, -, hS, -⟩ := xsafeRunH_inv h0 hA0 hr
    refine ⟨.step hr hst ⟨hF.arm, fun p0 k W hph hV => ?_, by rw [hM.own]; exact moveHeldP hK⟩, ?_⟩
    · obtain ⟨i, hP⟩ := hF.start p0 k W hph hK hU
      have hko : s.ko = OwnMap.ko K.toKLayout H := by
        rw [hM.ko]
        refine (ko_congrP hK fun y hy => xsafeRunH_agree h0 hA0 hr y fun d hd => ?_).symm
        rw [hM.own, hy] at hd; exact hd
      rw [hM.own, hM.cls, hko] at hV ⊢
      exact (LP i K H hK hU).safeH (moveHeldP hK) (ownDepP hK hU) hP hV
    · by_cases hs : SerStep s c
      · exact hF.ser hs
      · rw [hF.keep hs]
        exact ⟨hK, hU, maps_stepP hK hM (allowed_of_sinv hS c) hst hs⟩
  | hw _ hh ih =>
    obtain ⟨hr, hK, hU, hM⟩ := ih
    refine ⟨.hw hr (hh.hwWr hK hM) fun m => ?_, hK, hU, maps_hwP hK hM hh⟩
    rw [hM.own]
    exact ownP_upd_nondec hK (OwnMapV.vcpu_nondec hK.base (hh.vcpu hK.base).1) _ _

/-- **End to end with rules 7 and 8, the starts at the serial-prefix memory** (module docstring). -/
theorem serializable_e2ePH {ι : Type} (LP : PathsP ι) {s0 s : Cfg U64 U64 U64 U64}
    {K0 K : KLayoutP} {H : U64 → U64} (h0 : Init s0) (hA0 : ArmInv s0) (hK0 : RegionOKP K0)
    (hU0 : UserOKP K0) (hM0 : MapsP K0 s0) (h : ExecPH LP s0 K0 s K H) (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_safeXH h0 hA0 (exec_safeRunPH h0 hA0 hK0 hU0 hM0 h).1 hq

end exec

end
end Fl4Proofs.P2.E2EP
