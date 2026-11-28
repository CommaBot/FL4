/-
P2 (iolay gen 8): **E2EVFl4W16 — W14 without the execution-layer [J] `VcpuLay`** (new definitions only, on top of
W14; no existing statement changes).

## What `VcpuLay` is and where it is asked

`VcpuLay L K := VcpuHeap K ∧ VcpuSpec L K` (famw, `P2/E2EVFl4W3.lean`): every VCPU of the layout's VCPU set
`K.vcpus` is a P1 heap object `.other 15`, and a spec `vcpu` object of the spec state of **every** clause-7 bundle
of `K.toKLayout`. Its only consumer is `serExitW_ok` (`RegionOKV K` from `regionOKV_of_JAtZ`, i.e. the VCPU fields
`none` / `disj` / `tcbw` of `RegionOKV`). It is asked at the boot layout (W3's `hV0`; from W5 on replaced by the
untagged `K0.vcpus = ∅`, `vcpuLay_empty`) and **per serial step** as `Fl4StepW.serV : SerStep s c → VcpuLay L K'`,
consumed once, in `execV_of_W` / `execV_of_WC` (`Fl4StepV.ser`'s `RegionOKV K'`).

## Result: not derivable from W14's premises; replaced by the existing untagged layout convention

* **Not derivable.** In `Fl4StepW` the new layout's VCPU set `K'.vcpus` is constrained only by `serV` itself:
  `SerExitW P K' Ch'` reads `K'.toKLayout` only (**`serExitW_vcpus`**: it holds for `K'` iff for `K'` with any other
  VCPU set), `ExitGhostV K' s'` constrains the model state `s'` (its `own` := `ownV K'`), not `K'`, `keep` speaks of
  non-serial steps, and `Serial.Step.serial` installs arbitrary ghost maps. So for any layout chosen by `SerExitW`
  and any address `p` that is not a heap `.other 15` object (e.g. the current TCB of the exit's bundle), the layout
  `{K' with vcpus := {p}}` together with `s'.own := ownV …` meets every field of `Fl4StepW` except `serV`, and
  **`not_vcpuLay_single`** shows `VcpuLay` fails there. (No full Lean counter-execution: the claim is that no other
  premise mentions `K'.vcpus`, and the lemma shows the obligation is not vacuous.)
* **True where the glue chooses the P3-scope layout.** At `K'.vcpus = ∅` it holds outright (`vcpuLay_empty`).
  `K.vcpus = ∅` is already an untagged premise of W14 in two places: the boot layout (`nv0`) and **every slot's start
  fact** (vmF `VmFEntJ14.nv`, vmR `VmRPremP3.nv`, io / st / irq / sl through `SlotU.ofP3` / `SlotC.ofP3`'s record
  `K.vcpus = ∅ ∧ R`, vx `VxPremP3.nv`, vt `VtPremP5.nv`), documented as "the glue's layout choice at P3 scope" (W6
  docstring). **`startP3W14_nv`**: every `StartP3W14` fact implies `K.vcpus = ∅` for its layout.
* **W16**: `Fl4StepW16` = `Fl4StepW` with `serV : VcpuLay L K'` [J] replaced by `serN : K'.vcpus = ∅` (untagged:
  the same glue layout convention as `nv0` and the starts' `nv`, applied at serial exits too); `Fl4StepW16.toW`,
  `ExecW16`, `ExecW16.toW`, **`serializable_fl4_localW16`** (W14's premises with `ExecW16` for `ExecW`).

## Premise diff vs `serializable_fl4_localW14`

| | W14 | W16 |
|---|---|---|
| per serial step | `serV : VcpuLay L K'` [J] | `serN : K'.vcpus = ∅` (untagged layout convention) |
| everything else | `SerExitW` [P] (boot, per step), `nv0`, `MapsV`, `Init`, `ArmInv`, `LocPlat`, `hIoa`, `arm` [P], `serX` [P], `serG` (`ExitGhostV`) [P], `HwStepV` [P], `StartP3W14` starts | unchanged |

No new [W] / [J] / [P].

## Vacuity check

* `serN` is a fact about the ghost layout, not quantified over store states, so the ≥ 2-core problem of a fixed
  datum quantified over all `Pre` states (jsweep gen 1 finding 1) does not arise.
* No start fact becomes unsatisfiable: no slot's start fact asks `K.vcpus ≠ ∅` (each asks `K.vcpus = ∅`,
  `startP3W14_nv`), so in an epoch with at least one start `serN` is implied by that start's own fact; in an epoch
  with none it only fixes a ghost.
* Consistency with the other per-step fields: `SerExitW` is insensitive to the VCPU set (`serExitW_vcpus`), so the
  layout P3's `chainC` chooses can always be taken with `vcpus := ∅`; `ExitGhostV` then sets `s'.own := ownV K'`,
  which is `own K'.toKLayout` (`ownV_off`). `HwStepV K'` becomes unsatisfiable at `K'.vcpus = ∅` (a hardware write
  of a non-user word must be in a VCPU of the layout), which matches P3 scope (no TCB is bound to a VCPU at a P3
  state, `JExt.vw`, so no guest runs); it was already so under W14's `nv0` and the starts' `nv`.
-/
import Fl4Proofs.P2.E2EVFl4W14
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EV
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
open Fl4Proofs.P2.E2E (StartAt SP LocalPath SerStep)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg)

noncomputable section
open Classical

/-! ## `VcpuLay` is not constrained by the other per-step fields -/

section free
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

omit [Fl4Proofs.P1.PlainStore st] in
/-- **`VcpuLay` is a real obligation**: a VCPU set containing an address that is not a heap `.other 15` object
breaks it. -/
theorem not_vcpuLay_single (K : KLayoutV) {p : U64} (hp : K.heap p ≠ some (.other 15)) :
    ¬ VcpuLay L { K with vcpus := {p} } :=
  fun h => hp (h.1 p (Set.mem_singleton p))

end free

/-! ## Every start fact of W14 asks the P3-scope layout -/

section start
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st] {A : Type}
  (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop) (MR : A3 → Fl4Spec.MachineState → Prop)

variable {arI AR MR} in
/-- **Every `StartP3W14` fact implies `K.vcpus = ∅`** for its layout (module docstring, vacuity check). -/
theorem startP3W14_nv {Ch : S → Prop} {K : KLayoutV} {m : U64 → U64} {hK : RegionOKV K} {hU : UserOKV K}
    {c : U64} {hs : U64 → Prop} {q : SP} {i : Fl4IxW (S := S)}
    (h : StartP3W14 st ar hA hm hSt a0 arI AR MR Ch K m hK hU c hs q i) : K.vcpus = ∅ := by
  cases i with
  | vmF j =>
    obtain ⟨_, σ, a, he, -⟩ := h
    exact (VmFEntJ14.nv he.2)
  | vmR j =>
    obtain ⟨hp, -⟩ := h
    exact hp.nv
  | io j =>
    obtain ⟨hp, -⟩ := h
    exact (hp.toW3 st).toP3.1
  | st j =>
    obtain ⟨hp, -⟩ := h
    exact hp.toP3.1
  | irq j =>
    obtain ⟨⟨hn, -⟩, -⟩ := h
    exact hn
  | sl j =>
    obtain ⟨⟨hn, -⟩, -⟩ := h
    exact hn
  | vq j =>
    cases j with
    | inl j =>
      obtain ⟨hp, -⟩ := h
      exact hp.nv
    | inr j =>
      obtain ⟨hp, -⟩ := h
      exact hp.toP5.nv

end start

/-! ## Executions with the layout convention at serial exits -/

section exec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {ι : Type}

/-- **A step of FL4, W16 form**: `Fl4StepW` with `serV : VcpuLay L K'` [J] replaced by the glue's layout
convention `serN : K'.vcpus = ∅` (module docstring). -/
structure Fl4StepW16 (LP : PathsV ι)
    (SF : (S → Prop) → ∀ K : KLayoutV, (U64 → U64) → RegionOKV K → UserOKV K → U64 → (U64 → Prop) → SP → ι → Prop)
    (P : LocPlat st arI AR MR) (s : Cfg U64 U64 U64 U64) (K : KLayoutV) (Ch : S → Prop) (c : U64)
    (s' : Cfg U64 U64 U64 U64) (K' : KLayoutV) (Ch' : S → Prop) : Prop where
  /-- [P] an armed program is pure glue (as `Fl4StepW.arm`). -/
  arm : ∀ p, s'.ph c = .arm p → PureGlue p
  /-- [P] the glue's start (as `Fl4StepW.start`). -/
  start : ∀ p0 k W, s.ph c = .loc p0 (.start k) W → ∀ (hK : RegionOKV K) (hU : UserOKV K),
    ∃ i, SF Ch K s.mem hK hU c (fun l => s.lk l = some c) k i
  /-- [P] the serial exit's ghost choice (as `Fl4StepW.serX`). -/
  serX : SerStep s c → SerExitW P K' Ch'
  /-- The glue's layout choice at P3 scope (untagged, as the boot `nv0` and every start's `nv`). -/
  serN : SerStep s c → K'.vcpus = ∅
  /-- [P] the exit ghost with rule 7 (as `Fl4StepW.serG`). -/
  serG : SerStep s c → ExitGhostV K' s'
  /-- Layout and chain change only at serial steps. -/
  keep : ¬ SerStep s c → K' = K ∧ Ch' = Ch

/-- **An execution of FL4, W16 form**: `ExecW` with `Fl4StepW16` steps. -/
inductive ExecW16 (LP : PathsV ι)
    (SF : (S → Prop) → ∀ K : KLayoutV, (U64 → U64) → RegionOKV K → UserOKV K → U64 → (U64 → Prop) → SP → ι → Prop)
    (P : LocPlat st arI AR MR) (s0 : Cfg U64 U64 U64 U64) (K0 : KLayoutV) (Ch0 : S → Prop) :
    Cfg U64 U64 U64 U64 → KLayoutV → (S → Prop) → Prop
  | refl : ExecW16 LP SF P s0 K0 Ch0 s0 K0 Ch0
  | step {s s' : Cfg U64 U64 U64 U64} {K K' : KLayoutV} {Ch Ch' : S → Prop} {c : U64} :
      ExecW16 LP SF P s0 K0 Ch0 s K Ch → Step s c s' → Fl4StepW16 LP SF P s K Ch c s' K' Ch' →
      ExecW16 LP SF P s0 K0 Ch0 s' K' Ch'
  | hw {s : Cfg U64 U64 U64 U64} {K : KLayoutV} {Ch : S → Prop} {v a x : U64} :
      ExecW16 LP SF P s0 K0 Ch0 s K Ch → HwStepV K s v a x → ExecW16 LP SF P s0 K0 Ch0 (hwCfg s a x) K Ch

end exec

/-! ## The top -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

end top

end
end Fl4Proofs.P2.E2EV
