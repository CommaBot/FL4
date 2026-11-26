/-
P2 (line pte, gen 2): **`serializable_fl4_localP3P`**, FL4's eight local paths (`fl4LocP3W`, int/j16's newest slots
at P3 scope) under rule 8 with **`K.ptes` arbitrary**: each slot's `ownV` path is PTE-cut and lifted to `ownP`
(`PathsP.ofVCut`, `P2/E2EPCut.lean`), and the execution is an `ExecP` (`P2/E2EP.lean`).

The lift premise, per slot (`Fl4AvP`): `AvoidP` [W] (the slot's runs read no PTE word), asked only
* at layouts with PTE words (`K.ptes = ∅`: `avoidP_empty`, no premise), and
* where the slot's premise record `Prem` holds (elsewhere the slot's path is the empty path, which never starts:
  `SlotU.noPre`, `SlotC.noPre`, `SlotN.noPre`, `avoidE_of_noPre`).
`Fl4AvP.all` assembles the family-wide `AvoidP` from these.

Remaining per-slot [W] (`Fl4AvP` fields, `AvoidP` at `K.ptes ≠ ∅` under `Prem`): **vmF, vmR, io, st, irq, sl, vx,
vt** (none discharged: each needs its accepted and declining walks re-run with every read word shown off the PTEs;
the existing walks show reads inside `IoRS` / `SlRS` / `VexitRS`, which contain every gate-only word, PTE words
included, and the only generic facts about read words (`region ≠ .none`, from `fire_rdG` / `IoPre.region_kernel`)
are local to the walks, not exported per run).

Glue ([P]/[J], `ExecP`'s `Fl4StepP`): `start` [P] (a body started is the cut lift's body of one of the slots:
`startAt_ofVCut` turns a start of the `ownV` path into one of its cut lift), `ser` [J] / [P] (a serial exit leaves a
layout with `RegionOKP` / `UserOKP` and the maps `ownP`'s; **choosing `K.ptes` there is the glue's [P]**, as the
gen-1 module docstring of `E2EP`), `arm` [P], `HwStepP` [P]; start layout `RegionOKP` / `UserOKP` [J], `MapsP`.
`serializable_fl4_localP3W` is unchanged (the `K.ptes = ∅` instance: `E2EP.execP_of_V`).
-/
import Fl4Proofs.P2.E2EPCut
import Fl4Proofs.P2.E2EVFl4Top
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.E2E (StartAt SP)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll)

noncomputable section
open Classical

/-! ## The empty branch of a slot never starts -/

section noPre
variable {ι : Type} (D : Dflt)

theorem SlotU.noPre (X : SlotU ι) {i : ι} {K : KLayoutV} {m : U64 → U64} {hK : RegionOKV K} {hU : UserOKV K}
    (h : ¬ X.Prem i K m) (s) : ¬ (X.lift D i K m hK hU).Pre s := by
  have key : ∀ P (W : E2EV.NoVcpuRW K P),
      P = E2EV.LocalPath.void D (OwnMap.ko_aligned (regionOK_userV hK) (userOK_userV hK hU) m) →
      ∀ s, ¬ (E2EV.LocalPath.liftV hK (E2EV.LocalPath.atV hK P W) (noVcpuRd_atV hK P W)).Pre s := by
    rintro P W rfl s hs; exact hs
  exact key _ _ (dif_neg h) s

theorem SlotC.noPre (X : SlotC ι) {i : ι} {K : KLayoutV} {m : U64 → U64} {hK : RegionOKV K} {hU : UserOKV K}
    (h : ¬ X.Prem i K m) (s) : ¬ (X.lift D i K m hK hU).Pre s := by
  have key : ∀ (P : E2E.LocalPath (OwnMap.own K.toKLayout) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m)
      (· ∈ K.user)) (W : E2EV.AvoidV K P),
      P = E2EV.LocalPath.void D (OwnMap.ko_aligned hK.base hU.base m) →
      ∀ s, ¬ (E2EV.LocalPath.cutLiftV hK hU (fun x ⟨_, hv, _⟩ => ko_vcpu hK hv m) P W).Pre s := by
    rintro P W rfl s hs; exact hs
  exact key _ _ (dif_neg h) s

theorem SlotN.noPre (X : SlotN ι) {i : ι} {K : KLayoutV} {m : U64 → U64} {hK : RegionOKV K} {hU : UserOKV K}
    (h : ¬ X.Prem i K m) (s) : ¬ (X.fam D i K m hK hU).Pre s := by
  have key : ∀ P, P = E2EV.LocalPath.void (own := ownV K) (cls := OwnMap.cls K.toKLayout)
      (User := (· ∈ K.user)) D (OwnMap.ko_aligned hK.base hU.base m) → ∀ s, ¬ P.Pre s := by
    rintro P rfl s hs; exact hs
  exact key _ (dif_neg h) s

end noPre

/-! ## The lift premise per slot -/

section av
variable {ιF ιR ιI ιS ιT ιL ν : Type}

/-- **`AvoidP` per slot** [W] (module docstring): at a layout with PTE words, where the slot's premises hold, the
slot's `ownV` path reads no PTE word. -/
structure Fl4AvP (D : Dflt) (F : Fl4Loc ιF ιR ιI ιS ιT ιL ν) : Prop where
  vmF : ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K), K.ptes ≠ ∅ → F.vmF.Prem i K.toKLayoutV m →
    AvoidP K (F.vmF.lift D i K.toKLayoutV m hK.base hU.base)
  vmR : ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K), K.ptes ≠ ∅ → F.vmR.Prem i K.toKLayoutV m →
    AvoidP K (F.vmR.lift D i K.toKLayoutV m hK.base hU.base)
  io : ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K), K.ptes ≠ ∅ → F.io.Prem i K.toKLayoutV m →
    AvoidP K (F.io.lift D i K.toKLayoutV m hK.base hU.base)
  st : ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K), K.ptes ≠ ∅ → F.st.Prem i K.toKLayoutV m →
    AvoidP K (F.st.lift D i K.toKLayoutV m hK.base hU.base)
  irq : ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K), K.ptes ≠ ∅ → F.irq.Prem i K.toKLayoutV m →
    AvoidP K (F.irq.lift D i K.toKLayoutV m hK.base hU.base)
  sl : ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K), K.ptes ≠ ∅ → F.sl.Prem i K.toKLayoutV m →
    AvoidP K (F.sl.lift D i K.toKLayoutV m hK.base hU.base)
  vq : ∀ j (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K), K.ptes ≠ ∅ →
    AvoidP K (F.vq j K.toKLayoutV m hK.base hU.base)

/-- **The family-wide `AvoidP`** from the per-slot premises: no premise at `K.ptes = ∅` (`avoidP_empty`) or where a
slot's premises fail (its path never starts). -/
theorem Fl4AvP.all {D : Dflt} {F : Fl4Loc ιF ιR ιI ιS ιT ιL ν} (h : Fl4AvP D F) :
    ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K), AvoidP K (F.paths D i K.toKLayoutV m hK.base hU.base) := by
  intro i K m hK hU
  by_cases he : K.ptes = ∅
  · exact avoidP_empty he _
  cases i with
  | vmF i =>
    by_cases hp : F.vmF.Prem i K.toKLayoutV m
    · exact h.vmF i K m hK hU he hp
    · exact avoidE_of_noPre (SlotU.noPre D F.vmF hp)
  | vmR i =>
    by_cases hp : F.vmR.Prem i K.toKLayoutV m
    · exact h.vmR i K m hK hU he hp
    · exact avoidE_of_noPre (SlotU.noPre D F.vmR hp)
  | io i =>
    by_cases hp : F.io.Prem i K.toKLayoutV m
    · exact h.io i K m hK hU he hp
    · exact avoidE_of_noPre (SlotU.noPre D F.io hp)
  | st i =>
    by_cases hp : F.st.Prem i K.toKLayoutV m
    · exact h.st i K m hK hU he hp
    · exact avoidE_of_noPre (SlotU.noPre D F.st hp)
  | irq i =>
    by_cases hp : F.irq.Prem i K.toKLayoutV m
    · exact h.irq i K m hK hU he hp
    · exact avoidE_of_noPre (SlotU.noPre D F.irq hp)
  | sl i =>
    by_cases hp : F.sl.Prem i K.toKLayoutV m
    · exact h.sl i K m hK hU he hp
    · exact avoidE_of_noPre (SlotC.noPre D F.sl hp)
  | vq j => exact h.vq j K m hK hU he

/-- **`AvoidP` for two native slots side by side** (`fl4LQP3`'s shape), each asked only under its `Prem`. -/
theorem avoidP_sumN {D : Dflt} {ι κ : Type} {X : SlotN ι} {Y : SlotN κ}
    (hX : ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K), K.ptes ≠ ∅ → X.Prem i K.toKLayoutV m →
      AvoidP K (X.fam D i K.toKLayoutV m hK.base hU.base))
    (hY : ∀ j (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K), K.ptes ≠ ∅ → Y.Prem j K.toKLayoutV m →
      AvoidP K (Y.fam D j K.toKLayoutV m hK.base hU.base)) :
    ∀ j (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K), K.ptes ≠ ∅ →
      AvoidP K (E2EV.PathsV.sum (X.fam D) (Y.fam D) j K.toKLayoutV m hK.base hU.base) := by
  intro j K m hK hU he
  cases j with
  | inl i =>
    by_cases hp : X.Prem i K.toKLayoutV m
    · exact hX i K m hK hU he hp
    · exact avoidE_of_noPre (SlotN.noPre D X hp)
  | inr i =>
    by_cases hp : Y.Prem i K.toKLayoutV m
    · exact hY i K m hK hU he hp
    · exact avoidE_of_noPre (SlotN.noPre D Y hp)

end av

/-! ## The top theorem -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hSt : P0.StoreTotal st) (hm : E2E.MasksWr st) (a0 : A)

/-- **The per-slot `AvoidP` premises of `fl4LocP3W`** [W] (module docstring): the six `Fl4Loc` slots and lvm's two
native slots (vx, vt), each at layouts with PTE words and under its own premise record. -/
structure P3AvP : Prop where
  -- (`stm`: the `TCB_SetTimer` slot; `st` names the store here)
  vmF : ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K), K.ptes ≠ ∅ →
    (fl4LocP3W st ar hA hSt hm a0).vmF.Prem i K.toKLayoutV m →
    AvoidP K ((fl4LocP3W st ar hA hSt hm a0).vmF.lift (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base)
  vmR : ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K), K.ptes ≠ ∅ →
    (fl4LocP3W st ar hA hSt hm a0).vmR.Prem i K.toKLayoutV m →
    AvoidP K ((fl4LocP3W st ar hA hSt hm a0).vmR.lift (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base)
  io : ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K), K.ptes ≠ ∅ →
    (fl4LocP3W st ar hA hSt hm a0).io.Prem i K.toKLayoutV m →
    AvoidP K ((fl4LocP3W st ar hA hSt hm a0).io.lift (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base)
  stm : ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K), K.ptes ≠ ∅ →
    (fl4LocP3W st ar hA hSt hm a0).st.Prem i K.toKLayoutV m →
    AvoidP K ((fl4LocP3W st ar hA hSt hm a0).st.lift (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base)
  irq : ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K), K.ptes ≠ ∅ →
    (fl4LocP3W st ar hA hSt hm a0).irq.Prem i K.toKLayoutV m →
    AvoidP K ((fl4LocP3W st ar hA hSt hm a0).irq.lift (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base)
  sl : ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K), K.ptes ≠ ∅ →
    (fl4LocP3W st ar hA hSt hm a0).sl.Prem i K.toKLayoutV m →
    AvoidP K ((fl4LocP3W st ar hA hSt hm a0).sl.lift (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base)
  vx : ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K), K.ptes ≠ ∅ →
    (E2EV.vxSlotP3 st ar hA hm).Prem i K.toKLayoutV m →
    AvoidP K ((E2EV.vxSlotP3 st ar hA hm).fam (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base)
  vt : ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K), K.ptes ≠ ∅ →
    (E2EV.vtSlotP3 st ar hA hm).Prem i K.toKLayoutV m →
    AvoidP K ((E2EV.vtSlotP3 st ar hA hm).fam (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base)

theorem P3AvP.fl4 (h : P3AvP st ar hA hSt hm a0) : Fl4AvP (fl4Dflt st ar hm) (fl4LocP3W st ar hA hSt hm a0) where
  vmF := h.vmF
  vmR := h.vmR
  io := h.io
  st := h.stm
  irq := h.irq
  sl := h.sl
  vq := avoidP_sumN h.vx h.vt

/-- **FL4's eight local paths under rule 8, `K.ptes` arbitrary**: `fl4LocP3W`'s paths, each PTE-cut and lifted
to `ownP` (`PathsP.ofVCut`, from the per-slot `AvoidP` [W] record `hAv`). -/
def fl4LocP3P (hAv : P3AvP st ar hA hSt hm a0) : PathsP (E2EV.Fl4IxW (S := S)) :=
  PathsP.ofVCut ((fl4LocP3W st ar hA hSt hm a0).paths (fl4Dflt st ar hm)) (P3AvP.fl4 st ar hA hSt hm a0 hAv).all

/-- **FL4 end to end with rules 7 and 8 over its eight local paths, `K.ptes` arbitrary** (module docstring): every
execution `ExecP` over `fl4LocP3P` (the P3-scope slots of `serializable_fl4_localP3W`, PTE-cut and lifted to
`ownP`) from a start with `Init`, `ArmInv`, `RegionOKP` / `UserOKP` [J] and the maps, at a state with no local path
in progress, ran exactly as some serial order of its completed entries. Premises: `hAv` (per-slot `AvoidP` [W]),
`ExecP`'s glue (`Fl4StepP`: `arm` [P], `start` [P], `ser` with the layout choice [P] / [J]; `HwStepP` [P]). -/
theorem serializable_fl4_localP3P (hAv : P3AvP st ar hA hSt hm a0) {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP}
    (h0 : Init s0) (hA0 : ArmInv s0) (hK0 : RegionOKP K0) (hU0 : UserOKP K0) (hM0 : MapsP K0 s0)
    (h : ExecP (fl4LocP3P st ar hA hSt hm a0 hAv) s0 K0 s K) (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_e2eP _ h0 hA0 hK0 hU0 hM0 h hq

end top

end
end Fl4Proofs.P2.E2EP
