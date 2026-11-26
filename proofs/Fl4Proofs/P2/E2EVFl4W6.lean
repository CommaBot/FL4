/-
P2 (integration int/j17): **`serializable_fl4_localW6`, the P3-scope top with no [W] premise** (wiring only; new
definitions, no existing statement changed, no `kernel_entry_reach*` touched).

`serializable_fl4_localW5` (famw gen 4) left one [W] at P3 scope: sl's `ro` (`SlPremB.ro`, the `ReadOnce` of the
generated `handle_syscall_local` tree that `sl_pathsKC5`'s `hpz` asks). slhuf gen 7/8 proved it outright
(`sl_hro2`, from `hSt` / `hA` / `hm` / `a0` only) and packaged the path as **`sl_pathsKC7`** (P2/SlOnceR3.lean:
`sl_pathsKC5` with `IsProg` / `NoZero` / `ReadOnce` all discharged; premises `hCs` [P], `hKD` [P]). This module puts
it in the sl slot:

* `SlPremK7` = `SlPremK` minus `ro` [W] (`vf` [J], `cs` [P], `kd` [P]); **`slSlotK7`**: path `sl_pathsKC7`, its
  `AvoidV` is `slSlotK`'s at the record `⟨vf, cs, kd, sl_hro2 …⟩` (the two paths are the same term up to the proof
  of the `hpz` existential).
* `SlPremP6` = `SlPremB` minus `ro` [W] (`bun`, `cs` [P], `kd` [P]); **`slSlotP3W6`** = `slSlotK7.ofP3` (record
  `K.vcpus = ∅ ∧ SlPremP6`, as `slSlotP3`); `slSlotP3W6_path`: its path is `sl_pathsKC7` (by `rfl`).
* `fl4LocP3W6` = `fl4LocP3W5` with `sl := slSlotP3W6`; **`StartP3W6`** = `StartP3W5` with the sl index's record
  `SlPremP6` (entry fact `SlQ` unchanged); `startAt_P3W6`; `serializable_fl4_localP3W6V` (`ExecV` form) and the top
  **`serializable_fl4_localW6`** (`ExecW` form, `serializable_fl4_localW5`'s statement over `fl4LocP3W6` /
  `StartP3W6`).

## Premise table of `serializable_fl4_localW6` (no [W])

Execution level (as `serializable_fl4_localP3W`): `Init`, `ArmInv`, `MapsV K0`, boot `K0.vcpus = ∅`, `LocPlat` (P3's
platform premises, tagged in P3), `[PlainStore st]`, `hA : ArchTotal` / `hSt : StoreTotal` (proved in P0, parameters
here), `a0`.

| group | premise |
|---|---|
| [P] | `hm : MasksWr`; boot `SerExitW`; per step `arm`, `SerExitW`, `ExitGhostV`; per start `GlueAt` (with the slot record and entry facts below); per hardware step `HwStepV` |
| [J] | per step `VcpuLay` (vacuous at `K'.vcpus = ∅`: `vcpuLay_empty`) |

Per slot, record and start entry facts (beside `Ch σ`, clause 7 of `loc_chain_all`). Untagged: `nv` (`K.vcpus = ∅`,
the glue's layout choice at P3 scope), index conventions (`BunIx` / `ix`, io / st `hQ`), `bun` (the start state),
facts of the arguments (`irq.lt`, `vt.Nt`), `VmFoundC` (clause 10's fl4-sync input `hfd`).

| slot | record | [J] | [P] |
|---|---|---|---|
| vmF | `VmFPrem` + start `VmFEntJ` | record `lay`, `mA`, `uf`; start `br` (`VmBaseR`), `hyp`, `hyt`, `tab` (`RdTab`) | start `lk`, `gl` (`VmGlue`) |
| vmR | `VmRPremP3` + start `VmREntJ` | record `mA`; start `br`, `mid`, `hNt`, `nbt`, `tab` | record `cs`, `kd`; start `lk`, `nb` |
| io | `IoPremW3` + start `IoEntJ` | record `iw`; start `cur`, `lay`, `walk`, `fin` | record `kd` |
| st | `StPremW3` + start `StEntJ4` | record `eu`, `nu`; start `pre`, `tg` | record `kd` |
| irq | `IrqPremK2B` | — | `kd`, `pl` |
| sl | **`SlPremP6`** + start `SlQ` | `SlQ`'s `SlPreB` | **record `cs`, `kd`**; `SlQ`'s `SlEntL`, `SlSyncC`, `SlAccR` |
| vx | `VxPremP3` + start `VxEntJ4` | record `eu`; start `cs`, `curAff`, `cscCore`, `usr` | record `kd`; start `hv`, `buf` |
| vt | `VtPremP5` + start `VtEntJ4` | record `tu`, `eu`, `M`, `OL`, `UB`, `SL`, `pSg`; start `cs`, `curAff`, `cscCore`, `hAs` | record `kd`, `PL` |

**[W]: none.**

## Diff vs `serializable_fl4_localP3W` (int/j16)

| slot | removed | added | by |
|---|---|---|---|
| vmF | start `Pre` [J] as a whole (`VmBase`'s 8 P1 fields, `hEp`, `hRp`) | start `BunIx`, `nv`, `br` / `hyp` / `hyt` / `tab` [J], `lk` / `gl` [P] | famw gen 3 (W4) |
| vmR | start `VmRPre`'s `VmBase` P1 fields, `hEp`, `hRp` | start `BunIx` | famw gen 3 (W4) |
| io | record `pe`, `mA`, `qf` [J]; start `Q` [J] | record `hQ` (index), `iw` [J]; start `BunIx` + `cur` / `lay` / `walk` / `fin` [J] | famw gen 3 (W4) |
| st | record `pe`, `uf` [J]; start `Q` [J] | record `hQ` (index); start `BunIx` + `pre` / `tg` [J] | famw gen 3 (W4) |
| vx | start `inv` / `lay` / `ntw` / `aff` / `aff0` / `vh` / `hvK` [J], `vlk` [P] | start `BunIx`, `hv` [P] | famw gen 3 (W4) |
| vt | start `inv` / `lay` / `ntw` / `aff` / `vf` / `hvK` [J], `vlk` [P]; **record `ro` [W]** | start `BunIx`, `nv`; record `nv`, `tu` [J] | famw gen 3 (W4), gen 4 (W5) |
| sl | **record `ro` [W]** | — | slhuf gen 7/8 (`sl_pathsKC7`), wired here |
| irq | — | — | — |

Net: [W] 2 → 0 (sl `ro`, vt `ro`); [J] trades as listed (vt `tu` [J] is the one new [J] that is not a narrowing of
an old one: `VtmU` at every `VtPre` state, true at bundle states, `E2EVFl4W5`'s docstring); [P] −2 (`vlk` of vx /
vt) +1 (vx `hv`) and vmF's `lk` / `gl` [P] made explicit out of the old whole-`Pre` [J].
-/
import Fl4Proofs.P2.E2EVFl4W5
import Fl4Proofs.P2.SlOnceR3
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EV
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
open Fl4Proofs.P2.OwnMap (fld oAFFINITY region TcbSlot)
open Fl4Proofs.P2.E2E (StartAt SP LocalPath)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll)

noncomputable section
open Classical

section sl
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)

/-- **syscall_local's premises for `sl_pathsKC7`** (`SlPremK` minus `ro` [W]; module docstring). -/
structure SlPremK7 (i : SlArg S) (K : KLayoutV) : Prop where
  /-- [J] -/
  vf : VFacts L K
  /-- [P] the glue's core set is below 64 (P3's sets: `SlJAt.hCs`). -/
  cs : ∀ c ∈ i.Cs, c.val < 64
  /-- [P] at bundle states the locks are determined by kernel words. -/
  kd : ∀ (K : OwnMap.KLayout) (s : S), SlJAt (L := L) K s → KernDetAt (L := L) K i.Locks s

/-- **syscall_local's premises at P3 scope, no [W]** (`SlPremB` minus `ro` [W]; module docstring). -/
structure SlPremP6 (i : SlArg S) (K : KLayoutV) : Prop where
  /-- Some bundle state of the layout (no premise: the start state, `Pre` = `SlJAt K ∧ SlQ`). -/
  bun : ∃ σ : S, SlJAt (L := L) K.toKLayout σ
  /-- [P] the glue's core set is below 64 (P3's sets: `SlJAt.hCs`). -/
  cs : ∀ c ∈ i.Cs, c.val < 64
  /-- [P] at bundle states the locks are determined by kernel words. -/
  kd : ∀ (K : OwnMap.KLayout) (s : S), SlJAt (L := L) K s → KernDetAt (L := L) K i.Locks s

variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)

/-- **syscall_local slot at `sl_pathsKC7`** (route C; `ReadOnce` proved, no [W]). -/
def slSlotK7 : SlotC (SlArg S) where
  Prem i K _ := SlPremK7 st i K
  path i K m hK hU h :=
    sl_pathsKC7 (Locks := i.Locks) (n := i.n) (found := i.found) (Cs := i.Cs) (Ω := i.Ω) (Sg := i.Sg) (Ac := i.Ac)
      ar hSt hA hm a0 h.cs h.kd () K.toKLayout m hK.base hU.base
  Av i K m hK hU h := (slSlotK st ar hA hSt hm a0).Av i K m hK hU ⟨h.vf, h.cs, h.kd, sl_hro2 ar hSt hA hm a0⟩

/-- **syscall_local slot at P3 scope, no [W]** (`slSlotK7` with `VFacts` from `K.vcpus = ∅`). -/
def slSlotP3W6 : SlotC (SlArg S) :=
  (slSlotK7 st ar hA hm hSt a0).ofP3 L (fun i K _ => SlPremP6 st i K) (fun h => h.bun)
    (fun vf h => ⟨vf, h.cs, h.kd⟩)

/-- **The sl slot's path is `sl_pathsKC7`.** -/
theorem slSlotP3W6_path {i : SlArg S} {K : KLayoutV} {m : U64 → U64} (hK : RegionOKV K) (hU : UserOKV K)
    (h : (slSlotP3W6 st ar hA hm hSt a0).Prem i K m) :
    (slSlotP3W6 st ar hA hm hSt a0).path i K m hK hU h =
      sl_pathsKC7 (Locks := i.Locks) (n := i.n) (found := i.found) (Cs := i.Cs) (Ω := i.Ω) (Sg := i.Sg)
        (Ac := i.Ac) ar hSt hA hm a0 h.2.cs h.2.kd () K.toKLayout m hK.base hU.base :=
  rfl

/-- **`fl4LocP3W5` with sl at `sl_pathsKC7`**: every slot at P3 scope, no [W] in any record. -/
def fl4LocP3W6 : Fl4Loc (VmFArg S) (VmRArg S) (IoArg S) (StArg S) (IrqArg S) (SlArg S) (VxArg S ⊕ VtArg S) where
  vmF := vmFSlot st ar hA hm
  vmR := vmRSlotP3 st ar hA hm
  io := ioSlotP3W st ar hA hm
  st := stSlotP3W st ar hA hm
  irq := irqSlotP3W st ar hA hm
  sl := slSlotP3W6 st ar hA hm hSt a0
  vq := fl4LQP3W5 st ar hA hm (fl4Dflt st ar hm)

/-- **The start fact of `fl4LocP3W6`**: `StartP3W5` with the sl index's record `SlPremP6` (entry fact `SlQ` as
before). -/
def StartP3W6 (Ch : S → Prop) (K : KLayoutV) (m : U64 → U64) (hK : RegionOKV K) (hU : UserOKV K) (c : U64)
    (hs : U64 → Prop) (q : SP) : Fl4IxW (S := S) → Prop
  | .sl j => ∃ h : (slSlotP3W6 st ar hA hm hSt a0).Prem j K m,
      GlueAt ((slSlotP3W6 st ar hA hm hSt a0).liftAt j K m hK hU h)
      (fun σ : S => Ch σ ∧ Fl4Proofs.P2.PathObl.SlQ st ar j.Locks j.n j.found j.Cs j.Ω j.Sg j.Ac K.toKLayout m σ) c hs m q
  | i => StartP3W5 st ar hA hm hSt a0 Ch K m hK hU c hs q i

/-- **`StartAt` of `fl4LocP3W6`'s family from the start fact**, given clause 7 on the chain. -/
theorem startAt_P3W6 {Ch : S → Prop} {K : KLayoutV} (hCh : ∀ σ, Ch σ → SlJAt (L := L) K.toKLayout σ)
    {m : U64 → U64} {hK : RegionOKV K} {hU : UserOKV K} {c : U64} {hs : U64 → Prop} {q : SP}
    {i : Fl4IxW (S := S)} (h : StartP3W6 st ar hA hm hSt a0 Ch K m hK hU c hs q i) :
    StartAt ((fl4LocP3W6 st ar hA hm hSt a0).paths (fl4Dflt st ar hm) i K m hK hU) c hs m q := by
  cases i with
  | sl j =>
    obtain ⟨h, hG⟩ := h
    show StartAt ((slSlotP3W6 st ar hA hm hSt a0).lift (fl4Dflt st ar hm) j K m hK hU) c hs m q
    rw [SlotC.lift_eq _ _ h]
    exact hG.startAt fun σ he _ => ⟨hCh σ he.1, he.2⟩
  | vmF j => exact startAt_P3W5 st ar hA hm hSt a0 hCh (i := .vmF j) h
  | vmR j => exact startAt_P3W5 st ar hA hm hSt a0 hCh (i := .vmR j) h
  | io j => exact startAt_P3W5 st ar hA hm hSt a0 hCh (i := .io j) h
  | st j => exact startAt_P3W5 st ar hA hm hSt a0 hCh (i := .st j) h
  | irq j => exact startAt_P3W5 st ar hA hm hSt a0 hCh (i := .irq j) h
  | vq j =>
    cases j with
    | inl j => exact startAt_P3W5 st ar hA hm hSt a0 hCh (i := .vq (.inl j)) h
    | inr j => exact startAt_P3W5 st ar hA hm hSt a0 hCh (i := .vq (.inr j)) h

end sl

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

omit [Fl4Proofs.P1.PlainStore st] in
/-- **`fl4LocP3W6` over `ExecV`.** -/
theorem serializable_fl4_localP3W6V {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutV}
    (h0 : Init s0) (hA0 : ArmInv s0) (hK0 : RegionOKV K0) (hU0 : UserOKV K0) (hM0 : MapsV K0 s0)
    (h : ExecV ((fl4LocP3W6 st ar hA hm hSt a0).paths (fl4Dflt st ar hm)) s0 K0 s K) (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_fl4_localG _ _ h0 hA0 hK0 hU0 hM0 h hq

/-- **FL4 end to end with rule 7 over its eight local paths at P3 scope, no [W] premise** (module docstring: full
premise table and diff vs `serializable_fl4_localP3W`): every execution `ExecW` of FL4 whose starts are
`StartP3W6` facts of `fl4LocP3W6`'s paths, from a boot layout with no VCPU, at a state with no local path in
progress, ran exactly as some serial order of its completed entries. `serializable_fl4_localW5` with sl at
`sl_pathsKC7` (`ReadOnce` of the syscall tree proved). -/
theorem serializable_fl4_localW6 (P : LocPlat st arI AR MR) {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutV}
    {Ch0 Ch : S → Prop} (h0 : Init s0) (hA0 : ArmInv s0) (hB : SerExitW P K0 Ch0) (nv0 : K0.vcpus = ∅)
    (hM0 : MapsV K0 s0)
    (h : ExecW ((fl4LocP3W6 st ar hA hm hSt a0).paths (fl4Dflt st ar hm)) (StartP3W6 st ar hA hm hSt a0) P s0 K0
      Ch0 s K Ch) (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  have hE := (execV_of_W (fun _ _ _ _ _ _ _ _ _ hCh hi => startAt_P3W6 st ar hA hm hSt a0 hCh hi) hB h).1
  have hok := serExitW_ok hB (vcpuLay_empty nv0)
  exact serializable_fl4_localP3W6V st ar hA hm hSt a0 h0 hA0 hok.1 hok.2 hM0 hE hq

end top

end
end Fl4Proofs.P2.E2EV
