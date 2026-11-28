/-
# P2 (line vmscope, gen 1): a real VM exit beside the gate — `serializable_fl4_localVX1`

`serializable_fl4_localU1` (P2/E2EPU2.lean) covers the vmF / vmR / vx / vt local paths only at layouts with no VCPU:
its glue (`ExecWPR.serC`) asks `K'.vcpus = ∅` at every serial exit, so `VexitEnt.vin` forces the exiting VCPU
`v = 0`, and fl4-sync's `vm_local` declines every such exit before `handle_vcpu_exit_local` runs (`l.vcpu == 0`).
That is P3's scope: every P3 state has no TCB bound to a VCPU (`JExt.vw` [S], `NativeScope`), so the P3 chain the glue
ghost comes from (`SerExitW`) has no state at which a guest runs.

This module adds **VM epochs**: serial exits whose ghost layout has VCPUs, outside P3's scope, in which the VM-exit
local path (`local_vm_exit` with an exiting VCPU `v ≠ 0`, the accepted run writing `v.PENDING`, the exiting thread and
the core's scheduler words beside the gate, interleaved with the hardware's writes to running VCPUs) runs; and keeps
U1's eleven slots in the native epochs (`K.vcpus = ∅`), unchanged.

* **`VxPremV`**: the VM-exit slot's record at any layout (`VxPremP3` without `nv`): `hv0 : i.v ≠ 0` (the index is a
  real exit: fl4-sync runs the body only for a bound VCPU), `vu : VcpuNU K` [S], `eu` [S], `kd` [P].
* **`vxSlotV`** (`SlotN`, the path `vexit_localPathPG2`: `IsProg`, `NoZero`, `ReadOnce` discharged, as `vxSlotP3`),
  **`vx_avoidPV_path`** / **`vx_avoidPV`** (PTE avoidance under `QPs`: `vx_avoidPJ_path`'s proof, which never used
  `nv`), **`vxSlotPV`** (restricted to `QPs`, PTE-cut, lifted to `ownP`).
* **`VxStartV`** [S] (start fact): `GlueAt` of the path at a state with its `Pre` (`VexitEnt ∧ VexitPEnt`) and `QPs`;
  **`vxStartV_at`** (`StartAt` of `vxSlotPV`, no chain needed), **`vxStartV_vcpu`** (every such start has
  `i.v ∈ K.vcpus`: the exit is of a VCPU of the layout, so `K.vcpus ≠ ∅` — the start is outside P3's scope).
* **`Fl4StepVX`** / **`ExecVX`**: `ExecWPR`'s glue step with the serial exit either native (`SerExitW` [P], the
  convention `K'.vcpus = ∅ ∧ K'.ptes = ptesR K' s'.mem`) or a VM exit (`K'.vcpus ≠ ∅` and `VtxLayP K'` [S]);
  **`execP_of_VX`**: an `ExecVX` is an `ExecP`, with the epoch invariant "a native epoch has its chain and `ptesR`
  data" (`execP_of_WPRG`'s induction with the VM case added).
* **`StartVX`** (native starts carry `K.vcpus = ∅`; every U1 record already has it as `nv`), **`serializable_fl4_localVX1G`**
  (any native family whose start facts give `StartAt` from the chain and the epoch data) and
  **`serializable_fl4_localVX1`**: U1's family `⊕ vxSlotPV`.

## New premises (all only in VM epochs; native epochs are exactly U1's)
| premise | tag | why it is not proved here |
|---|---|---|
| `VtxLayP K'` at a VM serial exit (`RegionOKP` / `UserOKP` of a layout with VCPUs) | [S] | native epochs get it from the P3 chain (`serExitW_ok` + `vcpuLay_empty`). With VCPUs, `RegionOKV`'s VCPU fields need `VcpuLay` (VCPU objects are heap `.other 15` / spec `vcpu` objects), a fact about states with VT-x objects, which P3 does not have (`JExt.nat`: no VCPU cap; VT-x invocations are `JVtxScope` [scope]). A VT-x joint invariant (`JVm` at a nonempty set, P3/JVm.lean) would give it. |
| `VxPremV.vu : VcpuNU K` | [S] | vlift's `UserObj` (user words in no VCPU), derived in native epochs only through `JVmL` + a P3 bundle (`VFacts.ofJVm`). |
| `VxPremV.eu` (`VxPre` kept by aligned user writes) | [S] | jsweep gen 1 derived it (`vxEu_of`) from a P3 bundle and `nv` (the VCPU clauses vacuous); at a VM exit neither exists. It is lvm's `hEU`. |
| `VxStartV`'s entry (`VexitEnt ∧ VexitPEnt ∧ QPs` at the start state) | [S] | the start state is a guest-running state (`TS_RUNNING_VM` thread with a bound VCPU): P1's facts there (`BXI`) are not given by P3 (`NativeScope`), and P1's top excludes VT-x entries (`P3Place.vmchk`; P1/VcpuExitInv proves only that `handle_vcpu_exit` keeps `EntryInv`). |
| `VxPremV.kd`, `GlueAt`'s correspondence, `arm`, `serG`, `HwStepP` | [P] | as in U1. |
| `K'.vcpus ≠ ∅` at a VM exit; `K.vcpus = ∅` in a native start | convention | the glue's layout choice (a native start's `nv` is already a field of every U1 record). |

No new [J] / [W]. No existing statement or file changed except the root import list.
-/
import Fl4Proofs.P2.E2EPU2
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld)
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg xsafeRun_greach allowed_of_sinv)

noncomputable section
open Classical

/-! ## The VM-exit slot at any layout -/

section slot
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)

/-- **`local_vm_exit`'s record at a layout with VCPUs** (module docstring): `VxPremP3` without `nv`. -/
structure VxPremV (i : VxArg S) (K : KLayoutV) (m : U64 → U64) : Prop where
  /-- The index is a real exit (fl4-sync's `vm_local` runs the body only for a bound VCPU, `l.vcpu ≠ 0`). -/
  hv0 : i.v ≠ 0#u64
  /-- [S] no VCPU word is a user word (vlift's `UserObj`; VT-x layout, outside P3's scope). -/
  vu : VcpuNU K
  /-- [S] the path's `Pre` is kept by aligned user writes (lvm's `hEU`; jsweep's `vxEu_of` needs a P3 bundle). -/
  eu : VxEuX st i K m
  /-- [P] the locks are determined by the core, the kernel base and the aligned words off `(userV K).user`. -/
  kd : ∀ s, KernDetS (L := L) (userV K).user i.lk s

/-- **The VM-exit slot at any layout** (`vxSlotP3` with `vu` for `vcpuNU_empty nv`). -/
def vxSlotV : SlotN (VxArg S) where
  Prem i K m := VxPremV st i K m
  path i _ m hK hU h :=
    vexit_localPathPG2 (T := i.T) (Cs := i.Cs) (Ω := i.Ω) (Sg := i.Sg) (Rp := i.Rp) (Scs := i.Scs) (Nt := i.Nt)
      (Ac := i.Ac) (H := i.H) (Z := i.Z) (lk := i.lk) (v := i.v) (n := i.n) (m := m) ar hA hK hU hm
      h.vu h.eu
      (fun s b v' hb hba => hlk_of_kernelDetU (P := fun _ => True) (fun s _ => h.kd s) s b v' trivial
        (mem_userV.2 (Or.inl hb)) hba)

/-- **The VM-exit path at any layout reads no PTE word under `QPs`** (`vx_avoidPJ_path`'s proof; it never used
`nv`). -/
theorem vx_avoidPV_path (i : VxArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (h : (vxSlotV st ar hA hm).Prem i K.toKLayoutV m) :
    AvoidP K (((vxSlotV st ar hA hm).path i K.toKLayoutV m hK.base hU.base h).rJ K (fun b hb => Or.inl hb)) := by
  have hVU := vcpuNU_pteU hK
  have hP : ∀ s, QPs K st s → VxP (L := L) K s := fun s hq => vxP_of_ksb hq.ks hq.ksb
  refine avoidE_of_entry (P := ((vxSlotV st ar hA hm).path i K.toKLayoutV m hK.base hU.base h).rJ K
      (fun b hb => Or.inl hb))
    (E := (· ∈ K.ptes)) (vexit_noZero i.v i.n) (IsProg.on (vexit_isProg S i.v i.n) _ _ _)
    (fun s => VexitRSP (L := L) K st i.lk s) (fun s => VexitWS (L := L) K.toKLayoutV st i.lk s)
    (fun s x _ hx => hx.2) ?_
    (fun s => VexitRSP (L := L) K st i.lk s) (fun s => IrqDec (L := L) st s)
    (fun s x _ hx => ⟨hx.1.1, hx.1, hx.2⟩)
    (fun s x hs hx => by
      obtain ⟨hs1, -⟩ := hs
      exact ((show VxPre st i K.toKLayoutV m s from hs1).1.dec hx).1) ?_
  · intro s a r hs hr hb
    obtain ⟨hs1, hs2⟩ := hs
    have hs' : VxPre st i K.toKLayoutV m s := hs1
    have hq : QPs K st s := hs2
    obtain ⟨b, s1, a1⟩ := r
    have hb' : b = true := hb
    subst hb'
    have hr' : localvm.handle_vcpu_exit_local st ar s a i.v i.n = ok (true, s1, a1) := hr
    have hd := hP s hq
    have g : localvm.handle_vcpu_exit_local (guard st (VexitRSP K st i.lk s) (VexitWS K.toKLayoutV st i.lk s))
        ar s a i.v i.n = ok (true, s1, a1) := by
      by_cases hp0 : vcpu.get st s i.v vcpu.PENDING = ok 0#u64
      · exact vexit_acc_own_npP ar hA hK hK.base hVU hs'.1 hd.1 hd.2 hp0 hr'
      · exact vexit_acc_own_pP ar hA hK hK.base hVU hs'.1 hd.1 hd.2 hs'.2 hp0 hr'
    exact g
  · intro s a r hs hr hb
    obtain ⟨hs1, hs2⟩ := hs
    have hs' : VxPre st i K.toKLayoutV m s := hs1
    have hq : QPs K st s := hs2
    obtain ⟨b, s1, a1⟩ := r
    cases b
    · have hr' : localvm.handle_vcpu_exit_local st ar s a i.v i.n = ok (false, s1, a1) := hr
      have hd := hP s hq
      have g : localvm.handle_vcpu_exit_local (guard st (VexitRSP K st i.lk s) (IrqDec st s))
          ar s a i.v i.n = ok (false, s1, a1) :=
        vexit_dec_ownP ar hA hK hK.base hVU hs'.1 hd.1 hd.2 hr'
      exact g
    · exact absurd rfl hb

/-- **The VM-exit slot's family member reads no PTE word under `QPs`** (the empty path where `VxPremV` fails). -/
theorem vx_avoidPV (i : VxArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) :
    AvoidP K (((vxSlotV st ar hA hm).fam (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base).rJ K
      (fun b hb => Or.inl hb)) := by
  by_cases hp : (vxSlotV st ar hA hm).Prem i K.toKLayoutV m
  · have key : ∀ P, P = (vxSlotV st ar hA hm).path i K.toKLayoutV m hK.base hU.base hp →
        AvoidP K (P.rJ K (fun b hb => Or.inl hb)) := by
      rintro P rfl
      exact vx_avoidPV_path st ar hA hm i K m hK hU hp
    exact key _ (SlotN.fam_pos _ _ hp)
  · exact avoidE_restrQ_noPre (SlotN.noPre (fl4Dflt st ar hm) _ hp)

/-- **The VM-exit slot under `ownP`**: restricted to `QPs` states, PTE-cut, lifted. -/
def vxSlotPV : PathsP (VxArg S) :=
  fun i K m hK hU => LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx m) _ (vx_avoidPV st ar hA hm i K m hK hU)

/-- **The VM-exit slot's start fact** [S] (module docstring): the record, and the glue's correspondence `GlueAt`
[P] at a state with the path's `Pre` (`VexitEnt ∧ VexitPEnt`, a guest-running state P3 does not model) and `QPs`;
the armed program the cut of the `ownV` program. -/
def VxStartV (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64) (hs : U64 → Prop)
    (q : SP) (j : VxArg S) : Prop :=
  ∃ q0, (∃ h : VxPremV st j K.toKLayoutV m,
      GlueAt ((vxSlotV st ar hA hm).path j K.toKLayoutV m hK.base hU.base h)
        (fun σ : S => VxPre st j K.toKLayoutV m σ ∧ QPs K st σ) c hs m q0) ∧
    q = cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) c q0 ∅

/-- **`StartAt` of the VM-exit slot** from its start fact (no chain, no epoch data). -/
theorem vxStartV_at {K : KLayoutP} {μ : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64}
    {hs : U64 → Prop} {q : SP} {j : VxArg S} (h : VxStartV st ar hA hm K μ hK hU c hs q j) :
    StartAt (vxSlotPV st ar hA hm j K μ hK hU) c hs μ q := by
  obtain ⟨q0, ⟨hp, hG⟩, rfl⟩ := h
  have key : ∀ (Pf : LocalPath (ownV K.toKLayoutV) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) (· ∈ K.user))
      (hAv : AvoidP K (Pf.rJ K (fun b hb => Or.inl hb))),
      Pf = (vxSlotV st ar hA hm).path j K.toKLayoutV μ hK.base hU.base hp →
      StartAt (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx μ) _ hAv) c hs μ
        (cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c q0 ∅) := by
    rintro Pf hAv rfl
    obtain ⟨σ, a, he, hc, hl, hμ, e⟩ := hG
    refine ⟨σ, a, he, hc, hl, hμ, ?_⟩
    refine Eq.trans ?_ (body_cutLiftP hK hU (fun x hx => ko_pte hK hx μ) _ hAv σ a).symm
    change _ = cutP _ _ _ _ (((vxSlotV st ar hA hm).path j K.toKLayoutV μ hK.base hU.base hp).L.cpu σ)
      (((vxSlotV st ar hA hm).path j K.toKLayoutV μ hK.base hU.base hp).body σ a) ∅
    rw [hc, ← e]
  exact key _ _ (SlotN.fam_pos _ _ hp)

/-- **Every start of the VM-exit slot is a real VM exit**: the exiting VCPU is one of the layout's, so the layout
has VCPUs (the start is outside P3's scope, where `vOf = 0` and `K.vcpus = ∅`). -/
theorem vxStartV_vcpu {K : KLayoutP} {μ : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64}
    {hs : U64 → Prop} {q : SP} {j : VxArg S} (h : VxStartV st ar hA hm K μ hK hU c hs q j) :
    j.v ≠ 0#u64 ∧ j.v ∈ K.vcpus := by
  obtain ⟨q0, ⟨hp, σ, a, he, -⟩, -⟩ := h
  exact ⟨hp.hv0, (he.1.1.vin hp.hv0).1⟩

theorem vxStartV_ne {K : KLayoutP} {μ : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64}
    {hs : U64 → Prop} {q : SP} {j : VxArg S} (h : VxStartV st ar hA hm K μ hK hU c hs q j) :
    K.vcpus ≠ ∅ := fun e => by
  have hv := (vxStartV_vcpu st ar hA hm h).2
  rw [e] at hv
  exact hv

end slot

/-! ## Executions with native and VM epochs -/

section exec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {ι : Type}

/-- **The layout facts of a VM epoch** [S] (module docstring): rules 7 and 8's layout facts for a layout with VCPUs
(native epochs get them from the P3 chain, `okP_R`). -/
def VtxLayP (K : KLayoutP) : Prop := RegionOKP K ∧ UserOKP K

/-- **A step of FL4 with native and VM epochs** (module docstring): `Fl4StepWPR` with the serial exit's layout either
native (`serX` [P] + the convention, as `ExecWPR`) or a VM layout (`K'.vcpus ≠ ∅`, `VtxLayP` [S]). -/
structure Fl4StepVX (LP : PathsP ι)
    (SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop)
    (P : LocPlat st arI AR MR) (s : Cfg U64 U64 U64 U64) (K : KLayoutP) (Ch : S → Prop) (c : U64)
    (s' : Cfg U64 U64 U64 U64) (K' : KLayoutP) (Ch' : S → Prop) : Prop where
  /-- [P] an armed program is pure glue. -/
  arm : ∀ p, s'.ph c = .arm p → PureGlue p
  /-- [P] the glue's start fact. -/
  start : ∀ p0 k W, s.ph c = .loc p0 (.start k) W → ∀ (hK : RegionOKP K) (hU : UserOKP K),
    ∃ i, SF Ch K s.mem hK hU c (fun l => s.lk l = some c) k i
  /-- The serial exit: native ([P] `SerExitW`, the convention `vcpus = ∅`, `ptes = ptesR`) or VM (convention
  `vcpus ≠ ∅`, [S] `VtxLayP`). -/
  ser : SerStep s c → (SerExitW P K'.toKLayoutV Ch' ∧ K'.vcpus = ∅ ∧ K'.ptes = ptesR K' s'.mem) ∨
    (K'.vcpus ≠ ∅ ∧ VtxLayP K')
  /-- [P] the exit ghost with rule 8. -/
  serG : SerStep s c → MapsP K' s'
  /-- Layout and chain change only at serial steps. -/
  keep : ¬ SerStep s c → K' = K ∧ Ch' = Ch

/-- **An execution of FL4 with native and VM epochs.** -/
inductive ExecVX (LP : PathsP ι)
    (SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop)
    (P : LocPlat st arI AR MR) (s0 : Cfg U64 U64 U64 U64) (K0 : KLayoutP) (Ch0 : S → Prop) :
    Cfg U64 U64 U64 U64 → KLayoutP → (S → Prop) → Prop
  | refl : ExecVX LP SF P s0 K0 Ch0 s0 K0 Ch0
  | step {s s' : Cfg U64 U64 U64 U64} {K K' : KLayoutP} {Ch Ch' : S → Prop} {c : U64} :
      ExecVX LP SF P s0 K0 Ch0 s K Ch → Step s c s' → Fl4StepVX LP SF P s K Ch c s' K' Ch' →
      ExecVX LP SF P s0 K0 Ch0 s' K' Ch'
  | hw {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {Ch : S → Prop} {v a x : U64} :
      ExecVX LP SF P s0 K0 Ch0 s K Ch → HwStepP K s v a x → ExecVX LP SF P s0 K0 Ch0 (hwCfg s a x) K Ch

/-- The epoch data of a native epoch (`execP_of_WPRG`'s invariant). -/
def NatEp (P : LocPlat st arI AR MR) (K : KLayoutP) (Ch : S → Prop) (s : Cfg U64 U64 U64 U64) : Prop :=
  SerExitW P K.toKLayoutV Ch ∧
    ∃ s1 : Cfg U64 U64 U64 U64, (K.vcpus = ∅ ∧ K.ptes = ptesR K s1.mem) ∧ ∀ x, GateW K x → s.mem x = s1.mem x

/-- **`NatEp` on the re-based platform** (gen 55): the native exit is `SerExitC P` for `P : LocPlatC`; `NatEp P` is
`NatEpC P.toC` definitionally. -/
def NatEpC (P : LocPlatC st arI AR MR) (K : KLayoutP) (Ch : S → Prop) (s : Cfg U64 U64 U64 U64) : Prop :=
  SerExitC P K.toKLayoutV Ch ∧
    ∃ s1 : Cfg U64 U64 U64 U64, (K.vcpus = ∅ ∧ K.ptes = ptesR K s1.mem) ∧ ∀ x, GateW K x → s.mem x = s1.mem x

/-- **An `ExecVX` is an `ExecP`**; in a native epoch (`K.vcpus = ∅`) the chain and `ptesR` data hold
(`execP_of_WPRG`'s induction, the VM exit making the invariant vacuous). The start step is abstracted as `hSF`, which
receives the native data only when the epoch is native. -/
theorem execP_of_VX {LP : PathsP ι}
    {SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop}
    (P : LocPlat st arI AR MR)
    (hSF : ∀ (Ch : S → Prop) (K : KLayoutP) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K) c hs q i,
      (K.vcpus = ∅ → NatEp P K Ch s) → SF Ch K s.mem hK hU c hs q i → StartAt (LP i K s.mem hK hU) c hs s.mem q)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} (h0 : Init s0) (hA0 : ArmInv s0)
    (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0) (h : ExecVX LP SF P s0 K0 Ch0 s K Ch) :
    ExecP LP s0 K0 s K ∧ (K.vcpus = ∅ → NatEp P K Ch s) := by
  obtain ⟨hK0, hU0⟩ := okP_R hB hc0
  induction h with
  | refl => exact ⟨.refl, fun _ => ⟨hB, s0, hc0, fun _ _ => rfl⟩⟩
  | @step s1 s1' K1 K1' Ch1 Ch1' c1 _ hS g ih =>
    obtain ⟨hE, hN⟩ := ih
    have hst : Fl4StepP LP s1 K1 c1 s1' K1' := by
      refine ⟨g.arm, fun p0 k W hph hK hU => ?_, fun hs => ?_, fun hn => (g.keep hn).1⟩
      · obtain ⟨i, hi⟩ := g.start p0 k W hph hK hU
        exact ⟨i, hSF _ _ s1 _ _ _ _ _ i hN hi⟩
      · rcases g.ser hs with ⟨hX, hc⟩ | ⟨-, hV⟩
        · have hP := okP_R hX hc
          exact ⟨hP.1, hP.2, g.serG hs⟩
        · exact ⟨hV.1, hV.2, g.serG hs⟩
    refine ⟨.step hE hS hst, fun nv => ?_⟩
    by_cases hs : SerStep s1 c1
    · rcases g.ser hs with ⟨hX, hc⟩ | ⟨hne, -⟩
      · exact ⟨hX, s1', hc, fun _ _ => rfl⟩
      · exact absurd nv hne
    · obtain ⟨eK, eC⟩ := g.keep hs
      subst eK eC
      obtain ⟨hX, e1, hCe, hk1⟩ := hN nv
      obtain ⟨hr, -, -, hM⟩ := exec_safeRunP h0 hA0 hK0 hU0 hM0 hE
      obtain ⟨-, hSI, -⟩ := xsafeRun_greach h0 hA0 hr
      refine ⟨hX, e1, hCe, fun x hx => ?_⟩
      rw [← hk1 x hx]
      exact step_gate_keep hM (allowed_of_sinv hSI c1) hS hs hx
  | @hw s1 K1 Ch1 v a y _ hH ih =>
    obtain ⟨hE, hN⟩ := ih
    obtain ⟨-, hK, -, hM⟩ := exec_safeRunP h0 hA0 hK0 hU0 hM0 hE
    refine ⟨.hw hE hH, fun nv => ?_⟩
    obtain ⟨hX, e1, hCe, hk1⟩ := hN nv
    refine ⟨hX, e1, hCe, fun x hx => ?_⟩
    rw [← hk1 x hx]
    exact hw_gate_keep hK hM hH hx

end exec

/-! ## The tops -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

end top

end
end Fl4Proofs.P2.E2EP
