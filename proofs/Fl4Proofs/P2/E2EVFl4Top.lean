/-
P2 (integration int/j16): **`serializable_fl4_localP3W`, the best end-to-end instance on the tree** (wiring only;
new definitions, no existing statement changed).

One family `fl4LocP3W` combining the merged lines' newest slots. Two theorems over it:
`serializable_fl4_localP3WV` (`ExecV` form, `serializable_fl4_localW2`'s statement, by `serializable_fl4_localG`) and
the top **`serializable_fl4_localP3W`** in famw gen 2's glue form (`ExecW` with start fact `StartP3W`, as
`serializable_fl4_localW3`): `Fl4StepV.ser` [J] and `start` [P] are derived (`execV_of_W`, `startAt_P3W`) from the
named glue premises `SerExitW` [P], `ExitGhostV` [P], `VcpuLay` [J] (vacuous at `K'.vcpus = ∅`: `vcpuLay_empty`) and
per start `GlueAt` [P] with the slot's record; the boot layout's `RegionOKV` / `UserOKV` come from `SerExitW` and
`K0.vcpus = ∅` (`serExitW_ok`, `vcpuLay_empty`), and the `SlJAt` part of every bundle-based `Pre` (now also vmR's
`VmRRPreJ`, via `userV_empty`) is clause 7 of `loc_chain_all`.

* **P3 scope** (vlift gen 8): every slot that used `VFacts` [J] asks `K.vcpus = ∅` instead (`SlotU.ofP3` /
  `SlotC.ofP3`, `VFacts.ofEmpty`); with it `userV K = K.toKLayout` (`userV_empty`) and no VM-layout [J] is left.
  `K.vcpus = ∅` is the glue's layout choice (`Fl4StepV.ser` picks `K'`), consistent with P3 (no VCPU object at a
  `JAtZ` state is bound: `JAtZ.curVcpu0`).
* **io / st / irq** (famw gen 1): `ioSlotW2` / `stSlotW2` / `irqSlotW2` (their `ro` [W] proved at `userV K`, io's `uf`
  split into `qf` [J] + `kd` [P]) under `ofP3`: records `IoPremW2B` / `StPremK2B` / `IrqPremK2B` = famw's minus `vf`
  (+ `bun`, the start state: no premise).
* **vmR** (hpzg gen 5 + slhuf gen 6): `vmRSlotP3` at `rr_localPathJK2` (= hpzg's `rr_localPathJG2` route with the
  lock half of `hufR` from kernel words) at `userV K`, `hpz` = `rr_isProg` / `rr_noZero` / **`rr_hroJ`** (hpzg's
  `ReadOnce` walk), `hufR` by `vm_hufRK` from `cs` [P] + `kd` [P], `IoLayA` from the bundle (`SlJAt.ioLayA`),
  `NoVcpuRW` from `K.vcpus = ∅` (`noVcpuRW_empty`). Left: `mA` [J], `cs` [P], `kd` [P].
* **sl** (slhuf gen 5/6 via vlift): `slSlotP3` (`sl_pathsKC5`).
* **vx** (hpzg gen 5): `vxSlotP3` at **`vexit_localPathPG2`** (IsProg, NoZero, ReadOnce all discharged; `VcpuNU`
  from `K.vcpus = ∅`), `hlk` (lvm gen 10: aligned) by **`hlk_of_kernelDetU`** from `kd` [P].
* **vt** (lvm gen 10 + hpzg gen 5): `vtSlotP3` at **`vtimer_localPathF`** (the whole fire case proved), its
  `IsProg` / `NoZero` from hpzg's `vtimer_isProg` / `vtimer_noZero`, `hlk` by `hlk_of_kernelDetU` from `kd` [P].
  hpzg's `vtimer_localPathG2` (`ReadOnce` discharged) does **not** compose with F: `vtimer_hro` needs the fire case
  and the declines on the user-free guard `guard (VexitRSU …)` (`hFU` / `hDU` [W]), F proves them on
  `guard (VexitRS …)` (`vtimer_acc_fwk_own`, `vtimer_dec_own`). Re-instantiating lvm's generic `vtimer_accG_fwk` /
  `vtimer_accG_fnw` / `vtimer_decG` at `R := VexitRSU` needs `∉ K.user` for every word the fire tail reads
  (`fire_rdG`'s `hR` only gives `region ≠ .none`, and no lemma turns that into `∉ K.user`): a line task, not wiring.
  F removes `F` / `Fm` [W] (2 [W]) for 5 layout / glue facts ([J] `OL`, `UB`, `SL`, `pSg`, [P] `PL`); G2 would
  remove `ro` [W] but add `hFU` / `hFm` / `hDU` [W] (3 [W]) and `hTU` [J]. So F + hpzg's `IsProg` / `NoZero`.
* **vmF**: `vmFSlot` (already `vm_localPathG2`) unchanged.

**The VM paths are vacuous at P3 scope** (vlift gen 7/8): at every P3 state no thread is bound to a VCPU
(`JAtZ.curVcpu0`, `vOf_zero`), so `local_vm_exit` / `local_vm_timer_irq` / VM fault / VM ReplyRecv cannot accept
there, and with `K.vcpus = ∅` the hardware writes nothing. Their slots are kept with their newest paths (the
premise shape a VT-x extension inherits), not voided.

## Premise table of `serializable_fl4_localP3W` (per slot record)

Execution-level ([P] glue, as `serializable_fl4_localW3`): `Init`, `ArmInv`, boot `SerExitW` [P] + `K0.vcpus = ∅` +
`MapsV`, `LocPlat` (P3's platform premises, tagged there), per step `arm` [P], `SerExitW` [P], `VcpuLay` [J] (vacuous
at `K'.vcpus = ∅`), `ExitGhostV` [P], per start `GlueAt` [P] with the entry facts below, `HwStepV` [P].
Start entry facts (beside `GlueAt`): vmF its `Pre` [J]; vmR `VmRRPreJ` minus `SlJAt` (`VmRPre`, `RdTab` [J],
`VmFoundC` [P]); io / st `Q` [J]; irq none; sl `SlQ`; vx `VxEntJ`; vt `VtEntJ` (as `StartW2`).

| slot | [J] | [P] | [W] |
|---|---|---|---|
| all route-U/C slots | `K.vcpus = ∅` (glue's layout choice) | — | — |
| vmF (`VmFPrem`) | `lay`, `mA`, `uf` | — | — |
| vmR (`VmRPremP3`) | `mA` | `cs` (cores < 64), `kd` (`KernDetAt` at bundle states) | — |
| io (`IoPremW2B`) | `pe`, `mA`, `qf` | `kd` (`KernDetS (userV K).user`) | — |
| st (`StPremK2B`) | `pe`, `eu`, `nu`, `uf` | `kd` | — |
| irq (`IrqPremK2B`) | — | `kd`, `pl` (`PlanLk`) | — |
| sl (`SlPremB`) | — | `cs`, `kd` (`KernDetAt`) | `ro` |
| vx (`VxPremP3`) | `eu` | `kd` | — |
| vt (`VtPremP3`) | `eu`, `M`, `OL`, `UB`, `SL`, `pSg` | `kd`, `PL` | `ro` |

(`irq.lt`, `vt.Nt` are facts of the arguments; `bun` fields are the start state, no premise.)

## Diff vs `serializable_fl4_localW`

| slot | removed | added |
|---|---|---|
| io | `vf` [J] (6 VM-layout facts), `ro` [W], `uf` [J] (Q + locks + sets) | `K.vcpus = ∅`; `qf` [J] (Q only), `kd` [P] |
| st | `vf` [J], `ro` [W] | `K.vcpus = ∅` |
| irq | `vf` [J], `ro` [W] | `K.vcpus = ∅` |
| sl | `vf` [J] | `K.vcpus = ∅` |
| vmR | `lay` [J], `uf` [J], `pz` ([P] IsProg, [W] NoZero, [W] ReadOnce) | `K.vcpus = ∅`, `cs` [P], `kd` [P] (`mA` restated over `VmRRPreJ`) |
| vx | `pz` ([P] IsProg, [W] NoZero, [W] ReadOnce), `lk` [P] (unaligned) | `K.vcpus = ∅`, `kd` [P] |
| vt | `pz`'s [P] IsProg / [W] NoZero, `F` / `Fm` [W], `lk` [P] | `kd` [P], `OL` / `UB` / `SL` / `pSg` [J], `PL` [P] |

Net: −10 [W] (`ro` of io/st/irq, `NoZero` / `ReadOnce` of vmR and vx, `NoZero` of vt, `F` / `Fm` of vt), −3 [P]
`IsProg` (vmR/vx/vt), the unaligned `lk` [P] of vx/vt turned into kernel-word `kd` [P], −4 `VFacts` [J] (24 facts) and
vmR's `lay` / `uf` [J]. Remaining [W]: sl `ro`, vt `ro` (2, vs 12 in `serializable_fl4_localW`). With the `ExecW`
form, also `RegionOKV K0` / `UserOKV K0` [J] and the opaque `Fl4StepV.ser` [J] / `start` [P] are replaced by the
named glue premises (as `serializable_fl4_localW3`).

The `Pre`s change for vmR (`VmRRPreJ`: `SlJAt` + `VmRPre` at the layout's heap sets + `RdTab` + `VmFoundC`, the
start obligation of `rr_localPathJ`); the others are the old slots' `Pre`s.
-/
import Fl4Proofs.P2.E2EVFl4W3
import Fl4Proofs.P2.E2EVFl4P3
import Fl4Proofs.P2.RrOnce
import Fl4Proofs.P2.LvmOnce
import Fl4Proofs.P2.AccessLvmTv
import Fl4Proofs.P2.SlJLk2
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EV
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
open Fl4Proofs.P2.OwnMap (fld oAFFINITY region TcbSlot)
open Fl4Proofs.P2.E2E (StartAt SP)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll)

noncomputable section
open Classical

/-! ## No VCPU: generic facts -/

section empty
variable {K : KLayoutV}

/-- **Any path at `userV K` touches no VCPU data word when there is no VCPU.** -/
theorem noVcpuRW_empty (nv : K.vcpus = ∅) {m : U64 → U64}
    (P : E2E.LocalPath (OwnMap.own (userV K)) (OwnMap.cls (userV K)) (OwnMap.ko (userV K) m) (· ∈ (userV K).user)) :
    NoVcpuRW K P :=
  ⟨fun _ _ _ _ => Or.inl (not_vData_empty nv), fun _ _ _ _ => Or.inl (not_vData_empty nv)⟩

/-- **`VcpuNU` with no VCPU.** -/
theorem vcpuNU_empty (nv : K.vcpus = ∅) : VcpuNU K := fun _ _ hv => absurd hv (not_inVcpu_empty nv)

end empty

section fam
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)

/-! ## VM ReplyRecv at P3 scope: `rr_localPathJK2` with hpzg's `ReadOnce` -/

/-- **VM ReplyRecv's premises at P3 scope** (module docstring). -/
structure VmRPremP3 (i : VmRArg S) (K : KLayoutV) (m : U64 → U64) : Prop where
  /-- No VCPU in the layout (the glue's choice at P3 scope). -/
  nv : K.vcpus = ∅
  /-- Some bundle state of the layout (no premise: the start state, whose `Pre` `VmRRPreJ` contains `SlJAt`). -/
  bun : ∃ σ : S, SlJAt (L := L) (userV K) σ
  /-- [P] the glue's core set is below 64 (P3's sets: `SlJAt.hCs`). -/
  cs : ∀ c ∈ i.Cs, c.val < 64
  /-- [P] at bundle states the locks are determined by kernel words. -/
  kd : ∀ s : S, SlJAt (L := L) (userV K) s → KernDetAt (L := L) (userV K) i.Locks s
  /-- [J] `ko`'s memory agrees on TCB affinity words. -/
  mA : ∀ s, VmRRPreJ st ar (userV K) (userV K).heap.tcbs i.Cs i.Ω i.Sg (userV K).heap.scs (userV K).heap.ntfns
      (userV K).heap.scBits i.Ac i.Locks i.rptr i.ep s →
    ∀ d, (userV K).heap d = some .tcb → m (fld d OwnMap.oAFFINITY) = L.mem s (fld d OwnMap.oAFFINITY)

variable (hA : P0.ArchTotal ar) (hSt : P0.StoreTotal st) (hm : E2E.MasksWr st) (a0 : A)

/-- **VM ReplyRecv slot at P3 scope** (`rr_localPathJK2`, `ReadOnce` by `rr_hroJ`). -/
def vmRSlotP3 : SlotU (VmRArg S) where
  Prem i K m := VmRPremP3 st ar i K m
  path i _ m hK hU h :=
    rr_localPathJK2 (Cs := i.Cs) (Ω := i.Ω) (Sg := i.Sg) (Ac := i.Ac) (Locks := i.Locks) (m0 := m)
      ar hA (regionOK_userV hK) (userOK_userV hK hU) h.bun.choose_spec.ioLayA (rptr := i.rptr) (ep := i.ep) hm
      h.cs h.kd h.mA ⟨_, rr_isProg S i.rptr i.ep, rr_noZero i.rptr i.ep, rr_hroJ hA⟩
  W _ _ _ _ _ h := noVcpuRW_empty h.nv _

/-! ## io / st / irq: famw's records without `VFacts` -/

/-- **I/O port's premises without `VFacts`** (`IoPremW2` minus `vf`). -/
structure IoPremW2B (i : IoArg S) (K : KLayoutV) (m : U64 → U64) : Prop where
  /-- `IoPre` at bundle states ([J] P1 facts, fl4-sync contract). -/
  pe : ∀ s, SlJAt (L := L) K.toKLayout s → i.Q K m s →
    IoPre st K.toKLayout K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits i.Ac s
  /-- [J] -/
  mA : ∀ s, SlJAt (L := L) K.toKLayout s → i.Q K m s → ∀ d, K.heap d = some .tcb →
    m (fld d oAFFINITY) = L.mem s (fld d oAFFINITY)
  /-- [J] the caller's `Q` survives an aligned write of a `userV K` user word at a bundle state. -/
  qf : ∀ s b v, SlJAt (L := L) K.toKLayout s → i.Q K m s → b ∈ (userV K).user → Aligned b → i.Q K m (L.wr s b v)
  /-- [P] at bundle states the locks are determined by the words off `(userV K).user`. -/
  kd : ∀ s, SlJAt (L := L) K.toKLayout s → KernDetS (L := L) (userV K).user i.Locks s
  /-- Some bundle state of the layout (no premise: the start state). -/
  bun : ∃ σ : S, SlJAt (L := L) K.toKLayout σ

theorem IoPremW2B.toW2 {i : IoArg S} {K : KLayoutV} {m : U64 → U64} (vf : VFacts L K) (h : IoPremW2B st i K m) :
    IoPremW2 st i K m :=
  ⟨vf, h.pe, h.mA, h.qf, h.kd, h.bun⟩

/-- **`TCB_SetTimer`'s premises without `VFacts`** (`StPremK2` minus `vf`, plus `bun`). -/
structure StPremK2B (i : StArg S) (K : KLayoutV) (m : U64 → U64) : Prop where
  /-- Some bundle state of the layout (no premise: the start state, `Pre` = `SlJAt K ∧ Q`). -/
  bun : ∃ σ : S, SlJAt (L := L) K.toKLayout σ
  /-- [J] `StEntK` at bundle states. -/
  pe : ∀ s, SlJAt (L := L) K.toKLayout s → i.Q K m s →
    StEntK K.toKLayout st K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits i.Ac
      i.target m s
  /-- [J] -/
  eu : ∀ s b v, StEnt (userV K) st K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns
      K.heap.scBits i.Ac i.target s → b ∈ (userV K).user → Aligned b →
    StEnt (userV K) st K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits i.Ac
      i.target (L.wr s b v)
  /-- [P] the locks are determined by the core, the kernel base and the aligned words off `(userV K).user`. -/
  kd : ∀ s, KernDetS (L := L) (userV K).user i.lk s
  /-- [J] -/
  nu : ∀ s, StEnt (userV K) st K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns
      K.heap.scBits i.Ac i.target s → ∀ o : U64, o.val < 4288 → L.nodeAt s (L.cpu s) o ∉ (userV K).user
  /-- [J] -/
  uf : ∀ s b v, SlJAt (L := L) K.toKLayout s → i.Q K m s → b ∈ (userV K).user → Aligned b → i.Q K m (L.wr s b v)

theorem StPremK2B.toW2 {i : StArg S} {K : KLayoutV} {m : U64 → U64} (vf : VFacts L K) (h : StPremK2B st i K m) :
    StPremK2 st i K m :=
  ⟨vf, h.pe, h.eu, h.kd, h.nu, h.uf⟩

/-- **The timer interrupt's premises without `VFacts`** (`IrqPremK2` minus `vf`, plus `bun`). -/
structure IrqPremK2B (i : IrqArg S) (K : KLayoutV) (m : U64 → U64) : Prop where
  /-- Some bundle state of the layout (no premise: the start state, whose `IrqPreV` includes `SlJAt K`). -/
  bun : ∃ σ : S, SlJAt (L := L) K.toKLayout σ
  /-- The IRQ's state word lies in the kernel-state block (the timer IRQ is 2). -/
  lt : i.irq.val < 128
  /-- [P] at bundle states the locks are determined by the words off `(userV K).user`. -/
  kd : ∀ s, SlJAt (L := L) K.toKLayout s → KernDetS (L := L) (userV K).user i.lk s
  /-- [P] -/
  pl : PlanLk i.lk i.pl

theorem IrqPremK2B.toW2 {i : IrqArg S} {K : KLayoutV} {m : U64 → U64} (vf : VFacts L K)
    (h : IrqPremK2B st i K m) : IrqPremK2 st i K m :=
  ⟨vf, h.lt, h.kd, h.pl⟩

/-- I/O port slot at P3 scope (famw's `ioSlotW2`). -/
def ioSlotP3W : SlotU (IoArg S) :=
  (ioSlotW2 st ar hA hm).ofP3 L (IoPremW2B st) (fun h => h.bun) (fun vf h => IoPremW2B.toW2 st vf h)

/-- `TCB_SetTimer` slot at P3 scope (famw's `stSlotW2`). -/
def stSlotP3W : SlotU (StArg S) :=
  (stSlotW2 st ar hA hm).ofP3 L (StPremK2B st) (fun h => h.bun) (fun vf h => StPremK2B.toW2 st vf h)

/-- Timer interrupt slot at P3 scope (famw's `irqSlotW2`). -/
def irqSlotP3W : SlotU (IrqArg S) :=
  (irqSlotW2 st ar hA hm).ofP3 L (IrqPremK2B st) (fun h => h.bun) (fun vf h => IrqPremK2B.toW2 st vf h)

/-! ## lvm's two paths at their newest forms -/

/-- **`local_vm_exit`'s premises for `vexit_localPathPG2`** (module docstring). -/
structure VxPremP3 (i : VxArg S) (K : KLayoutV) (m : U64 → U64) : Prop where
  /-- No VCPU in the layout (the glue's choice at P3 scope; gives `VcpuNU`). -/
  nv : K.vcpus = ∅
  /-- [J] the entry facts kept by aligned user writes. -/
  eu : ∀ s b v', VxPre st i K m s → b ∈ K.user → Aligned b → VxPre st i K m (L.wr s b v')
  /-- [P] the locks are determined by the core, the kernel base and the aligned words off `(userV K).user`. -/
  kd : ∀ s, KernDetS (L := L) (userV K).user i.lk s

/-- **`local_vm_exit` slot at `vexit_localPathPG2`** (IsProg / NoZero / ReadOnce discharged). -/
def vxSlotP3 : SlotN (VxArg S) where
  Prem i K m := VxPremP3 st i K m
  path i _ m hK hU h :=
    vexit_localPathPG2 (T := i.T) (Cs := i.Cs) (Ω := i.Ω) (Sg := i.Sg) (Rp := i.Rp) (Scs := i.Scs) (Nt := i.Nt)
      (Ac := i.Ac) (H := i.H) (Z := i.Z) (lk := i.lk) (v := i.v) (n := i.n) (m := m) ar hA hK hU hm
      (vcpuNU_empty h.nv) h.eu
      (fun s b v' hb hba => hlk_of_kernelDetU (P := fun _ => True) (fun s _ => h.kd s) s b v' trivial
        (mem_userV.2 (Or.inl hb)) hba)

/-- **`local_vm_timer_irq`'s premises for `vtimer_localPathF`** (module docstring). -/
structure VtPremP3 (i : VtArg S) (K : KLayoutV) (m : U64 → U64) : Prop where
  /-- [W] `ReadOnce` of the generated tree. -/
  ro : E2E.ReadOnce st ar (R.localvm.handle_vm_timer_irq_local i.irq i.pl i.n) (OwnMap.cls K.toKLayout)
    (OwnMap.ko K.toKLayout m) (· ∈ K.user) (VtPre st i K) (VexitRS K st i.lk)
  /-- [J] -/
  eu : ∀ s b v', VtPre st i K s → b ∈ K.user → Aligned b → VtPre st i K (L.wr s b v')
  /-- [P] the locks are determined by the core, the kernel base and the aligned words off `(userV K).user`. -/
  kd : ∀ s, KernDetS (L := L) (userV K).user i.lk s
  /-- P1's notifications typed in the heap. -/
  Nt : ∀ q ∈ i.Nt, i.H q = some .ntfn
  /-- [J] the map memory agrees with the entry on every thread's `AFFINITY`. -/
  M : ∀ s, VtPre st i K s → ∀ y ∈ i.T, m (fld y oAFFINITY) = L.mem s (affA y)
  /-- [J] endpoints and replies lie in their object regions. -/
  OL : ObjLay K.toKLayout i.H i.Rp
  /-- [P] the glue holds the plan's notification / endpoint / reply locks. -/
  PL : PlanLk i.lk i.pl
  /-- [J] some user-word set with P1 `UserOK` holding every TCB's IPC-buffer lookup. -/
  UB : ∀ s, VtPre st i K s → ∃ U : Set U64, Fl4Proofs.P1.UserOK st i.T i.Cs i.Ω i.H U s ∧
    ∀ y ∈ i.T, msg.lookup_ipc_buffer st s true y ⦃ b => BufOK U b ⦄
  /-- [J] the VSpace slot words of this core's threads lie in TCB slot regions. -/
  SL : ∀ s, VtPre st i K s → SlotLayV K.toKLayout st i.T s
  /-- [J] the bound VCPU's `PENDING` is no frame word. -/
  pSg : ∀ s, VtPre st i K s → core.num.U64.wrapping_add (vOf st s) vcpu.PENDING ∉ i.Sg

/-- **`local_vm_timer_irq` slot at `vtimer_localPathF`** (fire case proved; `IsProg` / `NoZero` from hpzg). -/
def vtSlotP3 : SlotN (VtArg S) where
  Prem i K m := VtPremP3 st ar i K m
  path i K m hK hU h :=
    vtimer_localPathF (T := i.T) (Cs := i.Cs) (Ω := i.Ω) (Sg := i.Sg) (Rp := i.Rp) (Scs := i.Scs) (Nt := i.Nt)
      (Ac := i.Ac) (H := i.H) (Z := i.Z) (lk := i.lk) (irq := i.irq) (n := i.n) (pl := i.pl) (m := m) ar hA hK hU
      (vtimer_isProg S i.irq i.pl i.n) (vtimer_noZero i.irq i.pl i.n) hm h.ro h.eu
      (fun s b v' hb hba => hlk_of_kernelDetU (P := fun _ => True) (fun s _ => h.kd s) s b v' trivial
        (mem_userV.2 (Or.inl hb)) hba)
      h.Nt h.M h.OL h.PL h.UB h.SL h.pSg

/-- lvm's paths at their newest forms. -/
def fl4LQP3 (D : Dflt) : PathsV (VxArg S ⊕ VtArg S) :=
  PathsV.sum ((vxSlotP3 st ar hA hm).fam D) ((vtSlotP3 st ar hA hm).fam D)

/-! ## The family and the theorem -/

/-- **FL4's eight local paths, newest slots at P3 scope** (module docstring). -/
def fl4LocP3W : Fl4Loc (VmFArg S) (VmRArg S) (IoArg S) (StArg S) (IrqArg S) (SlArg S) (VxArg S ⊕ VtArg S) where
  vmF := vmFSlot st ar hA hm
  vmR := vmRSlotP3 st ar hA hm
  io := ioSlotP3W st ar hA hm
  st := stSlotP3W st ar hA hm
  irq := irqSlotP3W st ar hA hm
  sl := slSlotP3 st ar hA hSt hm a0
  vq := fl4LQP3 st ar hA hm (fl4Dflt st ar hm)

/-- **`fl4LocP3W` over `ExecV`** (the `Fl4StepV.ser` [J] / `start` [P] form, as `serializable_fl4_localW2`). -/
theorem serializable_fl4_localP3WV {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutV}
    (h0 : Init s0) (hA0 : ArmInv s0) (hK0 : RegionOKV K0) (hU0 : UserOKV K0) (hM0 : MapsV K0 s0)
    (h : ExecV ((fl4LocP3W st ar hA hSt hm a0).paths (fl4Dflt st ar hm)) s0 K0 s K) (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_fl4_localG _ _ h0 hA0 hK0 hU0 hM0 h hq

/-! ## The start fact of `fl4LocP3W` (famw gen 2's `GlueAt` form) -/

/-- **The start fact of `fl4LocP3W`** (module docstring): per index, the slot's record and `GlueAt` [P] of the slot's
path with the entry facts beside `Ch σ` (clause 7 gives the bundle). vmF as in `StartW2` (its `Pre`); vmR: `VmRRPreJ`
without its `SlJAt` conjunct; io / st / irq / sl / vx / vt: `StartW2`'s entry facts. -/
def StartP3W (Ch : S → Prop) (K : KLayoutV) (m : U64 → U64) (hK : RegionOKV K) (hU : UserOKV K) (c : U64)
    (hs : U64 → Prop) (q : SP) : Fl4IxW (S := S) → Prop
  | .vmF j => ∃ h : VmFPrem st ar j K m, GlueAt ((vmFSlot st ar hA hm).liftAt j K m hK hU h)
      ((vmFSlot st ar hA hm).path j K m hK hU h).Pre c hs m q
  | .vmR j => ∃ h : VmRPremP3 st ar j K m, GlueAt ((vmRSlotP3 st ar hA hm).liftAt j K m hK hU h)
      (fun σ : S => Ch σ ∧
        ((userV K).heap j.ep = some .ep → VmRPre st ar (userV K) (userV K).heap.tcbs j.Cs j.Ω (userV K).heap j.Sg
          (Heap.replies (userV K).heap) (userV K).heap.scs (userV K).heap.ntfns (userV K).heap.scBits j.Ac j.Locks σ
          j.rptr j.ep) ∧
        RdTab (L := L) (IoRS (st := st) (userV K) j.Locks σ) σ ∧ VmFoundC st j.rptr j.ep σ) c hs m q
  | .io j => ∃ h : (ioSlotP3W st ar hA hm).Prem j K m, GlueAt ((ioSlotP3W st ar hA hm).liftAt j K m hK hU h)
      (fun σ : S => Ch σ ∧ j.Q K m σ) c hs m q
  | .st j => ∃ h : (stSlotP3W st ar hA hm).Prem j K m, GlueAt ((stSlotP3W st ar hA hm).liftAt j K m hK hU h)
      (fun σ : S => Ch σ ∧ j.Q K m σ) c hs m q
  | .irq j => ∃ h : (irqSlotP3W st ar hA hm).Prem j K m, GlueAt ((irqSlotP3W st ar hA hm).liftAt j K m hK hU h)
      (fun σ : S => Ch σ) c hs m q
  | .sl j => ∃ h : (slSlotP3 st ar hA hSt hm a0).Prem j K m,
      GlueAt ((slSlotP3 st ar hA hSt hm a0).liftAt j K m hK hU h)
      (fun σ : S => Ch σ ∧ Fl4Proofs.P2.PathObl.SlQ st ar j.Locks j.n j.found j.Cs j.Ω j.Sg j.Ac K.toKLayout m σ) c hs m q
  | .vq (.inl j) => ∃ h : VxPremP3 st j K m, GlueAt ((vxSlotP3 st ar hA hm).path j K m hK hU h)
      (fun σ : S => Ch σ ∧ VxEntJ st j K m σ) c hs m q
  | .vq (.inr j) => ∃ h : VtPremP3 st ar j K m, GlueAt ((vtSlotP3 st ar hA hm).path j K m hK hU h)
      (fun σ : S => Ch σ ∧ VtEntJ st j K σ) c hs m q

/-- **`StartAt` of `fl4LocP3W`'s family from the start fact**, given clause 7 on the chain. -/
theorem startAt_P3W {Ch : S → Prop} {K : KLayoutV} (hCh : ∀ σ, Ch σ → SlJAt (L := L) K.toKLayout σ)
    {m : U64 → U64} {hK : RegionOKV K} {hU : UserOKV K} {c : U64} {hs : U64 → Prop} {q : SP}
    {i : Fl4IxW (S := S)} (h : StartP3W st ar hA hSt hm a0 Ch K m hK hU c hs q i) :
    StartAt ((fl4LocP3W st ar hA hSt hm a0).paths (fl4Dflt st ar hm) i K m hK hU) c hs m q := by
  cases i with
  | vmF j =>
    obtain ⟨h, hG⟩ := h
    show StartAt ((vmFSlot st ar hA hm).lift (fl4Dflt st ar hm) j K m hK hU) c hs m q
    rw [SlotU.lift_eq _ _ h]
    exact hG.startAt fun σ he _ => he
  | vmR j =>
    obtain ⟨h, hG⟩ := h
    show StartAt ((vmRSlotP3 st ar hA hm).lift (fl4Dflt st ar hm) j K m hK hU) c hs m q
    rw [SlotU.lift_eq _ _ h]
    refine hG.startAt fun σ he _ => ⟨?_, he.2⟩
    rw [userV_empty h.nv]
    exact hCh σ he.1
  | io j =>
    obtain ⟨h, hG⟩ := h
    show StartAt ((ioSlotP3W st ar hA hm).lift (fl4Dflt st ar hm) j K m hK hU) c hs m q
    rw [SlotU.lift_eq _ _ h]
    exact hG.startAt fun σ he _ => ⟨hCh σ he.1, he.2⟩
  | st j =>
    obtain ⟨h, hG⟩ := h
    show StartAt ((stSlotP3W st ar hA hm).lift (fl4Dflt st ar hm) j K m hK hU) c hs m q
    rw [SlotU.lift_eq _ _ h]
    exact hG.startAt fun σ he _ => ⟨hCh σ he.1, he.2⟩
  | irq j =>
    obtain ⟨h, hG⟩ := h
    show StartAt ((irqSlotP3W st ar hA hm).lift (fl4Dflt st ar hm) j K m hK hU) c hs m q
    rw [SlotU.lift_eq _ _ h]
    exact hG.startAt fun σ he hμ =>
      ⟨hCh σ he, fun x hx hxu => hμ x hx fun hu => hxu (mem_userV.2 (Or.inl hu))⟩
  | sl j =>
    obtain ⟨h, hG⟩ := h
    show StartAt ((slSlotP3 st ar hA hSt hm a0).lift (fl4Dflt st ar hm) j K m hK hU) c hs m q
    rw [SlotC.lift_eq _ _ h]
    exact hG.startAt fun σ he _ => ⟨hCh σ he.1, he.2⟩
  | vq j =>
    cases j with
    | inl j =>
      obtain ⟨h, hG⟩ := h
      show StartAt ((vxSlotP3 st ar hA hm).fam (fl4Dflt st ar hm) j K m hK hU) c hs m q
      rw [SlotN.fam_pos _ _ h]
      exact hG.startAt fun σ he _ => he.2.pre st (hCh σ he.1)
    | inr j =>
      obtain ⟨h, hG⟩ := h
      show StartAt ((vtSlotP3 st ar hA hm).fam (fl4Dflt st ar hm) j K m hK hU) c hs m q
      rw [SlotN.fam_pos _ _ h]
      exact hG.startAt fun σ he _ => he.2.pre st (hCh σ he.1)

end fam

/-! ## The top theorem (glue premises named) -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hSt : P0.StoreTotal st) (hm : E2E.MasksWr st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **FL4 end to end with rule 7 over its eight local paths: the newest slots at P3 scope, glue premises named**
(module docstring: premise table and diff vs `serializable_fl4_localW`): every execution `ExecW` of FL4 (famw gen 2:
`Fl4StepV.ser` / `start` derived from `SerExitW` [P], `VcpuLay` [J], `ExitGhostV` [P] and per start `GlueAt` [P]
with the slot record) whose starts are `StartP3W` facts of `fl4LocP3W`'s paths, from a boot layout with no VCPU, at a
state with no local path in progress, ran exactly as some serial order of its completed entries. The VM paths are
vacuous at this scope (no thread is bound to a VCPU at a P3 state). -/
theorem serializable_fl4_localP3W (P : LocPlat st arI AR MR) {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutV}
    {Ch0 Ch : S → Prop} (h0 : Init s0) (hA0 : ArmInv s0) (hB : SerExitW P K0 Ch0) (nv0 : K0.vcpus = ∅)
    (hM0 : MapsV K0 s0)
    (h : ExecW ((fl4LocP3W st ar hA hSt hm a0).paths (fl4Dflt st ar hm)) (StartP3W st ar hA hSt hm a0) P s0 K0 Ch0
      s K Ch) (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  have hE := (execV_of_W (fun _ _ _ _ _ _ _ _ _ hCh hi => startAt_P3W st ar hA hSt hm a0 hCh hi) hB h).1
  have hok := serExitW_ok hB (vcpuLay_empty nv0)
  exact serializable_fl4_localP3WV st ar hA hSt hm a0 h0 hA0 hok.1 hok.2 hM0 hE hq

end top

end
end Fl4Proofs.P2.E2EV
