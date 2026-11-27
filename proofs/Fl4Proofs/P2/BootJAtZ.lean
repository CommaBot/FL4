/-
# P2 (line p3mc, gen 35): **`JAtZ` at the boot, a P3 start, and the joint model of `P` / `hIoa` / `hB`**

Assembles gen 34's and gen 35's field lemmas (`P2/BootZCheap` … `P2/BootLiveF`):

* **`jAtZ_B`**: P3's `JAtZ archT ART (ZB G0) HB CsB AcB LstB DB sB σB.machineState σB`, every field proved at the
  concrete store state `sB` (`P2/BootMem`) and the relocated spec boot state `σB` (`P2/BootSpec`); `jAt_B` (`JAt`).
* **`jReach_B`**: `JReachU17 archT ART modelMR sB σB.machineState σB`, by `JReachU3.start` (`VxE (ZB G0)`,
  `SInvX σB` = P3's `boot_sinvX` ported, `SInvIP σB`, `modelMR_refl`, `UtPgR σB`) with `GpmOutV`, `IdleVtS`,
  `DevRangeS` at `σB`.
* **`serExitW_B`**: for every `OpaqueH`, `SerExitW (locPlat_archT O bs_ext) K Ch` at the layout / chain `chainC`
  picks at that start (`KB O`, `ChB O`; `vcpus = ptes = ∅`).
* **`joint_B`** (the joint satisfiability of E2EPV12's top premises `P`, `hIoa`, `hB`): under `OpaqueH` (gen 32's
  eight facts about the spec's `opaque` constants), with the concrete store `bst` (`StoreExt` by `bs_ext`) and the
  model arch `archT` / `ART` / `modelMR`: `∃ P : LocPlat bst archT ART modelMR, MRKeepIoapic archT modelMR ∧
  ∃ K0 Ch0, ∀ e, SerExitW P K0.toKLayoutV (Ch0 e)`. So `serializable_fl4_localV12`'s `P`, `hIoa`, `hB` are jointly
  satisfiable, non-vacuously (a real `JReachU17` state, `MR` inhabited), given `OpaqueH`.

The other premises of the top (`h0 : Init s0`, `hA0`, `hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem`, `hM0`, the
execution `h`) are about the initial configuration `s0` of the serial machine and are not addressed here: `KB O` has
`vcpus = ∅` (as `hc0` asks) and `ptes = ∅` (`hc0`'s `ptesR K0 s0.mem` then asks `s0` to map no leaf PTE word).

No premise beyond `OpaqueH` (gen 32, unchanged). No existing statement changed except the root import list.
-/
import Fl4Proofs.P2.BootLiveF
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.BootSt
open fl4_core Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P1 Classical
open Fl4Proofs.P2.PathObl Fl4Proofs.P2.E2EV Fl4Proofs.P2.OwnMapP Fl4Proofs.P2.OwnMapV

noncomputable section

/-- **`JAtZ` at the boot.** -/
theorem jAtZ_B : JAtZ (L := bsL) LocPlatM.archT LocPlatM.ART (ZB G0) HB CsB AcB LstB DB sB
    (σB (Z := Unit)).machineState (σB (Z := Unit)) where
  xtop := xtop_B (AR := LocPlatM.ART) trivial
  call := ZB_call G0
  rfree := ZB_rfree G0
  rrecv := ZB_rrecv G0
  yld := ZB_yld G0
  mcp := ZB_mcp G0
  buf := ZB_buf G0
  ks := ZB_ks G0
  thT := ZB_thT G0
  thk := ZB_thk G0
  ip := ZB_ip G0
  rp := rp_B
  apart := apart_B
  nk := ZB_nk G0
  nodeB := ZB_nodeB G0
  jpl := ⟨_, _, jpl_B⟩
  cover := ZB_cover
  obj := ZB_obj G0
  zH := ZB_zH G0
  sfree := sfree_B
  hset := ZB_hset G0
  hscC := ZB_hscC G0
  jcov := jcov_B
  kern := jKern_boot
  del := delInv_B
  ut := utInv_B
  bound := delBound_B
  finM := finM_B
  utc := utc_B
  nsc := ZB_nsc G0
  inv := σB_inv
  cur := σB_cur
  own := σB_own G0
  off := σB_off
  act := σB_act
  c0 := ZB_c0 G0
  bsa := σB_bsa
  sv := σB_sv
  isorted := σB_isorted
  slink := σB_slink
  curRun := σB_curRun
  blk := blk_B
  intL := ZB_intL G0
  vsc := ZB_vsc G0
  bok := σB_bok
  fcov := ZB_fcov G0
  fcap := ZB_fcap G0
  ext := ZB_ext G0
  live := live_B
  zD := zD_B
  carry := carry_B

/-- **`JAt` at the boot.** -/
theorem jAt_B : JAt (L := bsL) LocPlatM.archT LocPlatM.ART sB (σB (Z := Unit)).machineState (σB (Z := Unit)) :=
  ⟨ZB G0, HB, CsB, AcB, LstB, DB, jAtZ_B, inferInstance⟩

/-- **A P3 start at the boot** (`JReachU17` by `JReachU3.start`). -/
theorem jReach_B : SInvR.G5.JReachU17 (L := bsL) LocPlatM.archT LocPlatM.ART modelMR sB
    (σB (Z := Unit)).machineState (σB (Z := Unit)) :=
  ⟨.start jAtZ_B inferInstance SInvR.G4.boot_sinvX_B sInvIP_B (LocPlatM.modelMR_refl _) utPgR_B,
    SInvGp.boot_gpmOut_B, SInvIV.boot_idleVtS_B, devRangeS_B⟩

/-- The layout `chainC` picks at the boot start, as a `KLayoutP` (no VCPU, no PTE word). -/
def KB (O : LocPlatM.OpaqueH) : KLayoutP :=
  { toKLayoutV := { toKLayout := (chainC (LocPlatM.locPlat_archT O bs_ext) jReach_B).1, vcpus := ∅ }, ptes := ∅ }

/-- The chain `chainC` picks at the boot start. -/
def ChB (O : LocPlatM.OpaqueH) : BS → Prop := (chainC (LocPlatM.locPlat_archT O bs_ext) jReach_B).2

/-- **`hB` at the boot layout**: `SerExitW` at `KB O`, `ChB O`. -/
theorem serExitW_B (O : LocPlatM.OpaqueH) :
    SerExitW (LocPlatM.locPlat_archT O bs_ext) (KB O).toKLayoutV (ChB O) :=
  ⟨sB, _, _, jReach_B, rfl⟩

/-- **The joint satisfiability of `P`, `hIoa`, `hB`** (module docstring), under `OpaqueH`. -/
theorem joint_B (O : LocPlatM.OpaqueH) :
    ∃ P : LocPlat bst LocPlatM.archT LocPlatM.ART modelMR, MRKeepIoapic LocPlatM.archT modelMR ∧
      ∃ (K0 : KLayoutP) (Ch0 : U64 → BS → Prop), ∀ e, SerExitW P K0.toKLayoutV (Ch0 e) :=
  ⟨LocPlatM.locPlat_archT O bs_ext, LocPlatM.mrKeepIoapic_archT, KB O, fun _ => ChB O, fun _ => serExitW_B O⟩

end

end Fl4Proofs.P2.BootSt
