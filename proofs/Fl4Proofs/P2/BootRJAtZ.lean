/-
# P2 (line p3mc, gen 39): **`JAtZ` and a P3 start at the second boot start `(sR, σR)`** — a reachable state
whose current thread is not the idle thread

Assembles gen 39's field lemmas (P2/BootRZ … P2/BootRLiveF, units A–F):

* **`jAtZ_R`**: P3's `JAtZ archT ART ZR HR CsB AcR LstB DB sR σR.machineState σR`, every field proved at the
  concrete store state `sR` (P2/BootRMem) and the spec state `σR` (P2/BootRSpec: `σB` with the running root thread
  `tRp` current, bound to the root SC `scRp`, its CSpace-root slot holding `threadCap tRp` and its timeout-handler
  slot `schedContextCap scRp 0`); `jAt_R`.
* **`jReach_R`**: `JReachU17 archT ART modelMR sR σR.machineState σR` by `JReachU3.start` (`sinvX_R`, unit A;
  `sInvIP_R`, `utPgR_R`, `modelMR_refl`) with `gpmOut_R`, `idleVtS_R`, `devRangeS_R`.
* **`jReach_R_cur`**: at that P3 state the current thread is not the idle thread (`σR_cur_ne`) — the first P3
  start of this line with `NonIdle`'s conclusion, and `nonIdle_R` (P2/BootRNonIdle) says every `JReachU17` at `sR`
  has it.
* `KR O` / `ChR O` (`chainC`'s layout / chain at that start, `vcpus = ptes = ∅`), **`serExitW_R`** (`SerExitW` at
  them), `chR_sR`, `slJAt_sR`, **`ybw_R`** (V13's `ybw` [J] at `sR` and `KR O`: the TCBs' `YIELD_TO` words are 0),
  **`nonIdle_R_chain`** (`NonIdle` at `sR`, the chain state the vmF / sl entry records would name);
* **`vmFEnt_R`**: V13's vmF entry record `VmFEntV13` (with `ybw` [J] and `NonIdle` [P] proved, not assumed) at a
  concrete index whose lock set satisfies `LkC`, at the chain state `sR` of the chain `ChR O`. What `StartV13`'s
  vmF clause asks beyond the record (`VmFPremB` and the `GlueAt` of the lifted VM-fault body at `sR`) is not
  proved here.

No premise beyond `OpaqueH` (gen 32, only where `locPlat_archT` is used). No existing statement changed except the
root import list.
-/
import Fl4Proofs.P2.BootRSInv
import Fl4Proofs.P2.BootRMdbF
import Fl4Proofs.P2.BootRJpl
import Fl4Proofs.P2.BootRSpecF
import Fl4Proofs.P2.BootRRelF
import Fl4Proofs.P2.BootRFinF
import Fl4Proofs.P2.BootRLiveF
import Fl4Proofs.P2.BootRNonIdle
import Fl4Proofs.P2.BootStart
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.BootSt
open fl4_core Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P1 Classical
open Fl4Proofs.P2.PathObl Fl4Proofs.P2.E2EV Fl4Proofs.P2.OwnMapP Fl4Proofs.P2.OwnMapV Fl4Proofs.P2.E2EP

noncomputable section

/-- **`JAtZ` at the second boot start.** -/
theorem jAtZ_R : JAtZ (L := bsL) LocPlatM.archT LocPlatM.ART ZR HR CsB AcR LstB DB sR
    (σR (Z := Unit)).machineState (σR (Z := Unit)) where
  xtop := xtop_R_of (AR := LocPlatM.ART) trivial relTopB_R
  call := ZR_call
  rfree := ZR_rfree
  rrecv := ZR_rrecv
  yld := ZR_yld
  mcp := ZR_mcp
  buf := ZR_buf
  ks := ZR_ks
  thT := ZR_thT
  thk := ZR_thk
  ip := ZR_ip
  rp := rp_R
  apart := apart_R
  nk := ZR_nk
  nodeB := ZR_nodeB
  jpl := ⟨_, _, jpl_R⟩
  cover := ZR_cover
  obj := ZR_obj
  zH := ZR_zH
  sfree := sfree_R
  hset := ZR_hset
  hscC := ZR_hscC
  jcov := jcov_R
  kern := jKern_R
  del := delInv_R
  ut := utInv_R
  bound := delBound_R
  finM := finM_R
  utc := utc_R
  nsc := ZR_nsc
  inv := σR_inv
  cur := σR_curInv
  own := σR_own
  off := σR_off
  act := σR_act
  c0 := ZR_c0
  bsa := σR_bsa
  sv := σR_sv
  isorted := σR_isorted
  slink := σR_slink
  curRun := σR_curRun
  blk := blk_R
  intL := ZR_intL
  vsc := ZR_vsc
  bok := σR_bok
  fcov := ZR_fcov
  fcap := ZR_fcap
  ext := ZR_ext
  live := live_R
  zD := zD_R
  carry := carry_R

/-- **`JAt` at the second boot start.** -/
theorem jAt_R : JAt (L := bsL) LocPlatM.archT LocPlatM.ART sR (σR (Z := Unit)).machineState (σR (Z := Unit)) :=
  ⟨ZR, HR, CsB, AcR, LstB, DB, jAtZ_R, inferInstance⟩

/-- **A P3 start at the second boot start** (`JReachU17` by `JReachU3.start`). -/
theorem jReach_R : SInvR.G5.JReachU17 (L := bsL) LocPlatM.archT LocPlatM.ART modelMR sR
    (σR (Z := Unit)).machineState (σR (Z := Unit)) :=
  ⟨.start jAtZ_R inferInstance sinvX_R sInvIP_R (LocPlatM.modelMR_refl _) utPgR_R, gpmOut_R, idleVtS_R,
    devRangeS_R⟩

/-- **The current thread of that P3 start is not the idle thread.** -/
theorem jReach_R_cur : (σR (Z := Unit)).curThread ≠ (σR (Z := Unit)).idleThread := σR_cur_ne

/-- The layout `chainC` picks at the second boot start (no VCPU, no PTE word). -/
def KR (O : LocPlatM.OpaqueH) : KLayoutP :=
  { toKLayoutV := { toKLayout := (chainC (LocPlatM.locPlat_archT O bs_ext) jReach_R).1, vcpus := ∅ }, ptes := ∅ }

/-- The chain `chainC` picks at the second boot start. -/
def ChR (O : LocPlatM.OpaqueH) : BS → Prop := (chainC (LocPlatM.locPlat_archT O bs_ext) jReach_R).2

/-- **`hB` at the second boot start's layout**: `SerExitW` at `KR O`, `ChR O`. -/
theorem serExitW_R (O : LocPlatM.OpaqueH) :
    SerExitW (LocPlatM.locPlat_archT O bs_ext) (KR O).toKLayoutV (ChR O) :=
  ⟨sR, _, _, jReach_R, rfl⟩

theorem chR_spec (O : LocPlatM.OpaqueH) :
    ChainOf (L := bsL) LocPlatM.archT LocPlatM.ART modelMR sR (KR O).toKLayout (ChR O) :=
  chainC_spec (LocPlatM.locPlat_archT O bs_ext) jReach_R

/-- **The second boot state is on its chain.** -/
theorem chR_sR (O : LocPlatM.OpaqueH) : ChR O sR := by
  obtain ⟨Z, H, Cx, nc, -, -, -, -, h⟩ := chR_spec O
  exact h

theorem chR_lay (O : LocPlatM.OpaqueH) : ChainLay (L := bsL) (KR O).toKLayout (ChR O) := by
  obtain ⟨Z, H, Cx, nc, -, -, -, h, -⟩ := chR_spec O
  exact h

/-- **The second boot state is a bundle state of its layout.** -/
theorem slJAt_sR (O : LocPlatM.OpaqueH) : SlJAt (L := bsL) (KR O).toKLayout sR :=
  (chR_lay O).bun sR (chR_sR O)

/-- **`NonIdle` at the chain state `sR`** (the `σ` a vmF / sl entry record names), for the tops' instance. -/
theorem nonIdle_R_chain (O : LocPlatM.OpaqueH) :
    ChR O sR ∧ NonIdle bst LocPlatM.archT LocPlatM.ART modelMR sR :=
  ⟨chR_sR O, nonIdle_R⟩

/-- **`ybw` holds at the second boot state** (no TCB's `YIELD_TO` word is nonzero in `memR`). -/
theorem ybw_R (O : LocPlatM.OpaqueH) : YBW bst (KR O).toKLayout sR := by
  intro t ht h0
  exfalso
  apply h0
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := slJAt_sR O
  have hT : t ∈ Zx.T := by rw [B.j.tcbs_eq.1]; exact ht
  obtain ⟨Q, R0, hcq, -⟩ := B.j.xtop.fin.1.1.1.lists
  have hta : TcbAddr t := hcq.tcbs t hT
  have hv : (yieldA t).val = t.val + 3472 := Notif.tfield_val hta (by decide)
  have := hta.align
  rw [memR_at hv (by omega)]
  exact wordR_zero_of (by omega)


/-- **V13's vmF entry record at a concrete index** at the chain state `sR` (`VmFEntV13`, the record carrying
`ybw` [J] and `NonIdle` [P]): fault `addr = code = 0`, P1's sets of the layout `KR O` (`bunIxV_of` at the bundle
`slJAt_sR`), every address locked (`LkC` holds: one lock set for every state). `nv` (no VCPU), `ix`, `hct`
(`nonIdle_R`), `lk`, `ybw` (`ybw_R`), `gl` all proved. -/
theorem vmFEnt_R (O : LocPlatM.OpaqueH) {A : Type} (ar : machine.Arch A) :
    ∃ i : VmFArg BS, LkC i.Locks ∧ ChR O sR ∧
      VmFEntV13 bst ar LocPlatM.archT LocPlatM.ART modelMR i (KR O).toKLayoutV sR := by
  obtain ⟨Cs, Ac, Ω, U, hB⟩ := bunIxV_of (slJAt_sR O)
  refine ⟨⟨0#u64, 0#u64, (KR O).toKLayout.heap.tcbs, Cs, Ω, U, (KR O).toKLayout.heap.frame,
    (KR O).toKLayout.heap.replies, (KR O).toKLayout.heap.scs, (KR O).toKLayout.heap.ntfns, Ac,
    (KR O).toKLayout.heap, (KR O).toKLayout.heap.scBits, fun _ _ => True⟩, ⟨fun _ => True, rfl⟩, chR_sR O, ?_⟩
  exact
    { nv := rfl
      ix := hB
      hct := nonIdle_R
      lk := fun _ _ _ _ _ _ _ _ _ => ⟨trivial, trivial⟩
      ybw := ybw_R O
      gl := fun _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial }

end

end Fl4Proofs.P2.BootSt
