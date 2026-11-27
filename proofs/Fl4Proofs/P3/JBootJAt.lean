/-
P3 (line jboot, gen 3): **a concrete `JAtZ` / `JAt` / `JReachU17` state** — P3's joint invariant and its reachable
set are non-vacuous.

At P2's word store `wst` (WitPlat) with the model arch `warI`, `wAR = True`, `wMR = modelMR`:
* the FL4 state `w0` (JBootMem: the kernel-state block at `fkb`, core 0's node, the idle TCB and the idle SC),
* the spec state `fInitASt` (JBootSt: l4v's `init_A_st` with the IRQ node laid out for FL4),
* the ghosts of JBootZ: `Zw` (typed heap `thW`, MDB ghost `Gw`, `T = {idle TCB}`, `C = {idle SC}`, other sets
  empty, core 0, `vx = ∅`), P1's heap `Hw`, cores `Csw = {0}`, active SCs `C0`, call stacks `fun _ => []`, dead set
  `Dw`,

meet every field of `JAtZ` (**`jAtZ_w0`**, for every arch state `a`), hence **`jAt_w0`** (`JAt`), and with
`a := fInitASt.machineState` the start rule of `JReachU3` and `JReachU17`'s three spec facts: **`jReachU17_w0`**.

The fields come from JBootSched / JBootMem / JBootChar (gen 2) and JBootZ, JBootCs, JBootInv, JBootLay, JBootBlk,
JBootLive (gen 3). No sorry; no premises. New module; no existing statement changed.
-/
import Fl4Proofs.P3.JBootCs
import Fl4Proofs.P3.JBootInv
import Fl4Proofs.P3.JBootLay
import Fl4Proofs.P3.JBootBlk
import Fl4Proofs.P3.JBootLive
import Fl4Proofs.P3.XTopJointKEntryU17
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.JBoot
open fl4_core Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit

noncomputable section

/-- **The joint invariant at the witness** (module docstring). -/
theorem jAtZ_w0 (a : MachineState) :
    JAtZ (L := wL) warI wAR Zw Hw Csw C0 (fun _ => []) Dw w0 a fInitASt where
  xtop :=
    { fin := ⟨⟨w0_othersRel a, w0_topPlaced⟩, w0_vsRel, w0_ptRel, w0_poolsIn, w0_curOK⟩
      rel := ⟨placed_thW, w0_crel, w0_finInv, w0_domRel, w0_mdbOKV, w0_ipcApart, w0_scApart⟩
      ipc := w0_ipc
      esa := w0_esa }
  call := w0_call
  rfree := w0_rfree
  rrecv := w0_rrecv
  yld := w0_yld
  mcp := w0_mcp
  buf := w0_buf
  ks := w0_ks
  thT := thT_thW
  thk := thk_thW
  ip := w0_ip
  rp := w0_rp
  apart := w0_apart
  nk := w0_nk
  nodeB := w0_nodeB
  jpl := w0_jpl
  cover := w0_cover
  obj := fInit_obj
  zH := w0_zH
  sfree := w0_sfree
  hset := w0_hset
  hscC := w0_hscC
  jcov := w0_jcov
  kern := w0_jkern
  del := w0_delInv
  ut := w0_utInv
  bound := w0_delBound
  finM := w0_finM
  utc := w0_utc
  nsc := fInit_nsc
  inv := fInit_inv
  cur := Or.inr fInit_curInv
  own := fInit_own
  off := fInit_off
  act := fInit_act
  c0 := w0_c0
  bsa := fInit_bsa
  sv := fInit_sv
  isorted := fInit_isorted
  slink := fInit_slink
  curRun := fInit_curRun
  blk := w0_blk
  intL := intL_thW
  vsc := w0_vsc
  bok := w0_bok
  fcov := w0_fcov
  fcap := w0_fcap
  ext := w0_ext
  live := w0_live
  zD := w0_zD
  carry := w0_carry

/-- **`JAt` at the witness.** -/
theorem jAt_w0 (a : MachineState) : JAt (L := wL) warI wAR w0 a fInitASt :=
  ⟨Zw, Hw, Csw, C0, fun _ => [], Dw, jAtZ_w0 a, Zw_vx⟩

/-- **`modelMR` relates the spec's machine state to itself.** -/
theorem fInit_mr : wMR fInitASt.machineState fInitASt.machineState := ⟨rfl, rfl, rfl, rfl⟩

/-- **The witness starts `JReachU3`** (its `start` rule). -/
theorem jReachU3_w0 : SInvR.G5.JReachU3 (L := wL) warI wAR wMR w0 fInitASt.machineState fInitASt :=
  .start (jAtZ_w0 _) Zw_vx fInit_sinvX fInit_sinvIP fInit_mr fInit_utPgR

/-- **`JReachU17` at the witness**: the reachable joint states of `kernel_entry_reachU17V` are non-empty. -/
theorem jReachU17_w0 : SInvR.G5.JReachU17 (L := wL) warI wAR wMR w0 fInitASt.machineState fInitASt :=
  ⟨jReachU3_w0, fInit_gpmOut, fInit_idleVtS, fInit_devRangeS⟩

end

end Fl4Proofs.P3.JBoot
