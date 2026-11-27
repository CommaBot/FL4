/-
# P2 (line unify, gen 1): one family for the W11 slots and the invocation slots — `serializable_fl4_localU1G`

The PJ8–PJ12 chain (jsweep, family `fl4LocW11JA`: the `AFFINITY` agreement in vmF / vmR's `Pre`, `VtTP` in vt's) is
the only family whose vmF / vmR / vt records are satisfiable on ≥ 2 cores. This module moves the other results onto it.

## How the families were reconciled

1. **PTE convention** (the only convention clash between PJ12 and the mapped-frame Delete slot). PJ12's glue
   (`ExecWPJ`) fixes `K.ptes = ptesCanon K m` at every serial exit (the leaves of *some* bundle ghost), invj's
   `delPteSlot` (W11PRID, on pte's `ExecWPR`) needs `K.ptes = ptesR K m` (the reachable leaves of the epoch memory)
   inside its own `Pre` (`PreP.CvP`), so it cannot start under `ptesCanon`. The eight W11 slots use the convention
   only to get `QPs` at their start, which pte's `qPs_of_convR` gives under `ptesR` as well. So U1 is on `ExecWPR`:
   `execP_of_WPRG` (`execP_of_WPRI` generic in family and start fact) and `startAt_cutAR` (`startAt_cutA` with
   `qPs_of_convR`). No slot proof is redone; the eight paths (`fl4LocW11JA`) and `delPteSlot` are used as they are.
2. **YieldBlock** (iolay W14). `StartU` = PJ12's `StartD` with vmF at `VmFEntJ14` (W14's, `hyt` → `yb`; `hyt` back by
   `VmFEntJ14.toJ12` / `VmFEntJ12.toJ10`), vmR at `VmREntU` (`VmREntJ12` with `ry` → `yb`; `ry` by `SlJAtZ.ryB`),
   sl at `SlEntU` (`SlEntJ12` with `SlPreR2.hy0f` / `hy0r` → `yb`; both by `SlJAtZ.yield0LP` at `yb`'s bundle, the
   thread's being a heap TCB read blocked on receive / reply by `slSd` / `lpFault` / `slSu` at the index's bundle).
   `startD_of_U` converts at a state of the current chain (`run` by `chain_run`), then PJ12's own chain
   `startC_of_D` → `startAtV_C` (= `startAt_C` before the cut) → `startAt_cutAR`.
3. **`VcpuLay`** (iolay W16). Already absent: `ExecWPR`'s `serC` (like `ExecWPJ`'s) asks `K'.vcpus = ∅` per serial
   exit, which is W16's `serN` (the glue's layout choice at P3 scope), and `serExitW_ok` is used with
   `vcpuLay_empty`. No `serV` appears.
4. **Invocation slots as summands**: `PathsP.sum (fl4LocW11JA …) LQ`, start facts `StartU1 SFQ` (`StartU` on `.inl`,
   `SFQ` on `.inr`), `serializable_fl4_localU1G` for any `LQ` whose start facts give `StartAt` (`hSFQ`, handed the
   chain and the `ptesR` epoch data, as `execP_of_WPRI`'s). `serializable_fl4_localU1D` instantiates it at
   `delPteSlot` / `DelPteStart`. The CNodeDelete (WI) and Copy / Mint (WIC2) slots are `ownV` paths; they enter an
   `ownP` family only through `cutLiftP`, which needs their PTE avoidance (`AvoidP`), which no line has proved:
   P2/E2EPU1W.lean states the full family with these two as [W] premises (`serializable_fl4_localU1W`). The PageMap
   slot is one more `⊕` summand of `LQ` with its own `SFQ` case.

## Premise table of `serializable_fl4_localU1D` (vs `serializable_fl4_localW11PJ12`)

| where | premise | tag | vs PJ12 |
|---|---|---|---|
| top | `P : LocPlat`, `hIoa : MRKeepIoapic`, `hA` ArchTotal, `hm` MasksWr, `hSt` StoreTotal, `[PlainStore]`, `a0` | [P] | same |
| top | `h0 : Init s0`, `hA0 : ArmInv s0`, `hq : NoLoc s` | — | same |
| top | `hB : SerExitW` (boot), `hM0 : MapsP K0 s0` | [P] | same |
| top | `hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem` | conv. | `ptesCanon` → `ptesR` |
| step | `ExecWPR`: `arm`, `start` (the start fact `StartU1`), `serX`, `serG` | [P] | `ExecWPJ` → `ExecWPR` |
| step | `serC : K'.vcpus = ∅ ∧ K'.ptes = ptesR K' s'.mem` (first half = W16's `serN`), `keep` | conv. | `ptesCanon` → `ptesR` |
| hw | `HwStepP` | [P] | same |
| vmF | record `VmFPremB`: `nv`, `bun`, `kd` | kd [P] | same |
| vmF | entry `VmFEntJ14`: `nv`, `ix`, `hct`, `lk`, `gl`; **`yb`** | [P] ×3; **[J]** | `hyt` [J] → `yb` [J] |
| vmR | record `VmRPremA`: `nv`, `bun`, `cs`, `kd` | [P] ×2 | same |
| vmR | entry `VmREntU`: `ix`, `hct`, `lk`, `nbc`, `fd`; **`yb`** | [P] ×3; **[J]** | `ry` [J] → `yb` [J] |
| io | `IoPremW9` (`nv`, `hQ`, `kd`, `bunS`), `IoEntJ9` (`ix`, `hct`) | [P] ×2 | same |
| st | `StPremW3B` (`nv`, `bun`, `hQ`, `kd`), `StEntJ7` (`ix`, `fd`) | [P] ×2 | same |
| irq | `IrqPremK2B` (`bun`, `lt`, `kd`, `pl`), entry `Ch σ` | [P] ×2 | same |
| vx | `VxPremP3E` (`nv`, `kd`), `VxEntJ8N` (`ix`, `hv`, `buf`) | [P] ×3 | same |
| vt | `VtPremA0` (`nv`, `bun`, `kd`, `Nt`), `VtEntJ8` (pinned, `eu` derived) | [P] ×1 | same |
| sl | record `SlPremP6`: `bun`, `cs`, `kd` | [P] ×2 | same |
| sl | entry `SlEntU`: `ix`, `sg`, `hct`, `el`, `sc`, `nbc`, `acc`, `hlk`; **`yb`** | [P] ×7; **[J]** | `hy0f` / `hy0r` [J] → `yb` [J] |
| delPte | record `DelPtePrem`: `nv`, `bunS`, `lk`; `GlueAt` with `InvQFP` | [P] ×2 | new slot (invj W11PRID) |

Every slot's start is a `GlueAt` [P] at a state of the current chain (`Ch σ`), as in PJ12. **[J]: only `yb`** (W14's
`SlJAtYB` at the start state; one fact, asked at the vmF / vmR / sl starts; iolay gen 6: a kernel invariant not
derivable from `SerExitW` / `Ch σ`). No [W]. PJ12's four `YIELD_TO` [J]s (`hyt`, `ry`, `hy0f`, `hy0r`) are gone.
`serializable_fl4_localU1W` (P2/E2EPU1W.lean) adds the CNodeDelete / Copy-Mint slots (records `InvPremW`: `nv`,
`bunS`, `lk` [P]; `GlueAt` [P] with `InvQF` / `InvQCMW`) and the two [W]s `AvInvW` / `AvCMW`.

## Satisfiability (records constructed, `m := L.mem σ`, no core-count assumption, no ∀-`Pre` field with a fixed `m`)

`startU_vmF_sat` (record from the state + `kd`), `startU_vmR_sat`, `startU_sl_sat`, `startU_vt_sat` (= PJ12's
`startA_vt_sat`), `startU1_delPte_sat` (`delPteStart_sat` assembled into `DelPteStart`); in E2EPU1W
`invStartU_sat` / `cmStartU_sat` (`invStartW_sat` / `cmStartW_sat2`). `yb` is satisfiable at any state with a
bundle whose spec state carries YieldBlock (`slJAtYB_of`; YieldBlock holds at boot and is kept by every kernel exit,
`boot_yieldBlock'`, `kernel_entry_yieldScope2U29`). io / st / irq / vx have no start-level satisfiability lemma in PJ12
either (their records mention no `m`, jsweep gen 4); their start facts are PJ12's, unchanged.

No existing statement or file changed except the root import list.
-/
import Fl4Proofs.P2.E2EPW11J12
import Fl4Proofs.P2.E2EPW11RID
import Fl4Proofs.P2.E2EVFl4W14
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY)
open Fl4Proofs.P2.E2E (StartAt SP SerStep)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg xsafeRun_greach
  allowed_of_sinv)

noncomputable section
open Classical

/-! ## Executions under the reachability convention, generic in the family -/

section exec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {ι : Type}

/-- **An `ExecWPR` is an `ExecP`, with the epoch invariant**, for any family whose start facts give `StartAt`
(`execP_of_WPRI`'s proof with the start step abstracted as `hSF`, as `execP_of_WPJG` does for `ExecWPJ`). -/
theorem execP_of_WPRG {LP : PathsP ι}
    {SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop}
    (hSF : ∀ (Ch : S → Prop) (K : KLayoutP) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K) c hs q i,
      (∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) →
      (∃ s1 : Cfg U64 U64 U64 U64, (K.vcpus = ∅ ∧ K.ptes = ptesR K s1.mem) ∧ ∀ x, GateW K x → s.mem x = s1.mem x) →
      SF Ch K s.mem hK hU c hs q i → StartAt (LP i K s.mem hK hU) c hs s.mem q)
    (P : LocPlat st arI AR MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} (h0 : Init s0) (hA0 : ArmInv s0)
    (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0) (h : ExecWPR LP SF P s0 K0 Ch0 s K Ch) :
    ExecP LP s0 K0 s K ∧ SerExitW P K.toKLayoutV Ch ∧
      ∃ s1 : Cfg U64 U64 U64 U64, (K.vcpus = ∅ ∧ K.ptes = ptesR K s1.mem) ∧ ∀ x, GateW K x → s.mem x = s1.mem x := by
  obtain ⟨hK0, hU0⟩ := okP_R hB hc0
  induction h with
  | refl => exact ⟨.refl, hB, s0, hc0, fun _ _ => rfl⟩
  | @step s1 s1' K1 K1' Ch1 Ch1' c1 _ hS g ih =>
    obtain ⟨hE, hX, e1, hCe, hk1⟩ := ih
    have hst : Fl4StepP LP s1 K1 c1 s1' K1' := by
      refine ⟨g.arm, fun p0 k W hph hK hU => ?_, fun hs => ?_, fun hn => (g.keep hn).1⟩
      · obtain ⟨i, hi⟩ := g.start p0 k W hph hK hU
        exact ⟨i, hSF _ _ s1 _ _ _ _ _ i hX.chainOf ⟨e1, hCe, hk1⟩ hi⟩
      · have hP := okP_R (g.serX hs) (g.serC hs)
        exact ⟨hP.1, hP.2, g.serG hs⟩
    refine ⟨.step hE hS hst, ?_, ?_⟩
    · by_cases hs : SerStep s1 c1
      · exact g.serX hs
      · obtain ⟨e1, e2⟩ := g.keep hs
        rw [e1, e2]; exact hX
    · by_cases hs : SerStep s1 c1
      · exact ⟨s1', g.serC hs, fun _ _ => rfl⟩
      · obtain ⟨eK, -⟩ := g.keep hs
        subst eK
        obtain ⟨hr, -, -, hM⟩ := exec_safeRunP h0 hA0 hK0 hU0 hM0 hE
        obtain ⟨-, hSI, -⟩ := xsafeRun_greach h0 hA0 hr
        refine ⟨e1, hCe, fun x hx => ?_⟩
        rw [← hk1 x hx]
        exact step_gate_keep hM (allowed_of_sinv hSI c1) hS hs hx
  | @hw s1 K1 Ch1 v a y _ hH ih =>
    obtain ⟨hE, hX, e1, hCe, hk1⟩ := ih
    obtain ⟨-, hK, -, hM⟩ := exec_safeRunP h0 hA0 hK0 hU0 hM0 hE
    refine ⟨.hw hE hH, hX, e1, hCe, fun x hx => ?_⟩
    rw [← hk1 x hx]
    exact hw_gate_keep hK hM hH hx

end exec

/-! ## From the `ownV` start to the cut path's start, under `ptesR` -/

section cut
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)

/-- **The cut path's start from the `ownV` path's, the epoch at the reachability convention** (`startAt_cutA` with
`qPs_of_convR` for `qPs_of_conv`; the bundle state is any state of the layout's chain). -/
theorem startAt_cutAR (i : Fl4IxW (S := S)) (K : KLayoutP) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K)
    (hU : UserOKP K) {c : U64} {hs : U64 → Prop} {q0 : SP}
    (hS : StartAt ((fl4LocA st ar hA hm hSt a0).paths (fl4Dflt st ar hm) i K.toKLayoutV s.mem hK.base hU.base)
      c hs s.mem q0)
    (hb : ∃ σe, SlJAt (L := L) K.toKLayout σe)
    (hE : ∃ s1 : Cfg U64 U64 U64 U64, (K.vcpus = ∅ ∧ K.ptes = ptesR K s1.mem) ∧ ∀ x, GateW K x → s.mem x = s1.mem x) :
    StartAt (fl4LocW11JA st ar hA hm hSt a0 i K s.mem hK hU) c hs s.mem
      (cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout s.mem) c q0 ∅) := by
  obtain ⟨s1, ⟨nv, hcv⟩, hk1⟩ := hE
  obtain ⟨σ, a, hP, hc, hl, hμ, e⟩ := hS
  have hk := pre_ksbA st ar hA hm hSt a0 i K s.mem hK hU σ hP
  have hq := qPs_of_convR
    (L' := ((fl4LocA st ar hA hm hSt a0).paths (fl4Dflt st ar hm) i K.toKLayoutV s.mem hK.base hU.base).L)
    hcv nv hb hk1 hk (fun x hx hu => hμ x hx hu)
  refine ⟨σ, a, ⟨hP, hq⟩, hc, hl, hμ, ?_⟩
  show _ = (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx s.mem) _
    (allA st ar hA hm hSt a0 i K s.mem hK hU)).body σ a
  refine Eq.trans ?_ (body_cutLiftP hK hU (fun x hx => ko_pte hK hx s.mem) _
    (allA st ar hA hm hSt a0 i K s.mem hK hU) σ a).symm
  change _ = cutP _ _ _ _
    (((fl4LocA st ar hA hm hSt a0).paths (fl4Dflt st ar hm) i K.toKLayoutV s.mem hK.base hU.base).L.cpu σ)
    (((fl4LocA st ar hA hm hSt a0).paths (fl4Dflt st ar hm) i K.toKLayoutV s.mem hK.base hU.base).body σ a) ∅
  rw [hc, ← e]

end cut

/-! ## vmR's and sl's entry facts with `yb` -/

section ent
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)

/-- **vmR's start entry facts**: `VmREntJ12` (PJ12) with `ry` [J] replaced by `yb` [J] (as W14's `VmREntJ14`). -/
structure VmREntU {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop)
    (MR : A3 → Fl4Spec.MachineState → Prop) (i : VmRArg S) (Kl Kb : OwnMap.KLayout) (s : S) : Prop where
  /-- Index convention, as `VmREntJ12.ix`. -/
  ix : BunIxU (L := L) Kl Kl.heap.tcbs i.Cs i.Ω Kl.heap i.Sg Kl.heap.replies Kl.heap.scs Kl.heap.ntfns
    Kl.heap.scBits i.Ac s
  /-- [P] (`NonIdle`). -/
  hct : NonIdle st arI AR MR s
  /-- [J] a clause-7 bundle at the start state whose spec state carries YieldBlock (W14's `yb`). -/
  yb : SlJAtYB st Kb s
  /-- [P] -/
  lk : i.Locks s i.rptr ∧ i.Locks s i.ep
  /-- [P] fl4-sync's no-neighbour check (`VmNbC`), as `VmREntJ12.nbc`. -/
  nbc : VmNbC st i.rptr s
  /-- fl4-sync's `found` (`VmFoundC`), as `VmREntJ12.fd`. -/
  fd : VmFoundC st i.rptr i.ep s

/-- **sl's start entry facts**: `SlEntJ12` (PJ12) with `SlPreR2.hy0f` / `hy0r` [J] replaced by `yb` [J]. -/
structure SlEntU {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop)
    (MR : A3 → Fl4Spec.MachineState → Prop) (i : SlArg S) (K : KLayout) (s : S) : Prop where
  /-- Index convention, as `SlEntJ12.ix`. -/
  ix : ∃ (A' : Type) (arI' : machine.Arch A') (AR' : A' → Fl4Spec.Cr3 → Prop) (Zx : Fl4Proofs.P3.XSets)
    (Lst : U64 → List U64) (D : Set U64) (a' : A') (σ : Fl4Spec.State Unit),
    SlJAtZ (L := L) arI' AR' Zx i.Cs i.Ac Lst D K s a' σ ∧ i.Ω = OmegaS K Zx (L.ksb s) σ
  /-- Index convention: `Sg = SgS`. -/
  sg : i.Sg = SgS K
  /-- [P] (`NonIdle`). -/
  hct : NonIdle st arI AR MR s
  /-- [P] (`SlEntL`). -/
  el : SlEntL (st := st) K i.Locks i.found s
  /-- [P] (`SlSyncC`). -/
  sc : SlSyncC st i.n i.found s
  /-- [P] fl4-sync's no-neighbour check (`SlNbC`). -/
  nbc : SlNbC st i.n i.found s
  /-- [P] (`SlAccR`). -/
  acc : SlAccR (st := st) ar K i.Locks i.found s
  /-- [P] the endpoint is locked (`SlPreR2.hlk`). -/
  hlk : ¬ SlTrap st s → i.Locks s i.found.2
  /-- [J] a clause-7 bundle at the start state whose spec state carries YieldBlock (W14's `yb`). -/
  yb : SlJAtYB st K s

variable {st ar}

/-- **`VmREntJ12` from `VmREntU`** (`ry` by `SlJAtZ.ryB`). -/
theorem VmREntU.toJ12 (hA : P0.ArchTotal ar) {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop}
    {MR : A3 → Fl4Spec.MachineState → Prop} {i : VmRArg S} {Kl Kb : OwnMap.KLayout} {s : S}
    (E : VmREntU st arI AR MR i Kl Kb s) : VmREntJ12 st ar arI AR MR i Kl s := by
  refine ⟨E.ix, E.hct, ?_, E.lk, E.nbc, E.fd⟩
  obtain ⟨A', arI', AR', Zx, Cx, Ax, Lst, D, a', σ, B, hY⟩ := E.yb
  exact B.ryB hA hY E.fd

/-- **`SlEntJ12` from `SlEntU` and `run`** (`hy0f` / `hy0r` by `SlJAtZ.yield0LP` at the YieldBlock bundle; the
handler / receiver is a heap TCB read blocked on receive / reply by `SlJAtZ.slSd` / `lpFault` / `slSu` at the index's
bundle, as `SlPreBY.toBY`). -/
theorem SlEntU.toJ12 (hA : P0.ArchTotal ar) {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop}
    {MR : A3 → Fl4Spec.MachineState → Prop} {i : SlArg S} {K : KLayout} {s : S}
    (E : SlEntU st ar arI AR MR i K s)
    (hrun : L.mem s (stA (L.curW s)) = sched.TS_RESTART ∨ L.mem s (stA (L.curW s)) = sched.TS_RUNNING) :
    SlEntJ12 st ar arI AR MR i K s := by
  obtain ⟨A', arI', AR', Zx, Lst, D, a', σ, B, -⟩ := E.ix
  obtain ⟨A2, arI2, AR2, Zx2, Cx2, Ax2, Lst2, D2, a2, σ2, B2, hY⟩ := E.yb
  refine ⟨E.ix, E.sg, E.hct, E.el, E.sc, E.nbc, E.acc, ⟨?_, ?_, E.hlk⟩⟩
  · intro hS a X a1 LP ptr badge dest r C
    exact B2.yield0LP hA hY LP (B.slSd hA hrun E.el hS LP C).1 (Or.inl ((B.lpFault hA hrun LP).2 C))
  · intro hS a X a1 LP u usc C
    refine B2.yield0LP hA hY LP (B.slSu (Locks := i.Locks) hA hrun (E.sc.fd.rc hS (E.sc.arm hS)) LP C).1
      (Or.inr ?_)
    obtain ⟨iu, hiu, hiuc⟩ := C.ust
    have hiu' : iu = sched.TS_BLOCKED_ON_REPLY := UScalar.eq_of_val_eq (by simpa using hiuc)
    rw [eq_of_spec_fd (obj.Tcb.state.spec (L := L) X u)] at hiu
    rw [← hiu', ok_inj_ff hiu]

end ent

/-! ## The start fact of the eight W11 slots -/

section start
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st] {A : Type}
  (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop) (MR : A3 → Fl4Spec.MachineState → Prop)

/-- **The start fact of `fl4LocW11JA` with `yb`** [P] (module docstring): `StartD` (PJ12) with vmF at `VmFEntJ14`,
vmR at `VmREntU`, sl at `SlEntU` (each `StartD`'s entry with its `YIELD_TO` [J]s replaced by `yb` [J]). -/
def StartU (Ch : S → Prop) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (q : SP) : Fl4IxW (S := S) → Prop
  | .vmF j => ∃ q0, (∃ _h : VmFPremB st j K.toKLayoutV, ∃ σ : S,
      (Ch σ ∧ VmFEntJ14 st ar arI AR MR j K.toKLayoutV σ) ∧
      ∀ h' : VmFPremA st ar j K.toKLayoutV,
        GlueAt ((vmFSlotA st ar hA hm).liftAt j K.toKLayoutV m hK.base hU.base h') (fun σ' : S => σ' = σ)
          c hs m q0) ∧
      q = cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) c q0 ∅
  | .vmR j => ∃ q0, (∃ h : VmRPremA st j K.toKLayoutV,
      GlueAt ((vmRSlotA st ar hA hm).liftAt j K.toKLayoutV m hK.base hU.base h)
        (fun σ : S => Ch σ ∧ VmREntU st arI AR MR j (userV K.toKLayoutV) K.toKLayout σ) c hs m q0) ∧
      q = cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) c q0 ∅
  | .sl j => ∃ q0, (∃ h : (slSlotP3W6 st ar hA hm hSt a0).Prem j K.toKLayoutV m,
      GlueAt ((slSlotP3W6 st ar hA hm hSt a0).liftAt j K.toKLayoutV m hK.base hU.base h)
        (fun σ : S => Ch σ ∧ SlEntU st ar arI AR MR j K.toKLayoutV.toKLayout σ) c hs m q0) ∧
      q = cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) c q0 ∅
  | i => StartD st ar hA hm hSt a0 arI AR MR Ch K m hK hU c hs q i

variable {arI AR MR}

/-- **`StartU` gives `StartD`** at a state of the current chain (`run` by `chain_run`). -/
theorem startD_of_U (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR) {Ch : S → Prop}
    {K : KLayoutP} (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch)
    {m : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {hs : U64 → Prop} {q : SP}
    {i : Fl4IxW (S := S)} (h : StartU st ar hA hm hSt a0 arI AR MR Ch K m hK hU c hs q i) :
    StartD st ar hA hm hSt a0 arI AR MR Ch K m hK hU c hs q i := by
  obtain ⟨σe, hC'⟩ := hC
  cases i with
  | vmF j =>
    obtain ⟨q0, ⟨h1, σ, ⟨hCσ, hE⟩, hG⟩, e⟩ := h
    exact ⟨q0, ⟨h1, σ, ⟨hCσ, (hE.toJ12 st ar).toJ10 st ar hA (chain_run P hIoa hC' hCσ hE.hct)⟩, hG⟩, e⟩
  | vmR j =>
    obtain ⟨q0, ⟨h1, hG⟩, e⟩ := h
    exact ⟨q0, ⟨h1, hG.mono fun σ he _ => ⟨he.1, he.2.toJ12 hA⟩⟩, e⟩
  | sl j =>
    obtain ⟨q0, ⟨h1, hG⟩, e⟩ := h
    exact ⟨q0, ⟨h1, hG.mono fun σ he _ => ⟨he.1, he.2.toJ12 hA (chain_run P hIoa hC' he.1 he.2.hct)⟩⟩, e⟩
  | io j => exact h
  | st j => exact h
  | irq j => exact h
  | vq j => exact h

/-- **`StartC` gives a start of `fl4LocA`'s `ownV` path** (`startAt_C` stopped before the PTE cut). -/
theorem startAtV_C (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR) {Ch : S → Prop}
    {K : KLayoutP} (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch)
    {m : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {hs : U64 → Prop} {q : SP}
    {i : Fl4IxW (S := S)} (h : StartC st ar hA hm hSt a0 arI AR MR Ch K m hK hU c hs q i) :
    ∃ q0, StartAt ((fl4LocA st ar hA hm hSt a0).paths (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base)
      c hs m q0 ∧
      q = cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) c q0 ∅ := by
  have hC0 := hC
  obtain ⟨σe, hC'⟩ := hC
  cases i with
  | sl j =>
    obtain ⟨q0, ⟨h, hG⟩, e⟩ := h
    refine startAtV_A st ar hA hm hSt a0 P hIoa hC0 (m := m) (hK := hK) (hU := hU) (i := .sl j)
      ⟨q0, ⟨h, hG.mono fun σ he hμ => ⟨he.1, ?_⟩⟩, e⟩
    have hJ := ChainOf.bun hC' σ he.1
    refine he.2.toQ hA (chain_run P hIoa hC' he.1 he.2.hct) fun d hd => ?_
    obtain ⟨h1, h2⟩ := hJ.userOK.tcb d hd oAFFINITY (Or.inl rfl)
    exact (hμ _ h1 h2).symm
  | vmF j =>
    exact startAtV_A st ar hA hm hSt a0 P hIoa hC0 (hK := hK) (hU := hU)
      (startA_of_B st ar hA hm hSt a0 (hK := hK) (hU := hU) (i := .vmF j) h)
  | vmR j =>
    exact startAtV_A st ar hA hm hSt a0 P hIoa hC0 (hK := hK) (hU := hU)
      (startA_of_B st ar hA hm hSt a0 (hK := hK) (hU := hU) (i := .vmR j) h)
  | io j =>
    exact startAtV_A st ar hA hm hSt a0 P hIoa hC0 (hK := hK) (hU := hU)
      (startA_of_B st ar hA hm hSt a0 (hK := hK) (hU := hU) (i := .io j) h)
  | st j =>
    exact startAtV_A st ar hA hm hSt a0 P hIoa hC0 (hK := hK) (hU := hU)
      (startA_of_B st ar hA hm hSt a0 (hK := hK) (hU := hU) (i := .st j) h)
  | irq j =>
    exact startAtV_A st ar hA hm hSt a0 P hIoa hC0 (hK := hK) (hU := hU)
      (startA_of_B st ar hA hm hSt a0 (hK := hK) (hU := hU) (i := .irq j) h)
  | vq j =>
    exact startAtV_A st ar hA hm hSt a0 P hIoa hC0 (hK := hK) (hU := hU)
      (startA_of_B st ar hA hm hSt a0 (hK := hK) (hU := hU) (i := .vq j) h)

/-- **`StartU` gives `StartAt` of `fl4LocW11JA`**, given the current chain and the epoch data of `execP_of_WPRG`. -/
theorem startAt_U (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR) {Ch : S → Prop}
    {K : KLayoutP} {s : Cfg U64 U64 U64 U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {hs : U64 → Prop}
    {q : SP} {i : Fl4IxW (S := S)}
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch)
    (hE : ∃ s1 : Cfg U64 U64 U64 U64, (K.vcpus = ∅ ∧ K.ptes = ptesR K s1.mem) ∧ ∀ x, GateW K x → s.mem x = s1.mem x)
    (h : StartU st ar hA hm hSt a0 arI AR MR Ch K s.mem hK hU c hs q i) :
    StartAt (fl4LocW11JA st ar hA hm hSt a0 i K s.mem hK hU) c hs s.mem q := by
  obtain ⟨q0, hS, rfl⟩ := startAtV_C st ar hA hm hSt a0 P hIoa hC
    (startC_of_D st ar hA hm hSt a0 (startD_of_U st ar hA hm hSt a0 P hIoa hC h))
  obtain ⟨σe, hC'⟩ := hC
  have hσe : Ch σe := by
    obtain ⟨_, _, _, _, _, _, _, _, h'⟩ := hC'
    exact h'
  exact startAt_cutAR st ar hA hm hSt a0 i K s hK hU hS ⟨σe, ChainOf.bun hC' σe hσe⟩ hE

end start

/-! ## The family with invocation summands, and the tops -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop) (MR : A3 → Fl4Spec.MachineState → Prop)

/-- **The start facts of `PathsP.sum (fl4LocW11JA …) LQ`**: `StartU` on the eight W11 slots, `SFQ` on the summands. -/
def StartU1 {κ : Type}
    (SFQ : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → κ → Prop)
    (Ch : S → Prop) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (q : SP) : Fl4IxW (S := S) ⊕ κ → Prop
  | .inl i => StartU st ar hA hm hSt a0 arI AR MR Ch K m hK hU c hs q i
  | .inr j => SFQ Ch K m hK hU c hs q j

variable {arI AR MR}

/-- **FL4 end to end over `fl4LocW11JA` and any family of `ownP` summands** (module docstring): every `ExecWPR`
over `PathsP.sum (fl4LocW11JA …) LQ` whose starts are `StartU1 SFQ` facts ran as some serial order of its completed
entries, provided each summand's start fact gives its `StartAt` (`hSFQ`, given the chain and the epoch data). -/
theorem serializable_fl4_localU1G (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {κ : Type} (LQ : PathsP κ)
    {SFQ : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → κ → Prop}
    (hSFQ : ∀ (Ch : S → Prop) (K : KLayoutP) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K) c hs q j,
      (∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) →
      (∃ s1 : Cfg U64 U64 U64 U64, (K.vcpus = ∅ ∧ K.ptes = ptesR K s1.mem) ∧ ∀ x, GateW K x → s.mem x = s1.mem x) →
      SFQ Ch K s.mem hK hU c hs q j → StartAt (LQ j K s.mem hK hU) c hs s.mem q)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} (h0 : Init s0) (hA0 : ArmInv s0)
    (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPR (PathsP.sum (fl4LocW11JA st ar hA hm hSt a0) LQ) (StartU1 st ar hA hm hSt a0 arI AR MR SFQ) P
      s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  obtain ⟨hK0, hU0⟩ := okP_R hB hc0
  refine serializable_e2eP _ h0 hA0 hK0 hU0 hM0 (execP_of_WPRG ?_ P h0 hA0 hB hc0 hM0 h).1 hq
  intro Ch K s hK hU c hs q i hC hE hsf
  cases i with
  | inl i => exact startAt_U st ar hA hm hSt a0 P hIoa hC hE hsf
  | inr j => exact hSFQ Ch K s hK hU c hs q j hC hE hsf

end top

/-! ## Satisfiability at a chain state, any number of cores -/

section sat
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st] {A : Type}
  (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **vmF's `StartU` holds at every chain state with vmF's entry facts** (record `VmFPremB` built from the state,
`kd` [P]; `m := L.mem σ`). -/
theorem startU_vmF_sat (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR) {Ch : S → Prop}
    {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K)
    {σe σ : S} (hC : ChainOf (L := L) arI AR MR σe K.toKLayoutV.toKLayout Ch) (hσ : Ch σ)
    {j : VmFArg S} (hE : VmFEntJ14 st ar arI AR MR j K.toKLayoutV σ)
    (kd : ∀ s, KernDetS (L := L) (userV K.toKLayoutV).user j.Locks s) (a : A) :
    ∃ q, StartU st ar hA hm hSt a0 arI AR MR Ch K (L.mem σ) hK hU (L.cpu σ) (j.Locks σ) q (.vmF j) := by
  have hE10 := (hE.toJ12 st ar).toJ10 st ar hA (chain_run P hIoa hC hσ hE.hct)
  have h : VmFPremB st j K.toKLayoutV := ⟨hE.nv, ⟨σ, ChainOf.bun hC σ hσ⟩, kd⟩
  exact ⟨_, ((vmFSlotA st ar hA hm).liftAt j K.toKLayoutV (L.mem σ) hK.base hU.base (h.toA hA hE10)).body σ a,
    ⟨h, σ, ⟨hσ, hE⟩, fun _ => ⟨σ, a, rfl, rfl, rfl, fun _ _ _ => rfl, rfl⟩⟩, rfl⟩

/-- **vmR's `StartU` holds at every chain state with vmR's entry facts**, given the [P]s `cs` / `kd` and
`K.vcpus = ∅` (as `startD_vmR_sat`). -/
theorem startU_vmR_sat {Ch : S → Prop} {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K)
    {σe σ : S} (hC : ChainOf (L := L) arI AR MR σe K.toKLayoutV.toKLayout Ch) (hσ : Ch σ) (nv : K.vcpus = ∅)
    {j : VmRArg S} (hE : VmREntU st arI AR MR j (userV K.toKLayoutV) K.toKLayout σ) (cs : ∀ c ∈ j.Cs, c.val < 64)
    (kd : ∀ s : S, SlJAt (L := L) (userV K.toKLayoutV) s → KernDetAt (L := L) (userV K.toKLayoutV) j.Locks s)
    (a : A) :
    ∃ q, StartU st ar hA hm hSt a0 arI AR MR Ch K (L.mem σ) hK hU (L.cpu σ) (j.Locks σ) q (.vmR j) := by
  have h : VmRPremA st j K.toKLayoutV :=
    ⟨nv, ⟨σ, by rw [userV_empty nv]; exact ChainOf.bun hC σ hσ⟩, cs, kd⟩
  exact ⟨_, _, ⟨h, σ, a, ⟨hσ, hE⟩, rfl, rfl, fun _ _ _ => rfl, rfl⟩, rfl⟩

omit [Fl4Proofs.P1.PlainStore st] in
/-- **sl's `StartU` holds at every chain state with sl's entry facts**, given the record (as `startD_sl_sat`). -/
theorem startU_sl_sat {Ch : S → Prop} {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K) {σ : S} (hσ : Ch σ)
    {j : SlArg S} (h : (slSlotP3W6 st ar hA hm hSt a0).Prem j K.toKLayoutV (L.mem σ))
    (hE : SlEntU st ar arI AR MR j K.toKLayoutV.toKLayout σ) (a : A) :
    ∃ q, StartU st ar hA hm hSt a0 arI AR MR Ch K (L.mem σ) hK hU (L.cpu σ) (j.Locks σ) q (.sl j) :=
  ⟨_, _, ⟨h, σ, a, ⟨hσ, hE⟩, rfl, rfl, fun _ _ _ => rfl, rfl⟩, rfl⟩

/-- **vt's `StartU` is PJ12's** (`StartA`'s vt case): `startA_vt_sat` applies unchanged. -/
theorem startU_vt_sat {Ch : S → Prop} {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K)
    {σe σ : S} (hC : ChainOf (L := L) arI AR MR σe K.toKLayoutV.toKLayout Ch) (hσ : Ch σ)
    {j : VtArg S} (hE : VtEntJ8 st j K.toKLayoutV σ) (kd : ∀ s, KernDetS (L := L) (userV K.toKLayoutV).user j.lk s)
    (Nt : ∀ q ∈ j.Nt, j.H q = some .ntfn) (a : A) :
    ∃ q, StartU st ar hA hm hSt a0 arI AR MR Ch K (L.mem σ) hK hU (L.cpu σ) (j.lk σ) q (.vq (.inr j)) :=
  startA_vt_sat st ar hA hm hSt a0 hK hU hC hσ hE kd Nt a

/-- **The mapped-frame Delete slot's start fact holds at every chain state planning such a Delete**
(`delPteStart_sat`'s record and entry, assembled into `DelPteStart` at `m := L.mem s`, core `L.cpu s`, locks
`j.Locks s`). -/
theorem startU1_delPte_sat (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR) {σe : S}
    {K : KLayoutP} {Ch : S → Prop} (hC : ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (nv : K.vcpus = ∅)
    (hK : RegionOKP K) (hU : UserOKP K)
    {s : S} (hs : Ch s) (hct : NonIdle st arI AR MR s) {n : I64} {p : localinv.Plan}
    (hp : localinv.plan st s n = ok (some p))
    (hlbl : ∀ t info, sched.cur_thread st s = ok t → msg.msg_info st s t = ok info →
      info.label = fl4_abi.label.CNodeDelete)
    (hmap : ∀ cp cr cg cgb dest, obj.Slot.cap st p.slot s = ok (.CNode cp cr cg cgb) →
      cspace.lookup_target_slot st s (.CNode cp cr cg cgb) (L.mem s (regA (L.curW s) layout.reg.R10))
        (L.mem s (regA (L.curW s) layout.reg.R8)) = ok (.Ok dest) →
      ∃ fp rt asid va e, obj.Slot.cap st dest s = ok (.Frame fp .Small rt false true false asid va) ∧
        asid ≠ 0#u64 ∧ localinv.small_page_entry st s asid va = ok (some e) ∧ e ≠ 0#u64)
    {m1 : U64 → U64} (hc : K.ptes = ptesR K m1) (hag : GateAg st K m1 s) (a : A) :
    ∃ Ac : Set U64, ∀ j : InvArg S, j.Cs = {c : U64 | c.val < K.ncores} → j.Ω = K.heap.omega →
      j.Sg = K.heap.frame → j.Ac = Ac → j.p = p → j.Locks = planLocks p →
      ∃ q, StartU1 st ar hA hm hSt a0 arI AR MR (DelPteStart st ar hA hm) Ch K (L.mem s) hK hU (L.cpu s)
        (j.Locks s) q (.inr j) := by
  obtain ⟨Ac, H⟩ := delPteStart_sat st P hIoa hC nv hs hct hp hlbl hmap hc hag
  refine ⟨Ac, fun j e1 e2 e3 e4 e5 e6 => ?_⟩
  obtain ⟨h, -, hQ, -⟩ := H j e1 e2 e3 e4 e5 e6
  exact ⟨_, h, s, a, ⟨hs, hQ⟩, rfl, rfl, fun _ _ _ => rfl, rfl⟩

end sat

end
end Fl4Proofs.P2.E2EP
