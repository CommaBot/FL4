/-
P2 (line famw, gen 3): **the start entry facts of `serializable_fl4_localP3W` shrunk** (new definitions only; no
existing statement changes, no `kernel_entry_reach*` touched).

Same family `fl4LocP3W` (int/j16), same `ExecW` glue form; only the per-start fact changes: `StartP3W4` (this file)
implies `StartP3W` (`startP3W_of_W4`), so **`serializable_fl4_localW4`** is `serializable_fl4_localP3W` with
`StartP3W4` starts.

## 1. The bundle at the index's sets (`SlJAtS`, `BunIx`)

The P1 parts of every entry fact (`BXI`, `StLay`, the `EntryInv` fields `csc` / `hcsc`, `kb`, `nc`, the heap typing of
`T` / `Scs` / `Nt` / `Rp`, `ScAff`, notification regions) are P3 facts at a bundle state (`JAtZ.bxi`,
`JAtZ.entryInv`, `SlJAtZ.stLay`, `irqLayK_of_slJAt`, `XInv.core_eq`), **at the bundle's own sets**: `T` / `Ω` / `Sg` /
`Rp` / `Scs` / `Nt` / `Z` the layout heap's, `Cs` / `Ac` the `JAtZ` ghosts. An index (`VmFArg`, `IoArg`, ...) carries
its sets as free fields, so the start fact asks that they are those:
* `SlJAtS K Cs Ac s` = `SlJAt K s` with its core / active-SC ghosts named (`SlJAtS.slJAt`); **`slJAtS_of`**: every
  `SlJAt K s` (clause 7 at a chain state) is `SlJAtS K {c | c < ncores} Ac s` for some `Ac`.
* **`BunIx K T Cs Ω H Sg Rp Scs Nt Z Ac s`** (index convention, the glue's choice of the index at the start state,
  as the untagged `hKH` / `hTs` / `hΩ` / `hSg` conventions already were): `H = K.heap`, `T` / `Ω` / `Sg` / `Rp` /
  `Scs` / `Nt` / `Z` the heap's sets, and `SlJAtS K Cs Ac s`. **`bunIx_of`**: at every bundle state some index sets
  satisfy it (so it is a choice, not a fact about the state). Derived from it: `BunIx.bxi`, `.stLay`, `.entryInv`,
  `.aff`, `.ntw`, `.kb`, `.nc`, `.tcbT`, `.scsK`, `.scsT`, `.ntT`, `fld_aff_nu`.

## 2. The start entry facts (`StartP3W4` vs `StartP3W`)

* **vmF** (`VmFEntJ`): was the path's `Pre` `VmPre (userV K) …` [J]. Now `BunIx` + `nv` (`K.vcpus = ∅`, the glue's
  layout choice as everywhere at P3 scope; `vmPre_userV_empty`) + `VmBaseR` [J] (`run`, `curAff`, `cscCore`, `tmc`,
  `VmLay`) + `VmFPre`'s `hyp` [J], `lk` [P], `hyt` [J] + `VmGlue` [P] + `RdTab` [J]. Derived: `VmBase.bxi` / `csc` /
  `hcsc` / `kb` / `nc` / `hT` / `hSc` / `affSc`, `VmFPre.hEp` / `hRp`, the `userV` lift.
* **vmR** (`VmREntJ`): was `(ep typed → VmRPre) ∧ RdTab ∧ VmFoundC`. Now `BunIx` + `VmBaseR` [J] + `VmRPre`'s `mid`
  [J], `lk` / `nb` [P], `hNt` / `nbt` [J] + `RdTab` [J] + `VmFoundC` (clause 10's fl4-sync input `hfd`). Derived:
  the `VmBase` parts above, `hEp` (the implication's hypothesis), `hRp`.
* **io** (`IoEntJ`, record `IoPremW3`): the index's `Q` is **stpost's canonical `IoQ`** (`hQ`, index convention), so
  `IoPremW2B.pe` / `mA` [J] are projections and `qf` [J] is `iw` [J] (`IoPre` kept by a user write; the affinity half
  by `SlJAt.tcbW_wr`, user words = `userV` words at `K.vcpus = ∅`). The start's `Q σ` [J] is now `BunIx` + `CurEnt`
  [J] + `IoLay` [J] + `walk` / `fin` [J]; derived: `IoPre.bxi` / `csc` / `hcsc` / `kb` / `nc` / `hT` / `hSc` /
  `affSc`, and the whole affinity half of `IoQ` from `GlueAt`'s memory link (`fld_aff_nu`).
* **st** (`StEntJ4`, record `StPremW3`): `Q` is **`StEntKK`'s form `StEntK K …`** (`hQ`), so `StPremK2B.pe` [J] is a
  projection and **`uf` [J] is derived** from `eu` at `K.vcpus = ∅` (`StPremW3.uf`: the memory half reads non-user
  words only). The start's `Q σ` [J] is now `BunIx` + `StPre` [J] + `target ∈ T` [J]: `StEnt.inv` / `lay` / `aff`
  from `BunIx`, `StEntK.mem` from `GlueAt`'s memory link.
* **vx** (`VxEntJ4`): `VxEntJ` minus `inv` / `lay` / `ntw` / `aff` [J] and the set conventions (from `BunIx`), `vh`
  [J] (`vcpuHeap_empty`), `vlk` [P] and `hvK` [J] (vacuous: the glue's `v` is the bound VCPU, `hv` [P], which is 0 at
  a bundle, `bound_ne0`), `aff0` [J] (from `GlueAt`'s memory link). Left: `hv` [P], `cs`, `curAff`, `cscCore`, `usr`
  [J], `buf` [P].
* **vt** (`VtEntJ4`): `VtEntJ` minus `inv` / `lay` / `ntw` / `aff` [J] and conventions (`BunIx`), `vf` [J]
  (`VFacts.ofEmpty` at `nv`), `vlk` [P] and `hvK` [J] (`vOf = 0` at a bundle). Left: `nv`, `cs`, `curAff`, `cscCore`,
  `hAs` [J].
* irq / sl: unchanged.

## 3. Not vacuous: vt's `ro` [W] at P3 scope

`VtPremP3.ro` is `ReadOnce … (VtPre st i K) (VexitRS …)`: it quantifies over **every** run from a `VtPre` state,
declining ones included. `VtPre` at `K.vcpus = ∅` forces `vOf st s = 0` (`VexitEnt.vin`) but is satisfiable, and
`local_vm_timer_irq` from such a state runs and declines (`irq_state`, `plan_objects`, `ct.state`, `bound_ntfn`,
`ntfn_quiet`, `vm_running` are read before the `vOf = 0` test fails). So `ro` asks `Once` (no user word read, every
word once) of that decline prefix: not vacuous; it is hpzg's `vtimer_hro` decline obligation (`hDU`) at
`R := VexitRSU`, a line task (needs `∉ K.user` of the decline prefix's reads, which `VtPre`'s `StLay` / `ntw` /
`cs` give by region, as `irq_rd_nu`). Same for vx (`vexit_localPathPG2` already discharges it there). No other
VM-slot record field becomes trivially provable at `K.vcpus = ∅`: `VtPremP3.M` / `UB` / `SL` / `pSg` and the `eu`s
quantify over every `VtPre` / `VxPre` state, not over accepting runs.

## Premise table diff vs `serializable_fl4_localP3W` (start entry facts and records only)

| slot | removed | added |
|---|---|---|
| vmF | `Pre` [J] as a whole (`VmBase`'s 8 P1 fields, `hEp`, `hRp`) | `BunIx` (index convention), `nv` |
| vmR | `VmBase`'s 8 P1 fields, `hEp`, `hRp` | `BunIx` |
| io | record `pe`, `mA`, `qf` [J]; start `Q` [J] (its `IoPre` P1 fields and affinity half) | `hQ` (index: `Q = IoQ`), `iw` [J], start `BunIx` |
| st | record `pe`, `uf` [J]; start `Q` [J] (`StEnt.inv` / `lay` / `aff`, `StEntK.mem`) | `hQ` (index: `Q = StEntK`), start `BunIx` |
| vx | start `inv` / `lay` / `ntw` / `aff` / `aff0` / `vh` / `hvK` [J], `vlk` [P], 6 conventions | `BunIx`, `hv` [P] (the glue's `v` is the bound VCPU) |
| vt | start `inv` / `lay` / `ntw` / `aff` / `vf` / `hvK` [J], `vlk` [P], 5 conventions | `BunIx`, `nv` |

Net: −2 record [J] for io beyond what `iw` replaces (`pe`, `mA`), −2 record [J] for st (`pe`, `uf`), −2 start [P]
(`vlk` of vx / vt) and per start the P1 invariants (`BXI`, `StLay`, `ScAff`, `EntryInv`'s SC facts, heap typing) of
every VM / io / st entry, now from clause 7 at the index's sets.
-/
import Fl4Proofs.P2.E2EVFl4Top
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EV
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
open Fl4Proofs.P2.OwnMap (fld oAFFINITY region TcbSlot InW)
open Fl4Proofs.P2.E2E (StartAt SP LocalPath)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll)

noncomputable section
open Classical

/-! ## 1. The bundle at the index's sets -/

section bun
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Kl : OwnMap.KLayout} {T Cs Ω : Set U64} {H : Heap} {Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}
  {s : S}

/-- **The bundle with its core and active-SC ghosts named** (module docstring, item 1). -/
def SlJAtS (Kl : OwnMap.KLayout) (Cs Ac : Set U64) (s : S) : Prop :=
  ∃ (A' : Type) (arI : machine.Arch A') (AR : A' → Fl4Spec.Cr3 → Prop) (Zx : Fl4Proofs.P3.XSets)
    (Lst : U64 → List U64) (D : Set U64) (a' : A') (σ : Fl4Spec.State Unit),
    SlJAtZ (L := L) arI AR Zx Cs Ac Lst D Kl s a' σ

theorem SlJAtS.slJAt (h : SlJAtS (L := L) Kl Cs Ac s) : SlJAt (L := L) Kl s := by
  obtain ⟨A', arI, AR, Zx, Lst, D, a', σ, B⟩ := h
  exact ⟨A', arI, AR, Zx, Cs, Ac, Lst, D, a', σ, B⟩

/-- **Every bundle state is one at the canonical cores and some active-SC set.** -/
theorem slJAtS_of (h : SlJAt (L := L) Kl s) : ∃ Ac, SlJAtS (L := L) Kl {c : U64 | c.val < Kl.ncores} Ac s := by
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := h
  have e : Cx = {c : U64 | c.val < Kl.ncores} := Set.ext fun c => B.cs c
  subst e
  exact ⟨Ax, A', arI, AR, Zx, Lst, D, a', σ, B⟩

/-- **The index's sets are the bundle's** (module docstring, item 1; the glue's choice of the index). -/
structure BunIx (Kl : OwnMap.KLayout) (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat)
    (Ac : Set U64) (s : S) : Prop where
  hKH : Kl.heap = H
  hT : T = H.tcbs
  hΩ : Ω = H.omega
  hSg : Sg = H.frame
  hRp : Rp = H.replies
  hScs : Scs = H.scs
  hNt : Nt = H.ntfns
  hZ : Z = H.scBits
  /-- Clause 7 at the state, with the index's `Cs` / `Ac` the bundle's ghosts. -/
  ac : SlJAtS (L := L) Kl Cs Ac s

/-- **Some index sets satisfy `BunIx` at every bundle state** (so `BunIx` is a choice of the index). -/
theorem bunIx_of (h : SlJAt (L := L) Kl s) : ∃ Ac, BunIx (L := L) Kl Kl.heap.tcbs {c : U64 | c.val < Kl.ncores}
    Kl.heap.omega Kl.heap Kl.heap.frame Kl.heap.replies Kl.heap.scs Kl.heap.ntfns Kl.heap.scBits Ac s := by
  obtain ⟨Ac, hA⟩ := slJAtS_of h
  exact ⟨Ac, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hA⟩

variable (BI : BunIx (L := L) Kl T Cs Ω H Sg Rp Scs Nt Z Ac s)
include BI

theorem BunIx.bxi : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s := by
  obtain ⟨hKH, hT, hΩ, hSg, hRp, hScs, hNt, hZ, ⟨A', arI, AR, Zx, Lst, D, a', σ, B⟩⟩ := BI
  subst hKH hT hΩ hSg hRp hScs hNt hZ
  exact B.j.bxi

theorem BunIx.entryInv : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s := by
  obtain ⟨hKH, hT, hΩ, hSg, hRp, hScs, hNt, hZ, ⟨A', arI, AR, Zx, Lst, D, a', σ, B⟩⟩ := BI
  subst hKH hT hΩ hSg hRp hScs hNt hZ
  exact B.j.entryInv B.res

theorem BunIx.stLay : StLay Kl st T Scs Z s := by
  obtain ⟨hKH, hT, -, -, -, hScs, -, hZ, ⟨A', arI, AR, Zx, Lst, D, a', σ, B⟩⟩ := BI
  subst hKH hT hScs hZ
  exact B.stLay

theorem BunIx.kb : Kl.ksb = L.ksb s := by
  obtain ⟨-, -, -, -, -, -, -, -, ⟨A', arI, AR, Zx, Lst, D, a', σ, B⟩⟩ := BI
  exact B.ksb.symm

theorem BunIx.nc : (L.cpu s).val < Kl.ncores := by
  obtain ⟨-, -, -, -, -, -, -, -, ⟨A', arI, AR, Zx, Lst, D, a', σ, B⟩⟩ := BI
  exact B.cpu

theorem BunIx.aff : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t) :=
  fun _ ht h0 => (XInv.core_eq BI.bxi.2.2.1 ht h0).symm

theorem BunIx.ntw : ∀ p ∈ Nt, ∀ k : U64, k.val < 64 → region Kl (core.num.U64.wrapping_add p k) = .ntfn p := by
  have hL := irqLayK_of_slJAt BI.bxi BI.ac.slJAt
  obtain ⟨hKH, -, -, -, -, -, hNt, -, -⟩ := BI
  subst hKH hNt
  exact hL.ntw

theorem BunIx.tcbT : ∀ t ∈ T, Kl.heap t = some .tcb := by
  obtain ⟨hKH, hT, -, -, -, -, -, -, -⟩ := BI
  subst hKH hT
  exact fun t ht => ht

theorem BunIx.scsT : ∀ c ∈ Scs, H c = some (.sc (Z c)) := by
  obtain ⟨-, -, -, -, -, hScs, -, hZ, -⟩ := BI
  subst hScs hZ
  rintro c ⟨z, hz⟩
  simp only [Heap.scBits, hz]

theorem BunIx.scsK : ∀ c ∈ Scs, Kl.heap c = some (.sc (Z c)) := fun c hc => by
  rw [BI.hKH]; exact BI.scsT c hc

theorem BunIx.ntT : ∀ q ∈ Nt, H q = some .ntfn := fun q hq => by
  rw [BI.hNt] at hq; exact hq

end bun

section aff
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Kl : OwnMap.KLayout} {T Cs Ω : Set U64} {H : Heap} {Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}
  {s : S}

/-- A thread's `AFFINITY` word is aligned and no user word (its region is the TCB's). -/
theorem fld_aff_nu (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hL : StLay Kl st T Scs Z s) {t : U64} (ht : t ∈ T) :
    Aligned (fld t oAFFINITY) ∧ fld t oAFFINITY ∉ Kl.user := by
  have hA : TcbAddr t := hI.1.choose_spec.choose_spec.tcbs t ht
  have hr : region Kl (fld t oAFFINITY) = .tcb t :=
    hL.tcb t ht oAFFINITY (by simp [oAFFINITY]) (by simp [oAFFINITY])
  refine ⟨field_aligned hA (by simp [oAFFINITY]) (by simp [oAFFINITY]), hL.nu ?_⟩
  rw [hr]; intro e; cases e

end aff

/-! ## 2. Residual entry records -/

section rec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **The current thread's entry facts no bundle lemma gives yet** [J] (shared by `VmBase` / `IoPre`). -/
structure CurEnt (s : S) : Prop where
  /-- [J] -/
  run : L.mem s (stA (L.curW s)) = sched.TS_RESTART ∨ L.mem s (stA (L.curW s)) = sched.TS_RUNNING
  /-- [J] -/
  curAff : L.mem s (affA (L.curW s)) = L.cpu s
  /-- [J] -/
  cscCore : L.mem s (scCoreA (L.cscW s)) = L.cpu s
  /-- [J] -/
  tmc : L.mem s (tmA (L := L) s) ≠ 0#u64 → L.mem s (tdA (L.mem s (tmA (L := L) s))) ≠ 0#u64 ∧
    OwnMap.treeCore (L.mem s (thA (L.mem s (tmA (L := L) s)))) = L.cpu s

/-- **What stays of `VmBase`** beside `BunIx`. -/
structure VmBaseR (Kl : OwnMap.KLayout) (s : S) : Prop where
  /-- [J] -/
  cur : CurEnt (L := L) s
  /-- [J] -/
  lay : VmLay Kl

variable {Kl : OwnMap.KLayout} {T Cs Ω : Set U64} {H : Heap} {Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}
  {s : S}

/-- **`VmBase` from `BunIx` and the residue.** -/
theorem VmBaseR.base (BI : BunIx (L := L) Kl T Cs Ω H Sg Rp Scs Nt Z Ac s) (R : VmBaseR (L := L) Kl s) :
    VmBase st Kl T Cs Ω H Sg Rp Scs Nt Z Ac s where
  bxi := BI.bxi
  csc := BI.entryInv.csc
  hcsc := BI.entryInv.hcsc
  run := R.cur.run
  lay := R.lay
  kb := BI.kb
  nc := BI.nc
  hT := BI.tcbT
  hSc := BI.scsK
  curAff := R.cur.curAff
  cscCore := R.cur.cscCore
  affSc := BI.aff
  tmc := R.cur.tmc

end rec

/-! ## 3. Per-slot entry facts -/

section ent
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)

/-- **vmF's start entry facts** (module docstring, item 2). -/
structure VmFEntJ (i : VmFArg S) (K : KLayoutV) (s : S) : Prop where
  /-- No VCPU in the layout (the glue's layout choice at P3 scope). -/
  nv : K.vcpus = ∅
  /-- Index convention: the index's sets are the bundle's at `s`. -/
  ix : BunIx (L := L) K.toKLayout i.T i.Cs i.Ω i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac s
  /-- [J] -/
  br : VmBaseR (L := L) K.toKLayout s
  /-- [J] as `VmFPre.hyp`. -/
  hyp : ∀ a s1 a1, sched.update_timestamp st ar s a = ok (s1, a1) →
    VmFootHyps (L := L) i.T i.Cs i.Ω i.U i.Sg i.Rp i.Scs i.Nt i.Ac i.H i.Z s1
  /-- [P] as `VmFPre.lk`. -/
  lk : ∀ a s1 a1 ptr badge dest r, sched.update_timestamp st ar s a = ok (s1, a1) →
    FaultChecks st s1 (L.curW s1) ptr badge dest r → i.Locks s ptr ∧ i.Locks s r
  /-- [J] as `VmFPre.hyt`. -/
  hyt : ∀ a s1 a1 ptr badge dest r, sched.update_timestamp st ar s a = ok (s1, a1) →
    FaultChecks st s1 (L.curW s1) ptr badge dest r → L.mem s (yieldA dest) = 0#u64
  /-- [P] -/
  gl : VmGlue st ar i.Locks s
  /-- [J] -/
  tab : RdTab (L := L) (IoRS (st := st) K.toKLayout i.Locks s) s

theorem VmFEntJ.pre {i : VmFArg S} {K : KLayoutV} {s : S} (E : VmFEntJ st ar i K s) (hK : RegionOKV K) :
    VmPre st ar (userV K) i.T i.Cs i.Ω i.U i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac i.Locks s :=
  vmPre_userV_empty hK E.nv
    ⟨⟨E.br.base E.ix, E.hyp, E.lk, fun p hp => by rw [E.ix.hKH]; exact hp,
      fun r hr => by rw [E.ix.hKH]; rw [E.ix.hRp] at hr; exact hr, E.hyt⟩, E.gl, E.tab⟩

/-- **vmR's start entry facts** at the path's layout `Kl` (`userV K`) (module docstring, item 2). -/
structure VmREntJ (i : VmRArg S) (Kl : OwnMap.KLayout) (s : S) : Prop where
  /-- Index convention. -/
  ix : BunIx (L := L) Kl Kl.heap.tcbs i.Cs i.Ω Kl.heap i.Sg Kl.heap.replies Kl.heap.scs Kl.heap.ntfns
    Kl.heap.scBits i.Ac s
  /-- [J] -/
  br : VmBaseR (L := L) Kl s
  /-- [J] as `VmRPre.mid`. -/
  mid : ∀ a s2 a2, LocalPre (st := st) ar s a (s2, a2) →
    BXI st Kl.heap.tcbs i.Cs i.Ω Kl.heap i.Sg Kl.heap.replies Kl.heap.scs Kl.heap.ntfns Kl.heap.scBits i.Ac s2 ∧
      AsidOff (L := L) i.Ω i.Sg s2 ∧
      ∀ u usc, RRChecksG st ar fl4_abi.consts.fault.VMFault s2 a2 (L.curW s) i.rptr i.ep u usc →
        RRPl (L := L) Kl.heap.tcbs i.Cs i.Ω i.Sg Kl.heap.replies Kl.heap.scs Kl.heap.ntfns Kl.heap.scBits s2
          (L.curW s) i.rptr i.ep u usc ∧ L.mem s2 (yieldA u) = 0#u64
  /-- [P] -/
  lk : i.Locks s i.rptr ∧ i.Locks s i.ep
  /-- [P] -/
  nb : L.mem s (rPrevA i.rptr) = 0#u64 ∧ L.mem s (rNextA i.rptr) = 0#u64
  /-- [J] -/
  hNt : ∀ p ∈ Kl.heap.ntfns, Kl.heap p = some .ntfn ∧ p.val % 64 = 0 ∧ p.val + 64 ≤ 2 ^ 64 ∧
    ∀ b, InW p 64 b → region Kl b = .ntfn p
  /-- [J] -/
  nbt : L.mem s (boundA (L.curW s)) ≠ 0#u64 → L.mem s (fld (L.mem s (boundA (L.curW s))) 24#u64) = L.curW s
  /-- [J] -/
  tab : RdTab (L := L) (IoRS (st := st) Kl i.Locks s) s
  /-- `loc_chain_all` clause 10's fl4-sync input `hfd`. -/
  fd : VmFoundC st i.rptr i.ep s

theorem VmREntJ.toP3 {i : VmRArg S} {Kl : OwnMap.KLayout} {s : S} (E : VmREntJ st ar i Kl s) :
    (Kl.heap i.ep = some .ep → VmRPre st ar Kl Kl.heap.tcbs i.Cs i.Ω Kl.heap i.Sg (Heap.replies Kl.heap)
      Kl.heap.scs Kl.heap.ntfns Kl.heap.scBits i.Ac i.Locks s i.rptr i.ep) ∧
    RdTab (L := L) (IoRS (st := st) Kl i.Locks s) s ∧ VmFoundC st i.rptr i.ep s :=
  ⟨fun hep =>
    { base := E.br.base E.ix
      mid := E.mid
      lk := E.lk
      nb := E.nb
      hEp := hep
      hRp := fun _ hr => hr
      hNt := E.hNt
      nbt := E.nbt }, E.tab, E.fd⟩

/-- **io's start entry facts**: `IoPre` beside `BunIx` (module docstring, item 2). -/
structure IoEntJ (i : IoArg S) (K : KLayoutV) (s : S) : Prop where
  /-- Index convention. -/
  ix : BunIx (L := L) K.toKLayout K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns
    K.heap.scBits i.Ac s
  /-- [J] -/
  cur : CurEnt (L := L) s
  /-- [J] -/
  lay : IoLay K.toKLayout
  /-- [J] as `IoPre.walk`. -/
  walk : ∃ C : U64 → U64 → Prop, (∀ p r gs g, obj.Slot.cap st (L.curW s) s = ok (.CNode p r gs g) → C p r) ∧
    WalkCl (st := st) s C ∧
    ∀ p r m y, C p r → cspace.mask r = ok m → cnSlot p (y &&& m) ∈ K.slots ∧
      OutsideObjs st K.heap.tcbs i.Cs s (cnSlot p (y &&& m)) ∧
      OutsideObjs st K.heap.tcbs i.Cs s (core.num.U64.wrapping_add (cnSlot p (y &&& m)) 8#u64)
  /-- [J] as `IoPre.fin`. -/
  fin : ∀ x, cspace.lookup_slot st s (L.curW s) (L.mem s (regA (L.curW s) layout.reg.CAP)) = ok (.Ok x) →
    x.slot ∈ K.slots ∧ OutsideObjs st K.heap.tcbs i.Cs s x.slot ∧
      OutsideObjs st K.heap.tcbs i.Cs s (core.num.U64.wrapping_add x.slot 8#u64)

theorem IoEntJ.pre {i : IoArg S} {K : KLayoutV} {s : S} (E : IoEntJ st i K s) :
    IoPre st K.toKLayout K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits i.Ac s
    where
  bxi := E.ix.bxi
  csc := E.ix.entryInv.csc
  hcsc := E.ix.entryInv.hcsc
  run := E.cur.run
  lay := E.lay
  kb := E.ix.kb
  nc := E.ix.nc
  hT := E.ix.tcbT
  hSc := E.ix.scsK
  curAff := E.cur.curAff
  cscCore := E.cur.cscCore
  affSc := E.ix.aff
  tmc := E.cur.tmc
  walk := E.walk
  fin := E.fin

/-- **io's premises with stpost's canonical `Q`** (module docstring, item 2). -/
structure IoPremW3 (i : IoArg S) (K : KLayoutV) (m : U64 → U64) : Prop where
  /-- No VCPU in the layout (as `ioSlotP3W`). -/
  nv : K.vcpus = ∅
  /-- Index convention: the index's `Q` is stpost's `IoQ`. -/
  hQ : i.Q = fun K' m' s => IoQ st i.Cs i.Ω i.Sg i.Ac K'.toKLayout m' s
  /-- [J] `IoPre` survives an aligned user-word write at a bundle state (stpost's `hIw`). -/
  iw : ∀ s b v, SlJAt (L := L) K.toKLayout s →
    IoPre st K.toKLayout K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits i.Ac s →
    b ∈ K.user → Aligned b →
    IoPre st K.toKLayout K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits i.Ac
      (L.wr s b v)
  /-- [P] as `IoPremW2B.kd`. -/
  kd : ∀ s, SlJAt (L := L) K.toKLayout s → KernDetS (L := L) (userV K).user i.Locks s
  /-- Some bundle state of the layout (no premise: the start state). -/
  bun : ∃ σ : S, SlJAt (L := L) K.toKLayout σ

theorem IoPremW3.qE {i : IoArg S} {K : KLayoutV} {m : U64 → U64} (h : IoPremW3 st i K m) {s : S} :
    i.Q K m s = IoQ st i.Cs i.Ω i.Sg i.Ac K.toKLayout m s := by
  rw [h.hQ]

/-- **`IoPremW2B` (with `nv`) from `IoPremW3`**: `pe` / `mA` projections, `qf` from `iw` and `SlJAt.tcbW_wr`. -/
theorem IoPremW3.toP3 {i : IoArg S} {K : KLayoutV} {m : U64 → U64} (h : IoPremW3 st i K m) :
    K.vcpus = ∅ ∧ IoPremW2B st i K m := by
  refine ⟨h.nv, fun s _ hq => ?_, fun s _ hq => ?_, fun s b v hJ hq hb hba => ?_, h.kd, h.bun⟩
  · rw [h.qE] at hq; exact hq.1
  · rw [h.qE] at hq; exact hq.2
  · have hb' : b ∈ K.user := (mem_userV.1 hb).resolve_right (not_vData_empty h.nv)
    rw [h.qE] at hq ⊢
    exact ⟨h.iw s b v hJ hq.1 hb' hba, fun d hd => by
      rw [hJ.tcbW_wr hb' hba v hd (o := oAFFINITY) (by simp [oAFFINITY]) (by simp [oAFFINITY])]
      exact hq.2 d hd⟩

/-- **The start's `Q` from `IoEntJ` and `GlueAt`'s memory link.** -/
theorem IoEntJ.q {i : IoArg S} {K : KLayoutV} {m : U64 → U64} {s : S} (E : IoEntJ st i K s)
    (h : IoPremW3 st i K m) (hμ : ∀ x, Aligned x → ¬ x ∈ K.user → L.mem s x = m x) : i.Q K m s := by
  rw [h.qE]
  refine ⟨E.pre, fun d hd => ?_⟩
  have ha := fld_aff_nu E.ix.bxi E.ix.stLay (t := d) hd
  exact (hμ _ ha.1 ha.2).symm

/-- **st's premises with `Q := StEntK`** (module docstring, item 2): `StPremK2B` minus `pe` / `uf`. -/
structure StPremW3 (i : StArg S) (K : KLayoutV) (m : U64 → U64) : Prop where
  /-- No VCPU in the layout (as `stSlotP3W`). -/
  nv : K.vcpus = ∅
  /-- Some bundle state of the layout (no premise: the start state). -/
  bun : ∃ σ : S, SlJAt (L := L) K.toKLayout σ
  /-- Index convention: the index's `Q` is `StEntK` (stpost's `StEntKK`). -/
  hQ : i.Q = fun K' m' s => StEntK K'.toKLayout st K'.heap.tcbs i.Cs i.Ω K'.heap i.Sg K'.heap.replies
    K'.heap.scs K'.heap.ntfns K'.heap.scBits i.Ac i.target m' s
  /-- [J] -/
  eu : ∀ s b v, StEnt (userV K) st K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns
      K.heap.scBits i.Ac i.target s → b ∈ (userV K).user → Aligned b →
    StEnt (userV K) st K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits i.Ac
      i.target (L.wr s b v)
  /-- [P] -/
  kd : ∀ s, KernDetS (L := L) (userV K).user i.lk s
  /-- [J] -/
  nu : ∀ s, StEnt (userV K) st K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns
      K.heap.scBits i.Ac i.target s → ∀ o : U64, o.val < 4288 → L.nodeAt s (L.cpu s) o ∉ (userV K).user

theorem StPremW3.qE {i : StArg S} {K : KLayoutV} {m : U64 → U64} (h : StPremW3 st i K m) {s : S} :
    i.Q K m s = StEntK K.toKLayout st K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns
      K.heap.scBits i.Ac i.target m s := by
  rw [h.hQ]

/-- **`StPremK2B` (with `nv`) from `StPremW3`**: `pe` a projection, `uf` from `eu` (no VCPU data word). -/
theorem StPremW3.toP3 {i : StArg S} {K : KLayoutV} {m : U64 → U64} (h : StPremW3 st i K m) :
    K.vcpus = ∅ ∧ StPremK2B st i K m := by
  refine ⟨h.nv, h.bun, fun s _ hq => ?_, h.eu, h.kd, h.nu, fun s b v _ hq hb hba => ?_⟩
  · rw [h.qE] at hq; exact hq
  · have hb' : b ∈ K.user := (mem_userV.1 hb).resolve_right (not_vData_empty h.nv)
    have eu := h.eu
    rw [userV_empty h.nv] at eu
    rw [h.qE] at hq ⊢
    exact ⟨eu s b v hq.ent hb' hba, fun x hx hxu => by
      rw [mem_wr_ne' hba hx (fun e => hxu (e ▸ hb'))]; exact hq.mem x hx hxu⟩

/-- **st's start entry facts** (module docstring, item 2). -/
structure StEntJ4 (i : StArg S) (K : KLayoutV) (s : S) : Prop where
  /-- Index convention. -/
  ix : BunIx (L := L) K.toKLayout K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns
    K.heap.scBits i.Ac s
  /-- [J] -/
  pre : StPre st K.heap.scs s
  /-- [J] the target is a thread. -/
  tg : i.target ∈ K.heap.tcbs

theorem StEntJ4.q {i : StArg S} {K : KLayoutV} {m : U64 → U64} {s : S} (E : StEntJ4 st i K s)
    (h : StPremW3 st i K m) (hμ : ∀ x, Aligned x → ¬ x ∈ K.user → L.mem s x = m x) : i.Q K m s := by
  rw [h.qE]
  exact ⟨⟨E.ix.bxi, E.ix.stLay, E.pre, E.ix.aff, E.tg⟩, hμ⟩

/-- **vx's start entry facts** (module docstring, item 2). -/
structure VxEntJ4 (i : VxArg S) (K : KLayoutV) (s : S) : Prop where
  /-- Index convention. -/
  ix : BunIx (L := L) K.toKLayout i.T i.Cs i.Ω i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac s
  /-- [P] the glue's `v` is the current thread's bound VCPU. -/
  hv : i.v = vOf st s
  /-- [J] -/
  cs : ∀ k : U64, k.val < 192 → k.val % 32 < 16 → ∃ p,
    region K.toKLayout (core.num.U64.wrapping_add (L.curW s) k) = .slot p ∧ OwnMap.TcbSlot K.toKLayout p ∧
      (core.num.U64.wrapping_add (L.curW s) k).val - p.val < 16
  /-- [J] -/
  curAff : L.mem s (affA (L.curW s)) = L.cpu s
  /-- [J] -/
  cscCore : L.mem s (scCoreA (L.cscW s)) = L.cpu s
  /-- [J] -/
  usr : ∀ x, x ∈ K.user → Aligned x → UsrW st i.T i.Cs i.H i.Sg i.Scs i.Z s x
  /-- [P] -/
  buf : msg.lookup_ipc_buffer st s true (L.curW s) ⦃ b => BufOK {x | x ∈ K.user ∧ Aligned x} b ⦄

theorem VxEntJ4.toJ {i : VxArg S} {K : KLayoutV} {m : U64 → U64} {s : S} (nv : K.vcpus = ∅)
    (E : VxEntJ4 st i K s) (hμ : ∀ x, Aligned x → ¬ x ∈ K.user → L.mem s x = m x) : VxEntJ st i K m s := by
  have hJ := E.ix.ac.slJAt
  have hI := E.ix.bxi
  have ha := fld_aff_nu hI E.ix.stLay hI.1.choose_spec.choose_spec.curT
  exact
    { inv := hI
      lay := E.ix.stLay
      ntw := E.ix.ntw
      cs := E.cs
      aff := E.ix.aff
      curAff := E.curAff
      cscCore := E.cscCore
      vlk := bound_ne0 hJ E.hv
      usr := E.usr
      buf := E.buf
      aff0 := (hμ _ ha.1 ha.2).symm
      vh := vcpuHeap_empty nv
      hKH := E.ix.hKH
      hTs := E.ix.hT
      hΩ := E.ix.hΩ
      hSg := E.ix.hSg
      hScs := E.ix.scsT
      hNt := E.ix.ntT
      hvK := bound_ne0 hJ E.hv }

/-- **vt's start entry facts** (module docstring, item 2). -/
structure VtEntJ4 (i : VtArg S) (K : KLayoutV) (s : S) : Prop where
  /-- No VCPU in the layout (the glue's layout choice at P3 scope). -/
  nv : K.vcpus = ∅
  /-- Index convention. -/
  ix : BunIx (L := L) K.toKLayout i.T i.Cs i.Ω i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac s
  /-- [J] -/
  cs : ∀ k : U64, k.val < 192 → k.val % 32 < 16 → ∃ p,
    region K.toKLayout (core.num.U64.wrapping_add (L.curW s) k) = .slot p ∧ OwnMap.TcbSlot K.toKLayout p ∧
      (core.num.U64.wrapping_add (L.curW s) k).val - p.val < 16
  /-- [J] -/
  curAff : L.mem s (affA (L.curW s)) = L.cpu s
  /-- [J] -/
  cscCore : L.mem s (scCoreA (L.cscW s)) = L.cpu s
  /-- [J] -/
  hAs : AsidOff (L := L) i.Ω i.Sg s

theorem VtEntJ4.toJ {i : VtArg S} {K : KLayoutV} {s : S} (E : VtEntJ4 st i K s) : VtEntJ st i K s := by
  have hJ := E.ix.ac.slJAt
  exact
    { inv := E.ix.bxi
      lay := E.ix.stLay
      ntw := E.ix.ntw
      cs := E.cs
      aff := E.ix.aff
      curAff := E.curAff
      cscCore := E.cscCore
      vlk := bound_ne0 hJ rfl
      vf := VFacts.ofEmpty E.nv hJ
      hKH := E.ix.hKH
      hTs := E.ix.hT
      hΩ := E.ix.hΩ
      hScs := E.ix.scsT
      hNt := E.ix.ntT
      hvK := hvK_vtimer hJ
      hAs := E.hAs }

end ent

/-! ## 4. `GlueAt` monotone in the entry facts -/

section glue
variable {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
  {ko : U64 → ClsOwner U64} {User : U64 → Prop}

theorem GlueAt.mono {P : LocalPath own cls ko User} {Ent Ent' : P.S → Prop} {c : U64} {hs : U64 → Prop}
    {μ : U64 → U64} {q : SP} (h : GlueAt P Ent c hs μ q)
    (hE : ∀ σ, Ent σ → (∀ x, Aligned x → ¬ User x → P.L.mem σ x = μ x) → Ent' σ) : GlueAt P Ent' c hs μ q := by
  obtain ⟨σ, a, he, hc, hl, hμ, hq⟩ := h
  exact ⟨σ, a, hE σ he hμ, hc, hl, hμ, hq⟩

end glue

/-! ## 5. The start fact and the top -/

section start
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hSt : P0.StoreTotal st) (hm : E2E.MasksWr st) (a0 : A)

/-- **The start fact of `fl4LocP3W`, entry facts shrunk** (module docstring, item 2). -/
def StartP3W4 (Ch : S → Prop) (K : KLayoutV) (m : U64 → U64) (hK : RegionOKV K) (hU : UserOKV K) (c : U64)
    (hs : U64 → Prop) (q : SP) : Fl4IxW (S := S) → Prop
  | .vmF j => ∃ h : VmFPrem st ar j K m, GlueAt ((vmFSlot st ar hA hm).liftAt j K m hK hU h)
      (fun σ : S => Ch σ ∧ VmFEntJ st ar j K σ) c hs m q
  | .vmR j => ∃ h : VmRPremP3 st ar j K m, GlueAt ((vmRSlotP3 st ar hA hm).liftAt j K m hK hU h)
      (fun σ : S => Ch σ ∧ VmREntJ st ar j (userV K) σ) c hs m q
  | .io j => ∃ h : IoPremW3 st j K m, GlueAt ((ioSlotP3W st ar hA hm).liftAt j K m hK hU h.toP3)
      (fun σ : S => Ch σ ∧ IoEntJ st j K σ) c hs m q
  | .st j => ∃ h : StPremW3 st j K m, GlueAt ((stSlotP3W st ar hA hm).liftAt j K m hK hU h.toP3)
      (fun σ : S => Ch σ ∧ StEntJ4 st j K σ) c hs m q
  | .irq j => ∃ h : (irqSlotP3W st ar hA hm).Prem j K m, GlueAt ((irqSlotP3W st ar hA hm).liftAt j K m hK hU h)
      (fun σ : S => Ch σ) c hs m q
  | .sl j => ∃ h : (slSlotP3 st ar hA hSt hm a0).Prem j K m,
      GlueAt ((slSlotP3 st ar hA hSt hm a0).liftAt j K m hK hU h)
      (fun σ : S => Ch σ ∧ Fl4Proofs.P2.PathObl.SlQ st ar j.Locks j.n j.found j.Cs j.Ω j.Sg j.Ac K.toKLayout m σ) c hs m q
  | .vq (.inl j) => ∃ h : VxPremP3 st j K m, GlueAt ((vxSlotP3 st ar hA hm).path j K m hK hU h)
      (fun σ : S => Ch σ ∧ VxEntJ4 st j K σ) c hs m q
  | .vq (.inr j) => ∃ h : VtPremP3 st ar j K m, GlueAt ((vtSlotP3 st ar hA hm).path j K m hK hU h)
      (fun σ : S => Ch σ ∧ VtEntJ4 st j K σ) c hs m q

/-- **`StartP3W4` gives `StartP3W`** (module docstring). -/
theorem startP3W_of_W4 {Ch : S → Prop} {K : KLayoutV} {m : U64 → U64} {hK : RegionOKV K} {hU : UserOKV K}
    {c : U64} {hs : U64 → Prop} {q : SP} {i : Fl4IxW (S := S)}
    (h : StartP3W4 st ar hA hSt hm a0 Ch K m hK hU c hs q i) :
    StartP3W st ar hA hSt hm a0 Ch K m hK hU c hs q i := by
  cases i with
  | vmF j =>
    obtain ⟨h, hG⟩ := h
    exact ⟨h, hG.mono fun σ he _ => he.2.pre st ar hK⟩
  | vmR j =>
    obtain ⟨h, hG⟩ := h
    exact ⟨h, hG.mono fun σ he _ => ⟨he.1, he.2.toP3 st ar⟩⟩
  | io j =>
    obtain ⟨h, hG⟩ := h
    exact ⟨h.toP3, hG.mono fun σ he hμ => ⟨he.1, he.2.q st h hμ⟩⟩
  | st j =>
    obtain ⟨h, hG⟩ := h
    exact ⟨h.toP3, hG.mono fun σ he hμ => ⟨he.1, he.2.q st h hμ⟩⟩
  | irq j => exact h
  | sl j => exact h
  | vq j =>
    cases j with
    | inl j =>
      obtain ⟨h, hG⟩ := h
      exact ⟨h, hG.mono fun σ he hμ => ⟨he.1, he.2.toJ st h.nv hμ⟩⟩
    | inr j =>
      obtain ⟨h, hG⟩ := h
      exact ⟨h, hG.mono fun σ he _ => ⟨he.1, he.2.toJ st⟩⟩

end start

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hSt : P0.StoreTotal st) (hm : E2E.MasksWr st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **FL4 end to end, P3 scope, glue premises named, start entry facts shrunk** (module docstring):
`serializable_fl4_localP3W` with `StartP3W4` starts (the P1 invariants of every VM / io / st entry from clause 7 at
the index's sets, io / st at their canonical `Q`). -/
theorem serializable_fl4_localW4 (P : LocPlat st arI AR MR) {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutV}
    {Ch0 Ch : S → Prop} (h0 : Init s0) (hA0 : ArmInv s0) (hB : SerExitW P K0 Ch0) (nv0 : K0.vcpus = ∅)
    (hM0 : MapsV K0 s0)
    (h : ExecW ((fl4LocP3W st ar hA hSt hm a0).paths (fl4Dflt st ar hm)) (StartP3W4 st ar hA hSt hm a0) P s0 K0 Ch0
      s K Ch) (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  have hE := (execV_of_W (fun _ _ _ _ _ _ _ _ _ hCh hi =>
    startAt_P3W st ar hA hSt hm a0 hCh (startP3W_of_W4 st ar hA hSt hm a0 hi)) hB h).1
  have hok := serExitW_ok hB (vcpuLay_empty nv0)
  exact serializable_fl4_localP3WV st ar hA hSt hm a0 h0 hA0 hok.1 hok.2 hM0 hE hq

end top

end
end Fl4Proofs.P2.E2EV
