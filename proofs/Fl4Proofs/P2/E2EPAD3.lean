/-
# P2 (line mmuAD, gen 18): **two [S] items of the A/D top discharged** — `serializable_fl4_localAD3`

`serializable_fl4_localAD2` (P2/E2EPAD2.lean) rests on [S] start content of the VM-epoch PageMap start
(`PmStartX`: VX9's `InvEntV9` at `PmEntG` = `PmQF ∧ PmEx ∧ PmRoot ∧ WalkP ∧ ne0`) and on the [S] VM layout fact
`VmPweT` (= `VmPwe` (`nov`, `tab`) + `tabw`) at VM serial exits. This module removes what already follows from
the rest:

* **`PmRoot` is a theorem of `PmQF`** (`pmRoot_of_qf`, P2/InvPmRoot.lean: the plan's `X86PageMap` arm checks
  `find_vspace_for_asid asid = root` for the PML4 cap it reads, localinv.rs `plan_with`; `InvPlanD` records that
  plan). So the start entry **`PmEntG3`** = `PmQF ∧ PmEx ∧ WalkP ∧ ne0` and the start fact **`PmStartX3`** drop it;
  `pmStartX_of3` / `pmStartX3_of` convert both ways.
* **`tabw`'s table half (aligned, region `.none`) is a theorem of the epoch's `VtxBundle4`** (its `UserLayX.rx :
  RegionOKX`, field `asidT`), which every VM serial exit gives (`Fl4StepVX4.ser`). The [S] record **`VmPweU`** =
  `VmPwe` + `tabu` (the ASID-table words are not user words) + `pool` (the named pools' words are `VsW` words);
  `VmPweU.toT` (with `RegionOKX`) and `VmPweT.toU` convert. **`ExecVX4e`** is `ExecVX4d` with `VmPweU` at VM serial
  exits; `execVX4d_of_e` / `execVX4e_of_d` embed each into the other (start facts mapped pointwise).
* **`serializable_fl4_localAD3`**: `serializable_fl4_localAD2`'s premises with the execution over `ExecVX4e` and the
  start facts `StartAD3` = `StartAD` ⊕ `PmStartX3`. **`serializable_fl4_localAD2of3`**: AD2's exact statement from
  AD3 (so AD3's premises are implied by AD2's: nothing is strengthened).

## Premise diff, `serializable_fl4_localAD3` vs `serializable_fl4_localAD2`
* [S] start entry of the VM-epoch PageMap start: `PmQF ∧ PmEx ∧ PmRoot ∧ WalkP ∧ ne0` → `PmQF ∧ PmEx ∧ WalkP ∧ ne0`
  (**`PmRoot` gone**).
* [S] VM layout fact at VM serial exits: `VmPweT` (`nov`, `tab`, `tabw` = table words aligned ∧ region `.none` ∧ not
  user, pool words `VsW`) → `VmPweU` (`nov`, `tab`, `tabu` = table words not user, `pool` = pool words `VsW`):
  **the table words' alignment and region gone**.
* Everything else unchanged: `P`, [P] `hIoa`, `B : PmObl7` ([P] `cs`, [P] `lk`), `h0`, `hA0`, `hB`, `hc0`, `hM0`,
  [P] `MmuAD` (in the execution), `hq`; the other start facts; `InvEntV9`'s `hz`, `ent.1` (`InvLXS`), `qps`;
  [P] `PmPremX.lk`, `GlueAt` data. No [W], no [J].

## What is not discharged, and why (each checked against every VM-epoch fact the line has)
In VM epochs no state invariant is proved: P3's joint invariant reaches no guest-running state (`JExt.vw`: every
TCB's VCPU word is 0), so every VM-epoch fact is [S] start content or the [S] layout bundle `VtxBundle4` /
`VmPweU`, and the [S] items below follow from none of them.
* **`ne0`** (no walk answers entry address 0). Natively `SlJAtZ.spe_ne0` (P2/InvVsJ.lean): the L1 table is a spec
  page table (`PtRel.l1`), hence an `other` object of `H` (`SpecCover.arch`), and `H 0 = none` (`JKern.h0`). In a VM
  epoch the leaf set is the convention `K.ptes = ptesR K E` (`EpochJV.conv`), which is not tied to `K.heap`, and no
  layout fact (`RegionOK`, `RegionOKX`, `LayP`, `UserLayX`, `VtxBundle4`, `QPs`, `KsNoE`, `TabNoE`) says anything
  about address 0 (as for `InvEntV9.hz`). **Missing boot-level fact**: no leaf page-table entry at address 0 in a
  VM-epoch layout, `(0#u64) ∉ K.ptes` (Rust: `bootmem::ram` gives RAM untypeds only above `HIGHMEM_PADDR` = 1 MiB,
  fl4-kernel lib.rs l. 436; device untypeds retype only to frames, so no PT object covers page 0). With it, `ne0`
  is `ne0_of_ptes` from `WalkP` (proved below); the line does not add it (it would replace one [S] by another).
* **`PmQF ∧ PmEx`**: the glue's plan at the start state (natively the same content is in `StartPmK`, from
  `pmQF_of_plan` / `pmEx_of_plan`) together with P1's entry facts `IoQ` (`IoPre`: current thread, SC, CSpace walk,
  timer tree), which natively come from P3's bundle and in VM epochs from nothing proved.
* **`VmPwe.tab`** (the ASID-table words are `GateW`). From `VtxBundle4` one gets their region `.none`
  (`RegionOKX.asidT`) and, with `EpochJV.conv`, that they are no leaf PTE (`ptesR` excludes `WalkW` words); the
  missing part is "in no VCPU": `VcpuKsOff` puts every VCPU outside `[ksb, ksb + 304384)` as natural numbers, but
  `atAF ksb hi` is a wrapping sum, and no VM-epoch fact bounds `ksb + 304384 ≤ 2 ^ 64` (natively `JKern.ksbFit` /
  `VsTop.ksb_fit`). Missing fact: that bound at VM layouts.
* **`tabu`, `pool`, `nov`**: placement of the ASID table against user memory (`UserLayX.uks` covers only
  `[ksb, ksb + 13568)`, the table is at `ksb + 288000`), of the ASID pools (named by memory, tied to no `K.heap`
  object in a VM epoch), and of upper-level paging words against VCPUs (gen 14's counterexample shape: a named root
  whose L4 entry points into a VCPU makes `v.PENDING` a paging word; excluded only by the real kernel's typing).

No sorry / admit / native_decide / bv_decide. New module; no existing statement changes.
-/
import Fl4Proofs.P2.E2EPAD2U
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll Step hwCfg)
open Fl4Proofs.P2.MmuAD (MmuAD ADEq NotPresent)

noncomputable section
open Classical

/-! ## 1. `ne0` from a leaf set without address 0 (the missing fact made precise) -/

section ne0
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **`ne0` from `WalkP` and a leaf set without address 0** (module docstring: the boot-level fact the line lacks
in VM epochs). -/
theorem ne0_of_ptes {K : KLayoutP} {s : S} (W : WalkP st K s) (h0 : (0#u64) ∉ K.ptes) :
    ∀ asid va, localinv.small_page_entry st s asid va ≠ ok (some 0#u64) :=
  fun asid va he => h0 (W.lf asid va 0#u64 he).1

end ne0

/-! ## 2. The VM layout fact without what `VtxBundle4` gives -/

section tab
variable {K : KLayoutP} {E : U64 → U64}

/-- **[S] The VM layout fact, narrowed** (module docstring): `VmPwe` (`nov`, `tab`), the ASID-table words are not
user words (`tabu`), the named pools' words are `VsW` words (`pool`). `VmPweT`'s remaining content (the table
words aligned and of region `.none`) is `RegionOKX.asidT` of the epoch's `VtxBundle4`. Justification of the three
[S] fields: as `VmPwe` / `VmPweT` (P2/E2EPVX11AE.lean, P2/E2EPVX11AG.lean: `layout.rs` `ASID_TABLE` in the
kernel-global block, `objects.rs` `create_arch_object` for ASID pools). -/
structure VmPweU (K : KLayoutP) (E : U64 → U64) : Prop extends VmPwe K E where
  /-- [S] The ASID-table words are not user words (kernel-global block). -/
  tabu : ∀ hi : U64, hi.val < 2048 → atAF K.ksb hi ∉ K.user
  /-- [S] The named pools' words are `VsW` words (ASID pools are retyped arch objects). -/
  pool : ∀ hi : U64, hi.val < 2048 → ∀ lo : U64, lo.val < 512 → E (atAF K.ksb hi) ≠ 0#u64 →
    VsW K.toKLayout (peAF (E (atAF K.ksb hi)) lo)

/-- **`VmPweT` from `VmPweU` and the layout's `RegionOKX`** (`asidT`). -/
theorem VmPweU.toT (h : VmPweU K E) (X : RegionOKX K.toKLayout) : VmPweT K E :=
  { toVmPwe := h.toVmPwe
    tabw := fun hi hhi => ⟨⟨(X.asidT hi hhi).2, (X.asidT hi hhi).1, h.tabu hi hhi⟩,
      fun lo hlo hne => h.pool hi hhi lo hlo hne⟩ }

/-- `VmPweU` is part of `VmPweT`. -/
theorem VmPweT.toU (h : VmPweT K E) : VmPweU K E :=
  { toVmPwe := h.toVmPwe
    tabu := fun hi hhi => (h.tabw hi hhi).1.2.2
    pool := fun hi hhi lo hlo hne => (h.tabw hi hhi).2 lo hlo hne }

end tab

/-! ## 3. `ExecVX4e` and the embeddings -/

section exec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {ι : Type}

/-- **`ExecVX4d` whose VM serial exits give the narrowed [S] layout fact `VmPweU`.** -/
inductive ExecVX4e (LP : PathsP ι)
    (SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop)
    (P : LocPlat st arI AR MR) (s0 : Cfg U64 U64 U64 U64) (K0 : KLayoutP) (Ch0 : S → Prop) :
    Cfg U64 U64 U64 U64 → KLayoutP → (S → Prop) → (U64 → U64) → Prop
  | refl : ExecVX4e LP SF P s0 K0 Ch0 s0 K0 Ch0 s0.mem
  | step {s s' : Cfg U64 U64 U64 U64} {K K' : KLayoutP} {Ch Ch' : S → Prop} {c : U64} {E : U64 → U64} :
      ExecVX4e LP SF P s0 K0 Ch0 s K Ch E → Step s c s' → Fl4StepVX4 LP SF P s K Ch c s' K' Ch' →
      /- [S] the narrowed VM layout fact at a VM serial exit -/
      (SerStep s c → K'.vcpus ≠ ∅ → VmPweU K' s'.mem) →
      ExecVX4e LP SF P s0 K0 Ch0 s' K' Ch' (if SerStep s c then s'.mem else E)
  | hw {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {Ch : S → Prop} {E : U64 → U64} {v a x : U64} :
      ExecVX4e LP SF P s0 K0 Ch0 s K Ch E → HwStepP K s v a x → ExecVX4e LP SF P s0 K0 Ch0 (hwCfg s a x) K Ch E
  | mmu {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {Ch : S → Prop} {E : U64 → U64} {a x : U64} :
      ExecVX4e LP SF P s0 K0 Ch0 s K Ch E → MmuAD (PWE K E) s.mem a x →
      ExecVX4e LP SF P s0 K0 Ch0 (hwCfg s a x) K Ch E

/-- **An `ExecVX4e` run is an `ExecVX4d` run** (start facts mapped pointwise; `VmPweT` from `VmPweU` and the exit's
`VtxBundle4`). -/
theorem execVX4d_of_e {LP : PathsP ι}
    {SF SF' : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι →
      Prop}
    (hSF : ∀ Ch K m hK hU c hs q i, SF Ch K m hK hU c hs q i → SF' Ch K m hK hU c hs q i)
    {P : LocPlat st arI AR MR} {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop}
    {E : U64 → U64} (h : ExecVX4e LP SF P s0 K0 Ch0 s K Ch E) : ExecVX4d LP SF' P s0 K0 Ch0 s K Ch E := by
  induction h with
  | refl => exact .refl
  | @step s1 s1' K1 K1' Ch1 Ch1' c1 E1 _ hS g hPw ih =>
    refine .step ih hS ⟨g.arm, fun p0 k W hph hK hU => ?_, g.ser, g.serG, g.keep⟩ (fun hs hne => ?_)
    · obtain ⟨i, hi⟩ := g.start p0 k W hph hK hU
      exact ⟨i, hSF _ _ _ _ _ _ _ _ _ hi⟩
    · rcases g.ser hs with ⟨-, nv, -⟩ | ⟨-, -, hV⟩
      · exact (hne nv).elim
      · exact (hPw hs hne).toT hV.b.ul.rx
  | hw _ hH ih => exact .hw ih hH
  | mmu _ hH ih => exact .mmu ih hH

/-- **An `ExecVX4d` run is an `ExecVX4e` run** (start facts mapped pointwise; `VmPweT.toU`). -/
theorem execVX4e_of_d {LP : PathsP ι}
    {SF SF' : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι →
      Prop}
    (hSF : ∀ Ch K m hK hU c hs q i, SF Ch K m hK hU c hs q i → SF' Ch K m hK hU c hs q i)
    {P : LocPlat st arI AR MR} {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop}
    {E : U64 → U64} (h : ExecVX4d LP SF P s0 K0 Ch0 s K Ch E) : ExecVX4e LP SF' P s0 K0 Ch0 s K Ch E := by
  induction h with
  | refl => exact .refl
  | @step s1 s1' K1 K1' Ch1 Ch1' c1 E1 _ hS g hPw ih =>
    refine .step ih hS ⟨g.arm, fun p0 k W hph hK hU => ?_, g.ser, g.serG, g.keep⟩
      (fun hs hne => (hPw hs hne).toU)
    obtain ⟨i, hi⟩ := g.start p0 k W hph hK hU
    exact ⟨i, hSF _ _ _ _ _ _ _ _ _ hi⟩
  | hw _ hH ih => exact .hw ih hH
  | mmu _ hH ih => exact .mmu ih hH

end exec

/-! ## 4. The PageMap start without `PmRoot` -/

section slot
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)

/-- **The PageMap entry part of the VM start entry without `PmRoot`** (module docstring; `PmRoot` is
`pmRoot_of_qf`). -/
def PmEntG3 (j : InvArg S) (K : KLayoutP) (m : U64 → U64) (s : S) : Prop :=
  PmQF st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K m s ∧ PmEx st j.p s ∧ WalkP st K s ∧
    ∀ asid va, localinv.small_page_entry st s asid va ≠ ok (some 0#u64)

/-- **The PageMap slot's start fact in a VM epoch, gen 18**: `PmStartX` with `InvEntV9` [S] at `PmEntG3`. -/
def PmStartX3 (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64) (hs : U64 → Prop)
    (q : SP) (j : InvArg S) : Prop :=
  K.vcpus ≠ ∅ ∧ ∃ h : PmPremX st j K, ∃ (σ : S) (a : A),
    InvEntV9 st K (PmEntG3 st j K m) σ ∧
    L.cpu σ = c ∧ j.Locks σ = hs ∧ (∀ x, Aligned x → ¬ x ∈ K.user → L.mem σ x = m x) ∧
    q = (pmPathX st ar hA hm j K m hK hU h).body σ a

variable {st ar hA hm}

/-- **`PmStartX` from `PmStartX3`** (`PmRoot` by `pmRoot_of_qf`). -/
theorem pmStartX_of3 {K : KLayoutP} {m : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64}
    {hs : U64 → Prop} {q : SP} {j : InvArg S} (h : PmStartX3 st ar hA hm K m hK hU c hs q j) :
    PmStartX st ar hA hm K m hK hU c hs q j := by
  obtain ⟨hv, hp, σ, a, he, hc, hl, hμ, hq⟩ := h
  obtain ⟨hQ, hEx, hW, h0⟩ := he.ent.2
  exact ⟨hv, hp, σ, a, ⟨he.hz, ⟨he.ent.1, hQ, hEx, pmRoot_of_qf hQ, hW, h0⟩, he.qps⟩, hc, hl, hμ, hq⟩

/-- **`PmStartX3` from `PmStartX`** (forget `PmRoot`). -/
theorem pmStartX3_of {K : KLayoutP} {m : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64}
    {hs : U64 → Prop} {q : SP} {j : InvArg S} (h : PmStartX st ar hA hm K m hK hU c hs q j) :
    PmStartX3 st ar hA hm K m hK hU c hs q j := by
  obtain ⟨hv, hp, σ, a, he, hc, hl, hμ, hq⟩ := h
  obtain ⟨hQ, hEx, -, hW, h0⟩ := he.ent.2
  exact ⟨hv, hp, σ, a, ⟨he.hz, ⟨he.ent.1, hQ, hEx, hW, h0⟩, he.qps⟩, hc, hl, hμ, hq⟩

end slot

/-! ## 5. The top -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- The start facts of gen 18: `StartAD` ⊕ `PmStartX3`. -/
abbrev StartAD3 {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl7 st Cs Ω Sg Ac Locks) :=
  fun (Ch : S → Prop) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
      (hs : U64 → Prop) (q : SP) =>
    Sum.elim (StartAD st ar hA a0 B (arI := arI) (AR := AR) (MR := MR) Ch K m hK hU c hs q)
      (PmStartX3 st ar hA (masksWr_plain st) K m hK hU c hs q)

theorem startAD2_of3 {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl7 st Cs Ω Sg Ac Locks) :
    ∀ Ch K m hK hU c hs q i, StartAD3 st ar hA a0 B (arI := arI) (AR := AR) (MR := MR) Ch K m hK hU c hs q i →
      StartAD2 st ar hA a0 B (arI := arI) (AR := AR) (MR := MR) Ch K m hK hU c hs q i := by
  intro Ch K m hK hU c hs q i h
  rcases i with i | j
  · exact h
  · exact pmStartX_of3 h

theorem startAD3_of2 {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl7 st Cs Ω Sg Ac Locks) :
    ∀ Ch K m hK hU c hs q i, StartAD2 st ar hA a0 B (arI := arI) (AR := AR) (MR := MR) Ch K m hK hU c hs q i →
      StartAD3 st ar hA a0 B (arI := arI) (AR := AR) (MR := MR) Ch K m hK hU c hs q i := by
  intro Ch K m hK hU c hs q i h
  rcases i with i | j
  · exact h
  · exact pmStartX3_of h

/-- **FL4 end to end with the host walker's A/D writes, every U1 slot and PageMap in native and VM epochs, gen 18**
(module docstring). Premises: `serializable_fl4_localAD2`'s (`P`, [P] `hIoa`, `B` = [P] `cs` / [P] `lk`, `h0`,
`hA0`, `hB`, `hc0`, `hM0`, the execution, `hq`), with the execution over `ExecVX4e` ([P] `MmuAD`, [S] `VmPweU` at
VM serial exits) and the start facts `StartAD3` ([S] `InvEntV9` at `PmEntG3` for the VM-epoch PageMap start).
No [W]. -/
theorem serializable_fl4_localAD3 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl7 st Cs Ω Sg Ac Locks)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} {E : U64 → U64} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecVX4e (famAD2 st ar hA a0 B) (StartAD3 st ar hA a0 B (arI := arI) (AR := AR) (MR := MR))
      P s0 K0 Ch0 s K Ch E)
    (hq : NoLoc s) :
    ∃ ℓ : List SP, ℓ.Perm s.log ∧ RunAll ℓ s0.mem s.mem :=
  serializable_fl4_localAD2 st ar hA a0 P hIoa B h0 hA0 hB hc0 hM0
    (execVX4d_of_e (startAD2_of3 st ar hA a0 B) h) hq

/-- **`serializable_fl4_localAD2` from `serializable_fl4_localAD3`** (AD2's premises and conclusion verbatim): AD3
asks nothing AD2 does not. -/
theorem serializable_fl4_localAD2of3 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl7 st Cs Ω Sg Ac Locks)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} {E : U64 → U64} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecVX4d (famAD2 st ar hA a0 B) (StartAD2 st ar hA a0 B (arI := arI) (AR := AR) (MR := MR))
      P s0 K0 Ch0 s K Ch E)
    (hq : NoLoc s) :
    ∃ ℓ : List SP, ℓ.Perm s.log ∧ RunAll ℓ s0.mem s.mem :=
  serializable_fl4_localAD3 st ar hA a0 P hIoa B h0 hA0 hB hc0 hM0
    (execVX4e_of_d (startAD3_of2 st ar hA a0 B) h) hq

end top

end
end Fl4Proofs.P2.E2EP
