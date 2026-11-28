/-
# P2 (line vmscope, gen 10): the Delete PTE arm in VM epochs — `serializable_fl4_localVX10`

`serializable_fl4_localVX9` (P2/E2EPVX9.lean) runs vx, vt, io, st, irq, sl, CNodeDelete (no PTE lock) and Copy /
Mint in VM epochs; the Delete PTE arm (`delPteSlot`, U1's native slot) ran only in native epochs. This module adds it:

* record **`DelPtePremX`** (`lk` [P]: VX8's `InvPremX.lk`, the locks kept by an aligned user write at an `InvLX`
  state; `cs`: the index's cores below 64, the convention natively given by `DelPtePrem.hCs` from the bundle's
  `csLt`), with `delPtePremX_planLocks` (satisfiable at the canonical lock map);
* `delPtePathX` = E2EPVX10A's **`inv_localPathPV`** (`ownP`, VCPUs allowed, no bundle), **`delPteSlotVX`**;
* start fact **`DelPteStartX`**: `K.vcpus ≠ ∅`, the record, a start state with VX9's **`InvEntV9`** [S] whose entry
  part `G` is `InvQFP` (U1's PTE-arm entry fact, as natively in `DelPteStart`) **∧ `WalkP`** (the walk fact; E2EPVX10A),
  core / locks / memory link as `GlueAt` [P], the armed program the path's body;
* **`delPteStartX_at`**: `StartAt` of the slot from the start fact and the epoch's `VtxBundle4` (`InvLX` at the start
  state with its closure along user writes by VX9D's **`invEntP_cl`**; `InvVF` from the bundle; `KsNoE` from
  `InvEntV9.qps`);
* **`StartVX10`**, **`serializable_fl4_localVX10G`**, **`serializable_fl4_localVX10`** = VX9's family ⊕ `delPteSlotVX`,
  glue `ExecVX4`.

Slots starting in VM epochs now: vx, vt, io, st, irq, sl, CNodeDelete (no PTE lock), Copy / Mint, **CNodeDelete PTE
arm**. Not yet: vmF / vmR.

## Premise diff vs `serializable_fl4_localVX9`
| where | VX9 | VX10 |
|---|---|---|
| Delete PTE-arm record | native only (`DelPtePrem`: `nv`, `bunS`, `lk` [P] at `SlJAt` states) | also VM epochs: `DelPtePremX.lk` [P] (= `InvPremX.lk`), `cs` (convention) |
| its start entry | native (`Ch σ ∧ InvQFP`, `CvP` from the epoch start) | VM epochs: `InvEntV9` [S] (`hz`, `ent`, `qps`; the record VX9 already has) with `G := InvQFP ∧ WalkP`; `GlueAt` data [P] |
No new [J], no [W], no new [S] record: the new [S] content is the `WalkP` conjunct folded into `InvEntV9.ent`'s `G`.

## [S] justification of `WalkP` (Rust: fl4-core `arch/x86_64/vspace.rs` `find_vspace_for_asid`, `lookup_pt_slot`,
`localinv.rs` `small_page_entry` / `plan_with` / `add_pte`, `arch/x86_64/objects.rs` `create_arch_object`, `vcpu.rs`)
* walk reads: `find_vspace_for_asid` reads the ASID-table word (ks block) and the pool entry (an `ASIDPool` object
  word); `lookup_pt_slot` reads the PML4 / PDPT / PD entries of paging objects. All are untyped-retyped paging / pool
  objects (`create_arch_object`), never `bits::VCPU` objects (so no `VData` word), never user frames, and no leaf PT
  entry is read before the leaf (the walk stops at the PD entry naming the PT). Natively `SlJAtZ.vsRdX` with
  `ptesR_sub` at `CvP`. A guest writes only its VCPU's data words and guest frames (`HwStepP`), so this holds in a VM
  epoch as at the last native state.
* leaf: the entry `small_page_entry` returns is a word of a PT object (`VsW`: aligned, region `.none`, not user;
  natively `SlJAtZ.leafVsW`) and is in `K.ptes` (the epoch's `ptesR` at the epoch-start memory, whose gate words the
  start state shares: natively `ptesR_of_spe`; the plan's PTE lock `p.locks[p.pte]` is that entry, `add_pte`).
The closure of `WalkP` under user writes is proved (`walkP_wr`), as VX9's closure of the rest of `InvEntV9`.

## [P]s
`DelPtePremX.lk` = `InvPremX.lk` (fl4-sync `local_invocation` locks the plan's objects; `planLocks p` is
state-independent). `GlueAt` data as every slot.

No sorry / admit / native_decide / bv_decide. No existing statement or file changed except the root import list.
-/
import Fl4Proofs.P2.E2EPVX10A
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld InW RegionOK LayP)
open Fl4Proofs.P2.E2E (StartAt SP)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll)

noncomputable section
open Classical

section slot
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)

/-- **The Delete PTE-arm slot's record in VM epochs** (module docstring). -/
structure DelPtePremX (j : InvArg S) (K : KLayoutP) : Prop where
  /-- [P] (VX8's `InvPremX.lk`: U1's `lk` read at `InvLX` states). -/
  lk : ∀ s b v, (∃ F, InvLX st F K.toKLayout s) → b ∈ K.user → Aligned b → j.Locks (L.wr s b v) = j.Locks s
  /-- The index's cores are below 64 (convention; natively `DelPtePrem.hCs`). -/
  cs : ∀ c ∈ j.Cs, c.val < 64

/-- The slot's path where its record holds (E2EPVX10A's `inv_localPathPV`). -/
noncomputable def delPtePathX (j : InvArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (h : DelPtePremX st j K) :
    E2E.LocalPath (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) :=
  inv_localPathPV (Cs := j.Cs) (Ω := j.Ω) (Sg := j.Sg) (Ac := j.Ac) (Locks := j.Locks) ar hA j.number j.p hm
    h.cs K m hK hU (fun s b v hJ hb hba => h.lk s b v ⟨_, hJ⟩ hb hba)

/-- **The Delete PTE-arm slot in VM epochs, under `ownP`.** -/
noncomputable def delPteSlotVX : PathsP (InvArg S) :=
  fun j K m hK hU => if h : DelPtePremX st j K then delPtePathX st ar hA hm j K m hK hU h
    else E2EV.LocalPath.void (fl4Dflt st ar hm)
      (fun x hx => Fl4Proofs.P2.ko_aligned hK.base.base hU.base.base x hx)

theorem delPteSlotVX_pos {j : InvArg S} {K : KLayoutP} {m : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K}
    (h : DelPtePremX st j K) : delPteSlotVX st ar hA hm j K m hK hU = delPtePathX st ar hA hm j K m hK hU h :=
  dif_pos h

/-- **The Delete PTE-arm slot's start fact in a VM epoch** (module docstring): the record, a start state with
`InvEntV9` [S] at `G := InvQFP ∧ WalkP`, core / locks / memory link ([P], as `GlueAt`), the armed program the path's
body. -/
def DelPteStartX (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64) (hs : U64 → Prop)
    (q : SP) (j : InvArg S) : Prop :=
  K.vcpus ≠ ∅ ∧ ∃ h : DelPtePremX st j K, ∃ (σ : S) (a : A),
    InvEntV9 st K (fun s => InvQFP st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K.toKLayout m s ∧ WalkP st K s) σ ∧
    L.cpu σ = c ∧ j.Locks σ = hs ∧ (∀ x, Aligned x → ¬ x ∈ K.user → L.mem σ x = m x) ∧
    q = (delPtePathX st ar hA hm j K m hK hU h).body σ a

variable {st ar hA hm}

/-- **`StartAt` of the Delete PTE-arm slot in a VM epoch** from its start fact and the epoch's bundle (the closure
of the entry facts along user writes: VX9D's `invEntP_cl`). -/
theorem delPteStartX_at {K : KLayoutP} {μ : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64}
    {hs : U64 → Prop} {q : SP} {j : InvArg S} (E : VtxBundle4 st L K)
    (h : DelPteStartX st ar hA hm K μ hK hU c hs q j) :
    StartAt (delPteSlotVX st ar hA hm j K μ hK hU) c hs μ q := by
  obtain ⟨-, hp, σ, a, he, hc, hl, hμ, rfl⟩ := h
  rw [delPteSlotVX_pos st ar hA hm hp]
  have hcl := invEntP_cl (st := st) hK.base.base hU.base.base E.la he.hz E.b.ul hp.cs
    (fun s b v hJ hb hba => hp.lk s b v ⟨_, hJ⟩ hb hba) ⟨he.ent.1, he.ent.2.1⟩
  have hJ : InvLX st (fun _ => True) K.toKLayout σ :=
    ⟨hK.base.base, hU.base.base, E.la, E.b.ul, he.hz, fun s' hr => ⟨(hcl s' hr).1, trivial⟩⟩
  exact ⟨σ, a, ⟨hJ, he.ent.2.1, he.ent.2.2, he.qps.ks, ⟨E.b.vu, E.ko⟩⟩, hc, hl, hμ, rfl⟩

/-- **`DelPtePremX` holds for every index with a state-independent lock map and cores below 64** (the canonical
`planLocks p`). -/
theorem delPtePremX_planLocks {j : InvArg S} {K : KLayoutP} {p : localinv.Plan} (e : j.Locks = planLocks p)
    (hc : ∀ c ∈ j.Cs, c.val < 64) : DelPtePremX st j K :=
  ⟨fun _ _ _ _ _ _ => by rw [e]; rfl, hc⟩

end slot

/-! ## The tops -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **The start facts, gen 10** (VX9's, plus `DelPteStartX` for the Delete PTE arm in VM epochs). -/
def StartVX10 {ιN : Type}
    (SFN : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ιN → Prop)
    (Ch : S → Prop) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (q : SP) :
    ((((((((ιN ⊕ VxArg S) ⊕ VtArg S) ⊕ IoArg S) ⊕ StArg S) ⊕ IrqArg S) ⊕ SlArg S) ⊕ InvArg S) ⊕ InvArg S) ⊕
      InvArg S → Prop
  | .inl i => StartVX9 st ar hA hm hSt a0 SFN Ch K m hK hU c hs q i
  | .inr j => DelPteStartX st ar hA hm K m hK hU c hs q j

end top

end
end Fl4Proofs.P2.E2EP
