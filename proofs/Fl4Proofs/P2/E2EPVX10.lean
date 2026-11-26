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

/-- **FL4 end to end, gen 10, generic in the native family** (`serializable_fl4_localVX9G` with `delPteSlotVX`
added). -/
theorem serializable_fl4_localVX10G (P : LocPlat st arI AR MR) {ιN : Type} (LN : PathsP ιN)
    {SFN : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ιN → Prop}
    (hSFN : ∀ (Ch : S → Prop) (K : KLayoutP) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K) c hs q i,
      (∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) →
      (∃ s1 : Cfg U64 U64 U64 U64, (K.vcpus = ∅ ∧ K.ptes = ptesR K s1.mem) ∧ ∀ x, GateW K x → s.mem x = s1.mem x) →
      SFN Ch K s.mem hK hU c hs q i → StartAt (LN i K s.mem hK hU) c hs s.mem q)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} (h0 : Init s0) (hA0 : ArmInv s0)
    (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecVX4 (PathsP.sum (PathsP.sum (PathsP.sum (PathsP.sum (PathsP.sum (PathsP.sum (PathsP.sum (PathsP.sum
        (PathsP.sum LN
        (vxSlotPV st ar hA hm)) (vtSlotPV st ar hA hm)) (ioSlotPX st ar hA hm)) (stSlotPX st ar hA hm))
        (irqSlotPX st ar hA hm)) (slSlotPX st ar hA hm hSt a0)) (invSlotVX st ar hA hm)) (cmSlotVX st ar hA hm))
        (delPteSlotVX st ar hA hm))
      (StartVX10 st ar hA hm hSt a0 SFN) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  obtain ⟨hK0, hU0⟩ := okP_R hB hc0
  have hX := (execVX_of_VX4 hc0.1 h).1
  refine serializable_e2eP _ h0 hA0 hK0 hU0 hM0 (execP_of_VX P ?_ h0 hA0 hB hc0 hM0 hX).1 hq
  intro Ch K s hK hU c hs q i hN hsf
  obtain ⟨hV, hsf⟩ := hsf
  rcases i with ((((((((i | j) | j) | j) | j) | j) | j) | j) | j) | j
  · have hsf' : K.vcpus = ∅ ∧ SFN Ch K s.mem hK hU c hs q i := hsf
    obtain ⟨nv, hsf'⟩ := hsf'
    obtain ⟨hX, hE⟩ := hN nv
    exact hSFN Ch K s hK hU c hs q i hX.chainOf hE hsf'
  · have hsf' : VxStartV2 st ar hA hm K s.mem hK hU c hs q j := hsf
    exact vxStartV_at st ar hA hm (vxStartV_of_V2 (hV (vxStartV2_ne hsf')).b hsf')
  · have hsf' : VtStartV4 st ar hA hm K s.mem hK hU c hs q j := hsf
    exact vtStartV2_at (hV hsf'.1).b (vtStartV2_of_V4 (hV hsf'.1).b hsf')
  · have hsf' : IoStartX5 st ar hA hm K s.mem hK hU c hs q j := hsf
    exact ioStartX_at (hV hsf'.1) (ioStartX_of_X5 (hV hsf'.1) hsf')
  · have hsf' : StStartX st ar hA hm K s.mem hK hU c hs q j := hsf
    exact stStartX_at (hV hsf'.1) hsf'
  · have hsf' : IrqStartX st ar hA hm K s.mem hK hU c hs q j := hsf
    exact irqStartX_at (hV hsf'.1) hsf'
  · have hsf' : SlStartX st ar hA hm hSt a0 K s.mem hK hU c hs q j := hsf
    exact slStartX_at (hV hsf'.1) hsf'
  · have hsf' : InvStartX9 st ar hA hm K s.mem hK hU c hs q j := hsf
    exact invStartX_at (hV hsf'.1) (invStartX_of9 (hV hsf'.1) hsf')
  · have hsf' : CMStartX9 st ar hA hm K s.mem hK hU c hs q j := hsf
    exact cmStartX_at (hV hsf'.1) (cmStartX_of9 (hV hsf'.1) hsf')
  · have hsf' : DelPteStartX st ar hA hm K s.mem hK hU c hs q j := hsf
    exact delPteStartX_at (hV hsf'.1) hsf'

/-- **FL4 end to end with every U1 slot in native epochs and the VM-exit, VM-timer, I/O-port, `TCB_SetTimer`,
timer-interrupt, syscall, CNodeDelete (both arms) and Copy / Mint slots in VM epochs, gen 10** (module docstring):
`serializable_fl4_localVX9` with `delPteSlotVX` added (record `DelPtePremX`: `lk` [P], `cs` convention; start entry
VX9's `InvEntV9` [S] at `G := InvQFP ∧ WalkP`). No new [J], no [W], no new [S] record. -/
theorem serializable_fl4_localVX10 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} (h0 : Init s0) (hA0 : ArmInv s0)
    (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecVX4 (PathsP.sum (PathsP.sum (PathsP.sum (PathsP.sum (PathsP.sum (PathsP.sum (PathsP.sum (PathsP.sum
        (PathsP.sum (PathsP.sum (fl4LocW11JA st ar hA hm hSt a0)
          (PathsP.sum (PathsP.sum (delPteSlot st ar hA hm) (invSlotU st ar hA hm)) (cmSlotU st ar hA hm)))
        (vxSlotPV st ar hA hm)) (vtSlotPV st ar hA hm)) (ioSlotPX st ar hA hm)) (stSlotPX st ar hA hm))
        (irqSlotPX st ar hA hm)) (slSlotPX st ar hA hm hSt a0)) (invSlotVX st ar hA hm)) (cmSlotVX st ar hA hm))
        (delPteSlotVX st ar hA hm))
      (StartVX10 st ar hA hm hSt a0 (StartU1 st ar hA hm hSt a0 arI AR MR (StartInvU2 st ar hA hm)))
      P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  refine serializable_fl4_localVX10G st ar hA hm hSt a0 P _ ?_ h0 hA0 hB hc0 hM0 h hq
  intro Ch K s hK hU c hs q i hC hE hsf
  rcases i with i | ((j | j) | j)
  · exact startAt_U st ar hA hm hSt a0 P hIoa hC hE hsf
  · exact delPteStart_at st ar hA hm hC hE hsf
  · exact invStartU2_at st ar hA hm hC hE hsf
  · exact cmStartU2_at st ar hA hm hC hE hsf

end top

end
end Fl4Proofs.P2.E2EP
