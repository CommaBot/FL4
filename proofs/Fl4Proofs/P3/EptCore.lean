/-
P3 (line mmuAD, gen 42b0): **the flat guest-table record `EptCore` and `VmEptState := VmState ∧ EptCore`**
(architect contract mmuAD 42 item 4, agreed 08:29Z: `VmEptState = JAtZB ∧ VcpuCore ∧ EptCore`, `VcpuCore ⟂ EptCore`).
Interface draft: the record, its boot case, the embeddings from `VmState`, and its frame lemmas for the steps that
write no guest-table word. The EPT-touching steps (table / frame map and unmap, ASID-pool assign of an EPT root,
SetEPTRoot, EPT finalise / detype, retype of EPT objects) are left to 42b.

## The record `EptCore X XL th s σ` (no field mentions a VCPU, `V`, or a `VcpuCore` word)

* `rel : EptRel X XL σ (L.mem s)` (gen 41, P3/JAtZV3EptRel): every `t ∈ X` is the spec table `.ept (XL t) es` with
  FL4's words related to `es` up to the hardware-written bits (root: entries < 256 only), every spec guest table is
  at some `t ∈ X`, `t` 4 KiB aligned. FL4: retype zeroes the object (untyped.rs l. 237-246, objects.rs l. 446
  "already zero"; spec `defaultArchObject` `.ept l 0`, Structs l. 472-475); the table entry `paddr | 7`
  (ept.rs l. 300) and the frame entry (`frame_entry`, ept.rs l. 95-116, l. 187) are the spec's `GuestPte.encode`
  words (VirtEptInv l. 222 / l. 235); unmap writes 0 (ept.rs l. 217 ↔ `guestUnmap`'s `storeGuestEntry tbl i 0`);
  a table unmap clears the table (ept.rs l. 271 ↔ VirtEptInv l. 230); `mark_core` writes only the upper halves of
  root words 510 / 511 (ept.rs l. 14, l. 43-54), outside the related root entries; the VMX EPTP has A/D off
  (fl4-arch-x86_64 vm.rs l. 1002), SVM's walker writes A/D (`eptHw` = 0x60).
* `capL : EptCapL th XL (L.mem s)` (gen 41): an `Ept p l …` slot cap has `l.val = XL p`. FL4: the level is fixed at
  creation (x86_64/objects.rs l. 46-50, from the object type), kept by every rewrite of the cap (ept.rs l. 273-282,
  l. 301-310; vspace.rs l. 1246 rewrites a level-0 cap at level 0) and by derivation (objects.rs l. 219-224 returns
  the cap itself); the spec object's level is the same constant (Structs l. 455-458, l. 472-475).
* `exte : JExtEpt X th s` (**the EPT half of `JExtV2`**, moved here from `VcpuCore.extv` in gen 42b1 by the
  architect's split, P3/VmState `jextV2_iff`): an `Ept p …` slot cap has `p ∈ X`, an EPT-mapped frame cap
  (`mapped ∧ is_ept`) needs `X ≠ ∅`. FL4: `Ept` caps are issued only by the retype of an EPT object
  (x86_64/objects.rs l. 46-50); a frame cap is marked `is_ept` only by `ept::map_frame` (ept.rs l. 173-186) after
  `ept::root` found a root (l. 150). Gen 42b12: plus `vtop` (`EptVTop`, P3/VmState): a mapped `Ept` slot cap's guest
  address is below `2^47` (FL4: the table map writes `vaddr: gpa` after `gpa < LIMIT`, ept.rs l. 290-310; the pool
  assign `vaddr: 0`, vspace.rs l. 1246; `derive_cap` copies verbatim). Gen 42b13: plus `anz` (`EptANz`, P3/VmState,
  the Architect's `hz0` decision (i)): a mapped `Ept` slot cap's ASID is nonzero (the pool assign's free-entry search
  skips `base + i = 0`, vspace.rs l. 1238; the table map copies the root cap's ASID).
* `tag : GuestTag X XL σ` (**the ASID-pool guest tag**; one-directional: tagged pool entry ⇒ level-0 root in `X`): every guest-tagged entry (`e &&& 1 = 1`) of a pool of the
  ASID table names a root of `X` at level 0. FL4: a tagged word is written only by `X86ASIDPoolAssign` from an
  unmapped level-0 `Ept` cap (vspace.rs l. 1227, l. 1250: `ptr | 1`; spec VirtEptInv l. 247-249 `r ||| 1`); an
  unmapped `Ept` cap is never copied (`derive_cap`, objects.rs l. 219-224, spec VSpace l. 388-389), so the assigned
  cap's copies are all mapped, and the final one's deletion clears the entry (`finalise`, objects.rs l. 266 →
  ept.rs l. 229-230 → `delete_asid`, vspace.rs l. 344-348) before the root's memory can be detyped; a pool leaving
  the ASID table (`delete_asid_pool`, vspace.rs l. 358-371) takes its entries with it. (The base already relates
  the pool words themselves, tag included: P3/VsRel's `pool`; this field adds what the tagged word *names*.)
* `ks`: each `t ∈ X` is off the kernel-global area `[ksb, ksb + 304384)` (as `JVm.ks` for the VCPUs). FL4: EPT
  objects are created only from RAM untypeds (untyped.rs l. 66 refuses non-frame objects from device untypeds),
  whose regions miss the kernel-state block.
* `sep`: no other spec object meets `t`'s 4 KiB (l4v `pspace_distinct` at `X`, as `JVm.sep` for the VCPUs).
* `ue : UnmappedEmpty` (**the Architect's field, gen 42b2**; native F1's `VsNamed.empty` / `uun` companion): the
  table `p` of an *unmapped* slot cap `Ept p l false a v` is all zero on both sides (FL4's 512 words, the spec's
  `.ept (XL p) 0`), no other slot holds an `Ept` cap to `p`, and no guest-tagged pool entry names `p`. FL4: the
  only producers of an unmapped `Ept` cap are the retype (one cap per new object, x86_64/objects.rs l. 46-50,
  which writes nothing: objects.rs l. 446 "The memory is already zero" — the object lies in the free part of a RAM
  untyped (untyped.rs l. 66 refuses non-frame objects from device untypeds), which is zero: P3's `UtCapP3.zero`
  (ScUtRetype l. 239, `ZeroRegion` above the free index), established by `reset_untyped`'s `clear_free`
  (untyped.rs l. 238-239, 246) and at boot; spec `.ept l 0`, Structs l. 472-475) and the table unmap (ept.rs l. 266 `is_final_capability`
  first, then `s.zero(ptr, 4096)` whenever the cap was mapped, l. 276-279, and the cap rewritten unmapped,
  l. 281-282; spec `tableUnmap`, VirtEptInv l. 186-191); an unmapped `Ept` cap is never copied (`derive_cap`,
  objects.rs l. 219-224); a level-0 cap is never unmapped (ept.rs l. 253) and becomes mapped exactly when
  `X86ASIDPoolAssign` writes its tagged pool entry (vspace.rs l. 1227, 1246, 1250); table / frame map writes only
  into a table found from a mapped root (`ept::root`, ept.rs l. 24-41); `mark_core` writes only a mapped root
  (l. 43-54; uniqueness: no unmapped cap to it); the hardware sets A/D bits only in present entries
  (`VmEptState.hwWr`'s `h0`). Not stated: "no present entry of another table names `p`" — false for an orphan
  table left behind by a root's deletion (the Architect: the walk field will be stated only for tables reachable
  from a tagged root).
* `eslot : EptSlotOK th (L.mem s)` (**the Architect's field, gen 42b6**; it replaces SetEPTRoot's former premise
  `hold` [J]): every TCB's `SLOT_EPT` (index 5) holds `Null` or a mapped level-0 `Ept` cap. FL4: slot 5 is written
  only by SetEPTRoot (tcb.rs l. 416-417: `cdt::delete`, then `cdt::insert` of `derive_cap` of a source checked
  `Ept { level: 0, mapped: true }` at l. 414; `derive_cap` returns an `Ept` cap unchanged, objects.rs l. 219-224);
  `install_tcb_cap` / `install_buffer` / boot write other TCB slots (tcb.rs l. 68-75, 88; boot.rs l. 714-716);
  `empty_slot` writes `Null` (cdt.rs l. 198-214); the delete loop's remainder for an `Ept` cap is `Null` (no
  zombie), and `cap_swap_for_delete` swaps only into a slot holding a Zombie / CNode / Thread cap, which this field
  excludes for slot 5; CSpace-lookup writers resolve only into CNodes; a fresh TCB is zero memory (objects.rs l. 446),
  i.e. `Null`; a level-0 cap is never unmapped (ept.rs l. 253). The generic constructors take the step's
  **`EptSlotStep`** (`h5`: each TCB of `th'` has slot 5 null, or a mapped level-0 `Ept`, or was a TCB of `th` with
  the cap kept); `EptSlotStep.ofSS` / `ofOne` give it for slot-keeping and one-slot steps.
* `walk : EptWalk σ` (**the Architect's reachable-table walk field, gen 42b8**; spec side only): in every guest table
  reachable from a guest-tagged root by walk steps (`GStep`: a present, non-large entry — in the related range, root
  entries below 256 — of a non-PT table), a walked entry names a spec guest table one level down (`eptChild`: root 0 →
  39 → 30 → 21). With `rel` this fixes FL4's `ept::lookup` (ept.rs l. 72-84) against `guestLookupSlot`: every table
  the walk reads is a table of `X` at the level the walk expects (P3/EptLookup). FL4: a present non-large entry of a
  non-PT table is written only by the table map (ept.rs l. 300, `paddr(ptr) | 7`) into the table `ept::slot` found
  for the cap's level, whose level is one above the cap's (`lookup` stops at shift `level`); the frame map writes a
  large entry (bit 7, `frame_entry` l. 100) into a PD, a 4 KiB entry into a PT, or 0 (l. 96-98); unmap writes 0
  (l. 217); the table unmap zeroes the table (l. 271); a new tagged root is a zero table (`ue`); new tables are zero
  (retype). Stated only for reachable tables (the Architect): an orphan root left by `delete_asid` (vspace.rs
  l. 344-348) may keep entries naming tables detyped later (their `unmap` finds no root, ept.rs l. 199-202). Kept
  (gen 42b8) by `frameI` / `frame` / `wrIn` / `frameT` / `growS` / `clear` through **`EptCore.walkZ`** (tables kept,
  zeroed or created zero; new tagged entries name zero tables: `EptWalk.keep`); `ofObj` / `entry` / `shrink` take it
  after the step as a hypothesis (`hwk`), as they take `ue`.
* `named : EptNamed` (**the Architect's field, gen 42b10**: l4v `valid_vs_lookup` with `unique_table_refs` for the guest
  tables below the root): a table `u` reached at a level `l ≠ 0` along a walk path `GPath σ hi lo gpa l u` (the
  tagged root of the ASID `(hi, lo)`, then `guestLookupSlot`'s entries for `gpa < 2^47`) has a mapped slot cap `Ept u l
  true a v` with `a`'s ASID bits `(hi, lo)` and `v = gKey gpa l` (`ex`), and every `Ept` cap to `u` is such a cap
  (`all`); plus `PoolInj` (no pool at two ASID-table indices, l4v `valid_asid_table`; no root named by two tagged
  entries). FL4: a non-root table becomes reachable only by the table map, which writes the entry `paddr(ptr) | 7`
  into the table `ept::slot` found from the cap's ASID and `gpa` and rewrites the (unique, unmapped: `ue`) cap to `ptr`
  as `Ept { mapped: true, asid, vaddr: gpa }` (ept.rs l. 300-310); a mapped `Ept` cap is copied only verbatim
  (`derive_cap`, objects.rs l. 219-224); the table unmap runs only on the final cap (`is_final_capability`, ept.rs
  l. 266) and clears the parent entry first; the root's tagged entry is written only from an unmapped root cap
  (`ue`: no tagged entry names it), into a free entry of a pool of the ASID table (vspace.rs l. 1220-1252); a pool
  enters the table only as a fresh object at a free index (`X86ASIDControlMakePool`). Corollary
  **`EptNamed.unmUnreach`**: an unmapped cap's table is reached at no nonzero level. Kept by `EptNamed.keep` / `frameA`
  / `ofSS` (paths after are paths before: `GPath.mono`; mapped non-root caps kept; caps after old or to an unmapped
  cap's table); the generic constructors (`frameI` / `frame` / `ofBS`, P3/EptStep2-3, P3/EptRetype) take it after the
  step as their last hypothesis (`hnm`, as `hwk`); `eptCore_empty` / the embeddings take the ASID table's
  injectivity (`htab`); `ofB`, `ofTK`, `wrIn`, `assignE`, `ofEmpty`, SetEPTRoot's insert and restart and the root
  finalisation prove it.
* `tbl` (**the Architect's static table field, gen 42b12**): every `t ∈ X` has a level `XL t ∈ {0, 39, 30, 21}` and
  `PaM t 4503599627366400` (its physical address, `t - PPTR_BASE`, is 4 KiB aligned and below `2^52`). FL4: the four
  EPT object types fix the level (x86_64/objects.rs l. 46-50; spec `defaultArchObject`, Structs l. 472-475), and EPT
  objects are carved from RAM untypeds inside the kernel window (untyped.rs l. 66), as the native page tables whose
  retype proves `PaM` for `VCapW`. Static: established at boot (`X = ∅`) and by the retype (`growS` / `grow` /
  `growZ` / `growSZ` take it for the new tables as their last hypothesis `htb`), kept by every other step (`X`, `XL`
  unchanged; `shrink` removes a table). It discharges the table map's former case hypotheses `hpa` / `hlv`
  (`EptCore.capTbl`, P3/EptStep1).

**Placement apartness, derived (not fields)**: from the base and `EptCore`, every table of `X` misses every other
object of `H` (`JAtZB.eptApartH`, `H t = .other 12` by `JAtZB.eptHeap`: `SpecCover.arch` + `ArchFitHyp`), hence every
TCB (whose VCPU word `VcpuCore.extv` / `vb` read) and every CNode / TCB slot; every word a native step writes
(`OObj`, **`JAtZB.oobjX`**); the VCPU list head (`JAtZB.eptHead`, `VcpuCore.vl`'s head); and with `VcpuCore.vm`
every VCPU object of `V` (**`EptCore.apartV`**, from `JVm.sep`). So `EptCore` carries no VCPU fact and `VcpuCore`
none about tables: the two records share only the parameters (`X`, the state).

## Constraint 1 (`VcpuCore ⟂ EptCore`), checked

`rvm : RunVmB` (P3/JExtV l. 159: TCB state and VCPU words), `vm : JVm V H s σ` (P3/JVm l. 49: `V`'s spec VCPU objects,
`H`'s `.other 15`, `ksb`, `sep` over *all* spec objects — a VCPU-side apartness, no EPT-specific term), `vl : VList`
(P3/JExtVList l. 275: the VCPU list head and `V`'s link words), `vb : VBind` (P3/JAtZBVcpu l. 122: `V`'s spec VCPU
objects and their TCB words): none mentions `X`, `.ept`, a guest table, `EptRel` or a pool entry. Of the other
fields only `extv` took `X` (`JExtV2 V X`); since gen 42b1 it is `JExtVcpu V` and the `X` half `JExtEpt X` is
`EptCore.exte`: **`VcpuCore` has no `X` parameter and `EptCore` none `V`**. `vo`, `vr`, `noIoTcb`, `rngOne` do not
mention `X`. (`rngOne : RngOne` is generic over every exact range class — physical, not untyped, not a frame — so it
already covers `Ept` caps (range `[p, p + 4096)`): all caps to one table lie in one chain, which EPT finalise /
delete reads through `is_final`. It stays in `VcpuCore` as the shared MDB fact.)

## Theorems

* (gen 42b4) `UnmappedEmpty.keepI` / `EptCore.frameI`: `keep` / `frame` generalised in place to slot `Ept` caps that
  are old caps of some slot (an unmapped one at its own slot, a mapped one possibly copied: SetEPTRoot's insert); the
  originals corollaries with their statements unchanged.
* `UnmappedEmpty.keep` (gen 42b2): `ue` across a step keeping every slot `Ept` cap, the table words, the spec's
  tables and adding no pool entry (used by `EptCore.frame` / `ofBS` / `ofB` / `ofTK`; `frame`'s cap hypothesis is
  now "same slot, same cap").
* `eptCore_empty` (boot, gen 41's `eptRel_empty`): `X = ∅` with no spec guest table, no tagged pool entry,
  `JExtEpt ∅` (no `Ept` slot cap, no EPT-mapped frame cap).
* Embeddings: **`VmState.toEpt`** (`VmState V` + `JExtEpt ∅` + no spec guest table + no tagged entry ⇒
  `VmEptState V ∅`), **`JAtZ.toVmEptState`** (native, through gen 42a2's `JAtZ.toVmState` and `JExtEpt.of_jext`),
  **`VmEptState.toV3`** (`VmEptState` + `IoOwnV` ⇒ `JAtZV3 V X`), `vmEptState_iff` (the `JAtZB ∧ VcpuCore ∧
  EptCore` reading). (Gen 42b0's `VcpuCore.dropX` / `VmState.toEptX` are gone with the split: `VcpuCore` has no `X`.)
* Frames: **`EptCore.frame`** (generic: memory writes outside the table words of `X`, slot `Ept` caps that keep
  pointer and level, the spec's tables at `X` kept, no new spec guest table, no new tagged pool entry, object sizes
  kept), **`EptCore.ofBS`** / **`ofB`** / **`ofTK`** (the native step shapes of `VcpuCore.ofBS` / `ofB` / `ofTK`:
  `OObj` writes miss the tables by `JAtZB.oobjX`), and `VmEptState.ofBS` / `ofB` / `ofTK` / `archV`.

Gen 42b12 statement change (the `tbl` field): `structure EptCore` only (`eptCore_empty` and the frames keep their
statements: `X = ∅`, resp. `X`, `XL` unchanged).

Gen 42b10 statement changes (the `named` field): `structure EptCore`; `eptCore_empty`, `VmState.toEpt`,
`JAtZ.toVmEptState` (+ `htab`); `EptCore.frameI`, `EptCore.frame`, `EptCore.ofBS`, `VmEptState.ofBS` (+ `hnm`).

Gen 42b19 (the Architect's goal 2): **`EptNamed.keepW`**, `EptNamed.keep` generalised to a per-path witness after
(`hex`) in place of "every mapped non-root cap kept"; `keep` is its corollary (statement unchanged). It lets
P3/EptDelRoot's `EptCore.ofEmpty` drop a mapped non-root cap whose table is unreachable or has another cap.
`EptNamed` itself is unchanged (its `ex` already quantifies over the reachable tables only).

No named premise in this module: `EptCore`'s fields are state invariants (true at boot, `eptCore_empty`; kept by
every step: the non-EPT steps by the frames here, the EPT steps in 42b), and the embeddings' / frames' hypotheses
are hypotheses of those theorems. The spec is not touched; gen 42b1 changed only this module's and P3/VmState's own
(mmuAD 42a–42b0) statements.
-/
import Fl4Proofs.P3.VmStateNat
import Fl4Proofs.P3.JAtZV3EptRel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-! ## Definitions -/

/-- `e` is an entry of a pool of the ASID table. -/
def GuestEntry (σ : Fl4Spec.State Unit) (e : Fl4Spec.ObjRef) : Prop :=
  ∃ hi p f lo, σ.archState.x64AsidTable hi = some p ∧ σ.kheap p = some (.archObj (.asidPool f)) ∧ f lo = some e

/-- **The ASID-pool guest tag** (module docstring): a guest-tagged pool entry names a root of `X` at level 0. -/
def GuestTag (X : Set U64) (XL : U64 → Nat) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ e, GuestEntry σ e → e &&& 1 = 1 → ∃ t ∈ X, t.bv = Fl4Spec.asidEntryRoot e ∧ XL t = 0

/-- No pool entry of the ASID table is guest-tagged (boot; native states). -/
def NoGuestTag (σ : Fl4Spec.State Unit) : Prop := ∀ e, GuestEntry σ e → e &&& 1 = 0

/-- **Unmapped `Ept` caps name empty, unshared, unassigned tables** (the Architect's `UnmappedEmpty`, gen 42b2; module
docstring): the table `p` of an unmapped `Ept p l false a v` slot cap is all zero on both sides (FL4's 512 words, the
spec's `.ept (XL p) 0`), no other slot holds an `Ept` cap to `p`, and no guest-tagged pool entry names `p`. -/
def UnmappedEmpty (th : TypedHeap) (XL : U64 → Nat) (m : U64 → U64) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ y, IsSlot th y → ∀ p l a v, capV m y = .Ept p l false a v →
    (∀ i : BitVec 9, m (eptA p i) = 0#u64) ∧ σ.kheap p.bv = some (.archObj (.ept (XL p) (fun _ => 0))) ∧
    (∀ y', IsSlot th y' → y' ≠ y → ∀ l' (mm : Bool) a' v', capV m y' ≠ .Ept p l' mm a' v') ∧
    (∀ e, GuestEntry σ e → e &&& 1 = 1 → Fl4Spec.asidEntryRoot e ≠ p.bv)

/-- A spec object `(o, ko)` misses the 4 KiB at `t`. -/
def EptApart (t : U64) (o : Fl4Spec.ObjRef) (ko : Fl4Spec.KernelObject) : Prop :=
  o.toNat + 2 ^ Fl4Spec.objBits ko ≤ t.val ∨ t.val + 4096 ≤ o.toNat

/-- **A TCB's `SLOT_EPT` holds null or a mapped level-0 `Ept` cap** (the Architect's `EptSlotOK`, gen 42b6; module
docstring). -/
def EptSlotOK (th : TypedHeap) (m : U64 → U64) : Prop :=
  ∀ t, th t = some .tcb → capV m (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 5)) = .Null ∨
    ∃ p a v, capV m (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 5)) = .Ept p 0#u64 true a v

/-- **What a step does to the TCBs' `SLOT_EPT`** (gen 42b6, the hypothesis `h5` of the generic `EptCore`
constructors): each TCB of `th'` has its `SLOT_EPT` null, or holding a mapped level-0 `Ept` cap, or it was a TCB of
`th` whose `SLOT_EPT` cap is kept. -/
def EptSlotStep (th th' : TypedHeap) (m m' : U64 → U64) : Prop :=
  ∀ t, th' t = some .tcb → capV m' (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 5)) = .Null ∨
    (∃ p a v, capV m' (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 5)) = .Ept p 0#u64 true a v) ∨
    (th t = some .tcb ∧
      capV m' (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 5)) = capV m (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 5)))

theorem EptSlotOK.step {th th' : TypedHeap} {m m' : U64 → U64} (h : EptSlotOK th m)
    (h5 : EptSlotStep th th' m m') : EptSlotOK th' m' := by
  intro t ht
  rcases h5 t ht with h0 | h1 | ⟨ht0, e⟩
  · exact Or.inl h0
  · exact Or.inr h1
  · rw [e]; exact h t ht0

/-- A TCB's `SLOT_EPT` is a slot. -/
theorem isSlot_eptSlot {th : TypedHeap} {t : U64} (ht : th t = some .tcb) :
    IsSlot th (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 5)) :=
  AbsSlot.isSlot ⟨t, rfl, Or.inr ⟨ht, 5, by decide, rfl⟩⟩

/-- `EptSlotStep` for a step keeping every slot's cap. -/
theorem EptSlotStep.ofSS {th : TypedHeap} {m m' : U64 → U64} (h : SlotsSame th m m') : EptSlotStep th th m m' :=
  fun _ ht => Or.inr (Or.inr ⟨ht, h.capV (isSlot_eptSlot ht)⟩)

/-- `EptSlotStep` for a step writing one slot `x`, null or with a mapped level-0 `Ept` cap, and keeping the others. -/
theorem EptSlotStep.ofOne {th : TypedHeap} {m m' : U64 → U64} {x : U64}
    (hcp : ∀ y, IsSlot th y → y ≠ x → capV m' y = capV m y)
    (hx : capV m' x = .Null ∨ ∃ p a v, capV m' x = .Ept p 0#u64 true a v) : EptSlotStep th th m m' := by
  intro t ht
  by_cases e : cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 5) = x
  · rw [e]; exact hx.imp id Or.inl
  · exact Or.inr (Or.inr ⟨ht, hcp _ (isSlot_eptSlot ht) e⟩)

/-- **The level a walk reaches through an entry of a level-`l` guest table** (FL4 `ept::lookup`, ept.rs l. 72-84:
the root, level 0, is read at shift 39 and a level-`l` table at shift `l`; the table an entry read at shift `s` names
is a level-`s` table, `Cap::Ept.level`): `none` for a PT (level 21), whose entries are leaves. -/
def eptChild : Nat → Option Nat
  | 0 => some 39
  | 39 => some 30
  | 30 => some 21
  | _ => none

/-- **Entry `i` of a level-`l` guest table is followed by a walk** (`ept::lookup` l. 76-80, `guestLookupSlot`): `l`
is not a PT, `i` is in the related range (root: below 256, `EptRel.obj`), and the entry is present and not large. -/
def GWalkE (l : Nat) (es : BitVec 9 → Fl4Spec.Word) (i : BitVec 9) : Prop :=
  (eptChild l).isSome ∧ (l ≠ 0 ∨ i.toNat < 256) ∧ es i &&& 1 ≠ 0 ∧ es i &&& 128 = 0

/-- One walk step between spec guest tables: `u` is named by a walked entry of the table `t`. -/
def GStep (σ : Fl4Spec.State Unit) (t u : Fl4Spec.ObjRef) : Prop :=
  ∃ l es i, σ.kheap t = some (.archObj (.ept l es)) ∧ GWalkE l es i ∧
    u = Fl4Spec.ptrFromPAddr (es i &&& Fl4Spec.guestPteAddress)

/-- **The walk field** (the Architect's reachable-table field, gen 42b8; module docstring): in every table reachable
by walk steps from a guest-tagged root, a walked entry names a spec guest table one level down (`eptChild`). Stated
only for reachable tables: an orphan table left by a root's deletion may name a detyped table. -/
def EptWalk (σ : Fl4Spec.State Unit) : Prop :=
  ∀ e, GuestEntry σ e → e &&& 1 = 1 → ∀ t, Relation.ReflTransGen (GStep σ) (Fl4Spec.asidEntryRoot e) t →
    ∀ l es i, σ.kheap t = some (.archObj (.ept l es)) → GWalkE l es i → ∀ c, eptChild l = some c →
      ∃ es', σ.kheap (Fl4Spec.ptrFromPAddr (es i &&& Fl4Spec.guestPteAddress)) = some (.archObj (.ept c es'))

theorem gWalkE_zero {l : Nat} {i : BitVec 9} : ¬ GWalkE l (fun _ => 0) i := fun h => h.2.2.1 (by simp)

/-- **`EptWalk` across a step that keeps or zeroes each guest table** (and keeps every table's level), with every new
tagged entry naming a zero table: the tables reachable after are reachable before or zero. -/
theorem EptWalk.keep {σ σ' : Fl4Spec.State Unit} (hW : EptWalk σ)
    (hobj : ∀ r l es, σ'.kheap r = some (.archObj (.ept l es)) →
      σ.kheap r = some (.archObj (.ept l es)) ∨ es = fun _ => 0)
    (hlev : ∀ r l es, σ.kheap r = some (.archObj (.ept l es)) → ∃ es', σ'.kheap r = some (.archObj (.ept l es')))
    (hge : ∀ e, GuestEntry σ' e → e &&& 1 = 1 →
      GuestEntry σ e ∨ ∃ l, σ'.kheap (Fl4Spec.asidEntryRoot e) = some (.archObj (.ept l fun _ => 0))) :
    EptWalk σ' := by
  intro e he h1 t ht
  -- every table reachable after is zero or reachable before (from a root tagged before)
  have key : ∀ u, Relation.ReflTransGen (GStep σ') (Fl4Spec.asidEntryRoot e) u →
      (∃ l, σ'.kheap u = some (.archObj (.ept l fun _ => 0))) ∨
      (GuestEntry σ e ∧ Relation.ReflTransGen (GStep σ) (Fl4Spec.asidEntryRoot e) u) := by
    intro u hu
    induction hu with
    | refl => exact (hge e he h1).symm.imp id (fun g => ⟨g, Relation.ReflTransGen.refl⟩)
    | tail _ hst ih =>
      obtain ⟨l, es, i, hk, hwe, rfl⟩ := hst
      rcases ih with ⟨l', hz⟩ | ⟨g, hr⟩
      · rw [hk] at hz; cases hz; exact (gWalkE_zero hwe).elim
      · rcases hobj _ l es hk with hk0 | hz
        · exact Or.inr ⟨g, hr.tail ⟨l, es, i, hk0, hwe, rfl⟩⟩
        · subst hz; exact (gWalkE_zero hwe).elim
  intro l es i hk hwe c hc
  rcases key t ht with ⟨l', hz⟩ | ⟨g, hr⟩
  · rw [hk] at hz; cases hz; exact (gWalkE_zero hwe).elim
  · rcases hobj _ l es hk with hk0 | hz
    · obtain ⟨es', h'⟩ := hW e g h1 t hr l es i hk0 hwe c hc
      exact hlev _ _ _ h'
    · subst hz; exact (gWalkE_zero hwe).elim

/-- Boot: no spec guest table, no walk obligation. -/
theorem EptWalk.empty {σ : Fl4Spec.State Unit} (hE : ∀ r l es, σ.kheap r ≠ some (.archObj (.ept l es))) :
    EptWalk σ := fun _ _ _ _ _ l es _ hk => (hE _ l es hk).elim

/-! ## The named-table field (gen 42b10) -/

/-- The pool entry of the ASID with high bits `hi` and low bits `lo` (`findGuestRoot`'s read, VirtEptInv l. 89-98). -/
def PoolAt (σ : Fl4Spec.State Unit) (hi : Fl4Spec.AsidHighIndex) (lo : Fl4Spec.AsidLowIndex)
    (e : Fl4Spec.ObjRef) : Prop :=
  ∃ p f, σ.archState.x64AsidTable hi = some p ∧ σ.kheap p = some (.archObj (.asidPool f)) ∧ f lo = some e

theorem PoolAt.guest {σ : Fl4Spec.State Unit} {hi : Fl4Spec.AsidHighIndex} {lo : Fl4Spec.AsidLowIndex}
    {e : Fl4Spec.ObjRef} (h : PoolAt σ hi lo e) : GuestEntry σ e :=
  let ⟨p, f, h1, h2, h3⟩ := h; ⟨hi, p, f, lo, h1, h2, h3⟩

/-- The guest address bits a level-`l` table's cap records (the decoder's mask, VirtEptInv l. 167). -/
def gKey (gpa : Fl4Spec.Word) (l : Nat) : Fl4Spec.Word := gpa &&& ~~~(((1 : Fl4Spec.Word) <<< l) - 1)

/-- **A walk path** (l4v `vs_lookup_table` for the guest tables): `u` is the level-`l` table reached from the tagged
root of the ASID `(hi, lo)` along the guest address `gpa` (`guestLookupSlot.go`: the level-`l` table is read at the
shift `eptChild l`). -/
inductive GPath (σ : Fl4Spec.State Unit) (hi : Fl4Spec.AsidHighIndex) (lo : Fl4Spec.AsidLowIndex)
    (gpa : Fl4Spec.Word) : Nat → Fl4Spec.ObjRef → Prop
  | root {e : Fl4Spec.ObjRef} : PoolAt σ hi lo e → e &&& 1 = 1 → GPath σ hi lo gpa 0 (Fl4Spec.asidEntryRoot e)
  | step {l c : Nat} {t : Fl4Spec.ObjRef} {es : BitVec 9 → Fl4Spec.Word} : GPath σ hi lo gpa l t →
      σ.kheap t = some (.archObj (.ept l es)) → eptChild l = some c → GWalkE l es (Fl4Spec.guestIndex gpa c) →
      GPath σ hi lo gpa c (Fl4Spec.ptrFromPAddr (es (Fl4Spec.guestIndex gpa c) &&& Fl4Spec.guestPteAddress))

/-- **ASID-table and tagged-root injectivity** (l4v `valid_asid_table`'s `inj_on` and the uniqueness of a guest
root's ASID): no pool sits at two ASID-table indices, and no two tagged pool entries name the same root. -/
structure PoolInj (σ : Fl4Spec.State Unit) : Prop where
  tab : ∀ hi hi' p, σ.archState.x64AsidTable hi = some p → σ.archState.x64AsidTable hi' = some p → hi = hi'
  root : ∀ hi lo hi' lo' e e', PoolAt σ hi lo e → PoolAt σ hi' lo' e' → e &&& 1 = 1 → e' &&& 1 = 1 →
    Fl4Spec.asidEntryRoot e = Fl4Spec.asidEntryRoot e' → hi = hi' ∧ lo = lo'

/-- **Every reachable guest table is named by its mapped caps** (the Architect's `EptNamed`, gen 42b10: l4v
`valid_vs_lookup` with `unique_table_refs`, for the guest tables below the root; module docstring): a table `u`
reached at a level `l ≠ 0` along `(hi, lo, gpa)` (`gpa < 2^47`) has a mapped cap `Ept u l true a v` with `a`'s ASID
bits `(hi, lo)` and `v` the address bits of `gpa` above `l` (`ex`); every `Ept` cap to `u` is such a cap (`all`); and
`PoolInj`. -/
structure EptNamed (th : TypedHeap) (m : U64 → U64) (σ : Fl4Spec.State Unit) : Prop where
  ex : ∀ hi lo gpa l u, gpa.toNat < 2 ^ 47 → GPath σ hi lo gpa l u → l ≠ 0 →
    ∃ y p lv a v, IsSlot th y ∧ p.bv = u ∧ lv.val = l ∧ Fl4Spec.asidHighBitsOf a.bv = hi ∧
      Fl4Spec.asidLowBitsOf a.bv = lo ∧ v.bv = gKey gpa l ∧ capV m y = .Ept p lv true a v
  all : ∀ hi lo gpa l u, gpa.toNat < 2 ^ 47 → GPath σ hi lo gpa l u → l ≠ 0 →
    ∀ y p lv (mm : Bool) a v, IsSlot th y → p.bv = u → capV m y = .Ept p lv mm a v →
      mm = true ∧ Fl4Spec.asidHighBitsOf a.bv = hi ∧ Fl4Spec.asidLowBitsOf a.bv = lo ∧ v.bv = gKey gpa l
  inj : PoolInj σ

/-- A path starts at a tagged pool entry of its ASID. -/
theorem GPath.root_tag {σ : Fl4Spec.State Unit} {hi : Fl4Spec.AsidHighIndex} {lo : Fl4Spec.AsidLowIndex}
    {gpa : Fl4Spec.Word} {l : Nat} {u : Fl4Spec.ObjRef} (h : GPath σ hi lo gpa l u) :
    ∃ e, PoolAt σ hi lo e ∧ e &&& 1 = 1 ∧ Relation.ReflTransGen (GStep σ) (Fl4Spec.asidEntryRoot e) u := by
  induction h with
  | root hp h1 => exact ⟨_, hp, h1, Relation.ReflTransGen.refl⟩
  | step _ hk _ hw ih =>
    obtain ⟨e, hp, h1, hr⟩ := ih
    exact ⟨e, hp, h1, hr.tail ⟨_, _, _, hk, hw, rfl⟩⟩

/-- **Paths after a step are paths before** (or stay at a new zero root): tagged pool entries after are entries
before at the same ASID or name a zero table, and the guest tables after are tables before or zero. -/
theorem GPath.mono {σ σ' : Fl4Spec.State Unit}
    (hpool : ∀ hi lo e, PoolAt σ' hi lo e → e &&& 1 = 1 →
      PoolAt σ hi lo e ∨ ∃ l, σ'.kheap (Fl4Spec.asidEntryRoot e) = some (.archObj (.ept l fun _ => 0)))
    (hobj : ∀ r l es, σ'.kheap r = some (.archObj (.ept l es)) →
      σ.kheap r = some (.archObj (.ept l es)) ∨ es = fun _ => 0)
    {hi : Fl4Spec.AsidHighIndex} {lo : Fl4Spec.AsidLowIndex} {gpa : Fl4Spec.Word} {l : Nat} {u : Fl4Spec.ObjRef}
    (h : GPath σ' hi lo gpa l u) :
    GPath σ hi lo gpa l u ∨ (l = 0 ∧ ∃ l', σ'.kheap u = some (.archObj (.ept l' fun _ => 0))) := by
  induction h with
  | root hp h1 => exact (hpool _ _ _ hp h1).imp (fun h => .root h h1) (fun h => ⟨rfl, h⟩)
  | step _ hk hc hw ih =>
    rcases ih with ih | ⟨-, l', hz⟩
    · rcases hobj _ _ _ hk with hk0 | hz
      · exact Or.inl (.step ih hk0 hc hw)
      · subst hz; exact (gWalkE_zero hw).elim
    · rw [hk] at hz; cases hz; exact (gWalkE_zero hw).elim

/-- `GPath.mono` at a nonzero level. -/
theorem GPath.mono' {σ σ' : Fl4Spec.State Unit}
    (hpool : ∀ hi lo e, PoolAt σ' hi lo e → e &&& 1 = 1 →
      PoolAt σ hi lo e ∨ ∃ l, σ'.kheap (Fl4Spec.asidEntryRoot e) = some (.archObj (.ept l fun _ => 0)))
    (hobj : ∀ r l es, σ'.kheap r = some (.archObj (.ept l es)) →
      σ.kheap r = some (.archObj (.ept l es)) ∨ es = fun _ => 0) :
    ∀ hi lo gpa l u, GPath σ' hi lo gpa l u → l ≠ 0 → GPath σ hi lo gpa l u :=
  fun _ _ _ _ _ h hl => (GPath.mono hpool hobj h).resolve_right fun h' => hl h'.1

/-- `PoolInj` across a step keeping the ASID table whose tagged pool entries are old ones at the same ASID. -/
theorem PoolInj.mono {σ σ' : Fl4Spec.State Unit} (h : PoolInj σ)
    (hat : σ'.archState.x64AsidTable = σ.archState.x64AsidTable)
    (hpool : ∀ hi lo e, PoolAt σ' hi lo e → e &&& 1 = 1 → PoolAt σ hi lo e) : PoolInj σ' :=
  ⟨fun hi hi' p h1 h2 => h.tab hi hi' p (by rw [← hat]; exact h1) (by rw [← hat]; exact h2),
    fun hi lo hi' lo' e e' h1 h2 t1 t2 hr => h.root hi lo hi' lo' e e' (hpool _ _ _ h1 t1) (hpool _ _ _ h2 t2) t1 t2 hr⟩

/-- **`EptNamed` across a step, witnesses given per path** (gen 42b19, the generalisation of `EptNamed.keep`): paths
after at a nonzero level are old ones, and every such old path to a table has a witness cap after (`hex`: a mapped
`Ept` slot cap with the path's ASID bits, level and address bits); each `Ept` cap after an old one or to a table with
an unmapped cap before (so unreachable). `keep` (every mapped non-root cap kept at some slot) and P3/EptDelRoot's
`EptCore.ofEmpty` (a mapped non-root cap dropped whose table is unreachable or has another cap) are its instances. -/
theorem EptNamed.keepW {th th' : TypedHeap} {m m' : U64 → U64} {σ σ' : Fl4Spec.State Unit} (N : EptNamed th m σ)
    (hpath : ∀ hi lo gpa l u, GPath σ' hi lo gpa l u → l ≠ 0 → GPath σ hi lo gpa l u) (hinj : PoolInj σ')
    (hex : ∀ hi lo gpa l u, gpa.toNat < 2 ^ 47 → GPath σ hi lo gpa l u → l ≠ 0 →
      ∃ y p lv a v, IsSlot th' y ∧ p.bv = u ∧ lv.val = l ∧ Fl4Spec.asidHighBitsOf a.bv = hi ∧
        Fl4Spec.asidLowBitsOf a.bv = lo ∧ v.bv = gKey gpa l ∧ capV m' y = .Ept p lv true a v)
    (hcb : ∀ y' p lv (mm : Bool) a v, IsSlot th' y' → capV m' y' = .Ept p lv mm a v →
      (∃ y, IsSlot th y ∧ capV m y = .Ept p lv mm a v) ∨
        ∃ y lv0 a0 v0, IsSlot th y ∧ capV m y = .Ept p lv0 false a0 v0) :
    EptNamed th' m' σ' where
  ex hi lo gpa l u hg hp hl := hex hi lo gpa l u hg (hpath _ _ _ _ _ hp hl) hl
  all hi lo gpa l u hg hp hl y' p lv mm a v hy' hpu hc' := by
    have hp0 := hpath _ _ _ _ _ hp hl
    rcases hcb y' p lv mm a v hy' hc' with ⟨y, hy, hc⟩ | ⟨y, lv0, a0, v0, hy, hc⟩
    · exact N.all hi lo gpa l u hg hp0 hl y p lv mm a v hy hpu hc
    · exact absurd (N.all hi lo gpa l u hg hp0 hl y p lv0 false a0 v0 hy hpu hc).1 Bool.false_ne_true
  inj := hinj

/-- **`EptNamed` across a step** whose nonzero-level paths are old ones, keeping the mapped non-root `Ept` caps (at
some slot), each `Ept` cap after an old one or to a table with an unmapped cap before (so unreachable). -/
theorem EptNamed.keep {th th' : TypedHeap} {m m' : U64 → U64} {σ σ' : Fl4Spec.State Unit} (N : EptNamed th m σ)
    (hpath : ∀ hi lo gpa l u, GPath σ' hi lo gpa l u → l ≠ 0 → GPath σ hi lo gpa l u) (hinj : PoolInj σ')
    (hck : ∀ y p lv a v, IsSlot th y → capV m y = .Ept p lv true a v → lv.val ≠ 0 →
      ∃ y', IsSlot th' y' ∧ capV m' y' = .Ept p lv true a v)
    (hcb : ∀ y' p lv (mm : Bool) a v, IsSlot th' y' → capV m' y' = .Ept p lv mm a v →
      (∃ y, IsSlot th y ∧ capV m y = .Ept p lv mm a v) ∨
        ∃ y lv0 a0 v0, IsSlot th y ∧ capV m y = .Ept p lv0 false a0 v0) :
    EptNamed th' m' σ' :=
  N.keepW hpath hinj (fun hi lo gpa l u hg hp hl => by
    obtain ⟨y, p, lv, a, v, hy, hpu, hlv, h1, h2, h3, hc⟩ := N.ex hi lo gpa l u hg hp hl
    obtain ⟨y', hy', hc'⟩ := hck y p lv a v hy hc (by rw [hlv]; exact hl)
    exact ⟨y', p, lv, a, v, hy', hpu, hlv, h1, h2, h3, hc'⟩) hcb

/-- **`EptNamed` across a step keeping the ASID table, whose tagged pool entries and guest tables are old ones**
(the frames), the mapped non-root `Ept` caps kept at some slot, each `Ept` cap after an old one. -/
theorem EptNamed.frameA {th th' : TypedHeap} {m m' : U64 → U64} {σ σ' : Fl4Spec.State Unit} (N : EptNamed th m σ)
    (hat : σ'.archState.x64AsidTable = σ.archState.x64AsidTable)
    (hpool : ∀ hi lo e, PoolAt σ' hi lo e → e &&& 1 = 1 → PoolAt σ hi lo e)
    (hobj : ∀ r l es, σ'.kheap r = some (.archObj (.ept l es)) → σ.kheap r = some (.archObj (.ept l es)))
    (hck : ∀ y p lv a v, IsSlot th y → capV m y = .Ept p lv true a v → lv.val ≠ 0 →
      ∃ y', IsSlot th' y' ∧ capV m' y' = .Ept p lv true a v)
    (hcb : ∀ y' p lv (mm : Bool) a v, IsSlot th' y' → capV m' y' = .Ept p lv mm a v →
      ∃ y, IsSlot th y ∧ capV m y = .Ept p lv mm a v) :
    EptNamed th' m' σ' :=
  N.keep (GPath.mono' (fun hi lo e h1 h2 => Or.inl (hpool hi lo e h1 h2)) (fun r l es h => Or.inl (hobj r l es h)))
    (N.inj.mono hat hpool) hck (fun y' p lv mm a v hy hc => Or.inl (hcb y' p lv mm a v hy hc))

/-- **`EptNamed` across a step keeping every arch object, the ASID table and every slot's cap.** -/
theorem EptNamed.ofSS {th : TypedHeap} {m m' : U64 → U64} {σ σ' : Fl4Spec.State Unit} (N : EptNamed th m σ)
    (hSS : SlotsSame th m m') (hat : σ'.archState.x64AsidTable = σ.archState.x64AsidTable)
    (hA : ∀ p (ao : Fl4Spec.ArchKernelObj), σ'.kheap p = some (.archObj ao) → σ.kheap p = some (.archObj ao)) :
    EptNamed th m' σ' :=
  N.frameA hat (fun _ _ _ ⟨p, f, h1, h2, h3⟩ _ => ⟨p, f, by rw [← hat]; exact h1, hA _ _ h2, h3⟩) (fun r l es h => hA _ _ h)
    (fun y p lv a v hy hc _ => ⟨y, hy, by rw [hSS.capV hy]; exact hc⟩)
    (fun y p lv mm a v hy hc => ⟨y, hy, by rw [← hSS.capV hy]; exact hc⟩)

/-- **The Architect's corollary `unmUnreach`**: the table of an unmapped `Ept` cap is reached at no nonzero level
(`EptNamed.all`: every cap to a reachable table is mapped). -/
theorem EptNamed.unmUnreach {th : TypedHeap} {m : U64 → U64} {σ : Fl4Spec.State Unit} (N : EptNamed th m σ)
    {y p lv a v : U64} (hy : IsSlot th y) (hc : capV m y = .Ept p lv false a v) :
    ∀ hi lo gpa l, gpa.toNat < 2 ^ 47 → l ≠ 0 → ¬ GPath σ hi lo gpa l p.bv :=
  fun hi lo gpa l hg hl hp => absurd (N.all hi lo gpa l _ hg hp hl y p lv false a v hy rfl hc).1 Bool.false_ne_true

/-- Boot: no tagged pool entry, no path. -/
theorem EptNamed.empty {th : TypedHeap} {m : U64 → U64} {σ : Fl4Spec.State Unit} (hT : NoGuestTag σ)
    (htab : ∀ hi hi' p, σ.archState.x64AsidTable hi = some p → σ.archState.x64AsidTable hi' = some p → hi = hi') :
    EptNamed th m σ where
  ex _ _ _ _ _ _ hp _ := by
    obtain ⟨e, he, h1, -⟩ := hp.root_tag
    rw [hT e he.guest] at h1; exact absurd h1 (by decide)
  all _ _ _ _ _ _ hp _ := by
    obtain ⟨e, he, h1, -⟩ := hp.root_tag
    rw [hT e he.guest] at h1; exact absurd h1 (by decide)
  inj := ⟨htab, fun _ _ _ _ e _ he _ h1 _ _ => by rw [hT e he.guest] at h1; exact absurd h1 (by decide)⟩

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **The guest-table facts of the VM epoch, one flat record** (module docstring). -/
structure EptCore (X : Set U64) (XL : U64 → Nat) (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) : Prop where
  rel : EptRel X XL σ (L.mem s)
  capL : EptCapL th XL (L.mem s)
  exte : JExtEpt (L := L) X th s
  tag : GuestTag X XL σ
  ks : ∀ t ∈ X, t.val + 4096 ≤ (L.ksb s).val ∨ (L.ksb s).val + 304384 ≤ t.val
  sep : ∀ t ∈ X, ∀ o ko, σ.kheap o = some ko → o ≠ t.bv → EptApart t o ko
  ue : UnmappedEmpty th XL (L.mem s) σ
  eslot : EptSlotOK th (L.mem s)
  walk : EptWalk σ
  named : EptNamed th (L.mem s) σ
  tbl : ∀ t ∈ X, (XL t = 0 ∨ XL t = 39 ∨ XL t = 30 ∨ XL t = 21) ∧ Vs.PaM t 4503599627366400#u64

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The VM-epoch state with guest tables** (module docstring): `VmState ∧ EptCore`. -/
abbrev VmEptState (V X : Set U64) (XL : U64 → Nat) (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap)
    (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  VmState (L := L) arI V AR Z H Cs Ac Lst D s a σ ∧ EptCore (L := L) X XL Z.th s σ

end

/-! ## Arithmetic -/

theorem ept_bits (l : Nat) (es : BitVec 9 → Fl4Spec.Word) :
    Fl4Spec.objBits (.archObj (.ept l es)) = 12 := by
  simp [Fl4Spec.objBits, Fl4Spec.archKobjSize, Fl4Spec.tableSize, Fl4Spec.ptTranslationBits,
    Fl4Spec.wordSizeBits]

theorem eptA_val {t : U64} (h : t.val + 4096 ≤ 2 ^ 64) (i : BitVec 9) :
    (eptA t i).val = t.val + 8 * i.toNat := by
  have hi : i.toNat < 512 := i.isLt
  have hy : (⟨BitVec.ofNat 64 (8 * i.toNat)⟩ : U64).val = 8 * i.toNat := by
    show (BitVec.ofNat 64 (8 * i.toNat)).toNat = _
    rw [BitVec.toNat_ofNat]; omega
  unfold eptA
  rw [Sched.wadd_val' (by rw [hy]; omega), hy]

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {X : Set U64} {XL : U64 → Nat} {th : TypedHeap} {s : S} {σ : Fl4Spec.State Unit}

/-! ## Boot -/

/-- **Boot** (gen 41's obligation 1): no table, no spec guest table, no tagged pool entry, no `Ept` slot cap. -/
theorem eptCore_empty (hE : ∀ r l es, σ.kheap r ≠ some (.archObj (.ept l es))) (hT : NoGuestTag σ)
    (hX : JExtEpt (L := L) ∅ th s)
    (h5 : ∀ t, th t = some .tcb → capV (L.mem s) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 5)) = .Null)
    (htab : ∀ hi hi' p, σ.archState.x64AsidTable hi = some p → σ.archState.x64AsidTable hi' = some p → hi = hi') :
    EptCore (L := L) ∅ XL th s σ where
  rel := eptRel_empty hE
  capL y hy p l a v mm hc := by
    have h := hX.cap y hy
    rw [hc] at h
    exact (show p ∈ (∅ : Set U64) from h).elim
  exte := hX
  tag e he h1 := by have := hT e he; rw [this] at h1; exact absurd h1 (by decide)
  ks _ h := h.elim
  sep _ h := h.elim
  ue y hy p l a v hc := by
    have h := hX.cap y hy
    rw [hc] at h
    exact (show p ∈ (∅ : Set U64) from h).elim
  eslot t ht := Or.inl (h5 t ht)
  walk := EptWalk.empty hE
  named := EptNamed.empty hT htab
  tbl _ h := h.elim

/-- **`UnmappedEmpty` across a step whose slot `Ept` caps are old ones** (gen 42b4): each `Ept` cap after is the cap
of some slot before (a mapped one possibly copied to a new slot, an unmapped one at its own slot), the words of the
tables of `X`, the spec's tables at `X` kept, and no pool entry added. -/
theorem UnmappedEmpty.keepI (C : EptCore (L := L) X XL th s σ) {th' : TypedHeap} {s' : S} {σ' : Fl4Spec.State Unit}
    (hcap : ∀ y, IsSlot th' y → ∀ p l a v (mm : Bool), capV (L.mem s') y = .Ept p l mm a v →
      ∃ y0, IsSlot th y0 ∧ capV (L.mem s) y0 = .Ept p l mm a v ∧ (mm = false → y0 = y))
    (hm : ∀ t ∈ X, ∀ i : BitVec 9, L.mem s' (eptA t i) = L.mem s (eptA t i))
    (hxk : ∀ t ∈ X, σ'.kheap t.bv = σ.kheap t.bv)
    (hge : ∀ e, GuestEntry σ' e → GuestEntry σ e) :
    UnmappedEmpty th' XL (L.mem s') σ' := by
  intro y hy p l a v hc
  obtain ⟨y0, hy0, hc0, hyy⟩ := hcap y hy p l a v false hc
  have e0 : y0 = y := hyy rfl
  rw [e0] at hy0 hc0
  have hpX : p ∈ X := by have h := C.exte.cap y hy0; rw [hc0] at h; exact h
  obtain ⟨h1, h2, h3, h4⟩ := C.ue y hy0 p l a v hc0
  refine ⟨fun i => by rw [hm p hpX i]; exact h1 i, by rw [hxk p hpX]; exact h2, ?_,
    fun e he h1' => h4 e (hge e he) h1'⟩
  intro y' hy' hne l' mm a' v' hc'
  obtain ⟨y1, hy1, hc1, hyy1⟩ := hcap y' hy' p l' a' v' mm hc'
  have hne1 : y1 ≠ y := by
    cases mm with
    | false => rw [hyy1 rfl]; exact hne
    | true => intro e; rw [e, hc0] at hc1; cases hc1
  exact h3 y1 hy1 hne1 l' mm a' v' hc1

/-- **`UnmappedEmpty` across a step keeping every slot `Ept` cap** (same slot, same cap), the words of the tables of
`X`, the spec's tables at `X`, and adding no pool entry. -/
theorem UnmappedEmpty.keep (C : EptCore (L := L) X XL th s σ) {th' : TypedHeap} {s' : S} {σ' : Fl4Spec.State Unit}
    (hcap : ∀ y, IsSlot th' y → ∀ p l a v (mm : Bool), capV (L.mem s') y = .Ept p l mm a v →
      IsSlot th y ∧ capV (L.mem s) y = .Ept p l mm a v)
    (hm : ∀ t ∈ X, ∀ i : BitVec 9, L.mem s' (eptA t i) = L.mem s (eptA t i))
    (hxk : ∀ t ∈ X, σ'.kheap t.bv = σ.kheap t.bv)
    (hge : ∀ e, GuestEntry σ' e → GuestEntry σ e) :
    UnmappedEmpty th' XL (L.mem s') σ' :=
  UnmappedEmpty.keepI C (fun y hy p l a v mm hc => let ⟨h1, h2⟩ := hcap y hy p l a v mm hc; ⟨y, h1, h2, fun _ => rfl⟩) hm hxk hge

/-! ## The generic frame -/

/-- **`EptWalk` after a step keeping the guest tables of `X` but those of `Z0`, which it zeroes or creates zero**
(gen 42b8; the frames, the pool assign, the retype, the table clear), every new tagged entry naming a zero table. -/
theorem EptCore.walkZ (C : EptCore (L := L) X XL th s σ) {σ' : Fl4Spec.State Unit} {Z0 : Set U64}
    (hxk : ∀ t ∈ X, t ∉ Z0 → σ'.kheap t.bv = σ.kheap t.bv)
    (hz : ∀ t ∈ Z0, ∃ l, σ'.kheap t.bv = some (.archObj (.ept l fun _ => 0)) ∧ (t ∈ X → l = XL t))
    (hne : ∀ r l es, σ'.kheap r = some (.archObj (.ept l es)) →
      (∃ t ∈ Z0, r = t.bv) ∨ ∃ l' es', σ.kheap r = some (.archObj (.ept l' es')))
    (hge : ∀ e, GuestEntry σ' e → e &&& 1 = 1 →
      GuestEntry σ e ∨ ∃ l, σ'.kheap (Fl4Spec.asidEntryRoot e) = some (.archObj (.ept l fun _ => 0))) :
    EptWalk σ' := by
  refine EptWalk.keep C.walk (fun r l es hk => ?_) (fun r l es hk => ?_) hge
  · rcases hne r l es hk with ⟨t, ht, rfl⟩ | ⟨l', es', h⟩
    · obtain ⟨l0, h0, -⟩ := hz t ht
      rw [h0] at hk; cases hk; exact Or.inr rfl
    · obtain ⟨u, hu, e⟩ := C.rel.spec r l' es' h
      subst e
      by_cases hu0 : u ∈ Z0
      · obtain ⟨l0, h0, -⟩ := hz u hu0
        rw [h0] at hk; cases hk; exact Or.inr rfl
      · exact Or.inl (by rw [← hxk u hu hu0]; exact hk)
  · obtain ⟨u, hu, e⟩ := C.rel.spec r l es hk
    subst e
    obtain ⟨es0, hk0, -⟩ := C.rel.obj u hu
    rw [hk0] at hk; cases hk
    by_cases hu0 : u ∈ Z0
    · obtain ⟨l0, h0, hl⟩ := hz u hu0
      rw [hl hu] at h0; exact ⟨_, h0⟩
    · exact ⟨_, by rw [hxk u hu hu0]; exact hk0⟩

/-- **`EptCore` across writes outside the table words of `X`**, its slot `Ept` caps old ones (`UnmappedEmpty.keepI`;
gen 42b4: a mapped cap may be copied to a new slot). -/
theorem EptCore.frameI (C : EptCore (L := L) X XL th s σ) {th' : TypedHeap} {s' : S} {σ' : Fl4Spec.State Unit}
    {W : U64 → Prop} (hw : P1.WritesIn st s s' W)
    (hW : ∀ b, W b → ∀ t ∈ X, b.val < t.val ∨ t.val + 4096 ≤ b.val)
    (hcap : ∀ y, IsSlot th' y → ∀ p l a v (mm : Bool), capV (L.mem s') y = .Ept p l mm a v →
      ∃ y0, IsSlot th y0 ∧ capV (L.mem s) y0 = .Ept p l mm a v ∧ (mm = false → y0 = y))
    (hX' : JExtEpt (L := L) X th' s')
    (hxk : ∀ t ∈ X, σ'.kheap t.bv = σ.kheap t.bv)
    (hne : ∀ r l es, σ'.kheap r = some (.archObj (.ept l es)) →
      ∃ l' es', σ.kheap r = some (.archObj (.ept l' es')))
    (hge : ∀ e, GuestEntry σ' e → GuestEntry σ e)
    (hsz : ∀ o ko', σ'.kheap o = some ko' → ∃ ko, σ.kheap o = some ko ∧ Fl4Spec.objBits ko' = Fl4Spec.objBits ko)
    (h5 : EptSlotStep th th' (L.mem s) (L.mem s')) (hnm : EptNamed th' (L.mem s') σ') :
    EptCore (L := L) X XL th' s' σ' where
  rel := by
    refine ⟨fun t ht => ?_, fun r l es hk => ?_, C.rel.place⟩
    · obtain ⟨es, hk, hwd⟩ := C.rel.obj t ht
      refine ⟨es, (hxk t ht).trans hk, fun i hi => ?_⟩
      have hp := C.rel.place t ht
      have e := eptA_val hp.2 i
      have hi9 := i.isLt
      rw [hw.mem_eq (b := eptA t i) (by unfold P1.Aligned; rw [e]; omega)
        (fun hb => by rcases hW _ hb t ht with h | h <;> omega)]
      exact hwd i hi
    · obtain ⟨l', es', h⟩ := hne r l es hk
      exact C.rel.spec r l' es' h
  capL y hy p l a v mm hc := by
    obtain ⟨y0, hy', hc', -⟩ := hcap y hy p l a v mm hc
    exact C.capL y0 hy' p l a v mm hc'
  exte := hX'
  tag e he h1 := C.tag e (hge e he) h1
  ks t ht := by rw [hw.1]; exact C.ks t ht
  sep t ht o ko' ho hne' := by
    obtain ⟨ko, hko, hb⟩ := hsz o ko' ho
    unfold EptApart; rw [hb]; exact C.sep t ht o ko hko hne'
  ue := UnmappedEmpty.keepI C hcap (fun t ht i => by
      have hp := C.rel.place t ht
      have e := eptA_val hp.2 i
      have hi9 := i.isLt
      exact hw.mem_eq (b := eptA t i) (by unfold P1.Aligned; rw [e]; omega)
        (fun hb => by rcases hW _ hb t ht with h | h <;> omega)) hxk hge
  eslot := C.eslot.step h5
  walk := C.walkZ (Z0 := ∅) (fun t ht _ => hxk t ht) (fun _ h => h.elim) (fun r l es hk => Or.inr (hne r l es hk))
    (fun e he _ => Or.inl (hge e he))
  named := hnm
  tbl := C.tbl

/-- **`EptCore` across writes outside the table words of `X`** (module docstring). -/
theorem EptCore.frame (C : EptCore (L := L) X XL th s σ) {th' : TypedHeap} {s' : S} {σ' : Fl4Spec.State Unit}
    {W : U64 → Prop} (hw : P1.WritesIn st s s' W)
    (hW : ∀ b, W b → ∀ t ∈ X, b.val < t.val ∨ t.val + 4096 ≤ b.val)
    (hcap : ∀ y, IsSlot th' y → ∀ p l a v (mm : Bool), capV (L.mem s') y = .Ept p l mm a v →
      IsSlot th y ∧ capV (L.mem s) y = .Ept p l mm a v)
    (hX' : JExtEpt (L := L) X th' s')
    (hxk : ∀ t ∈ X, σ'.kheap t.bv = σ.kheap t.bv)
    (hne : ∀ r l es, σ'.kheap r = some (.archObj (.ept l es)) →
      ∃ l' es', σ.kheap r = some (.archObj (.ept l' es')))
    (hge : ∀ e, GuestEntry σ' e → GuestEntry σ e)
    (hsz : ∀ o ko', σ'.kheap o = some ko' → ∃ ko, σ.kheap o = some ko ∧ Fl4Spec.objBits ko' = Fl4Spec.objBits ko)
    (h5 : EptSlotStep th th' (L.mem s) (L.mem s')) (hnm : EptNamed th' (L.mem s') σ') :
    EptCore (L := L) X XL th' s' σ' :=
  C.frameI hw hW (fun y hy p l a v mm hc => let ⟨h1, h2⟩ := hcap y hy p l a v mm hc; ⟨y, h1, h2, fun _ => rfl⟩) hX' hxk
    hne hge hsz h5 hnm

/-- **`VcpuCore`-side apartness**: every table of `X` misses every VCPU object of `V` (`JVm.sep`). -/
theorem EptCore.apartV (C : EptCore (L := L) X XL th s σ) {V : Set U64} {H : P1.Heap}
    (Jv : JVm (L := L) V H s σ) : ∀ t ∈ X, ∀ v ∈ V, t.val + 4096 ≤ v.val ∨ v.val + 32768 ≤ t.val := by
  intro t ht v hv
  obtain ⟨es, hk, -⟩ := C.rel.obj t ht
  obtain ⟨x, hx⟩ := Jv.spec v hv
  have hne : t.bv ≠ v.bv := fun e => by rw [e, hx] at hk; cases hk
  have h := Jv.sep v hv t.bv _ hk hne
  unfold VcpuApart at h
  rw [ept_bits] at h
  exact h

end

/-! ## Placement from the base -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}
  {XL : U64 → Nat}

/-- A table of `X` is `H`'s `.other 12` (`SpecCover.arch` + `ArchFitHyp`). -/
theorem JAtZB.eptHeap (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (C : EptCore (L := L) X XL Z.th s σ) {t : U64} (ht : t ∈ X) : H t = some (.other 12) := by
  obtain ⟨es, hk, -⟩ := C.rel.obj t ht
  obtain ⟨n, hn, hH⟩ := B.cover.arch t.bv _ hk
  have hf := B.carry.archFit t.bv _ n hk hH
  rw [ept_bits] at hf
  have e : n = 12 := by omega
  subst e
  exact hH

/-- **Every other object of `H` misses a table of `X`.** -/
theorem JAtZB.eptApartH (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (C : EptCore (L := L) X XL Z.th s σ) {t : U64} (ht : t ∈ X) :
    ∀ p k, H p = some k → p ≠ t → p.val + 2 ^ k.bits ≤ t.val ∨ t.val + 4096 ≤ p.val := by
  intro p k hp hne
  rcases B.kern.heap.disj p k t _ hp (B.eptHeap C ht) hne with h | h
  · exact Or.inl h
  · simp only [P1.HKind.bits, Nat.reducePow] at h; exact Or.inr h

/-- The VCPU list head misses every table of `X`. -/
theorem JAtZB.eptHead (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (C : EptCore (L := L) X XL Z.th s σ) {t : U64} (ht : t ∈ X) :
    (P1.vHeadA st s).val + 8 ≤ t.val ∨ t.val + 4096 ≤ (P1.vHeadA st s).val := by
  have hv : (P1.vHeadA st s).val = (L.ksb s).val + 80 := vHead_val B.kern.ksbFit
  rcases C.ks t ht with h | h <;> omega

section
open Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Sched

/-- **`OObj` words miss every table of `X`** (the argument of `JAtZB.oobjV`, with `EptCore.ks` / `sep`). -/
theorem JAtZB.oobjX (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (C : EptCore (L := L) X XL Z.th s σ)
    {t : U64} (ht : t ∈ X) {b : U64} (hb : OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b) :
    b.val < t.val ∨ t.val + 4096 ≤ b.val := by
  have dH : ∀ p k, H p = some k → k ≠ .other 12 → p.val + 2 ^ k.bits ≤ t.val ∨ t.val + 4096 ≤ p.val := by
    intro p k hp hk
    have hne : p ≠ t := fun e => by subst e; rw [B.eptHeap C ht] at hp; cases hp; exact hk rfl
    exact B.eptApartH C ht p k hp hne
  have hks := C.ks t ht
  rcases hb with ⟨g1, g2⟩ | ⟨g1, g2, -⟩ | ⟨u, hu, g1, g2⟩ | ⟨e, he, g1, g2⟩ | ⟨r, hr, g1, g2⟩ | ⟨n, hn, g1, g2⟩ |
      ⟨sc, hsc, x, n, hk, hso⟩ | ⟨wp, hwp, g1, g2⟩
  · obtain ⟨Q, R0, hcq, -⟩ := B.xtop.fin.1.1.1.lists
    have hcC : Z.c ∈ Cs := hcq.cur ▸ B.kern.cpuCs
    have hc64 := B.kern.csLt Z.c hcC
    have hnb : L.nodeBase s Z.c = (L.ksb s).val + 13568 + Z.c.val * 4288 := rfl
    rw [hnb] at g1 g2
    omega
  · omega
  · have d := dH u _ (B.zH.1 u hu) (by intro h; cases h)
    simp only [P1.HKind.bits, Nat.reducePow] at d; omega
  · have d := dH e _ (B.zH.2.1 e he) (by intro h; cases h)
    simp only [P1.HKind.bits, Nat.reducePow] at d; omega
  · have d := dH r _ (B.zH.2.2.1 r hr) (by intro h; cases h)
    simp only [P1.HKind.bits, Nat.reducePow] at d; omega
  · have d := dH n _ (B.zH.2.2.2 n hn) (by intro h; cases h)
    simp only [P1.HKind.bits, Nat.reducePow] at d; omega
  · obtain ⟨Tr, Cq, hJ⟩ := B.jpl
    have hH := (hJ.sc sc x n (B.c0 sc hsc) hk).2
    have d := dH sc _ hH (by intro h; cases h)
    simp only [P1.HKind.bits, Nat.reducePow] at d
    unfold Sched.ScObj at hso
    omega
  · obtain ⟨q, vms, hq, q1, q2⟩ := B.carry.bufPg wp hwp
    obtain ⟨es, hk, -⟩ := C.rel.obj t ht
    have hne : q ≠ t.bv := fun e' => by rw [e', hk] at hq; cases hq
    have eb : Fl4Spec.objBits (.archObj (.dataPage false vms)) = Fl4Spec.pageBitsForSize vms := by
      simp [Fl4Spec.objBits, Fl4Spec.archKobjSize]
    rcases C.sep t ht q _ hq hne with e1 | e1
    · rw [eb] at e1; omega
    · omega

end

/-! ## Frames at the base -/

/-- An arch object of the post-state of an SC-code step was there before (`zv_tk_v` for any arch object). -/
theorem ept_tk_arch {σ σ' : Fl4Spec.State Unit} (h : Sched.ScTKw (fun _ => False) σ σ') :
    ∀ p (ao : Fl4Spec.ArchKernelObj), σ'.kheap p = some (.archObj ao) → σ.kheap p = some (.archObj ao) := by
  intro o ao ho
  have k := h.kh o
  rw [ho] at k
  cases e : σ.kheap o with
  | none => rw [e] at k; exact k.elim
  | some ko =>
    rw [e] at k
    change Sched.TKObj False ko (.archObj ao) at k
    rcases k with k | ⟨_, _, -, h2, -, -⟩ | ⟨_, _, _, -, h2⟩ | ⟨_, _, -, h2, -⟩ | ⟨_, _, -, h2, -⟩
    · rw [k]
    all_goals cases h2

/-- **`EptCore` across a native step** (`OObj` writes; the spec's tables at `X` kept, no new spec guest table, no new
pool entry, sizes kept — the shape of `VcpuCore.ofBS`). -/
theorem EptCore.ofBS (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (C : EptCore (L := L) X XL Z.th s σ)
    {s' : S} {σ' : Fl4Spec.State Unit} {W : U64 → Prop} (hw : P1.WritesIn st s s' W)
    (hO : ∀ b, W b → Vs.OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b)
    (hxk : ∀ t ∈ X, σ'.kheap t.bv = σ.kheap t.bv)
    (hne : ∀ r l es, σ'.kheap r = some (.archObj (.ept l es)) →
      ∃ l' es', σ.kheap r = some (.archObj (.ept l' es')))
    (hge : ∀ e, GuestEntry σ' e → GuestEntry σ e)
    (hsz : ∀ o ko', σ'.kheap o = some ko' → ∃ ko, σ.kheap o = some ko ∧ Fl4Spec.objBits ko' = Fl4Spec.objBits ko)
    (hnm : EptNamed Z.th (L.mem s') σ') :
    EptCore (L := L) X XL Z.th s' σ' := by
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s') := B.xtop.slotsSame_of hw hO
  exact C.frame hw (fun b hb t ht => B.oobjX C ht (hO b hb))
    (fun y hy p l a v mm hc => ⟨hy, by rw [← hSS.capV hy]; exact hc⟩)
    (C.exte.of_eq fun y hy => hSS.capV hy) hxk hne hge hsz (EptSlotStep.ofSS hSS) hnm

/-- **`EptCore` across a native step keeping the spec heap and the ASID table.** -/
theorem EptCore.ofB (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (C : EptCore (L := L) X XL Z.th s σ)
    {s' : S} {σ' : Fl4Spec.State Unit} {W : U64 → Prop} (hw : P1.WritesIn st s s' W)
    (hO : ∀ b, W b → Vs.OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b) (hke : σ'.kheap = σ.kheap)
    (hat : σ'.archState.x64AsidTable = σ.archState.x64AsidTable) :
    EptCore (L := L) X XL Z.th s' σ' :=
  C.ofBS B hw hO (fun _ _ => by rw [hke]) (fun r l es hk => ⟨l, es, by rw [← hke]; exact hk⟩)
    (fun e ⟨hi, p, f, lo, h1, h2, h3⟩ => ⟨hi, p, f, lo, by rw [← hat]; exact h1, by rw [← hke]; exact h2, h3⟩)
    (fun o ko' ho => ⟨ko', by rw [← hke]; exact ho, rfl⟩)
    (C.named.ofSS (B.xtop.slotsSame_of hw hO) hat (fun p ao h => by rw [← hke]; exact h))

/-- **`EptCore` across an SC-code step** (`TFoot` writes, `ScTKw`; as `VcpuCore.ofTK`). -/
theorem EptCore.ofTK (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (C : EptCore (L := L) X XL Z.th s σ)
    {s' : S} {σ' : Fl4Spec.State Unit}
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ)) (hK : Sched.ScTKw (fun _ => False) σ σ') :
    EptCore (L := L) X XL Z.th s' σ' := by
  have hS := B.xtop.fin.1.1.1
  obtain ⟨h1, h2, -⟩ := zv_tk hK
  have hA := ept_tk_arch hK
  refine C.ofBS B hw (fun b hb => Sched.tfoot_oobj hS hb) (fun t ht => ?_) (fun r l es hk => ⟨l, es, hA _ _ hk⟩)
    (fun e ⟨hi, p, f, lo, g1, g2, g3⟩ => ⟨hi, p, f, lo, by rw [← hK.arch]; exact g1, hA _ _ g2, g3⟩) h2
    (C.named.ofSS (B.xtop.slotsSame_of hw (fun b hb => Sched.tfoot_oobj hS hb)) (by rw [hK.arch]) hA)
  obtain ⟨es, hk, -⟩ := C.rel.obj t ht
  exact h1 _ _ hk

/-! ## `VmEptState` -/

/-- `VmEptState` is `JAtZB ∧ VcpuCore ∧ EptCore` (the contract's reading). -/
theorem vmEptState_iff {XL : U64 → Nat} :
    VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s a σ ↔
      JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ VcpuCore (L := L) V Z H s σ ∧
        EptCore (L := L) X XL Z.th s σ :=
  and_assoc

/-- **The embedding `VmState V → VmEptState V ∅`** (no `Ept` slot cap and no EPT-mapped frame cap — `JExtEpt ∅` —,
no spec guest table, no tagged pool entry). -/
theorem VmState.toEpt (J : VmState (L := L) arI V AR Z H Cs Ac Lst D s a σ) {XL : U64 → Nat}
    (hX : JExtEpt (L := L) ∅ Z.th s)
    (hE : ∀ r l es, σ.kheap r ≠ some (.archObj (.ept l es))) (hT : NoGuestTag σ)
    (h5 : ∀ t, Z.th t = some .tcb → capV (L.mem s) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 5)) = .Null)
    (htab : ∀ hi hi' p, σ.archState.x64AsidTable hi = some p → σ.archState.x64AsidTable hi' = some p → hi = hi') :
    VmEptState (L := L) arI V ∅ XL AR Z H Cs Ac Lst D s a σ :=
  ⟨J, eptCore_empty hE hT hX h5 htab⟩

/-- **The native embedding into `VmEptState ∅ ∅`** (gen 42a2's `JAtZ.toVmState`, `JExtEpt.of_jext`, then
`VmState.toEpt`). -/
theorem JAtZ.toVmEptState (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {XL : U64 → Nat}
    (hN : Endp.NativeScope σ) (h0 : L.mem s (P1.vHeadA st s) = 0#u64)
    (hd : P1.Aligned (P1.vHeadA st s) ∧ ¬ JW ∅ Z.th (P1.vHeadA st s) ∧ ¬ SW Z.th (P1.vHeadA st s))
    (hO : VOnly ∅ σ) (hR : VirtRngOne.RngOne (L.mem s) Z.G)
    (hE : ∀ r l es, σ.kheap r ≠ some (.archObj (.ept l es))) (hT : NoGuestTag σ)
    (h5 : ∀ t, Z.th t = some .tcb → capV (L.mem s) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 5)) = .Null)
    (htab : ∀ hi hi' p, σ.archState.x64AsidTable hi = some p → σ.archState.x64AsidTable hi' = some p → hi = hi') :
    VmEptState (L := L) arI ∅ ∅ XL AR Z H Cs Ac Lst D s a σ :=
  (J.toVmState hN h0 hd hO hR).toEpt (JExtEpt.of_jext J.ext) hE hT h5 htab

/-- **`VmEptState` + `IoOwnV` is a `JAtZV3`** (`VmState.toV3` with `EptCore.exte`). -/
theorem VmEptState.toV3 (J : VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s a σ)
    (hI : IoOwnV V Z.th (L.mem s)) : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ :=
  J.1.toV3 J.2.exte hI

/-- `VmEptState` across a native step that may change the spec heap (`VmState.ofBS`, `EptCore.ofBS`). -/
theorem VmEptState.ofBS (J : VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s a σ)
    {Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    (B' : JAtZB (L := L) arI AR Z H Cs Ac' Lst' D' s' a' σ') {W : U64 → Prop} (hw : P1.WritesIn st s s' W)
    (hO : ∀ b, W b → Vs.OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b) (hh : ∀ b, W b → b ≠ P1.vHeadA st s)
    (hv : VKeep (L := L) Z.th s s')
    (hvk : ∀ u ∈ V, σ'.kheap u.bv = σ.kheap u.bv)
    (hsz : ∀ o ko', σ'.kheap o = some ko' → ∃ ko, σ.kheap o = some ko ∧ Fl4Spec.objBits ko' = Fl4Spec.objBits ko)
    (hrv : ∀ o x', σ'.kheap o = some (.tcb x') → x'.tcbState = .runningVM →
      ∃ x, σ.kheap o = some (.tcb x) ∧ x.tcbState = .runningVM)
    (hnv : ∀ p (vs : Fl4Spec.VcpuState), σ'.kheap p = some (.archObj (.vcpu vs)) →
      σ.kheap p = some (.archObj (.vcpu vs)))
    (hxk : ∀ t ∈ X, σ'.kheap t.bv = σ.kheap t.bv)
    (hne : ∀ r l es, σ'.kheap r = some (.archObj (.ept l es)) →
      ∃ l' es', σ.kheap r = some (.archObj (.ept l' es')))
    (hge : ∀ e, GuestEntry σ' e → GuestEntry σ e) (hnm : EptNamed Z.th (L.mem s') σ') :
    VmEptState (L := L) arI V X XL AR Z H Cs Ac' Lst' D' s' a' σ' :=
  ⟨J.1.ofBS B' hw hO hh hv hvk hsz hrv hnv, J.2.ofBS J.1.1 hw hO hxk hne hge hsz hnm⟩

/-- `VmEptState` across a native step keeping the spec heap and the ASID table. -/
theorem VmEptState.ofB (J : VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s a σ)
    {Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    (B' : JAtZB (L := L) arI AR Z H Cs Ac' Lst' D' s' a' σ') {W : U64 → Prop} (hw : P1.WritesIn st s s' W)
    (hO : ∀ b, W b → Vs.OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b) (hh : ∀ b, W b → b ≠ P1.vHeadA st s)
    (hv : VKeep (L := L) Z.th s s') (hke : σ'.kheap = σ.kheap)
    (hat : σ'.archState.x64AsidTable = σ.archState.x64AsidTable) :
    VmEptState (L := L) arI V X XL AR Z H Cs Ac' Lst' D' s' a' σ' :=
  ⟨J.1.ofB B' hw hO hh hv hke, J.2.ofB J.1.1 hw hO hke hat⟩

/-- `VmEptState` across an SC-code step. -/
theorem VmEptState.ofTK (J : VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s a σ)
    {Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    (B' : JAtZB (L := L) arI AR Z H Cs Ac' Lst' D' s' a' σ')
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ)) (hK : Sched.ScTKw (fun _ => False) σ σ') :
    VmEptState (L := L) arI V X XL AR Z H Cs Ac' Lst' D' s' a' σ' :=
  ⟨J.1.ofTK B' hw hK, J.2.ofTK J.1.1 hw hK⟩

/-- `VmEptState` with another arch state relating to the same CR3. -/
theorem VmEptState.archV (J : VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s a σ) {a' : A}
    (hAR : AR a' σ.archState.x64CurrentCr3) : VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s a' σ :=
  ⟨J.1.archV hAR, J.2⟩

end

end

end Fl4Proofs.P3
