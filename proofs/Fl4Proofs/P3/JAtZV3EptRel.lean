/-
P3 (line mmuAD, gen 41): **the guest page-table relation** — design and definitions (gen 40 found the EPT arms
that read a guest table not provable at `JAtZV3`: nothing relates FL4's guest-table pages to the spec's
`.archObj (.ept l es)` objects).

## What the base relation already covers

* **The ASID pools, tagged entries included.** P3/VsRel's `VsRel.pool` relates every pool word to the spec's pool
  entry by `optRef` of the *whole* word (`f lo = optRef (m (peA p lo))`), tag bit 0 included; `nativeRef` only
  hides tagged entries from the native view. So FL4's `ept::find` (`vspace::find_asid`, `r & 1`, `r & !1`;
  ept.rs l. 16-23) and the spec's `findGuestRoot` (`e &&& 1`, `asidEntryRoot e`) read related words: the root
  lookup, and `ept::root`'s `r != ptr` check (l. 24-40), need no new relation.
* **Not covered: the tables.** `JAtZV3`'s `X` is used only by `JExtV.cap` (`VtxCap (Ept p …) = p ∈ X`); no field
  says what the 512 words of `p` are, nor that the spec has `.ept l es` at `p`.

## The relation (`EptRel`)

For a ghost level map `XL : U64 → Nat` (0 root, 39 PDPT, 30 PD, 21 PT — `Cap::Ept.level`):

* `obj`: every `t ∈ X` is a spec guest table `.ept (XL t) es`, and every entry word FL4 keeps at `t + 8 i`
  is `es i` **up to the bits hardware writes** (`eptHw virtKind`): on SVM the nested page tables are long-mode
  page tables whose accessed / dirty bits (5, 6) the walker sets (APM Vol. 2 §15.25.5, §5.4.2); on VMX FL4's
  EPTP is `root | 6 | 3 << 3` (fl4-arch-x86_64 vm.rs l. 1002, l. 1216: bit 6, EPT A/D enable, is clear), so the
  hardware writes nothing. Of the root (`XL t = 0`) only entries `i < 256` are related: words 510 and 511 of a
  root hold `mark_core`'s core bitmap in their upper halves (ept.rs `CORES` = 510·8, l. 41-53), and FL4 maps
  only below `LIMIT` = 2^47 (root index < 256; gen 40's `JAtZV3.eptGpaJ`).
* `spec`: every spec guest table is at some `t ∈ X` (so `getEpt` at an address outside `X` fails on both sides
  of every walk that matters).
* `place`: `t ∈ X` is 4 KiB aligned, inside the address space.
* `capL` (`EptCapL`): a slot's `Ept p l …` cap has `l.val = XL p` (with `VtxCap`, `p ∈ X`).

The walk's control bits (present 0, large 7) and address bits 51:12 are below / not in `eptHw`, so
`guestLookupSlot`, `guestUnmap`'s present / kind / address test and `ept::lookup` read the same values from
related words.

## Obligations (`EptObl`, not proved here)

1. **Boot**: `X = ∅` (P2's boot has no guest table): `EptRel ∅` with no spec guest table (`eptRel_empty`).
2. **Frames**: every FL4 write outside the tables of `X` and every spec step not touching an `.ept` object keeps
   `EptRel` (the tables are separate objects of `H`: needs the placement of `X` in `H`, as `JVm.sep` for VCPUs).
3. **Retype** (`ept` objects): `t` joins `X` with 512 zero words and the spec's `.ept l (fun _ => 0)`
   (Ext's `defaultArchObject`, Structs l. 472-475).
4. **Map / unmap** (ept.rs l. 269-310, `frame_entry`, `paddr | 7`): FL4's entry write paired with
   `storeGuestEntry` (`Function.update es i e`), the same word.
5. **Deletion / detype**: `t` leaves `X` with its spec object.
6. **Guest execution**: the only writes to `X` while a guest runs are `eptHw` bits.
7. **`mark_core`**: writes only the upper half of root words 510 / 511 (unrelated).

**Should it become a field?** Yes: `JAtZV4 := JAtZV3 ∧ EptRel ∧ EptCapL` (defined below), not a premise: it is
a state invariant like `VRel`, true at boot, and every step must keep it (obligations 2-7). `JAtZV3` itself
cannot change (no existing statement changes); the EPT success arms would be proved at `JAtZV4`, the rest of the
line lifted by obligation 2.

No theorem here depends on a premise; `eptRel_empty` is the boot case. No existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3EptG
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-- The entry bits the hardware walker writes (module docstring): accessed / dirty on SVM, none on VMX. -/
def eptHw (k : Fl4Spec.VirtKind) : Fl4Spec.Word := if k = .svm then 0x60 else 0

/-- An FL4 entry word against a spec entry, up to the hardware-written bits. -/
def EptWord (k : Fl4Spec.VirtKind) (w e : Fl4Spec.Word) : Prop := w &&& ~~~(eptHw k) = e &&& ~~~(eptHw k)

/-- The address of entry `i` of the table at `t`. -/
def eptA (t : U64) (i : BitVec 9) : U64 := core.num.U64.wrapping_add t ⟨BitVec.ofNat 64 (8 * i.toNat)⟩

/-- **The guest page-table relation** (module docstring). -/
structure EptRel (X : Set U64) (XL : U64 → Nat) (σ : Fl4Spec.State Unit) (m : U64 → U64) : Prop where
  obj : ∀ t ∈ X, ∃ es, σ.kheap t.bv = some (.archObj (.ept (XL t) es)) ∧
    ∀ i : BitVec 9, (XL t ≠ 0 ∨ i.toNat < 256) → EptWord Fl4Spec.virtKind (m (eptA t i)).bv (es i)
  spec : ∀ r l es, σ.kheap r = some (.archObj (.ept l es)) → ∃ t ∈ X, t.bv = r
  place : ∀ t ∈ X, t.val % 4096 = 0 ∧ t.val + 4096 ≤ 2 ^ 64

/-- A slot's EPT cap has the ghost level of its table (module docstring). -/
def EptCapL (th : TypedHeap) (XL : U64 → Nat) (m : U64 → U64) : Prop :=
  ∀ y, IsSlot th y → ∀ p l a v (mm : Bool), capV m y = .Ept p l mm a v → l.val = XL p

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

/-- **`JAtZV3` with the guest page-table relation** (module docstring: the field the EPT success arms need). -/
structure JAtZV4 (arI : machine.Arch A) (V X : Set U64) (XL : U64 → Nat) (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets)
    (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop where
  z3 : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ
  ept : EptRel X XL σ (L.mem s)
  capL : EptCapL Z.th XL (L.mem s)

end

/-- Boot (obligation 1): with no spec guest table, `EptRel ∅` holds. -/
theorem eptRel_empty {XL : U64 → Nat} {σ : Fl4Spec.State Unit} {m : U64 → U64}
    (h : ∀ r l es, σ.kheap r ≠ some (.archObj (.ept l es))) : EptRel ∅ XL σ m where
  obj := fun _ ht => ht.elim
  spec := fun r l es hk => (h r l es hk).elim
  place := fun _ ht => ht.elim

end

end Fl4Proofs.P3
