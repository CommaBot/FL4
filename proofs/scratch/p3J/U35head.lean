/-
P3 (line p3J, gen 1): **`kernel_entry_reachU35`** = `kernel_entry_reachU34` with two fields of the
syscall clause's per-entry `KDispHypsKVU32` discharged (inventory: `WS/handoff/p3J.md`).

* **`ArchIrqRelN.num`** (E2) is `JEntryAtR7T.ioapics` (E1) restated: the same proposition.
* **`ArchIrqRelN.mask`** (E6, `∀ a irq b, ∃ a', mask_irq a irq b = ok a'`) is
  `P0.ArchTotal.mask_irq`, U34's own premise `hA`.

`JEntryAtR7V` = `JEntryAtR7T` without those two; `KDispHypsKVU35` = `KDispHypsKVU32` with
`JEntryAtR7V` in both `inv` and `mid`. `KDispHypsKVU35.toU32` (from `hA`) and `KDispHypsKVU32.toU35`
(dropping fields).

**Premise diff U34 → U35**: in the syscall clause, `KDispHypsKVU32 …` ↦ `KDispHypsKVU35 …`, i.e.
`JEntryAtR7T.archIrq.num` and `JEntryAtR7T.archIrq.mask` removed (in `inv` and `mid`). Every other
premise, every other clause and the conclusion verbatim. No new premise. [W] 0.
**`kernel_entry_reachU34_of35`** proves U34's statement, verbatim, from U35.

Named premises still open in U35 (all inherited, statement-level, unchanged):
* [P] `JEntryAtR7V.ioapics` (IOAPIC count = spec `x64NumIoapics`), `.pins` (pin counts = spec
  `x64IoapicNirqs`), `.map` / `.mapr` (in-range routing succeeds with `true`);
* `JPathAtMU30` ([P]/[S] SchedControl `cpu = Z.c`; untyped `fan`, `core0`, `rcb` [P]; `vtx` [scope];
  Thread SetEPTRoot and EPT-frame `JVtxScope` [scope]);
* [J]/[scope] `JDecMRLK … VtxK …`; [P] `KFinAtR13` (`ArchSwF`, `ArchNdF`); the global [P] premises of U34.
The p3J inventory records which of these are false at reachable entries (the ∀-slot form of
`JPathAtMU30`): they are kept, not weakened.
No sorry.
-/
import Fl4Proofs.P3.XTopJointKEntryU34
import Fl4Proofs.P3.CnodeCaps
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JEntryAtR7T` without `archIrq.num` (= `ioapics`) and `archIrq.mask` (from `ArchTotal`).** -/
structure JEntryAtR7V (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (s : S) (ar : A) (σ : Fl4Spec.State Unit) :
    Prop where
  /-- [P] `JEntryAt.ioapics`: the backend's IOAPIC count is the spec's `x64NumIoapics`. -/
  ioapics : ∃ nA, arI.num_ioapics ar = ok nA ∧ nA.bv = σ.archState.x64NumIoapics
  /-- [P] `ArchIrqRelN.pins`: each IOAPIC's pin count is the spec's `x64IoapicNirqs`, at least one. -/
  pins : ∀ n, arI.num_ioapics ar = ok n → ∀ i : U64, i.val < n.val →
    ∃ p, arI.ioapic_pins ar i = ok p ∧ p.val = (σ.archState.x64IoapicNirqs i.bv).toNat ∧ 0 < p.val
  /-- [P] `ArchIrqRelN.map`: in-range IOAPIC routing succeeds and routes (`true`). -/
  map : ∀ (a : A) (n i p l po v np : U64), arI.num_ioapics a = ok n → ¬ i >= n → arI.ioapic_pins a i = ok np →
    ¬ p >= np → ¬ l > 1#u64 → ¬ po > 1#u64 → ∃ a', arI.ioapic_map a i p l po v = ok (true, a')
  /-- [P] `ArchIrqRelN.mapr`: the remapped form. -/
  mapr : ∀ (a : A) (n i p l po v h np : U64), arI.num_ioapics a = ok n → ¬ i >= n → arI.ioapic_pins a i = ok np →
    ¬ p >= np → ¬ l > 1#u64 → ¬ po > 1#u64 → ¬ h >= 65536#u64 →
    ∃ a', arI.ioapic_map_remapped a i p l po v h = ok (true, a')

/-- **`KDispHypsKVU32` with `JEntryAtR7V`.** -/
structure KDispHypsKVU35 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets)
    (H : P1.Heap) (Cs D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64) (c : Fl4Spec.Syscall) : Prop where
  /-- [P]/[J] as `KDispHypsKVU32.inv` without the two discharged fields. -/
  inv : ∀ ct call bl don, sched.cur_thread st s = ok ct → InvSys n call bl don →
    JEntryAtR7V arI AR Z s a σ ∧
    JPathAtMU30 (L := L) arI AR Z H Cs D s a σ ct call bl don false (L.mem s (regA ct layout.reg.CAP))
  /-- [P]/[J] as `KDispHypsKVU32.mid` without the two discharged fields. -/
  mid : ∀ ct rg sr cr, sched.cur_thread st s = ok ct → MidSysR n c rg sr cr →
    JEntryAtR7V arI AR Z s a σ ∧
    JPathAtMU30 (L := L) arI AR Z H Cs D s a σ ct false false true true (L.mem s (regA ct rg))

variable {arI}

/-- `JEntryAtR7T` from `JEntryAtR7V` and `ArchTotal` (`num` is `ioapics`, `mask` is total). -/
theorem JEntryAtR7V.toT (hA : P0.ArchTotal arI) {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} (h : JEntryAtR7V arI AR Z s ar σ) : JEntryAtR7T arI AR Z s ar σ :=
  ⟨h.ioapics, ⟨h.ioapics, h.pins, h.map, h.mapr, fun a irq b => by
    obtain ⟨v, hv, -⟩ := spec_exists (hA.mask_irq a irq b)
    exact ⟨v, hv⟩⟩⟩

/-- `JEntryAtR7V` from `JEntryAtR7T` (fields dropped). -/
theorem JEntryAtR7T.toV {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} (h : JEntryAtR7T arI AR Z s ar σ) : JEntryAtR7V arI AR Z s ar σ :=
  ⟨h.ioapics, h.archIrq.pins, h.archIrq.map, h.archIrq.mapr⟩

/-- **`KDispHypsKVU35` gives `KDispHypsKVU32`** under `ArchTotal`. -/
theorem KDispHypsKVU35.toU32 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S}
    {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : KDispHypsKVU35 (L := L) arI AR Z H Cs D s a σ n c) (hA : P0.ArchTotal arI) :
    KDispHypsKVU32 (L := L) arI AR Z H Cs D s a σ n c :=
  ⟨fun ct call bl don hct hi => ⟨(h.inv ct call bl don hct hi).1.toT hA, (h.inv ct call bl don hct hi).2⟩,
   fun ct rg sr cr hct hm => ⟨(h.mid ct rg sr cr hct hm).1.toT hA, (h.mid ct rg sr cr hct hm).2⟩⟩

/-- **`KDispHypsKVU32` gives `KDispHypsKVU35`.** -/
theorem KDispHypsKVU32.toU35 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S}
    {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : KDispHypsKVU32 (L := L) arI AR Z H Cs D s a σ n c) :
    KDispHypsKVU35 (L := L) arI AR Z H Cs D s a σ n c :=
  ⟨fun ct call bl don hct hi => ⟨(h.inv ct call bl don hct hi).1.toV, (h.inv ct call bl don hct hi).2⟩,
   fun ct rg sr cr hct hm => ⟨(h.mid ct rg sr cr hct hm).1.toV, (h.mid ct rg sr cr hct hm).2⟩⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)
