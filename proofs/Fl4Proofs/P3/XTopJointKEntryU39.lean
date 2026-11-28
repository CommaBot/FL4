/-
P3 (line p3J, gen 5): **`kernel_entry_reachU39`** = `kernel_entry_reachU38` with the per-entry [P] fields
`JEntryAtR7W.map` / `.mapr` (IOAPIC routing succeeds) stated once, at the backend level.

* `JEntryAtR7W`'s two fields mention only the arch `arI` (they quantify every arch state `a`; the joint state,
  ghosts and spec state are phantom), so asking them per entry, at every dispatch state of an invocation, asks
  one backend fact again and again. **`IoaMap arI`** [P] (platform premise, global): exactly those two fields
  (FL4 x86_64 `arch.rs` `ioapic_map` / `ioapic_map_remapped`: in range (`ioapic < count()`, `pin < pins(ioapic)`,
  level / polarity bits, handle below 2^16) the routing writes the redirection entry and answers `true`).
* `KDispHypsKVU39` = `KDispHypsKVU38` without `JEntryAtR7W` (only the `JPathAtMU30` path [J]s in `inv` and
  `mid`); `KDispHypsKVU39.toU38` (from `IoaMap`), `KDispHypsKVU38.toU39` (dropped).

**Premise diff U38 → U39**: new global premise `hMap : IoaMap arI` [P]; in the syscall clause
`KDispHypsKVU38 …` ↦ `KDispHypsKVU39 …` (`map`, `mapr` removed in `inv` and `mid`). Start condition
(`JReachU38`) and conclusion verbatim. [W] 0. The global premise is not weaker than the per-entry one: U38 asks
it only when an invocation is dispatched, U39 always; at any platform where some entry dispatches an invocation
the two coincide (`IoaMap.of_entry`).

Named premises: those of U38 (module XTopJointKEntryU38: the platform premises [P], the start condition
`JReachU38` with `IoaRel` [P], the per-entry syscall [J]s `KDispHypsKVU39` (path), `JDecMRLK`, `KFinAtR13`, the
event [J]s `KFinEv13`) plus `IoaMap` [P].
No sorry.
-/
import Fl4Proofs.P3.XTopJointKEntryU38
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **IOAPIC routing succeeds in range** [P] (module docstring; platform premise, global): `JEntryAtR7W`'s
fields, which mention only the backend. -/
structure IoaMap : Prop where
  /-- [P] `ArchIrqRelN.map`: in-range IOAPIC routing succeeds and routes (`true`). -/
  map : ∀ (a : A) (n i p l po v np : U64), arI.num_ioapics a = ok n → ¬ i >= n → arI.ioapic_pins a i = ok np →
    ¬ p >= np → ¬ l > 1#u64 → ¬ po > 1#u64 → ∃ a', arI.ioapic_map a i p l po v = ok (true, a')
  /-- [P] `ArchIrqRelN.mapr`: the remapped form. -/
  mapr : ∀ (a : A) (n i p l po v h np : U64), arI.num_ioapics a = ok n → ¬ i >= n → arI.ioapic_pins a i = ok np →
    ¬ p >= np → ¬ l > 1#u64 → ¬ po > 1#u64 → ¬ h >= 65536#u64 →
    ∃ a', arI.ioapic_map_remapped a i p l po v h = ok (true, a')

/-- **`KDispHypsKVU38` without `JEntryAtR7W`**: the path [J]s only. -/
structure KDispHypsKVU39 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets)
    (H : P1.Heap) (Cs D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64) (c : Fl4Spec.Syscall) : Prop where
  /-- [J] as `KDispHypsKVU38.inv` without `map` / `mapr`. -/
  inv : ∀ ct call bl don, sched.cur_thread st s = ok ct → InvSys n call bl don →
    JPathAtMU30 (L := L) arI AR Z H Cs D s a σ ct call bl don false (L.mem s (regA ct layout.reg.CAP))
  /-- [J] as `KDispHypsKVU38.mid` without `map` / `mapr`. -/
  mid : ∀ ct rg sr cr, sched.cur_thread st s = ok ct → MidSysR n c rg sr cr →
    JPathAtMU30 (L := L) arI AR Z H Cs D s a σ ct false false true true (L.mem s (regA ct rg))

variable {arI}

/-- `JEntryAtR7W` is `IoaMap` (at any joint state). -/
theorem IoaMap.toW (hM : IoaMap arI) {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} : JEntryAtR7W (S := S) arI AR Z s ar σ :=
  ⟨hM.map, hM.mapr⟩

/-- `IoaMap` from one `JEntryAtR7W` (any joint state): the per-entry and the global premise coincide as soon
as one entry asks it. -/
theorem IoaMap.of_entry {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (h : JEntryAtR7W (S := S) arI AR Z s ar σ) : IoaMap arI :=
  ⟨h.map, h.mapr⟩

/-- **`KDispHypsKVU39` gives `KDispHypsKVU38`** under `IoaMap`. -/
theorem KDispHypsKVU39.toU38 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S}
    {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : KDispHypsKVU39 (L := L) arI AR Z H Cs D s a σ n c) (hM : IoaMap arI) :
    KDispHypsKVU38 (L := L) arI AR Z H Cs D s a σ n c :=
  ⟨fun ct call bl don hct hi => ⟨hM.toW, h.inv ct call bl don hct hi⟩,
   fun ct rg sr cr hct hm => ⟨hM.toW, h.mid ct rg sr cr hct hm⟩⟩

end

end

end Fl4Proofs.P3.SInvR.G5
