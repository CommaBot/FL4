/-
P3 (line p3J, gen 4): **`kernel_entry_reachU38`** = `kernel_entry_reachU36` with the per-entry [P] fields
`JEntryAtR7V.ioapics` and `.pins` (inventory E1 / E3) discharged by a carried fact.

* **The spec side is kept**: no spec step writes `x64_num_ioapics` / `x64_ioapic_nirqs` (SpecInvIox:
  `kentry_ioxV`, `kcall_ioxV`, `fip_ioxV`, `budget_ioxV`), so `ioxV` is the boot state's at every reachable
  state.
* **`IoaRel arI σ`** [P] (start condition, carried): FL4's backend answers `num_ioapics` with one value `nA`
  at every arch state, equal to the spec's `x64_num_ioapics`, and for each IOAPIC below `nA` `ioapic_pins`
  equals the spec's `x64_ioapic_nirqs` (at least one pin), at every arch state (FL4 x86_64 `arch.rs`:
  `ioapic::count()` / `ioapic::pins(i)` are fixed at boot from the ACPI MADT; the spec's are set once by
  `init_arch_state`). It reads the spec state only through `ioxV` (`IoaRel.frame`), so it is kept.
* `JReachU38 := JReachU34 ∧ IoaRel arI σ`. `JEntryAtR7W` = `JEntryAtR7V` without `ioapics` and `pins`;
  `KDispHypsKVU38` = `KDispHypsKVU36` on `JEntryAtR7W`; `KDispHypsKVU38.toU36` (from `IoaRel` at the
  dispatch state, `BudgetAt.ioaRel`).

**Premise diff U36 → U38**: `hJ : JReachU34` ↦ `hJ : JReachU38` (the start condition `IoaRel`); in the
syscall clause `KDispHypsKVU36 …` ↦ `KDispHypsKVU38 …` (`ioapics`, `pins` removed in `inv` and `mid`).
Conclusion: U36's with every exit's `JReachU34` ↦ `JReachU38`. Everything else verbatim. [W] 0.

**`kernel_entry_reachU36_of38`**: U36's statement with one more hypothesis, `hIR : IoaRel arI σ`, at the
entry state. U36's own premises cannot give it: U36 asks the IOAPIC agreement only per entry, at the dispatch
state of an invocation, while U38 needs it as a fact about the backend at the start. So U38 covers exactly
U36's states where the backend's IOAPIC counts are the spec's, and there it implies U36.

**Finding (jboot witness)**: the witness arch `warI` (P2/WitPlat: `modelArch` with the timer fields) answers
`num_ioapics = 0` (XTopJointMachRel `modelArch`), while `fInitASt` (`initASt`'s arch state) has
`x64_num_ioapics = 1`. So `IoaRel warI fInitASt` is false, and so is U36's per-entry `ioapics` at every entry
from the witness: the invocation half of U36's syscall clause is vacuous on the witness platform. A witness
arch with one IOAPIC of 24 pins (`ioapicIRQLines`) would meet `IoaRel` (open).
No sorry.
-/
import Fl4Proofs.P3.XTopJointKEntryU36
import Fl4Proofs.P3.SpecInvIox
import Fl4Proofs.P3.MdbFull
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The backend's IOAPIC counts are the spec's** [P] (module docstring; start condition, carried). -/
def IoaRel (σ : Fl4Spec.State Unit) : Prop :=
  ∃ nA : U64, (∀ a, arI.num_ioapics a = ok nA) ∧ nA.bv = σ.archState.x64NumIoapics ∧
    ∀ a (i : U64), i.val < nA.val →
      ∃ p, arI.ioapic_pins a i = ok p ∧ p.val = (σ.archState.x64IoapicNirqs i.bv).toNat ∧ 0 < p.val

/-- `JEntryAtR7V` without `ioapics` and `pins`. -/
structure JEntryAtR7W (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (s : S) (ar : A) (σ : Fl4Spec.State Unit) :
    Prop where
  /-- [P] `ArchIrqRelN.map`: in-range IOAPIC routing succeeds and routes (`true`). -/
  map : ∀ (a : A) (n i p l po v np : U64), arI.num_ioapics a = ok n → ¬ i >= n → arI.ioapic_pins a i = ok np →
    ¬ p >= np → ¬ l > 1#u64 → ¬ po > 1#u64 → ∃ a', arI.ioapic_map a i p l po v = ok (true, a')
  /-- [P] `ArchIrqRelN.mapr`: the remapped form. -/
  mapr : ∀ (a : A) (n i p l po v h np : U64), arI.num_ioapics a = ok n → ¬ i >= n → arI.ioapic_pins a i = ok np →
    ¬ p >= np → ¬ l > 1#u64 → ¬ po > 1#u64 → ¬ h >= 65536#u64 →
    ∃ a', arI.ioapic_map_remapped a i p l po v h = ok (true, a')

/-- **`KDispHypsKVU36` with `JEntryAtR7W`.** -/
structure KDispHypsKVU38 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets)
    (H : P1.Heap) (Cs D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64) (c : Fl4Spec.Syscall) : Prop where
  /-- [P]/[J] as `KDispHypsKVU36.inv` without `ioapics` / `pins`. -/
  inv : ∀ ct call bl don, sched.cur_thread st s = ok ct → InvSys n call bl don →
    JEntryAtR7W arI AR Z s a σ ∧
    JPathAtMU35 (L := L) arI AR Z H Cs D s a σ ct call bl don false (L.mem s (regA ct layout.reg.CAP))
  /-- [P]/[J] as `KDispHypsKVU36.mid` without `ioapics` / `pins`. -/
  mid : ∀ ct rg sr cr, sched.cur_thread st s = ok ct → MidSysR n c rg sr cr →
    JEntryAtR7W arI AR Z s a σ ∧
    JPathAtMU35 (L := L) arI AR Z H Cs D s a σ ct false false true true (L.mem s (regA ct rg))

variable {arI}

/-- `IoaRel` reads the spec state only through `ioxV`. -/
theorem IoaRel.frame {σ σ' : Fl4Spec.State Unit} (h : IoaRel arI σ) (e : SInvIox.ioxV σ' = SInvIox.ioxV σ) :
    IoaRel arI σ' := by
  have e1 : σ'.archState.x64NumIoapics = σ.archState.x64NumIoapics := congrArg Prod.fst e
  have e2 : σ'.archState.x64IoapicNirqs = σ.archState.x64IoapicNirqs := congrArg Prod.snd e
  unfold IoaRel at h ⊢
  rw [e1, e2]; exact h

/-- `JEntryAtR7V` from `JEntryAtR7W` and `IoaRel`. -/
theorem JEntryAtR7W.toV {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (h : JEntryAtR7W arI AR Z s ar σ) (hI : IoaRel arI σ) : JEntryAtR7V (S := S) arI AR Z s ar σ := by
  obtain ⟨nA, hn, hb, hp⟩ := hI
  refine ⟨⟨nA, hn ar, hb⟩, fun n hn' i hi => ?_, h.map, h.mapr⟩
  have e : n = nA := eq_of_ok_eq (hn'.symm.trans (hn ar))
  subst e
  exact hp ar i hi

/-- `JEntryAtR7W` from `JEntryAtR7V` (fields dropped). -/
theorem JEntryAtR7V.toW {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (h : JEntryAtR7V (S := S) arI AR Z s ar σ) : JEntryAtR7W arI AR Z s ar σ :=
  ⟨h.map, h.mapr⟩

/-- **`KDispHypsKVU38` gives `KDispHypsKVU36`** under `IoaRel`. -/
theorem KDispHypsKVU38.toU36 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S}
    {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : KDispHypsKVU38 (L := L) arI AR Z H Cs D s a σ n c) (hI : IoaRel arI σ) :
    KDispHypsKVU36 (L := L) arI AR Z H Cs D s a σ n c :=
  ⟨fun ct call bl don hct hi => ⟨(h.inv ct call bl don hct hi).1.toV hI, (h.inv ct call bl don hct hi).2⟩,
   fun ct rg sr cr hct hm => ⟨(h.mid ct rg sr cr hct hm).1.toV hI, (h.mid ct rg sr cr hct hm).2⟩⟩

/-- **`KDispHypsKVU36` gives `KDispHypsKVU38`.** -/
theorem KDispHypsKVU36.toU38 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S}
    {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : KDispHypsKVU36 (L := L) arI AR Z H Cs D s a σ n c) :
    KDispHypsKVU38 (L := L) arI AR Z H Cs D s a σ n c :=
  ⟨fun ct call bl don hct hi => ⟨(h.inv ct call bl don hct hi).1.toW, (h.inv ct call bl don hct hi).2⟩,
   fun ct rg sr cr hct hm => ⟨(h.mid ct rg sr cr hct hm).1.toW, (h.mid ct rg sr cr hct hm).2⟩⟩

/-- `IoaRel` at the dispatch state (the FaultIP write and the budget front keep `ioxV`). -/
theorem BudgetAt.ioaRel {σ σb : Fl4Spec.State Unit} (h : IoaRel arI σ) (hb : BudgetAt σ σb true) :
    IoaRel arI σb := by
  obtain ⟨σ0, h0, hb⟩ := hb
  exact h.frame ((SInvIox.budget_ioxV σ0 _ hb).trans (SInvIox.fip_ioxV _ σ _ h0))

/-- `IoaRel` at every `EvOut` outcome. -/
theorem EvOut.ioaRel {fip : Bool} {ev : Fl4Spec.Event} {σ σ' : Fl4Spec.State Unit} (h : IoaRel arI σ)
    (hO : EvOut fip ev σ σ') : IoaRel arI σ' := by
  cases fip with
  | false => exact h.frame (SInvIox.kcall_ioxV true ev σ _ hO)
  | true =>
    obtain ⟨w, hw, hO⟩ := hO
    exact h.frame ((SInvIox.kcall_ioxV true ev w.2 _ hO).trans (SInvIox.fip_ioxV _ σ w hw))

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **The reachable joint states with the backend's IOAPIC counts** (module docstring). -/
abbrev JReachU38 (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  JReachU34 (L := L) arI AR MR s a σ ∧ IoaRel arI σ
