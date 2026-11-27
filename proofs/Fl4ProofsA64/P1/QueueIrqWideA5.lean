/-
P1 (aarch64): **the base layer of the IRQ-bound widening** (namespace `W7.R.A5.I`, the A5 shadow pattern one level
down): `DelCapOK` with GIC's bound — an IrqHandler cap names an IRQ below `layout::irq::COUNT` = 5376
(layout.rs; `irq::of`, QueueDecIrq's `layout.irq.of.lt`) instead of x86's 128 — and the bridges to the 128 form.

* `I.DelCapOK` = `W7.DelCapOK` with `i.val < 5376` for `.IrqHandler i`; `I.DelCapOK.null`;
* `I.DelCapOK.of7`: the 128 form implies the 5376 form;
* `I.DelCapOK.to7`: a 5376-typed cap that is no IrqHandler cap (or names an IRQ below 128) is 128-typed;
* `I.FinGapAt`: `W7.R.FinGapAt` over `I.DelCapOK`; **`I.FinGapAt.ofR`**: a finalisation gap of the 128 form for
  kinds without IrqHandler caps is one of the 5376 form (the in-hypothesis bound is only read by the IRQ kind,
  the out-caps convert by `of7`). So every per-kind gap but the IRQ kind's transfers unchanged; the IRQ kind is
  `irq_slotW_a64`'s (QueueIrqWide).

This is the layer the shadow copy of the deletion chain (`A5.DelGapsAt` / `A5.DelPlaceAt` with `cap` over
`I.DelCapOK` and `irq` at 5376, and the QueueDelVs5 / QueueDecDel5 text over them) builds on; that copy is not
in this module. No named premises.
-/
import Fl4ProofsA64.P1.QueueDelVs5
import Fl4ProofsA64.P1.QueueIrqWide
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

namespace W7
namespace R
namespace A5
namespace I

/-- **A cap's typing for its deletion, AArch64** (`W7.DelCapOK` with GIC's 5376 IRQs). -/
def DelCapOK (T Ω Sg : Set U64) (H : Heap) (Rp Nt : Set U64) (c : capability.Cap) : Prop :=
  CapTyped H Rp Nt c ∧ (∀ i, c = .IrqHandler i → i.val < 5376) ∧
  (∀ f l o, c = .IoPort f l o → f.val ≤ l.val ∧ l.val < 65536) ∧
  (∀ p r g b, c = .CNode p r g b → SlotW T Ω Sg p ∧ ∀ i : U64, i.val < 2 ^ (r.val % 64) → SlotW T Ω Sg (slotIdx p i)) ∧
  (∀ p t n, c = .Zombie p t n → SlotW T Ω Sg p ∧ ∀ i : U64, i.val < n.val → SlotW T Ω Sg (slotIdx p i)) ∧
  (∀ p, c = .Thread p → p ∈ T)

theorem DelCapOK.null : DelCapOK T Ω Sg H Rp Nt .Null := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> simp_all

/-- The 128 form implies the 5376 form. -/
theorem DelCapOK.of7 {c : capability.Cap} (h : W7.DelCapOK T Ω Sg H Rp Nt c) : DelCapOK T Ω Sg H Rp Nt c :=
  ⟨h.1, fun i e => by have := h.2.1 i e; omega, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- A 5376-typed cap whose IRQ (if an IrqHandler cap) is below 128 is 128-typed. -/
theorem DelCapOK.to7 {c : capability.Cap} (h : DelCapOK T Ω Sg H Rp Nt c)
    (hi : ∀ i, c = .IrqHandler i → i.val < 128) : W7.DelCapOK T Ω Sg H Rp Nt c :=
  ⟨h.1, hi, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- A 5376-typed cap that is no IrqHandler cap is 128-typed. -/
theorem DelCapOK.to7n {c : capability.Cap} (h : DelCapOK T Ω Sg H Rp Nt c)
    (hn : ∀ i, c ≠ .IrqHandler i) : W7.DelCapOK T Ω Sg H Rp Nt c :=
  DelCapOK.to7 h fun i e => absurd e (hn i)

/-- `W7.R.FinGapAt` over the 5376 form. -/
def FinGapAt (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A) (T Cs Ω : Set U64)
    (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (P : capability.Cap → Prop) (s0 : S) : Prop :=
  ∀ (Ac : Set U64) (s : S) (a : A) (c : capability.Cap) (fin : Bool),
    Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s → DelCapOK T Ω Sg H Rp Nt c → FinPl st Scs s c → P c →
    objects.finalise_cap st ar s a c fin false ⦃ r => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧
      DelCapOK T Ω Sg H Rp Nt r.1.1 ∧ DelCapOK T Ω Sg H Rp Nt r.1.2 ⦄

/-- **A 128-form finalisation gap for kinds without IrqHandler caps is a 5376-form gap.** -/
theorem FinGapAt.ofR {A : Type _} {ar : machine.Arch A} {P : capability.Cap → Prop} {s0 : S}
    (g : W7.R.FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z P s0) (hP : ∀ c, P c → ∀ i, c ≠ .IrqHandler i) :
    FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z P s0 := fun Ac s a c fin h hc hpl hp =>
  WP.spec_mono (g Ac s a c fin h (DelCapOK.to7n hc (hP c hp)) hpl hp) fun r ⟨h1, h2, h3⟩ => ⟨h1, DelCapOK.of7 h2, DelCapOK.of7 h3⟩

/-- A 5376-form gap read at a 128-typed cap (the hypothesis converts by `of7`). -/
theorem FinGapAt.toR {A : Type _} {ar : machine.Arch A} {P : capability.Cap → Prop} {s0 : S}
    (g : FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z P s0) :
    ∀ (Ac : Set U64) (s : S) (a : A) (c : capability.Cap) (fin : Bool),
      Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s → W7.DelCapOK T Ω Sg H Rp Nt c → FinPl st Scs s c → P c →
      objects.finalise_cap st ar s a c fin false ⦃ r => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧
        DelCapOK T Ω Sg H Rp Nt r.1.1 ∧ DelCapOK T Ω Sg H Rp Nt r.1.2 ⦄ :=
  fun Ac s a c fin h hc hpl hp => g Ac s a c fin h (DelCapOK.of7 hc) hpl hp

end I
end A5
end R
end W7

end

end Fl4ProofsA64.P1
