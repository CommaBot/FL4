/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN g4h): **FL4's decoders of the
IO port and IRQ handler caps with `MR`** (arch only).

* `MRKeepIo arI AR` [P]: `port_in` / `port_out` keep `AR` at every second
  argument (with `AR := MR`: a port access changes no IRQ mask, pending line
  or clock; l4v: `in8` / `in16` / `in32` / `out8` / `out16` / `out32` are
  `machine_op_lift`s of the machine's opaque rest, outside `irq_masks`,
  `irq_state`, `time_state`, `last_machine_time`). Arch-only, the shape of
  `MRKeepD`'s fields.
* `MKD.ioport_decode`, `MKD.decode_ioport`: FL4's decode of an IO port cap
  keeps `MR` (the walk of MachKeepD with the two port fields).
* `MKD.decode_irq_handler_mr`: FL4's decode of an IRQ handler cap ends, at
  the Ack label, at the arch state of the one `mask_irq irq false` (with
  `MR`: `MachPlat.mask`, the line unmasked), and at every other
  label at `MR` of the start's (Set / Clear: `cdt.delete_one` by
  `MKD.cdt_delete_one`, `cdt.insert` writes no arch state).
-/
import Fl4Proofs.P3.MachKeepG4d
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

section
variable {A C : Type} (arI : machine.Arch A)

/-- **[P] The port operations keep `AR`** (module docstring). -/
structure MRKeepIo (AR : A → C → Prop) : Prop where
  port_in : ∀ a p z c, AR a c → arI.port_in a p z ⦃ r => AR r.2 c ⦄
  port_out : ∀ a p z d c, AR a c → arI.port_out a p z d ⦃ a' => AR a' c ⦄

end

set_option hygiene false in
/-- `mkd_walk` with `MRKeepIo`'s fields (named `hIo`). -/
macro "mkdio_walk" : tactic => `(tactic| ((repeat' (first | mkd_call | (refine WP.spec_bind (hIo.port_in _ _ _ _ (by assumption)) (fun _ _ => ?_)) | (refine WP.spec_bind (hIo.port_out _ _ _ _ _ (by assumption)) (fun _ _ => ?_)) | (exact hIo.port_out _ _ _ _ _ (by assumption)) | p0_ite_head | (simp only [bind_tc_ok, bind_ok, bind_assoc_eq, Aeneas.Std.bind_assoc, Aeneas.Std.uncurry]) | p0_cases_prod | (dsimp only) | step | split)) <;> mkd_close))

section
variable {S A C : Type} {st : machine.Store S} {arI : machine.Arch A} {AR : A → C → Prop}
  (hS : P0.StoreTotal st) (hA : P0.ArchTotal arI) (hK : MRKeepD arI AR) (hIo : MRKeepIo arI AR) {c₀ : C}
include hS hA hK hIo
set_option linter.unusedSectionVars false

set_option maxHeartbeats 4000000 in
theorem MKD.ioport_decode {s : S} {a : A} {lbl length : Std.U64} {cap : capability.Cap} {call : Bool}
    {buf : Std.U64} (h : AR a c₀) :
    ioport.decode st arI s a lbl length cap call buf ⦃ r => AR r.2.2 c₀ ⦄ := by
  unfold ioport.decode; mkdio_walk

set_option maxHeartbeats 4000000 in
/-- **FL4's decode of an IO port cap keeps `MR`** (module docstring). -/
theorem MKD.decode_ioport {s : S} {a : A} {lbl length : Std.U64} {slot : obj.Slot} {first last z : Std.U64}
    {blk call don fp : Bool} {buf : Std.U64} {extra : Array obj.Slot 3#usize} (h : AR a c₀) :
    syscall.decode_invocation st arI s a lbl length slot (.IoPort first last z) blk call don fp buf extra ⦃ r =>
      AR r.2.2 c₀ ⦄ := by
  unfold syscall.decode_invocation ioport.decode; mkdio_walk

end

section
variable {S A C : Type} {st : machine.Store S} {arI : machine.Arch A} {AR : A → C → Prop}
  (hS : P0.StoreTotal st) (hA : P0.ArchTotal arI) (hK : MRKeepD arI AR) {c₀ : C}
include hS hA hK
set_option linter.unusedSectionVars false

set_option maxHeartbeats 4000000 in
/-- **FL4's decode of an IRQ handler cap** (module docstring): at the Ack
label the arch state after the one `mask_irq irq false` (related at `c₁` by
`hm`), at every other label the start's. -/
theorem MKD.decode_irq_handler_mr {s : S} {a : A} {lbl length : Std.U64} {slot : obj.Slot} {irq : Std.U64}
    {blk call don fp : Bool} {buf : Std.U64} {extra : Array obj.Slot 3#usize} {c₁ : C}
    (hm : arI.mask_irq a irq false ⦃ a' => AR a' c₁ ⦄) (h : AR a c₀) :
    syscall.decode_invocation st arI s a lbl length slot (.IrqHandler irq) blk call don fp buf extra ⦃ r =>
      AR r.2.2 (if r.1 = .Ok () then (if lbl = fl4_abi.label.IRQAckIRQ then c₁ else c₀) else c₀) ⦄ := by
  unfold syscall.decode_invocation interrupt.decode_irq_handler
  by_cases hl : lbl = fl4_abi.label.IRQAckIRQ
  · simp only [if_pos hl]
    repeat' (first | (refine WP.spec_bind hm (fun _ _ => ?_)) |
      (simp only [bind_tc_ok, bind_ok, Aeneas.Std.bind_assoc]) | step)
    all_goals (first | assumption | (rw [WP.spec_ok]; simp only [↓reduceIte]; assumption))
  · simp only [if_neg hl, ite_self]
    mkd_walk

end

end Fl4Proofs.P3
