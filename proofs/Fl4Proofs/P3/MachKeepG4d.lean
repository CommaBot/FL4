/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN g4d): **FL4's decoders of the
quiet cap kinds keep `MR`** (`MKD.*`, arch only): MachKeepF's walk extended to
the arch-threading call graphs of `domain.decode`, `schedcontext.decode`,
`schedcontext.decode_sched_control`, `vspace.decode` (Frame / page tables /
ASID control / ASID pool), `ioport.decode_control` and `ipc.do_reply_transfer`
(scripted: scratch/mr6/topo.py + mkdgen.py on scratch/g4d/dec_order.txt).
Every arch operation reached is a field of `MRKeepD` or a query returning no
arch state (`virtualization`, `private_device_frame`, `kernel_wcet_ticks`,
`ticks_to_us`, `us_to_ticks`, `max_us`). `MKD.decode_quiet`: FL4's
`decode_invocation` of a cap of a quiet kind (`QuietF`: not CNode, Thread,
Untyped, IrqControl, IrqHandler, IoPort, Vcpu, Ept) keeps `MR`.
-/
import Fl4Proofs.P3.MachKeepF
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

/-- **The quiet FL4 cap kinds** (module docstring): their decoders reach no
clock, interrupt or port operation. -/
def QuietF : capability.Cap → Prop
  | .CNode .. => False
  | .Thread _ => False
  | .Untyped .. => False
  | .IrqControl => False
  | .IrqHandler _ => False
  | .IoPort .. => False
  | .Vcpu _ => False
  | .Ept .. => False
  | _ => True

section
variable {S A C : Type} {st : machine.Store S} {arI : machine.Arch A} {AR : A → C → Prop}
  (hS : P0.StoreTotal st) (hA : P0.ArchTotal arI) (hK : MRKeepD arI AR) {c₀ : C}
include hS hA hK
set_option linter.unusedSectionVars false

set_option maxHeartbeats 4000000 in
theorem MKD.debug_configure_single_stepping {s : S} {a : A} {t : obj.Tcb} {bp : Std.U64} {n_instr : Std.U64} {is_reply : Bool} (h : AR a c₀) :
    debug.configure_single_stepping st arI s a t bp n_instr is_reply ⦃ r => AR r.2.2 c₀ ⦄ := by
  unfold debug.configure_single_stepping; mkd_walk

set_option maxHeartbeats 4000000 in
theorem MKD.domain_decode {s : S} {a : A} {lbl : Std.U64} {length : Std.U64} {buf : Std.U64} {extra : Array obj.Slot 3#usize} (h : AR a c₀) :
    domain.decode st arI s a lbl length buf extra ⦃ r => AR r.2.2 c₀ ⦄ := by
  unfold domain.decode; mkd_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 200000 in
theorem MKD.ept_map_frame {s : S} {a : A} {length : Std.U64} {cap : capability.Cap} {dest : obj.Slot} {buf : Std.U64} {ex : Array obj.Slot 3#usize} (h : AR a c₀) :
    ept.map_frame st arI s a length cap dest buf ex ⦃ r => AR r.2.2 c₀ ⦄ := by
  unfold ept.map_frame; mkd_walk
  all_goals (rw [WP.spec_ok]; exact h)

set_option maxHeartbeats 4000000 in
theorem MKD.faults_handle_fault_reply {s : S} {a : A} {receiver : obj.Tcb} {sender : obj.Tcb} (h : AR a c₀) :
    faults.handle_fault_reply st arI s a receiver sender ⦃ r => AR r.2.2 c₀ ⦄ := by
  unfold faults.handle_fault_reply; mkd_walk

set_option maxHeartbeats 4000000 in
theorem MKD.ioport_decode_control {s : S} {a : A} {lbl : Std.U64} {length : Std.U64} {slot : obj.Slot} {buf : Std.U64} {extra : Array obj.Slot 3#usize} (h : AR a c₀) :
    ioport.decode_control st arI s a lbl length slot buf extra ⦃ r => AR r.2.2 c₀ ⦄ := by
  unfold ioport.decode_control; mkd_walk

set_option maxHeartbeats 4000000 in
theorem MKD.ipc_do_reply_transfer {s : S} {a : A} {sender : obj.Tcb} {r : obj.Reply} {grant : Bool} (h : AR a c₀) :
    ipc.do_reply_transfer st arI s a sender r grant ⦃ r => AR r.2 c₀ ⦄ := by
  unfold ipc.do_reply_transfer; mkd_walk

set_option maxHeartbeats 4000000 in
theorem MKD.schedcontext_bind_tcb {s : S} {a : A} {sc : obj.Sc} {t : obj.Tcb} (h : AR a c₀) :
    schedcontext.bind_tcb st arI s a sc t ⦃ r => AR r.2 c₀ ⦄ := by
  unfold schedcontext.bind_tcb; mkd_walk

set_option maxHeartbeats 4000000 in
theorem MKD.schedcontext_configure_flags {s : S} {a : A} {target : obj.Sc} {cpu : Std.U64} {budget : Std.U64} {period : Std.U64} {max_refills : Std.U64} {badge : Std.U64} {flags : Std.U64} (h : AR a c₀) :
    schedcontext.configure_flags st arI s a target cpu budget period max_refills badge flags ⦃ r => AR r.2 c₀ ⦄ := by
  unfold schedcontext.configure_flags; mkd_walk

set_option maxHeartbeats 4000000 in
theorem MKD.schedcontext_yield_to {s : S} {a : A} {sc : obj.Sc} {call : Bool} (h : AR a c₀) :
    schedcontext.yield_to st arI s a sc call ⦃ r => AR r.2 c₀ ⦄ := by
  unfold schedcontext.yield_to; mkd_walk

set_option maxHeartbeats 4000000 in
theorem MKD.schedcontext_decode {s : S} {a : A} {lbl : Std.U64} {sc : obj.Sc} {call : Bool} {extra : Array obj.Slot 3#usize} (h : AR a c₀) :
    schedcontext.decode st arI s a lbl sc call extra ⦃ r => AR r.2.2 c₀ ⦄ := by
  unfold schedcontext.decode; mkd_walk

set_option maxHeartbeats 4000000 in
theorem MKD.schedcontext_decode_sched_control {s : S} {a : A} {lbl : Std.U64} {cpu : Std.U64} {length : Std.U64} {buf : Std.U64} {extra : Array obj.Slot 3#usize} (h : AR a c₀) :
    schedcontext.decode_sched_control st arI s a lbl cpu length buf extra ⦃ r => AR r.2.2 c₀ ⦄ := by
  unfold schedcontext.decode_sched_control; mkd_walk

set_option maxHeartbeats 4000000 in
theorem MKD.vspace_write_mapping {s : S} {a : A} {slot : Std.U64} {e : Std.U64} {asid : Std.U64} {vaddr : Std.U64} {defer : Bool} (h : AR a c₀) :
    vspace.write_mapping st arI s a slot e asid vaddr defer ⦃ r => AR r.2 c₀ ⦄ := by
  unfold vspace.write_mapping; mkd_walk

set_option maxHeartbeats 4000000 in
theorem MKD.vspace_decode_page_map {s : S} {a : A} {length : Std.U64} {slot : obj.Slot} {f : vspace.FrameCap} {buf : Std.U64} {ex : Array obj.Slot 3#usize} (h : AR a c₀) :
    vspace.decode_page_map st arI s a length slot f buf ex ⦃ r => AR r.2.2 c₀ ⦄ := by
  unfold vspace.decode_page_map; mkd_walk

set_option maxHeartbeats 4000000 in
theorem MKD.vspace_derive_subframe {s : S} {a : A} {length : Std.U64} {src : obj.Slot} {cap : capability.Cap} {buf : Std.U64} {ex : Array obj.Slot 3#usize} (h : AR a c₀) :
    vspace.derive_subframe st arI s a length src cap buf ex ⦃ r => AR r.2.2 c₀ ⦄ := by
  unfold vspace.derive_subframe; mkd_walk

set_option maxHeartbeats 4000000 in
theorem MKD.vspace_decode_frame {s : S} {a : A} {lbl : Std.U64} {length : Std.U64} {slot : obj.Slot} {cap : capability.Cap} {call : Bool} {buf : Std.U64} {ex : Array obj.Slot 3#usize} (h : AR a c₀) :
    vspace.decode_frame st arI s a lbl length slot cap call buf ex ⦃ r => AR r.2.2 c₀ ⦄ := by
  unfold vspace.decode_frame; mkd_walk

set_option maxHeartbeats 4000000 in
theorem MKD.vspace_decode_table_map {s : S} {a : A} {length : Std.U64} {slot : obj.Slot} {cap : capability.Cap} {level : Std.U64} {ptr : Std.U64} {buf : Std.U64} {ex : Array obj.Slot 3#usize} (h : AR a c₀) :
    vspace.decode_table_map st arI s a length slot cap level ptr buf ex ⦃ r => AR r.2.2 c₀ ⦄ := by
  unfold vspace.decode_table_map; mkd_walk

set_option maxHeartbeats 4000000 in
theorem MKD.vspace_decode_table_unmap {s : S} {a : A} {slot : obj.Slot} {cap : capability.Cap} {level : Std.U64} {ptr : Std.U64} {mapped : Bool} {masid : Std.U64} {mvaddr : Std.U64} (h : AR a c₀) :
    vspace.decode_table_unmap st arI s a slot cap level ptr mapped masid mvaddr ⦃ r => AR r.2.2 c₀ ⦄ := by
  unfold vspace.decode_table_unmap; mkd_walk

set_option maxHeartbeats 4000000 in
theorem MKD.vspace_decode_table {s : S} {a : A} {lbl : Std.U64} {length : Std.U64} {slot : obj.Slot} {cap : capability.Cap} {buf : Std.U64} {ex : Array obj.Slot 3#usize} (h : AR a c₀) :
    vspace.decode_table st arI s a lbl length slot cap buf ex ⦃ r => AR r.2.2 c₀ ⦄ := by
  unfold vspace.decode_table; mkd_walk

set_option maxHeartbeats 4000000 in
theorem MKD.vspace_decode {s : S} {a : A} {lbl : Std.U64} {length : Std.U64} {slot : obj.Slot} {cap : capability.Cap} {call : Bool} {buf : Std.U64} {ex : Array obj.Slot 3#usize} (h : AR a c₀) :
    vspace.decode st arI s a lbl length slot cap call buf ex ⦃ r => AR r.2.2 c₀ ⦄ := by
  unfold vspace.decode; mkd_walk

set_option maxHeartbeats 4000000 in
/-- **FL4's decode of a quiet cap keeps `MR`** (module docstring). -/
theorem MKD.decode_quiet {s : S} {a : A} {lbl length : Std.U64} {slot : obj.Slot} {c : capability.Cap}
    {blk call don fp : Bool} {buf : Std.U64} {extra : Array obj.Slot 3#usize} (hq : QuietF c) (h : AR a c₀) :
    syscall.decode_invocation st arI s a lbl length slot c blk call don fp buf extra ⦃ r => AR r.2.2 c₀ ⦄ := by
  cases c <;> simp only [QuietF] at hq <;> unfold syscall.decode_invocation <;> mkd_walk

end

end Fl4Proofs.P3
