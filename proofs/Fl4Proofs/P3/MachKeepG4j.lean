/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN g4j): **FL4's Thread cap decode
at a label that installs no cap keeps `MR`** (`MKD.*`, arch only): MachKeepD's
walk extended to the arch-threading callees of `tcb.decode` reached at the
labels other than SetEPTRoot, Configure, SetSchedParams, SetIPCBuffer,
SetSpace and SetTimeoutEndpoint (scratch/mr6/topo.py + mkdgen.py). Every arch
operation reached is a field of `MRKeepD` or a query (`kernel_wcet_ticks`).
SetPriority / SetMCPriority reach `tcb.thread_control_sched` with flags
without `SCHED_UPDATE_FAULT`, so its install branch is never taken
(`MKD.tcb_thread_control_sched_nf`). `MKD.decode_thread_nonins`: FL4's
`decode_invocation` of a Thread cap at such a label keeps `MR`.
-/
import Fl4Proofs.P3.MachKeepG4d
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

section
variable {S A C : Type} {st : machine.Store S} {arI : machine.Arch A} {AR : A → C → Prop}
  (hS : P0.StoreTotal st) (hA : P0.ArchTotal arI) (hK : MRKeepD arI AR) {c₀ : C}
include hS hA hK
set_option linter.unusedSectionVars false

set_option maxHeartbeats 4000000 in
theorem MKD.sched_restart {s : S} {a : A} {t : obj.Tcb} (h : AR a c₀) :
    sched.restart st arI s a t ⦃ r => AR r.2 c₀ ⦄ := by
  unfold sched.restart; mkd_walk

set_option maxHeartbeats 4000000 in
theorem MKD.tcb_copy_registers {s : S} {a : A} {dest : obj.Tcb} {src : obj.Tcb} {flags : Std.U64} (h : AR a c₀) :
    tcb.copy_registers st arI s a dest src flags ⦃ r => AR r.2.2 c₀ ⦄ := by
  unfold tcb.copy_registers; mkd_walk

set_option maxHeartbeats 4000000 in
theorem MKD.tcb_decode_configure_single_stepping {s : S} {a : A} {target : obj.Tcb} {c : tcb.Ctx} (h : AR a c₀) :
    tcb.decode_configure_single_stepping st arI s a target c ⦃ r => AR r.2.2 c₀ ⦄ := by
  unfold tcb.decode_configure_single_stepping; mkd_walk

set_option maxHeartbeats 4000000 in
theorem MKD.tcb_decode_copy_registers {s : S} {a : A} {target : obj.Tcb} {c : tcb.Ctx} (h : AR a c₀) :
    tcb.decode_copy_registers st arI s a target c ⦃ r => AR r.2.2 c₀ ⦄ := by
  unfold tcb.decode_copy_registers; mkd_walk

set_option maxHeartbeats 4000000 in
theorem MKD.tcb_read_registers {s : S} {a : A} {src : obj.Tcb} {suspend : Bool} {n : Std.U64} {call : Bool} (h : AR a c₀) :
    tcb.read_registers st arI s a src suspend n call ⦃ r => AR r.2 c₀ ⦄ := by
  unfold tcb.read_registers; mkd_walk

set_option maxHeartbeats 4000000 in
theorem MKD.tcb_decode_read_registers {s : S} {a : A} {target : obj.Tcb} {c : tcb.Ctx} (h : AR a c₀) :
    tcb.decode_read_registers st arI s a target c ⦃ r => AR r.2.2 c₀ ⦄ := by
  unfold tcb.decode_read_registers; mkd_walk

set_option maxHeartbeats 4000000 in
theorem MKD.tcb_decode_set_flags {s : S} {a : A} {target : obj.Tcb} {c : tcb.Ctx} (h : AR a c₀) :
    tcb.decode_set_flags st arI s a target c ⦃ r => AR r.2.2 c₀ ⦄ := by
  unfold tcb.decode_set_flags; mkd_walk

set_option maxHeartbeats 4000000 in
theorem MKD.tcb_write_registers {s : S} {a : A} {dest : obj.Tcb} {resume : Bool} {n_in : Std.U64} {buf : Std.U64} (h : AR a c₀) :
    tcb.write_registers st arI s a dest resume n_in buf ⦃ r => AR r.2 c₀ ⦄ := by
  unfold tcb.write_registers; mkd_walk

set_option maxHeartbeats 4000000 in
theorem MKD.tcb_decode_write_registers {s : S} {a : A} {target : obj.Tcb} {c : tcb.Ctx} (h : AR a c₀) :
    tcb.decode_write_registers st arI s a target c ⦃ r => AR r.2.2 c₀ ⦄ := by
  unfold tcb.decode_write_registers; mkd_walk

set_option maxHeartbeats 4000000 in
theorem MKD.tcb_fpu_transfer {s : S} {a : A} {target : obj.Tcb} {c : tcb.Ctx} {to_frame : Bool} (h : AR a c₀) :
    tcb.fpu_transfer st arI s a target c to_frame ⦃ r => AR r.2.2 c₀ ⦄ := by
  unfold tcb.fpu_transfer; mkd_walk

set_option maxHeartbeats 4000000 in
/-- `thread_control_sched` with flags that do not update the fault handler:
the install branch is not taken. -/
theorem MKD.tcb_thread_control_sched_nf {s : S} {a : A} {target : obj.Tcb} {slot : obj.Slot}
    {fh : capability.Cap × obj.Slot} {mcp prio : Std.U64} {sc : obj.Sc} {flags : Std.U64}
    (hf : (flags &&& tcb.SCHED_UPDATE_FAULT) = 0#u64) (h : AR a c₀) :
    tcb.thread_control_sched st arI s a target slot fh mcp prio sc flags ⦃ r => AR r.2.2 c₀ ⦄ := by
  unfold tcb.thread_control_sched
  simp only [lift, hf, bind_ok, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  mkd_walk

set_option maxHeartbeats 4000000 in
theorem MKD.tcb_decode_set_priority {s : S} {a : A} {target : obj.Tcb} {c : tcb.Ctx} {prio : Bool} (h : AR a c₀) :
    tcb.decode_set_priority st arI s a target c prio ⦃ r => AR r.2.2 c₀ ⦄ := by
  have hp : (tcb.SCHED_UPDATE_PRIO &&& tcb.SCHED_UPDATE_FAULT) = 0#u64 := by
    simp only [tcb.SCHED_UPDATE_PRIO, tcb.SCHED_UPDATE_FAULT]; decide
  have hm : (tcb.SCHED_UPDATE_MCP &&& tcb.SCHED_UPDATE_FAULT) = 0#u64 := by
    simp only [tcb.SCHED_UPDATE_MCP, tcb.SCHED_UPDATE_FAULT]; decide
  unfold tcb.decode_set_priority
  ((repeat' (first | exact MKD.tcb_thread_control_sched_nf hS hA hK hp (by assumption) | exact MKD.tcb_thread_control_sched_nf hS hA hK hm (by assumption) | mkd_call | p0_ite_head | (simp only [bind_tc_ok, bind_ok, bind_assoc_eq, Aeneas.Std.bind_assoc, Aeneas.Std.uncurry]) | p0_cases_prod | (dsimp only) | step | split)) <;> mkd_close)

/-- **The labels of the Thread cap that install no cap** (module docstring). -/
def TcbNonIns (lbl : Std.U64) : Prop :=
  lbl ≠ fl4_abi.label.TCBSetEPTRoot ∧ lbl ≠ fl4_abi.label.TCBConfigure ∧ lbl ≠ fl4_abi.label.TCBSetSchedParams ∧
    lbl ≠ fl4_abi.label.TCBSetIPCBuffer ∧ lbl ≠ fl4_abi.label.TCBSetSpace ∧
    lbl ≠ fl4_abi.label.TCBSetTimeoutEndpoint

set_option maxHeartbeats 16000000 in
theorem MKD.tcb_decode_nonins {s : S} {a : A} {lbl : Std.U64} {target : obj.Tcb} {c : tcb.Ctx}
    (hl : TcbNonIns lbl) (h : AR a c₀) :
    tcb.decode st arI s a lbl target c ⦃ r => AR r.2.2 c₀ ⦄ := by
  obtain ⟨hE, h5, h8, h10, h11, h9⟩ := hl
  unfold tcb.decode
  simp only [hE, h5, h8, h10, h11, h9, if_false, ↓reduceIte]
  mkd_walk

set_option maxHeartbeats 4000000 in
/-- **FL4's Thread cap decode at a non-installing label keeps `MR`** (module
docstring). -/
theorem MKD.decode_thread_nonins {s : S} {a : A} {lbl length : Std.U64} {slot : obj.Slot} {p : Std.U64}
    {blk call don fp : Bool} {buf : Std.U64} {extra : Array obj.Slot 3#usize} (hl : TcbNonIns lbl) (h : AR a c₀) :
    syscall.decode_invocation st arI s a lbl length slot (.Thread p) blk call don fp buf extra ⦃ r =>
      AR r.2.2 c₀ ⦄ := by
  unfold syscall.decode_invocation
  ((repeat' (first | exact MKD.tcb_decode_nonins hS hA hK hl (by assumption) | mkd_call | p0_ite_head | (simp only [bind_tc_ok, bind_ok, bind_assoc_eq, Aeneas.Std.bind_assoc, Aeneas.Std.uncurry]) | p0_cases_prod | (dsimp only) | step | split)) <;> mkd_close)

set_option maxHeartbeats 4000000 in
theorem MKD.objects_create_arch_object {s : S} {a : A} {t : Std.U64} {base : Std.U64} {device : Bool} (h : AR a c₀) :
    objects.create_arch_object st arI s a t base device ⦃ r => AR r.2.2 c₀ ⦄ := by
  unfold objects.create_arch_object; mkd_walk

set_option maxHeartbeats 4000000 in
theorem MKD.objects_create_object {s : S} {a : A} {t : Std.U64} {base : Std.U64} {user_size : Std.U64} {device : Bool} (h : AR a c₀) :
    objects.create_object st arI s a t base user_size device ⦃ r => AR r.2.2 c₀ ⦄ := by
  unfold objects.create_object; mkd_walk

set_option maxHeartbeats 4000000 in
theorem MKD.objects_create_new_objects_loop {s : S} {a : A} {t : Std.U64} {parent : obj.Slot} {dest_cnode dest_offset
    dest_length base user_size : Std.U64} {device : Bool} {size i : Std.U64} (h : AR a c₀) :
    objects.create_new_objects_loop st arI s a t parent dest_cnode dest_offset dest_length base user_size device size i
      ⦃ r => AR r.2 c₀ ⦄ := by
  unfold objects.create_new_objects_loop
  apply loop.spec_decr_nat (measure := fun x => dest_length.val - x.2.2.val) (inv := fun x => AR x.2.1 c₀)
  · rintro ⟨s1, a1, i1⟩ h1
    dsimp only at h1
    unfold objects.create_new_objects_loop.body
    mkd_walk
  · exact h

set_option maxHeartbeats 4000000 in
theorem MKD.objects_create_new_objects {s : S} {a : A} {t : Std.U64} {parent : obj.Slot} {dest_cnode dest_offset
    dest_length base user_size : Std.U64} {device : Bool} (h : AR a c₀) :
    objects.create_new_objects st arI s a t parent dest_cnode dest_offset dest_length base user_size device
      ⦃ r => AR r.2 c₀ ⦄ := by
  unfold objects.create_new_objects; mkd_walk

set_option maxHeartbeats 4000000 in
/-- **FL4's retype without a reset keeps `MR`** (module docstring). -/
theorem MKD.untyped_retype_nr {s : S} {a : A} {slot : obj.Slot} {base nt us dest off len : Std.U64} {dev : Bool}
    (h : AR a c₀) :
    untyped.retype st arI s a slot false base nt us dest off len dev ⦃ r => AR r.2.2 c₀ ⦄ := by
  unfold untyped.retype
  simp only [Bool.false_eq_true, ↓reduceIte]
  mkd_walk

end

end Fl4Proofs.P3
