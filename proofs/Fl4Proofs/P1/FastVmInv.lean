/-
# The VM fault fast path's reads from the entry state (FL4 #71, pf1)

m61–m73's derivation of the general fault path's reads, stated over the
fault (FastFaultInv `faultReads_ofG`, FastFinInv `faultOK_ofG`, FastTailFault
`faultNvm_tailG`; `set_fault` of a VM fault writes the same four words as an
UnknownSyscall fault, `sfG` / `set_fault_vm`, and its message is four
`set_mr`, `set_mrs_fault_rgV`), used here at a VM fault:

* `faultOK_ofV`, `faultNvm_ofRV`, `vmFault_of` (m73's `fastFault_of`):
  FastVm's `FaultOKG … VMFault` and `VmFaultNvm` at a state where
  `fastpath_vm.vm_fault` is entered, from `BXI` and the facts of
  `faultEntAt_ofT`.
-/
import Fl4Proofs.P1.FastVm
import Fl4Proofs.P1.FastFaultEntU
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {A : Type _} {st : machine.Store S} (ar : machine.Arch A) [L : LawfulStore st]

theorem faultOK_ofV {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s : S} {a : A}
    {t : obj.Tcb} {addr fsr : U64} {ins : Bool} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hF : FaultEntAt (L := L) T Cs Ω U Sg Rp s t) :
    FaultOKG (L := L) ar s a t (error.Fault.VmFault addr fsr ins) fl4_abi.consts.fault.VMFault :=
  faultOK_ofG ar (Or.inr rfl) (set_fault_vm (L := L) s t addr fsr ins) hI hF

theorem faultNvm_ofRV {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
    (hA : P0.ArchTotal ar)
    {s : S} {a : A} {t : obj.Tcb} {addr fsr : U64} {ins : Bool} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hrecv0 : ∀ {ptr badge dest r : U64}, FaultChecks st s t ptr badge dest r →
      L.mem s (stA dest) = sched.TS_BLOCKED_ON_RECV)
    (hF : FaultEntAt (L := L) T Cs Ω U Sg Rp s t) :
    VmFaultNvm (L := L) ar s a t (error.Fault.VmFault addr fsr ins) := by
  intro sF aF h
  obtain ⟨ptr, badge, dest, r, hc, hfast⟩ := vm_fault_acc st ar h
  exact faultNvm_tailG ar hA hI hrecv0 hF (Or.inr rfl) (set_fault_vm (L := L) s t addr fsr ins) hc hfast

/-- **m73's `fastFault_of` for a VM fault**: `FaultOKG … VMFault` and
`VmFaultNvm` at one state where `fastpath_vm.vm_fault` is entered, from
`BXI` and the facts of `faultEntAt_ofT`. -/
theorem vmFault_of {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
    (hA : P0.ArchTotal ar) {s : S} {a : A} {t : obj.Tcb} {addr fsr : U64} {ins : Bool}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (et : sched.cur_thread st s = ok t)
    (hnb : ¬ Blocked (L.mem s (stA (L.curW s))))
    (hcap : obj.Tcb.slot (L.curW s) layout.tcb.SLOT_FAULT_HANDLER ⦃ sl =>
      obj.Slot.cap st sl s ⦃ c => CapTyped H Rp Nt c ⦄ ⦄)
    (hU : ∀ b ∈ U, OutsideObjs st T Cs s b ∧ b ∉ Ω)
    (hbuf : ∀ y ∈ T, msg.lookup_ipc_buffer st s true y ⦃ b => BufOK U b ⦄)
    (hAs : AsidOff (L := L) Ω Sg s) :
    FaultOKG (L := L) ar s a t (error.Fault.VmFault addr fsr ins) fl4_abi.consts.fault.VMFault ∧
      VmFaultNvm (L := L) ar s a t (error.Fault.VmFault addr fsr ins) := by
  have hF := faultEntAt_ofT hI et hnb hcap hU hbuf hAs
  exact ⟨faultOK_ofV ar hI hF, faultNvm_ofRV ar hA hI (fun hc => faultRecv_ofT hI et hcap hc) hF⟩

end

end Fl4Proofs.P1
