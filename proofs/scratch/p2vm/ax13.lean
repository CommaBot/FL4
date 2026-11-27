import Fl4Proofs.P2.AccessVmAcc
open Aeneas Aeneas.Std Result
open Fl4Proofs.P2.PathObl in
#print axioms syscall.handle_vm_fault_local.guard_acc
open Fl4Proofs.P2.PathObl in
#print axioms vm_acc_of_tail
open Fl4Proofs.P2.PathObl in
#print axioms VmMidF.preRW
open Fl4Proofs.P2.PathObl in
#print axioms VmMidF.chk
open Fl4Proofs.P2.PathObl in
#print axioms vm_queue
open Fl4Proofs.P2.PathObl in
#print axioms fastFaultG_checks
open Fl4Proofs.P2.PathObl in
#print axioms faultTailG_split
open Fl4Proofs.P2.PathObl in
#print axioms vmPre14.guard
open Fl4Proofs.P2.PathObl in
#print axioms faultTail3.guard

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts

section
variable {S : Type}
-- PROBE fcA
example {A : Type} (m : machine.Store S) (ar : machine.Arch A) {s : S} {a : A}
    {t : obj.Tcb} {f : error.Fault} {ty ptr badge dest r : U64} (C : FaultChecks m s t ptr badge dest r) :
    fastFaultG m ar s a t f ty = faultTailG m ar s a t f ty ptr badge dest r := by
  obtain ⟨hact, ⟨sl, x, y, g, gr, hsl, hcap, hg⟩, hep, hhd, hrp, hr0, hhere, ⟨d, p, hd, hp, hhi⟩⟩ := C
  unfold fastFaultG
  rw [hact]; simp only [bind_ok, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rw [hsl]; simp only [bind_ok]
  rw [hcap]; simp only [bind_ok]
  cases g <;> cases gr <;> simp only [Bool.false_eq_true, or_self] at hg
  all_goals
    simp only [Bool.false_eq_true, eq_self_iff_true, ↓reduceIte]
    rw [hep]; simp only [bind_ok, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    rw [hhd]; simp only [bind_ok]
    rw [hrp]; simp only [bind_ok, if_neg hr0]
    rw [hhere]; simp only [bind_ok, eq_self_iff_true, ↓reduceIte]
    rw [hd]; simp only [bind_ok]
    rw [hp]; simp only [bind_ok]
    simp only [hhi, bind_ok, ↓reduceIte]
    rfl
-- PROBE sp1
example {A : Type} (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A) (t : obj.Tcb)
    (f : error.Fault) (ty ptr badge i2 i3 : U64) :
    faultTailG m ar s a t f ty ptr badge i2 i3 =
      (do let s14 ← vmPre14 m ar s a t f ty ptr badge i2 i3; faultTail3 m ar s14 a i2) := by
  unfold faultTailG vmPre14 faultTail3
  simp only [Std.bind_assoc]
  iterate 7 (congr 1; funext _)
  rename_i x
  obtain ⟨sent, s6⟩ := x
  rfl
-- PROBE sp2
example {A : Type} (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A) (t : obj.Tcb)
    (f : error.Fault) (ty ptr badge i2 i3 : U64) :
    faultTailG m ar s a t f ty ptr badge i2 i3 =
      (do let s14 ← vmPre14 m ar s a t f ty ptr badge i2 i3; faultTail3 m ar s14 a i2) := by
  unfold faultTailG vmPre14 faultTail3
  simp only [Std.bind_assoc]
  iterate 7 (congr 1; funext _)
  rename_i x
  obtain ⟨sent, s6⟩ := x
  simp only [uncurry_apply_pair, Std.bind_assoc]
-- PROBE sp3
example {A : Type} (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A) (t : obj.Tcb)
    (f : error.Fault) (ty ptr badge i2 i3 : U64) :
    faultTailG m ar s a t f ty ptr badge i2 i3 =
      (do let s14 ← vmPre14 m ar s a t f ty ptr badge i2 i3; faultTail3 m ar s14 a i2) := by
  unfold faultTailG vmPre14 faultTail3
  simp only [Std.bind_assoc]
  iterate 7 (congr 1; funext _)
  rename_i x
  obtain ⟨sent, s6⟩ := x
  dsimp only
  simp only [Std.bind_assoc]
end

section
variable {S : Type} {st : machine.Store S} {R W : U64 → Prop} [L : LawfulStore st]
-- PROBE sf1
example (s : S) (t : obj.Tcb) (w0 w1 : U64) (ins : Bool) (h : FaultWr W t) :
    faults.set_fault (guard st R W) s t (error.Fault.VmFault w0 w1 ins) =
      faults.set_fault st s t (error.Fault.VmFault w0 w1 ins) := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  unfold faults.set_fault
  cases ins <;> simp only [Bool.false_eq_true, ↓reduceIte, bind_ok]
  all_goals
    simp only [uncurry_apply_pair]
    rw [obj.Tcb.set_fault_type.guard t s _ h0]
    refine bind_guard_congr rfl (fun s2 _ => ?_)
    rw [obj.Tcb.set_fault_w0.guard t s2 _ h1]
    refine bind_guard_congr rfl (fun s3 _ => ?_)
    rw [obj.Tcb.set_fault_w1.guard t s3 _ h2]
    refine bind_guard_congr rfl (fun s4 _ => ?_)
    rw [obj.Tcb.set_fault_w2.guard t s4 _ h3]
-- PROBE sf2
example (s : S) (t : obj.Tcb) (w0 w1 : U64) (ins : Bool) (h : FaultWr W t) :
    faults.set_fault (guard st R W) s t (error.Fault.VmFault w0 w1 ins) =
      faults.set_fault st s t (error.Fault.VmFault w0 w1 ins) := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  unfold faults.set_fault
  cases ins <;> simp only [Bool.false_eq_true, ↓reduceIte, bind_ok]
  all_goals
    dsimp only
    rw [obj.Tcb.set_fault_type.guard t s _ h0]
    refine bind_guard_congr rfl (fun s2 _ => ?_)
    rw [obj.Tcb.set_fault_w0.guard t s2 _ h1]
    refine bind_guard_congr rfl (fun s3 _ => ?_)
    rw [obj.Tcb.set_fault_w1.guard t s3 _ h2]
    refine bind_guard_congr rfl (fun s4 _ => ?_)
    rw [obj.Tcb.set_fault_w2.guard t s4 _ h3]
end

end Fl4Proofs.P2.PathObl
