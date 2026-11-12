import Fl4Proofs.P0.Auto
open Aeneas Aeneas.Std Result
namespace Fl4Proofs.P0
open fl4_core Fl4Proofs.P0.Consts
example {S : Type _} (machineStoreInst : machine.Store S) (s : S) (t : obj.Tcb) (f : error.Fault) (hS : StoreTotal machineStoreInst) :
    faults.set_fault machineStoreInst s t f ⦃ _ => True ⦄ := by
  unfold faults.set_fault
  repeat (first | step | split)
end Fl4Proofs.P0
