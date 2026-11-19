/-
P3 (DESIGN.md §9), IPC: **the notification finalisation record's IPC-buffer
frame** (`NFr.ipcFr`, split from BufFr so XTopJointFin, upstream of BufFr's
other records, can use it), and the `objfrk` tactic BufFr uses.
-/
import Fl4Proofs.P3.BufDefs
import Fl4Proofs.P3.IpcFinNtfnInv

open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif

noncomputable section

open Fl4Spec Classical

/-- `ObjFrK` of a TCB replaced by a functional update keeping the frame and
buffer fields, or of two non-TCB, non-data-page objects. -/
macro "objfrk" : tactic => `(tactic| first
  | exact IpcFrKeep.objFrK_tcb rfl rfl
  | exact IpcFrKeep.objFrK_other (fun _ e => by cases e) (fun _ e => by cases e) (fun _ e => by cases e))

variable {σ σ' : State Unit}

theorem NChg.objFrK {q : Bool} {r cur p : ObjRef} {o o' : KernelObject} (h : NChg q r cur p o o') :
    IpcFrKeep.ObjFrK o o' := by
  rcases h with ⟨_, _, _, _, rfl, rfl, -⟩ | ⟨_, _, _, _, rfl, rfl, -⟩ | ⟨_, _, rfl, rfl, -⟩ <;> objfrk

theorem NFr.ipcFr {q : Bool} {r : ObjRef} (F : NFr q r σ σ') : IpcFrKeep σ σ' :=
  IpcFrKeep.of_chg F.kh fun _ _ _ h => h.objFrK

end

end Fl4Proofs.P3.Sched
