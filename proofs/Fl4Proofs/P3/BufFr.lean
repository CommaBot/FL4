/-
P3 (DESIGN.md §9), IPC: **the IPC-buffer frames of the spec's step records**
(handoff/glob.md "gl6"/"gl8"): each record (`KFr`, `NFr` (BufFrN), `EFr`, `DWFr`,
`CFr`, `PFr`) keeps what `JAtZ.bok`/`JAtZ.fcov` read (`IpcFrKeep`, by
`IpcFrKeep.of_chg`: each record's per-object change is `ObjFrK`). The
records say nothing of the spec's memory (and cannot: XTopJointXferB's
`CFr.um`/`DWFr.ofUm` compose them with arbitrary `setUm` writes).
-/
import Fl4Proofs.P3.BufDefs
import Fl4Proofs.P3.BufFrN
import Fl4Proofs.P3.IpcCancelFr
import Fl4Proofs.P3.IpcFinNtfnInv
import Fl4Proofs.P3.IpcFinEpInv
import Fl4Proofs.P3.IpcSignalDonFr
import Fl4Proofs.P3.IpcSignalBoundFr
import Fl4Proofs.P3.TcbPrioFr
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif

noncomputable section

open Fl4Spec Classical

variable {σ σ' : State Unit}

theorem KChg.objFrK {t p : ObjRef} {o o' : KernelObject} (h : KChg t p o o') : IpcFrKeep.ObjFrK o o' := by
  rcases h with ⟨_, _, _, rfl, rfl, -⟩ | ⟨_, _, rfl, rfl, -⟩ | ⟨_, _, rfl, rfl, -⟩ <;> objfrk

theorem EChg.objFrK {e : ObjRef} {P : ObjRef → Prop} {cur p : ObjRef} {o o' : KernelObject}
    (h : EChg e P cur p o o') : IpcFrKeep.ObjFrK o o' := by
  rcases h with ⟨_, _, rfl, rfl, -⟩ | ⟨_, _, _, rfl, rfl, -⟩ | ⟨_, _, rfl, rfl, -⟩ | ⟨_, _, rfl, rfl, -⟩ <;> objfrk

theorem DChg.objFrK {r t cur p : ObjRef} {o o' : KernelObject} (h : DChg r t cur p o o') :
    IpcFrKeep.ObjFrK o o' := by
  rcases h with ⟨_, _, _, _, _, _, rfl, rfl, -⟩ | ⟨_, _, _, _, _, rfl, rfl, -⟩ | ⟨_, _, rfl, rfl, -⟩ |
    ⟨_, _, rfl, rfl, -⟩ | ⟨_, rfl, rfl, -⟩ <;> objfrk

theorem CChg.objFrK {r t cur p : ObjRef} {o o' : KernelObject} (h : CChg r t cur p o o') :
    IpcFrKeep.ObjFrK o o' := by
  rcases h with ⟨_, _, _, _, _, rfl, rfl, -⟩ | ⟨hn, -⟩ | ⟨_, _, rfl, rfl, -⟩ | ⟨_, rfl, rfl, -⟩
  · objfrk
  · exact hn.objFrK
  all_goals objfrk

theorem PChg.objFrK {t p : ObjRef} {o o' : KernelObject} (h : PChg t p o o') : IpcFrKeep.ObjFrK o o' := by
  rcases h with ⟨_, _, rfl, rfl, -⟩ | ⟨_, _, rfl, rfl, -⟩ | ⟨_, _, rfl, rfl, -⟩ <;> objfrk

theorem KFr.ipcFr {t : ObjRef} (F : KFr t σ σ') : IpcFrKeep σ σ' :=
  IpcFrKeep.of_chg F.kh fun _ _ _ h => h.objFrK
theorem EFr.ipcFr {e : ObjRef} {P : ObjRef → Prop} (F : EFr e P σ σ') : IpcFrKeep σ σ' :=
  IpcFrKeep.of_chg F.kh fun _ _ _ h => h.objFrK
theorem DWFr.ipcFr {r t : ObjRef} (F : DWFr r t σ σ') : IpcFrKeep σ σ' :=
  IpcFrKeep.of_chg F.kh fun _ _ _ h => h.objFrK
theorem CFr.ipcFr {r t : ObjRef} (F : CFr r t σ σ') : IpcFrKeep σ σ' :=
  IpcFrKeep.of_chg F.kh fun _ _ _ h => h.objFrK
theorem PFr.ipcFr {t : ObjRef} (F : PFr t σ σ') : IpcFrKeep σ σ' :=
  IpcFrKeep.of_chg F.kh fun _ _ _ h => h.objFrK

end

end Fl4Proofs.P3.Sched
