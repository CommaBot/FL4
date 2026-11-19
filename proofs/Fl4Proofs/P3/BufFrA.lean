/-
P3 (DESIGN.md §9), IPC: **`IpcFrKeep` across the arch frame `ArFr`**
(handoff/glob.md "gl8"): an arch object replaced by one of the same
`aaType` keeps a non-device data page (`aUserData vms` names it), and the
TCBs are kept.
-/
import Fl4Proofs.P3.BufDefs
import Fl4Proofs.P3.XTopJointFinVsSpec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section Spec
open Fl4Spec

variable {σ σ' : State Unit}

theorem ArFr.ipcFr (h : ArFr σ σ') : IpcFrKeep σ σ' := by
  refine ⟨fun t x' hx' => Or.inr ?_, fun p vms hp => ?_, fun p vms hp => ?_⟩
  · rcases h.kh t with e | ⟨a, a', -, h2, -⟩
    · exact ⟨x', by rw [← e]; exact hx', rfl, rfl⟩
    · rw [hx'] at h2; cases h2
  · rcases h.kh p with e | ⟨a, a', h1, h2, ht⟩
    · rw [e]; exact hp
    · rw [hp] at h1; cases h1
      rw [h2, aaType_userData.1 ht]
  · rcases h.kh p with e | ⟨a, a', h1, h2, ht⟩
    · rw [← e]; exact hp
    · rw [hp] at h2; cases h2
      rw [h1, (aaType_userData.1 ht.symm)]

end Spec

end

end Fl4Proofs.P3
