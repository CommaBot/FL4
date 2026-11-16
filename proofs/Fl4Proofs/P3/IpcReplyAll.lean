/-
P3 (DESIGN.md §9), IPC: **`ReplyHyps` from the proved steps** (`replyHyps_of`).

`ReplyHyps.ofL` (IpcSchedLift) with every proof obligation discharged:
`remove` (IpcRemove's `remove_top`), the timeout transfer (IpcTmo's
`tmoXfer_top`), `PostponeOK` (`postponeOK_of`), the timeout handler's
endpoint (`epE_of`) and the endpoint tails (IpcEpTail's
`ipcEpTailHyps_top`). What is left is named l4v and platform facts:
`IpcSchedHyps`, `EpBufHyps` and `EpBufMapHyps` (the scheduler and buffer
steps), `SchedValid`, `QSorted`, `ActReady`, `RemoveOK`, `Inv`, "a runnable
thread with an SC about to be postponed is not released", `ObjCover`,
`TmoCapsValid`, `hmax`, `htu`.
-/
import Fl4Proofs.P3.IpcRemove
import Fl4Proofs.P3.IpcTmo
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- **`ReplyHyps` from the named l4v and platform facts** (module docstring). -/
theorem replyHyps_of (hH : IpcSchedHyps st ar N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hBf : EpBufHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hBm : EpBufMapHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hP0 : IPlaced N T E R B)
    (hAct : ∀ s σ, IpcRel N T E R B (L.mem s) σ → SRT st th cr N T C E R B c (SRE st N T C E R B c) s σ →
      ActReady σ)
    (hSV : ∀ s' σ', IRel st th cr N T C E R B c s' σ' → Sched.SchedValid σ')
    (hsort : ∀ s' σ', IRel st th cr N T C E R B c s' σ' → QSorted st T E s')
    (hD : ∀ s σ (r t : U64), IRel st th cr N T C E R B c s σ → r ∈ R → t ∈ T → RemoveOK st N T C R c s σ r t)
    (hInv : ∀ s σ, IRel st th cr N T C E R B c s σ → Inv σ)
    (hJ : ∀ s σ, IRel st th cr N T C E R B c s σ → BlockedScActive σ)
    (hnr : ∀ s σ (t : U64) (x : Fl4Spec.Tcb), IRel st th cr N T C E R B c s σ → t ∈ T →
      σ.kheap t.bv = some (.tcb x) → Fl4Spec.runnable x.tcbState = true → x.tcbSchedContext ≠ none →
      t.bv ∉ σ.releaseQueue)
    (hO : ∀ s σ, IRel st th cr N T C E R B c s σ → Sched.ObjCover N T E R C σ)
    (hV : ∀ s σ, IRel st th cr N T C E R B c s σ → TmoCapsValid σ)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ (a : A) v, ar.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    ReplyHyps st ar th cr N T C E R B c :=
  ReplyHyps.ofL hH hBf hBm (ipcEpTailHyps_top hP0 hAct) hP0 hSV hsort (remove_top hP0 hD hJ)
    (fun s σ t sc x y n hX ht _ hk hrun hsc hky =>
      postponeOK_of (hInv s σ hX) hk hsc hky (hnr s σ t x hX ht hk hrun (by rw [hsc]; exact Option.some_ne_none _)))
    (tmoXfer_top hH hBf hBm hP0 hmax htu)
    (fun s σ t x p bd r hX _ hk hh => epE_of (hO s σ hX) (hV s σ hX) hk hh) hInv

end

end

end Fl4Proofs.P3.Ipc
