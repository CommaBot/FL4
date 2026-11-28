/-
P3 (DESIGN.md §9), scheduler: **`schedule` refines l4v's up to the FPU**
(KENTRY-PLAN.md sch4 (A)): ScScheduleTop's chain (`schedule_choose_new_thread_refinesF`,
`sw_refinesF`, `cn_refinesF`, `switch_branch_refinesF`, `schedule_refinesWPF`)
with the arch hypothesis `ArchSwF` [P] (ScArchF) in place of `ArchSwF`,
whose `ArchKeeps` heap equality is false whenever the spec has an FPU
owner. Every post's `HeapEqUpToFpu σ σ'` becomes `HeapEqUpToFpu σ σ'`; the
switching lemmas take `FpuOwnOK` at the switch state (`ArchSwF`'s [J]
side condition), carried from the state after the TCB timers
(`schedule_refinesWPF`'s `hPo`: the fire predicate implies it) across
`awaken` (`ow_awaken`, `Calm`'s heap equality) and the queue operations
(`ow_tcbSchedAction`, `QChange`). `schedule_refinesWPF` supersedes
`schedule_refinesWPF` (same post).
-/
import Fl4Proofs.P3.ScArchF
import Fl4Proofs.P3.G7cCr3K
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

/-- An outcome of a `CRK` spec function keeps the ASID table (g7d: frames
`VsRootOK` to the switch states). -/
theorem asid_of_crk {α : Type} {m : Fl4Spec.NonDet (Fl4Spec.State Unit) α} (h : Vs.CRK m)
    {σ σ' : Fl4Spec.State Unit} {a : α} {X : Prop} (he : m σ = ({(a, σ')}, X)) :
    σ'.archState.x64AsidTable = σ.archState.x64AsidTable := by
  have e := h σ (a, σ') (by rw [he]; exact Set.mem_singleton _)
  exact congrArg (fun q => q.2.1) e

end

end Fl4Proofs.P3.Sched
