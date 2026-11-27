/-
P3 (line mmuAD, gen 33): **overwriting a message register of a written message** (spec side), toward `ReportJ3`.

FL4's `vcpu::report` writes its 30 MRs with `set_mr` and then overwrites some of them (the entry state over the
exit record when `VALID = 0`, MR2 masked when full, `finish_notification`'s MR3..6/25/26), while the spec's
`vmReportF` writes the final list once (`setMrs`). XTopJointFault's `MrJ` follows appends only (`mrState_snoc_lt`
/ `_ge`); these lemmas give the overwrite of a word already written, register case (`k < 4`):

* `v3_mrRegs_set_lt`: `mrRegs ctx (ms.set k v)` = `mrRegs ctx ms` updated at `mrIdx k` (`k < |ms|`, `k < 4`).
* `v3_drop_set_lt`, **`v3_mrState_set_lt`** / **`v3_mrStateN_set_lt`**: `setReg` of `mrIdx k` at the state after
  `set_mrs rcv buf ms` is the state after `set_mrs rcv buf (ms.set k v)`, with and without a buffer.

The buffer case (`4 ≤ k`, `storeMem` over `mrMem`) is not here (gen 33 handoff).

No named premise. No existing statement changed.
-/
import Fl4Proofs.P3.EpFault
import Fl4Proofs.P3.EpFaultNone
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
open Fl4Spec

theorem v3_mrRegs_set_lt (ctx : Register → Word) (ms : List Word) (v : Word) {k : Nat} (hk : k < ms.length)
    (h4 : k < 4) : mrRegs ctx (ms.set k v) = Function.update (mrRegs ctx ms) (mrIdx k) v := by
  funext reg
  rcases mr_cases reg with ⟨j, hj, rfl⟩ | hr
  · rw [mrRegs_mr _ _ hj]
    by_cases e : j = k
    · subst e
      rw [Function.update_self, List.length_set, if_pos hk]
      simp [List.getD_eq_getElem?_getD, hk]
    · have e' : k ≠ j := fun h => e h.symm
      rw [Function.update_of_ne (fun h' => e (by
          have := congrArg (theIndex msg_registers) h'; rwa [theIndex_mr _ hj, theIndex_mr _ h4] at this)),
        mrRegs_mr _ _ hj, List.length_set]
      by_cases hl : j < ms.length
      · rw [if_pos hl, if_pos hl]
        simp [List.getD_eq_getElem?_getD, List.getElem?_set, e']
      · rw [if_neg hl, if_neg hl]
  · rw [mrRegs_other _ _ hr, Function.update_of_ne (fun h' => hr (by rw [h']; exact mrIdx_mem _)),
      mrRegs_other _ _ hr]

theorem v3_drop_set_lt (ms : List Word) (v : Word) {k : Nat} (h4 : k < 4) : (ms.set k v).drop 4 = ms.drop 4 := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_drop, List.getElem?_drop, List.getElem?_set_ne (by omega)]

theorem v3_mrState_set_lt (σ : State Unit) (rcv : ObjRef) (x : Tcb) (p : ObjRef) (ms : List Word) (v : Word)
    {k : Nat} (hk : k < ms.length) (h4 : k < 4) :
    updK (mrState σ rcv x p ms) rcv
      (.tcb (setReg (withRegs x (mrRegs x.tcbArch.tcbContext.userRegs ms)) (mrIdx k) v)) =
    mrState σ rcv x p (ms.set k v) := by
  have hp : mrPairs (ms.set k v) = mrPairs ms := by unfold mrPairs; rw [v3_drop_set_lt _ _ h4]
  unfold mrState
  rw [hp, v3_mrRegs_set_lt _ _ _ hk h4, setReg_withRegs]
  simp only [updK, setUm, Function.update_idem]

theorem v3_mrStateN_set_lt (σ : State Unit) (rcv : ObjRef) (x : Tcb) (ms : List Word) (v : Word)
    {k : Nat} (hk : k < ms.length) (h4 : k < 4) :
    updK (mrStateN σ rcv x ms) rcv
      (.tcb (setReg (withRegs x (mrRegs x.tcbArch.tcbContext.userRegs ms)) (mrIdx k) v)) =
    mrStateN σ rcv x (ms.set k v) := by
  unfold mrStateN
  rw [v3_mrRegs_set_lt _ _ _ hk h4, setReg_withRegs]
  simp only [updK, Function.update_idem]

end

end

end Fl4Proofs.P3.Endp
