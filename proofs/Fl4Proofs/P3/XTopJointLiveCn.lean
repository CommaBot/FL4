/-
P3 (DESIGN.md §9), CSpace (KENTRY-PLAN g2g (a')): **every CNode label ends in
`LiveDN`**: XTopJointMRCnode's `decode_invocation_cnodeJ_stepsLM` with the
posts `JAtL` / `JAtPreMVL` (XTopJointWJPL), from `LiveDN` and `SpecGlob` at
the decode's state, with no new premise.

* `JAtZ.zNoBlk`: `ZNoBlk` (XTopJointLiveStep) from `SpecGlob` at a `JAtZ`
  state: a zombie's object is a TCB (off the kernel-state block, `JKern.hks`)
  or a CNode; a CNode inside the block has its slot 0 in the IRQ node
  (`IpcApart.ks`), so it is one of the IRQ node's CNodes (`Placed.disj`),
  which no cap but a frame cap names (`SpecGlob.ref`, `IrqRel.node`).
* `JAtZLB` (`JAtZ ∧ LiveDN ∧ ZNoBlk`): the copy, mint, move, mutate and
  rotate labels by `decode_invocation_cnode_copyXS` at it (`Steps.jatL`).
* `JAtZ.cancelBadgedJL`, `cn_cancel_topJL`, `decode_invocation_cnode_cancelJL`:
  CancelBadgedSends (XTopJointCbs's `…J` at `JAtL`: the restart by
  `stepClosed_jatL`, the cancel by `LiveDN.of_jstep` with the debug words from
  P1's footprint, the original bits by `orig_eq_of_slots`, the idle thread
  from the spec's `inv_cancelBadgedSends`).
* `decode_invocation_cnode_illegalXG`: the invalid labels at any post holding
  at the decode's state.
* `decode_invocation_cnodeJ_stepsLML`: all labels; Revoke / Delete by
  g2f's `decode_invocation_cnode_{revoke,delete}JLML`.
-/
import Fl4Proofs.P3.XTopJointWJPL
import Fl4Proofs.P3.XTopJointLiveStep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets} {H : P1.Heap}
  {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}

/-- **The CNode cap's invalid labels at any post holding at the decode's
state** (XTopJointCbs's `decode_invocation_cnode_illegalJ`). -/
theorem decode_invocation_cnode_illegalXG {X : S → A → Fl4Spec.State Unit → Prop} (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (hX0 : X s ar σ)
    (lbl : U64) (hlo : lbl.val < 25 ∨ 32 < lbl.val) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = cnodeLabelOf lbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List Fl4Spec.Data)
    (p r gs g : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI X s ar σ lbl length slot (.CNode p r gs g) blk call don fp buf extra slbl
      args ci sl excaps buffer ct := by
  have hg : Fl4Spec.genInvocationType slbl = .invalidInvocation := by
    rw [hlbl]; unfold cnodeLabelOf
    simp only [show lbl.val ≠ 25 by omega, show lbl.val ≠ 26 by omega, show lbl.val ≠ 27 by omega,
      show lbl.val ≠ 28 by omega, show lbl.val ≠ 29 by omega, show lbl.val ≠ 30 by omega,
      show lbl.val ≠ 31 by omega, show lbl.val ≠ 32 by omega, ↓reduceIte]
  have hdec := decode_illegal slbl args (absCap (.CNode p r gs g)) (excaps.map Prod.fst) σ (by rw [hg]; decide)
  left
  unfold DecOKDMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    unfold cnode.decode
    rcases hlo with h | h
    · have n1 : lbl < fl4_abi.label.CNodeRevoke := by have := lbl_revoke_val; scalar_tac
      rw [if_pos n1]
      simp only [error.illegal, bind_ok]
      rw [WP.spec_ok]
      exact Or.inl ⟨_, rfl, rfl, ⟨.illegalOperation, run_liftME_err hdec, Or.inl trivial⟩, hX0⟩
    · have n1 : ¬ lbl < fl4_abi.label.CNodeRevoke := by have := lbl_revoke_val; scalar_tac
      have n2 : lbl > fl4_abi.label.CNodeRotate := by have := lbl_rotate_val; scalar_tac
      rw [if_neg n1, if_pos n2]
      simp only [error.illegal, bind_ok]
      rw [WP.spec_ok]
      exact Or.inl ⟨_, rfl, rfl, ⟨.illegalOperation, run_liftME_err hdec, Or.inl trivial⟩, hX0⟩
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, hX0⟩

end

end

end Fl4Proofs.P3
