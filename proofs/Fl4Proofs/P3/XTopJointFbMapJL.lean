/-
P3 (issue #16, FL4 #71), VSpace FrameBatch: **`batch_map` at `J` with the
deletion's liveness facts** (KENTRY-PLAN fb3l): XTopJointFbMapJ's
`JAtZ.batchMapJ`, and on its `Ok` path `LiveDN` at the same sets (the slot's cap
replaced by a frame cap of the same frame, the page tables written), `NoSwitch`,
`SpecGlob` and `PPR0` kept (the batch's loop invariant `FbMidJ` carries them for
the DELETE entries' frame deletes). OPEN (scratch stub).
-/
import Fl4Proofs.P3.XTopJointFbMapJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 8000000 in
/-- **`JAtZ.batchMapJ` with the liveness facts** (module docstring). OPEN. -/
theorem JAtZ.batchMapJL [Fl4Proofs.P1.PlainStore st] (hA : ArchRefines arI AR) {s : S} {a : A}
    {τ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a τ)
    (hLv : LiveDN (L := L) Z.th H Cs Z.G s τ) (hns : Vs.NoSwitch τ) (hsg : SpecGlob τ) (hp0 : PPR0 τ)
    {pc : U64} {r : Nat} (hpc : Z.th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {p1 as1 : U64} (has1 : as1 ≠ 0#u64) (has2 : as1.val < 2 ^ 20)
    (hf : ExceptT.run (Fl4Spec.findVspaceForAsid (Z := Unit) as1.bv) τ = ({(.ok p1.bv, τ)}, False))
    (op depth a1 cr a2 : U64) (dd : Bool) (cn dcn : capability.Cap) (a0 : U64)
    (b : Fl4Spec.Fl4FrameBatchInvocation) (hbv : b.vspace = p1.bv) (hba : b.asid = as1.bv)
    (hbm : b.mapRights = a1.bv) (hbat : b.attr = a2.bv) :
    vspace.batch_map st arI s a (cslotAddr (pc.bv, idx)) ⟨p1, as1, op, depth, a1, cr, a2, dd, cn, dcn⟩ a0 ⦃ res =>
      (∃ e e', res.1 = .Err e ∧ MapErrRel e e' ∧
        ExceptT.run (Fl4Spec.fbMap (Z := Unit) b (pc.bv, idx) a0.bv) τ = ({(.error e', τ)}, False) ∧
        res.2.1 = s ∧ res.2.2 = a) ∨
      (res.1 = .Ok () ∧ ∃ τ1, ((.ok (), τ1) : Except Fl4Spec.SyscallError Unit × Fl4Spec.State Unit) ∈
          (ExceptT.run (Fl4Spec.fbMap (Z := Unit) b (pc.bv, idx) a0.bv) τ).1 ∧
        JAtZ (L := L) arI AR Z H Cs Ac Lst D res.2.1 res.2.2 τ1 ∧ FbKeep τ τ1 ∧ FbFootK (L := L) Z s res.2.1 ∧
        LiveDN (L := L) Z.th H Cs Z.G res.2.1 τ1 ∧ Vs.NoSwitch τ1 ∧ SpecGlob τ1 ∧ PPR0 τ1) ⦄ := by
  fail "FB3 OPEN: batch_map's liveness facts (KENTRY-PLAN fb3l)"

end

end

end Fl4Proofs.P3
