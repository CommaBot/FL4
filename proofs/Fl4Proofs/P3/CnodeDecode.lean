/-
P3 (DESIGN.md §9), CSpace: **the whole of `cnode::decode`** against l4v's
`decode_cnode_invocation`, then `set_thread_state Restart` and
`invoke_cnode`, for every label (`cnode_decode_refines`). The labels outside
`CNodeRevoke ..= CNodeRotate` are the spec's `IllegalOperation`; each of
the others is its own theorem (copy, mint, move and mutate:
`cnode_copy_refines`; revoke and delete: `cnode_revoke_refines`,
`cnode_delete_refines`; `cnode_cancel_refines`; `cnode_rotate_refines`).
The result is `PInvPost`: the CSpace relation, `MdbInv` and `FinInv` after
the spec's outcome (done, or preempted in a revoke or delete), or the spec's
error with the state unchanged. The single-outcome `InvPost` is one
(`InvPost.toP`).
-/
import Fl4Proofs.P3.CnodeRevoke
import Fl4Proofs.P3.CnodeCancel
import Fl4Proofs.P3.CnodeRotate
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

theorem decode_illegal (label : Fl4Spec.Data) (args : List Fl4Spec.Data) (cap : Fl4Spec.Cap)
    (excaps : List Fl4Spec.Cap) (σ : Fl4Spec.State Unit)
    (h1 : Fl4Spec.genInvocationType label ∉
      Fl4Spec.GenInvocationLabels.uptoEnum .cnodeRevoke .cnodeRotate) :
    (Fl4Spec.decodeCnodeInvocation (Z := Unit) label args cap excaps).run σ =
      ({(.error .illegalOperation, σ)}, False) := by
  rw [cnodeDecode_eq]
  simp only [Fl4Spec.NonDetE.unlessE, h1, ↓reduceIte, Fl4Spec.NonDetE.throwError, ndE_throw_bind]
  rfl

theorem ExtraRel2.one {th : TypedHeap} {mem : U64 → U64} {x0 x1 : U64} {excaps : List Fl4Spec.Cap}
    (h : ExtraRel2 th mem x0 x1 excaps) : ExtraRel th mem x0 excaps := by
  rcases h with h | ⟨hx, c, a, hc, hca, hcv, ⟨-, rfl⟩ | ⟨-, c', a', rest, -, -, -, rfl⟩⟩
  · exact Or.inl h
  · exact Or.inr ⟨hx, c, a, [], hc, hca, hcv, rfl⟩
  · exact Or.inr ⟨hx, c, a, a' :: rest, hc, hca, hcv, rfl⟩

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- A single spec outcome is one of its outcomes. -/
theorem InvPost.toP {th : TypedHeap} {σ : Fl4Spec.State Unit} {G : MdbGhost}
    {m : Fl4Spec.SEMonad Unit Fl4Spec.CnodeInvocation} {s : S} {res : core.result.Result Unit error.Exc × S}
    (h : InvPost (L := L) th σ G m s res) : PInvPost (L := L) th σ G m s res := by
  obtain ⟨r, s'⟩ := res
  cases r with
  | Err e =>
    obtain ⟨h1, e', h2, h3⟩ := h
    exact Or.inl ⟨e, rfl, h1, e', h2, h3⟩
  | Ok u =>
    obtain ⟨inv, h2, σ1, hst, σ', G', hrun, hR, hV, hM, hC, hI, hF, hSt⟩ := h
    exact Or.inr ⟨inv, h2, σ1, hst, σ', G', Or.inl ⟨rfl, by rw [hrun]; rfl⟩, ⟨hR, hV, hM, hC, hI⟩, hF, hSt⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **FL4's `cnode::decode` refines l4v's CNode invocations, every label**:
decode, `set_thread_state Restart` and `invoke_cnode` against FL4's
`cnode::decode`, with the CSpace relation, `MdbInv` and `FinInv` after it.
The hypotheses are those of the labels' theorems: the extra caps
(`ExtraRel2`, two of them for Rotate, the first for the copies), the
endpoint side of CancelBadgedSends (`CancelEpHyp`), and the deletes and
preemption points of Revoke and Delete (`DelHyp`, `RPPHyp`, with `E` after
the restart giving `FinInv`, and a measure `μ` below `u64::MAX`). -/
theorem cnode_decode_refines (th : TypedHeap) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = cnodeLabelOf lbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (cap : capability.Cap) (a : Fl4Spec.Cap) (hca : CapRel cap a) (hcv : CapValid th cap)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (hx1 : Aeneas.Std.Array.index_usize extra 1#usize = ok x1)
    (excaps : List Fl4Spec.Cap) (hex : ExtraRel2 th (L.mem s) x0 x1 excaps)
    (hI : MdbInv (L.mem s) G) (hFI : FinInv th (L.mem s) σ G)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hEp : CancelEpHyp (L := L) th s σ)
    (E : S → Fl4Spec.State Unit → Prop) (μ : (U64 → U64) → MdbGhost → Nat)
    (hμ : ∀ m m' G, MdbLinks th m G → SlotsSame th m m' → μ m' G = μ m G)
    (hD : DelHyp (L := L) arI μ th E) (hPP : RPPHyp (L := L) arI th E)
    (hE : ∀ s1 σ1, SlotsSame th (L.mem s) (L.mem s1) →
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) → E s1 σ1)
    (hEF : ∀ s1 σ1 G1, CRel th (L.mem s1) σ1 G1 → E s1 σ1 → FinInv th (L.mem s1) σ1 G1)
    (hfew : μ (L.mem s) G < 2 ^ 64 - 1) :
    cnode.decode st arI s ar lbl length cap buf extra ⦃ res =>
      PInvPost (L := L) th σ G (Fl4Spec.decodeCnodeInvocation slbl (args.map UScalar.bv) a excaps) s
        (res.1, res.2.1) ⦄ := by
  by_cases hlo : lbl.val < 25 ∨ 32 < lbl.val
  · -- outside the CNode labels
    have hg : Fl4Spec.genInvocationType slbl = .invalidInvocation := by
      rw [hlbl]; unfold cnodeLabelOf
      simp only [show lbl.val ≠ 25 by omega, show lbl.val ≠ 26 by omega, show lbl.val ≠ 27 by omega,
        show lbl.val ≠ 28 by omega, show lbl.val ≠ 29 by omega, show lbl.val ≠ 30 by omega,
        show lbl.val ≠ 31 by omega, show lbl.val ≠ 32 by omega, ↓reduceIte]
    have hdec := decode_illegal slbl (args.map UScalar.bv) a excaps σ (by rw [hg]; decide)
    unfold cnode.decode
    rcases hlo with h | h
    · have n1 : lbl < fl4_abi.label.CNodeRevoke := by have := lbl_revoke_val; scalar_tac
      rw [if_pos n1]
      simp only [error.illegal, bind_ok]
      rw [WP.spec_ok]
      exact Or.inl ⟨_, rfl, rfl, .illegalOperation, hdec, trivial⟩
    · have n1 : ¬ lbl < fl4_abi.label.CNodeRevoke := by have := lbl_revoke_val; scalar_tac
      have n2 : lbl > fl4_abi.label.CNodeRotate := by have := lbl_rotate_val; scalar_tac
      rw [if_neg n1, if_pos n2]
      simp only [error.illegal, bind_ok]
      rw [WP.spec_ok]
      exact Or.inl ⟨_, rfl, rfl, .illegalOperation, hdec, trivial⟩
  have hl : 25 ≤ lbl.val ∧ lbl.val ≤ 32 := by omega
  by_cases hcp : 28 ≤ lbl.val ∧ lbl.val ≤ 31
  · exact WP.spec_mono (cnode_copy_refines arI th s ar σ G hR hV hP hM hC lbl slbl hlbl hcp length buf ct hct args
      hlen hargs cap a hca hcv extra x0 hx0 excaps hex.one hI hFI hact hcur htcb) (fun res h => h.toP)
  have hcase : lbl.val = 25 ∨ lbl.val = 26 ∨ lbl.val = 27 ∨ lbl.val = 32 := by omega
  rcases hcase with h | h | h | h
  · have e : lbl = fl4_abi.label.CNodeRevoke := UScalar.eq_of_val_eq (by rw [h, lbl_revoke_val])
    subst e
    exact cnode_revoke_refines arI th s ar σ G hR hV hP hM hC slbl (by rw [hlbl]; simp [cnodeLabelOf])
      length buf ct hct args hlen hargs cap a hca hcv extra excaps hI hact hcur htcb E μ hμ hD hPP hE hEF hfew
  · have e : lbl = fl4_abi.label.CNodeDelete := UScalar.eq_of_val_eq (by rw [h, lbl_delete_val])
    subst e
    exact cnode_delete_refines arI th s ar σ G hR hV hP hM hC slbl (by rw [hlbl]; simp [cnodeLabelOf])
      length buf ct hct args hlen hargs cap a hca hcv extra excaps hI hact hcur htcb E μ hD hE hEF
  · have e : lbl = fl4_abi.label.CNodeCancelBadgedSends := UScalar.eq_of_val_eq (by rw [h]; simp [fl4_abi.label.CNodeCancelBadgedSends])
    subst e
    exact WP.spec_mono (cnode_cancel_refines arI th s ar σ G hR hV hP hM hC slbl (by rw [hlbl]; simp [cnodeLabelOf])
      length buf ct hct args hlen hargs cap a hca hcv extra excaps hI hFI hact hcur htcb hEp) (fun res h => h.toP)
  · have e : lbl = fl4_abi.label.CNodeRotate := UScalar.eq_of_val_eq (by rw [h, lbl_rotate_val])
    subst e
    exact WP.spec_mono (cnode_rotate_refines arI th s ar σ G hR hV hP hM hC slbl (by rw [hlbl]; simp [cnodeLabelOf])
      length buf ct hct args hlen hargs cap a hca hcv extra x0 x1 hx0 hx1 excaps hex hI hFI hact hcur htcb)
      (fun res h => h.toP)

end

end

end Fl4Proofs.P3
