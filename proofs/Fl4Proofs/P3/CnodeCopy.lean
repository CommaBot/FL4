/-
P3 (DESIGN.md §9), CSpace: **the CNode Copy, Mint, Move and Mutate
invocations** (FL4 `cnode::decode` with `decode_copy`, `copied_cap`)
against l4v `decode_cnode_invocation` followed by `set_thread_state
Restart` and `invoke_cnode` (as `handle_invocation` runs them).

Hypotheses beyond the CSpace relation, all explicit:
* labels: FL4's label word `lbl` (28..31, FL4 ABI numbering, which has the
  debug and FL4 TCB labels before the CNode ones) has the spec label
  `slbl` with `gen_invocation_type slbl = cnodeLabelOf lbl`;
* message: `cur_thread` is `ct`, and `syscall_arg i` is the `i`-th element
  of the argument list `args` (`length` its length), as `handle_invocation`
  provides (`getMRs`, with the length clipped when there is no buffer);
* extra caps: `extra[0]` is null and there are none, or is the slot of the
  first extra cap (`ExtraRel`);
* `MdbInv` (MdbInv.lean), the MDB invariant, which gives `ParentAdj` and
  so `NoChildrenRel` at the source slot (for deriving untyped caps), and the
  sibling condition of `insert_refines`; it holds again afterwards;
* `OutsideObjects` for the current core's scheduler-action word
  (StateFrame.lean), which gives `SlotsSame` across `set_thread_state`.
-/
import Fl4Proofs.P3.CnodeSpec
import Fl4Proofs.P3.MoveRefine
import Fl4Proofs.P3.StateFrame
import Fl4Proofs.P3.NoChildren
import Fl4Proofs.P3.CnodeShape
import Fl4Proofs.P3.CnodeKey
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-- FL4's CNode labels (FL4 ABI numbering) as the spec's. -/
def cnodeLabelOf (lbl : U64) : Fl4Spec.GenInvocationLabels :=
  if lbl.val = 25 then .cnodeRevoke else if lbl.val = 26 then .cnodeDelete
  else if lbl.val = 27 then .cnodeCancelBadgedSends else if lbl.val = 28 then .cnodeCopy
  else if lbl.val = 29 then .cnodeMint else if lbl.val = 30 then .cnodeMove
  else if lbl.val = 31 then .cnodeMutate else if lbl.val = 32 then .cnodeRotate
  else .invalidInvocation

theorem SameBadgeKind.refl (c : capability.Cap) : SameBadgeKind c c := by
  cases c <;> simp [SameBadgeKind]

theorem u64_eq_iff (x y : U64) : x = y ↔ x.val = y.val := ⟨congrArg _, UScalar.eq_of_val_eq⟩

@[simp] theorem lbl_revoke_val : fl4_abi.label.CNodeRevoke.val = 25 := by simp [fl4_abi.label.CNodeRevoke]
@[simp] theorem lbl_delete_val : fl4_abi.label.CNodeDelete.val = 26 := by simp [fl4_abi.label.CNodeDelete]
@[simp] theorem lbl_cancel_val : fl4_abi.label.CNodeCancelBadgedSends.val = 27 := by
  simp [fl4_abi.label.CNodeCancelBadgedSends]
@[simp] theorem lbl_copy_val : fl4_abi.label.CNodeCopy.val = 28 := by simp [fl4_abi.label.CNodeCopy]
@[simp] theorem lbl_mint_val : fl4_abi.label.CNodeMint.val = 29 := by simp [fl4_abi.label.CNodeMint]
@[simp] theorem lbl_move_val : fl4_abi.label.CNodeMove.val = 30 := by simp [fl4_abi.label.CNodeMove]
@[simp] theorem lbl_mutate_val : fl4_abi.label.CNodeMutate.val = 31 := by simp [fl4_abi.label.CNodeMutate]
@[simp] theorem lbl_rotate_val : fl4_abi.label.CNodeRotate.val = 32 := by simp [fl4_abi.label.CNodeRotate]

/-- FL4's `copied_cap` outcome against the spec's `copyRest`. -/
def CopiedRel (th : TypedHeap) (srcC : capability.Cap) (sl dsl : Fl4Spec.CslotPtr) :
    core.result.Result (capability.Cap × Bool) error.Exc → Except Fl4Spec.SyscallError Fl4Spec.CnodeInvocation →
    Prop
  | .Err e, .error e' => SysErrRel e e'
  | .Ok (nc, mv), R => R = finishRes mv sl dsl (.ok (absCap nc)) ∧ CapWf nc ∧ EncWf nc ∧
      CapValid th nc ∧ SameBadgeKind nc srcC
  | _, _ => False

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`copied_cap` refines the per-label part of `decode_cnode_invocation`**
(`copyRest`): the same error, or the new cap and whether to move. -/
theorem copied_rel (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (lbl : U64) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = cnodeLabelOf lbl) (hl : 28 ≤ lbl.val ∧ lbl.val ≤ 31)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (rest : List U64)
    (hlen : length.val = rest.length + 4)
    (hargs : ∀ (i : U64) x, rest[i.val - 4]? = some x → 4 ≤ i.val → msg.syscall_arg st s ct buf i = ok x)
    (sl dsl : Fl4Spec.CslotPtr) (srcC : capability.Cap) (hw : CapWf srcC) (he : EncWf srcC)
    (hcv : CapValid th srcC) (hnc : NoChildrenRel (st := st) s σ (cslotAddr sl) sl) :
    ∃ r, cnode.copied_cap st s lbl length buf (cslotAddr sl) srcC = ok r ∧ ∃ R,
      (copyRest slbl (rest.map UScalar.bv) sl dsl (absCap srcC)).run σ = ({(R, σ)}, False) ∧
      CopiedRel th srcC sl dsl r R := by
  have hcases : lbl.val = 28 ∨ lbl.val = 29 ∨ lbl.val = 30 ∨ lbl.val = 31 := by omega
  -- the derive step shared by Copy and Mint
  have hder : ∀ c1, CapWf c1 → EncWf c1 → (∀ th, CapValid th srcC → CapValid th c1) → SameBadgeKind c1 srcC →
      ∀ mv : Fl4Spec.Cap → Except Fl4Spec.SyscallError Fl4Spec.CnodeInvocation,
      (∀ r', (Fl4Spec.deriveCap (Z := Unit) sl (absCap c1)).run σ = ({(r', σ)}, False) →
        (copyRest slbl (rest.map UScalar.bv) sl dsl (absCap srcC)).run σ =
          ({(finishRes false sl dsl r', σ)}, False)) →
      ∃ r, (do
          let r1 ← objects.derive_cap st s (cslotAddr sl) c1
          let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
          match cf with
            | core.ops.control_flow.ControlFlow.Continue val => ok (core.result.Result.Ok (val, false))
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual (capability.Cap × Bool)
                (core.convert.FromSame error.Exc) residual) = ok r ∧ ∃ R,
        (copyRest slbl (rest.map UScalar.bv) sl dsl (absCap srcC)).run σ = ({(R, σ)}, False) ∧
        CopiedRel th srcC sl dsl r R := by
    intro c1 hw1 he1 hv1 hk1 _ hrest
    obtain ⟨r, hr, r', hr', hd⟩ := derive_rel (Z := Unit) s σ (cslotAddr sl) sl c1 hw1 he1 (fun _ => hnc)
    rw [hr]; simp only [bind_ok]
    have hR := hrest r' hr'
    cases r with
    | Ok c' =>
      cases r' with
      | error _ => exact hd.elim
      | ok a' =>
        obtain ⟨hw', ha', he', hv', hk'⟩ := hd
        refine ⟨.Ok (c', false), by simp [core.result.Result.Insts.CoreOpsTry.branch], _, hR, ?_, hw', he',
          hv' th (hv1 th hcv), hk'.trans hk1⟩
        rw [ha']
    | Err e =>
      cases r' with
      | ok _ => exact hd.elim
      | error e' =>
        refine ⟨.Err e, ?_, _, hR, hd⟩
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
          core.convert.FromSame.from]
  unfold cnode.copied_cap
  rw [hct]; simp only [bind_ok]
  rcases hcases with hv | hv | hv | hv
  · -- Copy
    have hg : Fl4Spec.genInvocationType slbl = .cnodeCopy := by rw [hlbl]; simp [cnodeLabelOf, hv]
    have e : lbl = fl4_abi.label.CNodeCopy := by rw [u64_eq_iff]; simp [hv]
    rw [if_pos e]
    cases rest with
    | nil =>
      have : length < 5#u64 := by scalar_tac
      rw [if_pos this]
      exact ⟨_, rfl, _, copyRest_trunc _ _ _ _ σ _ (Or.inl ⟨hg, rfl⟩), trivial⟩
    | cons w rest =>
      have : ¬ length < 5#u64 := by scalar_tac
      rw [if_neg this]
      rw [hargs 4#u64 w (by simp) (by simp)]; simp only [bind_ok]; rw [from_word_eq]; simp only [bind_ok]
      obtain ⟨c1, hm, hw1, ha1, he1, hv1, hk1, -⟩ := mask_rel (rightsW w) srcC hw
      rw [hm]; simp only [bind_ok]
      refine hder c1 hw1 (he1 he) hv1 hk1 (fun _ => .error .illegalOperation) (fun r' hr' => ?_)
      rw [ha1, rightsW_spec] at hr'
      exact copyRest_copy _ _ _ _ σ hg w.bv _ hr'
  · -- Mint
    have hg : Fl4Spec.genInvocationType slbl = .cnodeMint := by rw [hlbl]; simp [cnodeLabelOf, hv]
    have e : lbl = fl4_abi.label.CNodeMint := by rw [u64_eq_iff]; simp [hv]
    have e' : ¬ lbl = fl4_abi.label.CNodeCopy := by rw [u64_eq_iff]; simp [hv]
    rw [if_neg e', if_pos e]
    match rest, hlen, hargs with
    | [], hlen, _ =>
      have : length < 6#u64 := by scalar_tac
      rw [if_pos this]
      exact ⟨_, rfl, _, copyRest_trunc _ _ _ _ σ _ (Or.inr (Or.inl ⟨hg, by simp⟩)), trivial⟩
    | [_], hlen, _ =>
      have : length < 6#u64 := by simp at hlen; scalar_tac
      rw [if_pos this]
      exact ⟨_, rfl, _, copyRest_trunc _ _ _ _ σ _ (Or.inr (Or.inl ⟨hg, by simp⟩)), trivial⟩
    | w :: d :: rest, hlen, hargs =>
      have : ¬ length < 6#u64 := by simp at hlen; scalar_tac
      rw [if_neg this]
      rw [hargs 4#u64 w (by simp) (by simp)]; simp only [bind_ok]; rw [from_word_eq]; simp only [bind_ok]
      rw [hargs 5#u64 d (by simp) (by simp)]; simp only [bind_ok]
      obtain ⟨c1, hm, hw1, ha1, he1, hv1, hk1, -⟩ := mask_rel (rightsW w) srcC hw
      rw [hm]; simp only [bind_ok]
      obtain ⟨c2, hu, hw2, ha2, he2, hv2, hk2⟩ := update_rel false d c1 hw1 (he1 he)
      rw [hu]; simp only [bind_ok]
      refine hder c2 hw2 he2 (fun th h => hv2 th (hv1 th h)) (hk2.trans hk1) (fun _ => .error .illegalOperation)
        (fun r' hr' => ?_)
      rw [ha2, ha1, rightsW_spec] at hr'
      exact copyRest_mint _ _ _ _ σ hg w.bv d.bv _ hr'
  · -- Move
    have hg : Fl4Spec.genInvocationType slbl = .cnodeMove := by rw [hlbl]; simp [cnodeLabelOf, hv]
    have e : lbl = fl4_abi.label.CNodeMove := by rw [u64_eq_iff]; simp [hv]
    have e1 : ¬ lbl = fl4_abi.label.CNodeCopy := by rw [u64_eq_iff]; simp [hv]
    have e2 : ¬ lbl = fl4_abi.label.CNodeMint := by rw [u64_eq_iff]; simp [hv]
    rw [if_neg e1, if_neg e2, if_pos e]
    refine ⟨.Ok (srcC, true), rfl, _, copyRest_move _ _ _ _ σ hg _, ?_, hw, he, hcv, SameBadgeKind.refl _⟩
    rw [maskCap_all _ hw]
  · -- Mutate
    have hg : Fl4Spec.genInvocationType slbl = .cnodeMutate := by rw [hlbl]; simp [cnodeLabelOf, hv]
    have e1 : ¬ lbl = fl4_abi.label.CNodeCopy := by rw [u64_eq_iff]; simp [hv]
    have e2 : ¬ lbl = fl4_abi.label.CNodeMint := by rw [u64_eq_iff]; simp [hv]
    have e3 : ¬ lbl = fl4_abi.label.CNodeMove := by rw [u64_eq_iff]; simp [hv]
    rw [if_neg e1, if_neg e2, if_neg e3]
    cases rest with
    | nil =>
      have : length < 5#u64 := by scalar_tac
      rw [if_pos this]
      exact ⟨_, rfl, _, copyRest_trunc _ _ _ _ σ _ (Or.inr (Or.inr ⟨hg, rfl⟩)), trivial⟩
    | cons d rest =>
      have : ¬ length < 5#u64 := by scalar_tac
      rw [if_neg this]
      rw [hargs 4#u64 d (by simp) (by simp)]; simp only [bind_ok]
      obtain ⟨c', hu, hw', ha', he', hv', hk'⟩ := update_rel true d srcC hw he
      rw [hu]; simp only [bind_ok]
      refine ⟨.Ok (c', true), rfl, _, copyRest_mutate _ _ _ _ σ hg d.bv _, ?_, hw', he', hv' th hcv, hk'⟩
      rw [maskCap_all _ hw, ha']

end

/-! ## `decode_copy` -/

/-- Extra caps: `extra[0]` (`x0`) is null and there are none, or it is
the slot of the first extra cap, related to the spec's. -/
def ExtraRel (th : TypedHeap) (mem : U64 → U64) (x0 : U64) (excaps : List Fl4Spec.Cap) : Prop :=
  (x0 = 0#u64 ∧ excaps = []) ∨
  (x0 ≠ 0#u64 ∧ ∃ c a rest, capAt mem x0 = ok c ∧ CapRel c a ∧ CapValid th c ∧ excaps = a :: rest)


theorem run_liftE' {σ α ε : Type} {m : Fl4Spec.NonDet σ α} {s s' : σ} {a : α} (h : m s = ({(a, s')}, False)) :
    (Fl4Spec.NonDetE.liftE (ε := ε) m).run s = ({(.ok a, s')}, False) := by
  unfold Fl4Spec.NonDetE.liftE
  rw [ExceptT.run_lift]
  show (m >>= _) s = _
  rw [nd_bind_one h]; rfl

theorem SlotsValid.abs {th : TypedHeap} {mem : U64 → U64} (hV : SlotsValid th mem) {sl : Fl4Spec.CslotPtr}
    (h : AbsSlot th sl) {c : capability.Cap} (hc : capAt mem (cslotAddr sl) = ok c) : CapValid th c := by
  obtain ⟨p, i, hi, -, he⟩ := h.at
  rw [he] at hc
  rcases hi with ⟨r, hp, hi⟩ | ⟨hp, hi⟩
  · exact hV.cnode p r hp i hi c hc
  · exact hV.tcb p hp i hi c hc

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- The outcome of a Copy/Mint/Move/Mutate against a spec decode `m`: the
same error with the state unchanged, or an invocation after which (with
`set_thread_state Restart` first) `invoke_cnode` ends in a related state,
with the MDB invariant, `FinInv`, and the `MdbStep` taken. -/
def InvPost (th : TypedHeap) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (m : Fl4Spec.SEMonad Unit Fl4Spec.CnodeInvocation) (s : S) :
    core.result.Result Unit error.Exc × S → Prop
  | (.Err e, s') => s' = s ∧ ∃ e', m.run σ = ({(.error e', σ)}, False) ∧ SysErrRel e e'
  | (.Ok (), s') => ∃ inv, m.run σ = ({(.ok inv, σ)}, False) ∧ ∃ σ1,
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
      ∃ σ' G', (Fl4Spec.invokeCnode (Z := Unit) inv).run σ1 = ({(.ok (), σ')}, False) ∧
        StateRel th (L.mem s') σ' ∧ SlotsValid th (L.mem s') ∧ MdbLinks th (L.mem s') G' ∧
        CdtRel th (L.mem s') σ' G' ∧ MdbInv (L.mem s') G' ∧ FinInv th (L.mem s') σ' G' ∧
        MdbStep (L.mem s) G (L.mem s') G'

theorem InvPost.of_run {th : TypedHeap} {σ : Fl4Spec.State Unit} {G : MdbGhost}
    {m m' : Fl4Spec.SEMonad Unit Fl4Spec.CnodeInvocation} (h : m.run σ = m'.run σ) {s : S}
    {res : core.result.Result Unit error.Exc × S} (hq : InvPost (L := L) th σ G m' s res) :
    InvPost (L := L) th σ G m s res := by
  obtain ⟨r, s'⟩ := res
  cases r with
  | Err e => obtain ⟨h1, e', h2, h3⟩ := hq; exact ⟨h1, e', h.trans h2, h3⟩
  | Ok u => obtain ⟨inv, h2, h3⟩ := hq; exact ⟨inv, h.trans h2, h3⟩

theorem InvPost.congr {th : TypedHeap} {σ : Fl4Spec.State Unit} {G : MdbGhost}
    {m m' : Fl4Spec.SEMonad Unit Fl4Spec.CnodeInvocation} (h : m.run σ = m'.run σ) {s : S}
    {prog : Result (core.result.Result Unit error.Exc × S)}
    (hp : prog ⦃ res => InvPost (L := L) th σ G m' s res ⦄) : prog ⦃ res => InvPost (L := L) th σ G m s res ⦄ := by
  refine WP.spec_mono hp ?_
  rintro ⟨r, s'⟩ hq
  cases r with
  | Err e => obtain ⟨h1, e', h2, h3⟩ := hq; exact ⟨h1, e', h.trans h2, h3⟩
  | Ok u => obtain ⟨inv, h2, h3⟩ := hq; exact ⟨inv, h.trans h2, h3⟩

/-- A spec computation with the single, state-preserving outcome `R`. -/
def ofExcept {α : Type} (R : Except Fl4Spec.SyscallError α) : Fl4Spec.SEMonad Unit α :=
  match R with
  | .ok a => Fl4Spec.NonDetE.returnOk a
  | .error e => Fl4Spec.NonDetE.throwError e

theorem run_ofExcept {α : Type} (R : Except Fl4Spec.SyscallError α) (σ : Fl4Spec.State Unit) :
    (ofExcept R).run σ = ({(R, σ)}, False) := by
  cases R <;> rfl

theorem lookup_source_eq (s : S) (root : capability.Cap) (c d : U64) :
    cspace.lookup_source_slot st s root c d = cspace.lookup_slot_for_cnode_op st s true root c d := rfl

/-- **`decode_copy` refines the spec's Copy/Mint/Move/Mutate branch**
(`copyTail`, after the target slot lookup), then `set_thread_state
Restart` and `invoke_cnode` (`insert_refines`, `move_refines`). -/
theorem decode_copy_rel (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = cnodeLabelOf lbl)
    (hl : 28 ≤ lbl.val ∧ lbl.val ≤ 31)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length) (h2 : 2 ≤ args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List Fl4Spec.Cap) (hex : ExtraRel th (L.mem s) x0 excaps)
    (hI : MdbInv (L.mem s) G) (hFI : FinInv th (L.mem s) σ G)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (dsl : Fl4Spec.CslotPtr) (pd : U64) (hpd1 : dsl.1 = pd.bv) (hpd : th pd = some (.cnode dsl.2.length)) :
    cnode.decode_copy st s lbl length buf extra (cslotAddr dsl) ⦃ res =>
      InvPost (L := L) th σ G (copyTail slbl ((args.map UScalar.bv).drop 2) excaps dsl) s res ⦄ := by
  have hts := set_thread_state_slots th hP s ct sched.TS_RESTART htcb hact
  have hgl : IsCopyLabel (Fl4Spec.genInvocationType slbl) := by
    rw [hlbl]; unfold cnodeLabelOf IsCopyLabel
    have : lbl.val = 28 ∨ lbl.val = 29 ∨ lbl.val = 30 ∨ lbl.val = 31 := by omega
    rcases this with h | h | h | h <;> simp [h]
  unfold cnode.decode_copy
  by_cases h4 : length < 4#u64
  · -- too few arguments
    rw [if_pos h4]
    simp only [error.truncated, bind_ok, WP.spec_ok]
    refine ⟨rfl, .truncatedMessage, ?_, trivial⟩
    rw [copyTail_short _ _ hgl _ _ (fun ⟨h, _⟩ => by simp at h; scalar_tac)]; rfl
  rw [if_neg h4]
  obtain ⟨a0, a1, i1, d1, rest, rfl⟩ : ∃ a0 a1 i1 d1 rest, args = a0 :: a1 :: i1 :: d1 :: rest := by
    match args, h2 with
    | [_, _], _ => exfalso; simp at hlen; scalar_tac
    | [_, _, _], _ => exfalso; simp at hlen; scalar_tac
    | a0 :: a1 :: i1 :: d1 :: rest, _ => exact ⟨a0, a1, i1, d1, rest, rfl⟩
  simp only [List.map_cons, List.drop_succ_cons, List.drop_zero]
  rw [hx0]; simp only [bind_ok, obj.Slot.is_null]
  rcases hex with ⟨rfl, rfl⟩ | ⟨hx0n, c0, ac0, erest, hc0, hca0, hcv0, rfl⟩
  · -- no extra cap
    simp only [decide_true, ↓reduceIte, error.truncated, bind_ok, WP.spec_ok]
    refine ⟨rfl, .truncatedMessage, ?_, trivial⟩
    rw [copyTail_short _ _ hgl _ _ (fun ⟨_, h⟩ => by simp at h)]; rfl
  simp only [hx0n, decide_false, Bool.false_eq_true, ↓reduceIte]
  simp only [hct, hargs 2#u64 i1 (by simp), hargs 3#u64 d1 (by simp), slot_cap_eq, hc0, bind_ok]
  rw [copyTail_body _ hgl]
  -- the destination must be empty
  obtain ⟨cd, ad, hcd, hcad, hgd⟩ := hR.slot_cap (Z := Unit) hpd1 hpd
  unfold cdt.ensure_empty_slot
  simp only [slot_cap_eq, hcd, bind_ok]
  have hee := ensureEmpty_run dsl σ hgd
  by_cases hdn : cd = .Null
  swap
  · rw [cap_is_null_ne hdn]
    simp only [bind_ok, Bool.false_eq_true, ↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from, bind_tc_ok]
    rw [WP.spec_ok]
    have : ad ≠ .nullCap := fun h => hdn ((hcad.null_iff).1 h)
    simp only [this, ↓reduceIte] at hee
    exact ⟨rfl, .deleteFirst, run_bind_error hee _, trivial⟩
  subst hdn
  have hadn : ad = .nullCap := (hcad.null_iff).2 rfl
  simp only [hadn, ↓reduceIte] at hee
  rw [cap_is_null_null]
  simp only [bind_ok, ↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch]
  refine InvPost.congr (run_bind_ok hee _) ?_
  -- the source slot
  rw [lookup_source_eq]
  obtain ⟨r1, hr1, e1, he1, hrel1⟩ := spec_exists
    (lookup_slot_for_cnode_op_refines (Z := Unit) th s σ hR hV true c0 ac0 hca0 hcv0 i1 d1)
  rw [hr1]; simp only [bind_ok]
  have hls : (Fl4Spec.lookupSourceSlot (Z := Unit) ac0 (Fl4Spec.dataToCptr i1.bv) (Fl4Spec.dataToNat d1.bv)).run σ =
      ({(e1, σ)}, False) := he1
  cases r1 with
  | Err e =>
    cases e1 with
    | ok _ => exact hrel1.elim
    | error e' =>
      simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
        core.convert.FromSame.from, bind_ok, bind_tc_ok]
      rw [WP.spec_ok]
      exact ⟨rfl, e', run_bind_error hls _, hrel1⟩
  | Ok src =>
    cases e1 with
    | error _ => exact hrel1.elim
    | ok sl =>
      obtain ⟨rfl, ps, hps1, hps⟩ := hrel1
      refine InvPost.congr (run_bind_ok hls _) ?_
      have hAs : AbsSlot th sl := ⟨ps, hps1, Or.inl hps⟩
      obtain ⟨srcC, srcA, hsc, hsca, hgs⟩ := hR.slot_cap (Z := Unit) hps1 hps
      have hscv := hV.abs hAs hsc
      simp only [hsc, bind_ok]
      refine InvPost.congr (run_bind_ok (run_liftE hgs) _) ?_
      by_cases hsn : srcC = .Null
      · subst hsn
        have : srcA = .nullCap := (hsca.null_iff).2 rfl
        rw [cap_is_null_null]
        simp only [bind_ok, ↓reduceIte, cnode.missing_source]
        rw [WP.spec_ok]
        refine ⟨rfl, .failedLookup true (.missingCapability d1.val), ?_, show true = true ∧ d1.val = d1.val from ⟨rfl, rfl⟩⟩
        simp only [this, Fl4Spec.NonDetE.whenE, ↓reduceIte, Fl4Spec.NonDetE.throwError, ndE_throw_bind]; rfl
      have hsan : srcA ≠ .nullCap := fun h => hsn ((hsca.null_iff).1 h)
      rw [cap_is_null_ne hsn]
      simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
      refine InvPost.congr (show _ = (copyRest slbl (rest.map UScalar.bv) sl dsl srcA).run σ by
        simp only [hsan, Fl4Spec.NonDetE.whenE, ↓reduceIte, ndE_pure_bind]) ?_
      -- the new cap
      have hsw : CapWf srcC := hsca.1
      have hse : EncWf srcC := by rw [capAt_words] at hsc; exact decode_encWf hsc
      have hlen' : length.val = rest.length + 4 := by simp at hlen; omega
      have hargs' : ∀ (i : U64) x, rest[i.val - 4]? = some x → 4 ≤ i.val → msg.syscall_arg st s ct buf i = ok x := by
        intro i x hx hi
        apply hargs i x
        have : i.val = (i.val - 4) + 4 := by omega
        rw [this]; simpa using hx
      have hnc0 := noChildren_of_adj th hP s σ G hM hC (hI.parentAdj (th := th)) sl hAs
        ((hM.members _).2 ⟨hAs.isSlot, srcC, hsc, hsn⟩)
      obtain ⟨r2, hr2, R, hR2, hrel2⟩ := copied_rel th s σ lbl slbl hlbl hl length buf ct hct rest hlen' hargs'
        sl dsl srcC hsw hse hscv hnc0
      rw [← hsca.abs] at hR2
      refine InvPost.congr (hR2.trans (run_ofExcept R σ).symm) ?_
      rw [hr2]; simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
      cases r2 with
      | Err e =>
        cases R with
        | ok _ => exact hrel2.elim
        | error e' =>
          simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame, core.convert.FromSame.from, bind_ok, bind_tc_ok]
          rw [WP.spec_ok]
          exact ⟨rfl, e', run_ofExcept _ σ, hrel2⟩
      | Ok v =>
        obtain ⟨nc, mv⟩ := v
        obtain ⟨rfl, hw', he', hv', hk'⟩ := hrel2
        simp only [bind_ok, uncurry_apply_pair]
        by_cases hnn : nc = .Null
        · subst hnn
          rw [cap_is_null_null]
          simp only [bind_ok, ↓reduceIte, error.illegal]
          rw [WP.spec_ok]
          exact ⟨rfl, .illegalOperation, by rw [run_ofExcept]; simp [finishRes, absCap], trivial⟩
        have hann : absCap nc ≠ .nullCap := fun h => hnn ((show CapRel nc (absCap nc) from ⟨hw', rfl⟩).null_iff.1 h)
        obtain ⟨hsh, hbm, hbi⟩ := copied_shape hr2 hnn hnc0
        rw [cap_is_null_ne hnn]
        simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
        -- set_thread_state
        obtain ⟨s2, hs2, hS⟩ := spec_exists hts
        rw [hs2]; simp only [bind_ok]
        obtain ⟨tcb, hk, -⟩ := hR.tcb ct htcb
        rw [← hcur] at hk
        obtain ⟨σ1, hst, hR1, hV1, hM1, hC1, -, hio1⟩ := restart_rel hR hV hM hC hS hk .restart
        have hI1 := MdbInv.of_same hM hI hS
        have hFI1 := hFI.of_same hM hS (ksub_of_eq (setThreadState_nks _ _) hst)
        have hkey := copied_okey hr2 hnn
        -- the slots, after `set_thread_state`
        obtain ⟨sa, sb⟩ := sl
        simp only at hps1; subst hps1
        obtain ⟨da, db⟩ := dsl
        simp only at hpd1; subst hpd1
        have hAd : AbsSlot th (pd.bv, db) := ⟨pd, rfl, Or.inl hpd⟩
        have hsc2 : capAt (L.mem s2) (cslotAddr (ps.bv, sb)) = ok srcC := by rw [hS.capAt hAs.isSlot, hsc]
        have hdc2 : capAt (L.mem s2) (cslotAddr (pd.bv, db)) = ok .Null := by rw [hS.capAt hAd.isSlot, hcd]
        cases mv
        · -- insert
          simp only [Bool.false_eq_true, ↓reduceIte]
          obtain ⟨hbd, hzb, hut⟩ := hbi rfl
          have hut' : isUt srcC = true → ∀ y, ¬ Mdb.Desc G.par y (cslotAddr (ps.bv, sb)) := by
            intro hu y hy
            obtain ⟨z, hz⟩ := desc_tail_child hy
            exact hut hu ((hC.has_child_iff hP hAs).2 ⟨z, hz⟩)
          obtain ⟨s3, hs3, σ', G', hins, hR', hV', hM', hC', hI', hFI', hSt⟩ := spec_exists
            (insert_full_fin th s2 σ1 G hR1 hV1 hP hM1 hC1 hI1 hFI1 hps hpd rfl rfl hsc2 hsn hdc2 nc (absCap nc)
              ⟨hw', rfl⟩ hv' he' hnn hsh hbd hut' hzb hkey (copied_vcap hr2))
          rw [hs3]; simp only [bind_ok]
          rw [WP.spec_ok]
          refine ⟨.insertCall (absCap nc) (ps.bv, sb) (pd.bv, db), ?_, σ1, hst,
            σ', G', run_liftE' hins, hR', hV', hM', hC', hI', hFI', MdbStep.same_left hM hS (hSt (copied_ut hr2))⟩
          rw [run_ofExcept]; simp [finishRes, hann]
        · -- move
          simp only [↓reduceIte]
          obtain ⟨s3, hs3, σ', G', hmv, hR', hV', hM', hC', hI', hFI', hSt⟩ := spec_exists
            (move_full_fin th s2 σ1 G hR1 hV1 hP hM1 hC1 hI1 hFI1 hps hpd rfl rfl hsc2 hsn hdc2 nc (absCap nc) ⟨hw', rfl⟩
              hv' he' hnn hsh (hbm rfl) hkey (copied_vcap hr2))
          rw [hs3]; simp only [bind_ok]
          rw [WP.spec_ok]
          refine ⟨.moveCall (absCap nc) (ps.bv, sb) (pd.bv, db), ?_, σ1, hst,
            σ', G', run_liftE' hmv, hR', hV', hM', hC', hI', hFI', MdbStep.same_left hM hS (hSt (copied_ut hr2))⟩
          rw [run_ofExcept]; simp [finishRes, hann]

/-- **FL4's CNode Copy, Mint, Move and Mutate refine l4v's**: for labels
28..31, `cnode::decode` ends with the error `decode_cnode_invocation`
throws (state unchanged), or, when the spec decodes an invocation, in a
state related to the spec's after `set_thread_state Restart` and
`invoke_cnode`, with the MDB invariant and `FinInv` kept. -/
theorem cnode_copy_refines {A : Type} (arI : machine.Arch A) (th : TypedHeap) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = cnodeLabelOf lbl)
    (hl : 28 ≤ lbl.val ∧ lbl.val ≤ 31)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (cap : capability.Cap) (a : Fl4Spec.Cap) (hca : CapRel cap a) (hcv : CapValid th cap)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List Fl4Spec.Cap) (hex : ExtraRel th (L.mem s) x0 excaps)
    (hI : MdbInv (L.mem s) G) (hFI : FinInv th (L.mem s) σ G)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb) :
    cnode.decode st arI s ar lbl length cap buf extra ⦃ res =>
      InvPost (L := L) th σ G (Fl4Spec.decodeCnodeInvocation slbl (args.map UScalar.bv) a excaps) s
        (res.1, res.2.1) ⦄ := by
  have hgl : IsCopyLabel (Fl4Spec.genInvocationType slbl) := by
    rw [hlbl]; unfold cnodeLabelOf IsCopyLabel
    have : lbl.val = 28 ∨ lbl.val = 29 ∨ lbl.val = 30 ∨ lbl.val = 31 := by omega
    rcases this with h | h | h | h <;> simp [h]
  unfold cnode.decode
  have n1 : ¬ lbl < fl4_abi.label.CNodeRevoke := by have := lbl_revoke_val; scalar_tac
  have n2 : ¬ lbl > fl4_abi.label.CNodeRotate := by have := lbl_rotate_val; scalar_tac
  rw [if_neg n1, if_neg n2]
  by_cases h2 : length < 2#u64
  · rw [if_pos h2]
    simp only [error.truncated, bind_ok]
    rw [WP.spec_ok]
    exact ⟨rfl, .truncatedMessage, decode_short _ _ _ σ hgl.facts.1 _ (by simp; scalar_tac), trivial⟩
  rw [if_neg h2]
  obtain ⟨y0, y1, rest, rfl⟩ : ∃ y0 y1 rest, args = y0 :: y1 :: rest := by
    match args with
    | [] => exfalso; simp at hlen; scalar_tac
    | [_] => exfalso; simp at hlen; scalar_tac
    | y0 :: y1 :: rest => exact ⟨y0, y1, rest, rfl⟩
  simp only [hct, hargs 0#u64 y0 (by simp), hargs 1#u64 y1 (by simp), bind_ok]
  unfold cspace.lookup_target_slot
  obtain ⟨r1, hr1, e1, he1, hrel1⟩ := spec_exists
    (lookup_slot_for_cnode_op_refines (Z := Unit) th s σ hR hV false cap a hca hcv y0 y1)
  rw [hr1]; simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
  have hlt : (Fl4Spec.lookupTargetSlot (Z := Unit) a (Fl4Spec.dataToCptr y0.bv) (Fl4Spec.dataToNat y1.bv)).run σ =
      ({(e1, σ)}, False) := he1
  have hdec := decode_lookup slbl a excaps hgl.facts.1 y0.bv y1.bv (rest.map UScalar.bv)
  simp only [List.map_cons]
  rw [hdec]
  cases r1 with
  | Err e =>
    cases e1 with
    | ok _ => exact hrel1.elim
    | error e' =>
      simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, core.convert.FromSame.from, bind_ok, bind_tc_ok]
      rw [WP.spec_ok]
      exact ⟨rfl, e', run_bind_error hlt _, hrel1⟩
  | Ok dest =>
    cases e1 with
    | error _ => exact hrel1.elim
    | ok dsl =>
      obtain ⟨rfl, pd, hpd1, hpd⟩ := hrel1
      have g1 : lbl ≥ fl4_abi.label.CNodeCopy := by have := lbl_copy_val; scalar_tac
      have g2 : lbl ≤ fl4_abi.label.CNodeMutate := by have := lbl_mutate_val; scalar_tac
      simp only [g1, g2, ↓reduceIte, bind_ok]
      obtain ⟨⟨r2, s2⟩, hdc, hpost⟩ := spec_exists
        (decode_copy_rel th s σ G hR hV hP hM hC lbl slbl hlbl hl length buf ct hct (y0 :: y1 :: rest) hlen
          (by simp) hargs extra x0 hx0 excaps hex hI hFI hact hcur htcb dsl pd hpd1 hpd)
      rw [hdc]; simp only [bind_ok, uncurry_apply_pair]
      rw [WP.spec_ok]
      simp only [List.map_cons, List.drop_succ_cons, List.drop_zero] at hpost
      exact InvPost.of_run (run_bind_ok hlt _) hpost

end

end

end Fl4Proofs.P3
