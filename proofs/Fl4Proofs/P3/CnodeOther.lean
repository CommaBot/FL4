/-
P3 (DESIGN.md §9), CSpace: the CNode invocations Revoke, Delete and
CancelBadgedSends (labels 25, 26, 27), in the scopes where they are trivial
(see `cnode_other_refines`), and the transport lemmas they need across
`set_thread_state`:
* spec: `get_cap` (hence `is_final_cap`) does not see thread states
  (`getCap_set_iff`, `isFinalCap'_tcb_state`);
* FL4: `is_final_capability` and `is_mdb_parent_of` read only slot words
  (`is_final_same`, `is_mdb_parent_same`, `ParentAdj.of_same`).
-/
import Fl4Proofs.P3.Delete
import Fl4Proofs.P3.CnodeCopy
import Fl4Proofs.P3.SwapRefine
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-! ## Spec: caps do not depend on thread states -/

section
open Fl4Spec

/-- The cap at index `c` of an object, as `get_cap` reads it. -/
def capOpt : Option KernelObject → CnodeIndex → Option Cap
  | some (.cnode sz cn), c => if wellFormedCnodeN sz cn then cn c else none
  | some (.tcb tcb), c => tcbCnodeMap tcb c
  | _, _ => none

theorem getCap_set_iff (σ : State Unit) (o : ObjRef) (c : CnodeIndex) (a : Cap) :
    (getCap (Z := Unit) (o, c) σ).1 = {(a, σ)} ↔ capOpt (σ.kheap o) c = some a := by
  unfold getCap getObject
  cases h : σ.kheap o with
  | none =>
    simp [nd_bind_apply, NonDet.getsThe, readObject, h, NonDet.assertOpt, NonDet.fail, capOpt]
  | some obj =>
    cases obj <;> simp [nd_bind_apply, NonDet.getsThe, readObject, h, NonDet.assertOpt, NonDet.fail, capOpt,
      NonDet.pure, NonDet.assert]
    case cnode sz cs =>
      by_cases hw : wellFormedCnodeN sz cs
      · cases hc : cs c <;> simp [hw, hc, NonDet.pure, NonDet.fail]
      · simp [hw]
    case tcb t =>
      cases hc : tcbCnodeMap t c <;> simp [NonDet.pure, NonDet.fail]
theorem capOpt_tcb_state {σ σ1 : State Unit} {t : ObjRef} {tcb : Tcb} (hk : σ.kheap t = some (.tcb tcb))
    {ts : ThreadState} (h1 : σ1.kheap = Function.update σ.kheap t (some (.tcb { tcb with tcbState := ts })))
    (o : ObjRef) : capOpt (σ1.kheap o) = capOpt (σ.kheap o) := by
  rw [h1]
  by_cases ho : o = t
  · subst ho; rw [Function.update_self, hk]; funext c; rfl
  · rw [Function.update_of_ne ho]

theorem isFinalCap'_tcb_state {σ σ1 : State Unit} {t : ObjRef} {tcb : Tcb} (hk : σ.kheap t = some (.tcb tcb))
    {ts : ThreadState} (h1 : σ1.kheap = Function.update σ.kheap t (some (.tcb { tcb with tcbState := ts })))
    (a : Cap) : isFinalCap' a σ1 ↔ isFinalCap' a σ := by
  have e : ∀ cref : CslotPtr, ∀ cap' : Cap, ((getCap (Z := Unit) cref σ1).1 = {(cap', σ1)}) ↔
      ((getCap (Z := Unit) cref σ).1 = {(cap', σ)}) := by
    rintro ⟨o, c⟩ cap'
    rw [getCap_set_iff, getCap_set_iff, capOpt_tcb_state hk h1]
  unfold isFinalCap'
  simp only [e]

end

/-! ## FL4: reads of slot words only -/

theorem SlotsSame.fbOf {th : TypedHeap} {m m' : U64 → U64} (h : SlotsSame th m m') {a : U64} (ha : IsSlot th a) :
    fbOf m' a = fbOf m a := by
  unfold Fl4Proofs.P3.fbOf; rw [(h a ha).2.2.2]

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem is_final_same {th : TypedHeap} {s s' : S} (hS : SlotsSame th (L.mem s) (L.mem s')) {x : U64}
    (hx : IsSlot th x) (hp : prevOf (L.mem s) x = 0#u64 ∨ IsSlot th (prevOf (L.mem s) x))
    (hn : nextOf (L.mem s) x = 0#u64 ∨ IsSlot th (nextOf (L.mem s) x)) :
    cdt.is_final_capability st s' x = cdt.is_final_capability st s x := by
  unfold cdt.is_final_capability
  simp only [slot_cap_eq, slot_prev_eq, slot_next_eq, hS.capAt hx, hS.prevOf hx, hS.nextOf hx, bind_ok]
  rcases hp with hp | hp <;> rcases hn with hn | hn
  · simp [hp, hn, obj.Slot.is_null]
  · simp [hp, obj.Slot.is_null, hS.capAt hn]
  · simp [hn, obj.Slot.is_null, hS.capAt hp]
  · simp [obj.Slot.is_null, hS.capAt hp, hS.capAt hn]

theorem is_mdb_parent_same {th : TypedHeap} {s s' : S} (hS : SlotsSame th (L.mem s) (L.mem s')) {a b : U64}
    (ha : IsSlot th a) (hb : IsSlot th b) :
    cdt.is_mdb_parent_of st s' a b = cdt.is_mdb_parent_of st s a b := by
  unfold cdt.is_mdb_parent_of
  simp only [slot_rev_eq, slot_cap_eq, slot_first_badged_eq, hS.revOf ha, hS.capAt ha, hS.capAt hb, hS.fbOf hb]

theorem ParentAdj.of_same {th : TypedHeap} {s s' : S} {G : MdbGhost} (hM : MdbLinks th (L.mem s) G)
    (hA : ParentAdj (L := L) th s G) (hS : SlotsSame th (L.mem s) (L.mem s')) : ParentAdj (L := L) th s' G := by
  intro x hx hn
  have hxs : IsSlot th x := ((hM.members x).1 hx).1
  rw [hS.nextOf hxs] at hn ⊢
  obtain ⟨b, hb, hbd⟩ := hA x hx hn
  have hns : IsSlot th (nextOf (L.mem s) x) := by
    rcases hM.next_mem hx with h | ⟨h, -⟩
    · exact absurd h hn
    · exact ((hM.members _).1 h).1
  exact ⟨b, by rw [is_mdb_parent_same hS hxs hns, hb], hbd⟩

end

/-! ## Revoke of a slot without children -/

theorem lfp_one {σ α ι : Type} (F : (ι → Fl4Spec.NonDet σ α) → ι → Fl4Spec.NonDet σ α) (j : ι) (s : σ)
    (X : Set (α × σ) × Prop) (hj : ∀ f, F f j s = X) : Fl4Spec.NonDet.lfp F j s = X := by
  let S := {f : ι → σ → Set (α × σ) × Prop | ∀ k t, F f k t ≤ f k t}
  have hl : Fl4Spec.NonDet.lfp F = (sInf S : ι → σ → Set (α × σ) × Prop) := rfl
  let fs : ι → Fl4Spec.NonDet σ α := fun k t => if k = j ∧ t = s then X else ⊤
  have hfsj : fs j s = X := by simp [fs]
  have hfs : (fs : ι → σ → Set (α × σ) × Prop) ∈ S := by
    intro k t
    by_cases h1 : k = j ∧ t = s
    · obtain ⟨rfl, rfl⟩ := h1; exact (hj fs).le.trans hfsj.ge
    · show F fs k t ≤ (if k = j ∧ t = s then X else ⊤)
      simp only [h1, ↓reduceIte]; exact le_top
  have hup : (sInf S : ι → σ → Set (α × σ) × Prop) ≤ fs := sInf_le hfs
  let g : ι → σ → Set (α × σ) × Prop := fun k t => if k = j ∧ t = s then X else ⊥
  have hlow : g ≤ (sInf S : ι → σ → Set (α × σ) × Prop) := by
    apply le_sInf
    intro f hf k t
    by_cases h1 : k = j ∧ t = s
    · obtain ⟨rfl, rfl⟩ := h1; simp only [g, and_self, ↓reduceIte]; exact (hj f).ge.trans (hf _ _)
    · simp only [g, h1, ↓reduceIte]; exact bot_le
  rw [hl]
  apply le_antisymm
  · exact (hup j s).trans hfsj.le
  · have := hlow j s; simpa [g] using this

theorem descendantsOf_empty_iff (p : Fl4Spec.CslotPtr) (t : Fl4Spec.Cdt) :
    Fl4Spec.descendantsOf p t = ∅ ↔ ¬ ∃ c, t c = some p := by
  constructor
  · rintro h ⟨c, hc⟩
    have : c ∈ Fl4Spec.descendantsOf p t := Relation.TransGen.single hc
    rw [h] at this; exact this
  · intro h
    apply Set.eq_empty_iff_forall_notMem.2
    intro q hq
    obtain ⟨b, hb, -⟩ := Relation.TransGen.head'_iff.1 hq
    exact h ⟨b, hb⟩

/-- **The spec's `cap_revoke` of a slot without children** does nothing. -/
theorem capRevoke_none (sl : Fl4Spec.CslotPtr) (σ : Fl4Spec.State Unit) {a : Fl4Spec.Cap}
    (hg : Fl4Spec.getCap (Z := Unit) sl σ = ({(a, σ)}, False)) (hn : ¬ ∃ c, σ.cdt c = some sl) :
    (Fl4Spec.capRevoke (Z := Unit) sl).run σ = ({(.ok (), σ)}, False) := by
  have hd := (descendantsOf_empty_iff sl σ.cdt).2 hn
  refine lfp_one (fun r c => Fl4Spec.capRevokeF (Z := Unit) r c) sl σ _ (fun f => ?_)
  show (Fl4Spec.capRevokeF f sl).run σ = _
  unfold Fl4Spec.capRevokeF Fl4Spec.withoutPreemption
  rw [run_bind_ok (run_liftE hg)]
  rw [run_bind_ok (run_liftE (m := Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.cdt) rfl)]
  simp only [Fl4Spec.NonDetE.returnOk, ndE_pure_bind, Fl4Spec.NonDetE.whenE, hd, ne_eq, not_true_eq_false,
    and_false, ↓reduceIte]
  rfl

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **FL4's `revoke` of a slot of the tree without (ghost) children**
returns at once. -/
theorem revoke_none (th : TypedHeap) (hP : Placed th) (s : S) (a : A) (G : MdbGhost)
    (hM : MdbLinks th (L.mem s) G) (hA : ParentAdj (L := L) th s G) {x : U64} (hx : x ∈ G.chains.flatten)
    (hn : ¬ ∃ c, G.par c = some x) :
    cdt.revoke st arI s a x = ok (.Ok (), s, a) := by
  unfold cdt.revoke cdt.revoke_loop
  rw [loop]
  have hf : layout.WALK_FUEL > 0#u64 := by simp [layout.WALK_FUEL, U64.rMax]
  obtain ⟨v, hv, -⟩ := spec_exists (U64.sub_spec (x := layout.WALK_FUEL) (y := 1#u64) (by simp [layout.WALK_FUEL, U64.rMax]))
  unfold cdt.revoke_loop.body
  simp only [hf, ↓reduceIte, hv, bind_ok, slot_next_eq, obj.Slot.is_null]
  by_cases h0 : nextOf (L.mem s) x = 0#u64
  · simp [h0]
  · obtain ⟨b, hb, hbd⟩ := hA x hx h0
    have hbf : b = false := by
      cases b
      · rfl
      · exact absurd ((hM.has_child_iff hP hx).2 ⟨h0, hbd.1 rfl⟩) hn
    simp [h0, hb, hbf]

end

/-! ## The spec's Revoke, Delete and CancelBadgedSends branches -/

section
open Fl4Spec

def IsOtherLabel (g : GenInvocationLabels) : Prop :=
  g = .cnodeRevoke ∨ g = .cnodeDelete ∨ g = .cnodeCancelBadgedSends

theorem IsOtherLabel.facts {g : GenInvocationLabels} (h : IsOtherLabel g) :
    g ∈ GenInvocationLabels.uptoEnum .cnodeRevoke .cnodeRotate ∧
    g ∉ GenInvocationLabels.uptoEnum .cnodeCopy .cnodeMutate := by
  rcases h with rfl | rfl | rfl <;> decide

theorem copyTail_revoke (label : Data) (args : List Data) (excaps : List Cap) (d : CslotPtr)
    (hg : genInvocationType label = .cnodeRevoke) :
    copyTail label args excaps d = NonDetE.returnOk (.revokeCall d) := by
  have := (IsOtherLabel.facts (Or.inl hg)).2
  have hc : ¬ (args.length ≥ 2 ∧ excaps.length > 0 ∧
      genInvocationType label ∈ GenInvocationLabels.uptoEnum .cnodeCopy .cnodeMutate) := fun h => this h.2.2
  unfold copyTail; rw [if_neg hc]; simp [hg]

theorem copyTail_delete (label : Data) (args : List Data) (excaps : List Cap) (d : CslotPtr)
    (hg : genInvocationType label = .cnodeDelete) :
    copyTail label args excaps d = NonDetE.returnOk (.deleteCall d) := by
  have := (IsOtherLabel.facts (Or.inr (Or.inl hg))).2
  have hc : ¬ (args.length ≥ 2 ∧ excaps.length > 0 ∧
      genInvocationType label ∈ GenInvocationLabels.uptoEnum .cnodeCopy .cnodeMutate) := fun h => this h.2.2
  unfold copyTail; rw [if_neg hc]; simp [hg]

theorem copyTail_cancel (label : Data) (args : List Data) (excaps : List Cap) (d : CslotPtr)
    (hg : genInvocationType label = .cnodeCancelBadgedSends) :
    copyTail label args excaps d = (do
      let cap ← NonDetE.liftE <| getCap d
      NonDetE.unlessE (hasCancelSendRights cap) <| NonDetE.throwError .illegalOperation
      NonDetE.returnOk <| .cancelBadgedSendsCall cap) := by
  have := (IsOtherLabel.facts (Or.inr (Or.inr hg))).2
  have hc : ¬ (args.length ≥ 2 ∧ excaps.length > 0 ∧
      genInvocationType label ∈ GenInvocationLabels.uptoEnum .cnodeCopy .cnodeMutate) := fun h => this h.2.2
  unfold copyTail; rw [if_neg hc]; simp [hg]

end

theorem rightsOf_all (a b c d : Bool) :
    rightsOf a b c d = Fl4Spec.allRights ↔ (a = true ∧ b = true ∧ c = true ∧ d = true) := by
  constructor
  · intro h
    have h1 : Fl4Spec.Rights.allowWrite ∈ rightsOf a b c d := by rw [h]; trivial
    have h2 : Fl4Spec.Rights.allowRead ∈ rightsOf a b c d := by rw [h]; trivial
    have h3 : Fl4Spec.Rights.allowGrant ∈ rightsOf a b c d := by rw [h]; trivial
    have h4 : Fl4Spec.Rights.allowGrantReply ∈ rightsOf a b c d := by rw [h]; trivial
    exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    ext x; cases x <;> simp [rightsOf, Fl4Spec.allRights]

/-- `full_endpoint` is the spec's `has_cancel_send_rights`. -/
theorem full_endpoint_rel (c : capability.Cap) :
    ∃ o, cnode.full_endpoint c = ok o ∧
      (∀ p b, o = some (p, b) ↔ c = .Endpoint p b true true true true) ∧
      (Fl4Spec.hasCancelSendRights (absCap c) ↔ o.isSome) := by
  cases c
  case Endpoint p b w r g gr =>
    cases w <;> cases r <;> cases g <;> cases gr <;>
      simp [cnode.full_endpoint, absCap, Fl4Spec.hasCancelSendRights, rightsOf_all]
  all_goals exact ⟨none, rfl, by simp, by simp [absCap, Fl4Spec.hasCancelSendRights]⟩

/-! ## `cnode::decode` for Revoke, Delete and CancelBadgedSends -/

theorem TrivKind.of_iff {σ σ' : Fl4Spec.State Unit} (h : ∀ a, Fl4Spec.isFinalCap' a σ' ↔ Fl4Spec.isFinalCap' a σ)
    {c : capability.Cap} {fin : Bool} (ht : TrivKind σ c fin) : TrivKind σ' c fin := by
  cases c <;> simp only [TrivKind] at ht ⊢ <;> first | trivial | exact ⟨ht.1, by rw [h]; exact ht.2⟩

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- The scope of `cnode_other_refines`, at the slot the target lookup
finds: Revoke of a slot with a cap and no children; Delete of an empty or
trivially finalised slot; CancelBadgedSends of anything but a full-rights
endpoint cap with a non-zero badge. -/
def OtherTriv (lbl : U64) (s : S) (σ : Fl4Spec.State Unit) (dsl : Fl4Spec.CslotPtr) : Prop :=
  ∃ c, capAt (L.mem s) (cslotAddr dsl) = ok c ∧
    (lbl.val = 25 → c ≠ .Null ∧ ¬ ∃ x, σ.cdt x = some dsl) ∧
    (lbl.val = 26 → c = .Null ∨
      ∃ fin, cdt.is_final_capability st s (cslotAddr dsl) = ok fin ∧ TrivKind σ c fin) ∧
    (lbl.val = 27 → ∀ p b, c = .Endpoint p b true true true true → b = 0#u64)


/-- **FL4's CNode Revoke, Delete and CancelBadgedSends refine l4v's** (labels
25..27), within `OtherTriv` at the slot the target lookup finds: the same
error as `decode_cnode_invocation` with the state unchanged, or the spec's
invocation, after which `set_thread_state Restart` and `invoke_cnode` end
in a state related to FL4's. -/
theorem cnode_other_refines {A : Type} (arI : machine.Arch A) (th : TypedHeap) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = cnodeLabelOf lbl)
    (hl : 25 ≤ lbl.val ∧ lbl.val ≤ 27)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (cap : capability.Cap) (a : Fl4Spec.Cap) (hca : CapRel cap a) (hcv : CapValid th cap)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List Fl4Spec.Cap)
    (hI : MdbInv (L.mem s) G)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hT : ∀ y0 y1 rest dsl, args = y0 :: y1 :: rest →
      (Fl4Spec.lookupTargetSlot (Z := Unit) a (Fl4Spec.dataToCptr y0.bv) (Fl4Spec.dataToNat y1.bv)).run σ =
        ({(.ok dsl, σ)}, False) → OtherTriv (L := L) lbl s σ dsl) :
    cnode.decode st arI s ar lbl length cap buf extra ⦃ res =>
      InvPost (L := L) th σ G (Fl4Spec.decodeCnodeInvocation slbl (args.map UScalar.bv) a excaps) s
        (res.1, res.2.1) ⦄ := by
  have hcases : lbl.val = 25 ∨ lbl.val = 26 ∨ lbl.val = 27 := by omega
  have hgl : IsOtherLabel (Fl4Spec.genInvocationType slbl) := by
    rw [hlbl]; unfold cnodeLabelOf IsOtherLabel
    rcases hcases with h | h | h <;> simp [h]
  have hmem := hgl.facts.1
  unfold cnode.decode
  have n1 : ¬ lbl < fl4_abi.label.CNodeRevoke := by have := lbl_revoke_val; scalar_tac
  have n2 : ¬ lbl > fl4_abi.label.CNodeRotate := by have := lbl_rotate_val; scalar_tac
  rw [if_neg n1, if_neg n2]
  by_cases h2 : length < 2#u64
  · rw [if_pos h2]
    simp only [error.truncated, bind_ok]
    rw [WP.spec_ok]
    exact ⟨rfl, .truncatedMessage, decode_short _ _ _ σ hmem _ (by simp; scalar_tac), trivial⟩
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
  have hdec := decode_lookup slbl a excaps hmem y0.bv y1.bv (rest.map UScalar.bv)
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
      obtain ⟨c, hc, h25, h26, h27⟩ := hT y0 y1 rest dsl rfl hlt
      have g1 : ¬ lbl ≥ fl4_abi.label.CNodeCopy := by have := lbl_copy_val; scalar_tac
      simp only [g1, ↓reduceIte, bind_ok]
      have hAd : AbsSlot th dsl := ⟨pd, hpd1, Or.inl hpd⟩
      obtain ⟨c', ad, hc', hcad, hgd⟩ := hR.slot_cap (Z := Unit) hpd1 hpd
      rw [hc] at hc'
      have : c' = c := by simpa using hc'.symm
      subst this
      -- `set_thread_state`, on both sides
      have hts := set_thread_state_slots th hP s ct sched.TS_RESTART htcb hact
      obtain ⟨s2, hs2, hS⟩ := spec_exists hts
      obtain ⟨tcb, hk, -⟩ := hR.tcb ct htcb
      rw [← hcur] at hk
      obtain ⟨σ1, hst, hR1, hV1, hM1, hC1, hcdt1, -⟩ := restart_rel hR hV hM hC hS hk .restart
      obtain ⟨σ1', hst', hk1, -, -⟩ := setThreadState_eq σ _ tcb hk .restart
      have hσ : σ1' = σ1 := by
        have := hst'.symm.trans hst
        simpa using this
      subst hσ
      have hfin1 : ∀ x, Fl4Spec.isFinalCap' x σ1' ↔ Fl4Spec.isFinalCap' x σ := isFinalCap'_tcb_state hk hk1
      have hc2 : capAt (L.mem s2) (cslotAddr dsl) = ok c' := by rw [hS.capAt hAd.isSlot, hc]
      obtain ⟨c2, a2, hc2', hca2, hgd2⟩ := hR1.slot_cap (Z := Unit) hpd1 hpd
      rw [hc2] at hc2'
      have : c2 = c' := by simpa using hc2'.symm
      subst this
      rcases hcases with hv | hv | hv
      · -- Revoke
        have hg : Fl4Spec.genInvocationType slbl = .cnodeRevoke := by rw [hlbl]; simp [cnodeLabelOf, hv]
        have e : lbl = fl4_abi.label.CNodeRevoke := by rw [u64_eq_iff]; simp [hv]
        rw [if_pos e, hs2]; simp only [bind_ok]
        obtain ⟨hcn, hnc⟩ := h25 hv
        have hx : cslotAddr dsl ∈ G.chains.flatten := (hM.members _).2 ⟨hAd.isSlot, c2, hc, hcn⟩
        have hng : ¬ ∃ y, G.par y = some (cslotAddr dsl) := fun h => hnc ((hC.has_child_iff hP hAd).2 h)
        rw [revoke_none arI th hP s2 ar G hM1 ((MdbInv.of_same hM hI hS).parentAdj (th := th)) hx hng, WP.spec_ok]
        refine ⟨.revokeCall dsl, ?_, σ1', hst, σ1', G, ?_, hR1, hV1, hM1, hC1, MdbInv.of_same hM hI hS⟩
        · rw [run_bind_ok hlt, copyTail_revoke _ _ _ _ hg]; rfl
        · exact capRevoke_none dsl σ1' hgd2 (by rw [hcdt1]; exact hnc)
      · -- Delete
        have hg : Fl4Spec.genInvocationType slbl = .cnodeDelete := by rw [hlbl]; simp [cnodeLabelOf, hv]
        have e1 : ¬ lbl = fl4_abi.label.CNodeRevoke := by rw [u64_eq_iff]; simp [hv]
        have e : lbl = fl4_abi.label.CNodeDelete := by rw [u64_eq_iff]; simp [hv]
        rw [if_neg e1, if_pos e, hs2]; simp only [bind_ok]
        obtain ⟨da, db⟩ := dsl
        simp only at hpd1 hpd; subst hpd1
        have ht2 : c2 = .Null ∨ ∃ fin, cdt.is_final_capability st s2 (cslotAddr (pd.bv, db)) = ok fin ∧
            TrivKind σ1' c2 fin := by
          rcases h26 hv with h | ⟨fin, hf, htk⟩
          · exact Or.inl h
          · right
            have hcn : c2 ≠ .Null := by intro e; subst e; simp [TrivKind] at htk
            have hx : cslotAddr (pd.bv, db) ∈ G.chains.flatten := (hM.members _).2 ⟨hAd.isSlot, c2, hc, hcn⟩
            have hslot : ∀ y, y ∈ G.chains.flatten → IsSlot th y := fun y h => ((hM.members y).1 h).1
            have hp : prevOf (L.mem s) (cslotAddr (pd.bv, db)) = 0#u64 ∨
                IsSlot th (prevOf (L.mem s) (cslotAddr (pd.bv, db))) := by
              by_cases h0 : prevOf (L.mem s) (cslotAddr (pd.bv, db)) = 0#u64
              · exact Or.inl h0
              · exact Or.inr (hslot _ (hM.prev_link hx h0).1)
            have hn : nextOf (L.mem s) (cslotAddr (pd.bv, db)) = 0#u64 ∨
                IsSlot th (nextOf (L.mem s) (cslotAddr (pd.bv, db))) := by
              rcases hM.next_mem hx with h | ⟨h, -⟩
              · exact Or.inl h
              · exact Or.inr (hslot _ h)
            exact ⟨fin, by rw [is_final_same hS hAd.isSlot hp hn, hf], htk.of_iff hfin1⟩
        obtain ⟨⟨r3, s3, a3⟩, hd3, hok, σ', G', hcd, hR', hV', hM', hC', hI'⟩ := spec_exists
          (delete_refines arI th s2 ar σ1' G hR1 hV1 hP hM1 hC1 (MdbInv.of_same hM hI hS) hpd rfl hc2 ht2)
        simp only at hok hR' hV' hM' hC'
        subst hok
        rw [hd3, WP.spec_ok]
        refine ⟨.deleteCall (pd.bv, db), ?_, σ1', hst, σ', G', hcd, hR', hV', hM', hC', hI'⟩
        rw [run_bind_ok hlt, copyTail_delete _ _ _ _ hg]; rfl
      · -- CancelBadgedSends
        have hg : Fl4Spec.genInvocationType slbl = .cnodeCancelBadgedSends := by
          rw [hlbl]; simp [cnodeLabelOf, hv]
        have e1 : ¬ lbl = fl4_abi.label.CNodeRevoke := by rw [u64_eq_iff]; simp [hv]
        have e2 : ¬ lbl = fl4_abi.label.CNodeDelete := by rw [u64_eq_iff]; simp [hv]
        have e : lbl = fl4_abi.label.CNodeCancelBadgedSends := by rw [u64_eq_iff]; simp [hv]
        rw [if_neg e1, if_neg e2, if_pos e]
        unfold cnode.decode_cancel_badged_sends
        obtain ⟨o, ho, hoe, hos⟩ := full_endpoint_rel c2
        simp only [slot_cap_eq, hc, bind_ok, ho]
        rw [hcad.abs] at hgd
        have hsp : (copyTail slbl (rest.map UScalar.bv) excaps dsl).run σ =
            (Fl4Spec.NonDetE.unlessE (Fl4Spec.hasCancelSendRights (absCap c2))
              (Fl4Spec.NonDetE.throwError .illegalOperation) >>= fun _ =>
              Fl4Spec.NonDetE.returnOk (Fl4Spec.CnodeInvocation.cancelBadgedSendsCall (absCap c2))).run σ := by
          rw [copyTail_cancel _ _ _ _ hg, run_bind_ok (run_liftE hgd)]
        cases o with
        | none =>
          have hn : ¬ Fl4Spec.hasCancelSendRights (absCap c2) := by simp [hos]
          simp only [error.illegal, bind_ok, uncurry_apply_pair]
          rw [WP.spec_ok]
          refine ⟨rfl, .illegalOperation, ?_, trivial⟩
          rw [run_bind_ok hlt, hsp]
          simp only [Fl4Spec.NonDetE.unlessE, hn, ↓reduceIte, Fl4Spec.NonDetE.throwError, ndE_throw_bind]; rfl
        | some pb =>
          obtain ⟨p, b⟩ := pb
          have hce := (hoe p b).1 rfl
          have hb0 := h27 hv p b hce
          subst hce hb0
          have hy : Fl4Spec.hasCancelSendRights (absCap (.Endpoint p 0#u64 true true true true)) := by simp [hos]
          simp only [uncurry_apply_pair, hct, bind_ok, hs2, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
          rw [WP.spec_ok]
          refine ⟨.cancelBadgedSendsCall (absCap (.Endpoint p 0#u64 true true true true)), ?_, σ1', hst,
            σ1', G, ?_, hR1, hV1, hM1, hC1, MdbInv.of_same hM hI hS⟩
          · rw [run_bind_ok hlt, hsp]
            simp only [Fl4Spec.NonDetE.unlessE, hy, ↓reduceIte, ndE_pure_bind]; rfl
          · show (Fl4Spec.invokeCnode (Z := Unit) (.cancelBadgedSendsCall
              (.endpointCap p.bv (0#u64 : U64).bv (rightsOf true true true true)))).run σ1' = _
            unfold Fl4Spec.invokeCnode Fl4Spec.withoutPreemption
            simp only [Fl4Spec.NonDet.when]
            have : ¬ ((0#u64 : U64).bv ≠ 0) := by simp
            simp only [this, ↓reduceIte]
            exact run_liftE rfl

end

end

end Fl4Proofs.P3
