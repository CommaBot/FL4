/-
P3 (DESIGN.md §9), CSpace: **`cap_revoke`** (FL4 `cdt::revoke`, a loop
over the MDB with fuel, deleting the next slot while it is a child, with
a preemption point after each delete) against l4v `cap_revoke` (the least
fixed point of `capRevokeF`: pick a descendant, `cap_delete` it,
`preemption_point`, recurse), and then **CNode Revoke**, decode and
invoke.

The spec is nondeterministic: which descendant it deletes next (for
`Z = Unit`, `select_ext` picks any), and whether its preemption points
preempt. FL4 is deterministic. The refinement is that FL4's outcome is one
of the spec's: Ok, or preempted, with related states.

The deletes of the children and the preemption points are hypotheses
(`DelHyp`, `RPPHyp`); `DelFull` discharges `DelHyp` for the measure
`psiD`. The fuel never runs out: each delete makes a measure `μ` of the
CSpace smaller (`DelHyp`), the preemption points keep the cap slots, and
`μ` starts below `WALK_FUEL` (`u64::MAX`).
-/
import Fl4Proofs.P3.CnodeOther
import Fl4Proofs.P3.UntypedResetSpec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-! ## Outcomes of the spec monads -/

section
variable {σ ε α β : Type}

theorem mem_bind_nd {m : Fl4Spec.NonDet σ α} {f : α → Fl4Spec.NonDet σ β} {s : σ} {x : α × σ} {y : β × σ}
    (hx : x ∈ (m s).1) (hy : y ∈ (f x.1 x.2).1) : y ∈ ((m >>= f) s).1 := by
  obtain ⟨z, hz, rfl⟩ := nhas_bind (m := m) (f := f) (s := s) (P := (· = y)) ⟨x, hx, y, hy, rfl⟩
  exact hz

theorem mem_bindE_ok {m : Fl4Spec.NonDetE σ ε α} {f : α → Fl4Spec.NonDetE σ ε β} {s s' : σ} {a : α}
    {y : Except ε β × σ} (hx : (.ok a, s') ∈ (m.run s).1) (hy : y ∈ ((f a).run s').1) :
    y ∈ ((m >>= f).run s).1 := by
  obtain ⟨z, hz, rfl⟩ := nhasE_bind (m := m) (f := f) (s := s) (P := (· = y))
    ⟨(.ok a, s'), hx, show Fl4Proofs.P3.NHas (f a).run s' (· = y) from ⟨y, hy, rfl⟩⟩
  exact hz

theorem mem_bindE_err {m : Fl4Spec.NonDetE σ ε α} {f : α → Fl4Spec.NonDetE σ ε β} {s s' : σ} {e : ε}
    (hx : (.error e, s') ∈ (m.run s).1) : (.error e, s') ∈ ((m >>= f).run s).1 := by
  obtain ⟨z, hz, rfl⟩ := nhasE_bind (m := m) (f := f) (s := s) (P := (· = (.error e, s')))
    ⟨(.error e, s'), hx, rfl⟩
  exact hz

theorem mem_of_run {m : Fl4Spec.NonDetE σ ε α} {s : σ} {y : Except ε α × σ} (h : m.run s = ({y}, False)) :
    y ∈ (m.run s).1 := by rw [h]; rfl

end

/-! ## Least fixed points -/

section
variable {σ α ι : Type}

theorem lfp_le_prefixed (F : (ι → Fl4Spec.NonDet σ α) → ι → Fl4Spec.NonDet σ α) (f : ι → Fl4Spec.NonDet σ α)
    (hf : ∀ k t, F f k t ≤ f k t) (i : ι) (s : σ) : Fl4Spec.NonDet.lfp F i s ≤ f i s := by
  let S := {f : ι → σ → Set (α × σ) × Prop | ∀ k t, F f k t ≤ f k t}
  have hl : Fl4Spec.NonDet.lfp F = (sInf S : ι → σ → Set (α × σ) × Prop) := rfl
  rw [hl]
  exact (sInf_le (show (f : ι → σ → Set (α × σ) × Prop) ∈ S from hf) : sInf S ≤ _) i s

/-- An outcome of `F f` at `(i, s)` for every pre-fixed point `f` is an
outcome of the least fixed point. -/
theorem lfp_mem (F : (ι → Fl4Spec.NonDet σ α) → ι → Fl4Spec.NonDet σ α) {i : ι} {s : σ} {x : α × σ}
    (h : ∀ f : ι → Fl4Spec.NonDet σ α, (∀ k t, F f k t ≤ f k t) → x ∈ (F f i s).1) :
    x ∈ (Fl4Spec.NonDet.lfp F i s).1 := by
  let S := {f : ι → σ → Set (α × σ) × Prop | ∀ k t, F f k t ≤ f k t}
  have hl : Fl4Spec.NonDet.lfp F = (sInf S : ι → σ → Set (α × σ) × Prop) := rfl
  let g : ι → σ → Set (α × σ) × Prop := fun k t => if k = i ∧ t = s then ({x}, False) else ⊥
  have hlow : g ≤ (sInf S : ι → σ → Set (α × σ) × Prop) := by
    apply le_sInf
    intro f hf k t
    by_cases h1 : k = i ∧ t = s
    · obtain ⟨rfl, rfl⟩ := h1
      simp only [g, and_self, ↓reduceIte]
      refine ⟨?_, fun h => h.elim⟩
      intro y hy
      rw [Set.mem_singleton_iff.1 hy]
      exact (hf k t).1 (h f hf)
    · simp only [g, h1, ↓reduceIte]; exact bot_le
  rw [hl]
  have := (hlow i s).1
  simp only [g, and_self, ↓reduceIte] at this
  exact this rfl

end

/-! ## The spec's `cap_revoke`, step by step -/

section
open Fl4Spec

theorem capRevoke_run (sl : CslotPtr) (σ : State Unit) :
    (capRevoke (Z := Unit) sl).run σ = NonDet.lfp (fun r c => capRevokeF (Z := Unit) r c) sl σ := rfl

theorem selectExt_mem {D : Type} (a : State DetExt → D) {A : Set D} {x : D} (hx : x ∈ A) (σ : State Unit) :
    (x, σ) ∈ (selectExt (Z := Unit) a A σ).1 := by
  unfold selectExt
  refine mem_bind_nd (x := (σ, σ)) rfl ?_
  refine mem_bind_nd (x := (x, σ)) ⟨hx, rfl⟩ ?_
  refine mem_bind_nd (x := ((), σ)) ⟨hx, rfl⟩ ?_
  rfl

/-- The stop case: a null cap, or no children. -/
theorem capRevokeF_stop (f : CslotPtr → NonDet (State Unit) (Except Unit Unit)) (sl : CslotPtr)
    (σ : State Unit) {a : Cap} (hg : getCap (Z := Unit) sl σ = ({(a, σ)}, False))
    (hn : a = .nullCap ∨ ¬ ∃ c, σ.cdt c = some sl) :
    (.ok (), σ) ∈ ((capRevokeF (Z := Unit) f sl).run σ).1 := by
  unfold capRevokeF withoutPreemption
  refine mem_bindE_ok (mem_of_run (run_liftE hg)) ?_
  refine mem_bindE_ok (mem_of_run (run_liftE (m := NonDet.gets fun s : State Unit => s.cdt) rfl)) ?_
  refine mem_bindE_ok (mem_of_run (run_returnOk _ σ)) ?_
  have : ¬ (a ≠ .nullCap ∧ descendantsOf sl σ.cdt ≠ ∅) := by
    rintro ⟨h1, h2⟩
    rcases hn with h | h
    · exact h1 h
    · exact h2 ((descendantsOf_empty_iff sl σ.cdt).2 h)
  simp only [NonDetE.whenE]
  rw [if_neg this]
  rfl

/-- The step: delete a child `child`, then the preemption point, then
the rest (`k`). -/
theorem capRevokeF_step (f : CslotPtr → NonDet (State Unit) (Except Unit Unit)) (sl child : CslotPtr)
    (σ : State Unit) {a ac : Cap} (hg : getCap (Z := Unit) sl σ = ({(a, σ)}, False)) (ha : a ≠ .nullCap)
    (hch : child ∈ descendantsOf sl σ.cdt) (hgc : getCap (Z := Unit) child σ = ({(ac, σ)}, False))
    (hac : ac ≠ .nullCap) {y : Except Unit Unit × State Unit}
    (hy : y ∈ ((capDelete (Z := Unit) child >>= fun _ => preemptionPoint >>= fun _ => f sl).run σ).1) :
    y ∈ ((capRevokeF (Z := Unit) f sl).run σ).1 := by
  unfold capRevokeF withoutPreemption
  refine mem_bindE_ok (mem_of_run (run_liftE hg)) ?_
  refine mem_bindE_ok (mem_of_run (run_liftE (m := NonDet.gets fun s : State Unit => s.cdt) rfl)) ?_
  refine mem_bindE_ok (mem_of_run (run_returnOk _ σ)) ?_
  have hne : descendantsOf sl σ.cdt ≠ ∅ := fun h => by rw [h] at hch; exact hch
  have : a ≠ .nullCap ∧ descendantsOf sl σ.cdt ≠ ∅ := ⟨ha, hne⟩
  simp only [NonDetE.whenE]
  rw [if_pos this]
  refine mem_bindE_ok (a := child) (s' := σ) ?_ ?_
  · rw [liftE_run]; exact mem_bind_nd (selectExt_mem _ hch σ) rfl
  refine mem_bindE_ok (mem_of_run (run_liftE hgc)) ?_
  refine mem_bindE_ok (a := ()) (s' := σ) ?_ hy
  rw [NonDetE.assertE, liftE_run]
  exact mem_bind_nd (x := ((), σ)) ⟨hac, rfl⟩ rfl

/-- **One round of `cap_revoke`**: from the deletion of a child and a
preemption point that do not preempt, an outcome of the rest is one of
`cap_revoke`'s. -/
theorem capRevoke_step {sl child : CslotPtr} {σ σd σp : State Unit} {a ac : Cap}
    (hg : getCap (Z := Unit) sl σ = ({(a, σ)}, False)) (ha : a ≠ .nullCap)
    (hch : child ∈ descendantsOf sl σ.cdt) (hgc : getCap (Z := Unit) child σ = ({(ac, σ)}, False))
    (hac : ac ≠ .nullCap) (hd : (.ok (), σd) ∈ ((capDelete (Z := Unit) child).run σ).1)
    (hp : (.ok (), σp) ∈ ((preemptionPoint (Z := Unit)).run σd).1) {x : Except Unit Unit × State Unit}
    (hx : x ∈ ((capRevoke (Z := Unit) sl).run σp).1) : x ∈ ((capRevoke (Z := Unit) sl).run σ).1 := by
  rw [capRevoke_run]
  refine lfp_mem _ fun f hf => capRevokeF_step f sl child σ hg ha hch hgc hac ?_
  refine mem_bindE_ok hd (mem_bindE_ok hp ?_)
  exact (lfp_le_prefixed _ f hf sl σp).1 hx

/-- The deletion of a child preempts. -/
theorem capRevoke_del_preempt {sl child : CslotPtr} {σ σd : State Unit} {a ac : Cap}
    (hg : getCap (Z := Unit) sl σ = ({(a, σ)}, False)) (ha : a ≠ .nullCap)
    (hch : child ∈ descendantsOf sl σ.cdt) (hgc : getCap (Z := Unit) child σ = ({(ac, σ)}, False))
    (hac : ac ≠ .nullCap) (hd : (.error (), σd) ∈ ((capDelete (Z := Unit) child).run σ).1) :
    (.error (), σd) ∈ ((capRevoke (Z := Unit) sl).run σ).1 := by
  rw [capRevoke_run]
  exact lfp_mem _ fun f _ => capRevokeF_step f sl child σ hg ha hch hgc hac (mem_bindE_err hd)

/-- The preemption point after the deletion of a child preempts. -/
theorem capRevoke_pp_preempt {sl child : CslotPtr} {σ σd σp : State Unit} {a ac : Cap}
    (hg : getCap (Z := Unit) sl σ = ({(a, σ)}, False)) (ha : a ≠ .nullCap)
    (hch : child ∈ descendantsOf sl σ.cdt) (hgc : getCap (Z := Unit) child σ = ({(ac, σ)}, False))
    (hac : ac ≠ .nullCap) (hd : (.ok (), σd) ∈ ((capDelete (Z := Unit) child).run σ).1)
    (hp : (.error (), σp) ∈ ((preemptionPoint (Z := Unit)).run σd).1) :
    (.error (), σp) ∈ ((capRevoke (Z := Unit) sl).run σ).1 := by
  rw [capRevoke_run]
  exact lfp_mem _ fun f _ => capRevokeF_step f sl child σ hg ha hch hgc hac (mem_bindE_ok hd (mem_bindE_err hp))

/-- `cap_revoke` stops at a null cap or a slot without children. -/
theorem capRevoke_stop {sl : CslotPtr} {σ : State Unit} {a : Cap}
    (hg : getCap (Z := Unit) sl σ = ({(a, σ)}, False)) (hn : a = .nullCap ∨ ¬ ∃ c, σ.cdt c = some sl) :
    (.ok (), σ) ∈ ((capRevoke (Z := Unit) sl).run σ).1 := by
  rw [capRevoke_run]
  exact lfp_mem _ fun f _ => capRevokeF_stop f sl σ hg hn

end

/-! ## The MDB and the spec's CDT -/

theorem srB_null (b : capability.Cap) : srB .Null b = false :=
  srB_of_eq (by unfold objects.same_region_as; rfl)

/-- A ghost parent link to a slot is a spec CDT link. -/
theorem cdt_of_par {Z : Type} {th : TypedHeap} {mem : U64 → U64} {σ : Fl4Spec.State Z} {G : MdbGhost}
    (hP : Placed th) (hC : CdtRel th mem σ G) {y : U64} {q : Fl4Spec.CslotPtr} (hq : AbsSlot th q)
    (h : G.par y = some (cslotAddr q)) : ∃ c, AbsSlot th c ∧ cslotAddr c = y ∧ σ.cdt c = some q := by
  obtain ⟨c, hcs, rfl⟩ := hC.par_slot _ _ h
  have h1 := hC.cdt c hcs
  rw [h] at h1
  cases hq' : σ.cdt c with
  | none => rw [hq'] at h1; cases h1
  | some q' =>
    rw [hq'] at h1
    have he : cslotAddr q' = cslotAddr q := by simpa using h1
    have := cslotAddr_inj hP (hC.cdt_slot c q' hq').2 hq he
    exact ⟨c, hcs, rfl, by rw [hq', this]⟩

/-- **A ghost descendant of a slot is a spec descendant.** -/
theorem ghost_desc {Z : Type} {th : TypedHeap} {mem : U64 → U64} {σ : Fl4Spec.State Z} {G : MdbGhost}
    (hP : Placed th) (hC : CdtRel th mem σ G) {sl : Fl4Spec.CslotPtr} (hs : AbsSlot th sl) {y : U64}
    (h : Mdb.Desc G.par y (cslotAddr sl)) :
    ∃ c, AbsSlot th c ∧ cslotAddr c = y ∧ c ∈ Fl4Spec.descendantsOf sl σ.cdt := by
  refine Relation.TransGen.head_induction_on (motive := fun y _ =>
    ∃ c, AbsSlot th c ∧ cslotAddr c = y ∧ c ∈ Fl4Spec.descendantsOf sl σ.cdt) h ?_ ?_
  · intro y hb
    obtain ⟨c, hcs, he, hcd⟩ := cdt_of_par hP hC hs hb
    exact ⟨c, hcs, he, Relation.TransGen.single hcd⟩
  · intro y b hab _ ih
    obtain ⟨cb, hcb, rfl, hd⟩ := ih
    obtain ⟨c, hcs, he, hcd⟩ := cdt_of_par hP hC hcb hab
    exact ⟨c, hcs, he, Relation.TransGen.tail hd hcd⟩

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- The cap in any slot of the typed heap (a CNode's or a TCB's), on both
sides. -/
theorem StateRel.abs_cap {th : TypedHeap} {s : S} {σ : Fl4Spec.State Unit} (hR : StateRel th (L.mem s) σ)
    {sl : Fl4Spec.CslotPtr} (hs : AbsSlot th sl) :
    ∃ c a, capAt (L.mem s) (cslotAddr sl) = ok c ∧ CapRel c a ∧
      Fl4Spec.getCap (Z := Unit) sl σ = ({(a, σ)}, False) := by
  obtain ⟨p, h1, h2 | ⟨ht, i, hi, hidx⟩⟩ := hs
  · exact hR.slot_cap (Z := Unit) h1 h2
  · obtain ⟨tcb, hk, hsl⟩ := hR.tcb p ht
    obtain ⟨c, a, hc, ha, hca⟩ := hsl i hi
    obtain ⟨o, idx⟩ := sl
    simp only at h1 hidx; subst h1 hidx
    have he : cslotAddr (p.bv, Fl4Spec.tcbCnodeIndex i) = slotOf p i := by
      show slotAddr p.bv (Fl4Spec.ofBl _) = _
      rw [slotAddr_ofBl, tcbCnodeIndex_blVal i hi]
    refine ⟨c, a, by rw [he]; exact hc, hca, ?_⟩
    have ho : Fl4Spec.getObject (Z := Unit) p.bv σ = ({(.tcb tcb, σ)}, False) := by
      simp [Fl4Spec.getObject, Fl4Spec.NonDet.getsThe, Fl4Spec.readObject, hk, Fl4Spec.NonDet.assertOpt]; rfl
    unfold Fl4Spec.getCap
    show (Fl4Spec.getObject _ >>= _) σ = _
    rw [nd_bind_one ho]
    show (Fl4Spec.NonDet.pure (Fl4Spec.tcbCnodeMap tcb) >>= fun caps => Fl4Spec.NonDet.assertOpt _) σ = _
    rw [nd_bind_one (show Fl4Spec.NonDet.pure (Fl4Spec.tcbCnodeMap tcb) σ = ({(_, σ)}, False) from rfl), ha]
    rfl

end

/-! ## FL4's `revoke` loop -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- The CSpace relations, bundled. -/
def CRel (th : TypedHeap) (mem : U64 → U64) (σ : Fl4Spec.State Unit) (G : MdbGhost) : Prop :=
  StateRel th mem σ ∧ SlotsValid th mem ∧ MdbLinks th mem G ∧ CdtRel th mem σ G ∧ MdbInv mem G

/-- **Hypothesis on FL4's `delete`** (exposed) of a slot of the MDB, from
related states with a property `E` (any further invariant the deletion
needs): Ok, with an `Ok` outcome of the spec's `cap_delete` and a smaller
measure `μ`, or preempted, with a preempted outcome; the states related,
`E` kept. -/
def DelHyp (μ : (U64 → U64) → MdbGhost → Nat) (th : TypedHeap) (E : S → Fl4Spec.State Unit → Prop) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (c : Fl4Spec.CslotPtr),
    CRel th (L.mem s) σ G → E s σ → AbsSlot th c → cslotAddr c ∈ G.chains.flatten →
    cdt.delete st arI s a (cslotAddr c) true ⦃ r => ∃ σ' G',
      ((r.1 = .Ok () ∧ (.ok (), σ') ∈ ((Fl4Spec.capDelete (Z := Unit) c).run σ).1 ∧
          μ (L.mem r.2.1) G' < μ (L.mem s) G) ∨
        (r.1 = .Err .Preempted ∧ (.error (), σ') ∈ ((Fl4Spec.capDelete (Z := Unit) c).run σ).1)) ∧
      CRel th (L.mem r.2.1) σ' G' ∧ E r.2.1 σ' ∧ MdbStep (L.mem s) G (L.mem r.2.1) G' ⦄

/-- **Hypothesis on FL4's preemption point** (the scheduler's): Ok with a
non-preempting outcome of the spec's, or preempted with a preempting one;
the cap slots, the CSpace relations and `E` kept. -/
def RPPHyp (th : TypedHeap) (E : S → Fl4Spec.State Unit → Prop) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost), CRel th (L.mem s) σ G → E s σ →
    sched.preemption_point st arI s a ⦃ r => SlotsSame th (L.mem s) (L.mem r.2.1) ∧ ∃ σ',
      ((r.1 = .Ok () ∧ (.ok (), σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1) ∨
        (r.1 = .Err .Preempted ∧ (.error (), σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1)) ∧
      CRel th (L.mem r.2.1) σ' G ∧ E r.2.1 σ' ⦄

/-- What `revoke` ends with: an outcome of the spec's `cap_revoke` of the
same kind (Ok or preempted), with related states. -/
def RevPost (th : TypedHeap) (E : S → Fl4Spec.State Unit → Prop) (sl : Fl4Spec.CslotPtr)
    (σ : Fl4Spec.State Unit) (m0 : U64 → U64) (G0 : MdbGhost) (res : core.result.Result Unit error.Exc × S × A) : Prop :=
  ∃ σ' G', ((res.1 = .Ok () ∧ (.ok (), σ') ∈ ((Fl4Spec.capRevoke (Z := Unit) sl).run σ).1) ∨
      (res.1 = .Err .Preempted ∧ (.error (), σ') ∈ ((Fl4Spec.capRevoke (Z := Unit) sl).run σ).1)) ∧
    CRel th (L.mem res.2.1) σ' G' ∧ E res.2.1 σ' ∧ MdbStep m0 G0 (L.mem res.2.1) G'

/-- **`DelHyp` with an invariant `E` that sees the arch state and the ghost
tree** (the W-threading: `DelHyp` is the instance ignoring them). -/
def DelHypW (μ : (U64 → U64) → MdbGhost → Nat) (th : TypedHeap)
    (E : S → A → Fl4Spec.State Unit → MdbGhost → Prop) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (c : Fl4Spec.CslotPtr),
    CRel th (L.mem s) σ G → E s a σ G → AbsSlot th c → cslotAddr c ∈ G.chains.flatten →
    cdt.delete st arI s a (cslotAddr c) true ⦃ r => ∃ σ' G',
      ((r.1 = .Ok () ∧ (.ok (), σ') ∈ ((Fl4Spec.capDelete (Z := Unit) c).run σ).1 ∧
          μ (L.mem r.2.1) G' < μ (L.mem s) G) ∨
        (r.1 = .Err .Preempted ∧ (.error (), σ') ∈ ((Fl4Spec.capDelete (Z := Unit) c).run σ).1)) ∧
      CRel th (L.mem r.2.1) σ' G' ∧ E r.2.1 r.2.2 σ' G' ∧ MdbStep (L.mem s) G (L.mem r.2.1) G' ⦄

/-- **`RPPHyp` with an invariant `E` that sees the arch state and the ghost
tree.** -/
def RPPHypW (th : TypedHeap) (E : S → A → Fl4Spec.State Unit → MdbGhost → Prop) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost), CRel th (L.mem s) σ G → E s a σ G →
    sched.preemption_point st arI s a ⦃ r => SlotsSame th (L.mem s) (L.mem r.2.1) ∧ ∃ σ',
      ((r.1 = .Ok () ∧ (.ok (), σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1) ∨
        (r.1 = .Err .Preempted ∧ (.error (), σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1)) ∧
      CRel th (L.mem r.2.1) σ' G ∧ E r.2.1 r.2.2 σ' G ⦄

/-- `RevPost` with `E` seeing the arch state and the ghost tree. -/
def RevPostW (th : TypedHeap) (E : S → A → Fl4Spec.State Unit → MdbGhost → Prop) (sl : Fl4Spec.CslotPtr)
    (σ : Fl4Spec.State Unit) (m0 : U64 → U64) (G0 : MdbGhost) (res : core.result.Result Unit error.Exc × S × A) :
    Prop :=
  ∃ σ' G', ((res.1 = .Ok () ∧ (.ok (), σ') ∈ ((Fl4Spec.capRevoke (Z := Unit) sl).run σ).1) ∨
      (res.1 = .Err .Preempted ∧ (.error (), σ') ∈ ((Fl4Spec.capRevoke (Z := Unit) sl).run σ).1)) ∧
    CRel th (L.mem res.2.1) σ' G' ∧ E res.2.1 res.2.2 σ' G' ∧ MdbStep m0 G0 (L.mem res.2.1) G'

theorem DelHyp.w {μ : (U64 → U64) → MdbGhost → Nat} {th : TypedHeap} {E : S → Fl4Spec.State Unit → Prop}
    (h : DelHyp (L := L) arI μ th E) : DelHypW (L := L) arI μ th (fun s _ σ _ => E s σ) := h

theorem RPPHyp.w {th : TypedHeap} {E : S → Fl4Spec.State Unit → Prop}
    (h : RPPHyp (L := L) arI th E) : RPPHypW (L := L) arI th (fun s _ σ _ => E s σ) := h

/-- The revoke loop's invariant from `σ0`: related to a spec state `σ`
from which every outcome of `cap_revoke` is one from `σ0`, fuel above the
measure. -/
def RevInv (μ : (U64 → U64) → MdbGhost → Nat) (th : TypedHeap) (E : S → A → Fl4Spec.State Unit → MdbGhost → Prop)
    (sl : Fl4Spec.CslotPtr) (σ0 : Fl4Spec.State Unit) (m0 : U64 → U64) (G0 : MdbGhost) (x : S × A × U64) : Prop :=
  ∃ σ G, CRel th (L.mem x.1) σ G ∧ E x.1 x.2.1 σ G ∧ μ (L.mem x.1) G < x.2.2.val ∧ MdbStep m0 G0 (L.mem x.1) G ∧
    ∀ y, y ∈ ((Fl4Spec.capRevoke (Z := Unit) sl).run σ).1 → y ∈ ((Fl4Spec.capRevoke (Z := Unit) sl).run σ0).1

/-- **FL4's revoke loop refines l4v's `cap_revoke`**, with fuel above the
measure, with an invariant `E` (W-threading). -/
theorem revoke_loop_refinesW (th : TypedHeap) (hP : Placed th) (E : S → A → Fl4Spec.State Unit → MdbGhost → Prop)
    (μ : (U64 → U64) → MdbGhost → Nat)
    (hμ : ∀ m m' G, MdbLinks th m G → SlotsSame th m m' → μ m' G = μ m G)
    (hD : DelHypW (L := L) arI μ th E) (hPP : RPPHypW (L := L) arI th E)
    (sl : Fl4Spec.CslotPtr) (hs : AbsSlot th sl) (s : S) (a : A) (σ0 : Fl4Spec.State Unit) (G0 : MdbGhost)
    (fuel : U64) (hCR0 : CRel th (L.mem s) σ0 G0) (hE0 : E s a σ0 G0) (hlen0 : μ (L.mem s) G0 < fuel.val) :
    cdt.revoke_loop st arI s a (cslotAddr sl) fuel ⦃ res => RevPostW (L := L) th E sl σ0 (L.mem s) G0 res ⦄ := by
  obtain ⟨m0, hm0⟩ : ∃ m0, m0 = L.mem s := ⟨_, rfl⟩
  have hmS0 : MdbStep m0 G0 (L.mem s) G0 := by rw [hm0]; exact MdbStep.refl hCR0.2.2.1
  rw [← hm0]
  unfold cdt.revoke_loop
  refine loop.spec_decr_nat (fun x => x.2.2.val) (RevInv (L := L) μ th E sl σ0 m0 G0) _ _ _ ?_
    ⟨σ0, G0, hCR0, hE0, hlen0, hmS0, fun _ h => h⟩
  rintro ⟨s, a, fuel⟩ ⟨σ, G, ⟨hR, hV, hM, hC, hI⟩, hE, hlen, hmS, htr⟩
  simp only at hlen htr ⊢
  unfold cdt.revoke_loop.body
  have hf : fuel > 0#u64 := by scalar_tac
  obtain ⟨fuel1, hv, hv1⟩ := spec_exists (U64.sub_spec (x := fuel) (y := 1#u64) (by scalar_tac))
  simp only [hf, ↓reduceIte, hv, bind_ok, slot_next_eq, obj.Slot.is_null]
  obtain ⟨c, ac, hc, hca, hg⟩ := hR.abs_cap hs
  have hCR : CRel th (L.mem s) σ G := ⟨hR, hV, hM, hC, hI⟩
  have stop : (ac = .nullCap ∨ ¬ ∃ c, σ.cdt c = some sl) →
      RevPostW (L := L) th E sl σ0 m0 G0 (core.result.Result.Ok (), s, a) := fun h =>
    ⟨σ, G, Or.inl ⟨rfl, htr _ (capRevoke_stop hg h)⟩, hCR, hE, hmS⟩
  by_cases hcn : c = .Null
  · subst hcn
    have hacn : ac = .nullCap := hca.null_iff.2 rfl
    by_cases h0 : nextOf (L.mem s) (cslotAddr sl) = 0#u64
    · simp only [h0, decide_true, ↓reduceIte, WP.spec_ok]
      exact stop (Or.inl hacn)
    · have hcv : capV (L.mem s) (cslotAddr sl) = .Null := by
        have := hc; rw [capAt_capV] at this; exact eq_of_ok_eq this
      simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte, is_mdb_parent_eq, hcv, isPF, srB_null,
        Bool.and_false, Bool.false_and, bind_ok, WP.spec_ok]
      exact stop (Or.inl hacn)
  have hx : cslotAddr sl ∈ G.chains.flatten := (hM.members _).2 ⟨hs.isSlot, c, hc, hcn⟩
  have hacn : ac ≠ .nullCap := fun h => hcn (hca.null_iff.1 h)
  have nochild : ¬ (nextOf (L.mem s) (cslotAddr sl) ≠ 0#u64 ∧
      Mdb.Desc G.par (nextOf (L.mem s) (cslotAddr sl)) (cslotAddr sl)) → ¬ ∃ c, σ.cdt c = some sl := by
    intro h hh
    exact h ((hM.has_child_iff hP hx).1 ((hC.has_child_iff hP hs).1 hh))
  by_cases h0 : nextOf (L.mem s) (cslotAddr sl) = 0#u64
  · simp only [h0, decide_true, ↓reduceIte, WP.spec_ok]
    exact stop (Or.inr (nochild fun h => h.1 h0))
  obtain ⟨b, hb, hbd⟩ := (hI.parentAdj (th := th)) _ hx h0
  simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte, hb, bind_ok]
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact stop (Or.inr (nochild fun h => by have := hbd.2 h.2; cases this))
  | true =>
  simp only [↓reduceIte]
  have hdesc := hbd.1 rfl
  obtain ⟨cd, hcd, hcde, hcdesc⟩ := ghost_desc hP hC hs hdesc
  have hnx : nextOf (L.mem s) (cslotAddr sl) ∈ G.chains.flatten := by
    rcases hM.next_mem hx with h | ⟨h, -⟩
    · exact absurd h h0
    · exact h
  obtain ⟨cc, acc, hcc, hcca, hgc⟩ := hR.abs_cap hcd
  have hccn : cc ≠ .Null := by
    obtain ⟨-, c', hc', hn'⟩ := (hM.members _).1 hnx
    rw [← hcde, hcc] at hc'; rw [eq_of_ok_eq hc']; exact hn'
  have haccn : acc ≠ .nullCap := fun h => hccn (hcca.null_iff.1 h)
  rw [← hcde]
  obtain ⟨⟨r, s1, a1⟩, hdl, σd, Gd, hcase, hCR1, hE1, hmD⟩ := spec_exists
    (hD s a σ G cd hCR hE hcd (by rw [hcde]; exact hnx))
  rw [hdl]
  simp only [bind_ok, uncurry_apply_pair]
  rcases hcase with ⟨rfl, hdm, hlt⟩ | ⟨rfl, hdm⟩
  swap
  · simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_ok, bind_tc_ok, WP.spec_ok]
    exact ⟨σd, Gd, Or.inr ⟨rfl, htr _ (capRevoke_del_preempt hg hacn hcdesc hgc haccn hdm)⟩, hCR1, hE1, hmS.trans hmD⟩
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨⟨r2, s2, a2⟩, hpp, hS2, σp, hcase2, hCR2, hE2⟩ := spec_exists (hPP s1 a1 σd Gd hCR1 hE1)
  have hμ2 : μ (L.mem s2) Gd = μ (L.mem s1) Gd := hμ _ _ _ hCR1.2.2.1 hS2
  rw [hpp]
  simp only [bind_ok, uncurry_apply_pair]
  rcases hcase2 with ⟨rfl, hpm⟩ | ⟨rfl, hpm⟩
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, WP.spec_ok]
    refine ⟨⟨σp, Gd, hCR2, hE2, by simp only at hμ2 hlt ⊢; rw [hμ2]; scalar_tac,
      (hmS.trans hmD).same_right hCR1.2.2.1 hS2, fun y hy => htr _ (capRevoke_step hg hacn hcdesc hgc haccn hdm hpm hy)⟩, by scalar_tac⟩
  · simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_ok, bind_tc_ok, WP.spec_ok]
    exact ⟨σp, Gd, Or.inr ⟨rfl, htr _ (capRevoke_pp_preempt hg hacn hcdesc hgc haccn hdm hpm)⟩, hCR2, hE2,
      (hmS.trans hmD).same_right hCR1.2.2.1 hS2⟩

/-- **FL4's revoke loop refines l4v's `cap_revoke`**, with fuel above the
measure. -/
theorem revoke_loop_refines (th : TypedHeap) (hP : Placed th) (E : S → Fl4Spec.State Unit → Prop)
    (μ : (U64 → U64) → MdbGhost → Nat)
    (hμ : ∀ m m' G, MdbLinks th m G → SlotsSame th m m' → μ m' G = μ m G)
    (hD : DelHyp (L := L) arI μ th E) (hPP : RPPHyp (L := L) arI th E)
    (sl : Fl4Spec.CslotPtr) (hs : AbsSlot th sl) (s : S) (a : A) (σ0 : Fl4Spec.State Unit) (G0 : MdbGhost)
    (fuel : U64) (hCR0 : CRel th (L.mem s) σ0 G0) (hE0 : E s σ0) (hlen0 : μ (L.mem s) G0 < fuel.val) :
    cdt.revoke_loop st arI s a (cslotAddr sl) fuel ⦃ res => RevPost (L := L) th E sl σ0 (L.mem s) G0 res ⦄ :=
  revoke_loop_refinesW arI th hP (fun s _ σ _ => E s σ) μ hμ (hD.w arI) (hPP.w arI) sl hs s a σ0 G0 fuel hCR0 hE0
    hlen0

/-- **FL4's `revoke` refines l4v's `cap_revoke`**, given the measure below
`WALK_FUEL` (`u64::MAX`), with an invariant `E` (W-threading). -/
theorem revoke_refinesW (th : TypedHeap) (hP : Placed th) (E : S → A → Fl4Spec.State Unit → MdbGhost → Prop)
    (μ : (U64 → U64) → MdbGhost → Nat)
    (hμ : ∀ m m' G, MdbLinks th m G → SlotsSame th m m' → μ m' G = μ m G)
    (hD : DelHypW (L := L) arI μ th E) (hPP : RPPHypW (L := L) arI th E)
    (sl : Fl4Spec.CslotPtr) (hs : AbsSlot th sl) (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hCR : CRel th (L.mem s) σ G) (hE : E s a σ G) (hfew : μ (L.mem s) G < 2 ^ 64 - 1) :
    cdt.revoke st arI s a (cslotAddr sl) ⦃ res => RevPostW (L := L) th E sl σ (L.mem s) G res ⦄ := by
  unfold cdt.revoke
  have : layout.WALK_FUEL.val = 2 ^ 64 - 1 := by simp [layout.WALK_FUEL, U64.rMax]
  exact revoke_loop_refinesW arI th hP E μ hμ hD hPP sl hs s a σ G _ hCR hE (by rw [this]; exact hfew)

/-- **FL4's `revoke` refines l4v's `cap_revoke`**, given the measure below
`WALK_FUEL` (`u64::MAX`). -/
theorem revoke_refines (th : TypedHeap) (hP : Placed th) (E : S → Fl4Spec.State Unit → Prop)
    (μ : (U64 → U64) → MdbGhost → Nat)
    (hμ : ∀ m m' G, MdbLinks th m G → SlotsSame th m m' → μ m' G = μ m G)
    (hD : DelHyp (L := L) arI μ th E) (hPP : RPPHyp (L := L) arI th E)
    (sl : Fl4Spec.CslotPtr) (hs : AbsSlot th sl) (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hCR : CRel th (L.mem s) σ G) (hE : E s σ) (hfew : μ (L.mem s) G < 2 ^ 64 - 1) :
    cdt.revoke st arI s a (cslotAddr sl) ⦃ res => RevPost (L := L) th E sl σ (L.mem s) G res ⦄ :=
  revoke_refinesW arI th hP (fun s _ σ _ => E s σ) μ hμ (hD.w arI) (hPP.w arI) sl hs s a σ G hCR hE hfew

/-! ## CNode Revoke, decode and invoke -/

/-- The outcome of a preemptible CNode invocation (Revoke, Delete) against a spec decode `m`: the same
error with the state unchanged, or the invocation, after which (with
`set_thread_state Restart` first) `invoke_cnode` has an outcome of the
same kind as FL4's (Ok, or preempted) in a related state, with `FinInv`, and
the `MdbStep` from `G` taken. -/
def PInvPost (th : TypedHeap) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (m : Fl4Spec.SEMonad Unit Fl4Spec.CnodeInvocation)
    (s : S) : core.result.Result Unit error.Exc × S → Prop
  | (r, s') => (∃ e, r = .Err e ∧ s' = s ∧ ∃ e', m.run σ = ({(.error e', σ)}, False) ∧ SysErrRel e e') ∨
      ∃ inv, m.run σ = ({(.ok inv, σ)}, False) ∧ ∃ σ1,
        Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧ ∃ σ' G',
          ((r = .Ok () ∧ (.ok (), σ') ∈ ((Fl4Spec.invokeCnode (Z := Unit) inv).run σ1).1) ∨
            (r = .Err .Preempted ∧ (.error (), σ') ∈ ((Fl4Spec.invokeCnode (Z := Unit) inv).run σ1).1)) ∧
          CRel th (L.mem s') σ' G' ∧ FinInv th (L.mem s') σ' G' ∧
          MdbStep (L.mem s) G (L.mem s') G'

/-- `PInvPost` with the arch state and an invariant `E` after: the error
with the state and arch state unchanged, or the invocation's outcome with
`E` (W-threading). -/
def PInvPostW (th : TypedHeap) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (m : Fl4Spec.SEMonad Unit Fl4Spec.CnodeInvocation) (E : S → A → Fl4Spec.State Unit → MdbGhost → Prop)
    (s : S) (ar : A) : core.result.Result Unit error.Exc × S × A → Prop
  | (r, s', a') => (∃ e, r = .Err e ∧ s' = s ∧ a' = ar ∧ ∃ e', m.run σ = ({(.error e', σ)}, False) ∧ SysErrRel e e') ∨
      ∃ inv, m.run σ = ({(.ok inv, σ)}, False) ∧ ∃ σ1,
        Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧ ∃ σ' G',
          ((r = .Ok () ∧ (.ok (), σ') ∈ ((Fl4Spec.invokeCnode (Z := Unit) inv).run σ1).1) ∨
            (r = .Err .Preempted ∧ (.error (), σ') ∈ ((Fl4Spec.invokeCnode (Z := Unit) inv).run σ1).1)) ∧
          CRel th (L.mem s') σ' G' ∧ FinInv th (L.mem s') σ' G' ∧
          MdbStep (L.mem s) G (L.mem s') G' ∧ E s' a' σ' G'

theorem PInvPostW.toP {th : TypedHeap} {σ : Fl4Spec.State Unit} {G : MdbGhost}
    {m : Fl4Spec.SEMonad Unit Fl4Spec.CnodeInvocation} {E : S → A → Fl4Spec.State Unit → MdbGhost → Prop}
    {s : S} {ar : A} {res : core.result.Result Unit error.Exc × S × A}
    (h : PInvPostW (L := L) th σ G m E s ar res) : PInvPost (L := L) th σ G m s (res.1, res.2.1) := by
  obtain ⟨r, s', a'⟩ := res
  rcases h with ⟨e, h1, h2, -, h3⟩ | ⟨inv, h1, σ1, h2, σ', G', h3, h4, h5, h6, -⟩
  · exact Or.inl ⟨e, h1, h2, h3⟩
  · exact Or.inr ⟨inv, h1, σ1, h2, σ', G', h3, h4, h5, h6⟩

/-- `delete` of an empty slot does nothing. -/
theorem delete_null_ok (σ : Fl4Spec.State Unit) (s : S) (a : A) (x : U64) (hc : capAt (L.mem s) x = ok .Null) :
    cdt.delete st arI s a x true = ok (.Ok (), s, a) := by
  unfold cdt.delete
  simp only [↓reduceIte]
  rw [finalise_imm_triv arI σ s a _ .Null hc (Or.inl rfl)]
  simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch, uncurry_apply_pair]
  rw [empty_slot_null arI s a _ hc]
  simp only [bind_ok]; rfl

/-- **CNode Revoke at an invariant `E`** (W-threading), decode and invoke: FL4's `cnode::decode` at label
`CNodeRevoke` against l4v's `decode_cnode_invocation`, then
`set_thread_state Restart` and `invoke_cnode` (`cap_revoke`), given the
deletes and preemption points (`DelHyp`, `RPPHyp`, with an invariant `E`
that holds after the restart) and a measure `μ` of the CSpace below
`u64::MAX`. -/
theorem cnode_revoke_refinesW (th : TypedHeap) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .cnodeRevoke)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (cap : capability.Cap) (a : Fl4Spec.Cap) (hca : CapRel cap a) (hcv : CapValid th cap)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List Fl4Spec.Cap)
    (hI : MdbInv (L.mem s) G)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (E : S → A → Fl4Spec.State Unit → MdbGhost → Prop) (μ : (U64 → U64) → MdbGhost → Nat)
    (hμ : ∀ m m' G, MdbLinks th m G → SlotsSame th m m' → μ m' G = μ m G)
    (hD : DelHypW (L := L) arI μ th E) (hPP : RPPHypW (L := L) arI th E)
    (hE : ∀ s1 σ1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 → SlotsSame th (L.mem s) (L.mem s1) →
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) → E s1 ar σ1 G)
    (hEF : ∀ s1 a1 σ1 G1, CRel th (L.mem s1) σ1 G1 → E s1 a1 σ1 G1 → FinInv th (L.mem s1) σ1 G1)
    (hfew : μ (L.mem s) G < 2 ^ 64 - 1) :
    cnode.decode st arI s ar fl4_abi.label.CNodeRevoke length cap buf extra ⦃ res =>
      PInvPostW (L := L) th σ G (Fl4Spec.decodeCnodeInvocation slbl (args.map UScalar.bv) a excaps) E s ar res ⦄ := by
  have hin : Fl4Spec.genInvocationType slbl ∈
      Fl4Spec.GenInvocationLabels.uptoEnum .cnodeRevoke .cnodeRotate := by rw [hlbl]; decide
  unfold cnode.decode
  have n1 : ¬ fl4_abi.label.CNodeRevoke < fl4_abi.label.CNodeRevoke := by scalar_tac
  have n2 : ¬ fl4_abi.label.CNodeRevoke > fl4_abi.label.CNodeRotate := by
    have := lbl_revoke_val; have := lbl_rotate_val; scalar_tac
  rw [if_neg n1, if_neg n2]
  by_cases h2 : length < 2#u64
  · rw [if_pos h2]
    simp only [error.truncated, bind_ok]
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, rfl, .truncatedMessage, decode_short _ _ _ σ hin _ (by simp; scalar_tac), trivial⟩
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
  have hdec := decode_lookup slbl a excaps hin y0.bv y1.bv (rest.map UScalar.bv)
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
      exact Or.inl ⟨_, rfl, rfl, rfl, e', run_bind_error hlt _, hrel1⟩
  | Ok dest =>
    cases e1 with
    | error _ => exact hrel1.elim
    | ok dsl =>
      obtain ⟨rfl, pd, hpd1, hpd, -⟩ := hrel1
      have g1 : ¬ fl4_abi.label.CNodeRevoke ≥ fl4_abi.label.CNodeCopy := by
        have := lbl_copy_val; have := lbl_revoke_val; scalar_tac
      simp only [g1, ↓reduceIte, bind_ok]
      have hAd : AbsSlot th dsl := ⟨pd, hpd1, Or.inl hpd⟩
      -- `set_thread_state`, on both sides
      have hts := set_thread_state_slots th hP s ct sched.TS_RESTART htcb hact
      obtain ⟨s2, hs2, hS⟩ := spec_exists hts
      obtain ⟨tcb, hk, -⟩ := hR.tcb ct htcb
      rw [← hcur] at hk
      obtain ⟨σ1, hst, hR1, hV1, hM1, hC1, -, -⟩ := restart_rel hR hV hM hC hS hk .restart
      have hI1 := MdbInv.of_same hM hI hS
      rw [hs2]; simp only [bind_ok]
      have hfew' : μ (L.mem s2) G < 2 ^ 64 - 1 := by rw [hμ _ _ _ hM hS]; exact hfew
      refine WP.spec_mono (revoke_refinesW arI th hP E μ hμ hD hPP dsl hAd s2 ar σ1 G ⟨hR1, hV1, hM1, hC1, hI1⟩
        (hE s2 σ1 hs2 hS hst) hfew') ?_
      rintro ⟨r, s', a'⟩ ⟨σ', G', hk', hCR', hE', hmR⟩
      refine Or.inr ⟨.revokeCall dsl, ?_, σ1, hst, σ', G', ?_, hCR', hEF _ _ _ _ hCR' hE',
        (MdbStep.same_left hM hS hmR), hE'⟩
      · rw [run_bind_ok hlt, copyTail_revoke _ _ _ _ hlbl]; rfl
      · exact hk'

/-- **CNode Revoke**, decode and invoke (`cnode_revoke_refinesW` with `E`
ignoring the arch state and the ghost tree). -/
theorem cnode_revoke_refines (th : TypedHeap) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .cnodeRevoke)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (cap : capability.Cap) (a : Fl4Spec.Cap) (hca : CapRel cap a) (hcv : CapValid th cap)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List Fl4Spec.Cap)
    (hI : MdbInv (L.mem s) G)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (E : S → Fl4Spec.State Unit → Prop) (μ : (U64 → U64) → MdbGhost → Nat)
    (hμ : ∀ m m' G, MdbLinks th m G → SlotsSame th m m' → μ m' G = μ m G)
    (hD : DelHyp (L := L) arI μ th E) (hPP : RPPHyp (L := L) arI th E)
    (hE : ∀ s1 σ1, SlotsSame th (L.mem s) (L.mem s1) →
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) → E s1 σ1)
    (hEF : ∀ s1 σ1 G1, CRel th (L.mem s1) σ1 G1 → E s1 σ1 → FinInv th (L.mem s1) σ1 G1)
    (hfew : μ (L.mem s) G < 2 ^ 64 - 1) :
    cnode.decode st arI s ar fl4_abi.label.CNodeRevoke length cap buf extra ⦃ res =>
      PInvPost (L := L) th σ G (Fl4Spec.decodeCnodeInvocation slbl (args.map UScalar.bv) a excaps) s
        (res.1, res.2.1) ⦄ :=
  WP.spec_mono (cnode_revoke_refinesW arI th s ar σ G hR hV hP hM hC slbl hlbl length buf ct hct args hlen hargs cap
    a hca hcv extra excaps hI hact hcur htcb (fun s _ σ _ => E s σ) μ hμ (hD.w arI) (hPP.w arI)
    (fun s1 σ1 _ hS h => hE s1 σ1 hS h) (fun s1 _ σ1 G1 h1 h2 => hEF s1 σ1 G1 h1 h2) hfew) fun _ h => h.toP

/-- **CNode Delete at an invariant `E`** (W-threading), decode and invoke, for any cap: FL4's `cnode::decode`
at label `CNodeDelete` against l4v's `decode_cnode_invocation`, then
`set_thread_state Restart` and `invoke_cnode` (`cap_delete`). An empty
slot is `delete_refines`; any other cap is `DelHyp` (`cnode_other_refines`
covers the trivially finalised ones without it). -/
theorem cnode_delete_refinesW (th : TypedHeap) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .cnodeDelete)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (cap : capability.Cap) (a : Fl4Spec.Cap) (hca : CapRel cap a) (hcv : CapValid th cap)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List Fl4Spec.Cap)
    (hI : MdbInv (L.mem s) G)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (E : S → A → Fl4Spec.State Unit → MdbGhost → Prop) (μ : (U64 → U64) → MdbGhost → Nat)
    (hD : DelHypW (L := L) arI μ th E)
    (hE : ∀ s1 σ1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 → SlotsSame th (L.mem s) (L.mem s1) →
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) → E s1 ar σ1 G)
    (hEF : ∀ s1 a1 σ1 G1, CRel th (L.mem s1) σ1 G1 → E s1 a1 σ1 G1 → FinInv th (L.mem s1) σ1 G1) :
    cnode.decode st arI s ar fl4_abi.label.CNodeDelete length cap buf extra ⦃ res =>
      PInvPostW (L := L) th σ G (Fl4Spec.decodeCnodeInvocation slbl (args.map UScalar.bv) a excaps) E s ar res ⦄ := by
  have hin : Fl4Spec.genInvocationType slbl ∈
      Fl4Spec.GenInvocationLabels.uptoEnum .cnodeRevoke .cnodeRotate := by rw [hlbl]; decide
  unfold cnode.decode
  have n1 : ¬ fl4_abi.label.CNodeDelete < fl4_abi.label.CNodeRevoke := by
    have := lbl_revoke_val; have := lbl_delete_val; scalar_tac
  have n2 : ¬ fl4_abi.label.CNodeDelete > fl4_abi.label.CNodeRotate := by
    have := lbl_delete_val; have := lbl_rotate_val; scalar_tac
  rw [if_neg n1, if_neg n2]
  by_cases h2 : length < 2#u64
  · rw [if_pos h2]
    simp only [error.truncated, bind_ok]
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, rfl, .truncatedMessage, decode_short _ _ _ σ hin _ (by simp; scalar_tac), trivial⟩
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
  have hdec := decode_lookup slbl a excaps hin y0.bv y1.bv (rest.map UScalar.bv)
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
      exact Or.inl ⟨_, rfl, rfl, rfl, e', run_bind_error hlt _, hrel1⟩
  | Ok dest =>
    cases e1 with
    | error _ => exact hrel1.elim
    | ok dsl =>
      obtain ⟨rfl, pd, hpd1, hpd, -⟩ := hrel1
      have g1 : ¬ fl4_abi.label.CNodeDelete ≥ fl4_abi.label.CNodeCopy := by
        have := lbl_copy_val; have := lbl_delete_val; scalar_tac
      have k1 : ¬ fl4_abi.label.CNodeDelete = fl4_abi.label.CNodeRevoke := by rw [u64_eq_iff]; simp
      simp only [g1, k1, ↓reduceIte, bind_ok]
      have hAd : AbsSlot th dsl := ⟨pd, hpd1, Or.inl hpd⟩
      obtain ⟨c, ad, hc, hcad, -⟩ := hR.slot_cap (Z := Unit) hpd1 hpd
      -- `set_thread_state`, on both sides
      have hts := set_thread_state_slots th hP s ct sched.TS_RESTART htcb hact
      obtain ⟨s2, hs2, hS⟩ := spec_exists hts
      obtain ⟨tcb, hk, -⟩ := hR.tcb ct htcb
      rw [← hcur] at hk
      obtain ⟨σ1, hst, hR1, hV1, hM1, hC1, -, -⟩ := restart_rel hR hV hM hC hS hk .restart
      have hI1 := MdbInv.of_same hM hI hS
      rw [hs2]; simp only [bind_ok]
      have hc2 : capAt (L.mem s2) (cslotAddr dsl) = ok c := by rw [hS.capAt hAd.isSlot, hc]
      have hdc : (Fl4Spec.lookupTargetSlot (Z := Unit) a (Fl4Spec.dataToCptr y0.bv)
          (Fl4Spec.dataToNat y1.bv) >>= fun d => copyTail slbl (rest.map UScalar.bv) excaps d).run σ =
          ({(.ok (.deleteCall dsl), σ)}, False) := by
        rw [run_bind_ok hlt, copyTail_delete _ _ _ _ hlbl]; rfl
      by_cases hcn : c = .Null
      · subst hcn
        have hE1 := hE s2 σ1 hs2 hS hst
        have hFI1 := hEF s2 ar σ1 G ⟨hR1, hV1, hM1, hC1, hI1⟩ hE1
        obtain ⟨c1, a1, hc1, hca1, hg1'⟩ := hR1.abs_cap hAd
        rw [hc2] at hc1
        cases eq_of_ok_eq hc1
        rw [hca1.abs] at hg1'
        have he : Fl4Spec.emptySlot (Z := Unit) dsl .nullCap σ1 = ({((), σ1)}, False) := by
          unfold Fl4Spec.emptySlot
          rw [nd_bind_single hg1']; simp [absCap]
        have hcd := capDelete_triv dsl σ1 σ1 hg1' (Or.inl rfl) he
        rw [delete_null_ok arI σ1 s2 ar _ hc2, WP.spec_ok]
        exact Or.inr ⟨.deleteCall dsl, hdc, σ1, hst, σ1, G, Or.inl ⟨rfl, mem_of_run hcd⟩,
          ⟨hR1, hV1, hM1, hC1, hI1⟩, hFI1, (MdbStep.same_left hM hS (MdbStep.refl hM1)), hE1⟩
      · have hx : cslotAddr dsl ∈ G.chains.flatten := (hM1.members _).2 ⟨hAd.isSlot, c, hc2, hcn⟩
        refine WP.spec_mono (hD s2 ar σ1 G dsl ⟨hR1, hV1, hM1, hC1, hI1⟩ (hE s2 σ1 hs2 hS hst) hAd hx) ?_
        rintro ⟨r, s', a'⟩ ⟨σ', G', hk', hCR', hE', hmD⟩
        refine Or.inr ⟨.deleteCall dsl, hdc, σ1, hst, σ', G', ?_, hCR', hEF _ _ _ _ hCR' hE',
          (MdbStep.same_left hM hS hmD), hE'⟩
        rcases hk' with ⟨h1, h2, -⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr ⟨h1, h2⟩
/-- **CNode Delete**, decode and invoke, for any cap (`cnode_delete_refinesW`
with `E` ignoring the arch state and the ghost tree). -/
theorem cnode_delete_refines (th : TypedHeap) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .cnodeDelete)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (cap : capability.Cap) (a : Fl4Spec.Cap) (hca : CapRel cap a) (hcv : CapValid th cap)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List Fl4Spec.Cap)
    (hI : MdbInv (L.mem s) G)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (E : S → Fl4Spec.State Unit → Prop) (μ : (U64 → U64) → MdbGhost → Nat) (hD : DelHyp (L := L) arI μ th E)
    (hE : ∀ s1 σ1, SlotsSame th (L.mem s) (L.mem s1) →
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) → E s1 σ1)
    (hEF : ∀ s1 σ1 G1, CRel th (L.mem s1) σ1 G1 → E s1 σ1 → FinInv th (L.mem s1) σ1 G1) :
    cnode.decode st arI s ar fl4_abi.label.CNodeDelete length cap buf extra ⦃ res =>
      PInvPost (L := L) th σ G (Fl4Spec.decodeCnodeInvocation slbl (args.map UScalar.bv) a excaps) s
        (res.1, res.2.1) ⦄ :=
  WP.spec_mono (cnode_delete_refinesW arI th s ar σ G hR hV hP hM hC slbl hlbl length buf ct hct args hlen hargs cap
    a hca hcv extra excaps hI hact hcur htcb (fun s _ σ _ => E s σ) μ (hD.w arI)
    (fun s1 σ1 _ hS h => hE s1 σ1 hS h) (fun s1 _ σ1 G1 h1 h2 => hEF s1 σ1 G1 h1 h2)) fun _ h => h.toP

end

end

end Fl4Proofs.P3
