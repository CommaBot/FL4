/-
P3 (DESIGN.md §9), CSpace: **the spec's `rec_del`, step by step**, as
outcomes of the least fixed point (`NonDet.lfp` of `recDelF`): one lemma per
branch of each call kind (`CTEDeleteCall`, `FinaliseSlotCall`,
`ReduceZombieCall`), each turning outcomes of the recursive calls into an
outcome of the call (as `capRevoke_step` does for `cap_revoke`). FL4's
loops are matched against these.
-/
import Fl4Proofs.P3.CnodeRevoke
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
open Fl4Spec

/-- An outcome of a `rec_del` call. -/
abbrev RD (c : RecDelCall) (σ : State Unit) (x : Except Unit (Bool × Cap) × State Unit) : Prop :=
  x ∈ ((recDel (Z := Unit) c).run σ).1

abbrev RDF := fun (r : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))) (c : RecDelCall) =>
  recDelF (Z := Unit) r c

theorem recDel_run (c : RecDelCall) (σ : State Unit) :
    (recDel (Z := Unit) c).run σ = NonDet.lfp RDF c σ := rfl

/-- Lift an outcome of `recDelF f` for every pre-fixed point `f`, given the
recursive outcomes, to an outcome of `rec_del`. -/
theorem rd_of_F {c : RecDelCall} {σ : State Unit} {x : Except Unit (Bool × Cap) × State Unit}
    (h : ∀ f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap)),
      (∀ k t, RDF f k t ≤ f k t) → (∀ c' σ' y, RD c' σ' y → y ∈ (f c' σ').1) →
      x ∈ ((recDelF (Z := Unit) f c).run σ).1) : RD c σ x := by
  show x ∈ (NonDet.lfp RDF c σ).1
  exact lfp_mem _ fun f hf => h f hf fun c' σ' y hy => (lfp_le_prefixed _ f hf c' σ').1 hy

/-! ### `CTEDeleteCall` -/

theorem rd_cte_ok {sl : CslotPtr} {e : Bool} {σ σ1 σ2 : State Unit} {succ : Bool} {cl : Cap}
    (hf : RD (.finaliseSlotCall sl e) σ (.ok (succ, cl), σ1))
    (he : ((), σ2) ∈ ((NonDet.when (e = true ∨ succ = true) (emptySlot (Z := Unit) sl cl)) σ1).1) :
    ∃ v, RD (.cTEDeleteCall sl e) σ (.ok v, σ2) := by
  refine ⟨undefined, rd_of_F fun f _ hl => ?_⟩
  unfold recDelF withoutPreemption
  refine mem_bindE_ok (hl _ _ _ hf) ?_
  show (Except.ok undefined, σ2) ∈ ((NonDetE.liftE _ >>= fun _ => NonDetE.returnOk undefined).run σ1).1
  refine mem_bindE_ok (s' := σ2) (a := ()) ?_ (mem_of_run (run_returnOk _ σ2))
  rw [liftE_run]
  exact mem_bind_nd he rfl

theorem rd_cte_err {sl : CslotPtr} {e : Bool} {σ σ1 : State Unit}
    (hf : RD (.finaliseSlotCall sl e) σ (.error (), σ1)) : RD (.cTEDeleteCall sl e) σ (.error (), σ1) := by
  refine rd_of_F fun f _ hl => ?_
  unfold recDelF
  exact mem_bindE_err (hl _ _ _ hf)

/-- `cap_delete` from `CTEDeleteCall slot True`. -/
theorem capDelete_ok {sl : CslotPtr} {σ σ' : State Unit} {v : Bool × Cap}
    (h : RD (.cTEDeleteCall sl true) σ (.ok v, σ')) :
    (.ok (), σ') ∈ ((capDelete (Z := Unit) sl).run σ).1 := by
  unfold capDelete
  exact mem_bindE_ok h (mem_of_run (run_returnOk _ σ'))

theorem capDelete_err {sl : CslotPtr} {σ σ' : State Unit}
    (h : RD (.cTEDeleteCall sl true) σ (.error (), σ')) :
    (.error (), σ') ∈ ((capDelete (Z := Unit) sl).run σ).1 := by
  unfold capDelete
  exact mem_bindE_err h

/-! ### `FinaliseSlotCall` -/

theorem rd_fin_null {sl : CslotPtr} {e : Bool} {σ : State Unit}
    (hg : getCap (Z := Unit) sl σ = ({(.nullCap, σ)}, False)) :
    RD (.finaliseSlotCall sl e) σ (.ok (true, .nullCap), σ) := by
  refine rd_of_F fun f _ _ => ?_
  unfold recDelF withoutPreemption
  refine mem_bindE_ok (mem_of_run (run_liftE hg)) ?_
  simp only [↓reduceIte]
  exact mem_of_run (run_returnOk _ σ)

/-- The common prefix of a round on a non-null cap: read it, its finality,
finalise it. -/
theorem fin_prefix {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))} {sl : CslotPtr} {e : Bool}
    {σ σ1 : State Unit} {c rem cl : Cap} (hg : getCap (Z := Unit) sl σ = ({(c, σ)}, False)) (hc : c ≠ .nullCap)
    (hfc : ((rem, cl), σ1) ∈ (finaliseCap (Z := Unit) c (decide (isFinalCap' c σ)) σ).1)
    {y : Except Unit (Bool × Cap) × State Unit}
    (hy : y ∈ ((if capRemoveable rem sl then NonDetE.returnOk (true, cl)
        else if capCyclicZombie rem sl ∧ ¬ e = true then do
          withoutPreemption <| setCap rem sl
          NonDetE.returnOk (false, .nullCap)
        else do
          withoutPreemption <| setCap rem sl
          let _ ← f (.reduceZombieCall rem sl e)
          preemptionPoint
          f (.finaliseSlotCall sl e) : PMonad Unit (Bool × Cap)).run σ1).1) :
    y ∈ ((recDelF (Z := Unit) f (.finaliseSlotCall sl e)).run σ).1 := by
  unfold recDelF withoutPreemption
  refine mem_bindE_ok (mem_of_run (run_liftE hg)) ?_
  simp only [hc, ↓reduceIte]
  refine mem_bindE_ok (mem_of_run (run_liftE (m := isFinalCap (Z := Unit) c) rfl)) ?_
  refine mem_bindE_ok (a := (rem, cl)) (s' := σ1) ?_ ?_
  · rw [liftE_run]; exact mem_bind_nd hfc rfl
  · exact hy

theorem rd_fin_removable {sl : CslotPtr} {e : Bool} {σ σ1 : State Unit} {c rem cl : Cap}
    (hg : getCap (Z := Unit) sl σ = ({(c, σ)}, False)) (hc : c ≠ .nullCap)
    (hfc : ((rem, cl), σ1) ∈ (finaliseCap (Z := Unit) c (decide (isFinalCap' c σ)) σ).1)
    (hr : capRemoveable rem sl) :
    RD (.finaliseSlotCall sl e) σ (.ok (true, cl), σ1) := by
  refine rd_of_F fun f _ _ => fin_prefix hg hc hfc ?_
  rw [if_pos hr]
  exact mem_of_run (run_returnOk _ σ1)

theorem rd_fin_cyclic {sl : CslotPtr} {σ σ1 σ2 : State Unit} {c rem cl : Cap}
    (hg : getCap (Z := Unit) sl σ = ({(c, σ)}, False)) (hc : c ≠ .nullCap)
    (hfc : ((rem, cl), σ1) ∈ (finaliseCap (Z := Unit) c (decide (isFinalCap' c σ)) σ).1)
    (hr : ¬ capRemoveable rem sl) (hcy : capCyclicZombie rem sl)
    (hs : setCap (Z := Unit) rem sl σ1 = ({((), σ2)}, False)) :
    RD (.finaliseSlotCall sl false) σ (.ok (false, .nullCap), σ2) := by
  refine rd_of_F fun f _ _ => fin_prefix hg hc hfc ?_
  rw [if_neg hr, if_pos ⟨hcy, by decide⟩]
  refine mem_bindE_ok (mem_of_run (run_liftE_st hs)) (mem_of_run (run_returnOk _ σ2))

/-- The reducing round: set the remainder, reduce the zombie, preemption
point, and then the outcome `y` of the next round. -/
theorem rd_fin_reduce {sl : CslotPtr} {e : Bool} {σ σ1 σ2 σ3 σ4 : State Unit} {c rem cl : Cap}
    (hg : getCap (Z := Unit) sl σ = ({(c, σ)}, False)) (hc : c ≠ .nullCap)
    (hfc : ((rem, cl), σ1) ∈ (finaliseCap (Z := Unit) c (decide (isFinalCap' c σ)) σ).1)
    (hr : ¬ capRemoveable rem sl) (hcy : ¬ (capCyclicZombie rem sl ∧ e = false))
    (hs : setCap (Z := Unit) rem sl σ1 = ({((), σ2)}, False)) {v : Bool × Cap}
    (hz : RD (.reduceZombieCall rem sl e) σ2 (.ok v, σ3))
    (hp : (.ok (), σ4) ∈ ((preemptionPoint (Z := Unit)).run σ3).1) {y : Except Unit (Bool × Cap) × State Unit}
    (hy : RD (.finaliseSlotCall sl e) σ4 y) :
    RD (.finaliseSlotCall sl e) σ y := by
  refine rd_of_F fun f _ hl => fin_prefix hg hc hfc ?_
  rw [if_neg hr, if_neg (fun h => hcy ⟨h.1, by simpa using h.2⟩)]
  refine mem_bindE_ok (mem_of_run (run_liftE_st hs)) ?_
  exact mem_bindE_ok (hl _ _ _ hz) (mem_bindE_ok hp (hl _ _ _ hy))

theorem rd_fin_reduce_err {sl : CslotPtr} {e : Bool} {σ σ1 σ2 σ3 : State Unit} {c rem cl : Cap}
    (hg : getCap (Z := Unit) sl σ = ({(c, σ)}, False)) (hc : c ≠ .nullCap)
    (hfc : ((rem, cl), σ1) ∈ (finaliseCap (Z := Unit) c (decide (isFinalCap' c σ)) σ).1)
    (hr : ¬ capRemoveable rem sl) (hcy : ¬ (capCyclicZombie rem sl ∧ e = false))
    (hs : setCap (Z := Unit) rem sl σ1 = ({((), σ2)}, False))
    (hz : RD (.reduceZombieCall rem sl e) σ2 (.error (), σ3)) :
    RD (.finaliseSlotCall sl e) σ (.error (), σ3) := by
  refine rd_of_F fun f _ hl => fin_prefix hg hc hfc ?_
  rw [if_neg hr, if_neg (fun h => hcy ⟨h.1, by simpa using h.2⟩)]
  refine mem_bindE_ok (mem_of_run (run_liftE_st hs)) ?_
  exact mem_bindE_err (hl _ _ _ hz)

theorem rd_fin_pp_err {sl : CslotPtr} {e : Bool} {σ σ1 σ2 σ3 σ4 : State Unit} {c rem cl : Cap}
    (hg : getCap (Z := Unit) sl σ = ({(c, σ)}, False)) (hc : c ≠ .nullCap)
    (hfc : ((rem, cl), σ1) ∈ (finaliseCap (Z := Unit) c (decide (isFinalCap' c σ)) σ).1)
    (hr : ¬ capRemoveable rem sl) (hcy : ¬ (capCyclicZombie rem sl ∧ e = false))
    (hs : setCap (Z := Unit) rem sl σ1 = ({((), σ2)}, False)) {v : Bool × Cap}
    (hz : RD (.reduceZombieCall rem sl e) σ2 (.ok v, σ3))
    (hp : (.error (), σ4) ∈ ((preemptionPoint (Z := Unit)).run σ3).1) :
    RD (.finaliseSlotCall sl e) σ (.error (), σ4) := by
  refine rd_of_F fun f _ hl => fin_prefix hg hc hfc ?_
  rw [if_neg hr, if_neg (fun h => hcy ⟨h.1, by simpa using h.2⟩)]
  refine mem_bindE_ok (mem_of_run (run_liftE_st hs)) ?_
  exact mem_bindE_ok (hl _ _ _ hz) (mem_bindE_err hp)

/-! ### `ReduceZombieCall` -/

/-- Not exposed: swap the zombie into its first slot. -/
theorem rd_reduce_false {ptr : ObjRef} {bits : Option Nat} {n : Nat} {sl : CslotPtr} {σ σ' : State Unit}
    (hne : firstCslotOf (.zombie ptr bits (n + 1)) ≠ sl)
    (hsw : ((), σ') ∈ (capSwapForDelete (Z := Unit) (firstCslotOf (.zombie ptr bits (n + 1))) sl σ).1) :
    ∃ v, RD (.reduceZombieCall (.zombie ptr bits (n + 1)) sl false) σ (.ok v, σ') := by
  refine ⟨undefined, rd_of_F fun f _ _ => ?_⟩
  unfold recDelF withoutPreemption
  refine mem_bindE_ok (mem_of_run (run_returnOk _ σ)) ?_
  refine mem_bindE_ok (a := ()) (s' := σ) ?_ ?_
  · rw [NonDetE.assertE, liftE_run]; exact mem_bind_nd (x := ((), σ)) ⟨hne, rfl⟩ rfl
  refine mem_bindE_ok (a := ()) (s' := σ') ?_ (mem_of_run (run_returnOk _ σ'))
  rw [liftE_run]; exact mem_bind_nd hsw rfl

/-- Exposed, the zombie's end slot deleted, the cap in the slot unchanged:
decrement the zombie. -/
theorem rd_reduce_true_dec {ptr : ObjRef} {bits : Option Nat} {n : Nat} {sl : CslotPtr}
    {σ σ1 σ2 : State Unit} {v : Bool × Cap}
    (hd : RD (.cTEDeleteCall (ptr, natToCref (zombieCteBits bits) n) false) σ (.ok v, σ1))
    (hg : getCap (Z := Unit) sl σ1 = ({(.zombie ptr bits (n + 1), σ1)}, False))
    (hs : setCap (Z := Unit) (.zombie ptr bits n) sl σ1 = ({((), σ2)}, False)) :
    ∃ v, RD (.reduceZombieCall (.zombie ptr bits (n + 1)) sl true) σ (.ok v, σ2) := by
  refine ⟨undefined, rd_of_F fun f _ hl => ?_⟩
  unfold recDelF withoutPreemption
  refine mem_bindE_ok (mem_of_run (run_returnOk _ σ)) ?_
  refine mem_bindE_ok (hl _ _ _ hd) ?_
  refine mem_bindE_ok (mem_of_run (run_liftE hg)) ?_
  simp only [↓reduceIte]
  exact mem_bindE_ok (mem_of_run (run_liftE_st hs)) (mem_of_run (run_returnOk _ σ2))

/-- Exposed, the cap in the slot changed: the spec's assertion. -/
theorem rd_reduce_true_chg {ptr : ObjRef} {bits : Option Nat} {n : Nat} {sl : CslotPtr}
    {σ σ1 : State Unit} {v : Bool × Cap} {nc : Cap}
    (hd : RD (.cTEDeleteCall (ptr, natToCref (zombieCteBits bits) n) false) σ (.ok v, σ1))
    (hg : getCap (Z := Unit) sl σ1 = ({(nc, σ1)}, False)) (hnc : nc ≠ .zombie ptr bits (n + 1))
    (ha : nc = .nullCap ∨ isZombie nc ∧ firstCslotOf nc = sl ∧ firstCslotOf (.zombie ptr bits (n + 1)) ≠ sl) :
    ∃ v, RD (.reduceZombieCall (.zombie ptr bits (n + 1)) sl true) σ (.ok v, σ1) := by
  refine ⟨undefined, rd_of_F fun f _ hl => ?_⟩
  unfold recDelF withoutPreemption
  refine mem_bindE_ok (mem_of_run (run_returnOk _ σ)) ?_
  refine mem_bindE_ok (hl _ _ _ hd) ?_
  refine mem_bindE_ok (mem_of_run (run_liftE hg)) ?_
  simp only [hnc, ↓reduceIte]
  refine mem_bindE_ok (a := ()) (s' := σ1) ?_ (mem_of_run (run_returnOk _ σ1))
  rw [NonDetE.assertE, liftE_run]; exact mem_bind_nd (x := ((), σ1)) ⟨ha, rfl⟩ rfl

theorem rd_reduce_true_err {ptr : ObjRef} {bits : Option Nat} {n : Nat} {sl : CslotPtr}
    {σ σ1 : State Unit}
    (hd : RD (.cTEDeleteCall (ptr, natToCref (zombieCteBits bits) n) false) σ (.error (), σ1)) :
    RD (.reduceZombieCall (.zombie ptr bits (n + 1)) sl true) σ (.error (), σ1) := by
  refine rd_of_F fun f _ hl => ?_
  unfold recDelF withoutPreemption
  refine mem_bindE_ok (mem_of_run (run_returnOk _ σ)) ?_
  exact mem_bindE_err (hl _ _ _ hd)

end

end

end Fl4Proofs.P3
