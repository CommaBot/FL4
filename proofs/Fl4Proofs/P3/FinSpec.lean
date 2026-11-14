/-
P3 (DESIGN.md §9), CSpace: **`KTyped` is kept by the spec's CSpace
operations**. An operation keeps it when every CNode and TCB of its final
heap was already one (`KSub`): `set_object` asserts the object's type is
unchanged, so whatever is built from `set_object` and updates of other state
fields does (`NKS`, with the lemmas for `cap_insert`, `cap_move`,
`cap_swap`, `empty_slot`, `cap_swap_for_delete`, `set_thread_state`).
-/
import Fl4Proofs.P3.FinKeep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
open Fl4Spec

/-- Every CNode and TCB of `σ'` was one in `σ`, and `σ'` has no object
where `σ` has none. -/
def KSub (σ σ' : State Unit) : Prop :=
  ∀ o, (∀ r cs, σ'.kheap o = some (.cnode r cs) → wellFormedCnodeN r cs →
      ∃ cs0, σ.kheap o = some (.cnode r cs0) ∧ wellFormedCnodeN r cs0) ∧
    (∀ t, σ'.kheap o = some (.tcb t) → ∃ t0, σ.kheap o = some (.tcb t0)) ∧
    (σ.kheap o = none → σ'.kheap o = none)

theorem KSub.refl (σ : State Unit) : KSub σ σ :=
  fun _ => ⟨fun r cs h hw => ⟨cs, h, hw⟩, fun t h => ⟨t, h⟩, fun h => h⟩

theorem KSub.trans {σ1 σ2 σ3 : State Unit} (h1 : KSub σ1 σ2) (h2 : KSub σ2 σ3) : KSub σ1 σ3 := by
  intro o
  refine ⟨fun r cs h hw => ?_, fun t h => ?_, fun h => (h2 o).2.2 ((h1 o).2.2 h)⟩
  · obtain ⟨cs1, h1', hw1⟩ := (h2 o).1 r cs h hw; exact (h1 o).1 r cs1 h1' hw1
  · obtain ⟨t1, h1'⟩ := (h2 o).2.1 t h; exact (h1 o).2.1 t1 h1'

theorem KSub.of_kheap {σ σ' : State Unit} (h : σ'.kheap = σ.kheap) : KSub σ σ' := by
  intro o; rw [h]; exact KSub.refl σ o

theorem KTyped.sub {th : TypedHeap} {σ σ' : State Unit} (hK : KTyped th σ) (h : KSub σ σ') : KTyped th σ' := by
  intro o
  refine ⟨fun r cs hk hw => ?_, fun t hk => ?_⟩
  · obtain ⟨cs0, h0, hw0⟩ := (h o).1 r cs hk hw; exact (hK o).1 r cs0 h0 hw0
  · obtain ⟨t0, h0⟩ := (h o).2.1 t hk; exact (hK o).2 t0 h0

/-- Every outcome keeps the CNodes and TCBs. -/
def NKS {α : Type} (m : NonDet (State Unit) α) : Prop := ∀ σ x, x ∈ (m σ).1 → KSub σ x.2

theorem ksub_of_eq {α : Type} {m : NonDet (State Unit) α} (hm : NKS m)
    {σ σ' : State Unit} {a : α} {X : Prop} (h : m σ = ({(a, σ')}, X)) : KSub σ σ' :=
  hm σ (a, σ') (by rw [h]; rfl)

theorem nks_bind {α β : Type} {m : NonDet (State Unit) α} {f : α → NonDet (State Unit) β} (hm : NKS m)
    (hf : ∀ a, NKS (f a)) : NKS (m >>= f) := by
  intro σ x ⟨y, hy, hx⟩
  exact (hm σ y hy).trans (hf y.1 y.2 x hx)

theorem nks_pure {α : Type} (a : α) : NKS (pure a : NonDet (State Unit) α) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact KSub.refl σ

theorem nks_pure' {α : Type} (a : α) : NKS (NonDet.pure a : NonDet (State Unit) α) := nks_pure a

theorem nks_gets {α : Type} (f : State Unit → α) : NKS (NonDet.gets f) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact KSub.refl σ

theorem nks_get : NKS (NonDet.get : NonDet (State Unit) (State Unit)) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact KSub.refl σ

theorem nks_modify {f : State Unit → State Unit} (hf : ∀ σ, (f σ).kheap = σ.kheap) : NKS (NonDet.modify f) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact KSub.of_kheap (hf σ)

theorem nks_assert (P : Prop) : NKS (NonDet.assert P : NonDet (State Unit) Unit) := by
  intro σ x hx; obtain ⟨-, rfl⟩ := hx; exact KSub.refl σ

theorem nks_fail {α : Type} : NKS (NonDet.fail : NonDet (State Unit) α) := by
  intro σ x hx; exact hx.elim

theorem nks_assertOpt {α : Type} (o : Option α) : NKS (NonDet.assertOpt o : NonDet (State Unit) α) := by
  cases o
  · exact nks_fail
  · exact nks_pure' _

theorem nks_getsThe {α : Type} (f : State Unit → Option α) : NKS (NonDet.getsThe f) := by
  intro σ x hx
  exact nks_assertOpt (f σ) σ x hx

theorem nks_selectF {α : Type} (S : Set α × Prop) : NKS (NonDet.selectF S : NonDet (State Unit) α) := by
  intro σ x hx; obtain ⟨-, h⟩ := hx; rw [h]; exact KSub.refl σ

theorem nks_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDet (State Unit) α} (h1 : NKS m1) (h2 : NKS m2) :
    NKS (if P then m1 else m2) := by
  split <;> assumption

theorem nks_getObject (p : ObjRef) : NKS (getObject (Z := Unit) p) := nks_getsThe _

theorem aType_capTable {k : KernelObject} {r : Nat} (h : aType k = .aCapTable r) :
    ∃ cs, k = .cnode r cs ∧ wellFormedCnodeN r cs := by
  cases k <;> simp only [aType, reduceCtorEq] at h
  case cnode sz cs => split_ifs at h with hw <;> simp_all
  case schedContext => split_ifs at h

theorem aType_tcb {k : KernelObject} (h : aType k = .aTCB) : ∃ t, k = .tcb t := by
  cases k <;> simp only [aType, reduceCtorEq] at h
  case tcb t => exact ⟨t, rfl⟩
  case cnode => split_ifs at h
  case schedContext => split_ifs at h

theorem nks_setObject (p : ObjRef) (o : KernelObject) : NKS (setObject (Z := Unit) p o) := by
  intro σ x ⟨y, hy, hx⟩
  -- `get_object`
  obtain ⟨k, hk⟩ : ∃ k, σ.kheap p = some k ∧ y = (k, σ) := by
    unfold getObject NonDet.getsThe readObject at hy
    cases h : σ.kheap p with
    | none => rw [h] at hy; exact hy.elim
    | some k => rw [h] at hy; exact ⟨k, rfl, Set.mem_singleton_iff.1 hy⟩
  obtain ⟨hk, rfl⟩ := hk
  obtain ⟨z, hz, hx⟩ := hx
  obtain ⟨hty, rfl⟩ := hz
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  intro o'
  refine ⟨fun r cs h hwf => ?_, fun t h => ?_, fun h => ?_⟩
  · by_cases e : o' = p
    · subst e
      simp only [Function.update_self, Option.some.injEq] at h
      subst h
      have : aType (.cnode r cs) = .aCapTable r := by simp [aType, hwf]
      rw [this] at hty
      obtain ⟨cs0, rfl, hw0⟩ := aType_capTable hty
      exact ⟨cs0, hk, hw0⟩
    · simp only [Function.update_of_ne e] at h; exact ⟨cs, h, hwf⟩
  · by_cases e : o' = p
    · subst e
      simp only [Function.update_self, Option.some.injEq] at h
      subst h
      obtain ⟨t0, rfl⟩ := aType_tcb (show aType k = .aTCB by rw [hty]; rfl)
      exact ⟨t0, hk⟩
    · simp only [Function.update_of_ne e] at h; exact ⟨t, h⟩
  · have e : o' ≠ p := fun e => by subst e; rw [hk] at h; cases h
    simp only [Function.update_of_ne e]; exact h

theorem nks_get_put {f : State Unit → State Unit} (hf : ∀ σ, (f σ).kheap = σ.kheap) :
    NKS (NonDet.get >>= fun s => NonDet.put (f s)) := by
  intro σ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact KSub.of_kheap (hf σ)

macro "nks_step" : tactic => `(tactic| first
  | exact nks_pure _ | exact nks_pure' _ | exact nks_fail | exact nks_gets _ | exact nks_get
  | exact nks_assert _ | exact nks_assertOpt _ | exact nks_getObject _ | exact nks_setObject _ _
  | exact nks_getsThe _
  | exact nks_get_put (fun σ => rfl)
  | exact nks_modify (fun σ => rfl)
  | (refine nks_bind ?_ (fun _ => ?_))
  | (apply nks_ite)
  | split)

theorem nks_getCap (sl : CslotPtr) : NKS (getCap (Z := Unit) sl) := by
  obtain ⟨o, c⟩ := sl
  unfold getCap
  refine nks_bind (nks_getObject o) (fun obj => ?_)
  cases obj <;> simp only [] <;> repeat nks_step

theorem nks_setCap (cap : Cap) (sl : CslotPtr) : NKS (setCap (Z := Unit) cap sl) := by
  obtain ⟨o, c⟩ := sl
  unfold setCap
  refine nks_bind (nks_getObject o) (fun obj => ?_)
  cases obj <;> simp only [] <;> repeat nks_step

theorem nks_doExtendedOp (eop : DetExtMonad Unit) : NKS (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine nks_bind nks_get (fun _ => nks_bind (nks_selectF _) (fun _ => ?_))
  split
  exact nks_modify (fun σ => rfl)

theorem nks_doMachineOp {α : Type} (mop : NonDet MachineState α) : NKS (doMachineOp (Z := Unit) mop) := by
  unfold doMachineOp
  refine nks_bind (nks_gets _) (fun _ => nks_bind (nks_selectF _) (fun x => ?_))
  obtain ⟨r, ms⟩ := x
  exact nks_bind (nks_modify (fun σ => rfl)) (fun _ => nks_pure _)

macro "nks_auto" : tactic => `(tactic| repeat (first | exact nks_getCap _ | exact nks_setCap _ _ | exact nks_doExtendedOp _ | exact nks_doMachineOp _ | nks_step))

theorem capInsert_nks (c : Cap) (src dest : CslotPtr) : NKS (capInsert (Z := Unit) c src dest) := by
  unfold capInsert setUntypedCapAsFull updateCdt setCdt setOriginal
  nks_auto

theorem capMove_nks (c : Cap) (src dest : CslotPtr) : NKS (capMove (Z := Unit) c src dest) := by
  unfold capMove setCdt setOriginal
  nks_auto

theorem capSwap_nks (c1 : Cap) (s1 : CslotPtr) (c2 : Cap) (s2 : CslotPtr) :
    NKS (capSwap (Z := Unit) c1 s1 c2 s2) := by
  unfold capSwap setCdt setOriginal
  nks_auto

theorem capSwapForDelete_nks (s1 s2 : CslotPtr) : NKS (capSwapForDelete (Z := Unit) s1 s2) := by
  unfold capSwapForDelete NonDet.when
  split
  · exact nks_bind (nks_getCap _) (fun _ => nks_bind (nks_getCap _) (fun _ => capSwap_nks _ _ _ _))
  · exact nks_pure' _

theorem setThreadState_nks (t : ObjRef) (ts : ThreadState) : NKS (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState threadSet setThreadStateAct setSchedulerAction NonDet.when
  nks_auto

theorem postCapDeletion_nks (c : Cap) : NKS (postCapDeletion (Z := Unit) c) := by
  unfold postCapDeletion deletedIrqHandler setIrqState archPostCapDeletion freeIoportRange setIoportMask
    maskInterrupt
  nks_auto

theorem emptySlot_nks (sl : CslotPtr) (cl : Cap) : NKS (emptySlot (Z := Unit) sl cl) := by
  unfold emptySlot setCdt setOriginal
  refine nks_bind (nks_getCap _) (fun _ => ?_)
  apply nks_ite
  · exact nks_pure _
  · nks_auto
    all_goals exact postCapDeletion_nks _

/-- `FinInv` across a step that keeps every slot and every CNode and TCB. -/
theorem FinInv.of_same {th : TypedHeap} {mem mem' : U64 → U64} {σ σ' : State Unit} {G : MdbGhost}
    (hFI : FinInv th mem σ G) (hM : MdbLinks th mem G) (hS : SlotsSame th mem mem') (hK : KSub σ σ') :
    FinInv th mem' σ' G :=
  ⟨hFI.kt.sub hK, hFI.fm.of_caps hM.tree.nodup (fun z hz => hS.capV ((hM.members z).1 hz).1)⟩

/-! ## The exception monad -/

def NKSE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := NKS (ExceptT.run m)

theorem nkse_bind {ε α β : Type} {m : NonDetE (State Unit) ε α} {f : α → NonDetE (State Unit) ε β}
    (hm : NKSE m) (hf : ∀ a, NKSE (f a)) : NKSE (m >>= f) := by
  unfold NKSE; rw [ExceptT.run_bind]
  refine nks_bind hm (fun r => ?_)
  cases r with
  | ok a => exact hf a
  | error e => exact nks_pure _

theorem nkse_liftE {ε α : Type} {m : NonDet (State Unit) α} (hm : NKS m) : NKSE (NonDetE.liftE (ε := ε) m) := by
  unfold NKSE NonDetE.liftE; rw [ExceptT.run_lift]
  exact nks_bind hm (fun _ => nks_pure _)

theorem nkse_throw {ε α : Type} (e : ε) : NKSE (NonDetE.throwError e : NonDetE (State Unit) ε α) := nks_pure _
theorem nkse_pure {ε α : Type} (a : α) : NKSE (pure a : NonDetE (State Unit) ε α) := nks_pure _
theorem nkse_returnOk {ε α : Type} (a : α) : NKSE (NonDetE.returnOk a : NonDetE (State Unit) ε α) := nks_pure _

theorem nkse_ite {ε α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDetE (State Unit) ε α} (h1 : NKSE m1) (h2 : NKSE m2) :
    NKSE (if P then m1 else m2) := by split <;> assumption

theorem nkse_whenE {ε : Type} (P : Prop) [Decidable P] {m : NonDetE (State Unit) ε Unit} (h : NKSE m) :
    NKSE (NonDetE.whenE P m) := by unfold NonDetE.whenE; split; exact h; exact nkse_pure _

theorem nkse_orChoiceE {ε α : Type} (c : DetExtMonad Bool) {f g : NonDetE (State Unit) ε α} (hf : NKSE f) (hg : NKSE g) :
    NKSE (orChoiceE c f g) := by
  unfold orChoiceE
  refine nkse_bind (nkse_liftE nks_get) (fun _ => nkse_bind (nkse_liftE (nks_selectF _)) (fun x => ?_))
  obtain ⟨rv, _⟩ := x
  exact nkse_ite _ hf hg

theorem nks_updateTimeStamp : NKS (updateTimeStamp (Z := Unit)) := by
  unfold updateTimeStamp NonDet.when
  nks_auto

theorem preemptionPoint_nks : NKSE (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint
  refine nkse_bind (nkse_liftE (nks_doExtendedOp _)) (fun _ => nkse_orChoiceE _ ?_ (nkse_returnOk _))
  refine nkse_bind (nkse_liftE (nks_doExtendedOp _)) (fun _ => ?_)
  refine nkse_bind (nkse_liftE nks_updateTimeStamp) (fun _ => ?_)
  refine nkse_bind (nkse_liftE (nks_doMachineOp _)) (fun _ => ?_)
  refine nkse_bind (nkse_liftE (nks_gets _)) (fun _ => ?_)
  refine nkse_bind (nkse_liftE (nks_gets _)) (fun _ => ?_)
  refine nkse_bind (nkse_liftE (nks_gets _)) (fun _ => ?_)
  refine nkse_bind (nkse_liftE (nks_getsThe _)) (fun _ => ?_)
  refine nkse_bind (nkse_liftE (nks_gets _)) (fun _ => ?_)
  exact nkse_whenE _ (nkse_throw _)

end

end

end Fl4Proofs.P3
