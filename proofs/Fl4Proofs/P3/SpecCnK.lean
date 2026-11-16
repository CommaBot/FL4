/-
P3 (DESIGN.md §9): **the spec side of `cap_insert`** (`CnK`, moved from
IpcGrant.lean so the VSpace decodes can use it): every outcome changes
CNodes, TCBs' caps, the CDT, the original bits and the extended state only
(`capInsert_nkn`).
-/
import Fl4Spec
import Fl4Spec.Ext.VSpace
import Fl4Proofs.P3.InsertSpec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Ipc

noncomputable section

section CnK
open Fl4Spec

/-- The abstract state without the heap, the CDT and the original bits. -/
def abs0 (σ : State Unit) : AbstractState :=
  { σ.toAbstractState with kheap := fun _ => none, cdt := fun _ => none, isOriginalCap := fun _ => false }

/-- Two TCBs alike but for their caps. -/
def CapsOnly (x y : Tcb) : Prop :=
  y.tcbState = x.tcbState ∧ y.tcbIpcBuffer = x.tcbIpcBuffer ∧ y.tcbFault = x.tcbFault ∧
  y.tcbBoundNotification = x.tcbBoundNotification ∧ y.tcbMcpriority = x.tcbMcpriority ∧
  y.tcbSchedContext = x.tcbSchedContext ∧ y.tcbYieldTo = x.tcbYieldTo ∧ y.tcbPriority = x.tcbPriority ∧
  y.tcbDomain = x.tcbDomain ∧ y.tcbFlags = x.tcbFlags ∧ y.tcbArch = x.tcbArch

theorem CapsOnly.refl (x : Tcb) : CapsOnly x x := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem CapsOnly.trans {x y z : Tcb} (h1 : CapsOnly x y) (h2 : CapsOnly y z) : CapsOnly x z :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.1.trans h1.2.2.2.1,
    h2.2.2.2.2.1.trans h1.2.2.2.2.1, h2.2.2.2.2.2.1.trans h1.2.2.2.2.2.1,
    h2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.1, h2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.1,
    h2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.1, h2.2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.2.1,
    h2.2.2.2.2.2.2.2.2.2.2.trans h1.2.2.2.2.2.2.2.2.2.2⟩

/-- An object replaced by one of the same CNode size, or a TCB by one alike
but for its caps. -/
def ObjCn (o o' : Option KernelObject) : Prop :=
  o' = o ∨ (∃ r cs cs', o = some (.cnode r cs) ∧ o' = some (.cnode r cs')) ∨
    (∃ x y, o = some (.tcb x) ∧ o' = some (.tcb y) ∧ CapsOnly x y)

theorem ObjCn.trans {o1 o2 o3 : Option KernelObject} (h1 : ObjCn o1 o2) (h2 : ObjCn o2 o3) : ObjCn o1 o3 := by
  rcases h1 with rfl | ⟨r, cs, cs', rfl, rfl⟩ | ⟨x, y, rfl, rfl, hxy⟩
  · exact h2
  · rcases h2 with rfl | ⟨r', ds, ds', h, rfl⟩ | ⟨x', y', h, rfl, -⟩
    · exact Or.inr (Or.inl ⟨r, cs, cs', rfl, rfl⟩)
    · cases h; exact Or.inr (Or.inl ⟨r, cs, ds', rfl, rfl⟩)
    · cases h
  · rcases h2 with rfl | ⟨r', ds, ds', h, rfl⟩ | ⟨x', y', h, rfl, hxy'⟩
    · exact Or.inr (Or.inr ⟨x, y, rfl, rfl, hxy⟩)
    · cases h
    · cases h; exact Or.inr (Or.inr ⟨x, y', rfl, rfl, hxy.trans hxy'⟩)

/-- **The spec's state changed in CNodes, TCBs' caps, the CDT, the original
bits and the extended state only.** -/
def CnK (σ σ' : State Unit) : Prop := abs0 σ' = abs0 σ ∧ ∀ p, ObjCn (σ.kheap p) (σ'.kheap p)

theorem CnK.refl (σ : State Unit) : CnK σ σ := ⟨rfl, fun _ => Or.inl rfl⟩

theorem CnK.trans {σ1 σ2 σ3 : State Unit} (h1 : CnK σ1 σ2) (h2 : CnK σ2 σ3) : CnK σ1 σ3 :=
  ⟨h2.1.trans h1.1, fun p => (h1.2 p).trans (h2.2 p)⟩

/-- Every outcome is `CnK`. -/
def NKN {α : Type} (m : NonDet (State Unit) α) : Prop := ∀ σ x, x ∈ (m σ).1 → CnK σ x.2

theorem nkn_bind {α β : Type} {m : NonDet (State Unit) α} {f : α → NonDet (State Unit) β} (hm : NKN m)
    (hf : ∀ a, NKN (f a)) : NKN (m >>= f) := by
  intro σ x ⟨y, hy, hx⟩
  exact (hm σ y hy).trans (hf y.1 y.2 x hx)

theorem nkn_pure {α : Type} (a : α) : NKN (pure a : NonDet (State Unit) α) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact CnK.refl σ

theorem nkn_pure' {α : Type} (a : α) : NKN (NonDet.pure a : NonDet (State Unit) α) := nkn_pure a

theorem nkn_gets {α : Type} (f : State Unit → α) : NKN (NonDet.gets f) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact CnK.refl σ

theorem nkn_get : NKN (NonDet.get : NonDet (State Unit) (State Unit)) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact CnK.refl σ

theorem nkn_assert (P : Prop) : NKN (NonDet.assert P : NonDet (State Unit) Unit) := by
  intro σ x hx; obtain ⟨-, rfl⟩ := hx; exact CnK.refl σ

theorem nkn_fail {α : Type} : NKN (NonDet.fail : NonDet (State Unit) α) := by
  intro σ x hx; exact hx.elim

theorem nkn_assertOpt {α : Type} (o : Option α) : NKN (NonDet.assertOpt o : NonDet (State Unit) α) := by
  cases o
  · exact nkn_fail
  · exact nkn_pure' _

theorem nkn_getsThe {α : Type} (f : State Unit → Option α) : NKN (NonDet.getsThe f) := by
  intro σ x hx
  exact nkn_assertOpt (f σ) σ x hx

theorem nkn_selectF {α : Type} (S : Set α × Prop) : NKN (NonDet.selectF S : NonDet (State Unit) α) := by
  intro σ x hx; obtain ⟨-, h⟩ := hx; rw [h]; exact CnK.refl σ

theorem nkn_getObject (p : ObjRef) : NKN (getObject (Z := Unit) p) := nkn_getsThe _

theorem nkn_get_put {f : State Unit → State Unit} (hf : ∀ σ, CnK σ (f σ)) :
    NKN (NonDet.get >>= fun s => NonDet.put (f s)) := by
  intro σ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact hf σ

theorem nkn_modify {f : State Unit → State Unit} (hf : ∀ σ, CnK σ (f σ)) : NKN (NonDet.modify f) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact hf σ

theorem nkn_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDet (State Unit) α} (h1 : NKN m1) (h2 : NKN m2) :
    NKN (if P then m1 else m2) := by
  split <;> assumption

/-- The outcome of `set_object`. -/
theorem setObject_out {σ : State Unit} {p : ObjRef} {o : KernelObject} {x : Unit × State Unit}
    (hx : x ∈ (setObject (Z := Unit) p o σ).1) : x.2 = { σ with kheap := Function.update σ.kheap p (some o) } := by
  unfold setObject at hx
  obtain ⟨y, hy, hx⟩ := hx
  obtain ⟨k, hk, rfl⟩ : ∃ k, σ.kheap p = some k ∧ y = (k, σ) := by
    unfold getObject NonDet.getsThe readObject at hy
    cases h : σ.kheap p with
    | none => rw [h] at hy; exact hy.elim
    | some k => rw [h] at hy; exact ⟨k, rfl, Set.mem_singleton_iff.1 hy⟩
  obtain ⟨z, hz, hx⟩ := hx
  obtain ⟨-, rfl⟩ := hz
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]

theorem cnk_update {σ : State Unit} {p : ObjRef} {o : KernelObject} (h : ObjCn (σ.kheap p) (some o)) :
    CnK σ { σ with kheap := Function.update σ.kheap p (some o) } := by
  refine ⟨rfl, fun q => ?_⟩
  by_cases e : q = p
  · subst e; simpa using h
  · simp [Function.update_of_ne e]; exact Or.inl rfl

theorem nkn_getCap (sl : CslotPtr) : NKN (getCap (Z := Unit) sl) := by
  obtain ⟨o, c⟩ := sl
  unfold getCap
  refine nkn_bind (nkn_getObject o) (fun obj => ?_)
  cases obj <;> simp only [] <;>
    repeat (first | exact nkn_pure _ | exact nkn_fail | exact nkn_assert _ | exact nkn_assertOpt _ |
      (refine nkn_bind ?_ (fun _ => ?_)))

/-- **`set_cap` changes a CNode or a TCB's caps.** -/
theorem nkn_setCap (cap : Cap) (sl : CslotPtr) : NKN (setCap (Z := Unit) cap sl) := by
  obtain ⟨o, c⟩ := sl
  unfold setCap
  intro σ x hx
  dsimp only at hx
  obtain ⟨y, hy, hx⟩ := hx
  obtain ⟨k, hk, rfl⟩ : ∃ k, σ.kheap o = some k ∧ y = (k, σ) := by
    unfold getObject NonDet.getsThe readObject at hy
    cases h : σ.kheap o with
    | none => rw [h] at hy; exact hy.elim
    | some k => rw [h] at hy; exact ⟨k, rfl, Set.mem_singleton_iff.1 hy⟩
  have fin : ∀ o', ObjCn (some k) (some o') → x ∈ (setObject (Z := Unit) o o' σ).1 → CnK σ x.2 :=
    fun o' ho' hx' => by rw [setObject_out hx']; exact cnk_update (by rw [hk]; exact ho')
  have pb : ∀ o', x ∈ ((pure o' >>= fun obj' => setObject (Z := Unit) o obj') σ).1 →
      x ∈ (setObject (Z := Unit) o o' σ).1 := by
    intro o' hx'; obtain ⟨z, hz, hx'⟩ := hx'; rw [Set.mem_singleton_iff.1 hz] at hx'; exact hx'
  have fb : ∀ (f : KernelObject → NonDet (State Unit) Unit), x ∈ ((NonDet.fail >>= f) σ).1 → False := by
    intro f hx'; obtain ⟨z, hz, -⟩ := hx'; exact hz
  cases k with
  | cnode r cs =>
    dsimp only at hx
    split at hx
    · exact (fun h => fin _ h (pb _ hx)) (Or.inr (Or.inl ⟨r, cs, _, rfl, rfl⟩))
    · exact (fb _ hx).elim
  | tcb t =>
    dsimp only at hx
    repeat' split at hx
    all_goals first
      | exact (fb _ hx).elim
      | exact (fun h => fin _ h (pb _ hx)) (Or.inr (Or.inr ⟨t, _, rfl, rfl, CapsOnly.refl t⟩))
  | _ => dsimp only at hx; exact (fb _ hx).elim

theorem nkn_doExtendedOp (eop : DetExtMonad Unit) : NKN (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine nkn_bind nkn_get (fun _ => nkn_bind (nkn_selectF _) (fun _ => ?_))
  split
  exact nkn_modify (fun σ => CnK.refl σ)

/-- **`cap_insert` changes CNodes, TCBs' caps, the CDT and the original bits
only.** -/
theorem capInsert_nkn (c : Cap) (src dest : CslotPtr) : NKN (capInsert (Z := Unit) c src dest) := by
  unfold capInsert setUntypedCapAsFull updateCdt setCdt setOriginal
  repeat (first | exact nkn_getCap _ | exact nkn_setCap _ _ | exact nkn_doExtendedOp _ |
    exact nkn_pure _ | exact nkn_pure' _ | exact nkn_fail | exact nkn_gets _ | exact nkn_get |
    exact nkn_assert _ | exact nkn_get_put (fun σ => ⟨rfl, fun _ => Or.inl rfl⟩) |
    exact nkn_modify (fun σ => ⟨rfl, fun _ => Or.inl rfl⟩) | (refine nkn_bind ?_ (fun _ => ?_)) |
    (apply nkn_ite) | split)


theorem nkn_mapMx {α β : Type} {f : α → NonDet (State Unit) β} (hf : ∀ a, NKN (f a)) :
    ∀ l, NKN (NonDet.mapMx f l)
  | [] => nkn_pure' _
  | a :: l => nkn_bind (hf a) (fun _ => nkn_mapMx hf l)

/-- A `CnK` step keeps the SC objects and their sizes (`SzKeep`). -/
theorem CnK.szKeep {σ σ' : State Unit} (h : CnK σ σ') :
    ∀ p x n, σ'.kheap p = some (.schedContext x n) → ∃ x0, σ.kheap p = some (.schedContext x0 n) := by
  intro p x n hp
  rcases h.2 p with e | ⟨r, cs, cs', -, e⟩ | ⟨a, b, -, e, -⟩
  · exact ⟨x, by rw [← e]; exact hp⟩
  · rw [hp] at e; cases e
  · rw [hp] at e; cases e

/-- **`perform_derive_subframe`** changes CNodes and the CDT only. -/
theorem performDeriveSubframe_nkn (iv : Fl4SubframeInvocation) : NKN (performDeriveSubframe (Z := Unit) iv) := by
  unfold performDeriveSubframe
  exact nkn_mapMx (fun _ => capInsert_nkn _ _ _) _

end CnK

end

end Fl4Proofs.P3.Ipc
