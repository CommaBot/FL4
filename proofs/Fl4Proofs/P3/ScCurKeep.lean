/-
P3 (DESIGN.md §9), scheduling contexts: **the current thread's invariants
across the SC operations** (the fold's (a): `CurInv` unless a reschedule is
pending, `OffOK`, `CurRun`).

* `CurK σ σ'`: the current thread, SC and time kept, a pending reschedule kept
  pending, and, unless a reschedule is pending after, the current thread's
  SC link and IPC-freedom, the current SC's activeness, and the current
  thread out of the release queue kept (`CurKeep`). With it,
  `CurInvW σ → CurInvW σ'` (`CurInvW.ck`).
* `CurKA P m`: every outcome of `m` from a state satisfying `P` is
  `CurK`-related to its start. Combinators (`cka_bind` with a `CurK`-stable
  precondition), and the leaves: reads, `setObject` (the current thread's
  TCB and SC written as allowed), `modify`.
* `OKs σ σ'`: the consumed time cleared, or kept with the current SC's head
  refill kept; `OffOK σ → OKs σ σ' → OffOK σ'`.
-/
import Fl4Proofs.P3.ScBsaOps
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open Fl4Spec Classical Fl4Proofs.P3.Notif

noncomputable section

/-- `CurInv` unless a reschedule is pending. -/
def CurInvW (σ : State Unit) : Prop := σ.schedulerAction = .chooseNewThread ∨ CurInv σ

/-- What `CurInv` reads, kept (module docstring). -/
def CurKeep (σ σ' : State Unit) : Prop :=
  (∀ x, σ.kheap σ.curThread = some (.tcb x) → ∃ y, σ'.kheap σ.curThread = some (.tcb y) ∧
      y.tcbSchedContext = x.tcbSchedContext ∧ (NotIpcBlk x.tcbState → NotIpcBlk y.tcbState)) ∧
  (∀ y n, σ.kheap σ.curSc = some (.schedContext y n) → ∃ y', σ'.kheap σ.curSc = some (.schedContext y' n) ∧
      (scActive y = true → scActive y' = true)) ∧
  (σ.curThread ∈ σ'.releaseQueue → σ.curThread ∈ σ.releaseQueue)

theorem CurKeep.refl (σ : State Unit) : CurKeep σ σ :=
  ⟨fun x h => ⟨x, h, rfl, id⟩, fun y n h => ⟨y, h, id⟩, id⟩

/-- **The current-thread step** (module docstring). -/
structure CurK (σ σ' : State Unit) : Prop where
  ct : σ'.curThread = σ.curThread
  csc : σ'.curSc = σ.curSc
  time : σ'.curTime = σ.curTime
  isc : σ'.idleSc = σ.idleSc
  cn : σ.schedulerAction = .chooseNewThread → σ'.schedulerAction = .chooseNewThread
  keep : σ'.schedulerAction = .chooseNewThread ∨ CurKeep σ σ'

theorem CurK.refl (σ : State Unit) : CurK σ σ := ⟨rfl, rfl, rfl, rfl, id, Or.inr (CurKeep.refl σ)⟩

theorem CurK.trans {σ1 σ2 σ3 : State Unit} (h1 : CurK σ1 σ2) (h2 : CurK σ2 σ3) : CurK σ1 σ3 := by
  refine ⟨h2.ct.trans h1.ct, h2.csc.trans h1.csc, h2.time.trans h1.time, h2.isc.trans h1.isc,
    fun h => h2.cn (h1.cn h), ?_⟩
  rcases h2.keep with e | k2
  · exact Or.inl e
  rcases h1.keep with e | k1
  · exact Or.inl (h2.cn e)
  right
  obtain ⟨a1, b1, c1⟩ := k1
  obtain ⟨a2, b2, c2⟩ := k2
  rw [h1.ct] at a2 c2; rw [h1.csc] at b2
  refine ⟨fun x hx => ?_, fun y n hy => ?_, fun h => c1 (c2 h)⟩
  · obtain ⟨y, hy, e1, f1⟩ := a1 x hx
    obtain ⟨z, hz, e2, f2⟩ := a2 y hy
    exact ⟨z, hz, e2.trans e1, fun h => f2 (f1 h)⟩
  · obtain ⟨y', hy', f1⟩ := b1 y n hy
    obtain ⟨z, hz, f2⟩ := b2 y' n hy'
    exact ⟨z, hz, fun h => f2 (f1 h)⟩

theorem CurInvW.ck {σ σ' : State Unit} (h : CurInvW σ) (hK : CurK σ σ') : CurInvW σ' := by
  rcases hK.keep with e | k
  · exact Or.inl e
  rcases h with e | hC
  · exact Or.inl (hK.cn e)
  right
  obtain ⟨ka, kb, kc⟩ := k
  obtain ⟨xt, hkt, hsc, hnb⟩ := hC.tcb
  obtain ⟨y, hy, e1, f1⟩ := ka xt hkt
  obtain ⟨x, n, hx⟩ := hC.sc
  obtain ⟨x', hx', fa⟩ := kb x n hx
  refine ⟨⟨y, by rw [hK.ct]; exact hy, by rw [e1, hK.csc]; exact hsc, f1 hnb⟩, ⟨x', n, by rw [hK.csc]; exact hx'⟩,
    fun hid y2 m hy2 => ?_, fun hm => hC.notRel (kc (by rw [← hK.ct]; exact hm))⟩
  rw [hK.csc, hK.isc] at hid; rw [hK.csc] at hy2
  rw [hx'] at hy2; cases hy2
  exact fa (hC.active hid x n hx)

/-! ## The monad -/

/-- `CurK` from the states satisfying `P`. -/
def CurKA {α : Type} (P : State Unit → Prop) (m : NonDet (State Unit) α) : Prop :=
  ∀ σ, P σ → ∀ x, x ∈ (m σ).1 → CurK σ x.2

/-- A precondition kept by `CurK` steps. -/
def CurKStable (P : State Unit → Prop) : Prop := ∀ σ σ', P σ → CurK σ σ' → P σ'

theorem cka_bind {α β : Type} {P : State Unit → Prop} (hP : CurKStable P) {m : NonDet (State Unit) α}
    {g : α → NonDet (State Unit) β} (hm : CurKA P m) (hg : ∀ a, CurKA P (g a)) : CurKA P (m >>= g) := by
  intro σ hσ x ⟨y, hy, hx⟩
  have h1 := hm σ hσ y hy
  exact h1.trans (hg y.1 y.2 (hP σ y.2 hσ h1) x hx)

theorem cka_bind' {α β : Type} {P : State Unit → Prop} (hP : CurKStable P) {m : NonDet (State Unit) α}
    {g : α → NonDet (State Unit) β} (hm : CurKA P m) (hg : ∀ a, CurKA P (g a)) : CurKA P (NonDet.bind m g) :=
  cka_bind hP hm hg

theorem cka_of_eq {α : Type} {P : State Unit → Prop} {m : NonDet (State Unit) α}
    (h : ∀ σ x, x ∈ (m σ).1 → x.2 = σ) : CurKA P m := by
  intro σ _ x hx; rw [h σ x hx]; exact CurK.refl σ

theorem cka_pure {α : Type} {P : State Unit → Prop} (a : α) : CurKA P (pure a : NonDet (State Unit) α) :=
  cka_of_eq fun _ x hx => by rw [Set.mem_singleton_iff.1 hx]

theorem cka_pure' {α : Type} {P : State Unit → Prop} (a : α) : CurKA P (NonDet.pure a : NonDet (State Unit) α) :=
  cka_pure a

theorem cka_gets {α : Type} {P : State Unit → Prop} (g : State Unit → α) : CurKA P (NonDet.gets g) :=
  cka_of_eq fun _ x hx => by rw [Set.mem_singleton_iff.1 hx]

theorem cka_get {P : State Unit → Prop} : CurKA P (NonDet.get : NonDet (State Unit) (State Unit)) :=
  cka_of_eq fun _ x hx => by rw [Set.mem_singleton_iff.1 hx]

theorem cka_assert {P : State Unit → Prop} (Q : Prop) : CurKA P (NonDet.assert Q : NonDet (State Unit) Unit) :=
  cka_of_eq fun _ x hx => by obtain ⟨-, rfl⟩ := hx; rfl

theorem cka_fail {α : Type} {P : State Unit → Prop} : CurKA P (NonDet.fail : NonDet (State Unit) α) :=
  fun _ _ _ hx => hx.elim

theorem cka_assertOpt {α : Type} {P : State Unit → Prop} (o : Option α) :
    CurKA P (NonDet.assertOpt o : NonDet (State Unit) α) := by
  cases o
  · exact cka_fail
  · exact cka_pure' _

theorem cka_getsThe {α : Type} {P : State Unit → Prop} (g : State Unit → Option α) : CurKA P (NonDet.getsThe g) := by
  intro σ hσ x hx; exact cka_assertOpt (g σ) σ hσ x hx

theorem cka_ite {α : Type} {P : State Unit → Prop} (Q : Prop) [Decidable Q] {m1 m2 : NonDet (State Unit) α}
    (h1 : CurKA P m1) (h2 : CurKA P m2) : CurKA P (if Q then m1 else m2) := by
  split <;> assumption

theorem cka_when {P : State Unit → Prop} (Q : Prop) [Decidable Q] {m : NonDet (State Unit) Unit} (h : CurKA P m) :
    CurKA P (NonDet.when Q m) := by
  unfold NonDet.when; exact cka_ite Q h (cka_pure' _)

theorem cka_unless {P : State Unit → Prop} (Q : Prop) [Decidable Q] {m : NonDet (State Unit) Unit} (h : CurKA P m) :
    CurKA P (NonDet.unless Q m) := by
  unfold NonDet.unless; exact cka_ite Q (cka_pure' _) h

theorem cka_maybeM {α : Type} {P : State Unit → Prop} {g : α → NonDet (State Unit) Unit} (h : ∀ a, CurKA P (g a))
    (o : Option α) : CurKA P (NonDet.maybeM g o) := by
  cases o
  · exact cka_pure' _
  · exact h _

theorem cka_liftM {α β : Type} {P : State Unit → Prop} (hP : CurKStable P) (g : α → β) {m : NonDet (State Unit) α}
    (h : CurKA P m) : CurKA P (NonDet.liftM g m) := cka_bind' hP h fun _ => cka_pure' _

theorem cka_mono {α : Type} {P Q : State Unit → Prop} {m : NonDet (State Unit) α} (h : CurKA Q m)
    (hPQ : ∀ σ, P σ → Q σ) : CurKA P m := fun σ hσ => h σ (hPQ σ hσ)

/-- **`modify`.** -/
theorem cka_modify {P : State Unit → Prop} {g : State Unit → State Unit} (hg : ∀ σ, P σ → CurK σ (g σ)) :
    CurKA P (NonDet.modify g) := by
  intro σ hσ x hx; rw [Set.mem_singleton_iff.1 hx]; exact hg σ hσ

/-- **`set_object`**, the current thread's TCB and the current SC written as
`CurKeep` allows. -/
theorem cka_setObject {P : State Unit → Prop} (p : ObjRef) (o : KernelObject)
    (ht : ∀ σ, P σ → p = σ.curThread → ∀ x, σ.kheap p = some (.tcb x) → ∃ y, o = .tcb y ∧
      y.tcbSchedContext = x.tcbSchedContext ∧ (NotIpcBlk x.tcbState → NotIpcBlk y.tcbState))
    (hs : ∀ σ, P σ → p = σ.curSc → ∀ y n, σ.kheap p = some (.schedContext y n) → ∃ y', o = .schedContext y' n ∧
      (scActive y = true → scActive y' = true)) :
    CurKA P (setObject (Z := Unit) p o) := by
  intro σ hσ x hx
  obtain ⟨k, hk, -, e⟩ := MaxK.mk_setObject_mem hx
  rw [e]
  refine ⟨rfl, rfl, rfl, rfl, id, Or.inr ⟨fun xt hxt => ?_, fun y n hy => ?_, id⟩⟩
  · by_cases hp : σ.curThread = p
    · obtain ⟨y, rfl, e1, e2⟩ := ht σ hσ hp.symm xt (hp ▸ hxt)
      exact ⟨y, by rw [hp]; simp, e1, e2⟩
    · exact ⟨xt, by simp [Function.update_of_ne hp, hxt], rfl, id⟩
  · by_cases hp : σ.curSc = p
    · obtain ⟨y', rfl, e1⟩ := hs σ hσ hp.symm y n (hp ▸ hy)
      exact ⟨y', by rw [hp]; simp, e1⟩
    · exact ⟨y, by simp [Function.update_of_ne hp, hy], id⟩

end

end Fl4Proofs.P3.Sched
