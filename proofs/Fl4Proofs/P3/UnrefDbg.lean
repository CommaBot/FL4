/-
P3 (KENTRY-PLAN jc6e): **part (c) of `RegionUnrefAt` and `DeadUnarmed` at every `JAtZ`
state**, from the dead set's `DeadX` (`JCovD.dx`: a dead TCB's `DEBUG_PREV` word is 0, no
core's `DEBUG_TCBS` head names it, its deadline word is 0) and the debug lists' shape
(`J.live.2.1 : DbgWF`).

* **`JAtZ.keptCW J : DbgKeptCAll H Cs D s`** (jc6a's carried form of (c), no premise): a
  list member is not dead (`DbgWFL.notMem_of_off` with `DeadX`), and every debug word is 0
  or a list member (`nextIn_zero_or_mem`, `prevA_zero_or_mem`, `headD_zero_or_mem`; an
  off-list TCB's links are 0, `DbgWFL.off`; `H 0 = none`).
* **`JAtZ.unrefCW J hni : RegionUnrefC H Cs D s`** at an `Entered` `JAtZ` state:
  `keptCW` at `JAtZ.restartSJ`'s state (the same `H`, `D`), then `DbgKeptCAll.region`.
* **`JAtZ.deadUnarmed J : DeadUnarmed H D s`** (`DeadX`'s third part), and
  `JAtZ.regionUnrefCU` = U27's `RegionUnrefCU`.
-/
import Fl4Proofs.P3.UnrefBnd
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **(c), carried form, at any `JAtZ` state** (module docstring). -/
theorem JAtZ.keptCW (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) : DbgKeptCAll (L := L) H Cs D s := by
  obtain ⟨lst, hW⟩ := J.live.2.1
  have h0 : H 0#u64 = none := J.kern.h0
  have hnl : ∀ c ∈ Cs, ∀ x ∈ lst c, x ∉ D := fun c hc x hx hxD => by
    have hxT : H x = some .tcb := (hW.mem c hc x hx).1
    obtain ⟨d1, d2, -⟩ := J.jcov.dx x hxD hxT
    exact hW.notMem_of_off d1 d2 c hc hx
  have kr : ∀ c ∈ Cs, ∀ w : U64, (w = 0#u64 ∨ w ∈ lst c) → P1.KeptRef H (· ∈ D) w := by
    intro c hc w hw hH hD
    rcases hw with rfl | hw
    · exact hH h0
    · exact hnl c hc w hw hD
  refine ⟨fun y hy => ?_, fun c hc => ?_⟩
  · by_cases hl : ∃ c ∈ Cs, y ∈ lst c
    · obtain ⟨c, hc, hyc⟩ := hl
      refine ⟨kr c hc _ ?_, kr c hc _ ?_⟩
      · rw [hW.next c hc y hyc]; exact nextIn_zero_or_mem _ _
      · rw [hW.prev c hc y hyc]
        rcases prevA_zero_or_mem (lst c) 0#u64 y with h | h | h
        · exact Or.inl h
        · exact Or.inl h
        · exact Or.inr h
    · have hn : ∀ c ∈ Cs, y ∉ lst c := fun c hc hyc => hl ⟨c, hc, hyc⟩
      obtain ⟨e1, e2⟩ := hW.off y hy hn
      exact ⟨fun hH _ => hH (by rw [e1]; exact h0), fun hH _ => hH (by rw [e2]; exact h0)⟩
  · refine kr c hc _ ?_
    have e : L.mem s (L.nodeAt s c layout.node.DEBUG_TCBS) = (lst c).headD 0#u64 := hW.head c hc
    rw [e]; exact headD_zero_or_mem _

/-- **(c) of `RegionUnrefAt` at an `Entered` `JAtZ` state** (module docstring). -/
theorem JAtZ.unrefCW (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) :
    RegionUnrefC (L := L) H Cs D s := by
  intro s1 hs1 lo hi hD
  have hct : sched.cur_thread st s = ok (L.curW s) := cur_thread_eq s
  obtain ⟨hcur, x, hk, hrun⟩ := J.curRunnable hni hct
  have htcb : Z.th (L.curW s) = some .tcb := (J.xtop.curTcb hcur).1
  obtain ⟨Ac', Lst', J1⟩ := J.restartSJ (jStepHyps arI) hcur hk htcb hrun hs1
  exact J1.keptCW.region hD

/-- **The dead TCBs are unarmed** at any `JAtZ` state (`DeadX`). -/
theorem JAtZ.deadUnarmed (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) : DeadUnarmed (L := L) H D s :=
  fun q hq hH => (J.jcov.dx q hq hH).2.2

/-- **U27's `RegionUnrefCU`** at an `Entered` `JAtZ` state. -/
theorem JAtZ.regionUnrefCU (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) :
    RegionUnrefCU (L := L) H Cs D s :=
  ⟨J.unrefCW hni, J.deadUnarmed⟩

end

end

end Fl4Proofs.P3
