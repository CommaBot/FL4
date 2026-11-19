/-
P3 (DESIGN.md §9), Untyped's reset (the drop step): **no yield link names a
dead object** (`JAtZ.yield_noDead`), the fact the drop of a region's dead
objects needs for `SchedValid.scYieldFrom`/`tcbYieldTo` and `YieldRel.frm`/
`toSc` (handoff utj Round 6, G2): a dead thread's `YIELD_TO` word and a dead
SC's `YIELD_FROM` word are null (`DeadP`'s yield clauses), and the links are
symmetric (`YieldRel`), so

* an SC of `Z.C` whose `YIELD_FROM` word is a thread `q` of `D` would make
  `q`'s `YIELD_TO` word that SC (`YieldRel.frm`), not null;
* a thread of `Z.T` whose `YIELD_TO` word is an SC `q` of `D` would make
  `q`'s `YIELD_FROM` word that thread (`YieldRel.toSc`, `ScRelW.yieldFrom`),
  not null.

l4v: `if_live_then_nonz_cap` with `sym_refs` (a TCB with `tcb_yield_to` and an
SC with `sc_yield_from` are live, so covered by a cap, so not in a childless
untyped's region).
-/
import Fl4Proofs.P3.ScDeadStep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

/-- **No yield link names a dead object** (module docstring). -/
theorem JAtZ.yield_noDead {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {q : U64} (hqD : q ∈ D) :
    (∀ c ∈ Z.C, L.mem s (P1.scYieldFromA c) = q → q = 0#u64) ∧
    (∀ t ∈ Z.T, L.mem s (P1.yieldA t) = q → q = 0#u64) := by
  have hd := J.jcov.dead q hqD
  obtain ⟨Q, R, hc, hs⟩ := J.xtop.fin.1.1.1.lists
  refine ⟨fun c hcC e => ?_, fun t ht e => ?_⟩
  · by_contra hq0
    obtain ⟨y, n, hk, hR⟩ := hs.scs c hcC
    have hyf : y.scYieldFrom = some q.bv := by
      rw [hR.yieldFrom, ← scYieldFromA_eq, e, Notif.optRef_ne hq0]
    obtain ⟨u, huT, eu, hu⟩ := J.yld.frm c hcC y n hk q.bv hyf
    have huq : u = q := P1.eq_of_bv eu
    rw [huq] at huT hu
    have h0 := (hd.1 (J.zH.1 q huT)).2.2.2.2.2
    rw [h0] at hu
    exact J.c0 c hcC hu.symm
  · by_contra hq0
    obtain ⟨hqC, y, n, hk, hyf⟩ := J.yld.toSc t ht (by rw [e]; exact hq0)
    rw [e] at hqC hk
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    have hH := (hJ.sc q y n (J.c0 q hqC) hk).2
    have h0 := (hd.2.2.2.2 _ hH).2.2.2
    obtain ⟨y', n', hk', hR⟩ := hs.scs q hqC
    rw [hk] at hk'; cases hk'
    rw [hR.yieldFrom, ← scYieldFromA_eq, h0, Notif.optRef_zero] at hyf
    cases hyf

end

end

end Fl4Proofs.P3
