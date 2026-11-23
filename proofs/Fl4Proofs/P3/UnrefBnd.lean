/-
P3 (issue #16, jc6b2; KENTRY-PLAN jc6b, jc6b2): **part (b) of `RegionUnrefAt` at every
`JAtZ` state**, from P1's carried bound-link symmetry (`ScExtra0.bs : BndS`, the FL4-word
form of jc6b's spec-side `BndSym`: a TCB's bound notification names it back, a
notification's bound TCB names it back, an SC's notification names it back as its SC).

* **`JAtZ.keptBW J : KeptRefsBAll H D s`** (jc6a's carried form of (b), no premise): a link
  to a dead object has a back-link word (`BndS.tb` / `.nt` / `.sn`) naming the (live, so
  nonzero) source, while the dead object's `DeadP` zeroes that word (`nBoundA`, `tBoundA`,
  `nScA`).
* **`JAtZ.unrefBW J hni : RegionUnrefB H D s`** at an `Entered` `JAtZ` state: `keptBW` at
  `JAtZ.restartSJ`'s state (the same `H`, `D`), then `KeptRefsBAll.region` (as `unrefB`,
  without jc6b's `BndSym` premise: the restart's `JAtZ` carries `BndS` itself).
* `RegionUnrefCU` = (c) ∧ `DeadUnarmed` (what `kernel_entry_reachU27` asks), and
  `JAtZ.regionUnrefBCU` rebuilds U26's `RegionUnrefBCU`.
-/
import Fl4Proofs.P3.UnrefSym
import Fl4Proofs.P3.UnrefTimer
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **(c) ∧ `DeadUnarmed`**: what `kernel_entry_reachU27` asks in place of U26's
`RegionUnrefBCU` ((b) is proved, `JAtZ.unrefBW`). -/
def RegionUnrefCU (H : P1.Heap) (Cs D : Set U64) (s : S) : Prop :=
  RegionUnrefC (L := L) H Cs D s ∧ DeadUnarmed (L := L) H D s

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **(b), carried form, at any `JAtZ` state** (module docstring). -/
theorem JAtZ.keptBW (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) : KeptRefsBAll (L := L) H D s := by
  have h0 := J.kern.h0
  have hE := J.blk.2.2.1.2.2
  have nz : ∀ q, H q ≠ none → q ≠ 0#u64 := fun q hq e => hq (by rw [e]; exact h0)
  refine ⟨fun t ht hw hD => ?_, fun c hc hw hD => ?_, fun n hn hw hD => ?_⟩
  · -- a TCB's bound notification
    have hw0 : L.mem s (P1.boundA t) ≠ 0#u64 := fun e => hw (by rw [e]; exact h0)
    have hwN : L.mem s (P1.boundA t) ∈ P1.Heap.ntfns H := hE.bnd t ht hw0
    have tb : L.mem s (P1.ntfnBtA (L.mem s (P1.boundA t))) = t := hE.bs.tb t ht hw0
    have d : L.mem s (Notif.nBoundA (L.mem s (P1.boundA t))) = 0#u64 := ((J.jcov.dead _ hD).2.2.1 hwN).2.1
    have e : t = 0#u64 := tb.symm.trans d
    exact nz t (by rw [show H t = some .tcb from ht]; simp) e
  · -- an SC's notification
    have hw0 : L.mem s (P1.scNtfnA c) ≠ 0#u64 := fun e => hw (by rw [e]; exact h0)
    have hwN : L.mem s (P1.scNtfnA c) ∈ P1.Heap.ntfns H := hE.scn c hc hw0
    obtain ⟨z, hz⟩ := id hc
    have hc0 : c ≠ 0#u64 := nz c (by rw [hz]; simp)
    have sn : L.mem s (P1.ntfnScA (L.mem s (P1.scNtfnA c))) = c := hE.bs.sn c hc hc0 hw0
    have d : L.mem s (Notif.nScA (L.mem s (P1.scNtfnA c))) = 0#u64 := ((J.jcov.dead _ hD).2.2.1 hwN).2.2
    exact hc0 (sn.symm.trans d)
  · -- a notification's bound TCB
    have hw0 : L.mem s (P1.ntfnBtA n) ≠ 0#u64 := fun e => hw (by rw [e]; exact h0)
    have hwT : L.mem s (P1.ntfnBtA n) ∈ P1.Heap.tcbs H := (hE.ntb n hn).ne0 hw0
    have hwZ : L.mem s (P1.ntfnBtA n) ∈ Z.T := by rw [J.tcbs_eq.1]; exact hwT
    have nt : L.mem s (P1.boundA (L.mem s (P1.ntfnBtA n))) = n := hE.bs.nt n hn hw0
    have d : L.mem s (Endp.tBoundA (L.mem s (P1.ntfnBtA n))) = 0#u64 :=
      ((J.jcov.dead _ hD).1 (J.zH.1 _ hwZ)).2.2.1
    exact nz n (by rw [show H n = some .ntfn from hn]; simp) (nt.symm.trans d)

/-- **(b) of `RegionUnrefAt` at an `Entered` `JAtZ` state** (module docstring). -/
theorem JAtZ.unrefBW (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) :
    RegionUnrefB (L := L) H D s := by
  intro s1 hs1 lo hi hD
  have hct : sched.cur_thread st s = ok (L.curW s) := cur_thread_eq s
  obtain ⟨hcur, x, hk, hrun⟩ := J.curRunnable hni hct
  have htcb : Z.th (L.curW s) = some .tcb := (J.xtop.curTcb hcur).1
  obtain ⟨Ac', Lst', J1⟩ := J.restartSJ (jStepHyps arI) hcur hk htcb hrun hs1
  exact J1.keptBW.region hD

/-- **U26's `RegionUnrefBCU` from `RegionUnrefCU`** at an `Entered` `JAtZ` state. -/
theorem JAtZ.regionUnrefBCU (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ)
    (h : RegionUnrefCU (L := L) H Cs D s) : RegionUnrefBCU (L := L) H Cs D s :=
  ⟨J.unrefBW hni, h.1, h.2⟩

end

end

end Fl4Proofs.P3
