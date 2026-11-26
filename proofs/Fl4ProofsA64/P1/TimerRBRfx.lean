-- AArch64 port of Fl4Proofs.P1.TimerRBRfx (proofs/scratch/a64/port.py): the x86_64 text, re-checked
-- over Fl4CoreA64. Edits beyond the renaming are marked `-- a64:`.
/-
P1 (jc6d, TIMER-RB-PLAN stage 7, heap part): `timer::remove_fixup` keeps the red-black shape.  The loop
state `(s, x, p, fuel)` satisfies `RfInv`: the heap is a tree `W` over the fixed keys (`FB`, the walk state
of the insert fixup, reused with its colour-write and rotation steps `FB.set_red`, `FB.rotL`, `FB.rotR`), in
mode `RfA` (doubly black at `x`) or `RfB` (balanced, `x` the root).  One round (`rf_body`):
- exit when `x` is the root (`rf_body_top`, `rf_body_B`) or red (`rf_body_red`);
- `x` a left child (`rf_body_L`): red sibling → recolour + `rotate_left(p)` (case 1), then from the black
  sibling (`RfC2L`): both nephews black → recolour, `x := p` (case 2, the path gets one shorter, or the new
  `x` is red); near nephew red only → recolour + `rotate_right(w)` (case 3, `rf_c3L`), then far nephew red
  (`RfC4L`) → recolour + `rotate_left(p)`, `x := root` (case 4, `rf_c4L`, balanced: mode `RfB`);
- `x` a right child (`rf_body_R`), mirrored.
The `fuel = 0` exit is never taken: a round that spends fuel starts with a black `x`, whose path length is at
most the fuel, and either ends in mode `RfB`, or leaves a red `x`, or shortens the path by one.
`timer.remove_fixup.rb`: from the doubly-black state (`rf_init` gives it for `remove`, path length ≤ 128 <
256), the result is a red-black tree with black root over the same keys (`FB`).
-/
import Fl4ProofsA64.P1.TimerRBRfxP
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64}

/-- The loop invariant on `(s, x, p, fuel)`. -/
abbrev RfInv (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s0 : S) (c : U64) (Ks : List U64)
    (x : S × U64 × U64 × U64) : Prop :=
  ∃ W, FB st T s0 c Ks x.1 W ∧ (TRB.RfA W x.2.1 x.2.2.1 x.2.2.2.val ∨ TRB.RfB W x.2.1)

/-- The loop's result `(s, x)`: balanced with black root and `x` the root, or `x` red and to be blackened. -/
abbrev RfOut (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s0 : S) (c : U64) (Ks : List U64)
    (y : S × U64) : Prop :=
  ∃ W, FB st T s0 c Ks y.1 W ∧ (TRB.RfB W y.2 ∨ TRB.RfR W y.2)

/-- What one round must deliver (`loop.spec_decr_nat`, measure = fuel). -/
abbrev RfPost (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s0 : S) (c : U64) (Ks : List U64)
    (f : U64) (r : ControlFlow (S × U64 × U64 × U64) (S × U64)) : Prop :=
  match r with
  | .done y => RfOut st T s0 c Ks y
  | .cont x' => RfInv st T s0 c Ks x' ∧ x'.2.2.2.val < f.val

/-- `x` on the left, black sibling `w1` (after the optional case 1). -/
def RfC2L (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s0 : S) (c : U64) (Ks : List U64)
    (tx : TRB.RBT) (pk : U64) (n f1 : Nat) (s1 : S) (w1 : U64) : Prop :=
  ∃ up cp wl wr, FB st T s0 c Ks s1 (up.plug (.node cp tx pk (.node false wl w1 wr))) ∧ TRB.Bal wl n ∧
    TRB.Bal wr n ∧ TRB.UpOK up cp n ∧ (cp = true ∨ up.depth ≤ f1)

/-- `x` on the right, black sibling `w1`. -/
def RfC2R (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s0 : S) (c : U64) (Ks : List U64)
    (tx : TRB.RBT) (pk : U64) (n f1 : Nat) (s1 : S) (w1 : U64) : Prop :=
  ∃ up cp wl wr, FB st T s0 c Ks s1 (up.plug (.node cp (.node false wl w1 wr) pk tx)) ∧ TRB.Bal wl n ∧
    TRB.Bal wr n ∧ TRB.UpOK up cp n ∧ (cp = true ∨ up.depth ≤ f1)

/-- `x` on the left, black sibling `w2` whose right child is red (case 4). -/
def RfC4L (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s0 : S) (c : U64) (Ks : List U64)
    (tx : TRB.RBT) (pk : U64) (n : Nat) (s2 : S) (w2 : U64) : Prop :=
  ∃ up cp wl c1 k2 d1, FB st T s0 c Ks s2 (up.plug (.node cp tx pk (.node false wl w2 (.node true c1 k2 d1)))) ∧
    TRB.Bal wl n ∧ TRB.Bal c1 n ∧ TRB.Bal d1 n ∧ TRB.UpOK up cp n

/-- `x` on the right, black sibling `w2` whose left child is red (case 4). -/
def RfC4R (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s0 : S) (c : U64) (Ks : List U64)
    (tx : TRB.RBT) (pk : U64) (n : Nat) (s2 : S) (w2 : U64) : Prop :=
  ∃ up cp wr c1 k2 d1, FB st T s0 c Ks s2 (up.plug (.node cp (.node false (.node true c1 k2 d1) w2 wr) pk tx)) ∧
    TRB.Bal wr n ∧ TRB.Bal c1 n ∧ TRB.Bal d1 n ∧ TRB.UpOK up cp n

/-- Case 4, `x` on the left. -/
theorem rf_c4L {s0 s2 : S} {c : U64} {Ks : List U64} (hT : TcbPlaced T) (hd : Ks.Nodup)
    (hk : ∀ y ∈ Ks, y ∈ T) {tx : TRB.RBT} {pk w2 f1 f : U64} {n : Nat} (htx : TRB.Bal tx n)
    (hC : RfC4L st T s0 c Ks tx pk n s2 w2) (hlt : f1.val < f.val) :
    (do
      let pr ← timer.is_red st s2 pk
      let s3 ← timer.set_red st s2 w2 pr
      let s4 ← timer.set_red st s3 pk false
      let wr ← timer.right st s4 w2
      let s5 ← timer.set_red st s4 wr false
      let s6 ← timer.rotate_left st s5 c pk
      let x1 ← timer.root st s6 c
      ok (ControlFlow.cont (s6, x1, 0#u64, f1))) ⦃ r => RfPost st T s0 c Ks f r ⦄ := by
  obtain ⟨up, cp, wl, c1, k2, d1, h, hwl, hc1, hd1, hU⟩ := hC
  have hpr : TRB.Rep (lk st s2) up.par pk (.node cp tx pk (.node false wl w2 (.node true c1 k2 d1))) :=
    ((TRB.rep_plug up _).1 h.rep).2
  step with timer.is_red.rep s2 hpr as ⟨pr, epr⟩
  replace epr : pr = cp := epr
  subst pr
  step with FB.set_red (.rc cp tx pk up) false wl w2 (.node true c1 k2 d1) hT hd hk h cp as ⟨s3, h3⟩
  step with FB.set_red up cp tx pk (.node cp wl w2 (.node true c1 k2 d1)) hT hd hk h3 false as ⟨s4, h4⟩
  have hw : TRB.Rep (lk st s4) pk w2 (.node cp wl w2 (.node true c1 k2 d1)) :=
    ((TRB.rep_plug (.rc false tx pk up) _).1 h4.rep).2
  step with timer.right.rep s4 hw as ⟨wr, ewr⟩
  replace ewr : wr = k2 := ewr
  subst wr
  step with FB.set_red (.rc cp wl w2 (.rc false tx pk up)) true c1 k2 d1 hT hd hk h4 false as ⟨s5, h5⟩
  step with FB.rotL up false tx pk cp wl w2 (.node false c1 k2 d1) hT hd hk h5 as ⟨s6, h6⟩
  step with timer.root.val (st := st) s6 c as ⟨x1, ex1⟩
  try simp only [WP.spec_ok]
  obtain ⟨m, hb, hbl⟩ := TRB.rf_case4L (pk := pk) (w := w2) (k := k2) htx hwl hc1 hd1 hU
  exact ⟨⟨_, h6, Or.inr ⟨ex1.trans h6.rep.root, m, hb, hbl⟩⟩, hlt⟩

/-- Case 4, `x` on the right. -/
theorem rf_c4R {s0 s2 : S} {c : U64} {Ks : List U64} (hT : TcbPlaced T) (hd : Ks.Nodup)
    (hk : ∀ y ∈ Ks, y ∈ T) {tx : TRB.RBT} {pk w2 f1 f : U64} {n : Nat} (htx : TRB.Bal tx n)
    (hC : RfC4R st T s0 c Ks tx pk n s2 w2) (hlt : f1.val < f.val) :
    (do
      let pr ← timer.is_red st s2 pk
      let s3 ← timer.set_red st s2 w2 pr
      let s4 ← timer.set_red st s3 pk false
      let wl ← timer.left st s4 w2
      let s5 ← timer.set_red st s4 wl false
      let s6 ← timer.rotate_right st s5 c pk
      let x1 ← timer.root st s6 c
      ok (ControlFlow.cont (s6, x1, 0#u64, f1))) ⦃ r => RfPost st T s0 c Ks f r ⦄ := by
  obtain ⟨up, cp, wr, c1, k2, d1, h, hwr, hc1, hd1, hU⟩ := hC
  have hpr : TRB.Rep (lk st s2) up.par pk (.node cp (.node false (.node true c1 k2 d1) w2 wr) pk tx) :=
    ((TRB.rep_plug up _).1 h.rep).2
  step with timer.is_red.rep s2 hpr as ⟨pr, epr⟩
  replace epr : pr = cp := epr
  subst pr
  step with FB.set_red (.lc cp pk tx up) false (.node true c1 k2 d1) w2 wr hT hd hk h cp as ⟨s3, h3⟩
  step with FB.set_red up cp (.node cp (.node true c1 k2 d1) w2 wr) pk tx hT hd hk h3 false as ⟨s4, h4⟩
  have hw : TRB.Rep (lk st s4) pk w2 (.node cp (.node true c1 k2 d1) w2 wr) :=
    ((TRB.rep_plug (.lc false pk tx up) _).1 h4.rep).2
  step with timer.left.rep s4 hw as ⟨wl, ewl⟩
  replace ewl : wl = k2 := ewl
  subst wl
  step with FB.set_red (.lc cp w2 wr (.lc false pk tx up)) true c1 k2 d1 hT hd hk h4 false as ⟨s5, h5⟩
  step with FB.rotR up false cp (.node false c1 k2 d1) w2 wr pk tx hT hd hk h5 as ⟨s6, h6⟩
  step with timer.root.val (st := st) s6 c as ⟨x1, ex1⟩
  try simp only [WP.spec_ok]
  obtain ⟨m, hb, hbl⟩ := TRB.rf_case4R (pk := pk) (w := w2) (k := k2) htx hwr hc1 hd1 hU
  exact ⟨⟨_, h6, Or.inr ⟨ex1.trans h6.rep.root, m, hb, hbl⟩⟩, hlt⟩

/-- Case 3, `x` on the left: near nephew red, far nephew black; afterwards case 4 applies. -/
theorem rf_c3L {s0 s1 : S} {c : U64} {Ks : List U64} (hT : TcbPlaced T) (hd : Ks.Nodup)
    (hk : ∀ y ∈ Ks, y ∈ T) {tx a1 b1 wr : TRB.RBT} {pk w1 k1 : U64} {n : Nat} {up : TRB.Ctx} {cp : Bool}
    (h : FB st T s0 c Ks s1 (up.plug (.node cp tx pk (.node false (.node true a1 k1 b1) w1 wr))))
    (ha : TRB.Bal a1 n) (hb : TRB.Bal b1 n) (hbb : b1.isRed = false) (hwr : TRB.Bal wr n)
    (hwrb : wr.isRed = false) (hU : TRB.UpOK up cp n) :
    (do
      let s3 ← timer.set_red st s1 k1 false
      let s4 ← timer.set_red st s3 w1 true
      let s5 ← timer.rotate_right st s4 c w1
      let w3 ← timer.right st s5 pk
      ok (s5, w3)) ⦃ x => RfC4L st T s0 c Ks tx pk n x.1 x.2 ⦄ := by
  step with FB.set_red (.lc false w1 wr (.rc cp tx pk up)) true a1 k1 b1 hT hd hk h false as ⟨s3, h3⟩
  step with FB.set_red (.rc cp tx pk up) false (.node false a1 k1 b1) w1 wr hT hd hk h3 true as ⟨s4, h4⟩
  step with FB.rotR (.rc cp tx pk up) true false a1 k1 b1 w1 wr hT hd hk h4 as ⟨s5, h5⟩
  have hp : TRB.Rep (lk st s5) up.par pk (.node cp tx pk (.node false a1 k1 (.node true b1 w1 wr))) :=
    ((TRB.rep_plug up _).1 h5.rep).2
  step with timer.right.rep s5 hp as ⟨w3, ew3⟩
  replace ew3 : w3 = k1 := ew3
  subst w3
  try simp only [WP.spec_ok]
  exact ⟨up, cp, a1, b1, w1, wr, h5, ha, hb, hwr, hU⟩

/-- Case 3, `x` on the right. -/
theorem rf_c3R {s0 s1 : S} {c : U64} {Ks : List U64} (hT : TcbPlaced T) (hd : Ks.Nodup)
    (hk : ∀ y ∈ Ks, y ∈ T) {tx a1 b1 wl : TRB.RBT} {pk w1 k1 : U64} {n : Nat} {up : TRB.Ctx} {cp : Bool}
    (h : FB st T s0 c Ks s1 (up.plug (.node cp (.node false wl w1 (.node true a1 k1 b1)) pk tx)))
    (ha : TRB.Bal a1 n) (hab : a1.isRed = false) (hb : TRB.Bal b1 n) (hwl : TRB.Bal wl n)
    (hwlb : wl.isRed = false) (hU : TRB.UpOK up cp n) :
    (do
      let s3 ← timer.set_red st s1 k1 false
      let s4 ← timer.set_red st s3 w1 true
      let s5 ← timer.rotate_left st s4 c w1
      let w3 ← timer.left st s5 pk
      ok (s5, w3)) ⦃ x => RfC4R st T s0 c Ks tx pk n x.1 x.2 ⦄ := by
  step with FB.set_red (.rc false wl w1 (.lc cp pk tx up)) true a1 k1 b1 hT hd hk h false as ⟨s3, h3⟩
  step with FB.set_red (.lc cp pk tx up) false wl w1 (.node false a1 k1 b1) hT hd hk h3 true as ⟨s4, h4⟩
  step with FB.rotL (.lc cp pk tx up) true wl w1 false a1 k1 b1 hT hd hk h4 as ⟨s5, h5⟩
  have hp : TRB.Rep (lk st s5) up.par pk (.node cp (.node false (.node true wl w1 a1) k1 b1) pk tx) :=
    ((TRB.rep_plug up _).1 h5.rep).2
  step with timer.left.rep s5 hp as ⟨w3, ew3⟩
  replace ew3 : w3 = k1 := ew3
  subst w3
  try simp only [WP.spec_ok]
  exact ⟨up, cp, b1, wl, w1, a1, h5, hb, hwl, ha, hU⟩

end

end Fl4ProofsA64.P1
