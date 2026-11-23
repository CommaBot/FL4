/-
P3 (issue #16, jc6a): **`RegionUnrefAt` split into its four parts** (KENTRY-PLAN jc6
(3)–(4)), and part (a) proved at `JAtZ`.

`RegionUnrefAt H Cs D s0` (ScJoint) asks, after the caller's restart from `s0`, for a
region whose `H` objects are all in `D`, `KeptRefsP3` and `DbgTimerKept` at the region.
Its links fall in four groups:

* (a) `KeptRefsA`: the reply stacks' links (reply next/prev, an SC's reply head) and
  the yield links (TCB yield-to, SC yield-from). **Proved at every `JAtZ` state**
  (`JAtZ.keptA`): a link to a dead object has a back-link the dead object's `DeadP`
  zeroes. A dead reply has a null `rTcb` (`DeadP`), so (`IpcRel.reply`) it is `Free`,
  so (`RFree`) on no call stack and with null links; a reply a link names is on a call
  stack (`CallRel.stack`'s `StackW`) or links back to the linking reply (`CallRel.det`).
  A yield-to link names an SC whose spec `scYieldFrom` is the TCB (`YieldRel.toSc`),
  which is the SC's word 56 (`ScRel.yieldFrom`), zero for a dead SC; a yield-from
  word names a TCB whose `YIELD_TO` word is the SC (`YieldRel.frm`), zero for a dead
  TCB (the SC non-null, `JAtZ.c0`; `H`'s SCs are `Z.C`'s, `hscC`).
  `JAtZ.unrefA` lifts it across the restart (`JAtZ.restartSJ`, which keeps `D`).
* (b) `KeptRefsB`: the bound-notification and SC-notification links (needs a carried
  symmetry, jc6b).
* (c) `DbgKeptC`: the debug-list links and every core's `DEBUG_TCBS` (jc6c).
* (d) `TimerKeptD`: the timer-tree links and every core's `TIMER_ROOT` / `TIMER_MIN`
  (jc6d).

`regionUnrefAt_iff`: `RegionUnrefAt ↔ (a) ∧ (b) ∧ (c) ∧ (d)` (each at the region,
after the restart). `RegionUnrefBCD` is (b) ∧ (c) ∧ (d), the premise
`kernel_entry_reachU25` keeps; `JAtZ.regionUnrefAt` assembles `RegionUnrefAt` from it
at an `Entered` `JAtZ` state.

**Carried forms** of (b)–(d) (`KeptRefsBAll`, `DbgKeptCAll`, `TimerKeptDAll`;
definitions only, not threaded): the jc6 design correction (2): each quantifies over
every object of `H`, dead ones included (no `¬ D y →` antecedent), with `(· ∈ D)` as
the dead set; `…All.region` gives the region form at the same state, for any region
whose `H` objects are in `D`.
-/
import Fl4Proofs.P3.XTopJointTcbInstall
import Fl4Proofs.P3.ScJoint
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched

noncomputable section

/-! ## The four parts -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **(a) The reply-stack and yield links** of `KeptRefsP3`. -/
def KeptRefsA (H : P1.Heap) (D : U64 → Prop) (s : S) : Prop :=
  (∀ r ∈ H.replies, ¬ D r → P1.headBit (L.mem s (P1.rNextA r)) = false →
    P1.KeptRef H D (L.mem s (P1.rNextA r) &&& ~~~1#u64)) ∧
  (∀ r ∈ H.replies, ¬ D r → P1.KeptRef H D (L.mem s (P1.rPrevA r) &&& ~~~1#u64)) ∧
  (∀ c ∈ H.scs, ¬ D c → P1.KeptRef H D (L.mem s (P1.scReplyA c))) ∧
  (∀ t ∈ H.tcbs, ¬ D t → P1.KeptRef H D (L.mem s (P1.yieldA t))) ∧
  (∀ c ∈ H.scs, ¬ D c → P1.KeptRef H D (L.mem s (P1.scYieldFromA c)))

/-- **(b) The bound-notification and SC-notification links** of `KeptRefsP3`. -/
def KeptRefsB (H : P1.Heap) (D : U64 → Prop) (s : S) : Prop :=
  (∀ t ∈ H.tcbs, ¬ D t → P1.KeptRef H D (L.mem s (P1.boundA t))) ∧
  (∀ c ∈ H.scs, ¬ D c → P1.KeptRef H D (L.mem s (P1.scNtfnA c))) ∧
  (∀ n ∈ H.ntfns, ¬ D n → P1.KeptRef H D (L.mem s (P1.ntfnBtA n)))

/-- **(c) The debug lists** of `DbgTimerKept`: the TCBs' `dn`/`dp` links and every
core's `DEBUG_TCBS` head. -/
def DbgKeptC (H : P1.Heap) (D : U64 → Prop) (Cs : Set U64) (s : S) : Prop :=
  (∀ y ∈ H.tcbs, ¬ D y → P1.KeptRef H D (L.mem s (P1.dnA y)) ∧ P1.KeptRef H D (L.mem s (P1.dpA y))) ∧
  (∀ c ∈ Cs, P1.KeptRef H D (L.mem s (L.nodeAt s c layout.node.DEBUG_TCBS)))

/-- **(d) The timer trees** of `DbgTimerKept`: the TCBs' `tl`/`tr`/`tp` links and
every core's `TIMER_ROOT` and `TIMER_MIN`. -/
def TimerKeptD (H : P1.Heap) (D : U64 → Prop) (Cs : Set U64) (s : S) : Prop :=
  (∀ y ∈ H.tcbs, ¬ D y → P1.KeptRef H D (L.mem s (P1.tlA y)) ∧ P1.KeptRef H D (L.mem s (P1.trA y)) ∧
    P1.KeptRef H D (L.mem s (P1.tpA y))) ∧
  (∀ c ∈ Cs, P1.KeptRef H D (L.mem s (L.nodeAt s c layout.node.TIMER_ROOT)) ∧
    P1.KeptRef H D (L.mem s (L.nodeAt s c layout.node.TIMER_MIN)))

theorem keptRefsP3_iff {H : P1.Heap} {D : U64 → Prop} {s : S} :
    KeptRefsP3 (L := L) H D s ↔ KeptRefsA (L := L) H D s ∧ KeptRefsB (L := L) H D s := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩; exact ⟨⟨h1, h2, h3, h7, h8⟩, h4, h5, h6⟩
  · rintro ⟨⟨h1, h2, h3, h7, h8⟩, h4, h5, h6⟩; exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem dbgTimerKept_iff {H : P1.Heap} {D : U64 → Prop} {Cs : Set U64} {s : S} :
    DbgTimerKept (L := L) H D Cs s ↔ DbgKeptC (L := L) H D Cs s ∧ TimerKeptD (L := L) H D Cs s := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨fun y hy hd => ⟨(h1 y hy hd).2.2.2.1, (h1 y hy hd).2.2.2.2⟩, fun c hc => (h2 c hc).2.2⟩,
      fun y hy hd => ⟨(h1 y hy hd).1, (h1 y hy hd).2.1, (h1 y hy hd).2.2.1⟩, fun c hc => ⟨(h2 c hc).1, (h2 c hc).2.1⟩⟩
  · rintro ⟨⟨c1, c2⟩, d1, d2⟩
    exact ⟨fun y hy hd => ⟨(d1 y hy hd).1, (d1 y hy hd).2.1, (d1 y hy hd).2.2, (c1 y hy hd).1, (c1 y hy hd).2⟩,
      fun c hc => ⟨(d2 c hc).1, (d2 c hc).2, c2 c hc⟩⟩

/-- A part `P` of `RegionUnrefAt`: after the restart from `s0`, `P` at every region
whose `H` objects are all in `D`. -/
def RegionPartAt (P : (U64 → Prop) → S → Prop) (H : P1.Heap) (D : Set U64) (s0 : S) : Prop :=
  ∀ s : S, sched.set_thread_state st s0 (L.curW s0) sched.TS_RESTART = ok s →
    ∀ lo hi : Nat, (∀ q k, H q = some k → P1.RegionD H lo hi q → q ∈ D) → P (P1.RegionD H lo hi) s

/-- (a) of `RegionUnrefAt`. -/
def RegionUnrefA (H : P1.Heap) (D : Set U64) (s0 : S) : Prop :=
  RegionPartAt (L := L) (fun R s => KeptRefsA (L := L) H R s) H D s0

/-- (b) of `RegionUnrefAt`. -/
def RegionUnrefB (H : P1.Heap) (D : Set U64) (s0 : S) : Prop :=
  RegionPartAt (L := L) (fun R s => KeptRefsB (L := L) H R s) H D s0

/-- (c) of `RegionUnrefAt`. -/
def RegionUnrefC (H : P1.Heap) (Cs D : Set U64) (s0 : S) : Prop :=
  RegionPartAt (L := L) (fun R s => DbgKeptC (L := L) H R Cs s) H D s0

/-- (d) of `RegionUnrefAt`. -/
def RegionUnrefD (H : P1.Heap) (Cs D : Set U64) (s0 : S) : Prop :=
  RegionPartAt (L := L) (fun R s => TimerKeptD (L := L) H R Cs s) H D s0

/-- **`RegionUnrefAt` without part (a)**: (b) ∧ (c) ∧ (d), the premise
`kernel_entry_reachU25` keeps. -/
def RegionUnrefBCD (H : P1.Heap) (Cs D : Set U64) (s0 : S) : Prop :=
  RegionUnrefB (L := L) H D s0 ∧ RegionUnrefC (L := L) H Cs D s0 ∧ RegionUnrefD (L := L) H Cs D s0

/-- **`RegionUnrefAt` is its four parts.** -/
theorem regionUnrefAt_iff {H : P1.Heap} {Cs D : Set U64} {s0 : S} :
    RegionUnrefAt (L := L) H Cs D s0 ↔ RegionUnrefA (L := L) H D s0 ∧ RegionUnrefB (L := L) H D s0 ∧
      RegionUnrefC (L := L) H Cs D s0 ∧ RegionUnrefD (L := L) H Cs D s0 := by
  constructor
  · intro h
    refine ⟨fun s hs lo hi hD => ?_, fun s hs lo hi hD => ?_, fun s hs lo hi hD => ?_, fun s hs lo hi hD => ?_⟩
    · exact (keptRefsP3_iff.1 (h s hs lo hi hD).1).1
    · exact (keptRefsP3_iff.1 (h s hs lo hi hD).1).2
    · exact (dbgTimerKept_iff.1 (h s hs lo hi hD).2).1
    · exact (dbgTimerKept_iff.1 (h s hs lo hi hD).2).2
  · rintro ⟨ha, hb, hc, hd⟩ s hs lo hi hD
    exact ⟨keptRefsP3_iff.2 ⟨ha s hs lo hi hD, hb s hs lo hi hD⟩,
      dbgTimerKept_iff.2 ⟨hc s hs lo hi hD, hd s hs lo hi hD⟩⟩

/-! ## The carried forms of (b)–(d) (definitions; jc6 (2)) -/

/-- **(b), carried**: every TCB's bound notification, every SC's notification and
every notification's bound TCB (dead objects' included) names no object of `D`. -/
def KeptRefsBAll (H : P1.Heap) (D : Set U64) (s : S) : Prop :=
  (∀ t ∈ H.tcbs, P1.KeptRef H (· ∈ D) (L.mem s (P1.boundA t))) ∧
  (∀ c ∈ H.scs, P1.KeptRef H (· ∈ D) (L.mem s (P1.scNtfnA c))) ∧
  (∀ n ∈ H.ntfns, P1.KeptRef H (· ∈ D) (L.mem s (P1.ntfnBtA n)))

/-- **(c), carried**: every TCB's debug links (dead TCBs' included) and every core's
debug-list head name no object of `D`. -/
def DbgKeptCAll (H : P1.Heap) (Cs D : Set U64) (s : S) : Prop :=
  (∀ y ∈ H.tcbs, P1.KeptRef H (· ∈ D) (L.mem s (P1.dnA y)) ∧ P1.KeptRef H (· ∈ D) (L.mem s (P1.dpA y))) ∧
  (∀ c ∈ Cs, P1.KeptRef H (· ∈ D) (L.mem s (L.nodeAt s c layout.node.DEBUG_TCBS)))

/-- **(d), carried**: every TCB's timer-tree links (dead TCBs' included) and every
core's timer root and minimum name no object of `D`. -/
def TimerKeptDAll (H : P1.Heap) (Cs D : Set U64) (s : S) : Prop :=
  (∀ y ∈ H.tcbs, P1.KeptRef H (· ∈ D) (L.mem s (P1.tlA y)) ∧ P1.KeptRef H (· ∈ D) (L.mem s (P1.trA y)) ∧
    P1.KeptRef H (· ∈ D) (L.mem s (P1.tpA y))) ∧
  (∀ c ∈ Cs, P1.KeptRef H (· ∈ D) (L.mem s (L.nodeAt s c layout.node.TIMER_ROOT)) ∧
    P1.KeptRef H (· ∈ D) (L.mem s (L.nodeAt s c layout.node.TIMER_MIN)))

/-- `KeptRef` at `D` gives `KeptRef` at any region whose `H` objects are in `D`. -/
theorem keptRef_mono {H : P1.Heap} {D : Set U64} {R : U64 → Prop} (hD : ∀ q k, H q = some k → R q → q ∈ D)
    {x : U64} (h : P1.KeptRef H (· ∈ D) x) : P1.KeptRef H R x := fun hx hr => by
  obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp hx
  exact h hx (hD x k hk hr)

theorem KeptRefsBAll.region {H : P1.Heap} {D : Set U64} {s : S} (h : KeptRefsBAll (L := L) H D s)
    {R : U64 → Prop} (hD : ∀ q k, H q = some k → R q → q ∈ D) : KeptRefsB (L := L) H R s :=
  ⟨fun t ht _ => keptRef_mono hD (h.1 t ht), fun c hc _ => keptRef_mono hD (h.2.1 c hc),
    fun n hn _ => keptRef_mono hD (h.2.2 n hn)⟩

theorem DbgKeptCAll.region {H : P1.Heap} {Cs D : Set U64} {s : S} (h : DbgKeptCAll (L := L) H Cs D s)
    {R : U64 → Prop} (hD : ∀ q k, H q = some k → R q → q ∈ D) : DbgKeptC (L := L) H R Cs s :=
  ⟨fun y hy _ => ⟨keptRef_mono hD (h.1 y hy).1, keptRef_mono hD (h.1 y hy).2⟩,
    fun c hc => keptRef_mono hD (h.2 c hc)⟩

theorem TimerKeptDAll.region {H : P1.Heap} {Cs D : Set U64} {s : S} (h : TimerKeptDAll (L := L) H Cs D s)
    {R : U64 → Prop} (hD : ∀ q k, H q = some k → R q → q ∈ D) : TimerKeptD (L := L) H R Cs s :=
  ⟨fun y hy _ => ⟨keptRef_mono hD (h.1 y hy).1, keptRef_mono hD (h.1 y hy).2.1, keptRef_mono hD (h.1 y hy).2.2⟩,
    fun c hc => ⟨keptRef_mono hD (h.2 c hc).1, keptRef_mono hD (h.2 c hc).2⟩⟩

end

/-! ## (a) at `JAtZ` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **A dead reply is free**: on no call stack, with null links (`DeadP`'s `rTcb`,
`IpcRel.reply`, `RFree`). -/
theorem JAtZ.replyDead (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {y : U64} (hy : y ∈ Z.R) (hyD : y ∈ D) :
    Detached Z.C Lst y ∧ L.mem s (P1.rNextA y) = 0#u64 ∧ L.mem s (P1.rPrevA y) = 0#u64 := by
  have hH : H y = some .reply := J.zH.2.2.1 y hy
  have d : L.mem s (P1.rTcbA y) = 0#u64 := (J.jcov.dead y hyD).2.2.2.1 hH
  obtain ⟨x, hk, hx⟩ := J.xtop.ipc.reply y hy
  have hn : x.replyTcb = none := by
    rw [hx]; show optRef (L.mem s (P1.rTcbA y)) = none; rw [d]; exact optRef_zero
  exact J.rfree y hy ⟨x, hk, hn⟩

/-- A reply of `Z.R` is even (5-bit aligned in `H`). -/
theorem JAtZ.replyEven (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {y : U64} (hy : y ∈ Z.R) :
    y.val % 2 = 0 := by
  have := J.kern.heap.align y _ (J.zH.2.2.1 y hy)
  simp only [P1.HKind.bits] at this
  omega

/-- The masked link of a reply: zero, or a live reply. -/
theorem JAtZ.keptMasked (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {Rg : U64 → Prop}
    (hD : ∀ q k, H q = some k → Rg q → q ∈ D) {x : U64}
    (hx : x = 0#u64 ∨ (x ∈ Z.R ∧ x ∉ D)) : P1.KeptRef H Rg (x &&& ~~~1#u64) := by
  rcases hx with rfl | ⟨hxR, hxD⟩
  · rw [P1.zero_or_masked]; intro h; exact absurd J.kern.h0 h
  · rw [and_not1 x (J.replyEven hxR)]
    intro hH hr
    obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp hH
    exact hxD (hD x k hk hr)

/-- A reply on a call stack is live. -/
theorem JAtZ.stackLive (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {sc : U64} (hsc : sc ∈ Z.C)
    {y : U64} (hy : y ∈ Lst sc) : y ∈ Z.R ∧ y ∉ D := by
  have hyR := (J.call.stack sc hsc).2.1 y hy
  exact ⟨hyR, fun hyD => (J.replyDead hyR hyD).1 sc hsc hy⟩

/-- **(a) at every `JAtZ` state**, at every region (any `Rg`) whose `H` objects are
all dead (module docstring). -/
theorem JAtZ.keptA (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {Rg : U64 → Prop}
    (hD : ∀ q k, H q = some k → Rg q → q ∈ D) : KeptRefsA (L := L) H Rg s := by
  have h0 := J.kern.h0
  have hk0 : ∀ x : U64, x = 0#u64 → P1.KeptRef H Rg x := fun x e h => by subst e; exact absurd h0 h
  have hlive : ∀ x : U64, (H x ≠ none → x ∉ D) → P1.KeptRef H Rg x := fun x h hH hr => by
    obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp hH
    exact h hH (hD x k hk hr)
  have hr0 : ∀ r ∈ P1.Heap.replies H, r ≠ 0#u64 := fun r hr e => by
    subst e; have : H 0#u64 = some .reply := hr; rw [h0] at this; cases this
  obtain ⟨Q, R, hc, hs⟩ := J.xtop.fin.1.1.1.lists
  refine ⟨fun r hr _ hhb => ?_, fun r hr _ => ?_, fun c hc' _ => ?_, fun t ht _ => ?_, fun c hc' _ => ?_⟩
  · -- a reply's next link
    have hrR : r ∈ Z.R := J.hset.2.2 r hr
    by_cases hon : ∃ sc ∈ Z.C, r ∈ Lst sc
    · obtain ⟨sc, hsc, hm⟩ := hon
      obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.mp hm
      have hW := ((J.call.stack sc hsc).2.2.2.2 i hi).2
      rw [e] at hW
      rw [hW] at hhb ⊢
      cases i with
      | zero => rw [headBit_or1] at hhb; cases hhb
      | succ j =>
        have hj : j < (Lst sc).length := by omega
        show P1.KeptRef H Rg ((Lst sc).getD j 0#u64 &&& ~~~1#u64)
        rw [List.getD_eq_getElem _ _ hj]
        exact J.keptMasked hD (Or.inr (J.stackLive hsc (List.getElem_mem hj)))
    · have hdet : Detached Z.C Lst r := fun sc hsc hm => hon ⟨sc, hsc, hm⟩
      obtain ⟨-, hn, -⟩ := J.call.det r hrR hdet
      refine J.keptMasked hD ?_
      by_cases hz : L.mem s (P1.rNextA r) = 0#u64
      · exact Or.inl hz
      · obtain ⟨hR, -, hb⟩ := hn hz
        exact Or.inr ⟨hR, fun hd => hr0 r hr (by rw [← hb]; exact (J.replyDead hR hd).2.2)⟩
  · -- a reply's previous link
    have hrR : r ∈ Z.R := J.hset.2.2 r hr
    by_cases hon : ∃ sc ∈ Z.C, r ∈ Lst sc
    · obtain ⟨sc, hsc, hm⟩ := hon
      obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.mp hm
      have hW := ((J.call.stack sc hsc).2.2.2.2 i hi).1
      rw [e] at hW
      rw [hW]
      refine J.keptMasked hD ?_
      by_cases hj : i + 1 < (Lst sc).length
      · rw [List.getD_eq_getElem _ _ hj]
        exact Or.inr (J.stackLive hsc (List.getElem_mem hj))
      · left; rw [List.getD_eq_default _ _ (by omega)]
    · have hdet : Detached Z.C Lst r := fun sc hsc hm => hon ⟨sc, hsc, hm⟩
      obtain ⟨-, -, hp⟩ := J.call.det r hrR hdet
      refine J.keptMasked hD ?_
      by_cases hz : L.mem s (P1.rPrevA r) = 0#u64
      · exact Or.inl hz
      · obtain ⟨hR, -, hb⟩ := hp hz
        exact Or.inr ⟨hR, fun hd => hr0 r hr (by rw [← hb]; exact (J.replyDead hR hd).2.1)⟩
  · -- an SC's reply head
    obtain ⟨z, hz⟩ := hc'
    have hcC : c ∈ Z.C := J.hscC c z hz
    have hW := (J.call.stack c hcC).2.2.2.1
    rw [hW]
    cases hL : Lst c with
    | nil => exact hk0 _ rfl
    | cons y ys =>
      have hy : y ∈ Lst c := by rw [hL]; exact List.mem_cons_self
      obtain ⟨hyR, hyD⟩ := J.stackLive hcC hy
      exact hlive _ fun _ => hyD
  · -- a TCB's yield-to link
    have htT : t ∈ Z.T := by rw [J.tcbs_eq.1]; exact ht
    by_cases hz : L.mem s (P1.yieldA t) = 0#u64
    · exact hk0 _ hz
    obtain ⟨hyC, y, n, hky, hyf⟩ := J.yld.toSc t htT hz
    refine hlive _ fun _ hd => ?_
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    have hH := (hJ.sc _ y n (J.c0 _ hyC) hky).2
    have d := ((J.jcov.dead _ hd).2.2.2.2 _ hH).2.2.2
    obtain ⟨y0, n0, hk0', hx⟩ := hs.scs _ hyC
    rw [hky] at hk0'; cases hk0'
    have : y.scYieldFrom = none := by
      rw [hx.yieldFrom, ← scYieldFromA_eq, d]; exact optRef_zero
    rw [hyf] at this; cases this
  · -- an SC's yield-from link
    obtain ⟨z, hz⟩ := hc'
    have hcC : c ∈ Z.C := J.hscC c z hz
    by_cases hw : L.mem s (P1.scYieldFromA c) = 0#u64
    · exact hk0 _ hw
    obtain ⟨y, n, hky, hx⟩ := hs.scs c hcC
    have hyf : y.scYieldFrom = some (L.mem s (P1.scYieldFromA c)).bv := by
      rw [hx.yieldFrom, ← scYieldFromA_eq]; exact Notif.optRef_ne hw
    obtain ⟨t, htT, htb, hyt⟩ := J.yld.frm c hcC y n hky _ hyf
    have et : t = L.mem s (P1.scYieldFromA c) := P1.eq_of_bv htb
    refine hlive _ fun _ hd => ?_
    rw [← et] at hd
    have d := ((J.jcov.dead t hd).1 (J.zH.1 t htT)).2.2.2.2.2
    rw [hyt] at d
    exact J.c0 c hcC d

/-- **(a) of `RegionUnrefAt` at an `Entered` `JAtZ` state**: `keptA` at the restart's
`JAtZ` (`JAtZ.restartSJ`, the same `H` and `D`). -/
theorem JAtZ.unrefA (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) :
    RegionUnrefA (L := L) H D s := by
  intro s1 hs1 lo hi hD
  have hct : sched.cur_thread st s = ok (L.curW s) := cur_thread_eq s
  obtain ⟨hcur, x, hk, hrun⟩ := J.curRunnable hni hct
  have htcb : Z.th (L.curW s) = some .tcb := (J.xtop.curTcb hcur).1
  obtain ⟨Ac', Lst', J1⟩ := J.restartSJ (jStepHyps arI) hcur hk htcb hrun hs1
  exact J1.keptA hD

/-- **`RegionUnrefAt` from (b) ∧ (c) ∧ (d)** at an `Entered` `JAtZ` state. -/
theorem JAtZ.regionUnrefAt (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ)
    (h : RegionUnrefBCD (L := L) H Cs D s) : RegionUnrefAt (L := L) H Cs D s :=
  regionUnrefAt_iff.2 ⟨J.unrefA hni, h⟩

end

end

end Fl4Proofs.P3
