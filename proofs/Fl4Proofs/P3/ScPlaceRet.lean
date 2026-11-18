/-
P3 (DESIGN.md §9): **`JCovD` across retype** (ScPlaceDead's dead set, with
retype's exposed post `RetExp`, UntypedExp).

* `ut_free_fi`: a covered range misses an untyped cap's free part (`noov`),
  so with `ut_free` (a childless cap's whole region) every object meeting
  the new objects' window is uncovered, hence dead (`retype_window_dead`).
* `RetypeP1Hyp`: P1's half, as one hypothesis in P1's shape: from `BlkOK`
  over a heap `H` whose objects meeting the window are dead, the retype
  ends in `BlkOK` over a heap `H'` keeping `H`'s objects off the window,
  dropping the ones on it, adding new ones only at the new caps (each at
  most a window slot), with the dead objects kept dead.
* `JCovD.retype`: the typed heap and `H'` after are covered or dead, with
  the dead set minus the new objects' addresses.
-/
import Fl4Proofs.P3.ScPlaceDead
import Fl4Proofs.P3.UntypedExp
import Fl4Proofs.P1.QueueRetypeTcb
import Fl4Proofs.P3.UntypedTcbLoop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P3 Fl4Proofs.P1

noncomputable section

/-- **A covered range misses an untyped cap's free part.** -/
theorem ut_free_fi {mem : U64 → U64} {G : MdbGhost} (hU : UtInv mem G) {x : U64}
    (hx : x ∈ G.chains.flatten) {p sb fi : U64} {d : Bool} (hcx : capV mem x = .Untyped p sb fi d)
    {lo hi : Nat} (hlh : lo < hi) (hc : Covered mem G lo hi) :
    hi ≤ p.val + fi.val ∨ p.val + 2 ^ sb.val ≤ lo := by
  obtain ⟨y, hy, hp, hut, hb, ht⟩ := hc
  have hreg := hU.reg y hy hp
  rcases hU.noov x hx p sb fi d hcx y hy hp with h | ⟨h, -⟩
  · unfold DisjR at h; omega
  · rw [hut] at h; cases h

/-- The window `[A, A + w k)` met by `[lo, hi)`. -/
def MeetsW (A k w lo hi : Nat) : Prop := ¬ (hi ≤ A ∨ A + w * k ≤ lo)

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {th th' : TypedHeap} {H H' : Heap} {G G' : MdbGhost} {D Cs : Set U64} {s s' : S} {m' : U64 → U64}
  {A k w : Nat} {dslot : Nat → U64} {cj : Nat → capability.Cap} {xs : U64}

/-- **The source cap's region holds the window, the idle objects outside
it** (`idleOut`, the source a RAM untyped). -/
theorem src_idleOut (h : JCovD (L := L) th H G D Cs s) (hE : RetExp th th' (L.mem s) m' G G' A k w dslot cj xs)
    (hdv : ∃ p0 sb0 fi0, capV (L.mem s) xs = .Untyped p0 sb0 fi0 false) :
    ∃ p1 sb1 : U64, p1.val ≤ A ∧ A + w * k ≤ p1.val + 2 ^ sb1.val ∧ ∀ q, IdleAt (L := L) s q →
      (q.val < p1.val ∨ p1.val + 2 ^ sb1.val ≤ q.val) ∧
      (∀ kd, th q = some kd → q.val + max (objSize kd) 1 ≤ p1.val ∨ p1.val + 2 ^ sb1.val ≤ q.val) ∧
      (∀ kd, H q = some kd → q.val + 2 ^ kd.bits ≤ p1.val ∨ p1.val + 2 ^ sb1.val ≤ q.val) := by
  obtain ⟨hxs, p1, sb1, fi1, fi2, d1, hcs, -, hpA, -, hAs, -, -⟩ := hE.usrc
  obtain ⟨p0, sb0, fi0, hc0⟩ := hdv
  rw [hc0] at hcs
  simp only [capability.Cap.Untyped.injEq] at hcs
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hcs
  exact ⟨p0, sb0, hpA, hAs, h.idleOut xs hxs p0 sb0 fi0 hc0⟩

/-- **The source cap's region holds the window, off the kernel-state
block** (`UtKsApart`, the source a RAM untyped). -/
theorem src_ks (h : JCovD (L := L) th H G D Cs s) (hE : RetExp th th' (L.mem s) m' G G' A k w dslot cj xs)
    (hdv : ∃ p0 sb0 fi0, capV (L.mem s) xs = .Untyped p0 sb0 fi0 false) :
    ∃ p1 sb1 : U64, p1.val ≤ A ∧ A + w * k ≤ p1.val + 2 ^ sb1.val ∧
      (p1.val + 2 ^ sb1.val ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ p1.val) := by
  obtain ⟨hxs, p1, sb1, fi1, fi2, d1, hcs, -, hpA, -, hAs, -, -⟩ := hE.usrc
  obtain ⟨p0, sb0, fi0, hc0⟩ := hdv
  rw [hc0] at hcs
  simp only [capability.Cap.Untyped.injEq] at hcs
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hcs
  exact ⟨p0, sb0, hpA, hAs, (h.ks xs hxs p0 sb0 fi0 hc0).1⟩

/-- **No new object in the kernel-state block** (`src_ks`). -/
theorem newQ_not_ks (h : JCovD (L := L) th H G D Cs s)
    (hE : RetExp th th' (L.mem s) m' G G' A k w dslot cj xs)
    (hdv : ∃ p0 sb0 fi0, capV (L.mem s) xs = .Untyped p0 sb0 fi0 false) {q : U64} (hn : NewQ A k w cj q)
    (h1 : (L.ksb s).val ≤ q.val) (h2 : q.val < (L.ksb s).val + 13568) : False := by
  obtain ⟨p1, sb1, hpA, hAs, hko⟩ := src_ks h hE hdv
  obtain ⟨j, hj, hv, -⟩ := hn
  have h3 : (j + 1) * k ≤ w * k := Nat.mul_le_mul_right _ hj
  rw [Nat.add_mul, Nat.one_mul] at h3
  have := hE.k1
  omega

/-- **The objects meeting the new objects' window are dead**: uncovered
(`ut_free_fi`, `ut_free`), so in the dead set; not idle, the source a RAM
untyped (`src_idleOut`). -/
theorem retype_window_dead (h : JCovD (L := L) th H G D Cs s) (hU : UtInv (L.mem s) G) (hI : MdbInv (L.mem s) G)
    (hE : RetExp th th' (L.mem s) m' G G' A k w dslot cj xs)
    (hdv : ∃ p0 sb0 fi0, capV (L.mem s) xs = .Untyped p0 sb0 fi0 false) :
    (∀ q kd, H q = some kd → MeetsW A k w q.val (q.val + 2 ^ kd.bits) → q ∈ D ∧ DeadP (L := L) H s q) ∧
    (∀ q kd, th q = some kd → MeetsW A k w q.val (q.val + max (objSize kd) 1) → q ∈ D ∧ DeadP (L := L) H s q) := by
  obtain ⟨x0, hx0, p0, sb0, fi0, d0, hc0, h1, h2, h3⟩ := hE.src
  have miss : ∀ {lo hi : Nat}, lo < hi → MeetsW A k w lo hi → ¬ Covered (L.mem s) G lo hi := by
    intro lo hi hlh hm hc
    unfold MeetsW at hm
    rcases h3 with h3 | h3
    · rcases ut_free_fi hU hx0 hc0 hlh hc with e | e <;> omega
    · rcases ut_free hU hI hx0 hc0 h3 hlh hc with e | e <;> omega
  obtain ⟨p1, sb1, hpA, hAs, io⟩ := src_idleOut h hE hdv
  obtain ⟨p2, sb2, hpA2, hAs2, hko⟩ := src_ks h hE hdv
  refine ⟨fun q kd hq hm => ?_, fun q kd hq hm => ?_⟩
  · rcases h.h q kd hq with hc | hd | hi | hi
    · exact absurd hc (miss (by have := Nat.one_le_two_pow (n := kd.bits); omega) hm)
    · exact ⟨hd, h.dead q hd⟩
    · have := (io q hi).2.2 kd hq
      unfold MeetsW at hm; omega
    · obtain ⟨k1, k2⟩ := hi.2 kd hq
      unfold MeetsW at hm; omega
  · rcases h.th q kd hq with hc | hd | hi | hi
    · exact absurd hc (miss (by omega) hm)
    · exact ⟨hd, h.dead q hd⟩
    · have := (io q hi).2.1 kd hq
      unfold MeetsW at hm; omega
    · obtain ⟨k1, k2⟩ := hi.1 kd hq
      unfold MeetsW at hm; omega

/-- **No new object at an idle address**: the window lies in an untyped
region, the idle objects outside (`idleOut`). -/
theorem newQ_not_idle (h : JCovD (L := L) th H G D Cs s)
    (hE : RetExp th th' (L.mem s) m' G G' A k w dslot cj xs)
    (hdv : ∃ p0 sb0 fi0, capV (L.mem s) xs = .Untyped p0 sb0 fi0 false) {q : U64} (hn : NewQ A k w cj q)
    (hi : IdleAt (L := L) s q) : False := by
  obtain ⟨p1, sb1, h1, h2, io⟩ := src_idleOut h hE hdv
  obtain ⟨j, hj, hv, -⟩ := hn
  have := (io q hi).1
  have h3 : (j + 1) * k ≤ w * k := Nat.mul_le_mul_right _ hj
  rw [Nat.add_mul, Nat.one_mul] at h3
  have := hE.k1
  omega

/-- A new object's range is covered by its new cap. -/
theorem _root_.Fl4Proofs.P3.RetExp.cov_new {m m' : U64 → U64} (hE : RetExp th th' m m' G G' A k w dslot cj xs) {q : U64}
    (hq : NewQ A k w cj q) {n : Nat} (hn : n ≤ k) : Covered m' G' q.val (q.val + n) := by
  obtain ⟨j, hj, hv, hu⟩ := hq
  refine ⟨dslot j, hE.newm j hj, by rw [hE.newc j hj]; exact hE.cphys j hj, by rw [hE.newc j hj]; exact hu,
    by rw [hE.newc j hj, hE.cbase j hj, hv], ?_⟩
  rw [hE.newc j hj, hE.ctop j hj, hv]
  have := hE.k1
  omega

/-- **A RAM untyped region after lies in a RAM untyped region before** (a
new cap's in the source's, the source a RAM untyped; an old cap's is its
own, the source keeping its region and device flag). -/
theorem ram_from (hE : RetExp th th' (L.mem s) m' G G' A k w dslot cj xs)
    (hdv : ∃ p0 sb0 fi0, capV (L.mem s) xs = .Untyped p0 sb0 fi0 false) {x : U64} (hx : x ∈ G'.chains.flatten)
    {p sb fi : U64} (hcx : capV m' x = .Untyped p sb fi false) :
    ∃ x0 ∈ G.chains.flatten, ∃ p0 sb0 fi0 : U64, capV (L.mem s) x0 = .Untyped p0 sb0 fi0 false ∧
      p0.val ≤ p.val ∧ p.val + 2 ^ sb.val ≤ p0.val + 2 ^ sb0.val := by
  obtain ⟨hxs, p1, sb1, fi1, fi2, d1, hcs, hcs', hpA, -, hAs, -, hoth⟩ := hE.usrc
  by_cases hnew : ∃ j, j < w ∧ x = dslot j
  · obtain ⟨j, hj, rfl⟩ := hnew
    obtain ⟨p0, sb0, fi0, hc0⟩ := hdv
    rw [hc0] at hcs
    simp only [capability.Cap.Untyped.injEq] at hcs
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hcs
    have hc := hE.newc j hj
    rw [hcx] at hc
    have hb := hE.cbase j hj
    have ht := hE.ctop j hj
    rw [← hc] at hb ht
    have := hE.k1
    obtain ⟨b1, t1, -⟩ := ut_range (capV_ut_sb hcx) (by rw [hb, ht]; omega)
    have h3 : (j + 1) * k ≤ w * k := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, Nat.one_mul] at h3
    have h4 := Nat.one_le_two_pow (n := sb.val)
    exact ⟨xs, hxs, p0, sb0, fi0, hc0, by omega, by omega⟩
  · have hxG : x ∈ G.chains.flatten := by
      rcases hE.gmem x hx with h' | ⟨j, hj, e⟩
      · exact h'
      · exact absurd ⟨j, hj, e⟩ hnew
    cases hu : isUt (capV (L.mem s) x)
    · have := (hE.keep x hxG hu).2
      rw [hcx] at this
      rw [← this] at hu; cases hu
    · by_cases ex : x = xs
      · rw [ex, hcs'] at hcx
        simp only [capability.Cap.Untyped.injEq] at hcx
        obtain ⟨e1, e2, -, e4⟩ := hcx
        rw [e1, e2, e4] at hcs
        exact ⟨xs, hxs, p, sb, fi1, hcs, le_rfl, le_rfl⟩
      · have e := hoth x hxG hu ex
        rw [hcx] at e
        exact ⟨x, hxG, p, sb, fi, e.symm, le_rfl, le_rfl⟩

/-- **`JCovD` across retype** (module docstring): `H'` from P1's
`RetypeP1Hyp`, the dead set losing the new objects' addresses. -/
theorem JCovD.retype (h : JCovD (L := L) th H G D Cs s)
    (hE : RetExp th th' (L.mem s) (L.mem s') G G' A k w dslot cj xs)
    (hH' : ∀ q kd, H' q = some kd → (H q = some kd ∧ ¬ NewQ A k w cj q) ∨ (NewQ A k w cj q ∧ 2 ^ kd.bits ≤ k))
    (hdead : ∀ q ∈ D, ¬ NewQ A k w cj q → H' q = H q → DeadP (L := L) H s q → DeadP (L := L) H' s' q)
    (hksb : L.ksb s' = L.ksb s) (hidl : IdleKeep (L := L) s s')
    (hdv : ∃ p0 sb0 fi0, capV (L.mem s) xs = .Untyped p0 sb0 fi0 false) :
    JCovD (L := L) th' H' G' {q | q ∈ D ∧ ¬ NewQ A k w cj q} Cs s' := by
  have hkeep : ∀ y ∈ G.chains.flatten, physF (capV (L.mem s) y) = true → isUt (capV (L.mem s) y) = false →
      y ∈ G'.chains.flatten ∧ capV (L.mem s') y = capV (L.mem s) y := fun y hy _ hu => hE.keep y hy hu
  -- an object inside the kernel-state block stays so: no new object there
  have hKs : ∀ q, KsObj (L := L) th H s q → (L.ksb s).val ≤ q.val → q.val < (L.ksb s).val + 13568 →
      KsObj (L := L) th' H' s' q := by
    intro q hq h1 h2
    refine ⟨fun kd hk => ?_, fun kd hk => ?_⟩
    · rcases hE.th q kd hk with ⟨ho, -⟩ | ⟨hn, -⟩
      · have := hq.1 kd ho; unfold KsIn at this ⊢; rw [hksb]; exact this
      · exact (newQ_not_ks h hE hdv hn h1 h2).elim
    · rcases hH' q kd hk with ⟨ho, -⟩ | ⟨hn, -⟩
      · have := hq.2 kd ho; unfold KsIn at this ⊢; rw [hksb]; exact this
      · exact (newQ_not_ks h hE hdv hn h1 h2).elim
  refine ⟨fun q kd hq => ?_, fun q kd hq => ?_, fun q ⟨hd, hn⟩ => ?_, fun x hx p sb fi hcx => ?_,
    fun x hx p sb fi hcx q hi => ?_⟩
  · rcases hE.th q kd hq with ⟨ho, h0⟩ | ⟨hn, hsz⟩
    · rcases h.th q kd ho with hc | hd | hi
      · exact Or.inl (covered_keep hc hkeep)
      · by_cases hn : NewQ A k w cj q
        · exact Or.inl (hE.cov_new hn (by rw [h0 hn]; have := hE.k1; omega))
        · exact Or.inr (Or.inl ⟨hd, hn⟩)
      · rcases hi with hi | hi
        · exact Or.inr (Or.inr (Or.inl ((idleAt_of hidl).2 hi)))
        · obtain ⟨k1, k2⟩ := hi.1 kd ho
          have := le_max_right (objSize kd) 1
          exact Or.inr (Or.inr (Or.inr (hKs q hi k1 (by omega))))
    · exact Or.inl (hE.cov_new hn (by have := hE.k1; omega))
  · rcases hH' q kd hq with ⟨ho, hn⟩ | ⟨hn, hsz⟩
    · rcases h.h q kd ho with hc | hd | hi
      · exact Or.inl (covered_keep hc hkeep)
      · exact Or.inr (Or.inl ⟨hd, hn⟩)
      · rcases hi with hi | hi
        · exact Or.inr (Or.inr (Or.inl ((idleAt_of hidl).2 hi)))
        · obtain ⟨k1, k2⟩ := hi.2 kd ho
          have := Nat.one_le_two_pow (n := kd.bits)
          exact Or.inr (Or.inr (Or.inr (hKs q hi k1 (by omega))))
    · exact Or.inl (hE.cov_new hn hsz)
  · cases hq : H' q with
    | none =>
      refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_, fun z e => ?_⟩ <;> rw [hq] at e <;> cases e
    | some kd =>
      rcases hH' q kd hq with ⟨ho, -⟩ | ⟨hn', -⟩
      · exact hdead q hd hn (hq.trans ho.symm) (h.dead q hd)
      · exact absurd hn' hn
  · obtain ⟨x0, hx0, p0, sb0, fi0, hc0, h1, h2⟩ := ram_from hE hdv hx hcx
    obtain ⟨k1, k2⟩ := h.ks x0 hx0 p0 sb0 fi0 hc0
    have hnb : ∀ c, L.nodeBase s' c = L.nodeBase s c := fun c => by simp [LawfulStore.nodeBase, hksb]
    refine ⟨by rw [hksb]; omega, fun c hc => ?_⟩
    rw [hnb]; have := k2 c hc; omega
  · -- the idle objects: outside the old region holding the new one, and no new object
    have hi0 := (idleAt_of hidl).1 hi
    -- a RAM untyped region after lies in one before, of a RAM cap (a new cap's in the source's)
    obtain ⟨p0, sb0, h1, h2, o1, o2, o3⟩ : ∃ p0 sb0 : U64, p0.val ≤ p.val ∧ p.val + 2 ^ sb.val ≤ p0.val + 2 ^ sb0.val ∧
        (q.val < p0.val ∨ p0.val + 2 ^ sb0.val ≤ q.val) ∧
        (∀ kd, th q = some kd → q.val + max (objSize kd) 1 ≤ p0.val ∨ p0.val + 2 ^ sb0.val ≤ q.val) ∧
        (∀ kd, H q = some kd → q.val + 2 ^ kd.bits ≤ p0.val ∨ p0.val + 2 ^ sb0.val ≤ q.val) := by
      by_cases hnew : ∃ j, j < w ∧ x = dslot j
      · obtain ⟨j, hj, rfl⟩ := hnew
        obtain ⟨p1, sb1, hpA, hAs, io⟩ := src_idleOut h hE hdv
        have hc := hE.newc j hj
        rw [hcx] at hc
        have hb := hE.cbase j hj
        have ht := hE.ctop j hj
        rw [← hc] at hb ht
        have := hE.k1
        obtain ⟨b1, t1, -⟩ := ut_range (capV_ut_sb hcx) (by rw [hb, ht]; omega)
        have h3 : (j + 1) * k ≤ w * k := Nat.mul_le_mul_right _ hj
        rw [Nat.add_mul, Nat.one_mul] at h3
        have h4 := Nat.one_le_two_pow (n := sb.val)
        exact ⟨p1, sb1, by omega, by omega, io q hi0⟩
      · have hxG : x ∈ G.chains.flatten := by
          rcases hE.gmem x hx with h' | ⟨j, hj, e⟩
          · exact h'
          · exact absurd ⟨j, hj, e⟩ hnew
        obtain ⟨hxs, p1, sb1, fi1, fi2, d1, hcs, hcs', -, -, -, -, hoth⟩ := hE.usrc
        cases hu : isUt (capV (L.mem s) x)
        · have := (hE.keep x hxG hu).2
          rw [hcx] at this
          rw [← this] at hu; cases hu
        · by_cases ex : x = xs
          · rw [ex, hcs'] at hcx
            simp only [capability.Cap.Untyped.injEq] at hcx
            obtain ⟨e1, e2, -, e4⟩ := hcx
            rw [e1, e2, e4] at hcs
            exact ⟨p, sb, le_rfl, le_rfl, h.idleOut xs hxs p sb fi1 hcs q hi0⟩
          · have e := hoth x hxG hu ex
            rw [hcx] at e
            exact ⟨p, sb, le_rfl, le_rfl, h.idleOut x hxG p sb fi e.symm q hi0⟩
    refine ⟨by omega, fun kd hq => ?_, fun kd hq => ?_⟩
    · rcases hE.th q kd hq with ⟨ho, -⟩ | ⟨hn, -⟩
      · have := o2 kd ho; omega
      · exact (newQ_not_idle h hE hdv hn hi0).elim
    · rcases hH' q kd hq with ⟨ho, -⟩ | ⟨hn, -⟩
      · have := o3 kd ho; omega
      · exact (newQ_not_idle h hE hdv hn hi0).elim

end

/-- **P1's half of retype** (module docstring), in P1's shape: the heaps'
canonical sets, the window `[A, A + w k)` and the new addresses `New`. -/
def RetypeP1Hyp {S : Type} (st : machine.Store S) [L : P1.LawfulStore st] (s s' : S) (H : Heap) (Cs Ac : Set U64)
    (A k w : Nat) (New : U64 → Prop) : Prop :=
  BlkOK st (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H)
      (Heap.scBits H) Ac s →
    (∀ q kd, H q = some kd → MeetsW A k w q.val (q.val + 2 ^ kd.bits) → DeadP (L := L) H s q) →
    ∃ (H' : Heap) (Ac' : Set U64),
      BlkOK st (Heap.tcbs H') Cs (Heap.omega H') H' (Heap.frame H') (Heap.replies H') (Heap.scs H') (Heap.ntfns H')
        (Heap.scBits H') Ac' s' ∧
      (∀ q kd, H q = some kd → ¬ MeetsW A k w q.val (q.val + 2 ^ kd.bits) → H' q = some kd) ∧
      (∀ q kd, H' q = some kd → (H q = some kd ∧ ¬ MeetsW A k w q.val (q.val + 2 ^ kd.bits)) ∨
        (New q ∧ 2 ^ kd.bits ≤ k)) ∧
      (∀ q, H' q = H q → DeadP (L := L) H s q → DeadP (L := L) H' s' q)

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {th th' : TypedHeap} {H : Heap} {G G' : MdbGhost} {D Cs Ac : Set U64} {s s' : S}
  {A k w : Nat} {dslot : Nat → U64} {cj : Nat → capability.Cap} {xs : U64}

/-- **`JCovD` and `BlkOK` across retype, from P1's `RetypeP1Hyp`**: the
window's objects are dead (`retype_window_dead`), so P1's half applies. -/
theorem JCovD.retype_p1 (h : JCovD (L := L) th H G D Cs s) (hU : UtInv (L.mem s) G) (hI : MdbInv (L.mem s) G)
    (hE : RetExp th th' (L.mem s) (L.mem s') G G' A k w dslot cj xs) (hksb : L.ksb s' = L.ksb s)
    (hb : BlkOK st (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H)
      (Heap.scBits H) Ac s)
    (hP1 : RetypeP1Hyp st s s' H Cs Ac A k w (NewQ A k w cj)) (hidl : IdleKeep (L := L) s s')
    (hdv : ∃ p0 sb0 fi0, capV (L.mem s) xs = .Untyped p0 sb0 fi0 false) :
    ∃ (H' : Heap) (Ac' : Set U64),
      BlkOK st (Heap.tcbs H') Cs (Heap.omega H') H' (Heap.frame H') (Heap.replies H') (Heap.scs H') (Heap.ntfns H')
        (Heap.scBits H') Ac' s' ∧
      JCovD (L := L) th' H' G' {q | q ∈ D ∧ ¬ NewQ A k w cj q} Cs s' := by
  obtain ⟨H', Ac', hb', -, hshape, hdead⟩ := hP1 hb fun q kd hq hm => ((retype_window_dead h hU hI hE hdv).1 q kd hq hm).2
  refine ⟨H', Ac', hb', h.retype hE (fun q kd hq => ?_) (fun q _ _ e hd => hdead q e hd) hksb hidl hdv⟩
  rcases hshape q kd hq with ⟨ho, hm⟩ | hn
  · refine Or.inl ⟨ho, fun hn => hm ?_⟩
    obtain ⟨j, hj, hv, -⟩ := hn
    unfold MeetsW
    have h1 : (j + 1) * k ≤ w * k := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, Nat.one_mul] at h1
    have := Nat.one_le_two_pow (n := kd.bits)
    have := hE.k1
    omega
  · exact Or.inr hn

end

/-! ## From P1's `RetypeP1Step` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {th th' : TypedHeap} {H : Heap} {G G' : MdbGhost} {D Cs Ac : Set U64} {s s' : S}
  {A k w : Nat} {dslot : Nat → U64} {cj : Nat → capability.Cap} {xs : U64}

/-- P3's dead objects are P1's. -/
theorem DeadP_iff {q : U64} : DeadP (L := L) H s q ↔ DeadQ st H s q := Iff.rfl

/-- **The objects meeting a region of an untyped cap's free part, or of a
childless untyped cap, are dead** (uncovered, so in the dead set). -/
theorem region_dead (h : JCovD (L := L) th H G D Cs s) (hU : UtInv (L.mem s) G) (hI : MdbInv (L.mem s) G)
    {lo hi : Nat} {x0 : U64} (hx0 : x0 ∈ G.chains.flatten) {p0 sb0 fi0 : U64}
    (hc0 : capV (L.mem s) x0 = .Untyped p0 sb0 fi0 false)
    (hreg : (p0.val + fi0.val ≤ lo ∧ hi ≤ p0.val + 2 ^ sb0.val) ∨
      ((∀ y, ¬ Mdb.Desc G.par y x0) ∧ p0.val ≤ lo ∧ hi ≤ p0.val + 2 ^ sb0.val)) :
    ∀ q kd, H q = some kd → MeetsR lo hi q.val (q.val + 2 ^ kd.bits) → q ∈ D ∧ DeadP (L := L) H s q := by
  intro q kd hq hm
  unfold MeetsR at hm
  rcases h.h q kd hq with hc | hd | hi
  · exfalso
    have hlh : q.val < q.val + 2 ^ kd.bits := by have := Nat.one_le_two_pow (n := kd.bits); omega
    rcases hreg with ⟨h1, h2⟩ | ⟨hnd, h1, h2⟩
    · rcases ut_free_fi hU hx0 hc0 hlh hc with e | e <;> omega
    · rcases ut_free hU hI hx0 hc0 hnd hlh hc with e | e <;> omega
  · exact ⟨hd, h.dead q hd⟩
  · rcases hi with hi | hi
    · have := (h.idleOut x0 hx0 p0 sb0 fi0 hc0 q hi).2.2 kd hq
      rcases hreg with ⟨h1, h2⟩ | ⟨-, h1, h2⟩ <;> omega
    · obtain ⟨k1, k2⟩ := hi.2 kd hq
      have := (h.ks x0 hx0 p0 sb0 fi0 hc0).1
      rcases hreg with ⟨h1, h2⟩ | ⟨-, h1, h2⟩ <;> omega

/-- **`JCovD` and `BlkOK` across retype from P1's `RetypeP1Step`** (the
region `[lo, hi)` of an untyped cap's free part or of a childless one,
holding the window; the new caps non-untyped when the new objects are heap
objects). -/
theorem JCovD.retype_step (h : JCovD (L := L) th H G D Cs s) (hU : UtInv (L.mem s) G) (hI : MdbInv (L.mem s) G)
    (hE : RetExp th th' (L.mem s) (L.mem s') G G' A k w dslot cj xs) (hksb : L.ksb s' = L.ksb s)
    {lo hi n us : Nat} {x0 : U64} (hx0 : x0 ∈ G.chains.flatten) {p0 sb0 fi0 : U64} {d0 : Bool}
    (hc0 : capV (L.mem s) x0 = .Untyped p0 sb0 fi0 d0)
    (hreg : (p0.val + fi0.val ≤ lo ∧ hi ≤ p0.val + 2 ^ sb0.val) ∨
      ((∀ y, ¬ Mdb.Desc G.par y x0) ∧ p0.val ≤ lo ∧ hi ≤ p0.val + 2 ^ sb0.val))
    (hlo : lo ≤ A) (hhi : A + w * k ≤ hi) (hbits : ∀ kd, newKind n us = some kd → 2 ^ kd.bits ≤ k)
    (hcj : (newKind n us).isSome → ∀ j, j < w → isUt (cj j) = false)
    (hcur : ¬ (lo ≤ (L.curW s).val ∧ (L.curW s).val < hi))
    (hw : WritesIn st s s' (fun b => CapW (Heap.tcbs H) (Heap.omega H) (Heap.frame H) b ∨ (lo ≤ b.val ∧ b.val < hi) ∨
      DbgW st (Heap.tcbs H) Cs s b))
    (hwin : WinInit st s' lo hi A k w n us)
    (hb : BlkOK st (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H)
      (Heap.scBits H) Ac s)
    (hdrop : DropOK st H (RegionD H lo hi) Cs s) (hnode : RegionOffNodes st Cs s lo hi)
    (hdbg : DbgLinksOK st H Cs s' lo hi A k w n) (hwp : WinPlaced A k w n us) (h0Cs : 0#u64 ∈ Cs)
    (hidl : IdleKeep (L := L) s s') (hdv : ∃ p0 sb0 fi0, capV (L.mem s) xs = .Untyped p0 sb0 fi0 false) :
    ∃ (H' : Heap) (Ac' : Set U64),
      BlkOK st (Heap.tcbs H') Cs (Heap.omega H') H' (Heap.frame H') (Heap.replies H') (Heap.scs H') (Heap.ntfns H')
        (Heap.scBits H') Ac' s' ∧
      JCovD (L := L) th' H' G' {q | q ∈ D ∧ ¬ NewQ A k w cj q} Cs s' := by
  obtain ⟨H', Ac', hb', -, hshape, -, hdead⟩ :=
    (P1.retypeP1Step : RetypeP1Step st s s' H Cs Ac lo hi A k w n us) hb hlo hhi hbits hdrop hnode hw hwin hdbg hwp h0Cs
  refine ⟨H', Ac', hb', h.retype hE (fun q kd hq => ?_) (fun q _ _ e hd => hdead q e hd) hksb hidl hdv⟩
  rcases hshape q kd hq with ⟨ho, hm⟩ | ⟨⟨j, hj, hv⟩, hk⟩
  · refine Or.inl ⟨ho, fun ⟨j, hj, hv, _⟩ => hm ?_⟩
    unfold MeetsR
    have h1 : (j + 1) * k ≤ w * k := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, Nat.one_mul] at h1
    have := Nat.one_le_two_pow (n := kd.bits)
    have := hE.k1
    omega
  · exact Or.inr ⟨⟨j, hj, hv, hcj (by rw [hk]; rfl) j hj⟩, hbits kd hk⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **P1's `WinInit` from `WinZero`** (the window `[A, A + win * k)` as the
region; TCBs 4 KiB), the window zero needed only for the tracked kinds (not
`.other`). -/
theorem winInit_of_winZero {s' : S} {A k win n us : Nat}
    (h : (P1.newKind n us).isSome → (∀ z, P1.newKind n us ≠ some (.other z)) → WinZero (L.mem s') A k win (n = 1))
    (hk : n = 1 → k = 4096) (hfit : A + win * k ≤ 2 ^ 64) :
    P1.WinInit st s' A (A + win * k) A k win n us := by
  intro hs ho b hb h1 h2
  rcases h hs ho b hb h1 h2 with e | ⟨hn, j, hj, hT⟩
  · exact Or.inl e
  · right
    have hk' := hk hn
    subst hk'
    have hjv : (⟨BitVec.ofNat 64 (A + j * 4096)⟩ : U64).val = A + j * 4096 := by
      have : j * 4096 < win * 4096 := Nat.mul_lt_mul_of_pos_right hj (by omega)
      show (BitVec.ofNat 64 (A + j * 4096)).toNat = _; simp; omega
    unfold InT at hT; rw [hjv] at hT
    refine ⟨hn, j, hj, b.val - (A + j * 4096), ?_, by omega⟩
    unfold P1.TcbInitK; omega

end

end
end Fl4Proofs.P3.Sched
