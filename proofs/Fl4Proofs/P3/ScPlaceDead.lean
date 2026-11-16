/-
P3 (DESIGN.md §9): **keeping `JCov`: monotone ghost heaps and a dead set**
(ScPlaceUt's design note, option 2).

* `DeadP H s q`: the object at `q` is read by nothing P1 tracks: a TCB
  inactive, in no queue, with no SC, bound notification or reply, neither
  current, the scheduler action nor idle; an endpoint idle; a notification
  idle with no bound TCB and no SC; a reply with no TCB; an SC with no TCB
  and no reply, not the current SC.
* `JCovD th H G D Cs s`: every object of `th` and `H` is covered by a cap
  or in the dead set `D`, `D`'s objects are `DeadP`, and the untyped caps
  miss the kernel area (`JCov` with "covered" weakened to "covered or
  dead"; `JCov.toD` with `D = ∅`).
* `JCovD.step`: across any step, with `D' = D ∪` the objects no longer
  covered, given that an object losing its cover is then dead, and the dead
  stay dead (`JCovD.same`: the frame for steps keeping the MDB's caps;
  `JCovD.delete`: a slot's cap removed, the objects of its range dead).
* `dead_childless`: an object meeting a childless untyped region is dead,
  so retype removes only dead objects.
* `FinDeadHyp`: what P1's finalisation of a final cap must add to its
  post (the `.slots` lemmas give `BlkOK` and the footprint, not this).
-/
import Fl4Proofs.P3.ScPlaceUt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P3 Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **A dead object** (module docstring). -/
def DeadP (H : Heap) (s : S) (q : U64) : Prop :=
  (H q = some .tcb → L.mem s (P1.stA q) = sched.TS_INACTIVE ∧ L.mem s (inqA q) = 0#u64 ∧
    L.mem s (scA q) = 0#u64 ∧ L.mem s (boundA q) = 0#u64 ∧ L.mem s (replyA q) = 0#u64 ∧
    q ≠ L.curW s ∧ q ≠ L.actionW s ∧ q ≠ L.idleW s) ∧
  (H q = some .ep → L.epState s q = 0#u64) ∧
  (H q = some .ntfn → L.epState s q = 0#u64 ∧ L.mem s (ntfnBtA q) = 0#u64 ∧ L.mem s (ntfnScA q) = 0#u64) ∧
  (H q = some .reply → L.mem s (rTcbA q) = 0#u64) ∧
  (∀ z, H q = some (.sc z) → L.mem s (scTcbA q) = 0#u64 ∧ L.mem s (scReplyA q) = 0#u64 ∧
    L.mem s (scNtfnA q) = 0#u64 ∧ q ≠ L.cscW s)

/-- **`JCov` with a dead set** (module docstring). -/
structure JCovD (th : TypedHeap) (H : Heap) (G : MdbGhost) (D : Set U64) (Cs : Set U64) (s : S) : Prop where
  th : ∀ q k, th q = some k → Covered (L.mem s) G q.val (q.val + max (objSize k) 1) ∨ q ∈ D
  h : ∀ q k, H q = some k → Covered (L.mem s) G q.val (q.val + 2 ^ k.bits) ∨ q ∈ D
  dead : ∀ q ∈ D, DeadP (L := L) H s q
  ks : ∀ x ∈ G.chains.flatten, ∀ p sb fi d, capV (L.mem s) x = .Untyped p sb fi d →
    (p.val + 2 ^ sb.val ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ p.val) ∧
    ∀ c ∈ Cs, p.val + 2 ^ sb.val ≤ L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ p.val

variable {th : TypedHeap} {H : Heap} {G : MdbGhost} {D Cs : Set U64} {s : S}

theorem JCov.toD (h : JCov (L := L) th H G Cs s) : JCovD (L := L) th H G ∅ Cs s :=
  ⟨fun q k hq => Or.inl (h.th q k hq), fun q k hq => Or.inl (h.h q k hq), fun _ h => h.elim, h.ks⟩

/-- The objects of a typed heap that lose their cover. -/
def Uncov (th : TypedHeap) (H : Heap) (mem : U64 → U64) (G : MdbGhost) : Set U64 :=
  {q | (∃ k, th q = some k ∧ ¬ Covered mem G q.val (q.val + max (objSize k) 1)) ∨
    (∃ k, H q = some k ∧ ¬ Covered mem G q.val (q.val + 2 ^ k.bits))}

/-- **`JCovD` across a step**: the dead set grows by the objects no longer
covered, which must then be dead, and the dead stay dead; the untyped caps
after miss the kernel area. -/
theorem JCovD.step (h : JCovD (L := L) th H G D Cs s) {s' : S} {G' : MdbGhost}
    (hunc : ∀ q, q ∈ Uncov th H (L.mem s') G' → DeadP (L := L) H s' q)
    (hdead : ∀ q ∈ D, DeadP (L := L) H s q → DeadP (L := L) H s' q)
    (hks : ∀ x ∈ G'.chains.flatten, ∀ p sb fi d, capV (L.mem s') x = .Untyped p sb fi d →
      (p.val + 2 ^ sb.val ≤ (L.ksb s').val ∨ (L.ksb s').val + 13568 ≤ p.val) ∧
      ∀ c ∈ Cs, p.val + 2 ^ sb.val ≤ L.nodeBase s' c ∨ L.nodeBase s' c + 4288 ≤ p.val) :
    JCovD (L := L) th H G' (D ∪ Uncov th H (L.mem s') G') Cs s' := by
  refine ⟨fun q k hq => ?_, fun q k hq => ?_, fun q hq => ?_, hks⟩
  · by_cases hc : Covered (L.mem s') G' q.val (q.val + max (objSize k) 1)
    · exact Or.inl hc
    · exact Or.inr (Or.inr (Or.inl ⟨k, hq, hc⟩))
  · by_cases hc : Covered (L.mem s') G' q.val (q.val + 2 ^ k.bits)
    · exact Or.inl hc
    · exact Or.inr (Or.inr (Or.inr ⟨k, hq, hc⟩))
  · rcases hq with hq | hq
    · exact hdead q hq (h.dead q hq)
    · exact hunc q hq

/-- **A cover kept**: a cap of the MDB kept by the step (in the MDB after,
the same cap) covers the same range. -/
theorem covered_keep {m m' : U64 → U64} {G' : MdbGhost} {lo hi : Nat} (hc : Covered m G lo hi)
    (hk : ∀ y ∈ G.chains.flatten, physF (capV m y) = true → isUt (capV m y) = false →
      y ∈ G'.chains.flatten ∧ capV m' y = capV m y) : Covered m' G' lo hi := by
  obtain ⟨y, hy, hp, hu, hb, ht⟩ := hc
  obtain ⟨hy', e⟩ := hk y hy hp hu
  exact ⟨y, hy', by rw [e]; exact hp, by rw [e]; exact hu, by rw [e]; exact hb, by rw [e]; exact ht⟩

/-- **`JCovD` across a step keeping the MDB's covering caps** (creating and
destroying no object): nothing loses its cover, and the dead stay dead. -/
theorem JCovD.same (h : JCovD (L := L) th H G D Cs s) {s' : S} {G' : MdbGhost}
    (hk : ∀ y ∈ G.chains.flatten, physF (capV (L.mem s) y) = true → isUt (capV (L.mem s) y) = false →
      y ∈ G'.chains.flatten ∧ capV (L.mem s') y = capV (L.mem s) y)
    (hdead : ∀ q ∈ D, DeadP (L := L) H s q → DeadP (L := L) H s' q)
    (hks : ∀ x ∈ G'.chains.flatten, ∀ p sb fi d, capV (L.mem s') x = .Untyped p sb fi d →
      (p.val + 2 ^ sb.val ≤ (L.ksb s').val ∨ (L.ksb s').val + 13568 ≤ p.val) ∧
      ∀ c ∈ Cs, p.val + 2 ^ sb.val ≤ L.nodeBase s' c ∨ L.nodeBase s' c + 4288 ≤ p.val) :
    JCovD (L := L) th H G' D Cs s' := by
  refine ⟨fun q k hq => ?_, fun q k hq => ?_, fun q hq => hdead q hq (h.dead q hq), hks⟩
  · rcases h.th q k hq with hc | hd
    · exact Or.inl (covered_keep hc hk)
    · exact Or.inr hd
  · rcases h.h q k hq with hc | hd
    · exact Or.inl (covered_keep hc hk)
    · exact Or.inr hd

/-- **`JCovD` across the removal of one slot's cap** (`delete`'s
`empty_slot`, after the finalisation): every other cap of the MDB is kept;
an object covered by the removed cap `c` is then dead (P1's `FinDeadHyp`
for a final cap; for a non-final one another cap covers it, `hother`). -/
theorem JCovD.delete (h : JCovD (L := L) th H G D Cs s) {s' : S} {G' : MdbGhost} {x : U64}
    (hk : ∀ y ∈ G.chains.flatten, y ≠ x → physF (capV (L.mem s) y) = true → isUt (capV (L.mem s) y) = false →
      y ∈ G'.chains.flatten ∧ capV (L.mem s') y = capV (L.mem s) y)
    (hx : ∀ lo hi, lo < hi → baseF (capV (L.mem s) x) ≤ lo → hi ≤ topF (capV (L.mem s) x) + 1 →
      Covered (L.mem s') G' lo hi ∨ (∀ q, q.val = lo → DeadP (L := L) H s' q))
    (hdead : ∀ q ∈ D, DeadP (L := L) H s q → DeadP (L := L) H s' q)
    (hks : ∀ x ∈ G'.chains.flatten, ∀ p sb fi d, capV (L.mem s') x = .Untyped p sb fi d →
      (p.val + 2 ^ sb.val ≤ (L.ksb s').val ∨ (L.ksb s').val + 13568 ≤ p.val) ∧
      ∀ c ∈ Cs, p.val + 2 ^ sb.val ≤ L.nodeBase s' c ∨ L.nodeBase s' c + 4288 ≤ p.val) :
    JCovD (L := L) th H G' (D ∪ Uncov th H (L.mem s') G') Cs s' := by
  have cov : ∀ {lo hi : Nat}, lo < hi → Covered (L.mem s) G lo hi →
      Covered (L.mem s') G' lo hi ∨ (∀ q, q.val = lo → DeadP (L := L) H s' q) := by
    intro lo hi hlh hc
    obtain ⟨y, hy, hp, hu, hb, ht⟩ := hc
    by_cases hyx : y = x
    · subst hyx; exact hx lo hi hlh hb ht
    · obtain ⟨hy', e⟩ := hk y hy hyx hp hu
      exact Or.inl ⟨y, hy', by rw [e]; exact hp, by rw [e]; exact hu, by rw [e]; exact hb, by rw [e]; exact ht⟩
  refine h.step (fun q hq => ?_) hdead hks
  rcases hq with ⟨k, hq, hnc⟩ | ⟨k, hq, hnc⟩
  · rcases h.th q k hq with hc | hd
    · rcases cov (by omega) hc with hc' | hd'
      · exact absurd hc' hnc
      · exact hd' q rfl
    · exact hdead q hd (h.dead q hd)
  · rcases h.h q k hq with hc | hd
    · rcases cov (by have := Nat.one_le_two_pow (n := k.bits); omega) hc with hc' | hd'
      · exact absurd hc' hnc
      · exact hd' q rfl
    · exact hdead q hd (h.dead q hd)

/-- **An object meeting a childless untyped region is dead** (`ut_free`:
a covered object misses the region), so a retype over the region removes
only dead objects. -/
theorem dead_childless (h : JCovD (L := L) th H G D Cs s) (hU : UtInv (L.mem s) G) (hI : MdbInv (L.mem s) G)
    {x : U64} (hx : x ∈ G.chains.flatten) {p sb fi : U64} {d : Bool}
    (hcx : capV (L.mem s) x = .Untyped p sb fi d) (hnd : ∀ y, ¬ Mdb.Desc G.par y x) :
    (∀ q k, th q = some k → ¬ (q.val + max (objSize k) 1 ≤ p.val ∨ p.val + 2 ^ sb.val ≤ q.val) →
      q ∈ D ∧ DeadP (L := L) H s q) ∧
    (∀ q k, H q = some k → ¬ (q.val + 2 ^ k.bits ≤ p.val ∨ p.val + 2 ^ sb.val ≤ q.val) →
      q ∈ D ∧ DeadP (L := L) H s q) := by
  refine ⟨fun q k hq hm => ?_, fun q k hq hm => ?_⟩
  · rcases h.th q k hq with hc | hd
    · exact absurd (ut_free hU hI hx hcx hnd (by omega) hc) hm
    · exact ⟨hd, h.dead q hd⟩
  · rcases h.h q k hq with hc | hd
    · exact absurd (ut_free hU hI hx hcx hnd (by have := Nat.one_le_two_pow (n := k.bits); omega) hc) hm
    · exact ⟨hd, h.dead q hd⟩

end

/-- **What P1's finalisation of a final cap must add to its post**: the
cap's object is dead afterwards (`DeadP`). P1's `fin_cap_*.slots` give
`BlkOK`, the footprint and the cap-slot words only; this is the missing
post, per kind (`K`, with the object `obj`). -/
def FinDeadHyp {S A : Type} (st : machine.Store S) [L : P1.LawfulStore st] (ar : machine.Arch A)
    (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (Ac : Set U64)
    (K : capability.Cap → Prop) (obj : capability.Cap → U64) : Prop :=
  ∀ (s : S) (a : A) (c : capability.Cap) (ex : Bool), K c → BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    objects.finalise_cap st ar s a c true ex ⦃ r => DeadP (L := L) H r.2.1 (obj c) ⦄

end

end Fl4Proofs.P3.Sched
