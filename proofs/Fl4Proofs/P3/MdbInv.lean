/-
P3 (DESIGN.md §9), CSpace: **the MDB invariant** `MdbInv`, tying the slot
bits (revocable, first-badged) and caps to the ghost derivation tree, in the
manner of l4v's `valid_mdb` pieces:

* `orig`: parents are original (revocable) — l4v's cdt/`is_original_cap`
  correspondence (`ut_revocable`-like for parents);
* `desc`: every descendant passes FL4's `is_mdb_parent_of` test from each
  of its ancestors (l4v: the cdt is the "subtree" of the MDB list);
* `after`: the slot right after a slot's block of descendants fails the
  test from it and from its ancestors (the subtree is maximal);
* `chunk`: caps in a region form one stretch of a chain (`mdb_chunked`);
* `badges`: a badged cap followed, in its region, by one with another
  non-zero badge has that one first-badged (`valid_badges`);
* `utrev`: untyped caps are revocable (`ut_revocable`);
* `self`: every cap but a zombie is in its own region (its region does not
  wrap).

`MdbInv.parentAdj` gives `ParentAdj`: `is_mdb_parent_of x (next x)` is ghost
descent.
-/
import Fl4Proofs.P3.MdbSem
import Fl4Proofs.P3.MdbChunk
import Fl4Proofs.P3.Restart
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-- FL4's parent test between two slots, from memory. -/
def isPM (mem : U64 → U64) (x y : U64) : Bool := isPF (revOf mem x) (capV mem x) (capV mem y) (fbOf mem y)

/-- Same region, between the caps of two slots. -/
def srM (mem : U64 → U64) (x y : U64) : Bool := srB (capV mem x) (capV mem y)

/-- The relation the chains are chunked by: same region, except that the
slot of a frame cap with its revocable bit clear is unconstrained
(`DeriveSubframe` puts non-revocable 4 KiB aliases right after the large
frame's cap, in any order). The parent test needs the revocable bit
(`isPF`), and frame caps' finalisation does not depend on finality (as in
l4v `arch_finalise_cap`), so nothing needs chunking there. -/
def srF (mem : U64 → U64) (x y : U64) : Bool := srM mem x y || (isFrame (capV mem x) && !revOf mem x)

theorem srF_of_srM {mem : U64 → U64} {x y : U64} (h : srM mem x y = true) : srF mem x y = true := by
  simp [srF, h]

theorem srF_nf {mem : U64 → U64} {x y : U64} (h : isFrame (capV mem x) = false) : srF mem x y = srM mem x y := by
  simp [srF, h]

theorem srF_rev {mem : U64 → U64} {x y : U64} (h : revOf mem x = true) : srF mem x y = srM mem x y := by
  simp [srF, h]

theorem srF_congr {mem mem' : U64 → U64} {u v u' v' : U64} (hs : srM mem' u' v' = srM mem u v)
    (hf : isFrame (capV mem' u') = isFrame (capV mem u)) (hr : revOf mem' u' = revOf mem u) :
    srF mem' u' v' = srF mem u v := by
  simp only [srF, hs, hf, hr]

theorem ca_true {R : U64 → U64 → Bool} {a : U64} (h : ∀ v, R a v = true) : ∀ L, Mdb.CA R a L
  | [] => trivial
  | v :: L => ⟨fun h0 => (by rw [h v] at h0; cases h0), ca_true h L⟩

theorem chunkL_srF {mem : U64 → U64} {L : List U64} (h : Mdb.ChunkL (srM mem) L) : Mdb.ChunkL (srF mem) L := by
  induction L with
  | nil => trivial
  | cons a L ih =>
    refine ⟨?_, ih h.2⟩
    cases hf : (isFrame (capV mem a) && !revOf mem a)
    · exact Mdb.ca_congr h.1 (fun v _ => by simp [srF, hf])
    · exact ca_true (fun v => by simp [srF, hf]) L

theorem revF_frame {c : capability.Cap} (h : isFrame c = true) (d : capability.Cap) : revF c d = false := by
  cases c <;> simp [isFrame] at h; cases d <;> rfl

theorem isFrame_of_badged {c : capability.Cap} (h : isBadged c = true) : isFrame c = false := by
  cases c <;> simp_all [isBadged, isFrame]

/-- The chunk condition at a slot that is not an unconstrained frame. -/
theorem ca_srM {mem : U64 → U64} {a : U64} {L : List U64} (h : Mdb.CA (srF mem) a L)
    (hf : isFrame (capV mem a) = false ∨ revOf mem a = true) : Mdb.CA (srM mem) a L :=
  Mdb.ca_congr h (fun v _ => by rcases hf with hf | hf <;> simp [srF, hf])

structure MdbInv (mem : U64 → U64) (G : MdbGhost) : Prop where
  orig : ∀ c p, G.par c = some p → revOf mem p = true
  desc : ∀ x y, Mdb.Desc G.par y x → isPM mem x y = true
  after : ∀ y ∈ G.chains.flatten, nextOf mem y ≠ 0#u64 → ∀ x, (x = y ∨ Mdb.Desc G.par y x) →
      ¬ Mdb.Desc G.par (nextOf mem y) x → isPM mem x (nextOf mem y) = false
  chunk : ∀ ch ∈ G.chains, Mdb.ChunkL (srF mem) ch
  badges : ∀ y ∈ G.chains.flatten, nextOf mem y ≠ 0#u64 → isBadged (capV mem y) = true →
      srM mem y (nextOf mem y) = true → badgeF (capV mem y) ≠ badgeF (capV mem (nextOf mem y)) →
      badgeF (capV mem (nextOf mem y)) ≠ 0#u64 → fbOf mem (nextOf mem y) = true
  utrev : ∀ x ∈ G.chains.flatten, isUt (capV mem x) = true → revOf mem x = true
  self : ∀ x ∈ G.chains.flatten, isZb (capV mem x) = false → srM mem x x = true

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`ParentAdj` from the invariant.** -/
theorem MdbInv.parentAdj {th : TypedHeap} {s : S} {G : MdbGhost} (hI : MdbInv (L.mem s) G) :
    ParentAdj (L := L) th s G := by
  intro x hx hn
  refine ⟨_, is_mdb_parent_eq s x _, ?_⟩
  by_cases hd : Mdb.Desc G.par (nextOf (L.mem s) x) x
  · exact ⟨fun _ => hd, fun _ => hI.desc _ _ hd⟩
  · have := hI.after x hx hn x (Or.inl rfl) hd
    constructor
    · intro h; exact absurd (show isPM (L.mem s) x (nextOf (L.mem s) x) = true from h) (by simp [this])
    · intro h; exact absurd h hd

end

/-! ## Transport across writes outside the slots -/

theorem SlotsSame.fbOf' {th : TypedHeap} {m m' : U64 → U64} (h : SlotsSame th m m') {a : U64} (ha : IsSlot th a) :
    fbOf m' a = fbOf m a := by
  unfold Fl4Proofs.P3.fbOf; rw [(h a ha).2.2.2]

theorem SlotsSame.capV {th : TypedHeap} {m m' : U64 → U64} (h : SlotsSame th m m') {a : U64} (ha : IsSlot th a) :
    capV m' a = capV m a := by
  unfold Fl4Proofs.P3.capV; rw [(h a ha).1, (h a ha).2.1]

theorem desc_mem {th : TypedHeap} {mem : U64 → U64} {G : MdbGhost} (hM : MdbLinks th mem G) {x y : U64}
    (h : Mdb.Desc G.par y x) : y ∈ G.chains.flatten ∧ x ∈ G.chains.flatten := by
  induction h with
  | single h1 => exact hM.tree.par_mem _ _ h1
  | tail _ h2 ih => exact ⟨ih.1, (hM.tree.par_mem _ _ h2).2⟩

theorem MdbInv.of_same {th : TypedHeap} {m m' : U64 → U64} {G : MdbGhost} (hM : MdbLinks th m G)
    (hI : MdbInv m G) (hS : SlotsSame th m m') : MdbInv m' G := by
  have hsl : ∀ x, x ∈ G.chains.flatten → IsSlot th x := fun x h => ((hM.members x).1 h).1
  have hnx : ∀ y ∈ G.chains.flatten, nextOf m y ≠ 0#u64 → nextOf m y ∈ G.chains.flatten := by
    intro y hy hn
    rcases hM.next_mem hy with h | ⟨h, -⟩
    · exact absurd h hn
    · exact h
  have hpm : ∀ x y, x ∈ G.chains.flatten → y ∈ G.chains.flatten → isPM m' x y = isPM m x y := by
    intro x y hx hy
    unfold isPM
    rw [hS.revOf (hsl x hx), hS.capV (hsl x hx), hS.capV (hsl y hy), hS.fbOf' (hsl y hy)]
  have hsr : ∀ x y, x ∈ G.chains.flatten → y ∈ G.chains.flatten → srM m' x y = srM m x y := by
    intro x y hx hy
    unfold srM; rw [hS.capV (hsl x hx), hS.capV (hsl y hy)]
  refine ⟨fun c p h => ?_, fun x y h => ?_, fun y hy hn x hx hd => ?_, fun ch hch => ?_,
    fun y hy hn hb hs hbd hb0 => ?_, fun x hx hu => ?_, fun x hx hz => ?_⟩
  · rw [hS.revOf (hsl p (hM.tree.par_mem _ _ h).2)]; exact hI.orig c p h
  · obtain ⟨h1, h2⟩ := desc_mem hM h
    rw [hpm x y h2 h1]; exact hI.desc x y h
  · have hy' := hsl y hy
    rw [hS.nextOf hy'] at hn hd ⊢
    have hx' : x ∈ G.chains.flatten := by rcases hx with rfl | hx; exact hy; exact (desc_mem hM hx).2
    rw [hpm x _ hx' (hnx y hy hn)]; exact hI.after y hy hn x hx hd
  · refine Mdb.chunkL_congr (hI.chunk ch hch) (fun u hu v hv => srF_congr ?_ ?_ ?_)
    · exact hsr u v (List.mem_flatten.2 ⟨_, hch, hu⟩) (List.mem_flatten.2 ⟨_, hch, hv⟩)
    · rw [hS.capV (hsl u (List.mem_flatten.2 ⟨_, hch, hu⟩))]
    · rw [hS.revOf (hsl u (List.mem_flatten.2 ⟨_, hch, hu⟩))]
  · have hy' := hsl y hy
    rw [hS.nextOf hy'] at hn hs hbd hb0 ⊢
    have hn' := hnx y hy hn
    rw [hS.capV hy'] at hb hbd
    rw [hS.capV (hsl _ hn')] at hbd hb0
    rw [hsr y _ hy hn'] at hs
    rw [hS.fbOf' (hsl _ hn')]; exact hI.badges y hy hn hb hs hbd hb0
  · rw [hS.capV (hsl x hx)] at hu; rw [hS.revOf (hsl x hx)]; exact hI.utrev x hx hu
  · rw [hS.capV (hsl x hx)] at hz; rw [hsr x x hx hx]; exact hI.self x hx hz

end

end Fl4Proofs.P3
