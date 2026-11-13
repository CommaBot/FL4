/-
P3 (DESIGN.md §9), CSpace: the derivation-tree relation after renaming
slots (what `cte_move` and `cte_swap` do to the links), from how the slot
words change.
-/
import Fl4Proofs.P3.MdbInsert
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-! ## Links of linked slots -/

theorem MdbLinks.next_link {th : TypedHeap} {mem : U64 → U64} {G : MdbGhost} (hM : MdbLinks th mem G)
    {a : U64} (ha : a ∈ G.chains.flatten) (hn : nextOf mem a ≠ 0#u64) :
    nextOf mem a ∈ G.chains.flatten ∧ prevOf mem (nextOf mem a) = a := by
  obtain ⟨ch0, hch0, hsch⟩ := List.mem_flatten.1 ha
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hsch
  have hc0 := hM.chain _ hch0
  cases B with
  | nil => exact absurd (by simpa using hM.last _ hch0 (by simp)) hn
  | cons b0 B' =>
    rw [List.isChain_append] at hc0
    obtain ⟨h1, h2⟩ := (List.isChain_cons_cons.1 hc0.2.1).1
    rw [h1]; exact ⟨List.mem_flatten.2 ⟨_, hch0, by simp⟩, h2⟩

theorem MdbLinks.prev_link {th : TypedHeap} {mem : U64 → U64} {G : MdbGhost} (hM : MdbLinks th mem G)
    {b : U64} (hb : b ∈ G.chains.flatten) (hp : prevOf mem b ≠ 0#u64) :
    prevOf mem b ∈ G.chains.flatten ∧ nextOf mem (prevOf mem b) = b := by
  obtain ⟨ch0, hch0, hsch⟩ := List.mem_flatten.1 hb
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hsch
  have hc0 := hM.chain _ hch0
  rcases List.eq_nil_or_concat A with rfl | ⟨A', x, rfl⟩
  · exact absurd (by simpa using hM.head _ hch0 (by simp)) hp
  · simp only [List.concat_eq_append, List.append_assoc, List.singleton_append] at hc0 hch0
    rw [List.isChain_append_cons_cons] at hc0
    obtain ⟨h1, h2⟩ := hc0.2.1
    rw [h2]; exact ⟨List.mem_flatten.2 ⟨_, hch0, by simp⟩, h1⟩

theorem MdbLinks.no_self_par {th : TypedHeap} {mem : U64 → U64} {G : MdbGhost} (hM : MdbLinks th mem G)
    {a : U64} : G.par a ≠ some a := by
  intro h
  have ha := (hM.tree.par_mem a a h).1
  obtain ⟨ch, hch, hach⟩ := List.mem_flatten.1 ha
  exact Mdb.not_desc_self (hM.tree.seg ch hch) ((List.nodup_flatten.1 hM.tree.nodup).1 ch hch) hach
    (Relation.TransGen.single h)

/-! ## Renaming -/

/-- How the slot words change when the linked slots are renamed by `e`
(fixing 0). -/
structure RenLinks (th : TypedHeap) (mem mem' : U64 → U64) (e : U64 ≃ U64) (G : MdbGhost) : Prop where
  e0 : e 0#u64 = 0#u64
  next : ∀ a ∈ G.chains.flatten, nextOf mem' (e a) = e (nextOf mem a)
  prev : ∀ a ∈ G.chains.flatten, prevOf mem' (e a) = e (prevOf mem a)
  members : ∀ a, a ∈ G.chains.flatten.map e ↔ IsSlot th a ∧ ∃ c, capAt mem' a = ok c ∧ c ≠ .Null

theorem MdbLinks.rename {th : TypedHeap} {mem mem' : U64 → U64} {G : MdbGhost} (hM : MdbLinks th mem G)
    {e : U64 ≃ U64} (hL : RenLinks th mem mem' e G) :
    MdbLinks th mem' ⟨G.chains.map (List.map e), Mdb.conjPar e G.par⟩ := by
  refine ⟨Mdb.MdbOK.conj e hM.tree, ?_, ?_, ?_, ?_, ?_⟩
  · intro ch' hch'
    obtain ⟨ch, hch, rfl⟩ := List.mem_map.1 hch'
    simpa using hM.ne_nil ch hch
  · intro ch' hch'
    obtain ⟨ch, hch, rfl⟩ := List.mem_map.1 hch'
    rw [List.isChain_map]
    apply (hM.chain ch hch).imp_of_mem_imp
    rintro a b ha hb ⟨h1, h2⟩
    have haf : a ∈ G.chains.flatten := List.mem_flatten.2 ⟨_, hch, ha⟩
    have hbf : b ∈ G.chains.flatten := List.mem_flatten.2 ⟨_, hch, hb⟩
    exact ⟨by rw [hL.next a haf, h1], by rw [hL.prev b hbf, h2]⟩
  · intro ch' hch' hne
    obtain ⟨ch, hch, rfl⟩ := List.mem_map.1 hch'
    have hne0 : ch ≠ [] := by simpa using hne
    rw [List.head_map, hL.prev _ (List.mem_flatten.2 ⟨_, hch, List.head_mem hne0⟩),
      hM.head ch hch hne0, hL.e0]
  · intro ch' hch' hne
    obtain ⟨ch, hch, rfl⟩ := List.mem_map.1 hch'
    have hne0 : ch ≠ [] := by simpa using hne
    rw [List.getLast_map, hL.next _ (List.mem_flatten.2 ⟨_, hch, List.getLast_mem hne0⟩),
      hM.last ch hch hne0, hL.e0]
  · intro a
    rw [← hL.members a]
    simp only [List.map_flatten]

end

end Fl4Proofs.P3
