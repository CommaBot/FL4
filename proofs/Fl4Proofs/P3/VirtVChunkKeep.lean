/-
P3x for virtualization (line virt, gen 26, item 4): **`VcpuChunked` kept by the ghost MDB steps** (gen 24's
P3/VirtVChunk; l4v `mdb_chunked` for `Vcpu` caps).

* The interval form of `VcpuChunked`'s first half (`ChunkI P ch`: between two positions satisfying `P` every position
  does) is equivalent to a triple form (`Chunk3 P ch`: `[a, b, c] <+ ch`, `P a`, `P c` ⇒ `P b`):
  `cons_sublist_of_getElem?`, `getElem?_of_cons_sublist`, **`chunk3_of_I`**, **`I_of_chunk3`**. The triple form is
  kept by sublists, which is what deletion does to a chain.
* **`vcpuChunked_congr`**: caps of the chain members unchanged (a step that writes no slot word, e.g.
  `vcpu.finalise`, VirtVCappedDel's `slotsSame_of_writes`).
* **`vcpuChunked_remG`** — `cdt::delete` / `empty_slot` (cdt.rs; ghost `remG G x`, P3/EmptyRefine): the slot `x`
  nulled, the other members' caps kept, `G.chains.flatten` nodup (`MdbOK.nodup`).
* **`vcpuChunked_renG`** — `cdt::move_cap` and `cdt::swap` (ghost `renG G e`, P3/MdbRename; MoveRefine / SwapRefine:
  `e = Equiv.swap src dest`): the caps move with their slots (`capV mem' (e a) = capV mem a` for every member).
* **`empty_vcpu_chunked`**: at the `empty_slot` of a `Vcpu v` slot (P3/VirtJExtV2Del's `empty_vcpu_post`), the
  ghost-level lemma at FL4's words.

Not done (open): the insertions (`cdt::insert` after the source, `insG`; the retype's `insert_new_cap`), which need
the sublist structure of `Mdb.insAfter` (a new `Vcpu v` cap only next to a `Vcpu v` source; a non-VCPU insertion
after a slot that is not `Vcpu w` splits no `Vcpu w` interval). No named premise; no existing statement changed;
new file.
-/
import Fl4Proofs.P3.VirtJExtV2Del
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtVChunkKeep
open fl4_core Fl4Proofs.P3 Classical Fl4Proofs.P3.VirtVChunk

noncomputable section

section
variable {α : Type}

/-- The interval form (`VcpuChunked`'s first half at one chain). -/
def ChunkI (P : α → Prop) (ch : List α) : Prop :=
  ∀ (i j k : Nat) (a c : α), i ≤ j → j ≤ k → ch[i]? = some a → ch[k]? = some c → P a → P c →
    ∃ b, ch[j]? = some b ∧ P b

/-- The triple form. -/
def Chunk3 (P : α → Prop) (ch : List α) : Prop :=
  ∀ a b c, [a, b, c].Sublist ch → P a → P c → P b

theorem cons_sublist_of_getElem? : ∀ (ch : List α) (i : Nat) (a : α) (l : List α), ch[i]? = some a →
    l.Sublist (ch.drop (i + 1)) → (a :: l).Sublist ch
  | [], i, a, l, h, _ => by simp at h
  | x :: t, 0, a, l, h, hl => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact List.Sublist.cons₂ _ (by simpa using hl)
  | x :: t, i + 1, a, l, h, hl => by
    simp only [List.getElem?_cons_succ] at h
    exact List.Sublist.cons _ (cons_sublist_of_getElem? t i a l h (by simpa using hl))

theorem getElem?_of_cons_sublist : ∀ (ch : List α) (a : α) (l : List α), (a :: l).Sublist ch →
    ∃ i, ch[i]? = some a ∧ l.Sublist (ch.drop (i + 1))
  | [], a, l, h => by simp at h
  | x :: t, a, l, h => by
    cases h with
    | cons _ h' =>
      obtain ⟨i, hi, hl⟩ := getElem?_of_cons_sublist t a l h'
      exact ⟨i + 1, by simpa using hi, by simpa using hl⟩
    | cons_cons _ h' => exact ⟨0, rfl, by simpa using h'⟩

theorem chunk3_of_I {P : α → Prop} {ch : List α} (h : ChunkI P ch) : Chunk3 P ch := by
  intro a b c hs pa pc
  obtain ⟨i, hi, h1⟩ := getElem?_of_cons_sublist ch a [b, c] hs
  obtain ⟨j, hj, h2⟩ := getElem?_of_cons_sublist _ b [c] h1
  obtain ⟨k, hk, -⟩ := getElem?_of_cons_sublist _ c [] h2
  simp only [List.getElem?_drop] at hj hk
  obtain ⟨b', hb', pb⟩ := h i (i + 1 + j) (i + 1 + (j + 1 + k)) a c (by omega) (by omega) hi hk pa pc
  rw [hj] at hb'
  cases hb'
  exact pb

theorem I_of_chunk3 {P : α → Prop} {ch : List α} (h : Chunk3 P ch) : ChunkI P ch := by
  intro i j k a c hij hjk ha hc pa pc
  have hkl : k < ch.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hc
    cases hc
  have hjl : j < ch.length := by omega
  have hb : ch[j]? = some ch[j] := List.getElem?_eq_getElem hjl
  refine ⟨ch[j], hb, ?_⟩
  rcases Nat.eq_or_lt_of_le hij with e | hij'
  · subst e
    rw [hb] at ha
    cases ha
    exact pa
  rcases Nat.eq_or_lt_of_le hjk with e | hjk'
  · subst e
    rw [hb] at hc
    cases hc
    exact pc
  have h2 : [c].Sublist ((ch.drop (i + 1)).drop (j - i - 1 + 1)) := by
    refine List.singleton_sublist.2 (List.mem_of_getElem? (i := k - j - 1) ?_)
    simp only [List.getElem?_drop]
    have e : i + 1 + (j - i - 1 + 1 + (k - j - 1)) = k := by omega
    rw [e]; exact hc
  have h1 : [ch[j], c].Sublist (ch.drop (i + 1)) := by
    refine cons_sublist_of_getElem? _ (j - i - 1) _ _ ?_ h2
    simp only [List.getElem?_drop]
    have e : i + 1 + (j - i - 1) = j := by omega
    rw [e]; exact hb
  exact h _ _ _ (cons_sublist_of_getElem? ch i a _ ha h1) pa pc

end

section
variable {G : MdbGhost} {mem mem' : U64 → U64}

/-- **Caps of the chain members unchanged.** -/
theorem vcpuChunked_congr (hK : VcpuChunked G mem)
    (hk : ∀ y ∈ G.chains.flatten, capV mem' y = capV mem y) : VcpuChunked G mem' := by
  have hm : ∀ ch ∈ G.chains, ∀ y ∈ ch, capV mem' y = capV mem y := fun ch hch y hy =>
    hk y (List.mem_flatten.2 ⟨ch, hch, hy⟩)
  refine ⟨fun v ch hch => I_of_chunk3 ?_, fun v ch hch ch' hch' y hy y' hy' h1 h2 => ?_⟩
  · intro a b c hs pa pc
    have hsub := hs.subset
    rw [hm ch hch a (hsub (by simp))] at pa
    rw [hm ch hch c (hsub (by simp))] at pc
    rw [hm ch hch b (hsub (by simp))]
    exact chunk3_of_I (hK.1 v ch hch) a b c hs pa pc
  · rw [hm ch hch y hy] at h1
    rw [hm ch' hch' y' hy'] at h2
    exact hK.2 v ch hch ch' hch' y hy y' hy' h1 h2

theorem mem_removeChains {α : Type} [DecidableEq α] {x : α} {chains : List (List α)} (hnd : chains.flatten.Nodup)
    {ch' : List α} (h : ch' ∈ Mdb.removeChains x chains) :
    ∃ ch ∈ chains, ch' = ch.erase x ∧ ch'.Sublist ch ∧ x ∉ ch' := by
  unfold Mdb.removeChains at h
  obtain ⟨ch, hch, e⟩ := List.mem_map.1 (List.mem_filter.1 h).1
  subst e
  exact ⟨ch, hch, rfl, by apply List.erase_sublist, List.Nodup.not_mem_erase ((List.nodup_flatten.1 hnd).1 ch hch)⟩

/-- **Deleting the slot `x`** (`remG`, `cdt::delete`'s `empty_slot`). -/
theorem vcpuChunked_remG (hK : VcpuChunked G mem) (hnd : G.chains.flatten.Nodup) {x : U64}
    (hx0 : capV mem' x = .Null) (hk : ∀ y ∈ G.chains.flatten, y ≠ x → capV mem' y = capV mem y) :
    VcpuChunked (remG G x) mem' := by
  have hm : ∀ ch ∈ G.chains, ∀ y ∈ ch, y ≠ x → capV mem' y = capV mem y := fun ch hch y hy =>
    hk y (List.mem_flatten.2 ⟨ch, hch, hy⟩)
  have hnx : ∀ (v y : U64), capV mem' y = .Vcpu v → y ≠ x := fun v y h e => by
    rw [e, hx0] at h; cases h
  refine ⟨fun v ch' hch' => I_of_chunk3 ?_, fun v c1 hc1 c2 hc2 y hy y' hy' h1 h2 => ?_⟩
  · obtain ⟨ch, hch, -, hsl, hxn⟩ := mem_removeChains hnd hch'
    intro a b c hs pa pc
    have hs' : [a, b, c].Sublist ch := hs.trans hsl
    have hsub := hs'.subset
    have hbm := hs.subset (show b ∈ [a, b, c] by simp)
    have hbx : b ≠ x := fun e => hxn (by rw [← e]; exact hbm)
    rw [hm ch hch a (hsub (by simp)) (hnx v a pa)] at pa
    rw [hm ch hch c (hsub (by simp)) (hnx v c pc)] at pc
    rw [hm ch hch b (hsub (by simp)) hbx]
    exact chunk3_of_I (hK.1 v ch hch) a b c hs' pa pc
  · obtain ⟨d1, hd1, rfl, hs1, -⟩ := mem_removeChains hnd hc1
    obtain ⟨d2, hd2, rfl, hs2, -⟩ := mem_removeChains hnd hc2
    have hy1 := hs1.subset hy
    have hy2 := hs2.subset hy'
    rw [hm d1 hd1 y hy1 (hnx v y h1)] at h1
    rw [hm d2 hd2 y' hy2 (hnx v y' h2)] at h2
    rw [hK.2 v d1 hd1 d2 hd2 y hy1 y' hy2 h1 h2]

/-- **Moving / swapping caps with their slots** (`renG G e`). -/
theorem vcpuChunked_renG (hK : VcpuChunked G mem) (e : U64 ≃ U64)
    (hk : ∀ a ∈ G.chains.flatten, capV mem' (e a) = capV mem a) : VcpuChunked (renG G e) mem' := by
  have hm : ∀ ch ∈ G.chains, ∀ y ∈ ch, capV mem' (e y) = capV mem y := fun ch hch y hy =>
    hk y (List.mem_flatten.2 ⟨ch, hch, hy⟩)
  have hback : ∀ ch : List U64, (ch.map e).map e.symm = ch := fun ch => by
    rw [List.map_map]; simp
  have hmem : ∀ (ch : List U64) (y : U64), y ∈ ch.map e → e.symm y ∈ ch := fun ch y hy => by
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    simpa using hz
  have hP : ∀ ch ∈ G.chains, ∀ y ∈ ch.map e, capV mem' y = capV mem (e.symm y) := fun ch hch y hy => by
    have := hm ch hch (e.symm y) (hmem ch y hy)
    simpa using this
  refine ⟨fun v ch' hch' => I_of_chunk3 ?_, fun v c1 hc1 c2 hc2 y hy y' hy' h1 h2 => ?_⟩
  · obtain ⟨ch, hch, rfl⟩ := List.mem_map.1 hch'
    intro a b c hs pa pc
    have hsub := hs.subset
    have hs' : [e.symm a, e.symm b, e.symm c].Sublist ch := by
      have := hs.map e.symm
      rw [hback] at this
      simpa using this
    rw [hP ch hch a (hsub (by simp))] at pa
    rw [hP ch hch c (hsub (by simp))] at pc
    rw [hP ch hch b (hsub (by simp))]
    exact chunk3_of_I (hK.1 v ch hch) _ _ _ hs' pa pc
  · obtain ⟨d1, hd1, rfl⟩ := List.mem_map.1 hc1
    obtain ⟨d2, hd2, rfl⟩ := List.mem_map.1 hc2
    rw [hP d1 hd1 y hy] at h1
    rw [hP d2 hd2 y' hy'] at h2
    rw [hK.2 v d1 hd1 d2 hd2 _ (hmem d1 y hy) _ (hmem d2 y' hy') h1 h2]

end

/-! ## At FL4's words: the `empty_slot` of a `Vcpu` slot -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {th : TypedHeap}

/-- **`VcpuChunked` across the `empty_slot` of a `Vcpu v` slot** (P3/VirtJExtV2Del's `empty_vcpu_post`). -/
theorem empty_vcpu_chunked (hP : Placed th) {s1 : S} {a1 : A} {G : MdbGhost} (hM1 : MdbLinks th (L.mem s1) G)
    (hK : VcpuChunked G (L.mem s1)) {slot v : U64} (hxm : slot ∈ G.chains.flatten) (hx : IsSlot th slot)
    (hc1 : capAt (L.mem s1) slot = ok (.Vcpu v)) {y2 : S × A}
    (he : cdt.empty_slot st arI s1 a1 slot .Null = ok y2) : VcpuChunked (remG G slot) (L.mem y2.1) := by
  have emp := VirtJExtV2Del.empty_vcpu_post arI hP hM1 hxm hx hc1 he
  refine vcpuChunked_remG hK hM1.tree.nodup ?_ fun y hy hne => ?_
  · rw [emp.1 slot hx, if_pos rfl]
  · rw [emp.1 y ((hM1.members y).1 hy).1, if_neg hne]

end

end
end Fl4Proofs.P3.VirtVChunkKeep
