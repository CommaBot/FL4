/-
P3 (DESIGN.md §9), CSpace: `MdbInv` after emptying a slot of the tree
(`cdt::empty_slot`), at the level of the slot contents and the ghost tree:
`x` leaves its chain (its `prev` and `next` are linked), its children go to
its parent, and its `next` inherits its first-badged bit.

The new adjacent pair (`prev x`, `next x`) is where the work is: the chunk
and badge parts of the invariant say that `next x` cannot pass the parent
test from a slot whose block `x` was not in.
-/
import Fl4Proofs.P3.MdbInvIns
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

theorem isPF_fb_or {r : Bool} {a b : capability.Cap} {f g : Bool} (h : isPF r a b f = false) :
    isPF r a b (f || g) = false := by
  unfold isPF at h ⊢; cases f <;> cases g <;> simp_all

/-- Two consecutive elements of a chain are linked. -/
theorem MdbLinks.adj {th : TypedHeap} {mem : U64 → U64} {G : MdbGhost} (hM : MdbLinks th mem G)
    {ch : List U64} (hch : ch ∈ G.chains) {L R : List U64} {u v : U64} (he : ch = L ++ u :: v :: R) :
    nextOf mem u = v ∧ prevOf mem v = u := by
  have hc := hM.chain _ hch
  rw [he, List.isChain_append] at hc
  exact (List.isChain_cons_cons.1 hc.2.1).1

/-- The element before a descendant of `a` is `a` or a descendant of `a`. -/
theorem MdbLinks.prev_in_block {th : TypedHeap} {mem : U64 → U64} {G : MdbGhost} (hM : MdbLinks th mem G)
    {a n : U64} (hd : Mdb.Desc G.par n a) : prevOf mem n = a ∨ Mdb.Desc G.par (prevOf mem n) a := by
  obtain ⟨-, ha⟩ := desc_mem hM hd
  obtain ⟨ch, hch, hach⟩ := List.mem_flatten.1 ha
  obtain ⟨A, post, rfl⟩ := List.append_of_mem hach
  obtain ⟨d, rest, rfl, hdd⟩ := hM.tree.seg _ hch A a post rfl
  have hn := (hdd n).1 hd
  obtain ⟨d1, d2, rfl⟩ := List.append_of_mem hn
  rcases List.eq_nil_or_concat d1 with rfl | ⟨d1', z, rfl⟩
  · left
    exact (hM.adj hch (L := A) (R := d2 ++ rest) (by simp)).2
  · right
    have := (hM.adj hch (L := A ++ a :: d1') (u := z) (v := n) (R := d2 ++ rest) (by simp)).2
    rw [this]; exact (hdd z).2 (by simp)

/-- For `a` at or above `p`, with `x` after `p` and `n` after `x`: `a` is
followed in its chain by a stretch containing `x` and then `n`. -/
theorem MdbLinks.stretch {th : TypedHeap} {mem : U64 → U64} {G : MdbGhost} (hM : MdbLinks th mem G)
    {a p x n : U64} (hp : p ∈ G.chains.flatten) (hpa : a = p ∨ Mdb.Desc G.par p a)
    (hpx : nextOf mem p = x) (hx0 : x ≠ 0#u64) (hxn : nextOf mem x = n) (hn0 : n ≠ 0#u64) :
    ∃ ch ∈ G.chains, ∃ A B C, ch = A ++ a :: (B ++ n :: C) ∧ x ∈ B := by
  obtain ⟨ch, hch, hpch⟩ := List.mem_flatten.1 hp
  obtain ⟨A0, R, rfl⟩ := List.append_of_mem hpch
  have hN1 := hM.next_eq_succ hch
  rw [hpx] at hN1
  obtain ⟨R', rfl⟩ : ∃ R', R = x :: R' := by
    cases R with
    | nil => simp at hN1; exact absurd hN1 hx0
    | cons r R' => simp at hN1; exact ⟨R', by rw [hN1]⟩
  have hN2 := hM.next_eq_succ (pre := A0 ++ [p]) (a := x) (post := R') (by simpa using hch)
  rw [hxn] at hN2
  obtain ⟨R'', rfl⟩ : ∃ R'', R' = n :: R'' := by
    cases R' with
    | nil => simp at hN2; exact absurd hN2 hn0
    | cons r R'' => simp at hN2; exact ⟨R'', by rw [hN2]⟩
  rcases hpa with hpa | hd
  · rw [hpa]; exact ⟨A0 ++ p :: x :: n :: R'', hch, A0, [x], R'', by simp, by simp⟩
  · have ha := (desc_mem hM hd).2
    obtain ⟨ch', hch', hach⟩ := List.mem_flatten.1 ha
    obtain ⟨A1, post, rfl⟩ := List.append_of_mem hach
    have hppost := Mdb.desc_after (hM.tree.seg _ hch') rfl hd
    have e := chain_unique hM.tree.nodup hch' hch (by simp [hppost]) hpch
    obtain ⟨M, S, rfl⟩ := List.append_of_mem hppost
    have hnd : (A1 ++ a :: (M ++ p :: S)).Nodup := (List.nodup_flatten.1 hM.tree.nodup).1 _ hch'
    have hS : S = x :: n :: R'' :=
      Mdb.nodup_suffix_unique (x := p) (p1 := A1 ++ a :: M) (p2 := A0) hnd (by simp) e
    subst hS
    exact ⟨A1 ++ a :: (M ++ p :: x :: n :: R''), hch', A1, M ++ [p, x], R'', by simp, by simp⟩

/-- The situation of emptying slot `x`, at the level of the slot contents. -/
structure EmpCtx (th : TypedHeap) (mem mem' : U64 → U64) (G : MdbGhost) (x : U64) : Prop where
  hP : Placed th
  hM : MdbLinks th mem G
  hI : MdbInv mem G
  hx : x ∈ G.chains.flatten
  hcap : ∀ a, IsSlot th a → a ≠ x → capV mem' a = capV mem a
  hrev : ∀ a, IsSlot th a → a ≠ x → revOf mem' a = revOf mem a
  hfb : ∀ a, IsSlot th a → a ≠ x → fbOf mem' a =
    if nextOf mem x ≠ 0#u64 ∧ a = nextOf mem x then (fbOf mem a || fbOf mem x) else fbOf mem a
  hnext : ∀ a, IsSlot th a → a ≠ x → nextOf mem' a =
    if prevOf mem x ≠ 0#u64 ∧ a = prevOf mem x then nextOf mem x else nextOf mem a

namespace EmpCtx
variable {th : TypedHeap} {mem mem' : U64 → U64} {G : MdbGhost} {x : U64} (h : EmpCtx th mem mem' G x)
include h

theorem sl {z : U64} (hz : z ∈ G.chains.flatten) : IsSlot th z := ((h.hM.members z).1 hz).1

theorem memE (z : U64) : z ∈ (remG G x).chains.flatten ↔ z ∈ G.chains.flatten ∧ z ≠ x :=
  Mdb.mem_removeChains h.hM.tree.nodup

theorem descE (y z : U64) : Mdb.Desc (remG G x).par y z ↔ y ≠ x ∧ z ≠ x ∧ Mdb.Desc G.par y z :=
  Mdb.desc_remove_iff h.hM.no_self_par y z

theorem cz {z : U64} (hz : z ∈ G.chains.flatten) (hzx : z ≠ x) : capV mem' z = capV mem z :=
  h.hcap z (h.sl hz) hzx
theorem rz {z : U64} (hz : z ∈ G.chains.flatten) (hzx : z ≠ x) : revOf mem' z = revOf mem z :=
  h.hrev z (h.sl hz) hzx

/-- The parent test after: the same, except towards `next x`, which got
`x`'s first-badged bit. -/
theorem pm {a y : U64} (ha : a ∈ G.chains.flatten) (hax : a ≠ x) (hy : y ∈ G.chains.flatten) (hyx : y ≠ x) :
    isPM mem' a y = if nextOf mem x ≠ 0#u64 ∧ y = nextOf mem x then
      isPF (revOf mem a) (capV mem a) (capV mem y) (fbOf mem y || fbOf mem x) else isPM mem a y := by
  unfold isPM
  rw [h.rz ha hax, h.cz ha hax, h.cz hy hyx, h.hfb y (h.sl hy) hyx]
  split <;> rfl

theorem pm_false {a y : U64} (ha : a ∈ G.chains.flatten) (hax : a ≠ x) (hy : y ∈ G.chains.flatten) (hyx : y ≠ x)
    (hf : isPM mem a y = false) : isPM mem' a y = false := by
  rw [h.pm ha hax hy hyx]
  split
  · exact isPF_fb_or hf
  · exact hf

theorem orig' (c p : U64) (hc : (remG G x).par c = some p) : revOf mem' p = true := by
  change Mdb.removePar x G.par c = some p at hc
  unfold Mdb.removePar at hc
  by_cases hcx : c = x
  · simp [hcx] at hc
  simp only [hcx, ↓reduceIte] at hc
  by_cases hpx : G.par c = some x
  · rw [if_pos hpx] at hc
    have hp := (h.hM.tree.par_mem _ _ hc).2
    have hpx' : p ≠ x := fun e => h.hM.no_self_par (e ▸ hc)
    rw [h.rz hp hpx']; exact h.hI.orig _ _ hc
  · rw [if_neg hpx] at hc
    have hp := (h.hM.tree.par_mem _ _ hc).2
    have hpx' : p ≠ x := fun e => hpx (e ▸ hc)
    rw [h.rz hp hpx']; exact h.hI.orig _ _ hc

theorem desc' (a y : U64) (hd : Mdb.Desc (remG G x).par y a) : isPM mem' a y = true := by
  obtain ⟨hyx, hax, hd⟩ := (h.descE y a).1 hd
  obtain ⟨hy, ha⟩ := desc_mem h.hM hd
  have h0 := h.hI.desc a y hd
  rw [h.pm ha hax hy hyx]
  split
  · rename_i hyn
    obtain ⟨hn0, rfl⟩ := hyn
    -- `x` is right before `next x`, hence `a` or in `a`'s block
    have hpn : prevOf mem (nextOf mem x) = x := (h.hM.next_link h.hx hn0).2
    have hxa : Mdb.Desc G.par x a := by
      rcases h.hM.prev_in_block hd with e | e
      · rw [hpn] at e; exact absurd e.symm hax
      · rwa [hpn] at e
    have hx1 := h.hI.desc a x hxa
    unfold isPM isPF at h0 hx1
    unfold isPF
    cases hfx : fbOf mem x
    · simpa using h0
    · simp only [hfx, Bool.not_true, Bool.and_false, Bool.or_false, Bool.and_true, Bool.or_true] at hx1 ⊢
      simp only [Bool.and_eq_true] at hx1 h0 ⊢
      refine ⟨h0.1, ?_⟩
      revert hx1; split <;> simp_all
  · exact h0

theorem after' (y : U64) (hy : y ∈ (remG G x).chains.flatten) (hn : nextOf mem' y ≠ 0#u64) (a : U64)
    (ha : a = y ∨ Mdb.Desc (remG G x).par y a)
    (hnd : ¬ Mdb.Desc (remG G x).par (nextOf mem' y) a) : isPM mem' a (nextOf mem' y) = false := by
  obtain ⟨hy, hyx⟩ := (h.memE y).1 hy
  have ha' : a = y ∨ Mdb.Desc G.par y a := by
    rcases ha with e | e
    · exact Or.inl e
    · exact Or.inr ((h.descE y a).1 e).2.2
  have hax : a ≠ x := by
    rcases ha with e | e
    · rw [e]; exact hyx
    · exact ((h.descE y a).1 e).2.1
  have ham : a ∈ G.chains.flatten := by
    rcases ha' with e | e
    · rw [e]; exact hy
    · exact (desc_mem h.hM e).2
  rw [h.hnext y (h.sl hy) hyx] at hn hnd ⊢
  by_cases hyp : prevOf mem x ≠ 0#u64 ∧ y = prevOf mem x
  · -- `y = prev x`: the new pair (`prev x`, `next x`)
    rw [if_pos hyp] at hn hnd ⊢
    obtain ⟨hp0, rfl⟩ := hyp
    have hxl := h.hM.prev_link h.hx hp0
    have hN := (h.hM.next_link h.hx hn).1
    have hNx : nextOf mem x ≠ x := by
      rcases h.hM.next_mem h.hx with e | ⟨-, e⟩
      · exact absurd e hn
      · exact e
    have hnd' : ¬ Mdb.Desc G.par (nextOf mem x) a := fun e => hnd ((h.descE _ a).2 ⟨hNx, hax, e⟩)
    by_cases hxa : Mdb.Desc G.par x a
    · -- `x` was in `a`'s block, and was its last element
      exact h.pm_false ham hax hN hNx (h.hI.after x h.hx hn a (Or.inr hxa) hnd')
    · -- `x` was after `a`'s block: the chunk and badge parts
      have hx0 : x ≠ 0#u64 := (h.sl h.hx).ne_zero h.hP
      have h1 := h.hI.after (prevOf mem x) hxl.1 (by rw [hxl.2]; exact hx0) a ha' (by rw [hxl.2]; exact hxa)
      rw [hxl.2] at h1
      rw [h.pm ham hax hN hNx, if_pos ⟨hn, rfl⟩]
      obtain ⟨ch, hch, A, B, C, he, hxB⟩ := h.hM.stretch hxl.1 ha' hxl.2 hx0 rfl hn
      have hca : Mdb.CA (srM mem) a (B ++ nextOf mem x :: C) := by
        have := h.hI.chunk ch hch; rw [he] at this; exact Mdb.chunkL_ca this
      cases hc : isPF (revOf mem a) (capV mem a) (capV mem (nextOf mem x)) (fbOf mem (nextOf mem x) || fbOf mem x)
      · rfl
      exfalso
      unfold isPF at hc
      simp only [Bool.and_eq_true] at hc
      obtain ⟨⟨hra, hsN⟩, hbN⟩ := hc
      have hsx : srM mem a x = true := Mdb.ca_use hca hsN x hxB
      unfold isPM isPF at h1
      unfold srM at hsx
      rw [hra, hsx] at h1
      cases hba : isBadged (capV mem a)
      · simp [hba] at h1
      rw [hba] at h1 hbN
      simp only [↓reduceIte, Bool.true_and] at h1 hbN
      have ha0 : badgeF (capV mem a) ≠ 0#u64 := by intro e; simp [e] at h1
      have e0 : (badgeF (capV mem a) == 0#u64) = false := by simpa using ha0
      rw [e0, Bool.false_or] at h1 hbN
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', Bool.or_eq_false_iff] at hbN
      obtain ⟨hbNa, hfN, hfx⟩ := hbN
      rw [hfx] at h1
      simp only [Bool.not_false, Bool.and_true, beq_eq_false_iff_ne] at h1
      have hbx := (srB_badged hba hsx).1
      have hfN' := h.hI.badges x h.hx hn hbx (by unfold srM; exact srB_badged_trans hba hsx hsN)
        (by rw [hbNa]; exact h1) (by rw [hbNa]; exact ha0)
      rw [hfN'] at hfN; cases hfN
  · -- other slots: their pair is unchanged
    rw [if_neg hyp] at hn hnd ⊢
    have hw := (h.hM.next_link hy hn).1
    have hwx : nextOf mem y ≠ x := by
      intro e
      have := (h.hM.next_link hy hn).2
      rw [e] at this
      exact hyp ⟨fun e0 => by rw [e0] at this; exact (h.sl hy).ne_zero h.hP this.symm, this.symm⟩
    have hnd' : ¬ Mdb.Desc G.par (nextOf mem y) a := fun e => hnd ((h.descE _ a).2 ⟨hwx, hax, e⟩)
    exact h.pm_false ham hax hw hwx (h.hI.after y hy hn a ha' hnd')

theorem sm {u v : U64} (hu : u ∈ G.chains.flatten) (hux : u ≠ x) (hv : v ∈ G.chains.flatten) (hvx : v ≠ x) :
    srM mem' u v = srM mem u v := by
  unfold srM; rw [h.cz hu hux, h.cz hv hvx]

theorem chunk' (ch' : List U64) (hch' : ch' ∈ (remG G x).chains) : Mdb.ChunkL (srM mem') ch' := by
  change ch' ∈ Mdb.removeChains x G.chains at hch'
  unfold Mdb.removeChains at hch'
  obtain ⟨hch', -⟩ := List.mem_filter.1 hch'
  obtain ⟨ch, hch, rfl⟩ := List.mem_map.1 hch'
  letI : BEq U64 := instBEqOfDecidableEq
  have hchm : ∀ z, z ∈ ch → z ∈ G.chains.flatten := fun z hz => List.mem_flatten.2 ⟨_, hch, hz⟩
  have hnd0 : ch.Nodup := (List.nodup_flatten.1 h.hM.tree.nodup).1 _ hch
  have hne : ∀ z, z ∈ ch.erase x → z ≠ x := fun z hz e => by
    subst e; exact (List.Nodup.not_mem_erase hnd0) hz
  have hm : ∀ z, z ∈ ch.erase x → z ∈ G.chains.flatten := fun z hz => hchm z (List.erase_subset hz)
  have hk : Mdb.ChunkL (srM mem) (ch.erase x) := by
    by_cases hxc : x ∈ ch
    · obtain ⟨A, B, rfl⟩ := List.append_of_mem hxc
      rw [Mdb.erase_mid (Mdb.nodup_mid hnd0).1]
      exact Mdb.chunkL_erase (h.hI.chunk _ hch)
    · rw [Mdb.erase_not_mem' hxc]; exact h.hI.chunk _ hch
  exact Mdb.chunkL_congr hk (fun u hu v hv => h.sm (hm u hu) (hne u hu) (hm v hv) (hne v hv))

theorem badges' (y : U64) (hy : y ∈ (remG G x).chains.flatten) (hn : nextOf mem' y ≠ 0#u64)
    (hbg : isBadged (capV mem' y) = true) (hsr : srM mem' y (nextOf mem' y) = true)
    (hbne : badgeF (capV mem' y) ≠ badgeF (capV mem' (nextOf mem' y)))
    (hb0 : badgeF (capV mem' (nextOf mem' y)) ≠ 0#u64) : fbOf mem' (nextOf mem' y) = true := by
  obtain ⟨hy, hyx⟩ := (h.memE y).1 hy
  rw [h.hnext y (h.sl hy) hyx] at hn hsr hbne hb0 ⊢
  rw [h.cz hy hyx] at hbg hbne
  by_cases hyp : prevOf mem x ≠ 0#u64 ∧ y = prevOf mem x
  · rw [if_pos hyp] at hn hsr hbne hb0 ⊢
    obtain ⟨hp0, rfl⟩ := hyp
    have hxl := h.hM.prev_link h.hx hp0
    have hN := (h.hM.next_link h.hx hn).1
    have hNx : nextOf mem x ≠ x := by
      rcases h.hM.next_mem h.hx with e | ⟨-, e⟩
      · exact absurd e hn
      · exact e
    rw [h.cz hN hNx] at hbne hb0
    rw [h.sm hy hyx hN hNx] at hsr
    rw [h.hfb _ (h.sl hN) hNx, if_pos ⟨hn, rfl⟩]
    cases hfx : fbOf mem x
    · rw [Bool.or_false]
      have hx0 : x ≠ 0#u64 := (h.sl h.hx).ne_zero h.hP
      obtain ⟨ch, hch, A, B, C, he, hxB⟩ := h.hM.stretch hxl.1 (Or.inl rfl) hxl.2 hx0 rfl hn
      have hca : Mdb.CA (srM mem) (prevOf mem x) (B ++ nextOf mem x :: C) := by
        have := h.hI.chunk ch hch; rw [he] at this; exact Mdb.chunkL_ca this
      have hsx : srM mem (prevOf mem x) x = true := Mdb.ca_use hca hsr x hxB
      unfold srM at hsx hsr
      have hbx := (srB_badged hbg hsx).1
      by_cases hbxN : badgeF (capV mem x) = badgeF (capV mem (nextOf mem x))
      · have := h.hI.badges (prevOf mem x) hxl.1 (by rw [hxl.2]; exact hx0) hbg (by rw [hxl.2]; exact hsx)
          (by rw [hxl.2, hbxN]; exact hbne) (by rw [hxl.2, hbxN]; exact hb0)
        rw [hxl.2, hfx] at this; cases this
      · exact h.hI.badges x h.hx hn hbx (by unfold srM; exact srB_badged_trans hbg hsx hsr) hbxN hb0
    · simp
  · rw [if_neg hyp] at hn hsr hbne hb0 ⊢
    have hw := (h.hM.next_link hy hn).1
    have hwx : nextOf mem y ≠ x := by
      intro e
      have := (h.hM.next_link hy hn).2
      rw [e] at this
      exact hyp ⟨fun e0 => by rw [e0] at this; exact (h.sl hy).ne_zero h.hP this.symm, this.symm⟩
    rw [h.cz hw hwx] at hbne hb0
    rw [h.sm hy hyx hw hwx] at hsr
    have := h.hI.badges y hy hn hbg hsr hbne hb0
    rw [h.hfb _ (h.sl hw) hwx]
    split
    · simp [this]
    · exact this

theorem utrev' (z : U64) (hz : z ∈ (remG G x).chains.flatten) (hu : isUt (capV mem' z) = true) :
    revOf mem' z = true := by
  obtain ⟨hz, hzx⟩ := (h.memE z).1 hz
  rw [h.cz hz hzx] at hu; rw [h.rz hz hzx]; exact h.hI.utrev z hz hu

theorem self' (z : U64) (hz : z ∈ (remG G x).chains.flatten) (hzb : isZb (capV mem' z) = false) :
    srM mem' z z = true := by
  obtain ⟨hz, hzx⟩ := (h.memE z).1 hz
  rw [h.cz hz hzx] at hzb; rw [h.sm hz hzx hz hzx]; exact h.hI.self z hz hzb

/-- **`MdbInv` after emptying a slot.** -/
theorem inv : MdbInv mem' (remG G x) :=
  ⟨h.orig', h.desc', h.after', h.chunk', h.badges', h.utrev', h.self'⟩

end EmpCtx

end

end Fl4Proofs.P3
