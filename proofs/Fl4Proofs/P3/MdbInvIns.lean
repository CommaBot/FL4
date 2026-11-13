/-
P3 (DESIGN.md §9), CSpace: `MdbInv` after inserting `dest` after `src`
(`cdt::insert`), at the level of the slot contents and the ghost tree.

The new cap `c` must be derived from `src`'s cap: the same shape (so the
same region, `srB`), the same badge or a fresh badge from an unbadged cap,
not from an untyped cap with children; `src`'s cap may change to `c1` of
the same shape and badge (`set_untyped_cap_as_full`). The new slot's
revocable and first-badged bits are `is_cap_revocable c src`, and the ghost
parent is `src` iff FL4's parent test from `src` passes (`b`); this is
l4v's `should_be_parent_of` (shown in `MdbSpec`).
-/
import Fl4Proofs.P3.MdbInv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

theorem desc_tail_child {par : U64 → Option U64} {y x : U64} (h : Mdb.Desc par y x) : ∃ z, par z = some x := by
  obtain ⟨b, -, hb⟩ := Relation.TransGen.tail'_iff.1 h; exact ⟨b, hb⟩

/-- `src` passes its own parent test (when revocable and not a zombie). -/
theorem isPF_self {ca : capability.Cap} (hs : srB ca ca = true) : isPF true ca ca false = true := by
  unfold isPF; simp [hs]

/-- **The sibling condition** (`hsib` of `insert_refines`): if FL4's parent
test from `src` fails for a derived cap, `src` has no descendants. -/
theorem MdbInv.sib {th : TypedHeap} {mem : U64 → U64} {G : MdbGhost} (hI : MdbInv mem G)
    {src : U64} (hsrc : src ∈ G.chains.flatten) (hzb : isZb (capV mem src) = false) {c : capability.Cap}
    (hsh : shape c = shape (capV mem src)) (hbd : badgeF c = badgeF (capV mem src) ∨ badgeF (capV mem src) = 0#u64)
    (hb : isPF (revOf mem src) (capV mem src) c (revF c (capV mem src)) = false) :
    ∀ y, ¬ Mdb.Desc G.par y src := by
  intro y hy
  obtain ⟨z, hz⟩ := desc_tail_child hy
  have hr := hI.orig z src hz
  rw [hr] at hb
  have := isPF_child (isPF_self (hI.self src hsrc hzb)) hsh hbd
  rw [hb] at this; cases this

theorem mem_flatten_ins {chains : List (List U64)} {src dest z : U64} (hsrc : src ∈ chains.flatten) :
    z ∈ (chains.map (Mdb.insAfter src dest)).flatten ↔ z = dest ∨ z ∈ chains.flatten := by
  simp only [List.mem_flatten, List.mem_map]
  constructor
  · rintro ⟨_, ⟨ch, hch, rfl⟩, hz⟩
    by_cases hs : src ∈ ch
    · rcases (mem_insAfter hs).1 hz with h | h
      · exact Or.inl h
      · exact Or.inr ⟨ch, hch, h⟩
    · rw [Mdb.insAfter_of_not_mem hs] at hz; exact Or.inr ⟨ch, hch, hz⟩
  · rintro (rfl | ⟨ch, hch, hz⟩)
    · obtain ⟨ch, hch, hs⟩ := List.mem_flatten.1 hsrc
      exact ⟨_, ⟨ch, hch, rfl⟩, (mem_insAfter hs).2 (Or.inl rfl)⟩
    · by_cases hs : src ∈ ch
      · exact ⟨_, ⟨ch, hch, rfl⟩, (mem_insAfter hs).2 (Or.inr hz)⟩
      · exact ⟨_, ⟨ch, hch, rfl⟩, by rw [Mdb.insAfter_of_not_mem hs]; exact hz⟩

theorem np_desc_iff {par : U64 → Option U64} {src x : U64} (b : Bool) :
    ((if b then some src else par src) = some x ∨
      ∃ p, (if b then some src else par src) = some p ∧ Mdb.Desc par p x) ↔
      (b = true ∧ x = src) ∨ Mdb.Desc par src x := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, false_and, false_or]
    constructor
    · rintro (h | ⟨p, hp, h⟩)
      · exact Relation.TransGen.single h
      · exact Relation.TransGen.head hp h
    · intro h
      obtain ⟨p, hp, h2⟩ := Relation.TransGen.head'_iff.1 h
      rcases Relation.reflTransGen_iff_eq_or_transGen.1 h2 with rfl | h3
      · exact Or.inl hp
      · exact Or.inr ⟨p, hp, h3⟩
  · simp only [↓reduceIte, Option.some.injEq, true_and]
    constructor
    · rintro (rfl | ⟨p, rfl, h⟩)
      · exact Or.inl rfl
      · exact Or.inr h
    · rintro (rfl | h)
      · exact Or.inl rfl
      · exact Or.inr ⟨src, rfl, h⟩

/-- The situation of an insertion, at the level of the slot contents. -/
structure InsCtx (th : TypedHeap) (mem mem' : U64 → U64) (G : MdbGhost) (src dest : U64)
    (c c1 : capability.Cap) : Prop where
  hM : MdbLinks th mem G
  hI : MdbInv mem G
  hsrc : src ∈ G.chains.flatten
  hd : IsSlot th dest
  hdest : dest ∉ G.chains.flatten
  hnext : ∀ a, IsSlot th a → nextOf mem' a =
    if a = dest then nextOf mem src else if a = src then dest else nextOf mem a
  hcap : ∀ a, IsSlot th a → capV mem' a = if a = dest then c else if a = src then c1 else capV mem a
  hrev : ∀ a, IsSlot th a → revOf mem' a = if a = dest then revF c (capV mem src) else revOf mem a
  hfb : ∀ a, IsSlot th a → fbOf mem' a = if a = dest then revF c (capV mem src) else fbOf mem a
  hsh : shape c = shape (capV mem src)
  hbd : badgeF c = badgeF (capV mem src) ∨ badgeF (capV mem src) = 0#u64
  hsh1 : shape c1 = shape (capV mem src)
  hbd1 : badgeF c1 = badgeF (capV mem src)
  hut : isUt (capV mem src) = true → ∀ y, ¬ Mdb.Desc G.par y src
  hzb : isZb (capV mem src) = false

namespace InsCtx
variable {th : TypedHeap} {mem mem' : U64 → U64} {G : MdbGhost} {src dest : U64} {c c1 : capability.Cap}
  (h : InsCtx th mem mem' G src dest c c1)
include h

theorem sl {z : U64} (hz : z ∈ G.chains.flatten) : IsSlot th z := ((h.hM.members z).1 hz).1
theorem dne {z : U64} (hz : z ∈ G.chains.flatten) : z ≠ dest := fun e => h.hdest (e ▸ hz)
theorem sd : src ≠ dest := h.dne h.hsrc

theorem cz {z : U64} (hz : z ∈ G.chains.flatten) :
    shape (capV mem' z) = shape (capV mem z) ∧ badgeF (capV mem' z) = badgeF (capV mem z) := by
  rw [h.hcap z (h.sl hz), if_neg (h.dne hz)]
  by_cases hzs : z = src
  · subst hzs; simp [h.hsh1, h.hbd1]
  · simp [hzs]
theorem rz {z : U64} (hz : z ∈ G.chains.flatten) : revOf mem' z = revOf mem z := by
  rw [h.hrev z (h.sl hz), if_neg (h.dne hz)]
theorem fz {z : U64} (hz : z ∈ G.chains.flatten) : fbOf mem' z = fbOf mem z := by
  rw [h.hfb z (h.sl hz), if_neg (h.dne hz)]
theorem nz {z : U64} (hz : z ∈ G.chains.flatten) (hzs : z ≠ src) : nextOf mem' z = nextOf mem z := by
  rw [h.hnext z (h.sl hz), if_neg (h.dne hz), if_neg hzs]
theorem ns : nextOf mem' src = dest := by rw [h.hnext src (h.sl h.hsrc), if_neg h.sd, if_pos rfl]
theorem nd : nextOf mem' dest = nextOf mem src := by rw [h.hnext dest h.hd, if_pos rfl]
theorem cd : capV mem' dest = c := by rw [h.hcap dest h.hd, if_pos rfl]
theorem cs : capV mem' src = c1 := by rw [h.hcap src (h.sl h.hsrc), if_neg h.sd, if_pos rfl]
theorem rd : revOf mem' dest = revF c (capV mem src) := by rw [h.hrev dest h.hd, if_pos rfl]
theorem fd : fbOf mem' dest = revF c (capV mem src) := by rw [h.hfb dest h.hd, if_pos rfl]

theorem pm {x y : U64} (hx : x ∈ G.chains.flatten) (hy : y ∈ G.chains.flatten) : isPM mem' x y = isPM mem x y := by
  unfold isPM
  rw [h.rz hx, h.fz hy]
  exact isPF_congr (h.cz hx).1 (h.cz hx).2 (h.cz hy).1 (h.cz hy).2
theorem sm {x y : U64} (hx : x ∈ G.chains.flatten) (hy : y ∈ G.chains.flatten) : srM mem' x y = srM mem x y := by
  unfold srM; exact srB_congr (h.cz hx).1 (h.cz hy).1

theorem nm (h0 : nextOf mem src ≠ 0#u64) : nextOf mem src ∈ G.chains.flatten ∧ nextOf mem src ≠ src := by
  rcases h.hM.next_mem h.hsrc with h1 | h1
  · exact absurd h1 h0
  · exact h1

theorem nxm {y : U64} (hy : y ∈ G.chains.flatten) (h0 : nextOf mem y ≠ 0#u64) : nextOf mem y ∈ G.chains.flatten := by
  rcases h.hM.next_mem hy with h1 | h1
  · exact absurd h1 h0
  · exact h1.1

theorem pd (z : U64) : G.par z ≠ some dest := fun e => h.hdest (h.hM.tree.par_mem z dest e).2
theorem dn : G.par dest = none := by
  cases e : G.par dest with
  | none => rfl
  | some p => exact absurd (h.hM.tree.par_mem dest p e).1 h.hdest

theorem desc (b : Bool) (y x : U64) : Mdb.Desc (insG G src dest b).par y x ↔
    Mdb.Desc G.par y x ∨ (y = dest ∧ ((b = true ∧ x = src) ∨ Mdb.Desc G.par src x)) := by
  have hnp : (if b then some src else G.par src) ≠ some dest := by
    cases b <;> simp [h.sd, h.pd src]
  show Mdb.Desc (Function.update G.par dest _) y x ↔ _
  rw [Mdb.desc_update_iff h.pd h.dn hnp, np_desc_iff]

theorem no_desc_dest (x : U64) : ¬ Mdb.Desc G.par x dest := Mdb.not_desc_of_no_child h.pd
theorem dest_no_desc (x : U64) : ¬ Mdb.Desc G.par dest x := fun e => h.hdest (desc_mem h.hM e).1

theorem memI (b : Bool) (z : U64) : z ∈ (insG G src dest b).chains.flatten ↔ z = dest ∨ z ∈ G.chains.flatten :=
  mem_flatten_ins h.hsrc

/-- The parent test from `src` to `dest` is `b`. -/
theorem psd : isPM mem' src dest = isPF (revOf mem src) (capV mem src) c (revF c (capV mem src)) := by
  unfold isPM
  rw [h.rz h.hsrc, h.cs, h.cd, h.fd]
  exact isPF_congr (by rw [h.hsh1]) (by rw [h.hbd1]) rfl rfl

end InsCtx

namespace InsCtx
variable {th : TypedHeap} {mem mem' : U64 → U64} {G : MdbGhost} {src dest : U64} {c c1 : capability.Cap}
  (h : InsCtx th mem mem' G src dest c c1)
include h

local notation "bI" => isPF (revOf mem src) (capV mem src) c (revF c (capV mem src))

theorem orig' (z p : U64) (hz : (insG G src dest bI).par z = some p) : revOf mem' p = true := by
  change Function.update G.par dest (if bI then some src else G.par src) z = some p at hz
  by_cases hzd : z = dest
  · subst hzd
    rw [Function.update_self] at hz
    cases hb : bI
    · rw [hb] at hz; simp only [Bool.false_eq_true, ↓reduceIte] at hz
      rw [h.rz (h.hM.tree.par_mem _ _ hz).2]; exact h.hI.orig _ _ hz
    · rw [hb] at hz
      have hp : p = src := by simpa using hz.symm
      rw [hp, h.rz h.hsrc]
      simp only [isPF, Bool.and_eq_true] at hb
      exact hb.1.1
  · rw [Function.update_of_ne hzd] at hz
    rw [h.rz (h.hM.tree.par_mem _ _ hz).2]; exact h.hI.orig _ _ hz

theorem desc' (x y : U64) (hd : Mdb.Desc (insG G src dest bI).par y x) : isPM mem' x y = true := by
  rcases (h.desc bI y x).1 hd with hd | ⟨hy, hd⟩
  · obtain ⟨h1, h2⟩ := desc_mem h.hM hd
    rw [h.pm h2 h1]; exact h.hI.desc x y hd
  · rw [hy]
    rcases hd with ⟨hb, hxs⟩ | hd
    · rw [hxs, h.psd]; exact hb
    · have hx := (desc_mem h.hM hd).2
      have h0 := h.hI.desc x src hd
      unfold isPM at h0 ⊢
      rw [h.rz hx, h.cd, h.fd, isPF_congr (h.cz hx).1 (h.cz hx).2 rfl rfl]
      exact isPF_child h0 h.hsh h.hbd

/-- From `dest`, the slot after it (`src`'s old next) fails the test. -/
theorem after_dest (hn : nextOf mem src ≠ 0#u64) :
    isPF (revF c (capV mem src)) c (capV mem (nextOf mem src)) (fbOf mem (nextOf mem src)) = false := by
  obtain ⟨hN, -⟩ := h.nm hn
  cases hrv : revF c (capV mem src)
  · simp [isPF]
  rcases revF_cases h.hsh hrv with ⟨hbc, hbne⟩ | hut'
  · have hs0 : badgeF (capV mem src) = 0#u64 := h.hbd.resolve_left hbne
    have hbs : isBadged (capV mem src) = true := by rw [← isBadged_of_shape h.hsh]; exact hbc
    have hc0 : badgeF c ≠ 0#u64 := by intro e; exact hbne (by rw [e, hs0])
    unfold isPF
    by_cases hsr : srB c (capV mem (nextOf mem src)) = true
    · have hsr' : srM mem src (nextOf mem src) = true := by
        unfold srM; rw [← srB_congr h.hsh rfl]; exact hsr
      by_cases hbN : badgeF (capV mem (nextOf mem src)) = badgeF c
      · have hfN := h.hI.badges src h.hsrc hn hbs hsr' (by rw [hs0, hbN]; exact Ne.symm hc0)
          (by rw [hbN]; exact hc0)
        simp [hfN, hbc, hc0]
      · simp [hbN, hbc, hc0]
    · simp at hsr; simp [hsr]
  · have hus : isUt (capV mem src) = true := by rw [← isUt_of_shape h.hsh]; exact hut'
    have ha := h.hI.after src h.hsrc hn src (Or.inl rfl) (h.hut hus _)
    unfold isPM isPF at ha
    rw [h.hI.utrev src h.hsrc hus] at ha
    have hnb : isBadged (capV mem src) = false := by
      cases e : capV mem src <;> simp_all [isUt, isBadged]
    simp only [Bool.true_and, hnb, Bool.false_eq_true, ↓reduceIte, Bool.and_true] at ha
    unfold isPF
    rw [srB_congr h.hsh rfl, ha]; simp

theorem after' (y : U64) (hy : y ∈ (insG G src dest bI).chains.flatten) (hn : nextOf mem' y ≠ 0#u64) (x : U64)
    (hx : x = y ∨ Mdb.Desc (insG G src dest bI).par y x)
    (hnd : ¬ Mdb.Desc (insG G src dest bI).par (nextOf mem' y) x) : isPM mem' x (nextOf mem' y) = false := by
  rcases (h.memI bI y).1 hy with hyd | hy
  · rw [hyd] at hn hnd hx ⊢
    rw [h.nd] at hn hnd ⊢
    obtain ⟨hN, -⟩ := h.nm hn
    rcases hx with hxd | hx
    · subst hxd
      unfold isPM
      rw [h.rd, h.cd, h.fz hN, isPF_congr rfl rfl (h.cz hN).1 (h.cz hN).2]
      exact h.after_dest hn
    · have hx' : x = src ∨ Mdb.Desc G.par src x := by
        rcases (h.desc bI dest x).1 hx with e | ⟨-, ⟨-, e⟩ | e⟩
        · exact absurd e (h.dest_no_desc x)
        · exact Or.inl e
        · exact Or.inr e
      have hnd' : ¬ Mdb.Desc G.par (nextOf mem src) x := fun e => hnd ((h.desc bI _ x).2 (Or.inl e))
      have hxm : x ∈ G.chains.flatten := by
        rcases hx' with e | e
        · rw [e]; exact h.hsrc
        · exact (desc_mem h.hM e).2
      rw [h.pm hxm hN]
      exact h.hI.after src h.hsrc hn x hx' hnd'
  · by_cases hys : y = src
    · rw [hys] at hn hnd hx hy ⊢
      rw [h.ns] at hn hnd ⊢
      rcases hx with hxy | hx
      · rw [hxy] at hnd ⊢
        rw [h.psd]
        cases hb : bI
        · rfl
        · exact absurd ((h.desc bI dest src).2 (Or.inr ⟨rfl, Or.inl ⟨hb, rfl⟩⟩)) hnd
      · have hx' : Mdb.Desc G.par src x := ((h.desc bI src x).1 hx).resolve_right (fun e => h.sd e.1)
        exact absurd ((h.desc bI dest x).2 (Or.inr ⟨rfl, Or.inr hx'⟩)) hnd
    · rw [h.nz hy hys] at hn hnd ⊢
      have hw := h.nxm hy hn
      have hx' : x = y ∨ Mdb.Desc G.par y x := by
        rcases hx with e | e
        · exact Or.inl e
        · exact Or.inr (((h.desc bI y x).1 e).resolve_right (fun e => h.dne hy e.1))
      have hnd' : ¬ Mdb.Desc G.par (nextOf mem y) x := fun e => hnd ((h.desc bI _ x).2 (Or.inl e))
      have hxm : x ∈ G.chains.flatten := by
        rcases hx' with e | e
        · rw [e]; exact hy
        · exact (desc_mem h.hM e).2
      rw [h.pm hxm hw]
      exact h.hI.after y hy hn x hx' hnd'

theorem chunk' (ch' : List U64) (hch' : ch' ∈ (insG G src dest bI).chains) : Mdb.ChunkL (srM mem') ch' := by
  obtain ⟨ch, hch, rfl⟩ := List.mem_map.1 hch'
  have hchm : ∀ z, z ∈ ch → z ∈ G.chains.flatten := fun z hz => List.mem_flatten.2 ⟨_, hch, hz⟩
  by_cases hsc : src ∈ ch
  · obtain ⟨A, B, rfl⟩ := List.append_of_mem hsc
    have hnd0 : (A ++ src :: B).Nodup := (List.nodup_flatten.1 h.hM.tree.nodup).1 _ hch
    rw [Mdb.insAfter_split (Mdb.nodup_mid hnd0).1]
    refine Mdb.chunkL_ins (h.hI.chunk _ hch) (fun u hu v hv => h.sm (hchm u hu) (hchm v hv))
      (fun u hu => ?_) (fun v hv => ?_) ?_
    · unfold srM; rw [h.cd]; exact srB_congr (h.cz (hchm u hu)).1 h.hsh
    · unfold srM; rw [h.cd]; exact srB_congr h.hsh (h.cz (hchm v hv)).1
    · unfold srM; rw [h.cs, h.cd, srB_congr h.hsh1 h.hsh]; exact h.hI.self src h.hsrc h.hzb
  · rw [Mdb.insAfter_of_not_mem hsc]
    exact Mdb.chunkL_congr (h.hI.chunk _ hch) (fun u hu v hv => h.sm (hchm u hu) (hchm v hv))

theorem badges' (y : U64) (hy : y ∈ (insG G src dest bI).chains.flatten) (hn : nextOf mem' y ≠ 0#u64)
    (hbg : isBadged (capV mem' y) = true) (hsr : srM mem' y (nextOf mem' y) = true)
    (hbne : badgeF (capV mem' y) ≠ badgeF (capV mem' (nextOf mem' y)))
    (hb0 : badgeF (capV mem' (nextOf mem' y)) ≠ 0#u64) : fbOf mem' (nextOf mem' y) = true := by
  rcases (h.memI bI y).1 hy with hyd | hy
  · rw [hyd] at hn hsr hbne hb0 hbg ⊢
    rw [h.nd] at hn hsr hbne hb0 ⊢
    obtain ⟨hN, -⟩ := h.nm hn
    rw [h.cd] at hbg hbne
    unfold srM at hsr; rw [h.cd] at hsr
    rw [h.fz hN]
    have hbs : isBadged (capV mem src) = true := by rw [← isBadged_of_shape h.hsh]; exact hbg
    rw [(h.cz hN).2] at hbne hb0
    refine h.hI.badges src h.hsrc hn hbs (by unfold srM; rw [← srB_congr h.hsh (h.cz hN).1]; exact hsr) ?_ hb0
    rcases h.hbd with e | e
    · rw [← e]; exact hbne
    · rw [e]; exact Ne.symm hb0
  · by_cases hys : y = src
    · rw [hys] at hn hsr hbne hb0 hbg ⊢
      rw [h.ns] at hn hsr hbne hb0 ⊢
      rw [h.fd]
      rw [h.cs] at hbg hbne
      rw [h.cd] at hbne hb0
      have hbc : isBadged c = true := by rw [isBadged_of_shape h.hsh, ← isBadged_of_shape h.hsh1]; exact hbg
      rw [revF_badged h.hsh hbc, ← h.hbd1]
      simpa using Ne.symm hbne
    · rw [h.nz hy hys] at hn hsr hbne hb0 ⊢
      have hw := h.nxm hy hn
      rw [h.fz hw]
      rw [(h.cz hy).2, (h.cz hw).2] at hbne
      rw [(h.cz hw).2] at hb0
      rw [isBadged_of_shape (h.cz hy).1] at hbg
      exact h.hI.badges y hy hn hbg (by rw [← h.sm hy hw]; exact hsr) hbne hb0

theorem utrev' (x : U64) (hx : x ∈ (insG G src dest bI).chains.flatten) (hu : isUt (capV mem' x) = true) :
    revOf mem' x = true := by
  rcases (h.memI bI x).1 hx with hxd | hx
  · rw [hxd] at hu ⊢; rw [h.rd]; rw [h.cd] at hu; exact revF_ut hu
  · rw [h.rz hx]; rw [isUt_of_shape (h.cz hx).1] at hu; exact h.hI.utrev x hx hu

theorem self' (x : U64) (hx : x ∈ (insG G src dest bI).chains.flatten) (hz : isZb (capV mem' x) = false) :
    srM mem' x x = true := by
  rcases (h.memI bI x).1 hx with hxd | hx
  · rw [hxd]; unfold srM; rw [h.cd, srB_congr h.hsh h.hsh]; exact h.hI.self src h.hsrc h.hzb
  · rw [isZb_of_shape (h.cz hx).1] at hz
    rw [h.sm hx hx]; exact h.hI.self x hx hz

/-- **`MdbInv` after an insertion.** -/
theorem inv : MdbInv mem' (insG G src dest bI) :=
  ⟨h.orig', h.desc', h.after', h.chunk', h.badges', h.utrev', h.self'⟩

end InsCtx

end

end Fl4Proofs.P3
