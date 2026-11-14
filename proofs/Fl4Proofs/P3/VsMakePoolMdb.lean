/-
P3 (DESIGN.md §9), VSpace: the MDB invariant after ASIDControl `MakePool`'s
`cdt::insert` of the new ASID-pool cap as a child of the untyped cap.

`MakePool` links the pool cap with `cdt::insert` (seL4 `cteInsert`, l4v
`cap_insert`), not `insert_new_cap`: the new slot's revocable and
first-badged bits are `is_cap_revocable` of an ASID-pool cap from an
untyped cap, false. An ASID-pool cap is `same_region_as` only ASID-pool
caps to the same pool (`srB_ap_left`, `srB_ap_right`).

* `InsWords.fbOf'`: the first-badged bits after `cdt::insert`;
* `InsACtx.inv`: `MdbInv` after the insertion, from the range hypotheses
  of `InsNCtx` (l4v `caps_no_overlap`, `descendants_range_in` for the
  pool's frame);
* `utinv_pool`: the untyped invariant afterwards, for an untyped cap with no
  descendants and a full free index, the pool cap's range being the untyped
  cap's.
-/
import Fl4Proofs.P3.UntypedUtInv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P3 Classical

noncomputable section
set_option linter.unusedSimpArgs false

section Fields
variable {th : TypedHeap} {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {s s' : S} {c srcC : capability.Cap} {src dest : U64}

theorem InsWords.fbOf' (hW : InsWords (L := L) th s s' c srcC src dest) {a : U64} (ha : IsSlot th a)
    (hne : src ≠ dest) :
    fbOf (L.mem s') a = if a = dest then revF c srcC else fbOf (L.mem s) a := by
  rw [show fbOf (L.mem s') a = (L.mem s' (wordOf a 24#u64)).bv.getLsbD 49 from rfl, hW a ha _ off24]
  by_cases h1 : a = dest
  · simp only [h1, ↓reduceIte, lit_ne]
    show (setBitF (setBitF _ 48 _) 49 _).getLsbD 49 = _
    rw [getLsbD_setBitF _ _ _ (Or.inr rfl) (Or.inr rfl)]
    simp
  · by_cases h2 : a = src
    · subst h2
      simp only [h1, ↓reduceIte]
      show (setNextF _ _).getLsbD 49 = _
      rw [getLsbD_setNextF _ _ 49 (by decide) (by decide)]; rfl
    · simp only [h1, h2, ↓reduceIte, lit_ne, and_false]; rfl

end Fields

/-! ## ASID-pool caps and `same_region_as` -/

theorem physF_ap (q b : U64) : physF (.AsidPool q b) = true := ok_inj (phys_eq _).symm
theorem ptrF_ap (q b : U64) : ptrF (.AsidPool q b) = q := ok_inj (ptr_eq _).symm
theorem sizeF_ap (q b : U64) : sizeF (.AsidPool q b) = fl4_abi.consts.bits.ASID_POOL := ok_inj (size_eq _).symm

theorem srB_ap_left {q b : U64} {v : capability.Cap} (h : srB (.AsidPool q b) v = true) :
    shape v = shape (.AsidPool q b) := by
  have h' := srB_eq (.AsidPool q b) v
  rw [h] at h'
  cases v <;> simp [objects.same_region_as] at h'
  case AsidPool p' b' =>
    rw [UScalar.eq_of_val_eq h']; rfl

theorem srB_ap_right {u : capability.Cap} {q b : U64} (hu : isUt u = false) (h : srB u (.AsidPool q b) = true) :
    shape (.AsidPool q b) = shape u := by
  have h' := srB_eq u (.AsidPool q b)
  rw [h] at h'
  cases u <;> simp [isUt] at hu <;> simp [objects.same_region_as] at h'
  case AsidPool p' b' =>
    rw [UScalar.eq_of_val_eq h']; rfl

theorem srB_ap_self (q b : U64) : srB (.AsidPool q b) (.AsidPool q b) = true := by
  have h' := srB_eq (.AsidPool q b) (.AsidPool q b)
  simpa [objects.same_region_as] using h'

theorem isUt_ap (q b : U64) : isUt (.AsidPool q b) = false := rfl
theorem isBadged_ap (q b : U64) : isBadged (.AsidPool q b) = false := rfl

/-! ## The insertion -/

section
open Mdb

/-- The insertion of the ASID-pool cap `AsidPool q b` at `dest` after the
untyped cap's slot `src` (`cdt::insert`), at the level of the slot contents:
the links as `cdt::insert`'s, the new slot's bits false, and the range
hypotheses of `InsNCtx`. -/
structure InsACtx (th : TypedHeap) (mem mem' : U64 → U64) (G : MdbGhost) (src dest : U64) (q b : U64) :
    Prop where
  hM : MdbLinks th mem G
  hI : MdbInv mem G
  hsrc : src ∈ G.chains.flatten
  hd : IsSlot th dest
  hdest : dest ∉ G.chains.flatten
  hnext : ∀ a, IsSlot th a → nextOf mem' a =
    if a = dest then nextOf mem src else if a = src then dest else nextOf mem a
  hcap : ∀ a, IsSlot th a → capV mem' a = if a = dest then .AsidPool q b else capV mem a
  hrev : ∀ a, IsSlot th a → revOf mem' a = if a = dest then false else revOf mem a
  hfb : ∀ a, IsSlot th a → fbOf mem' a = if a = dest then false else fbOf mem a
  hut : isUt (capV mem src) = true
  hcr : baseF (.AsidPool q b) ≤ topF (.AsidPool q b)
  hcin : Within (.AsidPool q b) (capV mem src)
  hreg : ∀ x ∈ G.chains.flatten, physF (capV mem x) = true → baseF (capV mem x) ≤ topF (capV mem x)
  hno : ∀ x ∈ G.chains.flatten, physF (capV mem x) = true →
    Disj (capV mem x) (.AsidPool q b) ∨ (isUt (capV mem x) = true ∧ Within (capV mem src) (capV mem x))
  hdd : ∀ y, Mdb.Desc G.par y src → Disj (capV mem y) (.AsidPool q b)

namespace InsACtx
variable {th : TypedHeap} {mem mem' : U64 → U64} {G : MdbGhost} {src dest : U64} {q b : U64}
  (h : InsACtx th mem mem' G src dest q b)
include h

local notation "cA" => capability.Cap.AsidPool q b

theorem sl {z : U64} (hz : z ∈ G.chains.flatten) : IsSlot th z := ((h.hM.members z).1 hz).1
theorem dne {z : U64} (hz : z ∈ G.chains.flatten) : z ≠ dest := fun e => h.hdest (e ▸ hz)
theorem sd : src ≠ dest := h.dne h.hsrc
theorem cz {z : U64} (hz : z ∈ G.chains.flatten) : capV mem' z = capV mem z := by
  rw [h.hcap z (h.sl hz), if_neg (h.dne hz)]
theorem rz {z : U64} (hz : z ∈ G.chains.flatten) : revOf mem' z = revOf mem z := by
  rw [h.hrev z (h.sl hz), if_neg (h.dne hz)]
theorem fz {z : U64} (hz : z ∈ G.chains.flatten) : fbOf mem' z = fbOf mem z := by
  rw [h.hfb z (h.sl hz), if_neg (h.dne hz)]
theorem nz {z : U64} (hz : z ∈ G.chains.flatten) (hzs : z ≠ src) : nextOf mem' z = nextOf mem z := by
  rw [h.hnext z (h.sl hz), if_neg (h.dne hz), if_neg hzs]
theorem ns : nextOf mem' src = dest := by rw [h.hnext src (h.sl h.hsrc), if_neg h.sd, if_pos rfl]
theorem nd : nextOf mem' dest = nextOf mem src := by rw [h.hnext dest h.hd, if_pos rfl]
theorem cd : capV mem' dest = cA := by rw [h.hcap dest h.hd, if_pos rfl]
theorem rd : revOf mem' dest = false := by rw [h.hrev dest h.hd, if_pos rfl]
theorem fd : fbOf mem' dest = false := by rw [h.hfb dest h.hd, if_pos rfl]

theorem pm {x y : U64} (hx : x ∈ G.chains.flatten) (hy : y ∈ G.chains.flatten) : isPM mem' x y = isPM mem x y := by
  unfold isPM
  rw [h.rz hx, h.fz hy]
  exact isPF_congr (by rw [h.cz hx]) (by rw [h.cz hx]) (by rw [h.cz hy]) (by rw [h.cz hy])
theorem sm {x y : U64} (hx : x ∈ G.chains.flatten) (hy : y ∈ G.chains.flatten) : srM mem' x y = srM mem x y := by
  unfold srM; rw [h.cz hx, h.cz hy]

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

theorem desc (y x : U64) : Mdb.Desc (insG G src dest true).par y x ↔
    Mdb.Desc G.par y x ∨ (y = dest ∧ (x = src ∨ Mdb.Desc G.par src x)) := by
  have hnp : (if true then some src else G.par src) ≠ some dest := by simp [h.sd]
  show Mdb.Desc (Function.update G.par dest _) y x ↔ _
  rw [Mdb.desc_update_iff h.pd h.dn hnp, np_desc_iff]
  simp

theorem dest_no_desc (x : U64) : ¬ Mdb.Desc G.par dest x := fun e => h.hdest (desc_mem h.hM e).1

theorem memI (z : U64) : z ∈ (insG G src dest true).chains.flatten ↔ z = dest ∨ z ∈ G.chains.flatten :=
  mem_flatten_ins h.hsrc

theorem srcUt : ∃ q sz f d, capV mem src = .Untyped q sz f d := isUt_iff.1 h.hut

/-- No old cap is in the pool cap's region. -/
theorem k1 {v : U64} (hv : v ∈ G.chains.flatten) (hs : srB cA (capV mem v) = true) : False := by
  have e := srB_ap_left hs
  obtain ⟨hb, ht, hp⟩ := range_of_shape e
  rw [physF_ap] at hp
  rcases h.hno v hv hp with hd | ⟨hu'', -⟩
  · unfold Disj at hd; have := h.hcr; omega
  · rw [isUt_of_shape e] at hu''; cases hu''

theorem ssrc : srB (capV mem src) cA = true := (srB_ut_iff h.hut cA).2 ⟨physF_ap q b, h.hcin, h.hcr⟩

/-- Every old cap sees the pool cap as it sees the untyped cap. -/
theorem k2 {u : U64} (hu : u ∈ G.chains.flatten) : srB (capV mem u) cA = srB (capV mem u) (capV mem src) := by
  obtain ⟨q', sz, f, d, hS⟩ := h.srcUt
  have hsr := h.hreg src h.hsrc (physF_of_ut h.hut)
  apply Bool.eq_iff_iff.2
  constructor
  · intro hs
    cases hU : isUt (capV mem u)
    · have e := srB_ap_right hU hs
      obtain ⟨hb, ht, hp⟩ := range_of_shape e
      rw [physF_ap] at hp
      rcases h.hno u hu hp.symm with hd | ⟨hu', -⟩
      · exfalso; have := h.hcr; unfold Disj at hd; omega
      · rw [hU] at hu'; cases hu'
    · obtain ⟨-, hw, -⟩ := (srB_ut_iff hU cA).1 hs
      rcases h.hno u hu (physF_of_ut hU) with hd | ⟨-, hw2⟩
      · exact absurd hd (not_disj_within hw h.hcr)
      · exact (srB_ut_iff hU _).2 ⟨physF_of_ut h.hut, hw2, hsr⟩
  · intro hs
    rw [hS] at hs
    have hU := srB_to_ut hs
    rw [← hS] at hs
    obtain ⟨-, hw, -⟩ := (srB_ut_iff hU _).1 hs
    refine (srB_ut_iff hU cA).2 ⟨physF_ap q b, ?_, h.hcr⟩
    unfold Within at *; obtain ⟨a1, a2⟩ := h.hcin; omega

theorem orig' (z p : U64) (hz : (insG G src dest true).par z = some p) : revOf mem' p = true := by
  change Function.update G.par dest (if true then some src else G.par src) z = some p at hz
  by_cases hzd : z = dest
  · subst hzd
    rw [Function.update_self] at hz
    have hp : p = src := by simpa using hz.symm
    rw [hp, h.rz h.hsrc]; exact h.hI.utrev src h.hsrc h.hut
  · rw [Function.update_of_ne hzd] at hz
    rw [h.rz (h.hM.tree.par_mem _ _ hz).2]; exact h.hI.orig _ _ hz

theorem desc' (x y : U64) (hd : Mdb.Desc (insG G src dest true).par y x) : isPM mem' x y = true := by
  rcases (h.desc y x).1 hd with hd | ⟨hy, hx⟩
  · obtain ⟨h1, h2⟩ := desc_mem h.hM hd
    rw [h.pm h2 h1]; exact h.hI.desc x y hd
  · rw [hy]
    rcases hx with rfl | hx
    · unfold isPM
      rw [h.rz h.hsrc, h.hI.utrev x h.hsrc h.hut, h.cz h.hsrc, h.cd, h.fd]
      simp [isPF, h.ssrc, isBadged_ut h.hut]
    · have hxm := (desc_mem h.hM hx).2
      have h0 := h.hI.desc x src hx
      unfold isPM at h0 ⊢
      rw [h.rz hxm, h.cz hxm, h.cd, h.fd]
      unfold isPF at h0 ⊢
      simp only [Bool.and_eq_true] at h0 ⊢
      obtain ⟨⟨h1, h2⟩, -⟩ := h0
      obtain ⟨q', sz, f, d, hS⟩ := h.srcUt
      have hX : isUt (capV mem x) = true := by rw [hS] at h2; exact srB_to_ut h2
      refine ⟨⟨h1, by rw [h.k2 hxm]; exact h2⟩, ?_⟩
      simp [isBadged_ut hX]

theorem after' (y : U64) (hy : y ∈ (insG G src dest true).chains.flatten) (hn : nextOf mem' y ≠ 0#u64) (x : U64)
    (hx : x = y ∨ Mdb.Desc (insG G src dest true).par y x)
    (hnd : ¬ Mdb.Desc (insG G src dest true).par (nextOf mem' y) x) : isPM mem' x (nextOf mem' y) = false := by
  rcases (h.memI y).1 hy with hyd | hy
  · rw [hyd] at hn hnd hx ⊢
    rw [h.nd] at hn hnd ⊢
    obtain ⟨hN, -⟩ := h.nm hn
    rcases hx with hxd | hx
    · subst hxd
      unfold isPM
      rw [h.rd]
      simp [isPF]
    · have hx' : x = src ∨ Mdb.Desc G.par src x := by
        rcases (h.desc dest x).1 hx with e | ⟨-, e⟩
        · exact absurd e (h.dest_no_desc x)
        · exact e
      have hnd' : ¬ Mdb.Desc G.par (nextOf mem src) x := fun e => hnd ((h.desc _ x).2 (Or.inl e))
      have hxm : x ∈ G.chains.flatten := by
        rcases hx' with e | e
        · rw [e]; exact h.hsrc
        · exact (desc_mem h.hM e).2
      rw [h.pm hxm hN]
      exact h.hI.after src h.hsrc hn x hx' hnd'
  · by_cases hys : y = src
    · rw [hys] at hn hnd hx hy ⊢
      rw [h.ns] at hn hnd ⊢
      exfalso
      rcases hx with hxy | hx
      · rw [hxy] at hnd; exact hnd ((h.desc dest src).2 (Or.inr ⟨rfl, Or.inl rfl⟩))
      · have hx' : Mdb.Desc G.par src x := ((h.desc src x).1 hx).resolve_right (fun e => h.sd e.1)
        exact hnd ((h.desc dest x).2 (Or.inr ⟨rfl, Or.inr hx'⟩))
    · rw [h.nz hy hys] at hn hnd ⊢
      have hw := h.nxm hy hn
      have hx' : x = y ∨ Mdb.Desc G.par y x := by
        rcases hx with e | e
        · exact Or.inl e
        · exact Or.inr (((h.desc y x).1 e).resolve_right (fun e => h.dne hy e.1))
      have hnd' : ¬ Mdb.Desc G.par (nextOf mem y) x := fun e => hnd ((h.desc _ x).2 (Or.inl e))
      have hxm : x ∈ G.chains.flatten := by
        rcases hx' with e | e
        · rw [e]; exact hy
        · exact (desc_mem h.hM e).2
      rw [h.pm hxm hw]
      exact h.hI.after y hy hn x hx' hnd'

theorem chunk' (ch' : List U64) (hch' : ch' ∈ (insG G src dest true).chains) : Mdb.ChunkL (srF mem') ch' := by
  obtain ⟨ch, hch, rfl⟩ := List.mem_map.1 hch'
  have hchm : ∀ z, z ∈ ch → z ∈ G.chains.flatten := fun z hz => List.mem_flatten.2 ⟨_, hch, hz⟩
  have hsf : ∀ u ∈ G.chains.flatten, ∀ v ∈ G.chains.flatten, srF mem' u v = srF mem u v :=
    fun u hu v hv => srF_congr (h.sm hu hv) (by rw [h.cz hu]) (h.rz hu)
  by_cases hsc : src ∈ ch
  · obtain ⟨A, B, rfl⟩ := List.append_of_mem hsc
    have hnd0 : (A ++ src :: B).Nodup := (List.nodup_flatten.1 h.hM.tree.nodup).1 _ hch
    rw [Mdb.insAfter_split (Mdb.nodup_mid hnd0).1]
    have hcd : ∀ v, srF mem' dest v = srB cA (capV mem' v) := fun v => by
      rw [srF_nf (by rw [h.cd]; rfl)]; unfold srM; rw [h.cd]
    refine Mdb.chunkL_ins2 (h.hI.chunk _ hch) (fun u hu v hv => hsf u (hchm u hu) v (hchm v hv))
      (fun u hu => ?_) ?_ ?_
    · unfold srF srM; rw [h.cd, h.cz (hchm u hu), h.rz (hchm u hu), h.k2 (hchm u hu)]
    · apply Mdb.ca_false
      intro w hw
      rw [hcd, h.cz (hchm w (by simp [hw]))]
      cases e : srB cA (capV mem w)
      · rfl
      · exact (h.k1 (hchm w (by simp [hw])) e).elim
    · apply srF_of_srM; unfold srM; rw [h.cz h.hsrc, h.cd]; exact h.ssrc
  · rw [Mdb.insAfter_of_not_mem hsc]
    exact Mdb.chunkL_congr (h.hI.chunk _ hch) (fun u hu v hv => hsf u (hchm u hu) v (hchm v hv))

theorem badges' (y : U64) (hy : y ∈ (insG G src dest true).chains.flatten) (hn : nextOf mem' y ≠ 0#u64)
    (hbg : isBadged (capV mem' y) = true) (hsr : srM mem' y (nextOf mem' y) = true)
    (hbne : badgeF (capV mem' y) ≠ badgeF (capV mem' (nextOf mem' y)))
    (hb0 : badgeF (capV mem' (nextOf mem' y)) ≠ 0#u64) : fbOf mem' (nextOf mem' y) = true := by
  rcases (h.memI y).1 hy with hyd | hy
  · exfalso
    rw [hyd, h.cd] at hbg; cases hbg
  · by_cases hys : y = src
    · exfalso; rw [hys, h.cz h.hsrc, isBadged_ut h.hut] at hbg; cases hbg
    · rw [h.nz hy hys] at hn hsr hbne hb0 ⊢
      have hw := h.nxm hy hn
      rw [h.fz hw]
      rw [h.cz hy, h.cz hw] at hbne
      rw [h.cz hw] at hb0
      rw [h.cz hy] at hbg
      exact h.hI.badges y hy hn hbg (by rw [← h.sm hy hw]; exact hsr) hbne hb0

theorem utrev' (x : U64) (hx : x ∈ (insG G src dest true).chains.flatten) (hu : isUt (capV mem' x) = true) :
    revOf mem' x = true := by
  rcases (h.memI x).1 hx with hxd | hx
  · rw [hxd, h.cd] at hu; cases hu
  · rw [h.rz hx]; rw [h.cz hx] at hu; exact h.hI.utrev x hx hu

theorem self' (x : U64) (hx : x ∈ (insG G src dest true).chains.flatten) (hz : isZb (capV mem' x) = false) :
    srM mem' x x = true := by
  rcases (h.memI x).1 hx with hxd | hx
  · rw [hxd]; unfold srM; rw [h.cd]; exact srB_ap_self q b
  · rw [h.cz hx] at hz
    rw [h.sm hx hx]; exact h.hI.self x hx hz

/-- **`MdbInv` after inserting the ASID-pool cap.** -/
theorem inv : MdbInv mem' (insG G src dest true) :=
  ⟨h.orig', h.desc', h.after', h.chunk', h.badges', h.utrev', h.self'⟩

end InsACtx

end

end


/-! ## The untyped invariant -/

section
variable {th : TypedHeap} {mem memf : U64 → U64} {G : MdbGhost}

/-- **`UtInv` after inserting a cap of the untyped cap's range as its only
child**, the untyped cap full (`MakePool`: the pool's frame is the whole
untyped region, whose free index is set to its size). -/
theorem utinv_pool (hM : MdbLinks th mem G) (hU : UtInv mem G) {x val p sb f : U64} {d : Bool}
    (hx : x ∈ G.chains.flatten) (hcx : capV mem x = .Untyped p sb f d) (hf : f.val = 2 ^ sb.val)
    (hnd : ∀ y, ¬ Mdb.Desc G.par y x) (hval : val ∉ G.chains.flatten) {q b : U64}
    (hcf : capV memf val = .AsidPool q b)
    (hbA : baseF (.AsidPool q b) = baseF (capV mem x)) (htA : topF (.AsidPool q b) = topF (capV mem x))
    (hco : ∀ y ∈ G.chains.flatten, capV memf y = capV mem y) :
    UtInv memf (insG G x val true) := by
  have hxv : x ≠ val := fun e => hval (e ▸ hx)
  have memI : ∀ z, z ∈ (insG G x val true).chains.flatten ↔ z = val ∨ z ∈ G.chains.flatten :=
    fun z => mem_flatten_ins hx
  have desc : ∀ y z, Mdb.Desc (insG G x val true).par y z ↔
      Mdb.Desc G.par y z ∨ (y = val ∧ (z = x ∨ Mdb.Desc G.par x z)) :=
    fun y z => desc_insG_true hM hval hxv y z
  have hp0 : physF (capV mem x) = true := by rw [hcx]; exact physF_ut _ _ _ _
  have hr0 := hU.reg x hx hp0
  have hpA : physF (capV memf val) = true := by rw [hcf]; exact physF_ap q b
  -- the caps of the new tree's slots: the old ones, or the pool cap
  have hcapU : ∀ u ∈ (insG G x val true).chains.flatten, ∀ pu su fu du, capV memf u = .Untyped pu su fu du →
      u ∈ G.chains.flatten ∧ u ≠ val ∧ capV mem u = .Untyped pu su fu du := by
    intro u hu pu su fu du hcu
    rcases (memI u).1 hu with rfl | hu
    · rw [hcf] at hcu; cases hcu
    · exact ⟨hu, fun e => hval (e ▸ hu), by rw [← hco u hu]; exact hcu⟩
  -- an untyped cap other than `x` meeting `x` is an ancestor of `x`
  have hanc : ∀ u ∈ G.chains.flatten, ∀ pu su fu du, capV mem u = .Untyped pu su fu du → u ≠ x →
      ¬ Disj (capV mem x) (capV mem u) → Mdb.Desc G.par x u := by
    intro u hu pu su fu du hcu hux hdj
    rcases hU.drange u hu pu su fu du hcu x hx (Ne.symm hux) hp0 hdj with h | h
    · exact h
    · exact absurd h (hnd u)
  refine ⟨fun z hz hp => ?_, fun u hu pu su fu du hcu y hy => ?_, fun u hu pu su fu du hcu y hy hp => ?_,
    fun u hu y hy huy pu su fu fu' du du' hcu hcy => ?_, fun u hu pu su fu du hcu => ?_,
    fun u hu pu su fu du hcu y hy hyu hp hdj => ?_⟩
  · -- reg
    rcases (memI z).1 hz with rfl | hz
    · rw [hcf, hbA, htA]; exact hr0
    · rw [hco z hz] at hp ⊢; exact hU.reg z hz hp
  · -- inc
    obtain ⟨huG, -, hcu'⟩ := hcapU u hu pu su fu du hcu
    rcases (desc y u).1 hy with hy | ⟨rfl, hux⟩
    · rw [hco y (desc_mem hM hy).1]; exact hU.inc u huG pu su fu du hcu' y hy
    · rw [hcf, hbA, htA]
      rcases hux with rfl | hux
      · rw [hcx] at hcu'
        cases hcu'
        obtain ⟨e1, e2, -⟩ := ut_range (capV_ut_sb hcx) (by rw [hcx] at hr0; exact hr0)
        rw [hcx, e1, e2]
        refine ⟨physF_ap q b, le_refl _, ?_⟩
        have := Nat.one_le_two_pow (n := sb.val); omega
      · obtain ⟨-, h2, h3⟩ := hU.inc u huG pu su fu du hcu' x hux
        exact ⟨physF_ap q b, h2, h3⟩
  · -- noov
    obtain ⟨huG, -, hcu'⟩ := hcapU u hu pu su fu du hcu
    rw [hco u huG]
    rcases (memI y).1 hy with rfl | hy
    · left
      rw [hcf]
      unfold DisjR
      by_cases hux : u = x
      · subst hux
        rw [hcx] at hcu'; cases hcu'
        obtain ⟨-, e2, -⟩ := ut_range (capV_ut_sb hcx) (by rw [hcx] at hr0; exact hr0)
        rw [htA, hcx, e2, hf]; have := Nat.one_le_two_pow (n := sb.val); omega
      · rcases hU.noov u huG pu su fu du hcu' x hx hp0 with h | ⟨-, hw⟩
        · unfold DisjR at h; rw [htA, hbA]; exact h
        · -- `u` inside `x`: an ancestor of `x`, so full
          have hpu : physF (capV mem u) = true := by rw [hcu']; exact physF_ut _ _ _ _
          have hru := hU.reg u huG hpu
          rw [hcu'] at hru
          obtain ⟨u1, u2, -⟩ := ut_range (capV_ut_sb hcu') hru
          have hdj : ¬ Disj (capV mem x) (capV mem u) := by
            unfold Disj; unfold Within at hw; rw [hcu', u1, u2] at hw ⊢
            have := Nat.one_le_two_pow (n := su.val); omega
          obtain ⟨-, -, h3⟩ := hU.inc u huG pu su fu du hcu' x (hanc u huG pu su fu du hcu' hux hdj)
          have hfu := hU.fib u huG pu su fu du hcu'
          unfold Within at hw; rw [hcu', u1, u2] at hw
          rw [htA]; omega
    · rw [hco y hy] at hp ⊢; exact hU.noov u huG pu su fu du hcu' y hy hp
  · -- excl
    obtain ⟨hu', -, hcu'⟩ := hcapU u hu pu su fu du hcu
    obtain ⟨hy', -, hcy'⟩ := hcapU y hy pu su fu' du' hcy
    exact hU.excl u hu' y hy' huy pu su fu fu' du du' hcu' hcy'
  · -- fib
    obtain ⟨hu', -, hcu'⟩ := hcapU u hu pu su fu du hcu
    exact hU.fib u hu' pu su fu du hcu'
  · -- drange
    obtain ⟨hu', huv, hcu'⟩ := hcapU u hu pu su fu du hcu
    rw [hco u hu'] at hdj
    rcases (memI y).1 hy with rfl | hy'
    · left
      by_cases hux : u = x
      · subst hux; exact (desc _ _).2 (Or.inr ⟨rfl, Or.inl rfl⟩)
      · have hdj' : ¬ Disj (capV mem x) (capV mem u) := by
          rw [hcf] at hdj; unfold Disj at hdj ⊢; rw [← hbA, ← htA]; exact hdj
        exact (desc _ _).2 (Or.inr ⟨rfl, Or.inr (hanc u hu' pu su fu du hcu' hux hdj')⟩)
    · rw [hco y hy'] at hp hdj
      rcases hU.drange u hu' pu su fu du hcu' y hy' hyu hp hdj with h | h
      · exact Or.inl ((desc _ _).2 (Or.inl h))
      · exact Or.inr ((desc _ _).2 (Or.inl h))

end

end Fl4Proofs.P3.Vs
