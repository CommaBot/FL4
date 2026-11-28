/-
P1 (aarch64, gen 43): **`UnmZ` along `ept::map_table` and ASIDPool `Assign`**, with the two facts gen 42 left
missing stated as the case fact `UnmU` (*an unmapped cap is its object's only cap*, *the unmapped objects are
pairwise disjoint and disjoint from the pools*), kept along every step `UnmZ` is kept along — toward discharging
gen 41's [J] `SlotTyEntE` (QueueS2Inv) step by step.

* **`UnmC st x p n s`**: slot `x` holds an unmapped `PageTable` cap of `p` (`n = 4096`) or an unmapped level-0 `Ept`
  cap of `p` (`n = 8192`) — exactly the caps `UnmZ` (QueueS2Map) speaks of. **`NmC st x p s`**: slot `x` holds a
  `PageTable` or `Ept` cap (any flag, level, ASID) naming `p`. **`VsC st x p n s`**: a `PageTable` (`n = 4096`) or
  level-0 `Ept` (`n = 8192`) cap of `p`, mapped or not.
* **[case fact] `UnmU st OS Pp s`** (a definition, not a premise):
  * `one`: an unmapped cap in an `OS` slot is the only `PageTable` / `Ept` cap in `OS` naming its object;
  * `dis`: two `VsC` caps naming different objects name disjoint objects (no common word) — the `Pt` objects the
    caps of `OS` name are pairwise disjoint;
  * `pool`: no word of a `VsC` cap's object is a pool word (`PtW Pp`).

  Source: a `PageTable` / `ArmStage2VSpace` object is made by `create_new_objects` (objects.rs:528; arch
  objects.rs:26/48/55) from a reset / `clear_free`d untyped region with exactly **one** (unmapped) cap, and the
  objects of all retypes are disjoint (untyped carving; an untyped is reset only without children); `ASID_POOL`
  objects are such objects too (MakePool, vspace.rs:1210–1228), so they are disjoint from the others. An unmapped
  cap is never copied: `derive_cap` (objects.rs:207–231) refuses unmapped `PageTable` / `Ept` caps, so Copy / Mint
  cannot duplicate it; Move / Mutate / Swap move it. A cap becomes unmapped again only through ARMPageTableUnmap
  (vspace.rs:1097–1107), which first requires `is_final_capability` (no other cap to the object), and a mapped
  level-0 `Ept` cap is never unmapped (only finalised). Hence an unmapped cap has no sibling naming its object.

* **Preservation (pure)**: `UnmC.congr`, `NmC.congr`, `UnmC.nm`, `UnmZ.words` (an unmapped cap's object words: `VsR`,
  no `Te` word, zero), `ptwb_insert`, **`UnmZ.step`** — one cap slot `x0` changes to a cap that is not an
  unmapped one and names at most the object `x0` named before; every `VsR` word outside a write set `W` kept (`W`
  avoiding the unmapped objects' words); `Te` grows at most by `x0`'s old object: then `UnmZ` over the new `Te` and
  `UnmU` hold after. `UnmU.keepC` (caps of `OS` unchanged).
* **Store steps**: `stt_capk` (`set_thread_state`'s two words are no `OS` slot word, so every `OS` cap kept),
  `wr2_cap` (`set_cap`'s two writes: `VsR` words and the other slots kept, the slot reads the decoded words),
  `wrv_cap` (a write of a `VsR` word keeps the `OS` caps), `capk_vsr` (`VsR`-only writes keep the `OS` caps);
  the cap round trip of the two mapped caps written (only pointer and flag are needed, so no ASID / address bound):
  `CapRt.dec_pt_mapped`, `CapRt.dec_ept_mapped`, `canon_pt`, `canon_ept` (a decoded cap's pointer is canonical),
  `set_cap_pt`, `set_cap_ept`.
* **Steps**: **`ept.map_table.unmz`** (ept.rs:174–197: the slot's unmapped `PageTable` cap of `pt` becomes mapped,
  the descriptor goes into a `Te` word; post `UnmZ` over `insert pt Te` and `UnmU`), **`vspace.decode.assign_s2.unmz`**
  (vspace.rs:1229–1261: the extra slot's unmapped level-0 `Ept` cap of `r0` becomes mapped, the pool word is written;
  `UnmZ` over `insert r0 Te`, `UnmU`), the unmap walks **`ept.unmap.unmu`**, **`ept.unmap_table.unmu`**,
  **`vspace.unmap_page_table.unmu`**, **`vspace.unmap_page.unmu`** (`VsR`-only writes, `UnmU.wr0`).
* **Decode level**: **`vspace.decode_page_table.unmap_ty`** (vspace.rs:1094–1107, ARMPageTableUnmap: restart,
  `unmap_page_table`, `zero(ptr, 4096)`, the cap write; `VsTy ∧ S2Ty` and `ks` kept over the **same** ghost sets);
  `root_map_ok`, **`ept.root.ty`** (ept.rs:153–164: the root is a `Te` root at depth `s2lv n − 1`),
  **`vspace.decode_page_table.map_s2`** (vspace.rs:1108–1135, ARMPageTableMap with an `Ept` cap in the extra slot:
  `VsTy`, `S2Ty` over `insert ptr Te`, `UnmZ` over `insert ptr Te`, `UnmU`, `ks`).
* **`S2Ty.drop`** (pure): `S2Ty` over `Te \ D` when no pool tag-1 entry and no remaining table's descriptor names a
  `D` table.

**Finding (goal "the unmapped table leaves `Te`")**: "each `Te` table has one parent descriptor" does **not** suffice.
ARMPageTableUnmap clears only the slot that `unmap_page_table` finds from the cap's recorded `(asid, vaddr)`; after
the Stage-2 VSpace was deleted (`ept::finalise` → `delete_asid` clears the pool entry, ept.rs:167–171) the walk finds
nothing, while the dead VSpace's tables (still in a ghost `Te` that the deletion keeps, gen 41's `cdt.delete.zqET`)
keep their descriptor to the table. So `S2Ty` over `Te \ {ptr}` fails for such a `Te`; what holds is `S2Ty` over the
tables **reachable** from live tag-1 pool entries. The owed fact is therefore "`Te` = the tables reachable from the
pool entries" (with `S2Ty.drop` for the dead subtrees at deletion and the unmapped table here), plus, for `UnmU.one`
after the cap becomes unmapped, that `is_final_capability` (cdt.rs:158–175: same-object test against the two MDB
neighbours only) implies no other `OS` slot names the object — the MDB same-object adjacency of the reachable states.
Over the same `Te` the step does keep `VsTy ∧ S2Ty` (`unmap_ty`), but not `UnmZ` (the table stays in `Te`).

**Which part of [J] `SlotTyEntE` each covered step preserves** (with QueueS2Map): `ept::map_table` and Stage-2
`Assign`: `VsTy`, `S2Ty` (over the extended `Te`), `ks` (QueueS2Map) and now the case facts `UnmZ` (over the
extended `Te`) and `UnmU`; the unmap walks: `VsTy ∧ S2Ty` (gen 41), `UnmZ` (gen 42), `UnmU`. `Gran`, `S2OK`, `HrOK`
stay state-free case hypotheses over the extended `Te`. Still not covered by any of these steps: the slot-typing /
VCPU / apartness fields of `SlotTyEntP` along the cap writes.

**Still owed** (for discharging `SlotTyEntE` from the steps):
* `UnmZ` / `UnmU` after ARMPageTableUnmap: needs `Te` tied to reachability from the pool entries and the MDB
  same-object adjacency (finding above); `UnmZ` / `UnmU` along `ept::map_frame` / `install_s2_leaf`;
* ARMPageTableMap into Stage-1 / `HighVSpace` VSpaces at decode level (`decode_page_table`'s other two branches) and
  the frame decode (`vspace.decode_frame` → `ept::map_frame`);
* ASIDPool `Assign` of Stage-1 / `HighVSpace` roots; Stage-1 `decode_page_map` / table map / `map_high_page_table`;
* ASIDControl `MakePool`, `create_new_objects` / untyped reset (establishing `UnmZ` / `UnmU`);
* `S2Pl`, `UnmZ`, `UnmU` and `hPA` as fields of the entry fact (they are case hypotheses here).

No named premise is new: [P] `ArchPlat.s2_ipa_bits_const` (QueueS2Ty) is consumed via `hPl` (map_table's walk);
`UnmU`, `UnmZ` are case facts (definitions).
-/
import Fl4ProofsA64.P1.QueueS2Map
import Fl4ProofsA64.P1.QueueCapRt
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1.CapRt

/-- A mapped `PageTable` cap decodes back to a mapped `PageTable` cap of the same object (pointer and flag; the
ASID and address need not fit). -/
theorem dec_pt_mapped (p asid va : U64) (hp : Canonical p) :
    ∃ a' v', decodeF (encodeF (.PageTable p true asid va)).1 (encodeF (.PageTable p true asid va)).2 =
      .PageTable p true a' v' := by
  have htag := tag_gen (w := (encodeF (.PageTable p true asid va)).1) (k := 14) (by bvext) (by decide)
  have hun := unpack_gen (encodeF (.PageTable p true asid va)).1 p hp (by
    intro j hj hj'; simp only [encodeF, BitVec.getElem_or, tagF, packF, getElem_bF, BitVec.getElem_and, BitVec.getElem_shiftLeft, asidHiF]
    interval_cases j <;> simp)
  have hm : (encodeF (.PageTable p true asid va)).1.getLsbD 48 = true := by
    simp only [encodeF]; fields
  simp only [decodeF, htag, hun, hm]
  exact ⟨_, _, rfl⟩

/-- A mapped `Ept` cap decodes back to a mapped `Ept` cap of the same object and level. -/
theorem dec_ept_mapped (p level asid va : U64) (hp : Canonical p) (hl : level.val < 64) :
    ∃ a' v', decodeF (encodeF (.Ept p level true asid va)).1 (encodeF (.Ept p level true asid va)).2 =
      .Ept p level true a' v' := by
  have h1 := hb (k := 6) hl
  have htag := tag_gen (w := (encodeF (.Ept p level true asid va)).1) (k := 23) (by bvext) (by decide)
  have hun := unpack_gen (encodeF (.Ept p level true asid va)).1 p hp (by
    intro j hj hj'; simp only [encodeF, BitVec.getElem_or, tagF, packF, getElem_bF, BitVec.getElem_and, BitVec.getElem_shiftLeft, asidHiF, M48]
    interval_cases j <;> simp)
  have hm : (encodeF (.Ept p level true asid va)).1.getLsbD 48 = true := by
    simp only [encodeF]; fields
  have hlv : (⟨((encodeF (.Ept p level true asid va)).1 >>> 53) &&& 63#64⟩ : U64) = level := by
    simp only [encodeF]; fields
  simp only [decodeF, htag, hun, hm]
  exact ⟨_, _, by rw [hlv]⟩

end Fl4ProofsA64.P1.CapRt

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

/-! ## The unmapped caps and the case fact `UnmU` -/

/-- Slot `x` holds an unmapped `PageTable` cap of `p` (`n = 4096`) or an unmapped level-0 `Ept` cap of `p`
(`n = 8192`). -/
def UnmC (st : machine.Store S) (x p : U64) (n : Nat) (s : S) : Prop :=
  (n = 4096 ∧ ∃ asid v, obj.Slot.cap st x s = ok (.PageTable p false asid v)) ∨
    (n = 8192 ∧ ∃ asid v, obj.Slot.cap st x s = ok (.Ept p 0#u64 false asid v))

/-- Slot `x` holds a `PageTable` or `Ept` cap naming `p`. -/
def NmC (st : machine.Store S) (x p : U64) (s : S) : Prop :=
  (∃ m asid v, obj.Slot.cap st x s = ok (.PageTable p m asid v)) ∨
    (∃ l m asid v, obj.Slot.cap st x s = ok (.Ept p l m asid v))

/-- Slot `x` holds a `PageTable` cap of `p` (`n = 4096`) or a level-0 `Ept` cap of `p` (`n = 8192`), mapped or not:
the 4 KiB / 8 KiB VSpace objects the caps of `OS` name. -/
def VsC (st : machine.Store S) (x p : U64) (n : Nat) (s : S) : Prop :=
  (n = 4096 ∧ ∃ m asid v, obj.Slot.cap st x s = ok (.PageTable p m asid v)) ∨
    (n = 8192 ∧ ∃ m asid v, obj.Slot.cap st x s = ok (.Ept p 0#u64 m asid v))

/-- **[case fact] The unmapped caps' objects** (module docstring for the source): an unmapped cap is the only
`PageTable` / `Ept` cap naming its object; the `PageTable` / level-0 `Ept` caps of different objects name disjoint
objects; their words are no pool words. -/
structure UnmU (st : machine.Store S) (OS Pp : Set U64) (s : S) : Prop where
  one : ∀ x ∈ OS, ∀ y ∈ OS, ∀ p n, UnmC st x p n s → NmC st y p s → y = x
  dis : ∀ x ∈ OS, ∀ y ∈ OS, ∀ p q n m, VsC st x p n s → VsC st y q m s → p ≠ q →
    ∀ o o' : U64, o.val < n → o.val % 8 = 0 → o'.val < m → o'.val % 8 = 0 → wa p o ≠ wa q o'
  pool : ∀ x ∈ OS, ∀ p n, VsC st x p n s → ∀ o : U64, o.val < n → o.val % 8 = 0 → ¬ PtW Pp (wa p o)

section unmu
variable {OS Vc Ub : Set U64} {kb : U64} {Pp Tb Pt Hr Te : Set U64} {Lv Re bits : U64 → Nat}

theorem UnmC.congr {x p : U64} {n : Nat} {s s' : S} (e : obj.Slot.cap st x s' = obj.Slot.cap st x s) :
    UnmC st x p n s' ↔ UnmC st x p n s := by
  unfold UnmC; rw [e]

theorem NmC.congr {x p : U64} {s s' : S} (e : obj.Slot.cap st x s' = obj.Slot.cap st x s) :
    NmC st x p s' ↔ NmC st x p s := by
  unfold NmC; rw [e]

theorem VsC.congr {x p : U64} {n : Nat} {s s' : S} (e : obj.Slot.cap st x s' = obj.Slot.cap st x s) :
    VsC st x p n s' ↔ VsC st x p n s := by
  unfold VsC; rw [e]

theorem UnmC.vs {x p : U64} {n : Nat} {s : S} (h : UnmC st x p n s) : VsC st x p n s := by
  rcases h with ⟨hn, a, v, e⟩ | ⟨hn, a, v, e⟩
  · exact Or.inl ⟨hn, false, a, v, e⟩
  · exact Or.inr ⟨hn, false, a, v, e⟩

theorem UnmC.nm {x p : U64} {n : Nat} {s : S} (h : UnmC st x p n s) : NmC st x p s := by
  rcases h with ⟨-, a, v, e⟩ | ⟨-, a, v, e⟩
  · exact Or.inl ⟨false, a, v, e⟩
  · exact Or.inr ⟨0#u64, false, a, v, e⟩

/-- An unmapped cap's object words: `VsR` words, no `Te` word, zero (from `UnmZ`). -/
theorem UnmZ.words {s : S} (hU : UnmZ st OS Pt Te bits s) {x p : U64} {n : Nat} (hx : x ∈ OS)
    (h : UnmC st x p n s) {o : U64} (ho : o.val < n) (h8 : o.val % 8 = 0) :
    VsR kb Pt (wa p o) ∧ ¬ PtWb Te bits (wa p o) ∧ L.mem s (wa p o) = 0#u64 := by
  rcases h with ⟨rfl, asid, v, e⟩ | ⟨rfl, asid, v, e⟩
  · obtain ⟨hp, hf⟩ := hU.pt x hx p asid v e
    exact ⟨Or.inl ⟨p, hp, o, ho, h8, rfl⟩, hf o ho h8⟩
  · obtain ⟨hp, hf⟩ := hU.ept x hx p asid v e
    exact ⟨Or.inl (ptw_mono hp (ptwb_gran (bits := fun _ => 13) (fun _ _ => Or.inr rfl)
      ⟨p, Set.mem_singleton p, o, lt_of_lt_of_eq ho (by norm_num), h8, rfl⟩)), hf o ho h8⟩

theorem ptwb_insert {q b : U64} (hb : PtWb (insert q Te) bits b) :
    PtWb Te bits b ∨ ∃ o : U64, o.val < 2 ^ bits q ∧ o.val % 8 = 0 ∧ b = wa q o := by
  obtain ⟨p, hp, o, ho, h8, e⟩ := hb
  rcases hp with hpq | hp
  · subst hpq; exact Or.inr ⟨o, ho, h8, e⟩
  · exact Or.inl ⟨p, hp, o, ho, h8, e⟩

/-- **`UnmZ` and `UnmU` along a step changing one cap slot `x0`** (module docstring). -/
theorem UnmZ.step {W : U64 → Prop} {Te' : Set U64} {s s' : S} {x0 : U64} (hx0 : x0 ∈ OS)
    (hU : UnmZ st OS Pt Te bits s) (hV : UnmU st OS Pp s)
    (hc : ∀ x ∈ OS, x ≠ x0 → obj.Slot.cap st x s' = obj.Slot.cap st x s)
    (h0 : ∀ p n, ¬ UnmC st x0 p n s') (hn0 : ∀ p, NmC st x0 p s' → NmC st x0 p s)
    (hv0 : ∀ p n, VsC st x0 p n s' → VsC st x0 p n s)
    (hm : ∀ b, VsR kb Pt b → ¬ W b → L.mem s' b = L.mem s b)
    (hW : ∀ x ∈ OS, ∀ p n, UnmC st x p n s → ∀ o : U64, o.val < n → o.val % 8 = 0 → ¬ W (wa p o))
    (hT : ∀ b, PtWb Te' bits b → PtWb Te bits b ∨
      ∃ q n, UnmC st x0 q n s ∧ ∃ o : U64, o.val < n ∧ o.val % 8 = 0 ∧ b = wa q o) :
    UnmZ st OS Pt Te' bits s' ∧ UnmU st OS Pp s' := by
  have tr : ∀ x ∈ OS, ∀ p n, UnmC st x p n s' → x ≠ x0 ∧ UnmC st x p n s := fun x hx p n h => by
    have hne : x ≠ x0 := fun e => h0 p n (by subst e; exact h)
    exact ⟨hne, (UnmC.congr (hc x hx hne)).1 h⟩
  have trv : ∀ x ∈ OS, ∀ p n, VsC st x p n s' → VsC st x p n s := fun x hx p n h => by
    by_cases hx0' : x = x0
    · subst hx0'; exact hv0 p n h
    · exact (VsC.congr (hc x hx hx0')).1 h
  have key : ∀ x ∈ OS, ∀ p n, UnmC st x p n s' → ∀ o : U64, o.val < n → o.val % 8 = 0 →
      ¬ PtWb Te' bits (wa p o) ∧ L.mem s' (wa p o) = 0#u64 := by
    intro x hx p n h o ho h8
    obtain ⟨hne, hu⟩ := tr x hx p n h
    obtain ⟨hv, hn, hz⟩ := UnmZ.words (kb := kb) hU hx hu ho h8
    refine ⟨fun hb => ?_, by rw [hm _ hv (hW x hx p n hu o ho h8)]; exact hz⟩
    rcases hT _ hb with hb' | ⟨q', n', hq, o', ho', h8', e⟩
    · exact hn hb'
    · by_cases hpq : p = q'
      · subst hpq
        exact hne (hV.one x hx x0 hx0 p n hu (UnmC.nm hq)).symm
      · exact hV.dis x hx x0 hx0 p q' n n' hu.vs hq.vs hpq o o' ho h8 ho' h8' e
  refine ⟨⟨fun x hx p asid v e => ?_, fun x hx p asid v e => ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · have hu' : UnmC st x p 4096 s' := Or.inl ⟨rfl, asid, v, e⟩
    obtain ⟨hne, -⟩ := tr x hx p 4096 hu'
    exact ⟨(hU.pt x hx p asid v (by rw [← hc x hx hne]; exact e)).1, key x hx p 4096 hu'⟩
  · have hu' : UnmC st x p 8192 s' := Or.inr ⟨rfl, asid, v, e⟩
    obtain ⟨hne, -⟩ := tr x hx p 8192 hu'
    exact ⟨(hU.ept x hx p asid v (by rw [← hc x hx hne]; exact e)).1, key x hx p 8192 hu'⟩
  · intro x hx y hy p n hu hnm
    obtain ⟨-, hu0⟩ := tr x hx p n hu
    have hn : NmC st y p s := by
      by_cases hy0 : y = x0
      · subst hy0; exact hn0 p hnm
      · exact (NmC.congr (hc y hy hy0)).1 hnm
    exact hV.one x hx y hy p n hu0 hn
  · intro x hx y hy p q n m hu hu' hpq
    exact hV.dis x hx y hy p q n m (trv x hx p n hu) (trv y hy q m hu') hpq
  · intro x hx p n hu
    exact hV.pool x hx p n (trv x hx p n hu)

/-- **`UnmU` along a step keeping every `OS` cap.** -/
theorem UnmU.keepC {s s' : S} (hV : UnmU st OS Pp s)
    (hc : ∀ x ∈ OS, obj.Slot.cap st x s' = obj.Slot.cap st x s) : UnmU st OS Pp s' :=
  ⟨fun x hx y hy p n hu hn => hV.one x hx y hy p n ((UnmC.congr (hc x hx)).1 hu) ((NmC.congr (hc y hy)).1 hn),
    fun x hx y hy p q n m hu hu' =>
      hV.dis x hx y hy p q n m ((VsC.congr (hc x hx)).1 hu) ((VsC.congr (hc y hy)).1 hu'),
    fun x hx p n hu => hV.pool x hx p n ((VsC.congr (hc x hx)).1 hu)⟩

/-! ## Store steps and the cap writes -/

/-- `VsR`-only writes keep every `OS` cap. -/
theorem capk_vsr (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) (hO : OSOK T Ω Sg OS) {s s' : S}
    (hw : WritesIn st s s' (VsR kb Pt)) : ∀ x ∈ OS, obj.Slot.cap st x s' = obj.Slot.cap st x s := by
  intro x hx
  obtain ⟨v8, -, -⟩ := vals hO hx
  rw [DPF.slot_cap_dec, DPF.slot_cap_dec,
    hw.mem_eq (hO.al0 hx) fun hb => hR.os _ hb ⟨x, hx, by omega, by omega⟩,
    hw.mem_eq (hO.al hx (k := 8#u64) (by simp) (by simp)) fun hb => hR.os _ hb ⟨x, hx, by omega, by omega⟩]

/-- **`UnmU` along a `Wr0` step of `VsR` words.** -/
theorem UnmU.wr0 (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) (hO : OSOK T Ω Sg OS) {X : Set U64} (hX : X ⊆ Pt)
    {s s' : S} (hV : UnmU st OS Pp s) (z : Wr0 st X s s') : UnmU st OS Pp s' := by
  have z' : Wr0 st Pt s s' := Or.imp id (fun ⟨b, hb, e⟩ => ⟨b, ptw_mono hX hb, e⟩) z
  exact hV.keepC (capk_vsr hR hO ((Wr0.w (fun b hb => hR.al b (Or.inl hb)) z').mono fun _ hb => Or.inl hb))

/-- `set_thread_state`'s two words (the thread's `STATE`, the core's `SCHED_ACTION`) are no `OS` slot word: every
`OS` cap kept. -/
theorem stt_capk (hO : OSOK T Ω Sg OS) {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s s1 : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q Rq) {t : U64} (ht : t ∈ T)
    (w1 : WritesIn st s s1 (fun b => b = stA t ∨ b = L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION)) :
    ∀ x ∈ OS, obj.Slot.cap st x s1 = obj.Slot.cap st x s := by
  have nw : ∀ b, W7.CapW T Ω Sg b → ¬ (b = stA t ∨ b = L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) := by
    rintro b hb (e | e)
    · rcases hb with hl | ⟨hΩ, -⟩
      · exact W7.tlow_ne_field (K := 3328#u64) q.tcbs ht (by simp) (by simp) hl (by rw [e, stA_eq])
      · exact out_ne_field (K := 3328#u64) (q.omega b hΩ) ht (q.tcbs t ht) (by simp) (by rw [← stA_eq, ← e])
    · rcases hb with hl | ⟨hΩ, -⟩
      · exact W7.tlow_ne_node (o := layout.node.SCHED_ACTION) q.tcbs (q.nodes _ q.cur)
          (by simp [layout.node.SCHED_ACTION]) hl e.symm
      · exact out_ne_node (q.omega b hΩ) q.cur (q.nodes _ q.cur) (o := layout.node.SCHED_ACTION)
          (by simp [layout.node.SCHED_ACTION]) (by rw [e])
  intro x hx
  rw [DPF.slot_cap_dec, DPF.slot_cap_dec, w1.mem_eq (hO.al0 hx) (nw _ (hO.cw0 hx)),
    w1.mem_eq (hO.al hx (k := 8#u64) (by simp) (by simp)) (nw _ (hO.cw hx (k := 8#u64) (by simp) (by simp)))]

/-- `set_cap`'s two writes into a slot of `OS`: every `VsR` word and every other `OS` cap kept, the slot reads the
decoded words. -/
theorem wr2_cap (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) (hO : OSOK T Ω Sg OS) {s : S} {x w0 w1 : U64}
    (hx : x ∈ OS) :
    VsKeep st kb Pt s (L.wr (L.wr s x w0) (wa x 8#u64) w1) ∧
      (∀ y ∈ OS, y ≠ x → obj.Slot.cap st y (L.wr (L.wr s x w0) (wa x 8#u64) w1) = obj.Slot.cap st y s) ∧
      obj.Slot.cap st x (L.wr (L.wr s x w0) (wa x 8#u64) w1) = capability.Cap.decode w0 w1 := by
  obtain ⟨v8, -, -⟩ := vals hO hx
  have a0 := hO.al0 hx
  have a8 := hO.al hx (k := 8#u64) (by simp) (by simp)
  refine ⟨fun b hb => ?_, fun y hy hne => ?_, ?_⟩
  · have ab := hR.al b hb
    rw [L.mem_wr_ne a8 ab (fun e => hR.os b hb ⟨x, hx, by omega, by omega⟩),
      L.mem_wr_ne a0 ab (fun e => hR.os b hb ⟨x, hx, by omega, by omega⟩)]
  · obtain ⟨e1, e2, -, -⟩ := other_keep (st := st) (s := L.wr s x w0) (v := w1) hO hx hy hne a8 (by omega)
    obtain ⟨f1, f2, -, -⟩ := other_keep (st := st) (s := s) (v := w0) hO hx hy hne a0 (by omega)
    rw [DPF.slot_cap_dec, DPF.slot_cap_dec, e1, f1, e2, f2]
  · rw [DPF.slot_cap_dec, L.mem_wr_ne a8 a0 (by omega), L.mem_wr_same a0, L.mem_wr_same a8]

/-- A write of a `VsR` word keeps every `OS` cap. -/
theorem wrv_cap (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) (hO : OSOK T Ω Sg OS) {s : S} {b v : U64}
    (hb : VsR kb Pt b) : ∀ x ∈ OS, obj.Slot.cap st x (L.wr s b v) = obj.Slot.cap st x s := by
  intro x hx
  obtain ⟨v8, -, -⟩ := vals hO hx
  have ab := hR.al b hb
  rw [DPF.slot_cap_dec, DPF.slot_cap_dec, L.mem_wr_ne ab (hO.al0 hx) (fun e => hR.os b hb ⟨x, hx, by omega, by omega⟩),
    L.mem_wr_ne ab (hO.al hx (k := 8#u64) (by simp) (by simp)) (fun e => hR.os b hb ⟨x, hx, by omega, by omega⟩)]

/-- A decoded `PageTable` cap's pointer is canonical. -/
theorem canon_pt {s : S} {x p : U64} {m : Bool} {a v : U64}
    (h : obj.Slot.cap st x s = ok (.PageTable p m a v)) : CapRt.Canonical p := by
  rw [DPF.slot_cap_dec, CapRt.decode_eq] at h
  have hw := CapRt.decodeF_encWf (L.mem s x).bv (L.mem s (wa x 8#u64)).bv
  rw [okinj h] at hw
  simp only [CapRt.EncWf] at hw
  exact hw.1

/-- A decoded `Ept` cap's pointer is canonical. -/
theorem canon_ept {s : S} {x p l : U64} {m : Bool} {a v : U64}
    (h : obj.Slot.cap st x s = ok (.Ept p l m a v)) : CapRt.Canonical p := by
  rw [DPF.slot_cap_dec, CapRt.decode_eq] at h
  have hw := CapRt.decodeF_encWf (L.mem s x).bv (L.mem s (wa x 8#u64)).bv
  rw [okinj h] at hw
  simp only [CapRt.EncWf] at hw
  exact hw.1

/-- **`set_cap` of a mapped `PageTable` cap** into a slot of `OS`. -/
theorem set_cap_pt (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) (hO : OSOK T Ω Sg OS) {x p : U64} (hx : x ∈ OS)
    (hp : CapRt.Canonical p) (s : S) (asid va : U64) :
    obj.Slot.set_cap st x s (.PageTable p true asid va) ⦃ s' => VsKeep st kb Pt s s' ∧
      (∀ y ∈ OS, y ≠ x → obj.Slot.cap st y s' = obj.Slot.cap st y s) ∧
      ∃ a' v', obj.Slot.cap st x s' = ok (.PageTable p true a' v') ⦄ := by
  rw [set_cap_eq (CapRt.encode_eq _), WP.spec_ok]
  obtain ⟨k, c2o, c2x⟩ := wr2_cap (st := st) (s := s) hR hO hx
    (w0 := ⟨(CapRt.encodeF (.PageTable p true asid va)).1⟩) (w1 := ⟨(CapRt.encodeF (.PageTable p true asid va)).2⟩)
  obtain ⟨a', v', e⟩ := CapRt.dec_pt_mapped p asid va hp
  refine ⟨k, c2o, a', v', ?_⟩
  rw [c2x, CapRt.decode_eq]
  exact congrArg ok e

/-- **`set_cap` of a mapped `Ept` cap** into a slot of `OS`. -/
theorem set_cap_ept (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) (hO : OSOK T Ω Sg OS) {x p : U64} (hx : x ∈ OS)
    (hp : CapRt.Canonical p) (s : S) (level asid va : U64) (hl : level.val < 64) :
    obj.Slot.set_cap st x s (.Ept p level true asid va) ⦃ s' => VsKeep st kb Pt s s' ∧
      (∀ y ∈ OS, y ≠ x → obj.Slot.cap st y s' = obj.Slot.cap st y s) ∧
      ∃ a' v', obj.Slot.cap st x s' = ok (.Ept p level true a' v') ⦄ := by
  rw [set_cap_eq (CapRt.encode_eq _), WP.spec_ok]
  obtain ⟨k, c2o, c2x⟩ := wr2_cap (st := st) (s := s) hR hO hx
    (w0 := ⟨(CapRt.encodeF (.Ept p level true asid va)).1⟩) (w1 := ⟨(CapRt.encodeF (.Ept p level true asid va)).2⟩)
  obtain ⟨a', v', e⟩ := CapRt.dec_ept_mapped p level asid va hp hl
  refine ⟨k, c2o, a', v', ?_⟩
  rw [c2x, CapRt.decode_eq]
  exact congrArg ok e

end unmu

/-! ## `ept::map_table` and ASIDPool `Assign` -/

section steps
variable {OS Vc Ub : Set U64} {kb : U64} {Pp Tb Pt Hr Te : Set U64} {Lv Re bits : U64 → Nat}
variable {A : Type _} {ar : machine.Arch A}

set_option maxHeartbeats 4000000 in
/-- **`ept::map_table` keeps `UnmZ` (over `insert pt Te`) and `UnmU`** (ept.rs:174–197; module docstring): the
slot's unmapped `PageTable` cap of `pt` becomes mapped, the descriptor is written into a `Te` word. -/
theorem ept.map_table.unmz (hPl : ArchPlat ar) (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) (hO : OSOK T Ω Sg OS)
    {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q Rq) (hTe : Gran Te bits ⊆ Pt) (hS0 : S2OK Te bits Hr)
    (h2 : S2Ty st hPl.ipa Pp Hr Te Re bits s)
    {root : U64} (hr : root ∈ Te) (hre : Re root + 1 = s2lv hPl.ipa) (hrb : s2rb hPl.ipa ≤ bits root)
    (a : A) (asid ipa : U64) {pt asid0 v0 slot : U64} (hsl : slot ∈ OS) (h12 : bits pt = 12)
    (hc : obj.Slot.cap st slot s = ok (.PageTable pt false asid0 v0))
    (hU : UnmZ st OS Pt Te bits s) (hV : UnmU st OS Pp s) :
    ept.map_table st ar s a root asid ipa pt slot ⦃ r => r.2.1 = s ∨
      (UnmZ st OS Pt (insert pt Te) bits r.2.1 ∧ UnmU st OS Pp r.2.1) ⦄ := by
  have hpc := canon_pt hc
  unfold ept.map_table
  rw [hPl.ipa_eq a, bind_ok]
  refine WP.spec_bind (P0.ept.ipa_limit.p0 _) fun _ _ => ?_
  refine spec_ite (fun _ => by mtErr) (fun _ => ?_)
  refine WP.spec_bind (ept.lookup_slot.tyD h2 hS0 hr hre hrb ipa) fun lu hlu => ?_
  obtain ⟨p, hp, o, ho, h8, hsl', -⟩ := hlu
  refine spec_ite (fun _ => by mtErr) (fun _ => ?_)
  refine WP.spec_bind (LawfulStore.read_spec s lu.slot) fun _ _ => ?_
  refine WP.spec_bind P0.ept.D_VALID.p0 fun _ _ => ?_
  try simp only [lift, bind_ok]
  refine spec_ite (fun _ => by mtErr) (fun _ => ?_)
  refine WP.spec_bind (shl_and63u _) fun _ _ => ?_
  try simp only [lift, bind_ok]
  refine WP.spec_bind (sched.cur_thread.spec s) fun ct ect => ?_
  have hct : ct ∈ T := by rw [ect]; exact q.curT
  refine WP.spec_bind (stt_vk hR q hct) fun s1 ⟨w1, k1⟩ => ?_
  have c1 := stt_capk hO q hct w1
  refine WP.spec_bind (set_cap_pt hR hO hsl hpc s1 _ _) fun s2 ⟨k2, c2o, a', v', c2x⟩ => ?_
  refine WP.spec_bind (show layout.paddr pt ⦃ _ => True ⦄ by
    unfold layout.paddr; exact (WP.spec_ok _).2 trivial) fun _ _ => ?_
  refine WP.spec_bind (P0.ept.make_s2_table.p0 _) fun v _ => ?_
  refine WP.spec_bind (LawfulStore.write_spec s2 lu.slot v) fun s3 e3 => ?_
  subst e3
  rw [hsl']
  have hw : PtWb Te bits (wa p o) := ⟨p, hp, o, ho, h8, rfl⟩
  have hv0 : VsR kb Pt (wa p o) := Or.inl (ptw_mono hTe (ptwb_gran hS0.sz hw))
  have c3 := wrv_cap (st := st) (s := s2) (v := v) hR hO hv0
  have cs3 : obj.Slot.cap st slot (L.wr s2 (wa p o) v) = ok (.PageTable pt true a' v') := by
    rw [c3 slot hsl]; exact c2x
  refine (WP.spec_ok _).2 (Or.inr (UnmZ.step (kb := kb) (W := PtWb Te bits) hsl hU hV ?_ ?_ ?_ ?_ ?_ ?_ ?_))
  · intro x hx hne; rw [c3 x hx, c2o x hx hne, c1 x hx]
  · rintro p' n (⟨-, a1, v1, e⟩ | ⟨-, a1, v1, e⟩) <;> rw [cs3] at e <;> cases okinj e
  · rintro p' (⟨m, a1, v1, e⟩ | ⟨l, m, a1, v1, e⟩) <;> rw [cs3] at e
    · cases okinj e; exact Or.inl ⟨false, asid0, v0, hc⟩
    · cases okinj e
  · rintro p' n (⟨rfl, m, a1, v1, e⟩ | ⟨rfl, m, a1, v1, e⟩) <;> rw [cs3] at e
    · cases okinj e; exact Or.inl ⟨rfl, false, asid0, v0, hc⟩
    · cases okinj e
  · intro b hb hn
    have hne : (wa p o).val ≠ b.val := fun e => hn (by rw [← UScalar.eq_of_val_eq e]; exact hw)
    rw [L.mem_wr_ne (hR.al _ hv0) (hR.al b hb) hne, k2 b hb, k1 b hb]
  · intro x hx p' n hu o' ho' h8'
    exact (UnmZ.words (kb := kb) hU hx hu ho' h8').2.1
  · intro b hb
    rcases ptwb_insert hb with h | ⟨o', ho', h8', e⟩
    · exact Or.inl h
    · exact Or.inr ⟨pt, 4096, Or.inl ⟨rfl, asid0, v0, hc⟩, o', lt_of_lt_of_eq ho' (by rw [h12]; norm_num), h8', e⟩

set_option maxHeartbeats 4000000 in
/-- **ASIDPool `Assign` of an unmapped Stage-2 root keeps `UnmZ` (over `insert r0 Te`) and `UnmU`**
(vspace.rs:1229–1261; module docstring): the extra slot's unmapped level-0 `Ept` cap of `r0` becomes mapped, the
pool word is written. -/
theorem vspace.decode.assign_s2.unmz (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) (hO : OSOK T Ω Sg OS)
    {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q Rq) (hk : L.ksb s = kb) (hPp : Pp ⊆ Pt) (hY : VsTy st kb Pp Tb Lv s)
    {r0 a0 v0 : U64} (h13 : bits r0 = 13) (hU : UnmZ st OS Pt Te bits s) (hV : UnmU st OS Pp s)
    (a : A) (len slot pptr abase : U64) (call : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (hx : ∀ x ∈ extra.val, x ≠ 0#u64 → x ∈ OS ∧ obj.Slot.cap st x s = ok (.Ept r0 0#u64 false a0 v0)) :
    vspace.decode st ar s a fl4_abi.label.ARMASIDPoolAssign len slot (.AsidPool pptr abase) call buf extra
      ⦃ r => r.2.1 = s ∨ (UnmZ st OS Pt (insert r0 Te) bits r.2.1 ∧ UnmU st OS Pp r.2.1) ⦄ := by
  have hS' : P0.StoreTotal st := L.total
  unfold vspace.decode
  refine WP.spec_bind (sched.cur_thread.spec s) fun ct ect => ?_
  have hct : ct ∈ T := by rw [ect]; exact q.curT
  try dsimp only
  refine spec_ite (fun _ => by asErr) (fun _ => ?_)
  refine WP.spec_bind (vspace.extra.memA extra 0#usize) fun o ho => ?_
  rcases o with _ | x
  · asErr
  obtain ⟨hxm, hx0⟩ := ho x rfl
  obtain ⟨hxO, hxc⟩ := hx x hxm hx0
  have hpc := canon_ept hxc
  try dsimp only
  rw [hxc, bind_ok]
  try dsimp only
  try split
  all_goals try asErr
  refine spec_ite (fun _ => by asErr) (fun _ => ?_)
  refine WP.spec_bind (Pₘ := fun _ => True) (by p0_auto) fun i _ => ?_
  refine WP.spec_bind (vspace.asid_table.w s i) fun pool ⟨oA, hA1, hA2, hA8, epool⟩ => ?_
  refine spec_ite (fun _ => by asErr) (fun hp0 => ?_)
  refine spec_ite (fun _ => by asErr) (fun _ => ?_)
  refine WP.spec_bind (P0.vspace.decode_loop2.p0 st s _ _ _ hS') fun i2 _ => ?_
  refine spec_ite (fun _ => by asErr) (fun _ => ?_)
  try simp only [lift, bind_ok]
  refine WP.spec_bind (stt_vk hR q hct) fun s1 ⟨w1, k1⟩ => ?_
  have c1 := stt_capk hO q hct w1
  refine WP.spec_bind (Pₘ := fun s2 => VsKeep st kb Pt s1 s2 ∧
      (∀ y ∈ OS, y ≠ x → obj.Slot.cap st y s2 = obj.Slot.cap st y s1) ∧
      ∃ a' v', obj.Slot.cap st x s2 = ok (.Ept r0 0#u64 true a' v')) (by
    repeat' (first
      | exact set_cap_ept hR hO hxO hpc s1 _ _ _ (by decide)
      | (exfalso; first | contradiction | (rename_i h; exact h rfl))
      | split)) fun s2 ⟨k2, c2o, a', v', c2x⟩ => ?_
  try simp only [lift, bind_ok]
  step as ⟨i4, hi4⟩
  try simp only [lift, bind_ok]
  refine WP.spec_bind (LawfulStore.write_spec s2 _ _) fun s3 e3 => ?_
  subst e3
  have hpP : pool ∈ Pp := by
    have := hY.tbl oA hA1 hA2 hA8 (by rw [← hk, ← epool]; exact hp0)
    rwa [← hk, ← epool] at this
  have ho4 : i4.val < 4096 ∧ i4.val % 8 = 0 := by
    obtain ⟨Y, hY4⟩ : ∃ Y : U64, i4.val = (Y &&& 511#u64).val * 8 := ⟨_, hi4⟩
    have hb : (Y &&& 511#u64).val ≤ 511 := by
      rw [UScalar.val_and]; exact le_trans Nat.and_le_right (by simp)
    omega
  have hw : PtW Pp (wa pool i4) := ⟨pool, hpP, i4, ho4.1, ho4.2, rfl⟩
  have hv0 : VsR kb Pt (wa pool i4) := Or.inl (ptw_mono hPp hw)
  have fin : ∀ v : U64, UnmZ st OS Pt (insert r0 Te) bits (L.wr s2 (wa pool i4) v) ∧
      UnmU st OS Pp (L.wr s2 (wa pool i4) v) := fun v => by
    have c3 := wrv_cap (st := st) (s := s2) (v := v) hR hO hv0
    have cs3 : obj.Slot.cap st x (L.wr s2 (wa pool i4) v) = ok (.Ept r0 0#u64 true a' v') := by
      rw [c3 x hxO]; exact c2x
    refine UnmZ.step (kb := kb) (W := PtW Pp) hxO hU hV ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro y hy hne; rw [c3 y hy, c2o y hy hne, c1 y hy]
    · rintro p' n (⟨-, a1, v1, e⟩ | ⟨-, a1, v1, e⟩) <;> rw [cs3] at e <;> cases okinj e
    · rintro p' (⟨m, a1, v1, e⟩ | ⟨l, m, a1, v1, e⟩) <;> rw [cs3] at e
      · cases okinj e
      · cases okinj e; exact Or.inr ⟨0#u64, false, a0, v0, hxc⟩
    · rintro p' n (⟨rfl, m, a1, v1, e⟩ | ⟨rfl, m, a1, v1, e⟩) <;> rw [cs3] at e
      · cases okinj e
      · cases okinj e; exact Or.inr ⟨rfl, false, a0, v0, hxc⟩
    · intro b hb hn
      have hne : (wa pool i4).val ≠ b.val := fun e => hn (by rw [← UScalar.eq_of_val_eq e]; exact hw)
      rw [L.mem_wr_ne (hR.al _ hv0) (hR.al b hb) hne, k2 b hb, k1 b hb]
    · intro y hy p' n hu o' ho' h8'
      exact hV.pool y hy p' n hu.vs o' ho' h8'
    · intro b hb
      rcases ptwb_insert hb with h | ⟨o', ho', h8', e⟩
      · exact Or.inl h
      · exact Or.inr ⟨r0, 8192, Or.inr ⟨rfl, a0, v0, hxc⟩, o', lt_of_lt_of_eq ho' (by rw [h13]; norm_num), h8', e⟩
  exact (WP.spec_ok _).2 (Or.inr (fin _))

end steps

/-! ## The unmap walks keep `UnmU` -/

section walks
variable {OS Vc Ub : Set U64} {kb : U64} {Pp Tb Pt Hr Te : Set U64} {Lv Re bits : U64 → Nat}
variable {A : Type _} {ar : machine.Arch A}

/-- **`ept::unmap` keeps `UnmU`.** -/
theorem ept.unmap.unmu (hA : P0.ArchTotal ar) (hPl : ArchPlat ar) (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt)
    (hO : OSOK T Ω Sg OS) (hS : S2OK Te bits Hr) (hTe : Gran Te bits ⊆ Pt) {s : S}
    (hY : VsTy st kb Pp Tb Lv s ∧ S2Ty st hPl.ipa Pp Hr Te Re bits s) (hk : L.ksb s = kb)
    (hV : UnmU st OS Pp s) (a : A) (asid ipa ptr shift : U64) (it : Bool) :
    ept.unmap st ar s a asid ipa ptr shift it ⦃ r => UnmU st OS Pp r.1 ⦄ :=
  WP.spec_mono (ept.unmap.z hA hPl hY.1 hY.2 hS hk a asid ipa ptr shift it) fun _ z =>
    UnmU.wr0 hR hO hTe hV z

/-- **`ept::unmap_table` keeps `UnmU`.** -/
theorem ept.unmap_table.unmu (hA : P0.ArchTotal ar) (hPl : ArchPlat ar) (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt)
    (hO : OSOK T Ω Sg OS) (hS : S2OK Te bits Hr) (hTe : Gran Te bits ⊆ Pt) {s : S}
    (hY : VsTy st kb Pp Tb Lv s ∧ S2Ty st hPl.ipa Pp Hr Te Re bits s) (hk : L.ksb s = kb)
    (hV : UnmU st OS Pp s) (a : A) (asid ipa pt : U64) :
    ept.unmap_table st ar s a asid ipa pt ⦃ r => UnmU st OS Pp r.1 ⦄ :=
  WP.spec_mono (ept.unmap_table.z hA hPl hY.1 hY.2 hS hk a asid ipa pt) fun _ z =>
    UnmU.wr0 hR hO hTe hV z

/-- **`unmap_page_table` keeps `UnmU`** (all three branches). -/
theorem vspace.unmap_page_table.unmu (hA : P0.ArchTotal ar) (hPl : ArchPlat ar)
    (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) (hO : OSOK T Ω Sg OS) (hTb : Tb ⊆ Pt)
    (hTe : Gran Te bits ⊆ Pt) (hH : HrOK kb Pp Tb Lv Hr) (hS : S2OK Te bits Hr) {s : S}
    (hY : VsTy st kb Pp Tb Lv s ∧ S2Ty st hPl.ipa Pp Hr Te Re bits s) (hk : L.ksb s = kb)
    (hV : UnmU st OS Pp s) (a : A) (asid vaddr pt : U64) :
    vspace.unmap_page_table st ar s a asid vaddr pt ⦃ r => UnmU st OS Pp r.1 ⦄ :=
  WP.spec_mono (vspace.unmap_page_table.s2 hA hPl hH hS hY.1 hY.2 hk a asid vaddr pt) fun _ z =>
    UnmU.wr0 hR hO (fun b (h : b ∈ TbO Tb Hr ∪ Gran Te bits) => h.elim (fun h' => hTb h'.1) (fun h' => hTe h')) hV z

/-- **Stage-1 `unmap_page` keeps `UnmU`.** -/
theorem vspace.unmap_page.unmu (hA : P0.ArchTotal ar) (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt)
    (hO : OSOK T Ω Sg OS) (hTb : Tb ⊆ Pt) (hH : HrOK kb Pp Tb Lv Hr) {s : S} (hY : VsTy st kb Pp Tb Lv s)
    (hk : L.ksb s = kb) (hV : UnmU st OS Pp s) (a : A) (size : capability.FrameSize) (asid vaddr pptr : U64) :
    vspace.unmap_page st ar s a size asid vaddr pptr ⦃ r => UnmU st OS Pp r.1 ⦄ :=
  WP.spec_mono (vspace.unmap_page.hr hA hH hY hk a size asid vaddr pptr) fun _ z =>
    UnmU.wr0 hR hO (fun b (h : b ∈ TbO Tb Hr) => hTb h.1) hV z

end walks

/-! ## Dropping tables from `Te`; ARMPageTableUnmap at decode level -/

section drop
variable {OS Vc Ub : Set U64} {kb : U64} {Pp Tb Pt Hr Te : Set U64} {Lv Re bits : U64 → Nat}
variable {A : Type _} {ar : machine.Arch A}

/-- **`S2Ty` over `Te \ D`** when no pool tag-1 entry and no descriptor of a remaining table names a `D` table (the
pure step for a table leaving `Te`; what is owed is a reachable-state fact giving these two premises after
ARMPageTableUnmap, module docstring). -/
theorem S2Ty.drop {n : U64} {D : Set U64} {s : S} (h : S2Ty st n Pp Hr Te Re bits s)
    (htag : ∀ p ∈ Pp, ∀ o : U64, o.val < 4096 → o.val % 8 = 0 → (L.mem s (wa p o) &&& 3#u64) = 1#u64 →
      (L.mem s (wa p o) &&& ~~~3#u64) ∉ D)
    (hdesc : ∀ p ∈ Te, p ∉ D → 0 < Re p → ∀ o : U64, o.val < 2 ^ bits p → o.val % 8 = 0 →
      (L.mem s (wa p o) &&& 3#u64) = 3#u64 → wa (L.mem s (wa p o) &&& ept.ADDR_MASK) layout.PPTR_BASE ∉ D) :
    S2Ty st n Pp Hr (Te \ D) Re bits s := by
  refine ⟨fun p hp o ho h8 hne => ?_, h.hi, fun p hp hr o ho h8 h3 => ?_⟩
  · rcases h.tag p hp o ho h8 hne with h0 | h2 | ⟨h1, hT, hR, hb⟩
    · exact Or.inl h0
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr ⟨h1, ⟨hT, htag p hp o ho h8 h1⟩, hR, hb⟩)
  · obtain ⟨hT, hR⟩ := h.desc p hp.1 hr o ho h8 h3
    exact ⟨⟨hT, hdesc p hp.1 hp.2 hr o ho h8 h3⟩, hR⟩

set_option maxHeartbeats 4000000 in
/-- **ARMPageTableUnmap at decode level keeps `VsTy ∧ S2Ty`** (vspace.rs:1094–1107, `decode_page_table` at
`ARMPageTableUnmap`): the state unchanged (not final), or `ks`, `VsTy` and `S2Ty` (same ghost sets) kept — the
restart, `unmap_page_table`, `zero(ptr, 4096)` and the cap write. Case hypotheses on the cap's object: aligned, no
wrap, no `R + 4088` word. -/
theorem vspace.decode_page_table.unmap_ty (hA : P0.ArchTotal ar) (hPl : ArchPlat ar)
    (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) (hO : OSOK T Ω Sg OS)
    {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q Rq) (hk : L.ksb s = kb) (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt)
    (hTe : Gran Te bits ⊆ Pt) (hH : HrOK kb Pp Tb Lv Hr) (hS : S2OK Te bits Hr)
    (hY : VsTy st kb Pp Tb Lv s) (h2 : S2Ty st hPl.ipa Pp Hr Te Re bits s)
    (a : A) (len slot buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ptr : U64) (mapped : Bool)
    (masid mvaddr : U64) (hsl : slot ∈ OS) (hal : Aligned ptr) (hfit : ptr.val + 4096 ≤ 2 ^ 64)
    (hh : ∀ R ∈ Hr, ∀ o : U64, o.val < 4096 → o.val % 8 = 0 → wa ptr o ≠ wa R 4088#u64) :
    vspace.decode_page_table st ar s a fl4_abi.label.ARMPageTableUnmap len slot
      (.PageTable ptr mapped masid mvaddr) buf extra ⦃ r => r.2.1 = s ∨
        (L.ksb r.2.1 = kb ∧ VsTy st kb Pp Tb Lv r.2.1 ∧ S2Ty st hPl.ipa Pp Hr Te Re bits r.2.1) ⦄ := by
  have hS' : P0.StoreTotal st := L.total
  unfold vspace.decode_page_table
  refine WP.spec_bind (sched.cur_thread.spec s) fun ct ect => ?_
  have hct : ct ∈ T := by rw [ect]; exact q.curT
  try dsimp only
  refine spec_ite (fun _ => ?_) (fun hne => absurd rfl hne)
  refine WP.spec_bind (P0.cdt.is_final_capability.p0 st s slot hS') fun b _ => ?_
  refine spec_ite (fun _ => ?_) (fun _ => (WP.spec_ok _).2 (Or.inl rfl))
  refine WP.spec_bind (stt_vk hR q hct) fun s1 ⟨w1, k1⟩ => ?_
  have hk1 : L.ksb s1 = kb := by rw [w1.1, hk]
  have hY1 : VsTy st kb Pp Tb Lv s1 := hY.keepZ hPp hTb (VsKeep.vsz k1)
  have h21 : S2Ty st hPl.ipa Pp Hr Te Re bits s1 :=
    h2.keep hPp hTe hS (VsKeep.vsz k1) fun R hR' => k1 _ (hr_vsr hTb hH hR')
  refine WP.spec_bind (Pₘ := fun r : S × A => L.ksb r.1 = kb ∧ VsTy st kb Pp Tb Lv r.1 ∧
    S2Ty st hPl.ipa Pp Hr Te Re bits r.1) ?_ ?_
  · split
    · refine WP.spec_bind (vspace.unmap_page_table.ty hA hPl hR hPp hTb hTe hH hS ⟨hY1, h21⟩ hk1 a masid mvaddr
        ptr) ?_
      rintro ⟨s3, a2⟩ ⟨w3, hY3, h23⟩
      try simp only [uncurry_apply_pair]
      refine WP.spec_bind (LawfulStore.zero_spec s3 ptr 4096#u64) fun s4 e4 => ?_
      subst e4
      obtain ⟨wz, -, hYz, h2z⟩ := zr.ty hR hPp hTb hTe hH hS ⟨hY3, h23⟩ hal hfit hh
      exact (WP.spec_ok _).2 ⟨by rw [wz.1, w3.1, hk1], hYz, h2z⟩
    · exact (WP.spec_ok _).2 ⟨hk1, hY1, h21⟩
  rintro ⟨s2, a1⟩ ⟨hk2, hY2, h22⟩
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (W7.obj.Slot.set_cap.capw (s := s2) (osw hO hsl)) fun s3 w3 => ?_
  have k3 : VsKeep st kb Pt s2 s3 := vsk_cw q hR w3
  exact (WP.spec_ok _).2 (Or.inr ⟨by rw [w3.1, hk2], hY2.keepZ hPp hTb (VsKeep.vsz k3),
    h22.keep hPp hTe hS (VsKeep.vsz k3) fun R hR' => k3 _ (hr_vsr hTb hH hR')⟩)

end drop

/-! ## ARMPageTableMap into a Stage-2 VSpace at decode level -/

section maps2
variable {OS Vc Ub : Set U64} {kb : U64} {Pp Tb Pt Hr Te : Set U64} {Lv Re bits : U64 → Nat}
variable {A : Type _} {ar : machine.Arch A}

/-- `ept::root`'s `map_err` keeps an `Ok`. -/
theorem root_map_ok (r : core.result.Result U64 error.LookupFault) :
    core.result.Result.map_err (ept.root.closure.Insts.CoreOpsFunctionFnOnceTupleLookupFaultExc st) r () ⦃ r' =>
      ∀ v, r' = .Ok v → r = .Ok v ⦄ := by
  cases r <;> simp [core.result.Result.map_err,
    ept.root.closure.Insts.CoreOpsFunctionFnOnceTupleLookupFaultExc,
    ept.root.closure.Insts.CoreOpsFunctionFnOnceTupleLookupFaultExc.call_once]

set_option maxHeartbeats 2000000 in
/-- **`ept::root` returns a Stage-2 root of `Te`** (ept.rs:153–164: `find` of the cap's ASID, equal to its pointer). -/
theorem ept.root.ty {n : U64} {s : S} (h : VsTy st kb Pp Tb Lv s) (h2 : S2Ty st n Pp Hr Te Re bits s)
    (hk : L.ksb s = kb) (c : capability.Cap) (arg : U64) :
    ept.root st s c arg ⦃ r => ∀ v, r = .Ok v → v.1 ∈ Te ∧ Re v.1 + 1 = s2lv n ∧ s2rb n ≤ bits v.1 ⦄ := by
  unfold ept.root
  split
  all_goals try (simp only [error.invalid_cap]; exact (WP.spec_ok _).2 fun v e => by cases e)
  split
  all_goals try (simp only [error.invalid_cap]; exact (WP.spec_ok _).2 fun v e => by cases e)
  split
  all_goals try (simp only [error.invalid_cap]; exact (WP.spec_ok _).2 fun v e => by cases e)
  refine WP.spec_bind (ept.find.ty h h2 hk _) fun r hr => ?_
  refine WP.spec_bind (root_map_ok (st := st) r) fun r1 hr1 => ?_
  rcases r1 with v | e
  · have hv := hr v (hr1 v rfl)
    simp only [irq_branch_ok, bind_ok]
    split
    · simp only [error.invalid_cap]; exact (WP.spec_ok _).2 fun w e => by cases e
    · exact (WP.spec_ok _).2 fun w e => by cases e; exact hv
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 fun w e => by cases e

set_option maxHeartbeats 4000000 in
/-- **ARMPageTableMap into a Stage-2 VSpace at decode level** (vspace.rs:1108–1135, `decode_page_table` at
`ARMPageTableMap` with an unmapped `PageTable` cap and an `Ept` cap in the extra slot): the state unchanged, or `ks`
and `VsTy` kept, `S2Ty` over `insert ptr Te` (depth extended), `UnmZ` over `insert ptr Te` and `UnmU`
(`ept.root.ty`, then `ept.map_table.tyU` and `ept.map_table.unmz`). -/
theorem vspace.decode_page_table.map_s2 (hPl : ArchPlat ar) (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt)
    (hO : OSOK T Ω Sg OS) {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q Rq) (hk : L.ksb s = kb) (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt)
    (hTe : Gran Te bits ⊆ Pt) (hH : HrOK kb Pp Tb Lv Hr) {ptr asid0 v0 : U64} (h12 : bits ptr = 12)
    (hS : S2OK (insert ptr Te) bits Hr) (hD : S2Pl kb Pp Tb (insert ptr Te) bits) (hU : UnmZ st OS Pt Te bits s)
    (hV : UnmU st OS Pp s) (hY : VsTy st kb Pp Tb Lv s) (h2 : S2Ty st hPl.ipa Pp Hr Te Re bits s)
    (a : A) (len slot buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (hsl : slot ∈ OS)
    (hc : obj.Slot.cap st slot s = ok (.PageTable ptr false asid0 v0))
    (hx : ∀ x ∈ extra.val, x ≠ 0#u64 → ∃ p l m asid v, obj.Slot.cap st x s = ok (.Ept p l m asid v)) :
    vspace.decode_page_table st ar s a fl4_abi.label.ARMPageTableMap len slot (.PageTable ptr false asid0 v0) buf
      extra ⦃ r => r.2.1 = s ∨ (L.ksb r.2.1 = kb ∧ VsTy st kb Pp Tb Lv r.2.1 ∧
        (∃ Re' : U64 → Nat, (∀ p ∈ Te, Re' p = Re p) ∧ S2Ty st hPl.ipa Pp Hr (insert ptr Te) Re' bits r.2.1) ∧
        UnmZ st OS Pt (insert ptr Te) bits r.2.1 ∧ UnmU st OS Pp r.2.1) ⦄ := by
  have hS' : P0.StoreTotal st := L.total
  have hS0 : S2OK Te bits Hr := S2OK.sub hS (Set.subset_insert _ _)
  unfold vspace.decode_page_table
  refine WP.spec_bind (sched.cur_thread.spec s) fun ct ect => ?_
  try dsimp only
  refine spec_ite (fun h => absurd h (by first | decide | simp [fl4_abi.label.ARMPageTableMap,
    fl4_abi.label.ARMPageTableUnmap])) (fun _ => ?_)
  refine spec_ite (fun _ => by asErr) (fun _ => ?_)
  refine WP.spec_bind (vspace.extra.memA extra 0#usize) fun o ho => ?_
  rcases o with _ | x
  · asErr
  obtain ⟨hxm, hx0⟩ := ho x rfl
  obtain ⟨p0, l0, m0, as0, va0, hxc⟩ := hx x hxm hx0
  try dsimp only
  refine spec_ite (fun _ => ?_) (fun _ => by asErr)
  refine spec_ite (fun _ => by asErr) (fun _ => ?_)
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS') fun vaddr1 _ => ?_
  refine WP.spec_bind (show obj.Slot.cap st x s ⦃ c => c = .Ept p0 l0 m0 as0 va0 ⦄ by
    rw [hxc]; exact (WP.spec_ok _).2 rfl) fun vcap hv => ?_
  subst hv
  refine WP.spec_bind (Pₘ := fun b => b = false) ((WP.spec_ok _).2 rfl) fun b hb => ?_
  refine spec_ite (fun h => by rw [hb] at h; cases h) (fun _ => ?_)
  refine WP.spec_bind (P0.vspace.is_valid_vtable_root.p0 _) fun b1 _ => ?_
  refine spec_ite (fun _ => ?_) (fun _ => by asErr)
  refine WP.spec_bind (Pₘ := fun b => b = true) ((WP.spec_ok _).2 rfl) fun b2 hb2 => ?_
  refine spec_ite (fun _ => ?_) (fun h => absurd hb2 h)
  refine WP.spec_bind (ept.root.ty hY h2 hk _ 1#u64) fun r hr => ?_
  rcases r with ⟨root, asid1⟩ | e
  swap
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 (Or.inl rfl)
  obtain ⟨hrT, hre, hrb⟩ := hr _ rfl
  simp only [irq_branch_ok, bind_ok]
  refine WP.spec_mono (WP.spec_and
    (ept.map_table.tyU hPl hR hO q hk hPp hTb hTe hH h12 hS hD hU hY h2 hrT hre hrb a asid1 vaddr1 hsl hc)
    (ept.map_table.unmz hPl hR hO q hTe hS0 h2 hrT hre hrb a asid1 vaddr1 hsl h12 hc hU hV)) ?_
  rintro r ⟨h1, h3⟩
  rcases h1 with e | ⟨hk', hY', hS2⟩
  · exact Or.inl e
  rcases h3 with e | ⟨hU', hV'⟩
  · exact Or.inl e
  exact Or.inr ⟨hk', hY', hS2, hU', hV'⟩

end maps2

end ST
end R
end W7

end

end Fl4ProofsA64.P1
