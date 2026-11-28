/-
P1 (aarch64, gen 56): **retype (no reset) keeps `RngOneA64`, `KindA` and `UtRev`**, with `UtRev` along the
flag-bit writes of `insert_new_cap`; the generic `create_new_objects` loop; `OSOK` of a union of slot sets.

* **Bit 48** (`MDB_REVOCABLE`, obj.rs:276–282): `revocable_eqA` (`revocable` reads bit 48 of the `NEXT` word),
  `set_next_rvb` (`set_next` keeps bit 48: it rewrites the pointer bits only, obj.rs:263–266), **`set_nf_rvb`**
  (`set_next_flags … true _` sets bit 48, obj.rs:270–275). Word-level frame lemmas `w24_wr16` / `w24_wr24` /
  `w24_wr2` (a `PREV` write, another slot's `NEXT` write, an in-place cap write keep every `OS` slot's `NEXT` word).
* **`cdt.insert_new_cap.rvb`**: every `OS` slot but the new one keeps bit 48 of its `NEXT` word, the new one has it
  set (cdt.rs:187–196: flags `true true`); `UtRev.newcap` (data level) and **`cdt.insert_new_cap.utRev`**.
* **`RngOneA64.insN`**: `RngOneA64` along an insertion after a non-key `src` (an `Untyped`) of a cap whose class is
  fresh (meets no member's class) — x86 has no counterpart (its `RngOne` is not kept along retype; A64's `chunk`
  is a field). The new slot sits right after `src`; if it fell strictly between two members of one class, the old
  `chunk` would put `src` (not a key cap) in that class.
* **`objects.create_new_objects_loop.inv`**: the gen-55 loop (`create_new_objects_loop.loopA`) for any invariant
  kept by `OSKeep` steps and by each `insert_new_cap` (same proof, invariant abstracted).
* **`LoopK`** (ghost + `MdbLk` + `RngOneA64` + `UtRev` + the cap facts of `LoopA`), `LoopK.start` / `.keep` /
  `.step`; freshness of the new objects' bases (`bjA_inj`; old key caps off the free region by `FreeFresh`, from
  `UtInvA.freeFresh`).
* **`untyped.retype.rk`** (`reset = false`, the hypotheses of gen 55's `untyped.retype.tree`): from `TreeA` and
  `RngOneA64` / `KindA` / `UtRev` at the start, `∃ G', MdbLk ∧ RngOneA64 ∧ KindA ∧ UtRev` at the end;
  **`untyped.retype.treeK`**: both on one ghost (`MdbLk.chains_iff`, `RngOneA64.congr`).
* **`cdt.insert_with_cap.rvb`** / **`cdt.insert_with_cap.utRev`** (cdt.rs:35–46: `set_untyped_cap_as_full` rewrites
  only the source's cap words, `cdt.set_untyped_cap_as_full.w2`; the new slot's flags are `is_cap_revocable`, `true`
  for an `Untyped`, objects.rs:186–198, `is_cap_revocable_ut`; `set_nf_rv`); the source stays untyped only if it
  was (`SrcU`), so it keeps its bit.
* **`cdt.move_cap.rvb`** / **`cdt.move_cap.utRev`** (cdt.rs:49–64: `dest` takes the source's bit; case hypothesis: a
  moved `Untyped` comes from an `Untyped` slot, `UA.isut`), `bit_next`.
* `UtRev.rev`: `UtRev` gives the `revocable = true` hypothesis of `objects.derive_cap.noDesc` /
  `cdt.ensure_no_children.noDesc` / `TreeA.lowerW_enc`; `objects.derive_cap.noDescU` (that instance).
* **`OSOK.union`**: `OSOK` of `OS ∪ N` from `OSOK` of each over the new sets and the two sets' slots apart (the
  apartness of old slots from the new objects' slots is the heap fact of the gen-56 handoff, not proved here).
* **Gen 60**: `inv` is an instance of MdbTreeL's `create_new_objects_loop.genJK`; `untyped.retype.rkG` is the one
  proof of `rk` (`Zq := True`) and MdbUZL's `rkZ`; `keyPairA` is the common end of `rkG` (`KindA`) and MdbTreeN's
  `nlG` (`ClsA`).

No named premise; new definitions and theorems only (`hCO` and the decode's size checks stay case hypotheses as in
gen 55).
-/
import Fl4ProofsA64.P1.MdbTreeS
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts Fl4Proofs.P3

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {Sg : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

/-! ## Bit 48 -/

theorem revocable_eqA (s : S) (x : U64) :
    obj.Slot.revocable st x s = ok ((L.mem s (wa x 24#u64) &&& RVB) != 0#u64) := by
  unfold obj.Slot.revocable obj.Slot.next_word
  simp only [lift, bind_ok, cte_next, L.read_eq, rvb_val]

theorem or_bit_and (a f R : U64) : ((a ||| R) ||| f) &&& R = R := by
  rw [UScalar.eq_equiv_bv_eq]
  simp only [UScalar.bv_and, UScalar.bv_or]
  apply BitVec.eq_of_getLsbD_eq; intro i
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or]
  cases a.bv.getLsbD i <;> cases R.bv.getLsbD i <;> cases f.bv.getLsbD i <;> simp

theorem rvb_or (a f : U64) : ((a ||| RVB) ||| f) &&& RVB = RVB := or_bit_and a f RVB

theorem ptr_bits (a n P R : U64) (hc : R &&& P = 0#u64) : ((a &&& ~~~ P) ||| (n &&& P)) &&& R = a &&& R := by
  rw [UScalar.eq_equiv_bv_eq] at hc ⊢
  apply BitVec.eq_of_getLsbD_eq; intro i
  have h1 := congrArg (fun x => BitVec.getLsbD x i) hc
  simp only [UScalar.bv_and, UScalar.bv_or, UScalar.bv_not, BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_not] at h1 ⊢
  revert h1
  cases a.bv.getLsbD i <;> cases n.bv.getLsbD i <;> cases R.bv.getLsbD i <;> cases P.bv.getLsbD i <;> simp

theorem ptr_rvb (a n : U64) :
    ((a &&& ~~~ obj.MDB_PTR_MASK) ||| (n &&& obj.MDB_PTR_MASK)) &&& RVB = a &&& RVB := ptr_bits a n _ _ rvbc

/-- **`set_next_flags` with `revocable = true`** writes a `NEXT` word with bit 48 set. -/
theorem set_nf_rvb (s : S) (x n : U64) (f : Bool) :
    obj.Slot.set_next_flags st x s n true f ⦃ s' => ∃ w, s' = L.wr s (wa x 24#u64) w ∧ w &&& RVB = RVB ⦄ := by
  unfold obj.Slot.set_next_flags obj.Slot.next_word
  simp only [lift, bind_ok, cte_next, L.read_eq, fb_val, rvb_val]
  cases f <;> simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, L.write_eq, WP.spec_ok] <;>
    exact ⟨_, rfl, rvb_or _ _⟩

section words
variable {OS : Set U64}

/-- A `PREV` write keeps every `OS` slot's `NEXT` word. -/
theorem w24_wr16 (hO : OSOK T Ω Sg OS) (s : S) {p y : U64} (hp : p ∈ OS) (hy : y ∈ OS) (v : U64) :
    L.mem (L.wr s (wa p 16#u64) v) (wa y 24#u64) = L.mem s (wa y 24#u64) := by
  by_cases e : y = p
  · subst e
    obtain ⟨v8, v16, v24⟩ := vals hO hy
    exact L.mem_wr_ne (hO.al hy (k := 16#u64) (by simp) (by simp)) (hO.al hy (k := 24#u64) (by simp) (by simp))
      (by omega)
  · exact (SK.wr (st := st) hO s hp hy e (k := 16#u64) (by simp) (by simp) v).2.2.2

/-- Another slot's `NEXT` write keeps an `OS` slot's `NEXT` word. -/
theorem w24_wr24 (hO : OSOK T Ω Sg OS) (s : S) {p y : U64} (hp : p ∈ OS) (hy : y ∈ OS) (e : y ≠ p) (v : U64) :
    L.mem (L.wr s (wa p 24#u64) v) (wa y 24#u64) = L.mem s (wa y 24#u64) :=
  (SK.wr (st := st) hO s hp hy e (k := 24#u64) (by simp) (by simp) v).2.2.2

theorem w24_self (hO : OSOK T Ω Sg OS) (s : S) {p : U64} (hp : p ∈ OS) (v : U64) :
    L.mem (L.wr s (wa p 24#u64) v) (wa p 24#u64) = v :=
  L.mem_wr_same (hO.al hp (k := 24#u64) (by simp) (by simp))

/-- **`insert_new_cap` and bit 48**: every `OS` slot but `dest` keeps bit 48 of its `NEXT` word (`set_next`
rewrites `src`'s pointer bits only), `dest`'s is set (`set_next_flags … true true`). -/
theorem cdt.insert_new_cap.rvb (hO : OSOK T Ω Sg OS) {s : S} {src dest : U64} {nc : capability.Cap}
    (hsrc : src ∈ OS) (hd : dest ∈ OS) (hsd : src ≠ dest) (hw : CapRt.EncWf nc)
    (hnN : NxA st s src ≠ 0#u64 → NxA st s src ∈ OS) :
    cdt.insert_new_cap st s src dest nc ⦃ s' =>
      (∀ y ∈ OS, y ≠ dest → L.mem s' (wa y 24#u64) &&& RVB = L.mem s (wa y 24#u64) &&& RVB) ∧
      L.mem s' (wa dest 24#u64) &&& RVB = RVB ⦄ := by
  unfold cdt.insert_new_cap
  rw [next_eq, bind_ok]
  obtain ⟨w0, w1, he, -⟩ := CapRt.decode_encode nc hw
  rw [set_cap_eq he, bind_ok]
  have K2 : ∀ y ∈ OS, L.mem (L.wr (L.wr s dest w0) (wa dest 8#u64) w1) (wa y 24#u64) = L.mem s (wa y 24#u64) :=
    fun y hy => (set_cap_links hO hd y hy).2
  generalize L.wr (L.wr s dest w0) (wa dest 8#u64) w1 = s2 at K2 ⊢
  rw [set_prev_eq, bind_ok]
  have K3 : ∀ y ∈ OS, L.mem (L.wr s2 (wa dest 16#u64) src) (wa y 24#u64) = L.mem s (wa y 24#u64) :=
    fun y hy => (w24_wr16 hO s2 hd hy src).trans (K2 y hy)
  generalize L.wr s2 (wa dest 16#u64) src = s3 at K3 ⊢
  refine WP.spec_bind (set_nf_rvb s3 dest _ true) ?_
  rintro s4 ⟨w4, rfl, hw4⟩
  have K4 : ∀ y ∈ OS, y ≠ dest → L.mem (L.wr s3 (wa dest 24#u64) w4) (wa y 24#u64) = L.mem s (wa y 24#u64) :=
    fun y hy e => (w24_wr24 hO s3 hd hy e w4).trans (K3 y hy)
  have D4 : L.mem (L.wr s3 (wa dest 24#u64) w4) (wa dest 24#u64) &&& RVB = RVB := by rw [w24_self hO s3 hd]; exact hw4
  generalize L.wr s3 (wa dest 24#u64) w4 = s5 at K4 D4 ⊢
  have fin : ∀ s6 : S, (∀ y ∈ OS, L.mem s6 (wa y 24#u64) = L.mem s5 (wa y 24#u64)) →
      obj.Slot.set_next st src s6 dest ⦃ s' =>
        (∀ y ∈ OS, y ≠ dest → L.mem s' (wa y 24#u64) &&& RVB = L.mem s (wa y 24#u64) &&& RVB) ∧
        L.mem s' (wa dest 24#u64) &&& RVB = RVB ⦄ := by
    intro s6 h6
    rw [set_next_eq, WP.spec_ok]
    refine ⟨fun y hy e => ?_, ?_⟩
    · by_cases ys : y = src
      · subst ys
        rw [w24_self hO s6 hy, ptr_rvb, h6 y hy, K4 y hy e]
      · rw [w24_wr24 hO s6 hsrc hy ys, h6 y hy, K4 y hy e]
    · rw [w24_wr24 hO s6 hsrc hd hsd.symm, h6 dest hd]; exact D4
  simp only [obj.Slot.is_null, bind_ok]
  split
  · simp only [bind_ok]
    exact fin s5 fun _ _ => rfl
  · rename_i hn0
    have hN0 : NxA st s src ≠ 0#u64 := by simpa using hn0
    rw [set_prev_eq, bind_ok]
    exact fin _ fun y hy => w24_wr16 hO s5 (hnN hN0) hy dest

variable {G : List (List U64)} in
/-- **`insert_new_cap` keeps the link invariant** (`cdt.insert_new_cap.lkT` without the tree). -/
theorem cdt.insert_new_cap.lk (hO : OSOK T Ω Sg OS) {s : S} (hM : MdbLk st OS G s)
    {src dest : U64} {nc : capability.Cap} (hsrc : src ∈ G.flatten) (hd : dest ∈ OS)
    (hd0 : capA st s dest = .Null) (hdc : obj.sext48 dest = ok dest) (hw : CapRt.EncWf nc) (hnc : nc ≠ .Null) :
    cdt.insert_new_cap st s src dest nc ⦃ s' => MdbLk st OS (insG src dest G) s' ∧ capA st s' dest = nc ∧
      (∀ y ∈ OS, y ≠ dest → capA st s' y = capA st s y) ⦄ := by
  have h0 : ∀ y ∈ OS, y ≠ 0#u64 := hO.nz
  have inOS : ∀ y ∈ G.flatten, y ∈ OS := fun y hy => ((hM.members y).1 hy).1
  have F := hM.lkF h0
  have os := inOS src hsrc
  have dG : dest ∉ G.flatten := fun hm => ((hM.members dest).1 hm).2 hd0
  have hsd : src ≠ dest := fun e => dG (e ▸ hsrc)
  have hNm : NxA st s src ≠ 0#u64 → NxA st s src ∈ G.flatten := F.nxm _ hsrc
  have hNd : NxA st s src ≠ dest := fun e => by
    have h1 : NxA st s src ≠ 0#u64 := fun e0 => h0 dest hd (e ▸ e0)
    exact dG (e ▸ hNm h1)
  refine WP.spec_mono (cdt.insert_new_cap.lr hO (LR.self s) os hd hsd hdc hw (fun h => inOS _ (hNm h))) ?_
  rintro s' ⟨hL, ed, ek⟩
  refine ⟨hM.ins h0 hsrc hd hd0 (by rw [ed]; exact hnc) (fun y hy hyd => by rw [ek y hy hyd]) ?_ ?_ ?_
    (fun hN => ?_) (fun y hy h1 h2 => ?_) (fun y hy h1 h2 => ?_), ed, ek⟩
  · rw [(hL src os).2]; simp
  · rw [(hL dest hd).1]; simp [hNd.symm]
  · rw [(hL dest hd).2]; simp [hsd.symm]
  · rw [(hL _ (inOS _ (hNm hN))).1]; simp [hN]
  · rw [(hL y hy).2]; simp [h1, h2]
  · rw [(hL y hy).1]; simp [h1, h2]

/-- **`UtRev` after a step that writes a new cap with bit 48 set** and keeps every other slot's cap and bit. -/
theorem UtRev.newcap {s s' : S} (h : UtRev st OS s) {dest : U64}
    (hk : ∀ y ∈ OS, y ≠ dest → capA st s' y = capA st s y ∧
      L.mem s' (wa y 24#u64) &&& RVB = L.mem s (wa y 24#u64) &&& RVB)
    (hd : L.mem s' (wa dest 24#u64) &&& RVB = RVB) : UtRev st OS s' := by
  intro u hu hc
  by_cases e : u = dest
  · rw [e, revocable_eqA, hd]; first | rfl | decide | simp
  · have h1 := h u hu (by rw [← (hk u hu e).1]; exact hc)
    rw [revocable_eqA] at h1 ⊢
    rw [(hk u hu e).2]; exact h1

/-- **`insert_new_cap` keeps `UtRev`.** -/
theorem cdt.insert_new_cap.utRev (hO : OSOK T Ω Sg OS) {s : S} (hR : UtRev st OS s) {src dest : U64}
    {nc : capability.Cap} (hsrc : src ∈ OS) (hd : dest ∈ OS) (hsd : src ≠ dest) (hdc : obj.sext48 dest = ok dest)
    (hw : CapRt.EncWf nc) (hnN : NxA st s src ≠ 0#u64 → NxA st s src ∈ OS) :
    cdt.insert_new_cap st s src dest nc ⦃ s' => UtRev st OS s' ⦄ := by
  have hA := cdt.insert_new_cap.lr hO (LR.self s) hsrc hd hsd hdc hw hnN
  have hB := cdt.insert_new_cap.rvb hO hsrc hd hsd hw hnN
  obtain ⟨v, hv, hpa⟩ := spec_exA hA
  rw [hv, WP.spec_ok] at hB ⊢
  exact hR.newcap (fun y hy e => ⟨hpa.2.2 y hy e, hB.1 y hy e⟩) hB.2

/-- `UtRev` gives `derive_cap.noDesc`'s / `ensure_no_children.noDesc`'s `revocable = true`. -/
theorem UtRev.rev {s : S} (h : UtRev st OS s) {x p b i : U64} {d : Bool} (hx : x ∈ OS)
    (hc : capA st s x = .Untyped p b i d) : obj.Slot.revocable st x s = ok true :=
  h x hx (by rw [hc]; rfl)

end words

theorem objects.derive_cap.noDescU {OS : Set U64} {G : List (List U64)} {par : U64 → Option U64}
    (hO : OSOK T Ω Sg OS) {s : S} (h : TreeA st OS G par s) (hR : UtRev st OS s) {x p b i : U64}
    {d : Bool} (hx : x ∈ OS) (hcx : capA st s x = .Untyped p b i d) :
    objects.derive_cap st s x (.Untyped p b i d) ⦃ r => ∀ nc, r = .Ok nc → ∀ y, ¬ Mdb.Desc par y x ⦄ :=
  objects.derive_cap.noDesc hO h hx hcx (hR.rev hx hcx)

/-! ## `RngOneA64` along the insertion of a fresh class after a non-key slot -/

section insN
variable {G : List (List U64)}

theorem nodup_idxA {l : List U64} (hl : l.Nodup) {i k : Nat} {a : U64} (hi : l[i]? = some a)
    (hk : l[k]? = some a) : i = k := by
  obtain ⟨hi1, hi2⟩ := List.getElem?_eq_some_iff.1 hi
  obtain ⟨hk1, hk2⟩ := List.getElem?_eq_some_iff.1 hk
  first
  | exact (List.Nodup.getElem_inj_iff hl).1 (hi2.trans hk2.symm)
  | (by_contra hne
     rcases Nat.lt_or_gt_of_ne hne with q | q
     · exact (List.nodup_iff_getElem?_ne_getElem?.1 hl i k q hk1) (hi.trans hk.symm)
     · exact (List.nodup_iff_getElem?_ne_getElem?.1 hl k i q hi1) (hk.trans hi.symm))

/-- **`RngOneA64` along `dest` inserted after a non-key `src`, `dest`'s cap of a fresh class** (module
docstring). -/
theorem RngOneA64.insN {s s' : S} (h : RngOneA64 st G s) (hnd : G.flatten.Nodup) {src dest : U64}
    (hsrc : src ∈ G.flatten) (dG : dest ∉ G.flatten)
    (hk : ∀ y ∈ G.flatten, capA st s' y = capA st s y) (hns : ¬ RngKeyA (capA st s src))
    (hfr : RngKeyA (capA st s' dest) → ∀ y ∈ G.flatten, RngKeyA (capA st s y) →
      clsA (capA st s y) ≠ clsA (capA st s' dest)) :
    RngOneA64 st (insG src dest G) s' := by
  have hperm := insG_perm (dest := dest) hnd hsrc
  have hnd' : (insG src dest G).flatten.Nodup := hperm.nodup_iff.2 (List.nodup_cons.2 ⟨dG, hnd⟩)
  have memc : ∀ {c : List U64}, c ∈ G → ∀ {n : Nat} {w : U64}, c[n]? = some w → w ∈ G.flatten :=
    fun hc _ _ e => List.mem_flatten.2 ⟨_, hc, List.mem_of_getElem? e⟩
  have ndst : ∀ {c : List U64}, c ∈ G → ∀ {n : Nat} {w : U64}, c[n]? = some w → w ≠ dest :=
    fun hc _ _ e hw => dG (hw ▸ memc hc e)
  obtain ⟨cs, hcs0, hscs⟩ := List.mem_flatten.1 hsrc
  refine ⟨fun y hy y' hy' k k' hc => ?_, fun ch hch i j k y z y' hi hj hk2 hij hjk ky ky' hc => ?_⟩
  · rcases List.mem_cons.1 (hperm.mem_iff.1 hy) with e | hyo <;>
      rcases List.mem_cons.1 (hperm.mem_iff.1 hy') with e' | hyo'
    · rw [e, e']
      refine ⟨insA src dest cs, List.mem_map.2 ⟨cs, hcs0, rfl⟩, ?_, ?_⟩ <;>
        exact (List.Perm.mem_iff (insA_perm hscs)).2 (List.mem_cons.2 (Or.inl rfl))
    · rw [e] at k hc
      rw [hk y' hyo'] at k' hc
      exact absurd hc.symm (hfr k y' hyo' k')
    · rw [e'] at k' hc
      rw [hk y hyo] at k hc
      exact absurd hc (hfr k' y hyo k)
    · rw [hk y hyo] at k hc; rw [hk y' hyo'] at k' hc
      obtain ⟨c, hc0, m1, m2⟩ := h.one y hyo y' hyo' k k' hc
      have ins : ∀ {w : U64}, w ∈ c → w ≠ dest → w ∈ insA src dest c := fun hw hwd =>
        mem_insA_of (by unfold oldA; rw [if_neg hwd]; exact hw)
      exact ⟨_, List.mem_map.2 ⟨c, hc0, rfl⟩, ins m1 (fun e => dG (e ▸ hyo)), ins m2 (fun e => dG (e ▸ hyo'))⟩
  · obtain ⟨c, hcG, rfl⟩ := insG_mem hch
    have hcn := ch_nodup hnd hcG
    have hchn := ch_nodup hnd' hch
    have memn : ∀ {n : Nat} {w : U64}, (insA src dest c)[n]? = some w → w ∈ (insG src dest G).flatten :=
      fun e => List.mem_flatten.2 ⟨_, hch, List.mem_of_getElem? e⟩
    have old : ∀ {n : Nat} {w : U64}, (insA src dest c)[n]? = some w → w ≠ dest → w ∈ G.flatten := by
      intro n w e hw
      rcases List.mem_cons.1 (hperm.mem_iff.1 (memn e)) with e' | h'
      · exact absurd e' hw
      · exact h'
    -- the two ends are old slots
    have yd : y ≠ dest := by
      intro e; rw [e] at hi ky hc
      by_cases e' : y' = dest
      · rw [e'] at hk2; have := nodup_idxA hchn hi hk2; omega
      · have o' := old hk2 e'
        rw [hk y' o'] at ky' hc
        exact hfr ky y' o' ky' hc.symm
    have yd' : y' ≠ dest := by
      intro e; rw [e] at hk2 ky' hc
      have o := old hi yd
      rw [hk y o] at ky hc
      exact hfr ky' y o ky hc
    have oy := old hi yd
    have oy' := old hk2 yd'
    rw [hk y oy] at ky hc ⊢; rw [hk y' oy'] at ky' hc
    by_cases hsc : src ∈ c
    · obtain ⟨is, his, hsi⟩ := List.getElem_of_mem hsc
      have esi : c[is]? = some src := by rw [List.getElem?_eq_getElem his, hsi]
      have hI := insA_idx (dest := dest) hcn esi
      rw [hI] at hi hj hk2
      have iy : i ≠ is + 1 := fun e => by
        rw [e, if_neg (by omega), if_pos rfl] at hi; exact yd (Option.some.inj hi).symm
      have ky1 : k ≠ is + 1 := fun e => by
        rw [e, if_neg (by omega), if_pos rfl] at hk2; exact yd' (Option.some.inj hk2).symm
      by_cases jz : j = is + 1
      · -- `z` is `dest`: `src` lies strictly between two members of one class
        exfalso
        have hi' : i ≤ is := by omega
        rw [if_pos hi'] at hi
        have hk' : c[k - 1]? = some y' := by rw [if_neg (by omega), if_neg ky1] at hk2; exact hk2
        have hii : i < is := by
          rcases Nat.lt_or_ge i is with q | q
          · exact q
          · have : i = is := by omega
            rw [this, esi] at hi
            have e5 := Option.some.inj hi
            rw [← e5] at ky; exact absurd ky hns
        exact hns (h.chunk c hcG i is (k - 1) y src y' hi esi hk' hii (by omega) ky ky' hc).1
      · have zd : z ≠ dest := by
          intro e
          by_cases q : j ≤ is
          · rw [if_pos q] at hj; exact ndst hcG hj e
          · rw [if_neg q, if_neg jz] at hj; exact ndst hcG hj e
        have oz := old (by rw [hI]; exact hj) zd
        rw [hk z oz]
        -- old indices: `n ↦ n` below `is + 1`, `n ↦ n - 1` above
        have e1 : c[if i ≤ is then i else i - 1]? = some y := by
          by_cases q : i ≤ is
          · rw [if_pos q] at hi ⊢; exact hi
          · rw [if_neg q, if_neg iy] at hi; rw [if_neg q]; exact hi
        have e2 : c[if j ≤ is then j else j - 1]? = some z := by
          by_cases q : j ≤ is
          · rw [if_pos q] at hj ⊢; exact hj
          · rw [if_neg q, if_neg jz] at hj; rw [if_neg q]; exact hj
        have e3 : c[if k ≤ is then k else k - 1]? = some y' := by
          by_cases q : k ≤ is
          · rw [if_pos q] at hk2 ⊢; exact hk2
          · rw [if_neg q, if_neg ky1] at hk2; rw [if_neg q]; exact hk2
        refine h.chunk c hcG _ _ _ y z y' e1 e2 e3 ?_ ?_ ky ky' hc
        · split_ifs <;> omega
        · split_ifs <;> omega
    · rw [insA_of_not_mem hsc] at hi hj hk2
      have oz := memc hcG hj
      rw [hk z oz]
      exact h.chunk c hcG i j k y z y' hi hj hk2 hij hjk ky ky' hc

end insN

/-! ## The loop, for any invariant -/

/-- **`create_new_objects`' loop for any invariant** kept by `OSKeep` steps and by each `insert_new_cap` (gen 55's
`create_new_objects_loop.loopA`, the invariant abstracted). -/
theorem objects.create_new_objects_loop.inv {A : Type _} (ar : machine.Arch A) {OS : Set U64}
    {cj : Nat → capability.Cap} {I : S → Nat → Prop} (t src dcn off w base us z : U64) (dev : Bool)
    (hz : z.val < 64) (hfit : base.val + w.val * 2 ^ z.val ≤ 2 ^ 64)
    (hCO : ∀ (s : S) (a : A) (j : Nat), j < w.val →
      objects.create_object st ar s a t (bjA base z j) us dev ⦃ r => r.1 = cj j ∧ OSKeep st OS s r.2.1 ⦄)
    (hkeep : ∀ (s s' : S) (i : Nat), i < w.val → I s i → OSKeep st OS s s' → I s' i)
    (hstep : ∀ (s : S) (i : Nat), i < w.val → I s i →
      cdt.insert_new_cap st s src (djA dcn off i) (cj i) ⦃ s' => I s' (i + 1) ⦄)
    (s : S) (a : A) (hinv : I s 0) :
    objects.create_new_objects_loop st ar s a t src dcn off w base us dev z 0#u64 ⦃ r => I r.1 w.val ⦄ :=
  objects.create_new_objects_loop.genJK ar t src dcn off w base us z dev hz hfit
    (fun s a j hj h => WP.spec_mono (hCO s a j hj) fun r hr => ⟨hr.1, hkeep s r.2.1 j hj h hr.2⟩) hstep s a hinv

/-! ## The loop invariant for `RngOneA64` / `UtRev` -/

/-- **After `i` objects** (module docstring): a ghost with `MdbLk` and `RngOneA64`, `src` a member, `UtRev`, the
old slots as at `s1`, the first `i` new slots holding `cj j`. -/
def LoopK (st : machine.Store S) [L : LawfulStore st] (OS : Set U64) (s1 : S) (src : U64) (dslot : Nat → U64)
    (cj : Nat → capability.Cap) (s : S) (i : Nat) : Prop :=
  ∃ G : List (List U64), MdbLk st OS G s ∧ RngOneA64 st G s ∧ src ∈ G.flatten ∧ UtRev st OS s ∧
    (∀ x ∈ OS, (∀ j, j < i → x ≠ dslot j) → capA st s x = capA st s1 x) ∧
    (∀ j, j < i → capA st s (dslot j) = cj j)

section loopk
variable {OS : Set U64} {s1 : S} {src : U64} {dslot : Nat → U64} {cj : Nat → capability.Cap}

theorem LoopK.start {G : List (List U64)} (hM : MdbLk st OS G s1) (hRO : RngOneA64 st G s1)
    (hsrc : src ∈ G.flatten) (hR : UtRev st OS s1) : LoopK st OS s1 src dslot cj s1 0 :=
  ⟨G, hM, hRO, hsrc, hR, fun _ _ _ => rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩

theorem LoopK.keep {s s' : S} {i : Nat} (h : LoopK st OS s1 src dslot cj s i) (hdO : ∀ j, j < i → dslot j ∈ OS)
    (k : OSKeep st OS s s') : LoopK st OS s1 src dslot cj s' i := by
  obtain ⟨G, hM, hRO, hs, hR, h1, h2⟩ := h
  have hOS : ∀ x ∈ G.flatten, x ∈ OS := fun x hx => ((hM.members x).1 hx).1
  refine ⟨G, hM.keep (fun x hx => ⟨(k x hx).2.2.1, (k x hx).2.2.2⟩) (fun x hx => by rw [k.capA hx]),
    hRO.keep (fun x hx => by rw [k.capA (hOS x hx)]; exact ⟨Iff.rfl, fun _ => rfl⟩), hs, hR.keep k,
    fun x hx hn => (k.capA hx).trans (h1 x hx hn), fun j hj => (k.capA (hdO j hj)).trans (h2 j hj)⟩

theorem spec_andA {α : Type _} {m : Result α} {P Q : α → Prop} (h1 : m ⦃ r => P r ⦄) (h2 : m ⦃ r => Q r ⦄) :
    m ⦃ r => P r ∧ Q r ⦄ :=
  spec_andL h1 h2

set_option maxHeartbeats 1000000 in
/-- **One `insert_new_cap`** (`LoopA.step`'s shape): the new cap's base meets no old key cap's base, nor another
new cap's. -/
theorem LoopK.step (hO : OSOK T Ω Sg OS) {s : S} {i w : Nat} (hi : i < w)
    (h : LoopK st OS s1 src dslot cj s i) (hdO : ∀ j, j < w → dslot j ∈ OS)
    (hdn : ∀ j, j < w → capA st s1 (dslot j) = .Null) (hdc : ∀ j, j < w → obj.sext48 (dslot j) = ok (dslot j))
    (hinj : ∀ j l, j < w → l < w → dslot j = dslot l → j = l) (hsn : ∀ j, j < w → src ≠ dslot j)
    (hwf : ∀ j, j < w → CapRt.EncWf (cj j)) (hcn : ∀ j, j < w → cj j ≠ .Null)
    (hns : ¬ RngKeyA (capA st s1 src))
    (hfo : ∀ j, j < w → ∀ x ∈ OS, RngKeyA (capA st s1 x) → ptrA (capA st s1 x) ≠ ptrA (cj j))
    (hfn : ∀ j l, j < w → l < w → j ≠ l → ptrA (cj l) ≠ ptrA (cj j)) :
    cdt.insert_new_cap st s src (dslot i) (cj i) ⦃ s' => LoopK st OS s1 src dslot cj s' (i + 1) ⦄ := by
  obtain ⟨G, hM, hRO, hs, hR, h1, h2⟩ := h
  have hne : ∀ j, j < i → dslot i ≠ dslot j := fun j hj e => by
    have := hinj i j hi (by omega) e; omega
  have hd0 : capA st s (dslot i) = .Null := by rw [h1 _ (hdO i hi) hne]; exact hdn i hi
  have dG : dslot i ∉ G.flatten := fun hm => ((hM.members _).1 hm).2 hd0
  have hsOS : src ∈ OS := ((hM.members src).1 hs).1
  have hsd : src ≠ dslot i := hsn i hi
  have F := hM.lkF hO.nz
  have hNm : NxA st s src ≠ 0#u64 → NxA st s src ∈ G.flatten := F.nxm _ hs
  have hnN : NxA st s src ≠ 0#u64 → NxA st s src ∈ OS := fun hN => ((hM.members _).1 (hNm hN)).1
  have hA := cdt.insert_new_cap.lk hO hM hs (hdO i hi) hd0 (hdc i hi) (hwf i hi) (hcn i hi)
  refine WP.spec_mono (spec_andA hA (cdt.insert_new_cap.utRev hO hR hsOS (hdO i hi) hsd (hdc i hi) (hwf i hi) hnN))
    ?_
  rintro s' ⟨⟨hM', ed, ek⟩, hR'⟩
  have hsrc1 : capA st s src = capA st s1 src := h1 src hsOS fun j hj e => hsn j (by omega) e
  refine ⟨_, hM', ?_, ?_, hR', fun x hx hn => ?_, fun j hj => ?_⟩
  · refine hRO.insN hM.nodup hs dG (fun y hy => ek y ((hM.members y).1 hy).1 (fun e => dG (e ▸ hy)))
      (by rw [hsrc1]; exact hns) (fun kd y hy ky hc => ?_)
    rw [ed] at hc
    have hyO : y ∈ OS := ((hM.members y).1 hy).1
    have pe := ptrA_of_cls hc.symm
    by_cases hyd : ∃ j, j < i ∧ y = dslot j
    · obtain ⟨j, hj, rfl⟩ := hyd
      rw [h2 j hj] at pe
      exact hfn j i (by omega) hi (by omega) pe
    · have hyn : ∀ j, j < i → y ≠ dslot j := fun j hj e => hyd ⟨j, hj, e⟩
      rw [h1 y hyO hyn] at ky pe
      exact hfo i hi y hyO ky pe.symm
  · refine (hM'.members src).2 ⟨hsOS, ?_⟩
    rw [ek src hsOS hsd]; exact ((hM.members src).1 hs).2
  · rw [ek x hx (hn i (by omega))]; exact h1 x hx fun j hj => hn j (by omega)
  · by_cases hji : j = i
    · subst hji; exact ed
    · rw [ek _ (hdO j (by omega)) (fun e => hji (hinj j i (by omega) hi e))]; exact h2 j (by omega)

end loopk

/-! ## Retype (no reset) -/

theorem bjA_inj {base z : U64} {w : Nat} (hfit : base.val + w * 2 ^ z.val ≤ 2 ^ 64) {j l : Nat} (hj : j < w)
    (hl : l < w) (e : bjA base z j = bjA base z l) : j = l := by
  have hk1 : 1 ≤ 2 ^ z.val := Nat.one_le_two_pow
  have a1 : (j + 1) * 2 ^ z.val ≤ w * 2 ^ z.val := Nat.mul_le_mul_right _ hj
  have a2 : (l + 1) * 2 ^ z.val ≤ w * 2 ^ z.val := Nat.mul_le_mul_right _ hl
  rw [Nat.add_mul, Nat.one_mul] at a1 a2
  have v := congrArg UScalar.val e
  rw [bjA_val (base := base) (z := z) (j := j) (by omega), bjA_val (base := base) (z := z) (j := l) (by omega)] at v
  exact Nat.eq_of_mul_eq_mul_right (by omega) (by omega : j * 2 ^ z.val = l * 2 ^ z.val)

theorem rngKey_ut {p b i : U64} {d : Bool} : ¬ RngKeyA (.Untyped p b i d) := fun h => by
  have := h.2.1; simp [isUtA] at this

/-- **A pairwise key-cap property after retype** (gen 60: the common end of `rkG` (`KindA`, `f := kindA`) and
`nlG` (`ClsA`, `f := clsA`)): two key caps of one base agree on `f` — two new caps of one base are one cap
(`hfn`), a new cap's base is no old key cap's (`hfo`), old key slots hold their old caps (`old`). -/
theorem keyPairA {β : Type _} (f : capability.Cap → β) {OS : Set U64} {s0 sf : S} {w : Nat} {dslot : Nat → U64}
    {cj : Nat → capability.Cap} (hnew : ∀ j, j < w → capA st sf (dslot j) = cj j)
    (old : ∀ y ∈ OS, (∀ l, l < w → y ≠ dslot l) → RngKeyA (capA st sf y) → capA st sf y = capA st s0 y)
    (hfn : ∀ j l, j < w → l < w → j ≠ l → ptrA (cj l) ≠ ptrA (cj j))
    (hfo : ∀ j, j < w → ∀ x ∈ OS, RngKeyA (capA st s0 x) → ptrA (capA st s0 x) ≠ ptrA (cj j))
    (h0 : ∀ x ∈ OS, ∀ y ∈ OS, RngKeyA (capA st s0 x) → RngKeyA (capA st s0 y) →
      ptrA (capA st s0 x) = ptrA (capA st s0 y) → f (capA st s0 x) = f (capA st s0 y)) :
    ∀ x ∈ OS, ∀ y ∈ OS, RngKeyA (capA st sf x) → RngKeyA (capA st sf y) →
      ptrA (capA st sf x) = ptrA (capA st sf y) → f (capA st sf x) = f (capA st sf y) := by
  intro x hx y hy kx ky hp
  by_cases hxd : ∃ j, j < w ∧ x = dslot j
  · obtain ⟨j, hj, rfl⟩ := hxd
    by_cases hyd : ∃ l, l < w ∧ y = dslot l
    · obtain ⟨l, hl, rfl⟩ := hyd
      rw [hnew j hj, hnew l hl] at hp ⊢
      by_cases hjl : j = l
      · subst hjl; rfl
      · exact absurd hp.symm (hfn j l hj hl hjl)
    · have hyn : ∀ l, l < w → y ≠ dslot l := fun l hl e => hyd ⟨l, hl, e⟩
      have ey := old y hy hyn ky
      rw [ey] at hp ky
      rw [hnew j hj] at hp
      exact absurd hp.symm (hfo j hj y hy ky)
  · have hxn : ∀ l, l < w → x ≠ dslot l := fun l hl e => hxd ⟨l, hl, e⟩
    have ex := old x hx hxn kx
    by_cases hyd : ∃ l, l < w ∧ y = dslot l
    · obtain ⟨l, hl, rfl⟩ := hyd
      rw [ex] at hp kx
      rw [hnew l hl] at hp
      exact absurd hp (hfo l hl x hx kx)
    · have hyn : ∀ l, l < w → y ≠ dslot l := fun l hl e => hyd ⟨l, hl, e⟩
      have ey := old y hy hyn ky
      rw [ex] at hp kx ⊢
      rw [ey] at hp ky ⊢
      exact h0 x hx y hy kx ky hp

set_option maxHeartbeats 4000000 in
/-- **Retype (no reset) keeps `RngOneA64`, `KindA` and `UtRev`, with an extra invariant** (gen 60: the common
proof of gen 56's `untyped.retype.rk` (`Zq := fun _ _ => True`) and gen 59's `rkZ`): `LoopK` along
`untyped.retype.genJK`. -/
theorem untyped.retype.rkG {A : Type _} (ar : machine.Arch A) {OS : Set U64} (hO : OSOK T Ω Sg OS)
    {G : List (List U64)} {par : U64 → Option U64} {s : S} (hT : TreeA st OS G par s) (hRO : RngOneA64 st G s)
    (hK : KindA st OS s) (hR : UtRev st OS s) (a : A)
    {src p sb fi : U64} {dev : Bool} (hsrc : src ∈ OS) (hcs : capA st s src = .Untyped p sb fi dev)
    (nt us dcn off len base : U64) (device : Bool) (hn : nt.val < 15) (hz : (zA nt.val us).val < 64)
    (hfi : fi.val < 2 ^ sb.val) (hA : p.val + fi.val ≤ base.val)
    (hAw : base.val + len.val * 2 ^ (zA nt.val us).val ≤ p.val + 2 ^ sb.val)
    {Zq : S → Nat → Prop}
    (hCOZ : ∀ (s' : S) (a' : A) (j : Nat), j < len.val → Zq s' j →
      objects.create_object st ar s' a' nt (bjA base (zA nt.val us) j) us device ⦃ r =>
        r.1 = newCapA nt.val (bjA base (zA nt.val us) j) us device ∧ OSKeep st OS s' r.2.1 ∧ Zq r.2.1 (j + 1) ⦄)
    (hZW : ∀ (s1 s2 : S) (j : Nat), Zq s1 j → WritesIn st s1 s2 (W7.CapW T Ω Sg) → Zq s2 j)
    (hZ0 : ∀ s1 : S, WritesIn st s s1 (fun b => b = src ∨ b = wa src 8#u64) → Zq s1 0)
    (hdO : ∀ j, j < len.val → djA dcn off j ∈ OS)
    (hdn : ∀ j, j < len.val → capA st s (djA dcn off j) = .Null)
    (hdc : ∀ j, j < len.val → obj.sext48 (djA dcn off j) = ok (djA dcn off j))
    (hinj : ∀ j l, j < len.val → l < len.val → djA dcn off j = djA dcn off l → j = l)
    (hcan : ∀ j, j < len.val → CapRt.Canonical (bjA base (zA nt.val us) j)) (hus : us.val < 64) :
    untyped.retype st ar s a src false base nt us dcn off len device ⦃ r => r.1 = .Ok () ∧
      (∃ G' : List (List U64), MdbLk st OS G' r.2.1 ∧ RngOneA64 st G' r.2.1 ∧ KindA st OS r.2.1 ∧
        UtRev st OS r.2.1) ∧ Zq r.2.1 len.val ⦄ := by
  have hU := hT.ut
  have hM := hT.lk
  have hF := hU.freeFresh
  set z := zA nt.val us with hzdef
  have hk1 : 1 ≤ 2 ^ z.val := Nat.one_le_two_pow
  have hsb : 2 ^ sb.val < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (capA_ut_b hcs)
  obtain ⟨-, -, hpfit⟩ := ut_rangeA (capA_ut_b hcs) (by
    have := hU.reg src hsrc (by rw [hcs]; exact physA_ut _ _ _ _); rwa [hcs] at this)
  have hs0 : capA st s src ≠ .Null := by rw [hcs]; exact fun h => by cases h
  have hsG : src ∈ G.flatten := (hM.members src).2 ⟨hsrc, hs0⟩
  have hsn : ∀ j, j < len.val → src ≠ djA dcn off j := fun j hj e => hs0 (by rw [e]; exact hdn j hj)
  have hOS : ∀ x ∈ G.flatten, x ∈ OS := fun x hx => ((hM.members x).1 hx).1
  have hbj : ∀ j, j < len.val → (bjA base z j).val = base.val + j * 2 ^ z.val := fun j hj => by
    have : (j + 1) * 2 ^ z.val ≤ len.val * 2 ^ z.val := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, Nat.one_mul] at this
    exact bjA_val (by omega)
  have hfn : ∀ j l, j < len.val → l < len.val → j ≠ l →
      ptrA (newCapA nt.val (bjA base z l) us device) ≠ ptrA (newCapA nt.val (bjA base z j) us device) := by
    intro j l hj hl hjl e
    rw [newCapA_ptr, newCapA_ptr] at e
    exact hjl (bjA_inj (by omega) hl hj e).symm
  have hwf : ∀ j, j < len.val → CapRt.EncWf (newCapA nt.val (bjA base z j) us device) := fun j hj =>
    newCapA_encWf _ _ _ _ (hcan j hj) hus
  have hfit : base.val + len.val * 2 ^ z.val ≤ 2 ^ 64 := by omega
  -- what the source's rewrite keeps (`s1` any state `RtSrc`)
  have D : ∀ s1, RtSrc st s src p sb dev base.val (base.val + len.val * 2 ^ z.val) s1 →
      (∀ x ∈ OS, (RngKeyA (capA st s1 x) ↔ RngKeyA (capA st s x)) ∧
        (RngKeyA (capA st s x) → capA st s1 x = capA st s x)) ∧
      ¬ RngKeyA (capA st s1 src) ∧ (∀ j, j < len.val → capA st s1 (djA dcn off j) = .Null) ∧
      MdbLk st OS G s1 ∧ RngOneA64 st G s1 ∧ UtRev st OS s1 ∧
      WritesIn st s s1 (fun b => b = src ∨ b = wa src 8#u64) := fun s1 h1 => by
    obtain ⟨nfi, -, hcs1, hc1, hl1, hW⟩ := h1.facts hO hsrc
    have hkey1 : ∀ x ∈ OS, (RngKeyA (capA st s1 x) ↔ RngKeyA (capA st s x)) ∧
        (RngKeyA (capA st s x) → capA st s1 x = capA st s x) := fun x hx => by
      by_cases e : x = src
      · rw [e, hcs1, hcs]; exact ⟨⟨fun k => absurd k rngKey_ut, fun k => absurd k rngKey_ut⟩,
          fun k => absurd k rngKey_ut⟩
      · rw [hc1 x hx e]; exact ⟨Iff.rfl, fun _ => rfl⟩
    refine ⟨hkey1, by rw [hcs1]; exact rngKey_ut, fun j hj => ?_, h1.lk hO hsrc hM hs0,
      hRO.keep fun x hx => ⟨(hkey1 x (hOS x hx)).1, fun k => by rw [(hkey1 x (hOS x hx)).2 k]⟩, ?_, hW⟩
    · rw [hc1 _ (hdO j hj) (fun e => hsn j hj e.symm)]; exact hdn j hj
    · intro u hu hc
      rw [revocable_congr (hl1 u hu).2]
      by_cases e : u = src
      · rw [e]; exact hR src hsrc (by rw [hcs]; rfl)
      · rw [hc1 u hu e] at hc; exact hR u hu hc
  have hfo : ∀ s1, RtSrc st s src p sb dev base.val (base.val + len.val * 2 ^ z.val) s1 →
      ∀ j, j < len.val → ∀ x ∈ OS, RngKeyA (capA st s1 x) →
      ptrA (capA st s1 x) ≠ ptrA (newCapA nt.val (bjA base z j) us device) := by
    intro s1 h1 j hj x hx kx e
    have hkey1 := (D s1 h1).1
    rw [newCapA_ptr] at e
    have k0 := (hkey1 x hx).1.1 kx
    rw [(hkey1 x hx).2 k0] at e
    have jk : (j + 1) * 2 ^ z.val ≤ len.val * 2 ^ z.val := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, Nat.one_mul] at jk
    refine hF.fresh src hsrc p sb fi dev hcs x hx k0 ⟨?_, ?_⟩ <;> rw [e, hbj j hj] <;> omega
  refine WP.spec_mono (untyped.retype.genJK ar a hcs nt us dcn off len base device hn hz hfit
    (J := fun s1 s' i => LoopK st OS s1 src (djA dcn off) (fun j => newCapA nt.val (bjA base z j) us device) s' i ∧
      Zq s' i)
    (K := fun s1 s' i => LoopK st OS s1 src (djA dcn off) (fun j => newCapA nt.val (bjA base z j) us device) s' i ∧
      Zq s' (i + 1))
    (fun _ _ s' a' j hj h => WP.spec_mono (hCOZ s' a' j hj h.2) fun r hr =>
      ⟨hr.1, h.1.keep (fun l hl => hdO l (by omega)) hr.2.1, hr.2.2⟩)
    (fun s1 h1 s' i hi h => spec_andL
      (LoopK.step hO hi h.1 hdO (D s1 h1).2.2.1 hdc hinj hsn hwf (fun j _ => newCapA_ne _ _ _ _) (D s1 h1).2.1
        (hfo s1 h1) hfn)
      (cdt.insert_new_cap.zqW hO hZW (hdO i hi)
        (by obtain ⟨G1, hM1, -, hs1, -⟩ := h.1; exact MdbLk.nxG hO hM1 hs1) h.2))
    (fun s1 h1 => ⟨LoopK.start (D s1 h1).2.2.2.1 (D s1 h1).2.2.2.2.1 hsG (D s1 h1).2.2.2.2.2.1,
      hZ0 s1 (D s1 h1).2.2.2.2.2.2⟩)) ?_
  rintro r ⟨hok, s1, h1, ⟨G', hM', hRO', -, hR', hF2b, hF2a⟩, hZf⟩
  have hkey1 := (D s1 h1).1
  have hK1 : KindA st OS s1 := hK.keep fun x hx =>
    ⟨(hkey1 x hx).1, fun k => by rw [(hkey1 x hx).2 k]; exact ⟨rfl, rfl⟩⟩
  have hfo1 := hfo s1 h1
  exact ⟨hok, ⟨G', hM', hRO', ⟨keyPairA kindA hF2a (fun y hy hyn _ => hF2b y hy hyn) hfn hfo1 hK1.kind⟩, hR'⟩, hZf⟩

/-- **`untyped::retype` without reset keeps `RngOneA64`, `KindA` and `UtRev`** (module docstring; the hypotheses
of `untyped.retype.tree`). -/
theorem untyped.retype.rk {A : Type _} (ar : machine.Arch A) {OS : Set U64} (hO : OSOK T Ω Sg OS)
    {G : List (List U64)} {par : U64 → Option U64} {s : S} (hT : TreeA st OS G par s) (hRO : RngOneA64 st G s)
    (hK : KindA st OS s) (hR : UtRev st OS s) (a : A)
    {src p sb fi : U64} {dev : Bool} (hsrc : src ∈ OS) (hcs : capA st s src = .Untyped p sb fi dev)
    (nt us dcn off len base : U64) (device : Bool) (hn : nt.val < 15) (hz : (zA nt.val us).val < 64)
    (hfi : fi.val < 2 ^ sb.val) (hA : p.val + fi.val ≤ base.val)
    (hAw : base.val + len.val * 2 ^ (zA nt.val us).val ≤ p.val + 2 ^ sb.val)
    (hCO : ∀ (s' : S) (a' : A) (j : Nat), j < len.val →
      objects.create_object st ar s' a' nt (bjA base (zA nt.val us) j) us device ⦃ r =>
        r.1 = newCapA nt.val (bjA base (zA nt.val us) j) us device ∧ OSKeep st OS s' r.2.1 ⦄)
    (hdO : ∀ j, j < len.val → djA dcn off j ∈ OS)
    (hdn : ∀ j, j < len.val → capA st s (djA dcn off j) = .Null)
    (hdc : ∀ j, j < len.val → obj.sext48 (djA dcn off j) = ok (djA dcn off j))
    (hinj : ∀ j l, j < len.val → l < len.val → djA dcn off j = djA dcn off l → j = l)
    (hcan : ∀ j, j < len.val → CapRt.Canonical (bjA base (zA nt.val us) j)) (hus : us.val < 64) :
    untyped.retype st ar s a src false base nt us dcn off len device ⦃ r => r.1 = .Ok () ∧
      ∃ G' : List (List U64), MdbLk st OS G' r.2.1 ∧ RngOneA64 st G' r.2.1 ∧ KindA st OS r.2.1 ∧
        UtRev st OS r.2.1 ⦄ :=
  WP.spec_mono (untyped.retype.rkG ar hO hT hRO hK hR a hsrc hcs nt us dcn off len base device hn hz hfi hA hAw
    (Zq := fun _ _ => True) (fun s' a' j hj _ => WP.spec_mono (hCO s' a' j hj) fun r h => ⟨h.1, h.2, trivial⟩)
    (fun _ _ _ _ _ => trivial) (fun _ _ => trivial) hdO hdn hdc hinj hcan hus) fun _ h => ⟨h.1, h.2.1⟩

/-- **Retype (no reset) keeps the tree, `RngOneA64`, `KindA` and `UtRev` on one ghost** (`untyped.retype.tree`
and `untyped.retype.rk`, the two ghosts aligned by `MdbLk.chains_iff`). -/
theorem untyped.retype.treeK {A : Type _} (ar : machine.Arch A) {OS : Set U64} (hO : OSOK T Ω Sg OS)
    {G : List (List U64)} {par : U64 → Option U64} {s : S} (hT : TreeA st OS G par s) (hRO : RngOneA64 st G s)
    (hK : KindA st OS s) (hR : UtRev st OS s) (a : A)
    {src p sb fi : U64} {dev : Bool} (hsrc : src ∈ OS) (hcs : capA st s src = .Untyped p sb fi dev)
    (nt us dcn off len base : U64) (device : Bool) (hn : nt.val < 15) (hz : (zA nt.val us).val < 64)
    (hfi : fi.val < 2 ^ sb.val) (hA : p.val + fi.val ≤ base.val)
    (hAw : base.val + len.val * 2 ^ (zA nt.val us).val ≤ p.val + 2 ^ sb.val)
    (hCO : ∀ (s' : S) (a' : A) (j : Nat), j < len.val →
      objects.create_object st ar s' a' nt (bjA base (zA nt.val us) j) us device ⦃ r =>
        r.1 = newCapA nt.val (bjA base (zA nt.val us) j) us device ∧ OSKeep st OS s' r.2.1 ⦄)
    (hdO : ∀ j, j < len.val → djA dcn off j ∈ OS)
    (hdn : ∀ j, j < len.val → capA st s (djA dcn off j) = .Null)
    (hdc : ∀ j, j < len.val → obj.sext48 (djA dcn off j) = ok (djA dcn off j))
    (hinj : ∀ j l, j < len.val → l < len.val → djA dcn off j = djA dcn off l → j = l)
    (hcan : ∀ j, j < len.val → CapRt.Canonical (bjA base (zA nt.val us) j)) (hus : us.val < 64) :
    untyped.retype st ar s a src false base nt us dcn off len device ⦃ r => r.1 = .Ok () ∧
      ∃ G' : List (List U64), ∃ par' : U64 → Option U64, TreeA st OS G' par' r.2.1 ∧ RngOneA64 st G' r.2.1 ∧
        KindA st OS r.2.1 ∧ UtRev st OS r.2.1 ⦄ := by
  refine WP.spec_mono (spec_andA
    (untyped.retype.tree ar hO hT a hsrc hcs nt us dcn off len base device hn hz hfi hA hAw hCO hdO hdn hdc hinj
      hcan hus)
    (untyped.retype.rk ar hO hT hRO hK hR a hsrc hcs nt us dcn off len base device hn hz hfi hA hAw hCO hdO hdn
      hdc hinj hcan hus)) ?_
  rintro r ⟨⟨hok, G1, par1, hT1⟩, -, G2, hM2, hRO2, hK2, hR2⟩
  exact ⟨hok, G1, par1, hT1, hRO2.congr (hM2.chains_iff hT1.lk hO.nz), hK2, hR2⟩

/-! ## `UtRev` along `insert_with_cap` -/

section iwc
variable {OS : Set U64}

/-- `set_next_flags` with any `revocable`: bit 48 set when it is `true`. -/
theorem set_nf_rv (s : S) (x n : U64) (r f : Bool) :
    obj.Slot.set_next_flags st x s n r f ⦃ s' => ∃ w, s' = L.wr s (wa x 24#u64) w ∧
      (r = true → w &&& RVB = RVB) ⦄ := by
  cases r
  · refine WP.spec_mono (set_nf_spec s x n false f) ?_
    rintro s' ⟨w, h, -⟩; exact ⟨w, h, fun e => by cases e⟩
  · refine WP.spec_mono (set_nf_rvb s x n f) ?_
    rintro s' ⟨w, h, h'⟩; exact ⟨w, h, fun _ => h'⟩

/-- `set_untyped_cap_as_full` leaves the state or rewrites `src`'s two cap words. -/
theorem cdt.set_untyped_cap_as_full.w2 {s : S} {src : U64} {sc nc : capability.Cap} (hsc : capA st s src = sc) :
    cdt.set_untyped_cap_as_full st s sc nc src ⦃ s1 => s1 = s ∨
      ∃ w0 w1, s1 = L.wr (L.wr s src w0) (wa src 8#u64) w1 ⦄ := by
  have hd : capability.Cap.decode (L.mem s src) (L.mem s (wa src 8#u64)) = ok sc := by
    have e := capA_eq (st := st) s src; rw [DPF.slot_cap_dec, hsc] at e; exact e
  cases sc with
  | Untyped p b i d =>
    cases nc with
    | Untyped p' b' i' d' =>
      simp only [cdt.set_untyped_cap_as_full]
      by_cases e1 : p = p'
      · rw [if_pos e1]
        by_cases e2 : b = b'
        · rw [if_pos e2]
          simp only [lift, bind_ok]
          have wf0 := CapRt.decode_encWf hd
          have hb : b.val < 64 := wf0.2
          refine WP.spec_bind (shl1_val hb) fun i1 _ => ?_
          have wf : CapRt.EncWf (.Untyped p b i1 d) := wf0
          obtain ⟨w0, w1, he, -⟩ := CapRt.decode_encode _ wf
          rw [set_cap_eq he, WP.spec_ok]
          exact Or.inr ⟨w0, w1, rfl⟩
        · rw [if_neg e2]; exact (WP.spec_ok _).2 (Or.inl rfl)
      · rw [if_neg e1]; exact (WP.spec_ok _).2 (Or.inl rfl)
    | _ => exact (WP.spec_ok _).2 (Or.inl rfl)
  | _ => exact (WP.spec_ok _).2 (Or.inl rfl)

theorem is_cap_revocable_ut {nc sc : capability.Cap} {rv : Bool} (h : objects.is_cap_revocable nc sc = ok rv)
    (hu : isUtA nc = true) : rv = true := by
  obtain ⟨p, b, i, e, rfl⟩ := isUtA_ex hu
  have : objects.is_cap_revocable (.Untyped p b i e) sc = ok true := rfl
  rw [this] at h; exact (okinj h).symm

set_option maxHeartbeats 1000000 in
/-- **`insert_with_cap` and bit 48**: every `OS` slot but `dest` keeps it, `dest` gets it when the new cap is an
`Untyped` (`is_cap_revocable`, objects.rs:186–198). -/
theorem cdt.insert_with_cap.rvb (hO : OSOK T Ω Sg OS) {s : S} {src dest : U64} {nc sc : capability.Cap}
    (hsrc : src ∈ OS) (hd : dest ∈ OS) (hsd : src ≠ dest) (hsc : capA st s src = sc) (hw : CapRt.EncWf nc)
    (hnN : NxA st s src ≠ 0#u64 → NxA st s src ∈ OS) :
    cdt.insert_with_cap st s nc sc src dest ⦃ s' =>
      (∀ y ∈ OS, y ≠ dest → L.mem s' (wa y 24#u64) &&& RVB = L.mem s (wa y 24#u64) &&& RVB) ∧
      (isUtA nc = true → L.mem s' (wa dest 24#u64) &&& RVB = RVB) ⦄ := by
  unfold cdt.insert_with_cap
  obtain ⟨rv, hrv, -⟩ := spec_exA (P0.objects.is_cap_revocable.p0 nc sc)
  rw [hrv, bind_ok, next_eq, bind_ok]
  refine WP.spec_bind (cdt.set_untyped_cap_as_full.w2 (nc := nc) hsc) fun s1 h1 => ?_
  have K1 : ∀ y ∈ OS, L.mem s1 (wa y 24#u64) = L.mem s (wa y 24#u64) := by
    rcases h1 with rfl | ⟨w0, w1, rfl⟩
    · exact fun _ _ => rfl
    · exact fun y hy => (set_cap_links hO hsrc y hy).2
  obtain ⟨w0, w1, he, -⟩ := CapRt.decode_encode nc hw
  rw [set_cap_eq he, bind_ok]
  have K2 : ∀ y ∈ OS, L.mem (L.wr (L.wr s1 dest w0) (wa dest 8#u64) w1) (wa y 24#u64) = L.mem s (wa y 24#u64) :=
    fun y hy => (set_cap_links hO hd y hy).2.trans (K1 y hy)
  generalize L.wr (L.wr s1 dest w0) (wa dest 8#u64) w1 = s2 at K2 ⊢
  rw [set_prev_eq, bind_ok]
  have K3 : ∀ y ∈ OS, L.mem (L.wr s2 (wa dest 16#u64) src) (wa y 24#u64) = L.mem s (wa y 24#u64) :=
    fun y hy => (w24_wr16 hO s2 hd hy src).trans (K2 y hy)
  generalize L.wr s2 (wa dest 16#u64) src = s3 at K3 ⊢
  refine WP.spec_bind (set_nf_rv s3 dest _ rv rv) ?_
  rintro s4 ⟨w4, rfl, hw4⟩
  rw [set_next_eq, bind_ok]
  have K5 : ∀ y ∈ OS, y ≠ dest → L.mem (L.wr (L.wr s3 (wa dest 24#u64) w4) (wa src 24#u64)
      ((L.mem (L.wr s3 (wa dest 24#u64) w4) (wa src 24#u64) &&& ~~~ obj.MDB_PTR_MASK) |||
        (dest &&& obj.MDB_PTR_MASK))) (wa y 24#u64) &&& RVB = L.mem s (wa y 24#u64) &&& RVB := by
    intro y hy e
    by_cases ys : y = src
    · rw [ys, w24_self hO _ hsrc, ptr_rvb, w24_wr24 hO s3 hd hsrc hsd, K3 src hsrc]
    · rw [w24_wr24 hO _ hsrc hy ys, w24_wr24 hO s3 hd hy e, K3 y hy]
  have D5 : isUtA nc = true → L.mem (L.wr (L.wr s3 (wa dest 24#u64) w4) (wa src 24#u64)
      ((L.mem (L.wr s3 (wa dest 24#u64) w4) (wa src 24#u64) &&& ~~~ obj.MDB_PTR_MASK) |||
        (dest &&& obj.MDB_PTR_MASK))) (wa dest 24#u64) &&& RVB = RVB := fun hu => by
    rw [w24_wr24 hO _ hsrc hd hsd.symm, w24_self hO s3 hd]; exact hw4 (is_cap_revocable_ut hrv hu)
  generalize L.wr (L.wr s3 (wa dest 24#u64) w4) (wa src 24#u64) _ = s5 at K5 D5 ⊢
  simp only [obj.Slot.is_null, bind_ok]
  split
  · exact (WP.spec_ok _).2 ⟨K5, D5⟩
  · rename_i hn0
    have hN0 : NxA st s src ≠ 0#u64 := by simpa using hn0
    rw [set_prev_eq, WP.spec_ok]
    exact ⟨fun y hy e => by rw [w24_wr16 hO s5 (hnN hN0) hy]; exact K5 y hy e,
      fun hu => by rw [w24_wr16 hO s5 (hnN hN0) hd]; exact D5 hu⟩

theorem revocable_of_bit {s s' : S} {u : U64} (h : obj.Slot.revocable st u s = ok true)
    (e : L.mem s' (wa u 24#u64) &&& RVB = L.mem s (wa u 24#u64) &&& RVB) : obj.Slot.revocable st u s' = ok true := by
  rw [revocable_eqA] at h ⊢; rw [e]; exact h

/-- **`insert_with_cap` keeps `UtRev`** (the source stays revocable, a new `Untyped` gets the bit). -/
theorem cdt.insert_with_cap.utRev (hO : OSOK T Ω Sg OS) {s : S} (hR : UtRev st OS s) {src dest : U64}
    {nc sc : capability.Cap} (hsrc : src ∈ OS) (hd : dest ∈ OS) (hsd : src ≠ dest) (hdc : obj.sext48 dest = ok dest)
    (hsc : capA st s src = sc) (hsc0 : sc ≠ .Null) (hw : CapRt.EncWf nc)
    (hnN : NxA st s src ≠ 0#u64 → NxA st s src ∈ OS) :
    cdt.insert_with_cap st s nc sc src dest ⦃ s' => UtRev st OS s' ⦄ := by
  refine WP.spec_mono (WP.spec_and (WP.spec_and (cdt.insert_with_cap.lr hO (LR.self s) hsrc hd hsd hdc hsc hsc0 hw hnN)
    (cdt.insert_with_cap.srcU hO hsrc hd hsd hsc hw hnN)) (cdt.insert_with_cap.rvb hO hsrc hd hsd hsc hw hnN)) ?_
  rintro s' ⟨⟨⟨-, ed, -, -, ek, -⟩, hsu⟩, hb, hdb⟩
  intro u hu hc
  by_cases e1 : u = dest
  · rw [e1, revocable_eqA, hdb (by rw [← ed, ← e1]; exact hc)]; first | rfl | decide | simp
  · by_cases e2 : u = src
    · rw [e2] at hc ⊢
      have hus : isUtA sc = true := by
        rcases hsu.1 with e | ⟨p, b, i, d, i1, hc', -, -⟩
        · rw [← e]; exact hc
        · rw [hc']; rfl
      exact revocable_of_bit (hR src hsrc (by rw [hsc]; exact hus)) (hb src hsrc hsd)
    · rw [ek u hu e2 e1] at hc
      exact revocable_of_bit (hR u hu hc) (hb u hu e1)

end iwc

/-! ## `UtRev` along `move_cap` -/

section mv
variable {OS : Set U64}

/-- A `set_next` keeps bit 48 of every `OS` slot's `NEXT` word. -/
theorem bit_next (hO : OSOK T Ω Sg OS) (s : S) {p y : U64} (hp : p ∈ OS) (hy : y ∈ OS) (n : U64) :
    L.mem (L.wr s (wa p 24#u64) ((L.mem s (wa p 24#u64) &&& ~~~ obj.MDB_PTR_MASK) ||| (n &&& obj.MDB_PTR_MASK)))
      (wa y 24#u64) &&& RVB = L.mem s (wa y 24#u64) &&& RVB := by
  by_cases e : y = p
  · rw [e, w24_self hO s hp, ptr_rvb]
  · rw [w24_wr24 hO s hp hy e]

set_option maxHeartbeats 2000000 in
/-- **`move_cap` and bit 48** (cdt.rs:49–64): `dest` gets the source's bit (`set_next_flags … revocable …`),
every other slot but the (cleared) source keeps its own. -/
theorem cdt.move_cap.rvb (hO : OSOK T Ω Sg OS) {s : S} {src dest : U64} {nc : capability.Cap}
    (hsrc : src ∈ OS) (hd : dest ∈ OS) (hsd : src ≠ dest) (hw : CapRt.EncWf nc)
    (hpP : L.mem s (wa src 16#u64) ≠ 0#u64 → L.mem s (wa src 16#u64) ∈ OS)
    (hnN : NxA st s src ≠ 0#u64 → NxA st s src ∈ OS) :
    cdt.move_cap st s nc src dest ⦃ s' =>
      (∀ y ∈ OS, y ≠ src → y ≠ dest → L.mem s' (wa y 24#u64) &&& RVB = L.mem s (wa y 24#u64) &&& RVB) ∧
      (((L.mem s (wa src 24#u64) &&& RVB) != 0#u64) = true → L.mem s' (wa dest 24#u64) &&& RVB = RVB) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.move_cap
  rw [slot_prev_eq s src, bind_ok, next_eq, bind_ok, revocable_eqA, bind_ok]
  refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st src s hS) fun f1 _ => ?_
  obtain ⟨w0, w1, he, -⟩ := CapRt.decode_encode nc hw
  rw [set_cap_eq he, bind_ok]
  have K1 : ∀ y ∈ OS, L.mem (L.wr (L.wr s dest w0) (wa dest 8#u64) w1) (wa y 24#u64) = L.mem s (wa y 24#u64) :=
    fun y hy => (set_cap_links hO hd y hy).2
  generalize L.wr (L.wr s dest w0) (wa dest 8#u64) w1 = s1 at K1 ⊢
  rw [set_prev_eq, bind_ok]
  have K2 : ∀ y ∈ OS, L.mem (L.wr s1 (wa dest 16#u64) (L.mem s (wa src 16#u64))) (wa y 24#u64) =
      L.mem s (wa y 24#u64) := fun y hy => (w24_wr16 hO s1 hd hy _).trans (K1 y hy)
  generalize L.wr s1 (wa dest 16#u64) (L.mem s (wa src 16#u64)) = s2 at K2 ⊢
  refine WP.spec_bind (set_nf_rv s2 dest _ _ f1) ?_
  rintro s3 ⟨w3, rfl, hw3⟩
  have K3 : ∀ y ∈ OS, y ≠ dest → L.mem (L.wr s2 (wa dest 24#u64) w3) (wa y 24#u64) = L.mem s (wa y 24#u64) :=
    fun y hy e => (w24_wr24 hO s2 hd hy e w3).trans (K2 y hy)
  have D3 : ((L.mem s (wa src 24#u64) &&& RVB) != 0#u64) = true →
      L.mem (L.wr s2 (wa dest 24#u64) w3) (wa dest 24#u64) &&& RVB = RVB := fun h => by
    rw [w24_self hO s2 hd]; exact hw3 h
  generalize L.wr s2 (wa dest 24#u64) w3 = s3 at K3 D3 ⊢
  rw [clear_eq, bind_ok]
  have K4 : ∀ y ∈ OS, y ≠ src → L.mem (L.wr (L.wr (L.wr (L.wr s3 src 0#u64) (wa src 8#u64) 0#u64)
      (wa src 16#u64) 0#u64) (wa src 24#u64) 0#u64) (wa y 24#u64) = L.mem s3 (wa y 24#u64) := fun y hy e => by
    rw [w24_wr24 hO _ hsrc hy e, w24_wr16 hO _ hsrc hy, (set_cap_links hO hsrc y hy).2]
  generalize L.wr (L.wr (L.wr (L.wr s3 src 0#u64) (wa src 8#u64) 0#u64) (wa src 16#u64) 0#u64)
    (wa src 24#u64) 0#u64 = s4 at K4 ⊢
  simp only [obj.Slot.is_null, bind_ok]
  refine WP.spec_bind (Pₘ := fun s5 => ∀ y ∈ OS, L.mem s5 (wa y 24#u64) &&& RVB = L.mem s4 (wa y 24#u64) &&& RVB)
    ?_ fun s5 h5 => ?_
  · split
    · exact (WP.spec_ok _).2 fun _ _ => rfl
    · rename_i hp0
      have hP0 : L.mem s (wa src 16#u64) ≠ 0#u64 := by simpa using hp0
      rw [set_next_eq, WP.spec_ok]
      exact fun y hy => bit_next hO s4 (hpP hP0) hy dest
  have fin : ∀ s6 : S, (∀ y ∈ OS, L.mem s6 (wa y 24#u64) = L.mem s5 (wa y 24#u64)) →
      (∀ y ∈ OS, y ≠ src → y ≠ dest → L.mem s6 (wa y 24#u64) &&& RVB = L.mem s (wa y 24#u64) &&& RVB) ∧
      (((L.mem s (wa src 24#u64) &&& RVB) != 0#u64) = true → L.mem s6 (wa dest 24#u64) &&& RVB = RVB) :=
    fun s6 h6 => ⟨fun y hy e1 e2 => by rw [h6 y hy, h5 y hy, K4 y hy e1, K3 y hy e2],
      fun h => by rw [h6 dest hd, h5 dest hd, K4 dest hd hsd.symm]; exact D3 h⟩
  split
  · exact (WP.spec_ok _).2 (fin s5 fun _ _ => rfl)
  · rename_i hn0
    have hN0 : NxA st s src ≠ 0#u64 := by simpa using hn0
    rw [set_prev_eq, WP.spec_ok]
    exact fin _ fun y hy => w24_wr16 hO s5 (hnN hN0) hy dest

/-- **`move_cap` keeps `UtRev`** when a moved `Untyped` comes from an `Untyped` slot (`UA.isut`). -/
theorem cdt.move_cap.utRev (hO : OSOK T Ω Sg OS) {s : S} (hR : UtRev st OS s) {src dest : U64}
    {nc : capability.Cap} (hsrc : src ∈ OS) (hd : dest ∈ OS) (hsd : src ≠ dest) (hdc : obj.sext48 dest = ok dest)
    (hw : CapRt.EncWf nc) (hpP : L.mem s (wa src 16#u64) ≠ 0#u64 → L.mem s (wa src 16#u64) ∈ OS)
    (hnN : NxA st s src ≠ 0#u64 → NxA st s src ∈ OS) (hu : isUtA nc = true → isUtA (capA st s src) = true) :
    cdt.move_cap st s nc src dest ⦃ s' => UtRev st OS s' ⦄ := by
  refine WP.spec_mono (WP.spec_and (cdt.move_cap.lr hO (LR.self s) hsrc hd hsd hdc hw hpP hnN)
    (cdt.move_cap.rvb hO hsrc hd hsd hw hpP hnN)) ?_
  rintro s' ⟨⟨-, ed, es, ek⟩, hb, hdb⟩
  intro u hu' hc
  by_cases e1 : u = dest
  · rw [e1] at hc ⊢
    rw [ed] at hc
    have r := hR src hsrc (hu hc)
    rw [revocable_eqA] at r
    rw [revocable_eqA, hdb (okinj r)]; first | rfl | decide | simp
  · by_cases e2 : u = src
    · rw [e2, es] at hc; simp [isUtA] at hc
    · rw [ek u hu' e2 e1] at hc
      exact revocable_of_bit (hR u hu' hc) (hb u hu' e2 e1)

end mv

/-! ## `OSOK` of a union -/

/-- **`OSOK` of `OS ∪ N`**: each placed over the same sets, the two apart. -/
theorem OSOK.union {OS N : Set U64} (h1 : OSOK T Ω Sg OS) (h2 : OSOK T Ω Sg N)
    (hap : ∀ x ∈ OS, ∀ y ∈ N, x.val + 32 ≤ y.val ∨ y.val + 32 ≤ x.val) : OSOK T Ω Sg (OS ∪ N) := by
  refine ⟨fun x hx => ((Set.mem_union x OS N).1 hx).elim (h1.slot x) (h2.slot x),
    fun x hx => ((Set.mem_union x OS N).1 hx).elim (h1.fit x) (h2.fit x),
    fun x hx y hy hxy => ?_, fun x hx => ((Set.mem_union x OS N).1 hx).elim (h1.nz x) (h2.nz x)⟩
  rcases (Set.mem_union x OS N).1 hx with hx | hx <;> rcases (Set.mem_union y OS N).1 hy with hy | hy
  · exact h1.disj x hx y hy hxy
  · exact hap x hx y hy
  · exact (hap y hy x hx).symm
  · exact h2.disj x hx y hy hxy

/-- `OSOK` over larger cap-slot word sets (`CapW` monotone: more TCBs, more `Ω` words outside `Sg'`). -/
theorem OSOK.mono {OS : Set U64} {T' Ω' Sg' : Set U64} (h : OSOK T Ω Sg OS)
    (hw : ∀ b, W7.CapW T Ω Sg b → W7.CapW T' Ω' Sg' b) : OSOK T' Ω' Sg' OS :=
  ⟨fun x hx => ⟨(h.slot x hx).1, fun o h1 h2 => hw _ ((h.slot x hx).2 o h1 h2)⟩, h.fit, h.disj, h.nz⟩

end ST
end R
end W7

end

end Fl4ProofsA64.P1
