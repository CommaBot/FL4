/-
P1 (aarch64, gen 47): **`MdbLk ∧ RngOneA64 ∧ KindA` along `cdt::empty_slot`** (cdt.rs:198–215) at function level.

`empty_slot st ar s a x cl` on a slot `x` of `OS` with a non-null cap: `P` = `x`'s `PREV` word, `N` = its `NEXT`;
`set_next(P, N)` if `P ≠ 0`, `set_prev(N, P)` and a first-badged update of `N` if `N ≠ 0`, `clear(x)`, then
`post_cap_deletion(cl)`. The words written are, in order: `P + 24`, `N + 16`, `N + 24`, the four words of `x`.

* `SK s s' y`: slot `y`'s four words equal at `s` and `s'`; `SK.wr` (a write in another `OS` slot keeps it).
* Stage facts: `es_s1` (after `set_next`), `es_s2` (after `set_prev` / first-badged), `es_s3` (after `clear`),
  with `sx_set_next` (the `NEXT` pointer `set_next` stores reads back as the pointer, `link_bits`) and `sx_fb` (a
  first-badged update keeps the pointer, `fb_bits`).
* **`cdt.empty_slot.mdb`**: `∃ G'` with `MdbLk OS G'`, `RngOneA64 G'` and `KindA OS` after (`G' = remG x G`; the
  null-cap path returns the state, `G' = G`). Hypothesis on the cleanup: its `post_cap_deletion` writes only words
  `Pw` outside the `OS` slots (`hpw`), the form `cdt.empty_slot.os` (QueueVsWs) takes; `h0`: no `OS` slot at 0.
* Gen 49: the proof moved (not copied) into **`cdt.empty_slot.mdbF`**, whose post adds the slot frame (other `OS`
  slots keep their caps, other null slots keep their four words, `x` ends null with zero links); `.mdb` is its
  corollary, statement unchanged. `NullLk` / `ClsA` along `empty_slot` (MdbNull) use the frame.
* Gen 53: that proof moved again into **`cdt.empty_slot.mdbFL`**, whose post adds, on the non-null path, the
  `NEXT` facts `MdbLk.rem` consumes (every other `OS` slot but `x`'s `PREV` keeps its `NEXT`; the `PREV` takes `x`'s
  `NEXT`) for MdbUt's `UtRangeOrd.remL`; `.mdbF` is its instance, statement unchanged.
* Gen 54: that proof moved again into **`cdt.empty_slot.mdbFLG`**, whose post names the ghost (`G' = G` on the
  null-cap path, `G' = remG x G` otherwise) for MdbTreeF's tree step; `.mdbFL` is its instance, statement unchanged.

No named premise.
-/
import Fl4ProofsA64.P1.MdbRem
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {Sg : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

/-- Slot `y`'s four words equal at `s` and `s'`. -/
def SK (st : machine.Store S) [L : LawfulStore st] (s s' : S) (y : U64) : Prop :=
  L.mem s' y = L.mem s y ∧ L.mem s' (wa y 8#u64) = L.mem s (wa y 8#u64) ∧
    L.mem s' (wa y 16#u64) = L.mem s (wa y 16#u64) ∧ L.mem s' (wa y 24#u64) = L.mem s (wa y 24#u64)

theorem SK.refl (s : S) (y : U64) : SK st s s y := ⟨rfl, rfl, rfl, rfl⟩

theorem SK.trans {s1 s2 s3 : S} {y : U64} (h1 : SK st s1 s2 y) (h2 : SK st s2 s3 y) : SK st s1 s3 y :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.trans h1.2.2.2⟩

section
variable {OS : Set U64}

theorem SK.wr (hO : OSOK T Ω Sg OS) (s : S) {z y : U64} (hz : z ∈ OS) (hy : y ∈ OS) (hne : y ≠ z) {k : U64}
    (hk : k.val < 32) (hk8 : k.val % 8 = 0) (v : U64) : SK st s (L.wr s (wa z k) v) y := by
  have e := wv (hO.fit z hz) hk
  exact other_keep hO hz hy hne (hO.al hz hk hk8) ⟨by rw [e]; omega, by rw [e]; omega⟩

theorem SK.wr0 (hO : OSOK T Ω Sg OS) (s : S) {z y : U64} (hz : z ∈ OS) (hy : y ∈ OS) (hne : y ≠ z) (v : U64) :
    SK st s (L.wr s z v) y :=
  other_keep hO hz hy hne (hO.al0 hz) ⟨Nat.le_refl _, by omega⟩

theorem SK.cp {s s' : S} {y : U64} (h : SK st s s' y) : capA st s' y = capA st s y := by
  unfold capA; rw [h.1, h.2.1]

theorem SK.nx {s s' : S} {y : U64} (h : SK st s s' y) : NxA st s' y = NxA st s y := by
  unfold NxA; rw [h.2.2.2]

/-- Every `OS` slot's words kept by a write set outside the `OS` slots. -/
theorem SK.of_w (hO : OSOK T Ω Sg OS) {s s' : S} {Pw : U64 → Prop} (hw : WritesIn st s s' Pw)
    (hpw : ∀ b, Pw b → ¬ InOS OS b) {y : U64} (hy : y ∈ OS) : SK st s s' y := by
  obtain ⟨v8, v16, v24⟩ := vals hO hy
  have k : ∀ b, Aligned b → y.val ≤ b.val → b.val < y.val + 32 → L.mem s' b = L.mem s b :=
    fun b hb h1 h2 => hw.mem_eq hb fun hp => hpw b hp ⟨y, hy, h1, h2⟩
  exact ⟨k _ (hO.al0 hy) (by omega) (by omega), k _ (hO.al hy (by simp) (by simp)) (by omega) (by omega),
    k _ (hO.al hy (by simp) (by simp)) (by omega) (by omega), k _ (hO.al hy (by simp) (by simp)) (by omega) (by omega)⟩

/-! ## The pointer words -/

theorem sx_set_next (w n : U64) (hn : obj.sext48 n = ok n) :
    sxF ((w &&& ~~~ obj.MDB_PTR_MASK) ||| (n &&& obj.MDB_PTR_MASK)) = n := by
  have := sext48_eq ((w &&& ~~~ obj.MDB_PTR_MASK) ||| (n &&& obj.MDB_PTR_MASK))
  rw [← sx_mask, link_bits, sx_mask, hn] at this
  exact (okinj this).symm

theorem sx_fb (w v : U64) (hv : v = FB ∨ v = 0#u64) : sxF ((w &&& ~~~ FB) ||| v) = sxF w := by
  have h1 := sext48_eq ((w &&& ~~~ FB) ||| v)
  have h2 := sext48_eq w
  have hvM : v &&& obj.MDB_PTR_MASK = 0#u64 := by rcases hv with rfl | rfl; exact fbc1; exact fbc3
  rw [← sx_mask, fb_bits w v FB obj.MDB_PTR_MASK hvM fbc2, sx_mask, h2] at h1
  exact (okinj h1).symm

theorem is_null_t : capability.Cap.is_null .Null = ok true := rfl

theorem is_null_f {c : capability.Cap} (h : c ≠ .Null) : capability.Cap.is_null c = ok false := by
  cases c <;> first | rfl | exact absurd rfl h

/-! ## `empty_slot` -/

variable {A : Type _} {ar : machine.Arch A}

set_option maxHeartbeats 4000000 in
/-- (gen 54) **`cdt.empty_slot.mdbFL` with the ghost named** (`mdbFL`'s proof, moved; `mdbFL` is its instance): the
`∃ G'` is `G` on the null-cap path and `remG x G` otherwise — what MdbTreeF's tree step (`Mdb.MdbOK.remove`) reads. -/
theorem cdt.empty_slot.mdbFLG (hO : OSOK T Ω Sg OS) (h0 : ∀ y ∈ OS, y ≠ 0#u64) {G : List (List U64)} {s : S}
    (hM : MdbLk st OS G s) (hRO : RngOneA64 st G s) (hK : KindA st OS s) {a : A} {x : U64} (hx : x ∈ OS)
    {cl : capability.Cap} {Pw : U64 → Prop} (hpw : ∀ b, Pw b → ¬ InOS OS b)
    (hpcd : ∀ (s1 : S) (a1 : A), L.ksb s1 = L.ksb s →
      objects.post_cap_deletion st ar s1 a1 cl ⦃ r => WritesIn st s1 r.1 Pw ⦄) :
    cdt.empty_slot st ar s a x cl ⦃ r => (∃ G' : List (List U64), (capA st s x = .Null → G' = G) ∧ (capA st s x ≠ .Null → G' = remG x G) ∧
      MdbLk st OS G' r.1 ∧ RngOneA64 st G' r.1 ∧
      KindA st OS r.1 ∧ (∀ y ∈ OS, y ≠ x → capA st r.1 y = capA st s y) ∧
      (∀ y ∈ OS, y ≠ x → capA st s y = .Null → SK st s r.1 y) ∧ capA st r.1 x = .Null ∧
      (SK st s r.1 x ∨ (L.mem r.1 (wa x 16#u64) = 0#u64 ∧ L.mem r.1 (wa x 24#u64) = 0#u64))) ∧
      (capA st s x ≠ .Null → (∀ y ∈ OS, y ≠ x → y ≠ L.mem s (wa x 16#u64) → NxA st r.1 y = NxA st s y) ∧
        (L.mem s (wa x 16#u64) ≠ 0#u64 → NxA st r.1 (L.mem s (wa x 16#u64)) = NxA st s x)) ∧
      (capA st s x = .Null → ∀ y ∈ OS, NxA st r.1 y = NxA st s y) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.empty_slot
  rw [capA_eq, bind_ok]
  by_cases hn : capA st s x = .Null
  · rw [hn, is_null_t, bind_ok, if_pos rfl]
    exact (WP.spec_ok _).2 ⟨⟨G, fun _ => rfl, fun h => absurd rfl h, hM, hRO, hK, fun _ _ _ => rfl, fun y _ _ _ => SK.refl s y, hn,
      Or.inl (SK.refl s x)⟩, fun h => absurd rfl h, fun _ _ _ => rfl⟩
  rw [is_null_f hn, bind_ok, if_neg (by simp)]
  -- the slot's place in its chain
  have hxG : x ∈ G.flatten := (hM.members x).2 ⟨hx, hn⟩
  have inOS : ∀ y ∈ G.flatten, y ∈ OS := fun y hy => ((hM.members y).1 hy).1
  obtain ⟨cx, hcx0, hxcx⟩ := List.mem_flatten.1 hxG
  obtain ⟨ix, hix, hxi⟩ := List.getElem_of_mem hxcx
  have exi : cx[ix]? = some x := by rw [getElem?_of_lt hix, hxi]
  have hcxn := ch_nodup hM.nodup hcx0
  have memc : ∀ {n : Nat} {y : U64}, cx[n]? = some y → y ∈ OS := fun e =>
    inOS _ (List.mem_flatten.2 ⟨_, hcx0, List.mem_of_getElem? e⟩)
  have Pf : L.mem s (wa x 16#u64) ≠ 0#u64 → L.mem s (wa x 16#u64) ∈ OS ∧ L.mem s (wa x 16#u64) ≠ x := by
    intro hP0
    obtain ⟨j, hj, ej⟩ := hM.prev_idx hcx0 exi hP0
    exact ⟨memc ej, fun e => by have := nd_idx hcxn ej (e ▸ exi); omega⟩
  have Nf : NxA st s x ≠ 0#u64 → NxA st s x ∈ OS ∧ NxA st s x ≠ x := by
    intro hN0
    have ej := hM.next_idx hcx0 exi hN0
    exact ⟨memc ej, fun e => by have := nd_idx hcxn ej (e ▸ exi); omega⟩
  have PN : L.mem s (wa x 16#u64) ≠ 0#u64 → NxA st s x ≠ 0#u64 → L.mem s (wa x 16#u64) ≠ NxA st s x := by
    intro hP0 hN0 e
    obtain ⟨j, hj, ej⟩ := hM.prev_idx hcx0 exi hP0
    have ek := hM.next_idx hcx0 exi hN0
    have := nd_idx hcxn ej (e ▸ ek); omega
  have hNs : obj.sext48 (NxA st s x) = ok (NxA st s x) := sx_idem _ _ (sext48_eq _)
  rw [slot_prev_eq, bind_ok, next_eq, bind_ok]
  refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st x s hS) fun fb _ => ?_
  simp only [obj.Slot.is_null, bind_ok]
  -- stage 1: `set_next(P, N)`
  refine WP.spec_bind (Pₘ := fun s1 => (∀ y ∈ OS, y ≠ L.mem s (wa x 16#u64) → SK st s s1 y) ∧
      (L.mem s (wa x 16#u64) ≠ 0#u64 → NxA st s1 (L.mem s (wa x 16#u64)) = NxA st s x) ∧
      (∀ y ∈ OS, capA st s1 y = capA st s y) ∧
      (∀ y ∈ OS, L.mem s1 (wa y 16#u64) = L.mem s (wa y 16#u64)) ∧ L.ksb s1 = L.ksb s) ?_ fun s1 h1 => ?_
  · split
    · rename_i hp0
      have hP0 : L.mem s (wa x 16#u64) = 0#u64 := by simpa using hp0
      exact (WP.spec_ok _).2 ⟨fun y _ _ => SK.refl s y, fun h => absurd hP0 h, fun _ _ => rfl, fun _ _ => rfl, rfl⟩
    · rename_i hp0
      have hP0 : L.mem s (wa x 16#u64) ≠ 0#u64 := by simpa using hp0
      obtain ⟨hPO, -⟩ := Pf hP0
      rw [set_next_eq]
      refine (WP.spec_ok _).2 ⟨fun y hy hne => SK.wr hO s hPO hy hne (by simp) (by simp) _, fun _ => ?_,
        fun y hy => ?_, fun y hy => ?_, L.ksb_wr _ _ _⟩
      · have a24 := hO.al hPO (k := 24#u64) (by simp) (by simp)
        unfold NxA; rw [L.mem_wr_same a24]; exact sx_set_next _ _ hNs
      · by_cases e : y = L.mem s (wa x 16#u64)
        · subst e
          obtain ⟨v8, v16, v24⟩ := vals hO hy
          have a24 := hO.al hy (k := 24#u64) (by simp) (by simp)
          unfold capA
          rw [L.mem_wr_ne a24 (hO.al0 hy) (by omega), L.mem_wr_ne a24 (hO.al hy (by simp) (by simp)) (by omega)]
        · exact (SK.wr hO s hPO hy e (by simp) (by simp) _).cp
      · by_cases e : y = L.mem s (wa x 16#u64)
        · subst e
          obtain ⟨v8, v16, v24⟩ := vals hO hy
          exact L.mem_wr_ne (hO.al hy (by simp) (by simp)) (hO.al hy (by simp) (by simp)) (by omega)
        · exact (SK.wr hO s hPO hy e (by simp) (by simp) _).2.2.1
  obtain ⟨k1, p1, c1, w1, b1⟩ := h1
  -- stage 2: `set_prev(N, P)` and the first-badged update of `N`
  refine WP.spec_bind (Pₘ := fun s2 => (∀ y ∈ OS, y ≠ L.mem s (wa x 16#u64) → y ≠ NxA st s x → SK st s s2 y) ∧
      (∀ y ∈ OS, capA st s2 y = capA st s y) ∧
      (∀ y ∈ OS, y ≠ NxA st s x → L.mem s2 (wa y 16#u64) = L.mem s (wa y 16#u64)) ∧
      (L.mem s (wa x 16#u64) ≠ 0#u64 → NxA st s2 (L.mem s (wa x 16#u64)) = NxA st s x) ∧
      (NxA st s x ≠ 0#u64 → L.mem s2 (wa (NxA st s x) 16#u64) = L.mem s (wa x 16#u64) ∧
        (NxA st s x ≠ L.mem s (wa x 16#u64) → NxA st s2 (NxA st s x) = NxA st s (NxA st s x))) ∧
      L.ksb s2 = L.ksb s) ?_
    fun s2 h2 => ?_
  · split
    · rename_i hn0
      have hN0 : NxA st s x = 0#u64 := by simpa using hn0
      refine (WP.spec_ok _).2 ⟨fun y hy h1 _ => k1 y hy h1, c1, fun y hy _ => w1 y hy, p1,
        fun h => absurd hN0 h, b1⟩
    · rename_i hn0
      have hN0 : NxA st s x ≠ 0#u64 := by simpa using hn0
      obtain ⟨hNO, -⟩ := Nf hN0
      obtain ⟨v8, v16, v24⟩ := vals hO hNO
      have a16 := hO.al hNO (k := 16#u64) (by simp) (by simp)
      have a24 := hO.al hNO (k := 24#u64) (by simp) (by simp)
      rw [set_prev_eq, bind_ok]
      refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st _ _ hS) fun nfb _ => ?_
      -- both first-badged writes: `(w &&& ~~~FB) ||| v` with `v ∈ {FB, 0}`
      have key : ∀ v, (v = FB ∨ v = 0#u64) →
          let s3 := L.wr s1 (wa (NxA st s x) 16#u64) (L.mem s (wa x 16#u64))
          let s2 := L.wr s3 (wa (NxA st s x) 24#u64) ((L.mem s3 (wa (NxA st s x) 24#u64) &&& ~~~ FB) ||| v)
          (∀ y ∈ OS, y ≠ L.mem s (wa x 16#u64) → y ≠ NxA st s x → SK st s s2 y) ∧
          (∀ y ∈ OS, capA st s2 y = capA st s y) ∧
          (∀ y ∈ OS, y ≠ NxA st s x → L.mem s2 (wa y 16#u64) = L.mem s (wa y 16#u64)) ∧
          (L.mem s (wa x 16#u64) ≠ 0#u64 → NxA st s2 (L.mem s (wa x 16#u64)) = NxA st s x) ∧
          (NxA st s x ≠ 0#u64 → L.mem s2 (wa (NxA st s x) 16#u64) = L.mem s (wa x 16#u64) ∧
            (NxA st s x ≠ L.mem s (wa x 16#u64) → NxA st s2 (NxA st s x) = NxA st s (NxA st s x))) ∧
          L.ksb s2 = L.ksb s := by
        intro v hv
        have kk : ∀ y ∈ OS, y ≠ NxA st s x →
            SK st s1 (L.wr (L.wr s1 (wa (NxA st s x) 16#u64) (L.mem s (wa x 16#u64))) (wa (NxA st s x) 24#u64)
              ((L.mem (L.wr s1 (wa (NxA st s x) 16#u64) (L.mem s (wa x 16#u64))) (wa (NxA st s x) 24#u64) &&&
                ~~~ FB) ||| v)) y := fun y hy hne =>
          (SK.wr hO s1 hNO hy hne (by simp) (by simp) _).trans (SK.wr hO _ hNO hy hne (by simp) (by simp) _)
        have m24 : L.mem (L.wr s1 (wa (NxA st s x) 16#u64) (L.mem s (wa x 16#u64))) (wa (NxA st s x) 24#u64) =
            L.mem s1 (wa (NxA st s x) 24#u64) := L.mem_wr_ne a16 a24 (by omega)
        refine ⟨fun y hy h1' h2' => (k1 y hy h1').trans (kk y hy h2'), fun y hy => ?_, fun y hy hne => ?_,
          fun hP0 => ?_, fun _ => ⟨?_, fun hne => ?_⟩, by simp only [L.ksb_wr]; exact b1⟩
        · by_cases e : y = NxA st s x
          · subst e
            unfold capA
            rw [L.mem_wr_ne a24 (hO.al0 hy) (by omega), L.mem_wr_ne a24 (hO.al hy (by simp) (by simp)) (by omega),
              L.mem_wr_ne a16 (hO.al0 hy) (by omega), L.mem_wr_ne a16 (hO.al hy (by simp) (by simp)) (by omega)]
            exact c1 _ hy
          · rw [(kk y hy e).cp]; exact c1 y hy
        · rw [(kk y hy hne).2.2.1]; exact w1 y hy
        · have hne : L.mem s (wa x 16#u64) ≠ NxA st s x := PN hP0 hN0
          rw [(kk _ (Pf hP0).1 hne).nx]; exact p1 hP0
        · rw [L.mem_wr_ne a24 a16 (by omega), L.mem_wr_same a16]
        · show sxF (L.mem _ (wa (NxA st s x) 24#u64)) = sxF (L.mem s (wa (NxA st s x) 24#u64))
          rw [L.mem_wr_same a24, sx_fb _ _ hv, m24]
          exact congrArg sxF (k1 _ hNO hne).2.2.2
      split
      · rw [set_fb_eq_t]; exact (WP.spec_ok _).2 (key FB (Or.inl rfl))
      · cases fb
        · rw [set_fb_eq_f]; exact (WP.spec_ok _).2 (key 0#u64 (Or.inr rfl))
        · rw [set_fb_eq_t]; exact (WP.spec_ok _).2 (key FB (Or.inl rfl))
  obtain ⟨k2, c2, w2, p2, n2, b2⟩ := h2
  -- stage 3: `clear(x)`
  rw [clear_eq, bind_ok]
  obtain ⟨v8, v16, v24⟩ := vals hO hx
  have kx : ∀ y ∈ OS, y ≠ x → SK st s2
      (L.wr (L.wr (L.wr (L.wr s2 x 0#u64) (wa x 8#u64) 0#u64) (wa x 16#u64) 0#u64) (wa x 24#u64) 0#u64) y :=
    fun y hy hne => (((SK.wr0 hO s2 hx hy hne _).trans (SK.wr hO _ hx hy hne (by simp) (by simp) _)).trans
      (SK.wr hO _ hx hy hne (by simp) (by simp) _)).trans (SK.wr hO _ hx hy hne (by simp) (by simp) _)
  have cx0 : capA st
      (L.wr (L.wr (L.wr (L.wr s2 x 0#u64) (wa x 8#u64) 0#u64) (wa x 16#u64) 0#u64) (wa x 24#u64) 0#u64) x = .Null := by
    have a0 := hO.al0 hx
    have a8 := hO.al hx (k := 8#u64) (by simp) (by simp)
    have a16 := hO.al hx (k := 16#u64) (by simp) (by simp)
    have a24 := hO.al hx (k := 24#u64) (by simp) (by simp)
    have e0 : L.mem (L.wr (L.wr (L.wr (L.wr s2 x 0#u64) (wa x 8#u64) 0#u64) (wa x 16#u64) 0#u64) (wa x 24#u64)
        0#u64) x = 0#u64 := by
      rw [L.mem_wr_ne a24 a0 (by omega), L.mem_wr_ne a16 a0 (by omega), L.mem_wr_ne a8 a0 (by omega),
        L.mem_wr_same a0]
    have := capA_eq (st := st) (L.wr (L.wr (L.wr (L.wr s2 x 0#u64) (wa x 8#u64) 0#u64) (wa x 16#u64) 0#u64)
      (wa x 24#u64) 0#u64) x
    rw [DPF.slot_cap_dec, e0, decode_zero] at this; exact (okinj this).symm
  -- stage 4: `post_cap_deletion`
  refine WP.spec_mono (hpcd _ a (by simp only [L.ksb_wr]; exact b2)) fun r hr => ?_
  have kr : ∀ y ∈ OS, SK st _ r.1 y := fun y hy => SK.of_w hO hr hpw hy
  have fin : ∀ y ∈ OS, y ≠ x → SK st s2 r.1 y := fun y hy hne => (kx y hy hne).trans (kr y hy)
  have hcr : ∀ y ∈ OS, y ≠ x → capA st r.1 y = capA st s y := fun y hy hne => by
    rw [(fin y hy hne).cp]; exact c2 y hy
  have hnxF : ∀ y ∈ OS, y ≠ x → y ≠ L.mem s (wa x 16#u64) → NxA st r.1 y = NxA st s y := by
    intro y hy hne hP
    rw [(fin y hy hne).nx]
    by_cases e : y = NxA st s x
    · subst e
      exact (n2 (h0 _ hy)).2 hP
    · exact (k2 y hy hP e).nx
  have hPF : L.mem s (wa x 16#u64) ≠ 0#u64 → NxA st r.1 (L.mem s (wa x 16#u64)) = NxA st s x := by
    intro hP0
    rw [(fin _ (Pf hP0).1 (Pf hP0).2).nx]; exact p2 hP0
  have hM' : MdbLk st OS (remG x G) r.1 := by
    refine hM.rem h0 hxG (by rw [(kr x hx).cp]; exact cx0) hcr hnxF (fun y hy hne hN => ?_)
      hPF (fun hN0 => ?_)
    · rw [(fin y hy hne).2.2.1]; exact w2 y hy hN
    · rw [(fin _ (Nf hN0).1 (Nf hN0).2).2.2.1]; exact (n2 hN0).1
  have nnP : ∀ y ∈ OS, capA st s y = .Null → y ≠ L.mem s (wa x 16#u64) := by
    intro y hy hy0 e
    by_cases hP0 : L.mem s (wa x 16#u64) = 0#u64
    · exact h0 y hy (e.trans hP0)
    · obtain ⟨j, -, ej⟩ := hM.prev_idx hcx0 exi hP0
      have hm := ((hM.members _).1 (List.mem_flatten.2 ⟨cx, hcx0, List.mem_of_getElem? ej⟩)).2
      exact hm (by rw [← e]; exact hy0)
  have nnN : ∀ y ∈ OS, capA st s y = .Null → y ≠ NxA st s x := by
    intro y hy hy0 e
    by_cases hN0 : NxA st s x = 0#u64
    · exact h0 y hy (e.trans hN0)
    · have ej := hM.next_idx hcx0 exi hN0
      have hm := ((hM.members _).1 (List.mem_flatten.2 ⟨cx, hcx0, List.mem_of_getElem? ej⟩)).2
      exact hm (by rw [← e]; exact hy0)
  have a16 := hO.al hx (k := 16#u64) (by simp) (by simp)
  have a24 := hO.al hx (k := 24#u64) (by simp) (by simp)
  refine ⟨⟨remG x G, fun h => absurd h hn, fun _ => rfl, hM', hRO.rem hM.nodup fun y hy hne => hcr y (inOS y hy) hne, hK.rem ?_ hcr, hcr,
    fun y hy hne hy0 => (k2 y hy (nnP y hy hy0) (nnN y hy hy0)).trans (fin y hy hne), ?_, Or.inr ⟨?_, ?_⟩⟩,
    fun _ => ⟨hnxF, hPF⟩, fun h => absurd h hn⟩
  · rw [(kr x hx).cp]; exact cx0
  · rw [(kr x hx).cp]; exact cx0
  · rw [(kr x hx).2.2.1, L.mem_wr_ne a24 a16 (by omega), L.mem_wr_same a16]
  · rw [(kr x hx).2.2.2, L.mem_wr_same a24]

/-- (gen 53) **`cdt.empty_slot.mdbF` with the links** (`mdbF`'s proof, moved; `mdbF` is its instance): on the
non-null path, every other `OS` slot but `x`'s `PREV` keeps its `NEXT`, and `x`'s `PREV` (if not 0) takes `x`'s
`NEXT` (on the null path every `NEXT` is kept) — the facts `MdbLk.rem` consumes, which MdbUt's `UtRangeOrd.remL` reads. -/
theorem cdt.empty_slot.mdbFL (hO : OSOK T Ω Sg OS) (h0 : ∀ y ∈ OS, y ≠ 0#u64) {G : List (List U64)} {s : S}
    (hM : MdbLk st OS G s) (hRO : RngOneA64 st G s) (hK : KindA st OS s) {a : A} {x : U64} (hx : x ∈ OS)
    {cl : capability.Cap} {Pw : U64 → Prop} (hpw : ∀ b, Pw b → ¬ InOS OS b)
    (hpcd : ∀ (s1 : S) (a1 : A), L.ksb s1 = L.ksb s →
      objects.post_cap_deletion st ar s1 a1 cl ⦃ r => WritesIn st s1 r.1 Pw ⦄) :
    cdt.empty_slot st ar s a x cl ⦃ r => (∃ G' : List (List U64), MdbLk st OS G' r.1 ∧ RngOneA64 st G' r.1 ∧
      KindA st OS r.1 ∧ (∀ y ∈ OS, y ≠ x → capA st r.1 y = capA st s y) ∧
      (∀ y ∈ OS, y ≠ x → capA st s y = .Null → SK st s r.1 y) ∧ capA st r.1 x = .Null ∧
      (SK st s r.1 x ∨ (L.mem r.1 (wa x 16#u64) = 0#u64 ∧ L.mem r.1 (wa x 24#u64) = 0#u64))) ∧
      (capA st s x ≠ .Null → (∀ y ∈ OS, y ≠ x → y ≠ L.mem s (wa x 16#u64) → NxA st r.1 y = NxA st s y) ∧
        (L.mem s (wa x 16#u64) ≠ 0#u64 → NxA st r.1 (L.mem s (wa x 16#u64)) = NxA st s x)) ∧
      (capA st s x = .Null → ∀ y ∈ OS, NxA st r.1 y = NxA st s y) ⦄ :=
  WP.spec_mono (cdt.empty_slot.mdbFLG hO h0 hM hRO hK hx hpw hpcd)
    fun _ ⟨⟨G', _, _, r⟩, h2⟩ => ⟨⟨G', r⟩, h2⟩

/-- **`cdt.empty_slot.mdb` with the slot frame** (gen 49): besides `MdbLk ∧ RngOneA64 ∧ KindA`, every other `OS`
slot keeps its cap, every other null `OS` slot keeps its four words (the link writes hit the chain neighbours, which
are members), and `x` ends null with zero links (or untouched, on the null-cap path). -/
theorem cdt.empty_slot.mdbF (hO : OSOK T Ω Sg OS) (h0 : ∀ y ∈ OS, y ≠ 0#u64) {G : List (List U64)} {s : S}
    (hM : MdbLk st OS G s) (hRO : RngOneA64 st G s) (hK : KindA st OS s) {a : A} {x : U64} (hx : x ∈ OS)
    {cl : capability.Cap} {Pw : U64 → Prop} (hpw : ∀ b, Pw b → ¬ InOS OS b)
    (hpcd : ∀ (s1 : S) (a1 : A), L.ksb s1 = L.ksb s →
      objects.post_cap_deletion st ar s1 a1 cl ⦃ r => WritesIn st s1 r.1 Pw ⦄) :
    cdt.empty_slot st ar s a x cl ⦃ r => ∃ G' : List (List U64), MdbLk st OS G' r.1 ∧ RngOneA64 st G' r.1 ∧
      KindA st OS r.1 ∧ (∀ y ∈ OS, y ≠ x → capA st r.1 y = capA st s y) ∧
      (∀ y ∈ OS, y ≠ x → capA st s y = .Null → SK st s r.1 y) ∧ capA st r.1 x = .Null ∧
      (SK st s r.1 x ∨ (L.mem r.1 (wa x 16#u64) = 0#u64 ∧ L.mem r.1 (wa x 24#u64) = 0#u64)) ⦄ :=
  WP.spec_mono (cdt.empty_slot.mdbFL hO h0 hM hRO hK hx hpw hpcd) fun _ h => h.1

/-- **`MdbLk ∧ RngOneA64 ∧ KindA` along `cdt::empty_slot`** (module docstring). -/
theorem cdt.empty_slot.mdb (hO : OSOK T Ω Sg OS) (h0 : ∀ y ∈ OS, y ≠ 0#u64) {G : List (List U64)} {s : S}
    (hM : MdbLk st OS G s) (hRO : RngOneA64 st G s) (hK : KindA st OS s) {a : A} {x : U64} (hx : x ∈ OS)
    {cl : capability.Cap} {Pw : U64 → Prop} (hpw : ∀ b, Pw b → ¬ InOS OS b)
    (hpcd : ∀ (s1 : S) (a1 : A), objects.post_cap_deletion st ar s1 a1 cl ⦃ r => WritesIn st s1 r.1 Pw ⦄) :
    cdt.empty_slot st ar s a x cl ⦃ r => ∃ G' : List (List U64), MdbLk st OS G' r.1 ∧ RngOneA64 st G' r.1 ∧
      KindA st OS r.1 ⦄ :=
  WP.spec_mono (cdt.empty_slot.mdbF hO h0 hM hRO hK hx hpw fun s1 a1 _ => hpcd s1 a1)
    fun _ ⟨G', a1, a2, a3, _⟩ => ⟨G', a1, a2, a3⟩

end

end ST
end R
end W7

end

end Fl4ProofsA64.P1
