/-
P1 (aarch64, gen 48): **`MdbLk ∧ RngOneA64 ∧ KindA` along `cdt::swap` / `cap_swap_for_delete` and
`cdt::insert_with_cap` / `cdt::insert` at function level** (cdt.rs:28–46, 67–103), landing on gen 47's data-level
`MdbLk.ren` / `RngOneA64.ren` / `KindA.ren` (MdbSwap) and `MdbLk.ins` / `RngOneA64.ins` / `KindA.ins` (MdbIns).

* **The link words as two functions.** `LR st OS s pv nx`: every `OS` slot `z` has `PREV` word `pv z` and `NEXT`
  pointer (`NxA`) `nx z`. Store steps: `LR.wr2` (a cap write keeps it), `LR.prev` (`set_prev`), `LR.nw` (a `NEXT`
  word with the pointer bits of a canonical `n`: `set_next`, `set_next_flags`), `LR.congr`; `capA_lnk` (a link
  write keeps every `OS` cap).
* **The swap's link algebra, abstractly** (`LkAbs`, any type with decidable equality and a null `o`): `LkF o M pv nx`
  (the link facts of a member set: closure, inverse links, no self-links, `PREV ≠ NEXT`), the swap's eight link writes
  as the pointwise functions `s3` / `s4` (the first two writes) and `sN` / `sP` (the final `NEXT` / `PREV`), and
  **`LkAbs.sw_ok`**: under `LkF`, `sN (tr y) = tr (nx y)` and `sP (tr y) = tr (pv y)` for every member `y` (`tr` =
  the transposition `swp`) — including the two adjacent cases, where `swap` reads `slot2`'s links after it has
  rewritten them (cdt.rs:79–84). `MdbLk.lkF`: `MdbLk` gives `LkF` on its members.
* **`cdt.swap.lr`**: `swap` of two distinct canonical `OS` slots ends with `LR` at `sP` / `sN` and the two caps
  exchanged; **`cdt.swap.mdb`** (both slots members, i.e. non-null caps): `MdbLk ∧ RngOneA64 ∧ KindA` at the ghost
  `renG x1 x2 G`; **`cdt.cap_swap_for_delete.mdb`** (`∃ G'`; equal slots return the state).
* **`cdt.set_untyped_cap_as_full.lk`** (only the source's cap words written; the new cap is an `Untyped` of the same
  base and size: `AlikeA.ut`); **`cdt.insert_with_cap.lr`**; **`cdt.insert_with_cap.mdb`** at the ghost
  `insG src dest G`: case hypotheses on the caller — `dest` an `OS` slot with a null cap (`ensure_empty_slot`),
  canonical; the new cap encodable (`EncWf`, true of every decoded cap and kept by `derive_cap` /
  `update_cap_data`), not null, and `AlikeA` the source's cap (same key; for a key cap the same class and kind:
  `derive_cap`, objects.rs:200–240, keeps constructor and object); **`cdt.insert.mdb`** (`src_cap` read from `src`).

(gen 52, in place) **`cdt.swap.lrW`**: `swap.lr` for any two encodable caps (`EncWf`), the proof moved there;
`swap.lr` (statement unchanged) is its instance at the two slots' own caps.

No named premise; new definitions and theorems only (the hypotheses above are case hypotheses of the callers).
-/
import Fl4ProofsA64.P1.MdbIns
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1

/-! ## The swap's link algebra, abstractly -/

namespace LkAbs
variable {α : Type} [DecidableEq α]

/-- The transposition of `x1` and `x2` (`W7.R.ST.swp` at `U64`). -/
def tr (x1 x2 y : α) : α := if y = x1 then x2 else if y = x2 then x1 else y

/-- The link facts of a member set `M` with null `o`, `PREV` function `pv` and `NEXT` function `nx`. -/
structure LkF (o : α) (M : α → Prop) (pv nx : α → α) : Prop where
  z : ¬ M o
  nxm : ∀ y, M y → nx y ≠ o → M (nx y)
  pvm : ∀ y, M y → pv y ≠ o → M (pv y)
  nxpv : ∀ y, M y → nx y ≠ o → pv (nx y) = y
  pvnx : ∀ y, M y → pv y ≠ o → nx (pv y) = y
  nxne : ∀ y, M y → nx y ≠ y
  pvne : ∀ y, M y → pv y ≠ y
  pn : ∀ y, M y → pv y ≠ o → pv y ≠ nx y

/-- `NEXT` after `swap`'s first link write (`P1.NEXT := x2`). -/
def s3 (o : α) (pv nx : α → α) (x1 x2 : α) (z : α) : α := if pv x1 ≠ o ∧ z = pv x1 then x2 else nx z

/-- `PREV` after `swap`'s second link write (`N1.PREV := x2`). -/
def s4 (o : α) (pv nx : α → α) (x1 x2 : α) (z : α) : α := if nx x1 ≠ o ∧ z = nx x1 then x2 else pv z

/-- `NEXT` at the end of `swap`. -/
def sN (o : α) (pv nx : α → α) (x1 x2 : α) (z : α) : α :=
  if s4 o pv nx x1 x2 x2 ≠ o ∧ z = s4 o pv nx x1 x2 x2 then x1 else if z = x2 then nx x1
  else if z = x1 then s3 o pv nx x1 x2 x2 else s3 o pv nx x1 x2 z

/-- `PREV` at the end of `swap`. -/
def sP (o : α) (pv nx : α → α) (x1 x2 : α) (z : α) : α :=
  if s3 o pv nx x1 x2 x2 ≠ o ∧ z = s3 o pv nx x1 x2 x2 then x1 else if z = x2 then pv x1
  else if z = x1 then s4 o pv nx x1 x2 x2 else s4 o pv nx x1 x2 z

/-- **The swap renames the links** (module docstring). -/
theorem sw_ok {o : α} {M : α → Prop} {pv nx : α → α} (h : LkF o M pv nx) {x1 x2 : α} (m1 : M x1) (m2 : M x2)
    (hne : x1 ≠ x2) {y : α} (my : M y) :
    sN o pv nx x1 x2 (tr x1 x2 y) = tr x1 x2 (nx y) ∧ sP o pv nx x1 x2 (tr x1 x2 y) = tr x1 x2 (pv y) := by
  have z := h.z; have nxm := h.nxm; have pvm := h.pvm; have nxpv := h.nxpv; have pvnx := h.pvnx
  have nxne := h.nxne; have pvne := h.pvne; have pn := h.pn
  constructor
  · unfold sN s3 s4 tr
    grind
  · unfold sP s3 s4 tr
    grind

end LkAbs

open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {Sg : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

theorem swp_tr (x1 x2 y : U64) : swp x1 x2 y = LkAbs.tr x1 x2 y := rfl

theorem nxA_can (s : S) (x : U64) : obj.sext48 (NxA st s x) = ok (NxA st s x) := sx_idem _ _ (sext48_eq _)

/-! ## The link words as functions -/

/-- Every `OS` slot `z` has `PREV` word `pv z` and `NEXT` pointer `nx z`. -/
def LR (st : machine.Store S) [L : LawfulStore st] (OS : Set U64) (s : S) (pv nx : U64 → U64) : Prop :=
  ∀ z ∈ OS, L.mem s (wa z 16#u64) = pv z ∧ NxA st s z = nx z

section lr
variable {OS : Set U64}

theorem LR.self (s : S) : LR st OS s (fun z => L.mem s (wa z 16#u64)) (NxA st s) := fun _ _ => ⟨rfl, rfl⟩

theorem LR.congr {s : S} {pv nx pv' nx' : U64 → U64} (h : LR st OS s pv nx) (hp : ∀ z ∈ OS, pv z = pv' z)
    (hn : ∀ z ∈ OS, nx z = nx' z) : LR st OS s pv' nx' := fun z hz =>
  ⟨(h z hz).1.trans (hp z hz), (h z hz).2.trans (hn z hz)⟩

/-- A two-word cap write into an `OS` slot keeps `LR`. -/
theorem LR.wr2 (hO : OSOK T Ω Sg OS) {s : S} {pv nx : U64 → U64} (h : LR st OS s pv nx) {x0 w0 w1 : U64}
    (hx0 : x0 ∈ OS) : LR st OS (L.wr (L.wr s x0 w0) (wa x0 8#u64) w1) pv nx := by
  intro z hz
  obtain ⟨e16, e24⟩ := set_cap_links (st := st) (s := s) (w0 := w0) (w1 := w1) hO hx0 z hz
  refine ⟨e16.trans (h z hz).1, ?_⟩
  unfold NxA; rw [e24]; exact (h z hz).2

/-- **`set_prev`** of an `OS` slot. -/
theorem LR.prev (hO : OSOK T Ω Sg OS) {s : S} {pv nx : U64 → U64} (h : LR st OS s pv nx) {p : U64} (hp : p ∈ OS)
    (v : U64) : LR st OS (L.wr s (wa p 16#u64) v) (fun z => if z = p then v else pv z) nx := by
  intro z hz
  show L.mem _ (wa z 16#u64) = (if z = p then v else pv z) ∧ NxA st _ z = nx z
  by_cases e : z = p
  · subst e
    obtain ⟨v8, v16, v24⟩ := vals hO hz
    have a16 := hO.al hz (k := 16#u64) (by simp) (by simp)
    have a24 := hO.al hz (k := 24#u64) (by simp) (by simp)
    refine ⟨by rw [if_pos rfl, L.mem_wr_same a16], ?_⟩
    unfold NxA; rw [L.mem_wr_ne a16 a24 (by omega)]; exact (h z hz).2
  · have k := SK.wr (st := st) hO s hp hz e (k := 16#u64) (by simp) (by simp) v
    exact ⟨by rw [if_neg e, k.2.2.1]; exact (h z hz).1, by rw [k.nx]; exact (h z hz).2⟩

/-- **A `NEXT` word with the pointer bits of a canonical `n`** (`set_next`, `set_next_flags`). -/
theorem LR.nw (hO : OSOK T Ω Sg OS) {s : S} {pv nx : U64 → U64} (h : LR st OS s pv nx) {p : U64} (hp : p ∈ OS)
    {n w : U64} (hw : w &&& obj.MDB_PTR_MASK = n &&& obj.MDB_PTR_MASK) (hn : obj.sext48 n = ok n) :
    LR st OS (L.wr s (wa p 24#u64) w) pv (fun z => if z = p then n else nx z) := by
  intro z hz
  show L.mem _ (wa z 16#u64) = pv z ∧ NxA st _ z = (if z = p then n else nx z)
  by_cases e : z = p
  · subst e
    obtain ⟨v8, v16, v24⟩ := vals hO hz
    have a16 := hO.al hz (k := 16#u64) (by simp) (by simp)
    have a24 := hO.al hz (k := 24#u64) (by simp) (by simp)
    refine ⟨by rw [L.mem_wr_ne a24 a16 (by omega)]; exact (h z hz).1, ?_⟩
    rw [if_pos rfl]
    unfold NxA; rw [L.mem_wr_same a24]
    have := sext48_eq w
    rw [← sx_mask, hw, sx_mask, hn] at this
    exact (okinj this).symm
  · have k := SK.wr (st := st) hO s hp hz e (k := 24#u64) (by simp) (by simp) w
    exact ⟨by rw [k.2.2.1]; exact (h z hz).1, by rw [k.nx, if_neg e]; exact (h z hz).2⟩

/-- (gen 60) A `PREV` write into an `OS` slot is a cap-slot word write. -/
theorem WritesIn.cwp (hO : OSOK T Ω Sg OS) {s0 s : S} (h : WritesIn st s0 s (W7.CapW T Ω Sg)) {p : U64}
    (hp : p ∈ OS) (v : U64) : WritesIn st s0 (L.wr s (wa p 16#u64) v) (W7.CapW T Ω Sg) :=
  h.trans1 ((writesIn_wr (v := v) (hO.al hp (k := 16#u64) (by simp) (by simp))).mono fun b e => by
    subst e; exact hO.cw hp (by simp) (by simp))

/-- (gen 60) A `NEXT` write into an `OS` slot is a cap-slot word write. -/
theorem WritesIn.cwn (hO : OSOK T Ω Sg OS) {s0 s : S} (h : WritesIn st s0 s (W7.CapW T Ω Sg)) {p : U64}
    (hp : p ∈ OS) (v : U64) : WritesIn st s0 (L.wr s (wa p 24#u64) v) (W7.CapW T Ω Sg) :=
  h.trans1 ((writesIn_wr (v := v) (hO.al hp (k := 24#u64) (by simp) (by simp))).mono fun b e => by
    subst e; exact hO.cw hp (by simp) (by simp))

/-- (gen 60) A two-word cap write into an `OS` slot is a cap-slot word write. -/
theorem WritesIn.cw2 (hO : OSOK T Ω Sg OS) {s0 s : S} (h : WritesIn st s0 s (W7.CapW T Ω Sg)) {x : U64}
    (hx : x ∈ OS) (w0 w1 : U64) : WritesIn st s0 (L.wr (L.wr s x w0) (wa x 8#u64) w1) (W7.CapW T Ω Sg) :=
  (h.trans1 ((writesIn_wr (v := w0) (hO.al0 hx)).mono fun b e => by subst e; exact hO.cw0 hx)).trans1
    ((writesIn_wr (v := w1) (hO.al hx (k := 8#u64) (by simp) (by simp))).mono fun b e => by
      subst e; exact hO.cw hx (by simp) (by simp))

/-- A link write keeps every `OS` slot's cap. -/
theorem capA_lnk (hO : OSOK T Ω Sg OS) {s : S} {p k v y : U64} (hp : p ∈ OS) (hk : k.val = 16 ∨ k.val = 24)
    (hy : y ∈ OS) : capA st (L.wr s (wa p k) v) y = capA st s y := by
  have e := lnk_cap (st := st) (s := s) (v := v) hO hp hk hy
  rw [capA_eq, capA_eq] at e; exact okinj e

/-- Every `OS` slot's cap at `s` is the one at `s0`. -/
def CK (st : machine.Store S) [L : LawfulStore st] (OS : Set U64) (s0 s : S) : Prop :=
  ∀ y ∈ OS, capA st s y = capA st s0 y

theorem CK.refl (s : S) : CK st OS s s := fun _ _ => rfl

theorem CK.p (hO : OSOK T Ω Sg OS) {s0 s : S} (h : CK st OS s0 s) {p : U64} (hp : p ∈ OS) (v : U64) :
    CK st OS s0 (L.wr s (wa p 16#u64) v) := fun y hy => (capA_lnk hO hp (by simp) hy).trans (h y hy)

theorem CK.n (hO : OSOK T Ω Sg OS) {s0 s : S} (h : CK st OS s0 s) {p : U64} (hp : p ∈ OS) (v : U64) :
    CK st OS s0 (L.wr s (wa p 24#u64) v) := fun y hy => (capA_lnk hO hp (by simp) hy).trans (h y hy)

end lr

/-! ## `MdbLk` gives the abstract link facts -/

section lkf
variable {OS : Set U64} {G : List (List U64)}

theorem MdbLk.loc {s : S} (h : MdbLk st OS G s) {x : U64} (hx : x ∈ G.flatten) :
    ∃ c ∈ G, ∃ i : Nat, c[i]? = some x := by
  obtain ⟨c, hc, hxc⟩ := List.mem_flatten.1 hx
  obtain ⟨i, hi, e⟩ := List.getElem_of_mem hxc
  exact ⟨c, hc, i, by rw [getElem?_of_lt hi, e]⟩

/-- **`MdbLk` gives `LkF`** on its members, with `PREV` words and `NEXT` pointers. -/
theorem MdbLk.lkF {s : S} (h : MdbLk st OS G s) (h0 : ∀ y ∈ OS, y ≠ 0#u64) :
    LkAbs.LkF 0#u64 (fun y => y ∈ G.flatten) (fun z => L.mem s (wa z 16#u64)) (NxA st s) := by
  have inOS : ∀ y ∈ G.flatten, y ∈ OS := fun y hy => ((h.members y).1 hy).1
  have mem : ∀ {c : List U64}, c ∈ G → ∀ {n : Nat} {y : U64}, c[n]? = some y → y ∈ G.flatten :=
    fun hc _ _ e => List.mem_flatten.2 ⟨_, hc, List.mem_of_getElem? e⟩
  have nd : ∀ {c : List U64}, c ∈ G → c.Nodup := fun hc => ch_nodup h.nodup hc
  refine ⟨fun hm => h0 _ (inOS _ hm) rfl, fun y hy hn => ?_, fun y hy hp => ?_, fun y hy hn => ?_,
    fun y hy hp => ?_, fun y hy => ?_, fun y hy => ?_, fun y hy hp => ?_⟩
  · obtain ⟨c, hc, i, hi⟩ := h.loc hy
    exact mem hc (h.next_idx hc hi hn)
  · obtain ⟨c, hc, i, hi⟩ := h.loc hy
    obtain ⟨j, -, hj⟩ := h.prev_idx hc hi hp
    exact mem hc hj
  · obtain ⟨c, hc, i, hi⟩ := h.loc hy
    exact (h.chain c hc i y _ hi (h.next_idx hc hi hn)).2
  · obtain ⟨c, hc, i, hi⟩ := h.loc hy
    obtain ⟨j, rfl, hj⟩ := h.prev_idx hc hi hp
    exact (h.chain c hc j _ y hj hi).1
  · intro e
    by_cases hn : NxA st s y = 0#u64
    · exact h0 y (inOS y hy) (e ▸ hn)
    · obtain ⟨c, hc, i, hi⟩ := h.loc hy
      have := nd_idx (nd hc) (h.next_idx hc hi hn) (e.symm ▸ hi); omega
  · intro e
    by_cases hp : L.mem s (wa y 16#u64) = 0#u64
    · exact h0 y (inOS y hy) (e ▸ hp)
    · obtain ⟨c, hc, i, hi⟩ := h.loc hy
      obtain ⟨j, rfl, hj⟩ := h.prev_idx hc hi hp
      have := nd_idx (nd hc) hj (e.symm ▸ hi); omega
  · intro e
    by_cases hn : NxA st s y = 0#u64
    · exact hp (e.trans hn)
    · obtain ⟨c, hc, i, hi⟩ := h.loc hy
      obtain ⟨j, rfl, hj⟩ := h.prev_idx hc hi hp
      have := nd_idx (nd hc) hj (e ▸ h.next_idx hc hi hn); omega

end lkf

/-! ## `swap` at function level -/

section swap
variable {OS : Set U64}

set_option maxHeartbeats 4000000 in
/-- (gen 60) **`swap`'s links and caps for any two encodable caps, and its write frame** (gen 52's `swap.lrW`
proof with the written words tracked: every word written is a cap-slot word of `OS`, `W7.CapW`). -/
theorem cdt.swap.lrWF (hO : OSOK T Ω Sg OS) {s : S} {pv nx : U64 → U64} (hL : LR st OS s pv nx) {x1 x2 : U64}
    {c1 c2 : capability.Cap} (hx1 : x1 ∈ OS) (hx2 : x2 ∈ OS) (hne : x1 ≠ x2) (hs1 : obj.sext48 x1 = ok x1)
    (hs2 : obj.sext48 x2 = ok x2) (hw1 : CapRt.EncWf c1) (hw2 : CapRt.EncWf c2)
    (hp1 : pv x1 ≠ 0#u64 → pv x1 ∈ OS) (hn1 : nx x1 ≠ 0#u64 → nx x1 ∈ OS)
    (hp2 : pv x2 ≠ 0#u64 → pv x2 ∈ OS) (hn2 : nx x2 ≠ 0#u64 → nx x2 ∈ OS) :
    cdt.swap st s c1 x1 c2 x2 ⦃ s' => WritesIn st s s' (W7.CapW T Ω Sg) ∧
      LR st OS s' (LkAbs.sP 0#u64 pv nx x1 x2) (LkAbs.sN 0#u64 pv nx x1 x2) ∧
      capA st s' x1 = c2 ∧ capA st s' x2 = c1 ∧ ∀ y ∈ OS, y ≠ x1 → y ≠ x2 → capA st s' y = capA st s y ⦄ := by
  have hS : P0.StoreTotal st := L.total
  obtain ⟨a1, b1, he1, hr1⟩ := CapRt.decode_encode c1 hw1
  obtain ⟨a2, b2, he2, hr2⟩ := CapRt.decode_encode c2 hw2
  have cn1 : obj.sext48 (nx x1) = ok (nx x1) := by rw [← (hL x1 hx1).2]; exact nxA_can s x1
  unfold cdt.swap
  rw [set_cap_eq he2, bind_ok, set_cap_eq he1, bind_ok]
  have L2 : LR st OS (L.wr (L.wr (L.wr (L.wr s x1 a2) (wa x1 8#u64) b2) x2 a1) (wa x2 8#u64) b1) pv nx :=
    (hL.wr2 hO hx1).wr2 hO hx2
  have C2 : capA st (L.wr (L.wr (L.wr (L.wr s x1 a2) (wa x1 8#u64) b2) x2 a1) (wa x2 8#u64) b1) x1 = c2 ∧
      capA st (L.wr (L.wr (L.wr (L.wr s x1 a2) (wa x1 8#u64) b2) x2 a1) (wa x2 8#u64) b1) x2 = c1 ∧
      ∀ y ∈ OS, y ≠ x1 → y ≠ x2 →
        capA st (L.wr (L.wr (L.wr (L.wr s x1 a2) (wa x1 8#u64) b2) x2 a1) (wa x2 8#u64) b1) y = capA st s y :=
    ⟨by rw [capA_wr2_other hO hx2 hx1 hne, capA_wr2_self hO hx1 hr2], capA_wr2_self hO hx2 hr1,
      fun y hy n1 n2 => by rw [capA_wr2_other hO hx2 hy n2, capA_wr2_other hO hx1 hy n1]⟩
  have W2 : WritesIn st s (L.wr (L.wr (L.wr (L.wr s x1 a2) (wa x1 8#u64) b2) x2 a1) (wa x2 8#u64) b1)
      (W7.CapW T Ω Sg) :=
    WritesIn.cw2 hO (WritesIn.cw2 hO (WritesIn.refl (st := st) s (W7.CapW T Ω Sg)) hx1 a2 b2) hx2 a1 b1
  generalize L.wr (L.wr (L.wr (L.wr s x1 a2) (wa x1 8#u64) b2) x2 a1) (wa x2 8#u64) b1 = s2 at L2 C2 W2 ⊢
  -- slot 1's links
  rw [slot_prev_eq s2 x1, bind_ok, (L2 x1 hx1).1, next_eq, bind_ok, (L2 x1 hx1).2]
  refine WP.spec_bind (P0.obj.Slot.revocable.p0 st x1 s2 hS) fun r1 _ => ?_
  refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st x1 s2 hS) fun f1 _ => ?_
  simp only [obj.Slot.is_null, bind_ok]
  -- stage 3: `P1.NEXT := x2`
  refine WP.spec_bind (Pₘ := fun s3 => LR st OS s3 pv (LkAbs.s3 0#u64 pv nx x1 x2) ∧ CK st OS s2 s3 ∧
      WritesIn st s s3 (W7.CapW T Ω Sg)) ?_
    fun s3 h3 => ?_
  · split
    · rename_i hp0
      have hP0 : pv x1 = 0#u64 := by simpa using hp0
      refine (WP.spec_ok _).2 ⟨L2.congr (fun _ _ => rfl) fun z _ => ?_, CK.refl s2, W2⟩
      unfold LkAbs.s3; simp [hP0]
    · rename_i hp0
      have hP0 : pv x1 ≠ 0#u64 := by simpa using hp0
      rw [set_next_eq, WP.spec_ok]
      refine ⟨(L2.nw hO (hp1 hP0) (link_bits _ _) hs2).congr (fun _ _ => rfl) fun z _ => ?_,
        (CK.refl s2).n hO (hp1 hP0) _, WritesIn.cwn hO W2 (hp1 hP0) _⟩
      unfold LkAbs.s3; by_cases e : z = pv x1 <;> simp [e, hP0]
  obtain ⟨L3, C3, W3⟩ := h3
  -- stage 4: `N1.PREV := x2`
  refine WP.spec_bind (Pₘ := fun s4 => LR st OS s4 (LkAbs.s4 0#u64 pv nx x1 x2) (LkAbs.s3 0#u64 pv nx x1 x2) ∧
      CK st OS s2 s4 ∧ WritesIn st s s4 (W7.CapW T Ω Sg)) ?_ fun s4 h4 => ?_
  · split
    · rename_i hn0
      have hN0 : nx x1 = 0#u64 := by simpa using hn0
      refine (WP.spec_ok _).2 ⟨L3.congr (fun z _ => ?_) (fun _ _ => rfl), C3, W3⟩
      unfold LkAbs.s4; simp [hN0]
    · rename_i hn0
      have hN0 : nx x1 ≠ 0#u64 := by simpa using hn0
      rw [set_prev_eq, WP.spec_ok]
      refine ⟨(L3.prev hO (hn1 hN0) x2).congr (fun z _ => ?_) (fun _ _ => rfl), C3.p hO (hn1 hN0) _,
        WritesIn.cwp hO W3 (hn1 hN0) _⟩
      unfold LkAbs.s4; by_cases e : z = nx x1 <;> simp [e, hN0]
  obtain ⟨L4, C4, W4⟩ := h4
  -- the two values read from slot 2, and their membership
  have hP2 : LkAbs.s4 0#u64 pv nx x1 x2 x2 ≠ 0#u64 → LkAbs.s4 0#u64 pv nx x1 x2 x2 ∈ OS := by
    unfold LkAbs.s4; split
    · exact fun _ => hx2
    · exact hp2
  have hN2 : LkAbs.s3 0#u64 pv nx x1 x2 x2 ≠ 0#u64 → LkAbs.s3 0#u64 pv nx x1 x2 x2 ∈ OS := by
    unfold LkAbs.s3; split
    · exact fun _ => hx2
    · exact hn2
  have cn2 : obj.sext48 (LkAbs.s3 0#u64 pv nx x1 x2 x2) = ok (LkAbs.s3 0#u64 pv nx x1 x2 x2) := by
    rw [← (L4 x2 hx2).2]; exact nxA_can s4 x2
  rw [slot_prev_eq s4 x2, bind_ok, (L4 x2 hx2).1, next_eq, bind_ok, (L4 x2 hx2).2]
  refine WP.spec_bind (P0.obj.Slot.revocable.p0 st x2 s4 hS) fun r2 _ => ?_
  refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st x2 s4 hS) fun f2 _ => ?_
  -- stages 5–8: slot 1 and slot 2 get each other's links
  rw [set_prev_eq s4 x1 _, bind_ok]
  have L5 := L4.prev hO hx1 (LkAbs.s4 0#u64 pv nx x1 x2 x2)
  refine WP.spec_bind (set_nf_spec _ x1 _ r2 f2) ?_
  rintro s6 ⟨w6, rfl, hw6⟩
  have L6 := L5.nw hO hx1 hw6 cn2
  rw [set_prev_eq _ x2 _, bind_ok]
  have L7 := L6.prev hO hx2 (pv x1)
  refine WP.spec_bind (set_nf_spec _ x2 _ r1 f1) ?_
  rintro s8 ⟨w8, rfl, hw8⟩
  have L8 := L7.nw hO hx2 hw8 cn1
  have C8 := (((C4.p hO hx1 (LkAbs.s4 0#u64 pv nx x1 x2 x2)).n hO hx1 w6).p hO hx2 (pv x1)).n hO hx2 w8
  have W8 := WritesIn.cwn hO (WritesIn.cwp hO (WritesIn.cwn hO
    (WritesIn.cwp hO W4 hx1 (LkAbs.s4 0#u64 pv nx x1 x2 x2)) hx1 w6) hx2 (pv x1)) hx2 w8
  try simp only [obj.Slot.is_null, bind_ok]
  -- stage 9: `P2.NEXT := x1`
  refine WP.spec_bind (Pₘ := fun s9 => LR st OS s9
      (fun z => if z = x2 then pv x1 else if z = x1 then LkAbs.s4 0#u64 pv nx x1 x2 x2 else
        LkAbs.s4 0#u64 pv nx x1 x2 z) (LkAbs.sN 0#u64 pv nx x1 x2) ∧ CK st OS s2 s9 ∧
        WritesIn st s s9 (W7.CapW T Ω Sg)) ?_ fun s9 h9 => ?_
  · split
    · rename_i hp0
      have hP0 : LkAbs.s4 0#u64 pv nx x1 x2 x2 = 0#u64 := by simpa using hp0
      refine (WP.spec_ok _).2 ⟨L8.congr (fun _ _ => rfl) fun z _ => ?_, C8, W8⟩
      unfold LkAbs.sN; simp [hP0]
    · rename_i hp0
      have hP0 : LkAbs.s4 0#u64 pv nx x1 x2 x2 ≠ 0#u64 := by simpa using hp0
      rw [set_next_eq, WP.spec_ok]
      refine ⟨(L8.nw hO (hP2 hP0) (link_bits _ _) hs1).congr (fun _ _ => rfl) fun z _ => ?_,
        C8.n hO (hP2 hP0) _, WritesIn.cwn hO W8 (hP2 hP0) _⟩
      unfold LkAbs.sN; simp only [ne_eq, hP0, not_false_eq_true, true_and]
  obtain ⟨L9, C9, W9⟩ := h9
  -- stage 10: `N2.PREV := x1`
  split
  · rename_i hn0
    have hN0 : LkAbs.s3 0#u64 pv nx x1 x2 x2 = 0#u64 := by simpa using hn0
    refine (WP.spec_ok _).2 ⟨W9, L9.congr (fun z _ => ?_) (fun _ _ => rfl), ?_⟩
    · unfold LkAbs.sP; simp [hN0]
    · exact ⟨(C9 x1 hx1).trans C2.1, (C9 x2 hx2).trans C2.2.1, fun y hy n1 n2 => (C9 y hy).trans (C2.2.2 y hy n1 n2)⟩
  · rename_i hn0
    have hN0 : LkAbs.s3 0#u64 pv nx x1 x2 x2 ≠ 0#u64 := by simpa using hn0
    rw [set_prev_eq, WP.spec_ok]
    have C10 := C9.p hO (hN2 hN0) x1
    refine ⟨WritesIn.cwp hO W9 (hN2 hN0) x1,
      (L9.prev hO (hN2 hN0) x1).congr (fun z _ => ?_) (fun _ _ => rfl), ?_⟩
    · unfold LkAbs.sP; simp only [ne_eq, hN0, not_false_eq_true, true_and]
    · exact ⟨(C10 x1 hx1).trans C2.1, (C10 x2 hx2).trans C2.2.1,
        fun y hy n1 n2 => (C10 y hy).trans (C2.2.2 y hy n1 n2)⟩

/-- (gen 52) **`swap`'s links and caps for any two encodable caps** (`swap.lr`'s proof, moved; `swap.lr` is its
instance at the two slots' own caps; CNode Rotate swaps `update_cap_data` caps): two distinct canonical `OS` slots;
every link it follows that is not null is an `OS` slot. -/
theorem cdt.swap.lrW (hO : OSOK T Ω Sg OS) {s : S} {pv nx : U64 → U64} (hL : LR st OS s pv nx) {x1 x2 : U64}
    {c1 c2 : capability.Cap} (hx1 : x1 ∈ OS) (hx2 : x2 ∈ OS) (hne : x1 ≠ x2) (hs1 : obj.sext48 x1 = ok x1)
    (hs2 : obj.sext48 x2 = ok x2) (hw1 : CapRt.EncWf c1) (hw2 : CapRt.EncWf c2)
    (hp1 : pv x1 ≠ 0#u64 → pv x1 ∈ OS) (hn1 : nx x1 ≠ 0#u64 → nx x1 ∈ OS)
    (hp2 : pv x2 ≠ 0#u64 → pv x2 ∈ OS) (hn2 : nx x2 ≠ 0#u64 → nx x2 ∈ OS) :
    cdt.swap st s c1 x1 c2 x2 ⦃ s' => LR st OS s' (LkAbs.sP 0#u64 pv nx x1 x2) (LkAbs.sN 0#u64 pv nx x1 x2) ∧
      capA st s' x1 = c2 ∧ capA st s' x2 = c1 ∧ ∀ y ∈ OS, y ≠ x1 → y ≠ x2 → capA st s' y = capA st s y ⦄ :=
  WP.spec_mono (cdt.swap.lrWF hO hL hx1 hx2 hne hs1 hs2 hw1 hw2 hp1 hn1 hp2 hn2) fun _ h => h.2

/-- **`swap`'s links and caps** (module docstring): two distinct canonical `OS` slots; every link it follows that
is not null is an `OS` slot. -/
theorem cdt.swap.lr (hO : OSOK T Ω Sg OS) {s : S} {pv nx : U64 → U64} (hL : LR st OS s pv nx) {x1 x2 : U64}
    {c1 c2 : capability.Cap} (hx1 : x1 ∈ OS) (hx2 : x2 ∈ OS) (hne : x1 ≠ x2) (hs1 : obj.sext48 x1 = ok x1)
    (hs2 : obj.sext48 x2 = ok x2) (hc1 : capA st s x1 = c1) (hc2 : capA st s x2 = c2)
    (hp1 : pv x1 ≠ 0#u64 → pv x1 ∈ OS) (hn1 : nx x1 ≠ 0#u64 → nx x1 ∈ OS)
    (hp2 : pv x2 ≠ 0#u64 → pv x2 ∈ OS) (hn2 : nx x2 ≠ 0#u64 → nx x2 ∈ OS) :
    cdt.swap st s c1 x1 c2 x2 ⦃ s' => LR st OS s' (LkAbs.sP 0#u64 pv nx x1 x2) (LkAbs.sN 0#u64 pv nx x1 x2) ∧
      capA st s' x1 = c2 ∧ capA st s' x2 = c1 ∧ ∀ y ∈ OS, y ≠ x1 → y ≠ x2 → capA st s' y = capA st s y ⦄ :=
  cdt.swap.lrW hO hL hx1 hx2 hne hs1 hs2 (by rw [← hc1]; exact CapRt.decodeF_encWf _ _)
    (by rw [← hc2]; exact CapRt.decodeF_encWf _ _) hp1 hn1 hp2 hn2

variable {G : List (List U64)}

set_option maxHeartbeats 1000000 in
/-- **`MdbLk ∧ RngOneA64 ∧ KindA` along `cdt::swap`** of two distinct canonical members (non-null caps): the
ghost renamed by the transposition (gen 47's `MdbLk.ren`, `RngOneA64.ren`, `KindA.ren`). -/
theorem cdt.swap.mdb (hO : OSOK T Ω Sg OS) (h0 : ∀ y ∈ OS, y ≠ 0#u64) {s : S} (hM : MdbLk st OS G s)
    (hRO : RngOneA64 st G s) (hK : KindA st OS s) {x1 x2 : U64} {c1 c2 : capability.Cap} (hx1 : x1 ∈ G.flatten)
    (hx2 : x2 ∈ G.flatten) (hne : x1 ≠ x2) (hs1 : obj.sext48 x1 = ok x1) (hs2 : obj.sext48 x2 = ok x2)
    (hc1 : capA st s x1 = c1) (hc2 : capA st s x2 = c2) :
    cdt.swap st s c1 x1 c2 x2 ⦃ s' => MdbLk st OS (renG x1 x2 G) s' ∧ RngOneA64 st (renG x1 x2 G) s' ∧
      KindA st OS s' ⦄ := by
  have inOS : ∀ y ∈ G.flatten, y ∈ OS := fun y hy => ((hM.members y).1 hy).1
  have F := hM.lkF h0
  have o1 := inOS x1 hx1
  have o2 := inOS x2 hx2
  refine WP.spec_mono (cdt.swap.lr hO (LR.self s) o1 o2 hne hs1 hs2 hc1 hc2
    (fun h => inOS _ (F.pvm _ hx1 h)) (fun h => inOS _ (F.nxm _ hx1 h))
    (fun h => inOS _ (F.pvm _ hx2 h)) (fun h => inOS _ (F.nxm _ hx2 h))) ?_
  rintro s' ⟨hL, e1, e2, ek⟩
  have hc : ∀ y ∈ OS, capA st s' (swp x1 x2 y) = capA st s y := by
    intro y hy
    unfold swp
    by_cases a1 : y = x1
    · rw [a1, if_pos rfl, e2, hc1]
    · rw [if_neg a1]
      by_cases a2 : y = x2
      · rw [a2, if_pos rfl, e1, hc2]
      · rw [if_neg a2]; exact ek y hy a1 a2
  have sw : ∀ y ∈ G.flatten, swp x1 x2 y ∈ OS := fun y hy => swp_os o1 o2 (inOS y hy)
  refine ⟨hM.ren h0 o1 o2 hc (fun y hy => ?_) (fun y hy => ?_), hRO.ren fun y hy => hc y (inOS y hy),
    hK.ren o1 o2 hc⟩
  · rw [(hL _ (sw y hy)).2, swp_tr, swp_tr]; exact (LkAbs.sw_ok F hx1 hx2 hne hy).1
  · rw [(hL _ (sw y hy)).1, swp_tr, swp_tr]; exact (LkAbs.sw_ok F hx1 hx2 hne hy).2

/-- **`MdbLk ∧ RngOneA64 ∧ KindA` along `cap_swap_for_delete`** of two canonical members (cdt.rs:96–103: equal
slots return the state). -/
theorem cdt.cap_swap_for_delete.mdb (hO : OSOK T Ω Sg OS) (h0 : ∀ y ∈ OS, y ≠ 0#u64) {s : S}
    (hM : MdbLk st OS G s) (hRO : RngOneA64 st G s) (hK : KindA st OS s) {x1 x2 : U64} (hx1 : x1 ∈ G.flatten)
    (hx2 : x2 ∈ G.flatten) (hs1 : obj.sext48 x1 = ok x1) (hs2 : obj.sext48 x2 = ok x2) :
    cdt.cap_swap_for_delete st s x1 x2 ⦃ s' => ∃ G' : List (List U64), MdbLk st OS G' s' ∧ RngOneA64 st G' s' ∧
      KindA st OS s' ⦄ := by
  unfold cdt.cap_swap_for_delete
  simp only [obj.Slot.Insts.CoreCmpPartialEqSlot.eq, bind_ok]
  split
  · exact (WP.spec_ok _).2 ⟨G, hM, hRO, hK⟩
  · rename_i hne'
    have hne : x1 ≠ x2 := by simpa using hne'
    rw [capA_eq, bind_ok, capA_eq, bind_ok]
    exact WP.spec_mono (cdt.swap.mdb hO h0 hM hRO hK hx1 hx2 hne hs1 hs2 rfl rfl) fun s' h => ⟨_, h⟩

end swap

/-! ## `insert_with_cap` at function level -/

section ins
variable {OS : Set U64}

theorem nk_ut (p b i : U64) (d : Bool) : ¬ RngKeyA (.Untyped p b i d) := fun h => by
  have := h.2.1; simp [isUtA] at this

/-- Two `Untyped` caps are alike (neither is a key cap). -/
theorem AlikeA.ut (p b i : U64) (d : Bool) (p' b' i' : U64) (d' : Bool) :
    AlikeA (.Untyped p b i d) (.Untyped p' b' i' d') :=
  ⟨iff_of_false (nk_ut _ _ _ _) (nk_ut _ _ _ _), fun h => absurd h (nk_ut _ _ _ _)⟩

/-- (gen 60) **`set_untyped_cap_as_full`**'s effect (`set_untyped_cap_as_full.lk`) **and its write frame** (only the
source's two cap words). -/
theorem cdt.set_untyped_cap_as_full.lkF (hO : OSOK T Ω Sg OS) {s : S} {src : U64} (hsrc : src ∈ OS)
    {sc nc : capability.Cap} (hsc : capA st s src = sc) (hsc0 : sc ≠ .Null) :
    cdt.set_untyped_cap_as_full st s sc nc src ⦃ s1 => WritesIn st s s1 (W7.CapW T Ω Sg) ∧
      (∀ y ∈ OS, L.mem s1 (wa y 16#u64) = L.mem s (wa y 16#u64) ∧ L.mem s1 (wa y 24#u64) = L.mem s (wa y 24#u64)) ∧
      (∀ y ∈ OS, y ≠ src → capA st s1 y = capA st s y) ∧ AlikeA (capA st s1 src) sc ∧ capA st s1 src ≠ .Null ∧
      (capA st s1 src = capA st s src ∨ ∃ p b i d, capA st s1 src = .Untyped p b i d) ⦄ := by
  have same0 : (∀ y ∈ OS, L.mem s (wa y 16#u64) = L.mem s (wa y 16#u64) ∧
      L.mem s (wa y 24#u64) = L.mem s (wa y 24#u64)) ∧ (∀ y ∈ OS, y ≠ src → capA st s y = capA st s y) ∧
      AlikeA (capA st s src) sc ∧ capA st s src ≠ .Null ∧
      (capA st s src = capA st s src ∨ ∃ p b i d, capA st s src = .Untyped p b i d) :=
    ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ _ => rfl, by rw [hsc]; exact AlikeA.refl _, by rw [hsc]; exact hsc0, Or.inl rfl⟩
  have same := And.intro (WritesIn.refl (st := st) s (W7.CapW T Ω Sg)) same0
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
          refine WP.spec_bind (Pₘ := fun _ => True) (by first | p0_auto | p0_split) fun i1 _ => ?_
          have wf0 := CapRt.decode_encWf hd
          have wf : CapRt.EncWf (.Untyped p b i1 d) := wf0
          obtain ⟨w0, w1, he, hr⟩ := CapRt.decode_encode _ wf
          rw [set_cap_eq he, WP.spec_ok]
          refine ⟨WritesIn.cw2 hO (WritesIn.refl (st := st) s (W7.CapW T Ω Sg)) hsrc w0 w1,
            set_cap_links hO hsrc,
            fun y hy hne => capA_wr2_other hO hsrc hy hne, ?_, ?_, Or.inr ⟨p, b, i1, d, capA_wr2_self hO hsrc hr⟩⟩
          · rw [capA_wr2_self hO hsrc hr]; exact AlikeA.ut _ _ _ _ _ _ _ _
          · rw [capA_wr2_self hO hsrc hr]; exact fun h => by cases h
        · rw [if_neg e2]; exact (WP.spec_ok _).2 same
      · rw [if_neg e1]; exact (WP.spec_ok _).2 same
    | _ => exact (WP.spec_ok _).2 same
  | _ => exact (WP.spec_ok _).2 same

/-- **`set_untyped_cap_as_full`** writes only the source's cap words; the source's cap stays alike and non-null. -/
theorem cdt.set_untyped_cap_as_full.lk (hO : OSOK T Ω Sg OS) {s : S} {src : U64} (hsrc : src ∈ OS)
    {sc nc : capability.Cap} (hsc : capA st s src = sc) (hsc0 : sc ≠ .Null) :
    cdt.set_untyped_cap_as_full st s sc nc src ⦃ s1 =>
      (∀ y ∈ OS, L.mem s1 (wa y 16#u64) = L.mem s (wa y 16#u64) ∧ L.mem s1 (wa y 24#u64) = L.mem s (wa y 24#u64)) ∧
      (∀ y ∈ OS, y ≠ src → capA st s1 y = capA st s y) ∧ AlikeA (capA st s1 src) sc ∧ capA st s1 src ≠ .Null ∧
      (capA st s1 src = capA st s src ∨ ∃ p b i d, capA st s1 src = .Untyped p b i d) ⦄ :=
  WP.spec_mono (cdt.set_untyped_cap_as_full.lkF hO hsrc (nc := nc) hsc hsc0) fun _ h => h.2

set_option maxHeartbeats 4000000 in
/-- (gen 60) **`insert_with_cap`'s links and caps, and its write frame** (`insert_with_cap.lr`'s proof with the
written words tracked: every word written is a cap-slot word of `OS`, `W7.CapW`). -/
theorem cdt.insert_with_cap.lrF (hO : OSOK T Ω Sg OS) {s : S} {pv nx : U64 → U64} (hL : LR st OS s pv nx)
    {src dest : U64} {nc sc : capability.Cap} (hsrc : src ∈ OS) (hd : dest ∈ OS) (hsd : src ≠ dest)
    (hdc : obj.sext48 dest = ok dest) (hsc : capA st s src = sc) (hsc0 : sc ≠ .Null) (hw : CapRt.EncWf nc)
    (hnN : nx src ≠ 0#u64 → nx src ∈ OS) :
    cdt.insert_with_cap st s nc sc src dest ⦃ s' => WritesIn st s s' (W7.CapW T Ω Sg) ∧ LR st OS s'
      (fun z => if nx src ≠ 0#u64 ∧ z = nx src then dest else if z = dest then src else pv z)
      (fun z => if z = src then dest else if z = dest then nx src else nx z) ∧
      capA st s' dest = nc ∧ AlikeA (capA st s' src) sc ∧ capA st s' src ≠ .Null ∧
      (∀ y ∈ OS, y ≠ src → y ≠ dest → capA st s' y = capA st s y) ∧
      (capA st s' src = capA st s src ∨ ∃ p b i d, capA st s' src = .Untyped p b i d) ⦄ := by
  have cnN : obj.sext48 (nx src) = ok (nx src) := by rw [← (hL src hsrc).2]; exact nxA_can s src
  unfold cdt.insert_with_cap
  refine WP.spec_bind (P0.objects.is_cap_revocable.p0 nc sc) fun rv _ => ?_
  rw [next_eq, bind_ok, (hL src hsrc).2]
  refine WP.spec_bind (cdt.set_untyped_cap_as_full.lkF hO hsrc (nc := nc) hsc hsc0) ?_
  rintro s1 ⟨W1, k1, c1, a1, n1, u1⟩
  have L1 : LR st OS s1 pv nx := fun z hz => ⟨(k1 z hz).1.trans (hL z hz).1, by
    unfold NxA; rw [(k1 z hz).2]; exact (hL z hz).2⟩
  obtain ⟨w0, w1, he, hr⟩ := CapRt.decode_encode nc hw
  rw [set_cap_eq he, bind_ok]
  have L2 := L1.wr2 hO hd (w0 := w0) (w1 := w1)
  have C2 : capA st (L.wr (L.wr s1 dest w0) (wa dest 8#u64) w1) dest = nc ∧
      capA st (L.wr (L.wr s1 dest w0) (wa dest 8#u64) w1) src = capA st s1 src ∧
      ∀ y ∈ OS, y ≠ src → y ≠ dest → capA st (L.wr (L.wr s1 dest w0) (wa dest 8#u64) w1) y = capA st s y :=
    ⟨capA_wr2_self hO hd hr, capA_wr2_other hO hd hsrc hsd, fun y hy n1 n2 => by
      rw [capA_wr2_other hO hd hy n2]; exact c1 y hy n1⟩
  have W2 := WritesIn.cw2 hO W1 hd w0 w1
  generalize L.wr (L.wr s1 dest w0) (wa dest 8#u64) w1 = s2 at L2 C2 W2 ⊢
  rw [set_prev_eq, bind_ok]
  have L3 := L2.prev hO hd src
  refine WP.spec_bind (set_nf_spec _ dest _ rv rv) ?_
  rintro s4 ⟨w4, rfl, hw4⟩
  have L4 := L3.nw hO hd hw4 cnN
  rw [set_next_eq, bind_ok]
  have L5 := L4.nw hO hsrc
    (link_bits (L.mem (L.wr (L.wr s2 (wa dest 16#u64) src) (wa dest 24#u64) w4) (wa src 24#u64)) dest) hdc
  have C5 := (((CK.refl (st := st) (OS := OS) s2).p hO hd src).n hO hd w4).n hO hsrc
    ((L.mem (L.wr (L.wr s2 (wa dest 16#u64) src) (wa dest 24#u64) w4) (wa src 24#u64) &&& ~~~ obj.MDB_PTR_MASK) |||
      (dest &&& obj.MDB_PTR_MASK))
  have W5 := WritesIn.cwn hO (WritesIn.cwn hO (WritesIn.cwp hO W2 hd src) hd w4) hsrc
    ((L.mem (L.wr (L.wr s2 (wa dest 16#u64) src) (wa dest 24#u64) w4) (wa src 24#u64) &&& ~~~ obj.MDB_PTR_MASK) |||
      (dest &&& obj.MDB_PTR_MASK))
  simp only [obj.Slot.is_null, bind_ok]
  have fin : ∀ s' : S, CK st OS s2 s' →
      capA st s' dest = nc ∧ AlikeA (capA st s' src) sc ∧ capA st s' src ≠ .Null ∧
      (∀ y ∈ OS, y ≠ src → y ≠ dest → capA st s' y = capA st s y) ∧
      (capA st s' src = capA st s src ∨ ∃ p b i d, capA st s' src = .Untyped p b i d) := fun s' hc =>
    ⟨(hc dest hd).trans C2.1, by rw [hc src hsrc, C2.2.1]; exact a1, by rw [hc src hsrc, C2.2.1]; exact n1,
      fun y hy n1 n2 => (hc y hy).trans (C2.2.2 y hy n1 n2), by rw [hc src hsrc, C2.2.1]; exact u1⟩
  split
  · rename_i hn0
    have hN0 : nx src = 0#u64 := by simpa using hn0
    refine (WP.spec_ok _).2 ⟨W5, L5.congr (fun z _ => ?_) (fun _ _ => rfl), fin _ C5⟩
    simp [hN0]
  · rename_i hn0
    have hN0 : nx src ≠ 0#u64 := by simpa using hn0
    rw [set_prev_eq, WP.spec_ok]
    refine ⟨WritesIn.cwp hO W5 (hnN hN0) dest,
      (L5.prev hO (hnN hN0) dest).congr (fun z _ => ?_) (fun _ _ => rfl),
      fin _ (C5.p hO (hnN hN0) dest)⟩
    simp only [ne_eq, hN0, not_false_eq_true, true_and]

/-- **`insert_with_cap`'s links and caps** (module docstring): the new cap into `dest` (`PREV` `src`, `NEXT` the
old `NEXT` `N` of `src`), `src.NEXT := dest`, `N.PREV := dest`. -/
theorem cdt.insert_with_cap.lr (hO : OSOK T Ω Sg OS) {s : S} {pv nx : U64 → U64} (hL : LR st OS s pv nx)
    {src dest : U64} {nc sc : capability.Cap} (hsrc : src ∈ OS) (hd : dest ∈ OS) (hsd : src ≠ dest)
    (hdc : obj.sext48 dest = ok dest) (hsc : capA st s src = sc) (hsc0 : sc ≠ .Null) (hw : CapRt.EncWf nc)
    (hnN : nx src ≠ 0#u64 → nx src ∈ OS) :
    cdt.insert_with_cap st s nc sc src dest ⦃ s' => LR st OS s'
      (fun z => if nx src ≠ 0#u64 ∧ z = nx src then dest else if z = dest then src else pv z)
      (fun z => if z = src then dest else if z = dest then nx src else nx z) ∧
      capA st s' dest = nc ∧ AlikeA (capA st s' src) sc ∧ capA st s' src ≠ .Null ∧
      (∀ y ∈ OS, y ≠ src → y ≠ dest → capA st s' y = capA st s y) ∧
      (capA st s' src = capA st s src ∨ ∃ p b i d, capA st s' src = .Untyped p b i d) ⦄ :=
  WP.spec_mono (cdt.insert_with_cap.lrF hO hL hsrc hd hsd hdc hsc hsc0 hw hnN) fun _ h => h.2

variable {G : List (List U64)}

set_option maxHeartbeats 1000000 in
/-- **`MdbLk ∧ RngOneA64 ∧ KindA` along `cdt::insert_with_cap`** (module docstring): the ghost `insG src dest G`. -/
theorem cdt.insert_with_cap.mdb (hO : OSOK T Ω Sg OS) (h0 : ∀ y ∈ OS, y ≠ 0#u64) {s : S} (hM : MdbLk st OS G s)
    (hRO : RngOneA64 st G s) (hK : KindA st OS s) {src dest : U64} {nc sc : capability.Cap}
    (hsrc : src ∈ G.flatten) (hd : dest ∈ OS) (hd0 : capA st s dest = .Null) (hdc : obj.sext48 dest = ok dest)
    (hsc : capA st s src = sc) (hw : CapRt.EncWf nc) (hnc : nc ≠ .Null) (hA : AlikeA nc sc) :
    cdt.insert_with_cap st s nc sc src dest ⦃ s' => MdbLk st OS (insG src dest G) s' ∧
      RngOneA64 st (insG src dest G) s' ∧ KindA st OS s' ⦄ := by
  have inOS : ∀ y ∈ G.flatten, y ∈ OS := fun y hy => ((hM.members y).1 hy).1
  have F := hM.lkF h0
  have os := inOS src hsrc
  have hs0 : capA st s src ≠ .Null := ((hM.members src).1 hsrc).2
  have hsc0 : sc ≠ .Null := by rw [← hsc]; exact hs0
  have dG : dest ∉ G.flatten := fun hm => ((hM.members dest).1 hm).2 hd0
  have hsd : src ≠ dest := fun e => dG (e ▸ hsrc)
  have hNm : NxA st s src ≠ 0#u64 → NxA st s src ∈ G.flatten := F.nxm _ hsrc
  have hNd : NxA st s src ≠ dest := fun e => by
    have h1 : NxA st s src ≠ 0#u64 := fun e0 => h0 dest hd (e ▸ e0)
    exact dG (e ▸ hNm h1)
  refine WP.spec_mono (cdt.insert_with_cap.lr hO (LR.self s) os hd hsd hdc hsc hsc0 hw
    (fun h => inOS _ (hNm h))) ?_
  rintro s' ⟨hL, ed, es, ns, ek, -⟩
  have hk : ∀ y ∈ OS, y ≠ src → y ≠ dest → capA st s' y = capA st s y := ek
  refine ⟨hM.ins h0 hsrc hd hd0 (by rw [ed]; exact hnc) (fun y hy hyd => ?_) ?_ ?_ ?_ (fun hN => ?_)
    (fun y hy h1 h2 => ?_) (fun y hy h1 h2 => ?_), hRO.ins hM.nodup hsrc dG
    (fun y hy h1 => hk y (inOS y hy) h1 (fun e => dG (e ▸ hy))) (by rw [hsc]; exact es) (by rw [ed, hsc]; exact hA),
    hK.ins os hk (by rw [hsc]; exact es) (by rw [ed, hsc]; exact hA)⟩
  · by_cases e : y = src
    · rw [e]
      exact ⟨fun h => absurd h ns, fun h => absurd h hs0⟩
    · rw [hk y hy e hyd]
  · rw [(hL src os).2]; simp
  · rw [(hL dest hd).1]; simp [hNd.symm]
  · rw [(hL dest hd).2]; simp [hsd.symm]
  · rw [(hL _ (inOS _ (hNm hN))).1]; simp [hN]
  · rw [(hL y hy).2]; simp [h1, h2]
  · rw [(hL y hy).1]; simp [h1, h2]

/-- **`MdbLk ∧ RngOneA64 ∧ KindA` along `cdt::insert`** (cdt.rs:28–31: the source cap read from `src`). -/
theorem cdt.insert.mdb (hO : OSOK T Ω Sg OS) (h0 : ∀ y ∈ OS, y ≠ 0#u64) {s : S} (hM : MdbLk st OS G s)
    (hRO : RngOneA64 st G s) (hK : KindA st OS s) {src dest : U64} {nc : capability.Cap}
    (hsrc : src ∈ G.flatten) (hd : dest ∈ OS) (hd0 : capA st s dest = .Null) (hdc : obj.sext48 dest = ok dest)
    (hw : CapRt.EncWf nc) (hnc : nc ≠ .Null) (hA : AlikeA nc (capA st s src)) :
    cdt.insert st s nc src dest ⦃ s' => MdbLk st OS (insG src dest G) s' ∧
      RngOneA64 st (insG src dest G) s' ∧ KindA st OS s' ⦄ := by
  unfold cdt.insert
  rw [capA_eq, bind_ok]
  exact cdt.insert_with_cap.mdb hO h0 hM hRO hK hsrc hd hd0 hdc rfl hw hnc hA

end ins

end ST
end R
end W7

end

end Fl4ProofsA64.P1
