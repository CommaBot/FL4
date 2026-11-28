/-
P1 (aarch64, gen 54): **`TreeA` (the ghost tree on the chain with `UtInvA`, MdbTreeA) along the cdt.rs steps at
function level** — x86 UntypedUtOps's `insert_utinv` / `move_utinv` / `swap_utinv` / `empty_slot_utinv` and
MdbStepInv's `recap`, over A64's existing function-level link lemmas (`cdt.swap.lrW`, `cdt.move_cap.lr`,
`cdt.insert_with_cap.lr`, `cdt.empty_slot.mdbFLG`).

* `MdbLk.renN`: gen 47's `MdbLk.ren` with the caps compared by null-ness only (`ren`'s proof, members part
  changed) — what a swap / move writing caps other than the slots' own needs (Rotate, Mutate).
* **`TreeA.set_cap`** (in-place `set_cap` of a non-null cap `UA` the old one, e.g. the PageTable map / unmap /
  Assign rewrites once `UA` is shown for them).
* **`cdt.swap.tree`** (two members, any two encodable non-null caps `UA` the replaced ones; tree and ghost renamed
  by `Equiv.swap`, x86 `MdbOK.conj`), **`cdt.cap_swap_for_delete.tree`**, **`cdt.move_cap.tree`** (into a null
  canonical `OS` slot).
* **`cdt.set_untyped_cap_as_full.fullU`**: gen 53's `.full`, plus the source becomes a full `Untyped` exactly when
  the new cap is an `Untyped` of the same region (`SrcU`); **`cdt.insert_with_cap.srcU`** (the later writes keep it).
* **`cdt.insert_with_cap.tree`** / **`cdt.insert.tree`**: the new slot `src`'s child (x86 `MdbOK.insert`,
  `InsCase` left), case hypotheses as gen 53's `.ut` with `UA` for `RA`, plus `hut` (an untyped source has no
  descendants: `derive_cap`'s `ensure_no_children`, by `cdt.ensure_no_children.noDesc`).
* **`cdt.empty_slot.tree`** (x86 `MdbOK.remove`, `UtInvA.rem`; the null-cap path keeps the ghosts).

No named premise; new definitions and theorems only (the hypotheses are case hypotheses of the callers).
-/
import Fl4ProofsA64.P1.MdbTreeA
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts Fl4Proofs.P3

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {Sg : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

section fn
variable {OS : Set U64} {G : List (List U64)} {par : U64 → Option U64}

/-- **`MdbLk` along a renaming with the caps compared by null-ness** (gen 47's `MdbLk.ren`, members part). -/
theorem MdbLk.renN {s s' : S} (h : MdbLk st OS G s) (h0 : ∀ y ∈ OS, y ≠ 0#u64) {x1 x2 : U64} (hx1 : x1 ∈ OS)
    (hx2 : x2 ∈ OS) (hc : ∀ y ∈ OS, (capA st s' (swp x1 x2 y) = .Null ↔ capA st s y = .Null))
    (hn : ∀ y ∈ G.flatten, NxA st s' (swp x1 x2 y) = swp x1 x2 (NxA st s y))
    (hp : ∀ y ∈ G.flatten, L.mem s' (wa (swp x1 x2 y) 16#u64) = swp x1 x2 (L.mem s (wa y 16#u64))) :
    MdbLk st OS (renG x1 x2 G) s' := by
  have hz := swp_zero (h0 x1 hx1) (h0 x2 hx2)
  have mem : ∀ ch ∈ G, ∀ {i : Nat} {a : U64}, ch[i]? = some a → a ∈ G.flatten := fun ch hch _ _ e =>
    List.mem_flatten.2 ⟨ch, hch, List.mem_of_getElem? e⟩
  refine ⟨?_, fun ch hch => ?_, fun ch hch i a b ha hb => ?_, fun ch hch a ha => ?_, fun ch hch a ha => ?_,
    fun y => ?_⟩
  · rw [renG_flat]; exact h.nodup.map (swp_inj x1 x2)
  · obtain ⟨c, hc0, rfl⟩ := List.mem_map.1 hch
    simpa using h.ne_nil c hc0
  · obtain ⟨c, hc0, rfl⟩ := List.mem_map.1 hch
    rw [List.getElem?_map] at ha hb
    obtain ⟨a0, ha0, rfl⟩ := Option.map_eq_some_iff.1 ha
    obtain ⟨b0, hb0, rfl⟩ := Option.map_eq_some_iff.1 hb
    have old := h.chain c hc0 i a0 b0 ha0 hb0
    exact ⟨by rw [hn a0 (mem c hc0 ha0), old.1], by rw [hp b0 (mem c hc0 hb0), old.2]⟩
  · obtain ⟨c, hc0, rfl⟩ := List.mem_map.1 hch
    rw [List.head?_map] at ha
    obtain ⟨a0, ha0, rfl⟩ := Option.map_eq_some_iff.1 ha
    have a0m : a0 ∈ G.flatten := List.mem_flatten.2 ⟨c, hc0, List.mem_of_mem_head? ha0⟩
    rw [hp a0 a0m, h.head c hc0 a0 ha0, hz]
  · obtain ⟨c, hc0, rfl⟩ := List.mem_map.1 hch
    rw [List.getLast?_map] at ha
    obtain ⟨a0, ha0, rfl⟩ := Option.map_eq_some_iff.1 ha
    have a0m : a0 ∈ G.flatten := List.mem_flatten.2 ⟨c, hc0, List.mem_of_getLast? ha0⟩
    rw [hn a0 a0m, h.last c hc0 a0 ha0, hz]
  · rw [mem_renG_flat, h.members]
    constructor
    · rintro ⟨hy, hcy⟩
      have hyO : y ∈ OS := by rw [← swp_swp x1 x2 y]; exact swp_os hx1 hx2 hy
      have e := hc _ hy
      rw [swp_swp] at e
      exact ⟨hyO, fun h' => hcy (e.1 h')⟩
    · rintro ⟨hy, hcy⟩
      refine ⟨swp_os hx1 hx2 hy, fun h' => hcy ?_⟩
      have e := hc _ (swp_os hx1 hx2 hy)
      rw [swp_swp] at e
      exact e.2 h'

/-! ## In-place `set_cap` -/

theorem TreeA.set_cap (hO : OSOK T Ω Sg OS) {s : S} (h : TreeA st OS G par s) {x0 : U64} (hx0 : x0 ∈ OS)
    {c : capability.Cap} {w0 w1 : U64} (hd : capability.Cap.decode w0 w1 = ok c) (hc : c ≠ .Null)
    (hc0 : capA st s x0 ≠ .Null) (ha : UA c (capA st s x0)) :
    TreeA st OS G par (L.wr (L.wr s x0 w0) (wa x0 8#u64) w1) :=
  ⟨h.lk.set_cap hO hx0 hd hc hc0, h.tree, h.ut.recap h.parIn fun y hy => by
    by_cases hyx : y = x0
    · rw [hyx, capA_wr2_self hO hx0 hd]; exact ha
    · rw [capA_wr2_other hO hx0 hy hyx]; exact UA.refl _⟩

/-! ## `swap`, `cap_swap_for_delete`, `move_cap` -/

set_option maxHeartbeats 1000000 in
/-- **`swap`** of two distinct canonical members writing encodable non-null caps alike the replaced ones. -/
theorem cdt.swap.tree (hO : OSOK T Ω Sg OS) {s : S} (hT : TreeA st OS G par s) {x1 x2 : U64}
    {c1 c2 : capability.Cap} (hx1 : x1 ∈ G.flatten) (hx2 : x2 ∈ G.flatten) (hne : x1 ≠ x2)
    (hs1 : obj.sext48 x1 = ok x1) (hs2 : obj.sext48 x2 = ok x2) (hw1 : CapRt.EncWf c1) (hw2 : CapRt.EncWf c2)
    (hn1 : c1 ≠ .Null) (hn2 : c2 ≠ .Null) (ha1 : UA c1 (capA st s x1)) (ha2 : UA c2 (capA st s x2)) :
    cdt.swap st s c1 x1 c2 x2 ⦃ s' => TreeA st OS (renG x1 x2 G) (Mdb.conjPar (Equiv.swap x1 x2) par) s' ⦄ := by
  have hM := hT.lk
  have h0 : ∀ y ∈ OS, y ≠ 0#u64 := hO.nz
  have inOS : ∀ y ∈ G.flatten, y ∈ OS := fun y hy => ((hM.members y).1 hy).1
  have F := hM.lkF h0
  have o1 := inOS x1 hx1
  have o2 := inOS x2 hx2
  refine WP.spec_mono (cdt.swap.lrW hO (LR.self s) o1 o2 hne hs1 hs2 hw1 hw2
    (fun h => inOS _ (F.pvm _ hx1 h)) (fun h => inOS _ (F.nxm _ hx1 h))
    (fun h => inOS _ (F.pvm _ hx2 h)) (fun h => inOS _ (F.nxm _ hx2 h))) ?_
  rintro s' ⟨hL, e1, e2, ek⟩
  have hc : ∀ y ∈ OS, UA (capA st s' (swp x1 x2 y)) (capA st s y) := by
    intro y hy
    unfold swp
    by_cases a1 : y = x1
    · rw [a1, if_pos rfl, e2]; exact ha1
    · rw [if_neg a1]
      by_cases a2 : y = x2
      · rw [a2, if_pos rfl, e1]; exact ha2
      · rw [if_neg a2, ek y hy a1 a2]; exact UA.refl _
  have hnul : ∀ y ∈ OS, (capA st s' (swp x1 x2 y) = .Null ↔ capA st s y = .Null) := by
    intro y hy
    unfold swp
    by_cases a1 : y = x1
    · rw [a1, if_pos rfl, e2]
      exact ⟨fun h => absurd h hn1, fun h => absurd h ((hM.members x1).1 hx1).2⟩
    · rw [if_neg a1]
      by_cases a2 : y = x2
      · rw [a2, if_pos rfl, e1]
        exact ⟨fun h => absurd h hn2, fun h => absurd h ((hM.members x2).1 hx2).2⟩
      · rw [if_neg a2, ek y hy a1 a2]
  have sw : ∀ y ∈ G.flatten, swp x1 x2 y ∈ OS := fun y hy => swp_os o1 o2 (inOS y hy)
  refine ⟨hM.renN h0 o1 o2 hnul (fun y hy => ?_) (fun y hy => ?_), by rw [renG_eq]; exact hT.tree.conj _, ?_⟩
  · rw [(hL _ (sw y hy)).2, swp_tr, swp_tr]; exact (LkAbs.sw_ok F hx1 hx2 hne hy).1
  · rw [(hL _ (sw y hy)).1, swp_tr, swp_tr]; exact (LkAbs.sw_ok F hx1 hx2 hne hy).2
  · refine hT.ut.ren hT.parIn (Equiv.swap x1 x2) (fun y hy => ?_) (fun y hy => ?_) (fun y hy => ?_)
    · rw [swap_eq_swp]; exact swp_os o1 o2 hy
    · rw [Equiv.symm_swap, swap_eq_swp]; exact swp_os o1 o2 hy
    · rw [swap_eq_swp]; exact hc y hy

/-- **`cap_swap_for_delete`** of two canonical members (equal slots return the state). -/
theorem cdt.cap_swap_for_delete.tree (hO : OSOK T Ω Sg OS) {s : S} (hT : TreeA st OS G par s) {x1 x2 : U64}
    (hx1 : x1 ∈ G.flatten) (hx2 : x2 ∈ G.flatten) (hs1 : obj.sext48 x1 = ok x1) (hs2 : obj.sext48 x2 = ok x2) :
    cdt.cap_swap_for_delete st s x1 x2 ⦃ s' => ∃ G' : List (List U64), ∃ par' : U64 → Option U64,
      TreeA st OS G' par' s' ⦄ := by
  unfold cdt.cap_swap_for_delete
  simp only [obj.Slot.Insts.CoreCmpPartialEqSlot.eq, bind_ok]
  split
  · exact (WP.spec_ok _).2 ⟨G, par, hT⟩
  · rename_i hne'
    have hne : x1 ≠ x2 := by simpa using hne'
    rw [capA_eq, bind_ok, capA_eq, bind_ok]
    exact WP.spec_mono (cdt.swap.tree hO hT hx1 hx2 hne hs1 hs2 (CapRt.decodeF_encWf _ _)
      (CapRt.decodeF_encWf _ _) ((hT.lk.members x1).1 hx1).2 ((hT.lk.members x2).1 hx2).2 (UA.refl _) (UA.refl _))
      fun s' h => ⟨_, _, h⟩

set_option maxHeartbeats 1000000 in
/-- **`move_cap`** of a member into a null canonical slot, the new cap non-null, encodable, alike the source's. -/
theorem cdt.move_cap.tree (hO : OSOK T Ω Sg OS) {s : S} (hT : TreeA st OS G par s) {src dest : U64}
    {nc : capability.Cap} (hsG : src ∈ G.flatten) (hd : dest ∈ OS) (hd0 : capA st s dest = .Null)
    (hdc : obj.sext48 dest = ok dest) (hw : CapRt.EncWf nc) (hn : nc ≠ .Null) (hal : UA nc (capA st s src)) :
    cdt.move_cap st s nc src dest ⦃ s' => TreeA st OS (renG dest src G)
      (Mdb.conjPar (Equiv.swap dest src) par) s' ⦄ := by
  have hM := hT.lk
  have h0 : ∀ y ∈ OS, y ≠ 0#u64 := hO.nz
  have inOS : ∀ y ∈ G.flatten, y ∈ OS := fun y hy => ((hM.members y).1 hy).1
  have F := hM.lkF h0
  have hsrc := inOS src hsG
  have hs0 : capA st s src ≠ .Null := ((hM.members src).1 hsG).2
  have hdG : dest ∉ G.flatten := fun m => ((hM.members dest).1 m).2 hd0
  have hsd : src ≠ dest := fun e => hdG (e ▸ hsG)
  have r1 : ∀ y, y ∈ G.flatten → NxA st s y ≠ dest ∧ L.mem s (wa y 16#u64) ≠ dest :=
    fun y hy => ⟨fun e => hdG (by rw [← e]; exact F.nxm y hy (by rw [e]; exact h0 dest hd)),
      fun e => hdG (by rw [← e]; exact F.pvm y hy (by rw [e]; exact h0 dest hd))⟩
  refine WP.spec_mono (cdt.move_cap.lr hO (LR.self s) hsrc hd hsd hdc hw
    (fun h => inOS _ (F.pvm _ hsG h)) (fun h => inOS _ (F.nxm _ hsG h))) ?_
  rintro s' ⟨hL, ed, es, ek⟩
  have hc : ∀ y ∈ OS, UA (capA st s' (swp dest src y)) (capA st s y) := by
    intro y hy
    unfold swp
    by_cases a1 : y = dest
    · rw [a1, if_pos rfl, es, hd0]; exact UA.refl _
    · rw [if_neg a1]
      by_cases a2 : y = src
      · rw [a2, if_pos rfl, ed]; exact hal
      · rw [if_neg a2, ek y hy a2 a1]; exact UA.refl _
  have hnul : ∀ y ∈ OS, (capA st s' (swp dest src y) = .Null ↔ capA st s y = .Null) := by
    intro y hy
    unfold swp
    by_cases a1 : y = dest
    · rw [a1, if_pos rfl, es, hd0]
    · rw [if_neg a1]
      by_cases a2 : y = src
      · rw [a2, if_pos rfl, ed]; exact ⟨fun h => absurd h hn, fun h => absurd h hs0⟩
      · rw [if_neg a2, ek y hy a2 a1]
  have sw : ∀ y ∈ G.flatten, swp dest src y ∈ OS := fun y hy => swp_os hd hsrc (inOS y hy)
  have key : ∀ y ∈ G.flatten,
      LkAbs.mN 0#u64 (fun z => L.mem s (wa z 16#u64)) (NxA st s) dest src (LkAbs.tr dest src y) =
        LkAbs.tr dest src (NxA st s y) ∧
      LkAbs.mP 0#u64 (fun z => L.mem s (wa z 16#u64)) (NxA st s) dest src (LkAbs.tr dest src y) =
        LkAbs.tr dest src (L.mem s (wa y 16#u64)) :=
    fun y hy => LkAbs.mv_ok F hdG r1 hsG hy
  refine ⟨hM.renN h0 hd hsrc hnul (fun y hy => ?_) (fun y hy => ?_), by rw [renG_eq]; exact hT.tree.conj _, ?_⟩
  · rw [(hL _ (sw y hy)).2, swp_tr, swp_tr]; exact (key y hy).1
  · rw [(hL _ (sw y hy)).1, swp_tr, swp_tr]; exact (key y hy).2
  · refine hT.ut.ren hT.parIn (Equiv.swap dest src) (fun y hy => ?_) (fun y hy => ?_) (fun y hy => ?_)
    · rw [swap_eq_swp]; exact swp_os hd hsrc hy
    · rw [Equiv.symm_swap, swap_eq_swp]; exact swp_os hd hsrc hy
    · rw [swap_eq_swp]; exact hc y hy

/-! ## `set_untyped_cap_as_full`, `insert_with_cap`, `insert` -/

/-- The source's cap `d` after `set_untyped_cap_as_full sc nc`: `FullA`, and full when `nc` is an `Untyped` of
`sc`'s region. -/
def SrcU (d sc nc : capability.Cap) : Prop :=
  FullA d sc ∧ ∀ p b i e i' e', sc = .Untyped p b i e → nc = .Untyped p b i' e' →
    ∃ i1, d = .Untyped p b i1 e ∧ i1.val = 2 ^ b.val

/-- **`set_untyped_cap_as_full`** (gen 53's `.full` with the full case named). -/
theorem cdt.set_untyped_cap_as_full.fullU (hO : OSOK T Ω Sg OS) {s : S} {src : U64} (hsrc : src ∈ OS)
    {sc nc : capability.Cap} (hsc : capA st s src = sc) :
    cdt.set_untyped_cap_as_full st s sc nc src ⦃ s1 => SrcU (capA st s1 src) sc nc ⦄ := by
  have same : FullA (capA st s src) sc := Or.inl hsc
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
          refine WP.spec_bind (shl1_val hb) fun i1 hi1 => ?_
          have wf : CapRt.EncWf (.Untyped p b i1 d) := wf0
          obtain ⟨w0, w1, he, hr⟩ := CapRt.decode_encode _ wf
          rw [set_cap_eq he, WP.spec_ok]
          refine ⟨Or.inr ⟨p, b, i, d, i1, rfl, capA_wr2_self hO hsrc hr, hi1⟩, fun q bb ii ee ii' ee' h1 _ => ?_⟩
          injection h1 with a1 a2 a3 a4
          subst a1 a2 a3 a4
          exact ⟨i1, capA_wr2_self hO hsrc hr, hi1⟩
        · rw [if_neg e2]
          refine (WP.spec_ok _).2 ⟨same, fun q bb ii ee ii' ee' h1 h2 => ?_⟩
          injection h1 with a1 a2; injection h2 with b1 b2
          exact absurd (a2.trans b2.symm) e2
      · rw [if_neg e1]
        refine (WP.spec_ok _).2 ⟨same, fun q bb ii ee ii' ee' h1 h2 => ?_⟩
        injection h1 with a1 a2; injection h2 with b1 b2
        exact absurd (a1.trans b1.symm) e1
    | _ => exact (WP.spec_ok _).2 ⟨same, fun _ _ _ _ _ _ _ h2 => by cases h2⟩
  | _ => exact (WP.spec_ok _).2 ⟨same, fun _ _ _ _ _ _ h1 _ => by cases h1⟩

set_option maxHeartbeats 1000000 in
/-- **`insert_with_cap`'s effect on the source's cap** (gen 53's `.srcF` with `SrcU`). -/
theorem cdt.insert_with_cap.srcU (hO : OSOK T Ω Sg OS) {s : S} {src dest : U64} {nc sc : capability.Cap}
    (hsrc : src ∈ OS) (hd : dest ∈ OS) (hsd : src ≠ dest) (hsc : capA st s src = sc) (hw : CapRt.EncWf nc)
    (hnN : NxA st s src ≠ 0#u64 → NxA st s src ∈ OS) :
    cdt.insert_with_cap st s nc sc src dest ⦃ s' => SrcU (capA st s' src) sc nc ⦄ := by
  unfold cdt.insert_with_cap
  refine WP.spec_bind (P0.objects.is_cap_revocable.p0 nc sc) fun rv _ => ?_
  rw [next_eq, bind_ok]
  refine WP.spec_bind (cdt.set_untyped_cap_as_full.fullU hO hsrc (nc := nc) hsc) fun s1 h1 => ?_
  obtain ⟨w0, w1, he, hr⟩ := CapRt.decode_encode nc hw
  rw [set_cap_eq he, bind_ok]
  have C2 : capA st (L.wr (L.wr s1 dest w0) (wa dest 8#u64) w1) src = capA st s1 src :=
    capA_wr2_other hO hd hsrc hsd
  generalize L.wr (L.wr s1 dest w0) (wa dest 8#u64) w1 = s2 at C2 ⊢
  rw [set_prev_eq, bind_ok]
  refine WP.spec_bind (set_nf_spec _ dest _ rv rv) ?_
  rintro s4 ⟨w4, rfl, -⟩
  rw [set_next_eq, bind_ok]
  have fin : ∀ s' : S, CK st OS s2 s' → SrcU (capA st s' src) sc nc := fun s' hc => by
    rw [hc src hsrc, C2]; exact h1
  simp only [obj.Slot.is_null, bind_ok]
  split
  · exact (WP.spec_ok _).2 (fin _ ((((CK.refl (st := st) (OS := OS) s2).p hO hd src).n hO hd w4).n hO hsrc _))
  · rename_i hn0
    have hN0 : NxA st s src ≠ 0#u64 := by simpa using hn0
    rw [set_prev_eq, WP.spec_ok]
    exact fin _ (((((CK.refl (st := st) (OS := OS) s2).p hO hd src).n hO hd w4).n hO hsrc _).p hO (hnN hN0) dest)

set_option maxHeartbeats 2000000 in
/-- **`insert_with_cap`** of a non-null encodable cap alike the source's into a null canonical slot, as `src`'s
child; an untyped source has no descendants (`hut`). -/
theorem cdt.insert_with_cap.tree (hO : OSOK T Ω Sg OS) {s : S} (hT : TreeA st OS G par s) {src dest : U64}
    {nc sc : capability.Cap} (hsrc : src ∈ G.flatten) (hd : dest ∈ OS) (hd0 : capA st s dest = .Null)
    (hdc : obj.sext48 dest = ok dest) (hsc : capA st s src = sc) (hw : CapRt.EncWf nc) (hnc : nc ≠ .Null)
    (hA : UA nc sc) (hut : isUtA sc = true → ∀ y, ¬ Mdb.Desc par y src) :
    cdt.insert_with_cap st s nc sc src dest ⦃ s' => TreeA st OS (insG src dest G)
      (Function.update par dest (some src)) s' ⦄ := by
  have hM := hT.lk
  have h0 : ∀ y ∈ OS, y ≠ 0#u64 := hO.nz
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
  refine WP.spec_mono (WP.spec_and (cdt.insert_with_cap.lr hO (LR.self s) os hd hsd hdc hsc hsc0 hw
    (fun h => inOS _ (hNm h))) (cdt.insert_with_cap.srcU hO os hd hsd hsc hw (fun h => inOS _ (hNm h)))) ?_
  rintro s' ⟨⟨hL, ed, -, ns, ek, -⟩, hsu⟩
  have hk : ∀ y ∈ OS, y ≠ src → y ≠ dest → capA st s' y = capA st s y := ek
  have hLk : MdbLk st OS (insG src dest G) s' := by
    refine hM.ins h0 hsrc hd hd0 (by rw [ed]; exact hnc) (fun y hy hyd => ?_) ?_ ?_ ?_ (fun hN => ?_)
      (fun y hy h1 h2 => ?_) (fun y hy h1 h2 => ?_)
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
  have hfib : ∀ p b i e, capA st s src = .Untyped p b i e → i.val ≤ 2 ^ b.val :=
    fun p b i e h => hT.ut.fib src os p b i e h
  have hs : UA (capA st s' src) (capA st s src) := by
    rw [hsc]; exact hsu.1.ua fun p b i e h => hfib p b i e (hsc.trans h)
  have hdA : UA (capA st s' dest) (capA st s src) := by rw [ed, hsc]; exact hA
  refine ⟨hLk, by rw [insG_eq]; exact hT.tree.insert hsrc dG (Or.inl rfl), ?_⟩
  refine hT.ut.ins hT.parIn os hd hsd (fun z e => dG (hT.tree.par_mem z dest e).2) ?_ hk hs hdA
    (fun p b i e h => ?_) (fun hu => hut (by rw [← hsc]; exact hu))
  · cases e : par dest with
    | none => rfl
    | some q => exact absurd (hT.tree.par_mem dest q e).1 dG
  · rw [ed] at h
    obtain ⟨i0, e0, hsc0', -, -⟩ := hA.ut p b i e h
    obtain ⟨i1, h1, h2⟩ := hsu.2 p b i0 e0 i e hsc0' h
    exact ⟨i1, e0, h1, h2⟩

/-- **`insert`** (the source cap read from `src`). -/
theorem cdt.insert.tree (hO : OSOK T Ω Sg OS) {s : S} (hT : TreeA st OS G par s) {src dest : U64}
    {nc : capability.Cap} (hsrc : src ∈ G.flatten) (hd : dest ∈ OS) (hd0 : capA st s dest = .Null)
    (hdc : obj.sext48 dest = ok dest) (hw : CapRt.EncWf nc) (hnc : nc ≠ .Null) (hA : UA nc (capA st s src))
    (hut : isUtA (capA st s src) = true → ∀ y, ¬ Mdb.Desc par y src) :
    cdt.insert st s nc src dest ⦃ s' => TreeA st OS (insG src dest G) (Function.update par dest (some src)) s' ⦄ := by
  unfold cdt.insert
  rw [capA_eq, bind_ok]
  exact cdt.insert_with_cap.tree hO hT hsrc hd hd0 hdc rfl hw hnc hA hut

/-! ## `empty_slot` -/

set_option maxHeartbeats 1000000 in
/-- **`empty_slot`** of an `OS` slot (gen 49's cleanup hypotheses): `x` removed from the tree (its children get its
parent), or nothing on the null-cap path. -/
theorem cdt.empty_slot.tree {A : Type _} {ar : machine.Arch A} (hO : OSOK T Ω Sg OS) {s : S}
    (hT : TreeA st OS G par s) (hRO : RngOneA64 st G s) (hK : KindA st OS s) {a : A} {x : U64} (hx : x ∈ OS)
    {cl : capability.Cap} {Pw : U64 → Prop} (hpw : ∀ b, Pw b → ¬ InOS OS b)
    (hpcd : ∀ (s1 : S) (a1 : A), L.ksb s1 = L.ksb s →
      objects.post_cap_deletion st ar s1 a1 cl ⦃ r => WritesIn st s1 r.1 Pw ⦄) :
    cdt.empty_slot st ar s a x cl ⦃ r => ∃ G' : List (List U64), ∃ par' : U64 → Option U64,
      TreeA st OS G' par' r.1 ⦄ := by
  refine WP.spec_mono (cdt.empty_slot.mdbFLG hO hO.nz hT.lk hRO hK hx hpw hpcd) ?_
  rintro r ⟨⟨G', hG1, hG2, hM', -, -, hcr, -, hx0, -⟩, -, -⟩
  by_cases hn : capA st s x = .Null
  · rw [hG1 hn] at hM'
    refine ⟨G, par, hM', hT.tree, hT.ut.recap hT.parIn fun y hy => ?_⟩
    by_cases e : y = x
    · rw [e, hx0, hn]; exact UA.refl _
    · rw [hcr y hy e]; exact UA.refl _
  · refine ⟨G', Mdb.removePar x par, hM', by rw [hG2 hn, remG_eq]; exact hT.tree.remove (hT.noself x),
      hT.ut.rem hT.parIn (hT.noself x) hx0 hcr⟩

end fn

end ST
end R
end W7

end

end Fl4ProofsA64.P1
