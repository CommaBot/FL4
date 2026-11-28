/-
P1 (aarch64, gen 47): **`MdbLk`, `RngOneA64` and `KindA` along the insertion of a slot after another** — the data
step of `cdt::insert` / `insert_with_cap` (cdt.rs:28–46: the new cap goes into `dest`, right after `src` in `src`'s
chain; `dest`'s `PREV` = `src`, its `NEXT` = `src`'s old `NEXT` `N`, `src`'s `NEXT` = `dest`, `N`'s `PREV` = `dest`).

* Ghost: `insA src dest c` (`dest` after `src`), `insG src dest G`; `insA_idx`, `insG_perm`
  (`(insG …).flatten ~ dest :: G.flatten`).
* **`MdbLk.ins`**: `dest` an `OS` slot outside the ghost (null cap), `src` a member; after: `dest` non-null, the
  other slots' null-ness kept, the four links above, every other `NEXT` (off `src`, `dest`) and `PREV` (off `dest`,
  `N`) kept ⇒ `MdbLk OS (insG src dest G)`.
* `AlikeA d c`: same key, and for a key cap the same class and kind (`derive_cap` / `update_cap_data` /
  `set_untyped_cap_as_full` keep them, objects.rs); **`RngOneA64.ins`**, **`KindA.ins`** for a new cap alike the
  source's (Copy / Mint / Move-free insertions; the IRQ handler issue has neither cap a key). Retype
  (`insert_new_cap`, fresh objects in an untyped's free region) is not this step.

No named premise.
-/
import Fl4ProofsA64.P1.MdbSwap
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

/-- `dest` inserted right after `src`. -/
def insA (src dest : U64) : List U64 → List U64
  | [] => []
  | a :: l => if a = src then a :: dest :: l else a :: insA src dest l

/-- The ghost with `dest` inserted after `src`. -/
def insG (src dest : U64) (G : List (List U64)) : List (List U64) := G.map (insA src dest)

theorem insA_of_not_mem {src dest : U64} : ∀ {c : List U64}, src ∉ c → insA src dest c = c
  | [], _ => rfl
  | a :: l, h => by
    have ha : a ≠ src := fun e => h (by rw [e]; exact List.mem_cons.2 (Or.inl rfl))
    have hl : src ∉ l := fun e => h (List.mem_cons.2 (Or.inr e))
    unfold insA; rw [if_neg ha, insA_of_not_mem hl]

theorem insA_perm {src dest : U64} : ∀ {c : List U64}, src ∈ c → (insA src dest c).Perm (dest :: c)
  | [], h => by simp at h
  | a :: l, h => by
    unfold insA
    split
    · exact List.Perm.swap dest a l
    · rename_i ha
      have hl : src ∈ l := (List.mem_cons.1 h).resolve_left (fun e => ha e.symm)
      exact ((insA_perm hl).cons a).trans (List.Perm.swap dest a l)

theorem insG_perm {src dest : U64} : ∀ {G : List (List U64)}, G.flatten.Nodup → src ∈ G.flatten →
    (insG src dest G).flatten.Perm (dest :: G.flatten)
  | [], _, h => by simp at h
  | c :: G, hnd, h => by
    unfold insG
    rw [List.map_cons, List.flatten_cons, List.flatten_cons]
    rw [List.flatten_cons] at hnd h
    by_cases hc : src ∈ c
    · have hG : src ∉ G.flatten := fun hm => List.disjoint_of_nodup_append hnd hc hm
      have e : G.map (insA src dest) = G := by
        refine (List.map_congr_left fun d hd => ?_).trans (List.map_id' G)
        exact insA_of_not_mem fun hm => hG (List.mem_flatten.2 ⟨d, hd, hm⟩)
      rw [e]
      exact (insA_perm hc).append_right _
    · have hG : src ∈ G.flatten := (List.mem_append.1 h).resolve_left hc
      rw [insA_of_not_mem hc]
      have ih := insG_perm (dest := dest) hnd.of_append_right hG
      unfold insG at ih
      exact (ih.append_left c).trans List.perm_middle

theorem insA_idx {src dest : U64} : ∀ {c : List U64} {i : Nat}, c.Nodup → c[i]? = some src → ∀ n : Nat,
    (insA src dest c)[n]? = if n ≤ i then c[n]? else if n = i + 1 then some dest else c[n - 1]?
  | [], _, _, hi, _ => by simp at hi
  | a :: l, 0, _, hi, n => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    unfold insA; rw [if_pos rfl]
    rcases n with _ | _ | m
    · simp
    · simp
    · simp only [List.getElem?_cons_succ]
      rw [if_neg (by omega), if_neg (by omega), show m + 1 + 1 - 1 = m + 1 by omega, List.getElem?_cons_succ]
  | a :: l, j + 1, hnd, hi, n => by
    simp only [List.getElem?_cons_succ] at hi
    have ha : a ≠ src := fun e => (List.nodup_cons.1 hnd).1 (e ▸ List.mem_of_getElem? hi)
    unfold insA; rw [if_neg ha]
    rcases n with _ | m
    · simp
    · rw [List.getElem?_cons_succ, insA_idx (List.nodup_cons.1 hnd).2 hi m]
      by_cases h1 : m ≤ j
      · rw [if_pos h1, if_pos (show m + 1 ≤ j + 1 by omega), List.getElem?_cons_succ]
      · rw [if_neg h1, if_neg (show ¬ (m + 1 ≤ j + 1) by omega)]
        by_cases h2 : m = j + 1
        · rw [if_pos h2, if_pos (show m + 1 = j + 1 + 1 by omega)]
        · rw [if_neg h2, if_neg (show ¬ (m + 1 = j + 1 + 1) by omega), show m + 1 - 1 = (m - 1) + 1 by omega,
            List.getElem?_cons_succ]

theorem insA_len {src dest : U64} {c : List U64} (h : src ∈ c) : (insA src dest c).length = c.length + 1 := by
  rw [(insA_perm h).length_eq]; rfl

theorem insG_mem {src dest : U64} {G : List (List U64)} {c' : List U64} (h : c' ∈ insG src dest G) :
    ∃ c ∈ G, c' = insA src dest c := by
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 h; exact ⟨c, hc, rfl⟩

/-- A cap alike another: same key, and for a key cap the same class and kind. -/
def AlikeA (d c : capability.Cap) : Prop :=
  (RngKeyA d ↔ RngKeyA c) ∧ (RngKeyA c → clsA d = clsA c ∧ kindA d = kindA c)

theorem AlikeA.refl (c : capability.Cap) : AlikeA c c := ⟨Iff.rfl, fun _ => ⟨rfl, rfl⟩⟩

theorem ptrA_of_cls {c d : capability.Cap} (h : clsA d = clsA c) : ptrA d = ptrA c := congrArg Prod.fst h

section ins
variable {OS : Set U64} {G : List (List U64)}

/-- **`MdbLk` along the insertion of `dest` after `src`** (module docstring). -/
theorem MdbLk.ins {s s' : S} (h : MdbLk st OS G s) (h0 : ∀ y ∈ OS, y ≠ 0#u64) {src dest : U64}
    (hsrc : src ∈ G.flatten) (hd : dest ∈ OS) (hd0 : capA st s dest = .Null) (hd1 : capA st s' dest ≠ .Null)
    (hn : ∀ y ∈ OS, y ≠ dest → (capA st s' y = .Null ↔ capA st s y = .Null))
    (l1 : NxA st s' src = dest) (l2 : L.mem s' (wa dest 16#u64) = src) (l3 : NxA st s' dest = NxA st s src)
    (l4 : NxA st s src ≠ 0#u64 → L.mem s' (wa (NxA st s src) 16#u64) = dest)
    (hnx : ∀ y ∈ OS, y ≠ src → y ≠ dest → NxA st s' y = NxA st s y)
    (hpv : ∀ y ∈ OS, y ≠ dest → y ≠ NxA st s src → L.mem s' (wa y 16#u64) = L.mem s (wa y 16#u64)) :
    MdbLk st OS (insG src dest G) s' := by
  have hnd := h.nodup
  have inOS : ∀ y ∈ G.flatten, y ∈ OS := fun y hy => ((h.members y).1 hy).1
  have dG : dest ∉ G.flatten := fun hm => ((h.members dest).1 hm).2 hd0
  have hperm := insG_perm (dest := dest) hnd hsrc
  obtain ⟨cs, hcs0, hscs⟩ := List.mem_flatten.1 hsrc
  obtain ⟨is, his, hsi⟩ := List.getElem_of_mem hscs
  have esi : cs[is]? = some src := by rw [getElem?_of_lt his, hsi]
  have hcsn := ch_nodup hnd hcs0
  have memc : ∀ {c : List U64}, c ∈ G → ∀ {n : Nat} {y : U64}, c[n]? = some y → y ∈ G.flatten :=
    fun hc0 _ _ e => List.mem_flatten.2 ⟨_, hc0, List.mem_of_getElem? e⟩
  have ned : ∀ {c : List U64}, c ∈ G → ∀ {n : Nat} {y : U64}, c[n]? = some y → y ≠ dest :=
    fun hc0 _ _ e he => dG (he ▸ memc hc0 e)
  -- `src` and `N` are located in `cs`
  have keyS : ∀ {c : List U64}, c ∈ G → ∀ {n : Nat}, c[n]? = some src → c = cs ∧ n = is := by
    intro c hc0 n e
    have hcc : c = cs := ch_eq hnd hc0 hcs0 (List.mem_of_getElem? e) hscs
    subst hcc; exact ⟨rfl, nd_idx hcsn e esi⟩
  have keyN : ∀ {c : List U64}, c ∈ G → ∀ {n : Nat} {y : U64}, c[n]? = some y → y = NxA st s src →
      c = cs ∧ n = is + 1 := by
    intro c hc0 n y hy e
    have hN0 : NxA st s src ≠ 0#u64 := e ▸ h0 y (inOS y (memc hc0 hy))
    have ej := h.next_idx hcs0 esi hN0
    have hcc : c = cs := ch_eq hnd hc0 hcs0 (List.mem_of_getElem? hy)
      (by rw [e]; exact List.mem_of_getElem? ej)
    subst hcc
    exact ⟨rfl, nd_idx hcsn hy (e ▸ ej)⟩
  refine ⟨hperm.nodup_iff.2 (List.nodup_cons.2 ⟨dG, hnd⟩), fun ch hch => ?_, fun ch hch n a b ha hb => ?_,
    fun ch hch a ha => ?_, fun ch hch a ha => ?_, fun y => ?_⟩
  · obtain ⟨c, hc0, rfl⟩ := insG_mem hch
    have hne := h.ne_nil c hc0
    by_cases hsc : src ∈ c
    · intro e; have := insA_len (dest := dest) hsc; rw [e] at this; simp at this
    · rw [insA_of_not_mem hsc]; exact hne
  · -- chain
    obtain ⟨c, hc0, rfl⟩ := insG_mem hch
    by_cases hsc : src ∈ c
    · obtain rfl : c = cs := ch_eq hnd hc0 hcs0 hsc hscs
      rw [insA_idx hcsn esi] at ha hb
      by_cases h1 : n + 1 ≤ is
      · rw [if_pos (by omega)] at ha; rw [if_pos h1] at hb
        have old := h.chain c hc0 n a b ha hb
        refine ⟨?_, ?_⟩
        · rw [hnx a (inOS a (memc hc0 ha)) (fun e => by have := (keyS hc0 (e ▸ ha)).2; omega)
            (ned hc0 ha)]; exact old.1
        · rw [hpv b (inOS b (memc hc0 hb)) (ned hc0 hb) (fun e => by have := (keyN hc0 hb e).2; omega)]
          exact old.2
      · by_cases h2 : n = is
        · subst h2
          rw [if_pos (Nat.le_refl _)] at ha; rw [if_neg h1, if_pos rfl] at hb
          rw [esi] at ha
          obtain rfl := Option.some.inj ha; obtain rfl := Option.some.inj hb
          exact ⟨l1, l2⟩
        · by_cases h3 : n = is + 1
          · subst h3
            rw [if_neg (by omega), if_pos rfl] at ha; rw [if_neg (by omega), if_neg (by omega),
              show is + 1 + 1 - 1 = is + 1 by omega] at hb
            obtain rfl := Option.some.inj ha
            have hb' := h.chain c hc0 is src b esi hb
            have hb0 : b ≠ 0#u64 := h0 b (inOS b (memc hc0 hb))
            refine ⟨by rw [l3, hb'.1], ?_⟩
            have := l4 (by rw [hb'.1]; exact hb0)
            rw [hb'.1] at this; exact this
          · rw [if_neg (by omega), if_neg (by omega)] at ha; rw [if_neg (by omega), if_neg (by omega)] at hb
            rw [show n + 1 - 1 = (n - 1) + 1 by omega] at hb
            have old := h.chain c hc0 (n - 1) a b ha hb
            refine ⟨?_, ?_⟩
            · rw [hnx a (inOS a (memc hc0 ha)) (fun e => by have := (keyS hc0 (e ▸ ha)).2; omega)
                (ned hc0 ha)]; exact old.1
            · rw [hpv b (inOS b (memc hc0 hb)) (ned hc0 hb) (fun e => by have := (keyN hc0 hb e).2; omega)]
              exact old.2
    · rw [insA_of_not_mem hsc] at ha hb
      have old := h.chain c hc0 n a b ha hb
      refine ⟨?_, ?_⟩
      · rw [hnx a (inOS a (memc hc0 ha)) (fun e => hsc (e ▸ List.mem_of_getElem? ha)) (ned hc0 ha)]
        exact old.1
      · rw [hpv b (inOS b (memc hc0 hb)) (ned hc0 hb)
          (fun e => hsc ((keyN hc0 hb e).1 ▸ hscs))]; exact old.2
  · -- head
    obtain ⟨c, hc0, rfl⟩ := insG_mem hch
    rw [List.head?_eq_getElem?] at ha
    by_cases hsc : src ∈ c
    · obtain rfl : c = cs := ch_eq hnd hc0 hcs0 hsc hscs
      rw [insA_idx hcsn esi, if_pos (Nat.zero_le _)] at ha
      rw [hpv a (inOS a (memc hc0 ha)) (ned hc0 ha) (fun e => by have := (keyN hc0 ha e).2; omega)]
      exact h.head c hc0 a (by rw [List.head?_eq_getElem?]; exact ha)
    · rw [insA_of_not_mem hsc] at ha
      rw [hpv a (inOS a (memc hc0 ha)) (ned hc0 ha) (fun e => hsc ((keyN hc0 ha e).1 ▸ hscs))]
      exact h.head c hc0 a (by rw [List.head?_eq_getElem?]; exact ha)
  · -- last
    obtain ⟨c, hc0, rfl⟩ := insG_mem hch
    rw [List.getLast?_eq_getElem?] at ha
    by_cases hsc : src ∈ c
    · obtain rfl : c = cs := ch_eq hnd hc0 hcs0 hsc hscs
      rw [insA_len hsc, insA_idx hcsn esi, show c.length + 1 - 1 = c.length by omega] at ha
      by_cases hl : is + 1 = c.length
      · rw [if_neg (by omega), if_pos hl.symm] at ha
        obtain rfl := Option.some.inj ha
        rw [l3]
        exact h.last c hc0 src (by rw [List.getLast?_eq_getElem?, ← hl, show is + 1 - 1 = is by omega]; exact esi)
      · rw [if_neg (by omega), if_neg (by omega)] at ha
        rw [hnx a (inOS a (memc hc0 ha)) (fun e => by have := (keyS hc0 (e ▸ ha)).2; omega) (ned hc0 ha)]
        exact h.last c hc0 a (by rw [List.getLast?_eq_getElem?]; exact ha)
    · rw [insA_of_not_mem hsc] at ha
      rw [hnx a (inOS a (memc hc0 ha)) (fun e => hsc (e ▸ List.mem_of_getElem? ha)) (ned hc0 ha)]
      exact h.last c hc0 a (by rw [List.getLast?_eq_getElem?]; exact ha)
  · -- members
    rw [hperm.mem_iff, List.mem_cons, h.members]
    constructor
    · rintro (rfl | ⟨hy, hcy⟩)
      · exact ⟨hd, hd1⟩
      · have hyd : y ≠ dest := fun e => hcy (e ▸ hd0)
        exact ⟨hy, fun e => hcy ((hn y hy hyd).1 e)⟩
    · rintro ⟨hy, hcy⟩
      by_cases hyd : y = dest
      · exact Or.inl hyd
      · exact Or.inr ⟨hy, fun e => hcy ((hn y hy hyd).2 e)⟩

/-- The slot whose cap a new member's cap is alike: `src` for `dest`, itself otherwise. -/
def oldA (src dest y : U64) : U64 := if y = dest then src else y

/-- The old index of a new index (`dest`'s position maps to `src`'s). -/
def oidx (is n : Nat) : Nat := if n ≤ is then n else if n = is + 1 then is else n - 1

theorem mem_insA_of {src dest y : U64} {c : List U64} (hm : oldA src dest y ∈ c) : y ∈ insA src dest c := by
  by_cases e : y = dest
  · subst e
    unfold oldA at hm; rw [if_pos rfl] at hm
    exact (List.Perm.mem_iff (insA_perm hm)).2 (List.mem_cons.2 (Or.inl rfl))
  · unfold oldA at hm; rw [if_neg e] at hm
    by_cases hsc : src ∈ c
    · exact (List.Perm.mem_iff (insA_perm hsc)).2 (List.mem_cons.2 (Or.inr hm))
    · rw [insA_of_not_mem hsc]; exact hm

/-- **`RngOneA64` along the insertion** of a cap alike the source's (the source's own cap may be rewritten alike). -/
theorem RngOneA64.ins {s s' : S} (h : RngOneA64 st G s) (hnd : G.flatten.Nodup) {src dest : U64}
    (hsrc : src ∈ G.flatten) (dG : dest ∉ G.flatten)
    (hk : ∀ y ∈ G.flatten, y ≠ src → capA st s' y = capA st s y)
    (hs : AlikeA (capA st s' src) (capA st s src)) (hdA : AlikeA (capA st s' dest) (capA st s src)) :
    RngOneA64 st (insG src dest G) s' := by
  have hperm := insG_perm (dest := dest) hnd hsrc
  have hold : ∀ y ∈ (insG src dest G).flatten,
      oldA src dest y ∈ G.flatten ∧ AlikeA (capA st s' y) (capA st s (oldA src dest y)) := by
    intro y hy
    rcases List.mem_cons.1 (hperm.mem_iff.1 hy) with e | hy
    · subst e; unfold oldA; rw [if_pos rfl]; exact ⟨hsrc, hdA⟩
    · have hyd : y ≠ dest := fun e => dG (e ▸ hy)
      unfold oldA; rw [if_neg hyd]
      refine ⟨hy, ?_⟩
      by_cases hys : y = src
      · subst hys; exact hs
      · rw [hk y hy hys]; exact AlikeA.refl _
  have nd : ∀ {c : List U64}, c ∈ G → ∀ {n : Nat} {w : U64}, c[n]? = some w → oldA src dest w = w :=
    by
      intro c hcG n w e
      have : w ≠ dest := fun hw => dG (hw ▸ List.mem_flatten.2 ⟨c, hcG, List.mem_of_getElem? e⟩)
      unfold oldA; rw [if_neg this]
  obtain ⟨cs, hcs0, hscs⟩ := List.mem_flatten.1 hsrc
  obtain ⟨is, his, hsi⟩ := List.getElem_of_mem hscs
  have esi : cs[is]? = some src := by rw [getElem?_of_lt his, hsi]
  have hcsn := ch_nodup hnd hcs0
  refine ⟨fun y hy y' hy' k k' hc => ?_, fun ch hch i j k y z y' hi hj hk2 hij hjk ky ky' hc => ?_⟩
  · obtain ⟨o1, a1⟩ := hold y hy
    obtain ⟨o2, a2⟩ := hold y' hy'
    have k1 := a1.1.1 k
    have k2 := a2.1.1 k'
    obtain ⟨c, hc0, m1, m2⟩ := h.one _ o1 _ o2 k1 k2 (by rw [← (a1.2 k1).1, ← (a2.2 k2).1]; exact hc)
    exact ⟨_, List.mem_map.2 ⟨c, hc0, rfl⟩, mem_insA_of m1, mem_insA_of m2⟩
  · have mem : ∀ {n : Nat} {w : U64}, ch[n]? = some w → w ∈ (insG src dest G).flatten := fun e =>
      List.mem_flatten.2 ⟨ch, hch, List.mem_of_getElem? e⟩
    obtain ⟨o1, a1⟩ := hold y (mem hi)
    obtain ⟨o2, a2⟩ := hold y' (mem hk2)
    obtain ⟨o3, a3⟩ := hold z (mem hj)
    have k1 := a1.1.1 ky
    have k2 := a2.1.1 ky'
    have hc0 : clsA (capA st s (oldA src dest y)) = clsA (capA st s (oldA src dest y')) := by
      rw [← (a1.2 k1).1, ← (a2.2 k2).1]; exact hc
    obtain ⟨c, hcG, rfl⟩ := insG_mem hch
    have goal : RngKeyA (capA st s (oldA src dest z)) ∧
        clsA (capA st s (oldA src dest z)) = clsA (capA st s (oldA src dest y)) := by
      by_cases hsc : src ∈ c
      · obtain rfl : c = cs := ch_eq hnd hcG hcs0 hsc hscs
        have oi : ∀ n w, (insA src dest c)[n]? = some w → c[oidx is n]? = some (oldA src dest w) := by
          intro n w e
          rw [insA_idx hcsn esi] at e
          unfold oidx
          by_cases h1 : n ≤ is
          · rw [if_pos h1] at e ⊢; rw [nd hcG e]; exact e
          · rw [if_neg h1] at e ⊢
            by_cases h2 : n = is + 1
            · rw [if_pos h2] at e ⊢; obtain rfl := Option.some.inj e; unfold oldA; rw [if_pos rfl]; exact esi
            · rw [if_neg h2] at e ⊢; rw [nd hcG e]; exact e
        have e1 := oi i y hi
        have e2 := oi j z hj
        have e3 := oi k y' hk2
        by_cases q1 : oidx is i < oidx is j
        · by_cases q2 : oidx is j < oidx is k
          · exact h.chunk c hcG _ _ _ _ _ _ e1 e2 e3 q1 q2 k1 k2 hc0
          · have q : oidx is j = oidx is k := by
              unfold oidx at q1 q2 ⊢; split_ifs at q1 q2 ⊢ <;> omega
            rw [q, e3] at e2
            rw [← Option.some.inj e2]; exact ⟨k2, hc0.symm⟩
        · have q : oidx is i = oidx is j := by
            unfold oidx at q1 ⊢; split_ifs at q1 ⊢ <;> omega
          rw [← q, e1] at e2
          rw [← Option.some.inj e2]; exact ⟨k1, rfl⟩
      · rw [insA_of_not_mem hsc] at hi hj hk2
        rw [nd hcG hi] at k1 hc0 ⊢; rw [nd hcG hk2] at k2 hc0; rw [nd hcG hj]
        exact h.chunk c hcG i j k y z y' hi hj hk2 hij hjk k1 k2 hc0
    obtain ⟨g1, g2⟩ := goal
    refine ⟨a3.1.2 g1, ?_⟩
    rw [(a3.2 g1).1, (a1.2 k1).1]; exact g2

/-- **`KindA` along the insertion** of a cap alike the source's. -/
theorem KindA.ins {s s' : S} (h : KindA st OS s) {src dest : U64} (hsrc : src ∈ OS)
    (hk : ∀ y ∈ OS, y ≠ src → y ≠ dest → capA st s' y = capA st s y)
    (hs : AlikeA (capA st s' src) (capA st s src)) (hdA : AlikeA (capA st s' dest) (capA st s src)) :
    KindA st OS s' := by
  have hold : ∀ y ∈ OS, oldA src dest y ∈ OS ∧ AlikeA (capA st s' y) (capA st s (oldA src dest y)) := by
    intro y hy
    by_cases hyd : y = dest
    · subst hyd; unfold oldA; rw [if_pos rfl]; exact ⟨hsrc, hdA⟩
    · unfold oldA; rw [if_neg hyd]
      refine ⟨hy, ?_⟩
      by_cases hys : y = src
      · subst hys; exact hs
      · rw [hk y hy hys hyd]; exact AlikeA.refl _
  refine ⟨fun y hy y' hy' k k' hp => ?_⟩
  obtain ⟨o1, a1⟩ := hold y hy
  obtain ⟨o2, a2⟩ := hold y' hy'
  have k1 := a1.1.1 k
  have k2 := a2.1.1 k'
  rw [(a1.2 k1).2, (a2.2 k2).2]
  exact h.kind _ o1 _ o2 k1 k2 (by rw [← ptrA_of_cls (a1.2 k1).1, ← ptrA_of_cls (a2.2 k2).1]; exact hp)

end ins

end ST
end R
end W7

end

end Fl4ProofsA64.P1
