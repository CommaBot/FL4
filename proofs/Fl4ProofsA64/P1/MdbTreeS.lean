/-
P1 (aarch64, gen 55): **`MdbS ∧ MdbTU` aligned on one ghost** — the gen-46 chain ghost of `MdbS` (`∃ G`, with
`RngOneA64` / `KindA` / `NullLk` / `ClsA`) and the gen-54 tree's (`MdbTU = ∃ G par, TreeA`) are the same chains:

* **`MdbLk.chains_sub`** (and `chains_iff`): two ghosts satisfying `MdbLk` at one state have the same chains — a
  chain is fixed by its head (`PREV` word 0: a non-head member's `PREV` is its predecessor, a non-null `OS` slot)
  and its `NEXT` pointers (a member with `NEXT ≠ 0` is followed by it, `NEXT = 0` ends the chain).
* **`RngOneA64.congr`**, **`MdbOK.congr`**: both read the ghost only through chain and member membership.
* **`MdbST st OS s`**: one ghost `G` and one parent map `par` with `MdbLk`, `RngOneA64`, `KindA`, `NullLk`, `ClsA`,
  `Mdb.MdbOK par G`, `UtInvA` — **`MdbST.of`** (from `MdbS ∧ MdbTU`), `MdbST.mdbS`, `MdbST.tu`, `MdbST.tree`
  (`TreeA` with `RngOneA64` / `KindA` at the tree's own ghost: what `cdt.empty_slot.tree` takes), `MdbST.empty`.
* **`TreeA.grow`** / `UtInvA.grow`: `OS` grown by slots that are null (retype's new CNode / TCB slots: the
  `OS`-growth half of the retype obligation on the tree; `OSOK` / `WinOK` of the grown set are not here).

So every existing `∃ G` top over `MdbS` composes with the tree tops without carrying a second ghost. No named
premise; new definitions and theorems only.
-/
import Fl4ProofsA64.P1.MdbTreeD
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts Fl4Proofs.P3

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {Sg : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

section uniq
variable {OS : Set U64} {G : List (List U64)}

/-- A member whose `PREV` word is 0 is its chain's head. -/
theorem MdbLk.idx_head {s : S} (h : MdbLk st OS G s) (h0 : ∀ y ∈ OS, y ≠ 0#u64) {ch : List U64} (hch : ch ∈ G)
    {i : Nat} {a : U64} (ha : ch[i]? = some a) (hz : L.mem s (wa a 16#u64) = 0#u64) : i = 0 := by
  cases i with
  | zero => rfl
  | succ j =>
    exfalso
    have hj : j < ch.length := by
      have : j + 1 < ch.length := by
        by_contra hc; rw [List.getElem?_eq_none (by omega)] at ha; cases ha
      omega
    have hb : ch[j]? = some ch[j] := List.getElem?_eq_getElem hj
    have e := (h.chain ch hch j ch[j] a hb ha).2
    rw [hz] at e
    have hm : ch[j] ∈ G.flatten := List.mem_flatten.2 ⟨ch, hch, List.getElem_mem hj⟩
    exact h0 _ ((h.members _).1 hm).1 e.symm

/-- A member with `NEXT ≠ 0` is followed by its `NEXT`. -/
theorem MdbLk.idx_next {s : S} (h : MdbLk st OS G s) {ch : List U64} (hch : ch ∈ G) {i : Nat} {a : U64}
    (ha : ch[i]? = some a) (hn : NxA st s a ≠ 0#u64) : ch[i + 1]? = some (NxA st s a) := by
  cases e : ch[i + 1]? with
  | some b => rw [(h.chain ch hch i a b ha e).1]
  | none =>
    exfalso
    have hi : i < ch.length := by
      by_contra hc; rw [List.getElem?_eq_none (by omega)] at ha; cases ha
    have hl : ch.length ≤ i + 1 := List.getElem?_eq_none_iff.1 e
    have hlast : ch.getLast? = some a := by
      rw [List.getLast?_eq_getElem?, show ch.length - 1 = i by omega]; exact ha
    exact hn (h.last ch hch a hlast)

/-- A member with `NEXT = 0` ends its chain. -/
theorem MdbLk.idx_last {s : S} (h : MdbLk st OS G s) (h0 : ∀ y ∈ OS, y ≠ 0#u64) {ch : List U64} (hch : ch ∈ G)
    {i : Nat} {a : U64} (ha : ch[i]? = some a) (hn : NxA st s a = 0#u64) : ch[i + 1]? = none := by
  cases e : ch[i + 1]? with
  | none => rfl
  | some b =>
    exfalso
    have hb := (h.chain ch hch i a b ha e).1
    rw [hn] at hb
    have hm : b ∈ G.flatten := List.mem_flatten.2 ⟨ch, hch, List.mem_of_getElem? e⟩
    exact h0 _ ((h.members _).1 hm).1 hb.symm

/-- **Two ghosts of `MdbLk` at one state have the same chains** (one inclusion). -/
theorem MdbLk.chains_sub {s : S} {G' : List (List U64)} (h : MdbLk st OS G s) (h' : MdbLk st OS G' s)
    (h0 : ∀ y ∈ OS, y ≠ 0#u64) : ∀ ch ∈ G, ch ∈ G' := by
  intro ch hch
  have hne := h.ne_nil ch hch
  obtain ⟨a, ha⟩ : ∃ a, ch[0]? = some a := by
    cases ch with
    | nil => exact absurd rfl hne
    | cons a l => exact ⟨a, rfl⟩
  have hz : L.mem s (wa a 16#u64) = 0#u64 := h.head ch hch a (by rw [List.head?_eq_getElem?]; exact ha)
  have haG : a ∈ G.flatten := List.mem_flatten.2 ⟨ch, hch, List.mem_of_getElem? ha⟩
  have haG' : a ∈ G'.flatten := (h'.members a).2 ((h.members a).1 haG)
  obtain ⟨ch', hch', hac⟩ := List.mem_flatten.1 haG'
  obtain ⟨k, hk', hkk⟩ := List.getElem_of_mem hac
  have hk : ch'[k]? = some a := by rw [List.getElem?_eq_getElem hk', hkk]
  have hk0 := h'.idx_head h0 hch' hk hz
  subst hk0
  have key : ∀ i : Nat, ch[i]? = ch'[i]? := by
    intro i
    induction i with
    | zero => rw [ha, hk]
    | succ i ih =>
      cases e : ch[i]? with
      | none =>
        rw [e] at ih
        have h1 : ch.length ≤ i := List.getElem?_eq_none_iff.1 e
        have h2 : ch'.length ≤ i := List.getElem?_eq_none_iff.1 ih.symm
        rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
      | some x =>
        rw [e] at ih
        by_cases hn : NxA st s x = 0#u64
        · rw [h.idx_last h0 hch e hn, h'.idx_last h0 hch' ih.symm hn]
        · rw [h.idx_next hch e hn, h'.idx_next hch' ih.symm hn]
  rw [List.ext_getElem? key]; exact hch'

theorem MdbLk.chains_iff {s : S} {G' : List (List U64)} (h : MdbLk st OS G s) (h' : MdbLk st OS G' s)
    (h0 : ∀ y ∈ OS, y ≠ 0#u64) : ∀ ch, ch ∈ G ↔ ch ∈ G' :=
  fun ch => ⟨h.chains_sub h' h0 ch, h'.chains_sub h h0 ch⟩

theorem flatten_congr {G G' : List (List U64)} (hG : ∀ ch, ch ∈ G ↔ ch ∈ G') (y : U64) :
    y ∈ G.flatten ↔ y ∈ G'.flatten := by
  simp only [List.mem_flatten]
  exact ⟨fun ⟨c, hc, hy⟩ => ⟨c, (hG c).1 hc, hy⟩, fun ⟨c, hc, hy⟩ => ⟨c, (hG c).2 hc, hy⟩⟩

/-- `RngOneA64` reads the ghost only through its chains. -/
theorem RngOneA64.congr {s : S} {G' : List (List U64)} (h : RngOneA64 st G s) (hG : ∀ ch, ch ∈ G ↔ ch ∈ G') :
    RngOneA64 st G' s := by
  refine ⟨fun y hy y' hy' k k' hc => ?_, fun ch hch => h.chunk ch ((hG ch).2 hch)⟩
  obtain ⟨c, hc0, h1, h2⟩ := h.one y ((flatten_congr hG y).2 hy) y' ((flatten_congr hG y').2 hy') k k' hc
  exact ⟨c, (hG c).1 hc0, h1, h2⟩

/-- `Mdb.MdbOK` reads the ghost only through its chains and members (and the members' `Nodup`). -/
theorem MdbOK.congr {par : U64 → Option U64} {G' : List (List U64)} (h : Mdb.MdbOK par G)
    (hG : ∀ ch, ch ∈ G ↔ ch ∈ G') (hnd : G'.flatten.Nodup) : Mdb.MdbOK par G' :=
  ⟨hnd, fun ch hch => h.seg ch ((hG ch).2 hch), fun a b e =>
    ⟨(flatten_congr hG a).1 (h.par_mem a b e).1, (flatten_congr hG b).1 (h.par_mem a b e).2⟩⟩

end uniq

/-- **The MDB facts and the tree on one ghost** (module docstring). -/
def MdbST (st : machine.Store S) [L : LawfulStore st] (OS : Set U64) (s : S) : Prop :=
  ∃ G : List (List U64), ∃ par : U64 → Option U64, MdbLk st OS G s ∧ RngOneA64 st G s ∧ KindA st OS s ∧
    NullLk st OS s ∧ ClsA st OS s ∧ Mdb.MdbOK par G ∧ UtInvA st OS par s

section st
variable {OS : Set U64}

/-- **`MdbS ∧ MdbTU` align** (`MdbLk.chains_iff`). -/
theorem MdbST.of {s : S} (h0 : ∀ y ∈ OS, y ≠ 0#u64) (hS : MdbS st OS s) (hT : MdbTU st OS s) : MdbST st OS s := by
  obtain ⟨G, hM, hRO, hK, hN, hC⟩ := hS
  obtain ⟨G', par, hT'⟩ := hT
  exact ⟨G, par, hM, hRO, hK, hN, hC, MdbOK.congr hT'.tree (hT'.lk.chains_iff hM h0) hM.nodup, hT'.ut⟩

theorem MdbST.mdbS {s : S} (h : MdbST st OS s) : MdbS st OS s := by
  obtain ⟨G, par, hM, hRO, hK, hN, hC, -, -⟩ := h
  exact ⟨G, hM, hRO, hK, hN, hC⟩

/-- The tree with `RngOneA64` / `KindA` at its own ghost (`cdt.empty_slot.tree`'s hypotheses). -/
theorem MdbST.tree {s : S} (h : MdbST st OS s) : ∃ G : List (List U64), ∃ par : U64 → Option U64,
    TreeA st OS G par s ∧ RngOneA64 st G s ∧ KindA st OS s := by
  obtain ⟨G, par, hM, hRO, hK, -, -, hT, hU⟩ := h
  exact ⟨G, par, ⟨hM, hT, hU⟩, hRO, hK⟩

theorem MdbST.tu {s : S} (h : MdbST st OS s) : MdbTU st OS s := by
  obtain ⟨G, par, hT, -, -⟩ := h.tree
  exact ⟨G, par, hT⟩

theorem MdbST.iff {s : S} (h0 : ∀ y ∈ OS, y ≠ 0#u64) : MdbST st OS s ↔ MdbS st OS s ∧ MdbTU st OS s :=
  ⟨fun h => ⟨h.mdbS, h.tu⟩, fun h => MdbST.of h0 h.1 h.2⟩

/-- **Boot**: null `OS` slots with zero link words. -/
theorem MdbST.empty {s : S} (h0 : ∀ y ∈ OS, y ≠ 0#u64) (h : ∀ x ∈ OS, capA st s x = .Null)
    (hz : ∀ x ∈ OS, L.mem s (wa x 16#u64) = 0#u64 ∧ L.mem s (wa x 24#u64) = 0#u64) : MdbST st OS s :=
  MdbST.of h0 (MdbS.empty h hz) (MdbTU.empty h)

end st

/-! ## `OS` grown by null slots (retype's new CNode / TCB slots) -/

section grow
variable {OS OS' : Set U64} {G : List (List U64)} {par : U64 → Option U64}

/-- Null slots carry no physical cap. -/
theorem nullOut {s : S} (hsub : OS ⊆ OS') (hn : ∀ x ∈ OS', x ∉ OS → capA st s x = .Null) {y : U64} (hy : y ∈ OS')
    (hp : physA (capA st s y) = true) : y ∈ OS := by
  by_contra h; rw [hn y hy h, physA_null] at hp; cases hp

/-- **`UtInvA` over `OS` grown by null slots.** -/
theorem UtInvA.grow {s : S} (h : UtInvA st OS par s) (hsub : OS ⊆ OS')
    (hn : ∀ x ∈ OS', x ∉ OS → capA st s x = .Null) : UtInvA st OS' par s := by
  have ut : ∀ x ∈ OS', ∀ p b i d, capA st s x = .Untyped p b i d → x ∈ OS := fun x hx p b i d hc =>
    nullOut hsub hn hx (by rw [hc]; exact physA_ut _ _ _ _)
  refine ⟨fun x hx hp => h.reg x (nullOut hsub hn hx hp) hp,
    fun x hx p b i d hc => h.inc x (ut x hx p b i d hc) p b i d hc,
    fun x hx p b i d hc y hy hp => h.noov x (ut x hx p b i d hc) p b i d hc y (nullOut hsub hn hy hp) hp,
    fun x hx y hy hxy p b i i' d d' h1 h2 => h.excl x (ut x hx p b i d h1) y (ut y hy p b i' d' h2) hxy p b i i' d d' h1 h2,
    fun x hx p b i d hc => h.fib x (ut x hx p b i d hc) p b i d hc,
    fun x hx p b i d hc y hy hyx hp hD =>
      h.drange x (ut x hx p b i d hc) p b i d hc y (nullOut hsub hn hy hp) hyx hp hD, h.anc⟩

/-- **`TreeA` over `OS` grown by null slots** (the ghost and tree kept). -/
theorem TreeA.grow {s : S} (h : TreeA st OS G par s) (hsub : OS ⊆ OS')
    (hn : ∀ x ∈ OS', x ∉ OS → capA st s x = .Null) : TreeA st OS' G par s := by
  refine ⟨⟨h.lk.nodup, h.lk.ne_nil, h.lk.chain, h.lk.head, h.lk.last, fun x => ?_⟩, h.tree,
    h.ut.grow hsub hn⟩
  rw [h.lk.members x]
  constructor
  · rintro ⟨hx, hc⟩; exact ⟨hsub hx, hc⟩
  · rintro ⟨hx, hc⟩
    by_cases hxo : x ∈ OS
    · exact ⟨hxo, hc⟩
    · exact absurd (hn x hx hxo) hc

end grow

end ST
end R
end W7

end

end Fl4ProofsA64.P1
