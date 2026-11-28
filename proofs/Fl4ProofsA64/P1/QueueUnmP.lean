/-
P1 (aarch64, gen 52): **ARMPageTableUnmap's placement hypotheses `hD1` / `hD2` from the state-free placements** —
gen 46's `vspace.decode_page_table.unmapR` takes, for the unmapped table `ptr`, that its words meet no word of another
Stage-2 object of `Te` (`hD2`) and no word of another Stage-1 table of `Tb` (`hD1`), and `ptr ∈ Pt` (`hptr`).

* **`ptD_of_pl`**: both follow from gen 42 / 44's state-free placement case hypotheses `S1Pl kb Pp Tb` (Stage-1
  tables pairwise apart, `un`) and `S2Pl kb Pp Tb Te bits` (Stage-2 objects pairwise apart, `un`; apart from the
  Stage-1 tables, `tb`) once `ptr` is itself one of the placed tables, `ptr ∈ Tb ∨ ptr ∈ Te` (`S2OK.sz`: a Stage-2
  object has at least 4 KiB). **`ptr_pt_of`**: `ptr ∈ Pt` from the same membership (`Tb ⊆ Pt`, `Gran Te bits ⊆ Pt`).
* **`vspace.decode_page_table.unmapRP`**: `unmapR` with `hptr` / `hD1` / `hD2` replaced by `S1Pl`, `S2Pl` and the
  membership `hpT : ptr ∈ Tb ∨ ptr ∈ Te`. Source of `hpT` for a *mapped* `PageTable` cap (the cap `unmapR` takes):
  a table cap becomes mapped only by ARMPageTableMap, whose tops insert the table into `Tb` (Stage-1,
  `S1Pl kb Pp (insert ptr Tb)`, QueueS1Map) or `Te` (Stage-2, `S2OK (insert ptr Te)`, QueueS2Map), and the placement
  sets are never shrunk (Architect ruling, gen 45) — a carried cap fact over the `OS` slots, to be threaded with the
  map tops (still owed).

No named premise; `S1Pl` / `S2Pl` are the existing state-free case hypotheses, `hpT` a case hypothesis.
-/
import Fl4ProofsA64.P1.QueueUnmD
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

section pl
variable {kb : U64} {Pp Tb Te Hr : Set U64} {bits : U64 → Nat}

/-- **`hD2` / `hD1` from the placements** (module docstring). -/
theorem ptD_of_pl (hS : S2OK Te bits Hr) (h1 : S1Pl kb Pp Tb) (h2 : S2Pl kb Pp Tb Te bits) {ptr : U64}
    (hp : ptr ∈ Tb ∨ ptr ∈ Te) :
    (∀ q ∈ Te, q ≠ ptr → ∀ o o' : U64, o.val < 4096 → o.val % 8 = 0 → o'.val < 2 ^ bits q →
      o'.val % 8 = 0 → wa q o' ≠ wa ptr o) ∧
    (∀ q ∈ Tb, q ≠ ptr → ∀ o o' : U64, o.val < 4096 → o.val % 8 = 0 → o'.val < 4096 → o'.val % 8 = 0 →
      wa q o' ≠ wa ptr o) := by
  rcases hp with hp | hp
  · constructor
    · intro q hq _ o o' ho h8 ho' h8' e
      exact h2.tb (wa q o') ⟨q, hq, o', ho', h8', rfl⟩ ⟨ptr, hp, o, ho, h8, e⟩
    · intro q hq hne o o' ho h8 ho' h8' e
      exact hne (h1.un ptr hp q hq o o' ho h8 ho' h8' e)
  · have hb : 4096 ≤ 2 ^ bits ptr := (pow_bits (hS.sz ptr hp)).1
    constructor
    · intro q hq hne o o' ho h8 ho' h8' e
      exact hne (h2.un ptr hp q hq o o' (by omega) h8 ho' h8' e)
    · intro q hq _ o o' ho h8 ho' h8' e
      exact h2.tb (wa ptr o) ⟨ptr, hp, o, by omega, h8, rfl⟩ ⟨q, hq, o', ho', h8', e.symm⟩

/-- **`ptr ∈ Pt`** from the membership. -/
theorem ptr_pt_of {Pt : Set U64} (hTb : Tb ⊆ Pt) (hTe : Gran Te bits ⊆ Pt) {ptr : U64} (hp : ptr ∈ Tb ∨ ptr ∈ Te) :
    ptr ∈ Pt := by
  rcases hp with hp | hp
  · exact hTb hp
  · exact hTe ⟨ptr, hp, Or.inl rfl⟩

end pl

section dec
variable {OS Vc Ub : Set U64} {kb n : U64} {Pp Tb Pt Hr Te : Set U64} {Lv Re bits : U64 → Nat}
variable {A : Type _} {ar : machine.Arch A}

/-- **Decode-level ARMPageTableUnmap of a mapped cap, placement from `S1Pl` / `S2Pl`** (module docstring). -/
theorem vspace.decode_page_table.unmapRP (hA : P0.ArchTotal ar) (hPl : ArchPlat ar)
    (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) (hO : OSOK T Ω Sg OS)
    {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q Rq) (hk : L.ksb s = kb) (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt)
    (hTe : Gran Te bits ⊆ Pt) (hH : HrOK kb Pp Tb Lv Hr) (hS : S2OK Te bits Hr)
    (hP1 : S1Pl kb Pp Tb) (hP2 : S2Pl kb Pp Tb Te bits)
    (hY : VsTyR st kb Pp Hr Tb Lv s) (h2 : S2TyR st hPl.ipa Pp Hr Te Re bits s)
    (hU : UnmZ st OS Pt (S2Rt st Pp Te Re bits s) bits s) (hT : UnmT st OS (VsRt st Pp Hr Tb Lv s) s)
    (hV : UnmU st OS Pp s)
    (a : A) (len slot buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) {ptr masid mvaddr : U64}
    (hsl : slot ∈ OS) (hc : obj.Slot.cap st slot s = ok (.PageTable ptr true masid mvaddr))
    (hF : PtFnd st hPl.ipa Pp Hr Lv Re bits s masid mvaddr ptr)
    (hone : ∀ y ∈ OS, y ≠ slot → ¬ NmC st y ptr s)
    (hpT : ptr ∈ Tb ∨ ptr ∈ Te) (hal : Aligned ptr) (hfit : ptr.val + 4096 ≤ 2 ^ 64) :
    vspace.decode_page_table st ar s a fl4_abi.label.ARMPageTableUnmap len slot
      (.PageTable ptr true masid mvaddr) buf extra ⦃ r => r.2.1 = s ∨
        (L.ksb r.2.1 = kb ∧ VsTyR st kb Pp Hr Tb Lv r.2.1 ∧ S2TyR st hPl.ipa Pp Hr Te Re bits r.2.1 ∧
          UnmZ st OS Pt (S2Rt st Pp Te Re bits r.2.1) bits r.2.1 ∧ UnmT st OS (VsRt st Pp Hr Tb Lv r.2.1) r.2.1 ∧
          UnmU st OS Pp r.2.1) ⦄ :=
  vspace.decode_page_table.unmapR hA hPl hR hO q hk hPp hTb hTe hH hS hY h2 hU hT hV a len slot buf extra hsl hc hF
    hone (ptr_pt_of hTb hTe hpT) hal hfit (ptD_of_pl hS hP1 hP2 hpT).1 (ptD_of_pl hS hP1 hP2 hpT).2

end dec

end ST
end R
end W7

end

end Fl4ProofsA64.P1
