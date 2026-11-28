/-
P1 (aarch64, gen 60): **retype (no reset) keeps `CoverA`** (l4v `if_unsafe_then_cap` along `retype_region` /
`create_cap`: every new cap goes into a slot the destination CNode cap covers), and the bundle top carrying `StA`.

* **`LoopV.cov`** (data level): from `CoverA` at the start and `LoopV` after `len` objects — every covering cap is
  held after (the source is an untyped, not a cover; the new slots were null, so no cover), every slot non-null after
  is the source (non-null before), a new slot (covered before: `hcd`), or an old slot holding its old cap.
* **`untyped.retype.cov`**: no `hCO`; the run is MdbUZR's `untyped.retype.lvR` (RAM source) / `lvD` (device
  source), both instances of the one function-level proof `untyped.retype.genJK` (MdbTreeL) through `genFG` and
  `loopVG`.
* **`untyped.retype.stA`**: `StA H` (`MdbST ∧ UtRev ∧ ValidUntypedA ∧ UtZeroA ∧ CoverA`) before ⇒ `Ok` and `StA H'`
  after (MdbUZR's `untyped.retype.mdbSTVUZ` with `cov`).

No named premise. New case hypothesis **`hcd`**: each destination slot `djA dcn off j` is covered at the start by an
`OS` cap (the destination CNode's cap: decode, untyped.rs:44–55 looks the CNode up through a cap of the caller's
CSpace; that cap's range holds the slots `[off, off + len)`, untyped.rs:57–60). The other case hypotheses are
`mdbSTVUZ`'s.
-/
import Fl4ProofsA64.P1.MdbUZR
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts Fl4Proofs.P3

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {Sg : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

variable {OS : Set U64} {H : Heap}

/-- **`CoverA` after the loop** (module docstring). -/
theorem LoopV.cov {s sf : S} (hC : CoverA st OS s) {src p sb fi : U64} {dev : Bool} {F w : Nat}
    {dslot : Nat → U64} {cj : Nat → capability.Cap} (hcs : capA st s src = .Untyped p sb fi dev)
    (hdn : ∀ j, j < w → capA st s (dslot j) = .Null)
    (hcd : ∀ j, j < w → ∃ z ∈ OS, CovBy (capA st s z) (dslot j))
    (h : LoopV st OS s src p sb dev F dslot cj sf w) : CoverA st OS sf := by
  obtain ⟨⟨G, -, -, -, hold, -, -⟩, -⟩ := h
  refine hC.step (fun z hz hp hu => ?_) fun y hy hn => ?_
  · by_cases zs : z = src
    · rw [zs, hcs] at hu; simp [isUtA] at hu
    · by_cases hzd : ∃ j, j < w ∧ z = dslot j
      · obtain ⟨j, hj, rfl⟩ := hzd
        rw [hdn j hj, physA_null] at hp; cases hp
      · exact ⟨z, hz, hold z hz zs fun j hj e => hzd ⟨j, hj, e⟩⟩
  · by_cases hyd : ∃ j, j < w ∧ y = dslot j
    · obtain ⟨j, hj, rfl⟩ := hyd
      exact Or.inr (hcd j hj)
    · by_cases ys : y = src
      · exact Or.inl (by rw [ys, hcs]; exact fun e => by cases e)
      · exact Or.inl (by rw [← hold y hy ys fun j hj e => hyd ⟨j, hj, e⟩]; exact hn)

section arch3
variable {A : Type _} {ar : machine.Arch A}

/-- **Retype (no reset) keeps `CoverA`, no `hCO`** (module docstring). -/
theorem untyped.retype.cov {Sg : Set U64} (hA : P0.ArchTotal ar) (hH : HeapOK H)
    (hO : OSOK H.tcbs H.omega Sg OS) {G : List (List U64)} {par : U64 → Option U64} {s : S}
    (hT : TreeA st OS G par s) (hN : NullLk st OS s) (hV : ValidUntypedA st H OS s) (hUZ : UtZeroA st OS s)
    (hC : CoverA st OS s) (a : A) {src p sb fi : U64} {dev : Bool} (hsrc : src ∈ OS)
    (hcs : capA st s src = .Untyped p sb fi dev)
    (nt us dcn off len base : U64) (device : Bool) (hdv : device = dev) (hn : nt.val < 15)
    (hz : (zA nt.val us).val < 64) (hdev : dev = true → nt.val ≠ 1 ∧ nt.val ≠ 12 ∧ nt.val ≠ 14)
    (hal : base.val % 8 = 0)
    (hfi : fi.val < 2 ^ sb.val) (hA0 : p.val + fi.val ≤ base.val)
    (hAw : base.val + len.val * 2 ^ (zA nt.val us).val ≤ p.val + 2 ^ sb.val)
    (hnA : Aligned (nwA st s)) (hnC : ¬ W7.CapW H.tcbs H.omega Sg (nwA st s))
    (hnF : ∀ u ∈ OS, ∀ p b i, capA st s u = .Untyped p b i false →
      (nwA st s).val < p.val + i.val ∨ p.val + 2 ^ b.val ≤ (nwA st s).val)
    (hhd0 : L.mem s (nwA st s) = 0#u64 ∨ H (L.mem s (nwA st s)) = some .tcb)
    (hdO : ∀ j, j < len.val → djA dcn off j ∈ OS)
    (hdn : ∀ j, j < len.val → capA st s (djA dcn off j) = .Null)
    (hdc : ∀ j, j < len.val → obj.sext48 (djA dcn off j) = ok (djA dcn off j))
    (hinj : ∀ j l, j < len.val → l < len.val → djA dcn off j = djA dcn off l → j = l)
    (hcan : ∀ j, j < len.val → CapRt.Canonical (bjA base (zA nt.val us) j)) (hus : us.val < 64)
    (hcd : ∀ j, j < len.val → ∃ z ∈ OS, CovBy (capA st s z) (djA dcn off j)) :
    untyped.retype st ar s a src false base nt us dcn off len device ⦃ r => r.1 = .Ok () ∧
      CoverA st OS r.2.1 ⦄ := by
  cases dev
  · refine WP.spec_mono (untyped.retype.lvR hA hH hO hT hN hV hUZ a hsrc hcs nt us dcn off len base device hdv hn
      hz hal hfi hA0 hAw hnA hnC hnF hhd0 hdO hdn hdc hinj hcan hus) ?_
    rintro r ⟨hok, hLV, -⟩
    exact ⟨hok, LoopV.cov hC hcs hdn hcd hLV⟩
  · refine WP.spec_mono (untyped.retype.lvD hH hO hT hN hV hUZ a hsrc hcs nt us dcn off len base device hdv hn hz
      (hdev rfl) hfi hA0 hAw hnF hdO hdn hdc hinj hcan hus) ?_
    rintro r ⟨hok, hLV, -⟩
    exact ⟨hok, LoopV.cov hC hcs hdn hcd hLV⟩

/-- **Retype (no reset) carries the bundle `StA`** (module docstring). -/
theorem untyped.retype.stA {Sg : Set U64} (hA : P0.ArchTotal ar) (hH : HeapOK H)
    (hO : OSOK H.tcbs H.omega Sg OS) {s : S} {H' : Heap} (hSt : StA st H OS s) (a : A)
    {src p sb fi : U64} {dev : Bool} (hsrc : src ∈ OS) (hcs : capA st s src = .Untyped p sb fi dev)
    (nt us dcn off len base : U64) (device : Bool) (hdv : device = dev) (hn : nt.val < 15)
    (hz : (zA nt.val us).val < 64) (hdev : dev = true → nt.val ≠ 1 ∧ nt.val ≠ 12 ∧ nt.val ≠ 14)
    (hal : base.val % 8 = 0)
    (hfi : fi.val < 2 ^ sb.val) (hA0 : p.val + fi.val ≤ base.val)
    (hAw : base.val + len.val * 2 ^ (zA nt.val us).val ≤ p.val + 2 ^ sb.val)
    (hH' : ∀ q k, H' q = some k → H q = some k ∨
      (nt.val ≠ 0 ∧ base.val ≤ q.val ∧ q.val + 2 ^ k.bits ≤ base.val + len.val * 2 ^ (zA nt.val us).val))
    (hnA : Aligned (nwA st s)) (hnC : ¬ W7.CapW H.tcbs H.omega Sg (nwA st s))
    (hnF : ∀ u ∈ OS, ∀ p b i, capA st s u = .Untyped p b i false →
      (nwA st s).val < p.val + i.val ∨ p.val + 2 ^ b.val ≤ (nwA st s).val)
    (hhd0 : L.mem s (nwA st s) = 0#u64 ∨ H (L.mem s (nwA st s)) = some .tcb)
    (hdO : ∀ j, j < len.val → djA dcn off j ∈ OS)
    (hdn : ∀ j, j < len.val → capA st s (djA dcn off j) = .Null)
    (hdc : ∀ j, j < len.val → obj.sext48 (djA dcn off j) = ok (djA dcn off j))
    (hinj : ∀ j l, j < len.val → l < len.val → djA dcn off j = djA dcn off l → j = l)
    (hcan : ∀ j, j < len.val → CapRt.Canonical (bjA base (zA nt.val us) j)) (hus : us.val < 64)
    (hcd : ∀ j, j < len.val → ∃ z ∈ OS, CovBy (capA st s z) (djA dcn off j)) :
    untyped.retype st ar s a src false base nt us dcn off len device ⦃ r => r.1 = .Ok () ∧
      StA st H' OS r.2.1 ⦄ := by
  obtain ⟨hS, hR, hV, hUZ, hC⟩ := hSt
  obtain ⟨G, par, hM, -, -, hN, -, hTr, hU⟩ := id hS
  have hT : TreeA st OS G par s := ⟨hM, hTr, hU⟩
  refine WP.spec_mono (spec_andA
    (untyped.retype.mdbSTVUZ hA hH hO hS hR hV hUZ a hsrc hcs nt us dcn off len base device hdv hn hz hdev hal hfi
      hA0 hAw hH' hnA hnC hnF hhd0 hdO hdn hdc hinj hcan hus)
    (untyped.retype.cov hA hH hO hT hN hV hUZ hC a hsrc hcs nt us dcn off len base device hdv hn hz hdev hal hfi
      hA0 hAw hnA hnC hnF hhd0 hdO hdn hdc hinj hcan hus hcd)) ?_
  rintro r ⟨⟨hok, h1, h2, h3, h4⟩, -, h5⟩
  exact ⟨hok, h1, h2, h3, h4, h5⟩

end arch3

end ST
end R
end W7

end

end Fl4ProofsA64.P1
