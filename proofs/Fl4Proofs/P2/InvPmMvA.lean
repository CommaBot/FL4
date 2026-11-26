/-
# P2 (line pte, generation 15): `mv` pieces — the encoded Frame cap's first word

* **`nof_enc_framePm`**: the first word `Cap::encode` gives for any Frame cap is a Frame word (`NullOrFrame`): its
  tag bits are 13 whatever the fields (the ASID's high nibble sits at bits 54–57, the size code at 48–49, the
  rights at 50–51). slhuf's `nof_enc_frame8` (int19 InvCMAcc8) proves the unmapped ASID-0 case the same way
  (`P3.encode_eq`, `P3.tag_gen … (by bvext)`, `P3.codeF_hb`). This is what the `gd … PWs` store needs to let the
  PageMap decode's `set_cap` write the slot's `CAP0` (`OwnMap.gds_write_cap0`).

No named premise. New module; no existing statement changes.
-/
import Fl4Proofs.P2.InvPmBlkF
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl
open Fl4Proofs.P2.OwnMap (NullOrFrame)

open Fl4Proofs.P3 in
/-- **A Frame cap's first encoded word is a Frame word** (module docstring). -/
theorem nof_enc_framePm {p r asid va : U64} {sz : capability.FrameSize} {d m ep : Bool} {w0 w1 : U64}
    (h : capability.Cap.encode (.Frame p sz r d m ep asid va) = ok (w0, w1)) : NullOrFrame w0 := by
  rw [Fl4Proofs.P3.encode_eq] at h
  have e := ok_inj_ff h
  simp only [Prod.mk.injEq] at e
  obtain ⟨e0, -⟩ := e
  subst e0
  right
  have h4 := Fl4Proofs.P3.codeF_hb sz
  have htag := Fl4Proofs.P3.tag_gen (w := (Fl4Proofs.P3.encodeF (.Frame p sz r d m ep asid va)).1)
    (k := 13) (by bvext) (by decide)
  have e1 : ((Fl4Proofs.P3.encodeF (.Frame p sz r d m ep asid va)).1 >>> 59).toNat =
      (Fl4Proofs.P3.encodeF (.Frame p sz r d m ep asid va)).1.toNat / 2 ^ 59 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have e2 : (⟨(Fl4Proofs.P3.encodeF (.Frame p sz r d m ep asid va)).1⟩ : U64).val =
      (Fl4Proofs.P3.encodeF (.Frame p sz r d m ep asid va)).1.toNat := rfl
  rw [e2, ← e1]
  exact htag

end Fl4Proofs.P2.E2EP
