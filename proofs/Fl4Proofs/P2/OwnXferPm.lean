/-
# P2 (line p3mc, gen 53): **the owner transfer applies to an existing certificate** — gen 51's PageMap `InsAP`

A check that P2/OwnXfer's `insAP_xfer` takes an existing certificate as it is: gen 51's **`pm_insAP`**
(P2/InsV15Pm, unchanged, used read-only) concludes `InsAP (PWE K E) ADEq NotPresent (ownP K) …` of the PageMap
program at a view start. **`pm_insAP_xfer`**: with the same hypotheses, for any word set `W` and owner map `own₂`
with `OwnXfer W (ownP K) own₂`, and a run of the program avoiding `W` (`Avoid W (FReachA … (ownP K) …)`), the
program is `InsAP … own₂ …` at the same memory.

Named premises: none (the transfer's conditions are hypotheses). New module; no existing file touched.
-/
import Fl4Proofs.P2.OwnXfer
import Fl4Proofs.P2.InsV15Pm
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY InW)
open Fl4Proofs.P2.E2E (StartAt SP LocalPath tr masksOf InsTP insTP_of_within)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll VEq Safe InsAP narrowSP PO HeldV FReachA OwnXfer
  Avoid insAP_xfer eqOff_refl)
open Fl4Proofs.P2.CoreView (view VN vn_of_nf nf_none)
open Fl4Proofs.P2.MmuAD (MmuAD ADEq NotPresent adEq_equiv)

noncomputable section
open Classical

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)

/-- **Gen 51's PageMap certificate moved to an owner map `own₂` differing from `ownP K` only on a word set the run
avoids** (module docstring). -/
theorem pm_insAP_xfer (hA : P0.ArchTotal ar) {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K)
    {c : U64} {hs : U64 → Prop} {ρ μ : U64 → U64} {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}
    (B : PmObl7 st Cs Ω Sg Ac Locks) (E : U64 → U64) (hcv : K.ptes = ptesR K E)
    (hTv : ∀ hi : U64, hi.val < 2048 → view K.toKLayout c ρ (atAF K.ksb hi) = E (atAF K.ksb hi))
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    {j : I64 × localinv.Plan} {σ : S} {a : A}
    (hPre : PmPreG st Cs Ω Sg Ac Locks j.2 K (view K.toKLayout c ρ) σ) (hqu : QU st K σ)
    (hc : L.cpu σ = c) (hl : Locks σ = hs)
    (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x)
    {W : Set U64} {own₂ : (U64 → U64) → U64 → Owner U64 U64} (X : OwnXfer W (ownP K) own₂)
    (hAv : Avoid W (FReachA (PWE K E) ADEq NotPresent (ownP K) (OwnMap.cls K.toKLayout)
        (OwnMap.ko K.toKLayout μ) c hs) μ
      (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅
        (tr (PmRSU st K Locks σ) (· ∈ K.user)
          (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ) (masksOf st σ) ar
          (R.invBodyPmG j.1 j.2) ∅ a))) :
    InsAP (PWE K E) ADEq NotPresent own₂ (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ∅ μ
      (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅
        (tr (PmRSU st K Locks σ) (· ∈ K.user)
          (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ) (masksOf st σ) ar
          (R.invBodyPmG j.1 j.2) ∅ a)) :=
  insAP_xfer X (pm_insAP ar hA hK hU B E hcv hTv hV hPre hqu hc hl hmm) μ hAv (eqOff_refl W μ)

end main

end
end Fl4Proofs.P2.E2EP
