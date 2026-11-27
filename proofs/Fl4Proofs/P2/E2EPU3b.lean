/-
# P2 (line mmuAD, gen 2): FL4's A/D writes are `Serial.ADWr` steps

The bridge from `MmuAD` [P] to `P2/SerialAD.lean` under rule 8 (`ownP`): an A/D write to any paging word that
decides no owner — every leaf PTE (`pte_nondec`), and every upper-level entry in `own`'s `.none` region (the
PML4 / PDPT / PD tables are not typed kernel objects of `region`) — moves no owner and has an untracked class, so
it is an `ADWr (PW K) ADEq NotPresent` whatever its lock state (`MmuAD.adWrP`, `MmuAD.adWr_pte`,
`MmuAD.adWr_none`). With `SerialAD.serializable_safeA` this covers, at the `Serial` level, A bits on gate words
read lock-free by local walks and A/D on a leaf a local Delete holds, provided the started bodies are `ADIns`
(`MmuADProg.body_adIns` reduces that to `SADIns` of each path's explicit tree; not yet proved per slot — see the
handoff).

No premise beyond `MmuAD` [P]; no existing statement or file changed.
-/
import Fl4Proofs.P2.E2EPU3
import Fl4Proofs.P2.MmuADProg
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.MmuAD
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.Serial (ADWr Cfg)
open Fl4Proofs.P2.OwnMap (DecW region)

/-- **An A/D write to a word that decides no owner is an `ADWr`** (rule 8 ghost maps). -/
theorem MmuAD.adWrP {K : KLayoutP} (hK : RegionOKP K) {PW : U64 → Prop} {s : Cfg U64 U64 U64 U64} {a x : U64}
    (hM : E2EP.MapsP K s) (hd : ¬ DecW K.toKLayout a) (h : MmuAD PW s.mem a x) :
    ADWr PW ADEq NotPresent s a x :=
  h.adWr (fun m => by rw [hM.own]; exact ownP_upd_nondec hK hd m x)
    (by rw [hM.ko]; exact OwnMap.ko_free_of_nondec hK.base.base hd s.mem)

/-- A leaf PTE, any lock state. -/
theorem MmuAD.adWr_pte {K : KLayoutP} (hK : RegionOKP K) {PW : U64 → Prop} {s : Cfg U64 U64 U64 U64}
    {a x : U64} (hM : E2EP.MapsP K s) (ha : a ∈ K.ptes) (h : MmuAD PW s.mem a x) :
    ADWr PW ADEq NotPresent s a x :=
  h.adWrP hK hM (pte_nondec hK ha)

/-- A word of `own`'s `.none` region (the upper paging levels). -/
theorem MmuAD.adWr_none {K : KLayoutP} (hK : RegionOKP K) {PW : U64 → Prop} {s : Cfg U64 U64 U64 U64}
    {a x : U64} (hM : E2EP.MapsP K s) (ha : region K.toKLayout a = .none) (h : MmuAD PW s.mem a x) :
    ADWr PW ADEq NotPresent s a x :=
  h.adWrP hK hM (OwnMap.nondec_of_region hK.base.base (Or.inr (Or.inr (Or.inr (Or.inl ha)))))

end Fl4Proofs.P2.MmuAD
