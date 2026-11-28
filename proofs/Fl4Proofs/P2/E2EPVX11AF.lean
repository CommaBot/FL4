/-
# P2 (line mmuAD, gen 14): **Copy / Mint in VM epochs under A/D writes** — `serializable_fl4_localVX11AF`

`E2EPVX11AE` leaves [W] `VmInsAE` with three fields (CNodeDelete, Copy / Mint, delPte in VM epochs). This module
discharges the Copy / Mint field.

* `insA_cutKU` (generic): `insA_kuV` with the no-paging-word fact `hNG` of the runs as a hypothesis (the KU-layout
  path may differ from the `K`-layout one in its `Pre`).
* **`insAW_cm`**: VX8's Copy / Mint path `cmPathVX` at `KU K E` has the same states, program and read set as at `K`;
  its `Pre` differs only in the entry fact `FCM st j (KU K E) m` (the same `InvQCMW`, and `InvVF` whose fields are
  `K.toKLayoutV`'s) and in `QPs (KU K E)` instead of `QPs K`, so a restricted start of the `K` path is a start of the
  `KU` path (`InvLX.mono`), and `cmAvPX` at `KU K E` (layout from `VmPwe`) gives `hNG` by `noPWE_of_avoid`.
* **`serializable_fl4_localVX11AF`**: `serializable_fl4_localVX11AE` with [W] **`VmInsAF`** (two fields:
  CNodeDelete and delPte in VM epochs, both `unmap_page`'s masked walk).

Named premises of `serializable_fl4_localVX11AF` beyond VX11's and [P] `MmuAD`: [S] `VmPwe` at VM serial exits (in
`ExecVX4c`, E2EPVX11AE), [W] `VmInsAF` (`inv`, `del`). No existing statement changed.

Gen 56 (handoff p3mc §61) retired, with `ExecWPRV10–12` and the V15 stepping stones: `serializable_fl4_localVX11AF`.
-/
import Fl4Proofs.P2.E2EPVX11AE
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg HwWr allowed_of_sinv
  InsA ARunR aRunR_inv serializable_safeR)
open Fl4Proofs.P2.MmuAD (MmuAD ADEq NotPresent adEq_equiv adEq_trans adOr_adEq)

noncomputable section
open Classical

section gen
variable {K : KLayoutP} {E : U64 → U64}

/-- **`insA_kuV` with the runs' no-paging-word fact as a hypothesis.** -/
theorem insA_cutKU {s : Cfg U64 U64 U64 U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {hs : U64 → Prop}
    {q : SP} (hP : VmPwe K E) (J : EpochJV K E s) (hM : MapsP K s)
    (R : LocalPath (ownV K.toKLayoutV) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout s.mem) (· ∈ K.user))
    (hAvK : AvoidP K R)
    (hQ : ∀ σ, (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx s.mem) _ hAvK).Pre σ → QPt K R σ)
    (hNG : ∀ s1 s2 a, (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx s.mem) _ hAvK).Pre s1 →
      QPt (KU K E) R s1 →
      @Alt _ R.st R.L ((LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx s.mem) _ hAvK).RS s1)
        (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout s.mem) (· ∈ K.user) s1 s2 →
      Within R.st R.ar (fun b => ¬ PWE K E b) (fun b => b ∈ K.user ∨ ¬ PWE K E b) R.p s2 a)
    (h : StartAt (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx s.mem) _ hAvK) c hs s.mem q) :
    InsA (PWE K E) ADEq NotPresent s.own s.cls s.ko c hs s.mem q := by
  obtain ⟨σ, a, hpre, hc, hl, hμ, rfl⟩ := h
  letI := R.L
  have hq : QPt (KU K E) R σ := qPs_kuV J hP (hQ σ hpre) (fun x hx hu => hμ x hx hu)
  have h' : StartAt ((LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx s.mem) _ hAvK).restrQ
      (QPt (KU K E) (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx s.mem) _ hAvK))
      (qPt_stab (KU K E) _ (fun b hb => Or.inl hb))) c hs s.mem
      ((LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx s.mem) _ hAvK).body σ a) :=
    ⟨σ, a, ⟨hpre, hq⟩, hc, hl, hμ, rfl⟩
  rw [hM.own, hM.cls, hM.ko]
  refine LocalPath.insA _ (moveHeldP hK) (ownDepP hK hU) (pwe_own hK) ?_ h'
  intro s1 s2 a' hp1 hA'
  exact hNG s1 s2 a' hp1.1 hp1.2 hA'

end gen

section slots
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)

/-- **Copy / Mint in VM epochs.** -/
theorem insAW_cm : InsAW st (cmSlotVX st ar hA hm) := by
  intro K E s hK hU c hs q j _ _ hP J hM h
  by_cases hp : InvPremX st j K
  · rw [cmSlotVX_pos st ar hA hm hp] at h
    have hp' : InvPremX st j (KU K E) := ⟨hp.lk⟩
    refine insA_cutKU hP J hM _ (cmAvPX st ar hA hm j K s.mem hK hU hp) (fun σ hσ => hσ.2) ?_ h
    intro s1 s2 a hp1 hq hAl
    obtain ⟨⟨hL, hW⟩, -⟩ := hp1
    have hpre : (cmPathVX st ar hA hm j (KU K E) s.mem (regionOKP_kuV hK hP) (userOKP_ku hU) hp').Pre s1 :=
      ⟨⟨hL.mono (fun _ hF => ⟨hF.1, ⟨hF.2.vu, hF.2.ko⟩⟩), hW⟩, hq⟩
    exact LocalPath.noPWE_of_avoid _ (fun _ _ hb => ownV_pwe_gateV hK hP hb)
      (cmAvPX st ar hA hm j (KU K E) s.mem (regionOKP_kuV hK hP) (userOKP_ku hU) hp') hpre hAl
      (fun x hx hn => ⟨hx, fun hp'' => hn (pte_ku hU hp'')⟩) a
  · unfold cmSlotVX at h
    rw [dif_neg hp] at h
    obtain ⟨σ, a, hpre, -⟩ := h
    exact (hpre : False).elim

/-- **[W] The two VM-epoch slots left** (named premise; module docstring): CNodeDelete and delPte in VM epochs are
`InsA` at the epoch's paging words, given `VmPwe`. -/
structure VmInsAF : Prop where
  /-- [W] CNodeDelete in VM epochs (masked walk of `unmap_page`). -/
  inv : InsAW st (invSlotVX st ar hA hm)
  /-- [W] delPte in VM epochs (masked walk, store `0`). -/
  del : InsAW st (delPteSlotVX st ar hA hm)

end slots

/-! ## 5. The top -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

end top

end
end Fl4Proofs.P2.E2EP
