/-
# P2 (line mmuAD, gen 16): **one A/D top over the union family** — `serializable_fl4_localAD`

Two A/D tops existed:
* `serializable_fl4_localU3d` (P2/E2EPU3j.lean): U1P's family (`famU1P`: W11, delPte, CNodeDelete, Copy / Mint and
  **PageMap**), native epochs only, over `ExecU3b`. Conclusion up to deferral: `∃ ℓ, ℓ.Perm s.log ∧ RunAll ℓ …`.
* `serializable_fl4_localVX11AG` (P2/E2EPVX11AG.lean): VX11's family (every U1 slot in native and VM epochs, no
  PageMap), over `ExecVX4d` ([S] `VmPweT` at VM serial exits). Conclusion `RunAll s.log …`.

This module states one top over the union: **`famAD`** is VX11's family with U1P's family as its native part (so
PageMap starts in native epochs), and the VM-epoch slots are VX11's eleven. The execution is `ExecVX4d`. PageMap's
present store needs the deferred view (`SerialADD.ARunD` / `InvD`), and every other slot fits it through
`insAP_of_insA`.
* **`execVX4d_aRunD`**: `execVX4d_aRunR` with `ARunD`. It is `execU3b_aRunD`'s step, plus VX11's VM epochs.
* `serializable_VXD_of` (`serializable_safeD`).
* `famAD`, `StartAD` (`StartVX11` over `StartU1P`), **`ad_startAt`**: `vx11_startAt`'s case split, with
  `serializable_fl4_localU3c_of`'s native cases (PageMap: `pm_hSFQK`).
* **`serializable_fl4_localAD`**. Its premises are U1P's: `P`, [P] `hIoa`, `B : PmObl7` ([P] `cs` / `lk`), `h0`,
  `hA0`, `hB`, `hc0`, `hM0`, the execution, `hq`. These contain VX11's, which are the same list without `B`. On top:
  [P] `MmuAD` (the `mmu` step) and [S] `VmPweT` (VM serial exits, in `ExecVX4d`). There is no [W].
  - Native `hIns`: gen 5 / 7's `insA_*` through `insAP_of_insA`, and PageMap's `insAP_pmR` with gen 12's `pmAccIns`.
  - VM `hIns`: gen 14 / 15's `insAW_*` through `insAP_of_insA`.

## Scope: PageMap in VM epochs
FL4 runs PageMap beside the gate whenever it is planned (fl4-sync `local_invocation`, lib.rs l. 538: no VCPU
condition), so it also starts while the layout has VCPUs. There it stores a present PTE (vspace.rs `write_mapping`
l. 446, `s.write(slot, e)` with `e` present). That case is **not** in `famAD`, and it is in no existing top:
VX11 (without A/D) has no PageMap slot. It needs:
1. a VM-epoch PageMap path and start fact, as vmscope gens 8 / 10 did for CNodeDelete / delPte. `pmPathsK`'s entry
   `PmPreG` contains P3's bundle `SlJAt` and needs `vcpus = ∅`, so it needs an `InvLX`-based copy with a walk fact
   and an [S] start entry (`GlueAt` [P]);
2. its `InsAP` at the VM layout: gen 11–12's `PmAccIns` walk with VM guard facts, restricted to `TabKU` (gen 15).
The A/D side needs nothing new. The deferral (`ARunD`, `InsAP`'s done set) does not depend on the epoch, so the
present store is handled as it is natively.

Named premises beyond U1P's: [P] `MmuAD`, [S] `VmPweT`. No [W]. No existing statement changed (new file; root import
list extended).

Gen 55 (line p3mc): `execVX4d_aRunD_C`, `serializable_VXD_of_C` (`P : LocPlatC`) and `ad_startAt_C`
(`P : LocPlatC`, `hRun : ChainRun`), the old names one-line corollaries (statements unchanged; P2/E2EPAD3).
-/
import Fl4Proofs.P2.E2EPVX11AG
import Fl4Proofs.P2.E2EPU3j
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg HwWr allowed_of_sinv
  InsA InsAP insAP_of_insA ARunD aRunD_inv serializable_safeD IgnG)
open Fl4Proofs.P2.MmuAD (MmuAD ADEq NotPresent adEq_equiv adEq_trans adOr_adEq)

noncomputable section
open Classical

section exec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {ι : Type}

/-- **`execVX4d_aRunD` on the re-based platform** (gen 55, in place: `P : LocPlatC` for `P : LocPlat`). -/
theorem execVX4d_aRunD_C {LP : PathsP ι}
    {SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop}
    (P : LocPlatC st arI AR MR)
    (hSF : ∀ (Ch : S → Prop) (K : KLayoutP) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K) c hs q i,
      (K.vcpus = ∅ → NatEpC P K Ch s) → (K.vcpus ≠ ∅ → VtxBundle4 st L K) →
      SF Ch K s.mem hK hU c hs q i → StartAt (LP i K s.mem hK hU) c hs s.mem q)
    (hIns : ∀ (Ch : S → Prop) (K : KLayoutP) (E : U64 → U64) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K)
      (hU : UserOKP K) (c : U64) (hs : U64 → Prop) (q : SP) (i : ι),
      (K.vcpus = ∅ → SerExitC P K.toKLayoutV Ch) → (K.vcpus ≠ ∅ → VtxBundle4 st L K) →
      (K.vcpus ≠ ∅ → VmPweT K E) → EpochJV K E s →
      MapsP K s → SF Ch K s.mem hK hU c hs q i → StartAt (LP i K s.mem hK hU) c hs s.mem q →
      InsAP (PWE K E) ADEq NotPresent s.own s.cls s.ko c hs ∅ s.mem q)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} {E : U64 → U64} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : SerExitC P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0) (h : ExecVX4dC LP SF P s0 K0 Ch0 s K Ch E) :
    ARunD ADEq NotPresent s0 s (PWE K E) ∧ RegionOKP K ∧ UserOKP K ∧ MapsP K s ∧
      (K.vcpus = ∅ → SerExitC P K.toKLayoutV Ch) ∧ (K.vcpus ≠ ∅ → VtxBundle4 st L K) ∧
      (K.vcpus ≠ ∅ → VmPweT K E) ∧ EpochJV K E s := by
  obtain ⟨hK0, hU0⟩ := okP_R_C hB hc0
  induction h with
  | refl => exact ⟨.refl _, hK0, hU0, hM0, fun _ => hB, fun hn => (hn hc0.1).elim, fun hn => (hn hc0.1).elim,
      epochJV_ser hc0.2⟩
  | @step s1 s1' K1 K1' Ch1 Ch1' c1 E1 _ hS g hPw ih =>
    obtain ⟨hR, hK, hU, hM, hX, hV, hW, J⟩ := ih
    obtain ⟨⟨_, _, _, _, _, I, -⟩, hSI, -⟩ := aRunD_inv adEq_equiv (fun _ _ h => adEq_np h) h0 hA0 hR
    have hN : K1.vcpus = ∅ → NatEpC P K1 Ch1 s1 := fun nv => ⟨hX nv, epoch_start (J.toJ nv)⟩
    have hst : ∀ p0 k W, s1.ph c1 = .loc p0 (.start k) W →
        ∃ i, SF Ch1 K1 s1.mem hK hU c1 (fun l => s1.lk l = some c1) k i ∧
          StartAt (LP i K1 s1.mem hK hU) c1 (fun l => s1.lk l = some c1) s1.mem k := by
      intro p0 k W hph
      obtain ⟨i, hi⟩ := g.start p0 k W hph hK hU
      exact ⟨i, hi, hSF _ _ s1 _ _ _ _ _ i hN hV hi⟩
    have hok : Fl4Proofs.P2.Serial.SafeStep s1 c1 s1' := by
      refine ⟨g.arm, fun p0 k W hph => ?_⟩
      obtain ⟨i, -, hP⟩ := hst p0 k W hph
      rw [hM.own, hM.cls, hM.ko]
      exact (LP i K1 s1.mem hK hU).safe (moveHeldP hK) (ownDepP hK hU) hP
    by_cases hs : SerStep s1 c1
    · rw [if_pos hs]
      have hnl : NoLoc s1 := I.r.inv.clo hs.1
      have hR' := ARunD.regate (PWE K1' s1'.mem) hR hs.1
      have hig : IgnG (PWE K1' s1'.mem) s1'.own := by
        rw [(g.serG hs).own]
        rcases g.ser hs with ⟨hXs, nv, hc⟩ | ⟨hne, hc, hb⟩
        · exact pwe_own (okP_R_C hXs ⟨nv, hc⟩).1
        · exact pwe_own (hb.b.okP hc).1
      have hst' : ARunD ADEq NotPresent s0 s1' (PWE K1' s1'.mem) :=
        .step hR' hS hok (fun p0 k W hph => absurd (by rw [hph]; trivial) (hnl c1)) hig
      rcases g.ser hs with ⟨hXs, nv, hc⟩ | ⟨hne, hc, hb⟩
      · have hK' := okP_R_C hXs ⟨nv, hc⟩
        exact ⟨hst', hK'.1, hK'.2, g.serG hs, fun _ => hXs, fun hn => (hn nv).elim, fun hn => (hn nv).elim,
          epochJV_ser hc⟩
      · have hK' := hb.b.okP hc
        exact ⟨hst', hK'.1, hK'.2, g.serG hs, fun nv => (hne nv).elim, fun _ => hb, hPw hs,
          epochJV_ser hc⟩
    · rw [if_neg hs]
      obtain ⟨eK, eC⟩ := g.keep hs
      subst eK eC
      have hal := allowed_of_sinv hSI c1
      have hM' := maps_stepP hK hM hal hS hs
      refine ⟨.step hR hS hok (fun p0 k W hph => ?_) (by rw [hM'.own]; exact pwe_own hK), hK, hU, hM', hX, hV, hW,
        epochJV_keep J (fun x hx => step_gate_keep hM hal hS hs hx)⟩
      obtain ⟨i, hi, hP⟩ := hst p0 k W hph
      exact hIns _ _ _ _ hK hU _ _ _ i hX hV hW J hM hi hP
  | hw _ hH ih =>
    obtain ⟨hR, hK, hU, hM, hX, hV, hW, J⟩ := ih
    exact ⟨.hw hR (hH.hwWr hK hM), hK, hU, maps_hwP hK hM hH, hX, hV, hW,
      epochJV_keep J (fun x hx => hw_gate_keep hK hM hH hx)⟩
  | mmu _ hH ih =>
    obtain ⟨hR, hK, hU, hM, hX, hV, hW, J⟩ := ih
    exact ⟨.ad hR (adWr_pwe hK hM hH), hK, hU, maps_pwe hK hM hH, hX, hV, hW, epochJV_mmu J hH⟩

/-- **An `ExecVX4d` execution is an `ARunD` one at the epoch's paging words**; `hIns` also receives `VmPweT` in VM
epochs (`execVX4c_aRunR`'s proof). -/
theorem execVX4d_aRunD {LP : PathsP ι}
    {SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop}
    (P : LocPlat st arI AR MR)
    (hSF : ∀ (Ch : S → Prop) (K : KLayoutP) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K) c hs q i,
      (K.vcpus = ∅ → NatEp P K Ch s) → (K.vcpus ≠ ∅ → VtxBundle4 st L K) →
      SF Ch K s.mem hK hU c hs q i → StartAt (LP i K s.mem hK hU) c hs s.mem q)
    (hIns : ∀ (Ch : S → Prop) (K : KLayoutP) (E : U64 → U64) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K)
      (hU : UserOKP K) (c : U64) (hs : U64 → Prop) (q : SP) (i : ι),
      (K.vcpus = ∅ → SerExitW P K.toKLayoutV Ch) → (K.vcpus ≠ ∅ → VtxBundle4 st L K) →
      (K.vcpus ≠ ∅ → VmPweT K E) → EpochJV K E s →
      MapsP K s → SF Ch K s.mem hK hU c hs q i → StartAt (LP i K s.mem hK hU) c hs s.mem q →
      InsAP (PWE K E) ADEq NotPresent s.own s.cls s.ko c hs ∅ s.mem q)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} {E : U64 → U64} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0) (h : ExecVX4d LP SF P s0 K0 Ch0 s K Ch E) :
    ARunD ADEq NotPresent s0 s (PWE K E) ∧ RegionOKP K ∧ UserOKP K ∧ MapsP K s ∧
      (K.vcpus = ∅ → SerExitW P K.toKLayoutV Ch) ∧ (K.vcpus ≠ ∅ → VtxBundle4 st L K) ∧
      (K.vcpus ≠ ∅ → VmPweT K E) ∧ EpochJV K E s :=
  execVX4d_aRunD_C P.toC hSF hIns h0 hA0 hB hc0 hM0 h.toC

/-- **`serializable_VXD_of` on the re-based platform** (gen 55, in place: `P : LocPlatC` for `P : LocPlat`). -/
theorem serializable_VXD_of_C {LP : PathsP ι}
    {SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop}
    (P : LocPlatC st arI AR MR)
    (hSF : ∀ (Ch : S → Prop) (K : KLayoutP) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K) c hs q i,
      (K.vcpus = ∅ → NatEpC P K Ch s) → (K.vcpus ≠ ∅ → VtxBundle4 st L K) →
      SF Ch K s.mem hK hU c hs q i → StartAt (LP i K s.mem hK hU) c hs s.mem q)
    (hIns : ∀ (Ch : S → Prop) (K : KLayoutP) (E : U64 → U64) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K)
      (hU : UserOKP K) (c : U64) (hs : U64 → Prop) (q : SP) (i : ι),
      (K.vcpus = ∅ → SerExitC P K.toKLayoutV Ch) → (K.vcpus ≠ ∅ → VtxBundle4 st L K) →
      (K.vcpus ≠ ∅ → VmPweT K E) → EpochJV K E s →
      MapsP K s → SF Ch K s.mem hK hU c hs q i → StartAt (LP i K s.mem hK hU) c hs s.mem q →
      InsAP (PWE K E) ADEq NotPresent s.own s.cls s.ko c hs ∅ s.mem q)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} {E : U64 → U64} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : SerExitC P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0) (h : ExecVX4dC LP SF P s0 K0 Ch0 s K Ch E) (hq : NoLoc s) :
    ∃ ℓ : List SP, ℓ.Perm s.log ∧ RunAll ℓ s0.mem s.mem :=
  serializable_safeD adEq_equiv (fun _ _ h => adEq_np h) h0 hA0
    (execVX4d_aRunD_C P hSF hIns h0 hA0 hB hc0 hM0 h).1 hq

/-- **Every quiescent `ExecVX4d` state is serial up to deferring A/D entries**, given `hSF` and `hIns`. -/
theorem serializable_VXD_of {LP : PathsP ι}
    {SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop}
    (P : LocPlat st arI AR MR)
    (hSF : ∀ (Ch : S → Prop) (K : KLayoutP) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K) c hs q i,
      (K.vcpus = ∅ → NatEp P K Ch s) → (K.vcpus ≠ ∅ → VtxBundle4 st L K) →
      SF Ch K s.mem hK hU c hs q i → StartAt (LP i K s.mem hK hU) c hs s.mem q)
    (hIns : ∀ (Ch : S → Prop) (K : KLayoutP) (E : U64 → U64) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K)
      (hU : UserOKP K) (c : U64) (hs : U64 → Prop) (q : SP) (i : ι),
      (K.vcpus = ∅ → SerExitW P K.toKLayoutV Ch) → (K.vcpus ≠ ∅ → VtxBundle4 st L K) →
      (K.vcpus ≠ ∅ → VmPweT K E) → EpochJV K E s →
      MapsP K s → SF Ch K s.mem hK hU c hs q i → StartAt (LP i K s.mem hK hU) c hs s.mem q →
      InsAP (PWE K E) ADEq NotPresent s.own s.cls s.ko c hs ∅ s.mem q)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} {E : U64 → U64} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0) (h : ExecVX4d LP SF P s0 K0 Ch0 s K Ch E) (hq : NoLoc s) :
    ∃ ℓ : List SP, ℓ.Perm s.log ∧ RunAll ℓ s0.mem s.mem :=
  serializable_VXD_of_C P.toC hSF hIns h0 hA0 hB hc0 hM0 h.toC hq

end exec

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **The union family**: VX11's with U1P's family (PageMap included) as the native part, at `masksWr_plain`. -/
abbrev famAD {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl7 st Cs Ω Sg Ac Locks) :=
  PathsP.sum (PathsP.sum (PathsP.sum (PathsP.sum (PathsP.sum (PathsP.sum (PathsP.sum
    (PathsP.sum (PathsP.sum (PathsP.sum (PathsP.sum (famU1P st ar hA a0 B)
    (vxSlotPV st ar hA (masksWr_plain st))) (vtSlotPV st ar hA (masksWr_plain st)))
    (ioSlotPX st ar hA (masksWr_plain st))) (stSlotPX st ar hA (masksWr_plain st)))
    (irqSlotPX st ar hA (masksWr_plain st))) (slSlotPX st ar hA (masksWr_plain st) L.total a0))
    (invSlotVX st ar hA (masksWr_plain st))) (cmSlotVX st ar hA (masksWr_plain st)))
    (delPteSlotVX st ar hA (masksWr_plain st))) (vmFSlotPY st ar hA (masksWr_plain st)))
    (vmRSlotPY st ar hA (masksWr_plain st))

/-- The union's start facts: VX11's over U1P's. -/
abbrev StartAD {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl7 st Cs Ω Sg Ac Locks) :=
  StartVX11 st ar hA (masksWr_plain st) L.total a0 (StartU1P st ar hA a0 B (arI := arI) (AR := AR) (MR := MR))

/-- **`ad_startAt` on the re-based platform**
(gen 55, in place: `P : LocPlatC` and `hRun : ChainRun` for `P : LocPlat` / `hIoa`). -/
theorem ad_startAt_C (P : LocPlatC st arI AR MR) (hRun : ChainRun st arI AR MR)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl7 st Cs Ω Sg Ac Locks) :
    ∀ (Ch : S → Prop) (K : KLayoutP) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K) c hs q i,
      (K.vcpus = ∅ → NatEpC P K Ch s) → (K.vcpus ≠ ∅ → VtxBundle4 st L K) →
      StartAD st ar hA a0 B (arI := arI) (AR := AR) (MR := MR) Ch K s.mem hK hU c hs q i →
      StartAt (famAD st ar hA a0 B i K s.mem hK hU) c hs s.mem q := by
  intro Ch K s hK hU c hs q i hN hV hsf
  rcases i with ((((((((((i | j) | j) | j) | j) | j) | j) | j) | j) | j) | j) | j
  · have hsf' : K.vcpus = ∅ ∧ StartU1P st ar hA a0 B (arI := arI) (AR := AR) (MR := MR) Ch K s.mem hK hU c hs
        q i := hsf
    obtain ⟨nv, hsf'⟩ := hsf'
    obtain ⟨hX, hE⟩ := hN nv
    have hC := hX.chainOf
    rcases i with i | (((j | j) | j) | j)
    · exact startAt_U_C st ar hA (masksWr_plain st) L.total a0 hRun hC hE hsf'
    · exact delPteStart_at st ar hA (masksWr_plain st) hC hE hsf'
    · exact invStartU2_at st ar hA (masksWr_plain st) hC hE hsf'
    · exact cmStartU2_at st ar hA (masksWr_plain st) hC hE hsf'
    · exact pm_hSFQK hA (masksWr_plain st) B Ch K s.mem hK hU c hs q j hC hE hsf'
  · have hsf' : VxStartV2 st ar hA (masksWr_plain st) K s.mem hK hU c hs q j := hsf
    exact vxStartV_at st ar hA (masksWr_plain st) (vxStartV_of_V2 (hV (vxStartV2_ne hsf')).b hsf')
  · have hsf' : VtStartV4 st ar hA (masksWr_plain st) K s.mem hK hU c hs q j := hsf
    exact vtStartV2_at (hV hsf'.1).b (vtStartV2_of_V4 (hV hsf'.1).b hsf')
  · have hsf' : IoStartX5 st ar hA (masksWr_plain st) K s.mem hK hU c hs q j := hsf
    exact ioStartX_at (hV hsf'.1) (ioStartX_of_X5 (hV hsf'.1) hsf')
  · have hsf' : StStartX st ar hA (masksWr_plain st) K s.mem hK hU c hs q j := hsf
    exact stStartX_at (hV hsf'.1) hsf'
  · have hsf' : IrqStartX st ar hA (masksWr_plain st) K s.mem hK hU c hs q j := hsf
    exact irqStartX_at (hV hsf'.1) hsf'
  · have hsf' : SlStartX st ar hA (masksWr_plain st) L.total a0 K s.mem hK hU c hs q j := hsf
    exact slStartX_at (hV hsf'.1) hsf'
  · have hsf' : InvStartX9 st ar hA (masksWr_plain st) K s.mem hK hU c hs q j := hsf
    exact invStartX_at (hV hsf'.1) (invStartX_of9 (hV hsf'.1) hsf')
  · have hsf' : CMStartX9 st ar hA (masksWr_plain st) K s.mem hK hU c hs q j := hsf
    exact cmStartX_at (hV hsf'.1) (cmStartX_of9 (hV hsf'.1) hsf')
  · have hsf' : DelPteStartX st ar hA (masksWr_plain st) K s.mem hK hU c hs q j := hsf
    exact delPteStartX_at (hV hsf'.1) hsf'
  · have hsf' : VmFStartY st ar hA (masksWr_plain st) K s.mem hK hU c hs q j := hsf
    exact vmFStartY_at (hV hsf'.1) hsf'
  · have hsf' : VmRStartY st ar hA (masksWr_plain st) K s.mem hK hU c hs q j := hsf
    exact vmRStartY_at (hV hsf'.1) hsf'

/-- **The union's start case split** (`vx11_startAt`, native cases `serializable_fl4_localU3c_of`'s). -/
theorem ad_startAt (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl7 st Cs Ω Sg Ac Locks) :
    ∀ (Ch : S → Prop) (K : KLayoutP) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K) c hs q i,
      (K.vcpus = ∅ → NatEp P K Ch s) → (K.vcpus ≠ ∅ → VtxBundle4 st L K) →
      StartAD st ar hA a0 B (arI := arI) (AR := AR) (MR := MR) Ch K s.mem hK hU c hs q i →
      StartAt (famAD st ar hA a0 B i K s.mem hK hU) c hs s.mem q :=
  ad_startAt_C st ar hA a0 P.toC (chainRun_of P hIoa) B

/-- **FL4 end to end with the host walker's A/D writes, over the union family** (module docstring): every U1 slot in
native and VM epochs and PageMap in native epochs. Premises: U1P's (`P`, [P] `hIoa`, `B` = [P] `cs` / [P] `lk`,
`h0`, `hA0`, `hB`, `hc0`, `hM0`, the execution, `hq`), [P] `MmuAD` (`ExecVX4d`'s `mmu` step), [S] `VmPweT` (its VM
serial exits). No [W]. -/
theorem serializable_fl4_localAD (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl7 st Cs Ω Sg Ac Locks)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} {E : U64 → U64} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecVX4d (famAD st ar hA a0 B) (StartAD st ar hA a0 B (arI := arI) (AR := AR) (MR := MR))
      P s0 K0 Ch0 s K Ch E)
    (hq : NoLoc s) :
    ∃ ℓ : List SP, ℓ.Perm s.log ∧ RunAll ℓ s0.mem s.mem := by
  refine serializable_VXD_of P (ad_startAt st ar hA a0 P hIoa B) ?_ h0 hA0 hB hc0 hM0 h hq
  intro Ch K E s hK hU c hs q i hX hV hW J hM hsf hP
  rcases i with ((((((((((i | j) | j) | j) | j) | j) | j) | j) | j) | j) | j) | j
  · have hsf' : K.vcpus = ∅ ∧ StartU1P st ar hA a0 B (arI := arI) (AR := AR) (MR := MR) Ch K s.mem hK hU c hs
        q i := hsf
    have nv := hsf'.1
    have J' := J.toJ nv
    have hb : ∃ σe, SlJAt (L := L) K.toKLayout σe := by
      obtain ⟨σe, hC'⟩ := (hX nv).chainOf
      have hσe : Ch σe := by
        obtain ⟨_, _, _, _, _, _, _, _, h'⟩ := hC'
        exact h'
      exact ⟨σe, ChainOf.bun hC' σe hσe⟩
    rcases i with i | (((j | j) | j) | j)
    · exact insAP_of_insA (insA_w11 st ar hA (masksWr_plain st) L.total a0 i (hK := hK) (hU := hU) hb J' hM hP)
    · exact insAP_of_insA (insA_delR st ar hA (masksWr_plain st) j (hK := hK) (hU := hU) hb J' hM hP)
    · exact insAP_of_insA (insA_invR st ar hA (masksWr_plain st) j (hK := hK) (hU := hU) hb J' hM hP)
    · exact insAP_of_insA (insA_cm st ar hA (masksWr_plain st) j (hK := hK) (hU := hU) hb J' hM hP)
    · exact insAP_pmR hA (masksWr_plain st) B (pmAccIns st ar hA (masksWr_plain st) B) K E s hK hU c hs q j
        hb J' hM hP
  · have hsf' : VxStartV2 st ar hA (masksWr_plain st) K s.mem hK hU c hs q j := hsf
    have hne := vxStartV2_ne hsf'
    exact insAP_of_insA (insAW_vx st ar hA (masksWr_plain st) K E s hK hU c hs q j hne (hV hne) (hW hne).toVmPwe
      J hM hP)
  · have hsf' : VtStartV4 st ar hA (masksWr_plain st) K s.mem hK hU c hs q j := hsf
    exact insAP_of_insA (insAW_vt st ar hA (masksWr_plain st) K E s hK hU c hs q j hsf'.1 (hV hsf'.1)
      (hW hsf'.1).toVmPwe J hM hP)
  · have hsf' : IoStartX5 st ar hA (masksWr_plain st) K s.mem hK hU c hs q j := hsf
    exact insAP_of_insA (insAW_io st ar hA (masksWr_plain st) K E s hK hU c hs q j hsf'.1 (hV hsf'.1)
      (hW hsf'.1).toVmPwe J hM hP)
  · have hsf' : StStartX st ar hA (masksWr_plain st) K s.mem hK hU c hs q j := hsf
    exact insAP_of_insA (insAW_st st ar hA (masksWr_plain st) K E s hK hU c hs q j hsf'.1 (hV hsf'.1)
      (hW hsf'.1).toVmPwe J hM hP)
  · have hsf' : IrqStartX st ar hA (masksWr_plain st) K s.mem hK hU c hs q j := hsf
    exact insAP_of_insA (insAW_irq st ar hA (masksWr_plain st) K E s hK hU c hs q j hsf'.1 (hV hsf'.1)
      (hW hsf'.1).toVmPwe J hM hP)
  · have hsf' : SlStartX st ar hA (masksWr_plain st) L.total a0 K s.mem hK hU c hs q j := hsf
    exact insAP_of_insA (insAW_sl st ar hA (masksWr_plain st) L.total a0 K E s hK hU c hs q j hsf'.1 (hV hsf'.1)
      (hW hsf'.1).toVmPwe J hM hP)
  · have hsf' : InvStartX9 st ar hA (masksWr_plain st) K s.mem hK hU c hs q j := hsf
    exact insAP_of_insA (insAW_inv st ar hA (masksWr_plain st) K E s hK hU c hs q j hsf'.1 (hV hsf'.1)
      (hW hsf'.1) J hM hP)
  · have hsf' : CMStartX9 st ar hA (masksWr_plain st) K s.mem hK hU c hs q j := hsf
    exact insAP_of_insA (insAW_cm st ar hA (masksWr_plain st) K E s hK hU c hs q j hsf'.1 (hV hsf'.1)
      (hW hsf'.1).toVmPwe J hM hP)
  · have hsf' : DelPteStartX st ar hA (masksWr_plain st) K s.mem hK hU c hs q j := hsf
    exact insAP_of_insA (insAW_del st ar hA (masksWr_plain st) K E s hK hU c hs q j hsf'.1 (hV hsf'.1)
      (hW hsf'.1) J hM hP)
  · have hsf' : VmFStartY st ar hA (masksWr_plain st) K s.mem hK hU c hs q j := hsf
    exact insAP_of_insA (insAW_vmF st ar hA (masksWr_plain st) K E s hK hU c hs q j hsf'.1 (hV hsf'.1)
      (hW hsf'.1).toVmPwe J hM hP)
  · have hsf' : VmRStartY st ar hA (masksWr_plain st) K s.mem hK hU c hs q j := hsf
    exact insAP_of_insA (insAW_vmR st ar hA (masksWr_plain st) K E s hK hU c hs q j hsf'.1 (hV hsf'.1)
      (hW hsf'.1).toVmPwe J hM hP)

end top

end
end Fl4Proofs.P2.E2EP
