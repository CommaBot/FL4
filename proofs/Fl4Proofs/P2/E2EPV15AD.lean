/-
# P2 (line p3mc, gen 45): `PmObl7`'s glue facts, and **the A/D-admitting top over `ExecV15`** (permuted conclusion)

## 1. `PmObl7`'s [P] `cs` and `lk` (handoff §49d 1)
* **`cs`** (`∀ c ∈ Cs, c.val < 64`) is a condition on the slot's core-set *parameter*, not on the world. It holds for
  every `Cs` inside the layout's cores at any P3 bundle state (P2/SlJLk.lean:187 `SlJAt.ncores_le`: a bundle layout
  counts at most 64 cores, from P3's `JKern.csLt`; P2/SlJLk.lean:201 `hCs_of_sub`), and the start layout `K0` has
  one (`hB`: every serial exit is a P3 chain, `SerExitW.chainOf` / `ChainLay.bun`). So **`pmCs_of_serExit`**
  discharges it from `Cs ⊆ {c | c.val < K0.ncores}` — the set P3's slots use (`invStartW_sat`, `SlJAt.hCs`) — and
  **`serializable_fl4_V15_pmKC`** is gen 44's authoritative top with `cs` replaced by that inclusion (a choice of
  the parameter: the slot's cores are the machine's).
* **`lk`** (`PmLk`: a user-word write at a bundle state keeps `Locks`) stays **[P]**. `Locks` is the glue's ghost
  "locks this core holds", tied to the model only by `StartAt`'s `Locks σ = hs` with `hs l ↔ s.lk l = some c`
  (`E2E.Fl4Step.start`); `Serial.Cfg.lk` is a separate component that no memory write touches, and the lock words are
  deliberately not in model memory. A memory-read lock map cannot meet that equality: fl4-store's lock table
  (`crates/fl4-store/src/lock.rs`, `TABLE`: 4,096 hashed `AtomicU64`) stores `1`, not the holder, and is indexed by
  hash, not by object address; the holder is only in the glue's stack-local `Held` record (P2/SlJLk.lean:1–25 has the
  full argument). So `lk` is a lock-discipline fact about the glue (its held set lives in kernel data, which no user
  store reaches), not provable inside the model. **`pmLk_of_kernelDet`** gives it from the slightly more primitive
  [P] `hKD` (the glue's locks are determined by kernel words at every bundle state, `KernDetAt`, P2/SlJLk.lean:67),
  by `hlk_of_kernelDet`.

## 2. The A/D-admitting top over `ExecV15` (handoff §46e 1, §46b)
`ExecV15`'s `ad` step is `cfg.AdStep K E s.mem a x`; here it is the host walker's write, **`MmuAD (PWE K E)`**
([P], P2/MmuADWalk.lean), `PWE K E` the epoch's paging words (P2/MmuADEpoch.lean).
* **`InsV15 cfg`** [J] (per start, at the CoreView start): the armed program (the start's body `k0` where `¬ NoV`, or
  its re-annotation `annV`) is `InsAP (PWE K E) ADEq NotPresent … ∅` at the physical memory — mmuAD's `hIns`
  (P2/E2EPAD.lean:62 `execVX4d_aRunD`), whose instances mmuAD proves only at **physical-memory** starts (`insA_w11`,
  `insA_delR`, `insA_invR`, `insA_cm`, PageMap's `insAP_pmR`): a CoreView start's body is the same program, armed at a
  memory agreeing with the view off the words the view rewrites, but the transfer of those `InsA` proofs to view
  starts is not done (see §50 of the handoff). Not discharged.
* **`execV15_aRunD`**: an `ExecV15` run (the A/D step inside `MmuAD (PWE K E)`, no VCPU) is a `SerialADD.ARunD ADEq
  NotPresent` run at `PWE K E`: safe starts exactly as `exec_safeRunPV9` / `execPV9_of_WPRV10S` (the view start's
  `EpochPteN` now from the A/D epoch invariant `EpochJV` by mmuAD's `epoch_start`), `InsAP` at starts by `InsV15`,
  `IgnG` by `pwe_own`, hardware steps `HwWr`, A/D steps `ADWr` (`adWr_pwe`), the epoch by `epochJV_*`.
* **`serializable_fl4_V15_ad`**: every quiescent state is serial **up to a permutation of the log**:
  `∃ ℓ, ℓ.Perm s.log ∧ RunAll ℓ s0.mem s.mem` (`SerialADD.serializable_safeD`). Premises: `SlotOblV15 cfg`, `InsV15
  cfg` [J], `hAd` (the A/D step is `MmuAD (PWE K E)`), `VcpuNone`, `P`, `h0`, `hA0`, `hB`, `hc0`, `hM0`, the
  execution, `hq`.
* Instance: **`ExecCfg.nativePmKAD B`** (gen 44's `nativePmK B` with `AdStep := MmuAD (PWE K E)`),
  `slotOblV13PmKAD`, **`serializable_fl4_V15_pmKAD`**: V13's slots and PageMap on CoreView with A/D writes; premises
  gen 44's (`P`, [P] `hIoa`, `B : PmObl7` = [P] `cs` / `lk`, `h0`, `hA0`, `hB`, `hc0`, `hM0`, `hq`), the
  execution over `nativePmKAD` ([P] `MmuAD` in its `ad` step) and **`InsV15` [J]**. `execV15_pmKAD_of_pmK`: every
  gen-44 execution is one of these (so the A/D top covers it, with the weaker, permuted conclusion).

VCPU-admitting tops (§46e 3) are not here: `execV15_aRunD` keeps `VcpuNone`.

Named premises added: `InsV15` [J] (A/D top only), `hKD` [P] (alternative to `lk`). Removed from the
`serializable_fl4_V15_pmKC` top: [P] `cs`. New module; no existing statement changes.

Gen 48 (in place, statements unchanged): `InsV15V` (`InsV15` at layouts without a VCPU), `insV15V_of`,
`execV15_aRunDV` (split out of `execV15_aRunD`, which uses the obligation only at the current layout, without a VCPU),
`serializable_fl4_V15_adV`.

Gen 56 (handoff p3mc §61) retired, with `ExecWPRV10–12` and the V15 stepping stones: `pmCs_of_serExit`,
`pmObl7_ofSer`, `serializable_fl4_V15_pmKC`, `insV15V_of`, `execV15_aRunDV`, `execV15_aRunD`,
`serializable_fl4_V15_ad`, `serializable_fl4_V15_adV`, `slotOblV13PmKAD`, `serializable_fl4_V15_pmKAD`.
-/
import Fl4Proofs.P2.InvPmGdV
import Fl4Proofs.P2.E2EPVX11AD
import Fl4Proofs.P2.E2EPU3g
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg VEq Safe narrowSP safe_narrow
  allowed_of_sinv InsAP ARunD aRunD_inv serializable_safeD IgnG SafeStep)
open Fl4Proofs.P2.MmuAD (MmuAD ADEq NotPresent adEq_equiv)

noncomputable section
open Classical

/-! ## 1. `PmObl7`'s glue facts -/

section glue
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}

/-- **`PmObl7.lk` from `hKD`** [P] (module docstring §1): the glue's locks are determined by kernel words at every
bundle state. -/
theorem pmLk_of_kernelDet
    (hKD : ∀ (K : OwnMap.KLayout) (s : S), SlJAt (L := L) K s → KernDetAt (L := L) K Locks s) :
    PmLk st Locks :=
  hlk_of_kernelDet hKD

end glue

section topC
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}

end topC

/-! ## 2. The A/D-admitting top over `ExecV15` -/

section ad
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {ι : Type}

variable (arI AR MR) in
/-- **[J] The armed program is insensitive to the walker's A/D writes** (module docstring §2): at every CoreView start
(the start fact at the view, `VEq` of the view source, the chain, the A/D epoch invariant), the armed program — the
body `k0` where `¬ NoV`, or its re-annotation `annV` — is `InsAP (PWE K E) ADEq NotPresent … ∅` at the physical
memory (mmuAD's `hIns`, P2/E2EPAD.lean:62, at view starts). -/
def InsV15 (cfg : ExecCfg S ι) : Prop :=
  ∀ (Ch : S → Prop) (s : Cfg U64 U64 U64 U64) (K : KLayoutP) (E : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (c : U64) (k k0 : SP) (ρ : U64 → U64) (i : ι),
    (∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) → EpochJV K E s → MapsP K s →
    VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem →
    cfg.SF Ch K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k0 i →
    ((k = k0 ∧ ¬ cfg.NoV i) ∨ k = annV s K c ρ k0) →
    InsAP (PWE K E) ADEq NotPresent s.own s.cls s.ko c (fun l => s.lk l = some c) ∅ s.mem k

variable (arI AR MR) in
/-- **[J] `InsV15` asked only at layouts without a VCPU** (gen 48): `InsV15` with the hypothesis `K.vcpus = ∅`, which
`execV15_aRunD`'s invariant carries at every start (`VcpuNone`). `InsV15` gives it (`insV15V_of`). At a layout with a
VCPU the W11 slots' start facts (sl, vmF, vmR: `startAt_slB`, `startU_of_U2` need `EpochPteN`, hence no VCPU) say
nothing about the armed program, so this is the form a discharge can reach. -/
def InsV15V (cfg : ExecCfg S ι) : Prop :=
  ∀ (Ch : S → Prop) (s : Cfg U64 U64 U64 U64) (K : KLayoutP) (E : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (c : U64) (k k0 : SP) (ρ : U64 → U64) (i : ι), K.vcpus = ∅ →
    (∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) → EpochJV K E s → MapsP K s →
    VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem →
    cfg.SF Ch K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k0 i →
    ((k = k0 ∧ ¬ cfg.NoV i) ∨ k = annV s K c ρ k0) →
    InsAP (PWE K E) ADEq NotPresent s.own s.cls s.ko c (fun l => s.lk l = some c) ∅ s.mem k

set_option maxHeartbeats 1000000 in
/-- **`execV15_aRunDV` on the re-based platform** (gen 54, in place: `P : LocPlatC` for `P : LocPlat`). -/
theorem execV15_aRunDV_C {cfg : ExecCfg S ι} (O : SlotOblV15 (L := L) arI AR MR cfg)
    (hI : InsV15V (L := L) arI AR MR cfg)
    (hAd : ∀ K E m a x, cfg.AdStep K E m a x → MmuAD (PWE K E) m a x) (hV : cfg.VcpuNone)
    (P : LocPlatC st arI AR MR) {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop}
    {E : U64 → U64} (h0 : Init s0) (hA0 : ArmInv s0) (hB : ∀ e, SerExitC P K0.toKLayoutV (Ch0 e))
    (hc0 : cfg.VcpuOK K0 s0.mem ∧ K0.ptes = ptesR K0 s0.mem) (hM0 : MapsP K0 s0)
    (h : ExecV15C cfg P s0 K0 Ch0 s K Ch E) :
    ARunD ADEq NotPresent s0 s (PWE K E) ∧ RegionOKP K ∧ UserOKP K ∧ MapsP K s ∧
      (∀ e, SerExitC P K.toKLayoutV (Ch e)) ∧ K.vcpus = ∅ ∧ EpochJV K E s := by
  have nv0 : K0.vcpus = ∅ := hV _ _ hc0.1
  obtain ⟨hK0, hU0⟩ := okP_R_C (hB 0#u64) ⟨nv0, hc0.2⟩
  induction h with
  | refl => exact ⟨.refl _, hK0, hU0, hM0, hB, nv0, epochJV_ser hc0.2⟩
  | @step s1 s1' K1 K1' Ch1 Ch1' c1 E1 _ hS g ih =>
    obtain ⟨hR, hK, hU, hM, hX, nv, J⟩ := ih
    obtain ⟨⟨_, _, _, _, _, I, -⟩, hSI, -⟩ := aRunD_inv adEq_equiv (fun _ _ h => adEq_np h) h0 hA0 hR
    obtain ⟨e1, hCe, hk1⟩ := epoch_start (J.toJ nv)
    have hstart : ∀ p0 k W, s1.ph c1 = .loc p0 (.start k) W →
        Safe s1.own s1.cls s1.ko c1 (fun l => s1.lk l = some c1) s1.mem k ∧
        InsAP (PWE K1 E1) ADEq NotPresent s1.own s1.cls s1.ko c1 (fun l => s1.lk l = some c1) ∅ s1.mem k := by
      intro p0 k W hph
      obtain ⟨ρ, hVq, i, k0, hi, hk⟩ := g.start p0 k W hph hK hU
      have hρg : ∀ x, GateW K1 x → ρ x = e1.mem x := fun x hx =>
        (hVq.2.1 x (by rw [hM.own, hx s1.mem]; exact Or.inr rfl)).trans (hk1 x hx)
      have hEv : EpochPteN K1 (CoreView.view K1.toKLayout c1 ρ) :=
        epochPteN_view c1 (epochPteN_of ⟨e1, hCe, hρg⟩)
      have hC := (hX c1).chainOf
      have hP : StartAt (cfg.Fam i K1 (CoreView.view K1.toKLayout c1 ρ) hK hU) c1 (fun l => s1.lk l = some c1)
          (CoreView.view K1.toKLayout c1 ρ) k0 :=
        O.sf (Ch1 c1) _ { s1 with mem := CoreView.view K1.toKLayout c1 ρ } hK hU _ _ _ i hC hEv hi
      have hS0 : CoreView.view K1.toKLayout c1 ρ = ρ →
          Safe s1.own s1.cls s1.ko c1 (fun l => s1.lk l = some c1) s1.mem k0 := by
        intro hv
        have hP' := hP
        rw [hv] at hP'
        have hko := ko_viewP hK hM hVq
        have hVq' := hVq
        rw [hM.own, hM.cls, hko] at hVq' ⊢
        exact (cfg.Fam i K1 ρ hK hU).safeH (moveHeldP hK) (ownDepP hK hU) hP' hVq'
      refine ⟨?_, hI (Ch1 c1) s1 K1 E1 hK hU c1 k k0 ρ i nv hC J hM hVq hi hk⟩
      rcases hk with ⟨rfl, hn⟩ | rfl
      · by_cases hv : CoreView.view K1.toKLayout c1 ρ = ρ
        · exact hS0 hv
        · exact O.vs s1 K1 hK hU c1 k ρ i hM hVq hn hv hP
      · by_cases hn : cfg.NoV i
        · exact O.fh (Ch1 c1) s1 K1 hK hU c1 k0 ρ i hC hEv hi hM hVq hn
        · by_cases hv : CoreView.view K1.toKLayout c1 ρ = ρ
          · exact safe_narrow _ (hS0 hv) ∅
          · exact vSafe9_of_vSafe (O.vs s1 K1 hK hU c1 k0 ρ i hM hVq hn) hv hP
    have hok : SafeStep s1 c1 s1' := ⟨g.arm, fun p0 k W hph => (hstart p0 k W hph).1⟩
    by_cases hs : SerStep s1 c1
    · rw [if_pos hs]
      have hnl : NoLoc s1 := I.r.inv.clo hs.1
      have hR' := ARunD.regate (PWE K1' s1'.mem) hR hs.1
      have nv' : K1'.vcpus = ∅ := hV _ _ (g.serC hs).1
      have hK' := okP_R_C (g.serX hs 0#u64) ⟨nv', (g.serC hs).2⟩
      have hig : IgnG (PWE K1' s1'.mem) s1'.own := by
        rw [(g.serG hs).own]; exact pwe_own hK'.1
      exact ⟨.step hR' hS hok (fun p0 k W hph => absurd (by rw [hph]; trivial) (hnl c1)) hig, hK'.1, hK'.2,
        g.serG hs, g.serX hs, nv', epochJV_ser (g.serC hs).2⟩
    · rw [if_neg hs]
      obtain ⟨eK, eC⟩ := g.keep hs
      subst eK eC
      have hal := allowed_of_sinv hSI c1
      have hM' := maps_stepP hK hM hal hS hs
      exact ⟨.step hR hS hok (fun p0 k W hph => (hstart p0 k W hph).2) (by rw [hM'.own]; exact pwe_own hK), hK,
        hU, hM', hX, nv, epochJV_keep J (fun x hx => step_gate_keep hM hal hS hs hx)⟩
  | hw _ hH ih =>
    obtain ⟨hR, hK, hU, hM, hX, nv, J⟩ := ih
    exact ⟨.hw hR (hH.hwWr hK hM), hK, hU, maps_hwP hK hM hH, hX, nv,
      epochJV_keep J (fun x hx => hw_gate_keep hK hM hH hx)⟩
  | ad _ hH ih =>
    obtain ⟨hR, hK, hU, hM, hX, nv, J⟩ := ih
    have hH' := hAd _ _ _ _ _ hH
    exact ⟨.ad hR (adWr_pwe hK hM hH'), hK, hU, maps_pwe hK hM hH', hX, nv, epochJV_mmu J hH'⟩

/-- **`serializable_fl4_V15_adV` on the re-based platform** (gen 54, in place: `P : LocPlatC` for `P : LocPlat`). -/
theorem serializable_fl4_V15_adV_C {cfg : ExecCfg S ι} (O : SlotOblV15 (L := L) arI AR MR cfg)
    (hI : InsV15V (L := L) arI AR MR cfg) (hAd : ∀ K E m a x, cfg.AdStep K E m a x → MmuAD (PWE K E) m a x)
    (hV : cfg.VcpuNone) (P : LocPlatC st arI AR MR) {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP}
    {Ch0 Ch : U64 → S → Prop} {E : U64 → U64} (h0 : Init s0) (hA0 : ArmInv s0)
    (hB : ∀ e, SerExitC P K0.toKLayoutV (Ch0 e)) (hc0 : cfg.VcpuOK K0 s0.mem ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0) (h : ExecV15C cfg P s0 K0 Ch0 s K Ch E) (hq : NoLoc s) :
    ∃ ℓ : List SP, ℓ.Perm s.log ∧ RunAll ℓ s0.mem s.mem :=
  serializable_safeD adEq_equiv (fun _ _ h => adEq_np h) h0 hA0
    (execV15_aRunDV_C O hI hAd hV P h0 hA0 hB hc0 hM0 h).1 hq

end ad

section pmAD
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop) (MR : A3 → Fl4Spec.MachineState → Prop)
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}

/-- **V13's slots and PageMap on CoreView, with the host walker's A/D writes** (module docstring §2): gen 44's
`nativePmK B` with `AdStep := MmuAD (PWE K E)` [P]. -/
def ExecCfg.nativePmKAD (B : PmObl7 st Cs Ω Sg Ac Locks) : ExecCfg S (IxV13Pm S) where
  Fam := fl4LocV13PmK st ar hA a0 B
  NoV := NoVPm (S := S)
  SF := StartV13PmK st ar hA a0 arI AR MR B
  VcpuOK := fun K _ => K.vcpus = ∅
  AdStep := fun K E m a x => MmuAD (PWE K E) m a x

variable {arI AR MR}

/-- **`slotOblV13PmKAD` on the re-based platform** (gen 54, in place: `P : LocPlatCR` for `P : LocPlat` / `hIoa`). -/
theorem slotOblV13PmKAD_C (P : LocPlatCR st arI AR MR)
    (B : PmObl7 st Cs Ω Sg Ac Locks) :
    SlotOblV15 (L := L) arI AR MR (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B) :=
  have O := slotOblV13PmK_C st ar hA a0 P B (pmFhK_holds st ar hA B)
  ⟨O.sf, O.vs, O.fh⟩

end pmAD

end
end Fl4Proofs.P2.E2EP
