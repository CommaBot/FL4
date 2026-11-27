/-
# P2 (line mmuAD, gen 8): **U1P's family under A/D writes** — the PageMap slot, deferred A/D entries

`serializable_fl4_localU1P` (P2/E2EPU1P.lean) is U1 plus line pte's PageMap slot (`pmPathsK`). PageMap's
`write_mapping` (vspace.rs l. 444-458: `old = read(slot); write(slot, e); flush`) stores a **present** leaf entry
under the leaf's lock, and the lock is released only at `leave`, after `set_cap`'s tail and `after_invocation`.
Between the store and `leave` another core whose thread runs in that address space can walk to the new entry
and set A (and D) in it (Intel SDM 3A §4.8, locked RMW): the walker does not respect FL4's software lock. Such a
write cannot be logged at its time, before PageMap's entry (whose serial run stores `e` without the bits); it is
serialised right *after* PageMap's entry (`SerialADD`), which is sound because PageMap does not write the leaf
again after its store and every read of a paging word it makes is masked (`InsAP`).

* `famU1P`, `StartU1P`: U1P's family and start facts at `masksWr_plain` (as `famU2` for U3b).
* **`execU3b_aRunD`**: an `ExecU3b` execution over any family is an `SerialADD.ARunD ADEq NotPresent` one with
  word set `PWE K E` (the regate before each serial step, `IgnG` from `pwe_own`), given the start facts' `StartAt`
  (`hSF`) and, at every start, `InsAP` of the started body (`hIns`, nothing done).
* **`serializable_U3c_of`**: hence, at every quiescent state, **some permutation `ℓ` of `s.log` (A/D entries made
  while their word's PageMap holder was in progress moved right after the holder's entry) runs serially from
  `s0.mem` to `s.mem`** (`serializable_safeD`).
* **`serializable_fl4_localU3c_of`**: U1P's premises over `ExecU3b (famU1P …)`, the W11, delPte, CNodeDelete and
  Copy / Mint shares of `hIns` discharged by gen 5 / 7 (`insA_w11`, `insA_delR`, `insA_invR`, `insA_cm`, through
  `insAP_of_insA`), with **`hPm`** — `InsAP` of the PageMap body at its start — as the one explicit hypothesis.
* `run_apl`: the serial-section note (handoff, gen 8): a straight-line body of writes runs to `apl`.

No [W], no new [J]; the [P] is `MmuAD` (P2/MmuADWalk.lean), in `ExecU3b`'s `mmu` step, plus U1P's `B : PmObl7`
([P] `cs`, [P] `lk`). `hPm` is a hypothesis of a reduction theorem, not a premise of a top. No existing statement
changed.
-/
import Fl4Proofs.P2.E2EPU3f
import Fl4Proofs.P2.E2EPU1P
import Fl4Proofs.P2.SerialADD
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll Run Prog Step PureGlue hwCfg HwWr
  allowed_of_sinv InsA InsAP insAP_of_insA ARunD aRunD_inv serializable_safeD IgnG apl)
open Fl4Proofs.P2.MmuAD (MmuAD ADEq NotPresent adEq_equiv and_eq_of_adEq kP)

noncomputable section
open Classical

/-- `ADEq` keeps the present bit. -/
theorem adEq_np {u w : U64} (h : ADEq u w) : NotPresent u ↔ NotPresent w := by
  unfold NotPresent; rw [and_eq_of_adEq h kP]

section exec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {ι : Type}

/-- **An `ExecU3b` execution is an `ARunD` one** (module docstring). -/
theorem execU3b_aRunD {LP : PathsP ι}
    {SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop}
    (hSF : ∀ (Ch : S → Prop) (K : KLayoutP) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K) c hs q i,
      (∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) →
      (∃ s1 : Cfg U64 U64 U64 U64, (K.vcpus = ∅ ∧ K.ptes = ptesR K s1.mem) ∧ ∀ x, GateW K x → s.mem x = s1.mem x) →
      SF Ch K s.mem hK hU c hs q i → StartAt (LP i K s.mem hK hU) c hs s.mem q)
    (hIns : ∀ (K : KLayoutP) (E : U64 → U64) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K)
      (c : U64) (hs : U64 → Prop) (q : SP) (i : ι), (∃ σe, SlJAt (L := L) K.toKLayout σe) → EpochJ K E s →
      MapsP K s → StartAt (LP i K s.mem hK hU) c hs s.mem q →
      InsAP (PWE K E) ADEq NotPresent s.own s.cls s.ko c hs ∅ s.mem q)
    (P : LocPlat st arI AR MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} {E : U64 → U64} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0) (h : ExecU3b LP SF P s0 K0 Ch0 s K Ch E) :
    ARunD ADEq NotPresent s0 s (PWE K E) ∧ RegionOKP K ∧ UserOKP K ∧ MapsP K s ∧
      SerExitW P K.toKLayoutV Ch ∧ EpochJ K E s := by
  obtain ⟨hK0, hU0⟩ := okP_R hB hc0
  induction h with
  | refl => exact ⟨.refl _, hK0, hU0, hM0, hB, epochJ_ser hc0⟩
  | @step s1 s1' K1 K1' Ch1 Ch1' c1 E1 _ hS g ih =>
    obtain ⟨hR, hK, hU, hM, hX, J⟩ := ih
    obtain ⟨⟨_, _, _, _, _, I, -⟩, hSI, -⟩ := aRunD_inv adEq_equiv (fun _ _ h => adEq_np h) h0 hA0 hR
    have hb : ∃ σe, SlJAt (L := L) K1.toKLayout σe := by
      obtain ⟨σe, hC'⟩ := hX.chainOf
      have hσe : Ch1 σe := by
        obtain ⟨_, _, _, _, _, _, _, _, h'⟩ := hC'
        exact h'
      exact ⟨σe, ChainOf.bun hC' σe hσe⟩
    have hst : ∀ p0 k W, s1.ph c1 = .loc p0 (.start k) W →
        ∃ i, StartAt (LP i K1 s1.mem hK hU) c1 (fun l => s1.lk l = some c1) s1.mem k := by
      intro p0 k W hph
      obtain ⟨i, hi⟩ := g.start p0 k W hph hK hU
      exact ⟨i, hSF _ _ s1 _ _ _ _ _ i hX.chainOf (epoch_start J) hi⟩
    have hok : Fl4Proofs.P2.Serial.SafeStep s1 c1 s1' := by
      refine ⟨g.arm, fun p0 k W hph => ?_⟩
      obtain ⟨i, hP⟩ := hst p0 k W hph
      rw [hM.own, hM.cls, hM.ko]
      exact (LP i K1 s1.mem hK hU).safe (moveHeldP hK) (ownDepP hK hU) hP
    by_cases hs : SerStep s1 c1
    · rw [if_pos hs]
      have hnl : NoLoc s1 := I.r.inv.clo hs.1
      have hR' := ARunD.regate (PWE K1' s1'.mem) hR hs.1
      have hK' := okP_R (g.serX hs) (g.serC hs)
      have hig : IgnG (PWE K1' s1'.mem) s1'.own := by
        rw [(g.serG hs).own]; exact pwe_own hK'.1
      refine ⟨.step hR' hS hok (fun p0 k W hph => absurd (by rw [hph]; trivial) (hnl c1)) hig, hK'.1, hK'.2,
        g.serG hs, g.serX hs, epochJ_ser (g.serC hs)⟩
    · rw [if_neg hs]
      obtain ⟨eK, eC⟩ := g.keep hs
      subst eK eC
      have hal := allowed_of_sinv hSI c1
      have hM' := maps_stepP hK hM hal hS hs
      refine ⟨.step hR hS hok (fun p0 k W hph => ?_) (by rw [hM'.own]; exact pwe_own hK), hK, hU, hM', hX,
        epochJ_keep J (fun x hx => step_gate_keep hM hal hS hs hx)⟩
      obtain ⟨i, hP⟩ := hst p0 k W hph
      exact hIns _ _ _ hK hU _ _ _ i hb J hM hP
  | hw _ hH ih =>
    obtain ⟨hR, hK, hU, hM, hX, J⟩ := ih
    exact ⟨.hw hR (hH.hwWr hK hM), hK, hU, maps_hwP hK hM hH, hX,
      epochJ_keep J (fun x hx => hw_gate_keep hK hM hH hx)⟩
  | mmu _ hH ih =>
    obtain ⟨hR, hK, hU, hM, hX, J⟩ := ih
    exact ⟨.ad hR (adWr_pwe hK hM hH), hK, hU, maps_pwe hK hM hH, hX, epochJ_mmu J hH⟩

/-- **Every quiescent `ExecU3b` state is serial up to deferring A/D entries**, given `hSF` and `hIns`. -/
theorem serializable_U3c_of {LP : PathsP ι}
    {SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop}
    (hSF : ∀ (Ch : S → Prop) (K : KLayoutP) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K) c hs q i,
      (∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) →
      (∃ s1 : Cfg U64 U64 U64 U64, (K.vcpus = ∅ ∧ K.ptes = ptesR K s1.mem) ∧ ∀ x, GateW K x → s.mem x = s1.mem x) →
      SF Ch K s.mem hK hU c hs q i → StartAt (LP i K s.mem hK hU) c hs s.mem q)
    (hIns : ∀ (K : KLayoutP) (E : U64 → U64) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K)
      (c : U64) (hs : U64 → Prop) (q : SP) (i : ι), (∃ σe, SlJAt (L := L) K.toKLayout σe) → EpochJ K E s →
      MapsP K s → StartAt (LP i K s.mem hK hU) c hs s.mem q →
      InsAP (PWE K E) ADEq NotPresent s.own s.cls s.ko c hs ∅ s.mem q)
    (P : LocPlat st arI AR MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} {E : U64 → U64} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0) (h : ExecU3b LP SF P s0 K0 Ch0 s K Ch E) (hq : NoLoc s) :
    ∃ ℓ : List SP, ℓ.Perm s.log ∧ RunAll ℓ s0.mem s.mem :=
  serializable_safeD adEq_equiv (fun _ _ h => adEq_np h) h0 hA0
    (execU3b_aRunD hSF hIns P h0 hA0 hB hc0 hM0 h).1 hq

end exec

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- U1P's family (`serializable_fl4_localU1P`'s) at `masksWr_plain`. -/
abbrev famU1P {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl7 st Cs Ω Sg Ac Locks) :=
  PathsP.sum (fl4LocW11JA st ar hA (masksWr_plain st) L.total a0)
    (PathsP.sum (PathsP.sum (PathsP.sum (delPteSlot st ar hA (masksWr_plain st)) (invSlotU st ar hA (masksWr_plain st)))
      (cmSlotU st ar hA (masksWr_plain st))) (pmPathsK hA (masksWr_plain st) B))

/-- U1P's start facts at `masksWr_plain`. -/
abbrev StartU1P {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl7 st Cs Ω Sg Ac Locks) :=
  StartU1 st ar hA (masksWr_plain st) L.total a0 arI AR MR (StartInvU1P st ar hA (masksWr_plain st) B)

/-- **FL4 end to end with the PageMap slot and A/D writes to every paging word of the epoch, given `hPm`**
(module docstring): U1P's premises over `ExecU3b`; the A/D entries a PageMap holder's tenure delays are moved after
its entry (`ℓ` a permutation of `s.log`). `hPm`: the PageMap body is `InsAP` at its start. -/
theorem serializable_fl4_localU3c_of (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl7 st Cs Ω Sg Ac Locks)
    (hPm : ∀ (K : KLayoutP) (E : U64 → U64) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K)
      (c : U64) (hs : U64 → Prop) (q : SP) (j : I64 × localinv.Plan), (∃ σe, SlJAt (L := L) K.toKLayout σe) →
      EpochJ K E s → MapsP K s → StartAt (pmPathsK hA (masksWr_plain st) B j K s.mem hK hU) c hs s.mem q →
      InsAP (PWE K E) ADEq NotPresent s.own s.cls s.ko c hs ∅ s.mem q)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} {E : U64 → U64} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecU3b (famU1P st ar hA a0 B) (StartU1P st ar hA a0 B (arI := arI) (AR := AR) (MR := MR)) P s0 K0 Ch0
      s K Ch E)
    (hq : NoLoc s) :
    ∃ ℓ : List SP, ℓ.Perm s.log ∧ RunAll ℓ s0.mem s.mem := by
  refine serializable_U3c_of ?_ ?_ P h0 hA0 hB hc0 hM0 h hq
  · intro Ch K s hK hU c hs q i hC hE hsf
    rcases i with i | (((j | j) | j) | j)
    · exact startAt_U st ar hA (masksWr_plain st) L.total a0 P hIoa hC hE hsf
    · exact delPteStart_at st ar hA (masksWr_plain st) hC hE hsf
    · exact invStartU2_at st ar hA (masksWr_plain st) hC hE hsf
    · exact cmStartU2_at st ar hA (masksWr_plain st) hC hE hsf
    · exact pm_hSFQK hA (masksWr_plain st) B Ch K s.mem hK hU c hs q j hC hE hsf
  · intro K E s hK hU c hs q i hb J hM hP
    rcases i with i | (((j | j) | j) | j)
    · exact insAP_of_insA (insA_w11 st ar hA (masksWr_plain st) L.total a0 i hb J hM hP)
    · exact insAP_of_insA (insA_delR st ar hA (masksWr_plain st) j hb J hM hP)
    · exact insAP_of_insA (insA_invR st ar hA (masksWr_plain st) j hb J hM hP)
    · exact insAP_of_insA (insA_cm st ar hA (masksWr_plain st) j hb J hM hP)
    · exact hPm K E s hK hU c hs q j hb J hM hP

end top

/-! ## The serial-section note -/

section ser
variable {A V C L : Type} [DecidableEq A]

/-- A straight-line body of writes. -/
def wrsAD : List (C × A × V) → Prog A V L
  | [] => .done
  | e :: l => .wr e.2.1 e.2.2 (wrsAD l)

/-- **A serial section's net effect is a body**: the writes it made, the walker's A/D writes interleaved in
order, as one straight-line `Prog` (`Step.serial` leaves the body uninterpreted; handoff, gen 8). -/
theorem run_apl (l : List (C × A × V)) (m : A → V) : Run (wrsAD (L := L) l) m (apl l m) := by
  induction l generalizing m with
  | nil => exact .done m
  | cons e l ih => exact .wr (ih _)

end ser

end
end Fl4Proofs.P2.E2EP
