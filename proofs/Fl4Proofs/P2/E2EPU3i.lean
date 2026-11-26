/-
# P2 (line mmuAD, gen 11): the PageMap slot restricted to the epoch's start states; `hPm` from accepted runs

gen 8's `serializable_fl4_localU3c_of` leaves `hPm`: `InsAP (PWE K E) ADEq NotPresent … ∅` of the PageMap body at its
start. As gen 7 did for delPte / CNodeDelete, the slot `pmPathsK` is restricted to `QPs (KU K E)` states (`pmR`): a
start state of the epoch satisfies it (`epoch_start` + `qPs_of_convR` + `qPs_ku`).

* **`pm_decR`**: PageMap's declined runs touch no paging word of the epoch: `LocalPath.decG` with
  `R0 := IoRSR st K.ptU Locks` (gen 10's `ioRSR_ptU_notPWE`), the run reproduced by `inv_dec_guardRSR` at the
  layout `ptU K` (`IoPre.ptU`), the alternative moved by `alt_pmU` / `alt_ptU` / `Alt.anti`, the seen words by
  `IoPre.lockSlotR` (`pm_seenR`), the declined writes by `ioDS_notPWE`.
* **`insAP_pmR`**: `hPm` from `PmAccIns` (accepted runs of the restricted slot are `InsTP … Set.univ ∅`) by
  `LocalPath.insAQP` (gen 9).
* `serializable_fl4_localU3c_ofAcc`: gen 8's `serializable_fl4_localU3c_of` with `hPm` replaced by `PmAccIns`.
* **`serializable_fl4_localU3c`**: U1P's premises (`P`, [P] `hIoa`, `B : PmObl7` = [P] `cs` / [P] `lk`, `h0`, `hA0`,
  `hB`, `hc0`, `hM0`, the execution, `hq`), [P] `MmuAD` (in `ExecU3b`), and one named premise:

Named premises of `serializable_fl4_localU3c` beyond U1P's and [P] `MmuAD`:
* [W] `PmAccInsW.acc` — `PmAccIns`: accepted runs of the restricted PageMap slot are `InsTP … Set.univ ∅` at the
  epoch's paging words (Rust `vspace.rs` `decode_page_map` l. 551, `write_mapping` l. 444-458; see its docstring).

The declined runs, the restriction and the start are proved here (no premise). No existing statement changed.
-/
import Fl4Proofs.P2.E2EPU3g
import Fl4Proofs.P2.E2EPU3h
import Fl4Proofs.P2.E2EADQP
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath InsTP)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll InsAP)
open Fl4Proofs.P2.MmuAD (MmuAD ADEq NotPresent adEq_equiv)

noncomputable section
open Classical

section seen
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP} {μ : U64 → U64} {s : S}
variable {T Rp Scs Nt : Set U64} {H : Heap} {Z : U64 → Nat}

/-- The plan's seen words are `IoRSR` words at `ptU K` (`pm_seen` with `IoPre.lockSlotR`). -/
theorem pm_seenR (hJ : SlJAt (L := L) K.toKLayout s) (hq : PmQF st Cs Ω Sg Ac Locks p K μ s)
    (P : IoPre st K.ptU T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    ∀ x, SeenW p x → IoRSR st K.ptU Locks s x := by
  intro x hx
  obtain ⟨-, -, -, -, -, -, hsl, -, hlk, hSn⟩ := pm_core hq
  have h0 : p.slot ≠ 0#u64 := fun e => slJAt_slot0 hJ (e ▸ hsl)
  rcases hSn x hx with rfl | rfl
  · exact P.lockSlotR hsl (hlk h0) (by simp [layout.cte.CAP0]) (by simp [layout.cte.CAP0])
  · exact P.lockSlotR hsl (hlk h0) (by simp [layout.cte.CAP1]) (by simp [layout.cte.CAP1])

end seen

section slot
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)

/-- PageMap's slot restricted to `QPs (KU K E)` states. -/
noncomputable abbrev pmR {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl7 st Cs Ω Sg Ac Locks)
    (j : I64 × localinv.Plan) (K : KLayoutP) (E m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) :
    LocalPath (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) :=
  (pmPathsK hA hm B j K m hK hU).restrQ (QPt (KU K E) (pmPathsK hA hm B j K m hK hU))
    (qPt_stab (KU K E) _ (fun b hb => Or.inl hb))

/-- **What is left of `hPm`**: accepted runs of the restricted PageMap slot are `InsTP` at the epoch's paging words
from nothing done. -/
def PmAccIns {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl7 st Cs Ω Sg Ac Locks) : Prop :=
  ∀ (j : I64 × localinv.Plan) (K : KLayoutP) (E m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K),
    let P := pmR st ar hA hm B j K E m hK hU
    ∀ s a r, P.Pre s → P.F P.ar P.st s a = ok r → P.Acc r.1 →
      InsTP P.st P.ar (PWE K E) ADEq NotPresent (· ∈ K.user) Set.univ ∅ P.p s a

variable {st ar}

/-- **PageMap's declined runs touch no paging word of the epoch** (module docstring). -/
theorem pm_decR {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl7 st Cs Ω Sg Ac Locks)
    (j : I64 × localinv.Plan) {K : KLayoutP} {E m : U64 → U64} (hK : RegionOKP K) (hU : UserOKP K) :
    let P := pmR st ar hA hm B j K E m hK hU
    ∀ s s' a r, P.Pre s → P.F P.ar P.st s a = ok r → ¬ P.Acc r.1 →
      @Alt _ P.st P.L (P.RS s) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) s s' →
      Within P.st P.ar (fun b => ¬ PWE K E b) (fun b => b ∈ K.user ∨ ¬ PWE K E b) P.p s' a := by
  intro P
  refine LocalPath.decG P (R0 := fun s => IoRSR st K.ptU Locks s) ?_ ?_ ?_
  · intro s s' a r r' hs0 hr hn Al hr'
    have hs : PmPreG st Cs Ω Sg Ac Locks j.2 K m s := hs0.1
    obtain ⟨⟨hJ, hq, hG⟩, -, -⟩ := hs
    have P0' := hq.1.1.1
    have Pu := P0'.ptU hG
    have Al' : Alt st (PmRSU st K Locks s) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m)
        (· ∈ K.user) s s' := Al
    have AlR := (alt_ptU hG (alt_pmU Al')).anti (R' := IoRSR st K.ptU Locks s) (fun x hx => hx.1)
    have hr0 : r.1 ≠ true := hn
    exact inv_dec_guardRSR hA Pu (pm_seenR hJ hq Pu) AlR hr hr0 hr'
  · intro s x hs0 hx
    have hs : PmPreG st Cs Ω Sg Ac Locks j.2 K m s := hs0.1
    exact ioRSR_ptU_notPWE hK (ksNoE_conv hs.1.2.2.choose_spec.1.2) hx
  · intro s x hs0 hx
    have hs : PmPreG st Cs Ω Sg Ac Locks j.2 K m s := hs0.1
    exact ioDS_notPWE hK (ksNoE_conv hs.1.2.2.choose_spec.1.2) hs.1.2.1.1.1.1 hx

/-- **`hPm` from `PmAccIns`** (module docstring). -/
theorem insAP_pmR {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl7 st Cs Ω Sg Ac Locks)
    (hAcc : PmAccIns st ar hA hm B) (K : KLayoutP) (E : U64 → U64) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K)
    (hU : UserOKP K) (c : U64) (hs : U64 → Prop) (q : SP) (j : I64 × localinv.Plan)
    (hb : ∃ σe, SlJAt (L := L) K.toKLayout σe) (J : EpochJ K E s) (hM : MapsP K s)
    (h : StartAt (pmPathsK hA hm B j K s.mem hK hU) c hs s.mem q) :
    InsAP (PWE K E) ADEq NotPresent s.own s.cls s.ko c hs ∅ s.mem q := by
  obtain ⟨σ, a, hpre, hc, hl, hμ, rfl⟩ := h
  have hpre' : PmPreG st Cs Ω Sg Ac Locks j.2 K s.mem σ := hpre
  obtain ⟨s1, ⟨nv, he⟩, hkeep⟩ := epoch_start J
  have hq0 : QPs K st σ := qPs_of_convR he nv hb hkeep hpre'.1.2.1.1.1.1.kb.symm hμ
  have hqK : QPs (KU K E) st σ := qPs_ku L J hb hq0 hμ
  have h' : StartAt (pmR st ar hA hm B j K E s.mem hK hU) c hs s.mem
      ((pmPathsK hA hm B j K s.mem hK hU).body σ a) :=
    ⟨σ, a, ⟨hpre, hqK⟩, hc, hl, hμ, rfl⟩
  rw [hM.own, hM.cls, hM.ko]
  exact LocalPath.insAQP _ adEq_equiv (moveHeldP hK) (ownDepP hK hU) (pwe_own hK) (fun x hx => pwe_ko hK _ hx)
    (fun x hx => pwe_user hU hx) (hAcc j K E s.mem hK hU)
    (fun s1 s2 a r hs1 hr hn Al => pm_decR hA hm B j hK hU s1 s2 a r hs1 hr hn Al) h'

end slot

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **gen 8's reduction with `hPm` replaced by `PmAccIns`** (module docstring). -/
theorem serializable_fl4_localU3c_ofAcc (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl7 st Cs Ω Sg Ac Locks)
    (hAcc : PmAccIns st ar hA (masksWr_plain st) B)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} {E : U64 → U64} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecU3b (famU1P st ar hA a0 B) (StartU1P st ar hA a0 B (arI := arI) (AR := AR) (MR := MR)) P s0 K0 Ch0
      s K Ch E)
    (hq : NoLoc s) :
    ∃ ℓ : List SP, ℓ.Perm s.log ∧ RunAll ℓ s0.mem s.mem :=
  serializable_fl4_localU3c_of st ar hA a0 P hIoa B
    (fun K E s hK hU c hs q j hb J hM hP =>
      insAP_pmR (st := st) (ar := ar) hA (masksWr_plain st) B hAcc K E s hK hU c hs q j hb J hM hP)
    h0 hA0 hB hc0 hM0 h hq

/-- **[W] The PageMap walk** (named premise; `PmAccIns`): every accepted run of the restricted PageMap slot is
`InsTP (PWE K E) ADEq NotPresent (· ∈ K.user) Set.univ ∅` of `R.invBodyPmG` at its entry. Rust:
`crates/fl4-core/src/arch/x86_64/vspace.rs` `decode_page_map` (l. 551) and `write_mapping` (l. 444-458). Why it
holds (handoff gens 8-10): the only paging words of the epoch an accepted run reads are the small-page walk of
`page_entry_slot` (`lookup_pt_slot`: `&&& 1`, `&&& 128`, `ADDR_MASK`; tree-level `sIns_lookup_pt_slot`) and the
locked leaf in `write_mapping` (`&&& P_PRESENT`, `rights_raised`, `rights_lowered`: `rr_adEq` / `rl_adEq`), and
the only paging word it stores is that leaf, once (`insTP_write_mapping`); every other access is an `IoRSR (ptU K)`
/ `IoWS` / user word (`ioRSR_ptU_notPWE`, `ioWS_notPWE`) or an ASID word (`AsidW`, off `PWE` under `QPs (KU K E)`).
Not discharged here: the per-call guard reproduction of the PageMap prefix, decode and tail on a store guarded off
`PWE` (the `IoRSR` copies of `pm_s2` / `pm_decRd` / `pmAccG` / `pmFinG`, as gen 7 made of delAccX / delFinR). -/
structure PmAccInsW {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl7 st Cs Ω Sg Ac Locks) : Prop where
  /-- [W] accepted PageMap runs are `InsTP` at the epoch's paging words. -/
  acc : PmAccIns st ar hA (masksWr_plain st) B

/-- **FL4 end to end with the PageMap slot and A/D writes to every paging word of the epoch** (module docstring):
premises U1P's (`P`, [P] `hIoa`, `B` = [P] `cs` / [P] `lk`, `h0`, `hA0`, `hB`, `hc0`, `hM0`, the execution, `hq`),
[P] `MmuAD` (in `ExecU3b`'s `mmu` step) and [W] `hW : PmAccInsW` (the PageMap walk). -/
theorem serializable_fl4_localU3c (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl7 st Cs Ω Sg Ac Locks)
    (hW : PmAccInsW st ar hA B)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} {E : U64 → U64} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecU3b (famU1P st ar hA a0 B) (StartU1P st ar hA a0 B (arI := arI) (AR := AR) (MR := MR)) P s0 K0 Ch0
      s K Ch E)
    (hq : NoLoc s) :
    ∃ ℓ : List SP, ℓ.Perm s.log ∧ RunAll ℓ s0.mem s.mem :=
  serializable_fl4_localU3c_ofAcc st ar hA a0 P hIoa B hW.acc h0 hA0 hB hc0 hM0 h hq

end top

end
end Fl4Proofs.P2.E2EP
