/-
# P2 (line p3mc, gen 29): FL4 end to end without `VSafe9`

With U28 (P2/E2EPU28) every non-io start of the family is exempt: **`u28At_all`** — at every start index `i` with
`¬ IoIx i` and for every layout / core / locks / view / body, `U28At` holds (vmF, vmR, sl: their classes are all
starts; st: the target is homed (`StHAt`) or not (`StFhAt`); irq: `u24At_irq`; vx, vt: all; CNodeDelete, Copy /
Mint, PTE delete: all). So the exempt predicate is no premise at all, and the chain-level step need not mention
`VSafe9` [J]:

* `Fl4StepWPRV11` / `ExecWPRV11`: U10's step (`Fl4StepWPRV10`) whose `start` field's second arm is only "the armed
  program is the re-annotated body `annV k0`" — **no `VSafe9` [J]**, no exempt predicate;
* **`execWPRV10_of_11`**: an `ExecWPRV11` is an `ExecWPRV10` for any `FH` holding at every `NoV` start;
  **`execWPRV11_of_10`**: every `ExecWPRV10` is an `ExecWPRV11` (drop the `VSafe9` obligation);
* **`serializable_fl4_localV11`**: over U18's family with the invocation summands, `ExecWPRV11 … (¬ IoIx)
  StartV2C` ⇒ `RunAll` (through U28 at `FH := U28At` and `u28At_all`);
* **`serializable_fl4_localU28ofV11`**: U28's statement follows (so every earlier `serializable_fl4_localU*`
  statement over this family does too, through the `…of…` chain).

## Premises of `serializable_fl4_localV11` (exactly)
* the execution `h : ExecWPRV11 …`, whose steps carry: `arm` [P] (armed programs are pure glue); `start` [P] (the
  glue's start fact at `c`'s view, `StartV2C` [P] — the W11 slots' `StartU2C` records and the invocation slots'
  `StartInvU3` (`LkC`, `InvLkW →` `DelPteStart` / `InvStartU2` / `CMStartU2`, with their `DelPtePrem.lk` /
  `InvPremW.lk` [P]) — and, for a start whose armed program is the body itself, **`VSafe` [J] where `¬ IoIx`**);
  `serX` [P] / `serC` / `serG` [P] / `keep` (as U10);
* `P : LocPlat` [P], `hIoa : MRKeepIoapic` [P], `h0` (`Init`), `hA0` (`ArmInv`), `hB` (`SerExitW` [P] at the start),
  `hc0`, `hM0`, `hq` (`NoLoc`).
* **Removed vs `serializable_fl4_localU28`: `VSafe9` [J] (asked nowhere; the exempt predicate `U28At` is proved,
  `u28At_all`).** Nothing added.

No existing statement changed except the root import list.
-/
import Fl4Proofs.P2.E2EPU28
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY)
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath tr masksOf)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg NextH VEq Safe narrowSP)
open Fl4Proofs.P2.CoreView (view)

noncomputable section
open Classical

/-! ## The chain-level step without `VSafe9` -/

section exec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {ι : Type}

/-- **A step of FL4 as in U10, without `VSafe9`** (module docstring). -/
structure Fl4StepWPRV11 (LP : PathsP ι) (NoV : ι → Prop)
    (SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop)
    (P : LocPlat st arI AR MR) (s : Cfg U64 U64 U64 U64) (K : KLayoutP) (Ch : U64 → S → Prop) (c : U64)
    (s' : Cfg U64 U64 U64 U64) (K' : KLayoutP) (Ch' : U64 → S → Prop) : Prop where
  /-- [P] an armed program is pure glue. -/
  arm : ∀ p, s'.ph c = .arm p → PureGlue p
  /-- [P] the glue's start fact at `c`'s view for the body `k0`; the armed program is `k0` with `VSafe` [J] for
  paths with `NoV`, or its re-annotation (nothing asked). -/
  start : ∀ p0 k W, s.ph c = .loc p0 (.start k) W → ∀ (hK : RegionOKP K) (hU : UserOKP K),
    ∃ ρ : U64 → U64, VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem ∧
      ∃ i k0, SF (Ch c) K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k0 i ∧
        ((k = k0 ∧ (NoV i → VSafe LP s K c k0 hK hU ρ i)) ∨ k = annV s K c ρ k0)
  /-- [P] the serial exit's ghost choice, one P3 chain per core. -/
  serX : SerStep s c → ∀ e, SerExitW P K'.toKLayoutV (Ch' e)
  /-- The glue's layout convention at the serial exit. -/
  serC : SerStep s c → K'.vcpus = ∅ ∧ K'.ptes = ptesR K' s'.mem
  /-- [P] the exit ghost with rule 8. -/
  serG : SerStep s c → MapsP K' s'
  /-- Layout and chains change only at serial steps. -/
  keep : ¬ SerStep s c → K' = K ∧ Ch' = Ch

inductive ExecWPRV11 (LP : PathsP ι) (NoV : ι → Prop)
    (SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop)
    (P : LocPlat st arI AR MR) (s0 : Cfg U64 U64 U64 U64) (K0 : KLayoutP) (Ch0 : U64 → S → Prop) :
    Cfg U64 U64 U64 U64 → KLayoutP → (U64 → S → Prop) → Prop
  | refl : ExecWPRV11 LP NoV SF P s0 K0 Ch0 s0 K0 Ch0
  | step {s s' : Cfg U64 U64 U64 U64} {K K' : KLayoutP} {Ch Ch' : U64 → S → Prop} {c : U64} :
      ExecWPRV11 LP NoV SF P s0 K0 Ch0 s K Ch → Step s c s' → Fl4StepWPRV11 LP NoV SF P s K Ch c s' K' Ch' →
      ExecWPRV11 LP NoV SF P s0 K0 Ch0 s' K' Ch'
  | hw {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {Ch : U64 → S → Prop} {v a x : U64} :
      ExecWPRV11 LP NoV SF P s0 K0 Ch0 s K Ch → HwStepP K s v a x →
      ExecWPRV11 LP NoV SF P s0 K0 Ch0 (hwCfg s a x) K Ch

/-- **An `ExecWPRV11` is an `ExecWPRV10` for any exempt predicate holding at every `NoV` start.** -/
theorem execWPRV10_of_11 {LP : PathsP ι} {NoV : ι → Prop}
    {FH : KLayoutP → U64 → (U64 → Prop) → (U64 → U64) → SP → ι → Prop}
    (hFH : ∀ K c hs ρ k i, NoV i → FH K c hs ρ k i)
    {SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop}
    {P : LocPlat st arI AR MR} {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop}
    (h : ExecWPRV11 LP NoV SF P s0 K0 Ch0 s K Ch) : ExecWPRV10 LP NoV FH SF P s0 K0 Ch0 s K Ch := by
  induction h with
  | refl => exact .refl
  | step _ hS g ih =>
    refine .step ih hS ⟨g.arm, fun p0 k W hph hK hU => ?_, g.serX, g.serC, g.serG, g.keep⟩
    obtain ⟨ρ, hV, i, k0, hi, hvs⟩ := g.start p0 k W hph hK hU
    refine ⟨ρ, hV, i, k0, hi, ?_⟩
    rcases hvs with h1 | hk
    · exact Or.inl h1
    · exact Or.inr ⟨hk, fun hn hnf => absurd (hFH _ _ _ _ _ _ hn) hnf⟩
  | hw _ hH ih => exact .hw ih hH

/-- **Every `ExecWPRV10` is an `ExecWPRV11`** (its `VSafe9` obligations dropped). -/
theorem execWPRV11_of_10 {LP : PathsP ι} {NoV : ι → Prop}
    {FH : KLayoutP → U64 → (U64 → Prop) → (U64 → U64) → SP → ι → Prop}
    {SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop}
    {P : LocPlat st arI AR MR} {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop}
    (h : ExecWPRV10 LP NoV FH SF P s0 K0 Ch0 s K Ch) : ExecWPRV11 LP NoV SF P s0 K0 Ch0 s K Ch := by
  induction h with
  | refl => exact .refl
  | step _ hS g ih =>
    refine .step ih hS ⟨g.arm, fun p0 k W hph hK hU => ?_, g.serX, g.serC, g.serG, g.keep⟩
    obtain ⟨ρ, hV, i, k0, hi, hvs⟩ := g.start p0 k W hph hK hU
    refine ⟨ρ, hV, i, k0, hi, ?_⟩
    rcases hvs with h1 | ⟨hk, -⟩
    · exact Or.inl h1
    · exact Or.inr hk
  | hw _ hH ih => exact .hw ih hH

end exec

/-! ## Every non-io start is exempt -/

section all
variable {S : Type}

/-- **`U28At` holds at every non-io start** (module docstring). -/
theorem u28At_all (K : KLayoutP) (c : U64) (hs : U64 → Prop) (ρ : U64 → U64) (k0 : SP)
    (i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)) (hn : ¬ IoIx (S := S) i) :
    U28At (S := S) K c hs ρ k0 i := by
  have l24 : U24At (S := S) K c hs ρ k0 i → U28At (S := S) K c hs ρ k0 i :=
    fun h => Or.inl (Or.inl (Or.inl (Or.inl h)))
  have l16 : U16At (S := S) K c hs ρ k0 i → U24At (S := S) K c hs ρ k0 i :=
    fun h => Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h)))))))
  rcases i with ((j | j | j | j | j | j | (j | j)) | ((j | j) | j))
  · exact l24 (l16 (Or.inl (Or.inl trivial)))
  · exact l24 (l16 (Or.inl (Or.inr trivial)))
  · exact (hn trivial).elim
  · by_cases hT : ρ (fld j.target oAFFINITY) = c
    · exact l24 (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hT)))))))
    · exact l24 (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hT))))))))
  · exact l24 (u24At_irq K c hs ρ k0 j)
  · exact l24 (l16 (Or.inr trivial))
  · exact l24 (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr trivial))))))
  · exact l24 (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr trivial)))))
  · exact u28At_pte K c hs ρ k0 j
  · exact Or.inl (u27At_del K c hs ρ k0 j)
  · exact Or.inl (u27At_cm K c hs ρ k0 j)

end all

/-! ## The top without `VSafe9` -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **FL4 end to end without `VSafe9`** (module docstring), over U18's family with the invocation summands. The
conclusion is about the physical memory. -/
theorem serializable_fl4_localV11 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : ∀ e, SerExitW P K0.toKLayoutV (Ch0 e)) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPRV11 (PathsP.sum (fl4LocW11JC st ar hA (masksWr_plain st) L.total a0)
        (PathsP.sum (PathsP.sum (delPteSlot st ar hA (masksWr_plain st)) (invSlotU st ar hA (masksWr_plain st)))
          (cmSlotU st ar hA (masksWr_plain st))))
      (fun i => ¬ IoIx (S := S) i) (StartV2C st ar hA a0 arI AR MR) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_fl4_localU28 st ar hA a0 P hIoa h0 hA0 hB hc0 hM0
    (execWPRV10_of_11 (FH := U28At (S := S)) (fun K c hs ρ k i hn => u28At_all K c hs ρ k i hn) h) hq

/-- **U28's statement follows from the top without `VSafe9`** (every U28 execution is an `ExecWPRV11`). -/
theorem serializable_fl4_localU28ofV11 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : ∀ e, SerExitW P K0.toKLayoutV (Ch0 e)) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPRV10 (PathsP.sum (fl4LocW11JC st ar hA (masksWr_plain st) L.total a0)
        (PathsP.sum (PathsP.sum (delPteSlot st ar hA (masksWr_plain st)) (invSlotU st ar hA (masksWr_plain st)))
          (cmSlotU st ar hA (masksWr_plain st))))
      (fun i => ¬ IoIx (S := S) i) (U28At (S := S)) (StartV2C st ar hA a0 arI AR MR) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_fl4_localV11 st ar hA a0 P hIoa h0 hA0 hB hc0 hM0 (execWPRV11_of_10 h) hq

end top

end
end Fl4Proofs.P2.E2EP
