/-
# P2 (line p3mc, gen 29): FL4 end to end without a read premise, the glue arming the re-annotated body

After V11 (P2/E2EPV11) the only read premise left is **`VSafe` [J]**: at a non-io start whose armed program is the
**unannotated** body `k0` (the first arm of `start`), that body is `Safe` at the physical memory where the view
differs from `ρ`. That premise is **false** at some reachable starts (handoff §9, P2/ViewSafeObstr `view_home_rd_unsafe`:
the view lets `c` read a foreign thread's home-owned word, which `k0` then reads with `rd`; e.g. vmF's
`dest.reply_obj` before any `AFFINITY` check), so it cannot be discharged for every start. It is consumed only when
the glue arms `k0` itself; the re-annotated body `annV k0` is `Safe` at every non-io start (U28, `u28At_all`). The
annotation is ghost (the `StartAt` docstring), so the glue may always arm `annV k0`:

* `Fl4StepWPRV12` / `ExecWPRV12`: V11's step whose `start` field arms the unannotated body only at io starts
  (`k = k0 ∧ ¬ NoV i`) and otherwise the re-annotated one (`k = annV k0`) — **[P]**, part of `start` [P]: the glue
  arms `annV k0` at every non-io start (satisfiable wherever V11's start is: V11 already allows `annV k0`; it is a
  choice of ghost annotation, not a fact about the kernel);
* **`execWPRV11_of_12`**: an `ExecWPRV12` is an `ExecWPRV11` (its `VSafe` obligations are vacuous);
* **`serializable_fl4_localV12`**: over U18's family with the invocation summands, `ExecWPRV12 … (¬ IoIx) StartV2C`
  ⇒ `RunAll`.

## Premises of `serializable_fl4_localV12` vs `serializable_fl4_localV11`
* **Removed: `VSafe` [J]** (no read premise is asked at any start).
* **Narrowed: `start` [P]** — at a non-io start the armed program is the re-annotated body `annV k0` (V11 also
  allowed the unannotated `k0` with `VSafe`). Nothing else changed: `arm` [P], `StartV2C` [P] (its vmF / vmR / sl
  entry records still carry `yb` [J], unchanged since U1), `serX` [P] / `serC` / `serG` [P] / `keep`, `P` [P],
  `hIoa` [P], `h0`, `hA0`, `hB` [P], `hc0`, `hM0`, `hq`.

No existing statement changed except the root import list.
-/
import Fl4Proofs.P2.E2EPV11
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath tr masksOf)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg NextH VEq Safe narrowSP)

noncomputable section
open Classical

section exec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {ι : Type}

/-- **A step of FL4 as in V11, the glue arming the re-annotated body at every `NoV` start** (module docstring). -/
structure Fl4StepWPRV12 (LP : PathsP ι) (NoV : ι → Prop)
    (SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop)
    (P : LocPlat st arI AR MR) (s : Cfg U64 U64 U64 U64) (K : KLayoutP) (Ch : U64 → S → Prop) (c : U64)
    (s' : Cfg U64 U64 U64 U64) (K' : KLayoutP) (Ch' : U64 → S → Prop) : Prop where
  /-- [P] an armed program is pure glue. -/
  arm : ∀ p, s'.ph c = .arm p → PureGlue p
  /-- [P] the glue's start fact at `c`'s view for the body `k0`; the armed program is `k0` only for paths without
  `NoV`, and otherwise its re-annotation `annV k0`. -/
  start : ∀ p0 k W, s.ph c = .loc p0 (.start k) W → ∀ (hK : RegionOKP K) (hU : UserOKP K),
    ∃ ρ : U64 → U64, VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem ∧
      ∃ i k0, SF (Ch c) K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k0 i ∧
        ((k = k0 ∧ ¬ NoV i) ∨ k = annV s K c ρ k0)
  /-- [P] the serial exit's ghost choice, one P3 chain per core. -/
  serX : SerStep s c → ∀ e, SerExitW P K'.toKLayoutV (Ch' e)
  /-- The glue's layout convention at the serial exit. -/
  serC : SerStep s c → K'.vcpus = ∅ ∧ K'.ptes = ptesR K' s'.mem
  /-- [P] the exit ghost with rule 8. -/
  serG : SerStep s c → MapsP K' s'
  /-- Layout and chains change only at serial steps. -/
  keep : ¬ SerStep s c → K' = K ∧ Ch' = Ch

inductive ExecWPRV12 (LP : PathsP ι) (NoV : ι → Prop)
    (SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop)
    (P : LocPlat st arI AR MR) (s0 : Cfg U64 U64 U64 U64) (K0 : KLayoutP) (Ch0 : U64 → S → Prop) :
    Cfg U64 U64 U64 U64 → KLayoutP → (U64 → S → Prop) → Prop
  | refl : ExecWPRV12 LP NoV SF P s0 K0 Ch0 s0 K0 Ch0
  | step {s s' : Cfg U64 U64 U64 U64} {K K' : KLayoutP} {Ch Ch' : U64 → S → Prop} {c : U64} :
      ExecWPRV12 LP NoV SF P s0 K0 Ch0 s K Ch → Step s c s' → Fl4StepWPRV12 LP NoV SF P s K Ch c s' K' Ch' →
      ExecWPRV12 LP NoV SF P s0 K0 Ch0 s' K' Ch'
  | hw {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {Ch : U64 → S → Prop} {v a x : U64} :
      ExecWPRV12 LP NoV SF P s0 K0 Ch0 s K Ch → HwStepP K s v a x →
      ExecWPRV12 LP NoV SF P s0 K0 Ch0 (hwCfg s a x) K Ch

/-- **An `ExecWPRV12` is an `ExecWPRV11`** (`VSafe` is asked only at `NoV` starts arming `k0`: none). -/
theorem execWPRV11_of_12 {LP : PathsP ι} {NoV : ι → Prop}
    {SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop}
    {P : LocPlat st arI AR MR} {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop}
    (h : ExecWPRV12 LP NoV SF P s0 K0 Ch0 s K Ch) : ExecWPRV11 LP NoV SF P s0 K0 Ch0 s K Ch := by
  induction h with
  | refl => exact .refl
  | step _ hS g ih =>
    refine .step ih hS ⟨g.arm, fun p0 k W hph hK hU => ?_, g.serX, g.serC, g.serG, g.keep⟩
    obtain ⟨ρ, hV, i, k0, hi, hvs⟩ := g.start p0 k W hph hK hU
    refine ⟨ρ, hV, i, k0, hi, ?_⟩
    rcases hvs with ⟨hk, hn⟩ | hk
    · exact Or.inl ⟨hk, fun h' => absurd h' hn⟩
    · exact Or.inr hk
  | hw _ hH ih => exact .hw ih hH

end exec

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **FL4 end to end without a read premise** (module docstring), over U18's family with the invocation summands,
the glue arming the re-annotated body at every non-io start. The conclusion is about the physical memory. -/
theorem serializable_fl4_localV12 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : ∀ e, SerExitW P K0.toKLayoutV (Ch0 e)) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPRV12 (PathsP.sum (fl4LocW11JC st ar hA (masksWr_plain st) L.total a0)
        (PathsP.sum (PathsP.sum (delPteSlot st ar hA (masksWr_plain st)) (invSlotU st ar hA (masksWr_plain st)))
          (cmSlotU st ar hA (masksWr_plain st))))
      (fun i => ¬ IoIx (S := S) i) (StartV2C st ar hA a0 arI AR MR) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_fl4_localV11 st ar hA a0 P hIoa h0 hA0 hB hc0 hM0 (execWPRV11_of_12 h) hq

end top

end
end Fl4Proofs.P2.E2EP
