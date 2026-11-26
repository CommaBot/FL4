/-
# P2 (line mmuAD, gen 17): **every `ExecU3b` run is an `ExecVX4d` run** — U3d as a corollary of AD / AD2

* **`execVX4d_of_U3b`**: an `ExecU3b` execution over U1P's start facts `StartU1P` (native epochs only: every
  serial exit has `K.vcpus = ∅`, `Fl4StepWPR.serC`) is an `ExecVX4d` execution over `StartAD` (its native case
  `.inl^11`, which is `K.vcpus = ∅ ∧ StartU1P`), from `famU1P` into `famAD`, and its layout keeps `vcpus = ∅`. Its [S] `VmPweT` step is vacuous (no VM exit).
* `execVX4d_of_U3b2`: the same into `famAD2` / `StartAD2` (the `.inl` case).
* **`serializable_fl4_localU3d_ofAD`** / **`serializable_fl4_localU3d_ofAD2`**: `serializable_fl4_localU3d`'s
  statement (premises and conclusion verbatim) from `serializable_fl4_localAD` / `serializable_fl4_localAD2`.

No named premise. New module; no existing statement changes.
-/
import Fl4Proofs.P2.E2EPAD2
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll Step)

noncomputable section
open Classical

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **An `ExecU3b` run over `StartU1P` is an `ExecVX4d` run over `StartAD`**, with `vcpus = ∅` throughout. -/
theorem execVX4d_of_U3b (P : LocPlat st arI AR MR)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl7 st Cs Ω Sg Ac Locks)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} {E : U64 → U64}
    (hc0 : K0.vcpus = ∅)
    (h : ExecU3b (famU1P st ar hA a0 B) (StartU1P st ar hA a0 B (arI := arI) (AR := AR) (MR := MR)) P s0 K0 Ch0 s K Ch E) :
    ExecVX4d (famAD st ar hA a0 B) (StartAD st ar hA a0 B (arI := arI) (AR := AR) (MR := MR)) P s0 K0 Ch0 s K Ch E ∧
      K.vcpus = ∅ := by
  induction h with
  | refl => exact ⟨.refl, hc0⟩
  | @step s1 s1' K1 K1' Ch1 Ch1' c1 E1 _ hS g ih =>
    obtain ⟨hX, nv⟩ := ih
    have nv' : K1'.vcpus = ∅ := by
      by_cases hs : SerStep s1 c1
      · exact (g.serC hs).1
      · rw [(g.keep hs).1]; exact nv
    refine ⟨.step hX hS ⟨g.arm, fun p0 k W hph hK hU => ?_, fun hs => Or.inl ⟨g.serX hs, g.serC hs⟩, g.serG,
      g.keep⟩ (fun _ hne => (hne nv').elim), nv'⟩
    obtain ⟨i, hi⟩ := g.start p0 k W hph hK hU
    exact ⟨.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl i)))))))))), ⟨nv, hi⟩⟩
  | hw _ hH ih => exact ⟨.hw ih.1 hH, ih.2⟩
  | mmu _ hH ih => exact ⟨.mmu ih.1 hH, ih.2⟩

/-- **The same into `StartAD2`** (its `.inl` case). -/
theorem execVX4d_of_U3b2 (P : LocPlat st arI AR MR)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl7 st Cs Ω Sg Ac Locks)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} {E : U64 → U64}
    (hc0 : K0.vcpus = ∅)
    (h : ExecU3b (famU1P st ar hA a0 B) (StartU1P st ar hA a0 B (arI := arI) (AR := AR) (MR := MR)) P s0 K0 Ch0 s K Ch E) :
    ExecVX4d (famAD2 st ar hA a0 B) (StartAD2 st ar hA a0 B (arI := arI) (AR := AR) (MR := MR)) P s0 K0 Ch0 s K Ch E ∧
      K.vcpus = ∅ := by
  induction h with
  | refl => exact ⟨.refl, hc0⟩
  | @step s1 s1' K1 K1' Ch1 Ch1' c1 E1 _ hS g ih =>
    obtain ⟨hX, nv⟩ := ih
    have nv' : K1'.vcpus = ∅ := by
      by_cases hs : SerStep s1 c1
      · exact (g.serC hs).1
      · rw [(g.keep hs).1]; exact nv
    refine ⟨.step hX hS ⟨g.arm, fun p0 k W hph hK hU => ?_, fun hs => Or.inl ⟨g.serX hs, g.serC hs⟩, g.serG,
      g.keep⟩ (fun _ hne => (hne nv').elim), nv'⟩
    obtain ⟨i, hi⟩ := g.start p0 k W hph hK hU
    exact ⟨.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl i))))))))))), ⟨nv, hi⟩⟩
  | hw _ hH ih => exact ⟨.hw ih.1 hH, ih.2⟩
  | mmu _ hH ih => exact ⟨.mmu ih.1 hH, ih.2⟩

/-- **`serializable_fl4_localU3d` from `serializable_fl4_localAD`** (same premises, same conclusion). -/
theorem serializable_fl4_localU3d_ofAD (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl7 st Cs Ω Sg Ac Locks)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} {E : U64 → U64} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecU3b (famU1P st ar hA a0 B) (StartU1P st ar hA a0 B (arI := arI) (AR := AR) (MR := MR)) P s0 K0 Ch0
      s K Ch E)
    (hq : NoLoc s) :
    ∃ ℓ : List SP, ℓ.Perm s.log ∧ RunAll ℓ s0.mem s.mem :=
  serializable_fl4_localAD st ar hA a0 P hIoa B h0 hA0 hB hc0 hM0
    (execVX4d_of_U3b st ar hA a0 P B hc0.1 h).1 hq

/-- **`serializable_fl4_localU3d` from `serializable_fl4_localAD2`** (same premises, same conclusion). -/
theorem serializable_fl4_localU3d_ofAD2 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl7 st Cs Ω Sg Ac Locks)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} {E : U64 → U64} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecU3b (famU1P st ar hA a0 B) (StartU1P st ar hA a0 B (arI := arI) (AR := AR) (MR := MR)) P s0 K0 Ch0
      s K Ch E)
    (hq : NoLoc s) :
    ∃ ℓ : List SP, ℓ.Perm s.log ∧ RunAll ℓ s0.mem s.mem :=
  serializable_fl4_localAD2 st ar hA a0 P hIoa B h0 hA0 hB hc0 hM0
    (execVX4d_of_U3b2 st ar hA a0 P B hc0.1 h).1 hq

end top

end
end Fl4Proofs.P2.E2EP
