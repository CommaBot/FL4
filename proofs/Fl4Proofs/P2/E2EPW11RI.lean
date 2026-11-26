/-
# P2 (line pte, gen 9): the invocation-index family over W11 with the reachability convention

The family the local invocation slots (PageMap: line pte; Delete with a PTE: line invj) are added to:
**`PathsP.sum (fl4LocW11J …) LQ`** for any family `LQ : PathsP κ` of `ownP` paths (the invocation slots, indexed by
`κ`), with start facts **`StartW11RI … SFQ`**: W11's `StartP3W11JC` on the eight existing slots, an arbitrary start
relation `SFQ` on the new ones. The glue is `ExecWPR` (P2/E2EPW11R.lean: the PTE set by the reachability convention
`ptesR` at every serial exit and at boot).

* **`execP_of_WPRI`**: an `ExecWPR` over this family is an `ExecP`, provided `SFQ` gives `StartAt` of its slot
  (`hSFQ`); `hSFQ` is given the current chain (`ChainOf`) and the **epoch data**: an epoch start `s1` with
  `K.ptes = ptesR K s1.mem`, no VCPU, and the current memory equal to `s1`'s on the `GateW` words — what
  `ptesR_at_run` (P2/E2EPRStart.lean) needs for `PtePlanLocked`'s [J] half (`gateAg_at`'s ingredients).
* **`serializable_fl4_localW11PRI`**: every such execution, at a state with no local path in progress, ran as some
  serial order of its completed entries.

Premises: `serializable_fl4_localW11PR`'s, plus `hSFQ` for the new slots (each slot's own start obligation).
No new premise for the existing slots; no existing statement or file changed.
-/
import Fl4Proofs.P2.E2EPW11R
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld)
open Fl4Proofs.P2.E2E (StartAt SP SerStep)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg xsafeRun_greach allowed_of_sinv)

noncomputable section
open Classical

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop) (MR : A3 → Fl4Spec.MachineState → Prop)

/-- **The start facts of the invocation-index family**: W11's on the existing slots, `SFQ` on the new ones. -/
def StartW11RI {κ : Type}
    (SFQ : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → κ → Prop)
    (Ch : S → Prop) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (q : SP) : Fl4IxW (S := S) ⊕ κ → Prop
  | .inl i => StartP3W11JC st ar hA hm hSt a0 arI AR MR Ch K m hK hU c hs q i
  | .inr j => SFQ Ch K m hK hU c hs q j

variable {arI AR MR}

/-- **An `ExecWPR` over the invocation-index family is an `ExecP`, with the epoch invariant.** -/
theorem execP_of_WPRI (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR) {κ : Type} (LQ : PathsP κ)
    {SFQ : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → κ → Prop}
    (hSFQ : ∀ Ch K m hK hU c hs q j, (∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) →
      (∃ s1 : Cfg U64 U64 U64 U64, (K.vcpus = ∅ ∧ K.ptes = ptesR K s1.mem) ∧ ∀ x, GateW K x → m x = s1.mem x) →
      SFQ Ch K m hK hU c hs q j → StartAt (LQ j K m hK hU) c hs m q)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} (h0 : Init s0) (hA0 : ArmInv s0)
    (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPR (PathsP.sum (fl4LocW11J st ar hA hm hSt a0) LQ) (StartW11RI st ar hA hm hSt a0 arI AR MR SFQ) P s0 K0 Ch0 s K Ch) :
    ExecP (PathsP.sum (fl4LocW11J st ar hA hm hSt a0) LQ) s0 K0 s K ∧ SerExitW P K.toKLayoutV Ch ∧
      ∃ s1 : Cfg U64 U64 U64 U64, (K.vcpus = ∅ ∧ K.ptes = ptesR K s1.mem) ∧ ∀ x, GateW K x → s.mem x = s1.mem x := by
  obtain ⟨hK0, hU0⟩ := okP_R hB hc0
  induction h with
  | refl => exact ⟨.refl, hB, s0, hc0, fun _ _ => rfl⟩
  | @step s1 s1' K1 K1' Ch1 Ch1' c1 _ hS g ih =>
    obtain ⟨hE, hX, e1, hCe, hk1⟩ := ih
    have hst : Fl4StepP (PathsP.sum (fl4LocW11J st ar hA hm hSt a0) LQ) s1 K1 c1 s1' K1' := by
      refine ⟨g.arm, fun p0 k W hph hK hU => ?_, fun hs => ?_, fun hn => (g.keep hn).1⟩
      · obtain ⟨i, hi⟩ := g.start p0 k W hph hK hU
        cases i with
        | inr j => exact ⟨.inr j, hSFQ _ _ _ _ _ _ _ _ j hX.chainOf ⟨e1, hCe, hk1⟩ hi⟩
        | inl i =>
          obtain ⟨q0, hW, rfl⟩ := hi
          obtain ⟨σ, a, hP, hc, hl, hμ, e⟩ := startAt_P3W11 st ar hA hm hSt a0 P hIoa hX.chainOf hW
          have hk := pre_ksbW6 st ar hA hm hSt a0 i K1 s1.mem hK hU σ hP
          obtain ⟨σe, hC, hσ⟩ := hX.lay
          have hq := qPs_of_convR
            (L' := ((fl4LocP3W6 st ar hA hm hSt a0).paths (fl4Dflt st ar hm) i K1.toKLayoutV s1.mem hK.base hU.base).L)
            hCe.2 hCe.1 ⟨σe, hC.bun σe hσ⟩ hk1 hk (fun x hx hu => hμ x hx hu)
          exact ⟨.inl i, σ, a, ⟨hP, hq⟩, hc, hl, hμ,
            startQPB_of st ar hA hm hSt a0 i K1 s1.mem hK hU c1 _ q0 σ a hP hc hl hμ e⟩
      · have hP := okP_R (g.serX hs) (g.serC hs)
        exact ⟨hP.1, hP.2, g.serG hs⟩
    refine ⟨.step hE hS hst, ?_, ?_⟩
    · by_cases hs : SerStep s1 c1
      · exact g.serX hs
      · obtain ⟨e1, e2⟩ := g.keep hs
        rw [e1, e2]; exact hX
    · by_cases hs : SerStep s1 c1
      · exact ⟨s1', g.serC hs, fun _ _ => rfl⟩
      · obtain ⟨eK, -⟩ := g.keep hs
        subst eK
        obtain ⟨hr, -, -, hM⟩ := exec_safeRunP h0 hA0 hK0 hU0 hM0 hE
        obtain ⟨-, hSI, -⟩ := xsafeRun_greach h0 hA0 hr
        refine ⟨e1, hCe, fun x hx => ?_⟩
        rw [← hk1 x hx]
        exact step_gate_keep hM (allowed_of_sinv hSI c1) hS hs hx
  | @hw s1 K1 Ch1 v a y _ hH ih =>
    obtain ⟨hE, hX, e1, hCe, hk1⟩ := ih
    obtain ⟨-, hK, -, hM⟩ := exec_safeRunP h0 hA0 hK0 hU0 hM0 hE
    refine ⟨.hw hE hH, hX, e1, hCe, fun x hx => ?_⟩
    rw [← hk1 x hx]
    exact hw_gate_keep hK hM hH hx

/-- **FL4 end to end over the invocation-index family, W11's glue with the reachability convention** (module
docstring). -/
theorem serializable_fl4_localW11PRI (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {κ : Type} (LQ : PathsP κ)
    {SFQ : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → κ → Prop}
    (hSFQ : ∀ Ch K m hK hU c hs q j, (∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) →
      (∃ s1 : Cfg U64 U64 U64 U64, (K.vcpus = ∅ ∧ K.ptes = ptesR K s1.mem) ∧ ∀ x, GateW K x → m x = s1.mem x) →
      SFQ Ch K m hK hU c hs q j → StartAt (LQ j K m hK hU) c hs m q)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} (h0 : Init s0) (hA0 : ArmInv s0)
    (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPR (PathsP.sum (fl4LocW11J st ar hA hm hSt a0) LQ) (StartW11RI st ar hA hm hSt a0 arI AR MR SFQ) P
      s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  obtain ⟨hK0, hU0⟩ := okP_R hB hc0
  exact serializable_e2eP _ h0 hA0 hK0 hU0 hM0
    (execP_of_WPRI st ar hA hm hSt a0 P hIoa LQ hSFQ h0 hA0 hB hc0 hM0 h).1 hq

end top

end
end Fl4Proofs.P2.E2EP
