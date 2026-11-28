/-
# P2 (line p3mc, gen 48): the start obligation asked only at layouts without a VCPU, narrowed to the starts still
open; the new A/D top

`InsV15` / `InsV15N` / `InsV15NO` [J] (P2/E2EPV15AD, P2/InsV15N, P2/InsV15O) quantify over every layout `K`, also one
with a VCPU. At such a layout the sl, vmF and vmR start facts (`StartV13`'s W11 clauses) say nothing about the armed
program: the glue's `GlueAt` is asked only under the slot's `Prem`, whose first conjunct is `K.vcpus = ∅`, and
`startAt_slB` / `startU_of_U2` / `startAt_UN` need `EpochPteN` of the view, i.e. no VCPU. So there the obligation is
about an arbitrary cut program and no discharge can reach it (finding, gen 48; not proved false: a witness would need
a chain with a VCPU in the layout). `execV15_aRunD` uses the obligation only at the current layout, which has none
(`execV15_aRunDV`, P2/E2EPV15AD, split in place this generation).

* `InsV15NOV cfg Op` [J]: `InsV15NO cfg Op` with the hypothesis `K.vcpus = ∅`; **`insV15NOV_of_NO`** (any `Op`).
* `Open48V s K c ρ k0 i`: `Open48` (P2/InsV15O48) without the homed sl starts (`SlHPm`) and the vmR starts whose reply
  names no thread homed elsewhere (`VmRHPm`, P2/InsV15SlR).
* **`insV15V_of_NOV`**: for `ExecCfg.nativePmKAD B`, from `P`, `hIoa` and `InsV15NOV … Open48V`, the obligation
  `InsV15V` (`insAP_vx_view`, `insAP_vt_view`, `insAP_stF_view`, `insAP_stH_view`, `insAP_slH_view`,
  `insAP_vmRH_view` at the closed starts).
* **`serializable_fl4_V15_pmKADW`**: gen 48's `serializable_fl4_V15_pmKADH` with `InsV15NOV … Open48V` [J] for
  `InsV15NO … Open48` [J] (through `serializable_fl4_V15_adV`); **`serializable_fl4_V15_pmKADHofW`**: the old statement
  follows (`insV15NOV_of_NO` and `Open48V ⊆ Open48`). The converse premise implication does not hold in general: the
  new premise is strictly weaker (it says nothing at layouts with a VCPU).

Named premises: `InsV15NOV … Open48V` [J] (replaces `InsV15NO … Open48` [J] on the new top; justification as `InsV15`
[J], P2/E2EPV15AD). New module; no existing statement changed.

Gen 56 (handoff p3mc §61) retired, with `ExecWPRV10–12` and the V15 stepping stones: `insV15NOV48_of_NO48`,
`serializable_fl4_V15_pmKADW`, `serializable_fl4_V15_pmKADHofW`.
-/
import Fl4Proofs.P2.InsV15SlR
import Fl4Proofs.P2.InsV15O48
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.E2E (StartAt SP)
open Fl4Proofs.P2.Serial (Cfg Init ArmInv NoLoc RunAll VEq InsAP)
open Fl4Proofs.P2.MmuAD (MmuAD ADEq NotPresent)

noncomputable section
open Classical

section opn
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

variable (arI AR MR) in
/-- **[J] `InsV15NO` at layouts without a VCPU** (module docstring; justification as `InsV15` [J]). -/
def InsV15NOV {ι : Type} (cfg : ExecCfg S ι)
    (Op : Cfg U64 U64 U64 U64 → KLayoutP → U64 → (U64 → U64) → SP → ι → Prop) : Prop :=
  ∀ (Ch : S → Prop) (s : Cfg U64 U64 U64 U64) (K : KLayoutP) (E : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (c : U64) (k0 : SP) (ρ : U64 → U64) (i : ι), K.vcpus = ∅ → Op s K c ρ k0 i →
    (∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) → EpochJV K E s → MapsP K s →
    VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem →
    cfg.SF Ch K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k0 i →
    InsAP (PWE K E) ADEq NotPresent s.own s.cls s.ko c (fun l => s.lk l = some c) ∅ s.mem
      (if cfg.NoV i then annV s K c ρ k0 else k0)

/-- **`InsV15NO` gives `InsV15NOV`** at any `Op`. -/
theorem insV15NOV_of_NO {ι : Type} {cfg : ExecCfg S ι}
    {Op : Cfg U64 U64 U64 U64 → KLayoutP → U64 → (U64 → U64) → SP → ι → Prop}
    (h : InsV15NO (L := L) arI AR MR cfg Op) : InsV15NOV (L := L) arI AR MR cfg Op :=
  fun Ch s K E hK hU c k0 ρ i _ => h Ch s K E hK hU c k0 ρ i

end opn

section pm
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}

/-- **The view starts at which the obligation is still asked after gen 48, at layouts without a VCPU** (module
docstring). -/
def Open48V (s : Cfg U64 U64 U64 U64) (K : KLayoutP) (c : U64) (ρ : U64 → U64) (k0 : SP) (i : IxV13Pm S) :
    Prop :=
  Open48 s K c ρ k0 i ∧ ¬ SlHPm st K c ρ i ∧ ¬ VmRHPm (S := S) K c ρ i

set_option maxHeartbeats 4000000 in
/-- **`insV15V_of_NOV` on the re-based platform** (gen 54, in place: `P : LocPlatCR` for `P : LocPlat` / `hIoa`). -/
theorem insV15V_of_NOV_C (P : LocPlatCR st arI AR MR)
    (B : PmObl7 st Cs Ω Sg Ac Locks)
    (h : InsV15NOV (L := L) arI AR MR (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B) (Open48V st)) :
    InsV15V (L := L) arI AR MR (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B) := by
  intro Ch s K E hK hU c k k0 ρ i nv hC J hM hVq hi hk
  have h1 : InsAP (PWE K E) ADEq NotPresent s.own s.cls s.ko c (fun l => s.lk l = some c) ∅ s.mem
      (if (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).NoV i then annV s K c ρ k0 else k0) := by
    by_cases hx : VxPm (S := S) i
    · exact insAP_vx_view st ar hA a0 B E hx hC hM hVq hi
    by_cases ht : VtPm (S := S) i
    · exact insAP_vt_view st ar hA a0 B E ht hC J hM hVq hi
    by_cases hy : StFPm (S := S) c ρ i
    · exact insAP_stF_view st ar hA a0 B E hy hC J hM hVq hi
    by_cases hh : StHPm (S := S) c ρ i
    · exact insAP_stH_view st ar hA a0 B E hh hC J hM hVq hi
    by_cases hl : SlHPm st K c ρ i
    · exact insAP_slH_view_C st ar hA a0 P B E nv hl hC J hM hVq hi
    by_cases hr : VmRHPm (S := S) K c ρ i
    · exact insAP_vmRH_view_C st ar hA a0 P B E nv hr hC J hM hVq hi
    exact h Ch s K E hK hU c k0 ρ i nv ⟨⟨⟨hx, ht, hy⟩, hh⟩, hl, hr⟩ hC J hM hVq hi
  by_cases hn : (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).NoV i
  · rw [if_pos hn] at h1
    rcases hk with ⟨-, hn'⟩ | rfl
    · exact absurd hn hn'
    · exact h1
  · rw [if_neg hn] at h1
    rcases hk with ⟨rfl, -⟩ | rfl
    · exact h1
    · exact insAP_annV h1

set_option maxHeartbeats 4000000 in
/-- **`InsV15NOV … Open48V` gives `InsV15V`** for `nativePmKAD B` (module docstring). -/
theorem insV15V_of_NOV (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    (B : PmObl7 st Cs Ω Sg Ac Locks)
    (h : InsV15NOV (L := L) arI AR MR (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B) (Open48V st)) :
    InsV15V (L := L) arI AR MR (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B) :=
  insV15V_of_NOV_C st ar hA a0 (locPlatCR_of P hIoa) B h

/-- **`serializable_fl4_V15_pmKADW` on the re-based platform**
(gen 54, in place: `P : LocPlatCR` for `P : LocPlat` / `hIoa`). -/
theorem serializable_fl4_V15_pmKADW_C (P : LocPlatCR st arI AR MR)
    (B : PmObl7 st Cs Ω Sg Ac Locks)
    (hI : InsV15NOV (L := L) arI AR MR (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B) (Open48V st))
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} {E : U64 → U64} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : ∀ e, SerExitC P.toC K0.toKLayoutV (Ch0 e))
    (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0) (h : ExecV15C (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B) P.toC s0 K0 Ch0 s K Ch E)
    (hq : NoLoc s) :
    ∃ ℓ : List SP, ℓ.Perm s.log ∧ RunAll ℓ s0.mem s.mem :=
  serializable_fl4_V15_adV_C (slotOblV13PmKAD_C st ar hA a0 P B) (insV15V_of_NOV_C st ar hA a0 P B hI)
    (fun _ _ _ _ _ h => h) (fun _ _ h => h) P.toC h0 hA0 hB hc0 hM0 h hq

end pm

end
end Fl4Proofs.P2.E2EP
