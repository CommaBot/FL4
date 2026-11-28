/-
# P2 (line p3mc, gen 11): U12a, U11 with vmF's `VSafe9` discharged also at every start whose action is not 0

## Action `RESUME_CURRENT` at every vmF start (the P3→P2 bridge)
P2's own entry facts (`VmPre`, `BoundInv`) allow `SCHED_ACTION ≠ 0`; P3 does not: at a reachable kernel entry
whose current thread is not idle, the spec state is `Entered` (`SInvX.entered`, schedulerAction
`resumeCurThread`), and `SchedRel.act` makes FL4's action word 0 (`JAtZ.curFacts`, P3/ScRestJ). This is the Rust
fact that `schedule()` (sched.rs) always leaves `RESUME_CURRENT` before returning to user. So no new premise is
needed: the fact is threaded from the glue's chain.
* **`chain_act0`**: a state of a P3 chain (`ChainOf`) with `NonIdle` has `L.actionW σ = 0`.
* **`vmF_act0_SF`**: at a vmF start fact `StartV2 … (.inl (.vmF j))` of a chain, the glue's start state `σc`
  (`GlueAt`'s witness, the chain state of `StartU`) is on core `c`, has the layout's kernel base, agrees with the
  view on every aligned kernel word, and has action 0.
* **`act_of_view`**: any `VmPre` start state on core `c` with the layout's kernel base whose kernel words are the
  view's has the same action word as `σc` (the action word is the aligned kernel node word
  `nodeAt ksb c SCHED_ACTION`), so action 0; `ut_act` (`update_timestamp` keeps it).
So the start shape of U11's residual case 2 (`ActStart` with the current SC another core's: action not 0) never
meets a vmF start fact: **`vmF_annV_dis12`** proves `Safe (annV k0)` at `VmDisAt12 := FHStart ∨ ActStartA ∨
NoGoStart` (`ActStartA` = `ActStart` without "the current SC homed") given the view's action fact `Act0V`.

## U12a
`execPV9_of_WPRV10S`: `execPV9_of_WPRV10` whose exempt-start obligation `hFH` may also use the step's start fact
`SF` and chain (`ChainOf`, `EpochPteN` at the view). **`serializable_fl4_localU12a`** (= `ExecWPRV10 …
(fun i => ¬IoIx i) (VmDisAt12 st ar)`), **`serializable_fl4_localU11of12a`**.

## Premises of `serializable_fl4_localU12a` vs `serializable_fl4_localU11`
* **Removed: `VSafe9` [J] at the vmF starts whose prefix action is not `RESUME_CURRENT` (current SC on any core).**
  Nothing added (the action fact is derived from P3 through `P`, `hIoa` and the chain of `serX` / `hB`).
* `VSafe9` [J] stays at the vmF starts with action `RESUME_CURRENT`, a granting endpoint cap, the endpoint
  receiving and its head homed on `c` (handoff p3mc §13 item 1, needs `vm_accN`), and at every other non-io slot,
  as in U11. Everything else unchanged.

No existing statement changed except the root import list.

Gen 56 (handoff p3mc §61) retired, with `ExecWPRV10–12` and the V15 stepping stones: `execPV9_of_WPRV10S`.
-/
import Fl4Proofs.P2.VmDecTop
import Fl4Proofs.P2.VmFhView
import Fl4Proofs.P3.ScRestJ
import Fl4Proofs.P3.JNativeScope
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld)
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath tr masksOf)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg NextH VEq Safe narrowSP
  xsafeRunH_inv)
open Fl4Proofs.P2.CoreView (view)

noncomputable section
open Classical

/-! ## Action 0 at the chain's start states -/

section view
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]

/-- **The view's action fact**: some state on core `c` with the layout's kernel base, the view's kernel words and
action 0. -/
def Act0V (K : KLayoutP) (c : U64) (ρ : U64 → U64) : Prop :=
  ∃ σc : S, L.cpu σc = c ∧ L.ksb σc = K.ksb ∧
    (∀ x, Aligned x → x ∉ K.user → L.mem σc x = view K.toKLayout c ρ x) ∧ L.actionW σc = 0#u64

variable {st}
variable {A : Type} (ar : machine.Arch A)

/-- **A `VmPre` start state at the view has the view's action word** (module docstring). -/
theorem act_of_view {K : KLayoutP} {c : U64} {ρ : U64 → U64} {T Cs Ω : Set U64} {H : Heap}
    {Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {σ : S}
    (B : VmBase st (userV K.toKLayoutV) T Cs Ω H Sg Rp Scs Nt Z Ac σ) (hk : L.ksb σ = K.ksb) (hc : L.cpu σ = c)
    (hm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x) (h0 : Act0V st K c ρ) :
    L.actionW σ = 0#u64 := by
  obtain ⟨σc, hcc, hkc, hmc, ha0⟩ := h0
  have hn := (B.nd (Locks := fun _ _ => True) layout.node.SCHED_ACTION (by simp [layout.node.SCHED_ACTION])
    (by simp [layout.node.SCHED_ACTION])).1
  have ha : Aligned (L.nodeAt σ (L.cpu σ) layout.node.SCHED_ACTION) := hn.1
  have hu : L.nodeAt σ (L.cpu σ) layout.node.SCHED_ACTION ∉ K.user := fun h => hn.2.1 (mem_userV.2 (Or.inl h))
  have ea : L.nodeAt σ (L.cpu σ) layout.node.SCHED_ACTION = L.nodeAt σc (L.cpu σc) layout.node.SCHED_ACTION := by
    rw [hc, hcc]; exact nodeAt_of_ksb (hk.trans hkc.symm) c _
  have ha' : Aligned (L.nodeAt σc (L.cpu σc) layout.node.SCHED_ACTION) := by rw [← ea]; exact ha
  have hu' : L.nodeAt σc (L.cpu σc) layout.node.SCHED_ACTION ∉ K.user := by rw [← ea]; exact hu
  unfold LawfulStore.actionW at ha0 ⊢
  rw [hm _ ha hu, ea, ← hmc _ ha' hu']
  exact ha0

end view

section act
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **Action `RESUME_CURRENT` at a non-idle chain state** (module docstring): P3's `JAtZ` / `SInvX` at the chain
state's `JReachU17`, `SInvX.entered`, `JAtZ.curFacts`. -/
theorem chain_act0 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR) {σe : S}
    {K : OwnMap.KLayout} {Ch : S → Prop} (hC : ChainOf (L := L) arI AR MR σe K Ch) {σ : S} (hσ : Ch σ)
    (hct : NonIdle st arI AR MR σ) : L.actionW σ = 0#u64 := by
  obtain ⟨Z, H, Cx, nc, -, -, hCh, -, -⟩ := hC
  subst hCh
  obtain ⟨a, τ, hR⟩ := hσ
  have hJ := hR.reach
  obtain ⟨Z', H', Cs, Ac, Lst, D, J, hX, -⟩ := Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU29 arI AR MR P.ari
    P.tot P.nd P.mach P.kd P.io hIoa P.pa P.ia P.t P.max P.tu P.ref P.pi P.sx P.dr hJ
  exact (J.curFacts (hX.entered (hct a τ hJ)) (cur_thread_ok σ)).2.2.2

variable (arI AR MR) in
/-- **What `chain_act0` gives, as a platform fact** (gen 54 re-base): at every state of a P3 chain with `NonIdle`,
the action word is `RESUME_CURRENT`. -/
def ChainAct0 : Prop :=
  ∀ {σe : S} {K : OwnMap.KLayout} {Ch : S → Prop}, ChainOf (L := L) arI AR MR σe K Ch → ∀ {σ : S}, Ch σ →
    NonIdle st arI AR MR σ → L.actionW σ = 0#u64

/-- **The base platform gives `ChainAct0`** (`chain_act0`). -/
theorem chainAct0_of (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR) :
    ChainAct0 st arI AR MR :=
  fun {_ _ _} hC {_} hσ hct => chain_act0 st P hIoa hC hσ hct

variable (arI AR MR) in
/-- **The re-based platform of the V15 trunk** (gen 54, handoff §59): `LocPlatC` (one domain, a P3 chain at every
`JReachU17` exit) and the two P3 facts the slot obligations read at chain states, `ChainRun` (`chain_run`) and
`ChainAct0` (`chain_act0`). These three are everything the trunk reads off `P : LocPlat` and `hIoa`
(constant-level cone of `serializable_fl4_V15_pmKADZ`: the only readers of `LocPlat`'s fields are
`chainOf_exists`, `chain_run`, `chain_act0`). -/
structure LocPlatCR : Prop where
  toC : LocPlatC st arI AR MR
  run : ChainRun st arI AR MR
  act0 : ChainAct0 st arI AR MR

variable {st} in
/-- **The base platform with `hIoa` gives `LocPlatCR`.** -/
theorem locPlatCR_of (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR) :
    LocPlatCR st arI AR MR :=
  ⟨P.toC, chainRun_of P hIoa, chainAct0_of st P hIoa⟩

/-- **`vmF_act0_SF` on the re-based platform** (gen 54, in place: `P : LocPlatCR` for `P : LocPlat` / `hIoa`). -/
theorem vmF_act0_SF_C (P : LocPlatCR st arI AR MR) {Ch : S → Prop}
    {K : KLayoutP} (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (nv : K.vcpus = ∅)
    {ρ : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {hs : U64 → Prop} {q : SP} {j : VmFArg S}
    (h : StartV2 st ar hA a0 arI AR MR Ch K (view K.toKLayout c ρ) hK hU c hs q (.inl (.vmF j))) :
    Act0V st K c ρ := by
  have h' : StartU2 st ar hA a0 arI AR MR Ch K (view K.toKLayout c ρ) hK hU c hs q (.vmF j) := h
  have hSU := startU_of_U2 st ar hA a0 hC nv h'
  obtain ⟨q0, ⟨hB, σ, ⟨hCσ, hE⟩, hG⟩, -⟩ := hSU
  obtain ⟨σe, hC'⟩ := hC
  have hpa : VmFPremA st ar j K.toKLayoutV :=
    hB.toA hA ((hE.toJ12 st ar).toJ10 st ar hA (P.run hC' hCσ hE.hct))
  obtain ⟨σ', a', e', hc, -, hμ, -⟩ := hG hpa
  subst e'
  exact ⟨_, hc, slJAt_ksb (ChainOf.bun hC' _ hCσ), fun x hx hu => hμ x hx hu,
    P.act0 hC' hCσ hE.hct⟩

end act

/-! ## The discharged starts of U12a -/

section dis
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)

end dis

/-! ## The chain-level converter with the start fact in the exempt obligation -/

section exec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {ι : Type}

end exec

/-! ## U12a -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

end top

end
end Fl4Proofs.P2.E2EP
