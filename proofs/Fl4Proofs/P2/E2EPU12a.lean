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
-/
import Fl4Proofs.P2.E2EPU11
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

/-- **`update_timestamp` keeps the action word.** -/
theorem ut_act (hA : P0.ArchTotal ar) {T : Set U64} {σ s1 : S} {a a1 : A} (hN : NodePlaced st T σ (L.cpu σ))
    (eu : sched.update_timestamp st ar σ a = ok (s1, a1)) : L.actionW s1 = L.actionW σ := by
  obtain ⟨⟨n, a2⟩, hn, -⟩ := spec_ex_fd (hA.now a)
  rw [update_timestamp_ok ar hN hn] at eu
  have eS := (Prod.mk.inj (ok_inj_ff eu)).1
  subst eS
  unfold LawfulStore.actionW
  rw [ut_nodeAt]
  exact ut_node hN n (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
    (by simp [layout.node.SCHED_ACTION, layout.node.CUR_TIME])
    (by simp [layout.node.SCHED_ACTION, layout.node.CONSUMED])

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

/-- **The vmF start fact of a chain gives the view's action fact** (module docstring): the glue's witness is the
chain state of `StartU`. -/
theorem vmF_act0_SF (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR) {Ch : S → Prop}
    {K : KLayoutP} (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (nv : K.vcpus = ∅)
    {ρ : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {hs : U64 → Prop} {q : SP} {j : VmFArg S}
    (h : StartV2 st ar hA a0 arI AR MR Ch K (view K.toKLayout c ρ) hK hU c hs q (.inl (.vmF j))) :
    Act0V st K c ρ := by
  have h' : StartU2 st ar hA a0 arI AR MR Ch K (view K.toKLayout c ρ) hK hU c hs q (.vmF j) := h
  have hSU := startU_of_U2 st ar hA a0 hC nv h'
  obtain ⟨q0, ⟨hB, σ, ⟨hCσ, hE⟩, hG⟩, -⟩ := hSU
  obtain ⟨σe, hC'⟩ := hC
  have hpa : VmFPremA st ar j K.toKLayoutV :=
    hB.toA hA ((hE.toJ12 st ar).toJ10 st ar hA (chain_run P hIoa hC' hCσ hE.hct))
  obtain ⟨σ', a', e', hc, -, hμ, -⟩ := hG hpa
  subst e'
  exact ⟨_, hc, slJAt_ksb (ChainOf.bun hC' _ hCσ), fun x hx hu => hμ x hx hu,
    chain_act0 st P hIoa hC' hCσ hE.hct⟩

end act

/-! ## The discharged starts of U12a -/

section dis
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)

/-- **A vmF start at `c`'s view whose prefix action is not `RESUME_CURRENT`**, the current SC on any core
(`ActStart` without its last clause). -/
def ActStartA (K : KLayoutP) (c : U64) (hs : U64 → Prop) (ρ : U64 → U64) (j : VmFArg S) (k0 : SP) : Prop :=
  ∃ (σ : S) (a : A), VmFPremA st ar j K.toKLayoutV ∧
    VmPre st ar (userV K.toKLayoutV) j.T j.Cs j.Ω j.U j.H j.Sg j.Rp j.Scs j.Nt j.Z j.Ac j.Locks σ ∧
    QPs K st σ ∧ L.cpu σ = c ∧ j.Locks σ = hs ∧
    (∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x) ∧
    (∃ (s1 : S) (a1 : A), sched.update_timestamp st ar σ a = ok (s1, a1) ∧ L.actionW s1 ≠ 0#u64) ∧
    k0 = tr (rsE (· ∈ K.ptes) (IoRS (st := st) (userV K.toKLayoutV) j.Locks) σ) (· ∈ K.user)
      (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ) (masksOf st σ) ar
      (R.syscall.handle_vm_fault_local j.addr j.code) ∅ a

/-- The discharged vmF starts of U12a, `False` at the other indices. -/
def VmDisAt12 (K : KLayoutP) (c : U64) (hs : U64 → Prop) (ρ : U64 → U64) (k0 : SP) :
    (Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)) → Prop
  | .inl (.vmF j) => FHStart st ar K c hs ρ j k0 ∨ ActStartA st ar K c hs ρ j k0 ∨ NoGoStart st ar K c hs ρ j k0
  | _ => False

theorem dis_dis12 {K : KLayoutP} {c : U64} {hs : U64 → Prop} {ρ : U64 → U64} {k0 : SP}
    {i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)} (h : VmDisAt st ar K c hs ρ k0 i) :
    VmDisAt12 st ar K c hs ρ k0 i := by
  rcases i with ((j | j | j | j | j | j | j) | j)
  · rcases h with h | ⟨σ, a, hpr, hP, hq, hc, hl, hmm, -, hu, e⟩ | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨σ, a, hpr, hP, hq, hc, hl, hmm, hu, e⟩)
    · exact Or.inr (Or.inr h)
  all_goals exact h

/-- **U9's re-annotated body is `Safe` at a discharged start of U12a**, given the view's action fact. At an
`ActStartA` start whose current SC is another core's the action fact contradicts the start (`act_of_view`). -/
theorem vmF_annV_dis12 (hA : P0.ArchTotal ar) (hmk : E2E.MasksWr st) {s : Cfg U64 U64 U64 U64} {K : KLayoutP}
    (hK : RegionOKP K) (hU : UserOKP K) {c : U64} {k0 : SP} {ρ : U64 → U64}
    {i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)} (hM : MapsP K s)
    (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem) (h0 : Act0V st K c ρ)
    (hf : VmDisAt12 st ar K c (fun l => s.lk l = some c) ρ k0 i) :
    Safe s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem (annV s K c ρ k0) := by
  rcases i with ((j | j | j | j | j | j | j) | j)
  · rcases hf with hf | hf | hf
    · exact vmF_annV_dis st ar hA hmk hK hU (i := .inl (.vmF j)) hM hV (Or.inl hf)
    · obtain ⟨σ, a, hpr, hP, hq, hc, hl, hmm, ⟨s1, a1, eu, hact⟩, e⟩ := hf
      by_cases hcH : ρ (fld (L.cscW σ) 16#u64) = c
      · exact vmF_annV_dis st ar hA hmk hK hU (i := .inl (.vmF j)) hM hV
          (Or.inr (Or.inl ⟨σ, a, hpr, hP, hq, hc, hl, hmm, hcH, ⟨s1, a1, eu, hact⟩, e⟩))
      · exfalso
        apply hact
        rw [ut_act ar hA hP.1.base.np eu]
        exact act_of_view hP.1.base hq.ksb hc hmm h0
    · exact vmF_annV_dis st ar hA hmk hK hU (i := .inl (.vmF j)) hM hV (Or.inr (Or.inr hf))
  all_goals exact False.elim hf

end dis

/-! ## The chain-level converter with the start fact in the exempt obligation -/

section exec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {ι : Type}

/-- **`execPV9_of_WPRV10` whose exempt obligation `hFH` may use the step's start fact and chain.** -/
theorem execPV9_of_WPRV10S {LP : PathsP ι} {NoV : ι → Prop}
    {FH : KLayoutP → U64 → (U64 → Prop) → (U64 → U64) → SP → ι → Prop}
    {SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop}
    (hSF : ∀ (Ch : S → Prop) (K : KLayoutP) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K) c hs q i,
      (∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) → EpochPteN K s.mem →
      SF Ch K s.mem hK hU c hs q i → StartAt (LP i K s.mem hK hU) c hs s.mem q)
    (hVS : ∀ (s : Cfg U64 U64 U64 U64) (K : KLayoutP) (hK : RegionOKP K) (hU : UserOKP K) c k ρ i, MapsP K s →
      VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem → ¬ NoV i → VSafe LP s K c k hK hU ρ i)
    (hFH : ∀ (Ch : S → Prop) (s : Cfg U64 U64 U64 U64) (K : KLayoutP) (hK : RegionOKP K) (hU : UserOKP K) c k ρ i,
      (∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) → EpochPteN K (CoreView.view K.toKLayout c ρ) →
      SF Ch K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k i → MapsP K s →
      VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem → FH K c (fun l => s.lk l = some c) ρ k i →
      Safe s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem (annV s K c ρ k))
    (P : LocPlat st arI AR MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : ∀ e, SerExitW P K0.toKLayoutV (Ch0 e)) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0) (h : ExecWPRV10 LP NoV FH SF P s0 K0 Ch0 s K Ch) :
    ExecPV9 LP s0 K0 s K ∧ (∀ e, SerExitW P K.toKLayoutV (Ch e)) ∧
      ∃ s1 : Cfg U64 U64 U64 U64, (K.vcpus = ∅ ∧ K.ptes = ptesR K s1.mem) ∧ ∀ x, GateW K x → s.mem x = s1.mem x := by
  obtain ⟨hK0, hU0⟩ := okP_R (hB 0#u64) hc0
  induction h with
  | refl => exact ⟨.refl, hB, s0, hc0, fun _ _ => rfl⟩
  | @step s1 s1' K1 K1' Ch1 Ch1' c1 _ hS g ih =>
    obtain ⟨hE, hX, e1, hCe, hk1⟩ := ih
    obtain ⟨H1, hR, -, -, hM⟩ := exec_safeRunPV9 h0 hA0 hK0 hU0 hM0 hE
    have hst : Fl4StepPV9 LP s1 K1 c1 s1' K1' := by
      refine ⟨g.arm, fun p0 k W hph hK hU => ?_, fun hs => ?_, fun hn => (g.keep hn).1⟩
      · obtain ⟨ρ, hV, i, k0, hi, hvs⟩ := g.start p0 k W hph hK hU
        have hρg : ∀ x, GateW K1 x → ρ x = e1.mem x := fun x hx =>
          (hV.2.1 x (by rw [hM.own, hx s1.mem]; exact Or.inr rfl)).trans (hk1 x hx)
        have hEv : EpochPteN K1 (CoreView.view K1.toKLayout c1 ρ) :=
          epochPteN_view c1 (epochPteN_of ⟨e1, hCe, hρg⟩)
        have hA := hSF (Ch1 c1) _ { s1 with mem := CoreView.view K1.toKLayout c1 ρ } _ _ _ _ _ i
          (hX c1).chainOf hEv hi
        refine ⟨ρ, hV, i, k0, hA, ?_⟩
        rcases hvs with ⟨hk, hvs⟩ | ⟨hk, hvs⟩
        · refine Or.inl ⟨hk, ?_⟩
          by_cases hn : NoV i
          · exact hvs hn
          · exact hVS s1 K1 hK hU c1 k0 ρ i hM hV hn
        · refine Or.inr ⟨hk, ?_⟩
          by_cases hn : NoV i
          · by_cases hf : FH K1 c1 (fun l => s1.lk l = some c1) ρ k0 i
            · exact fun _ _ => hFH (Ch1 c1) s1 K1 hK hU c1 k0 ρ i (hX c1).chainOf hEv hi hM hV hf
            · exact hvs hn hf
          · exact vSafe9_of_vSafe (hVS s1 K1 hK hU c1 k0 ρ i hM hV hn)
      · have hP := okP_R (g.serX hs 0#u64) (g.serC hs)
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
        obtain ⟨-, -, -, hSI, -⟩ := xsafeRunH_inv h0 hA0 hR
        refine ⟨e1, hCe, fun x hx => ?_⟩
        rw [← hk1 x hx]
        exact step_gate_keep hM (Fl4Proofs.P2.Serial.allowed_of_sinv hSI c1) hS hs hx
  | @hw s1 K1 Ch1 v a y _ hH ih =>
    obtain ⟨hE, hX, e1, hCe, hk1⟩ := ih
    obtain ⟨H1, -, hK, -, hM⟩ := exec_safeRunPV9 h0 hA0 hK0 hU0 hM0 hE
    refine ⟨.hw hE hH, hX, e1, hCe, fun x hx => ?_⟩
    rw [← hk1 x hx]
    exact hw_gate_keep hK hM hH hx

end exec

/-! ## U12a -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **FL4 end to end, U11 with vmF's `VSafe9` discharged also at every start whose action is not
`RESUME_CURRENT`** (module docstring). The conclusion is about the physical memory. -/
theorem serializable_fl4_localU12a (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : ∀ e, SerExitW P K0.toKLayoutV (Ch0 e)) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPRV10 (PathsP.sum (fl4LocW11JA st ar hA (masksWr_plain st) L.total a0)
        (PathsP.sum (PathsP.sum (delPteSlot st ar hA (masksWr_plain st)) (invSlotU st ar hA (masksWr_plain st)))
          (cmSlotU st ar hA (masksWr_plain st))))
      (fun i => ¬ IoIx (S := S) i) (VmDisAt12 st ar) (StartV2 st ar hA a0 arI AR MR) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  obtain ⟨hK0, hU0⟩ := okP_R (hB 0#u64) hc0
  refine serializable_e2ePV9 _ h0 hA0 hK0 hU0 hM0 (execPV9_of_WPRV10S ?_ ?_ ?_ P h0 hA0 hB hc0 hM0 h).1 hq
  · intro Ch K s hK hU c hs q i hC hE hsf
    have nv : K.vcpus = ∅ := by
      obtain ⟨_, ⟨nv, _⟩, _⟩ := hE
      exact nv
    rcases i with i | ((j | j) | j)
    · exact startAt_UN st ar hA (masksWr_plain st) L.total a0 P hIoa hC hE (startU_of_U2 st ar hA a0 hC nv hsf)
    · exact delPteStart_atN st ar hA (masksWr_plain st) hC hE (hsf.2 fun _ s b v _ _ _ => hsf.1.wr s b v)
    · exact invStartU2_atN st ar hA (masksWr_plain st) hC hE (hsf.2 fun _ s b v _ _ _ => hsf.1.wr s b v)
    · exact cmStartU2_atN st ar hA (masksWr_plain st) hC hE (hsf.2 fun _ s b v _ _ _ => hsf.1.wr s b v)
  · intro s K hK hU c k ρ i hM hV hn
    exact vSafe_io st ar hA a0 hM hV (not_not.mp hn)
  · intro Ch s K hK hU c k ρ i hC hE hsf hM hV hf
    have nv : K.vcpus = ∅ := by
      obtain ⟨_, ⟨nv, _⟩, _⟩ := hE
      exact nv
    rcases i with ((j | j | j | j | j | j | j) | j)
    · exact vmF_annV_dis12 st ar hA (masksWr_plain st) hK hU hM hV
        (vmF_act0_SF st ar hA a0 P hIoa hC nv hsf) hf
    all_goals exact False.elim hf

/-- **U11 follows from U12a** (every U11 execution is a U12a one). -/
theorem serializable_fl4_localU11of12a (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : ∀ e, SerExitW P K0.toKLayoutV (Ch0 e)) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPRV10 (PathsP.sum (fl4LocW11JA st ar hA (masksWr_plain st) L.total a0)
        (PathsP.sum (PathsP.sum (delPteSlot st ar hA (masksWr_plain st)) (invSlotU st ar hA (masksWr_plain st)))
          (cmSlotU st ar hA (masksWr_plain st))))
      (fun i => ¬ IoIx (S := S) i) (VmDisAt st ar) (StartV2 st ar hA a0 arI AR MR) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_fl4_localU12a st ar hA a0 P hIoa h0 hA0 hB hc0 hM0
    (execWPRV10_mono (fun _ _ _ _ _ _ h => dis_dis12 st ar h) h) hq

end top

end
end Fl4Proofs.P2.E2EP
