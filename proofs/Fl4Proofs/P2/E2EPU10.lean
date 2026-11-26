/-
# P2 (line p3mc, gen 9): U10, U9 with vmF's `VSafe9` discharged at the starts whose fault handler is another core's

## The discharged starts (`FHStart`, `FHAt`)
`FHStart K c hs ρ j k0`: `k0` is the VM-fault body (slot argument `j`) armed at a start state `σ` at core `c`'s view
`view K c ρ` (vmF's slot record `VmFPremA`, `VmPre (userV K)`, `QPs`, core `c`, locks `hs`, memory the view on aligned
kernel words), whose prefix state finds the action `RESUME_CURRENT` (0), the current thread's fault-handler slot
holding an endpoint cap, the endpoint in the receive state, and its head `d` homed off `c` in `ρ`
(`ρ (AFFINITY d) ≠ c`). These are the starts the gen-6 obstruction was about (the run reads `d`'s `REPLY_OBJ`
before its `AFFINITY`). **`vmF_annV_fh`**: at such a start the re-annotated body `annV k0` is `Safe` at the physical
memory (`P2/VmFhView.lean`: `vmF_fh_annV`, the decline split). `FHAt` is `FHStart` at vmF indices, `False` elsewhere.

## U10
`Fl4StepWPRV10` / `ExecWPRV10`: U9's chain-level step, `VSafe` [J] asked where `NoV i` (as U9), **`VSafe9` [J] asked
only where `NoV i` and not `FH K c hs ρ k0 i`**. `execPV9_of_WPRV10` rebuilds U9's `ExecPV9` (the exempt starts'
`VSafe9` from `hFH`). **`serializable_fl4_localU10`** (`NoV := ¬ IoIx`, `FH := FHAt`), `execWPRV10_of_WPRV9`,
**`serializable_fl4_localU9of10`**: every U9 execution is a U10 one.

## Premises of `serializable_fl4_localU10` vs `serializable_fl4_localU9`
* **Removed: `VSafe9` [J] at the vmF starts with `FHStart`** (foreign fault handler, action 0).
* **Unchanged**: `VSafe9` [J] at every other non-io start, among them the vmF starts without `FHStart` (action not
  0; no endpoint cap or endpoint not receiving; handler homed on `c`: handoff p3mc §12), `VSafe` [J] where the
  armed program is the body itself (non-io), `start` [P] otherwise, `serX` [P] / `hB`, `arm` [P], `serC`, `serG` [P],
  `keep`, `P`, `hIoa`, `h0`, `hA0`, `hc0`, `hM0`, `hq`, `StartV2`'s records with `yb` [J]. Nothing added.

No existing statement changed except the root import list.
-/
import Fl4Proofs.P2.VmFhView
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

/-! ## The discharged starts -/

section fh
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)

/-- **A vmF start at `c`'s view whose fault handler is another core's** (module docstring). -/
def FHStart (K : KLayoutP) (c : U64) (hs : U64 → Prop) (ρ : U64 → U64) (j : VmFArg S) (k0 : SP) : Prop :=
  ∃ (σ : S) (a : A), VmFPremA st ar j K.toKLayoutV ∧
    VmPre st ar (userV K.toKLayoutV) j.T j.Cs j.Ω j.U j.H j.Sg j.Rp j.Scs j.Nt j.Z j.Ac j.Locks σ ∧
    QPs K st σ ∧ L.cpu σ = c ∧ j.Locks σ = hs ∧
    (∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x) ∧ L.actionW σ = 0#u64 ∧
    (∃ (s1 : S) (a1 : A) (sl ptr badge : U64) (x' y g gr : Bool),
      sched.update_timestamp st ar σ a = ok (s1, a1) ∧
      obj.Tcb.slot (L.curW σ) layout.tcb.SLOT_FAULT_HANDLER = ok sl ∧
      obj.Slot.cap st sl s1 = ok (capability.Cap.Endpoint ptr badge x' y g gr) ∧
      L.epState s1 ptr = obj.EP_RECV ∧ ρ (affA (L.mem s1 (epHeadA ptr))) ≠ c) ∧
    k0 = tr (rsE (· ∈ K.ptes) (IoRS (st := st) (userV K.toKLayoutV) j.Locks) σ) (· ∈ K.user)
      (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ) (masksOf st σ) ar
      (R.syscall.handle_vm_fault_local j.addr j.code) ∅ a

/-- `FHStart` at the vmF indices of U9's family, `False` at the others. -/
def FHAt (K : KLayoutP) (c : U64) (hs : U64 → Prop) (ρ : U64 → U64) (k0 : SP) :
    (Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)) → Prop
  | .inl (.vmF j) => FHStart st ar K c hs ρ j k0
  | _ => False

/-- **U9's re-annotated body is `Safe` at a discharged start** (module docstring). -/
theorem vmF_annV_fh (hA : P0.ArchTotal ar) (hmk : E2E.MasksWr st) {s : Cfg U64 U64 U64 U64} {K : KLayoutP}
    (hK : RegionOKP K) (hU : UserOKP K) {c : U64} {k0 : SP} {ρ : U64 → U64}
    {i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)} (hM : MapsP K s)
    (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem)
    (hf : FHAt st ar K c (fun l => s.lk l = some c) ρ k0 i) :
    Safe s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem (annV s K c ρ k0) := by
  rcases i with ((j | j | j | j | j | j | j) | j)
  · obtain ⟨σ, a, hpr, hP, hq, hc, hl, hmm, hact, ⟨s1, a1, sl, ptr, badge, x', y, g, gr, eu, hsl, hcap, hst, hρd⟩,
      rfl⟩ := hf
    unfold annV
    rw [hM.own, hM.cls, hM.ko] at hV ⊢
    exact vmF_fh_annV hA hmk hK hU hpr.nv ⟨hpr.lay.slot8, hpr.lay.tcb, hpr.lay.ntfn8, hpr.lay.sc8⟩ hV hP hq hc hl hmm hact eu hsl hcap hst hρd
  all_goals exact False.elim hf

end fh

/-! ## The chain-level step, `VSafe9` exempt where `FH` holds -/

section exec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {ι : Type}

/-- **A step of FL4 as in U9, `VSafe9` not asked where `FH` holds** (module docstring). -/
structure Fl4StepWPRV10 (LP : PathsP ι) (NoV : ι → Prop)
    (FH : KLayoutP → U64 → (U64 → Prop) → (U64 → U64) → SP → ι → Prop)
    (SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop)
    (P : LocPlat st arI AR MR) (s : Cfg U64 U64 U64 U64) (K : KLayoutP) (Ch : U64 → S → Prop) (c : U64)
    (s' : Cfg U64 U64 U64 U64) (K' : KLayoutP) (Ch' : U64 → S → Prop) : Prop where
  /-- [P] an armed program is pure glue. -/
  arm : ∀ p, s'.ph c = .arm p → PureGlue p
  /-- [P] the glue's start fact at `c`'s view for the body `k0`; the armed program is `k0` with `VSafe` [J] for
  paths with `NoV`, or its re-annotation with `VSafe9` [J] for paths with `NoV` at starts without `FH`. -/
  start : ∀ p0 k W, s.ph c = .loc p0 (.start k) W → ∀ (hK : RegionOKP K) (hU : UserOKP K),
    ∃ ρ : U64 → U64, VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem ∧
      ∃ i k0, SF (Ch c) K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k0 i ∧
        ((k = k0 ∧ (NoV i → VSafe LP s K c k0 hK hU ρ i)) ∨
          (k = annV s K c ρ k0 ∧ (NoV i → ¬ FH K c (fun l => s.lk l = some c) ρ k0 i →
            VSafe9 LP s K c k0 hK hU ρ i)))
  /-- [P] the serial exit's ghost choice, one P3 chain per core. -/
  serX : SerStep s c → ∀ e, SerExitW P K'.toKLayoutV (Ch' e)
  /-- The glue's layout convention at the serial exit. -/
  serC : SerStep s c → K'.vcpus = ∅ ∧ K'.ptes = ptesR K' s'.mem
  /-- [P] the exit ghost with rule 8. -/
  serG : SerStep s c → MapsP K' s'
  /-- Layout and chains change only at serial steps. -/
  keep : ¬ SerStep s c → K' = K ∧ Ch' = Ch

inductive ExecWPRV10 (LP : PathsP ι) (NoV : ι → Prop)
    (FH : KLayoutP → U64 → (U64 → Prop) → (U64 → U64) → SP → ι → Prop)
    (SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop)
    (P : LocPlat st arI AR MR) (s0 : Cfg U64 U64 U64 U64) (K0 : KLayoutP) (Ch0 : U64 → S → Prop) :
    Cfg U64 U64 U64 U64 → KLayoutP → (U64 → S → Prop) → Prop
  | refl : ExecWPRV10 LP NoV FH SF P s0 K0 Ch0 s0 K0 Ch0
  | step {s s' : Cfg U64 U64 U64 U64} {K K' : KLayoutP} {Ch Ch' : U64 → S → Prop} {c : U64} :
      ExecWPRV10 LP NoV FH SF P s0 K0 Ch0 s K Ch → Step s c s' → Fl4StepWPRV10 LP NoV FH SF P s K Ch c s' K' Ch' →
      ExecWPRV10 LP NoV FH SF P s0 K0 Ch0 s' K' Ch'
  | hw {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {Ch : U64 → S → Prop} {v a x : U64} :
      ExecWPRV10 LP NoV FH SF P s0 K0 Ch0 s K Ch → HwStepP K s v a x →
      ExecWPRV10 LP NoV FH SF P s0 K0 Ch0 (hwCfg s a x) K Ch

/-- **Every U9 execution is a U10 one.** -/
theorem execWPRV10_of_WPRV9 {LP : PathsP ι} {NoV : ι → Prop}
    {FH : KLayoutP → U64 → (U64 → Prop) → (U64 → U64) → SP → ι → Prop}
    {SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop}
    {P : LocPlat st arI AR MR} {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop}
    (h : ExecWPRV9 LP NoV SF P s0 K0 Ch0 s K Ch) : ExecWPRV10 LP NoV FH SF P s0 K0 Ch0 s K Ch := by
  induction h with
  | refl => exact .refl
  | step _ hS g ih =>
    refine .step ih hS ⟨g.arm, fun p0 k W hph hK hU => ?_, g.serX, g.serC, g.serG, g.keep⟩
    obtain ⟨ρ, hV, i, k0, hi, hvs⟩ := g.start p0 k W hph hK hU
    refine ⟨ρ, hV, i, k0, hi, ?_⟩
    rcases hvs with h1 | ⟨hk, h2⟩
    · exact Or.inl h1
    · exact Or.inr ⟨hk, fun hn _ => h2 hn⟩
  | hw _ hH ih => exact .hw ih hH

/-- **An `ExecWPRV10` is an `ExecPV9`** (`execPV9_of_WPRV9`; the starts without `NoV` get `VSafe` from `hVS`, the
starts with `FH` their re-annotation's `Safe` from `hFH`). -/
theorem execPV9_of_WPRV10 {LP : PathsP ι} {NoV : ι → Prop}
    {FH : KLayoutP → U64 → (U64 → Prop) → (U64 → U64) → SP → ι → Prop}
    {SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop}
    (hSF : ∀ (Ch : S → Prop) (K : KLayoutP) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K) c hs q i,
      (∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) → EpochPteN K s.mem →
      SF Ch K s.mem hK hU c hs q i → StartAt (LP i K s.mem hK hU) c hs s.mem q)
    (hVS : ∀ (s : Cfg U64 U64 U64 U64) (K : KLayoutP) (hK : RegionOKP K) (hU : UserOKP K) c k ρ i, MapsP K s →
      VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem → ¬ NoV i → VSafe LP s K c k hK hU ρ i)
    (hFH : ∀ (s : Cfg U64 U64 U64 U64) (K : KLayoutP) (hK : RegionOKP K) (hU : UserOKP K) c k ρ i, MapsP K s →
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
            · exact fun _ _ => hFH s1 K1 hK hU c1 k0 ρ i hM hV hf
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

/-! ## U10 -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **FL4 end to end, U9 with vmF's `VSafe9` discharged at the starts with a foreign fault handler** (module
docstring). The conclusion is about the physical memory. -/
theorem serializable_fl4_localU10 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : ∀ e, SerExitW P K0.toKLayoutV (Ch0 e)) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPRV10 (PathsP.sum (fl4LocW11JA st ar hA (masksWr_plain st) L.total a0)
        (PathsP.sum (PathsP.sum (delPteSlot st ar hA (masksWr_plain st)) (invSlotU st ar hA (masksWr_plain st)))
          (cmSlotU st ar hA (masksWr_plain st))))
      (fun i => ¬ IoIx (S := S) i) (FHAt st ar) (StartV2 st ar hA a0 arI AR MR) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  obtain ⟨hK0, hU0⟩ := okP_R (hB 0#u64) hc0
  refine serializable_e2ePV9 _ h0 hA0 hK0 hU0 hM0 (execPV9_of_WPRV10 ?_ ?_ ?_ P h0 hA0 hB hc0 hM0 h).1 hq
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
  · intro s K hK hU c k ρ i hM hV hf
    exact vmF_annV_fh st ar hA (masksWr_plain st) hK hU hM hV hf

/-- **U9 follows from U10** (every U9 execution is a U10 one). -/
theorem serializable_fl4_localU9of10 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : ∀ e, SerExitW P K0.toKLayoutV (Ch0 e)) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPRV9 (PathsP.sum (fl4LocW11JA st ar hA (masksWr_plain st) L.total a0)
        (PathsP.sum (PathsP.sum (delPteSlot st ar hA (masksWr_plain st)) (invSlotU st ar hA (masksWr_plain st)))
          (cmSlotU st ar hA (masksWr_plain st))))
      (fun i => ¬ IoIx (S := S) i) (StartV2 st ar hA a0 arI AR MR) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_fl4_localU10 st ar hA a0 P hIoa h0 hA0 hB hc0 hM0 (execWPRV10_of_WPRV9 h) hq

end top

end
end Fl4Proofs.P2.E2EP
