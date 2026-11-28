/-
P2 (line nscope, gen 6): **`serializable_fl4_localW11PJ`** — pte gen 7's `serializable_fl4_localW11P` with the PTE
set picked by the glue's convention, `PteLay` [P] and `StartQP`'s `QPs` half [P] discharged.

* **The convention, definitionally.** `GhostOf Kl Zx`: `Zx` is the ghost of some bundle state of layout `Kl`.
  **`ptesCanon st K m`** := `ptesE K {b | PtW Zx.L1 b} m` for the ghost `Zx` chosen (`Classical.choose`) among the
  layout's bundle ghosts (`∅` if there is none): the leaf entries of a bundle ghost minus the ASID-table / pool words
  of the memory `m`. The glue step **`Fl4StepWPJ`** is `Fl4StepWP` with `serP` / `serV` replaced by **`serC`**: at a
  serial step the new layout is chosen with no VCPU and `K'.ptes = ptesCanon st K' s'.mem` (a choice of the glue, like
  `serX`'s layout choice, not a fact about the state). **`ExecWPJ`**: executions with these steps; the boot layout
  is chosen the same way (`K0.vcpus = ∅ ∧ K0.ptes = ptesCanon st K0 s0.mem`).
* **`PteLay` / `RegionOKP` / `UserOKP`** at the boot and every serial exit: `serExitW_ok` (as before) and the
  convention through `pteConv_canon` (a bundle state of the new layout exists: `SerExitW.lay`, `ChainLay.bun`) and
  gen 5's `regionOKP_of_conv` / `userOKP_of_conv`.
* **`StartQP`'s `QPs` half**: the start fact is now **`StartP3W11JB`** = `StartP3W11` [P] and **`StartQPB`** [P] —
  `StartQP` without the `QPs` clause (only "the armed program is the restricted, cut path's body", the program
  annotation `StartAt` uses). `QPs` at the start state is derived inside the execution: `execP_of_WPJ` carries, along
  the `ExecWPJ`, an epoch start `s1` with `PteConv st K s1` and agreement on every `GateW K` word (`step_gate_keep`,
  `hw_gate_keep`; the `ExecP` built so far gives `Allowed`), and **`qPs_of_conv`** gives `QPs` at the start state from
  the `StartAt` memory link and **`pre_ksbW6`** (`L.ksb σ = K.ksb` from each slot's `Pre`: the bundle for io / st /
  irq / sl, `VmBase.kb` for vmF / vmR, and for vx / vt the core's node in `StLay.nd` — **`ksb_of_stLay`** — since
  `startAt_P3W11` returns only the path's `Pre`, not the chain state of the glue entry fact, so `ksb_of_chain` is
  not reachable through it).
* **`serializable_fl4_localW11PJ`**: premises `LocPlat`, `MRKeepIoapic`, `Init`, `ArmInv`, the boot `SerExitW` [P],
  the boot convention (`K0.vcpus = ∅`, `K0.ptes = ptesCanon …`, the same choice as `serC`), `MapsP K0 s0`, the
  `ExecWPJ` (steps: `arm` [P], start `StartP3W11JB` [P], `serX` [P], `serC` = the convention, `serG` [P]; `HwStepP`
  [P]), `NoLoc s`. **No PTE-side premise beyond the convention**: `PteLay` and `StartQP`'s `QPs` are gone.

No existing statement or file changed (pte's `E2EPW11` untouched).
-/
import Fl4Proofs.P2.E2EPW11
import Fl4Proofs.P2.E2EPJEp2
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

/-! ## The kernel base at every start state -/

section ksb
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **The kernel base from the core's node layout** (`StLay.nd`, `NodePlaced`). -/
theorem ksb_of_stLay {Kl : OwnMap.KLayout} {T T' Scs : Set U64} {Z : U64 → Nat} {s : S}
    (hL : StLay Kl st T Scs Z s) (hN : NodePlaced st T' s (L.cpu s)) : L.ksb s = Kl.ksb := by
  have i0 := inNode_of_region (hL.nd 0#u64 (by simp))
  have i1 := inNode_of_region (hL.nd 4287#u64 (by simp))
  have v0 := nodeAt_val hN (off := 0#u64) (by simp)
  have v1 := nodeAt_val hN (off := 4287#u64) (by simp)
  obtain ⟨-, a0, -⟩ := i0
  obtain ⟨-, -, b1⟩ := i1
  unfold LawfulStore.nodeBase at v0 v1
  rw [v0] at a0
  rw [v1] at b1
  have e0 : (0#u64 : U64).val = 0 := rfl
  have e1 : (4287#u64 : U64).val = 4287 := rfl
  rw [e0] at a0
  rw [e1] at b1
  exact UScalar.eq_of_val_eq (by omega)

/-- The current core's node is placed (from P1's `BXI`). -/
theorem nodePlaced_of_bxi {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s : S}
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) : NodePlaced st T s (L.cpu s) := by
  have h0 := h.1.choose_spec.choose_spec
  exact h0.nodes _ h0.cur

end ksb

section pre
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)

/-- **Every start state of W6's family has the layout's kernel base** (module docstring). -/
theorem pre_ksbW6 (i : Fl4IxW (S := S)) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (σ : ((fl4LocP3W6 st ar hA hm hSt a0).paths (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base).S)
    (hσ : ((fl4LocP3W6 st ar hA hm hSt a0).paths (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base).Pre σ) :
    @LawfulStore.ksb _ _
      ((fl4LocP3W6 st ar hA hm hSt a0).paths (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base).L σ = K.ksb := by
  cases i with
  | vmF i =>
    by_cases hp : (vmFSlot st ar hA hm).Prem i K.toKLayoutV m
    · have key : ∀ (P : E2E.LocalPath (OwnMap.own (userV K.toKLayoutV)) (OwnMap.cls (userV K.toKLayoutV))
          (OwnMap.ko (userV K.toKLayoutV) m) (· ∈ (userV K.toKLayoutV).user)) (W : NoVcpuRW K.toKLayoutV P),
          P = (vmFSlot st ar hA hm).path i K.toKLayoutV m hK.base hU.base hp →
          ∀ σ, (LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)).Pre σ →
            @LawfulStore.ksb _ _ (LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)).L σ
              = K.ksb := by
        rintro P W rfl σ hσ
        have hs' : VmPre st ar (userV K.toKLayoutV) i.T i.Cs i.Ω i.U i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac i.Locks σ := hσ
        exact hs'.1.base.kb.symm
      exact key _ _ (SlotU.fam_pos _ _ hp) σ hσ
    · exact absurd hσ (SlotU.noPre (fl4Dflt st ar hm) _ hp σ)
  | vmR i =>
    by_cases hp : (vmRSlotP3 st ar hA hm).Prem i K.toKLayoutV m
    · have key : ∀ (P : E2E.LocalPath (OwnMap.own (userV K.toKLayoutV)) (OwnMap.cls (userV K.toKLayoutV))
          (OwnMap.ko (userV K.toKLayoutV) m) (· ∈ (userV K.toKLayoutV).user)) (W : NoVcpuRW K.toKLayoutV P),
          P = (vmRSlotP3 st ar hA hm).path i K.toKLayoutV m hK.base hU.base hp →
          ∀ σ, (LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)).Pre σ →
            @LawfulStore.ksb _ _ (LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)).L σ
              = K.ksb := by
        rintro P W rfl σ hσ
        have hs' : VmRRPreJ st ar (userV K.toKLayoutV) (userV K.toKLayoutV).heap.tcbs i.Cs i.Ω i.Sg
            (userV K.toKLayoutV).heap.scs (userV K.toKLayoutV).heap.ntfns (userV K.toKLayoutV).heap.scBits i.Ac
            i.Locks i.rptr i.ep σ := hσ
        exact (VmRRPreJ.pre hs').1.base.kb.symm
      exact key _ _ (SlotU.fam_pos _ _ hp) σ hσ
    · exact absurd hσ (SlotU.noPre (fl4Dflt st ar hm) _ hp σ)
  | io i =>
    by_cases hp : (ioSlotP3W st ar hA hm).Prem i K.toKLayoutV m
    · have key : ∀ (P : E2E.LocalPath (OwnMap.own (userV K.toKLayoutV)) (OwnMap.cls (userV K.toKLayoutV))
          (OwnMap.ko (userV K.toKLayoutV) m) (· ∈ (userV K.toKLayoutV).user)) (W : NoVcpuRW K.toKLayoutV P),
          P = (ioSlotP3W st ar hA hm).path i K.toKLayoutV m hK.base hU.base hp →
          ∀ σ, (LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)).Pre σ →
            @LawfulStore.ksb _ _ (LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)).L σ
              = K.ksb := by
        rintro P W rfl σ hσ
        have hs' : SlJAt (L := L) K.toKLayout σ ∧ i.Q K.toKLayoutV m σ := hσ
        exact (slJAt_ksb hs'.1 : L.ksb σ = K.ksb)
      exact key _ _ (SlotU.fam_pos _ _ hp) σ hσ
    · exact absurd hσ (SlotU.noPre (fl4Dflt st ar hm) _ hp σ)
  | st i =>
    by_cases hp : (stSlotP3W st ar hA hm).Prem i K.toKLayoutV m
    · have key : ∀ (P : E2E.LocalPath (OwnMap.own (userV K.toKLayoutV)) (OwnMap.cls (userV K.toKLayoutV))
          (OwnMap.ko (userV K.toKLayoutV) m) (· ∈ (userV K.toKLayoutV).user)) (W : NoVcpuRW K.toKLayoutV P),
          P = (stSlotP3W st ar hA hm).path i K.toKLayoutV m hK.base hU.base hp →
          ∀ σ, (LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)).Pre σ →
            @LawfulStore.ksb _ _ (LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)).L σ
              = K.ksb := by
        rintro P W rfl σ hσ
        have hs' : SlJAt (L := L) K.toKLayout σ ∧ i.Q K.toKLayoutV m σ := hσ
        exact (slJAt_ksb hs'.1 : L.ksb σ = K.ksb)
      exact key _ _ (SlotU.fam_pos _ _ hp) σ hσ
    · exact absurd hσ (SlotU.noPre (fl4Dflt st ar hm) _ hp σ)
  | irq i =>
    by_cases hp : (irqSlotP3W st ar hA hm).Prem i K.toKLayoutV m
    · have key : ∀ (P : E2E.LocalPath (OwnMap.own (userV K.toKLayoutV)) (OwnMap.cls (userV K.toKLayoutV))
          (OwnMap.ko (userV K.toKLayoutV) m) (· ∈ (userV K.toKLayoutV).user)) (W : NoVcpuRW K.toKLayoutV P),
          P = (irqSlotP3W st ar hA hm).path i K.toKLayoutV m hK.base hU.base hp →
          ∀ σ, (LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)).Pre σ →
            @LawfulStore.ksb _ _ (LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)).L σ
              = K.ksb := by
        rintro P W rfl σ hσ
        have hs' : IrqPreV K.toKLayoutV st m σ := hσ
        exact (slJAt_ksb hs'.1 : L.ksb σ = K.ksb)
      exact key _ _ (SlotU.fam_pos _ _ hp) σ hσ
    · exact absurd hσ (SlotU.noPre (fl4Dflt st ar hm) _ hp σ)
  | sl i =>
    by_cases hp : (slSlotP3W6 st ar hA hm hSt a0).Prem i K.toKLayoutV m
    · have key : ∀ (P : E2E.LocalPath (OwnMap.own K.toKLayout) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m)
          (· ∈ K.user)) (W : AvoidV K.toKLayoutV P),
          P = (slSlotP3W6 st ar hA hm hSt a0).path i K.toKLayoutV m hK.base hU.base hp →
          ∀ σ, (LocalPath.cutLiftV hK.base hU.base (fun x ⟨_, hv, _⟩ => ko_vcpu hK.base hv m) P W).Pre σ →
            @LawfulStore.ksb _ _ (LocalPath.cutLiftV hK.base hU.base (fun x ⟨_, hv, _⟩ => ko_vcpu hK.base hv m)
              P W).L σ = K.ksb := by
        rintro P W rfl σ hσ
        exact (slJAt_ksb (L := L) hσ.1 : L.ksb σ = K.ksb)
      exact key _ _ (SlotC.fam_pos _ _ hp) σ hσ
    · exact absurd hσ (SlotC.noPre (fl4Dflt st ar hm) _ hp σ)
  | vq j =>
    cases j with
    | inl i =>
      by_cases hp : (vxSlotP3 st ar hA hm).Prem i K.toKLayoutV m
      · have key : ∀ P, P = (vxSlotP3 st ar hA hm).path i K.toKLayoutV m hK.base hU.base hp →
            ∀ σ, P.Pre σ → @LawfulStore.ksb _ _ P.L σ = K.ksb := by
          rintro P rfl σ hσ
          have hs' : VxPre st i K.toKLayoutV m σ := hσ
          exact (ksb_of_stLay (L := L) hs'.1.lay (nodePlaced_of_bxi (L := L) hs'.1.inv) : L.ksb σ = K.ksb)
        exact key _ (SlotN.fam_pos _ _ hp) σ hσ
      · exact absurd hσ (SlotN.noPre (fl4Dflt st ar hm) _ hp σ)
    | inr i =>
      by_cases hp : (vtSlotP3W5 st ar hA hm).Prem i K.toKLayoutV m
      · have key : ∀ P, P = (vtSlotP3W5 st ar hA hm).path i K.toKLayoutV m hK.base hU.base hp →
            ∀ σ, P.Pre σ → @LawfulStore.ksb _ _ P.L σ = K.ksb := by
          rintro P rfl σ hσ
          have hs' : VtPre st i K.toKLayoutV σ := hσ
          exact (ksb_of_stLay (L := L) hs'.ent.lay (nodePlaced_of_bxi (L := L) hs'.ent.inv) : L.ksb σ = K.ksb)
        exact key _ (SlotN.fam_pos _ _ hp) σ hσ
      · exact absurd hσ (SlotN.noPre (fl4Dflt st ar hm) _ hp σ)

end pre

/-! ## The convention -/

section conv
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]

/-- `Zx` is the ghost of some bundle state of the layout `Kl`. -/
def GhostOf (Kl : OwnMap.KLayout) (Zx : Fl4Proofs.P3.XSets) : Prop :=
  ∃ (σe : S) (A' : Type) (arI : machine.Arch A') (AR : A' → Fl4Spec.Cr3 → Prop) (Cx Ax : Set U64)
    (Lst : U64 → List U64) (D : Set U64) (a' : A') (τ : Fl4Spec.State Unit),
    SlJAtZ (L := L) arI AR Zx Cx Ax Lst D Kl σe a' τ

/-- **The glue's PTE set** (module docstring): the leaf entries of a chosen bundle ghost of the layout, minus the
ASID-table / pool words of the memory `m`. -/
def ptesCanon (K : KLayoutP) (m : U64 → U64) : Set U64 :=
  if h : ∃ Zx, GhostOf st K.toKLayout Zx then ptesE K {b | Fl4Proofs.P3.Vs.PtW (Classical.choose h).L1 b} m else ∅

variable {st}

end conv

/-! ## The glue with the convention -/

section exec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {ι : Type}

variable (st) in
/-- **A step of FL4 with the glue premises named, rule 8, the PTE set by convention** (module docstring). -/
structure Fl4StepWPJ (LP : PathsP ι)
    (SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop)
    (P : LocPlat st arI AR MR) (s : Cfg U64 U64 U64 U64) (K : KLayoutP) (Ch : S → Prop) (c : U64)
    (s' : Cfg U64 U64 U64 U64) (K' : KLayoutP) (Ch' : S → Prop) : Prop where
  /-- [P] an armed program is pure glue. -/
  arm : ∀ p, s'.ph c = .arm p → PureGlue p
  /-- [P] the glue's start fact. -/
  start : ∀ p0 k W, s.ph c = .loc p0 (.start k) W → ∀ (hK : RegionOKP K) (hU : UserOKP K),
    ∃ i, SF Ch K s.mem hK hU c (fun l => s.lk l = some c) k i
  /-- [P] the serial exit's ghost choice. -/
  serX : SerStep s c → SerExitW P K'.toKLayoutV Ch'
  /-- The glue's layout convention at the serial exit: no VCPU, the PTE set `ptesCanon` of the exit memory. -/
  serC : SerStep s c → K'.vcpus = ∅ ∧ K'.ptes = ptesCanon st K' s'.mem
  /-- [P] the exit ghost with rule 8. -/
  serG : SerStep s c → MapsP K' s'
  /-- Layout and chain change only at serial steps. -/
  keep : ¬ SerStep s c → K' = K ∧ Ch' = Ch

/-- **An execution of FL4 with the convention-glue steps.** -/
inductive ExecWPJ (LP : PathsP ι)
    (SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop)
    (P : LocPlat st arI AR MR) (s0 : Cfg U64 U64 U64 U64) (K0 : KLayoutP) (Ch0 : S → Prop) :
    Cfg U64 U64 U64 U64 → KLayoutP → (S → Prop) → Prop
  | refl : ExecWPJ LP SF P s0 K0 Ch0 s0 K0 Ch0
  | step {s s' : Cfg U64 U64 U64 U64} {K K' : KLayoutP} {Ch Ch' : S → Prop} {c : U64} :
      ExecWPJ LP SF P s0 K0 Ch0 s K Ch → Step s c s' → Fl4StepWPJ st LP SF P s K Ch c s' K' Ch' →
      ExecWPJ LP SF P s0 K0 Ch0 s' K' Ch'
  | hw {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {Ch : S → Prop} {v a x : U64} :
      ExecWPJ LP SF P s0 K0 Ch0 s K Ch → HwStepP K s v a x → ExecWPJ LP SF P s0 K0 Ch0 (hwCfg s a x) K Ch

end exec

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop) (MR : A3 → Fl4Spec.MachineState → Prop)

variable {arI AR MR}

end top

end
end Fl4Proofs.P2.E2EP
