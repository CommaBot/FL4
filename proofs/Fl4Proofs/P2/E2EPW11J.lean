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

/-- **The convention gives `PteConv`** at a layout with a bundle state and no VCPU. -/
theorem pteConv_canon {K : KLayoutP} {s1 : Cfg U64 U64 U64 U64} (hb : ∃ σe, SlJAt (L := L) K.toKLayout σe)
    (nv : K.vcpus = ∅) (he : K.ptes = ptesCanon st K s1.mem) : PteConv st K s1 := by
  have h : ∃ Zx, GhostOf st K.toKLayout Zx := by
    obtain ⟨σe, A', arI, AR, Zx, Cx, Ax, Lst, D, a', τ, B⟩ := hb
    exact ⟨Zx, σe, A', arI, AR, Cx, Ax, Lst, D, a', τ, B⟩
  unfold ptesCanon at he
  rw [dif_pos h] at he
  obtain ⟨σe, A', arI, AR, Cx, Ax, Lst, D, a', τ, B⟩ := Classical.choose_spec h
  exact pteConv_of B nv (by rw [he])

/-- `RegionOKP` / `UserOKP` from `PteConv` (gen 5's lemmas at its bundle). -/
theorem okP_of_conv {K : KLayoutP} {s1 : Cfg U64 U64 U64 U64} (hC : PteConv st K s1)
    (hV : RegionOKV K.toKLayoutV) (hU : UserOKV K.toKLayoutV) : RegionOKP K ∧ UserOKP K := by
  obtain ⟨σe, A', arI, AR, Zx, Cx, Ax, Lst, D, a', τ, B, hsub, nv⟩ := hC
  exact ⟨regionOKP_of_conv B hV (fun b hb => (hsub hb).1) nv, userOKP_of_conv B hU (fun b hb => (hsub hb).1)⟩

/-- **`QPs` at a start state of any store type** from `PteConv` at the epoch start, agreement with it on the `GateW`
words, the kernel base and the start's memory link. -/
theorem qPs_of_conv {S' : Type} {st' : machine.Store S'} [L' : LawfulStore st'] {K : KLayoutP}
    {s1 s : Cfg U64 U64 U64 U64} (hC : PteConv st K s1) (hkeep : ∀ x, GateW K x → s.mem x = s1.mem x)
    {σ : S'} (hk : L'.ksb σ = K.ksb) (hμ : ∀ x, Aligned x → x ∉ K.user → L'.mem σ x = s.mem x) :
    QPs K st' σ := by
  obtain ⟨σe, A', arI, AR, Zx, Cx, Ax, Lst, D, a', τ, B, hsub, nv⟩ := hC
  have Q : QPs K st σe := qPs_of_bundle B (fun b hb => (hsub hb).1) nv
  have hnu : ∀ hi : U64, hi.val < 2048 → atAF K.ksb hi ∉ K.user :=
    fun hi hhi hu => Q.uoff _ (Or.inl hu) hi hhi rfl
  have hnp : ∀ hi : U64, hi.val < 2048 → atAF K.ksb hi ∉ K.ptes :=
    fun hi hhi hb => ((hsub hb).2 hi hhi).1 rfl
  have hm : ∀ hi : U64, hi.val < 2048 → L'.mem σ (atAF K.ksb hi) = s1.mem (atAF K.ksb hi) := by
    intro hi hhi
    rw [hμ _ (Q.al hi hhi) (hnu hi hhi)]
    exact hkeep _ (gateW_of_region (region_none_tab B hhi) (hnp hi hhi) nv)
  refine ⟨Q.ks, hk, ?_, Q.al, Q.uoff⟩
  intro hi hhi
  rw [hk]
  refine ⟨hnp hi hhi, fun lo hlo hne hb => ?_⟩
  rw [hm hi hhi] at hne hb
  exact ((hsub hb).2 hi hhi).2 hne lo hlo rfl

end conv

/-! ## The glue with the convention -/

/-- **`StartQPB`** [P]: `StartQP` without its `QPs` clause — at every state the glue starts the `ownV` path `Pv` as
`q0`, the armed program `q` is the body of `Pp` (the restricted, PTE-cut path) there. -/
def StartQPB {own own' : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
    {ko : U64 → Serial.ClsOwner U64} {User : U64 → Prop}
    (Pv : E2E.LocalPath own cls ko User) (Pp : E2E.LocalPath own' cls ko User) (hS : Pv.S = Pp.S)
    (hA : Pv.A = Pp.A) (c : U64) (hs : U64 → Prop) (μ : U64 → U64) (q0 q : SP) : Prop :=
  ∀ (σ : Pv.S) (a : Pv.A), Pv.Pre σ → Pv.L.cpu σ = c → Pv.Locks σ = hs →
    (∀ x, Aligned x → ¬ User x → Pv.L.mem σ x = μ x) → q0 = Pv.body σ a →
    q = Pp.body (cast hS σ) (cast hA a)

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

/-- **The W11 start fact, the convention's form**: `StartP3W11` [P] for some `q0` and `StartQPB` [P]. -/
def StartP3W11JB (Ch : S → Prop) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K)
    (hU : UserOKP K) (c : U64) (hs : U64 → Prop) (q : SP) (i : Fl4IxW (S := S)) : Prop :=
  ∃ q0, StartP3W11 st ar hA hm hSt a0 arI AR MR Ch K.toKLayoutV m hK.base hU.base c hs q0 i ∧
    StartQPB ((fl4LocP3W6 st ar hA hm hSt a0).paths (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base)
      (fl4LocW11J st ar hA hm hSt a0 i K m hK hU) rfl rfl c hs m q0 q

variable {arI AR MR}

/-- **The convention's boot facts** give the boot layout's `RegionOKP` / `UserOKP`. -/
theorem boot_okP (P : LocPlat st arI AR MR) {K0 : KLayoutP} {Ch0 : S → Prop} {s0 : Cfg U64 U64 U64 U64}
    (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesCanon st K0 s0.mem) :
    PteConv st K0 s0 ∧ RegionOKP K0 ∧ UserOKP K0 := by
  have hok := serExitW_ok hB (vcpuLay_empty hc0.1)
  obtain ⟨σe, hC, hσ⟩ := hB.lay
  have hc := pteConv_canon ⟨σe, hC.bun σe hσ⟩ hc0.1 hc0.2
  exact ⟨hc, okP_of_conv hc hok.1 hok.2⟩

/-- **An `ExecWPJ` is an `ExecP`, with the epoch invariant** (module docstring). -/
theorem execP_of_WPJ (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} (h0 : Init s0) (hA0 : ArmInv s0)
    (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesCanon st K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPJ (fl4LocW11J st ar hA hm hSt a0) (StartP3W11JB st ar hA hm hSt a0 arI AR MR) P s0 K0 Ch0 s K Ch) :
    ExecP (fl4LocW11J st ar hA hm hSt a0) s0 K0 s K ∧ SerExitW P K.toKLayoutV Ch ∧
      ∃ s1, PteConv st K s1 ∧ ∀ x, GateW K x → s.mem x = s1.mem x := by
  obtain ⟨hC0, hK0, hU0⟩ := boot_okP st P hB hc0
  induction h with
  | refl => exact ⟨.refl, hB, s0, hC0, fun _ _ => rfl⟩
  | @step s1 s1' K1 K1' Ch1 Ch1' c1 _ hS g ih =>
    obtain ⟨hE, hX, e1, hCe, hk1⟩ := ih
    have hst : Fl4StepP (fl4LocW11J st ar hA hm hSt a0) s1 K1 c1 s1' K1' := by
      refine ⟨g.arm, fun p0 k W hph hK hU => ?_, fun hs => ?_, fun hn => (g.keep hn).1⟩
      · obtain ⟨i, q0, hW, hQB⟩ := g.start p0 k W hph hK hU
        obtain ⟨σ, a, hP, hc, hl, hμ, e⟩ := startAt_P3W11 st ar hA hm hSt a0 P hIoa hX.chainOf hW
        have hk := pre_ksbW6 st ar hA hm hSt a0 i K1 s1.mem hK hU σ hP
        have hq := qPs_of_conv
          (L' := ((fl4LocP3W6 st ar hA hm hSt a0).paths (fl4Dflt st ar hm) i K1.toKLayoutV s1.mem hK.base hU.base).L)
          hCe hk1 hk (fun x hx hu => hμ x hx hu)
        exact ⟨i, σ, a, ⟨hP, hq⟩, hc, hl, hμ, hQB σ a hP hc hl hμ e⟩
      · have hok := serExitW_ok (g.serX hs) (vcpuLay_empty (g.serC hs).1)
        obtain ⟨σe, hC, hσ⟩ := (g.serX hs).lay
        have hc := pteConv_canon ⟨σe, hC.bun σe hσ⟩ (g.serC hs).1 (g.serC hs).2
        have hP := okP_of_conv hc hok.1 hok.2
        exact ⟨hP.1, hP.2, g.serG hs⟩
    refine ⟨.step hE hS hst, ?_, ?_⟩
    · by_cases hs : SerStep s1 c1
      · exact g.serX hs
      · obtain ⟨e1, e2⟩ := g.keep hs
        rw [e1, e2]; exact hX
    · by_cases hs : SerStep s1 c1
      · obtain ⟨σe, hC, hσ⟩ := (g.serX hs).lay
        exact ⟨s1', pteConv_canon ⟨σe, hC.bun σe hσ⟩ (g.serC hs).1 (g.serC hs).2, fun _ _ => rfl⟩
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

/-- **FL4 end to end, W11's family and glue, rule 8 with the PTE set by the glue's convention** (module
docstring): no `PteLay`, no `StartQP` `QPs` clause; the only PTE-side condition is the convention itself
(`serC` and its boot instance `hc0`). -/
theorem serializable_fl4_localW11PJ (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} (h0 : Init s0) (hA0 : ArmInv s0)
    (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesCanon st K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPJ (fl4LocW11J st ar hA hm hSt a0) (StartP3W11JB st ar hA hm hSt a0 arI AR MR) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  obtain ⟨-, hK0, hU0⟩ := boot_okP st P hB hc0
  exact serializable_e2eP _ h0 hA0 hK0 hU0 hM0
    (execP_of_WPJ st ar hA hm hSt a0 P hIoa h0 hA0 hB hc0 hM0 h).1 hq

end top

end
end Fl4Proofs.P2.E2EP
