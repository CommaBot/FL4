/-
# P2 (line p3mc, gen 7): U9, the body armed with the view's read set narrowed to the words whose owner the view keeps

## Why (gen 6, `P2/ViewSafeObstr.lean`)
U6–U8 arm the body annotated at the view start state: a word the view lets `c` read is a plain `rd`. For a thread
homed on another core in `ρ`, its home-owned words are held by `c` at the view but not readable at the physical
memory (`view_home_rd_unsafe`), so `VSafe` [J] is false at every start whose run reaches such a read (vmF / sl trap:
the fault handler's `REPLY_OBJ`; vmR / sl ReplyRecv: the caller's `STATE`).

## The narrowed annotation (`annV`)
The annotation is ghost (`E2E.StartAt` docstring; `Serial.narrowSP` module docstring). U9 arms
`annV s K c ρ k0 := narrowSP s.cls s.ko c (VO K c ρ) ∅ k0`, the start's body `k0` re-annotated for the read set
`RS σ ∧ VO K c ρ`, **`VO K c ρ x`: the view keeps `x`'s owner** (`ownP K (view K c ρ) x = ownP K ρ x`). A read of a
word whose owner the view changes is a class read where the configuration's class owner allows it and a speculative
read otherwise, exactly as U5's annotation at the physical memory reads such words (`AccessVmDec`: `VmRep`). This is
the conservative model.
* **`VSafe9` [J]** (per start, as `VSafe`, guarded by `view ≠ ρ`): the re-annotated body is `Safe` at the physical
  memory. `vSafe9_of_vSafe`: it follows from U8's `VSafe` (`Serial.safe_narrow`).
* **Not refuted at foreign-homed starts** (proved, the gen-6 obstruction is gone): for a thread homed off `c` in `ρ`
  and a home-owned word `x` of it, `VO` fails at `x` and the class owner is not `c`'s or the gate's, so the armed
  read of `x` is speculative (`u9_home_rds`) and `Safe` there asks nothing of `x` (`u9_home_safe_iff`); compare
  `CoreView.view_home_rd_unsafe` for U8's annotation.

## U9
`Fl4StepPV9` / `ExecPV9`: U6's step, the armed program either the start's body (U8's case, with `VSafe`) or its
re-annotation (with `VSafe9`); **`exec_safeRunPV9`**, `serializable_e2ePV9`. `Fl4StepWPRV9` / `ExecWPRV9`: U8's
chain-level step the same way, `VSafe` / `VSafe9` asked only where `NoV i`; `execPV9_of_WPRV9`.
**`serializable_fl4_localU9`** (NoV := ¬ IoIx: the io starts' `VSafe` and `VSafe9` from `vSafe_io`);
`execWPRV9_of_WPRV8`, **`serializable_fl4_localU8of9`**: every U8 execution is a U9 one.

## Premises of `serializable_fl4_localU9` vs `serializable_fl4_localU8`
* **Changed**: `start` [P] may arm the re-annotated body; then it carries `VSafe9` [J] instead of `VSafe` [J] for the
  non-io slots (vmF, vmR, st, irq, sl, vq, delPte, inv, cm). `VSafe9` is implied by `VSafe` and, unlike `VSafe`, is
  not refuted by the gen-6 obstruction at starts reading another core's thread. Discharged for no further slot yet
  (vmF / sl / vmR need the narrowed `PathObl` / `ReadOnce` and the decline split: handoff §10).
* Everything else unchanged (`serX` [P] / `hB`, `arm` [P], `serC`, `serG` [P], `keep`, `P`, `hIoa`, `h0`, `hA0`,
  `hc0`, `hM0`, `hq`, `StartV2`'s records with `yb` [J]).

No existing statement changed except the root import list.
-/
import Fl4Proofs.P2.ViewSafeIoU8
import Fl4Proofs.P2.ViewSafeObstr
import Fl4Proofs.P2.NarrowSP
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY)
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg NextH VEq SafeStepH XSafeRunH
  serializable_safeXH xsafeRunH_inv allowed_of_sinv Safe narrowSP safe_narrow)

noncomputable section
open Classical

/-! ## The narrowed annotation -/

/-- The view keeps the owner of `x`. -/
def VO (K : KLayoutP) (c : U64) (ρ : U64 → U64) (x : U64) : Prop :=
  ownP K (CoreView.view K.toKLayout c ρ) x = ownP K ρ x

/-- **The start's body re-annotated for the words whose owner the view keeps** (module docstring). -/
def annV (s : Cfg U64 U64 U64 U64) (K : KLayoutP) (c : U64) (ρ : U64 → U64) (k0 : SP) : SP :=
  narrowSP s.cls s.ko c (VO K c ρ) ∅ k0

/-- **[J] The read premise at one start, for the re-annotated body** (module docstring): where core `c`'s view of
`ρ` is not `ρ`, the re-annotation of the body a start of path `i` at the view gives is `Safe` at the physical memory.
Justification: DESIGN §7 as for `VSafe`; the words whose owner the view changes are read racily, as at the physical
memory (U5's annotation). -/
def VSafe9 {ι : Type} (LP : PathsP ι) (s : Cfg U64 U64 U64 U64) (K : KLayoutP) (c : U64) (k0 : SP)
    (hK : RegionOKP K) (hU : UserOKP K) (ρ : U64 → U64) (i : ι) : Prop :=
  CoreView.view K.toKLayout c ρ ≠ ρ →
    StartAt (LP i K (CoreView.view K.toKLayout c ρ) hK hU) c (fun l => s.lk l = some c)
      (CoreView.view K.toKLayout c ρ) k0 →
    Safe s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem (annV s K c ρ k0)

/-- **U8's read premise gives U9's.** -/
theorem vSafe9_of_vSafe {ι : Type} {LP : PathsP ι} {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {c : U64} {k0 : SP}
    {hK : RegionOKP K} {hU : UserOKP K} {ρ : U64 → U64} {i : ι} (h : VSafe LP s K c k0 hK hU ρ i) :
    VSafe9 LP s K c k0 hK hU ρ i :=
  fun hv hP => safe_narrow _ (h hv hP) ∅

/-! ## Not refuted at foreign-homed starts -/

section nonvac
open Fl4Proofs.P2.CoreView (HomeOff ownP_home view_home_rperm)

/-- A home-owned word of a thread homed off `c` in `ρ` is one whose owner the view changes. -/
theorem not_vo_home {K : KLayoutP} (hK : RegionOKP K) {c : U64} {ρ : U64 → U64} {t off : U64}
    (ht : K.heap t = some .tcb) (hoff : HomeOff off) (hf : ρ (fld t oAFFINITY) ≠ c) :
    ¬ VO K c ρ (fld t off) := by
  intro h
  unfold VO at h
  rw [ownP_home hK ht hoff, ownP_home hK ht hoff, CoreView.view_aff hK.base.base ht c ρ] at h
  exact hf (Serial.Owner.core.inj h).symm

/-- The class owner of a home-owned word is never the gate, and is its thread's home core where it is a core. -/
theorem ko_home {K : KLayoutP} (hK : RegionOKP K) {c : U64} {m : U64 → U64} {t off : U64}
    (ht : K.heap t = some .tcb) (hoff : HomeOff off) (hf : m (fld t oAFFINITY) ≠ c) :
    ¬ (OwnMap.ko K.toKLayout m (fld t off) = .gate ∨ OwnMap.ko K.toKLayout m (fld t off) = .core c) := by
  have hr := (hK.base.base.tcb t ht off (Fl4Proofs.P2.CoreView.homeOff_dec hoff)).1
  have e : OwnMap.ko K.toKLayout m (fld t off) =
      if (fld t off).val - t.val = 3328 ∨ (fld t off).val - t.val = 3528 then .core (m (fld t oAFFINITY))
      else .free := by
    simp only [OwnMap.ko, hr]
  rw [e]
  split_ifs <;> intro h <;> rcases h with h | h <;>
    first | exact hf (Serial.ClsOwner.core.inj h) | cases h

/-- **U9's armed read of another core's thread's home-owned word is speculative** (module docstring). -/
theorem u9_home_rds {K : KLayoutP} (hK : RegionOKP K) {s : Cfg U64 U64 U64 U64} {c : U64} {ρ : U64 → U64}
    (hko : s.ko = OwnMap.ko K.toKLayout s.mem) (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout s.mem) c
      (fun l => s.lk l = some c) ρ s.mem)
    {t off : U64} (ht : K.heap t = some .tcb) (hoff : HomeOff off) (hf : ρ (fld t oAFFINITY) ≠ c)
    {Wd : Set U64} (hW : fld t off ∉ Wd) (k : U64 → SP) :
    narrowSP s.cls s.ko c (VO K c ρ) Wd (.rd (fld t off) k) =
      .rds (fld t off) (fun v => narrowSP s.cls s.ko c (VO K c ρ) Wd (k v)) := by
  refine Serial.narrow_rd_rds (not_vo_home hK ht hoff hf) hW ?_
  rw [hko, CoreView.ko_of_veq hK hV]
  exact ko_home hK ht hoff hf

/-- **`Safe` at that read asks nothing of the word** (module docstring; contrast `view_home_rd_unsafe`). -/
theorem u9_home_safe_iff {K : KLayoutP} (hK : RegionOKP K) {s : Cfg U64 U64 U64 U64} {c : U64} {ρ : U64 → U64}
    (hko : s.ko = OwnMap.ko K.toKLayout s.mem) (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout s.mem) c
      (fun l => s.lk l = some c) ρ s.mem)
    {t off : U64} (ht : K.heap t = some .tcb) (hoff : HomeOff off) (hf : ρ (fld t oAFFINITY) ≠ c)
    {Wd : Set U64} (hW : fld t off ∉ Wd) (k : U64 → SP) {μ : U64 → U64} :
    Safe (ownP K) s.cls s.ko c (fun l => s.lk l = some c) μ (narrowSP s.cls s.ko c (VO K c ρ) Wd (.rd (fld t off) k)) ↔
      ∀ μ', Serial.FReach (ownP K) s.cls s.ko c (fun l => s.lk l = some c) μ μ' →
        Safe (ownP K) s.cls s.ko c (fun l => s.lk l = some c) μ'
          (narrowSP s.cls s.ko c (VO K c ρ) Wd (k (μ' (fld t off)))) := by
  rw [u9_home_rds hK hko hV ht hoff hf hW k]
  exact Serial.safe_rds_iff

end nonvac

/-! ## Steps and executions arming the body or its re-annotation -/

/-- **A step of FL4 with rule 8, the start at the core's view, arming the body or its re-annotation.** -/
structure Fl4StepPV9 {ι : Type} (LP : PathsP ι) (s : Cfg U64 U64 U64 U64) (K : KLayoutP) (c : U64)
    (s' : Cfg U64 U64 U64 U64) (K' : KLayoutP) : Prop where
  arm : ∀ p, s'.ph c = .arm p → PureGlue p
  start : ∀ p0 k W, s.ph c = .loc p0 (.start k) W → ∀ (hK : RegionOKP K) (hU : UserOKP K),
    ∃ ρ : U64 → U64, VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem ∧
      ∃ i k0, StartAt (LP i K (CoreView.view K.toKLayout c ρ) hK hU) c (fun l => s.lk l = some c)
        (CoreView.view K.toKLayout c ρ) k0 ∧
        ((k = k0 ∧ VSafe LP s K c k0 hK hU ρ i) ∨ (k = annV s K c ρ k0 ∧ VSafe9 LP s K c k0 hK hU ρ i))
  ser : SerStep s c → RegionOKP K' ∧ UserOKP K' ∧ MapsP K' s'
  keep : ¬ SerStep s c → K' = K

inductive ExecPV9 {ι : Type} (LP : PathsP ι) (s0 : Cfg U64 U64 U64 U64) (K0 : KLayoutP) :
    Cfg U64 U64 U64 U64 → KLayoutP → Prop
  | refl : ExecPV9 LP s0 K0 s0 K0
  | step {s s' : Cfg U64 U64 U64 U64} {K K' : KLayoutP} {c : U64} :
      ExecPV9 LP s0 K0 s K → Step s c s' → Fl4StepPV9 LP s K c s' K' → ExecPV9 LP s0 K0 s' K'
  | hw {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {v a x : U64} :
      ExecPV9 LP s0 K0 s K → HwStepP K s v a x → ExecPV9 LP s0 K0 (hwCfg s a x) K

/-- **An `ExecPV9` is an `XSafeRunH`** (`exec_safeRunPV`; a re-annotated body is `Safe` by `safe_narrow` where the
view is the identity, by `VSafe9` elsewhere). -/
theorem exec_safeRunPV9 {ι : Type} {LP : PathsP ι} {s0 s : Cfg U64 U64 U64 U64}
    {K0 K : KLayoutP} (h0 : Init s0) (hA0 : ArmInv s0) (hK0 : RegionOKP K0)
    (hU0 : UserOKP K0) (hM0 : MapsP K0 s0) (h : ExecPV9 LP s0 K0 s K) :
    ∃ H, XSafeRunH s0 s H ∧ RegionOKP K ∧ UserOKP K ∧ MapsP K s := by
  induction h with
  | refl => exact ⟨s0.mem, .refl, hK0, hU0, hM0⟩
  | @step s s' K K' c _ hst hF ih =>
    obtain ⟨H, hr, hK, hU, hM⟩ := ih
    obtain ⟨-, -, -, hS, -⟩ := xsafeRunH_inv h0 hA0 hr
    refine ⟨NextH s c s' H, .step hr hst ⟨hF.arm, fun p0 k W hph _ => ?_, by rw [hM.own]; exact moveHeldP hK⟩, ?_⟩
    · obtain ⟨ρ, hV, i, k0, hP, hX⟩ := hF.start p0 k W hph hK hU
      have hS0 : CoreView.view K.toKLayout c ρ = ρ →
          Safe s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem k0 := by
        intro hv
        rw [hv] at hP
        have hko := ko_viewP hK hM hV
        rw [hM.own, hM.cls, hko] at hV ⊢
        exact (LP i K ρ hK hU).safeH (moveHeldP hK) (ownDepP hK hU) hP hV
      rcases hX with ⟨rfl, hX⟩ | ⟨rfl, hX⟩
      · by_cases hv : CoreView.view K.toKLayout c ρ = ρ
        · exact hS0 hv
        · exact hX hv hP
      · by_cases hv : CoreView.view K.toKLayout c ρ = ρ
        · exact safe_narrow _ (hS0 hv) ∅
        · exact hX hv hP
    · by_cases hs : SerStep s c
      · exact hF.ser hs
      · rw [hF.keep hs]
        exact ⟨hK, hU, maps_stepP hK hM (allowed_of_sinv hS c) hst hs⟩
  | hw _ hh ih =>
    obtain ⟨H, hr, hK, hU, hM⟩ := ih
    refine ⟨Function.update H _ _, .hw hr (hh.hwWr hK hM) fun m => ?_, hK, hU, maps_hwP hK hM hh⟩
    rw [hM.own]
    exact ownP_upd_nondec hK (OwnMapV.vcpu_nondec hK.base (hh.vcpu hK.base).1) _ _

theorem serializable_e2ePV9 {ι : Type} (LP : PathsP ι) {s0 s : Cfg U64 U64 U64 U64}
    {K0 K : KLayoutP} (h0 : Init s0) (hA0 : ArmInv s0) (hK0 : RegionOKP K0)
    (hU0 : UserOKP K0) (hM0 : MapsP K0 s0) (h : ExecPV9 LP s0 K0 s K) (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  obtain ⟨H, hr, -⟩ := exec_safeRunPV9 h0 hA0 hK0 hU0 hM0 h
  exact serializable_safeXH h0 hA0 hr hq

/-! ## The chain-level step (U8's, arming the body or its re-annotation) -/

section exec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {ι : Type}

/-- **A step of FL4 as in U8, the armed program the start's body or its re-annotation** (module docstring). -/
structure Fl4StepWPRV9 (LP : PathsP ι) (NoV : ι → Prop)
    (SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop)
    (P : LocPlat st arI AR MR) (s : Cfg U64 U64 U64 U64) (K : KLayoutP) (Ch : U64 → S → Prop) (c : U64)
    (s' : Cfg U64 U64 U64 U64) (K' : KLayoutP) (Ch' : U64 → S → Prop) : Prop where
  /-- [P] an armed program is pure glue. -/
  arm : ∀ p, s'.ph c = .arm p → PureGlue p
  /-- [P] the glue's start fact at `c`'s view for the body `k0`; the armed program is `k0` with `VSafe` [J] or its
  re-annotation with `VSafe9` [J], both only for paths with `NoV`. -/
  start : ∀ p0 k W, s.ph c = .loc p0 (.start k) W → ∀ (hK : RegionOKP K) (hU : UserOKP K),
    ∃ ρ : U64 → U64, VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem ∧
      ∃ i k0, SF (Ch c) K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k0 i ∧
        ((k = k0 ∧ (NoV i → VSafe LP s K c k0 hK hU ρ i)) ∨
          (k = annV s K c ρ k0 ∧ (NoV i → VSafe9 LP s K c k0 hK hU ρ i)))
  /-- [P] the serial exit's ghost choice, one P3 chain per core. -/
  serX : SerStep s c → ∀ e, SerExitW P K'.toKLayoutV (Ch' e)
  /-- The glue's layout convention at the serial exit. -/
  serC : SerStep s c → K'.vcpus = ∅ ∧ K'.ptes = ptesR K' s'.mem
  /-- [P] the exit ghost with rule 8. -/
  serG : SerStep s c → MapsP K' s'
  /-- Layout and chains change only at serial steps. -/
  keep : ¬ SerStep s c → K' = K ∧ Ch' = Ch

inductive ExecWPRV9 (LP : PathsP ι) (NoV : ι → Prop)
    (SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop)
    (P : LocPlat st arI AR MR) (s0 : Cfg U64 U64 U64 U64) (K0 : KLayoutP) (Ch0 : U64 → S → Prop) :
    Cfg U64 U64 U64 U64 → KLayoutP → (U64 → S → Prop) → Prop
  | refl : ExecWPRV9 LP NoV SF P s0 K0 Ch0 s0 K0 Ch0
  | step {s s' : Cfg U64 U64 U64 U64} {K K' : KLayoutP} {Ch Ch' : U64 → S → Prop} {c : U64} :
      ExecWPRV9 LP NoV SF P s0 K0 Ch0 s K Ch → Step s c s' → Fl4StepWPRV9 LP NoV SF P s K Ch c s' K' Ch' →
      ExecWPRV9 LP NoV SF P s0 K0 Ch0 s' K' Ch'
  | hw {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {Ch : U64 → S → Prop} {v a x : U64} :
      ExecWPRV9 LP NoV SF P s0 K0 Ch0 s K Ch → HwStepP K s v a x → ExecWPRV9 LP NoV SF P s0 K0 Ch0 (hwCfg s a x) K Ch

/-- **Every U8 execution is a U9 one** (armed program the start's body). -/
theorem execWPRV9_of_WPRV8 {LP : PathsP ι} {NoV : ι → Prop}
    {SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop}
    {P : LocPlat st arI AR MR} {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop}
    (h : ExecWPRV8 LP NoV SF P s0 K0 Ch0 s K Ch) : ExecWPRV9 LP NoV SF P s0 K0 Ch0 s K Ch := by
  induction h with
  | refl => exact .refl
  | step _ hS g ih =>
    refine .step ih hS ⟨g.arm, fun p0 k W hph hK hU => ?_, g.serX, g.serC, g.serG, g.keep⟩
    obtain ⟨ρ, hV, i, hi, hvs⟩ := g.start p0 k W hph hK hU
    exact ⟨ρ, hV, i, k, hi, Or.inl ⟨rfl, hvs⟩⟩
  | hw _ hH ih => exact .hw ih hH

/-- **An `ExecWPRV9` is an `ExecPV9`** (`execPV_of_WPRV8`; the starts without `NoV` get `VSafe` from `hVS`, and
`VSafe9` from it). -/
theorem execPV9_of_WPRV9 {LP : PathsP ι} {NoV : ι → Prop}
    {SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop}
    (hSF : ∀ (Ch : S → Prop) (K : KLayoutP) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K) c hs q i,
      (∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) → EpochPteN K s.mem →
      SF Ch K s.mem hK hU c hs q i → StartAt (LP i K s.mem hK hU) c hs s.mem q)
    (hVS : ∀ (s : Cfg U64 U64 U64 U64) (K : KLayoutP) (hK : RegionOKP K) (hU : UserOKP K) c k ρ i, MapsP K s →
      VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem → ¬ NoV i → VSafe LP s K c k hK hU ρ i)
    (P : LocPlat st arI AR MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : ∀ e, SerExitW P K0.toKLayoutV (Ch0 e)) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0) (h : ExecWPRV9 LP NoV SF P s0 K0 Ch0 s K Ch) :
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
          · exact hvs hn
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

/-! ## U9 -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **FL4 end to end, U8 with the armed body optionally re-annotated** (module docstring). The conclusion is about
the physical memory. `VSafe` / `VSafe9` [J] stay for the non-io slots. -/
theorem serializable_fl4_localU9 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : ∀ e, SerExitW P K0.toKLayoutV (Ch0 e)) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPRV9 (PathsP.sum (fl4LocW11JA st ar hA (masksWr_plain st) L.total a0)
        (PathsP.sum (PathsP.sum (delPteSlot st ar hA (masksWr_plain st)) (invSlotU st ar hA (masksWr_plain st)))
          (cmSlotU st ar hA (masksWr_plain st))))
      (fun i => ¬ IoIx (S := S) i) (StartV2 st ar hA a0 arI AR MR) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  obtain ⟨hK0, hU0⟩ := okP_R (hB 0#u64) hc0
  refine serializable_e2ePV9 _ h0 hA0 hK0 hU0 hM0 (execPV9_of_WPRV9 ?_ ?_ P h0 hA0 hB hc0 hM0 h).1 hq
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

/-- **U8 follows from U9** (every U8 execution is a U9 one). -/
theorem serializable_fl4_localU8of9 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : ∀ e, SerExitW P K0.toKLayoutV (Ch0 e)) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPRV8 (PathsP.sum (fl4LocW11JA st ar hA (masksWr_plain st) L.total a0)
        (PathsP.sum (PathsP.sum (delPteSlot st ar hA (masksWr_plain st)) (invSlotU st ar hA (masksWr_plain st)))
          (cmSlotU st ar hA (masksWr_plain st))))
      (fun i => ¬ IoIx (S := S) i) (StartV2 st ar hA a0 arI AR MR) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_fl4_localU9 st ar hA a0 P hIoa h0 hA0 hB hc0 hM0 (execWPRV9_of_WPRV8 h) hq

end top

end
end Fl4Proofs.P2.E2EP
