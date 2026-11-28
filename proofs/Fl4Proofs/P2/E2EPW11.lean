/-
P2 (line pte, gen 7): **`serializable_fl4_localW11P`**, the PTE-avoiding version of iolay gen 3's top
`serializable_fl4_localW11`: the same family (`fl4LocP3W6`'s eight slots), the same glue form (`ExecW`-style steps
with `SerExitW` [P], `VcpuLay` [J], start facts `StartP3W11` [P]), ownership `ownP` with **`K.ptes` arbitrary**,
the PTE facts as nscope gen 3's start-state predicate `QPs` (`E2EPJW`, `E2EPJW5`).

* **`allW11J`**: every path of `fl4LocP3W6`, restricted to `QPs` states (`LocalPath.rJ`), reads no PTE word, with no
  premise (nscope's `allJ5` ported to W6's family). vmF, vmR, io, st, irq and vx are `fl4LocP3W`'s slots, so their
  `*_avoidPJ` are reused as they are. The two slots whose path differs are redone:
  - **sl** at `sl_pathsKC7` (`sl_avoidPJ_W6`): the same `sl_avoidVKE_rQ` argument as `sl_avoidPJ`, through
    `slSlotK7` / `sl_pathsKC7` / `sl_pathsKC6` down to `sl_pathsK` (the `ReadOnce` component is `sl_hro` with
    `sl_rr_once` and is not used by the avoidance proof).
  - **vt** at `vtSlotP3W5` (`vt_avoidPJ_W5`): `vtSlotP3W5`'s path is `vtSlotP3`'s at the record `VtPremP5.toP3`
    (`SlotN.pullK`, by definition), so `vt_avoidPJ_path` applies.
* **`fl4LocW11J`**: those paths PTE-cut and lifted to `ownP` (`LocalPath.cutLiftP`).
* **Steps** `Fl4StepWP` / **`ExecWP`**: `Fl4StepW` over `KLayoutP` with two rule-8 glue fields: `serP` [P] (the serial
  exit's PTE choice `K'.ptes` is as `PteLay` says: region `.none`, in no VCPU, aligned non-user words; the intended
  choice is `K'.ptes ⊆ ptesJ Zx'`, nscope's) and `serG` [P] (the exit ghost is `ownP K'`'s, `MapsP`); hardware
  steps `HwStepP`. `execP_of_WP`: an `ExecWP` is an `ExecP`.
* **Starts** `StartP3W11J`: the W11 start fact `StartP3W11` [P] at `K.toKLayoutV` for a program `q0`, together with
  **`StartQP` [P]**. At every state the start describes (the `ownV` path's `Pre`, core, locks, model memory on
  aligned non-user words, body `q0`):
  - `QPs K st σ` holds. This is the glue's start fact "QPs at each start" (nscope `E2EPJW` module docstring: true
    at every start of the epoch for the choice `K.ptes ⊆ ptesJ Zx'`; nscope gen 4 is formalising the carry lemma).
    `QPs` reads `L.ksb σ` and the ASID-table words only, which are aligned non-user words, so the model memory
    pins them.
  - The armed program `q` is the restricted, PTE-cut path's body at that state and Arch state. This is the program
    annotation `StartAt` already uses: the cut path classifies PTE reads as racy, so its body is not `q0`.
  `startAtP_W11`: `StartP3W11J` ⇒ `StartAt` of `fl4LocW11J` (from `startAt_P3W11`).
* **`serializable_fl4_localW11P`**.

Premises beyond `serializable_fl4_localW11`'s: the boot layout's `PteLay` [P] and `MapsP`, per serial step `serP` /
`serG` [P], and per start `StartQP` [P]. **No [W], and no PTE-line [J]**: `PteSl`, `VtmP`, `VxP` and `vmP` are not
used. No existing statement or file changed. `kernel_entry_reach*` is untouched.
-/
import Fl4Proofs.P2.E2EPJW5
import Fl4Proofs.P2.E2EVFl4W11
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld)
open Fl4Proofs.P2.E2E (StartAt SP SerStep)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg)

noncomputable section
open Classical

/-! ## The two redone slots and `allW11J` -/

section slots
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)

/-- **syscall_local at `sl_pathsKC7` under `QPs`** (W6's sl slot; `sl_avoidPJ`'s argument). -/
theorem sl_avoidPJ_W6 (i : SlArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (h : (slSlotP3W6 st ar hA hm hSt a0).Prem i K.toKLayoutV m) :
    AvoidP K (((slSlotP3W6 st ar hA hm hSt a0).lift (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base).rJ K
      (fun b hb => Or.inl hb)) := by
  have key : ∀ (P : E2E.LocalPath (OwnMap.own K.toKLayout) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m)
      (· ∈ K.user)) (W : AvoidV K.toKLayoutV P),
      P = (slSlotP3W6 st ar hA hm hSt a0).path i K.toKLayoutV m hK.base hU.base h →
      AvoidP K ((LocalPath.cutLiftV hK.base hU.base (fun x ⟨_, hv, _⟩ => ko_vcpu hK.base hv m) P W).rJ K
        (fun b hb => Or.inl hb)) := by
    rintro P W rfl
    apply avoidE_cutLiftV_rJ hK.base hU.base h.1
    dsimp only [slSlotP3W6, SlotC.ofP3, SlotC.pull, slSlotK7]
    dsimp only [sl_pathsKC7, sl_pathsKC6, sl_pathsKC5, sl_pathsKC4, sl_pathsKF, sl_pathsKU, sl_pathsK]
    exact sl_avoidVKE_rQ ar hSt hA hm a0 (regionOKE_pte hK) hU.base.base (fun _ h' => h'.1) _ _ _ _ _ _ _ _
      (fun s _ hq => QPs.ks (L := L) hq) (fun s _ hq => QPs.tab (L := L) hq) (userNoE_pte hU)
  exact key _ _ (SlotC.fam_pos _ _ h)

end slots

/-! ## The glue form with rule 8 -/

/-- **`PteLay K`** [P] (the serial exit's PTE choice): PTE words are region `.none`, in no VCPU, aligned non-user
words (P1 `HeapOK`). With `RegionOKV` / `UserOKV` it gives `RegionOKP` / `UserOKP`. -/
def PteLay (K : KLayoutP) : Prop :=
  (∀ e ∈ K.ptes, region K.toKLayout e = .none) ∧ (∀ e ∈ K.ptes, ¬ ∃ v, InVcpu K.toKLayoutV v e) ∧
    (∀ e ∈ K.ptes, Aligned e ∧ e ∉ K.user)

section exec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {ι : Type}

/-- **A step of FL4 with the glue premises named, rule 8** (`Fl4StepW` over `KLayoutP`; module docstring). -/
structure Fl4StepWP (LP : PathsP ι)
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
  /-- [J] the new layout's VCPU facts (vacuous at `K'.vcpus = ∅`). -/
  serV : SerStep s c → VcpuLay L K'.toKLayoutV
  /-- [P] the serial exit's PTE choice (intended: `K'.ptes ⊆ ptesJ Zx'` of the exit's bundle ghost). -/
  serP : SerStep s c → PteLay K'
  /-- [P] the exit ghost with rule 8. -/
  serG : SerStep s c → MapsP K' s'
  /-- Layout and chain change only at serial steps. -/
  keep : ¬ SerStep s c → K' = K ∧ Ch' = Ch

/-- **An execution of FL4 with the glue premises named, rule 8.** -/
inductive ExecWP (LP : PathsP ι)
    (SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop)
    (P : LocPlat st arI AR MR) (s0 : Cfg U64 U64 U64 U64) (K0 : KLayoutP) (Ch0 : S → Prop) :
    Cfg U64 U64 U64 U64 → KLayoutP → (S → Prop) → Prop
  | refl : ExecWP LP SF P s0 K0 Ch0 s0 K0 Ch0
  | step {s s' : Cfg U64 U64 U64 U64} {K K' : KLayoutP} {Ch Ch' : S → Prop} {c : U64} :
      ExecWP LP SF P s0 K0 Ch0 s K Ch → Step s c s' → Fl4StepWP LP SF P s K Ch c s' K' Ch' →
      ExecWP LP SF P s0 K0 Ch0 s' K' Ch'
  | hw {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {Ch : S → Prop} {v a x : U64} :
      ExecWP LP SF P s0 K0 Ch0 s K Ch → HwStepP K s v a x → ExecWP LP SF P s0 K0 Ch0 (hwCfg s a x) K Ch

end exec

/-! ## The start fact and the top -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop) (MR : A3 → Fl4Spec.MachineState → Prop)

variable {arI AR MR}

end top

end
end Fl4Proofs.P2.E2EP
