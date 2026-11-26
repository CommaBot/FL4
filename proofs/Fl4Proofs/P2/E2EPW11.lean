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

/-- **The VM timer at `vtSlotP3W5` under `QPs`** (W5's vt slot: `vtSlotP3`'s path at `VtPremP5.toP3`). -/
theorem vt_avoidPJ_W5 (i : VtArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (h : (vtSlotP3W5 st ar hA hm).Prem i K.toKLayoutV m) :
    AvoidP K (((vtSlotP3W5 st ar hA hm).fam (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base).rJ K
      (fun b hb => Or.inl hb)) := by
  have key : ∀ P, P = (vtSlotP3W5 st ar hA hm).path i K.toKLayoutV m hK.base hU.base h →
      AvoidP K (P.rJ K (fun b hb => Or.inl hb)) := by
    rintro P rfl
    exact vt_avoidPJ_path st ar hA hm i K m hK hU (VtPremP5.toP3 st ar hA hm hK.base h)
  exact key _ (SlotN.fam_pos _ _ h)

/-- **Every path of `fl4LocP3W6`, restricted to `QPs` states, reads no PTE word** (no premise; `allJ5` on W6's
family). -/
theorem allW11J :
    ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K),
      AvoidP K ((((fl4LocP3W6 st ar hA hm hSt a0).paths (fl4Dflt st ar hm)) i K.toKLayoutV m hK.base hU.base).rJ K
        (fun b hb => Or.inl hb)) := by
  intro i K m hK hU
  by_cases he : K.ptes = ∅
  · exact avoidP_empty he _
  cases i with
  | vmF i =>
    by_cases hp : (fl4LocP3W6 st ar hA hm hSt a0).vmF.Prem i K.toKLayoutV m
    · exact vmF_avoidPJ st ar hA hm i K m hK hU hp
    · exact avoidE_restrQ_noPre (SlotU.noPre (fl4Dflt st ar hm) _ hp)
  | vmR i =>
    by_cases hp : (fl4LocP3W6 st ar hA hm hSt a0).vmR.Prem i K.toKLayoutV m
    · exact vmR_avoidPJ st ar hA hm i K m hK hU hp
    · exact avoidE_restrQ_noPre (SlotU.noPre (fl4Dflt st ar hm) _ hp)
  | io i =>
    by_cases hp : (fl4LocP3W6 st ar hA hm hSt a0).io.Prem i K.toKLayoutV m
    · exact io_avoidPJ st ar hA hm i K m hK hU hp
    · exact avoidE_restrQ_noPre (SlotU.noPre (fl4Dflt st ar hm) _ hp)
  | st i =>
    by_cases hp : (fl4LocP3W6 st ar hA hm hSt a0).st.Prem i K.toKLayoutV m
    · exact stm_avoidPJ st ar hA hm i K m hK hU hp
    · exact avoidE_restrQ_noPre (SlotU.noPre (fl4Dflt st ar hm) _ hp)
  | irq i =>
    by_cases hp : (fl4LocP3W6 st ar hA hm hSt a0).irq.Prem i K.toKLayoutV m
    · exact irq_avoidPJ st ar hA hm i K m hK hU hp
    · exact avoidE_restrQ_noPre (SlotU.noPre (fl4Dflt st ar hm) _ hp)
  | sl i =>
    by_cases hp : (fl4LocP3W6 st ar hA hm hSt a0).sl.Prem i K.toKLayoutV m
    · exact sl_avoidPJ_W6 st ar hA hm hSt a0 i K m hK hU hp
    · exact avoidE_restrQ_noPre (SlotC.noPre (fl4Dflt st ar hm) _ hp)
  | vq j =>
    cases j with
    | inl i =>
      by_cases hp : (vxSlotP3 st ar hA hm).Prem i K.toKLayoutV m
      · exact vx_avoidPJ st ar hA hm i K m hK hU hp
      · exact avoidE_restrQ_noPre (SlotN.noPre (fl4Dflt st ar hm) _ hp)
    | inr i =>
      by_cases hp : (vtSlotP3W5 st ar hA hm).Prem i K.toKLayoutV m
      · exact vt_avoidPJ_W5 st ar hA hm i K m hK hU hp
      · exact avoidE_restrQ_noPre (SlotN.noPre (fl4Dflt st ar hm) _ hp)

/-- **W6's eight local paths, each restricted to `QPs` states, PTE-cut and lifted to `ownP`** (no premise). -/
def fl4LocW11J : PathsP (Fl4IxW (S := S)) :=
  fun i K m hK hU => LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx m) _
    (allW11J st ar hA hm hSt a0 i K m hK hU)

end slots

/-! ## The glue form with rule 8 -/

/-- **`PteLay K`** [P] (the serial exit's PTE choice): PTE words are region `.none`, in no VCPU, aligned non-user
words (P1 `HeapOK`). With `RegionOKV` / `UserOKV` it gives `RegionOKP` / `UserOKP`. -/
def PteLay (K : KLayoutP) : Prop :=
  (∀ e ∈ K.ptes, region K.toKLayout e = .none) ∧ (∀ e ∈ K.ptes, ¬ ∃ v, InVcpu K.toKLayoutV v e) ∧
    (∀ e ∈ K.ptes, Aligned e ∧ e ∉ K.user)

theorem PteLay.ok {K : KLayoutP} (h : PteLay K) (hK : RegionOKV K.toKLayoutV) (hU : UserOKV K.toKLayoutV) :
    RegionOKP K ∧ UserOKP K :=
  ⟨⟨hK, h.1, h.2.1⟩, ⟨hU, h.2.2⟩⟩

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

/-- **An `ExecWP` is an `ExecP`**: `Fl4StepP.ser` from `serExitW_ok`, `PteLay` and the exit ghost, `start` from the
family's start callback at the current chain. -/
theorem execP_of_WP {LP : PathsP ι}
    {SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop}
    (hSF : ∀ (Ch : S → Prop) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) c hs q i,
      (∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) → SF Ch K m hK hU c hs q i →
        StartAt (LP i K m hK hU) c hs m q)
    {P : LocPlat st arI AR MR} {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop}
    (hB : SerExitW P K0.toKLayoutV Ch0) (h : ExecWP LP SF P s0 K0 Ch0 s K Ch) :
    ExecP LP s0 K0 s K ∧ SerExitW P K.toKLayoutV Ch := by
  induction h with
  | refl => exact ⟨.refl, hB⟩
  | @step s1 s1' K1 K1' Ch1 Ch1' c1 _ hS g ih =>
    obtain ⟨hE, hX⟩ := ih
    refine ⟨.step hE hS ⟨g.arm, fun p0 k W hph hK hU => ?_, fun hs => ?_, fun hn => (g.keep hn).1⟩, ?_⟩
    · obtain ⟨i, hi⟩ := g.start p0 k W hph hK hU
      exact ⟨i, hSF _ _ _ _ _ _ _ _ i hX.chainOf hi⟩
    · have hok := serExitW_ok (g.serX hs) (g.serV hs)
      have hP := (g.serP hs).ok hok.1 hok.2
      exact ⟨hP.1, hP.2, g.serG hs⟩
    · by_cases hs : SerStep s1 c1
      · exact g.serX hs
      · obtain ⟨e1, e2⟩ := g.keep hs
        rw [e1, e2]; exact hX
  | hw _ hH ih => exact ⟨.hw ih.1 hH, ih.2⟩

end exec

/-! ## The start fact and the top -/

/-- **`StartQP`** [P] (module docstring): at every state `σ` and Arch state `a` at which the glue starts the `ownV`
path `Pv` as `q0` (its `Pre`, core `c`, locks `hs`, model memory `μ` on aligned non-user words, body `q0`), the PTE
facts `QPs K st σ` hold, and the armed program `q` is the body of `Pp` (the restricted, PTE-cut path) there. -/
def StartQP {own own' : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
    {ko : U64 → Serial.ClsOwner U64} {User : U64 → Prop} (K : KLayoutP)
    (Pv : E2E.LocalPath own cls ko User) (Pp : E2E.LocalPath own' cls ko User) (hS : Pv.S = Pp.S)
    (hA : Pv.A = Pp.A) (c : U64) (hs : U64 → Prop) (μ : U64 → U64) (q0 q : SP) : Prop :=
  ∀ (σ : Pv.S) (a : Pv.A), Pv.Pre σ → Pv.L.cpu σ = c → Pv.Locks σ = hs →
    (∀ x, Aligned x → ¬ User x → Pv.L.mem σ x = μ x) → q0 = Pv.body σ a →
    QPt K Pv σ ∧ q = Pp.body (cast hS σ) (cast hA a)

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop) (MR : A3 → Fl4Spec.MachineState → Prop)

/-- **The W11 start fact with rule 8**: `StartP3W11` [P] at the `ownV` layout for some `q0`, and `StartQP` [P]
(`QPs` at the start state; the armed program is the cut path's body). -/
def StartP3W11J (Ch : S → Prop) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K)
    (hU : UserOKP K) (c : U64) (hs : U64 → Prop) (q : SP) (i : Fl4IxW (S := S)) : Prop :=
  ∃ q0, StartP3W11 st ar hA hm hSt a0 arI AR MR Ch K.toKLayoutV m hK.base hU.base c hs q0 i ∧
    StartQP K ((fl4LocP3W6 st ar hA hm hSt a0).paths (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base)
      (fl4LocW11J st ar hA hm hSt a0 i K m hK hU) rfl rfl c hs m q0 q

variable {arI AR MR}

/-- **`StartAt` of `fl4LocW11J` from `StartP3W11J`**, given the current chain. -/
theorem startAtP_W11 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR) {Ch : S → Prop}
    {K : KLayoutP} (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch)
    {m : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {hs : U64 → Prop} {q : SP}
    {i : Fl4IxW (S := S)} (h : StartP3W11J st ar hA hm hSt a0 arI AR MR Ch K m hK hU c hs q i) :
    StartAt (fl4LocW11J st ar hA hm hSt a0 i K m hK hU) c hs m q := by
  obtain ⟨q0, hW, hQ⟩ := h
  obtain ⟨σ, a, hP, hc, hl, hμ, e⟩ := startAt_P3W11 st ar hA hm hSt a0 P hIoa hC hW
  obtain ⟨hq, hb⟩ := hQ σ a hP hc hl hμ e
  exact ⟨σ, a, ⟨hP, hq⟩, hc, hl, hμ, hb⟩

/-- **FL4 end to end, W11's family and glue, ownership with rule 8, `K.ptes` arbitrary, no [W] and no PTE-line
[J]** (module docstring): every `ExecWP` over `fl4LocW11J` whose starts are `StartP3W11J` facts, from a boot layout
with no VCPU whose PTE choice satisfies `PteLay`, at a state with no local path in progress, ran exactly as some
serial order of its completed entries. -/
theorem serializable_fl4_localW11P (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP}
    {Ch0 Ch : S → Prop} (h0 : Init s0) (hA0 : ArmInv s0) (hB : SerExitW P K0.toKLayoutV Ch0) (nv0 : K0.vcpus = ∅)
    (hP0 : PteLay K0) (hM0 : MapsP K0 s0)
    (h : ExecWP (fl4LocW11J st ar hA hm hSt a0) (StartP3W11J st ar hA hm hSt a0 arI AR MR) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  have hE := (execP_of_WP (fun _ _ _ _ _ _ _ _ _ hC hi => startAtP_W11 st ar hA hm hSt a0 P hIoa hC hi) hB h).1
  have hok := serExitW_ok hB (vcpuLay_empty nv0)
  have hok' := hP0.ok hok.1 hok.2
  exact serializable_e2eP _ h0 hA0 hok'.1 hok'.2 hM0 hE hq

end top

end
end Fl4Proofs.P2.E2EP
