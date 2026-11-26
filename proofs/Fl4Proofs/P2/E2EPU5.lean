/-
# P2 (line glue, gen 2): `serializable_fl4_localU5` — the start fact at any memory the starting core cannot tell from the physical one

Gen 1 (`E2EPU4`) moved every start fact of U2 from the physical memory `s.mem` to Serial's serial-prefix memory
`H`. Its remaining start [P] (`ExecWPRH.start`) then says: `H`, on aligned kernel words, is a state of the epoch's
P3 chain carrying the slot's record facts. Gen 2 tried to derive the chain part of it by induction on the execution
(handoff "What remains" item 1). Findings, per case:

* **Decline** (`leave` of a declined run): `H' = mix W s.mem H` with the decline's writes (`FAULT_IP` of the
  current thread, `update_timestamp`'s `CUR_TIME` / `CONSUMED` of the core's node: `AccessIoDecA` `IoDS`,
  `AccessLvmSets`). `Ch` is a `JReachSt` set, whose only constructors are the epoch's serial exit and accepted
  local runs (`LocAll`, which leaves declines out by design: U29D, `SlJStLocTop` module docstring); `JReachU17`
  itself has only complete kernel entries as steps (`JReachU`). The post-decline memory is a mid-entry memory (the
  general entry the decline falls back to runs later, under the gate), so no lemma puts it in `Ch`, and closure of
  `JReachU17` under those writes is not the question that matters: membership in `JReachSt` would need a `loc`
  step that does not exist. **So U4's start [P] is not derivable after a decline, and is doubtful there**: a core
  `c` starting between core `d`'s decline and `d`'s serial body is asked for a chain state agreeing with `d`'s
  fresh `FAULT_IP` / `CUR_TIME` / `CONSUMED`.
  What `c` can see does not include those words: they are core `d`'s (`own`: a core owns its node and its
  threads), and `c` reads only words it holds or the gate owns. This is what U5 uses: the start fact may be stated
  at any memory `ρ` that `c` cannot tell from the physical memory (`VEq`, gen 1's view relation), e.g. the prefix
  memory with the pending declines' writes left out (`veq_offCore`).
* **Accepted local run**: not derivable from the premises; three gaps, none closable here.
  (G1) No lemma links Serial's sequential meaning `Run (body σ a) μ μ'` (speculative reads returning any value,
  `tr`) to the store-level result of the path's `F` (`IsProgOn` + `ReadOnce` + `PathObl.acc` would be the
  ingredients; no such adequacy theorem exists in the repo).
  (G2) P3's closure clauses (`loc_chain_all` 2–10) are about `F` run with the arch state `a` of a `JReachSt`
  triple `(σ, a, τ)`; `GlueAt`'s body arch state `a` is quantified separately from `Ent σ` (`∃ σ a, Ent σ ∧ … ∧
  q = body σ a`), so the body's result need not be any chain triple's `Loc` successor (the body's `CUR_TIME` write
  is the arch clock of `a`).
  (G3) `LocInv.sim` gives the run from the prefix memory at *completion*, while the start fact's `σ` matches the
  prefix memory at *start*; bridging needs `Ch` to be closed under other cores' completed runs at a state of core
  `c` holding `hs` (`cpu` and `Locks` are part of the store state), which is no P3 fact.
* **Serial exit**: audU F3.3 confirmed: `SerExitW P K Ch` is `∃ σe a3 τ (hJ : JReachU17 σe a3 τ), chainC P hJ =
  (K, Ch)`, with no link between `σe` and `s'.mem`. The honest form would add `∀ x, Aligned x → x ∉ K.user →
  L.mem σe x = s'.mem x` (the serial gate's body *is* a P3 kernel entry, ending in `σe`). It is **not** added:
  with G1–G3 open it would discharge nothing, so it would only strengthen a [P].

So the chain part cannot be discharged. What this module does instead is **narrow the start [P]**:

* `Fl4StepWPRR` / `ExecWPRR`: `Fl4StepWPR` / `ExecWPR` with
  `start : ∃ ρ, VEq s.own s.cls s.ko c hs ρ s.mem ∧ ∃ i, SF Ch K ρ hK hU c hs k i` — the slot's start fact at
  **some** memory `ρ` the starting core cannot tell from the physical memory: owners of the words it may access
  agree, values of the words it may read agree, classes of the words whose class only the gate or `c` changes
  agree. No ghost index: `H` is only used inside the proof.
* **`serializable_fl4_localU5`**: U2's / U4's family, start facts `StartV2`, U2's `hSF` proof verbatim, on
  `ExecWPRR`. Soundness: `exec_safeRunPR` (the body from `σ ≈ ρ` is `Safe` at `s.mem` by `E2E.LocalPath.safeH`,
  the class owners at `ρ` are the configuration's by `ko_congrP` because `ρ` is the memory on gate words) into
  gen 1's `SerialH.XSafeRunH` (the start's `VEq H s.mem` argument unused), then `serializable_safeXH`.
* Coverage (item 2): **`execWPRR_of_WPR`** (every U2 execution is a U5 execution: `ρ := s.mem`),
  **`execWPRR_of_WPRH`** (every U4 execution is a U5 execution: `ρ := H`, `VEq` by `SerialH.veq_start`).
  U4 versus U2: **`execWPRH_of_WPRQ`**: a U2 execution whose every start happens with no local path having written
  (`QuietStart`) is a U4 execution (there `H = s.mem`, `InvH.agree`). Unrestricted `U2 ⊆ U4` is not derivable:
  at a start where another core has written (`H ≠ s.mem`), U2's fact is at `s.mem` and U4's at `H`, and `StartV2`
  depends on the memory (records, `GlueAt`'s memory clause, `ko`); those are exactly the starts audU F1 found U2's
  fact false at. U5 contains both, unconditionally.

## Premises (vs `serializable_fl4_localU4`)
* **Narrowed** — `ExecWPRR.start` [P] (was `ExecWPRH.start` [P]): U4's fact is the instance `ρ := H` (proved:
  `execWPRR_of_WPRH`), U2's the instance `ρ := s.mem` (`execWPRR_of_WPR`). Same platform fact: fl4-sync's glue
  reads physical memory only on the starting core's view (its held words and the gate's, `Allowed`), so what the
  glue's checks establish is a statement about any memory agreeing with the physical one there; the [P] says that
  some such memory is a P3 chain state with the slot's records. Unlike U4's, it is not asked to agree with other
  cores' pending declined writes (they are theirs).
* Removed: none. Added: none (no new [J] / [P] / [W]). `veq_offCore` is a lemma, not a premise.
* Unchanged: `P : LocPlat`, `hIoa`, `h0`, `hA0`, `hB`, `hc0`, `hM0`, `arm` [P], `serX` [P], `serC`, `serG` [P],
  `keep`, `HwStepP`, `hq`, the slot records inside `StartV2`, `yb` [J].

No per-path obligation re-proved; no existing statement or file changed except the root import list.
-/
import Fl4Proofs.P2.E2EPU4
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.Serial

section veq
variable {A V C L : Type}

/-- **A memory that differs from `μ` only on other cores' words is one core `c` cannot tell from `μ`** (module
docstring, the decline case): owners agree everywhere, a value differs only where another core owns the word, and
classes agree on the words whose class only the gate or `c` changes. -/
theorem veq_offCore {own : (A → V) → A → Owner C L} {cls : A → V → V} {ko : A → ClsOwner C} {c : C}
    {hs : L → Prop} {ρ μ : A → V} (hown : ∀ x, own ρ x = own μ x)
    (hval : ∀ y, ρ y ≠ μ y → ∃ e, e ≠ c ∧ own μ y = .core e)
    (hcls : ∀ y, (ko y = .gate ∨ ko y = .core c) → cls y (ρ y) = cls y (μ y)) :
    VEq own cls ko c hs ρ μ := by
  refine ⟨fun x _ => (hown x).symm, fun y hy => ?_, hcls⟩
  by_contra hne
  obtain ⟨e, hec, he⟩ := hval y hne
  rw [he] at hy
  rcases hy with h | h
  · exact hec h
  · cases h

end veq
end Fl4Proofs.P2.Serial

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld)
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg NextH VEq SafeStepH XSafeRunH
  serializable_safeXH xsafeRunH_inv xsafeRunH_agree allowed_of_sinv veq_start)

noncomputable section
open Classical

/-! ## Steps and executions with the start at a view-equal memory -/

/-- **A step of FL4 with rule 8, the start at a memory the core cannot tell from the physical one** (module
docstring): `Fl4StepPH` with `start` [P] asked at some `ρ` with `VEq … ρ s.mem`. -/
structure Fl4StepPR {ι : Type} (LP : PathsP ι) (s : Cfg U64 U64 U64 U64) (K : KLayoutP) (c : U64)
    (s' : Cfg U64 U64 U64 U64) (K' : KLayoutP) : Prop where
  arm : ∀ p, s'.ph c = .arm p → PureGlue p
  start : ∀ p0 k W, s.ph c = .loc p0 (.start k) W → ∀ (hK : RegionOKP K) (hU : UserOKP K),
    ∃ ρ : U64 → U64, VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem ∧
      ∃ i, StartAt (LP i K ρ hK hU) c (fun l => s.lk l = some c) ρ k
  ser : SerStep s c → RegionOKP K' ∧ UserOKP K' ∧ MapsP K' s'
  keep : ¬ SerStep s c → K' = K

/-- **An execution of FL4 with rules 7 and 8, starts at view-equal memories.** -/
inductive ExecPR {ι : Type} (LP : PathsP ι) (s0 : Cfg U64 U64 U64 U64) (K0 : KLayoutP) :
    Cfg U64 U64 U64 U64 → KLayoutP → Prop
  | refl : ExecPR LP s0 K0 s0 K0
  | step {s s' : Cfg U64 U64 U64 U64} {K K' : KLayoutP} {c : U64} :
      ExecPR LP s0 K0 s K → Step s c s' → Fl4StepPR LP s K c s' K' → ExecPR LP s0 K0 s' K'
  | hw {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {v a x : U64} :
      ExecPR LP s0 K0 s K → HwStepP K s v a x → ExecPR LP s0 K0 (hwCfg s a x) K

section exec

/-- **The configuration's class owners are the path's at a view-equal memory** (`ko_congrP`: `ρ` is the memory
on the gate's words). -/
theorem ko_viewP {K : KLayoutP} {s : Cfg U64 U64 U64 U64} (hK : RegionOKP K) (hM : MapsP K s) {c : U64}
    {hs : U64 → Prop} {ρ : U64 → U64} (hV : VEq s.own s.cls s.ko c hs ρ s.mem) :
    s.ko = OwnMap.ko K.toKLayout ρ := by
  rw [hM.ko]
  refine (ko_congrP hK fun y hy => hV.2.1 y ?_).symm
  rw [hM.own, hy]; exact Or.inr rfl

/-- **An `ExecPR` is an `XSafeRunH`** for the serial-prefix memory it determines (module docstring). -/
theorem exec_safeRunPR {ι : Type} {LP : PathsP ι} {s0 s : Cfg U64 U64 U64 U64}
    {K0 K : KLayoutP} (h0 : Init s0) (hA0 : ArmInv s0) (hK0 : RegionOKP K0)
    (hU0 : UserOKP K0) (hM0 : MapsP K0 s0) (h : ExecPR LP s0 K0 s K) :
    ∃ H, XSafeRunH s0 s H ∧ RegionOKP K ∧ UserOKP K ∧ MapsP K s := by
  induction h with
  | refl => exact ⟨s0.mem, .refl, hK0, hU0, hM0⟩
  | @step s s' K K' c _ hst hF ih =>
    obtain ⟨H, hr, hK, hU, hM⟩ := ih
    obtain ⟨-, -, -, hS, -⟩ := xsafeRunH_inv h0 hA0 hr
    refine ⟨NextH s c s' H, .step hr hst ⟨hF.arm, fun p0 k W hph _ => ?_, by rw [hM.own]; exact moveHeldP hK⟩, ?_⟩
    · obtain ⟨ρ, hV, i, hP⟩ := hF.start p0 k W hph hK hU
      have hko := ko_viewP hK hM hV
      rw [hM.own, hM.cls, hko] at hV ⊢
      exact (LP i K ρ hK hU).safeH (moveHeldP hK) (ownDepP hK hU) hP hV
    · by_cases hs : SerStep s c
      · exact hF.ser hs
      · rw [hF.keep hs]
        exact ⟨hK, hU, maps_stepP hK hM (allowed_of_sinv hS c) hst hs⟩
  | hw _ hh ih =>
    obtain ⟨H, hr, hK, hU, hM⟩ := ih
    refine ⟨Function.update H _ _, .hw hr (hh.hwWr hK hM) fun m => ?_, hK, hU, maps_hwP hK hM hh⟩
    rw [hM.own]
    exact ownP_upd_nondec hK (OwnMapV.vcpu_nondec hK.base (hh.vcpu hK.base).1) _ _

/-- **End to end with rules 7 and 8, the starts at view-equal memories** (module docstring). -/
theorem serializable_e2ePR {ι : Type} (LP : PathsP ι) {s0 s : Cfg U64 U64 U64 U64}
    {K0 K : KLayoutP} (h0 : Init s0) (hA0 : ArmInv s0) (hK0 : RegionOKP K0)
    (hU0 : UserOKP K0) (hM0 : MapsP K0 s0) (h : ExecPR LP s0 K0 s K) (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  obtain ⟨H, hr, -⟩ := exec_safeRunPR h0 hA0 hK0 hU0 hM0 h
  exact serializable_safeXH h0 hA0 hr hq

end exec

section exec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {ι : Type}

/-- **A step of FL4 with the glue premises named, the start fact at a view-equal memory** (module docstring). -/
structure Fl4StepWPRR (LP : PathsP ι)
    (SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop)
    (P : LocPlat st arI AR MR) (s : Cfg U64 U64 U64 U64) (K : KLayoutP) (Ch : S → Prop) (c : U64)
    (s' : Cfg U64 U64 U64 U64) (K' : KLayoutP) (Ch' : S → Prop) : Prop where
  /-- [P] an armed program is pure glue. -/
  arm : ∀ p, s'.ph c = .arm p → PureGlue p
  /-- [P] the glue's start fact, **at some memory `ρ` the starting core cannot tell from the physical one**
  (`VEq`; module docstring). U4's start is the instance `ρ := H`, U2's the instance `ρ := s.mem`. -/
  start : ∀ p0 k W, s.ph c = .loc p0 (.start k) W → ∀ (hK : RegionOKP K) (hU : UserOKP K),
    ∃ ρ : U64 → U64, VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem ∧
      ∃ i, SF Ch K ρ hK hU c (fun l => s.lk l = some c) k i
  /-- [P] the serial exit's ghost choice. -/
  serX : SerStep s c → SerExitW P K'.toKLayoutV Ch'
  /-- The glue's layout convention at the serial exit: no VCPU, the PTE set `ptesR` of the exit memory. -/
  serC : SerStep s c → K'.vcpus = ∅ ∧ K'.ptes = ptesR K' s'.mem
  /-- [P] the exit ghost with rule 8. -/
  serG : SerStep s c → MapsP K' s'
  /-- Layout and chain change only at serial steps. -/
  keep : ¬ SerStep s c → K' = K ∧ Ch' = Ch

/-- **An execution of FL4 with the glue steps, starts at view-equal memories.** -/
inductive ExecWPRR (LP : PathsP ι)
    (SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop)
    (P : LocPlat st arI AR MR) (s0 : Cfg U64 U64 U64 U64) (K0 : KLayoutP) (Ch0 : S → Prop) :
    Cfg U64 U64 U64 U64 → KLayoutP → (S → Prop) → Prop
  | refl : ExecWPRR LP SF P s0 K0 Ch0 s0 K0 Ch0
  | step {s s' : Cfg U64 U64 U64 U64} {K K' : KLayoutP} {Ch Ch' : S → Prop} {c : U64} :
      ExecWPRR LP SF P s0 K0 Ch0 s K Ch → Step s c s' → Fl4StepWPRR LP SF P s K Ch c s' K' Ch' →
      ExecWPRR LP SF P s0 K0 Ch0 s' K' Ch'
  | hw {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {Ch : S → Prop} {v a x : U64} :
      ExecWPRR LP SF P s0 K0 Ch0 s K Ch → HwStepP K s v a x → ExecWPRR LP SF P s0 K0 Ch0 (hwCfg s a x) K Ch

/-- **An `ExecWPRR` is an `ExecPR`, with the epoch invariant** (`execPH_of_WPRHG` at view-equal memories: the
epoch's gate-word agreement carries to `ρ`, the physical memory on gate words by `VEq`). -/
theorem execPR_of_WPRRG {LP : PathsP ι}
    {SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop}
    (hSF : ∀ (Ch : S → Prop) (K : KLayoutP) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K) c hs q i,
      (∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) →
      (∃ s1 : Cfg U64 U64 U64 U64, (K.vcpus = ∅ ∧ K.ptes = ptesR K s1.mem) ∧ ∀ x, GateW K x → s.mem x = s1.mem x) →
      SF Ch K s.mem hK hU c hs q i → StartAt (LP i K s.mem hK hU) c hs s.mem q)
    (P : LocPlat st arI AR MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0) (h : ExecWPRR LP SF P s0 K0 Ch0 s K Ch) :
    ExecPR LP s0 K0 s K ∧ SerExitW P K.toKLayoutV Ch ∧
      ∃ s1 : Cfg U64 U64 U64 U64, (K.vcpus = ∅ ∧ K.ptes = ptesR K s1.mem) ∧ ∀ x, GateW K x → s.mem x = s1.mem x := by
  obtain ⟨hK0, hU0⟩ := okP_R hB hc0
  induction h with
  | refl => exact ⟨.refl, hB, s0, hc0, fun _ _ => rfl⟩
  | @step s1 s1' K1 K1' Ch1 Ch1' c1 _ hS g ih =>
    obtain ⟨hE, hX, e1, hCe, hk1⟩ := ih
    obtain ⟨H1, hR, -, -, hM⟩ := exec_safeRunPR h0 hA0 hK0 hU0 hM0 hE
    have hst : Fl4StepPR LP s1 K1 c1 s1' K1' := by
      refine ⟨g.arm, fun p0 k W hph hK hU => ?_, fun hs => ?_, fun hn => (g.keep hn).1⟩
      · obtain ⟨ρ, hV, i, hi⟩ := g.start p0 k W hph hK hU
        have hρg : ∀ x, GateW K1 x → ρ x = e1.mem x := fun x hx =>
          (hV.2.1 x (by rw [hM.own, hx s1.mem]; exact Or.inr rfl)).trans (hk1 x hx)
        exact ⟨ρ, hV, i, hSF _ _ { s1 with mem := ρ } _ _ _ _ _ i hX.chainOf ⟨e1, hCe, hρg⟩ hi⟩
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
        obtain ⟨-, -, -, hSI, -⟩ := xsafeRunH_inv h0 hA0 hR
        refine ⟨e1, hCe, fun x hx => ?_⟩
        rw [← hk1 x hx]
        exact step_gate_keep hM (Fl4Proofs.P2.Serial.allowed_of_sinv hSI c1) hS hs hx
  | @hw s1 K1 Ch1 v a y _ hH ih =>
    obtain ⟨hE, hX, e1, hCe, hk1⟩ := ih
    obtain ⟨H1, -, hK, -, hM⟩ := exec_safeRunPR h0 hA0 hK0 hU0 hM0 hE
    refine ⟨.hw hE hH, hX, e1, hCe, fun x hx => ?_⟩
    rw [← hk1 x hx]
    exact hw_gate_keep hK hM hH hx

/-! ## Coverage: U2 ⊆ U5, U4 ⊆ U5, quiet U2 ⊆ U4 -/

/-- **Every U2 execution is a U5 execution** (`ρ := s.mem`). -/
theorem execWPRR_of_WPR {LP : PathsP ι}
    {SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop}
    {P : LocPlat st arI AR MR} {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop}
    (h : ExecWPR LP SF P s0 K0 Ch0 s K Ch) : ExecWPRR LP SF P s0 K0 Ch0 s K Ch := by
  induction h with
  | refl => exact .refl
  | @step s1 s1' K1 K1' Ch1 Ch1' c1 _ hS g ih =>
    exact .step ih hS ⟨g.arm, fun p0 k W hph hK hU =>
      ⟨s1.mem, ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩, g.start p0 k W hph hK hU⟩, g.serX, g.serC, g.serG,
      g.keep⟩
  | hw _ hH ih => exact .hw ih hH

/-- **Every U4 execution is a U5 execution** (`ρ := H`; `VEq H s.mem` by `SerialH.veq_start` from the invariants
of the execution so far). -/
theorem execWPRR_of_WPRH {LP : PathsP ι}
    {SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop}
    (hSF : ∀ (Ch : S → Prop) (K : KLayoutP) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K) c hs q i,
      (∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) →
      (∃ s1 : Cfg U64 U64 U64 U64, (K.vcpus = ∅ ∧ K.ptes = ptesR K s1.mem) ∧ ∀ x, GateW K x → s.mem x = s1.mem x) →
      SF Ch K s.mem hK hU c hs q i → StartAt (LP i K s.mem hK hU) c hs s.mem q)
    (P : LocPlat st arI AR MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {H : U64 → U64} {Ch0 Ch : S → Prop} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0) (h : ExecWPRH LP SF P s0 K0 Ch0 s K H Ch) : ExecWPRR LP SF P s0 K0 Ch0 s K Ch := by
  obtain ⟨hK0, hU0⟩ := okP_R hB hc0
  induction h with
  | refl => exact .refl
  | @step s1 s1' K1 K1' H1 Ch1 Ch1' c1 hE hS g ih =>
    obtain ⟨hr, -⟩ := exec_safeRunPH h0 hA0 hK0 hU0 hM0 (execPH_of_WPRHG hSF P h0 hA0 hB hc0 hM0 hE).1
    obtain ⟨I, O, Sw, -⟩ := xsafeRunH_inv h0 hA0 hr
    exact .step ih hS ⟨g.arm, fun p0 k W hph hK hU =>
      ⟨H1, veq_start I O Sw hph, g.start p0 k W hph hK hU⟩, g.serX, g.serC, g.serG, g.keep⟩
  | hw _ hH ih => exact .hw ih hH

/-- **A quiet start**: when core `c` is at a `.start`, no local path in progress has written. -/
def QuietStart (s : Cfg U64 U64 U64 U64) (c : U64) : Prop :=
  ∀ p0 k W, s.ph c = .loc p0 (.start k) W → ∀ d p0' p' W', s.ph d = .loc p0' p' W' → W' = ∅

/-- **U2 executions whose every start is quiet.** -/
inductive ExecWPRQ (LP : PathsP ι)
    (SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop)
    (P : LocPlat st arI AR MR) (s0 : Cfg U64 U64 U64 U64) (K0 : KLayoutP) (Ch0 : S → Prop) :
    Cfg U64 U64 U64 U64 → KLayoutP → (S → Prop) → Prop
  | refl : ExecWPRQ LP SF P s0 K0 Ch0 s0 K0 Ch0
  | step {s s' : Cfg U64 U64 U64 U64} {K K' : KLayoutP} {Ch Ch' : S → Prop} {c : U64} :
      ExecWPRQ LP SF P s0 K0 Ch0 s K Ch → Step s c s' → Fl4StepWPR LP SF P s K Ch c s' K' Ch' → QuietStart s c →
      ExecWPRQ LP SF P s0 K0 Ch0 s' K' Ch'
  | hw {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {Ch : S → Prop} {v a x : U64} :
      ExecWPRQ LP SF P s0 K0 Ch0 s K Ch → HwStepP K s v a x → ExecWPRQ LP SF P s0 K0 Ch0 (hwCfg s a x) K Ch

/-- A quiet U2 execution is a U2 execution. -/
theorem ExecWPRQ.toWPR {LP : PathsP ι}
    {SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop}
    {P : LocPlat st arI AR MR} {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop}
    (h : ExecWPRQ LP SF P s0 K0 Ch0 s K Ch) : ExecWPR LP SF P s0 K0 Ch0 s K Ch := by
  induction h with
  | refl => exact .refl
  | step _ hS g _ ih => exact .step ih hS g
  | hw _ hH ih => exact .hw ih hH

/-- **A quiet U2 execution is a U4 execution** (module docstring): at a quiet start the serial-prefix memory is the
physical memory (`InvH.agree`), so U2's start fact is U4's. -/
theorem execWPRH_of_WPRQ {LP : PathsP ι}
    {SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop}
    (hSF : ∀ (Ch : S → Prop) (K : KLayoutP) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K) c hs q i,
      (∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) →
      (∃ s1 : Cfg U64 U64 U64 U64, (K.vcpus = ∅ ∧ K.ptes = ptesR K s1.mem) ∧ ∀ x, GateW K x → s.mem x = s1.mem x) →
      SF Ch K s.mem hK hU c hs q i → StartAt (LP i K s.mem hK hU) c hs s.mem q)
    (P : LocPlat st arI AR MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0) (h : ExecWPRQ LP SF P s0 K0 Ch0 s K Ch) :
    ∃ H, ExecWPRH LP SF P s0 K0 Ch0 s K H Ch := by
  obtain ⟨hK0, hU0⟩ := okP_R hB hc0
  induction h with
  | refl => exact ⟨_, .refl⟩
  | @step s1 s1' K1 K1' Ch1 Ch1' c1 _ hS g hq ih =>
    obtain ⟨H1, hE⟩ := ih
    obtain ⟨hr, -⟩ := exec_safeRunPH h0 hA0 hK0 hU0 hM0 (execPH_of_WPRHG hSF P h0 hA0 hB hc0 hM0 hE).1
    obtain ⟨I, -⟩ := xsafeRunH_inv h0 hA0 hr
    refine ⟨_, .step hE hS ⟨g.arm, fun p0 k W hph hK hU => ?_, g.serX, g.serC, g.serG, g.keep⟩⟩
    have e : H1 = s1.mem := funext fun x =>
      (I.agree x fun d q0 q U hd => by rw [hq p0 k W hph d q0 q U hd]; exact Set.notMem_empty x).symm
    rw [e]
    exact g.start p0 k W hph hK hU
  | hw _ hH ih =>
    obtain ⟨H1, hE⟩ := ih
    exact ⟨_, .hw hE hH⟩

end exec

/-! ## The top -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **FL4 end to end with every slot, each start fact at a memory the starting core cannot tell from the physical
one** (module docstring): `serializable_fl4_localU4` with `start` asked at some `ρ` with `VEq … ρ s.mem` instead of
at the serial-prefix memory. Covers every U2 execution (`execWPRR_of_WPR`) and every U4 execution
(`execWPRR_of_WPRH`). -/
theorem serializable_fl4_localU5 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPRR (PathsP.sum (fl4LocW11JA st ar hA (masksWr_plain st) L.total a0)
        (PathsP.sum (PathsP.sum (delPteSlot st ar hA (masksWr_plain st)) (invSlotU st ar hA (masksWr_plain st)))
          (cmSlotU st ar hA (masksWr_plain st))))
      (StartV2 st ar hA a0 arI AR MR) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  obtain ⟨hK0, hU0⟩ := okP_R hB hc0
  refine serializable_e2ePR _ h0 hA0 hK0 hU0 hM0 (execPR_of_WPRRG ?_ P h0 hA0 hB hc0 hM0 h).1 hq
  intro Ch K s hK hU c hs q i hC hE hsf
  have nv : K.vcpus = ∅ := by
    obtain ⟨_, ⟨nv, _⟩, _⟩ := hE
    exact nv
  rcases i with i | ((j | j) | j)
  · exact startAt_U st ar hA (masksWr_plain st) L.total a0 P hIoa hC hE (startU_of_U2 st ar hA a0 hC nv hsf)
  · exact delPteStart_at st ar hA (masksWr_plain st) hC hE (hsf.2 fun _ s b v _ _ _ => hsf.1.wr s b v)
  · exact invStartU2_at st ar hA (masksWr_plain st) hC hE (hsf.2 fun _ s b v _ _ _ => hsf.1.wr s b v)
  · exact cmStartU2_at st ar hA (masksWr_plain st) hC hE (hsf.2 fun _ s b v _ _ _ => hsf.1.wr s b v)

end top

end
end Fl4Proofs.P2.E2EP
