/-
P2 (line pte, gen 1): **end to end with rule 8 (leaf PTEs)** (`serializable_e2eP`), beside
`E2EV.serializable_e2eV`, which stays as it is.

`E2EV.PathsV` / `Fl4StepV` / `ExecV` are stated for `OwnMapV.ownV`, under which every page-table word is the
gate's, so a local `X86PageMap` or `CNodeDelete` of a mapped frame (which write one leaf PTE under that PTE's word
lock) cannot be listed. This module states the same chain for `OwnMapP.ownP` (rule 8, `P2/OwnMapPte.lean`):

* `PathsP` / `MapsP` / `Fl4StepP`: `PathsV` / `MapsV` / `Fl4StepV` with `ownP K`, `RegionOKP`, `UserOKP` ([J]).
* `HwStepP` [P]: `HwStepV` of the underlying `KLayoutV` (the hardware writes a non-binding VCPU word, never a
  PTE: `RegionOKP.novcpu`); `HwStepP.hwWr` makes it a `Serial.HwWr` for `ownP`.
* `ExecP`: executions with core steps (`Fl4StepP`) and hardware steps (`HwStepP`).
* **`serializable_e2eP`**: where an `ExecP` reaches a state with no local path in progress, memory is the serial
  run of the completed entries (hardware writes included) in completion order. Its soundness needs of rule 8 only
  `moveHeldP` / `ownDepP` (`OwnMapPte`): the lock discipline for PTEs is the generic one of `Serial` (a lock owner
  is exclusive between a core's acquisition and release, and the closed gate waits for `NoLoc`).
* **Lifting** (`LocalPath.liftP`, `PathsP.ofV`): every `LocalPath` for `ownV` is one for `ownP` once its
  `ReadSet` has no PTE word (**`NoPteRd` [W]**, per path); with `K.ptes = ∅` that holds by itself
  (`noPteRd_empty`). Writes (`wpermP_of_V`), per-write checks (`stepOKP_of_stepOKV`) and everything else carry
  over for every step.
* **The old chain is the `K.ptes = ∅` instance** (`execP_of_V`): every `ExecV` over `LP` is an `ExecP` over
  `PathsP.ofVE LP` at the layouts `KLayoutV.noPte K`, so `serializable_e2eV` (and through it
  `serializable_fl4_localP3W`) is recovered from `serializable_e2eP` (`serializable_e2eV_viaP`).

**The glue premise for a PTE-writing path** (`PtePlanLocked` [P], `PtePlanLocked.wperm`): at the body's start the
plan's PTE entry (`p.locks[p.pte]` with `p.pte < p.n`) is a word of `K.ptes` whose lock the glue holds. Sources:
`crates/fl4-core/src/localinv.rs` `add_pte` (l. 88-91; Delete l. 225-235, PageMap l. 251-253) puts the entry in
the plan; fl4-sync `local_invocation` (`crates/fl4-sync/src/lib.rs` l. 521-545) locks `(p.locks[i], 8 if i ==
p.pte else 32)` for every `i < p.n` through `with_locks` / fl4-store `lock::try_lock_object` before calling the
body (so the `Cfg` lock `e` is that word lock, `StartAt`'s `Locks σ = hs`); the gate holder drains every local
core before a serial entry (`lib.rs` l. 150-183), which is when `K.ptes` may change (`Fl4StepP.keep`); upper
levels and the ASID table change only under the gate (`localinv.rs` l. 19-25, 147-149), so the entry stays the
leaf the plan found. That `e ∈ K.ptes` (the walk's result is a leaf entry of `K`) is a layout fact [J] of the
path, carried in the same premise.

Premises beyond `serializable_e2eV`'s: `RegionOKP` / `UserOKP` [J] in place of `RegionOKV` / `UserOKV`; for a lifted
path, `NoPteRd` [W] (vacuous at `K.ptes = ∅`); for a PTE-writing path, `PtePlanLocked` [P].

Outside the model (as before rule 8, when PTEs were gate-owned): the page walkers' accessed / dirty bit updates
of PTEs (hardware read-modify-writes with no kernel lock).
-/
import Fl4Proofs.P2.E2EV
import Fl4Proofs.P2.OwnMapPte
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.PathObl Fl4Proofs.P2.E2E Fl4Proofs.P2.OwnMapV Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV (PathsV MapsV Fl4StepV HwStepV ExecV interp_mguard_mono serializable_e2eV)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Step Init ArmInv NoLoc RunAll PureGlue Allowed SafeStep
  HwWr hwCfg XSafeRun xsafeRun_greach serializable_safeX allowed_of_sinv)

noncomputable section
open Classical

/-! ## Lifting a local path from `ownV` to `ownP` -/

section lift
variable {K : KLayoutP} {cls : U64 → U64 → U64} {ko : U64 → ClsOwner U64} {User : U64 → Prop}

/-- **`NoPteRd`** [W] (per path): no kernel word of the path's `ReadSet` is a PTE word. Vacuous at `K.ptes = ∅`
(`noPteRd_empty`). Not true of a path whose `ReadSet` is a maximal `own` set (every gate-only word) when
`K.ptes ≠ ∅`: such a path needs its read set cut off the PTEs (as `E2EVCutP` does for the VCPU data words). -/
def NoPteRd (K : KLayoutP) (P : LocalPath (ownV K.toKLayoutV) cls ko User) : Prop :=
  ∀ s x, P.Pre s → P.RS s x → ¬ User x → x ∉ K.ptes

theorem noPteRd_empty (h : K.ptes = ∅) (P : LocalPath (ownV K.toKLayoutV) cls ko User) : NoPteRd K P :=
  fun _ x _ _ _ => by rw [h]; exact Set.notMem_empty x

/-- **A local path for `ownV` is one for `ownP`**, given `NoPteRd`. -/
def LocalPath.liftP (hK : RegionOKP K) (P : LocalPath (ownV K.toKLayoutV) cls ko User)
    (hN : NoPteRd K P) : LocalPath (ownP K) cls ko User where
  S := P.S
  A := P.A
  X := P.X
  st := P.st
  L := P.L
  ar := P.ar
  F := P.F
  p := P.p
  Acc := P.Acc
  Locks := P.Locks
  Pre := P.Pre
  RS := P.RS
  WS := P.WS
  DS := P.DS
  isProg := P.isProg
  obl := by
    letI := P.L
    have mono : ∀ (cpu : U64) (lk : U64 → Prop) (s : P.S) (a : P.A) r,
        AltOf P.st P.Pre P.RS cls ko User s →
        P.F P.ar (mguard P.st (fun x y => StepOK (ownV K.toKLayoutV) cls ko User cpu lk
          (P.L.mem x) (P.L.mem y))) s a = ok r →
        P.F P.ar (mguard P.st (fun x y => StepOK (ownP K) cls ko User cpu lk (P.L.mem x) (P.L.mem y)))
          s a = ok r := by
      intro cpu lk s a r hG h
      have e1 := P.isProg _ (Narrow.mguard P.st (fun x y => StepOK (ownV K.toKLayoutV) cls ko User cpu lk
        (P.L.mem x) (P.L.mem y))) s hG a
      have e2 := P.isProg _ (Narrow.mguard P.st (fun x y => StepOK (ownP K) cls ko User cpu lk
        (P.L.mem x) (P.L.mem y))) s hG a
      exact e2.trans (interp_mguard_mono (fun x y hq => stepOKP_of_stepOKV hq) P.p s a r (e1.symm.trans h))
    exact {
      acc := P.obl.acc
      dec_alt := fun s a r hp h hd s' r' hA h' => by
        obtain ⟨h1, h2, h3⟩ := P.obl.dec_alt s a r hp h hd s' r' hA h'
        exact ⟨h1, h2, mono _ _ _ _ _ ⟨s, hp, hA⟩ h3⟩
      read_own := fun s x hp hr hu => rpermP_of_V (hN s x hp hr hu) (P.obl.read_own s x hp hr hu)
      write_own := fun s x hp hw hu => wpermP_of_V hK (P.obl.write_own s x hp hw hu)
      aligned := P.obl.aligned
      move := fun s a r hp h => mono _ _ _ _ _ (AltOf.pre hp) (P.obl.move s a r hp h) }
  side := P.side
  once := P.once
  total := P.total
  masks := P.masks

end lift

/-! ## Paths, maps, steps and executions with rule 8 -/

/-- The local paths with their obligations for `ownP`, for every layout. -/
abbrev PathsP (ι : Type) : Type 1 :=
  ι → ∀ (K : KLayoutP) (m : U64 → U64), RegionOKP K → UserOKP K →
    LocalPath (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user)

/-- **The `ownV` paths, lifted** (`LocalPath.liftP`), given `NoPteRd` [W] of each. -/
def PathsP.ofV {ι : Type} (LP : PathsV ι)
    (hN : ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K),
      NoPteRd K (LP i K.toKLayoutV m hK.base hU.base)) : PathsP ι :=
  fun i K m hK hU => LocalPath.liftP hK (LP i K.toKLayoutV m hK.base hU.base) (hN i K m hK hU)

/-- A path that never starts (`Pre := False`), for any ownership map: every obligation is vacuous. -/
def LocalPath.voidP {own own' : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
    {ko : U64 → ClsOwner U64} {User : U64 → Prop} (P : LocalPath own cls ko User) :
    LocalPath own' cls ko User where
  S := P.S
  A := P.A
  X := P.X
  st := P.st
  L := P.L
  ar := P.ar
  F := P.F
  p := P.p
  Acc := P.Acc
  Locks := P.Locks
  Pre := fun _ => False
  RS := P.RS
  WS := P.WS
  DS := P.DS
  isProg := fun _ _ _ hG _ => absurd hG.choose_spec.1 id
  obl := by
    letI := P.L
    exact {
    acc := fun _ _ _ h => absurd h id
    dec_alt := fun _ _ _ h => absurd h id
    read_own := fun _ _ h => absurd h id
    write_own := fun _ _ h => absurd h id
    aligned := fun _ _ h => absurd h id
    move := fun _ _ _ h => absurd h id }
  side := by
    letI := P.L
    exact {
    read_aligned := fun _ _ _ _ h => absurd h id
    rs_aligned := fun _ _ h => absurd h id
    ko_aligned := P.side.ko_aligned
    user_free := fun _ _ _ h => absurd h id }
  once := fun _ _ _ _ h => absurd h id
  total := P.total
  masks := P.masks

/-- **The `ownV` paths at the layouts without PTE words** (no premise): `liftP` where `K.ptes = ∅`
(`noPteRd_empty`), a never-starting path elsewhere. The family for which the old chain is rule 8's instance
(`execP_of_V`); beside PTE-writing paths (layouts with PTEs) use `PathsP.ofV` with `NoPteRd` [W]. -/
def PathsP.ofVE {ι : Type} (LP : PathsV ι) : PathsP ι :=
  fun i K m hK hU => if h : K.ptes = ∅ then
      LocalPath.liftP hK (LP i K.toKLayoutV m hK.base hU.base) (noPteRd_empty h _)
    else LocalPath.voidP (LP i K.toKLayoutV m hK.base hU.base)

/-- Two families of paths side by side (e.g. the lifted `ownV` paths and the PTE-writing paths). -/
def PathsP.sum {ι κ : Type} (LP : PathsP ι) (LQ : PathsP κ) : PathsP (ι ⊕ κ)
  | .inl i => LP i
  | .inr j => LQ j

/-- The ghost maps are `ownP`'s for the layout `K`. -/
structure MapsP (K : KLayoutP) (s : Cfg U64 U64 U64 U64) : Prop where
  own : s.own = ownP K
  cls : s.cls = OwnMap.cls K.toKLayout
  ko : s.ko = OwnMap.ko K.toKLayout s.mem

/-- **A step of FL4 with rule 8**: `Fl4StepV`'s fields for `ownP` (`arm` [P], `start` [P], `ser` [J], `keep`:
the PTE set is ghost layout only serial entries change, as the upper paging levels it is read from change only
under the gate). -/
structure Fl4StepP {ι : Type} (LP : PathsP ι) (s : Cfg U64 U64 U64 U64) (K : KLayoutP)
    (c : U64) (s' : Cfg U64 U64 U64 U64) (K' : KLayoutP) : Prop where
  arm : ∀ p, s'.ph c = .arm p → PureGlue p
  start : ∀ p0 k W, s.ph c = .loc p0 (.start k) W → ∀ (hK : RegionOKP K) (hU : UserOKP K),
    ∃ i, StartAt (LP i K s.mem hK hU) c (fun l => s.lk l = some c) s.mem k
  ser : SerStep s c → RegionOKP K' ∧ UserOKP K' ∧ MapsP K' s'
  keep : ¬ SerStep s c → K' = K

/-- **A hardware step** [P]: `HwStepV` of the underlying VCPU layout. -/
abbrev HwStepP (K : KLayoutP) (s : Cfg U64 U64 U64 U64) (v a x : U64) : Prop := HwStepV K.toKLayoutV s v a x

/-- **An execution of FL4 with rules 7 and 8**, from `s0` with layout `K0`: core steps and hardware steps. -/
inductive ExecP {ι : Type} (LP : PathsP ι) (s0 : Cfg U64 U64 U64 U64) (K0 : KLayoutP) :
    Cfg U64 U64 U64 U64 → KLayoutP → Prop
  | refl : ExecP LP s0 K0 s0 K0
  | step {s s' : Cfg U64 U64 U64 U64} {K K' : KLayoutP} {c : U64} :
      ExecP LP s0 K0 s K → Step s c s' → Fl4StepP LP s K c s' K' → ExecP LP s0 K0 s' K'
  | hw {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {v a x : U64} :
      ExecP LP s0 K0 s K → HwStepP K s v a x → ExecP LP s0 K0 (hwCfg s a x) K

section exec
variable {K : KLayoutP}

/-- **A hardware step is a `Serial.HwWr` for `ownP`**: its word is a VCPU word, never a PTE. -/
theorem HwStepP.hwWr (hK : RegionOKP K) {s : Cfg U64 U64 U64 U64} {v a x : U64} (h : HwStepP K s v a x)
    (hM : MapsP K s) : HwWr s a x v where
  own := by rw [hM.own, ownP_vcpu hK (h.vcpu hK.base).1]; exact (h.vcpu hK.base).2
  free := h.free
  keep := by
    rw [hM.own]
    exact ownP_upd_nondec hK (OwnMapV.vcpu_nondec hK.base (h.vcpu hK.base).1) _ _
  ko := by rw [hM.ko]; exact ko_vcpu hK.base (h.vcpu hK.base).1 _

open OwnMap in
/-- A core does not write a word deciding a home core: `ko` is kept. -/
theorem ko_updP (hK : RegionOKP K) {m : U64 → U64} {a v : U64} (ha : ownP K m a ≠ .gate) :
    ko K.toKLayout (Function.update m a v) = ko K.toKLayout m := by
  by_cases hap : a ∈ K.ptes
  · funext b
    unfold ko
    cases hr : region K.toKLayout b with
    | tcb t =>
      have ht := hK.base.base.tcbOf t b hr
      have hne : fld t oAFFINITY ≠ a := by
        intro e
        have h1 := (hK.base.base.tcb t ht oAFFINITY (Or.inl rfl)).1
        rw [e, hK.none a hap] at h1; cases h1
      simp only [Function.update_of_ne hne]
    | _ => rfl
  · rw [ownP_off hap] at ha; exact E2EV.ko_updV hK.base ha

/-- A step other than a serial entry's body keeps the ghost maps `ownP`'s. -/
theorem maps_stepP (hK : RegionOKP K) {s s' : Cfg U64 U64 U64 U64}
    {c : U64} (hM : MapsP K s) (hal : Allowed s c) (hst : Step s c s') (hn : ¬ SerStep s c) :
    MapsP K s' := by
  obtain ⟨h1, h2, h3⟩ := hM
  cases hst with
  | serial _ _ _ _ hh hg _ _ => exact absurd ⟨hg, hh⟩ hn
  | @wr p0 a v k W hc =>
    refine ⟨h1, h2, ?_⟩
    simp only [Allowed, hc] at hal
    have ha : ownP K s.mem a ≠ .gate := by
      rw [← h1]; intro e; have := hal.1; rw [e] at this; exact this
    show s.ko = OwnMap.ko K.toKLayout (Function.update s.mem a v)
    rw [ko_updP hK ha]; exact h3
  | _ => exact ⟨h1, h2, h3⟩

/-- A hardware step keeps the ghost maps. -/
theorem maps_hwP (hK : RegionOKP K) {s : Cfg U64 U64 U64 U64} {v a x : U64} (hM : MapsP K s)
    (h : HwStepP K s v a x) : MapsP K (hwCfg s a x) := by
  refine ⟨hM.own, hM.cls, ?_⟩
  show s.ko = OwnMap.ko K.toKLayout (Function.update s.mem a x)
  rw [ko_updP hK (by rw [ownP_vcpu hK (h.vcpu hK.base).1, (h.vcpu hK.base).2]; intro e; cases e)]
  exact hM.ko

theorem exec_safeRunP {ι : Type} {LP : PathsP ι} {s0 s : Cfg U64 U64 U64 U64}
    {K0 K : KLayoutP} (h0 : Init s0) (hA0 : ArmInv s0) (hK0 : RegionOKP K0)
    (hU0 : UserOKP K0) (hM0 : MapsP K0 s0) (h : ExecP LP s0 K0 s K) :
    XSafeRun s0 s ∧ RegionOKP K ∧ UserOKP K ∧ MapsP K s := by
  induction h with
  | refl => exact ⟨.refl, hK0, hU0, hM0⟩
  | @step s s' K K' c _ hst hF ih =>
    obtain ⟨hr, hK, hU, hM⟩ := ih
    obtain ⟨_, hS, _⟩ := xsafeRun_greach h0 hA0 hr
    refine ⟨.step hr hst ⟨hF.arm, fun p0 k W hph => ?_⟩, ?_⟩
    · obtain ⟨i, hP⟩ := hF.start p0 k W hph hK hU
      rw [hM.own, hM.cls, hM.ko]
      exact (LP i K s.mem hK hU).safe (moveHeldP hK) (ownDepP hK hU) hP
    · by_cases hs : SerStep s c
      · exact hF.ser hs
      · rw [hF.keep hs]
        exact ⟨hK, hU, maps_stepP hK hM (allowed_of_sinv hS c) hst hs⟩
  | hw _ hh ih =>
    obtain ⟨hr, hK, hU, hM⟩ := ih
    exact ⟨.hw hr (hh.hwWr hK hM), hK, hU, maps_hwP hK hM hh⟩

/-- **End to end with rules 7 and 8 and the hardware** (`serializable_e2eV`'s statement for `ExecP`): FL4's local
paths `LP` (each with its `LocalPath` obligations for `ownP`, for every layout: a PTE-writing path holds the PTE's
word lock, `wpermP_pte`) and the hardware's writes to running VCPUs run beside the serial gate exactly as some
serial order of the completed entries: where an `ExecP` reaches a state with no local path in progress, memory is
what running them one after another, in completion order, produces. Premises: at the start `Init`, `ArmInv`,
`RegionOKP` / `UserOKP` [J] and the ghost maps; per core step `Fl4StepP` (`arm`, `start` [P], `ser` [J]); per
hardware step `HwStepP` [P]; per path, `LocalPath`'s ([P]/[W]). -/
theorem serializable_e2eP {ι : Type} (LP : PathsP ι) {s0 s : Cfg U64 U64 U64 U64}
    {K0 K : KLayoutP} (h0 : Init s0) (hA0 : ArmInv s0) (hK0 : RegionOKP K0)
    (hU0 : UserOKP K0) (hM0 : MapsP K0 s0) (h : ExecP LP s0 K0 s K) (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_safeX h0 hA0 (exec_safeRunP h0 hA0 hK0 hU0 hM0 h).1 hq

/-- **The lifted `ownV` paths beside PTE-writing paths**: an execution over `PathsP.sum (PathsP.ofV LP hN) LQ`
(the `ownV` paths `LP`, e.g. `serializable_fl4_localP3W`'s family, each with `NoPteRd` [W]; the PTE paths `LQ`,
stated for `ownP`) is serializable where no local path is in progress. -/
theorem serializable_e2eP_lift {ι κ : Type} (LP : PathsV ι)
    (hN : ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K),
      NoPteRd K (LP i K.toKLayoutV m hK.base hU.base))
    (LQ : PathsP κ) {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} (h0 : Init s0) (hA0 : ArmInv s0)
    (hK0 : RegionOKP K0) (hU0 : UserOKP K0) (hM0 : MapsP K0 s0)
    (h : ExecP (PathsP.sum (PathsP.ofV LP hN) LQ) s0 K0 s K) (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_e2eP _ h0 hA0 hK0 hU0 hM0 h hq

end exec

/-! ## The old chain is the `K.ptes = ∅` instance -/

section empty

theorem mapsP_noPte {K : KLayoutV} {s : Cfg U64 U64 U64 U64} (h : MapsV K s) : MapsP (KLayoutV.noPte K) s :=
  ⟨by rw [h.own, ownP_noPte], h.cls, h.ko⟩

theorem regionOKP_noPte {K : KLayoutV} (h : RegionOKV K) : RegionOKP (KLayoutV.noPte K) :=
  regionOKP_empty rfl h

theorem userOKP_noPte {K : KLayoutV} (h : UserOKV K) : UserOKP (KLayoutV.noPte K) :=
  userOKP_empty rfl h

/-- **Every `ExecV` is an `ExecP`** at the layouts without PTE words (`KLayoutV.noPte`), over the lifted family
`PathsP.ofVE LP` (no premise: at these layouts `noPteRd_empty`). -/
theorem execP_of_V {ι : Type} {LP : PathsV ι}
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutV} (h : ExecV LP s0 K0 s K) :
    ExecP (PathsP.ofVE LP) s0 (KLayoutV.noPte K0) s (KLayoutV.noPte K) := by
  induction h with
  | refl => exact .refl
  | @step s s' K K' c _ hst hF ih =>
    refine .step ih hst ⟨hF.arm, fun p0 k W hph hK hU => ?_, fun hs => ?_, fun hs => ?_⟩
    · obtain ⟨i, hP⟩ := hF.start p0 k W hph hK.base hU.base
      refine ⟨i, ?_⟩
      show StartAt (if h : (KLayoutV.noPte K).ptes = ∅ then _ else _) _ _ _ _
      rw [dif_pos (show (KLayoutV.noPte K).ptes = ∅ from rfl)]
      exact hP
    · obtain ⟨h1, h2, h3⟩ := hF.ser hs
      exact ⟨regionOKP_noPte h1, userOKP_noPte h2, mapsP_noPte h3⟩
    · rw [hF.keep hs]
  | hw _ hh ih => exact .hw ih hh

/-- **`serializable_e2eV` through `serializable_e2eP`**: the existing end-to-end chain (and every instance of it,
`serializable_fl4_localP3W` included) is rule 8's at `K.ptes = ∅`. -/
theorem serializable_e2eV_viaP {ι : Type} (LP : PathsV ι) {s0 s : Cfg U64 U64 U64 U64}
    {K0 K : KLayoutV} (h0 : Init s0) (hA0 : ArmInv s0) (hK0 : RegionOKV K0)
    (hU0 : UserOKV K0) (hM0 : MapsV K0 s0) (h : ExecV LP s0 K0 s K) (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_e2eP (PathsP.ofVE LP) h0 hA0 (regionOKP_noPte hK0) (userOKP_noPte hU0)
    (mapsP_noPte hM0) (execP_of_V h) hq

end empty

/-! ## The glue premise of a PTE-writing path -/

/-- **`PtePlanLocked`** [P] (module docstring, with the Rust lines): at the body's start, if the plan holds a
page-table entry (`p.pte < p.n`), that entry `e = p.locks[p.pte]` is a leaf PTE of the layout (`e ∈ K.ptes`,
the walk's result: [J] part) and the glue holds its word lock (`Locks e`: fl4-sync `local_invocation`,
`crates/fl4-sync/src/lib.rs` l. 521-545, `with_locks` of `(p.locks[p.pte], 8)`; plan `localinv.rs` `add_pte`
l. 88-91). -/
def PtePlanLocked (K : KLayoutP) (Locks : U64 → Prop) (p : localinv.Plan) : Prop :=
  p.pte.val < p.n.val → ∃ e, p.locks.val[p.pte.val]? = some e ∧ e ∈ K.ptes ∧ Locks e

/-- **The planned PTE is writable by the path** (`PathObl.write_own` for that word). -/
theorem PtePlanLocked.wperm {K : KLayoutP} {Locks : U64 → Prop} {p : localinv.Plan}
    (h : PtePlanLocked K Locks p) (hp : p.pte.val < p.n.val) (c : U64) (m : U64 → U64) :
    ∃ e, p.locks.val[p.pte.val]? = some e ∧ PathObl.WPerm (ownP K) c Locks m e := by
  obtain ⟨e, he, hK, hl⟩ := h hp
  exact ⟨e, he, wpermP_pte hK hl⟩

/-- **The glue's plan locks give `PtePlanLocked`'s lock half**: `InvQ`'s lock conjunct (every `p.locks[i]`,
`i < p.n`, held) and the [J] fact that the entry is a leaf PTE of `K`. -/
theorem ptePlanLocked_of {K : KLayoutP} {Locks : U64 → Prop} {p : localinv.Plan}
    (hlk : ∀ (i : Nat) (x : U64), i < p.n.val → p.locks.val[i]? = some x → Locks x)
    (hpte : ∀ e, p.pte.val < p.n.val → p.locks.val[p.pte.val]? = some e → e ∈ K.ptes)
    (hin : p.pte.val < p.n.val → ∃ e, p.locks.val[p.pte.val]? = some e) :
    PtePlanLocked K Locks p := by
  intro hp
  obtain ⟨e, he⟩ := hin hp
  exact ⟨e, he, hpte e hp he, hlk _ e hp he⟩

end
end Fl4Proofs.P2.E2EP
