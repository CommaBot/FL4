/-
P2 (line lvm, gen 4): **end to end with rule 7 and the hardware step** (`serializable_e2eV`), beside
`E2E.serializable_e2e`.

`E2E.Paths` / `Fl4Step` / `Exec` are stated for `OwnMap.own`, under which every VCPU word is the gate's, so
#104's local VM paths (which write `v.PENDING` and other VCPU words under `lock v`) cannot be listed. This
module states the same chain for `OwnMapV.ownV` (rule 7) and adds the hardware's writes as steps:

* `PathsV` / `MapsV` / `Fl4StepV`: `E2E.Paths` / `Maps` / `Fl4Step` with `ownV K`, `RegionOKV`, `UserOKV`
  ([J], as before).
* `HwStepV K s v a x` [P]: the hardware's write `a := x` while `v`'s bound thread runs in the guest: the
  change is one `OwnMapV.VmRunFrame` allows (a non-binding word of `v`), of a kernel word, and no core holds
  `lock v`. `HwStepV.hwWr` turns it into `Serial.HwWr`, whose per-word content is `VmRunFrame.foreign`.
* `ExecV`: executions with core steps (`Fl4StepV`) and hardware steps (`HwStepV`).
* **`serializable_e2eV`**: where an `ExecV` reaches a state with no local path in progress, memory is the
  serial run of the completed entries (hardware writes included) in completion order. Same shape as
  `serializable_e2e`, which stays as it is.
* **Lifting the existing paths** (`LocalPath.liftV`, `PathsV.ofPaths`): every `LocalPath` for `own` is one
  for `ownV` once its `ReadSet` has no non-binding VCPU word (`NoVcpuRd` [W], per path, gen 5: `VData`; a
  binding word is the gate's under both maps; a word it writes, or reads under a held owner, is never a VCPU
  word, as `own` gives those to the gate). A maximal `own` read set fails `NoVcpuRd` (`E2EVTop`). `move` / `dec_alt`'s
  per-write checks lift for every step (`OwnMapV.stepOKV_of_stepOK`: rule 7's owners depend on no memory
  word), through `IsProg` and `interp_mguard_mono`.

Premises beyond `serializable_e2e`'s: `RegionOKV` / `UserOKV` [J] in place of `RegionOK` / `UserOK`;
`HwStepV` [P] for each hardware step (`VmRunFrame`'s sources, and that no core holds `lock v` while the
guest runs, `SerialHw`'s module docstring); for a lifted path, `NoVcpuRd` [W].
-/
import Fl4Proofs.P2.E2E
import Fl4Proofs.P2.OwnMapVcpu
import Fl4Proofs.P2.SerialHw
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EV
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.PathObl Fl4Proofs.P2.E2E Fl4Proofs.P2.OwnMapV
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Step Init ArmInv NoLoc RunAll PureGlue Allowed SafeStep
  HwWr hwCfg XSafeRun xsafeRun_greach serializable_safeX allowed_of_sinv)

noncomputable section
open Classical

/-! ## Lifting a run on `mguard` to a weaker check -/

section mono
variable {S A X : Type} {st : machine.Store S} {ar : machine.Arch A}

/-- A run that passes `mguard`'s check `Q` passes every weaker check `Q'`. -/
theorem interp_mguard_mono {Q Q' : S → S → Prop} (hQ : ∀ x y, Q x y → Q' x y) (p : SProg X) :
    ∀ (s : S) (a : A) (r : X × S × A), interp (mguard st Q) ar p s a = ok r →
      interp (mguard st Q') ar p s a = ok r := by
  have mw : ∀ {s s'' : S} {m : Result S},
      (do let s' ← m; if Q s s' then ok s' else fail .panic) = ok s'' →
      (do let s' ← m; if Q' s s' then ok s' else fail .panic) = ok s'' := by
    intro s s'' m h
    obtain ⟨hm, hq⟩ := mchk (st := st) h
    exact bok.mpr ⟨_, hm, by rw [if_pos (hQ _ _ hq)]⟩
  induction p with
  | ret x => intro s a r h; exact h
  | err e => intro s a r h; exact absurd h fail_not_ok
  | rd q k ih =>
    intro s a r h
    simp only [interp] at h ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    exact bok.mpr ⟨v, hv, ih v s a r hk⟩
  | rdp q k ih =>
    intro s a r h
    simp only [interp] at h ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    exact bok.mpr ⟨v, hv, ih v s a r hk⟩
  | wr q v k ih =>
    intro s a r h
    simp only [interp] at h ⊢
    obtain ⟨s', hv, hk⟩ := bok.mp h
    exact bok.mpr ⟨s', mw hv, ih s' a r hk⟩
  | zero q n k ih =>
    intro s a r h
    simp only [interp] at h ⊢
    obtain ⟨s', hv, hk⟩ := bok.mp h
    exact bok.mpr ⟨s', mw hv, ih s' a r hk⟩
  | clr q n k ih =>
    intro s a r h
    simp only [interp] at h ⊢
    obtain ⟨s', hv, hk⟩ := bok.mp h
    exact bok.mpr ⟨s', mw hv, ih s' a r hk⟩
  | ksb k ih =>
    intro s a r h
    simp only [interp] at h ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    exact bok.mpr ⟨v, hv, ih v s a r hk⟩
  | cpu k ih =>
    intro s a r h
    simp only [interp] at h ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    exact bok.mpr ⟨v, hv, ih v s a r hk⟩
  | masks k ih =>
    intro s a r h
    simp only [interp] at h ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    exact bok.mpr ⟨v, hv, ih v s a r hk⟩
  | arch op k ih =>
    intro s a r h
    simp only [interp] at h ⊢
    obtain ⟨⟨v, a'⟩, hv, hk⟩ := bok.mp h
    exact bok.mpr ⟨(v, a'), hv, ih v s a' r hk⟩

end mono

/-! ## Lifting a local path from `own` to `ownV` -/

section lift
variable {K : KLayoutV} {cls : U64 → U64 → U64} {ko : U64 → ClsOwner U64} {User : U64 → Prop}

/-- The **non-binding words of the VCPUs** (rule 7's `lock v` words, the ones the hardware and the local VM
paths write). -/
def VData (K : KLayoutV) (x : U64) : Prop := ∃ v, InVcpu K v x ∧ ¬ VcpuGate (x.val - v.val)

/-- A read permitted by `own` is one by `ownV` unless the word is a non-binding VCPU word (a binding word is the
gate's under both maps). -/
theorem rpermV_of_own_nd (hK : RegionOKV K) {m : U64 → U64} {x c : U64} {lk : U64 → Prop} (hx : ¬ VData K x)
    (h : PathObl.RPerm (OwnMap.own K.toKLayout) c lk m x) : PathObl.RPerm (ownV K) c lk m x := by
  by_cases hv : ∃ w, InVcpu K w x
  · obtain ⟨w, hw⟩ := hv
    have hg : VcpuGate (x.val - w.val) := by
      by_contra hn; exact hx ⟨w, hw, hn⟩
    right; unfold PathObl.GateOnly; rw [ownV_on hK hw]; simp only [vcpuOwner, if_pos hg]
  · exact rpermV_of_own hv h

/-- **`NoVcpuRd`** [W] (per path; gen 5: only the non-binding words): no word in the path's `ReadSet` (kernel
words) is a non-binding VCPU word. **Not** true of a path whose `ReadSet` is a maximal `own` set (`MaxR`,
`IoRS`, `SlRS`: every `own`-gate-only word, so every aligned VCPU word): `E2EVTop.not_noVcpuRd`. Such a path
has to be rebuilt with its read set cut to `¬ VData` (`E2EVTop.rsV`), for which this holds by definition. -/
def NoVcpuRd (K : KLayoutV) (P : LocalPath (OwnMap.own K.toKLayout) cls ko User) : Prop :=
  ∀ s x, P.Pre s → P.RS s x → ¬ User x → ¬ VData K x

/-- **A local path for `own` is one for `ownV`**, given `NoVcpuRd`. -/
def LocalPath.liftV (hK : RegionOKV K) (P : LocalPath (OwnMap.own K.toKLayout) cls ko User)
    (hN : NoVcpuRd K P) : LocalPath (ownV K) cls ko User where
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
    have mono : ∀ (cpu : U64) (lk : U64 → Prop) (st' : machine.Store P.S) (s : P.S) (a : P.A) r,
        P.F P.ar (mguard st' (fun x y => StepOK (OwnMap.own K.toKLayout) cls ko User cpu lk
          (P.L.mem x) (P.L.mem y))) s a = ok r →
        P.F P.ar (mguard st' (fun x y => StepOK (ownV K) cls ko User cpu lk (P.L.mem x) (P.L.mem y)))
          s a = ok r := by
      intro cpu lk st' s a r h
      have e1 := P.isProg _ P.ar (mguard st' (fun x y => StepOK (OwnMap.own K.toKLayout) cls ko User cpu lk
        (P.L.mem x) (P.L.mem y)))
      have e2 := P.isProg _ P.ar (mguard st' (fun x y => StepOK (ownV K) cls ko User cpu lk (P.L.mem x) (P.L.mem y)))
      exact (congrFun (congrFun e2 s) a).trans (interp_mguard_mono (fun x y hq => stepOKV_of_stepOK hK hq)
        P.p s a r ((congrFun (congrFun e1 s) a).symm.trans h))
    exact {
      acc := P.obl.acc
      dec_alt := fun s a r hp h hd s' r' hA h' => by
        obtain ⟨h1, h2, h3⟩ := P.obl.dec_alt s a r hp h hd s' r' hA h'
        exact ⟨h1, h2, mono _ _ _ _ _ _ h3⟩
      read_own := fun s x hp hr hu => rpermV_of_own_nd hK (hN s x hp hr hu) (P.obl.read_own s x hp hr hu)
      write_own := fun s x hp hw hu => wpermV_of_own' hK (P.obl.write_own s x hp hw hu)
      aligned := P.obl.aligned
      move := fun s a r hp h => mono _ _ _ _ _ _ (P.obl.move s a r hp h) }
  side := P.side
  once := P.once
  total := P.total
  masks := P.masks

end lift

/-! ## Paths, maps, steps and executions with rule 7 -/

/-- The local paths with their obligations for `ownV`, for every layout. -/
abbrev PathsV (ι : Type) : Type 1 :=
  ι → ∀ (K : KLayoutV) (m : U64 → U64), RegionOKV K → UserOKV K →
    LocalPath (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user)

/-- **The existing paths, lifted** (`LocalPath.liftV`), given `NoVcpuRd` [W] of each. -/
def PathsV.ofPaths {ι : Type} (LP : Paths ι)
    (hN : ∀ i (K : KLayoutV) m (hK : RegionOKV K) (hU : UserOKV K), NoVcpuRd K (LP i K.toKLayout m hK.base hU.base)) :
    PathsV ι :=
  fun i K m hK hU => LocalPath.liftV hK (LP i K.toKLayout m hK.base hU.base) (hN i K m hK hU)

/-- Two families of paths side by side (e.g. the lifted existing paths and the VM paths). -/
def PathsV.sum {ι κ : Type} (LP : PathsV ι) (LQ : PathsV κ) : PathsV (ι ⊕ κ)
  | .inl i => LP i
  | .inr j => LQ j

/-- The ghost maps are `ownV`'s for the layout `K`. -/
structure MapsV (K : KLayoutV) (s : Cfg U64 U64 U64 U64) : Prop where
  own : s.own = ownV K
  cls : s.cls = OwnMap.cls K.toKLayout
  ko : s.ko = OwnMap.ko K.toKLayout s.mem

/-- **A step of FL4 with rule 7**: `E2E.Fl4Step`'s fields for `ownV` (`arm` [P], `start` [P], `ser` [J],
`keep`). -/
structure Fl4StepV {ι : Type} (LP : PathsV ι) (s : Cfg U64 U64 U64 U64) (K : KLayoutV)
    (c : U64) (s' : Cfg U64 U64 U64 U64) (K' : KLayoutV) : Prop where
  arm : ∀ p, s'.ph c = .arm p → PureGlue p
  start : ∀ p0 k W, s.ph c = .loc p0 (.start k) W → ∀ (hK : RegionOKV K) (hU : UserOKV K),
    ∃ i, StartAt (LP i K s.mem hK hU) c (fun l => s.lk l = some c) s.mem k
  ser : SerStep s c → RegionOKV K' ∧ UserOKV K' ∧ MapsV K' s'
  keep : ¬ SerStep s c → K' = K

/-- **A hardware step** [P]: while `v`'s bound thread runs in the guest, the hardware writes the kernel word
`a := x`, a change `VmRunFrame` allows, and no core holds `lock v` (`SerialHw`'s module docstring). -/
structure HwStepV (K : KLayoutV) (s : Cfg U64 U64 U64 U64) (v a x : U64) : Prop where
  frame : VmRunFrame K v s.mem (Function.update s.mem a x)
  kern : a ∉ K.user
  chg : x ≠ s.mem a
  free : s.lk v = none

/-- **An execution of FL4 with rule 7**, from `s0` with layout `K0`: core steps and hardware steps. -/
inductive ExecV {ι : Type} (LP : PathsV ι) (s0 : Cfg U64 U64 U64 U64) (K0 : KLayoutV) :
    Cfg U64 U64 U64 U64 → KLayoutV → Prop
  | refl : ExecV LP s0 K0 s0 K0
  | step {s s' : Cfg U64 U64 U64 U64} {K K' : KLayoutV} {c : U64} :
      ExecV LP s0 K0 s K → Step s c s' → Fl4StepV LP s K c s' K' → ExecV LP s0 K0 s' K'
  | hw {s : Cfg U64 U64 U64 U64} {K : KLayoutV} {v a x : U64} :
      ExecV LP s0 K0 s K → HwStepV K s v a x → ExecV LP s0 K0 (hwCfg s a x) K

section exec
variable {K : KLayoutV}

/-- The hardware's word is a VCPU word of `v`. -/
theorem HwStepV.vcpu (hK : RegionOKV K) {s : Cfg U64 U64 U64 U64} {v a x : U64} (h : HwStepV K s v a x) :
    InVcpu K v a ∧ ownV K s.mem a = .lock v := by
  have hb : Function.update s.mem a x a ≠ s.mem a := by rw [Function.update_self]; exact h.chg
  obtain ⟨h1, -, h3⟩ := h.frame.kernel hK hb h.kern
  exact ⟨h1, h3⟩

/-- **A hardware step is a `Serial.HwWr`.** -/
theorem HwStepV.hwWr (hK : RegionOKV K) {s : Cfg U64 U64 U64 U64} {v a x : U64} (h : HwStepV K s v a x)
    (hM : MapsV K s) : HwWr s a x v where
  own := by rw [hM.own]; exact (h.vcpu hK).2
  free := h.free
  keep := by rw [hM.own]; exact ownV_upd_vcpu hK ⟨v, (h.vcpu hK).1⟩ _ _
  ko := by rw [hM.ko]; exact ko_vcpu hK (h.vcpu hK).1 _

open OwnMap in
/-- A core does not write a word deciding a home core: `ko` is kept. -/
theorem ko_updV (hK : RegionOKV K) {m : U64 → U64} {a v : U64} (ha : ownV K m a ≠ .gate) :
    ko K.toKLayout (Function.update m a v) = ko K.toKLayout m := by
  by_cases hav : ∃ w, InVcpu K w a
  · obtain ⟨w, hw⟩ := hav
    funext b
    unfold ko
    cases hr : region K.toKLayout b with
    | tcb t =>
      have ht := hK.base.tcbOf t b hr
      have hne : fld t oAFFINITY ≠ a := by
        intro e
        have h1 := (hK.base.tcb t ht oAFFINITY (Or.inl rfl)).1
        rw [e, hK.none w a hw] at h1; cases h1
      simp only [Function.update_of_ne hne]
    | _ => rfl
  · rw [ownV_off hav] at ha; exact ko_upd hK.base ha

/-- A step other than a serial entry's body keeps the ghost maps `ownV`'s. -/
theorem maps_stepV (hK : RegionOKV K) {s s' : Cfg U64 U64 U64 U64}
    {c : U64} (hM : MapsV K s) (hal : Allowed s c) (hst : Step s c s') (hn : ¬ SerStep s c) :
    MapsV K s' := by
  obtain ⟨h1, h2, h3⟩ := hM
  cases hst with
  | serial _ _ _ _ hh hg _ _ => exact absurd ⟨hg, hh⟩ hn
  | @wr p0 a v k W hc =>
    refine ⟨h1, h2, ?_⟩
    simp only [Allowed, hc] at hal
    have ha : ownV K s.mem a ≠ .gate := by
      rw [← h1]; intro e; have := hal.1; rw [e] at this; exact this
    show s.ko = OwnMap.ko K.toKLayout (Function.update s.mem a v)
    rw [ko_updV hK ha]; exact h3
  | _ => exact ⟨h1, h2, h3⟩

/-- A hardware step keeps the ghost maps. -/
theorem maps_hw (hK : RegionOKV K) {s : Cfg U64 U64 U64 U64} {v a x : U64} (hM : MapsV K s)
    (h : HwStepV K s v a x) : MapsV K (hwCfg s a x) := by
  refine ⟨hM.own, hM.cls, ?_⟩
  show s.ko = OwnMap.ko K.toKLayout (Function.update s.mem a x)
  rw [ko_updV hK (by rw [(h.vcpu hK).2]; intro e; cases e)]; exact hM.ko

theorem exec_safeRunV {ι : Type} {LP : PathsV ι} {s0 s : Cfg U64 U64 U64 U64}
    {K0 K : KLayoutV} (h0 : Init s0) (hA0 : ArmInv s0) (hK0 : RegionOKV K0)
    (hU0 : UserOKV K0) (hM0 : MapsV K0 s0) (h : ExecV LP s0 K0 s K) :
    XSafeRun s0 s ∧ RegionOKV K ∧ UserOKV K ∧ MapsV K s := by
  induction h with
  | refl => exact ⟨.refl, hK0, hU0, hM0⟩
  | @step s s' K K' c _ hst hF ih =>
    obtain ⟨hr, hK, hU, hM⟩ := ih
    obtain ⟨_, hS, _⟩ := xsafeRun_greach h0 hA0 hr
    refine ⟨.step hr hst ⟨hF.arm, fun p0 k W hph => ?_⟩, ?_⟩
    · obtain ⟨i, hP⟩ := hF.start p0 k W hph hK hU
      rw [hM.own, hM.cls, hM.ko]
      exact (LP i K s.mem hK hU).safe (moveHeldV hK) (ownDepV hK hU) hP
    · by_cases hs : SerStep s c
      · exact hF.ser hs
      · rw [hF.keep hs]
        exact ⟨hK, hU, maps_stepV hK hM (allowed_of_sinv hS c) hst hs⟩
  | hw _ hh ih =>
    obtain ⟨hr, hK, hU, hM⟩ := ih
    exact ⟨.hw hr (hh.hwWr hK hM), hK, hU, maps_hw hK hM hh⟩

/-- **End to end with rule 7 and the hardware** (`serializable_e2e`'s statement for `ExecV`): FL4's local
paths `LP` (each with its `LocalPath` obligations for `ownV`, for every layout) and the hardware's writes to
running VCPUs run beside the serial gate exactly as some serial order of the completed entries: where an
`ExecV` reaches a state with no local path in progress, memory is what running them one after another, in
completion order (each hardware write an entry of its own), produces. Premises: at the start `Init`,
`ArmInv`, `RegionOKV` / `UserOKV` [J] and the ghost maps; per core step `Fl4StepV` (`arm`, `start` [P],
`ser` [J]); per hardware step `HwStepV` [P]; per path, `LocalPath`'s ([P]/[W]). -/
theorem serializable_e2eV {ι : Type} (LP : PathsV ι) {s0 s : Cfg U64 U64 U64 U64}
    {K0 K : KLayoutV} (h0 : Init s0) (hA0 : ArmInv s0) (hK0 : RegionOKV K0)
    (hU0 : UserOKV K0) (hM0 : MapsV K0 s0) (h : ExecV LP s0 K0 s K) (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_safeX h0 hA0 (exec_safeRunV h0 hA0 hK0 hU0 hM0 h).1 hq

end exec

end
end Fl4Proofs.P2.E2EV
