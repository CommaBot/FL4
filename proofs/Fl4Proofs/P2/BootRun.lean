/-
# P2 (line p3mc, gen 38): **the started timer-IRQ body run to the end; V12 / V13 applied to an execution with a
real start**; a serial step from the boot to any P3 exit

Gen 37 (`P2/BootStart`) ran an execution from the boot configuration `s0B O` up to the `.start` step of the
timer-IRQ path (`execStartV12_B` / `execStartV13_B`), core 0 left in the started body `kB O a`, so `hq` (`NoLoc`) did
not hold and the tops were not applied. This module finishes the body and leaves.

## Running any body without a `.start` marker (generic)
* `StFree k`: the body `k` has no `.start` node. **`stFree_tr`**: every translated trait-call tree (`E2E.tr`, hence
  every `LocalPath.body`) is `StFree`; **`stFree_cutP`** / **`stFree_narrow`**: the PTE cut (`cutP`) and the
  re-annotation (`narrowSP`, hence `annV`) keep it. **`stFree_kB`**: the armed timer-IRQ body `kB O a` is `StFree` —
  no fact about the extracted `handle_timer_irq_local` beyond its being a translated tree is needed.
* **`run_loc`**: along an `ExecWPRV12`, a core-0 local path at an open gate whose remaining body is `StFree` runs to
  `.done` (reads `rd` / `rds` / `rdc` take memory's value, `wr` writes, every `lock` attempt is taken as a failure,
  `b = false`, which `Step.lock` allows at any time), other cores' phases, the gate and the log unchanged. Each step's
  `Fl4StepWPRV12` (`stepW_loc`): `arm` / `start` from the phases (no `.start` is ever met: `StFree`), `serX` / `serC`
  / `serG` vacuous (the gate is open, so no `SerStep`), `keep` by `rfl`. **`leave_loc`**: then the `leave` step.
  The program is an inductive (well-founded) tree, so the run terminates by induction; it is one of the body's runs,
  not a chosen one (the values read are memory's).
* **`runEnd`**: from `dfg3 K m k` (gen 37's configuration after the `.start` step) with `StFree k`, an execution to a
  configuration with `NoLoc` and log `[.start k]`.

## The tops on an execution with a real start (goal 1)
* **`runEndV12_B`** / **`runEndV13_B`**: `ExecWPRV12 (famB a0) (¬ IoIx) (StartV2C | StartV13) … (s0B O) … s …` with
  `NoLoc s` and `s.log = [.start (kB O a)]`: the execution runs the timer-IRQ path's `.start` step (start fact
  proved, gen 37) and its whole body.
* **`topV12_B`** / **`topV13_B`**: `serializable_fl4_localV12` / `serializable_fl4_localV13` applied to that
  execution: `Run (.start (kB O a)) memB s.mem` — the top's conclusion (the log's sequential run reaches the physical
  memory) on an execution containing a real start of a real path.

## A serial step from the boot to a P3 exit (goal 2, the Cfg side)
* `sfg1 … sfg4`: core 0 takes the ticket with a body `p`, scans itself, closes the gate and runs `p` (`Run p m m'`)
  as a serial entry, the exit ghosts being rule 8's for a new layout `K'` (memory `m'`), gate open again.
  **`exec_ser`**: the four steps are an `ExecWPRV12` from `cfg0 K m` (layout `K`, chain `Ch0`) to `sfg4 …` (layout
  `K'`, chain `Ch'`) for every `K'`, `Ch'` with `SerExitW P K' (Ch' e)` and `K'.vcpus = ∅ ∧ K'.ptes = ptesR K' m'`.
  `sfg4` is `cfg0 K' m'` up to `seen` / `log` (`sfg4_ph`, `sfg4_gate`, `mapsP_sfg4`, `noLoc_sfg4`).
* **`serExit_of`**: every P3 exit `hJ : JReachU17 σe a3 τ` gives `SerExitW` for `chainC P hJ`'s layout and chain.
  **`serBridge_B`**: from `s0B O`, for any such exit, any `Run p memB m'` and the convention
  `ptes = ptesR K' m'`, the serial step is an `ExecWPRV12` of V12 / V13's family to the exit's layout. So what goal 2
  still needs is entirely on the P3 side: a `JReachU17` state `σe` with a non-idle current thread, the memory `m'`
  reached from `memB` by writes, and the layout convention there (see the handoff, §43).

No premise added. No existing statement changed except the root import list.
-/
import Fl4Proofs.P2.BootStart
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.BootSt
open fl4_core Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P1 Classical
open Fl4Proofs.P2.PathObl Fl4Proofs.P2.E2EV Fl4Proofs.P2.OwnMapP Fl4Proofs.P2.OwnMapV Fl4Proofs.P2.E2EP
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll Step PureGlue Phase Gate Prog Run release VEq
  narrowSP)
open Fl4Proofs.P2.E2E (SerStep SP tr rdN)

noncomputable section

/-! ## Bodies without a `.start` marker -/

/-- **The body has no `.start` node.** -/
def StFree {A V L : Type} : Prog A V L → Prop
  | .done => True
  | .rd _ k => ∀ v, StFree (k v)
  | .wr _ _ k => StFree k
  | .lock _ k => ∀ b, StFree (k b)
  | .rds _ k => ∀ v, StFree (k v)
  | .start _ => False
  | .rdc _ _ k => ∀ v, StFree (k v)

theorem stFree_rdN {R User : U64 → Prop} {cls : U64 → U64 → U64} {ko : U64 → ClsOwner U64} {c : U64}
    {Wd : Set U64} {q : U64} {k : U64 → SP} (h : ∀ v, StFree (k v)) : StFree (rdN R User cls ko c Wd q k) := by
  unfold rdN
  split_ifs <;> exact h

/-- **Every translated trait-call tree is `StFree`.** -/
theorem stFree_tr (R User : U64 → Prop) (cls : U64 → U64 → U64) (ko : U64 → ClsOwner U64) (c kb : U64)
    (mk : U64 × U64) {A X : Type} (ar : machine.Arch A) :
    ∀ (x : SProg X) (Wd : Set U64) (a : A), StFree (tr R User cls ko c kb mk ar x Wd a) := by
  intro x
  induction x with
  | ret _ => intro _ _; trivial
  | err _ => intro _ _; trivial
  | rd q k ih => intro Wd a; exact stFree_rdN fun v => ih v Wd a
  | rdp q k ih => intro Wd a; exact stFree_rdN fun v => stFree_rdN fun w => ih (v, w) Wd a
  | wr q v k ih =>
    intro Wd a
    simp only [tr]
    split_ifs
    · exact ih Wd a
    · exact ih (insert q Wd) a
  | zero _ _ _ _ => intro _ _; trivial
  | clr _ _ _ _ => intro _ _; trivial
  | ksb k ih => intro Wd a; exact ih kb Wd a
  | cpu k ih => intro Wd a; exact ih c Wd a
  | masks k ih => intro Wd a; exact ih mk Wd a
  | arch op k ih =>
    intro Wd a
    simp only [tr]
    split_ifs with h
    · exact ih _ Wd _
    · trivial

/-- **The PTE cut keeps `StFree`.** -/
theorem stFree_cutP (E User : U64 → Prop) (cls : U64 → U64 → U64) (ko : U64 → ClsOwner U64) (c : U64) :
    ∀ (k : SP) (Wd : Set U64), StFree k → StFree (cutP E User cls ko c k Wd) := by
  intro k
  induction k with
  | done => intro _ _; trivial
  | rd q k ih =>
    intro Wd h
    simp only [cutP]
    split_ifs <;> exact fun v => ih v Wd (h v)
  | wr q v k ih => intro Wd h; exact ih (insert q Wd) h
  | lock l k ih => intro Wd h; exact fun b => ih b Wd (h b)
  | rds q k ih => intro Wd h; exact fun v => ih v Wd (h v)
  | start k ih => intro Wd h; exact False.elim h
  | rdc q K k ih => intro Wd h; exact fun v => ih v Wd (h v)

/-- **The re-annotation keeps `StFree`.** -/
theorem stFree_narrow (cls : U64 → U64 → U64) (ko : U64 → ClsOwner U64) (c : U64) (Q : U64 → Prop) :
    ∀ (k : SP) (Wd : Set U64), StFree k → StFree (narrowSP cls ko c Q Wd k) := by
  intro k
  induction k with
  | done => intro _ _; trivial
  | rd q k ih =>
    intro Wd h
    simp only [narrowSP]
    split_ifs <;> exact fun v => ih v Wd (h v)
  | wr q v k ih => intro Wd h; exact ih (insert q Wd) h
  | lock l k ih => intro Wd h; exact fun b => ih b Wd (h b)
  | rds q k ih => intro Wd h; exact fun v => ih v Wd (h v)
  | start k ih => intro Wd h; exact False.elim h
  | rdc q K k ih =>
    intro Wd h
    simp only [narrowSP]
    split_ifs <;> exact fun v => ih v Wd (h v)

/-- **The armed timer-IRQ body has no `.start` node** (module docstring). -/
theorem stFree_kB (O : LocPlatM.OpaqueH) (a : Fl4Spec.MachineState) : StFree (kB O a) := by
  unfold kB
  split
  · exact stFree_narrow _ _ _ _ _ _ (stFree_cutP _ _ _ _ _ _ _ (stFree_tr _ _ _ _ _ _ _ _ _ _ _))
  · trivial

/-! ## Running a local path to its end -/

theorem dfg3_ph (K : KLayoutP) (m : U64 → U64) (k : SP) {d : U64} (hd : d ≠ 0#u64) :
    (dfg3 K m k).ph d = .idle := by
  show Function.update (Function.update (Function.update (cfg0 K m).ph 0#u64 (.arm (.start k))) 0#u64
    (.loc (.start k) (.start k) ∅)) 0#u64 (.loc (.start k) k ∅) d = .idle
  simp only [Function.update_of_ne hd, cfg0_ph]

section run
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {ι : Type} {LP : PathsP ι} {NoV : ι → Prop}
  {SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop}
  {P : LocPlat st arI AR MR} {s0 : Cfg U64 U64 U64 U64} {K0 : KLayoutP} {Ch0 : U64 → S → Prop}
  {K : KLayoutP} {Ch : U64 → S → Prop}

/-- **A local step at an open gate** (no `SerStep`): every field of `Fl4StepWPRV12` from the phases. -/
theorem stepW_loc {s s' : Cfg U64 U64 U64 U64} {c : U64} (hg : s.gate = .opn)
    (harm : ∀ p, s'.ph c ≠ .arm p) (hst : ∀ p0 k W, s.ph c ≠ .loc p0 (.start k) W) :
    Fl4StepWPRV12 LP NoV SF P s K Ch c s' K Ch where
  arm p h := absurd h (harm p)
  start p0 k W h := absurd h (hst p0 k W)
  serX h := absurd (h.1.symm.trans hg) (by decide)
  serC h := absurd (h.1.symm.trans hg) (by decide)
  serG h := absurd (h.1.symm.trans hg) (by decide)
  keep _ := ⟨rfl, rfl⟩

/-- One local step of core 0, then the rest of the run. -/
theorem run_cont {s s1 : Cfg U64 U64 U64 U64} {p0 k' : SP} {W1 : Set U64}
    (he : ExecWPRV12 LP NoV SF P s0 K0 Ch0 s K Ch) (hg : s.gate = .opn) (hS : Step s 0#u64 s1)
    (hst : ∀ p0 k W, s.ph 0#u64 ≠ .loc p0 (.start k) W)
    (hph : s1.ph = Function.update s.ph 0#u64 (.loc p0 k' W1)) (hg1 : s1.gate = s.gate) (hl1 : s1.log = s.log)
    (ih : ∀ {s : Cfg U64 U64 U64 U64} {p0 : SP} {W : Set U64}, ExecWPRV12 LP NoV SF P s0 K0 Ch0 s K Ch →
      s.ph 0#u64 = .loc p0 k' W → s.gate = .opn →
      ∃ (s' : Cfg U64 U64 U64 U64) (W' : Set U64), ExecWPRV12 LP NoV SF P s0 K0 Ch0 s' K Ch ∧
        s'.ph 0#u64 = .loc p0 .done W' ∧ (∀ d, d ≠ 0#u64 → s'.ph d = s.ph d) ∧ s'.gate = .opn ∧ s'.log = s.log) :
    ∃ (s' : Cfg U64 U64 U64 U64) (W' : Set U64), ExecWPRV12 LP NoV SF P s0 K0 Ch0 s' K Ch ∧
      s'.ph 0#u64 = .loc p0 .done W' ∧ (∀ d, d ≠ 0#u64 → s'.ph d = s.ph d) ∧ s'.gate = .opn ∧ s'.log = s.log := by
  have e1 : ExecWPRV12 LP NoV SF P s0 K0 Ch0 s1 K Ch :=
    .step he hS (stepW_loc hg (fun p h => by rw [hph, Function.update_self] at h; cases h) hst)
  obtain ⟨s', W', e', hp', hd, hg', hl⟩ := ih e1 (by rw [hph, Function.update_self]) (hg1.trans hg)
  exact ⟨s', W', e', hp', fun d h => by rw [hd d h, hph, Function.update_of_ne h], hg', hl.trans hl1⟩

/-- **A `StFree` body of core 0 runs to `.done`** (module docstring). -/
theorem run_loc (k : SP) : StFree k → ∀ {s : Cfg U64 U64 U64 U64} {p0 : SP} {W : Set U64},
    ExecWPRV12 LP NoV SF P s0 K0 Ch0 s K Ch → s.ph 0#u64 = .loc p0 k W → s.gate = .opn →
    ∃ (s' : Cfg U64 U64 U64 U64) (W' : Set U64), ExecWPRV12 LP NoV SF P s0 K0 Ch0 s' K Ch ∧
      s'.ph 0#u64 = .loc p0 .done W' ∧ (∀ d, d ≠ 0#u64 → s'.ph d = s.ph d) ∧ s'.gate = .opn ∧ s'.log = s.log := by
  induction k with
  | done => intro _ s p0 W he hp hg; exact ⟨s, W, he, hp, fun _ _ => rfl, hg, rfl⟩
  | rd a k ih =>
    intro hk s p0 W he hp hg
    exact run_cont (k' := k (s.mem a)) (W1 := W) he hg (Step.rd hp)
      (fun p0' k' W' h => by rw [hp] at h; cases h) rfl rfl rfl (ih (s.mem a) (hk _))
  | wr a v k ih =>
    intro hk s p0 W he hp hg
    exact run_cont (k' := k) (W1 := insert a W) he hg (Step.wr hp)
      (fun p0' k' W' h => by rw [hp] at h; cases h) rfl rfl rfl (ih hk)
  | lock l k ih =>
    intro hk s p0 W he hp hg
    exact run_cont (k' := k false) (W1 := W) he hg (Step.lock false hp (fun h => by cases h))
      (fun p0' k' W' h => by rw [hp] at h; cases h) rfl rfl rfl (ih false (hk _))
  | rds a k ih =>
    intro hk s p0 W he hp hg
    exact run_cont (k' := k (s.mem a)) (W1 := W) he hg (Step.rds hp)
      (fun p0' k' W' h => by rw [hp] at h; cases h) rfl rfl rfl (ih (s.mem a) (hk _))
  | start k _ => intro hk; exact False.elim hk
  | rdc a R k ih =>
    intro hk s p0 W he hp hg
    exact run_cont (k' := k (s.mem a)) (W1 := W) he hg (Step.rdc hp)
      (fun p0' k' W' h => by rw [hp] at h; cases h) rfl rfl rfl (ih (s.mem a) (hk _))

/-- **The `leave` step** at an open gate. -/
theorem leave_loc {s s1 : Cfg U64 U64 U64 U64} {p0 : SP} {W : Set U64}
    (he : ExecWPRV12 LP NoV SF P s0 K0 Ch0 s K Ch) (hp : s.ph 0#u64 = .loc p0 .done W) (hg : s.gate = .opn)
    (hS : Step s 0#u64 s1) (hph : s1.ph = Function.update s.ph 0#u64 .idle) :
    ExecWPRV12 LP NoV SF P s0 K0 Ch0 s1 K Ch :=
  .step he hS (stepW_loc hg (fun p h => by rw [hph, Function.update_self] at h; cases h)
    (fun p0' k' W' h => by rw [hp] at h; cases h))

/-- **From the `.start` step to the end** (module docstring): the started `StFree` body runs and core 0 leaves. -/
theorem runEnd {m : U64 → U64} {k : SP} (hk : StFree k)
    (he : ExecWPRV12 LP NoV SF P s0 K0 Ch0 (dfg3 K m k) K Ch) :
    ∃ s : Cfg U64 U64 U64 U64, ExecWPRV12 LP NoV SF P s0 K0 Ch0 s K Ch ∧ NoLoc s ∧ s.log = [.start k] := by
  obtain ⟨s', W', he', hp', hd, hg', hl⟩ := run_loc k hk he (dfg3_ph0 K m k) rfl
  refine ⟨_, leave_loc he' hp' hg' (Step.leave hp') rfl, fun d => ?_, ?_⟩
  · show ¬ (Function.update s'.ph 0#u64 Phase.idle d).IsLoc
    by_cases h : d = 0#u64
    · subst h; rw [Function.update_self]; exact Phase.idle_not_loc
    · rw [Function.update_of_ne h, hd d h, dfg3_ph K m k h]; exact Phase.idle_not_loc
  · show s'.log ++ [.start k] = [.start k]
    rw [hl]
    rfl

end run

/-! ## The tops on an execution with a real start -/

/-- **V12: an execution from the boot that starts the timer-IRQ path, runs its body and leaves.** -/
theorem runEndV12_B (O : LocPlatM.OpaqueH) (a0 a : Fl4Spec.MachineState) :
    ∃ s : Cfg U64 U64 U64 U64,
      ExecWPRV12 (famB a0) (fun i => ¬ IoIx (S := BS) i)
        (StartV2C bst LocPlatM.archT LocPlatM.archT_total a0 LocPlatM.archT LocPlatM.ART modelMR)
        (LocPlatM.locPlat_archT O bs_ext) (s0B O) (KB O) (fun _ => ChB O) s (KB O) (fun _ => ChB O) ∧
      NoLoc s ∧ s.log = [.start (kB O a)] :=
  runEnd (stFree_kB O a) (execStartV12_B O a0 a)

/-- **V13: the same execution with V13's start fact.** -/
theorem runEndV13_B (O : LocPlatM.OpaqueH) (a0 a : Fl4Spec.MachineState) :
    ∃ s : Cfg U64 U64 U64 U64,
      ExecWPRV12 (famB a0) (fun i => ¬ IoIx (S := BS) i)
        (StartV13 bst LocPlatM.archT LocPlatM.archT_total a0 LocPlatM.archT LocPlatM.ART modelMR)
        (LocPlatM.locPlat_archT O bs_ext) (s0B O) (KB O) (fun _ => ChB O) s (KB O) (fun _ => ChB O) ∧
      NoLoc s ∧ s.log = [.start (kB O a)] :=
  runEnd (stFree_kB O a) (execStartV13_B O a0 a)

theorem runAll_one {p : SP} {m m' : U64 → U64} (h : RunAll [p] m m') : Run p m m' := by
  obtain ⟨m1, h1, h2⟩ := h
  have e : m' = m1 := h2
  rw [e]
  exact h1

/-- **V12 applied to an execution with a real start** (module docstring). -/
theorem topV12_B (O : LocPlatM.OpaqueH) (a0 a : Fl4Spec.MachineState) :
    ∃ s : Cfg U64 U64 U64 U64,
      ExecWPRV12 (famB a0) (fun i => ¬ IoIx (S := BS) i)
        (StartV2C bst LocPlatM.archT LocPlatM.archT_total a0 LocPlatM.archT LocPlatM.ART modelMR)
        (LocPlatM.locPlat_archT O bs_ext) (s0B O) (KB O) (fun _ => ChB O) s (KB O) (fun _ => ChB O) ∧
      NoLoc s ∧ s.log = [.start (kB O a)] ∧ Run (.start (kB O a)) memB s.mem := by
  obtain ⟨s, he, hq, hl⟩ := runEndV12_B O a0 a
  have hr := serializable_fl4_localV12 bst LocPlatM.archT LocPlatM.archT_total a0 (LocPlatM.locPlat_archT O bs_ext)
    LocPlatM.mrKeepIoapic_archT (init_B O) (armInv_B O) (fun _ => serExitW_B O) (hc0_B O) (mapsP_B O) he hq
  rw [hl] at hr
  exact ⟨s, he, hq, hl, runAll_one hr⟩

/-- **V13 applied to an execution with a real start.** -/
theorem topV13_B (O : LocPlatM.OpaqueH) (a0 a : Fl4Spec.MachineState) :
    ∃ s : Cfg U64 U64 U64 U64,
      ExecWPRV12 (famB a0) (fun i => ¬ IoIx (S := BS) i)
        (StartV13 bst LocPlatM.archT LocPlatM.archT_total a0 LocPlatM.archT LocPlatM.ART modelMR)
        (LocPlatM.locPlat_archT O bs_ext) (s0B O) (KB O) (fun _ => ChB O) s (KB O) (fun _ => ChB O) ∧
      NoLoc s ∧ s.log = [.start (kB O a)] ∧ Run (.start (kB O a)) memB s.mem := by
  obtain ⟨s, he, hq, hl⟩ := runEndV13_B O a0 a
  have hr := serializable_fl4_localV13 bst LocPlatM.archT LocPlatM.archT_total a0 (LocPlatM.locPlat_archT O bs_ext)
    LocPlatM.mrKeepIoapic_archT (init_B O) (armInv_B O) (fun _ => serExitW_B O) (hc0_B O) (mapsP_B O) he hq
  rw [hl] at hr
  exact ⟨s, he, hq, hl, runAll_one hr⟩

/-! ## A serial step to a new layout (goal 2, the `Cfg` side) -/

section sergen
variable (K : KLayoutP) (m : U64 → U64) (p : SP) (K' : KLayoutP) (m' : U64 → U64)

/-- Core 0 holds the ticket with body `p`; the gate drains. -/
def sfg1 : Cfg U64 U64 U64 U64 :=
  { cfg0 K m with holder := some 0#u64, seen := ∅, ph := Function.update (cfg0 K m).ph 0#u64 (.ser p),
                  gate := if (cfg0 K m).gate = .opn then .draining else (cfg0 K m).gate }
/-- Core 0 scanned itself. -/
def sfg2 : Cfg U64 U64 U64 U64 := { sfg1 K m p with seen := insert 0#u64 (sfg1 K m p).seen }
/-- The gate closed. -/
def sfg3 : Cfg U64 U64 U64 U64 := { sfg2 K m p with gate := .closed }
/-- The serial body ran to `m'`; rule 8's ghosts for `K'`; the gate open again. -/
def sfg4 : Cfg U64 U64 U64 U64 :=
  { sfg3 K m p with mem := m', holder := none, ph := Function.update (sfg3 K m p).ph 0#u64 .idle,
                    gate := if false then .closed else .opn, log := (sfg3 K m p).log ++ [p],
                    own := ownP K', cls := OwnMap.cls K'.toKLayout, ko := OwnMap.ko K'.toKLayout m' }

theorem sfg1_ph0 : (sfg1 K m p).ph 0#u64 = .ser p := by simp [sfg1]
theorem sfg2_ph0 : (sfg2 K m p).ph 0#u64 = .ser p := sfg1_ph0 K m p
theorem sfg3_ph0 : (sfg3 K m p).ph 0#u64 = .ser p := sfg1_ph0 K m p
theorem sfg3_ph {d : U64} (hd : d ≠ 0#u64) : (sfg3 K m p).ph d = .idle := by
  show Function.update (cfg0 K m).ph 0#u64 (.ser p) d = .idle
  simp only [Function.update_of_ne hd, cfg0_ph]

theorem sfg4_ph (d : U64) : (sfg4 K m p K' m').ph d = .idle := by
  by_cases hd : d = 0#u64
  · subst hd; show Function.update (sfg3 K m p).ph 0#u64 .idle 0#u64 = .idle; rw [Function.update_self]
  · exact (Function.update_of_ne hd _ _).trans (sfg3_ph K m p hd)

theorem sfg4_gate : (sfg4 K m p K' m').gate = .opn := rfl
theorem sfg4_mem : (sfg4 K m p K' m').mem = m' := rfl
theorem sfg4_log : (sfg4 K m p K' m').log = [p] := rfl
theorem mapsP_sfg4 : MapsP K' (sfg4 K m p K' m') := ⟨rfl, rfl, rfl⟩
theorem noLoc_sfg4 : NoLoc (sfg4 K m p K' m') := fun d h => by rw [sfg4_ph] at h; exact h

theorem sfg_steps (hr : Run p m m') :
    Step (cfg0 K m) 0#u64 (sfg1 K m p) ∧ Step (sfg1 K m p) 0#u64 (sfg2 K m p) ∧
    Step (sfg2 K m p) 0#u64 (sfg3 K m p) ∧ Step (sfg3 K m p) 0#u64 (sfg4 K m p K' m') :=
  ⟨Step.take p rfl rfl, Step.scan 0#u64 rfl rfl (by rw [sfg1_ph0]; exact id),
    Step.drain rfl rfl (fun d => by
      by_cases hd : d = 0#u64
      · subst hd; exact Or.inl (show (0#u64 : U64) ∈ insert 0#u64 (sfg1 K m p).seen from Set.mem_insert _ _)
      · exact Or.inr (sfg3_ph K m p hd)),
    Step.serial false _ _ _ rfl rfl (sfg3_ph0 K m p) hr⟩

end sergen

section serexec
variable {ι : Type} {LP : PathsP ι} {NoV : ι → Prop}
  {SF : (BS → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop}
  {P : LocPlat bst LocPlatM.archT LocPlatM.ART modelMR} {K : KLayoutP} {Ch0 : U64 → BS → Prop} {m : U64 → U64}

/-- **A serial step from `cfg0 K m` to any exit layout** (module docstring). -/
theorem exec_ser {p : SP} {K' : KLayoutP} {m' : U64 → U64} {Ch' : U64 → BS → Prop}
    (hB : ∀ e, SerExitW P K.toKLayoutV (Ch0 e)) (hc : K.vcpus = ∅ ∧ K.ptes = ptesR K m)
    (hX : ∀ e, SerExitW P K'.toKLayoutV (Ch' e)) (hc' : K'.vcpus = ∅ ∧ K'.ptes = ptesR K' m')
    (hr : Run p m m') :
    ExecWPRV12 LP NoV SF P (cfg0 K m) K Ch0 (sfg4 K m p K' m') K' Ch' := by
  obtain ⟨h1, h2, h3, h4⟩ := sfg_steps K m p K' m' hr
  have e1 := execE (LP := LP) (NoV := NoV) (SF := SF) (P := P) (s0 := cfg0 K m) (s := cfg0 K m) .refl h1
    (stepW_keep hB hc (fun q h => by rw [sfg1_ph0] at h; cases h) (noSt_idle (cfg0_ph K m _)) rfl ⟨rfl, rfl, rfl⟩)
  have e2 := execE e1 h2 (stepW_keep hB hc (fun q h => by rw [sfg2_ph0] at h; cases h)
      (fun p0 k W h => by rw [sfg1_ph0] at h; cases h) rfl ⟨rfl, rfl, rfl⟩)
  have e3 := execE e2 h3 (stepW_keep hB hc (fun q h => by rw [sfg3_ph0] at h; cases h)
      (fun p0 k W h => by rw [sfg2_ph0] at h; cases h) rfl ⟨rfl, rfl, rfl⟩)
  refine .step e3 h4 ?_
  exact
    { arm := fun q h => by rw [sfg4_ph] at h; cases h
      start := fun p0 k W h => by rw [sfg3_ph0] at h; cases h
      serX := fun _ => hX
      serC := fun _ => hc'
      serG := fun _ => mapsP_sfg4 K m p K' m'
      keep := fun h => absurd ⟨rfl, rfl⟩ h }

end serexec

/-- The layout `chainC` picks at a P3 exit `hJ`, with no VCPU and the PTE set `E`. -/
def KX (O : LocPlatM.OpaqueH) {σe : BS} {a3 : Fl4Spec.MachineState} {τ : Fl4Spec.State Unit}
    (hJ : SInvR.G5.JReachU17 (L := bsL) LocPlatM.archT LocPlatM.ART modelMR σe a3 τ) (E : Set U64) : KLayoutP :=
  { toKLayoutV := { toKLayout := (chainC (LocPlatM.locPlat_archT O bs_ext) hJ).1, vcpus := ∅ }, ptes := E }

/-- **Every P3 exit gives `SerExitW` for the layout and chain `chainC` picks there.** -/
theorem serExit_of (O : LocPlatM.OpaqueH) {σe : BS} {a3 : Fl4Spec.MachineState} {τ : Fl4Spec.State Unit}
    (hJ : SInvR.G5.JReachU17 (L := bsL) LocPlatM.archT LocPlatM.ART modelMR σe a3 τ) (E : Set U64) :
    SerExitW (LocPlatM.locPlat_archT O bs_ext) (KX O hJ E).toKLayoutV (chainC (LocPlatM.locPlat_archT O bs_ext) hJ).2 :=
  ⟨σe, a3, τ, hJ, rfl⟩

/-- **From the boot, a serial step to any P3 exit** (module docstring): for every exit `hJ`, memory `m'` reached
from `memB` by the serial body `p`, and the PTE convention at `m'`, an `ExecWPRV12` of V12 / V13's family. -/
theorem serBridge_B (O : LocPlatM.OpaqueH) (a0 : Fl4Spec.MachineState)
    {SF : (BS → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → IxB →
      Prop}
    {σe : BS} {a3 : Fl4Spec.MachineState} {τ : Fl4Spec.State Unit}
    (hJ : SInvR.G5.JReachU17 (L := bsL) LocPlatM.archT LocPlatM.ART modelMR σe a3 τ)
    {p : SP} {m' : U64 → U64} (hr : Run p memB m') {E : Set U64} (hE : E = ptesR (KX O hJ E) m') :
    ExecWPRV12 (famB a0) (fun i => ¬ IoIx (S := BS) i) SF (LocPlatM.locPlat_archT O bs_ext) (s0B O) (KB O)
      (fun _ => ChB O) (sfg4 (KB O) memB p (KX O hJ E) m') (KX O hJ E)
      (fun _ => (chainC (LocPlatM.locPlat_archT O bs_ext) hJ).2) :=
  exec_ser (fun _ => serExitW_B O) (hc0_B O) (fun _ => serExit_of O hJ E) ⟨rfl, hE⟩ hr

end
end Fl4Proofs.P2.BootSt
