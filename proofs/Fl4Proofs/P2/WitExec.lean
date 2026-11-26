/-
# P2 (line wit, gen 1): a non-vacuous execution for `serializable_fl4_localU2`

Audit F4 (audU.md): the premises of `serializable_fl4_localU2` were never shown jointly satisfiable with a local run
in the execution. This module builds, from **any P3 exit state** (`JReachU17 σe`) whose current thread is not the
idle thread (`NonIdle`, io's entry [P]), an execution that meets **every** hypothesis of U2 and contains an IO-port
local run (`handle_ioport_local`'s body) that arms, enters, starts and runs to completion, beside an open gate:

* `wit_exec_io`: `Init s0`, `ArmInv s0`, `SerExitW P K0 Ch0`, `K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem`,
  `MapsP K0 s0`, `ExecWPR (U2's family) (StartV2 …) P s0 K0 Ch0 s K0 Ch0`, `NoLoc s`, and `s.log = [.start q]`
  with `q` the io slot's body at `σe` (its start fact is satU's `startU1_io_satC`, lifted to U2's `StartV2`);
* `wit_U2_io`: U2 applied to it, so U2's conclusion is about this execution (`RunAll [.start q] s0.mem s.mem`).
* `wit_exec_io_conc` / `wit_U2_conc`: the same on the concrete platform of `WitPlat` (`wst`, `warI`), under
  `OpaqueW` [P].

The body is run by `wit_run`: every translated body (`LocalPath.body`, a `tr` tree, then `cutP`) has no `start`
node (`WNoSt`), so the model runs it to `done` step by step; every step meets `Fl4StepWPR` (no arm, no start, no
serial step).

**What is not here.**
1. A `JReachU17` state. P3 has no concrete boot refinement: `JAtZ` (the joint relation and invariants) at a concrete
   store state has never been built (ksfix.md: "Concrete `JAtZ` witness: not attempted"); spec-side boot facts exist
   (`boot_sinvX` …). So `hJ` stays a hypothesis: U2's premises are jointly satisfiable *given* one P3 exit state.
2. Two cores. A second core's start needs a chain state with `L.cpu σ = c₂` at the same memory (`GlueAt`'s core
   clause); `Ch0` is `JReachSt` at `chainC`'s chosen ghosts, and no lemma gives a member with another CPU number
   (audU F4 last bullet). With `wst`, `{σe with cpu := c₂}` is a store state with the same memory, but its
   `JReachU17` / `JAtSt` at the chosen ghosts would need P3's joint invariant re-established for another core.
3. Whether the io run *accepts* depends on `σe` (the current thread's registers and caps): the body here is the
   real `handle_ioport_local` tree at `σe`, run to completion, whichever way it ends.

Named premises: `hJ` (a P3 exit, the state the model starts from), `hct` [P] (`NonIdle`, io's entry fact),
`OpaqueW` [P] (opaque `Fl4Spec` constants, WitPlat). No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P2.E2EPU1S
import Fl4Proofs.P2.WitPlat
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.Wit
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV Fl4Proofs.P2.E2EP
open Fl4Proofs.P2.E2E (LocalPath SP SerStep)
open Fl4Proofs.P2.Serial (Cfg Init ArmInv NoLoc RunAll Step PureGlue Phase Prog Gate)

noncomputable section
open Classical

/-! ## Bodies without `start` nodes -/

/-- A program with no `start` node (a body, not glue). -/
inductive WNoSt : SP → Prop
  | done : WNoSt .done
  | rd {a : U64} {k : U64 → SP} : (∀ v, WNoSt (k v)) → WNoSt (.rd a k)
  | rds {a : U64} {k : U64 → SP} : (∀ v, WNoSt (k v)) → WNoSt (.rds a k)
  | rdc {a : U64} {K : U64 → U64 → Prop} {k : U64 → SP} : (∀ v, WNoSt (k v)) → WNoSt (.rdc a K k)
  | wr {a v : U64} {k : SP} : WNoSt k → WNoSt (.wr a v k)
  | lock {l : U64} {k : Bool → SP} : (∀ b, WNoSt (k b)) → WNoSt (.lock l k)

theorem wNoSt_rdN {R User : U64 → Prop} {cls : U64 → U64 → U64} {ko : U64 → Serial.ClsOwner U64} {c : U64}
    {Wd : Set U64} {q : U64} {k : U64 → SP} (h : ∀ v, WNoSt (k v)) : WNoSt (E2E.rdN R User cls ko c Wd q k) := by
  unfold E2E.rdN
  split_ifs <;> first | exact .rd h | exact .rdc h | exact .rds h

/-- **The translation has no `start` node.** -/
theorem wNoSt_tr {R User : U64 → Prop} {cls : U64 → U64 → U64} {ko : U64 → Serial.ClsOwner U64} {c kb : U64}
    {mk : U64 × U64} {A X : Type} {ar : machine.Arch A} (t : SProg X) :
    ∀ (Wd : Set U64) (a : A), WNoSt (E2E.tr R User cls ko c kb mk ar t Wd a) := by
  induction t with
  | ret _ => intro _ _; exact .done
  | err _ => intro _ _; exact .done
  | rd q k ih => intro Wd a; exact wNoSt_rdN fun v => ih v Wd a
  | rdp q k ih => intro Wd a; exact wNoSt_rdN fun v => wNoSt_rdN fun w => ih (v, w) Wd a
  | wr q v k ih =>
    intro Wd a
    show WNoSt (if User q then _ else _)
    split
    · exact ih Wd a
    · exact .wr (ih _ a)
  | zero _ _ _ _ => intro _ _; exact .done
  | clr _ _ _ _ => intro _ _; exact .done
  | ksb k ih => intro Wd a; exact ih _ Wd a
  | cpu k ih => intro Wd a; exact ih _ Wd a
  | masks k ih => intro Wd a; exact ih _ Wd a
  | arch op k ih =>
    intro Wd a
    show WNoSt (dite _ _ _)
    split
    · exact ih _ Wd _
    · exact .done

/-- **A path's body has no `start` node.** -/
theorem wNoSt_body {own : (U64 → U64) → U64 → Serial.Owner U64 U64} {cls : U64 → U64 → U64}
    {ko : U64 → Serial.ClsOwner U64} {User : U64 → Prop} (P : LocalPath own cls ko User) (σ : P.S) (a : P.A) :
    WNoSt (P.body σ a) :=
  wNoSt_tr P.p ∅ a

/-- **`cutP` keeps it.** -/
theorem wNoSt_cutP {E User : U64 → Prop} {cls : U64 → U64 → U64} {ko : U64 → Serial.ClsOwner U64} {c : U64}
    {p : SP} (h : WNoSt p) : ∀ Wd, WNoSt (cutP E User cls ko c p Wd) := by
  induction h with
  | done => intro _; exact .done
  | @rd a k _ ih =>
    intro Wd
    show WNoSt (if E a ∧ a ∉ Wd then _ else _)
    split
    · show WNoSt (if _ then _ else _)
      split
      · exact .rdc fun v => ih v Wd
      · exact .rds fun v => ih v Wd
    · exact .rd fun v => ih v Wd
  | rds _ ih => intro Wd; exact .rds fun v => ih v Wd
  | rdc _ ih => intro Wd; exact .rdc fun v => ih v Wd
  | wr _ ih => intro Wd; exact .wr (ih _)
  | lock _ ih => intro Wd; exact .lock fun b => ih b Wd

/-! ## Steps beside an open gate -/

section exec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {ι : Type} {LP : PathsP ι}
  {SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop}
  {P : LocPlat st arI AR MR}

theorem wit_notSer {s : Cfg U64 U64 U64 U64} {c : U64} (hg : s.gate = .opn) : ¬ SerStep s c := by
  intro hs
  have h := hs.1
  rw [hg] at h
  cases h

/-- **A step beside the open gate that arms only glue and starts nothing.** -/
theorem wit_step {s s' : Cfg U64 U64 U64 U64} {K : KLayoutP} {Ch : S → Prop} {c : U64} (hg : s.gate = .opn)
    (ha : ∀ p, s'.ph c = .arm p → PureGlue p) (hst : ∀ p0 k W, s.ph c ≠ .loc p0 (.start k) W) :
    Fl4StepWPR LP SF P s K Ch c s' K Ch where
  arm := ha
  start p0 k W h := absurd h (hst p0 k W)
  serX hs := absurd hs (wit_notSer hg)
  serC hs := absurd hs (wit_notSer hg)
  serG hs := absurd hs (wit_notSer hg)
  keep _ := ⟨rfl, rfl⟩

/-- **A body without `start` runs to `done`** beside the open gate, other cores untouched. -/
theorem wit_run {s0 : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} {c : U64} {p0 p : SP}
    (hp : WNoSt p) :
    ∀ (s : Cfg U64 U64 U64 U64) (W : Set U64), ExecWPR LP SF P s0 K0 Ch0 s K Ch → s.gate = .opn →
      s.ph c = .loc p0 p W →
      ∃ (s' : Cfg U64 U64 U64 U64) (W' : Set U64), ExecWPR LP SF P s0 K0 Ch0 s' K Ch ∧ s'.gate = .opn ∧
        s'.log = s.log ∧ (∀ d, d ≠ c → s'.ph d = s.ph d) ∧ s'.ph c = .loc p0 .done W' := by
  induction hp with
  | done => intro s W hE hg hph; exact ⟨s, W, hE, hg, rfl, fun _ _ => rfl, hph⟩
  | @rd a k _ ih =>
    intro s W hE hg hph
    obtain ⟨s', W', h1, h2, h3, h4, h5⟩ := ih (s.mem a) _ W
      (ExecWPR.step hE (Step.rd hph) (wit_step hg (fun p h => by simp at h)
        (fun p0' k' W' h => by rw [hph] at h; cases h))) hg (by simp)
    exact ⟨s', W', h1, h2, h3, fun d hd => (h4 d hd).trans (by simp [hd]), h5⟩
  | @rds a k _ ih =>
    intro s W hE hg hph
    obtain ⟨s', W', h1, h2, h3, h4, h5⟩ := ih (s.mem a) _ W
      (ExecWPR.step hE (Step.rds hph) (wit_step hg (fun p h => by simp at h)
        (fun p0' k' W' h => by rw [hph] at h; cases h))) hg (by simp)
    exact ⟨s', W', h1, h2, h3, fun d hd => (h4 d hd).trans (by simp [hd]), h5⟩
  | @rdc a K' k _ ih =>
    intro s W hE hg hph
    obtain ⟨s', W', h1, h2, h3, h4, h5⟩ := ih (s.mem a) _ W
      (ExecWPR.step hE (Step.rdc hph) (wit_step hg (fun p h => by simp at h)
        (fun p0' k' W' h => by rw [hph] at h; cases h))) hg (by simp)
    exact ⟨s', W', h1, h2, h3, fun d hd => (h4 d hd).trans (by simp [hd]), h5⟩
  | @wr a v k _ ih =>
    intro s W hE hg hph
    obtain ⟨s', W', h1, h2, h3, h4, h5⟩ := ih _ (insert a W)
      (ExecWPR.step hE (Step.wr hph) (wit_step hg (fun p h => by simp at h)
        (fun p0' k' W' h => by rw [hph] at h; cases h))) hg (by simp)
    exact ⟨s', W', h1, h2, h3, fun d hd => (h4 d hd).trans (by simp [hd]), h5⟩
  | @lock l k _ ih =>
    intro s W hE hg hph
    obtain ⟨s', W', h1, h2, h3, h4, h5⟩ := ih false _ W
      (ExecWPR.step hE (Step.lock false hph (fun h => absurd h (by decide))) (wit_step hg
        (fun p h => by simp at h) (fun p0' k' W' h => by rw [hph] at h; cases h))) hg (by simp)
    exact ⟨s', W', h1, h2, h3, fun d hd => (h4 d hd).trans (by simp [hd]), h5⟩

end exec

/-! ## The execution -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- U2's family of paths. -/
abbrev LPU2 :=
  PathsP.sum (fl4LocW11JA st ar hA (masksWr_plain st) L.total a0)
    (PathsP.sum (PathsP.sum (delPteSlot st ar hA (masksWr_plain st)) (invSlotU st ar hA (masksWr_plain st)))
      (cmSlotU st ar hA (masksWr_plain st)))

/-- The epoch layout at a P3 exit: `chainC`'s layout, no VCPU, the PTEs by the reachability convention. -/
def witK (P : LocPlat st arI AR MR) {σe : S} {a3 : A3} {τ : Fl4Spec.State Unit}
    (hJ : Fl4Proofs.P3.SInvR.G5.JReachU17 (L := L) arI AR MR σe a3 τ) : KLayoutP :=
  { toKLayoutV := { toKLayout := (chainC P hJ).1, vcpus := ∅ },
    ptes := ptesR ({ toKLayoutV := { toKLayout := (chainC P hJ).1, vcpus := ∅ }, ptes := ∅ } : KLayoutP)
      (L.mem σe) }

/-- The start configuration: memory of `σe`, gate open, every core idle, no lock held, the ghost maps of `K`. -/
def witS0 (K : KLayoutP) (m : U64 → U64) : Cfg U64 U64 U64 U64 where
  mem := m
  gate := .opn
  holder := none
  seen := ∅
  lk := fun _ => none
  ph := fun _ => .idle
  own := ownP K
  cls := OwnMap.cls K.toKLayout
  ko := OwnMap.ko K.toKLayout m
  log := []

/-- **U2's premises with one IO-port local run, from any P3 exit with a non-idle current thread** (module
docstring). -/
theorem wit_exec_io (P : LocPlat st arI AR MR) {σe : S} {a3 : A3} {τ : Fl4Spec.State Unit}
    (hJ : Fl4Proofs.P3.SInvR.G5.JReachU17 (L := L) arI AR MR σe a3 τ) (hct : NonIdle st arI AR MR σe) :
    ∃ (s0 s : Cfg U64 U64 U64 U64) (K0 : KLayoutP) (Ch0 : S → Prop) (q : SP),
      Init s0 ∧ ArmInv s0 ∧ SerExitW P K0.toKLayoutV Ch0 ∧ (K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem) ∧
      MapsP K0 s0 ∧
      ExecWPR (LPU2 st ar hA a0) (StartV2 st ar hA a0 arI AR MR) P s0 K0 Ch0 s K0 Ch0 ∧ NoLoc s ∧
      s.log = [.start q] ∧ s0.mem = L.mem σe := by
  let K0 := witK st P hJ
  let Ch0 := (chainC P hJ).2
  let s0 := witS0 K0 (L.mem σe)
  let c := L.cpu σe
  have hB : SerExitW P K0.toKLayoutV Ch0 := ⟨σe, a3, τ, hJ, rfl⟩
  have hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem := ⟨rfl, rfl⟩
  obtain ⟨hK, hU⟩ := okP_R hB hc0
  have hC : ChainOf (L := L) arI AR MR σe K0.toKLayoutV.toKLayout Ch0 := chainC_spec P hJ
  have hσ : Ch0 σe := by
    obtain ⟨_, _, _, _, _, _, _, _, h⟩ := chainC_spec P hJ
    exact h
  obtain ⟨Ac, H⟩ := startU1_io_satC st ar hA (masksWr_plain st) L.total a0
    (fun _ _ _ _ _ _ _ _ (_ : Empty) => False) hK hU hC hσ rfl hct a0
  let j : IoArg S := ⟨0#i64, {c : U64 | c.val < K0.ncores}, K0.heap.omega, K0.heap.frame, Ac,
    fun _ _ => False, fun K' m' s => IoQ st {c : U64 | c.val < K0.ncores} K0.heap.omega K0.heap.frame Ac
      K'.toKLayout m' s⟩
  obtain ⟨q, hq⟩ := H j rfl rfl rfl rfl rfl rfl
  have hSU : StartU st ar hA (masksWr_plain st) L.total a0 arI AR MR Ch0 K0 (L.mem σe) hK hU c (fun _ => False) q
      (.io j) := hq
  have hNo : WNoSt q := by
    obtain ⟨q0, ⟨_, σ', a', _, _, _, _, hq0⟩, hqq⟩ := hSU
    rw [hqq, hq0]
    exact wNoSt_cutP (wNoSt_body _ _ _) ∅
  have hSV : StartV2 st ar hA a0 arI AR MR Ch0 K0 (L.mem σe) hK hU c (fun _ => False) q (.inl (.io j)) :=
    ⟨⟨fun _ => False, rfl⟩, fun _ => hSU⟩
  -- arm `.start q`, enter, start
  have hE0 : ExecWPR (LPU2 st ar hA a0) (StartV2 st ar hA a0 arI AR MR) P s0 K0 Ch0 s0 K0 Ch0 := .refl
  have hE1 := ExecWPR.step hE0 (Step.arm (s := s0) (c := c) (.start q) rfl)
    (wit_step (K := K0) (Ch := Ch0) rfl (fun p h => by
        simp at h
        subst h
        exact PureGlue.start q)
      (fun _ _ _ h => by simp [s0, witS0] at h))
  have hE2 := ExecWPR.step hE1 (Step.enter (c := c) (p := .start q) (by simp) rfl)
    (wit_step (K := K0) (Ch := Ch0) rfl (fun p h => by simp at h) (fun _ _ _ h => by simp at h))
  have hph2 : ({ { s0 with ph := Function.update s0.ph c (.arm (.start q)) } with
      ph := Function.update (Function.update s0.ph c (.arm (.start q))) c (.loc (.start q) (.start q) ∅) } :
      Cfg U64 U64 U64 U64).ph c = .loc (.start q) (.start q) ∅ := by simp
  have hE3 := ExecWPR.step hE2 (Step.start hph2)
    { arm := fun p h => by simp at h
      start := fun p0' k W h hK' hU' => by
        have h' : (Phase.loc (.start q) (.start q) ∅ : Phase U64 U64 U64) = .loc p0' (.start k) W := hph2.symm.trans h
        simp only [Phase.loc.injEq, Prog.start.injEq] at h'
        obtain ⟨-, h2, -⟩ := h'
        subst h2
        have hs : (fun l : U64 => (none : Option U64) = some c) = fun _ => False := by
          funext l; simp
        exact ⟨.inl (.io j), by
          show StartV2 st ar hA a0 arI AR MR Ch0 K0 (L.mem σe) hK' hU' c (fun l : U64 => (none : Option U64) = some c) q
            (.inl (.io j))
          rw [hs]; exact hSV⟩
      serX := fun hs => absurd hs (wit_notSer rfl)
      serC := fun hs => absurd hs (wit_notSer rfl)
      serG := fun hs => absurd hs (wit_notSer rfl)
      keep := fun _ => ⟨rfl, rfl⟩ }
  -- the body
  obtain ⟨s4, W4, hE4, hg4, hl4, ho4, hc4⟩ := wit_run (c := c) (p0 := .start q) hNo _ ∅ hE3 rfl (by simp)
  have hE5 := ExecWPR.step hE4 (Step.leave hc4)
    (wit_step hg4 (fun p h => by simp at h) (fun _ _ _ h => by rw [hc4] at h; cases h))
  refine ⟨s0, _, K0, Ch0, q, ⟨rfl, fun d => Phase.idle_not_loc⟩, fun _ _ h => by simp [s0, witS0] at h, hB, hc0,
    ⟨rfl, rfl, rfl⟩, hE5, ?_, ?_, rfl⟩
  · intro d
    by_cases hd : d = c
    · rw [hd]; simp [Phase.IsLoc]
    · have e : s4.ph d = Phase.idle := by rw [ho4 d hd]; simp [hd, s0, witS0]
      simp [hd, e, Phase.IsLoc]
  · show s4.log ++ [Prog.start q] = [Prog.start q]
    rw [hl4]
    try rfl

include ar hA a0 in
/-- **U2's conclusion is about this execution.** -/
theorem wit_U2_io (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR) {σe : S} {a3 : A3}
    {τ : Fl4Spec.State Unit} (hJ : Fl4Proofs.P3.SInvR.G5.JReachU17 (L := L) arI AR MR σe a3 τ)
    (hct : NonIdle st arI AR MR σe) :
    ∃ (s0 s : Cfg U64 U64 U64 U64) (q : SP), s.log = [.start q] ∧ s0.mem = L.mem σe ∧ NoLoc s ∧
      RunAll s.log s0.mem s.mem := by
  obtain ⟨s0, s, K0, Ch0, q, h0, hA0, hB, hc0, hM0, h, hq, hl, hm⟩ := wit_exec_io st ar hA a0 P hJ hct
  exact ⟨s0, s, q, hl, hm, hq, serializable_fl4_localU2 st ar hA a0 P hIoa h0 hA0 hB hc0 hM0 h hq⟩

end top

/-! ## On the concrete platform -/

/-- An arch state for the bodies. -/
def wa0 : Fl4Spec.MachineState := Classical.ofNonempty

/-- **The concrete platform, every premise of U2, one IO-port local run** (from a P3 exit of the concrete
platform with a non-idle current thread, and `OpaqueW` [P]). -/
theorem wit_exec_io_conc (O : OpaqueW) {σe : WSt} {a3 : Fl4Spec.MachineState} {τ : Fl4Spec.State Unit}
    (hJ : Fl4Proofs.P3.SInvR.G5.JReachU17 (L := wL) warI wAR wMR σe a3 τ) (hct : NonIdle wst warI wAR wMR σe) :
    ∃ (s0 s : Cfg U64 U64 U64 U64) (K0 : KLayoutP) (Ch0 : WSt → Prop) (q : SP),
      Init s0 ∧ ArmInv s0 ∧ SerExitW (wit_locPlat O) K0.toKLayoutV Ch0 ∧
      (K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem) ∧ MapsP K0 s0 ∧
      ExecWPR (LPU2 wst warI warI_total wa0) (StartV2 wst warI warI_total wa0 warI wAR wMR) (wit_locPlat O)
        s0 K0 Ch0 s K0 Ch0 ∧ NoLoc s ∧ s.log = [.start q] ∧ s0.mem = wmem σe :=
  wit_exec_io wst warI warI_total wa0 (wit_locPlat O) hJ hct

theorem wit_U2_conc (O : OpaqueW) {σe : WSt} {a3 : Fl4Spec.MachineState} {τ : Fl4Spec.State Unit}
    (hJ : Fl4Proofs.P3.SInvR.G5.JReachU17 (L := wL) warI wAR wMR σe a3 τ) (hct : NonIdle wst warI wAR wMR σe) :
    ∃ (s0 s : Cfg U64 U64 U64 U64) (q : SP), s.log = [.start q] ∧ s0.mem = wmem σe ∧ NoLoc s ∧
      RunAll s.log s0.mem s.mem :=
  wit_U2_io wst warI warI_total wa0 (wit_locPlat O) wit_ioapic hJ hct

end
end Fl4Proofs.P2.Wit
