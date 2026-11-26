/-
# P2 (line p3mc, gen 2): `serializable_fl4_localU6`, one P3 chain per core, start facts at the core's view

U2, U4 and U5 ask every local start for a state of **one** epoch chain `Ch`. Each `Ch` state is a P3 state, and at a
P3 state every TCB's `AFFINITY` word equals the state's `cpu` (`GlueCross.slJAt_aff`). So U5's start [P] forces the
physical `AFFINITY` word of every TCB to be the starting core (`GlueCross.start_aff`), and two starts by different
cores in one epoch are impossible (`GlueCross.start_two_cores`). On real SMP, with threads (at least the idle
threads) homed on two cores, U5's start premise is false at the first local start.

U6 replaces the one chain with **one chain per core**, `Ch : U64 → S → Prop`, and asks core `c`'s start fact of
`Ch c` at **core `c`'s view** `CoreView.view K c ρ` of a memory `ρ` that `c` cannot tell from the physical one
(`VEq ρ s.mem`, U5's relation). The view rewrites exactly the words that say another core exists (gen 1,
`P2/CoreView.lean`): other cores' threads become passive and are homed on `c`, other cores' SCs are put on `c`, and
other cores' queues are emptied. At every core's view of every memory, every TCB is homed on that core (`view_aff`),
so the per-core chains are not refuted.

## Where the view appears, and where it does not
* **Only in premises and start facts.** The view appears in `Fl4StepWPRV.start`, in its two named parts `VPte` and
  `VSafe`, and in the family form `ViewSafe`.
* **The conclusion is about the real execution.** `serializable_fl4_localU6` concludes
  `RunAll s.log s0.mem s.mem`: from the physical initial memory, running the completed entries serially in
  completion order gives the physical final memory. This is U5's conclusion, word for word. Soundness goes through
  `Safe … s.mem k`, the body's safety at the **physical** memory (`exec_safeRunPV`), into gen 1 of glue's
  `SerialH.XSafeRunH` and `serializable_safeXH`. Neither mentions the view.

## `VEq` does not survive the view (proved: `veq_view_false`), hence the read premise `VSafe` [J]
`body_safeH` turns a start at `ρ'` into `Safe` at `μ` given `VEq ρ' μ`. At `ρ' := view K c ρ` this fails as soon as
some TCB is homed elsewhere. Its `AFFINITY` word is gate-owned, so readable (`PO`) by every core, and `VEq`'s
second clause would make the view agree with `μ` there. But the view says `c` and `μ` says the other core
(`veq_view_false`). Owners differ too: in the view the other core's thread words are owned by `c`. So the starting
core *can* tell the view from `ρ`, on gate words and on owners, and the safety of the body read off the view state
has to be a per-path premise:
* **`VSafe` [J]** (per start, consumed only when `view K c ρ ≠ ρ`): the body that a start at the view gives is
  `Safe` at the physical memory. The family form is **`ViewSafe` [J]**, one statement per path family, for later
  per-slot discharge (`vSafe_of_viewSafe` feeds it to every start).
  Justification (DESIGN §7): a local path declines on a thread's `AFFINITY` before it touches another core's thread.
  `Safe` is about the translated program, which branches on the values it reads. At the physical memory the
  `AFFINITY` read returns the other core and the program takes the decline branch, whose writes (`FAULT_IP`, the own
  node's timestamps) are held. The words the view rewrites are gate- or other-core-owned (`repl_own`), and the
  accepted branch, by DESIGN §7, reads none of them.
  Discharge, per slot: re-prove `body_safeH` with the `VEq` clauses restricted to the path's read, write and decline
  sets (`PathObl.read_own`/`write_own`), with `sim`'s check memory taken off the rewritten words.
* **`VPte` [P]** (per start): the view keeps the epoch's PTE convention witness. If `ρ` agrees on gate words with
  some configuration whose PTE set is `ptesR` of its memory, so does `view K c ρ`. Justification: `ptesR` reads the
  ASID table, ASID pools and paging structures. None of these is a TCB, SC or node word, and the view changes only
  those (`repl2_region`). Discharge: a read-set lemma for `ptesR` from the layout facts. It is trivial wherever the
  view is the identity (`vPte_of_eq`).

## U6 is not weaker than U5 on single-core-homed executions (proved)
`Homed K c ρ`: every TCB has `AFFINITY = c`, every SC has `CORE = c`, and other cores' queue words are zero. There
the view is the identity (`CoreView.view_eq_self`). **`execWPRV_of_WPRRHo`**: every U5 execution whose starts have
homed witnesses (`ExecWPRRHo`) is a U6 execution, with `Ch e := Ch` for every core. Its `VPte` and `VSafe` hold
trivially (`VSafe` is guarded by `view ≠ ρ`). **`serializable_fl4_localU5Ho`** derives U5's conclusion on those
executions from U6, under U5's premises with no `VSafe` / `ViewSafe` / `VPte` assumption.
Homed starts are the ones U5's start [P] already forces: by `GlueCross.start_aff`, every U5 start has every
`AFFINITY` word equal to the starting core. U5 admits no execution in which two cores start in one epoch.

## Two cores in one epoch (proved: `CoreView.u6_two_cores`, `CoreView.start_affV`)
This is the contrapositive of `start_two_cores`, at the level at which that theorem refutes U5. For any layout with
two TCBs `t₁ ≠ t₂` and any two cores `c₁ ≠ c₂`, there is a physical memory `μ` that homes `t₁` on `c₁` and `t₂`
on `c₂`, at which:
* **no** state of **any** chain (`ChainLay`), of any core, matches any memory view-equal to `μ` (U5 is refuted for
  both cores at once);
* **both** cores' views of `μ` meet every memory equation a P3 state of that core imposes on `AFFINITY` and `CORE`
  (`slJAt_aff`, `SchedRel.core`), with `ρ := μ` admissible (`VEq μ μ`) for both.
`start_affV`: in U6's start shape, `start_aff`'s conclusion becomes `view K e ρ (AFFINITY t) = e`, which holds for
every `ρ`. So it constrains no physical memory, and two starts by different cores with per-core chains no longer give
`c₁ = c₂`. The remaining content of the start [P] is that `Ch c` holds a P3 state at `c`'s view (the boot/rely
[P]/[J] of gen 3). It is not refuted, and it is not discharged here. No concrete P3 chain state exists anywhere in the
repo to instantiate it.

## Store surjectivity: no [W] needed (proved: `CoreView.modelStore_surj`)
The plan's [W] `StoreSurj` asks for a store state with any given memory, `ksb` and `cpu`. It is **not used** by
U6, because gen 2 never builds a store state at a view. For the concrete model store `P1.modelStoreWithMasks` it is
**proved** (`modelStore_surj`). For an abstract `LawfulStore` it is not derivable, since nothing forbids a lawful store
whose `cpu` is constant. No [W] is introduced.

## Premises of `serializable_fl4_localU6` vs `serializable_fl4_localU5`
* **Changed, `start` [P]**: was `∃ ρ, VEq ρ s.mem ∧ ∃ i, SF Ch K ρ …`. Now
  `∃ ρ, VEq ρ s.mem ∧ ∃ i, SF (Ch c) K (view K c ρ) … ∧ VPte ∧ VSafe`: core `c`'s own chain, at `c`'s view.
* **Added, `VPte` [P]** (inside `start`; justification above).
* **Added, `VSafe` [J]** (inside `start`, guarded by `view ≠ ρ`; family form `ViewSafe` [J]; justification above).
* **Changed, `serX` [P] and `hB`**: a serial exit chooses one chain per core
  (`∀ e, SerExitW P K' (Ch' e)`), each the P3 chain of a P3 state. Justification: P3 at core `e`'s view of the exit
  memory. Gen 3 derives this via view invariance at quiescent points.
* **Unchanged**: `P : LocPlat`, `hIoa`, `h0`, `hA0`, `hc0`, `hM0`, `arm` [P], `serC`, `serG` [P], `keep`,
  `HwStepP`, `hq`, the slot records inside `StartV2`, and `yb` [J] (inside the slots).
* Not introduced: [W] `StoreSurj`.

No `kernel_entry_reach*` theorem and no per-path obligation is re-proved. No existing statement or file changed except
the root import list.
-/
import Fl4Proofs.P2.E2EPU5
import Fl4Proofs.P2.CoreView
import Fl4Proofs.P2.GlueCross
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.CoreView
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap
open Fl4Proofs.P2.OwnMapP (KLayoutP ownP RegionOKP)

noncomputable section
open Classical

/-! ## Homed memories: where the view is the identity -/

/-- **All of `m` is homed on core `c`** (module docstring): every TCB has `AFFINITY = c`, every SC has `CORE = c`, and
other cores' queue words are zero. -/
def Homed (K : KLayout) (c : U64) (m : U64 → U64) : Prop :=
  (∀ t, K.heap t = some .tcb → m (fld t oAFFINITY) = c) ∧
  (∀ p b, region K b = .sc p → m (fld p 16#u64) = c) ∧
  (∀ d b, region K b = .node d → d ≠ c → QWord (nodeOff K d b) → m b = 0#u64)

/-- **On a homed memory the view is the identity.** -/
theorem view_eq_self {K : KLayout} (hK : RegionOK K) {c : U64} {m : U64 → U64} (h : Homed K c m) :
    view K c m = m := by
  funext b
  cases hr : region K b with
  | tcb t => exact view_home hr (h.1 t (hK.tcbOf t b hr))
  | sc p => exact view_sc_home hr (h.2.1 p b hr)
  | node d =>
    by_cases hd : d = c
    · subst hd; exact view_node_self hr
    · by_cases hq : QWord (nodeOff K d b)
      · rw [view_node_other hr hd hq, h.2.2 d b hr hd hq]
      · exact view_none (by simp only [repl, repl2, hr, nodeRepl, if_neg hd, if_neg hq])
  | slot p => exact view_none (by simp only [repl, repl2, hr])
  | ntfn p => exact view_none (by simp only [repl, repl2, hr])
  | obj p => exact view_none (by simp only [repl, repl2, hr])
  | none => exact view_none (by simp only [repl, repl2, hr])

/-! ## `VEq` does not survive the view -/

/-- **The starting core can tell its view from the memory** (module docstring): if some TCB of the layout is homed off
`c` in `ρ`, no memory `μ` with `VEq ρ μ` has `VEq (view K c ρ) μ`. The `AFFINITY` word is gate-owned, so `c` may
read it, and the view says `c` there. -/
theorem veq_view_false {K : KLayoutP} (hK : RegionOKP K) {cls : U64 → U64 → U64}
    {ko ko' : U64 → Serial.ClsOwner U64} {c : U64} {hs : U64 → Prop} {ρ μ : U64 → U64}
    {t : U64} (ht : K.heap t = some .tcb) (hρ : ρ (fld t oAFFINITY) ≠ c)
    (hV : Serial.VEq (ownP K) cls ko c hs ρ μ) : ¬ Serial.VEq (ownP K) cls ko' c hs (view K.toKLayout c ρ) μ := by
  intro hV'
  apply hρ
  rw [GlueCross.veq_aff hK hV ht, ← GlueCross.veq_aff hK hV' ht]
  exact view_aff hK.base.base ht c ρ

/-! ## Two cores in one epoch -/

/-- Two TCBs have two `AFFINITY` words. -/
theorem aff_fld_ne {K : KLayout} (hK : RegionOK K) {t₁ t₂ : U64} (h₁ : K.heap t₁ = some .tcb)
    (h₂ : K.heap t₂ = some .tcb) (hne : t₁ ≠ t₂) : fld t₁ oAFFINITY ≠ fld t₂ oAFFINITY := by
  intro e
  have r1 := (hK.tcb t₁ h₁ oAFFINITY (Or.inl rfl)).1
  have r2 := (hK.tcb t₂ h₂ oAFFINITY (Or.inl rfl)).1
  rw [e, r2] at r1
  injection r1 with h
  exact hne h.symm

section witness
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **`start_aff` in U6's start shape constrains no memory** (module docstring): a state `σ'` of core `L.cpu σ'`'s chain
that equals that core's view of `ρ` off user words has every TCB's `AFFINITY` word equal to its `cpu`. This is
`slJAt_aff`'s equation, and it holds at `view K (L.cpu σ') ρ` for **every** `ρ` (`view_aff`). So, unlike
`GlueCross.start_aff`, it says nothing about the physical memory. -/
theorem start_affV {K : KLayoutP} (hK : RegionOKP K) {Ch : S → Prop} (hC : PathObl.ChainLay (L := L) K.toKLayout Ch)
    {σ' : S} (h' : Ch σ') {ρ : U64 → U64}
    (hρ : ∀ x, P1.Aligned x → x ∉ K.user → L.mem σ' x = view K.toKLayout (L.cpu σ') ρ x) {t : U64}
    (ht : K.heap t = some .tcb) :
    L.mem σ' (fld t oAFFINITY) = L.cpu σ' ∧ view K.toKLayout (L.cpu σ') ρ (fld t oAFFINITY) = L.cpu σ' := by
  obtain ⟨ha, hu, e⟩ := GlueCross.slJAt_aff (hC.bun σ' h') ht
  exact ⟨e, (hρ _ ha hu).symm.trans e⟩

/-- **Two cores, one epoch: refuted for U5, consistent for U6** (module docstring; the contrapositive of
`GlueCross.start_two_cores`). For two TCBs and two cores there is a physical memory homing one TCB on each core, at
which (1) no state of any chain matches any memory view-equal to it, for any core (U5's start refuted for both cores),
and (2) both cores' views home every TCB and every SC on that core, the equations P3 imposes at that core's states,
with `ρ := μ` view-equal for both. -/
theorem u6_two_cores {K : KLayoutP} (hK : RegionOKP K) {t₁ t₂ : U64} (h₁ : K.heap t₁ = some .tcb)
    (h₂ : K.heap t₂ = some .tcb) (hne : t₁ ≠ t₂) {c₁ c₂ : U64} (hc : c₁ ≠ c₂) :
    ∃ μ : U64 → U64, μ (fld t₁ oAFFINITY) = c₁ ∧ μ (fld t₂ oAFFINITY) = c₂ ∧
      (∀ (Ch : S → Prop), PathObl.ChainLay (L := L) K.toKLayout Ch → ∀ σ', Ch σ' → ∀ ρ : U64 → U64,
        (∀ x, P1.Aligned x → x ∉ K.user → L.mem σ' x = ρ x) →
        ∀ (cls : U64 → U64 → U64) (ko : U64 → Serial.ClsOwner U64) (hs : U64 → Prop),
        ¬ Serial.VEq (ownP K) cls ko (L.cpu σ') hs ρ μ) ∧
      (∀ e, e = c₁ ∨ e = c₂ →
        (∀ t, K.heap t = some .tcb → view K.toKLayout e μ (fld t oAFFINITY) = e) ∧
        (∀ p b, region K.toKLayout b = .sc p → view K.toKLayout e μ (fld p 16#u64) = e) ∧
        ∀ (cls : U64 → U64 → U64) (ko : U64 → Serial.ClsOwner U64) (hs : U64 → Prop),
          Serial.VEq (ownP K) cls ko e hs μ μ) := by
  have hB := hK.base.base
  refine ⟨Function.update (fun _ => c₁) (fld t₂ oAFFINITY) c₂, ?_, Function.update_self .., ?_, ?_⟩
  · rw [Function.update_of_ne (aff_fld_ne hB h₁ h₂ hne)]
  · intro Ch hC σ' hσ' ρ hρ cls ko hs hV
    have a1 := GlueCross.start_aff hK hC hσ' hρ hV h₁
    have a2 := GlueCross.start_aff hK hC hσ' hρ hV h₂
    rw [Function.update_of_ne (aff_fld_ne hB h₁ h₂ hne)] at a1
    rw [Function.update_self] at a2
    exact hc (a1.trans a2.symm)
  · intro e _
    exact ⟨fun t ht => view_aff hB ht e _, fun p b hb => view_sc_core hB hb e _,
      fun _ _ _ => ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩⟩

end witness

/-! ## Store surjectivity of the model store -/

/-- **The model store reaches every memory, `ksb` and `cpu`** (module docstring: the plan's [W] `StoreSurj`, proved
for the concrete store, and not needed by U6). -/
theorem modelStore_surj (masks : U64 × U64) (m : U64 → U64) (k c : U64) :
    ∃ s : P1.ModelState, @LawfulStore.mem _ (P1.modelStoreWithMasks masks) _ s = m ∧
      @LawfulStore.ksb _ (P1.modelStoreWithMasks masks) _ s = k ∧
      @LawfulStore.cpu _ (P1.modelStoreWithMasks masks) _ s = c :=
  ⟨(m, k, c), rfl, rfl, rfl⟩

end
end Fl4Proofs.P2.CoreView

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld)
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg NextH VEq SafeStepH XSafeRunH
  serializable_safeXH xsafeRunH_inv xsafeRunH_agree allowed_of_sinv veq_start Safe)

noncomputable section
open Classical

/-! ## The named parts of the start at the view -/

/-- The epoch's PTE convention, witnessed for a memory `m` on gate words (`hSF`'s second hypothesis in U2/U4/U5). -/
def EpochPte (K : KLayoutP) (m : U64 → U64) : Prop :=
  ∃ s1 : Cfg U64 U64 U64 U64, (K.vcpus = ∅ ∧ K.ptes = ptesR K s1.mem) ∧ ∀ x, GateW K x → m x = s1.mem x

/-- **[P] The view keeps the epoch's PTE convention** (module docstring): a memory `ρ` with a convention witness on
gate words gives one for core `c`'s view of `ρ`. Justification: `ptesR` reads the ASID table, ASID pools and paging
structures, and the view rewrites only TCB, SC and node words (`CoreView.repl2_region`). Trivial where the view is the
identity (`vPte_of_eq`). -/
def VPte (K : KLayoutP) (c : U64) (ρ : U64 → U64) : Prop :=
  EpochPte K ρ → EpochPte K (CoreView.view K.toKLayout c ρ)

theorem vPte_of_eq {K : KLayoutP} {c : U64} {ρ : U64 → U64} (h : CoreView.view K.toKLayout c ρ = ρ) :
    VPte K c ρ := by
  intro hE; rw [h]; exact hE

/-- **[J] The read premise at one start** (module docstring): where core `c`'s view of `ρ` is not `ρ`, the body
that a start of path `i` at the view gives is `Safe` at the physical memory. Justification: DESIGN §7. A local path
declines on a thread's `AFFINITY` before touching another core's thread, and at the physical memory the program
takes that decline branch. Every word the view rewrites is gate- or other-core-owned (`CoreView.repl_own`), and no
accepted branch reads one. -/
def VSafe {ι : Type} (LP : PathsP ι) (s : Cfg U64 U64 U64 U64) (K : KLayoutP) (c : U64) (k : SP)
    (hK : RegionOKP K) (hU : UserOKP K) (ρ : U64 → U64) (i : ι) : Prop :=
  CoreView.view K.toKLayout c ρ ≠ ρ →
    StartAt (LP i K (CoreView.view K.toKLayout c ρ) hK hU) c (fun l => s.lk l = some c)
      (CoreView.view K.toKLayout c ρ) k →
    Safe s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem k

/-- **[J] The read premise of a path family** (module docstring; the per-slot discharge target): a start of any path
of the family at core `c`'s view of `ρ` gives a body that is `Safe` at every `μ` that `c` cannot tell from `ρ`, where
the view differs from `ρ`. -/
def ViewSafe {ι : Type} (LP : PathsP ι) : Prop :=
  ∀ i (K : KLayoutP) (hK : RegionOKP K) (hU : UserOKP K) (c : U64) (hs : U64 → Prop) (ρ μ : U64 → U64) (q : SP),
    CoreView.view K.toKLayout c ρ ≠ ρ →
    VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ →
    StartAt (LP i K (CoreView.view K.toKLayout c ρ) hK hU) c hs (CoreView.view K.toKLayout c ρ) q →
    Safe (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ q

/-- **The family read premise gives the one at every start.** -/
theorem vSafe_of_viewSafe {ι : Type} {LP : PathsP ι} (hF : ViewSafe LP) {s : Cfg U64 U64 U64 U64} {K : KLayoutP}
    (hM : MapsP K s) {c : U64} {k : SP} {hK : RegionOKP K} {hU : UserOKP K} {ρ : U64 → U64} {i : ι}
    (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem) : VSafe LP s K c k hK hU ρ i := by
  intro hv hP
  rw [hM.own, hM.cls, hM.ko] at hV ⊢
  exact hF i K hK hU c _ ρ s.mem k hv hV hP

/-- Where the view is the identity, the read premise holds trivially. -/
theorem vSafe_of_eq {ι : Type} {LP : PathsP ι} {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {c : U64} {k : SP}
    {hK : RegionOKP K} {hU : UserOKP K} {ρ : U64 → U64} {i : ι} (h : CoreView.view K.toKLayout c ρ = ρ) :
    VSafe LP s K c k hK hU ρ i :=
  fun hv => absurd h hv

/-! ## Steps and executions with the start at the core's view -/

/-- **A step of FL4 with rule 8, the start at the core's view of a view-equal memory** (module docstring). -/
structure Fl4StepPV {ι : Type} (LP : PathsP ι) (s : Cfg U64 U64 U64 U64) (K : KLayoutP) (c : U64)
    (s' : Cfg U64 U64 U64 U64) (K' : KLayoutP) : Prop where
  arm : ∀ p, s'.ph c = .arm p → PureGlue p
  start : ∀ p0 k W, s.ph c = .loc p0 (.start k) W → ∀ (hK : RegionOKP K) (hU : UserOKP K),
    ∃ ρ : U64 → U64, VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem ∧
      ∃ i, StartAt (LP i K (CoreView.view K.toKLayout c ρ) hK hU) c (fun l => s.lk l = some c)
        (CoreView.view K.toKLayout c ρ) k ∧ VSafe LP s K c k hK hU ρ i
  ser : SerStep s c → RegionOKP K' ∧ UserOKP K' ∧ MapsP K' s'
  keep : ¬ SerStep s c → K' = K

/-- **An execution of FL4 with rules 7 and 8, starts at the cores' views.** -/
inductive ExecPV {ι : Type} (LP : PathsP ι) (s0 : Cfg U64 U64 U64 U64) (K0 : KLayoutP) :
    Cfg U64 U64 U64 U64 → KLayoutP → Prop
  | refl : ExecPV LP s0 K0 s0 K0
  | step {s s' : Cfg U64 U64 U64 U64} {K K' : KLayoutP} {c : U64} :
      ExecPV LP s0 K0 s K → Step s c s' → Fl4StepPV LP s K c s' K' → ExecPV LP s0 K0 s' K'
  | hw {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {v a x : U64} :
      ExecPV LP s0 K0 s K → HwStepP K s v a x → ExecPV LP s0 K0 (hwCfg s a x) K

section exec

/-- **An `ExecPV` is an `XSafeRunH`** (module docstring). Each started body is `Safe` at the physical memory: by
`LocalPath.safeH` where the view is the identity (as in U5), and by `VSafe` elsewhere. -/
theorem exec_safeRunPV {ι : Type} {LP : PathsP ι} {s0 s : Cfg U64 U64 U64 U64}
    {K0 K : KLayoutP} (h0 : Init s0) (hA0 : ArmInv s0) (hK0 : RegionOKP K0)
    (hU0 : UserOKP K0) (hM0 : MapsP K0 s0) (h : ExecPV LP s0 K0 s K) :
    ∃ H, XSafeRunH s0 s H ∧ RegionOKP K ∧ UserOKP K ∧ MapsP K s := by
  induction h with
  | refl => exact ⟨s0.mem, .refl, hK0, hU0, hM0⟩
  | @step s s' K K' c _ hst hF ih =>
    obtain ⟨H, hr, hK, hU, hM⟩ := ih
    obtain ⟨-, -, -, hS, -⟩ := xsafeRunH_inv h0 hA0 hr
    refine ⟨NextH s c s' H, .step hr hst ⟨hF.arm, fun p0 k W hph _ => ?_, by rw [hM.own]; exact moveHeldP hK⟩, ?_⟩
    · obtain ⟨ρ, hV, i, hP, hX⟩ := hF.start p0 k W hph hK hU
      by_cases hv : CoreView.view K.toKLayout c ρ = ρ
      · rw [hv] at hP
        have hko := ko_viewP hK hM hV
        rw [hM.own, hM.cls, hko] at hV ⊢
        exact (LP i K ρ hK hU).safeH (moveHeldP hK) (ownDepP hK hU) hP hV
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

/-- **End to end with rules 7 and 8, the starts at the cores' views**: the conclusion is about the physical memory. -/
theorem serializable_e2ePV {ι : Type} (LP : PathsP ι) {s0 s : Cfg U64 U64 U64 U64}
    {K0 K : KLayoutP} (h0 : Init s0) (hA0 : ArmInv s0) (hK0 : RegionOKP K0)
    (hU0 : UserOKP K0) (hM0 : MapsP K0 s0) (h : ExecPV LP s0 K0 s K) (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  obtain ⟨H, hr, -⟩ := exec_safeRunPV h0 hA0 hK0 hU0 hM0 h
  exact serializable_safeXH h0 hA0 hr hq

end exec

section exec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {ι : Type}

/-- **A step of FL4 with the glue premises named, one chain per core, the start fact at the core's view** (module
docstring). -/
structure Fl4StepWPRV (LP : PathsP ι)
    (SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop)
    (P : LocPlat st arI AR MR) (s : Cfg U64 U64 U64 U64) (K : KLayoutP) (Ch : U64 → S → Prop) (c : U64)
    (s' : Cfg U64 U64 U64 U64) (K' : KLayoutP) (Ch' : U64 → S → Prop) : Prop where
  /-- [P] an armed program is pure glue. -/
  arm : ∀ p, s'.ph c = .arm p → PureGlue p
  /-- [P] the glue's start fact, **of core `c`'s own chain `Ch c` at `c`'s view of a memory `ρ`** that `c` cannot
  tell from the physical one (`VEq`). It comes with `VPte` [P] (the view keeps the PTE convention witness) and
  `VSafe` [J] (the read premise, used only where the view is not `ρ`) for that `ρ` (module docstring). -/
  start : ∀ p0 k W, s.ph c = .loc p0 (.start k) W → ∀ (hK : RegionOKP K) (hU : UserOKP K),
    ∃ ρ : U64 → U64, VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem ∧
      ∃ i, SF (Ch c) K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k i ∧
        VPte K c ρ ∧ VSafe LP s K c k hK hU ρ i
  /-- [P] the serial exit's ghost choice, **one P3 chain per core** (module docstring). -/
  serX : SerStep s c → ∀ e, SerExitW P K'.toKLayoutV (Ch' e)
  /-- The glue's layout convention at the serial exit: no VCPU, the PTE set `ptesR` of the exit memory. -/
  serC : SerStep s c → K'.vcpus = ∅ ∧ K'.ptes = ptesR K' s'.mem
  /-- [P] the exit ghost with rule 8. -/
  serG : SerStep s c → MapsP K' s'
  /-- Layout and chains change only at serial steps. -/
  keep : ¬ SerStep s c → K' = K ∧ Ch' = Ch

/-- **An execution of FL4 with the glue steps, one chain per core, starts at the cores' views.** -/
inductive ExecWPRV (LP : PathsP ι)
    (SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop)
    (P : LocPlat st arI AR MR) (s0 : Cfg U64 U64 U64 U64) (K0 : KLayoutP) (Ch0 : U64 → S → Prop) :
    Cfg U64 U64 U64 U64 → KLayoutP → (U64 → S → Prop) → Prop
  | refl : ExecWPRV LP SF P s0 K0 Ch0 s0 K0 Ch0
  | step {s s' : Cfg U64 U64 U64 U64} {K K' : KLayoutP} {Ch Ch' : U64 → S → Prop} {c : U64} :
      ExecWPRV LP SF P s0 K0 Ch0 s K Ch → Step s c s' → Fl4StepWPRV LP SF P s K Ch c s' K' Ch' →
      ExecWPRV LP SF P s0 K0 Ch0 s' K' Ch'
  | hw {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {Ch : U64 → S → Prop} {v a x : U64} :
      ExecWPRV LP SF P s0 K0 Ch0 s K Ch → HwStepP K s v a x → ExecWPRV LP SF P s0 K0 Ch0 (hwCfg s a x) K Ch

/-- **An `ExecWPRV` is an `ExecPV`, with the epoch invariant** (`execPR_of_WPRRG` with one chain per core: the
start's `SF` at `c`'s view gives `StartAt` at the view by `hSF`, its PTE witness by `VPte` from the epoch's). -/
theorem execPV_of_WPRVG {LP : PathsP ι}
    {SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop}
    (hSF : ∀ (Ch : S → Prop) (K : KLayoutP) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K) c hs q i,
      (∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) →
      (∃ s1 : Cfg U64 U64 U64 U64, (K.vcpus = ∅ ∧ K.ptes = ptesR K s1.mem) ∧ ∀ x, GateW K x → s.mem x = s1.mem x) →
      SF Ch K s.mem hK hU c hs q i → StartAt (LP i K s.mem hK hU) c hs s.mem q)
    (P : LocPlat st arI AR MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : ∀ e, SerExitW P K0.toKLayoutV (Ch0 e)) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0) (h : ExecWPRV LP SF P s0 K0 Ch0 s K Ch) :
    ExecPV LP s0 K0 s K ∧ (∀ e, SerExitW P K.toKLayoutV (Ch e)) ∧
      ∃ s1 : Cfg U64 U64 U64 U64, (K.vcpus = ∅ ∧ K.ptes = ptesR K s1.mem) ∧ ∀ x, GateW K x → s.mem x = s1.mem x := by
  obtain ⟨hK0, hU0⟩ := okP_R (hB 0#u64) hc0
  induction h with
  | refl => exact ⟨.refl, hB, s0, hc0, fun _ _ => rfl⟩
  | @step s1 s1' K1 K1' Ch1 Ch1' c1 _ hS g ih =>
    obtain ⟨hE, hX, e1, hCe, hk1⟩ := ih
    obtain ⟨H1, hR, -, -, hM⟩ := exec_safeRunPV h0 hA0 hK0 hU0 hM0 hE
    have hst : Fl4StepPV LP s1 K1 c1 s1' K1' := by
      refine ⟨g.arm, fun p0 k W hph hK hU => ?_, fun hs => ?_, fun hn => (g.keep hn).1⟩
      · obtain ⟨ρ, hV, i, hi, hvp, hvs⟩ := g.start p0 k W hph hK hU
        have hρg : ∀ x, GateW K1 x → ρ x = e1.mem x := fun x hx =>
          (hV.2.1 x (by rw [hM.own, hx s1.mem]; exact Or.inr rfl)).trans (hk1 x hx)
        have hEv : EpochPte K1 (CoreView.view K1.toKLayout c1 ρ) := hvp ⟨e1, hCe, hρg⟩
        have hA := hSF (Ch1 c1) _ { s1 with mem := CoreView.view K1.toKLayout c1 ρ } _ _ _ _ _ i
          (hX c1).chainOf hEv hi
        exact ⟨ρ, hV, i, hA, hvs⟩
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
    obtain ⟨H1, -, hK, -, hM⟩ := exec_safeRunPV h0 hA0 hK0 hU0 hM0 hE
    refine ⟨.hw hE hH, hX, e1, hCe, fun x hx => ?_⟩
    rw [← hk1 x hx]
    exact hw_gate_keep hK hM hH hx

/-! ## Coverage: single-core-homed U5 executions are U6 executions -/

/-- **A homed start** (module docstring): U5's start fact with a witness `ρ` homed on the starting core. -/
def HomedStart (SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP →
      ι → Prop)
    (s : Cfg U64 U64 U64 U64) (K : KLayoutP) (Ch : S → Prop) (c : U64) : Prop :=
  ∀ p0 k W, s.ph c = .loc p0 (.start k) W → ∀ (hK : RegionOKP K) (hU : UserOKP K),
    ∃ ρ : U64 → U64, VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem ∧
      CoreView.Homed K.toKLayout c ρ ∧ ∃ i, SF Ch K ρ hK hU c (fun l => s.lk l = some c) k i

/-- **U5 executions whose every start is homed.** -/
inductive ExecWPRRHo (LP : PathsP ι)
    (SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop)
    (P : LocPlat st arI AR MR) (s0 : Cfg U64 U64 U64 U64) (K0 : KLayoutP) (Ch0 : S → Prop) :
    Cfg U64 U64 U64 U64 → KLayoutP → (S → Prop) → Prop
  | refl : ExecWPRRHo LP SF P s0 K0 Ch0 s0 K0 Ch0
  | step {s s' : Cfg U64 U64 U64 U64} {K K' : KLayoutP} {Ch Ch' : S → Prop} {c : U64} :
      ExecWPRRHo LP SF P s0 K0 Ch0 s K Ch → Step s c s' → Fl4StepWPRR LP SF P s K Ch c s' K' Ch' →
      HomedStart SF s K Ch c → ExecWPRRHo LP SF P s0 K0 Ch0 s' K' Ch'
  | hw {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {Ch : S → Prop} {v a x : U64} :
      ExecWPRRHo LP SF P s0 K0 Ch0 s K Ch → HwStepP K s v a x → ExecWPRRHo LP SF P s0 K0 Ch0 (hwCfg s a x) K Ch

/-- A homed U5 execution is a U5 execution. -/
theorem ExecWPRRHo.toWPRR {LP : PathsP ι}
    {SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop}
    {P : LocPlat st arI AR MR} {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop}
    (h : ExecWPRRHo LP SF P s0 K0 Ch0 s K Ch) : ExecWPRR LP SF P s0 K0 Ch0 s K Ch := by
  induction h with
  | refl => exact .refl
  | step _ hS g _ ih => exact .step ih hS g
  | hw _ hH ih => exact .hw ih hH

/-- **Every homed U5 execution is a U6 execution**, with the one chain for every core (module docstring). The view
of a homed witness is the witness (`CoreView.view_eq_self`), so U5's `SF` is U6's, `VPte` is trivial and `VSafe` is
vacuous. -/
theorem execWPRV_of_WPRRHo {LP : PathsP ι}
    {SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop}
    {P : LocPlat st arI AR MR} {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop}
    (h : ExecWPRRHo LP SF P s0 K0 Ch0 s K Ch) :
    ExecWPRV LP SF P s0 K0 (fun _ => Ch0) s K (fun _ => Ch) := by
  induction h with
  | refl => exact .refl
  | @step s1 s1' K1 K1' Ch1 Ch1' c1 _ hS g hH ih =>
    refine .step ih hS ⟨g.arm, fun p0 k W hph hK hU => ?_, fun hs _ => g.serX hs, g.serC, g.serG, fun hn => ?_⟩
    · obtain ⟨ρ, hV, hho, i, hi⟩ := hH p0 k W hph hK hU
      have e := CoreView.view_eq_self hK.base.base hho
      refine ⟨ρ, hV, i, ?_, vPte_of_eq e, vSafe_of_eq e⟩
      rw [e]; exact hi
    · obtain ⟨e1, e2⟩ := g.keep hn
      exact ⟨e1, by rw [e2]⟩
  | hw _ hH ih => exact .hw ih hH

end exec

/-! ## The top -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **FL4 end to end with every slot, one P3 chain per core, each start fact at the starting core's view** (module
docstring). It is `serializable_fl4_localU5` with `start` asked of `Ch c` at `CoreView.view K c ρ` (with `VPte` [P]
and `VSafe` [J]) and one exit chain per core (`serX`, `hB`). The conclusion is about the physical memory. It covers
every homed U5 execution (`execWPRV_of_WPRRHo`), and it admits starts of two cores in one epoch
(`CoreView.u6_two_cores`). -/
theorem serializable_fl4_localU6 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : ∀ e, SerExitW P K0.toKLayoutV (Ch0 e)) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPRV (PathsP.sum (fl4LocW11JA st ar hA (masksWr_plain st) L.total a0)
        (PathsP.sum (PathsP.sum (delPteSlot st ar hA (masksWr_plain st)) (invSlotU st ar hA (masksWr_plain st)))
          (cmSlotU st ar hA (masksWr_plain st))))
      (StartV2 st ar hA a0 arI AR MR) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  obtain ⟨hK0, hU0⟩ := okP_R (hB 0#u64) hc0
  refine serializable_e2ePV _ h0 hA0 hK0 hU0 hM0 (execPV_of_WPRVG ?_ P h0 hA0 hB hc0 hM0 h).1 hq
  intro Ch K s hK hU c hs q i hC hE hsf
  have nv : K.vcpus = ∅ := by
    obtain ⟨_, ⟨nv, _⟩, _⟩ := hE
    exact nv
  rcases i with i | ((j | j) | j)
  · exact startAt_U st ar hA (masksWr_plain st) L.total a0 P hIoa hC hE (startU_of_U2 st ar hA a0 hC nv hsf)
  · exact delPteStart_at st ar hA (masksWr_plain st) hC hE (hsf.2 fun _ s b v _ _ _ => hsf.1.wr s b v)
  · exact invStartU2_at st ar hA (masksWr_plain st) hC hE (hsf.2 fun _ s b v _ _ _ => hsf.1.wr s b v)
  · exact cmStartU2_at st ar hA (masksWr_plain st) hC hE (hsf.2 fun _ s b v _ _ _ => hsf.1.wr s b v)

/-- **U6 is not weaker than U5 on homed executions** (module docstring): U5's conclusion for every homed U5 execution,
derived from `serializable_fl4_localU6` under U5's premises only (no `VSafe`, `ViewSafe` or `VPte` assumed). -/
theorem serializable_fl4_localU5Ho (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPRRHo (PathsP.sum (fl4LocW11JA st ar hA (masksWr_plain st) L.total a0)
        (PathsP.sum (PathsP.sum (delPteSlot st ar hA (masksWr_plain st)) (invSlotU st ar hA (masksWr_plain st)))
          (cmSlotU st ar hA (masksWr_plain st))))
      (StartV2 st ar hA a0 arI AR MR) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_fl4_localU6 st ar hA a0 P hIoa h0 hA0 (fun _ => hB) hc0 hM0 (execWPRV_of_WPRRHo h) hq

end top

end
end Fl4Proofs.P2.E2EP
