/-
P3 (line p3J, gen 13): **D1 discharged: FL4's `TCBSetEPTRoot` decode keeps `MR` where its `JVtxScope` holds**
(the Thread half of `JDecMRLK … VtxK …`, XTopJointKEntry40).

D1 asks, at a dispatch state, for a Thread cap invoked at label 88 (`TCBSetEPTRoot`, `tcb.rs:410-420`):
from its own `JPathM` hypothesis (whose Thread @88 leaf is `JVtxScope` = `XCapP JAt JAtPre`), the same
`XCapP` with `MR` at the outcome (`JAtM`, `JAtPreMV`). This module proves it with no premise beyond
U44's global ones (`P0.ArchTotal`, `MRKeepD`, the store's totality):

* **Spec side** (`specDec_ept_noOk`): the ported spec has no TCB label 88 (`tcbLabelOf 88 =
  invalidInvocation`, `tcbExtOf 88 = none`): `fl4DecodeTcbInvocation` → `decodeTcbInvocation` →
  `illegalOperation` (or `invalidCapability 0` in the first phase). No decode outcome, at any state.
* So `XCapP` at label 88 (`XCapP.mrN`) has only its error branches: FL4 ends with an error `e` with
  `ErrRel e e'` (never `Preempted`: `errRel_ne_preempted`), the store unchanged and `X` at the decode's
  spec state. `MR` there needs only that FL4's error outcomes keep it.
* **FL4 side** (`MKE.decode_thread_ept`): every outcome of FL4's decode at label 88 is `Ok ()`, or
  `Err Preempted`, or keeps `MR`. Before the deletion FL4 only stalls the target (`remote_tcb_stall`, an
  `MRKeepD` field) and errs (truncated / illegal / `derive_cap`'s error); `cdt.delete slot true`
  (`finalise_slot_immediate` + `empty_slot`, whose IRQ-handler cleanup may mask a line, and whose
  `preemption_point`s read the clock) ends only in `Ok ()` or `Err Preempted` (`MKE.cdt_delete_exp`,
  through `MKE.fsi_loop`, `MKE.delete_deferred`, `MKE.fsd_loop`, `MKE.preemption_point`: cdt.rs:244-316,
  the only errors there are the fuel's and `preemption_point`'s `Preempted`), after which FL4 returns
  `Ok ()` or that `Preempted`. Neither is an error branch of `XCapP`, so `MR` is not needed there.
* **`VtxU`** [scope]: `VtxK` without its Thread case (an Untyped cap retyping a VT-x object type 14..18,
  D2, unchanged). `jDecMRLK_ofVtxU`: `JDecMRLK VtxU → JDecMRLK VtxK` (the Thread case by the above, the
  Untyped case passed through); `JDecMRLK.mono`, `vtxU_vtxK` (the converse direction).

Named premises: none new. `MRKeepD` [P] and `P0.ArchTotal` are U44's global premises. D2 (`JDecMRLK VtxU`)
stays a per-entry [J] (the retype of a VT-x object: its reset path reads the clock on both sides, as the
native types' `JUtResetMR` [W]). No sorry.
-/
import Fl4Proofs.P3.XTopJointKEntry40
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

/-! ## FL4: result kinds of the exposed delete -/

set_option hygiene false in
local macro "mke_red" : tactic => `(tactic| (simp only [core.result.Result.Insts.CoreOpsTry.branch,
  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
  bind_tc_ok, bind_ok, Aeneas.Std.uncurry]))


section
variable {S A : Type} {st : machine.Store S} [L : P1.LawfulStore st] {arI : machine.Arch A}
  (hS : P0.StoreTotal st) (hA : P0.ArchTotal arI)
include hS hA
set_option linter.unusedSectionVars false

set_option maxHeartbeats 4000000 in
/-- `preemption_point` ends in `Ok ()` or `Err Preempted`. -/
theorem MKE.preemption_point {s : S} {a : A} :
    sched.preemption_point st arI s a ⦃ r => r.1 = .Err .Preempted ∨ r.1 = .Ok () ⦄ := by
  unfold sched.preemption_point
  p0_split

set_option hygiene false in
/-- A `preemption_point` bind, with its result kind. -/
local macro "mke_pp" : tactic => `(tactic| (
  refine WP.spec_bind (MKE.preemption_point hS hA) ?_
  rintro ⟨_r, _s, _a⟩ _h
  simp only at _h
  rcases _h with rfl | rfl))

set_option hygiene false in
local macro "mke_walk" : tactic => `(tactic|
  ((repeat' (first | mke_pp | mke_red | p0_ite_head | step | split | p0_cases_prod | (dsimp only))) <;> p0_close))

set_option maxHeartbeats 16000000 in
/-- `finalise_slot_deferred`'s loop ends in `Ok _` or `Err Preempted`. -/
theorem MKE.fsd_loop {s : S} {a : A} {slot : obj.Slot} {fuel : Std.U64} :
    cdt.finalise_slot_deferred_loop st arI s a slot fuel ⦃ r => r.1 = .Err .Preempted ∨ ∃ f, r.1 = .Ok f ⦄ := by
  unfold cdt.finalise_slot_deferred_loop
  apply loop.spec_decr_nat (measure := fun x => match x with | (_, _, x2) => x2.val) (inv := fun _ => True)
  · rintro ⟨x0, x1, x2⟩ -
    unfold cdt.finalise_slot_deferred_loop.body
    mke_walk
  · trivial

set_option maxHeartbeats 8000000 in
/-- `delete_deferred` ends in `Ok ()` or `Err Preempted`. -/
theorem MKE.delete_deferred {s : S} {a : A} {slot : obj.Slot} :
    cdt.delete_deferred st arI s a slot ⦃ r => r.1 = .Err .Preempted ∨ r.1 = .Ok () ⦄ := by
  unfold cdt.delete_deferred cdt.finalise_slot_deferred
  refine WP.spec_bind (MKE.fsd_loop hS hA) ?_
  rintro ⟨r, s1, a1⟩ h
  simp only at h
  rcases h with rfl | ⟨f, rfl⟩ <;> mke_walk

set_option hygiene false in
/-- A `delete_deferred` bind, with its result kind. -/
local macro "mke_dd" : tactic => `(tactic| (
  refine WP.spec_bind (MKE.delete_deferred hS hA) ?_
  rintro ⟨_r, _s, _a⟩ _h
  simp only at _h
  rcases _h with rfl | rfl))

set_option hygiene false in
local macro "mke_walk2" : tactic => `(tactic|
  ((repeat' (first | mke_pp | mke_dd | mke_red | p0_ite_head | step | split | p0_cases_prod | (dsimp only))) <;>
    p0_close))

set_option maxHeartbeats 32000000 in
/-- `finalise_slot_immediate`'s loop ends in `Ok _` or `Err Preempted`. -/
theorem MKE.fsi_loop {s : S} {a : A} {slot : obj.Slot} {fuel : Std.U64} :
    cdt.finalise_slot_immediate_loop st arI s a slot fuel ⦃ r => r.1 = .Err .Preempted ∨ ∃ f, r.1 = .Ok f ⦄ := by
  unfold cdt.finalise_slot_immediate_loop
  apply loop.spec_decr_nat (measure := fun x => match x with | (_, _, x2) => x2.val) (inv := fun _ => True)
  · rintro ⟨x0, x1, x2⟩ -
    unfold cdt.finalise_slot_immediate_loop.body
    mke_walk2
  · trivial

set_option maxHeartbeats 8000000 in
/-- **The exposed delete ends in `Ok ()` or `Err Preempted`** (module docstring). -/
theorem MKE.cdt_delete_exp {s : S} {a : A} {slot : obj.Slot} :
    cdt.delete st arI s a slot true ⦃ r => r.1 = .Err .Preempted ∨ r.1 = .Ok () ⦄ := by
  unfold cdt.delete cdt.finalise_slot_immediate
  simp only [↓reduceIte]
  refine WP.spec_bind (MKE.fsi_loop hS hA) ?_
  rintro ⟨r, s1, a1⟩ h
  simp only at h
  rcases h with rfl | ⟨f, rfl⟩ <;> mke_walk

end

/-! ## FL4: the SetEPTRoot decode keeps `AR` on its error outcomes -/

section
variable {S A C : Type} {st : machine.Store S} [L : P1.LawfulStore st] {arI : machine.Arch A} {AR : A → C → Prop}
  (hS : P0.StoreTotal st) (hA : P0.ArchTotal arI) (hK : MRKeepD arI AR) {c₀ : C}
include hS hA hK
set_option linter.unusedSectionVars false

set_option hygiene false in
/-- A `cdt.delete … true` bind, with its result kind. -/
local macro "mke_del" : tactic => `(tactic| (
  refine WP.spec_bind (MKE.cdt_delete_exp hS hA) ?_
  rintro ⟨_r, _s, _a⟩ _h
  simp only at _h
  rcases _h with rfl | rfl))

set_option hygiene false in
local macro "mke_close" : tactic => `(tactic| try (first
  | exact (WP.spec_ok _).2 (Or.inr (Or.inr (by assumption)))
  | exact Or.inr (Or.inr (by assumption))
  | (simp only [WP.spec_ok]; exact Or.inr (Or.inr (by assumption)))
  | exact (WP.spec_ok _).2 (Or.inl rfl)
  | exact (WP.spec_ok _).2 (Or.inr (Or.inl rfl))
  | (simp_all; done)
  | p0_close))

set_option maxHeartbeats 16000000 in
/-- `tcb.decode` at `TCBSetEPTRoot`: `Ok ()`, `Err Preempted`, or `AR` kept. -/
theorem MKE.tcb_decode_ept {s : S} {a : A} {target : obj.Tcb} {c : tcb.Ctx} (h : AR a c₀) :
    tcb.decode st arI s a fl4_abi.label.TCBSetEPTRoot target c ⦃ r =>
      r.1 = .Err .Preempted ∨ r.1 = .Ok () ∨ AR r.2.2 c₀ ⦄ := by
  unfold tcb.decode
  refine WP.spec_bind (MKD.smp_remote_tcb_stall hS hA hK h) ?_
  rintro ⟨s1, a1⟩ h1
  simp only at h1
  simp only [Aeneas.Std.uncurry, eq_self_iff_true, if_true, ↓reduceIte]
  ((repeat' (first | mke_del | mke_red | p0_ite_head | step | split | p0_cases_prod | (dsimp only))) <;>
    mke_close)

set_option maxHeartbeats 4000000 in
/-- **FL4's decode of a Thread cap at `TCBSetEPTRoot`**: `Ok ()`, `Err Preempted`, or `AR` kept (module
docstring). -/
theorem MKE.decode_thread_ept {s : S} {a : A} {length : Std.U64} {slot : obj.Slot} {p : Std.U64}
    {blk call don fp : Bool} {buf : Std.U64} {extra : Array obj.Slot 3#usize} (h : AR a c₀) :
    syscall.decode_invocation st arI s a fl4_abi.label.TCBSetEPTRoot length slot (.Thread p) blk call don fp buf
      extra ⦃ r => r.1 = .Err .Preempted ∨ r.1 = .Ok () ∨ AR r.2.2 c₀ ⦄ := by
  unfold syscall.decode_invocation
  ((repeat' (first | exact MKE.tcb_decode_ept hS hA hK h | p0_ite_head |
      (simp only [bind_tc_ok, bind_ok, Aeneas.Std.uncurry]) | p0_cases_prod | (dsimp only) | step | split)) <;>
    mke_close)

end

/-! ## Spec: no TCB label 88 -/

section
open Fl4Spec

theorem lbl_ept_val : fl4_abi.label.TCBSetEPTRoot.val = 88 := by simp [fl4_abi.label.TCBSetEPTRoot]

/-- **The ported spec has no decode outcome for a Thread cap at label 88** (module docstring). -/
theorem specDec_ept_noOk (fp : Bool) (args : List Data) (ci : CapRef) (sl : CslotPtr)
    (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) (p : U64) :
    NoPre.OkP (fun _ => False)
      (specDec fp fl4_abi.label.TCBSetEPTRoot.bv args ci sl (.Thread p) excaps buffer) := by
  obtain ⟨sl', hg, hx, hd⟩ := tcb_canon fl4_abi.label.TCBSetEPTRoot
  obtain ⟨-, -, hti, hte⟩ := tcb_out fl4_abi.label.TCBSetEPTRoot (by rw [lbl_ept_val]; omega)
  rw [hti] at hg
  have hx' := hx hg
  rw [hte] at hx'
  rw [specDec_thread p hd]
  simp only [specDec, absCap, Fl4Spec.fl4DecodeInvocation]
  split
  · simp only [NonDetE.throwError]; exact NoPre.okP_throw
  · have hne : genInvocationType sl' ≠ .tcbSetFlags := by rw [hg]; intro h; cases h
    rw [Fl4Spec.fl4DecodeTcbInvocation, if_neg hne, hx']
    dsimp only
    refine NoPre.okP_liftME' (Q := fun _ => False) ?_ (fun _ h => h)
    simp only [Fl4Spec.decodeTcbInvocation, hg, NonDetE.throwError]
    exact NoPre.okP_throw

end

/-! ## `XCapP` with `MR` when the spec decode has no outcome -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {MR : A → Fl4Spec.MachineState → Prop}

/-- `ErrRel` never relates `Preempted`. -/
theorem errRel_ne_preempted {e : error.Exc} {e' : Fl4Spec.SyscallError} (h : ErrRel e e') : e ≠ .Preempted := by
  rintro rfl
  rcases h with h | ⟨n, h1, -⟩
  · cases e' <;> simp [SysErrRel] at h
  · cases h1

/-- **`XCapP` gains `MR` when the spec's decode has no outcome** (module docstring): only the error
branches are left, and FL4's error outcomes other than `Preempted` keep `MR`. Any `XP'` after a
preemption (none is possible). -/
theorem XCapP.mrN {X XP XP' : S → A → Fl4Spec.State Unit → Prop} {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} {lbl length slot : U64} {c : capability.Cap} {blk call don fp : Bool} {buf : U64}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {slbl : Fl4Spec.Data} {args : List Fl4Spec.Data}
    {ci : Fl4Spec.CapRef} {sl : Fl4Spec.CslotPtr} {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    {buffer : Option Fl4Spec.ObjRef} {ct : U64}
    (hno : ∀ inv, ¬ DecOut (specDec fp slbl args ci sl c excaps buffer) σ inv)
    (h : XCapP (L := L) arI X XP s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer ct)
    (hW : syscall.decode_invocation st arI s ar lbl length slot c blk call don fp buf extra ⦃ r =>
      r.1 = .Err .Preempted ∨ r.1 = .Ok () ∨ MR r.2.2 σ.machineState ⦄) :
    XCapP (L := L) arI (fun s a σ => X s a σ ∧ MR a σ.machineState) XP' s ar σ lbl length slot c blk call don fp
      buf extra slbl args ci sl excaps buffer ct := by
  rcases h with h | h
  · refine Or.inl (WP.spec_mono (WP.spec_and h hW) ?_)
    rintro r ⟨h1, h2⟩
    unfold TopPostDMXP TopPostDMX at h1 ⊢
    rcases h1 with ⟨e, he, hs, ⟨e', hrun, hrel⟩, hX⟩ | ⟨inv, hd, -⟩
    · have hp : r.1 ≠ .Err .Preempted := by
        rw [he]; intro h; exact errRel_ne_preempted hrel (by cases h; rfl)
      have hMR : MR r.2.2 σ.machineState := by
        rcases h2 with h2 | h2 | h2
        · exact absurd h2 hp
        · rw [he] at h2; cases h2
        · exact h2
      refine Or.inl ⟨e, he, hs, ⟨e', hrun, hrel⟩, ?_⟩
      simp only [if_neg hp] at hX ⊢
      exact ⟨hX, hMR⟩
    · exact absurd hd (hno inv)
  · refine Or.inr (WP.spec_mono (WP.spec_and h hW) ?_)
    rintro r ⟨h1, h2⟩
    unfold TopPostRMX at h1 ⊢
    rcases h1 with ⟨e, he, hs, ⟨e', hrun, hrel⟩, hX⟩ | ⟨-, -, inv, hd, -⟩
    · have hp : r.1 ≠ .Err .Preempted := by
        rw [he]; intro h; exact errRel_ne_preempted hrel (by cases h; rfl)
      have hMR : MR r.2.2 σ.machineState := by
        rcases h2 with h2 | h2 | h2
        · exact absurd h2 hp
        · rw [he] at h2; cases h2
        · exact h2
      exact Or.inl ⟨e, he, hs, ⟨e', hrun, hrel⟩, hX, hMR⟩
    · exact absurd hd (hno inv)

end

/-! ## `JDecMRLK VtxK` from `JDecMRLK VtxU` -/

/-- **The VT-x decodes left after D1** [scope] (module docstring): an Untyped cap retyping a VT-x object
type (14..18), `VtxK` without its Thread case. -/
def VtxU : capability.Cap → U64 → List U64 → Prop
  | .Untyped .., _, argsU => ∃ x, argsU.head? = some x ∧ 14 ≤ x.val ∧ x.val < 19
  | _, _, _ => False

theorem vtxU_vtxK : ∀ c lbl argsU, VtxU c lbl argsU → VtxK c lbl argsU := by
  intro c lbl argsU h
  cases c <;> first | exact h | exact (show False from h).elim

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets} {H : P1.Heap}
  {Cs D : Set U64}

/-- `JDecMRLK` is antitone in the cap family. -/
theorem JDecMRLK.mono {K K' : capability.Cap → U64 → List U64 → Prop} (hKK : ∀ c l a, K' c l a → K c l a)
    {s : S} {ar : A} {σ : Fl4Spec.State Unit} {ct : U64}
    (h : JDecMRLK (L := L) arI K AR MR Z H Cs D s ar σ ct) : JDecMRLK (L := L) arI K' AR MR Z H Cs D s ar σ ct := by
  intro hR hVT hVI lbl length blk call don fp buf extra slbl argsU hlen hargs hbuf hl ci sl hsl c hc hk
  exact h hR hVT hVI lbl length blk call don fp buf extra slbl argsU hlen hargs hbuf hl ci sl hsl c hc
    (hKK c lbl argsU hk)

set_option maxHeartbeats 4000000 in
/-- **D1 discharged** (module docstring): `JDecMRLK VtxU → JDecMRLK VtxK`, from `MRKeepD` and
`ArchTotal`. -/
theorem jDecMRLK_ofVtxU (hA : P0.ArchTotal arI) (hKD : MRKeepD arI MR) {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} {ct : U64} (h : JDecMRLK (L := L) arI VtxU AR MR Z H Cs D s ar σ ct) :
    JDecMRLK (L := L) arI VtxK AR MR Z H Cs D s ar σ ct := by
  intro hR hVT hVI lbl length blk call don fp buf extra slbl argsU hlen hargs hbuf hl ci sl hsl c hc hk excaps
    buffer hXO hXN hLb hA5 hN
  cases c
  case Thread p =>
    have hl88 : lbl = fl4_abi.label.TCBSetEPTRoot := hk
    subst hl88
    subst hLb
    obtain ⟨hEpt, -⟩ := hN
    have hX := hEpt rfl
    exact XCapP.mrN arI
      (fun inv hd => specDec_ept_noOk fp _ ci sl excaps buffer p σ _ hd.1 inv rfl) hX
      (MKE.decode_thread_ept L.total hA hKD hR)
  case Untyped p sb fi dev =>
    exact h hR hVT hVI lbl length blk call don fp buf extra slbl argsU hlen hargs hbuf hl ci sl hsl _ hc hk
      excaps buffer hXO hXN hLb hA5 hN
  all_goals exact (show False from hk).elim

end

end Fl4Proofs.P3
