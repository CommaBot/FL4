/-
P3 (line p3J, gen 14): **D2 narrowed, and gone without virtualization**: FL4's decode of an Untyped cap whose
first message word is a VT-x object type (14..18) errs without touching the arch state, except for an
`UntypedRetype` on a platform reporting virtualization.

D2 (`JDecMRLK … VtxU …`, P3JVtxMR) asks, at a dispatch state, for an Untyped cap whose first argument `x`
lies in 14..18 at **any** label: from `JPathM`'s untyped leaf (`vtx` = `JVtxScope` = `XCapP JAt JAtPre`), the
same `XCapP` with `MR` (`JAtM`, `JAtPreMV`). FL4 (`untyped.rs:25-44`, `untyped::decode`):
* `lbl ≠ UntypedRetype`, `lbl ≠ UntypedRetypeShared`: `illegal()`.
* `lbl = UntypedRetypeShared`: sharing off: `illegal()`; sharing on: `retype_shared` (`untyped.rs:99-108`),
  whose first argument is the frame size `bits` and `shared_frame_spec bits` accepts only 12 and 21: with
  `bits = x ∈ 14..18` it errs `InvalidArgument 0` after only the truncation / cap checks (reads).
* `lbl = UntypedRetype`, `virtualization() = 0`: truncation checks, then `InvalidArgument 0`
  (`untyped.rs:43`; `X86Vcpu = 14`, `Count = 19`).
Every such outcome is `Err e` with `e ≠ Preempted`, the store and arch state unchanged
(**`MKE.untyped_vtx_err`**, `MKE.decode_untyped_vtx_err`). So `XCapP`'s decode-outcome branches (FL4 `Ok ()` /
`Err Preempted`) are impossible, and its error branches gain `MR` (the arch state is the dispatch one):
**`XCapP.mrE`**. This is the D1 method with the roles swapped: there the spec had no outcome, here FL4 has
only (non-preempted) errors; no spec look at `UntypedRetypeShared` is needed.

* **`VtxR`** [scope]: what is left of D2: an Untyped cap invoked at `UntypedRetype` with first argument in
  14..18 (the VT-x retype proper), on a platform where `virtualization()` answered non-zero.
  `VtxUE arI ar`: `VtxU` with `lbl ≠ UntypedRetype` or `virtualization ar = ok 0`; **`jDecMRLK_vtxUE`**:
  `JDecMRLK (VtxUE arI ar)` holds outright. **`jDecMRLK_ofVtxR : JDecMRLK VtxR → JDecMRLK VtxU`** (no premise
  beyond `ArchTotal` / the store's).
* **`NoVirt arI`** [P] (platform): `∀ a, arI.virtualization a = ok 0#u64`, a fact about the existing `Arch`
  field `virtualization` (FL4 `Arch::virtualization`, x86_64 backend: 0 when VMX is absent or disabled).
  Not implied by U45's premises (`P0.ArchTotal` gives `virtualization a = ok _` only; no other premise
  mentions the field). **`jDecMRLK_vtxU_nv : NoVirt arI → JDecMRLK VtxU`**: D2 is a theorem there.
  **`noVirt_warI1`**: the jboot witness arch (`warI1`, from `modelArch`) satisfies it.

Named premises: none new in the narrowing; `NoVirt` [P] only for the no-VT-x corollary. No sorry.
-/
import Fl4Proofs.P3.P3JVtxMR
import Fl4Proofs.P3.JBootIoa
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

/-- **[P] The platform reports no virtualization** (module docstring): the existing `Arch` field
`virtualization` answers 0 at every arch state. -/
def NoVirt {A : Type} (arI : machine.Arch A) : Prop := ∀ a, arI.virtualization a = ok 0#u64

/-- The jboot witness arch reports no virtualization (`modelArch`'s `virtualization _ := ok 0`). -/
theorem noVirt_warI1 : NoVirt Fl4Proofs.P3.JBoot.warI1 := fun _ => rfl

/-- The outcome kind of FL4's VT-x-type untyped decodes off the VT-x retype: a non-preempted error with the
arch state unchanged. -/
def ErrKeepA {S A : Type} (a : A) (r : core.result.Result Unit error.Exc × S × A) : Prop :=
  r.1 ≠ .Ok () ∧ r.1 ≠ .Err .Preempted ∧ r.2.2 = a

theorem errKeepA_err {S A : Type} {a : A} {s : S} (e : error.SysError) :
    ErrKeepA a ((core.result.Result.Err (error.Exc.Sys e) : core.result.Result Unit error.Exc), s, a) :=
  ⟨by simp, by simp, rfl⟩

/-! ## FL4 -/

theorem shared_frame_spec_vtx {x : Std.U64} (h14 : 14 ≤ x.val) (h19 : x.val < 19) :
    untyped.shared_frame_spec x = ok (.Err (error.Exc.Sys (error.SysError.InvalidArgument 0#u64))) := by
  unfold untyped.shared_frame_spec
  have h12 : x.val ≠ 12 := by omega
  have h21 : x.val ≠ 21 := by omega
  split
  · exact absurd rfl h12
  · exact absurd rfl h21
  · rfl

section
variable {S A : Type} {st : machine.Store S} [L : P1.LawfulStore st] {arI : machine.Arch A}
  (hS : P0.StoreTotal st) (hA : P0.ArchTotal arI)
include hS hA
set_option linter.unusedSectionVars false

set_option hygiene false in
local macro "vr_close" : tactic => `(tactic| first
  | exact (WP.spec_ok _).2 (errKeepA_err _)
  | (simp only [error.illegal, error.truncated, error.invalid_cap, error.invalid_arg, error.range, bind_tc_ok,
      bind_ok]; exact (WP.spec_ok _).2 (errKeepA_err _)))

set_option maxHeartbeats 4000000 in
/-- `retype_shared` with a first argument in 14..18: a non-preempted error, arch state unchanged. -/
theorem MKE.retype_shared_vtx {s : S} {a : A} {length : Std.U64} {slot : obj.Slot} {cap : capability.Cap}
    {buf : Std.U64} {extra : Array obj.Slot 3#usize} {ct x : Std.U64}
    (hct : sched.cur_thread st s = ok ct) (hx : msg.syscall_arg st s ct buf 0#u64 = ok x)
    (h14 : 14 ≤ x.val) (h19 : x.val < 19) :
    untyped.retype_shared st arI s a length slot cap buf extra ⦃ r => ErrKeepA a r ⦄ := by
  unfold untyped.retype_shared
  p0_ite_head
  · vr_close
  · step
    step
    p0_ite_head
    · vr_close
    · step
      split
      · vr_close
      · p0_ite_head
        · vr_close
        · simp only [hct, hx, shared_frame_spec_vtx h14 h19, bind_tc_ok, bind_ok,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          exact (WP.spec_ok _).2 (errKeepA_err _)

set_option maxHeartbeats 4000000 in
/-- **`untyped::decode` with a first argument in 14..18**, off an `UntypedRetype` on a platform with
virtualization: a non-preempted error, arch state unchanged (module docstring). -/
theorem MKE.untyped_vtx_err {s : S} {a : A} {lbl length : Std.U64} {slot : obj.Slot} {cap : capability.Cap}
    {buf : Std.U64} {extra : Array obj.Slot 3#usize} {ct x : Std.U64}
    (hct : sched.cur_thread st s = ok ct) (hx : msg.syscall_arg st s ct buf 0#u64 = ok x)
    (h14 : 14 ≤ x.val) (h19 : x.val < 19)
    (hv : lbl ≠ fl4_abi.label.UntypedRetype ∨ arI.virtualization a = ok 0#u64) :
    untyped.decode st arI s a lbl length slot cap buf extra ⦃ r => ErrKeepA a r ⦄ := by
  unfold untyped.decode
  apply p0_if <;> intro hne
  · have hl : lbl ≠ fl4_abi.label.UntypedRetype := bne_iff_ne.mp hne
    apply p0_if <;> intro
    · step
      p0_ite_head
      · exact MKE.retype_shared_vtx hS hA hct hx h14 h19
      · vr_close
    · vr_close
  · have hl : lbl = fl4_abi.label.UntypedRetype := by
      by_contra h; exact hne (bne_iff_ne.mpr h)
    have hv0 : arI.virtualization a = ok 0#u64 := hv.resolve_left (fun h => h hl)
    have hge : x ≥ fl4_abi.consts.object.X86Vcpu := by
      simp only [fl4_abi.consts.object.X86Vcpu, ge_iff_le, UScalar.le_equiv]; scalar_tac
    have hlt : x < fl4_abi.consts.object.Count := by
      simp only [fl4_abi.consts.object.Count, UScalar.lt_equiv]; scalar_tac
    apply p0_if <;> intro
    · vr_close
    · step
      step
      p0_ite_head
      · vr_close
      · rw [hct, bind_ok, hx, bind_ok]
        step
        step
        step
        step
        step
        p0_ite_head
        · p0_ite_head
          · rw [hv0, bind_ok]
            p0_ite_head
            · vr_close
            · rename_i h0; exact absurd rfl h0
          · rename_i h1; exact absurd hlt h1
        · rename_i h2; exact absurd hge h2

set_option maxHeartbeats 4000000 in
/-- **FL4's decode of an Untyped cap with a first argument in 14..18** (module docstring), off a VT-x
retype: a non-preempted error, arch state unchanged. -/
theorem MKE.decode_untyped_vtx_err {s : S} {a : A} {lbl length : Std.U64} {slot : obj.Slot}
    {p sb fi : Std.U64} {dev : Bool} {blk call don fp : Bool} {buf : Std.U64} {extra : Array obj.Slot 3#usize}
    {ct x : Std.U64}
    (hct : sched.cur_thread st s = ok ct) (hx : msg.syscall_arg st s ct buf 0#u64 = ok x)
    (h14 : 14 ≤ x.val) (h19 : x.val < 19)
    (hv : lbl ≠ fl4_abi.label.UntypedRetype ∨ arI.virtualization a = ok 0#u64) :
    syscall.decode_invocation st arI s a lbl length slot (.Untyped p sb fi dev) blk call don fp buf extra
      ⦃ r => ErrKeepA a r ⦄ := by
  unfold syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  exact MKE.untyped_vtx_err hS hA hct hx h14 h19 hv

end

/-! ## `XCapP` with `MR` when FL4 only errs -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {MR : A → Fl4Spec.MachineState → Prop}

/-- **`XCapP` gains `MR` when FL4's decode only errs (not `Preempted`) and keeps `MR`** (module docstring):
the decode-outcome branches need FL4 `Ok ()` / `Err Preempted`. Any `XP'`. -/
theorem XCapP.mrE {X XP XP' : S → A → Fl4Spec.State Unit → Prop} {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} {lbl length slot : U64} {c : capability.Cap} {blk call don fp : Bool} {buf : U64}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {slbl : Fl4Spec.Data} {args : List Fl4Spec.Data}
    {ci : Fl4Spec.CapRef} {sl : Fl4Spec.CslotPtr} {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    {buffer : Option Fl4Spec.ObjRef} {ct : U64}
    (h : XCapP (L := L) arI X XP s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer ct)
    (hW : syscall.decode_invocation st arI s ar lbl length slot c blk call don fp buf extra ⦃ r =>
      r.1 ≠ .Ok () ∧ r.1 ≠ .Err .Preempted ∧ MR r.2.2 σ.machineState ⦄) :
    XCapP (L := L) arI (fun s a σ => X s a σ ∧ MR a σ.machineState) XP' s ar σ lbl length slot c blk call don fp
      buf extra slbl args ci sl excaps buffer ct := by
  rcases h with h | h
  · refine Or.inl (WP.spec_mono (WP.spec_and h hW) ?_)
    rintro r ⟨h1, hok, hp, hMR⟩
    unfold TopPostDMXP TopPostDMX at h1 ⊢
    rcases h1 with ⟨e, he, hs, hrun, hX⟩ | ⟨inv, hd, σ1, h2, y, hy, ⟨th', G', h3, -⟩, -⟩
    · refine Or.inl ⟨e, he, hs, hrun, ?_⟩
      simp only [if_neg hp] at hX ⊢
      exact ⟨hX, hMR⟩
    · rcases h3 with ⟨h3, -⟩ | ⟨h3, -⟩
      · exact absurd h3 hok
      · exact absurd h3 hp
  · refine Or.inr (WP.spec_mono (WP.spec_and h hW) ?_)
    rintro r ⟨h1, hok, hp, hMR⟩
    unfold TopPostRMX at h1 ⊢
    rcases h1 with ⟨e, he, hs, hrun, hX⟩ | ⟨h3, -⟩
    · exact Or.inl ⟨e, he, hs, hrun, hX, hMR⟩
    · exact absurd h3 hok

end

/-! ## `JDecMRLK VtxU` from `JDecMRLK VtxR`, and without virtualization -/

/-- **What is left of D2** [scope] (module docstring): an Untyped cap invoked at `UntypedRetype` with a VT-x
object type (14..18) as its first argument. -/
def VtxR : capability.Cap → U64 → List U64 → Prop
  | .Untyped .., lbl, argsU => lbl = fl4_abi.label.UntypedRetype ∧
      ∃ x, argsU.head? = some x ∧ 14 ≤ x.val ∧ x.val < 19
  | _, _, _ => False

theorem vtxR_vtxU : ∀ c lbl argsU, VtxR c lbl argsU → VtxU c lbl argsU := by
  intro c lbl argsU h
  cases c <;> first | exact h.2 | exact (show False from h).elim

/-- `VtxU` off the VT-x retype at arch state `ar` (module docstring): a label other than `UntypedRetype`, or
no virtualization reported at `ar`. -/
def VtxUE {A : Type} (arI : machine.Arch A) (ar : A) (c : capability.Cap) (lbl : U64) (argsU : List U64) : Prop :=
  VtxU c lbl argsU ∧ (lbl ≠ fl4_abi.label.UntypedRetype ∨ arI.virtualization ar = ok 0#u64)

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets} {H : P1.Heap}
  {Cs D : Set U64}

set_option maxHeartbeats 4000000 in
/-- **`JDecMRLK` for the `VtxU` entries off the VT-x retype** (`VtxUE`): `XCapP` with `MR`, from `JPathM`'s
`vtx` leaf (module docstring). No premise beyond `ArchTotal`. -/
theorem jDecMRLK_vtxUE (hA : P0.ArchTotal arI) {s : S} {ar : A} {σ : Fl4Spec.State Unit} {ct : U64}
    (hct : sched.cur_thread st s = ok ct) :
    JDecMRLK (L := L) arI (VtxUE arI ar) AR MR Z H Cs D s ar σ ct := by
  intro hR _ _ lbl length blk call don fp buf extra slbl argsU _ hargs _ _ ci sl _ c hc hk excaps buffer _ _ _ _ hN
  clear hc
  obtain ⟨hk, hv⟩ := hk
  cases c
  case Untyped p sb fi dev =>
    obtain ⟨x, hx, h14, h19⟩ := hk
    have hx0 : msg.syscall_arg st s ct buf 0#u64 = ok x := hargs 0#u64 x (by
      cases argsU with
      | nil => cases hx
      | cons y ys => simp only [List.head?_cons, Option.some.injEq] at hx; subst hx; rfl)
    have hX : JVtxScope (L := L) arI AR s ar σ lbl length (.Untyped p sb fi dev) blk call don fp buf extra slbl
        argsU ci sl excaps buffer ct := by
      cases dev
      · exact (hN.2 rfl).vtx x hx h14 h19
      · exact (hN.1 rfl).vtx x hx h14 h19
    refine XCapP.mrE arI hX (WP.spec_mono (MKE.decode_untyped_vtx_err L.total hA hct hx0 h14 h19 hv) ?_)
    rintro r ⟨h1, h2, h3⟩
    exact ⟨h1, h2, h3 ▸ hR⟩
  all_goals exact (show False from hk).elim

set_option maxHeartbeats 4000000 in
/-- **D2 narrowed** (module docstring): `JDecMRLK VtxR → JDecMRLK VtxU`, from `ArchTotal`. -/
theorem jDecMRLK_ofVtxR (hA : P0.ArchTotal arI) {s : S} {ar : A} {σ : Fl4Spec.State Unit} {ct : U64}
    (hct : sched.cur_thread st s = ok ct) (h : JDecMRLK (L := L) arI VtxR AR MR Z H Cs D s ar σ ct) :
    JDecMRLK (L := L) arI VtxU AR MR Z H Cs D s ar σ ct := by
  have hE := jDecMRLK_vtxUE (L := L) arI (AR := AR) (MR := MR) (Z := Z) (H := H) (Cs := Cs) (D := D) hA (ar := ar) (σ := σ) hct
  intro hR hVT hVI lbl length blk call don fp buf extra slbl argsU hlen hargs hbuf hl ci sl hsl c hc hk
  by_cases hlr : lbl = fl4_abi.label.UntypedRetype
  · have hk' : VtxR c lbl argsU := by
      cases c <;> first | exact ⟨hlr, hk⟩ | exact (show False from hk).elim
    exact h hR hVT hVI lbl length blk call don fp buf extra slbl argsU hlen hargs hbuf hl ci sl hsl c hc hk'
  · exact hE hR hVT hVI lbl length blk call don fp buf extra slbl argsU hlen hargs hbuf hl ci sl hsl c hc
      ⟨hk, Or.inl hlr⟩

/-- **D2 without virtualization** (module docstring): `NoVirt arI` [P] gives `JDecMRLK VtxU` outright. -/
theorem jDecMRLK_vtxU_nv (hA : P0.ArchTotal arI) (hNV : NoVirt arI) {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    {ct : U64} (hct : sched.cur_thread st s = ok ct) :
    JDecMRLK (L := L) arI VtxU AR MR Z H Cs D s ar σ ct :=
  JDecMRLK.mono arI (fun _ _ _ h => ⟨h, Or.inr (hNV ar)⟩) (jDecMRLK_vtxUE arI hA hct)

end

end Fl4Proofs.P3
