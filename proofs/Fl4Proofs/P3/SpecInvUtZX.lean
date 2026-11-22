/-
P3 (DESIGN.md §9), invariant line G1 (g5g): **the deletion path of the cap
half `HU U`, and `zr_auto`** (spec side only; outside the `JAtZ` cone).

* `rv_finaliseCap_ut`: `finalise_cap`'s remainder is never a non-device
  untyped cap (an untyped cap finalises to `NullCap`), so `rec_del`'s
  `set_cap remainder` keeps `HU U`; the cleanup cap goes only to
  `post_cap_deletion` (no cap write).
* `hu_recDel` (`ik_lfp`), `hu_capDelete`, `hu_capRevoke`.
* `zr_auto`: `ZR` of a function with an `HU U` lemma (every `U`) and a `YK`
  lemma (every `D`, `F`), via `ik_zr`.
-/
import Fl4Proofs.P3.SpecInvUtZG
open Classical

namespace Fl4Proofs.P3.SInvUZ
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvV

noncomputable section

set_option maxHeartbeats 1000000

variable {U : UtSet}

/-! ## `finalise_cap`'s remainder -/

theorem rv_fc_pure_ut {a : Cap × Cap} (h1 : ∀ b n f, a.1 ≠ .untypedCap false b n f) :
    RV (fun r : Cap × Cap => ∀ b n f, r.1 ≠ .untypedCap false b n f) (pure a : NonDet (State Unit) (Cap × Cap)) :=
  rv_pure h1

macro "rv_auto_ut" : tactic => `(tactic| repeat' (first
  | (with_reducible refine rv_fc_pure_ut (fun _ _ _ h => ?_) <;> (try split at h) <;> simp_all; done)
  | (with_reducible refine rv_liftM (fun _ _ _ _ h => ?_) <;> simp_all; done)
  | (with_reducible exact rv_fail)
  | (with_reducible refine rv_bind fun _ => ?_)
  | split))

theorem rv_finaliseCap_ut (c : Cap) (fin : Bool) :
    RV (fun r : Cap × Cap => ∀ b n f, r.1 ≠ .untypedCap false b n f) (finaliseCap (Z := Unit) c fin) := by
  cases c with
  | archObjectCap a =>
    simp only [finaliseCap]; unfold archFinaliseCap
    rv_auto_ut
  | _ => simp only [finaliseCap]; rv_auto_ut

theorem zrun_liftE_bind_mem {ε α β : Type} {m : NonDet (State Unit) α} {k : α → NonDetE (State Unit) ε β}
    {σ : State Unit} {y : Except ε β × State Unit} (hy : y ∈ (ExceptT.run (NonDetE.liftE m >>= k) σ).1) :
    ∃ x ∈ (m σ).1, y ∈ (ExceptT.run (k x.1) x.2).1 := by
  unfold NonDetE.liftE at hy
  rw [ExceptT.run_bind, ExceptT.run_lift] at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨x, hx, hz⟩ := hz
  obtain rfl := Set.mem_singleton_iff.1 hz
  exact ⟨x, hx, hy⟩

theorem ike_liftE_bind_rv {P : State Unit → Prop} {ε α β : Type} {Pr : α → Prop} {m : NonDet (State Unit) α}
    {k : α → NonDetE (State Unit) ε β} (hm : IKH P m) (hr : RV Pr m) (hk : ∀ a, Pr a → IKHE P (k a)) :
    IKHE P (NonDetE.liftE m >>= k) := by
  intro σ hσ y hy
  obtain ⟨x, hx, hy⟩ := zrun_liftE_bind_mem hy
  exact hk x.1 (hr σ x hx) x.2 (hm σ hσ x hx) y hy

/-! ## `rec_del` -/

set_option maxHeartbeats 4000000 in
theorem hu_recDelF {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k, IKH (HU U) (f k)) (k : RecDelCall) : IKHE (ε := Unit) (HU U) (recDelF (Z := Unit) f k) := by
  have hrec' : ∀ k, IKHE (ε := Unit) (HU U) (f k : NonDetE (State Unit) Unit (Bool × Cap)) := hrec
  cases k with
  | cTEDeleteCall sl e => unfold recDelF withoutPreemption; hv_auto; all_goals exact hrec' _
  | finaliseSlotCall sl e =>
    unfold recDelF withoutPreemption
    refine ike_bind (ike_liftE (hv_getCap _)) fun cap => ?_
    split
    · exact ike_returnOk _
    refine ike_bind (ike_liftE (by hv_auto)) fun fin => ?_
    refine ike_liftE_bind_rv (hu_finaliseCap cap fin) (rv_finaliseCap_ut cap fin) fun rc hrc => ?_
    obtain ⟨rem, cl⟩ := rc
    have hrem : UtIn U rem := utIn_noUt hrc U
    dsimp only
    hv_auto
    all_goals exact hrec' _
  | reduceZombieCall c sl e =>
    unfold recDelF withoutPreemption
    split <;> hv_auto
    all_goals exact hrec' _

theorem hu_recDel (c : RecDelCall) : IKHE (ε := Unit) (HU U) (recDel (Z := Unit) c) := by
  unfold recDel
  exact ik_lfp (fun f hf k => hu_recDelF hf k) c

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hu_recDel _)

theorem hu_capDelete (sl : CslotPtr) : IKHE (ε := Unit) (HU U) (capDelete (Z := Unit) sl) := by
  unfold capDelete; hv_auto

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hu_capDelete _)

theorem hu_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, IKH (HU U) (f k)) (sl : CslotPtr) : IKHE (ε := Unit) (HU U) (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, IKHE (ε := Unit) (HU U) (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeF withoutPreemption selectExt
  hv_auto
  all_goals exact hrec' _

theorem hu_capRevoke (sl : CslotPtr) : IKHE (ε := Unit) (HU U) (capRevoke (Z := Unit) sl) := by
  unfold capRevoke
  exact ik_lfp (fun f hf k => hu_capRevokeF hf k) sl

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hu_capRevoke _)

/-! ## `zr_auto` -/

syntax "zr_leaf" : tactic
macro_rules | `(tactic| zr_leaf) => `(tactic| fail "no zr_leaf")

macro "zr_auto" : tactic => `(tactic| repeat' (first | zr_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

/-- A function with an `HU U` lemma (every `U`) and a `YK` lemma keeps `ZR`. -/
macro_rules | `(tactic| zr_leaf) => `(tactic| ((with_reducible refine ik_zr (fun _ => ?_) (fun _ _ => ?_)) <;> first | hv_leaf | yk_leaf))
macro_rules | `(tactic| zr_leaf) => `(tactic| ((with_reducible refine ike_zr (fun _ => ?_) (fun _ _ => ?_)) <;> first | hv_leaf | yk_leaf))
macro_rules | `(tactic| zr_leaf) => `(tactic| ((with_reducible apply ik_modify); intro _ h; exact h))
macro_rules | `(tactic| zr_leaf) => `(tactic| ((with_reducible refine ik_doExtendedOp ?_ _); intro _ _ h; exact h))
macro_rules | `(tactic| zr_leaf) => `(tactic| with_reducible exact ik_getObject _)

end

end Fl4Proofs.P3.SInvUZ
