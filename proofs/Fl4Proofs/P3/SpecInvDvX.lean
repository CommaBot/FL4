/-
P3 (issue #16, s26; SpecInvUtZX with the device flag, `HUD U`, `ZD`; was: invariant line G1, g5g): **the deletion path of the cap
half `HUD U`, and `zd_auto`** (spec side only; outside the `JAtZ` cone).

* `rv_finaliseCap_utD`: `finalise_cap`'s remainder is never a device
  untyped cap (an untyped cap finalises to `NullCap`), so `rec_del`'s
  `set_cap remainder` keeps `HUD U`; the cleanup cap goes only to
  `post_cap_deletion` (no cap write).
* `hd_recDel` (`ik_lfp`), `hd_capDelete`, `hd_capRevoke`.
* `zd_auto`: `ZD` of a function with an `HUD U` lemma (every `U`) and an `OBK`
  lemma (every `O`), via `ik_zd`.
-/
import Fl4Proofs.P3.SpecInvDvG
open Classical

namespace Fl4Proofs.P3.SInvDV
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvV

noncomputable section

set_option maxHeartbeats 1000000

variable {U : UtSetD}

/-! ## `finalise_cap`'s remainder -/

theorem rv_fc_pure_utD {a : Cap × Cap} (h1 : ∀ b n f, a.1 ≠ .untypedCap true b n f) :
    RV (fun r : Cap × Cap => ∀ b n f, r.1 ≠ .untypedCap true b n f) (pure a : NonDet (State Unit) (Cap × Cap)) :=
  rv_pure h1

macro "rv_auto_utD" : tactic => `(tactic| repeat' (first
  | (with_reducible refine rv_fc_pure_utD (fun _ _ _ h => ?_) <;> (try split at h) <;> simp_all; done)
  | (with_reducible refine rv_liftM (fun _ _ _ _ h => ?_) <;> simp_all; done)
  | (with_reducible exact rv_fail)
  | (with_reducible refine rv_bind fun _ => ?_)
  | split))

theorem rv_finaliseCap_utD (c : Cap) (fin : Bool) :
    RV (fun r : Cap × Cap => ∀ b n f, r.1 ≠ .untypedCap true b n f) (finaliseCap (Z := Unit) c fin) := by
  cases c with
  | archObjectCap a =>
    simp only [finaliseCap]; unfold archFinaliseCap
    rv_auto_utD
  | _ => simp only [finaliseCap]; rv_auto_utD

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
theorem hd_recDelF {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k, IKH (HUD U) (f k)) (k : RecDelCall) : IKHE (ε := Unit) (HUD U) (recDelF (Z := Unit) f k) := by
  have hrec' : ∀ k, IKHE (ε := Unit) (HUD U) (f k : NonDetE (State Unit) Unit (Bool × Cap)) := hrec
  cases k with
  | cTEDeleteCall sl e => unfold recDelF withoutPreemption; hv_auto; all_goals exact hrec' _
  | finaliseSlotCall sl e =>
    unfold recDelF withoutPreemption
    refine ike_bind (ike_liftE (hv_getCap _)) fun cap => ?_
    split
    · exact ike_returnOk _
    refine ike_bind (ike_liftE (by hv_auto)) fun fin => ?_
    refine ike_liftE_bind_rv (hd_finaliseCap cap fin) (rv_finaliseCap_utD cap fin) fun rc hrc => ?_
    obtain ⟨rem, cl⟩ := rc
    have hrem : UtInD U rem := utInD_noUt hrc U
    dsimp only
    hv_auto
    all_goals exact hrec' _
  | reduceZombieCall c sl e =>
    unfold recDelF withoutPreemption
    split <;> hv_auto
    all_goals exact hrec' _

theorem hd_recDel (c : RecDelCall) : IKHE (ε := Unit) (HUD U) (recDel (Z := Unit) c) := by
  unfold recDel
  exact ik_lfp (fun f hf k => hd_recDelF hf k) c

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hd_recDel _)

theorem hd_capDelete (sl : CslotPtr) : IKHE (ε := Unit) (HUD U) (capDelete (Z := Unit) sl) := by
  unfold capDelete; hv_auto

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hd_capDelete _)

theorem hd_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, IKH (HUD U) (f k)) (sl : CslotPtr) : IKHE (ε := Unit) (HUD U) (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, IKHE (ε := Unit) (HUD U) (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeF withoutPreemption selectExt
  hv_auto
  all_goals exact hrec' _

theorem hd_capRevoke (sl : CslotPtr) : IKHE (ε := Unit) (HUD U) (capRevoke (Z := Unit) sl) := by
  unfold capRevoke
  exact ik_lfp (fun f hf k => hd_capRevokeF hf k) sl

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hd_capRevoke _)

/-! ## `zd_auto` -/

syntax "zd_leaf" : tactic
macro_rules | `(tactic| zd_leaf) => `(tactic| fail "no zd_leaf")

macro "zd_auto" : tactic => `(tactic| repeat' (first | zd_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

/-- A function with an `HUD U` lemma (every `U`) and an `OBK` lemma keeps `ZD`. -/
macro_rules | `(tactic| zd_leaf) => `(tactic| ((with_reducible refine ik_zd (fun _ => ?_) (fun _ => ?_)) <;> first | hv_leaf | ob_leaf))
macro_rules | `(tactic| zd_leaf) => `(tactic| ((with_reducible refine ike_zd (fun _ => ?_) (fun _ => ?_)) <;> first | hv_leaf | ob_leaf))
macro_rules | `(tactic| zd_leaf) => `(tactic| ((with_reducible apply ik_modify); intro _ h; exact h))
macro_rules | `(tactic| zd_leaf) => `(tactic| ((with_reducible refine ik_doExtendedOp ?_ _); intro _ _ h; exact h))
macro_rules | `(tactic| zd_leaf) => `(tactic| with_reducible exact ik_getObject _)

end

end Fl4Proofs.P3.SInvDV
