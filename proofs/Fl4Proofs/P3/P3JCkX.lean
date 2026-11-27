/-
P3 (line p3J, gen 16): **the cap-kind invariant `CKI` across the deletion path** (spec side only; outside the
`JAtZ` cone; part 2 of P3JCkW).

* `ck_postCapDeletion`, `ck_emptySlot` (`NullCap` written; the post-deletion work writes IRQ states / IO
  ports only).
* `rv_finaliseCap_kw`: `finalise_cap`'s remainder is `NullCap` or a zombie, so `KW` for every input.
* **`ck_recDel`** (`ik_lfp`): the `FinaliseSlotCall` step writes the remainder back (`KW`), the
  `ReduceZombieCall` steps swap two slot caps or write a smaller zombie; `ck_capDelete`, `ck_capRevoke`.

Named premises: none. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JCkW
open Classical

namespace Fl4Proofs.P3.SInvCk
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvV Fl4Proofs.P3.SInvDom Fl4Proofs.P3.SInvIo

noncomputable section

set_option maxHeartbeats 4000000

theorem ck_postCapDeletion (c : Cap) : IKH CKI (postCapDeletion (Z := Unit) c) := by
  cases c with
  | irqHandlerCap irq => simp only [postCapDeletion, deletedIrqHandler]; exact ck_setIrqState _ _
  | archObjectCap a =>
    simp only [postCapDeletion]
    cases a <;> simp only [archPostCapDeletion] <;> first
      | exact ik_pure _
      | (unfold freeIoportRange setIoportMask; hv_auto)
  | _ => exact ik_pure _

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact ck_postCapDeletion _)

theorem ck_emptySlot (sl : CslotPtr) (c : Cap) : IKH CKI (emptySlot (Z := Unit) sl c) := by
  unfold emptySlot; hv_auto

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact ck_emptySlot _ _)

macro "rv_auto_kw" : tactic => `(tactic| repeat' (first
  | (with_reducible refine rv_pure ?_; (try dsimp only); (try split) <;> first | trivial | (simp [KW]; done))
  | (with_reducible refine rv_liftM fun _ => ?_; first | trivial | (simp [KW]; done))
  | (refine rv_pure ?_; (try dsimp only); (try split) <;> first | trivial | (simp [KW]; done))
  | (with_reducible exact rv_fail)
  | (with_reducible refine rv_bind fun _ => ?_)
  | split))

/-- **`finalise_cap`'s remainder is `KW`** (`NullCap` or a zombie). -/
theorem rv_finaliseCap_kw (c : Cap) (fin : Bool) :
    RV (fun r : Cap × Cap => KW r.1) (finaliseCap (Z := Unit) c fin) := by
  cases c with
  | archObjectCap a =>
    simp only [finaliseCap]; unfold archFinaliseCap
    rv_auto_kw
  | _ => simp only [finaliseCap]; rv_auto_kw

set_option maxHeartbeats 8000000 in
theorem ck_recDelF {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k, IKH CKI (f k)) (k : RecDelCall) : IKHE (ε := Unit) CKI (recDelF (Z := Unit) f k) := by
  have hrec' : ∀ k, IKHE (ε := Unit) CKI (f k : NonDetE (State Unit) Unit (Bool × Cap)) := hrec
  cases k with
  | cTEDeleteCall sl e => unfold recDelF withoutPreemption; hv_auto; all_goals exact hrec' _
  | reduceZombieCall c sl e =>
    unfold recDelF withoutPreemption
    split <;> hv_auto
    all_goals exact hrec' _
  | finaliseSlotCall slot ex =>
    unfold recDelF withoutPreemption
    refine ike_bind (ike_liftE (by hv_auto)) fun cap => ?_
    split
    · exact ike_returnOk _
    refine ike_bind (ike_liftE (by hv_auto)) fun fin => ?_
    intro σ h x hx
    obtain ⟨z, hz, ⟨rc, hrc, hx⟩ | ⟨e, he, rfl⟩⟩ := mem_bindE_inv' hx
    · obtain ⟨y, hy, rfl⟩ := mem_liftE_inv' hz
      simp only [Except.ok.injEq] at hrc; subst hrc
      have hs1 : CKI y.2 := ck_finaliseCap cap fin σ h y hy
      have hrem : KW y.1.1 := rv_finaliseCap_kw cap fin σ y hy
      obtain ⟨⟨rem, cl⟩, s1⟩ := y
      dsimp only at hrem hs1 hx
      exact (show IKHE (ε := Unit) CKI _ by hv_auto; all_goals exact hrec' _) s1 hs1 x hx
    · obtain ⟨y, hy, rfl⟩ := mem_liftE_inv' hz
      exact ck_finaliseCap cap fin σ h y hy

theorem ck_recDel (k : RecDelCall) : IKHE (ε := Unit) CKI (recDel (Z := Unit) k) := by
  unfold recDel
  exact ik_lfp (fun f hf k => ck_recDelF hf k) k

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact ck_recDel _)

theorem ck_capDelete (sl : CslotPtr) : IKHE (ε := Unit) CKI (capDelete (Z := Unit) sl) := by
  unfold capDelete; hv_auto

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact ck_capDelete _)

theorem ck_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, IKH CKI (f k)) (sl : CslotPtr) : IKHE (ε := Unit) CKI (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, IKHE (ε := Unit) CKI (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeF withoutPreemption selectExt
  hv_auto
  all_goals exact hrec' _

theorem ck_capRevoke (sl : CslotPtr) : IKHE (ε := Unit) CKI (capRevoke (Z := Unit) sl) := by
  unfold capRevoke
  exact ik_lfp (fun f hf k => ck_capRevokeF hf k) sl

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact ck_capRevoke _)

end

end Fl4Proofs.P3.SInvCk
