/-
P3x for virtualization (line virt, gen 3; proofs/VIRT-PLAN.md §10 R7 (b)): **no slot holds a virtualization cap,
kept by the ported deletion** (spec side only).

* `NVC σ`: no slot cap of `σ` (vih2's cap view `capOpt`) is a virtualization cap (`IsVirtCap`, VirtP3x). It is
  `NoVirtCaps` read through the slots (`nvc_of_noVirtCaps`). It reads only the cap view `hV`, so it is a `WLH`
  predicate and the generated frames of SpecInvValidIrqHandlersF1..F4 keep it.
* Writers, after sl5's `KS` (SpecInvSlKA) with `¬ IsVirtCap` for `KOk σ0`: `nvc_setCap` (a non-virtualization cap),
  `nvc_capSwapForDelete` (both caps re-read), `nvc_emptySlot`, `nvc_capDeleteOne`, `nvc_deletingIrqHandler`,
  `nvc_finaliseCap`, `nv_finaliseCap_rem` (the remainder of `finalise_cap` is null, a Zombie or the cap itself),
  **`nvc_recDel`**, `nvc_capDelete`, **`nvc_capRevoke`**.

No premises. New file only.
-/
import Fl4Proofs.P3.SpecInvSlKA
import Fl4Spec.Ext.VirtP3x
open Classical

namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU
open Fl4Proofs.P3.SInvV (hV hV_cap WLH wlh_of_hV hv_isFinalCap hv_preemptionPoint setIrqState_out)

noncomputable section

set_option maxHeartbeats 2000000
set_option maxErrors 2000

/-- **No slot holds a virtualization cap.** -/
def NVC (σ : State Unit) : Prop :=
  ∀ (sl : CslotPtr) (c : Cap), capOpt (σ.kheap sl.1) sl.2 = some c → ¬ IsVirtCap c

theorem NVC.view {σ σ' : State Unit} (e : hV σ' = hV σ) (h : NVC σ) : NVC σ' :=
  fun sl c hc => h sl c (by rw [← hV_cap e]; exact hc)

instance : WLH NVC := wlh_of_hV fun _ _ e h => h.view e

/-- `NoVirtCaps` gives `NVC`. -/
theorem nvc_of_noVirtCaps {σ : State Unit} (h : NoVirtCaps σ) : NVC σ := by
  intro sl c hc
  obtain ⟨p, r⟩ := sl
  cases hk : σ.kheap p with
  | none => simp [hk, capOpt] at hc
  | some ko =>
    rw [hk] at hc
    refine h p ko hk c ?_
    cases ko with
    | cnode sz cn =>
      simp only [capOpt] at hc
      split at hc
      · exact ⟨r, hc⟩
      · cases hc
    | tcb t => exact ⟨r, hc⟩
    | _ => simp [capOpt] at hc

/-! ## `set_cap` and the fields `NVC` does not read -/

theorem nvc_setCap {c : Cap} (sl : CslotPtr) (hc : ¬ IsVirtCap c) : IK NVC (setCap (Z := Unit) c sl) := by
  obtain ⟨o, r⟩ := sl
  intro σ hσ x hx sl' c' h
  obtain ⟨p, l⟩ := sl'
  rw [vfh_setCap_view hx p l] at h
  split at h
  · cases h; exact hc
  · exact hσ (p, l) c' h

theorem nvc_setCap_null (sl : CslotPtr) : IK NVC (setCap (Z := Unit) .nullCap sl) :=
  nvc_setCap sl (fun h => h)

theorem nvc_of_kheap {σ σ' : State Unit} (hk : σ'.kheap = σ.kheap) (h : NVC σ) : NVC σ' :=
  fun sl c hc => h sl c (by rw [hk] at hc; exact hc)

theorem nvc_setCdt (t : Cdt) : IK NVC (setCdt (Z := Unit) t) := by
  unfold setCdt
  intro σ hσ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact nvc_of_kheap rfl hσ

theorem nvc_updateCdt (f : Cdt → Cdt) : IK NVC (updateCdt (Z := Unit) f) := by
  unfold updateCdt
  exact ik_bind (ik_gets _) fun _ => nvc_setCdt _

theorem nvc_setOriginal (sl : CslotPtr) (b : Bool) : IK NVC (setOriginal (Z := Unit) sl b) := by
  unfold setOriginal
  exact ik_bind (ik_gets _) fun _ => ik_modify fun _ h => nvc_of_kheap rfl h

theorem nvc_doExtendedOp (eop : DetExtMonad Unit) : IK NVC (doExtendedOp (Z := Unit) eop) :=
  ik_doExtendedOp (fun _ _ h => nvc_of_kheap rfl h) eop

theorem nvc_setIrqState (st : IrqState) (i : Irq) : IK NVC (setIrqState (Z := Unit) st i) := by
  intro σ hσ x hx
  obtain ⟨hk, -⟩ := setIrqState_out hx
  exact nvc_of_kheap hk hσ

theorem nvc_doMachineOp {α : Type} (mop : NonDet MachineState α) : IK NVC (doMachineOp (Z := Unit) mop) :=
  ik_doMachineOp (fun _ _ h => nvc_of_kheap rfl h) mop

macro "nvc_tail" : tactic => `(tactic| repeat' (first
  | (with_reducible exact nvc_setCdt _) | (with_reducible exact nvc_updateCdt _)
  | (with_reducible exact nvc_setOriginal _ _) | (with_reducible exact nvc_doExtendedOp _)
  | (with_reducible exact nvc_setIrqState _ _) | (with_reducible exact nvc_setCap_null _)
  | (with_reducible exact nvc_doMachineOp _)
  | hv_leaf | ik_step0 | ik_unfold))

/-! ## The CSpace writers of deletion -/

theorem nvc_capSwap {c1 c2 : Cap} (s1 s2 : CslotPtr) (k1 : ¬ IsVirtCap c2) (k2 : ¬ IsVirtCap c1) :
    IK NVC (capSwap (Z := Unit) c1 s1 c2 s2) := by
  unfold capSwap
  refine ik_bind (nvc_setCap _ k1) fun _ => ?_
  refine ik_bind (nvc_setCap _ k2) fun _ => ?_
  nvc_tail

/-- **`cap_swap_for_delete`**: both caps are re-read from their slots. -/
theorem nvc_capSwapForDelete (s1 s2 : CslotPtr) : IK NVC (capSwapForDelete (Z := Unit) s1 s2) := by
  unfold capSwapForDelete
  refine ik_when _ ?_
  intro σ
  refine ikp_getCap_bind fun c1 hc1 => ikp_getCap_bind fun c2 hc2 => ?_
  intro hσ x hx
  exact nvc_capSwap _ _ (hσ _ _ hc2) (hσ _ _ hc1) σ hσ x hx

theorem nvc_emptySlot (sl : CslotPtr) (c : Cap) : IK NVC (emptySlot (Z := Unit) sl c) := by
  unfold emptySlot postCapDeletion deletedIrqHandler
  nvc_tail

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact nvc_emptySlot _ _)

theorem nvc_capDeleteOne (sl : CslotPtr) : IK NVC (capDeleteOne (Z := Unit) sl) := by
  unfold capDeleteOne; nvc_tail

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact nvc_capDeleteOne _)

theorem nvc_deletingIrqHandler (irq : Irq) : IK NVC (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler; nvc_tail

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact nvc_deletingIrqHandler _)

theorem nvc_finaliseCap (c : Cap) (b : Bool) : IK NVC (finaliseCap (Z := Unit) c b) := by
  unfold finaliseCap; nvc_tail

macro "nvv_auto" : tactic => `(tactic| repeat' (first
  | (refine vov_bind fun _ => ?_) | (refine vov_bind' fun _ => ?_)
  | (refine vov_liftM fun _ => ?_)
  | exact vov_fail
  | (refine vov_pure ?_) | (refine vov_pure' ?_)
  | (refine vov_ite ?_ ?_)
  | exact fun _ h => h
  | exact fun h => h
  | (dsimp only)
  | split))

/-- **`finalise_cap`'s remainder is null, a Zombie or the finalised cap.** -/
theorem nv_finaliseCap_rem (c : Cap) (fin : Bool) :
    VOV (fun p : Cap × Cap => ¬ IsVirtCap c → ¬ IsVirtCap p.1) (finaliseCap (Z := Unit) c fin) := by
  cases c <;> simp only [finaliseCap, archFinaliseCap] <;> nvv_auto

theorem nvc_recDelF {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k, IK NVC (f k)) (k : RecDelCall) : IKE NVC (recDelF (Z := Unit) f k) := by
  have hu : ∀ k, IKE (ε := Unit) NVC (f k : NonDetE (State Unit) Unit (Bool × Cap)) := hrec
  cases k with
  | cTEDeleteCall sl e =>
    unfold recDelF withoutPreemption
    try dsimp only
    refine ike_bind (hu _) fun _ => ?_
    nvc_tail
  | finaliseSlotCall sl e =>
    unfold recDelF withoutPreemption
    try dsimp only
    intro σ hσ
    refine ikpE_getCap_bind (fun cap hcap => ?_) hσ
    have hk : ¬ IsVirtCap cap := hσ _ _ hcap
    refine ikp_of_ik (?_ : IKE NVC _) σ
    refine ike_ite _ (ike_returnOk _) ?_
    refine ike_bind (ike_liftE (hv_isFinalCap _)) (fun fin => ?_)
    intro s hs x hx
    obtain ⟨y, hy, hx⟩ := vfh_run_liftE_bind_mem hx
    have hy1 := nvc_finaliseCap cap fin s hs y hy
    have hrem : ¬ IsVirtCap y.1.1 := nv_finaliseCap_rem cap fin s y hy hk
    obtain ⟨⟨rem, ci⟩, s1⟩ := y
    dsimp only at hx hrem hy1
    refine (?_ : IKE NVC _) s1 hy1 x hx
    refine ike_ite _ (ike_returnOk _) (ike_ite _ ?_ ?_)
    · exact ike_bind (ike_liftE (nvc_setCap _ hrem)) fun _ => ike_returnOk _
    · refine ike_bind (ike_liftE (nvc_setCap _ hrem)) fun _ => ?_
      refine ike_bind (hu _) fun _ => ?_
      exact ike_bind hv_preemptionPoint fun _ => hu _
  | reduceZombieCall c sl e =>
    by_cases hz : ∃ ptr bits n, c = .zombie ptr bits (n + 1)
    · obtain ⟨ptr, bits, n, rfl⟩ := hz
      cases e
      · unfold recDelF withoutPreemption
        try dsimp only
        refine ike_returnOk_bind ?_
        refine ike_bind (ike_assertE _) fun _ => ?_
        exact ike_bind (ike_liftE (nvc_capSwapForDelete _ _)) fun _ => ike_returnOk _
      · unfold recDelF withoutPreemption
        try dsimp only
        refine ike_returnOk_bind ?_
        refine ike_bind (hu _) fun _ => ?_
        intro s hs
        refine ikpE_getCap_bind (fun nc hnc => ?_) hs
        by_cases hz : nc = .zombie ptr bits (n + 1)
        · rw [if_pos hz]; subst hz
          exact ikp_of_ik (ike_bind (ike_liftE (nvc_setCap (c := .zombie ptr bits n) _ (fun h => h))) fun _ => ike_returnOk _) s
        · rw [if_neg hz]; exact ikp_of_ik (ike_bind (ike_assertE _) fun _ => ike_returnOk _) s
    · have e1 : recDelF (Z := Unit) f (.reduceZombieCall c sl e) = NonDetE.liftE NonDet.fail := by
        rw [recDelF.eq_def]
        split <;> first | rfl | (exfalso; apply hz; exact ⟨_, _, _, rfl⟩) | (exfalso; apply hz; simp_all)
      rw [e1]
      intro σ _ x hx
      unfold NonDetE.liftE at hx
      rw [ExceptT.run_lift] at hx
      obtain ⟨_, h, _⟩ := hx
      exact h.elim

/-- **`rec_del` keeps `NVC`** for every call. -/
theorem nvc_recDel (k : RecDelCall) : IKE NVC (recDel (Z := Unit) k) := by
  unfold recDel
  exact ik_lfp (fun f hf k => nvc_recDelF hf k) k

theorem nvc_capDelete (sl : CslotPtr) : IKE NVC (capDelete (Z := Unit) sl) := by
  unfold capDelete
  exact ike_bind (nvc_recDel (.cTEDeleteCall sl true)) fun _ => ike_returnOk _

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact nvc_capDelete _)

theorem nvc_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, IK NVC (f k)) (sl : CslotPtr) : IKE NVC (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, IKE (ε := Unit) NVC (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeF withoutPreemption selectExt
  nvc_tail
  all_goals exact hrec' _

/-- **`cap_revoke` keeps `NVC`.** -/
theorem nvc_capRevoke (sl : CslotPtr) : IKE NVC (capRevoke (Z := Unit) sl) := by
  unfold capRevoke
  exact ik_lfp (fun f hf k => nvc_capRevokeF hf k) sl

end

end Fl4Proofs.P3.SInvL
