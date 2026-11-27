/-
P3 (line irqfix, gen 3): vih3's deletion path (SpecInvValidIrqHandlersX) for l4v's `valid_irq_handlers`
(`VIL`, SpecInvVihLW): `empty_slot` with the cleanup cap's line named only by the emptied slot, `cap_delete_one`,
`deleting_irq_handler`, `finalise_cap`, `rec_del` (least fixed point with vih3's result-dependent post
`RDPostL`), `cap_delete`, `cap_revoke`. The line becomes inactive only after its last handler cap is gone
(`hkl_setIrqState_inactive`). vih3's generic pieces (`Uniq`, `HT`, `ht_lfp`, `RV`, `rv_finaliseCap`) are reused.
No premise; no sorry.
-/
import Fl4Proofs.P3.SpecInvVihLW
import Fl4Proofs.P3.SpecInvValidIrqHandlersX
open Classical

namespace Fl4Proofs.P3.SInvVL
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvDom Fl4Proofs.P3.SInvV

noncomputable section

set_option maxHeartbeats 1000000

/-! ## `empty_slot` and `cap_delete_one` -/

theorem vil_postCapDeletion_tail {c : Cap} {sl : CslotPtr} {σ : State Unit} (h : VIL σ)
    (hu : ∀ irq, c = .irqHandlerCap irq → Uniq irq sl σ) :
    ∀ x ∈ ((setCap (Z := Unit) .nullCap sl >>= fun _ => postCapDeletion (Z := Unit) c) σ).1, VIL x.2 := by
  rintro x ⟨y, hy, hx⟩
  have h1 : VIL y.2 := vhl_setCap .nullCap sl (fun _ _ => cal_noH (fun _ h => by cases h) _) σ h y hy
  cases c with
  | irqHandlerCap irq =>
    have hn := setCap_null_unique (hu irq rfl) hy
    simp only [postCapDeletion, deletedIrqHandler] at hx
    exact ⟨vim_sis _ _ _ h1.1 x hx, h1.2.1.hk (hkl_setIrqState_inactive hn x hx), trivial⟩
  | archObjectCap a =>
    simp only [postCapDeletion] at hx; exact (hv_archPostCapDeletion a : IKH VIL _) _ h1 x hx
  | _ => simp only [postCapDeletion] at hx; exact (ik_pure () : IKH VIL _) _ h1 x hx

/-- `VIL` and the uniqueness of a handler cleanup cap's line. -/
def ESQL (c : Cap) (sl : CslotPtr) (s : State Unit) : Prop :=
  VIL s ∧ ∀ irq, c = .irqHandlerCap irq → Uniq irq sl s

instance (c : Cap) (sl : CslotPtr) : WLH (ESQL c sl) :=
  have : WLH (fun s : State Unit => ∀ irq, c = .irqHandlerCap irq → Uniq irq sl s) :=
    wlh_of_hV fun σ σ' e h irq hc p cref hc' => h irq hc p cref (by rw [← hV_cap e]; exact hc')
  inferInstanceAs (WLH fun s => VIL s ∧ ∀ irq, c = .irqHandlerCap irq → Uniq irq sl s)

/-- **`empty_slot`** with the cleanup cap's line named only by the emptied slot. -/
theorem vil_emptySlot_p (sl : CslotPtr) (c : Cap) (σ : State Unit)
    (hu : ∀ irq, c = .irqHandlerCap irq → Uniq irq sl σ) : IKp VIL σ (emptySlot (Z := Unit) sl c) := by
  unfold emptySlot
  refine ikp_getCap_bind fun cap _ => ?_
  split
  · exact ikp_of_ik (ik_pure _) σ
  · intro h x hx
    have key : ∀ s, ESQL c sl s → ∀ x ∈ ((setCap (Z := Unit) .nullCap sl >>= fun _ => postCapDeletion (Z := Unit) c) s).1,
        VIL x.2 := fun s hs => vil_postCapDeletion_tail hs.1 hs.2
    obtain ⟨y1, hy1, hx⟩ := hx
    obtain ⟨y2, hy2, hx⟩ := hx
    obtain ⟨y3, hy3, hx⟩ := hx
    obtain ⟨y4, hy4, hx⟩ := hx
    obtain ⟨y5, hy5, hx⟩ := hx
    obtain ⟨y6, hy6, hx⟩ := hx
    obtain rfl := Set.mem_singleton_iff.1 hy1
    obtain rfl := Set.mem_singleton_iff.1 hy2
    obtain rfl := Set.mem_singleton_iff.1 hy3
    have q4 : ESQL c sl y4.2 := hv_setCdt (P := ESQL c sl) _ _ ⟨h, hu⟩ y4 hy4
    have q5 : ESQL c sl y5.2 := ik_doExtendedOp (P := ESQL c sl)
      (fun σ e h => WLH.view σ { σ with exst := e } (by rfl) (by rfl) h) _ _ q4 y5 hy5
    have q6 : ESQL c sl y6.2 := hv_setOriginal (P := ESQL c sl) _ _ _ q5 y6 hy6
    exact key _ q6 x hx

section U
variable {U : State Unit → Prop} [WLH U]

theorem vhlu_setCap_null (hU : ∀ sl σ x, U σ → x ∈ (setCap (Z := Unit) .nullCap sl σ).1 → U x.2) (sl : CslotPtr) :
    IKH (fun σ => VIL σ ∧ U σ) (setCap (Z := Unit) .nullCap sl) :=
  fun σ h x hx => ⟨vhl_setCap .nullCap sl (fun _ _ => cal_noH (fun _ h => by cases h) _) σ h.1 x hx, hU sl σ x h.2 hx⟩

/-- **`cap_delete_one`** (cleanup `NullCap`: no IRQ state change) keeps `VIL ∧ U`. -/
theorem vil_capDeleteOne_u (hU : ∀ sl σ x, U σ → x ∈ (setCap (Z := Unit) .nullCap sl σ).1 → U x.2)
    (sl : CslotPtr) : IKH (fun σ => VIL σ ∧ U σ) (capDeleteOne (Z := Unit) sl) := by
  unfold capDeleteOne emptySlot
  simp only [postCapDeletion]
  repeat' (first | (with_reducible exact vhlu_setCap_null hU _) | hv_leaf | ik_step0 | ik_unfold)

end U

theorem vil_capDeleteOne (sl : CslotPtr) : IKH VIL (capDeleteOne (Z := Unit) sl) := by
  have : WLH (fun _ : State Unit => True) := wlh_of_hV fun _ _ _ _ => trivial
  intro σ h x hx
  exact (vil_capDeleteOne_u (U := fun _ => True) (fun _ _ _ _ _ => trivial) sl σ ⟨h, trivial⟩ x hx).1

theorem vil_deletingIrqHandler_uniq (irq : Irq) (sl : CslotPtr) :
    IKH (fun σ => VIL σ ∧ Uniq irq sl σ) (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler
  exact ik_bind (ik_gets _) fun s => vil_capDeleteOne_u (fun _ _ _ h hx => uniq_setCap_null h hx) s

theorem vil_deletingIrqHandler (irq : Irq) : IKH VIL (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler
  exact ik_bind (ik_gets _) fun s => vil_capDeleteOne s

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vil_capDeleteOne _)
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vil_deletingIrqHandler _)

/-- `finalise_cap` keeps `VIL`. -/
theorem vil_finaliseCap (c : Cap) (fin : Bool) : IKH VIL (finaliseCap (Z := Unit) c fin) := by
  cases c <;> unfold finaliseCap <;> hv_auto

/-! ## `rec_del` -/

/-- The post of `rec_del`: `VIL`, and a `FinaliseSlotCall slot` returning a
handler cleanup cap leaves its line named only by `slot`. -/
def RDPostL (k : RecDelCall) (r : Except Unit (Bool × Cap)) (s : State Unit) : Prop :=
  VIL s ∧ ∀ sl e, k = .finaliseSlotCall sl e → ∀ b irq, r = .ok (b, .irqHandlerCap irq) → Uniq irq sl s

theorem ik_of_ht_rdL {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (h : ∀ k, HT VIL (RDPostL k) (f k)) (k : RecDelCall) : IKHE (ε := Unit) VIL (f k : PMonad Unit (Bool × Cap)) :=
  fun σ hσ x hx => (h k σ hσ x hx).1

theorem ht_of_ik_rdL {k : RecDelCall} {m : NonDet (State Unit) (Except Unit (Bool × Cap))} (h : SInvV.IK VIL m)
    (hk : ∀ sl e, k ≠ .finaliseSlotCall sl e) : HT VIL (RDPostL k) m :=
  fun σ hσ x hx => ⟨h σ hσ x hx, fun sl e e' => absurd e' (hk sl e)⟩

set_option maxHeartbeats 4000000 in
/-- The `FinaliseSlotCall` step. -/
theorem ht_recDelF_finL {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k, HT VIL (RDPostL k) (f k)) (slot : CslotPtr) (ex : Bool) :
    HT VIL (RDPostL (.finaliseSlotCall slot ex)) (recDelF (Z := Unit) f (.finaliseSlotCall slot ex)).run := by
  have hrec' := ik_of_ht_rdL hrec
  have post_ok : ∀ s b c, VIL s → (∀ irq, c = .irqHandlerCap irq → Uniq irq slot s) →
      RDPostL (.finaliseSlotCall slot ex) (.ok (b, c)) s := by
    intro s b c h hu
    refine ⟨h, fun sl e he b' irq hr => ?_⟩
    simp only [RecDelCall.finaliseSlotCall.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    simp only [Except.ok.injEq, Prod.mk.injEq] at hr
    exact hu irq hr.2
  have post_err : ∀ e s, VIL s → RDPostL (.finaliseSlotCall slot ex) (.error e) s :=
    fun e s h => ⟨h, fun _ _ _ _ _ hr => by cases hr⟩
  unfold recDelF withoutPreemption
  -- the cap read
  refine hte_bind (Q' := fun r s => ∃ c, r = .ok c ∧ VIL s ∧ capOpt (s.kheap slot.1) slot.2 = some c)
    (fun σ h x hx => by
      obtain ⟨y, hy, rfl⟩ := mem_liftE_inv' hx
      obtain ⟨o, r⟩ := slot
      obtain ⟨e1, e2⟩ := vih_mem_getCap hy
      exact ⟨y.1, rfl, by rw [e1]; exact h, by rw [e1]; exact e2⟩) (fun cap => ?_)
    (fun e s ⟨_, he, _⟩ => by cases he)
  refine ht_mono (Q := fun s => VIL s ∧ capOpt (s.kheap slot.1) slot.2 = some cap) ?_
    (fun s ⟨c, hc, h, hs⟩ => by cases hc; exact ⟨h, hs⟩) (fun _ _ h => h)
  split
  · exact hte_returnOk fun s h => post_ok s _ _ h.1 (fun _ h' => by cases h')
  -- finality
  refine hte_bind (Q' := fun r s => ∃ b, r = .ok b ∧ VIL s ∧ capOpt (s.kheap slot.1) slot.2 = some cap ∧
      (b = true → isFinalCap' (Z := Unit) cap s))
    (fun σ h x hx => by
      obtain ⟨y, hy, rfl⟩ := mem_liftE_inv' hx
      unfold isFinalCap at hy
      obtain rfl := Set.mem_singleton_iff.1 hy
      exact ⟨_, rfl, h.1, h.2, fun hb => of_decide_eq_true hb⟩) (fun fin => ?_)
    (fun e s ⟨_, he, _⟩ => by cases he)
  refine ht_mono (Q := fun s => VIL s ∧ capOpt (s.kheap slot.1) slot.2 = some cap ∧
      (fin = true → isFinalCap' (Z := Unit) cap s)) ?_
    (fun s ⟨c, hc, h⟩ => by cases hc; exact h) (fun _ _ h => h)
  -- finalise_cap: remainder no handler cap, cleanup's line named only by `slot`
  refine hte_bind (Q' := fun r s => ∃ rc, r = .ok rc ∧ VIL s ∧ (∀ irq, rc.1 ≠ .irqHandlerCap irq) ∧
      (∀ irq, rc.2 = .irqHandlerCap irq → Uniq irq slot s)) ?_ (fun rc => ?_)
    (fun e s ⟨_, he, _⟩ => by cases he)
  · intro σ h x hx
    obtain ⟨y, hy, rfl⟩ := mem_liftE_inv' hx
    refine ⟨y.1, rfl, vil_finaliseCap cap fin σ h.1 y hy, (rv_finaliseCap cap fin σ y hy).1, fun irq hc => ?_⟩
    have hcap := (rv_finaliseCap cap fin σ y hy).2 irq hc
    subst hcap
    cases fin with
    | false =>
      simp only [finaliseCap] at hy
      rw [if_neg (by simp)] at hy
      rw [Set.mem_singleton_iff.1 hy] at hc; cases hc
    | true =>
      have hu := final_handler_unique (h.2.2 rfl) h.2.1
      simp only [finaliseCap, if_true] at hy
      obtain ⟨z, hz, hy⟩ := hy
      rw [Set.mem_singleton_iff.1 hy]
      exact (vil_deletingIrqHandler_uniq irq slot σ ⟨h.1, hu⟩ z hz).2
  obtain ⟨rem, cl⟩ := rc
  refine ht_mono (Q := fun s => VIL s ∧ (∀ irq, rem ≠ .irqHandlerCap irq) ∧
      (∀ irq, cl = .irqHandlerCap irq → Uniq irq slot s)) ?_
    (fun s ⟨c, hc, h⟩ => by cases hc; exact h) (fun _ _ h => h)
  dsimp only
  split
  · exact hte_returnOk fun s h => post_ok s _ _ h.1 h.2.2
  split
  · refine hte_bind (Q' := fun r s => ∃ u, r = .ok u ∧ VIL s) ?_ (fun _ => ?_)
      (fun e s ⟨_, he, _⟩ => by cases he)
    · intro σ h x hx
      obtain ⟨y, hy, rfl⟩ := mem_liftE_inv' hx
      exact ⟨_, rfl, vhl_setCap rem slot (fun _ _ => cal_noH h.2.1 _) σ h.1 y hy⟩
    · exact ht_mono (hte_returnOk (Q := VIL) fun s h => post_ok s _ _ h (fun _ h' => by cases h'))
        (fun s ⟨_, hc, h⟩ => h) (fun _ _ h => h)
  · refine hte_bind (Q' := fun r s => ∃ u, r = .ok u ∧ VIL s) ?_ (fun _ => ?_)
      (fun e s ⟨_, he, _⟩ => by cases he)
    · intro σ h x hx
      obtain ⟨y, hy, rfl⟩ := mem_liftE_inv' hx
      exact ⟨_, rfl, vhl_setCap rem slot (fun _ _ => cal_noH h.2.1 _) σ h.1 y hy⟩
    refine ht_mono (Q := VIL) ?_ (fun s ⟨_, _, h⟩ => h) (fun _ _ h => h)
    refine hte_bind (Q' := fun r s => VIL s) (fun σ h x hx => hrec' _ σ h x hx) (fun _ => ?_) (fun e s h => post_err e s h)
    refine hte_bind (Q' := fun r s => VIL s) (fun σ h x hx => hv_preemptionPoint σ h x hx) (fun _ => ?_)
      (fun e s h => post_err e s h)
    exact hrec _

set_option maxHeartbeats 4000000 in
/-- One step of `rec_del`, its recursive calls satisfying `RDPostL`. -/
theorem ht_recDelFL {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k, HT VIL (RDPostL k) (f k)) (k : RecDelCall) : HT VIL (RDPostL k) (recDelF (Z := Unit) f k) := by
  have hrec' := ik_of_ht_rdL hrec
  cases k with
  | finaliseSlotCall sl e => exact ht_recDelF_finL hrec sl e
  | cTEDeleteCall sl e =>
    have hk : ∀ sl' e', RecDelCall.cTEDeleteCall sl e ≠ .finaliseSlotCall sl' e' := fun _ _ h => by cases h
    show HT VIL (RDPostL _) (recDelF (Z := Unit) f (.cTEDeleteCall sl e)).run
    unfold recDelF withoutPreemption
    refine hte_bind (Q' := RDPostL (.finaliseSlotCall sl e)) (hrec _) (fun r => ?_)
      (fun er s h => ⟨h.1, fun _ _ h' => absurd h' (hk _ _)⟩)
    obtain ⟨b, cl⟩ := r
    dsimp only
    refine hte_bind (Q' := fun r s => VIL s) ?_ (fun _ => hte_returnOk fun s h => ⟨h, fun _ _ h' => absurd h' (hk _ _)⟩)
      (fun er s h => ⟨h, fun _ _ h' => absurd h' (hk _ _)⟩)
    intro σ h x hx
    obtain ⟨y, hy, rfl⟩ := mem_liftE_inv' hx
    unfold NonDet.when at hy
    split at hy
    · exact vil_emptySlot_p sl cl σ (fun irq hc => h.2 sl e rfl b irq (by rw [hc])) h.1 y hy
    · rw [Set.mem_singleton_iff.1 hy]; exact h.1
  | reduceZombieCall c sl e =>
    refine ht_of_ik_rdL ?_ (fun _ _ h => by cases h)
    show IKHE VIL (recDelF (Z := Unit) f (.reduceZombieCall c sl e))
    unfold recDelF withoutPreemption
    split <;> (try (exfalso; simp_all; done)) <;> hv_auto
    all_goals exact hrec' _

/-- **`rec_del`** (module docstring). -/
theorem vil_recDel (k : RecDelCall) : HT VIL (RDPostL k) (recDel (Z := Unit) k) := by
  unfold recDel
  exact ht_lfp VIL RDPostL (fun f hf k => ht_recDelFL hf k) k

theorem vil_recDelE (k : RecDelCall) : IKHE (ε := Unit) VIL (recDel (Z := Unit) k) :=
  fun σ h x hx => (vil_recDel k σ h x hx).1

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vil_recDelE _)

theorem vil_capDelete (sl : CslotPtr) : IKHE (ε := Unit) VIL (capDelete (Z := Unit) sl) := by
  unfold capDelete; hv_auto

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vil_capDelete _)

theorem vil_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, IKH VIL (f k)) (sl : CslotPtr) : IKHE (ε := Unit) VIL (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, IKHE (ε := Unit) VIL (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeF withoutPreemption selectExt
  hv_auto
  all_goals exact hrec' _

theorem vil_capRevoke (sl : CslotPtr) : IKHE (ε := Unit) VIL (capRevoke (Z := Unit) sl) := by
  unfold capRevoke
  exact ik_lfp (fun f hf k => vil_capRevokeF hf k) sl

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vil_capRevoke _)

end

end Fl4Proofs.P3.SInvVL
