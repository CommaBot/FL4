/-
P3x for virtualization, spec side (line virt, gen 5; proofs/VIRT-PLAN.md §10, table row "NoVirt reachability"):
**the cap writers of the ported kernel keep `NVC`** (no slot holds a virtualization cap), and with them the
syscall entry's budget check.

This is vih3's writer families (SpecInvValidIrqHandlersW / Y / G, `IKH VI` with the carried cap fact `CA`)
restated for `NVC` (VirtNvCaps) with the cap fact "not a virtualization cap" (`¬ IsVirtCap`). That fact does not
read the state, so the carried IRQ-state predicate `R` of vih3 is replaced by plain hypotheses.

* Leaves (`IKH NVC`): `set_cap` of a non-virtualization cap (VirtNvCaps' `nvc_setCap`, as an `hv_leaf` with the
  side condition `nvc_side`), `cap_insert` (VirtNvTcb), `cap_move`, `cap_swap`, `cap_swap_for_delete`,
  `set_untyped_cap_as_full`.
* The carry (vih3's `OkV`): `okn_lookupCap` / `okn_lookupExtraCaps` (a looked-up cap sits in a slot of an `NVC`
  state), `okn_deriveCap` (`derive_cap` of a non-virtualization cap is not one: X64 `arch_derive_cap` returns the
  cap itself, a null cap, or an unmapped frame cap).
* IPC: `nvc_transferCapsLoop`, `nvc_transferCaps`, **`nvc_doNormalTransfer`**, `nvc_doIpcTransfer`,
  `nvc_sendIpc`, `nvc_sendFaultIpc`, `nvc_handleTimeout`; budget: `nvc_endTimeslice`, `nvc_chargeBudget`,
  `nvc_checkBudget`, **`nvc_checkBudgetRestart`**; `nvc_updateTimeStamp`.

No premises; no [J]/[P]/[W]/[S]. New file only.
-/
import Fl4Proofs.P3.VirtR7eK
open Classical

namespace Fl4Proofs.P3.VirtNvcW
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvV Fl4Proofs.P3.SInvL Fl4Proofs.P3.SInvDom
  Fl4Proofs.P3.VirtNvTcb

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

/-- Side conditions `¬ IsVirtCap c`. -/
macro "nvc_side" : tactic => `(tactic| first
  | assumption
  | (intro h; exact h)
  | (intro h; cases h; done)
  | (simp [IsVirtCap]; done)
  | (intro h; simp_all [IsVirtCap]; done))

macro_rules | `(tactic| hv_leaf) => `(tactic| ((with_reducible refine nvc_setCap _ ?_); nvc_side))
macro_rules | `(tactic| hv_leaf) => `(tactic| ((with_reducible refine nvc_capInsert _ _ ?_); nvc_side))

/-! ## Cap writers -/

theorem nvc_capMove {c : Cap} (src dst : CslotPtr) (hc : ¬ IsVirtCap c) : IKH NVC (capMove (Z := Unit) c src dst) := by
  unfold capMove; hv_auto

macro_rules | `(tactic| hv_leaf) => `(tactic| ((with_reducible refine nvc_capMove _ _ ?_); nvc_side))
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact nvc_capSwapForDelete _ _)

/-! ## The carry: looked-up and derived caps -/

/-- A looked-up cap is not a virtualization cap. -/
theorem okn_lookupCap {σ0 : State Unit} (hv : NVC σ0) (t : ObjRef) (c : CapRef) (cp : ObjRef) (rp : Bool) :
    OkV σ0 (fun r : Cap × CslotPtr => ¬ IsVirtCap r.1)
      (capFaultOnFailure (Z := Unit) cp rp (lookupCapAndSlot t c)) := by
  intro s hs a s' h
  have e : hV s' = hV s :=
    hv_capFaultOnFailure (P := fun x => hV x = hV s) cp rp _ (hv_lookupCapAndSlot t c) s rfl _ h
  have hc := okdAt_capFault cp rp (okCap_lookupCapAndSlot t c s) a s' h
  have e' := e.trans hs
  exact ⟨e', (hv.view e') _ _ hc⟩

theorem okn_lookupExtraCaps {σ0 : State Unit} (hv : NVC σ0) (t : ObjRef) (b : Option Data) (mi : MessageInfo) :
    OkV σ0 (fun caps : List (Cap × CslotPtr) => ∀ c ∈ caps, ¬ IsVirtCap c.1)
      (lookupExtraCaps (Z := Unit) t b mi) := by
  unfold lookupExtraCaps
  exact okv_bind (okv_frame fun v => ike_liftE (P := fun s => hV s = v) (hv_getExtraCptrs _ _)) fun cptrs _ =>
    okv_mapME (fun _ => okn_lookupCap hv _ _ _ _) cptrs

theorem okn_deriveCap {σ0 : State Unit} (sl : CslotPtr) (c : Cap) (hc : ¬ IsVirtCap c) :
    OkV σ0 (fun c' => ¬ IsVirtCap c') (deriveCap (Z := Unit) sl c) := by
  cases c with
  | archObjectCap a =>
    simp only [deriveCap]; unfold archDeriveCap
    split <;> first | exact okv_throw _ | exact okv_returnOk hc | exact okv_returnOk (fun h => h)
  | untypedCap d b n f =>
    simp only [deriveCap]
    exact okv_bind (okv_frame fun v => hv_ensureNoChildren (P := fun s => hV s = v) _) fun _ _ => okv_returnOk hc
  | zombie => simp only [deriveCap]; exact okv_returnOk (fun h => h)
  | irqControlCap => simp only [deriveCap]; exact okv_returnOk (fun h => h)
  | _ => simp only [deriveCap]; exact okv_returnOk hc

/-! ## IPC cap transfer -/

theorem nvc_transferCapsLoop (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (caps : List (Cap × CslotPtr)) (sl : List CslotPtr) (mi : MessageInfo),
      (∀ c ∈ caps, ¬ IsVirtCap c.1) → IKH NVC (transferCapsLoop (Z := Unit) ep rb n caps sl mi)
  | n, [], sl, mi, _ => by unfold transferCapsLoop; exact ik_pure _
  | n, (c, s) :: cs, sl, mi, hR => by
    have ih := fun sl' mi' hR' => nvc_transferCapsLoop ep rb (n + 1) cs sl' mi' hR'
    have hR1 : ∀ c' ∈ cs, ¬ IsVirtCap c'.1 := fun c' hc' => hR c' (List.mem_cons_of_mem _ hc')
    unfold transferCapsLoop constOnFailure
    refine ik_catch ?_ (fun _ => ik_pure' _)
    refine ike_returnOk_bind ?_
    split
    · exact ike_bind (ike_liftE (hv_setExtraBadge _ _ _)) fun _ => ike_liftE (ih _ _ hR1)
    · split
      · intro σ h x hx
        obtain ⟨z, hz, ⟨c', hc', hx⟩ | ⟨e, he, rfl⟩⟩ := mem_bindE_inv' hx
        · obtain ⟨r, s1⟩ := z
          simp only at hc'; subst hc'
          have hs1 : NVC s1 := hv_deriveCap (P := NVC) _ _ σ h _ hz
          have hca := (okn_deriveCap (σ0 := σ) s c (hR (c, s) (List.mem_cons_self ..)) σ rfl c' s1 hz).2
          exact (show IKHE NVC _ from
            ike_bind (ike_whenE _ (ike_throw _)) fun _ =>
              ike_bind (ike_liftE (nvc_capInsert _ _ hca)) fun _ =>
              ike_liftE (ih _ _ hR1)) s1 hs1 x hx
        · exact hv_deriveCap (P := NVC) _ _ σ h _ hz
      · exact ike_returnOk _

theorem nvc_transferCaps (info : MessageInfo) (caps : List (Cap × CslotPtr)) (ep : Option ObjRef) (r : ObjRef)
    (rb : Option ObjRef) (hR : ∀ c ∈ caps, ¬ IsVirtCap c.1) :
    IKH NVC (transferCaps (Z := Unit) info caps ep r rb) := by
  unfold transferCaps
  refine ik_bind (hv_getReceiveSlots _ _) fun _ => ik_pure_bind ?_
  split
  · exact ik_pure _
  · exact nvc_transferCapsLoop _ _ _ _ _ _ hR

/-- A bind whose first step yields a fact for the rest. -/
theorem ik_bind_carry {α β : Type} {m : NonDet (State Unit) α} {k : α → NonDet (State Unit) β}
    {Q : α → Prop} (hm : ∀ σ, NVC σ → ∀ y ∈ (m σ).1, NVC y.2 ∧ Q y.1)
    (hk : ∀ a, Q a → IKH NVC (k a)) : IKH NVC (m >>= k) := by
  intro σ h x ⟨y, hy, hx⟩
  obtain ⟨h1, hq⟩ := hm σ h y hy
  exact hk y.1 hq y.2 h1 x hx

theorem nvc_doNormalTransfer (sender : ObjRef) (sbuf ep : Option ObjRef) (badge : Data) (grant : Bool)
    (receiver : ObjRef) (rbuf : Option ObjRef) :
    IKH NVC (doNormalTransfer (Z := Unit) sender sbuf ep badge grant receiver rbuf) := by
  unfold doNormalTransfer
  refine ik_bind (hv_getMessageInfo _) fun mi => ?_
  dsimp only
  split
  all_goals refine ik_bind_carry (Q := fun (caps : List (Cap × CslotPtr)) => ∀ c ∈ caps, ¬ IsVirtCap c.1) ?_ (fun caps hcaps => ?_)
  · intro σ h y hy
    unfold NonDetE.catch at hy
    obtain ⟨z, hz, hy⟩ := hy
    obtain ⟨r, s⟩ := z
    have hs : NVC s := hv_lookupExtraCaps (P := NVC) _ _ _ σ h _ hz
    cases r with
    | ok a =>
      obtain rfl := Set.mem_singleton_iff.1 hy
      exact ⟨hs, (okn_lookupExtraCaps h _ _ _ σ rfl a s hz).2⟩
    | error e =>
      obtain rfl := Set.mem_singleton_iff.1 hy
      exact ⟨hs, fun c hc => by cases hc⟩
  · refine ik_bind (hv_copyMrs _ _ _ _ _) fun _ => ik_bind (nvc_transferCaps _ _ _ _ _ hcaps) fun _ =>
      ik_bind (hv_setMessageInfo _ _) fun _ => hv_asUser _ _
  · intro σ h y hy
    obtain rfl := Set.mem_singleton_iff.1 hy
    exact ⟨h, fun c hc => by cases hc⟩
  · refine ik_bind (hv_copyMrs _ _ _ _ _) fun _ => ik_bind (nvc_transferCaps _ _ _ _ _ hcaps) fun _ =>
      ik_bind (hv_setMessageInfo _ _) fun _ => hv_asUser _ _

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact nvc_doNormalTransfer _ _ _ _ _ _ _)

/-! ## IPC, timeouts, budget -/

theorem nvc_doIpcTransfer (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) :
    IKH NVC (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact nvc_doIpcTransfer _ _ _ _ _)

theorem nvc_sendIpc (block call : Bool) (badge : Badge) (canGrant canGrantReply canDonate : Bool)
    (thread epptr : ObjRef) :
    IKH NVC (sendIpc (Z := Unit) block call badge canGrant canGrantReply canDonate thread epptr) := by
  unfold sendIpc; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact nvc_sendIpc _ _ _ _ _ _ _ _)

theorem nvc_sendFaultIpc (tptr : ObjRef) (handlerCap : Cap) (fault : Fault) (canDonate : Bool) :
    IKH NVC (sendFaultIpc (Z := Unit) tptr handlerCap fault canDonate) := by
  unfold sendFaultIpc; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact nvc_sendFaultIpc _ _ _ _)

theorem nvc_handleTimeout (tptr : ObjRef) (ex : Fault) : IKH NVC (handleTimeout (Z := Unit) tptr ex) := by
  unfold handleTimeout; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact nvc_handleTimeout _ _)

theorem nvc_endTimeslice (canTimeout : Bool) : IKH NVC (endTimeslice (Z := Unit) canTimeout) := by
  unfold endTimeslice; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact nvc_endTimeslice _)

theorem nvc_chargeBudget (consumed : Ticks) (canTimeout : Bool) : IKH NVC (chargeBudget (Z := Unit) consumed canTimeout) := by
  unfold chargeBudget; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact nvc_chargeBudget _ _)

theorem nvc_checkBudget : IKH NVC (checkBudget (Z := Unit)) := by
  unfold checkBudget; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact nvc_checkBudget)

/-- **`check_budget_restart` keeps `NVC`.** -/
theorem nvc_checkBudgetRestart : IKH NVC (checkBudgetRestart (Z := Unit)) := by
  unfold checkBudgetRestart; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact nvc_checkBudgetRestart)

theorem nvc_updateTimeStamp : IKH NVC (updateTimeStamp (Z := Unit)) := WLH.uts

end

end Fl4Proofs.P3.VirtNvcW
