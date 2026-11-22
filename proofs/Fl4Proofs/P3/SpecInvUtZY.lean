/-
P3 (DESIGN.md §9), invariant line G1 (g5g): **the cap half `HU U` across the
cap writers whose caps come from slots** (spec side only; outside the `JAtZ`
cone; g5c's SpecInvIoPortsY with `HU U` for `HI S`).

* `hu_setIrqState`, the machine operations, `deleted_irq_handler`: no cap write;
  `cap_delete_one`, `deleting_irq_handler`, `finalise_cap` (cleanup caps null).
* `hu_okv_lookupCap` / `hu_okv_lookupExtraCaps`: a looked-up cap is `UtIn U`
  when `HU U` holds at the lookup; `utIn_deriveCap`: `derive_cap` returns the
  cap itself or a cap that is no untyped cap.
* IPC: `hu_transferCapsLoop` / `hu_transferCaps`, `hu_doNormalTransfer`.
* `hu_checkCapAt_ins` (an untyped cap is `same_object_as` no cap, so a TCB
  install never inserts one), `hu_performAsidControlInvocation` (the parent cap
  re-read and written back full). The page / table maps and unmaps write arch
  caps only (no `AtSl` needed, unlike g5c).
-/
import Fl4Proofs.P3.SpecInvUtZW
open Classical

namespace Fl4Proofs.P3.SInvUZ
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvV Fl4Proofs.P3.SInvDom

noncomputable section

set_option maxHeartbeats 1000000

variable {U : UtSet}

/-! ## Writers of no cap outside the frames -/

theorem hu_setIrqState (st : IrqState) (i : Irq) : IKH (HU U) (setIrqState (Z := Unit) st i) := by
  intro σ h x hx p cref c hc
  obtain ⟨hk, -⟩ := setIrqState_out hx
  exact h p cref c (by rw [← hk]; exact hc)

theorem hu_dmo {α : Type} (mop : NonDet MachineState α) : IKH (HU U) (doMachineOp (Z := Unit) mop) :=
  ik_doMachineOp (fun _ _ h => h) mop

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hu_setIrqState _ _)
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hu_dmo _)

theorem hu_capDeleteOne (sl : CslotPtr) : IKH (HU U) (capDeleteOne (Z := Unit) sl) := by
  unfold capDeleteOne emptySlot
  simp only [postCapDeletion]
  hv_auto

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hu_capDeleteOne _)

theorem hu_deletingIrqHandler (irq : Irq) : IKH (HU U) (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler; hv_auto

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hu_deletingIrqHandler _)

theorem hu_finaliseCap (c : Cap) (fin : Bool) : IKH (HU U) (finaliseCap (Z := Unit) c fin) := by
  cases c <;> unfold finaliseCap <;> hv_auto

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hu_finaliseCap _ _)

/-! ## Looked-up caps -/

theorem hu_okv_lookupCap {σ0 : State Unit} (hv : HU U σ0) (t : ObjRef) (c : CapRef) (cp : ObjRef) (rp : Bool) :
    OkV σ0 (fun r : Cap × CslotPtr => UtIn U r.1) (capFaultOnFailure (Z := Unit) cp rp (lookupCapAndSlot t c)) := by
  intro s hs a s' h
  have e : hV s' = hV s :=
    hv_capFaultOnFailure (P := fun x => hV x = hV s) cp rp _ (hv_lookupCapAndSlot t c) s rfl _ h
  have hc := okdAt_capFault cp rp (okCap_lookupCapAndSlot t c s) a s' h
  have e' := e.trans hs
  exact ⟨e', utIn_of_slot (hu_of_hV e' hv) hc⟩

theorem hu_okv_lookupExtraCaps {σ0 : State Unit} (hv : HU U σ0) (t : ObjRef) (b : Option Data) (mi : MessageInfo) :
    OkV σ0 (fun caps : List (Cap × CslotPtr) => ∀ c ∈ caps, UtIn U c.1) (lookupExtraCaps (Z := Unit) t b mi) := by
  unfold lookupExtraCaps
  exact okv_bind (okv_frame fun v => ike_liftE (P := fun s => hV s = v) (hv_getExtraCptrs _ _)) fun cptrs _ =>
    okv_mapME (fun _ => hu_okv_lookupCap hv _ _ _ _) cptrs

theorem utIn_deriveCap {sl : CslotPtr} {c c' : Cap} {σ s : State Unit} (hc : UtIn U c)
    (h : ((.ok c', s) : Except SyscallError Cap × State Unit) ∈ ((deriveCap (Z := Unit) sl c).run σ).1) :
    UtIn U c' := by
  have key : OkV σ (fun c' => UtIn U c') (deriveCap (Z := Unit) sl c) := by
    cases c with
    | archObjectCap a =>
      simp only [deriveCap]; unfold archDeriveCap
      split <;> first
        | exact okv_throw _
        | exact okv_returnOk hc
        | exact okv_returnOk (utIn_noUt (fun _ _ _ h => by cases h) _)
        | exact okv_returnOk (utIn_noUt (fun _ _ _ h => by simp_all) _)
    | untypedCap d b n f =>
      simp only [deriveCap]
      exact okv_bind (okv_frame fun v => hv_ensureNoChildren (P := fun s => hV s = v) _) fun _ _ => okv_returnOk hc
    | zombie => simp only [deriveCap]; exact okv_returnOk (utIn_noUt (fun _ _ _ h => by cases h) _)
    | irqControlCap => simp only [deriveCap]; exact okv_returnOk (utIn_noUt (fun _ _ _ h => by cases h) _)
    | _ => simp only [deriveCap]; exact okv_returnOk hc
  exact (key σ rfl c' s h).2

/-! ## IPC cap transfer -/

theorem hu_transferCapsLoop (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (caps : List (Cap × CslotPtr)) (sl : List CslotPtr) (mi : MessageInfo),
      (∀ c ∈ caps, UtIn U c.1) → IKH (HU U) (transferCapsLoop (Z := Unit) ep rb n caps sl mi)
  | n, [], sl, mi, _ => by unfold transferCapsLoop; exact ik_pure _
  | n, (c, s) :: cs, sl, mi, hR => by
    have ih := fun sl' mi' hR' => hu_transferCapsLoop ep rb (n + 1) cs sl' mi' hR'
    have hR1 : ∀ c' ∈ cs, UtIn U c'.1 := fun c' hc' => hR c' (List.mem_cons_of_mem _ hc')
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
          have hs1 : HU U s1 := hv_deriveCap (P := HU U) _ _ σ h _ hz
          have hca : UtIn U c' := utIn_deriveCap (hR (c, s) (List.mem_cons_self ..)) hz
          exact (show IKHE (HU U) _ from by
            refine ike_bind (ike_whenE _ (ike_throw _)) fun _ =>
              ike_bind (ike_liftE (hu_capInsert _ _ _ hca)) fun _ =>
              ike_liftE (ih _ _ hR1)) s1 hs1 x hx
        · exact hv_deriveCap (P := HU U) _ _ σ h _ hz
      · exact ike_returnOk _

theorem hu_transferCaps (info : MessageInfo) (caps : List (Cap × CslotPtr)) (ep : Option ObjRef) (r : ObjRef)
    (rb : Option ObjRef) (hR : ∀ c ∈ caps, UtIn U c.1) :
    IKH (HU U) (transferCaps (Z := Unit) info caps ep r rb) := by
  unfold transferCaps
  refine ik_bind (hv_getReceiveSlots _ _) fun _ => ik_pure_bind ?_
  split
  · exact ik_pure _
  · exact hu_transferCapsLoop _ _ _ _ _ _ hR

theorem hu_doNormalTransfer (sender : ObjRef) (sbuf ep : Option ObjRef) (badge : Data) (grant : Bool)
    (receiver : ObjRef) (rbuf : Option ObjRef) :
    IKH (HU U) (doNormalTransfer (Z := Unit) sender sbuf ep badge grant receiver rbuf) := by
  unfold doNormalTransfer
  refine ik_bind (hv_getMessageInfo _) fun mi => ?_
  dsimp only
  have carry : ∀ {β : Type} {m : NonDet (State Unit) (List (Cap × CslotPtr))} {k : List (Cap × CslotPtr) → NonDet (State Unit) β},
      (∀ σ, HU U σ → ∀ y ∈ (m σ).1, HU U y.2 ∧ ∀ c ∈ y.1, UtIn U c.1) →
      (∀ caps, (∀ c ∈ caps, UtIn U c.1) → IKH (HU U) (k caps)) → IKH (HU U) (m >>= k) := by
    intro β m k hm hk σ h x ⟨y, hy, hx⟩
    exact hk y.1 (hm σ h y hy).2 y.2 (hm σ h y hy).1 x hx
  split
  all_goals refine carry ?_ (fun caps hc => ?_)
  · intro σ h y hy
    unfold NonDetE.catch at hy
    obtain ⟨z, hz, hy⟩ := hy
    obtain ⟨r, s⟩ := z
    have hs : HU U s := hv_lookupExtraCaps (P := HU U) _ _ _ σ h _ hz
    cases r with
    | ok a =>
      obtain rfl := Set.mem_singleton_iff.1 hy
      exact ⟨hs, (hu_okv_lookupExtraCaps h _ _ _ σ rfl a s hz).2⟩
    | error e =>
      obtain rfl := Set.mem_singleton_iff.1 hy
      exact ⟨hs, fun c hc => by cases hc⟩
  · exact ik_bind (hv_copyMrs _ _ _ _ _) fun _ => ik_bind (hu_transferCaps _ _ _ _ _ hc) fun _ =>
      ik_bind (hv_setMessageInfo _ _) fun _ => hv_asUser _ _
  · intro σ h y hy
    obtain rfl := Set.mem_singleton_iff.1 hy
    exact ⟨h, fun c hc => by cases hc⟩
  · exact ik_bind (hv_copyMrs _ _ _ _ _) fun _ => ik_bind (hu_transferCaps _ _ _ _ _ hc) fun _ =>
      ik_bind (hv_setMessageInfo _ _) fun _ => hv_asUser _ _

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hu_doNormalTransfer _ _ _ _ _ _ _)

/-! ## TCB installs, ASID control -/

theorem hu_checkCapAt_ins (nc : Cap) (src : CslotPtr) (t : ObjRef) (sl dst : CslotPtr) :
    IKH (HU U) (checkCapAt (Z := Unit) nc src (checkCapAt (.threadCap t) sl (capInsert nc src dst))) := by
  unfold checkCapAt
  refine ik_getCap_bind fun c' σ hc' => ?_
  unfold NonDet.when
  split
  · rename_i hso
    intro h
    have hca : UtIn U nc := fun b n f e => by
      subst e
      exact absurd hso (by simp [sameObjectAs])
    exact (ik_bind (hv_getCap _) fun _ => ik_ite _ (hu_capInsert _ _ _ hca) (ik_pure _)) σ h
  · exact ikp_of_ik (ik_pure _) σ

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hu_checkCapAt_ins _ _ _ _ _)

theorem hu_performAsidControlInvocation (iv : AsidControlInvocation) :
    IKH (HU U) (performAsidControlInvocation (Z := Unit) iv) := by
  cases iv with
  | makePool frame slot parent base =>
    simp only [performAsidControlInvocation]
    refine ik_bind (hu_deleteObjects _ _) fun _ => ik_getCap_bind fun pcap σ hp => ?_
    intro h
    refine ikp_bind (hu_setCap_p _ _ σ fun h' => utIn_maxFree (utIn_of_slot h' hp)) (fun _ => ?_) h
    hv_auto

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hu_performAsidControlInvocation _)

end

end Fl4Proofs.P3.SInvUZ
