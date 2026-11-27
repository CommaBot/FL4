/-
P3 (line p3J, gen 16): **the cap-kind invariant `CKI`** (spec side only; outside the `JAtZ` cone; the IO-port
line's cap half `HI S` (SpecInvIoPortsW/Y/G) with a cap-kind predicate for `IoIn S`), part 1: the definition
and the cap writers.

* `KW c` (an *allowed* cap kind): `c` is no untyped cap, no SchedControl cap, no IRQ-control cap and no arch
  cap (frames, page tables, ASID / IO-port caps, VT-x caps). `CKI σ`: every slot's cap (`capOpt`, as `get_cap`
  reads it) is `KW`. It reads only the caps (`wlh_of_hV`), so the generated frames
  SpecInvValidIrqHandlersF1..F4 keep it across every spec function that writes no cap.
* Why these kinds: every cap kind outside `KW` is created only by an untyped retype (`create_cap`), the
  IRQ / ASID / IO-port control issues, or a perform on a cap of that kind (page maps, ASID pool assign, FL4's
  DeriveSubframe / frame batch); `derive_cap`, `mask_cap`, `update_cap_data` keep a cap's kind or give
  `NullCap`; `finalise_cap`'s remainder is `NullCap` or a zombie. So from a `CKI` state no entry reaches a
  creator of a non-`KW` cap (the decode carry, P3JCkS), and the cap writers it does reach write `KW` caps.
* Leaves (`hv_leaf` rules, so vih2's `hv_auto` proves `IKH CKI` of the callers): `set_cap` of a `KW` cap,
  `set_untyped_cap_as_full` of a `KW` source cap (it then writes nothing), `cap_insert` (its source cap is read
  from a slot), `cap_move` / `cap_swap` of `KW` caps, `cap_swap_for_delete`, `set_irq_state`, machine ops,
  `cap_delete_one`, `deleting_irq_handler`, `finalise_cap`; looked-up / derived caps (`OkV`), IPC cap transfer,
  the TCB installs' `check_cap_at` (an inserted cap `same_object_as` a `KW` slot cap is `KW`), and the
  generated callers (IPC, faults, timeouts, budgets, the preemption path), as SpecInvIoPortsG without the
  untyped / IRQ-control / ASID-pool / DeriveSubframe performs (unreachable from `CKI`, P3JCkS).

Named premises: none. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.SpecInvIoPortsS
open Classical

namespace Fl4Proofs.P3.SInvCk
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvV Fl4Proofs.P3.SInvDom Fl4Proofs.P3.SInvIo

noncomputable section

set_option maxHeartbeats 4000000

/-! ## The invariant -/

/-- **An allowed cap kind**: no untyped, SchedControl, IRQ-control or arch cap. -/
def KW : Cap → Prop
  | .untypedCap _ _ _ _ => False
  | .schedControlCap => False
  | .irqControlCap => False
  | .archObjectCap _ => False
  | _ => True

/-- **The cap-kind invariant**: every slot's cap is `KW`. -/
def CKI (σ : State Unit) : Prop := ∀ p cref c, capOpt (σ.kheap p) cref = some c → KW c

variable {σ σ' : State Unit}

theorem cki_of_hV (e : hV σ' = hV σ) (h : CKI σ) : CKI σ' :=
  fun p cref c hc => h p cref c (by rw [← hV_cap e]; exact hc)

instance : WLH CKI := wlh_of_hV fun _ _ e h => cki_of_hV e h

theorem kw_of_slot (h : CKI σ) {p : ObjRef} {r : CnodeIndex} {c : Cap} (hc : capOpt (σ.kheap p) r = some c) :
    KW c := h p r c hc

theorem kw_maskCap {c : Cap} (h : KW c) (r : CapRights) : KW (maskCap r c) := by
  cases c <;> simp_all [KW, maskCap, capRightsUpdate]

theorem kw_updateCapData {c : Cap} (h : KW c) (p : Bool) (w : Data) : KW (updateCapData p w c) := by
  unfold updateCapData
  split_ifs <;> first
    | trivial
    | (cases c <;> simp_all [KW, badgeUpdate, isEpCap, isNtfnCap]; done)
    | (cases c <;> simp_all [KW, isArchCap]; done)
    | (dsimp only; split_ifs <;> trivial)
    | exact h

/-- Side conditions `KW c`. -/
macro "ck_side" : tactic => `(tactic| first
  | assumption
  | trivial
  | (simp [KW]; done)
  | (refine kw_updateCapData (kw_maskCap ?_ _) _ _; assumption)
  | (refine kw_maskCap ?_ _; assumption)
  | (refine kw_updateCapData ?_ _ _; assumption))

/-! ## `set_cap` and the cap writers -/

theorem ck_setCap_p (c : Cap) (sl : CslotPtr) (σ : State Unit) (hc : CKI σ → KW c) :
    IKp CKI σ (setCap (Z := Unit) c sl) := by
  intro h x hx
  obtain ⟨o, r⟩ := sl
  intro p cref a hp
  rcases (vih_setCap_out hx).2 p cref _ hp with ⟨-, -, e⟩ | ⟨-, h0⟩
  · rw [e]; exact hc h
  · exact h p cref a h0

theorem ck_setCap (c : Cap) (sl : CslotPtr) (hc : KW c) : IKH CKI (setCap (Z := Unit) c sl) :=
  fun σ => ck_setCap_p c sl σ fun _ => hc

macro_rules | `(tactic| hv_leaf) => `(tactic| ((with_reducible refine ck_setCap _ _ ?_); ck_side))

/-- `set_untyped_cap_as_full` of a `KW` source cap writes nothing (the source is no untyped cap). -/
theorem ck_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : CslotPtr) (hs : KW srcCap) :
    IKH CKI (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull
  split
  · rename_i h
    exfalso
    have h1 := h.1
    cases srcCap <;> simp_all [KW, isUntypedCap]
  · exact ik_pure _

macro_rules | `(tactic| hv_leaf) => `(tactic| ((with_reducible refine ck_setUntypedCapAsFull _ _ _ ?_); ck_side))

theorem ck_capInsert (c : Cap) (src dst : CslotPtr) (hc : KW c) :
    IKH CKI (capInsert (Z := Unit) c src dst) := by
  unfold capInsert
  refine ik_getCap_bind fun sc σ hsc hσ => ?_
  have hk : KW sc := kw_of_slot hσ hsc
  exact (by hv_auto : IKH CKI _) σ hσ

theorem ck_capMove (c : Cap) (src dst : CslotPtr) (hc : KW c) :
    IKH CKI (capMove (Z := Unit) c src dst) := by
  unfold capMove; hv_auto

theorem ck_capSwap (c1 : Cap) (s1 : CslotPtr) (c2 : Cap) (s2 : CslotPtr) (hc1 : KW c1) (hc2 : KW c2) :
    IKH CKI (capSwap (Z := Unit) c1 s1 c2 s2) := by
  unfold capSwap; hv_auto

theorem ck_capSwapForDelete (s1 s2 : CslotPtr) : IKH CKI (capSwapForDelete (Z := Unit) s1 s2) := by
  unfold capSwapForDelete
  refine ik_when _ (ik_getCap_bind fun c1 σ h1 => ikp_getCap_bind fun c2 h2 hσ => ?_)
  exact ck_capSwap c1 s1 c2 s2 (kw_of_slot hσ h1) (kw_of_slot hσ h2) σ hσ

macro_rules | `(tactic| hv_leaf) => `(tactic| ((with_reducible refine ck_capInsert _ _ _ ?_); ck_side))
macro_rules | `(tactic| hv_leaf) => `(tactic| ((with_reducible refine ck_capMove _ _ _ ?_); ck_side))
macro_rules | `(tactic| hv_leaf) => `(tactic| ((with_reducible refine ck_capSwap _ _ _ _ ?_ ?_) <;> ck_side))
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact ck_capSwapForDelete _ _)

/-! ## Writers of no cap outside the frames -/

theorem ck_setIrqState (st : IrqState) (i : Irq) : IKH CKI (setIrqState (Z := Unit) st i) := by
  intro σ h x hx p cref c hc
  obtain ⟨hk, -⟩ := setIrqState_out hx
  exact h p cref c (by rw [← hk]; exact hc)

theorem ck_dmo {α : Type} (mop : NonDet MachineState α) : IKH CKI (doMachineOp (Z := Unit) mop) :=
  ik_doMachineOp (fun _ _ h => h) mop

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact ck_setIrqState _ _)
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact ck_dmo _)

theorem ck_capDeleteOne (sl : CslotPtr) : IKH CKI (capDeleteOne (Z := Unit) sl) := by
  unfold capDeleteOne emptySlot
  simp only [postCapDeletion]
  hv_auto

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact ck_capDeleteOne _)

theorem ck_deletingIrqHandler (irq : Irq) : IKH CKI (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler; hv_auto

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact ck_deletingIrqHandler _)

theorem ck_finaliseCap (c : Cap) (fin : Bool) : IKH CKI (finaliseCap (Z := Unit) c fin) := by
  cases c <;> unfold finaliseCap <;> hv_auto

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact ck_finaliseCap _ _)

/-! ## Looked-up and derived caps -/

theorem ck_okv_lookupCap {σ0 : State Unit} (hv : CKI σ0) (t : ObjRef) (c : CapRef) (cp : ObjRef) (rp : Bool) :
    OkV σ0 (fun r : Cap × CslotPtr => KW r.1) (capFaultOnFailure (Z := Unit) cp rp (lookupCapAndSlot t c)) := by
  intro s hs a s' h
  have e : hV s' = hV s :=
    hv_capFaultOnFailure (P := fun x => hV x = hV s) cp rp _ (hv_lookupCapAndSlot t c) s rfl _ h
  have hc := okdAt_capFault cp rp (okCap_lookupCapAndSlot t c s) a s' h
  have e' := e.trans hs
  exact ⟨e', kw_of_slot (cki_of_hV e' hv) hc⟩

theorem ck_okv_lookupExtraCaps {σ0 : State Unit} (hv : CKI σ0) (t : ObjRef) (b : Option Data) (mi : MessageInfo) :
    OkV σ0 (fun caps : List (Cap × CslotPtr) => ∀ c ∈ caps, KW c.1) (lookupExtraCaps (Z := Unit) t b mi) := by
  unfold lookupExtraCaps
  exact okv_bind (okv_frame fun v => ike_liftE (P := fun s => hV s = v) (hv_getExtraCptrs _ _)) fun cptrs _ =>
    okv_mapME (fun _ => ck_okv_lookupCap hv _ _ _ _) cptrs

/-- `derive_cap` of a `KW` cap returns the cap itself or `NullCap`. -/
theorem kw_deriveCap {sl : CslotPtr} {c c' : Cap} {σ s : State Unit} (hc : KW c)
    (h : ((.ok c', s) : Except SyscallError Cap × State Unit) ∈ ((deriveCap (Z := Unit) sl c).run σ).1) :
    KW c' := by
  have key : OkV σ (fun c' => KW c') (deriveCap (Z := Unit) sl c) := by
    cases c with
    | archObjectCap a => exact hc.elim
    | untypedCap d b n f => exact hc.elim
    | zombie => simp only [deriveCap]; exact okv_returnOk trivial
    | irqControlCap => exact hc.elim
    | _ => simp only [deriveCap]; exact okv_returnOk hc
  exact (key σ rfl c' s h).2

/-! ## IPC cap transfer -/

theorem ck_transferCapsLoop (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (caps : List (Cap × CslotPtr)) (sl : List CslotPtr) (mi : MessageInfo),
      (∀ c ∈ caps, KW c.1) → IKH CKI (transferCapsLoop (Z := Unit) ep rb n caps sl mi)
  | n, [], sl, mi, _ => by unfold transferCapsLoop; exact ik_pure _
  | n, (c, s) :: cs, sl, mi, hR => by
    have ih := fun sl' mi' hR' => ck_transferCapsLoop ep rb (n + 1) cs sl' mi' hR'
    have hR1 : ∀ c' ∈ cs, KW c'.1 := fun c' hc' => hR c' (List.mem_cons_of_mem _ hc')
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
          have hs1 : CKI s1 := hv_deriveCap (P := CKI) _ _ σ h _ hz
          have hca : KW c' := kw_deriveCap (hR (c, s) (List.mem_cons_self ..)) hz
          exact (show IKHE CKI _ from by
            refine ike_bind (ike_whenE _ (ike_throw _)) fun _ =>
              ike_bind (ike_liftE (ck_capInsert _ _ _ hca)) fun _ =>
              ike_liftE (ih _ _ hR1)) s1 hs1 x hx
        · exact hv_deriveCap (P := CKI) _ _ σ h _ hz
      · exact ike_returnOk _

theorem ck_transferCaps (info : MessageInfo) (caps : List (Cap × CslotPtr)) (ep : Option ObjRef) (r : ObjRef)
    (rb : Option ObjRef) (hR : ∀ c ∈ caps, KW c.1) :
    IKH CKI (transferCaps (Z := Unit) info caps ep r rb) := by
  unfold transferCaps
  refine ik_bind (hv_getReceiveSlots _ _) fun _ => ik_pure_bind ?_
  split
  · exact ik_pure _
  · exact ck_transferCapsLoop _ _ _ _ _ _ hR

theorem ck_doNormalTransfer (sender : ObjRef) (sbuf ep : Option ObjRef) (badge : Data) (grant : Bool)
    (receiver : ObjRef) (rbuf : Option ObjRef) :
    IKH CKI (doNormalTransfer (Z := Unit) sender sbuf ep badge grant receiver rbuf) := by
  unfold doNormalTransfer
  refine ik_bind (hv_getMessageInfo _) fun mi => ?_
  dsimp only
  have carry : ∀ {β : Type} {m : NonDet (State Unit) (List (Cap × CslotPtr))} {k : List (Cap × CslotPtr) → NonDet (State Unit) β},
      (∀ σ, CKI σ → ∀ y ∈ (m σ).1, CKI y.2 ∧ ∀ c ∈ y.1, KW c.1) →
      (∀ caps, (∀ c ∈ caps, KW c.1) → IKH CKI (k caps)) → IKH CKI (m >>= k) := by
    intro β m k hm hk σ h x ⟨y, hy, hx⟩
    exact hk y.1 (hm σ h y hy).2 y.2 (hm σ h y hy).1 x hx
  split
  all_goals refine carry ?_ (fun caps hc => ?_)
  · intro σ h y hy
    unfold NonDetE.catch at hy
    obtain ⟨z, hz, hy⟩ := hy
    obtain ⟨r, s⟩ := z
    have hs : CKI s := hv_lookupExtraCaps (P := CKI) _ _ _ σ h _ hz
    cases r with
    | ok a =>
      obtain rfl := Set.mem_singleton_iff.1 hy
      exact ⟨hs, (ck_okv_lookupExtraCaps h _ _ _ σ rfl a s hz).2⟩
    | error e =>
      obtain rfl := Set.mem_singleton_iff.1 hy
      exact ⟨hs, fun c hc => by cases hc⟩
  · exact ik_bind (hv_copyMrs _ _ _ _ _) fun _ => ik_bind (ck_transferCaps _ _ _ _ _ hc) fun _ =>
      ik_bind (hv_setMessageInfo _ _) fun _ => hv_asUser _ _
  · intro σ h y hy
    obtain rfl := Set.mem_singleton_iff.1 hy
    exact ⟨h, fun c hc => by cases hc⟩
  · exact ik_bind (hv_copyMrs _ _ _ _ _) fun _ => ik_bind (ck_transferCaps _ _ _ _ _ hc) fun _ =>
      ik_bind (hv_setMessageInfo _ _) fun _ => hv_asUser _ _

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact ck_doNormalTransfer _ _ _ _ _ _ _)

/-! ## TCB installs -/

/-- A cap `same_object_as` a `KW` cap is `KW`. -/
theorem kw_of_sameObjectAs {nc c : Cap} (h : sameObjectAs nc c) (hc : KW c) : KW nc := by
  cases nc <;> first
    | trivial
    | (exfalso; simp only [sameObjectAs] at h; done)
    | (exfalso; cases c <;> simp_all [sameObjectAs, sameRegionAs, KW]; done)

theorem ck_checkCapAt_ins (nc : Cap) (src : CslotPtr) (t : ObjRef) (sl dst : CslotPtr) :
    IKH CKI (checkCapAt (Z := Unit) nc src (checkCapAt (.threadCap t) sl (capInsert nc src dst))) := by
  unfold checkCapAt
  refine ik_getCap_bind fun c' σ hc' => ?_
  unfold NonDet.when
  split
  · rename_i hso
    intro h
    have hca : KW nc := kw_of_sameObjectAs hso (kw_of_slot h hc')
    exact (ik_bind (hv_getCap _) fun _ => ik_ite _ (ck_capInsert _ _ _ hca) (ik_pure _)) σ h
  · exact ikp_of_ik (ik_pure _) σ

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact ck_checkCapAt_ins _ _ _ _ _)

/-! ## The generated callers (SpecInvIoPortsG's list without the unreachable performs) -/

theorem ck_doIpcTransfer (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : IKH CKI (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact ck_doIpcTransfer _ _ _ _ _)

theorem ck_sendIpc (block call : Bool) (badge : Badge) (canGrant canGrantReply canDonate : Bool) (thread epptr : ObjRef) : IKH CKI (sendIpc (Z := Unit) block call badge canGrant canGrantReply canDonate thread epptr) := by
  unfold sendIpc; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact ck_sendIpc _ _ _ _ _ _ _ _)

theorem ck_sendFaultIpc (tptr : ObjRef) (handlerCap : Cap) (fault : Fault) (canDonate : Bool) : IKH CKI (sendFaultIpc (Z := Unit) tptr handlerCap fault canDonate) := by
  unfold sendFaultIpc; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact ck_sendFaultIpc _ _ _ _)

theorem ck_handleTimeout (tptr : ObjRef) (ex : Fault) : IKH CKI (handleTimeout (Z := Unit) tptr ex) := by
  unfold handleTimeout; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact ck_handleTimeout _ _)

theorem ck_endTimeslice (canTimeout : Bool) : IKH CKI (endTimeslice (Z := Unit) canTimeout) := by
  unfold endTimeslice; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact ck_endTimeslice _)

theorem ck_chargeBudget (consumed : Ticks) (canTimeout : Bool) : IKH CKI (chargeBudget (Z := Unit) consumed canTimeout) := by
  unfold chargeBudget; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact ck_chargeBudget _ _)

theorem ck_checkBudget  : IKH CKI (checkBudget (Z := Unit)) := by
  unfold checkBudget; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact ck_checkBudget)

theorem ck_checkBudgetRestart  : IKH CKI (checkBudgetRestart (Z := Unit)) := by
  unfold checkBudgetRestart; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact ck_checkBudgetRestart)

theorem ck_doReplyTransfer (sender reply : ObjRef) (grant : Bool) : IKH CKI (doReplyTransfer (Z := Unit) sender reply grant) := by
  unfold doReplyTransfer; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact ck_doReplyTransfer _ _ _)

theorem ck_handleFault (thread : ObjRef) (ex : Fault) : IKH CKI (handleFault (Z := Unit) thread ex) := by
  unfold handleFault; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact ck_handleFault _ _)

theorem ck_receiveIpc (thread : ObjRef) (cap : Cap) (isBlocking : Bool) (replyCap : Cap) :
    IKH CKI (receiveIpc (Z := Unit) thread cap isBlocking replyCap) := by
  unfold receiveIpc; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact ck_receiveIpc _ _ _ _)

theorem ck_handleRecv (isBlocking canReply : Bool) : IKH CKI (handleRecv (Z := Unit) isBlocking canReply) := by
  unfold handleRecv; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact ck_handleRecv _ _)

theorem ck_handleYield  : IKH CKI (handleYield (Z := Unit)) := by
  unfold handleYield; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact ck_handleYield)

theorem ck_preemptionPath  : IKH CKI (preemptionPath (Z := Unit)) := by
  unfold preemptionPath; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact ck_preemptionPath)

end

end Fl4Proofs.P3.SInvCk
