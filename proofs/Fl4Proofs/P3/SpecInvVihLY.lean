/-
P3 (line irqfix, gen 3): vih3's cap writers whose caps come from slots (SpecInvValidIrqHandlersY) for l4v's
`valid_irq_handlers` (`VIL`): looked-up / derived caps are `CAL` (`okvl_*`, vih3's `OkV` reused), IPC cap
transfer, the IRQ control issue (`set_irq_state IRQSignal irq` then `cap_insert (IRQHandlerCap irq)`: the line is
in `IRQSignal` when the cap is written), the TCB installs' `check_cap_at`, the page maps' dead handler branch, the
ASID pool creation, the CNode and IRQ handler performs. No premise; no sorry.
-/
import Fl4Proofs.P3.SpecInvVihLX
import Fl4Proofs.P3.SpecInvValidIrqHandlersY
open Classical

namespace Fl4Proofs.P3.SInvVL
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvDom Fl4Proofs.P3.SInvV

noncomputable section

set_option maxHeartbeats 1000000

theorem okvl_lookupCap {σ0 : State Unit} (hv : ValidIrqHandlersL σ0) (t : ObjRef) (c : CapRef) (cp : ObjRef) (rp : Bool) :
    OkV σ0 (fun r : Cap × CslotPtr => CAL r.1 σ0.interruptStates)
      (capFaultOnFailure (Z := Unit) cp rp (lookupCapAndSlot t c)) := by
  intro s hs a s' h
  have e : hV s' = hV s :=
    hv_capFaultOnFailure (P := fun x => hV x = hV s) cp rp _ (hv_lookupCapAndSlot t c) s rfl _ h
  have hc := okdAt_capFault cp rp (okCap_lookupCapAndSlot t c s) a s' h
  have e' := e.trans hs
  refine ⟨e', ?_⟩
  have := cal_of_slot (vihl_of_hV e' hv) hc
  rw [hV_is e'] at this; exact this

theorem okvl_lookupExtraCaps {σ0 : State Unit} (hv : ValidIrqHandlersL σ0) (t : ObjRef) (b : Option Data)
    (mi : MessageInfo) :
    OkV σ0 (fun caps : List (Cap × CslotPtr) => ∀ c ∈ caps, CAL c.1 σ0.interruptStates)
      (lookupExtraCaps (Z := Unit) t b mi) := by
  unfold lookupExtraCaps
  exact okv_bind (okv_frame fun v => ike_liftE (P := fun s => hV s = v) (hv_getExtraCptrs _ _)) fun cptrs _ =>
    okv_mapME (fun _ => okvl_lookupCap hv _ _ _ _) cptrs

theorem okvl_deriveCap {σ0 : State Unit} (sl : CslotPtr) (c : Cap) (hc : CAL c σ0.interruptStates) :
    OkV σ0 (fun c' => CAL c' σ0.interruptStates) (deriveCap (Z := Unit) sl c) := by
  cases c with
  | archObjectCap a =>
    simp only [deriveCap]; unfold archDeriveCap
    split <;> first | exact okv_throw _ | exact okv_returnOk (cal_noH (fun _ h => by cases h) _)
  | untypedCap d b n f =>
    simp only [deriveCap]
    exact okv_bind (okv_frame fun v => hv_ensureNoChildren (P := fun s => hV s = v) _) fun _ _ => okv_returnOk hc
  | zombie => simp only [deriveCap]; exact okv_returnOk (cal_noH (fun _ h => by cases h) _)
  | irqControlCap => simp only [deriveCap]; exact okv_returnOk (cal_noH (fun _ h => by cases h) _)
  | _ => simp only [deriveCap]; exact okv_returnOk hc

/-! ## IPC cap transfer -/

theorem vhl_transferCapsLoop (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (caps : List (Cap × CslotPtr)) (sl : List CslotPtr) (mi : MessageInfo)
      (R : (Irq → IrqState) → Prop), (∀ is, R is → ∀ c ∈ caps, CAL c.1 is) →
      IKH (VHL R) (transferCapsLoop (Z := Unit) ep rb n caps sl mi)
  | n, [], sl, mi, R, _ => by unfold transferCapsLoop; exact ik_pure _
  | n, (c, s) :: cs, sl, mi, R, hR => by
    have ih := fun sl' mi' R' hR' => vhl_transferCapsLoop ep rb (n + 1) cs sl' mi' R' hR'
    have hR1 : ∀ is, R is → ∀ c' ∈ cs, CAL c'.1 is := fun is h c' hc' => hR is h c' (List.mem_cons_of_mem _ hc')
    unfold transferCapsLoop constOnFailure
    refine ik_catch ?_ (fun _ => ik_pure' _)
    refine ike_returnOk_bind ?_
    split
    · exact ike_bind (ike_liftE (hv_setExtraBadge _ _ _)) fun _ => ike_liftE (ih _ _ R hR1)
    · split
      · intro σ h x hx
        obtain ⟨z, hz, ⟨c', hc', hx⟩ | ⟨e, he, rfl⟩⟩ := mem_bindE_inv' hx
        · obtain ⟨r, s1⟩ := z
          simp only at hc'; subst hc'
          have hs1 : VHL R s1 := hv_deriveCap (P := VHL R) _ _ σ h _ hz
          have hca := (okvl_deriveCap (σ0 := σ) s c (hR _ h.2.2 (c, s) (List.mem_cons_self ..)) σ rfl c' s1 hz)
          have hca' : CAL c' s1.interruptStates := by rw [hV_is hca.1]; exact hca.2
          have := (show IKHE (VHL fun is => R is ∧ CAL c' is) _ from by
            refine ike_bind (ike_whenE _ (ike_throw _)) fun _ =>
              ike_bind (ike_liftE (vhl_capInsert _ _ _ fun _ h => h.2)) fun _ =>
              ike_liftE (ih _ _ _ fun is h => hR1 is h.1)) s1 ⟨hs1.1, hs1.2.1, hs1.2.2, hca'⟩ x hx
          exact ⟨this.1, this.2.1, this.2.2.1⟩
        · exact hv_deriveCap (P := VHL R) _ _ σ h _ hz
      · exact ike_returnOk _

theorem vhl_transferCaps (info : MessageInfo) (caps : List (Cap × CslotPtr)) (ep : Option ObjRef) (r : ObjRef)
    (rb : Option ObjRef) {R : (Irq → IrqState) → Prop} (hR : ∀ is, R is → ∀ c ∈ caps, CAL c.1 is) :
    IKH (VHL R) (transferCaps (Z := Unit) info caps ep r rb) := by
  unfold transferCaps
  refine ik_bind (hv_getReceiveSlots _ _) fun _ => ik_pure_bind ?_
  split
  · exact ik_pure _
  · exact vhl_transferCapsLoop _ _ _ _ _ _ R hR

/-- A bind whose first step yields a carried IRQ-state fact for the rest. -/
theorem ik_bind_vhl_carry {α β : Type} {m : NonDet (State Unit) α} {k : α → NonDet (State Unit) β}
    {Q : α → (Irq → IrqState) → Prop} (hm : ∀ σ, VIL σ → ∀ y ∈ (m σ).1, VIL y.2 ∧ Q y.1 y.2.interruptStates)
    (hk : ∀ a, IKH (VHL (Q a)) (k a)) : IKH VIL (m >>= k) := by
  intro σ h x ⟨y, hy, hx⟩
  obtain ⟨h1, hq⟩ := hm σ h y hy
  have := hk y.1 y.2 ⟨h1.1, h1.2.1, hq⟩ x hx
  exact ⟨this.1, this.2.1, trivial⟩

theorem vil_doNormalTransfer (sender : ObjRef) (sbuf ep : Option ObjRef) (badge : Data) (grant : Bool)
    (receiver : ObjRef) (rbuf : Option ObjRef) :
    IKH VIL (doNormalTransfer (Z := Unit) sender sbuf ep badge grant receiver rbuf) := by
  unfold doNormalTransfer
  refine ik_bind (hv_getMessageInfo _) fun mi => ?_
  dsimp only
  split
  all_goals refine ik_bind_vhl_carry (Q := fun (caps : List (Cap × CslotPtr)) is => ∀ c ∈ caps, CAL c.1 is) ?_ (fun caps => ?_)
  · intro σ h y hy
    unfold NonDetE.catch at hy
    obtain ⟨z, hz, hy⟩ := hy
    obtain ⟨r, s⟩ := z
    have hs : VIL s := hv_lookupExtraCaps (P := VIL) _ _ _ σ h _ hz
    cases r with
    | ok a =>
      obtain rfl := Set.mem_singleton_iff.1 hy
      obtain ⟨e, hca⟩ := okvl_lookupExtraCaps h.2.1 _ _ _ σ rfl a s hz
      exact ⟨hs, fun c hc => by rw [hV_is e]; exact hca c hc⟩
    | error e =>
      obtain rfl := Set.mem_singleton_iff.1 hy
      exact ⟨hs, fun c hc => by cases hc⟩
  · refine ik_bind (hv_copyMrs _ _ _ _ _) fun _ => ik_bind (vhl_transferCaps _ _ _ _ _ fun _ h => h) fun _ =>
      ik_bind (hv_setMessageInfo _ _) fun _ => hv_asUser _ _
  · intro σ h y hy
    obtain rfl := Set.mem_singleton_iff.1 hy
    exact ⟨h, fun c hc => by cases hc⟩
  · refine ik_bind (hv_copyMrs _ _ _ _ _) fun _ => ik_bind (vhl_transferCaps _ _ _ _ _ fun _ h => h) fun _ =>
      ik_bind (hv_setMessageInfo _ _) fun _ => hv_asUser _ _

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vil_doNormalTransfer _ _ _ _ _ _ _)

/-! ## IRQ control issue, TCB installs, page maps -/

theorem vil_irqIssue (irq : Irq) (src dst : CslotPtr) :
    IKH VIL (setIrqState (Z := Unit) .irqSignal irq >>= fun _ => capInsert (Z := Unit) (.irqHandlerCap irq) src dst) := by
  intro σ h x ⟨y, hy, hx⟩
  obtain ⟨-, hi⟩ := setIrqState_out hy
  have h1 : VIL y.2 := vhl_setIrqState_signal rml_true rfl irq σ h y hy
  have h2 := vhl_capInsert (R := fun is => is irq = .irqSignal) (.irqHandlerCap irq) src dst
    (fun is h irq' e => by cases e; exact h) y.2 ⟨h1.1, h1.2.1, by simp [hi]⟩ x hx
  exact ⟨h2.1, h2.2.1, trivial⟩

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vil_irqIssue _ _ _)

theorem vil_checkCapAt_ins (nc : Cap) (src : CslotPtr) (t : ObjRef) (sl dst : CslotPtr) :
    IKH VIL (checkCapAt (Z := Unit) nc src (checkCapAt (.threadCap t) sl (capInsert nc src dst))) := by
  unfold checkCapAt
  refine ik_getCap_bind fun c' σ hc' => ?_
  unfold NonDet.when
  split
  · rename_i hso
    intro h
    have hca : CAL nc σ.interruptStates := fun irq e => by
      subst e
      exact cal_of_slot h.2.1 ((sameObjectAs_handler hso) ▸ hc') irq rfl
    exact ikp_vhl_and (Q := CAL nc) (ik_bind (hv_getCap _) fun _ =>
      ik_ite _ (vhl_capInsert _ _ _ fun _ h => h.2) (ik_pure _)) hca h
  · exact ikp_of_ik (ik_pure _) σ

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vil_checkCapAt_ins _ _ _ _ _)

theorem vil_setCap_bind_dead {β : Type} (cap : Cap) (sl : CslotPtr) {k : Unit → NonDet (State Unit) β}
    (hk : ∀ a, IKH VIL (k a)) (hd : ∀ irq, cap = .irqHandlerCap irq → ∀ a σ x, x ∈ (k a σ).1 → False) :
    IKH VIL (setCap (Z := Unit) cap sl >>= k) := by
  intro σ h x ⟨y, hy, hx⟩
  by_cases hc : ∃ irq, cap = .irqHandlerCap irq
  · obtain ⟨irq, e⟩ := hc; exact (hd irq e _ _ x hx).elim
  · exact hk _ _ (vhl_setCap cap sl (fun _ _ => cal_noH (fun irq e => hc ⟨irq, e⟩) _) σ h y hy) x hx

theorem vil_performPageInvocation (iv : PageInvocation) : IKH VIL (performPageInvocation (Z := Unit) iv) := by
  cases iv with
  | pageMap cap sl ent vs =>
    simp only [performPageInvocation]
    refine vil_setCap_bind_dead _ _ (fun _ => by hv_auto) ?_
    dead_k2
  | _ => simp only [performPageInvocation]; hv_auto

theorem vil_performPageTableInvocation (iv : PageTableInvocation) :
    IKH VIL (performPageTableInvocation (Z := Unit) iv) := by
  cases iv with
  | pageTableMap cap sl pde pd vs =>
    simp only [performPageTableInvocation]
    exact vil_setCap_bind_dead _ _ (fun _ => by hv_auto) (by dead_k)
  | _ => simp only [performPageTableInvocation]; split <;> (try (exfalso; simp_all; done)) <;> hv_auto

theorem vil_performPageDirectoryInvocation (iv : PageDirectoryInvocation) :
    IKH VIL (performPageDirectoryInvocation (Z := Unit) iv) := by
  cases iv with
  | pageDirectoryMap cap sl pde pd vs =>
    simp only [performPageDirectoryInvocation]
    exact vil_setCap_bind_dead _ _ (fun _ => by hv_auto) (by dead_k)
  | _ => simp only [performPageDirectoryInvocation]; split <;> (try (exfalso; simp_all; done)) <;> hv_auto

theorem vil_performPdptInvocation (iv : PdptInvocation) : IKH VIL (performPdptInvocation (Z := Unit) iv) := by
  cases iv with
  | pdptMap cap sl pde pd vs =>
    simp only [performPdptInvocation]
    exact vil_setCap_bind_dead _ _ (fun _ => by hv_auto) (by dead_k)
  | _ => simp only [performPdptInvocation]; split <;> (try (exfalso; simp_all; done)) <;> hv_auto

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vil_performPageInvocation _)
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vil_performPageTableInvocation _)
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vil_performPageDirectoryInvocation _)
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vil_performPdptInvocation _)

theorem cal_freeIndexUpdate {c : Cap} {is : Irq → IrqState} (h : CAL c is) (g : Nat → Nat) :
    CAL (freeIndexUpdate g c) is := by
  intro irq e; apply h irq; cases c <;> simp_all [freeIndexUpdate]

/-- The ASID pool creation: the parent untyped cap re-written full (read from its slot). -/
theorem vil_performAsidControlInvocation (iv : AsidControlInvocation) :
    IKH VIL (performAsidControlInvocation (Z := Unit) iv) := by
  cases iv with
  | makePool frame slot parent base =>
    simp only [performAsidControlInvocation]
    refine ik_bind (vhl_deleteObjects _ _) fun _ => ik_getCap_bind fun pcap σ hp => ?_
    intro h
    refine ikp_bind (vhl_setCap_p _ _ σ fun h' => cal_freeIndexUpdate (cal_of_slot h'.2.1 hp) _) (fun _ => ?_) h
    hv_auto

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vil_performAsidControlInvocation _)

/-! ## CNode and IRQ handler performs -/

/-- The caps a CNode invocation writes are `CAL`. -/
def CnCAL (i : CnodeInvocation) (is : Irq → IrqState) : Prop :=
  match i with
  | .insertCall c _ _ => CAL c is
  | .moveCall c _ _ => CAL c is
  | .rotateCall c1 c2 _ _ _ => CAL c1 is ∧ CAL c2 is
  | _ => True

theorem vhl_invokeCnode (i : CnodeInvocation) : IKHE (ε := Unit) (VHL (CnCAL i)) (invokeCnode (Z := Unit) i) := by
  cases i with
  | insertCall c s d => exact ike_liftE (vhl_capInsert c s d fun _ h => h)
  | moveCall c s d => exact ike_liftE (vhl_capMove c s d fun _ h => h)
  | rotateCall c1 c2 s1 s2 s3 =>
    refine ike_liftE ?_
    split
    · exact vhl_capSwap _ _ _ _ (fun _ h => h.1) (fun _ h => h.2)
    · exact ik_bind (vhl_capMove _ _ _ fun _ h => h.2) fun _ => vhl_capMove _ _ _ fun _ h => h.1
  | revokeCall s => exact vil_capRevoke s
  | deleteCall s => exact vil_capDelete s
  | cancelBadgedSendsCall c => simp only [invokeCnode]; split <;> (try (exfalso; simp_all; done)) <;> hv_auto

/-- The facts an IRQ handler invocation needs at its perform. -/
def IhCAL (i : IrqHandlerInvocation) (σ : State Unit) : Prop :=
  match i with
  | .aCKIrq irq => HIrq σ irq
  | .setIRQHandler _ c _ => CAL c σ.interruptStates
  | .clearIRQHandler _ => True

theorem vil_invokeIrqHandler (i : IrqHandlerInvocation) (σ : State Unit) (h : VIL σ) (hc : IhCAL i σ) :
    ∀ x ∈ (invokeIrqHandler (Z := Unit) i σ).1, VIL x.2 := by
  cases i with
  | aCKIrq irq =>
    intro x hx
    exact ⟨(vimhl_invokeIrqHandler_ack h.1 h.2.1 hc x hx).1, (vimhl_invokeIrqHandler_ack h.1 h.2.1 hc x hx).2, trivial⟩
  | setIRQHandler irq c sl =>
    have hU : WLH (fun s : State Unit => CAL c s.interruptStates) :=
      wlh_of_hV fun _ _ e h => by rw [hV_is e]; exact h
    have hd : ∀ s', IKH (VHL (CAL c)) (capDeleteOne (Z := Unit) s') := by
      intro s' σ h x hx
      have r := vil_capDeleteOne_u (U := fun s => CAL c s.interruptStates)
        (fun sl σ x h hx => by obtain ⟨o, r⟩ := sl; rw [(vih_setCap_out hx).1]; exact h) s' σ
        ⟨⟨h.1, h.2.1, trivial⟩, h.2.2⟩ x hx
      exact ⟨r.1.1, r.1.2.1, r.2⟩
    have key : IKH (VHL (CAL c)) (invokeIrqHandler (Z := Unit) (.setIRQHandler irq c sl)) := by
      simp only [invokeIrqHandler]
      exact ik_bind (hv_getIrqSlot _) fun s => ik_bind (hd s) fun _ => vhl_capInsert c sl s fun _ h => h
    intro x hx
    have := key σ ⟨h.1, h.2.1, hc⟩ x hx
    exact ⟨this.1, this.2.1, trivial⟩
  | clearIRQHandler irq =>
    simp only [invokeIrqHandler]
    exact ik_bind (hv_getIrqSlot _) (fun s => vil_capDeleteOne s) σ h

end

end Fl4Proofs.P3.SInvVL
