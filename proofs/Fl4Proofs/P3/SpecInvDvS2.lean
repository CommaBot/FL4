/-
P3 (issue #16, s26): **the perform / shell half of `ZD`** (l4v `valid_untyped`
for device untyped caps), SpecInvUtZS2 (g5h) with the device flag, `HUD U` and
the object half `OBK O` (spec side only; outside the `JAtZ` cone).

* `zd_split`: `ik_zd` / `ike_zd`, the cap half by `hv_auto`, the object half
  by `ob_auto`; `zd_pin`; `utInD_of_view`, `utInD_ci3`, `utInD_refEq` (ut7's
  CNode decode facts give `UtInD U` of the written caps).
* The performs: `zd_invokeCnode`, `zd_invokeIrqHandler`, `hd_invokeTcb`, the
  others by `zd_split`; `zd_fl4Perform` per invocation kind: the arch performs
  by SpecInvDvS's `zd_fl4Arch` (MakePool from the decode's `ArchOKN`, through
  `okv_fl4DecodeG`), the untyped perform by `PerfGapD` (proved in SpecInvDvP).
* `PerfGapD`, `IKD` (`ZD` from `P3 N ∧ NodeIs N ∧ ZD`) and its binds.
-/
import Fl4Proofs.P3.SpecInvDvS
open Classical

namespace Fl4Proofs.P3.SInvDV
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvV Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 1000000

/-- `ZD` of a function: the cap half by `hv_auto`, the memory half by `ob_auto`. -/
macro "zd_split" : tactic => `(tactic| first
  | ((with_reducible refine ike_zd (fun _ => ?_) (fun _ => ?_)); (focus (hv_auto; done)); (ob_auto; done))
  | ((with_reducible refine ik_zd (fun _ => ?_) (fun _ => ?_)); (focus (hv_auto; done)); (ob_auto; done)))

/-! ## Pinned form and the written caps -/

theorem zd_pin {α : Type} {m : NonDet (State Unit) α} {σ : State Unit} (hZ : ZD σ)
    (hH : ∀ U, HUD U σ → ∀ y ∈ (m σ).1, HUD U y.2) (hY : ∀ O, OBK O m) : ∀ y ∈ (m σ).1, ZD y.2 := by
  obtain ⟨U, O, hG, hU, hP⟩ := hZ
  intro y hy
  exact ⟨U, O, hG, hH U hU y hy, hY O σ hP y hy⟩

theorem utInD_of_view {U : UtSetD} {σ : State Unit} (h : HUD U σ) {sl : CslotPtr} {c : Cap}
    (hc : (uV σ).2.1 sl = some c) : UtInD U c := by
  have h1 : SInvU.capAt σ sl = some c := hc
  rw [dv_capAt_capOpt] at h1
  exact utInD_of_slot h h1

theorem utInD_ci3 {U : UtSetD} {σ : State Unit} (h : HUD U σ) {c : Cap} {src : CslotPtr}
    (hc : CI3 (uV σ) c src) : UtInD U c := by
  obtain ⟨c0, hs, hc⟩ := hc
  rcases hc with ⟨e, -⟩ | hR
  · subst e; exact utInD_of_view h hs
  · exact utInD_noUt (fun b n f => hR.2.2.2.2 true b n f) U

theorem utInD_refEq {U : UtSetD} {σ : State Unit} (h : HUD U σ) {s : CslotPtr} {c0 c : Cap}
    (hs : (uV σ).2.1 s = some c0) (hR : RefEq c0 c) : UtInD U c := by
  rcases hR with e | hR
  · subst e; exact utInD_of_view h hs
  · exact utInD_noUt (fun b n f => hR.2.2.2.2.2.1 true b n f) U

/-! ## The performs -/

set_option maxHeartbeats 4000000 in
theorem zd_invokeCnode (ci : CnodeInvocation) (σ : State Unit) (hZ : ZD σ) (hok : CnOKN (uV σ) ci) :
    ∀ y ∈ ((invokeCnode (Z := Unit) ci).run σ).1, ZD y.2 := by
  refine zd_pin hZ (fun U hU => ?_) (fun _ => ob_invokeCnode ci)
  cases ci with
  | insertCall c s d =>
    have hc : UtInD U c := utInD_ci3 hU hok.1
    have k : IKHE (ε := Unit) (HUD U) (invokeCnode (Z := Unit) (.insertCall c s d)) := by
      simp only [invokeCnode]; hv_auto
    exact k σ hU
  | moveCall c s d =>
    obtain ⟨c0, hs, -, hR, -⟩ := hok
    have hc : UtInD U c := utInD_refEq hU hs hR
    have k : IKHE (ε := Unit) (HUD U) (invokeCnode (Z := Unit) (.moveCall c s d)) := by
      simp only [invokeCnode]; hv_auto
    exact k σ hU
  | rotateCall c1 c2 s1 s2 s3 =>
    obtain ⟨c1', c2', h1, h2, hR1, -, hR2, -⟩ := hok
    have hc1 : UtInD U c1 := utInD_refEq hU h1 hR1
    have hc2 : UtInD U c2 := utInD_refEq hU h2 hR2
    have k : IKHE (ε := Unit) (HUD U) (invokeCnode (Z := Unit) (.rotateCall c1 c2 s1 s2 s3)) := by
      simp only [invokeCnode]; split <;> hv_auto
    exact k σ hU
  | revokeCall s => exact hd_capRevoke s σ hU
  | deleteCall s => exact hd_capDelete s σ hU
  | cancelBadgedSendsCall c =>
    have k : IKHE (ε := Unit) (HUD U) (invokeCnode (Z := Unit) (.cancelBadgedSendsCall c)) := by
      simp only [invokeCnode]; split <;> (try (exfalso; simp_all; done)) <;> hv_auto
    exact k σ hU

set_option maxHeartbeats 4000000 in
theorem zd_invokeIrqHandler (i : IrqHandlerInvocation) (σ : State Unit) (hZ : ZD σ)
    (hok : InvOKN (uV σ) (.invokeIRQHandler i)) :
    ∀ y ∈ (invokeIrqHandler (Z := Unit) i σ).1, ZD y.2 := by
  refine zd_pin hZ (fun U hU => ?_) (fun _ => ob_invokeIrqHandler i)
  cases i with
  | setIRQHandler irq c sl =>
    have hn : isNtfnCap c = true := hok.2.2
    have hc : UtInD U c := utInD_noUt (fun b n f e => by subst e; simp [isNtfnCap] at hn) U
    have k : IKH (HUD U) (invokeIrqHandler (Z := Unit) (.setIRQHandler irq c sl)) := by
      simp only [invokeIrqHandler]; hv_auto
    exact k σ hU
  | aCKIrq irq =>
    have k : IKH (HUD U) (invokeIrqHandler (Z := Unit) (.aCKIrq irq)) := by
      simp only [invokeIrqHandler]; hv_auto
    exact k σ hU
  | clearIRQHandler irq =>
    have k : IKH (HUD U) (invokeIrqHandler (Z := Unit) (.clearIRQHandler irq)) := by
      simp only [invokeIrqHandler]; hv_auto
    exact k σ hU

set_option maxHeartbeats 4000000 in
/-- The TCB invocations: every install re-reads its source slot (`hd_checkCapAt_ins`). -/
theorem hd_invokeTcb {U : UtSetD} (i : TcbInvocation) : IKHE (HUD U) (invokeTcb (Z := Unit) i) := by
  cases i <;> simp only [invokeTcb] <;> hv_auto

theorem zd_invokeTcb (i : TcbInvocation) : IKHE ZD (invokeTcb (Z := Unit) i) :=
  ike_zd (fun _ => hd_invokeTcb i) (fun _ => ob_invokeTcb i)

set_option maxHeartbeats 4000000 in
theorem zdp_endpoint (blk call don : Bool) (ep : ObjRef) (b : Word) (g gr : Bool) :
    IKHE ZD (fl4PerformInvocation (Z := Unit) blk call don (.invokeEndpoint ep b g gr)) := by
  simp only [fl4PerformInvocation]; zd_split

set_option maxHeartbeats 4000000 in
theorem zdp_notification (blk call don : Bool) (ep : ObjRef) (b : Word) :
    IKHE ZD (fl4PerformInvocation (Z := Unit) blk call don (.invokeNotification ep b)) := by
  simp only [fl4PerformInvocation]; zd_split

set_option maxHeartbeats 4000000 in
theorem zdp_domain (blk call don : Bool) (d : DomainInvocation) :
    IKHE ZD (fl4PerformInvocation (Z := Unit) blk call don (.invokeDomain d)) := by
  simp only [fl4PerformInvocation]; zd_split

set_option maxHeartbeats 4000000 in
theorem zdp_reply (blk call don : Bool) (r : ObjRef) (g : Bool) :
    IKHE ZD (fl4PerformInvocation (Z := Unit) blk call don (.invokeReply r g)) := by
  simp only [fl4PerformInvocation]; zd_split

set_option maxHeartbeats 4000000 in
theorem zdp_irqControl (blk call don : Bool) (i : Fl4IrqControlInvocation) :
    IKHE ZD (fl4PerformInvocation (Z := Unit) blk call don (.invokeIRQControl i)) := by
  simp only [fl4PerformInvocation]; zd_split

set_option maxHeartbeats 4000000 in
theorem zdp_schedContext (blk call don : Bool) (i : SchedContextInvocation) :
    IKHE ZD (fl4PerformInvocation (Z := Unit) blk call don (.invokeSchedContext i)) := by
  simp only [fl4PerformInvocation]; zd_split

set_option maxHeartbeats 4000000 in
theorem zdp_schedControl (blk call don : Bool) (i : SchedControlInvocation) :
    IKHE ZD (fl4PerformInvocation (Z := Unit) blk call don (.invokeSchedControl i)) := by
  simp only [fl4PerformInvocation]; zd_split

/-! ## `zd_fl4Perform` -/

/-- **The remaining obligation** (not an invariant premise): the untyped
perform keeps `ZD` for an invocation decoded from the state's view. -/
def PerfGapD : Prop :=
  ∀ (N : Irq → ObjRef) (ui : UntypedInvocation) (σ : State Unit), P3 N σ → NodeIs N σ → ZD σ →
    DecodedFrom (uV σ) (.invokeUntyped ui) → ∀ y ∈ ((fl4InvokeUntyped (Z := Unit) ui).run σ).1, ZD y.2

variable {N : Irq → ObjRef}

set_option maxHeartbeats 4000000 in
theorem zd_fl4Perform (hG : PerfGapD) (blk call don : Bool) (inv : Fl4Invocation) (σ : State Unit)
    (hP : P3 N σ) (hN : NodeIs N σ) (hZ : ZD σ) (hO : InvOKN (uV σ) inv)
    (hD : DecodedFrom (uV σ) inv) :
    ∀ y ∈ ((fl4PerformInvocation (Z := Unit) blk call don inv).run σ).1, ZD y.2 := by
  intro y hy
  cases inv with
  | invokeUntyped ui =>
    simp only [fl4PerformInvocation] at hy
    obtain ⟨z, hz, e⟩ := mem_ret_bindE hy
    rw [e]; exact hG N ui σ hP hN hZ hD z hz
  | invokeFl4TCB i =>
    simp only [fl4PerformInvocation] at hy
    exact zd_invokeFl4Tcb i σ hZ y hy
  | invokeCNode ci =>
    simp only [fl4PerformInvocation] at hy
    obtain ⟨z, hz, e⟩ := mem_ret_bindE hy
    rw [e]; exact zd_invokeCnode ci σ hZ hO z hz
  | invokeIRQHandler i =>
    simp only [fl4PerformInvocation] at hy
    obtain ⟨z, hz, e⟩ := mem_ret_bindE hy
    rw [e]
    obtain ⟨x, hx, rfl⟩ := mem_liftE' hz
    exact zd_invokeIrqHandler i σ hZ hO x hx
  | invokeArchObject fa =>
    simp only [fl4PerformInvocation] at hy
    obtain ⟨fp, label, args, ci, sl, cap, ex, buf, σ0, s0, hv, hc, hex, hmem⟩ := hD
    have hf : GapOKN (uV σ) (.invokeArchObject fa) :=
      okv_fl4DecodeG fp label args ci sl cap ex buf hc (fun p hp => (hex p hp).1) σ0 hv _ s0 hmem
    exact zd_fl4Arch fa σ hP hZ hf y hy
  | invokeTCB i =>
    simp only [fl4PerformInvocation] at hy
    exact zd_invokeTcb i σ hZ y hy
  | invokeEndpoint ep b g gr => exact zdp_endpoint blk call don ep b g gr σ hZ y hy
  | invokeNotification ep b => exact zdp_notification blk call don ep b σ hZ y hy
  | invokeDomain d => exact zdp_domain blk call don d σ hZ y hy
  | invokeReply r g => exact zdp_reply blk call don r g σ hZ y hy
  | invokeIRQControl i => exact zdp_irqControl blk call don i σ hZ y hy
  | invokeSchedContext i => exact zdp_schedContext blk call don i σ hZ y hy
  | invokeSchedControl i => exact zdp_schedControl blk call don i σ hZ y hy

/-! ## The invocation shell -/

/-- `ZD` kept from a `P3 N ∧ NodeIs N ∧ ZD` state. -/
def IKD {α : Type} (m : NonDet (State Unit) α) : Prop :=
  ∀ (N : Irq → ObjRef) σ, P3 N σ → NodeIs N σ → ZD σ → ∀ y ∈ (m σ).1, ZD y.2

abbrev IKDE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := IKD (ExceptT.run m)

theorem ikd_of_ik {α : Type} {m : NonDet (State Unit) α} (h : IKH ZD m) : IKD m :=
  fun _ σ _ _ hZ y hy => h σ hZ y hy

theorem ikde_bind_uk {ε α β : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β}
    (hm : ∀ v, UKE v m) (hmN : ∀ N, NKE N m) (hmZ : IKHE ZD m) (hg : ∀ a, IKDE (g a)) : IKDE (m >>= g) := by
  intro N σ hI hN hZ y hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
  · exact hg a N z.2 (p3_of_view (hm (uV σ) σ rfl z hz) hI) (hmN N σ hN z hz) (hmZ σ hZ z hz) y hy
  · exact hmZ σ hZ z hz

theorem ikde_bind {ε α β : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β}
    (hm : IKDE m) (hg : ∀ a, IKHE ZD (g a)) : IKDE (m >>= g) := by
  intro N σ hI hN hZ y hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
  · exact hg a z.2 (hm N σ hI hN hZ z hz) y hy
  · exact hm N σ hI hN hZ z hz

theorem ikd_bind_post {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β}
    (hm : IKD m) (hg : ∀ a, IKH ZD (g a)) : IKD (m >>= g) := by
  intro N σ hI hN hZ y ⟨x, hx, hy⟩
  exact hg x.1 x.2 (hm N σ hI hN hZ x hx) y hy

theorem zd_restart (thread : ObjRef) :
    IKHE (ε := Unit) ZD (withoutPreemption (Z := Unit) (setThreadState thread .restart)) := by
  zd_split

set_option maxHeartbeats 4000000 in
theorem zd_hiFront (thread : ObjRef) (cptr : CapRef) (info : MessageInfo) :
    IKHE (ε := Fault) ZD (do
       let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot (Z := Unit) thread cptr
       let buffer ← NonDetE.liftE <| lookupIpcBuffer false thread
       let extracaps ← lookupExtraCaps thread buffer info
       NonDetE.returnOk (slot, cap, extracaps, buffer)) := by
  zd_split

set_option maxHeartbeats 4000000 in
theorem zd_hiDecode (thread : ObjRef) (fp : Bool) (info : MessageInfo) (cptr : CapRef) (sl : CslotPtr) (cap : Cap)
    (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) :
    IKHE ZD (do
        let args ← NonDetE.liftE <| getMrs (Z := Unit) thread buf info
        fl4DecodeInvocation fp info.miLabel args cptr sl cap ex buf) := by
  zd_split


end

end Fl4Proofs.P3.SInvDV
