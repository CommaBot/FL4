/-
P3 (issue #16, sd7; KENTRY-PLAN g7a-4 (2)): **`SI N t` across the kernel entries**
(sg1's SpecInvSgE for the idle vtable slot; spec side only). The decode facts are
ut7's `InvOKN`, ut8's `GapOKN` and sg1's `SgOKN`; the performs `iwP_fl4Perform`, the
invocation shell `iwN_handleInvocationR`, the syscalls, the events, `fl4CallKernel`
and the syscall entry, as `IKSI` (kept from an `SI N t` state whose IRQ node is `N`).
-/
import Fl4Proofs.P3.SpecInvSiD
open Classical

namespace Fl4Proofs.P3.SInvIV
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvG

noncomputable section

set_option maxHeartbeats 1000000

variable {N : Irq → ObjRef} {t : ObjRef}

/-! ## The performs -/

set_option maxHeartbeats 4000000 in
theorem iwP_fl4Perform (blk call don : Bool) (inv : Fl4Invocation) (σ : State Unit)
    (hI : SI N t σ) (hN : NodeIs N σ) (hok : InvOKN (uV σ) inv) (hg : GapOKN (uV σ) inv) (hs : SgOKN (uV σ) inv) :
    ∀ y ∈ ((fl4PerformInvocation (Z := Unit) blk call don inv).run σ).1, SI N t y.2 := by
  intro y hy
  cases inv with
  | invokeUntyped ui =>
    simp only [fl4PerformInvocation] at hy
    obtain ⟨z, hz, e⟩ := mem_ret_bindE hy
    rw [e]
    exact iw_invokeUntyped ui σ hI hg z hz
  | invokeArchObject ai =>
    simp only [fl4PerformInvocation] at hy
    by_cases hm : ∃ a, ai = .spec (.invokeASIDControl a)
    · obtain ⟨a, rfl⟩ := hm
      simp only [fl4ArchPerformInvocation, archPerformInvocation] at hy
      obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
      obtain ⟨z, hz, hx⟩ := hx
      rw [Set.mem_singleton_iff.1 hx]
      exact iw_makePool hI hg z hz
    · exact iw_fl4ArchPerform ai (fun a e => hm ⟨a, e⟩) σ hI hg hs y hy
  | invokeCNode ci =>
    simp only [fl4PerformInvocation] at hy
    obtain ⟨z, hz, e⟩ := mem_ret_bindE hy
    rw [e]
    exact iw_invokeCnode ci σ hI hok hs z hz
  | invokeIRQControl i =>
    simp only [fl4PerformInvocation] at hy
    obtain ⟨z, hz, e⟩ := mem_ret_bindE hy
    rw [e]
    exact iw_invokeFl4IrqControl i σ hI hok z hz
  | invokeIRQHandler i =>
    simp only [fl4PerformInvocation] at hy
    obtain ⟨z, hz, e⟩ := mem_ret_bindE hy
    rw [e]
    cases i with
    | setIRQHandler irq c sl =>
      obtain ⟨x, hx, rfl⟩ := mem_liftE' hz
      exact iw_setIRQHandler irq c sl σ hI hN hok x hx
    | _ => exact (show IKE (SI N t) (NonDetE.liftE (ε := Unit) (invokeIrqHandler (Z := Unit) _)) by
        refine ike_liftE ?_; simp only [invokeIrqHandler]; iw_auto) σ hI z hz
  | _ => exact (show IKE (SI N t) _ by simp only [fl4PerformInvocation]; iw_auto) σ hI y hy

/-! ## The invocation shell -/

/-- `SI N t` kept from an `SI N t` state whose IRQ node is `N`. -/
def IKSI {α : Type} (m : NonDet (State Unit) α) : Prop :=
  ∀ (N : Irq → ObjRef) (t : ObjRef) σ, SI N t σ → NodeIs N σ → ∀ y ∈ (m σ).1, SI N t y.2

abbrev IKSIE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := IKSI (ExceptT.run m)

theorem iksi_of_ik {α : Type} {m : NonDet (State Unit) α} (h : ∀ N t, IK (SI N t) m) : IKSI m :=
  fun N t σ hI _ y hy => h N t σ hI y hy

theorem iksie_bind_uk {ε α β : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β}
    (hm : ∀ v, UKE v m) (hmN : ∀ N, NKE N m) (hg : ∀ a, IKSIE (g a)) : IKSIE (m >>= g) := by
  intro N t σ hI hN y hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
  · exact hg a N t z.2 (iw_of_view (hm (uV σ) σ rfl z hz) hI) (hmN N σ hN z hz) y hy
  · exact iw_of_view (hm (uV σ) σ rfl z hz) hI

theorem iksie_bind {ε α β : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β}
    (hm : IKSIE m) (hg : ∀ a, ∀ N t, IKE (SI N t) (g a)) : IKSIE (m >>= g) := by
  intro N t σ hI hN y hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
  · exact hg a N t z.2 (hm N t σ hI hN z hz) y hy
  · exact hm N t σ hI hN z hz

set_option maxHeartbeats 8000000 in
/-- **The invocation keeps `SI N t`.** -/
theorem iwN_handleInvocationR (rep calling blocking don fp : Bool) (cptr : CapRef) :
    IKSIE (fl4HandleInvocationR (Z := Unit) rep calling blocking don fp cptr) := by
  unfold fl4HandleInvocationR
  refine iksie_bind_uk (fun _ => by uk_auto) (fun _ => by nk_auto) fun thread =>
    iksie_bind_uk (fun _ => by uk_auto) (fun _ => by nk_auto) fun info => ?_
  intro N t σ hI hN y hy
  have hF : ∀ v, UKE v (do
       let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot (Z := Unit) thread cptr
       let buffer ← NonDetE.liftE <| lookupIpcBuffer false thread
       let extracaps ← lookupExtraCaps thread buffer info
       NonDetE.returnOk (slot, cap, extracaps, buffer)) := fun _ => by uk_auto
  have hFN : NKE N (do
       let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot (Z := Unit) thread cptr
       let buffer ← NonDetE.liftE <| lookupIpcBuffer false thread
       let extracaps ← lookupExtraCaps thread buffer info
       NonDetE.returnOk (slot, cap, extracaps, buffer)) := by nk_auto
  have hOk : OkV (uV σ) (fun r : CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef =>
      (uV σ).2.1 r.1 = some r.2.1 ∧ ∀ p ∈ r.2.2.1, (uV σ).2.1 p.2 = some p.1 ∧ DestRefV (uV σ) p.2) (do
       let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot (Z := Unit) thread cptr
       let buffer ← NonDetE.liftE <| lookupIpcBuffer false thread
       let extracaps ← lookupExtraCaps thread buffer info
       NonDetE.returnOk (slot, cap, extracaps, buffer)) := by
    refine okv_bind (fun _ => uk_capFaultOnFailure _ _ _ (uk_lookupCapAndSlot _ _))
      (okv_capFaultOnFailure _ _ (okv_lookupCapAndSlot _ _)) fun x hx => ?_
    obtain ⟨cap, slot⟩ := x
    dsimp only
    refine okv_bind_uk (fun _ => ike_liftE (uk_lookupIpcBuffer _ _)) fun buf => ?_
    refine okv_bind (fun _ => uk_lookupExtraCaps _ _ _) (okv_lookupExtraCapsN _ _ _) fun ex hex => okv_returnOk ?_
    exact ⟨hx, hex⟩
  refine syscall_postU (I := fun s => SI N t s ∧ uV s = uV σ ∧ NodeIs N s) (Q := SI N t)
    (fun w hw => ⟨iw_of_view (hF _ σ rfl w hw) hI, hF _ σ rfl w hw, hFN σ hN w hw⟩) ?_ ?_ ?_ ?_ y hy
  · intro f s hs v hv
    exact (show IK (SI N t) (NonDet.when blocking (handleFault thread f)) by iw_auto) s hs.1 v hv
  · intro a s has w hw
    have hs : SI N t s ∧ uV s = uV σ ∧ NodeIs N s :=
      ⟨iw_of_view (hF _ σ rfl _ has) hI, hF _ σ rfl _ has, hFN σ hN _ has⟩
    obtain ⟨sl, cap, ex, buf⟩ := a
    have hE : ∀ v, UKE v (do
        let args ← NonDetE.liftE <| getMrs (Z := Unit) thread buf info
        fl4DecodeInvocation fp info.miLabel args cptr sl cap ex buf) := fun _ => by uk_auto
    have hEN : NKE N (do
        let args ← NonDetE.liftE <| getMrs (Z := Unit) thread buf info
        fl4DecodeInvocation fp info.miLabel args cptr sl cap ex buf) := by nk_auto
    exact ⟨iw_of_view (hE _ s rfl w hw) hs.1, (hE _ s rfl w hw).trans hs.2.1, hEN s hs.2.2 w hw⟩
  · intro e s hs v hv
    exact (iw_of_uk fun _ => by uk_auto) s hs.1 v hv
  · intro a s b s' has hbs hI' y hy
    obtain ⟨sl, cap, ex, buf⟩ := a
    have hvs : uV s = uV σ := hF _ σ rfl _ has
    obtain ⟨hc, hex⟩ := hOk σ rfl _ s has
    obtain ⟨z0, hz0, ⟨args, ha0, hb0⟩ | ⟨e, -, he⟩⟩ := mem_bindE' hbs
    swap
    · simp at he
    obtain ⟨x0, hx0, e0⟩ := mem_liftE' hz0
    subst e0
    simp only [Except.ok.injEq] at ha0
    subst ha0
    have hvx : uV x0.2 = uV σ := (uk_getMrs (uvw := uV s) _ _ _ s rfl x0 hx0).trans hvs
    have hdec : InvOKN (uV σ) b :=
      okv_fl4DecodeN fp info.miLabel x0.1 cptr sl cap ex buf hc hex x0.2 hvx b s' hb0
    have hdg : GapOKN (uV σ) b :=
      okv_fl4DecodeG fp info.miLabel x0.1 cptr sl cap ex buf hc (fun p hp => (hex p hp).1) x0.2 hvx b s' hb0
    have hds : SgOKN (uV σ) b :=
      okv_fl4DecodeS fp info.miLabel x0.1 cptr sl cap ex buf hc (fun p hp => (hex p hp).1) x0.2 hvx b s' hb0
    obtain ⟨z, hz, ⟨u, hu, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
    · have hz' : uV z.2 = uV s' := (show ∀ v, UKE v (withoutPreemption (Z := Unit) (setThreadState thread .restart))
        from fun _ => by uk_auto) _ s' rfl z hz
      have hzN : NodeIs N z.2 := (show NKE N (withoutPreemption (Z := Unit) (setThreadState thread .restart))
        by nk_auto) s' hI'.2.2 z hz
      obtain ⟨r, s1⟩ := z
      simp only at hu; subst hu
      have hv1 : uV s1 = uV σ := hz'.trans hI'.2.1
      have hI1 : SI N t s1 := iw_of_view hz' hI'.1
      have hok1 : InvOKN (uV s1) b := by rw [hv1]; exact hdec
      have hg1 : GapOKN (uV s1) b := by rw [hv1]; exact hdg
      have hs1 : SgOKN (uV s1) b := by rw [hv1]; exact hds
      obtain ⟨z2, hz2, ⟨rp, hr, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
      · obtain ⟨r2, s2⟩ := z2
        simp only at hr; subst hr
        have hs2 := iwP_fl4Perform blocking calling don b s1 hI1 hzN hok1 hg1 hs1 _ hz2
        exact (iwe_of_uk fun _ => by uk_auto) s2 hs2 y hy
      · exact iwP_fl4Perform blocking calling don b s1 hI1 hzN hok1 hg1 hs1 _ hz2
    · exact iw_of_view ((show ∀ v, UKE v (withoutPreemption (Z := Unit) (setThreadState thread .restart))
        from fun _ => by uk_auto) _ s' rfl z hz) hI'.1

/-! ## The syscall paths and events -/

set_option maxHeartbeats 4000000 in
theorem iwN_fl4HandleSyscall (rep : Bool) (c : Syscall) : IKSIE (fl4HandleSyscall (Z := Unit) rep c) := by
  cases c <;> simp only [fl4HandleSyscall]
  all_goals first
    | exact iksie_bind_uk (fun _ => by uk_auto) (fun _ => by nk_auto) fun _ => iwN_handleInvocationR _ _ _ _ _ _
    | exact iksie_bind_uk (fun _ => by uk_auto) (fun _ => by nk_auto) fun _ =>
        iksie_bind (iwN_handleInvocationR _ _ _ _ _ _) fun _ _ _ => by iw_auto
    | exact iksi_of_ik fun _ _ => by iw_auto

set_option maxHeartbeats 4000000 in
theorem iw_handleEvent_other (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) :
    IKE (SI N t) (handleEvent (Z := Unit) ev) := by
  cases ev with
  | syscallEvent c => exact absurd rfl (h c)
  | _ => simp only [handleEvent]; iw_auto

set_option maxHeartbeats 4000000 in
theorem iwN_fl4HandleEvent (rep : Bool) (ev : Event) : IKSIE (fl4HandleEvent (Z := Unit) rep ev) := by
  by_cases h : ∃ c, ev = .syscallEvent c
  · obtain ⟨c, rfl⟩ := h
    simp only [fl4HandleEvent]
    refine iksie_bind_uk (fun _ => ike_liftE (uk_updateTimeStamp)) (fun _ => by nk_auto) fun _ => ?_
    intro N t σ hI hN y hy
    obtain ⟨z, hz, ⟨r, hr, hy⟩ | ⟨e, he, rfl⟩⟩ := mem_bindE' hy
    · obtain ⟨x, hx, rfl⟩ := mem_liftE' hz
      simp only [Except.ok.injEq] at hr; subst hr
      have hIx : SI N t x.2 := iw_checkBudgetRestart σ hI x hx
      have hNx : NodeIs N x.2 := (show NK N (checkBudgetRestart (Z := Unit)) by nk_auto) σ hN x hx
      unfold NonDetE.whenE at hy
      split at hy
      · exact iwN_fl4HandleSyscall rep c N t x.2 hIx hNx y hy
      · rw [Set.mem_singleton_iff.1 hy]; exact hIx
    · obtain ⟨x, hx, rfl⟩ := mem_liftE' hz; cases he
  · rw [fl4HandleEvent_other rep ev fun c e => h ⟨c, e⟩]
    exact iksi_of_ik fun _ _ => iw_handleEvent_other ev fun c e => h ⟨c, e⟩

theorem iksi_bind {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β}
    (hm : IKSI m) (hg : ∀ a, ∀ N t, IK (SI N t) (g a)) : IKSI (m >>= g) := by
  intro N t σ hI hN y ⟨x, hx, hy⟩
  exact hg x.1 N t x.2 (hm N t σ hI hN x hx) y hy

theorem iksi_bind_uk {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β}
    (hm : ∀ v, UK v m) (hmN : ∀ N, NK N m) (hg : ∀ a, IKSI (g a)) : IKSI (m >>= g) := by
  intro N t σ hI hN y ⟨x, hx, hy⟩
  exact hg x.1 N t x.2 (iw_of_view (uk_mem hm hx) hI) (hmN N σ hN x hx) y hy

set_option maxHeartbeats 4000000 in
theorem iwN_fl4CallKernel (rep : Bool) (ev : Event) : IKSI (fl4CallKernel (Z := Unit) rep ev) := by
  unfold fl4CallKernel
  refine iksi_bind ?_ fun _ _ _ => by iw_auto
  intro N t σ hI hN y hy
  unfold NonDetE.handleE at hy
  rw [ExceptT.run_mk] at hy
  obtain ⟨z, hz, hy⟩ := hy
  have hz' := iwN_fl4HandleEvent rep ev N t σ hI hN z hz
  obtain ⟨r, s⟩ := z
  cases r with
  | ok a => rw [Set.mem_singleton_iff.1 hy]; exact hz'
  | error e => exact (show IKE (SI N t) (withoutPreemption (Z := Unit) preemptionPath) by iw_auto) s hz' y hy

set_option maxHeartbeats 4000000 in
theorem iwN_kentry (c : Syscall) : IKSI (fl4KernelEntrySyscall (Z := Unit) true c) := by
  unfold fl4KernelEntrySyscall
  exact iksi_bind_uk (fun _ => ik_gets _) (fun _ => ik_gets _) fun ct => iksi_bind_uk
    (fun _ => uk_fl4SyscallFaultIP ct) (fun _ => nk_fl4SyscallFaultIP ct) fun _ => iwN_fl4CallKernel true _

/-! ## The handled event and the front of the syscall entry -/

set_option maxHeartbeats 4000000 in
/-- The handled event (with the preemption path on an error), as at the finish states. -/
theorem iwN_handleE (rep : Bool) (ev : Event) :
    IKSI (NonDetE.handleE (fl4HandleEvent (Z := Unit) rep ev) (fun _ => withoutPreemption preemptionPath)).run := by
  intro N t σ hI hN y hy
  unfold NonDetE.handleE at hy
  rw [ExceptT.run_mk] at hy
  obtain ⟨z, hz, hy⟩ := hy
  have hz' := iwN_fl4HandleEvent rep ev N t σ hI hN z hz
  obtain ⟨r, s⟩ := z
  cases r with
  | ok a => rw [Set.mem_singleton_iff.1 hy]; exact hz'
  | error e => exact (show IKE (SI N t) (withoutPreemption (Z := Unit) preemptionPath) by iw_auto) s hz' y hy

theorem idk_handleE' (K : ObjRef) (rep : Bool) (ev : Event) :
    IdK K (NonDetE.handleE (fl4HandleEvent (Z := Unit) rep ev) (fun _ => withoutPreemption preemptionPath)).run := by
  intro σ hσ y hy
  unfold NonDetE.handleE at hy
  rw [ExceptT.run_mk] at hy
  obtain ⟨z, hz, hy⟩ := hy
  have hz' := idk_fl4HandleEvent (N := K) rep ev σ hσ z hz
  obtain ⟨r, s⟩ := z
  cases r with
  | ok a => rw [Set.mem_singleton_iff.1 hy]; exact hz'
  | error e => exact idk_withoutPreemption (N := K) _ idk_preemptionPath s hz' y hy

/-- The `FaultIP` write, then the handled event (`specFront`'s shape). -/
theorem iwN_front (ct : ObjRef) (rep : Bool) (ev : Event) :
    IKSI (fl4SyscallFaultIP (Z := Unit) ct >>= fun _ =>
      (NonDetE.handleE (fl4HandleEvent (Z := Unit) rep ev) (fun _ => withoutPreemption preemptionPath)).run) :=
  iksi_bind_uk (fun _ => uk_fl4SyscallFaultIP ct) (fun _ => nk_fl4SyscallFaultIP ct) fun _ => iwN_handleE rep ev

theorem idk_front (K ct : ObjRef) (rep : Bool) (ev : Event) :
    IdK K (fl4SyscallFaultIP (Z := Unit) ct >>= fun _ =>
      (NonDetE.handleE (fl4HandleEvent (Z := Unit) rep ev) (fun _ => withoutPreemption preemptionPath)).run) :=
  ik_bind' (idk_fl4SyscallFaultIP ct) fun _ => idk_handleE' K rep ev

/-! ## The idle vtable fact on states -/

/-- **`IdleVtS σ`**: the idle TCB's vtable slot holds the null cap (if anything;
INV-PLAN §1.U3L D7, the spec-only form; l4v: `create_idle_thread` makes the idle TCB with
null caps, and no cap names the idle thread, so nothing writes its slots). -/
def IdleVtS (σ : State Unit) : Prop := IVV σ.idleThread (uV σ)

/-- The family at the state's node and idle thread, from sg1's carried facts. -/
theorem si_at {σ : State Unit} (hG : SpecGlobS σ) (hI : IdleOutV σ) (hU : UtInv3 σ) (hV : IdleVtS σ) :
    SI σ.interruptIrqNode σ.idleThread σ :=
  ⟨(S_of_specGlob hG hI hU).1, hI, hV⟩

/-- `IdleVtS` across any step of the family that keeps the idle thread. -/
theorem idleVtS_step {α : Type} {m : NonDet (State Unit) α} (hm : IKSI m) (hid : ∀ K, IdK K m)
    {σ : State Unit} (hG : SpecGlobS σ) (hI : IdleOutV σ) (hU : UtInv3 σ) (hV : IdleVtS σ) :
    ∀ y ∈ (m σ).1, IdleVtS y.2 := by
  intro y hy
  have h := hm _ _ σ (si_at hG hI hU hV) rfl y hy
  have e : y.2.idleThread = σ.idleThread := hid σ.idleThread σ rfl y hy
  show IVV y.2.idleThread (uV y.2)
  rw [e]; exact h.2.2

/-- **`IdleVtS` across the syscall entry.** -/
theorem kentry_idleVtS (c : Syscall) {σ : State Unit} (hG : SpecGlobS σ) (hI : IdleOutV σ) (hU : UtInv3 σ)
    (hV : IdleVtS σ) : ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, IdleVtS y.2 :=
  idleVtS_step (iwN_kentry c) (fun _ => idk_fl4KernelEntrySyscall true c) hG hI hU hV

/-- **`IdleVtS` across every kernel event.** -/
theorem kcall_idleVtS (rep : Bool) (ev : Event) {σ : State Unit} (hG : SpecGlobS σ) (hI : IdleOutV σ)
    (hU : UtInv3 σ) (hV : IdleVtS σ) : ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, IdleVtS y.2 :=
  idleVtS_step (iwN_fl4CallKernel rep ev) (fun _ => idk_fl4CallKernel rep ev) hG hI hU hV

/-- **`IdleVtS` at the handled event's outcomes** (the event finish states). -/
theorem handleE_idleVtS (rep : Bool) (ev : Event) {σ : State Unit} (hG : SpecGlobS σ) (hI : IdleOutV σ)
    (hU : UtInv3 σ) (hV : IdleVtS σ) :
    ∀ y ∈ ((NonDetE.handleE (fl4HandleEvent (Z := Unit) rep ev) (fun _ => withoutPreemption preemptionPath)).run σ).1,
      IdleVtS y.2 :=
  idleVtS_step (iwN_handleE rep ev) (fun K => idk_handleE' K rep ev) hG hI hU hV

/-- **`IdleVtS` after the `FaultIP` write and the handled event** (the syscall finish states and
the trap / unknown-syscall event finish states). -/
theorem front_idleVtS (ct : ObjRef) (rep : Bool) (ev : Event) {σ : State Unit} (hG : SpecGlobS σ)
    (hI : IdleOutV σ) (hU : UtInv3 σ) (hV : IdleVtS σ) :
    ∀ y ∈ ((fl4SyscallFaultIP (Z := Unit) ct >>= fun _ =>
      (NonDetE.handleE (fl4HandleEvent (Z := Unit) rep ev) (fun _ => withoutPreemption preemptionPath)).run) σ).1,
      IdleVtS y.2 :=
  idleVtS_step (iwN_front ct rep ev) (fun K => idk_front K ct rep ev) hG hI hU hV

/-- **`IdleVtS` after the `FaultIP` write and a kernel event** (the trap / unknown-syscall exits). -/
theorem fip_kcall_idleVtS (ct : ObjRef) (ev : Event) {σ : State Unit} (hG : SpecGlobS σ)
    (hI : IdleOutV σ) (hU : UtInv3 σ) (hV : IdleVtS σ) :
    ∀ y ∈ ((fl4SyscallFaultIP (Z := Unit) ct >>= fun _ => fl4CallKernel (Z := Unit) true ev) σ).1, IdleVtS y.2 :=
  idleVtS_step (iksi_bind_uk (fun _ => uk_fl4SyscallFaultIP ct) (fun _ => nk_fl4SyscallFaultIP ct)
      fun _ => iwN_fl4CallKernel true ev)
    (fun K => ik_bind' (idk_fl4SyscallFaultIP (N := K) ct) fun _ => idk_fl4CallKernel true ev) hG hI hU hV

/-- Boot (non-vacuity only: the initial state holds null caps). -/
theorem boot_idleVtS : IdleVtS (initASt (Z := Unit)) := fun _ ha => init_capAt (sl := ((initASt (Z := Unit)).idleThread, tcbCnodeIndex 1)) ha

end

end Fl4Proofs.P3.SInvIV
