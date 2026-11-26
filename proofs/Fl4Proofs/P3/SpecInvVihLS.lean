/-
P3 (line irqfix, gen 3): **l4v's `valid_irq_handlers` across the whole kernel entry** (SpecInvValidIrqHandlersS
restated for `ValidIrqHandlersL`, SpecInvVihL; spec side only; outside the `JAtZ` cone).

* The decode's carry `InvCALd` (CNode caps and the set-handler notification cap are `CAL`), `okdl_fl4Decode`;
  the ack's handler cap by vih2's `okAck_fl4Decode`.
* `vil_fl4Perform`, the shell `vil_handleInvocationR`, the syscalls, every event, `fl4CallKernel`, the syscall
  entry.
* **`kentry_validIrqMasksL`** / **`kirq_validIrqMasksL`** and `kentry_vihL` / `kirq_vihL`: `ValidIrqMasks ∧
  ValidIrqHandlersL` across `fl4KernelEntrySyscall true c` / `fl4CallKernel true .interrupt`, no side condition;
  `vil_fl4CallKernel` for every event, `vil_fl4SyscallFaultIP`, `vil_budget` (the dispatch front).

So no spec entry breaks l4v's `valid_irq_handlers`: the port's weaker `ValidIrqHandlers` is not needed to make the
preservation go through. No premise; no sorry.
-/
import Fl4Proofs.P3.SpecInvVihLG
import Fl4Proofs.P3.SpecInvValidIrqHandlersS
open Classical

namespace Fl4Proofs.P3.SInvVL
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvDom Fl4Proofs.P3.SInvV

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The decode's carry -/

theorem cal_maskCap {c : Cap} {is : Irq → IrqState} (h : CAL c is) (r : CapRights) : CAL (maskCap r c) is := by
  intro irq e; apply h irq
  cases c <;> simp_all [maskCap, capRightsUpdate]

theorem cal_updateCapData {c : Cap} {is : Irq → IrqState} (h : CAL c is) (p : Bool) (w : Data) :
    CAL (updateCapData p w c) is := by
  intro irq e; apply h irq
  unfold updateCapData at e
  split_ifs at e <;> first
    | (cases c <;> simp_all [badgeUpdate]; done)
    | (cases e; done)
    | (simp only [archUpdateCapData] at e; cases e)
    | (cases c <;> simp_all; done)
    | (dsimp only at e; split_ifs at e <;> cases e)
    | exact e

theorem okvl_getCap {σ0 : State Unit} (hv : ValidIrqHandlersL σ0) (sl : CslotPtr) :
    OkV σ0 (fun c => CAL c σ0.interruptStates) (NonDetE.liftE (ε := SyscallError) (getCap (Z := Unit) sl)) := by
  intro s hs a s' h
  obtain ⟨y, hy, e⟩ := mem_liftE_inv' h
  simp only [Prod.mk.injEq, Except.ok.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  obtain ⟨o, r⟩ := sl
  obtain ⟨e1, e2⟩ := vih_mem_getCap hy
  rw [e1]
  refine ⟨hs, ?_⟩
  have := cal_of_slot (vihl_of_hV hs hv) e2
  rw [hV_is hs] at this; exact this

macro "okvl_step" : tactic => `(tactic| first
  | exact okv_throw _
  | exact okv_returnOk trivial
  | (refine okv_returnOk_bind ?_)
  | (refine okv_bind (okvl_getCap (by assumption) _) fun _ _ => ?_)
  | (refine okv_bind (okv_frame fun v => by hv_auto) fun _ _ => ?_)
  | (apply okv_ite)
  | split)

set_option maxHeartbeats 4000000 in
theorem okvl_decodeCnode {σ0 : State Unit} (hv : ValidIrqHandlersL σ0) (label : Data) (args : List Data) (cap : Cap)
    (excaps : List Cap) :
    OkV σ0 (fun i => CnCAL i σ0.interruptStates) (decodeCnodeInvocation (Z := Unit) label args cap excaps) := by
  unfold decodeCnodeInvocation
  repeat' (first
    | (refine okv_bind (okvl_getCap hv _) fun c0 hc0 => ?_)
    | (refine okv_bind (okv_ite_app _ (okv_returnOk ?_) (okvl_deriveCap _ _ ?_)) fun c1 hc1 => ?_)
    | exact okv_returnOk (by split <;> (simp only [CnCAL]; assumption))
    | exact okv_returnOk ⟨cal_updateCapData (by assumption) _ _, cal_updateCapData (by assumption) _ _⟩
    | okvl_step)
  all_goals first
    | (split <;> exact cal_updateCapData (cal_maskCap (by assumption) _) _ _)
    | exact cal_updateCapData (cal_maskCap (by assumption) _) _ _
    | exact cal_maskCap (by assumption) _

/-- The caps a decoded invocation will write are `CAL`. -/
def InvCALd (is : Irq → IrqState) : Fl4Invocation → Prop
  | .invokeCNode i => CnCAL i is
  | .invokeIRQHandler (.setIRQHandler _ c _) => CAL c is
  | _ => True

theorem okdl_decodeCnode (label : Data) (args : List Data) (cap : Cap) (excaps : List Cap) (s : State Unit) :
    OkDAt s (fun s' i => ValidIrqHandlersL s' → InvCALd s'.interruptStates (.invokeCNode i))
      (decodeCnodeInvocation (Z := Unit) label args cap excaps) := by
  intro a s' h hv'
  have e : hV s' = hV s := hv_decodeCnodeInvocation (P := fun x => hV x = hV s) _ _ _ _ s rfl _ h
  have hv : ValidIrqHandlersL s := vihl_of_hV e.symm hv'
  obtain ⟨-, hc⟩ := okvl_decodeCnode hv label args cap excaps s rfl a s' h
  show CnCAL a s'.interruptStates
  rw [hV_is e]; exact hc

theorem okdl_decodeIrqHandler (label : Data) (irq : Irq) (cps : List (Cap × CslotPtr)) (s : State Unit) :
    OkDAt s (fun s' v => ValidIrqHandlersL s' → InvCALd s'.interruptStates (.invokeIRQHandler v))
      (decodeIrqHandlerInvocation (Z := Unit) label irq cps) := by
  unfold decodeIrqHandlerInvocation
  repeat' (first
    | exact okdAt_throw _
    | exact okdAt_returnOk (fun _ => trivial)
    | exact okdAt_returnOk (fun _ => cal_noH (fun irq e => by simp_all [isNtfnCap]) _)
    | split)

set_option maxHeartbeats 4000000 in
theorem okdl_fl4Decode (fp : Bool) (label : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr) (cap : Cap)
    (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) (σ : State Unit) :
    OkDAt σ (fun s' inv => ValidIrqHandlersL s' → InvCALd s'.interruptStates inv)
      (fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex buf) := by
  unfold fl4DecodeInvocation
  split
  all_goals try unfold fl4DecodeTcbInvocation
  all_goals repeat' (first
    | exact okdAt_throw _
    | exact okdAt_returnOk (fun _ => trivial)
    | exact okdAt_liftME (okdl_decodeCnode _ _ _ _ _)
    | exact okdAt_liftME (okdl_decodeIrqHandler _ _ _ _)
    | exact okdAt_liftME (fun _ _ _ _ => trivial)
    | (apply okdAt_ite)
    | (refine okdAt_bind fun _ _ _ => ?_)
    | split)

/-! ## The performs -/

set_option maxHeartbeats 8000000 in
theorem vil_fl4Perform (blk call don : Bool) (inv : Fl4Invocation) (σ : State Unit) (h : VIL σ)
    (hc : InvCALd σ.interruptStates inv) (hack : ∀ i, inv = .invokeIRQHandler (.aCKIrq i) → HIrq σ i) :
    ∀ x ∈ ((fl4PerformInvocation (Z := Unit) blk call don inv).run σ).1, VIL x.2 := by
  cases inv with
  | invokeCNode i =>
    intro x hx
    simp only [fl4PerformInvocation] at hx
    have := (ike_bind (vhl_invokeCnode i) fun _ => ike_returnOk _ :
      IKHE (ε := Unit) (VHL (CnCAL i)) (invokeCnode (Z := Unit) i >>= fun _ => NonDetE.returnOk [])) σ
      ⟨h.1, h.2.1, hc⟩ x hx
    exact ⟨this.1, this.2.1, trivial⟩
  | invokeIRQHandler i =>
    intro x hx
    simp only [fl4PerformInvocation] at hx
    obtain ⟨z, hz, ⟨u, hu, hx⟩ | ⟨e, he, rfl⟩⟩ := mem_bindE_inv' hx
    · obtain ⟨w, hw, rfl⟩ := mem_liftE_inv' hz
      have hi : IhCAL i σ := by
        cases i with
        | aCKIrq irq => exact hack irq rfl
        | setIRQHandler irq c s => exact hc
        | clearIRQHandler irq => trivial
      have h1 := vil_invokeIrqHandler i σ h hi w hw
      obtain rfl := Set.mem_singleton_iff.1 hx
      exact h1
    · obtain ⟨w, -, rfl⟩ := mem_liftE_inv' hz; cases he
  | _ => exact (show IKHE (ε := Unit) VIL (fl4PerformInvocation (Z := Unit) blk call don _) from by
      simp only [fl4PerformInvocation]; hv_auto) σ h

/-! ## The invocation shell -/

/-- **The invocation keeps `VIL`.** -/
theorem vil_handleInvocationR (rep calling blocking don fp : Bool) (cptr : CapRef) :
    IKHE (ε := Unit) VIL (fl4HandleInvocationR (Z := Unit) rep calling blocking don fp cptr) := by
  unfold fl4HandleInvocationR
  refine ike_bind (by hv_auto) fun thread => ike_bind (by hv_auto) fun info => ?_
  intro σ hs y hy
  have h1 : ∀ w ∈ ((ExceptT.run (do
       let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot (Z := Unit) thread cptr
       let buffer ← NonDetE.liftE <| lookupIpcBuffer false thread
       let extracaps ← lookupExtraCaps thread buffer info
       NonDetE.returnOk (slot, cap, extracaps, buffer))) σ).1, VIL w.2 :=
    fun w hw => (by hv_auto : IKHE (ε := Fault) VIL _) σ hs w hw
  refine syscall_post' (I := VIL) (Q := VIL) h1 ?_ ?_ ?_ ?_ y hy
  · intro f s hs v hv; exact (by hv_auto : IKH VIL _) s hs v hv
  · intro a s has w hw
    obtain ⟨sl, cap, ex, buf⟩ := a
    exact (by hv_auto : IKHE VIL _) s (h1 _ has) w hw
  · intro e s hs v hv; exact (by hv_auto : IKH VIL _) s hs v hv
  · intro a s b s' has hbs hI y hy
    obtain ⟨sl, cap, ex, buf⟩ := a
    have hcap : capOpt (s.kheap sl.1) sl.2 = some cap := okCap_front thread cptr info σ _ s has
    have eE : hV s' = hV s := (by hv_auto : IKHE (fun x => hV x = hV s) _) s rfl _ hbs
    have hd : ValidIrqHandlersL s' → InvCALd s'.interruptStates b :=
      okdAt_bind (fun _ s1 _ => okdl_fl4Decode _ _ _ _ _ _ _ _ s1) b s' hbs
    have hk : ∀ i, b = .invokeIRQHandler (.aCKIrq i) → HIrq s' i := fun i e => by
      have hc2 := okdAt_bind (fun _ s1 _ => okAck_fl4Decode _ _ _ _ _ _ _ _ s1) b s' hbs i e
      exact ⟨sl.1, sl.2, by rw [hV_cap eE, ← hc2]; exact hcap⟩
    obtain ⟨z, hz, ⟨u, hu, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE_inv' hy
    · have hz' : hV z.2 = hV s' := (by hv_auto : IKHE (ε := Unit) (fun x => hV x = hV s')
        (withoutPreemption (Z := Unit) (setThreadState thread .restart))) s' rfl z hz
      have hz1 : VIL z.2 := (by hv_auto : IKHE (ε := Unit) VIL
        (withoutPreemption (Z := Unit) (setThreadState thread .restart))) s' hI z hz
      obtain ⟨r, s1⟩ := z
      simp only at hu; subst hu
      have hd1 : InvCALd s1.interruptStates b := by rw [hV_is hz']; exact hd hI.2.1
      have hk1 : ∀ i, b = .invokeIRQHandler (.aCKIrq i) → HIrq s1 i := fun i e => hIrq_of_hV hz' (hk i e)
      obtain ⟨z2, hz2, ⟨rp, hr, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE_inv' hy
      · obtain ⟨r2, s2⟩ := z2
        simp only at hr; subst hr
        have hs2 := vil_fl4Perform blocking calling don b s1 hz1 hd1 hk1 _ hz2
        exact (by hv_auto : IKHE VIL _) s2 hs2 y hy
      · exact vil_fl4Perform blocking calling don b s1 hz1 hd1 hk1 _ hz2
    · exact (by hv_auto : IKHE (ε := Unit) VIL
        (withoutPreemption (Z := Unit) (setThreadState thread .restart))) s' hI z hz

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vil_handleInvocationR _ _ _ _ _ _)

/-! ## The kernel entry -/

set_option maxHeartbeats 8000000 in
theorem vil_fl4HandleSyscall (rep : Bool) (c : Syscall) : IKHE (ε := Unit) VIL (fl4HandleSyscall (Z := Unit) rep c) := by
  cases c <;> simp only [fl4HandleSyscall] <;> hv_auto

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vil_fl4HandleSyscall _ _)

set_option maxHeartbeats 8000000 in
theorem vil_handleEvent_other (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) :
    IKHE (ε := Unit) VIL (handleEvent (Z := Unit) ev) := by
  cases ev with
  | syscallEvent c => exact absurd rfl (h c)
  | _ => simp only [handleEvent]; hv_auto

set_option maxHeartbeats 4000000 in
theorem vil_fl4HandleEvent (rep : Bool) (ev : Event) : IKHE (ε := Unit) VIL (fl4HandleEvent (Z := Unit) rep ev) := by
  by_cases h : ∃ c, ev = .syscallEvent c
  · obtain ⟨c, rfl⟩ := h
    simp only [fl4HandleEvent]
    hv_auto
  · rw [fl4HandleEvent_other rep ev fun c e => h ⟨c, e⟩]
    exact vil_handleEvent_other ev fun c e => h ⟨c, e⟩

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vil_fl4HandleEvent _ _)

set_option maxHeartbeats 4000000 in
/-- **`fl4CallKernel` keeps `VIL`, for every event.** -/
theorem vil_fl4CallKernel (rep : Bool) (ev : Event) : IKH VIL (fl4CallKernel (Z := Unit) rep ev) := by
  unfold fl4CallKernel; hv_auto

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vil_fl4CallKernel _ _)

theorem vil_fl4KernelEntrySyscall (rep : Bool) (c : Syscall) : IKH VIL (fl4KernelEntrySyscall (Z := Unit) rep c) := by
  unfold fl4KernelEntrySyscall; hv_auto

/-! ## Tops -/

/-- **`ValidIrqMasks ∧ ValidIrqHandlersL` across a whole syscall entry** (no side condition). -/
theorem kentry_validIrqMasksL {c : Syscall} {σ : State Unit} (hm : ValidIrqMasks σ) (hh : ValidIrqHandlersL σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c σ).1), ValidIrqMasks y.2 ∧ ValidIrqHandlersL y.2 :=
  fun y hy => let h := vil_fl4KernelEntrySyscall true c σ ⟨hm, hh, trivial⟩ y hy; ⟨h.1, h.2.1⟩

/-- **The same across the interrupt / timer entry** (`fl4CallKernel true .interrupt`). -/
theorem kirq_validIrqMasksL {σ : State Unit} (hm : ValidIrqMasks σ) (hh : ValidIrqHandlersL σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) true .interrupt σ).1), ValidIrqMasks y.2 ∧ ValidIrqHandlersL y.2 :=
  fun y hy => let h := vil_fl4CallKernel true .interrupt σ ⟨hm, hh, trivial⟩ y hy; ⟨h.1, h.2.1⟩

/-- `ValidIrqHandlersL` across a syscall entry (jointly with `ValidIrqMasks`). -/
theorem kentry_vihL {c : Syscall} {σ : State Unit} (hm : ValidIrqMasks σ) (hh : ValidIrqHandlersL σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c σ).1), ValidIrqHandlersL y.2 :=
  fun y hy => (kentry_validIrqMasksL hm hh y hy).2

theorem kirq_vihL {σ : State Unit} (hm : ValidIrqMasks σ) (hh : ValidIrqHandlersL σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) true .interrupt σ).1), ValidIrqHandlersL y.2 :=
  fun y hy => (kirq_validIrqMasksL hm hh y hy).2


/-- The FaultIP write keeps `VIL`. -/
theorem vil_fl4SyscallFaultIP (t : ObjRef) : IKH VIL (fl4SyscallFaultIP (Z := Unit) t) :=
  hv_fl4SyscallFaultIP t

/-- The budget front (`update_time_stamp` then `check_budget_restart`) keeps `VIL`. -/
theorem vil_budget : IKH VIL (updateTimeStamp (Z := Unit) >>= fun _ => checkBudgetRestart (Z := Unit)) := by
  hv_auto

end

end Fl4Proofs.P3.SInvVL
