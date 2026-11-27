/-
P3 (line p3J, gen 16): **the cap-kind invariant `CKI` across the whole kernel entry** (spec side only;
outside the `JAtZ` cone; part 3 of P3JCkW / P3JCkX; SpecInvIoPortsS's shell with `InvK` for `InvIo`).

* The decode's carry `InvK inv` (a pure fact of the invocation): a CNode invocation writes `KW` caps
  (`CnK`), a set-handler cap is `KW` (a notification cap), and the invocation is **no** untyped, SchedControl,
  IRQ-control or arch invocation (`False` there). `okd_fl4Decode_ck`: the decoded cap is a slot cap of a `CKI`
  state, so `KW`, so `fl4_decode_invocation` takes none of the untyped / SchedControl / IRQ-control / arch
  branches; the CNode decode reads `KW` slot caps and derives / masks / badges them (`kw_deriveCap`,
  `kw_maskCap`, `kw_updateCapData`).
* The performs (`ck_fl4Perform`: the excluded invocations by `InvK`, the CNode / IRQ-handler ones by their
  caps, the rest by `hv_auto`), the shell `ck_handleInvocationR`, the syscalls, every event.
* **`ck_fl4KernelEntrySyscall`** / **`ck_fl4CallKernel`**: `CKI` across `fl4KernelEntrySyscall rep c` /
  `fl4CallKernel rep ev` (every event), no side condition. **`kentry_cki`**, **`kcall_cki`** (the statements
  over outcomes).

Named premises: none. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JCkX
open Classical

namespace Fl4Proofs.P3.SInvCk
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvV Fl4Proofs.P3.SInvDom Fl4Proofs.P3.SInvIo

noncomputable section

set_option maxHeartbeats 4000000

/-! ## The decode's carry -/

/-- The caps a CNode invocation writes are `KW`. -/
def CnK (i : CnodeInvocation) : Prop :=
  match i with
  | .insertCall c _ _ => KW c
  | .moveCall c _ _ => KW c
  | .rotateCall c1 c2 _ _ _ => KW c1 ∧ KW c2
  | _ => True

/-- **The decode's carry** (module docstring). -/
def InvK (inv : Fl4Invocation) : Prop :=
  match inv with
  | .invokeCNode i => CnK i
  | .invokeIRQHandler (.setIRQHandler _ c _) => KW c
  | .invokeUntyped _ => False
  | .invokeSchedControl _ => False
  | .invokeIRQControl _ => False
  | .invokeArchObject _ => False
  | _ => True

theorem okv_getCap_ck {σ0 : State Unit} (hv : CKI σ0) (sl : CslotPtr) :
    OkV σ0 (fun c => KW c) (NonDetE.liftE (ε := SyscallError) (getCap (Z := Unit) sl)) := by
  intro s hs a s' h
  obtain ⟨y, hy, e⟩ := mem_liftE_inv' h
  simp only [Prod.mk.injEq, Except.ok.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  obtain ⟨o, r⟩ := sl
  obtain ⟨e1, e2⟩ := vih_mem_getCap hy
  rw [e1]
  exact ⟨hs, kw_of_slot (cki_of_hV hs hv) e2⟩

theorem okv_deriveCap_ck {σ0 : State Unit} (sl : CslotPtr) (c : Cap) (hc : KW c) :
    OkV σ0 (fun c' => KW c') (deriveCap (Z := Unit) sl c) := by
  intro s hs a s' h
  have e : hV s' = hV s := hv_deriveCap (P := fun x => hV x = hV s) _ _ s rfl _ h
  exact ⟨e.trans hs, kw_deriveCap hc h⟩

macro "ck_cn_close" : tactic => `(tactic| first
  | assumption
  | (refine kw_updateCapData (kw_maskCap ?_ _) _ _; assumption)
  | (refine kw_maskCap ?_ _; assumption)
  | (refine kw_updateCapData ?_ _ _; assumption)
  | (split <;> first
      | assumption
      | (refine kw_updateCapData (kw_maskCap ?_ _) _ _; assumption)
      | (refine kw_maskCap ?_ _; assumption)
      | (refine kw_updateCapData ?_ _ _; assumption)))

set_option maxHeartbeats 8000000 in
theorem okv_decodeCnode_ck {σ0 : State Unit} (hv : CKI σ0) (label : Data) (args : List Data)
    (cap : Cap) (excaps : List Cap) :
    OkV σ0 (fun i => CnK i) (decodeCnodeInvocation (Z := Unit) label args cap excaps) := by
  unfold decodeCnodeInvocation
  repeat' (first
    | (refine okv_bind (okv_getCap_ck hv _) fun c0 hc0 => ?_)
    | (refine okv_bind (okv_ite_app _ (okv_returnOk ?_) (okv_deriveCap_ck _ _ ?_)) fun c1 hc1 => ?_)
    | okv_step)
  all_goals first
    | (refine okv_returnOk ?_; simp only [CnK]; ck_cn_close; done)
    | (refine okv_returnOk ?_; simp only [CnK]; constructor <;> ck_cn_close; done)
    | ck_cn_close

theorem okd_decodeCnode_ck (label : Data) (args : List Data) (cap : Cap) (excaps : List Cap) (s : State Unit) :
    OkDAt s (fun s' i => hV s' = hV s ∧ (CKI s → CnK i)) (decodeCnodeInvocation (Z := Unit) label args cap excaps) := by
  intro a s' h
  have e : hV s' = hV s := hv_decodeCnodeInvocation (P := fun x => hV x = hV s) _ _ _ _ s rfl _ h
  exact ⟨e, fun hs => (okv_decodeCnode_ck hs label args cap excaps s rfl a s' h).2⟩

theorem kw_of_ntfn {c : Cap} {P : Prop} (h : isNtfnCap c ∧ P) : KW c := by
  cases c <;> simp_all [isNtfnCap, KW]

theorem okd_decodeIrqHandler_ck (label : Data) (irq : Irq) (cps : List (Cap × CslotPtr)) (s : State Unit) :
    OkDAt s (fun _ v => InvK (.invokeIRQHandler v)) (decodeIrqHandlerInvocation (Z := Unit) label irq cps) := by
  unfold decodeIrqHandlerInvocation
  repeat' (first
    | exact okdAt_throw _
    | exact okdAt_returnOk trivial
    | exact okdAt_returnOk (kw_of_ntfn (by assumption))
    | split)

set_option maxHeartbeats 8000000 in
/-- **The decode of a `KW` cap at a `CKI` state yields `InvK`.** -/
theorem okd_fl4Decode_ck (fp : Bool) (label : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr) (cap : Cap)
    (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) (s0 : State Unit) (h0 : CKI s0) (hk : KW cap)
    (σ : State Unit) :
    OkDAt σ (fun s' inv => hV s' = hV s0 → InvK inv)
      (fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex buf) := by
  cases cap with
  | untypedCap => exact hk.elim
  | schedControlCap => exact hk.elim
  | irqControlCap => exact hk.elim
  | archObjectCap a => exact hk.elim
  | cnodeCap p b g =>
    simp only [fl4DecodeInvocation]
    split
    · exact okdAt_throw _
    · exact okdAt_liftME fun a s' h e0 => by
        obtain ⟨e, hc⟩ := okd_decodeCnode_ck label args _ _ σ a s' h
        exact hc (cki_of_hV (e.symm.trans e0) h0)
  | irqHandlerCap irq =>
    simp only [fl4DecodeInvocation]
    exact okdAt_liftME fun a s' h _ => okd_decodeIrqHandler_ck _ _ _ σ a s' h
  | _ =>
    simp only [fl4DecodeInvocation]
    all_goals try unfold fl4DecodeTcbInvocation
    all_goals repeat' (first
      | exact okdAt_throw _
      | exact okdAt_returnOk (fun _ => trivial)
      | exact okdAt_liftME (fun _ _ _ _ => trivial)
      | exact okdAt_pure' (fun _ => trivial)
      | (apply okdAt_ite)
      | (refine okdAt_bind fun _ _ _ => ?_)
      | split)

/-! ## The performs -/

theorem ck_invokeCnode (i : CnodeInvocation) (hc : CnK i) : IKHE (ε := Unit) CKI (invokeCnode (Z := Unit) i) := by
  cases i with
  | insertCall c s d => exact ike_liftE (ck_capInsert c s d hc)
  | moveCall c s d => exact ike_liftE (ck_capMove c s d hc)
  | rotateCall c1 c2 s1 s2 s3 =>
    simp only [invokeCnode]
    split
    · exact ike_liftE (ck_capSwap _ _ _ _ hc.1 hc.2)
    · exact ike_liftE (ik_bind (ck_capMove _ _ _ hc.2) fun _ => ck_capMove _ _ _ hc.1)
  | revokeCall s => exact ck_capRevoke s
  | deleteCall s => exact ck_capDelete s
  | cancelBadgedSendsCall c =>
    simp only [invokeCnode]; split <;> (try (exfalso; simp_all; done)) <;> hv_auto

theorem ck_invokeIrqHandler (i : IrqHandlerInvocation) (hc : InvK (.invokeIRQHandler i)) :
    IKH CKI (invokeIrqHandler (Z := Unit) i) := by
  cases i with
  | setIRQHandler irq c sl =>
    have hc' : KW c := hc
    simp only [invokeIrqHandler]
    exact ik_bind (hv_getIrqSlot _) fun s => ik_bind (ck_capDeleteOne s) fun _ => ck_capInsert c sl s hc'
  | _ => simp only [invokeIrqHandler]; hv_auto

set_option maxHeartbeats 16000000 in
theorem ck_fl4Perform (blk call don : Bool) (inv : Fl4Invocation) (hc : InvK inv) :
    IKHE (ε := Unit) CKI (fl4PerformInvocation (Z := Unit) blk call don inv) := by
  cases inv with
  | invokeUntyped _ => exact hc.elim
  | invokeSchedControl _ => exact hc.elim
  | invokeIRQControl _ => exact hc.elim
  | invokeArchObject _ => exact hc.elim
  | invokeCNode i =>
    simp only [fl4PerformInvocation]
    exact ike_bind (ck_invokeCnode i hc) fun _ => ike_returnOk _
  | invokeIRQHandler i =>
    simp only [fl4PerformInvocation]
    exact ike_bind (ike_liftE (ck_invokeIrqHandler i hc)) fun _ => ike_returnOk _
  | _ => simp only [fl4PerformInvocation]; hv_auto

/-! ## The invocation shell -/

set_option maxHeartbeats 16000000 in
/-- **The invocation keeps `CKI`.** -/
theorem ck_handleInvocationR (rep calling blocking don fp : Bool) (cptr : CapRef) :
    IKHE (ε := Unit) CKI (fl4HandleInvocationR (Z := Unit) rep calling blocking don fp cptr) := by
  unfold fl4HandleInvocationR
  refine ike_bind (by hv_auto) fun thread => ike_bind (by hv_auto) fun info => ?_
  intro σ hs y hy
  have h1 : ∀ w ∈ ((ExceptT.run (do
       let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot (Z := Unit) thread cptr
       let buffer ← NonDetE.liftE <| lookupIpcBuffer false thread
       let extracaps ← lookupExtraCaps thread buffer info
       NonDetE.returnOk (slot, cap, extracaps, buffer))) σ).1, CKI w.2 :=
    fun w hw => (by hv_auto : IKHE (ε := Fault) CKI _) σ hs w hw
  refine syscall_post' (I := CKI) (Q := CKI) h1 ?_ ?_ ?_ ?_ y hy
  · intro f s hs v hv; exact (by hv_auto : IKH CKI _) s hs v hv
  · intro a s has w hw
    obtain ⟨sl, cap, ex, buf⟩ := a
    exact (by hv_auto : IKHE CKI _) s (h1 _ has) w hw
  · intro e s hs v hv; exact (by hv_auto : IKH CKI _) s hs v hv
  · intro a s b s' has hbs hI y hy
    obtain ⟨sl, cap, ex, buf⟩ := a
    have hcap : capOpt (s.kheap sl.1) sl.2 = some cap := okCap_front thread cptr info σ _ s has
    have hCs : CKI s := h1 _ has
    have hk : KW cap := kw_of_slot hCs hcap
    have eE : hV s' = hV s := (by hv_auto : IKHE (fun x => hV x = hV s) _) s rfl _ hbs
    have hd : InvK b :=
      okdAt_bind (fun _ s1 _ => okd_fl4Decode_ck _ _ _ _ _ _ _ _ s hCs hk s1) b s' hbs eE
    obtain ⟨z, hz, ⟨u, hu, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE_inv' hy
    · have hz1 : CKI z.2 := (by hv_auto : IKHE (ε := Unit) CKI
        (withoutPreemption (Z := Unit) (setThreadState thread .restart))) s' hI z hz
      obtain ⟨r, s1⟩ := z
      simp only at hu; subst hu
      obtain ⟨z2, hz2, ⟨rp, hr, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE_inv' hy
      · obtain ⟨r2, s2⟩ := z2
        simp only at hr; subst hr
        have hs2 := ck_fl4Perform blocking calling don b hd s1 hz1 _ hz2
        exact (by hv_auto : IKHE CKI _) s2 hs2 y hy
      · exact ck_fl4Perform blocking calling don b hd s1 hz1 _ hz2
    · exact (by hv_auto : IKHE (ε := Unit) CKI
        (withoutPreemption (Z := Unit) (setThreadState thread .restart))) s' hI z hz

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact ck_handleInvocationR _ _ _ _ _ _)

/-! ## The kernel entry -/

set_option maxHeartbeats 8000000 in
theorem ck_fl4HandleSyscall (rep : Bool) (c : Syscall) : IKHE (ε := Unit) CKI (fl4HandleSyscall (Z := Unit) rep c) := by
  cases c <;> simp only [fl4HandleSyscall] <;> hv_auto

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact ck_fl4HandleSyscall _ _)

set_option maxHeartbeats 8000000 in
theorem ck_handleEvent_other (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) :
    IKHE (ε := Unit) CKI (handleEvent (Z := Unit) ev) := by
  cases ev with
  | syscallEvent c => exact absurd rfl (h c)
  | _ => simp only [handleEvent]; hv_auto

set_option maxHeartbeats 4000000 in
theorem ck_fl4HandleEvent (rep : Bool) (ev : Event) : IKHE (ε := Unit) CKI (fl4HandleEvent (Z := Unit) rep ev) := by
  by_cases h : ∃ c, ev = .syscallEvent c
  · obtain ⟨c, rfl⟩ := h
    simp only [fl4HandleEvent]
    hv_auto
  · rw [fl4HandleEvent_other rep ev fun c e => h ⟨c, e⟩]
    exact ck_handleEvent_other ev fun c e => h ⟨c, e⟩

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact ck_fl4HandleEvent _ _)

/-- **`fl4CallKernel` keeps `CKI`, for every event.** -/
theorem ck_fl4CallKernel (rep : Bool) (ev : Event) : IKH CKI (fl4CallKernel (Z := Unit) rep ev) := by
  unfold fl4CallKernel; hv_auto

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact ck_fl4CallKernel _ _)

/-- **The syscall entry keeps `CKI`.** -/
theorem ck_fl4KernelEntrySyscall (rep : Bool) (c : Syscall) :
    IKH CKI (fl4KernelEntrySyscall (Z := Unit) rep c) := by
  unfold fl4KernelEntrySyscall; hv_auto

/-- **`CKI` across the syscall entry** (every outcome). -/
theorem kentry_cki (rep : Bool) (c : Syscall) {σ : State Unit} (h : CKI σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) rep c) σ).1, CKI y.2 :=
  fun y hy => ck_fl4KernelEntrySyscall rep c σ h y hy

/-- **`CKI` across every kernel event** (`fl4CallKernel rep ev`). -/
theorem kcall_cki (rep : Bool) (ev : Event) {σ : State Unit} (h : CKI σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, CKI y.2 :=
  fun y hy => ck_fl4CallKernel rep ev σ h y hy

end

end Fl4Proofs.P3.SInvCk
