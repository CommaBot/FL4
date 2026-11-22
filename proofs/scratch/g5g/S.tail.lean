/-! ## The performs -/

/-- **The remaining obligation** (module docstring; not an invariant premise):
the untyped perform keeps `ZR` for an invocation decoded from the state's view. -/
def PerfGapZ : Prop :=
  ∀ (N : Irq → ObjRef) (ui : UntypedInvocation) (σ : State Unit), P3 N σ → NodeIs N σ → ZR σ →
    DecodedFrom (uV σ) (.invokeUntyped ui) → ∀ y ∈ ((fl4InvokeUntyped (Z := Unit) ui).run σ).1, ZR y.2

variable {N : Irq → ObjRef}

set_option maxHeartbeats 8000000 in
theorem zr_fl4Perform (hG : PerfGapZ) (blk call don : Bool) (inv : Fl4Invocation) (σ : State Unit)
    (hP : P3 N σ) (hN : NodeIs N σ) (hZ : ZR σ) (hI : InvZ (uV σ) inv) (hD : DecodedFrom (uV σ) inv) :
    ∀ y ∈ ((fl4PerformInvocation (Z := Unit) blk call don inv).run σ).1, ZR y.2 := by
  intro y hy
  cases inv with
  | invokeUntyped ui =>
    simp only [fl4PerformInvocation] at hy
    obtain ⟨z, hz, ⟨u, hu, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
    · obtain rfl := Set.mem_singleton_iff.1 hy
      exact hG N ui σ hP hN hZ hD z hz
    · exact hG N ui σ hP hN hZ hD z hz
  | invokeFl4TCB i =>
    simp only [fl4PerformInvocation] at hy
    exact zr_invokeFl4Tcb i σ hZ hP.1.2.2.2.1 hI y hy
  | _ => exact (show IKHE (ε := Unit) ZR (fl4PerformInvocation (Z := Unit) blk call don _) from by
      simp only [fl4PerformInvocation]; zr_auto) σ hZ y hy

/-! ## The invocation shell -/

/-- `ZR` kept from a `P3 N ∧ NodeIs N ∧ ZR` state. -/
def IKZ {α : Type} (m : NonDet (State Unit) α) : Prop :=
  ∀ (N : Irq → ObjRef) σ, P3 N σ → NodeIs N σ → ZR σ → ∀ y ∈ (m σ).1, ZR y.2

abbrev IKZE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := IKZ (ExceptT.run m)

theorem ikz_of_ik {α : Type} {m : NonDet (State Unit) α} (h : IKH ZR m) : IKZ m :=
  fun _ σ _ _ hZ y hy => h σ hZ y hy

theorem ikze_bind_uk {ε α β : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β}
    (hm : ∀ v, UKE v m) (hmN : ∀ N, NKE N m) (hmZ : IKHE ZR m) (hg : ∀ a, IKZE (g a)) : IKZE (m >>= g) := by
  intro N σ hI hN hZ y hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
  · exact hg a N z.2 (p3_of_view (hm (uV σ) σ rfl z hz) hI) (hmN N σ hN z hz) (hmZ σ hZ z hz) y hy
  · exact hmZ σ hZ z hz

theorem ikze_bind {ε α β : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β}
    (hm : IKZE m) (hg : ∀ a, IKHE ZR (g a)) : IKZE (m >>= g) := by
  intro N σ hI hN hZ y hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
  · exact hg a z.2 (hm N σ hI hN hZ z hz) y hy
  · exact hm N σ hI hN hZ z hz

theorem ikz_bind_post {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β}
    (hm : IKZ m) (hg : ∀ a, IKH ZR (g a)) : IKZ (m >>= g) := by
  intro N σ hI hN hZ y ⟨x, hx, hy⟩
  exact hg x.1 x.2 (hm N σ hI hN hZ x hx) y hy

set_option maxHeartbeats 8000000 in
/-- **The invocation keeps `ZR`** (given `PerfGapZ`; ut7's `p3N_handleInvocationR` with `ZR`). -/
theorem zr_handleInvocationR (hG : PerfGapZ) (rep calling blocking don fp : Bool) (cptr : CapRef) :
    IKZE (fl4HandleInvocationR (Z := Unit) rep calling blocking don fp cptr) := by
  unfold fl4HandleInvocationR
  refine ikze_bind_uk (fun _ => by uk_auto) (fun _ => by nk_auto) (by zr_auto) fun thread =>
    ikze_bind_uk (fun _ => by uk_auto) (fun _ => by nk_auto) (by zr_auto) fun info => ?_
  intro N σ hI hN hZ y hy
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
  have hFZ : IKHE (ε := Fault) ZR (do
       let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot (Z := Unit) thread cptr
       let buffer ← NonDetE.liftE <| lookupIpcBuffer false thread
       let extracaps ← lookupExtraCaps thread buffer info
       NonDetE.returnOk (slot, cap, extracaps, buffer)) := by zr_auto
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
  refine syscall_postU (I := fun s => ZR s ∧ P3 N s ∧ uV s = uV σ ∧ NodeIs N s) (Q := ZR)
    (fun w hw => ⟨hFZ σ hZ w hw, p3_of_view (hF _ σ rfl w hw) hI, hF _ σ rfl w hw, hFN σ hN w hw⟩) ?_ ?_ ?_ ?_ y hy
  · intro f s hs v hv
    exact (show IKH ZR (NonDet.when blocking (handleFault thread f)) by zr_auto) s hs.1 v hv
  · intro a s has w hw
    have hs : ZR s ∧ P3 N s ∧ uV s = uV σ ∧ NodeIs N s :=
      ⟨hFZ σ hZ _ has, p3_of_view (hF _ σ rfl _ has) hI, hF _ σ rfl _ has, hFN σ hN _ has⟩
    obtain ⟨sl, cap, ex, buf⟩ := a
    have hE : ∀ v, UKE v (do
        let args ← NonDetE.liftE <| getMrs (Z := Unit) thread buf info
        fl4DecodeInvocation fp info.miLabel args cptr sl cap ex buf) := fun _ => by uk_auto
    have hEN : NKE N (do
        let args ← NonDetE.liftE <| getMrs (Z := Unit) thread buf info
        fl4DecodeInvocation fp info.miLabel args cptr sl cap ex buf) := by nk_auto
    have hEZ : IKHE ZR (do
        let args ← NonDetE.liftE <| getMrs (Z := Unit) thread buf info
        fl4DecodeInvocation fp info.miLabel args cptr sl cap ex buf) := by zr_auto
    exact ⟨hEZ s hs.1 w hw, p3_of_view (hE _ s rfl w hw) hs.2.1, (hE _ s rfl w hw).trans hs.2.2.1,
      hEN s hs.2.2.2 w hw⟩
  · intro e s hs v hv
    exact (show IKH ZR _ by zr_auto) s hs.1 v hv
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
    have hdec : InvZ (uV σ) b :=
      okv_fl4Decode_z fp info.miLabel x0.1 cptr sl cap ex buf (fun p hp => (hex p hp).1) x0.2 hvx b s' hb0
    have hDF : DecodedFrom (uV σ) b := ⟨fp, info.miLabel, x0.1, cptr, sl, cap, ex, buf, x0.2, s', hvx, hc, hex, hb0⟩
    obtain ⟨z, hz, ⟨u, hu, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
    · have hz' : uV z.2 = uV s' := (show ∀ v, UKE v (withoutPreemption (Z := Unit) (setThreadState thread .restart))
        from fun _ => by uk_auto) _ s' rfl z hz
      have hzN : NodeIs N z.2 := (show NKE N (withoutPreemption (Z := Unit) (setThreadState thread .restart))
        by nk_auto) s' hI'.2.2.2 z hz
      have hzZ : ZR z.2 := (show IKHE (ε := Unit) ZR (withoutPreemption (Z := Unit) (setThreadState thread .restart))
        by zr_auto) s' hI'.1 z hz
      obtain ⟨r, s1⟩ := z
      simp only at hu; subst hu
      have hv1 : uV s1 = uV σ := hz'.trans hI'.2.2.1
      have hI1 : P3 N s1 := p3_of_view hz' hI'.2.1
      have hok1 : InvZ (uV s1) b := by rw [hv1]; exact hdec
      have hDF1 : DecodedFrom (uV s1) b := by rw [hv1]; exact hDF
      obtain ⟨z2, hz2, ⟨rp, hr, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
      · obtain ⟨r2, s2⟩ := z2
        simp only at hr; subst hr
        have hs2 := zr_fl4Perform hG blocking calling don b s1 hI1 hzN hzZ hok1 hDF1 _ hz2
        exact (show IKHE ZR _ by zr_auto) s2 hs2 y hy
      · exact zr_fl4Perform hG blocking calling don b s1 hI1 hzN hzZ hok1 hDF1 _ hz2
    · exact (show IKHE (ε := Unit) ZR (withoutPreemption (Z := Unit) (setThreadState thread .restart))
        by zr_auto) s' hI'.1 z hz

/-! ## The syscall paths and events -/

set_option maxHeartbeats 8000000 in
theorem zr_fl4HandleSyscall (hG : PerfGapZ) (rep : Bool) (c : Syscall) : IKZE (fl4HandleSyscall (Z := Unit) rep c) := by
  cases c <;> simp only [fl4HandleSyscall]
  all_goals first
    | exact ikze_bind_uk (fun _ => by uk_auto) (fun _ => by nk_auto) (by zr_auto) fun _ =>
        zr_handleInvocationR hG _ _ _ _ _ _
    | exact ikze_bind_uk (fun _ => by uk_auto) (fun _ => by nk_auto) (by zr_auto) fun _ =>
        ikze_bind (zr_handleInvocationR hG _ _ _ _ _ _) fun _ => by zr_auto
    | exact ikz_of_ik (by zr_auto)

set_option maxHeartbeats 4000000 in
theorem zr_handleEvent_other (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) :
    IKHE (ε := Unit) ZR (handleEvent (Z := Unit) ev) := by
  cases ev with
  | syscallEvent c => exact absurd rfl (h c)
  | _ => simp only [handleEvent]; zr_auto

set_option maxHeartbeats 4000000 in
theorem zr_fl4HandleEvent (hG : PerfGapZ) (rep : Bool) (ev : Event) : IKZE (fl4HandleEvent (Z := Unit) rep ev) := by
  by_cases h : ∃ c, ev = .syscallEvent c
  · obtain ⟨c, rfl⟩ := h
    simp only [fl4HandleEvent]
    refine ikze_bind_uk (fun _ => ike_liftE (uk_updateTimeStamp)) (fun _ => by nk_auto) (by zr_auto) fun _ => ?_
    intro N σ hI hN hZ y hy
    obtain ⟨z, hz, ⟨r, hr, hy⟩ | ⟨e, he, rfl⟩⟩ := mem_bindE' hy
    · obtain ⟨x, hx, rfl⟩ := mem_liftE' hz
      simp only [Except.ok.injEq] at hr; subst hr
      have hIx : P3 N x.2 := un_checkBudgetRestart σ hI x hx
      have hNx : NodeIs N x.2 := (show NK N (checkBudgetRestart (Z := Unit)) by nk_auto) σ hN x hx
      have hZx : ZR x.2 := (show IKH ZR (checkBudgetRestart (Z := Unit)) by zr_auto) σ hZ x hx
      unfold NonDetE.whenE at hy
      split at hy
      · exact zr_fl4HandleSyscall hG rep c N x.2 hIx hNx hZx y hy
      · rw [Set.mem_singleton_iff.1 hy]; exact hZx
    · obtain ⟨x, hx, rfl⟩ := mem_liftE' hz; cases he
  · rw [fl4HandleEvent_other rep ev fun c e => h ⟨c, e⟩]
    exact ikz_of_ik (zr_handleEvent_other ev fun c e => h ⟨c, e⟩)

set_option maxHeartbeats 4000000 in
theorem zr_fl4CallKernel (hG : PerfGapZ) (rep : Bool) (ev : Event) : IKZ (fl4CallKernel (Z := Unit) rep ev) := by
  unfold fl4CallKernel
  refine ikz_bind_post ?_ fun _ => by zr_auto
  intro N σ hI hN hZ x hx
  unfold NonDetE.handleE at hx
  rw [ExceptT.run_mk] at hx
  obtain ⟨z, hz, hx⟩ := hx
  have hz' := zr_fl4HandleEvent hG rep ev N σ hI hN hZ z hz
  obtain ⟨r, s⟩ := z
  cases r with
  | ok a => rw [Set.mem_singleton_iff.1 hx]; exact hz'
  | error e => exact (show IKHE (ε := Unit) ZR (withoutPreemption (Z := Unit) preemptionPath) by zr_auto) s hz' x hx

/-! ## Tops -/

theorem zr_fl4SyscallFaultIP (t : ObjRef) : IKH ZR (fl4SyscallFaultIP (Z := Unit) t) := by
  unfold fl4SyscallFaultIP; zr_auto

set_option maxHeartbeats 4000000 in
theorem zr_kentry (hG : PerfGapZ) (c : Syscall) : IKZ (fl4KernelEntrySyscall (Z := Unit) true c) := by
  unfold fl4KernelEntrySyscall
  intro N σ hI hN hZ y hy
  obtain ⟨x, hx, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hx] at hy
  obtain ⟨x1, hx1, hy⟩ := hy
  exact zr_fl4CallKernel hG true _ N x1.2 (p3_of_view (uk_mem (fun _ => uk_fl4SyscallFaultIP _) hx1) hI)
    (nk_fl4SyscallFaultIP _ σ hN x1 hx1) (zr_fl4SyscallFaultIP _ σ hZ x1 hx1)
    y hy

/-- **`ZR` across the syscall entry, given `PerfGapZ`** (`UtInv3`: the carried
untyped invariant, `SInvA.ut`). -/
theorem kentry_zr_of (hG : PerfGapZ) (c : Syscall) {σ : State Unit} (hU : UtInv3 σ) (hZ : ZR σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, ZR y.2 :=
  zr_kentry hG c σ.interruptIrqNode σ (utInv3_iff.1 hU) rfl hZ

/-- **`ZR` across every kernel event, given `PerfGapZ`.** -/
theorem kcall_zr_of (hG : PerfGapZ) (rep : Bool) (ev : Event) {σ : State Unit} (hU : UtInv3 σ) (hZ : ZR σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, ZR y.2 :=
  zr_fl4CallKernel hG rep ev σ.interruptIrqNode σ (utInv3_iff.1 hU) rfl hZ

/-- **`ZR` across the non-syscall events, with no premise** (they reach no perform). -/
theorem kcall_zr_other (rep : Bool) (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) {σ : State Unit} (hZ : ZR σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, ZR y.2 := by
  intro y hy
  unfold fl4CallKernel at hy
  refine (ik_bind ?_ fun _ => by zr_auto) σ hZ y hy
  refine ike_handleE ?_ fun _ => by zr_auto
  rw [fl4HandleEvent_other rep ev h]
  exact zr_handleEvent_other ev h

end

end Fl4Proofs.P3.SInvUZ
