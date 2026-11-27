/-
P3x for virtualization, spec side (line virt, gen 6; proofs/VIRT-PLAN.md §10, table row "NoVirt reachability"):
**`NR` (no virtualization cap, no VCPU object, no thread running a VM) is kept by the whole ported kernel step**
off the three virtualization routes at `virtKind = none`, and so `fl4CallKernelV_eqNR5` applies along every run.

* The decoder's carry (vih3's `okd_fl4Decode` for `InvNV`, VirtNvInv): `nv_maskCap`, `nv_updateCapData`,
  `okn_getCap`, `okv_decodeCnode_nv` / `okd_decodeCnode_nv` (the copied / minted / moved / rotated caps are read
  from slots of an `NVC` state), `okd_decodeIrqHandler_nv` (the set-handler cap is a notification cap),
  `okd_dataToObjType_vtx` / `okd_decodeUntypedVtx` (a VT-x type comes only from the numbers 14..18, i.e. from the
  VT-x gate's inputs), `okd_fl4DecodeTcb_invNV`, **`okd_fl4Decode_invNV`**.
* The shell: `post_bindE`, `liftE_no_err`, **`nr_handleInvocationR`** (the decode point off `Route3`, the carry
  from the decode to the perform: `InvNV`, VirtNvK1's `InvTcbNV` and `UnmapOK`), `nr_invoke`, `nr_invoke0`,
  `nr_fl4HandleSyscall`, `nr_fl4HandleEvent`, **`nr_fl4CallKernel`**.
* Runs: `RunNR` (a sequence of kernel steps, each event off the routes at its state), **`runNR_nr`** (every state
  of such a run from an `NR` state is `NR`), **`runNR_eqV`** (at every step of it `fl4CallKernelV = fl4CallKernel`,
  VirtTcbOK's `fl4CallKernelV_eqNR5`), `nr_boot` (`NoVirtCaps ∧ NoVirtObjects ∧ NoRunVM` gives `NR`).

Named premises:
* **`hvk : virtKind = .none` [S]** (route scope, as VirtInvOK / VirtTcbOK).
* **`hr5 : ∀ c, ev = .syscallEvent c → ∀ t, EntryPt σ t → OffRouteS5 c t` [S]** (VirtTcbOK): the event's decode
  points are off the three routes; the on-route entries are covered by the route-B posts.

No [J]/[P]/[W]. New file only.
-/
import Fl4Proofs.P3.VirtNvK1
import Fl4Proofs.P3.VirtTyK7
open Classical

namespace Fl4Proofs.P3.VirtNvK2
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvV Fl4Proofs.P3.SInvL Fl4Proofs.P3.SInvDom
  Fl4Proofs.P3.SInvTY Fl4Proofs.P3.VirtR7b Fl4Proofs.P3.VirtR7d Fl4Proofs.P3.VirtR7e Fl4Proofs.P3.VirtR7eK
  Fl4Proofs.P3.VirtNvTcb Fl4Proofs.P3.VirtNvcW Fl4Proofs.P3.VirtOffNv Fl4Proofs.P3.VirtInvOK
  Fl4Proofs.P3.VirtTcbOK Fl4Proofs.P3.VirtNvInv Fl4Proofs.P3.VirtNvK1 Fl4Proofs.P3.VirtTyK7

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

/-! ## The decoder's carry -/

theorem nv_maskCap {c : Cap} (h : ¬ IsVirtCap c) (r : CapRights) : ¬ IsVirtCap (maskCap r c) := by
  intro h'; apply h
  cases c with
  | archObjectCap a =>
    cases a with
    | pageCap d p R mt sz m => cases mt <;> simp_all [maskCap, capRightsUpdate, acapRightsUpdate, IsVirtCap]
    | _ => simp_all [maskCap, capRightsUpdate, acapRightsUpdate, IsVirtCap]
  | _ => simp_all [maskCap, capRightsUpdate, IsVirtCap]

theorem nv_updateCapData {c : Cap} (h : ¬ IsVirtCap c) (p : Bool) (w : Data) :
    ¬ IsVirtCap (updateCapData p w c) := by
  intro h'; apply h
  unfold updateCapData at h'
  split_ifs at h' with h1 h2 h3 h4 h5 h6 h7
  all_goals first
    | (simp [IsVirtCap] at h'; done)
    | (cases c <;> simp_all [badgeUpdate, isEpCap, isNtfnCap, IsVirtCap]; done)
    | (dsimp only at h'; split_ifs at h' <;> simp [IsVirtCap] at h'; done)
    | (cases c <;> simp_all [archUpdateCapData, isArchCap, Cap.theArchCap, IsVirtCap]; done)
    | exact h'

theorem okn_getCap {σ0 : State Unit} (hv : NVC σ0) (sl : CslotPtr) :
    OkV σ0 (fun c => ¬ IsVirtCap c) (NonDetE.liftE (ε := SyscallError) (getCap (Z := Unit) sl)) := by
  intro s hs a s' h
  obtain ⟨y, hy, e⟩ := mem_liftE_inv' h
  simp only [Prod.mk.injEq, Except.ok.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  obtain ⟨o, r⟩ := sl
  obtain ⟨e1, e2⟩ := vih_mem_getCap hy
  rw [e1]
  exact ⟨hs, (hv.view hs) (o, r) _ e2⟩

set_option maxHeartbeats 4000000 in
theorem okv_decodeCnode_nv {σ0 : State Unit} (hv : NVC σ0) (label : Data) (args : List Data) (cap : Cap)
    (excaps : List Cap) :
    OkV σ0 (fun i => CnNV i) (decodeCnodeInvocation (Z := Unit) label args cap excaps) := by
  unfold decodeCnodeInvocation
  repeat' (first
    | (refine okv_bind (okn_getCap hv _) fun c0 hc0 => ?_)
    | (refine okv_bind (okv_ite_app _ (okv_returnOk ?_) (okn_deriveCap _ _ ?_)) fun c1 hc1 => ?_)
    | exact okv_returnOk (by split <;> (simp only [CnNV]; assumption))
    | exact okv_returnOk ⟨nv_updateCapData (by assumption) _ _, nv_updateCapData (by assumption) _ _⟩
    | exact okv_throw _
    | exact okv_returnOk trivial
    | (refine okv_returnOk_bind ?_)
    | (refine okv_bind (okv_frame fun v => by hv_auto) fun _ _ => ?_)
    | (apply okv_ite)
    | split)
  all_goals first
    | (split <;> exact nv_updateCapData (nv_maskCap (by assumption) _) _ _)
    | exact nv_updateCapData (nv_maskCap (by assumption) _) _ _
    | exact nv_maskCap (by assumption) _

theorem okd_decodeCnode_nv {σ : State Unit} (hv : NVC σ) (label : Data) (args : List Data) (cap : Cap)
    (excaps : List Cap) :
    OkDAt σ (fun _ i => InvNV (.invokeCNode i)) (decodeCnodeInvocation (Z := Unit) label args cap excaps) :=
  fun a s' h => (okv_decodeCnode_nv hv label args cap excaps σ rfl a s' h).2

theorem ntfn_nv {c : Cap} (h : isNtfnCap c = true) : ¬ IsVirtCap c := by
  cases c <;> simp_all [isNtfnCap, IsVirtCap]

theorem okd_decodeIrqHandler_nv (label : Data) (irq : Irq) (cps : List (Cap × CslotPtr)) (s : State Unit) :
    OkDAt s (fun _ v => InvNV (.invokeIRQHandler v)) (decodeIrqHandlerInvocation (Z := Unit) label irq cps) := by
  unfold decodeIrqHandlerInvocation
  repeat' (first
    | exact okdAt_throw _
    | exact okdAt_returnOk trivial
    | (refine okdAt_returnOk (ntfn_nv ?_); simp_all; done)
    | split)

theorem archDataToObjType_vtx {k : Nat} {tp : AObjectType} (h : archDataToObjType k = some tp)
    (hv : VtxTy (.archObject tp)) : 7 ≤ k ∧ k ≤ 11 := by
  unfold archDataToObjType at h
  split_ifs at h <;> cases h <;> first | omega | (simp [VtxTy] at hv)

/-- `data_to_obj_type` returns a VT-x type only for 14..18. -/
theorem okd_dataToObjType_vtx (type : Data) (σ : State Unit) :
    OkDAt σ (fun _ t => VtxTy t → isVtxObjectTypeNum (dataToNat type) = true)
      (dataToObjType (Z := Unit) type) := by
  unfold dataToObjType
  refine okdAt_returnOk_bind ?_
  by_cases h0 : dataToNat type = 0
  · rw [if_pos h0]; exact okdAt_returnOk (fun h => by simp [VtxTy] at h)
  rw [if_neg h0]
  by_cases h1 : dataToNat type = 1
  · rw [if_pos h1]; exact okdAt_returnOk (fun h => by simp [VtxTy] at h)
  rw [if_neg h1]
  by_cases h2 : dataToNat type = 2
  · rw [if_pos h2]; exact okdAt_returnOk (fun h => by simp [VtxTy] at h)
  rw [if_neg h2]
  by_cases h3 : dataToNat type = 3
  · rw [if_pos h3]; exact okdAt_returnOk (fun h => by simp [VtxTy] at h)
  rw [if_neg h3]
  by_cases h4 : dataToNat type = 4
  · rw [if_pos h4]; exact okdAt_returnOk (fun h => by simp [VtxTy] at h)
  rw [if_neg h4]
  by_cases h5 : dataToNat type = 5
  · rw [if_pos h5]; exact okdAt_returnOk (fun h => by simp [VtxTy] at h)
  rw [if_neg h5]
  by_cases h6 : dataToNat type = 6
  · rw [if_pos h6]; exact okdAt_returnOk (fun h => by simp [VtxTy] at h)
  rw [if_neg h6]
  split
  · rename_i tp htp
    refine okdAt_returnOk fun h => ?_
    obtain ⟨k1, k2⟩ := archDataToObjType_vtx htp h
    simp only [isVtxObjectTypeNum, decide_eq_true_eq]
    omega
  · exact okdAt_throw _

/-- **A VT-x retype of the untyped decoder is on the VT-x gate's inputs.** -/
theorem okd_decodeUntypedVtx (bitsApi : ApiObjectType → Nat → Nat) (label : Data) (args : List Data)
    (slot : CslotPtr) (cap : Cap) (excaps : List Cap) (σ : State Unit) :
    OkDAt σ (fun _ ui => VtxTy (utType ui) →
        genInvocationType label = .untypedRetype ∧ 6 ≤ args.length ∧ excaps ≠ [] ∧
          isVtxObjectTypeNum (dataToNat (args.getD 0 0)) = true)
      (decodeUntypedInvocationWith (Z := Unit) bitsApi label args slot cap excaps) := by
  unfold decodeUntypedInvocationWith
  refine okdAt_unlessE_bind _ _ fun hl => ?_
  refine okdAt_whenE_bind _ _ fun hlen => ?_
  refine okdAt_whenE_bind _ _ fun hex => ?_
  refine okdAt_returnOk_bind ?_
  refine okdAt_bind fun t s ht => ?_
  have ht' := okd_dataToObjType_vtx _ σ t s ht
  have hargs : the args[0]? = args.getD 0 0 := by
    cases args with
    | nil => simp at hlen
    | cons a l => rfl
  refine okdAt_mono' (Q := fun _ ui => utType ui = t) ?_ fun _ ui hu hv => ?_
  · okt_auto
  · refine ⟨hl, by omega, fun e => by simp [e] at hex, ?_⟩
    rw [← hargs]; exact ht' (hu ▸ hv)

/-- `InvNV` of FL4's TCB decoder (VirtTcbOK's `okd_decodeTcb`). -/
theorem okd_fl4DecodeTcb_invNV (label : Data) (args : List Data) (cap : Cap) (slot : CslotPtr)
    (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) (σ : State Unit) :
    OkDAt σ (fun _ i => InvNV i) (fl4DecodeTcbInvocation (Z := Unit) label args cap slot excaps buffer) := by
  unfold fl4DecodeTcbInvocation
  split
  · exact okdAt_liftME fun _ _ _ => trivial
  · split
    · exact okdAt_liftME fun _ _ _ => trivial
    · exact okdAt_liftME (okd_decodeTcb _ _ _ _ _ σ)

/-- **`InvNV` of the ported dispatcher's outcomes** from an `NVC` decode state, off the VT-x gate. -/
theorem okd_fl4Decode_invNV (hvk : virtKind = .none) (fp : Bool) (label : Data) (args : List Data) (ci : CapRef)
    (sl : CslotPtr) (cap : Cap) (ex : List (Cap × CslotPtr)) (b : Option ObjRef) (σ : State Unit) (hv : NVC σ)
    (hg : ∀ d p n f, cap = .untypedCap d p n f → ¬ untypedVtxGate label args (ex.map Prod.fst)) :
    OkDAt σ (fun _ i => InvNV i) (fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex b) := by
  cases cap with
  | untypedCap d p n f =>
    simp only [fl4DecodeInvocation]
    refine okdAt_liftME ?_
    intro ui s hu e
    obtain ⟨h1, h2, h3, h4⟩ := okd_decodeUntypedVtx fl4ObjBitsApi label args sl _ _ σ _ s hu e
    exact hg d p n f rfl ⟨h1, h2, h3, h4, hvk⟩
  | threadCap p =>
    simp only [fl4DecodeInvocation]
    split
    · exact okdAt_throw _
    · exact okd_fl4DecodeTcb_invNV _ _ _ _ _ _ σ
  | cnodeCap =>
    simp only [fl4DecodeInvocation]; split
    · exact okdAt_throw _
    · exact okdAt_liftME (okd_decodeCnode_nv hv _ _ _ _)
  | irqHandlerCap => simp only [fl4DecodeInvocation]; exact okdAt_liftME (okd_decodeIrqHandler_nv _ _ _ σ)
  | archObjectCap => simp only [fl4DecodeInvocation]; exact okdAt_liftME (okd_fl4ArchDecode_nv _ _ _ _ _ _ σ)
  | _ =>
    simp only [fl4DecodeInvocation]
    repeat' (first
      | exact okdAt_throw _
      | exact okdAt_returnOk trivial
      | exact okdAt_liftME fun _ _ _ => trivial
      | split)

/-! ## Pointwise posts -/

section
variable {S ε α β : Type}

theorem post_bindE {m : NonDetE S ε α} {k : α → NonDetE S ε β} {σ : S} {Q : S → Prop}
    (hm : ∀ a s, ((Except.ok a : Except ε α), s) ∈ (ExceptT.run m σ).1 → ∀ y ∈ (ExceptT.run (k a) s).1, Q y.2)
    (he : ∀ e s, ((Except.error e : Except ε α), s) ∈ (ExceptT.run m σ).1 → Q s) :
    ∀ y ∈ (ExceptT.run (m >>= k) σ).1, Q y.2 := by
  intro y hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, he', rfl⟩⟩ := mem_bindE_inv' hy
  · obtain ⟨r, s⟩ := z
    simp only at ha; subst ha
    exact hm a s hz y hy
  · obtain ⟨r, s⟩ := z
    simp only at he'; subst he'
    exact he e s hz

theorem liftE_no_err {m : NonDet S α} {σ s : S} {e : ε}
    (h : ((Except.error e : Except ε α), s) ∈ (ExceptT.run (NonDetE.liftE (ε := ε) m) σ).1) : False := by
  obtain ⟨x, -, e⟩ := mem_liftE_inv' h
  simp only [Prod.mk.injEq] at e
  cases e.1

end

/-! ## The invocation -/

set_option maxHeartbeats 8000000 in
/-- **The ported invocation keeps `NR`** from an `NR` state whose decode points are off the routes. -/
theorem nr_handleInvocationR (hvk : virtKind = .none) (rep calling blocking don fp : Bool) (cptr : CapRef)
    (σ : State Unit) (hs : NR σ) (hoff : OffRoute5 fp cptr σ) :
    ∀ y ∈ (ExceptT.run (fl4HandleInvocationR (Z := Unit) rep calling blocking don fp cptr) σ).1, NR y.2 := by
  unfold fl4HandleInvocationR
  refine post_bindE (fun th s0 h0 => ?_) (fun e s h => (liftE_no_err h).elim)
  have h0' := mem_run_liftE' h0
  simp only [NonDet.gets, Set.mem_singleton_iff, Prod.mk.injEq] at h0'
  obtain ⟨e1, e2⟩ := h0'
  subst s0; subst th
  refine post_bindE (fun info s1 h1 => ?_) (fun e s h => (liftE_no_err h).elim)
  have h1' := mem_run_liftE' h1
  have n1 : NR s1 := nr_getMessageInfo _ _ hs _ h1'
  refine syscall_post' (I := NR) (Q := NR) (fun w hw => nr_lookupPart _ cptr info s1 n1 w hw) ?_ ?_ ?_ ?_
  · intro f s hs' v hv
    exact SInv.ik_when _ (nr_of (nvc_handleFault _ _) (ty_handleFault _ _) (ns_handleFault _ _)) s hs' v hv
  · intro a s has w hw
    obtain ⟨sl, cap, ex, buf⟩ := a
    have nt : NR s := nr_lookupPart _ cptr info s1 n1 _ has
    exact (SInv.ike_bind (SInv.ike_liftE (nr_getMrs _ _ _)) fun _ => nr_fl4Decode _ _ _ _ _ _ _ _) s nt w hw
  · intro e s hs' v hv
    exact SInv.ik_when _ (nr_of (SInvV.hv_fl4ReplyFromKernelError _ _ _) (ty_fl4ReplyFromKernelError _ _ _)
      (ns_fl4ReplyFromKernelError _ _ _)) s hs' v hv
  · intro a s b s' has hbs hI
    obtain ⟨sl, cap, ex, buf⟩ := a
    have nt : NR s := nr_lookupPart _ cptr info s1 n1 _ has
    have eE : hV s' = hV s := (by hv_auto : IKHE (ε := SyscallError) (fun x => hV x = hV s) (do
      let args ← NonDetE.liftE <| getMrs (Z := Unit) σ.curThread buf info
      fl4DecodeInvocation fp info.miLabel args cptr sl cap ex buf)) s rfl _ hbs
    have hcap : capOpt (s.kheap sl.1) sl.2 = some cap := okCap_front σ.curThread cptr info s1 _ s has
    rw [ExceptT.run_bind] at hbs
    obtain ⟨⟨r1, t2⟩, hr1, hb'⟩ := hbs
    cases r1 with
    | error e =>
      exfalso
      simp only [ExceptT.bindCont] at hb'
      cases Set.mem_singleton_iff.1 hb'
    | ok args =>
      simp only [ExceptT.bindCont] at hb'
      have hr1' := mem_run_liftE' hr1
      have n2 : NR t2 := nr_getMrs _ _ _ s nt _ hr1'
      have hr := hoff info (sl, cap, ex, buf) args t2 ⟨s1, s, h1', has, hr1'⟩
      have hg : ∀ d p n f, cap = .untypedCap d p n f → ¬ untypedVtxGate info.miLabel args (ex.map Prod.fst) :=
        fun d p n f e hgate => hr (by subst e; exact hgate)
      have hInv : InvNV b := okd_fl4Decode_invNV hvk fp _ args cptr sl cap ex buf t2 n2.1.1 hg b s' hb'
      have hK := okd_fl4Decode_nvK1 fp info.miLabel args cptr sl cap ex buf t2 b s' hb'
      refine post_bindE (fun _ s2 h2 => ?_) (fun e s2 h2 => (liftE_no_err h2).elim)
      have h2' := mem_run_liftE' h2
      have n3 : NR s2 := nr_setRestart _ s' hI _ h2'
      have e3 : hV s2 = hV s' :=
        (SInvV.hv_setThreadState (P := fun x => hV x = hV s') _ _) s' rfl _ h2'
      have hU : UnmapOK s2 b := unmapOK_of_hV (e3.trans eE) (unmapOK_of hK.2 hcap)
      have hP : ∀ x ∈ (ExceptT.run (fl4PerformInvocation (Z := Unit) blocking calling don b) s2).1, NR x.2 :=
        fun x hx => ⟨⟨nvc_fl4Perform blocking calling don b s2 n3.1.1 hInv hK.1 hU x hx,
          ty_fl4Perform blocking calling don b hInv s2 n3.1.2 x hx⟩,
          ns_fl4PerformInvocation blocking calling don b s2 n3.2 x hx⟩
      refine post_bindE (fun rp s3 h3 => ?_) (fun e s3 h3 => hP _ h3)
      exact (nr_ofE (by hv_auto) (by ty_auto)
        (SInv.ike_liftE (SInv.ik_bind (ns_getThreadState _) fun st => by
          split
          · exact SInv.ik_bind (SInv.ik_when _ (ns_replyFromKernel _ _)) fun _ =>
              ns_setThreadState _ _ (by decide)
          · exact SInv.ik_pure _)) : SInv.IKE NR (withoutPreemption (do
        let state ← getThreadState (Z := Unit) σ.curThread
        match state with
        | .restart => do
          NonDet.when calling <| replyFromKernel σ.curThread (0, rp)
          setThreadState σ.curThread .running
        | _ => return ()))) s3 (hP _ h3)

/-! ## Syscalls, events, the kernel step -/

theorem nr_invoke (hvk : virtKind = .none) (rep calling blocking don fp : Bool) (reg : Register)
    {k : Unit → PMonad Unit Unit} (hk : ∀ u, SInv.IKE NR (k u)) {t : State Unit} (ht : NR t)
    (hoff : ∀ cptr t', (cptr, t') ∈ (getCapReg (Z := Unit) reg t).1 → OffRoute5 fp cptr t') :
    ∀ y ∈ (ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) reg) >>= fun cptr =>
        fl4HandleInvocationR rep calling blocking don fp cptr >>= k) t).1, NR y.2 := by
  refine post_bindE (fun cptr t' h => ?_) (fun e s h => (liftE_no_err h).elim)
  have h' := mem_run_liftE' h
  have nt' := nr_getCapReg reg t ht _ h'
  exact post_bindE (fun _ u hu => hk _ u (nr_handleInvocationR hvk rep calling blocking don fp cptr t' nt'
    (hoff _ _ h') _ hu)) (fun e u hu => nr_handleInvocationR hvk rep calling blocking don fp cptr t' nt'
    (hoff _ _ h') _ hu)

theorem nr_invoke0 (hvk : virtKind = .none) (rep calling blocking don fp : Bool) (reg : Register)
    {t : State Unit} (ht : NR t)
    (hoff : ∀ cptr t', (cptr, t') ∈ (getCapReg (Z := Unit) reg t).1 → OffRoute5 fp cptr t') :
    ∀ y ∈ (ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) reg) >>= fun cptr =>
        fl4HandleInvocationR rep calling blocking don fp cptr) t).1, NR y.2 := by
  refine post_bindE (fun cptr t' h => ?_) (fun e s h => (liftE_no_err h).elim)
  have h' := mem_run_liftE' h
  exact nr_handleInvocationR hvk rep calling blocking don fp cptr t' (nr_getCapReg reg t ht _ h') (hoff _ _ h')

theorem nr_recv (a b : Bool) : SInv.IKE (ε := Unit) NR (withoutPreemption (handleRecv (Z := Unit) a b)) :=
  SInv.ike_liftE (nr_of (nvc_handleRecv a b) (ty_handleRecv a b) (ns_handleRecv a b))

theorem nr_recvK (b : Bool) : ∀ _u : Unit, SInv.IKE (ε := Unit) NR (withoutPreemption (handleRecv (Z := Unit) true b)) :=
  fun _ => nr_recv true b

set_option maxHeartbeats 8000000 in
/-- **Every syscall keeps `NR`** off the routes. -/
theorem nr_fl4HandleSyscall (hvk : virtKind = .none) (rep : Bool) (c : Syscall) {t : State Unit} (ht : NR t)
    (hoff : OffRouteS5 c t) : ∀ y ∈ (ExceptT.run (fl4HandleSyscall (Z := Unit) rep c) t).1, NR y.2 := by
  cases c with
  | sysSend =>
    show ∀ y ∈ (ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) cap_register) >>= fun cptr =>
        fl4HandleInvocationR rep false true false false cptr) t).1, NR y.2
    exact nr_invoke0 hvk rep false true false false cap_register ht fun cptr t' h => hoff _ rfl cptr t' h _
  | sysNBSend =>
    show ∀ y ∈ (ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) cap_register) >>= fun cptr =>
        fl4HandleInvocationR rep false false false false cptr) t).1, NR y.2
    exact nr_invoke0 hvk rep false false false false cap_register ht fun cptr t' h => hoff _ rfl cptr t' h _
  | sysCall =>
    show ∀ y ∈ (ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) cap_register) >>= fun cptr =>
        fl4HandleInvocationR rep true true true false cptr) t).1, NR y.2
    exact nr_invoke0 hvk rep true true true false cap_register ht fun cptr t' h => hoff _ rfl cptr t' h _
  | sysReplyRecv =>
    show ∀ y ∈ (ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) replyRegister) >>= fun cptr =>
        fl4HandleInvocationR rep false false true true cptr >>= fun _ =>
          withoutPreemption (handleRecv (Z := Unit) true true)) t).1, NR y.2
    exact nr_invoke hvk rep false false true true replyRegister (nr_recvK true) ht
      fun cptr t' h => hoff _ rfl cptr t' h _
  | sysNBSendRecv =>
    show ∀ y ∈ (ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) nbsendRecvDest) >>= fun cptr =>
        fl4HandleInvocationR rep false false true true cptr >>= fun _ =>
          withoutPreemption (handleRecv (Z := Unit) true true)) t).1, NR y.2
    exact nr_invoke hvk rep false false true true nbsendRecvDest (nr_recvK true) ht
      fun cptr t' h => hoff _ rfl cptr t' h _
  | sysNBSendWait =>
    show ∀ y ∈ (ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) replyRegister) >>= fun cptr =>
        fl4HandleInvocationR rep false false true true cptr >>= fun _ =>
          withoutPreemption (handleRecv (Z := Unit) true false)) t).1, NR y.2
    exact nr_invoke hvk rep false false true true replyRegister (nr_recvK false) ht
      fun cptr t' h => hoff _ rfl cptr t' h _
  | sysRecv => exact nr_recv true true t ht
  | sysWait => exact nr_recv true false t ht
  | sysNBWait => exact nr_recv false false t ht
  | sysNBRecv => exact nr_recv false true t ht
  | sysYield => exact SInv.ike_liftE (nr_of nvc_handleYield ty_handleYield ns_handleYield) t ht

theorem nr_updateTimeStamp : SInv.IK NR (updateTimeStamp (Z := Unit)) :=
  nr_of nvc_updateTimeStamp ty_updateTimeStamp ns_updateTimeStamp

theorem nr_checkBudgetRestart : SInv.IK NR (checkBudgetRestart (Z := Unit)) :=
  nr_of nvc_checkBudgetRestart ty_checkBudgetRestart ns_checkBudgetRestart

set_option maxHeartbeats 4000000 in
/-- **Every event keeps `NR`** off the routes. -/
theorem nr_fl4HandleEvent (hvk : virtKind = .none) (rep : Bool) (ev : Event) {σ : State Unit} (hs : NR σ)
    (hr5 : ∀ c, ev = .syscallEvent c → ∀ t, EntryPt σ t → OffRouteS5 c t) :
    ∀ y ∈ (ExceptT.run (fl4HandleEvent (Z := Unit) rep ev) σ).1, NR y.2 := by
  by_cases h : ∃ c, ev = .syscallEvent c
  · obtain ⟨c, rfl⟩ := h
    show ∀ y ∈ (ExceptT.run (NonDetE.liftE updateTimeStamp >>= fun _ => NonDetE.liftE checkBudgetRestart >>=
      fun restart => NonDetE.whenE restart (fl4HandleSyscall (Z := Unit) rep c)) σ).1, NR y.2
    refine post_bindE (fun _ t1 h1 => ?_) (fun e s h => (liftE_no_err h).elim)
    have h1' := mem_run_liftE' h1
    refine post_bindE (fun restart t h2 => ?_) (fun e s h => (liftE_no_err h).elim)
    have h2' := mem_run_liftE' h2
    have nt : NR t := nr_checkBudgetRestart t1 (nr_updateTimeStamp σ hs _ h1') _ h2'
    unfold NonDetE.whenE
    cases restart with
    | false => rw [if_neg Bool.false_ne_true]; exact (SInv.ike_returnOk (P := NR) ()) t nt
    | true =>
      rw [if_pos rfl]
      exact nr_fl4HandleSyscall hvk rep c nt (hr5 c rfl t ⟨t1, h1', h2'⟩)
  · have h' : ∀ c, ev ≠ .syscallEvent c := fun c e => h ⟨c, e⟩
    intro y hy
    have hn := ns_fl4HandleEvent rep ev σ hs.2 y hy
    have ht := ty_fl4HandleEvent_other rep ev h' σ hs.1.2 y hy
    rw [fl4HandleEvent_other rep ev h'] at hy
    exact ⟨⟨nvc_handleEvent_other ev h' σ hs.1.1 y hy, ht⟩, hn⟩

theorem nr_preemptionPath : SInv.IK NR (preemptionPath (Z := Unit)) :=
  nr_of nvc_preemptionPath ty_preemptionPath ns_preemptionPath

theorem nr_kernelExit : SInv.IK NR (do fl4Awaken (Z := Unit); schedule (Z := Unit); activateThread (Z := Unit)) :=
  nr_of nvc_kernelExit (SInv.ik_bind ty_fl4Awaken fun _ => SInv.ik_bind ty_schedule fun _ => ty_activateThread)
    (SInv.ik_bind ns_fl4Awaken fun _ => SInv.ik_bind ns_schedule fun _ => ns_activateThread)

/-- **The ported kernel step keeps `NR`** off the routes at `virtKind = none` (premises: module docstring). -/
theorem nr_fl4CallKernel (hvk : virtKind = .none) (rep : Bool) (ev : Event) {σ : State Unit} (hs : NR σ)
    (hr5 : ∀ c, ev = .syscallEvent c → ∀ t, EntryPt σ t → OffRouteS5 c t) :
    ∀ y ∈ (fl4CallKernel (Z := Unit) rep ev σ).1, NR y.2 := by
  unfold fl4CallKernel
  intro y ⟨z, hz, hy⟩
  have nz : NR z.2 := by
    unfold NonDetE.handleE at hz
    rw [ExceptT.run_mk] at hz
    obtain ⟨⟨r, u⟩, hw, hz⟩ := hz
    have nu : NR u := nr_fl4HandleEvent hvk rep ev hs hr5 _ hw
    cases r with
    | ok a =>
      obtain rfl := Set.mem_singleton_iff.1 hz
      exact nu
    | error e => exact (SInv.ike_liftE (P := NR) nr_preemptionPath) u nu z hz
  exact nr_kernelExit z.2 nz y hy

/-- **The extended step keeps `NR`** where it is the ported one (VirtTcbOK's `fl4CallKernelV_eqNR5`). -/
theorem nr_fl4CallKernelV (hvk : virtKind = .none) (onCore : ObjRef → Bool) (rep : Bool) (ev : Event)
    {σ : State Unit} (hs : NR σ) (hr5 : ∀ c, ev = .syscallEvent c → ∀ t, EntryPt σ t → OffRouteS5 c t) :
    ∀ y ∈ (fl4CallKernelV (Z := Unit) onCore rep ev σ).1, NR y.2 := by
  rw [fl4CallKernelV_eqNR5 hvk onCore rep ev hs hr5]
  exact nr_fl4CallKernel hvk rep ev hs hr5

/-! ## Runs -/

/-- A run of kernel steps `σ →ev₁ … →evₙ σ'` of the ported kernel, each event off the routes at its state
(`hr5`). -/
inductive RunNR (rep : Bool) : State Unit → State Unit → Prop
  | refl (σ : State Unit) : RunNR rep σ σ
  | step {σ σ' σ'' : State Unit} (ev : Event) (hr : ∀ c, ev = .syscallEvent c → ∀ t, EntryPt σ t → OffRouteS5 c t)
      (h : ((), σ') ∈ (fl4CallKernel (Z := Unit) rep ev σ).1) (hn : RunNR rep σ' σ'') : RunNR rep σ σ''

/-- **Every state of an off-route run from an `NR` state is `NR`.** -/
theorem runNR_nr (hvk : virtKind = .none) {rep : Bool} {σ σ' : State Unit} (h : RunNR rep σ σ') (hs : NR σ) :
    NR σ' := by
  induction h with
  | refl => exact hs
  | step ev hr h _ ih => exact ih (nr_fl4CallKernel hvk rep ev hs hr _ h)

/-- **Along such a run the extended step is the ported one at every reached state**, so
`fl4CallKernelV_eqNR5` applies along every off-route run. -/
theorem runNR_eqV (hvk : virtKind = .none) (onCore : ObjRef → Bool) {rep : Bool} {σ0 σ : State Unit}
    (h : RunNR rep σ0 σ) (hs : NR σ0) (ev : Event)
    (hr : ∀ c, ev = .syscallEvent c → ∀ t, EntryPt σ t → OffRouteS5 c t) :
    fl4CallKernelV (Z := Unit) onCore rep ev σ = fl4CallKernel rep ev σ :=
  fl4CallKernelV_eqNR5 hvk onCore rep ev (runNR_nr hvk h hs) hr

/-- The boot condition: no virtualization cap, object or running VM. -/
theorem nr_boot {σ : State Unit} (hc : NoVirtCaps σ) (ho : NoVirtObjects σ) (hn : NoRunVM σ) : NR σ :=
  ⟨nv_of_noVirt hc ho, hn⟩

end

end Fl4Proofs.P3.VirtNvK2
