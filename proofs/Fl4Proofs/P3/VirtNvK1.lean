/-
P3x for virtualization, spec side (line virt, gen 6; proofs/VIRT-PLAN.md §10, table row "NoVirt reachability"):
**every perform of the ported kernel keeps `NVC`** (no slot holds a virtualization cap), given the decode facts
carried to it, and so do the writers of the kernel shell outside the invocation. This is vih3's G / Y / W / S
(SpecInvValidIrqHandlers*) restated for `NVC`, with VirtNvcW's IPC and budget writers.

* Retype: `nvc_retypeRegion(With)` (default objects hold no virtualization cap), `nvc_deleteObjects`,
  `nvc_createCap` (type not `VtxTy`, VirtNvInv), `nvc_resetUntypedCap`, **`nvc_invokeUntypedWith`**.
* `nvc_invokeCnode` (`CnNV`), `nvc_invokeIrqHandler` (the set-handler cap), `nvc_invokeTcb` (`TcbCapsOK` and
  `TcbNV`: the IPC buffer frame cap of a `ThreadControlCaps`, the fault handler of a `ThreadControlSched` —
  neither is covered by `TcbCapsOK`).
* Arch: page / table maps (`nvc_setCap_bind_dead`: a table map's continuation matches the written cap as the
  table cap), unmaps (`unmapTail`: the slot still holds the invoked cap, `UnmapOK`; X64 `update_map_data` of an
  unknown cap is `undefined`, so the slot fact is needed), ASID control / pool, IO port control,
  **`nvc_performFrameBatch`** (SpecFbX's `ik_fbEntryX_of`; `nvc_fbMap` with the page decoder's carry),
  `nvc_archPerform`, `nvc_fl4ArchPerform`.
* **`nvc_fl4Perform`**: every `fl4PerformInvocation` outcome from an `NVC` state is `NVC`, given `InvNV`
  (VirtNvInv), `InvTcbNV` and `UnmapOK`.
* The decoder's carry: `okd_decodePageInvocation`, `okd_archDecode` (`ArchAt`: a page map writes a `vmVSpaceMap`
  cap, an unmap names the invoked slot and cap), `okd_fl4ArchDecode_at`, **`okd_fl4ArchDecode_nv`** (`ArchNV`),
  `okd_decodeTcb_nv` / `okd_fl4DecodeTcb_nv` (`TcbNV`), **`okd_fl4Decode_nvK1`** (`InvTcbNV ∧ UnmapAt sl cap` of
  every dispatcher outcome), `unmapOK_of` (with the invoked cap in its slot), `unmapOK_of_hV` (kept by every
  `hV`-preserving step).
* Shell: `nvc_archInvokeIrqControl`, `nvc_doReplyTransfer`, `nvc_handleFault`, `nvc_receiveIpc`,
  `nvc_handleRecv`, `nvc_handleYield`, `nvc_invokeIrqControl`, `nvc_invokeFl4IrqControl`, `nvc_preemptionPath`
  (all `hv_leaf`s), **`nvc_handleEvent_other`**, **`nvc_kernelExit`**.

No premises beyond the carried facts named above; no [J]/[P]/[W]/[S]. New file only.
-/
import Fl4Proofs.P3.VirtNvInv
import Fl4Proofs.P3.VirtNvcW
import Fl4Proofs.P3.SpecInvValidIrqHandlersS
open Classical

namespace Fl4Proofs.P3.VirtNvK1
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvV Fl4Proofs.P3.SInvL Fl4Proofs.P3.SInvDom
  Fl4Proofs.P3.VirtNvTcb Fl4Proofs.P3.VirtNvcW Fl4Proofs.P3.VirtNvInv Fl4Proofs.P3.VirtInvOK

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

/-! ## Retype and detype -/

theorem capOpt_default_nv {ty : ApiObjectType} (hty : ty ≠ .untyped) (dev : Bool) (n : Nat) (d : Domain)
    (cref : CnodeIndex) {c : Cap} (h : capOpt (some (defaultObject ty dev n d)) cref = some c) :
    ¬ IsVirtCap c := by
  cases ty with
  | untyped => exact absurd rfl hty
  | capTableObject =>
    simp only [defaultObject, capOpt] at h
    split_ifs at h with h1
    simp only [emptyCnode] at h
    split_ifs at h with h2
    cases h; exact fun h => h
  | tcbObject =>
    simp only [defaultObject, capOpt, tcbCnodeMap, defaultTcb, Function.update_apply] at h
    split_ifs at h <;> (cases h; exact fun h => h)
  | archObject a => simp only [defaultObject, capOpt] at h; cases h
  | _ => simp only [defaultObject, capOpt] at h; cases h

theorem nvc_retypeRegionWith (bA : ApiObjectType → Nat → Nat) (ptr : ObjRef) (n oB : Nat) (ty : ApiObjectType)
    (dev : Bool) : IKH NVC (retypeRegionWith (Z := Unit) bA ptr n oB ty dev) := by
  intro σ h y hy
  rcases (SInvU.retypeRegionWith_out hy).2 with e' | ⟨hty, e'⟩
  · rw [e']; exact h
  · rw [e']
    intro sl c hc
    simp only [SInvU.retKh] at hc
    split_ifs at hc
    · exact capOpt_default_nv hty _ _ _ _ hc
    · exact h sl c hc

theorem nvc_retypeRegion (ptr : ObjRef) (n oB : Nat) (ty : ApiObjectType) (dev : Bool) :
    IKH NVC (retypeRegion (Z := Unit) ptr n oB ty dev) := by
  rw [← retypeRegionWith_objBitsApi]; exact nvc_retypeRegionWith _ _ _ _ _ _

theorem nvc_deleteObjects (ptr : Word) (bits : Nat) : IKH NVC (deleteObjects (Z := Unit) ptr bits) := by
  unfold deleteObjects
  refine ik_bind (nvc_doMachineOp _) fun _ => ik_modify fun σ h => ?_
  intro sl c hc
  simp only [detype] at hc
  split_ifs at hc
  · simp [capOpt] at hc
  · exact h sl c hc

theorem nvc_createCap (t : ApiObjectType) (b : Nat) (u : CslotPtr) (d : Bool) (x : CslotPtr × ObjRef)
    (ht : ¬ VtxTy t) : IKH NVC (createCap (Z := Unit) t b u d x) := by
  obtain ⟨dest, oref⟩ := x
  unfold createCap; dsimp only
  exact ik_bind (ik_gets _) fun _ => ik_bind (ik_gets _) fun _ => ik_bind (nvc_setCdt _) fun _ =>
    ik_bind (nvc_doExtendedOp _) fun _ => ik_bind (nvc_setOriginal _ _) fun _ =>
    nvc_setCap _ (defaultCap_nv ht _ _ _)

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact nvc_retypeRegionWith _ _ _ _ _ _)
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact nvc_retypeRegion _ _ _ _ _)
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact nvc_deleteObjects _ _)
macro_rules | `(tactic| hv_leaf) => `(tactic| ((with_reducible refine nvc_createCap _ _ _ _ _ ?_); assumption))

theorem nvc_resetUntypedCap (srcSlot : CslotPtr) : IKHE NVC (resetUntypedCap (Z := Unit) srcSlot) := by
  unfold resetUntypedCap; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact nvc_resetUntypedCap _)

/-- **The retype keeps `NVC`** for a non-VT-x type. -/
theorem nvc_invokeUntypedWith (bA : ApiObjectType → Nat → Nat) (ui : UntypedInvocation)
    (h : ¬ VtxTy (utType ui)) : IKHE NVC (invokeUntypedWith (Z := Unit) bA ui) := by
  obtain ⟨src, reset, base, rb, t, sz, slots, dev⟩ := ui
  change ¬ VtxTy t at h
  unfold invokeUntypedWith; hv_auto

/-! ## CNode and IRQ handler performs -/

theorem nvc_invokeCnode (i : CnodeInvocation) (hi : CnNV i) : IKHE (ε := Unit) NVC (invokeCnode (Z := Unit) i) := by
  cases i with
  | insertCall c s d => exact ike_liftE (nvc_capInsert s d hi)
  | moveCall c s d => exact ike_liftE (nvc_capMove s d hi)
  | rotateCall c1 c2 s1 s2 s3 =>
    obtain ⟨h1, h2⟩ := hi
    refine ike_liftE ?_
    split
    · first | exact nvc_capSwap _ _ h2 h1 | exact nvc_capSwap _ _ h1 h2
    · exact ik_bind (nvc_capMove _ _ h2) fun _ => nvc_capMove _ _ h1
  | revokeCall s => exact nvc_capRevoke s
  | deleteCall s => exact nvc_capDelete s
  | cancelBadgedSendsCall c => simp only [invokeCnode]; split <;> (try (exfalso; simp_all; done)) <;> hv_auto

theorem nvc_invokeIrqHandler (i : IrqHandlerInvocation)
    (hi : ∀ irq c sl, i = .setIRQHandler irq c sl → ¬ IsVirtCap c) :
    IKH NVC (invokeIrqHandler (Z := Unit) i) := by
  cases i with
  | aCKIrq irq => simp only [invokeIrqHandler, archInvokeIrqHandler]; exact nvc_doMachineOp _
  | setIRQHandler irq c sl =>
    have hc := hi irq c sl rfl
    simp only [invokeIrqHandler]
    exact ik_bind (hv_getIrqSlot _) fun s => ik_bind (nvc_capDeleteOne s) fun _ => nvc_capInsert sl s hc
  | clearIRQHandler irq =>
    simp only [invokeIrqHandler]
    exact ik_bind (hv_getIrqSlot _) fun s => nvc_capDeleteOne s

/-! ## TCB performs -/

/-- The IPC buffer frame cap a `ThreadControlCaps` installs is not a virtualization cap. -/
def BufNV : Option (VSpaceRef × Option (Cap × CslotPtr)) → Prop
  | some (_, some (c, _)) => ¬ IsVirtCap c
  | _ => True

/-- **The TCB caps `TcbCapsOK` does not cover**: the IPC buffer frame cap of a `ThreadControlCaps`, the fault
handler of a `ThreadControlSched` (carried from the decoder by `okd_decodeTcb_nv`). -/
def TcbNV : TcbInvocation → Prop
  | .threadControlCaps _ _ _ _ _ _ b => BufNV b
  | .threadControlSched _ _ fh _ _ _ => CapOK fh
  | _ => True

/-- `TcbNV` of a TCB invocation. -/
def InvTcbNV : Fl4Invocation → Prop
  | .invokeTCB i => TcbNV i
  | _ => True

theorem nvc_installTcbCap' (target : ObjRef) (slot : CslotPtr) (n : Nat) {o : Option (Cap × CslotPtr)}
    (ho : CapOK o) : IKHE (ε := Unit) NVC (installTcbCap (Z := Unit) target slot n o) := by
  cases o with
  | none => simp only [installTcbCap]; exact ike_returnOk _
  | some p =>
    obtain ⟨c, src⟩ := p
    exact ik_installTcbCap (P := NVC) target slot src n (fun sl => nvc_capDelete sl)
      (fun a b => nvc_capInsert a b (ho c src rfl)) (fun sl => hv_getCap (P := NVC) sl)

theorem nvc_installTcbFrameCap (target : ObjRef) (slot : CslotPtr) (buf : Option (VSpaceRef × Option (Cap × CslotPtr)))
    (hb : BufNV buf) : IKHE (ε := Unit) NVC (installTcbFrameCap (Z := Unit) target slot buf) := by
  rcases buf with _ | ⟨ptr, _ | ⟨c, src⟩⟩
  · simp only [installTcbFrameCap]; exact ike_returnOk _
  · simp only [installTcbFrameCap]; hv_auto
  · have hc : ¬ IsVirtCap c := hb
    simp only [installTcbFrameCap]; hv_auto

theorem nvc_invokeTcb (i : TcbInvocation) (hc : TcbCapsOK i) (hn : TcbNV i) :
    IKHE (ε := Unit) NVC (invokeTcb (Z := Unit) i) := by
  cases i with
  | threadControlCaps target slot fh th cr vr buf =>
    obtain ⟨h1, h2, h3, h4⟩ := hc
    simp only [invokeTcb]
    exact ike_bind (nvc_installTcbCap' _ _ _ h1) fun _ => ike_bind (nvc_installTcbCap' _ _ _ h2) fun _ =>
      ike_bind (nvc_installTcbCap' _ _ _ h3) fun _ => ike_bind (nvc_installTcbCap' _ _ _ h4) fun _ =>
      ike_bind (nvc_installTcbFrameCap _ _ _ hn) fun _ => ike_returnOk _
  | threadControlSched target slot fh mcp prio sc =>
    simp only [invokeTcb]
    refine ike_bind (nvc_installTcbCap' _ _ _ hn) fun _ => ?_
    hv_auto
  | _ => simp only [invokeTcb]; hv_auto

/-! ## Arch performs -/

/-- A slot holds a given cap, on an `NVC` state (a predicate of `hV` alone). -/
def SlotQ (sl : CslotPtr) (c : Cap) (σ : State Unit) : Prop :=
  NVC σ ∧ capOpt (σ.kheap sl.1) sl.2 = some c

instance (sl : CslotPtr) (c : Cap) : WLH (SlotQ sl c) :=
  wlh_of_hV fun _ _ e h => ⟨h.1.view e, by rw [hV_cap e]; exact h.2⟩

/-- The unmap tail: the slot's cap re-written with its mapping cleared. -/
theorem unmapTail (sl : CslotPtr) (c : ArchCap) (mt : Option VMMapType)
    (hk : ¬ IsVirtCap (.archObjectCap (updateMapData c none mt))) (σ : State Unit)
    (h : SlotQ sl (.archObjectCap c) σ) :
    ∀ x ∈ ((NonDet.liftM Cap.theArchCap (getCap (Z := Unit) sl) >>= fun cap =>
      setCap (Z := Unit) (.archObjectCap (updateMapData cap none mt)) sl) σ).1, NVC x.2 := by
  obtain ⟨o, r⟩ := sl
  intro x hx
  obtain ⟨y, hy, hx⟩ := hx
  unfold NonDet.liftM at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨c0, s0⟩ := z
  obtain ⟨e1, e2⟩ := vih_mem_getCap hz
  simp only at e1 e2
  subst e1
  rw [h.2] at e2
  cases e2
  obtain rfl := Set.mem_singleton_iff.1 hy
  exact nvc_setCap (o, r) hk _ h.1 x hx

theorem nvc_setCap_bind_dead {β : Type} (cap : Cap) (sl : CslotPtr) {k : Unit → NonDet (State Unit) β}
    (hk : ∀ a, IKH NVC (k a)) (hd : IsVirtCap cap → ∀ a σ x, x ∈ (k a σ).1 → False) :
    IKH NVC (setCap (Z := Unit) cap sl >>= k) := by
  intro σ h x ⟨y, hy, hx⟩
  by_cases hc : IsVirtCap cap
  · exact (hd hc _ _ x hx).elim
  · exact hk _ _ (nvc_setCap sl hc σ h y hy) x hx

theorem slotq_of_hV {sl : CslotPtr} {c : Cap} {σ σ' : State Unit} (e : hV σ' = hV σ) (h : SlotQ sl c σ) :
    SlotQ sl c σ' := ⟨h.1.view e, by rw [hV_cap e]; exact h.2⟩

/-- A step keeping `hV`, then a continuation with an `NVC` post from every state with the same `hV`. -/
theorem hvb {α β : Type} {σ0 : State Unit} {m : NonDet (State Unit) α} {k : α → NonDet (State Unit) β}
    (hm : ∀ v, IKH (fun s => hV s = v) m) (hk : ∀ a s, hV s = hV σ0 → ∀ x ∈ (k a s).1, NVC x.2) :
    ∀ s, hV s = hV σ0 → ∀ x ∈ ((m >>= k) s).1, NVC x.2 := by
  intro s e x ⟨y, hy, hx⟩
  exact hk y.1 y.2 ((hm (hV s) s rfl y hy).trans e) x hx

/-- The unmap tail from every state with the `hV` of a `SlotQ` state. -/
theorem unmapTail' (sl : CslotPtr) (c : ArchCap) (mt : Option VMMapType) {σ0 : State Unit}
    (h0 : SlotQ sl (.archObjectCap c) σ0) (hk : ¬ IsVirtCap (.archObjectCap (updateMapData c none mt))) :
    ∀ s, hV s = hV σ0 → ∀ x ∈ ((NonDet.liftM Cap.theArchCap (getCap (Z := Unit) sl) >>= fun cap =>
      setCap (Z := Unit) (.archObjectCap (updateMapData cap none mt)) sl) s).1, NVC x.2 :=
  fun s e => unmapTail sl c mt hk s (slotq_of_hV e h0)

theorem hv_start {β : Type} {m : NonDet (State Unit) β} {σ : State Unit}
    (h : ∀ s, hV s = hV σ → ∀ x ∈ (m s).1, NVC x.2) : ∀ x ∈ (m σ).1, NVC x.2 := h σ rfl

macro "unmap_auto" : tactic => `(tactic| (refine hv_start ?_; repeat' (first
  | (exact unmapTail' _ _ _ ⟨by assumption, by assumption⟩ (by intro h; exact h))
  | (refine hvb (fun v => by hv_auto) fun _ => ?_))))

theorem nvc_performPageTableInvocation (iv : PageTableInvocation) (σ : State Unit) (h : NVC σ)
    (hu : ∀ c sl, iv = .pageTableUnmap c sl → capOpt (σ.kheap sl.1) sl.2 = some c) :
    ∀ x ∈ (performPageTableInvocation (Z := Unit) iv σ).1, NVC x.2 := by
  cases iv with
  | pageTableMap cap sl pde pd vs =>
    simp only [performPageTableInvocation]
    refine nvc_setCap_bind_dead _ _ (fun _ => by hv_auto) ?_ σ h
    intro hv _ _ x hx
    obtain ⟨_, _, hf⟩ := hx
    split at hf <;> first | exact hv | (obtain ⟨_, hf', _⟩ := hf; exact hf') | (simp_all [IsVirtCap]; done)
  | pageTableUnmap c sl =>
    have hc := hu c sl rfl
    cases c with
    | archObjectCap a =>
      cases a with
      | pageTableCap p ma =>
        rcases ma with _ | ⟨a, v⟩ <;> simp only [performPageTableInvocation] <;> unmap_auto
      | _ => intro x hx; exact (show False from hx).elim
    | _ => intro x hx; exact (show False from hx).elim

theorem nvc_performPageDirectoryInvocation (iv : PageDirectoryInvocation) (σ : State Unit) (h : NVC σ)
    (hu : ∀ c sl, iv = .pageDirectoryUnmap c sl → capOpt (σ.kheap sl.1) sl.2 = some c) :
    ∀ x ∈ (performPageDirectoryInvocation (Z := Unit) iv σ).1, NVC x.2 := by
  cases iv with
  | pageDirectoryMap cap sl pde pd vs =>
    simp only [performPageDirectoryInvocation]
    refine nvc_setCap_bind_dead _ _ (fun _ => by hv_auto) ?_ σ h
    intro hv _ _ x hx
    obtain ⟨_, _, hf⟩ := hx
    split at hf <;> first | exact hv | (obtain ⟨_, hf', _⟩ := hf; exact hf') | (simp_all [IsVirtCap]; done)
  | pageDirectoryUnmap c sl =>
    have hc := hu c sl rfl
    cases c with
    | archObjectCap a =>
      cases a with
      | pageDirectoryCap p ma =>
        rcases ma with _ | ⟨a, v⟩ <;> simp only [performPageDirectoryInvocation] <;> unmap_auto
      | _ => intro x hx; exact (show False from hx).elim
    | _ => intro x hx; exact (show False from hx).elim

theorem nvc_performPdptInvocation (iv : PdptInvocation) (σ : State Unit) (h : NVC σ)
    (hu : ∀ c sl, iv = .pdptUnmap c sl → capOpt (σ.kheap sl.1) sl.2 = some c) :
    ∀ x ∈ (performPdptInvocation (Z := Unit) iv σ).1, NVC x.2 := by
  cases iv with
  | pdptMap cap sl pde pd vs =>
    simp only [performPdptInvocation]
    refine nvc_setCap_bind_dead _ _ (fun _ => by hv_auto) ?_ σ h
    intro hv _ _ x hx
    obtain ⟨_, _, hf⟩ := hx
    split at hf <;> first | exact hv | (obtain ⟨_, hf', _⟩ := hf; exact hf') | (simp_all [IsVirtCap]; done)
  | pdptUnmap c sl =>
    have hc := hu c sl rfl
    cases c with
    | archObjectCap a =>
      cases a with
      | pdPointerTableCap p ma =>
        rcases ma with _ | ⟨a, v⟩ <;> simp only [performPdptInvocation] <;> unmap_auto
      | _ => intro x hx; exact (show False from hx).elim
    | _ => intro x hx; exact (show False from hx).elim

/-- What a page invocation needs at its perform. -/
def PageNV (σ : State Unit) : PageInvocation → Prop
  | .pageMap c _ _ _ => ¬ IsVirtCap c
  | .pageUnmap c sl => capOpt (σ.kheap sl.1) sl.2 = some (.archObjectCap c)
  | _ => True

theorem nvc_performPageInvocationUnmap (cap : ArchCap) (sl : CslotPtr) (σ : State Unit)
    (h : SlotQ sl (.archObjectCap cap) σ) :
    ∀ x ∈ (performPageInvocationUnmap (Z := Unit) cap sl σ).1, NVC x.2 := by
  cases cap with
  | pageCap d p R mt sz m =>
    obtain ⟨h1, h2⟩ := h
    rcases m with _ | ⟨a, v⟩ <;> simp only [performPageInvocationUnmap] <;> unmap_auto
  | _ => intro x hx; exact (show False from hx).elim

theorem nvc_performPageInvocation (iv : PageInvocation) (σ : State Unit) (h : NVC σ) (hp : PageNV σ iv) :
    ∀ x ∈ (performPageInvocation (Z := Unit) iv σ).1, NVC x.2 := by
  cases iv with
  | pageMap cap sl ent vs =>
    simp only [performPageInvocation]
    exact (ik_bind (nvc_setCap sl hp) fun _ => by hv_auto) σ h
  | pageUnmap cap sl =>
    cases cap with
    | pageCap d p R mt sz m =>
      simp only [performPageInvocation]
      cases m with
      | none => exact (by hv_auto : IKH NVC _) σ h
      | some am =>
        cases mt with
        | vmVSpaceMap =>
          intro x ⟨y, hy, hx⟩
          have h1 := nvc_performPageInvocationUnmap _ sl σ ⟨h, hp⟩ y hy
          rw [Set.mem_singleton_iff.1 hx]; exact h1
        | _ => intro x ⟨y, hy, _⟩; exact (show False from hy).elim
    | _ => intro x hx; exact (show False from hx).elim
  | _ => simp only [performPageInvocation]; exact (by hv_auto : IKH NVC _) σ h

theorem nvc_maxFreeIndexUpdate {c : Cap} (h : ¬ IsVirtCap c) : ¬ IsVirtCap (maxFreeIndexUpdate c) := by
  cases c <;> simp only [maxFreeIndexUpdate] <;> first | exact h | exact id

theorem nvc_performAsidControlInvocation (iv : AsidControlInvocation) :
    IKH NVC (performAsidControlInvocation (Z := Unit) iv) := by
  cases iv with
  | makePool frame slot parent base =>
    simp only [performAsidControlInvocation]
    refine ik_bind (nvc_deleteObjects _ _) fun _ => ik_getCap_bind fun pcap σ hp => ?_
    intro h
    exact ikp_bind (fun hσ => nvc_setCap parent (nvc_maxFreeIndexUpdate (h parent pcap hp)) σ hσ)
      (fun _ => by hv_auto) h
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact nvc_performAsidControlInvocation _)

theorem nvc_performAsidPoolInvocation (iv : AsidPoolInvocation) :
    IKH NVC (performAsidPoolInvocation (Z := Unit) iv) := by
  unfold performAsidPoolInvocation; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact nvc_performAsidPoolInvocation _)

theorem nvc_performIoportControlInvocation (i : IoPortControlInvocation) :
    IKH NVC (performIoportControlInvocation (Z := Unit) i) := by
  unfold performIoportControlInvocation; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact nvc_performIoportControlInvocation _)

/-- The unmaps' slot facts at the perform (carried from the decode: `okd_fl4Decode_unmapAt`, `unmapOK_of`). -/
def ArchUnmapOK (σ : State Unit) : ArchInvocation → Prop
  | .invokePage (.pageUnmap c sl) => capOpt (σ.kheap sl.1) sl.2 = some (.archObjectCap c)
  | .invokePageTable (.pageTableUnmap c sl) => capOpt (σ.kheap sl.1) sl.2 = some c
  | .invokePageDirectory (.pageDirectoryUnmap c sl) => capOpt (σ.kheap sl.1) sl.2 = some c
  | .invokePDPT (.pdptUnmap c sl) => capOpt (σ.kheap sl.1) sl.2 = some c
  | _ => True

/-- `ArchUnmapOK` of a decoded invocation. -/
def UnmapOK (σ : State Unit) : Fl4Invocation → Prop
  | .invokeArchObject (.spec a) => ArchUnmapOK σ a
  | _ => True

theorem nvc_archPerform (i : ArchInvocation) (σ : State Unit) (h : NVC σ) (hm : ArchNV (.spec i))
    (hu : ArchUnmapOK σ i) : ∀ x ∈ ((archPerformInvocation (Z := Unit) i).run σ).1, NVC x.2 := by
  intro x hx
  obtain ⟨w, hw, rfl⟩ := mem_liftE_inv' hx
  show NVC w.2
  cases i <;> dsimp only at hw
  case invokePageTable oper =>
    obtain ⟨y, hy, hw⟩ := hw
    rw [Set.mem_singleton_iff.1 hw]
    exact nvc_performPageTableInvocation oper σ h (fun c sl e => by subst e; exact hu) y hy
  case invokePageDirectory oper =>
    obtain ⟨y, hy, hw⟩ := hw
    rw [Set.mem_singleton_iff.1 hw]
    exact nvc_performPageDirectoryInvocation oper σ h (fun c sl e => by subst e; exact hu) y hy
  case invokePDPT oper =>
    obtain ⟨y, hy, hw⟩ := hw
    rw [Set.mem_singleton_iff.1 hw]
    exact nvc_performPdptInvocation oper σ h (fun c sl e => by subst e; exact hu) y hy
  case invokePage oper =>
    refine nvc_performPageInvocation oper σ h ?_ w hw
    cases oper with
    | pageMap c _ _ _ => exact hm
    | pageUnmap c sl => exact hu
    | _ => trivial
  all_goals exact (by hv_auto : IKH NVC _) σ h w hw

/-! ## The page decoder's outcomes; the frame batch -/

/-- What the arch decoder's outcomes carry, state-free: a page map writes a non-virtualization cap (the
ported decoder builds a `vmVSpaceMap` cap), an unmap names the invoked slot and cap. -/
def ArchAt (sl0 : CslotPtr) (cap0 : ArchCap) : ArchInvocation → Prop
  | .invokePage (.pageMap c _ _ _) => ¬ IsVirtCap c
  | .invokePage (.pageUnmap c sl) => sl = sl0 ∧ c = cap0
  | .invokePageTable (.pageTableUnmap c sl) => sl = sl0 ∧ c = .archObjectCap cap0
  | .invokePageDirectory (.pageDirectoryUnmap c sl) => sl = sl0 ∧ c = .archObjectCap cap0
  | .invokePDPT (.pdptUnmap c sl) => sl = sl0 ∧ c = .archObjectCap cap0
  | _ => True

theorem okdAt_liftE_fail {ε α : Type} {σ : State Unit} {P : State Unit → α → Prop} :
    OkDAt σ P (NonDetE.liftE (ε := ε) (NonDet.fail : NonDet (State Unit) α)) := by
  intro a s h
  obtain ⟨w, hw, -⟩ := mem_liftE_inv' h
  exact (show False from hw).elim

macro "okd_arch" : tactic => `(tactic| repeat' (first
  | (intro _ _ _ hh; exact (show False from hh).elim)
  | exact okdAt_throw _
  | exact okdAt_liftE_fail
  | exact okdAt_returnOk trivial
  | exact okdAt_returnOk ⟨rfl, rfl⟩
  | exact okdAt_returnOk (fun h => h)
  | (refine okdAt_whenE_bind _ _ fun _ => ?_)
  | (refine okdAt_unlessE_bind _ _ fun _ => ?_)
  | (with_reducible refine okdAt_returnOk_bind ?_)
  | (with_reducible refine okdAt_bind fun _ _ _ => ?_)
  | (refine okdAt_ite _ ?_ ?_)
  | split
  | (dsimp only)))

set_option maxHeartbeats 4000000 in
theorem okd_decodePageInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap)
    (ex : List (Cap × CslotPtr)) (σ : State Unit) :
    OkDAt σ (fun _ i => ArchAt cte cap i) (decodePageInvocation (Z := Unit) label args cte cap ex) := by
  unfold decodePageInvocation; okd_arch

set_option maxHeartbeats 4000000 in
theorem okd_archDecode (label : Data) (args : List Data) (x : CapRef) (cte : CslotPtr) (cap : ArchCap)
    (ex : List (Cap × CslotPtr)) (σ : State Unit) :
    OkDAt σ (fun _ i => ArchAt cte cap i) (archDecodeInvocation (Z := Unit) label args x cte cap ex) := by
  unfold archDecodeInvocation
  split
  all_goals first
    | exact okd_decodePageInvocation _ _ _ _ _ _
    | (unfold decodePdptInvocation; okd_arch; done)
    | (unfold decodePageDirectoryInvocation; okd_arch; done)
    | (unfold decodePageTableInvocation; okd_arch; done)
    | (okd_arch; done)
    | (unfold decodePortInvocation; okd_arch; done)
    | (unfold decodeIoportControlInvocation; okd_arch; done)

theorem derive_page_nv {sl : CslotPtr} {c0 : Cap} (hp : isPageCap c0 = true) (r : CapRights) (σ : State Unit) :
    OkDAt σ (fun _ c => ¬ IsVirtCap c) (deriveCap (Z := Unit) sl (maskCap r c0)) := by
  cases c0 with
  | archObjectCap a =>
    cases a with
    | pageCap d p R mt sz m =>
      simp only [maskCap, capRightsUpdate, acapRightsUpdate, deriveCap, archDeriveCap]
      exact okdAt_returnOk (fun h => h)
    | _ => simp [isPageCap] at hp
  | _ => simp [isPageCap] at hp

/-- A `liftE` step with a σ-local post, then a continuation keeping `NVC`. -/
theorem nvc_liftE_bind {ε α β : Type} {m : NonDet (State Unit) α} {k : α → NonDetE (State Unit) ε β}
    {σ : State Unit} (hm : ∀ x ∈ (m σ).1, NVC x.2) (hk : ∀ a, IKHE NVC (k a)) :
    ∀ y ∈ ((NonDetE.liftE m >>= k).run σ).1, NVC y.2 := by
  intro y hy
  obtain ⟨z, hz, ⟨u, hu, hy⟩ | ⟨e, he, rfl⟩⟩ := mem_bindE_inv' hy
  · obtain ⟨w, hw, rfl⟩ := mem_liftE_inv' hz
    exact hk u _ (hm w hw) y hy
  · obtain ⟨w, -, rfl⟩ := mem_liftE_inv' hz; cases he

theorem nvc_fbMap (b : Fl4FrameBatchInvocation) (sl : CslotPtr) (v : Data) :
    IKHE NVC (fbMap (Z := Unit) b sl v) := by
  unfold fbMap
  intro σ h y hy
  obtain ⟨z, hz, ⟨c, hc, hy⟩ | ⟨e, he, rfl⟩⟩ := mem_bindE_inv' hy
  · obtain ⟨w, hw, rfl⟩ := mem_liftE_inv' hz
    obtain ⟨c0, s0⟩ := w
    obtain ⟨o, r⟩ := sl
    obtain ⟨e1, e2⟩ := vih_mem_getCap hw
    simp only at e1 e2 hc; subst e1; cases hc
    revert hy
    split
    · rename_i dev p R mt sz m
      intro hy
      obtain ⟨z1, hz1, ⟨u1, hu1, hy⟩ | ⟨e, he, rfl⟩⟩ := mem_bindE_inv' hy
      · have hs1 : NVC z1.2 := (ike_whenE _ (ike_throw _) : IKHE NVC _) s0 h z1 hz1
        have hz1' : hV z1.2 = hV s0 :=
          (ike_whenE _ (ike_throw _) : IKHE (fun x => hV x = hV s0) _) s0 rfl z1 hz1
        obtain ⟨r1, s1⟩ := z1
        simp only at hu1 hs1 hz1'; subst hu1
        obtain ⟨z2, hz2, ⟨iv, hiv, hy⟩ | ⟨e, he, rfl⟩⟩ := mem_bindE_inv' hy
        · obtain ⟨r2, s2⟩ := z2
          simp only at hiv; subst hiv
          have hs2 : NVC s2 := fbx_decodePageInvocation (P := NVC) _ _ _ _ _ s1 hs1 _ hz2
          have e2' : hV s2 = hV s1 :=
            fbx_decodePageInvocation (P := fun x => hV x = hV s1) _ _ _ _ _ s1 rfl _ hz2
          have hat := okd_decodePageInvocation _ _ _ _ _ s1 iv s2 hz2
          revert hy
          split
          · rename_i pi
            intro hy
            refine nvc_liftE_bind (fun x hx => nvc_performPageInvocation pi s2 hs2 ?_ x hx)
              (fun _ => ike_returnOk _) y hy
            cases pi with
            | pageMap c _ _ _ => exact hat
            | pageUnmap c sl' =>
              obtain ⟨rfl, rfl⟩ := hat
              show capOpt (s2.kheap o) r = _
              rw [hV_cap e2', hV_cap hz1']; exact e2
            | _ => trivial
          · intro hy; exact (ike_liftE ik_fail : IKHE NVC _) s2 hs2 y hy
        · exact fbx_decodePageInvocation (P := NVC) _ _ _ _ _ s1 hs1 z2 hz2
      · exact (ike_whenE _ (ike_throw _) : IKHE NVC _) s0 h z1 hz1
    · intro hy; exact (ike_throw _ : IKHE NVC _) s0 h y hy
  · obtain ⟨w, -, rfl⟩ := mem_liftE_inv' hz; cases he

theorem nvc_performFrameBatch (b : Fl4FrameBatchInvocation) : IKH NVC (performFrameBatch (Z := Unit) b) := by
  refine ik_performFrameBatchX (fun w => ?_) (hv_flushAll _ _)
  refine ik_fbEntryX_of b w fbx_lookupTargetSlot fbx_lookupSourceSlot fbx_ensureEmpty fbx_deriveCap
    (fun s c src dest c0 hs _ _ _ _ hpg hd => nvc_capInsert src dest (derive_page_nv hpg _ s c s hd) s hs)
    (fun sl v => nvc_fbMap b sl v) (fun sl => ?_) (fun _ _ _ _ => by unfold unmapPageUnflushed; hv_auto)
    (fun s dev p R _ sz _ sl hs _ => nvc_setCap (c := .archObjectCap (.pageCap dev p R .vmNoMap sz none)) sl (fun h => h) s hs)
  unfold fbDelX
  refine ike_liftE (ik_bind (fbx_ik_getCap _) fun c => ?_)
  split
  · exact ik_bind (fbx_isFinalCap _) fun _ => ik_bind (hv_archFinaliseCap _ _) fun _ => nvc_emptySlot _ _
  · exact ik_fail
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact nvc_performFrameBatch _)

theorem nvc_fl4ArchPerform (a : Fl4ArchInvocation) (σ : State Unit) (h : NVC σ) (hm : ArchNV a)
    (hu : ∀ i, a = .spec i → ArchUnmapOK σ i) :
    ∀ x ∈ ((fl4ArchPerformInvocation (Z := Unit) a).run σ).1, NVC x.2 := by
  cases a with
  | spec i => exact nvc_archPerform i σ h hm (hu i rfl)
  | frameBatch b => simp only [fl4ArchPerformInvocation]; exact ike_liftE (nvc_performFrameBatch b) σ h
  | _ => simp only [fl4ArchPerformInvocation]; exact (by hv_auto : IKHE (ε := Unit) NVC _) σ h

/-! ## The writers outside the invocation (vih3's G for `NVC`) -/

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact nvc_setIrqState _ _)

theorem nvc_archInvokeIrqControl (aic : ArchIrqControlInvocation) :
    IKHE NVC (archInvokeIrqControl (Z := Unit) aic) := by
  unfold archInvokeIrqControl; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact nvc_archInvokeIrqControl _)

theorem nvc_doReplyTransfer (sender reply : ObjRef) (grant : Bool) :
    IKH NVC (doReplyTransfer (Z := Unit) sender reply grant) := by
  unfold doReplyTransfer; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact nvc_doReplyTransfer _ _ _)

theorem nvc_handleFault (thread : ObjRef) (ex : Fault) : IKH NVC (handleFault (Z := Unit) thread ex) := by
  unfold handleFault; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact nvc_handleFault _ _)

set_option maxHeartbeats 4000000 in
theorem nvc_receiveIpc (thread : ObjRef) (cap : Cap) (isBlocking : Bool) (replyCap : Cap) :
    IKH NVC (receiveIpc (Z := Unit) thread cap isBlocking replyCap) := by
  unfold receiveIpc; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact nvc_receiveIpc _ _ _ _)

theorem nvc_handleRecv (isBlocking canReply : Bool) : IKH NVC (handleRecv (Z := Unit) isBlocking canReply) := by
  unfold handleRecv; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact nvc_handleRecv _ _)

theorem nvc_handleYield : IKH NVC (handleYield (Z := Unit)) := by
  unfold handleYield; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact nvc_handleYield)

theorem nvc_invokeIrqControl (a0 : IrqControlInvocation) : IKHE NVC (invokeIrqControl (Z := Unit) a0) := by
  unfold invokeIrqControl; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact nvc_invokeIrqControl _)

theorem nvc_invokeFl4IrqControl (a0 : Fl4IrqControlInvocation) :
    IKHE NVC (invokeFl4IrqControl (Z := Unit) a0) := by
  unfold invokeFl4IrqControl; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact nvc_invokeFl4IrqControl _)

theorem nvc_preemptionPath : IKH NVC (preemptionPath (Z := Unit)) := by
  unfold preemptionPath; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact nvc_preemptionPath)

/-! ## The perform -/

set_option maxHeartbeats 8000000 in
/-- **Every perform keeps `NVC`**, given the carried decode facts: `InvNV` (VirtNvInv), `InvTcbNV` (the IPC
buffer cap and the scheduling fault handler of a TCB invocation) and `UnmapOK` (an unmap's slot still holds the
invoked cap). -/
theorem nvc_fl4Perform (blk call don : Bool) (inv : Fl4Invocation) (σ : State Unit) (h : NVC σ)
    (hi : InvNV inv) (ht : InvTcbNV inv) (hu : UnmapOK σ inv) :
    ∀ x ∈ ((fl4PerformInvocation (Z := Unit) blk call don inv).run σ).1, NVC x.2 := by
  cases inv with
  | invokeUntyped ui =>
    simp only [fl4PerformInvocation]
    exact (ike_bind (nvc_invokeUntypedWith _ ui hi) fun _ => ike_returnOk _) σ h
  | invokeTCB i => simp only [fl4PerformInvocation]; exact nvc_invokeTcb i hi ht σ h
  | invokeCNode i =>
    simp only [fl4PerformInvocation]
    exact (ike_bind (nvc_invokeCnode i hi) fun _ => ike_returnOk _) σ h
  | invokeIRQHandler i =>
    simp only [fl4PerformInvocation]
    refine (ike_bind (ike_liftE (nvc_invokeIrqHandler i ?_)) fun _ => ike_returnOk _) σ h
    intro irq c sl e; subst e; exact hi
  | invokeArchObject a =>
    simp only [fl4PerformInvocation]
    exact nvc_fl4ArchPerform a σ h hi (fun i e => by subst e; exact hu)
  | _ => exact (show IKHE (ε := Unit) NVC (fl4PerformInvocation (Z := Unit) blk call don _) from by
      simp only [fl4PerformInvocation]; hv_auto) σ h

/-! ## The kernel shell outside the invocation -/

set_option maxHeartbeats 8000000 in
theorem nvc_handleEvent_other (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) :
    IKHE (ε := Unit) NVC (handleEvent (Z := Unit) ev) := by
  cases ev with
  | syscallEvent c => exact absurd rfl (h c)
  | _ => simp only [handleEvent]; hv_auto

theorem nvc_kernelExit : IKH NVC (do fl4Awaken (Z := Unit); schedule (Z := Unit); activateThread (Z := Unit)) := by
  hv_auto

/-! ## The decoder's carry for `InvTcbNV`, `ArchNV` and `UnmapOK` -/

theorem okdAt_bindQ {ε α β : Type} {σ : State Unit} {Q : State Unit → α → Prop} {P : State Unit → β → Prop}
    {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β} (hm : OkDAt σ Q m)
    (hg : ∀ a s, Q s a → OkDAt s P (g a)) : OkDAt σ P (m >>= g) :=
  okdAt_bind fun a s h => hg a s (hm a s h)

theorem okdAt_throw_bind {ε α β : Type} {σ : State Unit} {P : State Unit → β → Prop} (e : ε)
    {g : α → NonDetE (State Unit) ε β} : OkDAt σ P (NonDetE.throwError e >>= g) :=
  okdAt_bind fun _ _ h => (okdAt_throw (P := fun _ _ => False) e _ _ h).elim

/-- `derive_cap` returns a frame cap only unmapped (`vmNoMap`). -/
theorem okd_deriveCap_page (sl : CslotPtr) (c : Cap) (σ : State Unit) :
    OkDAt σ (fun _ c' => ∀ d p R mt sz m, c' = .archObjectCap (.pageCap d p R mt sz m) → mt = .vmNoMap)
      (deriveCap (Z := Unit) sl c) := by
  cases c with
  | archObjectCap a =>
    simp only [deriveCap]; unfold archDeriveCap
    split <;> first
      | exact okdAt_throw _
      | exact okdAt_returnOk (fun _ _ _ _ _ _ e => by cases e; rfl)
      | exact okdAt_returnOk (fun _ _ _ _ _ _ e => by cases e)
  | untypedCap d b n f =>
    simp only [deriveCap]
    exact okdAt_bind fun _ _ _ => okdAt_returnOk (fun _ _ _ _ _ _ e => by cases e)
  | _ => simp only [deriveCap]; exact okdAt_returnOk (fun _ _ _ _ _ _ e => by cases e)

theorem okd_decodeSetIpcBuffer_nv (args : List Data) (cap : Cap) (slot : CslotPtr) (excs : List (Cap × CslotPtr))
    (σ : State Unit) :
    OkDAt σ (fun _ ti => BufNV ti.tcNewBuffer ∧ TcbNV ti) (decodeSetIpcBuffer (Z := Unit) args cap slot excs) := by
  unfold decodeSetIpcBuffer
  refine okdAt_whenE_bind _ _ fun _ => ?_
  refine okdAt_whenE_bind _ _ fun _ => ?_
  refine okdAt_returnOk_bind ?_
  refine okdAt_returnOk_bind ?_
  split
  rename_i bcap bslot _
  refine okdAt_bindQ (Q := fun _ nb => ∀ c s, nb = some (c, s) → ¬ IsVirtCap c) ?_ fun nb s hnb => ?_
  · refine okdAt_ite _ (okdAt_returnOk fun _ _ h => by cases h) ?_
    refine okdAt_bindQ (okd_deriveCap_page bslot bcap _) fun bc s hbc => ?_
    cases bc with
    | archObjectCap a =>
      cases a with
      | pageCap d p R mt sz m =>
        have := hbc d p R mt sz m rfl; subst this
        cases d
        · simp only [checkValidIpcBuffer]
          refine okdAt_bind fun _ _ _ => ?_
          exact okdAt_returnOk fun c s e => by cases e; exact fun h => h
        · simp only [checkValidIpcBuffer]; exact okdAt_throw_bind _
      | _ => simp only [checkValidIpcBuffer]; exact okdAt_throw_bind _
    | _ => simp only [checkValidIpcBuffer]; exact okdAt_throw_bind _
  · refine okdAt_returnOk ⟨?_, ?_⟩ <;>
    (rcases nb with _ | ⟨c, s'⟩
     · trivial
     · exact hnb c s' rfl)

theorem okd_decodeTcbConfigure_nv (args : List Data) (cap : Cap) (slot : CslotPtr)
    (excaps : List (Cap × CslotPtr)) (σ : State Unit) :
    OkDAt σ (fun _ ti => TcbNV ti) (decodeTcbConfigure (Z := Unit) args cap slot excaps) := by
  unfold decodeTcbConfigure
  refine okdAt_whenE_bind _ _ fun _ => ?_
  refine okdAt_whenE_bind _ _ fun _ => ?_
  refine okdAt_returnOk_bind ?_
  refine okdAt_returnOk_bind ?_
  refine okdAt_bindQ (okd_decodeSetIpcBuffer_nv _ _ _ _ _) fun sp s hsp => ?_
  refine okdAt_bind fun _ _ _ => ?_
  exact okdAt_returnOk hsp.1

theorem okd_decodeSetSchedParams_nv (args : List Data) (cap : Cap) (slot : CslotPtr)
    (excaps : List (Cap × CslotPtr)) (σ : State Unit) :
    OkDAt σ (fun _ ti => TcbNV ti) (decodeSetSchedParams (Z := Unit) args cap slot excaps) := by
  unfold decodeSetSchedParams
  repeat' (first
    | exact okdAt_throw _
    | (refine okdAt_bindQ (Fl4Proofs.P3.VirtTcbOK.okd_checkHandlerEp _ _ _) fun fh _ hfh => okdAt_returnOk ?_
       intro c src e; cases e; exact hfh)
    | (refine okdAt_whenE_bind _ _ fun _ => ?_)
    | (with_reducible refine okdAt_returnOk_bind ?_)
    | (with_reducible refine okdAt_bind fun _ _ _ => ?_)
    | split)

theorem okd_decodeSetPriority_nv (args : List Data) (cap : Cap) (slot : CslotPtr)
    (excaps : List (Cap × CslotPtr)) (σ : State Unit) :
    OkDAt σ (fun _ ti => TcbNV ti) (decodeSetPriority (Z := Unit) args cap slot excaps) := by
  unfold decodeSetPriority
  refine okdAt_whenE_bind _ _ fun _ => ?_
  refine okdAt_returnOk_bind ?_
  dsimp only
  split
  · refine okdAt_returnOk_bind ?_
    refine okdAt_bind fun _ _ _ => ?_
    exact okdAt_returnOk Fl4Proofs.P3.VirtTcbOK.capOK_none
  · exact okdAt_throw_bind _

theorem okd_decodeSetMcpriority_nv (args : List Data) (cap : Cap) (slot : CslotPtr)
    (excaps : List (Cap × CslotPtr)) (σ : State Unit) :
    OkDAt σ (fun _ ti => TcbNV ti) (decodeSetMcpriority (Z := Unit) args cap slot excaps) := by
  unfold decodeSetMcpriority
  refine okdAt_whenE_bind _ _ fun _ => ?_
  refine okdAt_returnOk_bind ?_
  dsimp only
  split
  · refine okdAt_returnOk_bind ?_
    refine okdAt_bind fun _ _ _ => ?_
    exact okdAt_returnOk Fl4Proofs.P3.VirtTcbOK.capOK_none
  · exact okdAt_throw_bind _

macro "tk_cap" : tactic => `(tactic| repeat' (first
  | exact okdAt_throw _
  | exact okdAt_returnOk trivial
  | exact okdAt_returnOk Fl4Proofs.P3.VirtTcbOK.capOK_none
  | (refine okdAt_ite _ ?_ ?_)
  | (with_reducible refine okdAt_bind fun _ _ _ => ?_)
  | split))

/-- **The TCB decoder's outcomes are `TcbNV`.** -/
theorem okd_decodeTcb_nv (label : Data) (args : List Data) (cap : Cap) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) (σ : State Unit) :
    OkDAt σ (fun _ ti => TcbNV ti) (decodeTcbInvocation (Z := Unit) label args cap slot excs) := by
  unfold decodeTcbInvocation
  split
  all_goals first
    | (with_reducible exact okd_decodeTcbConfigure_nv _ _ _ _ _)
    | (with_reducible exact okd_decodeSetSchedParams_nv _ _ _ _ _)
    | (with_reducible exact okdAt_mono' (okd_decodeSetIpcBuffer_nv _ _ _ _ _) fun _ _ h => h.2)
    | ((with_reducible refine okdAt_returnOk ?_); trivial)
    | (with_reducible exact okdAt_throw _)
    | (unfold decodeSetSpace; tk_cap; done)
    | (unfold decodeSetTimeoutEp; tk_cap; done)
    | (unfold decodeReadRegisters; tk_cap; done)
    | (unfold decodeWriteRegisters; tk_cap; done)
    | (unfold decodeCopyRegisters; tk_cap; done)
    | (with_reducible exact okd_decodeSetPriority_nv _ _ _ _ _)
    | (with_reducible exact okd_decodeSetMcpriority_nv _ _ _ _ _)
    | (unfold decodeBindNotification; tk_cap; done)
    | (unfold decodeUnbindNotification; tk_cap; done)
    | (unfold decodeSetTlsBase; tk_cap; done)
    | (unfold decodeSetFlags; tk_cap; done)

/-- An unmap of a decoded invocation names the invoked slot and cap (state-free; `unmapOK_of`). -/
def UnmapAt (sl : CslotPtr) (cap : Cap) : Fl4Invocation → Prop
  | .invokeArchObject (.spec a) => ∃ ac, cap = .archObjectCap ac ∧ ArchAt sl ac a
  | _ => True

theorem okd_fl4DecodeTcb_nv (label : Data) (args : List Data) (cap : Cap) (slot : CslotPtr)
    (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) (σ : State Unit) :
    OkDAt σ (fun _ i => InvTcbNV i ∧ ∀ sl c, UnmapAt sl c i)
      (fl4DecodeTcbInvocation (Z := Unit) label args cap slot excaps buffer) := by
  unfold fl4DecodeTcbInvocation
  split
  · exact okdAt_liftME fun _ _ _ => ⟨trivial, fun _ _ => trivial⟩
  · split
    · exact okdAt_liftME fun _ _ _ => ⟨trivial, fun _ _ => trivial⟩
    · exact okdAt_liftME (okdAt_mono' (okd_decodeTcb_nv _ _ _ _ _ σ) fun _ _ h => ⟨h, fun _ _ => trivial⟩)

theorem okd_fl4ArchDecode_at (label : Data) (args : List Data) (x : CapRef) (cte : CslotPtr) (cap : ArchCap)
    (ex : List (Cap × CslotPtr)) (σ : State Unit) :
    OkDAt σ (fun _ a => ∀ i, a = .spec i → ArchAt cte cap i)
      (fl4ArchDecodeInvocation (Z := Unit) label args x cte cap ex) := by
  unfold fl4ArchDecodeInvocation
  repeat' (first
    | exact okdAt_liftME fun i s h i' e => by cases e; exact okd_archDecode _ _ _ _ _ _ _ i s h
    | exact okdAt_liftME fun _ _ _ i e => by cases e
    | (refine okdAt_ite _ ?_ ?_)
    | split)

theorem archNV_of_at {cte : CslotPtr} {cap : ArchCap} {a : Fl4ArchInvocation}
    (h : ∀ i, a = .spec i → ArchAt cte cap i) : ArchNV a := by
  cases a with
  | spec i =>
    have hi := h i rfl
    cases i with
    | invokePage pi => cases pi with
      | pageMap c _ _ _ => exact hi
      | _ => trivial
    | _ => trivial
  | _ => trivial

/-- **`ArchNV` of the arch decoder's outcomes** (the page-map carry). -/
theorem okd_fl4ArchDecode_nv (label : Data) (args : List Data) (x : CapRef) (cte : CslotPtr) (cap : ArchCap)
    (ex : List (Cap × CslotPtr)) (σ : State Unit) :
    OkDAt σ (fun _ a => ArchNV a) (fl4ArchDecodeInvocation (Z := Unit) label args x cte cap ex) :=
  okdAt_mono' (okd_fl4ArchDecode_at label args x cte cap ex σ) fun _ _ h => archNV_of_at h

set_option maxHeartbeats 4000000 in
/-- **The dispatcher's outcomes: `InvTcbNV` and `UnmapAt` of the invoked slot and cap.** -/
theorem okd_fl4Decode_nvK1 (fp : Bool) (label : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr)
    (cap : Cap) (ex : List (Cap × CslotPtr)) (b : Option ObjRef) (σ : State Unit) :
    OkDAt σ (fun _ i => InvTcbNV i ∧ UnmapAt sl cap i)
      (fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex b) := by
  cases cap with
  | threadCap p =>
    simp only [fl4DecodeInvocation]
    split
    · exact okdAt_throw _
    · exact okdAt_mono' (okd_fl4DecodeTcb_nv _ _ _ _ _ _ σ) fun _ _ h => ⟨h.1, h.2 _ _⟩
  | archObjectCap ac =>
    simp only [fl4DecodeInvocation]
    exact okdAt_liftME fun a s h => ⟨trivial, by
      cases a with
      | spec i => exact ⟨ac, rfl, okd_fl4ArchDecode_at _ _ _ _ _ _ σ (.spec i) s h i rfl⟩
      | _ => trivial⟩
  | _ =>
    simp only [fl4DecodeInvocation]
    repeat' (first
      | exact okdAt_throw _
      | exact okdAt_returnOk ⟨trivial, trivial⟩
      | exact okdAt_liftME fun _ _ _ => ⟨trivial, trivial⟩
      | split)

theorem unmapOK_of {sl : CslotPtr} {cap : Cap} {inv : Fl4Invocation} {σ : State Unit} (hU : UnmapAt sl cap inv)
    (hc : capOpt (σ.kheap sl.1) sl.2 = some cap) : UnmapOK σ inv := by
  cases inv with
  | invokeArchObject a =>
    cases a with
    | spec i =>
      obtain ⟨ac, rfl, h⟩ := hU
      cases i with
      | invokePage pi =>
        cases pi with
        | pageUnmap c sl' => obtain ⟨rfl, rfl⟩ := h; exact hc
        | _ => trivial
      | invokePageTable pi =>
        cases pi with
        | pageTableUnmap c sl' => obtain ⟨rfl, rfl⟩ := h; exact hc
        | _ => trivial
      | invokePageDirectory pi =>
        cases pi with
        | pageDirectoryUnmap c sl' => obtain ⟨rfl, rfl⟩ := h; exact hc
        | _ => trivial
      | invokePDPT pi =>
        cases pi with
        | pdptUnmap c sl' => obtain ⟨rfl, rfl⟩ := h; exact hc
        | _ => trivial
      | _ => trivial
    | _ => trivial
  | _ => trivial

/-- `UnmapOK` survives every step that keeps `hV` (the decode, the restart state write). -/
theorem unmapOK_of_hV {σ σ' : State Unit} {inv : Fl4Invocation} (e : hV σ' = hV σ) (h : UnmapOK σ inv) :
    UnmapOK σ' inv := by
  cases inv with
  | invokeArchObject a =>
    cases a with
    | spec i =>
      cases i with
      | invokePage pi => cases pi with
        | pageUnmap c sl' => show capOpt _ _ = _; rw [hV_cap e]; exact h
        | _ => trivial
      | invokePageTable pi => cases pi with
        | pageTableUnmap c sl' => show capOpt _ _ = _; rw [hV_cap e]; exact h
        | _ => trivial
      | invokePageDirectory pi => cases pi with
        | pageDirectoryUnmap c sl' => show capOpt _ _ = _; rw [hV_cap e]; exact h
        | _ => trivial
      | invokePDPT pi => cases pi with
        | pdptUnmap c sl' => show capOpt _ _ = _; rw [hV_cap e]; exact h
        | _ => trivial
      | _ => trivial
    | _ => trivial
  | _ => trivial

end

end Fl4Proofs.P3.VirtNvK1
