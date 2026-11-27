/-
P3x for virtualization, spec side (line virt, gen 5; proofs/VIRT-PLAN.md §10 "Remaining (R7)" (e)):
**on `NVC` states the virtualization routes reduce to the three label / gate conditions**, which shrinks gen 4's
scope premise `OffRoute` / `OffRouteS` [S].

* `Route3 fp label args cap excaps`: the three routes that exist without a virtualization cap — label 60
  (`fl4PageMapEptLabel`) on a frame cap, label 88 (`fl4SetEptRootLabel`) on a thread cap in the second phase, the
  VT-x retype gate (`untypedVtxGate`) on an untyped cap.
* `route3_of_virtRoute`: if the invoked cap and the extra caps are not virtualization caps, `VirtRoute` implies
  `Route3` (the VCPU / EPT caps, the EPT-mapped frame cases and the ASID-pool assign of an EPT root all need a
  virtualization cap: `swer_virt`).
* `okn_lookupPart`: the looked-up cap and extra caps of the invocation path are not virtualization caps on an
  `NVC` state (VirtNvcW's carry).
* `OffRoute3` / `OffRouteS3`: `OffRoute` / `OffRouteS` with `Route3` in place of `VirtRoute`;
  `offRoute_of3`, `offRouteS_of3` (on `NVC` states the reduced form gives gen 4's).
* **`fl4CallKernelV_eqNR3`**: `fl4CallKernelV onCore rep ev σ = fl4CallKernel rep ev σ` on an `NR` state, given
  the reduced premise below (gen 5's `fl4CallKernelV_eqNR'` with `hoff` shrunk).

Named premise:
* **`hoff3 : ∀ c, ev = .syscallEvent c → ∀ t, EntryPt σ t → OffRouteS3 c t` [S]** (syscall events only): at every
  decode point the syscall reaches, (1) the input is not on one of the three routes `Route3` (pure label / gate
  condition on the looked-up cap's kind, the label and the message words; the on-route inputs are the route-B
  posts `decOKV_frame60_noVirt`, `decOKV_thread88_noVirt`, `decOKV_untyped_vtxGate`), and (2) every invocation
  the ported decoder returns is `InvOK` (VirtR7e: retype type ≠ VCPU, TCB caps `TcbCapsOK`) — part (2) is not yet
  derived from the decoder (open item).

No [J]/[P]/[W]. New file only.
-/
import Fl4Proofs.P3.VirtR7eK2
open Classical

namespace Fl4Proofs.P3.VirtOffNv
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvV Fl4Proofs.P3.SInvL Fl4Proofs.P3.SInvDom
  Fl4Proofs.P3.VirtR7b Fl4Proofs.P3.VirtR7e Fl4Proofs.P3.VirtR7eK Fl4Proofs.P3.VirtNvcW Fl4Proofs.P3.VirtR7eK2

noncomputable section

set_option maxHeartbeats 1000000

/-- **The three routes without a virtualization cap** (module docstring). -/
def Route3 (fp : Bool) (label : Data) (args : List Data) (cap : Cap) (excaps : List (Cap × CslotPtr)) : Prop :=
  match cap with
  | .archObjectCap (.pageCap _ _ _ _ _ _) => dataToNat label = fl4PageMapEptLabel
  | .threadCap _ => ¬ fp ∧ dataToNat label = fl4SetEptRootLabel
  | .untypedCap _ _ _ _ => untypedVtxGate label args (excaps.map Prod.fst)
  | _ => False

theorem swer_virt {ex : List (Cap × CslotPtr)} (h : startsWithEptRoot ex = true) : ∃ c ∈ ex, IsVirtCap c.1 := by
  match ex, h with
  | (c, sl) :: t, h =>
    refine ⟨(c, sl), List.mem_cons_self .., ?_⟩
    cases c with
    | archObjectCap a => cases a <;> first | trivial | (simp [startsWithEptRoot] at h)
    | _ => simp [startsWithEptRoot] at h
  | [], h => simp [startsWithEptRoot] at h

/-- **Off virtualization caps, `VirtRoute` is `Route3`.** -/
theorem route3_of_virtRoute {fp : Bool} {label : Data} {args : List Data} {cap : Cap}
    {excaps : List (Cap × CslotPtr)} (hc : ¬ IsVirtCap cap) (he : ∀ c ∈ excaps, ¬ IsVirtCap c.1)
    (h : VirtRoute fp label args cap excaps) : Route3 fp label args cap excaps := by
  cases cap with
  | archObjectCap a =>
    cases a with
    | vcpuCap _ => exact (hc trivial).elim
    | eptCap _ _ _ => exact (hc trivial).elim
    | pageCap d r R mt sz m =>
      rcases h with h | ⟨e, _, _⟩ | ⟨e, _, _⟩
      · exact h
      · subst e; exact (hc trivial).elim
      · subst e; exact (hc trivial).elim
    | asidPoolCap _ _ =>
      obtain ⟨c, hm, hv⟩ := swer_virt h.2
      exact (he c hm hv).elim
    | _ => exact (h : False).elim
  | threadCap _ => exact h
  | untypedCap _ _ _ _ => exact h
  | _ => exact (h : False).elim

/-- The invocation path's looked-up cap and extra caps are not virtualization caps. -/
theorem okn_lookupPart {σ0 : State Unit} (hv : NVC σ0) (t : ObjRef) (cptr : CapRef) (info : MessageInfo) :
    OkV σ0 (fun a : CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef =>
        ¬ IsVirtCap a.2.1 ∧ ∀ c ∈ a.2.2.1, ¬ IsVirtCap c.1)
      (lookupPart t cptr info) := by
  unfold lookupPart
  refine okv_bind (okn_lookupCap hv t cptr _ false) fun p hp => ?_
  obtain ⟨cap, slot⟩ := p
  refine okv_bind (okv_frame fun v => ike_liftE (P := fun s => hV s = v) (hv_lookupIpcBuffer _ _)) fun b _ => ?_
  exact okv_bind (okn_lookupExtraCaps hv t b info) fun ex hex => okv_returnOk ⟨hp, hex⟩

/-- **`OffRoute` with the three routes** (the reduced [S] premise, module docstring). -/
def OffRoute3 (fp : Bool) (cptr : CapRef) (s : State Unit) : Prop :=
  ∀ info a args u, DecPt cptr s info a args u →
    ¬ Route3 fp info.miLabel args a.2.1 a.2.2.1 ∧
    ∀ i v, ((Except.ok i : Except SyscallError Fl4Invocation), v) ∈
      (ExceptT.run (fl4DecodeInvocation (Z := Unit) fp info.miLabel args cptr a.1 a.2.1 a.2.2.1 a.2.2.2) u).1 →
      InvOK i

theorem offRoute_of3 {fp : Bool} {cptr : CapRef} {s : State Unit} (hs : NVC s) (h : OffRoute3 fp cptr s) :
    OffRoute fp cptr s := by
  intro info a args u hd
  obtain ⟨s1, t, h1, ha, hu⟩ := hd
  have n1 : NVC s1 := hv_getMessageInfo (P := NVC) _ s hs _ h1
  obtain ⟨-, hc, he⟩ := okn_lookupPart n1 s.curThread cptr info s1 rfl a t ha
  obtain ⟨hr, hi⟩ := h info a args u ⟨s1, t, h1, ha, hu⟩
  exact ⟨fun hv => hr (route3_of_virtRoute hc he hv), hi⟩

/-- **`OffRouteS` with the three routes.** -/
def OffRouteS3 (c : Syscall) (t : State Unit) : Prop :=
  ∀ reg, sysReg c = some reg → ∀ cptr t', (cptr, t') ∈ (getCapReg (Z := Unit) reg t).1 → ∀ fp, OffRoute3 fp cptr t'

theorem offRouteS_of3 {c : Syscall} {t : State Unit} (ht : NVC t) (h : OffRouteS3 c t) : OffRouteS c t :=
  fun reg hr cptr t' hm fp => offRoute_of3 (hv_getCapReg (P := NVC) reg t ht _ hm) (h reg hr cptr t' hm fp)

/-- **R7 (e) with the reduced scope**: the extended kernel step is the ported one on an `NR` state (premise
`hoff3` [S], module docstring). -/
theorem fl4CallKernelV_eqNR3 (onCore : ObjRef → Bool) (rep : Bool) (ev : Event) {σ : State Unit} (hs : NR σ)
    (hoff3 : ∀ c, ev = .syscallEvent c → ∀ t, EntryPt σ t → OffRouteS3 c t) :
    fl4CallKernelV (Z := Unit) onCore rep ev σ = fl4CallKernel rep ev σ :=
  fl4CallKernelV_eqNR' onCore rep ev hs fun c hc t ht => offRouteS_of3 (nvc_entryPt hs.1.1 ht) (hoff3 c hc t ht)

end

end Fl4Proofs.P3.VirtOffNv
