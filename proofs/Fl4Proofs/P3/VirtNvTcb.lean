/-
P3x for virtualization, spec side (line virt, gen 4; proofs/VIRT-PLAN.md §10 "Remaining (R7)" (b)):
**the CNode and TCB performs of the extended kernel are the ported ones on `NV` states**, and the TCB installs
keep `NV`.

Spec: `Fl4Spec/Ext/VirtFinalise` (`invokeCnodeV`, l4v `CSpace_A.invoke_cnode` with `capRevokeV` / `capDeleteV`;
`installTcbCapV` / `installTcbFrameCapV` / `invokeTcbV`, l4v `Tcb_A.install_tcb_cap` / `install_tcb_frame_cap` /
`invoke_tcb` with `capDeleteV`), against the ported `invokeCnode`, `installTcbCap`, `installTcbFrameCap`,
`invokeTcb`. Nothing of the port changes.

* `invokeCnodeV_eq`, `installTcbCapV_eq`, `installTcbFrameCapV_eq`: on an `NV` state (VirtR7b) these are the
  ported ones (from `capRevokeV_eq` / `capDeleteV_eq`; the continuations are the same).
* `NV` writers: `nvc_setUntypedCapAsFull` (the written cap is the untyped source cap made full),
  `nvc_capInsert` (a non-virtualization cap), `ik_installTcbCap` (generic in the invariant), **`nv_installTcbCap`**
  (`install_tcb_cap` of a non-virtualization cap keeps `NV`).
* **`invokeTcbV_eq`**: on an `NV` state `invokeTcbV = invokeTcb`, given `TcbCapsOK` of the invocation.
* `CapOK o` / `TcbCapsOK i`: the caps a `ThreadControlCaps` installs in slots 3, 4, 0, 1 are not virtualization
  caps. **Named premise `hc : TcbCapsOK i` [S]**: on the routes this module covers it is a decode fact (the
  installed caps are looked up in slots of an `NV` state and derived; `derive_cap` / `update_cap_data` of a
  non-virtualization cap is not one), not carried from the decoder here — an open item of the composition (the
  vih3 `OkV` carry pattern, SpecInvValidIrqHandlersY, applies).

Premises: the state fact `NV`; `hc` [S] for `invokeTcbV_eq` only. No [J]/[P]/[W]. New file only.
-/
import Fl4Proofs.P3.VirtR7b
open Classical

namespace Fl4Proofs.P3.VirtNvTcb
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvL Fl4Proofs.P3.SInvTY Fl4Proofs.P3.VirtR7b
open Fl4Proofs.P3.SInvV (hv_getCap)

noncomputable section

set_option maxHeartbeats 2000000

/-! ## CNode -/

/-- **`invoke_cnode`** on an `NV` state. -/
theorem invokeCnodeV_eq (i : CnodeInvocation) {s : State Unit} (hs : NV s) :
    invokeCnodeV (Z := Unit) i s = invokeCnode i s := by
  cases i with
  | revokeCall sl => exact capRevokeV_eq sl hs
  | deleteCall sl => exact capDeleteV_eq sl hs
  | _ => rfl

/-! ## The TCB installs -/

theorem installTcbCapV_eq (target : ObjRef) (slot : CslotPtr) (n : Nat) (so : Option (Cap × CslotPtr))
    {s : State Unit} (hs : NV s) :
    installTcbCapV (Z := Unit) target slot n so s = installTcbCap target slot n so s := by
  cases so with
  | none => rfl
  | some p =>
    obtain ⟨c, src⟩ := p
    show ExceptT.run (installTcbCapV (Z := Unit) target slot n (some (c, src))) s =
      ExceptT.run (installTcbCap (Z := Unit) target slot n (some (c, src))) s
    unfold installTcbCapV installTcbCap
    exact nde_bind_congr (capDeleteV_eq _ hs) fun _ _ _ => rfl

theorem installTcbFrameCapV_eq (target : ObjRef) (slot : CslotPtr)
    (buffer : Option (VSpaceRef × Option (Cap × CslotPtr))) {s : State Unit} (hs : NV s) :
    installTcbFrameCapV (Z := Unit) target slot buffer s = installTcbFrameCap target slot buffer s := by
  cases buffer with
  | none => rfl
  | some p =>
    obtain ⟨ptr, frame⟩ := p
    show ExceptT.run (installTcbFrameCapV (Z := Unit) target slot (some (ptr, frame))) s =
      ExceptT.run (installTcbFrameCap (Z := Unit) target slot (some (ptr, frame))) s
    unfold installTcbFrameCapV installTcbFrameCap
    exact nde_bind_congr (capDeleteV_eq _ hs) fun _ _ _ => rfl

/-! ## `NV` across `cap_insert` and `install_tcb_cap` -/

theorem nvc_setUntypedCapAsFull (srcCap newCap : Cap) (sl : CslotPtr) (h : ¬ IsVirtCap srcCap) :
    IK NVC (setUntypedCapAsFull (Z := Unit) srcCap newCap sl) := by
  unfold setUntypedCapAsFull
  split
  · refine nvc_setCap sl ?_
    cases srcCap <;> simp only [maxFreeIndexUpdate] <;> first | exact h | exact id
  · exact ik_pure' _

/-- **`cap_insert` of a non-virtualization cap keeps `NVC`** (the source cap is read from a slot). -/
theorem nvc_capInsert {c : Cap} (src dst : CslotPtr) (hc : ¬ IsVirtCap c) :
    IK NVC (capInsert (Z := Unit) c src dst) := by
  unfold capInsert
  intro σ
  refine ikp_getCap_bind fun sc hsc => ?_
  intro hσ x hx
  refine (?_ : IK NVC _) σ hσ x hx
  refine ik_bind (ik_pure' _) fun _ => ik_bind (hv_getCap (P := NVC) _) fun _ =>
    ik_bind (ik_assert _) fun _ => ik_bind (nvc_setUntypedCapAsFull _ _ _ (hσ src sc hsc)) fun _ =>
    ik_bind (nvc_setCap _ hc) fun _ => ?_
  nvc_tail

/-- `install_tcb_cap` of a cap keeps any invariant kept by its pieces. -/
theorem ik_installTcbCap {P : State Unit → Prop} {c : Cap} (target : ObjRef) (slot src : CslotPtr) (n : Nat)
    (hd : ∀ sl, IKE (ε := Unit) P (capDelete (Z := Unit) sl)) (hi : ∀ src dst, IK P (capInsert (Z := Unit) c src dst))
    (hg : ∀ sl, IK P (getCap (Z := Unit) sl)) :
    IKE P (installTcbCap (Z := Unit) target slot n (some (c, src))) := by
  unfold installTcbCap
  refine ike_bind (hd _) fun _ => ?_
  unfold NonDetE.unlessE
  split
  · exact ike_returnOk _
  · unfold checkCapAt
    exact ike_liftE (ik_bind (hg _) fun _ => ik_when _ (ik_bind (hg _) fun _ => ik_when _ (hi _ _)))

/-- A `ThreadControlCaps` cap argument that is not a virtualization cap. -/
def CapOK (o : Option (Cap × CslotPtr)) : Prop := ∀ c src, o = some (c, src) → ¬ IsVirtCap c

/-- **`install_tcb_cap` of a non-virtualization cap keeps `NV`.** -/
theorem nv_installTcbCap (target : ObjRef) (slot : CslotPtr) (n : Nat) {o : Option (Cap × CslotPtr)}
    (ho : CapOK o) : Pres NV (ExceptT.run (installTcbCap (Z := Unit) target slot n o)) := by
  cases o with
  | none =>
    intro s hs x hx
    rw [Set.mem_singleton_iff.1 hx]
    exact hs
  | some p =>
    obtain ⟨c, src⟩ := p
    have hc := ho c src rfl
    intro s hs x hx
    exact ⟨ik_installTcbCap (P := NVC) target slot src n (fun sl => nvc_capDelete sl)
        (fun a b => nvc_capInsert a b hc) (fun sl => hv_getCap (P := NVC) sl) s hs.1 x hx,
      ik_installTcbCap (P := TIn NVT) target slot src n (fun sl => ty_capDelete sl)
        (fun a b => ty_capInsert c a b) (fun sl => ty_getCap sl) s hs.2 x hx⟩

/-! ## `invoke_tcb` -/

/-- An outcome of the extended install from an `NV` state is one of the ported install. -/
theorem toP {target : ObjRef} {slot : CslotPtr} {n : Nat} {o : Option (Cap × CslotPtr)} {s : State Unit}
    {hs : NV s} {x : Except Unit Unit × State Unit}
    (m : x ∈ (ExceptT.run (installTcbCapV (Z := Unit) target slot n o) s).1) :
    x ∈ (ExceptT.run (installTcbCap (Z := Unit) target slot n o) s).1 := by
  change x ∈ (installTcbCapV (Z := Unit) target slot n o s).1 at m
  rw [installTcbCapV_eq target slot n o hs] at m
  exact m

/-- **The caps a `ThreadControlCaps` installs before the IPC buffer are not virtualization caps** (premise
`hc` of `invokeTcbV_eq`, [S]: module docstring). -/
def TcbCapsOK : TcbInvocation → Prop
  | .threadControlCaps _ _ fh th cr vr _ => CapOK fh ∧ CapOK th ∧ CapOK cr ∧ CapOK vr
  | _ => True

/-- **`invoke_tcb`** on an `NV` state, given `TcbCapsOK` ([S]). -/
theorem invokeTcbV_eq (i : TcbInvocation) {s : State Unit} (hs : NV s) (hc : TcbCapsOK i) :
    invokeTcbV (Z := Unit) i s = invokeTcb i s := by
  cases i with
  | threadControlCaps target slot fh th cr vr buf =>
    obtain ⟨h1, h2, h3, h4⟩ := hc
    show ExceptT.run (invokeTcbV (Z := Unit) (.threadControlCaps target slot fh th cr vr buf)) s =
      ExceptT.run (invokeTcb (Z := Unit) (.threadControlCaps target slot fh th cr vr buf)) s
    unfold invokeTcbV invokeTcb
    refine nde_bind_congr (installTcbCapV_eq _ _ _ _ hs) fun _ t1 m1 => ?_
    have n1 := nv_installTcbCap target slot 3 h1 s hs _ (toP (hs := hs) m1)
    refine nde_bind_congr (installTcbCapV_eq _ _ _ _ n1) fun _ t2 m2 => ?_
    have n2 := nv_installTcbCap target slot 4 h2 t1 n1 _ (toP (hs := n1) m2)
    refine nde_bind_congr (installTcbCapV_eq _ _ _ _ n2) fun _ t3 m3 => ?_
    have n3 := nv_installTcbCap target slot 0 h3 t2 n2 _ (toP (hs := n2) m3)
    refine nde_bind_congr (installTcbCapV_eq _ _ _ _ n3) fun _ t4 m4 => ?_
    have n4 := nv_installTcbCap target slot 1 h4 t3 n3 _ (toP (hs := n3) m4)
    exact nde_bind_congr (installTcbFrameCapV_eq _ _ _ n4) fun _ _ _ => rfl
  | threadControlSched target slot fh mcp prio sc =>
    show ExceptT.run (invokeTcbV (Z := Unit) (.threadControlSched target slot fh mcp prio sc)) s =
      ExceptT.run (invokeTcb (Z := Unit) (.threadControlSched target slot fh mcp prio sc)) s
    unfold invokeTcbV invokeTcb
    exact nde_bind_congr (installTcbCapV_eq _ _ _ _ hs) fun _ _ _ => rfl
  | _ => rfl

end

end Fl4Proofs.P3.VirtNvTcb
