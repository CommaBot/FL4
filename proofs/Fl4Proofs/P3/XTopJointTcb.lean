/-
P3 (DESIGN.md §9), TCB: **the Thread cap at `JAt`, label by label**
(`decode_invocation_threadJ`, in the shape of the CNode cap's
`decode_invocation_cnodeJ_steps`).

* `TcbJOpen`: the Thread cap's labels whose `JAt` step is not yet proved;
  only for them the per-op named premise `JPostHyp` [W] (XTopJointStep) is
  still taken, lifted by `XCap.jat` from `decode_invocation_threadJAt`.
* Every other label through `decode_invocation_threadX` at `X := JAt`: the
  labels of no TCB invocation (and the fast-path flag's decode error) are the
  spec's `IllegalOperation` with the state unchanged (`tcb_illegalX`, `JAt`
  at the start).
-/
import Fl4Proofs.P3.XTopJointDelR
import Fl4Proofs.P3.XTopJointReply
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

/-- **The Thread cap's labels still open at `JAt`** (their `JPostHyp` [W]
taken): the TCB invocation labels (2..24). -/
def TcbJOpen (lbl : U64) : Prop := 2 ≤ lbl.val ∧ lbl.val ≤ 24

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 4000000 in
/-- **The Thread cap, `JAt` after** (module docstring): the labels of
`TcbJOpen` by `decode_invocation_threadJAt` and `XCap.jat` with the per-op
premise (`JPostHyp` [W], only at those labels); the others proved. -/
theorem decode_invocation_threadJ [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hG : CsGlobal (L := L) arI AR Z.th)
    (hARI : ARIface arI AR) (hT : P0.ArchTotal arI)
    (hA : ∀ s a σ G, WX (L := L) AR Z.th s a σ G → Notif.ActReady σ)
    (hBT : ∀ (Z' : XSets) s' a' σ', Z'.th = Z.th → XTopAt (L := L) AR Z' s' a' σ' → BufWordRel Z'.T (L.mem s') σ')
    (hOK : ∀ (Z' : XSets) s' a' σ', Z'.th = Z.th → XTopAt (L := L) AR Z' s' a' σ' → Endp.IpcBufCapOK σ')
    (hBC : ∀ (Z' : XSets) s' a' σ', Z'.th = Z.th → XTopAt (L := L) AR Z' s' a' σ' → Endp.BufCover Z'.T Z'.B σ')
    (hBPl : ∀ (Z' : XSets) s' a' σ', Z'.th = Z.th → XTopAt (L := L) AR Z' s' a' σ' →
      Vs.BufPlaced (L := L) Z'.N Z'.C Z'.B Z'.c s' σ')
    (hFl : ∀ (Z' : XSets) s' a' σ', Z'.th = Z.th → XTopAt (L := L) AR Z' s' a' σ' → FlagsRel Z'.T (L.mem s') σ')
    (lbl length : U64) (p : U64)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ct : U64)
    (hct : sched.cur_thread st s = ok ct)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = tcbLabelOf lbl)
    (argsU : List U64) (hlen : length.val = argsU.length)
    (hargs : ∀ (i : U64) x, argsU[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th sl)
    (hsc : capV (L.mem s) (cslotAddr sl) = .Thread p)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (hext : Fl4Spec.genInvocationType slbl = .invalidInvocation → Fl4Spec.fl4TcbExtLabelOf slbl = tcbExtOf lbl)
    (hstall' : ∀ q, smp.remote_tcb_stall st arI s ar q = ok (s, ar))
    (hNative : lbl ≠ fl4_abi.label.TCBSetEPTRoot)
    (hcw : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD))
    (hpI : p ≠ L.idleW s)
    (x0 x1 x2 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (hx1 : Aeneas.Std.Array.index_usize extra 1#usize = ok x1)
    (hx2 : Aeneas.Std.Array.index_usize extra 2#usize = ok x2)
    (hXc : XcRel Z.th (L.mem s) x0 x1 x2 excaps) (hnc : NcHyp (st := st) s σ x0 x1 x2)
    (hnc0 : ∀ sl : Fl4Spec.CslotPtr, x0 = cslotAddr sl → isUt (capV (L.mem s) x0) = true →
      NoChildrenRel (st := st) s σ x0 sl)
    (hcapC : x1 ≠ 0#u64 → ∀ q b, capV (L.mem s) x1 = .SchedContext q b → q ∈ Z.C)
    (hA5 : ArgRel (st := st) s σ ct buf buffer 5) (hGb : GetBpHyp (st := st) s ct p)
    (hI : TcbXIpc (L := L) arI AR Z.th s ar σ p ct buf argsU blk call don)
    (hFr : ∀ (x ptr offset r : U64) (sz : capability.FrameSize) (m ep : Bool) (asid va : U64),
      capV (L.mem s) x = .Frame ptr sz r false m ep asid va → FpuPass true offset r sz →
      FpuFrameXHyp (L := L) AR Z p (core.num.U64.wrapping_add ptr offset))
    (hR : TcbJOpen lbl → JPostHyp (L := L) arI AR s ar σ lbl length (cslotAddr sl) (.Thread p) blk call don fp buf
      extra slbl (argsU.map UScalar.bv) ci sl excaps buffer ct) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length (cslotAddr sl) (.Thread p) blk call don fp buf extra slbl
      (argsU.map UScalar.bv) ci sl excaps buffer ct := by
  by_cases hop : TcbJOpen lbl
  · exact XCap.jat arI (decode_invocation_threadJAt arI s ar σ J hni hG hARI hT hA hBT hOK hBC hBPl hFl lbl length p
      blk call don fp buf extra ct hct slbl hlbl argsU hlen hargs ci sl hAs hsc excaps buffer hext hstall' hNative hcw
      hpI x0 x1 x2 hx0 hx1 hx2 hXc hnc hnc0 hcapC hA5 hGb hI hFr) J (hR hop)
  have no : ∀ l : U64, 2 ≤ l.val → l.val ≤ 24 → lbl = l → False := fun l h1 h2 h => hop (h ▸ ⟨h1, h2⟩)
  have hJ0 : JAt (L := L) arI AR s ar σ := ⟨Z, H, Cs, Ac, Lst, D, J⟩
  exact decode_invocation_threadX arI s ar σ hJ0 lbl length (cslotAddr sl) p blk call don fp buf extra ct hct slbl
    hlbl _ ci sl excaps buffer hext (hstall' p) hNative
    ⟨fun h => (no _ (by simp) (by simp) h).elim, fun h => (no _ (by simp) (by simp) h).elim,
      fun h => (no _ (by simp) (by simp) h).elim, fun h => (no _ (by simp) (by simp) h).elim,
      fun h => (no _ (by simp) (by simp) h).elim, fun h => (no _ (by simp) (by simp) h).elim,
      fun h => (no _ (by simp) (by simp) h).elim, fun h => (no _ (by simp) (by simp) h).elim,
      fun h => (no _ (by simp) (by simp) h).elim, fun h => (no _ (by simp) (by simp) h).elim,
      fun h => (no _ (by simp) (by simp) h).elim, fun h => (no _ (by simp) (by simp) h).elim,
      fun h => (no _ (by simp) (by simp) h).elim, fun h => (no _ (by simp) (by simp) h).elim,
      fun h => (no _ (by simp) (by simp) h).elim, fun h => (no _ (by simp) (by simp) h).elim,
      fun h => (no _ (by simp) (by simp) h).elim, fun h => (no _ (by simp) (by simp) h).elim,
      fun h => (no _ (by simp) (by simp) h).elim, fun h => (no _ (by simp) (by simp) h).elim,
      fun h => (no _ (by simp) (by simp) h).elim, fun h => (no _ (by simp) (by simp) h).elim,
      fun h => (no _ (by simp) (by simp) h).elim⟩

end

end

end Fl4Proofs.P3
