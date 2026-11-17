/-
P3 (DESIGN.md §9), CSpace: **CNode CancelBadgedSends at `XTop` with the IPC
side's `xCancelBadged`** (IpcCancelBadged) in place of the named
`XCancelBadgedHyp`: `decode_invocation_cnode_cancelXI`.
-/
import Fl4Proofs.P3.IpcCancelBadged
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`CnodeXHyp` at the CancelBadgedSends label** (27), the IPC step
discharged by `xCancelBadged`: beyond `decode_invocation_cnode_cancelX`'s
CSpace premises, the caller's state code below 3 (running, restarting or
inactive), and at every `XTopAt` sets `KsApart`, the IPC placement, the
caller among the TCBs, the endpoint of a full-rights endpoint cap in a slot
among the endpoints; at the spec state every endpoint's queued threads'
facts, `ScBack` and `ActReady` (`EpQPre`), the caller not the switch target. -/
theorem decode_invocation_cnode_cancelXI {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} (s : S)
    (ar : A) (σ : Fl4Spec.State Unit) (hX : XTopAt (L := L) AR Z s ar σ) (hC : CurRun σ)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .cnodeCancelBadgedSends)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (p r gs g : U64) (hwf : CapWf (.CNode p r gs g)) (hcv : CapValid Z.th (.CNode p r gs g))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hcur : σ.curThread = ct.bv)
    (hrun : ∀ xt, σ.kheap ct.bv = some (.tcb xt) → tsCode xt.tcbState < 3)
    (hZ : ∀ Z' : XSets, XTopAt (L := L) AR Z' s ar σ → KsApart Z'.N Z'.T Z'.E Z'.R Z'.B (L.ksb s) ∧
      BufWordRel Z'.T (L.mem s) σ ∧ IPlaced Z'.N Z'.T Z'.E Z'.R Z'.B ∧ ct ∈ Z'.T)
    (hQ : ∀ e, EpQPre σ e) (hsw : ∀ u, σ.schedulerAction = .switchThread u → u ≠ ct.bv)
    (hE : ∀ (Z' : XSets) (e b : U64) (sl : Fl4Spec.CslotPtr), XTopAt (L := L) AR Z' s ar σ → AbsSlot Z.th sl →
      capV (L.mem s) (cslotAddr sl) = .Endpoint e b true true true true → e ∈ Z'.E)
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (XTop (L := L) AR) s ar σ fl4_abi.label.CNodeCancelBadgedSends length slot (.CNode p r gs g)
      blk call don fp buf extra slbl (args.map UScalar.bv) ci sl excaps buffer ct := by
  obtain ⟨-, xt, hkt⟩ := hX.curTcb hcur
  refine decode_invocation_cnode_cancelX arI s ar σ hX hC slbl hlbl length buf ct hct args hlen hargs p r gs g hwf
    hcv extra excaps hact hcur (fun σ1 e b sl' hsl hcV hst _ => ?_) slot blk call don fp ci sl buffer
  exact xCancelBadged hcur hkt (hrun xt hkt) hst (fun Z' hX' =>
    let ⟨h1, h0, h2, h3⟩ := hZ Z' hX'
    ⟨h1, h0, h2, h3, hE Z' e b sl' hX' hsl hcV⟩) (hQ _) hsw

end

end

end Fl4Proofs.P3
