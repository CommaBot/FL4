/-
P3 (DESIGN.md §9): **every cap but the Domain cap has its `DomFrame`**,
assembled from FL4's halves (`DecDomHyp`) and the spec's (`dk_spec_notDom`).

`domFrame_all`: for a cap other than the Domain cap, `DomFrame` from
`DecDomHyp` of the caps other than Null and Zombie (whose decode only fails,
`decDomHyp_null`, `decDomHyp_zombie`). The FL4 halves, per cap, and what each
still names:

* Untyped: `decDomHyp_untyped` (UtDom); names `UtApart` (the cap's region
  misses the kernel-global block; `JCovD.utApart` from `JCovD`'s field).
* IRQ control, IRQ handler, IO port control, IO port: `decDomHyp_irqControl`,
  `decDomHyp_irqHandler`, `decDomHyp_ioportControl`, `decDomHyp_ioport`
  (DomCaps); the handler names `IrqDelP1` (P1's `BlkOK` and `KWApart` at the
  restarted state).
* Thread, CNode: `decDomHyp_thread`, `decDomHyp_cnode` (AllDom), from
  `TcbDomHyp` / `CnodeDomHyp`, which TcbDom / CnodeDom derive from P1's
  `TcbDecFootP1` / `CnodeDecFootP1` and `KWDom`.
* Notification: `decFootP1_notification` and `decDomHyp_of_foot` (DomFoot),
  from P1's `send_signal.tinvF` and `KWDom`.
* Endpoint, Reply: `decWritesHyp_endpoint_rsp`, `decWritesHyp_reply_rsp`
  (IpcRS) and `decDomHyp_of_writes` (DomFoot): P1's `send_ipc.footB` /
  `do_reply_transfer.foot` at P3's `RSP`; name P1's `XferHyps` and, for the
  reply, `do_reply_transfer.foot`'s timeout-handler and user-word premises.
* SchedContext, SchedControl: `domFrame_sched_context`,
  `domFrame_sched_control` (ScTop, ScTopCfg), whole `DomFrame`s under
  `ScPlaced`.
* Page table, page directory, PDPT, ASID pool: `domFrame_page_table` etc.
  (VsDomF); Frame, PML4 and ASID control at `DecOKDM` (VsDomF's
  `…D` theorems), from `VsFootW`.
* Vcpu, EPT: not covered here.
-/
import Fl4Proofs.P3.UtDom
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Spec

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **Every cap but the Domain cap has its `DomFrame`**, from FL4's half for
each cap other than Null and Zombie (module docstring). -/
theorem domFrame_all (s : S) (ar : A) (σ : State Unit) (lbl length slot : U64) (cap : capability.Cap)
    (hc : cap ≠ .Domain) (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (ct : U64) (hct : sched.cur_thread st s = ok ct)
    {tcb : Tcb} (hkt : σ.kheap σ.curThread = some (.tcb tcb)) (slbl : Data) (args : List Data) (ci : CapRef)
    (sl : CslotPtr) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef)
    (hK : ∀ c, cap = c → c ≠ .Null → (∀ p zt n, c ≠ .Zombie p zt n) →
      DecDomHyp (L := L) arI s ar lbl length slot c blk call don fp buf extra) :
    DomFrame (L := L) arI s ar σ lbl length slot cap blk call don fp buf extra slbl args ci sl excaps buffer := by
  refine domFrame_of arI s ar σ lbl length slot cap hc blk call don fp buf extra hkt slbl args ci sl excaps buffer ?_
  by_cases hn : cap = .Null
  · subst hn; exact decDomHyp_null arI s ar lbl length slot blk call don fp buf extra ct hct
  by_cases hz : ∃ p zt n, cap = .Zombie p zt n
  · obtain ⟨p, zt, n, rfl⟩ := hz
    exact decDomHyp_zombie arI s ar lbl length slot p zt n blk call don fp buf extra ct hct
  exact hK cap rfl hn fun p zt n e => hz ⟨p, zt, n, e⟩

end

end

end Fl4Proofs.P3
