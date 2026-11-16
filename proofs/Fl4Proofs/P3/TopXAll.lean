/-
P3 (DESIGN.md §9): **one extra relation for `handle_invocation_refinesMX`**
(`XTop`) and every cap's `hDec` for it (`decOK_XTop`).

* `XSets`, `XTopAt`, `XTop`: the families' relations at one typed heap and
  one family of object sets, the sets existential (retype and `MakePool`
  grow them). Fields: `fin` (VSpace's `FinX` at `TopSR`: the scheduler,
  endpoint, notification, IRQ, IO-port and kernel-root relations, the arch
  relation, the placement, the ASID and page-table relations, the pools and
  the current thread), `rel` (`RelTopB`: the CSpace relation at the same
  typed heap, with the IPC words and SCs apart from its slots), `ipc`
  (`IpcRel`) and `esa` (`EpSchedApart`). The IPC proofs' `IRel` from it:
  IpcXTop.lean's `XTopAt.irelK`. Fields can be added (the kernel-entry composition's) without
  touching the producers.
* `DecOKDMX.imp`, `DecOKRMX.imp`: a producer at `X₁` gives one at `X₂` when
  `X₁` implies `X₂` (the only generic lift: the relations sit under the
  spec outcome the producer picks).
* `FinXR`: VSpace's `FinX` with `RelTopB` at its own typed heap and
  `EpSchedApart`; `xtop_of_finXR`: it implies `XTop` (`IpcRel` from the
  endpoint and notification relations and the scheduler's TCB SC fields).
* The named hypotheses, one uniform shape each:
  - `XLeaf X s a σ prog spec`: from `X`, the FL4 leaf `prog` ends `Ok`
    related (`RelTopM`, `X`) to an outcome of `spec` (the `hsend` shape of
    IpcSendTop). `IpcVsFrame`: the send, signal and reply leaves at `XTop`
    (the IPC leaves at `IRel` with the VSpace relations framed: their writes
    in the other objects and the receive slots).
  - `XCap X … c`: the cap's `DecOKDMX X ∨ DecOKRMX X`. `VsThX`: a VSpace
    cap's at `FinXR` for sets chosen per outcome (`∃ Z, FinXR AR Z` inside
    the post: MakePool picks the typed heap per outcome);
    `TcbXHyp`, `ScXHyp`, `CnodeXHyp`, `UtXHyp`, `IrqXHyp`, `IoXHyp`,
    `DomXHyp`, `VcpuXHyp`: the cap's at `XTop`.
* `decOK_XTop`: every cap's `XCap (XTop AR)` by dispatch: Null and Zombie
  (the state unchanged), Endpoint, Notification, Reply (IpcSendTop's
  `decode_*DMX` from `IpcVsFrame`), the VSpace caps (`VsThX`, `.imp`), the
  rest named (table in `decOK_XTop`'s docstring); `hDec_XTop`: the `hDec`
  of `handle_invocation_refinesMX` at `XTop`, the spec's restart from `XTop`
  (`XTop.restart`).
-/
import Fl4Proofs.P3.HandleTopX
import Fl4Proofs.P3.IpcSendTop
import Fl4Proofs.P3.IpcLeaves
import Fl4Proofs.P3.VsTopX
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

/-- The typed heap, ghost tree and object sets of the composite relation. -/
structure XSets where
  th : TypedHeap
  G : MdbGhost
  P : Set U64
  L4 : Set U64
  L3 : Set U64
  L2 : Set U64
  L1 : Set U64
  N : Set U64
  T : Set U64
  C : Set U64
  E : Set U64
  R : Set U64
  B : Set (U64 × Fl4Spec.Word)
  c : U64

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

/-- **The composite relation at the sets `Z`** (module docstring). -/
structure XTopAt (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  fin : FinX st Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1
    (TopSR st Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 Z.N Z.T Z.C Z.E Z.R Z.B Z.c AR) s a σ
  rel : RelTopB (L := L) Z.th Z.G Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ
  ipc : IpcRel Z.N Z.T Z.E Z.R Z.B (L.mem s) σ
  esa : EpSchedApart st Z.T Z.C Z.E Z.R Z.B Z.c s σ

/-- **The composite relation** (module docstring). -/
def XTop (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  ∃ Z : XSets, XTopAt (L := L) AR Z s a σ

theorem XTopAt.relTop {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : XTopAt (L := L) AR Z s a σ) : RelTopM (L := L) s σ :=
  let ⟨hPl, hCR, hFI, hD, hMO, _, _⟩ := h.rel
  ⟨Z.th, Z.G, hPl, hCR, hFI, hD, hMO⟩

/-- **VSpace's `FinX` with the CSpace relation at its own typed heap** and
the endpoint words apart from the scheduler's. -/
def FinXR (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  FinX st Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (TopSR st Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 Z.N Z.T Z.C Z.E Z.R Z.B Z.c AR) s a σ ∧
    (∃ G, RelTopB (L := L) Z.th G Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ) ∧ EpSchedApart st Z.T Z.C Z.E Z.R Z.B Z.c s σ

/-- The scheduler relation's TCB SC fields. -/
theorem sched_sc {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit} (h : Sched.SchedRel st N T C c s σ) :
    ∀ t ∈ T, ∀ x, σ.kheap t.bv = some (.tcb x) → x.tcbSchedContext = Notif.optRef (L.mem s (P1.scA t)) := by
  intro t ht x hk
  obtain ⟨Q, R, -, hS⟩ := h.lists
  obtain ⟨y, hy, -, -, hsc, -⟩ := hS.tcb t ht
  rw [hk] at hy; cases hy; exact hsc

/-- **`FinXR` gives `XTop`.** -/
theorem xtop_of_finXR {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : FinXR (L := L) AR Z s a σ) : XTop (L := L) AR s a σ := by
  obtain ⟨hF, ⟨G, hR⟩, hE⟩ := h
  obtain ⟨⟨⟨hSch, hEp, hNt, -⟩, -⟩, -⟩ := id hF
  exact ⟨{ Z with G := G }, hF, hR, IpcRel.of hNt hEp (sched_sc hSch), hE⟩

end

/-! ## Lifting a producer -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

theorem TopPostDMX.imp {X₁ X₂ : S → A → Fl4Spec.State Unit → Prop} {σ : Fl4Spec.State Unit} {blk call don : Bool}
    {m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation} {s : S} {res : core.result.Result Unit error.Exc × S × A}
    (h : TopPostDMX (L := L) X₁ σ blk call don m s res) (hX : ∀ s a σ, X₁ s a σ → X₂ s a σ) :
    TopPostDMX (L := L) X₂ σ blk call don m s res := by
  rcases h with ⟨e, h1, h2, h3, h4⟩ | ⟨inv, h1, σ1, h2, y, hy, h3, h4⟩
  · exact Or.inl ⟨e, h1, h2, h3, hX _ _ _ h4⟩
  · exact Or.inr ⟨inv, h1, σ1, h2, y, hy, h3, hX _ _ _ h4⟩

theorem TopPostRMX.imp {X₁ X₂ : S → A → Fl4Spec.State Unit → Prop} {σ : Fl4Spec.State Unit} {blk call don : Bool}
    {m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation} {ct : U64} {s : S}
    {res : core.result.Result Unit error.Exc × S × A}
    (h : TopPostRMX (L := L) X₁ σ blk call don m ct s res) (hX : ∀ s a σ, X₁ s a σ → X₂ s a σ) :
    TopPostRMX (L := L) X₂ σ blk call don m ct s res := by
  rcases h with ⟨e, h1, h2, h3, h4⟩ | ⟨h1, h2, inv, h3, σ1, h4, rr, σy, h5, z, hz, h6, h7⟩
  · exact Or.inl ⟨e, h1, h2, h3, hX _ _ _ h4⟩
  · exact Or.inr ⟨h1, h2, inv, h3, σ1, h4, rr, σy, h5, z, hz, h6, hX _ _ _ h7⟩

/-- **The cap's statement for `handle_invocation_refinesMX`** at `X`. -/
def XCap (X : S → A → Fl4Spec.State Unit → Prop) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (lbl length slot : U64)
    (c : capability.Cap) (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) (ct : U64) : Prop :=
  DecOKDMX (L := L) arI X s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer ∨
    DecOKRMX (L := L) arI X s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer ct

/-- **The generic lift**: `XCap` at `X₁` gives it at `X₂` when `X₁ → X₂`. -/
theorem XCap.imp {X₁ X₂ : S → A → Fl4Spec.State Unit → Prop} {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    {lbl length slot : U64} {c : capability.Cap} {blk call don fp : Bool} {buf : U64}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {slbl : Fl4Spec.Data} {args : List Fl4Spec.Data}
    {ci : Fl4Spec.CapRef} {sl : Fl4Spec.CslotPtr} {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    {buffer : Option Fl4Spec.ObjRef} {ct : U64}
    (h : XCap (L := L) arI X₁ s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer ct)
    (hX : ∀ s a σ, X₁ s a σ → X₂ s a σ) :
    XCap (L := L) arI X₂ s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer ct := by
  rcases h with h | h
  · exact Or.inl (WP.spec_mono h fun _ hr => hr.imp hX)
  · exact Or.inr (WP.spec_mono h fun _ hr => hr.imp hX)

/-- **A leaf keeping `X`** (the uniform shape of the named leaf hypotheses):
from `X`, `prog` ends `Ok` related to an outcome of `spec`. -/
def XLeaf (X : S → A → Fl4Spec.State Unit → Prop) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (prog : Result ((core.result.Result Unit error.Exc) × S × A))
    (spec : Set (Unit × Fl4Spec.State Unit) × Prop) : Prop :=
  X s a σ → prog ⦃ r => r.1 = .Ok () ∧ ∃ z ∈ spec.1, RelTopM (L := L) r.2.1 z.2 ∧ X r.2.1 r.2.2 z.2 ⦄

end

/-! ## The named hypotheses and the dispatch -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The IPC leaves at `XTop`** (`IpcVsFrame`), for the cap: with the send
right, `set_thread_state Restart` then `send_ipc` (endpoint) or
`send_signal` (notification); for a reply cap, then `do_reply_transfer`;
`σ1` the spec's state after its restart. -/
def IpcVsFrame (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (ar : A) (σ σ1 : Fl4Spec.State Unit) (ct : U64)
    (blk call don : Bool) : capability.Cap → Prop
  | .Endpoint p b true _ g gr => XLeaf (L := L) (XTop (L := L) AR) s ar σ (do
      let s1 ← sched.set_thread_state st s ct sched.TS_RESTART
      let (s2, a1) ← endpoint.send_ipc st arI s1 ar blk call b g gr don ct p
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a1))
      (Fl4Spec.sendIpc (Z := Unit) blk call b.bv g gr don σ1.curThread p.bv σ1)
  | .Notification p b true _ => XLeaf (L := L) (XTop (L := L) AR) s ar σ (do
      let s1 ← sched.set_thread_state st s ct sched.TS_RESTART
      let (s2, a1) ← notification.send_signal st arI s1 ar p b
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a1))
      (Fl4Spec.sendSignal (Z := Unit) p.bv b.bv σ1)
  | .Reply p g => XLeaf (L := L) (XTop (L := L) AR) s ar σ (do
      let s1 ← sched.set_thread_state st s ct sched.TS_RESTART
      let (s2, a1) ← ipc.do_reply_transfer st arI s1 ar ct p g
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a1))
      (Fl4Spec.doReplyTransfer (Z := Unit) σ1.curThread p.bv g σ1)
  | _ => True

/-- **The hypotheses still named**, per cap (`decOK_XTop`'s docstring): the
IPC leaves (`IpcVsFrame`); for a VSpace cap its statement at `FinXR` with the
sets per outcome (`VsThX`: the producer's post at its own typed heap); for the others
their statement at `XTop` (`TcbXHyp`, `ScXHyp`, `CnodeXHyp`, `UtXHyp`,
`IrqXHyp`, `IoXHyp`, `DomXHyp`, `VcpuXHyp`); nothing for Null and Zombie. -/
def XNamed (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (ar : A) (σ σ1 : Fl4Spec.State Unit) (lbl length slot : U64)
    (c : capability.Cap) (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) (ct : U64) : Prop :=
  match c with
  | .Null | .Zombie .. => True
  | .Endpoint .. | .Notification .. | .Reply .. => IpcVsFrame (L := L) arI AR s ar σ σ1 ct blk call don c
  | .Frame .. | .PageTable .. | .PageDirectory .. | .Pdpt .. | .Pml4 .. | .AsidControl | .AsidPool .. =>
    XCap (L := L) arI (fun s a σ => ∃ Z, FinXR (L := L) AR Z s a σ) s ar σ lbl length slot c blk call don fp buf
      extra slbl args ci sl excaps buffer ct
  | _ => XCap (L := L) arI (XTop (L := L) AR) s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl
      excaps buffer ct

/-- **Every cap's statement at `XTop`**, by dispatch on the cap:

| cap | from | still named |
|---|---|---|
| Null, Zombie | the decode fails, the state unchanged | — |
| Endpoint, Notification | `decode_endpointDMX`, `decode_notificationDMX` | `IpcVsFrame` (send, signal leaves at `XTop`) |
| Reply | `decode_replyDMX` | `IpcVsFrame` (`do_reply_transfer` at `XTop`) |
| Frame, page table, page directory, PDPT, PML4, ASID control, ASID pool | `XCap.imp`, `xtop_of_finXR` | `VsThX` (the producer at `FinXR`) |
| Thread | — | `TcbXHyp` |
| SchedContext, SchedControl | — | `ScXHyp` |
| CNode | — | `CnodeXHyp` |
| Untyped | — | `UtXHyp` |
| IRQ control, IRQ handler | — | `IrqXHyp` |
| IO port control, IO port | — | `IoXHyp` |
| Domain | — | `DomXHyp` |
| Vcpu, EPT | — | `VcpuXHyp` |
-/
theorem decOK_XTop (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (hX0 : XTop (L := L) AR s ar σ) (lbl length slot : U64) (c : capability.Cap) (blk call don fp : Bool)
    (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) (ct : U64) (hct : sched.cur_thread st s = ok ct) {σ1 : Fl4Spec.State Unit}
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (hN : XNamed (L := L) arI AR s ar σ σ1 lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer
      ct) :
    XCap (L := L) arI (XTop (L := L) AR) s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps
      buffer ct := by
  cases c
  case Null =>
    left; unfold DecOKDMX syscall.decode_invocation
    rw [hct]; simp only [bind_ok, WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, hX0⟩
  case Zombie p zt n =>
    left; unfold DecOKDMX syscall.decode_invocation
    rw [hct]; simp only [bind_ok, WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, hX0⟩
  case Endpoint p b sd rv g gr =>
    left
    refine decode_endpointDMX arI _ s ar σ lbl length slot p b sd rv g gr blk call don fp buf extra slbl args ci sl
      excaps buffer ct hct hX0 hst fun hsd => ?_
    subst hsd; exact hN hX0
  case Notification p b sd rv =>
    left
    refine decode_notificationDMX arI _ s ar σ lbl length slot p b sd rv blk call don fp buf extra slbl args ci sl
      excaps buffer ct hct hX0 hst fun hsd => ?_
    subst hsd; exact hN hX0
  case Reply p g =>
    exact Or.inl (decode_replyDMX arI _ s ar σ lbl length slot p g blk call don fp buf extra slbl args ci sl excaps
      buffer ct hct hst (hN hX0))
  all_goals first
    | exact hN
    | exact hN.imp arI fun _ _ _ ⟨_, hx⟩ => xtop_of_finXR hx

/-- The spec's restart of the current thread, at `XTop`. -/
theorem XTop.restart {AR : A → Fl4Spec.Cr3 → Prop} {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (h : XTop (L := L) AR s ar σ) :
    ∃ σ1, Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) := by
  obtain ⟨Z, hZ⟩ := h
  obtain ⟨t, htb, hth, -⟩ := hZ.fin.2.2.2.2
  obtain ⟨x, hk, -⟩ := hZ.rel.2.1.1.tcb t hth
  rw [htb] at hk
  rw [Notif.setThreadState_eq .restart hk]; exact ⟨_, rfl⟩

/-- **`handle_invocation_refinesMX`'s `hDec` at `XTop`**: every cap from its
`XNamed` (`decOK_XTop`). -/
theorem hDec_XTop (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (hX0 : XTop (L := L) AR s ar σ) (lbl length : U64) (blk call don fp : Bool) (buf : U64)
    (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef)
    (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (r2 : core.result.Result (Aeneas.Std.Array obj.Slot 3#usize) error.Fault)
    (er : Except Fl4Spec.Fault (List (Fl4Spec.Cap × Fl4Spec.CslotPtr)))
    (hN : ∀ (sl : Fl4Spec.CslotPtr) (c : capability.Cap) (e : Aeneas.Std.Array obj.Slot 3#usize)
      (exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), capAt (L.mem s) (cslotAddr sl) = ok c →
      Fl4Spec.getCap (Z := Unit) sl σ = ({(absCap c, σ)}, False) → r2 = .Ok e → er = .ok exs →
      ∀ σ1, Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
      XNamed (L := L) arI AR s ar σ σ1 lbl length (cslotAddr sl) c blk call don fp buf e slbl args ci sl exs buffer
        ct) :
    ∀ (sl : Fl4Spec.CslotPtr) (c : capability.Cap) (e : Aeneas.Std.Array obj.Slot 3#usize)
      (exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), capAt (L.mem s) (cslotAddr sl) = ok c →
      Fl4Spec.getCap (Z := Unit) sl σ = ({(absCap c, σ)}, False) → r2 = .Ok e → er = .ok exs →
      DecOKDMX (L := L) arI (XTop (L := L) AR) s ar σ lbl length (cslotAddr sl) c blk call don fp buf e slbl args ci
        sl exs buffer ∨
      DecOKRMX (L := L) arI (XTop (L := L) AR) s ar σ lbl length (cslotAddr sl) c blk call don fp buf e slbl args ci
        sl exs buffer ct := by
  intro sl c e exs h1 h2 h3 h4
  obtain ⟨σ1, hst⟩ := hX0.restart
  exact decOK_XTop arI AR s ar σ hX0 lbl length _ c blk call don fp buf e slbl args ci sl exs buffer ct hct hst
    (hN sl c e exs h1 h2 h3 h4 σ1 hst)

end

end

end Fl4Proofs.P3
