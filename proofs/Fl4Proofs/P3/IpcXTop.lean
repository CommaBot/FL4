/-
P3 (DESIGN.md §9), IPC: **the IPC proofs' relation and `XTopAt`**.

`IRel` at a typed heap `th` carries, in `RelTopI`, the VSpace and
kernel-state parts of `XTopAt` (`VsP`: VSpace's `FinX` relations and
placement, the IRQ, IO-port and kernel-root relations, the IPC objects and
SCs apart from the kernel-global block), so:

* `XTopAt.irelK`: `XTopAt` at sets `Z`, with the IPC objects outside the
  kernel-global block (`KsApart`) and the IPC-buffer words (`BufWordRel`),
  gives `IRel` at `Z.th`;
* `IRel.xtop`: `IRel` with the arch relation gives `XTopAt` at the sets with
  `th` (and `KsApart` and `BufWordRel` again), so the IPC leaves proved on `IRel` end at
  `XTopAt` directly.
-/
import Fl4Proofs.P3.XTopStep
import Fl4Proofs.P3.IpcSchedLift
import Fl4Proofs.P3.IpcLeaves
import Fl4Proofs.P3.IpcReply
import Fl4Proofs.P3.ArchKeep
import Fl4Proofs.P3.IpcEpTail
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P1 Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

/-- **`XTopAt` gives the IPC proofs' `IRel`** at its typed heap, with the IPC
objects outside the kernel-global block. -/
theorem XTopAt.irelK {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : XTopAt (L := L) AR Z s a σ) (hK : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s))
    (hBW : BufWordRel Z.T (L.mem s) σ) :
    IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ := by
  obtain ⟨⟨⟨⟨hSch, -, -, hIrq, hIo, hKr, -⟩, hP⟩, hR, hPt, hPI, hCO⟩, hB, hIR, hEA⟩ := h
  obtain ⟨Q, R0, hc, -⟩ := hSch.lists
  refine ⟨hIR, ⟨⟨Z.G, hB⟩, ⟨⟨Z.P, Z.L4, Z.L3, Z.L2, Z.L1, hR, hPt, hPI, hCO, hP⟩, hIrq, hIo, hKr,
    fun t ht => ?_, hK.ep, hK.rep, hK.ntfn, hK.buf,
    fun sc hsc x n hk a ha => (hSch.scOut sc hsc x n hk a ha).2.2.2, rfl, hBW, bn_of_node hc.node hc.tcbs⟩⟩, hSch, hEA⟩
  have := hc.ksOut t ht; omega

/-- **`IRel` gives `XTopAt`** at the sets with its typed heap, given the arch
relation; and the IPC objects outside the kernel-global block. -/
theorem IRel.xtop {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64}
    {B : Set (U64 × Fl4Spec.Word)} {c : U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : IRel st th cr N T C E R B c s σ) (hAR : AR a cr) :
    (∃ Z : XSets, Z.th = th ∧ Z.N = N ∧ Z.T = T ∧ Z.C = C ∧ Z.E = E ∧ Z.R = R ∧ Z.B = B ∧ Z.c = c ∧
      XTopAt (L := L) AR Z s a σ) ∧ KsApart N T E R B (L.ksb s) ∧ BufWordRel T (L.mem s) σ := by
  obtain ⟨hIR, ⟨⟨G, hB⟩, hV⟩, hS, hEA⟩ := h
  obtain ⟨P, L4, L3, L2, L1, hR, hPt, hPI, hCO, hP⟩ := hV.ex
  exact ⟨⟨⟨th, G, P, L4, L3, L2, L1, N, T, C, E, R, B, c⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    ⟨⟨⟨hS, hIR.toE, hIR.toN, hV.irq, hV.io, hV.kr, by rw [hV.cr3]; exact hAR⟩, hP⟩, hR, hPt, hPI, hCO⟩, hB, hIR, hEA⟩,
    ⟨hV.ksE, hV.ksR, hV.ksN, hV.ksB⟩, hV.bw⟩

end


section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

/-- **An IPC leaf on `IRel` ends at `XTopAt`**: from `XTopAt Z` with the IPC
objects outside the kernel-global block, a leaf proved on `IRel` at `Z.th`
(and the spec's CR3), whose FL4 side keeps the arch relation (`hAk`: the
IPC paths' arch calls are the FPU and remote-stall ones), ends at
`XTopAt` at the same typed heap and sets, with `KsApart` again. -/
theorem xtopAt_of_irel {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hX : XTopAt (L := L) AR Z s a σ) (hK : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s))
    (hBW : BufWordRel Z.T (L.mem s) σ) {prog : Result ((core.result.Result Unit error.Exc) × S × A)} {spec : Set (Unit × Fl4Spec.State Unit) × Prop}
    (hI : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ → prog ⦃ r => r.1 = .Ok () ∧
      ∃ z ∈ spec.1, RelTopM (L := L) r.2.1 z.2 ∧
        IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c r.2.1 z.2 ⦄)
    (hAk : ∀ cr, AR a cr → prog ⦃ r => AR r.2.2 cr ⦄) :
    prog ⦃ r => r.1 = .Ok () ∧ ∃ z ∈ spec.1, RelTopM (L := L) r.2.1 z.2 ∧
      (∃ Z' : XSets, Z'.th = Z.th ∧ Z'.N = Z.N ∧ Z'.T = Z.T ∧ Z'.C = Z.C ∧ Z'.E = Z.E ∧ Z'.R = Z.R ∧ Z'.B = Z.B ∧
        Z'.c = Z.c ∧ XTopAt (L := L) AR Z' r.2.1 r.2.2 z.2) ∧ KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb r.2.1) ∧
      BufWordRel Z.T (L.mem r.2.1) z.2 ⦄ := by
  have hAR : AR a σ.archState.x64CurrentCr3 := hX.fin.1.1.2.2.2.2.2.2
  refine WP.spec_mono (WP.spec_and (hI (hX.irelK hK hBW)) (hAk _ hAR)) ?_
  rintro r ⟨⟨h1, z, hz, hRT, hIz⟩, ha⟩
  exact ⟨h1, z, hz, hRT, IRel.xtop hIz ha⟩

/-- **The XLeaf shape** (TopXAll's `XLeaf (XTop AR)`): for every `Z` the
entry's `XTopAt Z` holds at, `KsApart` and the leaf on `IRel` at `Z.th`. -/
theorem xleaf_of_irel {AR : A → Fl4Spec.Cr3 → Prop} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    {prog : Result ((core.result.Result Unit error.Exc) × S × A)} {spec : Set (Unit × Fl4Spec.State Unit) × Prop}
    (hKA : ∀ Z : XSets, XTopAt (L := L) AR Z s a σ → KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s) ∧
      BufWordRel Z.T (L.mem s) σ)
    (hI : ∀ Z : XSets, XTopAt (L := L) AR Z s a σ →
      IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ → prog ⦃ r => r.1 = .Ok () ∧
        ∃ z ∈ spec.1, RelTopM (L := L) r.2.1 z.2 ∧
          IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c r.2.1 z.2 ⦄)
    (hAk : ∀ cr, AR a cr → prog ⦃ r => AR r.2.2 cr ⦄) :
    XLeaf (L := L) (XTop (L := L) AR) s a σ prog spec := by
  rintro ⟨Z, hZ⟩
  refine WP.spec_mono (xtopAt_of_irel hZ (hKA Z hZ).1 (hKA Z hZ).2 (hI Z hZ) hAk) ?_
  rintro r ⟨h1, z, hz, hRT, ⟨Z', -, -, -, -, -, -, -, -, hZ'⟩, -⟩
  exact ⟨h1, z, hz, hRT, Z', hZ'⟩

end


/-! ## The IPC leaves at `XTop` (`IpcVsFrame`) -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- The IPC tails' shared hypotheses at sets `Z` (with the spec's CR3 `cr`):
`KsApart`, the scheduler and buffer steps (`IpcSchedHyps`, `EpBufHyps`,
`EpBufMapHyps`), the switch target ready on `IRel` (`act`, for the
endpoint tails `IpcEpTailHyps`: `IpcZ.Tl`), placement, and the current
thread in `Z.T`. -/
structure IpcZ (cr : Fl4Spec.Cr3) (s : S) (σ : Fl4Spec.State Unit) (ct : U64) (Z : XSets) : Prop where
  ks : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s)
  bt : BufWordRel Z.T (L.mem s) σ
  H : IpcSchedHyps st arI Z.N Z.T Z.E Z.R Z.B (SRT st Z.th cr Z.N Z.T Z.C Z.E Z.R Z.B Z.c
    (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c))
  Bf : EpBufHyps st Z.T Z.E Z.R Z.B (SRT st Z.th cr Z.N Z.T Z.C Z.E Z.R Z.B Z.c (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c))
  Bm : EpBufMapHyps st Z.T Z.E Z.R Z.B (SRT st Z.th cr Z.N Z.T Z.C Z.E Z.R Z.B Z.c (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c))
  act : ∀ s σ, IpcRel Z.N Z.T Z.E Z.R Z.B (L.mem s) σ →
    SRT st Z.th cr Z.N Z.T Z.C Z.E Z.R Z.B Z.c (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c) s σ → ActReady σ
  P : IPlaced Z.N Z.T Z.E Z.R Z.B
  ct : ct ∈ Z.T

/-- The endpoint tails (`IpcEpTailHyps`) at `Z`, by `ipcEpTailHyps_top`. -/
theorem IpcZ.Tl {cr : Fl4Spec.Cr3} {s : S} {σ : Fl4Spec.State Unit} {ct : U64} {Z : XSets}
    (h : IpcZ (L := L) arI cr s σ ct Z) :
    IpcEpTailHyps st A Z.N Z.T Z.E Z.R Z.B (SRT st Z.th cr Z.N Z.T Z.C Z.E Z.R Z.B Z.c
      (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c)) :=
  ipcEpTailHyps_top h.P h.act

/-- **`IpcVsFrame` for an endpoint cap with the send right**: `send_tail_top`
at every `Z` the entry's `XTopAt` holds at. Named: `IpcZ` and the send
tail's own hypotheses at `Z` (`SchedValid`, `QSorted` on `IRel`, the
endpoint in `Z.E`, `SendRest`); the arch relation by `ARKeep` (`AK.send_tail`). -/
theorem ipcVsFrame_endpoint {AR : A → Fl4Spec.Cr3 → Prop} {s : S} {a : A} {σ σ1 : Fl4Spec.State Unit}
    {ct : U64} (hcur : σ.curThread = ct.bv) {xt : Fl4Spec.Tcb} (hkt : σ.kheap ct.bv = some (.tcb xt))
    (hrun : tsCode xt.tcbState < 3) (hft : xt.tcbFault = none)
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (blk call don : Bool) (p b : U64) (rv g gr : Bool)
    (hZ : ∀ Z : XSets, XTopAt (L := L) AR Z s a σ → IpcZ (L := L) arI σ.archState.x64CurrentCr3 s σ ct Z ∧
      (∀ s' σ', IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ' → Sched.SchedValid σ') ∧
      (∀ s' σ', IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ' → QSorted st Z.T Z.E s') ∧
      p ∈ Z.E ∧
      (∀ s' σ', IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ' →
        SendRest st arI (IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c) Z.T s' a σ' blk call b
          g gr don ct p))
    (hS : P0.StoreTotal st) (hA : P0.ArchTotal arI) (hK : ARKeep arI AR) :
    IpcVsFrame (L := L) arI AR s a σ σ1 ct blk call don (.Endpoint p b true rv g gr) :=
  xleaf_of_irel (fun Z hX => ⟨(hZ Z hX).1.ks, (hZ Z hX).1.bt⟩) (fun Z hX hI =>
    let ⟨hz, hSV, hso, hp, hU⟩ := hZ Z hX
    send_tail_top hz.H hz.Bf hz.Bm hz.Tl hz.P hSV hso s a σ hI hz.ct hcur hkt hrun hft hst hp b blk call g gr don hU)
    (fun _ h => AK.send_tail hS hA hK h)

/-- **`IpcVsFrame` for a notification cap with the send right**:
`send_tail_ntfn` at every `Z`. Named: `IpcZ`, no thread `RunningVM` on
`IRel`, the notification in `Z.N`; the arch relation by `ARKeep`. -/
theorem ipcVsFrame_notification {AR : A → Fl4Spec.Cr3 → Prop} {s : S} {a : A} {σ σ1 : Fl4Spec.State Unit}
    {ct : U64} (hcur : σ.curThread = ct.bv) {xt : Fl4Spec.Tcb} (hkt : σ.kheap ct.bv = some (.tcb xt))
    (hrun : tsCode xt.tcbState < 3)
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (blk call don : Bool) (p b : U64) (rv : Bool)
    (hZ : ∀ Z : XSets, XTopAt (L := L) AR Z s a σ → IpcZ (L := L) arI σ.archState.x64CurrentCr3 s σ ct Z ∧
      (∀ s' σ', IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ' → NativeScope σ') ∧
      p ∈ Z.N)
    (hS : P0.StoreTotal st) (hA : P0.ArchTotal arI) (hK : ARKeep arI AR) :
    IpcVsFrame (L := L) arI AR s a σ σ1 ct blk call don (.Notification p b true rv) :=
  xleaf_of_irel (fun Z hX => ⟨(hZ Z hX).1.ks, (hZ Z hX).1.bt⟩) (fun Z hX hI =>
    let ⟨hz, hvm, hp⟩ := hZ Z hX
    send_tail_ntfn hz.H hz.Bf hz.Bm hz.P hvm s a σ hI hz.ct hcur hkt hrun hst hp b)
    (fun _ h => AK.signal_tail hS hA hK h)

/-- **`IpcVsFrame` for a reply cap**: `reply_tail_inv` at every `Z`. Named:
`IpcZ`, `ReplyHyps`, `min_budget`, `SchedValid` and `ObjCover` on `IRel`,
the reply in `Z.R`; the arch relation by `ARKeep`. -/
theorem ipcVsFrame_reply {AR : A → Fl4Spec.Cr3 → Prop} {s : S} {a : A} {σ σ1 : Fl4Spec.State Unit}
    {ct : U64} (hcur : σ.curThread = ct.bv) {xt : Fl4Spec.Tcb} (hkt : σ.kheap ct.bv = some (.tcb xt))
    (hrun : tsCode xt.tcbState < 3) (hft : xt.tcbFault = none)
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (blk call don : Bool) (p : U64) (g : Bool)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hZ : ∀ Z : XSets, XTopAt (L := L) AR Z s a σ → IpcZ (L := L) arI σ.archState.x64CurrentCr3 s σ ct Z ∧
      ReplyHyps st arI Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c ∧
      (∀ s' σ', IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ' → Sched.SchedValid σ') ∧
      (∀ s' σ', IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ' →
        Sched.ObjCover Z.N Z.T Z.E Z.R Z.C σ') ∧
      (∀ s' σ', IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ' → Sched.IpcSorted σ') ∧
      p ∈ Z.R)
    (hS : P0.StoreTotal st) (hA : P0.ArchTotal arI) (hK : ARKeep arI AR) :
    IpcVsFrame (L := L) arI AR s a σ σ1 ct blk call don (.Reply p g) :=
  xleaf_of_irel (fun Z hX => ⟨(hZ Z hX).1.ks, (hZ Z hX).1.bt⟩) (fun Z hX hI =>
    let ⟨hz, hRH, hSV, hOC, hIS, hp⟩ := hZ Z hX
    reply_tail_inv hz.H hz.Bf hz.Bm hz.P hRH hz.Tl hmb hSV hOC hIS s a σ hI hz.ct hcur hkt hrun hft hst hp g)
    (fun _ h => AK.reply_tail hS hA hK h)

end

end

end Fl4Proofs.P3
