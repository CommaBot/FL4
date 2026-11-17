/-
P3 (DESIGN.md §9): **the joint invariant at a state, `JAt`** (the fold plan's
§1, `/home/user/Projects/.fl4-fold-plan.md`). One structure over the ghosts
(the typed heap and sets `Z`, P1's heap `H`, cores `Cs`, active SCs `Ac`,
the ghost call stacks `Lst`, the dead set `D`), grouped as the plan's 1a–1e:

* 1a the refinement relation: `XTopAt`, the call stacks (`CallRel`,
  `RFree`), yield, MCP, IPC-buffer words;
* 1b placement: the ghost sets placed and exhaustive, P1's heap `H` over the
  typed heap (`JPlaced`, `SpecCover`, `ObjCover`), `SpecFree`, the dead set
  (`JCovD`), the kernel-global placement (`JKern`);
* 1c CSpace: `DelInv`, `UtInv`, the CNode-size and fuel bound (`DelBound`),
  the untyped caps' facts (`UtCapP3`);
* 1d scheduler: `NSC`, `Inv`, `CurInv`, `OffOK`, `ActIdle`, `BlockedScActive`
  ([J]), `SchedValid`, `IpcSorted`, `CurRun`;
* 1e P1: `BlkOK` over `H`'s sets.

Projections to each leaf bundle: `WX`, `DState`, `IpcZ`, `ScExtra`,
`UtJoint`/`UtP3Ok`, `RemoveOK`, `DonNCOK`, `DonOK`, `PushDonOK`, and the P1
placement facts (`JAtZ.capTyped`, `JAtZ.slotCapW`, `JAtZ.mpPlaced`).

No preservation is proved here. Fields marked **[carried]** are facts the
projections need that the plan's groups did not list; several are derivable
from the others (noted per field) and are to be dropped once derived.
Projection premises marked **[global]** are not state facts (the platform,
or "∀ related states" hypotheses that the fold re-scopes, plan §0).

Merges (plan §1): `ARIface` (`ARKeep` with `ARMask`), `DelBound.delE`
(CnodeAll's `K`, `hK`, `hK6` and `DelE` from `DelBound`), `SchedValid.toLink`
(`ScLinkHyp`, whose `scSpor` is `SchedValid.scSpor`).
-/
import Fl4Proofs.P3.XTopCnodeAll
import Fl4Proofs.P3.XTopTcbAll
import Fl4Proofs.P3.IpcSendDon
import Fl4Proofs.P3.ScXProd
import Fl4Proofs.P3.ScUtRetype
import Fl4Proofs.P3.ScIpcSorted
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

/-! ## Merges -/

section
variable {A : Type} (arI : machine.Arch A)

/-- **The arch relation's interface** (`ARKeep` with `ARMask`, one premise). -/
structure ARIface (AR : A → Fl4Spec.Cr3 → Prop) : Prop extends ARKeep arI AR where
  mask : ∀ a c a', AR a c → ArchIrqStep arI a a' → AR a' c

theorem ARIface.toMask {AR : A → Fl4Spec.Cr3 → Prop} (h : ARIface arI AR) : ARMask arI AR := h.mask

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`DelBound` gives the CNode deletions' bound and `DelE`** (CnodeAll's
`K`, `hK`, `hK6`, `hDE`), with `DelInv`, `KTyped` and `FinM` at every tree. -/
theorem DelBound.delE {th : TypedHeap} (hB : DelBound th) {s : S} {σ : Fl4Spec.State Unit}
    (hD : DelInv th (L.mem s)) (hK : KTyped th σ) (hF : ∀ G, MdbLinks th (L.mem s) G → FinM (L.mem s) G) :
    ∃ K, (∀ p r, th p = some (.cnode r) → 2 ^ r ≤ K) ∧ 6 ≤ K ∧ DelE (L := L) th K s σ := by
  obtain ⟨K, h1, h2, h3⟩ := hB
  exact ⟨K, h1, h2, hD, fun G hG => h3 _ G hG, hK, hF⟩

end

/-- **`ScLinkHyp` is part of `SchedValid`** (its `scSpor` is `SchedValid.scSpor`). -/
theorem Sched.SchedValid.toLink {σ : Fl4Spec.State Unit} (h : Sched.SchedValid σ) : Sched.ScLinkHyp σ :=
  ⟨h.scTcb, h.scNtfn, h.tcbNtfn, h.scSpor⟩

/-! ## `JAt` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **[carried] The kernel-global placement and the current thread** (what
`UtJoint` reads): the original caps' slots, the current thread (a TCB of
`th` and of `H`, the spec's), the current SC (an `H` object, live), the
scheduler-action word outside the objects, core 0's debug-list head and
word, the global PML4, and `H` well formed and off the kernel-global area
and the nodes. Several are derivable (`cur`, `curT`: `SchedRel`/`CurOK`;
`heap`, `h0`, `hks`, `hnd`: `BlkOK`/`JPlaced`). -/
structure JKern (H : P1.Heap) (Cs D : Set U64) (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) : Prop where
  orig : ∀ sl, σ.isOriginalCap sl = true → AbsSlot th sl
  cur : σ.curThread = (L.curW s).bv
  curT : th (L.curW s) = some .tcb
  act : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION)
  dwAl : P1.Aligned (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)
  dwObj : ∀ a, IsSlot th a → ¬ (a.val ≤ (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ∧
    (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val < a.val + 32)
  dwNe : (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ≠ (P1.stA (L.curW s)).val ∧
    (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ≠ (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val
  head : L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = 0#u64 ∨
    (th (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) = some .tcb ∧
      TcbOk (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)))
  gpm : HasPm σ σ.archState.x64GlobalPml4
  ga : σ.archState.x64GlobalPml4.toNat % 4096 = 0
  gf : σ.archState.x64GlobalPml4.toNat + 4096 ≤ 2 ^ 64
  heap : P1.HeapOK H
  h0 : H 0#u64 = none
  hks : ∀ p k, H p = some k → p.val + 2 ^ k.bits ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ p.val
  hnd : ∀ p k, H p = some k → ∀ c ∈ Cs, p.val + 2 ^ k.bits ≤ L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ p.val
  ksbFit : (L.ksb s).val + 13568 ≤ 2 ^ 64
  ksbAl : (L.ksb s).val % 8 = 0
  nodeFit : (L.ksb s).val + 13568 + ((L.cpu s).val + 1) * 4288 ≤ 2 ^ 64
  cpuCs : L.cpu s ∈ Cs
  curH : H (L.curW s) = some .tcb
  cscH : H (L.cscW s) ≠ none
  cscLive : L.cscW s ∉ D
  /-- [carried] The cores are numbered below 64 (boot; `Cs` never grows). -/
  csLt : ∀ c ∈ Cs, c.val < 64

/-- **The joint invariant at the ghosts** (module docstring; plan §1). -/
structure JAtZ (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64)
    (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  -- 1a: the refinement relation
  xtop : XTopAt (L := L) AR Z s a σ
  call : Sched.CallRel (L.mem s) Z.R Z.C σ Lst
  rfree : Sched.RFree (L.mem s) Z.R Z.C σ Lst
  yld : Sched.YieldRel Z.T Z.C (L.mem s) σ
  mcp : Sched.McpRel Z.T (L.mem s) σ
  buf : BufWordRel Z.T (L.mem s) σ
  -- 1b: placement
  ks : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s)
  thT : ∀ t, Z.th t = some .tcb → t ∈ Z.T
  /-- [carried] `Z.th` holds TCBs and CNodes only (its one producer, the
  retype's `ThX`, adds `thKindN`'s kinds; deletions only drop entries). -/
  thk : ∀ q k, Z.th q = some k → k = .tcb ∨ ∃ r, k = .cnode r
  ip : IPlaced Z.N Z.T Z.E Z.R Z.B
  rp : Sched.RPlaced st Z.N Z.T Z.C Z.R Z.c s σ
  apart : Sched.SlotsApart (st := st) Z.th Z.T Z.N Z.C Z.R Z.c s σ
  nk : ∀ n ∈ Z.N, n.val + 40 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ n.val
  /-- [carried] The IPC-buffer words miss every core's node ([W] producer: the
  buffer words' frames). -/
  nodeB : ∀ wp ∈ Z.B, ∀ c ∈ Cs, wp.1.val + 8 ≤ L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ wp.1.val
  jpl : ∃ Tr Cq, Sched.JPlaced (L := L) Z.th H Tr Cq s σ
  cover : Sched.SpecCover H σ
  obj : Sched.ObjCover Z.N Z.T Z.E Z.R Z.C σ
  /-- [carried] The sets' objects are `H`'s (derivable: `IpcRel`/`SchedRel`
  and `SpecCover`, `JPlaced`). -/
  zH : (∀ t ∈ Z.T, H t = some .tcb) ∧ (∀ e ∈ Z.E, H e = some .ep) ∧ (∀ r ∈ Z.R, H r = some .reply) ∧
    (∀ n ∈ Z.N, H n = some .ntfn)
  sfree : Sched.SpecFree (L.mem s) Z.G σ
  /-- [carried] `H`'s endpoints, notifications and replies are the sets'
  (the converse of `zH`; for the `SchedValid` rebuild). -/
  hset : (∀ e, H e = some .ep → e ∈ Z.E) ∧ (∀ n, H n = some .ntfn → n ∈ Z.N) ∧
    (∀ r, H r = some .reply → r ∈ Z.R)
  jcov : Sched.JCovD (L := L) Z.th H Z.G D Cs s
  kern : JKern (L := L) H Cs D Z.th s σ
  -- 1c: CSpace
  del : DelInv Z.th (L.mem s)
  ut : UtInv (L.mem s) Z.G
  bound : DelBound Z.th
  /-- [carried] `FinM` at every tree of the slots (`FinInv` gives it at
  `Z.G`; `DelE` reads every `G`). -/
  finM : ∀ G, MdbLinks Z.th (L.mem s) G → FinM (L.mem s) G
  /-- [carried] The untyped caps' facts (`UtCapP3`: l4v `valid_untyped`,
  `valid_cap`, the kernel's placement). -/
  utc : ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi dev) →
    Sched.UtCapP3 (L := L) arI Z.th s σ Z.G sl p sb fi
  -- 1d: the scheduler
  nsc : Sched.NSC Z.N Z.C σ
  inv : Sched.Inv σ
  /-- `CurInv` unless a reschedule is pending (mid-entry, as `ScEntry`). -/
  cur : σ.schedulerAction = .chooseNewThread ∨ Sched.CurInv σ
  /-- The current SC's owner, or the current SC unowned (`CurOwnW`, what
  `schedule` from a mid-entry state reads; unowned after the current thread
  deleted itself or unbound its SC; `curOwn_of_curInv` where `CurInv`
  holds). -/
  own : Sched.CurOwnW Z.T Z.C σ
  off : Sched.OffOK σ
  act : Sched.ActIdle σ
  c0 : ∀ q ∈ Z.C, q ≠ 0#u64
  bsa : Sched.BlockedScActive σ
  sv : Sched.SchedValid σ
  /-- The spec's IPC queues sorted by priority (l4v `sorted_ipc_queues`). -/
  isorted : Sched.IpcSorted σ
  /-- The spec's SC, TCB and notification links (per-op; for the
  `SchedValid` rebuild). -/
  slink : Sched.ScLinkHyp σ
  /-- The current thread runnable, or the idle thread current (`CurRunW`:
  at kernel exit `schedule` may have chosen the idle thread). -/
  curRun : CurRunW σ
  -- 1e: P1
  blk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
    (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s
  /-- [carried] The interrupt state and node layout (`IntLayout`, the boot's
  [P]; kept by every step: `Z.th` and the kernel-state base are kept). -/
  intL : IntLayout Z.th (L.ksb s)

/-- **`JAt`: the joint invariant at a state** (the ghosts existential). -/
def JAt (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ

/-! ## Projections -/

namespace JAtZ
variable {arI} {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- `WX` (the deletions' bundle). -/
theorem wx (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) : WX (L := L) AR Z.th s a σ Z.G :=
  ⟨Z, rfl, rfl, J.xtop, J.ks, J.thT⟩

/-- `DState` (the CSpace deletions' state). -/
theorem dstate (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) : DState (L := L) Z.th s σ Z.G :=
  ⟨J.xtop.rel.2.1, J.del, J.xtop.rel.2.2.1⟩

/-- CnodeAll's bound and `DelE` (`DelBound.delE`). -/
theorem delE (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    ∃ K, (∀ p r, Z.th p = some (.cnode r) → 2 ^ r ≤ K) ∧ 6 ≤ K ∧ DelE (L := L) Z.th K s σ :=
  J.bound.delE J.del J.xtop.rel.2.2.1.kt J.finM

/-- `ScLinkHyp`. -/
theorem link (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) : Sched.ScLinkHyp σ := J.sv.toLink

/-- `IpcZ`, given the IPC tails' [global] hypotheses (re-scoped by the fold). -/
theorem ipcZ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (cr : Fl4Spec.Cr3) {ct : U64}
    (hH : IpcSchedHyps st arI Z.N Z.T Z.E Z.R Z.B (SRT st Z.th cr Z.N Z.T Z.C Z.E Z.R Z.B Z.c
      (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c)))
    (hBf : EpBufHyps st Z.T Z.E Z.R Z.B (SRT st Z.th cr Z.N Z.T Z.C Z.E Z.R Z.B Z.c (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c)))
    (hBm : EpBufMapHyps st Z.T Z.E Z.R Z.B (SRT st Z.th cr Z.N Z.T Z.C Z.E Z.R Z.B Z.c
      (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c)))
    (hact : ∀ s σ, IpcRel Z.N Z.T Z.E Z.R Z.B (L.mem s) σ →
      SRT st Z.th cr Z.N Z.T Z.C Z.E Z.R Z.B Z.c (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c) s σ → ActReady σ)
    (hct : ct ∈ Z.T) :
    IpcZ (L := L) arI cr s σ ct Z :=
  ⟨J.ks, J.buf, hH, hBf, hBm, hact, J.ip, hct⟩

/-- `CurInv` when no reschedule is pending. -/
theorem curInv (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (h : σ.schedulerAction ≠ .chooseNewThread) :
    Sched.CurInv σ := J.cur.resolve_left h

/-- `ScExtra` (the SC decodes' bundle), given the [global] platform facts and
no reschedule pending. -/
theorem scExtra (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hres : σ.schedulerAction ≠ .chooseNewThread)
    (htm : Sched.TimeAgree arI)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hmsg : Sched.MsgOK st Z.N Z.T Z.C Z.c) :
    Sched.ScExtra (L := L) arI Z s a σ :=
  ⟨J.nsc, J.inv, J.curInv hres, J.off, J.yld, J.act, J.mcp, J.c0, ⟨Lst, J.call, J.rfree⟩, J.rp, J.apart, J.ip, J.nk,
    htm, hmb, hmax, htu, hmsg⟩

/-- `RemoveOK` (`reply_remove`'s bundle) at `r` and its caller `t`, given the
reply's caller and the donation-back facts. -/
theorem removeOK (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {r t : U64}
    (hrt : ∀ xr, σ.kheap r.bv = some (.reply xr) → xr.replyTcb = some t.bv)
    (hdr : ∀ xt, σ.kheap t.bv = some (.tcb xt) →
      (∀ sc ∈ Z.C, ∀ y n, σ.kheap sc.bv = some (.schedContext y n) → (Lst sc).head? = some r →
        xt.tcbSchedContext = none → ∃ f, f ∈ Z.T ∧ y.scTcb = some f.bv ∧ f ≠ t) ∧
      (∀ sc ∈ Z.C, ∀ y n, σ.kheap sc.bv = some (.schedContext y n) → (Lst sc).head? = some r →
        xt.tcbSchedContext = none → inClass xt.tcbState → Fl4Spec.scActive y = true → released σ y)) :
    RemoveOK st Z.N Z.T Z.C Z.R Z.c s σ r t :=
  ⟨Lst, J.call, J.rp, J.nsc, J.inv, J.c0, J.obj.sc, hrt, hdr⟩

/-- `DonNCOK` (a donating send's bundle), given the sender's SC and the
receiver's release. -/
theorem donNCOK (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t d : U64} (hsc : L.mem s (P1.scA t) ≠ 0#u64)
    (hrel : ∀ y n, σ.kheap (L.mem s (P1.scA t)).bv = some (.schedContext y n) → ∀ x, σ.kheap d.bv = some (.tcb x) →
      inClass x.tcbState → Fl4Spec.scActive y = true → released σ y) :
    DonNCOK st Z.N Z.C s σ t d :=
  ⟨hsc, J.nsc, J.inv, hrel⟩

/-- `DonOK` (the wake donation's bundle), given the notification's SC among
the SCs and the thread out of its ready queue. -/
theorem donOK (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t n : U64}
    (hn : L.mem s (nScA n) ≠ 0#u64 → L.mem s (nScA n) ∈ Z.C)
    (hq : L.mem s (P1.scA t) = 0#u64 → ∀ x, σ.kheap t.bv = some (.tcb x) →
      t.bv ∉ σ.readyQueues x.tcbDomain x.tcbPriority) :
    DonOK st Z.C s σ t n :=
  ⟨J.inv.relOK, hn, hq, J.inv.actReady⟩

/-- `PushDonOK` (a donating call's bundle), given the reply isolated and
detached and the callee's release. -/
theorem pushDonOK (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t d r : U64}
    (hiso : Sched.Isolated (L.mem s) Z.R r) (hdet : Sched.Detached Z.C Lst r)
    (hrel : ∀ y n x, σ.kheap (L.mem s (P1.scA t)).bv = some (.schedContext y n) → σ.kheap d.bv = some (.tcb x) →
      inClass x.tcbState → Fl4Spec.scActive y = true → released σ y) :
    PushDonOK st Z.N Z.T Z.C Z.R Z.c s σ t d r :=
  ⟨J.nsc, J.inv, J.rp, hiso, ⟨Lst, J.call, hdet, J.rfree⟩, hrel⟩

/-- `UtJoint` (the untyped decode's bundle) at an invoked CNode slot. -/
theorem utJoint (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {slot : obj.Slot} {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {pp : U64} {rs : Nat} {idx : List Bool}
    (hnode : Z.th pp = some (.cnode rs)) (hidx : idx.length = rs) (hslot : slot = cslotAddr (pp.bv, idx))
    (hcap : capAt (L.mem s) slot = ok cap)
    (hext : ∀ x ∈ extra.val, x ≠ 0#u64 → ∃ c a, capAt (L.mem s) x = ok c ∧ CapRel c a ∧ CapValid Z.th c) :
    Sched.UtJoint (L := L) arI H Cs s slot cap extra Z.th Z.G D σ pp rs idx := by
  obtain ⟨hP, ⟨hSR, hV, hM, hC, hI⟩, -⟩ := J.xtop.rel
  have hAs : AbsSlot Z.th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hnode)⟩
  exact ⟨J.jcov, hSR, hV, hP, hM, hC, hI, J.ut, J.kern.orig, J.sfree, J.kern.cur, J.kern.curT, J.kern.act,
    hnode, hidx, hslot, hcap, hext,
    fun p sb fi dev e => J.utc _ p sb fi dev hAs (by rw [← hslot, hcap, e]),
    J.kern.dwAl, J.kern.dwObj, J.kern.dwNe, J.kern.head, J.kern.gpm, J.kern.ga, J.kern.gf, J.kern.heap,
    J.kern.h0, J.kern.hks, J.kern.hnd, J.kern.ksbFit, J.kern.ksbAl, J.kern.nodeFit, J.kern.cpuCs,
    J.kern.curH, J.kern.cscH, J.kern.cscLive, J.jpl⟩

/-- `UtP3Ok` (P1's `P3Ok` for the untyped retype). -/
theorem utP3Ok (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {slot : obj.Slot} {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {pp : U64} {rs : Nat} {idx : List Bool}
    (hnode : Z.th pp = some (.cnode rs)) (hidx : idx.length = rs) (hslot : slot = cslotAddr (pp.bv, idx))
    (hcap : capAt (L.mem s) slot = ok cap)
    (hext : ∀ x ∈ extra.val, x ≠ 0#u64 → ∃ c a, capAt (L.mem s) x = ok c ∧ CapRel c a ∧ CapValid Z.th c) :
    Sched.UtP3Ok (L := L) arI H Cs s slot cap extra :=
  ⟨_, _, _, _, _, _, _, J.utJoint hnode hidx hslot hcap hext⟩

/-- Today's `JointInv` body at this state (P1's `BlkOK` with `JPlaced`,
`SpecCover`, `SpecFree`). -/
theorem joint (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    ∃ (H : P1.Heap) (Cs Ac Tr C : Set U64),
      P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H) (P1.Heap.scs H)
        (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s ∧ Sched.JPlaced (L := L) Z.th H Tr C s σ ∧ Sched.SpecCover H σ ∧
        Sched.SpecFree (L.mem s) Z.G σ := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  exact ⟨H, Cs, Ac, Tr, Cq, J.blk, hJ, J.cover, J.sfree⟩

/-- **P1's cap slots are cap-slot words** (`JPlaced.slotCapW`; P1's
`CdtHyps`/`XferHyps`/`DelPlace` slot fields). -/
theorem slotCapW (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hTL : Sched.TLowSlots (P1.Heap.tcbs H)) :
    Sched.SlotCapW Z.th (P1.Heap.tcbs H) (P1.Heap.omega H) (P1.Heap.frame H) :=
  by obtain ⟨_, _, hJ⟩ := J.jpl; exact hJ.slotCapW hTL

/-- **A slot's cap is typed in P1's sets** (`capTypedP1Hyp_of` at this state;
P1's `CdtHyps.slotcap`, `InvHyps.slotcap`, `P3Place`'s cap fields). -/
theorem capTyped (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hTL : Sched.TLowSlots (P1.Heap.tcbs H))
    {sl : Fl4Spec.CslotPtr} {c : capability.Cap} (hA : AbsSlot Z.th sl) (hc : capAt (L.mem s) (cslotAddr sl) = ok c) :
    ∃ X : P1Sets, P1Blk (st := st) X s ∧ Sched.SlotCapW Z.th X.T X.Ω X.Sg ∧ P1.CapTyped X.H X.Rp X.Nt c := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hty := hJ.typed _ hA.isSlot
  rw [capV_of_capAt hc] at hty
  exact ⟨⟨_, Cs, _, H, _, _, _, _, _, Ac⟩, J.blk, hJ.slotCapW hTL, hty⟩

/-- **`MpPlacedHyp`** (MakePool's placement) when no object is dead
(`JCovD` with `D = ∅` is `JCov`; with dead objects MakePool's region needs
`restrictTh`, to rework by its owner). -/
theorem mpPlaced (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hD : D = ∅) (hc : Z.c ∈ Cs)
    (hB : ∀ wp ∈ Z.B, Sched.Covered (L.mem s) Z.G wp.1.val (wp.1.val + 8)) :
    MpPlacedHyp st Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 Z.N Z.T Z.C Z.E Z.R Z.B Z.c AR s σ Z.G := by
  subst hD
  have hJC : Sched.JCov (L := L) Z.th H Z.G Cs s :=
    ⟨fun q k hq => (J.jcov.th q k hq).resolve_right (by simp), fun q k hq => (J.jcov.h q k hq).resolve_right (by simp),
      J.jcov.ks⟩
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  obtain ⟨-, ⟨-, -, -, -, hI⟩, -⟩ := J.xtop.rel
  exact mpPlacedHyp_of hJC hJ J.ut hI hc J.zH.1 J.zH.2.1 J.zH.2.2.1 J.zH.2.2.2 J.c0 hB

end JAtZ

end

end

end Fl4Proofs.P3
