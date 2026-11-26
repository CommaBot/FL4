/-
P2 (iolay gen 4): **E2EVFl4W12 — vmF's `hyt` derived from the YieldScope spec invariant** (new definitions only, on
top of W11; no existing statement changes; no `kernel_entry_reach*` touched).

1. **`hyt`** (vmF, W10's [J] "`YIELD_TO = 0` of the dequeued handler"): **derived** (`SlJAtZ.hytY`). At the
   post-`update_timestamp` state the handler `dest` is the head of the fault endpoint's receive queue in state
   `TS_BLOCKED_ON_RECV` (P1 `faultRecv_ofT`, `faultEntAt_ofT` over `SlJAtZ.footU`), a TCB of the heap; the state word is
   the entry state's (`ut_tcb`); the TCB is in `JAtZ`'s `Z.T` (`JPlaced.tcb`, `JAtZ.thT`); and line YS's
   `JAtZ.yield0_recv` (P3/JYieldScope: `TcbRel.st` makes it `blockedOnReceive`, `YieldScopeS` makes its `tcbYieldTo`
   none, `YieldRel.tcb` makes the word 0) closes it, given **`YieldScopeS` of the bundle's spec state**.
2. That spec fact is the new entry fact **`ys` [J]** (`SlJAtY`: a clause-7 bundle at the start state whose spec state
   satisfies `YieldScopeS`). It is a spec invariant, not an FL4 word fact: P3's `kernel_entry_yieldScopeU29` carries
   `YieldScopeS ∧ CurYieldNone` at every `JReachY` state and every kernel exit (SpecInvYieldScope*: every spec step
   keeps it; `boot_yieldScope'` at `initASt`). It is not discharged here because `ChainOf`'s chains are `JReachSt`
   chains of `JReachU17` states (no YieldScope component) and the bundle's spec state is `SlJAt`'s witness, not the
   chain's; carrying YieldScope along the local steps (`LocAllSt`) is the next step.
3. **`ry`** (vmR, the ReplyRecv receiver's `YIELD_TO = 0`): **stays [J]**. Its thread `u` is the reply's caller,
   `TS_BLOCKED_ON_REPLY` (P1 `RRChecksG.ust`), not receive-blocked, so `YieldScopeS` says nothing about it. It needs the
   stronger invariant "`tcbYieldTo ≠ none` ⇒ not blocked at all" (receive, reply, send, notification), true at
   reachable states by the same argument (a thread blocks only as the current thread of its own entry, whose yield is
   none; a queued sender made `blockedOnReply` by `replyPush` had none either); its preservation needs the exempt-list
   proofs for every blocking writer (`sendIpc`, `receiveSignal`, `replyPush`, the fault sends), not written.
4. `VmFEntJ12` (= `VmFEntJ10` with `ys` [J] for `hyt` [J]) / `.toJ10` (given the chain's `run`), `slJAtY_of`
   (satisfiability: any bundle whose spec state carries YieldScope, e.g. one from a `JReachY` state),
   `StartP3W12`, `startAt_P3W12`, **`serializable_fl4_localW12`** (premises as W11).

| slot | removed | added |
|---|---|---|
| vmF | `hyt` [J] (FL4 word fact) | `ys` [J] (`YieldScopeS` of the start bundle's spec state) |
| vmR | — | — (`ry` [J] stays, item 3) |
-/
import Fl4Proofs.P2.E2EVFl4W11
import Fl4Proofs.P3.JYieldScope
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap Fl4Proofs.P0.Consts
open Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P3.Vs

section hyt
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type} {ar : machine.Arch A}
variable {K : KLayout} {s : S} {A' : Type} {arI : machine.Arch A'} {AR : A' → Fl4Spec.Cr3 → Prop}
  {Zx : Fl4Proofs.P3.XSets} {Cx Ax : Set U64} {Lst : U64 → List U64} {D : Set U64} {a' : A'}
  {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 4000000 in
/-- **vmF's `hyt` from YieldScope at the bundle's spec state** (module docstring, item 1). -/
theorem SlJAtZ.hytY (hA : P0.ArchTotal ar) (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ)
    (hY : Fl4Proofs.P3.SInv.YieldScopeS σ)
    (hrun : L.mem s (Fl4Proofs.P1.stA (L.curW s)) = sched.TS_RESTART ∨
      L.mem s (Fl4Proofs.P1.stA (L.curW s)) = sched.TS_RUNNING) :
    ∀ a s1 a1 ptr badge dest r, sched.update_timestamp st ar s a = ok (s1, a1) →
      FaultChecks st s1 (L.curW s1) ptr badge dest r → L.mem s (yieldA dest) = 0#u64 := by
  intro a s1 a1 ptr badge dest r eu C
  have HY := B.footU hA hrun a s1 a1 eu
  have et : sched.cur_thread st s1 = ok (L.curW s1) := cur_thread_ok s1
  have hrecv := faultRecv_ofT HY.bxi et HY.cap C
  have hF := faultEntAt_ofT HY.bxi et HY.nb HY.cap HY.user HY.buf HY.asid
  obtain ⟨-, rest, E⟩ := hF.2 ptr badge dest r C
  have hdT : dest ∈ Heap.tcbs K.heap := E.hq.mem dest (by simp)
  obtain ⟨hT, hN, -⟩ := B.j.bxiU.tcbNode
  obtain ⟨⟨n, a2⟩, hn, -⟩ := spec_ex_fd (hA.now a)
  rw [update_timestamp_ok (ar := ar) hN hn] at eu
  have eS := (Prod.mk.inj (ok_inj_ff eu)).1
  subst eS
  have hs : L.mem s (Fl4Proofs.P1.stA dest) = sched.TS_BLOCKED_ON_RECV := by
    rw [Fl4Proofs.P1.stA_eq, ← ut_tcb hN hT n hdT (Kx := 3328#u64) (by simp) (by simp), ← Fl4Proofs.P1.stA_eq]
    exact hrecv
  obtain ⟨Tr, Cq, hJP⟩ := B.j.jpl
  have hdZ : dest ∈ Zx.T := B.j.thT dest ((hJP.tcb dest).2 hdT)
  refine Fl4Proofs.P3.SInvR.G5.JAtZ.yield0_recv B.j hY hdZ ?_
  rw [show Fl4Proofs.P3.Notif.tStA dest = Fl4Proofs.P1.stA dest from rfl, hs]
  simp [sched.TS_BLOCKED_ON_RECV]

end hyt

end Fl4Proofs.P2.PathObl

namespace Fl4Proofs.P2.E2EV
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
open Fl4Proofs.P2.OwnMap (fld oAFFINITY region TcbSlot InW InNode)
open Fl4Proofs.P2.E2E (StartAt SP LocalPath SerStep)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg)

noncomputable section
open Classical

section ent
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)

/-- **A clause-7 bundle at `s` whose spec state carries YieldScope** (module docstring, item 2). -/
def SlJAtY (Kl : OwnMap.KLayout) (s : S) : Prop :=
  ∃ (A' : Type) (arI : machine.Arch A') (AR : A' → Fl4Spec.Cr3 → Prop) (Zx : Fl4Proofs.P3.XSets)
    (Cx Ax : Set U64) (Lst : U64 → List U64) (D : Set U64) (a' : A') (σ : Fl4Spec.State Unit),
    SlJAtZ (L := L) arI AR Zx Cx Ax Lst D Kl s a' σ ∧ Fl4Proofs.P3.SInv.YieldScopeS σ

/-- **Satisfiability of `SlJAtY`**: any bundle whose spec state carries YieldScope (e.g. a bundle read off a
`JReachY` state, P3/JYieldScope; YieldScope holds at boot, `boot_yieldScope'`). -/
theorem slJAtY_of {Kl : OwnMap.KLayout} {s : S} {A' : Type} {arI : machine.Arch A'} {AR : A' → Fl4Spec.Cr3 → Prop}
    {Zx : Fl4Proofs.P3.XSets} {Cx Ax : Set U64} {Lst : U64 → List U64} {D : Set U64} {a' : A'}
    {σ : Fl4Spec.State Unit} (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D Kl s a' σ)
    (hY : Fl4Proofs.P3.SInv.YieldScopeS σ) : SlJAtY st Kl s :=
  ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B, hY⟩

/-- **vmF's start entry facts**: `VmFEntJ10` with `hyt` [J] replaced by `ys` [J] (module docstring). -/
structure VmFEntJ12 {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop)
    (MR : A3 → Fl4Spec.MachineState → Prop) (i : VmFArg S) (K : KLayoutV) (s : S) : Prop where
  /-- No VCPU in the layout (the glue's layout choice at P3 scope). -/
  nv : K.vcpus = ∅
  /-- Index convention at `OmegaU` / `BufU` (a choice of index: `bunIxV_of`). -/
  ix : BunIxV (L := L) K.toKLayout i.T i.Cs i.Ω i.U i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac s
  /-- [P] (`NonIdle`). -/
  hct : NonIdle st arI AR MR s
  /-- [P] as `VmFPre.lk`. -/
  lk : ∀ a s1 a1 ptr badge dest r, sched.update_timestamp st ar s a = ok (s1, a1) →
    FaultChecks st s1 (L.curW s1) ptr badge dest r → i.Locks s ptr ∧ i.Locks s r
  /-- [J] a clause-7 bundle at the start state whose spec state carries YieldScope (module docstring, item 2:
  P3's `kernel_entry_yieldScopeU29` carries `YieldScopeS` at every `JReachY` state; not yet along `ChainOf`). -/
  ys : SlJAtY st K.toKLayout s
  /-- [P] -/
  gl : VmGlue st ar i.Locks s

/-- **`VmFEntJ10` from `VmFEntJ12` and the chain's `run`** (`hyt` by `SlJAtZ.hytY`). -/
theorem VmFEntJ12.toJ10 (hA : P0.ArchTotal ar) {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop}
    {MR : A3 → Fl4Spec.MachineState → Prop} {i : VmFArg S} {K : KLayoutV} {s : S}
    (E : VmFEntJ12 st ar arI AR MR i K s)
    (hrun : L.mem s (stA (L.curW s)) = sched.TS_RESTART ∨ L.mem s (stA (L.curW s)) = sched.TS_RUNNING) :
    VmFEntJ10 st ar arI AR MR i K s := by
  refine ⟨E.nv, E.ix, E.hct, E.lk, ?_, E.gl⟩
  obtain ⟨A', arI', AR', Zx, Cx, Ax, Lst, D, a', σ, B, hY⟩ := E.ys
  exact B.hytY hA hY hrun

end ent

section start
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st] {A : Type}
  (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop) (MR : A3 → Fl4Spec.MachineState → Prop)

/-- **The start fact of `fl4LocP3W6`, vmF at `VmFEntJ12`** (module docstring, item 4). -/
def StartP3W12 (Ch : S → Prop) (K : KLayoutV) (m : U64 → U64) (hK : RegionOKV K) (hU : UserOKV K) (c : U64)
    (hs : U64 → Prop) (q : SP) : Fl4IxW (S := S) → Prop
  | .vmF j => ∃ h : VmFPrem st ar j K m, GlueAt ((vmFSlot st ar hA hm).liftAt j K m hK hU h)
      (fun σ : S => Ch σ ∧ VmFEntJ12 st ar arI AR MR j K σ) c hs m q
  | i => StartP3W11 st ar hA hm hSt a0 arI AR MR Ch K m hK hU c hs q i

variable {arI AR MR}

/-- **`StartAt` of `fl4LocP3W6`'s family from `StartP3W12`**, given the current chain. -/
theorem startAt_P3W12 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR) {Ch : S → Prop}
    {K : KLayoutV} (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch)
    {m : U64 → U64} {hK : RegionOKV K} {hU : UserOKV K} {c : U64} {hs : U64 → Prop} {q : SP}
    {i : Fl4IxW (S := S)} (h : StartP3W12 st ar hA hm hSt a0 arI AR MR Ch K m hK hU c hs q i) :
    StartAt ((fl4LocP3W6 st ar hA hm hSt a0).paths (fl4Dflt st ar hm) i K m hK hU) c hs m q := by
  cases i with
  | vmF j =>
    obtain ⟨σe, hC'⟩ := hC
    obtain ⟨h, hG⟩ := h
    exact startAt_P3W11 st ar hA hm hSt a0 P hIoa ⟨σe, hC'⟩ (i := .vmF j)
      ⟨h, hG.mono fun σ he _ => ⟨he.1, he.2.toJ10 st ar hA (chain_run P hIoa hC' he.1 he.2.hct)⟩⟩
  | vmR j => exact startAt_P3W11 st ar hA hm hSt a0 P hIoa hC (i := .vmR j) h
  | io j => exact startAt_P3W11 st ar hA hm hSt a0 P hIoa hC (i := .io j) h
  | st j => exact startAt_P3W11 st ar hA hm hSt a0 P hIoa hC (i := .st j) h
  | irq j => exact startAt_P3W11 st ar hA hm hSt a0 P hIoa hC (i := .irq j) h
  | sl j => exact startAt_P3W11 st ar hA hm hSt a0 P hIoa hC (i := .sl j) h
  | vq j => exact startAt_P3W11 st ar hA hm hSt a0 P hIoa hC (i := .vq j) h

end start

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **FL4 end to end at P3 scope over W6's family, vmF's `hyt` derived from YieldScope** (module docstring):
`serializable_fl4_localW11`'s statement with `StartP3W12` starts. -/
theorem serializable_fl4_localW12 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutV}
    {Ch0 Ch : S → Prop} (h0 : Init s0) (hA0 : ArmInv s0) (hB : SerExitW P K0 Ch0) (nv0 : K0.vcpus = ∅)
    (hM0 : MapsV K0 s0)
    (h : ExecW ((fl4LocP3W6 st ar hA hm hSt a0).paths (fl4Dflt st ar hm)) (StartP3W12 st ar hA hm hSt a0 arI AR MR)
      P s0 K0 Ch0 s K Ch) (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  have hE := (execV_of_WC (fun _ _ _ _ _ _ _ _ _ hC hi => startAt_P3W12 st ar hA hm hSt a0 P hIoa hC hi) hB h).1
  have hok := serExitW_ok hB (vcpuLay_empty nv0)
  exact serializable_fl4_localP3W6V st ar hA hm hSt a0 h0 hA0 hok.1 hok.2 hM0 hE hq

end top

end
end Fl4Proofs.P2.E2EV
