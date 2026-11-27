/-
P2 (iolay gen 5): **E2EVFl4W13 — vmR's `ry` derived from the YieldBlock spec invariant** (new definitions only, on top
of W12; no existing statement changes; no `kernel_entry_reach*` touched).

1. **`ry`** (vmR, W11's [J] "the ReplyRecv receiver's `YIELD_TO = 0`"): **derived** (`SlJAtZ.ryB`). The receiver `u`
   (the reply's caller) is a TCB of the heap other than the current thread (`RRPl.hu` / `hut`, W11's `rrPlU`), in
   state `TS_BLOCKED_ON_REPLY` at the dispatch state (`RRChecksG.ust`); `LocalPre` writes none of its words
   (`localPre_w3`: only the current thread's `FAULT_IP` and the two timestamp words); it is in `JAtZ`'s `Z.T`; and
   line YB's `JAtZ.yield0_blk` (P3/JYieldBlock: `TcbRel.st` makes it `blockedOnReply`, `YieldBlockS` makes its
   `tcbYieldTo` none, `YieldRel.tcb` makes the word 0) closes it, given **`YieldBlockS` of the bundle's spec state**.
2. vmF's `ys` (W12, YieldScope of the bundle's spec state) now comes from the same fact (`YieldBlockS.scope`).
3. **The chain's YieldBlock states** (`ChainYB K Ch σ`: `Ch` is a `JReachSt` chain at some ghosts with layout `K`, and
   `σ` one of its states at a spec state carrying `YieldBlockS ∧ CurYieldNone`). `ChainYB.bun`: such a state has a
   clause-7 bundle at `K` whose spec state carries YieldBlock (`SlJAtYB`), hence vmF's YieldScope bundle and vmR's
   `ry`. Base and closure, no premise: `chainOfYB_exists` (at a `JReachYB` exit, `loc_chain_all`'s chain with the exit
   a `ChainYB` state, clauses 1 and 7 at the exit's own spec state), `chainCYB` its choice; `ChainYB.step` (a local
   run with a `YBOut` spec outcome, which is what each of `loc_chain_all`'s clauses 2–6 and 8–10 gives, keeps
   `ChainYB`: `ybOut_keep` from P3's `kentry_yieldBlock` / `kcall_yieldBlock` / `kcallF_yieldBlock` /
   `kirq_yieldBlock`, `SInvX` from `jreach_invU3`).
4. The P2 exits over YieldBlock: `SerExitWYB` (= `SerExitW` with a `JReachYB` exit and the `chainCYB` chain; [P] as
   `SerExitW`; P3's `kernel_entry_yieldScope2U29` gives `JReachYB` at every kernel exit from a `JReachYB` state,
   `boot_yieldBlock'` at boot), `SerExitWYB.base`, `serExitWYB_ok`, `Fl4StepWYB` / `ExecWYB` (`Fl4StepW` / `ExecW` with
   `serX` giving `SerExitWYB`), `execV_of_WYB`.
5. Starts: vmF / vmR start at a `ChainYB` state of the current chain (in place of `Ch σ`, which it implies,
   `ChainYB.ch`); `VmFEntJ13` = `VmFEntJ12` − `ys`, `VmREntJ13` = `VmREntJ11` − `ry`; `.toJ12` / `.toJ11` take the
   bundle; `StartP3W13`, `startAt_P3W13`, **`serializable_fl4_localW13`** (premises as W12, with `SerExitWYB` /
   `ExecWYB` in place of `SerExitW` / `ExecW`).
6. **The non-VM syscall fast paths' `hy0`** (`fastpath.fault` / `reply_recv_found`, `SlPreB.hy0f` / `hy0r`, the shared
   gap of iolay gen 4): derived, `SlPreBY.toBY` (`SlJAtZ.yield0LP`: a heap TCB read `TS_BLOCKED_ON_RECV` (the fault
   handler, `hrecv`) or `TS_BLOCKED_ON_REPLY` (the receiver, `RRChecks.ust`) at the dispatch state has `YIELD_TO = 0`
   under YieldBlock of the bundle). The sl start fact asks `SlQY` (`SlPreB` without the two fields) at a `ChainYB`
   state; `SlQY.toQ` gives W6's `SlQ`.

| slot | removed | added |
|---|---|---|
| vmF | `ys` [J] (YieldScope of the bundle) | start state a `ChainYB` state (part of the [P] start fact `GlueAt`) |
| vmR | `ry` [J] (FL4 word fact) | start state a `ChainYB` state (part of the [P] start fact `GlueAt`) |
| sl | `SlQ`'s `SlPreB` fields `hy0f` / `hy0r` (inside the [J] `SlPreB`) | start state a `ChainYB` state; `SlQY` (`SlPreBY` = `SlPreB` − `hy0f` − `hy0r`, [J] as `SlPreB`) |
| top | `SerExitW` / `ExecW` | `SerExitWYB` / `ExecWYB` (the exit a `JReachYB` state) |

Not derived here: that the glue starts a VM path only at a state of the current chain reached from the exit by the
chain's local runs (as for every other slot's `Ch σ`, [P] in `GlueAt`); given that, `SerExitWYB.base` and
`ChainYB.step` make it a `ChainYB` state.
-/
import Fl4Proofs.P2.E2EVFl4W12
import Fl4Proofs.P3.JYieldBlock
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap Fl4Proofs.P0.Consts
open Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P3.Vs

section ry
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type} {ar : machine.Arch A}
variable {K : KLayout} {s : S} {A' : Type} {arI : machine.Arch A'} {AR : A' → Fl4Spec.Cr3 → Prop}
  {Zx : Fl4Proofs.P3.XSets} {Cx Ax : Set U64} {Lst : U64 → List U64} {D : Set U64} {a' : A'}
  {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 4000000 in
/-- **vmR's `ry` from YieldBlock at the bundle's spec state** (module docstring, item 1). -/
theorem SlJAtZ.ryB (hA : P0.ArchTotal ar) (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ)
    (hY : Fl4Proofs.P3.SInv.YieldBlockS σ) {rptr ep : U64} (hfd : VmFoundC st rptr ep s) :
    ∀ a s2 a2, LocalPre (st := st) ar s a (s2, a2) →
      ∀ u usc, RRChecksG st ar fl4_abi.consts.fault.VMFault s2 a2 (L.curW s) rptr ep u usc →
        L.mem s2 (yieldA u) = 0#u64 := by
  intro a s2 a2 hLP u usc hC
  have P := B.rrPlU hA hfd a s2 a2 hLP u usc hC
  obtain ⟨hT, hN, hcT⟩ := B.j.bxiU.tcbNode
  have hW := localPre_w3 (ar := ar) hA hT hN hcT hLP
  have hu := P.hu
  have hut := P.hut
  have keep : ∀ Kx : U64, Kx.val < 4096 → Kx.val % 8 = 0 →
      L.mem s2 (core.num.U64.wrapping_add u Kx) = L.mem s (core.num.U64.wrapping_add u Kx) := by
    intro Kx hK h8
    refine hW.2.2 _ (field_aligned (hT u hu) hK h8) ?_
    rintro (e | e | e)
    · exact hut ((Fl4Proofs.P3.Notif.tt_eq_iff (hT u hu) (hT _ hcT) hK (by simp)).1 e).1
    · exact node_ne_field hN (by simp [layout.node.CUR_TIME]) hu (hT u hu) hK e.symm
    · exact node_ne_field hN (by simp [layout.node.CONSUMED]) hu (hT u hu) hK e.symm
  obtain ⟨iu, hiu, hiuc⟩ := hC.ust
  have hiu' : iu = sched.TS_BLOCKED_ON_REPLY := UScalar.eq_of_val_eq (by simpa using hiuc)
  have hus2 : L.mem s2 (Fl4Proofs.P1.stA u) = sched.TS_BLOCKED_ON_REPLY := by
    rw [eq_of_spec_fd (obj.Tcb.state.spec (L := L) s2 u)] at hiu; rw [← hiu', ok_inj_ff hiu]
  have hus : L.mem s (Fl4Proofs.P1.stA u) = sched.TS_BLOCKED_ON_REPLY := by
    rw [Fl4Proofs.P1.stA_eq, ← keep 3328#u64 (by simp) (by simp), ← Fl4Proofs.P1.stA_eq]; exact hus2
  obtain ⟨Tr, Cq, hJP⟩ := B.j.jpl
  have hdZ : u ∈ Zx.T := B.j.thT u ((hJP.tcb u).2 hu)
  have h0 := Fl4Proofs.P3.SInvR.G5.JAtZ.yield0_blk B.j hY hdZ (Or.inr (Or.inr (Or.inl (by
    rw [show Fl4Proofs.P3.Notif.tStA u = Fl4Proofs.P1.stA u from rfl, hus]; simp [sched.TS_BLOCKED_ON_REPLY]))))
  rw [show yieldA u = core.num.U64.wrapping_add u 3472#u64 from rfl, keep 3472#u64 (by simp) (by simp)]
  exact h0

end ry

/-! ## The syscall fast paths' `hy0` -/

section slY
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)

/-- **`SlPreB` without its two `YIELD_TO` fields** `hy0f` (the fault handler's) and `hy0r` (the ReplyRecv
receiver's), which `SlPreBY.toB` derives from a YieldBlock bundle. -/
structure SlPreBY (K : KLayout) (Locks : S → U64 → Prop) (m0 : U64 → U64) (n : I64) (found : U64 × U64)
    (T Cs Ω U Sg Rp Scs Nt Ac : Set U64) (H : Heap) (Z : U64 → Nat) (s : S) : Prop where
  hT : TcbPlaced T
  hN : NodePlaced st T s (L.cpu s)
  hcT : L.curW s ∈ T
  hI : ∀ a X a1, LocalPre (st := st) ar s a (X, a1) → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac X
  hAs : ∀ a X a1, LocalPre (st := st) ar s a (X, a1) → AsidOff (L := L) Ω Sg X
  aff : ∀ d, K.heap d = some .tcb → m0 (fld d oAFFINITY) = L.mem s (fld d oAFFINITY)
  hSt : K.heap (L.curW s) = some .tcb ∧ Safe0 (L.cpu s) (Locks s) (L.mem s) (L.curW s)
  -- the trap arm
  hrecv : SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) → ∀ {ptr badge dest r : U64},
    FaultChecks st X (L.curW s) ptr badge dest r → L.mem X (Fl4Proofs.P1.stA dest) = sched.TS_BLOCKED_ON_RECV
  hF : SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) →
    FaultEntAt (L := L) T Cs Ω U Sg Rp X (L.curW s)
  hTm : SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) → TimerOK st T Cs X
  hSd : SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) → ∀ {ptr badge dest r : U64},
    FaultChecks st X (L.curW s) ptr badge dest r →
      K.heap dest = some .tcb ∧ Safe0 (L.cpu s) (Locks s) (L.mem s) dest ∧
        SlWS (st := st) K Locks s (Fl4Proofs.P1.stA (L.curW s)) ∧ SlWS (st := st) K Locks s (Fl4Proofs.P1.stA dest)
  -- the ReplyRecv arm
  hPl : ¬ SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) → ∀ u usc,
    RRChecks st ar X a1 (L.curW s) found.1 found.2 u usc →
    RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z X (L.curW s) found.1 found.2 u usc
  hrz : ¬ SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) →
    L.mem X (rNextA found.1) &&& ~~~1#u64 = 0#u64 ∧ L.mem X (rPrevA found.1) &&& ~~~1#u64 = 0#u64
  hSu : ¬ SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) → ∀ u usc,
    RRChecks st ar X a1 (L.curW s) found.1 found.2 u usc →
      K.heap u = some .tcb ∧ Safe0 (L.cpu s) (Locks s) (L.mem s) u ∧
        SlWS (st := st) K Locks s (Fl4Proofs.P1.stA (L.curW s)) ∧ SlWS (st := st) K Locks s (blockA (L.curW s)) ∧ SlWS (st := st) K Locks s (Fl4Proofs.P1.stA u)
  hlk : ¬ SlTrap st s → Locks s found.2

variable {ar}

theorem SlPreBY.toB {K : KLayout} {Locks : S → U64 → Prop} {m0 : U64 → U64} {n : I64} {found : U64 × U64}
    {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s : S}
    (E : SlPreBY (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (hf : SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) → ∀ {ptr badge dest r : U64},
      FaultChecks st X (L.curW s) ptr badge dest r → L.mem X (yieldA dest) = 0#u64)
    (hr : ¬ SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) → ∀ u usc,
      RRChecks st ar X a1 (L.curW s) found.1 found.2 u usc → L.mem X (yieldA u) = 0#u64) :
    SlPreB (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s :=
  { hT := E.hT, hN := E.hN, hcT := E.hcT, hI := E.hI, hAs := E.hAs, aff := E.aff, hSt := E.hSt, hrecv := E.hrecv, hF := E.hF, hTm := E.hTm, hSd := E.hSd, hPl := E.hPl, hrz := E.hrz, hSu := E.hSu, hlk := E.hlk, hy0f := hf, hy0r := hr }

section
variable {A' : Type} {arI : machine.Arch A'} {AR : A' → Fl4Spec.Cr3 → Prop} {Zx : Fl4Proofs.P3.XSets}
  {Cx Ax : Set U64} {Lst : U64 → List U64} {D : Set U64} {a' : A'} {σ : Fl4Spec.State Unit} {K : KLayout} {s : S}

set_option maxHeartbeats 4000000 in
/-- **A heap TCB blocked on receive or on reply at the dispatch state has `YIELD_TO = 0`**, given YieldBlock of a
bundle's spec state at the entry state (`LocalPre` writes none of its words: `localPre_w3`; `JAtZ.yield0_blk`). -/
theorem SlJAtZ.yield0LP (hA : P0.ArchTotal ar) (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ)
    (hY : Fl4Proofs.P3.SInv.YieldBlockS σ) {a : A} {X : S} {a1 : A} (hLP : LocalPre (st := st) ar s a (X, a1))
    {d : U64} (hd : K.heap d = some .tcb)
    (hb : L.mem X (Fl4Proofs.P1.stA d) = sched.TS_BLOCKED_ON_RECV ∨ L.mem X (Fl4Proofs.P1.stA d) = sched.TS_BLOCKED_ON_REPLY) :
    L.mem X (yieldA d) = 0#u64 := by
  obtain ⟨hT, hN, hcT⟩ := B.j.bxiU.tcbNode
  have hW := localPre_w3 (ar := ar) hA hT hN hcT hLP
  have hu : d ∈ Heap.tcbs K.heap := hd
  have keep : ∀ Kx : U64, Kx.val < 4096 → Kx.val % 8 = 0 → Kx ≠ 392#u64 →
      L.mem X (core.num.U64.wrapping_add d Kx) = L.mem s (core.num.U64.wrapping_add d Kx) := by
    intro Kx hK h8 hne
    refine hW.2.2 _ (field_aligned (hT d hu) hK h8) ?_
    rintro (e | e | e)
    · exact hne ((Fl4Proofs.P3.Notif.tt_eq_iff (hT d hu) (hT _ hcT) hK (by simp)).1 e).2
    · exact node_ne_field hN (by simp [layout.node.CUR_TIME]) hu (hT d hu) hK e.symm
    · exact node_ne_field hN (by simp [layout.node.CONSUMED]) hu (hT d hu) hK e.symm
  have hus : L.mem s (Fl4Proofs.P1.stA d) = sched.TS_BLOCKED_ON_RECV ∨ L.mem s (Fl4Proofs.P1.stA d) = sched.TS_BLOCKED_ON_REPLY := by
    rw [Fl4Proofs.P1.stA_eq, ← keep 3328#u64 (by simp) (by simp) (by decide), ← Fl4Proofs.P1.stA_eq]; exact hb
  obtain ⟨Tr, Cq, hJP⟩ := B.j.jpl
  have hdZ : d ∈ Zx.T := B.j.thT d ((hJP.tcb d).2 hu)
  have h0 := Fl4Proofs.P3.SInvR.G5.JAtZ.yield0_blk B.j hY hdZ (by
    rw [show Fl4Proofs.P3.Notif.tStA d = Fl4Proofs.P1.stA d from rfl]
    rcases hus with h | h <;> rw [h] <;> simp [sched.TS_BLOCKED_ON_RECV, sched.TS_BLOCKED_ON_REPLY])
  rw [show yieldA d = core.num.U64.wrapping_add d 3472#u64 from rfl, keep 3472#u64 (by simp) (by simp) (by decide)]
  exact h0

set_option maxHeartbeats 4000000 in
/-- **`SlPreB` from `SlPreBY` and a YieldBlock bundle**: `hy0f` (the handler is read `TS_BLOCKED_ON_RECV`, `hrecv`,
and is a heap TCB, `hSd`) and `hy0r` (the receiver is read `TS_BLOCKED_ON_REPLY`, `RRChecks.ust`, and is a heap
TCB, `hSu`) by `SlJAtZ.yield0LP`. -/
theorem SlPreBY.toBY (hA : P0.ArchTotal ar) (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ)
    (hY : Fl4Proofs.P3.SInv.YieldBlockS σ) {Locks : S → U64 → Prop} {m0 : U64 → U64} {n : I64}
    {found : U64 × U64} {Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
    (E : SlPreBY (st := st) ar K Locks m0 n found K.heap.tcbs Cs Ω U Sg Rp Scs Nt Ac H Z s) :
    SlPreB (st := st) ar K Locks m0 n found K.heap.tcbs Cs Ω U Sg Rp Scs Nt Ac H Z s := by
  refine E.toB ?_ ?_
  · intro hS a X a1 LP ptr badge dest r C
    exact B.yield0LP hA hY LP (E.hSd hS a X a1 LP C).1 (Or.inl (E.hrecv hS a X a1 LP C))
  · intro hS a X a1 LP u usc C
    refine B.yield0LP hA hY LP (E.hSu hS a X a1 LP u usc C).1 (Or.inr ?_)
    obtain ⟨iu, hiu, hiuc⟩ := C.ust
    have hiu' : iu = sched.TS_BLOCKED_ON_REPLY := UScalar.eq_of_val_eq (by simpa using hiuc)
    rw [eq_of_spec_fd (obj.Tcb.state.spec (L := L) X u)] at hiu
    rw [← hiu', ok_inj_ff hiu]

end

variable (st) in
/-- **`SlQ` with `SlPreBY` in place of `SlPreB`.** -/
def SlQY (ar : machine.Arch A) (Locks : S → U64 → Prop) (n : I64) (found : U64 × U64)
    (Cs Ω Sg Ac : Set U64) (K : KLayout) (m : U64 → U64) (s : S) : Prop :=
  SlPreBY (st := st) ar K Locks m n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
      K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s ∧
    SlEntL (st := st) K Locks found s ∧ SlSyncC st n found s ∧ SlAccR (st := st) ar K Locks found s

end slY

/-! ## The YieldBlock states of a chain -/

section chainYB
open Fl4Proofs.P3.SInvR.G4 Fl4Proofs.P3.SInvR.G5
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop) (MR : A3 → Fl4Spec.MachineState → Prop)

/-- **A YieldBlock state of the chain `Ch` with layout `K`** (module docstring, item 3): `Ch` is the `JReachSt` chain
at some ghosts (`ChainOf`'s shape, base `k`), `K` its layout, and `σ` a state of it at a spec state carrying
`YieldBlockS ∧ CurYieldNone`. -/
def ChainYB (K : KLayout) (Ch : S → Prop) (σ : S) : Prop :=
  ∃ (k : U64) (Z : XSets) (H : Heap) (Cx : Set U64) (nc : Nat), K = layoutJ Z H k nc ∧
    (∀ c : U64, c ∈ Cx ↔ c.val < nc) ∧
    Ch = (fun σ => ∃ (a : A3) (τ : Fl4Spec.State Unit),
      JReachSt (L := L) arI AR MR (LocAllSt (L := L) arI AR Z.th Z.B H Cx) Z.th Z.B H Cx k σ a τ) ∧
    ∃ (a : A3) (τ : Fl4Spec.State Unit),
      JReachSt (L := L) arI AR MR (LocAllSt (L := L) arI AR Z.th Z.B H Cx) Z.th Z.B H Cx k σ a τ ∧
      SInv.YieldBlockS τ ∧ SInv.CurYieldNone τ

/-- **The spec outcomes of the chain's local runs** (`loc_chain_all` clauses 2–6 and 8–10): a syscall entry from a
non-idle current thread (3, 4, 5, 8, 10), or a non-syscall event, from a non-idle current thread unless it is the
interrupt (2: `EvOut true` of `KEvSpec (.sysU _) true`, 6: the timer interrupt, 9: the VM fault). -/
def YBOut (τ τ' : Fl4Spec.State Unit) : Prop :=
  (∃ c : Fl4Spec.Syscall, τ.curThread ≠ τ.idleThread ∧
    ((), τ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c τ).1) ∨
  (∃ (fip : Bool) (ev : Fl4Spec.Event), (∀ c, ev ≠ .syscallEvent c) ∧
    (ev ≠ .interrupt → τ.curThread ≠ τ.idleThread) ∧ (fip = true → ev ≠ .interrupt) ∧ EvOut fip ev τ τ')

/-- **Every such outcome keeps YieldBlock** (P3/SpecInvYieldBlockH's tops; ft3's entry facts from `SInvX`). -/
theorem ybOut_keep {τ τ' : Fl4Spec.State Unit} (hX : SInvX τ) (hY : SInv.YieldBlockS τ) (hC : SInv.CurYieldNone τ)
    (h : YBOut τ τ') : SInv.YieldBlockS τ' ∧ SInv.CurYieldNone τ' := by
  rcases h with ⟨c, hct, hm⟩ | ⟨fip, ev, hes, hct, hfi, hO⟩
  · obtain ⟨hF, hE⟩ := SInvX.ftEntry hX hct
    exact SInv.kentry_yieldBlock true c hY hC hF hE _ hm
  · cases fip
    · simp only [EvOut] at hO
      by_cases hi : ev = .interrupt
      · subst hi
        exact SInv.kirq_yieldBlock true hY hC _ hO
      · obtain ⟨hF, hE⟩ := SInvX.ftEntry hX (hct hi)
        exact SInv.kcall_yieldBlock true ev hi hes hY hC hF hE _ hO
    · have hi := hfi rfl
      simp only [EvOut] at hO
      obtain ⟨w, hw, hO⟩ := hO
      obtain ⟨hF, hE⟩ := SInvX.ftEntry hX (hct hi)
      exact SInv.kcallF_yieldBlock true ev hi hes hY hC hF hE w hw _ hO

variable {arI AR MR}

theorem ChainYB.ch {K : KLayout} {Ch : S → Prop} {σ : S} (h : ChainYB (L := L) arI AR MR K Ch σ) : Ch σ := by
  obtain ⟨k, Z, H, Cx, nc, -, -, rfl, a, τ, hR, -⟩ := h
  exact ⟨a, τ, hR⟩

/-- **The chain's YieldBlock states are closed under its local runs** (module docstring, item 3): if from every
`JReachSt` spec state of `σ` a local run reaches `σ'` with a `YBOut` outcome in the chain (what each `loc_chain_all`
clause 2–6, 8–10 gives), then `σ'` is a YieldBlock state of the chain. -/
theorem ChainYB.step (hnd : Fl4Spec.numDomains = 1) {K : KLayout} {Ch : S → Prop} {σ σ' : S}
    (h : ChainYB (L := L) arI AR MR K Ch σ)
    (hs : ∀ (k : U64) (Z : XSets) (H : Heap) (Cx : Set U64) (nc : Nat), K = layoutJ Z H k nc →
      (∀ c : U64, c ∈ Cx ↔ c.val < nc) →
      Ch = (fun σ => ∃ (a : A3) (τ : Fl4Spec.State Unit),
        JReachSt (L := L) arI AR MR (LocAllSt (L := L) arI AR Z.th Z.B H Cx) Z.th Z.B H Cx k σ a τ) →
      ∀ (a : A3) (τ : Fl4Spec.State Unit),
      JReachSt (L := L) arI AR MR (LocAllSt (L := L) arI AR Z.th Z.B H Cx) Z.th Z.B H Cx k σ a τ →
      ∃ (a' : A3) (τ' : Fl4Spec.State Unit), YBOut τ τ' ∧
        JReachSt (L := L) arI AR MR (LocAllSt (L := L) arI AR Z.th Z.B H Cx) Z.th Z.B H Cx k σ' a' τ') :
    ChainYB (L := L) arI AR MR K Ch σ' := by
  obtain ⟨k, Z, H, Cx, nc, hK, hn, hCh, a, τ, hR, hY, hC⟩ := h
  obtain ⟨a', τ', hO, hR'⟩ := hs k Z H Cx nc hK hn hCh a τ hR
  obtain ⟨-, -, -, -, -, -, -, hX, -⟩ := jreach_invU3 hnd hR.reach.1
  have h2 := ybOut_keep hX hY hC hO
  exact ⟨k, Z, H, Cx, nc, hK, hn, hCh, a', τ', hR', h2.1, h2.2⟩

/-- **A chain built at a `JReachYB` exit with its exit a YieldBlock state** (`loc_chain_all` clauses 1 and 7 at the
exit's own spec state). -/
theorem chainOfYB_exists [Fl4Proofs.P1.PlainStore st] (P : LocPlat st arI AR MR) {σe : S} {a3 : A3}
    {τ : Fl4Spec.State Unit} (h : JReachYB (L := L) arI AR MR σe a3 τ) :
    ∃ KC : KLayout × (S → Prop), ChainOf (L := L) arI AR MR σe KC.1 KC.2 ∧
      ChainYB (L := L) arI AR MR KC.1 KC.2 σe := by
  obtain ⟨Z, H, Cx, nc, hnc, hK, hU, -, h1, -, -, -, -, -, h7, -, -, -⟩ :=
    loc_chain_all P.ari P.tot P.nd P.mach P.kd P.io P.pa P.ia P.t P.max P.tu P.ref P.pi P.sx P.dr h.1
  exact ⟨(layoutJ Z H (L.ksb σe) nc, fun σ => ∃ (a : A3) (τ : Fl4Spec.State Unit),
      JReachSt (L := L) arI AR MR (LocAllSt (L := L) arI AR Z.th Z.B H Cx) Z.th Z.B H Cx (L.ksb σe) σ a τ),
    ⟨Z, H, Cx, nc, rfl, hnc, rfl, ⟨hK, hU, fun σ ⟨a, τ', hσ⟩ => h7 σ a τ' hσ⟩, ⟨a3, τ, h1⟩⟩,
    ⟨L.ksb σe, Z, H, Cx, nc, rfl, hnc, rfl, a3, τ, h1, h.2.1, h.2.2⟩⟩

/-- **The chain chosen at a `JReachYB` exit** (a choice from `chainOfYB_exists`). -/
noncomputable def chainCYB [Fl4Proofs.P1.PlainStore st] (P : LocPlat st arI AR MR) {σe : S} {a3 : A3} {τ : Fl4Spec.State Unit}
    (h : JReachYB (L := L) arI AR MR σe a3 τ) : KLayout × (S → Prop) :=
  Classical.choose (chainOfYB_exists P h)

theorem chainCYB_spec [Fl4Proofs.P1.PlainStore st] (P : LocPlat st arI AR MR) {σe : S} {a3 : A3}
    {τ : Fl4Spec.State Unit} (h : JReachYB (L := L) arI AR MR σe a3 τ) :
    ChainOf (L := L) arI AR MR σe (chainCYB P h).1 (chainCYB P h).2 ∧
      ChainYB (L := L) arI AR MR (chainCYB P h).1 (chainCYB P h).2 σe :=
  Classical.choose_spec (chainOfYB_exists P h)

end chainYB

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

/-- **A clause-7 bundle at `s` whose spec state carries YieldBlock** (module docstring, item 3). -/
def SlJAtYB (Kl : OwnMap.KLayout) (s : S) : Prop :=
  ∃ (A' : Type) (arI : machine.Arch A') (AR : A' → Fl4Spec.Cr3 → Prop) (Zx : Fl4Proofs.P3.XSets)
    (Cx Ax : Set U64) (Lst : U64 → List U64) (D : Set U64) (a' : A') (σ : Fl4Spec.State Unit),
    SlJAtZ (L := L) arI AR Zx Cx Ax Lst D Kl s a' σ ∧ Fl4Proofs.P3.SInv.YieldBlockS σ

theorem SlJAtYB.toY {Kl : OwnMap.KLayout} {s : S} (h : SlJAtYB st Kl s) : SlJAtY st Kl s := by
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B, hY⟩ := h
  exact ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B, hY.scope⟩

/-- **Satisfiability of `SlJAtYB`**: any bundle whose spec state carries YieldBlock (e.g. one read off a `JReachYB`
state, P3/JYieldBlock; YieldBlock holds at boot, `boot_yieldBlock'`). -/
theorem slJAtYB_of {Kl : OwnMap.KLayout} {s : S} {A' : Type} {arI : machine.Arch A'} {AR : A' → Fl4Spec.Cr3 → Prop}
    {Zx : Fl4Proofs.P3.XSets} {Cx Ax : Set U64} {Lst : U64 → List U64} {D : Set U64} {a' : A'}
    {σ : Fl4Spec.State Unit} (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D Kl s a' σ)
    (hY : Fl4Proofs.P3.SInv.YieldBlockS σ) : SlJAtYB st Kl s :=
  ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B, hY⟩

/-- **`SlQ` from `SlQY` at a state with a YieldBlock bundle** (`SlPreBY.toBY`). -/
theorem SlQY.toQ (hA : P0.ArchTotal ar) {Locks : S → U64 → Prop} {n : I64} {found : U64 × U64}
    {Cs Ω Sg Ac : Set U64} {Kl : OwnMap.KLayout} {m : U64 → U64} {s : S} (hB : SlJAtYB st Kl s)
    (h : SlQY st ar Locks n found Cs Ω Sg Ac Kl m s) : Fl4Proofs.P2.PathObl.SlQ st ar Locks n found Cs Ω Sg Ac Kl m s := by
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B, hY⟩ := hB
  exact ⟨h.1.toBY hA B hY, h.2⟩

/-- **vmF's start entry facts**: `VmFEntJ12` without `ys` [J] (now from the start state's `ChainYB`). -/
structure VmFEntJ13 {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop)
    (MR : A3 → Fl4Spec.MachineState → Prop) (i : VmFArg S) (K : KLayoutV) (s : S) : Prop where
  nv : K.vcpus = ∅
  ix : BunIxV (L := L) K.toKLayout i.T i.Cs i.Ω i.U i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac s
  /-- [P] (`NonIdle`). -/
  hct : NonIdle st arI AR MR s
  /-- [P] as `VmFPre.lk`. -/
  lk : ∀ a s1 a1 ptr badge dest r, sched.update_timestamp st ar s a = ok (s1, a1) →
    FaultChecks st s1 (L.curW s1) ptr badge dest r → i.Locks s ptr ∧ i.Locks s r
  /-- [P] -/
  gl : VmGlue st ar i.Locks s

/-- **vmR's start entry facts**: `VmREntJ11` without `ry` [J] (now from the start state's `ChainYB`). -/
structure VmREntJ13 {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop)
    (MR : A3 → Fl4Spec.MachineState → Prop) (i : VmRArg S) (Kl : OwnMap.KLayout) (s : S) : Prop where
  ix : BunIxU (L := L) Kl Kl.heap.tcbs i.Cs i.Ω Kl.heap i.Sg Kl.heap.replies Kl.heap.scs Kl.heap.ntfns
    Kl.heap.scBits i.Ac s
  /-- [P] (`NonIdle`). -/
  hct : NonIdle st arI AR MR s
  /-- [P] -/
  lk : i.Locks s i.rptr ∧ i.Locks s i.ep
  /-- [P] -/
  nb : L.mem s (rPrevA i.rptr) = 0#u64 ∧ L.mem s (rNextA i.rptr) = 0#u64
  /-- `loc_chain_all` clause 10's fl4-sync input `hfd`. -/
  fd : VmFoundC st i.rptr i.ep s

/-- `ry` from a YieldBlock bundle at any layout (`SlJAtZ.ryB` does not use the layout). -/
theorem VmREntJ13.toJ11 (hA : P0.ArchTotal ar) {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop}
    {MR : A3 → Fl4Spec.MachineState → Prop} {i : VmRArg S} {Kl Kb : OwnMap.KLayout} {s : S}
    (E : VmREntJ13 st arI AR MR i Kl s) (yb : SlJAtYB st Kb s) : VmREntJ11 st ar arI AR MR i Kl s := by
  refine ⟨E.ix, E.hct, ?_, E.lk, E.nb, E.fd⟩
  obtain ⟨A', arI', AR', Zx, Cx, Ax, Lst, D, a', σ, B, hY⟩ := yb
  exact B.ryB hA hY E.fd

end ent

section exec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **The serial exit's ghost choice at a YieldBlock exit** [P] (module docstring, item 3): `SerExitW` with the exit a
`JReachYB` state (every kernel exit from one is one, P3's `kernel_entry_yieldScope2U29`; boot `boot_yieldBlock'`) and
the chain chosen by `chainCYB`. -/
def SerExitWYB (P : LocPlat st arI AR MR) (K : KLayoutV) (Ch : S → Prop) : Prop :=
  ∃ (σe : S) (a3 : A3) (τ : Fl4Spec.State Unit) (hJ : Fl4Proofs.P3.SInvR.G5.JReachYB (L := L) arI AR MR σe a3 τ),
    chainCYB P hJ = (K.toKLayout, Ch)

theorem SerExitWYB.chainOf {P : LocPlat st arI AR MR} {K : KLayoutV} {Ch : S → Prop} (h : SerExitWYB P K Ch) :
    ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch ∧ ChainYB (L := L) arI AR MR K.toKLayout Ch σe := by
  obtain ⟨σe, a3, τ, hJ, e⟩ := h
  have hs := chainCYB_spec P hJ
  rw [e] at hs
  exact ⟨σe, hs⟩

/-- **The base**: the exit is a YieldBlock state of the chosen chain. -/
theorem SerExitWYB.base {P : LocPlat st arI AR MR} {K : KLayoutV} {Ch : S → Prop} (h : SerExitWYB P K Ch) :
    ∃ σe, ChainYB (L := L) arI AR MR K.toKLayout Ch σe :=
  let ⟨σe, _, h2⟩ := h.chainOf; ⟨σe, h2⟩

variable {ι : Type}

/-- **`Fl4StepW` with the serial exit at a YieldBlock exit** (`serX` gives `SerExitWYB`). -/
structure Fl4StepWYB (LP : PathsV ι)
    (SF : (S → Prop) → ∀ K : KLayoutV, (U64 → U64) → RegionOKV K → UserOKV K → U64 → (U64 → Prop) → SP → ι → Prop)
    (P : LocPlat st arI AR MR) (s : Cfg U64 U64 U64 U64) (K : KLayoutV) (Ch : S → Prop) (c : U64)
    (s' : Cfg U64 U64 U64 U64) (K' : KLayoutV) (Ch' : S → Prop) : Prop where
  /-- [P] an armed program is pure glue (as `Fl4StepV.arm`). -/
  arm : ∀ p, s'.ph c = .arm p → PureGlue p
  /-- [P] the glue's start: the start fact of some path. -/
  start : ∀ p0 k W, s.ph c = .loc p0 (.start k) W → ∀ (hK : RegionOKV K) (hU : UserOKV K),
    ∃ i, SF Ch K s.mem hK hU c (fun l => s.lk l = some c) k i
  /-- [P] the serial exit's ghost choice, at a YieldBlock exit. -/
  serX : SerStep s c → SerExitWYB P K' Ch'
  /-- [J] the new layout's VCPU facts (vacuous at `K'.vcpus = ∅`). -/
  serV : SerStep s c → VcpuLay L K'
  /-- [P] the exit ghost with rule 7. -/
  serG : SerStep s c → ExitGhostV K' s'
  /-- Layout and chain change only at serial steps. -/
  keep : ¬ SerStep s c → K' = K ∧ Ch' = Ch

/-- **`ExecW` with `Fl4StepWYB` steps.** -/
inductive ExecWYB (LP : PathsV ι)
    (SF : (S → Prop) → ∀ K : KLayoutV, (U64 → U64) → RegionOKV K → UserOKV K → U64 → (U64 → Prop) → SP → ι → Prop)
    (P : LocPlat st arI AR MR) (s0 : Cfg U64 U64 U64 U64) (K0 : KLayoutV) (Ch0 : S → Prop) :
    Cfg U64 U64 U64 U64 → KLayoutV → (S → Prop) → Prop
  | refl : ExecWYB LP SF P s0 K0 Ch0 s0 K0 Ch0
  | step {s s' : Cfg U64 U64 U64 U64} {K K' : KLayoutV} {Ch Ch' : S → Prop} {c : U64} :
      ExecWYB LP SF P s0 K0 Ch0 s K Ch → Step s c s' → Fl4StepWYB LP SF P s K Ch c s' K' Ch' →
      ExecWYB LP SF P s0 K0 Ch0 s' K' Ch'
  | hw {s : Cfg U64 U64 U64 U64} {K : KLayoutV} {Ch : S → Prop} {v a x : U64} :
      ExecWYB LP SF P s0 K0 Ch0 s K Ch → HwStepV K s v a x → ExecWYB LP SF P s0 K0 Ch0 (hwCfg s a x) K Ch

end exec

section start
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st] {A : Type}
  (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop) (MR : A3 → Fl4Spec.MachineState → Prop)

variable {arI AR MR}

end start

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

end top

end
end Fl4Proofs.P2.E2EV
