/-
# P2 (line p3mc, gen 30): V13 — `yb` [J] narrowed to the word-level YieldBlock `ybw` [J]

## What `yb` asserts (V12, inside `StartV2C`)
At a vmF / vmR / sl start, the glue's chain state `σ` (the `S` state of `Ch σ` the `GlueAt` agrees with, off user
words, at `c`'s view) carries `yb : SlJAtYB st Kl σ` (P2/E2EVFl4W13), at `Kl = K.toKLayout` in all three records
(`VmFEntJ14.yb`, `VmREntU.yb` with `Kb := K.toKLayout`, `SlEntU.yb`): **there is a clause-7 bundle
`SlJAtZ … Kl σ a' τ` whose spec state `τ` has P3's `YieldBlockS`** — no spec TCB has `tcbYieldTo ≠ none` and a
blocked state (receive / send / reply / notification). Consumers: vmF's `ys` (`YieldBlockS.scope`), vmR's `ry`
(the receiver's `YIELD_TO = 0`, `SlJAtZ.ryB`), sl's `hy0f` / `hy0r` (the handler's / receiver's `YIELD_TO = 0`,
`SlJAtZ.yield0LP`).

## Not derivable from the existing invariants
* P1 says of `YIELD_TO` only that a nonzero link is a typed SC (`YT`, P1/QueueObjs l.322; `BlkOK` / `BXI` carry it);
  nothing ties it to the `STATE` word.
* The chain's bundle at `σ` (`ChainOf.bun`, the entry records' `ix`, `SlJAt`) is a `JAtZ` with `SInvX`: P3's
  `YieldRel` ties the `YIELD_TO` word to `tcbYieldTo` / `scYieldFrom` only; `JReachU3.start` admits any such state, so
  `Ch` contains states with a blocked TCB whose `YIELD_TO ≠ 0` (P2/E2EVFl4W14 docstring (a)–(c)).
* `start` [P] / `serX` [P] relate the execution to *some* chain state; neither says which.
So `yb` stays a premise. What can be done is narrow it to the word fact it stands for.

## `YBW` [J], the narrower premise
**`YBW st Kl s`**: every TCB `t` of `Kl`'s typed heap with `YIELD_TO(t) ≠ 0` has a `STATE` word that is not 3, 4, 5,
6 (`TS_BLOCKED_ON_RECV / SEND / REPLY / NTFN`, `sched.rs` l.17–20). A fact about FL4 words of `σ` only (no spec
state, no existential bundle). Given any bundle at `σ` at layout `Kl` (always present: `ChainOf.bun`):
* **`yb_of_ybw`**: `SlJAt Kl σ → YBW Kl σ → SlJAtYB Kl σ` (`JAtZ.obj.tcb` covers every spec TCB by `Z.T`,
  `JAtZ.tcbs_eq` puts `Z.T` in the heap, `TcbRel.st` / `YieldRel.tcb` read state and yield off the words);
* **`ybw_of_yb`**: `SlJAtYB Kl σ → YBW Kl σ` (`JAtZ.tcbs_eq`, P3's `JAtZ.yield0_blk`).
So `YBW` is implied by `yb` and gives it back at every chain state: the same content, stated on FL4's words.
**`ybw_of_bun`**: `ybw` holds at every bundle state whose spec state has YieldBlock (satisfiability).

Checked against FL4 (`crates/fl4-core/src`) on reachable states, including other cores' steps:
* `YIELD_TO := nonzero` only in `schedcontext.rs` `yield_switches` (l.180, `ct.set_yield_to(s, sc.0)`), on the current
  thread, which `decode`'s `SchedContextYieldTo` arm has just set `TS_RESTART` (l.274) and which it enqueues (l.183);
  it is cleared by `cancel_yield_to` (l.131–136: `complete_yield_to` l.139, `suspend` `sched.rs` l.767) and by
  `activate_thread` before the thread runs again (`sched.rs` l.689–690).
* The writers of a blocked state are `send_ipc` (`endpoint.rs` l.80), `wait_for_sender` (`endpoint.rs` l.156),
  `receive_signal` (`notification.rs` l.166), `set_blocked_on_reply` (`sched.rs` l.156, from `reply_push`, `ipc.rs`
  l.171) and the fastpaths (`fastpath.rs` l.133 / l.247, `fastpath_vm.rs` l.77 / l.155); `set_thread_state`
  (`sched.rs` l.149) is called only with non-blocked constants. Each blocks the entry's current thread (yield 0:
  cleared by `activate_thread` at the previous exit; in the YieldTo entry itself the yielder is left `RESTART` /
  enqueued and nothing after `yield_to` blocks it), or a thread already read blocked (`reply_push`'s queued sender,
  `endpoint.rs` l.181; `do_reply_transfer`'s receiver, read `BLOCKED_ON_REPLY` at `ipc.rs` l.267 and sent a
  timeout fault at l.290), whose yield is 0 by the invariant. The timeout faults of `end_timeslice` (`sched.rs`
  l.494) hit the current thread at a budget check: at entry (`syscall.rs` l.269), at a preemption point, or on a
  stalled core (`smp.rs` l.80, its current thread, activated at its last exit). `yield_switches` yields only to an
  SC of the current core (`schedcontext.rs` l.175), and only the current core's current thread gets a yield, so no
  core sets the yield of, or blocks, another core's thread with a nonzero yield; `suspend` clears the yield before
  `INACTIVE` (`sched.rs` l.767–768). Intermediate states of a transaction: the YieldTo entry writes `RESTART`
  (l.274) before `YIELD_TO` (l.180), the blocking writers write a thread whose yield is already 0.
* The view (P2/CoreView `tcbRepl`) keeps `YIELD_TO` (offset 3472) and the blocked codes 3–6 of `STATE` (3328),
  rewriting only `Hidden` codes 1, 2, 7, 8 to 0: it creates no violation.
P3 proves the spec form at boot and across every kernel entry (`boot_yieldBlock'`, `kernel_entry_yieldScope2U29`,
`ybOut_keep`). So `YBW` is a kernel invariant of the execution's memory, true on reachable states: **[J]**, not a
platform fact. Discharging it needs a memory invariant carried along `ExecWPRV12` (each local path's writes, the
serial exit tied to its P3 exit), which no existing premise provides.

## V13
* `VmFEntV13` / `VmREntV13` / `SlEntV13`: `VmFEntJ14` / `VmREntU` / `SlEntU` with `yb` → `ybw : YBW`; `.toJ14` /
  `.toU` (given the chain's bundle) and `.ofJ14` / `.ofU` back.
* `StartU2V13` / **`StartV13`** [P]: `StartV2C` with those three entry records (every other clause literally
  `StartU2C`'s / `StartInvU3`'s). **`startV2C_of_V13`** (at a chain of the layout), **`startV13_of_V2C`**.
* **`execWPRV12_conv`**: an `ExecWPRV12` with start fact `SF` is one with `SF'` when `SF → SF'` at every layout whose
  chain is a serial exit's (carried along the execution from `hB` / `serX` / `keep`).
* **`serializable_fl4_localV13`** (`ExecWPRV12 … StartV13`), **`serializable_fl4_localV12ofV13`** (V12's statement
  follows from V13: V13's start fact is implied by V12's).

## Premises of `serializable_fl4_localV13` vs `serializable_fl4_localV12`
* **Narrowed: `yb` [J] → `ybw` [J]** in the vmF / vmR / sl entry records (from "a bundle whose spec state has
  YieldBlock" to "the layout's TCBs' `YIELD_TO` / `STATE` words": `ybw_of_yb`; equivalent at chain states).
* Everything else unchanged: `ExecWPRV12`'s `arm` [P], `start` [P] (gen 29's narrowing), `serX` [P], `serC`,
  `serG` [P], `keep`; `StartV13`'s other clauses (`LkC`, `DelPtePrem.lk` / `InvPremW.lk` [P], the slot records);
  `P` [P], `hIoa` [P], `h0`, `hA0`, `hB` [P], `hc0`, `hM0`, `hq`.
* The only [J] left is `ybw` (a kernel invariant, not a platform fact; satisfiable: `ybw_of_bun`). The top's
  premises are therefore not [P]-only: see handoff §35 for why `ybw` cannot be discharged from the existing
  premises (chain states are not anchored at boot; `ExecWPRV12` carries no memory invariant across serial steps).

No existing statement changed except the root import list.
-/
import Fl4Proofs.P2.E2EPV11
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath tr masksOf)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg NextH VEq Safe narrowSP)

noncomputable section
open Classical

/-! ## The word-level YieldBlock -/

section ybw
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]

/-- **[J] word-level YieldBlock** (module docstring): every TCB of `Kl`'s typed heap whose `YIELD_TO` word is nonzero
has a `STATE` word that codes no blocked state (3 receive, 4 send, 5 reply, 6 notification). A kernel invariant of
FL4's memory (checked against `schedcontext.rs` / `sched.rs` / `endpoint.rs` / `notification.rs` / `ipc.rs` /
`fastpath*.rs`, module docstring), kept by the view. -/
def YBW (Kl : OwnMap.KLayout) (s : S) : Prop :=
  ∀ t ∈ P1.Heap.tcbs Kl.heap, L.mem s (Fl4Proofs.P1.yieldA t) ≠ 0#u64 →
    ¬ ((L.mem s (Fl4Proofs.P3.Notif.tStA t)).val = 3 ∨ (L.mem s (Fl4Proofs.P3.Notif.tStA t)).val = 4 ∨
      (L.mem s (Fl4Proofs.P3.Notif.tStA t)).val = 5 ∨ (L.mem s (Fl4Proofs.P3.Notif.tStA t)).val = 6)

variable {st}

/-- **`yb` gives `ybw`** (`JAtZ.tcbs_eq`, `JAtZ.yield0_blk`). -/
theorem ybw_of_yb {Kl : OwnMap.KLayout} {s : S} (h : SlJAtYB st Kl s) : YBW st Kl s := by
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B, hY⟩ := h
  intro t ht h0 hb
  have htT : t ∈ Zx.T := by rw [B.j.tcbs_eq.1]; exact ht
  exact h0 (Fl4Proofs.P3.SInvR.G5.JAtZ.yield0_blk B.j hY htT hb)

/-- **`ybw` gives `yb` at a state with a bundle of the layout** (every spec TCB is a `Z.T` TCB of the heap; its
yield and state are read off the words). -/
theorem yb_of_ybw {Kl : OwnMap.KLayout} {s : S} (hJ : SlJAt (L := L) Kl s) (h : YBW st Kl s) : SlJAtYB st Kl s := by
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := hJ
  refine ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B, ?_⟩
  intro p x hk hy
  obtain ⟨t, ht, rfl⟩ := B.j.obj.tcb p x hk
  obtain ⟨x1, hk1, hr⟩ := B.j.xtop.ipc.tcb t ht
  obtain ⟨x2, hk2, hyr⟩ := B.j.yld.tcb t ht
  rw [hk] at hk1 hk2
  cases hk1
  cases hk2
  have htH : t ∈ P1.Heap.tcbs Kl.heap := by rw [← B.j.tcbs_eq.1]; exact ht
  have h0 : L.mem s (Fl4Proofs.P1.yieldA t) ≠ 0#u64 := by
    intro e
    apply hy
    rw [hyr, e]
    unfold Fl4Proofs.P3.Notif.optRef
    simp
  have hb := h t htH h0
  rw [hr.st] at hb
  revert hb
  generalize x.tcbState = ts
  cases ts <;> simp [Fl4Proofs.P3.Notif.tsCode, Fl4Proofs.P3.SInv.notBlkSt]

/-- **`ybw` is satisfiable at every bundle state whose spec state has YieldBlock** (`slJAtYB_of`, then `ybw_of_yb`):
at boot (`boot_yieldBlock'`) and after every kernel entry from such a state (`ybOut_keep`), so the [J] is not
vacuous. -/
theorem ybw_of_bun {Kl : OwnMap.KLayout} {s : S} {A' : Type} {arI : machine.Arch A'} {AR : A' → Fl4Spec.Cr3 → Prop}
    {Zx : Fl4Proofs.P3.XSets} {Cx Ax : Set U64} {Lst : U64 → List U64} {D : Set U64} {a' : A'}
    {σ : Fl4Spec.State Unit} (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D Kl s a' σ)
    (hY : Fl4Proofs.P3.SInv.YieldBlockS σ) : YBW st Kl s :=
  ybw_of_yb (slJAtYB_of st B hY)

end ybw

/-! ## The entry records with `ybw` -/

section ent
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)

/-- **vmF's start entry facts**: `VmFEntJ14` with `yb` [J] narrowed to `ybw` [J]. -/
structure VmFEntV13 {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop)
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
  /-- [J] word-level YieldBlock at the start state (`YBW`, module docstring). -/
  ybw : YBW st K.toKLayout s
  /-- [P] -/
  gl : VmGlue st ar i.Locks s

/-- **vmR's start entry facts**: `VmREntU` with `yb` [J] narrowed to `ybw` [J]. -/
structure VmREntV13 {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop)
    (MR : A3 → Fl4Spec.MachineState → Prop) (i : VmRArg S) (Kl Kb : OwnMap.KLayout) (s : S) : Prop where
  /-- Index convention, as `VmREntJ12.ix`. -/
  ix : BunIxU (L := L) Kl Kl.heap.tcbs i.Cs i.Ω Kl.heap i.Sg Kl.heap.replies Kl.heap.scs Kl.heap.ntfns
    Kl.heap.scBits i.Ac s
  /-- [P] (`NonIdle`). -/
  hct : NonIdle st arI AR MR s
  /-- [J] word-level YieldBlock at the start state (`YBW`, module docstring). -/
  ybw : YBW st Kb s
  /-- [P] -/
  lk : i.Locks s i.rptr ∧ i.Locks s i.ep
  /-- [P] fl4-sync's no-neighbour check (`VmNbC`), as `VmREntJ12.nbc`. -/
  nbc : VmNbC st i.rptr s
  /-- fl4-sync's `found` (`VmFoundC`), as `VmREntJ12.fd`. -/
  fd : VmFoundC st i.rptr i.ep s

/-- **sl's start entry facts**: `SlEntU` with `yb` [J] narrowed to `ybw` [J]. -/
structure SlEntV13 {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop)
    (MR : A3 → Fl4Spec.MachineState → Prop) (i : SlArg S) (K : OwnMap.KLayout) (s : S) : Prop where
  /-- Index convention, as `SlEntJ12.ix`. -/
  ix : ∃ (A' : Type) (arI' : machine.Arch A') (AR' : A' → Fl4Spec.Cr3 → Prop) (Zx : Fl4Proofs.P3.XSets)
    (Lst : U64 → List U64) (D : Set U64) (a' : A') (σ : Fl4Spec.State Unit),
    SlJAtZ (L := L) arI' AR' Zx i.Cs i.Ac Lst D K s a' σ ∧ i.Ω = OmegaS K Zx (L.ksb s) σ
  /-- Index convention: `Sg = SgS`. -/
  sg : i.Sg = SgS K
  /-- [P] (`NonIdle`). -/
  hct : NonIdle st arI AR MR s
  /-- [P] (`SlEntL`). -/
  el : SlEntL (st := st) K i.Locks i.found s
  /-- [P] (`SlSyncC`). -/
  sc : SlSyncC st i.n i.found s
  /-- [P] fl4-sync's no-neighbour check (`SlNbC`). -/
  nbc : SlNbC st i.n i.found s
  /-- [P] (`SlAccR`). -/
  acc : SlAccR (st := st) ar K i.Locks i.found s
  /-- [P] the endpoint is locked (`SlPreR2.hlk`). -/
  hlk : ¬ SlTrap st s → i.Locks s i.found.2
  /-- [J] word-level YieldBlock at the start state (`YBW`, module docstring). -/
  ybw : YBW st K s

variable {st ar}

theorem VmFEntV13.toJ14 {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop}
    {MR : A3 → Fl4Spec.MachineState → Prop} {i : VmFArg S} {K : KLayoutV} {s : S}
    (E : VmFEntV13 st ar arI AR MR i K s) (hJ : SlJAt (L := L) K.toKLayout s) : VmFEntJ14 st ar arI AR MR i K s :=
  ⟨E.nv, E.ix, E.hct, E.lk, yb_of_ybw hJ E.ybw, E.gl⟩

theorem VmREntV13.toU {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop}
    {MR : A3 → Fl4Spec.MachineState → Prop} {i : VmRArg S} {Kl Kb : OwnMap.KLayout} {s : S}
    (E : VmREntV13 st arI AR MR i Kl Kb s) (hJ : SlJAt (L := L) Kb s) : VmREntU st arI AR MR i Kl Kb s :=
  ⟨E.ix, E.hct, yb_of_ybw hJ E.ybw, E.lk, E.nbc, E.fd⟩

theorem SlEntV13.toU {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop}
    {MR : A3 → Fl4Spec.MachineState → Prop} {i : SlArg S} {K : OwnMap.KLayout} {s : S}
    (E : SlEntV13 st ar arI AR MR i K s) (hJ : SlJAt (L := L) K s) : SlEntU st ar arI AR MR i K s :=
  ⟨E.ix, E.sg, E.hct, E.el, E.sc, E.nbc, E.acc, E.hlk, yb_of_ybw hJ E.ybw⟩

end ent

/-! ## The start facts with `ybw` -/

section start
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st] {A : Type}
  (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop) (MR : A3 → Fl4Spec.MachineState → Prop)

/-- **The start facts of the W11 slots with `ybw`** [P] (module docstring): `StartU2C` with vmF's, vmR's and sl's
entry records at `VmFEntV13` / `VmREntV13` / `SlEntV13` (each clause otherwise `StartU2C`'s, unfolded through
`StartU2B` / `StartU2` / `StartU`); every other index is `StartU2C`'s. -/
def StartU2V13 (Ch : S → Prop) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (q : SP) : Fl4IxW (S := S) → Prop
  | .vmF j => LkC j.Locks ∧ ((∀ s, KernDetS (L := L) (userV K.toKLayoutV).user j.Locks s) →
      ∃ q0, (∃ _h : VmFPremB st j K.toKLayoutV, ∃ σ : S,
        (Ch σ ∧ VmFEntV13 st ar arI AR MR j K.toKLayoutV σ) ∧
        ∀ h' : VmFPremA st ar j K.toKLayoutV,
          GlueAt ((vmFSlotA st ar hA (masksWr_plain st)).liftAt j K.toKLayoutV m hK.base hU.base h')
            (fun σ' : S => σ' = σ) c hs m q0) ∧
        q = cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) c q0 ∅)
  | .vmR j => ∃ q0, (LkC j.Locks ∧ ∃ σ : S, (Ch σ ∧ VmREntV13 st arI AR MR j (userV K.toKLayoutV) K.toKLayout σ) ∧
      ∀ h : VmRPremA st j K.toKLayoutV,
        GlueAt ((vmRSlotA st ar hA (masksWr_plain st)).liftAt j K.toKLayoutV m hK.base hU.base h)
          (fun σ' : S => σ' = σ) c hs m q0) ∧
      q = cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) c q0 ∅
  | .sl j => ∃ q0, (LkC j.Locks ∧ ∃ σ : S, (Ch σ ∧ SlEntV13 st ar arI AR MR j K.toKLayoutV.toKLayout σ) ∧
      ∀ h : (slSlotB st ar hA (masksWr_plain st) L.total a0).Prem j K.toKLayoutV m,
        GlueAt ((slSlotB st ar hA (masksWr_plain st) L.total a0).liftAt j K.toKLayoutV m hK.base hU.base h)
          (fun σ' : S => σ' = σ) c hs m q0) ∧
      q = cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) c q0 ∅
  | i => StartU2C st ar hA a0 arI AR MR Ch K m hK hU c hs q i

/-- **V13's start facts** [P]: `StartV2C` with `StartU2V13` on the W11 slots. -/
def StartV13 (Ch : S → Prop) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (q : SP) : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S) → Prop
  | .inl i => StartU2V13 st ar hA a0 arI AR MR Ch K m hK hU c hs q i
  | .inr j => StartInvU3 st ar hA Ch K m hK hU c hs q j

variable {arI AR MR}

/-- **`StartV13` gives `StartV2C`** at a layout whose chain is `Ch` (`yb` from `ybw` and the chain's bundle). -/
theorem startV2C_of_V13 {Ch : S → Prop} {K : KLayoutP} (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch)
    {m : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {hs : U64 → Prop} {q : SP}
    {i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)}
    (h : StartV13 st ar hA a0 arI AR MR Ch K m hK hU c hs q i) :
    StartV2C st ar hA a0 arI AR MR Ch K m hK hU c hs q i := by
  obtain ⟨σe, hC'⟩ := hC
  rcases i with i | j
  · cases i with
    | vmF j =>
      obtain ⟨hL, hG⟩ := h
      refine ⟨hL, fun hk => ?_⟩
      obtain ⟨q0, ⟨h1, σ, ⟨hCσ, hE⟩, hG'⟩, e⟩ := hG hk
      exact ⟨q0, ⟨h1, σ, ⟨hCσ, hE.toJ14 (ChainOf.bun hC' σ hCσ)⟩, hG'⟩, e⟩
    | vmR j =>
      obtain ⟨q0, ⟨hL, σ, ⟨hCσ, hE⟩, hG⟩, e⟩ := h
      exact ⟨q0, ⟨hL, σ, ⟨hCσ, hE.toU (ChainOf.bun hC' σ hCσ)⟩, hG⟩, e⟩
    | sl j =>
      obtain ⟨q0, ⟨hL, σ, ⟨hCσ, hE⟩, hG⟩, e⟩ := h
      exact ⟨q0, ⟨hL, σ, ⟨hCσ, hE.toU (ChainOf.bun hC' σ hCσ)⟩, hG⟩, e⟩
    | io j => exact h
    | st j => exact h
    | irq j => exact h
    | vq j => exact h
  · exact h

end start

/-! ## Changing the start fact along an execution -/

section exec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {ι : Type}

end exec

/-! ## V13 -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

end top

end
end Fl4Proofs.P2.E2EP
