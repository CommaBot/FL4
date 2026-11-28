/-
# P2 (line p3mc, gen 32): route (C) — anchored start states, other cores' writes as a proved rely, V14

V13 (P2/E2EPV13) asks **`ybw` [J]** in its vmF / vmR / sl entry records: the glue's start state `σ` of core `c` has
`YBW` (every heap TCB with `YIELD_TO ≠ 0` has a non-blocked `STATE`). Gen 31 (handoff §36b) showed that tying `σ` to
`c`'s previous YieldBlock exit through `c`'s own runs alone is false on SMP (another core's ReplyRecv blocks its own
thread on a shared endpoint, which `c`'s view shows), and proposed route (C): the anchor plus a rely for other cores'
writes. This module builds it.

## The anchored states (`YbAnch`)
`YbAnch arI AR MR H c σ` (heap `H` = the layout's heap): `σ` is reached, as a store state seen by core `c`, by
* **`exit`**: a P3 YieldBlock exit (`JReachYB`, with a bundle at `H`): boot (`boot_yieldBlock'`), every kernel exit
  from one (`kernel_entry_yieldScope2U29`), the chain exit `SerExitWYB` chooses (`ybAnch_of_chainYB`,
  `ybAnch_of_serExitWYB`);
* **`run`**: a P3-covered local run of `c` (`YbRun`: from a `JReachU17` state with a bundle at `H` to a state with a
  bundle at `H`, with a `YBOut` spec outcome; every `JReachSt` chain step of `loc_chain_all` clauses 2–6, 8–10 is one,
  `ybRun_of_jreachSt`);
* **`env`**: **another core's run merged into `c`'s view** (`YbMerge`): core `d ≠ c` runs `δ → δ'` (`YbRun`, from a
  state anchored for `d`), writing a word set `W`; on the `YIELD_TO` / `STATE` words of `H`'s TCBs, `c`'s new state
  `σ'` is `σ` off `W` and `δ'` on `W` (for `STATE`: up to the view's rewriting of non-blocked codes, i.e. the same
  blockedness), `σ` and `δ` agree (yield word, blockedness) on every TCB `d` touches, and `c`'s current thread's
  yield word is unchanged;
* **`frame`**: any change that keeps every `YIELD_TO` / `STATE` word of `H` and `c`'s current thread's yield word
  (hardware user-word writes, declines' `FAULT_IP` / timestamp writes, changes of any other word).

## The rely, proved
**`YbRely`** ("other cores' writes keep YieldBlock in `c`'s view", the rely of handoff §3 R1 restricted to YieldBlock):
a merge of another core's run from a `YBW ∧ CYW` state into a `YBW ∧ CYW` state of `c` is `YBW ∧ CYW`.
**`ybRely`: proved** (`numDomains = 1` only), from `ybw_yBOut` (P2/YbwKeep: the other core's run is itself a
P3-covered run, so `YBW` holds at its exit `δ'`; `kernel_entry_ybwU29` is the same fact for the extracted handlers)
and `ybMerge_keep` (a word case split: a TCB whose yield is written takes it from `δ'`, whose `YBW` gives a
non-blocked state, read off `δ'` if its state is written and off `σ` = `δ` blockedness otherwise; a TCB whose state
only is written has `σ`'s yield = `δ`'s = `δ'`'s). **`YbAnch.ybw`**: every anchored state has `YBW ∧ CYW` (no
premise but `numDomains = 1`).

## V14
* `VmFEntV14` / `VmREntV14` / `SlEntV14`: V13's records without `ybw`; `StartU2V14` / **`StartV14`**: V13's start
  facts with each of the three records' start state `σ` asked `Ch σ ∧ YbAnch … K.heap c σ ∧ Ent14 σ`.
* **`startV13_of_V14`** (`YbAnch.ybw`), **`serializable_fl4_localV14`** (via V13 and `execWPRV12_conv`).

## Premise diff V14 vs V13
* **Removed: `ybw` [J]** (vmF / vmR / sl entry records).
* **Added: `anch` [J]** (same three records): the start state is a `YbAnch` state of core `c` at the layout's heap.
  Of its constructors, `run` and `env`'s `YbRun` are P3 facts (proved for chain steps, `ybRun_of_jreachSt`), `exit`
  is P3's `JReachYB` (what `SerExitWYB` [P] asks of the serial exit's ghost choice), `frame` is a word-frame
  condition. What is **not proved** is that the execution's history, seen from `c`'s view, *has* this shape:
  (i) the glue's start state descends from a `JReachYB` exit (the serial exit `serX` [P] picks only *some*
  `JReachU17` exit; boot `hB` likewise), (ii) each other core's committed local run, seen in `c`'s view, is a
  `YbMerge` of a P3-covered run — FL4's lock discipline (a local run of `d` writes only `d`-owned or `d`-locked words,
  P2/CoreView `write_own`; nobody else writes them between `d`'s start and commit) plus the view keeping `YIELD_TO`
  and the blocked codes (`CoreView.tcbRepl`) — and (iii) `c`'s own runs are P3-covered from the chain. (ii) is the
  YieldBlock instance of the SMP rely of handoff §3 R1, not proved anywhere in the tree; it is a statement about the
  concurrent execution, hence [J].
* **`anch` is not implied by `ybw`** (it is a fact about the history, `ybw` one about the state); it implies `ybw`
  (`YbAnch.ybw`). So V14 is not a weakening of V13's hypotheses: it trades the state invariant `ybw` for the
  structural `anch`, whose YieldBlock content (the rely and every kernel step) is now proved, leaving only the
  shape of the concurrent history as the [J].
* **The rely (`YbRely`) is not a premise**: it is proved (`ybRely`), so it is implied by anything.
* Everything else unchanged (`ExecWPRV12`'s `arm` / `start` / `serX` / `serG` [P], `serC`, `keep`; the records'
  other fields; `P`, `hIoa`, `h0`, `hA0`, `hB`, `hc0`, `hM0`, `hq`).

Checked on reachable states (handoff §37): gen 31's counterexample to route (B) (core `d`'s ReplyRecv blocking its
current thread `t` on an endpoint shared with `c`) is an `env` step: `W` = `t`'s state and the endpoint's words,
`t`'s yield is 0 (`d`'s current thread, `CYW` at `δ`), `σ`'s and `δ`'s yield word of `t` agree (written only by `d`),
both show `t` non-blocked before (running: view code 0 in `c`'s view, 1 in `d`'s) and blocked (code 3, kept by the
view) after. No counterexample to `anch` found.

No existing statement changed except the root import list.
-/
import Fl4Proofs.P2.YbwKeep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath tr masksOf)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg NextH VEq Safe narrowSP)
open Fl4Proofs.P3.SInvR.G5 (YBWH CYW)

noncomputable section
open Classical

/-! ## Anchored states and the rely -/

section anch
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop) (MR : A3 → Fl4Spec.MachineState → Prop)

/-- A blocked `STATE` code (3 receive, 4 send, 5 reply, 6 notification; `sched.rs` l.17–20). -/
def YbBlk (v : U64) : Prop := v.val = 3 ∨ v.val = 4 ∨ v.val = 5 ∨ v.val = 6

/-- A joint bundle (`JAtZ`) at the heap `H`. -/
def YbBun (H : Heap) (s : S) (a : A3) (τ : Fl4Spec.State Unit) : Prop :=
  ∃ (Z : Fl4Proofs.P3.XSets) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    Fl4Proofs.P3.JAtZ (L := L) arI AR Z H Cs Ac Lst D s a τ

/-- **A P3-covered run** (module docstring): from a reachable state with a bundle at `H` to a state with a bundle at
`H`, the spec outcome of `YBOut` shape (`loc_chain_all` clauses 2–6, 8–10). -/
def YbRun (H : Heap) (s s' : S) : Prop :=
  ∃ (a : A3) (τ : Fl4Spec.State Unit), Fl4Proofs.P3.SInvR.G5.JReachU17 (L := L) arI AR MR s a τ ∧
    YbBun (L := L) arI AR H s a τ ∧ ∃ (a' : A3) (τ' : Fl4Spec.State Unit), YBOut τ τ' ∧ YbBun (L := L) arI AR H s' a' τ'

variable {arI AR MR}

/-- **Another core's run `δ → δ'` merged into `c`'s state `σ`, giving `σ'`** (module docstring, `env`): `W` is the run's
write set on the `YIELD_TO` / `STATE` words of `H`'s TCBs. -/
def YbMerge (H : Heap) (σ δ δ' σ' : S) : Prop :=
  ∃ W : U64 → Prop,
    (∀ t ∈ Heap.tcbs H,
      (¬ W (Fl4Proofs.P1.yieldA t) → L.mem σ' (Fl4Proofs.P1.yieldA t) = L.mem σ (Fl4Proofs.P1.yieldA t) ∧
        L.mem δ' (Fl4Proofs.P1.yieldA t) = L.mem δ (Fl4Proofs.P1.yieldA t)) ∧
      (W (Fl4Proofs.P1.yieldA t) → L.mem σ' (Fl4Proofs.P1.yieldA t) = L.mem δ' (Fl4Proofs.P1.yieldA t)) ∧
      (¬ W (Fl4Proofs.P3.Notif.tStA t) →
        L.mem σ' (Fl4Proofs.P3.Notif.tStA t) = L.mem σ (Fl4Proofs.P3.Notif.tStA t) ∧
        L.mem δ' (Fl4Proofs.P3.Notif.tStA t) = L.mem δ (Fl4Proofs.P3.Notif.tStA t)) ∧
      (W (Fl4Proofs.P3.Notif.tStA t) →
        (YbBlk (L.mem σ' (Fl4Proofs.P3.Notif.tStA t)) ↔ YbBlk (L.mem δ' (Fl4Proofs.P3.Notif.tStA t)))) ∧
      (W (Fl4Proofs.P1.yieldA t) ∨ W (Fl4Proofs.P3.Notif.tStA t) →
        L.mem σ (Fl4Proofs.P1.yieldA t) = L.mem δ (Fl4Proofs.P1.yieldA t) ∧
        (YbBlk (L.mem σ (Fl4Proofs.P3.Notif.tStA t)) ↔ YbBlk (L.mem δ (Fl4Proofs.P3.Notif.tStA t))))) ∧
    L.mem σ' (Fl4Proofs.P1.yieldA (L.curW σ')) = L.mem σ (Fl4Proofs.P1.yieldA (L.curW σ))

/-- **A change keeping every `YIELD_TO` / `STATE` word of `H` and the current thread's yield word** (`frame`). -/
def YbFrame (H : Heap) (σ σ' : S) : Prop :=
  (∀ t ∈ Heap.tcbs H, L.mem σ' (Fl4Proofs.P1.yieldA t) = L.mem σ (Fl4Proofs.P1.yieldA t) ∧
    L.mem σ' (Fl4Proofs.P3.Notif.tStA t) = L.mem σ (Fl4Proofs.P3.Notif.tStA t)) ∧
  L.mem σ' (Fl4Proofs.P1.yieldA (L.curW σ')) = L.mem σ (Fl4Proofs.P1.yieldA (L.curW σ))

variable (arI AR MR)

/-- **The anchored states of core `c`** (module docstring): a P3 YieldBlock exit, then `c`'s own P3-covered runs,
other cores' P3-covered runs merged into `c`'s view, and changes off the yield / state words. -/
inductive YbAnch (H : Heap) : U64 → S → Prop
  | exit {c : U64} {σ : S} {a : A3} {τ : Fl4Spec.State Unit} :
      Fl4Proofs.P3.SInvR.G5.JReachYB (L := L) arI AR MR σ a τ → YbBun (L := L) arI AR H σ a τ → YbAnch H c σ
  | run {c : U64} {σ σ' : S} : YbAnch H c σ → YbRun (L := L) arI AR MR H σ σ' → YbAnch H c σ'
  | env {c d : U64} {σ δ δ' σ' : S} : YbAnch H c σ → YbAnch H d δ → d ≠ c → YbRun (L := L) arI AR MR H δ δ' →
      YbMerge (L := L) H σ δ δ' σ' → YbAnch H c σ'
  | frame {c : U64} {σ σ' : S} : YbAnch H c σ → YbFrame (L := L) H σ σ' → YbAnch H c σ'

variable {arI AR MR}

/-- **Every step of a `loc_chain_all` chain with a `YBOut` outcome is a P3-covered run** (`JReachSt.atSt'`). -/
theorem ybRun_of_jreachSt {Z : Fl4Proofs.P3.XSets} {H : Heap} {Cx : Set U64} {k : U64} {δ δ' : S} {a : A3}
    {τ : Fl4Spec.State Unit}
    (hR : JReachSt (L := L) arI AR MR (LocAllSt (L := L) arI AR Z.th Z.B H Cx) Z.th Z.B H Cx k δ a τ)
    {a' : A3} {τ' : Fl4Spec.State Unit} (hO : YBOut τ τ')
    (hR' : JReachSt (L := L) arI AR MR (LocAllSt (L := L) arI AR Z.th Z.B H Cx) Z.th Z.B H Cx k δ' a' τ') :
    YbRun (L := L) arI AR MR H δ δ' := by
  obtain ⟨Z1, Ac1, Lst1, D1, -, -, -, J1, -⟩ := hR.atSt' (locKeepSt_st _ _ _ _ _)
  obtain ⟨Z2, Ac2, Lst2, D2, -, -, -, J2, -⟩ := hR'.atSt' (locKeepSt_st _ _ _ _ _)
  exact ⟨a, τ, hR.reach, ⟨Z1, Cx, Ac1, Lst1, D1, J1⟩, a', τ', hO, ⟨Z2, Cx, Ac2, Lst2, D2, J2⟩⟩

/-- **A YieldBlock state of a chain is an anchor** for every core, at the chain's heap. -/
theorem ybAnch_of_chainYB {Kl : OwnMap.KLayout} {Ch : S → Prop} {σ : S}
    (h : ChainYB (L := L) arI AR MR Kl Ch σ) (c : U64) : YbAnch (L := L) arI AR MR Kl.heap c σ := by
  obtain ⟨k, Z, H, Cx, nc, rfl, -, -, a, τ, hR, hY, hC⟩ := h
  obtain ⟨Z1, Ac1, Lst1, D1, -, -, -, J1, -⟩ := hR.atSt' (locKeepSt_st _ _ _ _ _)
  exact .exit ⟨hR.reach, hY, hC⟩ ⟨Z1, Cx, Ac1, Lst1, D1, J1⟩

/-- **The exit `SerExitWYB` chooses is an anchor of its chain** (satisfiability of `anch` at the serial exit). -/
theorem ybAnch_of_serExitWYB [Fl4Proofs.P1.PlainStore st] {P : LocPlat st arI AR MR} {K : KLayoutV}
    {Ch : S → Prop} (h : SerExitWYB P K Ch) (c : U64) :
    ∃ σe, Ch σe ∧ YbAnch (L := L) arI AR MR K.toKLayout.heap c σe := by
  obtain ⟨σe, hY⟩ := h.base
  exact ⟨σe, hY.ch, ybAnch_of_chainYB hY c⟩

end anch

/-! ## The entry records without `ybw` -/

section ent
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)

/-- **vmF's start entry facts**: `VmFEntV13` without `ybw`. -/
structure VmFEntV14 {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop)
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
  /-- [P] -/
  gl : VmGlue st ar i.Locks s

/-- **vmR's start entry facts**: `VmREntV13` without `ybw`. -/
structure VmREntV14 {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop)
    (MR : A3 → Fl4Spec.MachineState → Prop) (i : VmRArg S) (Kl : OwnMap.KLayout) (s : S) : Prop where
  /-- Index convention, as `VmREntJ12.ix`. -/
  ix : BunIxU (L := L) Kl Kl.heap.tcbs i.Cs i.Ω Kl.heap i.Sg Kl.heap.replies Kl.heap.scs Kl.heap.ntfns
    Kl.heap.scBits i.Ac s
  /-- [P] (`NonIdle`). -/
  hct : NonIdle st arI AR MR s
  /-- [P] -/
  lk : i.Locks s i.rptr ∧ i.Locks s i.ep
  /-- [P] fl4-sync's no-neighbour check (`VmNbC`), as `VmREntJ12.nbc`. -/
  nbc : VmNbC st i.rptr s
  /-- fl4-sync's `found` (`VmFoundC`), as `VmREntJ12.fd`. -/
  fd : VmFoundC st i.rptr i.ep s

/-- **sl's start entry facts**: `SlEntV13` without `ybw`. -/
structure SlEntV14 {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop)
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

variable {st ar}

end ent

/-! ## The start facts with the anchor -/

section start
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st] {A : Type}
  (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop) (MR : A3 → Fl4Spec.MachineState → Prop)

variable {arI AR MR}

end start

/-! ## V14 -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

end top

end
end Fl4Proofs.P2.E2EP
