/-
P2 (iolay gen 6): **E2EVFl4W14 — W12's premises exactly ([P]s, `SerExitW`, `ExecW`, `Ch σ` starts), with the four
`YIELD_TO` [J]s `ys` (vmF), `ry` (vmR), `hy0f` / `hy0r` (sl, fields of `SlPreB`) replaced by one [J] `yb`** (new
definitions only, on top of W13; no existing statement changes).

1. **`yb` [J]** (`SlJAtYB` at the start state: a clause-7 bundle whose spec state carries P3's `YieldBlockS`). It is
   the single fact behind all four: vmF's `ys` is its `YieldBlockS.scope` (`SlJAtYB.toY`), vmR's `ry` is
   `SlJAtZ.ryB`, sl's `hy0f` / `hy0r` are `SlPreBY.toBY` (W13). `VmFEntJ14` = `VmFEntJ12` with `ys` → `yb`;
   `VmREntJ14` = `VmREntJ11` with `ry` → `yb`; `SlQYB` = W6's `SlQ` with `SlPreB.hy0f` / `hy0r` → `yb`.
2. **No `SerExitWYB` / `ExecWYB` / `ChainYB`**: W13's change to the serial exit was not used by its starts (they only
   read `ChainYB.ch` and `ChainYB.bun`), so W14 keeps W12's `SerExitW` / `ExecW` / `execV_of_WC` and `Ch σ`.
   `StartP3W14`, `startAt_P3W14`, **`serializable_fl4_localW14`** (premises: W12's, with `StartP3W14` for
   `StartP3W12`).

| slot | W12 [J] | W14 [J] |
|---|---|---|
| vmF | `ys` (`SlJAtY`, YieldScope of the start bundle) | `yb` (`SlJAtYB`, YieldBlock of the start bundle) |
| vmR | `ry` (receiver's `YIELD_TO = 0`) | `yb` |
| sl | `SlPreB.hy0f` / `hy0r` (handler's / receiver's `YIELD_TO = 0`) | `yb` (`SlPreBY` keeps `SlPreB`'s other [J] fields) |

**Why `yb` is not derived from W12's premises** (the gen-6 goal; checked against the definitions):

* (a) `SerExitW P K Ch := ∃ σe a3 τ (hJ : JReachU17 σe a3 τ), chainC P hJ = (K.toKLayout, Ch)`. `JReachU17` is
  `JReachU3 ∧ GpmOutV ∧ IdleVtS ∧ DevRangeS`, and `JReachU3.start` admits any state with
  `JAtZ ∧ VxE ∧ SInvX ∧ SInvIP ∧ MR ∧ UtPgR`. None of these relates `tcbYieldTo` to the thread state:
  `YieldBlockS` / `YieldScopeS` are defined only in P3/SpecInvYield*; `SInvX = SInvW ∧ RPos`; `YieldRel` only ties
  the `YIELD_TO` word to `tcbYieldTo` and the SC's `scYieldFrom` (gen 3 checked SInvX / SInvA / SchedValid /
  ValidIdle / UtDropSpec / ScYield / P1). So `σe` need not be a `JReachYB` state, and `SerExitWYB` does not follow.
* (b) There is no chain in the hypotheses along which to carry YieldBlock: `ExecW`'s serial step is
  `Serial.Step.serial` (`Run p s.mem m'` for an arbitrary body `p`, new ghosts arbitrary) and `Fl4StepW.serX` gives a
  fresh `SerExitW` for the new layout, whose `σe` is unrelated to the previous exit's and to `s'.mem`. The execution's
  memory is not a P3 store state; P3 states enter only through `SerExitW`'s witness and `GlueAt`'s `σ`.
* (c) `Ch σ` does not pin `σ` to the exit's local runs: `ChainOf` fixes `Ch = {σ | ∃ a τ, JReachSt … (L.ksb σe) σ a τ}`
  and `JReachSt.exit` admits **every** `JReachU17` state with `JAtSt` at the ghosts, not only `σe`. `GlueAt` constrains
  its `σ` only by `Ent σ` and agreement with the model memory off user words. So even at a `JReachYB` exit, `Ch`
  contains `JReachU3.start` states, and a store state with a blocked TCB whose `YIELD_TO` word is nonzero has, by
  `TcbRel.st` and `YieldRel.tcb`, no `YieldBlockS` spec state; `ChainYB` (or `SlJAtYB`) at a `Ch` state does not follow.
* The missing fact is therefore exactly `yb`: "the glue's start state carries YieldBlock". It is a kernel invariant
  (true at every state reachable from boot: `boot_yieldBlock'`, `kernel_entry_yieldScope2U29`, `ybOut_keep` /
  `ChainYB.step` along local runs), not a platform fact, hence [J]. Deriving it needs the P2 chain anchored at boot
  and at the actual exit (`JReachU3.start` at `initASt`, `JReachSt.exit` only at `σe`, serial exits tied to the
  previous chain), which are changes to existing definitions or to `SerExitW` / `Ch σ` (W13's route). No Lean
  counter-model is built: the claim is that W12's premises do not mention the fact, not that a model violating it
  exists.
-/
import Fl4Proofs.P2.E2EVFl4W13
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EV
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
open Fl4Proofs.P2.OwnMap (fld oAFFINITY region TcbSlot InW InNode)
open Fl4Proofs.P2.E2E (StartAt SP LocalPath SerStep)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg)

noncomputable section
open Classical

section ent
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)

/-- **vmF's start entry facts**: `VmFEntJ12` with `ys` [J] replaced by `yb` [J] (module docstring, item 1). -/
structure VmFEntJ14 {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop)
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
  /-- [J] a clause-7 bundle at the start state whose spec state carries YieldBlock (module docstring: true at
  reachable states, not derivable from `Ch σ`). -/
  yb : SlJAtYB st K.toKLayout s
  /-- [P] -/
  gl : VmGlue st ar i.Locks s

theorem VmFEntJ14.toJ12 {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop}
    {MR : A3 → Fl4Spec.MachineState → Prop} {i : VmFArg S} {K : KLayoutV} {s : S}
    (E : VmFEntJ14 st ar arI AR MR i K s) : VmFEntJ12 st ar arI AR MR i K s :=
  ⟨E.nv, E.ix, E.hct, E.lk, SlJAtYB.toY st E.yb, E.gl⟩

/-- **vmR's start entry facts**: `VmREntJ11` with `ry` [J] replaced by `yb` [J] (module docstring, item 1). -/
structure VmREntJ14 {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop)
    (MR : A3 → Fl4Spec.MachineState → Prop) (i : VmRArg S) (Kl Kb : OwnMap.KLayout) (s : S) : Prop where
  ix : BunIxU (L := L) Kl Kl.heap.tcbs i.Cs i.Ω Kl.heap i.Sg Kl.heap.replies Kl.heap.scs Kl.heap.ntfns
    Kl.heap.scBits i.Ac s
  /-- [P] (`NonIdle`). -/
  hct : NonIdle st arI AR MR s
  /-- [J] a clause-7 bundle at the start state whose spec state carries YieldBlock (as `VmFEntJ14.yb`). -/
  yb : SlJAtYB st Kb s
  /-- [P] -/
  lk : i.Locks s i.rptr ∧ i.Locks s i.ep
  /-- [P] -/
  nb : L.mem s (rPrevA i.rptr) = 0#u64 ∧ L.mem s (rNextA i.rptr) = 0#u64
  /-- `loc_chain_all` clause 10's fl4-sync input `hfd`. -/
  fd : VmFoundC st i.rptr i.ep s

theorem VmREntJ14.toJ11 (hA : P0.ArchTotal ar) {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop}
    {MR : A3 → Fl4Spec.MachineState → Prop} {i : VmRArg S} {Kl Kb : OwnMap.KLayout} {s : S}
    (E : VmREntJ14 st arI AR MR i Kl Kb s) : VmREntJ11 st ar arI AR MR i Kl s :=
  VmREntJ13.toJ11 st ar hA ⟨E.ix, E.hct, E.lk, E.nb, E.fd⟩ E.yb

/-- **sl's start entry facts**: `SlQY` (W6's `SlQ` without `SlPreB.hy0f` / `hy0r`) and `yb` [J] (a clause-7 bundle
at the start state whose spec state carries YieldBlock, as `VmFEntJ14.yb`). -/
def SlQYB (ar : machine.Arch A) (Locks : S → U64 → Prop) (n : I64) (found : U64 × U64)
    (Cs Ω Sg Ac : Set U64) (K : OwnMap.KLayout) (m : U64 → U64) (s : S) : Prop :=
  SlQY st ar Locks n found Cs Ω Sg Ac K m s ∧ SlJAtYB st K s

theorem SlQYB.toQ (hA : P0.ArchTotal ar) {Locks : S → U64 → Prop} {n : I64} {found : U64 × U64}
    {Cs Ω Sg Ac : Set U64} {Kl : OwnMap.KLayout} {m : U64 → U64} {s : S}
    (h : SlQYB st ar Locks n found Cs Ω Sg Ac Kl m s) :
    Fl4Proofs.P2.PathObl.SlQ st ar Locks n found Cs Ω Sg Ac Kl m s :=
  SlQY.toQ st ar hA h.2 h.1

end ent

section start
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st] {A : Type}
  (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop) (MR : A3 → Fl4Spec.MachineState → Prop)

/-- **The start fact of `fl4LocP3W6`, vmF / vmR / sl at `VmFEntJ14` / `VmREntJ14` / `SlQYB`**, every slot at a state of
the current chain (`Ch σ`, as W12). -/
def StartP3W14 (Ch : S → Prop) (K : KLayoutV) (m : U64 → U64) (hK : RegionOKV K) (hU : UserOKV K) (c : U64)
    (hs : U64 → Prop) (q : SP) : Fl4IxW (S := S) → Prop
  | .vmF j => ∃ h : VmFPrem st ar j K m, GlueAt ((vmFSlot st ar hA hm).liftAt j K m hK hU h)
      (fun σ : S => Ch σ ∧ VmFEntJ14 st ar arI AR MR j K σ) c hs m q
  | .vmR j => ∃ h : VmRPremP3 st ar j K m, GlueAt ((vmRSlotP3 st ar hA hm).liftAt j K m hK hU h)
      (fun σ : S => Ch σ ∧ VmREntJ14 st arI AR MR j (userV K) K.toKLayout σ) c hs m q
  | .sl j => ∃ h : (slSlotP3W6 st ar hA hm hSt a0).Prem j K m,
      GlueAt ((slSlotP3W6 st ar hA hm hSt a0).liftAt j K m hK hU h)
      (fun σ : S => Ch σ ∧ SlQYB st ar j.Locks j.n j.found j.Cs j.Ω j.Sg j.Ac K.toKLayout m σ) c hs m q
  | i => StartP3W12 st ar hA hm hSt a0 arI AR MR Ch K m hK hU c hs q i

variable {arI AR MR}

/-- **`StartAt` of `fl4LocP3W6`'s family from `StartP3W14`**, given the current chain. -/
theorem startAt_P3W14 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR) {Ch : S → Prop}
    {K : KLayoutV} (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch)
    {m : U64 → U64} {hK : RegionOKV K} {hU : UserOKV K} {c : U64} {hs : U64 → Prop} {q : SP}
    {i : Fl4IxW (S := S)} (h : StartP3W14 st ar hA hm hSt a0 arI AR MR Ch K m hK hU c hs q i) :
    StartAt ((fl4LocP3W6 st ar hA hm hSt a0).paths (fl4Dflt st ar hm) i K m hK hU) c hs m q := by
  cases i with
  | vmF j =>
    obtain ⟨h, hG⟩ := h
    exact startAt_P3W12 st ar hA hm hSt a0 P hIoa hC (i := .vmF j)
      ⟨h, hG.mono fun σ he _ => ⟨he.1, he.2.toJ12 st ar⟩⟩
  | vmR j =>
    obtain ⟨h, hG⟩ := h
    exact startAt_P3W12 st ar hA hm hSt a0 P hIoa hC (i := .vmR j)
      ⟨h, hG.mono fun σ he _ => ⟨he.1, he.2.toJ11 st ar hA⟩⟩
  | io j => exact startAt_P3W12 st ar hA hm hSt a0 P hIoa hC (i := .io j) h
  | st j => exact startAt_P3W12 st ar hA hm hSt a0 P hIoa hC (i := .st j) h
  | irq j => exact startAt_P3W12 st ar hA hm hSt a0 P hIoa hC (i := .irq j) h
  | sl j =>
    obtain ⟨h, hG⟩ := h
    exact startAt_P3W12 st ar hA hm hSt a0 P hIoa hC (i := .sl j)
      ⟨h, hG.mono fun σ he _ => ⟨he.1, he.2.toQ st ar hA⟩⟩
  | vq j => exact startAt_P3W12 st ar hA hm hSt a0 P hIoa hC (i := .vq j) h

end start

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **FL4 end to end at P3 scope over W6's family, the four `YIELD_TO` [J]s replaced by one** (module docstring):
`serializable_fl4_localW12`'s statement (same `SerExitW`, `ExecW`, `Ch σ` starts) with `StartP3W14` starts. -/
theorem serializable_fl4_localW14 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutV}
    {Ch0 Ch : S → Prop} (h0 : Init s0) (hA0 : ArmInv s0) (hB : SerExitW P K0 Ch0) (nv0 : K0.vcpus = ∅)
    (hM0 : MapsV K0 s0)
    (h : ExecW ((fl4LocP3W6 st ar hA hm hSt a0).paths (fl4Dflt st ar hm)) (StartP3W14 st ar hA hm hSt a0 arI AR MR)
      P s0 K0 Ch0 s K Ch) (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  have hE := (execV_of_WC (fun _ _ _ _ _ _ _ _ _ hC hi => startAt_P3W14 st ar hA hm hSt a0 P hIoa hC hi) hB h).1
  have hok := serExitW_ok hB (vcpuLay_empty nv0)
  exact serializable_fl4_localP3W6V st ar hA hm hSt a0 h0 hA0 hok.1 hok.2 hM0 hE hq

end top

end
end Fl4Proofs.P2.E2EV
