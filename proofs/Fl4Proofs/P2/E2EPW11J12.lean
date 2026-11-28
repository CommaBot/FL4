/-
P2 (line jsweep, gen 5): **`serializable_fl4_localW11PJ12`: sl `SlPreR.hrz` and vmR `VmREntJ11.nb` replaced by
fl4-sync's own no-neighbour check** (new definitions only, on top of E2EPW11J11; no existing statement changed).

## Where they stood (PJ11)

* sl `SlPreR.hrz`: at every `LocalPre` successor `X` of the start state, `mem X (rNextA r) &&& ~~~1 = 0` and
  `mem X (rPrevA r) &&& ~~~1 = 0` for the found reply `r` (tagged [P] in gen 4).
* vmR `VmREntJ11.nb`: `mem s (rPrevA rptr) = 0 ∧ mem s (rNextA rptr) = 0` at the start state (raw words, [P]).

## They are not kernel invariants (finding)

Neither holds at every reachable state where the fast path finds a reply whose caller is blocked on reply with an
UnknownSyscall / VM fault: a reply in the middle of an SC's call stack, or a detached reply left linked by
`schedcontext::unbind_reply` (P3's `CallRel.det` allows such chains), has non-zero links, and the core's own check
(`fastpath::reply_recv_found` / `fastpath_vm::reply_recv_vm_found`: `r.next(s) != 0 && r.next_is_head(s)`) only
declines the head of a stack. Concrete sequence (handoff gen 5): `A` (own SC) faults with UnknownSyscall to a
passive handler `B` waiting with reply `R1` (donation: `R1.next = SC|1`); `B` calls a passive `C` with reply `R2`
(`reply_push`: `R1.next = R2`, head bit clear, `R2.prev = R1`); a fresh released SC is bound to the blocked `A`
(`SchedContextBind` allows it); a thread `T` with its own SC holding a copy of `R1`'s cap does ReplyRecv on it:
`R1`'s caller is `A`, blocked on reply, fault UnknownSyscall, `R1.next = R2 ≠ 0` not head, so the core's check
passes, and `hrz` / `nb` are false there.

## What does hold: fl4-sync checks exactly these words

`fl4_sync::local_syscall` (crates/fl4-sync/src/lib.rs, the `SysReplyRecv` arm, l.710-724) locks the reply and then
continues only if `Reply(r).prev(s) == 0 && Reply(r).next(s) == 0` (masked words, as `obj::Reply::prev` / `next`
read them), "reply_remove would write the reply objects next to it on the call stack, which are not locked". The
local path (sl and vmR alike: `handle_syscall_local` / `handle_reply_recv_vm_local` are called from that one arm, at
the same state `s`) needs zero links for its footprint: with non-zero non-head links `reply_remove` writes the
neighbours' `PREV` / `NEXT` words, which no held lock covers, so the weaker "not head" check does not suffice. So
the premise is fl4-sync's call-site check, transcribed at the entry state, with the extracted readers:

* **`SlNbC`** [P] (sl): `¬ SlTrap → n = SysReplyRecv → Reply.prev found.1 = ok 0 ∧ Reply.next found.1 = ok 0` at
  the entry state (the arm's guard as in `SlSyncC`).
* **`VmNbC`** [P] (vmR): `Reply.prev rptr = ok 0 ∧ Reply.next rptr = ok 0` at the entry state (unguarded, as
  `VmFoundC`: vmR's slot is reached only from that arm).

## Derived here

* `and_not1_even`, **`callRel_nb_of_masked`**: at a `CallRel` state (P3, replies and SCs even and non-null), a reply
  whose masked links are 0 has raw links 0: on a stack its `NEXT` is `sc ||| 1` or a reply, both non-zero masked;
  detached, `CallRel.det` gives `NEXT`'s bit 0 clear and a non-zero `PREV` a reply.
* **`vmNb_of`**: vmR's `nb` (raw, at the start state) from `VmNbC`, the bundle (`JAtZ.call`, `rp`, `c0`, SchedRel's
  SC bounds) and `VmFoundC` (the reply is a heap reply, so in `Z.R` by `hset`).
* **`slHrz_of`**: sl's `hrz` at every `LocalPre` successor from `SlNbC` (the prefix writes only `W3`, and the reply's
  `PREV` / `NEXT` are in the reply's own region, `RegionOKX.rpW`, `SlJAtZ.notW3`).
* `SlPreR2` (`SlPreR` without `hrz`), `SlEntJ12` (`SlEntJ11` with `r : SlPreR2` and `nbc : SlNbC`),
  `SlEntJ12.toJ11`; `VmREntJ12` (`VmREntJ11` with `nbc : VmNbC` for `nb`), `VmREntJ12.toJ11`.
* `StartD` (= `StartC` with sl at `SlEntJ12`, vmR at `VmREntJ12`), `startC_of_D`,
  **`serializable_fl4_localW11PJ12`**; satisfiability `startD_sl_sat`, `startD_vmR_sat`.

## Premises changed (PJ11 → PJ12)

| slot | PJ11 | PJ12 |
|---|---|---|
| sl | `SlPreR.hrz` [P] (kernel state at every successor) | `SlEntJ12.nbc : SlNbC` [P] (fl4-sync's check, entry state) |
| vmR | `VmREntJ11.nb` [P] (raw kernel words) | `VmREntJ12.nbc : VmNbC` [P] (fl4-sync's check, masked) |
All other premises as PJ11.
-/
import Fl4Proofs.P2.E2EPW11J11
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld)
open Fl4Proofs.P2.E2E (StartAt SP SerStep)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg)

noncomputable section
open Classical

/-! ## Masked-zero links are zero links at a `CallRel` state -/

section callrel

/-- An even word is its own value with bit 0 masked. -/
theorem and_not1_even (x : U64) (h : x.val % 2 = 0) : x &&& ~~~1#u64 = x := by
  apply eq_of_bv; apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [UScalar.bv_and, UScalar.bv_not, BitVec.getLsbD_and, BitVec.getLsbD_not, one_bit, hi]
  by_cases h0 : i = 0
  · subst h0; have := Fl4Proofs.P3.Sched.even_bit0 x h
    simp only [BitVec.getLsbD_eq_getElem hi] at this; simp [this]
  · simp [h0]

/-- **A reply with masked-zero links has zero links** at a `CallRel` state (module docstring). -/
theorem callRel_nb_of_masked {m : U64 → U64} {R C : Set U64} {σ : Fl4Spec.State Unit} {Lst : U64 → List U64}
    (hCR : Fl4Proofs.P3.Sched.CallRel m R C σ Lst) (hR : ∀ d ∈ R, d.val % 2 = 0 ∧ d ≠ 0#u64)
    (hC : ∀ q ∈ C, q.val % 2 = 0 ∧ q ≠ 0#u64) {r : U64} (hr : r ∈ R)
    (hn : m (rNextA r) &&& ~~~1#u64 = 0#u64) (hp : m (rPrevA r) &&& ~~~1#u64 = 0#u64) :
    m (rPrevA r) = 0#u64 ∧ m (rNextA r) = 0#u64 := by
  have hRm : ∀ d ∈ R, d &&& ~~~1#u64 ≠ 0#u64 := fun d hd => by
    rw [and_not1_even d (hR d hd).1]; exact (hR d hd).2
  by_cases hlive : ∃ sc ∈ C, r ∈ Lst sc
  · exfalso
    obtain ⟨sc, hsc, hrL⟩ := hlive
    obtain ⟨-, hLR, -, hW⟩ := hCR.stack sc hsc
    unfold Fl4Proofs.P3.Sched.StackW at hW
    obtain ⟨k, hkl, e⟩ := List.getElem_of_mem hrL
    have hw := (hW.2 k hkl).2
    rw [e] at hw
    rw [hw] at hn
    cases k with
    | zero =>
      dsimp only at hn
      rw [Fl4Proofs.P3.Sched.or1_and_not1 sc (hC sc hsc).1] at hn
      exact (hC sc hsc).2 hn
    | succ j =>
      dsimp only at hn
      have hj : j < (Lst sc).length := by omega
      rw [List.getD_eq_getElem _ _ hj] at hn
      exact hRm _ (hLR _ (List.getElem_mem hj)) hn
  · have hd : Fl4Proofs.P3.Sched.Detached C Lst r := fun sc hsc h => hlive ⟨sc, hsc, h⟩
    obtain ⟨hb, -, hpv⟩ := hCR.det r hr hd
    refine ⟨?_, ?_⟩
    · by_contra hne
      exact hRm _ (hpv hne).1 hp
    · rw [← and_not1_even _ (Fl4Proofs.P3.Sched.even_of_bit hb)]; exact hn

end callrel

/-! ## fl4-sync's no-neighbour check -/

section chk
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

variable (st) in
/-- [P] **fl4-sync's no-neighbour check, sl** (`local_syscall`, crates/fl4-sync/src/lib.rs l.710-724): on the
untrapped `SysReplyRecv` arm, after locking `found.1`, fl4-sync continues only if
`Reply(r).prev(s) == 0 && Reply(r).next(s) == 0`, at the state it then hands to `handle_syscall_local`. -/
def SlNbC (n : I64) (found : U64 × U64) (s : S) : Prop :=
  ¬ SlTrap st s → n = fl4_abi.syscall.SysReplyRecv →
    obj.Reply.prev st found.1 s = ok 0#u64 ∧ obj.Reply.next st found.1 s = ok 0#u64

variable (st) in
/-- [P] **fl4-sync's no-neighbour check, VM ReplyRecv** (the same check, l.717-718; `handle_reply_recv_vm_local`
is called from that arm only, at the same state). -/
def VmNbC (rptr : U64) (s : S) : Prop :=
  obj.Reply.prev st rptr s = ok 0#u64 ∧ obj.Reply.next st rptr s = ok 0#u64

theorem SlNbC.mem {n : I64} {found : U64 × U64} {s : S} (h : SlNbC st n found s) (hS : ¬ SlTrap st s)
    (hn : n = fl4_abi.syscall.SysReplyRecv) :
    L.mem s (rNextA found.1) &&& ~~~1#u64 = 0#u64 ∧ L.mem s (rPrevA found.1) &&& ~~~1#u64 = 0#u64 := by
  obtain ⟨h1, h2⟩ := h hS hn
  rw [reply_prev_ok] at h1
  rw [reply_next_ok] at h2
  exact ⟨ok_inj_ff h2, ok_inj_ff h1⟩

variable {A : Type} {ar : machine.Arch A}
variable {K : KLayout} {s : S} {A' : Type} {arI : machine.Arch A'} {AR : A' → Fl4Spec.Cr3 → Prop}
  {Zx : Fl4Proofs.P3.XSets} {Cx Ax : Set U64} {Lst : U64 → List U64} {D : Set U64} {a' : A'}
  {σ : Fl4Spec.State Unit}

/-- **vmR's `nb` from fl4-sync's check** and P3's call stacks at the bundle state (module docstring). -/
theorem vmNb_of (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) {rptr ep : U64}
    (hfd : VmFoundC st rptr ep s) (hN : VmNbC st rptr s) :
    L.mem s (rPrevA rptr) = 0#u64 ∧ L.mem s (rNextA rptr) = 0#u64 := by
  have hJ : SlJAt (L := L) K s := ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩
  have hr : rptr ∈ Zx.R := B.j.hset.2.2 rptr (hJ.vmFound hfd).1
  have hRP := B.j.rp
  have hev : ∀ d ∈ Zx.R, d.val % 2 = 0 ∧ d ≠ 0#u64 := fun d hd => by
    have := hRP.align d hd
    exact ⟨by omega, this.2.1⟩
  have hC : ∀ q ∈ Zx.C, q.val % 2 = 0 ∧ q ≠ 0#u64 := fun q hq => by
    refine ⟨?_, B.j.c0 q hq⟩
    obtain ⟨Q0, R0, -, hs⟩ := B.j.xtop.fin.1.1.1.lists
    obtain ⟨x, n', -, hx⟩ := hs.scs q hq
    have := hx.bounds.1
    omega
  obtain ⟨h1, h2⟩ := hN
  rw [reply_prev_ok] at h1
  rw [reply_next_ok] at h2
  exact callRel_nb_of_masked B.j.call hev hC hr (ok_inj_ff h2) (ok_inj_ff h1)

/-- **sl's `hrz` from fl4-sync's check**: the prefix (`LocalPre`) writes only `W3`, which misses the reply's words. -/
theorem slHrz_of (hA : P0.ArchTotal ar) (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) {n : I64}
    {found : U64 × U64} (hC : SlSyncC st n found s) (hN : SlNbC st n found s) :
    ¬ SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) →
      L.mem X (rNextA found.1) &&& ~~~1#u64 = 0#u64 ∧ L.mem X (rPrevA found.1) &&& ~~~1#u64 = 0#u64 := by
  intro hS a X a1 hLP
  have hJ : SlJAt (L := L) K s := ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩
  have hrp := (hJ.rrG hC.fd hS (hC.arm hS)).1
  obtain ⟨hW, -⟩ := B.lpW hA hLP
  have X0 := B.regionOKX
  obtain ⟨rn, an⟩ := X0.rpW _ hrp layout.reply.NEXT (by simp [layout.reply.NEXT]) (by simp [layout.reply.NEXT])
  obtain ⟨rp, ap⟩ := X0.rpW _ hrp layout.reply.PREV (by simp [layout.reply.PREV]) (by simp [layout.reply.PREV])
  have nn := B.notW3 (b := rNextA found.1) (by unfold rNextA; rw [rn]; intro e; cases e)
    (fun c => by unfold rNextA; rw [rn]; intro e; cases e)
  have np := B.notW3 (b := rPrevA found.1) (by unfold rPrevA; rw [rp]; intro e; cases e)
    (fun c => by unfold rPrevA; rw [rp]; intro e; cases e)
  obtain ⟨h1, h2⟩ := hN.mem hS (hC.arm hS)
  exact ⟨by rw [hW.mem_eq (b := rNextA found.1) an nn]; exact h1,
    by rw [hW.mem_eq (b := rPrevA found.1) ap np]; exact h2⟩

end chk

/-! ## The entry facts with the check -/

section ent
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)

/-- **`SlPreR` without `hrz`**: `hy0f` / `hy0r` [J] (line iolay), `hlk` [P], verbatim. -/
structure SlPreR2 (K : KLayout) (Locks : S → U64 → Prop) (found : U64 × U64) (s : S) : Prop where
  /-- [J] (line iolay: YieldScope) as `SlPreR.hy0f`. -/
  hy0f : SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) → ∀ {ptr badge dest r : U64},
    FaultChecks st X (L.curW s) ptr badge dest r → L.mem X (yieldA dest) = 0#u64
  /-- [J] (line iolay: YieldScope) as `SlPreR.hy0r`. -/
  hy0r : ¬ SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) → ∀ u usc,
    RRChecks st ar X a1 (L.curW s) found.1 found.2 u usc → L.mem X (yieldA u) = 0#u64
  /-- [P] as `SlPreR.hlk`. -/
  hlk : ¬ SlTrap st s → Locks s found.2

/-- **sl's start entry facts, `hrz` replaced by fl4-sync's check** (`SlEntJ11` with `nbc` and `SlPreR2`). -/
structure SlEntJ12 {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop)
    (MR : A3 → Fl4Spec.MachineState → Prop) (i : SlArg S) (K : KLayout) (s : S) : Prop where
  /-- Index convention, as `SlEntJ11.ix`. -/
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
  /-- [J] `hy0f` / `hy0r` (iolay), [P] `hlk`. -/
  r : SlPreR2 st ar K i.Locks i.found s

/-- **vmR's start entry facts, `nb` replaced by fl4-sync's check** (`VmREntJ11` with `nbc : VmNbC`). -/
structure VmREntJ12 {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop)
    (MR : A3 → Fl4Spec.MachineState → Prop) (i : VmRArg S) (Kl : OwnMap.KLayout) (s : S) : Prop where
  /-- Index convention, as `VmREntJ11.ix`. -/
  ix : BunIxU (L := L) Kl Kl.heap.tcbs i.Cs i.Ω Kl.heap i.Sg Kl.heap.replies Kl.heap.scs Kl.heap.ntfns
    Kl.heap.scBits i.Ac s
  /-- [P] (`NonIdle`). -/
  hct : NonIdle st arI AR MR s
  /-- [J] as `VmREntJ11.ry` (iolay). -/
  ry : ∀ a s2 a2, LocalPre (st := st) ar s a (s2, a2) →
    ∀ u usc, RRChecksG st ar fl4_abi.consts.fault.VMFault s2 a2 (L.curW s) i.rptr i.ep u usc →
      L.mem s2 (yieldA u) = 0#u64
  /-- [P] -/
  lk : i.Locks s i.rptr ∧ i.Locks s i.ep
  /-- [P] fl4-sync's no-neighbour check (`VmNbC`). -/
  nbc : VmNbC st i.rptr s
  /-- fl4-sync's `found` (`VmFoundC`), as `VmREntJ11.fd`. -/
  fd : VmFoundC st i.rptr i.ep s

variable {st ar}

theorem SlEntJ12.toJ11 (hA : P0.ArchTotal ar) {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop}
    {MR : A3 → Fl4Spec.MachineState → Prop} {i : SlArg S} {K : KLayout} {s : S}
    (E : SlEntJ12 st ar arI AR MR i K s) : SlEntJ11 st ar arI AR MR i K s := by
  obtain ⟨A', arI', AR', Zx, Lst, D, a', σ, B, -⟩ := E.ix
  exact ⟨E.ix, E.sg, E.hct, E.el, E.sc, E.acc, ⟨E.r.hy0f, slHrz_of hA B E.sc E.nbc, E.r.hy0r, E.r.hlk⟩⟩

theorem VmREntJ12.toJ11 {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop}
    {MR : A3 → Fl4Spec.MachineState → Prop} {i : VmRArg S} {Kl : OwnMap.KLayout} {s : S}
    (E : VmREntJ12 st ar arI AR MR i Kl s) : VmREntJ11 st ar arI AR MR i Kl s := by
  refine ⟨E.ix, E.hct, E.ry, E.lk, ?_, E.fd⟩
  obtain ⟨-, -, -, -, -, -, -, ⟨A', arI', AR', Zx, Lst, D, a', σ, B, -⟩⟩ := E.ix
  exact vmNb_of B E.fd E.nbc

end ent

/-! ## The start fact and the top -/

section start
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st] {A : Type}
  (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop) (MR : A3 → Fl4Spec.MachineState → Prop)

/-- **The start fact with sl at `SlEntJ12` and vmR at `VmREntJ12`** [P] (module docstring). -/
def StartD (Ch : S → Prop) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (q : SP) : Fl4IxW (S := S) → Prop
  | .sl j => ∃ q0, (∃ h : (slSlotP3W6 st ar hA hm hSt a0).Prem j K.toKLayoutV m,
      GlueAt ((slSlotP3W6 st ar hA hm hSt a0).liftAt j K.toKLayoutV m hK.base hU.base h)
        (fun σ : S => Ch σ ∧ SlEntJ12 st ar arI AR MR j K.toKLayoutV.toKLayout σ) c hs m q0) ∧
      q = cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) c q0 ∅
  | .vmR j => ∃ q0, (∃ h : VmRPremA st j K.toKLayoutV,
      GlueAt ((vmRSlotA st ar hA hm).liftAt j K.toKLayoutV m hK.base hU.base h)
        (fun σ : S => Ch σ ∧ VmREntJ12 st ar arI AR MR j (userV K.toKLayoutV) σ) c hs m q0) ∧
      q = cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) c q0 ∅
  | i => StartC st ar hA hm hSt a0 arI AR MR Ch K m hK hU c hs q i

variable {arI AR MR}

omit [Fl4Proofs.P1.PlainStore st] in
/-- **`StartD` gives `StartC`.** -/
theorem startC_of_D {Ch : S → Prop} {K : KLayoutP} {m : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K}
    {c : U64} {hs : U64 → Prop} {q : SP} {i : Fl4IxW (S := S)}
    (h : StartD st ar hA hm hSt a0 arI AR MR Ch K m hK hU c hs q i) :
    StartC st ar hA hm hSt a0 arI AR MR Ch K m hK hU c hs q i := by
  cases i with
  | sl j =>
    obtain ⟨q0, ⟨h1, hG⟩, e⟩ := h
    exact ⟨q0, ⟨h1, hG.mono fun σ he _ => ⟨he.1, he.2.toJ11 hA⟩⟩, e⟩
  | vmR j =>
    obtain ⟨q0, ⟨h1, hG⟩, e⟩ := h
    exact ⟨q0, ⟨h1, hG.mono fun σ he _ => ⟨he.1, he.2.toJ11⟩⟩, e⟩
  | vmF j => exact h
  | io j => exact h
  | st j => exact h
  | irq j => exact h
  | vq j => exact h

end start

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

end top

/-! ## Satisfiability at a chain state -/

section sat
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st] {A : Type}
  (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

omit [Fl4Proofs.P1.PlainStore st] in
/-- **sl's `StartD` holds at every chain state with sl's entry facts** (memory `L.mem σ`, core `L.cpu σ`, locks
`j.Locks σ`), given the record. -/
theorem startD_sl_sat {Ch : S → Prop} {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K) {σ : S} (hσ : Ch σ)
    {j : SlArg S} (h : (slSlotP3W6 st ar hA hm hSt a0).Prem j K.toKLayoutV (L.mem σ))
    (hE : SlEntJ12 st ar arI AR MR j K.toKLayoutV.toKLayout σ) (a : A) :
    ∃ q, StartD st ar hA hm hSt a0 arI AR MR Ch K (L.mem σ) hK hU (L.cpu σ) (j.Locks σ) q (.sl j) :=
  ⟨_, _, ⟨h, σ, a, ⟨hσ, hE⟩, rfl, rfl, fun _ _ _ => rfl, rfl⟩, rfl⟩

/-- **vmR's `StartD` holds at every chain state with vmR's entry facts**, given the [P]s `cs` / `kd` and
`K.vcpus = ∅` (as `startA_vmR_sat`). -/
theorem startD_vmR_sat {Ch : S → Prop} {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K)
    {σe σ : S} (hC : ChainOf (L := L) arI AR MR σe K.toKLayoutV.toKLayout Ch) (hσ : Ch σ) (nv : K.vcpus = ∅)
    {j : VmRArg S} (hE : VmREntJ12 st ar arI AR MR j (userV K.toKLayoutV) σ) (cs : ∀ c ∈ j.Cs, c.val < 64)
    (kd : ∀ s : S, SlJAt (L := L) (userV K.toKLayoutV) s → KernDetAt (L := L) (userV K.toKLayoutV) j.Locks s)
    (a : A) :
    ∃ q, StartD st ar hA hm hSt a0 arI AR MR Ch K (L.mem σ) hK hU (L.cpu σ) (j.Locks σ) q (.vmR j) := by
  have h : VmRPremA st j K.toKLayoutV :=
    ⟨nv, ⟨σ, by rw [userV_empty nv]; exact ChainOf.bun hC σ hσ⟩, cs, kd⟩
  exact ⟨_, _, ⟨h, σ, a, ⟨hσ, hE⟩, rfl, rfl, fun _ _ _ => rfl, rfl⟩, rfl⟩

end sat

end
end Fl4Proofs.P2.E2EP
