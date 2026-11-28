/-
P3 (line p3J, gen 2): **`kernel_entry_reachU36`** = `kernel_entry_reachU35` with the path premise
narrowed to the invoked slot.

**Why** (inventory K1 / K4, `WS/handoff/p3J.md`): `JPathAtMU30` asks its per-cap leaf at *every* slot of
every CNode of `Z.th`, with the entry's message. FL4's boot gives the root CNode one `SchedControl` cap
per node (`crates/fl4-core/src/boot.rs:639-642`), so on any boot with two or more nodes the leaf
`cpu = Z.c` (K1, `JSchedCPathU7.core`) fails at some slot on every core, and `JUtPathMU29.core0`
(`Z.c = 0`, K4) fails on every core but 0 as soon as an untyped cap exists anywhere: the invocation half of
U35's syscall clause was vacuous on SMP. `jPathAtMU30_schedControl` states the forcing.

**Change**: `KDispHypsKVU36` = `KDispHypsKVU35` (collapse A, J: P3JLook's `JPathAtMU35`, `JPathAtMU30` with one more
hypothesis `LookAt ct cptr σ sl c`, is written back into `JPathAtMU30` itself, so the two records now have the same
fields; `KDispHypsKVU36.toU35`). `LookAt`: `sl` / `c` are the slot and cap the spec's `lookupCapAndSlot`
returns for the invoked `cptr` (with `capAt … (cslotAddr sl) = ok c`, FL4's read of the same slot;
`lookup_slot_refines` relates FL4's `cspace.lookup_slot` to it). The top `kernel_entry_reachU36` and its
predecessors U34 / U35 / U38 are removed (collapse A, J: no user once U40 runs on the base U33).

**Non-vacuity of the narrowing** (K1): `lookAt_unique` (one invoked slot per entry),
`lookAt_other` (no other slot satisfies `LookAt`), `JPathAtMU30.of_invoked` (the narrowed premise follows
from its instance at the invoked slot alone). So a `SchedControl {cpu}` cap with `cpu ≠ Z.c`, or an untyped
cap on a core ≠ 0, in a slot other than the invoked one no longer falsifies the premise; only invoking such
a cap does (K1 / K4 are then genuine [S] one-core premises about the invoked cap).

**Known false at these entries (not fixed here; the clause's scope)**, all VT-x [scope] leaves, now asked
only for the invoked cap:
* K6 / D1: a Thread cap invoked at label 88 (`TCBSetEPTRoot`) with no extra cap: FL4 `TruncatedMessage`
  (`crates/fl4-core/src/tcb.rs:410-411`), the ported spec `IllegalOperation`; with an EPT root cap FL4
  installs it (`tcb.rs:412-419`), the spec errs.
* K7: a frame cap invoked at label 60 (`X86PageMapEPT`): FL4 `ept::map_frame`
  (`crates/fl4-core/src/arch/x86_64/vspace.rs:495-496`) errs or maps with its own checks, the spec
  `IllegalOperation`.
* K3 / D2: `UntypedRetype` of an object type 14..18 with `virtualization() == 0`: FL4 `InvalidArgument 0`
  (`crates/fl4-core/src/untyped.rs:43`), the ported retype proceeds (Fl4Spec/Ext/VirtP3x §1).
At such entries `KDispHypsKVU36` / `JDecMRLK … VtxK …` are false and the clause says nothing.

Named premises still open (inherited, unchanged): [P] `JEntryAtR7V` (`ioapics`, `pins`, `map`, `mapr`);
`JPathAtMU30`'s leaves ([P]/[S] SchedControl `cpu = Z.c`, untyped `fan`, `core0`, `rcb` [P], `vtx` [scope],
Thread SetEPTRoot / EPT frame `JVtxScope` [scope]); [J]/[scope] `JDecMRLK … VtxK …`; [P] `KFinAtR13`; U34's
global [P] premises. No sorry.
-/
import Fl4Proofs.P3.XTopJointKEntryU35
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

/-- **One invoked slot per entry**: `lookupCapAndSlot` has a single outcome. -/
theorem lookAt_unique {ct cptr : U64} {σ : Fl4Spec.State Unit} {sl sl' : Fl4Spec.CslotPtr} {c c' : capability.Cap}
    (h : LookAt ct cptr σ sl c) (h' : LookAt ct cptr σ sl' c') : sl' = sl ∧ absCap c' = absCap c := by
  unfold LookAt at h h'
  rw [h] at h'
  have e := Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst h')
  have e2 := Except.ok.inj (Prod.mk.inj e).1
  exact ⟨(Prod.mk.inj e2).2.symm, (Prod.mk.inj e2).1.symm⟩

/-- **No other slot is the invoked one.** -/
theorem lookAt_other {ct cptr : U64} {σ : Fl4Spec.State Unit} {sl0 sl : Fl4Spec.CslotPtr} {c0 c : capability.Cap}
    (h0 : LookAt ct cptr σ sl0 c0) (hne : sl ≠ sl0) : ¬ LookAt ct cptr σ sl c :=
  fun h => hne (lookAt_unique h0 h).1

end Fl4Proofs.P3

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`KDispHypsKVU35` with `JPathAtMU30`** (the path premise at the invoked slot only). -/
structure KDispHypsKVU36 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets)
    (H : P1.Heap) (Cs D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64) (c : Fl4Spec.Syscall) : Prop where
  /-- [P]/[J] as `KDispHypsKVU35.inv`, the path premise at the invoked slot (`JPathAtMU30`). -/
  inv : ∀ ct call bl don, sched.cur_thread st s = ok ct → InvSys n call bl don →
    JEntryAtR7V arI AR Z s a σ ∧
    JPathAtMU30 (L := L) arI AR Z H Cs D s a σ ct call bl don false (L.mem s (regA ct layout.reg.CAP))
  /-- [P]/[J] as `KDispHypsKVU35.mid`, the path premise at the invoked slot (`JPathAtMU30`). -/
  mid : ∀ ct rg sr cr, sched.cur_thread st s = ok ct → MidSysR n c rg sr cr →
    JEntryAtR7V arI AR Z s a σ ∧
    JPathAtMU30 (L := L) arI AR Z H Cs D s a σ ct false false true true (L.mem s (regA ct rg))

variable {arI}

/-- **`JPathAtMU30` from its instance at the invoked slot alone** (non-vacuity of the narrowing): only the
slot `lookupCapAndSlot` returns is asked about; caps in other slots are unconstrained. -/
theorem JPathAtMU30.of_invoked {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S}
    {ar : A} {σ : Fl4Spec.State Unit} {ct : U64} {ic bl cd fp : Bool} {cptr : U64}
    {sl0 : Fl4Spec.CslotPtr} {c0 : capability.Cap} (h0 : LookAt ct cptr σ sl0 c0)
    (hI : ∀ (info : msginfo.MessageInfo) (mi : Fl4Spec.MessageInfo) (buf : U64) (buffer : Option Fl4Spec.ObjRef)
      (r2 : core.result.Result (Aeneas.Std.Array obj.Slot 3#usize) error.Fault)
      (er : Except Fl4Spec.Fault (List (Fl4Spec.Cap × Fl4Spec.CslotPtr))) (argsU : List U64)
      (c : capability.Cap) (e : Aeneas.Std.Array obj.Slot 3#usize) (exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)),
      capAt (L.mem s) (cslotAddr sl0) = ok c → LookAt ct cptr σ sl0 c → Vs.NativeCap c →
      JPathMEU30 (L := L) arI AR Z H Cs D s ar σ info.label (msgLen info buf) bl ic cd fp buf e
        mi.miLabel argsU (Fl4Spec.toBl cptr.bv) sl0 exs buffer ct c) :
    JPathAtMU30 (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr := by
  intro info mi buf buffer r2 er argsU _ _ _ _ _ _ _ sl c e exs _ h9 _ _ _ h13 hL
  obtain ⟨rfl, -⟩ := lookAt_unique h0 hL
  exact hI info mi buf buffer r2 er argsU c e exs h9 hL h13

/-- `KDispHypsKVU36` is `KDispHypsKVU35` (the same fields, `JPathAtMU30` narrowed in place). -/
theorem KDispHypsKVU36.toU35 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S}
    {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : KDispHypsKVU36 (L := L) arI AR Z H Cs D s a σ n c) :
    KDispHypsKVU35 (L := L) arI AR Z H Cs D s a σ n c :=
  KDispHypsKVU35.mk h.inv h.mid

end

end

end Fl4Proofs.P3.SInvR.G5
