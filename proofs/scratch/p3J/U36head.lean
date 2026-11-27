/-
P3 (line p3J, gen 2): **`kernel_entry_reachU36`** = `kernel_entry_reachU35` with the path premise
narrowed to the invoked slot.

**Why** (inventory K1 / K4, `WS/handoff/p3J.md`): `JPathAtMU30` asks its per-cap leaf at *every* slot of
every CNode of `Z.th`, with the entry's message. FL4's boot gives the root CNode one `SchedControl` cap
per node (`crates/fl4-core/src/boot.rs:639-642`), so on any boot with two or more nodes the leaf
`cpu = Z.c` (K1, `JSchedCPathU7.core`) fails at some slot on every core, and `JUtPathMU29.core0`
(`Z.c = 0`, K4) fails on every core but 0 as soon as an untyped cap exists anywhere: the invocation half of
U35's syscall clause was vacuous on SMP. `jPathAtMU30_schedControl` states the forcing.

**Change**: `KDispHypsKVU36` = `KDispHypsKVU35` with `JPathAtMU30` ↦ **`JPathAtMU35`** (P3JLook): one more
hypothesis `LookAt ct cptr σ sl c`, i.e. `sl` / `c` are the slot and cap the spec's `lookupCapAndSlot`
returns for the invoked `cptr` (with `capAt … (cslotAddr sl) = ok c`, FL4's read of the same slot;
`lookup_slot_refines` relates FL4's `cspace.lookup_slot` to it). The proof is P3JGen's kernel-checked
transport of U35's proof onto the narrowed premises (16 conversions, the refinement lemma's `hDec` and the
two consumers re-proved in P3JLook).

**Premise diff U35 → U36**: in the syscall clause `KDispHypsKVU35 …` ↦ `KDispHypsKVU36 …` (`JPathAtMU30` ↦
`JPathAtMU35`, weaker: `JPathAtMU30.toU35`). Every other premise and the conclusion verbatim. No new premise,
[W] 0. **`kernel_entry_reachU35_of36`** proves U35's statement, verbatim, from U36.

**Non-vacuity of the narrowing** (K1): `lookAt_unique` (one invoked slot per entry),
`lookAt_other` (no other slot satisfies `LookAt`), `JPathAtMU35.of_invoked` (the narrowed premise follows
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
`JPathAtMU35`'s leaves ([P]/[S] SchedControl `cpu = Z.c`, untyped `fan`, `core0`, `rcb` [P], `vtx` [scope],
Thread SetEPTRoot / EPT frame `JVtxScope` [scope]); [J]/[scope] `JDecMRLK … VtxK …`; [P] `KFinAtR13`; U34's
global [P] premises. No sorry.
-/
import Fl4Proofs.P3.P3JGen
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

/-- **`KDispHypsKVU35` with `JPathAtMU35`** (the path premise at the invoked slot only). -/
structure KDispHypsKVU36 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets)
    (H : P1.Heap) (Cs D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64) (c : Fl4Spec.Syscall) : Prop where
  /-- [P]/[J] as `KDispHypsKVU35.inv`, the path premise at the invoked slot (`JPathAtMU35`). -/
  inv : ∀ ct call bl don, sched.cur_thread st s = ok ct → InvSys n call bl don →
    JEntryAtR7V arI AR Z s a σ ∧
    JPathAtMU35 (L := L) arI AR Z H Cs D s a σ ct call bl don false (L.mem s (regA ct layout.reg.CAP))
  /-- [P]/[J] as `KDispHypsKVU35.mid`, the path premise at the invoked slot (`JPathAtMU35`). -/
  mid : ∀ ct rg sr cr, sched.cur_thread st s = ok ct → MidSysR n c rg sr cr →
    JEntryAtR7V arI AR Z s a σ ∧
    JPathAtMU35 (L := L) arI AR Z H Cs D s a σ ct false false true true (L.mem s (regA ct rg))

variable {arI}

/-- **The narrowed premise is weaker**: `JPathAtMU30` gives `JPathAtMU35` (drop `LookAt`). -/
theorem JPathAtMU30.toU35 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S}
    {ar : A} {σ : Fl4Spec.State Unit} {ct : U64} {ic bl cd fp : Bool} {cptr : U64}
    (h : JPathAtMU30 (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr) :
    JPathAtMU35 (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr :=
  fun info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13 _ =>
    h info mi buf buffer r2 er argsU h1 h2 h3 h4 h5 h6 h7 sl c e exs h8 h9 h10 h11 h12 h13

/-- **`JPathAtMU35` from its instance at the invoked slot alone** (non-vacuity of the narrowing): only the
slot `lookupCapAndSlot` returns is asked about; caps in other slots are unconstrained. -/
theorem JPathAtMU35.of_invoked {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S}
    {ar : A} {σ : Fl4Spec.State Unit} {ct : U64} {ic bl cd fp : Bool} {cptr : U64}
    {sl0 : Fl4Spec.CslotPtr} {c0 : capability.Cap} (h0 : LookAt ct cptr σ sl0 c0)
    (hI : ∀ (info : msginfo.MessageInfo) (mi : Fl4Spec.MessageInfo) (buf : U64) (buffer : Option Fl4Spec.ObjRef)
      (r2 : core.result.Result (Aeneas.Std.Array obj.Slot 3#usize) error.Fault)
      (er : Except Fl4Spec.Fault (List (Fl4Spec.Cap × Fl4Spec.CslotPtr))) (argsU : List U64)
      (c : capability.Cap) (e : Aeneas.Std.Array obj.Slot 3#usize) (exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)),
      capAt (L.mem s) (cslotAddr sl0) = ok c → LookAt ct cptr σ sl0 c → Vs.NativeCap c →
      JPathMEU30 (L := L) arI AR Z H Cs D s ar σ info.label (msgLen info buf) bl ic cd fp buf e
        mi.miLabel argsU (Fl4Spec.toBl cptr.bv) sl0 exs buffer ct c) :
    JPathAtMU35 (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr := by
  intro info mi buf buffer r2 er argsU _ _ _ _ _ _ _ sl c e exs _ h9 _ _ _ h13 hL
  obtain ⟨rfl, -⟩ := lookAt_unique h0 hL
  exact hI info mi buf buffer r2 er argsU c e exs h9 hL h13

/-- **The ∀-slot premise forces every SchedControl cap onto the current core** (inventory K1): at an entry
whose front-end reads succeed, `JPathAtMU30` gives `cpu = Z.c` for a `SchedControl cpu` cap in *any* CNode
slot, invoked or not. -/
theorem jPathAtMU30_schedControl {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S}
    {ar : A} {σ : Fl4Spec.State Unit} {ct : U64} {ic bl cd fp : Bool} {cptr : U64}
    (h : JPathAtMU30 (L := L) arI AR Z H Cs D s ar σ ct ic bl cd fp cptr)
    {info : msginfo.MessageInfo} {mi : Fl4Spec.MessageInfo} {buf : U64} {buffer : Option Fl4Spec.ObjRef}
    {e : Aeneas.Std.Array obj.Slot 3#usize} {exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)} {argsU : List U64}
    (h1 : msg.msg_info st s ct = ok info) (h2 : Fl4Spec.getMessageInfo (Z := Unit) ct.bv σ = ({(mi, σ)}, False))
    (h3 : msg.lookup_ipc_buffer st s false ct = ok buf)
    (h4 : Fl4Spec.lookupIpcBuffer (Z := Unit) false ct.bv σ = ({(buffer, σ)}, False))
    (h5 : ipc.lookup_extra_caps st s ct buf info = ok (.Ok e))
    (h6 : (Fl4Spec.lookupExtraCaps (Z := Unit) ct.bv buffer mi).run σ = ({(.ok exs, σ)}, False))
    (h7 : Fl4Spec.getMrs (Z := Unit) ct.bv buffer mi σ = ({(argsU.map UScalar.bv, σ)}, False))
    {sl : Fl4Spec.CslotPtr} {cpu : U64} (h8 : ∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length))
    (h9 : capAt (L.mem s) (cslotAddr sl) = ok (.SchedControl cpu))
    (h10 : Fl4Spec.getCap (Z := Unit) sl σ = ({(absCap (.SchedControl cpu), σ)}, False)) :
    cpu = Z.c :=
  h info mi buf buffer (.Ok e) (.ok exs) argsU h1 h2 h3 h4 h5 h6 h7 sl _ e exs h8 h9 h10 rfl rfl trivial

/-- `KDispHypsKVU36` as the transported record (P3JGen's copy of `KDispHypsKVU35`). -/
theorem KDispHypsKVU36.toJ {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S}
    {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : KDispHypsKVU36 (L := L) arI AR Z H Cs D s a σ n c) :
    Fl4ProofsJ.P3.SInvR.G5.KDispHypsKVU35 (L := L) arI AR Z H Cs D s a σ n c :=
  Fl4ProofsJ.P3.SInvR.G5.KDispHypsKVU35.mk h.inv h.mid

/-- **`KDispHypsKVU35` gives `KDispHypsKVU36`** (`JPathAtMU30.toU35`). -/
theorem KDispHypsKVU35.toU36 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S}
    {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : KDispHypsKVU35 (L := L) arI AR Z H Cs D s a σ n c) :
    KDispHypsKVU36 (L := L) arI AR Z H Cs D s a σ n c :=
  ⟨fun ct call bl don hct hi => ⟨(h.inv ct call bl don hct hi).1, (h.inv ct call bl don hct hi).2.toU35⟩,
   fun ct rg sr cr hct hm => ⟨(h.mid ct rg sr cr hct hm).1, (h.mid ct rg sr cr hct hm).2.toU35⟩⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)
