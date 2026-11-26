/-
P3 against the virtualization extension (line virt, gen 2; proofs/VIRT-PLAN.md §10 R7, route B):
**FL4's VT-x retype gate refines the extended decoder**.

FL4 source: `crates/fl4-core/src/untyped.rs:42-44` (`untyped::decode`: `UntypedRetype` of a type in
`ot::X86Vcpu ..< ot::Count` = 14..18 on a platform with `virtualization() == 0` is `InvalidArgument 0`, after the
length and extra-cap checks). Spec: `Fl4Spec/Ext/VirtDispatch` (`fl4DecodeInvocationV`, untyped caps) /
`Ext/VirtFinalise` (`untypedVtxGate`), extending l4v `Decode_A.decode_untyped_invocation` (ported as
`fl4DecodeUntypedInvocation`, which would create the VT-x objects: p3J's K3 / D2).

* `untyped_decode_vtx_gate`: FL4's `untyped::decode` at `UntypedRetype` with ≥ 6 message words, a non-empty
  first extra slot, MR0 ∈ 14..18 and `virtualization() = 0` returns `InvalidArgument 0`, state unchanged.
* `decV_untyped_gate`: when `untypedVtxGate` holds the extended decoder's single outcome is
  `error (invalidArgument 0)`, state unchanged.
* `decOKV_untyped_vtxGate`: so FL4's dispatcher satisfies `DecOKV` (`VirtTopV`) on these inputs.

Premises (named hypotheses): `hct`, `hlen` / `h6` / `hargs` (the message words, as `untyped_decode_refines_fl4`),
`hx0` / `hex` / `hx0n` (`ExtraSRel`, a non-empty first extra slot), `hnt` / `hlo` / `hhi` (MR0 a VT-x type),
`hlbl` (spec label `UntypedRetype`), `hvk` (the route's scope: `virtKind = none`) and
`hvirt` [P] (the platform agreement `Arch::virtualization() = virtKind.code`, VIRT-PLAN §11.1: FL4's
`virtualization()` is 0 when `virtKind = none`). No [J]/[W]. New file only.
-/
import Fl4Proofs.P3.VirtTopV
import Fl4Proofs.P3.UntypedDecode
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-- The extended decoder on an untyped cap when the VT-x gate holds. -/
theorem decV_untyped_gate {fp : Bool} {slbl : Fl4Spec.Data} {args : List Fl4Spec.Data} {ci : Fl4Spec.CapRef}
    {sl : Fl4Spec.CslotPtr} {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)} {buffer : Option Fl4Spec.ObjRef}
    {dev : Bool} {p : Fl4Spec.ObjRef} {sb fi : Nat}
    (hg : Fl4Spec.untypedVtxGate slbl args (excaps.map Prod.fst)) (σ : Fl4Spec.State Unit) :
    (Fl4Spec.fl4DecodeInvocationV (Z := Unit) fp slbl args ci sl (.untypedCap dev p sb fi) excaps buffer).run σ =
      ({(.error (.invalidArgument 0), σ)}, False) := by
  unfold Fl4Spec.fl4DecodeInvocationV
  dsimp only
  rw [if_pos hg]
  rfl

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- FL4's dispatcher on an Untyped cap is `untyped::decode`. -/
theorem decode_invocation_untyped_eq (s : S) (ar : A) (lbl length slot : U64) (p sb fi : U64) (dev : Bool)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ct : U64)
    (hct : sched.cur_thread st s = ok ct) :
    syscall.decode_invocation st arI s ar lbl length slot (.Untyped p sb fi dev) blk call don fp buf extra =
      untyped.decode st arI s ar lbl length slot (.Untyped p sb fi dev) buf extra := by
  unfold syscall.decode_invocation
  rw [hct]; simp only [bind_ok]

/-- **FL4's VT-x retype gate** (`untyped.rs:42-44`; module docstring). -/
theorem untyped_decode_vtx_gate (s : S) (ar : A) (length slot : U64) (p sb fi : U64) (dev : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (args : List U64) (hlen : length.val = args.length) (h6 : 6 ≤ args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0) (hx0n : x0 ≠ 0#u64)
    (nt : U64) (hnt : args.head? = some nt) (hlo : 14 ≤ nt.val) (hhi : nt.val < 19)
    (hvirt : arI.virtualization ar = ok 0#u64) :
    untyped.decode st arI s ar fl4_abi.label.UntypedRetype length slot (.Untyped p sb fi dev) buf extra =
      ok (.Err (.Sys (.InvalidArgument 0#u64)), s, ar) := by
  obtain ⟨nt', us, idx, dep, off, win, rest, rfl⟩ : ∃ nt us idx dep off win rest,
      args = nt :: us :: idx :: dep :: off :: win :: rest := by
    match args with
    | nt :: us :: idx :: dep :: off :: win :: rest => exact ⟨nt, us, idx, dep, off, win, rest, rfl⟩
    | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] => exfalso; simp at h6
  simp only [List.head?_cons, Option.some.injEq] at hnt
  subst hnt
  have h6' : ¬ length < 6#u64 := by simp at hlen; scalar_tac
  have hg : nt' ≥ 14#u64 := by scalar_tac
  have hl : nt' < 19#u64 := by scalar_tac
  unfold untyped.decode
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, h6', hx0, bind_ok, obj.Slot.is_null]
  simp only [hx0n, decide_false, Bool.false_eq_true, ↓reduceIte, hct, hargs 0#u64 nt' (by simp),
    hargs 1#u64 us (by simp), hargs 2#u64 idx (by simp), hargs 3#u64 dep (by simp), hargs 4#u64 off (by simp),
    hargs 5#u64 win (by simp), bind_ok]
  simp only [fl4_abi.consts.object.X86Vcpu, fl4_abi.consts.object.Count, hg, hl, ↓reduceIte, hvirt, bind_ok,
    error.invalid_arg]

/-- **The VT-x retype gate at the dispatcher, posted against the extended kernel** (module docstring). -/
theorem decOKV_untyped_vtxGate (onCore : Fl4Spec.ObjRef → Bool) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (length slot : U64) (p sb fi : U64) (dev : Bool) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (args : List U64) (hlen : length.val = args.length) (h6 : 6 ≤ args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (th : TypedHeap) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0) (hx0n : x0 ≠ 0#u64)
    (cps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraSRel th (L.mem s) x0 cps)
    (nt : U64) (hnt : args.head? = some nt) (hlo : 14 ≤ nt.val) (hhi : nt.val < 19)
    (hvirt : arI.virtualization ar = ok 0#u64) (hvk : Fl4Spec.virtKind = .none)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .untypedRetype)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (buffer : Option Fl4Spec.ObjRef) :
    DecOKV (L := L) arI onCore s ar σ fl4_abi.label.UntypedRetype length slot (.Untyped p sb fi dev) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci sl cps buffer := by
  have hne : cps.map Prod.fst ≠ [] := by
    rcases hex with ⟨h0, -⟩ | ⟨-, ps, rs, idxs, rest, -, -, -, rfl⟩
    · exact absurd h0 hx0n
    · simp
  have hvt : Fl4Spec.isVtxObjectTypeNum (Fl4Spec.dataToNat ((args.map UScalar.bv).getD 0 0)) = true := by
    cases args with
    | nil => simp at hnt
    | cons a tl =>
      simp only [List.head?_cons, Option.some.injEq] at hnt
      subst hnt
      show decide (14 ≤ a.val ∧ a.val ≤ 18) = true
      simp only [decide_eq_true_eq]
      omega
  have hgate : Fl4Spec.untypedVtxGate slbl (args.map UScalar.bv) (cps.map Prod.fst) :=
    ⟨hlbl, by simpa using h6, hne, hvt, hvk⟩
  unfold DecOKV
  rw [decode_invocation_untyped_eq arI s ar _ length slot p sb fi dev blk call don fp buf extra ct hct,
    untyped_decode_vtx_gate arI s ar length slot p sb fi dev buf extra ct hct args hlen h6 hargs x0 hx0 hx0n nt hnt
      hlo hhi hvirt, WP.spec_ok]
  exact Or.inl ⟨_, rfl, rfl, .invalidArgument 0, decV_untyped_gate hgate σ,
    Or.inl (show (0 : Nat) = (0#u64 : U64).val from rfl)⟩

end

end

end Fl4Proofs.P3
