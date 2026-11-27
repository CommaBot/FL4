/-
P3 against the virtualization extension (line virt, gen 3; proofs/VIRT-PLAN.md §10 R7, route B):
**FL4's `X86PageMapEPT` (label 60) error chain refines the extended decoder**.

FL4 source: `crates/fl4-core/src/ept.rs:24-42` (`ept::root`) and `ept.rs:119-160` (`ept::map_frame`), reached
from `syscall::decode_invocation` (Frame cap) → `vspace::decode` → `vspace::decode_frame` (`arch/x86_64/vspace.rs`,
label `X86PageMapEPT`). Spec: `Fl4Spec/Ext/VirtDispatch` (`fl4DecodeInvocationV`, page caps at label
`fl4PageMapEptLabel` = 60) and `Fl4Spec/Ext/VirtEptInv` (`decodePageMapEpt`, `eptCapRoot`), extending l4v
`Decode_A.decode_invocation` / `Arch_A.arch_decode_invocation` (ported as `fl4DecodeInvocation`, where label 60
is the ported x86 decoder's) after FL4's `map_frame` order.

The checks agree in order: length < 3 or an empty first extra slot (`TruncatedMessage`), the page-rounded gpa at or
above `ept::LIMIT` = 2^47 (`InvalidArgument 0`), a mapped frame (`InvalidCapability 0`), a first extra cap that is
not a mapped level-0 EPT cap (`InvalidCapability 1`, `ept::root` / `eptCapRoot`).

* `ept_limit_eq`, `gpa_ge_iff`: the gpa-limit bridge (`ept::LIMIT` as a U64, FL4's `≥` on U64 against the spec's
  on `BitVec 64`, `(a &&& ~~~4095).bv = a.bv &&& ~~~4095`).
* `ept_root_nonEpt`: `ept::root` of a cap that is not a mapped level-0 EPT cap is `InvalidCapability 1`;
  `eptCapRoot_bad`: the spec's likewise.
* `decV_frame60`: the extended decoder of a page cap at label 60 is `decodePageMapEpt`.
* `map_frame_err`: when the first extra slot is empty or not an EPT root, FL4's `map_frame` returns an error with
  the store and arch state unchanged, and `decodePageMapEpt` has the single outcome `error e'`, `ErrRel e e'`.
* `decode_invocation_frame60_eq`: FL4's dispatcher on a Frame cap at `X86PageMapEPT` is `ept::map_frame`.
* `decOKV_frame60`, **`decOKV_frame60_noVirt`**: FL4's dispatcher at label 60 satisfies `DecOKV` (`VirtTopV`)
  whenever the first extra cap is not an EPT root, in particular whenever the first spec extra cap is not a
  virtualization cap (`IsVirtCap`; so on every `NoVirtCaps` state, where the success side is vacuous).

Premises (named hypotheses): `hct` (`cur_thread` reads), `hlen` / `hargs` (the message words, as
`untyped_decode_refines_fl4`), `hx0` / `hex` (`ExtraSRel`), `hl` (spec label 60), `hbad` / `hnv` (the first extra
cap is not an EPT root / not a virtualization cap: a state fact of `NoVirtCaps`). No [J], no [P], no [W].
New file only.
-/
import Fl4Proofs.P3.VirtTopV
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-! ## The gpa-limit bridge -/

/-- `ept::LIMIT` as a word. -/
theorem ept_limit_eq : ept.LIMIT = ok ⟨(1 : BitVec 64) <<< 47⟩ := by
  unfold ept.LIMIT
  rw [shl_eq _ _ (by decide) (by decide)]
  rfl

/-- **The gpa-limit bridge**: FL4's test `(a & !4095) >= LIMIT` on U64 is the spec's
`args[0] &&& ~~~4095 ≥ guestGpaLimit` on `BitVec 64`. -/
theorem gpa_ge_iff (a : U64) :
    ((a &&& ~~~4095#u64) ≥ (⟨(1 : BitVec 64) <<< 47⟩ : U64)) ↔
      (a.bv &&& ~~~(4095 : Fl4Spec.Word) ≥ Fl4Spec.guestGpaLimit) := by
  have hb : (a &&& ~~~4095#u64).bv = a.bv &&& ~~~(4095 : Fl4Spec.Word) := by
    rw [UScalar.bv_and, UScalar.bv_not]; rfl
  rw [GE.ge, GE.ge, BitVec.le_def, UScalar.le_equiv, ← hb]
  rfl

/-! ## Spec side -/

/-- A local copy of `run_whenE_throw` (XTopTcbBp, not upstream). -/
theorem run_whenE_throwV {β : Type} (P : Prop) [Decidable P] (e : Fl4Spec.SyscallError)
    (k : Unit → Fl4Spec.SEMonad Unit β) (σ : Fl4Spec.State Unit) :
    ((Fl4Spec.NonDetE.whenE P (Fl4Spec.NonDetE.throwError e) : Fl4Spec.SEMonad Unit Unit) >>= k).run σ =
      if P then ({(.error e, σ)}, False) else (k ()).run σ := by
  by_cases h : P
  · rw [whenE_pos h, if_pos h]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError e : Fl4Spec.SEMonad Unit Unit)) rfl _
  · rw [whenE_neg h, if_neg h]
    exact run_bind_ok (m := (Fl4Spec.NonDetE.returnOk () : Fl4Spec.SEMonad Unit Unit)) rfl _

/-- The extended decoder of a page cap at label 60 is `decodePageMapEpt`. -/
theorem decV_frame60 {slbl : Fl4Spec.Data} (hl : Fl4Spec.dataToNat slbl = Fl4Spec.fl4PageMapEptLabel) (fp : Bool)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (dev : Bool) (p : Fl4Spec.ObjRef)
    (R : Fl4Spec.VMRights) (mt : Fl4Spec.VMMapType) (sz : Fl4Spec.VMPageSize) (m : Option (Fl4Spec.Asid × Fl4Spec.Word))
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) :
    Fl4Spec.fl4DecodeInvocationV (Z := Unit) fp slbl args ci sl (.archObjectCap (.pageCap dev p R mt sz m)) excaps
      buffer = Fl4Spec.NonDetE.liftME Fl4Spec.Fl4InvocationV.ept
        (Fl4Spec.decodePageMapEpt args sl (.pageCap dev p R mt sz m) excaps) := by
  unfold Fl4Spec.fl4DecodeInvocationV
  dsimp only
  rw [if_pos hl]

/-- The spec's `eptCapRoot` of a cap that is not a mapped level-0 EPT cap. -/
theorem eptCapRoot_bad {c : Fl4Spec.Cap} (h : ∀ q m, c ≠ .archObjectCap (.eptCap q 0 (some m)))
    (σ : Fl4Spec.State Unit) :
    (Fl4Spec.eptCapRoot (Z := Unit) c).run σ = ({(.error (.invalidCapability 1), σ)}, False) := by
  simp only [Fl4Spec.eptCapRoot]
  first
    | rfl
    | (split
       · exact absurd rfl (h _ _)
       · rfl)

/-! ## FL4 side -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`ept::root` of a cap that is not a mapped level-0 EPT cap** is `InvalidCapability 1` (`ept.rs:35-40`). -/
theorem ept_root_nonEpt (s : S) {c : capability.Cap} (h : ¬ EptRootC c) :
    ept.root st s c = ok (.Err (.Sys (.InvalidCapability 1#u64))) := by
  cases c with
  | Ept q i b asid va =>
    by_cases hroot : i = 0#u64 ∧ b = true
    · obtain ⟨rfl, rfl⟩ := hroot
      exact absurd ⟨q, asid, va, rfl⟩ h
    · unfold ept.root
      simp only [error.invalid_cap]
      split
      all_goals first
        | rfl
        | (cases b
           · simp only [Bool.false_eq_true, ↓reduceIte]
           · exfalso
             first
               | exact hroot ⟨rfl, rfl⟩
               | (rename_i heq; exact hroot ⟨UScalar.eq_of_val_eq (by rw [heq]; rfl), rfl⟩)
               | simp_all)
  | _ => simp only [ept.root, error.invalid_cap]

/-- FL4's dispatcher on a Frame cap at `X86PageMapEPT` is `ept::map_frame`. -/
theorem decode_invocation_frame60_eq (s : S) (ar : A) (length slot : U64) (p : U64) (sz : capability.FrameSize)
    (rt : U64) (d m ie : Bool) (asid va : U64) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (ct : U64) (hct : sched.cur_thread st s = ok ct) :
    syscall.decode_invocation st arI s ar fl4_abi.label.X86PageMapEPT length slot (.Frame p sz rt d m ie asid va)
        blk call don fp buf extra =
      ept.map_frame st arI s ar length (.Frame p sz rt d m ie asid va) slot buf extra := by
  unfold syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  unfold vspace.decode
  rw [hct]; simp only [bind_ok]
  unfold vspace.decode_frame
  simp only [vspace.as_frame, bind_ok, ↓reduceIte]

/-- The spec cap of an FL4 frame cap (`absCap`'s frame case). -/
abbrev frameACapV (p : U64) (sz : capability.FrameSize) (rt : U64) (d m ie : Bool) (asid va : U64) :
    Fl4Spec.ArchCap :=
  .pageCap d p.bv (vmRightsOf rt) (if m then (if ie then .vmEptMap else .vmVSpaceMap) else .vmNoMap)
    (frameSizeOf sz) (if m then some (asid.bv, va.bv) else none)

/-- **Label 60, error side** (module docstring). -/
theorem map_frame_err (s : S) (ar : A) (σ : Fl4Spec.State Unit) (length slot : U64) (p : U64)
    (sz : capability.FrameSize) (rt : U64) (d m ie : Bool) (asid va : U64) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (th : TypedHeap) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (cps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraSRel th (L.mem s) x0 cps)
    (hbad : x0 = 0#u64 ∨ ¬ EptRootC (capV (L.mem s) x0)) (sl : Fl4Spec.CslotPtr) :
    ∃ e, ept.map_frame st arI s ar length (.Frame p sz rt d m ie asid va) slot buf extra = ok (.Err e, s, ar) ∧
      ∃ e', (Fl4Spec.decodePageMapEpt (Z := Unit) (args.map UScalar.bv) sl (frameACapV p sz rt d m ie asid va)
          cps).run σ = ({(.error e', σ)}, False) ∧ ErrRel e e' := by
  by_cases h3 : length < 3#u64
  · refine ⟨.Sys .TruncatedMessage, ?_, .truncatedMessage, ?_, Or.inl trivial⟩
    · unfold ept.map_frame
      simp only [h3, ↓reduceIte, error.truncated, bind_ok]
    · have : (args.map UScalar.bv).length < 3 := by
        simp only [List.length_map, ← hlen]; scalar_tac
      unfold Fl4Spec.decodePageMapEpt
      rw [if_pos (Or.inl this)]; rfl
  rcases hex with ⟨rfl, rfl⟩ | ⟨hx0n, ps, rs, idxs, rest, -, -, -, rfl⟩
  · refine ⟨.Sys .TruncatedMessage, ?_, .truncatedMessage, ?_, Or.inl trivial⟩
    · unfold ept.map_frame
      simp only [h3, ↓reduceIte, hx0, is_null_eq, decide_true, error.truncated, bind_ok]
    · unfold Fl4Spec.decodePageMapEpt
      rw [if_pos (Or.inr rfl)]; rfl
  obtain ⟨a0, a1, a2, rest', rfl⟩ : ∃ a0 a1 a2 rest', args = a0 :: a1 :: a2 :: rest' := by
    match args, hlen with
    | a0 :: a1 :: a2 :: rest', _ => exact ⟨a0, a1, a2, rest', rfl⟩
    | [], h | [_], h | [_, _], h => exfalso; simp at h; scalar_tac
  have hntr : ¬ ((List.map UScalar.bv (a0 :: a1 :: a2 :: rest')).length < 3 ∨
      ((absCap (capV (L.mem s) x0), (ps.bv, idxs)) :: rest) = []) := by simp
  have hs0 := hargs 0#u64 a0 (by simp)
  have hs1 := hargs 1#u64 a1 (by simp)
  have hs2 := hargs 2#u64 a2 (by simp)
  by_cases hg : (a0 &&& ~~~4095#u64) ≥ (⟨(1 : BitVec 64) <<< 47⟩ : U64)
  · refine ⟨.Sys (.InvalidArgument 0#u64), ?_, .invalidArgument 0, ?_,
      Or.inl (show (0 : Nat) = (0#u64 : U64).val from rfl)⟩
    · unfold ept.map_frame
      simp only [h3, ↓reduceIte, hx0, is_null_eq, hx0n, decide_false, Bool.false_eq_true, hct, hs0, lift,
        bind_ok, ept_limit_eq, hg, error.invalid_arg]
    · unfold Fl4Spec.decodePageMapEpt
      rw [if_neg hntr]
      rw [run_whenE_throwV]
      split
      · rfl
      · rename_i h; exact absurd ((gpa_ge_iff a0).1 hg) h
  have hb : ¬ EptRootC (capV (L.mem s) x0) := hbad.resolve_left hx0n
  cases m
  · refine ⟨.Sys (.InvalidCapability 1#u64), ?_, .invalidCapability 1, ?_, Or.inr ⟨1#u64, rfl, rfl⟩⟩
    · unfold ept.map_frame
      simp only [h3, ↓reduceIte, hx0, is_null_eq, hx0n, decide_false, Bool.false_eq_true, hct, hs0, hs1, hs2, lift,
        bind_ok, ept_limit_eq, hg, slot_cap_eq, capAt_capV, ept_root_nonEpt (st := st) s hb,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
        core.convert.FromSame.from, bind_tc_ok]
    · unfold Fl4Spec.decodePageMapEpt
      rw [if_neg hntr]
      rw [run_whenE_throwV]
      split
      · rename_i h; exact (hg ((gpa_ge_iff a0).2 h)).elim
      simp only [frameACapV, Bool.false_eq_true, ↓reduceIte, Fl4Spec.the]
      exact run_bind_error (eptCapRoot_bad (absCap_not_eptRoot hb) σ) _
  · refine ⟨.Sys (.InvalidCapability 0#u64), ?_, .invalidCapability 0, ?_, Or.inr ⟨0#u64, rfl, rfl⟩⟩
    · unfold ept.map_frame
      simp only [h3, ↓reduceIte, hx0, is_null_eq, hx0n, decide_false, Bool.false_eq_true, hct, hs0, hs1, hs2, lift,
        bind_ok, ept_limit_eq, hg, error.invalid_cap]
    · unfold Fl4Spec.decodePageMapEpt
      rw [if_neg hntr]
      rw [run_whenE_throwV]
      split
      · rename_i h; exact (hg ((gpa_ge_iff a0).2 h)).elim
      simp only [frameACapV, ↓reduceIte]
      rfl

/-- **Label 60 at the dispatcher, posted against the extended kernel** (module docstring). -/
theorem decOKV_frame60 (onCore : Fl4Spec.ObjRef → Bool) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (length slot : U64) (p : U64) (sz : capability.FrameSize) (rt : U64) (d m ie : Bool) (asid va : U64)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ct : U64)
    (hct : sched.cur_thread st s = ok ct) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (th : TypedHeap) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (cps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraSRel th (L.mem s) x0 cps)
    (hbad : x0 = 0#u64 ∨ ¬ EptRootC (capV (L.mem s) x0))
    (slbl : Fl4Spec.Data) (hl : Fl4Spec.dataToNat slbl = Fl4Spec.fl4PageMapEptLabel)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (buffer : Option Fl4Spec.ObjRef) :
    DecOKV (L := L) arI onCore s ar σ fl4_abi.label.X86PageMapEPT length slot (.Frame p sz rt d m ie asid va)
      blk call don fp buf extra slbl (args.map UScalar.bv) ci sl cps buffer := by
  obtain ⟨e, h1, e', h2, h3⟩ := map_frame_err arI s ar σ length slot p sz rt d m ie asid va buf extra ct hct
    args hlen hargs th x0 hx0 cps hex hbad sl
  unfold DecOKV
  rw [decode_invocation_frame60_eq arI s ar length slot p sz rt d m ie asid va blk call don fp buf extra ct hct,
    h1, WP.spec_ok]
  refine Or.inl ⟨e, rfl, rfl, e', ?_, h3⟩
  show (Fl4Spec.fl4DecodeInvocationV (Z := Unit) fp slbl (args.map UScalar.bv) ci sl
    (.archObjectCap (frameACapV p sz rt d m ie asid va)) cps buffer).run σ = _
  rw [decV_frame60 hl]
  exact run_liftME_err h2

/-- **Label 60 on a state without virtualization caps**: `DecOKV` holds whenever the first spec extra cap
is not a virtualization cap. -/
theorem decOKV_frame60_noVirt (onCore : Fl4Spec.ObjRef → Bool) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (length slot : U64) (p : U64) (sz : capability.FrameSize) (rt : U64) (d m ie : Bool) (asid va : U64)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ct : U64)
    (hct : sched.cur_thread st s = ok ct) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (th : TypedHeap) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (cps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraSRel th (L.mem s) x0 cps)
    (hnv : ∀ x ∈ cps.head?, ¬ Fl4Spec.IsVirtCap x.1)
    (slbl : Fl4Spec.Data) (hl : Fl4Spec.dataToNat slbl = Fl4Spec.fl4PageMapEptLabel)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (buffer : Option Fl4Spec.ObjRef) :
    DecOKV (L := L) arI onCore s ar σ fl4_abi.label.X86PageMapEPT length slot (.Frame p sz rt d m ie asid va)
      blk call don fp buf extra slbl (args.map UScalar.bv) ci sl cps buffer := by
  have hbad : x0 = 0#u64 ∨ ¬ EptRootC (capV (L.mem s) x0) := by
    by_cases h0 : x0 = 0#u64
    · exact Or.inl h0
    · right
      intro hr
      rcases hex with ⟨h0', -⟩ | ⟨-, ps, rs, idxs, rest, -, -, -, rfl⟩
      · exact h0 h0'
      · exact hnv _ rfl (eptRootC_virt hr)
  exact decOKV_frame60 arI onCore s ar σ length slot p sz rt d m ie asid va blk call don fp buf extra ct hct
    args hlen hargs th x0 hx0 cps hex hbad slbl hl ci sl buffer

end

end

end Fl4Proofs.P3
