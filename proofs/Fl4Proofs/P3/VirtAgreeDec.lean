/-
P3x for virtualization (line virt, gen 7, item 1): **on a route-B decode point, U36I's own leaf forces the two
decoders to agree.**

U36I's syscall clause (XTopJointKEntryU36I, via `KDispHypsKVU32` → `JPathAtMU30`) asks at the invoked slot of
each of the three routes the leaf `JVtxScope … = XCapP X XP …` (XTopJointEntry): FL4's `decode_invocation` against
the **ported** decoder (`specDec`). Route B (VirtSetEptDec / VirtFrame60 / VirtUtGate) computes FL4's result there
on an `NR` state: an error `Err e` with the store kept, and the **extended** decoder's single error `e'` with
`ErrRel e e'`. FL4's result is one value, `ErrRel` is functional (`errRel_unique`), so wherever the leaf holds the
ported decoder has the same single error: `VirtAgree.ErrAgree` holds at that point. So the one thing VirtAgree's
widened scope `ScopeE6` [S] still excludes — an on-route point where the decoders differ — is a point where U36I's
own premise is false.

* `lookupFaultRel_unique`, `sysErrRel_unique`, **`errRel_unique`**, `errRel_not_preempted`.
* **`ported_err_of_xcap`**: `XCapP` (either disjunct: `DecOKDMXP`, `DecOKRMX`) + FL4's decode returning
  `Err e` (store kept) + `ErrRel e e'` ⇒ the ported decoder's run is `{(error e', σ)}`.
* Route B with FL4's result made explicit: `thread88_err`, `frame60_err`, `untypedGate_err`.
* **`agree_thread88`**, **`agree_frame60`**, **`agree_untypedGate`**: the leaf ⇒ both decoders give the same
  single error (`DecAgreeAt`); `errAgree_of` turns that into `VirtAgree.ErrAgree` at the matching decode point.

Named premises (as the route-B lemmas they reuse; none new): `hstall` [J] (label 88: the target's stall is a
no-op, as `tcb_decode_refines`; at a `JAtZ` state it is `JAtZ.stallT` for a thread of `Z.T`), `hct`, the
message-word relations (`hlen` / `hargs` / `h6`), `ExtraSRel` (`hx0` / `hex`, plus `hx0n` for the gate), the spec
label (`hl` / `hlbl`), `hnv` (the first spec extra cap is not a virtualization cap: every `NVC` state), the gate's
MR0 range, **`hvirt` [P]** (gen 2's, `Arch::virtualization() = 0`, untouched) and **`hvk : virtKind = .none`
[S]** for the gate. No [W]. New file only.
-/
import Fl4Proofs.P3.VirtAgree
import Fl4Proofs.P3.VirtFrame60
import Fl4Proofs.P3.VirtUtGate
import Fl4Proofs.P3.XTopJointEntry
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-! ## `ErrRel` is functional -/

theorem lookupFaultRel_unique {lf : error.LookupFault} {l1 l2 : Fl4Spec.LookupFailure}
    (h1 : LookupFaultRel lf l1) (h2 : LookupFaultRel lf l2) : l1 = l2 := by
  cases lf <;> cases l1 <;> (try exact (h1 : False).elim) <;> cases l2 <;> (try exact (h2 : False).elim) <;>
    simp only [LookupFaultRel] at h1 h2 <;> simp_all

theorem sysErrRel_unique {e : error.Exc} {e1 e2 : Fl4Spec.SyscallError}
    (h1 : SysErrRel e e1) (h2 : SysErrRel e e2) : e1 = e2 := by
  rcases e with f | l | x | _
  · cases e1 <;> exact (h1 : False).elim
  · cases e1 <;> exact (h1 : False).elim
  · cases x <;> cases e1 <;> (try exact (h1 : False).elim) <;> cases e2 <;> (try exact (h2 : False).elim) <;>
      simp only [SysErrRel] at h1 h2
    all_goals first
      | rfl
      | (obtain ⟨rfl, ha⟩ := h1; obtain ⟨hb1, hb⟩ := h2; subst hb1; rw [lookupFaultRel_unique ha hb])
      | simp_all
  · cases e1 <;> exact (h1 : False).elim

/-- **`ErrRel` is functional** (module docstring). -/
theorem errRel_unique {e : error.Exc} {e1 e2 : Fl4Spec.SyscallError} (h1 : ErrRel e e1) (h2 : ErrRel e e2) :
    e1 = e2 := by
  rcases h1 with h1 | ⟨n, rfl, rfl⟩ <;> rcases h2 with h2 | ⟨m, hm, rfl⟩
  · exact sysErrRel_unique h1 h2
  · subst hm; cases e1 <;> exact (h1 : False).elim
  · cases e2 <;> exact (h2 : False).elim
  · cases hm; rfl

theorem errRel_not_preempted {e' : Fl4Spec.SyscallError} : ¬ ErrRel .Preempted e' := by
  rintro (h | ⟨n, h, -⟩)
  · cases e' <;> exact (h : False).elim
  · cases h

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-! ## The leaf against FL4's error -/

/-- **The ported leaf `XCapP` at a point where FL4's decode errs**: the ported decoder has the related error,
which is the extended one's (module docstring). -/
theorem ported_err_of_xcap {X XP : S → A → Fl4Spec.State Unit → Prop} {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    {lbl length slot : U64} {c : capability.Cap} {blk call don fp : Bool} {buf : U64}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {slbl : Fl4Spec.Data} {args : List Fl4Spec.Data}
    {ci : Fl4Spec.CapRef} {sl : Fl4Spec.CslotPtr} {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    {buffer : Option Fl4Spec.ObjRef} {ct : U64} {e : error.Exc} {e' : Fl4Spec.SyscallError}
    (hX : XCapP (L := L) arI X XP s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer ct)
    (hF : syscall.decode_invocation st arI s ar lbl length slot c blk call don fp buf extra = ok (.Err e, s, ar))
    (hR : ErrRel e e') :
    (specDec fp slbl args ci sl c excaps buffer).run σ = ({(.error e', σ)}, False) := by
  rcases hX with h | h
  · unfold DecOKDMXP at h
    rw [hF, WP.spec_ok] at h
    unfold TopPostDMXP TopPostDMX at h
    rcases h with ⟨e0, h1, -, ⟨e'', h3, h4⟩, -⟩ | ⟨inv, -, σ1, -, y, -, ⟨th', G', hc, -⟩, -⟩
    · have h1' : (core.result.Result.Err e : core.result.Result Unit error.Exc) = .Err e0 := h1
      injection h1' with h1''
      subst h1''
      rw [h3, errRel_unique h4 hR]
    · exfalso
      rcases hc with ⟨hc, -⟩ | ⟨hc, -⟩
      · have hc' : (core.result.Result.Err e : core.result.Result Unit error.Exc) = .Ok () := hc
        cases hc'
      · have hc' : (core.result.Result.Err e : core.result.Result Unit error.Exc) = .Err .Preempted := hc
        injection hc' with hc''
        subst hc''
        exact errRel_not_preempted hR
  · unfold DecOKRMX at h
    rw [hF, WP.spec_ok] at h
    unfold TopPostRMX at h
    rcases h with ⟨e0, h1, -, ⟨e'', h3, h4⟩, -⟩ | ⟨hc, -⟩
    · have h1' : (core.result.Result.Err e : core.result.Result Unit error.Exc) = .Err e0 := h1
      injection h1' with h1''
      subst h1''
      rw [h3, errRel_unique h4 hR]
    · exfalso
      have hc' : (core.result.Result.Err e : core.result.Result Unit error.Exc) = .Ok () := hc
      cases hc'

/-- Both decoders give the same single error at the spec inputs of a FL4 decode. -/
def DecAgreeAt (fp : Bool) (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (c : capability.Cap) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) (σ : Fl4Spec.State Unit) : Prop :=
  ∃ e', (specDec fp slbl args ci sl c excaps buffer).run σ = ({(.error e', σ)}, False) ∧
    (specDecV fp slbl args ci sl c excaps buffer).run σ = ({(.error e', σ)}, False)

/-- `DecAgreeAt` is VirtAgree's `ErrAgree` at the matching decode point. -/
theorem errAgree_of {fp : Bool} {slbl : Fl4Spec.Data} {args : List Fl4Spec.Data} {ci : Fl4Spec.CapRef}
    {sl : Fl4Spec.CslotPtr} {c : capability.Cap} {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    {buffer : Option Fl4Spec.ObjRef} {σ : Fl4Spec.State Unit} {info : Fl4Spec.MessageInfo}
    (hi : info.miLabel = slbl) (h : DecAgreeAt fp slbl args ci sl c excaps buffer σ) :
    VirtAgree.ErrAgree fp ci info (sl, absCap c, excaps, buffer) args σ := by
  subst hi
  exact h

/-! ## Route B with FL4's result explicit -/

theorem thread88_err (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (length slot : U64) (p : U64) (blk call don : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (th : TypedHeap) (x0 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (cps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraSRel th (L.mem s) x0 cps)
    (hnv : ∀ x ∈ cps.head?, ¬ Fl4Spec.IsVirtCap x.1)
    (slbl : Fl4Spec.Data) (hl : Fl4Spec.dataToNat slbl = Fl4Spec.fl4SetEptRootLabel) (args : List Fl4Spec.Data)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (buffer : Option Fl4Spec.ObjRef) :
    ∃ e, syscall.decode_invocation st arI s ar fl4_abi.label.TCBSetEPTRoot length slot (.Thread p) blk call don
        false buf extra = ok (.Err e, s, ar) ∧
      ∃ e', (specDecV false slbl args ci sl (.Thread p) cps buffer).run σ = ({(.error e', σ)}, False) ∧
        ErrRel e e' := by
  have hbad : x0 = 0#u64 ∨ ¬ EptRootC (capV (L.mem s) x0) := by
    by_cases h0 : x0 = 0#u64
    · exact Or.inl h0
    · right
      intro hr
      rcases hex with ⟨h0', -⟩ | ⟨-, ps, rs, idxs, rest, -, -, -, rfl⟩
      · exact h0 h0'
      · exact hnv _ rfl (eptRootC_virt hr)
  obtain ⟨e, h1, e', h2, h3⟩ := setEptRoot_decode_err arI s ar σ p ⟨length, buf, call, slot, extra⟩ hstall th x0
    hx0 cps hex hbad slbl hl args ci sl buffer
  refine ⟨e, ?_, e', h2, h3⟩
  rw [decode_invocation_thread_eq arI s ar _ length slot p blk call don buf extra ct hct]
  exact h1

theorem frame60_err (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (length slot : U64) (p : U64) (sz : capability.FrameSize) (rt : U64) (d m ie : Bool) (asid va : U64)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ct : U64)
    (hct : sched.cur_thread st s = ok ct) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (th : TypedHeap) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (cps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraSRel th (L.mem s) x0 cps)
    (hnv : ∀ x ∈ cps.head?, ¬ Fl4Spec.IsVirtCap x.1)
    (slbl : Fl4Spec.Data) (hl : Fl4Spec.dataToNat slbl = Fl4Spec.fl4PageMapEptLabel)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (buffer : Option Fl4Spec.ObjRef) :
    ∃ e, syscall.decode_invocation st arI s ar fl4_abi.label.X86PageMapEPT length slot
        (.Frame p sz rt d m ie asid va) blk call don fp buf extra = ok (.Err e, s, ar) ∧
      ∃ e', (specDecV fp slbl (args.map UScalar.bv) ci sl (.Frame p sz rt d m ie asid va) cps buffer).run σ =
        ({(.error e', σ)}, False) ∧ ErrRel e e' := by
  have hbad : x0 = 0#u64 ∨ ¬ EptRootC (capV (L.mem s) x0) := by
    by_cases h0 : x0 = 0#u64
    · exact Or.inl h0
    · right
      intro hr
      rcases hex with ⟨h0', -⟩ | ⟨-, ps, rs, idxs, rest, -, -, -, rfl⟩
      · exact h0 h0'
      · exact hnv _ rfl (eptRootC_virt hr)
  obtain ⟨e, h1, e', h2, h3⟩ := map_frame_err arI s ar σ length slot p sz rt d m ie asid va buf extra ct hct
    args hlen hargs th x0 hx0 cps hex hbad sl
  refine ⟨e, ?_, e', ?_, h3⟩
  · rw [decode_invocation_frame60_eq arI s ar length slot p sz rt d m ie asid va blk call don fp buf extra ct hct]
    exact h1
  · show (Fl4Spec.fl4DecodeInvocationV (Z := Unit) fp slbl (args.map UScalar.bv) ci sl
      (.archObjectCap (frameACapV p sz rt d m ie asid va)) cps buffer).run σ = _
    rw [decV_frame60 hl]
    exact run_liftME_err h2

theorem untypedGate_err (s : S) (ar : A) (σ : Fl4Spec.State Unit)
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
    ∃ e, syscall.decode_invocation st arI s ar fl4_abi.label.UntypedRetype length slot (.Untyped p sb fi dev)
        blk call don fp buf extra = ok (.Err e, s, ar) ∧
      ∃ e', (specDecV fp slbl (args.map UScalar.bv) ci sl (.Untyped p sb fi dev) cps buffer).run σ =
        ({(.error e', σ)}, False) ∧ ErrRel e e' := by
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
  refine ⟨.Sys (.InvalidArgument 0#u64), ?_, .invalidArgument 0, decV_untyped_gate hgate σ,
    Or.inl (show (0 : Nat) = (0#u64 : U64).val from rfl)⟩
  rw [decode_invocation_untyped_eq arI s ar _ length slot p sb fi dev blk call don fp buf extra ct hct,
    untyped_decode_vtx_gate arI s ar length slot p sb fi dev buf extra ct hct args hlen h6 hargs x0 hx0 hx0n nt hnt
      hlo hhi hvirt]

/-! ## The leaf forces agreement -/

/-- **Label 88**: U36I's leaf at a thread cap ⇒ both decoders give the same single error. -/
theorem agree_thread88 {X XP : S → A → Fl4Spec.State Unit → Prop} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (length slot : U64) (p : U64) (blk call don : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (th : TypedHeap) (x0 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (cps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraSRel th (L.mem s) x0 cps)
    (hnv : ∀ x ∈ cps.head?, ¬ Fl4Spec.IsVirtCap x.1)
    (slbl : Fl4Spec.Data) (hl : Fl4Spec.dataToNat slbl = Fl4Spec.fl4SetEptRootLabel) (args : List Fl4Spec.Data)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (buffer : Option Fl4Spec.ObjRef)
    (hX : XCapP (L := L) arI X XP s ar σ fl4_abi.label.TCBSetEPTRoot length slot (.Thread p) blk call don false buf
      extra slbl args ci sl cps buffer ct) :
    DecAgreeAt false slbl args ci sl (.Thread p) cps buffer σ := by
  obtain ⟨e, hF, e', hV, hR⟩ := thread88_err arI s ar σ length slot p blk call don buf extra ct hct hstall th x0 hx0
    cps hex hnv slbl hl args ci sl buffer
  exact ⟨e', ported_err_of_xcap arI hX hF hR, hV⟩

/-- **Label 60**: U36I's leaf at a frame cap ⇒ both decoders give the same single error. -/
theorem agree_frame60 {X XP : S → A → Fl4Spec.State Unit → Prop} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (length slot : U64) (p : U64) (sz : capability.FrameSize) (rt : U64) (d m ie : Bool) (asid va : U64)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ct : U64)
    (hct : sched.cur_thread st s = ok ct) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (th : TypedHeap) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (cps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraSRel th (L.mem s) x0 cps)
    (hnv : ∀ x ∈ cps.head?, ¬ Fl4Spec.IsVirtCap x.1)
    (slbl : Fl4Spec.Data) (hl : Fl4Spec.dataToNat slbl = Fl4Spec.fl4PageMapEptLabel)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (buffer : Option Fl4Spec.ObjRef)
    (hX : XCapP (L := L) arI X XP s ar σ fl4_abi.label.X86PageMapEPT length slot (.Frame p sz rt d m ie asid va)
      blk call don fp buf extra slbl (args.map UScalar.bv) ci sl cps buffer ct) :
    DecAgreeAt fp slbl (args.map UScalar.bv) ci sl (.Frame p sz rt d m ie asid va) cps buffer σ := by
  obtain ⟨e, hF, e', hV, hR⟩ := frame60_err arI s ar σ length slot p sz rt d m ie asid va blk call don fp buf extra
    ct hct args hlen hargs th x0 hx0 cps hex hnv slbl hl ci sl buffer
  exact ⟨e', ported_err_of_xcap arI hX hF hR, hV⟩

/-- **The VT-x retype gate**: U36I's leaf at an untyped cap ⇒ both decoders give the same single error
(`hvirt` [P], `hvk` [S]). -/
theorem agree_untypedGate {X XP : S → A → Fl4Spec.State Unit → Prop} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (length slot : U64) (p sb fi : U64) (dev : Bool) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (args : List U64) (hlen : length.val = args.length) (h6 : 6 ≤ args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (th : TypedHeap) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0) (hx0n : x0 ≠ 0#u64)
    (cps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraSRel th (L.mem s) x0 cps)
    (nt : U64) (hnt : args.head? = some nt) (hlo : 14 ≤ nt.val) (hhi : nt.val < 19)
    (hvirt : arI.virtualization ar = ok 0#u64) (hvk : Fl4Spec.virtKind = .none)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .untypedRetype)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (buffer : Option Fl4Spec.ObjRef)
    (hX : XCapP (L := L) arI X XP s ar σ fl4_abi.label.UntypedRetype length slot (.Untyped p sb fi dev)
      blk call don fp buf extra slbl (args.map UScalar.bv) ci sl cps buffer ct) :
    DecAgreeAt fp slbl (args.map UScalar.bv) ci sl (.Untyped p sb fi dev) cps buffer σ := by
  obtain ⟨e, hF, e', hV, hR⟩ := untypedGate_err arI s ar σ length slot p sb fi dev blk call don fp buf extra ct hct
    args hlen h6 hargs th x0 hx0 hx0n cps hex nt hnt hlo hhi hvirt hvk slbl hlbl ci sl buffer
  exact ⟨e', ported_err_of_xcap arI hX hF hR, hV⟩

end

end

end Fl4Proofs.P3
