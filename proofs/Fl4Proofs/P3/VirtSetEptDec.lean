/-
P3 against the virtualization extension (line virt, gen 1; proofs/VIRT-PLAN.md §10 R7, route B):
**FL4's `TCBSetEPTRoot` decode (label 88) refines the extended decoder `fl4DecodeInvocationV`**.

FL4 source: `crates/fl4-core/src/tcb.rs:404-489` (`tcb::decode`, the `TCBSetEPTRoot` branch, lines 406-430),
reached from `syscall::decode_invocation` (Thread cap, second phase). Spec: `Fl4Spec/Ext/VirtDispatch`
(`fl4DecodeInvocationV`, thread cap at label `fl4SetEptRootLabel` = 88, not first phase) and
`Fl4Spec/Ext/VirtFinalise` (`decodeSetEptRoot`), which extend l4v `Decode_A.decode_invocation` /
`Tcb_A.decode_tcb_invocation` (ported as `Fl4Spec.fl4DecodeInvocation`, where label 88 is
`IllegalOperation`) after seL4 `decodeSetEPTRoot` (`src/object/tcb.c`, `CONFIG_VTX`).

The ported decoder disagrees with FL4 here (p3J's K6: `TruncatedMessage` vs `IllegalOperation`); the
extended one agrees, on both sides:

* **error side** `setEptRoot_decode_err`: when the first extra slot is empty (`TruncatedMessage`) or does
  not hold a mapped level-0 EPT cap (`IllegalOperation`), FL4's `tcb::decode` returns that error with the
  store and arch state unchanged, and the extended decode has the single outcome `error e'` with the spec
  state unchanged and `ErrRel e e'`;
* **success side** `setEptRoot_decode_ok`: when it holds a mapped level-0 EPT cap `cap`, the extended decode
  has the single outcome `ok (.setEptRoot ⟨p, absCap cap, src⟩)` with the state unchanged, `src` the spec
  slot of FL4's extra slot, and FL4's `tcb::decode` *is* `setEptRootF` — FL4's perform part (delete the
  target's EPT slot, insert `cap` derived from `src`, set the caller restart) with FL4's derived cap equal
  to `cap` (`derive_cap` of a mapped EPT cap is the identity, as the spec's `archDeriveCap`). So FL4's
  decode/perform split at label 88 is exact; `invokeSetEptRoot` vs `setEptRootF` is the perform half.
* `decode_invocation_thread_eq`: FL4's dispatcher on a Thread cap in the second phase is `tcb::decode`.

On a `NoVirtCaps` state (VirtP3x) the success side is vacuous (no EPT cap exists), so at
`virtKind = none` the error side covers every label-88 invocation.

Premises (named hypotheses of the theorems):
* `hstall` [J]: the target's `smp::remote_tcb_stall` returns the state unchanged (as `tcb_decode_refines`'s
  `hstall`; `remote_tcb_stall_id` gives it for a thread of the current core).
* `hx0`, `hex`: the first extra slot `x0` and its spec counterpart `cps` (`ExtraSRel`, as at every other
  decode with extra caps: what `lookup_extra_caps` relates).
* `hl`: the spec label is 88.
No [P], no [W]. No sorry. New file only.
-/
import Fl4Proofs.P3.IrqIssue
import Fl4Spec.Ext.VirtP3x
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-- A mapped level-0 EPT cap (an EPT root with an ASID): the only extra cap FL4's `TCBSetEPTRoot`
accepts (`tcb.rs:416`). -/
def EptRootC (c : capability.Cap) : Prop := ∃ q asid va, c = .Ept q 0#u64 true asid va

/-- The extended spec's decode of a cap, as FL4's dispatcher calls it (`specDec` with
`fl4DecodeInvocationV`). -/
abbrev specDecV (fp : Bool) (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (c : capability.Cap) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) : Fl4Spec.SEMonad Unit Fl4Spec.Fl4InvocationV :=
  Fl4Spec.fl4DecodeInvocationV fp slbl args ci sl (absCap c) excaps buffer

/-! ## Spec side -/

/-- The extended decoder of a thread cap at label 88 (second phase) is `decodeSetEptRoot`. -/
theorem decV_thread88 {t : Fl4Spec.ObjRef} {slbl : Fl4Spec.Data}
    (hl : Fl4Spec.dataToNat slbl = Fl4Spec.fl4SetEptRootLabel) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) :
    Fl4Spec.fl4DecodeInvocationV (Z := Unit) false slbl args ci sl (.threadCap t) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4InvocationV.setEptRoot (Fl4Spec.decodeSetEptRoot t excaps) := by
  unfold Fl4Spec.fl4DecodeInvocationV
  dsimp only
  rw [if_pos ⟨Bool.false_ne_true, hl⟩]

theorem decodeSetEptRoot_nil (t : Fl4Spec.ObjRef) (σ : Fl4Spec.State Unit) :
    (Fl4Spec.decodeSetEptRoot (Z := Unit) t []).run σ = ({(.error .truncatedMessage, σ)}, False) := rfl

theorem decodeSetEptRoot_bad {t : Fl4Spec.ObjRef} {c : Fl4Spec.Cap} {src : Fl4Spec.CslotPtr}
    {rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    (h : ∀ q m, c ≠ .archObjectCap (.eptCap q 0 (some m))) (σ : Fl4Spec.State Unit) :
    (Fl4Spec.decodeSetEptRoot (Z := Unit) t ((c, src) :: rest)).run σ =
      ({(.error .illegalOperation, σ)}, False) := by
  simp only [Fl4Spec.decodeSetEptRoot]
  first
    | rfl
    | (split
       · exact absurd rfl (h _ _)
       · rfl)

theorem decodeSetEptRoot_root {t : Fl4Spec.ObjRef} {q : Fl4Spec.ObjRef} {m}
    {src : Fl4Spec.CslotPtr} {rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)} (σ : Fl4Spec.State Unit) :
    (Fl4Spec.decodeSetEptRoot (Z := Unit) t ((.archObjectCap (.eptCap q 0 (some m)), src) :: rest)).run σ =
      ({(.ok ⟨t, .archObjectCap (.eptCap q 0 (some m)), src⟩, σ)}, False) := by
  simp only [Fl4Spec.decodeSetEptRoot, Fl4Spec.deriveCap, Fl4Spec.archDeriveCap]
  rw [run_bind_ok (run_returnOk _ _)]
  rfl

/-- The spec cap of an FL4 cap that is not a mapped level-0 EPT cap is not the spec's EPT root. -/
theorem absCap_not_eptRoot {c : capability.Cap} (h : ¬ EptRootC c) :
    ∀ q m, absCap c ≠ .archObjectCap (.eptCap q 0 (some m)) := by
  intro q m he
  cases c with
  | Ept p level mp asid va =>
    simp only [absCap, Fl4Spec.Cap.archObjectCap.injEq, Fl4Spec.ArchCap.eptCap.injEq] at he
    obtain ⟨-, hl, hm⟩ := he
    have hl0 : level = 0#u64 := UScalar.eq_of_val_eq (by rw [hl]; rfl)
    cases mp
    · simp at hm
    · exact h ⟨p, asid, va, by rw [hl0]⟩
  | _ => simp [absCap] at he

/-! ## FL4 side -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **FL4's `TCBSetEPTRoot` after its checks** (`tcb.rs:420-428`): delete the target's EPT slot, insert
`val` (the derived cap) from `src`, set the current thread restart. Verbatim the success branch of
`tcb::decode` with the derived cap as parameter. -/
def setEptRootF (s : S) (a : A) (target : obj.Tcb) (src : obj.Slot) (val : capability.Cap) :
    Result ((core.result.Result Unit error.Exc) × S × A) := do
  let s3 ← obj.Tcb.slot target layout.tcb.SLOT_EPT
  let (r1, s4, a2) ← cdt.delete st arI s a s3 true
  let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf1 with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let s5 ← cdt.insert st s4 val src s3
    let ct ← sched.cur_thread st s5
    let s6 ← sched.set_thread_state st s5 ct sched.TS_RESTART
    ok (core.result.Result.Ok (), s6, a2)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r2 ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        Unit (core.convert.FromSame error.Exc) residual
    ok (r2, s4, a2)

/-- FL4's dispatcher on a Thread cap in the second phase is `tcb::decode`. -/
theorem decode_invocation_thread_eq (s : S) (ar : A) (lbl length slot : U64) (p : U64) (blk call don : Bool)
    (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ct : U64) (hct : sched.cur_thread st s = ok ct) :
    syscall.decode_invocation st arI s ar lbl length slot (.Thread p) blk call don false buf extra =
      tcb.decode st arI s ar lbl p ⟨length, buf, call, slot, extra⟩ := by
  unfold syscall.decode_invocation
  rw [hct]; simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]

/-- Label 88 with an empty first extra slot: `TruncatedMessage` (`tcb.rs:411`). -/
theorem tcb_decode_ept_trunc (s : S) (ar : A) (p : U64) (c : tcb.Ctx)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (hx0 : Aeneas.Std.Array.index_usize c.extra 0#usize = ok 0#u64) :
    tcb.decode st arI s ar fl4_abi.label.TCBSetEPTRoot p c = ok (.Err (.Sys .TruncatedMessage), s, ar) := by
  unfold tcb.decode
  rw [hstall]
  simp only [bind_ok, ↓reduceIte, hx0, is_null_eq, decide_true, error.truncated]
  rfl

/-- Label 88 with a first extra cap that is not a mapped level-0 EPT cap: `IllegalOperation`
(`tcb.rs:416-418`). -/
theorem tcb_decode_ept_illegal (s : S) (ar : A) (p : U64) (c : tcb.Ctx)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (x0 : U64)
    (hx0 : Aeneas.Std.Array.index_usize c.extra 0#usize = ok x0) (hx0n : x0 ≠ 0#u64)
    (hbad : ¬ EptRootC (capV (L.mem s) x0)) :
    tcb.decode st arI s ar fl4_abi.label.TCBSetEPTRoot p c = ok (.Err (.Sys .IllegalOperation), s, ar) := by
  unfold tcb.decode
  rw [hstall]
  simp only [bind_ok, uncurry_apply_pair, ↓reduceIte, hx0, is_null_eq, hx0n, decide_false, Bool.false_eq_true,
    slot_cap_eq, capAt_capV]
  generalize capV (L.mem s) x0 = cv at hbad ⊢
  cases cv with
  | Ept q i b asid va =>
    by_cases hroot : i = 0#u64 ∧ b = true
    · obtain ⟨rfl, rfl⟩ := hroot
      exact absurd ⟨q, asid, va, rfl⟩ hbad
    · simp only [error.illegal, bind_ok]
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
  | _ => simp only [error.illegal, bind_ok]

/-- Label 88 with a mapped level-0 EPT cap: FL4's decode is `setEptRootF` with the cap itself as the
derived cap (`tcb.rs:419-428`; `derive_cap` of a mapped EPT cap, `objects.rs`). -/
theorem tcb_decode_ept_root (s : S) (ar : A) (p : U64) (c : tcb.Ctx)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (x0 : U64)
    (hx0 : Aeneas.Std.Array.index_usize c.extra 0#usize = ok x0) (hx0n : x0 ≠ 0#u64)
    {q asid va : U64} (hc : capV (L.mem s) x0 = .Ept q 0#u64 true asid va) :
    tcb.decode st arI s ar fl4_abi.label.TCBSetEPTRoot p c =
      setEptRootF (st := st) arI s ar p x0 (.Ept q 0#u64 true asid va) := by
  unfold tcb.decode
  rw [hstall]
  simp only [bind_ok, uncurry_apply_pair, ↓reduceIte, hx0, is_null_eq, hx0n, decide_false, Bool.false_eq_true,
    slot_cap_eq, capAt_capV, hc, objects.derive_cap, core.result.Result.Insts.CoreOpsTry.branch]
  first
    | rfl
    | (split
       · simp only [↓reduceIte, bind_ok]
         rfl
       · exfalso
         first
           | (rename_i hne; exact hne rfl)
           | simp_all)

/-! ## FL4 against the extended decoder -/

/-- **Label 88, error side** (module docstring). -/
theorem setEptRoot_decode_err (s : S) (ar : A) (σ : Fl4Spec.State Unit) (p : U64) (c : tcb.Ctx)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (th : TypedHeap) (x0 : U64)
    (hx0 : Aeneas.Std.Array.index_usize c.extra 0#usize = ok x0)
    (cps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraSRel th (L.mem s) x0 cps)
    (hbad : x0 = 0#u64 ∨ ¬ EptRootC (capV (L.mem s) x0))
    (slbl : Fl4Spec.Data) (hl : Fl4Spec.dataToNat slbl = Fl4Spec.fl4SetEptRootLabel) (args : List Fl4Spec.Data)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (buffer : Option Fl4Spec.ObjRef) :
    ∃ e, tcb.decode st arI s ar fl4_abi.label.TCBSetEPTRoot p c = ok (.Err e, s, ar) ∧
      ∃ e', (specDecV false slbl args ci sl (.Thread p) cps buffer).run σ = ({(.error e', σ)}, False) ∧
        ErrRel e e' := by
  have hd : specDecV false slbl args ci sl (.Thread p) cps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4InvocationV.setEptRoot (Fl4Spec.decodeSetEptRoot p.bv cps) :=
    decV_thread88 hl args ci sl cps buffer
  rw [hd]
  rcases hex with ⟨rfl, rfl⟩ | ⟨hx0n, ps, rs, idxs, rest, -, -, -, rfl⟩
  · exact ⟨_, tcb_decode_ept_trunc arI s ar p c hstall hx0, _,
      run_liftME_err (decodeSetEptRoot_nil _ σ), Or.inl trivial⟩
  · have hb : ¬ EptRootC (capV (L.mem s) x0) := hbad.resolve_left hx0n
    exact ⟨_, tcb_decode_ept_illegal arI s ar p c hstall x0 hx0 hx0n hb, _,
      run_liftME_err (decodeSetEptRoot_bad (absCap_not_eptRoot hb) σ), Or.inl trivial⟩

/-- **Label 88, success side** (module docstring). -/
theorem setEptRoot_decode_ok (s : S) (ar : A) (σ : Fl4Spec.State Unit) (p : U64) (c : tcb.Ctx)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (th : TypedHeap) (x0 : U64)
    (hx0 : Aeneas.Std.Array.index_usize c.extra 0#usize = ok x0)
    (cps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraSRel th (L.mem s) x0 cps)
    {q asid va : U64} (hx0n : x0 ≠ 0#u64) (hc : capV (L.mem s) x0 = .Ept q 0#u64 true asid va)
    (slbl : Fl4Spec.Data) (hl : Fl4Spec.dataToNat slbl = Fl4Spec.fl4SetEptRootLabel) (args : List Fl4Spec.Data)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (buffer : Option Fl4Spec.ObjRef) :
    ∃ (ps : U64) (idxs : Fl4Spec.CnodeIndex) (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), x0 = cslotAddr (ps.bv, idxs) ∧
      cps = (absCap (.Ept q 0#u64 true asid va), (ps.bv, idxs)) :: rest ∧
      (specDecV false slbl args ci sl (.Thread p) cps buffer).run σ =
        ({(.ok (.setEptRoot ⟨p.bv, absCap (.Ept q 0#u64 true asid va), (ps.bv, idxs)⟩), σ)}, False) ∧
      tcb.decode st arI s ar fl4_abi.label.TCBSetEPTRoot p c =
        setEptRootF (st := st) arI s ar p x0 (.Ept q 0#u64 true asid va) := by
  rcases hex with ⟨rfl, -⟩ | ⟨-, ps, rs, idxs, rest, -, -, hxe, rfl⟩
  · exact absurd rfl hx0n
  refine ⟨ps, idxs, rest, hxe, by rw [hc], ?_, tcb_decode_ept_root arI s ar p c hstall x0 hx0 hx0n hc⟩
  have hd : specDecV false slbl args ci sl (.Thread p) ((absCap (capV (L.mem s) x0), (ps.bv, idxs)) :: rest)
      buffer = Fl4Spec.NonDetE.liftME Fl4Spec.Fl4InvocationV.setEptRoot
        (Fl4Spec.decodeSetEptRoot p.bv ((absCap (capV (L.mem s) x0), (ps.bv, idxs)) :: rest)) :=
    decV_thread88 hl args ci sl _ buffer
  rw [hd, hc]
  exact run_liftME_ok (decodeSetEptRoot_root σ)

end

end

end Fl4Proofs.P3
