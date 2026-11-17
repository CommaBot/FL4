/-
P3 (DESIGN.md §9), CSpace and TCB: **SetBreakpoint at `XTop`**
(`tcb_set_bpX`).

* `set_bp_checked_eq`: FL4's `set_breakpoint_checked` (3,300 lines of
  extracted control flow) is its first failing check (`bpErrF`), else the
  restart and `debug::set_breakpoint`.
* `set_bp_spec_run`: the spec's `decodeFl4SetBreakpoint` is its first
  failing check (`bpErrS`), else the invocation; `bpErr_rel`: the two checks
  agree (`ErrRel`).
* `set_bp_wr`: `debug::set_breakpoint` writes the breakpoint's address word
  and `DR7` (offsets 448..504, read by no relation: `XTopAt.tcbWrA`).
* `tcb_set_bpX`, `tcbXOpen4_of`: TcbXOpen4's SetBreakpoint discharged; the
  Thread cap's labels still open are `TcbXOpen3` (ReadFPU, WriteFPU,
  SetTimer).
-/
import Fl4Proofs.P3.XTopTcbData
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

/-- **FL4's checks of SetBreakpoint**, in its order: the first failing one. -/
def bpErrF (bp vaddr ty size rw : U64) : Option error.Exc :=
  if vaddr ≥ fl4_abi.consts.USER_TOP then some (.Sys (.InvalidArgument 1#u64))
  else if ty ≠ 1#u64 ∧ ty ≠ 0#u64 then some (.Sys (.InvalidArgument 2#u64))
  else if ty = 1#u64 ∧ size ≠ 0#u64 then some (.Sys (.InvalidArgument 3#u64))
  else if ty = 1#u64 ∧ rw ≠ 0#u64 then some (.Sys (.InvalidArgument 4#u64))
  else if ty ≠ 1#u64 ∧ size = 0#u64 then some (.Sys (.InvalidArgument 3#u64))
  else if rw ≠ 0#u64 ∧ rw ≠ 1#u64 ∧ rw ≠ 2#u64 then some (.Sys (.InvalidArgument 3#u64))
  else if size ≠ 0#u64 ∧ size ≠ 1#u64 ∧ size ≠ 2#u64 ∧ size ≠ 4#u64 ∧ size ≠ 8#u64 then
    some (.Sys (.InvalidArgument 3#u64))
  else if 0#u64 < size ∧ (vaddr &&& core.num.U64.wrapping_sub size 1#u64) ≠ 0#u64 then some (.Sys .AlignmentError)
  else if bp ≥ 4#u64 then some (.Sys (.RangeError 0#u64 3#u64))
  else if size = 8#u64 then some (.Sys (.InvalidArgument 3#u64))
  else none

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem sub1_eq {x : U64} (h : 0#u64 < x) : x - 1#u64 = ok (core.num.U64.wrapping_sub x 1#u64) := by
  obtain ⟨v, hv, hv1⟩ := spec_exists (U64.sub_spec (x := x) (y := 1#u64) (by scalar_tac))
  rw [hv]; congr 1
  apply UScalar.eq_of_val_eq
  rw [core.num.U64.wrapping_sub_val_eq]
  have : (0 : Nat) < x.val := by scalar_tac
  have : x.val < 2 ^ 64 := by scalar_tac
  simp [U64.size, U64.numBits] at hv1 ⊢
  omega

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem set_bp_checked_eq (s : S) (t : U64) (c : tcb.Ctx) {bp vaddr ty size rw : U64}
    (h0 : tcb.arg st s c 0#u64 = ok bp) (h1 : tcb.arg st s c 1#u64 = ok vaddr)
    (h2 : tcb.arg st s c 2#u64 = ok ty) (h3 : tcb.arg st s c 3#u64 = ok size)
    (h4 : tcb.arg st s c 4#u64 = ok rw) :
    tcb.set_breakpoint_checked st s t c = (match bpErrF bp vaddr ty size rw with
      | some e => ok (.Err e, s)
      | none => (do
        let s1 ← tcb.restart_caller st s
        let s2 ← debug.set_breakpoint st s1 t bp vaddr ty size rw
        ok (.Ok (), s2))) := by
  unfold tcb.set_breakpoint_checked
  rw [h0, h1, h2, h3, h4]
  simp only [bind_ok]
  unfold bpErrF
  simp only [debug.INSTRUCTION_BREAKPOINT, debug.DATA_BREAKPOINT, debug.BREAK_ON_READ, debug.BREAK_ON_WRITE,
    debug.BREAK_ON_READ_WRITE, bne_iff_ne, ne_eq]
  have n01 : (0#u64 : U64) ≠ 1#u64 := by decide
  have n02 : (0#u64 : U64) ≠ 2#u64 := by decide
  have n04 : (0#u64 : U64) ≠ 4#u64 := by decide
  have n08 : (0#u64 : U64) ≠ 8#u64 := by decide
  have n10 : (1#u64 : U64) ≠ 0#u64 := by decide
  have n12 : (1#u64 : U64) ≠ 2#u64 := by decide
  have n14 : (1#u64 : U64) ≠ 4#u64 := by decide
  have n18 : (1#u64 : U64) ≠ 8#u64 := by decide
  have n20 : (2#u64 : U64) ≠ 0#u64 := by decide
  have n21 : (2#u64 : U64) ≠ 1#u64 := by decide
  have n24 : (2#u64 : U64) ≠ 4#u64 := by decide
  have n28 : (2#u64 : U64) ≠ 8#u64 := by decide
  have n40 : (4#u64 : U64) ≠ 0#u64 := by decide
  have n41 : (4#u64 : U64) ≠ 1#u64 := by decide
  have n42 : (4#u64 : U64) ≠ 2#u64 := by decide
  have n48 : (4#u64 : U64) ≠ 8#u64 := by decide
  have n80 : (8#u64 : U64) ≠ 0#u64 := by decide
  have n81 : (8#u64 : U64) ≠ 1#u64 := by decide
  have n82 : (8#u64 : U64) ≠ 2#u64 := by decide
  have n84 : (8#u64 : U64) ≠ 4#u64 := by decide
  have p1 : (0#u64 : U64) < 1#u64 := by decide
  have z0 : ¬ (0#u64 : U64) < 0#u64 := by decide
  have p2 : (0#u64 : U64) < 2#u64 := by decide
  have p4 : (0#u64 : U64) < 4#u64 := by decide
  have p8 : (0#u64 : U64) < 8#u64 := by decide
  by_cases c1 : vaddr ≥ fl4_abi.consts.USER_TOP
  · simp only [c1, ↓reduceIte, error.invalid_arg, bind_ok]
  simp only [c1, ↓reduceIte]
  by_cases c2 : ty ≠ 1#u64 ∧ ty ≠ 0#u64
  · obtain ⟨c2a, c2b⟩ := c2
    simp only [n01, n02, n04, n08, n10, n12, n14, n18, n20, n21, n24, n28, n40, n41, n42, n48, n80, n81, n82, n84, p1, p2, p4, p8, z0, ↓reduceIte, error.invalid_arg, error.sys, bind_ok, not_false_eq_true, not_true_eq_false,
      and_true, true_and, and_false, false_and, and_self, ne_eq, gt_iff_lt, lift, check_bp_eq,
      core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, c2a, c2b]
  have hty : ty = 1#u64 ∨ ty = 0#u64 := by
    by_contra h; exact c2 ⟨fun e => h (Or.inl e), fun e => h (Or.inr e)⟩
  rcases hty with rfl | rfl
  · by_cases c3 : size = 0#u64
    swap
    · simp only [n01, n02, n04, n08, n10, n12, n14, n18, n20, n21, n24, n28, n40, n41, n42, n48, n80, n81, n82, n84, p1, p2, p4, p8, z0, ↓reduceIte, error.invalid_arg, error.sys, bind_ok, not_false_eq_true, not_true_eq_false,
      and_true, true_and, and_false, false_and, and_self, ne_eq, gt_iff_lt, lift, check_bp_eq,
      core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, c3]
    subst c3
    by_cases c4 : rw = 0#u64
    swap
    · simp only [n01, n02, n04, n08, n10, n12, n14, n18, n20, n21, n24, n28, n40, n41, n42, n48, n80, n81, n82, n84, p1, p2, p4, p8, z0, ↓reduceIte, error.invalid_arg, error.sys, bind_ok, not_false_eq_true, not_true_eq_false,
      and_true, true_and, and_false, false_and, and_self, ne_eq, gt_iff_lt, lift, check_bp_eq,
      core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, c4]
    subst c4
    by_cases c9 : bp ≥ 4#u64
    · simp only [n01, n02, n04, n08, n10, n12, n14, n18, n20, n21, n24, n28, n40, n41, n42, n48, n80, n81, n82, n84, p1, p2, p4, p8, z0, ↓reduceIte, error.invalid_arg, error.sys, bind_ok, not_false_eq_true, not_true_eq_false,
      and_true, true_and, and_false, false_and, and_self, ne_eq, gt_iff_lt, lift, check_bp_eq,
      core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, c9]
    · simp only [n01, n02, n04, n08, n10, n12, n14, n18, n20, n21, n24, n28, n40, n41, n42, n48, n80, n81, n82, n84, p1, p2, p4, p8, z0, ↓reduceIte, error.invalid_arg, error.sys, bind_ok, not_false_eq_true, not_true_eq_false,
      and_true, true_and, and_false, false_and, and_self, ne_eq, gt_iff_lt, lift, check_bp_eq,
      core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, c9]
  · by_cases c5 : size = 0#u64
    · subst c5
      simp only [n01, n02, n04, n08, n10, n12, n14, n18, n20, n21, n24, n28, n40, n41, n42, n48, n80, n81, n82, n84, p1, p2, p4, p8, z0, ↓reduceIte, error.invalid_arg, error.sys, bind_ok, not_false_eq_true, not_true_eq_false,
      and_true, true_and, and_false, false_and, and_self, ne_eq, gt_iff_lt, lift, check_bp_eq,
      core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok]
    by_cases c6 : rw = 0#u64 ∨ rw = 1#u64 ∨ rw = 2#u64
    swap
    · simp only [not_or] at c6
      obtain ⟨c6a, c6b, c6c⟩ := c6
      simp only [n01, n02, n04, n08, n10, n12, n14, n18, n20, n21, n24, n28, n40, n41, n42, n48, n80, n81, n82, n84, p1, p2, p4, p8, z0, ↓reduceIte, error.invalid_arg, error.sys, bind_ok, not_false_eq_true, not_true_eq_false,
      and_true, true_and, and_false, false_and, and_self, ne_eq, gt_iff_lt, lift, check_bp_eq,
      core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, c5, c6a, c6b, c6c]
    by_cases c7 : size = 1#u64 ∨ size = 2#u64 ∨ size = 4#u64 ∨ size = 8#u64
    swap
    · simp only [not_or] at c7
      obtain ⟨c7a, c7b, c7c, c7d⟩ := c7
      rcases c6 with rfl | rfl | rfl <;>
      simp only [n01, n02, n04, n08, n10, n12, n14, n18, n20, n21, n24, n28, n40, n41, n42, n48, n80, n81, n82, n84, p1, p2, p4, p8, z0, ↓reduceIte, error.invalid_arg, error.sys, bind_ok, not_false_eq_true, not_true_eq_false,
      and_true, true_and, and_false, false_and, and_self, ne_eq, gt_iff_lt, lift, check_bp_eq,
      core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, c5, c7a, c7b, c7c, c7d]
    rw [sub1_eq (x := size) (by rcases c7 with rfl | rfl | rfl | rfl <;> decide)]
    by_cases c8 : (vaddr &&& core.num.U64.wrapping_sub size 1#u64) = 0#u64 <;>
    by_cases c9 : bp ≥ 4#u64 <;>
    rcases c6 with rfl | rfl | rfl <;> rcases c7 with rfl | rfl | rfl | rfl <;>
    (
     simp only [n01, n02, n04, n08, n10, n12, n14, n18, n20, n21, n24, n28, n40, n41, n42, n48, n80, n81, n82, n84, p1, p2, p4, p8, z0, ↓reduceIte, error.invalid_arg, error.sys, bind_ok, not_false_eq_true, not_true_eq_false,
      and_true, true_and, and_false, false_and, and_self, ne_eq, gt_iff_lt, lift, check_bp_eq,
      core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, c8, c9])

/-! ## The spec's checks -/

open Fl4Spec in
/-- **The spec's checks of SetBreakpoint** (`decodeFl4SetBreakpoint`), in its
order: the first failing one. -/
def bpErrS (bp : U64) (vaddr ty size rw : Data) : Option SyscallError :=
  if vaddr ≥ fl4UserTop then some (.invalidArgument 1)
  else if ty ≠ fl4InstructionBreakpoint ∧ ty ≠ fl4DataBreakpoint then some (.invalidArgument 2)
  else if ty = fl4InstructionBreakpoint ∧ size ≠ 0 then some (.invalidArgument 3)
  else if ty = fl4InstructionBreakpoint ∧ rw ≠ fl4BreakOnRead then some (.invalidArgument 4)
  else if ty ≠ fl4InstructionBreakpoint ∧ size = 0 then some (.invalidArgument 3)
  else if rw ≠ fl4BreakOnRead ∧ rw ≠ fl4BreakOnWrite ∧ rw ≠ fl4BreakOnReadWrite then some (.invalidArgument 3)
  else if size ≠ 0 ∧ size ≠ 1 ∧ size ≠ 2 ∧ size ≠ 4 ∧ size ≠ 8 then some (.invalidArgument 3)
  else if size > 0 ∧ vaddr &&& (size - 1) ≠ 0 then some .alignmentError
  else if bp ≥ 4#u64 then some (.rangeError 0 3)
  else if size = 8 then some (.invalidArgument 3)
  else none

theorem run_whenE_throw {β : Type} (P : Prop) [Decidable P] (e : Fl4Spec.SyscallError)
    (k : Unit → Fl4Spec.SEMonad Unit β) (σ : Fl4Spec.State Unit) :
    ((Fl4Spec.NonDetE.whenE P (Fl4Spec.NonDetE.throwError e) : Fl4Spec.SEMonad Unit Unit) >>= k).run σ =
      if P then ({(.error e, σ)}, False) else (k ()).run σ := by
  by_cases h : P
  · rw [whenE_pos h, if_pos h]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError e : Fl4Spec.SEMonad Unit Unit)) rfl _
  · rw [whenE_neg h, if_neg h]
    exact run_bind_ok (m := (Fl4Spec.NonDetE.returnOk () : Fl4Spec.SEMonad Unit Unit)) rfl _

theorem run_whenE_throw0 (P : Prop) [Decidable P] (e : Fl4Spec.SyscallError) (σ : Fl4Spec.State Unit) :
    (Fl4Spec.NonDetE.whenE P (Fl4Spec.NonDetE.throwError e) : Fl4Spec.SEMonad Unit Unit).run σ =
      if P then ({(.error e, σ)}, False) else ({(.ok (), σ)}, False) := by
  by_cases h : P
  · rw [whenE_pos h, if_pos h]; rfl
  · rw [whenE_neg h, if_neg h]; rfl

set_option maxHeartbeats 4000000 in
/-- **The spec's SetBreakpoint decode** is its first failing check, else
the invocation. -/
theorem set_bp_spec_run (σ : Fl4Spec.State Unit) (buffer : Option Fl4Spec.ObjRef) (t : Fl4Spec.ObjRef)
    {bp : U64} {vaddr ty size rw : Fl4Spec.Data}
    (g0 : (Fl4Spec.fl4Arg (Z := Unit) buffer 0).run σ = ({(.ok bp.bv, σ)}, False))
    (g1 : (Fl4Spec.fl4Arg (Z := Unit) buffer 1).run σ = ({(.ok vaddr, σ)}, False))
    (g2 : (Fl4Spec.fl4Arg (Z := Unit) buffer 2).run σ = ({(.ok ty, σ)}, False))
    (g3 : (Fl4Spec.fl4Arg (Z := Unit) buffer 3).run σ = ({(.ok size, σ)}, False))
    (g4 : (Fl4Spec.fl4Arg (Z := Unit) buffer 4).run σ = ({(.ok rw, σ)}, False)) :
    (Fl4Spec.decodeFl4SetBreakpoint (Z := Unit) buffer t).run σ = (match bpErrS bp vaddr ty size rw with
      | some e => ({(.error e, σ)}, False)
      | none => ({(.ok (.setBreakpoint t bp.bv vaddr ty size rw), σ)}, False)) := by
  unfold Fl4Spec.decodeFl4SetBreakpoint
  rw [run_bind_ok g0, run_bind_ok g1, run_bind_ok g2, run_bind_ok g3, run_bind_ok g4]
  unfold bpErrS
  rw [run_whenE_throw]
  by_cases c1 : vaddr ≥ Fl4Spec.fl4UserTop
  · rw [if_pos c1, if_pos c1]
  rw [if_neg c1, if_neg c1, run_whenE_throw]
  by_cases c2 : ty ≠ Fl4Spec.fl4InstructionBreakpoint ∧ ty ≠ Fl4Spec.fl4DataBreakpoint
  · rw [if_pos c2, if_pos c2]
  rw [if_neg c2, if_neg c2]
  -- the type's own checks
  have tail : ((Fl4Spec.NonDetE.whenE (rw ≠ Fl4Spec.fl4BreakOnRead ∧ rw ≠ Fl4Spec.fl4BreakOnWrite ∧
        rw ≠ Fl4Spec.fl4BreakOnReadWrite) (Fl4Spec.NonDetE.throwError (.invalidArgument 3)) :
        Fl4Spec.SEMonad Unit Unit) >>= fun _ =>
      (Fl4Spec.NonDetE.whenE (size ≠ 0 ∧ size ≠ 1 ∧ size ≠ 2 ∧ size ≠ 4 ∧ size ≠ 8)
        (Fl4Spec.NonDetE.throwError (.invalidArgument 3)) : Fl4Spec.SEMonad Unit Unit) >>= fun _ =>
      (Fl4Spec.NonDetE.whenE (size > 0 ∧ vaddr &&& (size - 1) ≠ 0)
        (Fl4Spec.NonDetE.throwError .alignmentError) : Fl4Spec.SEMonad Unit Unit) >>= fun _ =>
      Fl4Spec.fl4CheckBpNum (Z := Unit) bp.bv >>= fun _ =>
      (Fl4Spec.NonDetE.whenE (size = 8) (Fl4Spec.NonDetE.throwError (.invalidArgument 3)) :
        Fl4Spec.SEMonad Unit Unit) >>= fun _ =>
      Fl4Spec.NonDetE.returnOk (Fl4Spec.Fl4TcbInvocation.setBreakpoint t bp.bv vaddr ty size rw)).run σ =
      (match (if rw ≠ Fl4Spec.fl4BreakOnRead ∧ rw ≠ Fl4Spec.fl4BreakOnWrite ∧ rw ≠ Fl4Spec.fl4BreakOnReadWrite then
          some (Fl4Spec.SyscallError.invalidArgument 3)
        else if size ≠ 0 ∧ size ≠ 1 ∧ size ≠ 2 ∧ size ≠ 4 ∧ size ≠ 8 then some (.invalidArgument 3)
        else if size > 0 ∧ vaddr &&& (size - 1) ≠ 0 then some .alignmentError
        else if bp ≥ 4#u64 then some (.rangeError 0 3)
        else if size = 8 then some (.invalidArgument 3)
        else none) with
      | some e => ({(.error e, σ)}, False)
      | none => ({(.ok (.setBreakpoint t bp.bv vaddr ty size rw), σ)}, False)) := by
    rw [run_whenE_throw]
    by_cases c6 : rw ≠ Fl4Spec.fl4BreakOnRead ∧ rw ≠ Fl4Spec.fl4BreakOnWrite ∧ rw ≠ Fl4Spec.fl4BreakOnReadWrite
    · rw [if_pos c6, if_pos c6]
    rw [if_neg c6, if_neg c6, run_whenE_throw]
    by_cases c7 : size ≠ 0 ∧ size ≠ 1 ∧ size ≠ 2 ∧ size ≠ 4 ∧ size ≠ 8
    · rw [if_pos c7, if_pos c7]
    rw [if_neg c7, if_neg c7, run_whenE_throw]
    by_cases c8 : size > 0 ∧ vaddr &&& (size - 1) ≠ 0
    · rw [if_pos c8, if_pos c8]
    rw [if_neg c8, if_neg c8]
    by_cases c9 : bp ≥ 4#u64
    · rw [run_bind_error (by rw [checkBp_run, if_pos c9]), if_pos c9]
    rw [run_bind_ok (by rw [checkBp_run, if_neg c9]), if_neg c9, run_whenE_throw]
    by_cases c10 : size = 8
    · rw [if_pos c10, if_pos c10]
    · rw [if_neg c10, if_neg c10]; rfl
  by_cases cI : ty = Fl4Spec.fl4InstructionBreakpoint
  · rw [if_pos cI, run_whenE_throw]
    have hn5 : ¬ (ty ≠ Fl4Spec.fl4InstructionBreakpoint ∧ size = 0) := fun h => h.1 cI
    by_cases c3 : size ≠ 0
    · rw [if_pos c3, if_pos ⟨cI, c3⟩]
    rw [if_neg c3, if_neg (fun h => c3 h.2), run_whenE_throw]
    by_cases c4 : rw ≠ Fl4Spec.fl4BreakOnRead
    · rw [if_pos c4, if_pos ⟨cI, c4⟩]
    rw [if_neg c4, if_neg (fun h => c4 h.2), if_neg hn5]
    exact tail
  · rw [if_neg cI, if_neg (fun h => cI h.1), if_neg (fun h => cI h.1), run_whenE_throw]
    by_cases c5 : size = 0
    · rw [if_pos c5, if_pos ⟨cI, c5⟩]
    rw [if_neg c5, if_neg (fun h => c5 h.2)]
    exact tail

/-! ## The two checks agree -/

theorem bvq (x y : U64) : x.bv = y.bv ↔ x = y := (UScalar.eq_equiv_bv_eq _ _).symm

theorem bpc_top (x : U64) : x.bv ≥ Fl4Spec.fl4UserTop ↔ x ≥ fl4_abi.consts.USER_TOP := by
  rw [show Fl4Spec.fl4UserTop = fl4_abi.consts.USER_TOP.bv by unfold fl4_abi.consts.USER_TOP; rfl, GE.ge, GE.ge,
    BitVec.le_def, UScalar.bv_toNat, UScalar.bv_toNat]
  exact Iff.rfl

theorem bpc_i (x : U64) : x.bv = Fl4Spec.fl4InstructionBreakpoint ↔ x = 1#u64 := bvq x 1#u64
theorem bpc_d (x : U64) : x.bv = Fl4Spec.fl4DataBreakpoint ↔ x = 0#u64 := bvq x 0#u64
theorem bpc_r (x : U64) : x.bv = Fl4Spec.fl4BreakOnRead ↔ x = 0#u64 := bvq x 0#u64
theorem bpc_w (x : U64) : x.bv = Fl4Spec.fl4BreakOnWrite ↔ x = 1#u64 := bvq x 1#u64
theorem bpc_rw (x : U64) : x.bv = Fl4Spec.fl4BreakOnReadWrite ↔ x = 2#u64 := bvq x 2#u64
theorem bpc_0 (x : U64) : x.bv = 0 ↔ x = 0#u64 := bvq x 0#u64
theorem bpc_1 (x : U64) : x.bv = 1 ↔ x = 1#u64 := bvq x 1#u64
theorem bpc_2 (x : U64) : x.bv = 2 ↔ x = 2#u64 := bvq x 2#u64
theorem bpc_4 (x : U64) : x.bv = 4 ↔ x = 4#u64 := bvq x 4#u64
theorem bpc_8 (x : U64) : x.bv = 8 ↔ x = 8#u64 := bvq x 8#u64
theorem bpc_pos (x : U64) : x.bv > 0 ↔ 0#u64 < x := (Sched.lt_bv 0#u64 x).symm
theorem bpc_al (v x : U64) : v.bv &&& (x.bv - 1) = 0 ↔ (v &&& core.num.U64.wrapping_sub x 1#u64) = 0#u64 := by
  rw [UScalar.eq_equiv_bv_eq, UScalar.bv_and]
  simp [core.num.U64.wrapping_sub_bv_eq]

set_option maxHeartbeats 4000000 in
/-- **The two checks agree**: both pass, or both fail with related errors. -/
theorem bpErr_rel (bp vaddr ty size rw : U64) :
    match bpErrF bp vaddr ty size rw, bpErrS bp vaddr.bv ty.bv size.bv rw.bv with
    | none, none => True
    | some e, some e' => ErrRel e e'
    | _, _ => False := by
  unfold bpErrF bpErrS
  simp only [bpc_top, bpc_i, bpc_d, bpc_r, bpc_w, bpc_rw, bpc_0, bpc_1, bpc_2, bpc_4, bpc_8, bpc_pos, bpc_al, ne_eq]
  split_ifs <;> first | trivial | exact Or.inl rfl | exact Or.inl trivial | exact Or.inl ⟨rfl, rfl⟩

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem ite_ok {α : Type} (c : Prop) [Decidable c] (a b : α) :
    (if c then ok a else ok b : Result α) = ok (if c then a else b) := by split <;> rfl

/-- **FL4's `set_breakpoint`**: the breakpoint's address word, then `DR7`. -/
theorem set_bp_wr (s : S) (t bp vaddr ty size rw : U64) :
    debug.set_breakpoint st s t bp vaddr ty size rw ⦃ s2 =>
      ∃ v, s2 = L.wr (L.wr s (dbgA t bp) vaddr) (dbgA t 5#u64) v ⦄ := by
  unfold debug.set_breakpoint debug.set_dr7
  simp only [set_debug_reg_wr, debug.DR7]
  unfold debug.dr7 obj.Tcb.debug_reg debug.enable_bit debug.size_shift debug.type_shift
  simp only [ite_ok, bind_ok]
  step*

end

end

theorem bpErrF_bp {bp vaddr ty size rw : U64} (h : bpErrF bp vaddr ty size rw = none) : bp.val < 4 := by
  by_contra hb
  have hb' : bp ≥ 4#u64 := by scalar_tac
  unfold bpErrF at h
  simp only [hb', ↓reduceIte] at h
  split_ifs at h <;> cases h

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

set_option maxHeartbeats 4000000 in
/-- **TcbXOpen4's SetBreakpoint at `XTop`**: FL4's checks against the
spec's (`set_bp_checked_eq`, `set_bp_spec_run`, `bpErr_rel`; the five
arguments by `ArgRel` [J]), the restart, the two debug-register words (the
breakpoint's address, `DR7`; offsets 448..504, read by no relation:
`XTopAt.tcbWrA`); the spec keeps its state (the debug registers are not in
the model). -/
theorem tcb_set_bpX {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (hX : XTopAt (L := L) AR Z s ar σ) (hC : CurRun σ) (hDI : DelInv Z.th (L.mem s))
    (p : U64) (hpT : p ∈ Z.T) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .invalidInvocation)
    (hext : Fl4Spec.fl4TcbExtLabelOf slbl = some .setBreakpoint)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (buffer : Option Fl4Spec.ObjRef)
    (hA : ArgRel (st := st) s σ ct buf buffer 5)
    (call : Bool) (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk don : Bool)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) :
    TcbOKX (L := L) arI (XTop (L := L) AR) s ar σ fl4_abi.label.TCBSetBreakpoint p ⟨length, buf, call, slot, extra⟩
      blk call don slbl args ci sl excaps buffer := by
  have hP := hX.rel.1
  have htcb := (hX.curTcb hcur).1
  have hDS : DState (L := L) Z.th s σ Z.G := ⟨hX.rel.2.1, hDI, hX.rel.2.2.1⟩
  have hdec0 : specDec false slbl args ci sl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.decodeFl4SetBreakpoint (Z := Unit) buffer p.bv) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl args (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_ext hlbl hext]; rfl
  unfold TcbOKX
  rw [decode_setbp_eq arI s ar p _ hstall, hdec0]
  have hc : (⟨length, buf, call, slot, extra⟩ : tcb.Ctx).buf = buf := rfl
  obtain ⟨bp, h0, g0⟩ := arg_rel hA hct hcur _ hc 0#u64 (by decide)
  obtain ⟨vaddr, h1, g1⟩ := arg_rel hA hct hcur _ hc 1#u64 (by decide)
  obtain ⟨ty, h2, g2⟩ := arg_rel hA hct hcur _ hc 2#u64 (by decide)
  obtain ⟨size, h3, g3⟩ := arg_rel hA hct hcur _ hc 3#u64 (by decide)
  obtain ⟨rw, h4, g4⟩ := arg_rel hA hct hcur _ hc 4#u64 (by decide)
  rw [set_bp_checked_eq s p _ h0 h1 h2 h3 h4]
  have hsp := set_bp_spec_run σ buffer p.bv g0 g1 g2 g3 g4
  have hrel := bpErr_rel bp vaddr ty size rw
  cases hF : bpErrF bp vaddr ty size rw with
  | some e =>
    cases hS : bpErrS bp vaddr.bv ty.bv size.bv rw.bv with
    | none => rw [hF, hS] at hrel; exact hrel.elim
    | some e' =>
      rw [hF, hS] at hrel
      dsimp only at hrel
      dsimp only
      simp only [bind_tc_ok]
      refine (WP.spec_ok _).2 (Or.inl ⟨e, rfl, rfl, ⟨e', ?_, hrel⟩, ⟨Z, hX⟩⟩)
      apply run_liftME_err
      rw [hsp, hS]
  | none =>
    cases hS : bpErrS bp vaddr.bv ty.bv size.bv rw.bv with
    | some e' => rw [hF, hS] at hrel; exact hrel.elim
    | none =>
    have hbpv := bpErrF_bp hF
    simp only
    obtain ⟨s1, σ1, hrc1, hs1, hst1, -, -, -, -, -⟩ := restart_dstate Z.th hP s σ Z.G hDS ct hct hcur htcb hact
    have hst1' : Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) := by
      rw [← hcur]; exact hst1
    obtain ⟨hX1, -, -⟩ := hX.restart' hC hcur hs1 hst1'
    rw [hrc1]; simp only [bind_ok]
    have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.decodeFl4SetBreakpoint (Z := Unit) buffer p.bv)).run σ =
        ({(.ok (.invokeFl4TCB (.setBreakpoint p.bv bp.bv vaddr.bv ty.bv size.bv rw.bv)), σ)}, False) := by
      apply run_liftME_ok
      rw [hsp, hS]
    obtain ⟨Q, R0, hc', -⟩ := hX1.fin.1.1.1.lists
    have hpf := (hc'.tcbs p hpT).fits
    have hin : (do
        let s2 ← debug.set_breakpoint st s1 p bp vaddr ty size rw
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2)) ⦃ x =>
          ∃ v, x = (.Ok (), L.wr (L.wr s1 (dbgA p bp) vaddr) (dbgA p 5#u64) v) ⦄ :=
      WP.spec_bind (set_bp_wr (st := st) s1 p bp vaddr ty size rw) (fun s2 ⟨v, h⟩ => (WP.spec_ok _).2 ⟨v, by rw [h]⟩)
    refine WP.spec_bind hin ?_
    rintro x ⟨v, rfl⟩
    have hX2 := (hX1.tcbWrA hpT (dbgA p bp) (448 + 8 * bp.val) (by omega)
      (by rw [dbgA_val (i := bp) (by omega) (by omega)]; omega) vaddr).tcbWrA hpT (dbgA p 5#u64) (448 + 40) (by omega)
      (by rw [dbgA_val (by omega) (by decide)]; simp) v
    refine (WP.spec_ok _).2 (Or.inr ⟨_, DecOut.of_eq hdec, σ1, hst1, (.ok [], σ1), rfl,
      ⟨Z.th, Z.G, Or.inl ⟨rfl, rfl⟩, hX2.rel.1, hX2.rel.2.1, hX2.rel.2.2.1, hX2.rel.2.2.2.1,
        hX2.rel.2.2.2.2.1⟩, ⟨Z, hX2⟩⟩)

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The Thread cap's labels still open** [W] once SetBreakpoint is proved:
ReadFPU, WriteFPU, SetTimer. -/
structure TcbXOpen3 (X : S → A → Fl4Spec.State Unit → Prop) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (lbl : U64) (p : U64) (c : tcb.Ctx) (blk call don : Bool) (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) : Prop where
  readFPU : lbl = fl4_abi.label.TCBReadFPU →
    TcbOKX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer
  writeFPU : lbl = fl4_abi.label.TCBWriteFPU →
    TcbOKX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer
  setTimer : lbl = fl4_abi.label.TCBSetTimer →
    TcbOKX (L := L) arI X s ar σ lbl p c blk call don slbl args ci sl excaps buffer

/-- **`TcbXOpen4` with SetBreakpoint proved** (`tcb_set_bpX`; its five
arguments by `ArgRel` [J]). -/
theorem tcbXOpen4_of {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (hX : XTopAt (L := L) AR Z s ar σ) (hC : CurRun σ) (hTh : ∀ t, Z.th t = some .tcb → t ∈ Z.T)
    (hDI : DelInv Z.th (L.mem s)) (lbl length : U64) (p : U64) (hp : Z.th p = some .tcb)
    (blk call don : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ct : U64)
    (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = tcbLabelOf lbl)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (hext : Fl4Spec.genInvocationType slbl = .invalidInvocation → Fl4Spec.fl4TcbExtLabelOf slbl = tcbExtOf lbl)
    (hstall' : ∀ q, smp.remote_tcb_stall st arI s ar q = ok (s, ar))
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hA5 : ArgRel (st := st) s σ ct buf buffer 5)
    (hO : TcbXOpen3 (L := L) arI (XTop (L := L) AR) s ar σ lbl p ⟨length, buf, call, cslotAddr sl, extra⟩ blk call
      don slbl args ci sl excaps buffer) :
    TcbXOpen4 (L := L) arI (XTop (L := L) AR) s ar σ lbl p ⟨length, buf, call, cslotAddr sl, extra⟩ blk call
      don slbl args ci sl excaps buffer := by
  refine ⟨?_, hO.readFPU, hO.writeFPU, hO.setTimer⟩
  rintro rfl
  obtain ⟨hg, he⟩ := ext_lbl hlbl hext (by simp [tcbLabelOf]) (show tcbExtOf _ = some .setBreakpoint by
    simp [tcbExtOf])
  exact tcb_set_bpX arI s ar σ hX hC hDI p (hTh p hp) slbl hg he length buf ct hct hcur hact (hstall' p) buffer hA5
    call _ extra blk don args ci sl excaps

end

end

end Fl4Proofs.P3
