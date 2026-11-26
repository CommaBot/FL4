-- AArch64 port of Fl4Proofs.P2.ProgReifyLeaf (proofs/scratch/a64/port.py): the x86_64 text, re-checked
-- over Fl4CoreA64. Edits beyond the renaming are marked `-- a64:`.
/-
# P2: pilot reifications of extracted leaves as `SProg` trees (line hpz)

The pattern a generator follows for each extracted function (`P2/ProgReify.lean`): a tree `<f>R` written as
the body in `do` notation with the store / Arch threading removed (store and Arch calls become
`SProg.read` / `SProg.write` / …, callees their trees, pure steps `pure` or `SProg.liftR`), and the equation
`<f>R_eq`: `interp` of the tree is the body followed by `ok` of the threaded state. Read-only functions
(`Result R`) keep the state; writing ones (`Result S`) return `()`.
-/
import Fl4ProofsA64.P2.ProgReify
import Fl4ProofsA64.P2.AccessLeaf
import Fl4ProofsA64.P2.GuardGE
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P2.PathObl
open fl4_core_a64

namespace Reif

noncomputable def node_baseR (cpu : U64) : SProg U64 := do
  let i ← SProg.ksBase
  let i1 ← SProg.liftR layout.ks.NODES
  let i2 ← pure (core.num.U64.wrapping_add i i1)
  let i3 ← SProg.liftR layout.node.SIZE
  let i4 ← pure (core.num.U64.wrapping_mul cpu i3)
  pure (core.num.U64.wrapping_add i2 i4)

noncomputable def node_getR (cpu off : U64) : SProg U64 := do
  let i ← node_baseR cpu
  let i1 ← pure (core.num.U64.wrapping_add i off)
  SProg.read i1

noncomputable def cur_threadR : SProg obj.Tcb := do
  let i ← SProg.curCpu
  let i1 ← node_getR i layout.node.CUR_THREAD
  pure i1

def tcb_regR (self r : U64) : SProg U64 := do
  let i ← pure (core.num.U64.wrapping_add self layout.tcb.REGS)
  let i1 ← pure (core.num.U64.wrapping_mul r 8#u64)
  let i2 ← pure (core.num.U64.wrapping_add i i1)
  SProg.read i2

def tcb_set_regR (self r v : U64) : SProg Unit := do
  let i ← pure (core.num.U64.wrapping_add self layout.tcb.REGS)
  let i1 ← pure (core.num.U64.wrapping_mul r 8#u64)
  let i2 ← pure (core.num.U64.wrapping_add i i1)
  SProg.write i2 v

section
variable {S : Type} {A : Type} (st : machine.Store S) (ar : machine.Arch A)

theorem node_baseR_eq (cpu : U64) (s : S) (a : A) :
    interp st ar (node_baseR cpu) s a = (do let v ← obj.node_base st s cpu; ok (v, s, a)) := by
  simp only [node_baseR, obj.node_base, eq_ok_of_spec Fl4ProofsA64.P0.Consts.layout.ks.NODES.spec,
    eq_ok_of_spec Fl4ProofsA64.P0.Consts.layout.node.SIZE.spec, SProg.liftR_ok, SProg.bind_eq_sbind,
    SProg.pure_eq_ret, SProg.sbind, interp_sbind, interp_ksBase', interp_ret', lift, bind_tc_eq,
    Std.bind_assoc, bind_ok]

theorem node_getR_eq (cpu off : U64) (s : S) (a : A) :
    interp st ar (node_getR cpu off) s a = (do let v ← obj.node_get st s cpu off; ok (v, s, a)) := by
  simp only [node_getR, obj.node_get, SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind, interp_sbind,
    node_baseR_eq, interp_read', interp_ret', lift, bind_tc_eq, Std.bind_assoc, bind_ok]

theorem cur_threadR_eq (s : S) (a : A) :
    interp st ar cur_threadR s a = (do let v ← sched.cur_thread st s; ok (v, s, a)) := by
  simp only [cur_threadR, sched.cur_thread, SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind, interp_sbind,
    node_getR_eq, interp_curCpu', interp_ret', lift, bind_tc_eq, Std.bind_assoc, bind_ok]

theorem tcb_regR_eq (self r : U64) (s : S) (a : A) :
    interp st ar (tcb_regR self r) s a = (do let v ← obj.Tcb.reg st self s r; ok (v, s, a)) := by
  simp only [tcb_regR, obj.Tcb.reg, SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind, interp_sbind,
    interp_read', interp_ret', lift, bind_tc_eq, Std.bind_assoc, bind_ok]

theorem tcb_set_regR_eq (self r v : U64) (s : S) (a : A) :
    interp st ar (tcb_set_regR self r v) s a = (do let s' ← obj.Tcb.set_reg st self s r v; ok ((), s', a)) := by
  simp only [tcb_set_regR, obj.Tcb.set_reg, SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind,
    interp_sbind, interp_write', interp_ret', lift, bind_tc_eq, Std.bind_assoc, bind_ok]

end

/-- `NoZero` of a tree built from the safe leaves, `sbind`, `liftR`, `iter`, `if` and `match`. -/
macro "nozero_tac" : tactic => `(tactic| repeat' (first
  | (exact trivial) | (intro) | (apply NoZero.sbind) | (apply NoZero.iter) | (exact NoZero.liftR _)
  | (exact NoZero.read _) | (exact NoZero.readPair _) | (exact NoZero.write _ _) | (exact NoZero.ksBase)
  | (exact NoZero.curCpu) | (exact NoZero.frameMasks) | (exact NoZero.call _) | (split)))

theorem cur_threadR_noZero : NoZero cur_threadR := by
  simp only [cur_threadR, node_getR, node_baseR, SProg.bind_eq_sbind, SProg.pure_eq_ret]
  nozero_tac

/-! ## Pilot: a loop with abstract callees (`sporadic.unblock_check_loop`) -/

theorem u64_sub_ne_div (x y : U64) : (x - y : Result U64) ≠ div := by
  simp only [HSub.hSub, UScalar.sub]
  split
  · exact fail_not_div
  · exact ok_not_div

section
variable {S : Type} {A : Type} (st : machine.Store S) (ar : machine.Arch A)
variable (hoR : obj.Sc → SProg Bool) (popR : obj.Sc → SProg sporadic.Refill)
  (headR : obj.Sc → SProg sporadic.Refill) (setR : obj.Sc → sporadic.Refill → SProg Unit)
variable (hoR_eq : ∀ sc (s : S) (a : A),
    interp st ar (hoR sc) s a = (do let v ← sporadic.head_overlapping st s sc; ok (v, s, a)))
  (popR_eq : ∀ sc (s : S) (a : A),
    interp st ar (popR sc) s a = (do let r ← sporadic.pop_head st s sc; ok (r.1, r.2, a)))
  (headR_eq : ∀ sc (s : S) (a : A),
    interp st ar (headR sc) s a = (do let v ← sporadic.head st s sc; ok (v, s, a)))
  (setR_eq : ∀ sc r (s : S) (a : A),
    interp st ar (setR sc r) s a = (do let s' ← sporadic.set_head st s sc r; ok ((), s', a)))

noncomputable def ucBodyR (hoR : obj.Sc → SProg Bool) (popR headR : obj.Sc → SProg sporadic.Refill)
    (setR : obj.Sc → sporadic.Refill → SProg Unit) (sc : obj.Sc) (fuel : U64) :
    SProg (ControlFlow U64 Unit) := do
  let b ← hoR sc
  if b then
    if fuel > 0#u64 then
      let fuel1 ← SProg.liftR (fuel - 1#u64)
      let old ← popR sc
      let h ← headR sc
      let i ← pure (core.num.U64.wrapping_add h.amount old.amount)
      setR sc { old with amount := i }
      pure (.cont fuel1)
    else pure (.done ())
  else pure (.done ())

include hoR_eq popR_eq headR_eq setR_eq in
theorem ucBodyR_eq (sc : obj.Sc) (fuel : U64) (s : S) (a : A) :
    sporadic.unblock_check_loop.body st sc s fuel =
      interp st ar (ucBodyR hoR popR headR setR sc fuel) s a >>=
        fun r => cfOut (fun x s _ => (s, x)) (fun (_ : Unit) s _ => s) r := by
  simp only [cfOut, sporadic.unblock_check_loop.body, ucBodyR, SProg.bind_eq_sbind, SProg.pure_eq_ret, interp_sbind,
    hoR_eq, bind_tc_eq, Std.bind_assoc, bind_ok]
  congr 1; funext b
  by_cases hb : b = true
  · subst hb
    simp only [if_true]
    by_cases hf : fuel > 0#u64
    · simp only [if_pos hf, interp_sbind, interp_liftR st ar _ (u64_sub_ne_div fuel 1#u64), popR_eq, headR_eq,
        setR_eq, SProg.sbind, interp_ret', bind_tc_eq, Std.bind_assoc, bind_ok, lift]
      rcases result_trichotomy (fuel - 1#u64) with ⟨v, e⟩ | ⟨er, e⟩ | e
      · simp only [e, bind_ok]
        rfl
      · simp only [e, bind_fail]
      · exact absurd e (u64_sub_ne_div fuel 1#u64)
    · simp only [if_neg hf, interp_ret', bind_ok]
  · simp only [Bool.not_eq_true] at hb; subst hb
    simp only [Bool.false_eq_true, if_false, interp_ret', bind_ok]


/-- The loop's measure drops at every `cont` step, on every store. -/
theorem ucBody_dec {sc : obj.Sc} {s s' : S} {fuel fuel' : U64}
    (h : sporadic.unblock_check_loop.body st sc s fuel = ok (.cont (s', fuel'))) : fuel'.val < fuel.val := by
  unfold sporadic.unblock_check_loop.body at h
  obtain ⟨b, -, h⟩ := bind_eq_ok' h
  by_cases hb : b = true
  · rw [if_pos hb] at h
    by_cases hf : fuel > 0#u64
    · rw [if_pos hf] at h
      obtain ⟨f1, e1, h⟩ := bind_eq_ok' h
      obtain ⟨p, -, h⟩ := bind_eq_ok' h
      obtain ⟨hh, -, h⟩ := bind_eq_ok' h
      simp only [lift, bind_tc_ok, bind_ok] at h
      obtain ⟨s2, -, h⟩ := bind_eq_ok' h
      have hq : f1 = fuel' := by
        have := Result.ok_injective h
        injection this with h2
        injection h2
      subst hq
      exact Fl4ProofsA64.P2.ge_sub1_lt hf e1
    · rw [if_neg hf] at h
      exact absurd (Result.ok_injective h) (by intro e; cases e)
  · rw [if_neg hb] at h
    exact absurd (Result.ok_injective h) (by intro e; cases e)

include hoR_eq popR_eq headR_eq setR_eq in
/-- **Pilot loop**: `sporadic.unblock_check_loop` is the budgeted tree loop of `ucBodyR`. -/
theorem ucLoopR_eq (sc : obj.Sc) (fuel : U64) (s : S) (a : A) :
    sporadic.unblock_check_loop st s sc fuel =
      (do let r ← interp st ar (SProg.iter (ucBodyR hoR popR headR setR sc) (fuel.val + 1) fuel) s a
          ok r.2.1) := by
  unfold sporadic.unblock_check_loop
  exact interp_iter st ar _ (ucBodyR hoR popR headR setR sc) (fun x s _ => (s, x)) (fun _ s _ => s)
    (fun x => x.val)
    (fun x s a => by
      show sporadic.unblock_check_loop.body st sc s x = _
      exact ucBodyR_eq st ar hoR popR headR setR hoR_eq popR_eq headR_eq setR_eq sc x s a)
    (fun _ _ _ _ _ _ h => ucBody_dec st h) (fuel.val + 1) fuel s a (Nat.lt_succ_self _)

end

end Reif

end Fl4ProofsA64.P2.PathObl
