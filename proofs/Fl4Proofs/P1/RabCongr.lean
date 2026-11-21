/-
# `resolve_address_bits` read congruence (FL4 #56, m67 (R-a'))

`cspace.resolve_address_bits` reads the store only through `obj.Slot.cap` of
slots `ptr + off * 32` of the CNode caps it walks (the root, then each CNode
cap it reads). So two states agree on a lookup when they agree on the cap
slots of every CNode the walk can reach: a predicate `C` on CNode pointers,
true of the root's, closed under the CNode caps read from a `C` CNode's slots
at the first state, with the two states agreeing on every slot of a `C`
CNode. The proof is the loop's fuel induction (`rab_loop_congr`), in the
direction the fast path needs: a lookup that returns at the first state
returns the same at the second.
-/
import Fl4Proofs.P1.FastRR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core

section
variable {S : Type _} (st : machine.Store S)

/-- The slot `off` of the CNode at `p` (what `obj.Slot.index` returns). -/
abbrev cnSlot (p off : U64) : U64 := core.num.U64.wrapping_add p (core.num.U64.wrapping_mul off layout.cte.SIZE)

/-- `resolve_address_bits_loop` unfolded once. -/
theorem rabLoop_unfold (s : S) (cap : capability.Cap) (cptr n fuel : U64) :
    cspace.resolve_address_bits_loop st cap s cptr n fuel =
      (do
        let r ← cspace.resolve_address_bits_loop.body st s cptr cap n fuel
        match r with
        | ControlFlow.cont x => cspace.resolve_address_bits_loop st x.1 s cptr x.2.1 x.2.2
        | ControlFlow.done z => ok z) := by
  conv_lhs => unfold cspace.resolve_address_bits_loop; rw [loop]
  congr 1
  funext r
  cases r with
  | cont x => obtain ⟨a, b, c⟩ := x; rfl
  | done z => rfl

/-- The loop body reads only the slots of the CNode it walks. -/
theorem rab_body_congr {s s' : S} {cptr n fuel : U64} {cap : capability.Cap}
    (h : ∀ p r gs g, cap = .CNode p r gs g → ∀ off : U64,
      obj.Slot.cap st (cnSlot p off) s' = obj.Slot.cap st (cnSlot p off) s) :
    cspace.resolve_address_bits_loop.body st s' cptr cap n fuel =
      cspace.resolve_address_bits_loop.body st s cptr cap n fuel := by
  cases cap with
  | CNode p r gs g =>
    have hp := h p r gs g rfl
    unfold cspace.resolve_address_bits_loop.body
    simp only [obj.Slot.index, lift, bind_ok, bind_tc_ok, cnSlot] at hp ⊢
    simp only [hp]
  | _ => rfl

theorem sub1_lt {f z : U64} (h0 : ¬ f = 0#u64) (h : f - 1#u64 = ok z) : z.val < f.val := by
  have hf : f.val ≠ 0 := fun e => h0 (UScalar.eq_of_val_eq (by simpa using e))
  obtain ⟨z', hz, hv⟩ := spec_ex_fd (U64.sub_spec (x := f) (y := 1#u64) (by scalar_tac))
  rw [hz] at h
  have e := ok_inj_ff h
  subst e
  simp at hv; omega

/-- A continuing step of the loop body read a cap from a slot of its CNode
and spent one unit of fuel. -/
theorem rab_body_cont {s : S} {cptr n fuel p r gs g : U64} {x : capability.Cap × U64 × U64}
    (h : cspace.resolve_address_bits_loop.body st s cptr (.CNode p r gs g) n fuel = ok (ControlFlow.cont x)) :
    ∃ off : U64, obj.Slot.cap st (cnSlot p off) s = ok x.1 ∧ x.2.2.val < fuel.val := by
  unfold cspace.resolve_address_bits_loop.body at h
  simp only [obj.Slot.index, lift, bind_ok, bind_tc_ok] at h
  revert h
  repeat' (first
    | (with_reducible_and_instances refine eq_bind_imp (fun _ _ => ?_))
    | (with_reducible_and_instances refine eq_bind_imp' (fun _ _ => ?_))
    | (with_reducible refine eq_ite_imp (fun _ => ?_) (fun _ => ?_))
    | (intro h; simp at h; done))
  all_goals (intro h; split at h <;> (try (simp at h; done)))
  all_goals
    have e := ok_inj_ff h
    simp only [ControlFlow.cont.injEq] at e
    subst e
    exact ⟨_, ‹obj.Slot.cap st _ s = ok _›, sub1_lt ‹¬ fuel = 0#u64› ‹fuel - 1#u64 = ok _›⟩

/-- **`resolve_address_bits_loop` read congruence** (fuel induction): with a
predicate `C` on CNode pointers true of the walked cap's, closed under the
CNode caps read from a `C` CNode's slots at `s`, and `s'` agreeing with `s` on
every slot of a `C` CNode, a walk returning at `s` returns the same at `s'`. -/
theorem rab_loop_congr {s s' : S} {cptr : U64} (C : U64 → Prop)
    (hag : ∀ p off, C p → obj.Slot.cap st (cnSlot p off) s' = obj.Slot.cap st (cnSlot p off) s)
    (hcl : ∀ p off p' r' gs' g', C p → obj.Slot.cap st (cnSlot p off) s = ok (.CNode p' r' gs' g') → C p') :
    ∀ (N : Nat) (cap : capability.Cap) (n fuel : U64) (res : core.result.Result cspace.Resolved error.LookupFault),
      fuel.val < N → (∀ p r gs g, cap = .CNode p r gs g → C p) →
      cspace.resolve_address_bits_loop st cap s cptr n fuel = ok res →
      cspace.resolve_address_bits_loop st cap s' cptr n fuel = ok res := by
  intro N
  induction N with
  | zero => intro _ _ _ _ hf; omega
  | succ N ih =>
    intro cap n fuel res hf hc h
    rw [rabLoop_unfold] at h ⊢
    rw [rab_body_congr st (fun p r gs g e off => hag p off (hc p r gs g e))]
    obtain ⟨y, hy, hk⟩ := bind_eq_ok h
    rw [hy]; simp only [bind_ok]
    cases y with
    | done z => exact hk
    | cont x =>
      cases cap with
      | CNode p r gs g =>
        obtain ⟨off, hoff, hlt⟩ := rab_body_cont st hy
        exact ih x.1 x.2.1 x.2.2 res (by omega)
          (fun p' r' gs' g' e => hcl p off p' r' gs' g' (hc _ _ _ _ rfl) (e ▸ hoff)) hk
      | _ => simp [cspace.resolve_address_bits_loop.body] at hy

/-- `resolve_address_bits` congruence (the loop with fuel 65). -/
theorem rab_congr {s s' : S} {root : capability.Cap} {cptr n : U64}
    {res : core.result.Result cspace.Resolved error.LookupFault} (C : U64 → Prop)
    (hag : ∀ p off, C p → obj.Slot.cap st (cnSlot p off) s' = obj.Slot.cap st (cnSlot p off) s)
    (hcl : ∀ p off p' r' gs' g', C p → obj.Slot.cap st (cnSlot p off) s = ok (.CNode p' r' gs' g') → C p')
    (hroot : ∀ p r gs g, root = .CNode p r gs g → C p)
    (h : cspace.resolve_address_bits st s root cptr n = ok res) :
    cspace.resolve_address_bits st s' root cptr n = ok res :=
  rab_loop_congr st C hag hcl 66 root n 65#u64 res (by simp) hroot h

/-- **`lookup_cap` read congruence**: the CSpace root slot and the found slot
read the same at `s'`, and the walk's CNodes satisfy `rab_congr`'s
conditions. -/
theorem lookup_cap_congr {s s' : S} {t sl : U64} {root : capability.Cap} {cptr : U64} {found : cspace.Resolved}
    {c : capability.Cap} (C : U64 → Prop)
    (hsl : obj.Tcb.slot t layout.tcb.SLOT_CTABLE = ok sl) (hroot' : obj.Slot.cap st sl s' = ok root)
    (hag : ∀ p off, C p → obj.Slot.cap st (cnSlot p off) s' = obj.Slot.cap st (cnSlot p off) s)
    (hcl : ∀ p off p' r' gs' g', C p → obj.Slot.cap st (cnSlot p off) s = ok (.CNode p' r' gs' g') → C p')
    (hroot : ∀ p r gs g, root = .CNode p r gs g → C p)
    (hr : cspace.resolve_address_bits st s root cptr cspace.WORD_BITS = ok (core.result.Result.Ok found))
    (hc : obj.Slot.cap st found.slot s' = ok c) :
    cspace.lookup_cap st s' t cptr = ok (core.result.Result.Ok c) := by
  unfold cspace.lookup_cap cspace.lookup_slot
  rw [hsl]; simp only [bind_ok]
  rw [hroot']; simp only [bind_ok]
  rw [rab_congr st C hag hcl hroot hr]; simp only [bind_ok]
  rw [hc]; simp only [bind_ok]

end

end Fl4Proofs.P1
