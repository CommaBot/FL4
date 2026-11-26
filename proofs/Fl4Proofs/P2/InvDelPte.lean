/-
# P2 (line invj, generation 4): the plan side of the CNodeDelete **PTE arm**

stpost's `plan_with_delF` (P2/InvSeen.lean) gives the PTE branch one way: a mapped frame with a non-zero ASID whose
`small_page_entry` is a non-zero `e` ends with `pte < n`. The PTE arm needs the converse, with the lock's address:

* (gen 5) `plan_add_at` / `plan_add_n4` (one `Plan.add`) now come from the shared P2/PteLockRS.lean (par/pte, the
  same statements and proofs as this module's gen-4 copies, which are dropped);
* **`plan_with_delP`**: `plan_with` at `CNodeDelete` with `p.pte < p.n`: the target's cap is a **mapped** small RAM
  frame cap with a non-zero ASID, `small_page_entry` finds a non-zero `e`, and `p.locks[p.pte] = e` (the PTE word
  the glue locks for 8 bytes). Its walk is `plan_with_delF`'s, with the seen-word / lock bookkeeping dropped and the
  `pte` / `n` fields tracked instead (`Plan.new`: `pte = MAX_LOCKS`, `n = 0`; reads and `add` keep `pte`; only
  `add_pte` sets it, to the `n` before its `add`).

No named premise. No existing statement changes.
-/
import Fl4Proofs.P2.InvSeen
import Fl4Proofs.P2.PteLockRS
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField NullOrFrame TcbSlot
  slotOwner)

section plan
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

set_option maxHeartbeats 4000000 in
/-- (invj gen 4) **`plan_with` at `CNodeDelete` with a PTE lock** (module docstring). -/
theorem plan_with_delP {s : S} {t : obj.Tcb} {slot : obj.Slot} {extra : Array obj.Slot 3#usize}
    {p : localinv.Plan} (h : localinv.plan_with st s t fl4_abi.label.CNodeDelete slot extra = ok (some p)) :
    ∃ (cp cr cg cgb dest fp rt asid va : U64) (mp : Bool),
      obj.Slot.cap st slot s = ok (.CNode cp cr cg cgb) ∧
      cspace.lookup_target_slot st s (.CNode cp cr cg cgb) (L.mem s (regA t layout.reg.R10))
        (L.mem s (regA t layout.reg.R8)) = ok (.Ok dest) ∧
      obj.Slot.cap st dest s = ok (.Frame fp .Small rt false mp false asid va) ∧
      (p.pte.val < p.n.val → mp = true ∧ asid ≠ 0#u64 ∧ ∃ e, localinv.small_page_entry st s asid va = ok (some e) ∧
        e ≠ 0#u64 ∧ p.locks.val[p.pte.val]? = some e) := by
  unfold localinv.plan_with at h
  obtain ⟨q, eq, h⟩ := bind_eq_ok h
  obtain ⟨cap, ecap, h⟩ := bind_eq_ok h
  unfold localinv.Plan.new at eq
  have hq := ok_inj_ff eq
  subst hq
  rw [if_neg lbl_del_ne_copy, if_neg lbl_del_ne_mint, if_pos rfl] at h
  obtain ⟨b, eb, h⟩ := bind_eq_ok h
  cases b
  · simp at h
  have hcn : ∃ cp cr cg cgb, cap = .CNode cp cr cg cgb := by
    cases cap <;> simp at eb ⊢
  obtain ⟨cp, cr, cg, cgb, rfl⟩ := hcn
  simp only [↓reduceIte] at h
  obtain ⟨i, ei, h⟩ := bind_eq_ok h
  obtain ⟨i1, ei1, h⟩ := bind_eq_ok h
  obtain ⟨r, er, h⟩ := bind_eq_ok h
  obtain ⟨o, eo, h⟩ := bind_eq_ok h
  obtain ⟨cf, ecf, h⟩ := bind_eq_ok h
  unfold localinv.reg_arg at ei ei1
  rw [sarg0_reg, reg_ok] at ei
  rw [sarg1_reg, reg_ok] at ei1
  have hi := ok_inj_ff ei
  have hi1 := ok_inj_ff ei1
  subst hi hi1
  cases r with
  | Err e =>
    simp only [core.result.Result.ok] at eo
    cases ok_inj_ff eo
    simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch] at ecf
    cases ok_inj_ff ecf
    simp [core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual] at h
  | Ok dest =>
    simp only [core.result.Result.ok] at eo
    cases ok_inj_ff eo
    simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch] at ecf
    cases ok_inj_ff ecf
    try simp only at h
    obtain ⟨⟨c, q1⟩, ec, h⟩ := bind_eq_ok h
    try simp only [uncurry_apply_pair] at h
    try dsimp only at h
    have hc := read_cap_new (st := st) (by rfl) ec
    simp only at hc
    obtain ⟨c1n, c1s, c1l, c1nn, c1p, c1o⟩ := plan_read_cap_eq ec (by simp)
    obtain ⟨i2, ei2, h⟩ := bind_eq_ok h
    obtain ⟨⟨i3, q2⟩, e2, h⟩ := bind_eq_ok h
    try simp only [uncurry_apply_pair] at h
    try dsimp only at h
    obtain ⟨i4, ei4, h⟩ := bind_eq_ok h
    obtain ⟨⟨i5, q3⟩, e3, h⟩ := bind_eq_ok h
    try simp only [uncurry_apply_pair] at h
    try dsimp only at h
    simp only [lift, ok.injEq] at ei2 ei4
    subst ei2 ei4
    have c1n' : q1.nseen.val = 2 := by simpa using c1n
    obtain ⟨r2v, r2n, r2s, r2l, r2nn, r2p, r2o⟩ := plan_read_eq e2 (by omega)
    have r2n' : q2.nseen.val = 3 := by simp only at r2n; omega
    obtain ⟨r3v, r3n, r3s, r3l, r3nn, r3p, r3o⟩ := plan_read_eq e3 (by omega)
    simp only at r2v r3v r2n r3n r2l r3l r2nn r3nn r2p r3p r2o r3o
    subst r2v r3v
    obtain ⟨nx, enx, h⟩ := bind_eq_ok h
    obtain ⟨b1, eb1, h⟩ := bind_eq_ok h
    cases b1
    · simp at h
    have hfr : ∃ fp rt mp asid va, c = .Frame fp .Small rt false mp false asid va := by
      unfold localinv.small_ram_frame at eb1
      cases c with
      | Frame fp fs rt d m ep asid va =>
        cases fs <;> cases d <;> cases ep <;> simp at eb1
        exact ⟨fp, rt, m, asid, va, rfl⟩
      | _ => simp at eb1
    obtain ⟨fp, rt, mp, asid, va, rfl⟩ := hfr
    simp only [↓reduceIte] at h
    obtain ⟨⟨b2, q4⟩, e4, h⟩ := bind_eq_ok h
    try simp only [uncurry_apply_pair] at h
    try dsimp only at h
    cases b2
    · simp at h
    simp only [↓reduceIte] at h
    obtain ⟨⟨b3, q5⟩, e5, h⟩ := bind_eq_ok h
    try simp only [uncurry_apply_pair] at h
    try dsimp only at h
    cases b3
    · simp at h
    simp only [↓reduceIte] at h
    obtain ⟨⟨b4, q6⟩, e6, h⟩ := bind_eq_ok h
    try simp only [uncurry_apply_pair] at h
    try dsimp only at h
    cases b4
    · simp at h
    simp only [↓reduceIte] at h
    have a4 := plan_add_eq e4 rfl
    have a5 := plan_add_eq e5 rfl
    have a6 := plan_add_eq e6 rfl
    simp only at a4 a5 a6
    have p6 : q6.pte = localinv.MAX_LOCKS := by
      rw [a6.2.2.2.2.2.1, a5.2.2.2.2.2.1, a4.2.2.2.2.2.1, r3p, r2p, c1p]
    have n6 : q6.n.val ≤ 4 := by
      have n3 : q3.n.val = 0 := by rw [r3nn, r2nn, c1nn]; rfl
      have h4 := plan_add_n4 e4 rfl (by omega)
      have h5 := plan_add_n4 e5 rfl h4
      exact plan_add_n4 e6 rfl h5
    have hno : ¬ q6.pte.val < q6.n.val := by rw [p6, maxLocks_val]; omega
    refine ⟨cp, cr, cg, cgb, dest, fp, rt, asid, va, mp, ecap, er, hc, ?_⟩
    cases mp with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨-, rfl⟩ := some_if_eq h
      exact fun hlt => absurd hlt hno
    | true =>
      simp only [↓reduceIte] at h
      by_cases hA : asid = 0#u64
      · subst hA
        simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
        obtain ⟨-, rfl⟩ := some_if_eq h
        exact fun hlt => absurd hlt hno
      · have hA' : (asid != 0#u64) = true := by simpa using hA
        rw [if_pos hA'] at h
        obtain ⟨o1, eo1, h⟩ := bind_eq_ok h
        cases o1 with
        | none =>
          simp only at h
          obtain ⟨-, rfl⟩ := some_if_eq h
          exact fun hlt => absurd hlt hno
        | some e =>
          simp only at h
          obtain ⟨⟨ok1, q7⟩, e7, h⟩ := bind_eq_ok h
          try simp only [uncurry_apply_pair] at h
          try dsimp only at h
          obtain ⟨hok, rfl⟩ := some_if_eq h
          subst hok
          unfold localinv.Plan.add_pte at e7
          have a7 := plan_add_eq e7 rfl
          have b7 := plan_add_at e7 rfl
          simp only at a7 b7
          intro hlt
          have p7 : p.pte = q6.n := a7.2.2.2.2.2.1
          by_cases he0 : e = 0#u64
          · have e7' := b7.1 he0
            rw [e7'] at hlt
            simp at hlt
          · obtain ⟨hl, -, -⟩ := b7.2 he0
            refine ⟨rfl, hA, e, eo1, he0, ?_⟩
            rw [p7]
            exact hl

end plan

end Fl4Proofs.P2.PathObl
