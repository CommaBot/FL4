/-
# P2 (line invj, generation 8): a planned Delete of a live-mapped frame cap takes the PTE arm

**`plan_with_delP_lt`** (the converse half of gen 4's `plan_with_delP`, its proof copied up to the arm split): when
`plan_with` plans a CNodeDelete, the invoked slot holds a CNode cap, the target slot `dest` is found, and if `dest`
holds a mapped small frame cap with a non-zero ASID whose `small_page_entry` is a non-zero entry `e`, the plan's PTE
lock index is below its lock count (`p.pte < p.n`: the PTE arm). **`invArmP_of`**: `InvArmP` at a state where the
current thread's message is a CNodeDelete and its target holds such a cap.

Heartbeats: `plan_with_delP_lt` keeps `plan_with_delP`'s `maxHeartbeats 4000000`. No named premise. New module.
-/
import Fl4Proofs.P2.InvDelPteEnt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1

section plan
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

set_option maxHeartbeats 4000000 in
/-- (invj gen 8) **A planned Delete of a live-mapped small frame cap is on the PTE arm** (module docstring). -/
theorem plan_with_delP_lt {s : S} {t : obj.Tcb} {slot : obj.Slot} {extra : Array obj.Slot 3#usize}
    {p : localinv.Plan} (h : localinv.plan_with st s t fl4_abi.label.CNodeDelete slot extra = ok (some p)) :
    ∃ (cp cr cg cgb dest : U64), obj.Slot.cap st slot s = ok (.CNode cp cr cg cgb) ∧
      cspace.lookup_target_slot st s (.CNode cp cr cg cgb) (L.mem s (regA t layout.reg.R10))
        (L.mem s (regA t layout.reg.R8)) = ok (.Ok dest) ∧
      ∀ fp rt asid va e, obj.Slot.cap st dest s = ok (.Frame fp .Small rt false true false asid va) →
        asid ≠ 0#u64 → localinv.small_page_entry st s asid va = ok (some e) → e ≠ 0#u64 →
        p.pte.val < p.n.val := by
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
    refine ⟨cp, cr, cg, cgb, dest, ecap, er, fun fp' rt' asid' va' e' hc' hA0 hse he' => ?_⟩
    rw [hc] at hc'
    have ec := ok_inj_ff hc'
    simp only [capability.Cap.Frame.injEq, and_true, true_and] at ec
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := ec
    simp only [↓reduceIte] at h
    have hA' : (asid != 0#u64) = true := by simpa using hA0
    rw [if_pos hA'] at h
    obtain ⟨o1, eo1, h⟩ := bind_eq_ok h
    rw [hse] at eo1
    obtain rfl := ok_inj_ff eo1
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
    have p7 : p.pte = q6.n := a7.2.2.2.2.2.1
    obtain ⟨-, hn, -⟩ := b7.2 he'
    rw [p7, hn]
    omega

/-- (invj gen 8) **`InvArmP` from the plan** at a state whose current thread invokes CNodeDelete on a target holding
a live-mapped small frame cap (module docstring). -/
theorem invArmP_of {s : S} {n : I64} {p : localinv.Plan} (hp : localinv.plan st s n = ok (some p))
    (hlbl : ∀ t info, sched.cur_thread st s = ok t → msg.msg_info st s t = ok info →
      info.label = fl4_abi.label.CNodeDelete)
    (hmap : ∀ cp cr cg cgb dest, obj.Slot.cap st p.slot s = ok (.CNode cp cr cg cgb) →
      cspace.lookup_target_slot st s (.CNode cp cr cg cgb) (L.mem s (regA (L.curW s) layout.reg.R10))
        (L.mem s (regA (L.curW s) layout.reg.R8)) = ok (.Ok dest) →
      ∃ fp rt asid va e, obj.Slot.cap st dest s = ok (.Frame fp .Small rt false true false asid va) ∧
        asid ≠ 0#u64 ∧ localinv.small_page_entry st s asid va = ok (some e) ∧ e ≠ 0#u64) :
    InvArmP st p s := by
  intro t info ht hi
  have hl := hlbl t info ht hi
  refine ⟨hl, ?_⟩
  obtain ⟨t', info', ex, ht', hi', hpw⟩ := planD_of_plan hp
  have et : t = L.curW s := ok_inj_ff (ht.symm.trans (cur_thread_ok s))
  have et' : t' = L.curW s := ok_inj_ff (ht'.symm.trans (cur_thread_ok s))
  subst et et'
  have ei : info' = info := ok_inj_ff (hi'.symm.trans hi)
  subst ei
  rw [hl] at hpw
  obtain ⟨cp, cr, cg, cgb, dest, hcap, hlk, hlt⟩ := plan_with_delP_lt hpw
  obtain ⟨fp, rt, asid, va, e, hc, hA, hse, he⟩ := hmap cp cr cg cgb dest hcap hlk
  exact hlt fp rt asid va e hc hA hse he

end plan

end Fl4Proofs.P2.PathObl
