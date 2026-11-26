/-
# P2 (line pte, gen 8): the plan side of the PageMap arm (`X86PageMap`) of the frame-cap invocation path

`localinv.plan_with` at `X86PageMap` (`crates/fl4-core/src/localinv.rs` l. 238-254): the invoked slot's cap is read
once (`Plan.read_cap`, the slot's two cap words recorded as seen), it must be a small RAM frame cap
(`small_ram_frame`), `extra[0]` must be non-null and hold a mapped PML4 cap `Pml4 root true _`, the attribute check
`map_attr_local` (x86_64: always true) passes, and the walk `page_entry root vaddr` (`vaddr` = message register 0,
`R10`; `None` above `USER_TOP` or on a missing level) gives the leaf entry `e`. The plan then locks the slot (32 bytes)
and `e` (`add_pte`: `pte := n` before the add, 8 bytes in fl4-sync `local_invocation`).

* (`plan_add_at` is the shared copy in `P2/PteLockRS.lean`);
* **`plan_with_mapF`**: what `plan_with` decides at `X86PageMap`: the frame cap at the slot, the PML4 cap at
  `extra[0]`, the walk's result `some e`, the slot locked (when non-zero), and for `e ≠ 0` the PTE index:
  `p.pte < p.n` and `p.locks[p.pte] = e`; the seen words are the slot's `CAP0` / `CAP1`.

This is the input `PtePlanLocked` (P2/E2EP.lean) needs from the plan: its lock half follows with the glue's held
plan locks (`ptePlanLocked_of`); its [J] half (`e ∈ K.ptes`) is about the walk (`P2/PteLockRS.lean`).
No named premise. New module; no existing statement changes; no `kernel_entry_reach*` touched.
-/
import Fl4Proofs.P2.PteLockRS
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1

section plan
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- The slot's two cap words. -/
def MapW (slot x : U64) : Prop :=
  x = core.num.U64.wrapping_add slot layout.cte.CAP0 ∨ x = core.num.U64.wrapping_add slot layout.cte.CAP1

/-- **What `plan_with` decides at `X86PageMap`, with its locks and seen words** (module docstring). -/
theorem plan_with_mapF {s : S} {t : obj.Tcb} {slot : obj.Slot} {extra : Array obj.Slot 3#usize}
    {p : localinv.Plan} (h : localinv.plan_with st s t fl4_abi.label.X86PageMap slot extra = ok (some p)) :
    ∃ (fp rt asid va root rasid : U64) (mp : Bool) (x : obj.Slot) (e : U64),
      obj.Slot.cap st slot s = ok (.Frame fp .Small rt false mp false asid va) ∧
      Array.index_usize extra 0#usize = ok x ∧ x ≠ 0#u64 ∧
      obj.Slot.cap st x s = ok (.Pml4 root true rasid) ∧
      localinv.page_entry st s root (L.mem s (regA t layout.reg.R10)) = ok (some e) ∧
      (slot ≠ 0#u64 → PHeld p slot) ∧
      (e ≠ 0#u64 → p.pte.val < p.n.val ∧ p.locks.val[p.pte.val]? = some e) ∧
      SeenAddr (MapW slot) p := by
  unfold localinv.plan_with at h
  obtain ⟨q, eq, h⟩ := bind_eq_ok h
  obtain ⟨cap, -, h⟩ := bind_eq_ok h
  unfold localinv.Plan.new at eq
  have hq := ok_inj_ff eq
  subst hq
  rw [if_neg lbl_map_ne_copy, if_neg lbl_map_ne_mint, if_neg lbl_map_ne_del] at h
  obtain ⟨b, eb, h⟩ := bind_eq_ok h
  unfold localinv.is_page_map at eb
  have hb : b = true := by simpa using (ok_inj_ff eb).symm
  subst hb
  rw [if_pos rfl] at h
  obtain ⟨⟨fr, q1⟩, efr, h⟩ := bind_eq_ok h
  have hc := read_cap_new (st := st) (by rfl) efr
  simp only at hc
  obtain ⟨c1n, c1s, c1l, c1nn, c1p, c1o⟩ := plan_read_cap_eq efr (by simp)
  simp only at c1n c1s c1l c1nn c1p c1o
  obtain ⟨b1, eb1, h⟩ := bind_eq_ok h
  cases b1
  · simp at h
  have hfr : ∃ fp rt mp asid va, fr = .Frame fp .Small rt false mp false asid va := by
    unfold localinv.small_ram_frame at eb1
    cases fr with
    | Frame fp fs rt d m ep asid va =>
      cases fs <;> cases d <;> cases ep <;> simp at eb1
      exact ⟨fp, rt, m, asid, va, rfl⟩
    | _ => simp at eb1
  obtain ⟨fp, rt, mp, asid, va, hfe⟩ := hfr
  rw [hfe] at hc
  replace h := (if_pos (rfl : true = true)).symm.trans h
  obtain ⟨x, ex, h⟩ := bind_eq_ok h
  obtain ⟨b2, eb2, h⟩ := bind_eq_ok h
  unfold obj.Slot.is_null at eb2
  have hb2 : b2 = decide (x = 0#u64) := (ok_inj_ff eb2).symm
  subst hb2
  by_cases hx0 : x = 0#u64
  · replace h := (if_pos (show decide (x = 0#u64) = true by simpa using hx0)).symm.trans h
    simp at h
  replace h := (if_neg (show ¬ (decide (x = 0#u64) = true) by simpa using hx0)).symm.trans h
  obtain ⟨c, ec, h⟩ := bind_eq_ok h
  cases c
  case Pml4 root b3 rasid =>
    cases b3
    · replace h := (if_neg (show ¬ (false = true) by simp)).symm.trans h
      simp at h
    replace h := (if_pos (rfl : true = true)).symm.trans h
    obtain ⟨i, -, h⟩ := bind_eq_ok h
    obtain ⟨b4, eb4, h⟩ := bind_eq_ok h
    unfold localinv.map_attr_local at eb4
    have hb4 : b4 = true := (ok_inj_ff eb4).symm
    subst hb4
    replace h := (if_pos (rfl : true = true)).symm.trans h
    obtain ⟨i1, ei1, h⟩ := bind_eq_ok h
    unfold localinv.reg_arg at ei1
    rw [sarg0_reg, reg_ok] at ei1
    have hi1 := ok_inj_ff ei1
    subst hi1
    obtain ⟨o, eo, h⟩ := bind_eq_ok h
    obtain ⟨cf, ecf, h⟩ := bind_eq_ok h
    cases o with
    | none =>
      simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch] at ecf
      cases ok_inj_ff ecf
      simp [core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual] at h
    | some e =>
      simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch] at ecf
      cases ok_inj_ff ecf
      obtain ⟨⟨b5, q2⟩, e2, h⟩ := bind_eq_ok h
      obtain ⟨⟨q3, ok1⟩, e3, h⟩ := bind_eq_ok h
      obtain ⟨hok, hp⟩ := some_if_eq h
      cases b5
      · replace e3 := (if_neg (show ¬ (false = true) by simp)).symm.trans e3
        have e3' := ok_inj_ff e3
        simp only [Prod.mk.injEq] at e3'
        exact absurd (e3'.2.trans hok) (by simp)
      replace e3 := (if_pos (rfl : true = true)).symm.trans e3
      obtain ⟨⟨ok2, q4⟩, e4, e3⟩ := bind_eq_ok e3
      have e3' := ok_inj_ff e3
      simp only [Prod.mk.injEq] at e3'
      have hok2 : ok2 = true := e3'.2.trans hok
      rw [hp, ← e3'.1]
      obtain ⟨a2h, a2d, a2s, a2nn, -, a2p, -⟩ := plan_add_eq e2 rfl
      simp only at a2h a2d a2s a2nn a2p
      have e4' := e4
      unfold localinv.Plan.add_pte at e4'
      obtain ⟨a3h, -, a3s, a3nn, -, a3p, -⟩ := plan_add_eq e4' hok2
      simp only at a3h a3s a3nn a3p
      refine ⟨fp, rt, asid, va, root, rasid, mp, x, e, hc, ex, hx0, ec, eo,
        fun hs => a3h _ (a2d hs), fun he => ?_, ?_⟩
      · obtain ⟨l3, n3, -⟩ := (plan_add_at e4' hok2).2 he
        simp only at l3 n3
        rw [a3p]
        exact ⟨by omega, l3⟩
      · intro j hj hjn
        have es : q4.seen = q1.seen := a3s.trans a2s
        have en : q4.nseen = q1.nseen := a3nn.trans a2nn
        have hj' : j < q1.seen.val.length := by rw [← es]; exact hj
        have := c1s (MapW slot) (fun j _ hj => by simp at hj) (Or.inl rfl) (Or.inr rfl) j hj'
          (by rw [← en]; exact hjn)
        simp only [es]
        exact this
  all_goals simp at h

end plan

end Fl4Proofs.P2.PathObl
