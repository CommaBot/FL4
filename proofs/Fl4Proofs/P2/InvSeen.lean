/-
# P2 (line stpost, generation 13): the plan side of the CNodeDelete-no-PTE arm

What `localinv.plan` decided at the entry (`InvQF`: `InvQ`'s plan, arm and locks, `InvLk`'s lookup) gives the
decode block (`DelEnt`) and discharges the two [J] premises `hSeen` and `hps` of `inv_pathsKA`.

* `PHeld`, `SeenAddr`: a plan holds a lock on `y` (among `locks[0..n)`); every recorded seen address satisfies `D`;
* `plan_read_eq`, `plan_read_cap_eq`, `plan_add_eq`, `some_if_eq`: one step of the plan builder;
* **`plan_with_delF`**: `plan_with` at `CNodeDelete` (the gen-9 `plan_with_del` walk, extended): the invoked cap is
  a CNode cap, the target `dest` from `R10` / `R8`, its small RAM frame cap, the locks on `dest` / its `PREV` word /
  `Slot.next` (when non-zero), the seen words (`dest`'s four words) and the PTE branch (a mapped frame with a
  non-zero ASID whose `small_page_entry` is a non-zero `e` ends with `pte < n`);
* `lookup_slot_cn`, `lts_cn`: a lookup's slot is a radix-masked slot of a CNode of the walk's closure;
* **`del_core`**: from `InvQF` at the entry, all of the above at the entry, with the walk;
* **`delEnt_of`** / **`delEnt_at`**: `DelEnt` from `InvQF`, [J] `InvMapJ`, [J] `InvCdtJ`, [J] `hz` (`0 ∉ K.slots`);
* **`invSeen_of`**: `InvSeenRS … (InvQF …)` from [J] `hz` alone (the seen words are `dest`'s, `dest` locked);
* **`invPs_of`**: `inv_pathsKA`'s `hps` for `Q := InvQF` (no premise: the invoked slot is a capability slot
  holding a CNode cap, gate-owned).

Named premises: [J] `hz : 0 ∉ K.slots` (the null slot address is no capability slot: `Plan.add` skips a zero
address, so `dest`'s lock needs `dest ≠ 0`), [J] `InvMapJ`, [J] `InvCdtJ` (definitions in `InvDelEnt`).
No existing statement changes; no `kernel_entry_reach*` is touched.
-/
import Fl4Proofs.P2.InvDelEnt
import Fl4Proofs.P3.StPostInvAcc
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField NullOrFrame TcbSlot
  slotOwner)

section plan
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- The plan holds a lock on `y` (one of `locks[0..n)`). -/
def PHeld (q : localinv.Plan) (y : U64) : Prop := ∃ j : Nat, j < q.n.val ∧ q.locks.val[j]? = some y

/-- Every recorded seen address of the plan satisfies `D`. -/
def SeenAddr (D : U64 → Prop) (q : localinv.Plan) : Prop :=
  ∀ (j : Nat) (hj : j < q.seen.val.length), j < q.nseen.val → D (q.seen.val[j]'hj).1

theorem maxLocks_val : localinv.MAX_LOCKS.val = 4 := by unfold localinv.MAX_LOCKS; rfl

theorem plan_read_eq {q : localinv.Plan} {s : S} {a : U64} {x : U64 × localinv.Plan}
    (h : localinv.Plan.read st q s a = ok x) (hn : q.nseen.val < 4) :
    x.1 = L.mem s a ∧ x.2.nseen.val = q.nseen.val + 1 ∧
      (∀ D, SeenAddr D q → D a → SeenAddr D x.2) ∧
      x.2.locks = q.locks ∧ x.2.n = q.n ∧ x.2.pte = q.pte ∧ x.2.ok_words = q.ok_words := by
  unfold localinv.Plan.read at h
  have nlt : ¬ (q.nseen >= localinv.MAX_LOCKS) := by
    show ¬ (localinv.MAX_LOCKS ≤ q.nseen)
    intro hc; have h2 : localinv.MAX_LOCKS.val ≤ q.nseen.val := hc; rw [maxLocks_val] at h2; omega
  rw [if_neg nlt] at h
  obtain ⟨v, ev, h⟩ := bind_eq_ok h
  obtain ⟨a1, ea1, h⟩ := bind_eq_ok h
  obtain ⟨n1, en1, h⟩ := bind_eq_ok h
  rw [L.read_eq] at ev
  have hv : L.mem s a = v := ok_inj_ff ev
  have hlen : q.seen.val.length = 4 := by have hp := q.seen.property; simpa using hp
  have hl : q.nseen.val < q.seen.length := by
    simp only [Aeneas.Std.Array.length]; omega
  rw [eq_of_spec_fd (Aeneas.Std.Array.update_spec q.seen q.nseen (a, v) hl)] at ea1
  have ha1 : q.seen.set q.nseen (a, v) = a1 := ok_inj_ff ea1
  obtain ⟨z, ze, zv⟩ := spec_ex_fd (Usize.add_spec (x := q.nseen) (y := 1#usize) (by scalar_tac))
  rw [ze] at en1
  have hz : z = n1 := ok_inj_ff en1
  subst hz ha1
  cases ok_inj_ff h
  refine ⟨hv.symm, by simpa using zv, fun D hD hDa => ?_, rfl, rfl, rfl, rfl⟩
  intro j hj hjn
  have hzv : z.val = q.nseen.val + 1 := by simpa using zv
  simp only [Aeneas.Std.Array.set_val_eq] at hj ⊢
  by_cases e : j = q.nseen.val
  · subst e
    simp only [List.getElem_set_self]
    exact hDa
  · rw [List.getElem_set_ne (Ne.symm e)]
    exact hD j (by simpa using hj) (by simp only at hjn; omega)

theorem plan_read_cap_eq {q : localinv.Plan} {s : S} {sl : obj.Slot} {x : capability.Cap × localinv.Plan}
    (h : localinv.Plan.read_cap st q s sl = ok x) (hn : q.nseen.val + 2 ≤ 4) :
    x.2.nseen.val = q.nseen.val + 2 ∧
      (∀ D, SeenAddr D q → D (core.num.U64.wrapping_add sl layout.cte.CAP0) →
        D (core.num.U64.wrapping_add sl layout.cte.CAP1) → SeenAddr D x.2) ∧
      x.2.locks = q.locks ∧ x.2.n = q.n ∧ x.2.pte = q.pte ∧ x.2.ok_words = q.ok_words := by
  unfold localinv.Plan.read_cap at h
  obtain ⟨i, ei, h⟩ := bind_eq_ok h
  obtain ⟨⟨w0, q1⟩, e1, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  try dsimp only at h
  obtain ⟨i1, ei1, h⟩ := bind_eq_ok h
  obtain ⟨⟨w1, q2⟩, e2, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  try dsimp only at h
  obtain ⟨c, -, h⟩ := bind_eq_ok h
  cases ok_inj_ff h
  simp only [lift, ok.injEq] at ei ei1
  subst ei ei1
  obtain ⟨-, n1, s1, l1, nn1, p1, o1⟩ := plan_read_eq e1 (by omega)
  obtain ⟨-, n2, s2, l2, nn2, p2, o2⟩ := plan_read_eq e2 (by simp only at n1; omega)
  simp only at n1 n2 s1 s2 l1 l2 nn1 nn2 p1 p2 o1 o2 ⊢
  refine ⟨by omega, fun D hD h0 h1 => s2 D (s1 D hD h0) h1, l2.trans l1, nn2.trans nn1, p2.trans p1, o2.trans o1⟩

theorem plan_add_eq {q : localinv.Plan} {a : U64} {x : Bool × localinv.Plan}
    (h : localinv.Plan.add q a = ok x) (ht : x.1 = true) :
    (∀ y, PHeld q y → PHeld x.2 y) ∧ (a ≠ 0#u64 → PHeld x.2 a) ∧ x.2.seen = q.seen ∧ x.2.nseen = q.nseen ∧
      x.2.ok_words = q.ok_words ∧ x.2.pte = q.pte ∧ (a ≠ 0#u64 → x.2.n.val = q.n.val + 1) := by
  unfold localinv.Plan.add at h
  by_cases h0 : a = 0#u64
  · rw [if_pos h0] at h
    cases ok_inj_ff h
    exact ⟨fun y hy => hy, fun hn => absurd h0 hn, rfl, rfl, rfl, rfl, fun hn => absurd h0 hn⟩
  rw [if_neg h0] at h
  by_cases h1 : q.n >= localinv.MAX_LOCKS
  · rw [if_pos h1] at h
    cases ok_inj_ff h
    simp at ht
  rw [if_neg h1] at h
  have hn : q.n.val < 4 := by
    have h2 : ¬ localinv.MAX_LOCKS.val ≤ q.n.val := fun hc => h1 hc
    rw [maxLocks_val] at h2; omega
  have hlen : q.locks.val.length = 4 := by have hp := q.locks.property; simpa using hp
  have hl : q.n.val < q.locks.length := by
    simp only [Aeneas.Std.Array.length]; omega
  obtain ⟨a1, ea1, h⟩ := bind_eq_ok h
  obtain ⟨n1, en1, h⟩ := bind_eq_ok h
  rw [eq_of_spec_fd (Aeneas.Std.Array.update_spec q.locks q.n a hl)] at ea1
  have ha1 : q.locks.set q.n a = a1 := ok_inj_ff ea1
  obtain ⟨z, ze, zv⟩ := spec_ex_fd (Usize.add_spec (x := q.n) (y := 1#usize) (by scalar_tac))
  rw [ze] at en1
  have hz : z = n1 := ok_inj_ff en1
  subst hz ha1
  cases ok_inj_ff h
  have hzv : z.val = q.n.val + 1 := by simpa using zv
  refine ⟨fun y ⟨j, hj, hy⟩ => ⟨j, by simp only; omega, ?_⟩, fun _ => ⟨q.n.val, by simp only; omega, ?_⟩,
    rfl, rfl, rfl, rfl, fun _ => hzv⟩
  · simp only [Aeneas.Std.Array.set_val_eq]
    rw [List.getElem?_set_ne (by omega)]
    exact hy
  · simp only [Aeneas.Std.Array.set_val_eq]
    rw [List.getElem?_set_self (by omega)]

theorem some_if_eq {b : Bool} {q p : localinv.Plan} (h : localinv.some_if b q = ok (some p)) :
    b = true ∧ p = q := by
  unfold localinv.some_if at h
  split at h
  · split at h
    · have e := ok_inj_ff h
      simp only [Option.some.injEq] at e
      exact ⟨by assumption, e.symm⟩
    · simp at h
  · simp at h

/-- `dest`'s four words. -/
def DelW (dest x : U64) : Prop :=
  ∃ o : U64, (o = layout.cte.CAP0 ∨ o = layout.cte.CAP1 ∨ o = layout.cte.PREV ∨ o = layout.cte.NEXT) ∧
    x = core.num.U64.wrapping_add dest o

set_option maxHeartbeats 16000000 in
/-- (stpost gen 13) **What `plan_with` decides at `CNodeDelete`, with its locks and seen words** (module
docstring). -/
theorem plan_with_delF {s : S} {t : obj.Tcb} {slot : obj.Slot} {extra : Array obj.Slot 3#usize}
    {p : localinv.Plan} (h : localinv.plan_with st s t fl4_abi.label.CNodeDelete slot extra = ok (some p)) :
    ∃ (cp cr cg cgb dest fp rt asid va : U64) (mp : Bool),
      obj.Slot.cap st slot s = ok (.CNode cp cr cg cgb) ∧
      cspace.lookup_target_slot st s (.CNode cp cr cg cgb) (L.mem s (regA t layout.reg.R10))
        (L.mem s (regA t layout.reg.R8)) = ok (.Ok dest) ∧
      obj.Slot.cap st dest s = ok (.Frame fp .Small rt false mp false asid va) ∧
      (dest ≠ 0#u64 → PHeld p dest) ∧
      (L.mem s (core.num.U64.wrapping_add dest layout.cte.PREV) ≠ 0#u64 →
        PHeld p (L.mem s (core.num.U64.wrapping_add dest layout.cte.PREV))) ∧
      (∀ nx, obj.Slot.next st dest s = ok nx → nx ≠ 0#u64 → PHeld p nx) ∧
      SeenAddr (DelW dest) p ∧
      (mp = true → asid ≠ 0#u64 → ∀ e, localinv.small_page_entry st s asid va = ok (some e) → e ≠ 0#u64 →
        p.pte.val < p.n.val) := by
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
    obtain ⟨a4h, a4d, a4s, a4nn, -, -, -⟩ := plan_add_eq e4 rfl
    obtain ⟨a5h, a5d, a5s, a5nn, -, -, -⟩ := plan_add_eq e5 rfl
    obtain ⟨a6h, a6d, a6s, a6nn, -, -, -⟩ := plan_add_eq e6 rfl
    simp only at a4h a4d a4s a4nn a5h a5d a5s a5nn a6h a6d a6s a6nn
    -- the seen words of `q6`
    have hS6 : SeenAddr (DelW dest) q6 := by
      have s0 : SeenAddr (DelW dest) q1 :=
        c1s _ (fun j _ hj => by simp at hj) ⟨_, Or.inl rfl, rfl⟩ ⟨_, Or.inr (Or.inl rfl), rfl⟩
      have s3 := r3s _ (r2s _ s0 ⟨_, Or.inr (Or.inr (Or.inl rfl)), rfl⟩)
        ⟨_, Or.inr (Or.inr (Or.inr rfl)), rfl⟩
      intro j hj hjn
      have e' : q6.seen = q3.seen := (a6s.trans a5s).trans a4s
      have e'' : q6.nseen = q3.nseen := (a6nn.trans a5nn).trans a4nn
      have hj' : j < q3.seen.val.length := by rw [← e']; exact hj
      have := s3 j hj' (by rw [← e'']; exact hjn)
      simp only [e']
      exact this
    have hLd : dest ≠ 0#u64 → PHeld q6 dest := fun hd => a6h _ (a5h _ (a4d hd))
    have hLp : L.mem s (core.num.U64.wrapping_add dest layout.cte.PREV) ≠ 0#u64 →
        PHeld q6 (L.mem s (core.num.U64.wrapping_add dest layout.cte.PREV)) := fun hd => a6h _ (a5d hd)
    have hnx : ∀ nx', obj.Slot.next st dest s = ok nx' → nx = nx' := by
      intro nx' e
      unfold obj.Slot.next obj.Slot.next_word at e
      simp only [lift, bind_ok, L.read_eq] at e
      unfold obj.Slot.next_of_word at enx
      rw [enx] at e
      try simp only [bind_ok, bind_tc_ok] at e
      exact ok_inj_ff e
    have hLn : ∀ nx', obj.Slot.next st dest s = ok nx' → nx' ≠ 0#u64 → PHeld q6 nx' := by
      intro nx' e hne
      rw [← hnx nx' e] at hne ⊢
      exact a6d hne
    refine ⟨cp, cr, cg, cgb, dest, fp, rt, asid, va, mp, ecap, er, hc, ?_⟩
    cases mp with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨-, rfl⟩ := some_if_eq h
      exact ⟨hLd, hLp, hLn, hS6, fun e => by simp at e⟩
    | true =>
      simp only [↓reduceIte] at h
      by_cases hA : asid = 0#u64
      · subst hA
        simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
        obtain ⟨-, rfl⟩ := some_if_eq h
        exact ⟨hLd, hLp, hLn, hS6, fun _ e => absurd rfl e⟩
      · have hA' : (asid != 0#u64) = true := by simpa using hA
        rw [if_pos hA'] at h
        obtain ⟨o1, eo1, h⟩ := bind_eq_ok h
        cases o1 with
        | none =>
          simp only at h
          obtain ⟨-, rfl⟩ := some_if_eq h
          exact ⟨hLd, hLp, hLn, hS6, fun _ _ e he => by rw [eo1] at he; simp at he⟩
        | some e =>
          simp only at h
          obtain ⟨⟨ok1, q7⟩, e7, h⟩ := bind_eq_ok h
          try simp only [uncurry_apply_pair] at h
          try dsimp only at h
          obtain ⟨hok, rfl⟩ := some_if_eq h
          subst hok
          unfold localinv.Plan.add_pte at e7
          obtain ⟨a7h, a7d, a7s, a7nn, -, a7p, a7n⟩ := plan_add_eq e7 rfl
          simp only at a7h a7d a7s a7nn a7p a7n
          refine ⟨fun hd => a7h _ (hLd hd), fun hd => a7h _ (hLp hd), fun nx' en hne => a7h _ (hLn nx' en hne),
            ?_, fun _ _ e' he' hne => ?_⟩
          · intro j hj hjn
            have hj' : j < q6.seen.val.length := by rw [← a7s]; exact hj
            have := hS6 j hj' (by rw [← a7nn]; exact hjn)
            simp only [a7s]
            exact this
          · rw [eo1] at he'
            have ee : e = e' := by have := ok_inj_ff he'; simpa using this
            subst ee
            rw [a7p, a7n hne]
            omega

end plan

/-! ## The walk -/

section walk
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- `lookup_slot`'s slot is a radix-masked slot of a CNode of a closed set containing the root's CNode. -/
theorem lookup_slot_cn {s : S} {t cptr : U64} {x : cspace.Resolved} {C : U64 → U64 → Prop}
    (hroot : ∀ p r gs g, obj.Slot.cap st t s = ok (.CNode p r gs g) → C p r) (hcl : WalkCl (st := st) s C)
    (h : cspace.lookup_slot st s t cptr = ok (.Ok x)) :
    ∃ q r m y, C q r ∧ cspace.mask r = ok m ∧ x.slot = cnSlot q (y &&& m) := by
  unfold cspace.lookup_slot at h
  obtain ⟨sl, hsl, h⟩ := bind_eq_ok h
  rw [tcb_slot_ctable] at hsl
  have e := ok_inj_ff hsl
  subst e
  obtain ⟨root, hr, h⟩ := bind_eq_ok h
  exact rab_loop_slot st C hcl 66 root _ 65#u64 x (by simp) (fun p r gs g e => hroot p r gs g (e ▸ hr)) h

/-- `lookup_target_slot`'s slot likewise. -/
theorem lts_cn {s : S} {root : capability.Cap} {cptr depth : U64} {dest : obj.Slot} {C : U64 → U64 → Prop}
    (hroot : ∀ p r gs g, root = .CNode p r gs g → C p r) (hcl : WalkCl (st := st) s C)
    (h : cspace.lookup_target_slot st s root cptr depth = ok (.Ok dest)) :
    ∃ q r m y, C q r ∧ cspace.mask r = ok m ∧ dest = cnSlot q (y &&& m) := by
  unfold cspace.lookup_target_slot cspace.lookup_slot_for_cnode_op at h
  obtain ⟨b, -, h⟩ := bind_eq_ok h
  cases b
  · simp at h
  rw [if_pos rfl] at h
  split at h
  · simp at h
  split at h
  · simp at h
  obtain ⟨r, er, h⟩ := bind_eq_ok h
  cases r with
  | Err lf => simp at h
  | Ok r1 =>
    simp only at h
    split at h
    · simp at h
    · have e := ok_inj_ff h
      simp only [core.result.Result.Ok.injEq] at e
      obtain ⟨q, r, m, y, hq, hm, hs⟩ := rab_loop_slot st C hcl 66 root _ 65#u64 r1 (by simp) hroot er
      exact ⟨q, r, m, y, hq, hm, by rw [← e, hs]⟩

end walk

/-! ## From `InvQF` at the entry -/

section ent
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayout} {μ : U64 → U64}
  {s : S}

/-- (stpost gen 13) **`InvLk` from the plan at the entry** (`loc_chain_all` clause 8's input `hp`). -/
theorem invLk_of_plan {n : I64} (h : localinv.plan st s n = ok (some p)) : InvLk st p s := by
  obtain ⟨t, info, cptr, r, buf, e, et, -, ec, er, -, -, hs, -⟩ := plan_fields h
  have ht : t = L.curW s := ok_inj_ff (et.symm.trans (cur_thread_ok s))
  subst ht
  rw [reg_ok] at ec
  have hc := ok_inj_ff ec
  subst hc
  exact ⟨r, er, hs.symm⟩

/-- (stpost gen 13) **The arm's facts at the entry from `InvQF`** (no premise): the invoked slot a capability
slot holding a CNode cap, the target, its frame cap, the walk, the locks the plan took (as `Locks`), the seen
words, and the PTE branch refuted by any non-zero entry. -/
theorem del_core (hq : InvQF st Cs Ω Sg Ac Locks p K μ s) :
    ∃ (cp cr cg cgb dest fp rt asid va : U64) (mp : Bool) (C : U64 → U64 → Prop),
      obj.Slot.cap st p.slot s = ok (.CNode cp cr cg cgb) ∧ p.slot ∈ K.slots ∧
      cspace.lookup_target_slot st s (.CNode cp cr cg cgb) (L.mem s (regA (L.curW s) layout.reg.R10))
        (L.mem s (regA (L.curW s) layout.reg.R8)) = ok (.Ok dest) ∧
      obj.Slot.cap st dest s = ok (.Frame fp .Small rt false mp false asid va) ∧
      C cp cr ∧ WalkCl (st := st) s C ∧
      (∀ p r m y, C p r → cspace.mask r = ok m → cnSlot p (y &&& m) ∈ K.slots ∧
        OutsideObjs st K.heap.tcbs Cs s (cnSlot p (y &&& m)) ∧
        OutsideObjs st K.heap.tcbs Cs s (core.num.U64.wrapping_add (cnSlot p (y &&& m)) 8#u64)) ∧
      dest ∈ K.slots ∧ OutsideObjs st K.heap.tcbs Cs s dest ∧
      (dest ≠ 0#u64 → Locks s dest) ∧
      (L.mem s (core.num.U64.wrapping_add dest layout.cte.PREV) ≠ 0#u64 →
        Locks s (L.mem s (core.num.U64.wrapping_add dest layout.cte.PREV))) ∧
      (∀ nx, obj.Slot.next st dest s = ok nx → nx ≠ 0#u64 → Locks s nx) ∧
      (∀ x, SeenW p x → DelW dest x) ∧
      (mp = true → asid ≠ 0#u64 → ∀ e, localinv.small_page_entry st s asid va = ok (some e) → e ≠ 0#u64 →
        False) := by
  obtain ⟨⟨⟨PE, -⟩, ⟨t, info, ex, et, ei, hpw⟩, harm, hlk⟩, ⟨x, hx, hxs⟩⟩ := hq
  have ht : t = L.curW s := ok_inj_ff (et.symm.trans (cur_thread_ok s))
  subst ht
  obtain ⟨hlbl, hnp⟩ := harm _ _ (cur_thread_ok s) ei
  rw [hlbl] at hpw
  obtain ⟨cp, cr, cg, cgb, dest, fp, rt, asid, va, mp, hcap, htg, hdc, hHd, hHp, hHn, hSn, hpte⟩ :=
    plan_with_delF hpw
  obtain ⟨C, hroot, hcl, hC⟩ := PE.walk
  obtain ⟨q0, r0, m0, y0, hq0, hm0, hs0⟩ := lookup_slot_cn hroot hcl hx
  rw [hxs] at hs0
  have hCc : C cp cr := hcl q0 r0 m0 y0 cp cr cg cgb hq0 hm0 (by rw [← hs0]; exact hcap)
  obtain ⟨q1, r1, m1, y1, hq1, hm1, hs1⟩ :=
    lts_cn (fun p r gs g e => by cases e; exact hCc) hcl htg
  have hD := hC q1 r1 m1 y1 hq1 hm1
  rw [← hs1] at hD
  have held : ∀ y, PHeld p y → Locks s y := fun y ⟨j, hj, hy⟩ => hlk j y hj hy
  refine ⟨cp, cr, cg, cgb, dest, fp, rt, asid, va, mp, C, hcap, ?_, htg, hdc, hCc, hcl, hC, hD.1, hD.2.1,
    fun hd => held _ (hHd hd), fun hd => held _ (hHp hd), fun nx e hne => held _ (hHn nx e hne), ?_,
    fun hm hA e he hne => ?_⟩
  · rw [hs0]; exact (hC q0 r0 m0 y0 hq0 hm0).1
  · intro w ⟨i, q, hi, hiM, hidx, hq⟩
    have hM : localinv.MAX_LOCKS.val = 4 := maxLocks_val
    have hiv : i.val < 4 := by have : i.val < localinv.MAX_LOCKS.val := hiM; omega
    have hlen : p.seen.val.length = 4 := by have hp := p.seen.property; simpa using hp
    have hl : i.val < p.seen.length := by simp only [Aeneas.Std.Array.length]; omega
    rw [eq_of_spec_fd (Aeneas.Std.Array.index_usize_spec p.seen i hl)] at hidx
    have e := ok_inj_ff hidx
    subst e hq
    exact hSn i.val (by omega) hi
  · have := hpte hm hA e he hne
    have := hnp
    omega

/-- (stpost gen 13) **`DelEnt` at the entry** from `InvQF` and the [J] facts at `s` (`InvMapJ`, `InvCdtJ` for some
`P` with `P s`; `hz`: `0` is no capability slot). -/
theorem delEnt_of {P : S → Prop} (hPs : P s) (hq : InvQF st Cs Ω Sg Ac Locks p K μ s)
    (hmap : InvMapJ st K P) (hcdt : InvCdtJ st K P) (hz : (0#u64) ∉ K.slots) :
    DelEnt st K Cs Locks p s := by
  obtain ⟨cp, cr, cg, cgb, dest, fp, rt, asid, va, mp, C, hcap, -, htg, hdc, hCc, hcl, hC, hdK, hdO, hLd, hLp,
    hLn, -, hpte⟩ := del_core hq
  have hd0 : dest ≠ 0#u64 := fun e => hz (e ▸ hdK)
  have hunm : mp = false ∨ asid = 0#u64 := by
    cases mp with
    | false => exact Or.inl rfl
    | true =>
      by_cases hA : asid = 0#u64
      · exact Or.inr hA
      · obtain ⟨e, he, hne⟩ := hmap s dest fp rt asid va hPs hdK hdc hA
        exact (hpte rfl hA e he hne).elim
  obtain ⟨hcP, hcN⟩ := hcdt s dest hPs hdK
  exact ⟨cp, cr, cg, cgb, dest, fp, rt, asid, va, mp, C, hcap, htg, hdc, hunm, hCc, hcl, hC, hdK, hdO, hLd hd0,
    fun hp => ⟨hcP hp, hLp hp⟩, fun nx e hne => ⟨hcN nx e hne, hLn nx e hne⟩⟩

/-- (stpost gen 13) **`DelEnt` at every `Pre` state of the path** (`Q := InvQF`), from [J] `InvMapJ`, [J]
`InvCdtJ` (at `Pre`) and [J] `hz`. -/
theorem delEnt_at
    (hmap : ∀ K μ, InvMapJ st K (fun s => SlJAt (L := L) K s ∧ InvQF st Cs Ω Sg Ac Locks p K μ s))
    (hcdt : ∀ K μ, InvCdtJ st K (fun s => SlJAt (L := L) K s ∧ InvQF st Cs Ω Sg Ac Locks p K μ s))
    (hz : ∀ K μ s, SlJAt (L := L) K s → InvQF st Cs Ω Sg Ac Locks p K μ s → (0#u64) ∉ K.slots) :
    ∀ K μ s, SlJAt (L := L) K s → InvQF st Cs Ω Sg Ac Locks p K μ s → DelEnt st K Cs Locks p s :=
  fun K μ s hJ hq => delEnt_of (P := fun s => SlJAt (L := L) K s ∧ InvQF st Cs Ω Sg Ac Locks p K μ s) ⟨hJ, hq⟩ hq
    (hmap K μ) (hcdt K μ) (hz K μ s hJ hq)

/-- (stpost gen 13) **`hSeen` of `inv_pathsKA` for `Q := InvQF`**: the seen words are `dest`'s four words, `dest`
a capability slot whose lock the glue holds ([J] `hz`: `dest ≠ 0`, so `Plan.add` took it). -/
theorem invSeen_of
    (hz : ∀ K μ s, SlJAt (L := L) K s → InvQF st Cs Ω Sg Ac Locks p K μ s → (0#u64) ∉ K.slots) :
    InvSeenRS st Locks p (InvQF st Cs Ω Sg Ac Locks p) := by
  intro K μ s hJ hq x hx
  have PE := hq.1.1.1
  obtain ⟨cp, cr, cg, cgb, dest, fp, rt, asid, va, mp, C, -, -, -, -, -, -, -, hdK, -, hLd, -, -, hSn, -⟩ :=
    del_core hq
  have hd0 : dest ≠ 0#u64 := fun e => hz K μ s hJ hq (e ▸ hdK)
  obtain ⟨o, ho, rfl⟩ := hSn x hx
  have hov : o.val < 32 ∧ o.val % 8 = 0 := by
    rcases ho with rfl | rfl | rfl | rfl <;> simp [layout.cte.CAP0, layout.cte.CAP1, layout.cte.PREV, layout.cte.NEXT]
  exact (PE.lockSlot hdK (hLd hd0) hov.1 hov.2).1

/-- (stpost gen 13) **`hps` of `inv_pathsKA` for `Q := InvQF`** (no premise): the invoked slot is a capability
slot holding a CNode cap, so both cap words are the gate's (`IoPre.slot`). -/
theorem invPs_of :
    ∀ K μ s, SlJAt (L := L) K s → InvQF st Cs Ω Sg Ac Locks p K μ s →
      IoRS (st := st) K Locks s p.slot ∧ IoRS (st := st) K Locks s (core.num.U64.wrapping_add p.slot 8#u64) := by
  intro K μ s _ hq
  have PE := hq.1.1.1
  obtain ⟨cp, cr, cg, cgb, -, -, -, -, -, -, -, hcap, hsK, -⟩ := del_core hq
  exact PE.slot hsK (Or.inr (cap_not_nof hcap (Or.inl ⟨_, _, _, _, rfl⟩)))

end ent

end Fl4Proofs.P2.PathObl
