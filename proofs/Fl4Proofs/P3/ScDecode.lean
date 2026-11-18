/-
P3 (DESIGN.md §9), scheduling contexts: **`decode_sched_control` against l4v
`decode_sched_control_invocation_flags`** (Fl4Spec/Decode.lean): the errors,
and on success the arguments `configure_flags` gets.

FL4 compares the budget and period with `MIN_BUDGET` in ticks (after
`us_to_ticks`), the spec in µs; under `TimeAgree` (`us_to_ticks` exact below
`MAX_PERIOD_US`) the comparisons agree (`TimeAgree.usToTicks_lt`). FL4 has
no test for `MIN_REFILLS ≤ max_refills_cap` (the spec's assertion): a valid
SC cap (`CapWf`: at least `min_sched_context_bits`) has room for two.
-/
import Fl4Proofs.P3.ScConfig
import Fl4Proofs.P3.CnodeCopy
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- FL4's errors and the spec's, with `invalid_capability`. -/
def CErrRel (e : error.Exc) (e' : Fl4Spec.SyscallError) : Prop :=
  SysErrRel e e' ∨ ∃ n : U64, e = .Sys (.InvalidCapability n) ∧ e' = .invalidCapability n.val

/-- After a decode, either FL4 returned the spec's error with nothing
changed, or the spec decodes an invocation and `Q` relates it to FL4's
result. -/
def CPost {α : Type} (σ : Fl4Spec.State Unit) (m : Fl4Spec.SEMonad Unit α) (s : S) (a : A)
    (Q : α → core.result.Result Unit error.Exc × S × A → Prop)
    (res : core.result.Result Unit error.Exc × S × A) : Prop :=
  (∃ e e', res = (.Err e, s, a) ∧ m.run σ = ({(.error e', σ)}, False) ∧ CErrRel e e') ∨
  (∃ inv, m.run σ = ({(.ok inv, σ)}, False) ∧ Q inv res)

theorem CPost.err {α : Type} {σ : Fl4Spec.State Unit} {m : Fl4Spec.SEMonad Unit α} {s : S} {a : A} {Q}
    {e : error.Exc} {e' : Fl4Spec.SyscallError}
    (h : m.run σ = ({(.error e', σ)}, False)) (he : CErrRel e e') :
    (ok ((.Err e, s, a) : core.result.Result Unit error.Exc × S × A)) ⦃ res => CPost σ m s a Q res ⦄ := by
  rw [WP.spec_ok]; exact Or.inl ⟨e, e', rfl, h, he⟩

theorem dec_run_bind {σ ε α β : Type} {m : Fl4Spec.NonDetE σ ε α} {s s' : σ} {x : α}
    (h : m.run s = ({(.ok x, s')}, False)) (f : α → Fl4Spec.NonDetE σ ε β) : (m >>= f).run s = (f x).run s' := by
  rw [ExceptT.run_bind, nd_bind_one h]

theorem ndE_throw_run {α : Type} (e : Fl4Spec.SyscallError) (σ : Fl4Spec.State Unit) :
    (Fl4Spec.NonDetE.throwError e : Fl4Spec.SEMonad Unit α).run σ = ({(.error e, σ)}, False) := rfl

theorem gt_bv (a b : U64) : a > b ↔ a.bv > b.bv := by
  rw [gt_iff_lt, gt_iff_lt, BitVec.lt_def, UScalar.bv_toNat, UScalar.bv_toNat]; exact Iff.rfl

theorem lt_bv (a b : U64) : a < b ↔ a.bv < b.bv := gt_bv b a

theorem ucast_id (x : BitVec 64) : Fl4Spec.ucast 64 x = x := by simp [Fl4Spec.ucast]

theorem minUs_eq (hT : TimeAgree ar) : Fl4Spec.MIN_BUDGET_US = (20#u64 : U64).bv := by
  unfold Fl4Spec.MIN_BUDGET_US; rw [hT.wcetUs]; rfl

theorem isSc_absCap (c : capability.Cap) :
    Fl4Spec.isSchedContextCap (absCap c) = (match c with | .SchedContext .. => true | _ => false) := by
  cases c <;> rfl

/-- FL4's `refill_absolute_max` of a valid SC size is the spec's `max_num_refills`. -/
theorem refill_absolute_max_eq (sb : U64) (h7 : Fl4Spec.minSchedContextBits ≤ sb.val) (h64 : sb.val < 64) :
    sporadic.refill_absolute_max sb ⦃ m => m.val = Fl4Spec.maxNumRefills sb.val ⦄ := by
  unfold sporadic.refill_absolute_max
  have hge : ¬ (sb ≥ 64#u64) := by intro h; have : (64#u64 : U64).val ≤ sb.val := h; simp at this; omega
  simp only [hge, ↓reduceIte, lift, bind_ok]
  have h7' : 7 ≤ sb.val := h7
  have hsb : (sb &&& 63#u64).val = sb.val := by
    rw [UScalar.val_and, show (63#u64 : U64).val = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      Nat.mod_eq_of_lt (by omega)]
  step as ⟨bytes, hbytes⟩
  have hb : bytes.val = 2 ^ sb.val := by
    rw [hbytes, hsb, Nat.shiftLeft_eq, one_mul, Nat.mod_eq_of_lt]
    have : 2 ^ sb.val < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) h64
    simpa [U64.size_def, U64.numBits] using this
  have h96 : (layout.sc.REFILLS).val = 96 := by unfold layout.sc.REFILLS; rfl
  have h16 : (layout.sc.REFILL_SIZE).val = 16 := by unfold layout.sc.REFILL_SIZE; rfl
  have hle : 128 ≤ 2 ^ sb.val := by
    calc 128 = 2 ^ 7 := by norm_num
      _ ≤ 2 ^ sb.val := Nat.pow_le_pow_right (by norm_num) h7'
  have hnlt : ¬ bytes < layout.sc.REFILLS := by
    intro h; have : bytes.val < (layout.sc.REFILLS).val := h; omega
  simp only [hnlt, ↓reduceIte]
  step as ⟨d, hd⟩
  step as ⟨q, hq⟩
  rw [hq, hd, hb, h96, h16]
  unfold Fl4Spec.maxNumRefills Fl4Spec.sizeofSchedContextT Fl4Spec.wordSize Fl4Spec.refillSizeBytes
  rfl


/-- **`decode_sched_control` refines `decode_sched_control_invocation_flags`**:
FL4's errors are the spec's, and on success the spec's invocation is the one
`configure_flags` gets (`Q`), with the decoder's facts. -/
theorem decode_sched_control_refines (hT : TimeAgree ar) (th : TypedHeap) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (lbl : U64) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .schedControlConfigureFlags ↔
      lbl = fl4_abi.label.SchedControlConfigureFlags)
    (cpu length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List Fl4Spec.Cap) (hex : ExtraRel th (L.mem s) x0 excaps)
    (hsb : x0 ≠ 0#u64 → ∀ p sb, capAt (L.mem s) x0 = ok (.SchedContext p sb) → sb.val < 64)
    (Q : Fl4Spec.SchedControlInvocation → core.result.Result Unit error.Exc × S × A → Prop)
    (hQ : ∀ (p sb bu pu er bd fl budget period : U64), x0 ≠ 0#u64 → capAt (L.mem s) x0 = ok (.SchedContext p sb) →
      args[0]? = some bu → args[1]? = some pu → args[2]? = some er → args[3]? = some bd → args[4]? = some fl →
      budget.bv = Fl4Spec.usToTicks bu.bv → period.bv = Fl4Spec.usToTicks pu.bv →
      Fl4Spec.MIN_BUDGET ≤ budget.bv → budget.val ≤ period.val → er.val + 2 ≤ Fl4Spec.maxNumRefills sb.val →
      (do
        let s1 ← sched.set_thread_state st s ct sched.TS_RESTART
        let (s2, a1) ← schedcontext.configure_flags st ar s1 a p cpu budget period
          (core.num.U64.wrapping_add er sporadic.MIN_REFILLS) bd fl
        ok (core.result.Result.Ok (), s2, a1)) ⦃ res =>
        Q (.invokeSchedControlConfigureFlags p.bv (Fl4Spec.usToTicks bu.bv) (Fl4Spec.usToTicks pu.bv)
          (er.val + 2) bd.bv fl.bv) res ⦄) :
    schedcontext.decode_sched_control st ar s a lbl cpu length buf extra ⦃ res =>
      CPost σ (Fl4Spec.decodeSchedControlInvocationFlags (Z := Unit) slbl (args.map UScalar.bv) excaps)
        s a Q res ⦄ := by
  unfold schedcontext.decode_sched_control Fl4Spec.decodeSchedControlInvocationFlags
  by_cases hl : lbl = fl4_abi.label.SchedControlConfigureFlags
  swap
  · have : (lbl != fl4_abi.label.SchedControlConfigureFlags) = true := by simpa using hl
    simp only [this, ↓reduceIte, error.illegal, bind_ok]
    apply CPost.err (e := .Sys .IllegalOperation) (e' := .illegalOperation) _ (Or.inl trivial)
    have : ¬ Fl4Spec.genInvocationType slbl = .schedControlConfigureFlags := fun h => hl (hlbl.1 h)
    simp only [Fl4Spec.NonDetE.unlessE, this, ↓reduceIte, Fl4Spec.NonDetE.throwError, ndE_throw_bind]; rfl
  have hne : (lbl != fl4_abi.label.SchedControlConfigureFlags) = false := by simpa using hl
  have hsl' : Fl4Spec.genInvocationType slbl = .schedControlConfigureFlags := hlbl.2 hl
  simp only [hne, Bool.false_eq_true, ↓reduceIte, Fl4Spec.NonDetE.unlessE, hsl', ndE_pure_bind, hct, bind_ok]
  unfold schedcontext.extra_cap
  have h03 : ¬ (0#usize ≥ 3#usize) := by decide
  simp only [h03, ↓reduceIte, hx0, bind_ok, obj.Slot.is_null]
  rcases hex with ⟨rfl, rfl⟩ | ⟨hx0n, -, c0, a0, rest0, hc0, hca0, hcv0, rfl⟩
  · simp only [decide_true, ↓reduceIte, bind_ok, error.truncated]
    apply CPost.err (e := .Sys .TruncatedMessage) (e' := .truncatedMessage) _ (Or.inl trivial)
    simp only [List.length_nil, Fl4Spec.NonDetE.whenE, ↓reduceIte, Fl4Spec.NonDetE.throwError, ndE_throw_bind]
    rfl
  simp only [hx0n, decide_false, Bool.false_eq_true, ↓reduceIte, slot_cap_eq, hc0, bind_ok, List.length_cons,
    Fl4Spec.NonDetE.whenE, Nat.add_one_ne_zero, ndE_pure_bind]
  by_cases h5 : length < 5#u64
  · simp only [h5, ↓reduceIte, error.truncated, bind_ok]
    apply CPost.err (e := .Sys .TruncatedMessage) (e' := .truncatedMessage) _ (Or.inl trivial)
    have : (args.map UScalar.bv).length < Fl4Spec.timeArgLen * 2 + 3 := by
      simp only [List.length_map, Fl4Spec.timeArgLen]; scalar_tac
    simp only [this, ↓reduceIte, Fl4Spec.NonDetE.throwError, ndE_throw_bind]; rfl
  have h5' : ¬ (args.map UScalar.bv).length < Fl4Spec.timeArgLen * 2 + 3 := by
    simp only [List.length_map, Fl4Spec.timeArgLen]; scalar_tac
  simp only [h5, ↓reduceIte, h5', ndE_pure_bind]
  obtain ⟨bu, pu, er, bd, fl, rest, rfl⟩ : ∃ bu pu er bd fl rest, args = bu :: pu :: er :: bd :: fl :: rest := by
    match args with
    | bu :: pu :: er :: bd :: fl :: rest => exact ⟨bu, pu, er, bd, fl, rest, rfl⟩
    | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] => exfalso; simp at hlen; scalar_tac
  have h20 : sporadic.min_budget_us = ok 20#u64 := by unfold sporadic.min_budget_us; rfl
  refine WP.spec_bind (hT.maxPeriod a) ?_
  intro mx hmx
  simp only [h20, bind_ok, hargs 0#u64 bu (by simp), hargs 1#u64 pu (by simp), hargs 2#u64 er (by simp),
    hargs 3#u64 bd (by simp), hargs 4#u64 fl (by simp)]
  simp only [List.map_cons, Fl4Spec.NonDetE.returnOk, ndE_pure_bind, Fl4Spec.parseTimeArgA, Fl4Spec.timeArgLen,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Fl4Spec.the, ucast_id, List.head?_cons]
  rcases hca0 with ⟨hwf, rfl⟩
  have hmin : Fl4Spec.MIN_BUDGET_US = (20#u64 : U64).bv := minUs_eq hT
  -- the budget and period against the maximum
  by_cases g1 : bu > mx
  · have g1' : bu.bv > Fl4Spec.MAX_PERIOD_US := by rw [← hmx]; exact (gt_bv _ _).1 g1
    simp only [g1, ↓reduceIte, error.range, bind_ok]
    refine CPost.err (e' := .rangeError Fl4Spec.MIN_BUDGET_US Fl4Spec.MAX_PERIOD_US) ?_ (Or.inl ⟨hmin, hmx.symm⟩)
    simp only [g1', ↓reduceIte, Fl4Spec.NonDetE.throwError, ndE_throw_bind]; rfl
  have g1' : ¬ bu.bv > Fl4Spec.MAX_PERIOD_US := by rw [← hmx]; exact fun h => g1 ((gt_bv _ _).2 h)
  have hbu : bu.bv ≤ Fl4Spec.MAX_PERIOD_US := BitVec.not_lt.1 g1'
  simp only [g1, g1', ↓reduceIte, ndE_pure_bind]
  refine WP.spec_bind (hT.usToTicks a bu hbu) ?_
  intro budget hbud
  by_cases g2 : pu > mx
  · have g2' : pu.bv > Fl4Spec.MAX_PERIOD_US := by rw [← hmx]; exact (gt_bv _ _).1 g2
    simp only [g2, ↓reduceIte, error.range, bind_ok]
    refine CPost.err (e' := .rangeError Fl4Spec.MIN_BUDGET_US Fl4Spec.MAX_PERIOD_US) ?_ (Or.inl ⟨hmin, hmx.symm⟩)
    simp only [g2', ↓reduceIte, Fl4Spec.NonDetE.throwError, ndE_throw_bind]; rfl
  have g2' : ¬ pu.bv > Fl4Spec.MAX_PERIOD_US := by rw [← hmx]; exact fun h => g2 ((gt_bv _ _).2 h)
  have hpu : pu.bv ≤ Fl4Spec.MAX_PERIOD_US := BitVec.not_lt.1 g2'
  simp only [g2, g2', ↓reduceIte, ndE_pure_bind]
  refine WP.spec_bind (hT.usToTicks a pu hpu) ?_
  intro period hper
  refine WP.spec_bind (hT.mb a) ?_
  intro mb hmb
  -- the minimum, in ticks and in µs
  have hmb' : mb.bv = Fl4Spec.usToTicks Fl4Spec.MIN_BUDGET_US := hmb.trans hT.minBudget_eq
  have c3 : budget < mb ↔ bu.bv < Fl4Spec.MIN_BUDGET_US := by
    rw [lt_bv, hbud, hmb']; exact hT.usToTicks_lt hbu TimeAgree.minUs_le
  have c4 : period < mb ↔ pu.bv < Fl4Spec.MIN_BUDGET_US := by
    rw [lt_bv, hper, hmb']; exact hT.usToTicks_lt hpu TimeAgree.minUs_le
  have c5 : budget > period ↔ pu.bv < bu.bv := by
    rw [gt_bv, hbud, hper]; exact hT.usToTicks_lt hpu hbu
  by_cases g3 : budget < mb
  · simp only [g3, ↓reduceIte, error.range, bind_ok]
    refine CPost.err (e' := .rangeError Fl4Spec.MIN_BUDGET_US Fl4Spec.MAX_PERIOD_US) ?_ (Or.inl ⟨hmin, hmx.symm⟩)
    simp only [c3.1 g3, ↓reduceIte, Fl4Spec.NonDetE.throwError, ndE_throw_bind]; rfl
  simp only [g3, (not_congr c3).1 g3, ↓reduceIte, ndE_pure_bind]
  by_cases g4 : period < mb
  · simp only [g4, ↓reduceIte, error.range, bind_ok]
    refine CPost.err (e' := .rangeError Fl4Spec.MIN_BUDGET_US Fl4Spec.MAX_PERIOD_US) ?_ (Or.inl ⟨hmin, hmx.symm⟩)
    simp only [c4.1 g4, ↓reduceIte, Fl4Spec.NonDetE.throwError, ndE_throw_bind]; rfl
  simp only [g4, (not_congr c4).1 g4, ↓reduceIte, ndE_pure_bind]
  by_cases g5 : budget > period
  · simp only [g5, ↓reduceIte, error.range, bind_ok]
    refine CPost.err (e' := .rangeError Fl4Spec.MIN_BUDGET_US pu.bv) ?_ (Or.inl ⟨hmin, rfl⟩)
    simp only [c5.1 g5, ↓reduceIte, Fl4Spec.NonDetE.throwError, ndE_throw_bind]; rfl
  simp only [g5, (not_congr c5).1 g5, ↓reduceIte, ndE_pure_bind]
  have hmbB : Fl4Spec.MIN_BUDGET ≤ budget.bv := by
    rw [← hmb]; exact BitVec.not_lt.1 (fun h => g3 ((lt_bv _ _).2 h))
  have hbp : budget.val ≤ period.val := by
    have := (not_congr (gt_bv budget period)).1 g5
    rw [BitVec.not_lt, BitVec.le_def, UScalar.bv_toNat, UScalar.bv_toNat] at this; exact this
  -- the cap
  cases c0
  case SchedContext p sb =>
    dsimp only
    have h7 : 7 ≤ sb.val := hwf
    have h64 := hsb hx0n p sb hc0
    refine WP.spec_bind (refill_absolute_max_eq sb hwf h64) ?_
    intro mr hmr
    simp only [lift, bind_ok]
    have hN2 : 2 ≤ Fl4Spec.maxNumRefills sb.val := by
      unfold Fl4Spec.maxNumRefills Fl4Spec.sizeofSchedContextT Fl4Spec.wordSize Fl4Spec.refillSizeBytes
      have : 128 ≤ 2 ^ sb.val := by
        calc 128 = 2 ^ 7 := by norm_num
          _ ≤ 2 ^ sb.val := Nat.pow_le_pow_right (by norm_num) h7
      omega
    have hm2 : (sporadic.MIN_REFILLS).val = 2 := by unfold sporadic.MIN_REFILLS; rfl
    have hsz : UScalar.size .U64 = 2 ^ 64 := by simp [UScalar.size_def, UScalarTy.numBits]
    have hNb : Fl4Spec.maxNumRefills sb.val < 2 ^ 64 := by rw [← hmr]; exact mr.hBounds
    have hi : (core.num.U64.wrapping_sub mr sporadic.MIN_REFILLS).val = Fl4Spec.maxNumRefills sb.val - 2 := by
      rw [core.num.U64.wrapping_sub_val_eq, hm2, hmr, hsz]
      rw [show Fl4Spec.maxNumRefills sb.val + (2 ^ 64 - 2) = (Fl4Spec.maxNumRefills sb.val - 2) + 2 ^ 64 by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    have hA : (Fl4Spec.NonDetE.assertE (Fl4Spec.MIN_REFILLS ≤ Fl4Spec.maxNumRefills sb.val) :
        Fl4Spec.SEMonad Unit Unit).run σ = ({(.ok (), σ)}, False) := by
      apply run_liftE'
      show (({x | Fl4Spec.MIN_REFILLS ≤ Fl4Spec.maxNumRefills sb.val ∧ x = ((), σ)},
        ¬ Fl4Spec.MIN_REFILLS ≤ Fl4Spec.maxNumRefills sb.val) : Set (Unit × Fl4Spec.State Unit) × Prop) =
        ({((), σ)}, False)
      have : Fl4Spec.MIN_REFILLS ≤ Fl4Spec.maxNumRefills sb.val := hN2
      simp [this]
    have hcap : Fl4Spec.maxRefillsCap (absCap (.SchedContext p sb)) = Fl4Spec.maxNumRefills sb.val := by
      show Fl4Spec.maxNumRefills (Fl4Spec.minSchedContextBits + (sb.val - Fl4Spec.minSchedContextBits)) = _
      rw [Nat.add_sub_cancel' hwf]
    simp only [isSc_absCap, not_true_eq_false, ↓reduceIte, ndE_pure_bind, hcap]
    by_cases g6 : er > core.num.U64.wrapping_sub mr sporadic.MIN_REFILLS
    · have g6' : Fl4Spec.unat er.bv > Fl4Spec.maxNumRefills sb.val - Fl4Spec.MIN_REFILLS := by
        have : (core.num.U64.wrapping_sub mr sporadic.MIN_REFILLS).val < er.val := g6
        simp only [Fl4Spec.unat, UScalar.bv_toNat, Fl4Spec.MIN_REFILLS]; omega
      simp only [g6, ↓reduceIte, error.range, bind_ok]
      refine CPost.err (e' := .rangeError 0 (BitVec.ofNat 64 (Fl4Spec.maxNumRefills sb.val - Fl4Spec.MIN_REFILLS)))
        ?_ (Or.inl ⟨rfl, ?_⟩)
      · rw [dec_run_bind hA]
        simp only [g6', ↓reduceIte, Fl4Spec.NonDetE.throwError, ndE_throw_bind]; rfl
      · apply BitVec.eq_of_toNat_eq
        rw [UScalar.bv_toNat, hi, BitVec.toNat_ofNat, Fl4Spec.MIN_REFILLS, Nat.mod_eq_of_lt]
        omega
    · have g6' : ¬ Fl4Spec.unat er.bv > Fl4Spec.maxNumRefills sb.val - Fl4Spec.MIN_REFILLS := by
        have : ¬ (core.num.U64.wrapping_sub mr sporadic.MIN_REFILLS).val < er.val := g6
        simp only [Fl4Spec.unat, UScalar.bv_toNat, Fl4Spec.MIN_REFILLS]; omega
      have hle : er.val + 2 ≤ Fl4Spec.maxNumRefills sb.val := by
        have : ¬ (core.num.U64.wrapping_sub mr sporadic.MIN_REFILLS).val < er.val := g6
        omega
      simp only [g6, ↓reduceIte]
      refine WP.spec_mono (hQ p sb bu pu er bd fl budget period hx0n hc0 rfl rfl rfl rfl rfl hbud hper hmbB hbp hle) ?_
      intro res h
      refine Or.inr ⟨_, ?_, h⟩
      rw [dec_run_bind hA]
      have g6'' : ¬ er.val > Fl4Spec.maxNumRefills sb.val - 2 := by omega
      simp only [g6'', g6', ↓reduceIte, ndE_pure_bind, Fl4Spec.unat, UScalar.bv_toNat, Fl4Spec.MIN_REFILLS]
      rfl
  all_goals
    simp only [error.invalid_cap, bind_ok]
    refine CPost.err (e' := .invalidCapability 1) ?_ (Or.inr ⟨1#u64, rfl, rfl⟩)
    simp only [isSc_absCap, Bool.false_eq_true, not_false_eq_true, ↓reduceIte, Fl4Spec.NonDetE.throwError,
      ndE_throw_bind]
    rfl

end

end

end Fl4Proofs.P3.Sched
