/-
P3 (DESIGN.md §9), scheduling contexts: **`refill_update` refines l4v
`refill_update`** (`refill_update_refines`), the reconfiguration of an
SC's ring (SchedControl `Configure` on an active SC whose thread is
runnable). It changes `REFILL_MAX`, which the relation now allows: an SC's
footprint is its object (`ScObj`, `2 ^ n` bytes), not its current ring.

`rUpdL` is the new ring as a list: the old head (moved to the current time
if it is ready), cut to the new budget, then either an empty tail
(round-robin) or the unused budget one period later.

Hypotheses: the new ring size is at least `MIN_REFILLS` and fits in the
object (l4v `decode_sched_control_invocation` checks both).
-/
import Fl4Proofs.P3.ScEntry
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

/-- The head refill after `refill_update`'s move to the current time. -/
def rUpdHd (h : sporadic.Refill) (now : U64) : sporadic.Refill :=
  if h.time ≤ now then ⟨now, h.amount⟩ else h

/-- `refill_update` on the list. -/
def rUpdL (h : sporadic.Refill) (now p b : U64) : List sporadic.Refill :=
  let h' := rUpdHd h now
  if b ≤ h'.amount then
    (if p = 0#u64 then [⟨h'.time, b⟩, ⟨h'.time, 0#u64⟩] else [⟨h'.time, b⟩])
  else [h', ⟨core.num.U64.wrapping_add h'.time p, core.num.U64.wrapping_sub b h'.amount⟩]

section Spec
open Fl4Spec

/-- The head refill after `refill_update`'s move to the current time (spec). -/
def rUpdSHd (H : Refill) (now : Ticks) : Refill := if refillReady now H = true then { H with rTime := now } else H

theorem rUpdSHd_amount (H : Refill) (now : Ticks) : (rUpdSHd H now).rAmount = H.rAmount := by
  unfold rUpdSHd; split <;> rfl

/-- The ring after `refill_update`, from the (moved) head. -/
def rUpdL' (H : Refill) (np nb : Ticks) : List Refill :=
  if nb ≤ H.rAmount then
    (if np = 0 then [{ H with rAmount := nb }, { rTime := H.rTime, rAmount := 0 }] else [{ H with rAmount := nb }])
  else [H, { rTime := H.rTime + np, rAmount := nb - H.rAmount }]

/-- `refill_update` on the spec's list. -/
def rUpdS (H : Refill) (now np nb : Ticks) : List Refill := rUpdL' (rUpdSHd H now) np nb

/-- The SC with a new ring and configuration. -/
def rUpdY (x : SchedContext) (l : List Refill) (np nb : Ticks) (nm : Nat) : SchedContext :=
  { x with scRefills := l, scRefillMax := nm, scPeriod := np, scBudget := nb }

/-- The SC after `refill_update`. -/
def rUpdX (x : SchedContext) (now np nb : Ticks) (nm : Nat) : SchedContext :=
  rUpdY x (rUpdS (refillHd x) now np nb) np nb nm

theorem refillUpdate_eq {σ : State Unit} {p : ObjRef} {x : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext x n)) (np nb : Ticks) (nm : Nat) :
    refillUpdate (Z := Unit) p np nb nm σ = ({((), updSc σ p (rUpdX x σ.curTime np nb nm) n)}, False) := by
  have k : ∀ (z : SchedContext) (σ' : State Unit), (updSc σ' p z n).kheap p = some (.schedContext z n) :=
    fun z σ' => by simp [updK]
  have hne : ∀ y : SchedContext, ∀ r : Refill, y.scRefills = [r] → y.scRefills ≠ [] := fun y r h => by simp [h]
  -- the rest, once the head is known
  have tail : ∀ (H : Refill) (σ1 : State Unit) (y : SchedContext),
      σ1.kheap p = some (.schedContext y n) → y.scRefills = [H] → y.scPeriod = np →
      σ1 = updSc σ p (rUpdY x [H] np nb nm) n →
      (do
        let head ← getRefillHead (Z := Unit) p
        if nb ≤ head.rAmount
        then do
          updateRefillHd p fun refill => { refill with rAmount := nb }
          maybeAddEmptyTail p
        else do
          let unused ← pure (nb - head.rAmount)
          let new ← pure { rTime := head.rTime + np, rAmount := unused : Refill }
          refillAddTail p new) σ1 = ({((), updSc σ p (rUpdY x (rUpdL' H np nb) np nb nm) n)}, False) := by
    intro H σ1 y hy hyr hyp e1
    subst e1
    have ey : y = rUpdY x [H] np nb nm := by
      simp only [updK_kheap, Function.update_self, Option.some.injEq, KernelObject.schedContext.injEq] at hy
      exact hy.1.symm
    subst ey
    have hd : refillHd (rUpdY x [H] np nb nm) = H := rfl
    rw [nd_bind_one (getRefillHead_eq hy (hne _ H hyr)), hd]
    unfold rUpdL'
    by_cases hb : nb ≤ H.rAmount
    · rw [if_pos hb, if_pos hb, nd_bind_one (updateRefillHd_eq hy _)]
      unfold maybeAddEmptyTail
      rw [nd_bind_one (isRoundRobin_eq (k _ _))]
      unfold Fl4Spec.NonDet.when
      by_cases hp : np = 0
      · rw [if_pos hp]
        split
        · rw [nd_bind_one (getRefillHead_eq (k _ _) (by simp [rUpdY])), nd_pure_bind',
            refillAddTail_eq (k _ _), updSc_updSc, updSc_updSc]
          rfl
        · rename_i hp0; exact absurd (decide_eq_true hp) hp0
      · rw [if_neg hp]
        split
        · rename_i hp0; exact absurd (of_decide_eq_true hp0) hp
        · rw [updSc_updSc]; rfl
    · rw [if_neg hb, if_neg hb, nd_pure_bind', nd_pure_bind', refillAddTail_eq hy, updSc_updSc]
      rfl
  unfold refillUpdate
  rw [nd_bind_one (updateSchedContext_eq hk _), nd_bind_one (updateSchedContext_eq (k _ _) _),
    nd_bind_one (updateSchedContext_eq (k _ _) _), nd_bind_one (updateSchedContext_eq (k _ _) _)]
  simp only [updSc_updSc]
  rw [nd_bind_one (getScRefillReady_eq (k _ _) (hne _ (refillHd x) rfl))]
  unfold rUpdX rUpdS rUpdSHd Fl4Spec.NonDet.when
  split
  · rename_i h0
    have hr : refillReady σ.curTime (refillHd x) = true := h0
    rw [if_pos hr, nd_bind_assoc', nd_gets_bind, nd_bind_one (updateRefillHd_eq (k _ _) _), updSc_updSc]
    exact tail _ _ _ (k _ _) rfl rfl rfl
  · rename_i h0
    have hr : ¬ refillReady σ.curTime (refillHd x) = true := h0
    rw [if_neg hr, nd_bind_one (show Fl4Spec.NonDet.pure (σ := State Unit) () _ = _ from rfl)]
    exact tail _ _ _ (k _ _) rfl rfl rfl

end Spec

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

theorem wIn_trans {s₁ s₂ s₃ : S} {A : U64 → Prop} (h₁ : WritesIn st s₁ s₂ A) (h₂ : WritesIn st s₂ s₃ A) :
    WritesIn st s₁ s₃ A := (WritesIn.trans h₁ h₂).mono fun _ hb => by rcases hb with hb | hb <;> exact hb

/-- **FL4's `refill_update`**: writes inside the object, keeps the header
words other than the period, the ring size and the ring indices, and leaves
the ring `rUpdL`. -/
theorem refill_update_fl4 {s : S} {sc : U64} {n : Nat} (hW : RefillsWF st s sc n) (p b m : U64)
    (hm2 : 2 ≤ m.val) (hmx : m.val ≤ absMax n)
    (hct : Aligned (L.nodeA s layout.node.CUR_TIME) ∧ ¬ ScObj sc n (L.nodeA s layout.node.CUR_TIME)) :
    sporadic.refill_update st s sc p b m ⦃ s' => WritesIn st s s' (ScObj sc n) ∧ RefillsWF st s' sc n ∧
      L.rperiod s' sc = p ∧ L.rmax s' sc = m ∧
      L.refills s' sc = rUpdL (L.refill s sc (L.rhead s sc)) (L.curTime s) p b ∧
      ∀ K : U64, K.val < 96 → K.val % 8 = 0 → K.val ≠ 0 → K.val ≠ 72 → K.val ≠ 80 → K.val ≠ 88 →
        L.mem s' (scW sc K) = L.mem s (scW sc K) ⦄ := by
  have hP := hW.placed
  obtain ⟨h8, hb, hfit⟩ := hP.bounds hm2 hmx
  obtain ⟨-, hpA, hmA, hhA, htA, -⟩ := hW.inside
  have hi0 : sc.val + 96 + 16 * (0#u64).val + 16 ≤ 2 ^ 64 := by simp; omega
  -- the words `refill_update` writes
  let RW : U64 → Prop := fun a => ScObj sc n a ∧ ¬ ∃ K : U64, K.val < 96 ∧ K.val % 8 = 0 ∧ K.val ≠ 0 ∧
    K.val ≠ 72 ∧ K.val ≠ 80 ∧ K.val ≠ 88 ∧ a = scW sc K
  have hRW : ∀ a : U64, sc.val ≤ a.val → a.val < sc.val + 96 + 16 * m.val →
      (a.val = sc.val ∨ a.val = sc.val + 72 ∨ a.val = sc.val + 80 ∨ a.val = sc.val + 88 ∨ sc.val + 96 ≤ a.val) →
      RW a := by
    intro a h1 h2 h3
    refine ⟨⟨h1, by omega⟩, ?_⟩
    rintro ⟨K, hK, -, h0, h72, h80, h88, rfl⟩
    rw [scW_val (by omega)] at h3; omega
  have wH : ∀ {s0 : S} {a v : U64}, (a = periodA sc ∨ a = maxA sc ∨ a = headA sc ∨ a = tailA sc) →
      WritesIn st s0 (L.wr s0 a v) RW := by
    intro s0 a v ha
    have hv : a.val = sc.val ∨ a.val = sc.val + 72 ∨ a.val = sc.val + 80 ∨ a.val = sc.val + 88 := by
      rcases ha with rfl | rfl | rfl | rfl <;> omega
    have hal : Aligned a := by unfold Aligned; rcases hv with h | h | h | h <;> rw [h] <;> omega
    refine (writesIn_wr hal).mono fun b' hb' => ?_
    subst hb'; exact hRW _ (by omega) (by omega) (by omega)
  -- the ring of size `m` from `s0`: slots below `m`
  have wR : ∀ {s0 s1 : S} {k : Nat}, L.rmax s0 sc = m → RingAt st s0 s1 sc k → WritesIn st s0 s1 RW := by
    intro s0 s1 k hm h
    refine h.w.mono fun b' hb' => ?_
    rcases hb' with rfl | rfl | ⟨h1, h2⟩
    · exact hRW _ (by omega) (by omega) (by omega)
    · exact hRW _ (by omega) (by omega) (by omega)
    · rw [hm] at h2; exact hRW _ (by omega) h2 (by omega)
  have hfin : ∀ {s' : S}, WritesIn st s s' RW → WritesIn st s s' (ScObj sc n) ∧
      ∀ K : U64, K.val < 96 → K.val % 8 = 0 → K.val ≠ 0 → K.val ≠ 72 → K.val ≠ 80 → K.val ≠ 88 →
        L.mem s' (scW sc K) = L.mem s (scW sc K) := by
    intro s' hw
    refine ⟨hw.mono fun _ h => h.1, fun K h1 h2 h3 h4 h5 h6 => hw.mem_eq ?_ fun h => h.2 ⟨K, h1, h2, h3, h4, h5, h6, rfl⟩⟩
    unfold Aligned; rw [scW_val (by omega)]; omega
  have hctRW : ¬ RW (L.nodeA s layout.node.CUR_TIME) := fun h => hct.2 h.1
  unfold sporadic.refill_update
  step with sporadic.head.spec as ⟨h, h_post⟩
  step with sporadic.put.spec as ⟨s1, s1_post⟩
  step with obj.Sc.set_refill_head.spec as ⟨s2, s2_post⟩
  step with obj.Sc.set_refill_tail.spec as ⟨s3, s3_post⟩
  step with obj.Sc.set_refill_max.spec as ⟨s4, s4_post⟩
  step with obj.Sc.set_period.spec as ⟨s5, s5_post⟩
  have hW4 : RefillsWF st s4 sc n := by subst s4_post s3_post s2_post; exact RefillsWF.reset hP (by simpa using hm2) hmx
  have hW5 : RefillsWF st s5 sc n := by subst s5_post; exact hW4.wr_period
  have hh5 : L.rhead s5 sc = 0#u64 := by
    subst s5_post s4_post s3_post s2_post
    rw [rhead_wr_period h8, rhead_wr_max h8, rhead_wr_tail h8, rhead_wr_head h8]
  have hm5 : L.rmax s5 sc = m := by
    subst s5_post s4_post; rw [rmax_wr_period h8, rmax_wr_max h8]
  have hp5 : L.rperiod s5 sc = p := by subst s5_post; rw [rperiod_wr_period h8]
  have hs5 : L.size s5 sc = 1 := by
    subst s5_post s4_post s3_post s2_post
    simp only [LawfulStore.size, rhead_wr_period h8, rhead_wr_max h8, rhead_wr_tail h8, rhead_wr_head h8,
      rtail_wr_period h8, rtail_wr_max h8, rtail_wr_tail h8]; simp [ringN]
  have hr5 : L.refill s5 sc 0#u64 = h := by
    subst s5_post s4_post s3_post s2_post s1_post
    rw [refill_wr_hdr' h8 hi0 (Or.inl rfl), refill_wr_hdr' h8 hi0 (Or.inr (Or.inl rfl)),
      refill_wr_hdr' h8 hi0 (Or.inr (Or.inr (Or.inr rfl))), refill_wr_hdr' h8 hi0 (Or.inr (Or.inr (Or.inl rfl))),
      refill_putS_same h8]
  have hw5 : WritesIn st s s5 RW := by
    have w1 : WritesIn st s s1 RW := by
      obtain ⟨-, -, -, -, -, hin⟩ := hW.inside
      have h0 : (0#u64).val < (L.rmax s sc).val := by have := hW.min_le; simp at this ⊢; omega
      obtain ⟨e1, e2, -⟩ := hin _ h0
      have a1 : Aligned (rtA sc 0#u64) := by unfold Aligned; rw [e1]; omega
      have a2 : Aligned (raA sc 0#u64) := by unfold Aligned; rw [e2]; omega
      rw [s1_post]
      refine ((writesIn_wr (st := st) (s := s) (v := h.time) a1).trans
        (writesIn_wr (st := st) (s := L.wr s (rtA sc 0#u64) h.time) (v := h.amount) a2)).mono fun b' hb' => ?_
      rcases hb' with rfl | rfl
      · exact hRW _ (by rw [e1]; omega) (by rw [e1]; simp; omega) (by rw [e1]; omega)
      · exact hRW _ (by rw [e2]; omega) (by rw [e2]; simp; omega) (by rw [e2]; omega)
    have w2 : WritesIn st s1 s2 RW := by rw [s2_post]; exact wH (Or.inr (Or.inr (Or.inl rfl)))
    have w3 : WritesIn st s2 s3 RW := by rw [s3_post]; exact wH (Or.inr (Or.inr (Or.inr rfl)))
    have w4 : WritesIn st s3 s4 RW := by rw [s4_post]; exact wH (Or.inr (Or.inl rfl))
    have w5 : WritesIn st s4 s5 RW := by rw [s5_post]; exact wH (Or.inl rfl)
    exact wIn_trans (wIn_trans (wIn_trans (wIn_trans w1 w2) w3) w4) w5
  have hct5 : L.curTime s5 = L.curTime s := by
    simp only [LawfulStore.curTime]
    rw [show L.nodeA s5 layout.node.CUR_TIME = L.nodeA s layout.node.CUR_TIME by
      simp only [LawfulStore.nodeA, LawfulStore.nodeAt, hw5.1, hw5.2.1]]
    exact hw5.mem_eq hct.1 hctRW
  have hrs5 : L.refills s5 sc = [h] := by
    unfold LawfulStore.refills; rw [hs5]
    simp only [List.range_one, List.map_cons, List.map_nil, List.cons.injEq, and_true]
    rw [LawfulStore.rf, hW5.ix_zero, hh5, hr5]
  step with sporadic.ready.spec as ⟨rb, rb_post⟩
  rw [hh5, hr5, hct5] at rb_post
  have h0 : (0#u64).val < (L.rmax s5 sc).val := by rw [hm5]; simp; omega
  -- after the move to the current time
  have key : (if rb = true then do
        let now ← sporadic.cur_time st s5
        let r ← sporadic.head st s5 sc
        sporadic.set_head st s5 sc { r with time := now }
      else ok s5) ⦃ s6 => RingAt st s5 s6 sc n ∧ L.refills s6 sc = [rUpdHd h (L.curTime s)] ⦄ := by
    split
    · rename_i hrb
      step with sporadic.cur_time.spec as ⟨now, now_post⟩
      step with sporadic.head.spec as ⟨r, r_post⟩
      rw [hh5, hr5] at r_post
      refine WP.spec_mono (set_head_ring (RingAt.refl hW5) _) ?_
      rintro s6 ⟨h6, e6⟩
      refine ⟨h6, ?_⟩
      rw [e6, hrs5]
      have : h.time ≤ L.curTime s := by rw [rb_post] at hrb; simpa using hrb
      unfold rUpdHd; rw [if_pos this, now_post, hct5, r_post]; rfl
    · rename_i hrb
      rw [WP.spec_ok]
      refine ⟨RingAt.refl hW5, ?_⟩
      have : ¬ h.time ≤ L.curTime s := by rw [rb_post] at hrb; simpa using hrb
      rw [hrs5]; unfold rUpdHd; rw [if_neg this]
  refine WP.spec_bind key ?_
  rintro s6 ⟨h6, e6⟩
  have hW6 := h6.wf
  have hm6 : L.rmax s6 sc = m := h6.mx.trans hm5
  have alP : Aligned (scW sc 0#u64) := by unfold Aligned; rw [scW_val (by simp; omega)]; simp; omega
  have per : ∀ {s' : S}, RingAt st s5 s' sc n → L.rperiod s' sc = p := by
    intro s' h'
    have := h'.hdr (K := 0#u64) (by simp) (by simp) alP
    simp only [LawfulStore.rperiod, periodA_eq] at hp5 ⊢; rw [this]; exact hp5
  step with sporadic.head.spec as ⟨hd, hd_post⟩
  have ehd : hd = rUpdHd h (L.curTime s) := by
    rw [hd_post, head_eq' hW6, e6]; rfl
  split
  · rename_i hge
    refine WP.spec_bind (set_head_ring h6 _) ?_
    rintro s7 ⟨h7, e7⟩
    rw [e6] at e7
    simp only [List.tail_cons] at e7
    have hsz7 : L.size s7 sc = 1 := by rw [← refills_length, e7]; rfl
    unfold sporadic.maybe_add_empty_tail
    step with sporadic.is_round_robin.spec as ⟨rr, rr_post⟩
    rw [per h7] at rr_post
    split
    · rename_i hrr
      have hp0 : p = 0#u64 := by rw [rr_post] at hrr; simpa using hrr
      step with sporadic.head.spec as ⟨r, r_post⟩
      have er : r = ⟨hd.time, b⟩ := by rw [r_post, head_eq' h7.wf, e7]; rfl
      refine WP.spec_mono (add_tail_ring h7 (by rw [hsz7, h7.mx, hm5]; omega) _) ?_
      rintro s' ⟨h', e'⟩
      obtain ⟨hw, hK⟩ := hfin (wIn_trans hw5 (wR hm5 h'))
      refine ⟨hw, h'.wf, per h', h'.mx.trans hm5, ?_, hK⟩
      rw [e', e7, er, ← h_post]
      unfold rUpdL; rw [← ehd, if_pos hge, if_pos hp0]; rfl
    · rename_i hrr
      have hp0 : ¬ p = 0#u64 := by rw [rr_post] at hrr; simpa using hrr
      rw [WP.spec_ok]
      obtain ⟨hw, hK⟩ := hfin (wIn_trans hw5 (wR hm5 h7))
      refine ⟨hw, h7.wf, per h7, h7.mx.trans hm5, ?_, hK⟩
      rw [e7, ← h_post]
      unfold rUpdL; rw [← ehd, if_pos hge, if_neg hp0]
  · rename_i hlt
    simp only [lift, bind_ok]
    step as ⟨i1, i1_post⟩
    have hlt' : hd.amount.val < b.val := by simp only [ge_iff_le, UScalar.le_equiv, not_le] at hlt; exact hlt
    have ei1 : i1 = core.num.U64.wrapping_sub b hd.amount :=
      UScalar.eq_of_val_eq (by rw [wsub_val (by omega)]; omega)
    have hsz6 : L.size s6 sc = 1 := by rw [← refills_length, e6]; rfl
    refine WP.spec_mono (add_tail_ring h6 (by rw [hsz6, hm6]; omega) _) ?_
    rintro s' ⟨h', e'⟩
    obtain ⟨hw, hK⟩ := hfin (wIn_trans hw5 (wR hm5 h'))
    refine ⟨hw, h'.wf, per h', h'.mx.trans hm5, ?_, hK⟩
    rw [e', e6, ei1, ← h_post]
    unfold rUpdL; rw [← ehd, if_neg (fun h' => hlt h')]; rfl
theorem rUpdL_map (h : sporadic.Refill) (now p b : U64) :
    (rUpdL h now p b).map toRefill = rUpdS (toRefill h) now.bv p.bv b.bv := by
  have ready : Fl4Spec.refillReady now.bv (toRefill h) = decide (h.time ≤ now) := by
    show decide (h.time.bv + 0 ≤ now.bv) = _
    have e0 : h.time.bv + 0 = h.time.bv := by simp
    rw [e0]; exact decide_eq_decide.2 (u64_le_bv _ _).symm
  have hd : (rUpdSHd (toRefill h) now.bv) = toRefill (rUpdHd h now) := by
    unfold rUpdSHd rUpdHd; rw [ready]
    by_cases e : h.time ≤ now
    · simp only [e, decide_true, ↓reduceIte]; rfl
    · simp only [e, decide_false, Bool.false_eq_true, ↓reduceIte]
  unfold rUpdS rUpdL rUpdL'
  rw [hd]
  generalize rUpdHd h now = h'
  by_cases e1 : b ≤ h'.amount
  · have e1' : b.bv ≤ (toRefill h').rAmount := (u64_le_bv _ _).1 e1
    rw [if_pos e1, if_pos e1']
    by_cases e2 : p = 0#u64
    · have e2' : p.bv = 0 := by rw [e2]; rfl
      rw [if_pos e2, if_pos e2']; rfl
    · have e2' : ¬ p.bv = 0 := fun h => e2 (eq_of_bv (by rw [h]; rfl))
      rw [if_neg e2, if_neg e2']; rfl
  · have e1' : ¬ b.bv ≤ (toRefill h').rAmount := fun h => e1 ((u64_le_bv _ _).2 h)
    rw [if_neg e1, if_neg e1']
    simp [toRefill, core.num.U64.wrapping_add_bv_eq, core.num.U64.wrapping_sub_bv_eq]

/-- **`refill_update` refines `refill_update`.** -/
theorem refill_update_refines {N T C : Set U64} {c : U64} (s : S) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) {sc : U64} (hsc : sc ∈ C) {x : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap sc.bv = some (.schedContext x n)) (p b m : U64) (hm2 : 2 ≤ m.val) (hmx : m.val ≤ absMax n) :
    sporadic.refill_update st s sc p b m ⦃ s' => ∃ σ', Fl4Spec.refillUpdate (Z := Unit) sc.bv p.bv b.bv m.val σ =
      ({((), σ')}, False) ∧ SchedRel st N T C c s' σ' ∧ FootEq N T (L.mem s) (L.mem s') ∧ KView σ σ' ∧
      WritesIn st s s' (KFoot st T N C c s σ) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x', n', hk', hx⟩ := hs.scs sc hsc
  rw [hk] at hk'; cases hk'
  have hN := hc.node
  have hnA : L.nodeA s layout.node.CUR_TIME = L.nodeAt s c layout.node.CUR_TIME := by
    simp only [LawfulStore.nodeA, hc.cur]
  have h48 : layout.node.CUR_TIME.val = 48 := by simp [layout.node.CUR_TIME]
  have hct : Aligned (L.nodeA s layout.node.CUR_TIME) ∧ ¬ ScObj sc n (L.nodeA s layout.node.CUR_TIME) := by
    rw [hnA]
    refine ⟨nodeAt_aligned hN (by omega) (by omega), fun hin => ?_⟩
    have := (hS.scOut sc hsc x n hk _ hin).2.1
    rw [nodeAt_val hN (by omega)] at this; omega
  refine WP.spec_mono (refill_update_fl4 hx.wf p b m hm2 hmx hct) ?_
  rintro s' ⟨hw, hW', hp', hm', hr', hK⟩
  have hne := refills_ne' hx.wf
  have hhd : Fl4Spec.refillHd x = toRefill (L.refill s sc (L.rhead s sc)) := by
    rw [refillHd_map hx.refills hne, head_eq' hx.wf]
  have htm : σ.curTime = (L.curTime s).bv := by rw [hs.curTime, curTime_eq hc]
  have e := fun K : U64 => hK K
  have hx' : ScRel1 st s' sc (rUpdX x σ.curTime p.bv b.bv m.val) n :=
    ⟨hW', by rw [hp']; rfl, by rw [e 8#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]; exact hx.consumed,
      by rw [e 24#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]; exact hx.tcb,
      by rw [e 40#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]; exact hx.ntfn,
      by rw [e 48#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]; exact hx.badge,
      by rw [e 56#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]; exact hx.yieldFrom,
      by rw [e 64#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]; exact hx.sporadic,
      by rw [hm']; rfl, by
        show rUpdS (Fl4Spec.refillHd x) σ.curTime p.bv b.bv = _
        rw [hr', rUpdL_map, hhd, htm]⟩
  have h32 : L.mem s' (scW sc 32#u64) = L.mem s (scW sc 32#u64) :=
    e 32#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  refine ⟨updSc σ sc.bv (rUpdX x σ.curTime p.bv b.bv m.val) n, refillUpdate_eq hk _ _ _, ?_,
    scobj_footEq hS hsc hk hw, KView.of_sc hk,
    WritesIn.kfoot_of_scobj hsc hk hw (by rw [scReplyA_eq']; exact h32)⟩
  exact hS.sc_update hsc hk hw (e 16#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)) _ hx'

end

end

end Fl4Proofs.P3.Sched
