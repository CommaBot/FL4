/-
# The accepted ReplyRecv run's footprint X0 → X8 (FL4 #56, m68 (R-a'))

The general path's states `X1 … X8` along an accepted ReplyRecv run (m66's
`RRPre`) differ from the dispatch state `X0` only on

* `t`'s and `u`'s state words (`X1`, the unlink's `set_thread_state`, `X6`,
  `X8`), `u`'s fault word (`clear_fault`, `X5`);
* the reply link words of reply objects (`reply_remove`'s unlink branch: the
  reply's own `PREV` / `NEXT` and its neighbours' — replies by `ReplyInv0`
  `next` / `prev`, since the fast path checked the reply is no stack head)
  and the reply's `TCB` word (written 0);
* `u`'s SC ring and the core's `REPROGRAM` word (`refill_unblock_check`);
* the TCB registers (`handle_fault_reply`'s UnknownSyscall copy, `XferRegW`);
* the core's `SCHED_ACTION` word (`X7`).

`rr_remove_foot` is the unlink branch; `RRW` the union; `finKeep_rrw` turns a
footprint inside `RRW` into m63's `FinKeep` over `Ω` without the reply link
words (`RΩ`).
-/
import Fl4Proofs.P1.FastRREnt
import Fl4Proofs.P1.FastFinInv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {A : Type _} {st : machine.Store S} (ar : machine.Arch A) [L : LawfulStore st]

/-- The link words (`PREV`, `NEXT`) of the reply objects `Rp`. -/
def RpLW (Rp : Set U64) (b : U64) : Prop := ∃ r' ∈ Rp, b = rPrevA r' ∨ b = rNextA r'

/-- `Ω` without the reply link words. -/
def RΩ (Ω Rp : Set U64) : Set U64 := {b | b ∈ Ω ∧ ¬ RpLW Rp b}

/-- `schedule_tcb` of a thread that is not current is no write. -/
theorem schedule_tcb_ne {X : S} {x : obj.Tcb} (h : L.curW X ≠ x) : sched.schedule_tcb st X x = ok X := by
  unfold sched.schedule_tcb
  rw [eq_of_spec_fd (sched.cur_thread.spec (L := L) X)]; simp only [bind_ok]
  rw [eq_of_spec_fd (obj.Tcb.eq.spec _ _)]; simp only [bind_ok]
  have : decide (x = L.mem X (L.nodeAt X (L.cpu X) layout.node.CUR_THREAD)) = false := by
    simp only [decide_eq_false_iff_not]; intro e; exact h (by rw [e]; rfl)
  rw [this]; rfl

theorem writesIn_ite {s s1 : S} {c : Bool} {m : Result S} {F : U64 → Prop}
    (h : (if c = true then m else ok s) = ok s1) (hm : c = true → m = ok s1 → WritesIn st s s1 F) :
    WritesIn st s s1 F := by
  by_cases hc : c = true
  · rw [if_pos hc] at h; exact hm hc h
  · rw [if_neg hc] at h; rw [← ok_inj_ff h]; exact WritesIn.refl _ _

/-- **`reply_remove`'s unlink branch** (the fast path checked the reply is no
stack head): it writes only reply link words of replies, the reply's `TCB`
word (to 0) and `u`'s state; the Arch value is kept. -/
theorem rr_remove_foot {Rp : Set U64} {s s' : S} {a a' : A} {r u : U64}
    (hn : (∃ i, obj.Reply.next st r s = ok i ∧ ¬ (i != 0#u64) = true) ∨
      (∃ i, obj.Reply.next st r s = ok i ∧ (i != 0#u64) = true ∧
        ∃ b, obj.Reply.next_is_head st r s = ok b ∧ ¬ b = true))
    (hnx : L.mem s (rNextA r) &&& ~~~1#u64 ≠ 0#u64 → headBit (L.mem s (rNextA r)) = false →
      L.mem s (rNextA r) &&& ~~~1#u64 ∈ Rp)
    (hpv : L.mem s (rPrevA r) &&& ~~~1#u64 ≠ 0#u64 → L.mem s (rPrevA r) &&& ~~~1#u64 ∈ Rp)
    (hal : ∀ r' ∈ Rp, Aligned (rPrevA r') ∧ Aligned (rNextA r'))
    (hr : r ∈ Rp) (haT : Aligned (rTcbA r)) (haS : Aligned (stA u)) (hTS : rTcbA r ≠ stA u)
    (hcur : ∀ X, WritesIn st s X (fun b => RpLW Rp b ∨ b = rTcbA r ∨ b = stA u) → L.curW X ≠ u)
    (h : ipc.reply_remove st ar s a r u = ok (s', a')) :
    a' = a ∧ WritesIn st s s' (fun b => RpLW Rp b ∨ b = rTcbA r ∨ b = stA u) ∧ L.mem s' (rTcbA r) = 0#u64 := by
  have ha := reply_remove_a st ar hn h
  refine ⟨ha, ?_⟩
  have enx := eq_of_spec_fd (obj.Reply.next.spec (L := L) s r)
  have epv := eq_of_spec_fd (obj.Reply.prev.spec (L := L) s r)
  have ehd := eq_of_spec_fd (obj.Reply.next_is_head.spec (L := L) s r)
  -- the common unlink sequence
  have key : ∀ (nv pv : U64) (s1 s2 s3 s4 s5 : S), nv = L.mem s (rNextA r) &&& ~~~1#u64 →
      ((nv != 0#u64) = true → headBit (L.mem s (rNextA r)) = false) →
      pv = L.mem s (rPrevA r) &&& ~~~1#u64 →
      (if (nv != 0#u64) = true then obj.Reply.set_prev st nv s 0#u64 else ok s) = ok s1 →
      (if (pv != 0#u64) = true then obj.Reply.set_next st pv s1 0#u64 false else ok s1) = ok s2 →
      obj.Reply.set_prev st r s2 0#u64 = ok s3 →
      obj.Reply.set_next st r s3 0#u64 false = ok s4 →
      ipc.reply_unlink st s4 r u = ok s5 →
      WritesIn st s s5 (fun b => RpLW Rp b ∨ b = rTcbA r ∨ b = stA u) ∧ L.mem s5 (rTcbA r) = 0#u64 := by
    intro nv pv s1 s2 s3 s4 s5 hnv hhd hpv' e1 e2 e3 e4 e5
    have w1 : WritesIn st s s1 (fun b => RpLW Rp b ∨ b = rTcbA r ∨ b = stA u) := by
      refine writesIn_ite e1 fun hc hm => ?_
      have hR : nv ∈ Rp := by
        have h0 : nv ≠ 0#u64 := by simpa using hc
        rw [hnv] at h0 ⊢; exact hnx h0 (hhd hc)
      have := obj.Reply.set_prev.spec (L := L) s nv 0#u64
      rw [hm, WP.spec_ok] at this
      obtain ⟨w, rfl, -⟩ := this
      exact (writesIn_wr (hal nv hR).1).mono fun b hb => Or.inl ⟨nv, hR, Or.inl hb⟩
    have w2 : WritesIn st s1 s2 (fun b => RpLW Rp b ∨ b = rTcbA r ∨ b = stA u) := by
      refine writesIn_ite e2 fun hc hm => ?_
      have hR : pv ∈ Rp := by
        have h0 : pv ≠ 0#u64 := by simpa using hc
        rw [hpv'] at h0 ⊢; exact hpv h0
      have := obj.Reply.set_next.spec (L := L) s1 pv 0#u64
      rw [hm, WP.spec_ok] at this
      obtain ⟨w, rfl, -⟩ := this
      exact (writesIn_wr (hal pv hR).2).mono fun b hb => Or.inl ⟨pv, hR, Or.inr hb⟩
    have w3 : WritesIn st s2 s3 (fun b => RpLW Rp b ∨ b = rTcbA r ∨ b = stA u) := by
      have := obj.Reply.set_prev.spec (L := L) s2 r 0#u64
      rw [e3, WP.spec_ok] at this
      obtain ⟨w, rfl, -⟩ := this
      exact (writesIn_wr (hal r hr).1).mono fun b hb => Or.inl ⟨r, hr, Or.inl hb⟩
    have w4 : WritesIn st s3 s4 (fun b => RpLW Rp b ∨ b = rTcbA r ∨ b = stA u) := by
      have := obj.Reply.set_next.spec (L := L) s3 r 0#u64
      rw [e4, WP.spec_ok] at this
      obtain ⟨w, rfl, -⟩ := this
      exact (writesIn_wr (hal r hr).2).mono fun b hb => Or.inl ⟨r, hr, Or.inr hb⟩
    have w04 := ((w1.trans1 w2).trans1 w3).trans1 w4
    unfold ipc.reply_unlink at e5
    obtain ⟨s6, e6, e7⟩ := bind_eq_ok e5
    have x6 : s6 = L.wr s4 (rTcbA r) 0#u64 := by
      have := obj.Reply.set_tcb.spec (L := L) s4 r 0#u64; rw [e6, WP.spec_ok] at this; exact this
    unfold sched.set_thread_state at e7
    obtain ⟨s7, e8, e9⟩ := bind_eq_ok e7
    have x7 : s7 = L.wr s6 (stA u) sched.TS_INACTIVE := by
      have := obj.Tcb.set_state.spec (L := L) s6 u sched.TS_INACTIVE; rw [e8, WP.spec_ok] at this; exact this
    have w07 : WritesIn st s s7 (fun b => RpLW Rp b ∨ b = rTcbA r ∨ b = stA u) := by
      rw [x7, x6]
      refine (w04.trans1 ((writesIn_wr haT).mono fun b hb => Or.inr (Or.inl hb))).trans1
        ((writesIn_wr haS).mono fun b hb => Or.inr (Or.inr hb))
    rw [schedule_tcb_ne (hcur s7 w07)] at e9
    obtain rfl := ok_inj_ff e9
    refine ⟨w07, ?_⟩
    rw [x7, mem_wr_ne' haS haT (Ne.symm hTS), x6, LawfulStore.mem_wr_same haT]
  unfold ipc.reply_remove at h
  rw [enx] at h; simp only [bind_ok] at h
  rw [epv] at h; simp only [bind_ok] at h
  by_cases hc : (L.mem s (rNextA r) &&& ~~~1#u64 != 0#u64) = true
  · rw [if_pos hc, ehd] at h; simp only [bind_ok] at h
    by_cases hb : headBit (L.mem s (rNextA r)) = true
    · exfalso
      rcases hn with ⟨i, hi, hci⟩ | ⟨i, hi, -, b, hb', hbc⟩
      · rw [enx] at hi; rw [← ok_inj_ff hi] at hci; exact hci hc
      · rw [ehd] at hb'; rw [← ok_inj_ff hb'] at hbc; exact hbc hb
    rw [if_neg hb] at h
    obtain ⟨s1, e1, h⟩ := bind_eq_ok h
    obtain ⟨s2, e2, h⟩ := bind_eq_ok h
    obtain ⟨s3, e3, h⟩ := bind_eq_ok h
    obtain ⟨s4, e4, h⟩ := bind_eq_ok h
    obtain ⟨s5, e5, h⟩ := bind_eq_ok h
    obtain ⟨rfl, -⟩ := Prod.mk.inj (ok_inj_ff h).symm
    exact key _ _ s1 s2 s3 s4 _ rfl (fun _ => by simpa using hb) rfl e1 e2 e3 e4 e5
  · rw [if_neg hc] at h
    obtain ⟨s1, e1, h⟩ := bind_eq_ok h
    obtain ⟨s2, e2, h⟩ := bind_eq_ok h
    obtain ⟨s3, e3, h⟩ := bind_eq_ok h
    obtain ⟨s4, e4, h⟩ := bind_eq_ok h
    obtain ⟨s5, e5, h⟩ := bind_eq_ok h
    obtain ⟨rfl, -⟩ := Prod.mk.inj (ok_inj_ff h).symm
    exact key _ _ s1 s2 s3 s4 _ rfl (fun h' => absurd h' hc) rfl e1 e2 e3 e4 e5


/-- **The run's footprint up to `X8`** (module docstring). -/
def RRW (T Rp : Set U64) (X0 : S) (t u rptr usc : U64) (sb : Nat) (b : U64) : Prop :=
  b = stA t ∨ b = stA u ∨ b = faultA u ∨ XferRegW T ∅ b ∨ RpLW Rp b ∨ b = rTcbA rptr ∨ InRing usc sb b ∨
    b = L.nodeAt X0 (L.cpu X0) layout.node.REPROGRAM ∨ b = L.nodeAt X0 (L.cpu X0) layout.node.SCHED_ACTION

/-- **m63's `FinKeep` from a footprint inside `RRW`**, over `Ω` without the
reply link words. -/
theorem finKeep_rrw {T Cs Ω Rp : Set U64} {X0 Y : S} {t u rptr usc : U64} {sb : Nat}
    (hT : TcbPlaced T) (hN : NodePlaced st T X0 (L.cpu X0)) (hcC : L.cpu X0 ∈ Cs)
    (hΩ : ∀ a ∈ Ω, OutsideObjs st T Cs X0 a) (ht : t ∈ T) (hu : u ∈ T)
    (hRpΩ : ∀ b, RpLW Rp b → b ∈ Ω) (hrΩ : rTcbA rptr ∈ Ω)
    (scW : ∀ b, Aligned b → InSC usc sb b → b ∈ Ω)
    (w : WritesIn st X0 Y (RRW (L := L) T Rp X0 t u rptr usc sb)) :
    FinKeep (L := L) T (RΩ Ω Rp) X0 Y rptr usc sb := by
  have ht' := hT t ht
  have hu' := hT u hu
  have vS : (stA t).val = t.val + 3328 := by rw [stA_eq]; exact tcbw_val hT ht (by decide)
  have vSu : (stA u).val = u.val + 3328 := by rw [stA_eq]; exact tcbw_val hT hu (by decide)
  have vF : (faultA u).val = u.val + 3376 := tcbw_val hT hu (by decide)
  have vR : (L.nodeAt X0 (L.cpu X0) layout.node.REPROGRAM).val = L.nodeBase X0 (L.cpu X0) + 56 := by
    rw [nodeAt_val hN (by simp [layout.node.REPROGRAM])]; simp [layout.node.REPROGRAM]
  have vA : (L.nodeAt X0 (L.cpu X0) layout.node.SCHED_ACTION).val = L.nodeBase X0 (L.cpu X0) + 16 := by
    rw [nodeAt_val hN (by simp [layout.node.SCHED_ACTION])]; simp [layout.node.SCHED_ACTION]
  -- an `Ω`-type footprint word
  have oΩ : ∀ b, (RpLW Rp b ∨ b = rTcbA rptr ∨ (Aligned b ∧ InRing usc sb b)) → b ∈ Ω := by
    rintro b (h | rfl | ⟨hb, h⟩)
    · exact hRpΩ b h
    · exact hrΩ
    · exact scW b hb h.inSC
  have tn := ht'.align; have un := hu'.align
  have ntd := hN.disj t ht; have nud := hN.disj u hu
  refine ⟨w.1, w.2.1, ?_, ?_, ?_⟩
  · intro off ho h8 h16 h56
    have vb := nodeAt_val hN ho
    have hba := nodeAt_aligned hN ho h8
    refine w.2.2 _ hba ?_
    intro hw
    have inΩ : ∀ b, b ∈ Ω → b ≠ L.nodeAt X0 (L.cpu X0) off := fun b hb e => by
      have := (hΩ b hb).2.2 _ hcC; rw [e, vb] at this; omega
    rcases hw with e | e | e | e | e | e | e | e | e
    · have := congrArg UScalar.val e; rw [vb, vS] at this; omega
    · have := congrArg UScalar.val e; rw [vb, vSu] at this; omega
    · have := congrArg UScalar.val e; rw [vb, vF] at this; omega
    · rcases e with ⟨y, hy, K, -, h2, -, e⟩ | e
      · have := congrArg UScalar.val e; rw [vb, tcb_wadd_val (hT y hy) (by omega)] at this
        have := hN.disj y hy; omega
      · exact e
    · exact inΩ _ (oΩ _ (Or.inl e)) rfl
    · exact inΩ _ (oΩ _ (Or.inr (Or.inl e))) rfl
    · exact inΩ _ (oΩ _ (Or.inr (Or.inr ⟨hba, e⟩))) rfl
    · have := congrArg UScalar.val e; rw [vb, vR] at this; omega
    · have := congrArg UScalar.val e; rw [vb, vA] at this; omega
  · intro y hy K h1 h2 h3 k1 k2 k3 k4 k5 k6 k7
    have hy' := hT y hy
    have vb := tcb_wadd_val hy' h2
    have ya := hy'.align
    have hba : Aligned (core.num.U64.wrapping_add y K) := by show _ % 8 = 0; rw [vb]; omega
    refine w.2.2 _ hba ?_
    intro hw
    have inΩ : ∀ b, b ∈ Ω → b ≠ core.num.U64.wrapping_add y K := fun b hb e => by
      have := (hΩ b hb).2.1 y hy; rw [e, vb] at this; omega
    rcases hw with e | e | e | e | e | e | e | e | e
    · have := congrArg UScalar.val e; rw [vb, vS] at this
      rcases Nat.lt_or_ge y.val t.val with h | h <;> omega
    · have := congrArg UScalar.val e; rw [vb, vSu] at this
      rcases Nat.lt_or_ge y.val u.val with h | h <;> omega
    · have := congrArg UScalar.val e; rw [vb, vF] at this
      rcases Nat.lt_or_ge y.val u.val with h | h <;> omega
    · rcases e with ⟨z, hz, K', -, h2', -, e⟩ | e
      · have hz' := hT z hz; have za := hz'.align
        have := congrArg UScalar.val e; rw [vb, tcb_wadd_val hz' (by omega)] at this
        rcases Nat.lt_or_ge y.val z.val with h | h <;> omega
      · exact e
    · exact inΩ _ (oΩ _ (Or.inl e)) rfl
    · exact inΩ _ (oΩ _ (Or.inr (Or.inl e))) rfl
    · exact inΩ _ (oΩ _ (Or.inr (Or.inr ⟨hba, e⟩))) rfl
    · have := congrArg UScalar.val e; rw [vb, vR] at this; have := hN.disj y hy; omega
    · have := congrArg UScalar.val e; rw [vb, vA] at this; have := hN.disj y hy; omega
  · rintro b ⟨hb, hnl⟩ hbr hin
    have hO := hΩ b hb
    refine w.2.2 _ hO.1 ?_
    intro hw
    have oT := hO.2.1
    have oN := hO.2.2 _ hcC
    rcases hw with e | e | e | e | e | e | e | e | e
    · have := oT t ht; rw [e, vS] at this; omega
    · have := oT u hu; rw [e, vSu] at this; omega
    · have := oT u hu; rw [e, vF] at this; omega
    · rcases e with ⟨z, hz, K', -, h2', -, e⟩ | e
      · have := oT z hz; rw [e, tcb_wadd_val (hT z hz) (by omega)] at this; omega
      · exact e
    · exact hnl e
    · exact hbr e
    · exact hin e
    · rw [e, vR] at oN; omega
    · rw [e, vA] at oN; omega

end


/-! ## The ring of an SC read through an agreement on its words -/

section ring
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

theorem head_agree {s s' : S} {sc : obj.Sc} {sb : Nat} (hW : RefillsWF st s sc sb)
    (hag : ∀ b, Aligned b → InSC sc sb b → L.mem s' b = L.mem s b) :
    L.refill s' sc (L.rhead s' sc) = L.refill s sc (L.rhead s sc) := by
  obtain ⟨h8, hm, hfit⟩ := hW.bounds
  have := hW.min_le; simp at this
  have hl := hW.head_lt
  have eh : L.rhead s' sc = L.rhead s sc := hag (headA sc) (by addr) ⟨by addr, by addr⟩
  rw [eh]; unfold LawfulStore.refill
  rw [hag (rtA sc (L.rhead s sc)) (by addr) ⟨by addr, by addr⟩,
    hag (raA sc (L.rhead s sc)) (by addr) ⟨by addr, by addr⟩]

theorem amtSum_agree {s s' : S} {sc : obj.Sc} {sb : Nat} (hW : RefillsWF st s sc sb)
    (hag : ∀ b, Aligned b → InSC sc sb b → L.mem s' b = L.mem s b) : L.amtSum s' sc = L.amtSum s sc := by
  obtain ⟨h8, hm, hfit⟩ := hW.bounds
  have := hW.min_le; simp at this
  have em : L.rmax s' sc = L.rmax s sc := hag (maxA sc) (by addr) ⟨by addr, by addr⟩
  have eh : L.rhead s' sc = L.rhead s sc := hag (headA sc) (by addr) ⟨by addr, by addr⟩
  have et : L.rtail s' sc = L.rtail s sc := hag (tailA sc) (by addr) ⟨by addr, by addr⟩
  have ex : ∀ k, L.ix s' sc k = L.ix s sc k := fun k => by unfold LawfulStore.ix; rw [em, eh]
  have es : L.size s' sc = L.size s sc := by unfold LawfulStore.size; rw [em, eh, et]
  unfold LawfulStore.amtSum
  rw [es]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold LawfulStore.rf LawfulStore.refill
  rw [ex k]
  have hl := hW.ix_lt k
  rw [hag (raA sc (L.ix s sc k)) (by addr) ⟨by addr, by addr⟩]

end ring

/-! ## Placement facts at the dispatch state -/

section pl
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- **Placement facts at the dispatch state `X0`** of an accepted ReplyRecv
run (current `t`, reply `rptr`, endpoint `ep`, the reply's thread `u`, its SC
`usc`), from the P1 invariants there (`rrPl_of`). -/
structure RRPl (T Cs Ω Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (X0 : S) (t rptr ep u usc : U64) : Prop where
  hT : TcbPlaced T
  ht : t ∈ T
  hu : u ∈ T
  hut : u ≠ t
  hN : NodePlaced st T X0 (L.cpu X0)
  hcC : L.cpu X0 ∈ Cs
  hΩ : ∀ a ∈ Ω, OutsideObjs st T Cs X0 a
  hSg : SgOK st Ω Sg X0
  hO : ObjsOK st Ω Sg Rp Scs Nt Z X0
  hrR : rptr ∈ Rp
  hnx : L.mem X0 (rNextA rptr) &&& ~~~1#u64 ≠ 0#u64 → headBit (L.mem X0 (rNextA rptr)) = false →
    L.mem X0 (rNextA rptr) &&& ~~~1#u64 ∈ Rp
  hpv : L.mem X0 (rPrevA rptr) &&& ~~~1#u64 ≠ 0#u64 → L.mem X0 (rPrevA rptr) &&& ~~~1#u64 ∈ Rp
  husc : L.mem X0 (scA u) = usc
  hsc0 : usc ≠ 0#u64
  hcS : usc ∈ Scs
  hWF : RefillsWF st X0 usc (Z usc)
  scSg : ∀ b, Aligned b → InSC usc (Z usc) b → b ∈ Sg
  hE : EpPlaced T ep
  hEN : EpOutNodes st Cs X0 ep
  hEΩ : ∀ a ∈ Ω, a.val + 8 ≤ ep.val ∨ ep.val + 16 ≤ a.val
  hq0 : L.mem X0 (epHeadA ep) = 0#u64
  hcur : L.curW X0 = t
  /-- The bound notification (if any) is a placed queue object outside `Ω`. -/
  hNt : L.mem X0 (boundA t) ≠ 0#u64 → L.mem X0 (boundA t) ∈ Nt ∧ EpPlaced T (L.mem X0 (boundA t)) ∧
    EpOutNodes st Cs X0 (L.mem X0 (boundA t)) ∧
    ∀ a ∈ Ω, a.val + 8 ≤ (L.mem X0 (boundA t)).val ∨ (L.mem X0 (boundA t)).val + 16 ≤ a.val
  hTM : Tz T (L.mem X0 (L.nodeAt X0 (L.cpu X0) layout.node.TIMER_MIN))
  hRel : L.mem X0 (L.nodeAt X0 (L.cpu X0) layout.node.RELEASE_HEAD) ≠ 0#u64 →
    L.mem X0 (L.nodeAt X0 (L.cpu X0) layout.node.RELEASE_HEAD) ∈ T ∧
    ∃ zc, RefillsWF st X0 (L.mem X0 (scA (L.mem X0 (L.nodeAt X0 (L.cpu X0) layout.node.RELEASE_HEAD)))) zc ∧
      ∀ b, Aligned b → InSC (L.mem X0 (scA (L.mem X0 (L.nodeAt X0 (L.cpu X0) layout.node.RELEASE_HEAD)))) zc b →
        b ∈ RΩ Ω Rp ∧ b ≠ rTcbA rptr ∧ ¬ InRing usc (Z usc) b
  hBM : ∃ NE, BitmapOK st X0 (L.cpu X0) NE

variable {T Cs Ω Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {X0 : S} {t rptr ep u usc : U64}

theorem RRPl.rpS (P : RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z X0 t rptr ep u usc) :
    ∀ b, RpLW Rp b → b ∈ Sg := by
  rintro b ⟨r', hr', rfl | rfl⟩
  · exact P.hO.prevW hr'
  · exact P.hO.nextW hr'

theorem RRPl.rpA (P : RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z X0 t rptr ep u usc) :
    ∀ r' ∈ Rp, Aligned (rPrevA r') ∧ Aligned (rNextA r') := fun r' hr' => by
  have := P.hO.rp r' hr'
  exact ⟨by show _ % 8 = 0; rw [rPrevA_val this]; omega, by show _ % 8 = 0; rw [rNextA_val this]; omega⟩

theorem RRPl.rtS (P : RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z X0 t rptr ep u usc) : rTcbA rptr ∈ Sg :=
  P.hO.tcbW P.hrR

/-- A reply word (link or `TCB`) is no word of `u`'s SC. -/
theorem RRPl.rp_notSC (P : RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z X0 t rptr ep u usc) {b : U64}
    (hb : RpLW Rp b ∨ b = rTcbA rptr) : ¬ InSC usc (Z usc) b := by
  intro hin
  unfold InSC at hin
  rcases hb with ⟨r', hr', rfl | rfl⟩ | rfl
  · have := P.hO.rpSc r' hr' _ P.hcS; rw [rPrevA_val (P.hO.rp r' hr')] at hin; omega
  · have := P.hO.rpSc r' hr' _ P.hcS; rw [rNextA_val (P.hO.rp r' hr')] at hin; omega
  · have := P.hO.rpSc rptr P.hrR _ P.hcS; rw [rTcbA_val0] at hin; omega

theorem RRPl.vS (P : RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z X0 t rptr ep u usc) {y : U64} (hy : y ∈ T) :
    (stA y).val = y.val + 3328 := by rw [stA_eq]; exact tcbw_val P.hT hy (by decide)

theorem RRPl.aS (P : RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z X0 t rptr ep u usc) {y : U64} (hy : y ∈ T) :
    Aligned (stA y) := by
  show _ % 8 = 0; rw [P.vS hy]; have := (P.hT y hy).align; omega

/-- `Ω` words are no TCB / node words. -/
theorem RRPl.omg_tcb (P : RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z X0 t rptr ep u usc) {b y K : U64}
    (hb : b ∈ Ω) (hy : y ∈ T) (hK : K.val < 4096) : b ≠ core.num.U64.wrapping_add y K := by
  intro e; have := (P.hΩ b hb).2.1 y hy; rw [e, tcb_wadd_val (P.hT y hy) hK] at this; omega

theorem RRPl.omg_node (P : RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z X0 t rptr ep u usc) {b off : U64}
    (hb : b ∈ Ω) (ho : off.val < 4288) : b ≠ L.nodeAt X0 (L.cpu X0) off := by
  intro e; have := (P.hΩ b hb).2.2 _ P.hcC; rw [e, nodeAt_val P.hN ho] at this; omega

theorem RRPl.tcb_node (P : RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z X0 t rptr ep u usc) {y K off : U64}
    (hy : y ∈ T) (hK : K.val < 4096) (ho : off.val < 4288) :
    core.num.U64.wrapping_add y K ≠ L.nodeAt X0 (L.cpu X0) off := by
  intro e; have e' := congrArg UScalar.val e
  rw [tcb_wadd_val (P.hT y hy) hK, nodeAt_val P.hN ho] at e'; have := P.hN.disj y hy; omega

end pl

/-! ## The run to `X3`: the Restart write, the unlink, the receiver's unblock check -/

section x3
variable {S : Type _} {A : Type _} {st : machine.Store S} (ar : machine.Arch A) [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}

set_option maxHeartbeats 1600000 in
/-- **The run from `X0` to `X3`**: the footprint (the Restart write and the
unlink, then the unblock check on `u`'s ring), the reply's `TCB` word cleared,
the Arch value kept, and `u`'s ring after the unblock check: well formed, its
head ready at `X0`'s current time and holding no less (R4, under the ring-sum
bound `hsum` of `RRSum`). -/
theorem rr_x3G {ty : U64} [HfrRestart st ar ty] {X0 X1 X2 X3 : S} {a a1 : A} {t rptr ep u usc : U64} {b9 : Bool}
    (P : RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z X0 t rptr ep u usc) (C : RRChecksG st ar ty X0 a t rptr ep u usc)
    (hsum : L.mem X0 (sporA usc) ≠ 0#u64 → L.amtSum X0 usc < 2 ^ 64)
    (e1 : obj.Tcb.set_state st t X0 sched.TS_RESTART = ok X1)
    (e2 : ipc.reply_remove st ar X1 a rptr u = ok (X2, a1))
    (e3s : sporadic.sc_sporadic st X2 usc = ok b9)
    (e3 : (if b9 then do
      let i13 ← obj.Sc.cpu st usc X2
      let i14 ← obj.node_get st X2 i13 layout.node.CUR_SC
      if usc != i14 then sporadic.unblock_check st X2 usc else ok X2
    else ok X2) = ok X3) :
    a1 = a ∧ X1 = L.wr X0 (stA t) sched.TS_RESTART ∧
    WritesIn st X1 X2 (fun b => RpLW Rp b ∨ b = rTcbA rptr ∨ b = stA u) ∧
    WritesIn st X2 X3 (fun b => InRing usc (Z usc) b ∨ b = L.nodeAt X0 (L.cpu X0) layout.node.REPROGRAM) ∧
    L.mem X2 (rTcbA rptr) = 0#u64 ∧ RefillsWF st X3 usc (Z usc) ∧
    (L.refill X3 usc (L.rhead X3 usc)).time ≤ L.curTime X0 ∧
    (L.refill X0 usc (L.rhead X0 usc)).amount.val ≤ (L.refill X3 usc (L.rhead X3 usc)).amount.val := by
  have hT := P.hT
  have aSt := P.aS P.ht
  have aSu := P.aS P.hu
  have vSt := P.vS P.ht
  have vSu := P.vS P.hu
  have w1 : X1 = L.wr X0 (stA t) sched.TS_RESTART := by
    have := obj.Tcb.set_state.spec (L := L) X0 t sched.TS_RESTART; rw [e1, WP.spec_ok] at this; exact this
  have hrS := P.rtS
  have hrΩ := P.hSg.sub _ hrS
  have aR : Aligned (rTcbA rptr) := (P.hΩ _ hrΩ).1
  have ntS : ∀ b ∈ Ω, b ≠ stA t := fun b hb => by rw [stA_eq]; exact P.omg_tcb hb P.ht (by decide)
  have nuS : ∀ b ∈ Ω, b ≠ stA u := fun b hb => by rw [stA_eq]; exact P.omg_tcb hb P.hu (by decide)
  -- the reply words at `X1` are those of `X0`
  have aNx : Aligned (rNextA rptr) := (P.rpA rptr P.hrR).2
  have aPv : Aligned (rPrevA rptr) := (P.rpA rptr P.hrR).1
  have mNx : L.mem X1 (rNextA rptr) = L.mem X0 (rNextA rptr) := by
    rw [w1]; exact mem_wr_ne' aSt aNx (Ne.symm (ntS _ (P.hSg.sub _ (P.hO.nextW P.hrR))))
  have mPv : L.mem X1 (rPrevA rptr) = L.mem X0 (rPrevA rptr) := by
    rw [w1]; exact mem_wr_ne' aSt aPv (Ne.symm (ntS _ (P.hSg.sub _ (P.hO.prevW P.hrR))))
  have en : obj.Reply.next st rptr X1 = obj.Reply.next st rptr X0 := by
    rw [eq_of_spec_fd (obj.Reply.next.spec (L := L) X1 rptr), eq_of_spec_fd (obj.Reply.next.spec (L := L) X0 rptr),
      mNx]
  have eh : obj.Reply.next_is_head st rptr X1 = obj.Reply.next_is_head st rptr X0 := by
    rw [eq_of_spec_fd (obj.Reply.next_is_head.spec (L := L) X1 rptr),
      eq_of_spec_fd (obj.Reply.next_is_head.spec (L := L) X0 rptr), mNx]
  have hn1 := C.nxt
  simp only [← en, ← eh] at hn1
  have hRT : rTcbA rptr ≠ stA u := nuS _ hrΩ
  -- the current thread is `t ≠ u` while the unlink runs
  have hcur : ∀ X, WritesIn st X1 X (fun b => RpLW Rp b ∨ b = rTcbA rptr ∨ b = stA u) → L.curW X ≠ u := by
    intro X wX
    have aC : Aligned (L.nodeAt X0 (L.cpu X0) layout.node.CUR_THREAD) :=
      nodeAt_aligned P.hN (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
    have k1 : L.ksb X1 = L.ksb X0 := by rw [w1, L.ksb_wr]
    have c1 : L.cpu X1 = L.cpu X0 := by rw [w1, L.cpu_wr]
    show L.mem X (L.nodeAt X (L.cpu X) layout.node.CUR_THREAD) ≠ u
    rw [wX.2.1, c1, nodeAt_of_ksb (wX.1.trans k1)]
    rw [wX.2.2 _ aC ?_]
    · rw [w1, mem_wr_ne' aSt aC (by rw [stA_eq]; exact P.tcb_node P.ht (by decide) (by simp [layout.node.CUR_THREAD]))]
      have := P.hcur; unfold LawfulStore.curW at this; rw [this]; exact Ne.symm P.hut
    rintro (h | h | h)
    · exact P.omg_node (P.hSg.sub _ (P.rpS _ h)) (by simp [layout.node.CUR_THREAD]) rfl
    · exact P.omg_node hrΩ (by simp [layout.node.CUR_THREAD]) h.symm
    · rw [stA_eq] at h; exact P.tcb_node P.hu (by decide) (by simp [layout.node.CUR_THREAD]) h.symm
  have hnx1 : L.mem X1 (rNextA rptr) &&& ~~~1#u64 ≠ 0#u64 → headBit (L.mem X1 (rNextA rptr)) = false →
      L.mem X1 (rNextA rptr) &&& ~~~1#u64 ∈ Rp := by rw [mNx]; exact P.hnx
  have hpv1 : L.mem X1 (rPrevA rptr) &&& ~~~1#u64 ≠ 0#u64 → L.mem X1 (rPrevA rptr) &&& ~~~1#u64 ∈ Rp := by
    rw [mPv]; exact P.hpv
  obtain ⟨ha1, w12, hr2⟩ := rr_remove_foot ar hn1 hnx1 hpv1 P.rpA P.hrR aR aSu hRT hcur e2
  refine ⟨ha1, w1, w12, ?_⟩
  -- `u`'s SC words at `X2` are those of `X0`
  have scΩ : ∀ b, Aligned b → InSC usc (Z usc) b → b ∈ Ω := fun b hb h => P.hSg.sub _ (P.scSg b hb h)
  have k2 : L.ksb X2 = L.ksb X0 := by rw [w12.1, w1, L.ksb_wr]
  have c2 : L.cpu X2 = L.cpu X0 := by rw [w12.2.1, w1, L.cpu_wr]
  have scK : ∀ b, Aligned b → InSC usc (Z usc) b → L.mem X2 b = L.mem X0 b := by
    intro b hb hin
    rw [w12.2.2 b hb ?_, w1, mem_wr_ne' aSt hb (Ne.symm (ntS b (scΩ b hb hin)))]
    rintro (h | h | h)
    · exact P.rp_notSC (Or.inl h) hin
    · exact P.rp_notSC (Or.inr h) hin
    · exact nuS b (scΩ b hb hin) h
  have nodeK : ∀ off : U64, off.val < 4288 → off.val % 8 = 0 →
      L.mem X2 (L.nodeAt X0 (L.cpu X0) off) = L.mem X0 (L.nodeAt X0 (L.cpu X0) off) := by
    intro off ho h8
    have aN := nodeAt_aligned P.hN ho h8
    rw [w12.2.2 _ aN ?_, w1, mem_wr_ne' aSt aN (by rw [stA_eq]; exact P.tcb_node P.ht (by decide) ho)]
    rintro (h | h | h)
    · exact P.omg_node (P.hSg.sub _ (P.rpS _ h)) ho rfl
    · exact P.omg_node hrΩ ho h.symm
    · rw [stA_eq] at h; exact P.tcb_node P.hu (by decide) ho h.symm
  have eN2 : ∀ o, L.nodeAt X2 (L.cpu X2) o = L.nodeAt X0 (L.cpu X0) o := fun o => by
    rw [c2, nodeAt_of_ksb k2]
  have hW2 : RefillsWF st X2 usc (Z usc) := P.hWF.agree scK
  have ect : L.curTime X2 = L.curTime X0 := by
    unfold LawfulStore.curTime LawfulStore.nodeA
    rw [eN2]; exact nodeK _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
  have hrd0 : (L.refill X0 usc (L.rhead X0 usc)).time ≤ L.curTime X0 := by
    obtain ⟨b, hb, hbt⟩ := C.rdy
    rw [ready_ok] at hb; subst hbt; exact of_decide_eq_true (ok_inj_ff hb)
  have eh2 := head_agree P.hWF scK
  have hrep : Aligned (L.nodeA X2 layout.node.REPROGRAM) ∧ Outside (L.nodeA X2 layout.node.REPROGRAM) usc (Z usc) := by
    unfold LawfulStore.nodeA; rw [eN2]
    exact ⟨nodeAt_aligned P.hN (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM]),
      node_outside_sc P.hN P.hcC P.hΩ scΩ (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])⟩
  have eR : L.nodeA X2 layout.node.REPROGRAM = L.nodeAt X0 (L.cpu X0) layout.node.REPROGRAM := by
    unfold LawfulStore.nodeA; rw [eN2]
  have same : X3 = X2 → WritesIn st X2 X3 (fun b => InRing usc (Z usc) b ∨
      b = L.nodeAt X0 (L.cpu X0) layout.node.REPROGRAM) ∧
      L.mem X2 (rTcbA rptr) = 0#u64 ∧ RefillsWF st X3 usc (Z usc) ∧
      (L.refill X3 usc (L.rhead X3 usc)).time ≤ L.curTime X0 ∧
      (L.refill X0 usc (L.rhead X0 usc)).amount.val ≤ (L.refill X3 usc (L.rhead X3 usc)).amount.val := by
    rintro rfl
    exact ⟨WritesIn.refl _ _, hr2, hW2, by rw [eh2]; exact hrd0, by rw [eh2]⟩
  have ub : sporadic.unblock_check st X2 usc = ok X3 → L.mem X2 (sporA usc) ≠ 0#u64 →
      WritesIn st X2 X3 (fun b => InRing usc (Z usc) b ∨ b = L.nodeAt X0 (L.cpu X0) layout.node.REPROGRAM) ∧
      L.mem X2 (rTcbA rptr) = 0#u64 ∧ RefillsWF st X3 usc (Z usc) ∧
      (L.refill X3 usc (L.rhead X3 usc)).time ≤ L.curTime X0 ∧
      (L.refill X0 usc (L.rhead X0 usc)).amount.val ≤ (L.refill X3 usc (L.rhead X3 usc)).amount.val := by
    intro hu hsp
    have hsp0 : L.mem X0 (sporA usc) ≠ 0#u64 := by
      have := P.hWF.inside
      obtain ⟨h8, hm, hfit⟩ := P.hWF.bounds
      have vsp : (sporA usc).val = usc.val + 64 := by
        unfold sporA layout.sc.SPORADIC
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
      rw [← scK (sporA usc) (by show _ % 8 = 0; rw [vsp]; omega) ⟨by rw [vsp]; omega, by rw [vsp]; omega⟩]
      exact hsp
    have hs2 : L.amtSum X2 usc < 2 ^ 64 := by rw [amtSum_agree P.hWF scK]; exact hsum hsp0
    have hr2' : sporadic.ready st X2 usc = ok true := sporadic.ready_of (by rw [eh2, ect]; exact hrd0)
    obtain ⟨hW3, ht3, ha3⟩ := unblock_check_r4 hW2 hrep hs2 hr2' hu
    have wf := sporadic.unblock_check.fr hW2 hrep
    rw [hu, WP.spec_ok, eR] at wf
    exact ⟨wf, hr2, hW3, by rw [← ect]; exact ht3, by rw [← eh2]; exact ha3⟩
  rw [sc_sporadic_eq] at e3s
  have eb9 := (ok_inj_ff e3s).symm
  by_cases hb : b9 = true
  · rw [if_pos hb] at e3
    obtain ⟨i13, -, e3⟩ := bind_eq_ok e3
    obtain ⟨i14, -, e3⟩ := bind_eq_ok e3
    have hsp : L.mem X2 (sporA usc) ≠ 0#u64 := by
      rw [eb9, if_neg P.hsc0] at hb; simpa using hb
    by_cases hne : (usc != i14) = true
    · rw [if_pos hne] at e3; exact ub e3 hsp
    · rw [if_neg hne] at e3; exact same (ok_inj_ff e3).symm
  · rw [if_neg hb] at e3; exact same (ok_inj_ff e3).symm

/-- `rr_x3G` at an UnknownSyscall fault (pf1). -/
theorem rr_x3 {X0 X1 X2 X3 : S} {a a1 : A} {t rptr ep u usc : U64} {b9 : Bool}
    (P : RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z X0 t rptr ep u usc) (C : RRChecks st ar X0 a t rptr ep u usc)
    (hsum : L.mem X0 (sporA usc) ≠ 0#u64 → L.amtSum X0 usc < 2 ^ 64)
    (e1 : obj.Tcb.set_state st t X0 sched.TS_RESTART = ok X1)
    (e2 : ipc.reply_remove st ar X1 a rptr u = ok (X2, a1))
    (e3s : sporadic.sc_sporadic st X2 usc = ok b9)
    (e3 : (if b9 then do
      let i13 ← obj.Sc.cpu st usc X2
      let i14 ← obj.node_get st X2 i13 layout.node.CUR_SC
      if usc != i14 then sporadic.unblock_check st X2 usc else ok X2
    else ok X2) = ok X3) :
    a1 = a ∧ X1 = L.wr X0 (stA t) sched.TS_RESTART ∧
    WritesIn st X1 X2 (fun b => RpLW Rp b ∨ b = rTcbA rptr ∨ b = stA u) ∧
    WritesIn st X2 X3 (fun b => InRing usc (Z usc) b ∨ b = L.nodeAt X0 (L.cpu X0) layout.node.REPROGRAM) ∧
    L.mem X2 (rTcbA rptr) = 0#u64 ∧ RefillsWF st X3 usc (Z usc) ∧
    (L.refill X3 usc (L.rhead X3 usc)).time ≤ L.curTime X0 ∧
    (L.refill X0 usc (L.rhead X0 usc)).amount.val ≤ (L.refill X3 usc (L.rhead X3 usc)).amount.val := by
  apply rr_x3G (ty := fl4_abi.consts.fault.UnknownSyscall) <;> assumption


end x3


/-! ## Reads of TCB registers / fault words; endpoint words against the footprint -/

section rd
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- The address of register `r` of `t`. -/
def regA (t r : U64) : U64 :=
  core.num.U64.wrapping_add (core.num.U64.wrapping_add t layout.tcb.REGS) (core.num.U64.wrapping_mul r 8#u64)

theorem reg_ok (s : S) (t r : U64) : obj.Tcb.reg st t s r = ok (L.mem s (regA t r)) := by
  unfold obj.Tcb.reg regA; simp only [lift, bind_ok, L.read_eq]

theorem regA_val {t r : U64} (h : TcbAddr t) (hr : r.val < 384) : (regA t r).val = t.val + 256 + 8 * r.val := by
  have := h.fits
  unfold regA
  simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]
  omega

theorem regA_eq {t r : U64} (h : TcbAddr t) (hr : r.val < 384) :
    ∃ K : U64, K.val = 256 + 8 * r.val ∧ regA t r = core.num.U64.wrapping_add t K := by
  refine ⟨⟨BitVec.ofNat 64 (256 + 8 * r.val)⟩, ?_, ?_⟩
  · show (BitVec.ofNat 64 (256 + 8 * r.val)).toNat = _
    simp; omega
  · apply UScalar.eq_of_val_eq
    rw [regA_val h hr, tcb_wadd_val h (by show (BitVec.ofNat 64 (256 + 8 * r.val)).toNat < 4096; simp; omega)]
    show _ = t.val + (BitVec.ofNat 64 (256 + 8 * r.val)).toNat
    simp; omega

end rd

section x8
variable {S : Type _} {A : Type _} {st : machine.Store S} (ar : machine.Arch A) [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}

/-- A queue object's words (placed, outside the nodes and `Ω`) are no
footprint words. -/
theorem rrw_ep {X0 : S} {t rptr ep u usc e : U64}
    (P : RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z X0 t rptr ep u usc)
    (hE : EpPlaced T e) (hEN : EpOutNodes st Cs X0 e) (hEΩ : ∀ a ∈ Ω, a.val + 8 ≤ e.val ∨ e.val + 16 ≤ a.val)
    {b : U64} (hb : b.val = e.val ∨ b.val = e.val + 8) : ¬ RRW (L := L) T Rp X0 t u rptr usc (Z usc) b := by
  have ea := hE.align
  have hba : Aligned b := by show _ % 8 = 0; omega
  have oT : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → b ≠ core.num.U64.wrapping_add y K := fun y hy K hK e' => by
    have := hE.disj y hy; rw [e', tcb_wadd_val (P.hT y hy) hK] at hb; omega
  have oΩ : ∀ a ∈ Ω, b ≠ a := fun a ha e' => by have := hEΩ a ha; rw [← e'] at this; omega
  have oN : ∀ off : U64, off.val < 4288 → b ≠ L.nodeAt X0 (L.cpu X0) off := fun off ho e' => by
    have := hEN.1 _ P.hcC; rw [e', nodeAt_val P.hN ho] at hb; omega
  intro hw
  rcases hw with e' | e' | e' | e' | e' | e' | e' | e' | e'
  · rw [stA_eq] at e'; exact oT t P.ht _ (by decide) e'
  · rw [stA_eq] at e'; exact oT u P.hu _ (by decide) e'
  · exact oT u P.hu _ (by decide) e'
  · rcases e' with ⟨y, hy, K, -, h2, -, e'⟩ | e'
    · exact oT y hy K (by omega) e'
    · exact e'
  · exact oΩ _ (P.hSg.sub _ (P.rpS _ e')) rfl
  · exact oΩ _ (P.hSg.sub _ P.rtS) e'
  · exact oΩ _ (P.hSg.sub _ (P.scSg b hba e'.inSC)) rfl
  · exact oN _ (by simp [layout.node.REPROGRAM]) e'
  · exact oN _ (by simp [layout.node.SCHED_ACTION]) e'

/-- A ks word is in `RΩ` and none of the reply / ring words. -/
theorem RRPl.ks {X0 : S} {t rptr ep u usc : U64}
    (P : RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z X0 t rptr ep u usc) {o : U64} (h1 : o.val < 13568) (h2 : o.val % 8 = 0) :
    core.num.U64.wrapping_add (L.ksb X0) o ∈ RΩ Ω Rp ∧ core.num.U64.wrapping_add (L.ksb X0) o ≠ rTcbA rptr ∧
      ¬ InRing usc (Z usc) (core.num.U64.wrapping_add (L.ksb X0) o) := by
  have hm := P.hSg.ksΩ o h1 h2
  have ksv : (core.num.U64.wrapping_add (L.ksb X0) o).val = (L.ksb X0).val + o.val := by
    have := P.hN.fits
    simp only [LawfulStore.nodeBase] at this
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  have nS : ∀ b ∈ Sg, b ≠ core.num.U64.wrapping_add (L.ksb X0) o := fun b hb e => by
    have := P.hSg.ks _ hb; rw [e, ksv] at this; omega
  refine ⟨⟨hm, fun h => nS _ (P.rpS _ h) rfl⟩, fun e => nS _ P.rtS e.symm, fun hin => ?_⟩
  exact nS _ (P.scSg _ (P.hΩ _ hm).1 hin.inSC) rfl


set_option maxHeartbeats 1600000 in
/-- **`RRR3` at `X3`** (`u`'s fault type and `t`'s label, read before the
restart flag is known): the words are TCB words below the state word, not
written from `X0` to `X3`. -/
theorem rr_r3G {ty : U64} [HfrRestart st ar ty] {X0 X1 X2 X3 : S} {a a1 : A} {t rptr ep u usc : U64} {b9 : Bool}
    (P : RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z X0 t rptr ep u usc) (C : RRChecksG st ar ty X0 a t rptr ep u usc)
    (hsum : L.mem X0 (sporA usc) ≠ 0#u64 → L.amtSum X0 usc < 2 ^ 64)
    (e1 : obj.Tcb.set_state st t X0 sched.TS_RESTART = ok X1)
    (e2 : ipc.reply_remove st ar X1 a rptr u = ok (X2, a1))
    (e3s : sporadic.sc_sporadic st X2 usc = ok b9)
    (e3 : (if b9 then do
      let i13 ← obj.Sc.cpu st usc X2
      let i14 ← obj.node_get st X2 i13 layout.node.CUR_SC
      if usc != i14 then sporadic.unblock_check st X2 usc else ok X2
    else ok X2) = ok X3) : RRR3G (st := st) ty X3 t u := by
  obtain ⟨-, w1, w12, w23, -⟩ := rr_x3G ar P C hsum e1 e2 e3s e3
  have hT := P.hT
  have ht' := hT t P.ht
  have hu' := hT u P.hu
  have aSt := P.aS P.ht
  have hrΩ := P.hSg.sub _ P.rtS
  have scΩ : ∀ b, Aligned b → InSC usc (Z usc) b → b ∈ Ω := fun b hb h => P.hSg.sub _ (P.scSg b hb h)
  -- TCB words of `t` / `u` below the state at `X3`
  have tK3 : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3328 →
      L.mem X3 (core.num.U64.wrapping_add y K) = L.mem X0 (core.num.U64.wrapping_add y K) := by
    intro y hy K hK h8 hK3
    have hy' := hT y hy
    have vb := tcb_wadd_val hy' hK
    have hba : Aligned (core.num.U64.wrapping_add y K) := by show _ % 8 = 0; rw [vb]; have := hy'.align; omega
    have nΩ : ∀ b ∈ Ω, b ≠ core.num.U64.wrapping_add y K := fun b hb => P.omg_tcb hb hy hK
    rw [w23.2.2 _ hba ?_, w12.2.2 _ hba ?_, w1, mem_wr_ne' aSt hba ?_]
    · rw [stA_eq]; exact tcbw_ne ht' hy' (by decide) hK (Or.inr (by simp; omega))
    · rintro (h | h | h)
      · exact nΩ _ (P.hSg.sub _ (P.rpS _ h)) rfl
      · exact nΩ _ hrΩ h.symm
      · rw [stA_eq] at h; exact tcbw_ne hy' hu' hK (by decide) (Or.inr (by simp; omega)) h
    · rintro (h | h)
      · exact nΩ _ (scΩ _ hba h.inSC) rfl
      · exact P.tcb_node hy hK (by simp [layout.node.REPROGRAM]) h
  -- RRR3
  have hft3 : obj.Tcb.fault_type st u X3 = ok ty := by
    obtain ⟨i, hi, hc⟩ := C.uft
    rw [fault_type_ok] at hi ⊢
    have e3328 : L.mem X3 (faultA u) = L.mem X0 (faultA u) := tK3 u P.hu 3376#u64 (by decide) (by decide) (by decide)
    rw [e3328, ok_inj_ff hi]; exact congrArg ok (UScalar.eq_of_val_eq (by simpa using hc))
  have hMI : (layout.reg.MSG_INFO).val < 384 := by simp
  have hlb3 : ∃ tag, msg.msg_info st X3 t = ok tag ∧ tag.label = 0#u64 := by
    obtain ⟨info, hmi, -, hl⟩ := C.info
    refine ⟨info, ?_, UScalar.eq_of_val_eq (by simpa using hl)⟩
    obtain ⟨K, hK, eK⟩ := regA_eq ht' hMI
    have e : L.mem X3 (regA t layout.reg.MSG_INFO) = L.mem X0 (regA t layout.reg.MSG_INFO) := by
      rw [eK]; exact tK3 t P.ht K (by simp at hK; omega) (by simp at hK; omega) (by simp at hK; omega)
    unfold msg.msg_info at hmi ⊢
    rw [reg_ok] at hmi ⊢; rw [e]; exact hmi
  exact ⟨hft3, hlb3⟩

/-- `rr_r3G` at an UnknownSyscall fault (pf1). -/
theorem rr_r3 {X0 X1 X2 X3 : S} {a a1 : A} {t rptr ep u usc : U64} {b9 : Bool}
    (P : RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z X0 t rptr ep u usc) (C : RRChecks st ar X0 a t rptr ep u usc)
    (hsum : L.mem X0 (sporA usc) ≠ 0#u64 → L.amtSum X0 usc < 2 ^ 64)
    (e1 : obj.Tcb.set_state st t X0 sched.TS_RESTART = ok X1)
    (e2 : ipc.reply_remove st ar X1 a rptr u = ok (X2, a1))
    (e3s : sporadic.sc_sporadic st X2 usc = ok b9)
    (e3 : (if b9 then do
      let i13 ← obj.Sc.cpu st usc X2
      let i14 ← obj.node_get st X2 i13 layout.node.CUR_SC
      if usc != i14 then sporadic.unblock_check st X2 usc else ok X2
    else ok X2) = ok X3) : RRR3 (st := st) X3 t u := by
  apply rr_r3G (ty := fl4_abi.consts.fault.UnknownSyscall) <;> assumption


set_option maxHeartbeats 3200000 in
/-- **The run from `X0` to `X8`**: the reads `RRR3` at `X3`, the Arch value
kept, `FinKeep` at `X6` and `X8` (with the action word kept to `X6`), the
explicit action / state writes, and the general path's reads `sc2`, `sch6`,
`sc6`, `rdy6`, `suf6` (R4, under the ring-sum bound), `pst`, `st7`, `act8`,
`ct8`, `rt8`, `ntfn8`, `ep8`. -/
theorem rr_x8G {ty : U64} [HfrRestart st ar ty] {X0 X1 X2 X3 X4 X5 X6 X7 X8 : S} {a a1 a2 : A} {t rptr ep u usc : U64} {b9 restart : Bool}
    (P : RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z X0 t rptr ep u usc) (C : RRChecksG st ar ty X0 a t rptr ep u usc)
    (hsum : L.mem X0 (sporA usc) ≠ 0#u64 → L.amtSum X0 usc < 2 ^ 64)
    (e1 : obj.Tcb.set_state st t X0 sched.TS_RESTART = ok X1)
    (e2 : ipc.reply_remove st ar X1 a rptr u = ok (X2, a1))
    (e3s : sporadic.sc_sporadic st X2 usc = ok b9)
    (e3 : (if b9 then do
      let i13 ← obj.Sc.cpu st usc X2
      let i14 ← obj.node_get st X2 i13 layout.node.CUR_SC
      if usc != i14 then sporadic.unblock_check st X2 usc else ok X2
    else ok X2) = ok X3)
    (e4 : faults.handle_fault_reply st ar X3 a1 u t = ok (restart, X4, a2))
    (e5 : faults.clear_fault st X4 u = ok X5)
    (e6 : obj.Tcb.set_state st u X5 sched.TS_RESTART = ok X6)
    (e7 : sched.set_action st X6 u = ok X7)
    (e8 : obj.Tcb.set_state st t X7 sched.TS_RUNNING = ok X8) :
    RRR3G (st := st) ty X3 t u ∧ a2 = a ∧ FinKeep (L := L) T (RΩ Ω Rp) X0 X8 rptr usc (Z usc) ∧
    WritesIn st X0 X8 (RRW (L := L) T Rp X0 t u rptr usc (Z usc)) ∧
    (∀ K : U64, K.val < 3328 → K.val % 8 = 0 →
      L.mem X8 (core.num.U64.wrapping_add t K) = L.mem X0 (core.num.U64.wrapping_add t K)) ∧
    obj.Tcb.sc st u X2 = ok usc ∧ sched.schedule_tcb st X6 u = ok X6 ∧ obj.Tcb.sc st u X6 = ok usc ∧
    sporadic.ready st X6 usc = ok true ∧ sporadic.sufficient st ar X6 a2 usc 0#u64 = ok true ∧
    sched.possible_switch_to st X6 u = ok X7 ∧ obj.Tcb.state st t X7 = ok sched.TS_RESTART ∧
    L.actionW X8 = u ∧ L.actionW X8 ≠ sched.ACTION_RESUME_CURRENT ∧ sched.cur_thread st X8 = ok t ∧
    obj.Reply.tcb st rptr X8 = ok 0#u64 ∧
    (∃ n, obj.Tcb.bound_ntfn st t X8 = ok n ∧
      (n = 0#u64 ∨ (n ≠ 0#u64 ∧ ∃ i7, obj.Ntfn.state st n X8 = ok i7 ∧ ¬ i7 = obj.NTFN_ACTIVE ∧
        notification.maybe_return_sched_context st X8 n t = ok X8))) ∧
    obj.Ep.state st ep X8 = ok obj.EP_IDLE := by
  obtain ⟨ha1, w1, w12, w23, hr2, hW3, ht3, ha3⟩ := rr_x3G ar P C hsum e1 e2 e3s e3
  subst a1
  have hT := P.hT
  have ht' := hT t P.ht
  have hu' := hT u P.hu
  have aSt := P.aS P.ht
  have aSu := P.aS P.hu
  have vSt := P.vS P.ht
  have vSu := P.vS P.hu
  have hrS := P.rtS
  have hrΩ := P.hSg.sub _ hrS
  have aR : Aligned (rTcbA rptr) := (P.hΩ _ hrΩ).1
  have scΩ : ∀ b, Aligned b → InSC usc (Z usc) b → b ∈ Ω := fun b hb h => P.hSg.sub _ (P.scSg b hb h)
  have vF : (faultA u).val = u.val + 3376 := tcbw_val hT P.hu (by decide)
  have aF : Aligned (faultA u) := by show _ % 8 = 0; rw [vF]; have := hu'.align; omega
  have k1 : L.ksb X1 = L.ksb X0 := by rw [w1, L.ksb_wr]
  have c1 : L.cpu X1 = L.cpu X0 := by rw [w1, L.cpu_wr]
  have k3 : L.ksb X3 = L.ksb X0 := by rw [w23.1, w12.1, k1]
  have c3 : L.cpu X3 = L.cpu X0 := by rw [w23.2.1, w12.2.1, c1]
  -- TCB words of `t` / `u` below the state at `X3`
  have tK3 : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3328 →
      L.mem X3 (core.num.U64.wrapping_add y K) = L.mem X0 (core.num.U64.wrapping_add y K) := by
    intro y hy K hK h8 hK3
    have hy' := hT y hy
    have vb := tcb_wadd_val hy' hK
    have hba : Aligned (core.num.U64.wrapping_add y K) := by show _ % 8 = 0; rw [vb]; have := hy'.align; omega
    have nΩ : ∀ b ∈ Ω, b ≠ core.num.U64.wrapping_add y K := fun b hb => P.omg_tcb hb hy hK
    rw [w23.2.2 _ hba ?_, w12.2.2 _ hba ?_, w1, mem_wr_ne' aSt hba ?_]
    · rw [stA_eq]; exact tcbw_ne ht' hy' (by decide) hK (Or.inr (by simp; omega))
    · rintro (h | h | h)
      · exact nΩ _ (P.hSg.sub _ (P.rpS _ h)) rfl
      · exact nΩ _ hrΩ h.symm
      · rw [stA_eq] at h; exact tcbw_ne hy' hu' hK (by decide) (Or.inr (by simp; omega)) h
    · rintro (h | h)
      · exact nΩ _ (scΩ _ hba h.inSC) rfl
      · exact P.tcb_node hy hK (by simp [layout.node.REPROGRAM]) h
  -- RRR3
  have hft3 : obj.Tcb.fault_type st u X3 = ok ty := by
    obtain ⟨i, hi, hc⟩ := C.uft
    rw [fault_type_ok] at hi ⊢
    have e3328 : L.mem X3 (faultA u) = L.mem X0 (faultA u) := tK3 u P.hu 3376#u64 (by decide) (by decide) (by decide)
    rw [e3328, ok_inj_ff hi]; exact congrArg ok (UScalar.eq_of_val_eq (by simpa using hc))
  have hMI : (layout.reg.MSG_INFO).val < 384 := by simp
  have hlb3 : ∃ tag, msg.msg_info st X3 t = ok tag ∧ tag.label = 0#u64 := by
    obtain ⟨info, hmi, -, hl⟩ := C.info
    refine ⟨info, ?_, UScalar.eq_of_val_eq (by simpa using hl)⟩
    obtain ⟨K, hK, eK⟩ := regA_eq ht' hMI
    have e : L.mem X3 (regA t layout.reg.MSG_INFO) = L.mem X0 (regA t layout.reg.MSG_INFO) := by
      rw [eK]; exact tK3 t P.ht K (by simp at hK; omega) (by simp at hK; omega) (by simp at hK; omega)
    unfold msg.msg_info at hmi ⊢
    rw [reg_ok] at hmi ⊢; rw [e]; exact hmi
  have R3 : RRR3G (st := st) ty X3 t u := ⟨hft3, hlb3⟩
  obtain ⟨hrs, ha2⟩ := HfrRestart.restart (st := st) (ar := ar) hft3 hlb3 e4
  subst a2
  refine ⟨R3, rfl, ?_⟩
  -- X3 → X6
  have w34 := faults.handle_fault_reply.rg (L := L) (ar := ar) (T := T) (s := X3) (a := a) (snd := t) hT P.hu
  rw [e4, WP.spec_ok] at w34
  have x5 : X5 = L.wr X4 (faultA u) fl4_abi.consts.fault.NullFault := by
    unfold faults.clear_fault at e5
    have := obj.Tcb.set_fault_type.spec (L := L) X4 u fl4_abi.consts.fault.NullFault
    rw [e5, WP.spec_ok] at this; exact this
  have x6 : X6 = L.wr X5 (stA u) sched.TS_RESTART := by
    have := obj.Tcb.set_state.spec (L := L) X5 u sched.TS_RESTART; rw [e6, WP.spec_ok] at this; exact this
  have k6 : L.ksb X6 = L.ksb X0 := by rw [x6, L.ksb_wr, x5, L.ksb_wr, w34.1, k3]
  have c6 : L.cpu X6 = L.cpu X0 := by rw [x6, L.cpu_wr, x5, L.cpu_wr, w34.2.1, c3]
  have x7 : X7 = L.wr X6 (L.nodeAt X0 (L.cpu X0) layout.node.SCHED_ACTION) u := by
    rw [set_action_ok] at e7; rw [← ok_inj_ff e7, c6, nodeAt_of_ksb k6]
  have x8 : X8 = L.wr X7 (stA t) sched.TS_RUNNING := by
    have := obj.Tcb.set_state.spec (L := L) X7 t sched.TS_RUNNING; rw [e8, WP.spec_ok] at this; exact this
  have aA : Aligned (L.nodeAt X0 (L.cpu X0) layout.node.SCHED_ACTION) :=
    nodeAt_aligned P.hN (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
  have vA : (L.nodeAt X0 (L.cpu X0) layout.node.SCHED_ACTION).val = L.nodeBase X0 (L.cpu X0) + 16 := by
    rw [nodeAt_val P.hN (by simp [layout.node.SCHED_ACTION])]; simp [layout.node.SCHED_ACTION]
  have vRp : (L.nodeAt X0 (L.cpu X0) layout.node.REPROGRAM).val = L.nodeBase X0 (L.cpu X0) + 56 := by
    rw [nodeAt_val P.hN (by simp [layout.node.REPROGRAM])]; simp [layout.node.REPROGRAM]
  have tnA : ∀ y ∈ T, ∀ K : U64, K.val < 4096 →
      core.num.U64.wrapping_add y K ≠ L.nodeAt X0 (L.cpu X0) layout.node.SCHED_ACTION :=
    fun y hy K hK => P.tcb_node hy hK (by simp [layout.node.SCHED_ACTION])
  have oA : ∀ b ∈ Ω, b ≠ L.nodeAt X0 (L.cpu X0) layout.node.SCHED_ACTION :=
    fun b hb => P.omg_node hb (by simp [layout.node.SCHED_ACTION])
  let F6 : U64 → Prop := fun b => RRW (L := L) T Rp X0 t u rptr usc (Z usc) b ∧
    b ≠ L.nodeAt X0 (L.cpu X0) layout.node.SCHED_ACTION
  have w06 : WritesIn st X0 X6 F6 := by
    have a1 : WritesIn st X0 X1 F6 := by
      rw [w1]; refine (writesIn_wr aSt).mono fun b hb => ⟨Or.inl hb, ?_⟩
      rw [hb, stA_eq]; exact tnA t P.ht _ (by decide)
    have a2 : WritesIn st X1 X2 F6 := w12.mono fun b hb => by
      rcases hb with h | h | h
      · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))), oA _ (P.hSg.sub _ (P.rpS _ h))⟩
      · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))), by rw [h]; exact oA _ hrΩ⟩
      · exact ⟨Or.inr (Or.inl h), by rw [h, stA_eq]; exact tnA u P.hu _ (by decide)⟩
    have a3 : WritesIn st X2 X3 F6 := w23.mono' fun b hba hb => by
      rcases hb with h | h
      · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))), oA _ (scΩ _ hba h.inSC)⟩
      · refine ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))), ?_⟩
        intro e; rw [h] at e; have := congrArg UScalar.val e; rw [vRp, vA] at this; omega
    have a4 : WritesIn st X3 X4 F6 := w34.mono fun b hb => by
      refine ⟨Or.inr (Or.inr (Or.inr (Or.inl hb))), ?_⟩
      rcases hb with ⟨y, hy, K, -, h2, -, rfl⟩ | h
      · exact tnA y hy K (by omega)
      · exact absurd h (Set.notMem_empty _)
    have a5 : WritesIn st X4 X5 F6 := by
      rw [x5]; refine (writesIn_wr aF).mono fun b hb => ⟨Or.inr (Or.inr (Or.inl hb)), ?_⟩
      rw [hb]; exact tnA u P.hu _ (by decide)
    have a6 : WritesIn st X5 X6 F6 := by
      rw [x6]; refine (writesIn_wr aSu).mono fun b hb => ⟨Or.inr (Or.inl hb), ?_⟩
      rw [hb, stA_eq]; exact tnA u P.hu _ (by decide)
    exact ((((a1.trans1 a2).trans1 a3).trans1 a4).trans1 a5).trans1 a6
  have w08 : WritesIn st X0 X8 (RRW (L := L) T Rp X0 t u rptr usc (Z usc)) := by
    have a7 : WritesIn st X6 X7 (RRW (L := L) T Rp X0 t u rptr usc (Z usc)) := by
      rw [x7]; exact (writesIn_wr aA).mono fun b hb =>
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hb)))))))
    have a8 : WritesIn st X7 X8 (RRW (L := L) T Rp X0 t u rptr usc (Z usc)) := by
      rw [x8]; exact (writesIn_wr aSt).mono fun b hb => Or.inl hb
    exact ((w06.mono fun b hb => hb.1).trans1 a7).trans1 a8
  have hRpΩ : ∀ b, RpLW Rp b → b ∈ Ω := fun b h => P.hSg.sub _ (P.rpS _ h)
  have K2 : FinKeep (L := L) T (RΩ Ω Rp) X0 X2 rptr usc (Z usc) := by
    refine finKeep_rrw hT P.hN P.hcC P.hΩ P.ht P.hu hRpΩ hrΩ scΩ ?_
    have a1 : WritesIn st X0 X1 (RRW (L := L) T Rp X0 t u rptr usc (Z usc)) := by
      rw [w1]; exact (writesIn_wr aSt).mono fun b hb => Or.inl hb
    refine a1.trans1 (w12.mono fun b hb => ?_)
    rcases hb with h | h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inl h)
  have K6 := finKeep_rrw hT P.hN P.hcC P.hΩ P.ht P.hu hRpΩ hrΩ scΩ (w06.mono fun b hb => hb.1)
  have K8 := finKeep_rrw hT P.hN P.hcC P.hΩ P.ht P.hu hRpΩ hrΩ scΩ w08
  -- `t`'s words below the state (registers, slots) are kept to `X8`
  have w34u := faults.handle_fault_reply.rg (L := L) (ar := ar) (T := {u}) (s := X3) (a := a) (snd := t)
    (fun y hy => by rw [Set.mem_singleton_iff.1 hy]; exact hu') (Set.mem_singleton u)
  rw [e4, WP.spec_ok] at w34u
  have htw : ∀ K : U64, K.val < 3328 → K.val % 8 = 0 →
      L.mem X8 (core.num.U64.wrapping_add t K) = L.mem X0 (core.num.U64.wrapping_add t K) := by
    intro K hK h8
    have vb := tcb_wadd_val ht' (show K.val < 4096 by omega)
    have hba : Aligned (core.num.U64.wrapping_add t K) := by show _ % 8 = 0; rw [vb]; have := ht'.align; omega
    have nut : ∀ K' : U64, K'.val < 4096 → core.num.U64.wrapping_add u K' ≠ core.num.U64.wrapping_add t K :=
      fun K' hK' => tcbw_ne hu' ht' hK' (by omega) (Or.inl P.hut)
    rw [x8, mem_wr_ne' aSt hba (by rw [stA_eq]; exact tcbw_ne ht' ht' (by decide) (by omega) (Or.inr (by simp; omega))),
      x7, mem_wr_ne' aA hba (Ne.symm (tnA t P.ht K (by omega))), x6,
      mem_wr_ne' aSu hba (by rw [stA_eq]; exact nut _ (by decide)), x5, mem_wr_ne' aF hba (nut _ (by decide))]
    rw [w34u.2.2 _ hba ?_]
    · exact tK3 t P.ht K (by omega) h8 (by omega)
    · rintro (⟨y, hy, K', -, h2, -, e⟩ | h)
      · rw [Set.mem_singleton_iff.1 hy] at e; exact nut K' (by omega) e.symm
      · exact absurd h (Set.notMem_empty _)
  refine ⟨K8, w08, htw, ?_⟩
  -- reads
  have hact0 : L.actionW X0 = sched.ACTION_RESUME_CURRENT := by
    obtain ⟨i, hi, hc⟩ := C.act
    rw [eq_of_spec_fd (sched.action.spec (L := L) X0)] at hi
    rw [ok_inj_ff hi]; exact UScalar.eq_of_val_eq (by simpa using hc)
  have hact6 : L.actionW X6 = sched.ACTION_RESUME_CURRENT := by
    unfold LawfulStore.actionW; rw [c6, nodeAt_of_ksb k6, w06.mem_eq aA (fun h => h.2 rfl)]
    exact hact0
  have eN6 : ∀ o, L.nodeAt X6 (L.cpu X6) o = L.nodeAt X0 (L.cpu X0) o := fun o => by rw [c6, nodeAt_of_ksb k6]
  have eN8 : ∀ o, L.nodeAt X8 (L.cpu X8) o = L.nodeAt X0 (L.cpu X0) o := fun o => by rw [K8.cpu, nodeAt_of_ksb K8.ksb]
  have hcur0 : L.mem X0 (L.nodeAt X0 (L.cpu X0) layout.node.CUR_THREAD) = t := P.hcur
  have hcur6 : L.curW X6 = t := by
    unfold LawfulStore.curW; rw [eN6, K6.node _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
      (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])]; exact hcur0
  have hcur8 : L.mem X8 (L.nodeAt X8 (L.cpu X8) layout.node.CUR_THREAD) = t := by
    rw [eN8, K8.node _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
      (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])]; exact hcur0
  have hsc2 : obj.Tcb.sc st u X2 = ok usc := by
    rw [tcb_sc_ok, show scA u = core.num.U64.wrapping_add u 3464#u64 from rfl,
      K2.tw P.hu 3464#u64 (by decide)]; exact congrArg ok P.husc
  have esc6 : L.mem X6 (scA u) = usc := by
    rw [show scA u = core.num.U64.wrapping_add u 3464#u64 from rfl, K6.tw P.hu 3464#u64 (by decide)]; exact P.husc
  -- `u`'s ring from `X3` to `X6`
  have scK36 : ∀ b, Aligned b → InSC usc (Z usc) b → L.mem X6 b = L.mem X3 b := by
    intro b hb hin
    have hbΩ := scΩ b hb hin
    rw [x6, mem_wr_ne' aSu hb (Ne.symm (by rw [stA_eq]; exact P.omg_tcb hbΩ P.hu (by decide))), x5,
      mem_wr_ne' aF hb (Ne.symm (P.omg_tcb hbΩ P.hu (by decide)))]
    refine w34.2.2 b hb ?_
    rintro (⟨y, hy, K, -, h2, -, rfl⟩ | h)
    · exact P.omg_tcb hbΩ hy (by omega) rfl
    · exact absurd h (Set.notMem_empty _)
  have eh6 := head_agree hW3 scK36
  have ect6 : L.curTime X6 = L.curTime X0 := by
    unfold LawfulStore.curTime LawfulStore.nodeA
    rw [eN6]; exact K6.node _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
      (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
  have HF := here_facts (L := L) (by obtain ⟨b, hb, hbt⟩ := C.here; subst hbt; exact hb)
  have hrdy6 : sporadic.ready st X6 usc = ok true := sporadic.ready_of (by rw [eh6, ect6]; exact ht3)
  have hsuf6 : sporadic.sufficient st ar X6 a usc 0#u64 = ok true := by
    obtain ⟨b, hb, hbt⟩ := C.suf; subst hbt
    exact sporadic.sufficient_mono hb (by rw [eh6]; exact ha3)
  -- possible_switch_to
  have einq : L.mem X6 (inqA u) = L.mem X0 (inqA u) := K6.tw P.hu 3592#u64 (by decide)
  have edom : L.mem X6 (domA u) = L.mem X0 (domA u) := K6.tw P.hu 3432#u64 (by decide)
  have eaff : L.mem X6 (affA u) = L.mem X0 (affA u) := K6.tw P.hu 3520#u64 (by decide)
  have eks : L.mem X6 (core.num.U64.wrapping_add (L.ksb X6) layout.ks.CUR_DOMAIN) =
      L.mem X0 (core.num.U64.wrapping_add (L.ksb X0) layout.ks.CUR_DOMAIN) := by
    rw [k6]
    obtain ⟨h1, h2, h3⟩ := P.ks (o := layout.ks.CUR_DOMAIN) (by simp [layout.ks.CUR_DOMAIN])
      (by simp [layout.ks.CUR_DOMAIN])
    exact K6.omg _ h1 h2 h3
  have hpst : sched.possible_switch_to st X6 u = ok X7 := by
    unfold sched.possible_switch_to
    rw [tcb_sc_ok, esc6]; simp only [bind_ok, if_neg P.hsc0]
    rw [inrel_ok, einq, HF.nr]; simp only [bind_ok, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
      ↓reduceIte]
    rw [cur_domain_ok, eks, HF.dom, dom_ok, edom]; simp only [bind_ok, bne_self_eq_false, Bool.false_eq_true,
      ↓reduceIte]
    rw [aff_ok, eaff, HF.aff, L.cur_cpu_eq, c6]; simp only [bind_ok, bne_self_eq_false, Bool.false_eq_true,
      ↓reduceIte]
    rw [eq_of_spec_fd (sched.action.spec (L := L) X6), hact6]
    simp only [bind_ok, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    exact e7
  -- `t`'s state at `X7`
  have hst7 : L.mem X7 (stA t) = sched.TS_RESTART := by
    rw [x7, mem_wr_ne' aA aSt (Ne.symm (by rw [stA_eq]; exact tnA t P.ht _ (by decide))), x6,
      mem_wr_ne' aSu aSt (by rw [stA_eq, stA_eq]; exact tcbw_ne hu' ht' (by decide) (by decide) (Or.inl P.hut)),
      x5, mem_wr_ne' aF aSt (by rw [stA_eq]; exact tcbw_ne hu' ht' (by decide) (by decide) (Or.inl P.hut))]
    rw [w34.2.2 _ aSt ?_, w23.2.2 _ aSt ?_, w12.2.2 _ aSt ?_, w1, LawfulStore.mem_wr_same aSt]
    · rintro (h | h | h)
      · exact P.omg_tcb (P.hSg.sub _ (P.rpS _ h)) P.ht (by decide) (stA_eq t)
      · exact P.omg_tcb hrΩ P.ht (by decide) (h.symm.trans (stA_eq t))
      · rw [stA_eq, stA_eq] at h; exact tcbw_ne ht' hu' (by decide) (by decide) (Or.inl (Ne.symm P.hut)) h
    · rintro (h | h)
      · exact P.omg_tcb (scΩ _ aSt h.inSC) P.ht (by decide) (stA_eq t)
      · rw [stA_eq] at h; exact P.tcb_node P.ht (by decide) (by simp [layout.node.REPROGRAM]) h
    · rintro (⟨y, hy, K, -, h2, -, e⟩ | h)
      · rw [stA_eq] at e; exact tcbw_ne ht' (hT y hy) (by decide) (by omega) (Or.inr (by simp; omega)) e
      · exact absurd h (Set.notMem_empty _)
  have hact8 : L.actionW X8 = u := by
    unfold LawfulStore.actionW; rw [eN8, x8, mem_wr_ne' aSt aA (by rw [stA_eq]; exact tnA t P.ht _ (by decide)), x7,
      LawfulStore.mem_wr_same aA]
  have hu0 : u ≠ sched.ACTION_RESUME_CURRENT := by
    intro e; have := congrArg UScalar.val e; simp at this; exact hu'.ne0 this
  -- the reply's TCB word
  have nRt : rTcbA rptr ≠ stA t := by rw [stA_eq]; exact P.omg_tcb hrΩ P.ht (by decide)
  have nRu : rTcbA rptr ≠ stA u := by rw [stA_eq]; exact P.omg_tcb hrΩ P.hu (by decide)
  have hrt8 : L.mem X8 (rTcbA rptr) = 0#u64 := by
    rw [x8, mem_wr_ne' aSt aR (Ne.symm nRt), x7, mem_wr_ne' aA aR (Ne.symm (oA _ hrΩ)), x6,
      mem_wr_ne' aSu aR (Ne.symm nRu), x5, mem_wr_ne' aF aR (Ne.symm (P.omg_tcb hrΩ P.hu (by decide)))]
    rw [w34.2.2 _ aR ?_, w23.2.2 _ aR ?_]
    · exact hr2
    · rintro (h | h)
      · exact P.rp_notSC (Or.inr rfl) h.inSC
      · exact P.omg_node hrΩ (by simp [layout.node.REPROGRAM]) h
    · rintro (⟨y, hy, K, -, h2, -, e⟩ | h)
      · exact P.omg_tcb hrΩ hy (by omega) e
      · exact absurd h (Set.notMem_empty _)
  -- queue-object words at `X8`
  have epK : ∀ e, EpPlaced T e → EpOutNodes st Cs X0 e → (∀ a ∈ Ω, a.val + 8 ≤ e.val ∨ e.val + 16 ≤ a.val) →
      L.epState X8 e = L.epState X0 e := by
    intro e hE hEN hEΩ
    have vt := epTSA_val hE
    have ea := hE.align
    unfold LawfulStore.epState
    rw [w08.mem_eq (by show _ % 8 = 0; rw [vt]; omega) (rrw_ep P hE hEN hEΩ (Or.inr vt))]
  have hep8 : obj.Ep.state st ep X8 = ok obj.EP_IDLE := by
    rw [eq_of_spec_fd (obj.Ep.state.spec (L := L) X8 ep), epK ep P.hE P.hEN P.hEΩ]
    obtain ⟨i, hi, hc⟩ := C.ep
    rw [eq_of_spec_fd (obj.Ep.state.spec (L := L) X0 ep)] at hi
    rw [ok_inj_ff hi]; exact congrArg ok (UScalar.eq_of_val_eq (by simpa using hc))
  -- the bound notification
  have ebd : L.mem X8 (boundA t) = L.mem X0 (boundA t) :=
    K8.tcb t P.ht 3368#u64 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  have esct : L.mem X8 (scA t) = L.mem X0 (scA t) := K8.tw P.ht 3464#u64 (by decide)
  have hntfn : ∃ n, obj.Tcb.bound_ntfn st t X8 = ok n ∧
      (n = 0#u64 ∨ (n ≠ 0#u64 ∧ ∃ i7, obj.Ntfn.state st n X8 = ok i7 ∧ ¬ i7 = obj.NTFN_ACTIVE ∧
        notification.maybe_return_sched_context st X8 n t = ok X8)) := by
    refine ⟨L.mem X0 (boundA t), by rw [eq_of_spec_fd (obj.Tcb.bound_ntfn.val (L := L) X8 t), ebd], ?_⟩
    rcases C.ntfn with ⟨i, hi, hc⟩ | ⟨i, hi, hc, i7, h7, hn7, i8, h8, hsc⟩
    · rw [eq_of_spec_fd (obj.Tcb.bound_ntfn.val (L := L) X0 t)] at hi
      left; rw [ok_inj_ff hi]; exact UScalar.eq_of_val_eq (by simpa using hc)
    · rw [eq_of_spec_fd (obj.Tcb.bound_ntfn.val (L := L) X0 t)] at hi
      have ei := ok_inj_ff hi; subst ei
      have h0 : L.mem X0 (boundA t) ≠ 0#u64 := by simpa using hc
      obtain ⟨hnN, hnE, hnEN, hnΩ⟩ := P.hNt h0
      right; refine ⟨h0, i7, ?_, hn7, ?_⟩
      · rw [eq_of_spec_fd (obj.Ntfn.state.spec (L := L) X8 _), epK _ hnE hnEN hnΩ]
        rw [eq_of_spec_fd (obj.Ntfn.state.spec (L := L) X0 _)] at h7; exact h7
      · -- the notification's SC word
        have hnS := P.hO.ntW _ hnN
        have eNs : L.mem X8 (ntfnScA (L.mem X0 (boundA t))) = L.mem X0 (ntfnScA (L.mem X0 (boundA t))) := by
          refine K8.omg _ ⟨P.hSg.sub _ hnS, ?_⟩ ?_ ?_
          · rintro ⟨r', hr', e | e⟩
            · have := P.hO.ntRp _ hnN r' hr'; rw [e, rPrevA_val (P.hO.rp r' hr')] at this; omega
            · have := P.hO.ntRp _ hnN r' hr'; rw [e, rNextA_val (P.hO.rp r' hr')] at this; omega
          · intro e; have := P.hO.ntRp _ hnN rptr P.hrR; rw [e, rTcbA_val0] at this; omega
          · intro hin; have := P.hO.ntSc _ hnN usc P.hcS; unfold InRing at hin; omega
        rw [eq_of_spec_fd (obj.Ntfn.sc.val (L := L) X0 _)] at h8
        have e8 := ok_inj_ff h8
        unfold notification.maybe_return_sched_context
        rw [eq_of_spec_fd (obj.Ntfn.sc.val (L := L) X8 _), eNs, e8]; simp only [bind_ok]
        rw [eq_of_spec_fd (obj.Sc.is_null.spec _)]; simp only [bind_ok]
        rcases hsc with h0' | ⟨h0', i9, h9, hne⟩
        · have : i8 = 0#u64 := UScalar.eq_of_val_eq (by simpa using h0')
          subst this; simp
        · have : i8 ≠ 0#u64 := fun e => by subst e; simp at h0'
          simp only [this, decide_false, Bool.false_eq_true, ↓reduceIte]
          rw [tcb_sc_ok, esct]; simp only [bind_ok]
          rw [tcb_sc_ok] at h9; rw [ok_inj_ff h9, if_neg hne]
  exact ⟨hsc2, schedule_tcb_ne (by rw [hcur6]; exact Ne.symm P.hut), by rw [tcb_sc_ok, esc6], hrdy6, hsuf6, hpst,
    by rw [eq_of_spec_fd (obj.Tcb.state.spec (L := L) X7 t), hst7], hact8, by rw [hact8]; exact hu0,
    by rw [eq_of_spec_fd (sched.cur_thread.spec (L := L) X8), hcur8],
    by rw [eq_of_spec_fd (obj.Reply.tcb.blk (L := L) X8 rptr), hrt8], hntfn, hep8⟩

/-- `rr_x8G` at an UnknownSyscall fault (pf1). -/
theorem rr_x8 {X0 X1 X2 X3 X4 X5 X6 X7 X8 : S} {a a1 a2 : A} {t rptr ep u usc : U64} {b9 restart : Bool}
    (P : RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z X0 t rptr ep u usc) (C : RRChecks st ar X0 a t rptr ep u usc)
    (hsum : L.mem X0 (sporA usc) ≠ 0#u64 → L.amtSum X0 usc < 2 ^ 64)
    (e1 : obj.Tcb.set_state st t X0 sched.TS_RESTART = ok X1)
    (e2 : ipc.reply_remove st ar X1 a rptr u = ok (X2, a1))
    (e3s : sporadic.sc_sporadic st X2 usc = ok b9)
    (e3 : (if b9 then do
      let i13 ← obj.Sc.cpu st usc X2
      let i14 ← obj.node_get st X2 i13 layout.node.CUR_SC
      if usc != i14 then sporadic.unblock_check st X2 usc else ok X2
    else ok X2) = ok X3)
    (e4 : faults.handle_fault_reply st ar X3 a1 u t = ok (restart, X4, a2))
    (e5 : faults.clear_fault st X4 u = ok X5)
    (e6 : obj.Tcb.set_state st u X5 sched.TS_RESTART = ok X6)
    (e7 : sched.set_action st X6 u = ok X7)
    (e8 : obj.Tcb.set_state st t X7 sched.TS_RUNNING = ok X8) :
    RRR3 (st := st) X3 t u ∧ a2 = a ∧ FinKeep (L := L) T (RΩ Ω Rp) X0 X8 rptr usc (Z usc) ∧
    WritesIn st X0 X8 (RRW (L := L) T Rp X0 t u rptr usc (Z usc)) ∧
    (∀ K : U64, K.val < 3328 → K.val % 8 = 0 →
      L.mem X8 (core.num.U64.wrapping_add t K) = L.mem X0 (core.num.U64.wrapping_add t K)) ∧
    obj.Tcb.sc st u X2 = ok usc ∧ sched.schedule_tcb st X6 u = ok X6 ∧ obj.Tcb.sc st u X6 = ok usc ∧
    sporadic.ready st X6 usc = ok true ∧ sporadic.sufficient st ar X6 a2 usc 0#u64 = ok true ∧
    sched.possible_switch_to st X6 u = ok X7 ∧ obj.Tcb.state st t X7 = ok sched.TS_RESTART ∧
    L.actionW X8 = u ∧ L.actionW X8 ≠ sched.ACTION_RESUME_CURRENT ∧ sched.cur_thread st X8 = ok t ∧
    obj.Reply.tcb st rptr X8 = ok 0#u64 ∧
    (∃ n, obj.Tcb.bound_ntfn st t X8 = ok n ∧
      (n = 0#u64 ∨ (n ≠ 0#u64 ∧ ∃ i7, obj.Ntfn.state st n X8 = ok i7 ∧ ¬ i7 = obj.NTFN_ACTIVE ∧
        notification.maybe_return_sched_context st X8 n t = ok X8))) ∧
    obj.Ep.state st ep X8 = ok obj.EP_IDLE := by
  apply rr_x8G (ty := fl4_abi.consts.fault.UnknownSyscall) <;> assumption


end x8


/-! ## From `X8` to `X15`: the receive's explicit writes -/

section x15
variable {S : Type _} {A : Type _} {st : machine.Store S} (ar : machine.Arch A) [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}

set_option maxHeartbeats 3200000 in
/-- **The reads at `X11`, `X12`, `X15`** from `FinKeep` at `X8` and the
receive's writes (`t`'s state / block / reply / Ep-link words, the reply's
`TCB` word, the endpoint's two words): `act11`, `q12`, `T15` / `R15` (the
entry's `NoDue`, `here_facts`), `act15`, `ct15`, `hp15` (the bitmap kept,
`le_of_is_hp` / `is_hp_of_le`), `dq15` (`u` not queued). -/
theorem rr_x15G {ty : U64} [HfrRestart st ar ty] {X0 X8 X9 X10 X11 X12 X13 X14 X15 : S} {a : A} {t rptr ep u usc : U64}
    (P : RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z X0 t rptr ep u usc) (C : RRChecksG st ar ty X0 a t rptr ep u usc)
    (K8 : FinKeep (L := L) T (RΩ Ω Rp) X0 X8 rptr usc (Z usc))
    (w08 : WritesIn st X0 X8 (RRW (L := L) T Rp X0 t u rptr usc (Z usc)))
    (hact8 : L.actionW X8 = u)
    (e9 : obj.Tcb.set_state st t X8 sched.TS_BLOCKED_ON_RECV = ok X9)
    (e10 : obj.Tcb.set_block_obj st t X9 ep = ok X10)
    (e11 : obj.Tcb.set_reply_obj st t X10 rptr = ok X11)
    (e12 : obj.Reply.set_tcb st rptr X11 t = ok X12)
    (e13 : obj.Tcb.set_ep_next st t X12 0#u64 = ok X13)
    (e14 : obj.Tcb.set_ep_prev st t X13 0#u64 = ok X14)
    (e15 : obj.Ep.set_queue st ep X14 t t obj.EP_RECV = ok X15) :
    L.actionW X11 ≠ sched.ACTION_RESUME_CURRENT ∧
    (∃ q, endpoint.get_queue st X12 ep = ok q ∧ q.head = 0#u64) ∧
    NoDue (L := L) X15 ∧ sched.action st X15 = ok u ∧ sched.cur_thread st X15 = ok t ∧
    (∃ t1 b7 ff, sched.idle_thread st X15 = ok t1 ∧ obj.Tcb.Insts.CoreCmpPartialEqTcb.eq t t1 = ok b7 ∧
      (if b7 then ok true else do
        let i11 ← obj.Tcb.prio st u X15
        let i12 ← obj.Tcb.prio st t X15
        if i11 < i12 then ok true else ok false) = ok ff ∧
      (¬ ff = true ∨ (ff = true ∧ ∃ i11 i12 b8, sched.cur_domain st X15 = ok i11 ∧ obj.Tcb.prio st u X15 = ok i12 ∧
        sched.is_highest_prio st X15 i11 i12 = ok b8 ∧ b8 = true))) ∧
    sched.dequeue st X15 u = ok X15 := by
  have hT := P.hT
  have ht' := hT t P.ht
  have hu' := hT u P.hu
  have aSt := P.aS P.ht
  have hrΩ := P.hSg.sub _ P.rtS
  have aR : Aligned (rTcbA rptr) := (P.hΩ _ hrΩ).1
  have ta := ht'.align; have tf := ht'.fits
  -- the writes
  have w9 : X9 = L.wr X8 (stA t) sched.TS_BLOCKED_ON_RECV := by
    have := obj.Tcb.set_state.spec (L := L) X8 t sched.TS_BLOCKED_ON_RECV; rw [e9, WP.spec_ok] at this; exact this
  have w10 : X10 = L.wr X9 (blockA t) ep := by
    have := obj.Tcb.set_block_obj.wr (L := L) X9 t ep; rw [e10, WP.spec_ok] at this; exact this
  have w11 : X11 = L.wr X10 (replyA t) rptr := by
    have := obj.Tcb.set_reply_obj.wr (L := L) X10 t rptr; rw [e11, WP.spec_ok] at this; exact this
  have w12 : X12 = L.wr X11 (rTcbA rptr) t := by
    have := obj.Reply.set_tcb.spec (L := L) X11 rptr t; rw [e12, WP.spec_ok] at this; exact this
  have w13 : X13 = L.wr X12 (nextA .Ep t) 0#u64 := by
    rw [obj.Tcb.set_ep_next.ok] at e13; exact (ok_inj_ff e13).symm
  have w14 : X14 = L.wr X13 (prevA .Ep t) 0#u64 := by
    rw [obj.Tcb.set_ep_prev.ok] at e14; exact (ok_inj_ff e14).symm
  have w15 : X15 = epW (L := L) X14 ep t t obj.EP_RECV := by
    rw [obj.Ep.set_queue.ok] at e15; exact (ok_inj_ff e15).symm
  have vB : (blockA t).val = t.val + 3336 := tcbw_val hT P.ht (by decide)
  have vRp : (replyA t).val = t.val + 3360 := tcbw_val hT P.ht (by decide)
  have vN : (nextA .Ep t).val = t.val + 3496 := by rw [nextA_val ht']; rfl
  have vP : (prevA .Ep t).val = t.val + 3504 := by rw [prevA_val ht']; rfl
  have vS := P.vS P.ht
  have vH : (epHeadA ep).val = ep.val := epHeadA_val
  have vTS : (epTSA ep).val = ep.val + 8 := epTSA_val P.hE
  have ea := P.hE.align
  have aB : Aligned (blockA t) := by show _ % 8 = 0; omega
  have aRp : Aligned (replyA t) := by show _ % 8 = 0; omega
  have aN : Aligned (nextA .Ep t) := by show _ % 8 = 0; omega
  have aP : Aligned (prevA .Ep t) := by show _ % 8 = 0; omega
  have aH : Aligned (epHeadA ep) := by show _ % 8 = 0; omega
  have aTS : Aligned (epTSA ep) := by show _ % 8 = 0; omega
  have m11 : ∀ b, Aligned b → (b.val < t.val + 3328 ∨ t.val + 3328 < b.val) → b.val ≠ t.val + 3336 →
      b.val ≠ t.val + 3360 → L.mem X11 b = L.mem X8 b := by
    intro b hb h1 h2 h3
    rw [w11, mem_wr_ne' aRp hb (fun e => h3 (by rw [← e, vRp])), w10, mem_wr_ne' aB hb (fun e => h2 (by rw [← e, vB])),
      w9, mem_wr_ne' aSt hb (fun e => by rw [← e, vS] at h1; omega)]
  have m12 : ∀ b, Aligned b → (b.val < t.val + 3328 ∨ t.val + 3328 < b.val) → b.val ≠ t.val + 3336 →
      b.val ≠ t.val + 3360 → b ≠ rTcbA rptr → L.mem X12 b = L.mem X8 b := by
    intro b hb h1 h2 h3 h4
    rw [w12, mem_wr_ne' aR hb (Ne.symm h4)]; exact m11 b hb h1 h2 h3
  have m15 : ∀ b, Aligned b → (b.val < t.val + 3328 ∨ t.val + 3328 < b.val) → b.val ≠ t.val + 3336 →
      b.val ≠ t.val + 3360 → b ≠ rTcbA rptr → b.val ≠ t.val + 3496 → b.val ≠ t.val + 3504 →
      (b.val + 8 ≤ ep.val ∨ ep.val + 16 ≤ b.val) → L.mem X15 b = L.mem X8 b := by
    intro b hb h1 h2 h3 h4 h5 h6 h7
    rw [w15]; unfold epW
    rw [mem_wr_ne' aTS hb (fun e => by rw [← e, vTS] at h7; omega), mem_wr_ne' aH hb (fun e => by rw [← e, vH] at h7; omega),
      w14, mem_wr_ne' aP hb (fun e => h6 (by rw [← e, vP])), w13, mem_wr_ne' aN hb (fun e => h5 (by rw [← e, vN]))]
    exact m12 b hb h1 h2 h3 h4
  have k15 : L.ksb X15 = L.ksb X8 := by
    rw [w15]; unfold epW; simp only [L.ksb_wr]; rw [w14, w13, w12, w11, w10, w9]; simp only [L.ksb_wr]
  have c15 : L.cpu X15 = L.cpu X8 := by
    rw [w15]; unfold epW; simp only [L.cpu_wr]; rw [w14, w13, w12, w11, w10, w9]; simp only [L.cpu_wr]
  have k11 : L.ksb X11 = L.ksb X8 := by rw [w11, w10, w9]; simp only [L.ksb_wr]
  have c11 : L.cpu X11 = L.cpu X8 := by rw [w11, w10, w9]; simp only [L.cpu_wr]
  have k12 : L.ksb X12 = L.ksb X8 := by rw [w12, L.ksb_wr, k11]
  have c12 : L.cpu X12 = L.cpu X8 := by rw [w12, L.cpu_wr, c11]
  -- word classes
  have nodeC : ∀ off : U64, off.val < 4288 → off.val % 8 = 0 →
      L.mem X15 (L.nodeAt X0 (L.cpu X0) off) = L.mem X8 (L.nodeAt X0 (L.cpu X0) off) ∧
      L.mem X11 (L.nodeAt X0 (L.cpu X0) off) = L.mem X8 (L.nodeAt X0 (L.cpu X0) off) := by
    intro off ho h8
    have vb := nodeAt_val P.hN ho
    have hba := nodeAt_aligned P.hN ho h8
    have nd := P.hN.disj t P.ht
    have hn := P.hEN.1 _ P.hcC
    have nR : L.nodeAt X0 (L.cpu X0) off ≠ rTcbA rptr := fun e => P.omg_node hrΩ ho e.symm
    exact ⟨m15 _ hba (by rw [vb]; omega) (by rw [vb]; omega) (by rw [vb]; omega) nR (by rw [vb]; omega)
      (by rw [vb]; omega) (by rw [vb]; omega),
      m11 _ hba (by rw [vb]; omega) (by rw [vb]; omega) (by rw [vb]; omega)⟩
  have tcbC : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → 3328 < K.val → K.val ≠ 3336 → K.val ≠ 3360 →
      K.val ≠ 3496 → K.val ≠ 3504 →
      L.mem X15 (core.num.U64.wrapping_add y K) = L.mem X8 (core.num.U64.wrapping_add y K) := by
    intro y hy K hK h8 k1 k2 k3 k4 k5
    have hy' := hT y hy
    have vb := tcb_wadd_val hy' hK
    have ya := hy'.align
    have hba : Aligned (core.num.U64.wrapping_add y K) := by show _ % 8 = 0; rw [vb]; omega
    have ed := P.hE.disj y hy
    have nR : core.num.U64.wrapping_add y K ≠ rTcbA rptr := fun e => P.omg_tcb hrΩ hy hK e.symm
    refine m15 _ hba ?_ ?_ ?_ nR ?_ ?_ (by rw [vb]; omega) <;> rw [vb] <;>
      rcases Nat.lt_or_ge y.val t.val with h | h <;> omega
  have omgC : ∀ b ∈ Ω, b ≠ rTcbA rptr → L.mem X15 b = L.mem X8 b := by
    intro b hb hr
    have oT := (P.hΩ b hb).2.1 t P.ht
    exact m15 b (P.hΩ b hb).1 (by omega) (by omega) (by omega) hr (by omega) (by omega) (P.hEΩ b hb)
  have eN15 : ∀ o, L.nodeAt X15 (L.cpu X15) o = L.nodeAt X0 (L.cpu X0) o := fun o => by
    rw [c15, K8.cpu, nodeAt_of_ksb (k15.trans K8.ksb)]
  have eN11 : ∀ o, L.nodeAt X11 (L.cpu X11) o = L.nodeAt X0 (L.cpu X0) o := fun o => by
    rw [c11, K8.cpu, nodeAt_of_ksb (k11.trans K8.ksb)]
  have eN8 : ∀ o, L.nodeAt X8 (L.cpu X8) o = L.nodeAt X0 (L.cpu X0) o := fun o => by
    rw [K8.cpu, nodeAt_of_ksb K8.ksb]
  have nK : ∀ off : U64, off.val < 4288 → off.val % 8 = 0 → off.val ≠ 16 → off.val ≠ 56 →
      L.mem X15 (L.nodeAt X0 (L.cpu X0) off) = L.mem X0 (L.nodeAt X0 (L.cpu X0) off) := fun off h1 h2 h3 h4 => by
    rw [(nodeC off h1 h2).1]; exact K8.node off h1 h2 h3 h4
  have hu0 : u ≠ sched.ACTION_RESUME_CURRENT := by
    intro e; have := congrArg UScalar.val e; simp at this; exact hu'.ne0 this
  have hact15 : L.actionW X15 = u := by
    unfold LawfulStore.actionW at hact8 ⊢
    rw [eN15, (nodeC _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])).1, ← eN8 _]
    exact hact8
  have hact11 : L.actionW X11 = u := by
    unfold LawfulStore.actionW at hact8 ⊢
    rw [eN11, (nodeC _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])).2, ← eN8 _]
    exact hact8
  have hcur15 : L.mem X15 (L.nodeAt X15 (L.cpu X15) layout.node.CUR_THREAD) = t := by
    rw [eN15, nK _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
      (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])]; exact P.hcur
  -- q12
  have hq12 : ∃ q, endpoint.get_queue st X12 ep = ok q ∧ q.head = 0#u64 := by
    refine ⟨_, eq_of_spec_fd (endpoint.get_queue.spec (L := L) X12 ep), ?_⟩
    show L.mem X12 (epHeadA ep) = 0#u64
    have ed := P.hE.disj t P.ht
    rw [m12 _ aH (by rw [vH]; omega) (by rw [vH]; omega) (by rw [vH]; omega)
      (fun e => by have := P.hEΩ _ hrΩ; rw [← e, vH] at this; omega),
      w08.mem_eq aH (rrw_ep P P.hE P.hEN P.hEΩ (Or.inl vH))]
    exact P.hq0
  -- NoDue
  have HF := here_facts (L := L) (by obtain ⟨b, hb, hbt⟩ := C.here; subst hbt; exact hb)
  have hND : NoDue (L := L) X15 := by
    refine NoDue.agree HF.nd (k15.trans K8.ksb) (c15.trans K8.cpu)
      (nK _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
        (by simp [layout.node.TIMER_MIN]))
      (nK _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
        (by simp [layout.node.CUR_TIME])) ?_
      (nK _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
        (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])) ?_ ?_ ?_
    · intro h0
      rcases P.hTM with h | h
      · exact absurd h h0
      · rw [show tdA (L.mem X0 (L.nodeAt X0 (L.cpu X0) layout.node.TIMER_MIN)) = core.num.U64.wrapping_add _ 3528#u64
          from rfl, tcbC _ h 3528#u64 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)]
        exact K8.tw h 3528#u64 (by decide)
    · intro h0
      have h := (P.hRel h0).1
      rw [show scA (L.mem X0 (L.nodeAt X0 (L.cpu X0) layout.node.RELEASE_HEAD)) = core.num.U64.wrapping_add _ 3464#u64
          from rfl, tcbC _ h 3464#u64 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)]
      exact K8.tw h 3464#u64 (by decide)
    · intro h0
      obtain ⟨-, zc, hW, hin⟩ := P.hRel h0
      obtain ⟨h8, -, -⟩ := hW.bounds
      obtain ⟨h96, -, -, hh, -, -⟩ := hW.inside
      have hb : Aligned (headA (L.mem X0 (scA (L.mem X0 (L.nodeAt X0 (L.cpu X0) layout.node.RELEASE_HEAD))))) := by
        show _ % 8 = 0; rw [hh]; omega
      obtain ⟨a1, a2, a3⟩ := hin _ hb ⟨by rw [hh]; omega, by rw [hh]; omega⟩
      rw [omgC _ a1.1 a2]; exact K8.omg _ a1 a2 a3
    · intro h0
      obtain ⟨-, zc, hW, hin⟩ := P.hRel h0
      obtain ⟨h8, -, -⟩ := hW.bounds
      obtain ⟨-, -, -, -, -, hi⟩ := hW.inside
      obtain ⟨e1, e2, e3⟩ := hi _ hW.head_lt
      have hb : Aligned (rtA (L.mem X0 (scA (L.mem X0 (L.nodeAt X0 (L.cpu X0) layout.node.RELEASE_HEAD))))
          (L.rhead X0 (L.mem X0 (scA (L.mem X0 (L.nodeAt X0 (L.cpu X0) layout.node.RELEASE_HEAD)))))) := by
        show _ % 8 = 0; rw [e1]; omega
      obtain ⟨a1, a2, a3⟩ := hin _ hb ⟨by rw [e1]; omega, by rw [e1]; omega⟩
      rw [omgC _ a1.1 a2]; exact K8.omg _ a1 a2 a3
  -- hp15
  have epr : ∀ y ∈ T, obj.Tcb.prio st y X15 = obj.Tcb.prio st y X0 := fun y hy => by
    rw [eq_of_spec_fd (obj.Tcb.prio.spec (L := L) X15 y), eq_of_spec_fd (obj.Tcb.prio.spec (L := L) X0 y),
      show prioA y = core.num.U64.wrapping_add y 3448#u64 from rfl,
      tcbC y hy 3448#u64 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      K8.tw hy 3448#u64 (by decide)]
  have eidle : sched.idle_thread st X15 = sched.idle_thread st X0 := by
    rw [eq_of_spec_fd (sched.idle_thread.spec' (L := L) X15), eq_of_spec_fd (sched.idle_thread.spec' (L := L) X0),
      eN15, nK _ (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD])
        (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD])]
  have ecd : sched.cur_domain st X15 = sched.cur_domain st X0 := by
    rw [cur_domain_ok, cur_domain_ok, k15, K8.ksb]
    obtain ⟨h1, h2, h3⟩ := P.ks (o := layout.ks.CUR_DOMAIN) (by simp [layout.ks.CUR_DOMAIN])
      (by simp [layout.ks.CUR_DOMAIN])
    rw [omgC _ h1.1 h2, K8.omg _ h1 h2 h3]
  have hhp : ∀ d p, sched.is_highest_prio st X0 d p = ok true → sched.is_highest_prio st X15 d p = ok true := by
    intro d p h
    obtain ⟨NE, hB⟩ := P.hBM
    have hle := le_of_is_hp P.hN hB h
    have hN15 : NodePlaced st T X15 (L.cpu X15) := by rw [c15, K8.cpu]; exact P.hN.ksb (k15.trans K8.ksb)
    refine is_hp_of_le d hN15 (BitmapOK.agree (s := X0) ?_ ?_ ?_) hle
    · first | (rw [c15, K8.cpu]; exact hB) | rw [c15, K8.cpu]
    · unfold LawfulStore.l1W; rw [c15, K8.cpu, nodeAt_of_ksb (k15.trans K8.ksb)]
      exact nK _ (by rw [l1Off_val] <;> omega) (by rw [l1Off_val] <;> omega) (by rw [l1Off_val] <;> omega)
        (by rw [l1Off_val] <;> omega)
    · intro g hg
      unfold LawfulStore.l2W; rw [c15, K8.cpu, nodeAt_of_ksb (k15.trans K8.ksb)]
      exact nK _ (by rw [l2Off_val hg] <;> omega) (by rw [l2Off_val hg] <;> omega) (by rw [l2Off_val hg] <;> omega)
        (by rw [l2Off_val hg] <;> omega)
  have hhp15 : ∃ t1 b7 ff, sched.idle_thread st X15 = ok t1 ∧ obj.Tcb.Insts.CoreCmpPartialEqTcb.eq t t1 = ok b7 ∧
      (if b7 then ok true else do
        let i11 ← obj.Tcb.prio st u X15
        let i12 ← obj.Tcb.prio st t X15
        if i11 < i12 then ok true else ok false) = ok ff ∧
      (¬ ff = true ∨ (ff = true ∧ ∃ i11 i12 b8, sched.cur_domain st X15 = ok i11 ∧ obj.Tcb.prio st u X15 = ok i12 ∧
        sched.is_highest_prio st X15 i11 i12 = ok b8 ∧ b8 = true)) := by
    obtain ⟨t1, b7, ff, hi, he, hf, hr⟩ := C.hp
    refine ⟨t1, b7, ff, by rw [eidle]; exact hi, he, by rw [epr u P.hu, epr t P.ht]; exact hf, ?_⟩
    rcases hr with hr | ⟨hff, i11, i12, b8, h1, h2, h3, h4⟩
    · exact Or.inl hr
    · subst h4
      exact Or.inr ⟨hff, i11, i12, true, by rw [ecd]; exact h1, by rw [epr u P.hu]; exact h2, hhp _ _ h3, rfl⟩
  -- dq15
  have hdq : sched.dequeue st X15 u = ok X15 := by
    unfold sched.dequeue
    rw [queued_ok, show inqA u = core.num.U64.wrapping_add u 3592#u64 from rfl,
      tcbC u P.hu 3592#u64 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      K8.tw P.hu 3592#u64 (by decide), show core.num.U64.wrapping_add u 3592#u64 = inqA u from rfl, HF.nq]
    simp
  refine ⟨by rw [hact11]; exact hu0, hq12, hND, by rw [eq_of_spec_fd (sched.action.spec (L := L) X15), hact15],
    by rw [eq_of_spec_fd (sched.cur_thread.spec (L := L) X15), hcur15], hhp15, hdq⟩

/-- `rr_x15G` at an UnknownSyscall fault (pf1). -/
theorem rr_x15 {X0 X8 X9 X10 X11 X12 X13 X14 X15 : S} {a : A} {t rptr ep u usc : U64}
    (P : RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z X0 t rptr ep u usc) (C : RRChecks st ar X0 a t rptr ep u usc)
    (K8 : FinKeep (L := L) T (RΩ Ω Rp) X0 X8 rptr usc (Z usc))
    (w08 : WritesIn st X0 X8 (RRW (L := L) T Rp X0 t u rptr usc (Z usc)))
    (hact8 : L.actionW X8 = u)
    (e9 : obj.Tcb.set_state st t X8 sched.TS_BLOCKED_ON_RECV = ok X9)
    (e10 : obj.Tcb.set_block_obj st t X9 ep = ok X10)
    (e11 : obj.Tcb.set_reply_obj st t X10 rptr = ok X11)
    (e12 : obj.Reply.set_tcb st rptr X11 t = ok X12)
    (e13 : obj.Tcb.set_ep_next st t X12 0#u64 = ok X13)
    (e14 : obj.Tcb.set_ep_prev st t X13 0#u64 = ok X14)
    (e15 : obj.Ep.set_queue st ep X14 t t obj.EP_RECV = ok X15) :
    L.actionW X11 ≠ sched.ACTION_RESUME_CURRENT ∧
    (∃ q, endpoint.get_queue st X12 ep = ok q ∧ q.head = 0#u64) ∧
    NoDue (L := L) X15 ∧ sched.action st X15 = ok u ∧ sched.cur_thread st X15 = ok t ∧
    (∃ t1 b7 ff, sched.idle_thread st X15 = ok t1 ∧ obj.Tcb.Insts.CoreCmpPartialEqTcb.eq t t1 = ok b7 ∧
      (if b7 then ok true else do
        let i11 ← obj.Tcb.prio st u X15
        let i12 ← obj.Tcb.prio st t X15
        if i11 < i12 then ok true else ok false) = ok ff ∧
      (¬ ff = true ∨ (ff = true ∧ ∃ i11 i12 b8, sched.cur_domain st X15 = ok i11 ∧ obj.Tcb.prio st u X15 = ok i12 ∧
        sched.is_highest_prio st X15 i11 i12 = ok b8 ∧ b8 = true))) ∧
    sched.dequeue st X15 u = ok X15 := by
  apply rr_x15G (ty := fl4_abi.consts.fault.UnknownSyscall) <;> assumption


end x15


/-! ## `RRPl` from the P1 invariants at the dispatch state -/

section plof
variable {S : Type _} {A : Type _} {st : machine.Store S} (ar : machine.Arch A) [L : LawfulStore st]

set_option maxHeartbeats 1600000 in
/-- **`RRPl` at the dispatch state** from `BXI` / `XG` there, the receive-side
cap typing (`EntryHyps0.recvOK`, as `rrEnt_of`) and the notifications being
the heap's (`hNt`, the entry hypotheses' `∀ n ∈ Nt, H n = some .ntfn`). -/
theorem rrPl_lkG {ty : U64} [HfrRestart st ar ty] {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
    (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    {s : S} {a : A} {t rptr ep u usc : U64} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hlk : ∀ cptr, cspace.lookup_cap st s (L.curW s) cptr ⦃ r => ∀ c, r = .Ok c → CapTyped H Rp Nt c ⦄)
    (et : sched.cur_thread st s = ok t)
    (hrc : fastpath.reply_caps st s t = ok (some (rptr, ep))) (C : RRChecksG st ar ty s a t rptr ep u usc) :
    RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z s t rptr ep u usc := by
  have EE := rrEnt_lkG ar hI hlk et hrc C
  have et' : t = L.curW s := by
    rw [eq_of_spec_fd (sched.cur_thread.spec (L := L) s)] at et; exact (ok_inj_ff et).symm
  obtain ⟨⟨Q, R, hSQ⟩, hB, hX, hSg, hS⟩ := hI
  have hX0 := hX.2.2.toScExtra0
  obtain ⟨⟨sl, root, hsl, hroot, ⟨i, found, g, hi, hr, hc⟩, ⟨i1, found1, c0, c1, c3, c4, hi1, hr1, hc1⟩⟩⟩ :=
    reply_caps_some st hrc
  have hl1 := hlk i
  rw [← et', lookup_cap_of_found hsl hroot hr hc, WP.spec_ok] at hl1
  have hrR : rptr ∈ Rp := (hl1 _ rfl).2.2 rptr g rfl
  have htT : t ∈ T := EE.ht
  have huT : u ∈ T := EE.hu
  -- `u ≠ t`
  obtain ⟨b0, hsch0, hb0⟩ := C.sch
  subst hb0
  have hsp := sched.is_schedulable.spec' (L := L) s t
  rw [hsch0, WP.spec_ok] at hsp
  obtain ⟨hrun0, -, -, -⟩ := hsp rfl
  obtain ⟨iu, hiu, hiuc⟩ := C.ust
  have hiu' : iu = sched.TS_BLOCKED_ON_REPLY := UScalar.eq_of_val_eq (by simpa using hiuc)
  have hus0 : L.mem s (stA u) = sched.TS_BLOCKED_ON_REPLY := by
    rw [eq_of_spec_fd (obj.Tcb.state.spec (L := L) s u)] at hiu; rw [← hiu', ok_inj_ff hiu]
  have hut : u ≠ t := by
    rintro rfl; rw [hus0] at hrun0; exact bor_not_runnable hrun0
  -- `u`'s SC
  have husc : L.mem s (scA u) = usc := by
    have h0 := C.sc; rw [tcb_sc_ok] at h0; exact ok_inj_ff h0
  have hsc0 : usc ≠ 0#u64 := by
    obtain ⟨b, hb, hbn⟩ := C.sc0
    rw [eq_of_spec_fd (obj.Sc.is_null.spec _)] at hb; have e := ok_inj_ff hb; subst e; simpa using hbn
  have hsc0' : L.mem s (scA u) ≠ 0#u64 := by rw [husc]; exact hsc0
  have hcS : usc ∈ Scs := husc ▸ (hX0.bound u huT hsc0').1
  have hact : usc ∈ Ac := husc ▸ hB.sact u huT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hus0)))))) hsc0'
  have hWF : RefillsWF st s usc (Z usc) := (hS.all _ hcS).1 ((hS.act _ hcS).1 hact)
  -- the endpoint
  have hl3 := hlk i1
  rw [← et', lookup_cap_of_found hsl hroot hr1 hc1, WP.spec_ok] at hl3
  have hpH : H ep = some .ep := (hl3 _ rfl).1 ep c0 c1 true c3 c4 rfl
  obtain ⟨E, EQ, hW⟩ := hSQ.eps
  obtain ⟨w1, -, w3, w4, -, w6⟩ := hW
  have hpE : ep ∈ E := (w6.2.2.1 ep).2 (Or.inl hpH)
  obtain ⟨hEP, hEN, hQ⟩ := w1 ep hpE
  have hst : L.epState s ep = 0#u64 := by
    obtain ⟨i, hi, hc⟩ := C.ep
    rw [eq_of_spec_fd (obj.Ep.state.spec (L := L) s ep)] at hi
    rw [ok_inj_ff hi]; exact UScalar.eq_of_val_eq (by simpa using hc)
  have hq0 : L.mem s (epHeadA ep) = 0#u64 := by
    cases hl : EQ ep with
    | nil =>
      have h1 := hQ.head; rw [hl] at h1; simpa [LawfulStore.epQ] using h1
    | cons y ys =>
      have hy : y ∈ EQ ep := by rw [hl]; exact List.mem_cons_self
      obtain ⟨-, -, hbl⟩ := w4 ep hpE y hy
      obtain ⟨k1, k2, k3⟩ := w6.2.2.2.2.1 ep hpE y hy
      rcases hbl with e | e | e
      · have := k1 e; rw [hst] at this; exact absurd this (by decide)
      · have := k2 e; rw [hst] at this; exact absurd this (by decide)
      · have := k3 e; rw [hst] at this; exact absurd this (by decide)
  -- the release head (`rel_head` with the reply's link words)
  have HF := here_facts (L := L) (by obtain ⟨b, hb, hbt⟩ := C.here; subst hbt; exact hb)
  have hRel : L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) ≠ 0#u64 →
      L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) ∈ T ∧
      ∃ zc, RefillsWF st s (L.mem s (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD)))) zc ∧
        ∀ b, Aligned b → InSC (L.mem s (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD)))) zc b →
          b ∈ RΩ Ω Rp ∧ b ≠ rTcbA rptr ∧ ¬ InRing usc (Z usc) b := by
    intro h0
    have hq := hSQ.release _ hSQ.cur
    have hhd : (R (L.cpu s)).headD 0#u64 = L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) := hq.head.symm
    have hmem : L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) ∈ R (L.cpu s) := by
      rw [← hhd]
      cases e : R (L.cpu s) with
      | nil => rw [e] at hhd; exact absurd hhd.symm h0
      | cons x xs => simp
    have hrT := hq.mem _ hmem
    have haff := hSQ.inR _ hSQ.cur _ hmem
    have hrel := (hSQ.released _ hrT).2 (by rw [haff]; exact hmem)
    have hsc1 := hB.r _ hrT hrel
    have hact1 := hB.sact _ hrT (Or.inr (Or.inl hrel)) hsc1
    obtain ⟨hcS1, hback, -⟩ := hX0.bound _ hrT hsc1
    have hWF1 := (hS.all _ hcS1).1 ((hS.act _ hcS1).1 hact1)
    refine ⟨hrT, _, hWF1, fun b hb hin => ⟨⟨hS.sub _ ((hS.all _ hcS1).2.2 b hb hin), ?_⟩, ?_, ?_⟩⟩
    · rintro ⟨r', hr', e | e⟩
      · have := hX.1.rpSc r' hr' _ hcS1; rw [e] at hin; unfold InSC at hin
        rw [rPrevA_val (hX.1.rp r' hr')] at hin; omega
      · have := hX.1.rpSc r' hr' _ hcS1; rw [e] at hin; unfold InSC at hin
        rw [rNextA_val (hX.1.rp r' hr')] at hin; omega
    · intro e
      have := hX.1.rpSc rptr hrR _ hcS1
      rw [e] at hin; unfold InSC at hin; rw [rTcbA_val0] at hin; omega
    · intro hR
      have hne : L.mem s (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD))) ≠ usc := by
        intro e
        obtain ⟨-, hb2, -⟩ := hX0.bound u huT hsc0'
        rw [husc, ← e, hback] at hb2
        rw [hb2] at hrel; exact hrel HF.nr
      have := hX.1.scDisj _ hcS1 _ hcS hne
      unfold InRing at hR; unfold InSC at hin; omega
  refine {
    hT := hSQ.tcbs, ht := htT, hu := huT, hut := hut, hN := hSQ.nodes _ hSQ.cur, hcC := hSQ.cur,
    hΩ := hSQ.omega, hSg := hSg, hO := hX.1, hrR := hrR,
    hnx := fun h0 hb => (hX.2.1.next rptr hrR h0).2 hb,
    hpv := fun h0 => hX.2.1.prev rptr hrR h0,
    husc := husc, hsc0 := hsc0, hcS := hcS, hWF := hWF, scSg := (hS.all _ hcS).2.2,
    hE := hEP, hEN := hEN, hEΩ := w3 ep hpE, hq0 := hq0, hcur := et'.symm,
    hNt := fun h0 => by
      have hn := hX0.bnd t htT h0
      have hnE : L.mem s (boundA t) ∈ E := (w6.2.2.1 _).2 (Or.inr (hNt _ hn))
      obtain ⟨a1, a2, -⟩ := w1 _ hnE
      exact ⟨hn, a1, a2, w3 _ hnE⟩,
    hTM := hX0.tm.min _ hSQ.cur, hRel := hRel, hBM := ⟨_, (hSQ.ready _ hSQ.cur).2⟩ }

/-- `rrPl_lkG` at an UnknownSyscall fault (pf1). -/
theorem rrPl_lk {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
    (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    {s : S} {a : A} {t rptr ep u usc : U64} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hlk : ∀ cptr, cspace.lookup_cap st s (L.curW s) cptr ⦃ r => ∀ c, r = .Ok c → CapTyped H Rp Nt c ⦄)
    (et : sched.cur_thread st s = ok t)
    (hrc : fastpath.reply_caps st s t = ok (some (rptr, ep))) (C : RRChecks st ar s a t rptr ep u usc) :
    RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z s t rptr ep u usc := by
  apply rrPl_lkG (ty := fl4_abi.consts.fault.UnknownSyscall) <;> assumption


/-- `rrPl_lk` with the cap typing from `EntryHyps0.recvOK` at an `XG` state. -/
theorem rrPl_ofG {ty : U64} [HfrRestart st ar ty] {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {P3Ok : S → Prop}
    (E0 : EntryHyps0 st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    {s : S} {a : A} {t rptr ep u usc : U64} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hG : XG st T Cs Ω H Sg Scs Z P3Ok s) (et : sched.cur_thread st s = ok t)
    (hrc : fastpath.reply_caps st s t = ok (some (rptr, ep))) (C : RRChecksG st ar ty s a t rptr ep u usc) :
    RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z s t rptr ep u usc :=
  rrPl_lkG ar hNt hI (E0.recvOK Ac s hG hI).1 et hrc C

/-- `rrPl_ofG` at an UnknownSyscall fault (pf1). -/
theorem rrPl_of {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {P3Ok : S → Prop}
    (E0 : EntryHyps0 st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    {s : S} {a : A} {t rptr ep u usc : U64} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hG : XG st T Cs Ω H Sg Scs Z P3Ok s) (et : sched.cur_thread st s = ok t)
    (hrc : fastpath.reply_caps st s t = ok (some (rptr, ep))) (C : RRChecks st ar s a t rptr ep u usc) :
    RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z s t rptr ep u usc := by
  apply rrPl_ofG (ty := fl4_abi.consts.fault.UnknownSyscall) <;> assumption


end plof


/-! ## The assembly: `RRReads2` from `RRPl`, the ring-sum bound and two reads -/

section asm
variable {S : Type _} {A : Type _} {st : machine.Store S} (ar : machine.Arch A) [L : LawfulStore st]

/-- **The reads of `RRReads2` left after m68**: the two cap lookups at `X8`
(`lk8`) and m67's end-state read `nvm`. -/
structure RRReads4 (t rptr ep u : U64) (X8 X15 : S) (a2 : A) : Prop where
  lk8 : ∃ i i1 b0 b1 b3 b4 g, obj.Tcb.reg st t X8 layout.reg.CAP = ok i1 ∧
    cspace.lookup_cap st X8 t i1 = ok (core.result.Result.Ok (capability.Cap.Endpoint ep b0 b1 true b3 b4)) ∧
    obj.Tcb.reg st t X8 layout.reg.REPLY = ok i ∧
    cspace.lookup_cap st X8 t i = ok (core.result.Result.Ok (capability.Cap.Reply rptr g))
  nvm : ∀ s' a', fastpath.switch_to st ar X15 a2 u = ok (s', a') →
    L.mem s' (stA (L.curW s')) ≠ sched.TS_RUNNING_VM

variable {T Cs Ω Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}

theorem RRReads2.of_plG {ty : U64} [HfrRestart st ar ty] {X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15 : S} {a a1 a2 : A}
    {t rptr ep u usc : U64} {b9 : Bool}
    (P : RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z X0 t rptr ep u usc) (C : RRChecksG st ar ty X0 a t rptr ep u usc)
    (hsum : L.mem X0 (sporA usc) ≠ 0#u64 → L.amtSum X0 usc < 2 ^ 64)
    (e1 : obj.Tcb.set_state st t X0 sched.TS_RESTART = ok X1)
    (e2 : ipc.reply_remove st ar X1 a rptr u = ok (X2, a1))
    (e3s : sporadic.sc_sporadic st X2 usc = ok b9)
    (e3 : (if b9 then do
      let i13 ← obj.Sc.cpu st usc X2
      let i14 ← obj.node_get st X2 i13 layout.node.CUR_SC
      if usc != i14 then sporadic.unblock_check st X2 usc else ok X2
    else ok X2) = ok X3)
    (e4 : faults.handle_fault_reply st ar X3 a1 u t = ok (true, X4, a2))
    (e5 : faults.clear_fault st X4 u = ok X5)
    (e6 : obj.Tcb.set_state st u X5 sched.TS_RESTART = ok X6)
    (e7 : sched.set_action st X6 u = ok X7)
    (e8 : obj.Tcb.set_state st t X7 sched.TS_RUNNING = ok X8)
    (e9 : obj.Tcb.set_state st t X8 sched.TS_BLOCKED_ON_RECV = ok X9)
    (e10 : obj.Tcb.set_block_obj st t X9 ep = ok X10)
    (e11 : obj.Tcb.set_reply_obj st t X10 rptr = ok X11)
    (e12 : obj.Reply.set_tcb st rptr X11 t = ok X12)
    (e13 : obj.Tcb.set_ep_next st t X12 0#u64 = ok X13)
    (e14 : obj.Tcb.set_ep_prev st t X13 0#u64 = ok X14)
    (e15 : obj.Ep.set_queue st ep X14 t t obj.EP_RECV = ok X15)
    (R : RRReads4 (L := L) ar t rptr ep u X8 X15 a2) :
    RRReads2 (L := L) ar t rptr ep u usc X1 X2 X6 X7 X8 X11 X12 X15 a2 := by
  obtain ⟨-, ha2, K8, w08, -, hsc2, hsch6, hsc6, hrdy6, hsuf6, hpst, hst7, hact8, hact8', hct8, hrt8, hntfn, hep8⟩ :=
    rr_x8G ar P C hsum e1 e2 e3s e3 e4 e5 e6 e7 e8
  subst a2
  obtain ⟨hact11, hq12, hND, hact15, hct15, hhp15, hdq15⟩ := rr_x15G ar P C K8 w08 hact8 e9 e10 e11 e12 e13 e14 e15
  exact ⟨hsc2, hsch6, hsc6, hrdy6, hsuf6, hpst, hst7, hact8', hct8, R.lk8, hrt8, hntfn, hep8, hact11, hq12,
    hND.1, hND.2, hact15, hct15, hhp15, hdq15, R.nvm⟩

/-- `RRReads2.of_plG` at an UnknownSyscall fault (pf1). -/
theorem RRReads2.of_pl {X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15 : S} {a a1 a2 : A}
    {t rptr ep u usc : U64} {b9 : Bool}
    (P : RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z X0 t rptr ep u usc) (C : RRChecks st ar X0 a t rptr ep u usc)
    (hsum : L.mem X0 (sporA usc) ≠ 0#u64 → L.amtSum X0 usc < 2 ^ 64)
    (e1 : obj.Tcb.set_state st t X0 sched.TS_RESTART = ok X1)
    (e2 : ipc.reply_remove st ar X1 a rptr u = ok (X2, a1))
    (e3s : sporadic.sc_sporadic st X2 usc = ok b9)
    (e3 : (if b9 then do
      let i13 ← obj.Sc.cpu st usc X2
      let i14 ← obj.node_get st X2 i13 layout.node.CUR_SC
      if usc != i14 then sporadic.unblock_check st X2 usc else ok X2
    else ok X2) = ok X3)
    (e4 : faults.handle_fault_reply st ar X3 a1 u t = ok (true, X4, a2))
    (e5 : faults.clear_fault st X4 u = ok X5)
    (e6 : obj.Tcb.set_state st u X5 sched.TS_RESTART = ok X6)
    (e7 : sched.set_action st X6 u = ok X7)
    (e8 : obj.Tcb.set_state st t X7 sched.TS_RUNNING = ok X8)
    (e9 : obj.Tcb.set_state st t X8 sched.TS_BLOCKED_ON_RECV = ok X9)
    (e10 : obj.Tcb.set_block_obj st t X9 ep = ok X10)
    (e11 : obj.Tcb.set_reply_obj st t X10 rptr = ok X11)
    (e12 : obj.Reply.set_tcb st rptr X11 t = ok X12)
    (e13 : obj.Tcb.set_ep_next st t X12 0#u64 = ok X13)
    (e14 : obj.Tcb.set_ep_prev st t X13 0#u64 = ok X14)
    (e15 : obj.Ep.set_queue st ep X14 t t obj.EP_RECV = ok X15)
    (R : RRReads4 (L := L) ar t rptr ep u X8 X15 a2) :
    RRReads2 (L := L) ar t rptr ep u usc X1 X2 X6 X7 X8 X11 X12 X15 a2 := by
  apply RRReads2.of_plG (ty := fl4_abi.consts.fault.UnknownSyscall) <;> assumption


/-- **The ReplyRecv read bundle after m68** at a dispatch state: only
`RRReads4` (`lk8`, `nvm`) along every accepted run. -/
def RRPre3G (ty : U64) (X0 : S) (a : A) : Prop :=
  ∀ (t rptr ep u usc : U64) (X1 X2 : S) (a1 : A) (b9 : Bool) (X3 : S),
    sched.cur_thread st X0 = ok t → fastpath.reply_caps st X0 t = ok (some (rptr, ep)) →
    RRChecksG st ar ty X0 a t rptr ep u usc →
    obj.Tcb.set_state st t X0 sched.TS_RESTART = ok X1 →
    ipc.reply_remove st ar X1 a rptr u = ok (X2, a1) →
    sporadic.sc_sporadic st X2 usc = ok b9 →
    (if b9 then do
      let i13 ← obj.Sc.cpu st usc X2
      let i14 ← obj.node_get st X2 i13 layout.node.CUR_SC
      if usc != i14 then sporadic.unblock_check st X2 usc else ok X2
    else ok X2) = ok X3 →
    ∀ (X4 : S) (a2 : A) (X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15 : S),
      faults.handle_fault_reply st ar X3 a1 u t = ok (true, X4, a2) →
      faults.clear_fault st X4 u = ok X5 →
      obj.Tcb.set_state st u X5 sched.TS_RESTART = ok X6 →
      sched.set_action st X6 u = ok X7 →
      obj.Tcb.set_state st t X7 sched.TS_RUNNING = ok X8 →
      obj.Tcb.set_state st t X8 sched.TS_BLOCKED_ON_RECV = ok X9 →
      obj.Tcb.set_block_obj st t X9 ep = ok X10 →
      obj.Tcb.set_reply_obj st t X10 rptr = ok X11 →
      obj.Reply.set_tcb st rptr X11 t = ok X12 →
      obj.Tcb.set_ep_next st t X12 0#u64 = ok X13 →
      obj.Tcb.set_ep_prev st t X13 0#u64 = ok X14 →
      obj.Ep.set_queue st ep X14 t t obj.EP_RECV = ok X15 →
      RRReads4 (L := L) ar t rptr ep u X8 X15 a2

/-- `RRPre3G` at an UnknownSyscall fault (pf1). -/
abbrev RRPre3 (X0 : S) (a : A) : Prop :=
  RRPre3G (L := L) ar fl4_abi.consts.fault.UnknownSyscall X0 a


/-- m67's `RRPre2` from `RRPre3`, `RRPl` at every accepted run's checks and
the ring-sum bound `RRSum` at the dispatch state. -/
theorem RRPre2.of3G {ty : U64} [HfrRestart st ar ty] {X0 : S} {a : A}
    (hP : ∀ t rptr ep u usc, sched.cur_thread st X0 = ok t → fastpath.reply_caps st X0 t = ok (some (rptr, ep)) →
      RRChecksG st ar ty X0 a t rptr ep u usc → RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z X0 t rptr ep u usc)
    (hS : RRSum (L := L) Scs X0) (h : RRPre3G (L := L) ar ty X0 a) : RRPre2G (L := L) ar ty X0 a := by
  intro t rptr ep u usc X1 X2 a1 b9 X3 hct hrc hC e1 e2 e3s e3
  have P := hP t rptr ep u usc hct hrc hC
  have hsum : L.mem X0 (sporA usc) ≠ 0#u64 → L.amtSum X0 usc < 2 ^ 64 := hS usc P.hcS
  refine ⟨rr_r3G ar P hC hsum e1 e2 e3s e3,
    fun X4 a2 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 => ?_⟩
  exact RRReads2.of_plG ar P hC hsum e1 e2 e3s e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
    (h t rptr ep u usc X1 X2 a1 b9 X3 hct hrc hC e1 e2 e3s e3 X4 a2 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15
      e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15)

/-- `RRPre2.of3G` at an UnknownSyscall fault (pf1). -/
theorem RRPre2.of3 {X0 : S} {a : A}
    (hP : ∀ t rptr ep u usc, sched.cur_thread st X0 = ok t → fastpath.reply_caps st X0 t = ok (some (rptr, ep)) →
      RRChecks st ar X0 a t rptr ep u usc → RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z X0 t rptr ep u usc)
    (hS : RRSum (L := L) Scs X0) (h : RRPre3 (L := L) ar X0 a) : RRPre2 (L := L) ar X0 a := by
  apply RRPre2.of3G (ty := fl4_abi.consts.fault.UnknownSyscall) <;> assumption


/-- `RRPre3` at every dispatch state of the entry. -/
def RRPreAt3G (ty : U64) (s : S) (a : A) : Prop :=
  ∀ t nx s1 s2 a2, sched.cur_thread st s = ok t → obj.Tcb.reg st t s layout.reg.NEXT_IP = ok nx →
    obj.Tcb.set_reg st t s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1 →
    syscall.budget_ok st ar s1 a = ok (true, s2, a2) → RRPre3G (L := L) ar ty s2 a2

/-- `RRPreAt3G` at an UnknownSyscall fault (pf1). -/
abbrev RRPreAt3 (s : S) (a : A) : Prop :=
  RRPreAt3G (L := L) ar fl4_abi.consts.fault.UnknownSyscall s a


/-- **`RRSumAt` [J]** (l4v `valid_refills` / `refills_sum`; P3 `SInvR.RV`):
m65's `RRSum` at every dispatch state of the entry (after the `FAULT_IP`
write and a passing `budget_ok`), where R4 reads it for the receiver's SC.
Why at the dispatch state: `budget_ok` charges the current SC, whose ring sum
it conserves (`refill_budget_check` / `schedule_used` move amounts between
refills), but P1 has no sum carry through it either; asking it where it is
read keeps it one state, as m65 / m66 noted. Reachability: as `RRSum`
(m65): every sporadic SC's ring sums to its configured budget, below
`MAX_PERIOD < 2 ^ 64`; charges and merges conserve the sum. -/
def RRSumAt (Scs : Set U64) (s : S) (a : A) : Prop :=
  ∀ t nx s1 s2 a2, sched.cur_thread st s = ok t → obj.Tcb.reg st t s layout.reg.NEXT_IP = ok nx →
    obj.Tcb.set_reg st t s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1 →
    syscall.budget_ok st ar s1 a = ok (true, s2, a2) → RRSum (L := L) Scs s2

/-- **`RRPreAt2` from `RRPreAt3` and `RRSumAt`** at an entry state (the
dispatch state is a `BXI` / `XG` state, so `rrPl_of` gives `RRPl` there). -/
theorem RRPreAt2.of3G {ty : U64} [HfrRestart st ar ty] {U Ac : Set U64} {H : Heap} {P3Ok : S → Prop}
    (hA : P0.ArchTotal ar) (E0 : EntryHyps0 st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    {s : S} {a : A} (hP : P3Ok s) (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hSum : RRSumAt (L := L) ar Scs s a) (hR : RRPreAt3G (L := L) ar ty s a) : RRPreAt2G (L := L) ar ty s a := by
  intro t nx s1 s2 a2 et enx es1 hb
  have h0 := h.1.choose_spec.choose_spec
  have et' : t = L.curW s := by
    rw [eq_of_spec_fd (sched.cur_thread.spec (L := L) s)] at et; exact (ok_inj_ff et).symm
  have htT : t ∈ T := by rw [et']; exact h0.curT
  have h1 : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s1 := by
    have := reg_entry (r := layout.reg.FAULT_IP) (v := core.num.U64.wrapping_sub nx 2#u64) h htT
      (by simp [layout.reg.FAULT_IP])
    rw [es1, WP.spec_ok] at this; exact this
  have hW := obj.Tcb.set_reg.wrK (L := L) s t layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64)
    (h0.tcbs t htT) (by simp [layout.reg.FAULT_IP])
  rw [es1, WP.spec_ok] at hW
  obtain ⟨K, hK, e1⟩ := hW
  have hal : Aligned (core.num.U64.wrapping_add (L.curW s) K) := by
    rw [← et']; exact field_aligned (h0.tcbs t htT)
      (by rw [hK]; simp [layout.reg.FAULT_IP]) (by rw [hK]; simp [layout.reg.FAULT_IP])
  have e1' : s1 = L.wr s (core.num.U64.wrapping_add (L.curW s) K) (core.num.U64.wrapping_sub nx 2#u64) := by
    rw [e1, et']
  have he1 : EntAt st P3Ok s1 := ⟨s, hP, Ent.prefix hK hal e1' (WritesIn.refl _ _)⟩
  have hx := syscall.budget_ok.bxc hA E0 s1 a h1 he1.xg
  rw [hb, WP.spec_ok] at hx
  exact RRPre2.of3G ar (fun t' rptr ep u usc et2 hrc hC => rrPl_ofG ar E0 hNt hx.1 (hx.2.2 rfl) et2 hrc hC)
    (hSum t nx s1 s2 a2 et enx es1 hb) (hR t nx s1 s2 a2 et enx es1 hb)

/-- `RRPreAt2.of3G` at an UnknownSyscall fault (pf1). -/
theorem RRPreAt2.of3 {U Ac : Set U64} {H : Heap} {P3Ok : S → Prop}
    (hA : P0.ArchTotal ar) (E0 : EntryHyps0 st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    {s : S} {a : A} (hP : P3Ok s) (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hSum : RRSumAt (L := L) ar Scs s a) (hR : RRPreAt3 (L := L) ar s a) : RRPreAt2 (L := L) ar s a := by
  apply RRPreAt2.of3G (ty := fl4_abi.consts.fault.UnknownSyscall) <;> assumption


end asm

section top
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {U : Set U64}

/-- **Native kernel entries keep `EntryInv`, ReplyRecv half from two reads**
(m68): `entry_of7r2` with `hRP : RRPreAt2` (m67, 22 reads) replaced by
`hRP : RRPreAt3` (the two cap lookups `lk8` and m67's `nvm`) and the ring-sum
bound `hSum : RRSumAt` [J] at the dispatch states. -/
theorem kernel_entry.entry_of8 {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (GF : ∀ σ : PSets, Adm σ → Hyps4 st ar Adm Cs U P3Ok σ)
    (hσ : Adm ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩) {Ac : Set U64} (s : S) (a : A) (hP : P3Ok s)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hX : StoreExt st)
    (hAs : AsidOff (L := L) Ω Sg s)
    (hNv : ∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter → FaultNvmPre (L := L) ar s a number)
    (hSum : RRSumAt (L := L) ar Scs s a)
    (hRP : RRPreAt3 (L := L) ar s a) :
    (∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter → syscall.handle_syscall st ar s a number ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) ∧
    (∀ irq : U64, syscall.handle_interrupt_entry st ar s a irq ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) := by
  have E0 : EntryHyps0 st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok := by
    have G3 : InvGaps st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok := by
      obtain ⟨P, C, ⟨V, Pd⟩, Pt, G, -⟩ := GF _ hσ
      exact (G.gaps3 hA hσ C Pd Pt P.xfer).gaps hA P C
    exact (EntryHyps.of_gaps hA hσ (fun σ'' h'' => (GF σ'' h'').1) (GF _ hσ).1 G3).toEntryHyps0
  have hNt : ∀ n ∈ Nt, H n = some .ntfn := (GF _ hσ).2.2.2.2.2
  exact kernel_entry.entry_of7r2 hA GF hσ s a hP h hX hAs hNv (RRPreAt2.of3 ar hA E0 hNt hP h hSum hRP)

end top

end Fl4Proofs.P1
