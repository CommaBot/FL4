/-
# P2: guarded-store lemmas for `switch_sched_context` and its refill callees

Built on `P2/AccessRefill.lean` (`ScAcc`: the guarded sets hold an SC, read
everywhere, written on its ring part and `CONSUMED`), for the per-path
obligation of `P2/PathObl.lean`:

* `sporadic.unblock_check.guardS`: also the node's `CUR_TIME` (read) and
  `REPROGRAM` (written; outside the SC, as P1's `unblock_check.wf` asks);
* `sporadic.budget_check.guardS`: also the node's `CUR_SC` (read);
* `sched.commit_time.guardS`: the current SC `c` (`ScAcc`, its ring
  well formed when active), the node's `CUR_SC`, `IDLE_SC` and `CONSUMED`;
* `sched.switch_sched_context.guard`: the current thread's SC word, the
  node's words, the current SC and (when it differs) the thread's SC, under
  P1's facts of `sched.switch_sched_context.fp` (both rings well formed, the
  SCs disjoint, the node words outside both), stated directly.

Generic over the Arch instance: only `P0.ArchTotal` (P1's `.fr` lemmas use
it to know the Arch calls return). No premises.
-/
import Fl4Proofs.P2.AccessRefill
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts

section
variable {S : Type} {st : machine.Store S} {R W : U64 → Prop} [L : LawfulStore st]
variable {s : S} {sc : obj.Sc} {sb : Nat}

theorem sporadic.sc_active.guardSl (s : S) (sc : obj.Sc) (h : R (maxA sc)) :
    sporadic.sc_active (PathObl.guard st R W) s sc = sporadic.sc_active st s sc := by
  unfold sporadic.sc_active
  rw [obj.Sc.refill_max.guard sc s h]

theorem sporadic.unblock_check.guardS (hS : ScAcc R W sc sb) (h : RefillsWF st s sc sb)
    (hrep : Aligned (L.nodeA s layout.node.REPROGRAM) ∧ Outside (L.nodeA s layout.node.REPROGRAM) sc sb)
    (hct : R (ctA (L := L) s)) (hrp : W (L.nodeA s layout.node.REPROGRAM)) :
    sporadic.unblock_check (PathObl.guard st R W) s sc = sporadic.unblock_check st s sc := by
  unfold sporadic.unblock_check
  rw [sporadic.is_round_robin.guard s sc (hS.off h _ (by simp)), sporadic.ready.guard s sc (hS.head h) hct]
  refine bind_guard_congr rfl fun b _ => ?_
  split
  · rfl
  refine bind_guard_congr rfl fun b1 _ => ?_
  split
  · rw [sporadic.cur_time.guard s hct, sporadic.head.guardS hS h]
    refine bind_guard_congr rfl fun now _ => ?_
    refine bind_guard_congr rfl fun hd _ => ?_
    rw [sporadic.set_head.guardS hS h]
    refine bind_guard_congr rfl fun s1 hs1 => ?_
    rw [eq_ok_of_spec (sporadic.set_head.eq s sc _)] at hs1
    cases ok_inj_ff hs1
    have h1 := h.putS (r := { time := now, amount := hd.amount }) h.head_lt
    simp only [guard_cur_cpu, L.cur_cpu_eq, bind_ok]
    have e : ∀ r : sporadic.Refill, L.nodeAt (L.putS s sc (L.rhead s sc) r)
        (L.cpu (L.putS s sc (L.rhead s sc) r)) layout.node.REPROGRAM = L.nodeA s layout.node.REPROGRAM := by
      intro r; simp [LawfulStore.putS, LawfulStore.nodeA]
    rw [obj.node_set.guard _ _ _ _ (by rw [e]; exact hrp)]
    refine bind_guard_congr rfl fun s2 hs2 => ?_
    rw [eq_ok_of_spec (obj.node_set.spec _ _ _ _), e] at hs2
    cases ok_inj_ff hs2
    have h2 := h1.wr_out (v := 1#u64) hrep.1 hrep.2
    rw [obj.Sc.refill_max.guard sc _ (hS.off h2 _ (by simp))]
    refine bind_guard_congr rfl fun i _ => ?_
    simp only [lift, bind_ok]
    exact sporadic.unblock_check_loop.guardS hS h2 _
  · rfl

theorem sporadic.budget_check.guardS {A : Type} (ar : machine.Arch A) (a : A) (usage : U64)
    (hS : ScAcc R W sc sb) (h : RefillsWF st s sc sb) (hcur : L.mem s (L.nodeA s layout.node.CUR_SC) = sc)
    (hcs : R (L.nodeA s layout.node.CUR_SC)) :
    sporadic.budget_check (PathObl.guard st R W) ar s a usage = sporadic.budget_check st ar s a usage := by
  unfold sporadic.budget_check
  simp only [guard_cur_cpu, L.cur_cpu_eq, bind_ok]
  rw [obj.node_get.guard s _ _ hcs, node_get_ok]
  simp only [bind_ok]
  have e : L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_SC) = sc := hcur
  rw [e]
  simp only [obj.Sc.period.guard sc s (hS.off h _ (by simp)), sporadic.budget_check_loop0.guardS hS h]
  refine bind_guard_congr rfl fun mrt _ => ?_
  refine bind_guard_congr rfl fun per _ => ?_
  refine bind_guard_congr rfl fun p hp => ?_
  obtain ⟨s1, us⟩ := p
  have h1 : RefillsWF st s1 sc sb := post_of_ok (sporadic.budget_check_loop0.wf mrt per usage _ h) hp
  simp only [Aeneas.Std.uncurry_apply_pair]
  simp only [sporadic.head.guardS hS h1, sporadic.set_head.guardS hS h1]
  refine bind_guard_congr rfl fun hd _ => ?_
  refine bind_guard_congr ?_ fun s2 hs2 => ?_
  · split_ifs
    · simp only [lift, bind_ok]
      refine bind_guard_congr rfl fun s3 hs3 => ?_
      exact sporadic.schedule_used.guardS hS (post_of_ok (sporadic.set_head.wf _ h1) hs3) _
    all_goals rfl
  · have h2 : RefillsWF st s2 sc sb := by
      split_ifs at hs2
      · simp only [lift, bind_ok] at hs2
        obtain ⟨s3, hs3, hs2⟩ := bind_eq_ok hs2
        exact post_of_ok (sporadic.schedule_used.wf _ (post_of_ok (sporadic.set_head.wf _ h1) hs3)) hs2
      all_goals (cases ok_inj_ff hs2; exact h1)
    refine bind_guard_congr rfl fun mb _ => ?_
    rw [obj.Sc.refill_max.guard sc s2 (hS.off h2 _ (by simp))]
    refine bind_guard_congr rfl fun i2 _ => ?_
    simp only [lift, bind_ok]
    exact sporadic.budget_check_loop1.guardS hS h2 _ _

/-- **`commit_time`** on the current SC `c`. -/
theorem sched.commit_time.guardS {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (a : A) (c : U64)
    (hcur : L.mem s (L.nodeA s layout.node.CUR_SC) = c) (hS : ScAcc R W c sb)
    (h0 : L.rmax s c ≠ 0#u64 → RefillsWF st s c sb) (hmx : R (maxA c))
    (hcons : Aligned (L.nodeA s layout.node.CONSUMED)) (hconsO : Outside (L.nodeA s layout.node.CONSUMED) c sb)
    (hcs : R (L.nodeA s layout.node.CUR_SC)) (hid : R (L.nodeA s layout.node.IDLE_SC))
    (hcn : R (L.nodeA s layout.node.CONSUMED)) (hcw : W (L.nodeA s layout.node.CONSUMED)) :
    sched.commit_time (PathObl.guard st R W) ar s a = sched.commit_time st ar s a := by
  have hfr := sched.commit_time.fr hA a h0 hcur hcons hconsO
  unfold sched.commit_time at hfr ⊢
  rw [sched.cur_sc.guard s hcs, eq_ok_of_spec (sched.cur_sc.spec s), hcur]
  rw [eq_ok_of_spec (sched.cur_sc.spec s), hcur] at hfr
  simp only [bind_ok] at hfr ⊢
  rw [sporadic.sc_active.guardSl s c hmx]
  refine bind_guard_congr rfl fun b hb => ?_
  refine bind_guard_congr ?_ fun s1 hs1 => ?_
  · split
    · rename_i hbt
      have h := h0 (post_of_ok (sporadic.sc_active.val s c) hb hbt)
      rw [sched.idle_sc.guard s hid]
      refine bind_guard_congr rfl fun i2 _ => ?_
      refine bind_guard_congr rfl fun b1 _ => ?_
      split
      · rw [sched.consumed.guard s hcn]
        refine bind_guard_congr rfl fun cu _ => ?_
        obtain ⟨r1, w1, r2, w2⟩ := hS.rt h h.head_lt
        obtain ⟨r3, w3, r4, w4⟩ := hS.rt h h.tail_lt
        simp only [sporadic.is_round_robin.guard s c (hS.off h layout.sc.PERIOD (by simp)),
          obj.Sc.refill_head.guard _ s (hS.off h _ (by simp)), obj.Sc.refill_tail.guard _ s (hS.off h _ (by simp)),
          eq_ok_of_spec (obj.Sc.refill_head.spec s c), eq_ok_of_spec (obj.Sc.refill_tail.spec s c), bind_ok,
          sporadic.get.guard _ _ _ r1 r2, sporadic.get.guard _ _ _ r3 r4, sporadic.put.guard _ _ _ w1 w2,
          sporadic.put.guard _ _ _ w3 w4, sporadic.budget_check.guardS ar a _ hS h hcur hcs,
          obj.Sc.consumed.guard _ _ (hS.off h _ (by simp)), obj.Sc.set_consumed.guard _ _ _ hS.cons]
      · rfl
    · rfl
  · rw [hb] at hfr
    simp only [bind_ok] at hfr
    rw [hs1] at hfr
    simp only [bind_ok] at hfr
    rw [eq_ok_of_spec (sched.set_consumed.spec s1 0#u64)] at hfr
    have w := (WP.spec_ok _).1 hfr
    have k1 : L.ksb s1 = L.ksb s := by have := w.1.1; simpa using this
    have c1 : L.cpu s1 = L.cpu s := by have := w.1.2.1; simpa using this
    have e : L.nodeAt s1 (L.cpu s1) layout.node.CONSUMED = L.nodeA s layout.node.CONSUMED := by
      rw [c1, nodeAt_of_ksb k1]; rfl
    exact sched.set_consumed.guard s1 _ (by rw [e]; exact hcw)

/-- **`switch_sched_context`** (module docstring): `i` the current thread's
SC, `c` the current SC, P1's facts stated directly. -/
theorem sched.switch_sched_context.guard {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    {T : Set U64} {zc zt : Nat} {i c : U64} (hN' : NodePlaced st T s (L.cpu s))
    (hi : L.mem s (scA (L.curW s)) = i) (hc : L.mem s (L.nodeA s layout.node.CUR_SC) = c)
    (hNo : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → Aligned (L.nodeA s o) ∧ Outside (L.nodeA s o) c zc ∧
      (i ≠ c → Outside (L.nodeA s o) i zt))
    (hcq : L.rmax s c ≠ 0#u64 → RefillsWF st s c zc) (hcM : InSC c zc (maxA c) ∧ Aligned (maxA c))
    (hti : i ≠ c → RefillsWF st s i zt ∧ ∀ b, InSC i zt b → Outside b c zc)
    (hSc : ScAcc R W c zc) (hSi : i ≠ c → ScAcc R W i zt)
    (hNd : ∀ o : U64, o.val < 4288 → R (L.nodeA s o) ∧ W (L.nodeA s o)) (hsc : R (scA (L.curW s))) :
    sched.switch_sched_context (PathObl.guard st R W) ar s a = sched.switch_sched_context st ar s a := by
  have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
  have cs : layout.node.CUR_SC.val = 24 := by simp [layout.node.CUR_SC]
  have cn : layout.node.CONSUMED.val = 40 := by simp [layout.node.CONSUMED]
  have nd : ∀ o : U64, o.val < 4288 → R (L.nodeA s o) ∧ W (L.nodeA s o) := hNd
  have aR := (hNo _ (by rw [rp]; omega) (by rw [rp])).1
  have oRc := (hNo _ (by rw [rp]; omega) (by rw [rp])).2.1
  have oRi := (hNo _ (by rw [rp]; omega) (by rw [rp])).2.2
  have aC := (hNo _ (by rw [cs]; omega) (by rw [cs])).1
  have oCi := (hNo _ (by rw [cs]; omega) (by rw [cs])).2.2
  have aN := (hNo _ (by rw [cn]; omega) (by rw [cn])).1
  have oNc := (hNo _ (by rw [cn]; omega) (by rw [cn])).2.1
  have hRC : (L.nodeA s layout.node.REPROGRAM).val ≠ (L.nodeA s layout.node.CUR_SC).val := by
    simp only [LawfulStore.nodeA]; rw [nodeAt_val hN' (by rw [rp]; omega), nodeAt_val hN' (by rw [cs]; omega), rp, cs]
    omega
  unfold sched.switch_sched_context
  rw [sched.cur_thread.guard s (nd layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD])).1, cur_thread_ok]
  simp only [bind_ok]
  rw [obj.Tcb.sc.guard _ s hsc, tcb_sc_ok, hi]
  simp only [bind_ok]
  rw [sched.cur_sc.guard s (nd _ (by rw [cs]; omega)).1, eq_ok_of_spec (sched.cur_sc.spec s), hc]
  simp only [bind_ok]
  refine bind_guard_congr rfl fun b hb => ?_
  have hb' : b = true ↔ c ≠ i := post_of_ok (sc_ne.spec' c i) hb
  refine bind_guard_congr ?_ fun s2 hs2 => ?_
  · split
    · rename_i hbt
      have hne : i ≠ c := fun e => (hb'.1 hbt) e.symm
      have hSi' := hSi hne
      rw [sched.set_reprogram.guard s (nd _ (by rw [rp]; omega)).2]
      refine bind_guard_congr rfl fun s3 hs3 => ?_
      rw [eq_ok_of_spec (sched.set_reprogram.spec s)] at hs3
      cases ok_inj_ff hs3
      have hSt3 := (hti hne).1.wr_out (v := 1#u64) aR (oRi hne)
      rw [sporadic.sc_constant_bandwidth.guard _ i (hSi'.off hSt3 _ (by simp))]
      refine bind_guard_congr rfl fun b1 _ => ?_
      split
      · have e3 : ∀ o, L.nodeA (L.wr s (L.nodeA s layout.node.REPROGRAM) 1#u64) o = L.nodeA s o := fun o => by simp
        refine sporadic.unblock_check.guardS hSi' hSt3 ⟨by rw [e3]; exact aR, by rw [e3]; exact oRi hne⟩ ?_
          (by rw [e3]; exact (nd _ (by rw [rp]; omega)).2)
        show R (L.nodeA _ layout.node.CUR_TIME)
        rw [e3]; exact (nd _ (by simp [layout.node.CUR_TIME])).1
      · rfl
    · rfl
  · -- the state after the first `if`
    have w2 : WritesIn st s s2 (fun x => (i ≠ c ∧ InRing i zt x) ∨ x = L.nodeA s layout.node.REPROGRAM) := by
      split at hs2
      · rename_i hbt
        have hne : i ≠ c := fun e => (hb'.1 hbt) e.symm
        obtain ⟨s3, hs3, hs2⟩ := bind_eq_ok hs2
        rw [eq_ok_of_spec (sched.set_reprogram.spec s)] at hs3
        cases ok_inj_ff hs3
        have w3 : WritesIn st s (L.wr s (L.nodeA s layout.node.REPROGRAM) 1#u64)
            (fun x => (i ≠ c ∧ InRing i zt x) ∨ x = L.nodeA s layout.node.REPROGRAM) :=
          (writesIn_wr aR).mono fun x hx => Or.inr hx
        obtain ⟨b1, -, hs2⟩ := bind_eq_ok hs2
        split at hs2
        · have e3 : L.nodeA (L.wr s (L.nodeA s layout.node.REPROGRAM) 1#u64) layout.node.REPROGRAM =
              L.nodeA s layout.node.REPROGRAM := by simp
          have hSt3 := (hti hne).1.wr_out (v := 1#u64) aR (oRi hne)
          have w4 := post_of_ok (sporadic.unblock_check.fr hSt3 ⟨by rw [e3]; exact aR, by rw [e3]; exact oRi hne⟩) hs2
          rw [e3] at w4
          exact w3.trans1 (w4.mono fun x hx => hx.elim (fun h => Or.inl ⟨hne, h⟩) Or.inr)
        · cases ok_inj_ff hs2; exact w3
      · cases ok_inj_ff hs2; exact WritesIn.refl _ _
    have k2 := w2.1
    have c2 := w2.2.1
    have eN : ∀ o, L.nodeA s2 o = L.nodeA s o := fun o => by
      simp only [LawfulStore.nodeA]; rw [c2, nodeAt_of_ksb k2]
    have notC : ∀ x, InSC c zc x → ¬ ((i ≠ c ∧ InRing i zt x) ∨ x = L.nodeA s layout.node.REPROGRAM) := by
      rintro x hx (⟨hne, h⟩ | rfl)
      · have := (hti hne).2 x h.inSC; unfold Outside at this; unfold InSC at hx; omega
      · unfold Outside at oRc; unfold InSC at hx; omega
    have m2 : L.mem s2 (L.nodeA s2 layout.node.CUR_SC) = c := by
      rw [eN, w2.mem_eq aC ?_, hc]
      rintro (⟨hne, h⟩ | h)
      · have := oCi hne; unfold Outside at this; unfold InRing at h; omega
      · exact hRC (congrArg UScalar.val h).symm
    have mx2 : L.rmax s2 c = L.rmax s c := w2.mem_eq hcM.2 (notC _ hcM.1)
    have wf2 : L.rmax s2 c ≠ 0#u64 → RefillsWF st s2 c zc := fun hm =>
      (hcq (by rw [← mx2]; exact hm)).writesIn w2 fun x hx h => by
        by_contra hn
        have hin : InSC c zc x := by unfold Outside at hn; push Not at hn; exact hn
        exact notC x hin h
    simp only [guard_cur_cpu, L.cur_cpu_eq, bind_ok]
    have eN' : ∀ o, L.nodeAt s2 (L.cpu s2) o = L.nodeA s o := eN
    rw [obj.node_get.guard s2 _ _ (by rw [eN']; exact (nd _ (by rw [rp]; omega)).1), node_get_ok]
    simp only [bind_ok]
    refine bind_guard_congr ?_ fun s3 hs3 => ?_
    · split
      · exact sched.commit_time.guardS hA a c m2 hSc wf2 (hSc.rd _ hcM.1) (by rw [eN]; exact aN)
          (by rw [eN]; exact oNc) (by rw [eN]; exact (nd _ (by rw [cs]; omega)).1)
          (by rw [eN]; exact (nd _ (by simp [layout.node.IDLE_SC])).1)
          (by rw [eN]; exact (nd _ (by rw [cn]; omega)).1) (by rw [eN]; exact (nd _ (by rw [cn]; omega)).2)
      · rfl
    · have k3 : L.ksb s3 = L.ksb s2 ∧ L.cpu s3 = L.cpu s2 := by
        split at hs3
        · have := post_of_ok (sched.commit_time.fr hA a wf2 m2 (by rw [eN]; exact aN) (by rw [eN]; exact oNc)) hs3
          exact ⟨this.1.1, this.1.2.1⟩
        · cases ok_inj_ff hs3; exact ⟨rfl, rfl⟩
      have e : L.nodeAt s3 (L.cpu s3) layout.node.CUR_SC = L.nodeA s layout.node.CUR_SC := by
        rw [k3.2, nodeAt_of_ksb k3.1]; exact eN' _
      rw [obj.node_set.guard s3 _ _ _ (by rw [e]; exact (nd _ (by rw [cs]; omega)).2)]

end

end Fl4Proofs.P2.PathObl
