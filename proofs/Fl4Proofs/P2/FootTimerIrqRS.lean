/-
# P2: the round-robin case's walk: the writes of the `charge_budget` run

`is_schedulable_rel`: `is_schedulable` reads of the queue word only its `Q_RELEASE` bit (P1
`is_schedulable_congr` with that weaker premise), so `append`'s setting of `Q_QUEUED` keeps it (P1 `or_qq_qr`).

`RrWT`: the words the round-robin `charge_budget` run (`charge_budget_rr_run`: the ring merge, the node's
`CONSUMED`, `append` of the current thread, the action, `set_reprogram`) and the timer handler write, relative to
the entry state `X`: the current SC's ring and `CONSUMED`, this core's node words at 16, 40, 56, 80 and from 120 up
(ready queues and bitmap), the current thread's queue word and the sched links of any thread.

`rr_run_writes`: the run writes only `RrWT`, sets the current thread's `Q_QUEUED` bit (P1 `sched.append.foot`) and
leaves the action `CHOOSE_NEW`.

No named premises.
-/
import Fl4Proofs.P2.FootTimerIrqRC
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

section law
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- **`is_schedulable` reads only the `Q_RELEASE` bit of the queue word** (module docstring). -/
theorem is_schedulable_rel {s s' : S} {t : U64}
    (hr : Runnable (L.mem s' (stA t)) ↔ Runnable (L.mem s (stA t)))
    (hsc : L.mem s' (scA t) = L.mem s (scA t))
    (hm : L.mem s (scA t) ≠ 0#u64 → L.rmax s' (L.mem s (scA t)) = L.rmax s (L.mem s (scA t)))
    (hq : (L.mem s' (inqA t) &&& sched.Q_RELEASE) = (L.mem s (inqA t) &&& sched.Q_RELEASE)) :
    sched.is_schedulable st s' t = sched.is_schedulable st s t := by
  unfold sched.is_schedulable
  rw [eq_of_spec_fd (sched.is_runnable.spec (L := L) s' t), eq_of_spec_fd (sched.is_runnable.spec (L := L) s t)]
  have hd : decide (L.mem s' (stA t) = sched.TS_RUNNING ∨ L.mem s' (stA t) = sched.TS_RESTART ∨
      L.mem s' (stA t) = sched.TS_RUNNING_VM) = decide (L.mem s (stA t) = sched.TS_RUNNING ∨
      L.mem s (stA t) = sched.TS_RESTART ∨ L.mem s (stA t) = sched.TS_RUNNING_VM) := by
    unfold Runnable at hr; exact decide_eq_decide.2 hr
  rw [hd]; simp only [bind_ok]
  split
  · simp only [eq_of_spec_fd (obj.Tcb.sc.spec (L := L) s' t), eq_of_spec_fd (obj.Tcb.sc.spec (L := L) s t), hsc,
      bind_ok, eq_of_spec_fd (obj.Sc.is_null.spec _)]
    split
    · rfl
    · rename_i h0
      have h0' : L.mem s (scA t) ≠ 0#u64 := by simpa using h0
      unfold sporadic.sc_active
      simp only [eq_of_spec_fd (obj.Sc.refill_max.spec (L := L) s' _),
        eq_of_spec_fd (obj.Sc.refill_max.spec (L := L) s _), hm h0', bind_ok,
        eq_of_spec_fd (sched.in_release_queue.spec (L := L) s' t),
        eq_of_spec_fd (sched.in_release_queue.spec (L := L) s t), hq]
  · rfl

/-- The words the round-robin `charge_budget` run and the timer handler write (module docstring). -/
def RrWT (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (X : S) (ct csc : U64) (z : Nat) (b : U64) :
    Prop :=
  InRing csc z b ∨ b = core.num.U64.wrapping_add csc layout.sc.CONSUMED ∨
    L.NodeOf X (L.cpu X) (fun o => o = 16 ∨ o = 40 ∨ o = 56 ∨ o = 80 ∨ 120 ≤ o) b ∨ b = inqA ct ∨
    (∃ y ∈ T, b = nextA .Sched y ∨ b = prevA .Sched y)

/-- **`highest_prio` reads only the bitmap**: at a state agreeing on this core's bitmap words with one whose
bitmap is well formed and non-empty, it returns the same priority (both are the unique highest marked one, P1
`sched.highest_prio.spec`). -/
theorem highest_prio_agree {T : Set U64} {Y Z : S} {NE : U64 → Prop} (d : U64)
    (hN : NodePlaced st T Y (L.cpu Y)) (hB : BitmapOK st Y (L.cpu Y) NE) (hl : L.l1W Y (L.cpu Y) ≠ 0#u64)
    (k : L.ksb Z = L.ksb Y) (c : L.cpu Z = L.cpu Y) (h1 : L.l1W Z (L.cpu Y) = L.l1W Y (L.cpu Y))
    (h2 : ∀ g < 4, L.l2W Z (L.cpu Y) g = L.l2W Y (L.cpu Y) g) :
    sched.highest_prio st Z d = sched.highest_prio st Y d := by
  have hNZ : NodePlaced st T Z (L.cpu Z) := by rw [c]; exact hN.ksb k
  have hBZ : BitmapOK st Z (L.cpu Z) NE := by rw [c]; exact hB.agree h1 h2
  have hlZ : L.l1W Z (L.cpu Z) ≠ 0#u64 := by rw [c, h1]; exact hl
  obtain ⟨q1, e1, a1, b1, m1⟩ := spec_ex_fd (sched.highest_prio.spec (L := L) Y d NE hN hB hl)
  obtain ⟨q2, e2, a2, b2, m2⟩ := spec_ex_fd (sched.highest_prio.spec (L := L) Z d NE hNZ hBZ hlZ)
  rw [e1, e2]
  have i1 := m1 q2 a2 b2
  have i2 := m2 q1 a1 b1
  exact congrArg ok (UScalar.eq_of_val_eq (by omega))

end law

section run
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {R W : U64 → Prop}

/-- **The writes of the round-robin `charge_budget` run** (module docstring). -/
theorem rr_run_writes {A : Type} (ar : machine.Arch A) {s1 s2 s3 s4 Y : S} {a : A} {c : U64} {z : Nat}
    (hN : NodePlaced st T s1 (L.cpu s1)) (hW : RefillsWF st s1 (L.cscW s1) z)
    (hal : Aligned (core.num.U64.wrapping_add (L.cscW s1) layout.sc.CONSUMED))
    (e2 : cbRR st s1 (L.cscW s1) c = ok s2) (e3 : sched.set_consumed st s2 0#u64 = ok s3)
    (F3 : RRTail st ar T R W s3 a) (ea : sched.append st s3 (L.curW s3) = ok s4)
    (e6 : sched.set_reprogram st
      (L.wr s4 (L.nodeAt s4 (L.cpu s4) layout.node.SCHED_ACTION) sched.ACTION_CHOOSE_NEW) = ok Y) :
    WritesIn st s1 Y (RrWT st T s1 (L.curW s3) (L.cscW s1) z) ∧
      L.mem Y (inqA (L.curW s3)) =
        (if (L.mem s3 (inqA (L.curW s3)) &&& sched.Q_QUEUED) ≠ 0#u64 then L.mem s3 (inqA (L.curW s3))
          else L.mem s3 (inqA (L.curW s3)) ||| sched.Q_QUEUED) ∧
      L.actionW Y = sched.ACTION_CHOOSE_NEW := by
  obtain ⟨w2, -⟩ := cbRR_frame hW hal e2
  have e3' : s3 = L.wr s2 (L.nodeAt s2 (L.cpu s2) layout.node.CONSUMED) 0#u64 := by
    have e := e3
    rw [eq_of_spec_fd (sched.set_consumed.spec (L := L) s2 _)] at e
    exact (ok_inj_ff e).symm
  rw [w2.2.1, nodeAt_of_ksb w2.1] at e3'
  have aC : Aligned (L.nodeAt s1 (L.cpu s1) layout.node.CONSUMED) :=
    nodeAt_aligned hN (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
  have w2' : WritesIn st s1 s2 (RrWT st T s1 (L.curW s3) (L.cscW s1) z) :=
    w2.mono fun b hb => by
      rcases hb with hb | hb
      · exact Or.inl hb
      · exact Or.inr (Or.inl hb)
  have w3 : WritesIn st s2 s3 (RrWT st T s1 (L.curW s3) (L.cscW s1) z) := by
    rw [e3']
    exact (writesIn_wr aC).mono fun b hb => Or.inr (Or.inr (Or.inl ⟨layout.node.CONSUMED,
      by simp [layout.node.CONSUMED], by simp [layout.node.CONSUMED], by simp [layout.node.CONSUMED], hb⟩))
  have w13 := w2'.trans1 w3
  have k3 : L.ksb s3 = L.ksb s1 := w13.1
  have c3 : L.cpu s3 = L.cpu s1 := w13.2.1
  -- `append`
  obtain ⟨xs, hr, hq⟩ := F3.rel
  have hN3' : NodePlaced st T s3 (L.mem s3 (affA (L.curW s3))) := by rw [F3.aff]; exact F3.hN
  obtain ⟨wa, hinq⟩ := PathObl.post_of_ok
    (sched.append.foot (L := L) s3 (L.curW s3) xs F3.hT F3.ct F3.prio hN3' F3.hN (by rw [F3.aff]; exact hr) hq) ea
  have w4 : WritesIn st s3 s4 (RrWT st T s1 (L.curW s3) (L.cscW s1) z) := wa.mono fun b hb => by
    rcases hb with ⟨y, hy, hb⟩ | ⟨o, ho, h1, h2, rfl⟩ | rfl | ⟨o, ho, h1, h2, rfl⟩
    · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨y, ?_, hb⟩)))
      rcases List.mem_cons.1 hy with rfl | hy
      · exact F3.ct
      · exact hr.mem _ hy
    · refine Or.inr (Or.inr (Or.inl ⟨o, Or.inr (Or.inr (Or.inr (Or.inr (Nat.le_trans (by decide) ho)))), h1, h2,
        ?_⟩))
      rw [F3.aff, c3, nodeAt_of_ksb k3]
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · refine Or.inr (Or.inr (Or.inl ⟨o, Or.inr (Or.inr (Or.inr (Or.inr (Nat.le_of_eq (Eq.symm ho))))), h1, h2,
        ?_⟩))
      rw [c3, nodeAt_of_ksb k3]
  have k4 : L.ksb s4 = L.ksb s1 := wa.1.trans k3
  have c4 : L.cpu s4 = L.cpu s1 := wa.2.1.trans c3
  -- the action and `set_reprogram`
  have e5 : L.nodeAt s4 (L.cpu s4) layout.node.SCHED_ACTION = L.nodeAt s1 (L.cpu s1) layout.node.SCHED_ACTION := by
    rw [c4, nodeAt_of_ksb k4]
  rw [e5] at e6
  have aA : Aligned (L.nodeAt s1 (L.cpu s1) layout.node.SCHED_ACTION) :=
    nodeAt_aligned hN (by rw [act_val]; omega) (by rw [act_val])
  have aR : Aligned (L.nodeAt s1 (L.cpu s1) layout.node.REPROGRAM) :=
    nodeAt_aligned hN (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])
  have w5 : WritesIn st s4 (L.wr s4 (L.nodeAt s1 (L.cpu s1) layout.node.SCHED_ACTION) sched.ACTION_CHOOSE_NEW)
      (RrWT st T s1 (L.curW s3) (L.cscW s1) z) :=
    (writesIn_wr aA).mono fun b hb => Or.inr (Or.inr (Or.inl ⟨layout.node.SCHED_ACTION,
      Or.inl act_val, by rw [act_val]; omega, by rw [act_val], hb⟩))
  have e6' : Y = L.wr (L.wr s4 (L.nodeAt s1 (L.cpu s1) layout.node.SCHED_ACTION) sched.ACTION_CHOOSE_NEW)
      (L.nodeAt s1 (L.cpu s1) layout.node.REPROGRAM) 1#u64 := by
    have e := e6
    rw [eq_of_spec_fd (sched.set_reprogram.spec (L := L) _)] at e
    rw [← ok_inj_ff e]
    unfold LawfulStore.nodeA
    rw [LawfulStore.cpu_wr, nodeAt_of_ksb (L.ksb_wr _ _ _), c4, nodeAt_of_ksb k4]
  have w6 : WritesIn st (L.wr s4 (L.nodeAt s1 (L.cpu s1) layout.node.SCHED_ACTION) sched.ACTION_CHOOSE_NEW) Y
      (RrWT st T s1 (L.curW s3) (L.cscW s1) z) := by
    rw [e6']
    exact (writesIn_wr aR).mono fun b hb => Or.inr (Or.inr (Or.inl ⟨layout.node.REPROGRAM,
      Or.inr (Or.inr (Or.inl (by simp [layout.node.REPROGRAM]))), by simp [layout.node.REPROGRAM],
      by simp [layout.node.REPROGRAM], hb⟩))
  have wY := ((w13.trans1 w4).trans1 w5).trans1 w6
  have hRA : L.nodeAt s1 (L.cpu s1) layout.node.REPROGRAM ≠ L.nodeAt s1 (L.cpu s1) layout.node.SCHED_ACTION :=
    nodeAt_ne hN (by simp [layout.node.REPROGRAM]) (by rw [act_val]; omega)
      (by rw [act_val]; simp [layout.node.REPROGRAM])
  have ht' := F3.hT _ F3.ct
  have aI : Aligned (inqA (L.curW s3)) := field_aligned ht' (by simp) (by simp)
  refine ⟨wY, ?_, ?_⟩
  · rw [e6', mem_wr_ne' aR aI (Ne.symm (tcb_node_ne hN F3.ct ht' (K := 3592#u64) (by simp)
      (by simp [layout.node.REPROGRAM]))), mem_wr_ne' aA aI (Ne.symm (tcb_node_ne hN F3.ct ht' (K := 3592#u64)
      (by simp) (by rw [act_val]; omega)))]
    exact hinq
  · unfold LawfulStore.actionW
    rw [wY.2.1, nodeAt_of_ksb wY.1, e6', mem_wr_ne' aR aA hRA, L.mem_wr_same aA]

/-- **`check_budget` with an insufficient budget is `charge_budget`** (with `cto = true`). -/
theorem check_budget_ins {A : Type} (ar : machine.Arch A) {s s2 : S} {a a2 : A} {x : Bool}
    (hins : ∀ c, sched.consumed st s = ok c → sporadic.sufficient st ar s a (L.cscW s) c = ok false)
    (h : sched.check_budget st ar s a = ok (x, s2, a2)) :
    ∃ c, sched.consumed st s = ok c ∧ sched.charge_budget st ar s a c true = ok (s2, a2) := by
  have esc : sched.cur_sc st s = ok (L.cscW s) := eq_of_spec_fd (sched.cur_sc.spec (L := L) s)
  unfold sched.check_budget at h
  rw [esc] at h
  simp only [bind_ok] at h
  obtain ⟨c, ec, h⟩ := bind_eq_ok h
  rw [hins c ec] at h
  simp only [bind_ok, Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨⟨s', a'⟩, e, h⟩ := bind_eq_ok h
  have e' := ok_inj_ff h
  simp only [Prod.mk.injEq] at e'
  obtain ⟨-, rfl, rfl⟩ := e'
  exact ⟨c, ec, e⟩

end run

end Fl4Proofs.P2
