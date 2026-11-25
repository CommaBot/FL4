/-
# P2: the round-robin `charge_budget` tail with `end_timeslice` / `append` composed in

`cbTail.guard_rr`: `charge_budget`'s tail (`cbTail`, `P2/FootTimerIrqRR.lean`) on the guarded store, with its
`hend` premise discharged: at the state `end_timeslice` runs in, the facts `RRTail` (the current thread is a
thread of this core with its ready queue related, the SC is round-robin, ready and sufficient, the action is
`RESUME_CURRENT`, and `R` / `W` hold the words `end_timeslice` and `append` read and write) give
`end_timeslice.guard_rr` with `append.guard_local` for its `happ`, and the run's end state keeps the kernel base,
the core and the action (`end_timeslice_rr`: the run is `append`; `append_keep`: `append`'s footprint, P1
`sched.append.foot`, misses the node's `SCHED_ACTION`).

No named premises.
-/
import Fl4Proofs.P2.FootTimerIrqCh
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (RdBitmap RdHead bind_guard_congr)

section law
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)

/-- `end_timeslice` of a round-robin SC that is ready with sufficient budget is `append` of the current
thread. -/
theorem end_timeslice_rr {X Y : S} {a a' : A} (hrr : sporadic.is_round_robin st X (L.cscW X) = ok true)
    (hrd : sporadic.ready st X (L.cscW X) = ok true)
    (hsf : sporadic.sufficient st ar X a (L.cscW X) 0#u64 = ok true)
    (h : sched.end_timeslice st ar X a true = ok (Y, a')) :
    sched.append st X (L.curW X) = ok Y ∧ a' = a := by
  have esc : sched.cur_sc st X = ok (L.cscW X) := eq_of_spec_fd (sched.cur_sc.spec (L := L) X)
  unfold sched.end_timeslice at h
  rw [esc] at h
  simp only [bind_ok] at h
  rw [cur_thread_ok] at h
  simp only [bind_ok] at h
  rw [hrr] at h
  simp only [bind_ok] at h
  obtain ⟨v, -, h⟩ := bind_eq_ok h
  obtain ⟨valid, -, h⟩ := bind_eq_ok h
  simp only [↓reduceIte] at h
  rw [hrd] at h
  simp only [bind_ok, ↓reduceIte] at h
  rw [hsf] at h
  simp only [bind_ok, ↓reduceIte] at h
  obtain ⟨Y1, hY1, h⟩ := bind_eq_ok h
  have e := ok_inj_ff h
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact ⟨hY1, rfl⟩

/-- `append` of a thread of this core keeps the kernel base, the core and the node's `SCHED_ACTION`. -/
theorem append_keep {T : Set U64} {X Y : S} {t : U64} {xs : List U64} (hT : TcbPlaced T) (ht : t ∈ T)
    (hp : (L.mem X (prioA t)).val < 256) (haff : L.mem X (affA t) = L.cpu X)
    (hN : NodePlaced st T X (L.cpu X))
    (hr : QueueRel (L.mem X) T .Sched (L.rqQ X (L.cpu X) (L.mem X (prioA t))) xs)
    (hq : (L.mem X (inqA t) &&& sched.Q_QUEUED) = 0#u64 → t ∉ xs)
    (h : sched.append st X t = ok Y) :
    L.ksb Y = L.ksb X ∧ L.cpu Y = L.cpu X ∧ L.actionW Y = L.actionW X := by
  have hN' : NodePlaced st T X (L.mem X (affA t)) := by rw [haff]; exact hN
  obtain ⟨w, -⟩ := PathObl.post_of_ok
    (sched.append.foot (L := L) X t xs hT ht hp hN' hN (by rw [haff]; exact hr) hq) h
  refine ⟨w.1, w.2.1, ?_⟩
  have ho : layout.node.SCHED_ACTION.val < 4288 := by rw [act_val]; omega
  unfold LawfulStore.actionW
  rw [w.2.1, nodeAt_of_ksb w.1]
  refine w.2.2 _ (nodeAt_aligned hN ho (by rw [act_val])) ?_
  rintro (⟨y, hy, e | e⟩ | ⟨o, ho1, ho2, -, e⟩ | e | ⟨o, ho1, ho2, -, e⟩)
  · have hyT : y ∈ T := by
      obtain rfl | hy' := List.mem_cons.1 hy
      exacts [ht, hr.mem _ hy']
    exact tcb_node_ne hN hyT (hT y hyT) (K := 3480#u64) (by simp) ho e.symm
  · have hyT : y ∈ T := by
      obtain rfl | hy' := List.mem_cons.1 hy
      exacts [ht, hr.mem _ hy']
    exact tcb_node_ne hN hyT (hT y hyT) (K := 3488#u64) (by simp) ho e.symm
  · have h1 : 128 ≤ o.val := ho1
    rw [haff] at e
    have := congrArg UScalar.val e
    rw [nodeAt_val hN ho, nodeAt_val hN ho2, act_val] at this
    omega
  · exact tcb_node_ne hN ht (hT t ht) (K := 3592#u64) (by simp) ho e.symm
  · have h1 : o.val = 120 := ho1
    have := congrArg UScalar.val e
    rw [nodeAt_val hN ho, nodeAt_val hN ho2, act_val] at this
    omega

end law

section defs
variable {S : Type}

/-- What `cbTail.guard_rr` needs at the state `end_timeslice` runs in. -/
structure RRTail (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A) (T : Set U64)
    (R W : U64 → Prop) (X : S) (a : A) : Prop where
  hT : TcbPlaced T
  hN : NodePlaced st T X (L.cpu X)
  ct : L.curW X ∈ T
  prio : (L.mem X (prioA (L.curW X))).val < 256
  aff : L.mem X (affA (L.curW X)) = L.cpu X
  rel : ∃ xs, QueueRel (L.mem X) T .Sched (L.rqQ X (L.cpu X) (L.mem X (prioA (L.curW X)))) xs ∧
    ((L.mem X (inqA (L.curW X)) &&& sched.Q_QUEUED) = 0#u64 → L.curW X ∉ xs)
  tail : L.mem X (L.nodeAt X (L.cpu X) (rqOff (L.mem X (prioA (L.curW X))))) ≠ 0#u64 →
    L.mem X (L.nodeAt X (L.cpu X) (rqTailOff (L.mem X (prioA (L.curW X))))) ∈ T
  rr : sporadic.is_round_robin st X (L.cscW X) = ok true
  rd : sporadic.ready st X (L.cscW X) = ok true
  sf : sporadic.sufficient st ar X a (L.cscW X) 0#u64 = ok true
  act : L.actionW X = sched.ACTION_RESUME_CURRENT
  rCS : R (L.nodeAt X (L.cpu X) layout.node.CUR_SC)
  rCT : R (L.nodeAt X (L.cpu X) layout.node.CUR_THREAD)
  rPer : R (core.num.U64.wrapping_add (L.cscW X) layout.sc.PERIOD)
  rS : R (stA (L.curW X))
  rC : R (scA (L.curW X))
  rM : R (maxA (L.mem X (scA (L.curW X))))
  vt : ∀ sl, obj.Tcb.slot (L.curW X) layout.tcb.SLOT_TIMEOUT_HANDLER = ok sl →
    R sl ∧ R (core.num.U64.wrapping_add sl 8#u64)
  hd : RdHead (L := L) R X (L.cscW X)
  rNow : R (ctA (L := L) X)
  rI : R (inqA (L.curW X))
  wI : W (inqA (L.curW X))
  rA : R (affA (L.curW X))
  rD : R (domA (L.curW X))
  rP : R (prioA (L.curW X))
  rH : R (L.nodeAt X (L.cpu X) (rqOff (L.mem X (prioA (L.curW X)))))
  wH : W (L.nodeAt X (L.cpu X) (rqOff (L.mem X (prioA (L.curW X)))))
  rE : R (L.nodeAt X (L.cpu X) (rqTailOff (L.mem X (prioA (L.curW X)))))
  wE : W (L.nodeAt X (L.cpu X) (rqTailOff (L.mem X (prioA (L.curW X)))))
  bR : RdBitmap (L := L) R X
  bW1 : W (L.nodeAt X (L.cpu X) l1Off)
  bW2 : ∀ inv : U64, inv.val < 4 → W (L.nodeAt X (L.cpu X) (w64 (136 + 8 * inv.val)))
  wN : W (nextA .Sched (L.curW X))
  wP : W (prevA .Sched (L.curW X))
  wEn : L.mem X (L.nodeAt X (L.cpu X) (rqOff (L.mem X (prioA (L.curW X))))) ≠ 0#u64 →
    W (nextA .Sched (L.mem X (L.nodeAt X (L.cpu X) (rqTailOff (L.mem X (prioA (L.curW X)))))))

end defs

section gst
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]

/-- `end_timeslice` under `RRTail` on the guarded store. -/
theorem sched.end_timeslice.guard_rrT {A : Type} (ar : machine.Arch A) {T : Set U64} (X : S) (a : A)
    (F : RRTail st ar T R W X a) :
    sched.end_timeslice gS ar X a true = sched.end_timeslice st ar X a true :=
  sched.end_timeslice.guard_rr (gS := gS) ar X a F.rCS F.rCT F.rPer F.rr F.rS F.vt F.hd F.rNow F.rd F.sf
    (sched.append.guard_local (gS := gS) X (L.curW X) F.hT F.ct F.hN F.prio F.aff F.tail F.rI F.wI F.rA F.rD
      F.rP F.rH F.wH F.rE F.wE F.bR F.bW1 F.bW2 F.wN F.wP F.wEn)

/-- **`charge_budget`'s round-robin tail** with `end_timeslice` and `append` composed in (module docstring):
the node's words at `s2`, and `RRTail` at the state after the node's `CONSUMED` is cleared. -/
theorem cbTail.guard_rr {A : Type} (ar : machine.Arch A) {T : Set U64} (s2 : S) (a : A)
    (hNd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s2 (L.cpu s2) o) ∧ W (L.nodeAt s2 (L.cpu s2) o))
    (F : ∀ s3, sched.set_consumed st s2 0#u64 = ok s3 → RRTail st ar T R W s3 a) :
    cbTail gS ar s2 a true = cbTail st ar s2 a true := by
  refine cbTail.guard (gS := gS) ar s2 a true hNd (fun s3 e3 => ⟨(F s3 e3).rS, (F s3 e3).rC, (F s3 e3).rM,
    (F s3 e3).rI⟩) fun s3 e3 _ => ⟨sched.end_timeslice.guard_rrT (gS := gS) ar s3 a (F s3 e3), ?_⟩
  intro s4 a1 e4
  have F3 := F s3 e3
  have e3' : s3 = L.wr s2 (L.nodeA s2 layout.node.CONSUMED) 0#u64 := by
    have e := e3
    rw [eq_of_spec_fd (sched.set_consumed.spec (L := L) s2 _)] at e
    exact (ok_inj_ff e).symm
  have k3 : L.ksb s3 = L.ksb s2 := by rw [e3', L.ksb_wr]
  have c3 : L.cpu s3 = L.cpu s2 := by rw [e3', LawfulStore.cpu_wr]
  obtain ⟨ea, -⟩ := end_timeslice_rr ar F3.rr F3.rd F3.sf e4
  obtain ⟨xs, hr, hq⟩ := F3.rel
  obtain ⟨k4, c4, a4⟩ := append_keep F3.hT F3.ct F3.prio F3.aff F3.hN hr hq ea
  exact ⟨k4.trans k3, c4.trans c3, a4.trans F3.act⟩

end gst

end Fl4Proofs.P2
