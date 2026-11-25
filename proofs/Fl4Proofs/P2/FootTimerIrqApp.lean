/-
# P2: appending a local thread to its ready queue, on the guarded store

`sched.append.guard_local`: on any store `gS` answering `R` reads and `W` writes as `st` (`PathObl.GRd` /
`PathObl.GWr`), `sched.append` of a thread `t` of the current core (affinity = this core, priority below 256) reads
`t`'s queue flags, affinity, domain and priority, the ready queue's head / tail words (and, when the queue is
empty, the scheduler bitmap), and writes `t`'s `sched` links, the old tail's `next` link (queue not empty), the
queue words, the bitmap (queue empty) and `t`'s queue flags; `remote_queue_update` of a local thread reads only the
affinity (`smp.remote_queue_update.guard_local`: the affinity is kept by the writes before it).

Pieces: `sched.q_get.guard`, `sched.q_set.guard`, `sched.add_to_bitmap.guard` (one domain: `L1` and the four `L2`
words, as p2io's `RdBitmap`), `tcbqueue.append.guard_sched`, `sched.set_flag.guard`; `tq_append_empty` /
`tq_append_ne` (what `tcbqueue.append` on the `sched` links writes).

No named premises.
-/
import Fl4Proofs.P2.FootTimerIrqRR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (RdBitmap bind_guard_congr)

section law
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- `tcbqueue.append` on the `sched` links to an empty queue. -/
theorem tq_append_empty {X Y : S} {q q1 : tcbqueue.Queue} {t : U64} (hq : q.head = 0#u64)
    (h : tcbqueue.append st X tcbqueue.Link.Sched q t = ok (q1, Y)) :
    q1 = { head := t, «end» := t } ∧
      Y = L.wr (L.wr X (nextA .Sched t) 0#u64) (prevA .Sched t) 0#u64 := by
  unfold tcbqueue.append tcbqueue.Queue.is_empty at h
  rw [is_null_ok] at h
  simp only [bind_ok] at h
  rw [if_pos (by simp [hq])] at h
  rw [eq_of_spec_fd (tcbqueue.set_next.spec (L := L) X _ t _)] at h
  simp only [bind_ok] at h
  rw [eq_of_spec_fd (tcbqueue.set_prev.spec (L := L) _ _ t _)] at h
  simp only [bind_ok] at h
  have e := ok_inj_ff h
  simp only [Prod.mk.injEq] at e
  exact ⟨e.1.symm, e.2.symm⟩

/-- `tcbqueue.append` on the `sched` links to a nonempty queue. -/
theorem tq_append_ne {X Y : S} {q q1 : tcbqueue.Queue} {t : U64} (hq : q.head ≠ 0#u64)
    (h : tcbqueue.append st X tcbqueue.Link.Sched q t = ok (q1, Y)) :
    q1 = { q with «end» := t } ∧
      Y = L.wr (L.wr (L.wr X (nextA .Sched q.end) t) (prevA .Sched t) q.end) (nextA .Sched t) 0#u64 := by
  unfold tcbqueue.append tcbqueue.Queue.is_empty at h
  rw [is_null_ok] at h
  simp only [bind_ok] at h
  rw [if_neg (by simpa using hq)] at h
  rw [eq_of_spec_fd (tcbqueue.set_next.spec (L := L) X _ _ _)] at h
  simp only [bind_ok] at h
  rw [eq_of_spec_fd (tcbqueue.set_prev.spec (L := L) _ _ t _)] at h
  simp only [bind_ok] at h
  rw [eq_of_spec_fd (tcbqueue.set_next.spec (L := L) _ _ t _)] at h
  simp only [bind_ok] at h
  have e := ok_inj_ff h
  simp only [Prod.mk.injEq] at e
  exact ⟨e.1.symm, e.2.symm⟩

end law

section gst
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]

theorem sched.q_get.guard (X : S) (c off : U64) (h1 : R (L.nodeAt X c off))
    (h2 : R (L.nodeAt X c (core.num.U64.wrapping_add off 8#u64))) :
    sched.q_get gS X c off = sched.q_get st X c off := by
  unfold sched.q_get
  simp only [lift, bind_ok]
  rw [PathObl.obj.node_get.guard (gS := gS) X c off h1, PathObl.obj.node_get.guard (gS := gS) X c _ h2]

theorem sched.q_set.guard (X : S) (c off : U64) (q : tcbqueue.Queue) (h1 : W (L.nodeAt X c off))
    (h2 : W (L.nodeAt X c (core.num.U64.wrapping_add off 8#u64))) :
    sched.q_set gS X c off q = sched.q_set st X c off q := by
  unfold sched.q_set
  simp only [lift, bind_ok]
  rw [PathObl.obj.node_set.guard (gS := gS) X c off _ h1]
  refine bind_guard_congr rfl fun s1 e1 => ?_
  rw [eq_of_spec_fd (obj.node_set.spec (L := L) X _ _ _)] at e1
  rw [← ok_inj_ff e1]
  exact PathObl.obj.node_set.guard (gS := gS) _ c _ _ (by rw [nodeAt_wr]; exact h2)

theorem sched.set_flag.guard (X : S) (t : obj.Tcb) (f : U64) (v : Bool) (h1 : R (inqA t)) (h2 : W (inqA t)) :
    sched.set_flag gS X t f v = sched.set_flag st X t f v := by
  unfold sched.set_flag
  rw [PathObl.obj.Tcb.in_queues.guard (gS := gS) t X h1]
  refine bind_guard_congr rfl fun q _ => ?_
  cases v
  · simp only [Bool.false_eq_true, ↓reduceIte, lift, bind_ok]
    rw [PathObl.obj.Tcb.set_in_queues.guard (gS := gS) t X _ h2]
  · simp only [↓reduceIte, lift, bind_ok]
    rw [PathObl.obj.Tcb.set_in_queues.guard (gS := gS) t X _ h2]

theorem tcbqueue.set_next.guard_sched (X : S) (t v : U64) (h : W (nextA .Sched t)) :
    tcbqueue.set_next gS X tcbqueue.Link.Sched t v = tcbqueue.set_next st X tcbqueue.Link.Sched t v := by
  unfold tcbqueue.set_next
  exact PathObl.obj.Tcb.set_sched_next.guard (gS := gS) t X v h

theorem tcbqueue.set_prev.guard_sched (X : S) (t v : U64) (h : W (prevA .Sched t)) :
    tcbqueue.set_prev gS X tcbqueue.Link.Sched t v = tcbqueue.set_prev st X tcbqueue.Link.Sched t v := by
  unfold tcbqueue.set_prev
  exact PathObl.obj.Tcb.set_sched_prev.guard (gS := gS) t X v h

/-- **`tcbqueue.append` on the `sched` links**: `t`'s links, and the old tail's `next` when the queue is not
empty. -/
theorem tcbqueue.append.guard_sched (X : S) (q : tcbqueue.Queue) (t : U64) (h1 : W (nextA .Sched t))
    (h2 : W (prevA .Sched t)) (h3 : q.head ≠ 0#u64 → W (nextA .Sched q.end)) :
    tcbqueue.append gS X tcbqueue.Link.Sched q t = tcbqueue.append st X tcbqueue.Link.Sched q t := by
  unfold tcbqueue.append tcbqueue.Queue.is_empty
  rw [is_null_ok]
  simp only [bind_ok]
  by_cases hq : q.head = 0#u64
  · rw [if_pos (by simp [hq]), if_pos (by simp [hq]), tcbqueue.set_next.guard_sched X t _ h1]
    refine bind_guard_congr rfl fun s1 _ => ?_
    rw [tcbqueue.set_prev.guard_sched s1 t _ h2]
  · rw [if_neg (by simpa using hq), if_neg (by simpa using hq), tcbqueue.set_next.guard_sched X _ _ (h3 hq)]
    refine bind_guard_congr rfl fun s1 _ => ?_
    rw [tcbqueue.set_prev.guard_sched s1 t _ h2]
    refine bind_guard_congr rfl fun s2 _ => ?_
    rw [tcbqueue.set_next.guard_sched s2 t _ h1]

/-- **`add_to_bitmap` on this core** (one domain): reads and writes `L1` and an `L2` word. -/
theorem sched.add_to_bitmap.guard (X : S) (dom prio : U64) (h : RdBitmap (L := L) R X)
    (w1 : W (L.nodeAt X (L.cpu X) l1Off))
    (w2 : ∀ inv : U64, inv.val < 4 → W (L.nodeAt X (L.cpu X) (w64 (136 + 8 * inv.val)))) :
    sched.add_to_bitmap gS X (L.cpu X) dom prio = sched.add_to_bitmap st X (L.cpu X) dom prio := by
  obtain ⟨h1, h2⟩ := h
  unfold sched.add_to_bitmap
  simp only [bitmap_dom_one, bind_ok]
  rw [PathObl.eq_ok_of_spec l1_off_zero]
  simp only [lift, bind_ok]
  refine bind_guard_congr rfl fun l1 _ => ?_
  refine bind_guard_congr rfl fun inv hinv => ?_
  have hlt : inv.val < 4 := by
    have ha : (l1 &&& 3#u64).val ≤ 3 := by
      simp only [UScalar.val_and]; exact Nat.and_le_right
    obtain ⟨z, hz, hv⟩ := spec_ex_fd (U64.sub_spec (x := 3#u64) (y := l1 &&& 3#u64) (by scalar_tac))
    rw [hz] at hinv
    have := ok_inj_ff hinv
    subst this
    have h3 : (3#u64 : U64).val = 3 := by simp
    omega
  rw [PathObl.obj.node_get.guard (gS := gS) X _ _ h1]
  refine bind_guard_congr rfl fun v1 _ => ?_
  refine bind_guard_congr rfl fun i3 _ => ?_
  rw [PathObl.obj.node_set.guard (gS := gS) X _ _ _ w1]
  refine bind_guard_congr rfl fun s1 e1 => ?_
  rw [eq_of_spec_fd (obj.node_set.spec (L := L) X _ _ _)] at e1
  rw [← ok_inj_ff e1, PathObl.eq_ok_of_spec (l2_off_zero inv hlt)]
  simp only [bind_ok]
  rw [PathObl.obj.node_get.guard (gS := gS) _ _ _ (by rw [nodeAt_wr]; exact h2 inv hlt)]
  refine bind_guard_congr rfl fun v2 _ => ?_
  refine bind_guard_congr rfl fun i7 _ => ?_
  exact PathObl.obj.node_set.guard (gS := gS) _ _ _ _ (by rw [nodeAt_wr]; exact w2 inv hlt)

/-- **`remote_queue_update` of a local thread**: reads its affinity. -/
theorem smp.remote_queue_update.guard_local (X : S) (t : U64) (h : R (affA t))
    (ha : L.mem X (affA t) = L.cpu X) :
    smp.remote_queue_update gS X t = smp.remote_queue_update st X t := by
  unfold smp.remote_queue_update
  rw [PathObl.obj.Tcb.affinity.guard (gS := gS) t X h, aff_ok, PathObl.gst_cur_cpu (g := gS), L.cur_cpu_eq]
  simp only [bind_ok]
  rw [if_pos ha, if_pos ha]

set_option maxHeartbeats 4000000 in
/-- **`append` of a thread of this core** (module docstring). -/
theorem sched.append.guard_local {T : Set U64} (s : S) (t : U64) (hT : TcbPlaced T) (htT : t ∈ T)
    (hN : NodePlaced st T s (L.cpu s)) (hp : (L.mem s (prioA t)).val < 256) (haff : L.mem s (affA t) = L.cpu s)
    (hE : L.mem s (L.nodeAt s (L.cpu s) (rqOff (L.mem s (prioA t)))) ≠ 0#u64 →
      L.mem s (L.nodeAt s (L.cpu s) (rqTailOff (L.mem s (prioA t)))) ∈ T)
    (rI : R (inqA t)) (wI : W (inqA t)) (rA : R (affA t)) (rD : R (domA t)) (rP : R (prioA t))
    (rH : R (L.nodeAt s (L.cpu s) (rqOff (L.mem s (prioA t)))))
    (wH : W (L.nodeAt s (L.cpu s) (rqOff (L.mem s (prioA t)))))
    (rE : R (L.nodeAt s (L.cpu s) (rqTailOff (L.mem s (prioA t)))))
    (wE : W (L.nodeAt s (L.cpu s) (rqTailOff (L.mem s (prioA t)))))
    (bR : RdBitmap (L := L) R s) (bW1 : W (L.nodeAt s (L.cpu s) l1Off))
    (bW2 : ∀ inv : U64, inv.val < 4 → W (L.nodeAt s (L.cpu s) (w64 (136 + 8 * inv.val))))
    (wN : W (nextA .Sched t)) (wP : W (prevA .Sched t))
    (wEn : L.mem s (L.nodeAt s (L.cpu s) (rqOff (L.mem s (prioA t)))) ≠ 0#u64 →
      W (nextA .Sched (L.mem s (L.nodeAt s (L.cpu s) (rqTailOff (L.mem s (prioA t))))))) :
    sched.append gS s t = sched.append st s t := by
  have ht := hT t htT
  have aA : Aligned (affA t) := field_aligned ht (by simp) (by simp)
  have kA : ∀ (X : S) (b v : U64), Aligned b → b ≠ affA t → L.mem (L.wr X b v) (affA t) = L.mem X (affA t) :=
    fun X b v hb hne => mem_wr_ne' hb aA hne
  have aN : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → Aligned (L.nodeAt s (L.cpu s) o) :=
    fun o ho h8 => nodeAt_aligned hN ho h8
  have nA : ∀ o : U64, o.val < 4288 → L.nodeAt s (L.cpu s) o ≠ affA t := fun o ho e =>
    tcb_node_ne hN htT ht (K := 3520#u64) (by simp) ho e.symm
  have tA : ∀ (y K : U64), y ∈ T → K.val < 4096 → (y = t → K.val ≠ 3520) →
      core.num.U64.wrapping_add y K ≠ affA t :=
    fun y K hy hK hne => tcb_word_ne (hT y hy) ht hK (by simp) (fun e h => hne e (by simpa using h))
  have aI : Aligned (inqA t) := field_aligned ht (by simp) (by simp)
  have nI : inqA t ≠ affA t := tA t 3592#u64 htT (by simp) (fun _ => by simp)
  have aNx : Aligned (nextA .Sched t) := field_aligned (K := 3480#u64) ht (by simp) (by simp)
  have nNx : nextA .Sched t ≠ affA t := tA t 3480#u64 htT (by simp) (fun _ => by simp)
  have aPv : Aligned (prevA .Sched t) := field_aligned (K := 3488#u64) ht (by simp) (by simp)
  have nPv : prevA .Sched t ≠ affA t := tA t 3488#u64 htT (by simp) (fun _ => by simp)
  have ho : (rqOff (L.mem s (prioA t))).val < 4288 := by rw [rqOff_val hp]; omega
  have ho8 : (rqOff (L.mem s (prioA t))).val % 8 = 0 := by rw [rqOff_val hp]; omega
  have hoT : (rqTailOff (L.mem s (prioA t))).val < 4288 := by rw [rqTailOff_val hp]; omega
  have hoT8 : (rqTailOff (L.mem s (prioA t))).val % 8 = 0 := by rw [rqTailOff_val hp]; omega
  unfold sched.append
  rw [PathObl.sched.queued.guard (gS := gS) s t rI]
  refine bind_guard_congr rfl fun b _ => ?_
  cases b
  swap
  · simp only [↓reduceIte]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [PathObl.obj.Tcb.affinity.guard (gS := gS) t s rA, aff_ok, haff, PathObl.obj.Tcb.domain.guard (gS := gS) t s rD,
    PathObl.obj.Tcb.prio.guard (gS := gS) t s rP, eq_of_spec_fd (obj.Tcb.prio.spec (L := L) s t)]
  simp only [bind_ok]
  refine bind_guard_congr rfl fun dom _ => ?_
  obtain ⟨off, hoff, ho1, ho2⟩ := spec_ex_fd (sched.rq_head_off.spec dom _ hp)
  rw [hoff]
  simp only [bind_ok]
  subst ho1
  rw [sched.q_get.guard (gS := gS) s _ _ rH (by rw [ho2]; exact rE), eq_of_spec_fd (sched.q_get.spec (L := L) s _ _), ho2]
  simp only [bind_ok, tcbqueue.Queue.is_empty, is_null_ok]
  by_cases hH0 : L.mem s (L.nodeAt s (L.cpu s) (rqOff (L.mem s (prioA t)))) = 0#u64
  · -- empty queue: the bitmap
    rw [if_pos (by simp [hH0]), if_pos (by simp [hH0]), sched.add_to_bitmap.guard (gS := gS) s dom _ bR bW1 bW2]
    refine bind_guard_congr rfl fun s1 e1 => ?_
    obtain ⟨v1, v2, e1', -, -⟩ := PathObl.post_of_ok (sched.add_to_bitmap.spec (L := L) s _ dom _ hp) e1
    subst e1'
    rw [tcbqueue.append.guard_sched (gS := gS) _ _ t wN wP (fun h => (h (by simp [hH0])).elim)]
    refine bind_guard_congr rfl fun x ex => ?_
    obtain ⟨q1, s2⟩ := x
    simp only [Aeneas.Std.uncurry_apply_pair]
    obtain ⟨rfl, rfl⟩ := tq_append_empty (by simp [hH0]) ex
    rw [sched.q_set.guard (gS := gS) _ _ _ _ (by simp only [nodeAt_wr]; exact wH)
      (by simp only [nodeAt_wr]; rw [ho2]; exact wE)]
    refine bind_guard_congr rfl fun s3 e3 => ?_
    rw [eq_of_spec_fd (sched.q_set.spec (L := L) _ _ _ _)] at e3
    have e3' := ok_inj_ff e3
    subst e3'
    rw [sched.set_flag.guard (gS := gS) _ t _ _ rI wI]
    refine bind_guard_congr rfl fun s4 e4 => ?_
    rw [eq_of_spec_fd (sched.set_flag.spec (L := L) _ t _ _)] at e4
    have e4' := ok_inj_ff e4
    subst e4'
    have hg : (L.mem s (prioA t)).val / 64 < 4 := by omega
    have hl2 : (l2Off ((L.mem s (prioA t)).val / 64)).val < 4288 := by rw [l2Off_val hg]; omega
    have hl28 : (l2Off ((L.mem s (prioA t)).val / 64)).val % 8 = 0 := by rw [l2Off_val hg]; omega
    have hl1 : l1Off.val < 4288 := by rw [l1Off_val]; omega
    have hl18 : l1Off.val % 8 = 0 := by rw [l1Off_val]
    refine smp.remote_queue_update.guard_local _ t rA ?_
    simp only [nodeAt_wr, LawfulStore.cpu_wr, ho2]
    rw [kA _ _ _ aI nI, kA _ _ _ (aN _ hoT hoT8) (nA _ hoT), kA _ _ _ (aN _ ho ho8) (nA _ ho), kA _ _ _ aPv nPv,
      kA _ _ _ aNx nNx, kA _ _ _ (aN _ hl2 hl28) (nA _ hl2), kA _ _ _ (aN _ hl1 hl18) (nA _ hl1)]
    exact haff
  · -- nonempty queue
    rw [if_neg (by simpa using hH0), if_neg (by simpa using hH0)]
    simp only [bind_ok]
    refine bind_guard_congr (tcbqueue.append.guard_sched (gS := gS) _ _ t wN wP (fun _ => by exact wEn hH0)) fun x ex => ?_
    obtain ⟨q1, s2⟩ := x
    simp only [Aeneas.Std.uncurry_apply_pair]
    obtain ⟨rfl, rfl⟩ := tq_append_ne (by exact hH0) ex
    rw [sched.q_set.guard (gS := gS) _ _ _ _ (by simp only [nodeAt_wr]; exact wH)
      (by simp only [nodeAt_wr]; rw [ho2]; exact wE)]
    refine bind_guard_congr rfl fun s3 e3 => ?_
    rw [eq_of_spec_fd (sched.q_set.spec (L := L) _ _ _ _)] at e3
    have e3' := ok_inj_ff e3
    subst e3'
    rw [sched.set_flag.guard (gS := gS) _ t _ _ rI wI]
    refine bind_guard_congr rfl fun s4 e4 => ?_
    rw [eq_of_spec_fd (sched.set_flag.spec (L := L) _ t _ _)] at e4
    have e4' := ok_inj_ff e4
    subst e4'
    have hET := hE hH0
    have aNe : Aligned (nextA .Sched (L.mem s (L.nodeAt s (L.cpu s) (rqTailOff (L.mem s (prioA t)))))) :=
      field_aligned (K := 3480#u64) (hT _ hET) (by simp) (by simp)
    have nNe : nextA .Sched (L.mem s (L.nodeAt s (L.cpu s) (rqTailOff (L.mem s (prioA t))))) ≠ affA t :=
      tA _ 3480#u64 hET (by simp) (fun _ => by simp)
    refine smp.remote_queue_update.guard_local _ t rA ?_
    simp only [nodeAt_wr, LawfulStore.cpu_wr, ho2]
    rw [kA _ _ _ aI nI, kA _ _ _ (aN _ hoT hoT8) (nA _ hoT), kA _ _ _ (aN _ ho ho8) (nA _ ho), kA _ _ _ aNx nNx,
      kA _ _ _ aPv nPv, kA _ _ _ aNe nNe]
    exact haff

end gst

end Fl4Proofs.P2
