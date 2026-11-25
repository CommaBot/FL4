/-
# P2 (p2lf): ready-queue `dequeue` and `enqueue` of a local thread, on the guarded store

On any store `gS` answering `R` reads and `W` writes as `st`:

* `sched.dequeue.guardG`: `dequeue` of a queued thread `t` of this core from any position of its ready queue: its
  queue flags, affinity, domain and priority, the queue words, `tcbqueue.remove` (its links and its neighbours'),
  the bitmap when the queue empties;
* `sched.enqueue.guard_local`: `enqueue` (a `prepend`) of a thread `t` of this core, as p2lt's
  `sched.append.guard_local` with the old head's `prev` link for the old tail's `next` link (`tq_prepend_empty` /
  `tq_prepend_ne`: what `tcbqueue.prepend` on the `sched` links writes).

No named premises.
-/
import Fl4Proofs.P2.FootTimerFireQ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (RdBitmap bind_guard_congr)

section law
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

theorem removeF_kc (s : S) (l : tcbqueue.Link) (q : tcbqueue.Queue) (t : U64) :
    L.ksb (removeF st s l q t).2 = L.ksb s ∧ L.cpu (removeF st s l q t).2 = L.cpu s := by
  unfold removeF
  by_cases h1 : q.head = t <;> by_cases h2 : q.end = t <;> simp [h1, h2, L.ksb_wr, L.cpu_wr]

/-- `tcbqueue.prepend` on the `sched` links to an empty queue. -/
theorem tq_prepend_empty {X Y : S} {q q1 : tcbqueue.Queue} {t : U64} (hq : q.head = 0#u64)
    (h : tcbqueue.prepend st X tcbqueue.Link.Sched q t = ok (q1, Y)) :
    q1 = { head := t, «end» := t } ∧
      Y = L.wr (L.wr X (nextA .Sched t) 0#u64) (prevA .Sched t) 0#u64 := by
  unfold tcbqueue.prepend tcbqueue.Queue.is_empty at h
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

/-- `tcbqueue.prepend` on the `sched` links to a nonempty queue. -/
theorem tq_prepend_ne {X Y : S} {q q1 : tcbqueue.Queue} {t : U64} (hq : q.head ≠ 0#u64)
    (h : tcbqueue.prepend st X tcbqueue.Link.Sched q t = ok (q1, Y)) :
    q1 = { q with head := t } ∧
      Y = L.wr (L.wr (L.wr X (nextA .Sched t) q.head) (prevA .Sched t) 0#u64) (prevA .Sched q.head) t := by
  unfold tcbqueue.prepend tcbqueue.Queue.is_empty at h
  rw [is_null_ok] at h
  simp only [bind_ok] at h
  rw [if_neg (by simpa using hq)] at h
  rw [eq_of_spec_fd (tcbqueue.set_next.spec (L := L) X _ _ _)] at h
  simp only [bind_ok] at h
  rw [eq_of_spec_fd (tcbqueue.set_prev.spec (L := L) _ _ t _)] at h
  simp only [bind_ok] at h
  rw [eq_of_spec_fd (tcbqueue.set_prev.spec (L := L) _ _ _ _)] at h
  simp only [bind_ok] at h
  have e := ok_inj_ff h
  simp only [Prod.mk.injEq] at e
  exact ⟨e.1.symm, e.2.symm⟩

end law

section gst
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]

set_option maxHeartbeats 4000000 in
/-- **`dequeue` of a queued thread of this core** (module docstring). -/
theorem sched.dequeue.guardG (s : S) (t : U64) (hp : (L.mem s (prioA t)).val < 256)
    (haff : L.mem s (affA t) = L.cpu s) (hq : (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64)
    (rI : R (inqA t)) (wI : W (inqA t)) (rA : R (affA t)) (rD : R (domA t)) (rP : R (prioA t))
    (rH : R (L.nodeAt s (L.cpu s) (rqOff (L.mem s (prioA t)))))
    (wH : W (L.nodeAt s (L.cpu s) (rqOff (L.mem s (prioA t)))))
    (rE : R (L.nodeAt s (L.cpu s) (rqTailOff (L.mem s (prioA t)))))
    (wE : W (L.nodeAt s (L.cpu s) (rqTailOff (L.mem s (prioA t)))))
    (bR : RdBitmap (L := L) R s) (bW1 : W (L.nodeAt s (L.cpu s) l1Off))
    (bW2 : ∀ inv : U64, inv.val < 4 → W (L.nodeAt s (L.cpu s) (w64 (136 + 8 * inv.val))))
    (rN : R (nextA .Sched t)) (rPv : R (prevA .Sched t)) (wN : W (nextA .Sched t)) (wPv : W (prevA .Sched t))
    (wPn : L.mem s (L.nodeAt s (L.cpu s) (rqTailOff (L.mem s (prioA t)))) ≠ t →
      W (prevA .Sched (L.mem s (nextA .Sched t))))
    (wNp : L.mem s (L.nodeAt s (L.cpu s) (rqOff (L.mem s (prioA t)))) ≠ t →
      W (nextA .Sched (L.mem s (prevA .Sched t)))) :
    sched.dequeue gS s t = sched.dequeue st s t := by
  have hqd : sched.queued st s t = ok true := by
    rw [eq_of_spec_fd (sched.queued.spec (L := L) s t)]; simp [hq]
  unfold sched.dequeue
  rw [PathObl.sched.queued.guard (gS := gS) s t rI, hqd]
  simp only [bind_ok, ↓reduceIte]
  rw [PathObl.obj.Tcb.affinity.guard (gS := gS) t s rA, aff_ok, haff, PathObl.obj.Tcb.domain.guard (gS := gS) t s rD,
    PathObl.obj.Tcb.prio.guard (gS := gS) t s rP, eq_of_spec_fd (obj.Tcb.prio.spec (L := L) s t)]
  simp only [bind_ok]
  refine bind_guard_congr rfl fun dom _ => ?_
  obtain ⟨off, hoff, ho1, ho2⟩ := spec_ex_fd (sched.rq_head_off.spec dom _ hp)
  rw [hoff]
  simp only [bind_ok]
  subst ho1
  rw [sched.q_get.guard (gS := gS) s _ _ rH (by rw [ho2]; exact rE), eq_of_spec_fd (sched.q_get.spec (L := L) s _ _), ho2]
  simp only [bind_ok]
  refine bind_guard_congr (tcbqueue.remove.guardL (gS := gS) s _ _ t rPv rN wPn wNp wN wPv) fun x ex => ?_
  obtain ⟨q1, s1⟩ := x
  simp only [Aeneas.Std.uncurry_apply_pair]
  have ex' := PathObl.post_of_ok (tcbqueue.remove.eq (L := L) s _ _ t) ex
  have k1 : L.ksb s1 = L.ksb s := by
    rw [show s1 = (removeF st s _ _ t).2 from congrArg Prod.snd ex']; exact (removeF_kc s _ _ t).1
  rw [sched.q_set.guard (gS := gS) _ _ _ _ (by rw [nodeAt_of_ksb k1]; exact wH)
    (by rw [nodeAt_of_ksb k1, ho2]; exact wE)]
  refine bind_guard_congr rfl fun s3 e3 => ?_
  rw [eq_of_spec_fd (sched.q_set.spec (L := L) _ _ _ _)] at e3
  have e3' := ok_inj_ff e3
  subst e3'
  rw [sched.set_flag.guard (gS := gS) _ t _ _ rI wI]
  refine bind_guard_congr rfl fun s4 e4 => ?_
  rw [eq_of_spec_fd (sched.set_flag.spec (L := L) _ t _ _)] at e4
  have e4' := ok_inj_ff e4
  subst e4'
  simp only [tcbqueue.Queue.is_empty, is_null_ok, bind_ok]
  refine ite_congr rfl (fun _ => ?_) (fun _ => rfl)
  exact sched.remove_from_bitmap.guard (gS := gS) _ _ _ _ (by simp only [nodeAt_wr]; rw [nodeAt_of_ksb k1]; exact bR.1)
    (fun inv hi => by simp only [nodeAt_wr]; rw [nodeAt_of_ksb k1]; exact bR.2 inv hi)
    (by simp only [nodeAt_wr]; rw [nodeAt_of_ksb k1]; exact bW1)
    (fun inv hi => by simp only [nodeAt_wr]; rw [nodeAt_of_ksb k1]; exact bW2 inv hi)

set_option maxHeartbeats 4000000 in
/-- **`enqueue` (a `prepend`) of a thread of this core** (module docstring). -/
theorem sched.enqueue.guard_local {T : Set U64} (s : S) (t : U64) (hT : TcbPlaced T) (htT : t ∈ T)
    (hN : NodePlaced st T s (L.cpu s)) (hp : (L.mem s (prioA t)).val < 256) (haff : L.mem s (affA t) = L.cpu s)
    (hE : L.mem s (L.nodeAt s (L.cpu s) (rqOff (L.mem s (prioA t)))) ≠ 0#u64 →
      L.mem s (L.nodeAt s (L.cpu s) (rqOff (L.mem s (prioA t)))) ∈ T)
    (rI : R (inqA t)) (wI : W (inqA t)) (rA : R (affA t)) (rD : R (domA t)) (rP : R (prioA t))
    (rH : R (L.nodeAt s (L.cpu s) (rqOff (L.mem s (prioA t)))))
    (wH : W (L.nodeAt s (L.cpu s) (rqOff (L.mem s (prioA t)))))
    (rE : R (L.nodeAt s (L.cpu s) (rqTailOff (L.mem s (prioA t)))))
    (wE : W (L.nodeAt s (L.cpu s) (rqTailOff (L.mem s (prioA t)))))
    (bR : RdBitmap (L := L) R s) (bW1 : W (L.nodeAt s (L.cpu s) l1Off))
    (bW2 : ∀ inv : U64, inv.val < 4 → W (L.nodeAt s (L.cpu s) (w64 (136 + 8 * inv.val))))
    (wN : W (nextA .Sched t)) (wP : W (prevA .Sched t))
    (wEn : L.mem s (L.nodeAt s (L.cpu s) (rqOff (L.mem s (prioA t)))) ≠ 0#u64 →
      W (prevA .Sched (L.mem s (L.nodeAt s (L.cpu s) (rqOff (L.mem s (prioA t))))))) :
    sched.enqueue gS s t = sched.enqueue st s t := by
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
  unfold sched.enqueue
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
    rw [tcbqueue.prepend.guardL (gS := gS) _ _ _ t wN wP (fun h => (h (by simp [hH0])).elim)]
    refine bind_guard_congr rfl fun x ex => ?_
    obtain ⟨q1, s2⟩ := x
    simp only [Aeneas.Std.uncurry_apply_pair]
    obtain ⟨rfl, rfl⟩ := tq_prepend_empty (by simp [hH0]) ex
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
    refine bind_guard_congr (tcbqueue.prepend.guardL (gS := gS) _ _ _ t wN wP (fun _ => by exact wEn hH0)) fun x ex => ?_
    obtain ⟨q1, s2⟩ := x
    simp only [Aeneas.Std.uncurry_apply_pair]
    obtain ⟨rfl, rfl⟩ := tq_prepend_ne (by exact hH0) ex
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
    have aNe : Aligned (prevA .Sched (L.mem s (L.nodeAt s (L.cpu s) (rqOff (L.mem s (prioA t)))))) :=
      field_aligned (K := 3488#u64) (hT _ hET) (by simp) (by simp)
    have nNe : prevA .Sched (L.mem s (L.nodeAt s (L.cpu s) (rqOff (L.mem s (prioA t))))) ≠ affA t :=
      tA _ 3488#u64 hET (by simp) (fun _ => by simp)
    refine smp.remote_queue_update.guard_local _ t rA ?_
    simp only [nodeAt_wr, LawfulStore.cpu_wr, ho2]
    rw [kA _ _ _ aI nI, kA _ _ _ (aN _ hoT hoT8) (nA _ hoT), kA _ _ _ (aN _ ho ho8) (nA _ ho), kA _ _ _ aNe nNe,
      kA _ _ _ aPv nPv, kA _ _ _ aNx nNx]
    exact haff

end gst

end Fl4Proofs.P2
