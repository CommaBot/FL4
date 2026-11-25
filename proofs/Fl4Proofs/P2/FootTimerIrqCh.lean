/-
# P2: `schedule`'s choose-new path, on the guarded store

The round-robin case of the timer interrupt ends its current thread's timeslice (the thread is appended to its
ready queue, the action becomes `CHOOSE_NEW`), and `schedule` then picks the thread again: `enqueue` of the
(queued) current thread does nothing, `choose_thread` reads the bitmap, takes the head of the highest ready
queue, and `switch_to_thread` sets the VM root, dequeues it (here: the only thread of its queue) and makes it
current; then `schedule`'s tail with the action `RESUME_CURRENT` (`PathObl.LT.schedRes`).

On any store `gS` answering `R` reads and `W` writes as `st` (`PathObl.GRd` / `PathObl.GWr`):

* `tcbqueue.remove.guard_single`, `tq_remove_single`: removing the only thread of a `sched` queue reads its links
  and clears them;
* `sched.remove_from_bitmap.guard` (one domain: an `L2` word, then `L1`);
* `sched.dequeue.guard_single`: a queued thread of this core, alone in its ready queue;
* `sched.switch_to_thread.guard` (`set_vm_root`'s words `RdVm`, then `dequeue` via `hdq`, then `CUR_THREAD`);
* `sched.choose_thread.guard_ne` (`L1 ≠ 0`; the bitmap, the highest queue's words, then `switch_to_thread` of its
  head via `hq`); `sched.schedule_choose_new_thread.guard` (`DOMAIN_TIME ≠ 0`);
* `schedule_choose_eq` (any store) and **`sched.schedule.guard_choose`**: nothing due, the action `CHOOSE_NEW`, the
  current thread schedulable and queued; then the choose path (`hcn`) and `schedRes` at its end state (`hres`).

No named premises.
-/
import Fl4Proofs.P2.FootTimerIrqApp
import Fl4Proofs.P2.AccessVm
import Fl4Proofs.P1.QueueVsFin
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (RdBitmap bind_guard_congr)

section law
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- `tcbqueue.remove` on the `sched` links of the only thread of a queue. -/
theorem tq_remove_single {X Y : S} {q q1 : tcbqueue.Queue} {t : U64} (hH : q.head = t) (hE : q.end = t)
    (h : tcbqueue.remove st X tcbqueue.Link.Sched q t = ok (q1, Y)) :
    q1 = { head := 0#u64, «end» := 0#u64 } ∧
      Y = L.wr (L.wr X (nextA .Sched t) 0#u64) (prevA .Sched t) 0#u64 := by
  have b1 : obj.Tcb.Insts.CoreCmpPartialEqTcb.eq q.head t = ok true := by
    rw [eq_of_spec_fd (obj.Tcb.eq.spec _ _), hH]; simp
  have b2 : obj.Tcb.Insts.CoreCmpPartialEqTcb.eq q.end t = ok true := by
    rw [eq_of_spec_fd (obj.Tcb.eq.spec _ _), hE]; simp
  unfold tcbqueue.remove at h
  rw [eq_of_spec_fd (tcbqueue.prev.spec (L := L) X _ t), eq_of_spec_fd (tcbqueue.next.spec (L := L) X _ t)] at h
  simp only [bind_ok] at h
  rw [b1, b2] at h
  simp only [bind_ok, ↓reduceIte, tcbqueue.Queue.empty, Aeneas.Std.uncurry_apply_pair] at h
  rw [eq_of_spec_fd (tcbqueue.set_next.spec (L := L) X _ t _)] at h
  simp only [bind_ok] at h
  rw [eq_of_spec_fd (tcbqueue.set_prev.spec (L := L) _ _ t _)] at h
  simp only [bind_ok] at h
  have e := ok_inj_ff h
  simp only [Prod.mk.injEq] at e
  exact ⟨e.1.symm, e.2.symm⟩

end law

section gst
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]

theorem tcbqueue.prev.guard_sched (X : S) (t : U64) (h : R (prevA .Sched t)) :
    tcbqueue.prev gS X tcbqueue.Link.Sched t = tcbqueue.prev st X tcbqueue.Link.Sched t := by
  unfold tcbqueue.prev
  exact PathObl.obj.Tcb.sched_prev.guard (gS := gS) t X h

theorem tcbqueue.next.guard_sched (X : S) (t : U64) (h : R (nextA .Sched t)) :
    tcbqueue.next gS X tcbqueue.Link.Sched t = tcbqueue.next st X tcbqueue.Link.Sched t := by
  unfold tcbqueue.next
  exact PathObl.obj.Tcb.sched_next.guard (gS := gS) t X h

/-- **`tcbqueue.remove` of the only thread of a `sched` queue**: reads and clears its links. -/
theorem tcbqueue.remove.guard_single (X : S) (q : tcbqueue.Queue) (t : U64) (hH : q.head = t) (hE : q.end = t)
    (r1 : R (prevA .Sched t)) (r2 : R (nextA .Sched t)) (w1 : W (nextA .Sched t)) (w2 : W (prevA .Sched t)) :
    tcbqueue.remove gS X tcbqueue.Link.Sched q t = tcbqueue.remove st X tcbqueue.Link.Sched q t := by
  have b1 : obj.Tcb.Insts.CoreCmpPartialEqTcb.eq q.head t = ok true := by
    rw [eq_of_spec_fd (obj.Tcb.eq.spec _ _), hH]; simp
  have b2 : obj.Tcb.Insts.CoreCmpPartialEqTcb.eq q.end t = ok true := by
    rw [eq_of_spec_fd (obj.Tcb.eq.spec _ _), hE]; simp
  unfold tcbqueue.remove
  rw [tcbqueue.prev.guard_sched (gS := gS) X t r1, tcbqueue.next.guard_sched (gS := gS) X t r2]
  refine bind_guard_congr rfl fun i _ => ?_
  refine bind_guard_congr rfl fun i1 _ => ?_
  rw [b1, b2]
  simp only [bind_ok, ↓reduceIte]
  refine bind_guard_congr rfl fun x _ => ?_
  obtain ⟨s1, r⟩ := x
  simp only [Aeneas.Std.uncurry_apply_pair]
  rw [tcbqueue.set_next.guard_sched (gS := gS) s1 t _ w1]
  refine bind_guard_congr rfl fun s2 _ => ?_
  rw [tcbqueue.set_prev.guard_sched (gS := gS) s2 t _ w2]

/-- **`remove_from_bitmap`** (one domain), on the node of core `c`: an `L2` word, then `L1`. -/
theorem sched.remove_from_bitmap.guard (X : S) (c dom prio : U64) (h1 : R (L.nodeAt X c l1Off))
    (h2 : ∀ inv : U64, inv.val < 4 → R (L.nodeAt X c (w64 (136 + 8 * inv.val))))
    (w1 : W (L.nodeAt X c l1Off)) (w2 : ∀ inv : U64, inv.val < 4 → W (L.nodeAt X c (w64 (136 + 8 * inv.val)))) :
    sched.remove_from_bitmap gS X c dom prio = sched.remove_from_bitmap st X c dom prio := by
  unfold sched.remove_from_bitmap
  simp only [bitmap_dom_one, lift, bind_ok]
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
  rw [PathObl.eq_ok_of_spec (l2_off_zero inv hlt)]
  simp only [bind_ok]
  rw [PathObl.obj.node_get.guard (gS := gS) X _ _ (h2 inv hlt)]
  refine bind_guard_congr rfl fun v2 _ => ?_
  refine bind_guard_congr rfl fun i4 _ => ?_
  rw [PathObl.obj.node_set.guard (gS := gS) X _ _ _ (w2 inv hlt)]
  refine bind_guard_congr rfl fun s1 e1 => ?_
  rw [eq_of_spec_fd (obj.node_set.spec (L := L) X _ _ _)] at e1
  rw [← ok_inj_ff e1]
  refine ite_congr rfl (fun _ => ?_) (fun _ => rfl)
  rw [PathObl.eq_ok_of_spec l1_off_zero]
  simp only [bind_ok]
  rw [PathObl.obj.node_get.guard (gS := gS) _ _ _ (by rw [nodeAt_wr]; exact h1)]
  refine bind_guard_congr rfl fun v1 _ => ?_
  refine bind_guard_congr rfl fun i8 _ => ?_
  exact PathObl.obj.node_set.guard (gS := gS) _ _ _ _ (by rw [nodeAt_wr]; exact w1)

set_option maxHeartbeats 4000000 in
/-- **`dequeue` of a queued thread of this core that is alone in its ready queue**: its queue flags, affinity,
domain, priority and `sched` links, the queue's words and the bitmap. -/
theorem sched.dequeue.guard_single (s : S) (t : U64) (hp : (L.mem s (prioA t)).val < 256)
    (haff : L.mem s (affA t) = L.cpu s) (hq : (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64)
    (hH : L.mem s (L.nodeAt s (L.cpu s) (rqOff (L.mem s (prioA t)))) = t)
    (hE : L.mem s (L.nodeAt s (L.cpu s) (rqTailOff (L.mem s (prioA t)))) = t)
    (rI : R (inqA t)) (wI : W (inqA t)) (rA : R (affA t)) (rD : R (domA t)) (rP : R (prioA t))
    (rH : R (L.nodeAt s (L.cpu s) (rqOff (L.mem s (prioA t)))))
    (wH : W (L.nodeAt s (L.cpu s) (rqOff (L.mem s (prioA t)))))
    (rE : R (L.nodeAt s (L.cpu s) (rqTailOff (L.mem s (prioA t)))))
    (wE : W (L.nodeAt s (L.cpu s) (rqTailOff (L.mem s (prioA t)))))
    (bR : RdBitmap (L := L) R s) (bW1 : W (L.nodeAt s (L.cpu s) l1Off))
    (bW2 : ∀ inv : U64, inv.val < 4 → W (L.nodeAt s (L.cpu s) (w64 (136 + 8 * inv.val))))
    (rN : R (nextA .Sched t)) (rPv : R (prevA .Sched t)) (wN : W (nextA .Sched t)) (wPv : W (prevA .Sched t)) :
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
  refine bind_guard_congr (tcbqueue.remove.guard_single (gS := gS) s _ t (by exact hH) (by exact hE) rPv rN wN wPv)
    fun x ex => ?_
  obtain ⟨q1, s1⟩ := x
  simp only [Aeneas.Std.uncurry_apply_pair]
  obtain ⟨rfl, rfl⟩ := tq_remove_single (by exact hH) (by exact hE) ex
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
  simp only [tcbqueue.Queue.is_empty, is_null_ok, bind_ok]
  refine ite_congr rfl (fun _ => ?_) (fun _ => rfl)
  exact sched.remove_from_bitmap.guard (gS := gS) _ _ _ _ (by simp only [nodeAt_wr]; exact bR.1)
    (fun inv hi => by simp only [nodeAt_wr]; exact bR.2 inv hi) (by simp only [nodeAt_wr]; exact bW1)
    (fun inv hi => by simp only [nodeAt_wr]; exact bW2 inv hi)

/-- **`switch_to_thread t`**: `set_vm_root`'s words, then `dequeue` (`hdq`), then the node's `CUR_THREAD`. -/
theorem sched.switch_to_thread.guard {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (t : U64) (hRV : PathObl.RdVm (L := L) R s t)
    (hdq : sched.dequeue gS s t = sched.dequeue st s t)
    (hct : ∀ s2, sched.dequeue st s t = ok s2 → W (L.nodeAt s2 (L.cpu s2) layout.node.CUR_THREAD)) :
    sched.switch_to_thread gS ar s a t = sched.switch_to_thread st ar s a t := by
  unfold sched.switch_to_thread
  rw [PathObl.vspace.set_vm_root.guard (gS := gS) ar s a t hRV]
  refine bind_guard_congr rfl fun p1 h1 => ?_
  obtain ⟨Yv, a1⟩ := p1
  have e1 := PathObl.post_of_ok (vspace.set_vm_root.same hA s a t) h1
  simp only at e1
  subst Yv
  simp only [Aeneas.Std.uncurry_apply_pair]
  rw [hdq]
  refine bind_guard_congr rfl fun s2 h2 => ?_
  rw [PathObl.sched.set_cur_thread.guard (gS := gS) s2 t (hct s2 h2)]

/-- **`choose_thread` with a nonempty bitmap**: `L1`, `highest_prio`'s words, the highest queue's words, then
`switch_to_thread` of its head (`hq`). -/
theorem sched.choose_thread.guard_ne {A : Type} (ar : machine.Arch A) (s : S) (a : A)
    (hb : RdBitmap (L := L) R s) (h0 : L.mem s (L.nodeAt s (L.cpu s) l1Off) ≠ 0#u64)
    (hq : ∀ p, sched.highest_prio st s 0#u64 = ok p → p.val < 256 ∧
      R (L.nodeAt s (L.cpu s) (rqOff p)) ∧ R (L.nodeAt s (L.cpu s) (rqTailOff p)) ∧
      sched.switch_to_thread gS ar s a (L.mem s (L.nodeAt s (L.cpu s) (rqOff p))) =
        sched.switch_to_thread st ar s a (L.mem s (L.nodeAt s (L.cpu s) (rqOff p)))) :
    sched.choose_thread gS ar s a = sched.choose_thread st ar s a := by
  unfold sched.choose_thread
  rw [if_neg num_domains_one, if_neg num_domains_one]
  simp only [bind_ok, PathObl.LT.gcc, L.cur_cpu_eq, bitmap_dom_one]
  rw [PathObl.eq_ok_of_spec l1_off_zero]
  simp only [bind_ok]
  rw [PathObl.obj.node_get.guard (gS := gS) s _ _ hb.1, node_get_ok]
  simp only [bind_ok]
  rw [if_pos (bne_iff_ne.2 h0), if_pos (bne_iff_ne.2 h0), PathObl.sched.highest_prio.guard (gS := gS) s _ hb]
  refine bind_guard_congr rfl fun p hp => ?_
  obtain ⟨hp1, r1, r2, hsw⟩ := hq p hp
  obtain ⟨off, hoff, ho1, ho2⟩ := spec_ex_fd (sched.rq_head_off.spec 0#u64 _ hp1)
  rw [hoff]
  simp only [bind_ok]
  subst ho1
  rw [sched.q_get.guard (gS := gS) s _ _ r1 (by rw [ho2]; exact r2), eq_of_spec_fd (sched.q_get.spec (L := L) s _ _)]
  simp only [bind_ok]
  exact hsw

/-- **`schedule_choose_new_thread` with domain time left**: `DOMAIN_TIME`, then `choose_thread` (`hch`). -/
theorem sched.schedule_choose_new_thread.guard {A : Type} (ar : machine.Arch A) (s : S) (a : A)
    (hdt : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME))
    (hd0 : L.mem s (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME) ≠ 0#u64)
    (hch : sched.choose_thread gS ar s a = sched.choose_thread st ar s a) :
    sched.schedule_choose_new_thread gS ar s a = sched.schedule_choose_new_thread st ar s a := by
  unfold sched.schedule_choose_new_thread
  rw [PathObl.sched.domain_time.guard (gS := gS) s hdt, domain_time_eq]
  simp only [bind_ok]
  rw [if_neg hd0, if_neg hd0]
  simp only [bind_ok]
  exact hch

omit L in
/-- `schedule` with nothing due, the action `CHOOSE_NEW` and a schedulable, queued current thread, on any store:
the choose-new path, then `schedRes`. -/
theorem schedule_choose_eq {A : Type} (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A) (ct : U64)
    (haw : sched.awaken m ar s a = ok (s, a))
    (hac : sched.action m s = ok sched.ACTION_CHOOSE_NEW)
    (hct : sched.cur_thread m s = ok ct)
    (hsc : sched.is_schedulable m s ct = ok true)
    (hq : sched.queued m s ct = ok true) :
    sched.schedule m ar s a = (do
      let (s3, a2) ← sched.schedule_choose_new_thread m ar s a
      PathObl.LT.schedRes m ar s3 a2) := by
  have henq : sched.enqueue m s ct = ok s := by
    unfold sched.enqueue
    rw [hq]
    simp only [bind_ok, ↓reduceIte]
  unfold sched.schedule
  rw [haw]; simp only [bind_ok, Aeneas.Std.uncurry_apply_pair]
  rw [PathObl.LT.check_domain_time_any]; simp only [bind_ok]
  rw [hac]; simp only [bind_ok, cn_bne_resume, ↓reduceIte]
  rw [hct]; simp only [bind_ok]
  rw [hsc]; simp only [bind_ok, ↓reduceIte]
  rw [henq]; simp only [bind_ok]
  rfl

/-- **`schedule` with nothing due and the action `CHOOSE_NEW`** (module docstring): `awaken` as in
`sched.schedule.guard_nodue`, the action, the current thread's schedulability and queue flags, then the choose-new
path (`hcn`) and `schedRes` at every state it ends in (`hres`). -/
theorem sched.schedule.guard_choose {A : Type} (ar : machine.Arch A) (s : S) (a : A)
    (hNd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s (L.cpu s) o) ∧ W (L.nodeAt s (L.cpu s) o))
    (hd : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64 →
      R (tdA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))))
    (hT : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) = 0#u64 ∨
      L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_TIME) <
        L.mem s (tdA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))))
    (h2 : L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) ≠ 0#u64 →
      R (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD))) ∧
      PathObl.RdHead (L := L) R s (L.mem s (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD)))))
    (hRel : L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) = 0#u64 ∨
      ¬ ((L.refill s (L.mem s (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD))))
          (L.rhead s (L.mem s (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD)))))).time ≤
        L.curTime s))
    (ha : L.actionW s = sched.ACTION_CHOOSE_NEW)
    (rS : R (stA (L.curW s))) (rC : R (scA (L.curW s))) (rM : R (maxA (L.mem s (scA (L.curW s)))))
    (rI : R (inqA (L.curW s)))
    (hsch : sched.is_schedulable st s (L.curW s) = ok true)
    (hq : (L.mem s (inqA (L.curW s)) &&& sched.Q_QUEUED) ≠ 0#u64)
    (hcn : sched.schedule_choose_new_thread gS ar s a = sched.schedule_choose_new_thread st ar s a)
    (hres : ∀ s3 a2, sched.schedule_choose_new_thread st ar s a = ok (s3, a2) →
      PathObl.LT.schedRes gS ar s3 a2 = PathObl.LT.schedRes st ar s3 a2) :
    sched.schedule gS ar s a = sched.schedule st ar s a := by
  have ct := hNd layout.node.CUR_TIME (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
  have tm := hNd layout.node.TIMER_MIN (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
  have rh := hNd layout.node.RELEASE_HEAD (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
  have sa := hNd layout.node.SCHED_ACTION (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
  have cth := hNd layout.node.CUR_THREAD (by rw [curth_val]; omega) (by rw [curth_val])
  have hac : sched.action st s = ok sched.ACTION_CHOOSE_NEW := by
    rw [eq_of_spec_fd (sched.action.spec (L := L) s), ha]
  have hqd : sched.queued st s (L.curW s) = ok true := by
    rw [eq_of_spec_fd (sched.queued.spec (L := L) s _)]; simp [hq]
  have es := schedule_choose_eq st ar s a (L.curW s) (awaken_none ar s a hT hRel) hac (cur_thread_ok s) hsch hqd
  have haw : sched.awaken gS ar s a = ok (s, a) := by
    unfold sched.awaken
    rw [timer.fire.guard_nodue ar s a ct.1 tm.1 hd hT]
    simp only [bind_ok, bind_tc_ok, Aeneas.Std.uncurry_apply_pair]
    rw [sched.awaken_loop.guard_nodue s _ rh.1 h2 ct.1 hRel]
    simp only [bind_ok, bind_tc_ok]
  have eg := schedule_choose_eq gS ar s a (L.curW s) haw
    (by rw [PathObl.sched.action.guard (gS := gS) s sa.1]; exact hac)
    (by rw [PathObl.sched.cur_thread.guard (gS := gS) s cth.1]; exact cur_thread_ok s)
    (by rw [PathObl.sched.is_schedulable.guard (gS := gS) s _ rS rC rM rI]; exact hsch)
    (by rw [PathObl.sched.queued.guard (gS := gS) s _ rI]; exact hqd)
  rw [eg, es, hcn]
  refine bind_guard_congr rfl fun x hx => ?_
  obtain ⟨s3, a2⟩ := x
  simp only [Aeneas.Std.uncurry_apply_pair]
  exact hres s3 a2 hx

end gst

end Fl4Proofs.P2
