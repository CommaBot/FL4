/-
# P2 (line p3mc, gen 26): the waking tail after `awaken` with the per-class premises asked of homed objects

Handoff §30c (W-h), after P2/IrqWhW, P2/IrqWhA. The switch block (`schedSw_guard`, P2/FootTimerFireSy2) asks
`SwAcc` at the post-`awaken` state `Y`: the words of **every** thread whose `AFFINITY` is the core. It reads only
those of the current thread, the woken thread and members of this core's ready queues, all runnable but the current
thread. Here, by the same text (copied by a script):

* `SwAccH st R W T G Y`: `SwAcc` asked only of threads runnable at `Y` or satisfying `G`; `WH.swacc_mono` (the
  switch block writes no `STATE`); `rq_head_run` / `rq_tail_run` (ready-queue ends are runnable, `runQ`);
* `WH.enq_guard`, `WH.app_guard`, `WH.deq_guard_head`, `WH.sw_guard`, `WH.choose_guard`, **`WH.schedSw_guard`**
  (`G` holds of the current thread: `hgc`);
* **`WH.aw_tail_sw_core`**, **`WH.aw_tail_sw`**: `aw_tail_sw_core` / `aw_tail_sw` (P2/FootTimerFireSy) with `rL` /
  `wL` / `StW` / `hSlot` asked only of threads with `Hm` and `rS` / `wS` only of SCs with `Hs`, given `Hm` of every
  thread runnable at the entry (`hHr`) or with an SC (`hHsc`), and `Hs` of every thread's SC (`hHs`);
* **`WH.fire_tail_wk2`**: `fire_tail_wk2` so restricted, with `hwD` asked only for the due thread, by
  `WH.fire_wk_aw` and `WH.aw_tail_sw` (`aw_resume` unchanged).

No named premises; no existing statement changed.
-/
import Fl4Proofs.P2.IrqWhA
import Fl4Proofs.P2.FootTimerFireSy
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.WH
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2
open Fl4Proofs.P2.OwnMap
open Fl4Proofs.P2.PathObl (ScAcc rhA tmA RdHead NodeSt bind_guard_congr RdBitmap)

section law
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T Cs Ω : Set U64} {H : Heap}
variable {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {G : U64 → Prop}

/-- **`SwAcc` asked of runnable threads and of `G`** (module docstring). -/
def SwAccH (st : machine.Store S) [L : LawfulStore st] (R W : U64 → Prop) (T : Set U64) (G : U64 → Prop) (Y : S) :
    Prop :=
  (∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt Y (L.cpu Y) o) ∧ W (L.nodeAt Y (L.cpu Y) o)) ∧
  (∀ y ∈ T, L.mem Y (affA y) = L.cpu Y → (Runnable (L.mem Y (stA y)) ∨ G y) →
    R (inqA y) ∧ W (inqA y) ∧ R (affA y) ∧ R (domA y) ∧ R (prioA y) ∧
    R (nextA .Sched y) ∧ W (nextA .Sched y) ∧ R (prevA .Sched y) ∧ W (prevA .Sched y) ∧
    R (vtA y) ∧ R (core.num.U64.wrapping_add (vtA y) 8#u64)) ∧
  R (core.num.U64.wrapping_add (L.ksb Y) layout.ks.CUR_DOMAIN) ∧
  R (core.num.U64.wrapping_add (L.ksb Y) layout.ks.DOMAIN_TIME) ∧
  R (krA (L := L) Y) ∧ PathObl.RdTab (L := L) R Y

theorem swacc_mono {R W : U64 → Prop} {Y Z : S} (hq : SchedQueuesInv st T Cs Ω H Y Q Rq)
    (hAt : ∀ hi : U64, hi.val < 2048 → OutsideObjs st T Cs Y (atAF (L.ksb Y) hi))
    (hW : WritesIn st Y Z (SWN st T Y)) (h : SwAccH st R W T G Y) : SwAccH st R W T G Z := by
  have hT := hq.tcbs
  have hN := hq.nodes _ hq.cur
  have eN : ∀ o, L.nodeAt Z (L.cpu Z) o = L.nodeAt Y (L.cpu Y) o := fun o => by
    rw [hW.2.1, nodeAt_of_ksb hW.1]
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨fun o ho h8 => by rw [eN]; exact h1 o ho h8, fun y hy ha hr => h2 y hy ?_ ?_, by rw [hW.1]; exact h3,
    by rw [hW.1]; exact h4, by unfold krA; rw [hW.1]; exact h5, fun hi hhi => ?_⟩
  · have e : L.mem Z (affA y) = L.mem Y (affA y) := by
      unfold affA
      exact hW.mem_eq (field_aligned (hT y hy) (by simp) (by simp))
        (swn_tcb hT hN hy (by simp) (by simp) (by simp) (by simp))
    rw [← e, ha, hW.2.1]
  · have e : L.mem Z (stA y) = L.mem Y (stA y) := by
      rw [stA_eq]
      exact hW.mem_eq (field_aligned (hT y hy) (by simp) (by simp))
        (swn_tcb hT hN hy (by simp) (by simp) (by simp) (by simp))
    rw [← e]; exact hr
  · have e : L.mem Z (atAF (L.ksb Y) hi) = L.mem Y (atAF (L.ksb Y) hi) :=
      hW.mem_eq (hAt hi hhi).1 (swn_out hT hN hq.cur (hAt hi hhi))
    rw [hW.1, e]
    exact h6 hi hhi

/-- A non-null ready-queue head of this core is runnable. -/
theorem rq_head_run {Z : S} (hZ : SchedQueuesInv st T Cs Ω H Z Q Rq) {p : U64} (hp : p.val < 256)
    (h0 : L.mem Z (L.nodeAt Z (L.cpu Z) (rqOff p)) ≠ 0#u64) :
    Runnable (L.mem Z (stA (L.mem Z (L.nodeAt Z (L.cpu Z) (rqOff p))))) :=
  hZ.runQ _ hZ.cur p hp _ (rq_head_info hZ hp h0).2.2.2

/-- The tail of a non-empty ready queue of this core is runnable. -/
theorem rq_tail_run {Z : S} (hZ : SchedQueuesInv st T Cs Ω H Z Q Rq) {p : U64} (hp : p.val < 256)
    (h0 : L.mem Z (L.nodeAt Z (L.cpu Z) (rqOff p)) ≠ 0#u64) :
    Runnable (L.mem Z (stA (L.mem Z (L.nodeAt Z (L.cpu Z) (rqTailOff p))))) := by
  have hr := (hZ.ready _ hZ.cur).1.rel p hp
  have eh : L.mem Z (L.nodeAt Z (L.cpu Z) (rqOff p)) = (Q (L.cpu Z) p).headD 0#u64 := hr.head
  have el : L.mem Z (L.nodeAt Z (L.cpu Z) (rqTailOff p)) = (Q (L.cpu Z) p).getLastD 0#u64 := hr.last
  have hne : Q (L.cpu Z) p ≠ [] := fun e => h0 (by rw [eh, e]; rfl)
  rw [el]
  exact hZ.runQ _ hZ.cur p hp _ (getLastD_mem' hne 0#u64)

end law

section gst
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]
variable {T Cs Ω : Set U64} {H : Heap} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {G : U64 → Prop}

theorem enq_guard {Z : S} (t : U64) (hZ : SchedQueuesInv st T Cs Ω H Z Q Rq) (hacc : SwAccH st R W T G Z)
    (ht : t ∈ T) (ha : L.mem Z (affA t) = L.cpu Z) (hg : Runnable (L.mem Z (stA t)) ∨ G t) :
    sched.enqueue gS Z t = sched.enqueue st Z t := by
  have hT := hZ.tcbs
  have hN := hZ.nodes _ hZ.cur
  have hp := hZ.prio t ht
  obtain ⟨nRW, lRW, -⟩ := hacc
  obtain ⟨rI, wI, rA, rD, rP, -, wN, -, wP, -⟩ := lRW t ht ha hg
  have hpv := rqOff_val hp
  have hpt := rqTailOff_val hp
  refine sched.enqueue.guard_local Z t hT ht hN hp ha (fun h0 => (rq_head_info hZ hp h0).1) rI wI rA rD rP
    (nRW _ (by omega) (by omega)).1 (nRW _ (by omega) (by omega)).2
    (nRW _ (by omega) (by omega)).1 (nRW _ (by omega) (by omega)).2
    ⟨(nRW _ (by rw [l1Off_val]; omega) (by rw [l1Off_val])).1, fun inv hinv => (nRW _ (by simp; omega) (by simp)).1⟩
    (nRW _ (by rw [l1Off_val]; omega) (by rw [l1Off_val])).2 (fun inv hinv => (nRW _ (by simp; omega) (by simp)).2)
    wN wP (fun h0 => ?_)
  obtain ⟨hxT, hxa, -⟩ := rq_head_info hZ hp h0
  exact (lRW _ hxT hxa (Or.inl (rq_head_run hZ hp h0))).2.2.2.2.2.2.2.2.1

theorem app_guard {Z : S} (t : U64) (hZ : SchedQueuesInv st T Cs Ω H Z Q Rq) (hacc : SwAccH st R W T G Z)
    (ht : t ∈ T) (ha : L.mem Z (affA t) = L.cpu Z) (hg : Runnable (L.mem Z (stA t)) ∨ G t) :
    sched.append gS Z t = sched.append st Z t := by
  have hT := hZ.tcbs
  have hN := hZ.nodes _ hZ.cur
  have hp := hZ.prio t ht
  obtain ⟨nRW, lRW, -⟩ := hacc
  obtain ⟨rI, wI, rA, rD, rP, -, wN, -, wP, -⟩ := lRW t ht ha hg
  have hpv := rqOff_val hp
  have hpt := rqTailOff_val hp
  refine sched.append.guard_local Z t hT ht hN hp ha (fun h0 => (rq_tail_info hZ hp h0).1) rI wI rA rD rP
    (nRW _ (by omega) (by omega)).1 (nRW _ (by omega) (by omega)).2
    (nRW _ (by omega) (by omega)).1 (nRW _ (by omega) (by omega)).2
    ⟨(nRW _ (by rw [l1Off_val]; omega) (by rw [l1Off_val])).1, fun inv hinv => (nRW _ (by simp; omega) (by simp)).1⟩
    (nRW _ (by rw [l1Off_val]; omega) (by rw [l1Off_val])).2 (fun inv hinv => (nRW _ (by simp; omega) (by simp)).2)
    wN wP (fun h0 => ?_)
  obtain ⟨hxT, hxa⟩ := rq_tail_info hZ hp h0
  exact (lRW _ hxT hxa (Or.inl (rq_tail_run hZ hp h0))).2.2.2.2.2.2.1

set_option maxHeartbeats 4000000 in
/-- `dequeue` of the head of a ready queue of this core. -/
theorem deq_guard_head {Z : S} (t : U64) (hZ : SchedQueuesInv st T Cs Ω H Z Q Rq) (hacc : SwAccH st R W T G Z)
    (ht : t ∈ T) (ha : L.mem Z (affA t) = L.cpu Z) (hg : Runnable (L.mem Z (stA t)) ∨ G t) {p : U64} (hp : p.val < 256)
    (hpt : L.mem Z (prioA t) = p) (hhd : L.mem Z (L.nodeAt Z (L.cpu Z) (rqOff p)) = t) :
    sched.dequeue gS Z t = sched.dequeue st Z t := by
  subst hpt
  have hT := hZ.tcbs
  obtain ⟨nRW, lRW, -⟩ := hacc
  obtain ⟨rI, wI, rA, rD, rP, rN, wN, rPv, wPv, -⟩ := lRW t ht ha hg
  have hr := (hZ.ready _ hZ.cur).1.rel (L.mem Z (prioA t)) hp
  have eh : L.mem Z (L.nodeAt Z (L.cpu Z) (rqOff (L.mem Z (prioA t)))) = (Q (L.cpu Z) (L.mem Z (prioA t))).headD 0#u64 := hr.head
  have el : L.mem Z (L.nodeAt Z (L.cpu Z) (rqTailOff (L.mem Z (prioA t)))) = (Q (L.cpu Z) (L.mem Z (prioA t))).getLastD 0#u64 := hr.last
  have ht0 : t ≠ 0#u64 := fun e => (hT t ht).ne0 (by rw [e]; rfl)
  have hne : Q (L.cpu Z) (L.mem Z (prioA t)) ≠ [] := fun e => ht0 (by rw [← hhd, eh, e]; rfl)
  obtain ⟨y0, ys, eq⟩ := List.exists_cons_of_ne_nil hne
  have hy0 : y0 = t := by rw [← hhd, eh, eq]; rfl
  subst hy0
  have hmem : y0 ∈ Q (L.cpu Z) (L.mem Z (prioA y0)) := by rw [eq]; exact List.mem_cons_self
  have hpv := rqOff_val hp
  have hptv := rqTailOff_val hp
  refine sched.dequeue.guardG Z y0 hp ha
    ((hZ.queued y0 ht).2 (by rw [ha]; exact hmem)) rI wI rA rD rP
    (nRW _ (by omega) (by omega)).1 (nRW _ (by omega) (by omega)).2
    (nRW _ (by omega) (by omega)).1 (nRW _ (by omega) (by omega)).2
    ⟨(nRW _ (by rw [l1Off_val]; omega) (by rw [l1Off_val])).1, fun inv hinv => (nRW _ (by simp; omega) (by simp)).1⟩
    (nRW _ (by rw [l1Off_val]; omega) (by rw [l1Off_val])).2 (fun inv hinv => (nRW _ (by simp; omega) (by simp)).2)
    rN rPv wN wPv (fun htl => ?_) (fun hh => absurd hhd hh)
  have hrq : QueueRel (L.mem Z) T .Sched (L.rqQ Z (L.cpu Z) (L.mem Z (prioA y0))) (y0 :: ys) := eq ▸ hr
  rw [hrq.head_next]
  have hys : ys ≠ [] := fun e => htl (by rw [el, eq, e]; rfl)
  have hm : ys.headD 0#u64 ∈ Q (L.cpu Z) (L.mem Z (prioA y0)) := by rw [eq]; exact List.mem_cons_of_mem _ (headD_mem hys _)
  exact (lRW _ (hZ.memT hZ.cur hp hm) (hZ.inQ _ hZ.cur (L.mem Z (prioA y0)) hp _ hm).1
    (Or.inl (hZ.runQ _ hZ.cur _ hp _ hm))).2.2.2.2.2.2.2.2.1

theorem sw_guard {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {Z : S} (a : A) (t : U64)
    (hZ : SchedQueuesInv st T Cs Ω H Z Q Rq) (hacc : SwAccH st R W T G Z) (ht : t ∈ T)
    (ha : L.mem Z (affA t) = L.cpu Z) (hg : Runnable (L.mem Z (stA t)) ∨ G t) (hdq : sched.dequeue gS Z t = sched.dequeue st Z t) :
    sched.switch_to_thread gS ar Z a t = sched.switch_to_thread st ar Z a t := by
  obtain ⟨nRW, lRW, -, -, hKr, hTab⟩ := hacc
  have l := lRW t ht ha hg
  refine sched.switch_to_thread.guard hA Z a t ⟨l.2.2.2.2.2.2.2.2.2.1, l.2.2.2.2.2.2.2.2.2.2, hKr, hTab⟩ hdq
    fun s2 e => ?_
  have hd := deq_step Z t hZ ht ha
  rw [e, WP.spec_ok] at hd
  rw [hd.1.2.1, nodeAt_of_ksb hd.1.1]
  exact (nRW _ (by rw [curth_val]; omega) (by rw [curth_val])).2

set_option maxHeartbeats 4000000 in
/-- `schedule_choose_new_thread` with domain time left and a non-empty ready queue. -/
theorem choose_guard {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {Z : S} (a : A)
    (hZ : SchedQueuesInv st T Cs Ω H Z Q Rq) (hacc : SwAccH st R W T G Z) {p0 : U64} (hp0 : p0.val < 256)
    (hne0 : Q (L.cpu Z) p0 ≠ [])
    (hd0 : L.mem Z (core.num.U64.wrapping_add (L.ksb Z) layout.ks.DOMAIN_TIME) ≠ 0#u64) :
    sched.schedule_choose_new_thread gS ar Z a = sched.schedule_choose_new_thread st ar Z a := by
  have hacc' := hacc
  obtain ⟨nRW, -, -, rDT, -, -⟩ := hacc
  have hN := hZ.nodes _ hZ.cur
  obtain ⟨h', hh', hne', -, hl1, hhp, ehd, -⟩ := choose_head (A := A) ar hN (hZ.ready _ hZ.cur) hp0 hne0
  have bR : RdBitmap (L := L) R Z :=
    ⟨(nRW _ (by rw [l1Off_val]; omega) (by rw [l1Off_val])).1, fun inv hinv => (nRW _ (by simp; omega) (by simp)).1⟩
  refine sched.schedule_choose_new_thread.guard ar Z a rDT hd0
    (sched.choose_thread.guard_ne ar Z a bR hl1 fun p hp => ?_)
  rw [hhp] at hp
  obtain rfl := ok_inj_ff hp
  have hpv := rqOff_val hh'
  have hptv := rqTailOff_val hh'
  refine ⟨hh', (nRW _ (by omega) (by omega)).1, (nRW _ (by omega) (by omega)).1, ?_⟩
  have hmT : (Q (L.cpu Z) h').headD 0#u64 ∈ T := hZ.memT hZ.cur hh' (headD_mem hne' _)
  have hd0' : L.mem Z (L.nodeAt Z (L.cpu Z) (rqOff h')) ≠ 0#u64 := by
    intro e
    have := (hZ.tcbs _ hmT).ne0
    rw [← ehd, e] at this
    exact this rfl
  obtain ⟨hxT, hxa, hxp, -⟩ := rq_head_info hZ hh' hd0'
  exact WH.sw_guard hA a _ hZ hacc' hxT hxa (Or.inl (rq_head_run hZ hh' hd0'))
    (WH.deq_guard_head _ hZ hacc' hxT hxa (Or.inl (rq_head_run hZ hh' hd0')) hh' hxp rfl)

set_option maxHeartbeats 16000000 in
/-- **The switch block on the guarded store** (module docstring). -/
theorem schedSw_guard {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (Y : S) (a : A) {w : U64}
    (hq : SchedQueuesInv st T Cs Ω H Y Q Rq) (hw : w ∈ T) (hwa : L.mem Y (affA w) = L.cpu Y)
    (hact : L.actionW Y = w) (hca : L.mem Y (affA (L.curW Y)) = L.cpu Y) (hwc : w ≠ L.curW Y)
    (hwq : (L.mem Y (inqA w) &&& sched.Q_QUEUED) = 0#u64)
    (hdt : L.mem Y (core.num.U64.wrapping_add (L.ksb Y) layout.ks.DOMAIN_TIME) ≠ 0#u64)
    (hAt : ∀ hi : U64, hi.val < 2048 → OutsideObjs st T Cs Y (atAF (L.ksb Y) hi))
    (hacc : SwAccH st R W T G Y) (hgc : G (L.curW Y))
    (rSt : R (stA (L.curW Y))) (rSc : R (scA (L.curW Y))) (rM : R (maxA (L.mem Y (scA (L.curW Y))))) :
    schedSw gS ar Y a w = schedSw st ar Y a w := by
  have hT := hq.tcbs
  have hN := hq.nodes _ hq.cur
  have hct : L.curW Y ∈ T := hq.curT
  have hcn : w ≠ sched.ACTION_CHOOSE_NEW := fun h => by
    have := (hT w hw).align; rw [h] at this; simp [sched.ACTION_CHOOSE_NEW] at this
  have hwR : ∀ c ∈ Cs, w ∉ Rq c := fun c hc => by
    have := (hq.actOK (by rw [hact]; exact hw)).2 c hc; rwa [hact] at this
  have hwrun : Runnable (L.mem Y (stA w)) := by
    have := (hq.actOK (by rw [hact]; exact hw)).1; rwa [hact] at this
  have lc := hacc.2.1 _ hct hca (Or.inr hgc)
  refine schedSw.guard ar Y a w hcn (hacc.1 _ (by rw [curth_val]; omega) (by rw [curth_val])).1 rSt rSc rM lc.1
    (fun _ => WH.enq_guard _ hq hacc hct hca (Or.inr hgc)) fun was s4 hwas h4 => ?_
  obtain ⟨Q4, hq4, W4, -, hc4, hsub⟩ := requeue_run (w := w) Y hq hca hwas h4
  have acc4 := WH.swacc_mono hq hAt W4 hacc
  have hT4 : ∀ {y K : U64}, y ∈ T → K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3480 → K.val ≠ 3488 → K.val ≠ 3592 →
      L.mem s4 (core.num.U64.wrapping_add y K) = L.mem Y (core.num.U64.wrapping_add y K) :=
    fun hy hK h8 h1 h2 h3 => W4.mem_eq (field_aligned (hT _ hy) hK h8) (swn_tcb hT hN hy hK h1 h2 h3)
  have ha4 : L.mem s4 (affA w) = L.cpu s4 := by
    unfold affA; rw [hT4 hw (by simp) (by simp) (by simp) (by simp) (by simp), W4.2.1]; exact hwa
  have hca4 : L.mem s4 (affA (L.curW s4)) = L.cpu s4 := by
    rw [hc4]; unfold affA; rw [hT4 hct (by simp) (by simp) (by simp) (by simp) (by simp), W4.2.1]; exact hca
  have hr4 : (L.mem s4 (inqA w) &&& sched.Q_RELEASE) = 0#u64 := by
    by_contra h
    exact hwR _ (hq4.aff w hw) ((hq4.released w hw).1 h)
  have hrun4 : Runnable (L.mem s4 (stA w)) := by
    rw [stA_eq, hT4 hw (by simp) (by simp) (by simp) (by simp) (by simp), ← stA_eq]; exact hwrun
  have hwq4 : (L.mem s4 (inqA w) &&& sched.Q_QUEUED) = 0#u64 := by
    by_contra hne
    rcases hsub _ _ _ ((hq4.queued w hw).1 hne) with e | hm
    · exact hwc e
    · exact hq.notQ hw hwq (hq4.aff w hw) (hq4.prio w hw) hm
  have lw4 := acc4.2.1 w hw ha4 (Or.inl hrun4)
  have lc4 := acc4.2.1 _ (hq4.curT) hca4 (Or.inr (show G (L.curW s4) by rw [hc4]; exact hgc))
  have hN4 := hq4.nodes _ hq4.cur
  have hp4 := hq4.prio w hw
  have hdtZ : ∀ Z, WritesIn st Y Z (SWN st T Y) →
      L.mem Z (core.num.U64.wrapping_add (L.ksb Z) layout.ks.DOMAIN_TIME) ≠ 0#u64 := fun Z hZ => by
    rw [hZ.1, hZ.mem_eq (ks_aligned hN (by simp [layout.ks.DOMAIN_TIME]) (by simp [layout.ks.DOMAIN_TIME]))
      (swn_ks hq (by simp [layout.ks.DOMAIN_TIME]))]
    exact hdt
  have tail : ∀ s5 (Q5 : U64 → U64 → List U64), SchedQueuesInv st T Cs Ω H s5 Q5 Rq →
      WritesIn st s4 s5 (SWN st T s4) → Q5 (L.cpu Y) (L.mem s4 (prioA w)) ≠ [] →
      (do
        let s6 ← sched.set_action gS s5 sched.ACTION_CHOOSE_NEW
        sched.schedule_choose_new_thread gS ar s6 a) = (do
        let s6 ← sched.set_action st s5 sched.ACTION_CHOOSE_NEW
        sched.schedule_choose_new_thread st ar s6 a) := by
    intro s5 Q5 hq5 W5 hne5
    have W45 := swn_trans W4 W5
    have acc5 := WH.swacc_mono hq hAt W45 hacc
    refine bind_guard_congr (PathObl.sched.set_action.guard (gS := gS) s5 _
      (acc5.1 _ (by rw [act_val]; omega) (by rw [act_val])).2) fun s6 e6 => ?_
    have h6 := setact_step s5 sched.ACTION_CHOOSE_NEW hq5 (Or.inr (Or.inl choose_val))
      (fun h => by have := (hq5.tcbs _ h).align; simp [sched.ACTION_CHOOSE_NEW] at this)
    rw [e6, WP.spec_ok] at h6
    obtain ⟨W6, hq6, -⟩ := h6
    have W46 := swn_trans W45 W6
    exact WH.choose_guard hA a hq6 (WH.swacc_mono hq hAt W46 hacc) hp4 (by rw [W46.2.1]; exact hne5)
      (hdtZ s6 W46)
  refine schedSwB.guard ar s4 a w was (acc4.1 _ (by rw [curth_val]; omega) (by rw [curth_val])).1
    (acc4.1 _ (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD])).1 lw4.2.2.2.2.1
    lc4.2.2.2.2.1 acc4.2.2.1
    ⟨(acc4.1 _ (by rw [l1Off_val]; omega) (by rw [l1Off_val])).1,
      fun inv hinv => (acc4.1 _ (by simp; omega) (by simp)).1⟩ ?_ ?_
    (WH.sw_guard hA a w hq4 acc4 hw ha4 (Or.inl hrun4) (deq_guard_unq s4 w lw4.1 hwq4))
  · refine bind_guard_congr (WH.app_guard w hq4 acc4 hw ha4 (Or.inl hrun4)) fun s5 e5 => ?_
    have h5 := app_step s4 w hq4 hw ha4 (fun _ => hr4) (fun _ => hrun4)
    rw [e5, WP.spec_ok] at h5
    exact tail s5 _ h5.2 h5.1 (app_ne (by rw [ha4, W4.2.1]) (fun hd => (hq4.queued w hw).1 hd))
  · refine bind_guard_congr (WH.enq_guard w hq4 acc4 hw ha4 (Or.inl hrun4)) fun s5 e5 => ?_
    have h5 := enq_step s4 w hq4 hw ha4 (fun _ => hr4) (fun _ => hrun4)
    rw [e5, WP.spec_ok] at h5
    exact tail s5 _ h5.2 h5.1 (enq_ne (by rw [ha4, W4.2.1]) (fun hd => (hq4.queued w hw).1 hd))

end gst

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
variable {A : Type} (ar : machine.Arch A)
variable {Hm Hs : U64 → Prop}

set_option maxRecDepth 4000 in
set_option maxHeartbeats 64000000 in
/-- **The waking tail when the action is the woken thread, without `current_ok`** (`aw_tail_sw_core`, lvm gen 10):
`aw_tail_sw` with `eok` replaced by the yield fact it used (`hy0`) and the final `vcpu::check` of the entry's current
thread, when it runs a VM and stays (or becomes again) current, by `VcG`. -/
theorem aw_tail_sw_core {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]
    (hA : P0.ArchTotal ar) {s Y : S} {aY : A} {now w : U64} {Lk : U64 → Prop}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hok : IrqOk st s) (hAs : AsidOff (L := L) Ω Sg s)
    (gRd : ∀ w, Aligned w → FireRd st T Z s w → R w)
    (gWr : ∀ w, Aligned w → FireWr st T Z s w → w ≠ stA (L.curW s) → W w)
    (hD2 : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME))
    (hAffSc : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t))
    (rL : ∀ y, LocT st T s y → Hm y → ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → ¬ TimerField K.val →
      ¬ GField K.val → R (core.num.U64.wrapping_add y K))
    (wL : ∀ y, LocT st T s y → Hm y → ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → ¬ GateField K.val →
      ¬ TimerField K.val → ¬ GField K.val → K.val ≠ 3328 → K.val ≠ 3336 →
      W (core.num.U64.wrapping_add y K))
    (rS : ∀ p ∈ Scs, L.mem s (scCoreA p) = L.cpu s → Hs p → ∀ b, Aligned b → InSC p (Z p) b → R b)
    (wS : ∀ p ∈ Scs, L.mem s (scCoreA p) = L.cpu s → Hs p → ∀ b, Aligned b → InSC p (Z p) b → b.val ≠ p.val + 16 → W b)
    (rCD : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN))
    (hSW : StWH st gS T Lk Hm s)
    (hSlot : ∀ y, LocT st T s y → Hm y → R (vtA y) ∧ R (core.num.U64.wrapping_add (vtA y) 8#u64))
    (hKr : R (krA (L := L) s)) (hTab : PathObl.RdTab (L := L) R s)
    (hHr : ∀ y ∈ T, Runnable (L.mem s (stA y)) → Hm y) (hHsc : ∀ y ∈ T, L.mem s (scA y) ≠ 0#u64 → Hm y)
    (hHs : ∀ y ∈ T, L.mem s (scA y) ≠ 0#u64 → Hs (L.mem s (scA y)))
    (eq : localtimer.sched_quiet st s (L.cpu s) = ok true)
    (hy0 : L.mem s (yieldA (L.curW s)) = 0#u64)
    (hF : AwFacts st T Cs Ω H Sg Rp Scs Nt Z Ac R s Y now w)
    (hact : L.actionW Y = w) (hvc : VcG st gS ar T Cs Scs Z s Y) :
    AwTailG st gS ar Y aY := by
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced T := h0.tcbs
  have hcC : L.cpu s ∈ Cs := h0.cur
  have hN : NodePlaced st T s (L.cpu s) := h0.nodes _ hcC
  have hcT : L.curW s ∈ T := h0.curT
  have ht' := hT _ hcT
  obtain ⟨haff, hsct, hcore⟩ := hok
  have hXI := hI.2.2.1
  have hS := hI.2.2.2.2
  have hO := hXI.1
  have hcs : L.cscW s ∈ Scs := hXI.2.2.cur
  have hcq : SCq st s Ω (L.cscW s) (Z (L.cscW s)) := scq_of hO hS hcs
  have hact0 : L.actionW s = sched.ACTION_RESUME_CURRENT := sq_true eq
  have hsc0 : L.mem s (scA (L.curW s)) ≠ 0#u64 := hI.2.1.resume (hact0.trans resume_val)
  have hAc : L.cscW s ∈ Ac := by
    rw [← hsct]
    exact hI.2.1.sact _ hcT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hact0.trans resume_val, rfl⟩))))) hsc0
  have hmx0 : L.rmax s (L.cscW s) ≠ 0#u64 := (hS.act _ hcs).1 hAc
  obtain ⟨TY, kY, cY, nY, tY, scY, -, hstY, -, hwT, wbl, waff, wcur, -, hstw, hyw, htop, hout⟩ := hF
  have hBY := TY.bxi
  obtain ⟨⟨Q, Rq, hq⟩, hBd, hXY, -, hSY⟩ := hBY
  have eYN : ∀ o, L.nodeAt Y (L.cpu Y) o = L.nodeAt s (L.cpu s) o := fun o => by rw [cY, nodeAt_of_ksb kY]
  have hNY : NodePlaced st T Y (L.cpu Y) := by rw [cY]; exact hN.ksb kY
  have hcCY : L.cpu Y ∈ Cs := by rw [cY]; exact hcC
  -- the guarded store: what it admits
  have nR : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s (L.cpu s) o) := fun o h1 h2 =>
    gRd _ (nodeAt_aligned hN h1 h2) (Or.inl (Or.inl ⟨o, h1, h2, rfl⟩))
  have nW : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → W (L.nodeAt s (L.cpu s) o) := fun o h1 h2 =>
    gWr _ (nodeAt_aligned hN h1 h2) (Or.inl (Or.inl ⟨o, h1, h2, rfl⟩)) (fun e => by
      rw [stA_eq] at e; exact node_ne_field hN h1 hcT ht' (by simp) e)
  have rK : ∀ y, LocT st T s y → Hm y → ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 →
      ¬ (3528 ≤ K.val ∧ K.val ≤ 3568) → K.val ≠ 3496 → K.val ≠ 3504 → R (core.num.U64.wrapping_add y K) :=
    fun y hy hm K h1 h2 h3 h4 h5 h6 => rL y hy hm K h1 h2 h3 (by unfold TimerField; exact h4) (by unfold GField; omega)
  have wK : ∀ y, LocT st T s y → Hm y → ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → ¬ GateField K.val →
      ¬ (3528 ≤ K.val ∧ K.val ≤ 3568) → K.val ≠ 3496 → K.val ≠ 3504 → K.val ≠ 3328 → K.val ≠ 3336 →
      W (core.num.U64.wrapping_add y K) :=
    fun y hy hm K h1 h2 h3 hg h4 h5 h6 h7 h8 =>
      wL y hy hm K h1 h2 h3 hg (by unfold TimerField; exact h4) (by unfold GField; omega) h7 h8
  have coreS : ∀ y ∈ T, L.mem s (affA y) = L.cpu s → L.mem s (scA y) ≠ 0#u64 →
      L.mem s (scCoreA (L.mem s (scA y))) = L.cpu s := fun y hy ha h0' => (hAffSc y hy h0').trans ha
  -- frames from `AwFacts`
  have scaY : ∀ y ∈ T, L.mem Y (scA y) = L.mem s (scA y) := fun y hy => by
    rw [scA_eq]; exact tY y hy _ (by simp) (by simp) (Or.inl (by simp)) (by simp) (by simp) (fun _ => by simp)
  have affY : ∀ y ∈ T, L.mem Y (affA y) = L.mem s (affA y) := fun y hy => by
    unfold affA; exact tY y hy _ (by simp) (by simp) (Or.inl (by simp)) (by simp) (by simp) (fun _ => by simp)
  have yldY : ∀ y ∈ T, L.mem Y (yieldA y) = L.mem s (yieldA y) := fun y hy => by
    unfold yieldA; exact tY y hy _ (by simp) (by simp) (Or.inl (by simp)) (by simp) (by simp) (fun _ => by simp)
  have inqY : ∀ y ∈ T, L.mem Y (inqA y) = L.mem s (inqA y) := fun y hy => by
    unfold inqA; exact tY y hy _ (by simp) (by simp) (Or.inr (by simp)) (by simp) (by simp) (fun _ => by simp)
  have stY : ∀ y ∈ T, y ≠ w → L.mem Y (stA y) = L.mem s (stA y) := fun y hy hyw => by
    rw [stA_eq]
    exact tY y hy _ (by simp) (by simp) (Or.inl (by simp)) (by simp) (by simp) (fun e => absurd e hyw)
  have hcurY : L.curW Y = L.curW s := by
    unfold LawfulStore.curW
    rw [eYN]
    exact nY _ (by rw [curth_val]; omega) (by rw [curth_val]) (by rw [curth_val]; omega)
      (by rw [curth_val]; omega) (by rw [curth_val]; omega) (by rw [curth_val]; omega) (by rw [curth_val]; omega)
      (by rw [curth_val]; omega) (by rw [curth_val]; omega)
  have hcsY : L.cscW Y = L.cscW s := by
    unfold LawfulStore.cscW LawfulStore.nodeA
    rw [eYN]
    exact nY _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
      (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
      (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  have hneB : ∀ y ∈ T, y ≠ w → L.mem s (scA y) ≠ 0#u64 → L.mem s (scA y) ≠ L.mem s (scA w) := by
    intro y hy hyw hs0 e
    have b1 := (hXI.2.2.bound y hy hs0).2.1
    have hw0 : L.mem s (scA w) ≠ 0#u64 := by rw [← e]; exact hs0
    have b2 := (hXI.2.2.bound w hwT hw0).2.1
    rw [e] at b1
    exact hyw (b1.symm.trans b2)
  have hcw : L.cscW s ≠ L.mem s (scA w) := by
    rw [← hsct]; exact hneB _ hcT (fun e => wcur e.symm) hsc0
  have rmY : L.rmax Y (L.cscW s) = L.rmax s (L.cscW s) := by
    unfold LawfulStore.rmax; rw [scY _ hcs hcw _ hcq.2.2.2.2 hcq.2.2.2.1]
  -- facts at `Y` for the guarded switch block
  have hwT' := hT w hwT
  have hwaY : L.mem Y (affA w) = L.cpu Y := by rw [affY _ hwT, cY]; exact waff
  have hcaY : L.mem Y (affA (L.curW Y)) = L.cpu Y := by rw [hcurY, affY _ hcT, cY]; exact haff
  have hwc : w ≠ L.curW Y := by rw [hcurY]; exact wcur
  have hwq : (L.mem Y (inqA w) &&& sched.Q_QUEUED) = 0#u64 := by
    rw [inqY _ hwT]
    by_contra hne
    have hm := (h0.queued w hwT).1 hne
    exact not_runnable_of_blocked wbl
      (h0.runQ _ (h0.aff w hwT) _ (h0.prio w hwT) _ hm)
  have hdtv : (layout.ks.DOMAIN_TIME : U64).val < 13568 := by simp [layout.ks.DOMAIN_TIME]
  have hdt8 : (layout.ks.DOMAIN_TIME : U64).val % 8 = 0 := by simp [layout.ks.DOMAIN_TIME]
  have hdtY : L.mem Y (core.num.U64.wrapping_add (L.ksb Y) layout.ks.DOMAIN_TIME) ≠ 0#u64 := by
    rw [kY, hout _ (ks_aligned hN hdtv hdt8) (hS.ksΩ _ hdtv hdt8) (fun hsg => by
      have := hS.ks _ hsg
      rw [ks_word_val hN hdtv] at this
      simp [layout.ks.DOMAIN_TIME] at this
      omega)]
    exact sq_dt eq
  have hAtE : ∀ hi : U64, hi.val < 2048 → L.mem Y (atAF (L.ksb s) hi) = L.mem s (atAF (L.ksb s) hi) :=
    fun hi hhi => hout _ (h0.omega _ (hAs hi hhi).1).1 (hAs hi hhi).1 (hAs hi hhi).2.1
  have hAtY : ∀ hi : U64, hi.val < 2048 → OutsideObjs st T Cs Y (atAF (L.ksb Y) hi) := fun hi hhi => by
    rw [kY]; exact (h0.omega _ (hAs hi hhi).1).ksb kY
  have hlocY : ∀ y ∈ T, L.mem Y (affA y) = L.cpu Y → LocT st T s y := fun y hy ha =>
    ⟨hy, by rw [← affY y hy, ha, cY]⟩
  have hw0s : L.mem s (scA w) ≠ 0#u64 := by
    have := hBd.act (by rw [hact]; exact hwT); rw [hact] at this; rwa [← scaY _ hwT]
  have hmc : Hm (L.curW s) := hHsc _ hcT hsc0
  have hsC : Hs (L.cscW s) := by rw [← hsct]; exact hHs _ hcT hsc0
  have hacc : SwAccH st R W T (· = L.curW Y) Y := by
    refine ⟨fun o h1 h2 => by rw [eYN]; exact ⟨nR o h1 h2, nW o h1 h2⟩, fun y hy ha hg => ?_, by rw [kY]; exact rCD,
      by rw [kY]; exact hD2, by unfold krA; rw [kY]; exact hKr, fun hi hhi => ?_⟩
    · have hl := hlocY y hy ha
      have hm : Hm y := by
        rcases hg with hr | hc
        · by_cases hyw : y = w
          · rw [hyw]; exact hHsc w hwT hw0s
          · exact hHr y hy (by rw [← stY y hy hyw]; exact hr)
        · rw [hc, hcurY]; exact hmc
      have n1 : R (nextA .Sched y) := by
        rw [nextA_eq']
        exact rK y hl hm (nextOff .Sched) (by simp [nextOff]) (by simp [nextOff]) (by simp [nextOff])
          (by simp [nextOff]) (by simp [nextOff]) (by simp [nextOff])
      have n2 : W (nextA .Sched y) := by
        rw [nextA_eq']
        exact wK y hl hm (nextOff .Sched) (by simp [nextOff]) (by simp [nextOff]) (by simp [nextOff])
          (by unfold GateField; simp [nextOff]) (by simp [nextOff]) (by simp [nextOff]) (by simp [nextOff])
          (by simp [nextOff]) (by simp [nextOff])
      have p1 : R (prevA .Sched y) := by
        rw [prevA_eq']
        exact rK y hl hm (prevOff .Sched) (by simp [prevOff]) (by simp [prevOff]) (by simp [prevOff])
          (by simp [prevOff]) (by simp [prevOff]) (by simp [prevOff])
      have p2 : W (prevA .Sched y) := by
        rw [prevA_eq']
        exact wK y hl hm (prevOff .Sched) (by simp [prevOff]) (by simp [prevOff]) (by simp [prevOff])
          (by unfold GateField; simp [prevOff]) (by simp [prevOff]) (by simp [prevOff]) (by simp [prevOff])
          (by simp [prevOff]) (by simp [prevOff])
      have i1 : R (inqA y) := rK y hl hm 3592#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      have i2 : W (inqA y) := wK y hl hm 3592#u64 (by simp) (by simp) (by simp) (by unfold GateField; simp) (by simp)
        (by simp) (by simp) (by simp) (by simp)
      have a1 : R (affA y) := rK y hl hm 3520#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      have d1 : R (domA y) := rK y hl hm 3432#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      have q1 : R (prioA y) := rK y hl hm 3448#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      exact ⟨i1, i2, a1, d1, q1, n1, n2, p1, p2, (hSlot y hl hm).1, (hSlot y hl hm).2⟩
    · rw [kY, hAtE hi hhi]
      refine ⟨(hTab hi hhi).1, fun lo hlo hne => (hTab hi hhi).2 lo hlo hne⟩
  have rMc : R (maxA (L.cscW s)) := rS _ hcs hcore hsC _ hcq.2.2.2.2 hcq.2.2.2.1
  have hlct : LocT st T s (L.curW s) := ⟨hcT, haff⟩
  have hsw : schedSw gS ar Y aY (L.actionW Y) = schedSw st ar Y aY (L.actionW Y) := by
    rw [hact]
    refine WH.schedSw_guard hA Y aY hq hwT hwaY hact hcaY hwc hwq hdtY hAtY hacc rfl ?_ ?_ ?_
    · rw [hcurY, stA_eq]
      exact rK _ hlct hmc _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    · rw [hcurY]; exact rK _ hlct hmc _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    · rw [hcurY, scaY _ hcT, hsct]; exact rMc
  -- the tail after the switch block, for its new current thread `d`
  have key : ∀ X a' d, WritesIn st Y X (SWN st T Y) → L.curW X = d → d ∈ T → L.mem s (affA d) = L.cpu s →
      L.mem Y (yieldA d) = 0#u64 → (L.mem Y (stA d) = sched.TS_RUNNING_VM → d = L.curW s) →
      L.mem s (scA d) ≠ 0#u64 →
      (L.mem s (scA d) = L.cscW s ∨ L.rmax Y (L.mem s (scA d)) ≠ 0#u64) → SwTail st gS ar X a' := by
    intro X a' d hW hcur hd d2 d3 d4 d5 d6
    have hd' := hT d hd
    have hl : LocT st T s d := ⟨hd, d2⟩
    have hmd : Hm d := hHsc d hd d5
    have hsD : Hs (L.mem s (scA d)) := hHs d hd d5
    have eXN : ∀ o, L.nodeAt X (L.cpu X) o = L.nodeAt Y (L.cpu Y) o := fun o => by
      rw [hW.2.1, nodeAt_of_ksb hW.1]
    have kXn : ∀ o : U64, o.val < 128 → o.val % 8 = 0 → o.val ≠ 0 → o.val ≠ 16 → o.val ≠ 120 →
        L.mem X (L.nodeAt Y (L.cpu Y) o) = L.mem Y (L.nodeAt Y (L.cpu Y) o) := fun o h1 h2 h3 h4 h5 =>
      hW.mem_eq (nodeAt_aligned hNY (by omega) h2) (swn_node hT hNY (by omega) h3 h4 h5 h1)
    have kXt : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3480 → K.val ≠ 3488 → K.val ≠ 3592 →
        L.mem X (core.num.U64.wrapping_add y K) = L.mem Y (core.num.U64.wrapping_add y K) :=
      fun y hy K h1 h2 h3 h4 h5 => hW.mem_eq (field_aligned (hT y hy) h1 h2) (swn_tcb hT hNY hy h1 h3 h4 h5)
    have kXsc : ∀ p ∈ Scs, ∀ b, Aligned b → InSC p (Z p) b → L.mem X b = L.mem Y b := fun p hp b hb hin => by
      have hΩ := hSY.sub _ ((hSY.all p hp).2.2 b hb hin)
      exact hW.mem_eq hb (swn_out hT hNY hcCY (hq.omega b hΩ))
    have hcsX : L.cscW X = L.cscW s := by
      rw [← hcsY]
      unfold LawfulStore.cscW LawfulStore.nodeA
      rw [eXN]
      exact kXn _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
        (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
    have rmX : L.rmax X (L.cscW s) = L.rmax s (L.cscW s) := by
      rw [← rmY]; unfold LawfulStore.rmax; exact kXsc _ hcs _ hcq.2.2.2.2 hcq.2.2.2.1
    have pX : L.mem X (scA d) = L.mem s (scA d) := by
      rw [← scaY d hd, scA_eq]; exact kXt d hd _ (by simp) (by simp) (by simp) (by simp) (by simp)
    have hpS : L.mem s (scA d) ∈ Scs := (hXI.2.2.bound d hd d5).1
    have scinX : ∀ p ∈ Scs, L.rmax Y p ≠ 0#u64 → SCin st X Ω p (Z p) := fun p hp hm =>
      ⟨((hSY.all p hp).1 hm).agree (fun b hb hin => kXsc p hp b hb hin),
        fun b hb hin => hSY.sub _ ((hSY.all p hp).2.2 b hb hin)⟩
    have outS : ∀ p ∈ Scs, ∀ q ∈ Scs, p ≠ q → ∀ b, InSC p (Z p) b → Outside b q (Z q) := fun p hp q hq' hne b hb => by
      have := hO.scDisj _ hp _ hq' hne
      unfold Outside; unfold InSC at hb; omega
    have P : TailPld (L := L) T Cs Ω X d :=
      ⟨hT, hd, by rw [hW.2.1]; exact hNY.ksb hW.1, by rw [hW.2.1]; exact hcCY,
        fun b hb => (hq.omega b hb).ksb hW.1⟩
    have cX : L.cpu X = L.cpu s := hW.2.1.trans cY
    refine sw_tail_core (gS := gS) ar hA X a' P hcur (zc := Z (L.cscW s)) (zt := Z (L.mem s (scA d))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hcsX]
      exact SCq.agree' hcq (fun b hb hin => (kXsc _ hcs b hb hin).trans (scY _ hcs hcw b hb hin))
    · intro hne
      rw [pX, hcsX] at hne ⊢
      rcases d6 with e | hm
      · exact absurd e hne
      · exact ⟨scinX _ hpS hm, outS _ hpS _ hcs hne⟩
    · intro _
      rw [hcsX, rmX]; exact hmx0
    · intro hne'
      have eR : L.mem X (rhA (L := L) X) = L.mem Y (L.nodeAt Y (L.cpu Y) layout.node.RELEASE_HEAD) := by
        show L.mem X (L.nodeAt X (L.cpu X) _) = _
        rw [eXN]
        exact kXn _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
          (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
          (by simp [layout.node.RELEASE_HEAD])
      rw [eR] at hne' ⊢
      obtain ⟨r1, r2, r3, r4, r5⟩ := rel_facts TY.bxi hne'
      generalize L.mem Y (L.nodeAt Y (L.cpu Y) layout.node.RELEASE_HEAD) = rh at r1 r2 r3 r4 r5 ⊢
      have prX : L.mem X (scA rh) = L.mem Y (scA rh) := by
        rw [scA_eq]; exact kXt rh r1 _ (by simp) (by simp) (by simp) (by simp) (by simp)
      have hrl : LocT st T s rh := hlocY rh r1 r2
      have r3s : L.mem s (scA rh) ≠ 0#u64 := by rw [← scaY rh r1]; exact r3
      rw [prX, pX, hcsX]
      refine ⟨r1, by rw [scA_eq]; exact rK _ hrl (hHsc rh r1 r3s) _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp),
        Z (L.mem Y (scA rh)), scinX _ r4 r5, fun b hb hin => ?_, fun hne b hb => outS _ r4 _ hcs hne b hb,
        fun hne _ b hb => outS _ r4 _ hpS hne b hb⟩
      rw [scaY rh r1] at hin
      rw [scaY rh r1] at r4
      exact rS _ r4 (coreS rh r1 hrl.2 r3s) (hHs rh r1 r3s) b hb hin
    · intro hne'
      have eT : L.mem X (tmA (L := L) X) = L.mem Y (tmA (L := L) Y) := by
        show L.mem X (L.nodeAt X (L.cpu X) _) = L.mem Y (L.nodeAt Y (L.cpu Y) _)
        rw [eXN]
        exact kXn _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
          (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      rw [eT] at hne' ⊢
      exact ⟨(tmin_facts TY hcCY hne').1, (hstY.2 hne').1⟩
    · intro o h1 h2; rw [eXN, eYN]; exact ⟨nR o h1 h2, nW o h1 h2⟩
    · rw [hW.1, kY]; exact hD2
    · rw [hcsX]
      exact scacc_of hO hcs (fun b hb hin => rS _ hcs hcore hsC b hb hin)
        (fun b hb hin h16 => wS _ hcs hcore hsC b hb hin h16)
    · intro _
      rw [pX]
      have hc' := coreS d hd d2 d5
      exact scacc_of hO hpS (fun b hb hin => rS _ hpS hc' hsD b hb hin)
        (fun b hb hin h16 => wS _ hpS hc' hsD b hb hin h16)
    · unfold yieldA; rw [kXt d hd _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact d3
    · unfold affA; rw [kXt d hd _ (by simp) (by simp) (by simp) (by simp) (by simp)]
      change L.mem Y (affA d) = _
      rw [affY d hd, d2, cX]
    · exact rK _ hl hmd _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    · rw [stA_eq]; exact rK _ hl hmd _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    · obtain ⟨K, hK, e⟩ := regA_eq hd' (r := layout.reg.FAULT_IP) (by simp [layout.reg.FAULT_IP])
      have hr : layout.reg.FAULT_IP.val < 384 := by simp [layout.reg.FAULT_IP]
      have : K.val < 3328 := by omega
      rw [e]; exact rK _ hl hmd K (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · obtain ⟨K, hK, e⟩ := regA_eq hd' (r := layout.reg.NEXT_IP) (by simp [layout.reg.NEXT_IP])
      have hr : layout.reg.NEXT_IP.val < 384 := by simp [layout.reg.NEXT_IP]
      have : K.val < 3328 := by omega
      rw [e]; exact wK _ hl hmd K (by omega) (by omega) (by omega) (by unfold GateField; omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)
    · rw [scA_eq]; exact rK _ hl hmd _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    · exact rK _ hl hmd _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    · rw [pX]
      obtain ⟨m1, m2, m3⟩ := maxA_facts hO hpS
      exact rS _ hpS (coreS d hd d2 d5) hsD _ m1 ⟨m2, m3⟩
    · intro X' h1 h2
      exact hSW X' d sched.TS_RUNNING hl hmd (by rw [h2, cX]) (fun hq' => absurd hq' (by
        rw [h1]; unfold QueuedState; simp [sched.TS_RESTART])) (by unfold QueuedState; simp [sched.TS_RUNNING])
    · -- lvm gen 10: `d` runs a VM, so it is the entry's current thread (`d4`), and `VcG` applies
      intro hvm s4 a4 w4 hc4 s5 a5 eac
      have hvmY : L.mem Y (stA d) = sched.TS_RUNNING_VM := by
        rw [stA_eq, ← kXt d hd _ (by simp) (by simp) (by simp) (by simp) (by simp), ← stA_eq]; exact hvm
      obtain rfl := d4 hvmY
      have tK : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3480 → K.val ≠ 3488 → K.val ≠ 3592 →
          L.mem s4 (core.num.U64.wrapping_add (L.curW s) K) = L.mem Y (core.num.U64.wrapping_add (L.curW s) K) := by
        intro K hK h8 h1 h2 h3
        rw [← kXt _ hcT K hK h8 h1 h2 h3]
        refine w4.mem_eq (field_aligned hd' hK h8) ?_
        rintro (⟨o, ho', e⟩ | hin | ⟨-, hin⟩)
        · exact node_ne_field hNY ho' hcT hd' hK (by rw [← eXN]; exact e.symm)
        · rw [hcsX] at hin
          exact out_ne_field (h0.omega _ (hcq.2.1 _ (field_aligned hd' hK h8) hin)) hcT hd' hK rfl
        · rw [pX, hsct] at hin
          exact out_ne_field (h0.omega _ (hcq.2.1 _ (field_aligned hd' hK h8) hin)) hcT hd' hK rfl
      have hst4 : L.mem s4 (stA (L.curW s)) = sched.TS_RUNNING_VM := by
        rw [stA_eq, tK _ (by simp) (by simp) (by simp) (by simp) (by simp), ← stA_eq]; exact hvmY
      have hy4 : L.mem s4 (yieldA (L.curW s)) = 0#u64 := by
        unfold yieldA; rw [tK _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact d3
      have eac' := activate_nr ar s4 a4 (by rw [hc4]; exact hy4)
        (by rw [hc4, hst4]; simp [sched.TS_RUNNING_VM, sched.TS_RESTART])
      rw [eac'] at eac
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (ok_inj_ff eac)
      refine hvc (by rw [← stY _ hcT (fun e => wcur e.symm)]; exact hvmY) s4 a4 hc4 (fun b hv => ?_) tK
      rw [w4.mem_eq hv.1.1 ?_]
      · exact hW.mem_eq hv.1.1 (swn_out hT hNY hcCY (hv.1.ksb kY))
      rintro (⟨o, ho', e⟩ | hin | ⟨-, hin⟩)
      · exact out_ne_node hv.1 hcC hN ho' (by rw [e, eXN, eYN])
      · rw [hcsX] at hin; exact hv.2 _ hcs hin
      · rw [pX, hsct] at hin; exact hv.2 _ hcs hin
  refine aw_of_sw (gS := gS) ar Y aY (by rw [eYN]; exact nR _ (by rw [act_val]; omega) (by rw [act_val]))
    (by rw [hact, resume_val]; exact fun e => hwT'.ne0 (by rw [e]; rfl)) hsw ?_
  intro X a' e
  rw [hact] at e
  obtain ⟨hW, -, hcases⟩ := schedSw_run hA Y aY hq hwT hwaY hact (fun _ => hcaY) hdtY e
  rcases hcases with hc | hc | ⟨h, hh, hne, hmax, hc⟩
  · -- the current thread stays
    rw [hcurY] at hc
    refine key X a' _ hW hc hcT haff ?_ ?_ hsc0 (Or.inl hsct)
    · rw [yldY _ hcT]; exact hy0
    · exact fun _ => rfl
  · -- the woken thread
    have hwY0 : L.mem Y (scA w) ≠ 0#u64 := by
      have := hBd.act (by rw [hact]; exact hwT); rwa [hact] at this
    have hAcw : L.mem Y (scA w) ∈ Ac := hBd.sact w hwT (Or.inr (Or.inr (Or.inl hact))) hwY0
    have hwS : L.mem Y (scA w) ∈ Scs := (hXY.2.2.bound w hwT hwY0).1
    refine key X a' w hW hc hwT waff (by rw [yldY _ hwT]; exact hyw)
      (fun h => absurd (hstw.symm.trans h) (by simp [sched.TS_RUNNING, sched.TS_RUNNING_VM]))
      (by rw [← scaY _ hwT]; exact hwY0) (Or.inr ?_)
    rw [← scaY _ hwT]; exact (hSY.act _ hwS).1 hAcw
  · -- the old head of the highest ready queue
    obtain ⟨t1, t2, t3⟩ := htop (Q (L.cpu Y)) (hq.ready _ hq.cur) h hh hne hmax
    have hm := headD_mem hne 0#u64
    generalize (Q (L.cpu Y) h).headD 0#u64 = d at t1 t2 t3 hm hc
    have hd : d ∈ T := hq.memT hq.cur hh hm
    obtain ⟨i1, i2⟩ := hq.inQ _ hq.cur h hh d hm
    have hqd : (L.mem Y (inqA d) &&& sched.Q_QUEUED) ≠ 0#u64 := (hq.queued d hd).2 (by rw [i1, i2]; exact hm)
    have hdw : d ≠ w := fun e => by rw [e] at hqd; exact hqd hwq
    have hdY0 : L.mem Y (scA d) ≠ 0#u64 := hBd.q d hd hqd
    have hAcd : L.mem Y (scA d) ∈ Ac := hBd.sact d hd (Or.inl hqd) hdY0
    have hdS : L.mem Y (scA d) ∈ Scs := (hXY.2.2.bound d hd hdY0).1
    refine key X a' d hW hc hd t3 (by rw [yldY _ hd]; exact t1)
      (fun h => absurd (by rw [← stY _ hd hdw]; exact h) t2)
      (by rw [← scaY _ hd]; exact hdY0) (Or.inr ?_)
    rw [← scaY _ hd]; exact (hSY.act _ hdS).1 hAcd

/-- **The waking tail when the action is the woken thread** (module docstring). -/
theorem aw_tail_sw {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]
    (hA : P0.ArchTotal ar) {s Y : S} {aY : A} {now w : U64} {Lk : U64 → Prop}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hok : IrqOk st s) (hAs : AsidOff (L := L) Ω Sg s)
    (gRd : ∀ w, Aligned w → FireRd st T Z s w → R w)
    (gWr : ∀ w, Aligned w → FireWr st T Z s w → w ≠ stA (L.curW s) → W w)
    (hD2 : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME))
    (hAffSc : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t))
    (rL : ∀ y, LocT st T s y → Hm y → ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → ¬ TimerField K.val →
      ¬ GField K.val → R (core.num.U64.wrapping_add y K))
    (wL : ∀ y, LocT st T s y → Hm y → ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → ¬ GateField K.val →
      ¬ TimerField K.val → ¬ GField K.val → K.val ≠ 3328 → K.val ≠ 3336 →
      W (core.num.U64.wrapping_add y K))
    (rS : ∀ p ∈ Scs, L.mem s (scCoreA p) = L.cpu s → Hs p → ∀ b, Aligned b → InSC p (Z p) b → R b)
    (wS : ∀ p ∈ Scs, L.mem s (scCoreA p) = L.cpu s → Hs p → ∀ b, Aligned b → InSC p (Z p) b → b.val ≠ p.val + 16 → W b)
    (rCD : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN))
    (hSW : StWH st gS T Lk Hm s)
    (hSlot : ∀ y, LocT st T s y → Hm y → R (vtA y) ∧ R (core.num.U64.wrapping_add (vtA y) 8#u64))
    (hKr : R (krA (L := L) s)) (hTab : PathObl.RdTab (L := L) R s)
    (hHr : ∀ y ∈ T, Runnable (L.mem s (stA y)) → Hm y) (hHsc : ∀ y ∈ T, L.mem s (scA y) ≠ 0#u64 → Hm y)
    (hHs : ∀ y ∈ T, L.mem s (scA y) ≠ 0#u64 → Hs (L.mem s (scA y)))
    (eq : localtimer.sched_quiet st s (L.cpu s) = ok true)
    (eok : localtimer.current_ok st s (L.cpu s) (L.curW s) (L.cscW s) = ok true)
    (hF : AwFacts st T Cs Ω H Sg Rp Scs Nt Z Ac R s Y now w)
    (hact : L.actionW Y = w) :
    AwTailG st gS ar Y aY := by
  obtain ⟨hmr, -, -⟩ := current_ok_true eok
  obtain ⟨-, -, hnvm, -⟩ := may_run_here_true hmr
  exact WH.aw_tail_sw_core ar hA hI hok hAs gRd gWr hD2 hAffSc rL wL rS wS rCD hSW hSlot hKr hTab hHr hHsc hHs eq (mrh_yield hmr) hF
    hact (fun h => absurd h hnvm)

set_option maxHeartbeats 4000000 in
/-- **The waking fire tail**, its action-`w` tail by `aw_tail_sw` (module docstring). -/
theorem fire_tail_wk2 {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]
    (hA : P0.ArchTotal ar) {s s1 s2 s3 : S} {a a1 a2 a3 : A} {mx irq now i2 : U64} {x : Bool}
    {tip p : localtimer.TimerIrqPlan}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hNt : ∀ n ∈ Nt, H n = some .ntfn) (hok : IrqOk st s)
    (gRd : ∀ w, Aligned w → FireRd st T Z s w → R w)
    (gWr : ∀ w, Aligned w → FireWr st T Z s w → w ≠ stA (L.curW s) → W w)
    (hD2 : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME))
    (hwS : ∀ X, L.mem X (stA (L.curW s)) = sched.TS_RESTART → L.mem X (affA (L.curW s)) = L.cpu s →
      gS.write X (stA (L.curW s)) sched.TS_RUNNING = st.write X (stA (L.curW s)) sched.TS_RUNNING)
    (hwH : ∀ X y v, y ∈ T → FootLtArmed st s (L.cpu s) y →
      (L.mem X (tdA y) ≠ 0#u64 → (L.mem X (thA y)).val >>> 8 = (L.cpu s).val ∧ v.val >>> 8 = (L.cpu s).val) →
      gS.write X (thA y) v = st.write X (thA y) v)
    (hwD : ∀ X y v, y ∈ T → FootLtArmed st s (L.cpu s) y →
      y = L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) → L.mem X (affA y) = L.cpu s →
      L.mem s (affA y) = L.cpu s →
      (L.mem X (tdA y) ≠ 0#u64 ∨ v ≠ 0#u64 → (L.mem X (thA y)).val >>> 8 = (L.cpu s).val) →
      gS.write X (tdA y) v = st.write X (tdA y) v)
    (hWk : ¬ NoWake st s) {Lk : U64 → Prop} {U : Set U64}
    (hAffSc : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t))
    (rL : ∀ y, LocT st T s y → Hm y → ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → ¬ TimerField K.val →
      ¬ GField K.val → R (core.num.U64.wrapping_add y K))
    (wL : ∀ y, LocT st T s y → Hm y → ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → ¬ GateField K.val →
      ¬ TimerField K.val → ¬ GField K.val → K.val ≠ 3328 → K.val ≠ 3336 →
      W (core.num.U64.wrapping_add y K))
    (rS : ∀ p ∈ Scs, L.mem s (scCoreA p) = L.cpu s → Hs p → ∀ b, Aligned b → InSC p (Z p) b → R b)
    (wS : ∀ p ∈ Scs, L.mem s (scCoreA p) = L.cpu s → Hs p → ∀ b, Aligned b → InSC p (Z p) b → b.val ≠ p.val + 16 → W b)
    (lkL : ∀ y ∈ T, QueuedState (L.mem s (stA y)) → Lk (L.mem s (blockA y)) → ∀ k : U64,
      (k.val = 3496 ∨ k.val = 3504) → R (core.num.U64.wrapping_add y k) ∧ W (core.num.U64.wrapping_add y k))
    (rCD : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN))
    (hSW : StWH st gS T Lk Hm s)
    (hLkN : Lk p.ntfn) (hLkE : p.ep ≠ 0#u64 → Lk p.ep)
    (wNt : ∀ k : U64, k.val < 64 → k.val % 8 = 0 → k.val ≠ 24 → W (core.num.U64.wrapping_add p.ntfn k))
    (rwE : p.ep ≠ 0#u64 → ∀ k : U64, k.val < 16 → k.val % 8 = 0 →
      R (core.num.U64.wrapping_add p.ep k) ∧ W (core.num.U64.wrapping_add p.ep k))
    (wRt : p.reply ≠ 0#u64 → W (rTcbA p.reply))
    (etip : localtimer.plan_objects st s = ok tip) (eb : localtimer.same_plan tip p = ok true)
    (eq : localtimer.sched_quiet st s (L.cpu s) = ok true)
    (eok : localtimer.current_ok st s (L.cpu s) (L.curW s) (L.cscW s) = ok true)
    (eu : sched.update_timestamp st ar s a = ok (s1, a1)) (enow : sched.cur_time st s1 = ok now)
    (erel : localtimer.release_due st s1 (L.cpu s) = ok false) (ei2 : sched.consumed st s1 = ok i2)
    (eb4 : sporadic.sufficient st ar s1 a1 (L.cscW s) i2 = ok true)
    (edue : localtimer.timer_due st s1 (L.cpu s) now = ok true)
    (efo : localtimer.fire_ok st s1 (L.cpu s) (L.curW s) p now = ok true)
    (ecb : sched.check_budget st ar s1 a1 = ok (x, s2, a2))
    (emx : layout.irq.MAX = ok mx) (hle : ¬ irq > mx)
    (ei1 : interrupt.irq_state st s irq = ok interrupt.IRQ_TIMER)
    (ehi : interrupt.handle_interrupt st ar s2 a2 irq = ok (s3, a3))
    (hBA : BufAt st T Cs H Sg Scs Z U s3)
    (hAs : AsidOff (L := L) Ω Sg s)
    (hSlot : ∀ y, LocT st T s y → Hm y → R (vtA y) ∧ R (core.num.U64.wrapping_add (vtA y) 8#u64))
    (hKr : R (krA (L := L) s)) (hTab : PathObl.RdTab (L := L) R s)
    (hHr : ∀ y ∈ T, Runnable (L.mem s (stA y)) → Hm y) (hHsc : ∀ y ∈ T, L.mem s (scA y) ≠ 0#u64 → Hm y)
    (hHs : ∀ y ∈ T, L.mem s (scA y) ≠ 0#u64 → Hs (L.mem s (scA y)))
    (hHw : L.epState s (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))) =
        obj.NTFN_WAITING →
      Hm (L.epQ s (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))))).head)
    (hHtm : Hm (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))) :
    FireTailG st gS ar s3 a3 :=
  WH.fire_wk_aw ar hA hI hNt hok gRd gWr hD2 hwS hwH hwD hWk hAffSc rL wL rS wS lkL rCD hSW hLkN hLkE wNt rwE wRt etip
    eb eq eok eu enow erel ei2 eb4 edue efo ecb emx hle ei1 ehi hBA hHw hHtm hHs (fun Y aY w haw hF =>
      hF.2.2.2.2.2.2.2.2.2.2.2.2.2.1.elim
        (fun hact => aw_resume ar hA hI hok gRd gWr hD2 hwS eq eok hF hact)
        (fun hact => WH.aw_tail_sw ar hA hI hok hAs gRd gWr hD2 hAffSc rL wL rS wS rCD hSW hSlot hKr hTab hHr hHsc hHs eq eok
          hF hact))

end main

end Fl4Proofs.P2.WH
