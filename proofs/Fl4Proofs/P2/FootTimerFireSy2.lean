/-
# P2 (p2lf): `schedule`'s switch block on the guarded store

At the post-`awaken` state `Y` whose action is the woken thread `w` (unqueued, of this core), the switch block
`schedSw` on any store `gS` answering `R` reads and `W` writes as `st` is the real one, given `SwAcc` at `Y`:

* `SwAcc st R W T Y`: this core's node words readable and writable; for each thread of this core its queue flag and
  ready links (read / write), affinity / domain / priority and its VSpace slot words (read); `CUR_DOMAIN`,
  `DOMAIN_TIME`, the kernel root and the ASID table (`RdTab`) readable. `swacc_mono`: kept along any `SWN` run from
  `Y` (the ASID table words lie outside the objects, hence outside `SWN`).
* `rq_head_info` / `rq_tail_info`: a non-null ready-queue head / tail is a thread of this core.
* `enq_guard` / `app_guard` / `deq_guard_head` / `deq_guard_unq` / `sw_guard` / `choose_guard`: the steps.
* `enq_cur`, `requeue_run`: the re-queue of the current thread keeps `CUR_THREAD` and adds only it.
* **`schedSw_guard`**: `schedSw gS ar Y a w = schedSw st ar Y a w`.

No named premises.
-/
import Fl4Proofs.P2.FootTimerFireSy1
import Fl4Proofs.P2.FootTimerFireRq
import Fl4Proofs.P2.FootTimerIrqApp
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (RdBitmap bind_guard_congr)

section law
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T Cs Ω : Set U64} {H : Heap}

/-- What the switch block reads and writes, at `Y` (module docstring). -/
def SwAcc (st : machine.Store S) [L : LawfulStore st] (R W : U64 → Prop) (T : Set U64) (Y : S) : Prop :=
  (∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt Y (L.cpu Y) o) ∧ W (L.nodeAt Y (L.cpu Y) o)) ∧
  (∀ y ∈ T, L.mem Y (affA y) = L.cpu Y →
    R (inqA y) ∧ W (inqA y) ∧ R (affA y) ∧ R (domA y) ∧ R (prioA y) ∧
    R (nextA .Sched y) ∧ W (nextA .Sched y) ∧ R (prevA .Sched y) ∧ W (prevA .Sched y) ∧
    R (vtA y) ∧ R (core.num.U64.wrapping_add (vtA y) 8#u64)) ∧
  R (core.num.U64.wrapping_add (L.ksb Y) layout.ks.CUR_DOMAIN) ∧
  R (core.num.U64.wrapping_add (L.ksb Y) layout.ks.DOMAIN_TIME) ∧
  R (krA (L := L) Y) ∧ PathObl.RdTab (L := L) R Y

variable {Q : U64 → U64 → List U64} {Rq : U64 → List U64}

theorem swacc_mono {R W : U64 → Prop} {Y Z : S} (hq : SchedQueuesInv st T Cs Ω H Y Q Rq)
    (hAt : ∀ hi : U64, hi.val < 2048 → OutsideObjs st T Cs Y (atAF (L.ksb Y) hi))
    (hW : WritesIn st Y Z (SWN st T Y)) (h : SwAcc st R W T Y) : SwAcc st R W T Z := by
  have hT := hq.tcbs
  have hN := hq.nodes _ hq.cur
  have eN : ∀ o, L.nodeAt Z (L.cpu Z) o = L.nodeAt Y (L.cpu Y) o := fun o => by
    rw [hW.2.1, nodeAt_of_ksb hW.1]
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨fun o ho h8 => by rw [eN]; exact h1 o ho h8, fun y hy ha => h2 y hy ?_, by rw [hW.1]; exact h3,
    by rw [hW.1]; exact h4, by unfold krA; rw [hW.1]; exact h5, fun hi hhi => ?_⟩
  · have e : L.mem Z (affA y) = L.mem Y (affA y) := by
      unfold affA
      exact hW.mem_eq (field_aligned (hT y hy) (by simp) (by simp))
        (swn_tcb hT hN hy (by simp) (by simp) (by simp) (by simp))
    rw [← e, ha, hW.2.1]
  · have e : L.mem Z (atAF (L.ksb Y) hi) = L.mem Y (atAF (L.ksb Y) hi) :=
      hW.mem_eq (hAt hi hhi).1 (swn_out hT hN hq.cur (hAt hi hhi))
    rw [hW.1, e]
    exact h6 hi hhi

theorem rq_head_info {Z : S} (hZ : SchedQueuesInv st T Cs Ω H Z Q Rq) {p : U64} (hp : p.val < 256)
    (h0 : L.mem Z (L.nodeAt Z (L.cpu Z) (rqOff p)) ≠ 0#u64) :
    L.mem Z (L.nodeAt Z (L.cpu Z) (rqOff p)) ∈ T ∧
      L.mem Z (affA (L.mem Z (L.nodeAt Z (L.cpu Z) (rqOff p)))) = L.cpu Z ∧
      L.mem Z (prioA (L.mem Z (L.nodeAt Z (L.cpu Z) (rqOff p)))) = p ∧
      L.mem Z (L.nodeAt Z (L.cpu Z) (rqOff p)) ∈ Q (L.cpu Z) p := by
  have hr := (hZ.ready _ hZ.cur).1.rel p hp
  have eh : L.mem Z (L.nodeAt Z (L.cpu Z) (rqOff p)) = (Q (L.cpu Z) p).headD 0#u64 := hr.head
  have hne : Q (L.cpu Z) p ≠ [] := fun e => h0 (by rw [eh, e]; rfl)
  have hm := headD_mem hne 0#u64
  rw [eh]
  exact ⟨hZ.memT hZ.cur hp hm, (hZ.inQ _ hZ.cur p hp _ hm).1, (hZ.inQ _ hZ.cur p hp _ hm).2, hm⟩

theorem getLastD_mem' {l : List U64} (h : l ≠ []) (d : U64) : l.getLastD d ∈ l := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getLast h]
  exact List.getLast_mem h

theorem rq_tail_info {Z : S} (hZ : SchedQueuesInv st T Cs Ω H Z Q Rq) {p : U64} (hp : p.val < 256)
    (h0 : L.mem Z (L.nodeAt Z (L.cpu Z) (rqOff p)) ≠ 0#u64) :
    L.mem Z (L.nodeAt Z (L.cpu Z) (rqTailOff p)) ∈ T ∧
      L.mem Z (affA (L.mem Z (L.nodeAt Z (L.cpu Z) (rqTailOff p)))) = L.cpu Z := by
  have hr := (hZ.ready _ hZ.cur).1.rel p hp
  have eh : L.mem Z (L.nodeAt Z (L.cpu Z) (rqOff p)) = (Q (L.cpu Z) p).headD 0#u64 := hr.head
  have el : L.mem Z (L.nodeAt Z (L.cpu Z) (rqTailOff p)) = (Q (L.cpu Z) p).getLastD 0#u64 := hr.last
  have hne : Q (L.cpu Z) p ≠ [] := fun e => h0 (by rw [eh, e]; rfl)
  have hm := getLastD_mem' hne 0#u64
  rw [el]
  exact ⟨hZ.memT hZ.cur hp hm, (hZ.inQ _ hZ.cur p hp _ hm).1⟩

/-- `enqueue` of a thread of this core keeps `CUR_THREAD`. -/
theorem enq_cur (Z : S) (t : U64) (h : SchedQueuesInv st T Cs Ω H Z Q Rq) (ht : t ∈ T)
    (ha : L.mem Z (affA t) = L.cpu Z) :
    sched.enqueue st Z t ⦃ Z' => L.curW Z' = L.curW Z ⦄ := by
  have hc := h.aff t ht
  have hp := h.prio t ht
  have hR1 := h.ready _ hc
  have hT := h.tcbs
  have hN := h.nodes _ h.cur
  have hW : ∀ y ∈ t :: Q (L.mem Z (affA t)) (L.mem Z (prioA t)), y ∈ T := fun y hy => by
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ht
    · exact (hR1.1.rel _ hp).mem y hy
  refine WP.spec_mono (sched.enqueue.foot Z t _ hT ht hp (h.nodes _ hc) hN (hR1.1.rel _ hp)
    (fun h0 => h.notQ ht h0 hc hp)) ?_
  rintro Z' ⟨hw, -⟩
  unfold LawfulStore.curW
  rw [hw.2.1, nodeAt_of_ksb hw.1]
  have h0 : (layout.node.CUR_THREAD).val < 4288 := by rw [curth_val]; omega
  refine hw.mem_eq (nodeAt_aligned hN h0 (by rw [curth_val])) ?_
  rintro (⟨y, hy, e | e⟩ | ⟨o, ho, ho', -, e⟩ | e | ⟨o, ho, ho', -, e⟩)
  · rw [nextA_eq'] at e
    exact node_ne_field hN h0 (hW y hy) (hT _ (hW y hy)) (K := nextOff .Sched) (by simp [nextOff]) e
  · rw [prevA_eq'] at e
    exact node_ne_field hN h0 (hW y hy) (hT _ (hW y hy)) (K := prevOff .Sched) (by simp [prevOff]) e
  · rw [ha] at e
    exact nodeAt_ne hN h0 ho' (by rw [curth_val]; omega) e
  · rw [inqA_eq] at e
    exact node_ne_field hN h0 ht (hT _ ht) (K := 3592#u64) (by simp) e
  · exact nodeAt_ne hN h0 ho' (by rw [curth_val]; omega) e

/-- **The re-queue of the current thread** (real store): the queues grow by the current thread only, `CUR_THREAD`
is kept. -/
theorem requeue_run (Y : S) {w : U64} {was : Bool} {s4 : S} (hq : SchedQueuesInv st T Cs Ω H Y Q Rq)
    (hca : L.mem Y (affA (L.curW Y)) = L.cpu Y)
    (hwas : sched.is_schedulable st Y (L.curW Y) = ok was)
    (h4 : (if was then sched.enqueue st Y (L.curW Y) else ok Y) = ok s4) :
    ∃ Q4, SchedQueuesInv st T Cs Ω H s4 Q4 Rq ∧ WritesIn st Y s4 (SWN st T Y) ∧
      Grow (Q (L.cpu Y)) (Q4 (L.cpu Y)) (L.curW Y) w ∧ L.curW s4 = L.curW Y ∧
      ∀ c p x, x ∈ Q4 c p → x = L.curW Y ∨ x ∈ Q c p := by
  by_cases hb : was = true
  · subst hb
    rw [if_pos rfl] at h4
    have hs := sched.is_schedulable.spec' (L := L) Y (L.curW Y)
    rw [hwas, WP.spec_ok] at hs
    obtain ⟨hrun, -, hrel, -⟩ := hs rfl
    have hct : L.curW Y ∈ T := hq.curT
    have he := enq_step Y (L.curW Y) hq hct hca (fun _ => hrel) (fun _ => hrun)
    have hc := enq_cur Y (L.curW Y) hq hct hca
    rw [h4, WP.spec_ok] at he hc
    refine ⟨_, he.2, he.1, grow_enq (Grow.refl _ _ _) (Or.inl rfl) hca, hc, fun c p x hx => ?_⟩
    split at hx
    · exact Or.inr hx
    · rw [Function.update_apply] at hx
      split at hx
      · rename_i e1
        subst e1
        rw [Function.update_apply] at hx
        split at hx
        · rename_i e2
          subst e2
          rcases List.mem_cons.1 hx with e | e
          · exact Or.inl e
          · exact Or.inr e
        · exact Or.inr hx
      · exact Or.inr hx
  · rw [if_neg hb] at h4
    obtain rfl := ok_inj_ff h4
    exact ⟨Q, hq, WritesIn.refl _ _, Grow.refl _ _ _, rfl, fun _ _ _ hx => Or.inr hx⟩

end law

section gst
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]
variable {T Cs Ω : Set U64} {H : Heap} {Q : U64 → U64 → List U64} {Rq : U64 → List U64}

theorem enq_guard {Z : S} (t : U64) (hZ : SchedQueuesInv st T Cs Ω H Z Q Rq) (hacc : SwAcc st R W T Z)
    (ht : t ∈ T) (ha : L.mem Z (affA t) = L.cpu Z) :
    sched.enqueue gS Z t = sched.enqueue st Z t := by
  have hT := hZ.tcbs
  have hN := hZ.nodes _ hZ.cur
  have hp := hZ.prio t ht
  obtain ⟨nRW, lRW, -⟩ := hacc
  obtain ⟨rI, wI, rA, rD, rP, -, wN, -, wP, -⟩ := lRW t ht ha
  have hpv := rqOff_val hp
  have hpt := rqTailOff_val hp
  refine sched.enqueue.guard_local Z t hT ht hN hp ha (fun h0 => (rq_head_info hZ hp h0).1) rI wI rA rD rP
    (nRW _ (by omega) (by omega)).1 (nRW _ (by omega) (by omega)).2
    (nRW _ (by omega) (by omega)).1 (nRW _ (by omega) (by omega)).2
    ⟨(nRW _ (by rw [l1Off_val]; omega) (by rw [l1Off_val])).1, fun inv hinv => (nRW _ (by simp; omega) (by simp)).1⟩
    (nRW _ (by rw [l1Off_val]; omega) (by rw [l1Off_val])).2 (fun inv hinv => (nRW _ (by simp; omega) (by simp)).2)
    wN wP (fun h0 => ?_)
  obtain ⟨hxT, hxa, -⟩ := rq_head_info hZ hp h0
  exact (lRW _ hxT hxa).2.2.2.2.2.2.2.2.1

theorem app_guard {Z : S} (t : U64) (hZ : SchedQueuesInv st T Cs Ω H Z Q Rq) (hacc : SwAcc st R W T Z)
    (ht : t ∈ T) (ha : L.mem Z (affA t) = L.cpu Z) :
    sched.append gS Z t = sched.append st Z t := by
  have hT := hZ.tcbs
  have hN := hZ.nodes _ hZ.cur
  have hp := hZ.prio t ht
  obtain ⟨nRW, lRW, -⟩ := hacc
  obtain ⟨rI, wI, rA, rD, rP, -, wN, -, wP, -⟩ := lRW t ht ha
  have hpv := rqOff_val hp
  have hpt := rqTailOff_val hp
  refine sched.append.guard_local Z t hT ht hN hp ha (fun h0 => (rq_tail_info hZ hp h0).1) rI wI rA rD rP
    (nRW _ (by omega) (by omega)).1 (nRW _ (by omega) (by omega)).2
    (nRW _ (by omega) (by omega)).1 (nRW _ (by omega) (by omega)).2
    ⟨(nRW _ (by rw [l1Off_val]; omega) (by rw [l1Off_val])).1, fun inv hinv => (nRW _ (by simp; omega) (by simp)).1⟩
    (nRW _ (by rw [l1Off_val]; omega) (by rw [l1Off_val])).2 (fun inv hinv => (nRW _ (by simp; omega) (by simp)).2)
    wN wP (fun h0 => ?_)
  obtain ⟨hxT, hxa⟩ := rq_tail_info hZ hp h0
  exact (lRW _ hxT hxa).2.2.2.2.2.2.1

set_option maxHeartbeats 4000000 in
/-- `dequeue` of the head of a ready queue of this core. -/
theorem deq_guard_head {Z : S} (t : U64) (hZ : SchedQueuesInv st T Cs Ω H Z Q Rq) (hacc : SwAcc st R W T Z)
    (ht : t ∈ T) (ha : L.mem Z (affA t) = L.cpu Z) {p : U64} (hp : p.val < 256)
    (hpt : L.mem Z (prioA t) = p) (hhd : L.mem Z (L.nodeAt Z (L.cpu Z) (rqOff p)) = t) :
    sched.dequeue gS Z t = sched.dequeue st Z t := by
  subst hpt
  have hT := hZ.tcbs
  obtain ⟨nRW, lRW, -⟩ := hacc
  obtain ⟨rI, wI, rA, rD, rP, rN, wN, rPv, wPv, -⟩ := lRW t ht ha
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
  exact (lRW _ (hZ.memT hZ.cur hp hm) (hZ.inQ _ hZ.cur (L.mem Z (prioA y0)) hp _ hm).1).2.2.2.2.2.2.2.2.1

/-- `dequeue` of an unqueued thread reads its queue flag only. -/
theorem deq_guard_unq (Z : S) (t : U64) (rI : R (inqA t))
    (h0 : (L.mem Z (inqA t) &&& sched.Q_QUEUED) = 0#u64) :
    sched.dequeue gS Z t = sched.dequeue st Z t := by
  unfold sched.dequeue
  rw [PathObl.sched.queued.guard (gS := gS) Z t rI]
  have hq : sched.queued st Z t = ok false := by
    rw [eq_of_spec_fd (sched.queued.spec (L := L) Z t)]; simp [h0]
  rw [hq]
  simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]

theorem sw_guard {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {Z : S} (a : A) (t : U64)
    (hZ : SchedQueuesInv st T Cs Ω H Z Q Rq) (hacc : SwAcc st R W T Z) (ht : t ∈ T)
    (ha : L.mem Z (affA t) = L.cpu Z) (hdq : sched.dequeue gS Z t = sched.dequeue st Z t) :
    sched.switch_to_thread gS ar Z a t = sched.switch_to_thread st ar Z a t := by
  obtain ⟨nRW, lRW, -, -, hKr, hTab⟩ := hacc
  have l := lRW t ht ha
  refine sched.switch_to_thread.guard hA Z a t ⟨l.2.2.2.2.2.2.2.2.2.1, l.2.2.2.2.2.2.2.2.2.2, hKr, hTab⟩ hdq
    fun s2 e => ?_
  have hd := deq_step Z t hZ ht ha
  rw [e, WP.spec_ok] at hd
  rw [hd.1.2.1, nodeAt_of_ksb hd.1.1]
  exact (nRW _ (by rw [curth_val]; omega) (by rw [curth_val])).2

set_option maxHeartbeats 4000000 in
/-- `schedule_choose_new_thread` with domain time left and a non-empty ready queue. -/
theorem choose_guard {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {Z : S} (a : A)
    (hZ : SchedQueuesInv st T Cs Ω H Z Q Rq) (hacc : SwAcc st R W T Z) {p0 : U64} (hp0 : p0.val < 256)
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
  exact sw_guard hA a _ hZ hacc' hxT hxa (deq_guard_head _ hZ hacc' hxT hxa hh' hxp rfl)

set_option maxHeartbeats 16000000 in
/-- **The switch block on the guarded store** (module docstring). -/
theorem schedSw_guard {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (Y : S) (a : A) {w : U64}
    (hq : SchedQueuesInv st T Cs Ω H Y Q Rq) (hw : w ∈ T) (hwa : L.mem Y (affA w) = L.cpu Y)
    (hact : L.actionW Y = w) (hca : L.mem Y (affA (L.curW Y)) = L.cpu Y) (hwc : w ≠ L.curW Y)
    (hwq : (L.mem Y (inqA w) &&& sched.Q_QUEUED) = 0#u64)
    (hdt : L.mem Y (core.num.U64.wrapping_add (L.ksb Y) layout.ks.DOMAIN_TIME) ≠ 0#u64)
    (hAt : ∀ hi : U64, hi.val < 2048 → OutsideObjs st T Cs Y (atAF (L.ksb Y) hi))
    (hacc : SwAcc st R W T Y)
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
  have lc := hacc.2.1 _ hct hca
  refine schedSw.guard ar Y a w hcn (hacc.1 _ (by rw [curth_val]; omega) (by rw [curth_val])).1 rSt rSc rM lc.1
    (fun _ => enq_guard _ hq hacc hct hca) fun was s4 hwas h4 => ?_
  obtain ⟨Q4, hq4, W4, -, hc4, hsub⟩ := requeue_run (w := w) Y hq hca hwas h4
  have acc4 := swacc_mono hq hAt W4 hacc
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
  have lw4 := acc4.2.1 w hw ha4
  have lc4 := acc4.2.1 _ (hq4.curT) hca4
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
    have acc5 := swacc_mono hq hAt W45 hacc
    refine bind_guard_congr (PathObl.sched.set_action.guard (gS := gS) s5 _
      (acc5.1 _ (by rw [act_val]; omega) (by rw [act_val])).2) fun s6 e6 => ?_
    have h6 := setact_step s5 sched.ACTION_CHOOSE_NEW hq5 (Or.inr (Or.inl choose_val))
      (fun h => by have := (hq5.tcbs _ h).align; simp [sched.ACTION_CHOOSE_NEW] at this)
    rw [e6, WP.spec_ok] at h6
    obtain ⟨W6, hq6, -⟩ := h6
    have W46 := swn_trans W45 W6
    exact choose_guard hA a hq6 (swacc_mono hq hAt W46 hacc) hp4 (by rw [W46.2.1]; exact hne5)
      (hdtZ s6 W46)
  refine schedSwB.guard ar s4 a w was (acc4.1 _ (by rw [curth_val]; omega) (by rw [curth_val])).1
    (acc4.1 _ (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD])).1 lw4.2.2.2.2.1
    lc4.2.2.2.2.1 acc4.2.2.1
    ⟨(acc4.1 _ (by rw [l1Off_val]; omega) (by rw [l1Off_val])).1,
      fun inv hinv => (acc4.1 _ (by simp; omega) (by simp)).1⟩ ?_ ?_
    (sw_guard hA a w hq4 acc4 hw ha4 (deq_guard_unq s4 w lw4.1 hwq4))
  · refine bind_guard_congr (app_guard w hq4 acc4 hw ha4) fun s5 e5 => ?_
    have h5 := app_step s4 w hq4 hw ha4 (fun _ => hr4) (fun _ => hrun4)
    rw [e5, WP.spec_ok] at h5
    exact tail s5 _ h5.2 h5.1 (app_ne (by rw [ha4, W4.2.1]) (fun hd => (hq4.queued w hw).1 hd))
  · refine bind_guard_congr (enq_guard w hq4 acc4 hw ha4) fun s5 e5 => ?_
    have h5 := enq_step s4 w hq4 hw ha4 (fun _ => hr4) (fun _ => hrun4)
    rw [e5, WP.spec_ok] at h5
    exact tail s5 _ h5.2 h5.1 (enq_ne (by rw [ha4, W4.2.1]) (fun hd => (hq4.queued w hw).1 hd))

end gst

end Fl4Proofs.P2
