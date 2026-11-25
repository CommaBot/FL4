/-
# P2: the round-robin case's walk: nothing due at the `schedule` state, and the switch back

`rr_nodue`, `rr_rel`: the round-robin writes (`RrW`) keep "no timer due" (`NoDueT`: the node's `TIMER_MIN` and the
earliest thread's deadline are not written) and "no release due" (`RelNone`: the release head, its SC word and
the current time are not written; the head's SC is either the current SC, impossible since `round_robin_ok`
found the current SC's head refill ready while `RelNone` says the release head's is not, or disjoint from it,
P1 `SCsOK.disj`, so its refills are not written).

`dequeue_single_writes`: `dequeue` of a queued thread of this core alone in its ready queue writes only `DqW`:
this core's node words from 128 up (queue and bitmap), its queue word and its sched links.

`rr_choose`: `schedule_choose_new_thread` with domain time left, the L1 bitmap word nonzero and the current thread
the head and tail of the highest ready queue switches back to it (P1 `choose_thread_eq_pick`, the VM root step
keeps the state, P1 `vspace.set_vm_root.same`): it writes only `DqW` (the `CUR_THREAD` write stores the value
already there) and the thread stays current.

No named premises.
-/
import Fl4Proofs.P2.FootTimerIrqRB
import Fl4Proofs.P1.FastSched
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

section law
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- **`NoDueT` across the round-robin writes** (module docstring). -/
theorem rr_nodue {T Cs Ω Xs : Set U64} {H : Heap} {Q : U64 → U64 → List U64} {Rq : U64 → List U64}
    {X Y : S} {ct csc now : U64} {z : Nat}
    (h : SchedQueuesInvX st T Cs Ω H Xs X Q Rq) (hct : ct ∈ T)
    (hΩ : ∀ b, Aligned b → (InRing csc z b ∨ b = core.num.U64.wrapping_add csc layout.sc.CONSUMED) → b ∈ Ω)
    (hm : Tz T (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN)))
    (w : WritesIn st X Y (RrW st T X ct csc z)) (hd : NoDueT st X now) : NoDueT st Y now := by
  obtain ⟨kN, kT, -⟩ := rrw_keep h hct hΩ w
  unfold NoDueT at hd ⊢
  have eA : L.nodeAt Y (L.cpu Y) layout.node.TIMER_MIN = L.nodeAt X (L.cpu X) layout.node.TIMER_MIN := by
    rw [w.2.1, nodeAt_of_ksb w.1]
  have em : L.mem Y (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN) =
      L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN) :=
    kN _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
  rw [eA, em]
  rcases hm with h0 | hmT
  · exact Or.inl h0
  rcases hd with hd | hd
  · exact Or.inl hd
  right
  have e : L.mem Y (tdA (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN))) =
      L.mem X (tdA (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN))) :=
    kT _ hmT 3528#u64 (by simp) (by simp) (by simp) (by simp) (by simp)
  rw [e]; exact hd

end law

section inv
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}

/-- **`RelNone` across the round-robin writes** (module docstring). -/
theorem rr_rel {X Y : S} {ct : U64} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac X) (hct : ct ∈ T)
    (htime : (L.refill X (L.cscW X) (L.rhead X (L.cscW X))).time ≤ L.curTime X)
    (w : WritesIn st X Y (RrW st T X ct (L.cscW X) (Z (L.cscW X)))) (h : RelNone st X) : RelNone st Y := by
  obtain ⟨⟨Q, R, hq⟩, hB, hX, -, hS⟩ := hI
  have hT := hq.tcbs
  have hcC := hq.cur
  have hcS : L.cscW X ∈ Scs := hX.2.2.cur
  obtain ⟨hP, hz⟩ := hX.1.sc _ hcS
  obtain ⟨-, h128, -⟩ := sc_lo hP hz
  have hcv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
  have hcv' : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
  have inΩ : ∀ b, Aligned b → (InRing (L.cscW X) (Z (L.cscW X)) b ∨
      b = core.num.U64.wrapping_add (L.cscW X) layout.sc.CONSUMED) → b ∈ Ω := by
    rintro b hb (hh | rfl)
    · exact hX.1.scW _ hcS b hb hh.inSC
    · exact hX.1.scW _ hcS _ hb ⟨by rw [hcv]; omega, by rw [hcv, hcv']; omega⟩
  obtain ⟨kN, kT, kΩ⟩ := rrw_keep hq hct inΩ w
  have eA : ∀ o, L.nodeAt Y (L.cpu Y) o = L.nodeAt X (L.cpu X) o := fun o => by rw [w.2.1, nodeAt_of_ksb w.1]
  have eh : L.mem Y (L.nodeAt X (L.cpu X) layout.node.RELEASE_HEAD) =
      L.mem X (L.nodeAt X (L.cpu X) layout.node.RELEASE_HEAD) :=
    kN _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD])
  have ect : L.curTime Y = L.curTime X := by
    unfold LawfulStore.curTime LawfulStore.nodeA
    rw [eA]
    exact kN _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
      (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
  unfold RelNone at h ⊢
  rw [ect, eA, eh]
  generalize hh : L.mem X (L.nodeAt X (L.cpu X) layout.node.RELEASE_HEAD) = h0 at h ⊢
  rcases h with h | h
  · exact Or.inl h
  by_cases h00 : h0 = 0#u64
  · exact Or.inl h00
  right
  have hrel := hq.release _ hcC
  have hmem : h0 ∈ R (L.cpu X) := by
    have e := hrel.head
    change L.mem X (L.nodeAt X (L.cpu X) layout.node.RELEASE_HEAD) = _ at e
    rw [hh] at e
    cases hR : R (L.cpu X) with
    | nil => rw [hR] at e; exact absurd e h00
    | cons x xs => rw [hR] at e; simp only [List.headD_cons] at e; subst e; simp
  have hhT : h0 ∈ T := hq.memTR hcC hmem
  have esc : L.mem Y (scA h0) = L.mem X (scA h0) := by
    rw [scA_eq]
    exact kT _ hhT 3464#u64 (by simp) (by simp) (by simp) (by simp) (by simp)
  rw [esc]
  have haff : L.mem X (affA h0) = L.cpu X := hq.inR _ hcC h0 hmem
  have hrb : (L.mem X (inqA h0) &&& sched.Q_RELEASE) ≠ 0#u64 := (hq.released h0 hhT).2 (by rw [haff]; exact hmem)
  have hsc0 : L.mem X (scA h0) ≠ 0#u64 := hB.r h0 hhT hrb
  have hscS : L.mem X (scA h0) ∈ Scs := (hX.2.2.bound h0 hhT hsc0).1
  have hAc : L.mem X (scA h0) ∈ Ac := hB.sact h0 hhT (Or.inr (Or.inl hrb)) hsc0
  by_cases hsame : L.mem X (scA h0) = L.cscW X
  · exfalso
    rw [hsame] at h
    exact h htime
  have hdisj := hS.disj h0 hhT hsc0 hsame
  generalize hsc : L.mem X (scA h0) = sc at h hscS hAc hdisj ⊢
  have hmax : L.rmax X sc ≠ 0#u64 := (hS.act sc hscS).1 hAc
  obtain ⟨hwf, -, hin⟩ := hS.all sc hscS
  have wf := hwf hmax
  obtain ⟨h8, hm, hfit⟩ := wf.bounds
  obtain ⟨-, -, -, hhd, -, hri⟩ := wf.inside
  have keep : ∀ b, Aligned b → InSC sc (Z sc) b → L.mem Y b = L.mem X b := fun b hb hi => by
    have ho := hdisj b hi
    refine kΩ b (hS.sub b (hin b hb hi)) (fun hr => ?_) (fun e => ?_)
    · unfold Outside at ho; unfold InRing at hr; omega
    · rw [e] at ho; unfold Outside at ho; rw [hcv, hcv'] at ho; omega
  have hmin := wf.min_le
  simp at hmin
  have e1 : L.rhead Y sc = L.rhead X sc :=
    keep _ (by unfold Aligned; rw [hhd]; omega) ⟨by rw [hhd]; omega, by rw [hhd]; omega⟩
  obtain ⟨r1, r2, r3⟩ := hri (L.rhead X sc) wf.head_lt
  have e2 : L.mem Y (rtA sc (L.rhead X sc)) = L.mem X (rtA sc (L.rhead X sc)) :=
    keep _ (by unfold Aligned; rw [r1]; omega) ⟨by rw [r1]; omega, by rw [r1]; omega⟩
  simp only [LawfulStore.refill] at h ⊢
  rw [e1, e2]
  exact h

end inv

section deq
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- What `dequeue` of a thread `t` alone in its ready queue of this core writes (module docstring). -/
def DqW (st : machine.Store S) [L : LawfulStore st] (X : S) (t b : U64) : Prop :=
  L.NodeOf X (L.cpu X) (128 ≤ ·) b ∨ b = inqA t ∨ b = nextA .Sched t ∨ b = prevA .Sched t

/-- **`dequeue` of a queued thread alone in its ready queue of this core** (module docstring). -/
theorem dequeue_single_writes {T : Set U64} {X Y : S} {t : U64} (hT : TcbPlaced T) (ht : t ∈ T)
    (hN : NodePlaced st T X (L.cpu X)) (hp : (L.mem X (prioA t)).val < 256)
    (haff : L.mem X (affA t) = L.cpu X) (hq : (L.mem X (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64)
    (hH : L.mem X (L.nodeAt X (L.cpu X) (rqOff (L.mem X (prioA t)))) = t)
    (hE : L.mem X (L.nodeAt X (L.cpu X) (rqTailOff (L.mem X (prioA t)))) = t)
    (h : sched.dequeue st X t = ok Y) : WritesIn st X Y (DqW st X t) := by
  have hta := hT t ht
  have hqd : sched.queued st X t = ok true := by
    rw [eq_of_spec_fd (sched.queued.spec (L := L) X t)]; simp [hq]
  have nB : ∀ o : U64, 128 ≤ o.val → o.val < 4288 → o.val % 8 = 0 → DqW st X t (L.nodeAt X (L.cpu X) o) :=
    fun o h1 h2 h3 => Or.inl ⟨o, h1, h2, h3, rfl⟩
  have aN : Aligned (nextA .Sched t) := field_aligned hta (K := 3480#u64) (by simp) (by simp)
  have aP : Aligned (prevA .Sched t) := field_aligned hta (K := 3488#u64) (by simp) (by simp)
  have aI : Aligned (inqA t) := field_aligned hta (K := 3592#u64) (by simp) (by simp)
  have aH : Aligned (L.nodeAt X (L.cpu X) (rqOff (L.mem X (prioA t)))) :=
    nodeAt_aligned hN (by rw [rqOff_val hp]; omega) (by rw [rqOff_val hp]; omega)
  have aE : Aligned (L.nodeAt X (L.cpu X) (rqTailOff (L.mem X (prioA t)))) :=
    nodeAt_aligned hN (by rw [rqTailOff_val hp]; omega) (by rw [rqTailOff_val hp]; omega)
  unfold sched.dequeue at h
  rw [hqd] at h
  simp only [bind_ok, ↓reduceIte] at h
  rw [aff_ok, haff, dom_ok, eq_of_spec_fd (obj.Tcb.prio.spec (L := L) X t)] at h
  simp only [bind_ok] at h
  obtain ⟨off, hoff, ho1, ho2⟩ := spec_ex_fd (sched.rq_head_off.spec (L.mem X (domA t)) _ hp)
  rw [hoff] at h
  simp only [bind_ok] at h
  subst ho1
  rw [eq_of_spec_fd (sched.q_get.spec (L := L) X _ _), ho2] at h
  simp only [bind_ok] at h
  obtain ⟨⟨q1, s1⟩, e1, h⟩ := bind_eq_ok h
  simp only [Aeneas.Std.uncurry_apply_pair] at h
  obtain ⟨rfl, rfl⟩ := tq_remove_single (by exact hH) (by exact hE) e1
  obtain ⟨s2, e2, h⟩ := bind_eq_ok h
  obtain ⟨s3, e3, h⟩ := bind_eq_ok h
  rw [eq_of_spec_fd (sched.q_set.spec (L := L) _ _ _ _)] at e2
  rw [eq_of_spec_fd (sched.set_flag.spec (L := L) _ t _ _)] at e3
  have e2' := (ok_inj_ff e2).symm
  have e3' := (ok_inj_ff e3).symm
  simp only [nodeAt_wr, ho2] at e2'
  have w1 : WritesIn st X (L.wr (L.wr X (nextA .Sched t) 0#u64) (prevA .Sched t) 0#u64) (DqW st X t) :=
    ((writesIn_wr aN).trans (writesIn_wr aP)).mono fun b hb => by
      rcases hb with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
  have w2 : WritesIn st (L.wr (L.wr X (nextA .Sched t) 0#u64) (prevA .Sched t) 0#u64) s2 (DqW st X t) := by
    rw [e2']
    exact ((writesIn_wr aH).trans (writesIn_wr aE)).mono fun b hb => by
      rcases hb with rfl | rfl
      · exact nB _ (by rw [rqOff_val hp]; omega) (by rw [rqOff_val hp]; omega) (by rw [rqOff_val hp]; omega)
      · exact nB _ (by rw [rqTailOff_val hp]; omega) (by rw [rqTailOff_val hp]; omega)
          (by rw [rqTailOff_val hp]; omega)
  have w3 : WritesIn st s2 s3 (DqW st X t) := by
    rw [e3']
    exact (writesIn_wr aI).mono fun b hb => Or.inr (Or.inl hb)
  have w13 := (w1.trans1 w2).trans1 w3
  have k3 : L.ksb s3 = L.ksb X := w13.1
  obtain ⟨b1, -, h⟩ := bind_eq_ok h
  cases b1
  · rw [if_neg Bool.false_ne_true] at h
    rw [← ok_inj_ff h]
    exact w13
  · rw [if_pos rfl] at h
    have hr := sched.remove_from_bitmap.spec (L := L) s3 (L.cpu X) (L.mem X (domA t)) (L.mem X (prioA t)) hp
    rw [h, WP.spec_ok] at hr
    obtain ⟨v2, -, hv⟩ := hr
    have hg : (L.mem X (prioA t)).val / 64 < 4 := by omega
    have g2 : DqW st X t (L.nodeAt s3 (L.cpu X) (l2Off ((L.mem X (prioA t)).val / 64))) := by
      rw [nodeAt_of_ksb k3]
      exact nB _ (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega)
    have a2 : Aligned (L.nodeAt s3 (L.cpu X) (l2Off ((L.mem X (prioA t)).val / 64))) := by
      rw [nodeAt_of_ksb k3]
      exact nodeAt_aligned hN (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega)
    have g1 : DqW st X t (L.nodeAt s3 (L.cpu X) l1Off) := by
      rw [nodeAt_of_ksb k3]
      exact nB _ (by rw [l1Off_val]) (by rw [l1Off_val]; omega) (by rw [l1Off_val])
    have a1 : Aligned (L.nodeAt s3 (L.cpu X) l1Off) := by
      rw [nodeAt_of_ksb k3]
      exact nodeAt_aligned hN (by rw [l1Off_val]; omega) (by rw [l1Off_val])
    split at hv
    · obtain ⟨v1, rfl, -⟩ := hv
      exact w13.trans1 (((writesIn_wr a2).trans (writesIn_wr a1)).mono fun b hb => by
        rcases hb with rfl | rfl
        · exact g2
        · exact g1)
    · rw [hv]
      exact w13.trans1 ((writesIn_wr a2).mono fun b hb => by rw [hb]; exact g2)

/-- **The switch back to the current thread** (module docstring). -/
theorem rr_choose {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {T : Set U64} {X Y : S} {a a' : A}
    {t p : U64} (hT : TcbPlaced T) (ht : t ∈ T) (hN : NodePlaced st T X (L.cpu X)) (hcur : L.curW X = t)
    (hd0 : L.mem X (core.num.U64.wrapping_add (L.ksb X) layout.ks.DOMAIN_TIME) ≠ 0#u64)
    (hp : p.val < 256) (hl1 : L.l1W X (L.cpu X) ≠ 0#u64) (hhp : sched.highest_prio st X 0#u64 = ok p)
    (hpr : L.mem X (prioA t) = p) (haff : L.mem X (affA t) = L.cpu X)
    (hq : (L.mem X (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64)
    (hH : L.mem X (L.nodeAt X (L.cpu X) (rqOff p)) = t) (hE : L.mem X (L.nodeAt X (L.cpu X) (rqTailOff p)) = t)
    (h : sched.schedule_choose_new_thread st ar X a = ok (Y, a')) :
    WritesIn st X Y (DqW st X t) ∧ L.curW Y = t := by
  unfold sched.schedule_choose_new_thread at h
  rw [domain_time_eq] at h
  simp only [bind_ok] at h
  rw [if_neg hd0] at h
  simp only [bind_ok] at h
  rw [choose_thread_eq_pick ar X a hp hl1 hhp, hH] at h
  unfold sched.switch_to_thread at h
  obtain ⟨⟨Yv, a1⟩, e1, h⟩ := bind_eq_ok h
  have e1' := PathObl.post_of_ok (vspace.set_vm_root.same hA X a t) e1
  simp only at e1'
  subst Yv
  have h' : (do
      let s2 ← sched.dequeue st X t
      let s3 ← sched.set_cur_thread st s2 t
      ok (s3, a1)) = ok (Y, a') := h
  obtain ⟨s2, e2, h⟩ := bind_eq_ok h'
  obtain ⟨s3, e3, h⟩ := bind_eq_ok h
  have e := ok_inj_ff h
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  rw [eq_of_spec_fd (sched.set_cur_thread.spec (L := L) s2 t)] at e3
  have e3' := (ok_inj_ff e3).symm
  subst e3'
  rw [← hpr] at hH hE
  have w2 := dequeue_single_writes hT ht hN (by rw [hpr]; exact hp) haff hq hH hE e2
  have aC : Aligned (L.nodeAt X (L.cpu X) layout.node.CUR_THREAD) :=
    nodeAt_aligned hN (by rw [curth_val]; omega) (by rw [curth_val])
  have eC : L.nodeAt s2 (L.cpu s2) layout.node.CUR_THREAD = L.nodeAt X (L.cpu X) layout.node.CUR_THREAD := by
    rw [w2.2.1, nodeAt_of_ksb w2.1]
  rw [eC]
  refine ⟨⟨by rw [L.ksb_wr]; exact w2.1, by rw [LawfulStore.cpu_wr]; exact w2.2.1, fun b hb hn => ?_⟩, ?_⟩
  · by_cases hbC : b = L.nodeAt X (L.cpu X) layout.node.CUR_THREAD
    · rw [hbC, L.mem_wr_same aC]
      exact hcur.symm
    · rw [mem_wr_ne' aC hb (Ne.symm hbC)]
      exact w2.mem_eq hb hn
  · unfold LawfulStore.curW
    rw [LawfulStore.cpu_wr, nodeAt_of_ksb (L.ksb_wr _ _ _), w2.2.1, nodeAt_of_ksb w2.1, L.mem_wr_same aC]

end deq

end Fl4Proofs.P2
