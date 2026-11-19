/-
P3 (DESIGN.md §9), IPC: **`maybe_return_sched_context` at `J`** (KENTRY-PLAN.md
item 5, the former `JRecvSigRetHyp`): a thread that is not runnable gives the
notification's SC back when it is its own (l4v `maybe_return_sc`: a passive
server waiting again on the notification that lent it its SC).

* `maybeReturn_shape`: the spec's `maybe_return_sc` when the notification's
  SC is the thread's (its one outcome): the thread's and the SC's links cut,
  the other objects, the current thread and SC, the times and the idle
  thread kept, a reschedule pending iff the thread is the current one (as
  XTopJointFinThreadSc's `unbindTcb_shape`); `maybeReturn_mid`: the mid-entry
  facts after it (as `unbindTcb_mid`).
* `nkt_/lkm_/skm_/pres_maybeReturnSc`: the step kinds of the SC framework.
* `maybe_return_sfoot`: FL4's footprint (`SFoot` and the SC's TCB word).
* `JAtZ.maybeReturnJ`: `JAtZ` before to `JAtZ` after, as XTopJointFinThreadSc's
  `JAtZ.unbindTcbJ` (`maybe_return_refines` for `SchedRel`, `Inv.ret`,
  `ActIdle.ret`, P1's `maybe_return_sched_context.inv`/`.kw` for `BlkOK` and
  the node-0 debug word).
-/
import Fl4Proofs.P3.XTopJointRecvSigBlock
import Fl4Proofs.P3.XTopJointFinThreadSc
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif
open Fl4Spec Classical

noncomputable section

theorem nkt_maybeReturnSc (n t : ObjRef) : NKT (maybeReturnSc (Z := Unit) n t) := by
  unfold maybeReturnSc getTcbObjRef getNtfnObjRef getSkObjRef getSimpleKo getObject; repeat nkt_step2

theorem lkm_maybeReturnSc {W : ObjRef → Prop} (n t : ObjRef) : LKM W (maybeReturnSc (Z := Unit) n t) := by
  unfold maybeReturnSc getTcbObjRef getNtfnObjRef getSkObjRef getSimpleKo getObject; repeat lkm_step2

set_option maxHeartbeats 1000000 in
theorem skm_maybeReturnSc (n t : ObjRef) : SKaM (maybeReturnSc (Z := Unit) n t) := by
  unfold maybeReturnSc getTcbObjRef getNtfnObjRef getSkObjRef getSimpleKo getObject; repeat' skm_step

theorem pres_maybeReturnSc (f : Bool × Bool) (n t : ObjRef) : Pres f (maybeReturnSc (Z := Unit) n t) := by
  unfold maybeReturnSc getTcbObjRef getNtfnObjRef getSkObjRef getSimpleKo getObject; pres_auto
  all_goals exact pres_rescheduleRequired f

/-- **The spec's `maybe_return_sc`** when the notification's SC is the
thread's (module docstring). -/
theorem maybeReturn_shape {σ : State Unit} {n t i : ObjRef} {xn : Notification} {x : Tcb} {y : SchedContext}
    {m : Nat} (hI : Inv σ) (hkn : σ.kheap n = some (.notification xn)) (hkt : σ.kheap t = some (.tcb x))
    (hks : σ.kheap i = some (.schedContext y m)) (hxs : x.tcbSchedContext = some i) (hxn : xn.ntfnSc = some i)
    (hnr : runnable x.tcbState = false) :
    ∃ σ', maybeReturnSc (Z := Unit) n t σ = ({((), σ')}, False) ∧
      σ'.kheap t = some (.tcb (tcbSchedContextUpdate (fun _ => none) x)) ∧
      σ'.kheap i = some (.schedContext (scTcbUpdate (fun _ => none) y) m) ∧
      (∀ q, q ≠ t → q ≠ i → σ'.kheap q = σ.kheap q) ∧
      σ'.curThread = σ.curThread ∧ σ'.curSc = σ.curSc ∧ σ'.curTime = σ.curTime ∧
      σ'.consumedTime = σ.consumedTime ∧ σ'.idleThread = σ.idleThread ∧ σ'.idleSc = σ.idleSc ∧
      (∀ u ∈ σ'.releaseQueue, u ∈ σ.releaseQueue) ∧
      (t = σ.curThread → σ'.schedulerAction = .chooseNewThread) ∧
      (¬ t = σ.curThread → σ'.schedulerAction = σ.schedulerAction) := by
  have hti : t ≠ i := by rintro rfl; rw [hkt] at hks; cases hks
  set σ2 := updSc (updK σ t (.tcb (tcbSchedContextUpdate (fun _ => none) x))) i
    (scTcbUpdate (fun _ => none) y) m with hσ2
  have hI2 : Inv σ2 := hI.unbound hkt hxs hks (hI.notQueued hkt hnr)
  have hks1 : (updK σ t (.tcb (tcbSchedContextUpdate (fun _ => none) x))).kheap i = some (.schedContext y m) := by
    simp [updK, Ne.symm hti, hks]
  obtain ⟨σ1, he1, k1, c1, s1, t1, n1, i1, isc1, r1, a1, b1⟩ :=
    whenResched_fields (σ := σ2) hI2.actReady (t = σ2.curThread)
  have heq : maybeReturnSc (Z := Unit) n t σ = ({((), σ1)}, False) := by
    unfold maybeReturnSc getTcbObjRef
    rw [nd_bind_one (getNtfnSc_eq hkn), nd_bind_one (threadGet_eq _ hkt), hxn, hxs]
    unfold NonDet.when
    rw [if_pos ⟨rfl, by simp⟩,
      nd_bind_one (show NonDet.assertOpt (σ := State Unit) (some i) σ = ({(i, σ)}, False) from rfl),
      nd_bind_one (threadSet_eq _ hkt)]
    change (updateSchedContext i _ >>= _) _ = _
    rw [nd_bind_one (updateSchedContext_eq hks1 _), Notif.nd_gets_bind]
    exact he1
  refine ⟨σ1, heq, ?_, ?_, fun q hq1 hq2 => ?_, c1, s1, t1, n1, i1, isc1, fun u hu => by rw [r1] at hu; exact hu,
    fun h => a1 h, fun h => b1 h⟩
  · rw [k1]; simp [σ2, updSc, updK, hti]
  · rw [k1]; simp [σ2, updSc, updK]
  · rw [k1]; simp only [σ2, updSc, updK, Function.update_of_ne hq1, Function.update_of_ne hq2]

/-- **The mid-entry facts after `maybe_return_sc`** (module docstring; the
proof is `unbindTcb_mid`'s on `maybeReturn_shape`). -/
theorem maybeReturn_mid {T C : Set U64} {σ σ' : State Unit} {n i t : ObjRef} {y : SchedContext} {m : Nat}
    {x : Tcb} {xn : Notification}
    (hI : Inv σ) (hks : σ.kheap i = some (.schedContext y m)) (hy : y.scTcb = some t)
    (hkt : σ.kheap t = some (.tcb x)) (hxs : x.tcbSchedContext = some i)
    (hkn : σ.kheap n = some (.notification xn)) (hxn : xn.ntfnSc = some i) (hnr : runnable x.tcbState = false)
    (hiC : ∃ q ∈ C, UScalar.bv q = i)
    (hsa : ∀ u, σ.schedulerAction = .switchThread u → u ≠ t) (hid : t ≠ σ.idleThread)
    (hcur : σ.schedulerAction = .chooseNewThread ∨ CurInv σ) (hown : CurOwnW T C σ) (hoff : OffOK σ)
    (hact : ActIdle σ) (hcr : CurRunM σ)
    (he : maybeReturnSc (Z := Unit) n t σ = ({((), σ')}, False)) :
    (σ'.schedulerAction = .chooseNewThread ∨ CurInv σ') ∧ CurOwnW T C σ' ∧ OffOK σ' ∧ ActIdle σ' ∧
      CurRunM σ' ∧ FK σ σ' := by
  obtain ⟨σ2, e2, kt, ki, ko, ct, cs, tm, cn, hidl, hisc, rq, a1, b1⟩ := maybeReturn_shape hI hkn hkt hks hxs hxn hnr
  have e := the_result e2 he
  subst e
  have hti : t ≠ i := by rintro rfl; rw [hkt] at hks; cases hks
  have nTi : ∀ q (z : Tcb), σ.kheap q = some (.tcb z) → q ≠ i := by
    rintro q z hq rfl; rw [hks] at hq; cases hq
  have nSt : ∀ q (z : SchedContext) m, σ.kheap q = some (.schedContext z m) → q ≠ t := by
    rintro q z m hq rfl; rw [hkt] at hq; cases hq
  have hidi : σ.idleThread ≠ i := by obtain ⟨xi, h1, -⟩ := hact.2; exact nTi _ _ h1
  have hIdle : IdleOK σ' := IdleOK.of hact.2 hidl (ko _ (Ne.symm hid) hidi) (fun h => rq _ h)
  have hAct : ActIdle σ' := by
    refine ⟨fun u hu => ?_, hIdle⟩
    by_cases htc : t = σ.curThread
    · rw [a1 htc] at hu; cases hu
    rw [b1 htc] at hu
    obtain ⟨xu, scp, yu, nu, hku, hsc, hrun, hky, hac, hnr'⟩ := schedulable_inv (hact.1 u hu)
    have hut : u ≠ t := hsa u hu
    have hui : u ≠ i := nTi _ _ hku
    have hst : scp ≠ t := nSt _ _ _ hky
    have hsi : scp ≠ i := by
      rintro rfl
      obtain ⟨y1, n1, h1, h2⟩ := hI.back u xu scp hku hsc
      rw [hks] at h1; cases h1; rw [hy] at h2; cases h2; exact hut rfl
    exact schedulable_of (by rw [ko _ hut hui]; exact hku) hsc hrun (by rw [ko _ hst hsi]; exact hky) hac
      (fun h => hnr' (rq _ h))
  refine ⟨?_, ?_, ?_, hAct, ?_, ⟨cs, hidl, hisc⟩⟩
  · by_cases htc : t = σ.curThread
    · exact Or.inl (a1 htc)
    rcases hcur with h | hC
    · exact Or.inl (by rw [b1 htc]; exact h)
    right
    obtain ⟨xt, hkc, hcs, hnb⟩ := hC.tcb
    obtain ⟨y1, n1, hk1⟩ := hC.sc
    have hct : σ.curThread ≠ t := fun e => htc e.symm
    have hci : σ.curThread ≠ i := nTi _ _ hkc
    have hcst : σ.curSc ≠ t := nSt _ _ _ hk1
    have hcsi : σ.curSc ≠ i := by
      rintro e
      obtain ⟨y2, n2, h1, h2⟩ := hI.back _ xt _ hkc hcs
      rw [e, hks] at h1; cases h1; rw [hy] at h2; cases h2; exact htc rfl
    refine ⟨⟨xt, by rw [ct, ko _ hct hci]; exact hkc, by rw [cs]; exact hcs, hnb⟩,
      ⟨y1, n1, by rw [cs, ko _ hcst hcsi]; exact hk1⟩, fun hne y3 n3 h3 => ?_,
      fun h => hC.notRel (by rw [ct] at h; exact rq _ h)⟩
    rw [cs, hisc] at hne; rw [cs] at h3; rw [ko _ hcst hcsi] at h3
    exact hC.active hne y3 n3 h3
  · rcases hown with ⟨u, hu, xt, hku, hxt, hown, hnr'⟩ | ⟨hcs, hun⟩
    · by_cases hut : UScalar.bv u = t
      · have hku' : σ.kheap t = some (.tcb xt) := by rw [← hut]; exact hku
        rw [hkt] at hku'; cases hku'
        rw [hxs] at hxt; cases hxt
        refine Or.inr ⟨by rw [cs]; exact hiC, fun x' n' h => ?_⟩
        rw [cs, ki] at h; cases h; rfl
      · have hui : UScalar.bv u ≠ i := nTi _ _ hku
        obtain ⟨y1, n1, hk1, -⟩ := hI.back _ xt _ hku hxt
        have hcst : σ.curSc ≠ t := nSt _ _ _ hk1
        have hcsi : σ.curSc ≠ i := by
          rintro e
          have := hown y1 n1 hk1
          rw [e, hks] at hk1; cases hk1; rw [hy] at this; cases this; exact hut rfl
        exact Or.inl ⟨u, hu, xt, by rw [ko _ hut hui]; exact hku, by rw [cs]; exact hxt,
          fun x' n' h => hown x' n' (by rw [cs, ko _ hcst hcsi] at h; exact h),
          fun h0 hm => hnr' (by rw [← cn]; exact h0) (rq _ hm)⟩
    · refine Or.inr ⟨by rw [cs]; exact hcs, fun x' n' h => ?_⟩
      rw [cs] at h
      by_cases e : σ.curSc = i
      · rw [e, ki] at h; cases h; rfl
      by_cases e2 : σ.curSc = t
      · rw [e2, kt] at h; cases h
      rw [ko _ e2 e] at h; exact hun _ _ h
  · intro h0 y1 n1 h1 ha
    rw [cn] at h0 ⊢; rw [tm]
    rw [cs] at h1; rw [cs, hisc] at ha
    by_cases e : σ.curSc = i
    · rw [e, ki] at h1; cases h1
      exact hoff h0 y m (by rw [e]; exact hks) ha
    by_cases e2 : σ.curSc = t
    · rw [e2, kt] at h1; cases h1
    rw [ko _ e2 e] at h1
    exact hoff h0 y1 n1 h1 ha
  · by_cases htc : t = σ.curThread
    · exact Or.inl (act_cn_nr (a1 htc))
    rcases hcr with h | h | h
    · exact Or.inl (by rw [b1 htc]; exact h)
    · refine Or.inr (Or.inl fun x' hx' => ?_)
      rw [ct] at hx'
      by_cases e : σ.curThread = i
      · rw [e, ki] at hx'; cases hx'
      rw [ko _ (fun e' => htc e'.symm) e] at hx'
      exact h x' hx'
    · exact Or.inr (Or.inr (by rw [ct, hidl]; exact h))

end

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- **FL4's `maybe_return_sched_context`'s footprint**: the scheduler's words
and the SC's TCB word, for a thread whose SC is `i`. -/
theorem maybe_return_sfoot {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {t n i : U64} (ht : t ∈ T) (hiC : i ∈ C)
    {x : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb x)) (hsp : x.tcbSchedContext = some i.bv) :
    notification.maybe_return_sched_context st s n t ⦃ s' =>
      WritesIn st s s' (fun b => SFoot st T c s b ∨ b = scW i 24#u64) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨xt, hkt', -, -, hsct, -⟩ := hs.tcb t ht
  rw [hkt] at hkt'; cases hkt'
  have hsc : L.mem s (scA t) = i := by
    have h1 : optRef (L.mem s (scA t)) = some i.bv := by rw [← hsct]; exact hsp
    by_cases h0 : L.mem s (scA t) = 0#u64
    · rw [h0, optRef_zero] at h1; cases h1
    · rw [optRef_ne h0] at h1; exact eq_of_bv (Option.some.inj h1)
  obtain ⟨xs, ns, hks, hxs⟩ := hs.scs i hiC
  have ha24 : Aligned (scW i 24#u64) := (hxs.hdr (K := 24#u64) (by simp) (by simp)).1
  have hit : i.bv ≠ t.bv := fun e => by rw [e, hkt] at hks; cases hks
  unfold notification.maybe_return_sched_context
  refine WP.spec_bind (Notif.obj.Ntfn.sc.spec s n) ?_
  rintro v rfl
  refine WP.spec_bind (P1.obj.Sc.is_null.spec _) ?_
  rintro b rfl
  by_cases h0 : L.mem s (nScA n) = 0#u64
  · rw [if_pos (by simp [h0])]; exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  rw [if_neg (by simp [h0])]
  refine WP.spec_bind (P1.obj.Tcb.sc.spec s t) ?_
  rintro i1 rfl
  by_cases e : L.mem s (nScA n) = L.mem s (scA t)
  swap
  · rw [if_neg e]; exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  rw [if_pos e, e, hsc]
  refine WP.spec_bind (obj.Tcb.set_sc.spec' s t 0#u64) ?_
  rintro s1 rfl
  refine WP.spec_bind (obj.Sc.set_tcb.spec' _ i 0#u64) ?_
  rintro s2 rfl
  have w2 : WritesIn st s (L.wr (L.wr s (scA t) 0#u64) (scW i 24#u64) 0#u64)
      (fun b => SFoot st T c s b ∨ b = scW i 24#u64) :=
    ((writesIn_tcb (s := s) (c := c) (K := 3464#u64) hc.tcbs ht (by unfold SOff SOffL; decide) (by simp)
      0#u64).trans (writesIn_wr ha24)).mono fun b hb => hb.elim Or.inl Or.inr
  obtain ⟨hS1, -, -⟩ := hS.set_tcb_sc ht hkt (v := 0#u64) (Or.inl rfl)
  have hks1 : (updK σ t.bv (.tcb { x with tcbSchedContext := optRef 0#u64 })).kheap i.bv =
      some (.schedContext xs ns) := by simp [updK, hit, hks]
  obtain ⟨hS2, -, -⟩ := hS1.set_sc_tcb hiC hks1 0#u64
  step with sched.cur_thread.spec' as ⟨ct, hct⟩
  unfold obj.Tcb.Insts.CoreCmpPartialEqTcb.eq
  simp only [bind_ok]
  split
  · refine WP.spec_mono (reschedule_required_sfoot hS2) fun s3 h3 => ?_
    exact (w2.trans h3).mono fun b hb => hb.elim id fun h => Or.inl ((SFoot.ksb w2.1).1 h)
  · exact (WP.spec_ok _).2 w2

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 8000000 in
/-- **`maybe_return_sched_context` at `J`** (module docstring): a thread
`t`, not runnable, neither the idle thread nor the switch target, whose SC
`i` is the notification `n`'s, gives it back. -/
theorem JAtZ.maybeReturnJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t n i : U64} {x : Fl4Spec.Tcb}
    {xn : Fl4Spec.Notification} (ht : t ∈ Z.T) (hn : n ∈ Z.N) (hiC : i ∈ Z.C)
    (hk : σ.kheap t.bv = some (.tcb x)) (hkn : σ.kheap n.bv = some (.notification xn))
    (hsp : x.tcbSchedContext = some i.bv) (hxn : xn.ntfnSc = some i.bv) (hnr : Fl4Spec.runnable x.tcbState = false)
    (hnrw : ¬ P1.Runnable (L.mem s (P1.stA t)))
    (hsa : ∀ u, σ.schedulerAction = .switchThread u → u ≠ t.bv) (hid : t.bv ≠ σ.idleThread) :
    notification.maybe_return_sched_context st s n t ⦃ s' => ∃ σ',
      Fl4Spec.maybeReturnSc (Z := Unit) n.bv t.bv σ = ({((), σ')}, False) ∧
      ∃ (Ac' : Set U64) (Lst' : U64 → List U64), JAtZ (L := L) arI AR Z H Cs Ac' Lst' D s' a σ' ⦄ := by
  have hX := J.xtop
  have hS := hX.fin.1.1.1
  have hR := hX.fin.1.1.2.2.1
  obtain ⟨y, m, hky, hyt⟩ := J.inv.back t.bv x i.bv hk hsp
  obtain ⟨σ2, he, kt, ki, ko, -⟩ := maybeReturn_shape J.inv hkn hk hky hsp hxn hnr
  have hm : ((), σ2) ∈ (Fl4Spec.maybeReturnSc (Z := Unit) n.bv t.bv σ).1 := by
    rw [he]; exact Set.mem_singleton _
  obtain ⟨-, hidle⟩ := J.words_of_spec ht hsa hid
  have htP : t ∈ P1.Heap.tcbs H := by rw [← J.tcbs_eq.1]; exact ht
  obtain ⟨⟨Q0, R0, h0⟩, hB0, hX0, hS0, hSg0⟩ := J.blk
  have hout := P1.blocked_out h0 htP hnrw
  refine WP.spec_mono (WP.spec_and (WP.spec_and (maybe_return_refines s σ hR hS J.inv.actReady t n ht hn)
    (maybe_return_sfoot hS ht hiC hk hsp))
    (WP.spec_and (P1.notification.maybe_return_sched_context.inv s n t Q0 R0 h0 hB0 hX0 hS0 hSg0 htP hout hidle)
      (P1.notification.maybe_return_sched_context.kw s n t Q0 R0 h0 hB0 hX0 hS0 hSg0 htP hout hidle))) ?_
  rintro s' ⟨⟨⟨-, σ0, hm0, hf, hv, hS'⟩, hw5⟩, hP1, hfoot⟩
  rw [he] at hm0
  have e0 : σ0 = σ2 := congrArg Prod.snd (Set.mem_singleton_iff.1 hm0)
  rw [e0] at hS' hv
  have hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s' :=
    ⟨hP1.1, hP1.2.1, hP1.2.2.1, hP1.2.2.2.1, hP1.2.2.2.2.1⟩
  have hR' : NtfnStateRel Z.N Z.T (L.mem s') σ2 := hR.frame hS.placed hf hv
  have hN' : NSC Z.N Z.C σ2 := fun q hq x' p hx hp => J.nsc q hq x' p (by
    by_cases e1 : q.bv = t.bv
    · rw [e1, kt] at hx; cases hx
    by_cases e3 : q.bv = i.bv
    · rw [e3, ki] at hx; cases hx
    rw [ko _ e1 e3] at hx; exact hx) hp
  have hI' : Inv σ2 := Inv.ret J.inv hk hkn hnr hm
  have hWk : P1.WritesIn st s s' (KFoot st Z.T Z.N Z.C Z.c s σ) :=
    Sched.WritesIn.kfoot_of_sfoot_scw hS hiC (K := 24#u64) (by simp) (by simp) (by decide) hw5
  have hW : P1.WritesIn st s s' (TFoot st Z.T Z.N Z.C Z.c s σ) := Sched.WritesIn.tfoot_of_kfoot hWk
  have hK : ScTKw (fun _ => False) σ σ2 := nkt_maybeReturnSc n.bv t.bv σ ((), σ2) hm
  have hX' : XTopAt (L := L) AR Z s' a σ2 :=
    xtop_sc_step (ct := σ.curThread) hX J.ip J.nk hW (hK.mono fun _ h => h.elim) hS' hR' id
  have hall := ScAll.of_k hS J.rp J.yld J.mcp J.call J.rfree
    ⟨⟨hS', hR', hN', hI'⟩, hWk, (pres_maybeReturnSc (true, true) _ _).of_eq he⟩
  obtain ⟨-, hY', hM', ⟨Lst', hCR', hRF'⟩, hRP', -⟩ := hall
  obtain ⟨hcur', hown', hoff', hact', hcr', hF⟩ := maybeReturn_mid (T := Z.T) J.inv hky hyt hk hsp hkn hxn hnr
    ⟨i, hiC, rfl⟩ hsa hid J.cur J.own J.off J.act J.curRun he
  have hB' : BlockedScActive σ2 :=
    J.bsa.bk (bk_of_tk_sk hK (skm_maybeReturnSc _ _ σ _ hm)) ((pres_maybeReturnSc (true, true) _ _).of_eq he)
  have hL : LK (fun _ => False) σ σ2 := lkm_maybeReturnSc (W := fun _ => False) n.bv t.bv σ _ hm
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := fun q hq =>
    J.deadP_sc_step hX' hW hK (fun _ _ h => h.elim) hL hF hact'.1 hY'
      ((((pres_maybeReturnSc (true, true) _ _).of_eq he).ykeep rfl).dk q.bv) (fun h => h) (J.jcov.dead q hq)
  have hDbg := J.kw_dbg hfoot
  exact ⟨σ2, he, Ac, Lst', J.sc_frame hW hK hX' hCR' hRF' hY' hM' (J.sc_buf hW hK) hRP' (J.sc_apart hW hK)
    (J.sc_jpl hW hK (J.idleW_keep hX'.fin.1.1.1 hF.2.1 hF.2.2).2)
    (J.sc_jcov hW hdead (fun q hq hn => absurd hq hn) (J.idleW_keep hX'.fin.1.1.1 hF.2.1 hF.2.2))
    (J.sc_kern hW hK hF hX' hDbg fun _ h => h)
    (J.sc_utc hW hK hDbg) hN' hI' hcur' hown' hoff' hact' hB' hcr' hblk⟩

end

end

end Fl4Proofs.P3
