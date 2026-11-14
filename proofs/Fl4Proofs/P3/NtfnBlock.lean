/-
P3 (DESIGN.md §9), notifications: **a blocking `receive_signal` on a
notification that is not active refines l4v `receive_signal`** (`Z = Unit`;
l4v `receive_signal_blocked`): the thread's state becomes
`BlockedOnNotification n` (`schedule_tcb` ↔ `set_thread_state_act`,
`SchedHyps.scheduleTcb`), it is inserted in the queue in priority order
(FL4 `append_by_prio` ↔ l4v `tcb_append`, equal on priority-sorted queues),
the notification becomes waiting, then `maybe_return_sched_context` ↔
`maybe_return_sc` (`RecvHyps.returnSc`).

Extra hypotheses: the thread is a TCB not blocked on a notification (it is
the running thread in seL4), it is not the scheduler's switch target (l4v
`scheduler_act_sane`) and not the idle thread, and the notification's queue is sorted by
priority (`PrioSorted`, a P1 invariant: P1 proves `append_by_prio` keeps it,
`append_by_prio.sorted`; on an unsorted queue FL4's insertion, after the
*last* member of priority `≥ p`, and l4v's, after the *first run* of such
members, differ).
-/
import Fl4Proofs.P3.NtfnRecv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Notif
open fl4_core Fl4Proofs.P1

noncomputable section

/-! ## The spec's ordered insertion -/

section Spec
open Fl4Spec
variable {Z : Type}

theorem getsThe_threadRead {γ : Type} {σ : State Z} {p : ObjRef} {x : Tcb} (f : Tcb → γ)
    (hk : σ.kheap p = some (.tcb x)) : NonDet.getsThe (threadRead (Z := Z) f p) σ = ({(f x, σ)}, False) := by
  have h1 : getTcb (Z := Z) p σ = some x := by simp [getTcb, readObject, hk]
  have : threadRead (Z := Z) f p σ = some (f x) := by
    change Option.bind (getTcb (Z := Z) p σ) (fun a => Lookup.oreturn (f a) σ) = _
    rw [h1]; rfl
  simp [NonDet.getsThe, this, NonDet.assertOpt]; rfl

theorem mapM_one {α β : Type} {σ : State Z} (f : α → NonDet (State Z) β) (g : α → β) :
    ∀ ys : List α, (∀ y ∈ ys, f y σ = ({(g y, σ)}, False)) → NonDet.mapM f ys σ = ({(ys.map g, σ)}, False)
  | [], _ => rfl
  | y :: ys, h => by
    unfold NonDet.mapM
    rw [nd_bind_one' (h y List.mem_cons_self),
      nd_bind_one' (mapM_one f g ys fun z hz => h z (List.mem_cons_of_mem _ hz))]
    rfl

theorem zip_takeWhile {α β : Type} (g : α → β) (p : α × β → Bool) :
    ∀ ts : List α, ((ts.zip (ts.map g)).takeWhile p).map Prod.fst = ts.takeWhile (fun y => p (y, g y))
  | [] => rfl
  | a :: rs => by
    simp only [List.map_cons, List.zip_cons_cons, List.takeWhile_cons]
    split <;> simp [zip_takeWhile g p rs]

theorem zip_dropWhile {α β : Type} (g : α → β) (p : α × β → Bool) :
    ∀ ts : List α, ((ts.zip (ts.map g)).dropWhile p).map Prod.fst = ts.dropWhile (fun y => p (y, g y))
  | [] => rfl
  | a :: rs => by
    simp only [List.map_cons, List.zip_cons_cons, List.dropWhile_cons]
    split
    · exact zip_dropWhile g p rs
    · rw [List.map_cons, List.map_fst_zip (by simp)]

/-- The spec's ordered insertion of `t` (priority `v`) into `qs`, by the
priorities `g`. -/
def specIns (qs : List ObjRef) (g : ObjRef → Priority) (v : Priority) (t : ObjRef) : List ObjRef :=
  qs.takeWhile (fun y => @decide (g y ≥ v) (Classical.propDecidable _)) ++
    t :: qs.dropWhile (fun y => @decide (g y ≥ v) (Classical.propDecidable _))

/-- `tcb_append` on TCBs: the ordered insertion by the spec's priorities. -/
theorem tcbAppend_eq {σ : State Z} {t : ObjRef} {xt : Tcb} (hkt : σ.kheap t = some (.tcb xt))
    (qs : List ObjRef) (g : ObjRef → Priority)
    (hq : ∀ y ∈ qs, ∃ x, σ.kheap y = some (.tcb x) ∧ x.tcbPriority = g y) :
    tcbAppend (Z := Z) t qs σ = ({(specIns qs g xt.tcbPriority t, σ)}, False) := by
  unfold tcbAppend orderedInsert
  rw [nd_bind_one (getsThe_threadRead _ hkt),
    nd_bind_one (mapM_one (fun t' => NonDet.getsThe (threadRead (Z := Z) Tcb.tcbPriority t')) g qs
      (fun y hy => by obtain ⟨x, hx, e⟩ := hq y hy; rw [getsThe_threadRead _ hx, e])),
    nd_pure_bind', nd_pure_bind']
  show ({(_, σ)}, False) = _
  congr
  simp only [List.map_append, List.map_cons, zip_takeWhile, zip_dropWhile, List.append_assoc,
    List.singleton_append, specIns]

theorem tcbNtfnAppend_eq {σ : State Z} {t p : ObjRef} {x : Notification} {xt : Tcb}
    (hk : σ.kheap p = some (.notification x)) (hkt : σ.kheap t = some (.tcb xt)) (g : ObjRef → Priority)
    (hq : ∀ y ∈ ntfnQueueOf x, ∃ x, σ.kheap y = some (.tcb x) ∧ x.tcbPriority = g y) :
    tcbNtfnAppend (Z := Z) t p σ = ({((), updK σ p (.notification
      { x with ntfnObj := .waitingNtfn (specIns (ntfnQueueOf x) g xt.tcbPriority t) }))}, False) := by
  unfold tcbNtfnAppend
  rw [nd_bind_one (getNotification_eq hk), nd_pure_bind', nd_bind_one (tcbAppend_eq hkt _ g hq)]
  exact setNotification_eq _ hk

end Spec

/-! ## Lists -/

theorem takeWhile_congr' {α : Type} {p q : α → Bool} :
    ∀ {l : List α}, (∀ a ∈ l, p a = q a) → l.takeWhile p = l.takeWhile q
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.takeWhile_cons, h a List.mem_cons_self,
      takeWhile_congr' (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem dropWhile_congr' {α : Type} {p q : α → Bool} :
    ∀ {l : List α}, (∀ a ∈ l, p a = q a) → l.dropWhile p = l.dropWhile q
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.dropWhile_cons, h a List.mem_cons_self,
      dropWhile_congr' (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem mem_insPrio_sorted {pr : U64 → U64} {p t : U64} {xs : List U64} (h : PrioSorted pr xs) {y : U64}
    (hy : y ∈ insPrio pr p t xs) : y = t ∨ y ∈ xs := by
  rw [insPrio_eq_sorted pr p t xs h] at hy
  rcases List.mem_append.1 hy with hy | hy
  · exact Or.inr ((List.takeWhile_sublist _).subset hy)
  · rcases List.mem_cons.1 hy with rfl | hy
    · exact Or.inl rfl
    · exact Or.inr ((List.dropWhile_suffix _).subset hy)

theorem insPrio_ne_nil {pr : U64 → U64} {p t : U64} {xs : List U64} (h : PrioSorted pr xs) :
    insPrio pr p t xs ≠ [] := by
  rw [insPrio_eq_sorted pr p t xs h]; simp

theorem prioSorted_congr {pr pr' : U64 → U64} {xs : List U64} (h : PrioSorted pr xs)
    (he : ∀ y ∈ xs, pr' y = pr y) : PrioSorted pr' xs :=
  h.imp_of_mem fun ha hb hab => by rw [he _ ha, he _ hb]; exact hab


/-- The priority of the TCB at `y` in the spec's heap (0 if none). -/
def prioOf (σ : Fl4Spec.State Unit) (y : Fl4Spec.ObjRef) : Fl4Spec.Priority :=
  match σ.kheap y with
  | some (.tcb z) => z.tcbPriority
  | _ => 0

/-- The queue of a related notification, whatever its state. -/
theorem NtfnObjRel.queue {m : U64 → U64} {T : Set U64} {n : U64} {o : Fl4Spec.Ntfn} (h : NtfnObjRel m T n o) :
    ∃ xs, QueueRel m T .Ep (qOf m n) xs ∧ o.ntfnQueue = xs.map UScalar.bv ∧ ∀ y ∈ xs, BlockedOn m n y := by
  cases o with
  | idleNtfn => exact ⟨[], h.2, rfl, by simp⟩
  | activeNtfn b => exact ⟨[], h.2.1, rfl, by simp⟩
  | waitingNtfn q =>
    obtain ⟨-, xs, -, rfl, h2, h3⟩ := h
    exact ⟨xs, h2, rfl, h3⟩

/-! ## The blocking receive -/

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st] {N T : Set U64}
  {SR : S → Fl4Spec.State Unit → Prop}

theorem tsCode_six {ts : Fl4Spec.ThreadState} (h : tsCode ts = 6) : ∃ m, ts = .blockedOnNotification m := by
  cases ts <;> simp [tsCode] at h ⊢

/-- A TCB not blocked on a notification is in no notification queue. -/
theorem not_member {m : U64 → U64} {σ : Fl4Spec.State Unit} (hR : NtfnStateRel N T m σ) {t : U64} (ht : t ∈ T)
    {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt)) (hnb : ∀ m, xt.tcbState ≠ .blockedOnNotification m) :
    ∀ n ∈ N, ∀ z, σ.kheap n.bv = some (.notification z) → t.bv ∉ z.ntfnObj.ntfnQueue := by
  intro n hn z hz hm
  obtain ⟨-, h6, -⟩ := (hR.at_ntfn hn hz).obj.blocked hm
  have := (hR.at_tcb ht hkt).st
  rw [h6] at this
  obtain ⟨m', e⟩ := tsCode_six this.symm
  exact hnb m' e

theorem six_val : sched.TS_BLOCKED_ON_NTFN.val = 6 := by unfold sched.TS_BLOCKED_ON_NTFN; rfl

theorem prio_ge_iff (p q : U64) (v g : Fl4Spec.Priority) (hp : p.val = v.toNat) (hq : q.val = g.toNat) :
    (!decide (p > q)) = decide (g ≥ v) := by
  have e1 : (p > q) ↔ g.toNat < v.toNat := by rw [gt_iff_val, hp, hq]
  have e2 : (g ≥ v) ↔ v.toNat ≤ g.toNat := BitVec.le_def
  by_cases h : v.toNat ≤ g.toNat
  · have h1 : ¬ p > q := fun h' => by have := e1.1 h'; omega
    have h2 : g ≥ v := e2.2 h
    simp [h1, h2]
  · have h1 : p > q := e1.2 (by omega)
    have h2 : ¬ g ≥ v := fun h' => h (e2.1 h')
    simp [h1, h2]

/-- **Blocking receive** on an idle or waiting notification. -/
theorem receive_signal_block (hH : SchedHyps st ar N T SR) (hV : RecvHyps st ar N T SR) (hP : NPlaced T N)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : NtfnStateRel N T (L.mem s) σ) (hSR : SR s σ)
    {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hnb : ∀ m, xt.tcbState ≠ .blockedOnNotification m)
    {n : U64} (hn : n ∈ N) {x : Fl4Spec.Notification} (hk : σ.kheap n.bv = some (.notification x))
    (hna : ∀ b, x.ntfnObj ≠ .activeNtfn b)
    (hsort : ∀ xs, QueueRel (L.mem s) T .Ep (qOf (L.mem s) n) xs → PrioSorted (fun y => L.mem s (prioA y)) xs)
    (cb : Fl4Spec.Badge) (cr : Fl4Spec.CapRights) (hAR : ActReady σ) (hNQ : NotQueued σ t.bv)
    (hRB : RelIfBound σ t.bv) (hsane : ∀ u, σ.schedulerAction = .switchThread u → u ≠ t.bv)
    (hnidle : t.bv ≠ σ.idleThread) :
    notification.receive_signal st ar s a t n true ⦃ r =>
      ¬ (Fl4Spec.receiveSignal t.bv (.notificationCap n.bv cb cr) true σ).2 ∧
      ∃ σ', ((), σ') ∈ (Fl4Spec.receiveSignal t.bv (.notificationCap n.bv cb cr) true σ).1 ∧
        NtfnStateRel N T (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ := by
  have hx := hR.at_ntfn hn hk
  have hxt := hR.at_tcb ht hkt
  have hnm := not_member hR ht hkt hnb
  -- the queue
  obtain ⟨xs, hQ, hxs, hB, hst⟩ : ∃ xs, QueueRel (L.mem s) T .Ep (qOf (L.mem s) n) xs ∧
      x.ntfnObj.ntfnQueue = xs.map UScalar.bv ∧ (∀ y ∈ xs, BlockedOn (L.mem s) n y) ∧
      (stOf (L.mem s) n = obj.NTFN_IDLE ∨ stOf (L.mem s) n = obj.NTFN_WAITING) := by
    have := hx.obj
    cases h : x.ntfnObj with
    | idleNtfn =>
      rw [h] at this
      exact ⟨[], this.2, rfl, by simp, Or.inl (stOf_idle (T := T) (h ▸ hx.obj) rfl)⟩
    | waitingNtfn q =>
      rw [h] at this
      obtain ⟨h1, xs, -, rfl, h2, h3⟩ := this
      exact ⟨xs, h2, rfl, h3, Or.inr (stOf_waiting (T := T) (h ▸ hx.obj) rfl)⟩
    | activeNtfn b => exact absurd h (hna b)
  have htxs : t ∉ xs := fun h => hnm n hn x hk (by rw [hxs]; exact List.mem_map_of_mem h)
  have hsorted := hsort xs hQ
  -- step 1: the state and block-object words
  set x1 : Fl4Spec.Tcb := { xt with tcbState := .blockedOnNotification n.bv }
  set σ1 := updK σ t.bv (.tcb x1)
  set s2 := L.wr (L.wr s (tStA t) sched.TS_BLOCKED_ON_NTFN) (tBlockA t) n
  obtain ⟨hw1, hoth1⟩ := twr_wr (st := st) hP ht (K := 3328#u64) (Or.inl rfl) s sched.TS_BLOCKED_ON_NTFN
  obtain ⟨hw2, hoth2⟩ := twr_wr (st := st) hP ht (K := 3336#u64) (Or.inr (Or.inl rfl))
    (L.wr s (tStA t) sched.TS_BLOCKED_ON_NTFN) n
  rw [← tStA_eq] at hw1 hoth1
  rw [← tBlockA_eq] at hw2 hoth2
  have hw := hw1.trans hw2
  have hR1 : NtfnStateRel N T (L.mem s2) σ1 := by
    refine hR.upd_tcb ht _ hw.ntfn hw.tcb hw.links (Or.inl hnm) ⟨?_, ?_, ?_, ?_⟩
    · show (L.mem s2 (tStA t)).val = 6
      rw [tStA_eq, hoth2 _ (by simp) (by simp) (by simp), ← tStA_eq, rd_wr_eq (foot_st hP ht).1, six_val]
    · intro m hm
      cases hm
      show (L.mem s2 (tBlockA t)).bv = n.bv
      rw [rd_wr_eq (foot_blk hP ht).1]
    · show (L.mem s2 (badgeRegA t)).bv = badgeOf xt
      rw [badgeRegA_eq, hoth2 _ (by simp) (by simp) (by simp), hoth1 _ (by simp) (by simp) (by simp),
        ← badgeRegA_eq]; exact hxt.badge
    · show (L.mem s2 (prioA t)).val = xt.tcbPriority.toNat
      rw [prioA_eq', hoth2 _ (by simp) (by simp) (by simp), hoth1 _ (by simp) (by simp) (by simp),
        ← prioA_eq']; exact hxt.prio
  have hSR1 := hH.block _ _ _ _ t hSR hNQ hRB hsane hnidle hw.foot (NtfnStep.tcb hkt (.blockedOnNotification n.bv) xt.tcbArch)
    (fun p x y h1 h2 hp => by
      simp only [Function.update_apply, hp, ↓reduceIte] at h2; rw [h1] at h2; cases h2; rfl)
  set σ2 := stsAct σ1 t.bv
  have hnt : n.bv ≠ t.bv := by intro e; rw [e, hkt] at hk; cases hk
  have hk2 : σ2.kheap n.bv = some (.notification x) := by simp [σ2, σ1, stsAct_kheap, hnt, hk]
  have hkt2 : σ2.kheap t.bv = some (.tcb x1) := by simp [σ2, σ1, stsAct_kheap]
  -- step 2: `schedule_tcb`
  have key : (do
      let s1 ← obj.Tcb.set_state st t s sched.TS_BLOCKED_ON_NTFN
      let s2 ← obj.Tcb.set_block_obj st t s1 n
      let s3 ← sched.schedule_tcb st s2 t
      let s4 ← notification.ntfn_append st s3 n t
      let s5 ← notification.maybe_return_sched_context st s4 n t
      ok (s5, a)) ⦃ r =>
      ¬ (Fl4Spec.receiveSignal t.bv (.notificationCap n.bv cb cr) true σ).2 ∧
      ∃ σ', ((), σ') ∈ (Fl4Spec.receiveSignal t.bv (.notificationCap n.bv cb cr) true σ).1 ∧
        NtfnStateRel N T (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ := by
    step
    step
    subst s1_post s2_post
    refine WP.spec_bind (hH.scheduleTcb _ σ1 t hR1 hSR1 ht) ?_
    rintro s3 ⟨hf3, hS3⟩
    have hR3 : NtfnStateRel N T (L.mem s3) σ2 := hR1.frame hP hf3 (KView.stsAct _ _)
    obtain ⟨xs3, hQ3, hxs3, hB3⟩ := (hR3.at_ntfn hn hk2).obj.queue
    have e3 : xs3 = xs := by
      rw [hxs] at hxs3
      exact (List.map_injective_iff.2 (fun a b h => eq_of_bv h) hxs3).symm
    subst e3
    have hxt3 := hR3.at_tcb ht hkt2
    -- priorities agree with those of `s`
    have hpr : ∀ y ∈ xs3, L.mem s3 (prioA y) = L.mem s (prioA y) := by
      intro y hy
      have hyT := hQ.mem y hy
      have hyt : y ≠ t := fun e => htxs (e ▸ hy)
      exact (hf3.tfields hP hyT).prio.trans (hw.tcb y hyT hyt).prio
    have hsorted3 : PrioSorted (fun y => L.mem s3 (prioA y)) xs3 := prioSorted_congr hsorted hpr
    refine WP.spec_bind (ntfn_append_full hP s3 hn t xs3 hQ3 ht htxs) ?_
    rintro s4 ⟨hA1, hA2, hA3⟩
    set ys := insPrio (fun y => L.mem s3 (prioA y)) (L.mem s3 (prioA t)) t xs3
    have hblk3 : L.mem s3 (tBlockA t) = n := eq_of_bv (hxt3.blk n.bv rfl)
    have hR4 : NtfnStateRel N T (L.mem s4)
        (updK σ2 n.bv (.notification { x with ntfnObj := .waitingNtfn (ys.map UScalar.bv) })) := by
      have hx2 := hR3.at_ntfn hn hk2
      refine hR3.upd_ntfn hn _ hA3.ntfn hA3.tcb (fun y hy hb => hA3.links y hy ?_) ⟨?_, ?_, ?_, ?_⟩
      · intro hm
        rcases List.mem_cons.1 hm with rfl | hm
        · exact hb hblk3
        · exact hb (hB3 y hm).2
      · refine ⟨hA2, ys, insPrio_ne_nil hsorted3, rfl, hA1, fun y hy => ?_⟩
        have hyT : y ∈ T := by
          rcases mem_insPrio_sorted hsorted3 hy with rfl | hy'
          · exact ht
          · exact hQ.mem y hy'
        have e := hA3.tcb y hyT
        rcases mem_insPrio_sorted hsorted3 hy with rfl | hy'
        · exact ⟨by rw [e.st, hxt3.st]; rfl, by rw [e.blk]; exact hblk3⟩
        · exact ⟨by rw [e.st]; exact (hB3 y hy').1, by rw [e.blk]; exact (hB3 y hy').2⟩
      · show x.ntfnBoundTcb = _; rw [hA3.bound]; exact hx2.bound
      · rw [hA3.bound]; exact hx2.bound_mem
      · show x.ntfnSc = _; rw [hA3.sc]; exact hx2.sc
    -- the spec
    have hq : ∀ y ∈ Fl4Spec.ntfnQueueOf x, ∃ z, σ2.kheap y = some (.tcb z) ∧ z.tcbPriority = prioOf σ2 y := by
      intro y hy
      have hy' : y ∈ x.ntfnObj.ntfnQueue := hy
      rw [hxs] at hy'
      obtain ⟨y', hy'x, rfl⟩ := List.mem_map.1 hy'
      obtain ⟨z, hz, -⟩ := hR3.tcb y' (hQ.mem y' hy'x)
      exact ⟨z, hz, by simp [prioOf, hz]⟩
    have hlist : specIns (Fl4Spec.ntfnQueueOf x) (prioOf σ2) x1.tcbPriority t.bv = ys.map UScalar.bv := by
      have hq' : Fl4Spec.ntfnQueueOf x = xs3.map UScalar.bv := hxs
      rw [specIns, hq', List.takeWhile_map, List.dropWhile_map]
      simp only [ys, insPrio_eq_sorted _ _ t xs3 hsorted3, List.map_append, List.map_cons]
      have hc : ∀ y ∈ xs3, ((fun y => @decide (prioOf σ2 y ≥ x1.tcbPriority) (Classical.propDecidable _)) ∘
          UScalar.bv) y =
          (fun y => !decide (L.mem s3 (prioA t) > L.mem s3 (prioA y))) y := by
        intro y hy
        obtain ⟨z, hz, hzr⟩ := hR3.tcb y (hQ.mem y hy)
        have hpz : prioOf σ2 y.bv = z.tcbPriority := by simp [prioOf, hz]
        simp only [Function.comp, hpz]
        convert (prio_ge_iff _ _ _ _ hxt3.prio hzr.prio).symm using 2
      rw [takeWhile_congr' hc, dropWhile_congr' hc]
    set σ3 := updK σ2 n.bv (.notification { x with ntfnObj := .waitingNtfn (ys.map UScalar.bv) })
    have hspec : Fl4Spec.receiveSignal (Z := Unit) t.bv (.notificationCap n.bv cb cr) true σ =
        Fl4Spec.maybeReturnSc n.bv t.bv σ3 := by
      rw [receiveSignal_notActive hk hna]
      unfold Fl4Spec.receiveSignalBlocked
      simp only [↓reduceIte]
      rw [nd_bind_one (setThreadState_eq _ hkt), nd_bind_one (tcbNtfnAppend_eq hk2 hkt2 (prioOf σ2) hq), hlist]
    rw [hspec]
    have hSR4 := hH.stable _ _ _ _ hS3 hA3.foot
      (NtfnStep.ntfn (y := { x with ntfnObj := .waitingNtfn (ys.map UScalar.bv) }) hk2 rfl rfl)
      (NoBlock.ntfnUpd _ _ _)
    have hb : BlockStep σ σ3 t.bv n.bv := by
      refine ⟨?_, ?_, ?_, fun p h1 h2 => ?_,
        ⟨x, { x with ntfnObj := .waitingNtfn (ys.map UScalar.bv) }, hk, by simp [σ3, updK]⟩,
        ⟨xt, x1, hkt, by simp [σ3, updK, Ne.symm hnt, hkt2], rfl, rfl⟩⟩
      · show (stsAct σ1 t.bv).schedulerAction = σ.schedulerAction ∨
          (stsAct σ1 t.bv).schedulerAction = .chooseNewThread
        unfold stsAct; split_ifs
        · exact Or.inr rfl
        · exact Or.inl rfl
      · show (stsAct σ1 t.bv).curTime = σ.curTime
        unfold stsAct; split_ifs <;> rfl
      · show (stsAct σ1 t.bv).releaseQueue = σ.releaseQueue
        unfold stsAct; split_ifs <;> rfl
      · simp [σ3, σ2, σ1, updK, stsAct_kheap, h1, h2]
    have hid3 : σ3.idleThread = σ.idleThread := by
      show (stsAct σ1 t.bv).idleThread = _; unfold stsAct; split_ifs <;> rfl
    refine WP.spec_bind (hV.returnSc s4 σ σ3 t n hR4 hSR4 ht hn hAR hb (by rw [hid3]; exact hnidle)) ?_
    rintro s5 ⟨hnf, σ', hm, hf, hv, hS⟩
    simp only [WP.spec_ok]
    exact ⟨hnf, σ', hm, hR4.frame hP hf hv, hS⟩
  unfold notification.receive_signal
  step
  rw [st_post, epState_eq] at *
  rcases hst with hst | hst
  · simp only [hst, ↓reduceIte]
    exact key
  · simp only [hst, ntfn_consts.1, ntfn_consts.2.1, show (1#u64 : U64) ≠ 0#u64 by decide, ↓reduceIte]
    exact key

end

end

end Fl4Proofs.P3.Notif
