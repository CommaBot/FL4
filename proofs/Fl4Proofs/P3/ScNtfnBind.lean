/-
P3 (DESIGN.md §9), scheduling contexts: **SchedContext `Bind` and
`UnbindObject` for notifications** (l4v `sched_context_bind_ntfn`,
`sched_context_unbind_ntfn`).

* `NtfnStateRel.set_sc`, `SchedRel.set_ntfn_sc`: writing a notification's SC
  word (an `NtfnStepW` step, which the scheduler relation does not read).
* `SchedRel.set_sc_ntfn`: writing an SC's notification word.
* `Inv.updNtfn`: replacing a notification keeps `Inv` if its SC exists.
* `bind_ntfn_refines`, `unbind_ntfn_refines`, ending in `Inv` and keeping
  `ActIdle`.
-/
import Fl4Proofs.P3.ScBind
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

/-- **Replacing a notification keeps `Inv`**, if its SC (if any) exists. -/
theorem Inv.updNtfn {σ : State Unit} (h : Inv σ) {n : ObjRef} {x x' : Notification}
    (hk : σ.kheap n = some (.notification x))
    (hsc : ∀ p, x'.ntfnSc = some p → ∃ y m, σ.kheap p = some (.schedContext y m)) :
    Inv (updK σ n (.notification x')) := by
  set σ' := updK σ n (.notification x')
  have ko : ∀ q, q ≠ n → σ'.kheap q = σ.kheap q := fun q hq => by simp [σ', updK, hq]
  have kn : σ'.kheap n = some (.notification x') := by simp [σ', updK]
  have kt : ∀ q y, σ'.kheap q = some (.tcb y) ↔ σ.kheap q = some (.tcb y) := by
    intro q y
    by_cases e : q = n
    · subst e; rw [kn, hk]; simp
    · rw [ko q e]
  have ks : ∀ q y m, σ'.kheap q = some (.schedContext y m) ↔ σ.kheap q = some (.schedContext y m) := by
    intro q y m
    by_cases e : q = n
    · subst e; rw [kn, hk]; simp
    · rw [ko q e]
  have rt : ∀ u ∈ σ.releaseQueue, specRt σ' u = specRt σ u := by
    intro u hu
    obtain ⟨xu, scp, yu, nu, h1, h2, -, h4, h5⟩ := h.rel u hu
    have hne := h.ne scp yu nu h4 h5
    rw [specRt_eq ((kt _ _).2 h1) h2 ((ks _ _ _).2 h4) hne, specRt_eq h1 h2 h4 hne]
  refine ⟨fun d q u hu => ?_, fun u hu => ?_, ?_, fun u y hy hc => ?_, fun q y m hy => ?_,
    fun u y q hy hq => ?_, fun q y q' hy hq => ?_, fun q y m hy => ?_, fun q y m hy => ?_⟩
  · obtain ⟨xu, scp, yu, nu, h1, h2, h3, h4, h5⟩ := h.rq d q u hu
    exact ⟨xu, scp, yu, nu, (kt _ _).2 h1, h2, h3, (ks _ _ _).2 h4, h5⟩
  · obtain ⟨xu, scp, yu, nu, h1, h2, h3, h4, h5⟩ := h.rel u hu
    exact ⟨xu, scp, yu, nu, (kt _ _).2 h1, h2, h3, (ks _ _ _).2 h4, h5⟩
  · show σ.releaseQueue.Pairwise _
    refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab => ?_) h.sorted
    rw [rt a ha, rt b hb]; exact hab
  · intro x' scp yu nu h1 h2 h3 h4 h5
    exact h.rd u y ((kt _ _).1 hy) hc x' scp yu nu ((kt _ _).1 h1) h2 ((ks _ _ _).1 h3) h4 h5
  · exact h.refills q y m ((ks _ _ _).1 hy)
  · obtain ⟨yq, mq, h1, h2⟩ := h.back u y q ((kt _ _).1 hy) hq
    exact ⟨yq, mq, (ks _ _ _).2 h1, h2⟩
  · by_cases e : q = n
    · subst e; rw [kn] at hy; cases hy
      obtain ⟨yq, mq, h1⟩ := hsc q' hq
      exact ⟨yq, mq, (ks _ _ _).2 h1⟩
    · rw [ko q e] at hy
      obtain ⟨yq, mq, h1⟩ := h.ntfnSc q y q' hy hq
      exact ⟨yq, mq, (ks _ _ _).2 h1⟩
  · exact h.ne q y m ((ks _ _ _).1 hy)
  · exact h.rr q y m ((ks _ _ _).1 hy)

/-- Replacing a notification keeps the TCBs and SCs. -/
theorem TKeepE.updNtfn (E : ObjRef → Prop) {σ : State Unit} {n : ObjRef} {x : Notification}
    (hk : σ.kheap n = some (.notification x)) (x' : Notification) :
    TKeepE E σ (updK σ n (.notification x')) := by
  refine ⟨fun q y _ hy => ?_, fun q y m hy => ⟨y, ?_, rfl⟩⟩
  · have : q ≠ n := by rintro rfl; rw [hk] at hy; cases hy
    simp [updK, this, hy]
  · have : q ≠ n := by rintro rfl; rw [hk] at hy; cases hy
    simp [updK, this, hy]

theorem setNtfnSc_eq {σ : State Unit} {p : ObjRef} {x : Notification} (v : Option ObjRef)
    (hk : σ.kheap p = some (.notification x)) :
    setNtfnObjRef (Z := Unit) ntfnScUpdate p v σ =
      ({((), updK σ p (.notification { x with ntfnSc := v }))}, False) := by
  show updateSkObjRef KernelObject.notification ntfnScUpdate p v σ = _
  unfold updateSkObjRef
  rw [nd_bind_one (getNotification_eq hk)]
  exact setNotification_eq _ hk

end Spec

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

theorem obj.Ntfn.set_sc.spec2 (s : S) (n : obj.Ntfn) (v : U64) :
    obj.Ntfn.set_sc st n s v ⦃ s' => s' = L.wr s (nScA n) v ⦄ := by
  unfold obj.Ntfn.set_sc; step*; simp_all [nScA]
theorem obj.Sc.set_ntfn.spec2 (s : S) (sc : obj.Sc) (v : U64) :
    obj.Sc.set_ntfn st sc s v ⦃ s' => s' = L.wr s (scW sc 40#u64) v ⦄ := by
  unfold obj.Sc.set_ntfn; step*; simp_all [scW, layout.sc.NTFN]
theorem obj.Sc.ntfn.spec2 (s : S) (sc : obj.Sc) :
    obj.Sc.ntfn st sc s ⦃ v => v = L.mem s (scW sc 40#u64) ⦄ := by
  unfold obj.Sc.ntfn; step*; simp_all [scW, layout.sc.NTFN]

/-- `ntfn_obj` reads only the queue, state and badge words. -/
theorem NtfnObjRel.frame_sc {m m' : U64 → U64} {T : Set U64} {n : U64} {o : Fl4Spec.Ntfn}
    (h : NtfnObjRel m T n o) (hh : m' (epHeadA n) = m (epHeadA n)) (ht : m' (epTSA n) = m (epTSA n))
    (hb : m' (nBadgeA n) = m (nBadgeA n))
    (hy : ∀ y ∈ T, y.bv ∈ o.ntfnQueue → MemberEq m m' y) : NtfnObjRel m' T n o := by
  have hs : stOf m' n = stOf m n := by unfold stOf; rw [ht]
  have hq : qOf m' n = qOf m n := by unfold qOf; rw [hh, ht]
  cases o with
  | idleNtfn =>
    obtain ⟨h1, h2⟩ := h
    exact ⟨hs ▸ h1, hq ▸ queueRel_congr_links h2 (by simp)⟩
  | activeNtfn b =>
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨hs ▸ h1, hq ▸ queueRel_congr_links h2 (by simp), hb ▸ h3⟩
  | waitingNtfn q =>
    obtain ⟨h1, xs, hne, rfl, h2, h3⟩ := h
    have hy' : ∀ y ∈ xs, MemberEq m m' y := fun y hyx =>
      hy y (h2.mem y hyx) (by simp only [Fl4Spec.Ntfn.ntfnQueue]; exact List.mem_map_of_mem hyx)
    refine ⟨hs ▸ h1, xs, hne, rfl, hq ▸ queueRel_congr_links h2 (fun y hyx => (hy' y hyx).2.2),
      fun y hyx => ?_⟩
    obtain ⟨e1, e2⟩ := h3 y hyx
    exact ⟨(hy' y hyx).1 ▸ e1, (hy' y hyx).2.1 ▸ e2⟩

/-- **Writing a notification's SC word** keeps the notification relation. -/
theorem NtfnStateRel.set_sc {N T : Set U64} {s : S} {σ : Fl4Spec.State Unit}
    (hR : NtfnStateRel N T (L.mem s) σ) (hP : NPlaced T N) {n : U64} (hn : n ∈ N)
    {x : Fl4Spec.Notification} (hk : σ.kheap n.bv = some (.notification x)) (v : U64) :
    NtfnStateRel N T (L.mem (L.wr s (nScA n) v)) (updK σ n.bv (.notification { x with ntfnSc := optRef v })) := by
  have hw : NWr st N T n s (L.wr s (nScA n) v) := by
    rw [nScA_eq]; exact nwr_wr hP hn (by simp) (by simp) s v
  have hna := hP.ntfn n hn
  obtain ⟨x0, hk0, hx0⟩ := hR.ntfn n hn
  rw [hk] at hk0; cases hk0
  have ha := (nword hP hn (K := 32#u64) (by simp) (by simp)).1
  have keep : ∀ K : U64, K.val < 40 → K.val % 8 = 0 → K ≠ 32#u64 →
      L.mem (L.wr s (nScA n) v) (core.num.U64.wrapping_add n K) = L.mem s (core.num.U64.wrapping_add n K) := by
    intro K h1 h2 h3
    rw [nScA_eq]
    exact rd_wr_ne ha (nword hP hn h1 h2).1 (nwords_ne hna (by simp) (by omega) (Ne.symm h3))
  have hh : L.mem (L.wr s (nScA n) v) (epHeadA n) = L.mem s (epHeadA n) := by
    rw [epHeadA_eq]; exact keep _ (by simp) (by simp) (by decide)
  have ht : L.mem (L.wr s (nScA n) v) (epTSA n) = L.mem s (epTSA n) := by
    rw [epTSA_eq]; exact keep _ (by simp) (by simp) (by decide)
  have hb : L.mem (L.wr s (nScA n) v) (nBadgeA n) = L.mem s (nBadgeA n) := by
    rw [nBadgeA_eq]; exact keep _ (by simp) (by simp) (by decide)
  have hbd : L.mem (L.wr s (nScA n) v) (nBoundA n) = L.mem s (nBoundA n) := by
    rw [nBoundA_eq]; exact keep _ (by simp) (by simp) (by decide)
  have hsc : L.mem (L.wr s (nScA n) v) (nScA n) = v := by rw [nScA_eq]; exact rd_wr_eq ha
  refine hR.upd_ntfn hn _ hw.ntfn (fun y hy => (hw.tcb y hy).1) (fun y hy _ => (hw.tcb y hy).2) ?_
  refine ⟨NtfnObjRel.frame_sc hx0.obj hh ht hb (fun y hy _ => ⟨(hw.tcb y hy).1.st, (hw.tcb y hy).1.blk, (hw.tcb y hy).2⟩),
    ?_, ?_, ?_⟩
  · rw [hbd]; exact hx0.bound
  · rw [hbd]; exact hx0.bound_mem
  · show optRef v = _; rw [hsc]

/-- **Writing a notification's SC word** keeps the scheduler relation. -/
theorem SchedRel.set_ntfn_sc {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {n : U64} (hn : n ∈ N) {x : Fl4Spec.Notification}
    (hk : σ.kheap n.bv = some (.notification x)) (x' : Fl4Spec.Notification) (v : U64) :
    SchedRel st N T C c (L.wr s (nScA n) v) (updK σ n.bv (.notification x')) := by
  have hw : NWr st N T n s (L.wr s (nScA n) v) := by
    rw [nScA_eq]; exact nwr_wr hS.placed hn (by simp) (by simp) s v
  refine hS.stableW hw.foot ⟨rfl, rfl, fun q => ?_⟩
  by_cases e : q = n.bv
  · subst e; exact Or.inr (Or.inl ⟨x, x', hk, by simp [updK]⟩)
  · exact Or.inl (by simp [updK, e])

/-- Writing an SC's notification word. -/
theorem SchedRel.set_sc_ntfn {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {sc : U64} (hsc : sc ∈ C) {x : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap sc.bv = some (.schedContext x n)) (v : U64) :
    SchedRel st N T C c (L.wr s (scW sc 40#u64) v) (updSc σ sc.bv { x with scNtfn := optRef v } n) ∧
      FootEq N T (L.mem s) (L.mem (L.wr s (scW sc 40#u64) v)) ∧
      KView σ (updSc σ sc.bv { x with scNtfn := optRef v } n) := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x', n', hk', hx⟩ := hs.scs sc hsc
  rw [hk] at hk'; cases hk'
  obtain ⟨hst, ep, em, hw, hv, hwr⟩ := hx.wr_hdr (K := 40#u64) (by simp [HdrK]) v
  have hx' : ScRelW st σ.idleSc (L.wr s (scW sc 40#u64) v) sc { x with scNtfn := optRef v } n :=
    ⟨hx.pl, by rw [ep]; exact hx.period, by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.consumed, by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.tcb, by rw [hv], by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.badge, by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.yieldFrom, by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.sporadic, fun h0 => by rw [em]; exact hx.spor (by rwa [hw _ (by simp) (by simp) (by decide)] at h0), fun h0 => by rw [em]; exact hx.idle h0, by rw [em]; exact hx.max, fun h0 => ScRel1.ofWF (hst (by rwa [em] at h0)).1 (by rw [ep]; exact hx.period) (by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.consumed) (by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.tcb) (by rw [hv]) (by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.badge) (by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.yieldFrom) (by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.sporadic) (by rw [em]; exact hx.max) (by rw [(hst (by rwa [em] at h0)).2]; exact (hx.act (by rwa [em] at h0)).refills)⟩
  exact ⟨hS.sc_updateW hsc hk (hwr.mono fun b hb => hx.in_obj hb) (hw _ (by simp) (by simp) (by decide)) _ hx',
    scin_footEq hS hsc hwr, KView.of_sc hk⟩

/-- `NSC` after a notification's SC changes to one of `C` (or none). -/
theorem NSC.updNtfn {N C : Set U64} {σ : Fl4Spec.State Unit} (h : NSC N C σ) {n : Fl4Spec.ObjRef}
    {x' : Fl4Spec.Notification} (hx : ∀ p, x'.ntfnSc = some p → ∃ sc ∈ C, sc.bv = p) :
    NSC N C (updK σ n (.notification x')) := by
  intro m hm x q hxk hq
  by_cases e : m.bv = n
  · subst e; simp [updK] at hxk; subst hxk; exact hx q hq
  · simp only [updK_kheap, Function.update_of_ne e] at hxk; exact h m hm x q hxk hq

/-- **`bind_ntfn` refines `sched_context_bind_ntfn`.** -/
theorem bind_ntfn_refines {N T C : Set U64} {c : U64} (s : S) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    {p : U64} (hp : p ∈ C) (hp0 : p ≠ 0#u64) {y : Fl4Spec.SchedContext} {m : Nat}
    (hk : σ.kheap p.bv = some (.schedContext y m)) {n : U64} (hn : n ∈ N) (hn0 : n ≠ 0#u64)
    {x : Fl4Spec.Notification} (hkn : σ.kheap n.bv = some (.notification x)) :
    schedcontext.bind_ntfn st s p n ⦃ s' => ∃ σ',
      Fl4Spec.schedContextBindNtfn (Z := Unit) p.bv n.bv σ = ({((), σ')}, False) ∧
      SchedRel st N T C c s' σ' ∧ NtfnStateRel N T (L.mem s') σ' ∧ NSC N C σ' ∧ Inv σ' ∧
      (ActIdle σ → ActIdle σ') ∧ WritesIn st s s' (KFoot st T N C c s σ) ⦄ := by
  have hP := hS.placed
  have hnp : n.bv ≠ p.bv := fun e => by rw [e, hk] at hkn; cases hkn
  have hna := hP.ntfn n hn
  have hnsc : nScA n = core.num.U64.wrapping_add n 32#u64 := by unfold nScA layout.ntfn.SC; rfl
  have hw1 : WritesIn st s (L.wr s (nScA n) p) (KFoot st T N C c s σ) := by
    rw [hnsc]
    refine (writesIn_wr (st := st) (s := s) (v := p) (nfield_aligned hna (K := 32#u64) (by simp) (by simp))).mono
      fun b hb => ?_
    subst hb
    exact KFoot.of_nw ⟨n, hn, by rw [nfield_val hna (by simp)]; simp, by rw [nfield_val hna (by simp)]; simp⟩
  have hal40 : Aligned (scW p 40#u64) := by
    obtain ⟨Q0, R0, -, hs0⟩ := hS.lists
    obtain ⟨x0, n0, -, hx0⟩ := hs0.scs p hp; exact (hx0.hdr (K := 40#u64) (by simp) (by simp)).1
  have hsw40 := sw_hdr hS hp (K := 40#u64) (by simp) (by simp) (by decide)
  unfold schedcontext.bind_ntfn
  refine WP.spec_bind (obj.Ntfn.set_sc.spec2 s n p) ?_
  rintro s1 rfl
  have hR1 := NtfnStateRel.set_sc hR hP hn hkn p
  have hS1 := hS.set_ntfn_sc hn hkn { x with ntfnSc := optRef p } p
  rw [optRef_ne hp0] at hR1 hS1
  set σ1 := updK σ n.bv (.notification { x with ntfnSc := some p.bv }) with hσ1
  have hk1 : σ1.kheap p.bv = some (.schedContext y m) := by simp [σ1, updK, Ne.symm hnp, hk]
  have hI1 : Inv σ1 := hI.updNtfn hkn (fun q hq => by cases hq; exact ⟨y, m, hk⟩)
  have hN1 : NSC N C σ1 := hN.updNtfn (fun q hq => by cases hq; exact ⟨p, hp, rfl⟩)
  refine WP.spec_mono (obj.Sc.set_ntfn.spec2 _ p n) ?_
  rintro s2 rfl
  obtain ⟨hS2, hf2, hK2⟩ := hS1.set_sc_ntfn hp hk1 n
  rw [optRef_ne hn0] at hS2 hK2
  refine ⟨_, ?_, hS2, hR1.frame hS1.placed hf2 hK2, hN1.updSc, hI1.scFields hk1 rfl rfl rfl rfl, fun hA => ?_,
    WritesIn.kfoot_sw hw1 ((writesIn_wr hal40).mono fun b hb => hb ▸ hsw40)⟩
  · unfold Fl4Spec.schedContextBindNtfn
    rw [nd_bind_one (setNtfnSc_eq _ hkn)]
    exact updateSchedContext_eq hk1 _
  · have hA1 : ActIdle σ1 := hA.keepE (E := fun _ => False) (TKeepE.updNtfn _ hkn _) (fun u hu => Or.inl hu)
      (Or.inl rfl) rfl (fun _ _ h => h) id
    exact hA1.keepE (E := fun _ => False) (TKeepE.updSc _ hk1 rfl) (fun u hu => Or.inl hu) (Or.inl rfl) rfl
      (fun _ _ h => h) id

/-- **`unbind_ntfn` refines `sched_context_unbind_ntfn`**, for an SC whose
notification (if any) is one of `N`. -/
theorem unbind_ntfn_refines {N T C : Set U64} {c : U64} (s : S) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    {p : U64} (hp : p ∈ C) (hp0 : p ≠ 0#u64) {y : Fl4Spec.SchedContext} {m : Nat}
    (hk : σ.kheap p.bv = some (.schedContext y m)) (hbn : ∀ n : U64, y.scNtfn = some n.bv → n ∈ N) :
    schedcontext.unbind_ntfn st s p ⦃ s' => ∃ σ',
      Fl4Spec.schedContextUnbindNtfn (Z := Unit) p.bv σ = ({((), σ')}, False) ∧
      SchedRel st N T C c s' σ' ∧ NtfnStateRel N T (L.mem s') σ' ∧ NSC N C σ' ∧ Inv σ' ∧
      (ActIdle σ → ActIdle σ') ∧ WritesIn st s s' (fun b => NW N b ∨ b = scW p 40#u64) ∧ CKeep σ σ' ⦄ := by
  have hP := hS.placed
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x', n', hk', hx⟩ := hs.scs p hp
  rw [hk] at hk'; cases hk'
  have hg : Fl4Spec.getScObjRef (Z := Unit) Fl4Spec.SchedContext.scNtfn p.bv σ = ({(y.scNtfn, σ)}, False) := by
    unfold Fl4Spec.getScObjRef; rw [nd_bind_one (getSchedContext_eq hk)]; rfl
  unfold schedcontext.unbind_ntfn
  step with obj.Sc.is_null.spec' as ⟨b, hb⟩
  simp only [hb, hp0, decide_false, Bool.false_eq_true, ↓reduceIte]
  step with obj.Sc.ntfn.spec2 as ⟨i, hi⟩
  have hyi : y.scNtfn = optRef i := by rw [hx.ntfn, hi]
  by_cases hi0 : i = 0#u64
  · subst hi0
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    refine ⟨σ, ?_, hS, hR, hN, hI, id, WritesIn.refl _ _, CKeep.refl σ⟩
    unfold Fl4Spec.schedContextUnbindNtfn
    rw [nd_bind_one hg, hyi, optRef_zero]; rfl
  have hne : (i != 0#u64) = true := by simpa using hi0
  simp only [hne, ↓reduceIte]
  have hyn : y.scNtfn = some i.bv := by rw [hyi, optRef_ne hi0]
  have hn := hbn i hyn
  obtain ⟨x, hkn, -⟩ := hR.ntfn i hn
  have hnp : i.bv ≠ p.bv := fun e => by rw [e, hk] at hkn; cases hkn
  refine WP.spec_bind (obj.Ntfn.set_sc.spec2 s i 0#u64) ?_
  rintro s1 rfl
  have hR1 := NtfnStateRel.set_sc hR hP hn hkn 0#u64
  have hS1 := hS.set_ntfn_sc hn hkn { x with ntfnSc := optRef 0#u64 } 0#u64
  rw [optRef_zero] at hR1 hS1
  set σ1 := updK σ i.bv (.notification { x with ntfnSc := none }) with hσ1
  have hk1 : σ1.kheap p.bv = some (.schedContext y m) := by simp [σ1, updK, Ne.symm hnp, hk]
  have hI1 : Inv σ1 := hI.updNtfn hkn (fun q hq => by cases hq)
  have hN1 : NSC N C σ1 := hN.updNtfn (fun q hq => by cases hq)
  refine WP.spec_mono (obj.Sc.set_ntfn.spec2 _ p 0#u64) ?_
  rintro s2 rfl
  obtain ⟨hS2, hf2, hK2⟩ := hS1.set_sc_ntfn hp hk1 0#u64
  rw [optRef_zero] at hS2 hK2
  have hw1 : WritesIn st s (L.wr s (nScA i) 0#u64) (NW N) := by
    obtain ⟨ha, -⟩ := nword (T := T) hP hn (K := 32#u64) (by simp) (by simp)
    rw [← nScA_eq] at ha
    have hv : (nScA i).val = i.val + 32 := by rw [nScA_eq, nfield_val (hP.ntfn i hn) (by simp)]; rfl
    exact (writesIn_wr ha).mono fun b hb => ⟨i, hn, by rw [hb, hv]; omega, by rw [hb, hv]; omega⟩
  have ha40 := (hx.hdr (K := 40#u64) (by simp) (by simp)).1
  have hw : WritesIn st s (L.wr (L.wr s (nScA i) 0#u64) (scW p 40#u64) 0#u64)
      (fun b => NW N b ∨ b = scW p 40#u64) :=
    (hw1.trans (writesIn_wr ha40)).mono fun b hb => hb
  refine ⟨_, ?_, hS2, hR1.frame hS1.placed hf2 hK2, hN1.updSc, hI1.scFields hk1 rfl rfl rfl rfl, fun hA => ?_, hw,
    (CKeep.updOther hkn (fun _ _ e => by cases e) (fun _ e => by cases e) (fun _ _ e => by cases e)).trans
      (CKeep.updSc (y' := { y with scNtfn := none }) hk1 rfl)⟩
  · unfold Fl4Spec.schedContextUnbindNtfn
    rw [nd_bind_one hg, hyn]
    show (Fl4Spec.setNtfnObjRef Fl4Spec.ntfnScUpdate i.bv none >>= _) σ = _
    rw [nd_bind_one (setNtfnSc_eq _ hkn)]
    exact updateSchedContext_eq hk1 _
  · have hA1 : ActIdle σ1 := hA.keepE (E := fun _ => False) (TKeepE.updNtfn _ hkn _) (fun u hu => Or.inl hu)
      (Or.inl rfl) rfl (fun _ _ h => h) id
    exact hA1.keepE (E := fun _ => False) (TKeepE.updSc _ hk1 rfl) (fun u hu => Or.inl hu) (Or.inl rfl) rfl
      (fun _ _ h => h) id

/-- `unbind_ntfn_refines` without the invariants (and their posts). -/
theorem unbind_ntfn_refines0 {N T C : Set U64} {c : U64} (s : S) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ)
    {p : U64} (hp : p ∈ C) (hp0 : p ≠ 0#u64) {y : Fl4Spec.SchedContext} {m : Nat}
    (hk : σ.kheap p.bv = some (.schedContext y m)) (hbn : ∀ n : U64, y.scNtfn = some n.bv → n ∈ N) :
    schedcontext.unbind_ntfn st s p ⦃ s' => ∃ σ',
      Fl4Spec.schedContextUnbindNtfn (Z := Unit) p.bv σ = ({((), σ')}, False) ∧
      SchedRel st N T C c s' σ' ∧ NtfnStateRel N T (L.mem s') σ' ∧
      WritesIn st s s' (fun b => NW N b ∨ b = scW p 40#u64) ∧ CKeep σ σ' ⦄ := by
  have hP := hS.placed
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x', n', hk', hx⟩ := hs.scs p hp
  rw [hk] at hk'; cases hk'
  have hg : Fl4Spec.getScObjRef (Z := Unit) Fl4Spec.SchedContext.scNtfn p.bv σ = ({(y.scNtfn, σ)}, False) := by
    unfold Fl4Spec.getScObjRef; rw [nd_bind_one (getSchedContext_eq hk)]; rfl
  unfold schedcontext.unbind_ntfn
  step with obj.Sc.is_null.spec' as ⟨b, hb⟩
  simp only [hb, hp0, decide_false, Bool.false_eq_true, ↓reduceIte]
  step with obj.Sc.ntfn.spec2 as ⟨i, hi⟩
  have hyi : y.scNtfn = optRef i := by rw [hx.ntfn, hi]
  by_cases hi0 : i = 0#u64
  · subst hi0
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    refine ⟨σ, ?_, hS, hR, WritesIn.refl _ _, CKeep.refl σ⟩
    unfold Fl4Spec.schedContextUnbindNtfn
    rw [nd_bind_one hg, hyi, optRef_zero]; rfl
  have hne : (i != 0#u64) = true := by simpa using hi0
  simp only [hne, ↓reduceIte]
  have hyn : y.scNtfn = some i.bv := by rw [hyi, optRef_ne hi0]
  have hn := hbn i hyn
  obtain ⟨x, hkn, -⟩ := hR.ntfn i hn
  have hnp : i.bv ≠ p.bv := fun e => by rw [e, hk] at hkn; cases hkn
  refine WP.spec_bind (obj.Ntfn.set_sc.spec2 s i 0#u64) ?_
  rintro s1 rfl
  have hR1 := NtfnStateRel.set_sc hR hP hn hkn 0#u64
  have hS1 := hS.set_ntfn_sc hn hkn { x with ntfnSc := optRef 0#u64 } 0#u64
  rw [optRef_zero] at hR1 hS1
  set σ1 := updK σ i.bv (.notification { x with ntfnSc := none }) with hσ1
  have hk1 : σ1.kheap p.bv = some (.schedContext y m) := by simp [σ1, updK, Ne.symm hnp, hk]
  refine WP.spec_mono (obj.Sc.set_ntfn.spec2 _ p 0#u64) ?_
  rintro s2 rfl
  obtain ⟨hS2, hf2, hK2⟩ := hS1.set_sc_ntfn hp hk1 0#u64
  rw [optRef_zero] at hS2 hK2
  have hw1 : WritesIn st s (L.wr s (nScA i) 0#u64) (NW N) := by
    obtain ⟨ha, -⟩ := nword (T := T) hP hn (K := 32#u64) (by simp) (by simp)
    rw [← nScA_eq] at ha
    have hv : (nScA i).val = i.val + 32 := by rw [nScA_eq, nfield_val (hP.ntfn i hn) (by simp)]; rfl
    exact (writesIn_wr ha).mono fun b hb => ⟨i, hn, by rw [hb, hv]; omega, by rw [hb, hv]; omega⟩
  have ha40 := (hx.hdr (K := 40#u64) (by simp) (by simp)).1
  have hw : WritesIn st s (L.wr (L.wr s (nScA i) 0#u64) (scW p 40#u64) 0#u64)
      (fun b => NW N b ∨ b = scW p 40#u64) :=
    (hw1.trans (writesIn_wr ha40)).mono fun b hb => hb
  refine ⟨_, ?_, hS2, hR1.frame hS1.placed hf2 hK2, hw,
    (CKeep.updOther hkn (fun _ _ e => by cases e) (fun _ e => by cases e) (fun _ _ e => by cases e)).trans
      (CKeep.updSc (y' := { y with scNtfn := none }) hk1 rfl)⟩
  · unfold Fl4Spec.schedContextUnbindNtfn
    rw [nd_bind_one hg, hyn]
    show (Fl4Spec.setNtfnObjRef Fl4Spec.ntfnScUpdate i.bv none >>= _) σ = _
    rw [nd_bind_one (setNtfnSc_eq _ hkn)]
    exact updateSchedContext_eq hk1 _

end

end

end Fl4Proofs.P3.Sched
