/-
P3 (DESIGN.md §9), scheduling contexts: **`maybe_return_sched_context`
refines l4v `maybe_return_sc`** (`maybe_return_refines`): when the
notification's SC is the thread's, the thread gives it back (`tcb_sched_context
:= none`, `sc_tcb := none`) and, for the current thread,
`reschedule_required`. The refill hypothesis `ActReady` of the initial state
is needed for the latter (it transfers through the two writes).
-/
import Fl4Proofs.P3.ScReady
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

@[step] theorem obj.Tcb.set_sc.spec' (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_sc st t s v ⦃ s' => s' = L.wr s (scA t) v ⦄ := by
  unfold obj.Tcb.set_sc; step*; simp_all [scA]
@[step] theorem obj.Sc.set_tcb.spec' (s : S) (sc : obj.Sc) (v : U64) :
    obj.Sc.set_tcb st sc s v ⦃ s' => s' = L.wr s (scW sc 24#u64) v ⦄ := by
  unfold obj.Sc.set_tcb; step*; simp_all [scW, layout.sc.TCB]

theorem optRef_inj {a b : U64} : optRef a = optRef b ↔ a = b := by
  constructor
  · intro h
    by_cases ha : a = 0#u64
    · by_cases hb : b = 0#u64
      · rw [ha, hb]
      · rw [ha, optRef_zero, optRef_ne hb] at h; cases h
    · by_cases hb : b = 0#u64
      · rw [hb, optRef_zero, optRef_ne ha] at h; cases h
      · rw [optRef_ne ha, optRef_ne hb] at h; exact eq_of_bv (Option.some.inj h)
  · rintro rfl; rfl

theorem getNtfnSc_eq {σ : Fl4Spec.State Unit} {p : Fl4Spec.ObjRef} {x : Fl4Spec.Notification}
    (hk : σ.kheap p = some (.notification x)) :
    Fl4Spec.getNtfnObjRef (Z := Unit) Fl4Spec.Notification.ntfnSc p σ = ({(x.ntfnSc, σ)}, False) := by
  show Fl4Spec.getSkObjRef Fl4Spec.KernelObject.notification Fl4Spec.Notification.ntfnSc p σ = _
  unfold Fl4Spec.getSkObjRef
  rw [nd_bind_one (getNotification_eq hk)]; rfl

/-- **`maybe_return_sched_context` refines `maybe_return_sc`** (`RecvHyps.returnSc`,
with `ActReady`). -/
theorem maybe_return_refines {N T C : Set U64} {c : U64} (s : S) (σ : Fl4Spec.State Unit)
    (hR : NtfnStateRel N T (L.mem s) σ) (hS : SchedRel st N T C c s σ) (hr : ActReady σ)
    (t n : U64) (ht : t ∈ T) (hn : n ∈ N) :
    TailRef st N T (SchedRel st N T C c) id s σ (notification.maybe_return_sched_context st s n t)
      (Fl4Spec.maybeReturnSc n.bv t.bv) := by
  unfold TailRef
  have hP := hS.placed
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨xn, hkn, hxn⟩ := hR.ntfn n hn
  obtain ⟨xt, hkt, -, -, hsct, -⟩ := hs.tcb t ht
  have hspec0 : ∀ (P : Prop) [Decidable P] (m : Fl4Spec.SMonad Unit Unit),
      Fl4Spec.maybeReturnSc (Z := Unit) n.bv t.bv σ =
        Fl4Spec.NonDet.when (optRef (L.mem s (nScA n)) = optRef (L.mem s (scA t)) ∧
          optRef (L.mem s (nScA n)) ≠ none) (do
          let scPtr ← Fl4Spec.NonDet.assertOpt (optRef (L.mem s (nScA n)))
          Fl4Spec.setTcbObjRef Fl4Spec.tcbSchedContextUpdate t.bv none
          Fl4Spec.setScObjRef Fl4Spec.scTcbUpdate scPtr none
          let ct ← Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curThread
          Fl4Spec.NonDet.when (t.bv = ct) Fl4Spec.rescheduleRequired) σ := by
    intro _ _ _
    unfold Fl4Spec.maybeReturnSc Fl4Spec.getTcbObjRef
    rw [nd_bind_one (getNtfnSc_eq hkn), nd_bind_one (threadGet_eq _ hkt), hxn.sc, hsct]
  have hspec := hspec0 True (pure ())
  have fin : ∀ s' σ', Fl4Spec.maybeReturnSc (Z := Unit) n.bv t.bv σ = ({((), σ')}, False) →
      FootEq N T (L.mem s) (L.mem s') → KView σ σ' → SchedRel st N T C c s' σ' →
      ¬ (Fl4Spec.maybeReturnSc (Z := Unit) n.bv t.bv σ).2 ∧ ∃ σ'', ((), σ'') ∈ (Fl4Spec.maybeReturnSc (Z := Unit)
        n.bv t.bv σ).1 ∧ FootEq N T (L.mem s) (L.mem (id s')) ∧ KView σ σ'' ∧ SchedRel st N T C c (id s') σ'' := by
    intro s' σ' he hf hv hS'
    rw [he]; exact ⟨id, σ', rfl, hf, hv, hS'⟩
  unfold notification.maybe_return_sched_context
  step
  step
  by_cases h0 : i = 0#u64
  · have hb : b = true := by rw [b_post]; simp [h0]
    simp only [hb, ↓reduceIte, WP.spec_ok]
    refine fin s σ ?_ FootEq.rfl' (KView.refl σ) hS
    rw [hspec, ← i_post, h0, optRef_zero]
    simp [Fl4Spec.NonDet.when]; rfl
  · have hb : b = false := by rw [b_post]; simp [h0]
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    step
    by_cases e : i = i1
    · subst e
      rw [ite_t rfl]
      have hi : i = L.mem s (nScA n) := i_post
      have hi1 : i = L.mem s (scA t) := i1_post
      have hscC : i ∈ C := by rw [hi1]; exact hs.scMem t ht (by rw [← hi1]; exact h0)
      obtain ⟨xs, ns, hks, hxs⟩ := hs.scs i hscC
      step
      subst s1_post
      obtain ⟨hS1, hf1, hv1⟩ := hS.set_tcb_sc ht hkt (v := 0#u64) (Or.inl rfl)
      have hks1 : (updK σ t.bv (.tcb { xt with tcbSchedContext := optRef 0#u64 })).kheap i.bv =
          some (.schedContext xs ns) := by
        have : i.bv ≠ t.bv := by intro e'; rw [e', hkt] at hks; cases hks
        simp [updK, this, hks]
      obtain ⟨hS2, hf2, hv2⟩ := hS1.set_sc_tcb hscC hks1 0#u64
      step
      subst s2_post
      set σ1 := updK σ t.bv (.tcb { xt with tcbSchedContext := optRef 0#u64 })
      set σ2 := updSc σ1 i.bv { xs with scTcb := optRef 0#u64 } ns
      have hR2 : NtfnStateRel N T (L.mem (L.wr (L.wr s (scA t) 0#u64) (scW i 24#u64) 0#u64)) σ2 :=
        (hR.frame hP hf1 hv1).frame hP hf2 hv2
      -- the spec, up to the current-thread test
      have hpre : (do
          let scPtr ← Fl4Spec.NonDet.assertOpt (optRef (L.mem s (nScA n)))
          Fl4Spec.setTcbObjRef Fl4Spec.tcbSchedContextUpdate t.bv none
          Fl4Spec.setScObjRef Fl4Spec.scTcbUpdate scPtr none
          let ct ← Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curThread
          Fl4Spec.NonDet.when (t.bv = ct) Fl4Spec.rescheduleRequired) σ =
          Fl4Spec.NonDet.when (t.bv = σ2.curThread) Fl4Spec.rescheduleRequired σ2 := by
        rw [← hi, optRef_ne h0]
        rw [nd_bind_one (show Fl4Spec.NonDet.assertOpt (σ := Fl4Spec.State Unit) (some i.bv) σ = ({(i.bv, σ)}, False)
          from rfl)]
        rw [nd_bind_one (threadSet_eq _ hkt)]
        have e1 : Fl4Spec.tcbSchedContextUpdate (fun _ => none) xt = { xt with tcbSchedContext := optRef 0#u64 } := by
          simp [Fl4Spec.tcbSchedContextUpdate, optRef_zero]
        rw [e1]
        show (Fl4Spec.updateSchedContext i.bv _ >>= _) σ1 = _
        rw [nd_bind_one (updateSchedContext_eq hks1 _)]
        have e2 : Fl4Spec.scTcbUpdate (fun _ => none) xs = { xs with scTcb := optRef 0#u64 } := by
          simp [Fl4Spec.scTcbUpdate, optRef_zero]
        rw [e2, nd_gets_bind]
      have hcond : optRef (L.mem s (nScA n)) = optRef (L.mem s (scA t)) ∧ optRef (L.mem s (nScA n)) ≠ none := by
        rw [← hi, ← hi1]; refine ⟨rfl, ?_⟩; rw [optRef_ne h0]; simp
      have hct2 : σ2.curThread = (nodeW st s c layout.node.CUR_THREAD).bv := hs.curThread
      step with sched.cur_thread.spec'
      step
      have hcpu : L.cpu (L.wr (L.wr s (scA t) 0#u64) (scW i 24#u64) 0#u64) = c := by simp [hc.cur]
      have hcur2 : nodeW st (L.wr (L.wr s (scA t) 0#u64) (scW i 24#u64) 0#u64) c layout.node.CUR_THREAD =
          nodeW st s c layout.node.CUR_THREAD := by
        obtain ⟨Q2, R2, hc2, hs2⟩ := hS2.lists
        exact eq_of_bv (hs2.curThread.symm.trans hct2)
      rw [t1_post, hcpu, hcur2] at b1_post
      by_cases ec : t = nodeW st s c layout.node.CUR_THREAD
      · have hb1 : b1 = true := by rw [b1_post]; exact decide_eq_true ec
        simp only [hb1, ↓reduceIte]
        have hr2 : ActReady σ2 := by
          refine hr.transfer rfl rfl rfl (fun p x hx => ?_) (fun p y m hy => ?_) (fun p => ?_)
          · rw [tcbsOf_eq] at hx
            simp only [σ2, σ1, updSc, updK_kheap, Function.update_apply] at hx
            by_cases ep : p = i.bv
            · simp [ep] at hx
            · by_cases et : p = t.bv
              · subst et; simp [ep] at hx; subst hx; left; simp [optRef_zero]
              · simp only [ep, et, ↓reduceIte] at hx; right; rw [tcbsOf_eq]; exact hx
          · by_cases ep : p = i.bv
            · subst ep; rw [hks] at hy; cases hy
              exact ⟨{ xs with scTcb := optRef 0#u64 }, by simp [σ2, updK], rfl, rfl⟩
            · have et : p ≠ t.bv := by rintro rfl; rw [hkt] at hy; cases hy
              exact ⟨y, by simp [σ2, σ1, updK, ep, et, hy], rfl, rfl⟩
          · simp only [scsOf_eq, σ2, σ1, updSc, updK_kheap, Function.update_apply]
            by_cases ep : p = i.bv
            · subst ep; simp [hks]
            · by_cases et : p = t.bv
              · subst et; simp [ep, hkt]
              · simp [ep, et]
        refine WP.spec_mono (reschedule_required_refines _ σ2 hR2 hS2 hr2) ?_
        rintro s3 ⟨σ3, hrr, hk3, -, hf3, hS3⟩
        refine fin s3 σ3 ?_ (FootEq.trans' (FootEq.trans' hf1 hf2) hf3)
          (KView.trans (KView.trans hv1 hv2) (KView.of_kheap hk3)) hS3
        · rw [hspec, Fl4Spec.NonDet.when, ite_t hcond, hpre, Fl4Spec.NonDet.when,
            ite_t (by rw [hct2, ec])]
          exact hrr
      · have hb1 : b1 = false := by rw [b1_post]; exact decide_eq_false ec
        simp only [hb1, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        refine fin _ σ2 ?_ (FootEq.trans' hf1 hf2) (KView.trans hv1 hv2) hS2
        rw [hspec, Fl4Spec.NonDet.when, ite_t hcond, hpre, Fl4Spec.NonDet.when,
          ite_f (by rw [hct2]; exact bv_ne ec)]
        rfl
    · simp only [e, ↓reduceIte, WP.spec_ok]
      refine fin s σ ?_ FootEq.rfl' (KView.refl σ) hS
      rw [hspec, Fl4Spec.NonDet.when, ite_f]
      · rfl
      · rintro ⟨h1, -⟩
        exact e (by rw [i_post, i1_post]; exact optRef_inj.1 h1)

end

end

end Fl4Proofs.P3.Sched
