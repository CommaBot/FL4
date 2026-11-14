/-
P3 (DESIGN.md §9), scheduling contexts: **popping the head of a call stack**
(`reply_pop`, `reply_remove`'s head case) against l4v `reply_unlink_sc` and
the donation back to the caller.

* `CallRel.pop`: the call-stack relation after the pop, from the written
  words (the SC's `REPLY`, the new head's `NEXT`, the popped reply's `NEXT`
  and `PREV`) and the spec's new `sc_replies` and `reply_sc`; the popped
  reply ends detached and isolated.
-/
import Fl4Proofs.P3.ScCallPushRef
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **The call-stack relation after a pop** of the head `r` of `sc`'s stack. -/
theorem CallRel.pop {R C : Set U64} {m m' : U64 → U64} {σ σ' : Fl4Spec.State Unit} {Lst : U64 → List U64}
    (h : CallRel m R C σ Lst) (hR0 : ∀ d ∈ R, d ≠ 0#u64 ∧ d.val % 2 = 0) {sc r : U64} (hsc : sc ∈ C)
    {rest : List U64} (hL : Lst sc = r :: rest)
    (hmP : ∀ d ∈ R, d ≠ r → m' (rPrevA d) = m (rPrevA d))
    (hmN : ∀ d ∈ R, d ≠ r → rest.head? ≠ some d → m' (rNextA d) = m (rNextA d))
    (hmH : ∀ d, rest.head? = some d → m' (rNextA d) = sc ||| 1#u64)
    (hmPr : m' (rPrevA r) = 0#u64) (hmNr : m' (rNextA r) = 0#u64)
    (hmS : m' (scReplyA sc) = rest.headD 0#u64) (hmS' : ∀ q ∈ C, q ≠ sc → m' (scReplyA q) = m (scReplyA q))
    {y : Fl4Spec.SchedContext} {n : Nat} (hk : σ.kheap sc.bv = some (.schedContext y n))
    (hk' : σ'.kheap sc.bv = some (.schedContext { y with scReplies := y.scReplies.tail } n))
    (hkq : ∀ q ∈ C, q ≠ sc → σ'.kheap q.bv = σ.kheap q.bv)
    {xr : Fl4Spec.Reply} (hkr : σ.kheap r.bv = some (.reply xr))
    (hkr' : σ'.kheap r.bv = some (.reply { xr with replySc := none }))
    (hkh : ∀ d x, rest.head? = some d → σ.kheap d.bv = some (.reply x) →
      σ'.kheap d.bv = some (.reply { x with replySc := some sc.bv }))
    (hkd : ∀ d ∈ R, d ≠ r → rest.head? ≠ some d → σ'.kheap d.bv = σ.kheap d.bv) :
    CallRel m' R C σ' (Function.update Lst sc rest) ∧ Isolated m' R r := by
  set Lst' := Function.update Lst sc rest
  have hL'sc : Lst' sc = rest := by simp [Lst']
  have hL'q : ∀ q, q ≠ sc → Lst' q = Lst q := fun q hq => by simp [Lst', hq]
  obtain ⟨⟨y0, n0, hk0, hy0⟩, hLR, hLnd, hLw⟩ := h.stack sc hsc
  rw [hk] at hk0; cases hk0
  rw [hL] at hLR hLnd hLw
  have hrR : r ∈ R := hLR r (by simp)
  have hrrest : r ∉ rest := (List.nodup_cons.1 hLnd).1
  have hrestnd : rest.Nodup := (List.nodup_cons.1 hLnd).2
  have hmemsc : ∀ d q, q ∈ C → d ∈ Lst q → d ∈ r :: rest → q = sc := fun d q hq h1 h2 =>
    h.excl q hq sc hsc d h1 (by rw [hL]; exact h2)
  have hrq : ∀ q ∈ C, q ≠ sc → r ∉ Lst q := fun q hq hne h' => hne (hmemsc r q hq h' (by simp))
  have hdet_r : Detached C Lst' r := by
    intro q hq h'
    by_cases e : q = sc
    · subst e; rw [hL'sc] at h'; exact hrrest h'
    · rw [hL'q q e] at h'; exact hrq q hq e h'
  -- the old head is the only reply pointing to `sc`; old detached replies stay detached
  have hdetold : ∀ d, Detached C Lst d → Detached C Lst' d := by
    intro d hd q hq h'
    by_cases e : q = sc
    · subst e; rw [hL'sc] at h'; exact hd q hq (by rw [hL]; exact List.mem_cons_of_mem _ h')
    · rw [hL'q q e] at h'; exact hd q hq h'
  have hnh_det : ∀ d, Detached C Lst d → rest.head? ≠ some d := fun d hd h' =>
    hd sc hsc (by rw [hL]; exact List.mem_cons_of_mem _ (List.mem_of_mem_head? h'))
  have hne_r_det : ∀ d, Detached C Lst d → d ≠ r := fun d hd e => hd sc hsc (by rw [hL, e]; simp)
  refine ⟨⟨fun q hq => ?_, fun q hq q' hq' d h1 h2 => ?_, fun d hd => ?_, fun d hd hdd => ?_⟩, ?_⟩
  · by_cases e : q = sc
    · subst e
      refine ⟨⟨_, n, hk', by rw [hL'sc, hy0, hL]; rfl⟩, ?_, ?_, ?_, ?_⟩
      · rw [hL'sc]; exact fun d hd => hLR d (List.mem_cons_of_mem _ hd)
      · rw [hL'sc]; exact hrestnd
      · rw [hL'sc, hmS]
      · rw [hL'sc]; intro i hi
        have hm := List.getElem_mem hi
        have hdR := hLR _ (List.mem_cons_of_mem _ hm)
        have hne : rest[i] ≠ r := fun e' => hrrest (e' ▸ hm)
        obtain ⟨g1, g2⟩ := hLw.2 (i + 1) (by simp; omega)
        refine ⟨?_, ?_⟩
        · rw [hmP _ hdR hne]; simpa using g1
        · cases i with
          | zero =>
            rw [hmH _ (by rw [List.head?_eq_getElem?]; exact List.getElem?_eq_getElem hi)]
          | succ j =>
            have hnh : rest.head? ≠ some rest[j + 1] := by
              intro e'
              rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at e'
              have := (List.nodup_iff_injective_get.1 hrestnd) (a₁ := ⟨j + 1, hi⟩) (a₂ := ⟨0, by omega⟩)
                (by simpa using (Option.some.inj e').symm)
              simp at this
            rw [hmN _ hdR hne hnh]; simpa using g2
    · rw [hL'q q e]
      obtain ⟨⟨yq, nq, hkq0, hyq⟩, hqR, hqnd, hqw⟩ := h.stack q hq
      refine ⟨⟨yq, nq, by rw [hkq q hq e]; exact hkq0, hyq⟩, hqR, hqnd, by rw [hmS' q hq e]; exact hqw.1,
        fun i hi => ?_⟩
      have hm := List.getElem_mem hi
      have hne : (Lst q)[i] ≠ r := fun e' => hrq q hq e (e' ▸ hm)
      have hnh : rest.head? ≠ some (Lst q)[i] := fun e' =>
        e (hmemsc _ q hq hm (List.mem_cons_of_mem _ (List.mem_of_mem_head? e')))
      rw [hmP _ (hqR _ hm) hne, hmN _ (hqR _ hm) hne hnh]; exact hqw.2 i hi
  · have g : ∀ q, q ∈ C → d ∈ Lst' q → d ∈ Lst q := fun q hq hdq => by
      by_cases e : q = sc
      · subst e; rw [hL'sc] at hdq; rw [hL]; exact List.mem_cons_of_mem _ hdq
      · rw [hL'q q e] at hdq; exact hdq
    exact h.excl q hq q' hq' d (g q hq h1) (g q' hq' h2)
  · obtain ⟨x, hkx, hxs⟩ := h.reply d hd
    by_cases e : d = r
    · subst e
      rw [hkr] at hkx; cases hkx
      refine ⟨_, hkr', fun p => ⟨fun hp => (by cases hp), fun ⟨q, hq, hqp, hhd⟩ => ?_⟩⟩
      exact absurd (List.mem_of_mem_head? hhd) (hdet_r q hq)
    · by_cases eh : rest.head? = some d
      · refine ⟨_, hkh d x eh hkx, fun p => ⟨fun hp => ?_, fun ⟨q, hq, hqp, hhd⟩ => ?_⟩⟩
        · cases hp; exact ⟨sc, hsc, rfl, by rw [hL'sc]; exact eh⟩
        · by_cases e' : q = sc
          · subst e'; rw [hqp]
          · rw [hL'q q e'] at hhd
            exact absurd (hmemsc d q hq (List.mem_of_mem_head? hhd)
              (List.mem_cons_of_mem _ (List.mem_of_mem_head? eh))) e'
      · refine ⟨x, by rw [hkd d hd e eh]; exact hkx, fun p => ?_⟩
        rw [hxs p]
        constructor
        · rintro ⟨q, hq, hqp, hhd⟩
          refine ⟨q, hq, hqp, ?_⟩
          by_cases e' : q = sc
          · subst e'; rw [hL] at hhd; simp at hhd; exact absurd hhd.symm e
          · rw [hL'q q e']; exact hhd
        · rintro ⟨q, hq, hqp, hhd⟩
          refine ⟨q, hq, hqp, ?_⟩
          by_cases e' : q = sc
          · subst e'; rw [hL'sc] at hhd; exact absurd hhd eh
          · rw [hL'q q e'] at hhd; exact hhd
  · by_cases e : d = r
    · subst e
      rw [hmNr, hmPr]
      exact ⟨rfl, fun h' => absurd rfl h', fun h' => absurd rfl h'⟩
    · -- an old detached reply
      have hdo : Detached C Lst d := by
        intro q hq hdq
        by_cases e' : q = sc
        · subst e'
          rw [hL] at hdq
          rcases List.mem_cons.1 hdq with rfl | hdq
          · exact e rfl
          · exact hdd q hq (by rw [hL'sc]; exact hdq)
        · exact hdd q hq (by rw [hL'q q e']; exact hdq)
      obtain ⟨t1, t2, t3⟩ := h.det d hd hdo
      rw [hmP d hd e, hmN d hd e (hnh_det d hdo)]
      refine ⟨t1, fun hne => ?_, fun hne => ?_⟩
      · obtain ⟨g1, g2, g3⟩ := t2 hne
        exact ⟨g1, hdetold _ g2, by rw [hmP _ g1 (hne_r_det _ g2)]; exact g3⟩
      · obtain ⟨g1, g2, g3⟩ := t3 hne
        exact ⟨g1, hdetold _ g2, by rw [hmN _ g1 (hne_r_det _ g2) (hnh_det _ g2)]; exact g3⟩
  · -- `r` is isolated
    refine ⟨hmNr, hmPr, fun d hd => ?_⟩
    have hr0 := (hR0 r hrR).1
    by_cases e : d = r
    · subst e; rw [hmNr, hmPr]; exact ⟨fun h' => hr0 h'.symm, fun h' => hr0 h'.symm⟩
    by_cases hdet : Detached C Lst d
    · obtain ⟨-, t2, t3⟩ := h.det d hd hdet
      rw [hmP d hd e, hmN d hd e (hnh_det d hdet)]
      refine ⟨fun h' => ?_, fun h' => ?_⟩
      · have := (t2 (by rw [h']; exact hr0)).2.1; rw [h'] at this; exact hne_r_det r this rfl
      · have := (t3 (by rw [h']; exact hr0)).2.1; rw [h'] at this; exact hne_r_det r this rfl
    · -- `d` is on a stack
      have hq1 : ∀ q : U64, (q ||| 1#u64) ≠ r := by
        intro q h'
        have e1 : (q ||| 1#u64).bv.getLsbD 0 = true := by
          simp only [UScalar.bv_or, BitVec.getLsbD_or, one_bit]; simp
        rw [h', even_bit0 r (hR0 r hrR).2] at e1
        exact absurd e1 (by decide)
      simp only [Detached, not_forall, not_not] at hdet
      obtain ⟨q, hq, hdq⟩ := hdet
      obtain ⟨-, hqR, hqnd, hqw⟩ := h.stack q hq
      by_cases eq : q = sc
      · subst eq
        have hd' : d ∈ rest := by
          rw [hL] at hdq; rcases List.mem_cons.1 hdq with rfl | hd'
          · exact absurd rfl e
          · exact hd'
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hd'
        have hnr : rest[j] ≠ r := e
        have hi : j + 1 < (r :: rest).length := by simp; omega
        refine ⟨?_, ?_⟩
        · by_cases hj0 : j = 0
          · subst hj0
            rw [hmH _ (by rw [List.head?_eq_getElem?]; exact List.getElem?_eq_getElem hj)]
            exact hq1 q
          · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
            have hnh : rest.head? ≠ some rest[k + 1] := by
              intro e'
              rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at e'
              have := (List.nodup_iff_injective_get.1 hrestnd) (a₁ := ⟨k + 1, hj⟩) (a₂ := ⟨0, by omega⟩)
                (by simpa using (Option.some.inj e').symm)
              simp at this
            rw [hmN _ hd hnr hnh]
            have := (hLw.2 (k + 2) (by simp; omega)).2
            simp only [List.getElem_cons_succ] at this
            rw [this]
            show rest.getD k 0#u64 ≠ r
            rw [List.getD_eq_getElem _ _ (by omega)]
            exact fun e' => hrrest (e' ▸ List.getElem_mem _)
        · have := (hLw.2 (j + 1) hi).1
          simp only [List.getElem_cons_succ] at this
          rw [hmP _ hd hnr, this]
          show rest.getD (j + 1) 0#u64 ≠ r
          by_cases hj1 : j + 1 < rest.length
          · rw [List.getD_eq_getElem _ _ hj1]; exact fun e' => hrrest (e' ▸ List.getElem_mem _)
          · rw [List.getD_eq_default _ _ (by omega)]; exact fun e' => hr0 e'.symm
      · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hdq
        have hnr : (Lst q)[i] ≠ r := e
        have hnh : rest.head? ≠ some (Lst q)[i] := fun e' =>
          eq (hmemsc _ q hq hdq (List.mem_cons_of_mem _ (List.mem_of_mem_head? e')))
        rw [hmP _ hd hnr, hmN _ hd hnr hnh]
        obtain ⟨g1, g2⟩ := hqw.2 i hi
        refine ⟨?_, ?_⟩
        · rw [g2]
          cases i with
          | zero => exact hq1 q
          | succ j =>
            show (Lst q).getD j 0#u64 ≠ r
            rw [List.getD_eq_getElem _ _ (by omega)]
            exact fun e' => hrq q hq eq (e' ▸ List.getElem_mem _)
        · rw [g1]
          by_cases hj1 : i + 1 < (Lst q).length
          · rw [List.getD_eq_getElem _ _ hj1]; exact fun e' => hrq q hq eq (e' ▸ List.getElem_mem _)
          · rw [List.getD_eq_default _ _ (by omega)]; exact fun e' => hr0 e'.symm

end

end

end Fl4Proofs.P3.Sched
