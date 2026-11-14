/-
P3 (DESIGN.md §9), scheduling contexts: **removing a reply that is not a
stack's head** (`reply_remove`'s splice) against l4v `reply_unlink_sc`'s
non-head case.

* `CallRel.cut`: a reply `L[k]` (`k ≥ 1`) of `sc`'s stack `L` is cut out
  with the older ones (l4v `takeWhile`); the older ones become detached.
* `CallRel.dsplice`: a detached reply is spliced out of its detached chain.
* Both leave the reply isolated. `scWithReply_some`, `scWithReply_none`:
  l4v `sc_with_reply` from the relation, given that every SC is one of `C`.
-/
import Fl4Proofs.P3.ScCallPopRef
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

theorem The_spec {α : Type} [Nonempty α] {P : α → Prop} (h : ∃! x, P x) : P (The P) := by
  unfold The; rw [dif_pos h]; exact (Classical.choose_spec h).1

theorem scWithReply_some {σ : State Unit} {r p : ObjRef}
    (h : ∀ q, (∃ y n, σ.kheap q = some (.schedContext y n) ∧ r ∈ y.scReplies) ↔ q = p) :
    scWithReply r σ = some p := by
  classical
  unfold scWithReply partialInv
  split_ifs with hu
  · congr 1
    exact (h _).1 (of_decide_eq_true (The_spec hu))
  · exact absurd ⟨p, decide_eq_true ((h p).2 rfl), fun q hq => (h q).1 (of_decide_eq_true hq)⟩ hu

theorem scWithReply_none {σ : State Unit} {r : ObjRef}
    (h : ∀ q y n, σ.kheap q = some (.schedContext y n) → r ∉ y.scReplies) : scWithReply r σ = none := by
  classical
  unfold scWithReply partialInv
  split_ifs with hu
  · obtain ⟨q, hq, -⟩ := hu
    obtain ⟨y, n, hk, hm⟩ := of_decide_eq_true hq
    exact absurd hm (h q y n hk)
  · rfl

end Spec

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **The call-stack relation after splicing out a detached reply** `r`. -/
theorem CallRel.dsplice {R C : Set U64} {m m' : U64 → U64} {σ : Fl4Spec.State Unit} {Lst : U64 → List U64}
    (h : CallRel m R C σ Lst) (hR0 : ∀ d ∈ R, d ≠ 0#u64) (hEv : ∀ d ∈ R, d.val % 2 = 0) {r : U64} (hr : r ∈ R)
    (hdet : Detached C Lst r)
    (hmS : ∀ q ∈ C, m' (scReplyA q) = m (scReplyA q))
    (hmP : ∀ d ∈ R, d ≠ r → d ≠ m (rNextA r) → m' (rPrevA d) = m (rPrevA d))
    (hmN : ∀ d ∈ R, d ≠ r → d ≠ m (rPrevA r) → m' (rNextA d) = m (rNextA d))
    (hmPn : m (rNextA r) ≠ 0#u64 → m' (rPrevA (m (rNextA r))) = 0#u64)
    (hmNp : m (rPrevA r) ≠ 0#u64 → m' (rNextA (m (rPrevA r))) = 0#u64)
    (hmPr : m' (rPrevA r) = 0#u64) (hmNr : m' (rNextA r) = 0#u64) :
    CallRel m' R C σ Lst ∧ Isolated m' R r := by
  obtain ⟨t1, t2, t3⟩ := h.det r hr hdet
  -- the live replies' links
  have hlive : ∀ q ∈ C, ∀ d ∈ Lst q, (m (rNextA d) ≠ r ∧ m (rPrevA d) ≠ r) ∧ d ≠ m (rNextA r) ∧ d ≠ m (rPrevA r) := by
    intro q hq d hd
    obtain ⟨-, hqR, -, hqw⟩ := h.stack q hq
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
    obtain ⟨g1, g2⟩ := hqw.2 i hi
    have hnr : ∀ j (hj : j < (Lst q).length), (Lst q)[j] ≠ r := fun j hj e => hdet q hq (e ▸ List.getElem_mem hj)
    refine ⟨⟨?_, ?_⟩, fun e => ?_, fun e => ?_⟩
    · rw [g2]
      cases i with
      | zero =>
        intro h'
        dsimp only at h'
        have e1 : (q ||| 1#u64).bv.getLsbD 0 = true := by
          simp only [UScalar.bv_or, BitVec.getLsbD_or, one_bit]; simp
        rw [h', even_bit0 r (hEv r hr)] at e1
        exact absurd e1 (by decide)
      | succ j =>
        show (Lst q).getD j 0#u64 ≠ r
        rw [List.getD_eq_getElem _ _ (by omega)]; exact hnr j (by omega)
    · rw [g1]
      by_cases hj : i + 1 < (Lst q).length
      · rw [List.getD_eq_getElem _ _ hj]; exact hnr _ hj
      · rw [List.getD_eq_default _ _ (by omega)]; exact fun e => hR0 r hr e.symm
    · have hne : m (rNextA r) ≠ 0#u64 := fun h0 => hR0 _ (hqR _ (List.getElem_mem hi)) (e.trans h0)
      exact (t2 hne).2.1 q hq (e ▸ List.getElem_mem hi)
    · have hne : m (rPrevA r) ≠ 0#u64 := fun h0 => hR0 _ (hqR _ (List.getElem_mem hi)) (e.trans h0)
      exact (t3 hne).2.1 q hq (e ▸ List.getElem_mem hi)
  -- `r`'s neighbours are detached, so not live
  refine ⟨⟨fun q hq => ?_, h.excl, h.reply, fun d hd hdd => ?_⟩, hmNr, hmPr, fun d hd => ?_⟩
  · obtain ⟨hk, hqR, hqnd, hqw⟩ := h.stack q hq
    refine ⟨hk, hqR, hqnd, by rw [hmS q hq]; exact hqw.1, fun i hi => ?_⟩
    have hm := List.getElem_mem hi
    obtain ⟨⟨-, -⟩, hn1, hp1⟩ := hlive q hq _ hm
    have hnr : (Lst q)[i] ≠ r := fun e => hdet q hq (e ▸ hm)
    rw [hmP _ (hqR _ hm) hnr hn1, hmN _ (hqR _ hm) hnr hp1]; exact hqw.2 i hi
  · by_cases e : d = r
    · subst e; rw [hmNr, hmPr]; exact ⟨rfl, fun h' => absurd rfl h', fun h' => absurd rfl h'⟩
    obtain ⟨s1, s2, s3⟩ := h.det d hd hdd
    refine ⟨?_, fun hne => ?_, fun hne => ?_⟩
    · by_cases ep : d = m (rPrevA r)
      · rw [ep, hmNp (fun h0 => hR0 d hd (ep.trans h0))]; rfl
      · rw [hmN d hd e ep]; exact s1
    · by_cases ep : d = m (rPrevA r)
      · rw [ep, hmNp (fun h0 => hR0 d hd (ep.trans h0))] at hne; exact absurd rfl hne
      rw [hmN d hd e ep] at hne ⊢
      obtain ⟨g1, g2, g3⟩ := s2 hne
      -- the next of `d` is not `r` (else `d` would be `r`'s previous)
      have hnr : m (rNextA d) ≠ r := fun h' => ep (by rw [h'] at g3; exact g3.symm)
      have hnn : m (rNextA d) ≠ m (rNextA r) := fun h' => by
        have := g3; rw [h'] at this
        have h2 := (t2 (fun h0 => hR0 _ g1 (h'.trans h0))).2.2
        exact e (this.symm.trans h2)
      exact ⟨g1, g2, by rw [hmP _ g1 hnr hnn]; exact g3⟩
    · by_cases en : d = m (rNextA r)
      · rw [en, hmPn (fun h0 => hR0 d hd (en.trans h0))] at hne; exact absurd rfl hne
      rw [hmP d hd e en] at hne ⊢
      obtain ⟨g1, g2, g3⟩ := s3 hne
      have hnr : m (rPrevA d) ≠ r := fun h' => en (by rw [h'] at g3; exact g3.symm)
      have hnp : m (rPrevA d) ≠ m (rPrevA r) := fun h' => by
        have := g3; rw [h'] at this
        have h2 := (t3 (fun h0 => hR0 _ g1 (h'.trans h0))).2.2
        exact e (this.symm.trans h2)
      exact ⟨g1, g2, by rw [hmN _ g1 hnr hnp]; exact g3⟩
  · -- nothing links to `r`
    by_cases e : d = r
    · subst e; rw [hmNr, hmPr]; exact ⟨fun h' => hR0 _ hd h'.symm, fun h' => hR0 _ hd h'.symm⟩
    by_cases hdd : Detached C Lst d
    · obtain ⟨s1, s2, s3⟩ := h.det d hd hdd
      refine ⟨?_, ?_⟩
      · by_cases ep : d = m (rPrevA r)
        · rw [ep, hmNp (fun h0 => hR0 d hd (ep.trans h0))]; exact fun h' => hR0 _ hr h'.symm
        · rw [hmN d hd e ep]
          intro h'
          have := (s2 (by rw [h']; exact hR0 _ hr)).2.2
          rw [h'] at this; exact ep this.symm
      · by_cases en : d = m (rNextA r)
        · rw [en, hmPn (fun h0 => hR0 d hd (en.trans h0))]; exact fun h' => hR0 _ hr h'.symm
        · rw [hmP d hd e en]
          intro h'
          have := (s3 (by rw [h']; exact hR0 _ hr)).2.2
          rw [h'] at this; exact en this.symm
    · simp only [Detached, not_forall, not_not] at hdd
      obtain ⟨q, hq, hdq⟩ := hdd
      obtain ⟨⟨h1, h2⟩, hn1, hp1⟩ := hlive q hq d hdq
      rw [hmN d hd e hp1, hmP d hd e hn1]; exact ⟨h1, h2⟩


theorem reply_bit' {r : U64} (h : r.val % 2 = 0) : r &&& 1#u64 = 0#u64 := by
  apply UScalar.eq_of_val_eq
  rw [UScalar.val_and, show (1#u64 : U64).val = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  show r.val % 2 = 0; omega

theorem take_headD (l : List U64) {k : Nat} (hk : 1 ≤ k) : (l.take k).headD 0#u64 = l.headD 0#u64 := by
  cases l with
  | nil => simp
  | cons a l => obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩; rfl

theorem take_head? (l : List U64) {k : Nat} (hk : 1 ≤ k) : (l.take k).head? = l.head? := by
  cases l with
  | nil => simp
  | cons a l => obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩; rfl

theorem nodup_idx {L : List U64} (h : L.Nodup) {i j : Nat} (hi : i < L.length) (hj : j < L.length)
    (e : L[i] = L[j]) : i = j := by
  have := (List.nodup_iff_injective_get.1 h) (a₁ := ⟨i, hi⟩) (a₂ := ⟨j, hj⟩) (by simpa using e)
  simpa using this

theorem odd_ne_even {q r : U64} (h : r.val % 2 = 0) : (q ||| 1#u64) ≠ r := by
  intro h'
  have e1 : (q ||| 1#u64).bv.getLsbD 0 = true := by
    simp only [UScalar.bv_or, BitVec.getLsbD_or, one_bit]; simp
  rw [h', even_bit0 r h] at e1
  exact absurd e1 (by decide)

/-- **The call-stack relation after cutting a stack** at its `k`-th reply `r`
(`k ≥ 1`): the newer replies stay, `r` and the older ones are detached. -/
theorem CallRel.cut {R C : Set U64} {m m' : U64 → U64} {σ σ' : Fl4Spec.State Unit} {Lst : U64 → List U64}
    (h : CallRel m R C σ Lst) (hR0 : ∀ d ∈ R, d ≠ 0#u64) (hEv : ∀ d ∈ R, d.val % 2 = 0) {sc : U64} (hsc : sc ∈ C)
    {k : Nat} (hk1 : 1 ≤ k) (hkl : k < (Lst sc).length)
    (hmS : ∀ q ∈ C, m' (scReplyA q) = m (scReplyA q))
    (hmP : ∀ d ∈ R, d ≠ (Lst sc)[k] → d ≠ (Lst sc)[k - 1] → m' (rPrevA d) = m (rPrevA d))
    (hmN : ∀ d ∈ R, d ≠ (Lst sc)[k] → (∀ h : k + 1 < (Lst sc).length, d ≠ (Lst sc)[k + 1]) →
      m' (rNextA d) = m (rNextA d))
    (hmPn : m' (rPrevA (Lst sc)[k - 1]) = 0#u64)
    (hmNo : ∀ h : k + 1 < (Lst sc).length, m' (rNextA (Lst sc)[k + 1]) = 0#u64)
    (hmPr : m' (rPrevA (Lst sc)[k]) = 0#u64) (hmNr : m' (rNextA (Lst sc)[k]) = 0#u64)
    {y : Fl4Spec.SchedContext} {n : Nat} (hky : σ.kheap sc.bv = some (.schedContext y n))
    (hk' : σ'.kheap sc.bv = some (.schedContext { y with scReplies := ((Lst sc).take k).map UScalar.bv } n))
    (hko : ∀ q, q ≠ sc.bv → σ'.kheap q = σ.kheap q) :
    CallRel m' R C σ' (Function.update Lst sc ((Lst sc).take k)) ∧ Isolated m' R (Lst sc)[k] := by
  set Lst' := Function.update Lst sc ((Lst sc).take k)
  have hL'sc : Lst' sc = (Lst sc).take k := by simp [Lst']
  have hL'q : ∀ q, q ≠ sc → Lst' q = Lst q := fun q hq => by simp [Lst', hq]
  obtain ⟨⟨y0, n0, hk0, hy0⟩, hLR, hLnd, hLw⟩ := h.stack sc hsc
  rw [hky] at hk0; cases hk0
  have hmemL : ∀ i (hi : i < (Lst sc).length), (Lst sc)[i] ∈ Lst sc := fun i hi => List.getElem_mem hi
  have hRL : ∀ i (hi : i < (Lst sc).length), (Lst sc)[i] ∈ R := fun i hi => hLR _ (hmemL i hi)
  have hinj : ∀ i j (hi : i < (Lst sc).length) (hj : j < (Lst sc).length), (Lst sc)[i] = (Lst sc)[j] → i = j :=
    fun i j hi hj e => nodup_idx hLnd hi hj e
  have hneI : ∀ i j (hi : i < (Lst sc).length) (hj : j < (Lst sc).length), i ≠ j → (Lst sc)[i] ≠ (Lst sc)[j] :=
    fun i j hi hj hne e => hne (hinj i j hi hj e)
  -- other stacks hold none of `L`
  have hother : ∀ q ∈ C, q ≠ sc → ∀ d ∈ Lst q, d ∉ Lst sc := fun q hq hne d hd hdL =>
    hne (h.excl q hq sc hsc d hd hdL)
  -- the cut-off replies
  have hdetL : ∀ j (hj : j < (Lst sc).length), k ≤ j → Detached C Lst' (Lst sc)[j] := by
    intro j hj hkj q hq hdq
    by_cases e : q = sc
    · subst q; rw [hL'sc] at hdq
      obtain ⟨i, hi, hie⟩ := List.getElem_of_mem hdq
      rw [List.getElem_take] at hie
      have := hinj i j (by simp at hi; omega) hj hie
      simp at hi; omega
    · rw [hL'q q e] at hdq; exact hother q hq e _ hdq (hmemL j hj)
  have hdetold : ∀ d, Detached C Lst d → Detached C Lst' d := by
    intro d hd q hq h'
    by_cases e : q = sc
    · subst q; rw [hL'sc] at h'; exact hd sc hq (List.mem_of_mem_take h')
    · rw [hL'q q e] at h'; exact hd q hq h'
  have hdet_ne : ∀ d, Detached C Lst d → ∀ j (hj : j < (Lst sc).length), d ≠ (Lst sc)[j] := fun d hd j hj e =>
    hd sc hsc (e ▸ hmemL j hj)
  refine ⟨⟨fun q hq => ?_, fun q hq q' hq' d h1 h2 => ?_, fun d hd => ?_, fun d hd hdd => ?_⟩, ?_⟩
  · by_cases e : q = sc
    · subst q
      refine ⟨⟨_, n, hk', by rw [hL'sc]⟩, ?_, ?_, ?_, ?_⟩
      · rw [hL'sc]; exact fun d hd => hLR d (List.mem_of_mem_take hd)
      · rw [hL'sc]; exact hLnd.sublist (List.take_sublist _ _)
      · rw [hL'sc, hmS sc hq, hLw.1, take_headD _ hk1]
      · rw [hL'sc]; intro i hi
        have hik : i < k := by simp at hi; omega
        have hiL : i < (Lst sc).length := by omega
        rw [List.getElem_take]
        have hnr : (Lst sc)[i] ≠ (Lst sc)[k] := hneI i k hiL hkl (by omega)
        obtain ⟨g1, g2⟩ := hLw.2 i hiL
        refine ⟨?_, ?_⟩
        · by_cases hi1 : i = k - 1
          · subst hi1; rw [hmPn]
            rw [List.getD_eq_default _ _ (by simp; omega)]
          · rw [hmP _ (hRL i hiL) hnr (hneI i (k - 1) hiL (by omega) hi1), g1,
              List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by simp; omega), List.getElem_take]
        · rw [hmN _ (hRL i hiL) hnr (fun h' => hneI i (k + 1) hiL h' (by omega)), g2]
          cases i with
          | zero => rfl
          | succ j =>
            show (Lst sc).getD j 0#u64 = ((Lst sc).take k).getD j 0#u64
            rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by simp; omega), List.getElem_take]
    · rw [hL'q q e]
      obtain ⟨⟨yq, nq, hkq0, hyq⟩, hqR, hqnd, hqw⟩ := h.stack q hq
      refine ⟨⟨yq, nq, by rw [hko _ (bv_ne e)]; exact hkq0, hyq⟩, hqR, hqnd, by rw [hmS q hq]; exact hqw.1,
        fun i hi => ?_⟩
      have hm := List.getElem_mem hi
      have hnL : ∀ j (hj : j < (Lst sc).length), (Lst q)[i] ≠ (Lst sc)[j] := fun j hj e' => hother q hq e _ hm (e' ▸ hmemL j hj)
      rw [hmP _ (hqR _ hm) (hnL k hkl) (hnL (k - 1) (by omega)),
        hmN _ (hqR _ hm) (hnL k hkl) (fun h' => hnL (k + 1) h')]
      exact hqw.2 i hi
  · have g : ∀ q, q ∈ C → d ∈ Lst' q → d ∈ Lst q := fun q hq hdq => by
      by_cases e : q = sc
      · subst q; rw [hL'sc] at hdq; exact List.mem_of_mem_take hdq
      · rw [hL'q q e] at hdq; exact hdq
    exact h.excl q hq q' hq' d (g q hq h1) (g q' hq' h2)
  · obtain ⟨x, hkx, hxs⟩ := h.reply d hd
    have hdsc : d.bv ≠ sc.bv := fun e => by rw [e, hky] at hkx; cases hkx
    refine ⟨x, by rw [hko _ hdsc]; exact hkx, fun p => ?_⟩
    rw [hxs p]
    have hhd : (Lst' sc).head? = (Lst sc).head? := by
      rw [hL'sc, take_head? _ hk1]
    constructor
    · rintro ⟨q, hq, hqp, hhq⟩
      refine ⟨q, hq, hqp, ?_⟩
      by_cases e : q = sc
      · subst q; rw [hhd]; exact hhq
      · rw [hL'q q e]; exact hhq
    · rintro ⟨q, hq, hqp, hhq⟩
      refine ⟨q, hq, hqp, ?_⟩
      by_cases e : q = sc
      · subst q; rw [hhd] at hhq; exact hhq
      · rw [hL'q q e] at hhq; exact hhq
  · by_cases hdL : d ∈ Lst sc
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hdL
      have hkj : k ≤ j := by
        by_contra hlt
        exact hdd sc hsc (by rw [hL'sc]; exact List.mem_iff_getElem.2 ⟨j, by simp; omega, by rw [List.getElem_take]⟩)
      by_cases hjk : j = k
      · subst hjk
        rw [hmNr, hmPr]; exact ⟨rfl, fun h' => absurd rfl h', fun h' => absurd rfl h'⟩
      have hnr : (Lst sc)[j] ≠ (Lst sc)[k] := hneI j k hj hkl hjk
      have hnp : (Lst sc)[j] ≠ (Lst sc)[k - 1] := hneI j (k - 1) hj (by omega) (by omega)
      obtain ⟨g1, g2⟩ := hLw.2 j hj
      rw [hmP _ (hRL j hj) hnr hnp, g1]
      by_cases hj1 : j = k + 1
      · subst hj1
        rw [hmNo hj]
        refine ⟨rfl, fun h' => absurd rfl h', fun hne => ?_⟩
        have hj2 : k + 2 < (Lst sc).length := by
          by_contra h''; rw [List.getD_eq_default _ _ (by omega)] at hne; exact hne rfl
        rw [List.getD_eq_getElem _ _ hj2]
        refine ⟨hRL _ hj2, hdetL _ hj2 (by omega), ?_⟩
        have := (hLw.2 (k + 2) hj2).2
        dsimp only at this
        rw [hmN _ (hRL _ hj2) (hneI _ k hj2 hkl (by omega)) (fun h' => hneI _ (k + 1) hj2 h' (by omega)), this]
        rw [List.getD_eq_getElem _ _ hj]
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        dsimp only at g2
        rw [hmN _ (hRL _ hj) hnr (fun h' => hneI _ (k + 1) hj h' hj1), g2]
        show ((Lst sc).getD j' 0#u64 &&& 1#u64) = 0#u64 ∧ _ ∧ _
        have hj' : j' < (Lst sc).length := by omega
        rw [List.getD_eq_getElem _ _ hj']
        refine ⟨reply_bit' (hEv _ (hRL j' hj')), fun _ => ⟨hRL j' hj', hdetL j' hj' (by omega), ?_⟩, fun hne => ?_⟩
        · rw [hmP _ (hRL j' hj') (hneI j' k hj' hkl (by omega)) (hneI j' (k - 1) hj' (by omega) (by omega)),
            (hLw.2 j' hj').1, List.getD_eq_getElem _ _ hj]
        · have hj2 : j' + 2 < (Lst sc).length := by
            by_contra h''; rw [List.getD_eq_default _ _ (by omega)] at hne; exact hne rfl
          rw [List.getD_eq_getElem _ _ hj2]
          refine ⟨hRL _ hj2, hdetL _ hj2 (by omega), ?_⟩
          have := (hLw.2 (j' + 2) hj2).2
          dsimp only at this
          rw [hmN _ (hRL _ hj2) (hneI _ k hj2 hkl (by omega)) (fun h' => hneI _ (k + 1) hj2 h' (by omega)), this]
          rw [List.getD_eq_getElem _ _ hj]
    · -- an old detached reply
      have hdo : Detached C Lst d := by
        intro q hq hdq
        by_cases e : q = sc
        · subst q; exact hdL hdq
        · exact hdd q hq (by rw [hL'q q e]; exact hdq)
      obtain ⟨t1, t2, t3⟩ := h.det d hd hdo
      rw [hmP d hd (hdet_ne d hdo k hkl) (hdet_ne d hdo (k - 1) (by omega)),
        hmN d hd (hdet_ne d hdo k hkl) (fun h' => hdet_ne d hdo (k + 1) h')]
      refine ⟨t1, fun hne => ?_, fun hne => ?_⟩
      · obtain ⟨g1, g2, g3⟩ := t2 hne
        exact ⟨g1, hdetold _ g2, by rw [hmP _ g1 (hdet_ne _ g2 k hkl) (hdet_ne _ g2 (k - 1) (by omega))]; exact g3⟩
      · obtain ⟨g1, g2, g3⟩ := t3 hne
        exact ⟨g1, hdetold _ g2, by
          rw [hmN _ g1 (hdet_ne _ g2 k hkl) (fun h' => hdet_ne _ g2 (k + 1) h')]; exact g3⟩
  · -- `(Lst sc)[k]` is isolated
    refine ⟨hmNr, hmPr, fun d hd => ?_⟩
    have hr0 : (Lst sc)[k] ≠ 0#u64 := hR0 _ (hRL k hkl)
    by_cases e : d = (Lst sc)[k]
    · rw [e, hmNr, hmPr]; exact ⟨fun h' => hr0 h'.symm, fun h' => hr0 h'.symm⟩
    by_cases hdL : d ∈ Lst sc
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hdL
      have hjk : j ≠ k := fun h' => e (by subst h'; rfl)
      obtain ⟨g1, g2⟩ := hLw.2 j hj
      refine ⟨?_, ?_⟩
      · by_cases hj1 : j = k + 1
        · subst hj1; rw [hmNo hj]; exact fun h' => hr0 h'.symm
        rw [hmN _ (hRL j hj) (hneI j k hj hkl hjk) (fun h' => hneI j (k + 1) hj h' hj1), g2]
        cases j with
        | zero => exact odd_ne_even (hEv _ (hRL k hkl))
        | succ j' =>
          show (Lst sc).getD j' 0#u64 ≠ (Lst sc)[k]
          rw [List.getD_eq_getElem _ _ (by omega)]; exact hneI j' k (by omega) hkl (by omega)
      · by_cases hjp : j = k - 1
        · subst hjp; rw [hmPn]; exact fun h' => hr0 h'.symm
        rw [hmP _ (hRL j hj) (hneI j k hj hkl hjk) (hneI j (k - 1) hj (by omega) hjp), g1]
        by_cases hj1 : j + 1 < (Lst sc).length
        · rw [List.getD_eq_getElem _ _ hj1]; exact hneI (j + 1) k hj1 hkl (by omega)
        · rw [List.getD_eq_default _ _ (by omega)]; exact fun h' => hr0 h'.symm
    · by_cases hdd : Detached C Lst d
      · obtain ⟨-, t2, t3⟩ := h.det d hd hdd
        rw [hmP d hd (hdet_ne d hdd k hkl) (hdet_ne d hdd (k - 1) (by omega)),
          hmN d hd (hdet_ne d hdd k hkl) (fun h' => hdet_ne d hdd (k + 1) h')]
        refine ⟨fun h' => ?_, fun h' => ?_⟩
        · exact hdet_ne _ (t2 (by rw [h']; exact hr0)).2.1 k hkl h'
        · exact hdet_ne _ (t3 (by rw [h']; exact hr0)).2.1 k hkl h'
      · simp only [Detached, not_forall, not_not] at hdd
        obtain ⟨q, hq, hdq⟩ := hdd
        have hne : q ≠ sc := fun e' => hdL (e' ▸ hdq)
        obtain ⟨-, hqR, -, hqw⟩ := h.stack q hq
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hdq
        have hnL : ∀ j (hj : j < (Lst sc).length), (Lst q)[i] ≠ (Lst sc)[j] := fun j hj e' =>
          hother q hq hne _ hdq (e' ▸ hmemL j hj)
        rw [hmP _ hd (hnL k hkl) (hnL (k - 1) (by omega)), hmN _ hd (hnL k hkl) (fun h' => hnL (k + 1) h')]
        obtain ⟨g1, g2⟩ := hqw.2 i hi
        have hrq : ∀ j (hj : j < (Lst q).length), (Lst q)[j] ≠ (Lst sc)[k] := fun j hj e' =>
          hother q hq hne _ (List.getElem_mem hj) (e' ▸ hmemL k hkl)
        refine ⟨?_, ?_⟩
        · rw [g2]
          cases i with
          | zero => exact odd_ne_even (hEv _ (hRL k hkl))
          | succ j' =>
            show (Lst q).getD j' 0#u64 ≠ (Lst sc)[k]
            rw [List.getD_eq_getElem _ _ (by omega)]; exact hrq j' (by omega)
        · rw [g1]
          by_cases hj1 : i + 1 < (Lst q).length
          · rw [List.getD_eq_getElem _ _ hj1]; exact hrq _ hj1
          · rw [List.getD_eq_default _ _ (by omega)]; exact fun h' => hr0 h'.symm

end

end

end Fl4Proofs.P3.Sched
