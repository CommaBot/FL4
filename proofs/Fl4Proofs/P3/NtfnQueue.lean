/-
P3 (DESIGN.md §9), notifications: the queue operations with their frames.

P1 (QueueEp.lean) proves that `ntfn_dequeue` and `ntfn_append` refine
`List.erase` and the priority-ordered insertion on the queue. The
refinement proofs also need what they leave alone: here the same proofs,
with the frame added (`ntfn_dequeue_full`, `ntfn_append_full`).
-/
import Fl4Proofs.P3.NtfnSend
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Notif
open fl4_core Fl4Proofs.P1

noncomputable section

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {N T : Set U64}

/-- What writes to `Ep` links of TCBs in `W` leave alone. -/
theorem framed_keeps (hP : NPlaced T N) {W : List U64} (hW : ∀ w ∈ W, w ∈ T) {s s1 : S}
    (hf : Framed st .Ep W s s1) :
    (∀ n ∈ N, NWordsEq (L.mem s) (L.mem s1) n) ∧ (∀ y ∈ T, TFieldsEq (L.mem s) (L.mem s1) y) ∧
    (∀ y ∈ T, y ∉ W → TLinksEq (L.mem s) (L.mem s1) y) ∧ WritesIn st s s1 (NFoot N T) := by
  have hWa : ∀ w ∈ W, TcbAddr w := fun w hw => hP.tcb w (hW w hw)
  have hn : ∀ n ∈ N, ∀ K : U64, K.val < 40 → K.val % 8 = 0 →
      L.mem s1 (core.num.U64.wrapping_add n K) = L.mem s (core.num.U64.wrapping_add n K) := by
    intro n hn K h1 h2
    refine hf.2.2 _ (nword hP hn h1 h2).1 fun w hw => ⟨?_, ?_⟩
    · rw [nextEp_eq]
      exact (tn_ne (hWa w hw) (hP.ntfn n hn) (hP.disj n hn w (hW w hw)) (by simp) (by omega)).symm
    · rw [prevEp_eq]
      exact (tn_ne (hWa w hw) (hP.ntfn n hn) (hP.disj n hn w (hW w hw)) (by simp) (by omega)).symm
  have ht : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K ≠ 3496#u64 → K ≠ 3504#u64 →
      L.mem s1 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := by
    intro y hy K h1 h2 h3 h4
    refine hf.2.2 _ (tword hP hy h1 h2) fun w hw => ⟨?_, ?_⟩
    · rw [nextEp_eq, Ne, tt_eq_iff (hP.tcb y hy) (hWa w hw) h1 (by simp)]; exact fun h => h3 h.2
    · rw [prevEp_eq, Ne, tt_eq_iff (hP.tcb y hy) (hWa w hw) h1 (by simp)]; exact fun h => h4 h.2
  refine ⟨fun n hn' => ⟨?_, ?_, ?_, ?_, ?_⟩, fun y hy => ⟨?_, ?_, ?_, ?_⟩, fun y hy hyW => ⟨?_, ?_⟩, ?_⟩
  · rw [epHeadA_eq]; exact hn n hn' _ (by simp) (by simp)
  · rw [epTSA_eq]; exact hn n hn' _ (by simp) (by simp)
  · rw [nBadgeA_eq]; exact hn n hn' _ (by simp) (by simp)
  · rw [nBoundA_eq]; exact hn n hn' _ (by simp) (by simp)
  · rw [nScA_eq]; exact hn n hn' _ (by simp) (by simp)
  · rw [tStA_eq]; exact ht y hy _ (by simp) (by simp) (by simp) (by simp)
  · rw [tBlockA_eq]; exact ht y hy _ (by simp) (by simp) (by simp) (by simp)
  · rw [badgeRegA_eq]; exact ht y hy _ (by simp) (by simp) (by simp) (by simp)
  · rw [prioA_eq']; exact ht y hy _ (by simp) (by simp) (by simp) (by simp)
  · exact hf.2.2.prev_eq hWa (hP.tcb y hy) (fun _ => hyW)
  · exact hf.2.2.next_eq hWa (hP.tcb y hy) (fun _ => hyW)
  · refine hf.writesIn.mono fun b ⟨w, hw, hb⟩ => Or.inr ⟨w, hW w hw, ?_⟩
    rcases hb with hb | hb
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hb))))

/-- `set_queue` on the notification `n`: the two words written are its head
and tail/state words. -/
theorem set_queue_keeps (hP : NPlaced T N) {n : U64} (hn : n ∈ N) (s : S) (h v : U64) :
    let s' := L.wr (L.wr s (epHeadA n) h) (epTSA n) v
    NWr st N T n s s' ∧ L.mem s' (nBadgeA n) = L.mem s (nBadgeA n) ∧
      L.mem s' (nBoundA n) = L.mem s (nBoundA n) ∧ L.mem s' (nScA n) = L.mem s (nScA n) ∧
      L.mem s' (epHeadA n) = h ∧ L.mem s' (epTSA n) = v := by
  intro s'
  have hna := hP.ntfn n hn
  have h1 : NWr st N T n s (L.wr s (epHeadA n) h) := by rw [epHeadA_eq]; exact nwr_wr hP hn (by simp) (by simp) _ _
  have h2 : NWr st N T n (L.wr s (epHeadA n) h) s' := by
    show NWr st N T n _ (L.wr _ (epTSA n) v); rw [epTSA_eq]; exact nwr_wr hP hn (by simp) (by simp) _ _
  have keep : ∀ K : U64, K.val < 40 → K.val % 8 = 0 → K ≠ 0#u64 → K ≠ 8#u64 →
      L.mem s' (core.num.U64.wrapping_add n K) = L.mem s (core.num.U64.wrapping_add n K) := by
    intro K h1 h2 h3 h4
    show L.mem (L.wr (L.wr s (epHeadA n) h) (epTSA n) v) _ = _
    rw [epTSA_eq, epHeadA_eq,
      rd_wr_ne (nword hP hn (by simp) (by simp)).1 (nword hP hn h1 h2).1 (nwords_ne hna (by simp) (by omega) (Ne.symm h4)),
      rd_wr_ne (nword hP hn (by simp) (by simp)).1 (nword hP hn h1 h2).1 (nwords_ne hna (by simp) (by omega) (Ne.symm h3))]
  refine ⟨h1.trans h2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [nBadgeA_eq]; exact keep _ (by simp) (by simp) (by simp) (by simp)
  · rw [nBoundA_eq]; exact keep _ (by simp) (by simp) (by simp) (by simp)
  · rw [nScA_eq]; exact keep _ (by simp) (by simp) (by simp) (by simp)
  · show L.mem (L.wr (L.wr s (epHeadA n) h) (epTSA n) v) _ = _
    rw [epTSA_eq, epHeadA_eq,
      rd_wr_ne (nword hP hn (by simp) (by simp)).1 (nword hP hn (by simp) (by simp)).1
        (nwords_ne hna (by simp) (by simp) (by simp)), rd_wr_eq (nword hP hn (by simp) (by simp)).1]
  · exact rd_wr_eq (foot_ts hP hn).1

/-- Everything `ntfn_dequeue` and `ntfn_append` keep, for the TCBs `W`
whose links they write. -/
structure QKeeps (st : machine.Store S) [L : LawfulStore st] (N T : Set U64) (n : U64) (W : List U64)
    (s s' : S) : Prop where
  ntfn : ∀ n' ∈ N, n' ≠ n → NWordsEq (L.mem s) (L.mem s') n'
  badge : L.mem s' (nBadgeA n) = L.mem s (nBadgeA n)
  bound : L.mem s' (nBoundA n) = L.mem s (nBoundA n)
  sc : L.mem s' (nScA n) = L.mem s (nScA n)
  tcb : ∀ y ∈ T, TFieldsEq (L.mem s) (L.mem s') y
  links : ∀ y ∈ T, y ∉ W → TLinksEq (L.mem s) (L.mem s') y
  foot : WritesIn st s s' (NFoot N T)

theorem qkeeps_of (hP : NPlaced T N) {n : U64} (hn : n ∈ N) {W : List U64} (hW : ∀ w ∈ W, w ∈ T) {s s1 : S}
    (hf : Framed st .Ep W s s1) (h v : U64) :
    QKeeps st N T n W s (L.wr (L.wr s1 (epHeadA n) h) (epTSA n) v) := by
  obtain ⟨f1, f2, f3, f4⟩ := framed_keeps hP hW hf
  obtain ⟨g, g1, g2, g3, -, -⟩ := set_queue_keeps (st := st) hP hn s1 h v
  exact ⟨fun n' hn' e => (f1 n' hn').trans (g.ntfn n' hn' e), g1.trans (f1 n hn).badge,
    g2.trans (f1 n hn).bound, g3.trans (f1 n hn).sc, fun y hy => (f2 y hy).trans (g.tcb y hy).1,
    fun y hy hyW => (f3 y hy hyW).trans (g.tcb y hy).2,
    (f4.trans g.foot).mono fun _ h => by rcases h with h | h <;> exact h⟩

/-- `ntfn_dequeue` of a member, with its frame. -/
theorem ntfn_dequeue_full (hP : NPlaced T N) (s : S) {n : U64} (hn : n ∈ N) (t : obj.Tcb) (xs : List U64)
    (h : QueueRel (L.mem s) T .Ep (qOf (L.mem s) n) xs) (ht : t ∈ xs) :
    notification.ntfn_dequeue st s n t ⦃ s' =>
      QueueRel (L.mem s') T .Ep (qOf (L.mem s') n) (xs.erase t) ∧
      stOf (L.mem s') n = (if xs.erase t = [] then 0#u64 else stOf (L.mem s) n) ∧
      QKeeps st N T n xs s s' ⦄ := by
  have hE : EpPlaced T n :=
    ⟨by have := (hP.ntfn n hn).align; omega, by have := (hP.ntfn n hn).fits; omega,
     fun t ht => by have := hP.disj n hn t ht; omega⟩
  have hT := hP.tcb
  unfold notification.ntfn_dequeue
  step*
  subst q_post
  refine WP.spec_bind (tcbqueue.remove.rel s .Ep _ t xs hT h ht) ?_
  rintro ⟨q1, s1⟩ h1
  simp only [WP.uncurry'_pair] at h1
  obtain ⟨hr1, hf, -, -⟩ := h1
  have hW : ∀ w ∈ xs, w ∈ T := h.mem
  step*
  · subst s'_post
    have hemp : xs.erase t = [] := (hr1.empty_iff hT).1 (by simpa [b_post] using ‹b = true›)
    obtain ⟨h1, h2⟩ := ep_set_queue (state := obj.NTFN_IDLE) hT hE hr1
    refine ⟨h1, ?_, qkeeps_of hP hn hW hf _ _⟩
    rw [← epState_eq, h2]; simp only [hemp, ↓reduceIte]
    unfold obj.NTFN_IDLE
    exact UScalar.eq_of_val_eq (by simp)
  · subst s'_post
    have hne : xs.erase t ≠ [] := by
      rw [Ne, ← hr1.empty_iff hT]; simpa [b_post] using ‹¬b = true›
    obtain ⟨h1, h2⟩ := ep_set_queue (state := st) hT hE hr1
    refine ⟨h1, ?_, qkeeps_of hP hn hW hf _ _⟩
    rw [← epState_eq, h2]; simp only [hne, ↓reduceIte]; rw [st_post]
    apply eq_of_bv
    simp only [LawfulStore.epState, UScalar.bv_and, BitVec.and_assoc, BitVec.and_self, stOf]

/-- `ntfn_append`, with its frame. -/
theorem ntfn_append_full (hP : NPlaced T N) (s : S) {n : U64} (hn : n ∈ N) (t : obj.Tcb) (xs : List U64)
    (h : QueueRel (L.mem s) T .Ep (qOf (L.mem s) n) xs) (ht : t ∈ T) (hnt : t ∉ xs) :
    notification.ntfn_append st s n t ⦃ s' =>
      QueueRel (L.mem s') T .Ep (qOf (L.mem s') n)
        (insPrio (fun y => L.mem s (prioA y)) (L.mem s (prioA t)) t xs) ∧
      stOf (L.mem s') n = 1#u64 ∧ QKeeps st N T n (t :: xs) s s' ⦄ := by
  have hE : EpPlaced T n :=
    ⟨by have := (hP.ntfn n hn).align; omega, by have := (hP.ntfn n hn).fits; omega,
     fun t ht => by have := hP.disj n hn t ht; omega⟩
  have hT := hP.tcb
  unfold notification.ntfn_append
  step*
  subst q_post
  refine WP.spec_bind (tcbqueue.append_by_prio.rel s .Ep _ t xs hT h ht hnt) ?_
  rintro ⟨q1, s1⟩ h1
  simp only [WP.uncurry'_pair] at h1
  obtain ⟨hr1, hf⟩ := h1
  have hW : ∀ w ∈ t :: xs, w ∈ T := by
    intro w hw; rcases List.mem_cons.1 hw with rfl | hw; exacts [ht, h.mem w hw]
  step*
  subst_vars
  obtain ⟨h1, h2⟩ := ep_set_queue (state := obj.NTFN_WAITING) hT hE hr1
  refine ⟨h1, ?_, qkeeps_of hP hn hW hf _ _⟩
  rw [← epState_eq, h2]
  unfold obj.NTFN_WAITING
  decide

end

end

end Fl4Proofs.P3.Notif
