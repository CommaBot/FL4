/-
P3 (DESIGN.md §9), endpoints: `ep_append` and `ep_dequeue` with their
frames.

P1 (QueueEp.lean) proves that they refine the priority-ordered insertion
and `List.erase` on the queue; here the same proofs with what they leave
alone: everything but the endpoint's two words and the `Ep` links of the
TCBs involved (`ep_append_full`, `ep_dequeue_full`).
-/
import Fl4Proofs.P3.EpWrite
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T E R : Set U64} {B : Set (U64 × Fl4Spec.Word)}

omit [L : LawfulStore st] in
/-- What the queue operations on `e` leave alone, for the TCBs `W` whose
links they write. -/
def QAgree (T : Set U64) (e : U64) (W : List U64) (m m' : U64 → U64) : Prop :=
  Agree m m' (fun b => ¬ EW e b ∧ ¬ ∃ w ∈ W, TL w b)

theorem framed_agree (hP : EPlaced T E R B) {W : List U64} (hW : ∀ w ∈ W, w ∈ T) {s s1 : S}
    (hf : Framed st .Ep W s s1) :
    Agree (L.mem s) (L.mem s1) (fun b => ¬ ∃ w ∈ W, TL w b) ∧ WritesIn st s s1 (fun b => ∃ w ∈ W, TL w b) := by
  have hWa : ∀ w ∈ W, TcbAddr w := fun w hw => hP.tcb w (hW w hw)
  have key : ∀ b : U64, Aligned b → (¬ ∃ w ∈ W, TL w b) → L.mem s1 b = L.mem s b := by
    intro b hb hn
    refine hf.2.2 b hb fun w hw => ⟨fun e => hn ⟨w, hw, ?_⟩, fun e => hn ⟨w, hw, ?_⟩⟩
    · subst e; exact (a_next (hWa w hw)).2
    · subst e; exact (a_prev (hWa w hw)).2
  exact ⟨key, hf.1, hf.2.1, key⟩

/-- `set_queue` on the endpoint `e`. -/
theorem set_queue_agree (hP : EPlaced T E R B) {e : U64} (he : e ∈ E) (s : S) (h v : U64) :
    let s' := L.wr (L.wr s (epHeadA e) h) (epTSA e) v
    Agree (L.mem s) (L.mem s') (fun b => ¬ EW e b) ∧ WritesIn st s s' (EW e) := by
  intro s'
  obtain ⟨ah, at'⟩ := ep_aligned (hP.epPlaced he)
  have key : ∀ b : U64, Aligned b → ¬ EW e b → L.mem s' b = L.mem s b := by
    intro b hb hn
    unfold EW at hn
    show L.mem (L.wr (L.wr s (epHeadA e) h) (epTSA e) v) b = _
    rw [L.mem_wr_ne at' hb (by rw [val_ts hP he]; omega), L.mem_wr_ne ah hb (by rw [val_head]; omega)]
  exact ⟨key, by simp only [s', LawfulStore.ksb_wr], by simp only [s', LawfulStore.cpu_wr], key⟩

theorem qagree_of (hP : EPlaced T E R B) {e : U64} (he : e ∈ E) {W : List U64} (hW : ∀ w ∈ W, w ∈ T)
    {s s1 : S} (hf : Framed st .Ep W s s1) (h v : U64) :
    QAgree T e W (L.mem s) (L.mem (L.wr (L.wr s1 (epHeadA e) h) (epTSA e) v)) ∧
    WritesIn st s (L.wr (L.wr s1 (epHeadA e) h) (epTSA e) v) (EWrite T E R B) := by
  obtain ⟨f1, f2⟩ := framed_agree hP hW hf
  obtain ⟨g1, g2⟩ := set_queue_agree (st := st) hP he s1 h v
  refine ⟨fun b hb ⟨h1, h2⟩ => (g1 b hb h1).trans (f1 b hb h2), (f2.trans g2).mono fun b hb => ?_⟩
  rcases hb with ⟨w, hw, hl⟩ | hb
  · exact Or.inr (Or.inr (Or.inl ⟨w, hW w hw, Or.inr hl⟩))
  · exact Or.inl ⟨e, he, hb⟩

/-- `ep_dequeue` of a member, with its frame. -/
theorem ep_dequeue_full (hP : EPlaced T E R B) (s : S) {e : U64} (he : e ∈ E) (t : obj.Tcb) (xs : List U64)
    (h : QueueRel (L.mem s) T .Ep (qOf (L.mem s) e) xs) (ht : t ∈ xs) :
    endpoint.ep_dequeue st s e t ⦃ s' =>
      QueueRel (L.mem s') T .Ep (qOf (L.mem s') e) (xs.erase t) ∧
      stOf (L.mem s') e = (if xs.erase t = [] then 0#u64 else stOf (L.mem s) e) ∧
      QAgree T e xs (L.mem s) (L.mem s') ∧ WritesIn st s s' (EWrite T E R B) ∧
      L.mem s' (nextA .Ep t) = 0#u64 ∧ L.mem s' (prevA .Ep t) = 0#u64 ⦄ := by
  have hE := hP.epPlaced he
  have hT := hP.tcb
  unfold endpoint.ep_dequeue
  step*
  subst q_post
  refine WP.spec_bind (tcbqueue.remove.rel s .Ep _ t xs hT h ht) ?_
  rintro ⟨q1, s1⟩ h1
  simp only [WP.uncurry'_pair] at h1
  obtain ⟨hr1, hf, hn0, hp0⟩ := h1
  have hW : ∀ w ∈ xs, w ∈ T := h.mem
  have hta : TcbAddr t := hP.tcb t (h.mem t ht)
  have hlinks : ∀ (s2 : S) (hv : U64), s2 = L.wr (L.wr s1 (epHeadA e) q1.head) (epTSA e) hv →
      L.mem s2 (nextA .Ep t) = 0#u64 ∧ L.mem s2 (prevA .Ep t) = 0#u64 := by
    intro s2 hv hs2
    obtain ⟨g1, -⟩ := set_queue_agree (L := L) hP he s1 q1.head hv
    rw [← hs2] at g1
    have ne1 : ¬ EW e (nextA .Ep t) := by
      unfold EW; rw [val_next hta]; have := hP.et e he t (h.mem t ht); omega
    have ne2 : ¬ EW e (prevA .Ep t) := by
      unfold EW; rw [val_prev hta]; have := hP.et e he t (h.mem t ht); omega
    exact ⟨(g1 _ (a_next hta).1 ne1).trans hn0, (g1 _ (a_prev hta).1 ne2).trans hp0⟩
  step*
  · subst s'_post
    have hemp : xs.erase t = [] := (hr1.empty_iff hT).1 (by simpa [b_post] using ‹b = true›)
    obtain ⟨h1, h2⟩ := ep_set_queue (state := obj.EP_IDLE) hT hE hr1
    obtain ⟨q1', q2'⟩ := qagree_of hP he hW hf q1.head ((q1.end &&& ~~~3#u64) ||| (obj.EP_IDLE &&& 3#u64))
    refine ⟨h1, ?_, q1', q2', hlinks _ _ rfl⟩
    rw [← epState_eq, h2]; simp only [hemp, ↓reduceIte]
    unfold obj.EP_IDLE
    exact UScalar.eq_of_val_eq (by simp)
  · subst s'_post
    have hne : xs.erase t ≠ [] := by
      rw [Ne, ← hr1.empty_iff hT]; simpa [b_post] using ‹¬b = true›
    obtain ⟨h1, h2⟩ := ep_set_queue (state := st) hT hE hr1
    obtain ⟨q1', q2'⟩ := qagree_of hP he hW hf q1.head ((q1.end &&& ~~~3#u64) ||| (st &&& 3#u64))
    refine ⟨h1, ?_, q1', q2', hlinks _ _ rfl⟩
    rw [← epState_eq, h2]; simp only [hne, ↓reduceIte]; rw [st_post]
    apply eq_of_bv
    simp only [LawfulStore.epState, UScalar.bv_and, BitVec.and_assoc, BitVec.and_self, stOf]

/-- `ep_append`, with its frame. -/
theorem ep_append_full (hP : EPlaced T E R B) (s : S) {e : U64} (he : e ∈ E) (t : obj.Tcb) (state : U64)
    (xs : List U64) (h : QueueRel (L.mem s) T .Ep (qOf (L.mem s) e) xs) (ht : t ∈ T) (hnt : t ∉ xs) :
    endpoint.ep_append st s e t state ⦃ s' =>
      QueueRel (L.mem s') T .Ep (qOf (L.mem s') e)
        (insPrio (fun y => L.mem s (prioA y)) (L.mem s (prioA t)) t xs) ∧
      stOf (L.mem s') e = state &&& 3#u64 ∧ QAgree T e (t :: xs) (L.mem s) (L.mem s') ∧
      WritesIn st s s' (EWrite T E R B) ⦄ := by
  have hE := hP.epPlaced he
  have hT := hP.tcb
  unfold endpoint.ep_append
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
  obtain ⟨h1, h2⟩ := ep_set_queue (state := state) hT hE hr1
  obtain ⟨q1', q2'⟩ := qagree_of hP he hW hf q1.head ((q1.end &&& ~~~3#u64) ||| (state &&& 3#u64))
  exact ⟨h1, by rw [← epState_eq, h2], q1', q2'⟩

end

end

end Fl4Proofs.P3.Endp
