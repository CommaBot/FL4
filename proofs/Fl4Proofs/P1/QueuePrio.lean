/-
P1: `append_by_prio` (seL4 MCS `tcbEPAppend`, tcbqueue.rs) inserts in
priority order, FIFO among equals, and keeps a priority-sorted queue sorted.
-/
import Fl4Proofs.P1.Queue
import Mathlib.Data.List.TakeWhile
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

def prioA (t : U64) : U64 := core.num.U64.wrapping_add t 3448#u64

theorem walk_fuel_val : layout.WALK_FUEL.val = 2 ^ 64 - 1 := by
  unfold layout.WALK_FUEL; simp [core.num.U64.MAX, U64.rMax]

/-! ## The abstract operation -/

/-- Insert `t` after the last member whose priority is not below `p`. -/
def afterLast (pr : U64 → U64) (p t : U64) : List U64 → List U64
  | [] => [t]
  | x :: xs => if xs.any (fun y => !decide (p > pr y)) then x :: afterLast pr p t xs else x :: t :: xs

/-- What `append_by_prio` computes on the list, for a thread `t` of priority
`p` and priorities `pr`: in front if `p` beats the head's priority,
otherwise after the last member whose priority is at least `p` (seL4
`tcbEPAppend`). On a sorted queue, this is the ordered insertion after all
members of priority `≥ p` (`insPrio_eq_sorted`). -/
def insPrio (pr : U64 → U64) (p t : U64) : List U64 → List U64
  | [] => [t]
  | x :: xs => if p > pr x then t :: x :: xs else afterLast pr p t (x :: xs)

theorem afterLast_split (pr : U64 → U64) (p t b : U64) (post : List U64) (hb : ¬ p > pr b)
    (hpost : ∀ y ∈ post, p > pr y) :
    ∀ pre : List U64, afterLast pr p t (pre ++ b :: post) = pre ++ b :: t :: post
  | [] => by
    have : post.any (fun y => !decide (p > pr y)) = false := by
      simp only [List.any_eq_false, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
        not_not]
      exact hpost
    simp only [List.nil_append, afterLast, this, Bool.false_eq_true, ite_false]
  | x :: pre => by
    have : (pre ++ b :: post).any (fun y => !decide (p > pr y)) = true := by
      simp only [List.any_eq_true]; exact ⟨b, by simp, by simpa using hb⟩
    simp only [List.cons_append, afterLast, this, ite_true, afterLast_split pr p t b post hb hpost pre]

/-- Sorted by priority, highest first. -/
def PrioSorted (pr : U64 → U64) (xs : List U64) : Prop :=
  xs.Pairwise (fun a b => (pr b).val ≤ (pr a).val)

theorem gt_iff_val {a b : U64} : a > b ↔ b.val < a.val := by
  simp [GT.gt, UScalar.lt_equiv]

theorem any_congr_mem {f g : U64 → Bool} : ∀ {xs : List U64}, (∀ y ∈ xs, f y = g y) → xs.any f = xs.any g
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.any_cons, h x (by simp), any_congr_mem (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem afterLast_congr {pr pr' : U64 → U64} {p t : U64} :
    ∀ {xs : List U64}, (∀ y ∈ xs, pr y = pr' y) → afterLast pr p t xs = afterLast pr' p t xs
  | [], _ => rfl
  | x :: xs, h => by
    have h' : ∀ y ∈ xs, pr y = pr' y := fun y hy => h y (List.mem_cons_of_mem _ hy)
    have hany : xs.any (fun y => !decide (p > pr y)) = xs.any (fun y => !decide (p > pr' y)) :=
      any_congr_mem (fun y hy => by rw [h' y hy])
    simp only [afterLast, hany, afterLast_congr h']

/-- `insPrio` only reads the priorities of the members. -/
theorem insPrio_congr {pr pr' : U64 → U64} {p t : U64} {xs : List U64} (h : ∀ y ∈ xs, pr y = pr' y) :
    insPrio pr p t xs = insPrio pr' p t xs := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    simp only [insPrio, h x (by simp), afterLast_congr h]

/-- When the head does not lose to `p`, `insPrio` puts `t` right after the
last member `b` that does not lose to `p`. -/
theorem insPrio_of_head (pr : U64 → U64) (p t b : U64) (pre post : List U64)
    (hh : ¬ p > pr ((pre ++ b :: post).headD 0#u64)) (hb : ¬ p > pr b) (hpost : ∀ y ∈ post, p > pr y) :
    insPrio pr p t (pre ++ b :: post) = pre ++ b :: t :: post := by
  obtain ⟨x, rest, he⟩ : ∃ x rest, pre ++ b :: post = x :: rest := by
    cases pre <;> exact ⟨_, _, rfl⟩
  rw [he] at hh ⊢
  simp only [List.headD_cons] at hh
  simp only [insPrio, hh, ite_false]
  rw [← he, afterLast_split pr p t b post hb hpost]

/-- `insPrio` on a split into a prefix of members that do not lose to `p`
and a suffix of members that do. -/
theorem insPrio_split (pr : U64 → U64) (p t : U64) (pre post : List U64)
    (hpre : ∀ y ∈ pre, ¬ p > pr y) (hpost : ∀ y ∈ post, p > pr y) :
    insPrio pr p t (pre ++ post) = pre ++ t :: post := by
  rcases eq_nil_or_snoc pre with rfl | ⟨pre', b, rfl⟩
  · cases post with
    | nil => rfl
    | cons z post' => simp [insPrio, hpost z (by simp)]
  · simp only [List.append_assoc, List.singleton_append]
    apply insPrio_of_head pr p t b pre' post _ (hpre b (by simp)) hpost
    cases pre' with
    | nil => exact hpre b (by simp)
    | cons x _ => exact hpre x (by simp)


/-- In a sorted queue, every member past the prefix that does not lose to
`p` loses to `p`. -/
theorem dropWhile_lose (pr : U64 → U64) (p : U64) (xs : List U64) (h : PrioSorted pr xs) :
    ∀ y ∈ xs.dropWhile (fun y => !decide (p > pr y)), p > pr y := by
  intro y hy
  have hne : xs.dropWhile (fun y => !decide (p > pr y)) ≠ [] := List.ne_nil_of_mem hy
  have hz := List.head_dropWhile_not (fun y => !decide (p > pr y)) hne
  simp only [Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq] at hz
  set z := (xs.dropWhile (fun y => !decide (p > pr y))).head hne
  obtain ⟨rest, hrest⟩ : ∃ rest, xs.dropWhile (fun y => !decide (p > pr y)) = z :: rest :=
    ⟨_, (List.cons_head_tail hne).symm⟩
  rw [hrest] at hy
  rcases List.mem_cons.1 hy with rfl | hy'
  · exact hz
  · have hs : PrioSorted pr (z :: rest) := by
      rw [← hrest]; exact h.sublist (List.dropWhile_suffix _).sublist
    have := List.rel_of_pairwise_cons hs hy'
    rw [gt_iff_val] at hz ⊢; omega

/-- On a sorted queue, `insPrio` puts `t` after every member of priority
`≥ p` and before every member of priority `< p`: ordered insertion, FIFO
among equal priorities. -/
theorem insPrio_eq_sorted (pr : U64 → U64) (p t : U64) (xs : List U64) (h : PrioSorted pr xs) :
    insPrio pr p t xs = xs.takeWhile (fun y => !decide (p > pr y)) ++ t ::
      xs.dropWhile (fun y => !decide (p > pr y)) := by
  apply Eq.trans _ (insPrio_split pr p t _ _ ?_ (dropWhile_lose pr p xs h))
  · rw [List.takeWhile_append_dropWhile]
  · intro y hy; simpa using List.mem_takeWhile_imp hy

/-- Ordered insertion keeps a queue sorted. -/
theorem insPrio_sorted (pr : U64 → U64) (p t : U64) (xs : List U64) (h : PrioSorted pr xs)
    (hp : pr t = p) : PrioSorted pr (insPrio pr p t xs) := by
  rw [insPrio_eq_sorted pr p t xs h]
  have hpre : ∀ y ∈ xs.takeWhile (fun y => !decide (p > pr y)), p.val ≤ (pr y).val := by
    intro y hy; have := List.mem_takeWhile_imp hy
    simp [gt_iff_val] at this; exact this
  have hpost : ∀ y ∈ xs.dropWhile (fun y => !decide (p > pr y)), (pr y).val ≤ p.val := by
    intro y hy; have := dropWhile_lose pr p xs h y hy; rw [gt_iff_val] at this; omega
  have hs := h
  unfold PrioSorted at hs ⊢
  rw [← List.takeWhile_append_dropWhile (p := fun y => !decide (p > pr y)) (l := xs),
    List.pairwise_append] at hs
  obtain ⟨h1, h2, h3⟩ := hs
  rw [List.pairwise_append, List.pairwise_cons]
  refine ⟨h1, ⟨fun b hb => hp ▸ hpost b hb, h2⟩, fun a ha b hb => ?_⟩
  rcases List.mem_cons.1 hb with rfl | hb
  · rw [hp]; exact hpre a ha
  · exact h3 a ha b hb

/-! ## The code -/

theorem nodup_length_le {xs : List U64} (h : xs.Nodup) : xs.length ≤ 2 ^ 64 := by
  have hnd : (xs.map (·.val)).Nodup := h.map (fun a b e => UScalar.eq_of_val_eq e)
  have hsub : xs.map (·.val) ⊆ List.range (2 ^ 64) := by
    intro v hv
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hv
    have := a.hBounds
    simp only [List.mem_range]; simpa [UScalarTy.numBits] using this
  have := (hnd.subperm hsub).length_le
  simpa using this

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64}

@[step] theorem obj.Tcb.prio.spec (s : S) (t : obj.Tcb) :
    obj.Tcb.prio st t s ⦃ v => v = L.mem s (prioA t) ⦄ := by
  unfold obj.Tcb.prio; step*; simp_all [prioA]

/-- The backward walk from the end finds the last member that does not lose
to `p`. -/
theorem tcbqueue.append_by_prio_loop.spec (s : S) (l : tcbqueue.Link) (p : U64) (q : tcbqueue.Queue)
    (xs : List U64) (hT : TcbPlaced T) (h : QueueRel (L.mem s) T l q xs)
    (hh : ¬ p > L.mem s (prioA (xs.headD 0#u64))) (pre post : List U64) (fuel : U64)
    (hx : xs = pre ++ post) (hpre : pre ≠ []) (hpost : ∀ y ∈ post, p > L.mem s (prioA y))
    (hf : pre.length - 1 ≤ fuel.val) :
    tcbqueue.append_by_prio_loop st s l p (pre.getLastD 0#u64) fuel ⦃ r =>
      ∃ pre' post', xs = pre' ++ r :: post' ∧ ¬ p > L.mem s (prioA r) ∧
        ∀ y ∈ post', p > L.mem s (prioA y) ⦄ := by
  unfold tcbqueue.append_by_prio_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.val)
    (inv := fun x => ∃ pre post, xs = pre ++ post ∧ pre ≠ [] ∧ x.1 = pre.getLastD 0#u64 ∧
      (∀ y ∈ post, p > L.mem s (prioA y)) ∧ pre.length - 1 ≤ x.2.val)
  · rintro ⟨bef, fu⟩ ⟨pre, post, hx, hpre, hb, hpost, hf⟩
    obtain ⟨pre', b, rfl⟩ := (eq_nil_or_snoc pre).resolve_left hpre
    simp only [List.getLastD_concat] at hb
    simp only at hb hf; subst hb
    have hbx : bef ∈ xs := by simp [hx]
    unfold tcbqueue.append_by_prio_loop.body
    have hne : p > L.mem s (prioA bef) → pre' ≠ [] := by
      rintro hgt rfl; apply hh; simpa [hx] using hgt
    simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel] at hf
    step*
    · exfalso; apply h.ne0 hT bef hbx; simpa [b_post] using ‹b = true›
    · subst i_post
      have hpre' := hne ‹_›
      refine ⟨⟨pre', bef :: post, by simp [hx], hpre', ?_, ?_, ?_⟩, by omega⟩
      · have := h.seg; rw [hx, List.append_assoc, List.singleton_append, Seg_mid] at this
        rw [i1_post, this.2.1]
      · intro y hy; rcases List.mem_cons.1 hy with rfl | hy
        · assumption
        · exact hpost y hy
      · omega
    · exfalso; subst i_post
      have hpre' := hne ‹_›
      have : fu.val = 0 := by
        have := ‹¬fu > 0#u64›; simp [gt_iff_val] at this; omega
      have : pre'.length = 0 := by omega
      exact hpre' (List.eq_nil_of_length_eq_zero this)
    · subst i_post
      exact ⟨pre', post, by simp [hx], ‹_›, hpost⟩
  · exact ⟨pre, post, hx, hpre, rfl, hpost, hf⟩
theorem post_of {s : S} {l W} {f : Result (tcbqueue.Queue × S)} {ys ys' : List U64}
    (hf : f ⦃ q' s' => QueueRel (L.mem s') T l q' ys ∧ Framed st l W s s' ⦄) (he : ys = ys') :
    f ⦃ q' s' => QueueRel (L.mem s') T l q' ys' ∧ Framed st l W s s' ⦄ := by
  subst he; exact hf

/-- `append_by_prio` is `insPrio` with the priorities of the state it runs in. -/
theorem tcbqueue.append_by_prio.rel (s : S) (l : tcbqueue.Link) (q : tcbqueue.Queue) (t : obj.Tcb)
    (xs : List U64) (hT : TcbPlaced T) (h : QueueRel (L.mem s) T l q xs) (ht : t ∈ T) (hn : t ∉ xs) :
    tcbqueue.append_by_prio st s l q t ⦃ q' s' =>
      QueueRel (L.mem s') T l q' (insPrio (fun y => L.mem s (prioA y)) (L.mem s (prioA t)) t xs) ∧
      Framed st l (t :: xs) s s' ⦄ := by
  unfold tcbqueue.append_by_prio
  step*
  · have : xs = [] := (h.empty_iff hT).1 (by simpa [b_post] using ‹b = true›)
    subst this
    exact post_of (tcbqueue.prepend.rel s l q t [] hT h ht hn) rfl
  · have hne : xs ≠ [] := by
      rw [Ne, ← h.empty_iff hT]; simpa [b_post] using ‹¬b = true›
    obtain ⟨x, zs, rfl⟩ := List.exists_cons_of_ne_nil hne
    have hqx : q.head = x := by rw [h.head]; rfl
    refine post_of (tcbqueue.prepend.rel s l q t _ hT h ht hn) ?_
    subst i_post p_post
    rw [hqx] at *
    simp [insPrio, ‹_ > _›]
  · have hne : xs ≠ [] := by
      rw [Ne, ← h.empty_iff hT]; simpa [b_post] using ‹¬b = true›
    refine post_of (tcbqueue.append.rel s l q t _ hT h ht hn) ?_
    obtain ⟨pre, e, rfl⟩ := (eq_nil_or_snoc xs).resolve_left hne
    have hqe : q.end = e := by rw [h.last]; simp
    subst i_post i1_post p_post
    rw [hqe] at *
    have := insPrio_of_head (fun y => L.mem s (prioA y)) (L.mem s (prioA t)) t e pre []
      (by rw [← h.head]; exact ‹¬_ > _›) (by rw [gt_iff_val]; have := ‹_ ≥ _›; simp [UScalar.le_equiv] at this; omega)
      (by simp)
    simpa using this.symm
  · have hne : xs ≠ [] := by
      rw [Ne, ← h.empty_iff hT]; simpa [b_post] using ‹¬b = true›
    subst i_post i1_post
    have hhd : ¬ p > L.mem s (prioA (xs.headD 0#u64)) := by rw [← h.head]; exact ‹¬p > _›
    have hfuel : xs.length - 1 ≤ layout.WALK_FUEL.val := by
      rw [walk_fuel_val]; have := nodup_length_le h.nodup; omega
    have hl := tcbqueue.append_by_prio_loop.spec s l p q xs hT h hhd xs [] layout.WALK_FUEL
      (by simp) hne (by simp) hfuel
    rw [← h.last] at hl
    refine WP.spec_bind hl ?_
    rintro before ⟨pre', post', hx', hb', hpost'⟩
    have hpne : post' ≠ [] := by
      rintro rfl
      have : q.end = before := by rw [h.last, hx']; simp
      subst this
      apply ‹¬L.mem s (prioA q.end) ≥ p›
      rw [gt_iff_val] at hb'; simp [UScalar.le_equiv]; omega
    subst hx'
    refine WP.spec_bind (tcbqueue.insert_after.rel s l q t before pre' post' hT h hpne ht hn) ?_
    rintro s1 ⟨hr1, hr2⟩
    simp only [WP.spec_ok, WP.uncurry'_pair]
    refine ⟨?_, hr2⟩
    subst p_post
    have e := insPrio_of_head (fun y => L.mem s (prioA y)) (L.mem s (prioA t)) t before pre' post'
      hhd hb' hpost'
    rw [e]; exact hr1
theorem prioA_val {t : U64} (h : TcbAddr t) : (prioA t).val = t.val + 3448 := by
  have := h.fits
  simp [prioA, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega

/-- A primitive's frame leaves priorities alone. -/
theorem prio_framed {s s' : S} {l W} {y : U64} (hy : TcbAddr y) (hW : ∀ w ∈ W, TcbAddr w)
    (hf : Framed st l W s s') : L.mem s' (prioA y) = L.mem s (prioA y) := by
  have := hy.align
  refine hf.2.2 _ (by unfold Aligned; rw [prioA_val hy]; omega) fun w hw => ⟨?_, ?_⟩ <;> intro e <;>
    have := congrArg UScalar.val e <;> have := (hW w hw).align
  · rw [prioA_val hy, nextA_val (hW w hw)] at *; cases l <;> simp [nextOff] at * <;> omega
  · rw [prioA_val hy, prevA_val (hW w hw)] at *; cases l <;> simp [prevOff] at * <;> omega

/-- `append_by_prio` keeps a priority-sorted queue sorted, by the priorities
of the state it leaves (they are unchanged). -/
theorem tcbqueue.append_by_prio.sorted (s : S) (l : tcbqueue.Link) (q : tcbqueue.Queue) (t : obj.Tcb)
    (xs : List U64) (hT : TcbPlaced T) (h : QueueRel (L.mem s) T l q xs) (ht : t ∈ T) (hn : t ∉ xs)
    (hs : PrioSorted (fun y => L.mem s (prioA y)) xs) :
    tcbqueue.append_by_prio st s l q t ⦃ q' s' => ∃ ys, QueueRel (L.mem s') T l q' ys ∧
      PrioSorted (fun y => L.mem s' (prioA y)) ys ∧ Framed st l (t :: xs) s s' ⦄ := by
  refine WP.spec_mono (tcbqueue.append_by_prio.rel s l q t xs hT h ht hn) ?_
  rintro ⟨q', s'⟩ hr
  simp only [WP.uncurry'_pair] at hr ⊢
  obtain ⟨hr, hf⟩ := hr
  refine ⟨_, hr, ?_, hf⟩
  have hsrt := insPrio_sorted (fun y => L.mem s (prioA y)) (L.mem s (prioA t)) t xs hs rfl
  have hW : ∀ w ∈ t :: xs, TcbAddr w := by
    intro w hw; rcases List.mem_cons.1 hw with rfl | hw
    · exact hT _ ht
    · exact h.addr hT w hw
  refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab => ?_) hsrt
  have := hr.addr hT
  show (L.mem s' (prioA b)).val ≤ (L.mem s' (prioA a)).val
  rw [prio_framed (this a ha) hW hf, prio_framed (this b hb) hW hf]
  exact hab
end

end Fl4Proofs.P1
