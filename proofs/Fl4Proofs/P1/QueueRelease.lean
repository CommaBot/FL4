/-
P1: the release queue (sched.rs `release_enqueue`, seL4 `tcbReleaseEnqueue`)
is kept sorted by ready time.
-/
import Fl4Proofs.P1.QueueSched
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

/-! ## The abstract operation -/

/-- What `release_enqueue` computes on the list, for a thread `t` with ready
time `nt` and ready times `rt`: in front if the head is ready later than
`nt`; at the end if the head and the last member are ready no later than
`nt`; otherwise just before the first member that is ready later than `nt`
(seL4 `tcbReleaseEnqueue`). -/
def relIns (rt : U64 → U64) (nt t : U64) (xs : List U64) : List U64 :=
  if xs ≠ [] ∧ rt (xs.headD 0#u64) ≤ nt ∧ rt (xs.getLastD 0#u64) ≤ nt then xs ++ [t]
  else xs.takeWhile (fun y => decide (rt y ≤ nt)) ++ t :: xs.dropWhile (fun y => decide (rt y ≤ nt))

/-- Sorted by ready time, earliest first. -/
def TimeSorted (rt : U64 → U64) (xs : List U64) : Prop :=
  xs.Pairwise (fun a b => (rt a).val ≤ (rt b).val)

theorem le_iff_val {a b : U64} : a ≤ b ↔ a.val ≤ b.val := by
  simp [UScalar.le_equiv]

theorem takeWhile_split {P : U64 → Bool} {a : U64} {post : List U64} (ha : P a = false)
    (pre : List U64) (hpre : ∀ y ∈ pre, P y = true) :
      (pre ++ a :: post).takeWhile P = pre ∧ (pre ++ a :: post).dropWhile P = a :: post := by
  induction pre with
  | nil => simp [List.takeWhile_cons, List.dropWhile_cons, ha]
  | cons x pre ih =>
    have hx := hpre x (by simp)
    obtain ⟨h1, h2⟩ := ih (fun y hy => hpre y (by simp [hy]))
    simp [List.takeWhile_cons, List.dropWhile_cons, hx, h1, h2]

/-- `relIns` when the walk stops at `a`. -/
theorem relIns_split (rt : U64 → U64) (nt t a : U64) (pre post : List U64)
    (hpre : ∀ y ∈ pre, rt y ≤ nt) (ha : ¬ rt a ≤ nt)
    (hlast : ¬ rt ((pre ++ a :: post).getLastD 0#u64) ≤ nt) :
    relIns rt nt t (pre ++ a :: post) = pre ++ t :: a :: post := by
  obtain ⟨h1, h2⟩ := takeWhile_split (P := fun y => decide (rt y ≤ nt)) (post := post) (by simpa using ha)
    pre (fun y hy => by simpa using hpre y hy)
  unfold relIns
  rw [if_neg (fun h => hlast h.2.2), h1, h2]

/-- On a sorted queue, `relIns` is ordered insertion after every member
ready no later than `nt` (FIFO among equal times). -/
theorem relIns_eq_sorted (rt : U64 → U64) (nt t : U64) (xs : List U64) (h : TimeSorted rt xs) :
    relIns rt nt t xs = xs.takeWhile (fun y => decide (rt y ≤ nt)) ++ t ::
      xs.dropWhile (fun y => decide (rt y ≤ nt)) := by
  unfold relIns
  split
  · rename_i hc
    obtain ⟨hne, -, hl⟩ := hc
    have hall : ∀ y ∈ xs, rt y ≤ nt := by
      intro y hy
      rw [le_iff_val] at hl ⊢
      have hm := getLastD_mem hne 0#u64
      obtain ⟨pre, post, he⟩ := List.append_of_mem hy
      by_cases hp : post = []
      · subst hp; rw [he] at hl; simpa using hl
      · have : xs.getLastD 0#u64 ∈ post := by
          rw [he, show pre ++ y :: post = (pre ++ [y]) ++ post by simp, getLastD_append_of_ne _ hp]
          exact getLastD_mem hp _
        have hs : TimeSorted rt (y :: post) := by
          rw [he] at h; exact (List.pairwise_append.1 h).2.1
        have := List.rel_of_pairwise_cons hs this
        omega
    have h1 : xs.takeWhile (fun y => decide (rt y ≤ nt)) = xs := List.takeWhile_eq_self_iff.2 (by simpa using hall)
    have h2 : xs.dropWhile (fun y => decide (rt y ≤ nt)) = [] := List.dropWhile_eq_nil_iff.2 (by simpa using hall)
    rw [h1, h2]
  · rfl

/-- In a sorted queue, every member past the prefix ready no later than
`nt` is ready later. -/
theorem dropWhile_later (rt : U64 → U64) (nt : U64) (xs : List U64) (h : TimeSorted rt xs) :
    ∀ y ∈ xs.dropWhile (fun y => decide (rt y ≤ nt)), nt.val < (rt y).val := by
  intro y hy
  have hne : xs.dropWhile (fun y => decide (rt y ≤ nt)) ≠ [] := List.ne_nil_of_mem hy
  have hz0 := List.head_dropWhile_not (fun y => decide (rt y ≤ nt)) hne
  set z := (xs.dropWhile (fun y => decide (rt y ≤ nt))).head hne
  have hz : nt.val < (rt z).val := by
    have : ¬ rt z ≤ nt := by simpa using hz0
    rw [le_iff_val] at this; omega
  obtain ⟨rest, hrest⟩ : ∃ rest, xs.dropWhile (fun y => decide (rt y ≤ nt)) = z :: rest :=
    ⟨_, (List.cons_head_tail hne).symm⟩
  rw [hrest] at hy
  rcases List.mem_cons.1 hy with rfl | hy'
  · exact hz
  · have hs : TimeSorted rt (z :: rest) := by
      rw [← hrest]; exact h.sublist (List.dropWhile_suffix _).sublist
    have := List.rel_of_pairwise_cons hs hy'
    omega

/-- Ordered insertion keeps the release queue sorted. -/
theorem relIns_sorted (rt : U64 → U64) (nt t : U64) (xs : List U64) (h : TimeSorted rt xs)
    (ht : rt t = nt) : TimeSorted rt (relIns rt nt t xs) := by
  rw [relIns_eq_sorted rt nt t xs h]
  have hpre : ∀ y ∈ xs.takeWhile (fun y => decide (rt y ≤ nt)), (rt y).val ≤ nt.val := by
    intro y hy; have := List.mem_takeWhile_imp hy; simpa [le_iff_val] using this
  have hpost := dropWhile_later rt nt xs h
  have hs := h
  unfold TimeSorted at hs ⊢
  rw [← List.takeWhile_append_dropWhile (p := fun y => decide (rt y ≤ nt)) (l := xs),
    List.pairwise_append] at hs
  obtain ⟨h1, h2, h3⟩ := hs
  rw [List.pairwise_append, List.pairwise_cons]
  refine ⟨h1, ⟨fun b hb => ?_, h2⟩, fun a ha b hb => ?_⟩
  · rw [ht]; exact (hpost b hb).le
  · rcases List.mem_cons.1 hb with rfl | hb
    · rw [ht]; exact hpre a ha
    · exact h3 a ha b hb

/-! ## The code -/

def scA (t : U64) : U64 := core.num.U64.wrapping_add t 3464#u64

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64}

/-- `ready_time`: the time of the head refill of the thread's SC. -/
def LawfulStore.rtime (s : S) (y : U64) : U64 :=
  (L.refill s (L.mem s (scA y)) (L.rhead s (L.mem s (scA y)))).time

/-- The release queue of core `cpu`. -/
def LawfulStore.relQ (s : S) (cpu : U64) : tcbqueue.Queue :=
  ⟨L.mem s (L.nodeAt s cpu layout.node.RELEASE_HEAD),
   L.mem s (L.nodeAt s cpu (core.num.U64.wrapping_add layout.node.RELEASE_HEAD 8#u64))⟩

@[step] theorem obj.Tcb.sc.spec (s : S) (t : obj.Tcb) :
    obj.Tcb.sc st t s ⦃ v => v = L.mem s (scA t) ⦄ := by
  unfold obj.Tcb.sc; step*; simp_all [scA]

@[step] theorem sched.ready_time.spec (s : S) (t : obj.Tcb) :
    sched.ready_time st s t ⦃ v => v = L.rtime s t ⦄ := by
  unfold sched.ready_time; step*; simp_all [LawfulStore.rtime]

@[step] theorem sched.set_reprogram_on.spec (s : S) (cpu : U64) :
    sched.set_reprogram_on st s cpu ⦃ s' => s' = L.wr s (L.nodeAt s cpu layout.node.REPROGRAM) 1#u64 ⦄ := by
  unfold sched.set_reprogram_on; step*


theorem relh_val : layout.node.RELEASE_HEAD.val = 64 := by simp [layout.node.RELEASE_HEAD]
theorem relt_val : (core.num.U64.wrapping_add layout.node.RELEASE_HEAD 8#u64).val = 72 := by
  simp [layout.node.RELEASE_HEAD, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
theorem repr_val : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]

theorem relQ_wr_node {s : S} {c c' o v : U64} (hN : NodePlaced st T s c) (hN' : NodePlaced st T s c')
    (ho : o.val < 4288) (h8 : o.val % 8 = 0) (hne : c' = c → o.val ≠ 64 ∧ o.val ≠ 72) :
    L.relQ (L.wr s (L.nodeAt s c' o) v) c = L.relQ s c := by
  simp only [LawfulStore.relQ, nodeAt_wr]
  by_cases hc : c' = c
  · subst hc
    rw [rd_node_wr_node hN ho (by rw [relh_val]; omega) h8 (by rw [relh_val]),
      rd_node_wr_node hN ho (by rw [relt_val]; omega) h8 (by rw [relt_val]), relh_val, relt_val,
      if_neg (hne rfl).1, if_neg (hne rfl).2]
  · rw [rd_node_wr_node_cpu hN hN' ho (by rw [relh_val]; omega) h8 (by rw [relh_val]) hc,
      rd_node_wr_node_cpu hN hN' ho (by rw [relt_val]; omega) h8 (by rw [relt_val]) hc]

theorem relQ_wr_inq {s : S} {c t v : U64} (hN : NodePlaced st T s c) (ht : t ∈ T) (hta : TcbAddr t) :
    L.relQ (L.wr s (inqA t) v) c = L.relQ s c := by
  simp only [LawfulStore.relQ, nodeAt_wr]
  rw [rd_node_wr_inq hN (by rw [relh_val]; omega) (by rw [relh_val]) ht hta,
    rd_node_wr_inq hN (by rw [relt_val]; omega) (by rw [relt_val]) ht hta]

theorem relQ_framed {s s' : S} {c : U64} {l W} (hT : TcbPlaced T) (hN : NodePlaced st T s c)
    (hW : ∀ w ∈ W, w ∈ T) (hf : Framed st l W s s') : L.relQ s' c = L.relQ s c := by
  simp only [LawfulStore.relQ]
  rw [rd_node_framed hN (by rw [relh_val]; omega) (by rw [relh_val]) hW hT hf,
    rd_node_framed hN (by rw [relt_val]; omega) (by rw [relt_val]) hW hT hf]

theorem relQ_q_set {s : S} {c : U64} (q : tcbqueue.Queue) (hN : NodePlaced st T s c) :
    L.relQ (L.wr (L.wr s (L.nodeAt s c layout.node.RELEASE_HEAD) q.head)
      (L.nodeAt s c (core.num.U64.wrapping_add layout.node.RELEASE_HEAD 8#u64)) q.end) c = q := by
  simp only [LawfulStore.relQ, nodeAt_wr]
  have a64 : Aligned (L.nodeAt s c layout.node.RELEASE_HEAD) :=
    nodeAt_aligned hN (by rw [relh_val]; omega) (by rw [relh_val])
  have a72 : Aligned (L.nodeAt s c (core.num.U64.wrapping_add layout.node.RELEASE_HEAD 8#u64)) :=
    nodeAt_aligned hN (by rw [relt_val]; omega) (by rw [relt_val])
  have hne : (L.nodeAt s c (core.num.U64.wrapping_add layout.node.RELEASE_HEAD 8#u64)).val ≠
      (L.nodeAt s c layout.node.RELEASE_HEAD).val := by
    rw [nodeAt_val (off := layout.node.RELEASE_HEAD) hN (by rw [relh_val]; omega),
      nodeAt_val (off := core.num.U64.wrapping_add layout.node.RELEASE_HEAD 8#u64) hN (by rw [relt_val]; omega),
      relh_val, relt_val]
    omega
  rw [L.mem_wr_ne a72 a64 hne, L.mem_wr_same a64, L.mem_wr_same a72]

attribute [local step] smp.remote_queue_update.spec

/-- The end of `release_enqueue`: setting the flag, maybe reprogramming the
timer, maybe an IPI; none of it touches the release queue. -/
theorem release_tail (s3 : S) (c x : U64) (t : obj.Tcb) (ys : List U64) (hT : TcbPlaced T) (ht : t ∈ T)
    (hN3 : NodePlaced st T s3 c) (hN3' : NodePlaced st T s3 (L.cpu s3))
    (h3 : QueueRel (L.mem s3) T .Sched (L.relQ s3 c) ys) :
    (do
      let s4 ← sched.set_flag st s3 t sched.Q_RELEASE true
      let i ← obj.node_get st s4 c layout.node.RELEASE_HEAD
      let s5 ← if (i != x) = true then sched.set_reprogram_on st s4 c else ok s4
      smp.remote_queue_update st s5 t) ⦃ s' => QueueRel (L.mem s') T .Sched (L.relQ s' c) ys ⦄ := by
  have hta : TcbAddr t := hT t ht
  step as ⟨s4, s4_post⟩
  have hN4 : NodePlaced st T s4 c := by rw [s4_post]; exact hN3.wr
  have hN4' : NodePlaced st T s4 (L.cpu s4) := by rw [s4_post]; simp only [LawfulStore.cpu_wr]; exact hN3'.wr
  have h4 : QueueRel (L.mem s4) T .Sched (L.relQ s4 c) ys := by
    rw [s4_post, relQ_wr_inq hN3 ht hta]; exact h3.wr_inq hT hta
  step as ⟨i, _⟩
  have h5 : ∀ s5, (s5 = s4 ∨ s5 = L.wr s4 (L.nodeAt s4 c layout.node.REPROGRAM) 1#u64) →
      smp.remote_queue_update st s5 t ⦃ s' => QueueRel (L.mem s') T .Sched (L.relQ s' c) ys ⦄ := by
    intro s5 hs5
    have hN5 : NodePlaced st T s5 c ∧ NodePlaced st T s5 (L.cpu s5) ∧
        QueueRel (L.mem s5) T .Sched (L.relQ s5 c) ys := by
      rcases hs5 with rfl | rfl
      · exact ⟨hN4, hN4', h4⟩
      · refine ⟨hN4.wr, by simp only [LawfulStore.cpu_wr]; exact hN4'.wr, ?_⟩
        rw [relQ_wr_node hN4 hN4 (by rw [repr_val]; omega) (by rw [repr_val])
          (fun _ => by rw [repr_val]; omega)]
        exact h4.wr_node hT hN4 (by rw [repr_val]; omega) (by rw [repr_val])
    obtain ⟨hN5, hN5', h5⟩ := hN5
    refine WP.spec_mono (smp.remote_queue_update.spec s5 t) ?_
    rintro s6 (rfl | ⟨v, rfl⟩)
    · exact h5
    · rw [relQ_wr_node hN5 hN5' (by rw [ipi_val]; omega) (by rw [ipi_val]) (fun _ => by rw [ipi_val]; omega)]
      exact h5.wr_node hT hN5' (by rw [ipi_val]; omega) (by rw [ipi_val])
  split
  · step as ⟨s5, s5_post⟩; exact h5 s5 (Or.inr s5_post)
  · simp only [bind_ok]; exact h5 s4 (Or.inl rfl)

@[step] theorem obj.Tcb.sched_next.spec (s : S) (t : obj.Tcb) :
    obj.Tcb.sched_next st t s ⦃ v => v = L.mem s (nextA .Sched t) ⦄ := by
  unfold obj.Tcb.sched_next; step*; simp_all [nextA, nextOff]

/-- The forward walk from the head finds the first member ready later than
`nt`. -/
theorem sched.release_enqueue_loop.spec (s : S) (nt : U64) (q : tcbqueue.Queue) (xs : List U64)
    (hT : TcbPlaced T) (h : QueueRel (L.mem s) T .Sched q xs)
    (hlast : ¬ L.rtime s (xs.getLastD 0#u64) ≤ nt) (pre post : List U64) (a fuel : U64)
    (hx : xs = pre ++ a :: post) (hpre : ∀ y ∈ pre, L.rtime s y ≤ nt) (hf : post.length ≤ fuel.val) :
    sched.release_enqueue_loop st s nt a fuel ⦃ r =>
      ∃ pre' post', xs = pre' ++ r :: post' ∧ (∀ y ∈ pre', L.rtime s y ≤ nt) ∧ ¬ L.rtime s r ≤ nt ⦄ := by
  unfold sched.release_enqueue_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.val)
    (inv := fun x => ∃ pre post, xs = pre ++ x.1 :: post ∧ (∀ y ∈ pre, L.rtime s y ≤ nt) ∧
      post.length ≤ x.2.val)
  · rintro ⟨a, fu⟩ ⟨pre, post, hx, hpre, hf⟩
    simp only at hx hf
    have hax : a ∈ xs := by simp [hx]
    have hnil : post = [] → ¬ L.rtime s a ≤ nt := by
      rintro rfl; rw [hx] at hlast; simpa using hlast
    unfold sched.release_enqueue_loop.body
    step*
    · exfalso; apply h.ne0 hT a hax; simpa [b_post] using ‹b = true›
    · subst i_post
      cases post with
      | nil => exact absurd ‹_ ≥ _› (hnil rfl)
      | cons b post' =>
        have e : i1 = b := by
          have := h.seg; rw [hx, Seg_mid] at this
          rw [i1_post, this.2.2.1]; rfl
        subst e
        refine ⟨⟨pre ++ [a], post', by simp [hx], fun y hy => ?_, ?_⟩, by omega⟩
        · simp only [List.mem_append, List.mem_singleton] at hy
          rcases hy with hy | rfl
          · exact hpre y hy
          · exact ‹_ ≥ _›
        · simp at hf ⊢; omega
    · exfalso; subst i_post
      have : fu.val = 0 := by have := ‹¬fu > 0#u64›; simp at this; omega
      have : post = [] := List.eq_nil_of_length_eq_zero (by omega)
      exact hnil this ‹_ ≥ _›
  · exact ⟨pre, post, hx, hpre, hf⟩

theorem rel_q_set {s1 : S} {c : U64} {nq : tcbqueue.Queue} {ys : List U64} (hT : TcbPlaced T)
    (hN1 : NodePlaced st T s1 c) (h1 : QueueRel (L.mem s1) T .Sched nq ys) :
    let s2 := L.wr (L.wr s1 (L.nodeAt s1 c layout.node.RELEASE_HEAD) nq.head)
      (L.nodeAt s1 c (core.num.U64.wrapping_add layout.node.RELEASE_HEAD 8#u64)) nq.end
    QueueRel (L.mem s2) T .Sched (L.relQ s2 c) ys ∧ NodePlaced st T s2 c := by
  intro s2
  refine ⟨?_, hN1.wr.wr⟩
  rw [show L.relQ s2 c = nq from relQ_q_set nq hN1]
  have e : L.nodeAt s1 c (core.num.U64.wrapping_add layout.node.RELEASE_HEAD 8#u64) =
      L.nodeAt (L.wr s1 (L.nodeAt s1 c layout.node.RELEASE_HEAD) nq.head) c
        (core.num.U64.wrapping_add layout.node.RELEASE_HEAD 8#u64) := by simp
  have hl := (links_wr_node (v := nq.head) hT hN1 (o := layout.node.RELEASE_HEAD) (by rw [relh_val]; omega)
    (by rw [relh_val])).trans (links_wr_node (v := nq.end) hT hN1.wr
      (o := core.num.U64.wrapping_add layout.node.RELEASE_HEAD 8#u64) (by rw [relt_val]; omega) (by rw [relt_val]))
  rw [← e] at hl
  exact h1.links hl

/-- seL4 `tcbReleaseEnqueue`: the release queue of the thread's core becomes
`relIns` of the ready times (read in the state it runs in). -/
theorem sched.release_enqueue.rel (s : S) (t : obj.Tcb) (xs : List U64) (hT : TcbPlaced T) (ht : t ∈ T)
    (hn : t ∉ xs) (hN : NodePlaced st T s (L.mem s (affA t))) (hN' : NodePlaced st T s (L.cpu s))
    (h : QueueRel (L.mem s) T .Sched (L.relQ s (L.mem s (affA t))) xs) :
    sched.release_enqueue st s t ⦃ s' => QueueRel (L.mem s') T .Sched (L.relQ s' (L.mem s (affA t)))
      (relIns (L.rtime s) (L.rtime s t) t xs) ⦄ := by
  have hta : TcbAddr t := hT t ht
  unfold sched.release_enqueue
  step*
  all_goals subst cpu_post new_time_post
  all_goals have hqq : q = L.relQ s (L.mem s (affA t)) := by rw [q_post]; rfl
  all_goals have h0 := hqq ▸ h
  · -- empty: prepend
    have hx : xs = [] := (h0.empty_iff hT).1 (by simpa [b_post] using ‹b = true›)
    subst hx
    refine WP.spec_bind (tcbqueue.prepend.rel s .Sched q t [] hT h0 ht hn) ?_
    rintro ⟨nq, s1⟩ h1
    simp only [WP.uncurry'_pair] at h1
    obtain ⟨hr1, hf1⟩ := h1
    have hN1 := hN.framed hf1
    have hN1' : NodePlaced st T s1 (L.cpu s1) := by rw [hf1.2.1]; exact hN'.framed hf1
    step as ⟨s2, s2_post⟩
    obtain ⟨h2, hN2⟩ := rel_q_set hT hN1 hr1
    have hN2' : NodePlaced st T s2 (L.cpu s2) := by rw [s2_post]; simp only [LawfulStore.cpu_wr]; exact hN1'.wr.wr
    rw [← s2_post] at h2 hN2
    have e : relIns (L.rtime s) (L.rtime s t) t [] = [t] := by simp [relIns]
    rw [e]
    exact release_tail s2 _ q.head t [t] hT ht hN2 hN2' h2
  · -- earlier than the head: prepend
    have hne : xs ≠ [] := by
      rw [Ne, ← h0.empty_iff hT]; simpa [b_post] using ‹¬b = true›
    refine WP.spec_bind (tcbqueue.prepend.rel s .Sched q t xs hT h0 ht hn) ?_
    rintro ⟨nq, s1⟩ h1
    simp only [WP.uncurry'_pair] at h1
    obtain ⟨hr1, hf1⟩ := h1
    have hN1 := hN.framed hf1
    have hN1' : NodePlaced st T s1 (L.cpu s1) := by rw [hf1.2.1]; exact hN'.framed hf1
    step as ⟨s2, s2_post⟩
    obtain ⟨h2, hN2⟩ := rel_q_set hT hN1 hr1
    have hN2' : NodePlaced st T s2 (L.cpu s2) := by rw [s2_post]; simp only [LawfulStore.cpu_wr]; exact hN1'.wr.wr
    rw [← s2_post] at h2 hN2
    obtain ⟨a, post, rfl⟩ := List.exists_cons_of_ne_nil hne
    have hqa : q.head = a := by rw [h0.head]; rfl
    have ha : ¬ L.rtime s a ≤ L.rtime s t := by
      rw [← hqa, ← i_post, le_iff_val]; have := ‹L.rtime s t < i›; rw [UScalar.lt_equiv] at this; omega
    have e : relIns (L.rtime s) (L.rtime s t) t (a :: post) = t :: a :: post := by
      have := relIns_split (L.rtime s) (L.rtime s t) t a [] post (by simp) ha
      unfold relIns
      rw [if_neg (fun hc => ha (by simpa using hc.2.1))]
      obtain ⟨h1, h2⟩ := takeWhile_split (P := fun y => decide (L.rtime s y ≤ L.rtime s t)) (post := post)
        (by simpa using ha) [] (by simp)
      simp only [List.nil_append] at h1 h2
      rw [h1, h2]; rfl
    rw [e]
    exact release_tail s2 _ q.head t _ hT ht hN2 hN2' h2
  · -- no earlier than the end: append
    have hne : xs ≠ [] := by
      rw [Ne, ← h0.empty_iff hT]; simpa [b_post] using ‹¬b = true›
    refine WP.spec_bind (tcbqueue.append.rel s .Sched q t xs hT h0 ht hn) ?_
    rintro ⟨nq, s1⟩ h1
    simp only [WP.uncurry'_pair] at h1
    obtain ⟨hr1, hf1⟩ := h1
    have hN1 := hN.framed hf1
    have hN1' : NodePlaced st T s1 (L.cpu s1) := by rw [hf1.2.1]; exact hN'.framed hf1
    step as ⟨s2, s2_post⟩
    obtain ⟨h2, hN2⟩ := rel_q_set hT hN1 hr1
    have hN2' : NodePlaced st T s2 (L.cpu s2) := by rw [s2_post]; simp only [LawfulStore.cpu_wr]; exact hN1'.wr.wr
    rw [← s2_post] at h2 hN2
    have e : relIns (L.rtime s) (L.rtime s t) t xs = xs ++ [t] := by
      have hh : L.rtime s (xs.headD 0#u64) ≤ L.rtime s t := by
        rw [← h0.head, ← i_post, le_iff_val]
        have := ‹¬L.rtime s t < i›; rw [UScalar.lt_equiv] at this; omega
      have hl : L.rtime s (xs.getLastD 0#u64) ≤ L.rtime s t := by
        rw [← h0.last, ← i1_post]; exact ‹i1 ≤ L.rtime s t›
      unfold relIns
      rw [if_pos ⟨hne, hh, hl⟩]
    rw [e]
    exact release_tail s2 _ q.head t _ hT ht hN2 hN2' h2
  · -- in the middle: walk, then insert before
    have hne : xs ≠ [] := by
      rw [Ne, ← h0.empty_iff hT]; simpa [b_post] using ‹¬b = true›
    obtain ⟨a, post, hxa⟩ := List.exists_cons_of_ne_nil hne
    have hqa : q.head = a := by rw [h0.head, hxa]; rfl
    have hlast : ¬ L.rtime s (xs.getLastD 0#u64) ≤ L.rtime s t := by
      rw [← h0.last, ← i1_post]; exact ‹¬i1 ≤ L.rtime s t›
    have hfuel : post.length ≤ layout.WALK_FUEL.val := by
      rw [walk_fuel_val]; have := nodup_length_le h0.nodup; rw [hxa] at this; simp at this; omega
    have hl := sched.release_enqueue_loop.spec s (L.rtime s t) q xs hT h0 hlast [] post a
      layout.WALK_FUEL (by simp [hxa]) (by simp) hfuel
    rw [← hqa] at hl
    refine WP.spec_bind hl ?_
    rintro after ⟨pre, post', hx', hpre, hafter⟩
    have hpne : pre ≠ [] := by
      rintro rfl
      apply hafter
      have : after = q.head := by rw [h0.head, hx']; rfl
      rw [this, ← i_post, le_iff_val]
      have := ‹¬L.rtime s t < i›; rw [UScalar.lt_equiv] at this; omega
    refine WP.spec_bind (tcbqueue.insert_before.rel s .Sched q t after pre post' hT (hx' ▸ h0) hpne ht
      (hx' ▸ hn)) ?_
    rintro s2 ⟨h2, hf2⟩
    have hN2 := hN.framed hf2
    have hN2' : NodePlaced st T s2 (L.cpu s2) := by rw [hf2.2.1]; exact hN'.framed hf2
    have hW : ∀ w ∈ t :: (pre ++ after :: post'), w ∈ T := by
      intro w hw; rcases List.mem_cons.1 hw with rfl | hw
      · exact ht
      · exact h0.mem w (hx' ▸ hw)
    have hq2 : L.relQ s2 (L.mem s (affA t)) = q := by rw [relQ_framed hT hN hW hf2, hqq]
    have e : relIns (L.rtime s) (L.rtime s t) t xs = pre ++ t :: after :: post' := by
      rw [hx']; exact relIns_split _ _ t after pre post' hpre hafter (hx' ▸ hlast)
    rw [e]
    exact release_tail s2 _ q.head t _ hT ht hN2 hN2' (hq2 ▸ h2)

/-- `release_enqueue` keeps a release queue sorted by ready time sorted. -/
theorem sched.release_enqueue.sorted (s : S) (t : obj.Tcb) (xs : List U64) (hT : TcbPlaced T) (ht : t ∈ T)
    (hn : t ∉ xs) (hN : NodePlaced st T s (L.mem s (affA t))) (hN' : NodePlaced st T s (L.cpu s))
    (h : QueueRel (L.mem s) T .Sched (L.relQ s (L.mem s (affA t))) xs) (hs : TimeSorted (L.rtime s) xs) :
    sched.release_enqueue st s t ⦃ s' => ∃ ys, QueueRel (L.mem s') T .Sched (L.relQ s' (L.mem s (affA t))) ys ∧
      TimeSorted (L.rtime s) ys ∧ ys.Perm (t :: xs) ⦄ := by
  refine WP.spec_mono (sched.release_enqueue.rel s t xs hT ht hn hN hN' h) fun s' h' => ⟨_, h', ?_, ?_⟩
  · exact relIns_sorted _ _ t xs hs rfl
  · rw [relIns_eq_sorted _ _ t xs hs]
    exact (List.perm_middle).trans (List.Perm.cons _ (by rw [List.takeWhile_append_dropWhile]))

@[step] theorem sched.in_release_queue.spec (s : S) (t : obj.Tcb) :
    sched.in_release_queue st s t ⦃ b => b = decide ((L.mem s (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64) ⦄ := by
  unfold sched.in_release_queue; step*

/-- seL4 `tcbReleaseRemove`: a thread in the release queue leaves it (and a
sorted queue stays sorted, `TimeSorted.erase`). -/
theorem sched.release_remove.rel (s : S) (t : obj.Tcb) (xs : List U64) (hT : TcbPlaced T) (ht : t ∈ T)
    (hN : NodePlaced st T s (L.mem s (affA t)))
    (h : QueueRel (L.mem s) T .Sched (L.relQ s (L.mem s (affA t))) xs)
    (hq : (L.mem s (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64 → t ∈ xs) :
    sched.release_remove st s t ⦃ s' => QueueRel (L.mem s') T .Sched (L.relQ s' (L.mem s (affA t)))
      (if (L.mem s (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64 then xs.erase t else xs) ⦄ := by
  have hta : TcbAddr t := hT t ht
  unfold sched.release_remove
  step*
  have hq1 : (L.mem s (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64 := by
    intro hc; have := ‹b = true›; rw [b_post] at this; exact of_decide_eq_true this hc
  simp only [ne_eq, hq1, not_false_eq_true, if_true]
  subst cpu_post
  have htx := hq hq1
  have key : ∀ s1 : S, NodePlaced st T s1 (L.mem s (affA t)) →
      QueueRel (L.mem s1) T .Sched (L.relQ s1 (L.mem s (affA t))) xs →
      (do
        let q ← sched.q_get st s1 (L.mem s (affA t)) layout.node.RELEASE_HEAD
        let (q1, s2) ← tcbqueue.remove st s1 tcbqueue.Link.Sched q t
        let s3 ← sched.q_set st s2 (L.mem s (affA t)) layout.node.RELEASE_HEAD q1
        sched.set_flag st s3 t sched.Q_RELEASE false) ⦃ s' =>
      QueueRel (L.mem s') T .Sched (L.relQ s' (L.mem s (affA t))) (xs.erase t) ⦄ := by
    intro s1 hN1 h1
    step as ⟨q, q_post⟩
    have hq' : q = L.relQ s1 (L.mem s (affA t)) := by rw [q_post]; rfl
    refine WP.spec_bind (tcbqueue.remove.rel s1 .Sched q t xs hT (hq' ▸ h1) htx) ?_
    rintro ⟨q1, s2⟩ h2
    simp only [WP.uncurry'_pair] at h2
    obtain ⟨hr2, hf2, -, -⟩ := h2
    have hN2 := hN1.framed hf2
    step as ⟨s3, s3_post⟩
    obtain ⟨h3, hN3⟩ := rel_q_set hT hN2 hr2
    rw [← s3_post] at h3 hN3
    step as ⟨s4, s4_post⟩
    rw [s4_post, relQ_wr_inq hN3 ht hta]
    exact h3.wr_inq hT hta
  split
  · step as ⟨s1, s1_post⟩
    subst s1_post
    refine key _ hN.wr ?_
    rw [relQ_wr_node hN hN (by rw [repr_val]; omega) (by rw [repr_val]) (fun _ => by rw [repr_val]; omega)]
    exact h.wr_node hT hN (by rw [repr_val]; omega) (by rw [repr_val])
  · simp only [bind_ok]
    exact key s hN h

theorem TimeSorted.erase {rt : U64 → U64} {xs : List U64} (h : TimeSorted rt xs) (t : U64) :
    TimeSorted rt (xs.erase t) := h.sublist (List.erase_sublist)

end

end Fl4Proofs.P1
