-- AArch64 port of Fl4Proofs.P1.QueueInv (proofs/scratch/a64/port.py): the x86_64 text, re-checked
-- over Fl4CoreA64. Edits beyond the renaming are marked `-- a64:`.
/-
P1: the scheduler queues as one invariant (`SchedQueuesInv`): the ready
queues and release queues of all cores, the `IN_QUEUES` flags, and where a
queued thread may be (its own core, its own priority, one queue at most).

The four queue operations (`enqueue`, `dequeue`, `release_enqueue`,
`release_remove`) have a common shape of footprint (`QFoot`): the `Sched`
links of the TCBs `W` of one queue, some words of one core's node, the
thread's `IN_QUEUES` word, and the current core's `IPI_PENDING` (a64: either word of the pair). Everything
outside a footprint is unchanged (`WritesIn`), which is how every queue the
operation does not touch stays related.
-/
import Fl4ProofsA64.P1.QueueRelease
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64}

/-! ## Footprints -/

/-- `s'` differs from `s` at most on the aligned words satisfying `A`. -/
def WritesIn (st : machine.Store S) [L : LawfulStore st] (s s' : S) (A : U64 → Prop) : Prop :=
  L.ksb s' = L.ksb s ∧ L.cpu s' = L.cpu s ∧ ∀ b, Aligned b → ¬ A b → L.mem s' b = L.mem s b

theorem WritesIn.refl (s : S) (A : U64 → Prop) : WritesIn st s s A := ⟨rfl, rfl, fun _ _ _ => rfl⟩

theorem WritesIn.trans {s₁ s₂ s₃ : S} {A B : U64 → Prop} (h₁ : WritesIn st s₁ s₂ A)
    (h₂ : WritesIn st s₂ s₃ B) : WritesIn st s₁ s₃ (fun b => A b ∨ B b) :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, fun b hb hn =>
    (h₂.2.2 b hb (fun h => hn (Or.inr h))).trans (h₁.2.2 b hb (fun h => hn (Or.inl h)))⟩

theorem WritesIn.mono {s s' : S} {A B : U64 → Prop} (h : WritesIn st s s' A) (hAB : ∀ b, A b → B b) :
    WritesIn st s s' B :=
  ⟨h.1, h.2.1, fun b hb hn => h.2.2 b hb (fun h' => hn (hAB b h'))⟩

theorem writesIn_wr {s : S} {a v : U64} (ha : Aligned a) : WritesIn st s (L.wr s a v) (· = a) :=
  ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun b hb hn => L.mem_wr_ne ha hb (fun e => hn (UScalar.eq_of_val_eq e).symm)⟩

theorem WritesIn.mem_eq {s s' : S} {A : U64 → Prop} (h : WritesIn st s s' A) {b : U64} (hb : Aligned b)
    (hn : ¬ A b) : L.mem s' b = L.mem s b := h.2.2 b hb hn

theorem nodeAt_of_ksb {s s' : S} (h : L.ksb s' = L.ksb s) (c o : U64) : L.nodeAt s' c o = L.nodeAt s c o := by
  simp [LawfulStore.nodeAt, h]

/-- The `l` link fields of the TCBs `W`. -/
def LinkOf (l : tcbqueue.Link) (W : List U64) (b : U64) : Prop := ∃ w ∈ W, b = nextA l w ∨ b = prevA l w

theorem Framed.writesIn {s s' : S} {l W} (h : Framed st l W s s') : WritesIn st s s' (LinkOf l W) :=
  ⟨h.1, h.2.1, fun b hb hn => h.2.2 b hb fun w hw =>
    ⟨fun e => hn ⟨w, hw, Or.inl e⟩, fun e => hn ⟨w, hw, Or.inr e⟩⟩⟩

/-- The words of core `c`'s node at offsets satisfying `P`. -/
def LawfulStore.NodeOf (s : S) (c : U64) (P : Nat → Prop) (b : U64) : Prop :=
  ∃ o : U64, P o.val ∧ o.val < 4288 ∧ o.val % 8 = 0 ∧ b = L.nodeAt s c o

theorem writesIn_wr_node {s s1 : S} {c o v : U64} {P : Nat → Prop} (hN : NodePlaced st T s c)
    (hk : L.ksb s1 = L.ksb s) (hP : P o.val) (ho : o.val < 4288) (h8 : o.val % 8 = 0) :
    WritesIn st s1 (L.wr s1 (L.nodeAt s1 c o) v) (L.NodeOf s c P) := by
  rw [nodeAt_of_ksb hk]
  exact (writesIn_wr (nodeAt_aligned hN ho h8)).mono fun b hb => ⟨o, hP, ho, h8, hb⟩

/-- The footprint of a scheduler queue operation on the queue of TCBs `W`
of core `c` (node offsets `P`) for thread `t`. -/
def LawfulStore.QFoot (s : S) (W : List U64) (c : U64) (P : Nat → Prop) (t b : U64) : Prop :=
  LinkOf .Sched W b ∨ L.NodeOf s c P b ∨ b = inqA t ∨ L.NodeOf s (L.cpu s) (fun o => o = 120 ∨ o = 128) b  -- a64: IPI_PENDING pair

/-! ## What lies outside a footprint -/

section foot
variable {s : S} {W : List U64} {c t : U64} {P : Nat → Prop}
  (hT : TcbPlaced T) (hW : ∀ w ∈ W, w ∈ T) (hN : NodePlaced st T s c) (hN' : NodePlaced st T s (L.cpu s))
  (ht : t ∈ T)
include hT hW hN hN' ht

theorem nodeOf_not_link {c' : U64} {Q : Nat → Prop} (hNc : NodePlaced st T s c') {y : U64} (hy : y ∈ T)
    (l : tcbqueue.Link) : ¬ L.NodeOf s c' Q (nextA l y) ∧ ¬ L.NodeOf s c' Q (prevA l y) := by
  constructor <;> rintro ⟨o, -, ho, -, e⟩
  · exact nodeAt_ne_nextA hNc ho hy (hT y hy) l e.symm
  · exact nodeAt_ne_prevA hNc ho hy (hT y hy) l e.symm

/-- Link fields of TCBs outside `W`, or of the other link kind. -/
theorem qfoot_link {y : U64} (hy : y ∈ T) (l : tcbqueue.Link) (hl : l = .Sched → y ∉ W) :
    ¬ L.QFoot s W c P t (nextA l y) ∧ ¬ L.QFoot s W c P t (prevA l y) := by
  have hya := hT y hy
  have hta := hT t ht
  have n1 := nodeOf_not_link hT hW hN hN' ht hN hy l (Q := P)
  have n2 := nodeOf_not_link hT hW hN hN' ht hN' hy l (Q := (fun o => o = 120 ∨ o = 128))  -- a64: IPI_PENDING pair
  constructor
  · rintro (⟨w, hw, e | e⟩ | h | h | h)
    · rw [nextA_eq_iff hya (hT w (hW w hw))] at e
      obtain ⟨rfl, rfl⟩ := e; exact hl rfl hw
    · exact nextA_ne_prevA hya (hT w (hW w hw)) l _ e
    · exact n1.1 h
    · exact inqA_ne_nextA hta hya l h.symm
    · exact n2.1 h
  · rintro (⟨w, hw, e | e⟩ | h | h | h)
    · exact nextA_ne_prevA (hT w (hW w hw)) hya _ l e.symm
    · rw [prevA_eq_iff hya (hT w (hW w hw))] at e
      obtain ⟨rfl, rfl⟩ := e; exact hl rfl hw
    · exact n1.2 h
    · exact inqA_ne_prevA hta hya l h.symm
    · exact n2.2 h

/-- Words of a placed node, away from the footprint's offsets. -/
theorem qfoot_node {c' o : U64} (hNc : NodePlaced st T s c') (ho : o.val < 4288) (h8 : o.val % 8 = 0)
    (hP : c' = c → ¬ P o.val) (hI : c' = L.cpu s → ¬ (o.val = 120 ∨ o.val = 128)) : ¬ L.QFoot s W c P t (L.nodeAt s c' o) := by  -- a64: IPI_PENDING pair
  rintro (⟨w, hw, e | e⟩ | ⟨o', hP', ho', -, e⟩ | e | ⟨o', hP', ho', -, e⟩)
  · exact nodeAt_ne_nextA hNc ho (hW w hw) (hT w (hW w hw)) _ e
  · exact nodeAt_ne_prevA hNc ho (hW w hw) (hT w (hW w hw)) _ e
  · by_cases hc : c' = c
    · subst hc
      have := congrArg UScalar.val e
      rw [nodeAt_val hN ho, nodeAt_val hN ho'] at this
      exact hP rfl (by have : o.val = o'.val := by omega
                       rw [this]; exact hP')
    · exact nodeAt_ne_cpu hNc hN ho ho' hc e
  · exact inqA_ne_nodeAt hNc ho ht (hT t ht) e.symm
  · by_cases hc : c' = L.cpu s
    · subst hc
      have := congrArg UScalar.val e
      rw [nodeAt_val hN' ho, nodeAt_val hN' ho'] at this
      exact hI rfl (by omega)
    · exact nodeAt_ne_cpu hNc hN' ho ho' hc e

/-- A TCB field at offset `K` that is no link field (and not `t`'s
`IN_QUEUES`). -/
theorem qfoot_field {y K : U64} (hy : y ∈ T) (hK : K.val < 4096) (hK8 : K.val % 8 = 0)
    (hKl : K.val ≠ 3480 ∧ K.val ≠ 3488 ∧ K.val ≠ 3496 ∧ K.val ≠ 3504) (hKt : y = t → K.val ≠ 3592) :
    ¬ L.QFoot s W c P t (core.num.U64.wrapping_add y K) := by
  have hya := hT y hy
  have hval : (core.num.U64.wrapping_add y K).val = y.val + K.val := by
    have := hya.fits
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  have hya8 := hya.align
  rintro (⟨w, hw, e | e⟩ | ⟨o, -, ho, -, e⟩ | e | ⟨o, -, ho, -, e⟩) <;> have hv := congrArg UScalar.val e
  · have hwa := hT w (hW w hw); have hw8 := hwa.align
    rw [hval, nextA_val hwa] at hv; simp [nextOff] at hv; omega
  · have hwa := hT w (hW w hw); have hw8 := hwa.align
    rw [hval, prevA_val hwa] at hv; simp [prevOff] at hv; omega
  · have := nodeAt_out hN ho hy; omega
  · have hta := hT t ht; have ht8 := hta.align
    rw [hval, inqA_val hta] at hv
    by_cases e' : y = t
    · subst e'; exact hKt rfl (by omega)
    · have : y.val ≠ t.val := fun h => e' (UScalar.eq_of_val_eq h)
      omega
  · have := nodeAt_out hN' ho hy; omega

end foot

/-! Fields as offsets. -/

theorem affA_eq (y : U64) : affA y = core.num.U64.wrapping_add y 3520#u64 := rfl
theorem prioA_eq (y : U64) : prioA y = core.num.U64.wrapping_add y 3448#u64 := rfl
theorem inqA_eq (y : U64) : inqA y = core.num.U64.wrapping_add y 3592#u64 := rfl
theorem scA_eq (y : U64) : scA y = core.num.U64.wrapping_add y 3464#u64 := rfl

theorem field_aligned {y K : U64} (hy : TcbAddr y) (hK : K.val < 4096) (hK8 : K.val % 8 = 0) :
    Aligned (core.num.U64.wrapping_add y K) := by
  have := hy.fits; have := hy.align
  unfold Aligned
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega

/-! ## What survives a footprint -/

section keep
variable {s s' : S} {W : List U64} {c t : U64} {P : Nat → Prop}
  (hT : TcbPlaced T) (hW : ∀ w ∈ W, w ∈ T) (hN : NodePlaced st T s c) (hN' : NodePlaced st T s (L.cpu s))
  (ht : t ∈ T) (hw : WritesIn st s s' (L.QFoot s W c P t))
include hT hW hN hN' ht hw

theorem QueueRel.qfoot {l q xs} (h : QueueRel (L.mem s) T l q xs) (hl : l = .Sched → ∀ y ∈ xs, y ∉ W) :
    QueueRel (L.mem s') T l q xs :=
  ⟨h.nodup, h.mem, h.head, h.last, h.seg.congr fun y hy =>
    have hk := qfoot_link hT hW hN hN' ht (h.mem y hy) l (fun e => hl e y hy) (P := P)
    ⟨hw.mem_eq (prevA_aligned (h.addr hT y hy) l) hk.2, hw.mem_eq (nextA_aligned (h.addr hT y hy) l) hk.1⟩⟩

theorem node_qfoot {c' o : U64} (hNc : NodePlaced st T s c') (ho : o.val < 4288) (h8 : o.val % 8 = 0)
    (hP : c' = c → ¬ P o.val) (hI : c' = L.cpu s → ¬ (o.val = 120 ∨ o.val = 128)) :  -- a64: IPI_PENDING pair
    L.mem s' (L.nodeAt s' c' o) = L.mem s (L.nodeAt s c' o) := by
  rw [nodeAt_of_ksb hw.1]
  exact hw.mem_eq (nodeAt_aligned hNc ho h8) (qfoot_node hT hW hN hN' ht hNc ho h8 hP hI)

theorem ReadyQueues.qfoot {c' : U64} {Q : U64 → List U64} (hNc : NodePlaced st T s c')
    (h : ReadyQueues st T s c' Q) (hP : c' = c → ∀ o, 136 ≤ o → o < 4288 → ¬ P o)  -- a64: 128->136
    (hQ : ∀ p : U64, p.val < 256 → ∀ y ∈ Q p, y ∉ W) : ReadyQueues st T s' c' Q := by
  have hv : ViewsEq st s s' c' := by
    refine ⟨fun p hp => ?_, ?_, fun g hg => ?_⟩
    · simp only [LawfulStore.rqQ]
      rw [node_qfoot hT hW hN hN' ht hw hNc (by rw [rqOff_val hp]; omega) (by rw [rqOff_val hp]; omega)
          (fun e => hP e _ (by rw [rqOff_val hp]; omega) (by rw [rqOff_val hp]; omega))
          (fun _ => by rw [rqOff_val hp]; omega),
        node_qfoot hT hW hN hN' ht hw hNc (by rw [rqTailOff_val hp]; omega) (by rw [rqTailOff_val hp]; omega)
          (fun e => hP e _ (by rw [rqTailOff_val hp]; omega) (by rw [rqTailOff_val hp]; omega))
          (fun _ => by rw [rqTailOff_val hp]; omega)]
    · exact node_qfoot hT hW hN hN' ht hw hNc (by rw [l1Off_val]; omega) (by rw [l1Off_val])
        (fun e => hP e _ (by rw [l1Off_val]) (by rw [l1Off_val]; omega)) (fun _ => by rw [l1Off_val]; omega)
    · exact node_qfoot hT hW hN hN' ht hw hNc (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega)
        (fun e => hP e _ (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega))
        (fun _ => by rw [l2Off_val hg]; omega)
  refine ⟨h.1.agree hv.1 fun p hp y hy => ?_, h.2.views hv⟩
  have hy := (h.1.rel p hp).mem y hy
  have hk := qfoot_link hT hW hN hN' ht hy .Sched (fun _ => hQ p hp y ‹_›) (P := P)
  exact ⟨hw.mem_eq (nextA_aligned (hT y hy) _) hk.1, hw.mem_eq (prevA_aligned (hT y hy) _) hk.2⟩

theorem relQ_qfoot {c' : U64} (hNc : NodePlaced st T s c') (hP : c' = c → ¬ P 64 ∧ ¬ P 72) :
    L.relQ s' c' = L.relQ s c' := by
  simp only [LawfulStore.relQ]
  rw [node_qfoot hT hW hN hN' ht hw hNc (by rw [relh_val]; omega) (by rw [relh_val])
      (fun e => by rw [relh_val]; exact (hP e).1) (fun _ => by rw [relh_val]; omega),
    node_qfoot hT hW hN hN' ht hw hNc (by rw [relt_val]; omega) (by rw [relt_val])
      (fun e => by rw [relt_val]; exact (hP e).2) (fun _ => by rw [relt_val]; omega)]

theorem field_qfoot {y K : U64} (hy : y ∈ T) (hK : K.val < 4096) (hK8 : K.val % 8 = 0)
    (hKl : K.val ≠ 3480 ∧ K.val ≠ 3488 ∧ K.val ≠ 3496 ∧ K.val ≠ 3504) (hKt : y = t → K.val ≠ 3592) :
    L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
  hw.mem_eq (field_aligned (hT y hy) hK hK8) (qfoot_field hT hW hN hN' ht hy hK hK8 hKl hKt)

theorem aff_qfoot {y : U64} (hy : y ∈ T) : L.mem s' (affA y) = L.mem s (affA y) :=
  field_qfoot hT hW hN hN' ht hw hy (by simp) (by simp) (by simp) (fun _ => by simp)
theorem prio_qfoot {y : U64} (hy : y ∈ T) : L.mem s' (prioA y) = L.mem s (prioA y) :=
  field_qfoot hT hW hN hN' ht hw hy (by simp) (by simp) (by simp) (fun _ => by simp)
theorem sc_qfoot {y : U64} (hy : y ∈ T) : L.mem s' (scA y) = L.mem s (scA y) :=
  field_qfoot hT hW hN hN' ht hw hy (by simp) (by simp) (by simp) (fun _ => by simp)
theorem inq_qfoot {y : U64} (hy : y ∈ T) (hyt : y ≠ t) : L.mem s' (inqA y) = L.mem s (inqA y) :=
  field_qfoot hT hW hN hN' ht hw hy (by simp) (by simp) (by simp) (fun e => absurd e hyt)

end keep

/-! ## Footprints of the steps -/

theorem writesIn_node {s s1 : S} {c o v : U64} {P : Nat → Prop} (hN : NodePlaced st T s c)
    (hP : P o.val) (ho : o.val < 4288) (h8 : o.val % 8 = 0) :
    WritesIn st s1 (L.wr s1 (L.nodeAt s c o) v) (L.NodeOf s c P) :=
  (writesIn_wr (nodeAt_aligned hN ho h8)).mono fun b hb => ⟨o, hP, ho, h8, hb⟩

theorem remote_writesIn {s s4 s5 : S} (hN' : NodePlaced st T s (L.cpu s)) (hk : L.ksb s4 = L.ksb s)
    (hc : L.cpu s4 = L.cpu s)
    (h : s5 = s4 ∨ ∃ o v, (o.val = 120 ∨ o.val = 128) ∧ s5 = L.wr s4 (L.nodeAt s4 (L.cpu s4) o) v) :  -- a64: IPI_PENDING pair
    WritesIn st s4 s5 (L.NodeOf s (L.cpu s) (fun o => o = 120 ∨ o = 128)) := by  -- a64: IPI_PENDING pair
  rcases h with rfl | ⟨o, v, ho, rfl⟩
  · exact WritesIn.refl _ _
  · rw [hc, nodeAt_of_ksb hk]
    exact writesIn_node (P := fun o => o = 120 ∨ o = 128) hN' ho (by omega) (by omega)  -- a64: IPI_PENDING pair

theorem writesIn_inq {s1 : S} {t v : U64} (hta : TcbAddr t) :
    WritesIn st s1 (L.wr s1 (inqA t) v) (· = inqA t) := writesIn_wr (inqA_aligned hta)

/-- `t`'s `IN_QUEUES` word is outside the parts of a footprint other than
`inqA t`. -/
theorem inq_not_link_node {s : S} {W : List U64} {c t : U64} {Q : Nat → Prop} (hT : TcbPlaced T)
    (hW : ∀ w ∈ W, w ∈ T) (hN : NodePlaced st T s c) (ht : t ∈ T) :
    ¬ LinkOf .Sched W (inqA t) ∧ ¬ L.NodeOf s c Q (inqA t) := by
  constructor
  · rintro ⟨w, hw, e | e⟩
    · exact inqA_ne_nextA (hT t ht) (hT w (hW w hw)) _ e
    · exact inqA_ne_prevA (hT t ht) (hT w (hW w hw)) _ e
  · rintro ⟨o, -, ho, -, e⟩; exact inqA_ne_nodeAt hN ho ht (hT t ht) e

attribute [local step] smp.remote_queue_update.spec

/-! ## The footprint of `enqueue` -/

theorem enqueue_foot_tail (s s1 : S) (t c p off : U64) (q : tcbqueue.Queue) (xs : List U64)
    (hT : TcbPlaced T) (ht : t ∈ T) (hp : p.val < 256) (hN : NodePlaced st T s c)
    (hN' : NodePlaced st T s (L.cpu s)) (h1 : WritesIn st s s1 (L.NodeOf s c (136 ≤ ·)))  -- a64: 128->136
    (hr : QueueRel (L.mem s1) T .Sched q xs) (hn : t ∉ xs)
    (hoff : off = rqOff p) (hoff8 : core.num.U64.wrapping_add off 8#u64 = rqTailOff p) :
    (do
      let (q1, s2) ← tcbqueue.prepend st s1 tcbqueue.Link.Sched q t
      let s3 ← sched.q_set st s2 c off q1
      let s4 ← sched.set_flag st s3 t sched.Q_QUEUED true
      smp.remote_queue_update st s4 t) ⦃ s' =>
    WritesIn st s s' (L.QFoot s (t :: xs) c (136 ≤ ·) t) ∧  -- a64: 128->136
      L.mem s' (inqA t) = L.mem s (inqA t) ||| sched.Q_QUEUED ⦄ := by
  have hta : TcbAddr t := hT t ht
  have hW : ∀ w ∈ t :: xs, w ∈ T := by
    intro w hw; rcases List.mem_cons.1 hw with rfl | hw
    · exact ht
    · exact hr.mem w hw
  refine WP.spec_bind (tcbqueue.prepend.rel s1 .Sched q t xs hT hr ht hn) ?_
  rintro ⟨q1, s2⟩ h2
  simp only [WP.uncurry'_pair] at h2
  obtain ⟨-, hf2⟩ := h2
  have w12 := hf2.writesIn
  have w02 := h1.trans w12
  step as ⟨s3, s3_post⟩
  have w23 : WritesIn st s2 s3 (L.NodeOf s c (136 ≤ ·)) := by  -- a64: 128->136
    subst hoff
    rw [s3_post, nodeAt_of_ksb w02.1, nodeAt_of_ksb w02.1, hoff8]
    exact ((writesIn_node (P := (136 ≤ ·)) hN (by rw [rqOff_val hp]; omega) (by rw [rqOff_val hp]; omega)  -- a64: 128->136
      (by rw [rqOff_val hp]; omega)).trans (writesIn_node (P := (136 ≤ ·)) hN (by rw [rqTailOff_val hp]; omega)  -- a64: 128->136
      (by rw [rqTailOff_val hp]; omega) (by rw [rqTailOff_val hp]; omega))).mono fun b hb => by
        rcases hb with hb | hb <;> exact hb
  have w03 := w02.trans w23
  step as ⟨s4, s4_post⟩
  simp only [ite_true] at s4_post
  have w34 : WritesIn st s3 s4 (· = inqA t) := by rw [s4_post]; exact writesIn_inq hta
  have w04 := w03.trans w34
  refine WP.spec_mono (smp.remote_queue_update.spec s4 t) ?_
  intro s5 h5
  have w45 := remote_writesIn hN' w04.1 w04.2.1 h5
  refine ⟨(w04.trans w45).mono fun b hb => ?_, ?_⟩
  · simp only [LawfulStore.QFoot]; tauto
  · have ni := inq_not_link_node (W := t :: xs) (Q := (fun o => o = 120 ∨ o = 128)) hT hW hN' ht  -- a64: IPI_PENDING pair
    have ni' := inq_not_link_node (W := t :: xs) (Q := (136 ≤ ·)) hT hW hN ht  -- a64: 128->136
    rw [w45.mem_eq (inqA_aligned hta) ni.2, s4_post, L.mem_wr_same (inqA_aligned hta),
      w03.mem_eq (inqA_aligned hta) (by rintro (((h | h) | h)) <;> [exact ni'.2 h; exact ni'.1 h; exact ni'.2 h])]

/-- The footprint of `enqueue`: the `Sched` links of `t` and of its queue,
the bitmap and ready-queue words of its core, its `IN_QUEUES` word (which
gets `Q_QUEUED`), and the current core's `IPI_PENDING`. -/
theorem sched.enqueue.foot (s : S) (t : obj.Tcb) (xs : List U64) (hT : TcbPlaced T) (ht : t ∈ T)
    (hp : (L.mem s (prioA t)).val < 256)
    (hN : NodePlaced st T s (L.mem s (affA t))) (hN' : NodePlaced st T s (L.cpu s))
    (hr : QueueRel (L.mem s) T .Sched (L.rqQ s (L.mem s (affA t)) (L.mem s (prioA t))) xs)
    (hq : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 → t ∉ xs) :
    sched.enqueue st s t ⦃ s' => WritesIn st s s' (L.QFoot s (t :: xs) (L.mem s (affA t)) (136 ≤ ·) t) ∧  -- a64: 128->136
      L.mem s' (inqA t) = if (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64 then L.mem s (inqA t)
        else L.mem s (inqA t) ||| sched.Q_QUEUED ⦄ := by
  unfold sched.enqueue
  step*
  · have hq1 : (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64 := by
      intro hc; have := ‹b = true›; rw [b_post] at this; exact of_decide_eq_true this hc
    simp only [ne_eq, hq1, not_false_eq_true, if_true]
    exact ⟨WritesIn.refl _ _, by trivial⟩
  have hq0 : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 := by
    by_contra hc; exact ‹¬b = true› (by rw [b_post]; exact decide_eq_true hc)
  simp only [hq0, ne_eq, not_true_eq_false, if_false]
  subst cpu_post prio_post off_post
  have hqq : q = L.rqQ s (L.mem s (affA t)) (L.mem s (prioA t)) := by
    rw [q_post, off_post1]; rfl
  by_cases hb1 : b1 = true
  · rw [ite_cond_eq_true _ _ (eq_true hb1)]
    refine WP.spec_bind (sched.add_to_bitmap.spec s _ dom _ hp) ?_
    rintro s1 ⟨v1, v2, rfl, -, -⟩
    have hg : (L.mem s (prioA t)).val / 64 < 4 := by omega
    have w1 : WritesIn st s (L.wr (L.wr s (L.nodeAt s (L.mem s (affA t)) l1Off) v1)
        (L.nodeAt s (L.mem s (affA t)) (l2Off ((L.mem s (prioA t)).val / 64))) v2)
        (L.NodeOf s (L.mem s (affA t)) (136 ≤ ·)) :=  -- a64: 128->136
      ((writesIn_node (P := (136 ≤ ·)) hN (by simp [l1Off_val]) (by simp [l1Off_val]) (by simp [l1Off_val])).trans  -- a64: 128->136
        (writesIn_node (P := (136 ≤ ·)) hN (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega)  -- a64: 128->136
          (by rw [l2Off_val hg]; omega))).mono fun b hb => by rcases hb with hb | hb <;> exact hb
    have hN1 : NodePlaced st T (L.wr s (L.nodeAt s (L.mem s (affA t)) l1Off) v1) (L.mem s (affA t)) := hN.wr
    have hr1 := (hr.wr_node (v := v1) hT hN (by rw [l1Off_val]; omega) (by rw [l1Off_val])).wr_node (v := v2)
      hT hN1 (off := l2Off ((L.mem s (prioA t)).val / 64)) (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega)
    rw [show L.nodeAt (L.wr s (L.nodeAt s (L.mem s (affA t)) l1Off) v1) (L.mem s (affA t))
      (l2Off ((L.mem s (prioA t)).val / 64)) = L.nodeAt s (L.mem s (affA t)) (l2Off ((L.mem s (prioA t)).val / 64))
      by simp] at hr1
    exact enqueue_foot_tail s _ t _ _ _ q xs hT ht hp hN hN' w1 (hqq ▸ hr1) (hq hq0) rfl off_post1
  · rw [ite_cond_eq_false _ _ (eq_false hb1)]
    simp only [bind_ok]
    exact enqueue_foot_tail s s t _ _ _ q xs hT ht hp hN hN' (WritesIn.refl _ _) (hqq ▸ hr) (hq hq0) rfl off_post1

/-! ## The footprint of `dequeue` -/

/-- The footprint of `dequeue`: the `Sched` links of its queue, the bitmap
and ready-queue words of its core, and its `IN_QUEUES` word (which loses
`Q_QUEUED`). -/
theorem sched.dequeue.foot (s : S) (t : obj.Tcb) (xs : List U64) (hT : TcbPlaced T) (ht : t ∈ T)
    (hp : (L.mem s (prioA t)).val < 256)
    (hN : NodePlaced st T s (L.mem s (affA t))) (hN' : NodePlaced st T s (L.cpu s))
    (hr : QueueRel (L.mem s) T .Sched (L.rqQ s (L.mem s (affA t)) (L.mem s (prioA t))) xs)
    (hq : (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64 → t ∈ xs) :
    sched.dequeue st s t ⦃ s' => WritesIn st s s' (L.QFoot s xs (L.mem s (affA t)) (136 ≤ ·) t) ∧  -- a64: 128->136
      L.mem s' (inqA t) = if (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64
        then L.mem s (inqA t) &&& ~~~sched.Q_QUEUED else L.mem s (inqA t) ⦄ := by
  have hta : TcbAddr t := hT t ht
  unfold sched.dequeue
  step*
  · have hq1 : (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64 := by
      intro hc; have := ‹b = true›; rw [b_post] at this; exact of_decide_eq_true this hc
    rw [ite_cond_eq_true _ _ (eq_true hq1)]
    subst cpu_post prio_post off_post
    have hqq : q = L.rqQ s (L.mem s (affA t)) (L.mem s (prioA t)) := by rw [q_post, off_post1]; rfl
    have htx := hq hq1
    have hW : ∀ w ∈ xs, w ∈ T := hr.mem
    refine WP.spec_bind (tcbqueue.remove.rel s .Sched q t xs hT (hqq ▸ hr) htx) ?_
    rintro ⟨q1, s1⟩ h1
    simp only [WP.uncurry'_pair] at h1
    obtain ⟨-, hf1, -, -⟩ := h1
    have w01 := hf1.writesIn
    step as ⟨s2, s2_post⟩
    have w12 : WritesIn st s1 s2 (L.NodeOf s (L.mem s (affA t)) (136 ≤ ·)) := by  -- a64: 128->136
      rw [s2_post, nodeAt_of_ksb w01.1, nodeAt_of_ksb w01.1, off_post1]
      exact ((writesIn_node (P := (136 ≤ ·)) hN (by rw [rqOff_val hp]; omega) (by rw [rqOff_val hp]; omega)  -- a64: 128->136
        (by rw [rqOff_val hp]; omega)).trans (writesIn_node (P := (136 ≤ ·)) hN (by rw [rqTailOff_val hp]; omega)  -- a64: 128->136
        (by rw [rqTailOff_val hp]; omega) (by rw [rqTailOff_val hp]; omega))).mono fun b hb => by
          rcases hb with hb | hb <;> exact hb
    have w02 := w01.trans w12
    step as ⟨s3, s3_post⟩
    simp only [Bool.false_eq_true, ite_false] at s3_post
    have w23 : WritesIn st s2 s3 (· = inqA t) := by rw [s3_post]; exact writesIn_inq hta
    have w03 := w02.trans w23
    have ni := inq_not_link_node (W := xs) (Q := (136 ≤ ·)) hT hW hN ht  -- a64: 128->136
    have hinq3 : L.mem s3 (inqA t) = L.mem s (inqA t) &&& ~~~sched.Q_QUEUED := by
      rw [s3_post, L.mem_wr_same (inqA_aligned hta),
        w02.mem_eq (inqA_aligned hta) (by rintro (h | h) <;> [exact ni.1 h; exact ni.2 h])]
    have fin : ∀ s4, WritesIn st s3 s4 (L.NodeOf s (L.mem s (affA t)) (136 ≤ ·)) →  -- a64: 128->136
        WritesIn st s s4 (L.QFoot s xs (L.mem s (affA t)) (136 ≤ ·) t) ∧  -- a64: 128->136
        L.mem s4 (inqA t) = L.mem s (inqA t) &&& ~~~sched.Q_QUEUED := by
      intro s4 w34
      refine ⟨(w03.trans w34).mono fun b hb => ?_, ?_⟩
      · rcases hb with ((h | h) | h) | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inl h)
      · rw [w34.mem_eq (inqA_aligned hta) ni.2, hinq3]
    step as ⟨b1, b1_post⟩
    split
    · refine WP.spec_mono (sched.remove_from_bitmap.spec s3 _ dom _ hp) ?_
      rintro s4 ⟨v2, -, hs4⟩
      have hg : (L.mem s (prioA t)).val / 64 < 4 := by omega
      have hk3 := w03.1
      apply fin
      by_cases hz : v2 = 0#u64
      · rw [if_pos hz] at hs4
        obtain ⟨v1, rfl, -⟩ := hs4
        rw [nodeAt_of_ksb hk3, nodeAt_of_ksb hk3]
        exact ((writesIn_node (P := (136 ≤ ·)) hN (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega)  -- a64: 128->136
          (by rw [l2Off_val hg]; omega)).trans (writesIn_node (P := (136 ≤ ·)) hN (by simp [l1Off_val])  -- a64: 128->136
          (by simp [l1Off_val]) (by simp [l1Off_val]))).mono fun b hb => by rcases hb with hb | hb <;> exact hb
      · rw [if_neg hz] at hs4
        subst hs4
        rw [nodeAt_of_ksb hk3]
        exact writesIn_node (P := (136 ≤ ·)) hN (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega)  -- a64: 128->136
          (by rw [l2Off_val hg]; omega)
    · simp only [WP.spec_ok]
      exact fin s3 (WritesIn.refl _ _)
  · have hq0 : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 := by
      by_contra hc; exact ‹¬b = true› (by rw [b_post]; exact decide_eq_true hc)
    simp only [hq0, ne_eq, not_true_eq_false, ite_false]
    exact ⟨WritesIn.refl _ _, trivial⟩

/-! ## The footprints of `release_enqueue` and `release_remove` -/

/-- The node offsets the release queue code writes: `REPROGRAM` and the
release queue's head and tail. -/
def RelOffs (o : Nat) : Prop := o = 56 ∨ o = 64 ∨ o = 72

theorem release_tail_foot (s s3 : S) (c x : U64) (t : obj.Tcb) (hT : TcbPlaced T) (ht : t ∈ T)
    (hN : NodePlaced st T s c) (hN' : NodePlaced st T s (L.cpu s))
    (hk : L.ksb s3 = L.ksb s) (hc : L.cpu s3 = L.cpu s) :
    (do
      let s4 ← sched.set_flag st s3 t sched.Q_RELEASE true
      let i ← obj.node_get st s4 c layout.node.RELEASE_HEAD
      let s5 ← if (i != x) = true then sched.set_reprogram_on st s4 c else ok s4
      smp.remote_queue_update st s5 t) ⦃ s' =>
    WritesIn st s3 s' (fun b => b = inqA t ∨ L.NodeOf s c RelOffs b ∨ L.NodeOf s (L.cpu s) (fun o => o = 120 ∨ o = 128) b) ∧  -- a64: IPI_PENDING pair
      L.mem s' (inqA t) = L.mem s3 (inqA t) ||| sched.Q_RELEASE ⦄ := by
  have hta : TcbAddr t := hT t ht
  step as ⟨s4, s4_post⟩
  simp only [ite_true] at s4_post
  have w34 : WritesIn st s3 s4 (· = inqA t) := by rw [s4_post]; exact writesIn_inq hta
  have hi4 : L.mem s4 (inqA t) = L.mem s3 (inqA t) ||| sched.Q_RELEASE := by
    rw [s4_post, L.mem_wr_same (inqA_aligned hta)]
  have hk4 : L.ksb s4 = L.ksb s := w34.1.trans hk
  have hc4 : L.cpu s4 = L.cpu s := w34.2.1.trans hc
  step as ⟨i, _⟩
  have fin : ∀ s5, WritesIn st s4 s5 (L.NodeOf s c RelOffs) →
      smp.remote_queue_update st s5 t ⦃ s' =>
        WritesIn st s3 s' (fun b => b = inqA t ∨ L.NodeOf s c RelOffs b ∨ L.NodeOf s (L.cpu s) (fun o => o = 120 ∨ o = 128) b) ∧  -- a64: IPI_PENDING pair
        L.mem s' (inqA t) = L.mem s3 (inqA t) ||| sched.Q_RELEASE ⦄ := by
    intro s5 w45
    refine WP.spec_mono (smp.remote_queue_update.spec s5 t) ?_
    intro s6 h6
    have w56 := remote_writesIn hN' (w45.1.trans hk4) (w45.2.1.trans hc4) h6
    refine ⟨((w34.trans w45).trans w56).mono fun b hb => ?_, ?_⟩
    · rcases hb with (h | h) | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · have n1 := inq_not_link_node (W := []) (Q := (fun o => o = 120 ∨ o = 128)) hT (by simp) hN' ht  -- a64: IPI_PENDING pair
      have n2 := inq_not_link_node (W := []) (Q := RelOffs) hT (by simp) hN ht
      rw [w56.mem_eq (inqA_aligned hta) n1.2, w45.mem_eq (inqA_aligned hta) n2.2, hi4]
  split
  · step as ⟨s5, s5_post⟩
    apply fin
    rw [s5_post, nodeAt_of_ksb hk4]
    exact writesIn_node (P := RelOffs) hN (by rw [repr_val]; simp [RelOffs]) (by rw [repr_val]; omega) (by rw [repr_val])
  · simp only [bind_ok]; exact fin s4 (WritesIn.refl _ _)

/-- After the list operation: store the new queue, then the tail. -/
theorem release_qset_foot (s s1 : S) (c : U64) (nq : tcbqueue.Queue) (x : U64) (t : obj.Tcb) (xs : List U64)
    (hT : TcbPlaced T) (ht : t ∈ T) (hN : NodePlaced st T s c) (hN' : NodePlaced st T s (L.cpu s))
    (h1 : WritesIn st s s1 (LinkOf .Sched (t :: xs))) (hW : ∀ w ∈ t :: xs, w ∈ T) :
    (do
      let s2 ← sched.q_set st s1 c layout.node.RELEASE_HEAD nq
      let s3 ← sched.set_flag st s2 t sched.Q_RELEASE true
      let i ← obj.node_get st s3 c layout.node.RELEASE_HEAD
      let s4 ← if (i != x) = true then sched.set_reprogram_on st s3 c else ok s3
      smp.remote_queue_update st s4 t) ⦃ s' =>
    WritesIn st s s' (L.QFoot s (t :: xs) c RelOffs t) ∧
      L.mem s' (inqA t) = L.mem s (inqA t) ||| sched.Q_RELEASE ⦄ := by
  have hta : TcbAddr t := hT t ht
  step as ⟨s2, s2_post⟩
  have w12 : WritesIn st s1 s2 (L.NodeOf s c RelOffs) := by
    rw [s2_post, nodeAt_of_ksb h1.1, nodeAt_of_ksb h1.1]
    exact ((writesIn_node (P := RelOffs) hN (by rw [relh_val]; simp [RelOffs]) (by rw [relh_val]; omega)
      (by rw [relh_val])).trans (writesIn_node (P := RelOffs) hN (by rw [relt_val]; simp [RelOffs])
        (by rw [relt_val]; omega) (by rw [relt_val]))).mono fun b hb => by rcases hb with hb | hb <;> exact hb
  have w02 := h1.trans w12
  refine WP.spec_mono (release_tail_foot s s2 c x t hT ht hN hN' w02.1 w02.2.1) ?_
  rintro s' ⟨w2', hi⟩
  have ni := inq_not_link_node (W := t :: xs) (Q := RelOffs) hT hW hN ht
  refine ⟨(w02.trans w2').mono fun b hb => ?_, ?_⟩
  · rcases hb with (h | h) | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))
  · rw [hi, w02.mem_eq (inqA_aligned hta) (by rintro (h | h) <;> [exact ni.1 h; exact ni.2 h])]

/-- The footprint of `release_enqueue`: the `Sched` links of `t` and of
the release queue, `REPROGRAM` and the release queue words of its core, its
`IN_QUEUES` word (which gets `Q_RELEASE`), and the current core's
`IPI_PENDING`. -/
theorem sched.release_enqueue.foot (s : S) (t : obj.Tcb) (xs : List U64) (hT : TcbPlaced T) (ht : t ∈ T)
    (hn : t ∉ xs) (hN : NodePlaced st T s (L.mem s (affA t))) (hN' : NodePlaced st T s (L.cpu s))
    (h : QueueRel (L.mem s) T .Sched (L.relQ s (L.mem s (affA t))) xs) :
    sched.release_enqueue st s t ⦃ s' => WritesIn st s s' (L.QFoot s (t :: xs) (L.mem s (affA t)) RelOffs t) ∧
      L.mem s' (inqA t) = L.mem s (inqA t) ||| sched.Q_RELEASE ⦄ := by
  have hta : TcbAddr t := hT t ht
  have hW : ∀ w ∈ t :: xs, w ∈ T := by
    intro w hw; rcases List.mem_cons.1 hw with rfl | hw
    · exact ht
    · exact h.mem w hw
  unfold sched.release_enqueue
  step*
  all_goals subst cpu_post new_time_post
  all_goals have hqq : q = L.relQ s (L.mem s (affA t)) := by rw [q_post]; rfl
  all_goals have h0 := hqq ▸ h
  · refine WP.spec_bind (tcbqueue.prepend.rel s .Sched q t xs hT h0 ht hn) ?_
    rintro ⟨nq, s1⟩ h1
    simp only [WP.uncurry'_pair] at h1
    exact release_qset_foot s s1 _ nq q.head t xs hT ht hN hN' h1.2.writesIn hW
  · refine WP.spec_bind (tcbqueue.prepend.rel s .Sched q t xs hT h0 ht hn) ?_
    rintro ⟨nq, s1⟩ h1
    simp only [WP.uncurry'_pair] at h1
    exact release_qset_foot s s1 _ nq q.head t xs hT ht hN hN' h1.2.writesIn hW
  · refine WP.spec_bind (tcbqueue.append.rel s .Sched q t xs hT h0 ht hn) ?_
    rintro ⟨nq, s1⟩ h1
    simp only [WP.uncurry'_pair] at h1
    exact release_qset_foot s s1 _ nq q.head t xs hT ht hN hN' h1.2.writesIn hW
  · have hne : xs ≠ [] := by
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
    rintro s2 ⟨-, hf2⟩
    rw [← hx'] at hf2
    have w02 := hf2.writesIn
    refine WP.spec_mono (release_tail_foot s s2 _ q.head t hT ht hN hN' w02.1 w02.2.1) ?_
    rintro s' ⟨w2', hi⟩
    have ni := inq_not_link_node (W := t :: xs) (Q := RelOffs) hT hW hN ht
    refine ⟨(w02.trans w2').mono fun b hb => ?_, ?_⟩
    · rcases hb with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr h))
    · rw [hi, w02.mem_eq (inqA_aligned hta) ni.1]

/-- The footprint of `release_remove`: the `Sched` links of the release
queue, `REPROGRAM` and the release queue words of its core, and its
`IN_QUEUES` word (which loses `Q_RELEASE`). -/
theorem sched.release_remove.foot (s : S) (t : obj.Tcb) (xs : List U64) (hT : TcbPlaced T) (ht : t ∈ T)
    (hN : NodePlaced st T s (L.mem s (affA t))) (hN' : NodePlaced st T s (L.cpu s))
    (h : QueueRel (L.mem s) T .Sched (L.relQ s (L.mem s (affA t))) xs)
    (hq : (L.mem s (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64 → t ∈ xs) :
    sched.release_remove st s t ⦃ s' => WritesIn st s s' (L.QFoot s xs (L.mem s (affA t)) RelOffs t) ∧
      L.mem s' (inqA t) = if (L.mem s (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64
        then L.mem s (inqA t) &&& ~~~sched.Q_RELEASE else L.mem s (inqA t) ⦄ := by
  have hta : TcbAddr t := hT t ht
  have hW : ∀ w ∈ xs, w ∈ T := h.mem
  unfold sched.release_remove
  step*
  · have hq1 : (L.mem s (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64 := by
      intro hc; have := ‹b = true›; rw [b_post] at this; exact of_decide_eq_true this hc
    rw [ite_cond_eq_true _ _ (eq_true hq1)]
    subst cpu_post
    have htx := hq hq1
    have ni := inq_not_link_node (W := xs) (Q := RelOffs) hT hW hN ht
    have key : ∀ s1 : S, WritesIn st s s1 (L.NodeOf s (L.mem s (affA t)) RelOffs) →
        QueueRel (L.mem s1) T .Sched (L.relQ s1 (L.mem s (affA t))) xs →
        (do
          let q ← sched.q_get st s1 (L.mem s (affA t)) layout.node.RELEASE_HEAD
          let (q1, s2) ← tcbqueue.remove st s1 tcbqueue.Link.Sched q t
          let s3 ← sched.q_set st s2 (L.mem s (affA t)) layout.node.RELEASE_HEAD q1
          sched.set_flag st s3 t sched.Q_RELEASE false) ⦃ s' =>
        WritesIn st s s' (L.QFoot s xs (L.mem s (affA t)) RelOffs t) ∧
          L.mem s' (inqA t) = L.mem s (inqA t) &&& ~~~sched.Q_RELEASE ⦄ := by
      intro s1 w01 h1
      step as ⟨q, q_post⟩
      have hq' : q = L.relQ s1 (L.mem s (affA t)) := by rw [q_post]; rfl
      refine WP.spec_bind (tcbqueue.remove.rel s1 .Sched q t xs hT (hq' ▸ h1) htx) ?_
      rintro ⟨q1, s2⟩ h2
      simp only [WP.uncurry'_pair] at h2
      obtain ⟨-, hf2, -, -⟩ := h2
      have w02 := w01.trans hf2.writesIn
      step as ⟨s3, s3_post⟩
      have w23 : WritesIn st s2 s3 (L.NodeOf s (L.mem s (affA t)) RelOffs) := by
        rw [s3_post, nodeAt_of_ksb w02.1, nodeAt_of_ksb w02.1]
        exact ((writesIn_node (P := RelOffs) hN (by rw [relh_val]; simp [RelOffs]) (by rw [relh_val]; omega)
          (by rw [relh_val])).trans (writesIn_node (P := RelOffs) hN (by rw [relt_val]; simp [RelOffs])
            (by rw [relt_val]; omega) (by rw [relt_val]))).mono fun b hb => by rcases hb with hb | hb <;> exact hb
      have w03 := w02.trans w23
      step as ⟨s4, s4_post⟩
      simp only [Bool.false_eq_true, ite_false] at s4_post
      have w34 : WritesIn st s3 s4 (· = inqA t) := by rw [s4_post]; exact writesIn_inq hta
      refine ⟨(w03.trans w34).mono fun b hb => ?_, ?_⟩
      · rcases hb with ((h | h) | h) | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
      · rw [s4_post, L.mem_wr_same (inqA_aligned hta),
          w03.mem_eq (inqA_aligned hta) (by rintro ((h | h) | h) <;> [exact ni.2 h; exact ni.1 h; exact ni.2 h])]
    split
    · step as ⟨s1, s1_post⟩
      subst s1_post
      refine key _ (writesIn_node (P := RelOffs) hN (by rw [repr_val]; simp [RelOffs]) (by rw [repr_val]; omega)
        (by rw [repr_val])) ?_
      rw [relQ_wr_node hN hN (by rw [repr_val]; omega) (by rw [repr_val]) (fun _ => by rw [repr_val]; omega)]
      exact h.wr_node hT hN (by rw [repr_val]; omega) (by rw [repr_val])
    · simp only [bind_ok]
      exact key s (WritesIn.refl _ _) h
  · have hq0 : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by
      by_contra hc; exact ‹¬b = true› (by rw [b_post]; exact decide_eq_true hc)
    simp only [hq0, ne_eq, not_true_eq_false, ite_false]
    exact ⟨WritesIn.refl _ _, trivial⟩

end

end Fl4ProofsA64.P1
