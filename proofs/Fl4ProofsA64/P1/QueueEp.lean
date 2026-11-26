-- AArch64 port of Fl4Proofs.P1.QueueEp (proofs/scratch/a64/port.py): the x86_64 text, re-checked
-- over Fl4CoreA64. Edits beyond the renaming are marked `-- a64:`.
/-
P1: endpoint queues (endpoint.rs `ep_append`, `ep_dequeue`; seL4
`tcbEPAppend` / `tcbEPDequeue`). The queue head is the endpoint's `HEAD`
word, the end is its `TAIL_STATE` word with the two state bits masked off.
-/
import Fl4ProofsA64.P1.QueueSched
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

def epHeadA (ep : U64) : U64 := core.num.U64.wrapping_add ep layout.ep.HEAD
def epTSA (ep : U64) : U64 := core.num.U64.wrapping_add ep layout.ep.TAIL_STATE

theorem eq_of_bv {x y : U64} (h : x.bv = y.bv) : x = y := by
  cases x; cases y; exact congrArg UScalar.mk h

theorem three_bit (i : Nat) : (3#u64).bv.getLsbD i = decide (i < 2) := by
  have : (3#u64).bv = BitVec.ofNat _ 3 := rfl
  rw [this, BitVec.getLsbD_ofNat]
  rcases i with _ | _ | i <;> simp [Nat.testBit_succ]
/-- The tail word keeps the end and the state apart. -/
theorem ts_end (x y : U64) : ((x &&& ~~~3#u64) ||| (y &&& 3#u64)) &&& ~~~3#u64 = x &&& ~~~3#u64 := by
  apply eq_of_bv; apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [UScalar.bv_and, UScalar.bv_or, UScalar.bv_not, BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_not, three_bit]
  by_cases h : i < 2 <;> simp [h]
theorem ts_state (x y : U64) : ((x &&& ~~~3#u64) ||| (y &&& 3#u64)) &&& 3#u64 = y &&& 3#u64 := by
  apply eq_of_bv; apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [UScalar.bv_and, UScalar.bv_or, UScalar.bv_not, BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_not, three_bit]
  by_cases h : i < 2 <;> simp [h]
theorem mask_of_aligned {x : U64} (h : x.val % 4 = 0) : x &&& ~~~3#u64 = x := by
  apply eq_of_bv; apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [UScalar.bv_and, UScalar.bv_not, BitVec.getLsbD_and, BitVec.getLsbD_not, three_bit]
  by_cases h2 : i < 2
  · have hb : x.bv.getLsbD i = x.val.testBit i := rfl
    have := Nat.testBit_mod_two_pow x.val 2 i
    rw [show (2:Nat)^2 = 4 from rfl, h] at this
    simp [h2] at this
    simp [h2, hb, this]
  · simp [h2, hi]

/-- The end of a related queue is 0 or a TCB, so the state bits are clear. -/
theorem QueueRel.end_mod4 {m T l q xs} (hT : TcbPlaced T) (h : QueueRel m T l q xs) : q.end.val % 4 = 0 := by
  rw [h.last]
  cases xs with
  | nil => rfl
  | cons x xs =>
    have := (h.addr hT _ (getLastD_mem (List.cons_ne_nil x xs) 0#u64)).align
    simp only [UScalar.val] at this ⊢
    omega

/-- The endpoint at `ep`: two words, aligned, outside every TCB of `T`. -/
structure EpPlaced (T : Set U64) (ep : U64) : Prop where
  align : ep.val % 8 = 0
  fits : ep.val + 16 ≤ 2 ^ 64
  disj : ∀ t ∈ T, t.val + 2 ^ 12 ≤ ep.val ∨ ep.val + 16 ≤ t.val

theorem epHeadA_val {ep : U64} : (epHeadA ep).val = ep.val := by
  unfold epHeadA
  rw [core.num.U64.wrapping_add_val_eq]
  have : layout.ep.HEAD.val = 0 := by unfold layout.ep.HEAD; rfl
  rw [this, Nat.add_zero]
  exact Nat.mod_eq_of_lt (by have := ep.hBounds; simpa [U64.size_def, U64.numBits] using this)
theorem epTSA_val {T : Set U64} {ep : U64} (h : EpPlaced T ep) : (epTSA ep).val = ep.val + 8 := by
  have := h.fits
  unfold epTSA
  rw [core.num.U64.wrapping_add_val_eq]
  have : layout.ep.TAIL_STATE.val = 8 := by unfold layout.ep.TAIL_STATE; rfl
  rw [this]
  have : UScalar.size UScalarTy.U64 = 2 ^ 64 := by simp [U64.size_def, U64.numBits]
  exact Nat.mod_eq_of_lt (by omega)

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64}

def LawfulStore.epQ (s : S) (ep : U64) : tcbqueue.Queue :=
  ⟨L.mem s (epHeadA ep), L.mem s (epTSA ep) &&& ~~~3#u64⟩
def LawfulStore.epState (s : S) (ep : U64) : U64 := L.mem s (epTSA ep) &&& 3#u64

@[step] theorem endpoint.get_queue.spec (s : S) (ep : obj.Ep) :
    endpoint.get_queue st s ep ⦃ q => q = L.epQ s ep ⦄ := by
  unfold endpoint.get_queue obj.Ep.head obj.Ep.tail obj.Ep.tail_state; step*; simp_all [LawfulStore.epQ, epHeadA, epTSA]

@[step] theorem obj.Ep.state.spec (s : S) (ep : obj.Ep) :
    obj.Ep.state st ep s ⦃ v => v = L.epState s ep ⦄ := by
  unfold obj.Ep.state obj.Ep.tail_state; step*; simp_all [LawfulStore.epState, epTSA]

@[step] theorem endpoint.set_queue.spec (s : S) (ep : obj.Ep) (q : tcbqueue.Queue) (state : U64) :
    endpoint.set_queue st s ep q state ⦃ s' => s' = L.wr (L.wr s (epHeadA ep) q.head) (epTSA ep)
      ((q.end &&& ~~~3#u64) ||| (state &&& 3#u64)) ⦄ := by
  unfold endpoint.set_queue obj.Ep.set_queue obj.Ep.set_head obj.Ep.set_tail_state
  step*
  subst_vars
  have e3 : i3 = (q.end &&& ~~~3#u64) ||| (state &&& 3#u64) :=
    eq_of_bv (by simp only [i3_post1, i1_post1, i2_post1, UScalar.bv_or, UScalar.bv_and])
  simp only [epHeadA, epTSA, e3]

theorem ep_aligned {ep : U64} (h : EpPlaced T ep) : Aligned (epHeadA ep) ∧ Aligned (epTSA ep) := by
  have := h.align
  exact ⟨by unfold Aligned; rw [epHeadA_val]; omega, by unfold Aligned; rw [epTSA_val h]; omega⟩

/-- An endpoint word is no link field of a TCB of `T`. -/
theorem ep_ne_link {ep a : U64} (h : EpPlaced T ep) (ha : a = epHeadA ep ∨ a = epTSA ep) {y : U64} (hy : y ∈ T)
    (hya : TcbAddr y) (l : tcbqueue.Link) : a ≠ nextA l y ∧ a ≠ prevA l y := by
  have hd := h.disj y hy
  have hav : a.val = ep.val ∨ a.val = ep.val + 8 := by
    rcases ha with rfl | rfl
    · exact Or.inl epHeadA_val
    · exact Or.inr (epTSA_val h)
  constructor <;> intro e <;> have := congrArg UScalar.val e
  · have := nextA_inside hya l; omega
  · have := prevA_inside hya l; omega

/-- `set_queue` stores the queue and the state. -/
theorem ep_set_queue {s : S} {ep state : U64} {q : tcbqueue.Queue} {xs : List U64} (hT : TcbPlaced T)
    (hE : EpPlaced T ep) (h : QueueRel (L.mem s) T .Ep q xs) :
    let s' := L.wr (L.wr s (epHeadA ep) q.head) (epTSA ep) ((q.end &&& ~~~3#u64) ||| (state &&& 3#u64))
    QueueRel (L.mem s') T .Ep (L.epQ s' ep) xs ∧ L.epState s' ep = state &&& 3#u64 := by
  intro s'
  obtain ⟨ah, at'⟩ := ep_aligned hE
  have hne : (epHeadA ep).val ≠ (epTSA ep).val := by rw [epHeadA_val, epTSA_val hE]; omega
  have e1 : L.mem s' (epHeadA ep) = q.head := by
    simp only [s']; rw [L.mem_wr_ne at' ah (Ne.symm hne), L.mem_wr_same ah]
  have e2 : L.mem s' (epTSA ep) = (q.end &&& ~~~3#u64) ||| (state &&& 3#u64) := by
    simp only [s']; rw [L.mem_wr_same at']
  have hq : L.epQ s' ep = q := by
    simp only [LawfulStore.epQ, e1, e2]
    rw [ts_end, mask_of_aligned (h.end_mod4 hT)]
  refine ⟨?_, by simp only [LawfulStore.epState, e2, ts_state]⟩
  rw [hq]
  refine (h.wr_out hT ah fun y hy => ep_ne_link hE (Or.inl rfl) (h.mem y hy) (h.addr hT y hy) .Ep).wr_out
    hT at' fun y hy => ep_ne_link hE (Or.inr rfl) (h.mem y hy) (h.addr hT y hy) .Ep

/-- seL4 `tcbEPAppend`: the endpoint's queue becomes the priority-ordered
insertion of `t`, and the state is the one given. -/
theorem endpoint.ep_append.rel (s : S) (ep : obj.Ep) (t : obj.Tcb) (state : U64) (xs : List U64)
    (hT : TcbPlaced T) (hE : EpPlaced T ep) (h : QueueRel (L.mem s) T .Ep (L.epQ s ep) xs)
    (ht : t ∈ T) (hn : t ∉ xs) :
    endpoint.ep_append st s ep t state ⦃ s' =>
      QueueRel (L.mem s') T .Ep (L.epQ s' ep) (insPrio (fun y => L.mem s (prioA y)) (L.mem s (prioA t)) t xs) ∧
      L.epState s' ep = state &&& 3#u64 ⦄ := by
  unfold endpoint.ep_append
  step*
  subst q_post
  refine WP.spec_bind (tcbqueue.append_by_prio.rel s .Ep _ t xs hT h ht hn) ?_
  rintro ⟨q1, s1⟩ h1
  simp only [WP.uncurry'_pair] at h1
  obtain ⟨hr1, -⟩ := h1
  step*
  subst_vars
  exact ep_set_queue hT hE hr1

/-- seL4 `tcbEPDequeue`: the member `t` leaves the endpoint's queue; the
state becomes idle (0) if the queue is now empty and is kept otherwise. -/
theorem endpoint.ep_dequeue.rel (s : S) (ep : U64) (t : obj.Tcb) (xs : List U64)
    (hT : TcbPlaced T) (hE : EpPlaced T ep) (h : QueueRel (L.mem s) T .Ep (L.epQ s ep) xs) (ht : t ∈ xs) :
    endpoint.ep_dequeue st s ep t ⦃ s' =>
      QueueRel (L.mem s') T .Ep (L.epQ s' ep) (xs.erase t) ∧
      L.epState s' ep = if xs.erase t = [] then 0#u64 else L.epState s ep ⦄ := by
  unfold endpoint.ep_dequeue
  step*
  subst q_post
  refine WP.spec_bind (tcbqueue.remove.rel s .Ep _ t xs hT h ht) ?_
  rintro ⟨q1, s1⟩ h1
  simp only [WP.uncurry'_pair] at h1
  obtain ⟨hr1, -, -, -⟩ := h1
  step*
  · subst s'_post
    have hemp : xs.erase t = [] := (hr1.empty_iff hT).1 (by simpa [b_post] using ‹b = true›)
    obtain ⟨h1, h2⟩ := ep_set_queue (state := obj.EP_IDLE) hT hE hr1
    refine ⟨h1, ?_⟩
    rw [h2, if_pos hemp]
    unfold obj.EP_IDLE
    exact UScalar.eq_of_val_eq (by simp)
  · subst s'_post
    have hne : xs.erase t ≠ [] := by
      rw [Ne, ← hr1.empty_iff hT]; simpa [b_post] using ‹¬b = true›
    obtain ⟨h1, h2⟩ := ep_set_queue (state := st) hT hE hr1
    refine ⟨h1, ?_⟩
    rw [h2, if_neg hne, st_post]
    apply eq_of_bv
    simp only [LawfulStore.epState, UScalar.bv_and, BitVec.and_assoc, BitVec.and_self]

/-! ## Notifications: the same two words (layout.rs `ntfn::HEAD`, `TAIL_STATE`) -/

theorem ntfn_head_eq : layout.ntfn.HEAD = layout.ep.HEAD := by unfold layout.ntfn.HEAD layout.ep.HEAD; rfl
theorem ntfn_ts_eq : layout.ntfn.TAIL_STATE = layout.ep.TAIL_STATE := by
  unfold layout.ntfn.TAIL_STATE layout.ep.TAIL_STATE; rfl

@[step] theorem notification.get_queue.spec (s : S) (n : obj.Ntfn) :
    notification.get_queue st s n ⦃ q => q = L.epQ s n ⦄ := by
  unfold notification.get_queue obj.Ntfn.head obj.Ntfn.tail obj.Ntfn.tail_state
  step*; simp_all [LawfulStore.epQ, epHeadA, epTSA, ntfn_head_eq, ntfn_ts_eq]

@[step] theorem obj.Ntfn.state.spec (s : S) (n : obj.Ntfn) :
    obj.Ntfn.state st n s ⦃ v => v = L.epState s n ⦄ := by
  unfold obj.Ntfn.state obj.Ntfn.tail_state; step*; simp_all [LawfulStore.epState, epTSA, ntfn_ts_eq]

@[step] theorem notification.set_queue.spec (s : S) (n : obj.Ntfn) (q : tcbqueue.Queue) (state : U64) :
    notification.set_queue st s n q state ⦃ s' => s' = L.wr (L.wr s (epHeadA n) q.head) (epTSA n)
      ((q.end &&& ~~~3#u64) ||| (state &&& 3#u64)) ⦄ := by
  unfold notification.set_queue obj.Ntfn.set_queue obj.Ntfn.set_head obj.Ntfn.set_tail_state
  step*
  subst_vars
  have e3 : i3 = (q.end &&& ~~~3#u64) ||| (state &&& 3#u64) :=
    eq_of_bv (by simp only [i3_post1, i1_post1, i2_post1, UScalar.bv_or, UScalar.bv_and])
  simp only [epHeadA, epTSA, e3, ntfn_head_eq, ntfn_ts_eq]

/-- `ntfn_append`: priority-ordered insertion; the state becomes waiting. -/
theorem notification.ntfn_append.rel (s : S) (n : obj.Ntfn) (t : obj.Tcb) (xs : List U64)
    (hT : TcbPlaced T) (hE : EpPlaced T n) (h : QueueRel (L.mem s) T .Ep (L.epQ s n) xs)
    (ht : t ∈ T) (hn : t ∉ xs) :
    notification.ntfn_append st s n t ⦃ s' =>
      QueueRel (L.mem s') T .Ep (L.epQ s' n) (insPrio (fun y => L.mem s (prioA y)) (L.mem s (prioA t)) t xs) ∧
      L.epState s' n = obj.NTFN_WAITING &&& 3#u64 ⦄ := by
  unfold notification.ntfn_append
  step*
  subst q_post
  refine WP.spec_bind (tcbqueue.append_by_prio.rel s .Ep _ t xs hT h ht hn) ?_
  rintro ⟨q1, s1⟩ h1
  simp only [WP.uncurry'_pair] at h1
  obtain ⟨hr1, -⟩ := h1
  step*
  subst_vars
  exact ep_set_queue hT hE hr1

/-- `ntfn_dequeue`: the member `t` leaves; the state becomes idle if the
queue is now empty and is kept otherwise. -/
theorem notification.ntfn_dequeue.rel (s : S) (n : obj.Ntfn) (t : obj.Tcb) (xs : List U64)
    (hT : TcbPlaced T) (hE : EpPlaced T n) (h : QueueRel (L.mem s) T .Ep (L.epQ s n) xs) (ht : t ∈ xs) :
    notification.ntfn_dequeue st s n t ⦃ s' =>
      QueueRel (L.mem s') T .Ep (L.epQ s' n) (xs.erase t) ∧
      L.epState s' n = if xs.erase t = [] then 0#u64 else L.epState s n ⦄ := by
  unfold notification.ntfn_dequeue
  step*
  subst q_post
  refine WP.spec_bind (tcbqueue.remove.rel s .Ep _ t xs hT h ht) ?_
  rintro ⟨q1, s1⟩ h1
  simp only [WP.uncurry'_pair] at h1
  obtain ⟨hr1, -, -, -⟩ := h1
  step*
  · subst s'_post
    have hemp : xs.erase t = [] := (hr1.empty_iff hT).1 (by simpa [b_post] using ‹b = true›)
    obtain ⟨h1, h2⟩ := ep_set_queue (state := obj.NTFN_IDLE) hT hE hr1
    refine ⟨h1, ?_⟩
    rw [h2, if_pos hemp]
    unfold obj.NTFN_IDLE
    exact UScalar.eq_of_val_eq (by simp)
  · subst s'_post
    have hne : xs.erase t ≠ [] := by
      rw [Ne, ← hr1.empty_iff hT]; simpa [b_post] using ‹¬b = true›
    obtain ⟨h1, h2⟩ := ep_set_queue (state := st) hT hE hr1
    refine ⟨h1, ?_⟩
    rw [h2, if_neg hne, st_post]
    apply eq_of_bv
    simp only [LawfulStore.epState, UScalar.bv_and, BitVec.and_assoc, BitVec.and_self]

/-! ## Reordering after a priority change (seL4 `reorderEP`, `reorderNTFN`) -/

theorem epState_and3 (s : S) (ep : U64) : L.epState s ep &&& 3#u64 = L.epState s ep := by
  apply eq_of_bv
  simp only [LawfulStore.epState, UScalar.bv_and, BitVec.and_assoc, BitVec.and_self]

/-- `reorder_ep`: `t` is taken out and put back in priority order; the
state is kept. -/
theorem endpoint.reorder_ep.rel (s : S) (ep : U64) (t : obj.Tcb) (xs : List U64)
    (hT : TcbPlaced T) (hE : EpPlaced T ep) (h : QueueRel (L.mem s) T .Ep (L.epQ s ep) xs) (ht : t ∈ xs) :
    endpoint.reorder_ep st s ep t ⦃ s' =>
      QueueRel (L.mem s') T .Ep (L.epQ s' ep)
        (insPrio (fun y => L.mem s (prioA y)) (L.mem s (prioA t)) t (xs.erase t)) ∧
      L.epState s' ep = L.epState s ep ⦄ := by
  unfold endpoint.reorder_ep
  step*
  subst q_post
  refine WP.spec_bind (tcbqueue.remove.rel s .Ep _ t xs hT h ht) ?_
  rintro ⟨q1, s1⟩ h1
  simp only [WP.uncurry'_pair] at h1
  obtain ⟨hr1, hf1, -, -⟩ := h1
  have htT : t ∈ T := h.mem t ht
  have hn : t ∉ xs.erase t := h.nodup.not_mem_erase
  refine WP.spec_bind (tcbqueue.append_by_prio.rel s1 .Ep q1 t _ hT hr1 htT hn) ?_
  rintro ⟨q2, s2⟩ h2
  simp only [WP.uncurry'_pair] at h2
  obtain ⟨hr2, -⟩ := h2
  have hW : ∀ w ∈ xs, TcbAddr w := h.addr hT
  have hpr : ∀ y, TcbAddr y → L.mem s1 (prioA y) = L.mem s (prioA y) := fun y hy => prio_framed hy hW hf1
  step*
  subst_vars
  obtain ⟨h3, h4⟩ := ep_set_queue (state := L.epState s ep) hT hE hr2
  refine ⟨?_, by rw [h4, epState_and3]⟩
  have e : insPrio (fun y => L.mem s1 (prioA y)) (L.mem s1 (prioA t)) t (xs.erase t) =
      insPrio (fun y => L.mem s (prioA y)) (L.mem s (prioA t)) t (xs.erase t) := by
    rw [hpr t (hW t ht)]
    exact insPrio_congr fun y hy => hpr y (hW y (List.mem_of_mem_erase hy))
  rw [← e]; exact h3

/-- `reorder_ntfn`: `t` is taken out and put back in priority order; the
state is kept. -/
theorem notification.reorder_ntfn.rel (s : S) (ep : U64) (t : obj.Tcb) (xs : List U64)
    (hT : TcbPlaced T) (hE : EpPlaced T ep) (h : QueueRel (L.mem s) T .Ep (L.epQ s ep) xs) (ht : t ∈ xs) :
    notification.reorder_ntfn st s ep t ⦃ s' =>
      QueueRel (L.mem s') T .Ep (L.epQ s' ep)
        (insPrio (fun y => L.mem s (prioA y)) (L.mem s (prioA t)) t (xs.erase t)) ∧
      L.epState s' ep = L.epState s ep ⦄ := by
  unfold notification.reorder_ntfn
  step*
  subst q_post
  refine WP.spec_bind (tcbqueue.remove.rel s .Ep _ t xs hT h ht) ?_
  rintro ⟨q1, s1⟩ h1
  simp only [WP.uncurry'_pair] at h1
  obtain ⟨hr1, hf1, -, -⟩ := h1
  have htT : t ∈ T := h.mem t ht
  have hn : t ∉ xs.erase t := h.nodup.not_mem_erase
  refine WP.spec_bind (tcbqueue.append_by_prio.rel s1 .Ep q1 t _ hT hr1 htT hn) ?_
  rintro ⟨q2, s2⟩ h2
  simp only [WP.uncurry'_pair] at h2
  obtain ⟨hr2, -⟩ := h2
  have hW : ∀ w ∈ xs, TcbAddr w := h.addr hT
  have hpr : ∀ y, TcbAddr y → L.mem s1 (prioA y) = L.mem s (prioA y) := fun y hy => prio_framed hy hW hf1
  step*
  subst_vars
  obtain ⟨h3, h4⟩ := ep_set_queue (state := L.epState s ep) hT hE hr2
  refine ⟨?_, by rw [h4, epState_and3]⟩
  have e : insPrio (fun y => L.mem s1 (prioA y)) (L.mem s1 (prioA t)) t (xs.erase t) =
      insPrio (fun y => L.mem s (prioA y)) (L.mem s (prioA t)) t (xs.erase t) := by
    rw [hpr t (hW t ht)]
    exact insPrio_congr fun y hy => hpr y (hW y (List.mem_of_mem_erase hy))
  rw [← e]; exact h3

end

end Fl4ProofsA64.P1
