/-
P1: the scheduler's queues (sched.rs). Ready queues (per core, per priority;
one domain in this configuration) with their two-level bitmap, and the
release queue ordered by ready time.
-/
import Fl4Proofs.P1.QueuePrio
import Fl4Proofs.P1.Refill
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

def affA (t : U64) : U64 := core.num.U64.wrapping_add t 3520#u64
def domA (t : U64) : U64 := core.num.U64.wrapping_add t 3432#u64
def inqA (t : U64) : U64 := core.num.U64.wrapping_add t 3592#u64

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

@[step] theorem obj.Tcb.affinity.spec (s : S) (t : obj.Tcb) :
    obj.Tcb.affinity st t s ⦃ v => v = L.mem s (affA t) ⦄ := by
  unfold obj.Tcb.affinity; step*; simp_all [affA]
@[step] theorem obj.Tcb.domain.spec (s : S) (t : obj.Tcb) :
    obj.Tcb.domain st t s ⦃ v => v = L.mem s (domA t) ⦄ := by
  unfold obj.Tcb.domain; step*; simp_all [domA]
@[step] theorem obj.Tcb.in_queues.spec (s : S) (t : obj.Tcb) :
    obj.Tcb.in_queues st t s ⦃ v => v = L.mem s (inqA t) ⦄ := by
  unfold obj.Tcb.in_queues; step*; simp_all [inqA]
@[step] theorem obj.Tcb.set_in_queues.spec (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_in_queues st t s v ⦃ s' => s' = L.wr s (inqA t) v ⦄ := by
  unfold obj.Tcb.set_in_queues; step*; simp_all [inqA]
@[step] theorem obj.ks_get.spec (s : S) (off : U64) :
    obj.ks_get st s off ⦃ v => v = L.mem s (core.num.U64.wrapping_add (L.ksb s) off) ⦄ := by
  unfold obj.ks_get; step*; simp_all

/-- `remote_queue_update` at most sets the current core's `IPI_PENDING`. -/
theorem smp.remote_queue_update.spec (s : S) (t : obj.Tcb) :
    smp.remote_queue_update st s t ⦃ s' => s' = s ∨ ∃ v, s' = L.wr s (L.nodeAt s (L.cpu s) layout.node.IPI_PENDING) v ⦄ := by
  unfold smp.remote_queue_update sched.cur_domain
  step*
  all_goals first | (left; simp_all; done) | (right; subst_vars; exact ⟨_, rfl⟩)

/-! ## Placement of the nodes -/

/-- The first byte of core `cpu`'s node (`node_base`). -/
def LawfulStore.nodeBase (s : S) (cpu : U64) : Nat := (L.ksb s).val + 13568 + cpu.val * 4288

/-- Core `cpu`'s node is word aligned, does not wrap, and is disjoint from
every TCB of `T`. -/
structure NodePlaced (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s : S) (cpu : U64) : Prop where
  align : L.nodeBase s cpu % 8 = 0
  fits : L.nodeBase s cpu + 4288 ≤ 2 ^ 64
  disj : ∀ t ∈ T, t.val + 2 ^ 12 ≤ L.nodeBase s cpu ∨ L.nodeBase s cpu + 4288 ≤ t.val

theorem NodePlaced.wr {T : Set U64} {s : S} {cpu a v : U64} (h : NodePlaced st T s cpu) :
    NodePlaced st T (L.wr s a v) cpu := by
  have e : L.nodeBase (L.wr s a v) cpu = L.nodeBase s cpu := by simp [LawfulStore.nodeBase]
  exact ⟨by rw [e]; exact h.align, by rw [e]; exact h.fits, by rw [e]; exact h.disj⟩

theorem nodeAt_val {T : Set U64} {s : S} {cpu off : U64} (h : NodePlaced st T s cpu) (ho : off.val < 4288) :
    (L.nodeAt s cpu off).val = L.nodeBase s cpu + off.val := by
  have := h.fits
  simp only [LawfulStore.nodeBase] at this ⊢
  have hk := (L.ksb s).hBounds
  have hc := cpu.hBounds
  simp [LawfulStore.nodeAt, core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq,
    U64.size_def, U64.numBits, UScalar.size] at hk hc ⊢
  omega

theorem nodeAt_aligned {T : Set U64} {s : S} {cpu off : U64} (h : NodePlaced st T s cpu) (ho : off.val < 4288)
    (h8 : off.val % 8 = 0) : Aligned (L.nodeAt s cpu off) := by
  have := h.align
  unfold Aligned; rw [nodeAt_val h ho]; omega

/-- A word of a placed node is not inside a TCB of `T`. -/
theorem nodeAt_out {T : Set U64} {s : S} {cpu off : U64} (h : NodePlaced st T s cpu) (ho : off.val < 4288)
    {t : U64} (ht : t ∈ T) : (L.nodeAt s cpu off).val < t.val ∨ t.val + 2 ^ 12 ≤ (L.nodeAt s cpu off).val := by
  rw [nodeAt_val h ho]; have := h.disj t ht; omega

theorem nodeAt_ne_nextA {T : Set U64} {s : S} {cpu off : U64} (h : NodePlaced st T s cpu) (ho : off.val < 4288)
    {t : U64} (ht : t ∈ T) (hta : TcbAddr t) (l : tcbqueue.Link) : L.nodeAt s cpu off ≠ nextA l t := by
  intro e; have := congrArg UScalar.val e; have := nodeAt_out h ho ht; have := nextA_inside hta l; omega

theorem nodeAt_ne_prevA {T : Set U64} {s : S} {cpu off : U64} (h : NodePlaced st T s cpu) (ho : off.val < 4288)
    {t : U64} (ht : t ∈ T) (hta : TcbAddr t) (l : tcbqueue.Link) : L.nodeAt s cpu off ≠ prevA l t := by
  intro e; have := congrArg UScalar.val e; have := nodeAt_out h ho ht; have := prevA_inside hta l; omega

theorem nodeAt_ne {T : Set U64} {s : S} {cpu o1 o2 : U64} (h : NodePlaced st T s cpu) (h1 : o1.val < 4288)
    (h2 : o2.val < 4288) (hne : o1.val ≠ o2.val) : L.nodeAt s cpu o1 ≠ L.nodeAt s cpu o2 := by
  intro e; have := congrArg UScalar.val e; rw [nodeAt_val h h1, nodeAt_val h h2] at this; omega

theorem nodeAt_ne_cpu {T : Set U64} {s : S} {c1 c2 o1 o2 : U64} (h1 : NodePlaced st T s c1)
    (h2 : NodePlaced st T s c2) (ho1 : o1.val < 4288) (ho2 : o2.val < 4288) (hne : c1 ≠ c2) :
    L.nodeAt s c1 o1 ≠ L.nodeAt s c2 o2 := by
  intro e; have := congrArg UScalar.val e; rw [nodeAt_val h1 ho1, nodeAt_val h2 ho2] at this
  have : c1.val ≠ c2.val := fun e' => hne (UScalar.eq_of_val_eq e')
  simp only [LawfulStore.nodeBase] at *; omega

/-! ## Writes that leave queues alone -/

/-- A write to a word that is no link field of a queue's members keeps the
queue related. -/
theorem QueueRel.wr_out {T : Set U64} {s : S} {l q xs} {a v : U64} (hT : TcbPlaced T)
    (h : QueueRel (L.mem s) T l q xs) (ha : Aligned a)
    (hout : ∀ y ∈ xs, a ≠ nextA l y ∧ a ≠ prevA l y) : QueueRel (L.mem (L.wr s a v)) T l q xs :=
  ⟨h.nodup, h.mem, h.head, h.last, h.seg.congr fun y hy =>
    ⟨L.mem_wr_ne ha (prevA_aligned (h.addr hT y hy) l) (fun e => (hout y hy).2 (UScalar.eq_of_val_eq e)),
     L.mem_wr_ne ha (nextA_aligned (h.addr hT y hy) l) (fun e => (hout y hy).1 (UScalar.eq_of_val_eq e))⟩⟩

theorem QueueRel.wr_node {T : Set U64} {s : S} {l q xs} {cpu off v : U64} (hT : TcbPlaced T)
    (h : QueueRel (L.mem s) T l q xs) (hP : NodePlaced st T s cpu) (ho : off.val < 4288)
    (h8 : off.val % 8 = 0) : QueueRel (L.mem (L.wr s (L.nodeAt s cpu off) v)) T l q xs :=
  h.wr_out hT (nodeAt_aligned hP ho h8) fun y hy =>
    ⟨nodeAt_ne_nextA hP ho (h.mem y hy) (h.addr hT y hy) l, nodeAt_ne_prevA hP ho (h.mem y hy) (h.addr hT y hy) l⟩

theorem inqA_val {t : U64} (h : TcbAddr t) : (inqA t).val = t.val + 3592 := by
  have := h.fits
  simp [inqA, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega

theorem inqA_aligned {t : U64} (h : TcbAddr t) : Aligned (inqA t) := by
  have := h.align; unfold Aligned; rw [inqA_val h]; omega

theorem inqA_ne_nextA {t y : U64} (ht : TcbAddr t) (hy : TcbAddr y) (l) : inqA t ≠ nextA l y := by
  intro e; have := congrArg UScalar.val e; rw [inqA_val ht, nextA_val hy] at this
  have := ht.align; have := hy.align
  cases l <;> simp [nextOff] at this <;> omega

theorem inqA_ne_prevA {t y : U64} (ht : TcbAddr t) (hy : TcbAddr y) (l) : inqA t ≠ prevA l y := by
  intro e; have := congrArg UScalar.val e; rw [inqA_val ht, prevA_val hy] at this
  have := ht.align; have := hy.align
  cases l <;> simp [prevOff] at this <;> omega

theorem QueueRel.wr_inq {T : Set U64} {s : S} {l q xs} {t v : U64} (hT : TcbPlaced T)
    (h : QueueRel (L.mem s) T l q xs) (ht : TcbAddr t) : QueueRel (L.mem (L.wr s (inqA t) v)) T l q xs :=
  h.wr_out hT (inqA_aligned ht) fun y hy =>
    ⟨inqA_ne_nextA ht (h.addr hT y hy) l, inqA_ne_prevA ht (h.addr hT y hy) l⟩

theorem inqA_ne_nodeAt {T : Set U64} {s : S} {cpu off t : U64} (hP : NodePlaced st T s cpu) (ho : off.val < 4288)
    (ht : t ∈ T) (hta : TcbAddr t) : inqA t ≠ L.nodeAt s cpu off := by
  intro e; have := congrArg UScalar.val e; rw [inqA_val hta] at this
  have := nodeAt_out hP ho ht; omega

end

/-! ## Offsets in the node -/

/-- The word with value `n` (mod `2 ^ 64`). -/
def w64 (n : Nat) : U64 := ⟨BitVec.ofNat 64 n⟩

@[simp] theorem w64_val (n : Nat) : (w64 n).val = n % 2 ^ 64 := by
  show (BitVec.ofNat 64 n).toNat = _
  simp

theorem eq_w64 {x : U64} {n : Nat} (h : x.val = n) (hn : n < 2 ^ 64) : x = w64 n :=
  UScalar.eq_of_val_eq (by simp [h]; omega)

/-- `rq_head_off`, with one domain: the head word of the ready queue of `p`. -/
def rqOff (p : U64) : U64 := w64 (168 + 16 * p.val)
def rqTailOff (p : U64) : U64 := w64 (176 + 16 * p.val)
def l1Off : U64 := w64 128
/-- The L2 bitmap word of priority group `g` (priorities `64 g .. 64 g + 63`). -/
def l2Off (g : Nat) : U64 := w64 (136 + 8 * (3 - g))

theorem one_bit (j : Nat) : (1#u64).bv.getLsbD j = decide (j = 0) := by
  have : (1#u64).bv = BitVec.ofNat _ 1 := rfl
  rw [this, BitVec.getLsbD_ofNat]
  rcases j with _ | j <;> simp [Nat.testBit_succ]

theorem bit_or_shl (x y z k : U64) (hk : k.val < 64) (hy : y.bv = (1#u64).bv <<< k.val)
    (hz : z.bv = x.bv ||| y.bv) (i : Nat) :
    z.bv.getLsbD i = (x.bv.getLsbD i || decide (i = k.val)) := by
  rw [hz, BitVec.getLsbD_or]
  simp only [hy, BitVec.getLsbD_shiftLeft, one_bit, UScalarTy.U64_numBits_eq]
  congr 1
  by_cases h : i = k.val <;> simp [h] <;> omega

theorem bit_and_not_shl (x y z k : U64) (hk : k.val < 64) (hy : y.bv = (1#u64).bv <<< k.val)
    (hz : z.bv = x.bv &&& ~~~y.bv) (i : Nat) :
    z.bv.getLsbD i = (x.bv.getLsbD i && !decide (i = k.val)) := by
  rw [hz, BitVec.getLsbD_and, BitVec.getLsbD_not]
  simp only [hy, BitVec.getLsbD_shiftLeft, one_bit, UScalarTy.U64_numBits_eq]
  by_cases hi : i < 64
  · by_cases h : i = k.val <;> simp [h, hi] <;> omega
  · have : x.bv.getLsbD i = false := BitVec.getLsbD_of_ge _ _ (by simpa using hi)
    simp [this]

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

@[step] theorem sched.rq_head_off.spec (dom p : U64) (hp : p.val < 256) :
    sched.rq_head_off dom p ⦃ off => off = rqOff p ∧ core.num.U64.wrapping_add off 8#u64 = rqTailOff p ⦄ := by
  unfold sched.rq_head_off sched.rq_index
  simp only [layout.NUM_DOMAINS, fl4_abi.config.NUM_DOMAINS]
  rw [ite_cond_eq_false _ _ (by simp [gt_iff_val])]
  step*
  subst_vars
  constructor <;> apply eq_w64 <;>
    simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits] <;>
    omega

@[step] theorem sched.q_get.spec (s : S) (cpu off : U64) :
    sched.q_get st s cpu off ⦃ q => q = ⟨L.mem s (L.nodeAt s cpu off),
      L.mem s (L.nodeAt s cpu (core.num.U64.wrapping_add off 8#u64))⟩ ⦄ := by
  unfold sched.q_get; step*; simp_all

@[step] theorem sched.q_set.spec (s : S) (cpu off : U64) (q : tcbqueue.Queue) :
    sched.q_set st s cpu off q ⦃ s' => s' = L.wr (L.wr s (L.nodeAt s cpu off) q.head)
      (L.nodeAt s cpu (core.num.U64.wrapping_add off 8#u64)) q.end ⦄ := by
  unfold sched.q_set; step*; simp_all

@[step] theorem sched.queued.spec (s : S) (t : obj.Tcb) :
    sched.queued st s t ⦃ b => b = decide ((L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64) ⦄ := by
  unfold sched.queued; step*

@[step] theorem sched.set_flag.spec (s : S) (t : obj.Tcb) (f : U64) (v : Bool) :
    sched.set_flag st s t f v ⦃ s' => s' = L.wr s (inqA t)
      (if v then L.mem s (inqA t) ||| f else L.mem s (inqA t) &&& ~~~f) ⦄ := by
  unfold sched.set_flag; step* <;> (subst_vars; congr 1; apply UScalar.eq_of_val_eq; simp_all)

@[step] theorem l1_off_zero : sched.l1_off 0#u64 ⦃ o => o = l1Off ⦄ := by
  unfold sched.l1_off; step*; subst_vars
  apply eq_w64 <;> simp [layout.node.L1_BITMAP, core.num.U64.wrapping_add_val_eq,
    core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]

@[step] theorem l2_off_zero (inv : U64) (h : inv.val < 4) :
    sched.l2_off 0#u64 inv ⦃ o => o = w64 (136 + 8 * inv.val) ⦄ := by
  unfold sched.l2_off; step*; subst_vars
  apply eq_w64 _ (by omega)
  simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]
  omega

/-- The group and bit of priority `p`, as the bitmap code computes them. -/
theorem prio_bits {p : U64} (hp : p.val < 256) :
    p.val >>> 6 = p.val / 64 ∧ (p.val >>> 6) &&& 3 = p.val / 64 ∧ (p.val >>> 6) &&& 63 = p.val / 64 ∧
      p.val &&& 63 = p.val % 64 := by
  have h1 : p.val >>> 6 = p.val / 64 := by rw [Nat.shiftRight_eq_div_pow]
  have h3 := Nat.and_two_pow_sub_one_eq_mod (p.val / 64) 2
  have h63 := Nat.and_two_pow_sub_one_eq_mod (p.val / 64) 6
  have hp63 := Nat.and_two_pow_sub_one_eq_mod p.val 6
  simp only [show (2 : Nat) ^ 2 - 1 = 3 from rfl, show (2 : Nat) ^ 6 - 1 = 63 from rfl] at h3 h63 hp63
  refine ⟨h1, ?_, ?_, hp63⟩ <;> rw [h1] <;> [rw [h3]; rw [h63]] <;> omega

/-- `add_to_bitmap` sets the group bit in L1 and the priority bit in the
group's L2 word. -/
theorem sched.add_to_bitmap.spec (s : S) (cpu dom p : U64) (hp : p.val < 256) :
    sched.add_to_bitmap st s cpu dom p ⦃ s' => ∃ v1 v2,
      s' = L.wr (L.wr s (L.nodeAt s cpu l1Off) v1) (L.nodeAt s cpu (l2Off (p.val / 64))) v2 ∧
      (∀ i, v1.bv.getLsbD i = ((L.mem s (L.nodeAt s cpu l1Off)).bv.getLsbD i || decide (i = p.val / 64))) ∧
      (∀ i, v2.bv.getLsbD i = ((L.mem (L.wr s (L.nodeAt s cpu l1Off) v1)
        (L.nodeAt s cpu (l2Off (p.val / 64)))).bv.getLsbD i || decide (i = p.val % 64))) ⦄ := by
  obtain ⟨b1, b2, b3, b4⟩ := prio_bits hp
  unfold sched.add_to_bitmap sched.bitmap_dom
  simp only [layout.NUM_DOMAINS, fl4_abi.config.NUM_DOMAINS]
  rw [ite_cond_eq_false _ _ (by simp [gt_iff_val])]
  step*
  have hi : i.val = p.val / 64 := by rw [i_post, UScalar.val_and, l1_post]; exact b2
  have hi2 : i2.val = p.val / 64 := by rw [i2_post, UScalar.val_and, l1_post]; exact b3
  have hi6 : i6.val = p.val % 64 := by rw [i6_post, UScalar.val_and]; exact b4
  have h5 : i5 = l2Off (p.val / 64) := by rw [i5_post, l2Off, inv_post, hi]
  subst i1_post v1_post s1_post v2_post s'_post
  refine ⟨i4, i8, by rw [nodeAt_wr, h5], fun j => ?_, fun j => ?_⟩
  · rw [bit_or_shl _ i3 i4 i2 (by omega) i3_post1 i4_post1, hi2]
  · rw [bit_or_shl _ i7 i8 i6 (by omega) i7_post1 i8_post1, hi6, nodeAt_wr, h5]

/-- `remove_from_bitmap` clears the priority bit, and the group bit when the
group's word becomes 0. -/
theorem sched.remove_from_bitmap.spec (s : S) (cpu dom p : U64) (hp : p.val < 256) :
    sched.remove_from_bitmap st s cpu dom p ⦃ s' => ∃ v2,
      (∀ i, v2.bv.getLsbD i = ((L.mem s (L.nodeAt s cpu (l2Off (p.val / 64)))).bv.getLsbD i &&
        !decide (i = p.val % 64))) ∧
      (if v2 = 0#u64 then ∃ v1,
          s' = L.wr (L.wr s (L.nodeAt s cpu (l2Off (p.val / 64))) v2) (L.nodeAt s cpu l1Off) v1 ∧
          ∀ i, v1.bv.getLsbD i = ((L.mem (L.wr s (L.nodeAt s cpu (l2Off (p.val / 64))) v2)
            (L.nodeAt s cpu l1Off)).bv.getLsbD i && !decide (i = p.val / 64))
        else s' = L.wr s (L.nodeAt s cpu (l2Off (p.val / 64))) v2) ⦄ := by
  obtain ⟨b1, b2, b3, b4⟩ := prio_bits hp
  unfold sched.remove_from_bitmap sched.bitmap_dom
  simp only [layout.NUM_DOMAINS, fl4_abi.config.NUM_DOMAINS]
  rw [ite_cond_eq_false _ _ (by simp)]
  step*
  all_goals
    have hi : i.val = p.val / 64 := by rw [i_post, UScalar.val_and, l1_post]; exact b2
    have hi3 : i3.val = p.val % 64 := by rw [i3_post, UScalar.val_and]; exact b4
    have h1 : i1 = l2Off (p.val / 64) := by rw [i1_post, l2Off, inv_post, hi]
    have hv2 : ∀ j, v2.bv.getLsbD j = ((L.mem s (L.nodeAt s cpu (l2Off (p.val / 64)))).bv.getLsbD j &&
        !decide (j = p.val % 64)) := by
      intro j; rw [bit_and_not_shl i2 i4 v2 i3 (by omega) i4_post1 (by simp only [v2_post1, i5_post, UScalar.bv_not]), hi3,
        i2_post, h1]
    refine ⟨v2, hv2, ?_⟩
  · rw [ite_cond_eq_true _ _ (eq_true ‹v2 = 0#u64›)]
    subst s'_post s1_post i6_post
    rw [← h1]
    refine ⟨i10, by simp only [nodeAt_wr], fun j => ?_⟩
    have hi7 : i7.val = p.val / 64 := by rw [i7_post, UScalar.val_and, l1_post]; exact b3
    rw [bit_and_not_shl v1 i8 i10 i7 (by omega) i8_post1 (by simp only [i10_post1, i9_post, UScalar.bv_not]), hi7,
      v1_post, nodeAt_wr]
  · rw [ite_cond_eq_false _ _ (eq_false ‹¬v2 = 0#u64›)]
    subst s1_post; rw [h1]

end

/-! ## Offsets are words of the node -/

theorem rqOff_val {p : U64} (hp : p.val < 256) : (rqOff p).val = 168 + 16 * p.val := by
  simp [rqOff]; omega
theorem rqTailOff_val {p : U64} (hp : p.val < 256) : (rqTailOff p).val = 176 + 16 * p.val := by
  simp [rqTailOff]; omega
theorem l1Off_val : l1Off.val = 128 := by simp [l1Off]
theorem l2Off_val {g : Nat} (hg : g < 4) : (l2Off g).val = 136 + 8 * (3 - g) := by
  simp [l2Off]; omega
theorem ipi_val : layout.node.IPI_PENDING.val = 120 := by simp [layout.node.IPI_PENDING]

theorem ne_zero_iff_bit (w : U64) : w ≠ 0#u64 ↔ ∃ i < 64, w.bv.getLsbD i = true := by
  have hv : w ≠ 0#u64 ↔ w.val ≠ 0 :=
    ⟨fun h e => h (UScalar.eq_of_val_eq (by simpa using e)), fun h e => h (by rw [e]; rfl)⟩
  rw [hv]
  have hb : ∀ i, w.bv.getLsbD i = w.val.testBit i := fun i => rfl
  simp only [hb]
  have hw : w.val < 2 ^ 64 := by have := w.hBounds; simpa using this
  constructor
  · intro h
    obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero h
    refine ⟨i, ?_, hi⟩
    by_contra hc
    have : w.val < 2 ^ i := lt_of_lt_of_le hw (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.testBit_eq_false_of_lt this] at hi
    exact Bool.false_ne_true hi
  · rintro ⟨i, _, hi⟩ h0
    rw [h0] at hi; simp at hi

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64}

/-! ## Reading node words after writes -/

theorem rd_node_wr_node {s : S} {c o1 o2 v : U64} (hN : NodePlaced st T s c) (h1 : o1.val < 4288)
    (h2 : o2.val < 4288) (h18 : o1.val % 8 = 0) (h28 : o2.val % 8 = 0) :
    L.mem (L.wr s (L.nodeAt s c o1) v) (L.nodeAt s c o2) = if o1.val = o2.val then v else L.mem s (L.nodeAt s c o2) := by
  rw [L.mem_wr_val (nodeAt_aligned hN h1 h18) (nodeAt_aligned hN h2 h28), nodeAt_val hN h1, nodeAt_val hN h2]
  by_cases h : o1.val = o2.val
  · simp [h]
  · simp [h]

theorem rd_node_wr_node_cpu {s : S} {c c' o1 o2 v : U64} (hN : NodePlaced st T s c) (hN' : NodePlaced st T s c')
    (h1 : o1.val < 4288) (h2 : o2.val < 4288) (h18 : o1.val % 8 = 0) (h28 : o2.val % 8 = 0) (hc : c' ≠ c) :
    L.mem (L.wr s (L.nodeAt s c' o1) v) (L.nodeAt s c o2) = L.mem s (L.nodeAt s c o2) :=
  L.mem_wr_ne (nodeAt_aligned hN' h1 h18) (nodeAt_aligned hN h2 h28)
    (fun e => nodeAt_ne_cpu hN' hN h1 h2 hc (UScalar.eq_of_val_eq e))

theorem rd_node_wr_inq {s : S} {c o t v : U64} (hN : NodePlaced st T s c) (ho : o.val < 4288)
    (h8 : o.val % 8 = 0) (ht : t ∈ T) (hta : TcbAddr t) :
    L.mem (L.wr s (inqA t) v) (L.nodeAt s c o) = L.mem s (L.nodeAt s c o) :=
  L.mem_wr_ne (inqA_aligned hta) (nodeAt_aligned hN ho h8)
    (fun e => inqA_ne_nodeAt hN ho ht hta (UScalar.eq_of_val_eq e))

theorem rd_node_framed {s s' : S} {c o : U64} {l W} (hN : NodePlaced st T s c) (ho : o.val < 4288)
    (h8 : o.val % 8 = 0) (hW : ∀ w ∈ W, w ∈ T) (hT : TcbPlaced T) (hf : Framed st l W s s') :
    L.mem s' (L.nodeAt s' c o) = L.mem s (L.nodeAt s c o) := by
  have e : L.nodeAt s' c o = L.nodeAt s c o := by simp [LawfulStore.nodeAt, hf.1]
  rw [e]
  refine hf.2.2 _ (nodeAt_aligned hN ho h8) fun w hw => ⟨?_, ?_⟩
  · exact nodeAt_ne_nextA hN ho (hW w hw) (hT w (hW w hw)) l
  · exact nodeAt_ne_prevA hN ho (hW w hw) (hT w (hW w hw)) l

theorem NodePlaced.framed {s s' : S} {c : U64} {l W} (hN : NodePlaced st T s c) (hf : Framed st l W s s') :
    NodePlaced st T s' c := by
  have e : L.nodeBase s' c = L.nodeBase s c := by simp [LawfulStore.nodeBase, hf.1]
  exact ⟨by rw [e]; exact hN.align, by rw [e]; exact hN.fits, by rw [e]; exact hN.disj⟩

/-! ## Ready queues and the bitmap -/

def LawfulStore.rqQ (s : S) (cpu p : U64) : tcbqueue.Queue :=
  ⟨L.mem s (L.nodeAt s cpu (rqOff p)), L.mem s (L.nodeAt s cpu (rqTailOff p))⟩
def LawfulStore.l1W (s : S) (cpu : U64) : U64 := L.mem s (L.nodeAt s cpu l1Off)
def LawfulStore.l2W (s : S) (cpu : U64) (g : Nat) : U64 := L.mem s (L.nodeAt s cpu (l2Off g))

/-- The ready queues of core `cpu` (one domain) hold the lists `Q p` and are
pairwise disjoint. -/
structure ReadyRel (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s : S) (cpu : U64)
    (Q : U64 → List U64) : Prop where
  rel : ∀ p : U64, p.val < 256 → QueueRel (L.mem s) T .Sched (L.rqQ s cpu p) (Q p)
  disj : ∀ p p' : U64, p.val < 256 → p'.val < 256 → p ≠ p' → ∀ x ∈ Q p, x ∉ Q p'

/-- The two-level bitmap of core `cpu` records the predicate `NE` on
priorities: bit `p % 64` of the L2 word of group `p / 64` is set iff `NE p`,
and L1 bit `i` is set iff `i < 4` and group `i`'s L2 word is non-zero. -/
structure BitmapOK (st : machine.Store S) [L : LawfulStore st] (s : S) (cpu : U64) (NE : U64 → Prop) : Prop where
  l2 : ∀ p : U64, p.val < 256 → ((L.l2W s cpu (p.val / 64)).bv.getLsbD (p.val % 64) = true ↔ NE p)
  l1 : ∀ i < 64, ((L.l1W s cpu).bv.getLsbD i = true ↔ i < 4 ∧ L.l2W s cpu i ≠ 0#u64)

/-- seL4's `valid_queues` / `bitmapQ` for one core: the ready queues hold
`Q`, are disjoint, and the bitmap says which are non-empty. -/
def ReadyQueues (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s : S) (cpu : U64)
    (Q : U64 → List U64) : Prop :=
  ReadyRel st T s cpu Q ∧ BitmapOK st s cpu (fun p => Q p ≠ [])

/-- The bitmap only depends on its five words. -/
theorem BitmapOK.agree {s s' : S} {c : U64} {NE} (h : BitmapOK st s c NE)
    (h1 : L.l1W s' c = L.l1W s c) (h2 : ∀ g < 4, L.l2W s' c g = L.l2W s c g) : BitmapOK st s' c NE := by
  refine ⟨fun p hp => ?_, fun i hi => ?_⟩
  · rw [h2 _ (by omega)]; exact h.l2 p hp
  · rw [h1, h.l1 i hi]
    constructor
    · rintro ⟨hi4, hne⟩; exact ⟨hi4, by rwa [h2 i hi4]⟩
    · rintro ⟨hi4, hne⟩; exact ⟨hi4, by rwa [← h2 i hi4]⟩

theorem BitmapOK.congr {s : S} {c : U64} {NE NE'} (h : BitmapOK st s c NE)
    (he : ∀ p : U64, p.val < 256 → (NE p ↔ NE' p)) : BitmapOK st s c NE' :=
  ⟨fun p hp => (h.l2 p hp).trans (he p hp), h.l1⟩

/-- Replacing queue `p` by `xs`, everything else unchanged. -/
theorem ReadyRel.update {s s' : S} {c p : U64} {Q xs} (hT : TcbPlaced T) (hp : p.val < 256)
    (h : ReadyRel st T s c Q)
    (hq : ∀ p' : U64, p'.val < 256 → p' ≠ p → L.rqQ s' c p' = L.rqQ s c p')
    (hl : ∀ p' : U64, p'.val < 256 → p' ≠ p → ∀ y ∈ Q p',
      L.mem s' (nextA .Sched y) = L.mem s (nextA .Sched y) ∧ L.mem s' (prevA .Sched y) = L.mem s (prevA .Sched y))
    (hx : QueueRel (L.mem s') T .Sched (L.rqQ s' c p) xs)
    (hd : ∀ p' : U64, p'.val < 256 → p' ≠ p → ∀ x ∈ xs, x ∉ Q p') :
    ReadyRel st T s' c (Function.update Q p xs) := by
  refine ⟨fun p' hp' => ?_, fun p1 p2 hp1 hp2 hne x hx1 hx2 => ?_⟩
  · by_cases e : p' = p
    · subst e; simpa using hx
    · rw [Function.update_of_ne e, hq p' hp' e]
      have r := h.rel p' hp'
      exact ⟨r.nodup, r.mem, r.head, r.last, r.seg.congr fun y hy =>
        ⟨(hl p' hp' e y hy).2, (hl p' hp' e y hy).1⟩⟩
  · by_cases e1 : p1 = p
    · subst e1
      rw [Function.update_self] at hx1
      rw [Function.update_of_ne (Ne.symm hne)] at hx2
      exact hd p2 hp2 (Ne.symm hne) x hx1 hx2
    · by_cases e2 : p2 = p
      · subst e2
        rw [Function.update_self] at hx2
        rw [Function.update_of_ne e1] at hx1
        exact hd p1 hp1 e1 x hx2 hx1
      · rw [Function.update_of_ne e1] at hx1
        rw [Function.update_of_ne e2] at hx2
        exact h.disj p1 p2 hp1 hp2 hne x hx1 hx2

theorem ReadyRel.agree {s s' : S} {c : U64} {Q} (h : ReadyRel st T s c Q)
    (hq : ∀ p' : U64, p'.val < 256 → L.rqQ s' c p' = L.rqQ s c p')
    (hl : ∀ p' : U64, p'.val < 256 → ∀ y ∈ Q p',
      L.mem s' (nextA .Sched y) = L.mem s (nextA .Sched y) ∧ L.mem s' (prevA .Sched y) = L.mem s (prevA .Sched y)) :
    ReadyRel st T s' c Q := by
  refine ⟨fun p' hp' => ?_, h.disj⟩
  rw [hq p' hp']
  have r := h.rel p' hp'
  exact ⟨r.nodup, r.mem, r.head, r.last, r.seg.congr fun y hy => ⟨(hl p' hp' y hy).2, (hl p' hp' y hy).1⟩⟩

/-! Views after a node write. -/

theorem l1W_wr_node {s : S} {c o v : U64} (hN : NodePlaced st T s c) (ho : o.val < 4288) (h8 : o.val % 8 = 0) :
    L.l1W (L.wr s (L.nodeAt s c o) v) c = if o.val = 128 then v else L.l1W s c := by
  unfold LawfulStore.l1W; rw [nodeAt_wr, rd_node_wr_node hN ho (by simp [l1Off_val]) h8 (by simp [l1Off_val]),
    l1Off_val]

theorem l2W_wr_node {s : S} {c o v : U64} {g : Nat} (hN : NodePlaced st T s c) (ho : o.val < 4288)
    (h8 : o.val % 8 = 0) (hg : g < 4) :
    L.l2W (L.wr s (L.nodeAt s c o) v) c g = if o.val = 136 + 8 * (3 - g) then v else L.l2W s c g := by
  unfold LawfulStore.l2W; rw [nodeAt_wr, rd_node_wr_node hN ho (by rw [l2Off_val hg]; omega) h8
    (by rw [l2Off_val hg]; omega), l2Off_val hg]

theorem rqQ_wr_node {s : S} {c o v p : U64} (hN : NodePlaced st T s c) (ho : o.val < 4288)
    (h8 : o.val % 8 = 0) (hp : p.val < 256) :
    L.rqQ (L.wr s (L.nodeAt s c o) v) c p =
      ⟨if o.val = 168 + 16 * p.val then v else (L.rqQ s c p).head,
       if o.val = 176 + 16 * p.val then v else (L.rqQ s c p).end⟩ := by
  unfold LawfulStore.rqQ; simp only [nodeAt_wr]
  rw [rd_node_wr_node hN ho (by rw [rqOff_val hp]; omega) h8 (by rw [rqOff_val hp]; omega),
    rd_node_wr_node hN ho (by rw [rqTailOff_val hp]; omega) h8 (by rw [rqTailOff_val hp]; omega),
    rqOff_val hp, rqTailOff_val hp]

/-- Setting the bits of priority `p`. -/
theorem BitmapOK.add {s : S} {c p v1 v2 : U64} {NE : U64 → Prop} (hN : NodePlaced st T s c)
    (hp : p.val < 256) (h : BitmapOK st s c NE)
    (hv1 : ∀ i, v1.bv.getLsbD i = ((L.l1W s c).bv.getLsbD i || decide (i = p.val / 64)))
    (hv2 : ∀ i, v2.bv.getLsbD i = ((L.l2W s c (p.val / 64)).bv.getLsbD i || decide (i = p.val % 64))) :
    BitmapOK st (L.wr (L.wr s (L.nodeAt s c l1Off) v1) (L.nodeAt s c (l2Off (p.val / 64))) v2) c
      (fun p' => p' = p ∨ NE p') := by
  have hg : p.val / 64 < 4 := by omega
  have hN1 : NodePlaced st T (L.wr s (L.nodeAt s c l1Off) v1) c := hN.wr
  have e2 : ∀ g < 4, L.l2W (L.wr (L.wr s (L.nodeAt s c l1Off) v1) (L.nodeAt s c (l2Off (p.val / 64))) v2) c g =
      if g = p.val / 64 then v2 else L.l2W s c g := by
    intro g hg'
    have := l2W_wr_node (v := v2) (o := l2Off (p.val / 64)) hN1 (by rw [l2Off_val hg]; omega)
      (by rw [l2Off_val hg]; omega) hg'
    rw [show L.nodeAt (L.wr s (L.nodeAt s c l1Off) v1) c (l2Off (p.val / 64)) =
      L.nodeAt s c (l2Off (p.val / 64)) by simp] at this
    rw [this, l2Off_val hg, l2W_wr_node hN (by simp [l1Off_val]) (by simp [l1Off_val]) hg', l1Off_val]
    by_cases e : g = p.val / 64
    · simp [e]
    · have h1 : ¬ (3 - p.val / 64 = 3 - g) := by omega
      have h2 : ¬ (136 + 8 * (3 - g) = 128) := by omega
      simp [e, h1, h2]
  have e1 : L.l1W (L.wr (L.wr s (L.nodeAt s c l1Off) v1) (L.nodeAt s c (l2Off (p.val / 64))) v2) c = v1 := by
    have := l1W_wr_node (v := v2) (o := l2Off (p.val / 64)) hN1 (by rw [l2Off_val hg]; omega)
      (by rw [l2Off_val hg]; omega)
    rw [show L.nodeAt (L.wr s (L.nodeAt s c l1Off) v1) c (l2Off (p.val / 64)) =
      L.nodeAt s c (l2Off (p.val / 64)) by simp] at this
    rw [this, l2Off_val hg, l1W_wr_node hN (by simp [l1Off_val]) (by simp [l1Off_val]), l1Off_val]
    simp; omega
  refine ⟨fun p' hp' => ?_, fun i hi => ?_⟩
  · rw [e2 _ (by omega)]
    by_cases e : p'.val / 64 = p.val / 64
    · rw [if_pos e, hv2, ← e, Bool.or_eq_true, h.l2 p' hp']
      constructor
      · rintro (h' | h')
        · exact Or.inr h'
        · left; apply UScalar.eq_of_val_eq; simp at h'; omega
      · rintro (rfl | h')
        · right; simp
        · exact Or.inl h'
    · rw [if_neg e, h.l2 p' hp']
      constructor
      · exact Or.inr
      · rintro (rfl | h')
        · exact absurd rfl e
        · exact h'
  · rw [e1, hv1, Bool.or_eq_true]
    by_cases e : i = p.val / 64
    · subst e
      simp only [decide_true, or_true, true_iff]
      refine ⟨hg, ?_⟩
      rw [e2 _ hg, if_pos rfl, ne_zero_iff_bit]
      exact ⟨p.val % 64, by omega, by rw [hv2]; simp⟩
    · simp only [e, decide_false, Bool.false_eq_true, or_false]
      rw [h.l1 i hi]
      constructor
      · rintro ⟨hi4, hne⟩; exact ⟨hi4, by rwa [e2 i hi4, if_neg e]⟩
      · rintro ⟨hi4, hne⟩; exact ⟨hi4, by rwa [e2 i hi4, if_neg e] at hne⟩
/-- Clearing the bit of priority `p` (and the group bit if the group's word
becomes 0), for a priority whose bit was set. -/
theorem BitmapOK.remove {s s' : S} {c p v2 : U64} {NE : U64 → Prop} (hN : NodePlaced st T s c)
    (hp : p.val < 256) (h : BitmapOK st s c NE) (hNE : NE p)
    (hv2 : ∀ i, v2.bv.getLsbD i = ((L.l2W s c (p.val / 64)).bv.getLsbD i && !decide (i = p.val % 64)))
    (hs : if v2 = 0#u64 then ∃ v1,
          s' = L.wr (L.wr s (L.nodeAt s c (l2Off (p.val / 64))) v2) (L.nodeAt s c l1Off) v1 ∧
          ∀ i, v1.bv.getLsbD i = ((L.mem (L.wr s (L.nodeAt s c (l2Off (p.val / 64))) v2)
            (L.nodeAt s c l1Off)).bv.getLsbD i && !decide (i = p.val / 64))
        else s' = L.wr s (L.nodeAt s c (l2Off (p.val / 64))) v2) :
    BitmapOK st s' c (fun p' => p' ≠ p ∧ NE p') := by
  have hg : p.val / 64 < 4 := by omega
  set A2 := L.nodeAt s c (l2Off (p.val / 64))
  have hN2 : NodePlaced st T (L.wr s A2 v2) c := hN.wr
  have e2 : ∀ g < 4, L.l2W (L.wr s A2 v2) c g = if g = p.val / 64 then v2 else L.l2W s c g := by
    intro g hg'
    rw [l2W_wr_node hN (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega) hg', l2Off_val hg]
    by_cases e : g = p.val / 64
    · simp [e]
    · have h1 : ¬ (3 - p.val / 64 = 3 - g) := by omega
      simp [e, h1]
  have e1 : L.l1W (L.wr s A2 v2) c = L.l1W s c := by
    rw [l1W_wr_node hN (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega), l2Off_val hg]
    simp; omega
  -- The L2 clause, for the state after the L2 write.
  have hl2 : ∀ p' : U64, p'.val < 256 →
      ((L.l2W (L.wr s A2 v2) c (p'.val / 64)).bv.getLsbD (p'.val % 64) = true ↔ p' ≠ p ∧ NE p') := by
    intro p' hp'
    rw [e2 _ (by omega)]
    by_cases e : p'.val / 64 = p.val / 64
    · rw [if_pos e, hv2, ← e, Bool.and_eq_true, h.l2 p' hp']
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨fun e' => ?_, h1⟩
        subst e'; simp at h2
      · rintro ⟨h1, h2⟩
        refine ⟨h2, ?_⟩
        have : p'.val ≠ p.val := fun e' => h1 (UScalar.eq_of_val_eq e')
        simp; omega
    · rw [if_neg e, h.l2 p' hp']
      constructor
      · intro h'; exact ⟨fun e' => e (by rw [e']), h'⟩
      · exact fun h' => h'.2
  have hbit : (L.l2W s c (p.val / 64)).bv.getLsbD (p.val % 64) = true := (h.l2 p hp).2 hNE
  by_cases hz : v2 = 0#u64
  · rw [if_pos hz] at hs
    obtain ⟨v1, rfl, hv1⟩ := hs
    have hN3 := hN2
    have e2' : ∀ g < 4, L.l2W (L.wr (L.wr s A2 v2) (L.nodeAt s c l1Off) v1) c g = L.l2W (L.wr s A2 v2) c g := by
      intro g hg'
      have := l2W_wr_node (v := v1) (o := l1Off) hN2 (by simp [l1Off_val]) (by simp [l1Off_val]) hg'
      rw [show L.nodeAt (L.wr s A2 v2) c l1Off = L.nodeAt s c l1Off by simp] at this
      rw [this, l1Off_val]; simp; omega
    have e1' : L.l1W (L.wr (L.wr s A2 v2) (L.nodeAt s c l1Off) v1) c = v1 := by
      have := l1W_wr_node (v := v1) (o := l1Off) hN2 (by simp [l1Off_val]) (by simp [l1Off_val])
      rw [show L.nodeAt (L.wr s A2 v2) c l1Off = L.nodeAt s c l1Off by simp] at this
      rw [this, l1Off_val]; simp
    refine ⟨fun p' hp' => by rw [e2' _ (by omega)]; exact hl2 p' hp', fun i hi => ?_⟩
    rw [e1', hv1, Bool.and_eq_true]
    have hr : L.mem (L.wr s A2 v2) (L.nodeAt s c l1Off) = L.l1W (L.wr s A2 v2) c := by
      simp [LawfulStore.l1W]
    rw [hr, e1, h.l1 i hi]
    by_cases e : i = p.val / 64
    · subst e
      simp only [decide_true, Bool.not_true, Bool.false_eq_true, and_false, false_iff, not_and]
      intro _ hne; apply hne; rw [e2' _ hg, e2 _ hg, if_pos rfl, hz]
    · simp only [e, decide_false, Bool.not_false, and_true]
      constructor
      · rintro ⟨hi4, hne⟩; exact ⟨hi4, by rwa [e2' i hi4, e2 i hi4, if_neg e]⟩
      · rintro ⟨hi4, hne⟩; exact ⟨hi4, by rwa [e2' i hi4, e2 i hi4, if_neg e] at hne⟩
  · rw [if_neg hz] at hs
    subst hs
    refine ⟨hl2, fun i hi => ?_⟩
    rw [e1, h.l1 i hi]
    by_cases e : i = p.val / 64
    · subst e
      constructor
      · rintro ⟨hi4, -⟩; exact ⟨hi4, by rw [e2 _ hg, if_pos rfl]; exact hz⟩
      · rintro ⟨hi4, -⟩; exact ⟨hi4, (ne_zero_iff_bit _).2 ⟨p.val % 64, by omega, hbit⟩⟩
    · constructor
      · rintro ⟨hi4, hne⟩; exact ⟨hi4, by rwa [e2 i hi4, if_neg e]⟩
      · rintro ⟨hi4, hne⟩; exact ⟨hi4, by rwa [e2 i hi4, if_neg e] at hne⟩
/-! ## Writes that leave the scheduler views alone -/

/-- Core `c`'s ready queue heads, tails and bitmap words agree. -/
def ViewsEq (st : machine.Store S) [L : LawfulStore st] (s s' : S) (c : U64) : Prop :=
  (∀ p : U64, p.val < 256 → L.rqQ s' c p = L.rqQ s c p) ∧ L.l1W s' c = L.l1W s c ∧
    ∀ g < 4, L.l2W s' c g = L.l2W s c g

/-- The link fields of the TCBs of `T` agree. -/
def LinksEq (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s s' : S) : Prop :=
  ∀ y ∈ T, ∀ l, L.mem s' (nextA l y) = L.mem s (nextA l y) ∧ L.mem s' (prevA l y) = L.mem s (prevA l y)

theorem ViewsEq.refl (s : S) (c : U64) : ViewsEq st s s c := ⟨fun _ _ => rfl, rfl, fun _ _ => rfl⟩
theorem ViewsEq.trans {s₁ s₂ s₃ : S} {c} (h₁ : ViewsEq st s₁ s₂ c) (h₂ : ViewsEq st s₂ s₃ c) :
    ViewsEq st s₁ s₃ c :=
  ⟨fun p hp => (h₂.1 p hp).trans (h₁.1 p hp), h₂.2.1.trans h₁.2.1,
    fun g hg => (h₂.2.2 g hg).trans (h₁.2.2 g hg)⟩
theorem LinksEq.trans {s₁ s₂ s₃ : S} (h₁ : LinksEq st T s₁ s₂) (h₂ : LinksEq st T s₂ s₃) :
    LinksEq st T s₁ s₃ := fun y hy l =>
  ⟨(h₂ y hy l).1.trans (h₁ y hy l).1, (h₂ y hy l).2.trans (h₁ y hy l).2⟩

theorem views_wr_inq {s : S} {c t v : U64} (hN : NodePlaced st T s c) (ht : t ∈ T) (hta : TcbAddr t) :
    ViewsEq st s (L.wr s (inqA t) v) c := by
  refine ⟨fun p hp => ?_, ?_, fun g hg => ?_⟩
  · simp only [LawfulStore.rqQ, nodeAt_wr]
    rw [rd_node_wr_inq hN (by rw [rqOff_val hp]; omega) (by rw [rqOff_val hp]; omega) ht hta,
      rd_node_wr_inq hN (by rw [rqTailOff_val hp]; omega) (by rw [rqTailOff_val hp]; omega) ht hta]
  · simp only [LawfulStore.l1W, nodeAt_wr]
    rw [rd_node_wr_inq hN (by rw [l1Off_val]; omega) (by rw [l1Off_val]) ht hta]
  · simp only [LawfulStore.l2W, nodeAt_wr]
    rw [rd_node_wr_inq hN (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega) ht hta]

theorem links_wr_inq {s : S} {t v : U64} (hT : TcbPlaced T) (hta : TcbAddr t) :
    LinksEq st T s (L.wr s (inqA t) v) := fun y hy l =>
  ⟨L.mem_wr_ne (inqA_aligned hta) (nextA_aligned (hT y hy) l)
      (fun e => inqA_ne_nextA hta (hT y hy) l (UScalar.eq_of_val_eq e)),
   L.mem_wr_ne (inqA_aligned hta) (prevA_aligned (hT y hy) l)
      (fun e => inqA_ne_prevA hta (hT y hy) l (UScalar.eq_of_val_eq e))⟩

theorem links_wr_node {s : S} {c o v : U64} (hT : TcbPlaced T) (hN : NodePlaced st T s c) (ho : o.val < 4288)
    (h8 : o.val % 8 = 0) : LinksEq st T s (L.wr s (L.nodeAt s c o) v) := fun y hy l =>
  ⟨L.mem_wr_ne (nodeAt_aligned hN ho h8) (nextA_aligned (hT y hy) l)
      (fun e => nodeAt_ne_nextA hN ho hy (hT y hy) l (UScalar.eq_of_val_eq e)),
   L.mem_wr_ne (nodeAt_aligned hN ho h8) (prevA_aligned (hT y hy) l)
      (fun e => nodeAt_ne_prevA hN ho hy (hT y hy) l (UScalar.eq_of_val_eq e))⟩

/-- A write to a node word below the bitmap (offset `< 128`), on any placed
core, leaves core `c`'s views alone. -/
theorem views_wr_low {s : S} {c c' o v : U64} (hN : NodePlaced st T s c) (hN' : NodePlaced st T s c')
    (ho : o.val < 128) (h8 : o.val % 8 = 0) : ViewsEq st s (L.wr s (L.nodeAt s c' o) v) c := by
  by_cases hc : c' = c
  · subst hc
    refine ⟨fun p hp => ?_, ?_, fun g hg => ?_⟩
    · rw [rqQ_wr_node hN (by omega) h8 hp, if_neg (by omega), if_neg (by omega)]
    · rw [l1W_wr_node hN (by omega) h8, if_neg (by omega)]
    · rw [l2W_wr_node hN (by omega) h8 hg, if_neg (by omega)]
  · refine ⟨fun p hp => ?_, ?_, fun g hg => ?_⟩
    · simp only [LawfulStore.rqQ, nodeAt_wr]
      rw [rd_node_wr_node_cpu hN hN' (by omega) (by rw [rqOff_val hp]; omega) h8 (by rw [rqOff_val hp]; omega) hc,
        rd_node_wr_node_cpu hN hN' (by omega) (by rw [rqTailOff_val hp]; omega) h8
          (by rw [rqTailOff_val hp]; omega) hc]
    · simp only [LawfulStore.l1W, nodeAt_wr]
      rw [rd_node_wr_node_cpu hN hN' (by omega) (by rw [l1Off_val]; omega) h8 (by rw [l1Off_val]) hc]
    · simp only [LawfulStore.l2W, nodeAt_wr]
      rw [rd_node_wr_node_cpu hN hN' (by omega) (by rw [l2Off_val hg]; omega) h8 (by rw [l2Off_val hg]; omega) hc]

theorem views_framed {s s' : S} {c : U64} {l W} (hT : TcbPlaced T) (hN : NodePlaced st T s c)
    (hW : ∀ w ∈ W, w ∈ T) (hf : Framed st l W s s') : ViewsEq st s s' c := by
  refine ⟨fun p hp => ?_, ?_, fun g hg => ?_⟩
  · simp only [LawfulStore.rqQ]
    rw [rd_node_framed hN (by rw [rqOff_val hp]; omega) (by rw [rqOff_val hp]; omega) hW hT hf,
      rd_node_framed hN (by rw [rqTailOff_val hp]; omega) (by rw [rqTailOff_val hp]; omega) hW hT hf]
  · exact rd_node_framed hN (by rw [l1Off_val]; omega) (by rw [l1Off_val]) hW hT hf
  · exact rd_node_framed hN (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega) hW hT hf

/-- `remote_queue_update`'s write, on the current core's node. -/
theorem remote.views {s s' : S} {c : U64} (hT : TcbPlaced T) (hN : NodePlaced st T s c)
    (hN' : NodePlaced st T s (L.cpu s))
    (h : s' = s ∨ ∃ v, s' = L.wr s (L.nodeAt s (L.cpu s) layout.node.IPI_PENDING) v) :
    ViewsEq st s s' c ∧ LinksEq st T s s' ∧ NodePlaced st T s' c := by
  rcases h with rfl | ⟨v, rfl⟩
  · exact ⟨ViewsEq.refl _ _, fun _ _ _ => ⟨rfl, rfl⟩, hN⟩
  · exact ⟨views_wr_low hN hN' (by rw [ipi_val]; omega) (by rw [ipi_val]),
      links_wr_node hT hN' (by rw [ipi_val]; omega) (by rw [ipi_val]), hN.wr⟩

theorem QueueRel.links {s s' : S} {l q xs} (h : QueueRel (L.mem s) T l q xs) (he : LinksEq st T s s') :
    QueueRel (L.mem s') T l q xs :=
  ⟨h.nodup, h.mem, h.head, h.last, h.seg.congr fun y hy =>
    ⟨(he y (h.mem y hy) l).2, (he y (h.mem y hy) l).1⟩⟩

theorem ReadyRel.views {s s' : S} {c Q} (h : ReadyRel st T s c Q) (hv : ViewsEq st s s' c)
    (he : LinksEq st T s s') : ReadyRel st T s' c Q :=
  h.agree hv.1 fun p hp y hy => he y ((h.rel p hp).mem y hy) _

theorem BitmapOK.views {s s' : S} {c NE} (h : BitmapOK st s c NE) (hv : ViewsEq st s s' c) :
    BitmapOK st s' c NE := h.agree hv.2.1 hv.2.2

/-- What `q_set` of ready queue `p` changes. -/
theorem q_set_views {s : S} {c p : U64} (q : tcbqueue.Queue) (hT : TcbPlaced T) (hN : NodePlaced st T s c)
    (hp : p.val < 256) :
    let s' := L.wr (L.wr s (L.nodeAt s c (rqOff p)) q.head) (L.nodeAt s c (rqTailOff p)) q.end
    L.rqQ s' c p = q ∧ (∀ p' : U64, p'.val < 256 → p' ≠ p → L.rqQ s' c p' = L.rqQ s c p') ∧
      L.l1W s' c = L.l1W s c ∧ (∀ g < 4, L.l2W s' c g = L.l2W s c g) ∧ LinksEq st T s s' ∧
      NodePlaced st T s' c := by
  intro s'
  have hN1 : NodePlaced st T (L.wr s (L.nodeAt s c (rqOff p)) q.head) c := hN.wr
  have e : L.nodeAt s c (rqTailOff p) = L.nodeAt (L.wr s (L.nodeAt s c (rqOff p)) q.head) c (rqTailOff p) := by
    simp
  have ho : (rqOff p).val < 4288 := by rw [rqOff_val hp]; omega
  have ho8 : (rqOff p).val % 8 = 0 := by rw [rqOff_val hp]; omega
  have hto : (rqTailOff p).val < 4288 := by rw [rqTailOff_val hp]; omega
  have hto8 : (rqTailOff p).val % 8 = 0 := by rw [rqTailOff_val hp]; omega
  simp only [s']
  rw [e]
  refine ⟨?_, fun p' hp' hne => ?_, ?_, fun g hg => ?_, ?_, hN1.wr⟩
  · rw [rqQ_wr_node hN1 hto hto8 hp, rqQ_wr_node hN ho ho8 hp, rqTailOff_val hp, rqOff_val hp]
    simp
  · have : p'.val ≠ p.val := fun e' => hne (UScalar.eq_of_val_eq e')
    rw [rqQ_wr_node hN1 hto hto8 hp', rqQ_wr_node hN ho ho8 hp', rqTailOff_val hp, rqOff_val hp,
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  · rw [l1W_wr_node hN1 hto hto8, l1W_wr_node hN ho ho8, rqTailOff_val hp, rqOff_val hp,
      if_neg (by omega), if_neg (by omega)]
  · rw [l2W_wr_node hN1 hto hto8 hg, l2W_wr_node hN ho ho8 hg, rqTailOff_val hp, rqOff_val hp,
      if_neg (by omega), if_neg (by omega)]
  · exact (links_wr_node hT hN ho ho8).trans (links_wr_node hT hN1 hto hto8)

/-! ## `enqueue` -/

/-- The part of `enqueue` after the bitmap update. -/
theorem enqueue_tail (s1 : S) (t c p off : U64) (q : tcbqueue.Queue) (Q : U64 → List U64)
    (hT : TcbPlaced T) (ht : t ∈ T) (hp : p.val < 256)
    (hR : ReadyRel st T s1 c Q) (hB : BitmapOK st s1 c (fun p' => p' = p ∨ Q p' ≠ []))
    (hN : NodePlaced st T s1 c) (hN' : NodePlaced st T s1 (L.cpu s1))
    (hnot : ∀ p' : U64, p'.val < 256 → t ∉ Q p')
    (hoff : off = rqOff p) (hoff8 : core.num.U64.wrapping_add off 8#u64 = rqTailOff p)
    (hq : q = L.rqQ s1 c p) :
    (do
      let (q1, s2) ← tcbqueue.prepend st s1 tcbqueue.Link.Sched q t
      let s3 ← sched.q_set st s2 c off q1
      let s4 ← sched.set_flag st s3 t sched.Q_QUEUED true
      smp.remote_queue_update st s4 t) ⦃ s' =>
    ReadyQueues st T s' c (Function.update Q p (t :: Q p)) ⦄ := by
  have hta : TcbAddr t := hT t ht
  refine WP.spec_bind (tcbqueue.prepend.rel s1 .Sched q t (Q p) hT (hq ▸ hR.rel p hp) ht (hnot p hp)) ?_
  rintro ⟨q1, s2⟩ h2
  simp only [WP.uncurry'_pair] at h2
  obtain ⟨hr2, hf2⟩ := h2
  have hW : ∀ w ∈ t :: Q p, w ∈ T := by
    intro w hw; rcases List.mem_cons.1 hw with rfl | hw
    · exact ht
    · exact (hR.rel p hp).mem w hw
  have hN2 : NodePlaced st T s2 c := hN.framed hf2
  have hcpu2 : L.cpu s2 = L.cpu s1 := hf2.2.1
  have hN2' : NodePlaced st T s2 (L.cpu s2) := by rw [hcpu2]; exact hN'.framed hf2
  have hv12 := views_framed hT hN hW hf2
  step as ⟨s3, s3_post⟩
  step as ⟨s4, s4_post⟩
  subst hoff; rw [hoff8] at s3_post
  obtain ⟨e3p, e3o, e3l1, e3l2, hl3, hN3⟩ := q_set_views q1 hT hN2 hp
  rw [← s3_post] at e3p e3o e3l1 e3l2 hl3 hN3
  have hN3' : NodePlaced st T s3 (L.cpu s3) := by
    rw [s3_post]; simp only [LawfulStore.cpu_wr]; exact hN2'.wr.wr
  refine WP.spec_mono (smp.remote_queue_update.spec s4 t) ?_
  intro s5 h5
  have hN4 : NodePlaced st T s4 c := by rw [s4_post]; exact hN3.wr
  have hN4' : NodePlaced st T s4 (L.cpu s4) := by rw [s4_post]; simp only [LawfulStore.cpu_wr]; exact hN3'.wr
  have hv34 : ViewsEq st s3 s4 c := by rw [s4_post]; exact views_wr_inq hN3 ht hta
  have hl34 : LinksEq st T s3 s4 := by rw [s4_post]; exact links_wr_inq hT hta
  obtain ⟨hv45, hl45, -⟩ := remote.views hT hN4 hN4' h5
  have hv35 := hv34.trans hv45
  have hl35 := hl34.trans hl45
  have hrq5 : L.rqQ s5 c p = q1 := by rw [hv35.1 p hp, e3p]
  refine ⟨?_, ?_⟩
  · refine hR.update hT hp ?_ ?_ ?_ ?_
    · intro p' hp' hne
      rw [hv35.1 p' hp', e3o p' hp' hne, hv12.1 p' hp']
    · intro p' hp' hne y hy
      have hyT : y ∈ T := (hR.rel p' hp').mem y hy
      have hyW : y ∉ t :: Q p := by
        intro hy'; rcases List.mem_cons.1 hy' with rfl | hy'
        · exact hnot p' hp' hy
        · exact hR.disj p p' hp hp' (Ne.symm hne) y hy' hy
      have hWa : ∀ w ∈ t :: Q p, TcbAddr w := fun w hw => hT w (hW w hw)
      have h12n := hf2.2.2.next_eq hWa (hT y hyT) (l' := .Sched) (fun _ => hyW)
      have h12p := hf2.2.2.prev_eq hWa (hT y hyT) (l' := .Sched) (fun _ => hyW)
      exact ⟨((hl35 y hyT .Sched).1.trans (hl3 y hyT .Sched).1).trans h12n,
        ((hl35 y hyT .Sched).2.trans (hl3 y hyT .Sched).2).trans h12p⟩
    · rw [hrq5]; exact (hr2.links hl3).links hl35
    · intro p' hp' hne x hx hx'
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hnot p' hp' hx'
      · exact hR.disj p p' hp hp' (Ne.symm hne) x hx hx'
  · have hB5 : BitmapOK st s5 c (fun p' => p' = p ∨ Q p' ≠ []) := by
      refine hB.agree ?_ ?_
      · rw [hv35.2.1, e3l1, hv12.2.1]
      · intro g hg; rw [hv35.2.2 g hg, e3l2 g hg, hv12.2.2 g hg]
    refine hB5.congr fun p' _ => ?_
    by_cases e : p' = p
    · subst e; simp
    · simp [e]

/-- seL4 `tcbSchedEnqueue` keeps the ready queues of the thread's core and
their bitmap consistent: a queued thread is left alone; otherwise it is put
at the head of the queue of its priority (`prepend`), and the bitmap bits of
that priority are set. -/
theorem sched.enqueue.ready (s : S) (t : obj.Tcb) (Q : U64 → List U64) (hT : TcbPlaced T) (ht : t ∈ T)
    (hp : (L.mem s (prioA t)).val < 256)
    (hN : NodePlaced st T s (L.mem s (affA t))) (hN' : NodePlaced st T s (L.cpu s))
    (h : ReadyQueues st T s (L.mem s (affA t)) Q)
    (hq : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 → ∀ p : U64, p.val < 256 → t ∉ Q p) :
    sched.enqueue st s t ⦃ s' => ReadyQueues st T s' (L.mem s (affA t))
      (if (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64 then Q
       else Function.update Q (L.mem s (prioA t)) (t :: Q (L.mem s (prioA t)))) ⦄ := by
  have hta : TcbAddr t := hT t ht
  unfold sched.enqueue
  step*
  have hq0 : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 := by
    by_contra hc; exact ‹¬b = true› (by rw [b_post]; exact decide_eq_true hc)
  simp only [hq0, ne_eq, not_true_eq_false, if_false]
  subst cpu_post prio_post off_post
  have hqq : q = L.rqQ s (L.mem s (affA t)) (L.mem s (prioA t)) := by
    rw [q_post, off_post1]; rfl
  by_cases hb1 : b1 = true
  · rw [ite_cond_eq_true _ _ (eq_true hb1)]
    refine WP.spec_bind (sched.add_to_bitmap.spec s _ dom _ hp) ?_
    rintro s1 ⟨v1, v2, rfl, hv1, hv2⟩
    have hg : (L.mem s (prioA t)).val / 64 < 4 := by omega
    have hN1 : NodePlaced st T (L.wr s (L.nodeAt s (L.mem s (affA t)) l1Off) v1) (L.mem s (affA t)) := hN.wr
    have hA2 : L.nodeAt s (L.mem s (affA t)) (l2Off ((L.mem s (prioA t)).val / 64)) =
        L.nodeAt (L.wr s (L.nodeAt s (L.mem s (affA t)) l1Off) v1) (L.mem s (affA t))
          (l2Off ((L.mem s (prioA t)).val / 64)) := by simp
    have hrq : ∀ p' : U64, p'.val < 256 → L.rqQ (L.wr (L.wr s (L.nodeAt s (L.mem s (affA t)) l1Off) v1)
        (L.nodeAt s (L.mem s (affA t)) (l2Off ((L.mem s (prioA t)).val / 64))) v2) (L.mem s (affA t)) p' =
        L.rqQ s (L.mem s (affA t)) p' := by
      intro p' hp'
      rw [hA2, rqQ_wr_node hN1 (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega) hp',
        rqQ_wr_node hN (by rw [l1Off_val]; omega) (by rw [l1Off_val]) hp', l2Off_val hg, l1Off_val,
        if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have hlk := (links_wr_node (v := v1) hT hN (by rw [l1Off_val]; omega) (by rw [l1Off_val])).trans
      (links_wr_node (v := v2) hT hN1 (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega))
    rw [← hA2] at hlk
    have hv2' : ∀ i, v2.bv.getLsbD i = ((L.l2W s (L.mem s (affA t)) ((L.mem s (prioA t)).val / 64)).bv.getLsbD i ||
        decide (i = (L.mem s (prioA t)).val % 64)) := by
      intro i; rw [hv2]
      unfold LawfulStore.l2W
      rw [rd_node_wr_node hN (by rw [l1Off_val]; omega) (by rw [l2Off_val hg]; omega) (by rw [l1Off_val])
        (by rw [l2Off_val hg]; omega), if_neg (by rw [l1Off_val, l2Off_val hg]; omega)]
    have hempty : Q (L.mem s (prioA t)) = [] :=
      ((h.1.rel _ hp).empty_iff hT).1 (by rw [← hqq]; simpa [b1_post] using hb1)
    apply enqueue_tail _ t _ _ _ q Q hT ht hp
    · exact h.1.agree hrq fun p' hp' y hy => hlk y ((h.1.rel p' hp').mem y hy) _
    · exact BitmapOK.add hN hp h.2 hv1 hv2'
    · exact hN1.wr
    · simp only [LawfulStore.cpu_wr]; exact hN'.wr.wr
    · exact hq hq0
    · rfl
    · exact off_post1
    · rw [hrq _ hp, hqq]
  · rw [ite_cond_eq_false _ _ (eq_false hb1)]
    simp only [bind_ok]
    have hne : Q (L.mem s (prioA t)) ≠ [] := by
      rw [Ne, ← (h.1.rel _ hp).empty_iff hT, ← hqq]; simpa [b1_post] using hb1
    apply enqueue_tail _ t _ _ _ q Q hT ht hp h.1 _ hN hN' (hq hq0) rfl off_post1 hqq
    refine h.2.congr fun p' _ => ?_
    by_cases e : p' = L.mem s (prioA t)
    · subst e; simp [hne]
    · simp [e]

/-! ## `dequeue` -/

/-- A write below the ready queues (the bitmap, or any lower node word)
leaves the ready queues related. -/
theorem ReadyRel.wr_low {s : S} {c o v : U64} {Q} (hT : TcbPlaced T) (hN : NodePlaced st T s c)
    (ho : o.val < 168) (h8 : o.val % 8 = 0) (h : ReadyRel st T s c Q) :
    ReadyRel st T (L.wr s (L.nodeAt s c o) v) c Q :=
  h.agree (fun p hp => by rw [rqQ_wr_node hN (by omega) h8 hp, if_neg (by omega), if_neg (by omega)])
    fun p hp y hy => links_wr_node hT hN (by omega) h8 y ((h.rel p hp).mem y hy) _

/-- seL4 `tcbSchedDequeue` keeps the ready queues of the thread's core and
their bitmap consistent: an unqueued thread is left alone; otherwise it is
removed from the queue of its priority, and if that queue becomes empty the
bitmap bits are cleared. -/
theorem sched.dequeue.ready (s : S) (t : obj.Tcb) (Q : U64 → List U64) (hT : TcbPlaced T) (ht : t ∈ T)
    (hp : (L.mem s (prioA t)).val < 256)
    (hN : NodePlaced st T s (L.mem s (affA t)))
    (h : ReadyQueues st T s (L.mem s (affA t)) Q)
    (hq : (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64 → t ∈ Q (L.mem s (prioA t))) :
    sched.dequeue st s t ⦃ s' => ReadyQueues st T s' (L.mem s (affA t))
      (if (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64
       then Function.update Q (L.mem s (prioA t)) ((Q (L.mem s (prioA t))).erase t) else Q) ⦄ := by
  have hta : TcbAddr t := hT t ht
  unfold sched.dequeue
  step*
  have hq1 : (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64 := by
    intro hc; have := ‹b = true›; rw [b_post] at this; exact of_decide_eq_true this hc
  simp only [ne_eq, hq1, not_false_eq_true, if_true]
  subst cpu_post prio_post off_post
  set c := L.mem s (affA t)
  set p := L.mem s (prioA t)
  have hqq : q = L.rqQ s c p := by rw [q_post, off_post1]; rfl
  have htQ := hq hq1
  have hR := h.1
  refine WP.spec_bind (tcbqueue.remove.rel s .Sched q t (Q p) hT (hqq ▸ hR.rel p hp) htQ) ?_
  rintro ⟨q1, s1⟩ h1
  simp only [WP.uncurry'_pair] at h1
  obtain ⟨hr1, hf1, -, -⟩ := h1
  have hW : ∀ w ∈ Q p, w ∈ T := fun w hw => (hR.rel p hp).mem w hw
  have hN1 : NodePlaced st T s1 c := hN.framed hf1
  have hv01 := views_framed hT hN hW hf1
  step as ⟨s2, s2_post⟩
  rw [off_post1] at s2_post
  obtain ⟨e2p, e2o, e2l1, e2l2, hl2, hN2⟩ := q_set_views q1 hT hN1 hp
  rw [← s2_post] at e2p e2o e2l1 e2l2 hl2 hN2
  step as ⟨s3, s3_post⟩
  have hN3 : NodePlaced st T s3 c := by rw [s3_post]; exact hN2.wr
  have hv23 : ViewsEq st s2 s3 c := by rw [s3_post]; exact views_wr_inq hN2 ht hta
  have hl23 : LinksEq st T s2 s3 := by rw [s3_post]; exact links_wr_inq hT hta
  -- The queues after the removal.
  have hR3 : ReadyRel st T s3 c (Function.update Q p ((Q p).erase t)) := by
    refine hR.update hT hp ?_ ?_ ?_ ?_
    · intro p' hp' hne
      rw [hv23.1 p' hp', e2o p' hp' hne, hv01.1 p' hp']
    · intro p' hp' hne y hy
      have hyT : y ∈ T := (hR.rel p' hp').mem y hy
      have hyW : y ∉ Q p := fun hy' => hR.disj p p' hp hp' (Ne.symm hne) y hy' hy
      have hWa : ∀ w ∈ Q p, TcbAddr w := fun w hw => hT w (hW w hw)
      have h12n := hf1.2.2.next_eq hWa (hT y hyT) (l' := .Sched) (fun _ => hyW)
      have h12p := hf1.2.2.prev_eq hWa (hT y hyT) (l' := .Sched) (fun _ => hyW)
      exact ⟨((hl23 y hyT .Sched).1.trans (hl2 y hyT .Sched).1).trans h12n,
        ((hl23 y hyT .Sched).2.trans (hl2 y hyT .Sched).2).trans h12p⟩
    · rw [hv23.1 p hp, e2p]; exact (hr1.links hl2).links hl23
    · intro p' hp' hne x hx hx'
      exact hR.disj p p' hp hp' (Ne.symm hne) x (List.mem_of_mem_erase hx) hx'
  have hB3 : BitmapOK st s3 c (fun p' => Q p' ≠ []) := by
    refine h.2.agree ?_ ?_
    · rw [hv23.2.1, e2l1, hv01.2.1]
    · intro g hg; rw [hv23.2.2 g hg, e2l2 g hg, hv01.2.2 g hg]
  have hQne : Q p ≠ [] := List.ne_nil_of_mem htQ
  step as ⟨b1, b1_post⟩
  have hrq3 : L.rqQ s3 c p = q1 := by rw [hv23.1 p hp, e2p]
  have hrel3 := hR3.rel p hp
  simp only [Function.update_self] at hrel3
  rw [hrq3] at hrel3
  split
  · -- the queue became empty: clear the bits
    have hemp : (Q p).erase t = [] := (hrel3.empty_iff hT).1 (by simpa [b1_post] using ‹b1 = true›)
    refine WP.spec_mono (sched.remove_from_bitmap.spec s3 c dom p hp) ?_
    rintro s4 ⟨v2, hv2, hs4⟩
    have hB4 := BitmapOK.remove hN3 hp hB3 hQne hv2 hs4
    have hg : p.val / 64 < 4 := by omega
    have hR4 : ReadyRel st T s4 c (Function.update Q p ((Q p).erase t)) := by
      by_cases hz : v2 = 0#u64
      · rw [if_pos hz] at hs4
        obtain ⟨v1, rfl, -⟩ := hs4
        have h2' := hR3.wr_low (v := v2) hT hN3 (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega)
        have := h2'.wr_low (v := v1) hT hN3.wr (o := l1Off) (by rw [l1Off_val]; omega) (by rw [l1Off_val])
        simpa using this
      · rw [if_neg hz] at hs4
        subst hs4
        exact hR3.wr_low hT hN3 (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega)
    refine ⟨hR4, hB4.congr fun p' _ => ?_⟩
    by_cases e : p' = p
    · subst e; simp [hemp]
    · simp [e]
  · -- still non-empty: the bitmap stays
    have hne : (Q p).erase t ≠ [] := by
      rw [Ne, ← hrel3.empty_iff hT]; simpa [b1_post] using ‹¬b1 = true›
    simp only [WP.spec_ok]
    refine ⟨hR3, hB3.congr fun p' _ => ?_⟩
    by_cases e : p' = p
    · subst e; simp [hne, hQne]
    · simp [e]

end

end Fl4Proofs.P1
