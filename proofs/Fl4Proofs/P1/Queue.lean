/-
P1: intrusive TCB queues (tcbqueue.rs) stay well formed.

`QueueRel m T l q xs` (l4v `valid_ep_q` / `ready_queues` distinctness) says
that the queue `q` (head, end), linked through the TCB fields of link kind
`l` (`SCHED_NEXT/PREV` or `EP_NEXT/PREV`), holds exactly the TCBs `xs` in
memory `m`: they are distinct members of the ghost set `T` of TCB addresses
(`TcbPlaced T`: nonzero, aligned to `2 ^ 12`, not wrapping, so the link
fields lie inside the TCB), the head is the first (0 if empty), the end the
last, `next`/`prev` link each member to its neighbours, the head's `prev`
and the end's `next` are 0. The list is determined by memory
(`QueueRel.unique`).

The primitives refine list operations: `append` is `xs ++ [t]`, `prepend`
`t :: xs`, `remove` `xs.erase t`, `insert_before`/`insert_after` insert next
to a member. Each writes only the `l` links of `t :: xs` (`Framed`), so every
queue of the other link kind, or of other TCBs, stays related
(`QueueRel.frame`, `QueueRel.framed`).
-/
import Fl4Proofs.P1.Store
import Fl4Proofs.P0.Consts
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

/-! ## Link field addresses (layout.rs `tcb::SCHED_NEXT` ..) -/

/-- Offset of the `next` field of link kind `l` in a TCB. -/
def nextOff : tcbqueue.Link → U64
  | .Sched => 3480#u64
  | .Ep => 3496#u64
/-- Offset of the `prev` field of link kind `l` in a TCB. -/
def prevOff : tcbqueue.Link → U64
  | .Sched => 3488#u64
  | .Ep => 3504#u64

def nextA (l : tcbqueue.Link) (t : U64) : U64 := core.num.U64.wrapping_add t (nextOff l)
def prevA (l : tcbqueue.Link) (t : U64) : U64 := core.num.U64.wrapping_add t (prevOff l)

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

@[step] theorem tcbqueue.next.spec (s : S) (l : tcbqueue.Link) (t : obj.Tcb) :
    tcbqueue.next st s l t ⦃ v => v = L.mem s (nextA l t) ⦄ := by
  unfold tcbqueue.next; cases l
  · unfold obj.Tcb.sched_next; step*; simp_all [nextA, nextOff]
  · unfold obj.Tcb.ep_next; step*; simp_all [nextA, nextOff]

@[step] theorem tcbqueue.prev.spec (s : S) (l : tcbqueue.Link) (t : obj.Tcb) :
    tcbqueue.prev st s l t ⦃ v => v = L.mem s (prevA l t) ⦄ := by
  unfold tcbqueue.prev; cases l
  · unfold obj.Tcb.sched_prev; step*; simp_all [prevA, prevOff]
  · unfold obj.Tcb.ep_prev; step*; simp_all [prevA, prevOff]

@[step] theorem tcbqueue.set_next.spec (s : S) (l : tcbqueue.Link) (t : obj.Tcb) (v : U64) :
    tcbqueue.set_next st s l t v ⦃ s' => s' = L.wr s (nextA l t) v ⦄ := by
  unfold tcbqueue.set_next; cases l
  · unfold obj.Tcb.set_sched_next; step*; simp_all [nextA, nextOff]
  · unfold obj.Tcb.set_ep_next; step*; simp_all [nextA, nextOff]

@[step] theorem tcbqueue.set_prev.spec (s : S) (l : tcbqueue.Link) (t : obj.Tcb) (v : U64) :
    tcbqueue.set_prev st s l t v ⦃ s' => s' = L.wr s (prevA l t) v ⦄ := by
  unfold tcbqueue.set_prev; cases l
  · unfold obj.Tcb.set_sched_prev; step*; simp_all [prevA, prevOff]
  · unfold obj.Tcb.set_ep_prev; step*; simp_all [prevA, prevOff]

end

deriving instance DecidableEq for tcbqueue.Link

/-! ## TCB placement -/

/-- A TCB address: nonzero, aligned to `2 ^ 12` (the TCB object size), and
the object does not wrap around the address space. -/
structure TcbAddr (t : U64) : Prop where
  ne0 : t.val ≠ 0
  align : t.val % 2 ^ 12 = 0
  fits : t.val + 2 ^ 12 ≤ 2 ^ 64

/-- The ghost set `T` of TCB addresses: every member is placed. -/
def TcbPlaced (T : Set U64) : Prop := ∀ t ∈ T, TcbAddr t

theorem nextA_val {t : U64} (h : TcbAddr t) (l : tcbqueue.Link) :
    (nextA l t).val = t.val + (nextOff l).val := by
  have := h.fits
  cases l <;> simp [nextA, nextOff, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits] <;> omega

theorem prevA_val {t : U64} (h : TcbAddr t) (l : tcbqueue.Link) :
    (prevA l t).val = t.val + (prevOff l).val := by
  have := h.fits
  cases l <;> simp [prevA, prevOff, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits] <;> omega

/-- The link fields lie inside the TCB (`F + 152 .. F + 176`, `F = 0xd00`). -/
theorem nextA_inside {t : U64} (h : TcbAddr t) (l : tcbqueue.Link) :
    t.val ≤ (nextA l t).val ∧ (nextA l t).val + 8 ≤ t.val + 2 ^ 12 := by
  rw [nextA_val h]; cases l <;> simp [nextOff]

theorem prevA_inside {t : U64} (h : TcbAddr t) (l : tcbqueue.Link) :
    t.val ≤ (prevA l t).val ∧ (prevA l t).val + 8 ≤ t.val + 2 ^ 12 := by
  rw [prevA_val h]; cases l <;> simp [prevOff]

theorem nextA_aligned {t : U64} (h : TcbAddr t) (l : tcbqueue.Link) : Aligned (nextA l t) := by
  have := h.align
  unfold Aligned; rw [nextA_val h]; cases l <;> simp [nextOff] <;> omega

theorem prevA_aligned {t : U64} (h : TcbAddr t) (l : tcbqueue.Link) : Aligned (prevA l t) := by
  have := h.align
  unfold Aligned; rw [prevA_val h]; cases l <;> simp [prevOff] <;> omega

theorem nextA_eq_iff {x y : U64} (hx : TcbAddr x) (hy : TcbAddr y) (l l' : tcbqueue.Link) :
    nextA l x = nextA l' y ↔ l = l' ∧ x = y := by
  constructor
  · intro h
    have h' := congrArg UScalar.val h
    rw [nextA_val hx, nextA_val hy] at h'
    have := hx.align; have := hy.align
    have hxy : x.val = y.val := by cases l <;> cases l' <;> simp [nextOff] at h' <;> omega
    refine ⟨?_, UScalar.eq_of_val_eq hxy⟩
    rw [hxy] at h'
    cases l <;> cases l' <;> simp [nextOff] at h' ⊢
  · rintro ⟨rfl, rfl⟩; rfl

theorem prevA_eq_iff {x y : U64} (hx : TcbAddr x) (hy : TcbAddr y) (l l' : tcbqueue.Link) :
    prevA l x = prevA l' y ↔ l = l' ∧ x = y := by
  constructor
  · intro h
    have h' := congrArg UScalar.val h
    rw [prevA_val hx, prevA_val hy] at h'
    have := hx.align; have := hy.align
    have hxy : x.val = y.val := by cases l <;> cases l' <;> simp [prevOff] at h' <;> omega
    refine ⟨?_, UScalar.eq_of_val_eq hxy⟩
    rw [hxy] at h'
    cases l <;> cases l' <;> simp [prevOff] at h' ⊢
  · rintro ⟨rfl, rfl⟩; rfl

theorem nextA_ne_prevA {x y : U64} (hx : TcbAddr x) (hy : TcbAddr y) (l l' : tcbqueue.Link) :
    nextA l x ≠ prevA l' y := by
  intro h
  have h' := congrArg UScalar.val h
  rw [nextA_val hx, prevA_val hy] at h'
  have := hx.align; have := hy.align
  cases l <;> cases l' <;> simp [nextOff, prevOff] at h' <;> omega

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-! Reads of link fields after writes of link fields. -/

theorem rd_wr_nn {s : S} {x y v : U64} {l l' : tcbqueue.Link} (hx : TcbAddr x) (hy : TcbAddr y) :
    L.mem (L.wr s (nextA l x) v) (nextA l' y) = if l = l' ∧ x = y then v else L.mem s (nextA l' y) := by
  rw [L.mem_wr _ _ _ _ (nextA_aligned hx l) (nextA_aligned hy l')]
  simp only [nextA_eq_iff hx hy]
theorem rd_wr_pp {s : S} {x y v : U64} {l l' : tcbqueue.Link} (hx : TcbAddr x) (hy : TcbAddr y) :
    L.mem (L.wr s (prevA l x) v) (prevA l' y) = if l = l' ∧ x = y then v else L.mem s (prevA l' y) := by
  rw [L.mem_wr _ _ _ _ (prevA_aligned hx l) (prevA_aligned hy l')]
  simp only [prevA_eq_iff hx hy]
theorem rd_wr_np {s : S} {x y v : U64} {l l' : tcbqueue.Link} (hx : TcbAddr x) (hy : TcbAddr y) :
    L.mem (L.wr s (nextA l x) v) (prevA l' y) = L.mem s (prevA l' y) := by
  rw [L.mem_wr _ _ _ _ (nextA_aligned hx l) (prevA_aligned hy l')]
  simp [nextA_ne_prevA hx hy]
theorem rd_wr_pn {s : S} {x y v : U64} {l l' : tcbqueue.Link} (hx : TcbAddr x) (hy : TcbAddr y) :
    L.mem (L.wr s (prevA l x) v) (nextA l' y) = L.mem s (nextA l' y) := by
  rw [L.mem_wr _ _ _ _ (prevA_aligned hx l) (nextA_aligned hy l')]
  simp [Ne.symm (nextA_ne_prevA hy hx l' l)]

end

/-! ## Linked segments and the queue relation -/

/-- `Seg m l p xs n`: in memory `m`, the TCBs `xs` are linked in order
through the `l` fields; the first one's `prev` is `p` and the last one's
`next` is `n`. -/
def Seg (m : U64 → U64) (l : tcbqueue.Link) : U64 → List U64 → U64 → Prop
  | _, [], _ => True
  | p, x :: xs, n => m (prevA l x) = p ∧ m (nextA l x) = xs.headD n ∧ Seg m l x xs n

@[simp] theorem Seg_nil (m : U64 → U64) l p n : Seg m l p [] n := trivial
@[simp] theorem Seg_cons (m : U64 → U64) l p x xs n :
    Seg m l p (x :: xs) n ↔ m (prevA l x) = p ∧ m (nextA l x) = xs.headD n ∧ Seg m l x xs n := Iff.rfl

theorem headD_append (xs ys : List U64) (n : U64) : (xs ++ ys).headD n = xs.headD (ys.headD n) := by
  cases xs <;> rfl

theorem Seg_append (m : U64 → U64) l p xs ys n :
    Seg m l p (xs ++ ys) n ↔ Seg m l p xs (ys.headD n) ∧ Seg m l (xs.getLastD p) ys n := by
  induction xs generalizing p with
  | nil => simp
  | cons x xs ih =>
    simp only [List.cons_append, Seg_cons, ih, headD_append, List.getLastD_cons]
    tauto

/-- A segment split around a member. -/
theorem Seg_mid (m : U64 → U64) l p xs y ys n :
    Seg m l p (xs ++ y :: ys) n ↔ Seg m l p xs y ∧ m (prevA l y) = xs.getLastD p ∧
      m (nextA l y) = ys.headD n ∧ Seg m l y ys n := by
  rw [Seg_append]; simp

/-- A segment only depends on the link fields of its members. -/
theorem Seg.congr {m m' : U64 → U64} {l p xs n}
    (h : ∀ x ∈ xs, m' (prevA l x) = m (prevA l x) ∧ m' (nextA l x) = m (nextA l x))
    (hs : Seg m l p xs n) : Seg m' l p xs n := by
  induction xs generalizing p with
  | nil => trivial
  | cons x xs ih =>
    obtain ⟨h1, h2, h3⟩ := hs
    have hx := h x (by simp)
    exact ⟨hx.1.trans h1, hx.2.trans h2, ih (fun y hy => h y (by simp [hy])) h3⟩

/-- The list linked from the head is determined by memory: a segment ending
in `0` of nonzero TCBs is the list reachable from its first element. -/
theorem Seg.unique {m : U64 → U64} {l} :
    ∀ {p p' : U64} {xs ys : List U64}, Seg m l p xs 0#u64 → Seg m l p' ys 0#u64 →
      (∀ x ∈ xs, x ≠ 0#u64) → (∀ y ∈ ys, y ≠ 0#u64) → xs.headD 0#u64 = ys.headD 0#u64 → xs = ys
  | _, _, [], [], _, _, _, _, _ => rfl
  | _, _, [], y :: _, _, _, _, hy, he => by simp at he; exact absurd he.symm (hy y (by simp))
  | _, _, x :: _, [], _, _, hx, _, he => by simp at he; exact absurd he (hx x (by simp))
  | _, _, x :: xs, y :: ys, ⟨_, h2, h3⟩, ⟨_, h2', h3'⟩, hx, hy, he => by
    simp at he; subst he
    congr 1
    exact Seg.unique h3 h3' (fun z hz => hx z (by simp [hz])) (fun z hz => hy z (by simp [hz]))
      (h2.symm.trans h2')

/-- `QueueRel m T l q xs`: the queue `q` (head and end) of TCBs linked
through the `l` fields holds the TCBs `xs`, in order, in memory `m`
(l4v `valid_ep_q` / `ready_queues` distinctness, on intrusive links):
the members are distinct TCBs of the ghost set `T`, `q.head` is the first
(0 if empty), `q.end` the last (0 if empty), each member's `next` is its
successor and `prev` its predecessor, the head's `prev` and the end's `next`
are 0. -/
structure QueueRel (m : U64 → U64) (T : Set U64) (l : tcbqueue.Link) (q : tcbqueue.Queue)
    (xs : List U64) : Prop where
  nodup : xs.Nodup
  mem : ∀ t ∈ xs, t ∈ T
  head : q.head = xs.headD 0#u64
  last : q.end = xs.getLastD 0#u64
  seg : Seg m l 0#u64 xs 0#u64

theorem QueueRel.addr {m T l q xs} (hT : TcbPlaced T) (h : QueueRel m T l q xs) :
    ∀ t ∈ xs, TcbAddr t := fun t ht => hT t (h.mem t ht)

theorem QueueRel.ne0 {m T l q xs} (hT : TcbPlaced T) (h : QueueRel m T l q xs) :
    ∀ t ∈ xs, t ≠ 0#u64 := fun t ht h0 => (h.addr hT t ht).ne0 (by simp [h0])

/-- The list is determined by memory and the head. -/
theorem QueueRel.unique {m T l q xs ys} (hT : TcbPlaced T) (h : QueueRel m T l q xs)
    (h' : QueueRel m T l q ys) : xs = ys :=
  Seg.unique h.seg h'.seg (h.ne0 hT) (h'.ne0 hT) (h.head.symm.trans h'.head)

theorem QueueRel.empty_iff {m T l q xs} (hT : TcbPlaced T) (h : QueueRel m T l q xs) :
    q.head = 0#u64 ↔ xs = [] := by
  rw [h.head]
  cases xs with
  | nil => simp
  | cons x xs => simpa using h.ne0 hT x (by simp)

theorem QueueRel.nil {m T l} : QueueRel m T l ⟨0#u64, 0#u64⟩ [] :=
  ⟨List.nodup_nil, by simp, rfl, rfl, trivial⟩

/-! ## Frames -/

/-- `m'` agrees with `m` everywhere except on the `l` link fields of the
TCBs `W`. -/
def LinkFrame (l : tcbqueue.Link) (W : List U64) (m m' : U64 → U64) : Prop :=
  ∀ b : U64, Aligned b → (∀ w ∈ W, b ≠ nextA l w ∧ b ≠ prevA l w) → m' b = m b

theorem LinkFrame.refl l W (m : U64 → U64) : LinkFrame l W m m := fun _ _ _ => rfl

theorem LinkFrame.trans {l W} {m₁ m₂ m₃ : U64 → U64} (h₁ : LinkFrame l W m₁ m₂)
    (h₂ : LinkFrame l W m₂ m₃) : LinkFrame l W m₁ m₃ :=
  fun b hb hout => (h₂ b hb hout).trans (h₁ b hb hout)

theorem LinkFrame.mono {l W W'} {m m' : U64 → U64} (h : LinkFrame l W m m') (hW : W ⊆ W') :
    LinkFrame l W' m m' :=
  fun b hb hout => h b hb (fun w hw => hout w (hW hw))

/-- A link field of a TCB outside the frame, or of another link kind, is
unchanged. -/
theorem LinkFrame.next_eq {l W} {m m' : U64 → U64} (h : LinkFrame l W m m') (hW : ∀ w ∈ W, TcbAddr w)
    {l' y} (hy : TcbAddr y) (hout : l' = l → y ∉ W) : m' (nextA l' y) = m (nextA l' y) := by
  refine h _ (nextA_aligned hy l') (fun w hw => ⟨?_, nextA_ne_prevA hy (hW w hw) l' l⟩)
  rw [Ne, nextA_eq_iff hy (hW w hw)]
  rintro ⟨rfl, rfl⟩; exact hout rfl hw

theorem LinkFrame.prev_eq {l W} {m m' : U64 → U64} (h : LinkFrame l W m m') (hW : ∀ w ∈ W, TcbAddr w)
    {l' y} (hy : TcbAddr y) (hout : l' = l → y ∉ W) : m' (prevA l' y) = m (prevA l' y) := by
  refine h _ (prevA_aligned hy l') (fun w hw => ⟨Ne.symm (nextA_ne_prevA (hW w hw) hy l l'), ?_⟩)
  rw [Ne, prevA_eq_iff hy (hW w hw)]
  rintro ⟨rfl, rfl⟩; exact hout rfl hw

/-- The frame lemma: an operation that only writes the `l` links of the
TCBs `W` leaves every queue linked by another kind, or made of TCBs outside
`W`, related to the same list. -/
theorem QueueRel.frame {m m' : U64 → U64} {T l l' q ys W} (hT : TcbPlaced T)
    (hW : ∀ w ∈ W, TcbAddr w) (hf : LinkFrame l W m m')
    (hd : l' = l → ∀ y ∈ ys, y ∉ W) (h : QueueRel m T l' q ys) : QueueRel m' T l' q ys :=
  ⟨h.nodup, h.mem, h.head, h.last, h.seg.congr fun y hy =>
    ⟨hf.prev_eq hW (h.addr hT y hy) (fun e => hd e y hy),
     hf.next_eq hW (h.addr hT y hy) (fun e => hd e y hy)⟩⟩

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- What the queue primitives change: only `l` link fields of `W`. -/
def Framed (st : machine.Store S) [L : LawfulStore st] (l : tcbqueue.Link) (W : List U64) (s s' : S) : Prop :=
  L.ksb s' = L.ksb s ∧ L.cpu s' = L.cpu s ∧ LinkFrame l W (L.mem s) (L.mem s')

theorem Framed.refl l W (s : S) : Framed st l W s s := ⟨rfl, rfl, LinkFrame.refl _ _ _⟩

theorem Framed.trans {l W} {s₁ s₂ s₃ : S} (h₁ : Framed st l W s₁ s₂) (h₂ : Framed st l W s₂ s₃) :
    Framed st l W s₁ s₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₁.2.2.trans h₂.2.2⟩

theorem Framed.wr_next {l W} {s : S} {w v : U64} (hw : w ∈ W) (ha : TcbAddr w) :
    Framed st l W s (L.wr s (nextA l w) v) := by
  refine ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun b hb hout => ?_⟩
  rw [L.mem_wr _ _ _ _ (nextA_aligned ha l) hb]
  simp [Ne.symm (hout w hw).1]

theorem Framed.wr_prev {l W} {s : S} {w v : U64} (hw : w ∈ W) (ha : TcbAddr w) :
    Framed st l W s (L.wr s (prevA l w) v) := by
  refine ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun b hb hout => ?_⟩
  rw [L.mem_wr _ _ _ _ (prevA_aligned ha l) hb]
  simp [Ne.symm (hout w hw).2]

end

/-! ## List facts -/

theorem eq_nil_or_snoc (l : List U64) : l = [] ∨ ∃ l' b, l = l' ++ [b] := by
  rcases List.eq_nil_or_concat l with h | ⟨l', b, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨l', b, by simpa using h⟩

theorem ne_of_nodup_append {l1 l2 : List U64} {x y : U64} (h : (l1 ++ l2).Nodup) (hx : x ∈ l1)
    (hy : y ∈ l2) : x ≠ y :=
  (List.nodup_append.1 h).2.2 x hx y hy

theorem headD_append_of_ne {xs : List U64} (ys : List U64) (h : xs ≠ []) (a : U64) :
    (xs ++ ys).headD a = xs.headD a := by
  cases xs with
  | nil => exact absurd rfl h
  | cons => rfl

theorem getLastD_append_of_ne (xs : List U64) {ys : List U64} (h : ys ≠ []) (a : U64) :
    (xs ++ ys).getLastD a = ys.getLastD a := by
  rw [List.getLastD_eq_getLast?, List.getLastD_eq_getLast?, List.getLast?_append]
  cases hy : ys.getLast? with
  | none => simp at hy; exact absurd hy h
  | some v => rfl

theorem getLastD_of_ne {xs : List U64} (h : xs ≠ []) (a b : U64) : xs.getLastD a = xs.getLastD b := by
  rw [List.getLastD_eq_getLast?, List.getLastD_eq_getLast?]
  cases hy : xs.getLast? with
  | none => simp at hy; exact absurd hy h
  | some v => rfl

theorem headD_mem {xs : List U64} (h : xs ≠ []) (a : U64) : xs.headD a ∈ xs := by
  cases xs with
  | nil => exact absurd rfl h
  | cons => simp

theorem getLastD_mem {xs : List U64} (h : xs ≠ []) (a : U64) : xs.getLastD a ∈ xs := by
  rw [List.getLastD_eq_getLast?]
  cases hy : xs.getLast? with
  | none => simp at hy; exact absurd hy h
  | some v => exact List.mem_of_getLast? hy

/-! ## The primitives -/

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64}

@[step] theorem obj.Tcb.is_null.spec (t : obj.Tcb) :
    obj.Tcb.is_null t ⦃ b => b = decide (t = 0#u64) ⦄ := by
  unfold obj.Tcb.is_null; simp

@[step] theorem tcbqueue.Queue.is_empty.spec (q : tcbqueue.Queue) :
    tcbqueue.Queue.is_empty q ⦃ b => b = decide (q.head = 0#u64) ⦄ := by
  unfold tcbqueue.Queue.is_empty obj.Tcb.is_null; simp

theorem nodup_tail_ne {xs : List U64} {e t : U64} (h : (xs ++ [e]).Nodup) (ht : t ∈ xs) : t ≠ e := by
  rintro rfl; simp [List.nodup_append] at h; exact h.2 _ ht rfl

theorem nodup_snoc {xs : List U64} {t : U64} : (xs ++ [t]).Nodup ↔ xs.Nodup ∧ t ∉ xs := by
  rw [List.nodup_append_comm]; simp [List.nodup_cons]; tauto

theorem headD_ne_nil {xs : List U64} (h : xs ≠ []) (a b : U64) : xs.headD a = xs.headD b := by
  cases xs with
  | nil => exact absurd rfl h
  | cons => rfl

/-- Close goals about link fields after link writes. -/
macro "rdwr" : tactic => `(tactic| simp [rd_wr_nn, rd_wr_pp, rd_wr_np, rd_wr_pn, *])

theorem QueueRel.append_nonempty {s : S} {l : tcbqueue.Link} {q : tcbqueue.Queue} {t : U64}
    {xs : List U64} (hT : TcbPlaced T) (h : QueueRel (L.mem s) T l q xs) (ht : t ∈ T) (hn : t ∉ xs)
    (hne : xs ≠ []) :
    QueueRel (L.mem (L.wr (L.wr (L.wr s (nextA l q.end) t) (prevA l t) q.end) (nextA l t) 0#u64))
        T l { head := q.head, «end» := t } (xs ++ [t]) ∧
      Framed st l (t :: xs) s (L.wr (L.wr (L.wr s (nextA l q.end) t) (prevA l t) q.end) (nextA l t) 0#u64) := by
  have hta : TcbAddr t := hT t ht
  obtain ⟨ys, e, rfl⟩ : ∃ ys e, xs = ys ++ [e] := by
    rcases List.eq_nil_or_concat xs with h' | ⟨ys, e, h'⟩
    · exact absurd h' hne
    · exact ⟨ys, e, by simpa using h'⟩
  have hqe : q.end = e := by rw [h.last]; simp
  rw [hqe]
  have hea : TcbAddr e := h.addr hT e (by simp)
  have hte : t ≠ e := fun h' => hn (by simp [h'])
  have := hte.symm
  have old := h.seg
  rw [Seg_mid] at old
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact nodup_snoc.2 ⟨h.nodup, hn⟩
  · intro x hx; simp only [List.mem_append, List.mem_singleton] at hx; rcases hx with hx | hx
    · exact h.mem x (by simpa using hx)
    · exact hx ▸ ht
  · rw [h.head]; simp
  · simp
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [Seg_mid]
    refine ⟨Seg.congr ?_ old.1, ?_, ?_, ?_⟩
    · intro x hx
      have hxa : TcbAddr x := h.addr hT x (by simp [hx])
      have hxe : x ≠ e := nodup_tail_ne h.nodup hx
      have hxt : x ≠ t := fun h' => hn (by simp [← h', hx])
      have := hxe.symm; have := hxt.symm
      constructor <;> rdwr
    · rw [← old.2.1]; rdwr
    · rdwr
    · simp; constructor <;> rdwr
  · refine ((Framed.wr_next (by simp) hea).trans (Framed.wr_prev (by simp) hta)).trans
      (Framed.wr_next (by simp) hta)

theorem QueueRel.single {s : S} {l : tcbqueue.Link} {q : tcbqueue.Queue} {t : U64}
    {xs : List U64} (hT : TcbPlaced T) (h : QueueRel (L.mem s) T l q xs) (ht : t ∈ T)
    (he : q.head = 0#u64) :
    xs = [] ∧ QueueRel (L.mem (L.wr (L.wr s (nextA l t) 0#u64) (prevA l t) 0#u64)) T l
        { head := t, «end» := t } [t] ∧
      Framed st l [t] s (L.wr (L.wr s (nextA l t) 0#u64) (prevA l t) 0#u64) := by
  have hta : TcbAddr t := hT t ht
  refine ⟨(h.empty_iff hT).1 he, ⟨by simp, by simpa using ht, rfl, rfl, ?_⟩, ?_⟩
  · simp; constructor <;> rdwr
  · exact (Framed.wr_next (by simp) hta).trans (Framed.wr_prev (by simp) hta)

theorem Framed.mono {l W W'} {s s' : S} (h : Framed st l W s s') (hW : W ⊆ W') : Framed st l W' s s' :=
  ⟨h.1, h.2.1, h.2.2.mono hW⟩

/-- `append` is `xs ++ [t]`. -/
theorem tcbqueue.append.rel (s : S) (l : tcbqueue.Link) (q : tcbqueue.Queue) (t : obj.Tcb)
    (xs : List U64) (hT : TcbPlaced T) (h : QueueRel (L.mem s) T l q xs) (ht : t ∈ T) (hn : t ∉ xs) :
    tcbqueue.append st s l q t ⦃ q' s' =>
      QueueRel (L.mem s') T l q' (xs ++ [t]) ∧ Framed st l (t :: xs) s s' ⦄ := by
  unfold tcbqueue.append
  step*
  · subst_vars
    obtain ⟨rfl, h1, h2⟩ := h.single hT ht (by simpa using ‹decide (q.head = 0#u64) = true›)
    exact ⟨h1, h2.mono (by simp)⟩
  · subst_vars
    refine h.append_nonempty hT ht hn ?_
    rw [Ne, ← h.empty_iff hT]; simpa using ‹¬decide (q.head = 0#u64) = true›
@[step] theorem obj.Tcb.eq.spec (x y : obj.Tcb) :
    obj.Tcb.Insts.CoreCmpPartialEqTcb.eq x y ⦃ b => b = decide (x = y) ⦄ := by
  unfold obj.Tcb.Insts.CoreCmpPartialEqTcb.eq; simp

/-- `remove`, as a function of the state. -/
def removeF (st : machine.Store S) [L : LawfulStore st] (s : S) (l : tcbqueue.Link)
    (q : tcbqueue.Queue) (t : U64) : tcbqueue.Queue × S :=
  let before := L.mem s (prevA l t)
  let after := L.mem s (nextA l t)
  let p : S × tcbqueue.Queue :=
    if q.head = t ∧ q.end = t then (s, ⟨0#u64, 0#u64⟩)
    else if q.head = t then (L.wr s (prevA l after) 0#u64, ⟨after, q.end⟩)
    else if q.end = t then (L.wr s (nextA l before) 0#u64, ⟨q.head, before⟩)
    else (L.wr (L.wr s (nextA l before) after) (prevA l after) before, q)
  (p.2, L.wr (L.wr p.1 (nextA l t) 0#u64) (prevA l t) 0#u64)

theorem tcbqueue.remove.eq (s : S) (l : tcbqueue.Link) (q : tcbqueue.Queue) (t : obj.Tcb) :
    tcbqueue.remove st s l q t ⦃ q' s' => (q', s') = removeF st s l q t ⦄ := by
  unfold tcbqueue.remove tcbqueue.Queue.empty
  step*
  by_cases h1 : q.head = t <;> by_cases h2 : q.end = t <;> simp [b_post, h1, h2] <;> step* <;>
    simp_all [removeF] <;> step*

/-- Writing the links of a TCB outside a queue leaves the queue related. -/
theorem QueueRel.wr_out2 {s : S} {l q ys} {t v w : U64} (hT : TcbPlaced T) (hta : TcbAddr t)
    (h : QueueRel (L.mem s) T l q ys) (hn : t ∉ ys) :
    QueueRel (L.mem (L.wr (L.wr s (nextA l t) v) (prevA l t) w)) T l q ys :=
  h.frame hT (W := [t]) (by simpa using hta)
    ((Framed.wr_next (st := st) (l := l) (s := s) (v := v) (by simp) hta).trans
      (Framed.wr_prev (by simp) hta)).2.2
    (fun _ y hy hy' => hn (by simp at hy'; exact hy' ▸ hy))

theorem removeF_rel {s : S} {l : tcbqueue.Link} {q : tcbqueue.Queue} {t : U64} {xs : List U64}
    (hT : TcbPlaced T) (h : QueueRel (L.mem s) T l q xs) (ht : t ∈ xs) :
    QueueRel (L.mem (removeF st s l q t).2) T l (removeF st s l q t).1 (xs.erase t) ∧
      Framed st l xs s (removeF st s l q t).2 ∧
      L.mem (removeF st s l q t).2 (nextA l t) = 0#u64 ∧
      L.mem (removeF st s l q t).2 (prevA l t) = 0#u64 := by
  have hta : TcbAddr t := h.addr hT t ht
  obtain ⟨ys, zs, rfl⟩ := List.append_of_mem ht
  have hnd := h.nodup
  have hnd' := List.nodup_middle.1 hnd
  simp only [List.nodup_cons, List.mem_append, not_or] at hnd'
  obtain ⟨⟨hty, htz⟩, hyz⟩ := hnd'
  have herase : (ys ++ t :: zs).erase t = ys ++ zs := by
    rw [List.erase_append_right _ hty]; simp
  rw [herase]
  have old := h.seg
  rw [Seg_mid] at old
  obtain ⟨oldY, hbt, hat, oldZ⟩ := old
  -- The writes to `t` at the end.
  have fin : ∀ (s1 : S) q1, QueueRel (L.mem s1) T l q1 (ys ++ zs) → Framed st l (ys ++ t :: zs) s s1 →
      QueueRel (L.mem (L.wr (L.wr s1 (nextA l t) 0#u64) (prevA l t) 0#u64)) T l q1 (ys ++ zs) ∧
      Framed st l (ys ++ t :: zs) s (L.wr (L.wr s1 (nextA l t) 0#u64) (prevA l t) 0#u64) ∧
      L.mem (L.wr (L.wr s1 (nextA l t) 0#u64) (prevA l t) 0#u64) (nextA l t) = 0#u64 ∧
      L.mem (L.wr (L.wr s1 (nextA l t) 0#u64) (prevA l t) 0#u64) (prevA l t) = 0#u64 := by
    intro s1 q1 hq hf
    refine ⟨hq.wr_out2 hT hta (by simp [hty, htz]), hf.trans ((Framed.wr_next (by simp) hta).trans
      (Framed.wr_prev (by simp) hta)), by rdwr, by rdwr⟩
  rcases eq_nil_or_snoc ys with rfl | ⟨ys', b, rfl⟩ <;>
    rcases zs with _ | ⟨a, zs'⟩
  · -- the only member
    have h1 : q.head = t := by rw [h.head]; rfl
    have h2 : q.end = t := by rw [h.last]; rfl
    simp only [removeF, h1, h2, and_self, ite_true]
    exact fin s _ QueueRel.nil (Framed.refl _ _ _)
  · -- the head
    have h1 : q.head = t := by rw [h.head]; rfl
    have h2 : q.end ≠ t := by
      rw [h.last, List.nil_append, show t :: a :: zs' = [t] ++ a :: zs' from rfl,
        getLastD_append_of_ne _ (by simp)]
      intro he; apply htz; rw [← he]; exact getLastD_mem (by simp) _
    simp only [removeF, h1, h2, and_false, ite_false, ite_true, hat, List.headD_cons]
    simp only [List.nil_append, List.not_mem_nil, not_false_eq_true, List.mem_cons, not_or] at *
    have haa : TcbAddr a := h.addr hT a (by simp)
    have := htz.1; have := Ne.symm htz.1
    refine fin _ _ ⟨hyz, fun x hx => h.mem x (by simp_all), rfl, ?_, ?_⟩ ?_
    · rw [h.last]; simp
    · simp only [Seg_cons] at oldZ ⊢
      refine ⟨by rdwr, by rw [← oldZ.2.1]; rdwr, Seg.congr ?_ oldZ.2.2⟩
      intro x hx
      have hxa : TcbAddr x := h.addr hT x (by simp [hx])
      have : x ≠ a := fun e => (List.nodup_cons.1 hyz).1 (e ▸ hx)
      have := this.symm
      constructor <;> rdwr
    · exact Framed.wr_prev (by simp) haa
  · -- the end
    have h1 : q.head ≠ t := by
      rw [h.head, headD_append_of_ne _ (by simp)]
      intro he; apply hty; rw [← he]; exact headD_mem (by simp) _
    have h2 : q.end = t := by rw [h.last]; simp
    simp only [List.getLastD_concat] at hbt
    simp only [removeF, h1, h2, and_true, ite_false, ite_true, hbt]
    simp only [List.append_nil] at *
    have hba : TcbAddr b := h.addr hT b (by simp)
    have := hty; simp at this
    have htb : t ≠ b := fun e => this.2 (by rw [e])
    have := htb.symm
    refine fin _ _ ⟨hyz, fun x hx => h.mem x (by simp at hx ⊢; tauto), ?_, by simp, ?_⟩ ?_
    · rw [h.head]; simp
    · rw [Seg_mid] at oldY ⊢
      refine ⟨Seg.congr ?_ oldY.1, by rw [← oldY.2.1]; rdwr, by rdwr, trivial⟩
      intro x hx
      have hxa : TcbAddr x := h.addr hT x (by simp [hx])
      have : x ≠ b := nodup_tail_ne hyz hx
      have := this.symm
      constructor <;> rdwr
    · exact Framed.wr_next (by simp) hba
  · -- the middle
    have h1 : q.head ≠ t := by
      rw [h.head, headD_append_of_ne _ (by simp)]
      intro he; apply hty; rw [← he]; exact headD_mem (by simp) _
    have h2 : q.end ≠ t := by
      rw [h.last, getLastD_append_of_ne _ (by simp), show t :: a :: zs' = [t] ++ a :: zs' from rfl,
        getLastD_append_of_ne _ (by simp)]
      intro he; apply htz; rw [← he]; exact getLastD_mem (by simp) _
    simp only [List.getLastD_concat] at hbt
    simp only [List.headD_cons] at hat
    simp only [removeF, h1, h2, false_and, ite_false, hbt, hat]
    have hba : TcbAddr b := h.addr hT b (by simp)
    have haa : TcbAddr a := h.addr hT a (by simp)
    have hab : b ≠ a := ne_of_nodup_append (l1 := ys' ++ [b]) (l2 := a :: zs') hyz (by simp) (by simp)
    have := hab.symm
    have htb : t ≠ b := fun e => hty (by simp [e])
    have hta' : t ≠ a := fun e => htz (by simp [e])
    have := htb.symm; have := hta'.symm
    have hseg := oldZ; simp only [Seg_cons] at hseg
    refine fin _ _ ⟨hyz, fun x hx => h.mem x (by simp at hx ⊢; tauto),
      by rw [h.head, headD_append_of_ne (xs := ys' ++ [b]) _ (by simp),
        headD_append_of_ne (xs := ys' ++ [b]) _ (by simp)], ?_, ?_⟩ ?_
    · rw [h.last, getLastD_append_of_ne _ (by simp), getLastD_append_of_ne _ (by simp)]
      simp only [List.getLastD_cons]
    · rw [Seg_mid] at oldY
      rw [List.append_assoc, List.singleton_append, Seg_mid]
      refine ⟨Seg.congr ?_ oldY.1, by rw [← oldY.2.1]; rdwr, by rdwr, ?_⟩
      · intro x hx
        have hxa : TcbAddr x := h.addr hT x (by simp [hx])
        have : x ≠ b := ne_of_nodup_append (l1 := ys') (l2 := b :: a :: zs') (by simpa using hyz) hx (by simp)
        have : x ≠ a := ne_of_nodup_append (l1 := ys') (l2 := b :: a :: zs') (by simpa using hyz) hx (by simp)
        have := (‹x ≠ b›).symm; have := (‹x ≠ a›).symm
        constructor <;> rdwr
      · simp only [Seg_cons]
        refine ⟨by rdwr, by rw [← hseg.2.1]; rdwr, Seg.congr ?_ hseg.2.2⟩
        intro x hx
        have hxa : TcbAddr x := h.addr hT x (by simp [hx])
        have : a ≠ x := ne_of_nodup_append (l1 := ys' ++ [b, a]) (l2 := zs') (by simpa using hyz) (by simp) hx
        have : b ≠ x := ne_of_nodup_append (l1 := ys' ++ [b, a]) (l2 := zs') (by simpa using hyz) (by simp) hx
        have := (‹a ≠ x›).symm; have := (‹b ≠ x›).symm
        constructor <;> rdwr
    · exact (Framed.wr_next (by simp) hba).trans (Framed.wr_prev (by simp) haa)

/-- `remove` is `xs.erase t`, for a member `t`; it clears `t`'s links. -/
theorem tcbqueue.remove.rel (s : S) (l : tcbqueue.Link) (q : tcbqueue.Queue) (t : obj.Tcb)
    (xs : List U64) (hT : TcbPlaced T) (h : QueueRel (L.mem s) T l q xs) (ht : t ∈ xs) :
    tcbqueue.remove st s l q t ⦃ q' s' =>
      QueueRel (L.mem s') T l q' (xs.erase t) ∧ Framed st l xs s s' ∧
      L.mem s' (nextA l t) = 0#u64 ∧ L.mem s' (prevA l t) = 0#u64 ⦄ := by
  refine WP.spec_mono (tcbqueue.remove.eq s l q t) ?_
  rintro ⟨q', s'⟩ he
  have hr := removeF_rel (st := st) hT h ht
  simp only [WP.uncurry'] at he ⊢
  rw [← he] at hr; exact hr
/-- `prepend` is `t :: xs`. -/
theorem tcbqueue.prepend.rel (s : S) (l : tcbqueue.Link) (q : tcbqueue.Queue) (t : obj.Tcb)
    (xs : List U64) (hT : TcbPlaced T) (h : QueueRel (L.mem s) T l q xs) (ht : t ∈ T) (hn : t ∉ xs) :
    tcbqueue.prepend st s l q t ⦃ q' s' =>
      QueueRel (L.mem s') T l q' (t :: xs) ∧ Framed st l (t :: xs) s s' ⦄ := by
  have hta : TcbAddr t := hT t ht
  unfold tcbqueue.prepend
  step*
  · subst_vars
    obtain ⟨rfl, h1, h2⟩ := h.single hT ht (by simpa using ‹decide (q.head = 0#u64) = true›)
    exact ⟨h1, h2.mono (by simp)⟩
  · subst_vars
    have hne : xs ≠ [] := by
      rw [Ne, ← h.empty_iff hT]; simpa using ‹¬decide (q.head = 0#u64) = true›
    obtain ⟨a, zs, rfl⟩ := List.exists_cons_of_ne_nil hne
    have hqa : q.head = a := by rw [h.head]; rfl
    rw [hqa]
    have haa : TcbAddr a := h.addr hT a (by simp)
    have hta' : t ≠ a := fun e => hn (by simp [e])
    have := hta'.symm
    have old := h.seg
    simp only [Seg_cons] at old
    refine ⟨⟨List.nodup_cons.2 ⟨hn, h.nodup⟩, ?_, rfl, ?_, ?_⟩, ?_⟩
    · intro x hx; simp only [List.mem_cons] at hx; rcases hx with rfl | hx
      · exact ht
      · exact h.mem x (by simpa using hx)
    · rw [h.last, show t :: a :: zs = [t] ++ a :: zs from rfl, getLastD_append_of_ne _ (by simp)]
    · simp only [Seg_cons, List.headD_cons]
      refine ⟨by rdwr, by rdwr, by rw [← old.1]; rdwr, by rw [← old.2.1]; rdwr, Seg.congr ?_ old.2.2⟩
      intro x hx
      have hxa : TcbAddr x := h.addr hT x (by simp [hx])
      have : x ≠ a := fun e => (List.nodup_cons.1 h.nodup).1 (e ▸ hx)
      have : x ≠ t := fun e => hn (by simp [← e, hx])
      have := (‹x ≠ a›).symm; have := (‹x ≠ t›).symm
      constructor <;> rdwr
    · exact ((Framed.wr_next (by simp) hta).trans (Framed.wr_prev (by simp) hta)).trans
        (Framed.wr_prev (by simp) haa)

/-- Linking `t` between two neighbours `b` and `a`, as `insert_before` and
`insert_after` do (in different orders). -/
theorem QueueRel.insert_core {m m' : U64 → U64} {l q ys zs} {a b t : U64} (hT : TcbPlaced T)
    (h : QueueRel m T l q (ys ++ b :: a :: zs)) (ht : t ∈ T) (hn : t ∉ ys ++ b :: a :: zs)
    (h1 : m' (prevA l a) = t) (h2 : m' (nextA l t) = a) (h3 : m' (prevA l t) = b)
    (h4 : m' (nextA l b) = t) (h5 : m' (prevA l b) = m (prevA l b)) (h6 : m' (nextA l a) = m (nextA l a))
    (hf : LinkFrame l [t, a, b] m m') : QueueRel m' T l q (ys ++ b :: t :: a :: zs) := by
  have hta : TcbAddr t := hT t ht
  have haa : TcbAddr a := h.addr hT a (by simp)
  have hba : TcbAddr b := h.addr hT b (by simp)
  have hW : ∀ w ∈ [t, a, b], TcbAddr w := by simp [hta, haa, hba]
  have old := h.seg
  rw [Seg_mid] at old
  simp only [Seg_cons] at old
  obtain ⟨oY, ob1, ob2, oa1, oa2, oZ⟩ := old
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have e : ys ++ b :: t :: a :: zs = (ys ++ [b]) ++ t :: (a :: zs) := by simp
    rw [e, List.nodup_middle, List.nodup_cons]
    exact ⟨by simpa using hn, by simpa using h.nodup⟩
  · intro x hx
    simp only [List.mem_append, List.mem_cons] at hx
    rcases hx with hx | rfl | rfl | rfl | hx
    · exact h.mem x (by simp [hx])
    · exact h.mem _ (by simp)
    · exact ht
    · exact h.mem _ (by simp)
    · exact h.mem x (by simp [hx])
  · rw [h.head]; cases ys <;> rfl
  · rw [h.last, show ys ++ b :: a :: zs = (ys ++ [b]) ++ a :: zs by simp,
      show ys ++ b :: t :: a :: zs = (ys ++ [b, t]) ++ a :: zs by simp,
      getLastD_append_of_ne _ (by simp), getLastD_append_of_ne _ (by simp)]
  · rw [Seg_mid]
    simp only [Seg_cons]
    refine ⟨Seg.congr ?_ oY, h5.trans ob1, h4, h3, h2, h1, h6.trans oa2, Seg.congr ?_ oZ⟩
    · intro x hx
      have hxa : TcbAddr x := h.addr hT x (by simp [hx])
      have hxW : x ∉ [t, a, b] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨fun e => hn (by simp [← e, hx]),
          ne_of_nodup_append h.nodup hx (by simp), ne_of_nodup_append h.nodup hx (by simp)⟩
      exact ⟨hf.prev_eq hW hxa (fun _ => hxW), hf.next_eq hW hxa (fun _ => hxW)⟩
    · intro x hx
      have hxa : TcbAddr x := h.addr hT x (by simp [hx])
      have hn' : (ys ++ [b, a] ++ zs).Nodup := by simpa using h.nodup
      have hxW : x ∉ [t, a, b] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨fun e => hn (by simp [← e, hx]),
          (ne_of_nodup_append hn' (by simp) hx).symm, (ne_of_nodup_append hn' (by simp) hx).symm⟩
      exact ⟨hf.prev_eq hW hxa (fun _ => hxW), hf.next_eq hW hxa (fun _ => hxW)⟩

/-- `insert_before t a`, for a member `a` that is not the head, is inserting
`t` just before `a`. -/
theorem tcbqueue.insert_before.rel (s : S) (l : tcbqueue.Link) (q : tcbqueue.Queue) (t a : obj.Tcb)
    (ys zs : List U64) (hT : TcbPlaced T) (h : QueueRel (L.mem s) T l q (ys ++ a :: zs))
    (hys : ys ≠ []) (ht : t ∈ T) (hn : t ∉ ys ++ a :: zs) :
    tcbqueue.insert_before st s l t a ⦃ s' =>
      QueueRel (L.mem s') T l q (ys ++ t :: a :: zs) ∧ Framed st l (t :: (ys ++ a :: zs)) s s' ⦄ := by
  obtain ⟨ys', b, rfl⟩ := (eq_nil_or_snoc ys).resolve_left hys
  have hta : TcbAddr t := hT t ht
  have haa : TcbAddr a := h.addr hT a (by simp)
  have hba : TcbAddr b := h.addr hT b (by simp)
  have hab : a ≠ b :=
    (ne_of_nodup_append (l1 := ys' ++ [b]) (l2 := a :: zs) h.nodup (by simp) (by simp)).symm
  have htb : t ≠ b := fun e => hn (by simp [e])
  have hta' : t ≠ a := fun e => hn (by simp [e])
  have := hab.symm; have := htb.symm; have := hta'.symm
  have h' : QueueRel (L.mem s) T l q (ys' ++ b :: a :: zs) := by simpa using h
  unfold tcbqueue.insert_before
  step*
  subst_vars
  have hb : L.mem s (prevA l a) = b := by
    have := h.seg; rw [Seg_mid] at this; simpa using this.2.1
  rw [hb]
  refine ⟨?_, ?_⟩
  · have := h'.insert_core (m' := L.mem (L.wr (L.wr (L.wr (L.wr s (prevA l a) t) (nextA l t) a)
      (prevA l t) b) (nextA l b) t)) hT ht (by simpa using hn) (by rdwr) (by rdwr) (by rdwr) (by rdwr)
      (by rdwr) (by rdwr)
      (((((Framed.wr_prev (by simp) haa).trans (Framed.wr_next (by simp) hta)).trans
        (Framed.wr_prev (by simp) hta)).trans (Framed.wr_next (by simp) hba)).2.2)
    simpa using this
  · exact ((((Framed.wr_prev (by simp) haa).trans (Framed.wr_next (by simp) hta)).trans
        (Framed.wr_prev (by simp) hta)).trans (Framed.wr_next (by simp) hba))

/-- `insert_after t b`, for a member `b` that is not the end, is inserting
`t` just after `b`. -/
theorem tcbqueue.insert_after.rel (s : S) (l : tcbqueue.Link) (q : tcbqueue.Queue) (t b : obj.Tcb)
    (ys zs : List U64) (hT : TcbPlaced T) (h : QueueRel (L.mem s) T l q (ys ++ b :: zs))
    (hzs : zs ≠ []) (ht : t ∈ T) (hn : t ∉ ys ++ b :: zs) :
    tcbqueue.insert_after st s l t b ⦃ s' =>
      QueueRel (L.mem s') T l q (ys ++ b :: t :: zs) ∧ Framed st l (t :: (ys ++ b :: zs)) s s' ⦄ := by
  obtain ⟨a, zs', rfl⟩ := List.exists_cons_of_ne_nil hzs
  have hta : TcbAddr t := hT t ht
  have haa : TcbAddr a := h.addr hT a (by simp)
  have hba : TcbAddr b := h.addr hT b (by simp)
  have hab : a ≠ b :=
    (ne_of_nodup_append (l1 := ys ++ [b]) (l2 := a :: zs') (by simpa using h.nodup) (by simp) (by simp)).symm
  have htb : t ≠ b := fun e => hn (by simp [e])
  have hta' : t ≠ a := fun e => hn (by simp [e])
  have := hab.symm; have := htb.symm; have := hta'.symm
  unfold tcbqueue.insert_after
  step*
  subst_vars
  have ha : L.mem s (nextA l b) = a := by
    have := h.seg; rw [Seg_mid] at this; simpa using this.2.2.1
  rw [ha]
  have hf := (((Framed.wr_prev (st := st) (l := l) (W := [t, a, b]) (s := s) (v := b) (by simp) hta).trans
    (Framed.wr_next (v := a) (by simp) hta)).trans (Framed.wr_prev (v := t) (by simp) haa)).trans
    (Framed.wr_next (v := t) (by simp) hba)
  refine ⟨h.insert_core hT ht hn (by rdwr) (by rdwr) (by rdwr) (by rdwr) (by rdwr) (by rdwr) hf.2.2,
    hf.mono (by intro x hx; simp at hx ⊢; tauto)⟩
/-- The frame lemma on states: a queue of another link kind, or of TCBs
outside `W`, is unaffected by a primitive that wrote the `l` links of `W`. -/
theorem QueueRel.framed {s s' : S} {l l' q ys W} (hT : TcbPlaced T) (hW : ∀ w ∈ W, w ∈ T)
    (hf : Framed st l W s s') (hd : l' = l → ∀ y ∈ ys, y ∉ W)
    (h : QueueRel (L.mem s) T l' q ys) : QueueRel (L.mem s') T l' q ys :=
  h.frame hT (fun w hw => hT w (hW w hw)) hf.2.2 hd
end

end Fl4Proofs.P1
