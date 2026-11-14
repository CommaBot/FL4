/-
P1: reply objects and scheduling contexts as placed, disjoint objects, and
the invariants about them that `schedule`, `cancel_ipc`, `suspend` and
`restart` rely on:

* `ObjsOK`: reply objects (32 bytes, aligned) and SCs (`2 ^ Z c` bytes,
  `Placed`) are pairwise disjoint and lie among the other objects' words
  `Ω`; the reply words and the SCs' `CORE`/`TCB` words are frame words `Sg`.
* `ReplyInv` (l4v reply invariants): a thread blocked on reply has a reply
  object whose `TCB` word names it; so has a receiver with a reply object;
  the `next` link of a reply is an SC (head bit set) or a reply, its `prev`
  link a reply.
* `ScExtra` (l4v `sc_tcb_sc_at`, `valid_objs`): a bound TCB's SC is an SC
  object whose `TCB` word names it back and whose `CORE` word is a core; the
  current SC is an SC object.
-/
import Fl4Proofs.P1.QueueCancel
import Fl4Proofs.P1.QueueSchedStep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

/-- A timer link: null or a TCB. -/
def Tz (T : Set U64) (x : U64) : Prop := x = 0#u64 ∨ x ∈ T

theorem Tz.zero {T : Set U64} : Tz T 0#u64 := Or.inl rfl
theorem Tz.of_mem {T : Set U64} {x : U64} (h : x ∈ T) : Tz T x := Or.inr h


section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}

theorem Tz.ne0 {T : Set U64} {x : U64} (hx : Tz T x) (h0 : x ≠ 0#u64) : x ∈ T := hx.resolve_left h0

/-- The timer-tree typing invariant. -/
structure TimerOK (st : machine.Store S) [L : LawfulStore st] (T Cs : Set U64) (s : S) : Prop where
  /-- The cores' nodes are placed (what reading their timer-tree words needs). -/
  npl : ∀ c ∈ Cs, NodePlaced st T s c
  lt : ∀ y ∈ T, Tz T (L.mem s (tlA y))
  rt : ∀ y ∈ T, Tz T (L.mem s (trA y))
  pt : ∀ y ∈ T, Tz T (L.mem s (tpA y))
  root : ∀ c ∈ Cs, Tz T (L.mem s (L.nodeAt s c layout.node.TIMER_ROOT))
  min : ∀ c ∈ Cs, Tz T (L.mem s (L.nodeAt s c layout.node.TIMER_MIN))
  core : ∀ y ∈ T, L.mem s (tdA y) ≠ 0#u64 → ∀ c : U64, c.val = (L.mem s (thA y)).val >>> 8 → c ∈ Cs
  /-- The debug lists are typed: each TCB's debug links and each core's list head are null or TCBs. -/
  dn : ∀ y ∈ T, Tz T (L.mem s (dnA y))
  dp : ∀ y ∈ T, Tz T (L.mem s (dpA y))
  dh : ∀ c ∈ Cs, Tz T (L.mem s (L.nodeAt s c layout.node.DEBUG_TCBS))

/-- A notification's bound TCB is null or a TCB (l4v `valid_ntfn`, the
`ntfn_bound_tcb` part). -/
def NtbOK (st : machine.Store S) [L : LawfulStore st] (T Nt : Set U64) (s : S) : Prop :=
  ∀ n ∈ Nt, Tz T (L.mem s (ntfnBtA n))

theorem timer_root_val : layout.node.TIMER_ROOT.val = 104 := by simp [layout.node.TIMER_ROOT]
theorem timer_min_val : layout.node.TIMER_MIN.val = 112 := by simp [layout.node.TIMER_MIN]
theorem debug_val : layout.node.DEBUG_TCBS.val = 88 := by simp [layout.node.DEBUG_TCBS]

theorem ntfnBt_aligned {n : U64} (h : n.val % 64 = 0 ∧ n.val + 64 ≤ 2 ^ 64) : Aligned (ntfnBtA n) := by
  unfold Aligned; rw [ntfnBtA_val h]; omega

/-! ## Frames of the timer words -/

/-- An operation that leaves the timer-tree words alone: the TCBs' timer
fields, the nodes' timer-tree words and the notifications' `BOUND_TCB`
words. -/
def TmFr (st : machine.Store S) [L : LawfulStore st] (T Cs Nt : Set U64) (s s' : S) : Prop :=
  L.ksb s' = L.ksb s ∧
  (∀ y ∈ T, ∀ K : U64, 3528 ≤ K.val → K.val < 3592 → K.val % 8 = 0 →
    L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
  (∀ c ∈ Cs, ∀ o : U64, (o.val = 88 ∨ o.val = 104 ∨ o.val = 112) → L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o)) ∧
  (∀ n ∈ Nt, L.mem s' (ntfnBtA n) = L.mem s (ntfnBtA n))

theorem TmFr.refl (s : S) : TmFr st T Cs Nt s s :=
  ⟨rfl, fun _ _ _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ => rfl⟩

theorem TmFr.trans {s₁ s₂ s₃ : S} (h₁ : TmFr st T Cs Nt s₁ s₂) (h₂ : TmFr st T Cs Nt s₂ s₃) :
    TmFr st T Cs Nt s₁ s₃ :=
  ⟨h₂.1.trans h₁.1, fun y hy K a b c => (h₂.2.1 y hy K a b c).trans (h₁.2.1 y hy K a b c),
    fun c hc o ho => by
      have e := h₂.2.2.1 c hc o ho
      rw [nodeAt_of_ksb h₁.1] at e
      exact e.trans (h₁.2.2.1 c hc o ho),
    fun n hn => (h₂.2.2.2 n hn).trans (h₁.2.2.2 n hn)⟩

theorem TmFr.of_keepT {t : U64} {s s' : S} (k : KeepT st T Cs Rp Scs Nt t s s') : TmFr st T Cs Nt s s' :=
  ⟨k.ksb, fun y hy K h1 h2 h3 => k.fld y hy K (by omega) h3 (by omega) (by omega) (fun _ => ⟨by omega, by omega⟩),
    k.tnd, k.ntb⟩

theorem TmFr.of_fr {s s' : S} (f : Fr st T Sg s s') (hO : ObjsOK st Ω Sg Rp Scs Nt Z s)
    (hN : ∀ c ∈ Cs, NodePlaced st T s c) : TmFr st T Cs Nt s s' := by
  exact ⟨f.ksb, f.tmr,
    fun c hc o ho => f.tnd c (hN c hc) o ho, fun n hn => f.sig _ (hO.ntB n hn).2⟩

/-- The timer-tree words. -/
def TmW (st : machine.Store S) [L : LawfulStore st] (T Cs Nt : Set U64) (s : S) (b : U64) : Prop :=
  (∃ y ∈ T, ∃ K : U64, 3528 ≤ K.val ∧ K.val < 3592 ∧ K.val % 8 = 0 ∧ b = core.num.U64.wrapping_add y K) ∨
  (∃ c ∈ Cs, ∃ o : U64, (o.val = 88 ∨ o.val = 104 ∨ o.val = 112) ∧ b = L.nodeAt s c o) ∨ (∃ n ∈ Nt, b = ntfnBtA n)

/-- Writes that avoid the timer-tree words keep them. -/
theorem TmFr.of_writes {s s' : S} {B : U64 → Prop} (hT : TcbPlaced T) (hN : ∀ c ∈ Cs, NodePlaced st T s c)
    (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hw : WritesIn st s s' B) (hB : ∀ b, B b → ¬ TmW st T Cs Nt s b) :
    TmFr st T Cs Nt s s' :=
  ⟨hw.1, fun y hy K h1 h2 h3 => hw.mem_eq (field_aligned (hT y hy) (by omega) h3)
      (fun hb => hB _ hb (Or.inl ⟨y, hy, K, h1, h2, h3, rfl⟩)),
    fun c hc o ho => hw.mem_eq (nodeAt_aligned (hN c hc) (by omega) (by omega))
      (fun hb => hB _ hb (Or.inr (Or.inl ⟨c, hc, o, ho, rfl⟩))),
    fun n hn => hw.mem_eq (ntfnBt_aligned (hO.ntP n hn)) (fun hb => hB _ hb (Or.inr (Or.inr ⟨n, hn, rfl⟩)))⟩

/-- A TCB field at an offset outside the timer fields is no timer-tree word. -/
theorem notTmW_field {s : S} {y K : U64} (hT : TcbPlaced T) (hN : ∀ c ∈ Cs, NodePlaced st T s c)
    (hΩ : ∀ n ∈ Nt, OutsideObjs st T Cs s (ntfnBtA n)) (hy : y ∈ T) (hK : K.val < 4096)
    (hK' : K.val < 3528 ∨ 3592 ≤ K.val) : ¬ TmW st T Cs Nt s (core.num.U64.wrapping_add y K) := by
  rintro (⟨y', hy', K', h1, h2, h3, e⟩ | ⟨c, hc, o, ho, e⟩ | ⟨n, hn, e⟩)
  · exact field_ne (hT y hy) (hT y' hy') hK (by omega) (fun _ => by omega) e
  · exact node_ne_field (hN c hc) (by omega) hy (hT y hy) hK e.symm
  · exact out_ne_field (hΩ n hn) hy (hT y hy) hK (congrArg UScalar.val e)


theorem TmFr.wr {s : S} {a v : U64} (hT : TcbPlaced T) (hN : ∀ c ∈ Cs, NodePlaced st T s c)
    (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (ha : Aligned a) (hna : ¬ TmW st T Cs Nt s a) :
    TmFr st T Cs Nt s (L.wr s a v) :=
  TmFr.of_writes hT hN hO (writesIn_wr ha) (fun b hb => by subst hb; exact hna)

/-- A word of another object that is no notification `BOUND_TCB` word is no
timer-tree word. -/
theorem notTmW_omega {s : S} {b : U64} (hT : TcbPlaced T) (hN : ∀ c ∈ Cs, NodePlaced st T s c)
    (hb : OutsideObjs st T Cs s b) (hnb : ∀ n ∈ Nt, b.val ≠ (ntfnBtA n).val) :
    ¬ TmW st T Cs Nt s b := by
  rintro (⟨y, hy, K, h1, h2, h3, e⟩ | ⟨c, hc, o, ho, e⟩ | ⟨n, hn, e⟩)
  · exact out_ne_field hb hy (hT y hy) (by omega) (congrArg UScalar.val e).symm
  · exact out_ne_node hb hc (hN c hc) (by omega) (congrArg UScalar.val e).symm
  · exact hnb n hn (congrArg UScalar.val e)

/-- A node word other than the timer-tree words is no timer-tree word. -/
theorem notTmW_node {s : S} {c o : U64} (hT : TcbPlaced T) (hN : ∀ c ∈ Cs, NodePlaced st T s c)
    (hΩ : ∀ n ∈ Nt, OutsideObjs st T Cs s (ntfnBtA n)) (hc : c ∈ Cs) (ho : o.val < 4288)
    (hto : o.val ≠ 88 ∧ o.val ≠ 104 ∧ o.val ≠ 112) : ¬ TmW st T Cs Nt s (L.nodeAt s c o) := by
  rintro (⟨y, hy, K, h1, h2, h3, e⟩ | ⟨c', hc', o', ho', e⟩ | ⟨n, hn, e⟩)
  · exact node_ne_field (hN c hc) ho hy (hT y hy) (by omega) e
  · exact node_ne_node (hN c hc) (hN c' hc') ho (by omega) (fun _ => by omega) (congrArg UScalar.val e)
  · exact out_ne_node (hΩ n hn) hc (hN c hc) ho (congrArg UScalar.val e)


theorem TimerOK.tmfr {s s' : S} (h : TimerOK st T Cs s) (f : TmFr st T Cs Nt s s') : TimerOK st T Cs s' := by
  obtain ⟨fk, ft, fd, -⟩ := f
  have lk : ∀ y K, y ∈ T → K.val = 3544 ∨ K.val = 3552 ∨ K.val = 3560 →
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y K hy hK => ft y hy K (by omega) (by omega) (by omega)
  refine ⟨fun c hc => (h.npl c hc).ksb fk, fun y hy => ?_, fun y hy => ?_, fun y hy => ?_, fun c hc => ?_,
    fun c hc => ?_, fun y hy hd c hcv => ?_,
    fun y hy => by rw [show dnA y = core.num.U64.wrapping_add y 3576#u64 from rfl,
      ft y hy _ (by simp) (by simp) (by simp)]; exact h.dn y hy,
    fun y hy => by rw [show dpA y = core.num.U64.wrapping_add y 3584#u64 from rfl,
      ft y hy _ (by simp) (by simp) (by simp)]; exact h.dp y hy,
    fun c hc => by rw [nodeAt_of_ksb fk, fd c hc _ (by rw [debug_val]; simp)]; exact h.dh c hc⟩
  · rw [show tlA y = core.num.U64.wrapping_add y 3544#u64 from rfl, lk y _ hy (by simp)]; exact h.lt y hy
  · rw [show trA y = core.num.U64.wrapping_add y 3552#u64 from rfl, lk y _ hy (by simp)]; exact h.rt y hy
  · rw [show tpA y = core.num.U64.wrapping_add y 3560#u64 from rfl, lk y _ hy (by simp)]; exact h.pt y hy
  · rw [nodeAt_of_ksb fk, fd c hc _ (by rw [timer_root_val]; simp)]; exact h.root c hc
  · rw [nodeAt_of_ksb fk, fd c hc _ (by rw [timer_min_val]; simp)]; exact h.min c hc
  · rw [show tdA y = core.num.U64.wrapping_add y 3528#u64 from rfl, ft y hy _ (by simp) (by simp) (by simp)] at hd
    rw [show thA y = core.num.U64.wrapping_add y 3568#u64 from rfl, ft y hy _ (by simp) (by simp) (by simp)] at hcv
    exact h.core y hy hd c hcv

theorem NtbOK.tmfr {s s' : S} (h : NtbOK st T Nt s) (f : TmFr st T Cs Nt s s') : NtbOK st T Nt s' :=
  fun n hn => by rw [f.2.2.2 n hn]; exact h n hn

/-- A write of a word of another object keeps `TimerOK`. -/
theorem TimerOK.wr_out {s : S} {a v : U64} (h : TimerOK st T Cs s) (hT : TcbPlaced T)
    (hN : ∀ c ∈ Cs, NodePlaced st T s c) (ho : OutsideObjs st T Cs s a) : TimerOK st T Cs (L.wr s a v) :=
  h.tmfr (Nt := ∅) ⟨L.ksb_wr _ _ _,
    fun y hy K h1 h2 h3 => L.mem_wr_ne ho.1 (field_aligned (hT y hy) (by omega) h3)
      (fun e => out_ne_field ho hy (hT y hy) (by omega) e.symm),
    fun c hc o hoo => L.mem_wr_ne ho.1 (nodeAt_aligned (hN c hc) (by omega) (by omega))
      (fun e => out_ne_node ho hc (hN c hc) (by omega) e.symm),
    fun n hn => absurd hn (Set.notMem_empty n)⟩

/-- A write that puts a null or a TCB into any `BOUND_TCB` word it hits keeps `NtbOK`. -/
theorem NtbOK.wr_tz {s : S} {a v : U64} (h : NtbOK st T Nt s) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (ha : Aligned a)
    (hv : ∀ n ∈ Nt, a.val = (ntfnBtA n).val → Tz T v) : NtbOK st T Nt (L.wr s a v) := fun n hn => by
  rw [L.mem_wr_val ha (ntfnBt_aligned (hO.ntP n hn))]
  split
  · exact hv n hn ‹_›
  · exact h n hn


end

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}


/-- The reply invariants. -/
structure ReplyInv (st : machine.Store S) [L : LawfulStore st] (T Rp Scs : Set U64) (s : S) : Prop where
  reply : ∀ t ∈ T, L.mem s (stA t) = sched.TS_BLOCKED_ON_REPLY →
    L.mem s (replyA t) ∈ Rp ∧ L.mem s (rTcbA (L.mem s (replyA t))) = t
  recv : ∀ t ∈ T, L.mem s (stA t) = sched.TS_BLOCKED_ON_RECV → L.mem s (replyA t) ≠ 0#u64 →
    L.mem s (replyA t) ∈ Rp ∧ L.mem s (rTcbA (L.mem s (replyA t))) = t
  next : ∀ r ∈ Rp, L.mem s (rNextA r) &&& ~~~1#u64 ≠ 0#u64 →
    (headBit (L.mem s (rNextA r)) = true → L.mem s (rNextA r) &&& ~~~1#u64 ∈ Scs) ∧
    (headBit (L.mem s (rNextA r)) = false → L.mem s (rNextA r) &&& ~~~1#u64 ∈ Rp)
  prev : ∀ r ∈ Rp, L.mem s (rPrevA r) &&& ~~~1#u64 ≠ 0#u64 → L.mem s (rPrevA r) &&& ~~~1#u64 ∈ Rp
  /-- A reply naming a thread is that thread's reply object, and the thread
  is blocked on reply or on receive (l4v `sym_refs` for reply/TCB). -/
  back : ∀ r ∈ Rp, L.mem s (rTcbA r) ≠ 0#u64 → r ≠ 0#u64 ∧ L.mem s (rTcbA r) ∈ T ∧
    L.mem s (replyA (L.mem s (rTcbA r))) = r ∧
    (L.mem s (stA (L.mem s (rTcbA r))) = sched.TS_BLOCKED_ON_REPLY ∨
      L.mem s (stA (L.mem s (rTcbA r))) = sched.TS_BLOCKED_ON_RECV)
  /-- An SC's `REPLY` word is unused or a reply object (l4v `valid_sched_context`). -/
  screp : ∀ c ∈ Scs, L.mem s (scReplyA c) ≠ 0#u64 → L.mem s (scReplyA c) ∈ Rp

/-- The SCs' `TCB` and `YIELD_FROM` words name TCBs (or nothing) and the TCBs'
`YIELD_TO` words name SCs (or nothing): the typing part of l4v's
`valid_sched_context` / `valid_tcb` and `sym_refs` for these links. -/
def YT (st : machine.Store S) [L : LawfulStore st] (T Scs : Set U64) (s : S) : Prop :=
  (∀ c ∈ Scs, L.mem s (scTcbA c) ≠ 0#u64 → L.mem s (scTcbA c) ∈ T) ∧
  (∀ t ∈ T, L.mem s (yieldA t) ≠ 0#u64 → L.mem s (yieldA t) ∈ Scs) ∧
  (∀ c ∈ Scs, L.mem s (scYieldFromA c) ≠ 0#u64 → L.mem s (scYieldFromA c) ∈ T)

theorem YT.keep {s s' : S} (h : YT st T Scs s) (hfx : ∀ c ∈ Scs, L.mem s' (scTcbA c) = L.mem s (scTcbA c))
    (hyl : ∀ t ∈ T, L.mem s' (yieldA t) = L.mem s (yieldA t))
    (hyf : ∀ c ∈ Scs, L.mem s' (scYieldFromA c) = L.mem s (scYieldFromA c)) : YT st T Scs s' :=
  ⟨fun c hc => by rw [hfx c hc]; exact h.1 c hc, fun t ht => by rw [hyl t ht]; exact h.2.1 t ht,
    fun c hc => by rw [hyf c hc]; exact h.2.2 c hc⟩

/-- Bound SCs are SC objects naming their thread and a core. -/
structure ScExtra (st : machine.Store S) [L : LawfulStore st] (T Cs Scs Nt : Set U64) (s : S) : Prop where
  bound : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 →
    L.mem s (scA t) ∈ Scs ∧ L.mem s (scTcbA (L.mem s (scA t))) = t ∧ L.mem s (scCoreA (L.mem s (scA t))) ∈ Cs
  cur : L.cscW s ∈ Scs
  /-- Every SC's `CORE` word names a core. -/
  core : ∀ c ∈ Scs, L.mem s (scCoreA c) ∈ Cs
  /-- A TCB's bound notification is a notification object (l4v `bound_tcb_at`/`valid_tcb`). -/
  bnd : ∀ t ∈ T, L.mem s (boundA t) ≠ 0#u64 → L.mem s (boundA t) ∈ Nt
  /-- A notification's SC is an SC object (l4v `valid_ntfn`). -/
  nsc : ∀ n ∈ Nt, L.mem s (ntfnScA n) ≠ 0#u64 → L.mem s (ntfnScA n) ∈ Scs
  /-- The timer trees are typed. -/
  tm : TimerOK st T Cs s
  /-- A notification's bound TCB is null or a TCB. -/
  ntb : NtbOK st T Nt s
  /-- An SC's bound notification is null or a notification (l4v `valid_sched_context`, `sc_ntfn`). -/
  scn : ∀ c ∈ Scs, L.mem s (scNtfnA c) ≠ 0#u64 → L.mem s (scNtfnA c) ∈ Nt
  /-- The SC/TCB and yield links are typed. -/
  yt : YT st T Scs s

/-- The object invariants together. -/
def XInv (st : machine.Store S) [L : LawfulStore st] (T Cs Ω Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (s : S) : Prop :=
  ObjsOK st Ω Sg Rp Scs Nt Z s ∧ ReplyInv st T Rp Scs s ∧ ScExtra st T Cs Scs Nt s

/-! ## Under a frame -/

/-- `XInv` only reads the reply words, the SCs' `TCB`/`CORE` words, the TCBs'
reply, state and SC fields, and the current SC. -/
theorem XInv.keep' {s s' : S} (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hrw : ∀ r ∈ Rp, L.mem s' (rTcbA r) = L.mem s (rTcbA r) ∧ L.mem s' (rPrevA r) = L.mem s (rPrevA r) ∧
      L.mem s' (rNextA r) = L.mem s (rNextA r))
    (hfx : ∀ c ∈ Scs, L.mem s' (scTcbA c) = L.mem s (scTcbA c) ∧ L.mem s' (scCoreA c) = L.mem s (scCoreA c))
    (hsc : ∀ t ∈ T, L.mem s' (scA t) = L.mem s (scA t))
    (hrep : ∀ t ∈ T, L.mem s' (replyA t) = L.mem s (replyA t))
    (hst : ∀ t ∈ T, L.mem s' (stA t) = L.mem s (stA t))
    (hcs : L.cscW s' ∈ Scs)
    (hsr : ∀ c ∈ Scs, L.mem s' (scReplyA c) = L.mem s (scReplyA c))
    (hbd : ∀ t ∈ T, L.mem s' (boundA t) ≠ 0#u64 → L.mem s' (boundA t) ∈ Nt)
    (hns : ∀ n ∈ Nt, L.mem s' (ntfnScA n) = L.mem s (ntfnScA n))
    (htn : TimerOK st T Cs s' ∧ NtbOK st T Nt s')
    (hsn : ∀ c ∈ Scs, L.mem s' (scNtfnA c) ≠ 0#u64 → L.mem s' (scNtfnA c) ∈ Nt)
    (hyt : YT st T Scs s') :
    XInv st T Cs Ω Sg Rp Scs Nt Z s' := by
  obtain ⟨hO, hR, hE⟩ := hX
  refine ⟨hO.ksb, ⟨fun t ht hs => ?_, fun t ht hs hn => ?_, fun r hr => ?_, fun r hr => ?_, fun r hr hn => ?_,
      fun c hc => by rw [hsr c hc]; exact hR.screp c hc⟩,
    ⟨fun t ht hb => ?_, hcs, fun c hc => by rw [(hfx c hc).2]; exact hE.core c hc,
      hbd, fun n hn => by rw [hns n hn]; exact hE.nsc n hn,
      htn.1, htn.2, hsn, hyt⟩⟩
  rotate_left 4
  · rw [(hrw r hr).1] at hn ⊢
    obtain ⟨b0, b1, b2, b3⟩ := hR.back r hr hn
    rw [hrep _ b1, hst _ b1]; exact ⟨b0, b1, b2, b3⟩
  rotate_right 4
  · rw [hst t ht] at hs
    obtain ⟨h1, h2⟩ := hR.reply t ht hs
    rw [hrep t ht, (hrw _ h1).1]; exact ⟨h1, h2⟩
  · rw [hst t ht] at hs; rw [hrep t ht] at hn ⊢
    obtain ⟨h1, h2⟩ := hR.recv t ht hs hn
    rw [(hrw _ h1).1]; exact ⟨h1, h2⟩
  · rw [(hrw r hr).2.2]; exact hR.next r hr
  · rw [(hrw r hr).2.1]; exact hR.prev r hr
  · rw [hsc t ht] at hb ⊢
    obtain ⟨h1, h2, h3⟩ := hE.bound t ht hb
    rw [(hfx _ h1).1, (hfx _ h1).2]; exact ⟨h1, h2, h3⟩

theorem XInv.keep {s s' : S} (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hrw : ∀ r ∈ Rp, L.mem s' (rTcbA r) = L.mem s (rTcbA r) ∧ L.mem s' (rPrevA r) = L.mem s (rPrevA r) ∧
      L.mem s' (rNextA r) = L.mem s (rNextA r))
    (hfx : ∀ c ∈ Scs, L.mem s' (scTcbA c) = L.mem s (scTcbA c) ∧ L.mem s' (scCoreA c) = L.mem s (scCoreA c))
    (hsc : ∀ t ∈ T, L.mem s' (scA t) = L.mem s (scA t))
    (hrep : ∀ t ∈ T, L.mem s' (replyA t) = L.mem s (replyA t))
    (hst : ∀ t ∈ T, L.mem s' (stA t) = L.mem s (stA t))
    (hcs : L.cscW s' ∈ Scs)
    (hsr : ∀ c ∈ Scs, L.mem s' (scReplyA c) = L.mem s (scReplyA c))
    (hbd : ∀ t ∈ T, L.mem s' (boundA t) = L.mem s (boundA t))
    (hns : ∀ n ∈ Nt, L.mem s' (ntfnScA n) = L.mem s (ntfnScA n))
    (htn : TimerOK st T Cs s' ∧ NtbOK st T Nt s')
    (hsn : ∀ c ∈ Scs, L.mem s' (scNtfnA c) = L.mem s (scNtfnA c))
    (hyl : ∀ t ∈ T, L.mem s' (yieldA t) = L.mem s (yieldA t))
    (hyf : ∀ c ∈ Scs, L.mem s' (scYieldFromA c) = L.mem s (scYieldFromA c)) : XInv st T Cs Ω Sg Rp Scs Nt Z s' :=
  hX.keep' hrw hfx hsc hrep hst hcs hsr (fun t ht => by rw [hbd t ht]; exact hX.2.2.bnd t ht) hns htn
    (fun c hc => by rw [hsn c hc]; exact hX.2.2.scn c hc) (hX.2.2.yt.keep (fun c hc => (hfx c hc).1) hyl hyf)

/-- The timer-tree typing and the notifications' bound TCBs after a frame. -/
theorem XInv.tn {s s' : S} (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (f : TmFr st T Cs Nt s s') :
    TimerOK st T Cs s' ∧ NtbOK st T Nt s' := ⟨hX.2.2.tm.tmfr f, hX.2.2.ntb.tmfr f⟩

theorem XInv.fr {s s' : S} (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (f : Fr st T Sg s s') :
    XInv st T Cs Ω Sg Rp Scs Nt Z s' :=
  hX.keep (fun r hr => ⟨f.sig _ (hX.1.tcbW hr), f.sig _ (hX.1.prevW hr), f.sig _ (hX.1.nextW hr)⟩)
    (fun c hc => ⟨f.sig _ (hX.1.fixW c hc).1, f.sig _ (hX.1.fixW c hc).2⟩) f.sc f.rep f.st
    (by rw [f.csc]; exact hX.2.2.cur) (fun c hc => f.sig _ (hX.1.repW c hc)) f.bnd
    (fun n hn => f.sig _ (hX.1.ntW n hn)) (hX.tn (TmFr.of_fr f hX.1 hX.2.2.tm.npl))
    (fun c hc => f.sig _ (hX.1.snW c hc)) f.yld (fun c hc => f.sig _ (hX.1.syW c hc))

/-! ## Writes that avoid the protected words -/

/-- The words `XInv` reads (besides the current SC). -/
def Prot (T Rp Scs Nt : Set U64) (b : U64) : Prop :=
  (∃ r ∈ Rp, b = rTcbA r ∨ b = rPrevA r ∨ b = rNextA r) ∨
  (∃ c ∈ Scs, b = scTcbA c ∨ b = scCoreA c ∨ b = scReplyA c ∨ b = scNtfnA c ∨ b = scYieldFromA c) ∨
  (∃ t ∈ T, b = scA t ∨ b = replyA t ∨ b = stA t ∨ b = boundA t ∨ b = yieldA t) ∨
  (∃ n ∈ Nt, b = ntfnScA n)

theorem ObjsOK.aligned (h : ObjsOK st Ω Sg Rp Scs Nt Z s) (hT : TcbPlaced T) {b : U64} (hb : Prot T Rp Scs Nt b) :
    Aligned b := by
  rcases hb with ⟨r, hr, e⟩ | ⟨c, hc, e⟩ | ⟨t, ht, e⟩ | ⟨n, hn, rfl⟩
  rotate_right
  · exact h.ntAl n hn
  · have hp := h.rp r hr
    rcases e with rfl | rfl | rfl <;> unfold Aligned
    · rw [rTcbA_val hp]; omega
    · rw [rPrevA_val hp]; omega
    · rw [rNextA_val hp]; omega
  · obtain ⟨hP, hz⟩ := h.sc c hc
    have := (sc_lo hP hz).1
    rcases e with rfl | rfl | rfl | rfl | rfl <;> unfold Aligned
    · rw [scTcbA_val hP hz]; omega
    · rw [scCoreA_val hP hz]; omega
    · rw [scReplyA_val hP hz]; omega
    · rw [scNtfnA_val hP hz]; omega
    · unfold scYieldFromA; rw [scYieldA_val hP hz]; omega
  · rcases e with rfl | rfl | rfl | rfl | rfl
    · exact scA_aligned (hT t ht)
    · exact field_aligned (hT t ht) (by simp) (by simp)
    · rw [stA_eq]; exact field_aligned (hT t ht) (by simp) (by simp)
    · exact field_aligned (hT t ht) (by simp) (by simp)
    · exact field_aligned (hT t ht) (by simp) (by simp)

/-- `XInv` after writes that avoid the protected words, given the new
current SC is an SC object. -/
theorem XInv.writes {s s' : S} {B : U64 → Prop} (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hT : TcbPlaced T)
    (hw : WritesIn st s s' B) (hB : ∀ b, B b → ¬ Prot T Rp Scs Nt b) (hcs : L.cscW s' ∈ Scs)
    (htn : TimerOK st T Cs s' ∧ NtbOK st T Nt s') :
    XInv st T Cs Ω Sg Rp Scs Nt Z s' := by
  have k : ∀ b, Prot T Rp Scs Nt b → L.mem s' b = L.mem s b := fun b hb =>
    hw.mem_eq (hX.1.aligned hT hb) (fun h => hB b h hb)
  exact hX.keep (fun r hr => ⟨k _ (Or.inl ⟨r, hr, Or.inl rfl⟩), k _ (Or.inl ⟨r, hr, Or.inr (Or.inl rfl)⟩),
      k _ (Or.inl ⟨r, hr, Or.inr (Or.inr rfl)⟩)⟩)
    (fun c hc => ⟨k _ (Or.inr (Or.inl ⟨c, hc, Or.inl rfl⟩)), k _ (Or.inr (Or.inl ⟨c, hc, Or.inr (Or.inl rfl)⟩))⟩)
    (fun t ht => k _ (Or.inr (Or.inr (Or.inl ⟨t, ht, Or.inl rfl⟩))))
    (fun t ht => k _ (Or.inr (Or.inr (Or.inl ⟨t, ht, Or.inr (Or.inl rfl)⟩))))
    (fun t ht => k _ (Or.inr (Or.inr (Or.inl ⟨t, ht, Or.inr (Or.inr (Or.inl rfl))⟩)))) hcs
    (fun c hc => k _ (Or.inr (Or.inl ⟨c, hc, Or.inr (Or.inr (Or.inl rfl))⟩)))
    (fun t ht => k _ (Or.inr (Or.inr (Or.inl ⟨t, ht, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩))))
    (fun n hn => k _ (Or.inr (Or.inr (Or.inr ⟨n, hn, rfl⟩)))) htn
    (fun c hc => k _ (Or.inr (Or.inl ⟨c, hc, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩)))
    (fun t ht => k _ (Or.inr (Or.inr (Or.inl ⟨t, ht, Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩))))
    (fun c hc => k _ (Or.inr (Or.inl ⟨c, hc, Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩)))

/-- Protected words are words of `Ω` or TCB fields. -/
theorem ObjsOK.prot_cases (h : ObjsOK st Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω) {b : U64}
    (hb : Prot T Rp Scs Nt b) : b ∈ Ω ∨ ∃ t ∈ T, ∃ K : U64, K.val < 4096 ∧ b = core.num.U64.wrapping_add t K := by
  rcases hb with ⟨r, hr, e⟩ | ⟨c, hc, e⟩ | ⟨t, ht, e⟩ | ⟨n, hn, rfl⟩
  rotate_right
  · exact Or.inl (hsub _ (h.ntW n hn))
  · left; rcases e with rfl | rfl | rfl
    · exact hsub _ (h.tcbW hr)
    · exact hsub _ (h.prevW hr)
    · exact hsub _ (h.nextW hr)
  · left; rcases e with rfl | rfl | rfl | rfl | rfl
    · exact hsub _ (h.fixW c hc).1
    · exact hsub _ (h.fixW c hc).2
    · exact hsub _ (h.repW c hc)
    · exact hsub _ (h.snW c hc)
    · exact hsub _ (h.syW c hc)
  · right; refine ⟨t, ht, ?_⟩
    rcases e with rfl | rfl | rfl | rfl | rfl
    · exact ⟨3464#u64, by simp, rfl⟩
    rotate_right
    · exact ⟨3472#u64, by simp, rfl⟩
    · exact ⟨3360#u64, by simp, rfl⟩
    · exact ⟨3328#u64, by simp, stA_eq t⟩
    · exact ⟨3368#u64, by simp, rfl⟩

/-- Node words are not protected. -/
theorem not_prot_node {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    {c o : U64} (hc : c ∈ Cs) (ho : o.val < 4288) : ¬ Prot T Rp Scs Nt (L.nodeAt s c o) := by
  intro hp
  rcases hO.prot_cases hsub hp with hm | ⟨t, ht, K, hK, e⟩
  · exact out_ne_node (h.omega _ hm) hc (h.nodes c hc) ho rfl
  · exact node_ne_field (h.nodes c hc) ho ht (h.tcbs t ht) hK e

/-- The ring and `CONSUMED` word of an SC object are not protected. -/
theorem not_prot_ring {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) {c b : U64} (hc : c ∈ Scs)
    (hb : Aligned b) (hr : InRing c (Z c) b ∨ b = core.num.U64.wrapping_add c layout.sc.CONSUMED) :
    ¬ Prot T Rp Scs Nt b := by
  obtain ⟨hP, hz⟩ := hO.sc c hc
  obtain ⟨-, h128, -⟩ := sc_lo hP hz
  have hbv : (c.val + 72 ≤ b.val ∨ b.val = c.val + 8) ∧ b.val < c.val + 2 ^ Z c := by
    rcases hr with ⟨h1, h2⟩ | rfl
    · exact ⟨Or.inl h1, h2⟩
    · rw [sc_word_val hP hz (by simp [layout.sc.CONSUMED])]; simp [layout.sc.CONSUMED]; omega
  have hin : InSC c (Z c) b := ⟨by omega, hbv.2⟩
  rintro (⟨r, hr', e⟩ | ⟨c', hc', e⟩ | ⟨t, ht, e⟩ | ⟨n, hn, rfl⟩)
  rotate_right
  · have := hO.ntSc n hn c hc; have := hin.1; have := hin.2; omega
  · have hp := hO.rp r hr'
    have hrv : b.val = r.val ∨ b.val = r.val + 8 ∨ b.val = r.val + 16 := by
      rcases e with rfl | rfl | rfl
      · exact Or.inl (rTcbA_val hp)
      · exact Or.inr (Or.inl (rPrevA_val hp))
      · exact Or.inr (Or.inr (rNextA_val hp))
    have := hO.rpSc r hr' c hc
    omega
  · obtain ⟨hP', hz'⟩ := hO.sc c' hc'
    obtain ⟨-, h128', -⟩ := sc_lo hP' hz'
    have hcv : b.val = c'.val + 24 ∨ b.val = c'.val + 16 ∨ b.val = c'.val + 32 ∨ b.val = c'.val + 40 ∨
        b.val = c'.val + 56 := by
      rcases e with rfl | rfl | rfl | rfl | rfl
      · exact Or.inl (scTcbA_val hP' hz')
      · exact Or.inr (Or.inl (scCoreA_val hP' hz'))
      · exact Or.inr (Or.inr (Or.inl (scReplyA_val hP' hz')))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (scNtfnA_val hP' hz'))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (scYieldA_val hP' hz'))))
    by_cases e' : c = c'
    · subst e'; omega
    · have := hO.scDisj c hc c' hc' e'; omega
  · have hm := hO.scW c hc b hb hin
    have hout := (h.omega _ hm).2.1 t ht
    have hv : b.val = t.val + 3464 ∨ b.val = t.val + 3360 ∨ b.val = t.val + 3328 ∨ b.val = t.val + 3368 ∨
        b.val = t.val + 3472 := by
      rcases e with rfl | rfl | rfl | rfl | rfl
      · left; rw [scA_eq, field_val (h.tcbs t ht) (by simp)]; simp
      · right; left; unfold replyA; rw [field_val (h.tcbs t ht) (by simp)]; simp
      · right; right; left; rw [stA_eq, field_val (h.tcbs t ht) (by simp)]; simp
      · right; right; right; left; unfold boundA; rw [field_val (h.tcbs t ht) (by simp)]; simp
      · right; right; right; right; unfold yieldA; rw [field_val (h.tcbs t ht) (by simp)]; simp
    omega

/-- A word of an SC object is no timer-tree word. -/
theorem notTmW_insc {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    {c b : U64} (hc : c ∈ Scs) (hb : Aligned b) (hin : InSC c (Z c) b) : ¬ TmW st T Cs Nt s b := by
  have hm := hO.scW c hc b hb hin
  refine notTmW_omega h.tcbs h.nodes (h.omega _ hm) (fun n hn e => ?_)
  rw [ntfnBtA_val (hO.ntP n hn)] at e
  have := hO.ntOSc n hn c hc; have := hin.1; have := hin.2; omega

/-- A ring word or the `CONSUMED` word of an SC is no timer-tree word. -/
theorem notTmW_ring {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    {c b : U64} (hc : c ∈ Scs) (hb : Aligned b)
    (hr : InRing c (Z c) b ∨ b = core.num.U64.wrapping_add c layout.sc.CONSUMED) : ¬ TmW st T Cs Nt s b := by
  obtain ⟨hP, hz⟩ := hO.sc c hc
  obtain ⟨-, h128, -⟩ := sc_lo hP hz
  have hin : InSC c (Z c) b := by
    rcases hr with ⟨h1, h2⟩ | rfl
    · exact ⟨by omega, h2⟩
    · rw [InSC, sc_word_val hP hz (by simp [layout.sc.CONSUMED])]; simp [layout.sc.CONSUMED]; omega
  exact notTmW_insc h hO hsub hc hb hin

/-- A write avoiding the timer-tree words keeps their typing. -/
theorem XInv.tn_wr {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {a v : U64}
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ha : Aligned a)
    (hna : ¬ TmW st T Cs Nt s a) : TimerOK st T Cs (L.wr s a v) ∧ NtbOK st T Nt (L.wr s a v) :=
  hX.tn (TmFr.wr h.tcbs h.nodes hX.1 ha hna)

/-- A node word other than the timer-tree words. -/
theorem XInv.tn_node {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {c o v : U64}
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (hc : c ∈ Cs) (ho : o.val < 4288) (h8 : o.val % 8 = 0) (hto : o.val ≠ 88 ∧ o.val ≠ 104 ∧ o.val ≠ 112) :
    TimerOK st T Cs (L.wr s (L.nodeAt s c o) v) ∧ NtbOK st T Nt (L.wr s (L.nodeAt s c o) v) :=
  hX.tn_wr h (nodeAt_aligned (h.nodes c hc) ho h8)
    (notTmW_node h.tcbs h.nodes (fun n hn => h.omega _ (hsub _ (hX.1.ntB n hn).2)) hc ho hto)

/-- A TCB field other than the timer fields. -/
theorem XInv.tn_field {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {y K v : U64}
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (hy : y ∈ T) (hK : K.val < 4096) (hK8 : K.val % 8 = 0) (hKt : K.val < 3528 ∨ 3592 ≤ K.val) :
    TimerOK st T Cs (L.wr s (core.num.U64.wrapping_add y K) v) ∧
      NtbOK st T Nt (L.wr s (core.num.U64.wrapping_add y K) v) :=
  hX.tn_wr h (field_aligned (h.tcbs y hy) hK hK8)
    (notTmW_field h.tcbs h.nodes (fun n hn => h.omega _ (hsub _ (hX.1.ntB n hn).2)) hy hK hKt)

/-- An `EpFoot` write leaves the timer-tree words alone. -/
theorem TmFr.of_epfoot {X : Set U64} {s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    {E : Set U64} {EQ : U64 → List U64} {e : U64} {W : List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hEW : EpsWit st T Cs Ω H X s E EQ) (he : e ∈ E)
    (hWT : ∀ w ∈ W, w ∈ T) (hw : WritesIn st s s' (EpFoot W e)) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s)
    (hsub : ∀ b ∈ Sg, b ∈ Ω) : TmFr st T Cs Nt s s' := by
  obtain ⟨kf, kΩ, -⟩ := epfoot_keep h hEW he hWT hw
  exact ⟨hw.1, fun y hy K a b c => kf y hy K (by omega) c (by omega) (by omega),
    fun c hc o ho => epfoot_nodes h hEW he hWT hw c hc o (by omega) (by omega),
    fun n hn => kΩ _ (hsub _ (hO.ntB n hn).2)⟩

/-- Writes avoiding the timer-tree words keep their typing. -/
theorem XInv.tn_writes {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {s' : S} {B : U64 → Prop}
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hw : WritesIn st s s' B)
    (hB : ∀ b, Aligned b → B b → ¬ TmW st T Cs Nt s b) : TimerOK st T Cs s' ∧ NtbOK st T Nt s' :=
  hX.tn (TmFr.of_writes h.tcbs h.nodes hX.1 (hw.mono' (B := fun b => Aligned b ∧ B b) fun b hb hh => ⟨hb, hh⟩)
    fun b hh => hB b hh.1 hh.2)

/-! ## Under `KeepT` (what `cancel_ipc` keeps) -/

theorem KeepT.curW {t : U64} {s s' : S} (k : KeepT st T Cs Rp Scs Nt t s s') : L.curW s' = L.curW s :=
  k.nd _ (by rw [curth0]; omega)
theorem KeepT.idleW {t : U64} {s s' : S} (k : KeepT st T Cs Rp Scs Nt t s s') : L.idleW s' = L.idleW s :=
  k.nd _ (by rw [idle8]; omega)
theorem KeepT.cscW {t : U64} {s s' : S} (k : KeepT st T Cs Rp Scs Nt t s s') : L.cscW s' = L.cscW s :=
  k.nd _ (by simp [layout.node.CUR_SC])
theorem KeepT.scf {t : U64} {s s' : S} (k : KeepT st T Cs Rp Scs Nt t s s') {y : U64} (hy : y ∈ T) :
    L.mem s' (scA y) = L.mem s (scA y) := by
  rw [scA_eq]; exact k.fld y hy _ (by simp) (by simp) (by simp) (by simp) (fun _ => ⟨by simp, by simp⟩)
theorem KeepT.inqf {t : U64} {s s' : S} (k : KeepT st T Cs Rp Scs Nt t s s') {y : U64} (hy : y ∈ T) :
    L.mem s' (inqA y) = L.mem s (inqA y) := by
  rw [inqA_eq]; exact k.fld y hy _ (by simp) (by simp) (by simp) (by simp) (fun _ => ⟨by simp, by simp⟩)
theorem KeepT.repf {t : U64} {s s' : S} (k : KeepT st T Cs Rp Scs Nt t s s') {y : U64} (hy : y ∈ T) :
    L.mem s' (replyA y) = L.mem s (replyA y) :=
  k.fld y hy _ (by simp) (by simp) (by simp) (by simp) (fun _ => ⟨by simp, by simp⟩)
theorem KeepT.stf {t : U64} {s s' : S} (k : KeepT st T Cs Rp Scs Nt t s s') {y : U64} (hy : y ∈ T) (hyt : y ≠ t) :
    L.mem s' (stA y) = L.mem s (stA y) := by
  rw [stA_eq]; exact k.fld y hy _ (by simp) (by simp) (by simp) (by simp) (fun e => absurd e hyt)

theorem KeepT.bndf {t : U64} {s s' : S} (k : KeepT st T Cs Rp Scs Nt t s s') {y : U64} (hy : y ∈ T) :
    L.mem s' (boundA y) = L.mem s (boundA y) :=
  k.fld y hy _ (by simp) (by simp) (by simp) (by simp) (fun _ => ⟨by simp, by simp⟩)

/-- `BoundInv` under `KeepT`. -/
theorem BoundInv.keepT {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {t : U64} {s s' : S}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T s) (k : KeepT st T Cs Rp Scs Nt t s s')
    (hnb : ¬ Blocked (L.mem s' (stA t))) : BoundInv st T s' := by
  refine hB.mk' (fun y hy => k.scf hy) (fun y hy hf => Or.inl (by rw [← k.inqf hy]; exact hf))
    (fun y hy hf => Or.inr (Or.inl (by rw [← k.inqf hy]; exact hf))) (fun haT => ?_)
    (by rw [k.idleW]; exact ⟨h.idleT, hB.idle⟩) (fun h0 => ?_) ?_
  rotate_right
  · rw [k.idleW]
    by_cases e : L.idleW s = t
    · rw [e]; exact hnb
    · rw [k.stf (y := L.idleW s) h.idleT e]; exact hB.idleNB
  · rcases k.act with e | e
    · rw [e] at haT ⊢; exact ⟨haT, hB.act haT⟩
    · rw [e] at haT; exact absurd haT (notT_small h.tcbs (by simp))
  · rcases k.act with e | e
    · rw [e] at h0; rw [k.curW]; exact ⟨h.curT, hB.resume h0⟩
    · rw [e] at h0; simp at h0

/-- `XInv` under `KeepT`, when `t` ends neither blocked on reply nor on
receive and the replies naming `t` are cleared. -/
theorem XInv.keepT {t : U64} {s s' : S} (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (k : KeepT st T Cs Rp Scs Nt t s s')
    (hst : L.mem s' (stA t) ≠ sched.TS_BLOCKED_ON_REPLY ∧ L.mem s' (stA t) ≠ sched.TS_BLOCKED_ON_RECV)
    (hclr : ∀ r ∈ Rp, L.mem s (rTcbA r) = t → L.mem s' (rTcbA r) = 0#u64) :
    XInv st T Cs Ω Sg Rp Scs Nt Z s' := by
  obtain ⟨hO, hR, hE⟩ := hX
  have rt : ∀ u ∈ T, u ≠ t → ∀ r ∈ Rp, L.mem s (rTcbA r) = u → L.mem s' (rTcbA r) = u := by
    intro u hu hut r hr e
    rcases k.rtcb r hr with e' | ⟨e', -⟩
    · rw [e']; exact e
    · exact absurd (e.symm.trans e') hut
  refine ⟨hO.ksb, ⟨fun u hu hs => ?_, fun u hu hs hn => ?_, fun r hr hn => ?_, fun r hr hp => ?_,
      fun r hr hn => ?_, fun c hc hn => ?_⟩,
    ⟨fun u hu hb => ?_, by rw [k.cscW]; exact hE.cur, fun c hc => by rw [(k.fix c hc).2.1]; exact hE.core c hc,
      fun u hu => by rw [k.bndf hu]; exact hE.bnd u hu, fun n hn => by rw [k.nsc n hn]; exact hE.nsc n hn,
      hE.tm.tmfr (TmFr.of_keepT k), hE.ntb.tmfr (TmFr.of_keepT k),
      fun c hc => by rw [k.snt c hc]; exact hE.scn c hc,
      ⟨fun c hc => by rw [(k.fix c hc).1]; exact hE.yt.1 c hc,
        fun u hu => by
          rw [show yieldA u = core.num.U64.wrapping_add u 3472#u64 from rfl,
            k.fld u hu _ (by simp) (by simp) (by simp) (by simp) (fun _ => by simp)]
          exact hE.yt.2.1 u hu,
        fun c hc h0 => by
          rcases k.syf c hc with e | e
          · rw [e] at h0 ⊢; exact hE.yt.2.2 c hc h0
          · exact absurd e h0⟩⟩⟩
  · by_cases e : u = t
    · subst e; exact absurd hs hst.1
    rw [k.stf hu e] at hs
    obtain ⟨h1, h2⟩ := hR.reply u hu hs
    rw [k.repf hu]; exact ⟨h1, rt u hu e _ h1 h2⟩
  · by_cases e : u = t
    · subst e; exact absurd hs hst.2
    rw [k.stf hu e] at hs; rw [k.repf hu] at hn ⊢
    obtain ⟨h1, h2⟩ := hR.recv u hu hs hn
    exact ⟨h1, rt u hu e _ h1 h2⟩
  · rcases (k.rlink r hr).2 with e | e
    · rw [e] at hn ⊢; exact hR.next r hr hn
    · exact absurd e hn
  · rcases (k.rlink r hr).1 with e | e
    · rw [e] at hp ⊢; exact hR.prev r hr hp
    · exact absurd e hp
  · rcases k.rtcb r hr with e' | ⟨-, e0⟩
    · by_cases hut : L.mem s (rTcbA r) = t
      · exact absurd (hclr r hr hut) hn
      rw [e'] at hn ⊢
      obtain ⟨b0, b1, b2, b3⟩ := hR.back r hr hn
      rw [k.repf b1, k.stf b1 hut]; exact ⟨b0, b1, b2, b3⟩
    · exact absurd e0 hn
  · rcases k.srep c hc with e | e
    · rw [e] at hn ⊢; exact hR.screp c hc hn
    · exact absurd e hn
  · rw [k.scf hu] at hb ⊢
    obtain ⟨h1, h2, h3⟩ := hE.bound u hu hb
    obtain ⟨f1, f2, -⟩ := k.fix _ h1
    rw [f1, f2]; exact ⟨h1, h2, h3⟩

/-- No reply names a thread that is neither blocked on reply nor on
receive. -/
theorem XInv.noref {t : U64} {s : S} (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hta : TcbAddr t)
    (h1 : L.mem s (stA t) ≠ sched.TS_BLOCKED_ON_REPLY) (h2 : L.mem s (stA t) ≠ sched.TS_BLOCKED_ON_RECV) :
    ∀ r ∈ Rp, L.mem s (rTcbA r) ≠ t := fun r hr e => by
  obtain ⟨-, -, -, b3⟩ := hX.2.1.back r hr (by rw [e]; exact fun e0 => hta.ne0 (by rw [e0]; rfl))
  rw [e] at b3
  rcases b3 with b3 | b3
  · exact h1 b3
  · exact h2 b3

/-- `cancel_ipc` keeps the queue invariant, `BoundInv` and `XInv`; the reply
facts it needs come from `XInv`. -/
theorem ipc.cancel_ipc.all {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (t : obj.Tcb)
    (Q : U64 → U64 → List U64) (R : U64 → List U64) (h : SchedQueuesInv st T Cs Ω H s Q R) (ht : t ∈ T)
    (hB : BoundInv st T s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω) :
    ipc.cancel_ipc st ar s a t ⦃ s' _ => SchedQueuesInv st T Cs Ω H s' Q R ∧ BoundInv st T s' ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧ ¬ Blocked (L.mem s' (stA t)) ∧
      L.mem s' (stA t) ≠ sched.TS_BLOCKED_ON_REPLY ∧
      (L.mem s' (stA t) = sched.TS_INACTIVE ∨
        (L.mem s' (stA t) = L.mem s (stA t) ∧ L.actionW s' = L.actionW s)) ∧ KeepT st T Cs Rp Scs Nt t s s' ∧
      (∀ r ∈ Rp, L.mem s (rTcbA r) = t → L.mem s' (rTcbA r) = 0#u64) ⦄ := by
  obtain ⟨hO, hR, hE⟩ := hX
  have hreply : L.mem s (stA t) = sched.TS_BLOCKED_ON_REPLY → ReplyT st Rp Scs s t := fun hs => by
    obtain ⟨h1, h2⟩ := hR.reply t ht hs
    exact ⟨h1, h2, hR.next _ h1, hR.prev _ h1⟩
  refine WP.spec_mono (ipc.cancel_ipc.inv s a t Q R h ht hO hsub (hR.recv t ht) hreply) fun r hr => ?_
  obtain ⟨s', a'⟩ := r
  obtain ⟨h', nb, nr, hst, k, z⟩ := hr
  have hclr : ∀ r ∈ Rp, L.mem s (rTcbA r) = t → L.mem s' (rTcbA r) = 0#u64 := by
    intro r hr e
    obtain ⟨b0, -, b2, b3⟩ := hR.back r hr (by rw [e]; exact fun e0 => (h.tcbs t ht).ne0 (by rw [e0]; rfl))
    rw [e] at b2 b3
    rw [← b2]
    refine z ?_
    rcases b3 with b3 | b3
    · exact Or.inl b3
    · exact Or.inr ⟨b3, by rw [b2]; exact b0⟩
  exact ⟨h', hB.keepT h k nb, XInv.keepT (Z := Z) (Ω := Ω) (Sg := Sg) ⟨hO, hR, hE⟩ k
    ⟨nr, fun e => nb (Or.inr (Or.inl e))⟩ hclr, nb, nr, hst, k, hclr⟩

/-- A refill write: the ring of an SC and the current core's `REPROGRAM`. -/
theorem TmFr.of_ring {X : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {i : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (hiS : i ∈ Scs) (w : WritesIn st s s' (fun b => InRing i (Z i) b ∨ b = L.nodeA s layout.node.REPROGRAM)) :
    TmFr st T Cs Nt s s' := by
  have hT := h.tcbs
  have hO := hX.1
  have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
  have hΩ : ∀ n ∈ Nt, OutsideObjs st T Cs s (ntfnBtA n) := fun n hn => h.omega _ (hsub _ (hO.ntB n hn).2)
  refine TmFr.of_writes hT h.nodes hO
    (w.mono' (B := fun b => Aligned b ∧ (InRing i (Z i) b ∨ b = L.nodeA s layout.node.REPROGRAM))
      fun b hb hh => ⟨hb, hh⟩) ?_
  rintro b ⟨hb, hh | hh⟩
  · have hm := hO.scW i hiS b hb hh.inSC
    refine notTmW_omega hT h.nodes (h.omega _ hm) (fun n hn e => ?_)
    rw [ntfnBtA_val (hO.ntP n hn)] at e
    have := hO.ntOSc n hn i hiS; have := hh.1; have := hh.2; omega
  · subst hh
    exact notTmW_node hT h.nodes hΩ h.cur (by rw [rp]; omega) (by rw [rp]; omega)

end

end Fl4Proofs.P1
