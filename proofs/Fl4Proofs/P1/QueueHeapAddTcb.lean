/-
P1: **adding new TCBs keeps the invariants** — the TCB family of retype.  A
new TCB's fields (from `F` = 3328 on, but the domain, the debug links and the
name) are zero, so it is inactive, unqueued, unbound and in no timer tree;
its debug links (and the debug lists' heads) are typed over the grown TCB
set after the writes.  Since the debug links of the kept TCBs may name the
new ones, the frame off the debug lists (`AgreeD`) and the addition are
taken together (`BlkOK.agreeAddTcb`): `BlkOK` over the dropped heap before
the writes gives `BlkOK` over the dropped heap with the new TCBs after.
-/
import Fl4Proofs.P1.QueueHeapDbg
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- **What adding TCBs at `N` needs**: fresh, placed and nonzero addresses,
disjoint from `H`'s objects, from each other, from the nodes and from the
kernel-global area, and their fields from `F` zero but the domain, the debug
links and the name. -/
structure AddOKT (st : machine.Store S) [L : LawfulStore st] (H : Heap) (N : U64 → Prop) (Cs : Set U64) (s : S) :
    Prop where
  fresh : ∀ q, N q → H q = none
  align : ∀ q, N q → q.val % 2 ^ 12 = 0
  fits : ∀ q, N q → q.val + 2 ^ 12 ≤ 2 ^ 64
  nz : ∀ q, N q → q ≠ 0#u64
  disjH : ∀ q, N q → ∀ p kp, H p = some kp → q.val + 2 ^ 12 ≤ p.val ∨ p.val + 2 ^ kp.bits ≤ q.val
  disjN : ∀ q q', N q → N q' → q ≠ q' → q.val + 2 ^ 12 ≤ q'.val ∨ q'.val + 2 ^ 12 ≤ q.val
  nodes : ∀ q, N q → ∀ c ∈ Cs, q.val + 2 ^ 12 ≤ L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ q.val
  ks : ∀ q, N q → q.val + 2 ^ 12 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ q.val
  zero : ∀ q, N q → ∀ K : U64, 3328 ≤ K.val → K.val < 3600 → K.val % 8 = 0 → K.val ≠ 3432 → K.val ≠ 3576 →
    K.val ≠ 3584 → L.mem s (core.num.U64.wrapping_add q K) = 0#u64

variable {H : Heap} {N : U64 → Prop} {Cs : Set U64} {s : S}

theorem Heap.add_some_ne {kd k : HKind} (hf : ∀ q, N q → H q = none) {q : U64} (hk : k ≠ kd) :
    H.add N kd q = some k ↔ H q = some k := by
  rw [Heap.add_eq_some]
  constructor
  · rintro (⟨-, h⟩ | ⟨-, h⟩)
    · exact absurd h hk
    · exact h
  · intro h
    by_cases hn : N q
    · rw [hf q hn] at h; cases h
    · exact Or.inr ⟨hn, h⟩

namespace AddOKT
variable (A : AddOKT st H N Cs s)
include A

theorem addr {q : U64} (hq : N q) : TcbAddr q :=
  ⟨fun h0 => A.nz q hq (UScalar.eq_of_val_eq (by simpa using h0)), A.align q hq, A.fits q hq⟩

theorem tcbs_add {q : U64} : q ∈ (H.add N .tcb).tcbs ↔ q ∈ H.tcbs ∨ N q := by
  simp only [Heap.tcbs, Set.mem_setOf_eq, Heap.add_eq_some]
  constructor
  · rintro (⟨hn, -⟩ | ⟨-, h⟩)
    · exact Or.inr hn
    · exact Or.inl h
  · rintro (h | hn)
    · exact Or.inr ⟨fun hn => (by rw [A.fresh q hn] at h; cases h), h⟩
    · exact Or.inl ⟨hn, trivial⟩

theorem notN {q : U64} (h : q ∈ H.tcbs) : ¬ N q := fun hn => by
  have : H q = some .tcb := h
  rw [A.fresh q hn] at this; cases this

theorem up {q : U64} (h : q ∈ H.tcbs) : q ∈ (H.add N .tcb).tcbs := A.tcbs_add.2 (Or.inl h)

theorem replies_eq : (H.add N .tcb).replies = H.replies := by
  ext q; exact Heap.add_some_ne A.fresh (by simp)
theorem ntfns_eq : (H.add N .tcb).ntfns = H.ntfns := by
  ext q; exact Heap.add_some_ne A.fresh (by simp)
theorem scs_eq : (H.add N .tcb).scs = H.scs := by
  ext q; simp only [Heap.scs, Set.mem_setOf_eq]
  exact ⟨fun ⟨z, h⟩ => ⟨z, (Heap.add_some_ne A.fresh (by simp)).1 h⟩,
    fun ⟨z, h⟩ => ⟨z, (Heap.add_some_ne A.fresh (by simp)).2 h⟩⟩
theorem scBits_eq : (H.add N .tcb).scBits = H.scBits := by
  funext q; unfold Heap.scBits
  by_cases hn : N q
  · rw [Heap.add_of_mem hn, A.fresh q hn]
  · rw [Heap.add_of_not hn]
theorem omega_eq : (H.add N .tcb).omega = H.omega := by
  ext b; simp only [Heap.omega, Set.mem_setOf_eq]
  constructor
  · rintro ⟨ha, p, k, hp, hkk, hin⟩
    have hne : k ≠ .tcb := by rcases hkk with h | ⟨z, h⟩ | ⟨z, h⟩ | ⟨h, -⟩ <;> subst h <;> simp
    exact ⟨ha, p, k, (Heap.add_some_ne A.fresh hne).1 hp, hkk, hin⟩
  · rintro ⟨ha, p, k, hp, hkk, hin⟩
    have hne : k ≠ .tcb := by rcases hkk with h | ⟨z, h⟩ | ⟨z, h⟩ | ⟨h, -⟩ <;> subst h <;> simp
    exact ⟨ha, p, k, (Heap.add_some_ne A.fresh hne).2 hp, hkk, hin⟩
theorem frame_eq : (H.add N .tcb).frame = H.frame := by
  ext b; simp only [Heap.frame, Set.mem_setOf_eq]
  constructor
  · rintro ⟨ha, p, k, hp, hkk, hin⟩
    have hne : k ≠ .tcb := by rcases hkk with h | ⟨z, h⟩ | ⟨h, -⟩ <;> subst h <;> simp
    exact ⟨ha, p, k, (Heap.add_some_ne A.fresh hne).1 hp, hkk, hin⟩
  · rintro ⟨ha, p, k, hp, hkk, hin⟩
    have hne : k ≠ .tcb := by rcases hkk with h | ⟨z, h⟩ | ⟨h, -⟩ <;> subst h <;> simp
    exact ⟨ha, p, k, (Heap.add_some_ne A.fresh hne).2 hp, hkk, hin⟩

theorem zSt {q : U64} (hq : N q) : L.mem s (stA q) = 0#u64 := by
  rw [stA_eq]; exact A.zero q hq _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
theorem zRep {q : U64} (hq : N q) : L.mem s (replyA q) = 0#u64 :=
  A.zero q hq 3360#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
theorem zBnd {q : U64} (hq : N q) : L.mem s (boundA q) = 0#u64 :=
  A.zero q hq 3368#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
theorem zPrio {q : U64} (hq : N q) : L.mem s (prioA q) = 0#u64 :=
  A.zero q hq 3448#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
theorem zSc {q : U64} (hq : N q) : L.mem s (scA q) = 0#u64 :=
  A.zero q hq 3464#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
theorem zYl {q : U64} (hq : N q) : L.mem s (yieldA q) = 0#u64 :=
  A.zero q hq 3472#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
theorem zAff {q : U64} (hq : N q) : L.mem s (affA q) = 0#u64 :=
  A.zero q hq 3520#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
theorem zTd {q : U64} (hq : N q) : L.mem s (tdA q) = 0#u64 :=
  A.zero q hq 3528#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
theorem zTl {q : U64} (hq : N q) : L.mem s (tlA q) = 0#u64 :=
  A.zero q hq 3544#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
theorem zTr {q : U64} (hq : N q) : L.mem s (trA q) = 0#u64 :=
  A.zero q hq 3552#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
theorem zTp {q : U64} (hq : N q) : L.mem s (tpA q) = 0#u64 :=
  A.zero q hq 3560#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
theorem zInq {q : U64} (hq : N q) : L.mem s (inqA q) = 0#u64 := by
  rw [inqA_eq]; exact A.zero q hq _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)

end AddOKT

theorem Tz.up {T T' : Set U64} {x : U64} (h : Tz T x) (hT : ∀ y ∈ T, y ∈ T') : Tz T' x :=
  h.imp_right (hT x)

theorem not_blocked0 : ¬ Blocked 0#u64 := by
  unfold Blocked; simp [sched.TS_BLOCKED_ON_SEND, sched.TS_BLOCKED_ON_RECV, sched.TS_BLOCKED_ON_NTFN]

/-- A switch-to candidate that is a TCB after the addition was one before. -/
theorem AddOKT.actT (A : AddOKT st H N Cs s) {Ω : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInv st H.tcbs Cs Ω H s Q R) (ha : L.actionW s ∈ (H.add N .tcb).tcbs) : L.actionW s ∈ H.tcbs := by
  rcases A.tcbs_add.1 ha with ha | hn
  · exact ha
  · rcases h.action with e | e | e
    · exact absurd e (A.nz _ hn)
    · have := A.align _ hn; rw [e] at this; simp at this
    · exact e

/-- **The endpoint queues with new TCBs.** -/
theorem EpsOK.addTcb (A : AddOKT st H N Cs s) {Ω : Set U64} (h : EpsOK st H.tcbs Cs Ω H ∅ s) :
    EpsOK st (H.add N .tcb).tcbs Cs Ω (H.add N .tcb) ∅ s := by
  obtain ⟨E, EQ, w1, w2, w3, w4, w5, k1, k2, k3, k4, k5, k6⟩ := h
  have nE : ∀ e ∈ E, ¬ N e := fun e he hn => by
    rcases (k3 e).1 he with h | h <;> rw [A.fresh e hn] at h <;> cases h
  have stB : ∀ t, N t → ¬ (L.mem s (stA t) = sched.TS_BLOCKED_ON_SEND ∨ L.mem s (stA t) = sched.TS_BLOCKED_ON_RECV) :=
    fun t hn h => not_blocked0 (by rw [← A.zSt hn]; rcases h with h | h; exact Or.inl h; exact Or.inr (Or.inl h))
  refine ⟨E, EQ, fun e he => ?_, w2, w3, w4, fun t ht hx hbl => ?_, fun t ht hx hs => ?_, fun t ht hx hs => ?_,
    fun e => ?_, k4, k5, fun e he h0 => ?_⟩
  · obtain ⟨hP, hO, hq⟩ := w1 e he
    refine ⟨⟨hP.align, hP.fits, fun t ht => ?_⟩, hO, hq.sub fun t ht => A.up (hq.mem t ht)⟩
    rcases A.tcbs_add.1 ht with ht | hn
    · exact hP.disj t ht
    · rcases (k3 e).1 he with h | h
      · have := A.disjH t hn e .ep h; rw [show (HKind.ep).bits = 4 from rfl] at this; omega
      · have := A.disjH t hn e .ntfn h; rw [show (HKind.ntfn).bits = 6 from rfl] at this; omega
  · rcases A.tcbs_add.1 ht with ht | hn
    · exact w5 t ht hx hbl
    · rw [A.zSt hn] at hbl; exact absurd hbl not_blocked0
  · rcases A.tcbs_add.1 ht with ht | hn
    · obtain ⟨b1, -⟩ := w5 t ht hx (by rcases hs with e | e; exact Or.inl e; exact Or.inr (Or.inl e))
      rw [Heap.add_of_not (nE _ b1)]; exact k1 t ht hx hs
    · exact absurd hs (stB t hn)
  · rcases A.tcbs_add.1 ht with ht | hn
    · obtain ⟨b1, -⟩ := w5 t ht hx (Or.inr (Or.inr hs))
      rw [Heap.add_of_not (nE _ b1)]; exact k2 t ht hx hs
    · exact absurd (Or.inr (Or.inr hs)) (by rw [A.zSt hn]; exact not_blocked0)
  · by_cases hn : N e
    · rw [Heap.add_of_mem hn]
      exact ⟨fun he => absurd hn (nE e he), fun h => by rcases h with h | h <;> cases h⟩
    · rw [Heap.add_of_not hn]; exact k3 e
  · rw [Heap.add_of_not (nE e he)]; exact k6 e he h0

set_option maxHeartbeats 4000000 in
/-- **The scheduler queues with new TCBs** (none queued; core `0` a core). -/
theorem SchedQueuesInv.addTcb (A : AddOKT st H N Cs s) {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInv st H.tcbs Cs H.omega H s Q R) (h0Cs : 0#u64 ∈ Cs) :
    SchedQueuesInv st (H.add N .tcb).tcbs Cs H.omega (H.add N .tcb) s Q R := by
  have p0 : (0#u64 : U64).val < 256 := by decide
  have z0 : ∀ x : U64, (0#u64 &&& x) = 0#u64 := fun x => by
    apply eq_of_bv; have : (0#u64).bv = 0#64 := rfl; simp [UScalar.bv_and, this]
  refine {
      tcbs := (fun t ht => ?_), nodes := (fun c hc => ?_), cur := h.cur, aff := (fun t ht => ?_),
      prio := (fun t ht => ?_), ready := (fun c hc => ?_), release := (fun c hc => ?_), inQ := h.inQ, inR := h.inR,
      queued := (fun t ht => ?_), released := (fun t ht => ?_), excl := (fun t ht => ?_), action := ?_,
      runQ := h.runQ, runR := h.runR, actOK := (fun ha => h.actOK (A.actT h ha)), eps := h.eps.addTcb A,
      curT := A.up h.curT, idleT := A.up h.idleT, ksOut := (fun t ht => ?_), omega := (fun a ha => ?_) }
  · rcases A.tcbs_add.1 ht with ht | hn
    · exact h.tcbs t ht
    · exact A.addr hn
  · refine ⟨(h.nodes c hc).align, (h.nodes c hc).fits, fun t ht => ?_⟩
    rcases A.tcbs_add.1 ht with ht | hn
    · exact (h.nodes c hc).disj t ht
    · exact A.nodes t hn c hc
  · rcases A.tcbs_add.1 ht with ht | hn
    · exact h.aff t ht
    · rw [A.zAff hn]; exact h0Cs
  · rcases A.tcbs_add.1 ht with ht | hn
    · exact h.prio t ht
    · rw [A.zPrio hn]; exact p0
  · exact ⟨⟨fun p hp => ((h.ready c hc).1.rel p hp).sub fun t ht => A.up (((h.ready c hc).1.rel p hp).mem t ht),
      (h.ready c hc).1.disj⟩, (h.ready c hc).2⟩
  · exact (h.release c hc).sub fun t ht => A.up ((h.release c hc).mem t ht)
  · rcases A.tcbs_add.1 ht with ht | hn
    · exact h.queued t ht
    · rw [A.zInq hn, A.zAff hn, A.zPrio hn, z0]
      exact ⟨fun h1 => absurd rfl h1, fun hm => absurd (h.memT h0Cs p0 hm) (fun h' => A.notN h' hn)⟩
  · rcases A.tcbs_add.1 ht with ht | hn
    · exact h.released t ht
    · rw [A.zInq hn, A.zAff hn, z0]
      exact ⟨fun h1 => absurd rfl h1, fun hm => absurd (h.memTR h0Cs hm) (fun h' => A.notN h' hn)⟩
  · rcases A.tcbs_add.1 ht with ht | hn
    · exact h.excl t ht
    · rw [A.zAff hn, A.zPrio hn]
      exact fun hm => absurd (h.memT h0Cs p0 hm) (fun h' => A.notN h' hn)
  · rcases h.action with e | e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (A.up e))
  · rcases A.tcbs_add.1 ht with ht | hn
    · exact h.ksOut t ht
    · exact A.ks t hn
  · obtain ⟨al, ht, hn⟩ := h.omega a ha
    refine ⟨al, fun t ht' => ?_, hn⟩
    rcases A.tcbs_add.1 ht' with ht' | hnt
    · exact ht t ht'
    · obtain ⟨-, p, k, hp, -, hin⟩ := ha
      have := A.disjH t hnt p k hp
      have h1 := hin.1; have h2 := hin.2
      omega

/-- **The bound-SC invariant with new TCBs.** -/
theorem BoundInv.addTcb (A : AddOKT st H N Cs s) {Ac Ω : Set U64} {Q : U64 → U64 → List U64}
    {R : U64 → List U64} (hB : BoundInv st H.tcbs Ac s) (h : SchedQueuesInv st H.tcbs Cs Ω H s Q R) :
    BoundInv st (H.add N .tcb).tcbs Ac s := by
  have z0 : ∀ x : U64, (0#u64 &&& x) = 0#u64 := fun x => by
    apply eq_of_bv; have : (0#u64).bv = 0#64 := rfl; simp [UScalar.bv_and, this]
  refine { hB with
      q := (fun t ht hq => ?_), r := (fun t ht hq => ?_), act := (fun ha => hB.act (A.actT h ha)),
      sact := (fun t ht hs h0 => ?_) }
  · rcases A.tcbs_add.1 ht with ht | hn
    · exact hB.q t ht hq
    · rw [A.zInq hn, z0] at hq; exact absurd rfl hq
  · rcases A.tcbs_add.1 ht with ht | hn
    · exact hB.r t ht hq
    · rw [A.zInq hn, z0] at hq; exact absurd rfl hq
  · rcases A.tcbs_add.1 ht with ht | hn
    · exact hB.sact t ht hs h0
    · rw [A.zSc hn] at h0; exact absurd rfl h0

end


section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]
variable {H : Heap} {N : U64 → Prop} {Cs : Set U64}

set_option maxHeartbeats 8000000 in
/-- **`BlkOK` after writes off the debug lists, with new TCBs added**: from
`BlkOK` over `H` before, states agreeing off the debug lists (for `H`'s
TCBs), the new TCBs' placement and zero fields after (`AddOKT`), and the
debug lists typed over the grown TCB set after. -/
theorem BlkOK.agreeAddTcb {s s' : S} {Ac : Set U64} (hH : HeapOK H)
    (h : BlkOK st H.tcbs Cs H.omega H H.frame H.replies H.scs H.ntfns H.scBits Ac s)
    (G : AgreeD st H.tcbs Cs H H.frame s s') (A : AddOKT st H N Cs s') (h0Cs : 0#u64 ∈ Cs)
    (D : DbgTz st (H.add N .tcb).tcbs Cs s') :
    BlkOK st (H.add N .tcb).tcbs Cs (H.add N .tcb).omega (H.add N .tcb) (H.add N .tcb).frame
      (H.add N .tcb).replies (H.add N .tcb).scs (H.add N .tcb).ntfns (H.add N .tcb).scBits Ac s' := by
  rw [A.omega_eq, A.frame_eq, A.replies_eq, A.scs_eq, A.ntfns_eq, A.scBits_eq]
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hT := h0.tcbs
  have fld := G.fld
  have sig := G.sig
  have hsc : ∀ y ∈ H.tcbs, L.mem s' (scA y) = L.mem s (scA y) := fun y hy => by
    rw [scA_eq]; exact fld y hy _ (by simp) (by simp) (by simp) (by simp) (by simp)
  have hst : ∀ y ∈ H.tcbs, L.mem s' (stA y) = L.mem s (stA y) := fun y hy => by
    rw [stA_eq]; exact fld y hy _ (by simp) (by simp) (by simp) (by simp) (by simp)
  have hinq : ∀ y ∈ H.tcbs, L.mem s' (inqA y) = L.mem s (inqA y) := fun y hy => by
    rw [inqA_eq]; exact fld y hy _ (by simp) (by simp) (by simp) (by simp) (by simp)
  have ea : L.actionW s' = L.actionW s := by
    unfold LawfulStore.actionW; exact G.cur h0.cur (by rw [act_val]; omega) (by rw [act_val]) (by rw [act_val]; omega)
  have ec : L.curW s' = L.curW s := by
    unfold LawfulStore.curW; exact G.cur h0.cur (by rw [curth0]; omega) (by rw [curth0]) (by rw [curth0]; omega)
  have ei : L.idleW s' = L.idleW s := by
    unfold LawfulStore.idleW; exact G.cur h0.cur (by rw [idle8]; omega) (by rw [idle8]) (by rw [idle8]; omega)
  have ecs : L.cscW s' = L.cscW s := by
    unfold LawfulStore.cscW LawfulStore.nodeA
    exact G.cur h0.cur (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  -- the old invariants after, for the old TCBs (but the debug lists)
  have q1 := h0.agreeD G
  have hB1 : BoundInv st H.tcbs Ac s' :=
    hB.mk' hsc (fun y hy hf => Or.inl (by rw [← hinq y hy]; exact hf))
      (fun y hy hf => Or.inr (Or.inl (by rw [← hinq y hy]; exact hf)))
      (fun haT => by rw [ea] at haT ⊢; exact ⟨haT, hB.act haT⟩) (by rw [ei]; exact ⟨h0.idleT, hB.idle⟩)
      (fun h0' => by rw [ea] at h0'; rw [ec]; exact ⟨h0.curT, hB.resume h0'⟩)
      (hB.nb ei (hst _ h0.idleT))
      (fun y hy hS _ => Or.inl (Sch.of_eq (fun hf => by rwa [hinq y hy] at hf) (fun hf => by rwa [hinq y hy] at hf)
        ea ei ec (hst y hy) hS))
  -- with the new TCBs
  have q2 := q1.addTcb A h0Cs
  have hB2 := hB1.addTcb A q1
  have TU : ∀ y ∈ H.tcbs, y ∈ (H.add N .tcb).tcbs := fun y hy => A.up hy
  have tm := hX.2.2.tm
  have tmo : TimerOK st (H.add N .tcb).tcbs Cs s' := by
    refine ⟨fun c hc => q2.nodes c hc, fun y hy => ?_, fun y hy => ?_, fun y hy => ?_, fun c hc => ?_,
      fun c hc => ?_, fun y hy hd c hcv => ?_, D.dn, D.dp, D.dh⟩
    · rcases A.tcbs_add.1 hy with hy | hn
      · rw [show tlA y = core.num.U64.wrapping_add y 3544#u64 from rfl,
          fld y hy _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact (tm.lt y hy).up TU
      · rw [A.zTl hn]; exact Tz.zero
    · rcases A.tcbs_add.1 hy with hy | hn
      · rw [show trA y = core.num.U64.wrapping_add y 3552#u64 from rfl,
          fld y hy _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact (tm.rt y hy).up TU
      · rw [A.zTr hn]; exact Tz.zero
    · rcases A.tcbs_add.1 hy with hy | hn
      · rw [show tpA y = core.num.U64.wrapping_add y 3560#u64 from rfl,
          fld y hy _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact (tm.pt y hy).up TU
      · rw [A.zTp hn]; exact Tz.zero
    · rw [nodeAt_of_ksb G.ksb, G.nod c hc _ (by rw [timer_root_val]; omega) (by rw [timer_root_val])
        (by rw [timer_root_val]; omega)]; exact (tm.root c hc).up TU
    · rw [nodeAt_of_ksb G.ksb, G.nod c hc _ (by rw [timer_min_val]; omega) (by rw [timer_min_val])
        (by rw [timer_min_val]; omega)]; exact (tm.min c hc).up TU
    · rcases A.tcbs_add.1 hy with hy | hn
      · rw [show tdA y = core.num.U64.wrapping_add y 3528#u64 from rfl,
          fld y hy _ (by simp) (by simp) (by simp) (by simp) (by simp)] at hd
        rw [show thA y = core.num.U64.wrapping_add y 3568#u64 from rfl,
          fld y hy _ (by simp) (by simp) (by simp) (by simp) (by simp)] at hcv
        exact tm.core y hy hd c hcv
      · rw [A.zTd hn] at hd; exact absurd rfl hd
  have ntb : NtbOK st (H.add N .tcb).tcbs H.ntfns s' := fun n hn => by
    rw [sig _ (hX.1.ntB n hn).2]; exact (hX.2.2.ntb n hn).up TU
  have rb : TimerRB st (H.add N .tcb).tcbs Cs s' := by
    have r1 : TimerRB st H.tcbs Cs s' := hX.2.2.rb.congr
      ⟨fun y hy => fld y hy 3528#u64 (by simp) (by simp) (by simp) (by simp) (by simp),
        fun y hy => fld y hy 3544#u64 (by simp) (by simp) (by simp) (by simp) (by simp),
        fun y hy => fld y hy 3552#u64 (by simp) (by simp) (by simp) (by simp) (by simp),
        fun y hy => fld y hy 3560#u64 (by simp) (by simp) (by simp) (by simp) (by simp),
        fun y hy => fld y hy 3568#u64 (by simp) (by simp) (by simp) (by simp) (by simp),
        fun c hc => by
          rw [nodeAt_of_ksb G.ksb, G.nod c hc _ (by rw [timer_root_val]; omega) (by rw [timer_root_val])
            (by rw [timer_root_val]; omega)],
        fun c hc => by
          rw [nodeAt_of_ksb G.ksb, G.nod c hc _ (by rw [timer_min_val]; omega) (by rw [timer_min_val])
            (by rw [timer_min_val]; omega)]⟩
    have ct : ∀ {c : U64} {t : TRB.RBT}, CoreTree st H.tcbs s' c t → CoreTree st (H.add N .tcb).tcbs s' c t :=
      fun c1 => { c1 with inT := fun y hy => TU y (c1.inT y hy) }
    refine ⟨fun c hc => ?_, fun y hy hd => ?_, fun y hy hd => ?_⟩
    · obtain ⟨t, c1⟩ := r1.tree c hc
      exact ⟨t, ct c1⟩
    · rcases A.tcbs_add.1 hy with hy | hn
      · obtain ⟨c, hc, t, c1, hyt⟩ := r1.armed y hy hd
        exact ⟨c, hc, t, ct c1, hyt⟩
      · rw [A.zTd hn] at hd; exact absurd rfl hd
    · rcases A.tcbs_add.1 hy with hy | hn
      · exact r1.idle y hy hd
      · exact ⟨A.zTl hn, A.zTr hn, A.zTp hn⟩
  -- the object invariants
  obtain ⟨hO, hR, hE⟩ := hX
  have hrw : ∀ r ∈ H.replies, L.mem s' (rTcbA r) = L.mem s (rTcbA r) ∧ L.mem s' (rPrevA r) = L.mem s (rPrevA r) ∧
      L.mem s' (rNextA r) = L.mem s (rNextA r) := fun r hr =>
    ⟨sig _ (hO.tcbW hr), sig _ (hO.prevW hr), sig _ (hO.nextW hr)⟩
  have hfx : ∀ c ∈ H.scs, L.mem s' (scTcbA c) = L.mem s (scTcbA c) ∧ L.mem s' (scCoreA c) = L.mem s (scCoreA c) :=
    fun c hc => ⟨sig _ (hO.fixW c hc).1, sig _ (hO.fixW c hc).2⟩
  have hrep : ∀ y ∈ H.tcbs, L.mem s' (replyA y) = L.mem s (replyA y) := fun y hy => by
    unfold replyA; exact fld y hy _ (by simp) (by simp) (by simp) (by simp) (by simp)
  have hbd : ∀ y ∈ H.tcbs, L.mem s' (boundA y) = L.mem s (boundA y) := fun y hy => by
    unfold boundA; exact fld y hy _ (by simp) (by simp) (by simp) (by simp) (by simp)
  have haf : ∀ y ∈ H.tcbs, L.mem s' (affA y) = L.mem s (affA y) := fun y hy => by
    unfold affA; exact fld y hy _ (by simp) (by simp) (by simp) (by simp) (by simp)
  have hyl : ∀ y ∈ H.tcbs, L.mem s' (yieldA y) = L.mem s (yieldA y) := fun y hy => by
    unfold yieldA; exact fld y hy _ (by simp) (by simp) (by simp) (by simp) (by simp)
  have hsr : ∀ c ∈ H.scs, L.mem s' (scReplyA c) = L.mem s (scReplyA c) := fun c hc => sig _ (hO.repW c hc)
  have hns : ∀ n ∈ H.ntfns, L.mem s' (ntfnScA n) = L.mem s (ntfnScA n) := fun n hn => sig _ (hO.ntW n hn)
  have hsn : ∀ c ∈ H.scs, L.mem s' (scNtfnA c) = L.mem s (scNtfnA c) := fun c hc => sig _ (hO.snW c hc)
  have hyf : ∀ c ∈ H.scs, L.mem s' (scYieldFromA c) = L.mem s (scYieldFromA c) := fun c hc => sig _ (hO.syW c hc)
  have hmx : ∀ c ∈ H.scs, L.mem s' (maxA c) = L.mem s (maxA c) := fun c hc => sig _ (hO.mxW c hc)
  have st0 : ∀ v : U64, v = 0#u64 → v ≠ sched.TS_BLOCKED_ON_REPLY ∧ v ≠ sched.TS_BLOCKED_ON_RECV := by
    rintro v rfl; simp [sched.TS_BLOCKED_ON_REPLY, sched.TS_BLOCKED_ON_RECV]
  have rinv : ReplyInv st (H.add N .tcb).tcbs H.replies H.scs s' := by
    refine ⟨⟨fun t ht hs => ?_, fun t ht hs hn => ?_, fun r hr => ?_, fun r hr => ?_, fun r hr hn => ?_,
      fun c hc => by rw [hsr c hc]; exact hR.screp c hc,
      idleRep_keep hR.idle ei (fun c hc => (hfx c hc).1) (fun c hc => Or.inl (hsr c hc))⟩,
      hR.head.keep (fun r hr => (hrw r hr).2.2) hsr (fun r hr h0 hb => (hR.next r hr h0).1 hb)⟩
    · rcases A.tcbs_add.1 ht with ht | hnw
      · rw [hst t ht] at hs
        obtain ⟨h1, h2⟩ := hR.reply t ht hs
        rw [hrep t ht, (hrw _ h1).1]; exact ⟨h1, h2⟩
      · exact absurd hs (st0 _ (A.zSt hnw)).1
    · rcases A.tcbs_add.1 ht with ht | hnw
      · rw [hst t ht] at hs; rw [hrep t ht] at hn ⊢
        obtain ⟨h1, h2⟩ := hR.recv t ht hs hn
        rw [(hrw _ h1).1]; exact ⟨h1, h2⟩
      · exact absurd hs (st0 _ (A.zSt hnw)).2
    · rw [(hrw r hr).2.2]; exact hR.next r hr
    · rw [(hrw r hr).2.1]; exact hR.prev r hr
    · rw [(hrw r hr).1] at hn ⊢
      obtain ⟨b0, b1, b2, b3⟩ := hR.back r hr hn
      rw [hrep _ b1, hst _ b1]; exact ⟨b0, TU _ b1, b2, b3⟩
  have ext : ScExtra st (H.add N .tcb).tcbs Cs H.scs H.ntfns s' := by
    refine ⟨⟨fun t ht hb => ?_, by rw [ecs]; exact hE.cur, fun c hc => by rw [(hfx c hc).2]; exact hE.core c hc,
      fun t ht hb => ?_, ScExtra.nsc_keepN hE.nsc hns hsn (fun c hc _ => hmx c hc), tmo, ntb, rb,
      fun c hc => by rw [hsn c hc]; exact hE.scn c hc, ⟨fun c hc h0' => ?_, fun t ht h0' => ?_, fun c hc h0' => ?_⟩,
      ⟨fun t ht h0' => by
        rcases A.tcbs_add.1 ht with ht | hnw
        · rw [hbd t ht] at h0' ⊢; rw [sig _ (hO.ntB _ (hE.bnd t ht h0')).2]; exact hE.bs.tb t ht h0'
        · rw [A.zBnd hnw] at h0'; exact absurd rfl h0',
       fun n hn h0' => by
        rw [sig _ (hO.ntB n hn).2] at h0' ⊢
        rw [hbd _ ((hE.ntb n hn).ne0 h0')]; exact hE.bs.nt n hn h0',
       fun c hc hc0 h0' => by
        rw [hsn c hc] at h0' ⊢; rw [hns _ (hE.scn c hc h0')]; exact hE.bs.sn c hc hc0 h0'⟩⟩,
      hE.tsc.keep hE.yt.1 (fun c hc => (hfx c hc).1) hsc, fun t ht hb => ?_⟩
    · rcases A.tcbs_add.1 ht with ht | hnw
      · rw [hsc t ht] at hb ⊢
        obtain ⟨h1, h2, h3⟩ := hE.bound t ht hb
        rw [(hfx _ h1).1, (hfx _ h1).2]; exact ⟨h1, h2, h3⟩
      · rw [A.zSc hnw] at hb; exact absurd rfl hb
    · rcases A.tcbs_add.1 ht with ht | hnw
      · rw [hbd t ht] at hb ⊢; exact hE.bnd t ht hb
      · rw [A.zBnd hnw] at hb; exact absurd rfl hb
    · rw [(hfx c hc).1] at h0' ⊢; exact TU _ (hE.yt.1 c hc h0')
    · rcases A.tcbs_add.1 ht with ht | hnw
      · rw [hyl t ht] at h0' ⊢; exact hE.yt.2.1 t ht h0'
      · rw [A.zYl hnw] at h0'; exact absurd rfl h0'
    · rw [hyf c hc] at h0' ⊢; exact TU _ (hE.yt.2.2 c hc h0')
    · rcases A.tcbs_add.1 ht with ht | hnw
      · rw [hsc t ht] at hb ⊢
        rw [(hfx _ (hE.bound t ht hb).1).2, haf t ht]; exact hE.aff t ht hb
      · rw [A.zSc hnw] at hb; exact absurd rfl hb
  have hS' : SCsOK st (H.add N .tcb).tcbs H.omega H.frame H.scs H.scBits Ac s' := by
    refine ⟨hS.sub, fun b hb => by rw [G.ksb]; exact hS.ks b hb, fun o h1 h2 => by rw [G.ksb]; exact hS.ksΩ o h1 h2,
      fun t ht hb hne => ?_, fun c hc => (hS.all c hc).agree sig,
      fun c hc => by rw [show L.rmax s' c = L.rmax s c from sig _ (hS.all c hc).2.1]; exact hS.act c hc,
      fun c hc h1 => hS.spor c hc (by rw [← sig _ (hS.spSg c hc)]; exact h1), hS.spSg,
      fun c hc h1 => hS.rep c hc (by rw [← sig _ (hS.repSg c hc)]; exact h1), hS.repSg, fun c hc => by rw [G.ksb]; exact hS.scKs c hc⟩
    rcases A.tcbs_add.1 ht with ht | hnw
    · rw [hsc t ht] at hb hne ⊢; rw [ecs] at hne ⊢; exact hS.disj t ht hb hne
    · rw [A.zSc hnw] at hb; exact absurd rfl hb
  exact ⟨⟨Q, R, q2⟩, hB2, ⟨hO.ksb, rinv, ext⟩, hS',
    ⟨hSg.sub, fun b hb => by rw [G.ksb]; exact hSg.ks b hb, fun o h1 h2 => by rw [G.ksb]; exact hSg.ksΩ o h1 h2⟩⟩

end

end Fl4Proofs.P1
