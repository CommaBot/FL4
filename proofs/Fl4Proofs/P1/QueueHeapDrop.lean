/-
P1: **dropping dead objects keeps the invariants** — the core of the reset
and of retype (`ResetP1Step`, `RetypeP1Step`).  `H.drop D` is the heap `H`
with the objects at the addresses `D` removed.  From `BlkOK` over `H`'s sets,
with the dropped objects dead (`DeadQ`) and unreferenced where P1's
invariants hold a reference without a back-pointer (`DropOK`), `BlkOK` holds
over `H.drop D`'s sets, in the same state.  One lemma per `BlkOK` component
(`BoundInv.drop`, `SgOK.drop`, `SCsOK.drop`, `XInv.drop`,
`SchedQueuesInv.drop`) and `BlkOK.drop`.
-/
import Fl4Proofs.P1.QueueRetype
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

/-- `H` with the objects at `D` removed. -/
noncomputable def Heap.drop (H : Heap) (D : U64 → Prop) : Heap := fun q => by
  classical exact if D q then none else H q

section
variable {H : Heap} {D : U64 → Prop}

theorem Heap.drop_eq_some {q : U64} {k : HKind} : H.drop D q = some k ↔ ¬ D q ∧ H q = some k := by
  unfold Heap.drop; by_cases h : D q <;> simp [h]

theorem Heap.drop_of_not {q : U64} (h : ¬ D q) : H.drop D q = H q := by
  unfold Heap.drop; simp [h]

theorem Heap.mem_tcbs_drop {q : U64} : q ∈ (H.drop D).tcbs ↔ q ∈ H.tcbs ∧ ¬ D q := by
  simp only [Heap.tcbs, Set.mem_setOf_eq, Heap.drop_eq_some]; tauto
theorem Heap.mem_replies_drop {q : U64} : q ∈ (H.drop D).replies ↔ q ∈ H.replies ∧ ¬ D q := by
  simp only [Heap.replies, Set.mem_setOf_eq, Heap.drop_eq_some]; tauto
theorem Heap.mem_ntfns_drop {q : U64} : q ∈ (H.drop D).ntfns ↔ q ∈ H.ntfns ∧ ¬ D q := by
  simp only [Heap.ntfns, Set.mem_setOf_eq, Heap.drop_eq_some]; tauto
theorem Heap.mem_scs_drop {q : U64} : q ∈ (H.drop D).scs ↔ q ∈ H.scs ∧ ¬ D q := by
  simp only [Heap.scs, Set.mem_setOf_eq, Heap.drop_eq_some]
  constructor
  · rintro ⟨z, h1, h2⟩; exact ⟨⟨z, h2⟩, h1⟩
  · rintro ⟨⟨z, h2⟩, h1⟩; exact ⟨z, h1, h2⟩

theorem Heap.tcbs_drop_sub : (H.drop D).tcbs ⊆ H.tcbs := fun _ h => (Heap.mem_tcbs_drop.1 h).1
theorem Heap.scs_drop_sub : (H.drop D).scs ⊆ H.scs := fun _ h => (Heap.mem_scs_drop.1 h).1
theorem Heap.replies_drop_sub : (H.drop D).replies ⊆ H.replies := fun _ h => (Heap.mem_replies_drop.1 h).1
theorem Heap.ntfns_drop_sub : (H.drop D).ntfns ⊆ H.ntfns := fun _ h => (Heap.mem_ntfns_drop.1 h).1

theorem Heap.scBits_drop {c : U64} (h : ¬ D c) : (H.drop D).scBits c = H.scBits c := by
  unfold Heap.scBits; rw [Heap.drop_of_not h]

theorem Heap.omega_drop_sub : (H.drop D).omega ⊆ H.omega := by
  rintro b ⟨ha, p, k, hp, hk, hin⟩
  exact ⟨ha, p, k, (Heap.drop_eq_some.1 hp).2, hk, hin⟩

theorem Heap.frame_drop_sub : (H.drop D).frame ⊆ H.frame := by
  rintro b ⟨ha, p, k, hp, hk, hin⟩
  exact ⟨ha, p, k, (Heap.drop_eq_some.1 hp).2, hk, hin⟩

/-- A word in no dropped object. -/
def OffDrop (H : Heap) (D : U64 → Prop) (b : U64) : Prop := ∀ p k, H p = some k → D p → ¬ InObj p k b

theorem Heap.omega_drop {b : U64} (hb : b ∈ H.omega) (hoff : OffDrop H D b) : b ∈ (H.drop D).omega := by
  obtain ⟨ha, p, k, hp, hk, hin⟩ := hb
  refine ⟨ha, p, k, Heap.drop_eq_some.2 ⟨fun hD => hoff p k hp hD hin, hp⟩, hk, hin⟩

theorem Heap.frame_drop {b : U64} (hb : b ∈ H.frame) (hoff : OffDrop H D b) : b ∈ (H.drop D).frame := by
  obtain ⟨ha, p, k, hp, hk, hin⟩ := hb
  refine ⟨ha, p, k, Heap.drop_eq_some.2 ⟨fun hD => hoff p k hp hD hin, hp⟩, hk, hin⟩

/-- A word of a kept object is in no dropped object (the objects are disjoint). -/
theorem offDrop_of_obj (hH : HeapOK H) {c : U64} {kc : HKind} (hc : H c = some kc) (hcD : ¬ D c) {b : U64}
    (hb : InObj c kc b) : OffDrop H D b := fun p k hp hD hin => by
  have hne : p ≠ c := fun e => hcD (e ▸ hD)
  have h1 := hin.1; have h2 := hin.2; have h3 := hb.1; have h4 := hb.2
  rcases hH.disj p k c kc hp hc hne with h | h <;> omega

end


/-- A reference that, if it names a heap object, names a kept one. -/
def KeptRef (H : Heap) (D : U64 → Prop) (x : U64) : Prop := H x ≠ none → ¬ D x

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- **What dropping the objects at `D` needs** (P3's, from `sym_refs` and the
untyped region's emptiness): the typed heap, nothing at the null address,
the dropped objects dead, the current thread and SC kept, the kernel-global
words in no dropped object, and the references P1's invariants hold
without a back-pointer naming kept objects. -/
structure DropOK (st : machine.Store S) [L : LawfulStore st] (H : Heap) (D : U64 → Prop) (Cs : Set U64)
    (s : S) : Prop where
  heap : HeapOK H
  h0 : H 0#u64 = none
  dead : ∀ q k, H q = some k → D q → DeadQ st H s q
  cur : ¬ D (L.curW s)
  csc : ¬ D (L.cscW s)
  ks : ∀ o : U64, o.val < 13568 → o.val % 8 = 0 → OffDrop H D (core.num.U64.wrapping_add (L.ksb s) o)
  rnext : ∀ r ∈ H.replies, ¬ D r → KeptRef H D (L.mem s (rNextA r) &&& ~~~1#u64)
  rprev : ∀ r ∈ H.replies, ¬ D r → KeptRef H D (L.mem s (rPrevA r) &&& ~~~1#u64)
  screp : ∀ c ∈ H.scs, ¬ D c → KeptRef H D (L.mem s (scReplyA c))
  bnd : ∀ t ∈ H.tcbs, ¬ D t → KeptRef H D (L.mem s (boundA t))
  scn : ∀ c ∈ H.scs, ¬ D c → KeptRef H D (L.mem s (scNtfnA c))
  ntb : ∀ n ∈ H.ntfns, ¬ D n → KeptRef H D (L.mem s (ntfnBtA n))
  yto : ∀ t ∈ H.tcbs, ¬ D t → KeptRef H D (L.mem s (yieldA t))
  yfrom : ∀ c ∈ H.scs, ¬ D c → KeptRef H D (L.mem s (scYieldFromA c))
  tl : ∀ y ∈ H.tcbs, ¬ D y → KeptRef H D (L.mem s (tlA y)) ∧ KeptRef H D (L.mem s (trA y)) ∧
    KeptRef H D (L.mem s (tpA y)) ∧ KeptRef H D (L.mem s (dnA y)) ∧ KeptRef H D (L.mem s (dpA y))
  node : ∀ c ∈ Cs, KeptRef H D (L.mem s (L.nodeAt s c layout.node.TIMER_ROOT)) ∧
    KeptRef H D (L.mem s (L.nodeAt s c layout.node.TIMER_MIN)) ∧
    KeptRef H D (L.mem s (L.nodeAt s c layout.node.DEBUG_TCBS))

variable {H : Heap} {D : U64 → Prop} {Cs : Set U64} {s : S}

/-- A kept reference to a TCB is a TCB of the dropped heap. -/
theorem KeptRef.tz {x : U64} (k : KeptRef H D x) (h : Tz H.tcbs x) : Tz (H.drop D).tcbs x := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Heap.mem_tcbs_drop.2 ⟨h, k (by rw [show H x = some .tcb from h]; simp)⟩)

theorem KeptRef.mem_tcbs {x : U64} (k : KeptRef H D x) (h : x ∈ H.tcbs) : x ∈ (H.drop D).tcbs :=
  Heap.mem_tcbs_drop.2 ⟨h, k (by rw [show H x = some .tcb from h]; simp)⟩
theorem KeptRef.mem_replies {x : U64} (k : KeptRef H D x) (h : x ∈ H.replies) : x ∈ (H.drop D).replies :=
  Heap.mem_replies_drop.2 ⟨h, k (by rw [show H x = some .reply from h]; simp)⟩
theorem KeptRef.mem_ntfns {x : U64} (k : KeptRef H D x) (h : x ∈ H.ntfns) : x ∈ (H.drop D).ntfns :=
  Heap.mem_ntfns_drop.2 ⟨h, k (by rw [show H x = some .ntfn from h]; simp)⟩
theorem KeptRef.mem_scs {x : U64} (k : KeptRef H D x) (h : x ∈ H.scs) : x ∈ (H.drop D).scs := by
  obtain ⟨z, hz⟩ := h
  exact Heap.mem_scs_drop.2 ⟨⟨z, hz⟩, k (by rw [hz]; simp)⟩

/-- A dropped object is dead. -/
theorem DropOK.deadOf (P : DropOK st H D Cs s) {q : U64} (hq : H q ≠ none) (hD : D q) : DeadQ st H s q := by
  obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.1 hq
  exact P.dead q k hk hD

/-- An SC of the heap is placed (from the typed heap). -/
theorem DropOK.scPlaced (P : DropOK st H D Cs s) {c : U64} (hc : c ∈ H.scs) :
    Placed c (H.scBits c) ∧ 7 ≤ H.scBits c ∧ H c = some (.sc (H.scBits c)) := by
  obtain ⟨z, hz⟩ := hc
  have e : H.scBits c = z := by unfold Heap.scBits; rw [hz]
  rw [e]
  exact ⟨⟨P.heap.lt64 c _ hz, P.heap.align c _ hz, P.heap.fits c _ hz⟩, P.heap.scmin c z hz, hz⟩

/-- A frame word of a kept SC is a frame word of the dropped heap. -/
theorem DropOK.scFrame (P : DropOK st H D Cs s) {c : U64} (hc : c ∈ H.scs) (hcD : ¬ D c) {b : U64}
    (hb : b ∈ H.frame) (hin : InSC c (H.scBits c) b) : b ∈ (H.drop D).frame :=
  Heap.frame_drop hb (offDrop_of_obj P.heap (P.scPlaced hc).2.2 hcD hin)

theorem DropOK.scOmega (P : DropOK st H D Cs s) {c : U64} (hc : c ∈ H.scs) (hcD : ¬ D c) {b : U64}
    (hb : b ∈ H.omega) (hin : InSC c (H.scBits c) b) : b ∈ (H.drop D).omega :=
  Heap.omega_drop hb (offDrop_of_obj P.heap (P.scPlaced hc).2.2 hcD hin)

/-- A word of an SC at an offset below 128 is in the SC. -/
theorem DropOK.scIn (P : DropOK st H D Cs s) {c : U64} (hc : c ∈ H.scs) {o : U64} (ho : o.val < 128) :
    InSC c (H.scBits c) (core.num.U64.wrapping_add c o) := by
  obtain ⟨hP, hz, -⟩ := P.scPlaced hc
  rw [InSC, sc_word_val hP hz ho]
  obtain ⟨-, h1, -⟩ := sc_lo hP hz
  omega

/-! ## The components -/

theorem BoundInv.sub {T T' Ac : Set U64} (h : BoundInv st T Ac s) (hT : T' ⊆ T) : BoundInv st T' Ac s :=
  ⟨fun t ht => h.q t (hT ht), fun t ht => h.r t (hT ht), fun ha => h.act (hT ha), h.idle, h.resume, h.idleNB,
    fun t ht => h.sact t (hT ht)⟩

/-- **`BoundInv` over the dropped heap.** -/
theorem BoundInv.drop {Ac : Set U64} (h : BoundInv st H.tcbs Ac s) : BoundInv st (H.drop D).tcbs Ac s :=
  h.sub Heap.tcbs_drop_sub

/-- **`SgOK` over the dropped heap.** -/
theorem SgOK.drop (P : DropOK st H D Cs s) (h : SgOK st H.omega H.frame s) :
    SgOK st (H.drop D).omega (H.drop D).frame s :=
  ⟨fun b hb => Heap.frame_omega hb, fun b hb => h.ks b (Heap.frame_drop_sub hb),
    fun o ho h8 => Heap.omega_drop (h.ksΩ o ho h8) (P.ks o ho h8)⟩

/-- **`SCsOK` over the dropped heap**, the bound SCs of the kept threads kept
(`hb`, from `XInv`). -/
theorem SCsOK.drop (P : DropOK st H D Cs s) {Ac : Set U64}
    (h : SCsOK st H.tcbs H.omega H.frame H.scs H.scBits Ac s)
    (hb : ∀ t ∈ (H.drop D).tcbs, L.mem s (scA t) ≠ 0#u64 → ¬ D (L.mem s (scA t))) :
    SCsOK st (H.drop D).tcbs (H.drop D).omega (H.drop D).frame (H.drop D).scs (H.drop D).scBits Ac s := by
  refine ⟨fun b hb => Heap.frame_omega hb, fun b hb => h.ks b (Heap.frame_drop_sub hb),
    fun o ho h8 => Heap.omega_drop (h.ksΩ o ho h8) (P.ks o ho h8), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht h0 hne b hin
    rw [Heap.scBits_drop (hb t ht h0)] at hin
    rw [Heap.scBits_drop P.csc]
    exact h.disj t (Heap.tcbs_drop_sub ht) h0 hne b hin
  · intro c hc
    obtain ⟨hc', hcD⟩ := Heap.mem_scs_drop.1 hc
    rw [Heap.scBits_drop hcD]
    obtain ⟨wf, mx, ws⟩ := h.all c hc'
    exact ⟨wf, P.scFrame hc' hcD mx (P.scIn hc' (by simp [layout.sc.REFILL_MAX])),
      fun b ha hin => P.scFrame hc' hcD (ws b ha hin) hin⟩
  · intro c hc; exact h.act c (Heap.scs_drop_sub hc)
  · intro c hc; exact h.spor c (Heap.scs_drop_sub hc)
  · intro c hc
    obtain ⟨hc', hcD⟩ := Heap.mem_scs_drop.1 hc
    exact P.scFrame hc' hcD (h.spSg c hc') (P.scIn hc' (by simp [layout.sc.SPORADIC]))
  · intro c hc; exact h.rep c (Heap.scs_drop_sub hc)
  · intro c hc
    obtain ⟨hc', hcD⟩ := Heap.mem_scs_drop.1 hc
    exact P.scFrame hc' hcD (h.repSg c hc') (P.scIn hc' (by simp [layout.sc.REPLY]))

end


section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]
variable {H : Heap} {D : U64 → Prop} {Cs : Set U64} {s : S}

theorem DropOK.objFrame (P : DropOK st H D Cs s) {q : U64} {k : HKind} (hq : H q = some k) (hqD : ¬ D q)
    {b : U64} (hb : b ∈ H.frame) (hin : InObj q k b) : b ∈ (H.drop D).frame :=
  Heap.frame_drop hb (offDrop_of_obj P.heap hq hqD hin)

theorem DropOK.rpFrame (P : DropOK st H D Cs s) {r : U64} (hr : r ∈ H.replies) (hrD : ¬ D r) {b : U64}
    (hb : b ∈ H.frame) (h1 : r.val ≤ b.val) (h2 : b.val < r.val + 32) : b ∈ (H.drop D).frame :=
  P.objFrame (k := .reply) hr hrD hb ⟨h1, by simpa [HKind.bits] using h2⟩

theorem DropOK.ntFrame (P : DropOK st H D Cs s) {n : U64} (hn : n ∈ H.ntfns) (hnD : ¬ D n) {b : U64}
    (hb : b ∈ H.frame) (h1 : n.val ≤ b.val) (h2 : b.val < n.val + 64) : b ∈ (H.drop D).frame :=
  P.objFrame (k := .ntfn) hn hnD hb ⟨h1, by simpa [HKind.bits] using h2⟩

/-- **`ObjsOK` over the dropped heap.** -/
theorem ObjsOK.drop (P : DropOK st H D Cs s)
    (h : ObjsOK st H.omega H.frame H.replies H.scs H.ntfns H.scBits s) :
    ObjsOK st (H.drop D).omega (H.drop D).frame (H.drop D).replies (H.drop D).scs (H.drop D).ntfns
      (H.drop D).scBits s := by
  have R : ∀ {r}, r ∈ (H.drop D).replies → r ∈ H.replies ∧ ¬ D r := Heap.mem_replies_drop.1
  have C : ∀ {c}, c ∈ (H.drop D).scs → c ∈ H.scs ∧ ¬ D c := Heap.mem_scs_drop.1
  have N : ∀ {n}, n ∈ (H.drop D).ntfns → n ∈ H.ntfns ∧ ¬ D n := Heap.mem_ntfns_drop.1
  refine ⟨fun r hr => h.rp r (R hr).1, fun c hc => ?_, fun r hr b ha h1 h2 => ?_, fun c hc b ha hin => ?_,
    fun c hc => ?_, fun c hc c' hc' hne => ?_, fun r hr c hc => ?_, fun c hc => ?_, fun n hn => ?_,
    fun n hn r hr => h.ntRp n (N hn).1 r (R hr).1, fun n hn c hc => ?_, fun n hn => h.ntAl n (N hn).1,
    fun n hn => h.ntP n (N hn).1, fun n hn => ?_, fun n hn r hr => h.ntORp n (N hn).1 r (R hr).1,
    fun n hn c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun n hn => h.nt0 n (N hn).1,
    fun r hr => h.rp0 r (R hr).1⟩
  · rw [Heap.scBits_drop (C hc).2]; exact h.sc c (C hc).1
  · exact P.rpFrame (R hr).1 (R hr).2 (h.rpW r (R hr).1 b ha h1 h2) h1 h2
  · rw [Heap.scBits_drop (C hc).2] at hin
    exact P.scOmega (C hc).1 (C hc).2 (h.scW c (C hc).1 b ha hin) hin
  · obtain ⟨h1, h2⟩ := h.fixW c (C hc).1
    exact ⟨P.scFrame (C hc).1 (C hc).2 h1 (P.scIn (C hc).1 (by simp [layout.sc.TCB])),
      P.scFrame (C hc).1 (C hc).2 h2 (P.scIn (C hc).1 (by simp [layout.sc.CORE]))⟩
  · rw [Heap.scBits_drop (C hc).2, Heap.scBits_drop (C hc').2]; exact h.scDisj c (C hc).1 c' (C hc').1 hne
  · rw [Heap.scBits_drop (C hc).2]; exact h.rpSc r (R hr).1 c (C hc).1
  · exact P.scFrame (C hc).1 (C hc).2 (h.repW c (C hc).1) (P.scIn (C hc).1 (by simp [layout.sc.REPLY]))
  · have e := ntfnScA_val (h.ntP n (N hn).1)
    exact P.ntFrame (N hn).1 (N hn).2 (h.ntW n (N hn).1) (by omega) (by omega)
  · rw [Heap.scBits_drop (C hc).2]; exact h.ntSc n (N hn).1 c (C hc).1
  · have e1 := ntfnBdA_val (h.ntP n (N hn).1)
    have e2 := ntfnBtA_val (h.ntP n (N hn).1)
    obtain ⟨b1, b2⟩ := h.ntB n (N hn).1
    exact ⟨P.ntFrame (N hn).1 (N hn).2 b1 (by omega) (by omega),
      P.ntFrame (N hn).1 (N hn).2 b2 (by omega) (by omega)⟩
  · rw [Heap.scBits_drop (C hc).2]; exact h.ntOSc n (N hn).1 c (C hc).1
  · exact P.scFrame (C hc).1 (C hc).2 (h.snW c (C hc).1) (P.scIn (C hc).1 (by simp [layout.sc.NTFN]))
  · exact P.scFrame (C hc).1 (C hc).2 (h.syW c (C hc).1) (P.scIn (C hc).1 (by simp [layout.sc.YIELD_FROM]))
  · exact P.scFrame (C hc).1 (C hc).2 (h.mxW c (C hc).1) (P.scIn (C hc).1 (by simp [layout.sc.REFILL_MAX]))

end


section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]
variable {H : Heap} {D : U64 → Prop} {Cs : Set U64} {s : S}

/-! ## Kept objects: the dead ones are inactive, unbound and unnamed -/

/-- A thread not inactive is kept. -/
theorem DropOK.keepT (P : DropOK st H D Cs s) {t : U64} (ht : t ∈ H.tcbs)
    (hs : L.mem s (stA t) ≠ sched.TS_INACTIVE) : ¬ D t := fun hD =>
  hs ((P.deadOf (by rw [show H t = some .tcb from ht]; simp) hD).1 ht).1

/-- A thread with an SC is kept. -/
theorem DropOK.keepTsc (P : DropOK st H D Cs s) {t : U64} (ht : t ∈ H.tcbs)
    (hs : L.mem s (scA t) ≠ 0#u64) : ¬ D t := fun hD =>
  hs ((P.deadOf (by rw [show H t = some .tcb from ht]; simp) hD).1 ht).2.1

/-- A reply naming a thread is kept. -/
theorem DropOK.keepR (P : DropOK st H D Cs s) {r : U64} (hr : r ∈ H.replies)
    (hs : L.mem s (rTcbA r) ≠ 0#u64) : ¬ D r := fun hD =>
  hs ((P.deadOf (by rw [show H r = some .reply from hr]; simp) hD).2.2.2.1 hr)

/-- An SC naming a thread or a notification is kept. -/
theorem DropOK.keepSc (P : DropOK st H D Cs s) {c : U64} (hc : c ∈ H.scs)
    (hs : L.mem s (scTcbA c) ≠ 0#u64 ∨ L.mem s (scNtfnA c) ≠ 0#u64) : ¬ D c := fun hD => by
  obtain ⟨z, hz⟩ := hc
  have d := (P.deadOf (by rw [hz]; simp) hD).2.2.2.2 z hz
  rcases hs with h | h
  · exact h d.1
  · exact h d.2.2

/-- Heap objects are not at the null address. -/
theorem DropOK.ne0 (P : DropOK st H D Cs s) {q : U64} (hq : H q ≠ none) : q ≠ 0#u64 := fun e => by
  rw [e, P.h0] at hq; exact hq rfl

theorem NodePlaced.sub {T T' : Set U64} {c : U64} (h : NodePlaced st T s c) (hT : T' ⊆ T) :
    NodePlaced st T' s c :=
  ⟨h.align, h.fits, fun t ht => h.disj t (hT ht)⟩

/-- **`TimerOK` over the dropped heap.** -/
theorem TimerOK.drop (P : DropOK st H D Cs s) (h : TimerOK st H.tcbs Cs s) : TimerOK st (H.drop D).tcbs Cs s := by
  have T : ∀ {y}, y ∈ (H.drop D).tcbs → y ∈ H.tcbs ∧ ¬ D y := Heap.mem_tcbs_drop.1
  exact ⟨fun c hc => (h.npl c hc).sub Heap.tcbs_drop_sub,
    fun y hy => (P.tl y (T hy).1 (T hy).2).1.tz (h.lt y (T hy).1),
    fun y hy => (P.tl y (T hy).1 (T hy).2).2.1.tz (h.rt y (T hy).1),
    fun y hy => (P.tl y (T hy).1 (T hy).2).2.2.1.tz (h.pt y (T hy).1),
    fun c hc => (P.node c hc).1.tz (h.root c hc), fun c hc => (P.node c hc).2.1.tz (h.min c hc),
    fun y hy => h.core y (T hy).1,
    fun y hy => (P.tl y (T hy).1 (T hy).2).2.2.2.1.tz (h.dn y (T hy).1),
    fun y hy => (P.tl y (T hy).1 (T hy).2).2.2.2.2.tz (h.dp y (T hy).1),
    fun c hc => (P.node c hc).2.2.tz (h.dh c hc)⟩

/-- **`ReplyInv` over the dropped heap.** -/
theorem ReplyInv.drop (P : DropOK st H D Cs s) (hT : TcbPlaced H.tcbs)
    (h : ReplyInv st H.tcbs H.replies H.scs s) : ReplyInv st (H.drop D).tcbs (H.drop D).replies (H.drop D).scs s := by
  have T : ∀ {y}, y ∈ (H.drop D).tcbs → y ∈ H.tcbs ∧ ¬ D y := Heap.mem_tcbs_drop.1
  have R : ∀ {r}, r ∈ (H.drop D).replies → r ∈ H.replies ∧ ¬ D r := Heap.mem_replies_drop.1
  have C : ∀ {c}, c ∈ (H.drop D).scs → c ∈ H.scs ∧ ¬ D c := Heap.mem_scs_drop.1
  have t0 : ∀ {t}, t ∈ H.tcbs → t ≠ 0#u64 := fun ht e => (hT _ ht).ne0 (by simp [e])
  have rp : ∀ {t}, t ∈ H.tcbs → L.mem s (replyA t) ∈ H.replies → L.mem s (rTcbA (L.mem s (replyA t))) = t →
      L.mem s (replyA t) ∈ (H.drop D).replies := fun ht hr he =>
    Heap.mem_replies_drop.2 ⟨hr, P.keepR hr (by rw [he]; exact t0 ht)⟩
  refine ⟨⟨fun t ht hs => ?_, fun t ht hs h0 => ?_, fun r hr h0 => ?_, fun r hr h0 => ?_, fun r hr h0 => ?_,
    fun c hc h0 => ?_, fun c hc => h.idle c (C hc).1⟩, fun r hr => h.head r (R hr).1⟩
  · obtain ⟨h1, h2⟩ := h.reply t (T ht).1 hs
    exact ⟨rp (T ht).1 h1 h2, h2⟩
  · obtain ⟨h1, h2⟩ := h.recv t (T ht).1 hs h0
    exact ⟨rp (T ht).1 h1 h2, h2⟩
  · obtain ⟨h1, h2⟩ := h.next r (R hr).1 h0
    have k := P.rnext r (R hr).1 (R hr).2
    exact ⟨fun hb => k.mem_scs (h1 hb), fun hb => k.mem_replies (h2 hb)⟩
  · exact (P.rprev r (R hr).1 (R hr).2).mem_replies (h.prev r (R hr).1 h0)
  · obtain ⟨h1, h2, h3, h4⟩ := h.back r (R hr).1 h0
    refine ⟨h1, Heap.mem_tcbs_drop.2 ⟨h2, P.keepT h2 ?_⟩, h3, h4⟩
    rcases h4 with e | e <;> rw [e] <;> simp [sched.TS_BLOCKED_ON_REPLY, sched.TS_BLOCKED_ON_RECV,
      sched.TS_INACTIVE]
  · exact (P.screp c (C hc).1 (C hc).2).mem_replies (h.screp c (C hc).1 h0)

/-- **`ScExtra` over the dropped heap.** -/
theorem ScExtra.drop (P : DropOK st H D Cs s)
    (h : ScExtra st H.tcbs Cs H.scs H.ntfns s) : ScExtra st (H.drop D).tcbs Cs (H.drop D).scs (H.drop D).ntfns s := by
  have T : ∀ {y}, y ∈ (H.drop D).tcbs → y ∈ H.tcbs ∧ ¬ D y := Heap.mem_tcbs_drop.1
  have C : ∀ {c}, c ∈ (H.drop D).scs → c ∈ H.scs ∧ ¬ D c := Heap.mem_scs_drop.1
  have N : ∀ {n}, n ∈ (H.drop D).ntfns → n ∈ H.ntfns ∧ ¬ D n := Heap.mem_ntfns_drop.1
  have hne : ∀ {q}, q ∈ H.tcbs ∨ q ∈ H.ntfns ∨ q ∈ H.scs → H q ≠ none := by
    rintro q (h | h | ⟨z, h⟩) <;> rw [h] <;> simp
  refine ⟨⟨fun t ht h0 => ?_, Heap.mem_scs_drop.2 ⟨h.cur, P.csc⟩, fun c hc => h.core c (C hc).1,
    fun t ht h0 => (P.bnd t (T ht).1 (T ht).2).mem_ntfns (h.bnd t (T ht).1 h0), fun n hn h0 => ?_,
    h.tm.drop P, fun n hn => (P.ntb n (N hn).1 (N hn).2).tz (h.ntb n (N hn).1),
    fun c hc h0 => (P.scn c (C hc).1 (C hc).2).mem_ntfns (h.scn c (C hc).1 h0), ⟨fun c hc h0 => ?_,
    fun t ht h0 => (P.yto t (T ht).1 (T ht).2).mem_scs (h.yt.2.1 t (T ht).1 h0),
    fun c hc h0 => (P.yfrom c (C hc).1 (C hc).2).mem_tcbs (h.yt.2.2 c (C hc).1 h0)⟩⟩,
    fun c hc => h.tsc c (C hc).1⟩
  · obtain ⟨h1, h2, h3⟩ := h.bound t (T ht).1 h0
    exact ⟨Heap.mem_scs_drop.2 ⟨h1, P.keepSc h1 (Or.inl (by rw [h2]; exact P.ne0 (hne (Or.inl (T ht).1))))⟩,
      h2, h3⟩
  · obtain ⟨h1, h2⟩ := h.nsc n (N hn).1 h0
    exact ⟨Heap.mem_scs_drop.2 ⟨h1, P.keepSc h1 (Or.inr (by rw [h2]; exact P.ne0 (hne (Or.inr (Or.inl (N hn).1)))))⟩,
      h2⟩
  · have h1 := h.yt.1 c (C hc).1 h0
    have e := h.tsc c (C hc).1 (P.ne0 (hne (Or.inr (Or.inr (C hc).1)))) h0
    exact Heap.mem_tcbs_drop.2 ⟨h1, P.keepTsc h1 (by rw [e]; exact P.ne0 (hne (Or.inr (Or.inr (C hc).1))))⟩

/-- **`XInv` over the dropped heap.** -/
theorem XInv.drop (P : DropOK st H D Cs s) (hT : TcbPlaced H.tcbs)
    (h : XInv st H.tcbs Cs H.omega H.frame H.replies H.scs H.ntfns H.scBits s) :
    XInv st (H.drop D).tcbs Cs (H.drop D).omega (H.drop D).frame (H.drop D).replies (H.drop D).scs
      (H.drop D).ntfns (H.drop D).scBits s :=
  ⟨h.1.drop P, h.2.1.drop P hT, h.2.2.drop P⟩

end


section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]
variable {H : Heap} {D : U64 → Prop} {Cs : Set U64} {s : S}

theorem QueueRel.sub {m : U64 → U64} {T T' : Set U64} {l : tcbqueue.Link} {q : tcbqueue.Queue} {xs : List U64}
    (h : QueueRel m T l q xs) (hT : ∀ t ∈ xs, t ∈ T') : QueueRel m T' l q xs :=
  ⟨h.nodup, hT, h.head, h.last, h.seg⟩

theorem EpPlaced.sub {T T' : Set U64} {e : U64} (h : EpPlaced T e) (hT : T' ⊆ T) : EpPlaced T' e :=
  ⟨h.align, h.fits, fun t ht => h.disj t (hT ht)⟩

theorem OutsideObjs.sub {T T' : Set U64} {a : U64} (h : OutsideObjs st T Cs s a) (hT : T' ⊆ T) :
    OutsideObjs st T' Cs s a :=
  ⟨h.1, fun t ht => h.2.1 t (hT ht), h.2.2⟩

theorem runnable_ne_inactive {v : U64} (h : Runnable v) : v ≠ sched.TS_INACTIVE := by
  rcases h with e | e | e <;> rw [e] <;> simp [sched.TS_RUNNING, sched.TS_RESTART, sched.TS_RUNNING_VM,
    sched.TS_INACTIVE]

theorem blocked_ne_inactive {v : U64} (h : Blocked v) : v ≠ sched.TS_INACTIVE := by
  rcases h with e | e | e <;> rw [e] <;> simp [sched.TS_BLOCKED_ON_SEND, sched.TS_BLOCKED_ON_RECV,
    sched.TS_BLOCKED_ON_NTFN, sched.TS_INACTIVE]

/-- An endpoint or notification with a waiter is kept. -/
theorem DropOK.keepE (P : DropOK st H D Cs s) {T : Set U64} {E : Set U64} {EQ : U64 → List U64}
    (hw : EpsWit st T Cs H.omega H ∅ s E EQ) {e : U64} (he : e ∈ E) {t : U64} (ht : t ∈ EQ e) (htT : t ∈ T) :
    ¬ D e := by
  obtain ⟨-, -, -, w4, -, k1, -, k3, -, k5, -⟩ := hw
  obtain ⟨-, eb, hbl⟩ := w4 e he t ht
  obtain ⟨s1, s2, s3⟩ := k5 e he t ht
  intro hD
  rcases (k3 e).1 he with hk | hk
  · have d := (P.deadOf (by rw [hk]; simp) hD).2.1 hk
    rcases hbl with b | b | b
    · rw [s1 b] at d; simp at d
    · rw [s2 b] at d; simp at d
    · rw [s3 b] at d; simp at d
  · have d := ((P.deadOf (by rw [hk]; simp) hD).2.2.1 hk).1
    rcases hbl with b | b | b
    · exact d (s1 b)
    · have := k1 t htT (Set.notMem_empty _) (Or.inr b)
      rw [eb, hk] at this; cases this
    · exact d (s3 b)

/-- **The endpoint queues over the dropped heap** (the kept objects of `E`). -/
theorem EpsOK.drop (P : DropOK st H D Cs s) (h : EpsOK st H.tcbs Cs H.omega H ∅ s) :
    EpsOK st (H.drop D).tcbs Cs (H.drop D).omega (H.drop D) ∅ s := by
  obtain ⟨E, EQ, hw⟩ := h
  have hw' := hw
  obtain ⟨w1, w2, w3, w4, w5, k1, k2, k3, k4, k5, k6⟩ := hw'
  have T : ∀ {y}, y ∈ (H.drop D).tcbs → y ∈ H.tcbs ∧ ¬ D y := Heap.mem_tcbs_drop.1
  have memT : ∀ e ∈ E, ∀ t ∈ EQ e, t ∈ (H.drop D).tcbs := fun e he t ht => by
    have htT := (w1 e he).2.2.mem t ht
    exact Heap.mem_tcbs_drop.2 ⟨htT, P.keepT htT (blocked_ne_inactive (w4 e he t ht).2.2)⟩
  refine ⟨{e | e ∈ E ∧ ¬ D e}, EQ, fun e he => ?_, fun e he e' he' hne => w2 e he.1 e' he'.1 hne,
    fun e he a ha => w3 e he.1 a (Heap.omega_drop_sub ha), fun e he t ht => w4 e he.1 t ht,
    fun t ht hx hb => ?_, fun t ht hx hs => ?_, fun t ht hx hs => ?_, fun e => ?_,
    fun e he => k4 e he.1, fun e he => k5 e he.1, fun e he h0 => ?_⟩
  · obtain ⟨p1, p2, p3⟩ := w1 e he.1
    exact ⟨p1.sub Heap.tcbs_drop_sub, p2, p3.sub (memT e he.1)⟩
  · obtain ⟨b1, b2⟩ := w5 t (T ht).1 hx hb
    exact ⟨⟨b1, P.keepE hw b1 b2 (T ht).1⟩, b2⟩
  · have hb : Blocked (L.mem s (stA t)) := by rcases hs with e | e; exact Or.inl e; exact Or.inr (Or.inl e)
    obtain ⟨b1, b2⟩ := w5 t (T ht).1 hx hb
    rw [Heap.drop_of_not (P.keepE hw b1 b2 (T ht).1)]
    exact k1 t (T ht).1 hx hs
  · obtain ⟨b1, b2⟩ := w5 t (T ht).1 hx (Or.inr (Or.inr hs))
    rw [Heap.drop_of_not (P.keepE hw b1 b2 (T ht).1)]
    exact k2 t (T ht).1 hx hs
  · simp only [Set.mem_setOf_eq, Heap.drop_eq_some, k3 e]
    tauto
  · rw [Heap.drop_of_not he.2]; exact k6 e he.1 h0

/-- **The scheduler queues over the dropped heap.** -/
theorem SchedQueuesInv.drop (P : DropOK st H D Cs s) {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInv st H.tcbs Cs H.omega H s Q R) :
    SchedQueuesInv st (H.drop D).tcbs Cs (H.drop D).omega (H.drop D) s Q R := by
  have T : ∀ {y}, y ∈ (H.drop D).tcbs → y ∈ H.tcbs ∧ ¬ D y := Heap.mem_tcbs_drop.1
  have sub := (Heap.tcbs_drop_sub : (H.drop D).tcbs ⊆ H.tcbs)
  have keepRun : ∀ t ∈ H.tcbs, Runnable (L.mem s (stA t)) → t ∈ (H.drop D).tcbs := fun t ht hr =>
    Heap.mem_tcbs_drop.2 ⟨ht, P.keepT ht (runnable_ne_inactive hr)⟩
  have hact : L.actionW s ∈ H.tcbs → ¬ D (L.actionW s) := fun ha hD =>
    ((P.deadOf (by rw [show H (L.actionW s) = some .tcb from ha]; simp) hD).1 ha).2.2.2.1 rfl
  have hidl : L.idleW s ∈ H.tcbs → ¬ D (L.idleW s) := fun ha hD =>
    ((P.deadOf (by rw [show H (L.idleW s) = some .tcb from ha]; simp) hD).1 ha).2.2.2.2 rfl
  refine ⟨fun t ht => h.tcbs t (sub ht), fun c hc => (h.nodes c hc).sub sub, h.cur,
    fun t ht => h.aff t (sub ht), fun t ht => h.prio t (sub ht), fun c hc => ?_, fun c hc => ?_, h.inQ, h.inR,
    fun t ht => h.queued t (sub ht), fun t ht => h.released t (sub ht), fun t ht => h.excl t (sub ht), ?_,
    h.runQ, h.runR, fun ha => h.actOK (sub ha), h.eps.drop P, ?_, ?_, fun t ht => h.ksOut t (sub ht),
    fun a ha => (h.omega a (Heap.omega_drop_sub ha)).sub sub⟩
  · obtain ⟨⟨r1, r2⟩, b⟩ := h.ready c hc
    exact ⟨⟨fun p hp => (r1 p hp).sub fun t ht => keepRun t ((r1 p hp).mem t ht) (h.runQ c hc p hp t ht), r2⟩, b⟩
  · exact (h.release c hc).sub fun t ht => keepRun t ((h.release c hc).mem t ht) (h.runR c hc t ht)
  · rcases h.action with e | e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (Heap.mem_tcbs_drop.2 ⟨e, hact e⟩))
  · exact Heap.mem_tcbs_drop.2 ⟨h.curT, P.cur⟩
  · exact Heap.mem_tcbs_drop.2 ⟨h.idleT, hidl h.idleT⟩

/-- **`BlkOK` over the dropped heap**, in the same state: the components
(`SchedQueuesInv.drop`, `BoundInv.drop`, `XInv.drop`, `SCsOK.drop`,
`SgOK.drop`). -/
theorem BlkOK.drop (P : DropOK st H D Cs s) {Ac : Set U64}
    (h : BlkOK st H.tcbs Cs H.omega H H.frame H.replies H.scs H.ntfns H.scBits Ac s) :
    BlkOK st (H.drop D).tcbs Cs (H.drop D).omega (H.drop D) (H.drop D).frame (H.drop D).replies (H.drop D).scs
      (H.drop D).ntfns (H.drop D).scBits Ac s := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hb : ∀ t ∈ (H.drop D).tcbs, L.mem s (scA t) ≠ 0#u64 → ¬ D (L.mem s (scA t)) := fun t ht h0' => by
    obtain ⟨h1, h2, -⟩ := hX.2.2.bound t (Heap.tcbs_drop_sub ht) h0'
    have htH : H t = some .tcb := Heap.tcbs_drop_sub ht
    exact P.keepSc h1 (Or.inl (by rw [h2]; exact P.ne0 (by rw [htH]; simp)))
  exact ⟨⟨Q, R, h0.drop P⟩, hB.drop, hX.drop P h0.tcbs, hS.drop P hb, hSg.drop P⟩

end

end Fl4Proofs.P1
