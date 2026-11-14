/-
P1: `ObjsOK` (and the placement facts `SchedQueuesInv` and `SgOK` assume of
`Ω`) from a typed-heap invariant: a ghost map from pointers to object kinds
whose objects are aligned to their size, fit in the address space and are
pairwise disjoint (l4v `pspace_aligned`, `pspace_distinct`), plus the kernel
area (the global words and the per-core nodes) lying outside every object.
-/
import Fl4Proofs.P1.QueueObjs
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

/-- The typed-heap invariant. -/
structure HeapOK (H : Heap) : Prop where
  align : ∀ p k, H p = some k → p.val % 2 ^ k.bits = 0
  fits : ∀ p k, H p = some k → p.val + 2 ^ k.bits ≤ 2 ^ 64
  lt64 : ∀ p k, H p = some k → k.bits < 64
  scmin : ∀ p z, H p = some (.sc z) → 7 ≤ z
  disj : ∀ p k q k', H p = some k → H q = some k' → p ≠ q →
    p.val + 2 ^ k.bits ≤ q.val ∨ q.val + 2 ^ k'.bits ≤ p.val

/-- The objects of a kind. -/
def Heap.tcbs (H : Heap) : Set U64 := {p | H p = some .tcb}
def Heap.replies (H : Heap) : Set U64 := {p | H p = some .reply}
def Heap.scs (H : Heap) : Set U64 := {p | ∃ z, H p = some (.sc z)}
def Heap.ntfns (H : Heap) : Set U64 := {p | H p = some .ntfn}
/-- The size exponent of the SC at `c`. -/
def Heap.scBits (H : Heap) (c : U64) : Nat :=
  match H c with
  | some (.sc z) => z
  | _ => 0

/-- `b` is a word of the object at `p` of kind `k`. -/
def InObj (p : U64) (k : HKind) (b : U64) : Prop := p.val ≤ b.val ∧ b.val < p.val + 2 ^ k.bits

/-- A notification's frame words: `BADGE`, `BOUND_TCB` and `SC`. -/
def NtfnW (p b : U64) : Prop := b = ntfnScA p ∨ b = ntfnBdA p ∨ b = ntfnBtA p

/-- The other objects' words: aligned words of replies, SCs and other
objects, and the notifications' frame words. -/
def Heap.omega (H : Heap) : Set U64 :=
  {b | Aligned b ∧ ∃ p k, H p = some k ∧
    (k = .reply ∨ (∃ z, k = .sc z) ∨ (∃ z, k = .other z) ∨ (k = .ntfn ∧ NtfnW p b)) ∧ InObj p k b}

/-- The frame words: aligned words of replies and SCs, and the notifications'
frame words. -/
def Heap.frame (H : Heap) : Set U64 :=
  {b | Aligned b ∧ ∃ p k, H p = some k ∧ (k = .reply ∨ (∃ z, k = .sc z) ∨ (k = .ntfn ∧ NtfnW p b)) ∧
    InObj p k b}

theorem Heap.frame_omega {H : Heap} {b : U64} (hb : b ∈ H.frame) : b ∈ H.omega := by
  obtain ⟨ha, p, k, hp, hk, hin⟩ := hb
  refine ⟨ha, p, k, hp, ?_, hin⟩
  rcases hk with hk | hk | hk
  · exact Or.inl hk
  · exact Or.inr (Or.inl hk)
  · exact Or.inr (Or.inr (Or.inr hk))

theorem ntfnScA_val' {n : U64} (h : n.val % 64 = 0) (h2 : n.val + 64 ≤ 2 ^ 64) : (ntfnScA n).val = n.val + 32 := by
  unfold ntfnScA; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega

theorem Heap.scBits_eq {H : Heap} {c : U64} {z : Nat} (h : H c = some (.sc z)) : H.scBits c = z := by
  unfold Heap.scBits; rw [h]

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

theorem ntfn_word_val {n o : U64} (h : n.val % 64 = 0) (h2 : n.val + 64 ≤ 2 ^ 64) (ho : o.val < 64) :
    (core.num.U64.wrapping_add n o).val = n.val + o.val := by
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega

/-- The typed heap gives `ObjsOK`. -/
theorem ObjsOK.of_heap {H : Heap} (hH : HeapOK H) (h0 : H 0#u64 = none) (s : S) :
    ObjsOK st H.omega H.frame H.replies H.scs H.ntfns H.scBits s := by
  have nP : ∀ n ∈ H.ntfns, n.val % 64 = 0 ∧ n.val + 64 ≤ 2 ^ 64 := by
    intro n hn
    have := hH.align n _ hn; have := hH.fits n _ hn
    simp only [HKind.bits] at *
    exact ⟨by omega, by omega⟩
  have nv : ∀ n ∈ H.ntfns, (ntfnScA n).val = n.val + 32 ∧ n.val % 64 = 0 ∧ n.val + 64 ≤ 2 ^ 64 := fun n hn =>
    ⟨ntfnScA_val' (nP n hn).1 (nP n hn).2, nP n hn⟩
  have nfr : ∀ n ∈ H.ntfns, ∀ o : U64, o.val < 64 → o.val % 8 = 0 → NtfnW n (core.num.U64.wrapping_add n o) →
      core.num.U64.wrapping_add n o ∈ H.frame := by
    intro n hn o ho h8 hw
    obtain ⟨h1, h2⟩ := nP n hn
    refine ⟨by unfold Aligned; rw [ntfn_word_val h1 h2 ho]; omega, n, .ntfn, hn, Or.inr (Or.inr ⟨rfl, hw⟩), ?_⟩
    simp only [InObj, HKind.bits]; rw [ntfn_word_val h1 h2 ho]; omega
  have hsnW : ∀ c ∈ H.scs, scNtfnA c ∈ H.frame := by
    rintro c ⟨z, hz⟩
    have hP : Placed c z := ⟨by have := hH.lt64 c _ hz; simpa [HKind.bits] using this,
      by simpa [HKind.bits] using hH.align c _ hz, by simpa [HKind.bits] using hH.fits c _ hz⟩
    have hz7 := hH.scmin c z hz
    obtain ⟨h8, h128, -⟩ := sc_lo hP hz7
    refine ⟨?_, c, .sc z, hz, Or.inr (Or.inl ⟨z, rfl⟩), ?_⟩
    · unfold Aligned; rw [scNtfnA_val hP hz7]; omega
    · simp only [InObj, HKind.bits]; rw [scNtfnA_val hP hz7]; omega
  have hsyW : ∀ c ∈ H.scs, scYieldFromA c ∈ H.frame := by
    rintro c ⟨z, hz⟩
    have hP : Placed c z := ⟨by have := hH.lt64 c _ hz; simpa [HKind.bits] using this,
      by simpa [HKind.bits] using hH.align c _ hz, by simpa [HKind.bits] using hH.fits c _ hz⟩
    have hz7 := hH.scmin c z hz
    obtain ⟨h8, h128, -⟩ := sc_lo hP hz7
    refine ⟨?_, c, .sc z, hz, Or.inr (Or.inl ⟨z, rfl⟩), ?_⟩
    · unfold Aligned scYieldFromA; rw [scYieldA_val hP hz7]; omega
    · simp only [InObj, HKind.bits]; unfold scYieldFromA; rw [scYieldA_val hP hz7]; omega
  have hmxW : ∀ c ∈ H.scs, maxA c ∈ H.frame := by
    rintro c ⟨z, hz⟩
    have hP : Placed c z := ⟨by have := hH.lt64 c _ hz; simpa [HKind.bits] using this,
      by simpa [HKind.bits] using hH.align c _ hz, by simpa [HKind.bits] using hH.fits c _ hz⟩
    have hz7 := hH.scmin c z hz
    obtain ⟨h8, h128, -⟩ := sc_lo hP hz7
    refine ⟨?_, c, .sc z, hz, Or.inr (Or.inl ⟨z, rfl⟩), ?_⟩
    · unfold Aligned; rw [maxA_val hP hz7]; omega
    · simp only [InObj, HKind.bits]; rw [maxA_val hP hz7]; omega
  refine ⟨fun r hr => ?_, fun c ⟨z, hz⟩ => ?_, fun r hr b hb h1 h2 => ?_, fun c ⟨z, hz⟩ b hb hin => ?_,
    fun c ⟨z, hz⟩ => ?_, fun c ⟨z, hz⟩ c' ⟨z', hz'⟩ hne => ?_, fun r hr c ⟨z, hz⟩ => ?_, fun c ⟨z, hz⟩ => ?_,
    fun n hn => ?_, fun n hn r hr => ?_, fun n hn c ⟨z, hz⟩ => ?_, fun n hn => ?_,
    nP,
    fun n hn => ⟨nfr n hn _ (by simp [layout.ntfn.BADGE]) (by simp [layout.ntfn.BADGE]) (Or.inr (Or.inl rfl)),
      nfr n hn _ (by simp [layout.ntfn.BOUND_TCB]) (by simp [layout.ntfn.BOUND_TCB]) (Or.inr (Or.inr rfl))⟩,
    fun n hn r hr => ?_, fun n hn c ⟨z, hz⟩ => ?_, hsnW, hsyW, hmxW,
    fun n hn e => by subst e; have : H 0#u64 = some .ntfn := hn; rw [h0] at this; cases this⟩
  rotate_right 6
  · exact nfr n hn _ (by simp [layout.ntfn.SC]) (by simp [layout.ntfn.SC]) (Or.inl rfl)
  · obtain ⟨e, h1, h2⟩ := nv n hn
    have hne : n ≠ r := fun e' => by
      subst e'; have h1 : H n = some .ntfn := hn; have h2 : H n = some .reply := hr; rw [h1] at h2; cases h2
    have := hH.disj n _ r _ hn hr hne
    simp only [HKind.bits] at this; rw [e]; omega
  · obtain ⟨e, h1, h2⟩ := nv n hn
    have hne : n ≠ c := fun e' => by
      subst e'; have h1 : H n = some .ntfn := hn; rw [h1] at hz; cases hz
    have := hH.disj n _ c _ hn hz hne
    rw [Heap.scBits_eq hz]; simp only [HKind.bits] at this; rw [e]; omega
  · obtain ⟨e, h1, h2⟩ := nv n hn
    unfold Aligned; rw [e]; omega
  · have hne : n ≠ r := fun e' => by
      subst e'; have h1 : H n = some .ntfn := hn; have h2 : H n = some .reply := hr; rw [h1] at h2; cases h2
    have := hH.disj n _ r _ hn hr hne
    simpa [HKind.bits] using this
  · have hne : n ≠ c := fun e' => by
      subst e'; have h1 : H n = some .ntfn := hn; rw [h1] at hz; cases hz
    have := hH.disj n _ c _ hn hz hne
    rw [Heap.scBits_eq hz]; simpa [HKind.bits] using this
  · have := hH.align r _ hr; have := hH.fits r _ hr
    simp only [HKind.bits] at *; exact ⟨by omega, by omega⟩
  · rw [Heap.scBits_eq hz]
    exact ⟨⟨by have := hH.lt64 c _ hz; simpa [HKind.bits] using this, by simpa [HKind.bits] using hH.align c _ hz,
      by simpa [HKind.bits] using hH.fits c _ hz⟩, hH.scmin c z hz⟩
  · exact ⟨hb, r, .reply, hr, Or.inl rfl, by simp only [InObj, HKind.bits]; omega⟩
  · rw [Heap.scBits_eq hz] at hin
    exact ⟨hb, c, .sc z, hz, Or.inr (Or.inl ⟨z, rfl⟩), by unfold InObj HKind.bits; exact hin⟩
  · have hP : Placed c z := ⟨by have := hH.lt64 c _ hz; simpa [HKind.bits] using this,
      by simpa [HKind.bits] using hH.align c _ hz, by simpa [HKind.bits] using hH.fits c _ hz⟩
    have hz7 := hH.scmin c z hz
    obtain ⟨h8, h128, -⟩ := sc_lo hP hz7
    refine ⟨⟨?_, c, .sc z, hz, Or.inr (Or.inl ⟨z, rfl⟩), ?_⟩, ⟨?_, c, .sc z, hz, Or.inr (Or.inl ⟨z, rfl⟩), ?_⟩⟩
    · unfold Aligned; rw [scTcbA_val hP hz7]; omega
    · simp only [InObj, HKind.bits]; rw [scTcbA_val hP hz7]; omega
    · unfold Aligned; rw [scCoreA_val hP hz7]; omega
    · simp only [InObj, HKind.bits]; rw [scCoreA_val hP hz7]; omega
  · rw [Heap.scBits_eq hz, Heap.scBits_eq hz']
    simpa [HKind.bits] using hH.disj c _ c' _ hz hz' hne
  · rw [Heap.scBits_eq hz]
    have hne : r ≠ c := fun e => by rw [e] at hr; simp [Heap.replies, hz] at hr
    simpa [HKind.bits] using hH.disj r _ c _ hr hz hne
  · have hP : Placed c z := ⟨by have := hH.lt64 c _ hz; simpa [HKind.bits] using this,
      by simpa [HKind.bits] using hH.align c _ hz, by simpa [HKind.bits] using hH.fits c _ hz⟩
    have hz7 := hH.scmin c z hz
    obtain ⟨h8, h128, -⟩ := sc_lo hP hz7
    refine ⟨?_, c, .sc z, hz, Or.inr (Or.inl ⟨z, rfl⟩), ?_⟩
    · unfold Aligned; rw [scReplyA_val hP hz7]; omega
    · simp only [InObj, HKind.bits]; rw [scReplyA_val hP hz7]; omega

/-- The heap's TCBs are placed. -/
theorem tcbs_of_heap {H : Heap} (hH : HeapOK H) (h0 : H 0#u64 = none) : TcbPlaced H.tcbs := by
  intro t ht
  have h1 := hH.align t _ ht; have h2 := hH.fits t _ ht
  simp only [HKind.bits] at h1 h2
  refine ⟨fun e => ?_, h1, h2⟩
  have : t = 0#u64 := UScalar.eq_of_val_eq (by simpa using e)
  subst this; rw [show H 0#u64 = some .tcb from ht] at h0; simp at h0

/-- The other objects' words lie outside the TCBs and outside nodes that lie
outside every object. -/
theorem omega_of_heap {H : Heap} (hH : HeapOK H) {Cs : Set U64} {s : S}
    (hnode : ∀ c ∈ Cs, ∀ p k, H p = some k → p.val + 2 ^ k.bits ≤ L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ p.val) :
    ∀ a ∈ H.omega, OutsideObjs st H.tcbs Cs s a := by
  rintro a ⟨ha, p, k, hp, hk, hin⟩
  refine ⟨ha, fun t ht => ?_, fun c hc => ?_⟩
  · have hne : p ≠ t := by
      rintro rfl
      rw [show H p = some .tcb from ht] at hp
      cases hp; rcases hk with h | ⟨z, h⟩ | ⟨z, h⟩ | ⟨h, -⟩ <;> cases h
    have e12 : (2 : ℕ) ^ HKind.tcb.bits = 2 ^ 12 := rfl
    rcases hH.disj p k t .tcb hp ht hne with h | h
    · unfold InObj at hin; omega
    · unfold InObj at hin; rw [e12] at h; omega
  · rcases hnode c hc p k hp with h | h
    · unfold InObj at hin; omega
    · unfold InObj at hin; omega

end

end Fl4Proofs.P1
