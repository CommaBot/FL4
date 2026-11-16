/-
P1: **adding zeroed objects keeps the invariants** — the second half of
retype (`RetypeP1Step`), for the zero forms: `H.add N kd` is `H` with new
objects of kind `kd` at the addresses `N`; from `BlkOK` over `H`'s sets, with
the new objects fresh, placed, disjoint from `H`'s objects, each other, the
nodes and the kernel-global area, and their words zero (`AddOK`), `BlkOK`
holds over `H.add N kd`'s sets in the same state.  Endpoints
(`BlkOK.addEp`) first.
-/
import Fl4Proofs.P1.QueueReset
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

/-- `H` with new objects of kind `kd` at `N`. -/
noncomputable def Heap.add (H : Heap) (N : U64 → Prop) (kd : HKind) : Heap := fun q => by
  classical exact if N q then some kd else H q

section
variable {H : Heap} {N : U64 → Prop} {kd : HKind}

theorem Heap.add_eq_some {q : U64} {k : HKind} : H.add N kd q = some k ↔ (N q ∧ k = kd) ∨ (¬ N q ∧ H q = some k) := by
  unfold Heap.add; by_cases h : N q <;> simp [h, eq_comm]

theorem Heap.add_of_not {q : U64} (h : ¬ N q) : H.add N kd q = H q := by
  unfold Heap.add; simp [h]

theorem Heap.add_of_mem {q : U64} (h : N q) : H.add N kd q = some kd := by
  unfold Heap.add; simp [h]

end

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- **The placement of the objects at `N`**: fresh, placed and nonzero
addresses, disjoint from `H`'s objects, from each other, from the nodes and
from the kernel-global area. -/
structure AddOKP (st : machine.Store S) [L : LawfulStore st] (H : Heap) (N : U64 → Prop) (kd : HKind)
    (Cs : Set U64) (s : S) : Prop where
  fresh : ∀ q, N q → H q = none
  align : ∀ q, N q → q.val % 2 ^ kd.bits = 0
  fits : ∀ q, N q → q.val + 2 ^ kd.bits ≤ 2 ^ 64
  nz : ∀ q, N q → q ≠ 0#u64
  disjH : ∀ q, N q → ∀ p kp, H p = some kp → q.val + 2 ^ kd.bits ≤ p.val ∨ p.val + 2 ^ kp.bits ≤ q.val
  disjN : ∀ q q', N q → N q' → q ≠ q' → q.val + 2 ^ kd.bits ≤ q'.val ∨ q'.val + 2 ^ kd.bits ≤ q.val
  nodes : ∀ q, N q → ∀ c ∈ Cs, q.val + 2 ^ kd.bits ≤ L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ q.val
  ks : ∀ q, N q → q.val + 2 ^ kd.bits ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ q.val

/-- **What adding the objects at `N` needs**: their placement (`AddOKP`)
and zero words. -/
structure AddOK (st : machine.Store S) [L : LawfulStore st] (H : Heap) (N : U64 → Prop) (kd : HKind)
    (Cs : Set U64) (s : S) : Prop extends AddOKP st H N kd Cs s where
  zero : ∀ q, N q → ∀ b : U64, Aligned b → q.val ≤ b.val → b.val < q.val + 2 ^ kd.bits → L.mem s b = 0#u64

variable {H : Heap} {N : U64 → Prop} {Cs : Set U64} {s : S}

/-! ## The heap's sets -/

/-- Away from the new kind, the heap is unchanged. -/
theorem AddOKP.some_ne (A : AddOKP st H N kd Cs s) {q : U64} {k : HKind} (hk : k ≠ kd) :
    H.add N kd q = some k ↔ H q = some k := by
  rw [Heap.add_eq_some]
  constructor
  · rintro (⟨-, h⟩ | ⟨-, h⟩)
    · exact absurd h hk
    · exact h
  · intro h
    by_cases hn : N q
    · rw [A.fresh q hn] at h; cases h
    · exact Or.inr ⟨hn, h⟩

theorem AddOKP.tcbs_eq (A : AddOKP st H N kd Cs s) (hk : HKind.tcb ≠ kd) : (H.add N kd).tcbs = H.tcbs := by
  ext q; exact A.some_ne hk
theorem AddOKP.replies_eq (A : AddOKP st H N kd Cs s) (hk : HKind.reply ≠ kd) : (H.add N kd).replies = H.replies := by
  ext q; exact A.some_ne hk
theorem AddOKP.ntfns_eq (A : AddOKP st H N kd Cs s) (hk : HKind.ntfn ≠ kd) : (H.add N kd).ntfns = H.ntfns := by
  ext q; exact A.some_ne hk
theorem AddOKP.scs_eq (A : AddOKP st H N kd Cs s) (hk : ∀ z, HKind.sc z ≠ kd) : (H.add N kd).scs = H.scs := by
  ext q; simp only [Heap.scs, Set.mem_setOf_eq]
  exact ⟨fun ⟨z, h⟩ => ⟨z, (A.some_ne (hk z)).1 h⟩, fun ⟨z, h⟩ => ⟨z, (A.some_ne (hk z)).2 h⟩⟩
theorem AddOKP.scBits_eq (A : AddOKP st H N kd Cs s) (hk : ∀ z, HKind.sc z ≠ kd) : (H.add N kd).scBits = H.scBits := by
  funext q; unfold Heap.scBits
  by_cases hn : N q
  · rw [Heap.add_of_mem hn, A.fresh q hn]
    cases kd with
    | sc z => exact absurd rfl (hk z)
    | _ => rfl
  · rw [Heap.add_of_not hn]

/-- The words of objects of kinds other than `kd` are those of `H`. -/
theorem AddOKP.omega_eq (A : AddOKP st H N kd Cs s) (hk : kd = .ep) : (H.add N kd).omega = H.omega := by
  subst hk
  ext b; simp only [Heap.omega, Set.mem_setOf_eq]
  constructor
  · rintro ⟨ha, p, k, hp, hkk, hin⟩
    have hne : k ≠ .ep := by rcases hkk with h | ⟨z, h⟩ | ⟨z, h⟩ | ⟨h, -⟩ <;> subst h <;> simp
    exact ⟨ha, p, k, (A.some_ne hne).1 hp, hkk, hin⟩
  · rintro ⟨ha, p, k, hp, hkk, hin⟩
    have hne : k ≠ .ep := by rcases hkk with h | ⟨z, h⟩ | ⟨z, h⟩ | ⟨h, -⟩ <;> subst h <;> simp
    exact ⟨ha, p, k, (A.some_ne hne).2 hp, hkk, hin⟩

theorem AddOKP.frame_eq (A : AddOKP st H N kd Cs s) (hk : kd = .ep) : (H.add N kd).frame = H.frame := by
  subst hk
  ext b; simp only [Heap.frame, Set.mem_setOf_eq]
  constructor
  · rintro ⟨ha, p, k, hp, hkk, hin⟩
    have hne : k ≠ .ep := by rcases hkk with h | ⟨z, h⟩ | ⟨h, -⟩ <;> subst h <;> simp
    exact ⟨ha, p, k, (A.some_ne hne).1 hp, hkk, hin⟩
  · rintro ⟨ha, p, k, hp, hkk, hin⟩
    have hne : k ≠ .ep := by rcases hkk with h | ⟨z, h⟩ | ⟨h, -⟩ <;> subst h <;> simp
    exact ⟨ha, p, k, (A.some_ne hne).2 hp, hkk, hin⟩

/-! ## Endpoints: only the endpoint queues see them -/

theorem epHeadA_eq (e : U64) : epHeadA e = e := by
  unfold epHeadA
  apply UScalar.eq_of_val_eq
  have : layout.ep.HEAD.val = 0 := by unfold layout.ep.HEAD; rfl
  rw [core.num.U64.wrapping_add_val_eq, this, Nat.add_zero]
  exact Nat.mod_eq_of_lt (by have := e.hBounds; simpa [U64.size_def, U64.numBits] using this)

/-- **The endpoint queues with zeroed endpoints or notifications added**, over
`Ω` grown by words of the new objects past their first 16 bytes. -/
theorem EpsOK.addEN {kd : HKind} (hkd : kd = .ep ∨ kd = .ntfn) (A : AddOK st H N kd Cs s) (hH : HeapOK H)
    {Ω' : Set U64} (hΩ : ∀ a ∈ Ω', a ∈ H.omega ∨ ∃ q, N q ∧ a.val % 8 = 0 ∧ q.val + 16 ≤ a.val ∧ a.val < q.val + 2 ^ kd.bits)
    (h : EpsOK st H.tcbs Cs H.omega H ∅ s) : EpsOK st H.tcbs Cs Ω' (H.add N kd) ∅ s := by
  classical
  obtain ⟨E, EQ, w1, w2, w3, w4, w5, k1, k2, k3, k4, k5, k6⟩ := h
  have hb4 : 4 ≤ kd.bits := by rcases hkd with rfl | rfl <;> simp [HKind.bits]
  have h16 : 16 ∣ 2 ^ kd.bits := by
    have : 2 ^ kd.bits = 2 ^ 4 * 2 ^ (kd.bits - 4) := by rw [← Nat.pow_add]; congr 1; omega
    rw [this]; exact Dvd.dvd.mul_right (by norm_num) _
  have h16' : 16 ≤ 2 ^ kd.bits := Nat.le_of_dvd (Nat.two_pow_pos _) h16
  have al16 : ∀ q, N q → q.val % 16 = 0 := fun q hq => by
    have := A.align q hq; have := Nat.mod_mod_of_dvd q.val h16; omega
  have nE : ∀ q, N q → q ∉ E := fun q hq he => by
    rcases (k3 q).1 he with h | h <;> rw [A.fresh q hq] at h <;> cases h
  have zw : ∀ q, N q → L.mem s (epHeadA q) = 0#u64 ∧ L.mem s (epTSA q) = 0#u64 := fun q hq => by
    have al := al16 q hq; have fi := A.fits q hq
    have hev := epTSA_val' (e := q) (by omega)
    refine ⟨?_, ?_⟩
    · rw [epHeadA_eq]; exact A.zero q hq q (by unfold Aligned; omega) le_rfl (by omega)
    · exact A.zero q hq _ (by unfold Aligned; rw [hev]; omega) (by rw [hev]; omega) (by rw [hev]; omega)
  refine ⟨{e | e ∈ E ∨ N e}, fun e => if N e then [] else EQ e, fun e he => ?_, fun e he e' he' hne => ?_,
    fun e he a ha => ?_, fun e he t ht => ?_, fun t ht hx hbl => ?_, fun t ht hx hs => ?_, fun t ht hx hs => ?_,
    fun e => ?_, fun e he y hy z hz => ?_, fun e he y hy => ?_, fun e he h0 => ?_⟩
  · rcases he with he | hn
    · have hn : ¬ N e := fun hn => nE e hn he
      simp only [hn, if_false]; exact w1 e he
    · simp only [hn, if_true]
      have al := al16 e hn; have fi := A.fits e hn
      refine ⟨⟨by omega, by omega, fun t ht => ?_⟩, ⟨fun c hc => ?_, ?_⟩, ?_⟩
      · have := A.disjH e hn t .tcb ht; rw [show (HKind.tcb).bits = 12 from rfl] at this; omega
      · have := A.nodes e hn c hc; omega
      · have := A.ks e hn; omega
      · obtain ⟨z1, z2⟩ := zw e hn
        unfold LawfulStore.epQ; rw [z1, z2]
        exact QueueRel.nil
  · rcases he with he | hn <;> rcases he' with he' | hn'
    · exact w2 e he e' he' hne
    · rcases (k3 e).1 he with h | h
      · have := A.disjH e' hn' e .ep h; rw [show (HKind.ep).bits = 4 from rfl] at this; omega
      · have := A.disjH e' hn' e .ntfn h; rw [show (HKind.ntfn).bits = 6 from rfl] at this; omega
    · rcases (k3 e').1 he' with h | h
      · have := A.disjH e hn e' .ep h; rw [show (HKind.ep).bits = 4 from rfl] at this; omega
      · have := A.disjH e hn e' .ntfn h; rw [show (HKind.ntfn).bits = 6 from rfl] at this; omega
    · have := A.disjN e e' hn hn' hne; omega
  · have hal : a.val % 8 = 0 ∨ True := Or.inr trivial
    rcases hΩ a ha with ha' | ⟨q, hq, ha8, hq1, hq2⟩
    · rcases he with he | hn
      · exact w3 e he a ha'
      · obtain ⟨hal, p, k, hp, -, hin⟩ := ha'
        have al := al16 e hn
        have := A.disjH e hn p k hp
        have h1 := hin.1; have h2 := hin.2
        unfold Aligned at hal
        omega
    · have aq := al16 q hq
      rcases he with he | hn
      · rcases (k3 e).1 he with h | h
        · have := A.disjH q hq e .ep h; rw [show (HKind.ep).bits = 4 from rfl] at this
          have := hH.align e .ep h; rw [show (HKind.ep).bits = 4 from rfl] at this; omega
        · have := A.disjH q hq e .ntfn h; rw [show (HKind.ntfn).bits = 6 from rfl] at this
          have := hH.align e .ntfn h; rw [show (HKind.ntfn).bits = 6 from rfl] at this; omega
      · by_cases hqe : q = e
        · subst hqe; omega
        · have := A.disjN e q hn hq (Ne.symm hqe); have := al16 e hn; omega
  · by_cases hn : N e
    · simp [hn] at ht
    · simp only [hn, if_false] at ht
      exact w4 e (he.resolve_right hn) t ht
  · obtain ⟨b1, b2⟩ := w5 t ht hx hbl
    have hn : ¬ N (L.mem s (blockA t)) := fun hn => nE _ hn b1
    exact ⟨Or.inl b1, by simp only [hn, if_false]; exact b2⟩
  · obtain ⟨b1, -⟩ := w5 t ht hx (by rcases hs with e | e; exact Or.inl e; exact Or.inr (Or.inl e))
    have hn : ¬ N (L.mem s (blockA t)) := fun hn => nE _ hn b1
    rw [Heap.add_of_not hn]; exact k1 t ht hx hs
  · obtain ⟨b1, -⟩ := w5 t ht hx (Or.inr (Or.inr hs))
    have hn : ¬ N (L.mem s (blockA t)) := fun hn => nE _ hn b1
    rw [Heap.add_of_not hn]; exact k2 t ht hx hs
  · show (e ∈ E ∨ N e) ↔ _
    by_cases hn : N e
    · rw [Heap.add_of_mem hn]; rcases hkd with rfl | rfl <;> simp [hn]
    · rw [Heap.add_of_not hn, ← k3 e]; simp [hn]
  · by_cases hn : N e
    · simp [hn] at hy
    · simp only [hn, if_false] at hy hz; exact k4 e (he.resolve_right hn) y hy z hz
  · by_cases hn : N e
    · simp [hn] at hy
    · simp only [hn, if_false] at hy; exact k5 e (he.resolve_right hn) y hy
  · by_cases hn : N e
    · rw [Heap.add_of_mem hn]
      obtain ⟨-, z2⟩ := zw e hn
      have e0 : L.epState s e = 0#u64 := by unfold LawfulStore.epState; rw [z2]; rfl
      exact ⟨fun _ => e0, fun _ => by rw [e0]; decide⟩
    · rw [Heap.add_of_not hn]; simp only [hn, if_false] at h0; exact k6 e (he.resolve_right hn) h0

/-- **`BlkOK` with zeroed endpoints added.** -/
theorem BlkOK.addEp (A : AddOK st H N .ep Cs s) (hH : HeapOK H) {Ac : Set U64}
    (h : BlkOK st H.tcbs Cs H.omega H H.frame H.replies H.scs H.ntfns H.scBits Ac s) :
    BlkOK st (H.add N .ep).tcbs Cs (H.add N .ep).omega (H.add N .ep) (H.add N .ep).frame (H.add N .ep).replies
      (H.add N .ep).scs (H.add N .ep).ntfns (H.add N .ep).scBits Ac s := by
  rw [A.tcbs_eq (by simp), A.omega_eq rfl, A.frame_eq rfl, A.replies_eq (by simp), A.scs_eq (by simp),
    A.ntfns_eq (by simp), A.scBits_eq (by simp)]
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  exact ⟨⟨Q, R, { h0 with eps := h0.eps.addEN (Or.inl rfl) A hH (fun a ha => Or.inl ha) }⟩, hB, hX, hS, hSg⟩


/-! ## Notifications: their frame words join `Ω` and `Sg` -/

/-- A new notification's frame word. -/
def NewNtW (N : U64 → Prop) (b : U64) : Prop := Aligned b ∧ ∃ n, N n ∧ NtfnW n b

theorem ntfnW_vals {n b : U64} (hP : n.val % 64 = 0 ∧ n.val + 64 ≤ 2 ^ 64) (h : NtfnW n b) :
    n.val + 16 ≤ b.val ∧ b.val + 8 ≤ n.val + 64 := by
  rcases h with e | e | e <;> subst e
  · rw [ntfnScA_val hP]; omega
  · rw [ntfnBdA_val hP]; omega
  · rw [ntfnBtA_val hP]; omega

theorem AddOKP.ntP (A : AddOKP st H N .ntfn Cs s) {n : U64} (hn : N n) : n.val % 64 = 0 ∧ n.val + 64 ≤ 2 ^ 64 :=
  ⟨A.align n hn, A.fits n hn⟩

theorem AddOKP.omega_sub_ntfn (A : AddOKP st H N .ntfn Cs s) : H.omega ⊆ (H.add N .ntfn).omega := by
  rintro b ⟨ha, p, k, hp, hk, hin⟩
  exact ⟨ha, p, k, Heap.add_eq_some.2 (Or.inr ⟨fun hn => (by rw [A.fresh p hn] at hp; cases hp), hp⟩), hk, hin⟩

theorem AddOKP.frame_sub_ntfn (A : AddOKP st H N .ntfn Cs s) : H.frame ⊆ (H.add N .ntfn).frame := by
  rintro b ⟨ha, p, k, hp, hk, hin⟩
  exact ⟨ha, p, k, Heap.add_eq_some.2 (Or.inr ⟨fun hn => (by rw [A.fresh p hn] at hp; cases hp), hp⟩), hk, hin⟩

theorem AddOKP.newNt_frame (A : AddOKP st H N .ntfn Cs s) {b : U64} (h : NewNtW N b) : b ∈ (H.add N .ntfn).frame := by
  obtain ⟨ha, n, hn, hw⟩ := h
  have hv := ntfnW_vals (A.ntP hn) hw
  exact ⟨ha, n, .ntfn, Heap.add_of_mem hn, Or.inr (Or.inr ⟨rfl, hw⟩), ⟨by omega, by simp only [HKind.bits]; omega⟩⟩

theorem AddOKP.omega_ntfn (A : AddOKP st H N .ntfn Cs s) {b : U64} (h : b ∈ (H.add N .ntfn).omega) :
    b ∈ H.omega ∨ NewNtW N b := by
  obtain ⟨ha, p, k, hp, hk, hin⟩ := h
  rcases Heap.add_eq_some.1 hp with ⟨hn, rfl⟩ | ⟨hn, hp'⟩
  · rcases hk with h | ⟨z, h⟩ | ⟨z, h⟩ | ⟨-, hw⟩
    · cases h
    · cases h
    · cases h
    · exact Or.inr ⟨ha, p, hn, hw⟩
  · exact Or.inl ⟨ha, p, k, hp', hk, hin⟩

theorem AddOKP.frame_ntfn (A : AddOKP st H N .ntfn Cs s) {b : U64} (h : b ∈ (H.add N .ntfn).frame) :
    b ∈ H.frame ∨ NewNtW N b := by
  obtain ⟨ha, p, k, hp, hk, hin⟩ := h
  rcases Heap.add_eq_some.1 hp with ⟨hn, rfl⟩ | ⟨hn, hp'⟩
  · rcases hk with h | ⟨z, h⟩ | ⟨-, hw⟩
    · cases h
    · cases h
    · exact Or.inr ⟨ha, p, hn, hw⟩
  · exact Or.inl ⟨ha, p, k, hp', hk, hin⟩

theorem AddOKP.ntfns_ntfn (A : AddOKP st H N .ntfn Cs s) {n : U64} :
    n ∈ (H.add N .ntfn).ntfns ↔ n ∈ H.ntfns ∨ N n := by
  simp only [Heap.ntfns, Set.mem_setOf_eq, Heap.add_eq_some]
  constructor
  · rintro (⟨hn, -⟩ | ⟨-, h⟩); · exact Or.inr hn
    · exact Or.inl h
  · rintro (h | hn)
    · exact Or.inr ⟨fun hn => (by rw [A.fresh n hn] at h; cases h), h⟩
    · exact Or.inl ⟨hn, trivial⟩

set_option maxHeartbeats 4000000 in
/-- **`BlkOK` with zeroed notifications added.** -/
theorem BlkOK.addNtfn (A : AddOK st H N .ntfn Cs s) (hH : HeapOK H) {Ac : Set U64}
    (h : BlkOK st H.tcbs Cs H.omega H H.frame H.replies H.scs H.ntfns H.scBits Ac s) :
    BlkOK st (H.add N .ntfn).tcbs Cs (H.add N .ntfn).omega (H.add N .ntfn) (H.add N .ntfn).frame
      (H.add N .ntfn).replies (H.add N .ntfn).scs (H.add N .ntfn).ntfns (H.add N .ntfn).scBits Ac s := by
  rw [A.tcbs_eq (by simp), A.replies_eq (by simp), A.scs_eq (by simp), A.scBits_eq (by simp)]
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hO := hX.1
  have NT : ∀ n, n ∈ (H.add N .ntfn).ntfns ↔ n ∈ H.ntfns ∨ N n := fun n => A.ntfns_ntfn
  have oS := A.omega_sub_ntfn
  have fS := A.frame_sub_ntfn
  have hz : ∀ n, N n → ∀ b, NtfnW n b → L.mem s b = 0#u64 := fun n hn b hw => by
    have hv := ntfnW_vals (A.ntP hn) hw
    have ha : Aligned b := by
      unfold Aligned; have := (A.ntP hn).1
      rcases hw with e | e | e <;> subst e
      · rw [ntfnScA_val (A.ntP hn)]; omega
      · rw [ntfnBdA_val (A.ntP hn)]; omega
      · rw [ntfnBtA_val (A.ntP hn)]; omega
    exact A.zero n hn b ha (by omega) (by simp only [HKind.bits]; omega)
  have nwA : ∀ n, N n → ∀ b, NtfnW n b → Aligned b := fun n hn b hw => by
    unfold Aligned; have := (A.ntP hn).1
    rcases hw with e | e | e <;> subst e
    · rw [ntfnScA_val (A.ntP hn)]; omega
    · rw [ntfnBdA_val (A.ntP hn)]; omega
    · rw [ntfnBtA_val (A.ntP hn)]; omega
  have newF : ∀ n, N n → ∀ b, NtfnW n b → b ∈ (H.add N .ntfn).frame := fun n hn b hw =>
    A.newNt_frame ⟨nwA n hn b hw, n, hn, hw⟩
  -- the scheduler queues
  have q : SchedQueuesInv st H.tcbs Cs (H.add N .ntfn).omega (H.add N .ntfn) s Q R :=
    { h0 with
      eps := h0.eps.addEN (Or.inr rfl) A hH fun a ha => (A.omega_ntfn ha).imp id fun ⟨hal, n, hn, hw⟩ =>
        ⟨n, hn, hal, (ntfnW_vals (A.ntP hn) hw).1, by have := (ntfnW_vals (A.ntP hn) hw).2; simp only [HKind.bits]; omega⟩
      omega := fun a ha => by
        rcases A.omega_ntfn ha with ha | ⟨hal, n, hn, hw⟩
        · exact h0.omega a ha
        · have hv := ntfnW_vals (A.ntP hn) hw
          refine ⟨hal, fun t ht => ?_, fun c hc => ?_⟩
          · have := A.disjH n hn t .tcb ht
            rw [show (HKind.tcb).bits = 12 from rfl, show (HKind.ntfn).bits = 6 from rfl] at this; omega
          · have := A.nodes n hn c hc; rw [show (HKind.ntfn).bits = 6 from rfl] at this; omega }
  -- the objects
  have obj : ObjsOK st (H.add N .ntfn).omega (H.add N .ntfn).frame H.replies H.scs (H.add N .ntfn).ntfns H.scBits s := by
    refine ⟨hO.rp, hO.sc, fun r hr b ha h1 h2 => fS (hO.rpW r hr b ha h1 h2),
      fun c hc b ha hin => oS (hO.scW c hc b ha hin), fun c hc => ⟨fS (hO.fixW c hc).1, fS (hO.fixW c hc).2⟩,
      hO.scDisj, hO.rpSc, fun c hc => fS (hO.repW c hc), fun n hn => ?_, fun n hn r hr => ?_, fun n hn c hc => ?_,
      fun n hn => ?_, fun n hn => ?_, fun n hn => ?_, fun n hn r hr => ?_, fun n hn c hc => ?_,
      fun c hc => fS (hO.snW c hc), fun c hc => fS (hO.syW c hc), fun c hc => fS (hO.mxW c hc),
      fun n hn => ?_, hO.rp0⟩
    all_goals rcases (NT n).1 hn with hn | hn
    · exact fS (hO.ntW n hn)
    · exact newF n hn _ (Or.inl rfl)
    · exact hO.ntRp n hn r hr
    · have := A.disjH n hn r .reply hr; rw [ntfnScA_val (A.ntP hn)]
      rw [show (HKind.ntfn).bits = 6 from rfl, show (HKind.reply).bits = 5 from rfl] at this; omega
    · exact hO.ntSc n hn c hc
    · obtain ⟨z, hz'⟩ := hc
      have e : H.scBits c = z := by unfold Heap.scBits; rw [hz']
      have := A.disjH n hn c (.sc z) hz'; rw [ntfnScA_val (A.ntP hn), e]
      rw [show (HKind.ntfn).bits = 6 from rfl, show (HKind.sc z).bits = z from rfl] at this; omega
    · exact hO.ntAl n hn
    · exact nwA n hn _ (Or.inl rfl)
    · exact hO.ntP n hn
    · exact A.ntP hn
    · exact ⟨fS (hO.ntB n hn).1, fS (hO.ntB n hn).2⟩
    · exact ⟨newF n hn _ (Or.inr (Or.inl rfl)), newF n hn _ (Or.inr (Or.inr rfl))⟩
    · exact hO.ntORp n hn r hr
    · have := A.disjH n hn r .reply hr
      rw [show (HKind.ntfn).bits = 6 from rfl, show (HKind.reply).bits = 5 from rfl] at this; omega
    · exact hO.ntOSc n hn c hc
    · obtain ⟨z, hz'⟩ := hc
      have e : H.scBits c = z := by unfold Heap.scBits; rw [hz']
      have := A.disjH n hn c (.sc z) hz'; rw [e]
      rw [show (HKind.ntfn).bits = 6 from rfl, show (HKind.sc z).bits = z from rfl] at this; omega
    · exact hO.nt0 n hn
    · exact A.nz n hn
  have ext : ScExtra st H.tcbs Cs H.scs (H.add N .ntfn).ntfns s :=
    { hX.2.2 with
      bnd := fun t ht h0' => (NT _).2 (Or.inl (hX.2.2.bnd t ht h0'))
      nsc := fun n hn h0' => by
        rcases (NT n).1 hn with hn | hn
        · exact hX.2.2.nsc n hn h0'
        · exact absurd (hz n hn _ (Or.inl rfl)) h0'
      ntb := fun n hn => by
        rcases (NT n).1 hn with hn | hn
        · exact hX.2.2.ntb n hn
        · exact Or.inl (hz n hn _ (Or.inr (Or.inr rfl)))
      scn := fun c hc h0' => (NT _).2 (Or.inl (hX.2.2.scn c hc h0')) }
  have sub : ∀ b ∈ (H.add N .ntfn).frame, b ∈ (H.add N .ntfn).omega := fun b hb => Heap.frame_omega hb
  have ks : ∀ b ∈ (H.add N .ntfn).frame, b.val + 8 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ b.val := by
    intro b hb
    rcases A.frame_ntfn hb with hb | ⟨-, n, hn, hw⟩
    · exact hSg.ks b hb
    · have hv := ntfnW_vals (A.ntP hn) hw
      have := A.ks n hn; rw [show (HKind.ntfn).bits = 6 from rfl] at this; omega
  have kO : ∀ o : U64, o.val < 13568 → o.val % 8 = 0 →
      core.num.U64.wrapping_add (L.ksb s) o ∈ (H.add N .ntfn).omega := fun o h1 h2 => oS (hSg.ksΩ o h1 h2)
  have x : XInv st H.tcbs Cs (H.add N .ntfn).omega (H.add N .ntfn).frame H.replies H.scs (H.add N .ntfn).ntfns
      H.scBits s := ⟨obj, hX.2.1, ext⟩
  have sc : SCsOK st H.tcbs (H.add N .ntfn).omega (H.add N .ntfn).frame H.scs H.scBits Ac s :=
    ⟨sub, ks, kO, hS.disj,
      fun c hc => ⟨(hS.all c hc).1, fS (hS.all c hc).2.1, fun b ha hin => fS ((hS.all c hc).2.2 b ha hin)⟩,
      hS.act, hS.spor, fun c hc => fS (hS.spSg c hc), hS.rep, fun c hc => fS (hS.repSg c hc)⟩
  exact ⟨⟨Q, R, q⟩, hB, x, sc, ⟨sub, ks, kO⟩⟩


/-! ## Other kinds: the endpoint queues are unchanged -/

/-- **The endpoint queues with objects of another kind added**, over `Ω` grown
by words of the new objects. -/
theorem EpsOK.addOther {kd : HKind} (hkd : HKind.ep ≠ kd ∧ HKind.ntfn ≠ kd) (A : AddOKP st H N kd Cs s)
    (hH : HeapOK H) {Ω' : Set U64}
    (hΩ : ∀ a ∈ Ω', a ∈ H.omega ∨ ∃ q, N q ∧ a.val % 8 = 0 ∧ q.val ≤ a.val ∧ a.val < q.val + 2 ^ kd.bits)
    (h : EpsOK st H.tcbs Cs H.omega H ∅ s) : EpsOK st H.tcbs Cs Ω' (H.add N kd) ∅ s := by
  obtain ⟨E, EQ, w1, w2, w3, w4, w5, k1, k2, k3, k4, k5, k6⟩ := h
  have nE : ∀ q, N q → q ∉ E := fun q hq he => by
    rcases (k3 q).1 he with h | h <;> rw [A.fresh q hq] at h <;> cases h
  refine ⟨E, EQ, w1, w2, fun e he a ha => ?_, w4, w5, fun t ht hx hs => ?_, fun t ht hx hs => ?_,
    fun e => ?_, k4, k5, fun e he h0 => ?_⟩
  · rcases hΩ a ha with ha' | ⟨q, hq, ha8, hq1, hq2⟩
    · exact w3 e he a ha'
    · rcases (k3 e).1 he with h | h
      · have := A.disjH q hq e .ep h; rw [show (HKind.ep).bits = 4 from rfl] at this
        have := hH.align e .ep h; rw [show (HKind.ep).bits = 4 from rfl] at this; omega
      · have := A.disjH q hq e .ntfn h; rw [show (HKind.ntfn).bits = 6 from rfl] at this
        have := hH.align e .ntfn h; rw [show (HKind.ntfn).bits = 6 from rfl] at this; omega
  · obtain ⟨b1, -⟩ := w5 t ht hx (by rcases hs with e | e; exact Or.inl e; exact Or.inr (Or.inl e))
    rw [Heap.add_of_not fun hn => nE _ hn b1]; exact k1 t ht hx hs
  · obtain ⟨b1, -⟩ := w5 t ht hx (Or.inr (Or.inr hs))
    rw [Heap.add_of_not fun hn => nE _ hn b1]; exact k2 t ht hx hs
  · rw [k3 e, A.some_ne hkd.1, A.some_ne hkd.2]
  · rw [Heap.add_of_not fun hn => nE _ hn he]; exact k6 e he h0

/-! ## Replies: their words join `Ω` and `Sg` -/

/-- A new reply's word. -/
def NewRpW (N : U64 → Prop) (b : U64) : Prop := Aligned b ∧ ∃ r, N r ∧ r.val ≤ b.val ∧ b.val < r.val + 32

theorem AddOKP.omega_sub (A : AddOKP st H N kd Cs s) : H.omega ⊆ (H.add N kd).omega := by
  rintro b ⟨ha, p, k, hp, hk, hin⟩
  exact ⟨ha, p, k, Heap.add_eq_some.2 (Or.inr ⟨fun hn => (by rw [A.fresh p hn] at hp; cases hp), hp⟩), hk, hin⟩

theorem AddOKP.frame_sub (A : AddOKP st H N kd Cs s) : H.frame ⊆ (H.add N kd).frame := by
  rintro b ⟨ha, p, k, hp, hk, hin⟩
  exact ⟨ha, p, k, Heap.add_eq_some.2 (Or.inr ⟨fun hn => (by rw [A.fresh p hn] at hp; cases hp), hp⟩), hk, hin⟩

theorem AddOKP.newRp_frame (A : AddOKP st H N .reply Cs s) {b : U64} (h : NewRpW N b) : b ∈ (H.add N .reply).frame := by
  obtain ⟨ha, r, hr, h1, h2⟩ := h
  exact ⟨ha, r, .reply, Heap.add_of_mem hr, Or.inl rfl, ⟨h1, by rw [show (HKind.reply).bits = 5 from rfl]; omega⟩⟩

theorem AddOKP.omega_reply (A : AddOKP st H N .reply Cs s) {b : U64} (h : b ∈ (H.add N .reply).omega) :
    b ∈ H.omega ∨ NewRpW N b := by
  obtain ⟨ha, p, k, hp, hk, hin⟩ := h
  rcases Heap.add_eq_some.1 hp with ⟨hn, rfl⟩ | ⟨hn, hp'⟩
  · exact Or.inr ⟨ha, p, hn, hin.1, by have := hin.2; rw [show (HKind.reply).bits = 5 from rfl] at this; omega⟩
  · exact Or.inl ⟨ha, p, k, hp', hk, hin⟩

theorem AddOKP.frame_reply (A : AddOKP st H N .reply Cs s) {b : U64} (h : b ∈ (H.add N .reply).frame) :
    b ∈ H.frame ∨ NewRpW N b := by
  obtain ⟨ha, p, k, hp, hk, hin⟩ := h
  rcases Heap.add_eq_some.1 hp with ⟨hn, rfl⟩ | ⟨hn, hp'⟩
  · exact Or.inr ⟨ha, p, hn, hin.1, by have := hin.2; rw [show (HKind.reply).bits = 5 from rfl] at this; omega⟩
  · exact Or.inl ⟨ha, p, k, hp', hk, hin⟩

theorem AddOKP.replies_reply (A : AddOKP st H N .reply Cs s) {r : U64} :
    r ∈ (H.add N .reply).replies ↔ r ∈ H.replies ∨ N r := by
  simp only [Heap.replies, Set.mem_setOf_eq, Heap.add_eq_some]
  constructor
  · rintro (⟨hn, -⟩ | ⟨-, h⟩); · exact Or.inr hn
    · exact Or.inl h
  · rintro (h | hn)
    · exact Or.inr ⟨fun hn => (by rw [A.fresh r hn] at h; cases h), h⟩
    · exact Or.inl ⟨hn, trivial⟩

set_option maxHeartbeats 4000000 in
/-- **`BlkOK` with zeroed reply objects added.** -/
theorem BlkOK.addReply (A : AddOK st H N .reply Cs s) (hH : HeapOK H) {Ac : Set U64}
    (h : BlkOK st H.tcbs Cs H.omega H H.frame H.replies H.scs H.ntfns H.scBits Ac s) :
    BlkOK st (H.add N .reply).tcbs Cs (H.add N .reply).omega (H.add N .reply) (H.add N .reply).frame
      (H.add N .reply).replies (H.add N .reply).scs (H.add N .reply).ntfns (H.add N .reply).scBits Ac s := by
  rw [A.tcbs_eq (by simp), A.ntfns_eq (by simp), A.scs_eq (by simp), A.scBits_eq (by simp)]
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hO := hX.1
  have RP : ∀ r, r ∈ (H.add N .reply).replies ↔ r ∈ H.replies ∨ N r := fun r => A.replies_reply
  have oS := A.omega_sub
  have fS := A.frame_sub
  have rP : ∀ r, N r → r.val % 32 = 0 ∧ r.val + 32 ≤ 2 ^ 64 := fun r hr => ⟨A.align r hr, A.fits r hr⟩
  have hz : ∀ r, N r → ∀ o : U64, o.val < 32 → o.val % 8 = 0 → L.mem s (core.num.U64.wrapping_add r o) = 0#u64 :=
    fun r hr o ho h8 => by
      have hv := rp_val (rP r hr) ho
      exact A.zero r hr _ (by unfold Aligned; rw [hv]; have := (rP r hr).1; omega) (by rw [hv]; omega)
        (by rw [hv, show (HKind.reply).bits = 5 from rfl]; omega)
  have zT : ∀ r, N r → L.mem s (rTcbA r) = 0#u64 := fun r hr => by
    unfold rTcbA; exact hz r hr _ (by simp [layout.reply.TCB]) (by simp [layout.reply.TCB])
  have zP : ∀ r, N r → L.mem s (rPrevA r) = 0#u64 := fun r hr => by
    unfold rPrevA; exact hz r hr _ (by simp [layout.reply.PREV]) (by simp [layout.reply.PREV])
  have zN : ∀ r, N r → L.mem s (rNextA r) = 0#u64 := fun r hr => by
    unfold rNextA; exact hz r hr _ (by simp [layout.reply.NEXT]) (by simp [layout.reply.NEXT])
  have q : SchedQueuesInv st H.tcbs Cs (H.add N .reply).omega (H.add N .reply) s Q R :=
    { h0 with
      eps := h0.eps.addOther (by simp) A.toAddOKP hH fun a ha => (A.omega_reply ha).imp id fun ⟨hal, r, hr, h1, h2⟩ =>
        ⟨r, hr, hal, h1, by rw [show (HKind.reply).bits = 5 from rfl]; omega⟩
      omega := fun a ha => by
        rcases A.omega_reply ha with ha | ⟨hal, r, hr, h1, h2⟩
        · exact h0.omega a ha
        · refine ⟨hal, fun t ht => ?_, fun c hc => ?_⟩
          · have := A.disjH r hr t .tcb ht
            rw [show (HKind.tcb).bits = 12 from rfl, show (HKind.reply).bits = 5 from rfl] at this; omega
          · have := A.nodes r hr c hc; rw [show (HKind.reply).bits = 5 from rfl] at this; omega }
  have obj : ObjsOK st (H.add N .reply).omega (H.add N .reply).frame (H.add N .reply).replies H.scs H.ntfns
      H.scBits s := by
    refine ⟨fun r hr => ?_, hO.sc, fun r hr b ha h1 h2 => ?_, fun c hc b ha hin => oS (hO.scW c hc b ha hin),
      fun c hc => ⟨fS (hO.fixW c hc).1, fS (hO.fixW c hc).2⟩, hO.scDisj, fun r hr c hc => ?_,
      fun c hc => fS (hO.repW c hc), fun n hn => fS (hO.ntW n hn), fun n hn r hr => ?_, hO.ntSc, hO.ntAl, hO.ntP,
      fun n hn => ⟨fS (hO.ntB n hn).1, fS (hO.ntB n hn).2⟩, fun n hn r hr => ?_, hO.ntOSc,
      fun c hc => fS (hO.snW c hc), fun c hc => fS (hO.syW c hc), fun c hc => fS (hO.mxW c hc), hO.nt0,
      fun r hr => ?_⟩
    all_goals rcases (RP r).1 hr with hr | hr
    · exact hO.rp r hr
    · exact rP r hr
    · exact fS (hO.rpW r hr b ha h1 h2)
    · exact A.newRp_frame ⟨ha, r, hr, h1, h2⟩
    · exact hO.rpSc r hr c hc
    · obtain ⟨z, hz'⟩ := hc
      have e : H.scBits c = z := by unfold Heap.scBits; rw [hz']
      have := A.disjH r hr c (.sc z) hz'; rw [e]
      rw [show (HKind.reply).bits = 5 from rfl, show (HKind.sc z).bits = z from rfl] at this; omega
    · exact hO.ntRp n hn r hr
    · have := A.disjH r hr n .ntfn hn; rw [ntfnScA_val (hO.ntP n hn)]
      rw [show (HKind.reply).bits = 5 from rfl, show (HKind.ntfn).bits = 6 from rfl] at this; omega
    · exact hO.ntORp n hn r hr
    · have := A.disjH r hr n .ntfn hn
      rw [show (HKind.reply).bits = 5 from rfl, show (HKind.ntfn).bits = 6 from rfl] at this; omega
    · exact hO.rp0 r hr
    · exact A.nz r hr
  have rinv : ReplyInv st H.tcbs (H.add N .reply).replies H.scs s := by
    obtain ⟨⟨r1, r2, r3, r4, r5, r6, r7⟩, r8⟩ := hX.2.1
    refine ⟨⟨fun t ht hs => ?_, fun t ht hs h0' => ?_, fun r hr h0' => ?_, fun r hr h0' => ?_, fun r hr h0' => ?_,
      fun c hc h0' => (RP _).2 (Or.inl (r6 c hc h0')), r7⟩, fun r hr hb h0' => ?_⟩
    · obtain ⟨a1, a2⟩ := r1 t ht hs; exact ⟨(RP _).2 (Or.inl a1), a2⟩
    · obtain ⟨a1, a2⟩ := r2 t ht hs h0'; exact ⟨(RP _).2 (Or.inl a1), a2⟩
    · rcases (RP r).1 hr with hr | hr
      · obtain ⟨a1, a2⟩ := r3 r hr h0'
        exact ⟨a1, fun hb => (RP _).2 (Or.inl (a2 hb))⟩
      · rw [zN r hr] at h0'; exact absurd (zero_or_masked) h0'
    · rcases (RP r).1 hr with hr | hr
      · exact (RP _).2 (Or.inl (r4 r hr h0'))
      · rw [zP r hr] at h0'; exact absurd (zero_or_masked) h0'
    · rcases (RP r).1 hr with hr | hr
      · exact r5 r hr h0'
      · exact absurd (zT r hr) h0'
    · rcases (RP r).1 hr with hr | hr
      · exact r8 r hr hb h0'
      · rw [zN r hr] at h0'; exact absurd (zero_or_masked) h0'
  have sub : ∀ b ∈ (H.add N .reply).frame, b ∈ (H.add N .reply).omega := fun b hb => Heap.frame_omega hb
  have ks : ∀ b ∈ (H.add N .reply).frame, b.val + 8 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ b.val := by
    intro b hb
    rcases A.frame_reply hb with hb | ⟨hal, r, hr, h1, h2⟩
    · exact hSg.ks b hb
    · have := A.ks r hr; rw [show (HKind.reply).bits = 5 from rfl] at this
      have := (rP r hr).1; unfold Aligned at hal; omega
  have kO : ∀ o : U64, o.val < 13568 → o.val % 8 = 0 →
      core.num.U64.wrapping_add (L.ksb s) o ∈ (H.add N .reply).omega := fun o h1 h2 => oS (hSg.ksΩ o h1 h2)
  have x : XInv st H.tcbs Cs (H.add N .reply).omega (H.add N .reply).frame (H.add N .reply).replies H.scs H.ntfns
      H.scBits s := ⟨obj, rinv, hX.2.2⟩
  have sc : SCsOK st H.tcbs (H.add N .reply).omega (H.add N .reply).frame H.scs H.scBits Ac s :=
    ⟨sub, ks, kO, hS.disj,
      fun c hc => ⟨(hS.all c hc).1, fS (hS.all c hc).2.1, fun b ha hin => fS ((hS.all c hc).2.2 b ha hin)⟩,
      hS.act, hS.spor, fun c hc => fS (hS.spSg c hc), hS.rep, fun c hc => fS (hS.repSg c hc)⟩
  exact ⟨⟨Q, R, q⟩, hB, x, sc, ⟨sub, ks, kO⟩⟩

end

end Fl4Proofs.P1
