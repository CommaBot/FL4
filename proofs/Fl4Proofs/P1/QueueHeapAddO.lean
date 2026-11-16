/-
P1: **adding zeroed objects of an untracked kind keeps the invariants** —
CNodes (and any `.other` object): their words join `Ω` (as cap-slot words)
and nothing else (`BlkOK.addOther`).
-/
import Fl4Proofs.P1.QueueHeapAdd
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]
variable {H : Heap} {N : U64 → Prop} {Cs : Set U64} {s : S}

/-- A new `.other` object's word. -/
def NewOW (N : U64 → Prop) (z : Nat) (b : U64) : Prop := Aligned b ∧ ∃ q, N q ∧ q.val ≤ b.val ∧ b.val < q.val + 2 ^ z

theorem AddOKP.frame_eq_other {z : Nat} (A : AddOKP st H N (.other z) Cs s) :
    (H.add N (.other z)).frame = H.frame := by
  ext b; simp only [Heap.frame, Set.mem_setOf_eq]
  constructor
  · rintro ⟨ha, p, k, hp, hkk, hin⟩
    have hne : k ≠ .other z := by rcases hkk with h | ⟨z', h⟩ | ⟨h, -⟩ <;> subst h <;> simp
    exact ⟨ha, p, k, (A.some_ne hne).1 hp, hkk, hin⟩
  · rintro ⟨ha, p, k, hp, hkk, hin⟩
    have hne : k ≠ .other z := by rcases hkk with h | ⟨z', h⟩ | ⟨h, -⟩ <;> subst h <;> simp
    exact ⟨ha, p, k, (A.some_ne hne).2 hp, hkk, hin⟩

theorem AddOKP.omega_other {z : Nat} (A : AddOKP st H N (.other z) Cs s) {b : U64}
    (h : b ∈ (H.add N (.other z)).omega) : b ∈ H.omega ∨ NewOW N z b := by
  obtain ⟨ha, p, k, hp, hk, hin⟩ := h
  rcases Heap.add_eq_some.1 hp with ⟨hn, rfl⟩ | ⟨hn, hp'⟩
  · exact Or.inr ⟨ha, p, hn, hin.1, by have := hin.2; simpa [HKind.bits] using this⟩
  · exact Or.inl ⟨ha, p, k, hp', hk, hin⟩

set_option maxHeartbeats 4000000 in
/-- **`BlkOK` with zeroed `.other` objects (CNodes) added.** -/
theorem BlkOK.addOther {z : Nat} (A : AddOKP st H N (.other z) Cs s) (hH : HeapOK H) {Ac : Set U64}
    (h : BlkOK st H.tcbs Cs H.omega H H.frame H.replies H.scs H.ntfns H.scBits Ac s) :
    BlkOK st (H.add N (.other z)).tcbs Cs (H.add N (.other z)).omega (H.add N (.other z)) (H.add N (.other z)).frame
      (H.add N (.other z)).replies (H.add N (.other z)).scs (H.add N (.other z)).ntfns
      (H.add N (.other z)).scBits Ac s := by
  rw [A.tcbs_eq (by simp), A.replies_eq (by simp), A.scs_eq (by simp), A.ntfns_eq (by simp),
    A.scBits_eq (by simp), A.frame_eq_other]
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have oS := A.omega_sub
  have q : SchedQueuesInv st H.tcbs Cs (H.add N (.other z)).omega (H.add N (.other z)) s Q R :=
    { h0 with
      eps := h0.eps.addOther (by simp) A hH fun a ha => (A.omega_other ha).imp id fun ⟨hal, q, hq, h1, h2⟩ =>
        ⟨q, hq, hal, h1, by simpa [HKind.bits] using h2⟩
      omega := fun a ha => by
        rcases A.omega_other ha with ha | ⟨hal, q, hq, h1, h2⟩
        · exact h0.omega a ha
        · refine ⟨hal, fun t ht => ?_, fun c hc => ?_⟩
          · have := A.disjH q hq t .tcb ht
            rw [show (HKind.tcb).bits = 12 from rfl, show (HKind.other z).bits = z from rfl] at this; omega
          · have := A.nodes q hq c hc; rw [show (HKind.other z).bits = z from rfl] at this; omega }
  have x : XInv st H.tcbs Cs (H.add N (.other z)).omega H.frame H.replies H.scs H.ntfns H.scBits s :=
    ⟨{ hX.1 with scW := fun c hc b ha hin => oS (hX.1.scW c hc b ha hin) }, hX.2⟩
  exact ⟨⟨Q, R, q⟩, hB, x, { hS with sub := fun b hb => oS (hS.sub b hb), ksΩ := fun o h1 h2 => oS (hS.ksΩ o h1 h2) },
    ⟨fun b hb => oS (hSg.sub b hb), hSg.ks, fun o h1 h2 => oS (hSg.ksΩ o h1 h2)⟩⟩

end

end Fl4Proofs.P1
