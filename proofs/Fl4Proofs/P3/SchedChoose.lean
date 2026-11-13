/-
P3 (DESIGN.md §9), scheduler: **`choose_thread`'s pick refines l4v
`choose_thread`'s** (Schedule_A): on related states,

* `choose_empty`: FL4's L1 bitmap word is 0 exactly when every ready queue
  of the spec's current domain is empty (FL4 then switches to the idle
  thread, the spec `switch_to_idle_thread`);
* `choose_pick_refines`: otherwise the thread FL4's `highest_prio` / head
  lookup picks is `the (hd (max_non_empty_queue queues))`, the one the spec
  passes to `guarded_switch_to`.

The switch itself (`switch_to_thread`: address space and FPU, then
`tcb_sched_dequeue` and `cur_thread`) is not done here: it needs a relation
for the architecture state (`arch_switch_to_thread`), and the spec's
`guarded_switch_to` asserts the pick is schedulable and in the current
domain (l4v `valid_queues`, an invariant not in `SchedRel`).
-/
import Fl4Proofs.P3.SchedAppend
import Fl4Proofs.P1.QueueChoose
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

/-- `set_max` of a set with a greatest element is that element. -/
theorem setMax_eq {S : Set Fl4Spec.Priority} {m : Fl4Spec.Priority} (hm : m ∈ S) (hle : ∀ x ∈ S, x ≤ m) :
    Fl4Spec.setMax S = m := by
  have hu : ∃! x, x ∈ S ∧ ∀ y ∈ S, y ≤ x :=
    ⟨m, ⟨hm, hle⟩, fun y hy => BitVec.le_antisymm (hle y hy.1) (hy.2 m hm)⟩
  unfold Fl4Spec.setMax Fl4Spec.The
  rw [dite_t hu]
  exact hu.unique (Classical.choose_spec hu).1 ⟨hm, hle⟩

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

theorem prio_of_spec (q : Fl4Spec.Priority) : ∃ p : U64, p.val < 256 ∧ specPrio p = q := by
  refine ⟨⟨BitVec.ofNat 64 q.toNat⟩, ?_, ?_⟩
  · have := q.isLt
    show (BitVec.ofNat 64 q.toNat).toNat < 256
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact this
  · apply BitVec.eq_of_toNat_eq
    show (BitVec.ofNat 8 (BitVec.ofNat 64 q.toNat).toNat).toNat = q.toNat
    have := q.isLt
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt this]

theorem specPrio_le {p q : U64} (hp : p.val < 256) (hq : q.val < 256) :
    specPrio p ≤ specPrio q ↔ p.val ≤ q.val := by
  rw [BitVec.le_def]
  simp only [specPrio, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hq]

/-- The L1 bitmap word is 0 iff every ready queue is empty. -/
theorem choose_empty {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) :
    L.l1W s c = 0#u64 ↔ ∀ prio, σ.readyQueues σ.curDomain prio = [] := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  rw [hs.curDom.1]
  have hB := hc.ready.2
  have hall : (∀ prio, σ.readyQueues 0 prio = []) ↔ ∀ p : U64, p.val < 256 → Q p = [] := by
    constructor
    · intro h p hp; have := h (specPrio p); rw [hs.rq p hp] at this; exact List.map_eq_nil_iff.1 this
    · intro h q
      obtain ⟨p, hp, rfl⟩ := prio_of_spec q
      rw [hs.rq p hp, h p hp]; rfl
  rw [hall]
  constructor
  · intro h0 p hp
    by_contra hne
    have h2 := (hB.l2 p hp).2 hne
    have h1 := (hB.l1 (p.val / 64) (by omega)).2 ⟨by omega, fun e => by rw [e] at h2; simp at h2⟩
    rw [h0] at h1; simp at h1
  · intro h
    by_contra h0
    obtain ⟨i, hi, hb⟩ := (ne_zero_iff_bit _).1 h0
    obtain ⟨hi4, hl2⟩ := (hB.l1 i hi).1 hb
    obtain ⟨j, hj, hbj⟩ := (ne_zero_iff_bit _).1 hl2
    have hp : (64 * i + j) < 256 := by omega
    have := (hB.l2 ⟨BitVec.ofNat 64 (64 * i + j)⟩ (by
      show (BitVec.ofNat 64 (64 * i + j)).toNat < 256; rw [BitVec.toNat_ofNat]; omega)).1 (by
      show (L.l2W s c ((BitVec.ofNat 64 (64 * i + j)).toNat / 64)).bv.getLsbD
        ((BitVec.ofNat 64 (64 * i + j)).toNat % 64) = true
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have e1 : (64 * i + j) / 64 = i := by omega
      have e2 : (64 * i + j) % 64 = j := by omega
      rw [e1, e2]; exact hbj)
    exact this (h _ (by show (BitVec.ofNat 64 (64 * i + j)).toNat < 256; rw [BitVec.toNat_ofNat]; omega))

/-- **The pick**: with a non-empty bitmap, FL4's choice is the head of the
spec's highest non-empty ready queue. -/
theorem choose_pick_refines {N T C : Set U64} {c : U64} (s : S) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hne : L.l1W s c ≠ 0#u64) :
    (do
      let prio ← sched.highest_prio st s 0#u64
      let i3 ← sched.rq_head_off 0#u64 prio
      let q ← sched.q_get st s c i3
      ok q.head) ⦃ t => t ∈ T ∧ t.bv = Fl4Spec.the (Fl4Spec.maxNonEmptyQueue (σ.readyQueues σ.curDomain)).head? ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hN' : NodePlaced st T s (L.cpu s) := by rw [hc.cur]; exact hc.node
  have hB : BitmapOK st s (L.cpu s) (fun p => Q p ≠ []) := by rw [hc.cur]; exact hc.ready.2
  refine WP.spec_bind (sched.highest_prio.spec s 0#u64 _ hN' hB (by rw [hc.cur]; exact hne)) ?_
  rintro p ⟨hp, hpne, hmax⟩
  step as ⟨off, off_post, off_post1⟩
  step as ⟨q, q_post⟩
  have hq : q = L.rqQ s c p := by rw [q_post, off_post1, off_post]; rfl
  have hrel := hc.ready.1.rel p hp
  obtain ⟨d, rest, hd⟩ := List.exists_cons_of_ne_nil hpne
  have hhead : q.head = d := by rw [hq, hrel.head, hd]; rfl
  rw [hhead]
  refine ⟨hrel.mem d (by rw [hd]; exact List.mem_cons_self), ?_⟩
  rw [hs.curDom.1]
  have hmx : Fl4Spec.setMax {prio | σ.readyQueues 0 prio ≠ []} = specPrio p := by
    refine setMax_eq (by show σ.readyQueues 0 (specPrio p) ≠ []; rw [hs.rq p hp, hd]; simp) ?_
    intro x hx
    obtain ⟨p', hp', rfl⟩ := prio_of_spec x
    have hne' : Q p' ≠ [] := by
      intro e; apply hx; show σ.readyQueues 0 (specPrio p') = []; rw [hs.rq p' hp', e]; rfl
    exact (specPrio_le hp' hp).2 (hmax p' hp' hne')
  unfold Fl4Spec.maxNonEmptyQueue
  rw [hmx, hs.rq p hp, hd]
  rfl

end

end

end Fl4Proofs.P3.Sched
