-- AArch64 port of Fl4Proofs.P1.TimerRB (proofs/scratch/a64/port.py): the x86_64 text, re-checked
-- over Fl4CoreA64. Edits beyond the renaming are marked `-- a64:`.
/-
P1 (jc6d, TIMER-RB-PLAN stage 1): the red-black invariant of the per-core timer trees (`timer.rs`).

The heap links of a core's tree are related (`TRB.Rep`) to an abstract red-black tree `TRB.RBT` (Okasaki /
CLRS shape: a colour on every node, `leaf` for null).  `CoreTree` is the per-core invariant (parent/child
consistency, distinct keys, all armed TCBs of that core, in-order sorted by deadline with ties as `insert`
breaks them, red-black balance, black root, `TIMER_MIN` = the leftmost node), `TimerRB` the whole-state one
(every armed TCB is in its core's tree, every unarmed TCB has null links).

Main results: `TRB.height_le_128` (a red-black tree with a black root and distinct 64-bit keys has height at
most 128 = `TREE_FUEL`, so no tree loop of `timer.rs` is ever cut off) and `TimerRB.no_link` (no timer-tree
word names an unarmed TCB, e.g. one just passed to `timer::remove`).
-/
import Fl4ProofsA64.P1.TimerRBDef
import Fl4ProofsA64.P1.QueueTimerW
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T Cs : Set U64}


/-- **No timer-tree word names an unarmed TCB** (e.g. `t` right after `timer::remove t`): no TCB's
left/right/parent link and no core's `TIMER_ROOT`/`TIMER_MIN`. -/
theorem TimerRB.no_link {s : S} {x : U64} (h : TimerRB st T Cs s) (hT : TcbPlaced T) (hx : x ∈ T)
    (hd : L.mem s (tdA x) = 0#u64) :
    (∀ y ∈ T, L.mem s (tlA y) ≠ x ∧ L.mem s (trA y) ≠ x ∧ L.mem s (tpA y) ≠ x) ∧
    (∀ c ∈ Cs, L.mem s (L.nodeAt s c layout.node.TIMER_ROOT) ≠ x ∧
      L.mem s (L.nodeAt s c layout.node.TIMER_MIN) ≠ x) := by
  have hx0 : (0#u64) ≠ x := fun e => (hT x hx).ne0 (by rw [← e]; simp)
  have key : ∀ {c : U64} {t : TRB.RBT}, CoreTree st T s c t → ∀ v, v = 0#u64 ∨ v ∈ t.keys → v ≠ x :=
    fun {c t} ct v hv e => by
      subst e
      rcases hv with hv | hv
      · exact hx0 hv.symm
      · exact ct.armed v hv hd
  refine ⟨fun y hy => ?_, fun c hc => ?_⟩
  · by_cases hdy : L.mem s (tdA y) = 0#u64
    · obtain ⟨a, b, d⟩ := h.idle y hy hdy
      rw [a, b, d]; exact ⟨hx0, hx0, hx0⟩
    · obtain ⟨c, -, t, ct, hyt⟩ := h.armed y hy hdy
      obtain ⟨a, b, d⟩ := ct.rep.links y hyt
      exact ⟨key ct _ a, key ct _ b, key ct _ d⟩
  · obtain ⟨t, ct⟩ := h.tree c hc
    refine ⟨key ct _ ct.rep.root_mem, ?_⟩
    rw [ct.min]; exact key ct _ t.minKey_mem

/-- The nodes of the trees are TCBs whose links are typed: `TimerRB` gives the link part of `TimerOK` for
the TCBs of `T`. -/
theorem TimerRB.links_tz {s : S} (h : TimerRB st T Cs s) {y : U64} (hy : y ∈ T) :
    Tz T (L.mem s (tlA y)) ∧ Tz T (L.mem s (trA y)) ∧ Tz T (L.mem s (tpA y)) := by
  by_cases hdy : L.mem s (tdA y) = 0#u64
  · obtain ⟨a, b, d⟩ := h.idle y hy hdy
    rw [a, b, d]; exact ⟨Tz.zero, Tz.zero, Tz.zero⟩
  · obtain ⟨c, -, t, ct, hyt⟩ := h.armed y hy hdy
    obtain ⟨a, b, d⟩ := ct.rep.links y hyt
    have tz : ∀ v, v = 0#u64 ∨ v ∈ t.keys → Tz T v := fun v hv =>
      hv.elim (fun e => e ▸ Tz.zero) (fun m => Tz.of_mem (ct.inT v m))
    exact ⟨tz _ a, tz _ b, tz _ (d.imp_left id)⟩

end

end Fl4ProofsA64.P1
