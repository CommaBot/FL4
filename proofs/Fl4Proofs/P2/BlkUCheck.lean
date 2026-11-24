/-
P2 (p2j4, audit): **`EntryHyps0.blkU` and `EntryHyps0.tmoOK` are
unsatisfiable** once the invariants hold at a state. `BXI` does not exclude a
current thread that is the idle thread (every idle core has one; `BXI` is
kept by `set_cur_thread` of the idle thread), but both fields claim `CanBlock`
of the current thread, whose `ni` says it is not the idle thread. Not a
premise anywhere: a refutation, kept so that the fields get guarded.
-/
import Fl4Proofs.P2.StallPost
import Fl4Proofs.P1.QueueSignal
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}
variable {P3Ok : S → Prop} {A : Type _} {ar : machine.Arch A}

/-- From any `BXI` state there is a `BXI` state (reached by a `KW` write)
whose current thread is the idle thread. -/
theorem bxi_idle_state {s : S} (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    ∃ s', BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ L.curW s' = L.idleW s' ∧ Foot st T Cs Sg Scs Z (EH H) s s' := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hSg, hS⟩ := h
  have hk : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s := ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩
  have hsp := WP.spec_and
    (sched.set_cur_thread.sch s (L.idleW s) Q R h0 hB hSg h0.idleT (fun _ => hB.idle) (fun _ => hB.idleA h0.idleT))
    (sched.set_cur_thread.kwN (Kp := ∅) (Nd := False) (T := T) (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s (L.idleW s)
      h0.nodes h0.cur id)
  obtain ⟨s', hs'⟩ : ∃ s', sched.set_cur_thread st s (L.idleW s) = ok s' :=
    ⟨_, ib_eq_of_spec (sched.set_cur_thread.spec s (L.idleW s))⟩
  rw [hs'] at hsp
  obtain ⟨⟨P, ec, -⟩, f⟩ := (WP.spec_ok _).1 hsp
  have hk' := Post.blk hk P
  refine ⟨s', ⟨hk'.1, hk'.2.1, hk'.2.2.1, hk'.2.2.2.2, hk'.2.2.2.1⟩, ?_, f.foot⟩
  rw [ec]
  have k := StKeep.ofFr (Kp := ∅) (Es := EH H) hk (fun _ hy => absurd hy (Set.notMem_empty _)) f P.fr
  unfold LawfulStore.idleW
  rw [k.cpu, nodeAt_of_ksb k.ksb, k.nd _ h0.cur _ (Or.inl idle8)]

/-- `EntryHyps0` (its `blkU`) is contradictory with any `BXI` state. -/
theorem entryHyps0_blkU_false (E : EntryHyps0 st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok) {s : S}
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) : False := by
  obtain ⟨s', h', e, -⟩ := bxi_idle_state h
  exact (E.blkU Ac s' h').1.ni e.symm

/-- Its `tmoOK` alone (guarded by `XG`) is contradictory with any `XG` `BXI` state. -/
theorem tmoOK_false
  (hT : ∀ (Ac : Set U64) (s : S), XG st T Cs Ω H Sg Scs Z P3Ok s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    CanBlock st T Ac s (L.curW s)) {s : S} (hG : XG st T Cs Ω H Sg Scs Z P3Ok s)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) : False := by
  obtain ⟨s', h', e, f⟩ := bxi_idle_state h
  exact (hT Ac s' (hG.foot f) h').ni e.symm

end

end Fl4Proofs.P1
