/-
P3 (DESIGN.md §9), invariant line G1 (sl1): **the typed form gives sb2's
`ScLive`** (spec side only).

* `IdleScOutV σ := IrqOutV (fun _ => σ.idleSc) (uV σ)` (l4v `valid_global_refs`,
  `idle_sc_ptr ∈ global_refs`): no cap's range covers the idle SC; sg1's
  `IdleOutV` says it for the idle thread. Both are kept by sg1's `S N M` family
  (any fixed `M`); the idle SC pointer is constant (SpecInvSlI1..I6).
* **`scLive_of`**: `ScLiveT (idle thread, idle SC) ∧ IdleOutV ∧ IdleScOutV →
  ScLive`.
* `boot_scLiveT`, `boot_idleScOutV` (non-vacuity only).
-/
import Fl4Proofs.P3.SpecInvSlK
import Fl4Proofs.P3.SpecInvSbE
import Fl4Proofs.P3.SpecInvSgE
open Classical

namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-- **The idle SC lies outside every cap's range** (l4v `valid_global_refs`). -/
def IdleScOutV (σ : State Unit) : Prop := SInvU.IrqOutV (fun _ => σ.idleSc) (SInvU.uV σ)

/-- The idle pair of a state. -/
abbrev idleP (σ : State Unit) : ObjRef × ObjRef := (σ.idleThread, σ.idleSc)

theorem live_of_bound {σ : State Unit} {p : ObjRef} (h : SInvB.Bound (SInvB.bv σ.kheap p)) :
    ∃ o, σ.kheap p = some o ∧ liveO o := by
  obtain ⟨o, e | e⟩ := h
  · obtain ⟨x, hx, hs⟩ := SInvB.bv_t.1 e
    exact ⟨_, hx, by show x.tcbSchedContext ≠ none; rw [hs]; simp⟩
  · obtain ⟨y, n, hy, hs⟩ := SInvB.bv_s.1 e
    exact ⟨_, hy, Or.inl (by rw [hs]; simp)⟩

/-- **The typed form, with the idle thread and idle SC outside every cap's
range, gives `ScLive`.** -/
theorem scLive_of {σ : State Unit} (h : ScLiveT (idleP σ) σ) (hI : SInvG.IdleOutV σ)
    (hS : IdleScOutV σ) : SInvB.ScLive σ := by
  intro p hb
  obtain ⟨o, ho, hl⟩ := live_of_bound hb
  by_cases h1 : p = σ.idleThread
  · subst h1; exact Or.inr fun s c hc => hI default s c hc
  by_cases h2 : p = σ.idleSc
  · subst h2; exact Or.inr fun s c hc => hS default s c hc
  obtain ⟨s, c, hs, hn⟩ := h p o ho hl h1 h2
  exact Or.inl ⟨s, c, hs, ncap_objRefs hn⟩

theorem boot_scLiveT : ScLiveT (idleP (initASt (Z := Unit))) (initASt (Z := Unit)) := by
  intro p o hp hl h1 h2
  exfalso
  simp only [idleP, initASt] at hp h1 h2
  unfold initKheap at hp
  simp only [Function.update_apply] at hp
  split_ifs at hp <;> first
    | (exact h1 (by assumption))
    | (exact h2 (by assumption))
    | (cases hp; exact hl)
    | (cases hp)

theorem boot_idleScOutV : IdleScOutV (initASt (Z := Unit)) := by
  intro _ s c h
  rw [SInvU.init_capAt h]
  simp [SInvU.covR, SInvU.capRng, objRefs]

end

end Fl4Proofs.P3.SInvL
