/-
P1 (jc6d, TIMER-RB-PLAN stage 2a): frames of the timer red-black invariant `TimerRB`.  The invariant reads
only the timer words (`TW`: a TCB's deadline/left/right/parent/height and a core's `TIMER_ROOT`/`TIMER_MIN`),
so any step whose writes miss them keeps it (`TimerRB.of_writesIn`).
-/
import Fl4Proofs.P1.TimerRB
import Fl4Proofs.P1.QueueTimer
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T Cs : Set U64}

/-- A step whose writes miss the timer words `TW` keeps them. -/
theorem TAgree.of_writesIn {s s' : S} {A : U64 → Prop} (w : WritesIn st s s' A) (hT : TcbPlaced T)
    (hN : ∀ c ∈ Cs, NodePlaced st T s c) (hA : ∀ b, A b → ¬ TW st T Cs s b) : TAgree st T Cs s s' := by
  have fld : ∀ y ∈ T, ∀ K : U64, 3528 ≤ K.val → K.val < 3576 → K.val % 8 = 0 →
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y hy K h1 h2 h8 => w.2.2 _ (tz_aligned hT (Tz.of_mem hy) (by omega) h8)
      fun hb => hA _ hb (Or.inl ⟨y, hy, K, h1, h2, rfl⟩)
  have nd : ∀ c ∈ Cs, ∀ o : U64, (o.val = 104 ∨ o.val = 112) →
      L.mem s' (L.nodeAt s' c o) = L.mem s (L.nodeAt s c o) := fun c hc o ho => by
    rw [nodeAt_of_ksb w.1]
    exact w.2.2 _ (nodeAt_aligned (hN c hc) (by omega) (by omega))
      fun hb => hA _ hb (Or.inr ⟨c, hc, o, ho, rfl⟩)
  exact ⟨fun y hy => fld y hy 3528#u64 (by simp) (by simp) (by simp),
    fun y hy => fld y hy 3544#u64 (by simp) (by simp) (by simp),
    fun y hy => fld y hy 3552#u64 (by simp) (by simp) (by simp),
    fun y hy => fld y hy 3560#u64 (by simp) (by simp) (by simp),
    fun y hy => fld y hy 3568#u64 (by simp) (by simp) (by simp),
    fun c hc => nd c hc _ (by rw [timer_root_val]; simp),
    fun c hc => nd c hc _ (by rw [timer_min_val]; simp)⟩

/-- **Frame.** A step whose writes miss the timer words keeps `TimerRB`. -/
theorem TimerRB.of_writesIn {s s' : S} {A : U64 → Prop} (h : TimerRB st T Cs s) (w : WritesIn st s s' A)
    (hT : TcbPlaced T) (hN : ∀ c ∈ Cs, NodePlaced st T s c) (hA : ∀ b, A b → ¬ TW st T Cs s b) :
    TimerRB st T Cs s' := h.congr (TAgree.of_writesIn w hT hN hA)

/-- `TimerRB` gives the link and root/min typing part of `TimerOK`. -/
theorem TimerRB.root_tz {s : S} (h : TimerRB st T Cs s) {c : U64} (hc : c ∈ Cs) :
    Tz T (L.mem s (L.nodeAt s c layout.node.TIMER_ROOT)) ∧ Tz T (L.mem s (L.nodeAt s c layout.node.TIMER_MIN)) := by
  obtain ⟨t, ct⟩ := h.tree c hc
  have tz : ∀ v, v = 0#u64 ∨ v ∈ t.keys → Tz T v := fun v hv =>
    hv.elim (fun e => e ▸ Tz.zero) (fun m => Tz.of_mem (ct.inT v m))
  exact ⟨tz _ ct.rep.root_mem, by rw [ct.min]; exact tz _ t.minKey_mem⟩

end

end Fl4Proofs.P1
