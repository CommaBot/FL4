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

namespace TRB

/-- `Rep` depends only on the links of the tree's own nodes. -/
theorem Rep.congr {k k' : Links} {par x : U64} {t : RBT} (h : Rep k par x t)
    (he : ∀ y ∈ t.keys, k'.l y = k.l y ∧ k'.r y = k.r y ∧ k'.p y = k.p y ∧ k'.red y = k.red y) :
    Rep k' par x t := by
  revert he
  induction h with
  | leaf par x e => intro _; exact .leaf par x e
  | @node par x c l r hx hp hc hl hr ihl ihr =>
    intro he
    obtain ⟨e1, e2, e3, e4⟩ := he x (by simp [RBT.keys])
    refine .node hx (e3.trans hp) (e4.trans hc) ?_ ?_
    · rw [e1]; exact ihl fun y hy => he y (by simp [RBT.keys, hy])
    · rw [e2]; exact ihr fun y hy => he y (by simp [RBT.keys, hy])

end TRB

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T Cs : Set U64}

/-- Two states agree on the timer words of `T` and `Cs`. -/
structure TAgree (st : machine.Store S) [L : LawfulStore st] (T Cs : Set U64) (s s' : S) : Prop where
  td : ∀ y ∈ T, L.mem s' (tdA y) = L.mem s (tdA y)
  tl : ∀ y ∈ T, L.mem s' (tlA y) = L.mem s (tlA y)
  tr : ∀ y ∈ T, L.mem s' (trA y) = L.mem s (trA y)
  tp : ∀ y ∈ T, L.mem s' (tpA y) = L.mem s (tpA y)
  th : ∀ y ∈ T, L.mem s' (thA y) = L.mem s (thA y)
  root : ∀ c ∈ Cs, L.mem s' (L.nodeAt s' c layout.node.TIMER_ROOT) = L.mem s (L.nodeAt s c layout.node.TIMER_ROOT)
  min : ∀ c ∈ Cs, L.mem s' (L.nodeAt s' c layout.node.TIMER_MIN) = L.mem s (L.nodeAt s c layout.node.TIMER_MIN)

theorem CoreTree.congr {s s' : S} {c : U64} {t : TRB.RBT} (h : CoreTree st T s c t) (e : TAgree st T Cs s s')
    (hc : c ∈ Cs) : CoreTree st T s' c t := by
  have kT := h.inT
  refine ⟨?_, h.nodup, h.inT, fun y hy => by rw [e.td y (kT y hy)]; exact h.armed y hy,
    fun y hy => by rw [e.th y (kT y hy)]; exact h.core y hy, ?_, h.bal, h.black,
    by rw [e.min c hc]; exact h.min⟩
  · rw [e.root c hc]
    refine h.rep.congr fun y hy => ⟨e.tl y (kT y hy), e.tr y (kT y hy), e.tp y (kT y hy), ?_⟩
    show ((L.mem s' (thA y) &&& 1#u64) != 0#u64) = ((L.mem s (thA y) &&& 1#u64) != 0#u64)
    rw [e.th y (kT y hy)]
  · exact h.sorted.imp_of_mem fun ha hb hab => by
      rw [e.td _ (kT _ ha), e.td _ (kT _ hb)]; exact hab

/-- `TimerRB` reads only the timer words. -/
theorem TimerRB.congr {s s' : S} (h : TimerRB st T Cs s) (e : TAgree st T Cs s s') : TimerRB st T Cs s' := by
  refine ⟨fun c hc => ?_, fun y hy hd => ?_, fun y hy hd => ?_⟩
  · obtain ⟨t, ct⟩ := h.tree c hc
    exact ⟨t, ct.congr e hc⟩
  · rw [e.td y hy] at hd
    obtain ⟨c, hc, t, ct, hyt⟩ := h.armed y hy hd
    exact ⟨c, hc, t, ct.congr e hc, hyt⟩
  · rw [e.td y hy] at hd
    obtain ⟨a, b, d⟩ := h.idle y hy hd
    rw [e.tl y hy, e.tr y hy, e.tp y hy]
    exact ⟨a, b, d⟩

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
