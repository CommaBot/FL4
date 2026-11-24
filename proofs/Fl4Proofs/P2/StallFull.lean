/-
P2 (p2j4): **`smp.stall` then `smp.send_pending` keep the executing core's
entry invariants** (`EntryInv`, `IdleSc`), for any `LawfulStore` — so at the
stalled core's view — with the frame `StKeep` for the other cores.

* `smp.stall.entryN`, `stallSeq.entryN`.

**Named premise**: `hRSX` [P] (`tmoKG_N`, `P2/FootN5.lean`).
-/
import Fl4Proofs.P2.StallPost
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64} {Kp : Set U64}
variable {P3Ok : S → Prop} {A : Type _} {ar : machine.Arch A}

/-- `BlkOK` from `EntryInv`. -/
theorem EntryInv.blkOK {s : S} (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s := ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.1.sg⟩

/-- **`smp.stall`**: from the stalled core's `EntryInv` and `IdleSc`. -/
theorem smp.stall.entryN (hA : P0.ArchTotal ar) (E : EntryHyps0 st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (TX : TmoXG st ar) {RS : S → S → Prop}
    (hxw : XferFootOKC st ar T Cs Ω H Sg Rp Scs Nt Z U RS (XG st T Cs Ω H Sg Scs Z P3Ok))
    (hRSK : ∀ s0 s1 s2 : S, RS s0 s1 → WritesIn st s1 s2 (KW st T Cs Sg Scs Z (EH H) s1) → RS s2 s2)
    (hRSX : ∀ (Ac : Set U64) (s : S), XG st T Cs Ω H Sg Scs Z P3Ok s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → RS s s)
    (hKT : ∀ y ∈ Kp, y ∈ T) (s : S) (a : A) (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hI : IdleSc st (L.cpu s) s) (hG : XG st T Cs Ω H Sg Scs Z P3Ok s)
    (hKc : L.curW s ∉ Kp) (hKB : ∀ y ∈ Kp, ¬ Blocked (L.mem s (stA y))) :
    smp.stall st ar s a ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ StKeep st T Cs Scs Kp (L.cpu s) s s' ∧
      ((s' = s ∧ L.curW s = L.idleW s) ∨ Stalled0 st Ac s') ⦄ := by
  have q0 := h.1.choose_spec.choose_spec
  unfold smp.stall
  step with sched.cur_thread.spec as ⟨ct, hct⟩
  step with sched.idle_thread.spec' as ⟨t, ht⟩
  refine WP.spec_bind (tcb_ne.spec' ct t) ?_
  intro b hb
  have hctT : ct ∈ T := by rw [hct]; exact q0.curT
  split
  · refine WP.spec_bind (WP.spec_and (sched.update_timestamp.entry hA s a h)
      (sched.update_timestamp.kwN (Kp := Kp) (Nd := True) (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) hA s a
        q0.nodes q0.cur)) ?_
    rintro ⟨s1, a1⟩ hh1
    simp only [WP.uncurry'_pair] at hh1 ⊢
    obtain ⟨⟨⟨⟨Q, R, q1⟩, hB1, hX1, hSg1, hS1⟩, -, hcA, hna, hcsc, -⟩, f1⟩ := hh1
    have g1 : GN st Kp True T Cs Ω H Sg Scs Z U P3Ok s s1 := GN.foot (GN.refl hG) f1
    refine WP.spec_bind (sched.check_budget.allGN (Kp := Kp) (Nd := True) hA s1 a1 Q R q1 hB1 hX1 hSg1 hS1 hcsc hna hcA
      (G := GN st Kp True T Cs Ω H Sg Scs Z U P3Ok s) (fun _ _ g f => GN.foot g f) g1
      (tmoKG_N hA E TX hxw hRSK hRSX trivial hKT Ac s hKc hKB (q0.nodes _ q0.cur) q0.cur)) ?_
    rintro ⟨r, s2, a2⟩ hh2
    simp only [WP.uncurry'_pair] at hh2 ⊢
    obtain ⟨⟨b2, g2⟩, -⟩ := hh2
    have k2 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s2 := ⟨b2.1, b2.2.1, b2.2.2.1, b2.2.2.2.2, b2.2.2.2.1⟩
    refine WP.spec_bind (WP.spec_and (sched.commit_time.blk hA a2 k2)
      (sched.commit_time.kwN (Kp := Kp) (Nd := True) (Es := EH H) hA a2 k2)) ?_
    rintro s3 ⟨⟨k3, -⟩, f3⟩
    have g3 := GN.foot g2 f3
    have K3 : StKeep st T Cs Scs Kp (L.cpu s) s s3 := StKeep.ofI q0 h.2.2.1.1 hKT g3.2
    have hI3 : IdleSc st (L.cpu s3) s3 := by rw [K3.cpu]; exact K3.idle q0.cur q0.idleT hI
    refine WP.spec_mono (stall2.blk (Kp := Kp) hA s3 a2 ct k3 hctT (by rw [hct]; exact hKc) hKT hI3) ?_
    rintro ⟨s', a'⟩ hh
    simp only [WP.uncurry'_pair] at hh ⊢
    exact ⟨hh.1, K3.next hh.2.1, Or.inr hh.2.2⟩
  · rename_i hf
    have e : ct = t := by
      by_contra hne
      exact hf (hb.2 hne)
    refine (WP.spec_ok _).2 ⟨h.blkOK, StKeep.refl s, Or.inl ⟨rfl, ?_⟩⟩
    unfold LawfulStore.curW LawfulStore.idleW
    rw [← hct, ← ht]; exact e

/-- **`smp.stall` then `smp.send_pending`** keep the executing core's
`EntryInv` and `IdleSc`; the core then runs its idle thread; `StKeep`. -/
theorem stallSeq.entryN (hA : P0.ArchTotal ar) (E : EntryHyps0 st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (TX : TmoXG st ar) {RS : S → S → Prop}
    (hxw : XferFootOKC st ar T Cs Ω H Sg Rp Scs Nt Z U RS (XG st T Cs Ω H Sg Scs Z P3Ok))
    (hRSK : ∀ s0 s1 s2 : S, RS s0 s1 → WritesIn st s1 s2 (KW st T Cs Sg Scs Z (EH H) s1) → RS s2 s2)
    (hRSX : ∀ (Ac : Set U64) (s : S), XG st T Cs Ω H Sg Scs Z P3Ok s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → RS s s)
    (hKT : ∀ y ∈ Kp, y ∈ T) (s : S) (a : A) (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hI : IdleSc st (L.cpu s) s) (hG : XG st T Cs Ω H Sg Scs Z P3Ok s)
    (hKc : L.curW s ∉ Kp) (hKB : ∀ y ∈ Kp, ¬ Blocked (L.mem s (stA y))) :
    (do
      let (s1, a1) ← smp.stall st ar s a
      smp.send_pending st ar s1 a1) ⦃ s' _ => EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ IdleSc st (L.cpu s) s' ∧
        StKeep st T Cs Scs Kp (L.cpu s) s s' ∧ L.curW s' = L.idleW s' ∧
        (L.actionW s' = L.actionW s ∨ L.actionW s' = 0#u64) ⦄ := by
  have q0 := h.1.choose_spec.choose_spec
  refine WP.spec_bind (smp.stall.entryN (Kp := Kp) hA E TX hxw hRSK hRSX hKT s a h hI hG hKc hKB) ?_
  rintro ⟨s1, a1⟩ hh
  simp only [WP.uncurry'_pair] at hh ⊢
  obtain ⟨k1, K1, hc1⟩ := hh
  have q1 := k1.1.choose_spec.choose_spec
  refine WP.spec_mono (WP.spec_and
    (smp.send_pending.fp hA s1 a1 (B := (· = L.nodeAt s1 (L.cpu s1) layout.node.IPI_PENDING)) (q1.nodes _ q1.cur) rfl)
    (smp.send_pending.kwN (Kp := Kp) (Nd := True) (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) hA s1 a1 q1.nodes q1.cur)) ?_
  rintro ⟨s', a'⟩ hh
  simp only [WP.uncurry'_pair] at hh ⊢
  obtain ⟨w, f⟩ := hh
  have c120 : layout.node.IPI_PENDING.val = 120 := by simp [layout.node.IPI_PENDING]
  obtain ⟨k2, ea, ec, ei, ecs⟩ := node_blk k1 (by unfold LowFree; omega) (by omega) (by omega) w
  have K2 := K1.next (StKeep.ofN k1 hKT f)
  have kst := StKeep.ofN k1 hKT f
  have q2 := k2.1.choose_spec.choose_spec
  have hsc : L.mem s' (scA (L.curW s')) = L.mem s1 (scA (L.curW s1)) := by rw [ec]; exact kst.sc _ q1.curT
  refine ⟨⟨k2.1, k2.2.1, k2.2.2.1, k2.2.2.2.1, k2.2.2.1.2.2.tm, ?_⟩, K2.idle q0.cur q0.idleT hI, K2, ?_, ?_⟩
  · rcases hc1 with ⟨e, -⟩ | hs
    · subst e
      rw [ecs, ea, ec, kst.sc _ q1.curT]
      exact h.2.2.2.2.2
    · refine ⟨by rw [ecs]; exact hs.ac, ?_, fun _ => by rw [ecs, hsc]; exact hs.csc⟩
      rw [ea, hs.act]
      exact fun e => notT_small q2.tcbs (by simp) (e ▸ q2.curT : (0#u64) ∈ T)
  · rcases hc1 with ⟨e, e2⟩ | hs
    · subst e; rw [ec, ei]; exact e2
    · rw [ec, ei]; exact hs.cur
  · rcases hc1 with ⟨e, -⟩ | hs
    · subst e; exact Or.inl ea
    · exact Or.inr (ea.trans hs.act)

end

end Fl4Proofs.P1
