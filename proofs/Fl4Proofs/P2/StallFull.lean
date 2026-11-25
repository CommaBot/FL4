/-
P2 (p2j4): **`smp.stall` then `smp.send_pending` keep the executing core's
entry invariants** (`EntryInv`, `IdleSc`), for any `LawfulStore` — so at the
stalled core's view — with the frame `StKeep` for the other cores.

* `smp.stall.entryN`, `stallSeq.entryN`.

Premises: the transfer's (`XferOKRS`, `XferFootOKC`, `hRSK`, and
`hRS0`/`UserOK`/`XG` at the stall's start, as in P1), the per-core clauses of
the stalled core (`EntryInv`, `IdleSc`, `hnq`: its current thread, unless
idle, is not queued), the protected threads (`Kp`). **Named premises**:
`TmoCap` [P]; `XferFootOKC` [J] (the transfer writes only SC `CONSUMED` words
among SC words; its former discharge from P1's `XferHyps` was vacuous and is
deleted, `P2/XferN.lean`); `XferOKRS` [J] (p2j13, `P2/FootN5.lean`: P1's
`XferOK` only at states with `RS s s`; it replaces the unguarded `XferOK` at
`XG`, whose only discharge was from the vacuous `XferHyps`, and P1's
`TmoXG`). Both transfer premises are guarded by `RS s s`; their discharge
needs `RS` to carry P3's cap relation.
-/
import Fl4Proofs.P2.StallPost
import Fl4Proofs.P1.QueueSchedCtl
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

/-- **[P] The stalled thread's timeout handler cap is typed** at the states
its budget check reaches: from `s` writing only SC words and the core's own
node words (P1's `tmoOK` cap clause, at these states only; P3: the cap
relation, the TCB's slots being untouched). -/
def TmoCap (st : machine.Store S) [L : LawfulStore st] (Scs : Set U64) (Z : U64 → Nat) (H : Heap) (Rp Nt : Set U64)
    (s : S) : Prop :=
  ∀ s' : S, WritesIn st s s' (fun b => (∃ c ∈ Scs, InSC c (Z c) b) ∨ L.NodeOf s (L.cpu s) (fun _ => True) b) →
    obj.Tcb.slot (L.curW s) layout.tcb.SLOT_TIMEOUT_HANDLER ⦃ sl =>
      obj.Slot.cap st sl s' ⦃ c => CapTyped H Rp Nt c ⦄ ⦄

/-- **`smp.stall`**: from the stalled core's `EntryInv` and `IdleSc`.
Named premises: `hxf` [J] (`XferOKRS`, `P2/FootN5.lean`), `hxw` [J] (`XferFootOKC`,
`P2/XferN.lean`). -/
theorem smp.stall.entryN (hA : P0.ArchTotal ar)
    {RS : S → S → Prop} (hxf : XferOKRS st ar T Cs Ω H Sg Rp Scs Nt Z U RS (XG st T Cs Ω H Sg Scs Z P3Ok))
    (hxw : XferFootOKC st ar T Cs Ω H Sg Rp Scs Nt Z U RS (XG st T Cs Ω H Sg Scs Z P3Ok))
    (hRSK : ∀ s0 s1 s2 : S, RS s0 s1 → WritesIn st s1 s2 (KW st T Cs Sg Scs Z (EH H) s1) → RS s2 s2)
    (hKT : ∀ y ∈ Kp, y ∈ T) (s : S) (a : A) (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hI : IdleSc st (L.cpu s) s) (hG : XG st T Cs Ω H Sg Scs Z P3Ok s)
    (hKc : L.curW s ≠ L.idleW s → L.curW s ∉ Kp) (hKa : ActOut st T Kp s) (hKB : ∀ y ∈ Kp, ¬ Blocked (L.mem s (stA y)))
    (hRS0 : RS s s) (hU : UserOK st T Cs Ω H U s)
    (hnq : L.curW s ≠ L.idleW s → (L.mem s (inqA (L.curW s)) &&& sched.Q_QUEUED) = 0#u64)
    (hcap : TmoCap st Scs Z H Rp Nt s) :
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
  · rename_i hbt
    have hne : L.curW s ≠ L.idleW s := by
      have := hb.1 hbt
      rw [hct, ht] at this; exact this
    have hKc := hKc hne
    refine WP.spec_bind (WP.spec_and (WP.spec_and (sched.update_timestamp.entry hA s a h)
      (sched.update_timestamp.fr hA s a (q0.nodes _ q0.cur))) (sched.update_timestamp.kwN (Kp := Kp) (Nd := True) (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) hA s a
        q0.nodes q0.cur)) ?_
    rintro ⟨s1, a1⟩ hh1
    simp only [WP.uncurry'_pair] at hh1 ⊢
    obtain ⟨⟨⟨⟨⟨Q, R, q1⟩, hB1, hX1, hSg1, hS1⟩, -, hcA, hna, hcsc, hck⟩, w1⟩, f1⟩ := hh1
    have g1 : GN st Kp True T Cs Ω H Sg Scs Z U P3Ok s s1 := GN.foot (GN.refl hG) f1
    have K1 : StKeep st T Cs Scs Kp (L.cpu s) s s1 := StKeep.ofN h.blkOK hKT f1
    have ki1 : L.idleW s1 = L.idleW s := by
      unfold LawfulStore.idleW; rw [K1.cpu, nodeAt_of_ksb K1.ksb, K1.nd _ q0.cur _ (Or.inl idle8)]
    have b1 : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s1 := ⟨⟨Q, R, q1⟩, hB1, hX1, hSg1, hS1⟩
    have hq1 : (L.mem s1 (inqA (L.curW s1)) &&& sched.Q_QUEUED) = 0#u64 := by
      rw [hck.1]
      have kq : L.mem s1 (inqA (L.curW s)) = L.mem s (inqA (L.curW s)) := by
        rw [inqA_eq]
        refine w1.mem_eq (field_aligned (q0.tcbs _ q0.curT) (by simp) (by simp)) ?_
        rintro ⟨o, -, ho, -, e⟩
        exact node_ne_field (q0.nodes _ q0.cur) ho q0.curT (q0.tcbs _ q0.curT) (by simp) e.symm
      rw [kq]; exact hnq hne
    have hcap1 : ∀ s' : S, WritesIn st s1 s' (ChgW st Scs Z s1) →
        obj.Tcb.slot (L.curW s') layout.tcb.SLOT_TIMEOUT_HANDLER ⦃ sl =>
          obj.Slot.cap st sl s' ⦃ c => CapTyped H Rp Nt c ⦄ ⦄ := fun s' w' => by
      have wF : WritesIn st s1 s' (L.Free s1 Ω Cs) := w'.mono' fun b hb hh => by
        rcases hh with ⟨c, hc, hin⟩ | e
        · exact Or.inl (hX1.1.scW c hc b hb hin)
        · exact e ▸ free_cur_node q1.cur (by simp [layout.node.CONSUMED, LowFree])
      rw [(free_keys q1 wF).2.1, hck.1]
      refine hcap s' ((w1.trans w').mono fun b hh => ?_)
      rcases hh with hh | hh | e
      · exact Or.inr hh
      · exact Or.inl hh
      · exact Or.inr (by
          rw [e, K1.cpu, nodeAt_of_ksb K1.ksb]
          exact ⟨_, trivial, by simp [layout.node.CONSUMED], by simp [layout.node.CONSUMED], rfl⟩)
    refine WP.spec_bind (sched.check_budget.allGN (Kp := Kp) (Nd := True) hA s1 a1 Q R q1 hB1 hX1 hSg1 hS1 hcsc hna hcA
      (G := GN st Kp True T Cs Ω H Sg Scs Z U P3Ok s) (fun _ _ g f => GN.foot g f)
      (fun _ g => GN.out g trivial (q0.nodes _ q0.cur) q0.cur hKa hKc) g1
      (tmoKC_N hA hxf hxw hRSK trivial hKT Ac s s1 hKc hKB (q0.nodes _ q0.cur) q0.cur hKa b1
        (hRSK s s s1 hRS0 f1.foot) (hU.ksb K1.ksb) hq1 (by rw [ki1, hck.1]; exact hne.symm) hcap1)) ?_
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
`EntryInv` and `IdleSc`; the core then runs its idle thread; `StKeep`.
Named premises: `hxf` [J] (`XferOKRS`), `hxw` [J] (`XferFootOKC`). -/
theorem stallSeq.entryN (hA : P0.ArchTotal ar)
    {RS : S → S → Prop} (hxf : XferOKRS st ar T Cs Ω H Sg Rp Scs Nt Z U RS (XG st T Cs Ω H Sg Scs Z P3Ok))
    (hxw : XferFootOKC st ar T Cs Ω H Sg Rp Scs Nt Z U RS (XG st T Cs Ω H Sg Scs Z P3Ok))
    (hRSK : ∀ s0 s1 s2 : S, RS s0 s1 → WritesIn st s1 s2 (KW st T Cs Sg Scs Z (EH H) s1) → RS s2 s2)
    (hKT : ∀ y ∈ Kp, y ∈ T) (s : S) (a : A) (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hI : IdleSc st (L.cpu s) s) (hG : XG st T Cs Ω H Sg Scs Z P3Ok s)
    (hKc : L.curW s ≠ L.idleW s → L.curW s ∉ Kp) (hKa : ActOut st T Kp s) (hKB : ∀ y ∈ Kp, ¬ Blocked (L.mem s (stA y)))
    (hRS0 : RS s s) (hU : UserOK st T Cs Ω H U s)
    (hnq : L.curW s ≠ L.idleW s → (L.mem s (inqA (L.curW s)) &&& sched.Q_QUEUED) = 0#u64)
    (hcap : TmoCap st Scs Z H Rp Nt s) :
    (do
      let (s1, a1) ← smp.stall st ar s a
      smp.send_pending st ar s1 a1) ⦃ s' _ => EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ IdleSc st (L.cpu s) s' ∧
        StKeep st T Cs Scs Kp (L.cpu s) s s' ∧ L.curW s' = L.idleW s' ∧
        (L.actionW s' = L.actionW s ∨ L.actionW s' = 0#u64) ⦄ := by
  have q0 := h.1.choose_spec.choose_spec
  refine WP.spec_bind (smp.stall.entryN (Kp := Kp) hA hxf hxw hRSK hKT s a h hI hG hKc hKa hKB hRS0 hU hnq hcap) ?_
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
      rw [ecs, ea, ec, show L.mem s' (scA (L.curW s1)) = L.mem s1 (scA (L.curW s1)) from kst.sc _ q1.curT]
      exact h.2.2.2.2.2
    · refine ⟨by rw [ecs]; exact hs.ac, ?_, fun _ => by rw [ecs, hsc]; exact hs.csc⟩
      rw [ea, hs.act]
      exact fun e => notT_small q2.tcbs (v := 0#u64) (by simp) (by rw [e]; exact q2.curT)
  · rcases hc1 with ⟨e, e2⟩ | hs
    · subst e; rw [ec, ei]; exact e2
    · rw [ec, ei]; exact hs.cur
  · rcases hc1 with ⟨e, -⟩ | hs
    · subst e; exact Or.inl ea
    · exact Or.inr (ea.trans hs.act)

end

end Fl4Proofs.P1
