/-
P2 (tmofr, part D): **P2's stall budget path with the shared timeout-fault
lemma**: the `TmoKC` premise of the stall's budget check (`GN s0`, now over
`Timeout` faults only) from `faults.handle_timeout.tmoFr` (P2/TmoFrA), with no
transfer premise.

* `FootT.ipcN`: a timeout fault's `FootT` footprint is an `IpcFootN` one.
* **`tmoKC_NT`**: `tmoKC_N` without `XferOKRS` [J], `XferFootOKC` [J], `RS`
  and `UserOK`. Named premise `hcap` [P] as before.
* **`smp.stall.entryNT`**, **`stallSeq.entryNT`**: `smp.stall.entryN` /
  `stallSeq.entryN` (P2/StallFull) with `tmoKC_NT`: the premises `hxf` [J],
  `hxw` [J], `hRSK`, `hRS0`, `hU` are gone; left: `hcap` (`TmoCap` [P]),
  `hnq`, `XG` and the protected-thread layer, as before.
-/
import Fl4Proofs.P2.TmoFrA
import Fl4Proofs.P2.StallFull
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64} {Kp : Set U64} {Nd : Prop}
variable {P3Ok : S → Prop}

/-- A timeout fault's footprint is an `IpcFootN` footprint. -/
theorem FootT.ipcN {s s' : S} (hO : ObjsOK st Ω Sg Rp Scs Nt Z s)
    (f : FootT st Kp Nd T Cs Sg Scs Z (EH H) s s') : IpcFootN st Kp Nd T Cs Ω Sg Scs Z (EH H) U s s' :=
  WritesA.mono f fun b hb => ⟨by
    rcases hb.1 with hk | hd | (⟨y, hy, K, -, h2, h3, e⟩ | hu) | ⟨c, hc, e⟩
    · exact Or.inl hk.kw
    · exact Or.inr (Or.inr (Or.inr hd))
    · exact Or.inr (Or.inl (Or.inl ⟨y, hy, K, h2, h3, e⟩))
    · exact absurd hu (Set.notMem_empty _)
    · exact Or.inl (kw_sc hc (e ▸ (consW_in hO hc).2)), hb.2⟩

/-- **Timeout faults keep `GN s0`, no transfer premise** (`tmoKC_N` with the
shared timeout-fault lemma `handle_timeout.tmoFr`). Named premise `hcap` [P]:
the current thread's timeout handler cap typed at the states `ChgW` writes
reach from `s1`. -/
theorem tmoKC_NT {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (hNd : Nd) (hKT : ∀ y ∈ Kp, y ∈ T)
    (Ac : Set U64) (s0 s1 : S) (hKc : L.curW s0 ∉ Kp) (hKB0 : ∀ y ∈ Kp, ¬ Blocked (L.mem s0 (stA y)))
    (NP0 : NodePlaced st T s0 (L.cpu s0)) (hc0 : L.cpu s0 ∈ Cs) (hKa0 : ActOut st T Kp s0)
    (h1 : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s1)
    (hnq : (L.mem s1 (inqA (L.curW s1)) &&& sched.Q_QUEUED) = 0#u64) (hni : L.idleW s1 ≠ L.curW s1)
    (hcap : ∀ s : S, WritesIn st s1 s (ChgW st Scs Z s1) →
      obj.Tcb.slot (L.curW s) layout.tcb.SLOT_TIMEOUT_HANDLER ⦃ sl =>
        obj.Slot.cap st sl s ⦃ c => CapTyped H Rp Nt c ⦄ ⦄) :
    TmoKC st ar T Cs Ω H Sg Rp Scs Nt Z Ac s1 (GN st Kp Nd T Cs Ω H Sg Scs Z U P3Ok s0) :=
  fun s a f Q R h hB hX hSg hS hw hok hG => by
    obtain ⟨⟨Q1, R1, q1⟩, -, hX1, -, -⟩ := h1
    have hKt : L.curW s ∉ Kp := by rw [hG.2.curK hNd NP0 hc0]; exact hKc
    have hKB : ∀ y ∈ Kp, ¬ Blocked (L.mem s (stA y)) := fun y hy => by
      rw [hG.2.stK h.tcbs (hKT y hy) hy]; exact hKB0 y hy
    have hk : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s := ⟨⟨Q, R, h⟩, hB, hX, hS, hSg⟩
    have c40 : layout.node.CONSUMED.val = 40 := by simp [layout.node.CONSUMED]
    have wF : WritesIn st s1 s (L.Free s1 Ω Cs) := hw.mono' fun b hb hh => by
      rcases hh with ⟨c, hc, hin⟩ | e
      · exact Or.inl (hX1.1.scW c hc b hb hin)
      · exact e ▸ free_cur_node q1.cur (by unfold LowFree; omega)
    obtain ⟨-, kc, ki, -⟩ := free_keys q1 wF
    have hcT := q1.curT
    have kq : L.mem s (inqA (L.curW s1)) = L.mem s1 (inqA (L.curW s1)) := by
      rw [inqA_eq]
      refine wF.mem_eq (field_aligned (q1.tcbs _ hcT) (by simp) (by simp)) ?_
      rintro (hm | ⟨c, hc, o, ho, e⟩)
      · exact out_ne_field (q1.omega _ hm) hcT (q1.tcbs _ hcT) (by simp) rfl
      · exact node_ne_field (q1.nodes c hc) (by simp only [LowFree] at ho; omega) hcT (q1.tcbs _ hcT) (by simp) e.symm
    have hc : CanBlock st T Ac s (L.curW s) :=
      ⟨h.curT, fun hb => blocked_not_runnable hb hok.run, runnable_ne_reply hok.run,
        by rw [kc, kq]; exact hnq, hok.rel, hok.act, by rw [ki, kc]; exact hni,
        fun _ => (hS.act _ (hX.2.2.bound _ h.curT hok.bnd).1).2 hok.rmx⟩
    refine WP.spec_mono (faults.handle_timeout.tmoFr (Kp := Kp) (Nd := Nd) hA s a _ f hk hc (hcap s hw) hKt hKT hKB
      (hG.2.out hKa0)) ?_
    rintro ⟨s', a'⟩ hr
    simp only [WP.uncurry'_pair] at hr ⊢
    have hU0 : UserOK st T Cs Ω H ∅ s := fun _ hb => absurd hb (Set.notMem_empty _)
    exact ⟨BlkOK.bxi hr.1, XG.of_fr hG.1 ((FootT.ipcN (U := ∅) hX.1 hr.2).w.mono fun _ hb => IpcW.cur0w hU0 hb.1),
      hG.2.trans (FootT.ipcN hX.1 hr.2)⟩


variable {A : Type _} {ar : machine.Arch A}

set_option maxHeartbeats 4000000 in
/-- **`smp.stall`, no transfer premise** (`smp.stall.entryN` with `tmoKC_NT`).
Named premise: `hcap` (`TmoCap` [P]). -/
theorem smp.stall.entryNT (hA : P0.ArchTotal ar)
    (hKT : ∀ y ∈ Kp, y ∈ T) (s : S) (a : A) (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hI : IdleSc st (L.cpu s) s) (hG : XG st T Cs Ω H Sg Scs Z P3Ok s)
    (hKc : L.curW s ≠ L.idleW s → L.curW s ∉ Kp) (hKa : ActOut st T Kp s) (hKB : ∀ y ∈ Kp, ¬ Blocked (L.mem s (stA y)))
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
    have g1 : GN st Kp True T Cs Ω H Sg Scs Z ∅ P3Ok s s1 := GN.foot (GN.refl hG) f1
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
      (G := GN st Kp True T Cs Ω H Sg Scs Z ∅ P3Ok s) (fun _ _ g f => GN.foot g f)
      (fun _ g => GN.out g trivial (q0.nodes _ q0.cur) q0.cur hKa hKc) g1
      (tmoKC_NT (U := ∅) (P3Ok := P3Ok) hA trivial hKT Ac s s1 hKc hKB (q0.nodes _ q0.cur) q0.cur hKa b1 hq1 (by rw [ki1, hck.1]; exact hne.symm) hcap1)) ?_
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

set_option maxHeartbeats 4000000 in
/-- **`smp.stall` then `smp.send_pending`, no transfer premise**
(`stallSeq.entryN` with `smp.stall.entryNT`). Named premise: `hcap` (`TmoCap` [P]). -/
theorem stallSeq.entryNT (hA : P0.ArchTotal ar)
    (hKT : ∀ y ∈ Kp, y ∈ T) (s : S) (a : A) (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hI : IdleSc st (L.cpu s) s) (hG : XG st T Cs Ω H Sg Scs Z P3Ok s)
    (hKc : L.curW s ≠ L.idleW s → L.curW s ∉ Kp) (hKa : ActOut st T Kp s) (hKB : ∀ y ∈ Kp, ¬ Blocked (L.mem s (stA y)))
    (hnq : L.curW s ≠ L.idleW s → (L.mem s (inqA (L.curW s)) &&& sched.Q_QUEUED) = 0#u64)
    (hcap : TmoCap st Scs Z H Rp Nt s) :
    (do
      let (s1, a1) ← smp.stall st ar s a
      smp.send_pending st ar s1 a1) ⦃ s' _ => EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ IdleSc st (L.cpu s) s' ∧
        StKeep st T Cs Scs Kp (L.cpu s) s s' ∧ L.curW s' = L.idleW s' ∧
        (L.actionW s' = L.actionW s ∨ L.actionW s' = 0#u64) ⦄ := by
  have q0 := h.1.choose_spec.choose_spec
  refine WP.spec_bind (smp.stall.entryNT (Kp := Kp) hA hKT s a h hI hG hKc hKa hKB hnq hcap) ?_
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
