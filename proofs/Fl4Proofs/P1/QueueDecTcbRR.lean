/-
P1: the thread family's `ReadRegisters` (`tcb.decode_read_registers`):
after the checks and the caller's restart, the optional suspend of the
target (keeping the caller not blocked, `sched.suspend.curR`), the copy of
the target's registers into the caller's message registers and IPC buffer
(user words, `XferHyps.buf`), the message info, and the caller set running.
-/
import Fl4Proofs.P1.QueueDecTcb
import Fl4Proofs.P1.QueueFinThr
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {U Ac : Set U64}
variable {Q : U64 → U64 → List U64} {R : U64 → List U64}

/-- A thread not blocked (on IPC or a reply) set running. -/
theorem sched.set_thread_state.running_nbr {s : S} {t : U64} (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (ht : t ∈ T) (hr : ¬ BlockedR (L.mem s (stA t))) :
    sched.set_thread_state st s t sched.TS_RUNNING ⦃ s' => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hSg, hS⟩ := h
  have hnb : ¬ Blocked (L.mem s (stA t)) := fun h => hr (Or.inl h)
  have hnr : L.mem s (stA t) ≠ sched.TS_BLOCKED_ON_REPLY := fun h => hr (Or.inr h)
  have hnv : L.mem s (stA t) ≠ sched.TS_BLOCKED_ON_RECV := fun h => hnb (Or.inr (Or.inl h))
  have hnoref : ∀ r ∈ Rp, L.mem s (rTcbA r) ≠ t := hX.noref (h0.tcbs t ht) hnr hnv
  refine WP.spec_mono (sts_all s t _ Q R h0 hB hX hS hSg ht not_blocked_running running_ne
    (Or.inr hnb) hnoref
    ⟨fun _ _ _ _ _ => runnable_running, fun _ _ _ => runnable_running, fun _ => runnable_running⟩) ?_
  rintro s' ⟨h1, hB1, hX1, hS1, hSg1, -, -⟩
  exact ⟨⟨Q, R, h1.congrX empty_congr⟩, hB1, hX1, hSg1, hS1⟩

theorem frame_reg_lt {j : U64} (hj : j.val < 18) :
    Aeneas.Std.Array.index_usize regs.FRAME_REGISTERS (UScalar.cast .Usize j) ⦃ _ => True ⦄ := by
  have hl : (UScalar.cast .Usize j : Usize).val < regs.FRAME_REGISTERS.val.length := by
    rw [regs.FRAME_REGISTERS.property]; rw [cast_usize_small (by omega)]; simp; omega
  exact WP.spec_mono (Aeneas.Std.Array.index_usize_spec _ _ hl) fun _ _ => trivial

theorem gp_reg_lt {j : U64} (hj : j.val < 2) :
    Aeneas.Std.Array.index_usize regs.GP_REGISTERS (UScalar.cast .Usize j) ⦃ _ => True ⦄ := by
  have hl : (UScalar.cast .Usize j : Usize).val < regs.GP_REGISTERS.val.length := by
    rw [regs.GP_REGISTERS.property]; rw [cast_usize_small (by omega)]; simp; omega
  exact WP.spec_mono (Aeneas.Std.Array.index_usize_spec _ _ hl) fun _ _ => trivial

theorem tcb.read_registers_loop0.xs {s0 s : S} {src n ct i : U64}
    (h : XS st T Cs Ω H Sg Rp Scs Nt Z U Ac ∅ Q R s0 s) (hc : ct ∈ T) :
    tcb.read_registers_loop0 st s src n ct i ⦃ r => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac ∅ Q R s0 r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold tcb.read_registers_loop0
  apply loop.spec_decr_nat (measure := fun y => 18 - y.2.val)
    (inv := fun y => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac ∅ Q R s0 y.1)
  · rintro ⟨s1, j⟩ h1
    simp only at h1
    try dsimp only
    unfold tcb.read_registers_loop0.body
    try dsimp only
    split
    swap
    · exact (WP.spec_ok _).2 h1
    split
    swap
    · exact (WP.spec_ok _).2 h1
    rename_i hj
    have hj' : j.val < 18 := by simpa [tcb.N_FRAME] using hj
    split
    swap
    · exact (WP.spec_ok _).2 h1
    simp only [lift, bind_ok]
    refine WP.spec_bind (frame_reg_lt hj') fun r _ => ?_
    refine WP.spec_bind (P0.obj.Tcb.reg.p0 st src s1 r hS) fun v _ => ?_
    refine WP.spec_bind (msg.msg_register.lt j) fun rg hrg => ?_
    refine WP.spec_bind (obj.Tcb.set_reg.xs (v := v) h1 hc hrg) fun s2 h2 => ?_
    step as ⟨j2, hj2⟩
    exact ⟨h2, by first | omega | (dsimp only; omega)⟩
  · exact h

theorem tcb.read_registers_loop1.xs {s0 s : S} {src n buf i : U64}
    (h : XS st T Cs Ω H Sg Rp Scs Nt Z U Ac ∅ Q R s0 s) (hb : BufOK U buf) (h0 : buf ≠ 0#u64) :
    tcb.read_registers_loop1 st s src n buf i ⦃ r => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac ∅ Q R s0 r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold tcb.read_registers_loop1
  apply loop.spec_decr_nat (measure := fun y => 18 - y.2.val)
    (inv := fun y => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac ∅ Q R s0 y.1)
  · rintro ⟨s1, j⟩ h1
    simp only at h1
    try dsimp only
    unfold tcb.read_registers_loop1.body
    try dsimp only
    split
    swap
    · exact (WP.spec_ok _).2 h1
    split
    swap
    · exact (WP.spec_ok _).2 h1
    rename_i hj
    have hj' : j.val < 18 := by simpa [tcb.N_FRAME] using hj
    simp only [lift, bind_ok]
    refine WP.spec_bind (frame_reg_lt hj') fun r _ => ?_
    refine WP.spec_bind (P0.obj.Tcb.reg.p0 st src s1 r hS) fun v _ => ?_
    step as ⟨j2, hj2⟩
    refine WP.spec_bind (msg.buf_set.xs (v := v) h1 hb h0 (by omega)) fun s2 h2 => ?_
    exact (WP.spec_ok _).2 ⟨h2, by first | omega | (dsimp only; omega)⟩
  · exact h

theorem tcb.read_registers_loop2.xs {s0 s : S} {src n ct k : U64}
    (h : XS st T Cs Ω H Sg Rp Scs Nt Z U Ac ∅ Q R s0 s) (hc : ct ∈ T) :
    tcb.read_registers_loop2 st s src n ct k ⦃ r => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac ∅ Q R s0 r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold tcb.read_registers_loop2
  apply loop.spec_decr_nat (measure := fun y => 2 - y.2.val)
    (inv := fun y => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac ∅ Q R s0 y.1)
  · rintro ⟨s1, j⟩ h1
    simp only at h1
    try dsimp only
    unfold tcb.read_registers_loop2.body
    try dsimp only
    split
    swap
    · exact (WP.spec_ok _).2 h1
    rename_i hj
    have hj' : j.val < 2 := by simpa [tcb.N_GP] using hj
    step as ⟨i0, hi0⟩
    split
    swap
    · exact (WP.spec_ok _).2 h1
    split
    swap
    · exact (WP.spec_ok _).2 h1
    simp only [lift, bind_ok]
    refine WP.spec_bind (gp_reg_lt hj') fun r _ => ?_
    refine WP.spec_bind (P0.obj.Tcb.reg.p0 st src s1 r hS) fun v _ => ?_
    refine WP.spec_bind (msg.msg_register.lt i0) fun rg hrg => ?_
    refine WP.spec_bind (obj.Tcb.set_reg.xs (v := v) h1 hc hrg) fun s2 h2 => ?_
    step as ⟨j2, hj2⟩
    exact ⟨h2, by first | omega | (dsimp only; omega)⟩
  · exact h

theorem tcb.read_registers_loop4.xs {s0 s : S} {src n ct k : U64}
    (h : XS st T Cs Ω H Sg Rp Scs Nt Z U Ac ∅ Q R s0 s) (hc : ct ∈ T) :
    tcb.read_registers_loop4 st s src n ct k ⦃ r => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac ∅ Q R s0 r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold tcb.read_registers_loop4
  apply loop.spec_decr_nat (measure := fun y => 2 - y.2.val)
    (inv := fun y => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac ∅ Q R s0 y.1)
  · rintro ⟨s1, j⟩ h1
    simp only at h1
    try dsimp only
    unfold tcb.read_registers_loop4.body
    try dsimp only
    split
    swap
    · exact (WP.spec_ok _).2 h1
    rename_i hj
    have hj' : j.val < 2 := by simpa [tcb.N_GP] using hj
    step as ⟨i0, hi0⟩
    split
    swap
    · exact (WP.spec_ok _).2 h1
    split
    swap
    · exact (WP.spec_ok _).2 h1
    simp only [lift, bind_ok]
    refine WP.spec_bind (gp_reg_lt hj') fun r _ => ?_
    refine WP.spec_bind (P0.obj.Tcb.reg.p0 st src s1 r hS) fun v _ => ?_
    refine WP.spec_bind (msg.msg_register.lt i0) fun rg hrg => ?_
    refine WP.spec_bind (obj.Tcb.set_reg.xs (v := v) h1 hc hrg) fun s2 h2 => ?_
    step as ⟨j2, hj2⟩
    exact ⟨h2, by first | omega | (dsimp only; omega)⟩
  · exact h

theorem tcb.read_registers_loop6.xs {s0 s : S} {src n ct k : U64}
    (h : XS st T Cs Ω H Sg Rp Scs Nt Z U Ac ∅ Q R s0 s) (hc : ct ∈ T) :
    tcb.read_registers_loop6 st s src n ct k ⦃ r => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac ∅ Q R s0 r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold tcb.read_registers_loop6
  apply loop.spec_decr_nat (measure := fun y => 2 - y.2.val)
    (inv := fun y => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac ∅ Q R s0 y.1)
  · rintro ⟨s1, j⟩ h1
    simp only at h1
    try dsimp only
    unfold tcb.read_registers_loop6.body
    try dsimp only
    split
    swap
    · exact (WP.spec_ok _).2 h1
    rename_i hj
    have hj' : j.val < 2 := by simpa [tcb.N_GP] using hj
    step as ⟨i0, hi0⟩
    split
    swap
    · exact (WP.spec_ok _).2 h1
    split
    swap
    · exact (WP.spec_ok _).2 h1
    simp only [lift, bind_ok]
    refine WP.spec_bind (gp_reg_lt hj') fun r _ => ?_
    refine WP.spec_bind (P0.obj.Tcb.reg.p0 st src s1 r hS) fun v _ => ?_
    refine WP.spec_bind (msg.msg_register.lt i0) fun rg hrg => ?_
    refine WP.spec_bind (obj.Tcb.set_reg.xs (v := v) h1 hc hrg) fun s2 h2 => ?_
    step as ⟨j2, hj2⟩
    exact ⟨h2, by first | omega | (dsimp only; omega)⟩
  · exact h

theorem tcb.read_registers_loop8.xs {s0 s : S} {src n ct k : U64}
    (h : XS st T Cs Ω H Sg Rp Scs Nt Z U Ac ∅ Q R s0 s) (hc : ct ∈ T) :
    tcb.read_registers_loop8 st s src n ct k ⦃ r => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac ∅ Q R s0 r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold tcb.read_registers_loop8
  apply loop.spec_decr_nat (measure := fun y => 2 - y.2.val)
    (inv := fun y => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac ∅ Q R s0 y.1)
  · rintro ⟨s1, j⟩ h1
    simp only at h1
    try dsimp only
    unfold tcb.read_registers_loop8.body
    try dsimp only
    split
    swap
    · exact (WP.spec_ok _).2 h1
    rename_i hj
    have hj' : j.val < 2 := by simpa [tcb.N_GP] using hj
    step as ⟨i0, hi0⟩
    split
    swap
    · exact (WP.spec_ok _).2 h1
    split
    swap
    · exact (WP.spec_ok _).2 h1
    simp only [lift, bind_ok]
    refine WP.spec_bind (gp_reg_lt hj') fun r _ => ?_
    refine WP.spec_bind (P0.obj.Tcb.reg.p0 st src s1 r hS) fun v _ => ?_
    refine WP.spec_bind (msg.msg_register.lt i0) fun rg hrg => ?_
    refine WP.spec_bind (obj.Tcb.set_reg.xs (v := v) h1 hc hrg) fun s2 h2 => ?_
    step as ⟨j2, hj2⟩
    exact ⟨h2, by first | omega | (dsimp only; omega)⟩
  · exact h

theorem tcb.read_registers_loop3.xs {s0 s : S} {src n buf k : U64}
    (h : XS st T Cs Ω H Sg Rp Scs Nt Z U Ac ∅ Q R s0 s) (hb : BufOK U buf) (h0 : buf ≠ 0#u64) :
    tcb.read_registers_loop3 st s src n buf k ⦃ r => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac ∅ Q R s0 r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold tcb.read_registers_loop3
  apply loop.spec_decr_nat (measure := fun y => 2 - y.2.val)
    (inv := fun y => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac ∅ Q R s0 y.1)
  · rintro ⟨s1, j⟩ h1
    simp only at h1
    try dsimp only
    unfold tcb.read_registers_loop3.body
    try dsimp only
    split
    swap
    · exact (WP.spec_ok _).2 h1
    rename_i hj
    have hj' : j.val < 2 := by simpa [tcb.N_GP] using hj
    step as ⟨i0, hi0⟩
    split
    swap
    · exact (WP.spec_ok _).2 h1
    simp only [lift, bind_ok]
    refine WP.spec_bind (gp_reg_lt hj') fun r _ => ?_
    refine WP.spec_bind (P0.obj.Tcb.reg.p0 st src s1 r hS) fun v _ => ?_
    step as ⟨i3, hi3⟩
    refine WP.spec_bind (msg.buf_set.xs (v := v) h1 hb h0 (by simp [tcb.N_FRAME] at hi0; omega)) fun s2 h2 => ?_
    step as ⟨j2, hj2⟩
    exact ⟨h2, by first | omega | (dsimp only; omega)⟩
  · exact h

theorem tcb.read_registers_loop5.xs {s0 s : S} {src n buf k : U64}
    (h : XS st T Cs Ω H Sg Rp Scs Nt Z U Ac ∅ Q R s0 s) (hb : BufOK U buf) (h0 : buf ≠ 0#u64) :
    tcb.read_registers_loop5 st s src n buf k ⦃ r => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac ∅ Q R s0 r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold tcb.read_registers_loop5
  apply loop.spec_decr_nat (measure := fun y => 2 - y.2.val)
    (inv := fun y => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac ∅ Q R s0 y.1)
  · rintro ⟨s1, j⟩ h1
    simp only at h1
    try dsimp only
    unfold tcb.read_registers_loop5.body
    try dsimp only
    split
    swap
    · exact (WP.spec_ok _).2 h1
    rename_i hj
    have hj' : j.val < 2 := by simpa [tcb.N_GP] using hj
    step as ⟨i0, hi0⟩
    split
    swap
    · exact (WP.spec_ok _).2 h1
    simp only [lift, bind_ok]
    refine WP.spec_bind (gp_reg_lt hj') fun r _ => ?_
    refine WP.spec_bind (P0.obj.Tcb.reg.p0 st src s1 r hS) fun v _ => ?_
    step as ⟨i3, hi3⟩
    refine WP.spec_bind (msg.buf_set.xs (v := v) h1 hb h0 (by simp [tcb.N_FRAME] at hi0; omega)) fun s2 h2 => ?_
    step as ⟨j2, hj2⟩
    exact ⟨h2, by first | omega | (dsimp only; omega)⟩
  · exact h

theorem tcb.read_registers_loop7.xs {s0 s : S} {src n buf k : U64}
    (h : XS st T Cs Ω H Sg Rp Scs Nt Z U Ac ∅ Q R s0 s) (hb : BufOK U buf) (h0 : buf ≠ 0#u64) :
    tcb.read_registers_loop7 st s src n buf k ⦃ r => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac ∅ Q R s0 r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold tcb.read_registers_loop7
  apply loop.spec_decr_nat (measure := fun y => 2 - y.2.val)
    (inv := fun y => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac ∅ Q R s0 y.1)
  · rintro ⟨s1, j⟩ h1
    simp only at h1
    try dsimp only
    unfold tcb.read_registers_loop7.body
    try dsimp only
    split
    swap
    · exact (WP.spec_ok _).2 h1
    rename_i hj
    have hj' : j.val < 2 := by simpa [tcb.N_GP] using hj
    step as ⟨i0, hi0⟩
    split
    swap
    · exact (WP.spec_ok _).2 h1
    simp only [lift, bind_ok]
    refine WP.spec_bind (gp_reg_lt hj') fun r _ => ?_
    refine WP.spec_bind (P0.obj.Tcb.reg.p0 st src s1 r hS) fun v _ => ?_
    step as ⟨i3, hi3⟩
    refine WP.spec_bind (msg.buf_set.xs (v := v) h1 hb h0 (by simp [tcb.N_FRAME] at hi0; omega)) fun s2 h2 => ?_
    step as ⟨j2, hj2⟩
    exact ⟨h2, by first | omega | (dsimp only; omega)⟩
  · exact h

theorem tcb.read_registers_loop9.xs {s0 s : S} {src n buf k : U64}
    (h : XS st T Cs Ω H Sg Rp Scs Nt Z U Ac ∅ Q R s0 s) (hb : BufOK U buf) (h0 : buf ≠ 0#u64) :
    tcb.read_registers_loop9 st s src n buf k ⦃ r => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac ∅ Q R s0 r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold tcb.read_registers_loop9
  apply loop.spec_decr_nat (measure := fun y => 2 - y.2.val)
    (inv := fun y => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac ∅ Q R s0 y.1)
  · rintro ⟨s1, j⟩ h1
    simp only at h1
    try dsimp only
    unfold tcb.read_registers_loop9.body
    try dsimp only
    split
    swap
    · exact (WP.spec_ok _).2 h1
    rename_i hj
    have hj' : j.val < 2 := by simpa [tcb.N_GP] using hj
    step as ⟨i0, hi0⟩
    split
    swap
    · exact (WP.spec_ok _).2 h1
    simp only [lift, bind_ok]
    refine WP.spec_bind (gp_reg_lt hj') fun r _ => ?_
    refine WP.spec_bind (P0.obj.Tcb.reg.p0 st src s1 r hS) fun v _ => ?_
    step as ⟨i3, hi3⟩
    refine WP.spec_bind (msg.buf_set.xs (v := v) h1 hb h0 (by simp [tcb.N_FRAME] at hi0; omega)) fun s2 h2 => ?_
    step as ⟨j2, hj2⟩
    exact ⟨h2, by first | omega | (dsimp only; omega)⟩
  · exact h

end


section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {U Ac : Set U64}

set_option maxHeartbeats 8000000 in
/-- **`read_registers`** from the caller `curW s` not blocked: the invariants after. -/
theorem tcb.read_registers.bxi {A : Type _} {ar : machine.Arch A} (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    {s : S} {a : A} {src n : U64} {sus call : Bool} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hs : src ∈ T)
    (hna : L.actionW s ≠ src) (hct : L.curW s ∈ T) (hnb : ¬ BlockedR (L.mem s (stA (L.curW s))))
    (hU : UserOK st T Cs Ω H U s) (hG : XG st T Cs Ω H Sg Scs Z P3Ok s) :
    tcb.read_registers st ar s a src sus n call ⦃ r => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ⦄ := by
  unfold tcb.read_registers
  refine WP.spec_bind (sched.cur_thread.spec s) fun ct ect => ?_
  have e : ct = L.curW s := ect
  subst e
  refine WP.spec_bind (Pₘ := fun r : S × A => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧ L.ksb r.1 = L.ksb s ∧
      ¬ BlockedR (L.mem r.1 (stA (L.curW s))) ∧ XG st T Cs Ω H Sg Scs Z P3Ok r.1) ?_ ?_
  · split
    · obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
      refine WP.spec_mono (WP.spec_and (sched.suspend.blk s a src ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ hs hna)
        (sched.suspend.curR s a src (L.curW s) Q R h0 hs hB hX hSg hS hna (hX.2.2.yt.2.1 src hs) hct)) ?_
      rintro ⟨s1, a1⟩ ⟨⟨h1, f1⟩, ⟨-, -, -, -, nb⟩⟩
      exact ⟨h1, f1.1, nb hnb, hG.foot f1⟩
    · exact (WP.spec_ok _).2 ⟨h, rfl, hnb, hG⟩
  rintro ⟨s1, a1⟩ ⟨h1, k1, nb1, hG1⟩
  try simp only [uncurry_apply_pair]
  split
  swap
  · exact WP.spec_bind (sched.set_thread_state.running_nbr h1.bxi hct nb1) fun s2 h2 => (WP.spec_ok _).2 h2
  obtain ⟨Q1, R1, x1⟩ := BXI.xs (BlkOK.bxi h1) (hU.ksb k1)
  have x1s := x1
  have TL : ∀ (s' : S) (x y : U64), XS st T Cs Ω H Sg Rp Scs Nt Z U Ac ∅ Q1 R1 s1 s' →
      (do
        let i ← lift (core.num.U64.wrapping_add x y)
        let mi ← msginfo.MessageInfo.new 0#u64 0#u64 0#u64 i
        let s5 ← msg.set_msg_info st s' (L.curW s) mi
        let s6 ← sched.set_thread_state st s5 (L.curW s) sched.TS_RUNNING
        ok (s6, a1)) ⦃ r => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ⦄ := fun s' x y x' => by
    simp only [lift, bind_ok]
    refine WP.spec_bind (P0.msginfo.MessageInfo.new.p0 _ _ _ _) fun mi _ => ?_
    refine WP.spec_bind (Pₘ := fun s5 => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac ∅ Q1 R1 s1 s5) ?_ fun s5 x5 => ?_
    · unfold msg.set_msg_info
      exact WP.spec_bind (P0.msginfo.MessageInfo.to_word.p0 _) fun w _ =>
        obj.Tcb.set_reg.xs (v := w) x' hct (by simp [layout.reg.MSG_INFO, layout.reg.RSI])
    have est : L.mem s5 (stA (L.curW s)) = L.mem s1 (stA (L.curW s)) := by
      rw [stA_eq]; exact x5.fr.2.2.2.2.1 _ hct _ (by simp) (by simp) (by simp)
    refine WP.spec_bind (sched.set_thread_state.running_nbr x5.bxi hct (est ▸ nb1)) fun s6 h6 => ?_
    exact (WP.spec_ok _).2 h6
  refine WP.spec_bind (E.buf _ _ _ _ s1 (L.curW s) hG1 x1.1 hct) fun buf hb => ?_
  refine WP.spec_bind (obj.Tcb.set_reg.xs (v := 0#u64) x1s hct (by simp [layout.reg.BADGE, layout.reg.RDI]))
    fun s2 x2 => ?_
  refine WP.spec_bind (tcb.read_registers_loop0.xs x2 hct) ?_
  rintro ⟨s3, i⟩ x3
  try simp only [uncurry_apply_pair]
  -- the remaining tree: loops, then the tail
  have B0 : ∀ {b : Bool}, (buf != 0#u64) = b → b = true → buf ≠ 0#u64 := fun {b} hb hb' => by
    subst hb'; simpa using hb
  repeat' (first
    | exact TL _ _ _ ‹_›
    | (refine WP.spec_bind (tcb.read_registers_loop1.xs ‹_› hb (by simpa using ‹(buf != 0#u64) = true›)) ?_
       rintro ⟨_, _⟩ _; try simp only [uncurry_apply_pair])
    | (refine WP.spec_bind (tcb.read_registers_loop3.xs ‹_› hb (by simpa using ‹(buf != 0#u64) = true›)) ?_
       rintro ⟨_, _⟩ _; try simp only [uncurry_apply_pair])
    | (refine WP.spec_bind (tcb.read_registers_loop5.xs ‹_› hb (by simpa using ‹(buf != 0#u64) = true›)) ?_
       rintro ⟨_, _⟩ _; try simp only [uncurry_apply_pair])
    | (refine WP.spec_bind (tcb.read_registers_loop7.xs ‹_› hb (by simpa using ‹(buf != 0#u64) = true›)) ?_
       rintro ⟨_, _⟩ _; try simp only [uncurry_apply_pair])
    | (refine WP.spec_bind (tcb.read_registers_loop9.xs ‹_› hb (by simpa using ‹(buf != 0#u64) = true›)) ?_
       rintro ⟨_, _⟩ _; try simp only [uncurry_apply_pair])
    | (refine WP.spec_bind (tcb.read_registers_loop2.xs ‹_› hct) ?_
       rintro ⟨_, _⟩ _; try simp only [uncurry_apply_pair])
    | (refine WP.spec_bind (tcb.read_registers_loop4.xs ‹_› hct) ?_
       rintro ⟨_, _⟩ _; try simp only [uncurry_apply_pair])
    | (refine WP.spec_bind (tcb.read_registers_loop6.xs ‹_› hct) ?_
       rintro ⟨_, _⟩ _; try simp only [uncurry_apply_pair])
    | (refine WP.spec_bind (tcb.read_registers_loop8.xs ‹_› hct) ?_
       rintro ⟨_, _⟩ _; try simp only [uncurry_apply_pair])
    | split
    | (step as ⟨_, _⟩))


set_option maxHeartbeats 4000000 in
/-- **`ReadRegisters`** after the stall, the caller's buffer from `XferHyps`. -/
theorem tcb.decode_read_registers.dec {A : Type _} {ar : machine.Arch A} (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    {s s1 : S} {a1 : A} {t len buf : U64} {call : Bool} {slot : obj.Slot}
    {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Thread t) extra) (hE : EntAt st P3Ok s)
    (h1 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s1) :
    tcb.decode_read_registers st ar s1 a1 t { length := len, buf, call, slot, extra } ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have ht : t ∈ T := D.cap.2.1 t rfl
  have hct : L.curW s ∈ T := D.bxi.1.choose_spec.choose_spec.curT
  have c1 := h1.cur0 D
  have est : L.mem s1 (stA (L.curW s1)) = L.mem s (stA (L.curW s)) := by
    rw [h1.cur, stA_eq]; exact h1.fld _ hct _ (by simp) (by simp)
  have hr := runnable_ok D.run
  unfold tcb.decode_read_registers
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · simp only [error.truncated, error.sys, bind_ok]; exact (WP.spec_ok _).2 (Cur0.post c1)
  refine WP.spec_bind (P0.tcb.arg.p0 st s1 _ _ hS) fun flags _ => ?_
  refine WP.spec_bind (P0.tcb.arg.p0 st s1 _ _ hS) fun n _ => ?_
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · step as ⟨i, _⟩
    simp only [error.range, error.sys, bind_ok]; exact (WP.spec_ok _).2 (Cur0.post c1)
  step as ⟨i, _⟩
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · simp only [error.range, error.sys, bind_ok]; exact (WP.spec_ok _).2 (Cur0.post c1)
  refine WP.spec_bind (sched.cur_thread.spec s1) fun ct ect => ?_
  simp only [obj.Tcb.Insts.CoreCmpPartialEqTcb.eq, bind_ok]
  split
  · simp only [error.illegal, error.sys, bind_ok]; exact (WP.spec_ok _).2 (Cur0.post c1)
  rename_i hne
  have hne' : t ≠ L.curW s := by
    intro e; apply hne; rw [e, show ct = L.curW s from ect.trans h1.cur]; simp
  refine WP.spec_bind (WP.spec_and (h1.restart D)
    (tcb.restart_caller.blk (Es := ∅) s1 h1.bxi.blk (est ▸ hr.1) (est ▸ hr.2))) ?_
  rintro s2 ⟨⟨h2, hna, ec2, -⟩, ⟨-, f2, est2, -⟩⟩
  rw [h1.cur] at est2
  simp only [lift, bind_ok]
  have hU2 : UserOK st T Cs Ω H U s2 := D.user.ksb (f2.1.trans h1.node.1)
  have nb2 : ¬ BlockedR (L.mem s2 (stA (L.curW s2))) := by rw [ec2, est2]; exact nbr_restart
  rw [← ec2] at hct
  refine WP.spec_bind (tcb.read_registers.bxi E h2 ht (hna t ht) hct nb2 hU2
    ⟨s, hE, Cur0W.trans c1.fr (Foot.cur0w f2 (Set.empty_subset _))⟩) ?_
  rintro ⟨s3, a3⟩ h3
  exact (WP.spec_ok _).2 (DecPost.ok_bxi h3)

end

end Fl4Proofs.P1
