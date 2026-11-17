/-
P1: InvGaps' `reply` family: `do_reply_transfer` (seL4 `doReplyTransfer`)
keeps the invariants.  Pieces: `handle_fault_reply` writes only the
receiver's user context (`XferFoot T ∅`); the woken thread's SC is active or
null after `reply_remove` (`ipc.reply_remove.blk`).
-/
import Fl4Proofs.P1.QueueEntryGaps
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}

/-! ## `handle_fault_reply` writes the receiver's user context -/

theorem obj.Tcb.set_reg.rf {s : S} {t r v : U64} (hT : TcbPlaced T) (ht : t ∈ T) (hr : r.val < 384) :
    obj.Tcb.set_reg st t s r v ⦃ s' => WritesIn st s s' (XferFoot T ∅) ⦄ :=
  WP.spec_mono (obj.Tcb.set_reg.wrK s t r v (hT t ht) hr) fun s' ⟨K, hK, e⟩ => by
    subst e
    exact (writesIn_wr (field_aligned (hT t ht) (by omega) (by omega))).mono fun b e =>
      Or.inl ⟨t, ht, K, by omega, by omega, e⟩

theorem obj.Tcb.set_debug_reg.rf {s : S} {t i v : U64} (hT : TcbPlaced T) (ht : t ∈ T) (hi : i.val < 8) :
    obj.Tcb.set_debug_reg st t s i v ⦃ s' => WritesIn st s s' (XferFoot T ∅) ⦄ := by
  unfold obj.Tcb.set_debug_reg
  simp only [lift, bind_ok]
  refine WP.spec_mono (LawfulStore.write_spec s _ v) fun s' e => ?_
  subst e
  have hta := hT t ht
  let K : U64 := ⟨BitVec.ofNat 64 (448 + 8 * i.val)⟩
  have hK : K.val = 448 + 8 * i.val := by
    show (BitVec.ofNat 64 (448 + 8 * i.val)).toNat = _
    simp; omega
  have ea : core.num.U64.wrapping_add (core.num.U64.wrapping_add t layout.tcb.DEBUG)
      (core.num.U64.wrapping_mul i 8#u64) = core.num.U64.wrapping_add t K := by
    apply UScalar.eq_of_val_eq
    rw [field_val hta (by omega)]
    have := hta.fits
    simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits,
      layout.tcb.DEBUG] at ⊢
    omega
  rw [ea]
  exact (writesIn_wr (field_aligned hta (by omega) (by omega))).mono fun b e =>
    Or.inl ⟨t, ht, K, by omega, by omega, e⟩

theorem rf_trans {s1 s2 s3 : S} (h1 : WritesIn st s1 s2 (XferFoot T ∅)) (h2 : WritesIn st s2 s3 (XferFoot T ∅)) :
    WritesIn st s1 s3 (XferFoot T ∅) := (h1.trans h2).mono fun _ hb => hb.elim id id

theorem faults.copy_mrs_fault_reply_loop0.rf {s0 s : S} {snd rcv : U64} {regs : Slice U64} {n i : Usize}
    (hT : TcbPlaced T) (hr : rcv ∈ T) (hR : ∀ x ∈ regs.val, x.val < 384) (h : WritesIn st s0 s (XferFoot T ∅)) :
    faults.copy_mrs_fault_reply_loop0 st s snd rcv regs n i ⦃ r => WritesIn st s0 r.1 (XferFoot T ∅) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold faults.copy_mrs_fault_reply_loop0
  apply loop.spec_decr_nat (measure := fun y => n.val - y.2.val)
    (inv := fun y => WritesIn st s0 y.1 (XferFoot T ∅))
  · rintro ⟨s1, j⟩ h1
    simp only at h1
    dsimp only
    unfold faults.copy_mrs_fault_reply_loop0.body
    dsimp only
    split
    · rename_i hjn
      split
      · rename_i hj
        have hj' : j.val < regs.val.length := by simpa using hj
        simp only [lift, bind_ok]
        split
        · refine WP.spec_bind (Slice.index_usize_spec regs j hj') fun rg hrg => ?_
          have hrg' : rg.val < 384 := hR rg (hrg ▸ List.getElem_mem hj')
          refine WP.spec_bind (msg.msg_register.lt _) fun i4 _ => ?_
          refine WP.spec_bind (P0.obj.Tcb.reg.p0 st snd s1 i4 hS) fun v _ => ?_
          refine WP.spec_bind (P0.regs.sanitise.p0 rg v) fun v5 _ => ?_
          refine WP.spec_bind (obj.Tcb.set_reg.rf (v := v5) (s := s1) hT hr hrg') fun s2 w2 => ?_
          step as ⟨j2, hj2⟩
          refine ⟨rf_trans h1 w2, ?_⟩
          have : j.val < n.val := by simpa using hjn
          omega
        · exact (WP.spec_ok _).2 h1
      · exact (WP.spec_ok _).2 h1
    · exact (WP.spec_ok _).2 h1
  · exact h

theorem faults.copy_mrs_fault_reply_loop1.rf {s0 s : S} {rcv buf : U64} {regs : Slice U64} {n i : Usize}
    (hT : TcbPlaced T) (hr : rcv ∈ T) (hR : ∀ x ∈ regs.val, x.val < 384) (h : WritesIn st s0 s (XferFoot T ∅)) :
    faults.copy_mrs_fault_reply_loop1 st s rcv regs n i buf ⦃ s' => WritesIn st s0 s' (XferFoot T ∅) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold faults.copy_mrs_fault_reply_loop1
  apply loop.spec_decr_nat (measure := fun y => n.val - y.2.val)
    (inv := fun y => WritesIn st s0 y.1 (XferFoot T ∅))
  · rintro ⟨s1, j⟩ h1
    simp only at h1
    dsimp only
    unfold faults.copy_mrs_fault_reply_loop1.body
    dsimp only
    split
    · rename_i hjn
      split
      · rename_i hj
        have hj' : j.val < regs.val.length := by simpa using hj
        refine WP.spec_bind (Slice.index_usize_spec regs j hj') fun rg hrg => ?_
        have hrg' : rg.val < 384 := hR rg (hrg ▸ List.getElem_mem hj')
        simp only [lift, bind_ok]
        refine WP.spec_bind (P0.msg.buf_get.p0 st s1 buf _ hS) fun v _ => ?_
        refine WP.spec_bind (P0.regs.sanitise.p0 rg v) fun v5 _ => ?_
        refine WP.spec_bind (obj.Tcb.set_reg.rf (v := v5) (s := s1) hT hr hrg') fun s2 w2 => ?_
        step as ⟨j2, hj2⟩
        refine ⟨rf_trans h1 w2, ?_⟩
        have : j.val < n.val := by simpa using hjn
        omega
      · exact (WP.spec_ok _).2 h1
    · exact (WP.spec_ok _).2 h1
  · exact h

theorem faults.copy_mrs_fault_reply.rf {s : S} {snd rcv len : U64} {regs : Slice U64}
    (hT : TcbPlaced T) (hr : rcv ∈ T) (hR : ∀ x ∈ regs.val, x.val < 384) :
    faults.copy_mrs_fault_reply st s snd rcv regs len ⦃ s' => WritesIn st s s' (XferFoot T ∅) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold faults.copy_mrs_fault_reply
  simp only [lift, bind_ok]
  refine WP.spec_bind (Pₘ := fun _ => True) (by split <;> exact (WP.spec_ok _).2 trivial) fun n _ => ?_
  refine WP.spec_bind (faults.copy_mrs_fault_reply_loop0.rf (snd := snd) (n := n) (i := 0#usize) hT hr hR
    (WritesIn.refl s _)) ?_
  rintro ⟨s1, i2⟩ w1
  simp only at w1
  try simp only [WP.uncurry'_pair]
  try simp only [uncurry_apply_pair]
  split
  · refine WP.spec_bind (P0.msg.lookup_ipc_buffer.p0 st s1 false snd hS) fun buf _ => ?_
    split
    · exact faults.copy_mrs_fault_reply_loop1.rf hT hr hR w1
    · exact (WP.spec_ok _).2 w1
  · exact (WP.spec_ok _).2 w1

theorem debug.configure_single_stepping.rf {A : Type _} {ar : machine.Arch A} {s : S} {a : A} {t bp n : U64}
    {rep : Bool} (hT : TcbPlaced T) (ht : t ∈ T) :
    debug.configure_single_stepping st ar s a t bp n rep ⦃ r => WritesIn st s r.2.1 (XferFoot T ∅) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold debug.configure_single_stepping
  refine WP.spec_bind (Pₘ := fun s1 => WritesIn st s s1 (XferFoot T ∅)) ?_ fun s1 w1 => ?_
  · split
    · refine WP.spec_bind (obj.Tcb.set_debug_reg.rf (s := s) (v := 0#u64) hT ht (by simp [debug.SS_ENABLED]))
        fun s2 w2 => ?_
      refine WP.spec_bind (P0.obj.Tcb.reg.p0 st t s2 _ hS) fun i _ => ?_
      unfold debug.EFLAGS_TF
      step as ⟨i1, _⟩
      simp only [lift, bind_ok]
      exact WP.spec_mono (obj.Tcb.set_reg.rf (s := s2) hT ht (by simp [layout.reg.FLAGS])) fun s3 w3 =>
        rf_trans w2 w3
    · exact obj.Tcb.set_debug_reg.rf hT ht (by simp [debug.SS_ENABLED])
  refine WP.spec_bind (obj.Tcb.set_debug_reg.rf (s := s1) (v := n) hT ht (by simp [debug.SS_COUNT])) fun s2 w2 => ?_
  exact (WP.spec_ok _).2 (rf_trans w1 w2)

theorem regs_lt {n : Usize} (l : List U64) (hl : l.length = n.val) (h : ∀ x ∈ l, x.val < 384) :
    ∀ x ∈ (Aeneas.Std.Array.make n l hl).val, x.val < 384 := by
  intro x hx; exact h x (by simpa [Aeneas.Std.Array.make] using hx)

/-- **`handle_fault_reply`** writes only the receiver's user context. -/
theorem faults.handle_fault_reply.rf {A : Type _} {ar : machine.Arch A} {s : S} {a : A} {rcv snd : U64}
    (hT : TcbPlaced T) (hr : rcv ∈ T) :
    faults.handle_fault_reply st ar s a rcv snd ⦃ r => WritesIn st s r.2.1 (XferFoot T ∅) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold faults.handle_fault_reply
  refine WP.spec_bind (P0.msg.msg_info.p0 st s snd hS) fun tag _ => ?_
  refine WP.spec_bind (P0.obj.Tcb.fault_type.p0 st rcv s hS) fun ty _ => ?_
  have C : ∀ (regs : Slice U64), (∀ x ∈ regs.val, x.val < 384) →
      (do
        let s2 ← faults.copy_mrs_fault_reply st s snd rcv regs tag.length
        ok (decide (tag.label = 0#u64), s2, a)) ⦃ r => WritesIn st s r.2.1 (XferFoot T ∅) ⦄ := fun regs hR =>
    WP.spec_bind (faults.copy_mrs_fault_reply.rf hT hr hR) fun s2 w2 => (WP.spec_ok _).2 w2
  split
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  split
  · simp only [lift, bind_ok]
    exact C _ (by simp [faults.SYSCALL_MESSAGE, Aeneas.Std.Array.make, Aeneas.Std.Array.to_slice, layout.reg.RAX,
      layout.reg.RBX, layout.reg.RCX, layout.reg.RDX, layout.reg.RSI, layout.reg.RDI, layout.reg.RBP, layout.reg.R8,
      layout.reg.R9, layout.reg.R10, layout.reg.R11, layout.reg.R12, layout.reg.R13, layout.reg.R14, layout.reg.R15,
      layout.reg.FAULT_IP, layout.reg.RSP, layout.reg.FLAGS])
  split
  · simp only [lift, bind_ok]
    exact C _ (by simp [faults.EXCEPTION_MESSAGE, Aeneas.Std.Array.make, Aeneas.Std.Array.to_slice,
      layout.reg.FAULT_IP, layout.reg.RSP, layout.reg.FLAGS])
  split
  · simp only [lift, bind_ok]
    exact C _ (by simp [faults.TIMEOUT_REPLY_MESSAGE, Aeneas.Std.Array.make, Aeneas.Std.Array.to_slice,
      layout.reg.RAX, layout.reg.RBX, layout.reg.RCX, layout.reg.RDX, layout.reg.RSI, layout.reg.RDI, layout.reg.RBP,
      layout.reg.R8, layout.reg.R9, layout.reg.R10, layout.reg.R11, layout.reg.R12, layout.reg.R13, layout.reg.R14,
      layout.reg.R15, layout.reg.FAULT_IP, layout.reg.RSP, layout.reg.FLAGS, layout.reg.TLS_BASE])
  split
  · refine WP.spec_bind (P0.obj.Tcb.fault_w0.p0 st rcv s hS) fun w0 _ => ?_
    split
    · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
    refine WP.spec_bind (Pₘ := fun _ => True) (by
      split
      · exact (WP.spec_ok _).2 trivial
      · exact WP.spec_bind (msg.msg_register.lt _) fun _ _ => WP.spec_mono (P0.obj.Tcb.reg.p0 st snd s _ hS)
          fun _ _ => trivial) fun ni _ => ?_
    refine WP.spec_bind (debug.configure_single_stepping.rf (s := s) (a := a) (bp := 0#u64) (n := ni) (rep := true)
      hT hr) ?_
    rintro ⟨b, s1, a1⟩ w1
    try simp only [WP.uncurry'_pair]
    exact (WP.spec_ok _).2 w1
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)

/-! ## Field and state writes from `BXI` -/

theorem bxi_field {s : S} {y K v : U64} (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hy : y ∈ T)
    (hK : K.val < 4096) (hK8 : K.val % 8 = 0)
    (hKn : K.val ≠ 3464 ∧ K.val ≠ 3360 ∧ K.val ≠ 3328 ∧ K.val ≠ 3592 ∧ K.val ≠ 3368 ∧ K.val ≠ 3472 ∧
      K.val ≠ 3480 ∧ K.val ≠ 3488 ∧ K.val ≠ 3496 ∧ K.val ≠ 3504 ∧ K.val ≠ 3520 ∧ K.val ≠ 3448 ∧ K.val ≠ 3336)
    (hKt : K.val < 3528 ∨ 3592 ≤ K.val) :
    BXI st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s (core.num.U64.wrapping_add y K) v) := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hSg, hS⟩ := h
  obtain ⟨a1, a2, a3, a4, a5, a6, k1, k2, k3, k4, k5, k6, k7⟩ := hKn
  obtain ⟨b1, b2⟩ := bx_field (v := v) h0 hB hX hSg.sub hy hK hK8 ⟨a1, a2, a3, a4, a5, a6⟩ hKt
  exact ⟨⟨Q, R, inv_wr_field h0 hy hK hK8 ⟨k1, k2, k3, k4, a4, k5, k6, a3, k7⟩⟩, b1, b2,
    ⟨hSg.sub, fun b hb => by rw [L.ksb_wr]; exact hSg.ks b hb, fun o h1 h2 => by rw [L.ksb_wr]; exact hSg.ksΩ o h1 h2⟩,
    SCsOK.field h0 hS hX hy hK hK8 a1⟩

/-- `set_thread_state` of a thread that is not blocked to a state that is
not blocked, the thread being in no queue and not the candidate. -/
theorem sts_bxi {s : S} {t v : U64} (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T)
    (hv : ¬ Blocked v) (hvr : v ≠ sched.TS_BLOCKED_ON_REPLY ∧ v ≠ sched.TS_BLOCKED_ON_RECV)
    (hold : ¬ Blocked (L.mem s (stA t)) ∧ L.mem s (stA t) ≠ sched.TS_BLOCKED_ON_REPLY ∧
      L.mem s (stA t) ≠ sched.TS_BLOCKED_ON_RECV)
    (hq : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64) (hr : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64)
    (hna : L.actionW s ≠ t) :
    sched.set_thread_state st s t v ⦃ s' => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ L.mem s' (stA t) = v ∧
      KeepT st T Cs Rp Scs Nt t s s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hSg, hS⟩ := h
  refine WP.spec_mono (sts_all s t v Q R h0 hB hX hS hSg ht hv hvr (Or.inr hold.1)
    (hX.noref (h0.tcbs t ht) hold.2.1 hold.2.2)
    ⟨fun c hc' p hp hm => absurd hm (h0.notQ ht hq hc' hp), fun c hc' hm => absurd hm (h0.notR ht hr hc'),
      fun e => absurd e hna⟩) ?_
  rintro s' ⟨h1, hB1, hX1, hS1, hSg1, e1, k1⟩
  exact ⟨⟨⟨Q, R, h1.congrX empty_congr⟩, hB1, hX1, hSg1, hS1⟩, e1, k1⟩

/-! ## The scheduling tail of `do_reply_transfer` -/

/-- The facts about the replied-to thread `i` at the tail. -/
structure RTail (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (Ac : Set U64) (s : S) (i : U64) :
    Prop where
  mem : i ∈ T
  nb : ¬ Blocked (L.mem s (stA i))
  nrp : L.mem s (stA i) ≠ sched.TS_BLOCKED_ON_REPLY
  nrc : L.mem s (stA i) ≠ sched.TS_BLOCKED_ON_RECV
  nq : (L.mem s (inqA i) &&& sched.Q_QUEUED) = 0#u64
  nr : (L.mem s (inqA i) &&& sched.Q_RELEASE) = 0#u64
  na : L.actionW s ≠ i
  ni : L.idleW s ≠ i
  ac : L.mem s (scA i) ≠ 0#u64 → L.mem s (scA i) ∈ Ac

theorem RTail.cb {s : S} {i : U64} (h : RTail st T Ac s i) : CanBlock st T Ac s i :=
  ⟨h.mem, h.nb, h.nrp, h.nq, h.nr, h.na, h.ni, h.ac⟩

theorem RTail.switch {s : S} {i : U64} (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (r : RTail st T Ac s i)
    (hrun : Runnable (L.mem s (stA i))) :
    sched.possible_switch_to st s i ⦃ s' => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hSg, hS⟩ := h
  exact WP.spec_mono (sched.possible_switch_to.sch s i Q R h0 hB hSg r.mem hrun r.ac)
    fun s' ⟨⟨hq, hb, f⟩, _, _⟩ => ⟨hq, hb, hX.fr f, hSg.fr f, hS.fr f⟩

theorem RTail.postpone {s : S} {i : U64} (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (r : RTail st T Ac s i)
    (hrun : Runnable (L.mem s (stA i))) (hi0 : L.mem s (scA i) ≠ 0#u64) :
    sched.postpone st s (L.mem s (scA i)) ⦃ s' => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hSg, hS⟩ := h
  have hT := h0.tcbs
  obtain ⟨hcS, htc, hcc⟩ := hX.2.2.bound i r.mem hi0
  have hm : scCoreA (L.mem s (scA i)) ∈ Ω := hSg.sub _ (hX.1.fixW _ hcS).2
  refine WP.spec_mono (sched.postpone.all s _ Q R h0 (by rw [htc]; exact r.mem) hB hX hSg (by rw [htc]; exact r.nr)
    (h0.omega _ hm) hcc (by rw [htc]; exact hrun) (by rw [htc]; exact r.na) (by rw [htc]; exact hi0)
    (by rw [htc]; exact r.ac hi0)) ?_
  rintro s' ⟨Q', R', h1, hB1, hX1, hSg1, f1, -⟩
  exact ⟨⟨Q', R', h1⟩, hB1, hX1, hSg1, hS.fr f1⟩

theorem sporadic.unblock_check.kw {X : Set U64} {Ac Es : Set U64} (s : S) (t i : U64) {Q : U64 → U64 → List U64}
    {R : U64 → List U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T Ac s)
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (ht : t ∈ T)
    (i_post : i = L.mem s (scA t)) (hi0 : i ≠ 0#u64) (hiA : i ∈ Ac) :
    sporadic.unblock_check st s i ⦃ s' => Foot st T Cs Sg Scs Z Es s s' ⦄ := by
  have hT := h.tcbs
  have hsub := hSg.sub
  have hbt : L.mem s (scA t) ≠ 0#u64 := by rw [← i_post]; exact hi0
  obtain ⟨hiS, -, -⟩ := hX.2.2.bound t ht hbt
  rw [← i_post] at hiS
  have hW : RefillsWF st s i (Z i) := hS.wf hiS hiA
  have hSCin : SCin st s Ω i (Z i) := ⟨hW, hX.1.scW i hiS⟩
  have hN' := h.nodes _ h.cur
  have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
  have aR : Aligned (L.nodeA s layout.node.REPROGRAM) := nodeAt_aligned hN' (by rw [rp]; omega) (by rw [rp])
  have oR : Outside (L.nodeA s layout.node.REPROGRAM) i (Z i) :=
    hSCin.node_out h.omega h.cur hN' (by rw [rp]; omega) (by rw [rp])
  exact WP.spec_mono (sporadic.unblock_check.fr hW ⟨aR, oR⟩) fun s3 w => Foot.of w fun b hb => by
    rcases hb with hb | rfl
    · exact InRing.kw hiS hb
    · unfold LawfulStore.nodeA; exact kw_node h.cur (by rw [rp]; omega) (by rw [rp]; omega)

set_option maxHeartbeats 4000000 in
theorem RTail.timeout {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) {s : S} {a : A} {i : U64} {f : error.Fault}
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (r : RTail st T Ac s i) (hU : UserOK st T Cs Ω H U s)
    (hcap : obj.Tcb.slot i layout.tcb.SLOT_TIMEOUT_HANDLER ⦃ sl =>
      obj.Slot.cap st sl s ⦃ c => CapTyped H Rp Nt c ⦄ ⦄) (hG : XG st T Cs Ω H Sg Scs Z P3Ok s) :
    faults.handle_timeout st ar s a i f ⦃ s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ :=
  WP.spec_mono (faults.handle_timeout.bxi hA (xferOK_of hA E) s a i f (XG.faultG hG h.blk hU r.cb) h.blk hU r.cb
    hcap) fun r hr => by
    obtain ⟨s', a'⟩ := r; exact BlkOK.bxi (by simpa using hr)

/-- The tail of `do_reply_transfer`: the replied-to thread with an SC is
switched to, has its timeout fault raised, or is postponed. -/
theorem reply_tail {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (tmoAny : ∀ (Ac : Set U64) (s : S) (t : U64), BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → t ∈ T →
      obj.Tcb.slot t layout.tcb.SLOT_TIMEOUT_HANDLER ⦃ sl => obj.Slot.cap st sl s ⦃ c => CapTyped H Rp Nt c ⦄ ⦄)
    {s3 : S} {a2 : A} {i ft : U64}
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s3) (r : RTail st T Ac s3 i) (hU : UserOK st T Cs Ω H U s3)
    (hG : XG st T Cs Ω H Sg Scs Z P3Ok s3) :
    (do
      let i3 ← obj.Tcb.sc st i s3
      let b2 ← obj.Sc.is_null i3
      if b2 then ok (s3, a2)
      else
        let b3 ← sched.is_runnable st s3 i
        if b3 then
          let b4 ← sporadic.ready st s3 i3
          if b4 then
            let b5 ← sporadic.sufficient st ar s3 a2 i3 0#u64
            if b5 then
              let s4 ← sched.possible_switch_to st s3 i
              ok (s4, a2)
            else
              let b6 ← faults.valid_timeout_handler st s3 i
              if b6 then
                if ft != fl4_abi.consts.fault.Timeout then
                  let badge ← obj.Sc.badge st i3 s3
                  faults.handle_timeout st ar s3 a2 i (error.Fault.Timeout badge)
                else
                  let s4 ← sched.postpone st s3 i3
                  ok (s4, a2)
              else
                let s4 ← sched.postpone st s3 i3
                ok (s4, a2)
          else
            let b5 ← faults.valid_timeout_handler st s3 i
            if b5 then
              if ft != fl4_abi.consts.fault.Timeout then
                let badge ← obj.Sc.badge st i3 s3
                faults.handle_timeout st ar s3 a2 i (error.Fault.Timeout badge)
              else
                let s4 ← sched.postpone st s3 i3
                ok (s4, a2)
            else
              let s4 ← sched.postpone st s3 i3
              ok (s4, a2)
        else ok (s3, a2)) ⦃ s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  step with obj.Tcb.sc.spec as ⟨i3, ei3⟩
  step with obj.Sc.is_null.spec as ⟨b2, eb2⟩
  split
  · exact (WP.spec_ok _).2 h
  rename_i hb2
  have hi0 : L.mem s3 (scA i) ≠ 0#u64 := fun e => hb2 (by rw [eb2, ei3, e]; rfl)
  subst ei3
  refine WP.spec_bind (sched.is_runnable.spec' s3 i) fun b3 hb3 => ?_
  split
  swap
  · exact (WP.spec_ok _).2 h
  rename_i hb3t
  have hrun := hb3 hb3t
  have PP : (do
      let s4 ← sched.postpone st s3 (L.mem s3 (scA i))
      ok (s4, a2)) ⦃ s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ :=
    WP.spec_bind (r.postpone h hrun hi0) fun s4 h4 => (WP.spec_ok _).2 h4
  have TO : ∀ badge : U64, faults.handle_timeout st ar s3 a2 i (error.Fault.Timeout badge) ⦃ s' _ =>
      BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := fun badge => r.timeout hA E h hU (tmoAny Ac s3 i h r.mem) hG
  have VT : (do
      let b6 ← faults.valid_timeout_handler st s3 i
      if b6 then
        if ft != fl4_abi.consts.fault.Timeout then
          let badge ← obj.Sc.badge st (L.mem s3 (scA i)) s3
          faults.handle_timeout st ar s3 a2 i (error.Fault.Timeout badge)
        else
          let s4 ← sched.postpone st s3 (L.mem s3 (scA i))
          ok (s4, a2)
      else
        let s4 ← sched.postpone st s3 (L.mem s3 (scA i))
        ok (s4, a2)) ⦃ s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
    refine WP.spec_bind (P0.faults.valid_timeout_handler.p0 st s3 i hS) fun b6 _ => ?_
    split
    · split
      · exact WP.spec_bind (P0.obj.Sc.badge.p0 st _ s3 hS) fun badge _ => TO badge
      · exact PP
    · exact PP
  refine WP.spec_bind (sporadic.ready.spec s3 _) fun b4 _ => ?_
  split
  · refine WP.spec_bind (sporadic.sufficient.ok hA s3 a2 _ 0#u64) fun b5 _ => ?_
    split
    · exact WP.spec_bind (r.switch h hrun) fun s4 h4 => (WP.spec_ok _).2 h4
    · exact VT
  · exact VT

/-- The replied-to thread `i` once off the reply, before its new state. -/
structure RPre (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (Ac : Set U64) (s : S) (i : U64) :
    Prop where
  mem : i ∈ T
  st0 : L.mem s (stA i) = sched.TS_INACTIVE
  nq : (L.mem s (inqA i) &&& sched.Q_QUEUED) = 0#u64
  nr : (L.mem s (inqA i) &&& sched.Q_RELEASE) = 0#u64
  na : L.actionW s ≠ i
  ni : L.idleW s ≠ i
  ac : L.mem s (scA i) ≠ 0#u64 → L.mem s (scA i) ∈ Ac

/-- `RPre` across a step that keeps `i`'s state, queue and SC fields and the
scheduler action and idle words. -/
theorem RPre.keep {s s' : S} {i : U64} (r : RPre st T Ac s i) (e1 : L.mem s' (stA i) = L.mem s (stA i))
    (e2 : L.mem s' (inqA i) = L.mem s (inqA i)) (e3 : L.mem s' (scA i) = L.mem s (scA i))
    (e4 : L.actionW s' = L.actionW s) (e5 : L.idleW s' = L.idleW s) : RPre st T Ac s' i :=
  ⟨r.mem, e1.trans r.st0, by rw [e2]; exact r.nq, by rw [e2]; exact r.nr, by rw [e4]; exact r.na,
    by rw [e5]; exact r.ni, by rw [e3]; exact r.ac⟩

/-- The new state of `i` (not blocked) gives `RTail`. -/
theorem RPre.set {s : S} {i v : U64} (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (r : RPre st T Ac s i)
    (hv : ¬ Blocked v) (hvr : v ≠ sched.TS_BLOCKED_ON_REPLY ∧ v ≠ sched.TS_BLOCKED_ON_RECV) :
    sched.set_thread_state st s i v ⦃ s' => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ RTail st T Ac s' i ⦄ := by
  have hT := h.1.choose_spec.choose_spec.tcbs
  have o1 : ¬ Blocked (L.mem s (stA i)) := by rw [r.st0]; exact not_blocked_inactive
  have o2 : L.mem s (stA i) ≠ sched.TS_BLOCKED_ON_REPLY := by rw [r.st0]; exact inactive_ne.1
  have o3 : L.mem s (stA i) ≠ sched.TS_BLOCKED_ON_RECV := by rw [r.st0]; exact inactive_ne.2
  refine WP.spec_mono (sts_bxi h r.mem hv hvr ⟨o1, o2, o3⟩ r.nq r.nr r.na) ?_
  rintro s' ⟨h', e', k⟩
  refine ⟨h', r.mem, by rw [e']; exact hv, by rw [e']; exact hvr.1, by rw [e']; exact hvr.2,
    by rw [k.inqf r.mem]; exact r.nq, by rw [k.inqf r.mem]; exact r.nr, ?_, by rw [k.idleW]; exact r.ni,
    by rw [k.scf r.mem]; exact r.ac⟩
  rcases k.act with e | e
  · rw [e]; exact r.na
  · rw [e]; exact fun e' => notT_small hT (by simp) (e' ▸ r.mem)

set_option maxHeartbeats 4000000 in
/-- **`do_reply_transfer`** (seL4 `doReplyTransfer`) keeps the invariants. -/
theorem ipc.do_reply_transfer.bxi {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (tmoAny : ∀ (Ac : Set U64) (s : S) (t : U64), BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → t ∈ T →
      obj.Tcb.slot t layout.tcb.SLOT_TIMEOUT_HANDLER ⦃ sl => obj.Slot.cap st sl s ⦃ c => CapTyped H Rp Nt c ⦄ ⦄)
    (userOK : ∀ (Ac : Set U64) (s : S), BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → UserOK st T Cs Ω H U s)
    (s : S) (a : A) (ct r : U64) (grant : Bool) (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hr : r ∈ Rp)
    (hct : ct ∈ T) (hG : XG st T Cs Ω H Sg Scs Z P3Ok s) :
    ipc.do_reply_transfer st ar s a ct r grant ⦃ s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hT := h.1.choose_spec.choose_spec.tcbs
  unfold ipc.do_reply_transfer
  refine WP.spec_bind (obj.Reply.tcb.blk s r) fun i ei => ?_
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 h
  rename_i hb
  have hi0 : i ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
  obtain ⟨-, hiT, -, -⟩ := h.2.2.1.2.1.back r hr (by rw [← ei]; exact hi0)
  rw [← ei] at hiT
  step with obj.Tcb.state.spec as ⟨v, ev⟩
  split
  · exact (WP.spec_ok _).2 h
  rename_i hv
  have hst : L.mem s (stA i) = sched.TS_BLOCKED_ON_REPLY := by
    rw [← ev]; apply UScalar.eq_of_val_eq; simpa [sched.TS_BLOCKED_ON_REPLY] using hv
  have hni : L.idleW s ≠ i := fun e => h.2.1.idleNB (by rw [e, hst]; exact Or.inr rfl)
  refine WP.spec_bind (ipc.reply_remove.blk (Es := ∅) hA s a r i h.blk hr hiT ei.symm hst) ?_
  rintro ⟨s3, a2⟩ ⟨h3b, st3, F3, sca3, id3⟩
  try simp only [WP.uncurry'_pair]
  have h3 := BlkOK.bxi h3b
  obtain ⟨dq3, dr3, da3⟩ := blocked_out h3.1.choose_spec.choose_spec hiT (by rw [st3]; exact not_runnable_inactive)
  have R3 : RPre st T Ac s3 i := ⟨hiT, st3, dq3, dr3, da3, by rw [id3]; exact hni, sca3⟩
  have hG3 : XG st T Cs Ω H Sg Scs Z P3Ok s3 := hG.footD (F3.mono (Set.empty_subset _))
  -- the SC's refills
  step with obj.Tcb.sc.spec as ⟨i2, ei2⟩
  refine WP.spec_bind (sporadic.sc_sporadic.spec s3 i2) fun b1 hb1 => ?_
  refine WP.spec_bind (Pₘ := fun s4 => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s4 ∧ RPre st T Ac s4 i ∧
      XG st T Cs Ω H Sg Scs Z P3Ok s4) ?_ ?_
  · split
    · rename_i hb1t
      have hi20 := (hb1 hb1t).1
      step with obj.Sc.cpu.spec as ⟨cpu, _⟩
      step with obj.node_get.spec as ⟨cs, _⟩
      split
      · obtain ⟨⟨Q, R, q3⟩, hB3, hX3, hSg3, hS3⟩ := h3
        refine WP.spec_mono (WP.spec_and (sporadic.unblock_check.all s3 i i2 q3 hB3 hX3 hS3 hSg3 hiT ei2 hi20
          (by rw [ei2]; exact sca3 (by rw [← ei2]; exact hi20)))
          (sporadic.unblock_check.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s3 i i2 q3 hB3 hX3 hS3 hSg3 hiT
            ei2 hi20 (by rw [ei2]; exact sca3 (by rw [← ei2]; exact hi20)))) ?_
        rintro s4 ⟨⟨q4, hB4, hX4, hS4, hSg4, ea4, -, ei4, f4, -⟩, F4⟩
        refine ⟨⟨⟨Q, R, q4⟩, hB4, hX4, hSg4, hS4⟩, R3.keep ?_ ?_ ?_ ea4 ei4, hG3.foot F4⟩
        · rw [stA_eq]; exact f4 i hiT _ (by simp) (by simp)
        · rw [inqA_eq]; exact f4 i hiT _ (by simp) (by simp)
        · rw [scA_eq]; exact f4 i hiT _ (by simp) (by simp)
      · exact (WP.spec_ok _).2 ⟨h3, R3, hG3⟩
    · exact (WP.spec_ok _).2 ⟨h3, R3, hG3⟩
  rintro s4 ⟨h4, R4, hG4⟩
  refine WP.spec_bind (P0.obj.Tcb.fault_type.p0 st i s4 hS) fun ft _ => ?_
  refine WP.spec_bind (Pₘ := fun r : S × A => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧ RTail st T Ac r.1 i ∧
      XG st T Cs Ω H Sg Scs Z P3Ok r.1) ?_ ?_
  · split
    · -- the message
      obtain ⟨⟨Q, R, q4⟩, hB4, hX4, hSg4, hS4⟩ := h4
      refine WP.spec_bind (xferOK_of hA E Ac ∅ Q R s4 a2 ct 0#u64 0#u64 grant i hct hiT q4 hB4 hX4 hS4 hSg4
        (userOK Ac s4 ⟨⟨Q, R, q4⟩, hB4, hX4, hSg4, hS4⟩) hG4) ?_
      rintro s5 ⟨q5, hB5, hX5, hS5, hSg5, ⟨ea5, -, ei5, -, f5, -, -⟩, hG5⟩
      have h5 : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s5 := ⟨⟨Q, R, q5⟩, hB5, hX5, hSg5, hS5⟩
      have R5 : RPre st T Ac s5 i := R4.keep (by rw [stA_eq]; exact f5 i hiT _ (by simp) (by simp) (by simp))
        (by rw [inqA_eq]; exact f5 i hiT _ (by simp) (by simp) (by simp))
        (by rw [scA_eq]; exact f5 i hiT _ (by simp) (by simp) (by simp)) ea5 ei5
      refine WP.spec_bind (WP.spec_and (R5.set h5 not_blocked_running running_ne)
        (sched.set_thread_state.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) s5 i _ q5 hiT)) fun s6 ⟨h6, f6⟩ => ?_
      exact (WP.spec_ok _).2 ⟨h6.1, h6.2, hG5.foot (f6.mono (Set.empty_subset _))⟩
    · -- the fault reply
      refine WP.spec_bind (faults.handle_fault_reply.rf (s := s4) (a := a2) (snd := ct) hT hiT) ?_
      rintro ⟨rs, s5, a3⟩ w5
      try simp only [WP.uncurry'_pair]
      obtain ⟨⟨Q, R, q4⟩, hB4, hX4, hSg4, hS4⟩ := h4
      obtain ⟨q5, hB5, hX5, hS5, hSg5, ea5, -, ei5, -, f5, -⟩ :=
        xfer_all (U := ∅) q4 hB4 hX4 hS4 hSg4 (fun b hb => absurd hb (by simp)) w5
      have h5 : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s5 := ⟨⟨Q, R, q5⟩, hB5, hX5, hSg5, hS5⟩
      have R5 : RPre st T Ac s5 i := R4.keep (by rw [stA_eq]; exact f5 i hiT _ (by simp) (by simp) (by simp))
        (by rw [inqA_eq]; exact f5 i hiT _ (by simp) (by simp) (by simp))
        (by rw [scA_eq]; exact f5 i hiT _ (by simp) (by simp) (by simp)) ea5 ei5
      have hG5 : XG st T Cs Ω H Sg Scs Z P3Ok s5 :=
        hG4.of_fr (w5.mono fun _ hb => XferFoot.cur0w (fun b hb => absurd hb (by simp)) hb)
      have hG6 : XG st T Cs Ω H Sg Scs Z P3Ok (L.wr s5 (faultA i) fl4_abi.consts.fault.NullFault) :=
        hG5.foot (foot_field (K := 3376#u64) hT hiT (by simp) (by simp) (by simp) (by simp))
      unfold faults.clear_fault
      refine WP.spec_bind (obj.Tcb.set_fault_type.spec s5 i _) fun s6 e6 => ?_
      subst e6
      have h6 := bxi_field (K := 3376#u64) (v := fl4_abi.consts.fault.NullFault) h5 hiT (by simp) (by simp)
        (by simp) (by simp)
      have hN5 := h5.1.choose_spec.choose_spec.nodes _ h5.1.choose_spec.choose_spec.cur
      have n6 := ani_field (K := 3376#u64) (v := fl4_abi.consts.fault.NullFault) hT hN5 hiT (by simp) (by simp)
      have fw : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3376 →
          L.mem (L.wr s5 (faultA i) fl4_abi.consts.fault.NullFault) (core.num.U64.wrapping_add i K) =
            L.mem s5 (core.num.U64.wrapping_add i K) := fun K a1 a2 a3 =>
        L.mem_wr_ne (field_aligned (K := 3376#u64) (hT i hiT) (by simp) (by simp)) (field_aligned (hT i hiT) a1 a2)
          (fun e => field_ne (K1 := 3376#u64) (hT i hiT) (hT i hiT) (by simp) a1 (fun _ => by simp; omega)
            (UScalar.eq_of_val_eq e))
      have R6 : RPre st T Ac (L.wr s5 (faultA i) fl4_abi.consts.fault.NullFault) i :=
        R5.keep (by rw [stA_eq]; exact fw _ (by simp) (by simp) (by simp))
          (by rw [inqA_eq]; exact fw _ (by simp) (by simp) (by simp))
          (by rw [scA_eq]; exact fw _ (by simp) (by simp) (by simp)) n6.1 n6.2.1
      split
      · refine WP.spec_bind (WP.spec_and (R6.set h6 not_blocked_restart restart_ne)
          (sched.set_thread_state.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) _ i _
            h6.1.choose_spec.choose_spec hiT)) fun s7 ⟨h7, f7⟩ => ?_
        exact (WP.spec_ok _).2 ⟨h7.1, h7.2, hG6.foot (f7.mono (Set.empty_subset _))⟩
      · refine WP.spec_bind (WP.spec_and (R6.set h6 not_blocked_inactive inactive_ne)
          (sched.set_thread_state.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) _ i _
            h6.1.choose_spec.choose_spec hiT)) fun s7 ⟨h7, f7⟩ => ?_
        exact (WP.spec_ok _).2 ⟨h7.1, h7.2, hG6.foot (f7.mono (Set.empty_subset _))⟩
  rintro ⟨s6, a6⟩ ⟨h6, r6, g6⟩
  try simp only [WP.uncurry'_pair]
  exact reply_tail hA E tmoAny h6 r6 (userOK Ac s6 h6) g6

/-- **InvGaps' `reply`, discharged**, from the timeout-handler typing of any
thread (`tmoAny`) and the user words at every `BXI` state. -/
theorem decGap_reply {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (tmoAny : ∀ (Ac : Set U64) (s : S) (t : U64), BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → t ∈ T →
      obj.Tcb.slot t layout.tcb.SLOT_TIMEOUT_HANDLER ⦃ sl => obj.Slot.cap st sl s ⦃ c => CapTyped H Rp Nt c ⦄ ⦄)
    (userOK : ∀ (Ac : Set U64) (s : S), BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → UserOK st T Cs Ω H U s) :
    DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .reply := by
  intro Ac s a lbl len slot cap blk call don fp buf extra hf D _hslot hE
  cases cap <;> simp [capFam] at hf
  rename_i p g
  have hpR : p ∈ Rp := D.cap.1.2.2 p g rfl
  have hct : L.curW s ∈ T := D.bxi.1.choose_spec.choose_spec.curT
  unfold syscall.decode_invocation
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have e : ct = L.curW s := ect
  subst e
  try dsimp only
  refine WP.spec_bind (sched.set_thread_state.restart_blk (Es := ∅) s _ D.bxi.blk hct (runnable_ok D.run).1
    (runnable_ok D.run).2) fun s1 ⟨h1, f1, _, _⟩ => ?_
  refine WP.spec_bind (ipc.do_reply_transfer.bxi hA E tmoAny userOK s1 a _ p g (BlkOK.bxi h1) hpR hct
    (hE.xg.foot (f1.mono (Set.empty_subset _)))) ?_
  rintro ⟨s2, a2⟩ h2
  try simp only [WP.uncurry'_pair]
  exact (WP.spec_ok _).2 (DecPost.of_bxi h2 (by simp))

end

end Fl4Proofs.P1
