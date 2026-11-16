/-
P1: InvGaps' `thread` family, continued: `CopyRegisters` and the other
labels on top of QueueDecTcb's, and the family's decode (`tcb.decode.dec`,
`decGap_thread`).
-/
import Fl4Proofs.P1.QueueDecTcb
import Fl4Proofs.P1.QueueFinThr
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}

/-! ## `CopyRegisters` -/

/-- A second stall from a stalled state. -/
theorem Stalled.stall {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s s1 : S} {a1 : A} {y : U64}
    (h1 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s1) :
    smp.remote_tcb_stall st ar s1 a1 y ⦃ s2 _ => Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s2 ⦄ := by
  refine WP.spec_mono (smp.remote_tcb_stall.bxi hA s1 a1 y h1.bxi) ?_
  rintro ⟨s2, a2⟩ ⟨hb2, ea, ec, -, ecs, fld, -, wn⟩
  refine ⟨hb2, ea.trans h1.act, ec.trans h1.cur, ecs.trans h1.csc,
    fun z hz K hK hK8 => (fld z hz K hK hK8).trans (h1.fld z hz K hK hK8), ?_⟩
  refine (h1.node.trans wn).mono fun b hb => ?_
  rcases hb with hb | ⟨o, e⟩
  · exact hb
  · exact ⟨o, by rw [e, h1.node.2.1, nodeAt_of_ksb h1.node.1]⟩

set_option maxHeartbeats 2000000 in
theorem tcb.copy_registers.blk {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s : S} {a : A}
    {dest src flags : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hd : dest ∈ T) (hs : src ∈ T)
    (hna : L.actionW s ≠ src) :
    tcb.copy_registers st ar s a dest src flags ⦃ r => r.1 = .Ok () ∧ BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hT := h.1.choose_spec.choose_spec.tcbs
  unfold tcb.copy_registers
  simp only [lift, bind_ok]
  refine WP.spec_bind (Pₘ := fun r : S × A => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1) ?_ ?_
  · split
    · exact WP.spec_mono (sched.suspend.blk s a src h hs hna) fun r ⟨hr, _⟩ => by obtain ⟨s1, a1⟩ := r; exact hr
    · exact (WP.spec_ok _).2 h
  rintro ⟨s1, a1⟩ h1
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (Pₘ := fun r : S × A => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1) ?_ ?_
  · split
    · exact WP.spec_mono (sched.restart.tinv hA s1 a1 dest h1 hd) fun r hr => by obtain ⟨s2, a2⟩ := r; exact hr
    · exact (WP.spec_ok _).2 h1
  rintro ⟨s2, a2⟩ h2
  try simp only [uncurry_apply_pair]
  have TL : ∀ s3 : S, WritesIn st s2 s3 (XferFoot T ∅) →
      (do
        let s5 ← tcb.post_modify_registers st s3 dest
        let t ← sched.cur_thread st s5
        let b ← obj.Tcb.Insts.CoreCmpPartialEqTcb.eq dest t
        if b then do
          let s6 ← sched.reschedule_required st s5
          ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s6, a2)
        else ok (core.result.Result.Ok (), s5, a2)) ⦃ r => r.1 = .Ok () ∧
          BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1 ⦄ := fun s3 w3 => by
    refine WP.spec_bind (tcb.post_modify_registers.rf (s := s3) hT hd) fun s5 w5 => ?_
    have h5 := (blk_rf h2 (rf_trans w3 w5)).1
    refine WP.spec_bind (sched.cur_thread.spec s5) fun t1 _ => ?_
    simp only [obj.Tcb.Insts.CoreCmpPartialEqTcb.eq, bind_ok]
    split
    · exact WP.spec_bind (sched.reschedule_required.blk s5 h5) fun s6 h6 => (WP.spec_ok _).2 ⟨rfl, h6.1⟩
    · exact (WP.spec_ok _).2 ⟨rfl, h5⟩
  split
  · refine WP.spec_bind (tcb.copy_registers_loop0.rf (s0 := s2) hT hd (WritesIn.refl _ _)) fun s3 w3 => ?_
    refine WP.spec_bind (P0.obj.Tcb.reg.p0 st dest s3 _ hS) fun pc _ => ?_
    refine WP.spec_bind (obj.Tcb.set_reg.rf (v := pc) (s := s3) hT hd (by simp [layout.reg.NEXT_IP]))
      fun s4 w4 => ?_
    split
    · refine WP.spec_bind (tcb.copy_registers_loop1.rf (s0 := s2) hT hd (rf_trans w3 w4)) fun s5 w5 => ?_
      exact TL s5 w5
    · exact TL s4 (rf_trans w3 w4)
  · split
    · refine WP.spec_bind (tcb.copy_registers_loop2.rf (s0 := s2) hT hd (WritesIn.refl _ _)) fun s3 w3 => ?_
      exact TL s3 w3
    · exact TL s2 (WritesIn.refl _ _)

set_option maxHeartbeats 2000000 in
/-- **`CopyRegisters`** after the stall. -/
theorem tcb.decode_copy_registers.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {s s1 : S} {a1 : A} {t len buf : U64} {call : Bool} {slot : obj.Slot}
    {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Thread t) extra) (h1 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s1) :
    tcb.decode_copy_registers st ar s1 a1 t { length := len, buf, call, slot, extra } ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have ht : t ∈ T := D.cap.2.1 t rfl
  have c1 := h1.cur0 D
  unfold tcb.decode_copy_registers
  refine WP.spec_bind (tcb.extra_with_length.mem _ 1#u64) ?_
  rintro r ⟨-, hx⟩
  rcases r with x | e
  swap
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 (Cur0.post c1)
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨hxm, hx0⟩ := hx x rfl
  refine WP.spec_bind (P0.tcb.arg.p0 st s1 _ _ hS) fun flags _ => ?_
  refine WP.spec_bind (tcb.thread_arg.tcb (pos := 1#u64) D h1.node hxm hx0) ?_
  rintro r ⟨-, hT2⟩
  rcases r with src | e
  swap
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 (Cur0.post c1)
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  have hsrc := hT2 src rfl
  refine WP.spec_bind (h1.stall hA (y := src)) ?_
  rintro ⟨s1', a1'⟩ h1'
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (h1'.restart D) fun s2 ⟨h2, hna, _, _⟩ => ?_
  refine WP.spec_mono (tcb.copy_registers.blk hA h2 ht hsrc (hna src hsrc)) ?_
  rintro ⟨r, s3, a3⟩ ⟨e, h3⟩
  simp only at e h3 ⊢
  subst e
  exact DecPost.ok_bxi (BlkOK.bxi h3)

/-! ## `ConfigureSingleStepping` -/

set_option maxHeartbeats 2000000 in
theorem tcb.decode_configure_single_stepping.dec {A : Type _} {ar : machine.Arch A}
    {s s1 : S} {a1 : A} {t len buf : U64} {call : Bool} {slot : obj.Slot}
    {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Thread t) extra) (h1 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s1) :
    tcb.decode_configure_single_stepping st ar s1 a1 t { length := len, buf, call, slot, extra } ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have ht : t ∈ T := D.cap.2.1 t rfl
  have hT := D.bxi.1.choose_spec.choose_spec.tcbs
  have hct : L.curW s ∈ T := D.bxi.1.choose_spec.choose_spec.curT
  have est : L.mem s1 (stA (L.curW s1)) = L.mem s (stA (L.curW s)) := by
    rw [h1.cur, stA_eq]; exact h1.fld _ hct _ (by simp) (by simp)
  have hr := runnable_ok D.run
  unfold tcb.decode_configure_single_stepping
  refine WP.spec_bind (sched.cur_thread.spec s1) fun ct ect => ?_
  have ect' : ct = L.curW s := ect.trans h1.cur
  subst ect'
  refine WP.spec_bind (P0.tcb.arg.p0 st s1 _ _ hS) fun bp _ => ?_
  refine WP.spec_bind (P0.tcb.arg.p0 st s1 _ _ hS) fun n _ => ?_
  refine WP.spec_bind (tcb.restart_caller.blk (Es := ∅) s1 h1.bxi.blk (est ▸ hr.1) (est ▸ hr.2)) ?_
  rintro s2 ⟨h2, -, est2, k⟩
  rw [h1.cur] at est2 k
  refine WP.spec_bind (debug.configure_single_stepping.rf (s := s2) (a := a1) (bp := bp) (n := n) (rep := false)
    hT ht) ?_
  rintro ⟨cons, s3, a3⟩ w3
  try simp only [uncurry_apply_pair]
  have TL : ∀ (s4 : S), WritesIn st s2 s4 (XferFoot T ∅) →
      (do
        let s5 ← sched.set_thread_state st s4 (L.curW s) sched.TS_RUNNING
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s5, a3)) ⦃ r s' _ =>
          DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := fun s4 w4 => by
    obtain ⟨b4, -, -, f4⟩ := blk_rf h2 w4
    have e4 : L.mem s4 (stA (L.curW s)) = sched.TS_RESTART := by
      rw [stA_eq, f4 _ hct _ (by simp) (by simp) (by simp), ← stA_eq, est2]
    refine WP.spec_bind (sched.set_thread_state.running_bxi (BlkOK.bxi b4) hct e4) fun s5 h5 => ?_
    exact (WP.spec_ok _).2 (DecPost.ok_bxi h5)
  have RW : ∀ (v : U64) (b : U64), (do
        let (len, s4) ← msg.set_mr st s3 (L.curW s) b 0#u64 v
        let s5 ← tcb.reply_words st s4 (L.curW s) len
        let s6 ← sched.set_thread_state st s5 (L.curW s) sched.TS_RUNNING
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s6, a3)) ⦃ r s' _ =>
          DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := fun v b => by
    refine WP.spec_bind (msg.set_mr.rf0 hT hct) ?_
    rintro ⟨n4, s4⟩ w4
    try simp only [uncurry_apply_pair]
    refine WP.spec_bind (tcb.reply_words.rf hT hct) fun s5 w5 => ?_
    exact TL s5 (rf_trans w3 (rf_trans w4 w5))
  split
  · refine WP.spec_bind (P0.msg.lookup_ipc_buffer.p0 st s3 true _ hS) fun b _ => ?_
    split
    · split
      · exact RW _ _
      · exact RW _ _
    · exact RW _ _
  · exact TL s3 w3

/-! ## `thread_control_caps` within `Cur0` -/

theorem Cur0.resched {s0 s : S} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) :
    sched.reschedule_required st s ⦃ s' => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  obtain ⟨Ac', hb⟩ := h.bxi
  have hct : L.curW s ∈ T := hb.1.choose_spec.choose_spec.curT
  obtain ⟨⟨Q, R, q⟩, -, -, hSg, -⟩ := id hb
  refine WP.spec_mono (WP.spec_and (sched.reschedule_required.blk s hb.blk)
    (sched.reschedule_required.curR s Q R q hSg hct)) fun s' ⟨⟨h', _⟩, ec, ecs, esc, ea, enb⟩ => ?_
  exact Cur0.mk h (BlkOK.bxi h') ec ecs esc ea (Or.inr (enb h.nb))

theorem tcb_slot_val (p i : U64) : obj.Tcb.slot p i = ok (slotIdx p i) := by
  unfold obj.Tcb.slot slotIdx
  simp [lift, cte_size]

/-- **`install_tcb_cap`** of a TCB cap slot, the source a cap slot or null. -/
theorem tcb.install_tcb_cap.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (G : DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z) (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z)
    {s0 s : S} {a : A} {target slot index src : U64} {c : capability.Cap}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (ht : target ∈ T) (hi : index.val < 6)
    (hsrc : src ≠ 0#u64 → CapW T Ω Sg src) :
    tcb.install_tcb_cap st ar s a target slot index c src ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  obtain ⟨Ac', hb⟩ := h.bxi
  have hT := hb.1.choose_spec.choose_spec.tcbs
  have hW := tcb_slotIdxW (Ω := Ω) (Sg := Sg) hT ht hi
  unfold tcb.install_tcb_cap
  rw [tcb_slot_val]
  simp only [bind_ok]
  refine WP.spec_bind (cdt.delete.cur0 hA G h hW) ?_
  rintro ⟨r, s1, a1⟩ h1
  try simp only [uncurry_apply_pair]
  rcases r with _ | e
  swap
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 h1
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  refine WP.spec_bind (P0.capability.Cap.is_null.p0 c) fun bn _ => ?_
  split
  · exact (WP.spec_ok _).2 h1
  refine WP.spec_bind (tcb.still_valid.nz s1 target slot c src) fun b hbv => ?_
  split
  · rename_i hb'
    obtain ⟨Ac1, hb1⟩ := h1.bxi
    have hW0 : CapW T Ω Sg (slotIdx target index) := by
      have := hW.2 0#u64 (by simp) (by simp)
      have h0 : core.num.U64.wrapping_add (slotIdx target index) 0#u64 = slotIdx target index := by
        apply UScalar.eq_of_val_eq; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
      rwa [h0] at this
    refine WP.spec_bind (Pₘ := fun s2 => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s2) ?_
      fun s2 h2 => (WP.spec_ok _).2 h2
    unfold cdt.insert
    refine WP.spec_bind (P0.obj.Slot.cap.p0 st src s1 hS) fun sc _ => ?_
    exact WP.spec_mono (C.ins Ac1 s1 c sc src _ hb1 (hsrc (hbv hb')) hW0) fun s2 w2 => h1.capw w2 fun _ hb => hb
  · exact (WP.spec_ok _).2 h1

/-- **`install_buffer`**, the buffer's source slot a cap slot or null. -/
theorem tcb.install_buffer.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (G : DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z) (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z)
    {s0 s : S} {a : A} {target slot baddr : U64} {buffer : capability.Cap × obj.Slot}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (ht : target ∈ T)
    (hsrc : buffer.2 ≠ 0#u64 → CapW T Ω Sg buffer.2) :
    tcb.install_buffer st ar s a target slot baddr buffer ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  obtain ⟨Ac', hb⟩ := h.bxi
  have hT := hb.1.choose_spec.choose_spec.tcbs
  unfold tcb.install_buffer
  rw [tcb_slot_val]
  simp only [bind_ok]
  have hW := tcb_slotIdxW (Ω := Ω) (Sg := Sg) (i := layout.tcb.SLOT_BUFFER) hT ht (by simp [layout.tcb.SLOT_BUFFER])
  refine WP.spec_bind (cdt.delete.cur0 hA G h hW) ?_
  rintro ⟨r, s1, a1⟩ h1
  try simp only [uncurry_apply_pair]
  rcases r with _ | e
  swap
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 h1
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨Ac1, hb1⟩ := h1.bxi
  have hT1 := hb1.1.choose_spec.choose_spec.tcbs
  refine WP.spec_bind (obj.Tcb.set_ipc_buffer.wr s1 target baddr) fun s2 e2 => ?_
  subst e2
  have h2 : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 (L.wr s1 (core.num.U64.wrapping_add target 3512#u64) baddr) := by
    have hct : L.curW s1 ∈ T := hb1.1.choose_spec.choose_spec.curT
    obtain ⟨an, fr⟩ := fld_wr (K := 3512#u64) (v := baddr) hb1 ht (by simp) (by simp)
    exact Cur0.mk h1 (bxi_field hb1 ht (by simp) (by simp) (by simp) (by simp)) an.2.2
      (cscW_wr_field hT1 (hb1.1.choose_spec.choose_spec.nodes _ hb1.1.choose_spec.choose_spec.cur) ht
        (by simp) (by simp))
      (Or.inl (by rw [scA_eq]; exact fr _ hct _ (by simp) (by simp) (fun _ => by simp)))
      (Or.inl an.1) (Or.inl (by rw [stA_eq]; exact fr _ hct _ (by simp) (by simp) (fun _ => by simp)))
  obtain ⟨vc, vs⟩ := buffer
  simp only at hsrc
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (tcb.still_valid.nz _ target slot vc vs) fun b hbv => ?_
  refine WP.spec_bind (Pₘ := fun s3 => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s3) ?_ fun s3 h3 => ?_
  · split
    · rename_i hb'
      obtain ⟨Ac2, hb2⟩ := h2.bxi
      have hW0 : CapW T Ω Sg (slotIdx target layout.tcb.SLOT_BUFFER) := by
        have := hW.2 0#u64 (by simp) (by simp)
        have h0 : core.num.U64.wrapping_add (slotIdx target layout.tcb.SLOT_BUFFER) 0#u64 =
            slotIdx target layout.tcb.SLOT_BUFFER := by
          apply UScalar.eq_of_val_eq; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
        rwa [h0] at this
      unfold cdt.insert
      refine WP.spec_bind (P0.obj.Slot.cap.p0 st vs _ hS) fun sc _ => ?_
      exact WP.spec_mono (C.ins Ac2 _ vc sc vs _ hb2 (hsrc (hbv hb')) hW0) fun s' w => h2.capw w fun _ hb => hb
    · exact (WP.spec_ok _).2 h2
  refine WP.spec_bind (sched.cur_thread.spec s3) fun ct _ => ?_
  simp only [obj.Tcb.Insts.CoreCmpPartialEqTcb.eq, bind_ok]
  split
  · exact WP.spec_bind (Cur0.resched h3) fun s4 h4 => (WP.spec_ok _).2 h4
  · exact (WP.spec_ok _).2 h3

/-- The install step's continuation shape. -/
theorem inst_bind {A : Type _} {s0 : S} {m : Result ((core.result.Result Unit error.Exc) × S × A)}
    {k : S → A → Result ((core.result.Result Unit error.Exc) × S × A)}
    (hm : m ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ⦄)
    (hk : ∀ s' a', Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' → k s' a' ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ⦄) :
    (do
      let (r, s1, a1) ← m
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue _ => k s1 a1
      | core.ops.control_flow.ControlFlow.Break residual => do
        let r1 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual Unit
          (core.convert.FromSame error.Exc) residual
        ok (r1, s1, a1)) ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ⦄ := by
  refine WP.spec_bind hm ?_
  rintro ⟨r, s1, a1⟩ h1
  try simp only [uncurry_apply_pair]
  rcases r with _ | e
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]; exact hk s1 a1 h1
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 h1

set_option maxHeartbeats 4000000 in
/-- **`SetTimeoutEndpoint`** after the stall. -/
theorem tcb.decode_set_timeout_endpoint.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (G : DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z) (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z)
    {s s1 : S} {a1 : A} {t len buf : U64} {call : Bool} {slot : obj.Slot}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (hxw : ∀ sl ∈ extra.val, sl ≠ 0#u64 → CapW T Ω Sg sl)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Thread t) extra) (h1 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s1) :
    tcb.decode_set_timeout_endpoint st ar s1 a1 t { length := len, buf, call, slot, extra } ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have ht : t ∈ T := D.cap.2.1 t rfl
  have c1 := h1.cur0 D
  unfold tcb.decode_set_timeout_endpoint
  refine WP.spec_bind (tcb.extra_with_length.mem _ 0#u64) ?_
  rintro r ⟨-, hx⟩
  rcases r with x | e
  swap
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 (Cur0.post c1)
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨hxm, hx0⟩ := hx x rfl
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st x s1 hS) fun th _ => ?_
  refine WP.spec_bind (P0.faults.valid_fault_handler.p0 th) fun b _ => ?_
  split
  swap
  · simp only [error.invalid_cap, bind_ok]; exact (WP.spec_ok _).2 (Cur0.post c1)
  refine WP.spec_bind (h1.restart0 D) fun s2 c2 => ?_
  refine WP.spec_mono (P₀ := fun r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s r.2.1) ?_ fun r hr => by
    obtain ⟨r1, r2, r3⟩ := r; exact Cur0.post hr
  unfold tcb.thread_control_caps
  simp only [lift, bind_ok, tcb.UPDATE_FAULT, tcb.UPDATE_TIMEOUT, tcb.UPDATE_SPACE, tcb.UPDATE_IPC_BUFFER]
  simp
  exact inst_bind (tcb.install_tcb_cap.cur0 hA G C c2 ht (by simp [layout.tcb.SLOT_TIMEOUT_HANDLER])
    (fun _ => hxw x hxm hx0)) fun s' a' h' => (WP.spec_ok _).2 h'

theorem tcb.extra_with_length.memi (c : tcb.Ctx) (i : Usize) (n : U64) (hi : i.val < 3) :
    tcb.extra_with_length c i n ⦃ r => ∀ x, r = .Ok x → x ∈ c.extra.val ∧ x ≠ 0#u64 ⦄ := by
  unfold tcb.extra_with_length tcb.extra
  have hl : i.val < c.extra.val.length := by rw [c.extra.property]; simpa using hi
  simp only [show ¬ (i ≥ 3#usize) by simp; omega, ↓reduceIte]
  refine WP.spec_bind (Pₘ := fun o => ∀ x, o = some x → x ∈ c.extra.val ∧ x ≠ 0#u64) ?_ fun o ho => ?_
  · refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec c.extra i hl) fun sl hsl => ?_
    simp only [obj.Slot.is_null, bind_ok]
    split
    · exact (WP.spec_ok _).2 fun x e => by cases e
    · rename_i h0
      exact (WP.spec_ok _).2 fun x e => by
        cases e; exact ⟨hsl ▸ List.getElem_mem hl, by simpa using h0⟩
  rcases o with _ | x
  · simp [error.truncated]
  · simp only
    split
    · exact (WP.spec_ok _).2 fun y e => by cases e; exact ho x rfl
    · simp [error.truncated]

set_option hygiene false in
/-- An error leaf at the stalled `Cur0` state `c1`. -/
local macro "errc" : tactic => `(tactic| first
  | exact (WP.spec_ok _).2 (Cur0.post c1)
  | (simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok, error.invalid_cap, error.illegal, error.truncated]
     exact (WP.spec_ok _).2 (Cur0.post c1)))

set_option hygiene false in
/-- An extra-slot read with its error leaf. -/
local macro "xslot" i:term : tactic => `(tactic| (
  refine WP.spec_bind (tcb.extra_with_length.memi _ $i _ (by simp)) ?_
  rintro r hx
  rcases r with x | e
  swap
  · errc
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨hxm, hx0⟩ := hx x rfl))

set_option maxHeartbeats 8000000 in
/-- **`SetSpace`** after the stall. -/
theorem tcb.decode_set_space.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (G : DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z) (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z)
    {s s1 : S} {a1 : A} {t len buf : U64} {call : Bool} {slot : obj.Slot}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (hxw : ∀ sl ∈ extra.val, sl ≠ 0#u64 → CapW T Ω Sg sl)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Thread t) extra) (h1 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s1) :
    tcb.decode_set_space st ar s1 a1 t { length := len, buf, call, slot, extra } ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have ht : t ∈ T := D.cap.2.1 t rfl
  have c1 := h1.cur0 D
  unfold tcb.decode_set_space
  refine WP.spec_bind (tcb.extra_with_length.memi _ 0#usize _ (by simp)) ?_
  rintro r hx
  rcases r with x0 | e
  swap
  · errc
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨hxm0, hx00⟩ := hx x0 rfl
  refine WP.spec_bind (tcb.extra_with_length.memi _ 1#usize _ (by simp)) ?_
  rintro r hx
  rcases r with x1 | e
  swap
  · errc
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨hxm1, hx01⟩ := hx x1 rfl
  refine WP.spec_bind (tcb.extra_with_length.memi _ 2#usize _ (by simp)) ?_
  rintro r hx
  rcases r with x2 | e
  swap
  · errc
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨hxm2, hx02⟩ := hx x2 rfl
  refine WP.spec_bind (P0.tcb.arg.p0 st s1 _ _ hS) fun cdata _ => ?_
  refine WP.spec_bind (P0.tcb.arg.p0 st s1 _ _ hS) fun vdata _ => ?_
  refine WP.spec_bind (P0.tcb.derive_roots.p0 st s1 t cdata vdata x1 x2 hS) fun r _ => ?_
  rcases r with ⟨cc, vc⟩ | e
  swap
  · errc
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st x0 s1 hS) fun fh _ => ?_
  refine WP.spec_bind (P0.faults.valid_fault_handler.p0 fh) fun b _ => ?_
  split
  swap
  · simp only [error.invalid_cap, bind_ok]; exact (WP.spec_ok _).2 (Cur0.post c1)
  refine WP.spec_bind (h1.restart0 D) fun s2 c2 => ?_
  refine WP.spec_mono (P₀ := fun r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s r.2.1) ?_ fun r hr => by
    obtain ⟨r1, r2, r3⟩ := r; exact Cur0.post hr
  simp only [lift, bind_ok]
  unfold tcb.thread_control_caps
  simp only [lift, bind_ok, tcb.UPDATE_FAULT, tcb.UPDATE_TIMEOUT, tcb.UPDATE_SPACE, tcb.UPDATE_IPC_BUFFER]
  simp
  refine inst_bind (tcb.install_tcb_cap.cur0 hA G C c2 ht (by simp [layout.tcb.SLOT_FAULT_HANDLER])
    (fun _ => hxw x0 hxm0 hx00)) fun s3 a3 c3 => ?_
  refine inst_bind (tcb.install_tcb_cap.cur0 hA G C c3 ht (by simp [layout.tcb.SLOT_CTABLE])
    (fun _ => hxw x1 hxm1 hx01)) fun s4 a4 c4 => ?_
  exact inst_bind (tcb.install_tcb_cap.cur0 hA G C c4 ht (by simp [layout.tcb.SLOT_VTABLE])
    (fun _ => hxw x2 hxm2 hx02)) fun s5 a5 c5 => (WP.spec_ok _).2 c5

set_option maxHeartbeats 8000000 in
/-- **`Configure`** after the stall. -/
theorem tcb.decode_configure.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (G : DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z) (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z)
    {s s1 : S} {a1 : A} {t len buf : U64} {call : Bool} {slot : obj.Slot}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (hxw : ∀ sl ∈ extra.val, sl ≠ 0#u64 → CapW T Ω Sg sl)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Thread t) extra) (h1 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s1) :
    tcb.decode_configure st ar s1 a1 t { length := len, buf, call, slot, extra } ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have ht : t ∈ T := D.cap.2.1 t rfl
  have c1 := h1.cur0 D
  unfold tcb.decode_configure
  refine WP.spec_bind (tcb.extra_with_length.memi _ 0#usize _ (by simp)) ?_
  rintro r hx
  rcases r with x0 | e
  swap
  · errc
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨hxm0, hx00⟩ := hx x0 rfl
  refine WP.spec_bind (tcb.extra_with_length.memi _ 1#usize _ (by simp)) ?_
  rintro r hx
  rcases r with x1 | e
  swap
  · errc
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨hxm1, hx01⟩ := hx x1 rfl
  refine WP.spec_bind (tcb.extra_with_length.memi _ 2#usize _ (by simp)) ?_
  rintro r hx
  rcases r with x2 | e
  swap
  · errc
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨hxm2, hx02⟩ := hx x2 rfl
  refine WP.spec_bind (P0.tcb.arg.p0 st s1 _ _ hS) fun cdata _ => ?_
  refine WP.spec_bind (P0.tcb.arg.p0 st s1 _ _ hS) fun vdata _ => ?_
  refine WP.spec_bind (P0.tcb.arg.p0 st s1 _ _ hS) fun baddr _ => ?_
  refine WP.spec_bind (tcb.derive_for_buffer.slot s1 baddr x2) ?_
  rintro r hbf
  rcases r with bf | e
  swap
  · errc
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  have hbf' := hbf bf rfl
  refine WP.spec_bind (P0.tcb.derive_roots.p0 st s1 t cdata vdata x0 x1 hS) fun r _ => ?_
  rcases r with ⟨cc, vc⟩ | e
  swap
  · errc
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (h1.restart0 D) fun s2 c2 => ?_
  refine WP.spec_mono (P₀ := fun r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s r.2.1) ?_ fun r hr => by
    obtain ⟨r1, r2, r3⟩ := r; exact Cur0.post hr
  simp only [lift, bind_ok]
  unfold tcb.thread_control_caps
  simp only [lift, bind_ok, tcb.UPDATE_FAULT, tcb.UPDATE_TIMEOUT, tcb.UPDATE_SPACE, tcb.UPDATE_IPC_BUFFER]
  simp
  refine inst_bind (tcb.install_tcb_cap.cur0 hA G C c2 ht (by simp [layout.tcb.SLOT_CTABLE])
    (fun _ => hxw x0 hxm0 hx00)) fun s4 a4 c4 => ?_
  refine inst_bind (tcb.install_tcb_cap.cur0 hA G C c4 ht (by simp [layout.tcb.SLOT_VTABLE])
    (fun _ => hxw x1 hxm1 hx01)) fun s5 a5 c5 => ?_
  exact inst_bind (tcb.install_buffer.cur0 hA G C c5 ht (fun h0 => by
    rcases hbf' with e | e
    · rw [e]; exact hxw x2 hxm2 hx02
    · exact absurd e h0)) fun s6 a6 c6 => (WP.spec_ok _).2 c6

set_option maxHeartbeats 4000000 in
/-- **`tcb.decode`** keeps the invariants, from `TcbGaps` (the labels P1
does not prove), `TcbPlace`, `DelGaps` and `CdtHyps`. -/
theorem tcb.decode.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (G : TcbGaps st ar T Cs Ω H Sg Rp Scs Nt Z U) (P : TcbPlace st T Cs Ω H Sg Rp Scs Nt Z U)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U)
    (Gd : DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z) (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z)
    {s : S} {a : A} {lbl t len buf : U64} {call : Bool} {slot : obj.Slot}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Thread t) extra) :
    tcb.decode st ar s a lbl t { length := len, buf, call, slot, extra } ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  by_cases g0 : lbl = fl4_abi.label.TCBReadRegisters
  · subst g0; exact G.readRegisters Ac s a t len buf call slot extra D
  by_cases g4 : lbl = fl4_abi.label.TCBSetSchedParams
  · subst g4; exact G.setSchedParams Ac s a t len buf call slot extra D
  by_cases g18 : lbl = fl4_abi.label.TCBSetEPTRoot
  · subst g18; exact G.setEPTRoot Ac s a t len buf call slot extra D
  have ht : t ∈ T := D.cap.2.1 t rfl
  unfold tcb.decode
  refine WP.spec_bind (smp.remote_tcb_stall.bxi hA s a t D.bxi) ?_
  rintro ⟨s1, a1⟩ ⟨hb1, ea, ec, -, ecs, fld, -, wn⟩
  have h1 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s1 := ⟨hb1, ea, ec, ecs, fld, wn⟩
  try simp only [uncurry_apply_pair, WP.uncurry'_pair]
  refine spec_ite (fun hc => absurd hc g18) fun _ => ?_
  refine spec_ite (fun hc => absurd hc g0) fun _ => ?_
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.decode_write_registers.dec hA D h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.decode_copy_registers.dec hA D h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · -- Suspend
    refine WP.spec_bind (h1.restart D) fun s2 ⟨h2, hna, _, _⟩ => ?_
    refine WP.spec_bind (sched.suspend.blk s2 a1 t h2 ht (hna t ht)) ?_
    rintro ⟨s3, a2⟩ ⟨h3, _⟩
    exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi h3))
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · -- Resume
    refine WP.spec_bind (h1.restart D) fun s2 ⟨h2, _, _, _⟩ => ?_
    refine WP.spec_bind (sched.restart.tinv hA s2 a1 t h2 ht) ?_
    rintro ⟨s3, a2⟩ h3
    exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi h3))
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.decode_configure.dec hA Gd C (P.extraW Ac s _ _ D) D h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.decode_set_priority.dec _ P D h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.decode_set_priority.dec _ P D h1
  refine spec_ite (fun hc => absurd hc g4) fun _ => ?_
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.decode_set_ipc_buffer.dec hA Gd C (P.extraW Ac s _ _ D) D h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.decode_set_space.dec hA Gd C (P.extraW Ac s _ _ D) D h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.decode_set_timeout_endpoint.dec hA Gd C (P.extraW Ac s _ _ D) D h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.decode_bind_notification.dec D h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · -- UnbindNotification
    refine WP.spec_bind (obj.Tcb.bound_ntfn.val s1 t) fun i _ => ?_
    split
    · simp only [error.illegal, bind_ok]
      exact (WP.spec_ok _).2 (DecPost.of_bxi h1.bxi (by simp))
    refine WP.spec_bind (h1.restart D) fun s2 ⟨h2, _, _, _⟩ => ?_
    refine WP.spec_bind (notification.unbind_notification.blk s2 t h2 ht) fun s3 h3 => ?_
    exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi h3))
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.decode_configure_single_stepping.dec D h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.set_breakpoint_checked.dec D h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.decode_get_breakpoint.dec E D h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · -- UnsetBreakpoint
    have hS : P0.StoreTotal st := L.total
    have c1 := h1.cur0 D
    have hT := D.bxi.1.choose_spec.choose_spec.tcbs
    refine WP.spec_bind (P0.tcb.arg.p0 st s1 _ _ hS) fun bp _ => ?_
    refine WP.spec_bind (debug.check_bp_num.lt bp) ?_
    rintro r ⟨-, hbp⟩
    rcases r with _ | e
    swap
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_tc_ok]
      exact (WP.spec_ok _).2 (Cur0.post c1)
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    refine WP.spec_bind (h1.restart D) fun s2 ⟨h2, _, _, _⟩ => ?_
    refine WP.spec_bind (debug.unset_breakpoint.rf (s := s2) hT ht (hbp rfl)) fun s3 w3 => ?_
    exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi (blk_rf h2 w3).1))
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.decode_set_tls_base.dec D h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.decode_set_flags.dec hA D h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.set_timer.dec D h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.fpu_transfer.dec hA P D h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.fpu_transfer.dec hA P D h1
  exact (WP.spec_ok _).2 (DecPost.of_bxi h1.bxi (by simp))

/-- **InvGaps' `thread`, from the per-label gaps** `TcbGaps`, `TcbPlace`, `DelGaps`
and `CdtHyps`. -/
theorem decGap_thread {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (G : TcbGaps st ar T Cs Ω H Sg Rp Scs Nt Z U) (P : TcbPlace st T Cs Ω H Sg Rp Scs Nt Z U)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U)
    (Gd : DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z) (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z) :
    DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U .thread := by
  intro Ac s a lbl len slot cap blk call don fp buf extra hf D
  cases cap <;> simp [capFam] at hf
  unfold syscall.decode_invocation
  step with sched.cur_thread.spec as ⟨ct, _⟩
  try dsimp only
  split
  · exact (WP.spec_ok _).2 (DecPost.keep D.bxi (by simp))
  · exact tcb.decode.dec hA G P E Gd C D

end

end Fl4Proofs.P1
