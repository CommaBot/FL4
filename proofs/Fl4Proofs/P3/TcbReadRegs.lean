/-
P3 (DESIGN.md §9), TCB invocations: **FL4's ReadRegisters is a `WFr` step**
(`read_registers_frame`, discharging TcbDataX's `ReadRegsFrameHyp` from the
source's suspend as a `WFr` step, `SuspendWFrHyp`): the register-copy loops
write the caller's message registers (`set_reg`) and IPC-buffer words
(`buf_set`, `BufOutsideHyp`), then the message info and `Running`.
-/
import Fl4Proofs.P3.TcbDataX
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **A loop whose body keeps `WFr`** from `s0`, its index at most 20 and
increasing. -/
theorem loop_wfr {th : TypedHeap} (s0 : S) (body : S × U64 → Result (ControlFlow (S × U64) (S × U64)))
    (x0 : S × U64) (h0 : WFr (L := L) th s0 x0.1 ∧ x0.2.val ≤ 20)
    (hb : ∀ x : S × U64, WFr (L := L) th s0 x.1 → x.2.val ≤ 20 → body x ⦃ r =>
      match r with
      | .done y => WFr (L := L) th s0 y.1 ∧ y.2.val ≤ 20
      | .cont x' => (WFr (L := L) th s0 x'.1 ∧ x'.2.val ≤ 20) ∧ x.2.val < x'.2.val ⦄) :
    loop body x0 ⦃ y => WFr (L := L) th s0 y.1 ∧ y.2.val ≤ 20 ⦄ := by
  apply loop.spec_decr_nat (measure := fun x => 21 - x.2.val) (inv := fun x => WFr (L := L) th s0 x.1 ∧ x.2.val ≤ 20)
  · rintro x ⟨h1, h2⟩
    refine WP.spec_mono (hb x h1 h2) ?_
    rintro (x' | y) h
    · exact ⟨h.1, by have := h.1.2; have := h.2; omega⟩
    · exact h
  · exact h0


theorem cast_to_us (i : U64) (h : i.val < 2 ^ 32) : (UScalar.cast .Usize i).val = i.val := by
  rw [UScalar.cast_val_eq]
  refine Nat.mod_eq_of_lt ?_
  rw [UScalarTy.Usize_numBits_eq]
  rcases System.Platform.numBits_eq with e | e <;> rw [e] <;> omega

theorem nframe_val : tcb.N_FRAME.val = 18 := by unfold tcb.N_FRAME; rfl
theorem ngp_val : tcb.N_GP.val = 2 := by unfold tcb.N_GP; rfl
theorem nmsg_val : msg.N_MSG_REGISTERS.val = 4 := by unfold msg.N_MSG_REGISTERS; rfl

/-- The body writing frame register `i` into the caller's message register. -/
theorem body0_wfr {th : TypedHeap} (hP : Placed th) {s0 : S} {ct : U64} (hC : TCtx (L := L) th s0 ct)
    (src n : U64) (hn : n.val ≤ 20) (x : S × U64) (hw : WFr (L := L) th s0 x.1) (hx : x.2.val ≤ 20) :
    tcb.read_registers_loop0.body st src n ct x.1 x.2 ⦃ r =>
      match r with
      | .done y => WFr (L := L) th s0 y.1 ∧ y.2.val ≤ 20
      | .cont x' => (WFr (L := L) th s0 x'.1 ∧ x'.2.val ≤ 20) ∧ x.2.val < x'.2.val ⦄ := by
  obtain ⟨s, i⟩ := x
  simp only at hw hx ⊢
  have hC1 := hC.wfr hw
  unfold tcb.read_registers_loop0.body
  split
  · rename_i h1
    have hin : i.val < n.val := (P1.gt_iff_val).1 h1
    split
    · rename_i h2
      have hi18 : i.val < 18 := by have := (P1.gt_iff_val).1 h2; rw [nframe_val] at this; exact this
      split
      · rename_i h3
        have hi4 : i.val < 4 := by have := (P1.gt_iff_val).1 h3; rw [nmsg_val] at this; exact this
        simp only [lift, bind_ok]
        refine WP.spec_bind (Array.index_usize_spec _ _ (by rw [cast_to_us i (by omega)]; simp; omega)) ?_
        rintro i2 -
        refine WP.spec_bind (Endp.obj.Tcb.reg.spec s src i2) ?_
        rintro v -
        refine WP.spec_bind (Endp.msg_register_spec i hi4) ?_
        rintro r rfl
        refine WP.spec_bind (set_reg_wfr hP hC1.ksb hC1.tcb (Endp.regIdx_lt _) v) ?_
        intro s1 hw1
        obtain ⟨i4, hadd, hi4v⟩ := spec_exists (U64.add_spec (x := i) (y := 1#u64) (by scalar_tac))
        rw [hadd]; simp only [bind_ok]
        exact (WP.spec_ok _).2 ⟨⟨hw.trans hw1, by scalar_tac⟩, by scalar_tac⟩
      · exact (WP.spec_ok _).2 ⟨hw, hx⟩
    · exact (WP.spec_ok _).2 ⟨hw, hx⟩
  · exact (WP.spec_ok _).2 ⟨hw, hx⟩

theorem BufOutsideHyp.wfr {th : TypedHeap} {s s' : S} {buf : U64} (h : BufOutsideHyp (L := L) th s buf)
    (hw : WFr (L := L) th s s') : BufOutsideHyp (L := L) th s' buf := by
  intro h0 i hi
  obtain ⟨g1, g2, g3⟩ := h h0 i hi
  exact ⟨g1, g2, by rw [hw.2.1]; exact g3⟩

theorem body_loop1_wfr {th : TypedHeap} (hP : Placed th) {s0 : S} {ct : U64} (hC : TCtx (L := L) th s0 ct)
    {buf : U64} (hB : BufOutsideHyp (L := L) th s0 buf) (hb0 : buf ≠ 0#u64)
    (src n : U64) (hn : n.val ≤ 20) (x : S × U64) (hw : WFr (L := L) th s0 x.1) (hx : x.2.val ≤ 20) :
    tcb.read_registers_loop1.body st src n buf x.1 x.2 ⦃ r =>
      match r with
      | .done y => WFr (L := L) th s0 y.1 ∧ y.2.val ≤ 20
      | .cont x' => (WFr (L := L) th s0 x'.1 ∧ x'.2.val ≤ 20) ∧ x.2.val < x'.2.val ⦄ := by
  obtain ⟨s, i⟩ := x
  simp only at hw hx ⊢
  have hC1 := hC.wfr hw
  have hB1 := hB.wfr hw
  unfold tcb.read_registers_loop1.body
  split
  · rename_i h1
    have hin : i.val < n.val := (P1.gt_iff_val).1 h1
    split
    · rename_i h2
      have hi18 : i.val < 18 := by have := (P1.gt_iff_val).1 h2; rw [nframe_val] at this; exact this
      simp only [lift, bind_ok]
      refine WP.spec_bind (Array.index_usize_spec _ _ (by rw [cast_to_us i (by omega)]; simp; omega)) ?_
      rintro i2 -
      refine WP.spec_bind (Endp.obj.Tcb.reg.spec s src i2) ?_
      rintro v -
      obtain ⟨i3, hadd, hi3v⟩ := spec_exists (U64.add_spec (x := i) (y := 1#u64) (by scalar_tac))
      rw [hadd]; simp only [bind_ok]
      obtain ⟨ha, hsl, hd⟩ := hB1 hb0 i3 (by scalar_tac)
      refine WP.spec_bind (Endp.msg.buf_set.spec s buf i3 v) ?_
      rintro s1 rfl
      exact (WP.spec_ok _).2 ⟨⟨hw.trans (wfr_wr hP hC1.ksb ha hsl hd v), by scalar_tac⟩, by scalar_tac⟩
    · exact (WP.spec_ok _).2 ⟨hw, hx⟩
  · exact (WP.spec_ok _).2 ⟨hw, hx⟩

theorem body_loop2_wfr {th : TypedHeap} (hP : Placed th) {s0 : S} {ct : U64} (hC : TCtx (L := L) th s0 ct)
    (src n : U64) (hn : n.val ≤ 20) (x : S × U64) (hw : WFr (L := L) th s0 x.1) (hx : x.2.val ≤ 20) :
    tcb.read_registers_loop2.body st src n ct x.1 x.2 ⦃ r =>
      match r with
      | .done y => WFr (L := L) th s0 y.1 ∧ y.2.val ≤ 20
      | .cont x' => (WFr (L := L) th s0 x'.1 ∧ x'.2.val ≤ 20) ∧ x.2.val < x'.2.val ⦄ := by
  obtain ⟨s, k⟩ := x
  simp only at hw hx ⊢
  have hC1 := hC.wfr hw
  have hf := nframe_val
  unfold tcb.read_registers_loop2.body
  split
  · rename_i h1
    have hk2 : k.val < 2 := by have := (P1.gt_iff_val).1 h1; rw [ngp_val] at this; exact this
    obtain ⟨i, hadd0, hiv⟩ := spec_exists (U64.add_spec (x := k) (y := tcb.N_FRAME) (by scalar_tac))
    rw [hadd0]; simp only [bind_ok]
    split
    · split
      · rename_i h3
        have hi4 : i.val < 4 := by have := (P1.gt_iff_val).1 h3; rw [nmsg_val] at this; exact this
        simp only [lift, bind_ok]
        refine WP.spec_bind (Array.index_usize_spec _ _ (by rw [cast_to_us k (by omega)]; simp; omega)) ?_
        rintro i2 -
        refine WP.spec_bind (Endp.obj.Tcb.reg.spec s src i2) ?_
        rintro v -
        refine WP.spec_bind (Endp.msg_register_spec i hi4) ?_
        rintro r rfl
        refine WP.spec_bind (set_reg_wfr hP hC1.ksb hC1.tcb (Endp.regIdx_lt _) v) ?_
        intro s1 hw1
        obtain ⟨k1, hadd, hk1v⟩ := spec_exists (U64.add_spec (x := k) (y := 1#u64) (by scalar_tac))
        rw [hadd]; simp only [bind_ok]
        exact (WP.spec_ok _).2 ⟨⟨hw.trans hw1, by scalar_tac⟩, by scalar_tac⟩
      · exact (WP.spec_ok _).2 ⟨hw, hx⟩
    · exact (WP.spec_ok _).2 ⟨hw, hx⟩
  · exact (WP.spec_ok _).2 ⟨hw, hx⟩

theorem body_loop3_wfr {th : TypedHeap} (hP : Placed th) {s0 : S} {ct : U64} (hC : TCtx (L := L) th s0 ct)
    {buf : U64} (hB : BufOutsideHyp (L := L) th s0 buf) (hb0 : buf ≠ 0#u64)
    (src n : U64) (hn : n.val ≤ 20) (x : S × U64) (hw : WFr (L := L) th s0 x.1) (hx : x.2.val ≤ 20) :
    tcb.read_registers_loop3.body st src n buf x.1 x.2 ⦃ r =>
      match r with
      | .done y => WFr (L := L) th s0 y.1 ∧ y.2.val ≤ 20
      | .cont x' => (WFr (L := L) th s0 x'.1 ∧ x'.2.val ≤ 20) ∧ x.2.val < x'.2.val ⦄ := by
  obtain ⟨s, k⟩ := x
  simp only at hw hx ⊢
  have hC1 := hC.wfr hw
  have hB1 := hB.wfr hw
  have hf := nframe_val
  unfold tcb.read_registers_loop3.body
  split
  · rename_i h1
    have hk2 : k.val < 2 := by have := (P1.gt_iff_val).1 h1; rw [ngp_val] at this; exact this
    obtain ⟨i, hadd0, hiv⟩ := spec_exists (U64.add_spec (x := k) (y := tcb.N_FRAME) (by scalar_tac))
    rw [hadd0]; simp only [bind_ok]
    split
    · rename_i h2
      have hin : i.val < n.val := (P1.gt_iff_val).1 h2
      simp only [lift, bind_ok]
      refine WP.spec_bind (Array.index_usize_spec _ _ (by rw [cast_to_us k (by omega)]; simp; omega)) ?_
      rintro i2 -
      refine WP.spec_bind (Endp.obj.Tcb.reg.spec s src i2) ?_
      rintro v -
      obtain ⟨i3, hadd, hi3v⟩ := spec_exists (U64.add_spec (x := i) (y := 1#u64) (by scalar_tac))
      rw [hadd]; simp only [bind_ok]
      obtain ⟨ha, hsl, hd⟩ := hB1 hb0 i3 (by scalar_tac)
      refine WP.spec_bind (Endp.msg.buf_set.spec s buf i3 v) ?_
      rintro s1 rfl
      obtain ⟨k1, haddk, hk1v⟩ := spec_exists (U64.add_spec (x := k) (y := 1#u64) (by scalar_tac))
      rw [haddk]; simp only [bind_ok]
      exact (WP.spec_ok _).2 ⟨⟨hw.trans (wfr_wr hP hC1.ksb ha hsl hd v), by scalar_tac⟩, by scalar_tac⟩
    · exact (WP.spec_ok _).2 ⟨hw, hx⟩
  · exact (WP.spec_ok _).2 ⟨hw, hx⟩

theorem body_loop4_wfr {th : TypedHeap} (hP : Placed th) {s0 : S} {ct : U64} (hC : TCtx (L := L) th s0 ct)
    (src n : U64) (hn : n.val ≤ 20) (x : S × U64) (hw : WFr (L := L) th s0 x.1) (hx : x.2.val ≤ 20) :
    tcb.read_registers_loop4.body st src n ct x.1 x.2 ⦃ r =>
      match r with
      | .done y => WFr (L := L) th s0 y.1 ∧ y.2.val ≤ 20
      | .cont x' => (WFr (L := L) th s0 x'.1 ∧ x'.2.val ≤ 20) ∧ x.2.val < x'.2.val ⦄ := by
  obtain ⟨s, k⟩ := x
  simp only at hw hx ⊢
  have hC1 := hC.wfr hw
  have hf := nframe_val
  unfold tcb.read_registers_loop4.body
  split
  · rename_i h1
    have hk2 : k.val < 2 := by have := (P1.gt_iff_val).1 h1; rw [ngp_val] at this; exact this
    obtain ⟨i, hadd0, hiv⟩ := spec_exists (U64.add_spec (x := k) (y := tcb.N_FRAME) (by scalar_tac))
    rw [hadd0]; simp only [bind_ok]
    split
    · split
      · rename_i h3
        have hi4 : i.val < 4 := by have := (P1.gt_iff_val).1 h3; rw [nmsg_val] at this; exact this
        simp only [lift, bind_ok]
        refine WP.spec_bind (Array.index_usize_spec _ _ (by rw [cast_to_us k (by omega)]; simp; omega)) ?_
        rintro i2 -
        refine WP.spec_bind (Endp.obj.Tcb.reg.spec s src i2) ?_
        rintro v -
        refine WP.spec_bind (Endp.msg_register_spec i hi4) ?_
        rintro r rfl
        refine WP.spec_bind (set_reg_wfr hP hC1.ksb hC1.tcb (Endp.regIdx_lt _) v) ?_
        intro s1 hw1
        obtain ⟨k1, hadd, hk1v⟩ := spec_exists (U64.add_spec (x := k) (y := 1#u64) (by scalar_tac))
        rw [hadd]; simp only [bind_ok]
        exact (WP.spec_ok _).2 ⟨⟨hw.trans hw1, by scalar_tac⟩, by scalar_tac⟩
      · exact (WP.spec_ok _).2 ⟨hw, hx⟩
    · exact (WP.spec_ok _).2 ⟨hw, hx⟩
  · exact (WP.spec_ok _).2 ⟨hw, hx⟩

theorem body_loop6_wfr {th : TypedHeap} (hP : Placed th) {s0 : S} {ct : U64} (hC : TCtx (L := L) th s0 ct)
    (src n : U64) (hn : n.val ≤ 20) (x : S × U64) (hw : WFr (L := L) th s0 x.1) (hx : x.2.val ≤ 20) :
    tcb.read_registers_loop6.body st src n ct x.1 x.2 ⦃ r =>
      match r with
      | .done y => WFr (L := L) th s0 y.1 ∧ y.2.val ≤ 20
      | .cont x' => (WFr (L := L) th s0 x'.1 ∧ x'.2.val ≤ 20) ∧ x.2.val < x'.2.val ⦄ := by
  obtain ⟨s, k⟩ := x
  simp only at hw hx ⊢
  have hC1 := hC.wfr hw
  have hf := nframe_val
  unfold tcb.read_registers_loop6.body
  split
  · rename_i h1
    have hk2 : k.val < 2 := by have := (P1.gt_iff_val).1 h1; rw [ngp_val] at this; exact this
    obtain ⟨i, hadd0, hiv⟩ := spec_exists (U64.add_spec (x := k) (y := tcb.N_FRAME) (by scalar_tac))
    rw [hadd0]; simp only [bind_ok]
    split
    · split
      · rename_i h3
        have hi4 : i.val < 4 := by have := (P1.gt_iff_val).1 h3; rw [nmsg_val] at this; exact this
        simp only [lift, bind_ok]
        refine WP.spec_bind (Array.index_usize_spec _ _ (by rw [cast_to_us k (by omega)]; simp; omega)) ?_
        rintro i2 -
        refine WP.spec_bind (Endp.obj.Tcb.reg.spec s src i2) ?_
        rintro v -
        refine WP.spec_bind (Endp.msg_register_spec i hi4) ?_
        rintro r rfl
        refine WP.spec_bind (set_reg_wfr hP hC1.ksb hC1.tcb (Endp.regIdx_lt _) v) ?_
        intro s1 hw1
        obtain ⟨k1, hadd, hk1v⟩ := spec_exists (U64.add_spec (x := k) (y := 1#u64) (by scalar_tac))
        rw [hadd]; simp only [bind_ok]
        exact (WP.spec_ok _).2 ⟨⟨hw.trans hw1, by scalar_tac⟩, by scalar_tac⟩
      · exact (WP.spec_ok _).2 ⟨hw, hx⟩
    · exact (WP.spec_ok _).2 ⟨hw, hx⟩
  · exact (WP.spec_ok _).2 ⟨hw, hx⟩

theorem body_loop8_wfr {th : TypedHeap} (hP : Placed th) {s0 : S} {ct : U64} (hC : TCtx (L := L) th s0 ct)
    (src n : U64) (hn : n.val ≤ 20) (x : S × U64) (hw : WFr (L := L) th s0 x.1) (hx : x.2.val ≤ 20) :
    tcb.read_registers_loop8.body st src n ct x.1 x.2 ⦃ r =>
      match r with
      | .done y => WFr (L := L) th s0 y.1 ∧ y.2.val ≤ 20
      | .cont x' => (WFr (L := L) th s0 x'.1 ∧ x'.2.val ≤ 20) ∧ x.2.val < x'.2.val ⦄ := by
  obtain ⟨s, k⟩ := x
  simp only at hw hx ⊢
  have hC1 := hC.wfr hw
  have hf := nframe_val
  unfold tcb.read_registers_loop8.body
  split
  · rename_i h1
    have hk2 : k.val < 2 := by have := (P1.gt_iff_val).1 h1; rw [ngp_val] at this; exact this
    obtain ⟨i, hadd0, hiv⟩ := spec_exists (U64.add_spec (x := k) (y := tcb.N_FRAME) (by scalar_tac))
    rw [hadd0]; simp only [bind_ok]
    split
    · split
      · rename_i h3
        have hi4 : i.val < 4 := by have := (P1.gt_iff_val).1 h3; rw [nmsg_val] at this; exact this
        simp only [lift, bind_ok]
        refine WP.spec_bind (Array.index_usize_spec _ _ (by rw [cast_to_us k (by omega)]; simp; omega)) ?_
        rintro i2 -
        refine WP.spec_bind (Endp.obj.Tcb.reg.spec s src i2) ?_
        rintro v -
        refine WP.spec_bind (Endp.msg_register_spec i hi4) ?_
        rintro r rfl
        refine WP.spec_bind (set_reg_wfr hP hC1.ksb hC1.tcb (Endp.regIdx_lt _) v) ?_
        intro s1 hw1
        obtain ⟨k1, hadd, hk1v⟩ := spec_exists (U64.add_spec (x := k) (y := 1#u64) (by scalar_tac))
        rw [hadd]; simp only [bind_ok]
        exact (WP.spec_ok _).2 ⟨⟨hw.trans hw1, by scalar_tac⟩, by scalar_tac⟩
      · exact (WP.spec_ok _).2 ⟨hw, hx⟩
    · exact (WP.spec_ok _).2 ⟨hw, hx⟩
  · exact (WP.spec_ok _).2 ⟨hw, hx⟩

theorem body_loop5_wfr {th : TypedHeap} (hP : Placed th) {s0 : S} {ct : U64} (hC : TCtx (L := L) th s0 ct)
    {buf : U64} (hB : BufOutsideHyp (L := L) th s0 buf) (hb0 : buf ≠ 0#u64)
    (src n : U64) (hn : n.val ≤ 20) (x : S × U64) (hw : WFr (L := L) th s0 x.1) (hx : x.2.val ≤ 20) :
    tcb.read_registers_loop5.body st src n buf x.1 x.2 ⦃ r =>
      match r with
      | .done y => WFr (L := L) th s0 y.1 ∧ y.2.val ≤ 20
      | .cont x' => (WFr (L := L) th s0 x'.1 ∧ x'.2.val ≤ 20) ∧ x.2.val < x'.2.val ⦄ := by
  obtain ⟨s, k⟩ := x
  simp only at hw hx ⊢
  have hC1 := hC.wfr hw
  have hB1 := hB.wfr hw
  have hf := nframe_val
  unfold tcb.read_registers_loop5.body
  split
  · rename_i h1
    have hk2 : k.val < 2 := by have := (P1.gt_iff_val).1 h1; rw [ngp_val] at this; exact this
    obtain ⟨i, hadd0, hiv⟩ := spec_exists (U64.add_spec (x := k) (y := tcb.N_FRAME) (by scalar_tac))
    rw [hadd0]; simp only [bind_ok]
    split
    · rename_i h2
      have hin : i.val < n.val := (P1.gt_iff_val).1 h2
      simp only [lift, bind_ok]
      refine WP.spec_bind (Array.index_usize_spec _ _ (by rw [cast_to_us k (by omega)]; simp; omega)) ?_
      rintro i2 -
      refine WP.spec_bind (Endp.obj.Tcb.reg.spec s src i2) ?_
      rintro v -
      obtain ⟨i3, hadd, hi3v⟩ := spec_exists (U64.add_spec (x := i) (y := 1#u64) (by scalar_tac))
      rw [hadd]; simp only [bind_ok]
      obtain ⟨ha, hsl, hd⟩ := hB1 hb0 i3 (by scalar_tac)
      refine WP.spec_bind (Endp.msg.buf_set.spec s buf i3 v) ?_
      rintro s1 rfl
      obtain ⟨k1, haddk, hk1v⟩ := spec_exists (U64.add_spec (x := k) (y := 1#u64) (by scalar_tac))
      rw [haddk]; simp only [bind_ok]
      exact (WP.spec_ok _).2 ⟨⟨hw.trans (wfr_wr hP hC1.ksb ha hsl hd v), by scalar_tac⟩, by scalar_tac⟩
    · exact (WP.spec_ok _).2 ⟨hw, hx⟩
  · exact (WP.spec_ok _).2 ⟨hw, hx⟩

theorem body_loop7_wfr {th : TypedHeap} (hP : Placed th) {s0 : S} {ct : U64} (hC : TCtx (L := L) th s0 ct)
    {buf : U64} (hB : BufOutsideHyp (L := L) th s0 buf) (hb0 : buf ≠ 0#u64)
    (src n : U64) (hn : n.val ≤ 20) (x : S × U64) (hw : WFr (L := L) th s0 x.1) (hx : x.2.val ≤ 20) :
    tcb.read_registers_loop7.body st src n buf x.1 x.2 ⦃ r =>
      match r with
      | .done y => WFr (L := L) th s0 y.1 ∧ y.2.val ≤ 20
      | .cont x' => (WFr (L := L) th s0 x'.1 ∧ x'.2.val ≤ 20) ∧ x.2.val < x'.2.val ⦄ := by
  obtain ⟨s, k⟩ := x
  simp only at hw hx ⊢
  have hC1 := hC.wfr hw
  have hB1 := hB.wfr hw
  have hf := nframe_val
  unfold tcb.read_registers_loop7.body
  split
  · rename_i h1
    have hk2 : k.val < 2 := by have := (P1.gt_iff_val).1 h1; rw [ngp_val] at this; exact this
    obtain ⟨i, hadd0, hiv⟩ := spec_exists (U64.add_spec (x := k) (y := tcb.N_FRAME) (by scalar_tac))
    rw [hadd0]; simp only [bind_ok]
    split
    · rename_i h2
      have hin : i.val < n.val := (P1.gt_iff_val).1 h2
      simp only [lift, bind_ok]
      refine WP.spec_bind (Array.index_usize_spec _ _ (by rw [cast_to_us k (by omega)]; simp; omega)) ?_
      rintro i2 -
      refine WP.spec_bind (Endp.obj.Tcb.reg.spec s src i2) ?_
      rintro v -
      obtain ⟨i3, hadd, hi3v⟩ := spec_exists (U64.add_spec (x := i) (y := 1#u64) (by scalar_tac))
      rw [hadd]; simp only [bind_ok]
      obtain ⟨ha, hsl, hd⟩ := hB1 hb0 i3 (by scalar_tac)
      refine WP.spec_bind (Endp.msg.buf_set.spec s buf i3 v) ?_
      rintro s1 rfl
      obtain ⟨k1, haddk, hk1v⟩ := spec_exists (U64.add_spec (x := k) (y := 1#u64) (by scalar_tac))
      rw [haddk]; simp only [bind_ok]
      exact (WP.spec_ok _).2 ⟨⟨hw.trans (wfr_wr hP hC1.ksb ha hsl hd v), by scalar_tac⟩, by scalar_tac⟩
    · exact (WP.spec_ok _).2 ⟨hw, hx⟩
  · exact (WP.spec_ok _).2 ⟨hw, hx⟩

theorem body_loop9_wfr {th : TypedHeap} (hP : Placed th) {s0 : S} {ct : U64} (hC : TCtx (L := L) th s0 ct)
    {buf : U64} (hB : BufOutsideHyp (L := L) th s0 buf) (hb0 : buf ≠ 0#u64)
    (src n : U64) (hn : n.val ≤ 20) (x : S × U64) (hw : WFr (L := L) th s0 x.1) (hx : x.2.val ≤ 20) :
    tcb.read_registers_loop9.body st src n buf x.1 x.2 ⦃ r =>
      match r with
      | .done y => WFr (L := L) th s0 y.1 ∧ y.2.val ≤ 20
      | .cont x' => (WFr (L := L) th s0 x'.1 ∧ x'.2.val ≤ 20) ∧ x.2.val < x'.2.val ⦄ := by
  obtain ⟨s, k⟩ := x
  simp only at hw hx ⊢
  have hC1 := hC.wfr hw
  have hB1 := hB.wfr hw
  have hf := nframe_val
  unfold tcb.read_registers_loop9.body
  split
  · rename_i h1
    have hk2 : k.val < 2 := by have := (P1.gt_iff_val).1 h1; rw [ngp_val] at this; exact this
    obtain ⟨i, hadd0, hiv⟩ := spec_exists (U64.add_spec (x := k) (y := tcb.N_FRAME) (by scalar_tac))
    rw [hadd0]; simp only [bind_ok]
    split
    · rename_i h2
      have hin : i.val < n.val := (P1.gt_iff_val).1 h2
      simp only [lift, bind_ok]
      refine WP.spec_bind (Array.index_usize_spec _ _ (by rw [cast_to_us k (by omega)]; simp; omega)) ?_
      rintro i2 -
      refine WP.spec_bind (Endp.obj.Tcb.reg.spec s src i2) ?_
      rintro v -
      obtain ⟨i3, hadd, hi3v⟩ := spec_exists (U64.add_spec (x := i) (y := 1#u64) (by scalar_tac))
      rw [hadd]; simp only [bind_ok]
      obtain ⟨ha, hsl, hd⟩ := hB1 hb0 i3 (by scalar_tac)
      refine WP.spec_bind (Endp.msg.buf_set.spec s buf i3 v) ?_
      rintro s1 rfl
      obtain ⟨k1, haddk, hk1v⟩ := spec_exists (U64.add_spec (x := k) (y := 1#u64) (by scalar_tac))
      rw [haddk]; simp only [bind_ok]
      exact (WP.spec_ok _).2 ⟨⟨hw.trans (wfr_wr hP hC1.ksb ha hsl hd v), by scalar_tac⟩, by scalar_tac⟩
    · exact (WP.spec_ok _).2 ⟨hw, hx⟩
  · exact (WP.spec_ok _).2 ⟨hw, hx⟩

theorem loop0_wfr {th : TypedHeap} (hP : Placed th) {s0 : S} {ct : U64} (hC : TCtx (L := L) th s0 ct)
    (src n : U64) (hn : n.val ≤ 20) (s : S) (i : U64) (hw : WFr (L := L) th s0 s) (hi : i.val ≤ 20) :
    tcb.read_registers_loop0 st s src n ct i ⦃ y => WFr (L := L) th s0 y.1 ∧ y.2.val ≤ 20 ⦄ := by
  unfold tcb.read_registers_loop0
  exact loop_wfr s0 _ (s, i) ⟨hw, hi⟩ fun x h1 h2 => body0_wfr hP hC src n hn x h1 h2

theorem loop1_wfr {th : TypedHeap} (hP : Placed th) {s0 : S} {ct : U64} (hC : TCtx (L := L) th s0 ct)
    {buf : U64} (hB : BufOutsideHyp (L := L) th s0 buf) (hb0 : buf ≠ 0#u64)
    (src n : U64) (hn : n.val ≤ 20) (s : S) (i : U64) (hw : WFr (L := L) th s0 s) (hi : i.val ≤ 20) :
    tcb.read_registers_loop1 st s src n buf i ⦃ y => WFr (L := L) th s0 y.1 ∧ y.2.val ≤ 20 ⦄ := by
  unfold tcb.read_registers_loop1
  exact loop_wfr s0 _ (s, i) ⟨hw, hi⟩ fun x h1 h2 => body_loop1_wfr hP hC hB hb0 src n hn x h1 h2

theorem loop2_wfr {th : TypedHeap} (hP : Placed th) {s0 : S} {ct : U64} (hC : TCtx (L := L) th s0 ct)
    (src n : U64) (hn : n.val ≤ 20) (s : S) (i : U64) (hw : WFr (L := L) th s0 s) (hi : i.val ≤ 20) :
    tcb.read_registers_loop2 st s src n ct i ⦃ y => WFr (L := L) th s0 y.1 ∧ y.2.val ≤ 20 ⦄ := by
  unfold tcb.read_registers_loop2
  exact loop_wfr s0 _ (s, i) ⟨hw, hi⟩ fun x h1 h2 => body_loop2_wfr hP hC src n hn x h1 h2

theorem loop3_wfr {th : TypedHeap} (hP : Placed th) {s0 : S} {ct : U64} (hC : TCtx (L := L) th s0 ct)
    {buf : U64} (hB : BufOutsideHyp (L := L) th s0 buf) (hb0 : buf ≠ 0#u64)
    (src n : U64) (hn : n.val ≤ 20) (s : S) (i : U64) (hw : WFr (L := L) th s0 s) (hi : i.val ≤ 20) :
    tcb.read_registers_loop3 st s src n buf i ⦃ y => WFr (L := L) th s0 y.1 ∧ y.2.val ≤ 20 ⦄ := by
  unfold tcb.read_registers_loop3
  exact loop_wfr s0 _ (s, i) ⟨hw, hi⟩ fun x h1 h2 => body_loop3_wfr hP hC hB hb0 src n hn x h1 h2

theorem loop4_wfr {th : TypedHeap} (hP : Placed th) {s0 : S} {ct : U64} (hC : TCtx (L := L) th s0 ct)
    (src n : U64) (hn : n.val ≤ 20) (s : S) (i : U64) (hw : WFr (L := L) th s0 s) (hi : i.val ≤ 20) :
    tcb.read_registers_loop4 st s src n ct i ⦃ y => WFr (L := L) th s0 y.1 ∧ y.2.val ≤ 20 ⦄ := by
  unfold tcb.read_registers_loop4
  exact loop_wfr s0 _ (s, i) ⟨hw, hi⟩ fun x h1 h2 => body_loop4_wfr hP hC src n hn x h1 h2

theorem loop5_wfr {th : TypedHeap} (hP : Placed th) {s0 : S} {ct : U64} (hC : TCtx (L := L) th s0 ct)
    {buf : U64} (hB : BufOutsideHyp (L := L) th s0 buf) (hb0 : buf ≠ 0#u64)
    (src n : U64) (hn : n.val ≤ 20) (s : S) (i : U64) (hw : WFr (L := L) th s0 s) (hi : i.val ≤ 20) :
    tcb.read_registers_loop5 st s src n buf i ⦃ y => WFr (L := L) th s0 y.1 ∧ y.2.val ≤ 20 ⦄ := by
  unfold tcb.read_registers_loop5
  exact loop_wfr s0 _ (s, i) ⟨hw, hi⟩ fun x h1 h2 => body_loop5_wfr hP hC hB hb0 src n hn x h1 h2

theorem loop6_wfr {th : TypedHeap} (hP : Placed th) {s0 : S} {ct : U64} (hC : TCtx (L := L) th s0 ct)
    (src n : U64) (hn : n.val ≤ 20) (s : S) (i : U64) (hw : WFr (L := L) th s0 s) (hi : i.val ≤ 20) :
    tcb.read_registers_loop6 st s src n ct i ⦃ y => WFr (L := L) th s0 y.1 ∧ y.2.val ≤ 20 ⦄ := by
  unfold tcb.read_registers_loop6
  exact loop_wfr s0 _ (s, i) ⟨hw, hi⟩ fun x h1 h2 => body_loop6_wfr hP hC src n hn x h1 h2

theorem loop7_wfr {th : TypedHeap} (hP : Placed th) {s0 : S} {ct : U64} (hC : TCtx (L := L) th s0 ct)
    {buf : U64} (hB : BufOutsideHyp (L := L) th s0 buf) (hb0 : buf ≠ 0#u64)
    (src n : U64) (hn : n.val ≤ 20) (s : S) (i : U64) (hw : WFr (L := L) th s0 s) (hi : i.val ≤ 20) :
    tcb.read_registers_loop7 st s src n buf i ⦃ y => WFr (L := L) th s0 y.1 ∧ y.2.val ≤ 20 ⦄ := by
  unfold tcb.read_registers_loop7
  exact loop_wfr s0 _ (s, i) ⟨hw, hi⟩ fun x h1 h2 => body_loop7_wfr hP hC hB hb0 src n hn x h1 h2

theorem loop8_wfr {th : TypedHeap} (hP : Placed th) {s0 : S} {ct : U64} (hC : TCtx (L := L) th s0 ct)
    (src n : U64) (hn : n.val ≤ 20) (s : S) (i : U64) (hw : WFr (L := L) th s0 s) (hi : i.val ≤ 20) :
    tcb.read_registers_loop8 st s src n ct i ⦃ y => WFr (L := L) th s0 y.1 ∧ y.2.val ≤ 20 ⦄ := by
  unfold tcb.read_registers_loop8
  exact loop_wfr s0 _ (s, i) ⟨hw, hi⟩ fun x h1 h2 => body_loop8_wfr hP hC src n hn x h1 h2

theorem loop9_wfr {th : TypedHeap} (hP : Placed th) {s0 : S} {ct : U64} (hC : TCtx (L := L) th s0 ct)
    {buf : U64} (hB : BufOutsideHyp (L := L) th s0 buf) (hb0 : buf ≠ 0#u64)
    (src n : U64) (hn : n.val ≤ 20) (s : S) (i : U64) (hw : WFr (L := L) th s0 s) (hi : i.val ≤ 20) :
    tcb.read_registers_loop9 st s src n buf i ⦃ y => WFr (L := L) th s0 y.1 ∧ y.2.val ≤ 20 ⦄ := by
  unfold tcb.read_registers_loop9
  exact loop_wfr s0 _ (s, i) ⟨hw, hi⟩ fun x h1 h2 => body_loop9_wfr hP hC hB hb0 src n hn x h1 h2


theorem BufOutsideHyp.ksb {th : TypedHeap} {s s' : S} {buf : U64} (h : BufOutsideHyp (L := L) th s buf)
    (hk : L.ksb s' = L.ksb s) : BufOutsideHyp (L := L) th s' buf := by
  intro h0 i hi
  obtain ⟨g1, g2, g3⟩ := h h0 i hi
  exact ⟨g1, g2, by rw [hk]; exact g3⟩

/-- The message info and `Running` after the copy loops. -/
theorem rr_tail {th : TypedHeap} (hP : Placed th) {s1 s : S} {ct : U64} (hC : TCtx (L := L) th s1 ct)
    (hw : WFr (L := L) th s1 s) {x y : U64} (hx : x.val ≤ 20) (hy : y.val ≤ 20) {A : Type} (a1 : A) :
    (do
      let i ← lift (core.num.U64.wrapping_add x y)
      let mi ← msginfo.MessageInfo.new 0#u64 0#u64 0#u64 i
      let s5 ← msg.set_msg_info st s ct mi
      let s6 ← sched.set_thread_state st s5 ct sched.TS_RUNNING
      ok (s6, a1)) ⦃ r => WFr (L := L) th s1 r.1 ∧ L.mem r.1 (stA ct) = sched.TS_RUNNING ⦄ := by
  simp only [lift, bind_ok]
  unfold msginfo.MessageInfo.new
  simp only [bind_ok]
  have hC' := hC.wfr hw
  have hv : (core.num.U64.wrapping_add x y).val < 128 := by
    rw [core.num.U64.wrapping_add_val_eq]; simp [U64.size_def, U64.numBits]; omega
  refine WP.spec_bind (set_msg_info_wfr hP hC'.ksb hC'.tcb 0#u64 _ hv) ?_
  intro s5 hw5
  refine WP.spec_bind (sts_t hP (hC'.wfr hw5) sched.TS_RUNNING) ?_
  rintro s6 ⟨hw6, hst⟩
  exact (WP.spec_ok _).2 ⟨hw.trans (hw5.trans hw6), hst⟩

theorem add_nframe_spec (k : U64) (hk : k.val ≤ 20) : (k + tcb.N_FRAME) ⦃ z => z.val = k.val + 18 ⦄ := by
  have := nframe_val
  obtain ⟨z, h, hz⟩ := spec_exists (U64.add_spec (x := k) (y := tcb.N_FRAME) (by scalar_tac))
  rw [h]; exact (WP.spec_ok _).2 (by scalar_tac)

set_option maxHeartbeats 2000000 in
/-- **FL4's `read_registers` is a `WFr` step leaving the caller `Running`**,
the source's suspend one. -/
theorem read_registers_frame {A : Type} (arI : machine.Arch A) {th : TypedHeap} (hP : Placed th) {s1 : S}
    {ct : U64} (hC : TCtx (L := L) th s1 ct) (hct : sched.cur_thread st s1 = ok ct) (a : A) (src : U64)
    (susp : Bool) (n : U64) (hn : n.val ≤ 20) (call : Bool)
    (hS : susp = true → sched.suspend st arI s1 a src ⦃ r => WFr (L := L) th s1 r.1 ⦄)
    (hB : ∀ s' rw, WFr (L := L) th s1 s' → msg.lookup_ipc_buffer st s' true ct = ok rw →
      BufOutsideHyp (L := L) th s' rw) :
    tcb.read_registers st arI s1 a src susp n call ⦃ r =>
      WFr (L := L) th s1 r.1 ∧ L.mem r.1 (stA ct) = sched.TS_RUNNING ⦄ := by
  unfold tcb.read_registers
  rw [hct]; simp only [bind_ok]
  refine WP.spec_bind (Pₘ := fun r : S × A => WFr (L := L) th s1 r.1) ?_ ?_
  · split
    · exact hS ‹_›
    · exact (WP.spec_ok _).2 (WFr.refl _ _)
  rintro ⟨s2, a1⟩ hW2
  cases call
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_bind (sts_t hP (hC.wfr hW2) _) ?_
    rintro s3 ⟨hW3, hst⟩
    exact (WP.spec_ok _).2 ⟨hW2.trans hW3, hst⟩
  · simp only [↓reduceIte]
    obtain ⟨bf, hl, -⟩ := spec_exists (Fl4Proofs.P0.msg.lookup_ipc_buffer.p0 st s2 true ct L.total)
    have hBf : BufOutsideHyp (L := L) th s1 bf := (hB s2 bf hW2 hl).ksb hW2.2.1.symm
    have hlk : msg.lookup_ipc_buffer st s2 true ct ⦃ r => r = bf ⦄ := by rw [hl]; exact (WP.spec_ok _).2 rfl
    refine WP.spec_bind hlk ?_
    rintro _ rfl
    refine WP.spec_bind (set_reg_wfr hP (hC.wfr hW2).ksb hC.tcb (i := layout.reg.BADGE)
      (by unfold layout.reg.BADGE layout.reg.RDI; decide) 0#u64) ?_
    intro s3 hW3
    have hW23 := hW2.trans hW3
    try simp only [uncurry_apply_pair]
    refine WP.spec_bind (loop0_wfr hP hC src n hn s3 0#u64 hW23 (by simp)) ?_
    rintro ⟨s4, i⟩ ⟨hW4, hi⟩
    simp only [uncurry_apply_pair] at hW4 hi ⊢
    repeat (first
    | (split
       try (rename_i hbuf; have hb0 := bne_iff_ne.mp hbuf))
    | (refine WP.spec_bind (loop1_wfr hP hC hBf (by assumption) src n hn _ _ (by assumption) (by assumption)) ?_
       rintro ⟨_, _⟩ ⟨_, _⟩
       try simp only [uncurry_apply_pair])
    | (refine WP.spec_bind (loop3_wfr hP hC hBf (by assumption) src n hn _ _ (by assumption) (by assumption)) ?_
       rintro ⟨_, _⟩ ⟨_, _⟩
       try simp only [uncurry_apply_pair])
    | (refine WP.spec_bind (loop5_wfr hP hC hBf (by assumption) src n hn _ _ (by assumption) (by assumption)) ?_
       rintro ⟨_, _⟩ ⟨_, _⟩
       try simp only [uncurry_apply_pair])
    | (refine WP.spec_bind (loop7_wfr hP hC hBf (by assumption) src n hn _ _ (by assumption) (by assumption)) ?_
       rintro ⟨_, _⟩ ⟨_, _⟩
       try simp only [uncurry_apply_pair])
    | (refine WP.spec_bind (loop9_wfr hP hC hBf (by assumption) src n hn _ _ (by assumption) (by assumption)) ?_
       rintro ⟨_, _⟩ ⟨_, _⟩
       try simp only [uncurry_apply_pair])
    | (refine WP.spec_bind (loop2_wfr hP hC src n hn _ _ (by assumption) (by simp)) ?_
       rintro ⟨_, _⟩ ⟨_, _⟩
       try simp only [uncurry_apply_pair])
    | (refine WP.spec_bind (loop4_wfr hP hC src n hn _ _ (by assumption) (by simp)) ?_
       rintro ⟨_, _⟩ ⟨_, _⟩
       try simp only [uncurry_apply_pair])
    | (refine WP.spec_bind (loop6_wfr hP hC src n hn _ _ (by assumption) (by simp)) ?_
       rintro ⟨_, _⟩ ⟨_, _⟩
       try simp only [uncurry_apply_pair])
    | (refine WP.spec_bind (loop8_wfr hP hC src n hn _ _ (by assumption) (by simp)) ?_
       rintro ⟨_, _⟩ ⟨_, _⟩
       try simp only [uncurry_apply_pair])
    | (refine WP.spec_bind (add_nframe_spec _ (by assumption)) ?_
       intro _ _)
    | exact rr_tail hP hC (by assumption) (by assumption) (by assumption) _)



/-- The current thread across `set_thread_state`, its node word outside the
objects. -/
theorem cur_thread_sts {th : TypedHeap} (hP : Placed th) {s s1 : S} {t v ct : U64} (hC : TCtx (L := L) th s t)
    (hcw : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD))
    (hct : sched.cur_thread st s = ok ct) (hs1 : sched.set_thread_state st s t v = ok s1) :
    sched.cur_thread st s1 = ok ct := by
  have hc := set_thread_state_cases (L := L) s t v
  rw [hs1] at hc
  have hc' := (WP.spec_ok _).1 hc
  rw [cur_thread_eq] at hct ⊢
  have ht := hC.tcb
  have hf := hP.fits t _ ht
  have ha := hP.align t _ ht
  have e4 : objSize ObjKind.tcb = 4096 := rfl
  rw [e4] at hf
  have hv := stA_val hP ht
  have hal : P1.Aligned (stA t) := by unfold P1.Aligned; rw [hv]; omega
  have hne : (stA t).val ≠ (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD).val := fun e =>
    hcw.2 t _ ht ⟨by rw [← e, hv]; omega, by rw [← e, hv, e4]; omega⟩
  rcases hc' with rfl | rfl
  · have hn : L.nodeAt (L.wr s (stA t) v) (L.cpu (L.wr s (stA t) v)) layout.node.CUR_THREAD =
        L.nodeAt s (L.cpu s) layout.node.CUR_THREAD := by simp [P1.LawfulStore.nodeAt]
    rw [hn, L.mem_wr_ne hal hcw.1 hne]; exact hct
  · have hn : L.nodeAt (L.wr (L.wr s (stA t) v) (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION)
        sched.ACTION_CHOOSE_NEW) (L.cpu (L.wr (L.wr s (stA t) v) (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION)
        sched.ACTION_CHOOSE_NEW)) layout.node.CUR_THREAD = L.nodeAt s (L.cpu s) layout.node.CUR_THREAD := by
      simp [P1.LawfulStore.nodeAt]
    rw [hn, L.mem_wr_ne hC.act.1 hcw.1 (Ne.symm (cur_ne_action s)), L.mem_wr_ne hal hcw.1 hne]
    exact hct

/-- **The source's suspend** (P1's): a `WFr` step after the restart. -/
def SuspendWFrHyp {A : Type} (arI : machine.Arch A) (th : TypedHeap) (s : S) (ct p : U64) : Prop :=
  ∀ s1 (a : A), sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
    sched.suspend st arI s1 a p ⦃ r => WFr (L := L) th s1 r.1 ⦄

/-- **`ReadRegsFrameHyp` from the suspend's frame** and the caller's buffer
placement. -/
theorem readRegsFrameHyp_of {A : Type} (arI : machine.Arch A) {th : TypedHeap} (hP : Placed th) {s : S}
    {ct p : U64} (hC : TCtx (L := L) th s ct)
    (hcw : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD))
    (hct : sched.cur_thread st s = ok ct) (hS : SuspendWFrHyp (L := L) arI th s ct p)
    (hB : CallerBufHyp (L := L) th s ct) : ReadRegsFrameHyp (L := L) arI th s ct p := by
  intro s1 flags n call a hs1 _ h20
  have hW : WFr (L := L) th s s1 := by
    have h := sts_t hP hC sched.TS_RESTART
    rw [hs1] at h
    exact ((WP.spec_ok _).1 h).1
  exact read_registers_frame arI hP (hC.wfr hW) (cur_thread_sts hP hC hcw hct hs1) a p _ n h20 call
    (fun _ => hS s1 a hs1) (fun s' rw h hl => hB s' rw (hW.trans h) hl)

end

end

end Fl4Proofs.P3
