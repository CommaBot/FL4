/-
P2 (p2j4): **the message transfer writes only `CONSUMED` among SC words**.

P1's transfer footprint `XferW` (`P1/QueueXferFoot.lean`) admits every word
of every SC (`InSC`). The real transfer writes exactly one kind of SC word:
a timeout-fault message resets the faulting SC's `CONSUMED`
(`schedcontext.update_consumed`). This module re-runs P1's `XSF` steps with
the narrower footprint `XferWC` (SC words replaced by `CONSUMED` words, `XferConsW`)
and states `XferFootOKC` (P1's `XferFootOK` with `XferWC`). The lemma bodies
are P1's, over `XSFC` (`XSF` with `XferWC`); P1's statements are unchanged.

**(p2j8)** `XferFootOKC` is a **named premise [J]** of its users
(`stallSeq.entryN`, `stallAt.views`, `stallAt.all`). Its earlier discharge
`xferFootOKC_of` (with `transfer_caps_loop.xsfc`, `transfer_caps.xsfc`,
`do_normal_transfer.xsfc`) took P1's `XferHyps`, which is vacuous at `XG`
states (its `buf`/`extra`/`slot` fields claim cap typing at every `XG` state;
refuted in par/p1g `P1/EntryVacuous.lean`), and is deleted. What remains here
(the `XSFC` steps of the register, buffer and fault transfers,
`do_fault_transfer.xsfc`) takes no `XferHyps`.

Unlike `XferHyps` (guarded by `XG` alone, which lets every cap-slot word be
rewritten), `XferFootOKC` is guarded by `RS s s`, the caller's relation, which
its users keep along the stall's `KW` writes (`hRSK`); `KW` writes no TCB cap
slot. Its discharge needs an `RS` carrying the typing of the caps the
transfer reads (the receiver's IPC-buffer slot, the extra-cap and receive
slots), i.e. P3's cap relation; with such an `RS` the premise is not refuted
the `XferHyps.buf_false` way. (P1's `XferOK`, also taken by the stall
theorems, has no `RS` guard; its only discharge is P1's `xferOK_of` from
`XferHyps`.)
-/
import Fl4Proofs.P1.QueueXferFoot
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

/-- The SCs' `CONSUMED` words. -/
def XferConsW (Scs : Set U64) (b : U64) : Prop := ∃ c ∈ Scs, b = core.num.U64.wrapping_add c layout.sc.CONSUMED

/-- `XferW` with only `CONSUMED` among SC words. -/
def XferWC (T U Ω Sg Scs : Set U64) (k b : U64) : Prop :=
  XferFoot T U b ∨ (CapW T Ω Sg b ∧ KG k b) ∨ XferConsW Scs b

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-- `XSF` with the footprint `XferWC`. -/
def XSFC (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64)
    (Z : U64 → Nat) (U : Set U64) (RS : S → S → Prop) (Ac X : Set U64) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (s0 s : S) : Prop :=
  XI st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s ∧
    (XferFr st T Rp s0 s ∧ WritesIn st s0 s (XferWC T U Ω Sg Scs (L.ksb s0)) ∧ RS s0 s ∧
      ∀ s1 s2 : S, RS s0 s1 → WritesIn st s1 s2 (fun b => XferRegW T U b ∨ XferConsW Scs b) →
        RS s0 s2)

variable {U X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {RS : S → S → Prop} {P3Ok : S → Prop}
  {RD : S → U64 → Prop}

/-- A placed SC's `CONSUMED` word is an aligned word inside it. -/
theorem consW_in {s : S} {c : U64} (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hc : c ∈ Scs) :
    Aligned (core.num.U64.wrapping_add c layout.sc.CONSUMED) ∧
      InSC c (Z c) (core.num.U64.wrapping_add c layout.sc.CONSUMED) := by
  obtain ⟨hP, hz⟩ := hO.sc c hc
  obtain ⟨h8, h128, -⟩ := sc_lo hP hz
  have hv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
  have hcv : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
  exact ⟨by unfold Aligned; rw [hv, hcv]; omega, by rw [hv]; omega, by rw [hv]; omega⟩

theorem XSFC.xs {s0 s : S} (h : XSFC st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R s0 s) :
    XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s :=
  ⟨h.1, h.2.1, h.2.2.1.mono fun _ hb => by
    rcases hb with hb | hb | ⟨c, hc, e⟩
    exacts [Or.inl hb, Or.inr (Or.inl hb.1), Or.inr (Or.inr ⟨c, hc, e ▸ (consW_in h.1.2.2.1.1 hc).2⟩)]⟩

theorem XSFC.ksb {s0 s : S} (h : XSFC st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R s0 s) : L.ksb s = L.ksb s0 :=
  h.2.1.2.2.2.2.2.2

theorem XSFC.start {s : S} (h : XI st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s) (h0 : RS s s)
    (hst : ∀ s1 s2 : S, RS s s1 → WritesIn st s1 s2 (fun b => XferRegW T U b ∨ ∃ c ∈ Scs, InSC c (Z c) b) →
      RS s s2) :
    XSFC st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R s s :=
  ⟨h, XferFr.refl s, WritesIn.refl s _, h0, fun s1 s2 r w => hst s1 s2 r (w.mono fun b hb =>
    hb.imp id fun ⟨c, hc, e⟩ => ⟨c, hc, e ▸ (consW_in h.2.2.1.1 hc).2⟩)⟩

theorem XSFC.rs {s0 s : S} (h : XSFC st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R s0 s) : RS s0 s := h.2.2.2.1

/-- A register or user-word write. -/
theorem XSFC.foot {s0 s s' : S} (h : XSFC st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R s0 s)
    (hw : WritesIn st s s' (XferRegW T U)) : XSFC st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R s0 s' := by
  have h' := XS.foot h.xs (hw.mono fun _ hb => hb.foot)
  exact ⟨h'.1, h'.2.1, (h.2.2.1.trans hw).mono (fun b hb => hb.elim id fun hb => Or.inl hb.foot),
    h.2.2.2.2 _ _ h.rs (hw.mono fun b hb => Or.inl hb), h.2.2.2.2⟩

/-- A write of cap-slot words apart from the kernel-global block's first 256 bytes. -/
theorem XSFC.capw {s0 s s' : S} {B : U64 → Prop} (h : XSFC st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R s0 s)
    (hw : WritesIn st s s' B) (hB : ∀ b, B b → CapW T Ω Sg b ∧ KG (L.ksb s0) b) (hrs : RS s0 s') :
    XSFC st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R s0 s' := by
  have h' := XS.capw h.xs hw fun b hb => (hB b hb).1
  exact ⟨h'.1, h'.2.1, (h.2.2.1.trans hw).mono (fun b hb => hb.elim id fun hb => Or.inr (Or.inl (hB b hb))),
    hrs, h.2.2.2.2⟩

/-- A write of an SC's `CONSUMED` word. -/
theorem XSFC.consumed {s0 s : S} {c v : U64} (h : XSFC st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R s0 s) (hc : c ∈ Scs) :
    XSFC st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R s0 (L.wr s (core.num.U64.wrapping_add c layout.sc.CONSUMED) v) := by
  have h' := XS.consumed (v := v) h.xs hc
  have hal := (consW_in h.1.2.2.1.1 hc).1
  have hin : XferConsW Scs (core.num.U64.wrapping_add c layout.sc.CONSUMED) := ⟨c, hc, rfl⟩
  exact ⟨h'.1, h'.2.1, (h.2.2.1.trans (writesIn_wr (v := v) hal)).mono (fun b hb =>
    hb.elim id fun e => Or.inr (Or.inr (e ▸ hin))),
    h.2.2.2.2 _ _ h.rs ((writesIn_wr (v := v) hal).mono fun b e => Or.inr (e ▸ hin)), h.2.2.2.2⟩

theorem obj.Tcb.set_reg.xsfc {s0 s : S} {y r v : U64} (h : XSFC st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R s0 s) (hy : y ∈ T)
    (hr : r.val < 384) :
    obj.Tcb.set_reg st y s r v ⦃ s' => XSFC st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R s0 s' ⦄ := by
  have hT := h.1.1.tcbs
  refine WP.spec_mono (obj.Tcb.set_reg.wrK s y r v (hT y hy) hr) fun s' ⟨K, hK, e⟩ => ?_
  subst e
  exact h.foot ((writesIn_wr (field_aligned (hT y hy) (by omega) (by omega))).mono fun b e =>
    Or.inl ⟨y, hy, K, by omega, by omega, by omega, e⟩)

theorem msg.buf_set.xsfc {s0 s : S} {buf i v : U64} (h : XSFC st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R s0 s)
    (hb : BufOK U buf) (h0 : buf ≠ 0#u64) (hi : i.val < 128) :
    msg.buf_set st s buf i v ⦃ s' => XSFC st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R s0 s' ⦄ := by
  unfold msg.buf_set
  simp only [lift, bind_ok]
  refine WP.spec_mono (LawfulStore.write_spec s _ v) fun s' e => ?_
  subst e
  have hu := hb h0 i hi
  exact h.foot ((writesIn_wr (h.1.2.2.2.2.2 _ hu).1.1).mono fun b e => Or.inr (e ▸ hu))

theorem msg.buf_set.rwC {s0 s : S} {buf i v : U64} (h : XSFC st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R s0 s)
    (hb : BufOK U buf) (h0 : buf ≠ 0#u64) (hi : i.val < 128) :
    msg.buf_set st s buf i v ⦃ s' => WritesIn st s s' (XferRegW T U) ⦄ := by
  unfold msg.buf_set
  simp only [lift, bind_ok]
  refine WP.spec_mono (LawfulStore.write_spec s _ v) fun s' e => ?_
  subst e
  have hu := hb h0 i hi
  exact (writesIn_wr (h.1.2.2.2.2.2 _ hu).1.1).mono fun b e => Or.inr (e ▸ hu)

theorem msg.set_mr.xsfc {s0 s : S} {y buf i v : U64} (h : XSFC st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R s0 s)
    (hy : y ∈ T) (hb : BufOK U buf) (hi : i.val < 127) :
    msg.set_mr st s y buf i v ⦃ r => XSFC st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R s0 r.2 ∧ r.1.val ≤ i.val + 4 ⦄ := by
  unfold msg.set_mr
  split
  · have hreg : ∀ j, msg.msg_register j ⦃ r => r.val < 384 ⦄ := fun j => by
      unfold msg.msg_register
      split; · simp [layout.reg.R10]
      split; · simp [layout.reg.R8]
      split; · simp [layout.reg.R9]
      simp [layout.reg.R15]
    refine WP.spec_bind (hreg i) fun r hr => ?_
    refine WP.spec_bind (obj.Tcb.set_reg.xsfc (v := v) h hy hr) fun s1 h1 => ?_
    try simp only [lift, bind_ok]
    refine (WP.spec_ok _).2 ⟨h1, ?_⟩
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  · split
    · rename_i hne
      have h0 : buf ≠ 0#u64 := by simpa using hne
      simp only [lift, bind_ok]
      have hi1 : (core.num.U64.wrapping_add i 1#u64).val < 128 := by
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
      refine WP.spec_bind (msg.buf_set.xsfc (v := v) h hb h0 hi1) fun s1 h1 => ?_
      refine (WP.spec_ok _).2 ⟨h1, ?_⟩
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    · exact (WP.spec_ok _).2 ⟨h, by simp [msg.N_MSG_REGISTERS]⟩

theorem msg.copy_mrs_loop0.xsfc {s0 s : S} {snd rcv n i : U64} (h : XSFC st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R s0 s)
    (hr : rcv ∈ T) :
    msg.copy_mrs_loop0 st s snd rcv n i ⦃ r => XSFC st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R s0 r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold msg.copy_mrs_loop0
  apply loop.spec_decr_nat (measure := fun y => 4 - y.2.val)
    (inv := fun y => XSFC st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R s0 y.1)
  · rintro ⟨s1, i1⟩ h1
    simp only at h1
    dsimp only
    unfold msg.copy_mrs_loop0.body
    split
    · split
      · rename_i _ hi
        have hi' : i1.val < 4 := by simpa [msg.N_MSG_REGISTERS] using hi
        refine WP.spec_bind (msg.msg_register.lt i1) fun rg hrg => ?_
        refine WP.spec_bind (P0.obj.Tcb.reg.p0 st snd s1 rg hS) fun v _ => ?_
        refine WP.spec_bind (obj.Tcb.set_reg.xsfc (v := v) h1 hr hrg) fun s2 h2 => ?_
        step as ⟨i2, hi2⟩
        exact ⟨h2, by first | omega | (dsimp only; omega)⟩
      · exact (WP.spec_ok _).2 h1
    · exact (WP.spec_ok _).2 h1
  · exact h

theorem msg.copy_mrs_loop1.xsfc {s0 s : S} {sb rb n i : U64} (h : XSFC st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R s0 s)
    (hb : BufOK U rb) (h0 : rb ≠ 0#u64) :
    msg.copy_mrs_loop1 st s sb rb n i ⦃ r => XSFC st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R s0 r.2 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold msg.copy_mrs_loop1
  apply loop.spec_decr_nat (measure := fun y => 120 - y.2.val)
    (inv := fun y => XSFC st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R s0 y.1)
  · rintro ⟨s1, j⟩ h1
    simp only at h1
    dsimp only
    unfold msg.copy_mrs_loop1.body
    split
    · split
      · rename_i _ hi
        have hi' : j.val < 120 := by simpa [msg.MSG_MAX_LENGTH] using hi
        step
        have hi2 := i1_post
        refine WP.spec_bind (P0.msg.buf_get.p0 st s1 sb i1 hS) fun v _ => ?_
        refine WP.spec_bind (msg.buf_set.xsfc (v := v) h1 hb h0 (by omega)) fun s2 h2 => ?_
        exact (WP.spec_ok _).2 ⟨h2, by first | omega | (dsimp only; omega)⟩
      · exact (WP.spec_ok _).2 h1
    · exact (WP.spec_ok _).2 h1
  · exact h

theorem msg.copy_mrs.xsfc {s0 s : S} {snd sb rcv rb n : U64} (h : XSFC st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R s0 s)
    (hr : rcv ∈ T) (hb : BufOK U rb) :
    msg.copy_mrs st s snd sb rcv rb n ⦃ r => XSFC st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R s0 r.2 ⦄ := by
  unfold msg.copy_mrs
  refine WP.spec_bind (msg.copy_mrs_loop0.xsfc (snd := snd) (n := n) (i := 0#u64) h hr) ?_
  rintro ⟨s1, i⟩ h1
  simp only at h1
  try simp only [WP.uncurry'_pair]
  split
  · exact (WP.spec_ok _).2 h1
  split
  · exact (WP.spec_ok _).2 h1
  rename_i h0 _
  exact msg.copy_mrs_loop1.xsfc h1 hb h0

theorem faults.copy_mrs_fault_loop0.xsfc {s0 s : S} {snd rcv : U64} {regs : Slice U64} {i : Usize}
    (h : XSFC st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R s0 s) (hr : rcv ∈ T) (hi : i.val ≤ (Slice.len regs).val) :
    faults.copy_mrs_fault_loop0 st s snd rcv regs i ⦃ r => XSFC st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R s0 r.1 ∧
      r.2.val ≤ (Slice.len regs).val ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold faults.copy_mrs_fault_loop0
  apply loop.spec_decr_nat (measure := fun y => (Slice.len regs).val - y.2.val)
    (inv := fun y => XSFC st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R s0 y.1 ∧ y.2.val ≤ (Slice.len regs).val)
  · rintro ⟨s1, j⟩ ⟨h1, hj1⟩
    simp only at h1 hj1
    dsimp only
    unfold faults.copy_mrs_fault_loop0.body
    dsimp only
    split
    · rename_i hj
      have hj' : j.val < (Slice.len regs).val := by simpa using hj
      simp only [lift, bind_ok]
      split
      · step with Aeneas.Std.Slice.index_usize_spec as ⟨r0, _⟩
        refine WP.spec_bind (P0.obj.Tcb.reg.p0 st snd s1 r0 hS) fun v _ => ?_
        refine WP.spec_bind (msg.msg_register.lt _) fun rg hrg => ?_
        refine WP.spec_bind (obj.Tcb.set_reg.xsfc (v := v) h1 hr hrg) fun s2 h2 => ?_
        step as ⟨j2, hj2⟩
        exact ⟨h2, by omega, by omega⟩
      · exact (WP.spec_ok _).2 ⟨h1, hj1⟩
    · rename_i hj
      exact (WP.spec_ok _).2 ⟨h1, hj1⟩
  · exact ⟨h, hi⟩

theorem faults.copy_mrs_fault_loop1.xsfc {s0 s : S} {snd buf : U64} {regs : Slice U64} {i : Usize}
    (h : XSFC st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R s0 s) (hb : BufOK U buf) (h0 : buf ≠ 0#u64)
    (hl : (Slice.len regs).val < 127) :
    faults.copy_mrs_fault_loop1 st s snd regs buf i ⦃ s' => XSFC st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R s0 s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold faults.copy_mrs_fault_loop1
  apply loop.spec_decr_nat (measure := fun y => (Slice.len regs).val - y.2.val)
    (inv := fun y => XSFC st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R s0 y.1)
  · rintro ⟨s1, j⟩ h1
    simp only at h1
    dsimp only
    unfold faults.copy_mrs_fault_loop1.body
    dsimp only
    split
    · rename_i hj
      have hj' : j.val < (Slice.len regs).val := by simpa using hj
      step with Aeneas.Std.Slice.index_usize_spec as ⟨r0, _⟩
      refine WP.spec_bind (P0.obj.Tcb.reg.p0 st snd s1 r0 hS) fun v _ => ?_
      simp only [lift, bind_ok]
      have hc : (UScalar.cast .U64 j).val = j.val := by
        have : 2 ^ System.Platform.numBits ≤ 2 ^ 64 := by
          rcases System.Platform.numBits_eq with e | e <;> simp [e]
        have := j.hBounds
        simp only [UScalar.cast_val_eq, UScalarTy.numBits]
        exact Nat.mod_eq_of_lt (by simp [Usize.size] at *; omega)
      have hix : (core.num.U64.wrapping_add (UScalar.cast .U64 j) 1#u64).val < 128 := by
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, hc]; omega
      refine WP.spec_bind (msg.buf_set.xsfc (v := v) h1 hb h0 hix) fun s2 h2 => ?_
      step as ⟨j2, hj2⟩
      exact ⟨h2, by omega⟩
    · exact (WP.spec_ok _).2 h1
  · exact h

theorem faults.copy_mrs_fault.xsfc {s0 s : S} {snd rcv buf : U64} {regs : Slice U64}
    (h : XSFC st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R s0 s) (hr : rcv ∈ T) (hb : BufOK U buf)
    (hl : (Slice.len regs).val < 127) :
    faults.copy_mrs_fault st s snd rcv regs buf ⦃ s' => XSFC st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R s0 s' ⦄ := by
  unfold faults.copy_mrs_fault
  refine WP.spec_bind (faults.copy_mrs_fault_loop0.xsfc (snd := snd) (regs := regs) (i := 0#usize) h hr (by simp)) ?_
  rintro ⟨s1, i⟩ ⟨h1, -⟩
  simp only at h1
  try simp only [WP.uncurry'_pair]
  split
  · rename_i hne
    exact faults.copy_mrs_fault_loop1.xsfc h1 hb (by simpa using hne) hl
  · exact (WP.spec_ok _).2 h1

theorem faults.set_mrs_lookup_failure.xsfc {s0 s : S} {rcv buf off : U64} {lf : error.LookupFault}
    (h : XSFC st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R s0 s) (hr : rcv ∈ T) (hb : BufOK U buf) (ho : off.val < 124) :
    faults.set_mrs_lookup_failure st s rcv buf lf off ⦃ r => XSFC st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R s0 r.2 ⦄ := by
  unfold faults.set_mrs_lookup_failure
  have hk : ∀ k : U64, k.val < 4 → (core.num.U64.wrapping_add off k).val < 127 := fun k hk => by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  refine WP.spec_bind (P0.error.LookupFault.type_code.p0 lf) fun i _ => ?_
  refine WP.spec_bind (msg.set_mr.xsfc (v := i) h hr hb (by omega)) ?_
  rintro ⟨i1, s1⟩ ⟨h1, -⟩
  simp only at h1
  try simp only [WP.uncurry'_pair]
  split
  · exact (WP.spec_ok _).2 h1
  · try simp only [lift, bind_ok]
    exact WP.spec_mono (msg.set_mr.xsfc h1 hr hb (hk 1#u64 (by simp))) fun r hr' => hr'.1
  · try simp only [lift, bind_ok]
    refine WP.spec_bind (msg.set_mr.xsfc h1 hr hb (hk 1#u64 (by simp))) ?_
    rintro ⟨_, s2⟩ ⟨h2, -⟩
    simp only at h2
    try simp only [WP.uncurry'_pair]
    try simp only [lift, bind_ok]
    exact WP.spec_mono (msg.set_mr.xsfc h2 hr hb (hk 2#u64 (by simp))) fun r hr' => hr'.1
  · try simp only [lift, bind_ok]
    refine WP.spec_bind (msg.set_mr.xsfc h1 hr hb (hk 1#u64 (by simp))) ?_
    rintro ⟨_, s2⟩ ⟨h2, -⟩
    simp only at h2
    try simp only [WP.uncurry'_pair]
    try simp only [lift, bind_ok]
    refine WP.spec_bind (msg.set_mr.xsfc h2 hr hb (hk 2#u64 (by simp))) ?_
    rintro ⟨_, s3⟩ ⟨h3, -⟩
    simp only at h3
    try simp only [WP.uncurry'_pair]
    try simp only [lift, bind_ok]
    exact WP.spec_mono (msg.set_mr.xsfc h3 hr hb (hk 3#u64 (by simp))) fun r hr' => hr'.1

theorem schedcontext.update_consumed.xsfc {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s0 s : S} {a : A}
    {c : U64} (h : XSFC st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R s0 s) (hc : c ∈ Scs) :
    schedcontext.update_consumed st ar s a c ⦃ r => XSFC st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R s0 r.2 ⦄ := by
  unfold schedcontext.update_consumed
  step with obj.Sc.consumed.spec as ⟨x, _hx⟩
  split
  · step as ⟨y, hy⟩
    refine WP.spec_bind (obj.Sc.set_consumed.spec' s c y) fun s1 e1 => ?_
    subst e1
    exact WP.spec_bind (hA.ticks_to_us a _) fun i _ => (WP.spec_ok _).2 (h.consumed hc)
  · refine WP.spec_bind (obj.Sc.set_consumed.spec' s c 0#u64) fun s1 e1 => ?_
    subst e1
    exact WP.spec_bind (hA.ticks_to_us a _) fun i _ => (WP.spec_ok _).2 (h.consumed hc)

/-- Some `set_mr`s in a row, ending the computation. -/
theorem set_mr_lastFC {s0 s : S} {y buf i v : U64} (h : XSFC st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R s0 s)
    (hy : y ∈ T) (hb : BufOK U buf) (hi : i.val < 127) :
    msg.set_mr st s y buf i v ⦃ r => XSFC st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R s0 r.2 ⦄ :=
  WP.spec_mono (msg.set_mr.xsfc h hy hb hi) fun _ h' => h'.1

set_option hygiene false in
/-- One `set_mr` of the receiver, from the state of `hcur`. -/
local macro "smrF" : tactic => `(tactic| (
  refine WP.spec_bind (msg.set_mr.xsfc hcur hr hb (by simp)) ?_
  rintro ⟨_, s'⟩ ⟨hcur, -⟩
  try simp only at hcur
  try simp only [WP.uncurry'_pair]))

theorem faults.set_mrs_fault.xsfc {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s : S} {a : A}
    {snd rcv buf : U64} (h : XSFC st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R s s) (hs : snd ∈ T) (hr : rcv ∈ T)
    (hb : BufOK U buf) :
    faults.set_mrs_fault st ar s a snd rcv buf ⦃ r => XSFC st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R s r.2 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold faults.set_mrs_fault
  refine WP.spec_bind (P0.obj.Tcb.fault_type.p0 st snd s hS) fun ty _ => ?_
  refine WP.spec_bind (P0.obj.Tcb.fault_w0.p0 st snd s hS) fun w0 _ => ?_
  refine WP.spec_bind (P0.obj.Tcb.fault_w1.p0 st snd s hS) fun w1 _ => ?_
  refine WP.spec_bind (P0.obj.Tcb.fault_w2.p0 st snd s hS) fun w2 _ => ?_
  refine WP.spec_bind (P0.obj.Tcb.reg.p0 st snd s _ hS) fun pc _ => ?_
  have hcur := h
  split
  · smrF; smrF; smrF
    refine WP.spec_bind (P0.faults.lookup_failure.p0 st s' snd hS) fun lf _ => ?_
    exact faults.set_mrs_lookup_failure.xsfc hcur hr hb (by simp)
  split
  · try simp only [lift, bind_ok]
    refine WP.spec_bind (faults.copy_mrs_fault.xsfc (snd := snd) h hr hb (by simp [faults.SYSCALL_MESSAGE])) fun s2 h2 => ?_
    exact set_mr_lastFC h2 hr hb (by simp)
  split
  · try simp only [lift, bind_ok]
    refine WP.spec_bind (faults.copy_mrs_fault.xsfc (snd := snd) h hr hb (by simp [faults.EXCEPTION_MESSAGE]))
      fun s2 hcur => ?_
    smrF
    exact set_mr_lastFC hcur hr hb (by simp)
  split
  · step with obj.Tcb.sc.spec as ⟨c, hc⟩
    simp only [obj.Sc.is_null, bind_ok]
    split
    · exact set_mr_lastFC h hr hb (by simp)
    rename_i hne
    have hc0 : L.mem s (scA snd) ≠ 0#u64 := by rw [← hc]; simpa using hne
    have hcS : c ∈ Scs := hc ▸ (h.1.2.2.1.2.2.bound snd hs hc0).1
    refine WP.spec_bind (schedcontext.update_consumed.xsfc hA h hcS) ?_
    rintro ⟨cons, s1⟩ h1
    simp only at h1
    try simp only [WP.uncurry'_pair]
    refine WP.spec_bind (msg.set_mr.xsfc h1 hr hb (by simp)) ?_
    rintro ⟨len, s2⟩ ⟨h2, hl2⟩
    simp only at h2 hl2
    try simp only [WP.uncurry'_pair]
    exact set_mr_lastFC h2 hr hb (by simp at hl2; omega)
  split
  · smrF
    refine WP.spec_bind (msg.set_mr.xsfc hcur hr hb (by simp)) ?_
    rintro ⟨ret, s2⟩ ⟨hcur, -⟩
    simp only at hcur
    try simp only [WP.uncurry'_pair]
    split
    · split
      · smrF
        exact set_mr_lastFC hcur hr hb (by simp)
      · exact (WP.spec_ok _).2 hcur
    · exact (WP.spec_ok _).2 hcur
  split
  · smrF; smrF; smrF
    exact set_mr_lastFC hcur hr hb (by simp)
  · exact (WP.spec_ok _).2 h

theorem ipc.do_fault_transfer.xsfc {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s : S} {a : A}
    {badge snd rcv rb : U64} (h : XSFC st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R s s) (hs : snd ∈ T) (hr : rcv ∈ T)
    (hb : BufOK U rb) :
    ipc.do_fault_transfer st ar s a badge snd rcv rb ⦃ s' => XSFC st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R s s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold ipc.do_fault_transfer
  refine WP.spec_bind (faults.set_mrs_fault.xsfc hA h hs hr hb) ?_
  rintro ⟨sent, s1⟩ h1
  simp only at h1
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (P0.obj.Tcb.fault_type.p0 st snd s1 hS) fun ft _ => ?_
  refine WP.spec_bind (P0.msginfo.MessageInfo.new.p0 _ _ _ _) fun mi _ => ?_
  refine WP.spec_bind (Pₘ := fun s3 => XSFC st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R s s3) ?_
    fun s3 h3 => obj.Tcb.set_reg.xsfc h3 hr (by simp [layout.reg.BADGE, layout.reg.RDI])
  unfold msg.set_msg_info
  exact WP.spec_bind (P0.msginfo.MessageInfo.to_word.p0 _) fun w _ =>
    obj.Tcb.set_reg.xsfc (v := w) h1 hr (by simp [layout.reg.MSG_INFO, layout.reg.RSI])



/-- **The message transfer's footprint with only `CONSUMED` among SC words**:
`do_ipc_transfer` writes in `XferWC` (P1's `XferFootOK` with `XferWC`).
**[J]**: taken as a named premise by its users (module docstring, p2j8). -/
def XferFootOKC (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) (RS : S → S → Prop)
    (G : S → Prop) : Prop :=
  ∀ (Ac X : Set U64) (Q : U64 → U64 → List U64) (R : U64 → List U64) (s : S) (a : A) (snd ep badge : U64)
    (grant : Bool) (rcv : U64), snd ∈ T → rcv ∈ T →
    SchedQueuesInvX st T Cs Ω H X s Q R → BoundInv st T Ac s → XInv st T Cs Ω Sg Rp Scs Nt Z s →
    SCsOK st T Ω Sg Scs Z Ac s → SgOK st Ω Sg s → UserOK st T Cs Ω H U s → RS s s → G s →
    ipc.do_ipc_transfer st ar s a snd ep badge grant rcv ⦃ s' =>
      WritesIn st s s' (XferWC T U Ω Sg Scs (L.ksb s)) ∧ RS s s' ⦄

/-- `XferFootOKC` gives P1's `XferFootOK`. -/
theorem XferFootOKC.foot {A : Type _} {ar : machine.Arch A} {G : S → Prop}
    (h : XferFootOKC st ar T Cs Ω H Sg Rp Scs Nt Z U RS G) : XferFootOK st ar T Cs Ω H Sg Rp Scs Nt Z U RS G := by
  intro Ac X Q R s a snd ep badge grant rcv hs hr h0 hB hX hS hSg hU hrs hG0
  exact WP.spec_mono (h Ac X Q R s a snd ep badge grant rcv hs hr h0 hB hX hS hSg hU hrs hG0) fun s' h' =>
    ⟨h'.1.mono fun _ hb => hb.imp id (Or.imp id fun ⟨c, hc, e⟩ => ⟨c, hc, e ▸ (consW_in hX.1 hc).2⟩), h'.2⟩

end

end Fl4Proofs.P1
