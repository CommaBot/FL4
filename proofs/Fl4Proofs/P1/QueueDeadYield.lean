/-
P1: **the yielder's `complete_yield_to` clears the SC's `YIELD_FROM` word**
(for the SC finalisation's dead SC, P3's `DeadP`): when the yielder `y`'s
`YIELD_TO` word names the SC `p` (the yield links' symmetry, which P1 does
not track: P3's `YieldRel.frm` gives it), `complete_yield_to y` leaves
`p`'s `YIELD_FROM` word null.  `set_consumed` writes an SC word and the
thread's registers (`RgWd`), so it keeps every `YIELD_TO` word
(`set_consumed.ykeep`); `cancel_yield_to y` then clears `p`'s word.
-/
import Fl4Proofs.P1.QueueYield
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}
variable {A : Type _} {ar : machine.Arch A}

/-- An `Ω` word or a register word of a thread. -/
def RgWd (T Ω : Set U64) (b : U64) : Prop :=
  b ∈ Ω ∨ ∃ y ∈ T, ∃ K : U64, 256 ≤ K.val ∧ K.val < 3328 ∧ K.val % 8 = 0 ∧ b = core.num.U64.wrapping_add y K

theorem rgw_trans {s₁ s₂ s₃ : S} (h₁ : WritesIn st s₁ s₂ (RgWd T Ω)) (h₂ : WritesIn st s₂ s₃ (RgWd T Ω)) :
    WritesIn st s₁ s₃ (RgWd T Ω) := (h₁.trans h₂).mono fun _ hb => hb.elim id id

/-- `RgWd` writes keep every thread's `YIELD_TO` word. -/
theorem rgw_keepY {X : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hw : WritesIn st s s' (RgWd T Ω)) :
    ∀ y ∈ T, L.mem s' (yieldA y) = L.mem s (yieldA y) := by
  have hT := h.tcbs
  intro y hy
  refine hw.mem_eq (field_aligned (K := 3472#u64) (hT y hy) (by simp) (by simp)) fun hb => ?_
  rcases hb with hm | ⟨z, hz, K, hK1, hK2, -, e⟩
  · exact out_ne_field (h.omega _ hm) hy (hT y hy) (K := 3472#u64) (by simp) rfl
  · exact field_ne (hT y hy) (hT z hz) (K1 := 3472#u64) (by simp) (by omega) (fun _ => by have : (3472#u64).val = 3472 := rfl; omega) e

theorem reg_rgw {s : S} {t r v : U64} (hT : TcbPlaced T) (ht : t ∈ T) (hr : r.val < 384) :
    obj.Tcb.set_reg st t s r v ⦃ s' => WritesIn st s s' (RgWd T Ω) ⦄ :=
  WP.spec_mono (obj.Tcb.set_reg.wrK s t r v (hT t ht) hr) fun s' ⟨K, hK, e⟩ => by
    subst e
    exact (writesIn_wr (field_aligned (hT t ht) (by omega) (by omega))).mono fun b e =>
      Or.inr ⟨t, ht, K, by omega, by omega, by omega, e⟩

theorem schedcontext.update_consumed.rg {s : S} {a : A} {c : U64} (hA : P0.ArchTotal ar)
    (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hc : c ∈ Scs) :
    schedcontext.update_consumed st ar s a c ⦃ r => WritesIn st s r.2 (RgWd T Ω) ⦄ := by
  obtain ⟨hP, hz⟩ := hO.sc c hc
  obtain ⟨c8, c128, cfit⟩ := sc_lo hP hz
  have hv : (core.num.U64.wrapping_add c layout.sc.CONSUMED).val = c.val + layout.sc.CONSUMED.val := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, layout.sc.CONSUMED]; omega
  have ho : layout.sc.CONSUMED.val < 128 ∧ layout.sc.CONSUMED.val % 8 = 0 := by simp [layout.sc.CONSUMED]
  have ha : Aligned (core.num.U64.wrapping_add c layout.sc.CONSUMED) := by unfold Aligned; rw [hv]; omega
  have hw : RgWd T Ω (core.num.U64.wrapping_add c layout.sc.CONSUMED) :=
    Or.inl (hO.scW c hc _ ha ⟨by rw [hv]; omega, by rw [hv]; omega⟩)
  unfold schedcontext.update_consumed
  step with obj.Sc.consumed.spec as ⟨x, _hx⟩
  split
  · step as ⟨y, hy⟩
    refine WP.spec_bind (obj.Sc.set_consumed.spec' s c y) fun s1 e1 => ?_
    subst e1
    exact WP.spec_bind (hA.ticks_to_us a _) fun i _ =>
      (WP.spec_ok _).2 ((writesIn_wr ha).mono fun b e => by rw [e]; exact hw)
  · refine WP.spec_bind (obj.Sc.set_consumed.spec' s c 0#u64) fun s1 e1 => ?_
    subst e1
    exact WP.spec_bind (hA.ticks_to_us a _) fun i _ =>
      (WP.spec_ok _).2 ((writesIn_wr ha).mono fun b e => by rw [e]; exact hw)

theorem schedcontext.set_consumed.rg (hA : P0.ArchTotal ar) (s : S) (a : A) (c t : U64) (wm : Bool)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hc : c ∈ Scs) (ht : t ∈ T) :
    schedcontext.set_consumed st ar s a c t wm ⦃ s' => WritesIn st s s' (RgWd T Ω) ⦄ := by
  have hT := h.1.choose_spec.choose_spec.tcbs
  unfold schedcontext.set_consumed
  refine WP.spec_bind (schedcontext.update_consumed.rg (T := T) hA h.2.2.1.1 hc) ?_
  rintro ⟨x, s1⟩ w1
  simp only at w1
  try simp only [WP.uncurry'_pair]
  split
  · refine WP.spec_bind (P0.msg.lookup_ipc_buffer.p0 st s1 true t L.total) fun buf _ => ?_
    refine WP.spec_bind (reg_rgw (Ω := Ω) (r := layout.reg.BADGE) hT ht (by simp [layout.reg.BADGE, layout.reg.RDI]))
      fun s2 w2 => ?_
    unfold msg.set_mr
    simp only [show (0#u64 < msg.N_MSG_REGISTERS) = True from by simp [msg.N_MSG_REGISTERS], if_true]
    simp only [msg.msg_register, if_true, Aeneas.Std.bind_ok]
    refine WP.spec_bind (Pₘ := fun r : U64 × S => WritesIn st s2 r.2 (RgWd T Ω)) ?_ ?_
    · refine WP.spec_bind (reg_rgw (Ω := Ω) (r := layout.reg.R10) hT ht (by simp [layout.reg.R10])) fun s3 hh => ?_
      simp only [lift, Aeneas.Std.bind_ok, WP.spec_ok]; exact hh
    rintro ⟨len, s3⟩ w3
    simp only at w3
    try simp only [WP.uncurry'_pair]
    unfold msginfo.MessageInfo.new msg.set_msg_info
    simp only [Aeneas.Std.bind_ok]
    refine WP.spec_bind (P0.msginfo.MessageInfo.to_word.p0 _) fun w _ => ?_
    exact WP.spec_mono (reg_rgw (Ω := Ω) (r := layout.reg.MSG_INFO) hT ht (by simp [layout.reg.MSG_INFO, layout.reg.RSI]))
      fun s4 w4 => rgw_trans w1 (rgw_trans w2 (rgw_trans w3 w4))
  · exact (WP.spec_ok _).2 w1

/-- **`set_consumed` keeps every `YIELD_TO` word.** -/
theorem schedcontext.set_consumed.ykeep (hA : P0.ArchTotal ar) (s : S) (a : A) (c t : U64) (wm : Bool)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hc : c ∈ Scs) (ht : t ∈ T) :
    schedcontext.set_consumed st ar s a c t wm ⦃ s' => ∀ y ∈ T, L.mem s' (yieldA y) = L.mem s (yieldA y) ⦄ :=
  WP.spec_mono (schedcontext.set_consumed.rg hA s a c t wm h hc ht) fun _ w =>
    rgw_keepY h.1.choose_spec.choose_spec w

/-- **`cancel_yield_to t` clears the `YIELD_FROM` word of the SC `t` yields to.** -/
theorem schedcontext.cancel_yield_to.yfZ (s : S) (t p : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (ht : t ∈ T) (htp : L.mem s (yieldA t) = p) (hp0 : p ≠ 0#u64) :
    schedcontext.cancel_yield_to st s t ⦃ s' => L.mem s' (scYieldFromA p) = 0#u64 ⦄ := by
  have h0 := h.1.choose_spec.choose_spec
  have hT := h0.tcbs
  unfold schedcontext.cancel_yield_to
  step with obj.Tcb.is_null.spec as ⟨b, b_post⟩
  split
  · rename_i hb
    have e0 : t = 0#u64 := by rw [b_post] at hb; simpa using hb
    exact absurd (show t.val = 0 by rw [e0]; rfl) (hT t ht).ne0
  step with obj.Tcb.yield_to.spec as ⟨yt, yt_post⟩
  have hyp : yt = p := by rw [yt_post, htp]
  split
  · have hyS : L.mem s (yieldA t) ∈ Scs := h.2.2.1.2.2.yt.2.1 t ht (by rw [htp]; exact hp0)
    rw [htp] at hyS
    have hm : scYieldFromA p ∈ Ω := h.2.2.2.2.sub _ (h.2.2.1.1.syW p hyS)
    have ho := h0.omega _ hm
    step with obj.Sc.set_yield_from.spec as ⟨s5, s5_post⟩
    subst s5_post
    refine WP.spec_mono (obj.Tcb.set_yield_to.spec _ t 0#u64) fun s6 e => ?_
    subst e
    rw [hyp, show yieldA t = core.num.U64.wrapping_add t 3472#u64 from rfl, L.mem_wr_ne (field_aligned (K := 3472#u64) (hT t ht) (by simp) (by simp)) ho.1
      (out_ne_field ho ht (hT t ht) (K := 3472#u64) (by simp))]
    exact L.mem_wr_same ho.1
  · rename_i _ hy
    exact (hp0 (hyp.symm.trans (UScalar.eq_of_val_eq (by simpa using hy)))).elim

/-- **`complete_yield_to y` clears the `YIELD_FROM` word of the SC `y` yields
to** (module docstring). -/
theorem schedcontext.complete_yield_to.yfZ (hA : P0.ArchTotal ar) (s : S) (a : A) (y p : U64)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hyT : y ∈ T) (hyp : L.mem s (yieldA y) = p) (hp0 : p ≠ 0#u64) :
    schedcontext.complete_yield_to st ar s a y ⦃ r => L.mem r.1 (scYieldFromA p) = 0#u64 ⦄ := by
  have hT := h.1.choose_spec.choose_spec.tcbs
  unfold schedcontext.complete_yield_to
  step with obj.Tcb.is_null.spec as ⟨b, b_post⟩
  split
  · rename_i hb
    have e0 : y = 0#u64 := by rw [b_post] at hb; simpa using hb
    exact absurd (show y.val = 0 by rw [e0]; rfl) (hT y hyT).ne0
  step with obj.Tcb.yield_to.spec as ⟨i, ei⟩
  have hip : i = p := by rw [ei, hyp]
  subst hip
  split
  · have hiS : L.mem s (yieldA y) ∈ Scs := h.2.2.1.2.2.yt.2.1 y hyT (by rw [hyp]; exact hp0)
    rw [hyp] at hiS
    refine WP.spec_bind (WP.spec_and (schedcontext.set_consumed.blk hA s a i y true h hiS hyT)
      (schedcontext.set_consumed.ykeep hA s a i y true h hiS hyT)) fun s1 ⟨⟨h1, _, _⟩, w1⟩ => ?_
    refine WP.spec_bind (schedcontext.cancel_yield_to.yfZ s1 y i h1 hyT (by rw [w1 y hyT, hyp]) hp0)
      fun s2 w2 => ?_
    exact (WP.spec_ok _).2 w2
  · rename_i _ hi
    exact (hp0 (UScalar.eq_of_val_eq (by simpa using hi))).elim

end

end Fl4Proofs.P1
