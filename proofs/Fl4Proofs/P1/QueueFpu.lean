/-
P1's half of P3's `FpuHyp`: `fpu_transfer` (l4h ReadFPU/WriteFPU) keeps
`BlkOK`; after the caller's restart it writes only the target's FPU area (TCB
fields at offsets 512 to 3208) or the frame's words (`FpuFrameOK`, user
words for `UserOK`).  The P3 side shows those words are no slot words.
-/
import Fl4Proofs.P1.QueueCbs
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-- The `n` words from `dst`. -/
def CWW (dst n : U64) (b : U64) : Prop := ∃ k : Nat, k < n.val ∧ b.val = dst.val + 8 * k

theorem tcb.copy_words_loop.w (s : S) (src dst n i : U64) (hd : Aligned dst) (hfit : dst.val + 8 * n.val ≤ 2 ^ 64) :
    tcb.copy_words_loop st s src dst n i ⦃ s' => WritesIn st s s' (CWW dst n) ⦄ := by
  unfold tcb.copy_words_loop
  apply loop.spec_decr_nat (measure := fun x => n.val - x.2.val) (inv := fun x => WritesIn st s x.1 (CWW dst n))
  · rintro ⟨s1, j⟩ w1
    simp only at w1
    dsimp only
    unfold tcb.copy_words_loop.body
    split
    · rename_i hi
      have hi' : j.val < n.val := by simpa using hi
      step*
      have hv : i4.val = dst.val + 8 * j.val := by
        rw [i4_post, i3_post]
        simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]
        omega
      have ha : Aligned i4 := by unfold Aligned at hd ⊢; rw [hv]; omega
      subst s1_post
      refine ⟨(w1.trans (writesIn_wr ha)).mono fun b hb => hb.elim id fun e => ⟨j.val, hi', by rw [e, hv]⟩, ?_⟩
      omega
    · exact (WP.spec_ok _).2 w1
  · exact WritesIn.refl _ _

/-- The frame's 337 words (`FPU_STATE_SIZE` rounded up) are user words. -/
def FpuFrameOK (U : Set U64) (f : U64) : Prop := Aligned f ∧ f.val + 8 * 337 ≤ 2 ^ 64 ∧ ∀ b, CWW f 337#u64 b → b ∈ U

theorem fpu_area_xfer {t b : U64} (hT : TcbPlaced T) (ht : t ∈ T) {U : Set U64}
    (hb : CWW (core.num.U64.wrapping_add t layout.tcb.FPU) 337#u64 b) : XferFoot T U b := by
  obtain ⟨k, hk, e⟩ := hb
  have hv := field_val (hT t ht) (K := layout.tcb.FPU) (by simp [layout.tcb.FPU])
  have hk' : k < 337 := by simpa using hk
  let K : U64 := ⟨BitVec.ofNat 64 (512 + 8 * k)⟩
  have hK : K.val = 512 + 8 * k := by
    show (BitVec.ofNat 64 (512 + 8 * k)).toNat = _
    simp; omega
  refine Or.inl ⟨t, ht, K, by omega, by omega, UScalar.eq_of_val_eq ?_⟩
  rw [e, hv, field_val (hT t ht) (by omega), hK]; simp [layout.tcb.FPU]; omega

/-- The work of `fpu_transfer` after its checks. -/
theorem fpu_tail {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (target : obj.Tcb) (ptr offset : U64) (tf : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : target ∈ T)
    (hnb : ¬ Blocked (L.mem s (stA (L.curW s)))) (hnr : L.mem s (stA (L.curW s)) ≠ sched.TS_BLOCKED_ON_REPLY)
    {U : Set U64} (hU : UserOK st T Cs Ω H U s) (hF : FpuFrameOK U (core.num.U64.wrapping_add ptr offset)) :
    (do
      let s1 ← tcb.restart_caller st s
      let a1 ← ar.fpu_flush a target
      let i4 ← fl4_abi.consts.FPU_STATE_SIZE + 7#u64
      let words ← i4 / 8#u64
      let frame ← lift (core.num.U64.wrapping_add ptr offset)
      if tf
      then
        let i5 ← obj.Tcb.fpu_addr target
        let s2 ← tcb.copy_words st s1 i5 frame words
        if tf
        then ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a1)
        else
          let a2 ← ar.fpu_sanitise a1 target
          let a3 ← ar.fpu_reload a2 target
          ok (core.result.Result.Ok (), s2, a3)
      else
        let i5 ← obj.Tcb.fpu_addr target
        let s2 ← tcb.copy_words st s1 frame i5 words
        if tf
        then ok (core.result.Result.Ok (), s2, a1)
        else
          let a2 ← ar.fpu_sanitise a1 target
          let a3 ← ar.fpu_reload a2 target
          ok (core.result.Result.Ok (), s2, a3)) ⦃ res => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac res.2.1 ∧
      (res.2.1 = s ∨ ∃ s1, tcb.restart_caller st s = ok s1 ∧ WritesIn st s1 res.2.1 (XferFoot T U)) ⦄ := by
  have hT := h.1.choose_spec.choose_spec.tcbs
  have R := tcb.restart_caller.blk (Es := ∅) s h hnb hnr
  cases hr : tcb.restart_caller st s with
  | vis e k => rw [hr] at R; exact absurd R (by rw [WP.spec_vis]; exact id)
  | div => rw [hr] at R; exact absurd R (by rw [WP.spec_div]; exact id)
  | ret s1 =>
  rw [hr] at R
  replace R := (WP.spec_ok (p := fun s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      Foot st T Cs Sg Scs Z ∅ s s' ∧ L.mem s' (stA (L.curW s)) = sched.TS_RESTART ∧
      KeepT st T Cs Rp Scs Nt (L.curW s) s s') s1).1 R
  obtain ⟨hb1, -, -, k1⟩ := R
  have hU1 : UserOK st T Cs Ω H U s1 := hU.ksb k1.ksb
  simp only [bind_ok]
  refine WP.spec_bind (hA.fpu_flush a target) fun a1 _ => ?_
  step as ⟨i4, hi4⟩
  step as ⟨words, hw⟩
  have hw' : words = 337#u64 := by
    apply UScalar.eq_of_val_eq; simp [fl4_abi.consts.FPU_STATE_SIZE] at hi4; simp at hw ⊢; omega
  subst hw'
  simp only [lift, bind_ok, obj.Tcb.fpu_addr]
  have hta := hT target ht
  have hfv := field_val hta (K := layout.tcb.FPU) (by simp [layout.tcb.FPU])
  have hfa : Aligned (core.num.U64.wrapping_add target layout.tcb.FPU) := by
    unfold Aligned; rw [hfv]; have := hta.align; simp [layout.tcb.FPU]; omega
  have hff : (core.num.U64.wrapping_add target layout.tcb.FPU).val + 8 * (337#u64 : U64).val ≤ 2 ^ 64 := by
    rw [hfv]; have := hta.fits; simp [layout.tcb.FPU]; omega
  have fin : ∀ s2 : S, WritesIn st s1 s2 (XferFoot T U) →
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s2 ∧ (s2 = s ∨ WritesIn st s1 s2 (XferFoot T U)) :=
    fun s2 w2 => by
      obtain ⟨⟨Q1, R1, q1⟩, hB1, hX1, hS1, hSg1⟩ := hb1
      obtain ⟨q2, hB2, hX2, hS2, hSg2, -⟩ := xfer_all q1 hB1 hX1 hS1 hSg1 hU1 w2
      exact ⟨⟨⟨Q1, R1, q2⟩, hB2, hX2, hS2, hSg2⟩, Or.inr w2⟩
  cases tf
  · simp only [Bool.false_eq_true, ite_false]
    unfold tcb.copy_words
    refine WP.spec_bind (tcb.copy_words_loop.w s1 _ _ _ 0#u64 hfa hff) fun s2 w2 => ?_
    have w2' : WritesIn st s1 s2 (XferFoot T U) := w2.mono fun b hb => fpu_area_xfer hT ht hb
    refine WP.spec_bind (hA.fpu_sanitise a1 target) fun a2 _ => ?_
    refine WP.spec_bind (hA.fpu_reload a2 target) fun a3 _ => ?_
    exact (WP.spec_ok _).2 (fin s2 w2')
  · simp only [ite_true]
    unfold tcb.copy_words
    refine WP.spec_bind (tcb.copy_words_loop.w s1 _ _ _ 0#u64 hF.1 hF.2.1) fun s2 w2 => ?_
    have w2' : WritesIn st s1 s2 (XferFoot T U) := w2.mono fun b hb => Or.inr (hF.2.2 b hb)
    exact (WP.spec_ok _).2 (fin s2 w2')

/-- `fpu_transfer`'s size and offset checks, around the work `K`. -/
theorem fpu_chk {A : Type _} (s : S) (a : A) (sz : capability.FrameSize) (offset : U64)
    {Q : (core.result.Result Unit error.Exc) × S × A → Prop}
    (K : Result ((core.result.Result Unit error.Exc) × S × A)) (hK : K ⦃ Q ⦄)
    (herr : ∀ r, Q (r, s, a)) :
    (do
      let i ← capability.FrameSize.bits sz
      let i1 ← lift (i &&& 63#u64)
      let size1 ← 1#u64 <<< i1
      let i2 ← offset % 64#u64
      if i2 != 0#u64
      then let r ← error.invalid_arg Unit 0#u64
           ok (r, s, a)
      else
        if offset >= size1
        then let r ← error.invalid_arg Unit 0#u64
             ok (r, s, a)
        else
          let i3 ← size1 - offset
          if i3 < fl4_abi.consts.FPU_STATE_SIZE
          then let r ← error.invalid_arg Unit 0#u64
               ok (r, s, a)
          else K) ⦃ Q ⦄ := by
  have E : ∀ (m : Result (core.result.Result Unit error.Exc)), m ⦃ _ => True ⦄ →
      (do let r ← m; ok (r, s, a)) ⦃ Q ⦄ := fun m hm => WP.spec_bind hm fun r _ => (WP.spec_ok _).2 (herr r)
  refine WP.spec_bind (P0.capability.FrameSize.bits.p0 sz) fun i _ => ?_
  step*
  all_goals first | exact E _ (P0.error.invalid_arg.p0 _ _) | exact hK | skip

theorem tcb.fpu_transfer.blk {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (target : obj.Tcb) (c : tcb.Ctx) (tf : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : target ∈ T)
    (hnb : ¬ Blocked (L.mem s (stA (L.curW s)))) (hnr : L.mem s (stA (L.curW s)) ≠ sched.TS_BLOCKED_ON_REPLY)
    {U : Set U64} (hU : UserOK st T Cs Ω H U s)
    (hfr : tcb.extra c 0#usize ⦃ o => ∀ x, o = some x → tcb.arg st s c 0#u64 ⦃ off =>
      obj.Slot.cap st x s ⦃ cp => ∀ ptr sz r d m ep asid va, cp = .Frame ptr sz r d m ep asid va →
        FpuFrameOK U (core.num.U64.wrapping_add ptr off) ⦄ ⦄ ⦄) :
    tcb.fpu_transfer st ar s a target c tf ⦃ res => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac res.2.1 ∧
      (res.2.1 = s ∨ ∃ s1, tcb.restart_caller st s = ok s1 ∧ WritesIn st s1 res.2.1 (XferFoot T U)) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hT := h.1.choose_spec.choose_spec.tcbs
  unfold tcb.fpu_transfer
  have E : ∀ (m : Result (core.result.Result Unit error.Exc)), m ⦃ _ => True ⦄ →
      (do let r ← m; ok (r, s, a)) ⦃ res => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac res.2.1 ∧
        (res.2.1 = s ∨ ∃ s1, tcb.restart_caller st s = ok s1 ∧ WritesIn st s1 res.2.1 (XferFoot T U)) ⦄ :=
    fun m hm => WP.spec_bind hm fun _ _ => (WP.spec_ok _).2 ⟨h, Or.inl rfl⟩
  refine WP.spec_bind hfr fun o ho => ?_
  rcases o with _ | x
  · exact E _ (P0.error.truncated.p0 _)
  show (if c.length >= 1#u64 then _ else _) ⦃ _ ⦄
  by_cases hl : c.length >= 1#u64
  swap
  · rw [if_neg hl]; exact E _ (P0.error.truncated.p0 _)
  rw [if_pos hl]
  refine WP.spec_bind (ho x rfl) fun off hoff => ?_
  refine WP.spec_bind hoff fun cp hcp => ?_
  cases cp
  all_goals first | exact E _ (P0.error.invalid_cap.p0 _ _) | skip
  rename_i ptr sz r d m ep asid va
  have hF := hcp ptr sz r d m ep asid va rfl
  show (if d = true then _ else _) ⦃ _ ⦄
  by_cases hd : d = true
  · rw [if_pos hd]; exact E _ (P0.error.invalid_cap.p0 _ _)
  rw [if_neg hd]
  show (if r = capability.VM_KERNEL_ONLY then _ else _) ⦃ _ ⦄
  by_cases hk : r = capability.VM_KERNEL_ONLY
  · rw [if_pos hk]; exact E _ (P0.error.invalid_cap.p0 _ _)
  rw [if_neg hk]
  have hTail := fpu_tail hA s a target ptr off tf h ht hnb hnr hU hF
  have herr : ∀ x : core.result.Result Unit error.Exc, BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac (x, s, a).2.1 ∧
      ((x, s, a).2.1 = s ∨ ∃ s1, tcb.restart_caller st s = ok s1 ∧ WritesIn st s1 (x, s, a).2.1 (XferFoot T U)) :=
    fun _ => ⟨h, Or.inl rfl⟩
  cases tf
  · show (if false = true then _ else _) ⦃ _ ⦄
    rw [if_neg (by simp)]
    exact fpu_chk s a sz off _ hTail herr
  · show (if true = true then _ else _) ⦃ _ ⦄
    rw [if_pos rfl]
    show (if (r != capability.VM_READ_WRITE) = true then _ else _) ⦃ _ ⦄
    by_cases hrw : (r != capability.VM_READ_WRITE) = true
    · rw [if_pos hrw]; exact E _ (P0.error.invalid_cap.p0 _ _)
    · rw [if_neg hrw]; exact fpu_chk s a sz off _ hTail herr

end

end Fl4Proofs.P1
