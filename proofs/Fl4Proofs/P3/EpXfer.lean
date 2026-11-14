/-
P3 (DESIGN.md §9), endpoints: **FL4's `do_ipc_transfer` refines l4v
`do_ipc_transfer`** when the receiver has no IPC buffer, the sender has no
fault, and there are no extra caps to look up (`do_ipc_transfer_regs`): the
first `min len 4` message registers (`copy_mrs`, first loop), the message
info `⦇min len 4, 0, 0, label⦈` (`set_msg_info`; FL4's clamping of the length
to 120 is l4v's `data_to_message_info`) and the badge.

The IPC buffers are found by `lookup_ipc_buffer`, which reads the TCB's
buffer-frame cap (CSpace, not related here): `EpBufHyps.lookup` states that
FL4 finds no buffer exactly when the spec's `lookup_ipc_buffer` (as a function
of the TCB, `ipcBufOf`) does (the IPC-buffer frame-mapping hypothesis).
-/
import Fl4Proofs.P3.EpXferSpec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

/-- The `i`-th message register (msg.rs `msg_register`). -/
def mrIdx (i : Nat) : Fl4Spec.Register := Fl4Spec.msgRegisters.getD i .r15

theorem msg_register_spec (i : U64) (hi : i.val < 4) :
    msg.msg_register i ⦃ r => r = regIdx (mrIdx i.val) ⦄ := by
  unfold msg.msg_register
  by_cases h0 : i = 0#u64
  · subst h0; simp only [↓reduceIte, WP.spec_ok]; unfold layout.reg.R10; rfl
  · by_cases h1 : i = 1#u64
    · subst h1; simp only [h0, ↓reduceIte, WP.spec_ok]; unfold layout.reg.R8; rfl
    · by_cases h2 : i = 2#u64
      · subst h2; simp only [h0, h1, ↓reduceIte, WP.spec_ok]; unfold layout.reg.R9; rfl
      · simp only [h0, h1, h2, ↓reduceIte, WP.spec_ok]
        have : i.val = 3 := by
          have := val_ne_of_ne h0; have := val_ne_of_ne h1; have := val_ne_of_ne h2
          simp at *; omega
        rw [this]; unfold layout.reg.R15; rfl

theorem take_succ_mem (i : Nat) (hi : i < 4) (r : Fl4Spec.Register) :
    r ∈ Fl4Spec.msgRegisters.take (i + 1) ↔ r ∈ Fl4Spec.msgRegisters.take i ∨ r = mrIdx i := by
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;>
    simp [Fl4Spec.msgRegisters, mrIdx] <;> tauto

theorem take_four (k : Nat) (hk : 4 ≤ k) : Fl4Spec.msgRegisters.take k = Fl4Spec.msgRegisters := by
  apply List.take_of_length_le; simp [Fl4Spec.msgRegisters]; omega

theorem mrIdx_mem (i : Nat) : mrIdx i ∈ Fl4Spec.msgRegisters := by
  unfold mrIdx
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ 3 ≤ i by omega) with rfl | rfl | rfl | h
  · simp [Fl4Spec.msgRegisters]
  · simp [Fl4Spec.msgRegisters]
  · simp [Fl4Spec.msgRegisters]
  · rw [List.getD_eq_getElem?_getD]
    rcases (show i = 3 ∨ 4 ≤ i by omega) with rfl | h'
    · simp [Fl4Spec.msgRegisters]
    · rw [List.getElem?_eq_none (by simp [Fl4Spec.msgRegisters]; omega)]; simp [Fl4Spec.msgRegisters]

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T E R : Set U64} {B : Set (U64 × Fl4Spec.Word)}

/-- The receiver's message registers, as words. -/
def RcvMR (rcv b : U64) : Prop := ∃ r ∈ Fl4Spec.msgRegisters, b.val = (regA rcv (regIdx r)).val

/-- The first loop of `copy_mrs`: the first `min n 4` message registers of
the sender go to the receiver; nothing else changes. -/
theorem copy_mrs_loop0_spec (hP : EPlaced T E R B) (s : S) {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T)
    (hne : snd ≠ rcv) (n : U64) :
    msg.copy_mrs_loop0 st s snd rcv n 0#u64 ⦃ r => r.2.val = min n.val 4 ∧
      (∀ reg, L.mem r.1 (regA rcv (regIdx reg)) =
        if reg ∈ Fl4Spec.msgRegisters.take n.val then L.mem s (regA snd (regIdx reg))
        else L.mem s (regA rcv (regIdx reg))) ∧
      Agree (L.mem s) (L.mem r.1) (fun b => ¬ RcvMR rcv b) ∧ WritesIn st s r.1 (EWrite T E R B) ⦄ := by
  have hsa := hP.tcb snd hs
  have hra := hP.tcb rcv hr
  have hd := tcb_disj hP hr hs hne
  unfold msg.copy_mrs_loop0
  apply loop.spec_decr_nat (measure := fun x => 4 - x.2.val)
    (inv := fun x => x.2.val ≤ 4 ∧ x.2.val ≤ n.val ∧
      (∀ reg, L.mem x.1 (regA rcv (regIdx reg)) =
        if reg ∈ Fl4Spec.msgRegisters.take x.2.val then L.mem s (regA snd (regIdx reg))
        else L.mem s (regA rcv (regIdx reg))) ∧
      Agree (L.mem s) (L.mem x.1) (fun b => ¬ RcvMR rcv b) ∧ WritesIn st s x.1 (EWrite T E R B))
  · rintro ⟨s', i⟩ ⟨hi4, hin, hregs, hag, hw⟩
    unfold msg.copy_mrs_loop0.body
    simp only at hi4 hin hregs hag hw ⊢
    by_cases h1 : i < n
    · simp only [h1, ↓reduceIte]
      by_cases h2 : i < msg.N_MSG_REGISTERS
      · have hi : i.val < 4 := by
          have : msg.N_MSG_REGISTERS.val = 4 := by unfold msg.N_MSG_REGISTERS; rfl
          have := (gt_iff_val).1 h2; omega
        simp only [h2, ↓reduceIte]
        refine WP.spec_bind (msg_register_spec i hi) ?_
        rintro r rfl
        step as ⟨v, hv⟩
        step as ⟨s1, hs1⟩
        step as ⟨i2, hi2⟩
        subst hv hs1
        have hsnd : ∀ reg, L.mem s' (regA snd (regIdx reg)) = L.mem s (regA snd (regIdx reg)) := by
          intro reg
          refine hag _ (a_reg hsa reg).1 ?_
          rintro ⟨r', -, hv'⟩
          rw [regA_val hsa (regIdx_lt reg), regA_val hra (regIdx_lt r')] at hv'
          have := regIdx_lt reg; have := regIdx_lt r'; omega
        have ha := a_reg hra (mrIdx i.val)
        have hi2v : i2.val = i.val + 1 := by simpa using hi2
        refine ⟨by omega, by have := (gt_iff_val).1 h1; omega, fun reg => ?_, ?_, ?_, by omega⟩
        · rw [hi2v]
          by_cases e : reg = mrIdx i.val
          · subst e
            rw [rd_wr_eq ha.1, if_pos ((take_succ_mem _ hi _).2 (Or.inr rfl)), hsnd]
          · rw [rd_wr_ne ha.1 (a_reg hra reg).1 (fun h => regA_ne hra e (congrArg UScalar.val h).symm), hregs reg]
            by_cases hm : reg ∈ Fl4Spec.msgRegisters.take i.val
            · rw [if_pos hm, if_pos ((take_succ_mem _ hi _).2 (Or.inl hm))]
            · rw [if_neg hm, if_neg (fun h => ((take_succ_mem _ hi _).1 h).elim hm e)]
        · refine fun b hb hn => (agree_wr (L := L) (s := s') (v := L.mem s' (regA snd (regIdx (mrIdx i.val)))) ha.1
            b hb fun h => hn ⟨_, mrIdx_mem i.val, h⟩).trans (hag b hb hn)
        · exact (hw.trans (wr_ewrite hr (twf_reg hra _) ha.1 _ _)).mono fun b hb => by rcases hb with h | h <;> exact h
      · simp only [h2, ↓reduceIte, WP.spec_ok]
        have : msg.N_MSG_REGISTERS.val = 4 := by unfold msg.N_MSG_REGISTERS; rfl
        have hi : i.val = 4 := by
          have h2' : ¬ i.val < 4 := fun h => h2 ((gt_iff_val).2 (by rw [this]; exact h))
          omega
        have hn4 : 4 ≤ n.val := by have := (gt_iff_val).1 h1; omega
        refine ⟨by omega, fun reg => ?_, hag, hw⟩
        rw [hregs reg, hi, take_four 4 (le_refl _), take_four n.val hn4]
    · simp only [h1, ↓reduceIte, WP.spec_ok]
      have hni : i.val = n.val := by
        have : ¬ i.val < n.val := fun h => h1 ((gt_iff_val).2 h)
        omega
      refine ⟨by omega, fun reg => ?_, hag, hw⟩
      rw [hregs reg, hni]
  · refine ⟨by simp, by simp, fun reg => by simp, Agree.rfl', WritesIn.refl _ _⟩

theorem mask7 : (Fl4Spec.mask 7 : BitVec 64) = 127#64 := by decide
theorem mask2 : (Fl4Spec.mask 2 : BitVec 64) = 3#64 := by decide
theorem mask52 : (Fl4Spec.mask Fl4Spec.msgLabelBits : BitVec 64) = 4503599627370495#64 := by
  unfold Fl4Spec.msgLabelBits; decide

/-- `msg_info`: the sender's message info, as l4v's `data_to_message_info`. -/
theorem msg_info_spec (s : S) (t : obj.Tcb) :
    msg.msg_info st s t ⦃ mi => mi.label.bv = (L.mem s (regA t layout.reg.MSG_INFO)).bv >>> 12 ∧
      mi.length.bv = (Fl4Spec.dataToMessageInfo (L.mem s (regA t layout.reg.MSG_INFO)).bv).miLength ∧
      mi.extra_caps.bv = (Fl4Spec.dataToMessageInfo (L.mem s (regA t layout.reg.MSG_INFO)).bv).miExtraCaps ∧
      mi.length.val ≤ 120 ⦄ := by
  unfold msg.msg_info msginfo.MessageInfo.from_word_clamped msginfo.MessageInfo.from_word
  step as ⟨w, hw⟩
  step as ⟨i, hi1, hi2⟩
  step as ⟨i1, hi11, hi12⟩
  step as ⟨i2, hi2', hi2b⟩
  step as ⟨i3, hi31, hi32⟩
  step as ⟨i4, hi4, hi4b⟩
  step as ⟨i5, hi5, hi5b⟩
  subst hw
  have hl : i5.bv = (L.mem s (regA t layout.reg.MSG_INFO)).bv &&& Fl4Spec.mask 7 := by
    rw [mask7]; exact hi5b
  have hx : i4.bv = (Fl4Spec.dataToMessageInfo (L.mem s (regA t layout.reg.MSG_INFO)).bv).miExtraCaps := by
    show _ = ((L.mem s (regA t layout.reg.MSG_INFO)).bv >>> 7) &&& Fl4Spec.mask 2
    rw [mask2, ← hi32]; exact hi4b
  have hmax : fl4_abi.consts.MSG_MAX_LENGTH.val = 120 := by unfold fl4_abi.consts.MSG_MAX_LENGTH; rfl
  have hspecL : (Fl4Spec.dataToMessageInfo (L.mem s (regA t layout.reg.MSG_INFO)).bv).miLength =
      if i5.bv > 120 then 120 else i5.bv := by
    show (let v := _; if v > 120 then 120 else v) = _
    simp only [hl]
  by_cases hc : i5 > fl4_abi.consts.MSG_MAX_LENGTH
  · simp only [hc, ↓reduceIte, WP.spec_ok]
    have hc' : i5.bv > 120 := by
      rw [gt_iff_val, hmax] at hc
      show (120 : BitVec 64).toNat < i5.bv.toNat
      simpa using hc
    refine ⟨hi2, ?_, hx, by rw [hmax]⟩
    · rw [hspecL, if_pos hc']; unfold fl4_abi.consts.MSG_MAX_LENGTH; rfl
  · simp only [hc, ↓reduceIte, WP.spec_ok]
    have hc' : ¬ i5.bv > 120 := by
      rw [gt_iff_val, hmax] at hc
      show ¬ (120 : BitVec 64).toNat < i5.bv.toNat
      simpa using hc
    refine ⟨hi2, ?_, hx, ?_⟩
    · rw [hspecL, if_neg hc']
    · rw [gt_iff_val, hmax] at hc; omega

theorem and127 {n : U64} (hn : n.val < 128) : (n &&& 127#u64).bv = n.bv := by
  apply BitVec.eq_of_toNat_eq
  rw [UScalar.bv_and, BitVec.toNat_and]
  have : (UScalar.bv (127#u64 : U64)).toNat = 2 ^ 7 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt hn

/-- `to_word` of a message info without caps. -/
theorem to_word_spec (lab n : U64) (hn : n.val < 128) :
    msginfo.MessageInfo.to_word { label := lab, caps_unwrapped := 0#u64, extra_caps := 0#u64, length := n } ⦃ v =>
      v.bv = Fl4Spec.messageInfoToData ⟨n.bv, 0, 0, lab.bv &&& Fl4Spec.mask Fl4Spec.msgLabelBits⟩ ⦄ := by
  unfold msginfo.MessageInfo.to_word
  step*
  simp only [Fl4Spec.messageInfoToData, mask52]
  have h8 : i8.bv = n.bv := i8_post1.trans ((UScalar.bv_and n 127#u64).symm.trans (and127 hn))
  have z : UScalar.bv (0#u64 : U64) = 0#64 := rfl
  simp only [UScalar.bv_or, i7_post1, i4_post1, i6_post1, i5_post1, i3_post1, i2_post1, i1_post1, i_post1, h8, z,
    BitVec.zero_and, BitVec.zero_shiftLeft, BitVec.or_zero]
  have z7 : ((0 : BitVec 64) <<< 7) = 0 := by decide
  have z9 : ((0 : BitVec 64) <<< 9) = 0 := by decide
  have o : ∀ x : BitVec 64, (x ||| (0 : BitVec 64)) = x := fun x => by simp
  rw [z7, z9, o, o]
  rfl

/-- `copy_mrs` without a receive buffer: only the first loop. -/
theorem copy_mrs_norecv (hP : EPlaced T E R B) (s : S) {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T)
    (hne : snd ≠ rcv) (sb n : U64) :
    msg.copy_mrs st s snd sb rcv 0#u64 n ⦃ r => r.1.val = min n.val 4 ∧
      (∀ reg, L.mem r.2 (regA rcv (regIdx reg)) =
        if reg ∈ Fl4Spec.msgRegisters.take n.val then L.mem s (regA snd (regIdx reg))
        else L.mem s (regA rcv (regIdx reg))) ∧
      Agree (L.mem s) (L.mem r.2) (fun b => ¬ RcvMR rcv b) ∧ WritesIn st s r.2 (EWrite T E R B) ⦄ := by
  unfold msg.copy_mrs
  refine WP.spec_bind (copy_mrs_loop0_spec (L := L) hP s hs hr hne n) ?_
  rintro ⟨s1, i⟩ h
  simp only [↓reduceIte]
  show (ok (i, s1)) ⦃ _ ⦄
  simp only [WP.spec_ok]
  exact h

/-- `lookup_extra_caps` with no buffer or no extra caps does not fail. -/
theorem lookup_extra_caps_nil (s : S) (t buf : U64) (info : msginfo.MessageInfo)
    (h : buf = 0#u64 ∨ info.extra_caps = 0#u64) : ipc.lookup_extra_caps st s t buf info ⦃ _ => True ⦄ := by
  unfold ipc.lookup_extra_caps
  by_cases hb : buf = 0#u64
  · simp [hb]
  · simp only [hb, ↓reduceIte]
    have he : info.extra_caps = 0#u64 := h.resolve_left hb
    unfold ipc.lookup_extra_caps_loop
    apply loop.spec_decr_nat (measure := fun _ => 0) (inv := fun _ => True)
    · rintro ⟨caps, i⟩ -
      unfold ipc.lookup_extra_caps_loop.body
      have : ¬ i < info.extra_caps := by rw [he]; intro h'; have := (gt_iff_val).1 h'; simp at this
      simp [this]
    · trivial

/-- `transfer_caps` without a receive buffer: the message info with no caps,
the state unchanged. -/
theorem transfer_caps_norecv (s : S) (info : msginfo.MessageInfo) (extra : Array obj.Slot 3#usize)
    (ep : U64) (receiver : obj.Tcb) :
    ipc.transfer_caps st s info extra ep receiver 0#u64 ⦃ r =>
      r = ({ label := info.label, caps_unwrapped := 0#u64, extra_caps := 0#u64, length := info.length }, s) ⦄ := by
  unfold ipc.transfer_caps msginfo.MessageInfo.new
  step*
  all_goals simp_all [obj.Slot.is_null]

/-- `set_msg_info` of a message info without caps. -/
theorem set_msg_info_spec (s : S) (t : obj.Tcb) (lab n : U64) (hn : n.val < 128) :
    msg.set_msg_info st s t { label := lab, caps_unwrapped := 0#u64, extra_caps := 0#u64, length := n } ⦃ s' =>
      ∃ v : U64, s' = L.wr s (regA t layout.reg.MSG_INFO) v ∧
        v.bv = Fl4Spec.messageInfoToData ⟨n.bv, 0, 0, lab.bv &&& Fl4Spec.mask Fl4Spec.msgLabelBits⟩ ⦄ := by
  unfold msg.set_msg_info
  refine WP.spec_bind (to_word_spec lab n hn) ?_
  rintro v hv
  step as ⟨s', hs'⟩
  exact ⟨v, hs', hv⟩

omit [L : LawfulStore st] in
/-- A TCB with new register values. -/
theorem TcbRelE.with_regs {m m' : U64 → U64} {t : U64} {x x' : Fl4Spec.Tcb} (ht : TcbAddr t)
    (h : TcbRelE R m t x) (hA : Agree m m' (fun b => TF t b ∧ (b.val < t.val + 256 ∨ t.val + 448 ≤ b.val)))
    (hx : x' = { x with tcbArch := x'.tcbArch })
    (hregs : ∀ r, (m' (regA t (regIdx r))).bv = x'.tcbArch.tcbContext.userRegs r) : TcbRelE R m' t x' := by
  have g : ∀ {b}, Aligned b ∧ TF t b → (b.val < t.val + 256 ∨ t.val + 448 ≤ b.val) → m' b = m b :=
    fun hb hv => hA _ hb.1 ⟨hb.2, hv⟩
  rw [hx]
  refine ⟨?_, fun e he => ?_, fun e d he => ?_, fun e rr d he => ?_, fun rr he => ?_, fun r => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g (a_st ht) (by rw [val_st ht]; omega)]; exact h.st
  · rw [g (a_blk ht) (by rw [val_blk ht]; omega)]; exact h.blk e he
  · rw [g (a_badge ht) (by rw [val_badge ht]; omega), g (a_flags ht) (by rw [val_flags ht]; omega)]
    exact h.send e d he
  · rw [g (a_reply ht) (by rw [val_reply ht]; omega)]; exact h.recv e rr d he
  · rw [g (a_reply ht) (by rw [val_reply ht]; omega)]; exact h.reply rr he
  · exact hregs r
  · rw [g (a_prio ht) (by rw [val_prio ht]; omega)]; exact h.prio
  · rw [g (a_fault ht) (by rw [val_fault ht]; omega)]; exact h.fault0
  · rw [g (a_fault ht) (by rw [val_fault ht]; omega)]; exact h.faultT
  · rw [g (a_bound ht) (by rw [val_bound ht]; omega)]; exact h.bound
  · exact h.faultR.congr (g (a_fault ht) (by rw [val_fault ht]; omega)) (g (a_fw0 ht) (by rw [val_fw0 ht]; omega)) (g (a_fw1 ht) (by rw [val_fw1 ht]; omega)) (g (a_lf ht) (by rw [val_lf ht]; omega)) (g (a_lf0 ht) (by rw [val_lf0 ht]; omega)) (g (a_lf1 ht) (by rw [val_lf1 ht]; omega))

theorem xfer_len {i : U64} {Ln : Fl4Spec.LengthType} (hi : i.val = min Ln.toNat 4) :
    i.bv = min Ln (Fl4Spec.natToLen ((Fl4Spec.msg_registers.take (Fl4Spec.unat Ln)).length +
      ([] : List Fl4Spec.Word).length)) := by
  have hl : (Fl4Spec.msg_registers.take (Fl4Spec.unat Ln)).length + ([] : List Fl4Spec.Word).length =
      min Ln.toNat 4 := by
    simp [Fl4Spec.msg_registers, Fl4Spec.msgRegisters, Fl4Spec.unat]
  rw [hl]
  have hle : Fl4Spec.natToLen (min Ln.toNat 4) ≤ Ln := by
    rw [BitVec.le_def]
    unfold Fl4Spec.natToLen
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have key : i.bv = Fl4Spec.natToLen (min Ln.toNat 4) := by
    apply BitVec.eq_of_toNat_eq
    unfold Fl4Spec.natToLen
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hi
  rw [BitVec.min_def]
  by_cases hc : Ln ≤ Fl4Spec.natToLen (min Ln.toNat 4)
  · rw [if_pos hc]; rw [key]; exact (BitVec.le_antisymm hc hle).symm
  · rw [if_neg hc]; exact key

end

/-! ## The buffer hypothesis and the transfer -/

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st] {T E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {SR : S → Fl4Spec.State Unit → Prop}

variable (st) in
/-- The IPC-buffer hypothesis: FL4's `lookup_ipc_buffer` finds no buffer
exactly when the spec's does (the buffer-frame cap is CSpace state, related
by `SR`). -/
structure EpBufHyps (T E R : Set U64) (B : Set (U64 × Fl4Spec.Word)) (SR : S → Fl4Spec.State Unit → Prop) :
    Prop where
  lookup : ∀ s σ (t : U64) (x : Fl4Spec.Tcb) (b : Bool), EpStateRel T E R B (L.mem s) σ → SR s σ → t ∈ T →
    σ.kheap t.bv = some (.tcb x) → msg.lookup_ipc_buffer st s b t ⦃ w => (w = 0#u64 ↔ ipcBufOf b x = none) ⦄

/-- The receiver's register words. -/
def RcvReg (rcv b : U64) : Prop := ∃ r, b.val = (regA rcv (regIdx r)).val

/-- **`do_ipc_transfer`, registers only** (see the module docstring). -/
theorem do_ipc_transfer_regs (hH : EpHyps st T E R B SR) (hBf : EpBufHyps st T E R B SR) (hP : EPlaced T E R B)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr)) (hf : xs.tcbFault = none)
    (hrb : ipcBufOf true xr = none) (ep badge : U64) (grant : Bool)
    (hcaps : grant = false ∨ ipcBufOf false xs = none ∨
      Fl4Spec.unat (Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miExtraCaps = 0) :
    ipc.do_ipc_transfer st ar s a snd ep badge grant rcv ⦃ s' =>
      Fl4Spec.doIpcTransfer (Z := Unit) snd.bv (some ep.bv) badge.bv grant rcv.bv σ =
        ({((), updK σ rcv.bv (.tcb (xferTcb xr xs badge.bv)))}, False) ∧
      EpStateRel T E R B (L.mem s') (updK σ rcv.bv (.tcb (xferTcb xr xs badge.bv))) ∧
      SR s' (updK σ rcv.bv (.tcb (xferTcb xr xs badge.bv))) ∧
      Agree (L.mem s) (L.mem s') (fun b => ¬ RcvReg rcv b) ⦄ := by
  have hsa := hP.tcb snd hs
  have hra := hP.tcb rcv hr
  have hxs := hR.at_tcb hs hks
  have hxr := hR.at_tcb hr hkr
  have hspec := doIpcTransfer_regs (bv_inj hne) hks hkr hf hrb (some ep.bv) badge.bv grant hcaps
  have hwmi : (L.mem s (regA snd layout.reg.MSG_INFO)).bv = xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register := by
    rw [← regIdx_msgInfo]; exact hxs.regs _
  unfold ipc.do_ipc_transfer
  refine WP.spec_bind (hBf.lookup s σ rcv xr true hR hSR hr hkr) ?_
  rintro rb hrb0
  have hrb' : rb = 0#u64 := hrb0.2 hrb
  subst hrb'
  step as ⟨ft, hft⟩
  have hft0 : ft = fl4_abi.consts.fault.NullFault := by
    rw [hft, hxs.fault0.2 hf]; unfold fl4_abi.consts.fault.NullFault; rfl
  simp only [hft0, ↓reduceIte]
  refine WP.spec_bind (hBf.lookup s σ snd xs false hR hSR hs hks) ?_
  rintro sb hsb
  unfold ipc.do_normal_transfer
  refine WP.spec_bind (msg_info_spec (L := L) s snd) ?_
  rintro tag ⟨hlab, hlen, hext, hle⟩
  have hex : (if grant = true then (do
        let r ← ipc.lookup_extra_caps st s snd sb tag
        match r with
        | core.result.Result.Ok e => ok e
        | core.result.Result.Err _ => ok ipc.NO_EXTRA_CAPS)
      else ok ipc.NO_EXTRA_CAPS) ⦃ _ => True ⦄ := by
    cases grant with
    | false => simp
    | true =>
      simp only [↓reduceIte]
      have hc : sb = 0#u64 ∨ tag.extra_caps = 0#u64 := by
        rcases hcaps with h | h | h
        · cases h
        · exact Or.inl (hsb.2 h)
        · right; apply eq_of_bv; rw [hext, hwmi]; apply BitVec.eq_of_toNat_eq; exact h
      refine WP.spec_bind (lookup_extra_caps_nil s snd sb tag hc) ?_
      rintro r -
      split <;> simp
  refine WP.spec_bind hex ?_
  rintro extra -
  refine WP.spec_bind (copy_mrs_norecv (L := L) hP s hs hr hne sb tag.length) ?_
  rintro ⟨i, s1⟩ ⟨hi, hregs, hag, hw⟩
  refine WP.spec_bind (transfer_caps_norecv (L := L) s1 tag extra ep rcv) ?_
  rintro ⟨out, s2⟩ hout
  simp only [Prod.mk.injEq] at hout
  obtain ⟨rfl, h2⟩ := hout
  subst s2
  show (do
    let s3 ← msg.set_msg_info st s1 rcv
      { label := tag.label, caps_unwrapped := 0#u64, extra_caps := 0#u64, length := i }
    obj.Tcb.set_reg st rcv s3 layout.reg.BADGE badge) ⦃ _ ⦄
  have hi4 : i.val ≤ 4 := by rw [hi]; omega
  refine WP.spec_bind (set_msg_info_spec (L := L) s1 rcv tag.label i (by omega)) ?_
  rintro s3 ⟨v, hs3, hv⟩
  step as ⟨s4, hs4⟩
  subst hs3 hs4
  -- the spec's message info
  set w := xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register with hwdef
  have hLv : Fl4Spec.unat (Fl4Spec.dataToMessageInfo w).miLength = tag.length.val := by
    show _ = tag.length.bv.toNat
    rw [hlen, hwmi]
  have hvx : v.bv = Fl4Spec.messageInfoToData (xferInfo w) := by
    rw [hv]
    unfold xferInfo
    congr 1
    congr 1
    · exact xfer_len (by rw [hi]; show _ = min (Fl4Spec.unat _) 4; rw [hLv])
    · rw [hlab, hwmi]; rfl
  -- step 1: the copied registers
  set x1 := copyRegsTcb xr xs.tcbArch.tcbContext.userRegs (Fl4Spec.msg_registers.take
    (Fl4Spec.unat (Fl4Spec.dataToMessageInfo w).miLength)) with hx1
  have hnotreg : ∀ b, TF rcv b → (b.val < rcv.val + 256 ∨ rcv.val + 448 ≤ b.val) → ¬ RcvMR rcv b := by
    rintro b - hv' ⟨r, -, hb⟩
    rw [regA_val hra (regIdx_lt r)] at hb; have := regIdx_lt r; omega
  have hR1 : EpStateRel T E R B (L.mem s1) (updK σ rcv.bv (.tcb x1)) := by
    refine hR.upd_tcb hP hr x1 (hag.mono fun b hb h' => hb.2 ?_) (Or.inr ⟨hag _ (a_st hra).1 ?_, hag _ (a_blk hra).1 ?_⟩)
      (hxr.with_regs hra (hag.mono fun b hb => hnotreg b hb.1 hb.2) (copyRegsTcb_other _ _ _) fun r => ?_)
    · obtain ⟨r', -, hb'⟩ := h'
      exact TF.of_val (a_reg hra r').2 hb'
    · exact hnotreg _ (a_st hra).2 (by rw [val_st hra]; omega)
    · exact hnotreg _ (a_blk hra).2 (by rw [val_blk hra]; omega)
    · rw [hregs r, hx1, copyRegsTcb_regs, hLv]
      show _ = if r ∈ Fl4Spec.msgRegisters.take tag.length.val then _ else _
      split
      · exact hxs.regs r
      · exact hxr.regs r
  have hS1 : EpStep σ (updK σ rcv.bv (.tcb x1)) := by
    have h := EpStep.tcb hkr xr.tcbState x1.tcbArch
    rwa [← copyRegsTcb_other] at h
  have hSR1 := hH.stable _ _ _ _ hSR hw hS1
  have hkr1 : (updK σ rcv.bv (.tcb x1)).kheap rcv.bv = some (.tcb x1) := by simp
  -- step 2: the message info register
  obtain ⟨hR2, hW2, hS2⟩ := write_reg_rel hP s1 _ hR1 hr hkr1 Fl4Spec.msg_info_register v
  rw [regIdx_msgInfo] at hR2 hW2
  have hkr2 : (updK (updK σ rcv.bv (.tcb x1)) rcv.bv (.tcb (setReg x1 Fl4Spec.msg_info_register v.bv))).kheap rcv.bv =
      some (.tcb (setReg x1 Fl4Spec.msg_info_register v.bv)) := by simp
  -- step 3: the badge register
  obtain ⟨hR3, hW3, hS3⟩ := write_reg_rel hP _ _ hR2 hr hkr2 Fl4Spec.badge_register badge
  rw [regIdx_badge] at hR3 hW3
  have hfin : updK (updK (updK σ rcv.bv (.tcb x1)) rcv.bv (.tcb (setReg x1 Fl4Spec.msg_info_register v.bv))) rcv.bv
      (.tcb (setReg (setReg x1 Fl4Spec.msg_info_register v.bv) Fl4Spec.badge_register badge.bv)) =
      updK σ rcv.bv (.tcb (xferTcb xr xs badge.bv)) := by
    simp only [updK, Function.update_idem]
    rw [hvx]; rfl
  rw [hfin] at hR3
  refine ⟨hspec, hR3, ?_, ?_⟩
  · have := hH.stable _ _ _ _ (hH.stable _ _ _ _ hSR1 hW2 hS2) hW3 hS3
    rwa [hfin] at this
  · intro b hb hn
    have hn1 : ¬ RcvMR rcv b := fun ⟨r, _, h⟩ => hn ⟨r, h⟩
    rw [badgeRegA_eq_regA, ← regIdx_msgInfo,
      rd_wr_ne (a_reg hra Fl4Spec.badge_register).1 hb (fun h => hn ⟨Fl4Spec.badge_register, by rw [← h]⟩),
      rd_wr_ne (a_reg hra Fl4Spec.msg_info_register).1 hb (fun h => hn ⟨Fl4Spec.msg_info_register, by rw [← h]⟩)]
    exact hag b hb hn1

end

end

end Fl4Proofs.P3.Endp
