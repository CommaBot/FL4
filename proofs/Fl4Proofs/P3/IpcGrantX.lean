/-
P3 (DESIGN.md §9), IPC: **the grant path of `do_ipc_transfer`** (G4), as
fields of the transfer bundle `EpStepsBuf` with `GC := True`
(`IpcSchedHyps.stepsG`), on `SRT … SRE`:

* `do_ipc_transfer_regsX`, `doIpcTransfer_regsG`: without a receive buffer
  the caps are looked up (read-only on both sides) and dropped, so the
  transfer is the registers-only one.
* `do_ipc_transfer_grant`: with a receive buffer, the extra caps
  (`lookup_extra_top`), the copy (`copy_mrs_rel`, `RelTopB` by its frame),
  the receive slot (`get_receive_slot_top`) and `transfer_caps_top`.
-/
import Fl4Proofs.P3.IpcGrant
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

theorem transferCaps_noRecvBufG {σ : State Unit} (mi : MessageInfo) (caps : List (Cap × CslotPtr))
    (ep : Option ObjRef) (rcv : ObjRef) :
    transferCaps (Z := Unit) mi caps ep rcv none σ = ({(⟨mi.miLength, 0, 0, mi.miLabel⟩, σ)}, False) := by
  unfold transferCaps
  rw [nd_bind_one (show getReceiveSlots (Z := Unit) rcv none σ = ({([], σ)}, False) from rfl), nd_pure_bind']
  rfl

/-- **`do_ipc_transfer`, registers only**, the caps looked up (and dropped,
there being no receive buffer). -/
theorem doIpcTransfer_regsG {σ : State Unit} {snd rcv : ObjRef} {xs xr : Tcb} (hne : snd ≠ rcv)
    (hks : σ.kheap snd = some (.tcb xs)) (hkr : σ.kheap rcv = some (.tcb xr)) (hf : xs.tcbFault = none)
    (hrb : ipcBufOf true xr = none) (ep : Option ObjRef) (badge : Badge) (grant : Bool)
    (hlk : grant = true → ∃ l, NonDetE.catch (lookupExtraCaps (Z := Unit) snd (ipcBufOf false xs)
      (dataToMessageInfo (xs.tcbArch.tcbContext.userRegs msg_info_register))) (fun _ => pure []) σ =
      ({(l, σ)}, False)) :
    doIpcTransfer (Z := Unit) snd ep badge grant rcv σ = ({((), updK σ rcv (.tcb (xferTcb xr xs badge)))}, False) := by
  unfold doIpcTransfer
  rw [nd_bind_one (lookupIpcBuffer_eq hkr true), hrb, nd_bind_one (threadGet_eq _ hks), hf]
  dsimp only
  rw [nd_bind_one (lookupIpcBuffer_eq hks false)]
  unfold doNormalTransfer
  rw [nd_bind_one (getMessageInfo_eq hks)]
  cases grant <;> simp only [Bool.false_eq_true, ↓reduceIte]
  on_goal 1 => rw [nd_pure_bind']
  on_goal 2 => obtain ⟨l, hl⟩ := hlk rfl; rw [nd_bind_one hl]
  all_goals
    rw [nd_bind_one (copyMrs_noRecvBuf hne hks hkr _ _), nd_bind_one (transferCaps_noRecvBufG _ _ _ _)]
    have hkr1 : (updK σ rcv (.tcb (copyRegsTcb xr xs.tcbArch.tcbContext.userRegs
        (msg_registers.take (unat (dataToMessageInfo (xs.tcbArch.tcbContext.userRegs msg_info_register)).miLength))))).kheap
        rcv = some (.tcb (copyRegsTcb xr xs.tcbArch.tcbContext.userRegs
        (msg_registers.take (unat (dataToMessageInfo (xs.tcbArch.tcbContext.userRegs msg_info_register)).miLength)))) := by
      simp
    unfold setMessageInfo
    rw [nd_bind_one (asUser_setRegister_eq _ _ hkr1)]
    rw [asUser_setRegister_eq (x := setReg (copyRegsTcb xr xs.tcbArch.tcbContext.userRegs
        (msg_registers.take (unat (dataToMessageInfo (xs.tcbArch.tcbContext.userRegs msg_info_register)).miLength)))
        msg_info_register (messageInfoToData (xferInfo (xs.tcbArch.tcbContext.userRegs msg_info_register)))) _ _
        (by simp only [updK_kheap, Function.update_self]; rfl)]
    simp only [updK, Function.update_idem]
    rfl

/-- **`do_ipc_transfer` with a receive buffer and the caps transferred**:
the outcome from the caps looked up, the copy and `transfer_caps`. -/
theorem doIpcTransfer_grant {σ : State Unit} {snd rcv : ObjRef} {xs xr : Tcb}
    (hks : σ.kheap snd = some (.tcb xs)) (hkr : σ.kheap rcv = some (.tcb xr)) (hf : xs.tcbFault = none)
    {rb : ObjRef} (hrb : ipcBufOf true xr = some rb) (ep : Option ObjRef) (badge : Badge) (grant : Bool)
    {caps : List (Cap × CslotPtr)}
    (hlk : (if grant = true then NonDetE.catch (lookupExtraCaps (Z := Unit) snd (ipcBufOf false xs)
      (dataToMessageInfo (xs.tcbArch.tcbContext.userRegs msg_info_register))) (fun _ => pure []) else pure []) σ =
      ({(caps, σ)}, False))
    {mrs : LengthType} {σc : State Unit}
    (hcopy : copyMrs (Z := Unit) snd (ipcBufOf false xs) rcv (some rb)
      (dataToMessageInfo (xs.tcbArch.tcbContext.userRegs msg_info_register)).miLength σ = ({(mrs, σc)}, False))
    {mf : MessageInfo} {σt : State Unit}
    (htc : transferCaps (Z := Unit) (dataToMessageInfo (xs.tcbArch.tcbContext.userRegs msg_info_register)) caps ep
      rcv (some rb) σc = ({(mf, σt)}, False))
    {xt : Tcb} (hkt : σt.kheap rcv = some (.tcb xt)) :
    doIpcTransfer (Z := Unit) snd ep badge grant rcv σ =
      ({((), updK σt rcv (.tcb (setReg (setReg xt msg_info_register (messageInfoToData
        ⟨mrs, mf.miExtraCaps, mf.miCapsUnwrapped,
          (dataToMessageInfo (xs.tcbArch.tcbContext.userRegs msg_info_register)).miLabel⟩))
        badge_register badge)))}, False) := by
  unfold doIpcTransfer
  rw [nd_bind_one (lookupIpcBuffer_eq hkr true), hrb, nd_bind_one (threadGet_eq _ hks), hf]
  dsimp only
  rw [nd_bind_one (lookupIpcBuffer_eq hks false)]
  unfold doNormalTransfer
  rw [nd_bind_one (getMessageInfo_eq hks)]
  cases grant <;> simp only [Bool.false_eq_true, ↓reduceIte] at hlk ⊢
  all_goals
    rw [nd_bind_one hlk, nd_bind_one hcopy, nd_bind_one htc]
    unfold setMessageInfo
    rw [nd_bind_one (asUser_setRegister_eq _ _ hkt)]
    rw [asUser_setRegister_eq (x := setReg xt msg_info_register (messageInfoToData
        ⟨mrs, mf.miExtraCaps, mf.miCapsUnwrapped,
          (dataToMessageInfo (xs.tcbArch.tcbContext.userRegs msg_info_register)).miLabel⟩)) _ _
        (by simp only [updK_kheap, Function.update_self])]
    simp only [updK, Function.update_idem]

end Spec

section Regs
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st] {T E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {SR : S → Fl4Spec.State Unit → Prop}

/-- **`do_ipc_transfer`, registers only**, with the extra-cap lookup given
(`hX`: FL4's terminates, and the spec's is deterministic and read-only). -/
theorem do_ipc_transfer_regsX (hH : EpHyps st T E R B SR) (hBf : EpBufHyps st T E R B SR)
    (hBm : EpBufMapHyps st T E R B SR) (hP : EPlaced T E R B)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr)) (hf : xs.tcbFault = none)
    (hrb : ipcBufOf true xr = none) (ep badge : U64) (grant : Bool)
    (hX : grant = true → ∀ sb tag, ((ipcBufOf false xs = none ∧ sb = 0#u64) ∨
        (∃ sp, ipcBufOf false xs = some sp ∧ sb ≠ 0#u64 ∧ BufMap B sb sp)) →
      tag.extra_caps.bv = (Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miExtraCaps →
      ipc.lookup_extra_caps st s snd sb tag ⦃ _ => ∃ l, Fl4Spec.NonDetE.catch (Fl4Spec.lookupExtraCaps (Z := Unit) snd.bv
        (ipcBufOf false xs) (Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)))
        (fun _ => pure []) σ = ({(l, σ)}, False) ⦄) :
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
  have hwmi : (L.mem s (regA snd layout.reg.MSG_INFO)).bv = xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register := by
    rw [← regIdx_msgInfo]; exact hxs.regs _
  unfold ipc.do_ipc_transfer
  refine WP.spec_bind (hBf.lookup s σ rcv xr true hR hSR hr hkr) ?_
  rintro rb hrb0
  have hrb' : rb = 0#u64 := hrb0.2 hrb
  subst hrb'
  step with Fl4Proofs.P3.Endp.obj.Tcb.fault_type.spec as ⟨ft, hft⟩
  have hft0 : ft = fl4_abi.consts.fault.NullFault := by
    rw [hft, hxs.fault0.2 hf]; unfold fl4_abi.consts.fault.NullFault; rfl
  simp only [hft0, ↓reduceIte]
  refine WP.spec_bind (lookup_send_buf hBf hBm s σ hR hSR hs hks) ?_
  rintro sb hsb
  unfold ipc.do_normal_transfer
  refine WP.spec_bind (msg_info_spec (L := L) s snd) ?_
  rintro tag ⟨hlab, hlen, hext, hle⟩
  have hex : (if grant = true then (do
        let r ← ipc.lookup_extra_caps st s snd sb tag
        match r with
        | core.result.Result.Ok e => ok e
        | core.result.Result.Err _ => ok ipc.NO_EXTRA_CAPS)
      else ok ipc.NO_EXTRA_CAPS) ⦃ _ => grant = true → ∃ l, Fl4Spec.NonDetE.catch
        (Fl4Spec.lookupExtraCaps (Z := Unit) snd.bv (ipcBufOf false xs)
          (Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)))
        (fun _ => pure []) σ = ({(l, σ)}, False) ⦄ := by
    cases grant with
    | false => rw [if_neg (by decide), WP.spec_ok]; intro h; cases h
    | true =>
      rw [if_pos rfl]
      refine WP.spec_bind (hX rfl sb tag hsb (by rw [hext, hwmi])) ?_
      rintro r hl
      split <;> (rw [WP.spec_ok]; exact fun _ => hl)
  refine WP.spec_bind hex ?_
  rintro extra hlx
  have hspec := doIpcTransfer_regsG (fun h => hne (eq_of_bv h)) hks hkr hf hrb (some ep.bv) badge.bv grant hlx
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
  step with Fl4Proofs.P3.Endp.obj.Tcb.set_reg.spec as ⟨s4, hs4⟩
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
    rw [← regIdx_msgInfo, ← regIdx_badge,
      rd_wr_ne (a_reg hra Fl4Spec.badge_register).1 hb (fun h => hn ⟨Fl4Spec.badge_register, by rw [← h]⟩),
      rd_wr_ne (a_reg hra Fl4Spec.msg_info_register).1 hb (fun h => hn ⟨Fl4Spec.msg_info_register, by rw [← h]⟩)]
    exact hag b hb hn1


end Regs

section Info
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

theorem and_low {n : U64} {j : Nat} (hn : n.val < 2 ^ j) (k : U64) (hk : k.bv.toNat = 2 ^ j - 1) :
    (n &&& k).bv = n.bv := by
  apply BitVec.eq_of_toNat_eq
  rw [UScalar.bv_and, BitVec.toNat_and, hk, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt hn

/-- **`to_word`** of a message info with its fields in range. -/
theorem to_word_specG (m : msginfo.MessageInfo) (hl : m.length.val < 128) (hu : m.caps_unwrapped.val < 8)
    (he : m.extra_caps.val < 4) :
    msginfo.MessageInfo.to_word m ⦃ v => v.bv = Fl4Spec.messageInfoToData
      ⟨m.length.bv, m.extra_caps.bv, m.caps_unwrapped.bv, m.label.bv &&& Fl4Spec.mask Fl4Spec.msgLabelBits⟩ ⦄ := by
  unfold msginfo.MessageInfo.to_word
  step*
  simp only [Fl4Spec.messageInfoToData, mask52]
  have h8 : i8.bv = m.length.bv := i8_post1.trans ((UScalar.bv_and _ 127#u64).symm.trans (and_low (j := 7) hl _ rfl))
  have h2 : i2.bv = m.caps_unwrapped.bv :=
    i2_post1.trans ((UScalar.bv_and _ 7#u64).symm.trans (and_low (j := 3) hu _ rfl))
  have h5 : i5.bv = m.extra_caps.bv :=
    i5_post1.trans ((UScalar.bv_and _ 3#u64).symm.trans (and_low (j := 2) he _ rfl))
  simp only [UScalar.bv_or, i7_post1, i4_post1, i6_post1, i1_post1, i3_post1, i_post1, h8, h2, h5]
  show _ = ((m.label.bv &&& 4503599627370495#64) <<< 12 ||| m.extra_caps.bv <<< 7 ||| m.caps_unwrapped.bv <<< 9) |||
    m.length.bv
  ac_rfl

/-- `set_msg_info` of a message info with its fields in range. -/
theorem set_msg_info_specG (s : S) (t : obj.Tcb) (m : msginfo.MessageInfo) (hl : m.length.val < 128)
    (hu : m.caps_unwrapped.val < 8) (he : m.extra_caps.val < 4) :
    msg.set_msg_info st s t m ⦃ s' => ∃ v : U64, s' = L.wr s (regA t layout.reg.MSG_INFO) v ∧
      v.bv = Fl4Spec.messageInfoToData
        ⟨m.length.bv, m.extra_caps.bv, m.caps_unwrapped.bv, m.label.bv &&& Fl4Spec.mask Fl4Spec.msgLabelBits⟩ ⦄ := by
  unfold msg.set_msg_info
  refine WP.spec_bind (to_word_specG m hl hu he) ?_
  rintro v hv
  step with Fl4Proofs.P3.Endp.obj.Tcb.set_reg.spec as ⟨s', hs'⟩
  exact ⟨v, hs', hv⟩

/-- The label field of a message-info word has its 52 bits. -/
theorem label_mask (w : Fl4Spec.Word) : (w >>> 12) &&& Fl4Spec.mask Fl4Spec.msgLabelBits = w >>> 12 := by
  rw [mask52]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (4503599627370495#64).toNat = 2 ^ 52 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    BitVec.toNat_ushiftRight]
  refine Nat.mod_eq_of_lt ?_
  have := w.isLt
  rw [Nat.shiftRight_eq_div_pow]
  omega

theorem extra_le3 (w : Fl4Spec.Word) : ((Fl4Spec.dataToMessageInfo w).miExtraCaps).toNat ≤ 3 := by
  show ((w >>> 7) &&& Fl4Spec.mask 2).toNat ≤ 3
  rw [BitVec.toNat_and]
  exact (Nat.and_le_right).trans (by decide)

end Info

end

end Fl4Proofs.P3.Endp

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

section Grant
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

theorem RelTopB.tcbT {th : TypedHeap} {G : MdbGhost} {s : S} {σ : Fl4Spec.State Unit}
    (hB : RelTopB (L := L) th G N T C E R B c s σ) {t : U64} {x : Fl4Spec.Tcb}
    (hk : σ.kheap t.bv = some (.tcb x)) : th t = some .tcb :=
  (hB.2.2.1.kt t.bv).2 x hk

/-- Writes to IPC words keep the slots. -/
theorem slotsSame_of_iwords {th : TypedHeap} {kb : U64} (hPl : Placed th) (hA : IpcApart th N T E R B kb c)
    {s s' : S} {W : U64 → Prop} (hW : WritesIn st s s' W) (hWI : ∀ a, W a → IWords N T E R B a) :
    SlotsSame th (L.mem s) (L.mem s') := by
  intro a ha
  have hf := ha.fit hPl
  have hal := ha.align hPl
  have w : ∀ k : U64, k.val < 32 → k.val % 8 = 0 → L.mem s' (wordOf a k) = L.mem s (wordOf a k) := by
    intro k hk hk8
    have hv := wordOf_val (a := a) (k := k) (by omega)
    refine hW.2.2 _ (by unfold P1.Aligned; rw [hv]; omega) fun hw => ?_
    exact hA.slot _ (hWI _ hw) a ha (by rw [hv]; omega)
  refine ⟨?_, w 8#u64 (by decide) (by decide), w 16#u64 (by decide) (by decide), w 24#u64 (by decide) (by decide)⟩
  have := w 0#u64 (by decide) (by decide)
  rwa [wordOf_zero] at this

theorem ExtraOK.of_same {th : TypedHeap} {m m' : U64 → U64} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    {caps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)} (h : ExtraOK th m extra caps) (hS : SlotsSame th m m') :
    ExtraOK th m' extra caps := by
  refine ⟨h.1, fun j hj => ?_, h.2.2⟩
  obtain ⟨ps, rs, idx, cv, hps, hls, h1, hxa, hcv, h2⟩ := h.2.1 j hj
  refine ⟨ps, rs, idx, cv, hps, hls, h1, hxa, ?_, h2⟩
  rw [hS.capAt (by rw [hxa]; exact AbsSlot.isSlot (⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩ :
    AbsSlot th (ps.bv, idx))), hcv]

theorem RelTopB.stableE {th : TypedHeap} {G : MdbGhost} {s s' : S} {σ σ' : Fl4Spec.State Unit}
    (h : RelTopB (L := L) th G N T C E R B c s σ) (hW : WritesIn st s s' (EWrite T E R B)) (hK : EpStep σ σ') :
    RelTopB (L := L) th G N T C E R B c s' σ' :=
  let ⟨hc, hl, hs⟩ := hK.ckeep
  h.frameN hW (fun _ ha => Or.inl (EWrite.iwords ha)) hc hl hs (Ipc.SzKeep.epStep hK)

set_option maxHeartbeats 4000000 in
/-- **`do_ipc_transfer` with a receive buffer, caps granted** (G4), on
`SRT … SRE`: the transfer field `xbuf` of the bundle with `GC := True`. -/
theorem do_ipc_transfer_grant (hH : IpcSchedHyps st ar N T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hBf : EpBufHyps st T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hBm : EpBufMapHyps st T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hP0 : IPlaced N T E R B) (hP : EPlaced T E R B)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ)
    (hSR : SRN st N T (SRS st T (SRT st N T C E R B c (SRE st N T C E R B c))) s σ)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr)) (hf : xs.tcbFault = none)
    {rp : Fl4Spec.ObjRef} (hrb : ipcBufOf true xr = some rp) (ep badge : U64) (grant : Bool) :
    ipc.do_ipc_transfer st ar s a snd ep badge grant rcv ⦃ s' => ∃ σ',
      Fl4Spec.doIpcTransfer (Z := Unit) snd.bv (some ep.bv) badge.bv grant rcv.bv σ = ({((), σ')}, False) ∧
      EpStateRel T E R B (L.mem s') σ' ∧
      SRN st N T (SRS st T (SRT st N T C E R B c (SRE st N T C E R B c))) s' σ' ∧
      Agree (L.mem s) (L.mem s') (fun b => AllTF T b ∧ ¬ RcvReg rcv b ∧ ¬ BufW B b) ∧
      KeepNC σ σ' rcv.bv ∧
      ∃ x', σ'.kheap rcv.bv = some (.tcb x') ∧ x'.tcbState = xr.tcbState ⦄ := by
  have hra := hP.tcb rcv hr
  have hxs := hR.at_tcb hs hks
  have hwmi : (L.mem s (regA snd layout.reg.MSG_INFO)).bv = xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register := by
    rw [← regIdx_msgInfo]; exact hxs.regs _
  have hIR := (IpcRel.ofSRN hR hSR).1
  obtain ⟨⟨th, G, hB⟩, -⟩ := hSR.1.1
  have hEH := hH.epHyps hP0
  have hu := hBm.frame s σ rcv xr rp hR hSR.1.1 hr hkr hrb
  unfold ipc.do_ipc_transfer
  refine WP.spec_bind (hBm.lookupMap s σ rcv xr true rp hR hSR.1.1 hr hkr hrb) ?_
  rintro rw ⟨hrw0, hmr⟩
  step with Fl4Proofs.P3.Endp.obj.Tcb.fault_type.spec as ⟨ft, hft⟩
  have hft0 : ft = fl4_abi.consts.fault.NullFault := by
    rw [hft, hxs.fault0.2 hf]; unfold fl4_abi.consts.fault.NullFault; rfl
  simp only [hft0, ↓reduceIte]
  refine WP.spec_bind (lookup_send_buf hBf hBm s σ hR hSR.1.1 hs hks) ?_
  rintro sw hsw
  unfold ipc.do_normal_transfer
  refine WP.spec_bind (msg_info_spec (L := L) s snd) ?_
  rintro tag ⟨hlab, hlen, hext, hle⟩
  set w := xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register with hwdef
  have hn3 : tag.extra_caps.val ≤ 3 := by
    show tag.extra_caps.bv.toNat ≤ 3; rw [hext, hwmi]; exact extra_le3 w
  have hsb' : sw = 0#u64 ↔ ipcBufOf false xs = none := by
    rcases hsw with ⟨h1, h2⟩ | ⟨sp, h1, h2, -⟩
    · exact ⟨fun _ => h1, fun _ => h2⟩
    · rw [h1]; exact ⟨fun h => absurd h h2, fun h => by cases h⟩
  have hsm : ∀ sb, ipcBufOf false xs = some sb → BufMap B sw sb := by
    intro sb h
    rcases hsw with ⟨h1, -⟩ | ⟨sp, h1, -, h3⟩
    · rw [h1] at h; cases h
    · rw [h1] at h; cases h; exact h3
  have hex : (if grant = true then (do
        let r ← ipc.lookup_extra_caps st s snd sw tag
        match r with
        | core.result.Result.Ok e => ok e
        | core.result.Result.Err _ => ok ipc.NO_EXTRA_CAPS)
      else ok ipc.NO_EXTRA_CAPS) ⦃ extra => ∃ caps,
        (if grant = true then Fl4Spec.NonDetE.catch (Fl4Spec.lookupExtraCaps (Z := Unit) snd.bv (ipcBufOf false xs)
          (Fl4Spec.dataToMessageInfo w)) (fun _ => pure []) else pure []) σ = ({(caps, σ)}, False) ∧
        ExtraOK th (L.mem s) extra caps ⦄ := by
    cases grant with
    | false =>
      rw [if_neg (by decide), WP.spec_ok]
      exact ⟨[], rfl, extraOK_none th _⟩
    | true =>
      rw [if_pos rfl]
      refine WP.spec_bind (lookup_extra_top hP0 hB hIR (hB.tcbT hks) sw (ipcBufOf false xs) hsb' hsm tag
        (Fl4Spec.dataToMessageInfo w) (by show tag.extra_caps.bv.toNat = _; rw [hext, hwmi]) hn3) ?_
      rintro r ⟨caps, hc, hok⟩
      cases r <;> (simp only [WP.spec_ok]; exact ⟨caps, by simp only [↓reduceIte]; exact hc, hok⟩)
  refine WP.spec_bind hex ?_
  rintro extra ⟨caps, hlk, hok⟩
  refine WP.spec_bind (copy_mrs_rel hEH hP s σ hR hSR.1 hs hr hne hks hkr hmr hrw0 hu hsw tag.length hle) ?_
  rintro ⟨n, s1⟩ ⟨σc, hcopy, hkcf, hRc, hSc, hAc, hn, hWc, hEc⟩
  simp only at hcopy hkcf hRc hSc hAc hn hWc hEc
  set x1 := copyRegsTcb xr xs.tcbArch.tcbContext.userRegs (Fl4Spec.msg_registers.take tag.length.val) with hx1
  have hkc : σc.kheap rcv.bv = some (.tcb x1) := by rw [hkcf]; simp
  have hkco : ∀ p, p ≠ rcv.bv → σc.kheap p = σ.kheap p := fun p hp => by
    rw [hkcf]; simp [Function.update_of_ne hp]
  have hB1 : RelTopB (L := L) th G N T C E R B c s1 σc := hB.stableE hWc hEc
  have hN1 : NtfnStateRel N T (L.mem s1) σc :=
    ntfn_lift_rcv hP0.toC hSR.2 hRc hr (hAc.mono fun b hb => ⟨fun ⟨r, _, h'⟩ => hb.1 ⟨r, h'⟩, hb.2⟩) hkco hkr hkc
      (copyRegsTcb_state _ _ _)
  have hIR1 : IpcRel N T E R B (L.mem s1) σc := IpcRel.of hN1 hRc hSc.2.all
  have hSE1 : SRE st N T C E R B c s1 σc := hSc.1.2
  have hS1 : SlotsSame th (L.mem s) (L.mem s1) :=
    slotsSame_of_iwords hB.1 hB.2.2.2.2.2.1 hWc (fun _ ha => EWrite.iwords ha)
  have hok1 := hok.of_same hS1
  have hrb1 : ipcBufOf true x1 = some rp := by rw [ipcBufOf_copyRegs]; exact hrb
  have hlenw : tag.length.bv = (Fl4Spec.dataToMessageInfo w).miLength := by rw [hlen, hwmi]
  have hlabw : tag.label.bv = (Fl4Spec.dataToMessageInfo w).miLabel := by
    rw [hlab, hwmi]; exact (label_mask w).symm
  refine WP.spec_bind (transfer_caps_top hP0 hB1 hIR1 hSE1 tag (Fl4Spec.dataToMessageInfo w) hlenw hlabw hok1.1
    hok1.2.1 hok1.2.2 ep rcv rw (some rp) ⟨fun h => absurd h hrw0, fun h => by cases h⟩
    (fun rb h => by cases h; exact ⟨hmr, hBm.frame s1 σc rcv x1 rp hRc hSc.1 hr hkc hrb1⟩)
    (fun rb h => by cases h; exact hBm.recvSlots s1 σc rcv x1 rp hRc hSc.1 hr hkc hrb1)
    (fun rb h => by cases h; exact get_receive_slot_top hP0 hB1 hIR1 (hB1.tcbT hkc) hmr hrw0 caps extra)) ?_
  rintro ⟨out, s2⟩ ⟨σt, mf, htc, hMi, hexc, hIRt, hcu, he3, hlbt, hSEt, ⟨hKC, hWt⟩, G', hBt⟩
  simp only at hMi hexc hIRt hcu he3 hSEt hWt hBt
  show (do
    let s3 ← msg.set_msg_info st s2 rcv { out with length := n }
    obj.Tcb.set_reg st rcv s3 layout.reg.BADGE badge) ⦃ _ ⦄
  refine WP.spec_bind (set_msg_info_specG (L := L) s2 rcv { out with length := n } (by show n.val < 128; omega)
    hcu (by show out.extra_caps.val < 4; omega)) ?_
  rintro s3 ⟨v, hs3, hv⟩
  step with Fl4Proofs.P3.Endp.obj.Tcb.set_reg.spec as ⟨s4, hs4⟩
  subst hs3 hs4
  have hkt : σt.kheap rcv.bv = some (.tcb x1) := by
    rcases hKC rcv.bv with e | ⟨r, cs, cs', h1, -⟩
    · rw [e, hkc]
    · rw [hkc] at h1; cases h1
  have hcopy' : Fl4Spec.copyMrs (Z := Unit) snd.bv (ipcBufOf false xs) rcv.bv (some rp)
      (Fl4Spec.dataToMessageInfo w).miLength σ = ({(n.bv, σc)}, False) := by
    rw [← hlenw]; exact hcopy
  have hspec := doIpcTransfer_grant hks hkr hf hrb (some ep.bv) badge.bv grant hlk hcopy' htc hkt
  have hvx : v.bv = Fl4Spec.messageInfoToData
      ⟨n.bv, mf.miExtraCaps, mf.miCapsUnwrapped, (Fl4Spec.dataToMessageInfo w).miLabel⟩ := by
    rw [hv]
    show Fl4Spec.messageInfoToData ⟨n.bv, out.extra_caps.bv, out.caps_unwrapped.bv,
      out.label.bv &&& Fl4Spec.mask Fl4Spec.msgLabelBits⟩ = _
    rw [hexc, hMi.2.1, hMi.2.2, hlbt]
    congr 2
    show ((w >>> 12) &&& Fl4Spec.mask Fl4Spec.msgLabelBits) &&& Fl4Spec.mask Fl4Spec.msgLabelBits =
      (w >>> 12) &&& Fl4Spec.mask Fl4Spec.msgLabelBits
    rw [BitVec.and_assoc, BitVec.and_self]
  -- the two register writes
  obtain ⟨hR2, hW2, hS2⟩ := write_reg_rel hP s2 _ hIRt.toE hr hkt Fl4Spec.msg_info_register v
  rw [regIdx_msgInfo] at hR2 hW2
  have hkt2 : (updK σt rcv.bv (.tcb (setReg x1 Fl4Spec.msg_info_register v.bv))).kheap rcv.bv =
      some (.tcb (setReg x1 Fl4Spec.msg_info_register v.bv)) := by simp
  obtain ⟨hR3, hW3, hS3⟩ := write_reg_rel hP _ _ hR2 hr hkt2 Fl4Spec.badge_register badge
  rw [regIdx_badge] at hR3 hW3
  have hfin : updK (updK σt rcv.bv (.tcb (setReg x1 Fl4Spec.msg_info_register v.bv))) rcv.bv
      (.tcb (setReg (setReg x1 Fl4Spec.msg_info_register v.bv) Fl4Spec.badge_register badge.bv)) =
      updK σt rcv.bv (.tcb (setReg (setReg x1 Fl4Spec.msg_info_register (Fl4Spec.messageInfoToData
        ⟨n.bv, mf.miExtraCaps, mf.miCapsUnwrapped, (Fl4Spec.dataToMessageInfo w).miLabel⟩))
        Fl4Spec.badge_register badge.bv)) := by
    simp only [updK, Function.update_idem]; rw [hvx]
  rw [hfin] at hR3
  have hSRS2 : SRS st T (SRT st N T C E R B c (SRE st N T C E R B c)) s2 σt :=
    ⟨⟨⟨th, G', hBt⟩, hSEt⟩, ScRelM.of hIRt⟩
  have hSf := hEH.stable _ _ _ _ (hEH.stable _ _ _ _ hSRS2 hW2 hS2) hW3 hS3
  rw [hfin] at hSf
  have hA2 : Agree (L.mem s2) (L.mem (L.wr (L.wr s2 (regA rcv layout.reg.MSG_INFO) v) (regA rcv layout.reg.BADGE)
      badge)) (fun b => ¬ RcvReg rcv b) := by
    intro b hb hn'
    rw [← regIdx_msgInfo, ← regIdx_badge,
      rd_wr_ne (a_reg hra Fl4Spec.badge_register).1 hb (fun h => hn' ⟨Fl4Spec.badge_register, by rw [← h]⟩),
      rd_wr_ne (a_reg hra Fl4Spec.msg_info_register).1 hb (fun h => hn' ⟨Fl4Spec.msg_info_register, by rw [← h]⟩)]
  have hNf := ntfn_lift_rcv hP0.toC hIRt.toN hR3 hr (hA2.mono fun _ h => h.1)
    (fun p hp => by simp [updK, Function.update_of_ne hp]) hkt
    (by simp only [updK_kheap, Function.update_self]; rfl) (by rw [setReg_state, setReg_state])
  refine ⟨_, hspec, hR3, ⟨hSf, hNf⟩, ?_, ?_, _, by simp only [updK_kheap, Function.update_self]; rfl,
    by rw [setReg_state, setReg_state, copyRegsTcb_state]⟩
  · rintro b hb ⟨⟨y, hy, hty⟩, hnr, hnb⟩
    rw [hA2 b hb hnr]
    have h12 : L.mem s2 b = L.mem s1 b := by
      refine hWt.mem_eq hb fun hfw => ?_
      rcases hfw with hsw' | hbw
      · obtain ⟨y', hy', g1, g2⟩ := slotWd_range hB.1 hsw'
        have := hty.range
        exact hB.2.2.2.2.2.1.slot b (Or.inl ⟨y, hy, by omega, by omega⟩) y' hy' ⟨g1, g2⟩
      · exact hnb hbw
    rw [h12]
    exact hAc b hb ⟨fun ⟨r, _, h'⟩ => hnr ⟨r, h'⟩, hnb⟩
  · intro p hp
    simp only [updK_kheap, Function.update_of_ne hp]
    rcases hKC p with e | ⟨r, cs, cs', h1, h2⟩
    · left; rw [e, hkco p hp]
    · right; exact ⟨r, cs, cs', by rw [← hkco p hp]; exact h1, h2⟩

/-- **`do_ipc_transfer` without a receive buffer, caps looked up** (G4), on
`SRT … SRE`: the transfer field `xregs` of the bundle with `GC := True`. -/
theorem do_ipc_transfer_regsT (hH : IpcSchedHyps st ar N T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hBf : EpBufHyps st T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hBm : EpBufMapHyps st T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hP0 : IPlaced N T E R B) (hP : EPlaced T E R B)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ)
    (hSR : SRN st N T (SRS st T (SRT st N T C E R B c (SRE st N T C E R B c))) s σ)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr)) (hf : xs.tcbFault = none)
    (hrb : ipcBufOf true xr = none) (ep badge : U64) (grant : Bool) :
    ipc.do_ipc_transfer st ar s a snd ep badge grant rcv ⦃ s' =>
      Fl4Spec.doIpcTransfer (Z := Unit) snd.bv (some ep.bv) badge.bv grant rcv.bv σ =
        ({((), updK σ rcv.bv (.tcb (xferTcb xr xs badge.bv)))}, False) ∧
      EpStateRel T E R B (L.mem s') (updK σ rcv.bv (.tcb (xferTcb xr xs badge.bv))) ∧
      SRN st N T (SRS st T (SRT st N T C E R B c (SRE st N T C E R B c))) s'
        (updK σ rcv.bv (.tcb (xferTcb xr xs badge.bv))) ∧
      Agree (L.mem s) (L.mem s') (fun b => ¬ RcvReg rcv b) ⦄ := by
  have hIR := (IpcRel.ofSRN hR hSR).1
  obtain ⟨⟨th, G, hB⟩, -⟩ := hSR.1.1
  refine WP.spec_mono (do_ipc_transfer_regsX (ar := ar) (hH.epHyps hP0) hBf.srs hBm.srs hP s a σ hR hSR.1 hs hr hne
    hks hkr hf hrb ep badge grant ?_) fun _ ⟨h1, h2, h3, h4⟩ =>
      ⟨h1, h2, ⟨h3, ntfn_lift_rcv hP0.toC hSR.2 h2 hr (h4.mono fun _ h => h.1) (fun p hp => by simp [hp]) hkr
        (by simp only [updK_kheap, Function.update_self]; exact rfl) (xferTcb_state _ _ _)⟩, h4⟩
  intro _ sb tag hsb hext
  have hsb' : sb = 0#u64 ↔ ipcBufOf false xs = none := by
    rcases hsb with ⟨h1, h2⟩ | ⟨sp, h1, h2, -⟩
    · exact ⟨fun _ => h1, fun _ => h2⟩
    · rw [h1]; exact ⟨fun h => absurd h h2, fun h => by cases h⟩
  have hsm : ∀ sp, ipcBufOf false xs = some sp → BufMap B sb sp := by
    intro sp h
    rcases hsb with ⟨h1, -⟩ | ⟨sp', h1, -, h3⟩
    · rw [h1] at h; cases h
    · rw [h1] at h; cases h; exact h3
  refine WP.spec_mono (lookup_extra_top hP0 hB hIR (hB.tcbT hks) sb (ipcBufOf false xs) hsb' hsm tag
    (Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register))
    (by show tag.extra_caps.bv.toNat = _; rw [hext]) (by show tag.extra_caps.bv.toNat ≤ 3; rw [hext]; exact extra_le3 _))
    fun _ ⟨l, hl, _⟩ => ⟨l, hl⟩

/-- **The step lemmas with grants** (G4): the bundle with `GC := True`,
the transfers carrying caps, on `SRT … SRE`; the other fields as in
`IpcSchedHyps.steps`. -/
theorem IpcSchedHyps.stepsG (hH : IpcSchedHyps st ar N T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hBf : EpBufHyps st T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hBm : EpBufMapHyps st T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hP0 : IPlaced N T E R B) :
    EpStepsBuf st A ar T E R B (SRN st N T (SRS st T (SRT st N T C E R B c (SRE st N T C E R B c))))
      (fun ts => tsCode ts ≠ 6) True :=
  let h := hH.steps hBf hBm hP0
  { ns_ep := h.ns_ep, deq := h.deq, link := h.link, unlink := h.unlink, sts := h.sts, push := h.push,
    xregs := fun hP s a σ hR hSR _ _ hs hr hne _ _ hks hkr hf hrb ep badge grant _ =>
      do_ipc_transfer_regsT hH hBf hBm hP0 hP s a σ hR hSR hs hr hne hks hkr hf hrb ep badge grant
    xbuf := fun hP s a σ hR hSR _ _ hs hr hne _ _ hks hkr hf _ hrb ep badge grant _ =>
      do_ipc_transfer_grant hH hBf hBm hP0 hP s a σ hR hSR hs hr hne hks hkr hf hrb ep badge grant }

end Grant

end

end Fl4Proofs.P3.Ipc
