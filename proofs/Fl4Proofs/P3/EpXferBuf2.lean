/-
P3 (DESIGN.md §9), endpoints: **FL4's `do_ipc_transfer` refines l4v
`do_ipc_transfer` when the receiver has an IPC buffer**
(`do_ipc_transfer_buf`): sender without fault, no extra caps; the sender's
buffer may be absent. The message registers, then (with a sender buffer)
the buffer words `5 .. len` (`copy_mrs_rel`), the message info
`⦇len', 0, 0, label⦈` and the badge.

`EpBufMapHyps` (the IPC-buffer frame mapping, a hypothesis): when the spec
finds a buffer `p` for a TCB, FL4's `lookup_ipc_buffer` returns a nonzero
kernel address `w` whose first 128 words are mapped to `p`'s (`BufMap`);
the receiver's buffer words are in user data frames (`inUserFrame`); and
l4v's receive-slot lookup (`get_receive_slots`, CSpace, whose result is
unused without caps) has one outcome and changes nothing.
-/
import Fl4Proofs.P3.EpXferBuf
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Hyps
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]

/-- The IPC-buffer frame mapping (see the module docstring). -/
structure EpBufMapHyps (T E R : Set U64) (B : Set (U64 × Fl4Spec.Word)) (SR : S → Fl4Spec.State Unit → Prop) :
    Prop where
  lookupMap : ∀ s σ (t : U64) (x : Fl4Spec.Tcb) (b : Bool) (p : Fl4Spec.ObjRef), EpStateRel T E R B (L.mem s) σ →
    SR s σ → t ∈ T → σ.kheap t.bv = some (.tcb x) → ipcBufOf b x = some p →
    msg.lookup_ipc_buffer st s b t ⦃ w => w ≠ 0#u64 ∧ BufMap B w p ⦄
  frame : ∀ s σ (t : U64) (x : Fl4Spec.Tcb) (p : Fl4Spec.ObjRef), EpStateRel T E R B (L.mem s) σ → SR s σ →
    t ∈ T → σ.kheap t.bv = some (.tcb x) → ipcBufOf true x = some p →
    ∀ k, k < 128 → Fl4Spec.inUserFrame (bufAddr p k) σ
  recvSlots : ∀ s σ (t : U64) (x : Fl4Spec.Tcb) (p : Fl4Spec.ObjRef), EpStateRel T E R B (L.mem s) σ → SR s σ →
    t ∈ T → σ.kheap t.bv = some (.tcb x) → ipcBufOf true x = some p →
    ∃ sl, Fl4Spec.getReceiveSlots (Z := Unit) t.bv (some p) σ = ({(sl, σ)}, False)

end Hyps

theorem ipcBufOf_copyRegs (b : Bool) (x : Fl4Spec.Tcb) (v : Fl4Spec.Register → Fl4Spec.Word)
    (rs : List Fl4Spec.Register) : ipcBufOf b (copyRegsTcb x v rs) = ipcBufOf b x := by
  rw [copyRegsTcb_other]; rfl

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st] {T E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {SR : S → Fl4Spec.State Unit → Prop}

/-- The sender's buffer: none, or a mapped one. -/
theorem lookup_send_buf (hBf : EpBufHyps st T E R B SR) (hBm : EpBufMapHyps st T E R B SR) (s : S)
    (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ) {t : U64} (ht : t ∈ T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) :
    msg.lookup_ipc_buffer st s false t ⦃ w => (ipcBufOf false x = none ∧ w = 0#u64) ∨
      (∃ sp, ipcBufOf false x = some sp ∧ w ≠ 0#u64 ∧ BufMap B w sp) ⦄ := by
  cases h : ipcBufOf false x with
  | none =>
    exact WP.spec_mono (hBf.lookup s σ t x false hR hSR ht hk) fun w hw => Or.inl ⟨rfl, hw.2 h⟩
  | some sp =>
    exact WP.spec_mono (hBm.lookupMap s σ t x false sp hR hSR ht hk h) fun w hw => Or.inr ⟨sp, rfl, hw⟩

/-- **`do_ipc_transfer` with a receive buffer** (see the module docstring). -/
theorem do_ipc_transfer_buf (hH : EpHyps st T E R B SR) (hBf : EpBufHyps st T E R B SR)
    (hBm : EpBufMapHyps st T E R B SR) (hP : EPlaced T E R B)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr)) (hf : xs.tcbFault = none)
    {rp : Fl4Spec.ObjRef} (hrb : ipcBufOf true xr = some rp) (ep badge : U64) (grant : Bool)
    (hcaps : grant = false ∨ ipcBufOf false xs = none ∨
      Fl4Spec.unat (Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miExtraCaps = 0)
    (epo : Option Fl4Spec.ObjRef := some ep.bv) :
    ipc.do_ipc_transfer st ar s a snd ep badge grant rcv ⦃ s' => ∃ σ',
      Fl4Spec.doIpcTransfer (Z := Unit) snd.bv epo badge.bv grant rcv.bv σ = ({((), σ')}, False) ∧
      EpStateRel T E R B (L.mem s') σ' ∧ SR s' σ' ∧
      Agree (L.mem s) (L.mem s') (fun b => ¬ RcvReg rcv b ∧ ¬ BufW B b) ∧
      (∀ p, p ≠ rcv.bv → σ'.kheap p = σ.kheap p) ∧
      ∃ x', σ'.kheap rcv.bv = some (.tcb x') ∧ x'.tcbState = xr.tcbState ⦄ := by
  have hra := hP.tcb rcv hr
  have hxs := hR.at_tcb hs hks
  have hwmi : (L.mem s (regA snd layout.reg.MSG_INFO)).bv = xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register := by
    rw [← regIdx_msgInfo]; exact hxs.regs _
  have hu := hBm.frame s σ rcv xr rp hR hSR hr hkr hrb
  unfold ipc.do_ipc_transfer
  refine WP.spec_bind (hBm.lookupMap s σ rcv xr true rp hR hSR hr hkr hrb) ?_
  rintro rw ⟨hrw0, hmr⟩
  step as ⟨ft, hft⟩
  have hft0 : ft = fl4_abi.consts.fault.NullFault := by
    rw [hft, hxs.fault0.2 hf]; unfold fl4_abi.consts.fault.NullFault; rfl
  simp only [hft0, ↓reduceIte]
  refine WP.spec_bind (lookup_send_buf hBf hBm s σ hR hSR hs hks) ?_
  rintro sw hsw
  unfold ipc.do_normal_transfer
  refine WP.spec_bind (msg_info_spec (L := L) s snd) ?_
  rintro tag ⟨hlab, hlen, hext, hle⟩
  have hex : (if grant = true then (do
        let r ← ipc.lookup_extra_caps st s snd sw tag
        match r with
        | core.result.Result.Ok e => ok e
        | core.result.Result.Err _ => ok ipc.NO_EXTRA_CAPS)
      else ok ipc.NO_EXTRA_CAPS) ⦃ e => e = ipc.NO_EXTRA_CAPS ⦄ := by
    cases grant with
    | false => simp
    | true =>
      simp only [↓reduceIte]
      have hc : sw = 0#u64 ∨ tag.extra_caps = 0#u64 := by
        rcases hcaps with h | h | h
        · cases h
        · rcases hsw with ⟨-, h'⟩ | ⟨sp, h', -⟩
          · exact Or.inl h'
          · rw [h] at h'; cases h'
        · right; apply eq_of_bv; rw [hext, hwmi]; apply BitVec.eq_of_toNat_eq; exact h
      refine WP.spec_bind (lookup_extra_caps_none s snd sw tag hc) ?_
      rintro r rfl
      simp
  refine WP.spec_bind hex ?_
  rintro extra rfl
  refine WP.spec_bind (copy_mrs_rel hH hP s σ hR hSR hs hr hne hks hkr hmr hrw0 hu hsw tag.length hle) ?_
  rintro ⟨n, s1⟩ ⟨σc, hcopy, hkcf, hRc, hSc, hAc, hn, -⟩
  simp only at hcopy hkcf hRc hSc hAc hn
  have hkc : σc.kheap rcv.bv = some (.tcb (copyRegsTcb xr xs.tcbArch.tcbContext.userRegs
      (Fl4Spec.msg_registers.take tag.length.val))) := by rw [hkcf]; simp
  refine WP.spec_bind (transfer_caps_noextra (L := L) s1 tag ep rcv rw) ?_
  rintro ⟨out, s2⟩ hout
  simp only [Prod.mk.injEq] at hout
  obtain ⟨rfl, h2⟩ := hout
  subst s2
  show (do
    let s3 ← msg.set_msg_info st s1 rcv
      { label := tag.label, caps_unwrapped := 0#u64, extra_caps := 0#u64, length := n }
    obj.Tcb.set_reg st rcv s3 layout.reg.BADGE badge) ⦃ _ ⦄
  refine WP.spec_bind (set_msg_info_spec (L := L) s1 rcv tag.label n (by omega)) ?_
  rintro s3 ⟨v, hs3, hv⟩
  step as ⟨s4, hs4⟩
  subst hs3 hs4
  set w := xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register with hwdef
  set x1 := copyRegsTcb xr xs.tcbArch.tcbContext.userRegs (Fl4Spec.msg_registers.take tag.length.val)
  have hlenw : tag.length.bv = (Fl4Spec.dataToMessageInfo w).miLength := by rw [hlen, hwmi]
  -- the receive slots
  obtain ⟨sl, hsl⟩ := hBm.recvSlots s1 σc rcv x1 rp hRc hSc hr hkc (by rw [ipcBufOf_copyRegs]; exact hrb)
  have hcopy' := hcopy
  rw [hlenw] at hcopy'
  have hspec := doIpcTransfer_recvBuf hks hkr hf hrb epo badge.bv grant hcaps hcopy' hkc hsl
  -- the two register writes
  obtain ⟨hR2, hW2, hS2⟩ := write_reg_rel hP s1 _ hRc hr hkc Fl4Spec.msg_info_register v
  rw [regIdx_msgInfo] at hR2 hW2
  have hkc2 : (updK σc rcv.bv (.tcb (setReg x1 Fl4Spec.msg_info_register v.bv))).kheap rcv.bv =
      some (.tcb (setReg x1 Fl4Spec.msg_info_register v.bv)) := by simp
  obtain ⟨hR3, hW3, hS3⟩ := write_reg_rel hP _ _ hR2 hr hkc2 Fl4Spec.badge_register badge
  rw [regIdx_badge] at hR3 hW3
  have hvx : v.bv = Fl4Spec.messageInfoToData ⟨n.bv, 0, 0, (Fl4Spec.dataToMessageInfo w).miLabel⟩ := by
    rw [hv]; congr 2; rw [hlab, hwmi]; rfl
  have hfin : updK (updK σc rcv.bv (.tcb (setReg x1 Fl4Spec.msg_info_register v.bv))) rcv.bv
      (.tcb (setReg (setReg x1 Fl4Spec.msg_info_register v.bv) Fl4Spec.badge_register badge.bv)) =
      updK σc rcv.bv (.tcb (setReg (setReg x1 Fl4Spec.msg_info_register (Fl4Spec.messageInfoToData
        ⟨n.bv, 0, 0, (Fl4Spec.dataToMessageInfo w).miLabel⟩)) Fl4Spec.badge_register badge.bv)) := by
    simp only [updK, Function.update_idem]; rw [hvx]
  rw [hfin] at hR3
  have hS := hH.stable _ _ _ _ (hH.stable _ _ _ _ hSc hW2 hS2) hW3 hS3
  rw [hfin] at hS
  refine ⟨_, hspec, hR3, hS, ?_, ?_, setReg (setReg x1 Fl4Spec.msg_info_register (Fl4Spec.messageInfoToData
    ⟨n.bv, 0, 0, (Fl4Spec.dataToMessageInfo w).miLabel⟩)) Fl4Spec.badge_register badge.bv,
    by simp only [updK_kheap, Function.update_self]; rfl, ?_⟩
  · intro b hb hn'
    have hn1 : ¬ RcvMR rcv b := fun ⟨r, _, h⟩ => hn'.1 ⟨r, h⟩
    rw [badgeRegA_eq_regA, ← regIdx_msgInfo,
      rd_wr_ne (a_reg hra Fl4Spec.badge_register).1 hb (fun h => hn'.1 ⟨Fl4Spec.badge_register, by rw [← h]⟩),
      rd_wr_ne (a_reg hra Fl4Spec.msg_info_register).1 hb (fun h => hn'.1 ⟨Fl4Spec.msg_info_register, by rw [← h]⟩)]
    exact hAc b hb ⟨hn1, hn'.2⟩
  · intro p hp
    simp only [updK_kheap, Function.update_of_ne hp, hkcf]
  · rw [setReg_state, setReg_state, copyRegsTcb_state]

end

end

end Fl4Proofs.P3.Endp
