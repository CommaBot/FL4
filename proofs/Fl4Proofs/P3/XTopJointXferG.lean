/-
P3 (DESIGN.md §9), IPC: **`do_ipc_transfer` with a cap granted** (toward
XTopJointSendPushD's `JSendRecvHyp`), on `IRel` inside the dequeued interval
of a send to a waiting receiver, with the insert as a trace (IpcGrantTr).

* `copy_mrs_rgB`, `wr_reg_rg`, `updK_um_updK`: helpers.
* `do_ipc_transfer_grantG`: IpcGrantX's `do_ipc_transfer_grant` with the
  FL4 footprint (the receiver's registers, its buffer words, slot words) and
  the insert trace: no insert (the spec's outcome the start's up to user
  memory and the receiver's TCB, the slots kept) or one (`InsRec` at the
  state after the copy, the sources' and the receive slot's CNodes live at
  the start).
-/
import Fl4Proofs.P3.XTopJointXferB
import Fl4Proofs.P3.XTopJointGrant
import Fl4Proofs.P3.IpcGrantTr
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

section GrantG
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- `copy_mrs` writes the receiver's registers and buffer words only. -/
theorem copy_mrs_rgB {T1 : Set U64} (hT : P1.TcbPlaced T1) {rcv : U64} (hr : rcv ∈ T1) {rw : U64}
    (hrw0 : rw ≠ 0#u64) (hal : ∀ i : U64, i.val < 128 → P1.Aligned (fl4BufA rw i)) {s : S} {snd : U64}
    (sw n : U64) :
    msg.copy_mrs st s snd sw rcv rw n ⦃ r => P1.WritesIn st s r.2 (Fl4Proofs.P3.XferBW T1 rw) ⦄ := by
  unfold msg.copy_mrs
  refine WP.spec_bind (Fl4Proofs.P3.copy_mrs_loop0_rg (snd := snd) (n := n) hT hr (P1.WritesIn.refl s _)) ?_
  rintro ⟨s1, i⟩ h1
  have h1' : P1.WritesIn st s s1 (Fl4Proofs.P3.XferBW T1 rw) := h1.mono fun b hb => Or.inl hb
  simp only [hrw0, ↓reduceIte]
  by_cases hsw0 : sw = 0#u64
  · simp only [hsw0, ↓reduceIte]
    first | exact (WP.spec_ok _).2 h1' | (simp only [WP.spec_ok]; exact h1')
  · simp only [hsw0, ↓reduceIte]
    exact Fl4Proofs.P3.copy_mrs_loop1_rb hal (fun b hb => Or.inr hb) s1 h1' sw _ i

/-- A register write of a thread of `T1` lies in `XferRegW T1 ∅`. -/
theorem wr_reg_rg {T1 : Set U64} (hT1 : P1.TcbPlaced T1) {t : U64} (ht : t ∈ T1) (s : S) {r : U64}
    (hr : r.val < 384) (v : U64) : P1.WritesIn st s (L.wr s (regA t r) v) (XferRegW T1 ∅) := by
  have h1 := Fl4Proofs.P1.obj.Tcb.set_reg.rg (st := st) (s := s) (r := r) (v := v) hT1 ht hr
  have h2 := Fl4Proofs.P3.Endp.obj.Tcb.set_reg.spec (st := st) s t r v
  obtain ⟨s', -, h1', h2'⟩ := spec_exists (WP.spec_and h1 h2)
  rw [← h2']; exact h1'

theorem updK_um_updK (τ : Fl4Spec.State Unit) (p : Fl4Spec.ObjRef) (o o' : Fl4Spec.KernelObject)
    (u u' : Fl4Spec.Word → Fl4Spec.Word8) :
    Notif.updK (Endp.setUm (Notif.updK (Endp.setUm τ u') p o) u) p o' = Notif.updK (Endp.setUm τ u) p o' := by
  simp only [Notif.updK, Endp.setUm, Function.update_idem]

set_option maxHeartbeats 8000000 in
/-- **`do_ipc_transfer` with a receive buffer, caps granted, with the insert
trace** (module docstring). -/
theorem do_ipc_transfer_grantG (hH : IpcCore st N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hBf : EpBufHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hBm : EpBufMapHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hP0 : IPlaced N T E R B) (hP : EPlaced T E R B)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ)
    (hSR : SRN st N T (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c))) s σ)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr)) (hf : xs.tcbFault = none)
    {rp : Fl4Spec.ObjRef} (hrb : ipcBufOf true xr = some rp) (hOK : IpcBufCapOK σ) (ep badge : U64) (grant : Bool)
    {T1 : Set U64} (hT1 : P1.TcbPlaced T1) (hr1 : rcv ∈ T1) :
    ipc.do_ipc_transfer st ar s a snd ep badge grant rcv ⦃ s' => ∃ (σ' : Fl4Spec.State Unit) (x' : Fl4Spec.Tcb),
      Fl4Spec.doIpcTransfer (Z := Unit) snd.bv (some ep.bv) badge.bv grant rcv.bv σ = ({((), σ')}, False) ∧
      EpStateRel T E R B (L.mem s') σ' ∧
      SRN st N T (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c))) s' σ' ∧
      Agree (L.mem s) (L.mem s') (fun b => AllTF T b ∧ ¬ RcvReg rcv b ∧ ¬ BufW B b) ∧
      KeepNC σ σ' rcv.bv ∧ σ'.kheap rcv.bv = some (.tcb x') ∧ x' = { xr with tcbArch := x'.tcbArch } ∧
      WritesIn st s s' (fun b => XferRegW T1 ∅ b ∨ RBufW ⟨rp⟩ b ∨ Sched.SlotWd th b) ∧
      ((∃ um, σ' = Notif.updK (Endp.setUm σ um) rcv.bv (.tcb x') ∧ SlotsSame th (L.mem s) (L.mem s')) ∨
       ∃ (s1 : S) (x1 : Fl4Spec.Tcb) (um0 : Fl4Spec.Word → Fl4Spec.Word8) (caps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
         (slots : List Fl4Spec.CslotPtr) (sk' : S) (σc : Fl4Spec.State Unit) (um : Fl4Spec.Word → Fl4Spec.Word8),
         SlotsSame th (L.mem s) (L.mem s1) ∧ L.ksb s1 = L.ksb s ∧
         InsRec (L := L) th caps slots s1 (Notif.updK (Endp.setUm σ um0) rcv.bv (.tcb x1)) sk' σc ∧
         σ' = Notif.updK (Endp.setUm σc um) rcv.bv (.tcb x') ∧ SlotsSame th (L.mem sk') (L.mem s') ∧
         (∀ j (hj : j < caps.length), ∃ ps, (caps[j]).2.1 = ps.bv ∧ DestLive th (L.mem s) (L.ksb s) ps) ∧
         (∀ d ∈ slots, ∃ pd, d.1 = pd.bv ∧ DestLive th (L.mem s) (L.ksb s) pd)) ⦄ := by
  have hra := hP.tcb rcv hr
  have hxs := hR.at_tcb hs hks
  have hwmi : (L.mem s (regA snd layout.reg.MSG_INFO)).bv = xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register := by
    rw [← regIdx_msgInfo]; exact hxs.regs _
  have hIR := (IpcRel.ofSRN hR hSR).1
  obtain ⟨⟨⟨G, hB⟩, hBw⟩, -⟩ := hSR.1.1
  have hEH := hH.epHyps hP0
  have hu := hBm.frame s σ rcv xr rp hR hSR.1.1 hr hkr hrb
  unfold ipc.do_ipc_transfer
  have hlb := lookup_buf_full s σ hB.2.1.1 hB.2.1.2.1 (RelTopB.tcbT hB hkr) hkr hOK true
  obtain ⟨x0, hk0, hbw⟩ := hBw.bw rcv hr
  rw [hkr] at hk0; cases hk0
  refine WP.spec_bind (WP.spec_and (hBm.lookupMap s σ rcv xr true rp hR hSR.1.1 hr hkr hrb) hlb) ?_
  rintro rw ⟨⟨hrw0, hmr⟩, hwl⟩
  have hrwe : rw = ⟨rp⟩ := by
    have hwb : rw.bv = rp := hwl.2 hbw rp hrb
    rw [← hwb]
  subst hrwe
  have hal : ∀ i : U64, i.val < 128 → P1.Aligned (fl4BufA ⟨rp⟩ i) := fun i hi => (hP.balign _ (hmr i hi)).1
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
        ExtraOK th (L.mem s) extra caps ∧ ExtraLive th (L.mem s) (L.ksb s) extra ⦄ := by
    have hnl : ExtraLive th (L.mem s) (L.ksb s) ipc.NO_EXTRA_CAPS :=
      fun j hj hne => absurd (Ipc.exAt_none j hj) hne
    cases grant with
    | false =>
      rw [if_neg (by decide), WP.spec_ok]
      exact ⟨[], rfl, extraOK_none th _, hnl⟩
    | true =>
      rw [if_pos rfl]
      refine WP.spec_bind (WP.spec_and (lookup_extra_top hP0 hB hIR (hB.tcbT hks) sw (ipcBufOf false xs) hsb' hsm
        tag (Fl4Spec.dataToMessageInfo w) (by show tag.extra_caps.bv.toNat = _; rw [hext, hwmi]) hn3)
        (lookup_extra_live th s σ hB.2.1.1 hB.2.1.2.1 (hB.tcbT hks) sw tag)) ?_
      rintro r ⟨⟨caps, hc, hok⟩, hl⟩
      cases r with
      | Ok e => simp only [WP.spec_ok]; exact ⟨caps, by simp only [↓reduceIte]; exact hc, hok, hl _ rfl⟩
      | Err _ => simp only [WP.spec_ok]; exact ⟨caps, by simp only [↓reduceIte]; exact hc, hok, hnl⟩
  refine WP.spec_bind hex ?_
  rintro extra ⟨caps, hlk, hok, hlive⟩
  refine WP.spec_bind (WP.spec_and (copy_mrs_rel hEH hP s σ hR hSR.1 hs hr hne hks hkr hmr hrw0 hu hsw tag.length hle)
    (copy_mrs_rgB hT1 hr1 hrw0 hal sw tag.length (snd := snd))) ?_
  rintro ⟨n, s1⟩ ⟨⟨σc, hcopy, hkcf, hRc, hSc, hAc, hn, hWc, hEc⟩, hF1⟩
  simp only at hcopy hkcf hRc hSc hAc hn hWc hEc hF1
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
  refine WP.spec_bind (transfer_caps_topG hP0 hB1 hIR1 hSE1 tag (Fl4Spec.dataToMessageInfo w) hlenw hlabw hok1.1
    hok1.2.1 hok1.2.2 ep rcv ⟨rp⟩ (some rp) ⟨fun h => absurd h hrw0, fun h => by cases h⟩
    (fun rb h => by cases h; exact ⟨hmr, hBm.frame s1 σc rcv x1 rp hRc hSc.1 hr hkc hrb1⟩)
    (fun rb h => by cases h; exact hBm.recvSlots s1 σc rcv x1 rp hRc hSc.1 hr hkc hrb1)
    (fun rb h => by cases h; exact get_receive_slot_top hP0 hB1 hIR1.toE (hB1.tcbT hkc) hmr hrw0 caps extra)
    (fun rb h => by cases h; exact get_receive_slot_live th s1 σc hB1.2.1.1 hB1.2.1.2.1 (hB1.tcbT hkc) ⟨rp⟩)) ?_
  rintro ⟨out, s2⟩ ⟨σt, mf, htc, hMi, hexc, hIRt, hcu, he3, hlbt, hSEt, ⟨hKC, hWt⟩, ⟨G', hBt⟩, htr, hWr⟩
  simp only at hMi hexc hIRt hcu he3 hSEt hWt hBt htr hWr
  show (do
    let s3 ← msg.set_msg_info st s2 rcv { out with length := n }
    obj.Tcb.set_reg st rcv s3 layout.reg.BADGE badge) ⦃ _ ⦄
  refine WP.spec_bind (set_msg_info_specG (L := L) s2 rcv { out with length := n } (by show n.val < 128; omega)
    hcu (by show out.extra_caps.val < 4; omega)) ?_
  rintro s3 ⟨v, hs3, hv⟩
  step with Fl4Proofs.P3.Endp.obj.Tcb.set_reg.spec as ⟨s4, hs4⟩
  subst hs3 hs4
  have hkt : σt.kheap rcv.bv = some (.tcb x1) := by
    rcases hKC.1 rcv.bv with e | ⟨r, cs, cs', h1, -⟩
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
  have hSRS2 : SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c)) s2 σt :=
    ⟨⟨RelTopI.of_B (hSR.1.1.1.stableE hWc hEc) hBt hWt (fun b hb => by
        rcases hb with h | ⟨wp, hw, rfl⟩
        · exact Or.inr (Or.inr (Or.inr h))
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨wp, hw, le_refl _, by omega⟩)))))
      (fun b hb => by
        have hP := hSR.1.1.1.eplaced
        rcases hb with h | ⟨wp, hw, rfl⟩
        · exact Or.inr (slotWd_nobuf hB.2.2.2.2.2.1 hB.1 hP.tcb h)
        · exact Or.inr (NoBufW.out hP.tcb fun t ht => by have := hP.bt wp hw t ht; omega))
      hKC.vsKeep, hSEt⟩, ScRelM.of hIRt⟩
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
  -- the register writes keep the slots and lie in the receiver's registers
  have hW24 : WritesIn st s2 (L.wr (L.wr s2 (regA rcv layout.reg.MSG_INFO) v) (regA rcv layout.reg.BADGE) badge)
      (XferRegW T1 ∅) :=
    ((wr_reg_rg hT1 hr1 s2 (by simp [layout.reg.MSG_INFO, layout.reg.RSI]) v).trans
      (wr_reg_rg hT1 hr1 _ (by simp [layout.reg.BADGE, layout.reg.RDI]) badge)).mono fun b hb => hb.elim id id
  have hS24 : SlotsSame th (L.mem s2)
      (L.mem (L.wr (L.wr s2 (regA rcv layout.reg.MSG_INFO) v) (regA rcv layout.reg.BADGE) badge)) := by
    have hm1 : P1.Aligned (regA rcv layout.reg.MSG_INFO) := by
      rw [← regIdx_msgInfo]; exact (a_reg hra _).1
    have hm2 : P1.Aligned (regA rcv layout.reg.BADGE) := by
      rw [← regIdx_badge]; exact (a_reg hra _).1
    refine slotsSame_of_iwords hBt.1 hBt.2.2.2.2.2.1 ((writesIn_wr (v := v) hm1).trans (writesIn_wr (v := badge) hm2))
      fun b hb => Or.inl ⟨rcv, hr, ?_⟩
    rcases hb with rfl | rfl
    · rw [← regIdx_msgInfo, regA_val hra (regIdx_lt _)]; have := regIdx_lt Fl4Spec.msg_info_register; omega
    · rw [← regIdx_badge, regA_val hra (regIdx_lt _)]; have := regIdx_lt Fl4Spec.badge_register; omega
  obtain ⟨um0, hσc⟩ : ∃ um, σc = Notif.updK (Endp.setUm σ um) rcv.bv (.tcb x1) := ⟨_, Fl4Proofs.P3.epStep_form hEc hkcf⟩
  refine ⟨_, _, hspec, hR3, ⟨hSf, hNf⟩, ?_, ?_, by simp only [updK_kheap, Function.update_self]; rfl,
    Fl4Proofs.P3.setReg2_eqA xr _ _ _ _ _ _, ?_, ?_⟩
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
    rcases hKC.1 p with e | ⟨r, cs, cs', h1, h2⟩
    · left; rw [e, hkco p hp]
    · right; left; exact ⟨r, cs, cs', by rw [← hkco p hp]; exact h1, h2⟩
  · refine ((hF1.trans hWr).trans hW24).mono fun b hb => ?_
    rcases hb with (h | h) | h
    · rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases h with h | h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
    · exact Or.inl h
  · rcases htr with ⟨⟨um, hσt⟩, hSS⟩ | ⟨rb, slots, hrb', hsl, ⟨sk', σcI, hrec, ⟨um, hσt⟩, hSSk⟩, hDL⟩
    · left
      refine ⟨um, ?_, SlotsSame.trans' (SlotsSame.trans' hS1 hSS) hS24⟩
      rw [hσt, hσc]
      exact updK_um_updK σ rcv.bv _ _ um um0
    · right
      have hks1 : L.ksb s1 = L.ksb s := hWc.1
      refine ⟨s1, x1, um0, caps, slots, sk', σcI, um, hS1, hks1, hσc ▸ hrec, by rw [hσt], SlotsSame.trans' hSSk hS24,
        fun j hj => ?_, fun d hd => ?_⟩
      · obtain ⟨ps, rs, idx, cv, hps, hls, hsl', hxa, -⟩ := hok.2.1 j hj
        have hA : AbsSlot th (ps.bv, idx) := ⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩
        have hne0 : exAt extra j ≠ 0#u64 := by rw [hxa]; exact hA.isSlot.ne_zero hB.1
        obtain ⟨ps', idx', he', hth', hD'⟩ := hlive j (by have := hok.1; omega) hne0
        have e := cslotAddr_inj hB.1 hA (⟨ps', rfl, Or.inl hth'⟩ : AbsSlot th (ps'.bv, idx')) (hxa.symm.trans he')
        exact ⟨ps', by rw [hsl']; exact congrArg Prod.fst e, hD'⟩
      · obtain ⟨pd, h1, h2⟩ := hDL d hd
        exact ⟨pd, h1, h2.same (SlotsSame.symm' hS1) hks1.symm⟩

end GrantG

end

end Fl4Proofs.P3.Ipc
