/-
# P2 (line mmuAD, gen 17): **PageMap in VM epochs, part C** — `acc`, `move`, `ReadOnce` at the VM entry

Copies at `PmPreGX` / `K.uV.ptU` (E2EPAD2A / E2EPAD2B) of InvPmTop3's `pm_accU_of_blkG`, InvPmMvB's `pmAccG2`,
InvPmMvC's `pm_mvG` (the per-write check: `stepOKV_of_stepOK` at `RegionOKV`, no `vcpus = ∅`), InvPmRoB's `pmAccN`,
InvPmRoC's `PmRN` / `PmWN` / `pm_replyOnce` / `pm_tailOnce` / `pm_decOnce`, InvPmRoD's `pm_entOnce`, InvPmRoE's
`pm_roAG`. The VM-specific facts are the ones of E2EPAD2B (walk, leaf, buffer, slot 0).

No named premise. New module; no existing statement changes.
-/
import Fl4Proofs.P2.E2EPAD2B
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField NullOrFrame TcbSlot)
open Fl4Proofs.P2.E2E (Once ReadOnce StartAt SP)
open Fl4Proofs.P2.Serial (Cfg Init ArmInv NoLoc RunAll)

noncomputable section

section oblY
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP} {μ : U64 → U64}
variable {A : Type} {ar : machine.Arch A}

/-- **`acc` from the decode block at `PmPreG`** (gen 12's `pm_accU_of_blkX` via stpost's `inv_acc_gen2`). -/
theorem pm_accU_of_blkGX (hA : P0.ArchTotal ar) (hK : RegionOKP K) {number : I64}
    (hblk : PmBlkUW2X st ar p K Locks (PmPreGX st Cs Ω Sg Ac Locks p K μ)) :
    PmAccUW st ar number p K Locks (PmPreGX st Cs Ω Sg Ac Locks p K μ) := fun s a _ _ hE h => by
  obtain ⟨⟨hJ, hq, hG⟩, -, -⟩ := id hE
  have P := hq.1.1.1.ptUX hG
  obtain ⟨-, -, -, -, -, -, hsl, -, -, -⟩ := pm_core hq
  obtain ⟨-, hf⟩ := P.lay.slot8 _ hsl
  have r0 : IoRS (st := st) K.uV.ptU Locks s p.slot := by
    have := pm_slotRSX hJ hq P (o := 0#u64) (by simp) (by simp)
    rwa [wadd_zero hf] at this
  have r8 := pm_slotRSX hJ hq P (o := 8#u64) (by simp) (by simp)
  haveI : GRd (guard st (PmRSU st K Locks s) (PmWSU st K Locks s)) st (IoRS (st := st) K.uV.ptU Locks s) :=
    grd_sub (fun _ hy => pmRSU_ioRSX hG hy)
  exact inv_acc_gen2 (W := PmWSU st K Locks s) hA P
    ((P.ioWr (Locks := Locks)).mono (fun _ hy => pmWSU_ioWSX hK hy)) (pm_seenX hJ hq P) ⟨r0, r8⟩
    (fun info nx s1 s2 a1 buf length cap emi hc hl hk =>
      hblk s a info nx s1 s2 a1 buf length cap hE emi hc hl hk) h

end oblY

section accM
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP} {μ : U64 → U64}
variable {A : Type} {ar : machine.Arch A}

/-- **`pmAccGX` for stores that check the `STATE` write per value and the slot's `CAP0` write per word** (module
docstring). -/
theorem pmAccG2X (hA : P0.ArchTotal ar) {s : S} {a : A} {info : msginfo.MessageInfo} {nx : U64} {s1 s2 : S} {a1 : A}
    {buf length : U64} {cap : capability.Cap} {y : (core.result.Result Unit error.Exc) × S × A}
    {R W : U64 → Prop} {gS : machine.Store S} [GRd gS st R] [GWr gS st W]
    (hE : PmPreGX st Cs Ω Sg Ac Locks p K μ s)
    (hR : ∀ b, IoRS (st := st) K.uV.ptU Locks s b → R b) (hRu : ∀ b, UserW K.toKLayout b → R b)
    (hRe : ∀ b, PmRS st K Locks s b → R b)
    (hW : IoWr st W K.heap.scBits s)
    (hsw : ∀ v, v = sched.TS_RESTART ∨ v = sched.TS_RUNNING → SWr gS st (L.curW s) v)
    (hc0 : ∀ x v, OwnMap.NullOrFrame v → gS.write x p.slot v = st.write x p.slot v)
    (hW8 : W (core.num.U64.wrapping_add p.slot 8#u64))
    (hWu : ∀ b, UserW K.toKLayout b → W b) (hWe : ∀ b, b ∈ K.ptes → W b)
    (emi : msg.msg_info st s (L.curW s) = ok info) (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1)
    (hcap : obj.Slot.cap st p.slot s2 = ok cap)
    (hy : syscall.decode_invocation st ar s2 a1 info.label length p.slot cap true true true false buf p.extra =
      ok y) :
    syscall.decode_invocation gS ar s2 a1 info.label length p.slot cap true true true false buf p.extra = ok y ∧
    ∀ z, invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z → invRep gS (L.curW s) y.2.1 y.2.2 y.1 = ok z := by
  obtain ⟨fp, rt, asid, va, mp, x0, root, rasid, e, hcs, hcs2, hx0, hxK, hcx2, hcv2, hpe2, hpt, hle, hRS, hWS, hu,
    hf, hsl, hsl0, hO⟩ := pm_s2X hA hE C
  have hE0 := hE
  obtain ⟨⟨hJ, hq, hG⟩, -, -⟩ := hE
  have Pb := hq.1.1.1
  have P := Pb.ptUX hG
  -- the decode's first reads and its walk on `gS` (a store reading `IoRS (ptU K) s` as `st`)
  haveI hIo : GRd gS st (IoRS (st := st) K.uV.ptU Locks s) :=
    { read := fun hy s => GRd.read (g := gS) (hR _ hy) s
      read_pair := fun hy h8 s => GRd.read_pair (g := gS) (hR _ hy) (hR _ h8) s
      ks_base := gst_ks_base
      cur_cpu := gst_cur_cpu
      frame_masks := gst_frame_masks }
  obtain ⟨-, -, hargs, x0', root', rasid', hx0', hcxg, hcx', -⟩ := pm_decRdX (gS := gS) hA hE0 C
  have hWk := pm_decWalkX (gS := gS) hA hE0 C (root := root) (rasid := rasid) hu
  clear hIo
  rw [hx0] at hx0'
  have ex0 : x0' = x0 := by have := ok_inj_ff hx0'; simpa using this.symm
  subst ex0
  rw [hcx2] at hcx'
  obtain ⟨e1, e2⟩ : root = root' ∧ rasid = rasid' := by
    have := ok_inj_ff hcx'; simp only [capability.Cap.Pml4.injEq] at this; exact ⟨this.1, this.2.2⟩
  subst e1 e2
  obtain ⟨-, es1, eu, eac, ey, ehere, -⟩ := C
  have Ent := P.ent (Locks := Locks) hW
  have Hf := here_facts ehere
  have I := IoS2.of_ent hA Ent es1 eu Hf.sc
  have hct : L.curW s2 = L.curW s := I.cur
  have hL : Slot8 K.uV.ptU := fun q hq => P.lay.slot8 q hq
  have w0 := prefix_writes ar hA P.tp P.np P.cT es1 eu
  have hcap' : cap = .Frame fp .Small rt false mp false asid va := by
    rw [hcs2] at hcap; exact (ok_inj_ff hcap).symm
  subst hcap'
  obtain ⟨-, -, -, -, -, -, -, hlab, -, -⟩ := pm_core hq
  have hlbl := (hlab info emi).1
  rw [hlbl] at hy ⊢
  have tk : ∀ k : U64, k.val < 4096 → k.val % 8 = 0 → k.val ≠ 392 →
      L.mem s2 (core.num.U64.wrapping_add (L.curW s) k) = L.mem s (core.num.U64.wrapping_add (L.curW s) k) :=
    fun k h1 h2 h3 => w0.2.2 _ (field_aligned P.tA h1 h2) (preW_tcb P.tA P.np P.cT h1 h3)
  -- the node, the caller's words (cmAcc8's)
  have hctR : R (L.nodeAt s2 (L.cpu s2) layout.node.CUR_THREAD) := by
    rw [I.cp, nodeAt_of_ksb I.k]
    exact hR _ (P.nd layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])).1
  have hN : ∀ x : S, (∀ o, L.nodeAt x (L.cpu x) o = L.nodeAt s (L.cpu s) o) → NodeSt (L := L) R W x := by
    have n0 : IoRS (st := st) K.uV.ptU Locks s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) :=
      (P.nd layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])).1
    have n1 : IoRS (st := st) K.uV.ptU Locks s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) :=
      (P.nd layout.node.SCHED_ACTION (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])).1
    have n1w : W (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) :=
      hW.nd _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
    intro x hn
    refine ⟨?_, ?_, ?_⟩
    · rw [hn]; exact hR _ n0
    · rw [hn]; exact hR _ n1
    · rw [hn]; exact n1w
  have hnd2 : ∀ o, L.nodeAt s2 (L.cpu s2) o = L.nodeAt s (L.cpu s) o := fun o => by
    rw [I.cp, nodeAt_of_ksb I.k]
  have rst := P.stw (Locks := Locks)
  have rsc : IoRS (st := st) K.uV.ptU Locks s (scA (L.curW s)) :=
    P.gate (off := 3464#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField])
  have riq : IoRS (st := st) K.uV.ptU Locks s (inqA (L.curW s)) :=
    (P.home (off := 3592#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).1
  have hmxR : IoRS (st := st) K.uV.ptU Locks s (maxA (L.cscW s)) := by
    have hmx := maxA_facts P.bxi.2.2.1.1 P.cscS
    exact P.cscacc.rd _ hmx.1 ⟨hmx.2.1, hmx.2.2⟩
  have hsc2 : L.mem s2 (scA (L.curW s)) = L.cscW s := by rw [← hct]; exact I.F.i
  have ha2 : L.actionW s2 = sched.ACTION_RESUME_CURRENT := by
    rw [eq_of_spec_fd (sched.action.spec (L := L) s2)] at eac; exact ok_inj_ff eac
  have hrun : L.mem s2 (stA (L.curW s)) = sched.TS_RESTART ∨ L.mem s2 (stA (L.curW s)) = sched.TS_RUNNING := by
    rw [I.st]; exact Ent.run
  have hK0 := SchedOK.of_sw I.F (by rw [hct]; exact Hf.sc) (by rw [hct]; exact Hf.nr)
  rw [hct] at hK0
  have hK : SchedOK (L := L) s2 (L.curW s) := hK0
  have hmx2 : IoRS (st := st) K.uV.ptU Locks s
      (maxA (L.mem (L.wr s2 (stA (L.curW s)) sched.TS_RESTART) (scA (L.curW s)))) := by
    have kw := (KeepA.refl ha2 hrun).wr hK (b := stA (L.curW s)) (v := sched.TS_RESTART) (Or.inr rfl)
      (fun _ => Or.inl rfl)
    have e : L.mem (L.wr s2 (stA (L.curW s)) sched.TS_RESTART) (scA (L.curW s)) = L.mem s2 (scA (L.curW s)) :=
      kw.mem (field_aligned P.tA (by simp) (by simp)) (iotw_field P.tA (by simp) (by simp))
    rw [e, hsc2]
    exact hmxR
  -- the layout `KSUPm (ptU K)`
  have hn2 : ∀ o : U64, o.val < 4288 → ¬ UserW (KSUPm K.uV.ptU) (L.nodeAt s2 (L.cpu s2) o) := fun o ho => by
    rw [I.cp, nodeAt_of_ksb I.k]; exact not_usuPm (P.node_notUser ho) (P.node_notSlot ho)
  have hmx : ¬ UserW (KSUPm K.uV.ptU) (maxA (L.mem s2 (scA (L.curW s)))) := by
    rw [← hct, I.F.i]
    exact not_usuPm (P.sc_notUser (P.hSc _ P.cscS) I.F.q.2.2.2.1) (P.sc_notSlot (P.hSc _ P.cscS) I.F.q.2.2.2.1)
  have htU : ∀ t, K.heap t = some .tcb → ∀ k : U64, 192 ≤ k.val → k.val < 4096 →
      ¬ UserW (KSUPm K.uV.ptU) (core.num.U64.wrapping_add t k) := fun t ht k h1 h2 =>
    not_usuPm (P.tcb_notUser ht h1 h2) (P.tcb_notSlot ht h1 h2)
  have O : UsrOK (L := L) (KSUPm K.uV.ptU) s2 (L.curW s) :=
    ⟨hn2, fun k h1 h2 => htU _ (P.hT _ P.cT) k h1 h2, hmx⟩
  have heU : UserW (KSUPm K.uV.ptU) e := ⟨hRS.1, Or.inl (Or.inr hpt)⟩
  -- the st decode
  have hc2 : sched.cur_thread st s2 = ok (L.curW s2) := cur_thread_ok s2
  have hg0 : msg.syscall_arg st s2 (L.curW s2) buf 0#u64 = ok (L.mem s2 (regA (L.curW s2) layout.reg.R10)) := by
    rw [sarg0_reg, reg_ok]
  have hg1 : msg.syscall_arg st s2 (L.curW s2) buf 1#u64 = ok (L.mem s2 (regA (L.curW s2) layout.reg.R8)) := by
    rw [sarg1_reg, reg_ok]
  have hg2 : msg.syscall_arg st s2 (L.curW s2) buf 2#u64 = ok (L.mem s2 (regA (L.curW s2) layout.reg.R9)) := by
    rw [sarg2_reg, reg_ok]
  have hpe2' : vspace.page_entry_slot st s2 root (L.mem s2 (regA (L.curW s2) layout.reg.R10)) .Small =
      ok (.Ok e) := by rw [hct]; exact hpe2
  have hdst : ∀ m : machine.Store S, sched.cur_thread m s2 = ok (L.curW s2) →
      syscall.decode_invocation m ar s2 a1 fl4_abi.label.X86PageMap length p.slot
        (.Frame fp .Small rt false mp false asid va) true true true false buf p.extra =
      vspace.decode_page_map m ar s2 a1 length p.slot
        { ptr := fp, size := .Small, rights := rt, is_device := false, mapped := mp, is_ept := false, asid,
          vaddr := va } buf p.extra := by
    intro m hm
    rw [decInv_eq_Pm]
    unfold decPmG
    simp only [hm, bind_ok, ↓reduceIte, Bool.false_eq_true, ite_self, eq_self_iff_true, if_true]
  have hcg : sched.cur_thread gS s2 = ok (L.curW s2) := (sched.cur_thread.guard (gS := gS) s2 hctR).trans hc2
  rw [hdst st hc2] at hy
  have hout := post_of_ok (dpm_run ar hA hc2 hx0 hg0 hg1 hg2 hcx2 hcv2 hpe2') hy
  -- the decode on `gS`
  have hFt : R (core.num.U64.wrapping_add (L.ksb s2) layout.ks.FEATURES) := by
    rw [I.k]; exact hR _ (P.ksw (by simp [layout.ks.FEATURES]) (by simp [layout.ks.FEATURES]))
  have hnT : ¬ TcbSlot K.uV.ptU p.slot := notTcbSlot_of hO
  have hnf := nof_of_frame_slot hcs
  have hscF : ∀ y, obj.Slot.set_cap gS p.slot y (.Frame fp .Small rt false true false rasid
      (L.mem s2 (regA (L.curW s2) layout.reg.R10))) = obj.Slot.set_cap st p.slot y (.Frame fp .Small rt false
      true false rasid (L.mem s2 (regA (L.curW s2) layout.reg.R10))) := by
    intro y
    obtain ⟨⟨w0, w1⟩, hw⟩ : ∃ w, capability.Cap.encode (.Frame fp .Small rt false true false rasid
        (L.mem s2 (regA (L.curW s2) layout.reg.R10))) = ok w := ⟨_, Fl4Proofs.P3.encode_eq _⟩
    have hc0' : ∀ x, gS.write x p.slot w0 = st.write x p.slot w0 := fun x => hc0 x w0 (nof_enc_framePm hw)
    unfold obj.Slot.set_cap
    simp only [hw, bind_ok, uncurry_apply_pair, lift, hc0', gst_write hW8]
  have hst : sched.set_thread_state gS s2 (L.curW s2) sched.TS_RESTART =
      sched.set_thread_state st s2 (L.curW s2) sched.TS_RESTART := by
    rw [hct]
    exact sched.set_thread_state.guardV (gS := gS) s2 (L.curW s) _ (hN s2 hnd2) (hsw _ (Or.inl rfl)) (hR _ rst.1)
      (hR _ rsc) (hR _ hmx2) (hR _ riq)
  have hpeg : vspace.page_entry_slot gS s2 root (L.mem s2 (regA (L.curW s2) layout.reg.R10)) .Small =
      ok (.Ok e) := by rw [hct, hWk.2 hf]; exact hpe2
  have hNr : (0#u64 : U64) < msg.N_MSG_REGISTERS ∧ (1#u64 : U64) < msg.N_MSG_REGISTERS ∧
      (2#u64 : U64) < msg.N_MSG_REGISTERS := by simp [msg.N_MSG_REGISTERS]
  refine ⟨?_, ?_⟩
  · rw [hdst gS hcg, dpm_congrF ar gS st hcg hc2 hx0 ((hargs _ hNr.1 buf).trans hg0) hg0
      ((hargs _ hNr.2.1 buf).trans hg1) hg1 ((hargs _ hNr.2.2 buf).trans hg2) hg2 (hcxg.trans hcx2) hcx2
      hWk.1 hpeg hpe2' (fun f => vspace.frame_address.guardK ar s2 a1 f) (vspace.make_user_page.guardF s2 hFt)
      (vspace.huge_pages.guardF s2 hFt) hst hscF
      (fun y a' as' va' d => funext fun dd => vspace.write_mapping.guard ar y a' e as' va' d dd (hRe _ hRS) (hWe _ hpt))]
    exact hy
  · intro z hz
    rw [hct] at hout
    obtain ⟨r, x, a2⟩ := y
    cases r with
    | Ok u =>
      cases u
      have kx := pmDecKeep ar hA hK O ha2 hrun hL hsl heU hout rfl
      simp only at kx hz ⊢
      have Fx := kx.sched hK O
      refine invRep.guard_okS (gS := gS) (hR _ rst.1) (hsw _ (Or.inr rfl)) (hR _ rsc) (hR _ riq) (hW.reg _ rB384)
        (hW.reg _ rM384) ?_ hz
      intro s5 es5
      have k5 : KeepA (L := L) x (L.curW s) s5 := by
        unfold msg.reply_success_empty at es5
        rw [set_reg_ok'] at es5; simp only [bind_ok] at es5
        obtain ⟨mi, -, es5⟩ := bind_eq_ok es5
        unfold msg.set_msg_info at es5
        obtain ⟨w, -, es5⟩ := bind_eq_ok es5
        rw [set_reg_ok'] at es5
        cases ok_inj_ff es5
        exact ((KeepA.refl kx.2.1 kx.2.2).wr_reg Fx rB384).wr_reg Fx rM384
      have k6 := kx.keepA (k5.wr Fx (b := stA (L.curW s)) (v := sched.TS_RUNNING) (Or.inr rfl) (fun _ => Or.inr rfl))
      have k5' := kx.keepA k5
      refine ⟨hN s5 (fun o => (k5'.node o).trans (hnd2 o)), ?_⟩
      have e6 : L.mem (L.wr s5 (stA (L.curW s)) sched.TS_RUNNING) (scA (L.curW s)) =
          L.mem s2 (scA (L.curW s)) :=
        k6.tcbF hK O (k := 3464#u64) (by simp) (by simp) (by simp)
      rw [e6, hsc2]; exact hR _ hmxR
    | Err er =>
      have hx : x = s2 := by
        rcases hout with ⟨hx, -⟩ | ⟨h, -⟩
        · exact hx
        · cases h
      simp only at hz ⊢
      rw [hx] at hz ⊢
      obtain ⟨bsl, hbsl⟩ := buffer_slot_ok (L.curW s)
      obtain ⟨hb1, hb2⟩ := P.lay.tslot _ (P.hT _ P.cT) _ bsl hbsl (by simp [layout.tcb.SLOT_BUFFER])
      have hbs := P.slot (Locks := Locks) hb1 (Or.inl hb2)
      have hI : R (core.num.U64.wrapping_add (L.curW s) 3512#u64) :=
        hR _ (P.gate (off := 3512#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField]))
      have hlb : msg.lookup_ipc_buffer st s2 true (L.curW s) = msg.lookup_ipc_buffer st s true (L.curW s) :=
        lookup_buf_keep P.tA true tk
      have hbuf0 := hJ.here.1.buf8
      have hbw : ∀ b, msg.lookup_ipc_buffer st s2 true (L.curW s) = ok b → BufW W b ∧ BufW R b := by
        intro b eb
        rw [hlb] at eb
        exact ⟨fun h0 i hi => hWu _ (hbuf0 b eb h0 i hi), fun h0 i hi => hRu _ (hbuf0 b eb h0 i hi)⟩
      rw [invRep.guard_errPm (gS := gS) er (fun e1 => PathObl.syscall.reply_error.guard (gS := gS) s2 (L.curW s) e1 hbsl hI
        (hR _ hbs.1) (hR _ hbs.2) (fun r hr => hW.reg r hr) hbw)]
      exact hz

end accM

section mvX
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP}
variable {A : Type} {ar : machine.Arch A}

/-- **`move` at `PmPreG`** (gen 11's [W] `PmMoveW`, proved; module docstring). -/
theorem pm_mvGX (hA : P0.ArchTotal ar) (hKP : RegionOKP K) (hUP : UserOKP K) {number : I64} {m : U64 → U64} :
    PmMoveW st ar number p K Locks m (PmPreGX st Cs Ω Sg Ac Locks p K m) := by
  intro s a s1 a1 hE h
  have hJ := hE.1.1
  have hq := hE.1.2.1
  have hG := hE.1.2.2
  have Pb := hq.1.1.1
  have P := Pb.ptUX hG
  have hK := hJ.regionOK
  have hU := hJ.userOK
  have hLA := hJ.ioLayA
  -- the plan's slot
  obtain ⟨fp, rt, asid0, va0, mp, hcs, hsl, -, hlkS, -⟩ := pm_core hq
  have hsl0 : Locks s p.slot := hlkS (fun e => hJ.hz (e ▸ hsl))
  have hO : OutsideObjs st K.heap.tcbs Cs s p.slot := by
    obtain ⟨x, hx, hxs⟩ := hq.2
    obtain ⟨Cw, hroot, hcl, hC⟩ := Pb.walk
    obtain ⟨q0, r0, m0, y0, hq0, hm0, hs0⟩ := lookup_slot_cn hroot hcl hx
    rw [← hxs, hs0]; exact (hC q0 r0 m0 y0 hq0 hm0).2.1
  have hnT : ¬ TcbSlot K.toKLayout p.slot := notTcbSlot_of hO
  have hnf := nof_of_frame_slot hcs
  -- the checked store's write facts
  have hW := mvWrS Pb hK hLA (c := L.cpu s) (lk := Locks s) (m := L.mem s)
  have hS0 : OwnMap.Safe0 (L.cpu s) (Locks s) (L.mem s) (L.curW s) := by
    refine ⟨?_, fun hq => absurd hq ?_⟩
    · rw [← OwnMap.affA_fld]; exact Pb.curAff
    · rw [← OwnMap.stA_fld]; exact nq_run Pb.run
  have hsw : ∀ v, v = sched.TS_RESTART ∨ v = sched.TS_RUNNING →
      SWr (gd st (PmRSU st K Locks s) (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s))) st
        (L.curW s) v :=
    fun v hv X => OwnMap.gds_write_state (Pb.hT _ Pb.cT) hS0 (fun hq => absurd hq (nq_run hv))
  have hc0 : ∀ x v, NullOrFrame v →
      (gd st (PmRSU st K Locks s) (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s))).write x p.slot v
        = st.write x p.slot v :=
    fun x v hv => OwnMap.gds_write_cap0 hsl hnT hsl0 hnf hv
  have hW8 : WAll (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s))
      (core.num.U64.wrapping_add p.slot 8#u64) := by
    obtain ⟨q8, qf⟩ := Pb.lay.slot8 p.slot hsl
    have hv := PathObl.slot_word_val qf (o := 8#u64) (by simp)
    have hr := Pb.lay.slotw p.slot hsl _ (slot_inW qf (o := 8#u64) (by simp))
    have hne : core.num.U64.wrapping_add p.slot 8#u64 ≠ p.slot := fun e => by
      have := congrArg UScalar.val e; rw [hv] at this; simp at this
    have ha : Aligned (core.num.U64.wrapping_add p.slot 8#u64) := by
      unfold Aligned; rw [hv]; simp; omega
    exact fun _ _ => Or.inl (Or.inl ⟨ha, OwnMap.nondec_slotw hK hr hne⟩)
  have hWu : ∀ b, UserW K.toKLayout b → WAll (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s)) b :=
    fun b hb _ _ => Or.inl (Or.inl ⟨hb.1, fun hd => (OwnMap.decW_ok hU hd).2 hb.2⟩)
  have hWe : ∀ b, b ∈ K.ptes → WAll (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s)) b :=
    fun b hb _ _ => Or.inl (Or.inl ⟨(hUP.kern b hb).1, pte_nondec hKP hb⟩)
  -- the block on the checked store
  have hblk : ∀ info nx s1' s2 a1' buf length cap, msg.msg_info st s (L.curW s) = ok info →
      InvChk st ar s a (L.curW s) p nx s1' s2 a1' →
      (if info.length > msg.N_MSG_REGISTERS then (if buf = 0#u64 then ok msg.N_MSG_REGISTERS else ok info.length)
        else ok info.length) = ok length →
      obj.Slot.cap st p.slot s2 = ok cap →
      ∀ y, syscall.decode_invocation st ar s2 a1' info.label length p.slot cap true true true false buf p.extra =
        ok y →
        syscall.decode_invocation (gd st (PmRSU st K Locks s)
            (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s))) ar s2 a1' info.label length p.slot cap
            true true true false buf p.extra = ok y ∧
        ∀ z, invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z →
          invRep (gd st (PmRSU st K Locks s) (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s)))
            (L.curW s) y.2.1 y.2.2 y.1 = ok z ∧ z.2.2 = core.result.Result.Ok () ∧
          FinOK (L := L) (gd st (PmRSU st K Locks s)
              (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s)))
            (IoRS (st := st) K.uV.ptU Locks s) (WAll (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s)))
            ar s z.1 z.2.1 := by
    intro info nx s1' s2 a1' buf length cap emi C _ hcap y hy
    obtain ⟨hdec, hrep⟩ := pmAccG2X (R := PmRSU st K Locks s)
      (W := WAll (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s)))
      (gS := gd st (PmRSU st K Locks s) (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s)))
      hA hE (fun _ h => pmRSU_ioRSX hG h) (fun b hb => ⟨hb.1, Or.inl hb.2⟩) (fun b hb => ⟨hb.1, Or.inr hb⟩) hW hsw
      hc0 hW8 hWu hWe emi C hcap hy
    refine ⟨hdec, fun z hz => ⟨hrep z hz, ?_⟩⟩
    haveI : GRd (gd st (PmRSU st K Locks s) (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s))) st
        (IoRS (st := st) K.uV.ptU Locks s) := gdr_sub (fun _ hy => pmRSU_ioRSX hG hy)
    exact pmFinGX hA hE hW (hsw _ (Or.inr rfl)) emi C hcap hy hz
  have r0 : IoRS (st := st) K.uV.ptU Locks s p.slot := by
    have := pm_slotRSX hJ hq P (o := 0#u64) (by simp) (by simp)
    rwa [wadd_zero (Pb.lay.slot8 _ hsl).2] at this
  have r8 := pm_slotRSX hJ hq P (o := 8#u64) (by simp) (by simp)
  have hg : syscall.handle_invocation_local
      (gd st (PmRSU st K Locks s) (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s))) ar s a number p =
      ok (true, s1, a1) := by
    haveI : GRd (gd st (PmRSU st K Locks s) (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s))) st
        (IoRS (st := st) K.uV.ptU Locks s) := gdr_sub (fun _ hy => pmRSU_ioRSX hG hy)
    exact inv_acc_gen2 hA P hW (pm_seenX hJ hq P) ⟨r0, r8⟩ hblk h
  have hp := pm_isProgOnX (st := st) (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (Locks := Locks) (p := p) (K := K)
    (μ := m) hA number
  rw [inv_hp hp (Narrow.gd _ _ _) (AltOf.pre hE.1) a] at hg
  rw [inv_hp hp (Narrow.mguard _ _) (AltOf.pre hE.1) a]
  exact interp_mguard_mono (fun x y hs => stepOKP_of_stepOKV (stepOKV_of_stepOK hKP.base hs)) _ s a _
    (OwnMap.run_gds_mguard hK hU hq.1.1.2 _ hg)

end mvX

section accN
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP} {μ : U64 → U64}
variable {A : Type} {ar : machine.Arch A}

/-- **`pmAccGX` without the user words** (module docstring): the decode, the `Ok` reply, and the error arm. -/
theorem pmAccNX (hA : P0.ArchTotal ar) {s : S} {a : A} {info : msginfo.MessageInfo} {nx : U64} {s1 s2 : S} {a1 : A}
    {buf length : U64} {cap : capability.Cap} {y : (core.result.Result Unit error.Exc) × S × A}
    {R W : U64 → Prop} {gS : machine.Store S} [GRd gS st R] [GWr gS st W]
    (hE : PmPreGX st Cs Ω Sg Ac Locks p K μ s)
    (hR : ∀ b, IoRS (st := st) K.uV.ptU Locks s b → R b)
    (hRe : ∀ b, PmRS st K Locks s b → R b)
    (hW : IoWr st W K.heap.scBits s) (hWs : ∀ b, IoWS (st := st) K.uV.ptU Locks s b → W b)
    (hWe : ∀ b, PmWS st K Locks s b → b ∉ K.user → W b)
    (emi : msg.msg_info st s (L.curW s) = ok info) (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1)
    (hcap : obj.Slot.cap st p.slot s2 = ok cap)
    (hy : syscall.decode_invocation st ar s2 a1 info.label length p.slot cap true true true false buf p.extra =
      ok y) :
    syscall.decode_invocation gS ar s2 a1 info.label length p.slot cap true true true false buf p.extra = ok y ∧
    (y.1 = .Ok () → ∀ z, invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z → invRep gS (L.curW s) y.2.1 y.2.2 y.1 = ok z) ∧
    (∀ er, y.1 = .Err er → y.2.1 = s2 ∧ y.2.2 = a1 ∧ ∃ se, er = .Sys se ∧ PmNoLk se) := by
  obtain ⟨fp, rt, asid, va, mp, x0, root, rasid, e, hcs, hcs2, hx0, hxK, hcx2, hcv2, hpe2, hpt, hle, hRS, hWS, hu,
    hf, hsl, hsl0, hO⟩ := pm_s2X hA hE C
  have hE0 := hE
  obtain ⟨⟨hJ, hq, hG⟩, -, -⟩ := hE
  have Pb := hq.1.1.1
  have P := Pb.ptUX hG
  -- the decode's first reads and its walk on `gS` (a store reading `IoRS (ptU K) s` as `st`)
  haveI hIo : GRd gS st (IoRS (st := st) K.uV.ptU Locks s) :=
    { read := fun hy s => GRd.read (g := gS) (hR _ hy) s
      read_pair := fun hy h8 s => GRd.read_pair (g := gS) (hR _ hy) (hR _ h8) s
      ks_base := gst_ks_base
      cur_cpu := gst_cur_cpu
      frame_masks := gst_frame_masks }
  obtain ⟨-, -, hargs, x0', root', rasid', hx0', hcxg, hcx', -⟩ := pm_decRdX (gS := gS) hA hE0 C
  have hWk := pm_decWalkX (gS := gS) hA hE0 C (root := root) (rasid := rasid) hu
  clear hIo
  rw [hx0] at hx0'
  have ex0 : x0' = x0 := by have := ok_inj_ff hx0'; simpa using this.symm
  subst ex0
  rw [hcx2] at hcx'
  obtain ⟨e1, e2⟩ : root = root' ∧ rasid = rasid' := by
    have := ok_inj_ff hcx'; simp only [capability.Cap.Pml4.injEq] at this; exact ⟨this.1, this.2.2⟩
  subst e1 e2
  obtain ⟨-, es1, eu, eac, ey, ehere, -⟩ := C
  have Ent := P.ent (Locks := Locks) hW
  have Hf := here_facts ehere
  have I := IoS2.of_ent hA Ent es1 eu Hf.sc
  have hct : L.curW s2 = L.curW s := I.cur
  have hL : Slot8 K.uV.ptU := fun q hq => P.lay.slot8 q hq
  have w0 := prefix_writes ar hA P.tp P.np P.cT es1 eu
  have hcap' : cap = .Frame fp .Small rt false mp false asid va := by
    rw [hcs2] at hcap; exact (ok_inj_ff hcap).symm
  subst hcap'
  obtain ⟨-, -, -, -, -, -, -, hlab, -, -⟩ := pm_core hq
  have hlbl := (hlab info emi).1
  rw [hlbl] at hy ⊢
  have tk : ∀ k : U64, k.val < 4096 → k.val % 8 = 0 → k.val ≠ 392 →
      L.mem s2 (core.num.U64.wrapping_add (L.curW s) k) = L.mem s (core.num.U64.wrapping_add (L.curW s) k) :=
    fun k h1 h2 h3 => w0.2.2 _ (field_aligned P.tA h1 h2) (preW_tcb P.tA P.np P.cT h1 h3)
  -- the node, the caller's words (cmAcc8's)
  have hctR : R (L.nodeAt s2 (L.cpu s2) layout.node.CUR_THREAD) := by
    rw [I.cp, nodeAt_of_ksb I.k]
    exact hR _ (P.nd layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])).1
  have hN : ∀ x : S, (∀ o, L.nodeAt x (L.cpu x) o = L.nodeAt s (L.cpu s) o) → NodeSt (L := L) R W x := by
    have n0 : IoRS (st := st) K.uV.ptU Locks s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) :=
      (P.nd layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])).1
    have n1 : IoRS (st := st) K.uV.ptU Locks s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) :=
      (P.nd layout.node.SCHED_ACTION (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])).1
    have n1w : W (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) :=
      hW.nd _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
    intro x hn
    refine ⟨?_, ?_, ?_⟩
    · rw [hn]; exact hR _ n0
    · rw [hn]; exact hR _ n1
    · rw [hn]; exact n1w
  have hnd2 : ∀ o, L.nodeAt s2 (L.cpu s2) o = L.nodeAt s (L.cpu s) o := fun o => by
    rw [I.cp, nodeAt_of_ksb I.k]
  have rst := P.stw (Locks := Locks)
  have rsc : IoRS (st := st) K.uV.ptU Locks s (scA (L.curW s)) :=
    P.gate (off := 3464#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField])
  have riq : IoRS (st := st) K.uV.ptU Locks s (inqA (L.curW s)) :=
    (P.home (off := 3592#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).1
  have hmxR : IoRS (st := st) K.uV.ptU Locks s (maxA (L.cscW s)) := by
    have hmx := maxA_facts P.bxi.2.2.1.1 P.cscS
    exact P.cscacc.rd _ hmx.1 ⟨hmx.2.1, hmx.2.2⟩
  have hsc2 : L.mem s2 (scA (L.curW s)) = L.cscW s := by rw [← hct]; exact I.F.i
  have ha2 : L.actionW s2 = sched.ACTION_RESUME_CURRENT := by
    rw [eq_of_spec_fd (sched.action.spec (L := L) s2)] at eac; exact ok_inj_ff eac
  have hrun : L.mem s2 (stA (L.curW s)) = sched.TS_RESTART ∨ L.mem s2 (stA (L.curW s)) = sched.TS_RUNNING := by
    rw [I.st]; exact Ent.run
  have hK0 := SchedOK.of_sw I.F (by rw [hct]; exact Hf.sc) (by rw [hct]; exact Hf.nr)
  rw [hct] at hK0
  have hK : SchedOK (L := L) s2 (L.curW s) := hK0
  have hmx2 : IoRS (st := st) K.uV.ptU Locks s
      (maxA (L.mem (L.wr s2 (stA (L.curW s)) sched.TS_RESTART) (scA (L.curW s)))) := by
    have kw := (KeepA.refl ha2 hrun).wr hK (b := stA (L.curW s)) (v := sched.TS_RESTART) (Or.inr rfl)
      (fun _ => Or.inl rfl)
    have e : L.mem (L.wr s2 (stA (L.curW s)) sched.TS_RESTART) (scA (L.curW s)) = L.mem s2 (scA (L.curW s)) :=
      kw.mem (field_aligned P.tA (by simp) (by simp)) (iotw_field P.tA (by simp) (by simp))
    rw [e, hsc2]
    exact hmxR
  -- the layout `KSUPm (ptU K)`
  have hn2 : ∀ o : U64, o.val < 4288 → ¬ UserW (KSUPm K.uV.ptU) (L.nodeAt s2 (L.cpu s2) o) := fun o ho => by
    rw [I.cp, nodeAt_of_ksb I.k]; exact not_usuPm (P.node_notUser ho) (P.node_notSlot ho)
  have hmx : ¬ UserW (KSUPm K.uV.ptU) (maxA (L.mem s2 (scA (L.curW s)))) := by
    rw [← hct, I.F.i]
    exact not_usuPm (P.sc_notUser (P.hSc _ P.cscS) I.F.q.2.2.2.1) (P.sc_notSlot (P.hSc _ P.cscS) I.F.q.2.2.2.1)
  have htU : ∀ t, K.heap t = some .tcb → ∀ k : U64, 192 ≤ k.val → k.val < 4096 →
      ¬ UserW (KSUPm K.uV.ptU) (core.num.U64.wrapping_add t k) := fun t ht k h1 h2 =>
    not_usuPm (P.tcb_notUser ht h1 h2) (P.tcb_notSlot ht h1 h2)
  have O : UsrOK (L := L) (KSUPm K.uV.ptU) s2 (L.curW s) :=
    ⟨hn2, fun k h1 h2 => htU _ (P.hT _ P.cT) k h1 h2, hmx⟩
  have heU : UserW (KSUPm K.uV.ptU) e := ⟨hRS.1, Or.inl (Or.inr hpt)⟩
  -- the st decode
  have hc2 : sched.cur_thread st s2 = ok (L.curW s2) := cur_thread_ok s2
  have hg0 : msg.syscall_arg st s2 (L.curW s2) buf 0#u64 = ok (L.mem s2 (regA (L.curW s2) layout.reg.R10)) := by
    rw [sarg0_reg, reg_ok]
  have hg1 : msg.syscall_arg st s2 (L.curW s2) buf 1#u64 = ok (L.mem s2 (regA (L.curW s2) layout.reg.R8)) := by
    rw [sarg1_reg, reg_ok]
  have hg2 : msg.syscall_arg st s2 (L.curW s2) buf 2#u64 = ok (L.mem s2 (regA (L.curW s2) layout.reg.R9)) := by
    rw [sarg2_reg, reg_ok]
  have hpe2' : vspace.page_entry_slot st s2 root (L.mem s2 (regA (L.curW s2) layout.reg.R10)) .Small =
      ok (.Ok e) := by rw [hct]; exact hpe2
  have hdst : ∀ m : machine.Store S, sched.cur_thread m s2 = ok (L.curW s2) →
      syscall.decode_invocation m ar s2 a1 fl4_abi.label.X86PageMap length p.slot
        (.Frame fp .Small rt false mp false asid va) true true true false buf p.extra =
      vspace.decode_page_map m ar s2 a1 length p.slot
        { ptr := fp, size := .Small, rights := rt, is_device := false, mapped := mp, is_ept := false, asid,
          vaddr := va } buf p.extra := by
    intro m hm
    rw [decInv_eq_Pm]
    unfold decPmG
    simp only [hm, bind_ok, ↓reduceIte, Bool.false_eq_true, ite_self, eq_self_iff_true, if_true]
  have hcg : sched.cur_thread gS s2 = ok (L.curW s2) := (sched.cur_thread.guard (gS := gS) s2 hctR).trans hc2
  rw [hdst st hc2] at hy
  have hout2 := post_of_ok (dpm_run2 ar hA hc2 hx0 hg0 hg1 hg2 hcx2 hcv2 hpe2') hy
  have hout := dpmOut_of2 hout2
  -- the decode on `gS`
  have hFt : R (core.num.U64.wrapping_add (L.ksb s2) layout.ks.FEATURES) := by
    rw [I.k]; exact hR _ (P.ksw (by simp [layout.ks.FEATURES]) (by simp [layout.ks.FEATURES]))
  have hnT : ¬ TcbSlot K.uV.ptU p.slot := notTcbSlot_of hO
  have hnf := nof_of_frame_slot hcs
  have hW0 : W p.slot := by
    have := hWs _ ((P.lockSlot (o := 0#u64) hsl hsl0 (by simp) (by simp)).2 (Or.inr ⟨hnT, hnf⟩))
    rwa [wadd_zero (hL _ hsl).2] at this
  have hW8 : W (core.num.U64.wrapping_add p.slot 8#u64) :=
    hWs _ ((P.lockSlot (o := 8#u64) hsl hsl0 (by simp) (by simp)).2 (Or.inr ⟨hnT, hnf⟩))
  have hst : sched.set_thread_state gS s2 (L.curW s2) sched.TS_RESTART =
      sched.set_thread_state st s2 (L.curW s2) sched.TS_RESTART := by
    rw [hct]
    exact sched.set_thread_state.guard (gS := gS) s2 (L.curW s) _ (hN s2 hnd2) (hWs _ rst.2) (hR _ rst.1)
      (hR _ rsc) (hR _ hmx2) (hR _ riq)
  have hpeg : vspace.page_entry_slot gS s2 root (L.mem s2 (regA (L.curW s2) layout.reg.R10)) .Small =
      ok (.Ok e) := by rw [hct, hWk.2 hf]; exact hpe2
  have hNr : (0#u64 : U64) < msg.N_MSG_REGISTERS ∧ (1#u64 : U64) < msg.N_MSG_REGISTERS ∧
      (2#u64 : U64) < msg.N_MSG_REGISTERS := by simp [msg.N_MSG_REGISTERS]
  refine ⟨?_, ?_, ?_⟩
  · rw [hdst gS hcg, dpm_congr ar gS st hcg hc2 hx0 ((hargs _ hNr.1 buf).trans hg0) hg0
      ((hargs _ hNr.2.1 buf).trans hg1) hg1 ((hargs _ hNr.2.2 buf).trans hg2) hg2 (hcxg.trans hcx2) hcx2
      hWk.1 hpeg hpe2' (fun f => vspace.frame_address.guardK ar s2 a1 f) (vspace.make_user_page.guardF s2 hFt)
      (vspace.huge_pages.guardF s2 hFt) hst (fun y c => obj.Slot.set_cap.guard p.slot y c hW0 hW8)
      (fun y a' as' va' d => funext fun dd => vspace.write_mapping.guard ar y a' e as' va' d dd (hRe _ hRS) (hWe _ hWS hRS.2.1))]
    exact hy
  · intro hok0 z hz
    rw [hct] at hout
    obtain ⟨r, x, a2⟩ := y
    cases r with
    | Ok u =>
      cases u
      have kx := pmDecKeep ar hA hK O ha2 hrun hL hsl heU hout rfl
      simp only at kx hz ⊢
      have Fx := kx.sched hK O
      refine invRep.guard_ok (gS := gS) (hR _ rst.1) (hWs _ rst.2) (hR _ rsc) (hR _ riq) (hW.reg _ rB384)
        (hW.reg _ rM384) ?_ hz
      intro s5 es5
      have k5 : KeepA (L := L) x (L.curW s) s5 := by
        unfold msg.reply_success_empty at es5
        rw [set_reg_ok'] at es5; simp only [bind_ok] at es5
        obtain ⟨mi, -, es5⟩ := bind_eq_ok es5
        unfold msg.set_msg_info at es5
        obtain ⟨w, -, es5⟩ := bind_eq_ok es5
        rw [set_reg_ok'] at es5
        cases ok_inj_ff es5
        exact ((KeepA.refl kx.2.1 kx.2.2).wr_reg Fx rB384).wr_reg Fx rM384
      have k6 := kx.keepA (k5.wr Fx (b := stA (L.curW s)) (v := sched.TS_RUNNING) (Or.inr rfl) (fun _ => Or.inr rfl))
      have k5' := kx.keepA k5
      refine ⟨hN s5 (fun o => (k5'.node o).trans (hnd2 o)), ?_⟩
      have e6 : L.mem (L.wr s5 (stA (L.curW s)) sched.TS_RUNNING) (scA (L.curW s)) =
          L.mem s2 (scA (L.curW s)) :=
        k6.tcbF hK O (k := 3464#u64) (by simp) (by simp) (by simp)
      rw [e6, hsc2]; exact hR _ hmxR
    | Err er => simp at hok0
  · intro er her
    rcases hout2 with ⟨hx, ha, se, hse, hnl⟩ | ⟨hok, -⟩
    · rw [hse] at her
      cases her
      exact ⟨hx, ha, se, rfl, hnl⟩
    · rw [hok] at her; cases her

end accN

section setsX
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]

/-- The decode step's read set: `IoRS (ptU K) s ∪ PmRS s` (no user word). -/
def PmRNX (K : KLayoutP) (Locks : S → U64 → Prop) (s : S) (b : U64) : Prop :=
  IoRS (st := st) K.uV.ptU Locks s b ∨ PmRS st K Locks s b

/-- The decode step's write set: `IoWS (ptU K) s ∪ PmWS s` off `K.user`. -/
def PmWNX (K : KLayoutP) (Locks : S → U64 → Prop) (s : S) (b : U64) : Prop :=
  (IoWS (st := st) K.uV.ptU Locks s b ∨ PmWS st K Locks s b) ∧ b ∉ K.user

end setsX

section restX
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayoutP} {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}
variable {A : Type} {ar : machine.Arch A}

/-- **`reply_error e` read once, for a `PmNoLk` error** (invj's `invU_replyOnce` over any such error; module
docstring): every read but word 7 of the receiver's buffer is an `IoRS (ptU K) s` word (`error_mrs` writes registers
only, `syscall.error_mrs.guardN`); that one user word is read from the empty touched set, then written. -/
theorem pm_replyOnceX {s s2 : S} {a1 : A} {Y : Type} {k : Unit → SProg Y} {r' : Y × S × A} {e : error.SysError}
    {T Rp Scs Nt : Set U64} {H : Heap} {Z : U64 → Nat}
    (P : IoPre st K.uV.ptU T Cs Ω H Sg Rp Scs Nt Z Ac s) (hG : PmGX st K s) (he : PmNoLk e)
    (M : InvMid (L := L) (IoRS (st := st) K.uV.ptU Locks s) s s2 (L.curW s))
    (hTail : ∀ x5 Wd' T', syscall.reply_error st s2 (L.curW s) e = ok x5 →
      interp st ar (k ()) x5 a1 = ok r' →
      Once st ar (PmRSU st K Locks s) (· ∈ K.user) Wd' T' (k ()) x5 a1)
    (h : interp st ar ((R.syscall.reply_error (L.curW s) e).sbind k) s2 a1 = ok r')
    (Wd : Set U64) :
    Once st ar (PmRSU st K Locks s) (· ∈ K.user) Wd ∅
      ((R.syscall.reply_error (L.curW s) e).sbind k) s2 a1 := by
  have hR0 : ∀ q, IoRS (st := st) K.uV.ptU Locks s q → PmRSU st K Locks s q ∧ q ∉ K.user :=
    fun q hq => ⟨pmRSU_ioRSX hG hq, fun hu => hq.2.1 (Or.inl (Or.inl hu))⟩
  have hW0 : ∀ q, IoWS (st := st) K.uV.ptU Locks s q → q ∉ K.user := fun q hq hu => P.ioWS_nu hq (Or.inl (Or.inl hu))
  unfold R.syscall.reply_error at h ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- the receiver's buffer
  obtain ⟨bsl, hbsl⟩ := buffer_slot_ok (L.curW s)
  refine once_gstep hR0 hW0 (R.msg.lookup_ipc_buffer_nz _ _) h (fun r h1 => ?_) (fun r h1 hk Wd1 _ => ?_)
  · rw [R.msg.lookup_ipc_buffer_eq] at h1 ⊢
    rw [msg.lookup_ipc_buffer.guard (gS := PathObl.guard st (IoRS (st := st) K.uV.ptU Locks s) (IoWS (st := st) K.uV.ptU Locks s))
      s2 true (L.curW s) hbsl M.ib (M.bs _ hbsl).1 (M.bs _ hbsl).2]
    exact h1
  rw [R.msg.lookup_ipc_buffer_eq] at h1
  obtain ⟨b, eb, rfl⟩ := bind_shape h1
  replace h := hk
  dsimp only at h ⊢
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `BADGE`
  refine once_gstep hR0 hW0 (R.obj.Tcb.set_reg_nz _ _ _) h (fun r h1 => ?_) (fun r h1 hk Wd2 _ => ?_)
  · rw [R.obj.Tcb.set_reg_eq] at h1 ⊢
    rw [obj.Tcb.set_reg.guard (gS := PathObl.guard st (IoRS (st := st) K.uV.ptU Locks s) (IoWS (st := st) K.uV.ptU Locks s)) _ s2
      _ _ (P.reg (Locks := Locks) (by simp [layout.reg.BADGE])).2]
    exact h1
  rw [R.obj.Tcb.set_reg_eq] at h1
  obtain ⟨x3, es3, rfl⟩ := bind_shape h1
  replace h := hk
  dsimp only at h ⊢
  -- `error_mrs` (registers only) and the buffer word
  refine once_gstep hR0 hW0 (R.syscall.error_mrs_nz _ _ _) h (fun r h1 => ?_) (fun r h1 hk Wd3 _ => ?_)
  · rw [R.syscall.error_mrs_eq] at h1 ⊢
    rw [syscall.error_mrs.guardN (gS := PathObl.guard st (IoRS (st := st) K.uV.ptU Locks s)
      (IoWS (st := st) K.uV.ptU Locks s)) x3 (L.curW s) b e he (fun r hr => (P.ioWr (Locks := Locks)).reg r hr)]
    exact h1
  rw [R.syscall.error_mrs_eq] at h1
  obtain ⟨⟨len, x4⟩, em, rfl⟩ := bind_shape h1
  replace h := hk
  dsimp only at h ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind, SProg.blk,
    fl4_abi.config.KERNEL_INVOCATION_REPORT_ERROR_IPC, ↓reduceIte] at h ⊢
  refine once_ite h (fun hb0 h => ?_) (fun hb0 h => ?_)
  · simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
    refine once_liftR h (fun i ei h => ?_)
    unfold R.msg.buf_get at h ⊢
    simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind, SProg.read] at h ⊢
    simp only [interp] at h
    obtain ⟨w, hv, h⟩ := bok.mp h
    simp only [Once]
    refine ⟨fun _ => Set.notMem_empty _, fun w' hw' => ?_⟩
    rw [hv] at hw'
    obtain rfl := ok_inj_ff hw'
    unfold R.msg.buf_set at h ⊢
    simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind, SProg.write] at h ⊢
    simp only [interp] at h
    obtain ⟨s4, hs4, h⟩ := bok.mp h
    simp only [Once]
    intro s4' hs4'
    rw [hs4] at hs4'
    obtain rfl := ok_inj_ff hs4'
    refine once_liftR h (fun c ec h => ?_)
    refine once_liftR h (fun mi emi h => ?_)
    refine once_gstep hR0 hW0 (R.msg.set_msg_info_nz _ _) h (fun r h1 => ?_) (fun r h1 hk Wd5 _ => ?_)
    · rw [R.msg.set_msg_info_eq] at h1 ⊢
      rw [msg.set_msg_info.guard (gS := PathObl.guard st (IoRS (st := st) K.uV.ptU Locks s) (IoWS (st := st) K.uV.ptU Locks s)) _ _ _
        (P.reg (Locks := Locks) (by simp [layout.reg.MSG_INFO])).2]
      exact h1
    rw [R.msg.set_msg_info_eq] at h1
    obtain ⟨x5, es5, rfl⟩ := bind_shape h1
    dsimp only at hk ⊢
    refine hTail x5 _ _ ?_ hk
    unfold syscall.reply_error msg.buf_get msg.buf_set
    simp only [eb, es3, em, bind_ok, lift, uncurry_apply_pair,
      fl4_abi.config.KERNEL_INVOCATION_REPORT_ERROR_IPC, ↓reduceIte, hb0, ei, ec, hv, hs4, emi, es5]
  · refine once_liftR h (fun c ec h => ?_)
    refine once_liftR h (fun mi emi h => ?_)
    refine once_gstep hR0 hW0 (R.msg.set_msg_info_nz _ _) h (fun r h1 => ?_) (fun r h1 hk Wd5 _ => ?_)
    · rw [R.msg.set_msg_info_eq] at h1 ⊢
      rw [msg.set_msg_info.guard (gS := PathObl.guard st (IoRS (st := st) K.uV.ptU Locks s) (IoWS (st := st) K.uV.ptU Locks s)) _ _ _
        (P.reg (Locks := Locks) (by simp [layout.reg.MSG_INFO])).2]
      exact h1
    rw [R.msg.set_msg_info_eq] at h1
    obtain ⟨x5, es5, rfl⟩ := bind_shape h1
    dsimp only at hk ⊢
    refine hTail x5 _ _ ?_ hk
    unfold syscall.reply_error
    simp only [eb, es3, em, bind_ok, lift, uncurry_apply_pair,
      fl4_abi.config.KERNEL_INVOCATION_REPORT_ERROR_IPC, ↓reduceIte, hb0, ec, Bool.false_eq_true, emi, es5]

/-- **After the reply: `after_invocation (Ok ())` and `finish`** read only `IoRS (ptU K) s` words
(`syscall.finish.guard_resume` with `pmFinGX`'s `FinOK` at the reply's end state `z.1`). -/
theorem pm_tailOnceX (hA : P0.ArchTotal ar) {p : localinv.Plan} {μ : U64 → U64} {s s1 s2 : S} {a a1 : A}
    {info : msginfo.MessageInfo} {nx buf length : U64} {cap : capability.Cap}
    {y : (core.result.Result Unit error.Exc) × S × A} {z : S × A × core.result.Result Unit error.Exc}
    {r' : Bool × S × A}
    (hE : PmPreGX st Cs Ω Sg Ac Locks p K μ s)
    (emi : msg.msg_info st s (L.curW s) = ok info) (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1)
    (hcap : obj.Slot.cap st p.slot s2 = ok cap)
    (hy : syscall.decode_invocation st ar s2 a1 info.label length p.slot cap true true true false buf p.extra =
      ok y)
    (hz : invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z)
    (h : interp st ar ((R.syscall.after_invocation (.Ok ())).sbind fun _ =>
      R.syscall.finish.sbind fun _ => SProg.ret true) z.1 z.2.1 = ok r')
    (Wd T : Set U64) :
    Once st ar (PmRSU st K Locks s) (· ∈ K.user) Wd T ((R.syscall.after_invocation (.Ok ())).sbind fun _ =>
      R.syscall.finish.sbind fun _ => SProg.ret true) z.1 z.2.1 := by
  have hG := hE.1.2.2
  have P := hE.1.2.1.1.1.1.ptUX hG
  obtain ⟨-, F⟩ := pmFinGX (gS := PathObl.guard st (IoRS (st := st) K.uV.ptU Locks s) (IoWS (st := st) K.uV.ptU Locks s))
    (W := IoWS (st := st) K.uV.ptU Locks s) hA hE (P.ioWr (Locks := Locks)) (SWr.of_W (P.stw (Locks := Locks)).2)
    emi C hcap hy hz
  unfold R.syscall.after_invocation at h ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine once_gstep (R0 := IoRS (st := st) K.uV.ptU Locks s) (W0 := IoWS (st := st) K.uV.ptU Locks s)
    (fun q hq => ⟨pmRSU_ioRSX hG hq, fun hu => hq.2.1 (Or.inl (Or.inl hu))⟩) (fun q hq hu => P.ioWS_nu hq (Or.inl (Or.inl hu)))
    R.syscall.finish_nz h (fun r h1 => ?_) (fun _ _ _ _ _ => by simp only [Once])
  rw [R.syscall.finish_eq] at h1 ⊢
  rw [syscall.finish.guard_resume ar z.1 z.2.1 (nd_at (fun o h1 h2 => P.nd (Locks := Locks) o h1 h2) F.k F.c) F.nd
    F.td F.rs F.ha F.hsw F.hfr F.hact F.hvc]
  exact h1

/-- **The decode onward of an accepted PageMap run reads once** (module docstring). -/
theorem pm_decOnceX (hA : P0.ArchTotal ar) {number : I64} {p : localinv.Plan} {μ : U64 → U64} {s s1 s2 : S}
    {a a1 : A} {info : msginfo.MessageInfo} {nx buf length : U64} {cap : capability.Cap} {r' : Bool × S × A}
    (hE : PmPreGX st Cs Ω Sg Ac Locks p K μ s)
    (hac : ∃ s' a', syscall.handle_invocation_local st ar s a number p = ok (true, s', a'))
    (emi : msg.msg_info st s (L.curW s) = ok info) (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1)
    (ecap : obj.Slot.cap st p.slot s2 = ok cap)
    (h : interp st ar (pmRest (L.curW s) info p buf length cap) s2 a1 = ok r') (Wd : Set U64) :
    Once st ar (PmRSU st K Locks s) (· ∈ K.user) Wd ∅ (pmRest (L.curW s) info p buf length cap) s2 a1 := by
  have hG := hE.1.2.2
  have hq := hE.1.2.1
  have P := hE.1.2.1.1.1.1.ptUX hG
  obtain ⟨sA, aA, h0⟩ := hac
  have M := invCM_hmid (Locks := Locks) hA P h0 info nx s1 s2 a1 emi C.1 C.2.1 C.2.2.1
  obtain ⟨fp, rt, asid, va, mp, x0, root, rasid, e, -, hcs2, -⟩ := pm_s2X hA hE C
  have hcap' : cap = .Frame fp .Small rt false mp false asid va := by
    have := ecap; rw [hcs2] at this; exact (ok_inj_ff this).symm
  subst hcap'
  obtain ⟨-, -, -, -, -, -, -, hlab, -, -⟩ := pm_core hq
  have hlbl := (hlab info emi).1
  have hdI : ∀ m : machine.Store S, interp m ar (R.decPmG info.label length p.slot
      (.Frame fp .Small rt false mp false asid va) true true true false buf p.extra) s2 a1 =
      (syscall.decode_invocation m ar s2 a1 info.label length p.slot (.Frame fp .Small rt false mp false asid va)
        true true true false buf p.extra >>= fun r => ok (r.1, r.2.1, r.2.2)) := by
    intro m
    rw [R.decPmG_eq, hlbl, decInv_eq_Pm]
  have hR0 : ∀ q, PmRNX st K Locks s q → PmRSU st K Locks s q ∧ q ∉ K.user := by
    intro q hq'
    rcases hq' with hq' | hq'
    · exact ⟨pmRSU_ioRSX hG hq', fun hu => hq'.2.1 (Or.inl (Or.inl hu))⟩
    · exact ⟨pmRS_U hq', hq'.2.1⟩
  have hW0 : ∀ q, PmWNX st K Locks s q → q ∉ K.user := fun q hq' => hq'.2
  have hW : IoWr st (PmWNX st K Locks s) K.heap.scBits s :=
    (P.ioWr (Locks := Locks)).mono (fun b hb => ⟨Or.inl hb, fun hu => P.ioWS_nu hb (Or.inl (Or.inl hu))⟩)
  have hAcc := fun (y : (core.result.Result Unit error.Exc) × S × A)
      (hy : syscall.decode_invocation st ar s2 a1 info.label length p.slot
        (.Frame fp .Small rt false mp false asid va) true true true false buf p.extra = ok y) =>
    pmAccNX (R := PmRNX st K Locks s) (W := PmWNX st K Locks s)
      (gS := PathObl.guard st (PmRNX st K Locks s) (PmWNX st K Locks s)) hA hE (fun _ h => Or.inl h)
      (fun _ h => Or.inr h) hW (fun b hb => ⟨Or.inl hb, fun hu => P.ioWS_nu hb (Or.inl (Or.inl hu))⟩)
      (fun b hb hu => ⟨Or.inr hb, hu⟩) emi C ecap hy
  unfold pmRest at h ⊢
  refine once_gstep hR0 hW0 (R.decPmG_nz _ _ _ _ _ _ _ _ _ _) h (fun r h1 => ?_) (fun r h1 hk Wd1 _ => ?_)
  · rw [hdI] at h1 ⊢
    obtain ⟨y, hy, -⟩ := bind_eq_ok h1
    rw [(hAcc _ hy).1]
    rw [hy] at h1
    exact h1
  rw [hdI] at h1
  obtain ⟨y, hy, rfl⟩ := bind_shape h1
  obtain ⟨-, hrep, herr⟩ := hAcc _ hy
  obtain ⟨yr, yx, ya⟩ := y
  dsimp only at hk ⊢
  cases yr with
  | Ok u =>
    cases u
    refine once_gstep hR0 hW0 (R.invPostG_nz _ _) hk (fun r h2 => ?_) (fun r h2 hk2 Wd2 _ => ?_)
    · rw [R.invPostG_eq] at h2 ⊢
      obtain ⟨z, hz, -⟩ := bind_eq_ok h2
      have hg2 : invPostG (PathObl.guard st (PmRNX st K Locks s) (PmWNX st K Locks s)) yx ya (L.curW s) (.Ok ()) =
          ok z := hrep rfl z hz
      rw [hg2]
      rw [hz] at h2
      exact h2
    rw [R.invPostG_eq] at h2
    obtain ⟨z, hz, rfl⟩ := bind_shape h2
    dsimp only at hk2 ⊢
    have hz' : invRep st (L.curW s) yx ya (.Ok ()) = ok z := hz
    obtain ⟨hz2, -⟩ := pmFinGX (gS := PathObl.guard st (IoRS (st := st) K.uV.ptU Locks s)
      (IoWS (st := st) K.uV.ptU Locks s)) (W := IoWS (st := st) K.uV.ptU Locks s) (y := (.Ok (), yx, ya)) hA hE
      (P.ioWr (Locks := Locks)) (SWr.of_W (P.stw (Locks := Locks)).2) emi C ecap hy hz'
    rw [hz2] at hk2 ⊢
    exact pm_tailOnceX hA hE emi C ecap hy hz' hk2 Wd2 ∅
  | Err er =>
    obtain ⟨hx, ha, se, rfl, hnl⟩ := herr er rfl
    dsimp only at hx ha
    subst hx ha
    unfold R.invPostG at hk ⊢
    simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind, SProg.blk] at hk ⊢
    refine pm_replyOnceX P hG hnl M (fun x5 Wd' T' er hk' => ?_) hk Wd1
    have hz : invRep st (L.curW s) yx ya (.Err (.Sys se)) = ok (x5, ya, .Ok ()) := by
      unfold invRep
      simp only [er, bind_ok, uncurry_apply_pair]
      try rfl
    exact pm_tailOnceX (z := (x5, ya, .Ok ())) hA hE emi C ecap hy hz hk' Wd' T'

end restX

section walkX
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayoutP} {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}
variable {A : Type} {ar : machine.Arch A}

/-- **`Once` of an accepted PageMap run at its entry** (module docstring). -/
theorem pm_entOnceX (hA : P0.ArchTotal ar) {number : I64} {p : localinv.Plan} {μ : U64 → U64} :
    ∀ s (a : A) r, PmPreGX st Cs Ω Sg Ac Locks p K μ s →
      (∃ s1 a1, syscall.handle_invocation_local st ar s a number p = ok (true, s1, a1)) →
      interp st ar (R.invBodyPmG number p) s a = ok r →
      Once st ar (PmRSU st K Locks s) (· ∈ K.user) ∅ ∅ (R.invBodyPmG number p) s a := by
  intro s a r hE hac h
  obtain ⟨sA, aA, h0⟩ := hac
  have hG := hE.1.2.2
  have hJ := hE.1.1
  have hq := hE.1.2.1
  have P := hq.1.1.1.ptUX hG
  have hR0 : ∀ q, IoRS (st := st) K.uV.ptU Locks s q → PmRSU st K Locks s q ∧ q ∉ K.user :=
    fun q hq => ⟨pmRSU_ioRSX hG hq, fun hu => hq.2.1 (Or.inl (Or.inl hu))⟩
  have hW0 : ∀ q, IoRS (st := st) K.uV.ptU Locks s q → q ∉ K.user := fun q hq hu => hq.2.1 (Or.inl (Or.inl hu))
  obtain ⟨-, -, -, -, -, -, hsl, -, -, -⟩ := pm_core hq
  obtain ⟨-, hf⟩ := P.lay.slot8 _ hsl
  have r0 : IoRS (st := st) K.uV.ptU Locks s p.slot := by
    have := pm_slotRSX hJ hq P (o := 0#u64) (by simp) (by simp)
    rwa [wadd_zero hf] at this
  have r8 := pm_slotRSX hJ hq P (o := 8#u64) (by simp) (by simp)
  have nC := (P.nd (Locks := Locks) layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD])
    (by simp [layout.node.CUR_THREAD])).1
  unfold R.invBodyPmG at h ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- the current thread
  refine once_gstep hR0 hW0 (R.sched.cur_thread_nz) h (fun r h1 => ?_) (fun r h1 hk Wd1 _ => ?_)
  · rw [R.sched.cur_thread_eq] at h1 ⊢
    rw [sched.cur_thread.guard (gS := PathObl.guard st (IoRS (st := st) K.uV.ptU Locks s) (IoRS (st := st) K.uV.ptU Locks s)) s nC]
    exact h1
  replace h := hk
  rw [R.sched.cur_thread_eq] at h1
  obtain ⟨t, et, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  rw [cur_thread_ok] at et
  have et' : t = L.curW s := (ok_inj_ff et).symm
  subst et'
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `MSG_INFO`
  refine once_gstep hR0 hW0 (R.msg.msg_info_nz _) h (fun r h1 => ?_) (fun r h1 hk Wd2 _ => ?_)
  · rw [R.msg.msg_info_eq] at h1 ⊢
    rw [msg.msg_info.guard (gS := PathObl.guard st (IoRS (st := st) K.uV.ptU Locks s) (IoRS (st := st) K.uV.ptU Locks s)) s _
      (P.reg (Locks := Locks) (by simp [layout.reg.MSG_INFO])).1]
    exact h1
  replace h := hk
  rw [R.msg.msg_info_eq] at h1
  obtain ⟨info, emi, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  refine once_ite0 h (fun _ _ => by simp only [Once]) (fun _ h => ?_)
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- the flags
  refine once_gstep hR0 hW0 (R.obj.Tcb.flags_nz _) h (fun r h1 => ?_) (fun r h1 hk Wd3 _ => ?_)
  · rw [R.obj.Tcb.flags_eq] at h1 ⊢
    rw [obj.Tcb.flags.guard (gS := PathObl.guard st (IoRS (st := st) K.uV.ptU Locks s) (IoRS (st := st) K.uV.ptU Locks s)) _ s
      (P.home (Locks := Locks) (off := 3456#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField])).1]
    exact h1
  replace h := hk
  rw [R.obj.Tcb.flags_eq] at h1
  obtain ⟨i, -, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine once_ite0 h (fun _ _ => by simp only [Once]) (fun _ h => ?_)
  refine once_ite0 h (fun _ _ => by simp only [Once]) (fun _ h => ?_)
  -- the tail
  unfold R.invTailPmG at h ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine once_liftR h (fun b _ h => ?_)
  cases b
  · rw [if_neg Bool.false_ne_true]; simp only [Once]
  rw [if_pos rfl] at h ⊢
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `NEXT_IP`
  refine once_gstep hR0 hW0 (R.obj.Tcb.reg_nz _ _) h (fun r h1 => ?_) (fun r h1 hk Wd4 _ => ?_)
  · rw [R.obj.Tcb.reg_eq] at h1 ⊢
    rw [obj.Tcb.reg.guard (gS := PathObl.guard st (IoRS (st := st) K.uV.ptU Locks s) (IoRS (st := st) K.uV.ptU Locks s)) _ s _
      (P.reg (Locks := Locks) (by simp [layout.reg.NEXT_IP])).1]
    exact h1
  replace h := hk
  rw [R.obj.Tcb.reg_eq] at h1
  obtain ⟨nx, enx, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- the `FAULT_IP` write
  refine once_gstep hR0 hW0 (R.obj.Tcb.set_reg_nz _ _ _) h (fun r h1 => ?_) (fun r h1 hk Wd5 _ => ?_)
  · rw [R.obj.Tcb.set_reg_eq] at h1 ⊢
    rw [obj.Tcb.set_reg.guard (gS := PathObl.guard st (IoRS (st := st) K.uV.ptU Locks s) (IoRS (st := st) K.uV.ptU Locks s)) _ s
      _ _ (P.reg (Locks := Locks) (by simp [layout.reg.FAULT_IP])).1]
    exact h1
  replace h := hk
  rw [R.obj.Tcb.set_reg_eq] at h1
  obtain ⟨x1, es1, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  have ex1 : x1 = L.wr s (regA (L.curW s) layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx 2#u64) := by
    rw [set_reg_ok'] at es1; exact (ok_inj_ff es1).symm
  have hNx1 : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      IoRS (st := st) K.uV.ptU Locks s (L.nodeAt x1 (L.cpu x1) o) := fun o h1 h2 => by
    rw [ex1, LawfulStore.cpu_wr, nodeAt_of_ksb (L.ksb_wr _ _ _)]; exact (P.nd (Locks := Locks) o h1 h2).1
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `update_timestamp`
  have hct : IoRS (st := st) K.uV.ptU Locks s (ctA (L := L) x1) := by
    show IoRS (st := st) K.uV.ptU Locks s (L.nodeAt x1 (L.cpu x1) layout.node.CUR_TIME)
    exact hNx1 _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
  have hcn : IoRS (st := st) K.uV.ptU Locks s (cnA (L := L) x1) := by
    show IoRS (st := st) K.uV.ptU Locks s (L.nodeAt x1 (L.cpu x1) layout.node.CONSUMED)
    exact hNx1 _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
  refine once_gstep hR0 hW0 (R.sched.update_timestamp_nz) h (fun r h1 => ?_) (fun r h1 hk Wd6 _ => ?_)
  · rw [R.sched.update_timestamp_eq] at h1 ⊢
    rw [sched.update_timestamp.guard (gS := PathObl.guard st (IoRS (st := st) K.uV.ptU Locks s) (IoRS (st := st) K.uV.ptU Locks s))
      ar x1 a hct hct hcn hcn]
    exact h1
  replace h := hk
  rw [R.sched.update_timestamp_eq] at h1
  obtain ⟨⟨x2, a1⟩, eu, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  have M := invCM_hmid (Locks := Locks) hA P h0 info nx x1 x2 a1 emi enx es1 eu
  have nd2 : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      IoRS (st := st) K.uV.ptU Locks s (L.nodeAt x2 (L.cpu x2) o) := fun o h1 h2 => by
    rw [M.c, nodeAt_of_ksb M.k]; exact (P.nd (Locks := Locks) o h1 h2).1
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `cur_sc`
  refine once_gstep hR0 hW0 (R.sched.cur_sc_nz) h (fun r h1 => ?_) (fun r h1 hk Wd7 _ => ?_)
  · rw [R.sched.cur_sc_eq] at h1 ⊢
    rw [sched.cur_sc.guard (gS := PathObl.guard st (IoRS (st := st) K.uV.ptU Locks s) (IoRS (st := st) K.uV.ptU Locks s)) x2
      (nd2 _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]))]
    exact h1
  replace h := hk
  rw [R.sched.cur_sc_eq] at h1
  obtain ⟨csc, ecs, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  have ec : csc = L.cscW x2 := by
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) _)] at ecs; exact (ok_inj_ff ecs).symm
  subst ec
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `action`
  refine once_gstep hR0 hW0 (R.sched.action_nz) h (fun r h1 => ?_) (fun r h1 hk Wd8 _ => ?_)
  · rw [R.sched.action_eq] at h1 ⊢
    rw [sched.action.guard (gS := PathObl.guard st (IoRS (st := st) K.uV.ptU Locks s) (IoRS (st := st) K.uV.ptU Locks s)) x2
      (nd2 _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]))]
    exact h1
  replace h := hk
  rw [R.sched.action_eq] at h1
  obtain ⟨i3, ei3, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  refine once_ite0 h (fun _ _ => by simp only [Once]) (fun hi3 h => ?_)
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `yield_to`
  refine once_gstep hR0 hW0 (R.obj.Tcb.yield_to_nz _) h (fun r h1 => ?_) (fun r h1 hk Wd9 _ => ?_)
  · rw [R.obj.Tcb.yield_to_eq] at h1 ⊢
    rw [obj.Tcb.yield_to.guard (gS := PathObl.guard st (IoRS (st := st) K.uV.ptU Locks s) (IoRS (st := st) K.uV.ptU Locks s)) _ x2
      M.yld]
    exact h1
  replace h := hk
  rw [R.obj.Tcb.yield_to_eq] at h1
  obtain ⟨i4, ei4, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  refine once_ite0 h (fun _ _ => by simp only [Once]) (fun hi4 h => ?_)
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `consumed`, `sufficient`
  refine once_gstep hR0 hW0 (R.sched.consumed_nz) h (fun r h1 => ?_) (fun r h1 hk Wd10 _ => ?_)
  · rw [R.sched.consumed_eq] at h1 ⊢
    rw [sched.consumed.guard (gS := PathObl.guard st (IoRS (st := st) K.uV.ptU Locks s) (IoRS (st := st) K.uV.ptU Locks s)) x2
      (nd2 _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]))]
    exact h1
  replace h := hk
  rw [R.sched.consumed_eq] at h1
  obtain ⟨i5, -, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine once_gstep hR0 hW0 (R.sporadic.sufficient_nz _ _) h (fun r h1 => ?_) (fun r h1 hk Wd11 _ => ?_)
  · rw [R.sporadic.sufficient_eq] at h1 ⊢
    rw [sporadic.sufficient.guard (gS := PathObl.guard st (IoRS (st := st) K.uV.ptU Locks s) (IoRS (st := st) K.uV.ptU Locks s))
      ar x2 a1 _ i5 M.rh]
    exact h1
  replace h := hk
  rw [R.sporadic.sufficient_eq] at h1
  obtain ⟨b1, -, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  refine once_ite0 h (fun _ h => ?_) (fun _ _ => by simp only [Once])
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `schedulable_here`
  have htm : IoRS (st := st) K.uV.ptU Locks s (tmA (L := L) x2) := by
    show IoRS (st := st) K.uV.ptU Locks s (L.nodeAt x2 (L.cpu x2) layout.node.TIMER_MIN)
    exact nd2 _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
  have hrh : IoRS (st := st) K.uV.ptU Locks s (rhA (L := L) x2) := by
    show IoRS (st := st) K.uV.ptU Locks s (L.nodeAt x2 (L.cpu x2) layout.node.RELEASE_HEAD)
    exact nd2 _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
  have hct2 : IoRS (st := st) K.uV.ptU Locks s (ctA (L := L) x2) := by
    show IoRS (st := st) K.uV.ptU Locks s (L.nodeAt x2 (L.cpu x2) layout.node.CUR_TIME)
    exact nd2 _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
  refine once_gstep hR0 hW0 (R.fastpath.schedulable_here_nz _) h (fun r h1 => ?_) (fun r h1 hk Wd12 _ => ?_)
  · rw [R.fastpath.schedulable_here_eq] at h1 ⊢
    rw [fastpath.schedulable_here.guard (gS := PathObl.guard st (IoRS (st := st) K.uV.ptU Locks s)
      (IoRS (st := st) K.uV.ptU Locks s)) x2 _ hct2 htm hrh M.td M.rs M.dt M.cd M.af M.dom M.sc M.inq]
    exact h1
  replace h := hk
  rw [R.fastpath.schedulable_here_eq] at h1
  obtain ⟨b2, eb2, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  refine once_ite0 h (fun hb2 h => ?_) (fun _ _ => by simp only [Once])
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `still_holds`
  refine once_gstep hR0 hW0 (R.localinv.Plan.still_holds_nz _) h (fun r h1 => ?_) (fun r h1 hk Wd13 _ => ?_)
  · rw [R.localinv.Plan.still_holds_eq] at h1 ⊢
    rw [still_holds_guard p x2 (fun w hw => pm_seenX hJ hq P w hw)]
    exact h1
  replace h := hk
  rw [R.localinv.Plan.still_holds_eq] at h1
  obtain ⟨b3, eb3, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  refine once_ite0 h (fun hb3 h => ?_) (fun _ _ => by simp only [Once])
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- the IPC buffer
  obtain ⟨bsl, hbsl⟩ := buffer_slot_ok (L.curW s)
  refine once_gstep hR0 hW0 (R.msg.lookup_ipc_buffer_nz _ _) h (fun r h1 => ?_) (fun r h1 hk Wd14 _ => ?_)
  · rw [R.msg.lookup_ipc_buffer_eq] at h1 ⊢
    rw [msg.lookup_ipc_buffer.guard (gS := PathObl.guard st (IoRS (st := st) K.uV.ptU Locks s) (IoRS (st := st) K.uV.ptU Locks s))
      x2 false (L.curW s) hbsl M.ib (M.bs _ hbsl).1 (M.bs _ hbsl).2]
    exact h1
  replace h := hk
  rw [R.msg.lookup_ipc_buffer_eq] at h1
  obtain ⟨buf, ebuf, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  -- the length
  simp only [SProg.blk, ite_ret, SProg.sbind] at h ⊢
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- the invoked slot's cap
  refine once_gstep hR0 hW0 (R.obj.Slot.cap_nz _) h (fun r h1 => ?_) (fun r h1 hk Wd15 _ => ?_)
  · rw [R.obj.Slot.cap_eq] at h1 ⊢
    rw [obj.Slot.cap.guard (gS := PathObl.guard st (IoRS (st := st) K.uV.ptU Locks s) (IoRS (st := st) K.uV.ptU Locks s))
      p.slot x2 r0 r8]
    exact h1
  rw [R.obj.Slot.cap_eq] at h1
  obtain ⟨cap, ecap, rfl⟩ := bind_shape h1
  have hR := hk
  dsimp only at hR ⊢
  -- the decode onward
  simp only [bne_iff_ne, ne_eq, not_not] at hi3 hi4
  rw [hi3] at ei3
  rw [hi4] at ei4
  rw [hb2] at eb2
  rw [hb3] at eb3
  exact pm_decOnceX hA hE ⟨sA, aA, h0⟩ emi ⟨enx, es1, eu, ei3, ei4, eb2, eb3⟩ ecap hR Wd15

end walkX

section roX
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP}
variable {A : Type} {ar : machine.Arch A}

/-- **`roA` at `PmPreG`** (gen 12's [W] `PmRoAccW`, proved; module docstring). -/
theorem pm_roAGX (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hK : RegionOKP K) {number : I64} {m : U64 → U64} :
    PmRoAccW st ar number p K Locks m (R.invBodyPmG number p) (PmPreGX st Cs Ω Sg Ac Locks p K m) := by
  intro s s' a r hE hac Al _
  obtain ⟨s1, a1, h0⟩ := hac
  have hg := pm_accU_of_blkGX (number := number) hA hK (pm_blkGX hA hK) s a s1 a1 hE h0
  have hp := pm_isProgOnX (st := st) (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (Locks := Locks) (p := p) (K := K)
    (μ := m) hA number
  rw [inv_hp hp (Narrow.guard _ _ _) (AltOf.pre hE.1) a] at hg
  have h0' : interp st ar (R.invBodyPmG number p) s a = ok (true, s1, a1) := by
    rw [← inv_hp hp (Narrow.self st) (AltOf.pre hE.1) a]; exact h0
  have hent := pm_entOnceX (number := number) hA s a _ hE ⟨s1, a1, h0⟩ h0'
  exact once_agreeJ hm (fun w hw => hw.1) (fun w hw => hw.1) _ (pm_noZero number p) s s' a _ ∅ ∅ Al.ksb Al.cpu
    Al.masks Al.read hg hent

end roX

end
end Fl4Proofs.P2.E2EP
