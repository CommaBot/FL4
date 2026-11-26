/-
# P2 (line pte, generation 15): the PageMap decode block on any store answering as `st` (`blk`, fourth part)

At a `PmPreG` entry `s` with decode state `s2` (`InvChk`), on any store `gS` that reads `IoRS (ptU K) s`, the aligned
user words and `PmRS s` as `st` and writes `W ⊇ IoWS (ptU K) s ∪` aligned user words `∪ PmWS s` (with `IoWr`):

* `wm_st` (`write_mapping`'s state is one write of the leaf), **`pmDecKeep`** (an `Ok` decode keeps `KeepU` at
  `KSUPm (ptU K)`: the caller's `STATE`, the invoked slot's words, the leaf, a PTE word, hence a `ptU K` user word),
  **`pmRun`** (decode then `invRep`: reply `Ok ()`, `KeepU`; an error reply writes registers and buffer words);
* **`pmAccG`**: `decode_invocation` (→ `decode_page_map`, `dpm_congr`) and `invRep` run on `gS` as on `st`;
* **`pmFinG`**: the reply is `Ok ()` and `FinOK` holds after it (slhuf's `cmFin8` route at `KSUPm (ptU K)`).

No named premise (the error reply's buffer words: `invBufJ8_of`). New module; no existing statement changes.
-/
import Fl4Proofs.P2.InvPmBlkC
import Fl4Proofs.P2.InvCMG
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField NullOrFrame TcbSlot)

noncomputable section

section run
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type} (ar : machine.Arch A)

/-- `write_mapping`'s state is one write of the leaf. -/
theorem wm_st (hA : P0.ArchTotal ar) (y : S) (a : A) (sl e as' va' : U64) (d : Bool) :
    vspace.write_mapping st ar y a sl e as' va' d ⦃ r => ∃ a', r = (L.wr y sl e, a') ⦄ := by
  unfold vspace.write_mapping
  refine WP.spec_bind (LawfulStore.read_spec y sl) fun old _ => ?_
  refine WP.spec_bind (LawfulStore.write_spec y sl e) fun s1 e1 => ?_
  subst e1
  refine WP.spec_bind (Pₘ := fun _ => True) (by p0_auto) fun _ _ => ?_
  simp only [lift, bind_ok]
  split
  · exact (WP.spec_ok _).2 ⟨_, rfl⟩
  refine WP.spec_bind (P0.vspace.rights_raised.p0 _ _) fun _ _ => ?_
  split
  · exact WP.spec_bind (hA.invalidate_page a _ _) fun _ _ => (WP.spec_ok _).2 ⟨_, rfl⟩
  split
  · refine WP.spec_bind (P0.vspace.rights_lowered.p0 _ _) fun _ _ => ?_
    split
    · exact (WP.spec_ok _).2 ⟨_, rfl⟩
    · exact WP.spec_bind (hA.invalidate_asid a _) fun _ _ => (WP.spec_ok _).2 ⟨_, rfl⟩
  · exact WP.spec_bind (hA.invalidate_asid a _) fun _ _ => (WP.spec_ok _).2 ⟨_, rfl⟩

variable {K : KLayout} {s2 : S} {a1 : A} {t slot e : U64}

/-- **An `Ok` decode keeps `KeepU` at `KSUPm K`** (module docstring). -/
theorem pmDecKeep (hA : P0.ArchTotal ar) (F : SchedOK (L := L) s2 t) (O : UsrOK (L := L) (KSUPm K) s2 t)
    (ha : L.actionW s2 = sched.ACTION_RESUME_CURRENT)
    (hr : L.mem s2 (stA t) = sched.TS_RESTART ∨ L.mem s2 (stA t) = sched.TS_RUNNING)
    (hL : Slot8 K) (hsl : slot ∈ K.slots) (heU : UserW (KSUPm K) e)
    {y : (core.result.Result Unit error.Exc) × S × A} (hout : DpmOut st ar s2 a1 t slot e y)
    (hok : y.1 = .Ok ()) : KeepU st (KSUPm K) s2 t y.2.1 := by
  rcases hout with ⟨-, -, se, h⟩ | ⟨-, x1, x2, c, pte, as', va', d, h1, h2, h3⟩
  · rw [hok] at h; cases h
  have K1 : KeepU st (KSUPm K) s2 t x1 := KeepU.of_keepA ((KeepA.refl ha hr).sts F (Or.inl rfl) h1)
  have K2 : KeepU st (KSUPm K) s2 t x2 := K1.users F O (wi_usuPm (set_cap_keepPm hL hsl h2))
  have e3 : y.2.1 = L.wr x2 e pte := by
    obtain ⟨a', ha'⟩ := post_of_ok (wm_st ar hA x2 a1 e pte as' va' d) h3
    rw [Prod.mk.injEq] at ha'
    exact ha'.1
  rw [e3]
  exact KU_userPm F O K2 heU

/-- **Decode then reply: `Ok ()` and `KeepU` at `KSUPm K`** (module docstring). -/
theorem pmRun (hA : P0.ArchTotal ar) (F : SchedOK (L := L) s2 t) (O : UsrOK (L := L) (KSUPm K) s2 t)
    (ha : L.actionW s2 = sched.ACTION_RESUME_CURRENT)
    (hr : L.mem s2 (stA t) = sched.TS_RESTART ∨ L.mem s2 (stA t) = sched.TS_RUNNING)
    (hL : Slot8 K) (hsl : slot ∈ K.slots) (heU : UserW (KSUPm K) e)
    (hbuf : ∀ b, msg.lookup_ipc_buffer st s2 true t = ok b → b ≠ 0#u64 → ∀ i : U64, i.val < 128 →
      UserW K (core.num.U64.wrapping_add b (core.num.U64.wrapping_mul i 8#u64)))
    {y : (core.result.Result Unit error.Exc) × S × A} {z : S × A × core.result.Result Unit error.Exc}
    (hout : DpmOut st ar s2 a1 t slot e y) (hz : invRep st t y.2.1 y.2.2 y.1 = ok z) :
    z.2.2 = .Ok () ∧ KeepU st (KSUPm K) s2 t z.1 := by
  have hout0 := hout
  rcases hout with ⟨hx, -, se, he⟩ | ⟨hok, -⟩
  · obtain ⟨r, x, a2⟩ := y
    simp only at hx he hz
    subst hx he
    unfold invRep at hz
    obtain ⟨q0, eq0, hz⟩ := bind_eq_ok hz
    cases ok_inj_ff hz
    obtain ⟨s5, es5, e5⟩ := bind_eq_ok eq0
    cases ok_inj_ff e5
    exact ⟨rfl, reply_error_kuPm F O (KeepU.of_keepA (KeepA.refl ha hr))
      (fun b eb hne i hi => usu_of_userPm (hbuf b eb hne i hi)) es5⟩
  · have k := pmDecKeep ar hA F O ha hr hL hsl heU hout0 hok
    obtain ⟨r, x, a2⟩ := y
    simp only at hok k hz
    subst hok
    exact invRep_ok_kuPm F O k hz

end run

section acc
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP} {μ : U64 → U64}
variable {A : Type} {ar : machine.Arch A}

/-- **The PageMap decode block on any store answering as `st`** (module docstring). -/
theorem pmAccG (hA : P0.ArchTotal ar) {s : S} {a : A} {info : msginfo.MessageInfo} {nx : U64} {s1 s2 : S} {a1 : A}
    {buf length : U64} {cap : capability.Cap} {y : (core.result.Result Unit error.Exc) × S × A}
    {R W : U64 → Prop} {gS : machine.Store S} [GRd gS st R] [GWr gS st W]
    (hE : PmPreG st Cs Ω Sg Ac Locks p K μ s)
    (hR : ∀ b, IoRS (st := st) K.ptU Locks s b → R b) (hRu : ∀ b, UserW K.toKLayout b → R b)
    (hRe : ∀ b, PmRS st K Locks s b → R b)
    (hW : IoWr st W K.heap.scBits s) (hWs : ∀ b, IoWS (st := st) K.ptU Locks s b → W b)
    (hWu : ∀ b, UserW K.toKLayout b → W b) (hWe : ∀ b, PmWS st K Locks s b → W b)
    (emi : msg.msg_info st s (L.curW s) = ok info) (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1)
    (hcap : obj.Slot.cap st p.slot s2 = ok cap)
    (hy : syscall.decode_invocation st ar s2 a1 info.label length p.slot cap true true true false buf p.extra =
      ok y) :
    syscall.decode_invocation gS ar s2 a1 info.label length p.slot cap true true true false buf p.extra = ok y ∧
    ∀ z, invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z → invRep gS (L.curW s) y.2.1 y.2.2 y.1 = ok z := by
  obtain ⟨fp, rt, asid, va, mp, x0, root, rasid, e, hcs, hcs2, hx0, hxK, hcx2, hcv2, hpe2, hpt, hle, hRS, hWS, hu,
    hf, hsl, hsl0, hO⟩ := pm_s2 hA hE C
  have hE0 := hE
  obtain ⟨⟨hJ, hq, hG⟩, -, -⟩ := hE
  have Pb := hq.1.1.1
  have P := Pb.ptU hG
  -- the decode's first reads and its walk on `gS` (a store reading `IoRS (ptU K) s` as `st`)
  haveI hIo : GRd gS st (IoRS (st := st) K.ptU Locks s) :=
    { read := fun hy s => GRd.read (g := gS) (hR _ hy) s
      read_pair := fun hy h8 s => GRd.read_pair (g := gS) (hR _ hy) (hR _ h8) s
      ks_base := gst_ks_base
      cur_cpu := gst_cur_cpu
      frame_masks := gst_frame_masks }
  obtain ⟨-, -, hargs, x0', root', rasid', hx0', hcxg, hcx', -⟩ := pm_decRd (gS := gS) hA hE0 C
  have hWk := pm_decWalk (gS := gS) hA hE0 C (root := root) (rasid := rasid) hu
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
  have hL : Slot8 K.ptU := fun q hq => P.lay.slot8 q hq
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
    have n0 : IoRS (st := st) K.ptU Locks s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) :=
      (P.nd layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])).1
    have n1 : IoRS (st := st) K.ptU Locks s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) :=
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
  have rsc : IoRS (st := st) K.ptU Locks s (scA (L.curW s)) :=
    P.gate (off := 3464#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField])
  have riq : IoRS (st := st) K.ptU Locks s (inqA (L.curW s)) :=
    (P.home (off := 3592#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).1
  have hmxR : IoRS (st := st) K.ptU Locks s (maxA (L.cscW s)) := by
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
  have hmx2 : IoRS (st := st) K.ptU Locks s
      (maxA (L.mem (L.wr s2 (stA (L.curW s)) sched.TS_RESTART) (scA (L.curW s)))) := by
    have kw := (KeepA.refl ha2 hrun).wr hK (b := stA (L.curW s)) (v := sched.TS_RESTART) (Or.inr rfl)
      (fun _ => Or.inl rfl)
    have e : L.mem (L.wr s2 (stA (L.curW s)) sched.TS_RESTART) (scA (L.curW s)) = L.mem s2 (scA (L.curW s)) :=
      kw.mem (field_aligned P.tA (by simp) (by simp)) (iotw_field P.tA (by simp) (by simp))
    rw [e, hsc2]
    exact hmxR
  -- the layout `KSUPm (ptU K)`
  have hn2 : ∀ o : U64, o.val < 4288 → ¬ UserW (KSUPm K.ptU) (L.nodeAt s2 (L.cpu s2) o) := fun o ho => by
    rw [I.cp, nodeAt_of_ksb I.k]; exact not_usuPm (P.node_notUser ho) (P.node_notSlot ho)
  have hmx : ¬ UserW (KSUPm K.ptU) (maxA (L.mem s2 (scA (L.curW s)))) := by
    rw [← hct, I.F.i]
    exact not_usuPm (P.sc_notUser (P.hSc _ P.cscS) I.F.q.2.2.2.1) (P.sc_notSlot (P.hSc _ P.cscS) I.F.q.2.2.2.1)
  have htU : ∀ t, K.heap t = some .tcb → ∀ k : U64, 192 ≤ k.val → k.val < 4096 →
      ¬ UserW (KSUPm K.ptU) (core.num.U64.wrapping_add t k) := fun t ht k h1 h2 =>
    not_usuPm (P.tcb_notUser ht h1 h2) (P.tcb_notSlot ht h1 h2)
  have O : UsrOK (L := L) (KSUPm K.ptU) s2 (L.curW s) :=
    ⟨hn2, fun k h1 h2 => htU _ (P.hT _ P.cT) k h1 h2, hmx⟩
  have heU : UserW (KSUPm K.ptU) e := ⟨hRS.1, Or.inl (Or.inr hpt)⟩
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
  have hnT : ¬ TcbSlot K.ptU p.slot := notTcbSlot_of hO
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
  refine ⟨?_, ?_⟩
  · rw [hdst gS hcg, dpm_congr ar gS st hcg hc2 hx0 ((hargs _ hNr.1 buf).trans hg0) hg0
      ((hargs _ hNr.2.1 buf).trans hg1) hg1 ((hargs _ hNr.2.2 buf).trans hg2) hg2 (hcxg.trans hcx2) hcx2
      hWk.1 hpeg hpe2' (fun f => vspace.frame_address.guardK ar s2 a1 f) (vspace.make_user_page.guardF s2 hFt)
      (vspace.huge_pages.guardF s2 hFt) hst (fun y c => obj.Slot.set_cap.guard p.slot y c hW0 hW8)
      (fun y a' as' va' d => funext fun dd => vspace.write_mapping.guard ar y a' e as' va' d dd (hRe _ hRS) (hWe _ hWS))]
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
      have hbuf0 := invBufJ8_of hJ
      have hbw : ∀ b, msg.lookup_ipc_buffer st s2 true (L.curW s) = ok b → BufW W b ∧ BufW R b := by
        intro b eb
        rw [hlb] at eb
        exact ⟨fun h0 i hi => hWu _ (hbuf0 b eb h0 i hi), fun h0 i hi => hRu _ (hbuf0 b eb h0 i hi)⟩
      rw [invRep.guard_errPm (gS := gS) er (fun e1 => PathObl.syscall.reply_error.guard (gS := gS) s2 (L.curW s) e1 hbsl hI
        (hR _ hbs.1) (hR _ hbs.2) (fun r hr => hW.reg r hr) hbw)]
      exact hz

end acc

end
end Fl4Proofs.P2.E2EP
