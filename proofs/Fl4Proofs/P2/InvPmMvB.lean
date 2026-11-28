/-
# P2 (line pte, generation 15): `mv` pieces — the PageMap decode block on a store checking writes per value

`move` runs the accepted PageMap run on `gd st R (PWs …)` (invj's `invMovePP` route). That store lets the caller's
`STATE` write through per value (`OwnMap.gds_write_state`) and the slot's `CAP0` only for a Frame / Null word
(`OwnMap.gds_write_cap0`), so InvPmBlkD's `pmAccG` (which asks `IoWS (ptU K) ⊆ W`) is restated:

* `dpm_congrF` (`dpm_congr` with the slot's `set_cap` asked only for the Frame cap the decode writes);
* **`pmAccG2`**: `pmAccG` with `hWs` replaced by `SWr` for `RESTART` / `RUNNING`, the `CAP0` write for Frame / Null
  words (`nof_enc_framePm`), `W` at `CAP1`, and `W` at the PTE words (non-decision words under `PWs`).
  (`pmFinG` needs no write-set hypothesis beyond `IoWr` and `SWr RUNNING`, so it applies to `gd` as it is.)
* **`pmAccG2C`** (gen-45 p3mc, moved here from P2/InvPmGdV): `pmAccG2` with the `IoRS (ptU K) s` reads asked only
  where a word class `G` holds (at the words the block reads) and the leaf read / written only when locked;
  `pmAccG2` is its one-line instance at `G := fun _ => True` (statement unchanged).

No named premise. New module; gen 45 re-proves `pmAccG2` as a corollary (statement unchanged).
-/
import Fl4Proofs.P2.InvPmMvA
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField NullOrFrame TcbSlot)

noncomputable section

section congr
variable {S : Type} {A : Type} (ar : machine.Arch A)

/-- **`dpm_congr` with the slot's `set_cap` asked only for the cap the decode writes.** -/
theorem dpm_congrF (m1 m2 : machine.Store S) {x : S} {a : A} {length buf : U64} {slot : obj.Slot}
    {ex : Array obj.Slot 3#usize} {fp rt asid va : U64} {mp : Bool} {t x0 root rasid v0 v1 v2 e : U64}
    (hc1 : sched.cur_thread m1 x = ok t) (hc2 : sched.cur_thread m2 x = ok t)
    (hx0 : vspace.extra ex 0#usize = ok (some x0))
    (ha0 : msg.syscall_arg m1 x t buf 0#u64 = ok v0) (hb0 : msg.syscall_arg m2 x t buf 0#u64 = ok v0)
    (ha1 : msg.syscall_arg m1 x t buf 1#u64 = ok v1) (hb1 : msg.syscall_arg m2 x t buf 1#u64 = ok v1)
    (ha2 : msg.syscall_arg m1 x t buf 2#u64 = ok v2) (hb2 : msg.syscall_arg m2 x t buf 2#u64 = ok v2)
    (hk1 : obj.Slot.cap m1 x0 x = ok (.Pml4 root true rasid)) (hk2 : obj.Slot.cap m2 x0 x = ok (.Pml4 root true rasid))
    (hcv : vspace.check_vspace m1 x (.Pml4 root true rasid) = vspace.check_vspace m2 x (.Pml4 root true rasid))
    (hp1 : vspace.page_entry_slot m1 x root v0 .Small = ok (.Ok e))
    (hp2 : vspace.page_entry_slot m2 x root v0 .Small = ok (.Ok e))
    (hfa : ∀ f, vspace.frame_address m1 ar x a f = vspace.frame_address m2 ar x a f)
    (hmu : ∀ p at0 r l, vspace.make_user_page m1 x p at0 r l = vspace.make_user_page m2 x p at0 r l)
    (hhp : vspace.huge_pages m1 x = vspace.huge_pages m2 x)
    (hst : sched.set_thread_state m1 x t sched.TS_RESTART = sched.set_thread_state m2 x t sched.TS_RESTART)
    (hsc : ∀ y, obj.Slot.set_cap m1 slot y (.Frame fp .Small rt false true false rasid v0) =
      obj.Slot.set_cap m2 slot y (.Frame fp .Small rt false true false rasid v0))
    (hwm : ∀ y a' as' va' d, vspace.write_mapping m1 ar y a' e as' va' d = vspace.write_mapping m2 ar y a' e as' va' d) :
    vspace.decode_page_map m1 ar x a length slot
        { ptr := fp, size := .Small, rights := rt, is_device := false, mapped := mp, is_ept := false, asid,
          vaddr := va } buf ex =
      vspace.decode_page_map m2 ar x a length slot
        { ptr := fp, size := .Small, rights := rt, is_device := false, mapped := mp, is_ept := false, asid,
          vaddr := va } buf ex := by
  unfold vspace.decode_page_map
  simp only [hc1, hc2, hx0, ha0, hb0, ha1, hb1, ha2, hb2, hk1, hk2, hcv, hp1, hp2, hfa, hmu, hhp, hst, hsc, hwm,
    bind_ok, vspace.mapped_root, uncurry_apply_pair, Bool.false_eq_true, ↓reduceIte,
    core.result.Result.Insts.CoreOpsTry.branch]

end congr

section acc
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP} {μ : U64 → U64}
variable {A : Type} {ar : machine.Arch A}

set_option maxHeartbeats 2000000 in
/-- **`pmAccG2` cut by a word class `G`** (module docstring): reads of `IoRS (ptU K) s` words asked only where `G`
holds, the leaf read and written only when locked (gen-45 p3mc; `pmAccG2` is its instance at `G := True`). -/
theorem pmAccG2C (hA : P0.ArchTotal ar) {s : S} {a : A} {info : msginfo.MessageInfo} {nx : U64} {s1 s2 : S}
    {a1 : A} {buf length : U64} {cap : capability.Cap} {y : (core.result.Result Unit error.Exc) × S × A}
    {R W G : U64 → Prop} {gS : machine.Store S} [GRd gS st R] [GWr gS st W]
    (hE : PmPreG st Cs Ω Sg Ac Locks p K μ s)
    (hR : ∀ b, IoRS (st := st) K.ptU Locks s b → G b → R b) (hRu : ∀ b, UserW K.toKLayout b → R b)
    (hRe : ∀ b, b ∈ K.ptes → Locks s b → PmRS st K Locks s b → R b)
    (hW : IoWr st W K.heap.scBits s)
    (hsw : ∀ v, v = sched.TS_RESTART ∨ v = sched.TS_RUNNING → SWr gS st (L.curW s) v)
    (hc0 : ∀ x v, OwnMap.NullOrFrame v → gS.write x p.slot v = st.write x p.slot v)
    (hW8 : W (core.num.U64.wrapping_add p.slot 8#u64))
    (hWu : ∀ b, UserW K.toKLayout b → W b) (hWe : ∀ b, b ∈ K.ptes → Locks s b → W b)
    (hGn : ∀ o : U64, o.val < 4288 → G (L.nodeAt s (L.cpu s) o))
    (hGr : ∀ r : U64, r.val < 384 → G (regA (L.curW s) r))
    (hGs : ∀ q ∈ K.slots, G q ∧ G (core.num.U64.wrapping_add q 8#u64))
    (hGv : ∀ b, VsW K.toKLayout b → b ∉ K.ptes → G b)
    (hGst : G (stA (L.curW s))) (hGsc : G (scA (L.curW s))) (hGiq : G (inqA (L.curW s)))
    (hGm : G (maxA (L.cscW s))) (hGi : G (core.num.U64.wrapping_add (L.curW s) 3512#u64))
    (hGf : G (core.num.U64.wrapping_add (L.ksb s) layout.ks.FEATURES))
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
  -- the decode's first reads and its walk on `gS`, cut by `G`
  obtain ⟨-, -, hargs, x0', root', rasid', hx0', hcxg, hcx', -⟩ :=
    pm_decRdC (gS := gS) hA hE0 C hR hGn hGr hGs
  have hWk := pm_decWalkC (gS := gS) hA hE0 C hR hGv (root := root) (rasid := rasid) hu
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
  -- the node, the caller's words
  have hctR : R (L.nodeAt s2 (L.cpu s2) layout.node.CUR_THREAD) := by
    rw [I.cp, nodeAt_of_ksb I.k]
    exact hR _ (P.nd layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD])
      (by simp [layout.node.CUR_THREAD])).1 (hGn _ (by simp [layout.node.CUR_THREAD]))
  have hN : ∀ x : S, (∀ o, L.nodeAt x (L.cpu x) o = L.nodeAt s (L.cpu s) o) → NodeSt (L := L) R W x := by
    have n0 : IoRS (st := st) K.ptU Locks s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) :=
      (P.nd layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])).1
    have n1 : IoRS (st := st) K.ptU Locks s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) :=
      (P.nd layout.node.SCHED_ACTION (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])).1
    have n1w : W (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) :=
      hW.nd _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
    intro x hn
    refine ⟨?_, ?_, ?_⟩
    · rw [hn]; exact hR _ n0 (hGn _ (by simp [layout.node.CUR_THREAD]))
    · rw [hn]; exact hR _ n1 (hGn _ (by simp [layout.node.SCHED_ACTION]))
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
  have emx : L.mem (L.wr s2 (stA (L.curW s)) sched.TS_RESTART) (scA (L.curW s)) = L.mem s2 (scA (L.curW s)) := by
    have kw := (KeepA.refl ha2 hrun).wr hK (b := stA (L.curW s)) (v := sched.TS_RESTART) (Or.inr rfl)
      (fun _ => Or.inl rfl)
    exact kw.mem (field_aligned P.tA (by simp) (by simp)) (iotw_field P.tA (by simp) (by simp))
  have hmx2 : R (maxA (L.mem (L.wr s2 (stA (L.curW s)) sched.TS_RESTART) (scA (L.curW s)))) := by
    rw [emx, hsc2]
    exact hR _ hmxR hGm
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
    rw [I.k]; exact hR _ (P.ksw (by simp [layout.ks.FEATURES]) (by simp [layout.ks.FEATURES])) hGf
  have hnT : ¬ TcbSlot K.ptU p.slot := notTcbSlot_of hO
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
    exact sched.set_thread_state.guardV (gS := gS) s2 (L.curW s) _ (hN s2 hnd2) (hsw _ (Or.inl rfl))
      (hR _ rst.1 hGst) (hR _ rsc hGsc) hmx2 (hR _ riq hGiq)
  have hpeg : vspace.page_entry_slot gS s2 root (L.mem s2 (regA (L.curW s2) layout.reg.R10)) .Small =
      ok (.Ok e) := by rw [hct, hWk.2 hf]; exact hpe2
  have hNr : (0#u64 : U64) < msg.N_MSG_REGISTERS ∧ (1#u64 : U64) < msg.N_MSG_REGISTERS ∧
      (2#u64 : U64) < msg.N_MSG_REGISTERS := by simp [msg.N_MSG_REGISTERS]
  refine ⟨?_, ?_⟩
  · rw [hdst gS hcg, dpm_congrF ar gS st hcg hc2 hx0 ((hargs _ hNr.1 buf).trans hg0) hg0
      ((hargs _ hNr.2.1 buf).trans hg1) hg1 ((hargs _ hNr.2.2 buf).trans hg2) hg2 (hcxg.trans hcx2) hcx2
      hWk.1 hpeg hpe2' (fun f => vspace.frame_address.guardK ar s2 a1 f) (vspace.make_user_page.guardF s2 hFt)
      (vspace.huge_pages.guardF s2 hFt) hst hscF
      (fun y a' as' va' d => funext fun dd =>
        vspace.write_mapping.guard ar y a' e as' va' d dd (hRe _ hpt hle hRS) (hWe _ hpt hle))]
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
      refine invRep.guard_okS (gS := gS) (hR _ rst.1 hGst) (hsw _ (Or.inr rfl)) (hR _ rsc hGsc)
        (hR _ riq hGiq) (hW.reg _ rB384) (hW.reg _ rM384) ?_ hz
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
      rw [e6, hsc2]; exact hR _ hmxR hGm
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
        hR _ (P.gate (off := 3512#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField])) hGi
      have hlb : msg.lookup_ipc_buffer st s2 true (L.curW s) = msg.lookup_ipc_buffer st s true (L.curW s) :=
        lookup_buf_keep P.tA true tk
      have hbuf0 := invBufJ8_of hJ
      have hbw : ∀ b, msg.lookup_ipc_buffer st s2 true (L.curW s) = ok b → BufW W b ∧ BufW R b := by
        intro b eb
        rw [hlb] at eb
        exact ⟨fun h0 i hi => hWu _ (hbuf0 b eb h0 i hi), fun h0 i hi => hRu _ (hbuf0 b eb h0 i hi)⟩
      rw [invRep.guard_errPm (gS := gS) er (fun e1 => PathObl.syscall.reply_error.guard (gS := gS) s2 (L.curW s) e1
        hbsl hI (hR _ hbs.1 (hGs _ hb1).1) (hR _ hbs.2 (hGs _ hb1).2) (fun r hr => hW.reg r hr) hbw)]
      exact hz

/-- **`pmAccG` for stores that check the `STATE` write per value and the slot's `CAP0` write per word** (module
docstring): `pmAccG2C` at `G := True`. -/
theorem pmAccG2 (hA : P0.ArchTotal ar) {s : S} {a : A} {info : msginfo.MessageInfo} {nx : U64} {s1 s2 : S} {a1 : A}
    {buf length : U64} {cap : capability.Cap} {y : (core.result.Result Unit error.Exc) × S × A}
    {R W : U64 → Prop} {gS : machine.Store S} [GRd gS st R] [GWr gS st W]
    (hE : PmPreG st Cs Ω Sg Ac Locks p K μ s)
    (hR : ∀ b, IoRS (st := st) K.ptU Locks s b → R b) (hRu : ∀ b, UserW K.toKLayout b → R b)
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
    ∀ z, invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z → invRep gS (L.curW s) y.2.1 y.2.2 y.1 = ok z :=
  pmAccG2C (G := fun _ => True) hA hE (fun b h _ => hR b h) hRu (fun b _ _ h => hRe b h) hW hsw hc0 hW8 hWu
    (fun b h _ => hWe b h) (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ => ⟨trivial, trivial⟩)
    (fun _ _ _ => trivial) trivial trivial trivial trivial trivial trivial emi C hcap hy

end acc

end
end Fl4Proofs.P2.E2EP
