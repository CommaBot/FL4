/-
# P2 (line mmuAD, gen 17): **PageMap in VM epochs, part B** — the accepted run on the guarded store

Copies of the native accepted-run block (InvPmDecRd `pm_decRd` / `pm_decWalk`, InvPmBlkC `pm_s2`, InvPmBlkD
`pmAccG`, InvPmBlkE `pmFinG`, InvPmBlkF `pm_blkG`) at the VM entry fact `PmPreGX` (E2EPAD2A), at the read-set
layout `K.uV.ptU`:
* the walk reads only `VsW` words off `XD` (`pm_vsRdX`, from `WalkP`), which are `IoRS K.uV.ptU` words
  (`pm_vsW_ioRSX`);
* the leaf: `small_page_entry` answers it (`hspe`), so `WalkP.lf` makes it a `K.ptes` / `VsW` word and `PmGX.ne0` makes
  it non-null (natively `pm_leaf_pte` / `SlJAtZ.spe_ne0`);
* the error reply's buffer words: `InvLXS.buf8` (natively `invBufJ8_of`); the invoked slot is not 0: `InvLX.hz`;
* **`PmBlkUW2X`** (`PmBlkUW2` with `FinOK` at `K.uV.ptU`), **`pm_blkGX`**: it at `PmPreGX` (`IoRS K.uV.ptU ⊆ PmRSU`: `pmRSU_ioRSX`).

No named premise. New module; no existing statement changes.
-/
import Fl4Proofs.P2.E2EPAD2A
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField NullOrFrame TcbSlot)
open Fl4Proofs.P2.E2E (Once ReadOnce StartAt SP)
open Fl4Proofs.P2.Serial (Cfg Init ArmInv NoLoc RunAll)

noncomputable section

section words
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP} {μ : U64 → U64}
  {s : S} {x : U64}

/-- A `VsW` word off `XD` is an `IoRS K.uV.ptU` word. -/
theorem pm_vsW_ioRSX {w : U64} (hw : VsW K.toKLayout w) (hp : ¬ XD K w) :
    IoRS (st := st) K.uV.ptU Locks s w := by
  refine ⟨hw.1, ?_, Or.inr (own_none (K := K.uV.ptU) hw.2.1)⟩
  rintro ((hu | hu) | hu)
  · exact hw.2.2 hu
  · exact hp (Or.inl ⟨hw.1, hu⟩)
  · exact hp (Or.inr hu)

/-- **At a `PmPreFX` state the walk reads only `VsW` words off `XD`** (`WalkP`). -/
theorem pm_vsRdX (hE : PmPreFX st Cs Ω Sg Ac Locks p K μ s) (asid va : U64) (hv : Fl4Proofs.P3.Vs.UserV va) :
    VsRdG st (fun b => VsW K.toKLayout b ∧ ¬ XD K b) s asid va :=
  (hE.2.2.walk asid va (by
    have hU : fl4_abi.consts.USER_TOP.val = 140737488355327 := by unfold fl4_abi.consts.USER_TOP; rfl
    show va.val ≤ fl4_abi.consts.USER_TOP.val
    rw [hU]; exact hv)).1

theorem pmRSU_ioRSX (h : PmGX st K s) (hx : IoRS (st := st) K.uV.ptU Locks s x) : PmRSU st K Locks s x :=
  pmRS_U (pmRS_of_ptUX h hx)

theorem pmWSU_ioWSX (hK : RegionOKP K) (hx : IoWS (st := st) K.uV.ptU Locks s x) : PmWSU st K Locks s x :=
  pmWS_U ⟨hx.1, wpermP_of_V hK (wpermV_of_own' hK.base hx.2)⟩

end words


section rdX
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP} {μ : U64 → U64}
variable {A : Type} {ar : machine.Arch A}

/-- **The PageMap decode's first reads at the decode state** (module docstring). -/
theorem pm_decRdX (hA : P0.ArchTotal ar) {s : S} {gS : machine.Store S} [GRd gS st (IoRS (st := st) K.uV.ptU Locks s)]
    {a : A} {nx : U64} {s1 s2 : S} {a1 : A}
    (hE : PmPreGX st Cs Ω Sg Ac Locks p K μ s) (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1) :
    L.curW s2 = L.curW s ∧
    sched.cur_thread gS s2 = sched.cur_thread st s2 ∧
    (∀ i, i < msg.N_MSG_REGISTERS → ∀ buf,
      msg.syscall_arg gS s2 (L.curW s2) buf i = msg.syscall_arg st s2 (L.curW s2) buf i) ∧
    ∃ x0 root rasid, vspace.extra p.extra 0#usize = ok (some x0) ∧
      obj.Slot.cap gS x0 s2 = obj.Slot.cap st x0 s2 ∧
      obj.Slot.cap st x0 s2 = ok (.Pml4 root true rasid) ∧
      vspace.find_vspace_for_asid st s rasid = ok (.Ok root) := by
  obtain ⟨⟨hJ, hq, hG⟩, hEx, hRt⟩ := hE
  have Pb := hq.1.1.1
  have P := Pb.ptUX hG
  obtain ⟨-, es1, eu, -, -, ehere, -⟩ := C
  have Ent := P.ent (Locks := Locks) (P.ioWr (Locks := Locks))
  have Hf := here_facts ehere
  have I := IoS2.of_ent hA Ent es1 eu Hf.sc
  have hct : L.curW s2 = L.curW s := I.cur
  have w0 := prefix_writes ar hA Pb.tp Pb.np Pb.cT es1 eu
  have hL : Slot8 K.toKLayout := fun q hq => Pb.lay.slot8 q hq
  have ag : ∀ b, SlotW K.toKLayout b → Aligned b → L.mem s2 b = L.mem s b := fun b hs hb => by
    obtain ⟨q, hq, hbq⟩ := hs
    exact Pb.slot_keep w0 hq hbq hb
  refine ⟨hct, ?_, ?_, ?_⟩
  · have hctR : IoRS (st := st) K.uV.ptU Locks s (L.nodeAt s2 (L.cpu s2) layout.node.CUR_THREAD) := by
      rw [I.cp, nodeAt_of_ksb I.k]
      exact (P.nd layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])).1
    exact sched.cur_thread.guard (gS := gS) s2 hctR
  · intro i hi buf
    refine msg.syscall_arg.guard_lt (gS := gS) s2 (L.curW s2) buf i hi (fun r hr => ?_)
    rw [hct]
    exact (P.reg (msgReg_lt hr)).1
  · obtain ⟨⟨-, ⟨t, info, ex, ht, hi, hpw⟩, harm, -⟩, -⟩ := hq
    have et : t = L.curW s := by rw [cur_thread_ok] at ht; exact (ok_inj_ff ht).symm
    subst et
    rw [(harm _ info (cur_thread_ok s) hi).1] at hpw
    obtain ⟨-, -, -, -, root, rasid, -, x0, -, -, hx0, hx00, hcx, -⟩ := plan_with_mapF hpw
    have hkp := (plan_with_kp hpw).2
    rw [← hkp] at hx0
    obtain ⟨x0', hx0', hxK⟩ := pmEx_slots Pb hEx
    rw [hx0] at hx0'
    obtain rfl := ok_inj_ff hx0'
    have hc2 : obj.Slot.cap st x0 s2 = obj.Slot.cap st x0 s := cap_agree hL hxK ag
    have hR := P.slot (Locks := Locks) (sl := x0) hxK (Or.inr (cap_pml4_nof hcx))
    refine ⟨x0, root, rasid, ?_, obj.Slot.cap.guard (gS := gS) x0 s2 hR.1 hR.2, hc2.trans hcx,
      hRt x0 root rasid hx0 hcx⟩
    unfold vspace.extra obj.Slot.is_null
    simp only [show ¬ (0#usize ≥ 3#usize) by decide, ↓reduceIte, hx0, bind_ok, decide_eq_true_eq, hx00]

/-- **The PageMap decode's walk at the decode state** on a store reading `IoRS (ptU K) s` as `st`: `check_vspace`
and the small-page `page_entry_slot` give `st`'s answers at `s2` (`pm_vsRdX` + `vsRdG_tr` twice: the walk reads only
`VsW` words off `K.ptes`, which the prefix does not write). -/
theorem pm_decWalkX (hA : P0.ArchTotal ar) {s : S} {gS : machine.Store S}
    [GRd gS st (IoRS (st := st) K.uV.ptU Locks s)] {a : A} {nx : U64} {s1 s2 : S} {a1 : A}
    (hE : PmPreGX st Cs Ω Sg Ac Locks p K μ s) (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1)
    {root rasid va : U64} (hva : ¬ va > fl4_abi.consts.USER_TOP) :
    vspace.check_vspace gS s2 (.Pml4 root true rasid) = vspace.check_vspace st s2 (.Pml4 root true rasid) ∧
    (vspace.find_vspace_for_asid st s rasid = ok (.Ok root) →
      vspace.page_entry_slot gS s2 root va .Small = vspace.page_entry_slot st s2 root va .Small) := by
  have hV := pm_vsRdX hE.1 rasid va (userV_of_not_gt hva)
  obtain ⟨⟨-, hq, -⟩, -, -⟩ := hE
  have Pb := hq.1.1.1
  obtain ⟨-, es1, eu, -, -, -, -⟩ := C
  have w0 := prefix_writes ar hA Pb.tp Pb.np Pb.cT es1 eu
  have hrs : ∀ b, (VsW K.toKLayout b ∧ ¬ XD K b) → st.read s2 b = st.read s b := fun b hb => by
    rw [L.read_eq, L.read_eq, w0.2.2 b hb.1.1 (Pb.vs_notPreW hb.1)]
  have hrg : ∀ b, (VsW K.toKLayout b ∧ ¬ XD K b) → gS.read s2 b = st.read s b := fun b hb =>
    (gst_read (pm_vsW_ioRSX (Locks := Locks) (s := s) hb.1 hb.2)).trans (hrs b hb)
  have hks : st.ks_base s2 = st.ks_base s := by rw [L.ks_base_eq, L.ks_base_eq, w0.1]
  have hkg : gS.ks_base s2 = st.ks_base s := by rw [gst_ks_base]; exact hks
  have T1 := vsRdG_tr hV hrg hkg
  have T2 := vsRdG_tr hV hrs hks
  refine ⟨(check_vspace_tr (m' := gS) (x' := s2) (s := s) (root := root) T1.1).trans
    (check_vspace_tr (m' := st) (x' := s2) (s := s) (root := root) T2.1).symm, fun hf => ?_⟩
  exact (page_entry_slot_small_tr (m' := gS) (x' := s2) (s := s) ((T1.2 root hf))).trans
    (page_entry_slot_small_tr (m' := st) (x' := s2) (s := s) ((T2.2 root hf))).symm

end rdX

section s2X
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP} {μ : U64 → U64}
variable {A : Type} {ar : machine.Arch A}

/-- **The PageMap decode's facts at the decode state** (module docstring). -/
theorem pm_s2X (hA : P0.ArchTotal ar) {s : S} {a : A} {nx : U64} {s1 s2 : S} {a1 : A}
    (hE : PmPreGX st Cs Ω Sg Ac Locks p K μ s) (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1) :
    ∃ (fp rt asid va : U64) (mp : Bool) (x0 root rasid e : U64),
      obj.Slot.cap st p.slot s = ok (.Frame fp .Small rt false mp false asid va) ∧
      obj.Slot.cap st p.slot s2 = ok (.Frame fp .Small rt false mp false asid va) ∧
      vspace.extra p.extra 0#usize = ok (some x0) ∧ x0 ∈ K.slots ∧
      obj.Slot.cap st x0 s2 = ok (.Pml4 root true rasid) ∧
      vspace.check_vspace st s2 (.Pml4 root true rasid) = ok (.Ok (root, rasid)) ∧
      vspace.page_entry_slot st s2 root (L.mem s2 (regA (L.curW s) layout.reg.R10)) .Small = ok (.Ok e) ∧
      e ∈ K.ptes ∧ Locks s e ∧ PmRS st K Locks s e ∧ PmWS st K Locks s e ∧
      ¬ L.mem s2 (regA (L.curW s) layout.reg.R10) > fl4_abi.consts.USER_TOP ∧
      vspace.find_vspace_for_asid st s rasid = ok (.Ok root) ∧
      p.slot ∈ K.slots ∧ Locks s p.slot ∧ OutsideObjs st K.heap.tcbs Cs s p.slot := by
  obtain ⟨⟨hJ, hq, hG⟩, hEx, hRt⟩ := hE
  have Pb := hq.1.1.1
  obtain ⟨-, es1, eu, -, -, -, -⟩ := C
  have w0 := prefix_writes ar hA Pb.tp Pb.np Pb.cT es1 eu
  have hL : Slot8 K.toKLayout := fun q hq => Pb.lay.slot8 q hq
  have ag : ∀ b, SlotW K.toKLayout b → Aligned b → L.mem s2 b = L.mem s b := fun b hs hb => by
    obtain ⟨q, hq, hbq⟩ := hs
    exact Pb.slot_keep w0 hq hbq hb
  obtain ⟨-, -, -, -, -, -, hsl, -, hlkS, -⟩ := pm_core hq
  have hsl0 : Locks s p.slot := hlkS (fun e => hJ.hz (e ▸ hsl))
  have hO : OutsideObjs st K.heap.tcbs Cs s p.slot := by
    obtain ⟨x, hx, hxs⟩ := hq.2
    obtain ⟨Cw, hroot, hcl, hC⟩ := Pb.walk
    obtain ⟨q0, r0, m0, y0, hq0, hm0, hs0⟩ := lookup_slot_cn hroot hcl hx
    rw [← hxs, hs0]; exact (hC q0 r0 m0 y0 hq0 hm0).2.1
  have hq0 := hq
  obtain ⟨⟨-, ⟨t, info, ex, ht, hi, hpw⟩, harm, hlk⟩, -⟩ := hq0
  have et : t = L.curW s := by rw [cur_thread_ok] at ht; exact (ok_inj_ff ht).symm
  subst et
  rw [(harm _ info (cur_thread_ok s) hi).1] at hpw
  obtain ⟨fp, rt, asid, va, root, rasid, mp, x0, e, hcs, hx0, hx00, hcx, hpe, -, hpte, -⟩ := plan_with_mapF hpw
  have hkp := (plan_with_kp hpw).2
  rw [← hkp] at hx0
  obtain ⟨x0', hx0', hxK⟩ := pmEx_slots Pb hEx
  rw [hx0] at hx0'
  obtain rfl := ok_inj_ff hx0'
  have hf : vspace.find_vspace_for_asid st s rasid = ok (.Ok root) := hRt x0 root rasid hx0 hcx
  -- the walk at `s2` is the walk at `s`
  have hu : ¬ L.mem s (regA (L.curW s) layout.reg.R10) > fl4_abi.consts.USER_TOP := by
    intro hu
    unfold localinv.page_entry at hpe
    rw [if_pos hu] at hpe
    simp at hpe
  have hV := pm_vsRdX ⟨hJ, hq, hG⟩ rasid (L.mem s (regA (L.curW s) layout.reg.R10)) (userV_of_not_gt hu)
  have hrs : ∀ b, (VsW K.toKLayout b ∧ ¬ XD K b) → st.read s2 b = st.read s b := fun b hb => by
    rw [L.read_eq, L.read_eq, w0.2.2 b hb.1.1 (Pb.vs_notPreW hb.1)]
  have hks : st.ks_base s2 = st.ks_base s := by rw [L.ks_base_eq, L.ks_base_eq, w0.1]
  have T2 := vsRdG_tr hV hrs hks
  have hl : vspace.lookup_pt_slot st s root (L.mem s (regA (L.curW s) layout.reg.R10)) = ok (.Ok e) := by
    unfold localinv.page_entry at hpe
    rw [if_neg hu] at hpe
    unfold vspace.small_page_entry at hpe
    obtain ⟨r, hr, hpe⟩ := bind_eq_ok hpe
    cases r with
    | Ok y =>
      have : y = e := by simpa [core.result.Result.ok] using hpe
      rw [hr, this]
    | Err _ => simp [core.result.Result.ok] at hpe
  have tk : ∀ k : U64, k.val < 4096 → k.val % 8 = 0 → k.val ≠ 392 →
      L.mem s2 (core.num.U64.wrapping_add (L.curW s) k) = L.mem s (core.num.U64.wrapping_add (L.curW s) k) :=
    fun k h1 h2 h3 => w0.2.2 _ (field_aligned Pb.tA h1 h2) (preW_tcb Pb.tA Pb.np Pb.cT h1 h3)
  have r10 : L.mem s2 (regA (L.curW s) layout.reg.R10) = L.mem s (regA (L.curW s) layout.reg.R10) := by
    have e := reg_keepK (st := st) Pb.tA (r := layout.reg.R10) (by simp [layout.reg.R10])
      (by simp [layout.reg.R10]) tk
    rw [reg_ok, reg_ok] at e; exact ok_inj_ff e
  -- the leaf
  have hspe : localinv.small_page_entry st s rasid (L.mem s (regA (L.curW s) layout.reg.R10)) = ok (some e) := by
    unfold localinv.small_page_entry
    simp only [hf, bind_ok, core.result.Result.ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch]
    rw [hpe]
  have hne : e ≠ 0#u64 := fun h0 => hG.ne0 rasid _ (h0 ▸ hspe)
  obtain ⟨hpt, hvs⟩ := hG.walk.lf rasid _ e hspe
  obtain ⟨hn, hle⟩ := hpte hne
  have hlk' := hlk _ e hn hle
  refine ⟨fp, rt, asid, va, mp, x0, root, rasid, e, hcs, by rw [cap_agree hL hsl ag]; exact hcs, ?_, hxK,
    by rw [cap_agree hL hxK ag]; exact hcx, ?_, ?_, hpt, hlk', ⟨hvs.1, hvs.2.2, rpermP_pte hpt hlk'⟩,
    ⟨hvs.1, wpermP_pte hpt hlk'⟩, by rw [r10]; exact hu, hf, hsl, hsl0, hO⟩
  · unfold vspace.extra obj.Slot.is_null
    simp only [show ¬ (0#usize ≥ 3#usize) by decide, ↓reduceIte, hx0, bind_ok, decide_eq_true_eq, hx00]
  · rw [check_vspace_tr (m' := st) (x' := s2) (s := s) (root := root) T2.1]
    unfold vspace.check_vspace
    simp [hf]
  · rw [r10, page_entry_slot_small_tr (m' := st) (x' := s2) (s := s) (T2.2 root hf)]
    unfold vspace.page_entry_slot
    simp only [hl, bind_ok, ↓reduceIte]

end s2X

section accX
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP} {μ : U64 → U64}
variable {A : Type} {ar : machine.Arch A}

/-- **The PageMap decode block on any store answering as `st`** (module docstring). -/
theorem pmAccGX (hA : P0.ArchTotal ar) {s : S} {a : A} {info : msginfo.MessageInfo} {nx : U64} {s1 s2 : S} {a1 : A}
    {buf length : U64} {cap : capability.Cap} {y : (core.result.Result Unit error.Exc) × S × A}
    {R W : U64 → Prop} {gS : machine.Store S} [GRd gS st R] [GWr gS st W]
    (hE : PmPreGX st Cs Ω Sg Ac Locks p K μ s)
    (hR : ∀ b, IoRS (st := st) K.uV.ptU Locks s b → R b) (hRu : ∀ b, UserW K.toKLayout b → R b)
    (hRe : ∀ b, PmRS st K Locks s b → R b)
    (hW : IoWr st W K.heap.scBits s) (hWs : ∀ b, IoWS (st := st) K.uV.ptU Locks s b → W b)
    (hWu : ∀ b, UserW K.toKLayout b → W b) (hWe : ∀ b, PmWS st K Locks s b → W b)
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
      have hbuf0 := hJ.here.1.buf8
      have hbw : ∀ b, msg.lookup_ipc_buffer st s2 true (L.curW s) = ok b → BufW W b ∧ BufW R b := by
        intro b eb
        rw [hlb] at eb
        exact ⟨fun h0 i hi => hWu _ (hbuf0 b eb h0 i hi), fun h0 i hi => hRu _ (hbuf0 b eb h0 i hi)⟩
      rw [invRep.guard_errPm (gS := gS) er (fun e1 => PathObl.syscall.reply_error.guard (gS := gS) s2 (L.curW s) e1 hbsl hI
        (hR _ hbs.1) (hR _ hbs.2) (fun r hr => hW.reg r hr) hbw)]
      exact hz

end accX

section finX
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP} {μ : U64 → U64}
variable {A : Type} {ar : machine.Arch A}

/-- **`FinOK` after the PageMap decode block** (module docstring). -/
theorem pmFinGX (hA : P0.ArchTotal ar) {s : S} {a : A} {info : msginfo.MessageInfo} {nx : U64} {s1 s2 : S}
    {a1 : A} {buf length : U64} {cap : capability.Cap} {y : (core.result.Result Unit error.Exc) × S × A}
    {z : S × A × core.result.Result Unit error.Exc}
    {W : U64 → Prop} {gS : machine.Store S} [GRd gS st (IoRS (st := st) K.uV.ptU Locks s)] [GWr gS st W]
    (hE : PmPreGX st Cs Ω Sg Ac Locks p K μ s)
    (hW : IoWr st W K.heap.scBits s) (hsw : SWr gS st (L.curW s) sched.TS_RUNNING)
    (emi : msg.msg_info st s (L.curW s) = ok info) (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1)
    (hcap : obj.Slot.cap st p.slot s2 = ok cap)
    (hy : syscall.decode_invocation st ar s2 a1 info.label length p.slot cap true true true false buf p.extra =
      ok y)
    (hz : invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z) :
    z.2.2 = .Ok () ∧ FinOK (L := L) gS (IoRS (st := st) K.uV.ptU Locks s) W ar s z.1 z.2.1 := by
  obtain ⟨fp, rt, asid, va, mp, x0, root, rasid, e, hcs, hcs2, hx0, hxK, hcx2, hcv2, hpe2, hpt, hle, hRS, hWS, hu,
    hf, hsl, hsl0, hO⟩ := pm_s2X hA hE C
  obtain ⟨⟨hJ, hq, hG⟩, -, -⟩ := hE
  have Pb := hq.1.1.1
  have P := Pb.ptUX hG
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
  rw [(hlab info emi).1] at hy
  have tk : ∀ k : U64, k.val < 4096 → k.val % 8 = 0 → k.val ≠ 392 →
      L.mem s2 (core.num.U64.wrapping_add (L.curW s) k) = L.mem s (core.num.U64.wrapping_add (L.curW s) k) :=
    fun k h1 h2 h3 => w0.2.2 _ (field_aligned P.tA h1 h2) (preW_tcb P.tA P.np P.cT h1 h3)
  -- the st run
  have hc2 : sched.cur_thread st s2 = ok (L.curW s2) := cur_thread_ok s2
  have ha0 : msg.syscall_arg st s2 (L.curW s2) buf 0#u64 = ok (L.mem s2 (regA (L.curW s2) layout.reg.R10)) := by
    rw [sarg0_reg, reg_ok]
  have ha1 : msg.syscall_arg st s2 (L.curW s2) buf 1#u64 = ok (L.mem s2 (regA (L.curW s2) layout.reg.R8)) := by
    rw [sarg1_reg, reg_ok]
  have ha2 : msg.syscall_arg st s2 (L.curW s2) buf 2#u64 = ok (L.mem s2 (regA (L.curW s2) layout.reg.R9)) := by
    rw [sarg2_reg, reg_ok]
  have hpe2' : vspace.page_entry_slot st s2 root (L.mem s2 (regA (L.curW s2) layout.reg.R10)) .Small =
      ok (.Ok e) := by rw [hct]; exact hpe2
  have hdst : syscall.decode_invocation st ar s2 a1 fl4_abi.label.X86PageMap length p.slot
        (.Frame fp .Small rt false mp false asid va) true true true false buf p.extra =
      vspace.decode_page_map st ar s2 a1 length p.slot
        { ptr := fp, size := .Small, rights := rt, is_device := false, mapped := mp, is_ept := false, asid,
          vaddr := va } buf p.extra := by
    rw [decInv_eq_Pm]
    unfold decPmG
    simp only [hc2, bind_ok, ↓reduceIte, Bool.false_eq_true, ite_self, eq_self_iff_true, if_true]
  rw [hdst] at hy
  have hout := post_of_ok (dpm_run ar hA hc2 hx0 ha0 ha1 ha2 hcx2 hcv2 hpe2') hy
  rw [hct] at hout
  have hlb : msg.lookup_ipc_buffer st s2 true (L.curW s) = msg.lookup_ipc_buffer st s true (L.curW s) :=
    lookup_buf_keep P.tA true tk
  have hbuf2 : ∀ b, msg.lookup_ipc_buffer st s2 true (L.curW s) = ok b → b ≠ 0#u64 → ∀ i : U64, i.val < 128 →
      UserW K.uV.ptU (core.num.U64.wrapping_add b (core.num.U64.wrapping_mul i 8#u64)) := fun b eb hne i hi => by
    have h := hJ.here.1.buf8 b (by rw [← hlb]; exact eb) hne i hi
    exact ⟨h.1, Or.inl (Or.inl h.2)⟩
  -- the scheduler facts at `s2` (io_hfin)
  have ha2 : L.actionW s2 = sched.ACTION_RESUME_CURRENT := by
    rw [eq_of_spec_fd (sched.action.spec (L := L) s2)] at eac; exact ok_inj_ff eac
  have hy2 : L.mem s2 (yieldA (L.curW s)) = 0#u64 := by
    rw [eq_ok_of_spec (obj.Tcb.yield_to.spec (L := L) s2 (L.curW s))] at ey; exact ok_inj_ff ey
  have hrun : L.mem s2 (stA (L.curW s)) = sched.TS_RESTART ∨ L.mem s2 (stA (L.curW s)) = sched.TS_RUNNING := by
    rw [I.st]; exact Ent.run
  have A0 := Ent.acc
  have hK0 := SchedOK.of_sw I.F (by rw [hct]; exact Hf.sc) (by rw [hct]; exact Hf.nr)
  rw [hct] at hK0
  have hK : SchedOK (L := L) s2 (L.curW s) := hK0
  -- slot and user words miss the node, the TCB fields and the SC words
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
  -- the run
  obtain ⟨hz2, kz⟩ := pmRun ar hA hK O ha2 hrun hL hsl heU hbuf2 hout hz
  refine ⟨hz2, ?_⟩
  -- `Ω` cut to the SC words
  have hrh0 : L.mem s (rhA (L := L) s) ≠ 0#u64 → L.mem s (scA (L.mem s (rhA (L := L) s))) ∈ K.heap.scs ∧
      InSC (L.mem s (scA (L.mem s (rhA (L := L) s)))) (K.heap.scBits (L.mem s (scA (L.mem s (rhA (L := L) s)))))
        (headA (L.mem s (scA (L.mem s (rhA (L := L) s))))) := fun h0 => by
    obtain ⟨-, hc, -⟩ := bxi_rh P.bxi h0
    obtain ⟨⟨Q, Rq, hq⟩, hbd, ⟨hO, -, hX⟩, -, hS⟩ := P.bxi
    obtain ⟨hP, hz⟩ := hO.sc _ hc
    obtain ⟨h8, h128, -⟩ := sc_lo hP hz
    have hh := headA_val' hP hz
    exact ⟨hc, by omega, by omega⟩
  have F0' := I.F0.shrink P.cscS rfl hrh0
  have F2' := F0'.frame I.w
  have rh0' : RhSc st {b | b ∈ Ω ∧ ∃ c' ∈ K.heap.scs, InSC c' (K.heap.scBits c') b} s := fun h0 => by
    obtain ⟨-, hc, ha⟩ := bxi_rh P.bxi h0
    obtain ⟨hW', hΩ⟩ := bxi_scin P.bxi hc ha
    exact ⟨_, hW', fun b hb hin => ⟨hΩ b hb hin, _, hc, hin⟩⟩
  have rh2' := rh0'.frame F0' I.w
  have Q0 := QOK.of_sw F2' rh2' I.tm
  rw [hct] at Q0
  have ho' : ∀ b ∈ {b | b ∈ Ω ∧ ∃ c' ∈ K.heap.scs, InSC c' (K.heap.scBits c') b}, ¬ UserW (KSUPm K.uV.ptU) b := by
    rintro b ⟨-, c', hc', hin⟩
    exact not_usuPm (P.sc_notUser (P.hSc _ hc') hin) (P.sc_notSlot (P.hSc _ hc') hin)
  have stm : L.mem s2 (tmA (L := L) s2) ≠ 0#u64 → ¬ UserW (KSUPm K.uV.ptU) (tdA (L.mem s2 (tmA (L := L) s2))) :=
    fun h0 => by
      unfold tdA
      exact htU _ (I.tm h0) _ (by simp) (by simp)
  have srh : L.mem s2 (rhA (L := L) s2) ≠ 0#u64 → ¬ UserW (KSUPm K.uV.ptU) (scA (L.mem s2 (rhA (L := L) s2))) ∧
      ¬ UserW (KSUPm K.uV.ptU) (headA (L.mem s2 (scA (L.mem s2 (rhA (L := L) s2))))) ∧
      ¬ UserW (KSUPm K.uV.ptU) (rtA (L.mem s2 (scA (L.mem s2 (rhA (L := L) s2))))
        (L.rhead s2 (L.mem s2 (scA (L.mem s2 (rhA (L := L) s2)))))) := fun h0 => by
    refine ⟨?_, ?_⟩
    · unfold scA; exact htU _ (F2'.rh h0).1 _ (by simp) (by simp)
    obtain ⟨zr, hW', hΩ⟩ := rh2' h0
    obtain ⟨h8, hmm, hfit⟩ := hW'.bounds
    obtain ⟨h96, -, -, hhd, -, hrt⟩ := hW'.inside
    obtain ⟨e1, e2, e3⟩ := hrt _ hW'.head_lt
    exact ⟨ho' _ (hΩ _ (by unfold Aligned; omega) ⟨by omega, by omega⟩),
      ho' _ (hΩ _ (by unfold Aligned; omega) ⟨by omega, by omega⟩)⟩
  have FIN := kz.fin hK O Q0 Hf.nd I.F.td I.F.rs stm srh
  have hcur3 : L.curW z.1 = L.curW s := kz.cur hK O
  have w3 : WritesIn st s2 z.1 (fun b => IoPW st s2 b ∨ UserW (KSUPm K.uV.ptU) b) :=
    kz.1.mono fun b hb => hb.imp_left fun h => Or.inr (by rw [hct]; exact h)
  have Fz := F2'.frameU w3 hn2 (fun t ht k h1 h2 => htU t (P.hT t ht) k (by omega) h2) ho'
  refine FinOK.of_sw hA (kz.1.1.trans I.k) (kz.1.2.1.trans I.cp) FIN.1 kz.2.1 Fz ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    (by rw [hcur3]; exact hsw)
  · rw [hcur3]
    exact (kz.tcbF hK O (k := 3472#u64) (by simp) (by simp) (by simp)).trans hy2
  · rw [hcur3]; exact kz.2.2
  · rw [hcur3]; exact A0.ryl
  · rw [hcur3]; exact A0.rst
  · rw [hcur3]; exact A0.rfi
  · rw [hcur3]; exact A0.wnx
  · rw [hcur3]; exact A0.rin


end finX

section oblX
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP} {μ : U64 → U64}
variable {A : Type} {ar : machine.Arch A}

variable (st) in
/-- **The decode block (VM copy, `FinOK` at `K.uV.ptU`) of an accepted PageMap run on the guarded store, with the slot's cap and the length's
computation as hypotheses** (`InvBlkW2`'s shape at the user-word sets and `ptU K`). Gen 12's `PmBlkUW` quantified
`cap` and `length` freely, as stpost's `InvBlkW` did; it is false for a `cap` the slot does not hold (a `Large` frame
cap maps through an unlocked PD entry), so the block is asked only for the cap the accepted run reads. -/
def PmBlkUW2X (ar : machine.Arch A) (p : localinv.Plan) (K : KLayoutP) (Locks : S → U64 → Prop)
    (P : S → Prop) : Prop :=
  ∀ s (a : A) info nx s1 s2 a1 buf length cap, P s → msg.msg_info st s (L.curW s) = ok info →
    InvChk st ar s a (L.curW s) p nx s1 s2 a1 →
    (if info.length > msg.N_MSG_REGISTERS then (if buf = 0#u64 then ok msg.N_MSG_REGISTERS else ok info.length)
      else ok info.length) = ok length →
    obj.Slot.cap st p.slot s2 = ok cap →
    ∀ y, syscall.decode_invocation st ar s2 a1 info.label length p.slot cap true true true false buf p.extra = ok y →
      syscall.decode_invocation (guard st (PmRSU st K Locks s) (PmWSU st K Locks s)) ar s2 a1
          info.label length p.slot cap true true true false buf p.extra = ok y ∧
      ∀ z, invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z →
        invRep (guard st (PmRSU st K Locks s) (PmWSU st K Locks s)) (L.curW s) y.2.1 y.2.2 y.1 = ok z ∧
        z.2.2 = core.result.Result.Ok () ∧
        FinOK (L := L) (guard st (PmRSU st K Locks s) (PmWSU st K Locks s))
          (IoRS (st := st) K.uV.ptU Locks s) (PmWSU st K Locks s) ar s z.1 z.2.1


end oblX

section blkX
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP} {μ : U64 → U64}
variable {A : Type} {ar : machine.Arch A}

/-- **`blk` at `PmPreG`** (gen 13's [W] `PmBlkUW2`, proved; module docstring). -/
theorem pm_blkGX (hA : P0.ArchTotal ar) (hK : RegionOKP K) :
    PmBlkUW2X st ar p K Locks (PmPreGX st Cs Ω Sg Ac Locks p K μ) := by
  intro s a info nx s1 s2 a1 buf length cap hE emi C _ hcap y hy
  have hG := hE.1.2.2
  have P := hE.1.2.1.1.1.1.ptUX hG
  have hW : IoWr st (PmWSU st K Locks s) K.heap.scBits s :=
    (P.ioWr (Locks := Locks)).mono (fun _ hy => pmWSU_ioWSX hK hy)
  obtain ⟨hdec, hrep⟩ := pmAccGX (R := PmRSU st K Locks s) (W := PmWSU st K Locks s)
    (gS := guard st (PmRSU st K Locks s) (PmWSU st K Locks s)) hA hE (fun _ h => pmRSU_ioRSX hG h)
    (fun b hb => ⟨hb.1, Or.inl hb.2⟩) (fun b hb => ⟨hb.1, Or.inr hb⟩) hW (fun _ h => pmWSU_ioWSX hK h)
    (fun b hb => ⟨hb.1, Or.inl hb.2⟩) (fun b hb => ⟨hb.1, Or.inr hb⟩) emi C hcap hy
  refine ⟨hdec, fun z hz => ⟨hrep z hz, ?_⟩⟩
  have hsw : SWr (guard st (PmRSU st K Locks s) (PmWSU st K Locks s)) st (L.curW s) sched.TS_RUNNING :=
    SWr.of_W (pmWSU_ioWSX hK (P.stw (Locks := Locks)).2)
  haveI : GRd (guard st (PmRSU st K Locks s) (PmWSU st K Locks s)) st (IoRS (st := st) K.uV.ptU Locks s) :=
    grd_sub (fun _ hy => pmRSU_ioRSX hG hy)
  exact pmFinGX hA hE hW hsw emi C hcap hy hz

end blkX

end
end Fl4Proofs.P2.E2EP
