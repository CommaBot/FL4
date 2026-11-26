/-
# P2 (line mmuAD, gen 12): **`PmAccIns` proved**; FL4 end to end with PageMap and A/D writes without the [W]

gen 11's `serializable_fl4_localU3c` takes the [W] `PmAccInsW` (accepted runs of the restricted PageMap slot are
`InsTP (PWE K E) ADEq NotPresent (· ∈ K.user) Set.univ ∅` of `R.invBodyPmG` at their entry). Here it is proved:

* `insTP_tailG`: `invPostG`, `after_invocation`, `finish` from any done set of `G` words, each call run alike on a
  store guarded off `G` (MmuADDel's `insT_tailOk` for `InsTP`, any decode result, two guards);
* **`insTP_pmRest`**: the rest of the body after the invoked slot's cap read (`pmRest`, P2/InvPmRoC.lean) at the
  decode state of a `PmPreG ∧ QPs (KU K E)` entry: the decode (`MmuADPmD.insTP_decPm`, from `∅` to the `PWE` words;
  its guard facts from `pm_s2` and the `IoRSR (ptU K)` lemmas of `IoPre`, the ASID words by `rdTab_ku` and
  `find_vspace_for_asid.trV`), then the tail (`insTP_tailG`: the reply on `guard st (IoRSR ∨ UserW) (IoWS ∨ UserW)`
  as `pmAccG` does it, `finish` on `guard st IoRSR IoWS` with `MmuADPmR.pmFinR`'s `FinOK`);
* **`pmAccIns`**: `PmAccIns` (`MmuADPmT.insTP_entPm` at the layout `ptU K` with `insTP_pmRest` for its rest);
* **`serializable_fl4_localU3d`**: `serializable_fl4_localU3c` without `hW` — premises exactly U1P's (`P`, [P] `hIoa`,
  `B : PmObl7` = [P] `cs` / [P] `lk`, `h0`, `hA0`, `hB`, `hc0`, `hM0`, the execution, `hq`) and [P] `MmuAD` (in
  `ExecU3b`'s `mmu` step).

No new named premise. New module; no existing statement changes.
-/
import Fl4Proofs.P2.MmuADPmD
import Fl4Proofs.P2.MmuADPmR
import Fl4Proofs.P2.E2EPU3i
import Fl4Proofs.P2.InvPmRoC
import Fl4Proofs.P2.MmuADDelP
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField NullOrFrame TcbSlot)
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.E2E (InsT InsTP insTP_sbind SP)
open Fl4Proofs.P2.MmuAD (MmuAD ADEq NotPresent)
open Fl4Proofs.P2.Serial (Cfg Init ArmInv NoLoc RunAll)

noncomputable section

section tail
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type} {ar : machine.Arch A}

theorem invPostG_invRep (m : machine.Store S) (x : S) (a : A) (t : U64) (r : core.result.Result Unit error.Exc) :
    invPostG m x a t r = invRep m t x a r := by
  unfold invPostG invRep; cases r <;> rfl

/-- **The tail after the decode from any done set of `G` words** (module docstring). -/
theorem insTP_tailG {G User R0 W0 R1 W1 : U64 → Prop} (hGU : ∀ x, G x → ¬ User x) {D : Set U64}
    (hDG : ∀ x ∈ D, G x) (hR0 : ∀ q, R0 q → ¬ G q) (hW0 : ∀ q, W0 q → ¬ G q) (hR1 : ∀ q, R1 q → ¬ G q)
    (hW1 : ∀ q, W1 q → ¬ G q) {t : U64} {r : core.result.Result Unit error.Exc} {x : S} {a : A}
    {r' : Bool × S × A}
    (h : interp st ar ((R.invPostG t r).sbind fun r1 =>
      (R.syscall.after_invocation r1).sbind fun _ => R.syscall.finish.sbind fun _ => SProg.ret true) x a = ok r')
    (hI : ∀ z, invPostG st x a t r = ok z →
      invPostG (guard st R0 W0) x a t r = ok z ∧ z.2.2 = .Ok () ∧
      ∀ y, syscall.finish st ar z.1 z.2.1 = ok y → syscall.finish (guard st R1 W1) ar z.1 z.2.1 = ok y) :
    InsTP st ar G ADEq NotPresent User Set.univ D ((R.invPostG t r).sbind fun r1 =>
      (R.syscall.after_invocation r1).sbind fun _ => R.syscall.finish.sbind fun _ => SProg.ret true) x a := by
  refine insTP_gstep hGU hDG hR0 hW0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
  · rw [R.invPostG_eq] at h1 ⊢
    obtain ⟨z, ez, rfl⟩ := bind_shape h1
    rw [(hI z ez).1]
    exact bok.mpr ⟨_, rfl, rfl⟩
  rw [R.invPostG_eq] at h1
  obtain ⟨z, ez, rfl⟩ := bind_shape h1
  dsimp only at hk ⊢
  rw [(hI z ez).2.1] at hk ⊢
  refine insTP_gstep hGU hDG hR0 hW0 hk (fun r h1 => ?_) (fun r h1 hk2 => ?_)
  · rw [R.syscall.after_invocation_eq] at h1 ⊢
    rw [syscall.after_invocation.ok_eq] at h1 ⊢
    exact h1
  rw [R.syscall.after_invocation_eq, syscall.after_invocation.ok_eq] at h1
  obtain ⟨y, ey, rfl⟩ := bind_shape h1
  cases ok_inj_ff ey
  dsimp only at hk2 ⊢
  refine insTP_gstep hGU hDG hR1 hW1 hk2 (fun r h1 => ?_) (fun r _ _ => ?_)
  · rw [R.syscall.finish_eq] at h1 ⊢
    obtain ⟨y, ey, rfl⟩ := bind_shape h1
    rw [(hI z ez).2.2 y ey]
    exact bok.mpr ⟨_, rfl, rfl⟩
  simp only [InsTP]; exact Set.subset_univ _

end tail

section rest
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayoutP} {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}
variable {A : Type} {ar : machine.Arch A}

set_option maxHeartbeats 8000000 in
/-- **The rest of an accepted PageMap run is `InsTP` at the epoch's paging words** (module docstring). -/
theorem insTP_pmRest (hA : P0.ArchTotal ar) {E : U64 → U64} (hK : RegionOKP K) (hU : UserOKP K)
    {p : localinv.Plan} {μ : U64 → U64} {s s1 s2 : S} {a a1 : A} {info : msginfo.MessageInfo}
    {nx buf length : U64} {cap : capability.Cap} {r' : Bool × S × A}
    (hE : PmPreG st Cs Ω Sg Ac Locks p K μ s) (hqE : QPs (KU K E) st s)
    (emi : msg.msg_info st s (L.curW s) = ok info) (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1)
    (ecap : obj.Slot.cap st p.slot s2 = ok cap)
    (hR : interp st ar (pmRest (L.curW s) info p buf length cap) s2 a1 = ok r') :
    InsTP st ar (PWE K E) ADEq NotPresent (· ∈ K.user) Set.univ ∅ (pmRest (L.curW s) info p buf length cap) s2 a1 := by
  have hE0 := hE
  have hG := hE.1.2.2
  have hq := hE.1.2.1
  have hJ := hE.1.1
  have Pb := hq.1.1.1
  have P := Pb.ptU hG
  have hks := ksNoE_conv hG.choose_spec.1.2
  have nR : ∀ q, IoRSR st K.ptU Locks s q → ¬ PWE K E q := fun q h => ioRSR_ptU_notPWE hK hks h
  have nW : ∀ q, IoWS (st := st) K.ptU Locks s q → ¬ PWE K E q := fun q h => ioWS_notPWE hK h
  have hGU : ∀ x, PWE K E x → ¬ (x ∈ K.user) := fun x hx => pwe_user hU hx
  have nU : ∀ q, UserW K.toKLayout q → ¬ PWE K E q := fun q h hp => pwe_user hU hp h.2
  obtain ⟨fp, rt, asid, va, mp, x0, root, rasid, e, hcs, hcs2, hx0, hxK, hcx2, hcv2, hpe2, hpt, hle, hRS, hWS, hu,
    hf, hsl, hsl0, hO⟩ := pm_s2 hA hE C
  have hcap' : cap = .Frame fp .Small rt false mp false asid va := by
    rw [hcs2] at ecap; exact (ok_inj_ff ecap).symm
  subst hcap'
  obtain ⟨-, -, -, -, -, -, -, hlab, -, -⟩ := pm_core hq
  have hlbl := (hlab info emi).1
  have C0 := C
  obtain ⟨-, es1, eu, eac, ey, ehere, -⟩ := C
  have Ent := P.entR (Locks := Locks) (P.ioWr (Locks := Locks))
  have Hf := here_facts ehere
  have I := IoS2.of_ent hA Ent es1 eu Hf.sc
  have hct : L.curW s2 = L.curW s := I.cur
  have hL0 : Slot8 K.toKLayout := fun q hq => Pb.lay.slot8 q hq
  have hL : Slot8 K.ptU := fun q hq => P.lay.slot8 q hq
  have w0 := prefix_writes ar hA Pb.tp Pb.np Pb.cT es1 eu
  have ag : ∀ b, SlotW K.toKLayout b → Aligned b → L.mem s2 b = L.mem s b := fun b hs hb => by
    obtain ⟨q, hq, hbq⟩ := hs
    exact Pb.slot_keep w0 hq hbq hb
  have hcxs : obj.Slot.cap st x0 s = ok (.Pml4 root true rasid) := (cap_agree hL0 hxK ag).symm.trans hcx2
  have hnd2 : ∀ o, L.nodeAt s2 (L.cpu s2) o = L.nodeAt s (L.cpu s) o := fun o => by
    rw [I.cp, nodeAt_of_ksb I.k]
  -- the decode's guard facts (on `guard st (¬ PWE) (¬ PWE)`)
  have hct' : ¬ PWE K E (L.nodeAt s2 (L.cpu s2) layout.node.CUR_THREAD) := by
    rw [hnd2]
    exact nR _ (P.ndR (Locks := Locks) layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD])
      (by simp [layout.node.CUR_THREAD])).1
  have hreg : ∀ r : U64, r.val < 384 → ¬ PWE K E (regA (L.curW s2) r) := fun r hr => by
    rw [hct]; exact nR _ (P.regR (Locks := Locks) hr).1
  have hx0R := P.slotR (Locks := Locks) (sl := x0) hxK (Or.inr (cap_pml4_nof hcxs))
  have hFt : ¬ PWE K E (core.num.U64.wrapping_add (L.ksb s2) layout.ks.FEATURES) := by
    rw [I.k]; exact nR _ (P.kswR (Locks := Locks) (by simp [layout.ks.FEATURES]) (by simp [layout.ks.FEATURES]))
  -- `check_vspace`: the ASID words, off `PWE` under `QPs (KU K E)`, unwritten by the prefix
  have hcv : vspace.check_vspace (guard st (fun b => ¬ PWE K E b) (fun b => ¬ PWE K E b)) s2
      (.Pml4 root true rasid) = vspace.check_vspace st s2 (.Pml4 root true rasid) := by
    obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := id hJ
    have hTab := rdTab_ku (E := E) B.rdTab hqE
    have hV : ∀ q, (VsW K.toKLayout q ∧ q ∉ (KU K E).ptes) → VsW K.toKLayout q ∧ q ∉ K.ptes :=
      fun q h => ⟨h.1, fun hp => h.2 ⟨Or.inl hp, h.1.1⟩⟩
    have hrs : ∀ b, (VsW K.toKLayout b ∧ ¬ b ∈ K.ptes) → st.read s2 b = st.read s b := fun b hb => by
      rw [L.read_eq, L.read_eq, w0.2.2 b hb.1.1 (Pb.vs_notPreW hb.1)]
    have hks2 : st.ks_base s2 = st.ks_base s := by rw [L.ks_base_eq, L.ks_base_eq, w0.1]
    have hf0 := vspace.find_vspace_for_asid.guard
      (gS := guard st (fun q => VsW K.toKLayout q ∧ q ∉ (KU K E).ptes) (fun _ => False)) s rasid hTab
    obtain ⟨fr, efr, -⟩ := spec_ex_fd (P0.vspace.find_vspace_for_asid.p0 st s rasid L.total)
    have e1 : vspace.find_vspace_for_asid (guard st (fun b => ¬ PWE K E b) (fun b => ¬ PWE K E b)) s2 rasid =
        ok fr :=
      vspace.find_vspace_for_asid.trV (W := fun _ => False)
        (fun b hb => (guard_read (rf_notPWE hb)).trans (hrs b (hV b hb))) hks2 (hf0.trans efr)
    have e2 : vspace.find_vspace_for_asid st s2 rasid = ok fr :=
      vspace.find_vspace_for_asid.trV (W := fun _ => False) (fun b hb => hrs b (hV b hb)) hks2 (hf0.trans efr)
    exact check_vspace_tr (s := s2) (e1.trans e2.symm)
  -- `set_thread_state`
  have rst := P.stwR (Locks := Locks)
  have rsc : IoRSR st K.ptU Locks s (scA (L.curW s)) :=
    P.gateR (off := 3464#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField])
  have riq : IoRSR st K.ptU Locks s (inqA (L.curW s)) :=
    (P.homeR (Locks := Locks) (off := 3592#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField])).1
  have hmxR : IoRSR st K.ptU Locks s (maxA (L.cscW s)) := by
    have hmx := maxA_facts P.bxi.2.2.1.1 P.cscS
    exact (P.cscaccR (Locks := Locks)).rd _ hmx.1 ⟨hmx.2.1, hmx.2.2⟩
  have hsc2 : L.mem s2 (scA (L.curW s)) = L.cscW s := by rw [← hct]; exact I.F.i
  have ha2 : L.actionW s2 = sched.ACTION_RESUME_CURRENT := by
    rw [eq_of_spec_fd (sched.action.spec (L := L) s2)] at eac; exact ok_inj_ff eac
  have hrun : L.mem s2 (stA (L.curW s)) = sched.TS_RESTART ∨ L.mem s2 (stA (L.curW s)) = sched.TS_RUNNING := by
    rw [I.st]; exact Ent.run
  have hKs0 := SchedOK.of_sw I.F (by rw [hct]; exact Hf.sc) (by rw [hct]; exact Hf.nr)
  rw [hct] at hKs0
  have hKs : SchedOK (L := L) s2 (L.curW s) := hKs0
  have hmx2 : IoRSR st K.ptU Locks s
      (maxA (L.mem (L.wr s2 (stA (L.curW s)) sched.TS_RESTART) (scA (L.curW s)))) := by
    have kw := (KeepA.refl ha2 hrun).wr hKs (b := stA (L.curW s)) (v := sched.TS_RESTART) (Or.inr rfl)
      (fun _ => Or.inl rfl)
    have e : L.mem (L.wr s2 (stA (L.curW s)) sched.TS_RESTART) (scA (L.curW s)) = L.mem s2 (scA (L.curW s)) :=
      kw.mem (field_aligned P.tA (by simp) (by simp)) (iotw_field P.tA (by simp) (by simp))
    rw [e, hsc2]
    exact hmxR
  have n0 := P.ndR (Locks := Locks) layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD])
    (by simp [layout.node.CUR_THREAD])
  have n1 := P.ndR (Locks := Locks) layout.node.SCHED_ACTION (by simp [layout.node.SCHED_ACTION])
    (by simp [layout.node.SCHED_ACTION])
  have hN0 : NodeSt (L := L) (fun b => ¬ PWE K E b) (fun b => ¬ PWE K E b) s2 := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hnd2]; exact nR _ n0.1
    · rw [hnd2]; exact nR _ n1.1
    · rw [hnd2]; exact nW _ n1.2
  have hsts : sched.set_thread_state (guard st (fun b => ¬ PWE K E b) (fun b => ¬ PWE K E b)) s2 (L.curW s2)
      sched.TS_RESTART = sched.set_thread_state st s2 (L.curW s2) sched.TS_RESTART := by
    rw [hct]
    exact sched.set_thread_state.guard (gS := guard st (fun b => ¬ PWE K E b) (fun b => ¬ PWE K E b)) s2
      (L.curW s) _ hN0 (nW _ rst.2) (nR _ rst.1) (nR _ rsc) (nR _ hmx2) (nR _ riq)
  -- the invoked slot's words
  have hnT : ¬ TcbSlot K.ptU p.slot := notTcbSlot_of hO
  have hnf := nof_of_frame_slot hcs
  have hs0 : ¬ PWE K E p.slot := by
    have := nW _ ((P.lockSlot (Locks := Locks) (o := 0#u64) hsl hsl0 (by simp) (by simp)).2 (Or.inr ⟨hnT, hnf⟩))
    rwa [wadd_zero (hL _ hsl).2] at this
  have hs8 : ¬ PWE K E (core.num.U64.wrapping_add p.slot 8#u64) :=
    nW _ ((P.lockSlot (Locks := Locks) (o := 8#u64) hsl hsl0 (by simp) (by simp)).2 (Or.inr ⟨hnT, hnf⟩))
  -- the decode
  have hR' := hR
  unfold pmRest at hR' hR ⊢
  rw [interp_sbind] at hR'
  obtain ⟨y0, hy0, -⟩ := bind_eq_ok' hR'
  refine insTP_sbindR hR (insTP_decPm hGU hlbl hct' hx0 hreg (nR _ hx0R.1) (nR _ hx0R.2) hcx2 hcv hFt hsts
    hs0 hs8 hy0) (fun y hy hk => ?_)
  -- the tail
  have hdI : interp st ar (R.decPmG info.label length p.slot
      (.Frame fp .Small rt false mp false asid va) true true true false buf p.extra) s2 a1 =
      (syscall.decode_invocation st ar s2 a1 info.label length p.slot (.Frame fp .Small rt false mp false asid va)
        true true true false buf p.extra >>= fun r => ok (r.1, r.2.1, r.2.2)) := by
    rw [R.decPmG_eq, hlbl, decInv_eq_Pm]
  rw [hdI] at hy
  obtain ⟨y, hyD, rfl⟩ := bind_shape hy
  dsimp only at hk ⊢
  -- the reply's guard: `IoRSR ∨ UserW` / `IoWS ∨ UserW`
  let R0 : U64 → Prop := fun b => IoRSR st K.ptU Locks s b ∨ UserW K.toKLayout b
  let W0 : U64 → Prop := fun b => IoWS (st := st) K.ptU Locks s b ∨ UserW K.toKLayout b
  have hR0 : ∀ q, R0 q → ¬ PWE K E q := fun q h => h.elim (nR q) (nU q)
  have hW0 : ∀ q, W0 q → ¬ PWE K E q := fun q h => h.elim (nW q) (nU q)
  have hWio : IoWr st W0 K.heap.scBits s := (P.ioWr (Locks := Locks)).mono (fun b hb => Or.inl hb)
  refine insTP_tailG (R0 := R0) (W0 := W0) (R1 := IoRSR st K.ptU Locks s)
    (W1 := IoWS (st := st) K.ptU Locks s) hGU (fun _ h => h) hR0 hW0 nR nW hk (fun z hz => ?_)
  rw [invPostG_invRep] at hz ⊢
  obtain ⟨hz2, F⟩ := pmFinR (gS := guard st (IoRSR st K.ptU Locks s) (IoWS (st := st) K.ptU Locks s))
    (W := IoWS (st := st) K.ptU Locks s) hA hE0 (P.ioWr (Locks := Locks)) (SWr.of_W rst.2) emi C0 ecap hyD hz
  refine ⟨?_, hz2, fun w hw => ?_⟩
  swap
  · rw [syscall.finish.guard_resume ar z.1 z.2.1 (nd_at (fun o h1 h2 => P.ndR (Locks := Locks) o h1 h2) F.k F.c)
      F.nd F.td F.rs F.ha F.hsw F.hfr F.hact F.hvc]
    exact hw
  -- the reply runs alike (`pmAccG`'s second part)
  have hc2 : sched.cur_thread st s2 = ok (L.curW s2) := cur_thread_ok s2
  have hg0 : msg.syscall_arg st s2 (L.curW s2) buf 0#u64 = ok (L.mem s2 (regA (L.curW s2) layout.reg.R10)) := by
    rw [sarg0_reg, reg_ok]
  have hg1 : msg.syscall_arg st s2 (L.curW s2) buf 1#u64 = ok (L.mem s2 (regA (L.curW s2) layout.reg.R8)) := by
    rw [sarg1_reg, reg_ok]
  have hg2 : msg.syscall_arg st s2 (L.curW s2) buf 2#u64 = ok (L.mem s2 (regA (L.curW s2) layout.reg.R9)) := by
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
    simp only [hc2, bind_ok, ↓reduceIte, Bool.false_eq_true, ite_self]
  have hyD' := hyD
  rw [hlbl, hdst] at hyD'
  have hout := post_of_ok (dpm_run ar hA hc2 hx0 hg0 hg1 hg2 hcx2 hcv2 hpe2') hyD'
  rw [hct] at hout
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
  have hN : ∀ x : S, (∀ o, L.nodeAt x (L.cpu x) o = L.nodeAt s (L.cpu s) o) → NodeSt (L := L) R0 W0 x := by
    intro x hn
    refine ⟨?_, ?_, ?_⟩
    · rw [hn]; exact Or.inl n0.1
    · rw [hn]; exact Or.inl n1.1
    · rw [hn]; exact Or.inl n1.2
  obtain ⟨r, x, a2⟩ := y
  cases r with
  | Ok u =>
    cases u
    have kx := pmDecKeep ar hA hKs O ha2 hrun hL hsl heU hout rfl
    simp only at kx hz ⊢
    have Fx := kx.sched hKs O
    refine invRep.guard_ok (gS := guard st R0 W0) (Or.inl rst.1) (Or.inl rst.2) (Or.inl rsc) (Or.inl riq)
      (hWio.reg _ rB384) (hWio.reg _ rM384) ?_ hz
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
      k6.tcbF hKs O (k := 3464#u64) (by simp) (by simp) (by simp)
    rw [e6, hsc2]; exact Or.inl hmxR
  | Err er =>
    have hx : x = s2 := by
      rcases hout with ⟨hx, -⟩ | ⟨h, -⟩
      · exact hx
      · cases h
    simp only at hz ⊢
    rw [hx] at hz ⊢
    obtain ⟨bsl, hbsl⟩ := buffer_slot_ok (L.curW s)
    obtain ⟨hb1, hb2⟩ := P.lay.tslot _ (P.hT _ P.cT) _ bsl hbsl (by simp [layout.tcb.SLOT_BUFFER])
    have hbs := P.slotR (Locks := Locks) hb1 (Or.inl hb2)
    have hI : R0 (core.num.U64.wrapping_add (L.curW s) 3512#u64) :=
      Or.inl (P.gateR (off := 3512#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField]))
    have tk : ∀ k : U64, k.val < 4096 → k.val % 8 = 0 → k.val ≠ 392 →
        L.mem s2 (core.num.U64.wrapping_add (L.curW s) k) = L.mem s (core.num.U64.wrapping_add (L.curW s) k) :=
      fun k h1 h2 h3 => w0.2.2 _ (field_aligned P.tA h1 h2) (preW_tcb P.tA P.np P.cT h1 h3)
    have hlb : msg.lookup_ipc_buffer st s2 true (L.curW s) = msg.lookup_ipc_buffer st s true (L.curW s) :=
      lookup_buf_keep P.tA true tk
    have hbuf0 := invBufJ8_of hJ
    have hbw : ∀ b, msg.lookup_ipc_buffer st s2 true (L.curW s) = ok b → BufW W0 b ∧ BufW R0 b := by
      intro b eb
      rw [hlb] at eb
      exact ⟨fun h0 i hi => Or.inr (hbuf0 b eb h0 i hi), fun h0 i hi => Or.inr (hbuf0 b eb h0 i hi)⟩
    rw [invRep.guard_errPm (gS := guard st R0 W0) er (fun e1 => PathObl.syscall.reply_error.guard
      (gS := guard st R0 W0) s2 (L.curW s) e1 hbsl hI (Or.inl hbs.1) (Or.inl hbs.2) (fun r hr => hWio.reg r hr)
      hbw)]
    exact hz

end rest

section slot
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)

set_option maxHeartbeats 4000000 in
/-- **`PmAccIns` holds** (module docstring). -/
theorem pmAccIns {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl7 st Cs Ω Sg Ac Locks) :
    PmAccIns st ar hA hm B := by
  intro j K E m hK hU _P s a r hs hr hacc
  obtain ⟨hE0, hqE0⟩ := hs
  have hE : PmPreG st Cs Ω Sg Ac Locks j.2 K m s := hE0
  have hqE : QPs (KU K E) st s := hqE0
  have hr0 : syscall.handle_invocation_local st ar s a j.1 j.2 = ok r := hr
  have h0 : syscall.handle_invocation_local st ar s a j.1 j.2 = ok (true, r.2.1, r.2.2) := by
    obtain ⟨b, s1, a1⟩ := r
    have hb : b = true := hacc
    subst hb
    exact hr0
  have hp := pm_isProgOn (st := st) (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (Locks := Locks) (p := j.2) (K := K)
    (μ := m) hA j.1
  have hr' : interp st ar (R.invBodyPmG j.1 j.2) s a = ok (true, r.2.1, r.2.2) := by
    rw [← inv_hp hp (Narrow.self st) (AltOf.pre hE.1) a]; exact h0
  show InsTP st ar (PWE K E) ADEq NotPresent (· ∈ K.user) Set.univ ∅ (R.invBodyPmG j.1 j.2) s a
  refine insTP_entPm hA (K := K.ptU) (Locks := Locks)
    (P := fun s => PmPreG st Cs Ω Sg Ac Locks j.2 K m s ∧ QPs (KU K E) st s)
    (fun x hx => pwe_user hU hx) (fun s h => h.1.1.2.1.1.1.1.ptU h.1.1.2.2)
    (fun s h q hq => hq.elim (fun h' => ioRSR_ptU_notPWE hK (ksNoE_conv h.1.1.2.2.choose_spec.1.2) h')
      (fun h' => ioWS_notPWE hK h'))
    (fun s h => pm_seenR h.1.1.1 h.1.1.2.1 (h.1.1.2.1.1.1.1.ptU h.1.1.2.2)) (fun s h => ?_)
    (fun s a info nx s1 s2 a1 buf length cap r' h _ emi C _ ecap _ hR =>
      insTP_pmRest hA hK hU h.1 h.2 emi C ecap hR) s a _ ⟨hE, hqE⟩ ⟨_, _, h0⟩ hr'
  have Pu := h.1.1.2.1.1.1.1.ptU h.1.1.2.2
  obtain ⟨-, -, -, -, -, -, hsl, -, hlk, -⟩ := pm_core h.1.1.2.1
  have h0' : j.2.slot ≠ 0#u64 := fun e => slJAt_slot0 h.1.1.1 (e ▸ hsl)
  obtain ⟨-, hf⟩ := Pu.lay.slot8 _ hsl
  refine ⟨?_, Pu.lockSlotR hsl (hlk h0') (o := 8#u64) (by simp) (by simp)⟩
  have := Pu.lockSlotR (Locks := Locks) hsl (hlk h0') (o := 0#u64) (by simp) (by simp)
  rwa [wadd_zero hf] at this

end slot

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **FL4 end to end with the PageMap slot and A/D writes to every paging word of the epoch, without the [W]**
(module docstring): premises exactly U1P's (`P`, [P] `hIoa`, `B` = [P] `cs` / [P] `lk`, `h0`, `hA0`, `hB`, `hc0`,
`hM0`, the execution, `hq`) and [P] `MmuAD` (in `ExecU3b`'s `mmu` step). -/
theorem serializable_fl4_localU3d (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl7 st Cs Ω Sg Ac Locks)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} {E : U64 → U64} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecU3b (famU1P st ar hA a0 B) (StartU1P st ar hA a0 B (arI := arI) (AR := AR) (MR := MR)) P s0 K0 Ch0
      s K Ch E)
    (hq : NoLoc s) :
    ∃ ℓ : List SP, ℓ.Perm s.log ∧ RunAll ℓ s0.mem s.mem :=
  serializable_fl4_localU3c_ofAcc st ar hA a0 P hIoa B (pmAccIns st ar hA (masksWr_plain st) B) h0 hA0 hB hc0 hM0
    h hq

end top

end
end Fl4Proofs.P2.E2EP
