/-
# P2 (line mmuAD, gen 17): **PageMap in VM epochs, part E** — the A/D walk at the VM layout

Gen 11–12's PageMap walk (`pm_decR`, `insAP_pmR`, `pmFinR`, `insTP_pmRest`, `pmAccIns`) at the VM entry `PmPreGX`
(E2EPAD2A–D), restricted by gen 15's **`TabKU`** in place of `QPs (KU K E)`:
* the read set `IoRSR K.uV.ptU` is inside `IoRSR K.ptU` (**`ioRSR_uV`**), so gen 10's `ioRSR_ptU_notPWE` keeps
  it off the epoch's paging words (`KsNoE` from `PmGX.ks`, not from the native epoch convention);
* `check_vspace`'s ASID words: `rdTab_kuT` of `TabKU` (natively `rdTab_ku` of the bundle's `RdTab` and `QPs`);
* **`pmRV`** (VM PageMap path restricted to `TabKU`), **`PmAccInsX`** / **`pmAccInsX`** (its accepted runs are
  `InsTP` at `PWE K E` from nothing done), **`pm_decRV`** (its declined runs touch no paging word),
  **`insAP_pmX`**: `InsAP (PWE K E) …` of a VM-epoch PageMap start (`tabKU_start` from `EpochJV` and [S] `VmPweT`).

No named premise. New module; no existing statement changes.
-/
import Fl4Proofs.P2.E2EPAD2D
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField NullOrFrame TcbSlot)
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.E2E (InsT InsTP insTP_sbind SP StartAt LocalPath)
open Fl4Proofs.P2.MmuAD (MmuAD ADEq NotPresent adEq_equiv)
open Fl4Proofs.P2.Serial (Cfg Init ArmInv NoLoc RunAll InsA InsAP)

noncomputable section
open Classical

section io
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayoutP} {Locks : S → U64 → Prop} {s : S} {x : U64}

theorem ioRSR_uV (h : IoRSR st K.uV.ptU Locks s x) : IoRSR st K.ptU Locks s x :=
  ⟨⟨h.1.1, fun hu => h.1.2.1 (hu.elim (fun a => Or.inl (Or.inl a)) Or.inr), h.1.2.2⟩, h.2⟩

theorem ioWS_uV (h : IoWS (st := st) K.uV.ptU Locks s x) : IoWS (st := st) K.ptU Locks s x := ⟨h.1, h.2⟩

variable {Cs Ω Sg Ac : Set U64} {p : localinv.Plan} {μ : U64 → U64} {F : S → Prop}
variable {T Rp Scs Nt : Set U64} {H : Heap} {Z : U64 → Nat}

/-- The plan's seen words are `IoRSR` words at `K.uV.ptU` (`pm_seenR` with `InvLX.hz`). -/
theorem pm_seenRX (hJ : InvLX st F K.toKLayout s) (hq : PmQF st Cs Ω Sg Ac Locks p K μ s)
    (P : IoPre st K.uV.ptU T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    ∀ x, SeenW p x → IoRSR st K.uV.ptU Locks s x := by
  intro x hx
  obtain ⟨-, -, -, -, -, -, hsl, -, hlk, hSn⟩ := pm_core hq
  have h0 : p.slot ≠ 0#u64 := fun e => hJ.hz (e ▸ hsl)
  rcases hSn x hx with rfl | rfl
  · exact P.lockSlotR hsl (hlk h0) (by simp [layout.cte.CAP0]) (by simp [layout.cte.CAP0])
  · exact P.lockSlotR hsl (hlk h0) (by simp [layout.cte.CAP1]) (by simp [layout.cte.CAP1])

end io

section finR
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP} {μ : U64 → U64}
variable {A : Type} {ar : machine.Arch A}

/-- **`FinOK` after the PageMap decode block at `IoRSR`** (module docstring). -/
theorem pmFinRX (hA : P0.ArchTotal ar) {s : S} {a : A} {info : msginfo.MessageInfo} {nx : U64} {s1 s2 : S}
    {a1 : A} {buf length : U64} {cap : capability.Cap} {y : (core.result.Result Unit error.Exc) × S × A}
    {z : S × A × core.result.Result Unit error.Exc}
    {W : U64 → Prop} {gS : machine.Store S} [GRd gS st (IoRSR st K.uV.ptU Locks s)] [GWr gS st W]
    (hE : PmPreGX st Cs Ω Sg Ac Locks p K μ s)
    (hW : IoWr st W K.heap.scBits s) (hsw : SWr gS st (L.curW s) sched.TS_RUNNING)
    (emi : msg.msg_info st s (L.curW s) = ok info) (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1)
    (hcap : obj.Slot.cap st p.slot s2 = ok cap)
    (hy : syscall.decode_invocation st ar s2 a1 info.label length p.slot cap true true true false buf p.extra =
      ok y)
    (hz : invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z) :
    z.2.2 = .Ok () ∧ FinOK (L := L) gS (IoRSR st K.uV.ptU Locks s) W ar s z.1 z.2.1 := by
  obtain ⟨fp, rt, asid, va, mp, x0, root, rasid, e, hcs, hcs2, hx0, hxK, hcx2, hcv2, hpe2, hpt, hle, hRS, hWS, hu,
    hf, hsl, hsl0, hO⟩ := pm_s2X hA hE C
  obtain ⟨⟨hJ, hq, hG⟩, -, -⟩ := hE
  have Pb := hq.1.1.1
  have P := Pb.ptUX hG
  obtain ⟨-, es1, eu, eac, ey, ehere, -⟩ := C
  have Ent := P.entR (Locks := Locks) hW
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


end finR

section restR
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayoutP} {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}
variable {A : Type} {ar : machine.Arch A}

set_option maxHeartbeats 8000000 in
/-- **The rest of an accepted PageMap run is `InsTP` at the epoch's paging words** (module docstring). -/
theorem insTP_pmRestX (hA : P0.ArchTotal ar) {E : U64 → U64} (hK : RegionOKP K) (hU : UserOKP K)
    {p : localinv.Plan} {μ : U64 → U64} {s s1 s2 : S} {a a1 : A} {info : msginfo.MessageInfo}
    {nx buf length : U64} {cap : capability.Cap} {r' : Bool × S × A}
    (hE : PmPreGX st Cs Ω Sg Ac Locks p K μ s) (hqE : TabKU (L := L) K E s)
    (emi : msg.msg_info st s (L.curW s) = ok info) (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1)
    (ecap : obj.Slot.cap st p.slot s2 = ok cap)
    (hR : interp st ar (pmRest (L.curW s) info p buf length cap) s2 a1 = ok r') :
    InsTP st ar (PWE K E) ADEq NotPresent (· ∈ K.user) Set.univ ∅ (pmRest (L.curW s) info p buf length cap) s2 a1 := by
  have hE0 := hE
  have hG := hE.1.2.2
  have hq := hE.1.2.1
  have hJ := hE.1.1
  have Pb := hq.1.1.1
  have P := Pb.ptUX hG
  have hks := hG.ks
  have nR : ∀ q, IoRSR st K.uV.ptU Locks s q → ¬ PWE K E q := fun q h => ioRSR_ptU_notPWE hK hks (ioRSR_uV h)
  have nW : ∀ q, IoWS (st := st) K.uV.ptU Locks s q → ¬ PWE K E q := fun q h => ioWS_notPWE hK (ioWS_uV h)
  have hGU : ∀ x, PWE K E x → ¬ (x ∈ K.user) := fun x hx => pwe_user hU hx
  have nU : ∀ q, UserW K.toKLayout q → ¬ PWE K E q := fun q h hp => pwe_user hU hp h.2
  obtain ⟨fp, rt, asid, va, mp, x0, root, rasid, e, hcs, hcs2, hx0, hxK, hcx2, hcv2, hpe2, hpt, hle, hRS, hWS, hu,
    hf, hsl, hsl0, hO⟩ := pm_s2X hA hE C
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
  have hL : Slot8 K.uV.ptU := fun q hq => P.lay.slot8 q hq
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
    have hTab := rdTab_kuT hqE
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
  have rsc : IoRSR st K.uV.ptU Locks s (scA (L.curW s)) :=
    P.gateR (off := 3464#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField])
  have riq : IoRSR st K.uV.ptU Locks s (inqA (L.curW s)) :=
    (P.homeR (Locks := Locks) (off := 3592#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField])).1
  have hmxR : IoRSR st K.uV.ptU Locks s (maxA (L.cscW s)) := by
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
  have hmx2 : IoRSR st K.uV.ptU Locks s
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
  have hnT : ¬ TcbSlot K.uV.ptU p.slot := notTcbSlot_of hO
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
  let R0 : U64 → Prop := fun b => IoRSR st K.uV.ptU Locks s b ∨ UserW K.toKLayout b
  let W0 : U64 → Prop := fun b => IoWS (st := st) K.uV.ptU Locks s b ∨ UserW K.toKLayout b
  have hR0 : ∀ q, R0 q → ¬ PWE K E q := fun q h => h.elim (nR q) (nU q)
  have hW0 : ∀ q, W0 q → ¬ PWE K E q := fun q h => h.elim (nW q) (nU q)
  have hWio : IoWr st W0 K.heap.scBits s := (P.ioWr (Locks := Locks)).mono (fun b hb => Or.inl hb)
  refine insTP_tailG (R0 := R0) (W0 := W0) (R1 := IoRSR st K.uV.ptU Locks s)
    (W1 := IoWS (st := st) K.uV.ptU Locks s) hGU (fun _ h => h) hR0 hW0 nR nW hk (fun z hz => ?_)
  rw [invPostG_invRep] at hz ⊢
  obtain ⟨hz2, F⟩ := pmFinRX (gS := guard st (IoRSR st K.uV.ptU Locks s) (IoWS (st := st) K.uV.ptU Locks s))
    (W := IoWS (st := st) K.uV.ptU Locks s) hA hE0 (P.ioWr (Locks := Locks)) (SWr.of_W rst.2) emi C0 ecap hyD hz
  refine ⟨?_, hz2, fun w hw => ?_⟩
  swap
  · rw [syscall.finish.guard_resume ar z.1 z.2.1 (nd_at (fun o h1 h2 => P.ndR (Locks := Locks) o h1 h2) F.k F.c)
      F.nd F.td F.rs F.ha F.hsw F.hfr F.hact F.hvc]
    exact hw
  -- the reply runs alike (`pmAccGX`'s second part)
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
    have hbuf0 := hJ.here.1.buf8
    have hbw : ∀ b, msg.lookup_ipc_buffer st s2 true (L.curW s) = ok b → BufW W0 b ∧ BufW R0 b := by
      intro b eb
      rw [hlb] at eb
      exact ⟨fun h0 i hi => Or.inr (hbuf0 b eb h0 i hi), fun h0 i hi => Or.inr (hbuf0 b eb h0 i hi)⟩
    rw [invRep.guard_errPm (gS := guard st R0 W0) er (fun e1 => PathObl.syscall.reply_error.guard
      (gS := guard st R0 W0) s2 (L.curW s) e1 hbsl hI (Or.inl hbs.1) (Or.inl hbs.2) (fun r hr => hWio.reg r hr)
      hbw)]
    exact hz

end restR

section slot
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)

/-- The VM PageMap path restricted to `TabKU` states. -/
noncomputable abbrev pmRV (j : InvArg S) (K : KLayoutP) (E m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (h : PmPremX st j K) :
    LocalPath (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) :=
  (pmPathX st ar hA hm j K m hK hU h).restrQ (fun σ => TabKU (L := L) K E σ)
    (fun _ _ _ _ h hb ha => tabKU_wr h hb ha)

/-- Accepted runs of the restricted VM PageMap path are `InsTP` at the epoch's paging words. -/
def PmAccInsX : Prop :=
  ∀ (j : InvArg S) (K : KLayoutP) (E m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (h : PmPremX st j K),
    let P := pmRV st ar hA hm j K E m hK hU h
    ∀ s a r, P.Pre s → P.F P.ar P.st s a = ok r → P.Acc r.1 →
      InsTP P.st P.ar (PWE K E) ADEq NotPresent (· ∈ K.user) Set.univ ∅ P.p s a

set_option maxHeartbeats 4000000 in
/-- **`PmAccInsX` holds** (`pmAccIns` at the VM entry). -/
theorem pmAccInsX : PmAccInsX st ar hA hm := by
  intro j K E m hK hU hP _P s a r hs hr hacc
  obtain ⟨hE0, hqE0⟩ := hs
  have hE : PmPreGX st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K m s := hE0
  have hqE : TabKU (L := L) K E s := hqE0
  have hr0 : syscall.handle_invocation_local st ar s a j.number j.p = ok r := hr
  have h0 : syscall.handle_invocation_local st ar s a j.number j.p = ok (true, r.2.1, r.2.2) := by
    obtain ⟨b, s1, a1⟩ := r
    have hb : b = true := hacc
    subst hb
    exact hr0
  have hp := pm_isProgOnX (st := st) (Cs := j.Cs) (Ω := j.Ω) (Sg := j.Sg) (Ac := j.Ac) (Locks := j.Locks)
    (p := j.p) (K := K) (μ := m) hA j.number
  have hr' : interp st ar (R.invBodyPmG j.number j.p) s a = ok (true, r.2.1, r.2.2) := by
    rw [← inv_hp hp (Narrow.self st) (AltOf.pre hE.1) a]; exact h0
  show InsTP st ar (PWE K E) ADEq NotPresent (· ∈ K.user) Set.univ ∅ (R.invBodyPmG j.number j.p) s a
  refine insTP_entPm hA (K := K.uV.ptU) (Locks := j.Locks)
    (P := fun s => PmPreGX st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K m s ∧ TabKU (L := L) K E s)
    (fun x hx => pwe_user hU hx) (fun s h => h.1.1.2.1.1.1.1.ptUX h.1.1.2.2)
    (fun s h q hq => hq.elim (fun h' => ioRSR_ptU_notPWE hK h.1.1.2.2.ks (ioRSR_uV h'))
      (fun h' => ioWS_notPWE hK (ioWS_uV h')))
    (fun s h => pm_seenRX h.1.1.1 h.1.1.2.1 (h.1.1.2.1.1.1.1.ptUX h.1.1.2.2)) (fun s h => ?_)
    (fun s a info nx s1 s2 a1 buf length cap r' h _ emi C _ ecap _ hR =>
      insTP_pmRestX hA hK hU h.1 h.2 emi C ecap hR) s a _ ⟨hE, hqE⟩ ⟨_, _, h0⟩ hr'
  have Pu := h.1.1.2.1.1.1.1.ptUX h.1.1.2.2
  obtain ⟨-, -, -, -, -, -, hsl, -, hlk, -⟩ := pm_core h.1.1.2.1
  have h0' : j.p.slot ≠ 0#u64 := fun e => h.1.1.1.hz (e ▸ hsl)
  obtain ⟨-, hf⟩ := Pu.lay.slot8 _ hsl
  refine ⟨?_, Pu.lockSlotR hsl (hlk h0') (o := 8#u64) (by simp) (by simp)⟩
  have := Pu.lockSlotR (Locks := j.Locks) hsl (hlk h0') (o := 0#u64) (by simp) (by simp)
  rwa [wadd_zero hf] at this

variable {st ar}

/-- **The VM PageMap path's declined runs touch no paging word of the epoch** (`pm_decR`). -/
theorem pm_decRV (j : InvArg S) {K : KLayoutP} {E m : U64 → U64} (hK : RegionOKP K) (hU : UserOKP K)
    (hP : PmPremX st j K) :
    let P := pmRV st ar hA hm j K E m hK hU hP
    ∀ s s' a r, P.Pre s → P.F P.ar P.st s a = ok r → ¬ P.Acc r.1 →
      @Alt _ P.st P.L (P.RS s) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) s s' →
      Within P.st P.ar (fun b => ¬ PWE K E b) (fun b => b ∈ K.user ∨ ¬ PWE K E b) P.p s' a := by
  intro P
  refine LocalPath.decG P (R0 := fun s => IoRSR st K.uV.ptU j.Locks s) ?_ ?_ ?_
  · intro s s' a r r' hs0 hr hn Al hr'
    have hs : PmPreGX st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K m s := hs0.1
    obtain ⟨⟨hJ, hq, hG⟩, -, -⟩ := hs
    have P0' := hq.1.1.1
    have Pu := P0'.ptUX hG
    have Al' : Alt st (PmRSU st K j.Locks s) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m)
        (· ∈ K.user) s s' := Al
    have AlR := (alt_ptUX hG (alt_pmU Al')).anti (R' := IoRSR st K.uV.ptU j.Locks s) (fun x hx => hx.1)
    have hr0 : r.1 ≠ true := hn
    exact inv_dec_guardRSR hA Pu (pm_seenRX hJ hq Pu) AlR hr hr0 hr'
  · intro s x hs0 hx
    have hs : PmPreGX st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K m s := hs0.1
    exact ioRSR_ptU_notPWE hK hs.1.2.2.ks (ioRSR_uV hx)
  · intro s x hs0 hx
    have hs : PmPreGX st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K m s := hs0.1
    exact ioDS_notPWE hK hs.1.2.2.ks hs.1.2.1.1.1.1 hx

/-- **`InsAP` of a VM-epoch PageMap start** (`insAP_pmR` at the VM layout, `TabKU` from `EpochJV` and `VmPweT`). -/
theorem insAP_pmX (K : KLayoutP) (E : U64 → U64) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K)
    (c : U64) (hs : U64 → Prop) (q : SP) (j : InvArg S) (hW : VmPweT K E) (J : EpochJV K E s) (hM : MapsP K s)
    (h : StartAt (pmSlotVX st ar hA hm j K s.mem hK hU) c hs s.mem q) :
    InsAP (PWE K E) ADEq NotPresent s.own s.cls s.ko c hs ∅ s.mem q := by
  by_cases hp : PmPremX st j K
  · rw [pmSlotVX_pos st ar hA hm hp] at h
    obtain ⟨σ, a, hpre, hc, hl, hμ, rfl⟩ := h
    have hpre' : PmPreGX st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K s.mem σ := hpre
    have hT : TabKU (L := L) K E σ := tabKU_start J hW hpre'.1.2.1.1.1.1.kb.symm hμ
    have h' : StartAt (pmRV st ar hA hm j K E s.mem hK hU hp) c hs s.mem
        ((pmPathX st ar hA hm j K s.mem hK hU hp).body σ a) :=
      ⟨σ, a, ⟨hpre, hT⟩, hc, hl, hμ, rfl⟩
    rw [hM.own, hM.cls, hM.ko]
    exact LocalPath.insAQP _ adEq_equiv (moveHeldP hK) (ownDepP hK hU) (pwe_own hK) (fun x hx => pwe_ko hK _ hx)
      (fun x hx => pwe_user hU hx) (pmAccInsX st ar hA hm j K E s.mem hK hU hp)
      (fun s1 s2 a r hs1 hr hn Al => pm_decRV hA hm j hK hU hp s1 s2 a r hs1 hr hn Al) h'
  · unfold pmSlotVX at h
    rw [dif_neg hp] at h
    obtain ⟨σ, a, hpre, -⟩ := h
    exact (hpre : False).elim

end slot

end
end Fl4Proofs.P2.E2EP
