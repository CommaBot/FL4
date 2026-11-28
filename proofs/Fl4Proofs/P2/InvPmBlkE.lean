/-
# P2 (line pte, generation 15): `FinOK` after the PageMap decode block (`blk`, fifth part)

slhuf's `cmFin8` (P2/InvCMFin8.lean on int19) for the PageMap arm at the layout `KSUPm (ptU K)`: the st run of the
block (`pmRun`) writes `IoTW t` words, the invoked slot's words, the leaf (a PTE word, a `ptU K` user word) and,
on an error, the reply registers and the caller's buffer words (aligned user words, `invBufJ8_of`); all of them miss
what `finish` reads, so **`pmFinG`**: at a `PmPreG` entry, on any store `gS` reading `IoRS (ptU K) s` as `st` and
writing `W` (`IoWr`) with the caller's `STATE` write (`SWr`), the reply is `Ok ()` and `FinOK` holds after it.
The part after the run is `cmFin8`'s, verbatim at `KSUPm (ptU K)`.

**`pmFinGC`** (gen-45 p3mc, moved here from P2/InvPmGdV) is the proof for any read set `R`, the entry record
`IoEnt … R W s` given; `pmFinG` is its one-line instance at `R := IoRS (ptU K) s` (statement unchanged).

No named premise. New module; gen 45 re-proves `pmFinG` as a corollary (statement unchanged).
-/
import Fl4Proofs.P2.InvPmBlkD
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField NullOrFrame TcbSlot)

noncomputable section

section fin
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP} {μ : U64 → U64}
variable {A : Type} {ar : machine.Arch A}

set_option maxHeartbeats 2000000 in
/-- **`FinOK` after the PageMap decode block, for any read set `R`** (module docstring): the entry record
`IoEnt … R W s` is given (`pmFinG` is its instance at `R := IoRS (ptU K) s`). -/
theorem pmFinGC (hA : P0.ArchTotal ar) {s : S} {a : A} {info : msginfo.MessageInfo} {nx : U64} {s1 s2 : S}
    {a1 : A} {buf length : U64} {cap : capability.Cap} {y : (core.result.Result Unit error.Exc) × S × A}
    {z : S × A × core.result.Result Unit error.Exc}
    {R W : U64 → Prop} {gS : machine.Store S} [GRd gS st R] [GWr gS st W]
    (hE : PmPreG st Cs Ω Sg Ac Locks p K μ s)
    (Ent : IoEnt st K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac R W s)
    (hsw : SWr gS st (L.curW s) sched.TS_RUNNING)
    (emi : msg.msg_info st s (L.curW s) = ok info) (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1)
    (hcap : obj.Slot.cap st p.slot s2 = ok cap)
    (hy : syscall.decode_invocation st ar s2 a1 info.label length p.slot cap true true true false buf p.extra =
      ok y)
    (hz : invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z) :
    z.2.2 = .Ok () ∧ FinOK (L := L) gS R W ar s z.1 z.2.1 := by
  obtain ⟨fp, rt, asid, va, mp, x0, root, rasid, e, hcs, hcs2, hx0, hxK, hcx2, hcv2, hpe2, hpt, hle, hRS, hWS, hu,
    hf, hsl, hsl0, hO⟩ := pm_s2 hA hE C
  obtain ⟨⟨hJ, hq, hG⟩, -, -⟩ := hE
  have Pb := hq.1.1.1
  have P := Pb.ptU hG
  obtain ⟨-, es1, eu, eac, ey, ehere, -⟩ := C
  have Hf := here_facts ehere
  have I := IoS2.of_ent hA Ent es1 eu Hf.sc
  have hct : L.curW s2 = L.curW s := I.cur
  have hL : Slot8 K.ptU := fun q hq => P.lay.slot8 q hq
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
      UserW K.ptU (core.num.U64.wrapping_add b (core.num.U64.wrapping_mul i 8#u64)) := fun b eb hne i hi => by
    have h := invBufJ8_of hJ b (by rw [← hlb]; exact eb) hne i hi
    exact ⟨h.1, Or.inl h.2⟩
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
  have ho' : ∀ b ∈ {b | b ∈ Ω ∧ ∃ c' ∈ K.heap.scs, InSC c' (K.heap.scBits c') b}, ¬ UserW (KSUPm K.ptU) b := by
    rintro b ⟨-, c', hc', hin⟩
    exact not_usuPm (P.sc_notUser (P.hSc _ hc') hin) (P.sc_notSlot (P.hSc _ hc') hin)
  have stm : L.mem s2 (tmA (L := L) s2) ≠ 0#u64 → ¬ UserW (KSUPm K.ptU) (tdA (L.mem s2 (tmA (L := L) s2))) :=
    fun h0 => by
      unfold tdA
      exact htU _ (I.tm h0) _ (by simp) (by simp)
  have srh : L.mem s2 (rhA (L := L) s2) ≠ 0#u64 → ¬ UserW (KSUPm K.ptU) (scA (L.mem s2 (rhA (L := L) s2))) ∧
      ¬ UserW (KSUPm K.ptU) (headA (L.mem s2 (scA (L.mem s2 (rhA (L := L) s2))))) ∧
      ¬ UserW (KSUPm K.ptU) (rtA (L.mem s2 (scA (L.mem s2 (rhA (L := L) s2))))
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
  have w3 : WritesIn st s2 z.1 (fun b => IoPW st s2 b ∨ UserW (KSUPm K.ptU) b) :=
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

/-- **`FinOK` after the PageMap decode block** (module docstring): `pmFinGC` at `R := IoRS (ptU K) s`. -/
theorem pmFinG (hA : P0.ArchTotal ar) {s : S} {a : A} {info : msginfo.MessageInfo} {nx : U64} {s1 s2 : S}
    {a1 : A} {buf length : U64} {cap : capability.Cap} {y : (core.result.Result Unit error.Exc) × S × A}
    {z : S × A × core.result.Result Unit error.Exc}
    {W : U64 → Prop} {gS : machine.Store S} [GRd gS st (IoRS (st := st) K.ptU Locks s)] [GWr gS st W]
    (hE : PmPreG st Cs Ω Sg Ac Locks p K μ s)
    (hW : IoWr st W K.heap.scBits s) (hsw : SWr gS st (L.curW s) sched.TS_RUNNING)
    (emi : msg.msg_info st s (L.curW s) = ok info) (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1)
    (hcap : obj.Slot.cap st p.slot s2 = ok cap)
    (hy : syscall.decode_invocation st ar s2 a1 info.label length p.slot cap true true true false buf p.extra =
      ok y)
    (hz : invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z) :
    z.2.2 = .Ok () ∧ FinOK (L := L) gS (IoRS (st := st) K.ptU Locks s) W ar s z.1 z.2.1 := by
  obtain ⟨⟨-, hq, hG⟩, -, -⟩ := id hE
  exact pmFinGC hA hE ((hq.1.1.1.ptU hG).ent (Locks := Locks) hW) hsw emi C hcap hy hz

end fin

end
end Fl4Proofs.P2.E2EP
