/-
# P2 (line p3mc, gen 15): the declining arms' words at a view start (`fltDec_v`, `rrDec_v`)

At an sl entry state `s` at core `c`'s view (`SlVC`), whose decided thread (`slThr`), when live, is homed on `c` in
`ρ`, every word a declining arm reads (`FltDec` / `RrDec`, P2/SlDecG) is `SR`:

* **`fltDecT_v`** / **`rrDecT_v`**: the words read before the decided thread's (no homing needed), shared with the
  foreign-thread certificate;
* **`fltDec_v`** / **`rrDec_v`**: with the decided thread's words (`DestDec` / `UDec`), it homed.

(`fltDec_nu` / `rrDec_nu`'s walks, P2/SlJUB, P2/SlOnceN, with `SR` pins.)

No premise: every fact is a hypothesis. No existing statement changed.
-/
import Fl4Proofs.P2.SlVAccR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY oTIMER_DEADLINE InW)
open Fl4Proofs.P2.CoreView (view VN VKc VNW VDec NotForeign vn_of_nf nf_node nf_sc nf_slot nf_none nf_tcb vn_td
  view_keep_tcb vkc_of not_vdec_node not_vdec_sc not_vdec_tcb TZero decOff_list)

noncomputable section
open Classical

section rec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable {K : KLayoutP} {c : U64} {ρ : U64 → U64} {Locks : S → U64 → Prop} {m0 : U64 → U64} {n : I64}
  {found : U64 × U64} {Cs Ω Sg Ac : Set U64}

set_option maxHeartbeats 4000000 in
/-- **The trap arm's words before the receiver's are `SR`.** -/
theorem fltDecT_v (hA : P0.ArchTotal ar) {s : S}
    (F : SlOF (st := st) ar K.toKLayout Locks m0 n found Cs Ω Sg Ac s) (V : SlVC (L := L) K c ρ s)
    {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) : FltDecT (L := L) (SR K c ρ) X (L.curW s) := by
  have B := F.B
  have E := F.E
  have hK := V.hK
  have hX := B.regionOKX
  obtain ⟨hk, hcp⟩ := B.kc
  have C := slCom_v ar hA V B E LP
  have hcH := E.hSt.1
  have fs := sr_tslot (c := c) (ρ := ρ) hK hX hcH (i := layout.tcb.SLOT_FAULT_HANDLER) (by simp [layout.tcb.SLOT_FAULT_HANDLER])
  obtain ⟨hs, -, r8, -, a0, a8⟩ := hX.tslot _ hcH layout.tcb.SLOT_FAULT_HANDLER
    (by simp [layout.tcb.SLOT_FAULT_HANDLER])
  have hK0 := B.regionOK
  have nd0 : ¬ SlDS (L := L) s (slotIdx (L.curW s) layout.tcb.SLOT_FAULT_HANDLER) :=
    not_slDS_reg hX E.hN E.hT E.hcT hcH hk hcp (by rw [hK0.slot _ hs]; intro c h; cases h)
      (by rw [hK0.slot _ hs]; intro h; cases h)
  have nd8 : ¬ SlDS (L := L) s (core.num.U64.wrapping_add (slotIdx (L.curW s) layout.tcb.SLOT_FAULT_HANDLER) 8#u64) :=
    not_slDS_reg hX E.hN E.hT E.hcT hcH hk hcp (by rw [r8]; intro c h; cases h) (by rw [r8]; intro h; cases h)
  refine ⟨C.nd, C.dt, C.cd, C.bm, C.tm, C.rh, fs, fun ptr bb x y g gr hcap => ?_⟩
  have ecap : obj.Slot.cap st (fhA (L := L) s) X = obj.Slot.cap st (fhA (L := L) s) s :=
    cap_congr (lp_mem ar hA E.hT E.hN E.hcT LP a0 nd0) (lp_mem ar hA E.hT E.hN E.hcT LP a8 nd8)
  have hcap' : obj.Slot.cap st (fhA (L := L) s) s = ok (capability.Cap.Endpoint ptr bb x y g gr) := by
    rw [← ecap]; exact hcap
  have hpH : K.toKLayout.heap ptr = some .ep := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, B'⟩ := B
    have h := B'.hep ⟨ptr, bb, x, y, g, gr, hcap'⟩
    rwa [resPtr_ok hcap'] at h
  exact ⟨(srw_ep hK hX hpH (o := layout.ep.TAIL_STATE) (by simp [layout.ep.TAIL_STATE])
    (by simp [layout.ep.TAIL_STATE])).1, (srw_ep hK hX hpH (o := layout.ep.HEAD) (by simp [layout.ep.HEAD])
    (by simp [layout.ep.HEAD])).1⟩

set_option maxHeartbeats 4000000 in
/-- **The trap arm's declining reads are `SR`**, the receiver homed. -/
theorem fltDec_v (hA : P0.ArchTotal ar) {s : S}
    (F : SlOF (st := st) ar K.toKLayout Locks m0 n found Cs Ω Sg Ac s) (V : SlVC (L := L) K c ρ s)
    (hS : SlTrap st s) (hH : SlLive st found.1 s → ρ (fld (slThr st found.1 s) oAFFINITY) = c)
    {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) : FltDec (L := L) (SR K c ρ) X (L.curW s) := by
  have B := F.B
  have E := F.E
  have hK := V.hK
  have hX := B.regionOKX
  refine FltDec.of (fltDecT_v ar hA F V LP) (fun ptr bb x y g gr hcap hst d hd => ?_)
  have e1 := slThr_hd_trap ar hA E.hT E.hN E.hcT F.I hS LP hcap
  have lv := slLive_trap ar hA E.hT E.hN E.hcT F.I hS LP hcap hst
  have hdd : d = slThr st found.1 s := by
    rw [eq_of_spec_fd (obj.Ep.head.spec' (st := st) X ptr), e1] at hd
    exact (ok_inj_ff hd).symm
  subst hdd
  have hdT := F.N.hthr lv
  have ha := hH lv
  exact ⟨sr_tcb hK hX hdT ha (o := 3360#u64) (by simp) (by simp) (by simp),
    sr_tcb hK hX hdT ha (o := 3520#u64) (by simp) (by simp) (by simp),
    fun _ => ⟨sr_tcb hK hX hdT ha (o := 3432#u64) (by simp) (by simp) (by simp),
      sr_tcb hK hX hdT ha (o := 3464#u64) (by simp) (by simp) (by simp),
      sr_tcb hK hX hdT ha (o := 3592#u64) (by simp) (by simp) (by simp),
      sr_tcb hK hX hdT ha (o := 3448#u64) (by simp) (by simp) (by simp)⟩⟩

set_option maxHeartbeats 4000000 in
/-- **The ReplyRecv arm's words before the replied thread's are `SR`** (the replied thread homed or not: `RrDR`'s
thread-free part). -/
theorem rrDecT_v (hA : P0.ArchTotal ar) {s : S}
    (F : SlOF (st := st) ar K.toKLayout Locks m0 n found Cs Ω Sg Ac s) (V : SlVC (L := L) K c ρ s)
    (hS : ¬ SlTrap st s) {a X a1} (LP : LocalPre (st := st) ar s a (X, a1))
    (D' : RrDR (L := L) (SR K c ρ) X (L.curW s) found.1 found.2) :
    RrDecT (L := L) (SR K c ρ) X (L.curW s) found.1 found.2 := by
  have B := F.B
  have E := F.E
  have C := slCom_v ar hA V B E LP
  obtain ⟨-, -, aT, -, -, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
  have eS : L.mem X (scA (L.curW s)) = L.mem s (scA (L.curW s)) :=
    aT _ E.hcT 3464#u64 (by simp) (by simp) (by simp)
  refine ⟨D'.nd, D'.dt, D'.cd, C.bm, D'.tm, D'.rh, D'.tSt, D'.tSc, D'.tMx (by rw [eS]; exact V.scn), D'.tIq,
    D'.tMi, D'.tBn, D'.tPr, ?_, D'.rRt, D'.rNx, D'.eTS⟩
  intro nt hnt hne
  have e1 := (eq_of_spec_fd (obj.Tcb.bound_ntfn.val X (L.curW s))).symm.trans hnt
  have en : nt = L.mem X (boundA (L.curW s)) := (ok_inj_ff e1).symm
  subst en
  exact D'.ntf (fun h0 => by rw [h0] at hne; simp at hne)

set_option maxHeartbeats 4000000 in
/-- **The ReplyRecv arm's declining reads are `SR`**, the replied thread homed. -/
theorem rrDec_v (hA : P0.ArchTotal ar) {s : S}
    (F : SlOF (st := st) ar K.toKLayout Locks m0 n found Cs Ω Sg Ac s) (V : SlVC (L := L) K c ρ s)
    (hS : ¬ SlTrap st s) (hH : SlLive st found.1 s → ρ (fld (slThr st found.1 s) oAFFINITY) = c)
    {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) :
    RrDec (L := L) (SR K c ρ) X (L.curW s) found.1 found.2 := by
  have B := F.B
  have E := F.E
  have Hh := F.Hh
  have I := F.I
  have hK := V.hK
  have hX := B.regionOKX
  have hc := E.hSt.1
  have nT : ∀ {t o : U64}, K.toKLayout.heap t = some .tcb → 192 ≤ o.val → o.val < 4096 → o.val % 8 = 0 →
      o.val ≠ 392 → ¬ SlDS (L := L) s (core.num.U64.wrapping_add t o) := fun ht h1 h2 h3 h4 =>
    not_slDS_tcb hX E.hN E.hT E.hcT hc Hh.ksb Hh.cpu ht h1 h2 h3 h4
  have eTh : ∀ u, L.mem X (rTcbA found.1) = u → u ≠ 0#u64 → u = slThr st found.1 s ∧ SlLive st found.1 s := by
    intro u hu hu0
    have h2 := slThr_hd_rr ar hA E.hT E.hN E.hcT I hS LP (rp := found.1)
    have e : u = slThr st found.1 s := by rw [← hu]; exact h2
    exact ⟨e, slLive_rr (st := st) hS (by rw [← e]; exact hu0)⟩
  have D' := rrDR_v ar hA F V hS LP (fun u hu hu0 => by
    obtain ⟨e, lv⟩ := eTh u hu hu0; rw [e]; exact hH lv)
  refine RrDec.of (rrDecT_v ar hA F V hS LP D') ?_
  intro u hu hu0
  have h1 := obj.Reply.tcb.blk (st := st) X found.1
  rw [hu, WP.spec_ok, slThr_hd_rr ar hA E.hT E.hN E.hcT I hS LP] at h1
  have lv := slLive_rr (st := st) hS (by rw [← h1]; exact hu0)
  have ht := F.N.hthr lv
  have ha := hH lv
  rw [h1]
  have tw : ∀ o : U64, 192 ≤ o.val → o.val < 4096 → o.val % 8 = 0 →
      SR K c ρ (core.num.U64.wrapping_add (slThr st found.1 s) o) := fun o h1 h2 h3 => sr_tcb hK hX ht ha h1 h2 h3
  refine ⟨by rw [stA_eq]; exact tw _ (by simp) (by simp) (by simp), tw 3376#u64 (by simp) (by simp) (by simp),
    tw 3464#u64 (by simp) (by simp) (by simp), tw 3520#u64 (by simp) (by simp) (by simp),
    fun hh => ⟨tw 3432#u64 (by simp) (by simp) (by simp), tw 3592#u64 (by simp) (by simp) (by simp),
      tw 3448#u64 (by simp) (by simp) (by simp), fun usc eu hne => ?_⟩⟩
  obtain ⟨-, hcX, -, -, -, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
  have af := I.af lv
  have hh' : L.mem s (affA (slThr st found.1 s)) = L.cpu s := by
    rw [← lp_mem ar hA E.hT E.hN E.hcT LP af.1.1 af.2, hh, hcX]
  have eU : L.mem X (scA (slThr st found.1 s)) = L.mem s (scA (slThr st found.1 s)) :=
    lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ ht 3464#u64 (by simp) (by simp) (by simp)).2.2
      (nT ht (by simp) (by simp) (by simp) (by simp))
  have eX : L.mem X (scA (slThr st found.1 s)) = usc := by rw [tcb_sc_ok] at eu; exact ok_inj_ff eu
  have e1 : usc = L.mem s (scA (slThr st found.1 s)) := by rw [← eX, eU]
  -- `usc` homed in `ρ`: its back-pointer
  obtain ⟨⟨Q, Rq, hq⟩, hB, hXI, -, hSC⟩ := E.hI a X a1 LP
  have hX0 := hXI.2.2.toScExtra0
  have huT : slThr st found.1 s ∈ K.toKLayout.heap.tcbs := ht
  obtain ⟨hcS, htb, -⟩ := hX0.bound _ huT (by rw [eX]; exact hne)
  rw [eX] at hcS htb
  have hz := scs_heap (K := K.toKLayout) hcS
  obtain ⟨-, aT', -, rT⟩ := sc_off hX hz (o := layout.sc.TCB) (by simp [layout.sc.TCB]) (by simp [layout.sc.TCB])
  have rT' : region K.toKLayout (scTcbA usc) = .sc usc := rT
  have eT : L.mem X (scTcbA usc) = L.mem s (scTcbA usc) :=
    lp_mem ar hA E.hT E.hN E.hcT LP aT' (not_slDS_reg hX E.hN E.hT E.hcT hc Hh.ksb Hh.cpu
      (by rw [rT']; intro c h; cases h) (by rw [rT']; intro h; cases h))
  have hpc : ρ (fld usc 16#u64) = c := V.scb usc hcS (by rw [← eT, htb, ← h1]; exact hu0)
  have hHs := Hh.usc hS lv hh' (by rw [← e1]; exact hne)
  rw [← e1] at hHs
  exact rdHead_v ar hA V B E Hh LP hHs hpc

end rec

end
end Fl4Proofs.P2.E2EP
