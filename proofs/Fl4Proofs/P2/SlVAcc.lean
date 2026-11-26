/-
# P2 (line p3mc, gen 15): the accepted trap arm's words at a view start (`fltAcc_v`)

At an sl entry state `s` at core `c`'s view (`SlVC`), trap arm, with the receiver `dest` (the handler endpoint's head)
homed on `c` in `ρ` and its SC homed on `c`, every word of the accepted trap arm's record `FltAcc` (P2/AccessFastFault)
is `SR` when read and `VNW` when written:

* `vn_linkQ`: `vn_link` (P2/VmBView) for a queued (receive or notification) state at the view: the next queued
  thread's `EP_PREV`, whoever's it is, is kept by the view with its lock owner;
* `rdTab_v`: the ASID table and pools (region `.none`, no PTE word by `TabNoE`);
* **`fltAcc_v`**: `FltAcc Z (SR K c ρ) (VNW K c ρ)` at every prefix state under the trap arm's checks
  (`fltAcc_nuT`'s walk, P2/SlOnceN, with `SR` / `VNW` pins).

No premise: every fact is a hypothesis. No existing statement changed.
-/
import Fl4Proofs.P2.SlVPin
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

section link
theorem vn_linkQ {K : KLayoutP} (hK : RegionOKP K) {c : U64} {ρ : U64 → U64} {y off : U64}
    (hy : K.heap y = some .tcb) (hr : region K.toKLayout (fld y off) = .tcb y)
    (ho : (fld y off).val - y.val = off.val) (hoff : off.val = 3496 ∨ off.val = 3504)
    (hst : OwnMap.QueuedState (view K.toKLayout c ρ (fld y OwnMap.oSTATE))) :
    VN K c ρ (fld y off) ∧ VKc K.toKLayout c ρ (fld y off) ∧ ¬ VDec K.toKLayout c ρ (fld y off) := by
  have hK0 := hK.base.base
  have hkc : VKc K.toKLayout c ρ (fld y off) := by
    unfold VKc
    have hne : ¬ ((fld y off).val - y.val = 3328 ∨ (fld y off).val - y.val = 3528) := by omega
    simp only [OwnMap.ko, hr, if_neg hne]
  have hnd : ¬ VDec K.toKLayout c ρ (fld y off) := by
    rintro (⟨t', off', ht', -, ho', e⟩ | ⟨p, hp, e⟩ | ⟨t', ht', e⟩ | ⟨p, b', hb', -, e⟩)
    · obtain ⟨h1, h2⟩ := hK0.tcb t' ht' off' (decOff_list ho')
      rw [← e, hr] at h1
      cases h1
      rw [← e, ho] at h2
      rcases decOff_list ho' with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [OwnMap.oAFF_val, OwnMap.oSTATE_val, OwnMap.oBOBJ_val, OwnMap.oROBJ_val, OwnMap.oDL_val,
          OwnMap.oHT_val] at h2 <;> omega
    · have h1 := (hK0.ntfn p hp).1
      rw [← e, hr] at h1; cases h1
    · obtain ⟨h1, h2⟩ := hK0.tcb t' ht' _ (Or.inl rfl)
      rw [← e, hr] at h1
      cases h1
      rw [← e, ho, OwnMap.oAFF_val] at h2; omega
    · have h1 := (hK0.scw p b' hb').1
      rw [← e, hr] at h1; cases h1
  by_cases ha : ρ (fld y oAFFINITY) = c
  · exact ⟨vn_of_nf hK (nf_tcb hr ha), hkc, hnd⟩
  refine ⟨⟨view_keep_tcb hr (by omega) (by unfold TZero; omega) (by omega), ?_⟩, hkc, hnd⟩
  obtain ⟨hrS, hoS⟩ := hK0.tcb y hy OwnMap.oSTATE (Or.inr (Or.inl rfl))
  obtain ⟨hrB, hoB⟩ := hK0.tcb y hy OwnMap.oBLOCK_OBJ (Or.inr (Or.inr (Or.inl rfl)))
  rw [OwnMap.oSTATE_val] at hoS; rw [OwnMap.oBOBJ_val] at hoB
  have hne : view K.toKLayout c ρ (fld y OwnMap.oSTATE) ≠ 0#u64 := by
    intro h; rw [h] at hst; unfold OwnMap.QueuedState at hst; simp at hst
  have eS := view_state_keep hrS ha hoS hne
  have eB : view K.toKLayout c ρ (fld y OwnMap.oBLOCK_OBJ) = ρ (fld y OwnMap.oBLOCK_OBJ) :=
    view_keep_tcb hrB (by omega) (by unfold TZero; omega) (by omega)
  have hq : OwnMap.QueuedState (ρ (fld y OwnMap.oSTATE)) := by rw [← eS]; exact hst
  have hp : fld y off ∉ K.ptes := fun h => by rw [hK.none _ h] at hr; cases hr
  have hv : ¬ ∃ v, Fl4Proofs.P2.OwnMapV.InVcpu K.toKLayoutV v (fld y off) := by
    rintro ⟨v, hv⟩; rw [hK.base.none v _ hv] at hr; cases hr
  have g1 : ¬ OwnMap.GateField ((fld y off).val - y.val) := by rw [ho]; unfold OwnMap.GateField; omega
  have g2 : ¬ OwnMap.TimerField ((fld y off).val - y.val) := by rw [ho]; unfold OwnMap.TimerField; omega
  have g3 : OwnMap.GField ((fld y off).val - y.val) := by rw [ho]; unfold OwnMap.GField; omega
  rw [ownP_off hp, ownP_off hp, ownV_off hv, ownV_off hv]
  simp only [OwnMap.own, hr, OwnMap.tcbOwner, if_neg g1, if_neg g2, if_pos g3, OwnMap.gOwner, eS, eB, if_pos hq]

end link

section rec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable {K : KLayoutP} {c : U64} {ρ : U64 → U64} {Locks : S → U64 → Prop} {m0 : U64 → U64} {n : I64}
  {found : U64 × U64} {Cs Ω Sg Ac : Set U64}

/-- **The ASID table and pools are `SR` at the prefix state.** -/
theorem rdTab_v (hA : P0.ArchTotal ar) {s : S} (V : SlVC (L := L) K c ρ s) (hJ : SlJAt (L := L) K.toKLayout s)
    (E : SlPreB (st := st) ar K.toKLayout Locks m0 n found K.toKLayout.heap.tcbs Cs Ω K.user Sg
      K.toKLayout.heap.replies K.toKLayout.heap.scs K.toKLayout.heap.ntfns Ac K.toKLayout.heap
      K.toKLayout.heap.scBits s)
    (Hh : SlHere (st := st) K.toKLayout K.toKLayout.heap.scBits K.toKLayout.heap.scs found s)
    (Ai : SlAccIn (st := st) ar K.toKLayout Locks K.toKLayout.heap.scBits K.toKLayout.heap.scs found s)
    {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) : RdTab (L := L) (SR K c ρ) X := by
  have hX := hJ.regionOKX
  obtain ⟨kX, -, -, -, -, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
  intro hi hhi
  rw [kX]
  obtain ⟨r0, a0⟩ := hX.asidT hi hhi
  have e0 : L.mem X (atAF (L.ksb s) hi) = L.mem s (atAF (L.ksb s) hi) := by
    rw [Hh.ksb]
    exact lp_mem ar hA E.hT E.hN E.hcT LP a0 (not_slDS_reg hX E.hN E.hT E.hcT E.hSt.1 Hh.ksb Hh.cpu
      (by rw [r0]; intro c h; cases h) (by rw [r0]; intro h; cases h))
  have hk := V.ksb
  refine ⟨⟨vn_of_nf V.hK (nf_none (by rw [hk]; exact r0)), (V.tab hi hhi).1⟩, fun lo hlo hne => ?_⟩
  rw [e0] at hne ⊢
  have hne' : L.mem s (atAF K.ksb hi) ≠ 0#u64 := by rw [← hk]; exact hne
  obtain ⟨-, rp⟩ := Ai.pool hi hhi hne' lo hlo
  exact ⟨vn_of_nf V.hK (nf_none (by rw [hk]; exact rp)), (V.tab hi hhi).2 lo hlo hne⟩

set_option maxHeartbeats 8000000 in
/-- **The accepted trap arm's words are kept by the view** (module docstring). -/
theorem fltAcc_v (hA : P0.ArchTotal ar) {s : S}
    (F : SlOF (st := st) ar K.toKLayout Locks m0 n found Cs Ω Sg Ac s) (V : SlVC (L := L) K c ρ s)
    (hS : SlTrap st s) {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) {ptr badge dest r : U64}
    (hc : FaultChecks st X (L.curW s) ptr badge dest r) (hdA : ρ (fld dest oAFFINITY) = c)
    (hdS : ρ (fld (L.mem s (scA dest)) 16#u64) = c) :
    FltAcc (L := L) K.toKLayout.heap.scBits (SR K c ρ) (VNW K c ρ) X (L.curW s) ptr dest r := by
  have B := F.B
  have E := F.E
  have Hh := F.Hh
  have hK := V.hK
  have hK0 := B.regionOK
  have hX := B.regionOKX
  have C := slCom_v ar hA V B E LP
  obtain ⟨kX, cX, -, -, ecs, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
  have hc0 := E.hSt.1
  obtain ⟨hep, -⟩ := trap_ep ar hA E F.N F.I hS LP hc
  obtain ⟨hdt, -, -, -⟩ := E.hSd hS a X a1 LP hc
  have nT : ∀ {t o : U64}, K.toKLayout.heap t = some .tcb → 192 ≤ o.val → o.val < 4096 → o.val % 8 = 0 →
      o.val ≠ 392 → ¬ SlDS (L := L) s (core.num.U64.wrapping_add t o) := fun ht h1 h2 h3 h4 =>
    not_slDS_tcb hX E.hN E.hT E.hcT hc0 Hh.ksb Hh.cpu ht h1 h2 h3 h4
  obtain ⟨hz, -, -, -⟩ := F.Ai.dsc hS a X a1 LP hc
  have eSc : L.mem X (scA dest) = L.mem s (scA dest) :=
    lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ hdt 3464#u64 (by simp) (by simp) (by simp)).2.2
      (nT hdt (by simp) (by simp) (by simp) (by simp))
  have nX : ∀ o, L.nodeAt X (L.cpu X) o = L.nodeAt s (L.cpu s) o := fun o => by
    rw [cX, nodeAt_of_ksb kX]
  have eRh : L.mem X (rhA (L := L) X) = L.mem s (rhA (L := L) s) := by
    show L.mem X (L.nodeAt X (L.cpu X) layout.node.RELEASE_HEAD) =
      L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD)
    rw [nX]
    exact lp_mem ar hA E.hT E.hN E.hcT LP (nodeAt_aligned E.hN (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD])) (not_slDS_node E.hN E.hT E.hcT (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]))
  have trc : ∀ o : U64, 192 ≤ o.val → o.val < 4096 → o.val % 8 = 0 →
      SR K c ρ (core.num.U64.wrapping_add (L.curW s) o) := fun o h1 h2 h3 => sr_tcb hK hX hc0 V.cur h1 h2 h3
  have twc : ∀ o : U64, 192 ≤ o.val → o.val < 4096 → o.val % 8 = 0 → o.val ≠ 3520 →
      VNW K c ρ (core.num.U64.wrapping_add (L.curW s) o) := fun o h1 h2 h3 h4 =>
    vnw_tcb hK hX hc0 V.cur h1 h2 h3 h4
  have trd : ∀ o : U64, 192 ≤ o.val → o.val < 4096 → o.val % 8 = 0 →
      SR K c ρ (core.num.U64.wrapping_add dest o) := fun o h1 h2 h3 => sr_tcb hK hX hdt hdA h1 h2 h3
  have twd : ∀ o : U64, 192 ≤ o.val → o.val < 4096 → o.val % 8 = 0 → o.val ≠ 3520 →
      VNW K c ρ (core.num.U64.wrapping_add dest o) := fun o h1 h2 h3 h4 =>
    vnw_tcb hK hX hdt hdA h1 h2 h3 h4
  exact
  { nd := fun o h1 h2 => by rw [nX]; exact srw_node V B E.hN h1 h2
    dt := C.dt
    cd := C.cd
    kr := by
      show SR K c ρ (core.num.U64.wrapping_add (L.ksb X) layout.ks.KERNEL_ROOT)
      rw [kX]
      exact sr_ks V B E.hN (by simp [layout.ks.KERNEL_ROOT]) (by simp [layout.ks.KERNEL_ROOT])
    tab := rdTab_v ar hA V B E Hh F.Ai LP
    fh := fun sl hsl => by
      rw [tcb_slot_val] at hsl
      obtain rfl := ok_inj_ff hsl
      exact sr_tslot hK hX hc0 (by simp [layout.tcb.SLOT_FAULT_HANDLER])
    eph := srw_ep hK hX hep (o := layout.ep.HEAD) (by simp [layout.ep.HEAD]) (by simp [layout.ep.HEAD])
    ept := srw_ep hK hX hep (o := layout.ep.TAIL_STATE) (by simp [layout.ep.TAIL_STATE])
      (by simp [layout.ep.TAIL_STATE])
    tf := fun o ho => ⟨trc o (by rcases ho with h | h | h | h <;> omega)
      (by rcases ho with h | h | h | h <;> omega) (by rcases ho with h | h | h | h <;> omega),
      twc o (by rcases ho with h | h | h | h <;> omega) (by rcases ho with h | h | h | h <;> omega)
        (by rcases ho with h | h | h | h <;> omega) (by rcases ho with h | h | h | h <;> omega)⟩
    treg := fun _ hr => sr_reg hK hX hc0 V.cur hr
    trp := twc 3360#u64 (by simp) (by simp) (by simp) (by simp)
    drp := trd 3360#u64 (by simp) (by simp) (by simp)
    daf := trd 3520#u64 (by simp) (by simp) (by simp)
    ddo := trd 3432#u64 (by simp) (by simp) (by simp)
    dsc0 := trd 3464#u64 (by simp) (by simp) (by simp)
    diq := trd 3592#u64 (by simp) (by simp) (by simp)
    dpr := trd 3448#u64 (by simp) (by simp) (by simp)
    dyt := trd 3472#u64 (by simp) (by simp) (by simp)
    dst := by rw [stA_eq]; exact trd 3328#u64 (by simp) (by simp) (by simp)
    dfi := sr_reg hK hX hdt hdA (r := layout.reg.FAULT_IP) (by simp [layout.reg.FAULT_IP])
    den := trd 3496#u64 (by simp) (by simp) (by simp)
    dib := trd 3512#u64 (by simp) (by simp) (by simp)
    dvt := by
      rw [vtA_slot]
      exact sr_tslot hK hX hdt (by simp [layout.tcb.SLOT_VTABLE])
    dbs := fun sl hsl => by
      rw [tcb_slot_val] at hsl
      obtain rfl := ok_inj_ff hsl
      exact sr_tslot hK hX hdt (by simp [layout.tcb.SLOT_BUFFER])
    dw := ⟨twd 3496#u64 (by simp) (by simp) (by simp) (by simp), twd 3504#u64 (by simp) (by simp) (by simp) (by simp),
      twd 3480#u64 (by simp) (by simp) (by simp) (by simp), twd 3488#u64 (by simp) (by simp) (by simp) (by simp)⟩
    dreg := fun _ hr => vnw_reg hK hX hdt hdA hr
    nxt := fun hne => by
      obtain ⟨hyT, hyQ, -⟩ := F.Ai.nq hS a X a1 LP hc hne
      generalize ey : L.mem X (nextA .Ep dest) = y at hyT hyQ ⊢
      obtain ⟨rS, -, aS⟩ := hX.tcbW y hyT 3328#u64 (by simp) (by simp) (by simp)
      have eSt : L.mem X (stA y) = L.mem s (stA y) := by
        rw [stA_eq]
        exact lp_mem ar hA E.hT E.hN E.hcT LP aS (nT hyT (by simp) (by simp) (by simp) (by simp))
      have hQv : OwnMap.QueuedState (view K.toKLayout c ρ (fld y OwnMap.oSTATE)) := by
        rw [← OwnMap.stA_fld, ← V.hm (stA y) (by rw [stA_eq]; exact aS)
          (by rw [stA_eq]; exact hX.kern _ (by rw [rS]; intro h; cases h)), ← eSt]
        exact hyQ
      obtain ⟨r4, v4, -⟩ := hX.tcbW y hyT 3504#u64 (by simp) (by simp) (by simp)
      obtain ⟨h1, h2, h3⟩ := vn_linkQ hK hyT (off := 3504#u64) r4 v4 (by simp) hQv
      exact ⟨h1, h2, h3⟩
    buf := fun rb hrb hne i hi => (srw_user hK hX (F.Ai.fbuf hS a X a1 LP hc rb hrb hne i hi).2 V.upte).2
    rt := (srw_rp hK hX (F.Ai.frp hS a X a1 LP hc).1 (o := layout.reply.TCB) (by simp [layout.reply.TCB])
      (by simp [layout.reply.TCB])).2
    spo := by
      rw [eSc]
      obtain ⟨-, -, hin, -⟩ := sc_off hX hz (o := layout.sc.SPORADIC) (by simp [layout.sc.SPORADIC])
        (by simp [layout.sc.SPORADIC])
      exact (srw_sc hK hX hz hdS hin).1
    dsc := by rw [eSc]; exact scAcc_v hK hX hz hdS
    csc := by
      rw [ecs]
      obtain ⟨hz', -, -, -⟩ := Hh.cs
      exact scAcc_v hK hX hz' V.csc
    tm := C.tm
    rh := fun h => by
      refine ⟨(C.rh h).1, ?_, (C.rh h).2⟩
      rw [eRh] at h ⊢
      obtain ⟨ht, hs⟩ := Hh.rh h
      obtain ⟨-, hrS⟩ := V.rh h
      have eS : L.mem X (scA (L.mem s (rhA (L := L) s))) = L.mem s (scA (L.mem s (rhA (L := L) s))) :=
        lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ ht 3464#u64 (by simp) (by simp) (by simp)).2.2
          (nT ht (by simp) (by simp) (by simp) (by simp))
      rw [eS]
      obtain ⟨hz', -, -, -⟩ := hs
      exact fun b _ hb => (srw_sc hK hX hz' hrS hb).1 }

end rec

end
end Fl4Proofs.P2.E2EP
