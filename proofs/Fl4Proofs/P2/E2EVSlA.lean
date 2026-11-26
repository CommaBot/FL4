/-
P2 (line vlift, gen 4): **syscall_local's accepted run reads only the cut read set** (`AvoidV.acc` for
`sl_localPath`).

`slAccCV`, `fltAccV`, `rrAccV`: `P2/SlAccL.lean`'s `slAccC_of`, `fltAcc_wn`, `rrAcc_wn` with the read set cut to
`SlRV K Locks s` (`P2/E2EVSlW.lean`), word by word, writes unchanged (`SlWN`). New word sources beyond
`E2EVSlW`'s: the ASID table and pool words (`TabNoV`), the IPC-buffer words of the ReplyRecv arm's caller
(user words, `UserObj` [J]). **`sl_accV`**: an accepted run of `syscall.handle_syscall_local` is the same run on
`guard st (SlRV K Locks s) (SlWS s)` (p2sl's `sl_acc` with the cut bundles).

Premises (named arguments): `RegionOKV` / `RegionOKX` [J] (as everywhere), `VcpuKs` (derived, `E2EVHeap`),
`K.ksb + 13568 ≤ 2^64` (P3 `JKern.ksbFit`), `TabNoV` (derived by `tabNoV_of` from `VcpuTabOff` [J] / `PoolObj` [J]),
`HeapOK K.heap` (P1), `VcpuHeap` [J], `UserObj` [J]; the entry facts `SlPreB`, `SlEnt`, `SlHere`, `SlAccIn` as
p2sl's `slPre_of` takes them.
-/
import Fl4Proofs.P2.E2EVSlW
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EV
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
open Fl4Proofs.P2.OwnMap

noncomputable section
open Classical

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayoutV} {Locks : S → U64 → Prop}

theorem cutL {s : S} {W : U64 → Prop} {x : U64} (h : SlRS (st := st) K.toKLayout Locks s x ∧ W x)
    (hv : ¬ VData K x) : SlRV (st := st) K Locks s x ∧ W x :=
  ⟨⟨h.1, hv⟩, h.2⟩

variable {A : Type} (ar : machine.Arch A)
variable {m0 : U64 → U64} {n : I64} {found : U64 × U64}
  {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}

/-- `slAccC_of` for the cut read set. -/
theorem slAccCV (hA : P0.ArchTotal ar) (hK : RegionOKV K) (hX : RegionOKX K.toKLayout) (hks : VcpuKs K)
    (hf : K.ksb.val + 13568 ≤ 2 ^ 64) {s : S}
    (E : SlPreB (st := st) ar K.toKLayout Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (Hh : SlHere (st := st) K.toKLayout Z Scs found s)
    (Ai : SlAccIn (st := st) ar K.toKLayout Locks Z Scs found s) (hTN : TabNoV (L := L) K s)
    {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) :
    SlAccC (L := L) Z (SlRV (st := st) K Locks s) (SlWN (st := st) K.toKLayout Locks s) X := by
  have C := slComV ar hA hK hX hks hf E Hh LP
  obtain ⟨kX, cX, -, -, -, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
  have nX : ∀ o, L.nodeAt X (L.cpu X) o = L.nodeAt s (L.cpu s) o := fun o => by
    rw [cX, nodeAt_of_ksb kX]
  have eRh : L.mem X (rhA (L := L) X) = L.mem s (rhA (L := L) s) := by
    show L.mem X (L.nodeAt X (L.cpu X) layout.node.RELEASE_HEAD) =
      L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD)
    rw [nX]
    exact lp_mem ar hA E.hT E.hN E.hcT LP (nodeAt_aligned E.hN (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD])) (not_slDS_node E.hN E.hT E.hcT (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]))
  have hTN' := hTN
  unfold TabNoV at hTN'
  rw [Hh.ksb] at hTN'
  refine ⟨fun o h1 h2 => by
      rw [nX]
      exact ⟨sv_node hK hX E.hN Hh.ksb Hh.cpu h1 h2, (rs_node hX E.hN Hh.ksb Hh.cpu h1 h2).2,
        nonDec_node hK.base hX E.hN Hh.ksb Hh.cpu h1 h2⟩, C.dt, C.cd, ?_, ?_, C.tm, ?_⟩
  · show SlRV (st := st) K Locks s (core.num.U64.wrapping_add (L.ksb X) layout.ks.KERNEL_ROOT)
    rw [kX]
    exact sv_ks hX hks hf E.hN Hh.ksb (by simp [layout.ks.KERNEL_ROOT]) (by simp [layout.ks.KERNEL_ROOT])
  · intro hi hhi
    rw [kX, Hh.ksb]
    obtain ⟨r0, a0⟩ := hX.asidT hi hhi
    have e0 : L.mem X (atAF K.ksb hi) = L.mem s (atAF K.ksb hi) :=
      lp_mem ar hA E.hT E.hN E.hcT LP a0 (not_slDS_reg hX E.hN E.hT E.hcT E.hSt.1 Hh.ksb Hh.cpu
        (by rw [r0]; intro c h; cases h) (by rw [r0]; intro h; cases h))
    refine ⟨⟨slRS_of_gate a0 (by simp only [own, r0]), (hTN' hi hhi).1⟩, fun lo hlo hne => ?_⟩
    rw [e0] at hne ⊢
    obtain ⟨a1', r1⟩ := Ai.pool hi hhi hne lo hlo
    exact ⟨slRS_of_gate a1' (by simp only [own, r1]), (hTN' hi hhi).2 lo hlo hne⟩
  · intro h
    obtain ⟨h1, h3⟩ := C.rh h
    refine ⟨h1, ?_, h3⟩
    rw [eRh] at h ⊢
    obtain ⟨ht, hs⟩ := Hh.rh h
    have eS : L.mem X (scA (L.mem s (rhA (L := L) s))) = L.mem s (scA (L.mem s (rhA (L := L) s))) :=
      lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ ht 3464#u64 (by simp) (by simp) (by simp)).2.2
        (not_slDS_tcb hX E.hN E.hT E.hcT E.hSt.1 Hh.ksb Hh.cpu ht (by simp) (by simp) (by simp) (by simp))
    rw [eS]
    obtain ⟨hz, -, -, hco⟩ := hs
    exact (sv_scAcc hK hX hz hco).rd

set_option maxHeartbeats 4000000 in
/-- **`fltAcc_wn` for the cut read set.** -/
theorem fltAccV (hA : P0.ArchTotal ar) (hK : RegionOKV K) (hX : RegionOKX K.toKLayout) (hks : VcpuKs K)
    (hf : K.ksb.val + 13568 ≤ 2 ^ 64) {s : S}
    (E : SlPreB (st := st) ar K.toKLayout Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (N : SlEnt (st := st) K.toKLayout Locks found s) (Hh : SlHere (st := st) K.toKLayout Z Scs found s)
    (Ai : SlAccIn (st := st) ar K.toKLayout Locks Z Scs found s) (hTN : TabNoV (L := L) K s) (hS : SlTrap st s)
    {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) {ptr badge dest r : U64}
    (hc : FaultChecks st X (L.curW s) ptr badge dest r) :
    FltAcc (L := L) Z (SlRV (st := st) K Locks s) (SlWN (st := st) K.toKLayout Locks s) X (L.curW s) ptr dest r := by
  have hKb := hK.base
  have I : SlThrIn (st := st) K.toKLayout Locks found.1 s := slThrIn_of hKb hX (preAcc_of ar hX E Hh) E.hSt.1 N
  have C := slAccCV ar hA hK hX hks hf E Hh Ai hTN LP
  obtain ⟨-, -, -, -, ecs, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
  have hc0 := E.hSt.1
  have hs0 := E.hSt.2
  obtain ⟨hep, hlk⟩ := trap_ep ar hA E N I hS LP hc
  obtain ⟨hdt, hds, -, -⟩ := E.hSd hS a X a1 LP hc
  have nT : ∀ {t o : U64}, K.heap t = some .tcb → 192 ≤ o.val → o.val < 4096 → o.val % 8 = 0 →
      o.val ≠ 392 → ¬ SlDS (L := L) s (core.num.U64.wrapping_add t o) := fun ht h1 h2 h3 h4 =>
    not_slDS_tcb hX E.hN E.hT E.hcT hc0 Hh.ksb Hh.cpu ht h1 h2 h3 h4
  obtain ⟨hz, -, -, hco⟩ := Ai.dsc hS a X a1 LP hc
  have eSc : L.mem X (scA dest) = L.mem s (scA dest) :=
    lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ hdt 3464#u64 (by simp) (by simp) (by simp)).2.2
      (nT hdt (by simp) (by simp) (by simp) (by simp))
  obtain ⟨r1, a1h⟩ := hX.epW _ hep layout.ep.HEAD (by simp [layout.ep.HEAD]) (by simp [layout.ep.HEAD])
  obtain ⟨r2, a2h⟩ := hX.epW _ hep layout.ep.TAIL_STATE (by simp [layout.ep.TAIL_STATE])
    (by simp [layout.ep.TAIL_STATE])
  obtain ⟨hrp, hlr⟩ := Ai.frp hS a X a1 LP hc
  obtain ⟨r3, a3h⟩ := hX.rpW _ hrp layout.reply.TCB (by simp [layout.reply.TCB]) (by simp [layout.reply.TCB])
  exact
  { nd := C.nd
    dt := C.dt
    cd := C.cd
    kr := C.kr
    tab := C.tab
    fh := fun sl hsl => by
      rw [tcb_slot_val] at hsl
      obtain rfl := ok_inj_ff hsl
      exact sv_tslot hK hX hc0 (by simp [layout.tcb.SLOT_FAULT_HANDLER])
    eph := cutL (slRWN_of_lock hKb a1h r1 hlk) (nv_obj hK r1)
    ept := cutL (slRWN_of_lock hKb a2h r2 hlk) (nv_obj hK r2)
    tf := fun o ho => cutL (rwn_tcb hKb hX hc0 (by omega) (by omega) (by omega) (by simp only [GateField]; omega)
      (by simp only [TimerField]; omega) hs0 (by omega)) (nv_tcb hK hX hc0 (by omega) (by omega) (by omega))
    treg := fun _ hr => sv_regs hK hX hc0 hs0 hr
    trp := (rwn_tcb hKb hX hc0 (o := 3360#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) hs0 (by simp)).2
    drp := sv_tcbSafe hK hX hdt (o := 3360#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) hds
    daf := sv_tcbGate hK hX hdt (o := 3520#u64) (by simp) (by simp) (by simp) (by simp [GateField])
    ddo := sv_tcbGate hK hX hdt (o := 3432#u64) (by simp) (by simp) (by simp) (by simp [GateField])
    dsc0 := sv_tcbGate hK hX hdt (o := 3464#u64) (by simp) (by simp) (by simp) (by simp [GateField])
    diq := sv_tcbSafe hK hX hdt (o := 3592#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) hds
    dpr := sv_tcbGate hK hX hdt (o := 3448#u64) (by simp) (by simp) (by simp) (by simp [GateField])
    dyt := sv_tcbSafe hK hX hdt (o := 3472#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) hds
    dst := by
      rw [stA_eq]
      exact sv_tcbSafe hK hX hdt (o := 3328#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField]) hds
    dfi := sv_regs hK hX hdt hds (r := layout.reg.FAULT_IP) (by simp [layout.reg.FAULT_IP])
    den := sv_tcbSafe hK hX hdt (o := 3496#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) hds
    dib := sv_tcbGate hK hX hdt (o := 3512#u64) (by simp) (by simp) (by simp) (by simp [GateField])
    dvt := by
      rw [vtA_slot]
      exact sv_tslot hK hX hdt (by simp [layout.tcb.SLOT_VTABLE])
    dbs := fun sl hsl => by
      rw [tcb_slot_val] at hsl
      obtain rfl := ok_inj_ff hsl
      exact sv_tslot hK hX hdt (by simp [layout.tcb.SLOT_BUFFER])
    dw := ⟨(rwn_tcb hKb hX hdt (o := 3496#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField]) hds (by simp)).2,
      (rwn_tcb hKb hX hdt (o := 3504#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField]) hds (by simp)).2,
      (rwn_tcb hKb hX hdt (o := 3480#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField]) hds (by simp)).2,
      (rwn_tcb hKb hX hdt (o := 3488#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField]) hds (by simp)).2⟩
    dreg := fun _ hr => (regs_wn hKb hX hdt hds hr).2
    nxt := fun hne => by
      obtain ⟨hnt, hq, hb⟩ := Ai.nq hS a X a1 LP hc hne
      have eSt : L.mem X (stA (L.mem X (nextA .Ep dest))) = L.mem s (stA (L.mem X (nextA .Ep dest))) := by
        rw [stA_eq]
        exact lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ hnt 3328#u64 (by simp) (by simp) (by simp)).2.2
          (nT hnt (by simp) (by simp) (by simp) (by simp))
      have eBl : L.mem X (blockA (L.mem X (nextA .Ep dest))) = L.mem s (blockA (L.mem X (nextA .Ep dest))) :=
        lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ hnt 3336#u64 (by simp) (by simp) (by simp)).2.2
          (nT hnt (by simp) (by simp) (by simp) (by simp))
      rw [eSt] at hq
      rw [eBl] at hb
      exact ⟨(rw_tcb_q hX hnt (o := 3504#u64) (by simp) (by simp) (by simp) (by simp [GField]) hq
        (by rw [hb]; exact hlk)).2, nonDec_tcb hKb hX hnt (o := 3504#u64) (by simp) (by simp) (by simp) (by simp)⟩
    buf := fun rb hrb hne i hi => ⟨(slRW_of_user (Ai.fbuf hS a X a1 LP hc rb hrb hne i hi)).2,
      nonDec_user hKb hX (Ai.fbuf hS a X a1 LP hc rb hrb hne i hi)⟩
    rt := (slRWN_of_lock hKb a3h r3 hlr).2
    spo := by
      rw [eSc]
      obtain ⟨-, am, hin, -⟩ := sc_off hX hz (o := layout.sc.SPORADIC) (by simp [layout.sc.SPORADIC])
        (by simp [layout.sc.SPORADIC])
      exact (sv_scAcc hK hX hz hco).rd _ am hin
    dsc := by
      rw [eSc]
      exact sv_scAccWN hK hX hz hco
    csc := by
      rw [ecs]
      obtain ⟨hz', -, -, hco'⟩ := Hh.cs
      exact sv_scAccWN hK hX hz' hco'
    tm := C.tm
    rh := C.rh }

set_option maxHeartbeats 4000000 in
/-- **`rrAcc_wn` for the cut read set.** -/
theorem rrAccV (hA : P0.ArchTotal ar) (hK : RegionOKV K) (hX : RegionOKX K.toKLayout) (hks : VcpuKs K)
    (hf : K.ksb.val + 13568 ≤ 2 ^ 64) (hH : HeapOK K.heap) (hV : VcpuHeap K) (hUo : UserObj K) {s : S}
    (E : SlPreB (st := st) ar K.toKLayout Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (N : SlEnt (st := st) K.toKLayout Locks found s) (Hh : SlHere (st := st) K.toKLayout Z Scs found s)
    (Ai : SlAccIn (st := st) ar K.toKLayout Locks Z Scs found s) (hTN : TabNoV (L := L) K s) (hS : ¬ SlTrap st s)
    {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) {u usc : U64}
    (hc : RRChecks st ar X a1 (L.curW s) found.1 found.2 u usc) :
    RrAcc (L := L) Z (SlRV (st := st) K Locks s) (SlWN (st := st) K.toKLayout Locks s) X (L.curW s) found.1 found.2
      u usc := by
  have hKb := hK.base
  have I : SlThrIn (st := st) K.toKLayout Locks found.1 s := slThrIn_of hKb hX (preAcc_of ar hX E Hh) E.hSt.1 N
  have C := slAccCV ar hA hK hX hks hf E Hh Ai hTN LP
  have D := (slDecInV ar hA hK hX hks hf E N Hh).rT hS a X a1 LP
  obtain ⟨-, cX, -, -, ecs, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
  have hc0 := E.hSt.1
  have hs0 := E.hSt.2
  obtain ⟨hut, hus, -, -, -⟩ := E.hSu hS a X a1 LP u usc hc
  have nT : ∀ {t o : U64}, K.heap t = some .tcb → 192 ≤ o.val → o.val < 4096 → o.val % 8 = 0 →
      o.val ≠ 392 → ¬ SlDS (L := L) s (core.num.U64.wrapping_add t o) := fun ht h1 h2 h3 h4 =>
    not_slDS_tcb hX E.hN E.hT E.hcT hc0 Hh.ksb Hh.cpu ht h1 h2 h3 h4
  have eu : u = slThr st found.1 s := by
    have h1 := obj.Reply.tcb.blk (st := st) X found.1
    rw [hc.tcb, WP.spec_ok, slThr_hd_rr ar hA E.hT E.hN E.hcT I hS LP] at h1
    exact h1
  have lv : SlLive st found.1 s := slLive_rr (st := st) hS (by rw [← eu]; exact u_ne0 hc.u0)
  have haf : L.mem s (affA (slThr st found.1 s)) = L.cpu s := by rw [← eu, affA_fld]; exact hus.1
  have eusc : usc = L.mem s (scA u) := by
    have h1 := hc.sc
    rw [tcb_sc_ok] at h1
    rw [← ok_inj_ff h1]
    exact lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ hut 3464#u64 (by simp) (by simp) (by simp)).2.2
      (nT hut (by simp) (by simp) (by simp) (by simp))
  have husc0 : usc ≠ 0#u64 := by
    obtain ⟨b, hb, hn⟩ := hc.sc0
    rw [eq_of_spec_fd (obj.Sc.is_null.spec usc)] at hb
    rw [← ok_inj_ff hb] at hn
    simpa using hn
  have Hs := Hh.usc hS lv haf (by rw [← eu, ← eusc]; exact husc0)
  rw [← eu, ← eusc] at Hs
  obtain ⟨hz, hin0, hmx0, hco⟩ := Hs
  have hrp := N.hrp hS
  have hlr := N.lrp hS
  obtain ⟨rt1, rta⟩ := hX.rpW _ hrp layout.reply.TCB (by simp [layout.reply.TCB]) (by simp [layout.reply.TCB])
  obtain ⟨rn1, rna⟩ := hX.rpW _ hrp layout.reply.NEXT (by simp [layout.reply.NEXT]) (by simp [layout.reply.NEXT])
  obtain ⟨rp1, rpa⟩ := hX.rpW _ hrp layout.reply.PREV (by simp [layout.reply.PREV]) (by simp [layout.reply.PREV])
  obtain ⟨eh1, eha⟩ := hX.epW _ (Hh.ep hS) layout.ep.HEAD (by simp [layout.ep.HEAD]) (by simp [layout.ep.HEAD])
  obtain ⟨et1, eta⟩ := hX.epW _ (Hh.ep hS) layout.ep.TAIL_STATE (by simp [layout.ep.TAIL_STATE])
    (by simp [layout.ep.TAIL_STATE])
  obtain ⟨-, aC, hinC, rC⟩ := sc_off hX hz (o := layout.sc.CORE) (by simp [layout.sc.CORE]) (by simp [layout.sc.CORE])
  have eC : L.mem X (core.num.U64.wrapping_add usc layout.sc.CORE) = L.cpu X := by
    rw [lp_mem ar hA E.hT E.hN E.hcT LP aC (not_slDS_reg hX E.hN E.hT E.hcT hc0 Hh.ksb Hh.cpu
      (by rw [rC]; intro c h; cases h) (by rw [rC]; intro h; cases h)), cX]
    have e : core.num.U64.wrapping_add usc layout.sc.CORE = fld usc 16#u64 := by simp [fld, layout.sc.CORE]
    rw [e]
    exact hco
  exact
  { nd := C.nd
    dt := C.dt
    cd := C.cd
    kr := C.kr
    tab := C.tab
    tSt := D.tSt
    tSc := D.tSc
    tMx := D.tMx
    tIq := D.tIq
    tMi := D.tMi
    tBn := D.tBn
    tPr := D.tPr
    tReg := fun _ hr => sv_regs hK hX hc0 hs0 hr
    tBuf := ⟨_, tcb_slot_val _ _, sv_tcbGate hK hX hc0 (o := 3512#u64) (by simp) (by simp) (by simp)
      (by simp [GateField]), (sv_tslot hK hX hc0 (by simp [layout.tcb.SLOT_BUFFER])).1,
      (sv_tslot hK hX hc0 (by simp [layout.tcb.SLOT_BUFFER])).2⟩
    tBw := fun buf hb hne i hi => sv_user hH hV hUo (Ai.rbuf hS a X a1 LP buf hb hne i hi)
    ntf := D.ntf
    wRp := (rwn_tcb hKb hX hc0 (o := 3360#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) hs0 (by simp)).2
    wEn := (rwn_tcb hKb hX hc0 (o := 3496#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) hs0 (by simp)).2
    wEp := (rwn_tcb hKb hX hc0 (o := 3504#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) hs0 (by simp)).2
    rRt := D.rRt
    rNx := D.rNx
    rPv := sv_lock hK rpa rp1 hlr
    wNx := (slRWN_of_lock hKb rna rn1 hlr).2
    wPv := (slRWN_of_lock hKb rpa rp1 hlr).2
    wRt := (slRWN_of_lock hKb rta rt1 hlr).2
    uSt := by
      rw [stA_eq]
      exact sv_tcbSafe hK hX hut (o := 3328#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField]) hus
    uFt := cutL (rwn_tcb hKb hX hut (o := 3376#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) hus (by simp)) (nv_tcb hK hX hut (o := 3376#u64) (by simp) (by simp) (by simp))
    uSc := sv_tcbGate hK hX hut (o := 3464#u64) (by simp) (by simp) (by simp) (by simp [GateField])
    uPr := sv_tcbGate hK hX hut (o := 3448#u64) (by simp) (by simp) (by simp) (by simp [GateField])
    uAf := sv_tcbGate hK hX hut (o := 3520#u64) (by simp) (by simp) (by simp) (by simp [GateField])
    uDo := sv_tcbGate hK hX hut (o := 3432#u64) (by simp) (by simp) (by simp) (by simp [GateField])
    uIq := sv_tcbSafe hK hX hut (o := 3592#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) hus
    uMx := by
      obtain ⟨-, am, hin, -⟩ := sc_off hX hz (o := layout.sc.REFILL_MAX) (by simp [layout.sc.REFILL_MAX])
        (by simp [layout.sc.REFILL_MAX])
      exact (sv_scAcc hK hX hz hco).rd _ am hin
    uReg := fun _ hr => (regs_wn hKb hX hut hus hr).2
    uYt := sv_tcbSafe hK hX hut (o := 3472#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) hus
    uFi := sv_regs hK hX hut hus (r := layout.reg.FAULT_IP) (by simp [layout.reg.FAULT_IP])
    uVt := by
      rw [vtA_slot]
      exact sv_tslot hK hX hut (by simp [layout.tcb.SLOT_VTABLE])
    eTS := D.eTS
    wEh := (slRWN_of_lock hKb eha eh1 (E.hlk hS)).2
    wEt := (slRWN_of_lock hKb eta et1 (E.hlk hS)).2
    spo := by
      obtain ⟨-, am, hin, -⟩ := sc_off hX hz (o := layout.sc.SPORADIC) (by simp [layout.sc.SPORADIC])
        (by simp [layout.sc.SPORADIC])
      exact (sv_scAcc hK hX hz hco).rd _ am hin
    cor := (sv_scAcc hK hX hz hco).rd _ aC hinC
    ccs := by
      rw [eC]
      exact (C.nd _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])).1
    uHd := rdHead_hereV ar hA hK hX E Hh LP ⟨hz, hin0, hmx0, hco⟩
    uscA := sv_scAccWN hK hX hz hco
    csc := by
      rw [ecs]
      obtain ⟨hz', -, -, hco'⟩ := Hh.cs
      exact sv_scAccWN hK hX hz' hco'
    tm := C.tm
    rh := C.rh }

/-- **`AvoidV.acc` for syscall_local**: an accepted run is the same run on `guard st (SlRV K Locks s) (SlWS s)`
(p2sl's `sl_acc` with the cut bundles). -/
theorem sl_accV (hA : P0.ArchTotal ar) (hK : RegionOKV K) (hX : RegionOKX K.toKLayout) (hks : VcpuKs K)
    (hf : K.ksb.val + 13568 ≤ 2 ^ 64) (hH : HeapOK K.heap) (hV : VcpuHeap K) (hUo : UserObj K) {s s1 : S}
    {a a1 : A}
    (E : SlPreB (st := st) ar K.toKLayout Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (N : SlEnt (st := st) K.toKLayout Locks found s) (Hh : SlHere (st := st) K.toKLayout Z Scs found s)
    (Ai : SlAccIn (st := st) ar K.toKLayout Locks Z Scs found s) (hTN : TabNoV (L := L) K s)
    (h : syscall.handle_syscall_local st ar s a n found = ok (true, s1, a1)) :
    syscall.handle_syscall_local (guard st (SlRV (st := st) K Locks s) (SlWS (st := st) K.toKLayout Locks s))
      ar s a n found = ok (true, s1, a1) := by
  exact syscall.handle_syscall_local.guard_acc
    (gS := guard st (SlRV (st := st) K Locks s) (SlWS (st := st) K.toKLayout Locks s))
    (R := SlRV (st := st) K Locks s) (W := SlWS (st := st) K.toKLayout Locks s) ar hA E.hT E.hN E.hcT
    (preAccV ar hK hX E Hh) (fun X a1 csc LP hcs => hhdV ar hA hK hX E Hh LP hcs) (E.hI a) (E.hAs a)
    (fun h' => E.hrecv h' a) (fun h' => E.hF h' a) (fun h' => E.hy0f h' a) (fun h' => E.hTm h' a)
    (fun h' X a1 LP {_p _b _d _r} hc => (fltAccV ar hA hK hX hks hf E N Hh Ai hTN h' LP hc).wmono (fun _ h => h.1))
    (fun h' X a1 hP {_p _b _d _r} hc =>
      ⟨SWr.of_W (W := SlWS (st := st) K.toKLayout Locks s) (E.hSd h' a X a1 hP hc).2.2.1,
        fun _ _ => SWr.of_W (W := SlWS (st := st) K.toKLayout Locks s) (E.hSd h' a X a1 hP hc).2.2.2⟩)
    (fun h' => E.hPl h' a) (fun h' => E.hrz h' a) (fun h' => E.hy0r h' a)
    (fun h' X a1 LP u usc hc => (rrAccV ar hA hK hX hks hf hH hV hUo E N Hh Ai hTN h' LP hc).wmono (fun _ h => h.1))
    (fun h' X a1 hP u usc hc =>
      have hw := E.hSu h' a X a1 hP u usc hc
      { tR := SWr.of_W (W := SlWS (st := st) K.toKLayout Locks s) hw.2.2.1
        tN := SWr.of_W (W := SlWS (st := st) K.toKLayout Locks s) hw.2.2.1
        tB := fun _ _ => gst_write (W := SlWS (st := st) K.toKLayout Locks s) hw.2.2.1
        bl := fun _ => gst_write (W := SlWS (st := st) K.toKLayout Locks s) hw.2.2.2.1
        uI := SWr.of_W (W := SlWS (st := st) K.toKLayout Locks s) hw.2.2.2.2
        uR := SWr.of_W (W := SlWS (st := st) K.toKLayout Locks s) hw.2.2.2.2
        uN := SWr.of_W (W := SlWS (st := st) K.toKLayout Locks s) hw.2.2.2.2 })
    h

end

end
end Fl4Proofs.P2.E2EV
