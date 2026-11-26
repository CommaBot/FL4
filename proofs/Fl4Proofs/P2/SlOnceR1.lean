/-
# P2 (line slhuf, gen 7): the accepted ReplyRecv arm's words, without the IPC buffer, at `NU K`

Toward `SlRROnce` (P2/SlOnce.lean): an accepted ReplyRecv run reads the handler's IPC buffer (user words) and
otherwise only kernel words. `RrAccNB` is `RrAcc` without `tBw` (the buffer words); every remaining word is
shown not a user word (**`rrAccNB_nu`**, the ReplyRecv analogue of `fltAcc_nuT`), so the run outside
`copy_mrs_fault_reply_loop1` can be guarded on `SlRS s ∧ NU K` / `SlWS s ∧ NU K` (`RrAccNB.meet`).

No premises beyond the entry facts (`SlOF`).
-/
import Fl4Proofs.P2.SlOnce
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap Fl4Proofs.P0.Consts
open Fl4Proofs.P2.E2E (Once)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- `RrAcc` without the buffer words (`tBw`). -/
structure RrAccNB (Z : U64 → Nat) (R W : U64 → Prop) (X0 : S) (t rptr ep u usc : U64) : Prop where
  nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt X0 (L.cpu X0) o) ∧ W (L.nodeAt X0 (L.cpu X0) o)
  dt : R (core.num.U64.wrapping_add (L.ksb X0) layout.ks.DOMAIN_TIME)
  cd : R (core.num.U64.wrapping_add (L.ksb X0) layout.ks.CUR_DOMAIN)
  kr : R (krA (L := L) X0)
  tab : RdTab (L := L) R X0
  tSt : R (stA t)
  tSc : R (scA t)
  tMx : R (maxA (L.mem X0 (scA t)))
  tIq : R (inqA t)
  tMi : R (regA t layout.reg.MSG_INFO)
  tBn : R (core.num.U64.wrapping_add t 3368#u64)
  tPr : R (prioA t)
  tReg : Regs R t
  tBuf : RdBuf R t
  ntf : ∀ n, obj.Tcb.bound_ntfn st t X0 = ok n → (n != 0#u64) = true →
    R (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE) ∧ R (core.num.U64.wrapping_add n layout.ntfn.SC)
  wRp : W (replyA t)
  wEn : W (nextA .Ep t)
  wEp : W (prevA .Ep t)
  rRt : R (rTcbA rptr)
  rNx : R (rNextA rptr)
  rPv : R (rPrevA rptr)
  wNx : W (rNextA rptr)
  wPv : W (rPrevA rptr)
  wRt : W (rTcbA rptr)
  uSt : R (stA u)
  uFt : R (core.num.U64.wrapping_add u 3376#u64) ∧ W (core.num.U64.wrapping_add u 3376#u64)
  uSc : R (scA u)
  uPr : R (prioA u)
  uAf : R (affA u)
  uDo : R (core.num.U64.wrapping_add u 3432#u64)
  uIq : R (inqA u)
  uMx : R (maxA usc)
  uReg : Regs W u
  uYt : R (yieldA u)
  uFi : R (regA u layout.reg.FAULT_IP)
  uVt : R (vtA u) ∧ R (core.num.U64.wrapping_add (vtA u) 8#u64)
  eTS : R (epTSA ep)
  wEh : W (epHeadA ep)
  wEt : W (epTSA ep)
  spo : R (sporA usc)
  cor : R (core.num.U64.wrapping_add usc layout.sc.CORE)
  ccs : R (L.nodeAt X0 (L.mem X0 (core.num.U64.wrapping_add usc layout.sc.CORE)) layout.node.CUR_SC)
  uHd : RdHead (L := L) R X0 usc
  uscA : ScAcc R W usc (Z usc)
  csc : ScAcc R W (L.cscW X0) (Z (L.cscW X0))
  tm : L.mem X0 (tmA (L := L) X0) ≠ 0#u64 → R (core.num.U64.wrapping_add (L.mem X0 (tmA (L := L) X0)) 3528#u64)
  rh : L.mem X0 (rhA (L := L) X0) ≠ 0#u64 → R (scA (L.mem X0 (rhA (L := L) X0))) ∧
    (∀ b, Aligned b → InSC (L.mem X0 (scA (L.mem X0 (rhA (L := L) X0)))) (Z (L.mem X0 (scA (L.mem X0 (rhA (L := L) X0))))) b →
      R b) ∧
    RdHead (L := L) R X0 (L.mem X0 (scA (L.mem X0 (rhA (L := L) X0))))

theorem RrAcc.toNB {Z : U64 → Nat} {R W : U64 → Prop} {X0 : S} {t rptr ep u usc : U64}
    (K : RrAcc (L := L) Z R W X0 t rptr ep u usc) : RrAccNB (L := L) Z R W X0 t rptr ep u usc :=
  ⟨K.nd, K.dt, K.cd, K.kr, K.tab, K.tSt, K.tSc, K.tMx, K.tIq, K.tMi, K.tBn, K.tPr, K.tReg, K.tBuf, K.ntf,
    K.wRp, K.wEn, K.wEp, K.rRt, K.rNx, K.rPv, K.wNx, K.wPv, K.wRt, K.uSt, K.uFt, K.uSc, K.uPr, K.uAf, K.uDo,
    K.uIq, K.uMx, K.uReg, K.uYt, K.uFi, K.uVt, K.eTS, K.wEh, K.wEt, K.spo, K.cor, K.ccs, K.uHd, K.uscA, K.csc,
    K.tm, K.rh⟩

theorem ScAcc.meet {R1 W1 R2 W2 : U64 → Prop} {sc : U64} {sb : Nat} (K1 : ScAcc R1 W1 sc sb)
    (K2 : ScAcc R2 W2 sc sb) : ScAcc (fun q => R1 q ∧ R2 q) (fun q => W1 q ∧ W2 q) sc sb :=
  ⟨fun b ha hb => ⟨K1.rd b ha hb, K2.rd b ha hb⟩, fun b ha hb => ⟨K1.wr b ha hb, K2.wr b ha hb⟩,
    ⟨K1.cons, K2.cons⟩⟩

theorem RrAccNB.meet {Z : U64 → Nat} {R1 W1 R2 W2 : U64 → Prop} {X0 : S} {t rptr ep u usc : U64}
    (K1 : RrAccNB (L := L) Z R1 W1 X0 t rptr ep u usc) (K2 : RrAccNB (L := L) Z R2 W2 X0 t rptr ep u usc) :
    RrAccNB (L := L) Z (fun q => R1 q ∧ R2 q) (fun q => W1 q ∧ W2 q) X0 t rptr ep u usc where
  nd o h1 h2 := ⟨⟨(K1.nd o h1 h2).1, (K2.nd o h1 h2).1⟩, ⟨(K1.nd o h1 h2).2, (K2.nd o h1 h2).2⟩⟩
  dt := ⟨K1.dt, K2.dt⟩
  cd := ⟨K1.cd, K2.cd⟩
  kr := ⟨K1.kr, K2.kr⟩
  tab hi hhi := ⟨⟨(K1.tab hi hhi).1, (K2.tab hi hhi).1⟩, fun lo hlo hne =>
    ⟨(K1.tab hi hhi).2 lo hlo hne, (K2.tab hi hhi).2 lo hlo hne⟩⟩
  tSt := ⟨K1.tSt, K2.tSt⟩
  tSc := ⟨K1.tSc, K2.tSc⟩
  tMx := ⟨K1.tMx, K2.tMx⟩
  tIq := ⟨K1.tIq, K2.tIq⟩
  tMi := ⟨K1.tMi, K2.tMi⟩
  tBn := ⟨K1.tBn, K2.tBn⟩
  tPr := ⟨K1.tPr, K2.tPr⟩
  tReg r hr := ⟨K1.tReg r hr, K2.tReg r hr⟩
  tBuf := by
    obtain ⟨sl, h1, h2, h3, h4⟩ := K1.tBuf
    obtain ⟨sl', h1', h2', h3', h4'⟩ := K2.tBuf
    rw [h1] at h1'
    obtain rfl := ok_inj_ff h1'
    exact ⟨sl, h1, ⟨h2, h2'⟩, ⟨h3, h3'⟩, ⟨h4, h4'⟩⟩
  ntf n h1 h2 := ⟨⟨(K1.ntf n h1 h2).1, (K2.ntf n h1 h2).1⟩, ⟨(K1.ntf n h1 h2).2, (K2.ntf n h1 h2).2⟩⟩
  wRp := ⟨K1.wRp, K2.wRp⟩
  wEn := ⟨K1.wEn, K2.wEn⟩
  wEp := ⟨K1.wEp, K2.wEp⟩
  rRt := ⟨K1.rRt, K2.rRt⟩
  rNx := ⟨K1.rNx, K2.rNx⟩
  rPv := ⟨K1.rPv, K2.rPv⟩
  wNx := ⟨K1.wNx, K2.wNx⟩
  wPv := ⟨K1.wPv, K2.wPv⟩
  wRt := ⟨K1.wRt, K2.wRt⟩
  uSt := ⟨K1.uSt, K2.uSt⟩
  uFt := ⟨⟨K1.uFt.1, K2.uFt.1⟩, ⟨K1.uFt.2, K2.uFt.2⟩⟩
  uSc := ⟨K1.uSc, K2.uSc⟩
  uPr := ⟨K1.uPr, K2.uPr⟩
  uAf := ⟨K1.uAf, K2.uAf⟩
  uDo := ⟨K1.uDo, K2.uDo⟩
  uIq := ⟨K1.uIq, K2.uIq⟩
  uMx := ⟨K1.uMx, K2.uMx⟩
  uReg r hr := ⟨K1.uReg r hr, K2.uReg r hr⟩
  uYt := ⟨K1.uYt, K2.uYt⟩
  uFi := ⟨K1.uFi, K2.uFi⟩
  uVt := ⟨⟨K1.uVt.1, K2.uVt.1⟩, ⟨K1.uVt.2, K2.uVt.2⟩⟩
  eTS := ⟨K1.eTS, K2.eTS⟩
  wEh := ⟨K1.wEh, K2.wEh⟩
  wEt := ⟨K1.wEt, K2.wEt⟩
  spo := ⟨K1.spo, K2.spo⟩
  cor := ⟨K1.cor, K2.cor⟩
  ccs := ⟨K1.ccs, K2.ccs⟩
  uHd := RdHead.meet K1.uHd K2.uHd
  uscA := ScAcc.meet K1.uscA K2.uscA
  csc := ScAcc.meet K1.csc K2.csc
  tm h := ⟨K1.tm h, K2.tm h⟩
  rh h := ⟨⟨(K1.rh h).1, (K2.rh h).1⟩, fun b ha hb => ⟨(K1.rh h).2.1 b ha hb, (K2.rh h).2.1 b ha hb⟩,
    RdHead.meet (K1.rh h).2.2 (K2.rh h).2.2⟩

variable {K : KLayout}

/-- An SC's words, read and written, are `NU`. -/
theorem scAccNN (hX : RegionOKX K) {sc : U64} {z : Nat} (hz : K.heap sc = some (.sc z)) :
    ScAcc (NU K) (NU K) sc z := by
  refine ⟨fun b ha hb => nu_sc hX hz ha hb, fun b ha hb => nu_sc hX hz ha hb.inSC, ?_⟩
  obtain ⟨-, am, hin, -⟩ := sc_off hX hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
    (by simp [layout.sc.CONSUMED])
  exact nu_sc hX hz am hin

variable {A : Type} (ar : machine.Arch A)
variable {Locks : S → U64 → Prop} {m0 : U64 → U64} {n : I64} {found : U64 × U64} {Cs Ω Sg Ac : Set U64}

set_option maxHeartbeats 4000000 in
/-- **The accepted ReplyRecv arm's words (but the buffer's) are `NU`** (`rrAcc_wn` with `NU` facts). -/
theorem rrAccNB_nu (hA : P0.ArchTotal ar) {s : S} (F : SlOF (st := st) ar K Locks m0 n found Cs Ω Sg Ac s)
    (hS : ¬ SlTrap st s) {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) {u usc : U64}
    (hc : RRChecks st ar X a1 (L.curW s) found.1 found.2 u usc) :
    RrAccNB (L := L) K.heap.scBits (NU K) (NU K) X (L.curW s) found.1 found.2 u usc := by
  have B := F.B
  have E := F.E
  have Hh := F.Hh
  have N := F.N
  have I := F.I
  have hK := B.regionOK
  have hX := B.regionOKX
  have C := slCom_nu ar hA B E LP
  have D' := rrDR_nu ar hA B E F.C hS LP
  obtain ⟨kX, cX, -, -, ecs, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
  have hc0 := E.hSt.1
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
  have hepH := Hh.ep hS
  obtain ⟨-, aC, hinC, rC⟩ := sc_off hX hz (o := layout.sc.CORE) (by simp [layout.sc.CORE]) (by simp [layout.sc.CORE])
  have eC : L.mem X (core.num.U64.wrapping_add usc layout.sc.CORE) = L.cpu X := by
    rw [lp_mem ar hA E.hT E.hN E.hcT LP aC (not_slDS_reg hX E.hN E.hT E.hcT hc0 Hh.ksb Hh.cpu
      (by rw [rC]; intro c h; cases h) (by rw [rC]; intro h; cases h)), cX]
    have e : core.num.U64.wrapping_add usc layout.sc.CORE = fld usc 16#u64 := by simp [fld, layout.sc.CORE]
    rw [e]
    exact hco
  obtain ⟨hzc, -, -, -⟩ := Hh.csc hS
  have eSt : L.mem X (scA (L.curW s)) = L.mem s (scA (L.curW s)) := by
    obtain ⟨-, -, aT, -, -, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
    exact aT _ E.hcT 3464#u64 (by simp) (by simp) (by simp)
  have nX : ∀ o, L.nodeAt X (L.cpu X) o = L.nodeAt s (L.cpu s) o := fun o => by
    rw [cX, nodeAt_of_ksb kX]
  have eRh : L.mem X (rhA (L := L) X) = L.mem s (rhA (L := L) s) := by
    show L.mem X (L.nodeAt X (L.cpu X) layout.node.RELEASE_HEAD) =
      L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD)
    rw [nX]
    exact lp_mem ar hA E.hT E.hN E.hcT LP (nodeAt_aligned E.hN (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD])) (not_slDS_node E.hN E.hT E.hcT (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]))
  have tw : ∀ y, K.heap y = some .tcb → ∀ o : U64, 192 ≤ o.val → o.val < 4096 → o.val % 8 = 0 →
      NU K (core.num.U64.wrapping_add y o) := fun y hy o h1 h2 h3 => nu_tcb hX hy h1 h2 h3
  have sw : ∀ {o : U64}, o.val < 256 → o.val % 8 = 0 → NU K (core.num.U64.wrapping_add usc o) := by
    intro o h1 h2
    obtain ⟨-, am, hin, -⟩ := sc_off hX hz (o := o) h1 h2
    exact nu_sc hX hz am hin
  exact
  { nd := fun o h1 h2 => ⟨C.nd o h1 h2, C.nd o h1 h2⟩
    dt := C.dt
    cd := C.cd
    kr := by
      show NU K (core.num.U64.wrapping_add (L.ksb X) layout.ks.KERNEL_ROOT)
      rw [kX]
      exact B.nuKs E.hN (by simp [layout.ks.KERNEL_ROOT]) (by simp [layout.ks.KERNEL_ROOT])
    tab := rdTabN ar hA B E Hh LP
    tSt := D'.tSt
    tSc := D'.tSc
    tMx := by
      rw [eSt]
      exact nu_scw hX hzc (o := layout.sc.REFILL_MAX) (by simp [layout.sc.REFILL_MAX])
        (by simp [layout.sc.REFILL_MAX])
    tIq := D'.tIq
    tMi := D'.tMi
    tBn := D'.tBn
    tPr := D'.tPr
    tReg := nuRegs hX hc0
    tBuf := ⟨_, tcb_slot_val _ _, tw _ hc0 3512#u64 (by simp) (by simp) (by simp),
      (nu_tslot hK hX hc0 (by simp [layout.tcb.SLOT_BUFFER])).1, (nu_tslot hK hX hc0 (by simp [layout.tcb.SLOT_BUFFER])).2⟩
    ntf := fun nt hnt hne => by
      have e1 := (eq_of_spec_fd (obj.Tcb.bound_ntfn.val X (L.curW s))).symm.trans hnt
      have en : nt = L.mem X (boundA (L.curW s)) := (ok_inj_ff e1).symm
      subst en
      exact D'.ntf (fun h0 => by rw [h0] at hne; simp at hne)
    wRp := tw _ hc0 3360#u64 (by simp) (by simp) (by simp)
    wEn := tw _ hc0 3496#u64 (by simp) (by simp) (by simp)
    wEp := tw _ hc0 3504#u64 (by simp) (by simp) (by simp)
    rRt := nu_rp hX hrp (o := layout.reply.TCB) (by simp [layout.reply.TCB]) (by simp [layout.reply.TCB])
    rNx := nu_rp hX hrp (o := layout.reply.NEXT) (by simp [layout.reply.NEXT]) (by simp [layout.reply.NEXT])
    rPv := nu_rp hX hrp (o := layout.reply.PREV) (by simp [layout.reply.PREV]) (by simp [layout.reply.PREV])
    wNx := nu_rp hX hrp (o := layout.reply.NEXT) (by simp [layout.reply.NEXT]) (by simp [layout.reply.NEXT])
    wPv := nu_rp hX hrp (o := layout.reply.PREV) (by simp [layout.reply.PREV]) (by simp [layout.reply.PREV])
    wRt := nu_rp hX hrp (o := layout.reply.TCB) (by simp [layout.reply.TCB]) (by simp [layout.reply.TCB])
    uSt := by rw [stA_eq]; exact tw _ hut 3328#u64 (by simp) (by simp) (by simp)
    uFt := ⟨tw _ hut 3376#u64 (by simp) (by simp) (by simp), tw _ hut 3376#u64 (by simp) (by simp) (by simp)⟩
    uSc := tw _ hut 3464#u64 (by simp) (by simp) (by simp)
    uPr := tw _ hut 3448#u64 (by simp) (by simp) (by simp)
    uAf := tw _ hut 3520#u64 (by simp) (by simp) (by simp)
    uDo := tw _ hut 3432#u64 (by simp) (by simp) (by simp)
    uIq := tw _ hut 3592#u64 (by simp) (by simp) (by simp)
    uMx := by
      obtain ⟨-, am, hin, -⟩ := sc_off hX hz (o := layout.sc.REFILL_MAX) (by simp [layout.sc.REFILL_MAX])
        (by simp [layout.sc.REFILL_MAX])
      exact nu_sc hX hz am hin
    uReg := nuRegs hX hut
    uYt := tw _ hut 3472#u64 (by simp) (by simp) (by simp)
    uFi := nuReg hX hut (r := layout.reg.FAULT_IP) (by simp [layout.reg.FAULT_IP])
    uVt := by
      rw [vtA_slot]
      exact nu_tslot hK hX hut (by simp [layout.tcb.SLOT_VTABLE])
    eTS := nu_ep hX hepH (o := layout.ep.TAIL_STATE) (by simp [layout.ep.TAIL_STATE]) (by simp [layout.ep.TAIL_STATE])
    wEh := nu_ep hX hepH (o := layout.ep.HEAD) (by simp [layout.ep.HEAD]) (by simp [layout.ep.HEAD])
    wEt := nu_ep hX hepH (o := layout.ep.TAIL_STATE) (by simp [layout.ep.TAIL_STATE]) (by simp [layout.ep.TAIL_STATE])
    spo := by
      obtain ⟨-, am, hin, -⟩ := sc_off hX hz (o := layout.sc.SPORADIC) (by simp [layout.sc.SPORADIC])
        (by simp [layout.sc.SPORADIC])
      exact nu_sc hX hz am hin
    cor := nu_sc hX hz aC hinC
    ccs := by
      rw [eC]
      exact C.nd _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
    uHd := rdHead_hereN ar hA hX E Hh LP ⟨hz, hin0, hmx0, hco⟩
    uscA := scAccNN hX hz
    csc := by
      rw [ecs]
      obtain ⟨hz', -, -, -⟩ := Hh.cs
      exact scAccNN hX hz'
    tm := C.tm
    rh := fun h => by
      refine ⟨(C.rh h).1, ?_, (C.rh h).2⟩
      rw [eRh] at h ⊢
      obtain ⟨ht, hs⟩ := Hh.rh h
      have eS : L.mem X (scA (L.mem s (rhA (L := L) s))) = L.mem s (scA (L.mem s (rhA (L := L) s))) :=
        lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ ht 3464#u64 (by simp) (by simp) (by simp)).2.2
          (nT ht (by simp) (by simp) (by simp) (by simp))
      rw [eS]
      obtain ⟨hz', -, -, -⟩ := hs
      exact fun b ha hb => nu_sc hX hz' ha hb }

end

end Fl4Proofs.P2.PathObl
