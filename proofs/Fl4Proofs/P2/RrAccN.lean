/-
# P2 (line p3mc, gen 14): the accepted VM ReplyRecv local path on any guard holding its words (`rr_accR`)

`rr_vm_accG` (`P2/AccessVmRRA.lean`) runs the accepted VM ReplyRecv local path on any store answering
`IoRS K Locks s` as `st`: the read set is fixed, and the dispatch-state record `RrAccV` comes from `VmRPre.rrAccV`
for that set. Here the same proof is restated for **arbitrary** read / write sets `R`, `W` (the counterpart of
`vm_accR`, P2/VmAccN):

* `ScAcc.andV`, **`RrAccV.and`**: the records for two pairs of sets give the record for their meets;
* **`rr_accR`**: an accepted run on `st` is the run on any `gS` answering `R` / `W` as `st`, given the prefix words
  (the node, the current thread's `FLAGS` word, `NEXT_IP`, `FAULT_IP`, the current SC's head) and, at every dispatch
  state `rrX s v n` under the fast path's checks, the record `RrAccV Z R W` (`hRW`) and the `STATE` / `BLOCK_OBJ`
  writes `RrSW` for the checks' receiver (`hSW`).

No premise beyond `VmRPre`'s (as tagged in `AccessVmRRA`): every fact about the sets is a hypothesis.
No existing statement changed.
-/
import Fl4Proofs.P2.AccessVmRRA
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts
open Fl4Proofs.P2.OwnMap (KLayout InW fld own region GateField TimerField GField)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- Two `ScAcc` records give the record for the meets. -/
theorem ScAcc.andV {R1 W1 R2 W2 : U64 → Prop} {sc : U64} {sb : Nat} (A1 : ScAcc R1 W1 sc sb)
    (A2 : ScAcc R2 W2 sc sb) : ScAcc (fun b => R1 b ∧ R2 b) (fun b => W1 b ∧ W2 b) sc sb :=
  ⟨fun b h1 h2 => ⟨A1.rd b h1 h2, A2.rd b h1 h2⟩, fun b h1 h2 => ⟨A1.wr b h1 h2, A2.wr b h1 h2⟩,
    ⟨A1.cons, A2.cons⟩⟩

/-- **`RrAccV` for two pairs of sets gives `RrAccV` for their meets.** -/
theorem RrAccV.and {Z : U64 → Nat} {R1 W1 R2 W2 : U64 → Prop} {X0 : S} {t rptr ep u usc : U64}
    (A1 : RrAccV (L := L) Z R1 W1 X0 t rptr ep u usc) (A2 : RrAccV (L := L) Z R2 W2 X0 t rptr ep u usc) :
    RrAccV (L := L) Z (fun b => R1 b ∧ R2 b) (fun b => W1 b ∧ W2 b) X0 t rptr ep u usc where
  nd o h1 h2 := ⟨⟨(A1.nd o h1 h2).1, (A2.nd o h1 h2).1⟩, ⟨(A1.nd o h1 h2).2, (A2.nd o h1 h2).2⟩⟩
  dt := ⟨A1.dt, A2.dt⟩
  cd := ⟨A1.cd, A2.cd⟩
  kr := ⟨A1.kr, A2.kr⟩
  tab hi hhi := ⟨⟨(A1.tab hi hhi).1, (A2.tab hi hhi).1⟩,
    fun lo hlo h0 => ⟨(A1.tab hi hhi).2 lo hlo h0, (A2.tab hi hhi).2 lo hlo h0⟩⟩
  tSt := ⟨A1.tSt, A2.tSt⟩
  tSc := ⟨A1.tSc, A2.tSc⟩
  tMx := ⟨A1.tMx, A2.tMx⟩
  tIq := ⟨A1.tIq, A2.tIq⟩
  tMi := ⟨A1.tMi, A2.tMi⟩
  tBn := ⟨A1.tBn, A2.tBn⟩
  tPr := ⟨A1.tPr, A2.tPr⟩
  ntf n hn hne := ⟨⟨(A1.ntf n hn hne).1, (A2.ntf n hn hne).1⟩, ⟨(A1.ntf n hn hne).2, (A2.ntf n hn hne).2⟩⟩
  wRp := ⟨A1.wRp, A2.wRp⟩
  wEn := ⟨A1.wEn, A2.wEn⟩
  wEp := ⟨A1.wEp, A2.wEp⟩
  rRt := ⟨A1.rRt, A2.rRt⟩
  rNx := ⟨A1.rNx, A2.rNx⟩
  rPv := ⟨A1.rPv, A2.rPv⟩
  wNx := ⟨A1.wNx, A2.wNx⟩
  wPv := ⟨A1.wPv, A2.wPv⟩
  wRt := ⟨A1.wRt, A2.wRt⟩
  uSt := ⟨A1.uSt, A2.uSt⟩
  uFt := ⟨⟨A1.uFt.1, A2.uFt.1⟩, ⟨A1.uFt.2, A2.uFt.2⟩⟩
  uSc := ⟨A1.uSc, A2.uSc⟩
  uPr := ⟨A1.uPr, A2.uPr⟩
  uAf := ⟨A1.uAf, A2.uAf⟩
  uDo := ⟨A1.uDo, A2.uDo⟩
  uIq := ⟨A1.uIq, A2.uIq⟩
  uMx := ⟨A1.uMx, A2.uMx⟩
  uNi := ⟨A1.uNi, A2.uNi⟩
  uYt := ⟨A1.uYt, A2.uYt⟩
  uFi := ⟨A1.uFi, A2.uFi⟩
  uVt := ⟨⟨A1.uVt.1, A2.uVt.1⟩, ⟨A1.uVt.2, A2.uVt.2⟩⟩
  eTS := ⟨A1.eTS, A2.eTS⟩
  wEh := ⟨A1.wEh, A2.wEh⟩
  wEt := ⟨A1.wEt, A2.wEt⟩
  spo := ⟨A1.spo, A2.spo⟩
  cor := ⟨A1.cor, A2.cor⟩
  ccs := ⟨A1.ccs, A2.ccs⟩
  uHd := ⟨⟨A1.uHd.1, A2.uHd.1⟩, ⟨A1.uHd.2.1, A2.uHd.2.1⟩, ⟨A1.uHd.2.2, A2.uHd.2.2⟩⟩
  uscA := ScAcc.andV A1.uscA A2.uscA
  csc := ScAcc.andV A1.csc A2.csc
  tm h := ⟨A1.tm h, A2.tm h⟩
  rh h := ⟨⟨(A1.rh h).1, (A2.rh h).1⟩, fun b hb hin => ⟨(A1.rh h).2.1 b hb hin, (A2.rh h).2.1 b hb hin⟩,
    ⟨(A1.rh h).2.2.1, (A2.rh h).2.2.1⟩, ⟨(A1.rh h).2.2.2.1, (A2.rh h).2.2.2.1⟩,
    ⟨(A1.rh h).2.2.2.2, (A2.rh h).2.2.2.2⟩⟩

end

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s : S} {K : KLayout}
variable {Locks : S → U64 → Prop}
variable {A : Type} {ar : machine.Arch A}

set_option maxHeartbeats 4000000 in
/-- **The accepted VM ReplyRecv local path on any store answering `R` / `W` as `st`** (module docstring). -/
theorem rr_accR (hA : P0.ArchTotal ar) {s' : S} {a a' : A} {rptr ep : U64}
    (Q : VmRPre st ar K T Cs Ω H Sg Rp Scs Nt Z Ac Locks s rptr ep)
    {gS : machine.Store S} {R W : U64 → Prop} [GRd gS st R] [GWr gS st W]
    (hnode : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      R (L.nodeAt s (L.cpu s) o) ∧ W (L.nodeAt s (L.cpu s) o))
    (hfl : R (core.num.U64.wrapping_add (L.curW s) 3456#u64))
    (hni : R (regA (L.curW s) layout.reg.NEXT_IP)) (hfi : W (regA (L.curW s) layout.reg.FAULT_IP))
    (hcH : RdHead (L := L) R s (L.cscW s))
    (hRW : ∀ (a2 : A) (v n u usc : U64),
      RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z (rrX (L := L) s v n) (L.curW s) rptr ep u usc →
      RRChecksG st ar fl4_abi.consts.fault.VMFault (rrX (L := L) s v n) a2 (L.curW s) rptr ep u usc →
      AsidOff (L := L) Ω Sg (rrX (L := L) s v n) →
      RrAccV (L := L) Z R W (rrX (L := L) s v n) (L.curW s) rptr ep u usc)
    (hSW : ∀ (a2 : A) (v n u usc : U64),
      RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z (rrX (L := L) s v n) (L.curW s) rptr ep u usc →
      RRChecksG st ar fl4_abi.consts.fault.VMFault (rrX (L := L) s v n) a2 (L.curW s) rptr ep u usc →
      RrSW (L := L) gS (L.curW s) ep u)
    (h : syscall.handle_reply_recv_vm_local st ar s a (rptr, ep) = ok (true, s', a')) :
    syscall.handle_reply_recv_vm_local gS ar s a (rptr, ep) = ok (true, s', a') := by
  have P := Q.base
  have hN := P.np
  have hcT := P.cT
  have hc := P.tA
  have hcC : L.cpu s ∈ Cs := by obtain ⟨⟨Qs, Rq, hq⟩, -, -, -, -⟩ := P.bxi; exact hq.cur
  have hpre : ∀ v s1 s2 a1, obj.Tcb.set_reg st (L.curW s) s layout.reg.FAULT_IP v = ok s1 →
      sched.update_timestamp st ar s1 a = ok (s2, a1) → ∃ n, s2 = rrX (L := L) s v n := by
    intro v s1 s2 a1 e1 eu
    rw [set_reg_ok'] at e1
    obtain rfl := ok_inj_ff e1
    have hN1 : NodePlaced st T (L.wr s (regA (L.curW s) layout.reg.FAULT_IP) v)
        (L.cpu (L.wr s (regA (L.curW s) layout.reg.FAULT_IP) v)) := by
      rw [LawfulStore.cpu_wr]; exact hN.wr
    obtain ⟨⟨n, a2⟩, hn, -⟩ := spec_ex_fd (hA.now a)
    rw [update_timestamp_ok ar hN1 hn] at eu
    exact ⟨n, (Prod.mk.inj (ok_inj_ff eu)).1.symm⟩
  refine syscall.handle_reply_recv_vm_local.guard_acc (gS := gS) ar
    (hnode _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])).1
    hfl hni hfi ?_ ?_ ?_ ?_ h
  · intro v s1 e1
    rw [set_reg_ok'] at e1
    obtain rfl := ok_inj_ff e1
    rw [ctA_wr, cnA_wr]
    exact ⟨(hnode _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).1,
      (hnode _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).2,
      (hnode _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])).1,
      (hnode _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])).2⟩
  · intro v s1 s2 a1 e1 eu
    obtain ⟨n, rfl⟩ := hpre v s1 s2 a1 e1 eu
    rw [rrX_nodeAt, rrX_nodeAt]
    exact ⟨(hnode _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])).1,
      (hnode _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])).1⟩
  · intro v s1 s2 a1 csc e1 eu ecsc
    obtain ⟨n, rfl⟩ := hpre v s1 s2 a1 e1 eu
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) _)] at ecsc
    have e : csc = L.cscW s := by
      rw [← rrX_csc hN hc hcT v n]; exact (ok_inj_ff ecsc).symm
    subst e
    exact rdHead_rrX hN hc hcT hcC v n (bxi_headOut P.bxi P.cscS) hcH
  · intro nx s1 s2 a1 enx e1 eu h'
    have hLP : LocalPre (st := st) ar s a (s2, a1) := ⟨L.curW s, nx, s1, cur_thread_ok s, enx, e1, eu⟩
    obtain ⟨n, rfl⟩ := hpre _ s1 s2 a1 e1 eu
    obtain ⟨hI2, hAs2, hP2⟩ := Q.mid a _ a1 hLP
    obtain ⟨u0, usc0, C0, -⟩ := reply_recv_vm_found_acc st ar h'
    have Pl0 := (hP2 u0 usc0 C0).1
    have keep : ∀ b ∈ Ω, L.mem (rrX (L := L) s (core.num.U64.wrapping_sub nx 2#u64) n) b = L.mem s b :=
      fun b hb => rrX_out hN hc hcT hcC _ n ((Pl0.hΩ b hb).ksb (rrX_ksb s _ n).symm)
    have hrz : L.mem (rrX (L := L) s (core.num.U64.wrapping_sub nx 2#u64) n) (rNextA rptr) &&& ~~~1#u64 = 0#u64 ∧
        L.mem (rrX (L := L) s (core.num.U64.wrapping_sub nx 2#u64) n) (rPrevA rptr) &&& ~~~1#u64 = 0#u64 :=
      ⟨by rw [keep _ (Pl0.hSg.sub _ (Pl0.hO.nextW Pl0.hrR)), Q.nb.2]; exact zero_and_not1,
       by rw [keep _ (Pl0.hSg.sub _ (Pl0.hO.prevW Pl0.hrR)), Q.nb.1]; exact zero_and_not1⟩
    exact fastpath_vm.reply_recv_vm_found.guard (gS := gS) (R := R) (W := W) ar hA hI2
      (fun u usc C => (hP2 u usc C).1) hrz (fun u usc C => (hP2 u usc C).2) hAs2
      (fun u usc C => hRW a1 _ n u usc (hP2 u usc C).1 C hAs2)
      (fun u usc C => hSW a1 _ n u usc (hP2 u usc C).1 C) h'

end

end Fl4Proofs.P2.PathObl
