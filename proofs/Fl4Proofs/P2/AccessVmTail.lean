/-
# P2: the VM-fault local path's tail on the guarded store (line p2e, VM paths)

`vm_acc_of_tail` (`P2/AccessVmAcc.lean`) proves the accepted `handle_vm_fault_local` run on
`PathObl.guard st (IoRS K Locks s) (IoWS K Locks s)` up to one hypothesis, `htail`: the tail from the
handler made `Running` (`faultTail3`: the handler's SC, its scheduler links, `switch_to`) agrees on
the guarded store. Here it is discharged.

* `vmPre2`, `vmPre14_eq1`, `vmPre2_eq`: `vmPre14` ends at P1's meeting state `fS14` (as P1's
  `faultTailG_eq` / `faultTail2G_eq` for the whole fast path);
* `VmTailAcc`: the words the tail reads and writes, at the state the fast path is entered;
* `faultTail3.guardVm`: the tail on any store answering those words as `st` (`GRd` / `GWr`),
  from P1's facts there: the end of p2sl's `fastpath.fault.guard` (`P2/AccessFastFault.lean`:
  `endpoint.unblock_sporadic.guard`, `fastpath.switch_to.guard` at the pre-switch state) with the VM
  fault's `set_fault` (`set_fault_vm`, `faultReads_ofG` at the VM label);
* `VmMidF.tailAcc`: `VmTailAcc` for `IoRS K Locks s` / `IoWS K Locks s` at `utW s n` (the state after
  the entry's `update_timestamp`), from `VmBase` and `VmMidF`;
* `vm_accG`: **the accepted VM-fault local path on any store answering its words as `st`**
  (`GRd`/`GWr`, the `STATE` writes `VmSW`) ends as the real run, with no tail hypothesis; `vm_acc`: on
  the guarded store.

Premises of `vm_acc`: `VmFPre`'s (`P2/AccessVmAcc.lean`: `base`, `hyp` [J], `lk` [P], `hEp`/`hRp` [J],
`hyt` [J]) and
* `hTab` [J]: the ASID words `set_vm_root` may read (`RdTab`) are in `IoRS K Locks s`. Where they
  are: the ASID table is the 2048 words at `ks_base + 288000` (`layout.ks.ASID_TABLE`,
  `atAF (L.ksb s) hi`, `hi < 2048`), the pool words are `peAF p lo` (`lo < 512`) of each nonzero
  table entry `p`. Why gate-owned: `IoLay` covers the kernel-state area only up to
  `ks_base + 13568` (`IoLay.ks`), and no typed object of the layout (node, slot, TCB, notification,
  endpoint, reply object, SC) covers these words, so `region K` is `.none` and `own K` is `.gate`,
  readable by every path; they are not user memory (P1's `AsidOff` puts them among the kernel
  words `Ω`, disjoint from P1's user words `U` by `VmFootHyps.user`, which P3's layout takes as
  `K.user`). Discharging it = extending `IoLay` / the ownership map to that kernel-state region (the
  ASID table at `ks_base + 288000`, and the ASID pools as their own region kind), with
  `K.user ∩ Ω = ∅` from P3's layout.
-/
import Fl4Proofs.P2.AccessFastFault
import Fl4Proofs.P2.AccessVmAcc
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts
open Fl4Proofs.P2.OwnMap (KLayout GateField TimerField GField)

/-! ## `vmPre14` ends at P1's meeting state -/

section
variable {S : Type} {A : Type}

/-- `vmPre14` from the end of the dequeue (`s5`). -/
def vmPre2 (m : machine.Store S) (ar : machine.Arch A) (s5 : S) (a : A) (t : obj.Tcb) (ty i2 i3 badge : U64) :
    Result S := do
  let recv_buf ← msg.lookup_ipc_buffer m s5 true i2
  let (sent, s6) ← faults.set_mrs_fault m ar s5 a t i2 recv_buf
  let mi ← msginfo.MessageInfo.new ty 0#u64 0#u64 sent
  let s7 ← msg.set_msg_info m s6 i2 mi
  let s8 ← obj.Tcb.set_reg m i2 s7 layout.reg.BADGE badge
  let s9 ← obj.Reply.set_tcb m i3 s8 0#u64
  let s10 ← obj.Tcb.set_state m i2 s9 sched.TS_INACTIVE
  let s11 ← obj.Reply.set_tcb m i3 s10 t
  let s12 ← obj.Tcb.set_state m t s11 sched.TS_BLOCKED_ON_REPLY
  let s13 ← obj.Tcb.set_reply_obj m t s12 i3
  obj.Tcb.set_state m i2 s13 sched.TS_RUNNING

variable {st : machine.Store S} [L : LawfulStore st] (ar : machine.Arch A)

/-- `set_fault`, then the dequeue `epFast` (P1's `faultTailG_eq`). -/
theorem vmPre14_eq1 {s s2 : S} (a : A) (t : obj.Tcb) (f : error.Fault) (ty ptr badge dest r : U64)
    (h2 : faults.set_fault st s t f = ok s2) :
    vmPre14 st ar s a t f ty ptr badge dest r = vmPre2 st ar (epFast (L := L) s2 ptr dest) a t ty dest r badge := by
  unfold vmPre14
  rw [h2]; simp only [bind_ok]
  rw [obj.Ep.tail.ok]; simp only [bind_ok]
  by_cases htl : (L.epQ s2 ptr).end = dest
  · rw [if_pos htl, obj.Ep.set_queue.ok]; simp only [bind_ok]
    rw [obj.Tcb.set_ep_next.ok]; simp only [bind_ok]
    rw [obj.Tcb.set_ep_prev.ok]; simp only [bind_ok]
    unfold epFast; simp only [htl, ↓reduceIte]; rfl
  · rw [if_neg htl]
    rw [obj.Tcb.ep_next.ok]; simp only [bind_ok]
    rw [obj.Tcb.set_ep_prev.ok]; simp only [bind_ok]
    rw [obj.Ep.set_queue.ok]; simp only [bind_ok]
    rw [obj.Tcb.set_ep_next.ok]; simp only [bind_ok]
    rw [obj.Tcb.set_ep_prev.ok]; simp only [bind_ok]
    unfold epFast; simp only [htl, ↓reduceIte]; rfl

/-- From the dequeue to the handler `Running`: P1's `fS14` (`faultTail2G_eq`). -/
theorem vmPre2_eq (s5 : S) (a : A) (t : obj.Tcb) (ty dest r badge : U64)
    {rb sent : U64} {S6 S7 S8 : S} {mi : msginfo.MessageInfo}
    (hbuf : msg.lookup_ipc_buffer st s5 true dest = ok rb)
    (hmrs : faults.set_mrs_fault st ar s5 a t dest rb = ok (sent, S6))
    (hmi : msginfo.MessageInfo.new ty 0#u64 0#u64 sent = ok mi)
    (hS7 : msg.set_msg_info st S6 dest mi = ok S7)
    (hS8 : obj.Tcb.set_reg st dest S7 layout.reg.BADGE badge = ok S8) :
    vmPre2 st ar s5 a t ty dest r badge = ok (fS14 (L := L) S8 t dest r) := by
  unfold vmPre2
  rw [hbuf]; simp only [bind_ok]
  rw [hmrs]; simp only [bind_ok, uncurry_apply_pair]
  rw [hmi]; simp only [bind_ok]
  rw [hS7]; simp only [bind_ok]
  rw [hS8]; simp only [bind_ok]
  rw [eq_of_spec_fd (obj.Reply.set_tcb.spec (L := L) _ r _)]; simp only [bind_ok]
  rw [eq_of_spec_fd (obj.Tcb.set_state.spec (L := L) _ dest _)]; simp only [bind_ok]
  rw [eq_of_spec_fd (obj.Reply.set_tcb.spec (L := L) _ r _)]; simp only [bind_ok]
  rw [eq_of_spec_fd (obj.Tcb.set_state.spec (L := L) _ t _)]; simp only [bind_ok]
  rw [eq_of_spec_fd (obj.Tcb.set_reply_obj.wr (L := L) _ t _)]; simp only [bind_ok]
  rw [eq_of_spec_fd (obj.Tcb.set_state.spec (L := L) _ dest _)]
  rfl

end

/-! ## The tail on a store answering its words as `st` -/

section
variable {S : Type} {st : machine.Store S} {R W : U64 → Prop} {gS : machine.Store S} [GRd gS st R] [GWr gS st W]
  [L : LawfulStore st]

/-- **The words the tail reads and writes** (at the state `s` the fast path is entered, with
`dest` the handler; `Z` the SC sizes): the current core's node, the kernel's `DOMAIN_TIME` and root,
the ASID words, the handler's words `switch_to` and `unblock_sporadic` touch, its SC and the current
SC (`ScAcc`), the timer-min thread's deadline and the release head's SC. -/
structure VmTailAcc (Z : U64 → Nat) (R W : U64 → Prop) (s : S) (dest : U64) : Prop where
  nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s (L.cpu s) o) ∧ W (L.nodeAt s (L.cpu s) o)
  dt : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME)
  kr : R (krA (L := L) s)
  tab : RdTab (L := L) R s
  dvt : R (vtA dest) ∧ R (core.num.U64.wrapping_add (vtA dest) 8#u64)
  dsc0 : R (scA dest)
  diq : R (inqA dest)
  dyt : R (yieldA dest)
  dst : R (stA dest)
  dfi : R (regA dest layout.reg.FAULT_IP)
  dni : W (regA dest layout.reg.NEXT_IP)
  dsw : W (nextA .Sched dest) ∧ W (prevA .Sched dest)
  spo : R (sporA (L.mem s (scA dest)))
  dsc : ScAcc R W (L.mem s (scA dest)) (Z (L.mem s (scA dest)))
  csc : ScAcc R W (L.cscW s) (Z (L.cscW s))
  tm : L.mem s (tmA (L := L) s) ≠ 0#u64 → R (core.num.U64.wrapping_add (L.mem s (tmA (L := L) s)) 3528#u64)
  rh : L.mem s (rhA (L := L) s) ≠ 0#u64 → R (scA (L.mem s (rhA (L := L) s))) ∧
    (∀ b, Aligned b → InSC (L.mem s (scA (L.mem s (rhA (L := L) s))))
      (Z (L.mem s (scA (L.mem s (rhA (L := L) s))))) b → R b) ∧
    RdHead (L := L) R s (L.mem s (scA (L.mem s (rhA (L := L) s))))

variable {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 8000000 in
/-- **The VM-fault fast path's tail on the guarded store**: from the handler made `Running`
(`vmPre14`'s end), `faultTail3` on `gS` is the real run, when `gS` answers `VmTailAcc`'s words as
`st` and the handler's `STATE` write (`SWr`), under P1's facts at the fast path's entry `s` (`BXI`,
`FaultEntAt`), the handler blocked on receive and yielding to no SC. -/
theorem faultTail3.guardVm {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
    (hA : P0.ArchTotal ar) {s : S} {a : A} {t : obj.Tcb} {addr code : U64} {ins : Bool}
    {ptr badge dest r : U64} {s14 s' : S} {a' : A}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hF : FaultEntAt (L := L) T Cs Ω U Sg Rp s t)
    (hc : FaultChecks st s t ptr badge dest r)
    (hrecv : L.mem s (stA dest) = sched.TS_BLOCKED_ON_RECV)
    (hy0 : L.mem s (yieldA dest) = 0#u64)
    (K : VmTailAcc (L := L) Z R W s dest)
    (hSW : SWr gS st dest sched.TS_RUNNING)
    (e14 : vmPre14 st ar s a t (error.Fault.VmFault addr code ins) fl4_abi.consts.fault.VMFault ptr badge dest r =
      ok s14)
    (h : faultTail3 st ar s14 a dest = ok (true, s', a')) :
    faultTail3 gS ar s14 a dest = ok (true, s', a') := by
  have hAs : AsidOff (L := L) Ω Sg s := hF.1
  obtain ⟨⟨Q, RQ, hSQ⟩, hB, hX, hSg, hS⟩ := hI
  have hX0 : ScExtra0 st T Cs Scs Nt s := hX.2.2.toScExtra0
  have hO := hX.1
  have hTm : TimerOK st T Cs s := hX.2.2.tm
  -- `vmPre14` up to P1's meeting state
  rw [vmPre14_eq1 (st := st) ar a t _ _ ptr badge dest r (set_fault_vm (st := st) s t addr code ins)] at e14
  have e0 := e14
  unfold vmPre2 at e14
  obtain ⟨rb, hbuf, e1⟩ := bind_eq_ok e14
  obtain ⟨⟨sent, S6⟩, hmrs, e2⟩ := bind_eq_ok e1
  simp only [uncurry_apply_pair] at e2
  obtain ⟨mi, hmi, e3⟩ := bind_eq_ok e2
  obtain ⟨S7, hS7, e4⟩ := bind_eq_ok e3
  obtain ⟨S8, hS8, -⟩ := bind_eq_ok e4
  rw [vmPre2_eq ar _ a t _ dest r badge hbuf hmrs hmi hS7 hS8] at e0
  have e14' := ok_inj_ff e0
  subst e14'
  have hf0 := h
  rw [faultTail3_eq] at hf0
  obtain ⟨s15, h15, hfin⟩ := bind_eq_ok hf0
  obtain ⟨hr, rest, E⟩ := hF.2 ptr badge dest r hc
  obtain ⟨-, -, KF⟩ := faultReads_ofG ar (Or.inr rfl) E hbuf hmrs hS7 hS8
  have HF := here_facts (L := L) hc.here
  have hT := E.hT
  have hdT : dest ∈ T := E.hq.mem dest (by simp)
  have hd' := hT dest hdT
  have hN := E.hN
  have hcC := E.hcC
  have hΩ := E.hΩ
  -- the handler's SC (as P1's `faultNvm_tailG`)
  have hdsc : L.mem s (scA dest) ∈ Scs := (hX0.bound dest hdT HF.sc).1
  obtain ⟨hPl, hZ7⟩ := hO.sc _ hdsc
  have scW : ∀ b, Aligned b → InSC (L.mem s (scA dest)) (Z (L.mem s (scA dest))) b → b ∈ Ω :=
    fun b hb h => hS.sub _ ((hS.all _ hdsc).2.2 b hb h)
  have spWF : L.mem s (sporA (L.mem s (scA dest))) ≠ 0#u64 →
      RefillsWF st s (L.mem s (scA dest)) (Z (L.mem s (scA dest))) :=
    fun h => (hS.all _ hdsc).1 ((hS.act _ hdsc).1 (hS.spor _ hdsc h))
  have hact : L.mem s (scA dest) ∈ Ac :=
    hB.sact dest hdT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl hrecv)))))))) HF.sc
  have hWs : RefillsWF st s (L.mem s (scA dest)) (Z (L.mem s (scA dest))) :=
    (hS.all _ hdsc).1 ((hS.act _ hdsc).1 hact)
  have nrt : ∀ c ∈ Scs, ∀ b, InSC c (Z c) b → b ≠ rTcbA r := fun c hc' b hin e => by
    have := hO.rpSc r hr _ hc'; subst e; unfold InSC at hin; rw [rTcbA_val0] at hin; omega
  have hUo := usOff_of E KF scW (hS.sub _ (hS.spSg _ hdsc)) spWF (hO.rpSc r hr _ hdsc) hZ7 hPl.fits
  have w15 := unblock_sporadic_fr hUo h15
  have esc14 : L.mem (fS14 (L := L) S8 t dest r) (scA dest) = L.mem s (scA dest) :=
    KF.tcb dest hdT 3464#u64 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  have hW14 : RefillsWF st (fS14 (L := L) S8 t dest r) (L.mem s (scA dest)) (Z (L.mem s (scA dest))) :=
    hWs.agree fun b hb hin => KF.omg b (scW b hb hin) (nrt _ hdsc b hin)
  have hW15 : RefillsWF st s15 (L.mem s (scA dest)) (Z (L.mem s (scA dest))) := by
    have := unblock_sporadic_wf hUo (by rw [esc14]; exact hW14) h15
    rw [esc14] at this; exact this
  rw [esc14] at w15
  have K15 := finKeep15 hT hN hcC hΩ KF scW w15
  -- the end: the handler's links cleared, then `switch_to`
  rw [obj.Tcb.set_sched_next.ok] at hfin; simp only [bind_ok] at hfin
  rw [obj.Tcb.set_sched_prev.ok] at hfin; simp only [bind_ok] at hfin
  obtain ⟨⟨x1, x2⟩, hsw, hx⟩ := bind_eq_ok hfin
  have hx' := ok_inj_ff hx
  simp only [Prod.mk.injEq, true_and] at hx'
  obtain ⟨rfl, rfl⟩ := hx'
  generalize hY : L.wr (L.wr s15 (nextA .Sched dest) 0#u64) (prevA .Sched dest) 0#u64 = Y at hsw
  have nA : Aligned (nextA .Sched dest) := by unfold nextA nextOff; exact field_aligned hd' (by simp) (by simp)
  have pA : Aligned (prevA .Sched dest) := by unfold prevA prevOff; exact field_aligned hd' (by simp) (by simp)
  have kY : L.ksb Y = L.ksb s := by rw [← hY, L.ksb_wr, L.ksb_wr, K15.ksb]
  have cY : L.cpu Y = L.cpu s := by rw [← hY, LawfulStore.cpu_wr, LawfulStore.cpu_wr, K15.cpu]
  have agY : ∀ b, Aligned b → b ≠ nextA .Sched dest → b ≠ prevA .Sched dest → L.mem Y b = L.mem s15 b := by
    intro b hb h1 h2
    rw [← hY, mem_wr_ne' pA hb (Ne.symm h2), mem_wr_ne' nA hb (Ne.symm h1)]
  have lkΩ : ∀ b ∈ Ω, b ≠ nextA .Sched dest ∧ b ≠ prevA .Sched dest := fun b hb =>
    ⟨fun e => out_ne_field (hΩ b hb) hdT hd' (K := 3480#u64) (by simp) (by rw [e]; rfl),
     fun e => out_ne_field (hΩ b hb) hdT hd' (K := 3488#u64) (by simp) (by rw [e]; rfl)⟩
  have lkT : ∀ K : U64, K.val < 4096 → K.val ≠ 3480 → K.val ≠ 3488 →
      core.num.U64.wrapping_add dest K ≠ nextA .Sched dest ∧ core.num.U64.wrapping_add dest K ≠ prevA .Sched dest :=
    fun K hK h1 h2 => ⟨field_ne hd' hd' hK (K2 := 3480#u64) (by simp) (fun _ => by simpa using h1),
      field_ne hd' hd' hK (K2 := 3488#u64) (by simp) (fun _ => by simpa using h2)⟩
  have agΩ : ∀ b ∈ Ω, L.mem Y b = L.mem s15 b := fun b hb => agY b (hΩ b hb).1 (lkΩ b hb).1 (lkΩ b hb).2
  have agT : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3480 → K.val ≠ 3488 →
      L.mem Y (core.num.U64.wrapping_add dest K) = L.mem s15 (core.num.U64.wrapping_add dest K) :=
    fun K hK h8 h1 h2 => agY _ (field_aligned hd' hK h8) (lkT K hK h1 h2).1 (lkT K hK h1 h2).2
  have P : TailPld (L := L) T Cs Ω Y dest :=
    (⟨hT, hdT, hN, hcC, hΩ⟩ : TailPld (L := L) T Cs Ω s dest).ksb kY cY
  have escY : L.mem Y (scA dest) = L.mem s (scA dest) := by
    rw [scA_eq, agT _ (by simp) (by simp) (by simp) (by simp)]
    exact K15.tcb dest hdT 3464#u64 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  have eyY : L.mem Y (yieldA dest) = L.mem s (yieldA dest) := by
    rw [show yieldA dest = core.num.U64.wrapping_add dest 3472#u64 from rfl, agT _ (by simp) (by simp) (by simp)
      (by simp)]
    exact K15.tcb dest hdT 3472#u64 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  have csA : Aligned (L.nodeAt s (L.cpu s) layout.node.CUR_SC) :=
    nodeAt_aligned hN (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  have ecY : L.cscW Y = L.cscW s := by
    unfold LawfulStore.cscW LawfulStore.nodeA
    rw [cY, nodeAt_of_ksb kY]
    rw [agY _ csA (fun e => node_ne_field hN (by simp [layout.node.CUR_SC]) hdT hd' (K := 3480#u64) (by simp) e)
      (fun e => node_ne_field hN (by simp [layout.node.CUR_SC]) hdT hd' (K := 3488#u64) (by simp) e)]
    exact K15.node _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
      (by simp [layout.node.CUR_SC])
  have hWY : RefillsWF st Y (L.mem s (scA dest)) (Z (L.mem s (scA dest))) :=
    hW15.agree fun b hb hin => agΩ b (scW b hb hin)
  have hcs : L.cscW s ∈ Scs := hX0.cur
  have hcq0 : SCq st s Ω (L.cscW s) (Z (L.cscW s)) := by
    obtain ⟨hP, hz⟩ := hO.sc _ hcs
    obtain ⟨h8, h128, -⟩ := sc_lo hP hz
    have hv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
    have hcv : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
    obtain ⟨a1, a2, a3⟩ := maxA_facts hO hcs
    exact ⟨(hS.all _ hcs).1, fun b hb hi => hS.sub _ ((hS.all _ hcs).2.2 b hb hi),
      ⟨⟨by rw [hv]; omega, by rw [hv, hcv]; omega⟩, by unfold Aligned; rw [hv, hcv]; omega⟩, ⟨a2, a3⟩, a1⟩
  have hcY : SCq st Y Ω (L.cscW Y) (Z (L.cscW Y)) := by
    rw [ecY]
    refine ⟨fun hm => ?_, hcq0.2.1, hcq0.2.2⟩
    by_cases hcd : L.cscW s = L.mem s (scA dest)
    · rw [hcd]; exact hWY
    · have agC : ∀ b, Aligned b → InSC (L.cscW s) (Z (L.cscW s)) b → L.mem Y b = L.mem s b := by
        intro b hb hin
        have hbΩ := hcq0.2.1 b hb hin
        rw [agΩ b hbΩ]
        refine K15.omg b hbΩ (nrt _ hcs b hin) fun hR => ?_
        have := hO.scDisj _ hcs _ hdsc hcd
        unfold InSC at hin; unfold InRing at hR; omega
      have em : L.rmax Y (L.cscW s) = L.rmax s (L.cscW s) := by
        obtain ⟨a1, a2, a3⟩ := maxA_facts hO hcs
        exact agC _ a1 ⟨a2, a3⟩
      exact (hcq0.1 (em ▸ hm)).agree agC
  have htY : L.mem Y (scA dest) ≠ L.cscW Y → SCin st Y Ω (L.mem Y (scA dest)) (Z (L.mem Y (scA dest))) ∧
      ∀ b, InSC (L.mem Y (scA dest)) (Z (L.mem Y (scA dest))) b → Outside b (L.cscW Y) (Z (L.cscW Y)) := by
    rw [escY, ecY]
    intro hne
    refine ⟨⟨hWY, scW⟩, fun b hin => ?_⟩
    have := hO.scDisj _ hdsc _ hcs hne
    unfold InSC at hin; unfold Outside; omega
  have hrS : rTcbA r ∈ Sg := by
    have := (hO.rp r hr).1
    exact hO.rpW r hr _ (by show _ % 8 = 0; rw [rTcbA_val0]; omega) (by rw [rTcbA_val0] <;> omega)
      (by rw [rTcbA_val0]; omega)
  have eNY : ∀ o, L.nodeAt Y (L.cpu Y) o = L.nodeAt s (L.cpu s) o := fun o => by rw [cY, nodeAt_of_ksb kY]
  have ndY : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 16 → o.val ≠ 56 →
      L.mem Y (L.nodeAt s (L.cpu s) o) = L.mem s (L.nodeAt s (L.cpu s) o) := by
    intro o h1 h2 h3 h4
    rw [agY _ (nodeAt_aligned hN h1 h2) (fun e => node_ne_field hN h1 hdT hd' (K := 3480#u64) (by simp) e)
      (fun e => node_ne_field hN h1 hdT hd' (K := 3488#u64) (by simp) e)]
    exact K15.node o h1 h2 h3 h4
  have tfY : ∀ y ∈ T, ∀ K : U64, 3328 < K.val → K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3360 → K.val ≠ 3376 →
      K.val ≠ 3384 → K.val ≠ 3392 → K.val ≠ 3400 → K.val ≠ 3496 → K.val ≠ 3504 → K.val ≠ 3480 → K.val ≠ 3488 →
      L.mem Y (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := by
    intro y hy K h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
    have hy' := hT y hy
    rw [agY _ (field_aligned hy' h2 h3) (field_ne hy' hd' h2 (K2 := 3480#u64) (by simp) (fun _ => by simpa using h11))
      (field_ne hy' hd' h2 (K2 := 3488#u64) (by simp) (fun _ => by simpa using h12))]
    exact K15.tcb y hy K h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hrhY : L.mem Y (rhA (L := L) Y) = L.mem s (rhA (L := L) s) := by
    show L.mem Y (L.nodeAt Y (L.cpu Y) _) = _
    rw [eNY]
    exact ndY _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
  have htmY : L.mem Y (tmA (L := L) Y) = L.mem s (tmA (L := L) s) := by
    show L.mem Y (L.nodeAt Y (L.cpu Y) _) = _
    rw [eNY]
    exact ndY _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
  -- the release head: in `T`, its SC among `Scs` and active
  have rhF : L.mem s (rhA (L := L) s) ≠ 0#u64 → L.mem s (rhA (L := L) s) ∈ T ∧
      L.mem s (scA (L.mem s (rhA (L := L) s))) ∈ Scs ∧ L.mem s (scA (L.mem s (rhA (L := L) s))) ∈ Ac := by
    intro h0
    have hq := hSQ.release _ hcC
    have hhd : (L.relQ s (L.cpu s)).head = (RQ (L.cpu s)).headD 0#u64 := hq.head
    cases hl : RQ (L.cpu s) with
    | nil => rw [hl] at hhd; exact absurd hhd h0
    | cons y ys =>
      rw [hl] at hhd
      have e : L.mem s (rhA (L := L) s) = y := hhd
      have hyR : y ∈ RQ (L.cpu s) := by rw [hl]; simp
      have hyT := hq.mem y hyR
      have haf := hSQ.inR _ hcC y hyR
      have hfl : (L.mem s (inqA y) &&& sched.Q_RELEASE) ≠ 0#u64 := (hSQ.released y hyT).2 (by rw [haf]; exact hyR)
      have hs0 := hB.r y hyT hfl
      rw [e]
      exact ⟨hyT, (hX0.bound y hyT hs0).1, hB.sact y hyT (Or.inr (Or.inl hfl)) hs0⟩
  -- an SC other than the handler's keeps its words to `Y`
  have scY : ∀ q ∈ Scs, q ≠ L.mem s (scA dest) → ∀ b, Aligned b → InSC q (Z q) b → L.mem Y b = L.mem s b := by
    intro q hq hne b hb hin
    have hbΩ := hS.sub _ ((hS.all _ hq).2.2 b hb hin)
    rw [agΩ b hbΩ]
    refine K15.omg b hbΩ (nrt _ hq b hin) fun hR => ?_
    have := hO.scDisj _ hq _ hdsc hne
    unfold InSC at hin; unfold InRing at hR; omega
  have hrhG : L.mem Y (rhA (L := L) Y) ≠ 0#u64 → L.mem Y (rhA (L := L) Y) ∈ T ∧
      R (scA (L.mem Y (rhA (L := L) Y))) ∧
      ∃ zq, SCin st Y Ω (L.mem Y (scA (L.mem Y (rhA (L := L) Y)))) zq ∧
        (∀ b, Aligned b → InSC (L.mem Y (scA (L.mem Y (rhA (L := L) Y)))) zq b → R b) ∧
        (L.mem Y (scA (L.mem Y (rhA (L := L) Y))) ≠ L.cscW Y →
          ∀ b, InSC (L.mem Y (scA (L.mem Y (rhA (L := L) Y)))) zq b → Outside b (L.cscW Y) (Z (L.cscW Y))) ∧
        (L.mem Y (scA (L.mem Y (rhA (L := L) Y))) ≠ L.mem Y (scA dest) → L.mem Y (scA dest) ≠ L.cscW Y →
          ∀ b, InSC (L.mem Y (scA (L.mem Y (rhA (L := L) Y)))) zq b →
            Outside b (L.mem Y (scA dest)) (Z (L.mem Y (scA dest)))) := by
    rw [hrhY]
    intro h0
    obtain ⟨hyT, hqS, hqA⟩ := rhF h0
    obtain ⟨kr1, kr2, -⟩ := K.rh h0
    have esY : L.mem Y (scA (L.mem s (rhA (L := L) s))) = L.mem s (scA (L.mem s (rhA (L := L) s))) :=
      tfY _ hyT 3464#u64 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [esY, escY, ecY]
    generalize L.mem s (scA (L.mem s (rhA (L := L) s))) = q at hqS hqA kr2 ⊢
    refine ⟨hyT, kr1, Z q, ⟨?_, fun b hb hin => hS.sub _ ((hS.all _ hqS).2.2 b hb hin)⟩, kr2, ?_, ?_⟩
    · by_cases hqd : q = L.mem s (scA dest)
      · rw [hqd]; exact hWY
      · exact ((hS.all _ hqS).1 ((hS.act _ hqS).1 hqA)).agree (scY q hqS hqd)
    · intro hne b hin
      have := hO.scDisj _ hqS _ hcs hne
      unfold InSC at hin; unfold Outside; omega
    · intro hne _ b hin
      have := hO.scDisj _ hqS _ hdsc hne
      unfold InSC at hin; unfold Outside; omega
  have htmG : L.mem Y (tmA (L := L) Y) ≠ 0#u64 → L.mem Y (tmA (L := L) Y) ∈ T ∧
      R (core.num.U64.wrapping_add (L.mem Y (tmA (L := L) Y)) 3528#u64) := by
    rw [htmY]
    intro h0
    exact ⟨(hTm.min _ hcC).resolve_left h0, K.tm h0⟩
  have keepA : ∀ b ∈ Ω, b ∉ Sg → L.mem Y b = L.mem s b := fun b hb hs => by
    rw [agΩ b hb]
    exact K15.omg b hb (fun e => hs (e ▸ hrS)) fun hR => hs ((hS.all _ hdsc).2.2 b (hΩ b hb).1 hR.inSC)
  have hRV : RdVm (L := L) R Y dest := by
    refine ⟨K.dvt.1, K.dvt.2, ?_, ?_⟩
    · show R (core.num.U64.wrapping_add (L.ksb Y) _); rw [kY]; exact K.kr
    · refine fun hi hhi => ?_
      have aT := hAs hi hhi
      rw [kY, keepA _ aT.1 aT.2.1]
      exact K.tab hi hhi
  have hactY : L.mem Y (scA dest) = L.cscW Y → L.rmax Y (L.cscW Y) ≠ 0#u64 := by
    intro e
    rw [← e, escY]
    intro h0
    have hm := hWY.min_le
    rw [h0] at hm
    simp [sporadic.MIN_REFILLS] at hm
  have hNdY : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeA Y o) ∧ W (L.nodeA Y o) := fun o ho h8 => by
    show R (L.nodeAt Y (L.cpu Y) o) ∧ W (L.nodeAt Y (L.cpu Y) o)
    rw [eNY]; exact K.nd o ho h8
  have hSw := fastpath.switch_to.guard (gS := gS) hA Y a P hcY htY hactY (by rw [eyY]; exact hy0) hrhG htmG hRV hNdY
    (by rw [kY]; exact K.dt) (by rw [ecY]; exact K.csc) (fun _ => by rw [escY]; exact K.dsc)
    K.dsc0 K.dyt K.dst K.dfi K.dni hSW K.diq
  -- the guarded run
  rw [faultTail3_split ar gS]
  have h15f : endpoint.unblock_sporadic st (fS14 (L := L) S8 t dest r) dest = ok s15 := h15
  rw [endpoint.unblock_sporadic.guard (gS := gS) _ dest K.dsc0 (by rw [esc14]; exact K.spo)
    (by rw [KF.cpu, nodeAt_of_ksb KF.ksb]; exact (K.nd _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])).1)
    (by rw [esc14]; exact K.dsc) (by rw [esc14]; exact hW14) hUo.rp
    (by show R (L.nodeAt _ (L.cpu _) _); rw [KF.cpu, nodeAt_of_ksb KF.ksb];
        exact (K.nd _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).1)
    (by show W (L.nodeAt _ (L.cpu _) _); rw [KF.cpu, nodeAt_of_ksb KF.ksb];
        exact (K.nd _ (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])).2), h15f]
  simp only [bind_ok]
  rw [obj.Tcb.set_sched_next.guard (gS := gS) dest s15 _ K.dsw.1, obj.Tcb.set_sched_next.ok]; simp only [bind_ok]
  rw [obj.Tcb.set_sched_prev.guard (gS := gS) dest _ _ K.dsw.2, obj.Tcb.set_sched_prev.ok]; simp only [bind_ok]
  rw [hY, hSw, hsw]
  simp only [bind_ok]
  rfl

end

/-! ## The tail's words in the VM path's sets -/

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s : S} {K : KLayout}
variable {Locks : S → U64 → Prop}

/-- The release head's SC, whole (as `VmBase.rs`). -/
theorem VmBase.rsAcc (P : VmBase st K T Cs Ω H Sg Rp Scs Nt Z Ac s) (h0 : L.mem s (rhA (L := L) s) ≠ 0#u64) :
    L.mem s (scA (L.mem s (rhA (L := L) s))) ∈ Scs ∧
      ScAcc (IoRS (st := st) K Locks s) (IoWS (st := st) K Locks s) (L.mem s (scA (L.mem s (rhA (L := L) s))))
        (Z (L.mem s (scA (L.mem s (rhA (L := L) s))))) := by
  obtain ⟨hT, hsc, -⟩ := bxi_rh P.bxi h0
  obtain ⟨⟨Q, Rq, hq⟩, hb, -, -, -⟩ := P.bxi
  have hrel := hq.release _ hq.cur
  have hd : L.mem s (rhA (L := L) s) = (Rq (L.cpu s)).headD 0#u64 := hrel.head
  have hm : L.mem s (rhA (L := L) s) ∈ Rq (L.cpu s) := by
    cases hl : Rq (L.cpu s) with
    | nil => rw [hl] at hd; exact absurd hd h0
    | cons r rs => rw [hl] at hd; rw [hd]; simp
  have haff := hq.inR _ hq.cur _ hm
  have hne := hb.r _ hT ((hq.released _ hT).2 (by rw [haff]; exact hm))
  exact ⟨hsc, P.scacc hsc ((P.affSc _ hT hne).trans haff)⟩

variable {t ptr dest r n : U64}

/-- **`VmTailAcc` for the VM path's sets** at the state after the entry's `update_timestamp`
(`utW s n`), from `VmBase` at the entry, `VmMidF` and the ASID words (`hTab`). -/
theorem VmMidF.tailAcc (P : VmBase st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (M : VmMidF st K T H Rp Locks s (utW (L := L) s n) t ptr dest r)
    (hTab : RdTab (L := L) (IoRS (st := st) K Locks s) s)
    (hAs : AsidOff (L := L) Ω Sg (utW (L := L) s n))
    (hsc0 : L.mem (utW (L := L) s n) (scA dest) ≠ 0#u64) {W : U64 → Prop}
    (hW : ∀ b, VmWd K b → IoWS (st := st) K Locks s b → W b) :
    VmTailAcc (L := L) Z (IoRS (st := st) K Locks s) W (utW (L := L) s n) dest := by
  have hN := P.np
  have hT := P.tp
  obtain ⟨⟨Q, Rq, hq⟩, -, ⟨hO, -, hX⟩, -, -⟩ := P.bxi
  have hcC : L.cpu s ∈ Cs := hq.cur
  have hX0 : ScExtra0 st T Cs Scs Nt s := hX.toScExtra0
  have esc : L.mem (utW (L := L) s n) (scA dest) = L.mem s (scA dest) :=
    ut_tcb hN hT n M.dT (Kx := 3464#u64) (by simp) (by simp)
  have hne : L.mem s (scA dest) ≠ 0#u64 := by rw [← esc]; exact hsc0
  have hdsc : L.mem s (scA dest) ∈ Scs := (hX0.bound dest M.dT hne).1
  have hacc := P.scacc (Locks := Locks) hdsc ((P.affSc dest M.dT hne).trans M.aff)
  have etm : L.mem (utW (L := L) s n) (tmA (L := L) (utW (L := L) s n)) = L.mem s (tmA (L := L) s) := by
    show L.mem (utW (L := L) s n) (L.nodeAt (utW (L := L) s n) (L.cpu (utW (L := L) s n)) layout.node.TIMER_MIN) = _
    rw [ut_nodeAt]
    exact ut_node hN n (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      (by simp [layout.node.TIMER_MIN, layout.node.CUR_TIME]) (by simp [layout.node.TIMER_MIN, layout.node.CONSUMED])
  have erh : L.mem (utW (L := L) s n) (rhA (L := L) (utW (L := L) s n)) = L.mem s (rhA (L := L) s) := by
    show L.mem (utW (L := L) s n) (L.nodeAt (utW (L := L) s n) (L.cpu (utW (L := L) s n)) layout.node.RELEASE_HEAD) = _
    rw [ut_nodeAt]
    exact ut_node hN n (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD, layout.node.CUR_TIME])
      (by simp [layout.node.RELEASE_HEAD, layout.node.CONSUMED])
  refine
  { nd := fun o ho h8 => ⟨(M.nd P o ho h8).1, hW _ (by rw [M.c, nodeAt_of_ksb M.k]; exact P.wdNode ho) (M.nd P o ho h8).2⟩
    dt := by rw [utW_ksb]; exact P.ksw (by simp [layout.ks.DOMAIN_TIME]) (by simp [layout.ks.DOMAIN_TIME])
    kr := by unfold krA; rw [utW_ksb]; exact P.ksw (by simp [layout.ks.KERNEL_ROOT]) (by simp [layout.ks.KERNEL_ROOT])
    tab := ?_
    dvt := P.tslot M.dT (tcb_slot_eq dest layout.tcb.SLOT_VTABLE) (by simp [layout.tcb.SLOT_VTABLE])
    dsc0 := P.gate (off := 3464#u64) M.dT (by simp) (by simp) (by simp) (by simp [GateField])
    diq := (M.dh P (off := 3592#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])
      (by simp [GField])).1
    dyt := (M.dh P (off := 3472#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])
      (by simp [GField])).1
    dst := by
      rw [stA_eq]
      exact (M.dh P (off := 3328#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])
        (by simp [GField])).1
    dfi := (P.regOf M.dT M.aff (r := layout.reg.FAULT_IP) (by simp [layout.reg.FAULT_IP])).1
    dni := hW _ (P.wdReg M.dT (r := layout.reg.NEXT_IP) (by simp [layout.reg.NEXT_IP]))
      (P.regOf M.dT M.aff (r := layout.reg.NEXT_IP) (by simp [layout.reg.NEXT_IP])).2
    dsw := ⟨hW _ (P.wdTcb (off := 3480#u64) M.dT (by simp) (by simp) (by simp))
      (M.dh P (off := 3480#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])
      (by simp [GField])).2,
      hW _ (P.wdTcb (off := 3488#u64) M.dT (by simp) (by simp) (by simp))
      (M.dh P (off := 3488#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])
        (by simp [GField])).2⟩
    spo := by
      rw [esc]
      have hw := sc_word_in hO hdsc (o := layout.sc.SPORADIC) (by simp [layout.sc.SPORADIC])
        (by simp [layout.sc.SPORADIC])
      exact hacc.rd _ hw.1 hw.2
    dsc := by rw [esc]; exact P.scaccW hW hdsc hacc
    csc := by rw [ut_csc hN n]; exact P.scaccW hW P.cscS P.cscacc
    tm := fun h0 => by rw [etm] at h0 ⊢; exact P.td h0
    rh := fun h0 => by
      rw [erh] at h0 ⊢
      obtain ⟨hrT, -, -⟩ := bxi_rh P.bxi h0
      have e1 : L.mem (utW (L := L) s n) (scA (L.mem s (rhA (L := L) s))) =
          L.mem s (scA (L.mem s (rhA (L := L) s))) :=
        ut_tcb hN hT n hrT (Kx := 3464#u64) (by simp) (by simp)
      rw [e1]
      obtain ⟨hqS, hqA⟩ := P.rsAcc (Locks := Locks) h0
      exact ⟨(P.rs h0).1, hqA.rd, rdHead_ut P.bxi n hqS (P.rs h0).2⟩ }
  intro hi hhi
  have hA1 := hAs hi hhi
  rw [utW_ksb] at hA1 ⊢
  have e : L.mem (utW (L := L) s n) (atAF (L.ksb s) hi) = L.mem s (atAF (L.ksb s) hi) :=
    ut_out hN hcC n (hq.omega _ hA1.1)
  rw [e]
  exact hTab hi hhi

/-- **The accepted VM-fault local path on any store `gS`** answering `IoRS K Locks s` words as `st`,
the `VmWd` words of `IoWS K Locks s` (`hW`) and the `STATE` writes (`VmSW`) as `st`: an accepted run
on `gS` ends exactly as the real run (`vm_acc` for `PathObl.guard`, `vm_acc_gd` for p2sl's `gd`). Premises
(module docstring): `VmFPre`'s and `hTab` [J] (the ASID table at `ks_base + 288000` and the ASID
pool words are readable: no typed object covers them, so they are gate-owned; discharge = extend
`IoLay` / the ownership map to that kernel-state region). -/
theorem vm_accG {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s' : S} {a a' : A}
    {addr code : U64} (P : VmFPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s)
    (hTab : RdTab (L := L) (IoRS (st := st) K Locks s) s)
    {gS : machine.Store S} {W : U64 → Prop} [GRd gS st (IoRS (st := st) K Locks s)] [GWr gS st W]
    (hW : ∀ b, VmWd K b → IoWS (st := st) K Locks s b → W b) (hSW : VmSW st gS T Locks s)
    (h : syscall.handle_vm_fault_local st ar s a addr code = ok (true, s', a')) :
    syscall.handle_vm_fault_local gS ar s a addr code = ok (true, s', a') := by
  have B := P.base
  have hN := B.np
  have hT := B.tp
  refine vm_acc_of_tail hA P hW hSW ?_ h
  intro s1 a1 t ins ptr badge dest r s14 eu et C e14 h3
  have et' : t = L.curW s1 := by rw [cur_thread_ok] at et; exact (ok_inj_ff et).symm
  have hlk := P.lk a s1 a1 ptr badge dest r eu (by rw [← et']; exact C)
  have HY := P.hyp a s1 a1 eu
  have hy0 := P.hyt a s1 a1 ptr badge dest r eu (by rw [← et']; exact C)
  obtain ⟨⟨n, a2⟩, hn, -⟩ := spec_ex_fd (hA.now a)
  rw [update_timestamp_ok ar hN hn] at eu
  have eS := (Prod.mk.inj (ok_inj_ff eu)).1
  subst eS
  have hF := faultEntAt_ofT HY.bxi et HY.nb HY.cap HY.user HY.buf HY.asid
  obtain ⟨hr, rest, E⟩ := hF.2 ptr badge dest r C
  have hrecv := faultRecv_ofT HY.bxi et HY.cap C
  have hpH : H ptr = some .ep := by
    obtain ⟨sl, x, y, g, gr, esl, ecap, -⟩ := C.cap
    have h1 := HY.cap
    rw [← et', esl, WP.spec_ok, ecap, WP.spec_ok] at h1
    exact h1.1 ptr badge x y g gr rfl
  have hhd : dest = L.mem (utW (L := L) s n) (epHeadA ptr) := by
    have h1 := C.head
    rw [eq_of_spec_fd (obj.Ep.head.spec' (L := L) _ ptr)] at h1; exact (ok_inj_ff h1).symm
  have hQ := vm_queue HY.bxi hpH E.hst hhd hrecv
  have hdT : dest ∈ T := E.hq.mem dest (by simp)
  have HF := here_facts (L := L) C.here
  have hrP : r.val % 32 = 0 ∧ r.val + 32 ≤ 2 ^ 64 := by
    obtain ⟨-, -, hX, -, -⟩ := HY.bxi; exact hX.1.rp r hr
  have M : VmMidF st K T H Rp Locks s (utW (L := L) s n) t ptr dest r :=
    { k := utW_ksb s n
      c := utW_cpu s n
      cur := by rw [et', ut_cur hN n]
      tT := E.ht
      dT := hdT
      hT := hT
      hN := hN
      ep := E.hE
      epK := P.hEp ptr hpH
      rK := P.hRp r hr
      rP := hrP
      lp := hlk.1
      lr := hlk.2
      aff := by
        have e := ut_tcb hN hT n hdT (Kx := 3520#u64) (by simp) (by simp)
        calc L.mem s (affA dest) = L.mem (utW (L := L) s n) (affA dest) := e.symm
          _ = L.cpu (utW (L := L) s n) := HF.aff
          _ = L.cpu s := utW_cpu s n
      q := fun y hy => by
        obtain ⟨hyT, hb, hs⟩ := hQ y hy
        refine ⟨hyT, ?_, ?_⟩
        · rw [← hb, blockA_eq]; exact (ut_tcb hN hT n hyT (by simp) (by simp)).symm
        · rw [← hs, stA_eq]; exact (ut_tcb hN hT n hyT (by simp) (by simp)).symm }
  have hyX : L.mem (utW (L := L) s n) (yieldA dest) = 0#u64 := by
    rw [show yieldA dest = core.num.U64.wrapping_add dest 3472#u64 from rfl,
      ut_tcb hN hT n hdT (Kx := 3472#u64) (by simp) (by simp)]
    exact hy0
  exact faultTail3.guardVm (gS := gS) ar hA HY.bxi
    hF C hrecv hyX (M.tailAcc B hTab HY.asid HF.sc hW) (hSW dest _ hdT M.aff
      (fun _ => by rw [(M.q dest (Or.inl rfl)).2.1]; exact M.lp) (Or.inr (Or.inl rfl))) e14 h3

/-- **The accepted VM-fault local path on the guarded store** (`acc` for `handle_vm_fault_local`):
an accepted run on `PathObl.guard st (IoRS K Locks s) (IoWS K Locks s)` ends exactly as the real run
(`vm_accG`). Premises (module docstring): `VmFPre`'s and `hTab` [J]. -/
theorem vm_acc {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s' : S} {a a' : A}
    {addr code : U64} (P : VmFPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s)
    (hTab : RdTab (L := L) (IoRS (st := st) K Locks s) s)
    (h : syscall.handle_vm_fault_local st ar s a addr code = ok (true, s', a')) :
    syscall.handle_vm_fault_local (PathObl.guard st (IoRS (st := st) K Locks s) (IoWS (st := st) K Locks s)) ar s a addr code =
      ok (true, s', a') := by
  refine vm_accG (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoWS (st := st) K Locks s)) hA P hTab
    (fun _ _ hb => hb) ?_ h
  intro d v hd haff _ _
  have e : core.num.U64.wrapping_add d layout.tcb.STATE = core.num.U64.wrapping_add d 3328#u64 := stA_eq d
  refine SWr.of_W (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoWS (st := st) K Locks s)) ?_
  rw [e]
  exact (P.base.homeOf hd haff (off := 3328#u64) (by simp) (by simp) (by simp) (by simp [GateField])
    (by simp [TimerField]) (by simp [GField])).2

end

end Fl4Proofs.P2.PathObl
