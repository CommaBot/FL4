/-
P3 (line stpost, generation 3): **the ReplyRecv dispatch at stable ghosts**, the receive named.

KEntry38's `mid_invRecvJMUNM` / `dispatch_midJMUNM` restricted to ReplyRecv with a Reply cap in the
REPLY register (StPostInv's `handle_invocation_replyJSt`): the first phase ends at `JStabM Z H Cs`
and is never preempted, so the dispatch has a single (`.ok`) outcome kind.

* `JStabR`: `JStab` with `JAtZR` (the receive's exit form, as `DispPostRM`'s `JAtZR`).
* `JMidRecvHypSt` **[W]**: the receive at a mid state with the stable ghosts: the stable-post
  analogue of KEntry8's `JMidRecvHyp` (which P3 discharges through `jMidRecvHyp_of` /
  `jMidRecvHypS_of` and the `jMidLeavesHyp_of*` chain, all at `JAt`). Discharging it needs stable
  copies of `handle_recvJ` and of that chain (or the fast path's idle-endpoint block only:
  handoff, generation 3). l4v: `receive_ipc_corres` / `handle_recv_corres` with `invs` kept.
* `mid_invRecvReplyJSt`, `dispatch_replyRecvJSt`: the ReplyRecv arm of `dispatch_syscall` against
  `fl4HandleSyscall true .sysReplyRecv`: one `.ok` outcome with `RelTopM`, `JStabR Z H Cs` and `MR`.
  Premises: `handle_invocation_replyJSt`'s, `hnf` (JEntryAt's `cnf`), `hW` (`JMidPerfHyp`, as
  `dispatch_midJMUNM`) and `hRS` [W].
-/
import Fl4Proofs.P3.StPostInv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section StMidA
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

/-- (stpost) **`JStab` at `JAtZR`** (module docstring). -/
def JStabR (arI : machine.Arch A) (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  ∃ (G : MdbGhost) (V : XVs) (Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    JAtZR (L := L) arI AR (Z.mv G V) H Cs Ac Lst D s a σ

/-- **[W] The receive at a mid state, stable ghosts** (module docstring): every `.ok` outcome of
the first-phase invocation from `σ`, at every FL4 state related to it with `JStab Z H Cs`, the
current thread running and not idle. -/
def JMidRecvHypSt (arI : machine.Arch A) (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap)
    (Cs : Set U64) (cptr : Fl4Spec.CapRef) (cr : Bool) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ y ∈ ((Fl4Spec.fl4HandleInvocationR (Z := Unit) true false false true true cptr).run σ).1, y.1 = .ok () →
    ∀ (s1 : S) (a1 : A), RelTopM (L := L) s1 y.2 → JStab (L := L) arI AR Z H Cs s1 a1 y.2 → CurRun y.2 →
      y.2.curThread ≠ y.2.idleThread →
      syscall.handle_recv st arI s1 a1 true cr ⦃ r => ∃ z ∈ (Fl4Spec.handleRecv (Z := Unit) true cr y.2).1,
        RelTopM (L := L) r.1 z.2 ∧ JStabR (L := L) arI AR Z H Cs r.1 r.2 z.2 ⦄

end StMidA

section StMidB
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- (stpost) **The ReplyRecv invocation then receive at stable ghosts** (module docstring;
`mid_invRecvJMUNM` for the Reply cap). -/
theorem mid_invRecvReplyJSt [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z] (hni : Entered σ)
    (hnf : ∀ x, σ.kheap σ.curThread = some (.tcb x) → x.tcbFault = none)
    (hA : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ (a : A) v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hM : MachPlat arI MR) (hKD : MRKeepD arI MR) (hR0 : MR ar σ.machineState)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (cr : Bool)
    (found : cspace.Resolved)
    (hls : cspace.lookup_slot st s ct (L.mem s (regA ct layout.reg.REPLY)) = ok (.Ok found))
    {rptr : U64} {g : Bool} (hcap : obj.Slot.cap st found.slot s = ok (.Reply rptr g))
    (hW : MidRun.JMidPerfHyp true (Fl4Spec.toBl (L.mem s (regA ct layout.reg.REPLY)).bv) σ)
    (hRS : JMidRecvHypSt (L := L) arI AR Z H Cs (Fl4Spec.toBl (L.mem s (regA ct layout.reg.REPLY)).bv) cr σ) :
    (do
      let (r, s1, a1) ← syscall.handle_invocation st arI s ar false false true true (L.mem s (regA ct layout.reg.REPLY))
      let (b, s2, a2) ← syscall.after_invocation st arI s1 a1 r
      if b then syscall.handle_recv st arI s2 a2 true cr else ok (s2, a2)) ⦃ r =>
      ∃ y ∈ ((DispMid Fl4Spec.replyRegister cr).run σ).1, y.1 = .ok () ∧ RelTopM (L := L) r.1 y.2 ∧
        JStabR (L := L) arI AR Z H Cs r.1 r.2 y.2 ∧ MR r.2 y.2.machineState ⦄ := by
  obtain ⟨hcur, -⟩ := J.curEq hct
  obtain ⟨-, xs, hks⟩ := J.xtop.curTcb hcur
  have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hxs := (J.xtop.irelK J.ks J.buf).1.toE.at_tcb hctT hks
  have hcp : Fl4Spec.dataToCptr (xs.tcbArch.tcbContext.userRegs Fl4Spec.replyRegister) =
      Fl4Spec.toBl (L.mem s (regA ct layout.reg.REPLY)).bv := by
    rw [← regIdx_reply, hxs.regs]; rfl
  have hk' : σ.kheap σ.curThread = some (.tcb xs) := by rw [hcur]; exact hks
  have hreg := mem_getCapReg hk' Fl4Spec.replyRegister
  rw [hcp] at hreg
  have hME := J.midEntry hni hnf
  refine WP.spec_bind (handle_invocation_replyJSt s ar σ J hA hmax htu hmb hM hKD hni hR0 ct hct true true _
    found hls hcap) ?_
  rintro ⟨r, s1, a1⟩ ⟨⟨y1, σm⟩, hy, hc, hrel, hX⟩
  rcases hc with ⟨hr1, hy1⟩ | ⟨hr1, -⟩
  swap
  · dsimp only at hr1; subst hr1; rw [if_pos rfl] at hX; exact hX.elim
  dsimp only at hr1 hy1
  subst hr1 hy1
  rw [if_neg (fun h => by cases h)] at hX
  obtain ⟨hJs, hMm⟩ := hX
  have hC : CurRun σm := MidRun.jMidRunHyp_of hW hME _ hy rfl
  have hid : σm.curThread ≠ σm.idleThread := by
    obtain ⟨_, _, _, _, _, J'⟩ := hJs; exact curRun_ne_idle hC J'.act.2
  show (do
    let (b, s2, a2) ← syscall.after_invocation st arI s1 a1 (.Ok ())
    if b then syscall.handle_recv st arI s2 a2 true cr else ok (s2, a2)) ⦃ _ ⦄
  rw [show syscall.after_invocation st arI s1 a1 (.Ok ()) = ok (true, s1, a1) by
    unfold syscall.after_invocation; rfl, bind_ok]
  show (if true = true then syscall.handle_recv st arI s1 a1 true cr else ok (s1, a1)) ⦃ _ ⦄
  rw [if_pos rfl]
  refine WP.spec_mono (spec_mrz hM (hRS _ hy rfl s1 a1 hrel hJs hC hid) (MKD.syscall_handle_recv L.total hA hKD hMm)
    (fun z hz => congrArg Prod.fst (MachT.mtk_handleRecvG true cr _ z hz))) ?_
  rintro r ⟨z, hz, ⟨hrl, hJ⟩, hMz⟩
  exact ⟨(.ok z.1, z.2), mem_bindE_ok (mem_liftE (ε := Unit) hreg) (mem_bindE_ok hy (mem_liftE hz)),
    rfl, hrl, hJ, hMz⟩

set_option maxHeartbeats 4000000 in
/-- (stpost) **`dispatch_syscall` for `SysReplyRecv` with a Reply cap, stable ghosts**
(`dispatch_midJMUNM`'s ReplyRecv case at `mid_invRecvReplyJSt`). -/
theorem dispatch_replyRecvJSt [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z] (hni : Entered σ)
    (hnf : ∀ x, σ.kheap σ.curThread = some (.tcb x) → x.tcbFault = none)
    (hA : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ (a : A) v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hM : MachPlat arI MR) (hKD : MRKeepD arI MR) (hR0 : MR ar σ.machineState)
    (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (found : cspace.Resolved)
    (hls : cspace.lookup_slot st s ct (L.mem s (regA ct layout.reg.REPLY)) = ok (.Ok found))
    {rptr : U64} {g : Bool} (hcap : obj.Slot.cap st found.slot s = ok (.Reply rptr g))
    (hW : MidRun.JMidPerfHyp true (Fl4Spec.toBl (L.mem s (regA ct layout.reg.REPLY)).bv) σ)
    (hRS : JMidRecvHypSt (L := L) arI AR Z H Cs (Fl4Spec.toBl (L.mem s (regA ct layout.reg.REPLY)).bv) true σ) :
    syscall.dispatch_syscall st arI s ar fl4_abi.syscall.SysReplyRecv ⦃ r =>
      ∃ y ∈ ((Fl4Spec.fl4HandleSyscall (Z := Unit) true .sysReplyRecv).run σ).1, y.1 = .ok () ∧
        RelTopM (L := L) r.1 y.2 ∧ JStabR (L := L) arI AR Z H Cs r.1 r.2 y.2 ∧ MR r.2 y.2.machineState ⦄ := by
  have hn : MidSysR fl4_abi.syscall.SysReplyRecv .sysReplyRecv layout.reg.REPLY Fl4Spec.replyRegister true :=
    Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩
  have h := mid_invRecvReplyJSt s ar σ J hni hnf hA hmax htu hmb hM hKD hR0 ct hct true found hls hcap hW hRS
  rw [fl4HandleSyscall_mid hn]
  unfold syscall.dispatch_syscall
  rw [hct]; simp only [bind_ok]
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s ct layout.reg.CAP) ?_
  rintro c0 -
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s ct layout.reg.REPLY) ?_
  rintro c1 rfl
  rw [if_neg (show fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysSend by unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysSend; decide), if_neg (show fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysNBSend by unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysNBSend; decide), if_neg (show fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysCall by unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysCall; decide), if_neg (show fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysRecv by unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysRecv; decide), if_neg (show fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysNBRecv by unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysNBRecv; decide), if_neg (show fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysWait by unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysWait; decide), if_neg (show fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysNBWait by unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysNBWait; decide), if_pos trivial]
  exact h

end StMidB

end

end Fl4Proofs.P3
