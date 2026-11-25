/-
P3 (line stpost, generation 5): **the accepted I/O port entry beside the gate at stable ghosts**
(the ReplyRecv route of StPostInv / StPostRRTop / StPostRRReach for `handle_ioport_local`).

`handle_ioport_local` (fl4-sync's `local_syscall`: `SysCall` / `SysSend` on an I/O port label) is,
where it returns `true`, the general entry (P1 `ioport_local_same`): `FAULT_IP`, `budget_ok`,
`dispatch_syscall`'s invoking arm (`handle_invocation call true call false cptr`, `after_invocation`),
`finish`. The general entry's invocation decodes the cap in the `CAP` register over every cap type
(XTopJointKEntry38's `handle_invocation_entryJMUM`, whose Untyped arm grows the ghosts); the local entry
runs only where `ioport.invocation_ok` holds at the dispatch state, i.e. where that cap is an I/O port
cap. So:

* `P1.invocation_ok_cap`: `ioport.invocation_ok … = ok true` ⇒ `lookup_slot` found a slot holding an
  `IoPort` cap. `P1.ioport_local_acc`: an accepted `handle_ioport_local` has number `SysCall` or
  `SysSend`, and at the general entry's dispatch state (after its `FAULT_IP` write and passing
  `budget_ok`) the current thread is unchanged and the `CAP` register names an `IoPort` cap
  (`ioport_local_same`'s walk, `prefix_cur_keep`).
* `nativeSys_invC`: the spec syscall of an invoking number is `invSysOf`.
* `handle_invocation_ioportJSt`: `handle_invocation call true don false cptr` at `J` with the found
  `IoPort` cap (`hls`, `hcap`): `refinesMXPF` (StPostInv) at `X := JStabM Z H Cs`, `XP := False`; the
  extra-caps fault by StPostFault's `faultHypJZGSt`, the success / error tails by StPostIoLeaf's
  `flTailJSt` / `replyFailJSt`, the decode by StPostIoLeaf's `decode_invocation_ioportJ_stepsSt`
  (every label: errors, `Out`, `In`; no ghost change: the primitive steps keep `H`, `Cs`, the reply
  writes registers of the caller) with `MR` by `XCapP.mr` (`MKD.decode_ioport`, `MRKeepIo` [P]).
  The owner field of the cap is `0` by `JExt.nat`. Never preempted.
* `dispatch_ioportJSt`: `dispatch_syscall` for `SysCall` / `SysSend` with that cap: one `.ok` outcome
  of `fl4HandleSyscall true (invSysOf call true)` with `RelTopM`, `JStab Z H Cs`, `MR`.
* `kernel_entry_ioSt`: the general path `handle_syscall_old` (StPostRRTop's `kernel_entry_rrSt` with
  the dispatch above; the dispatch state's `vfh`, `ctnq`, `SpecGlob` from `SInvB` as
  `KDispHypsKV27.to26`), given `hio` (the cap fact at the dispatch state).
* **`kernel_entry_io_localSt17`**: from `JReachU17` and given `JAtZ Z H Cs` (with `VxE Z`), under
  U29I's clause inputs that this route reads (`hct`, `hn : NativeSys n c`, `hflag`, `hFin` at
  `KFinAtR13`; not `hK` / `hDec`), an accepted `handle_ioport_local … n` ends at a
  `fl4KernelEntrySyscall true c` outcome that is `JReachU17` **and** `JStab Z H Cs`.

Premises: U29I's (a subset: the platform facts, with `hIo : MRKeepIo` and `hPI : PortInValMR` that
U29 already has); no new premise.
-/
import Fl4Proofs.P3.StPostIoLeaf
import Fl4Proofs.P3.StPostRRReach
import Fl4Proofs.P1.FastIoLocal
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {A : Type _} {st : machine.Store S} (ar : machine.Arch A) [L : LawfulStore st]

/-- (stpost) **An accepted `invocation_ok` found an I/O port cap** (module docstring). -/
theorem invocation_ok_cap {s : S} {t cptr : U64} {info : msginfo.MessageInfo}
    (h : ioport.invocation_ok st s t cptr info = ok true) :
    ∃ (found : cspace.Resolved) (pf pl pz : U64), cspace.lookup_slot st s t cptr = ok (.Ok found) ∧
      obj.Slot.cap st found.slot s = ok (.IoPort pf pl pz) := by
  unfold ioport.invocation_ok at h
  obtain ⟨size, -, h⟩ := bind_eq_ok h
  by_cases h0 : size = 0#u64
  · rw [if_pos h0] at h; simp at h
  rw [if_neg h0] at h
  obtain ⟨r, er, h⟩ := bind_eq_ok h
  cases r with
  | Err _ => simp at h
  | Ok r1 =>
    try simp only at h
    by_cases hb : (r1.bits_left != 0#u64) = true
    · rw [if_pos hb] at h; simp at h
    rw [if_neg hb] at h
    obtain ⟨c, ec, h⟩ := bind_eq_ok h
    cases c <;> (try simp at h)
    all_goals exact ⟨r1, _, _, _, er, ec⟩

set_option maxHeartbeats 1600000 in
/-- (stpost) **An accepted I/O port run beside the gate: its number, and the cap at its dispatch
state** (module docstring; `ioport_local_same`'s walk). -/
theorem ioport_local_acc (hA : P0.ArchTotal ar) {T Cs Sg : Set U64} {s s' : S} {a a' : A} {number : I64}
    {Ω Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (h : syscall.handle_ioport_local st ar s a number = ok (true, s', a')) :
    (number = fl4_abi.syscall.SysCall ∨ number = fl4_abi.syscall.SysSend) ∧
    ∀ ct nx s2 a2, sched.cur_thread st s = ok ct → obj.Tcb.reg st ct s layout.reg.NEXT_IP = ok nx →
      syscall.budget_ok st ar (L.wr s (regA ct layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx 2#u64)) a =
        ok (true, s2, a2) →
      sched.cur_thread st s2 = ok ct ∧ ∃ (found : cspace.Resolved) (pf pl pz : U64),
        cspace.lookup_slot st s2 ct (L.mem s2 (regA ct layout.reg.CAP)) = ok (.Ok found) ∧
        obj.Slot.cap st found.slot s2 = ok (.IoPort pf pl pz) := by
  obtain ⟨⟨Q, R, hSQ⟩, -, -, -, -⟩ := hI
  have hT : TcbPlaced T := hSQ.tcbs
  have hcC : L.cpu s ∈ Cs := hSQ.cur
  have hN : NodePlaced st T s (L.cpu s) := hSQ.nodes _ hcC
  have hcT : L.curW s ∈ T := hSQ.curT
  unfold syscall.handle_ioport_local at h
  try simp only [lift, bind_ok] at h
  obtain ⟨t, et, h⟩ := bind_eq_ok h
  obtain ⟨info, -, h⟩ := bind_eq_ok h
  rw [num_domains_ne_one_false] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨i, -, h⟩ := bind_eq_ok h
  by_cases c1 : (i &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true
  · rw [if_pos c1] at h; simp at h
  rw [if_neg c1] at h
  have hn : number = fl4_abi.syscall.SysCall ∨ number = fl4_abi.syscall.SysSend := by
    by_cases hc : (number != fl4_abi.syscall.SysCall) = true
    · rw [if_pos hc] at h
      by_cases hs : (number != fl4_abi.syscall.SysSend) = true
      · rw [if_pos hs] at h; simp at h
      · simp only [bne_iff_ne, ne_eq, not_not] at hs; exact Or.inr hs
    · simp only [bne_iff_ne, ne_eq, not_not] at hc; exact Or.inl hc
  refine ⟨hn, fun ct nx s2 a2 hct hnx hb2 => ?_⟩
  have e1 : ct = t := ok_inj_ff (hct.symm.trans et)
  rw [e1] at hnx hb2 ⊢
  have htT : t ∈ T := by
    rw [cur_thread_ok] at et; rw [← ok_inj_ff et]; exact hcT
  by_cases hc : (number != fl4_abi.syscall.SysCall) = true
  on_goal 2 => rw [if_neg hc] at h
  on_goal 1 =>
    rw [if_pos hc] at h
    by_cases hs : (number != fl4_abi.syscall.SysSend) = true
    on_goal 1 => rw [if_pos hs] at h; simp at h
    rw [if_neg hs] at h
  all_goals
    obtain ⟨b, -, h⟩ := bind_eq_ok h
    cases b
    · simp at h
    simp only [↓reduceIte] at h
    obtain ⟨nx', enx, h⟩ := bind_eq_ok h
    obtain ⟨s1, es1, h⟩ := bind_eq_ok h
    obtain ⟨⟨s2', a1⟩, eu, h⟩ := bind_eq_ok h
    try simp only [uncurry_apply_pair] at h
    try dsimp only at h
    obtain ⟨cptr, ecp, h⟩ := bind_eq_ok h
    obtain ⟨csc, ecsc, h⟩ := bind_eq_ok h
    obtain ⟨i3, -, h⟩ := bind_eq_ok h
    by_cases g3 : (i3 != sched.ACTION_RESUME_CURRENT) = true
    · rw [if_pos g3] at h; simp at h
    rw [if_neg g3] at h
    obtain ⟨i4, -, h⟩ := bind_eq_ok h
    by_cases g4 : (i4 != 0#u64) = true
    · rw [if_pos g4] at h; simp at h
    rw [if_neg g4] at h
    by_cases g5 : (info.extra_caps != 0#u64) = true
    · rw [if_pos g5] at h; simp at h
    rw [if_neg g5] at h
    obtain ⟨b1, eio, h⟩ := bind_eq_ok h
    cases b1
    · simp at h
    simp only [↓reduceIte] at h
    obtain ⟨c, ec, h⟩ := bind_eq_ok h
    obtain ⟨b2, eb, h⟩ := bind_eq_ok h
    cases b2
    · simp at h
    have hb : syscall.budget_ok st ar s1 a = ok (true, s2', a1) := by
      unfold syscall.budget_ok
      rw [eu]; simp only [bind_ok, uncurry_apply_pair]
      exact check_budget_restart_suf ar ecsc ec eb
    have et2 := prefix_cur_keep ar hT hN et htT es1 hb hA
    have e2 : nx = nx' := ok_inj_ff (hnx.symm.trans enx)
    subst e2
    have hs1 := set_fip_wr (hT t htT) es1
    rw [← hs1, hb] at hb2
    have e3 := ok_inj_ff hb2
    simp only [Prod.mk.injEq] at e3
    obtain ⟨-, rfl, rfl⟩ := e3
    rw [reg_ok] at ecp
    have ecp' := (ok_inj_ff ecp).symm
    subst ecp'
    exact ⟨et2, invocation_ok_cap eio⟩

end

end Fl4Proofs.P1

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

/-- (stpost) **The spec syscall of an invoking number** (module docstring). -/
theorem nativeSys_invC {n : I64} {c : Fl4Spec.Syscall} {call bl don : Bool} (h : NativeSys n c)
    (hi : InvSys n call bl don) : c = invSysOf call bl := by
  rcases h with ⟨call', bl', don', hi', rfl⟩ | ⟨bl', cr, hr, rfl⟩ | ⟨he, rfl⟩ | hm
  · rcases hi with ⟨e1, rfl, rfl, -⟩ | ⟨e1, rfl, rfl, -⟩ | ⟨e1, rfl, rfl, -⟩ <;>
    rcases hi' with ⟨e2, rfl, rfl, -⟩ | ⟨e2, rfl, rfl, -⟩ | ⟨e2, rfl, rfl, -⟩ <;>
    first
    | rfl
    | (exfalso; rw [e1] at e2; revert e2
       simp only [fl4_abi.syscall.SysCall, fl4_abi.syscall.SysSend, fl4_abi.syscall.SysNBSend] <;> decide)
  · exfalso
    rcases hi with ⟨e1, -⟩ | ⟨e1, -⟩ | ⟨e1, -⟩ <;>
    rcases hr with ⟨e2, -⟩ | ⟨e2, -⟩ | ⟨e2, -⟩ | ⟨e2, -⟩ <;>
    (rw [e1] at e2; revert e2
     simp only [fl4_abi.syscall.SysCall, fl4_abi.syscall.SysSend, fl4_abi.syscall.SysNBSend,
       fl4_abi.syscall.SysRecv, fl4_abi.syscall.SysNBRecv, fl4_abi.syscall.SysWait, fl4_abi.syscall.SysNBWait] <;>
       decide)
  · exfalso
    rcases hi with ⟨e1, -⟩ | ⟨e1, -⟩ | ⟨e1, -⟩ <;>
    (rw [e1] at he; revert he
     simp only [fl4_abi.syscall.SysCall, fl4_abi.syscall.SysSend, fl4_abi.syscall.SysNBSend,
       fl4_abi.syscall.SysYield] <;> decide)
  · exfalso
    rcases hi with ⟨e1, -⟩ | ⟨e1, -⟩ | ⟨e1, -⟩ <;>
    rcases hm with ⟨e2, -⟩ | ⟨e2, -⟩ | ⟨e2, -⟩ <;>
    (rw [e1] at e2; revert e2
     simp only [fl4_abi.syscall.SysCall, fl4_abi.syscall.SysSend, fl4_abi.syscall.SysNBSend,
       fl4_abi.syscall.SysReplyRecv, fl4_abi.syscall.SysNBSendRecv, fl4_abi.syscall.SysNBSendWait] <;> decide)

section StIoInv
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 8000000 in
/-- (stpost) **The invocation of an I/O port cap at `J`, stable ghosts** (module docstring). -/
theorem handle_invocation_ioportJSt [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z]
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR)
    (hIo : MRKeepIo arI MR) (hPI : PortInValMR arI MR) (hni : Entered σ)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hvfh : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler)
    (hsg : SpecGlob σ) (hR : MR ar σ.machineState)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (is_call can_donate : Bool) (cptr : U64)
    (found : cspace.Resolved) (hls : cspace.lookup_slot st s ct cptr = ok (.Ok found))
    {pf pl pz : U64} (hcap : obj.Slot.cap st found.slot s = ok (.IoPort pf pl pz)) :
    syscall.handle_invocation st arI s ar is_call true can_donate false cptr ⦃ res =>
      HIPostMXP (L := L) (JStabM (L := L) arI AR MR Z H Cs) (fun _ _ _ => False) true σ is_call true can_donate
        false (Fl4Spec.toBl cptr.bv) res ⦄ := by
  obtain ⟨info, mi, buf, buffer, r2, er, argsU, hinfo, hmi, hbuf, hbuffer, hr2, her, hmrs⟩ :=
    JAtZ.frontEx arI J J.xferH.1 J.xferH.2.1 hct
  obtain ⟨hcur, -⟩ := J.curEq hct
  have htcb := (J.xtop.curTcb hcur).1
  have hX := J.xtop
  have hF : ∀ {f : error.Fault} {f' : Fl4Spec.Fault}, CapFaultCorr f f' →
      faults.handle_fault st arI s ar ct f ⦃ r => ∃ z ∈ (Fl4Spec.handleFault (Z := Unit) ct.bv f' σ).1,
        RelTopM (L := L) r.1 z.2 ∧ JStabM (L := L) arI AR MR Z H Cs r.1 r.2 z.2 ⦄ := fun hcf =>
    WP.spec_mono (spec_mrz hM (J.faultHypJZGSt hA hni hct hnq hvfh (FaultCorrG.cap hcf))
      (MKD.faults_handle_fault L.total hA hKD hR)
      (fun z hz => congrArg Prod.fst (MachT.mtk_handleFaultG _ _ σ z hz)))
      fun _ ⟨z, hz, ⟨h1, h2⟩, h3⟩ => ⟨z, hz, h1, h2, h3⟩
  refine handle_invocation_refinesMXPF arI (JStabM (L := L) arI AR MR Z H Cs) (fun _ _ _ => False) true s ar σ
    Z.th Z.G hX.rel.1 hX.rel.2.1 hX.rel.2.2.1 hX.rel.2.2.2.1 hX.rel.2.2.2.2.1 ⟨J.stab, hR⟩ ct hct hcur htcb
    is_call true can_donate false cptr found hls info hinfo mi hmi buf hbuf buffer hbuffer r2 hr2 er her
    ((J.extraJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf
      hbuffer hr2 her).imp id fun ⟨f, f', h1, h2, hcf⟩ => ⟨f, f', h1, h2, fun _ => hF hcf⟩)
    (argsU.map UScalar.bv) hmrs
    (fun s1 a1 σ' _ hXs hc => by
      obtain ⟨⟨_, _, _, _, _, J'⟩, hR'⟩ := hXs
      exact WP.spec_mono (WP.spec_and (J'.flTailJSt hc is_call) (MKD.fl_tail L.total hA hKD hR'))
        fun _ ⟨⟨h1, z, hz, h2, h3⟩, h4⟩ => ⟨h1, z, hz, h2, h3.mv, msF_mr hM h4
          (congrArg Prod.fst (MachT.mtk_specTailG _ _ _ σ' z hz))⟩)
    (fun a1 e e' hX1 he => by
      obtain ⟨⟨_, _, _, _, _, J''⟩, hR'⟩ := hX1
      exact WP.spec_mono (WP.spec_and ((J.archJ J''.xtop.fin.1.1.2.2.2.2.2.2).replyFailJSt hcur is_call e e' he)
        (MKD.reply_err_tail (e := e) (t := ct) (s := s) (is_call := is_call) L.total hA hKD hR'))
        fun _ ⟨⟨h1, z, hz, h2, h3⟩, h4⟩ => ⟨h1, z, hz, h2, h3, msF_mr hM h4
          (congrArg Prod.fst (MachT.mtk_when (MachT.mtk_fl4ReplyFromKernelErrorG _ _ _) σ z hz))⟩)
    (fun inv σ1 y hst hy => by
      rw [perfCurKeep _ _ _ inv σ1 y hy]
      obtain ⟨x, hk⟩ := (J.xtop.curTcb hcur).2
      rw [hcur] at hst
      have hm : ((), σ1) ∈ (Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ).1 := by
        rw [hst]; exact Set.mem_singleton _
      rw [Notif.setThreadState_eq .restart hk] at hm
      have e : σ1 = _ := congrArg Prod.snd (Set.mem_singleton_iff.1 hm)
      rw [e, Sched.stsAct_rec]; exact hcur) ?_
  obtain ⟨hLen, hArgs, -⟩ := J.argsJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf hbuffer hmrs
  obtain ⟨hLb, -⟩ := J.frontJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf hbuffer hr2 her
  intro sl c e exs hsl hfs hc hget _ _
  have hc' : c = .IoPort pf pl pz := by
    rw [slot_cap_eq, hfs, hc] at hcap; exact ok_inj hcap
  subst hc'
  have hAs : AbsSlot Z.th sl := by
    obtain ⟨p, hp, hth⟩ := hsl; exact ⟨p, hp, Or.inl hth⟩
  have hsc : capV (L.mem s) (cslotAddr sl) = .IoPort pf pl pz := capV_of_capAt hc
  have hz0 : pz = 0#u64 := by
    have hn := J.ext.nat _ hAs.isSlot
    rw [hsc] at hn; exact hn
  subst hz0
  rw [← hLb]
  exact XCapP.mr hM ((decode_invocation_ioportJ_stepsSt arI s ar σ J hni hARI hA (jStepHyps arI) (J.zNoBlk hsg)
    info.label info.label.bv (port_label _) (msgLen info buf) buf ct hct argsU hLen hArgs sl hAs pf pl hsc is_call
    (fun _ => hPI.at hR) true can_donate false e (Fl4Spec.toBl cptr.bv) exs buffer).toPN arI
    (specDec_noPreK (by trivial)))
    (MKD.decode_ioport L.total hA hKD hIo hR)
    (fun inv hd => MachT.dec_quiet false info.label.bv _ (Fl4Spec.toBl cptr.bv) sl _ exs buffer
      (by simp [absCap, MachT.QuietS]) σ _ hd.1 inv rfl)

set_option maxHeartbeats 8000000 in
/-- (stpost) **`dispatch_syscall` for `SysCall` / `SysSend` with an I/O port cap in `CAP`, stable
ghosts** (module docstring; `dispatch_invokeJMUNM` at `handle_invocation_ioportJSt`). -/
theorem dispatch_ioportJSt [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z]
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR)
    (hIo : MRKeepIo arI MR) (hPI : PortInValMR arI MR) (hni : Entered σ)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hvfh : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler)
    (hsg : SpecGlob σ) (hR : MR ar σ.machineState)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (number : I64) (call don : Bool)
    (hn : InvSys number call true don) (found : cspace.Resolved)
    (hls : cspace.lookup_slot st s ct (L.mem s (regA ct layout.reg.CAP)) = ok (.Ok found))
    {pf pl pz : U64} (hcap : obj.Slot.cap st found.slot s = ok (.IoPort pf pl pz)) :
    syscall.dispatch_syscall st arI s ar number ⦃ r =>
      ∃ y ∈ ((Fl4Spec.fl4HandleSyscall (Z := Unit) true (invSysOf call true)).run σ).1, y.1 = .ok () ∧
        RelTopM (L := L) r.1 y.2 ∧ JStab (L := L) arI AR Z H Cs r.1 r.2 y.2 ∧ MR r.2 y.2.machineState ⦄ := by
  obtain ⟨hcur, -⟩ := J.curEq hct
  obtain ⟨-, xs, hks⟩ := J.xtop.curTcb hcur
  have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hxs := (J.xtop.irelK J.ks J.buf).1.toE.at_tcb hctT hks
  have hcp : Fl4Spec.dataToCptr (xs.tcbArch.tcbContext.userRegs Fl4Spec.cap_register) =
      Fl4Spec.toBl (L.mem s (regA ct layout.reg.CAP)).bv := by
    rw [← regIdx_cap, hxs.regs]; rfl
  have hk' : σ.kheap σ.curThread = some (.tcb xs) := by rw [hcur]; exact hks
  have hreg := mem_getCapReg hk' Fl4Spec.cap_register
  rw [hcp] at hreg
  have hinv : (do
      let (r, s1, a1) ← syscall.handle_invocation st arI s ar call true don false (L.mem s (regA ct layout.reg.CAP))
      let (_, s2, a2) ← syscall.after_invocation st arI s1 a1 r
      ok (s2, a2)) ⦃ r => ∃ y ∈ ((DispInv call true don).run σ).1, y.1 = .ok () ∧
        RelTopM (L := L) r.1 y.2 ∧ JStab (L := L) arI AR Z H Cs r.1 r.2 y.2 ∧ MR r.2 y.2.machineState ⦄ := by
    refine WP.spec_bind (handle_invocation_ioportJSt s ar σ J hARI hA hM hKD hIo hPI hni hnq hvfh hsg hR ct hct
      call don _ found hls hcap) ?_
    rintro ⟨r, s1, a1⟩ ⟨y, hy, hres, hrel, hX⟩
    rcases hres with ⟨rfl, hy1⟩ | ⟨rfl, hy1⟩
    · show (do
        let (_, s2, a2) ← syscall.after_invocation st arI s1 a1 (.Ok ())
        ok (s2, a2)) ⦃ _ ⦄
      rw [show syscall.after_invocation st arI s1 a1 (.Ok ()) = ok (true, s1, a1) by
        unfold syscall.after_invocation; rfl, bind_ok]
      rw [if_neg (fun h => by cases h)] at hX
      exact (WP.spec_ok _).2 ⟨y, mem_bindE_ok (mem_liftE (ε := Unit) hreg) hy, hy1, hrel, hX.1, hX.2⟩
    · rw [if_pos rfl] at hX; exact hX.elim
  rw [fl4HandleSyscall_inv hn]
  unfold syscall.dispatch_syscall
  rw [hct]; simp only [bind_ok]
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s ct layout.reg.CAP) ?_
  rintro c0 rfl
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s ct layout.reg.REPLY) ?_
  rintro c1 -
  have n15 : fl4_abi.syscall.SysCall ≠ fl4_abi.syscall.SysSend := by
    unfold fl4_abi.syscall.SysCall fl4_abi.syscall.SysSend; decide
  have n16 : fl4_abi.syscall.SysCall ≠ fl4_abi.syscall.SysNBSend := by
    unfold fl4_abi.syscall.SysCall fl4_abi.syscall.SysNBSend; decide
  rcases hn with ⟨rfl, rfl, -, rfl⟩ | ⟨-, -, h, -⟩ | ⟨rfl, rfl, -, rfl⟩
  · rw [if_pos rfl]; exact hinv
  · cases h
  · rw [if_neg n15, if_neg n16, if_pos rfl]; exact hinv

end StIoInv

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 16000000 in
/-- (stpost) **The I/O port entry at stable ghosts, where the cap in `CAP` is an I/O port cap**
(module docstring; `kernel_entry_rrSt`'s shape). -/
theorem kernel_entry_ioSt [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] (hni : Entered σ)
    (hR : MR a σ.machineState) (hVI : ValidIrqMasks σ) (hNS0 : NativeScope σ)
    (n : I64) (call don : Bool) (hi : InvSys n call true don)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → KBudgetB arI a (faultIPSt σ σ.curThread x))
    (hS : SInvAll.SInvB σ) (hQ : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hFin : ∀ x ∈ (specFront (invSysOf call true) σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64)
      (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A),
        KFrontF (L := L) arI n s a s' a' →
        JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hio : ∀ ct nx s2 a2, sched.cur_thread st s = ok ct → obj.Tcb.reg st ct s layout.reg.NEXT_IP = ok nx →
      syscall.budget_ok st arI (L.wr s (regA ct layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx 2#u64)) a =
        ok (true, s2, a2) →
      sched.cur_thread st s2 = ok ct ∧ ∃ (found : cspace.Resolved) (pf pl pz : U64),
        cspace.lookup_slot st s2 ct (L.mem s2 (regA ct layout.reg.CAP)) = ok (.Ok found) ∧
        obj.Slot.cap st found.slot s2 = ok (.IoPort pf pl pz))
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hPI : PortInValMR arI MR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.handle_syscall_old st arI s a n ⦃ r =>
      ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true (invSysOf call true) σ).1 ∧
        RJ (L := L) arI AR r.1 r.2 σ' ∧ MR r.2 σ'.machineState ∧ JStab (L := L) arI AR Z H Cs r.1 r.2 σ' ⦄ := by
  have hn : NativeSys n (invSysOf call true) := Or.inl ⟨call, true, don, hi, rfl⟩
  have hct := cur_thread_eq (L := L) s
  generalize L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) = ct at hct
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hI := J.xtop.irelK J.ks J.buf
  obtain ⟨x, hk, hTR⟩ := hI.1.tcb ct hctT
  have hxs := hI.1.toE.at_tcb hctT hk
  have hk' : σ.kheap σ.curThread = some (.tcb x) := by rw [hcur]; exact hk
  -- the FaultIP write
  unfold syscall.handle_syscall_old
  rw [hct]; simp only [bind_ok]
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s ct layout.reg.NEXT_IP) ?_
  rintro nx hnx
  have hnx' : obj.Tcb.reg st ct s layout.reg.NEXT_IP = ok nx := by rw [P1.reg_ok, hnx]; rfl
  simp only [lift, bind_ok]
  refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s ct layout.reg.FAULT_IP _) ?_
  rintro s1 rfl
  generalize hv : core.num.U64.wrapping_sub nx 2#u64 = v
  have hvb : v.bv = x.tcbArch.tcbContext.userRegs .nextIP - 2 := by
    rw [← hv, core.num.U64.wrapping_sub_bv_eq, hnx, ← hxs.regs .nextIP, regIdx_nextIP]; rfl
  have hX2 := reg_wr_irel J.ip hI hctT hk Fl4Spec.Register.faultIP (by decide) v
  rw [regIdx_faultIP] at hX2
  obtain ⟨V0, J0⟩ := J.regWrJ hctT hk Fl4Spec.Register.faultIP v (by rw [regIdx_faultIP]; exact hX2)
  rw [regIdx_faultIP, hvb] at J0
  rw [← hcur] at J0
  have hF : ((), faultIPSt σ σ.curThread x) ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1 := by
    rw [fl4SyscallFaultIP_eq hk']; exact Set.mem_singleton _
  have hni0 : Entered (faultIPSt σ σ.curThread x) := hni
  have hBu := hB x hk'
  -- the trap flag and the number range
  refine WP.spec_bind (hflag ct v hct) ?_
  rintro f hf
  simp only [hf, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rw [if_neg hn.range.1, if_neg hn.range.2]
  -- budget_ok
  have hAK := hARI.toARKeep
  have hNSf := SInv.ns_fl4SyscallFaultIP σ.curThread σ hNS0 _ hF
  have hBud := JAtZ.budgetOkB (σ0 := faultIPSt σ σ.curThread x) J0 hni0 hBu hNSf hAK hA hnd hmrt hmb hmax htu
  have hBudS := JAtZ.budgetOkBSt (σ0 := faultIPSt σ σ.curThread x) J0 hni0 hBu hNSf hAK hA hnd hmrt hmb hmax htu
  have hMK := hKD.toK
  refine WP.spec_bind (WP.spec_and (WP.spec_and (spec_and_eq hBud fun _ h => h) hBudS)
    (budget_ok_mr hM hMK hA hR _)) ?_
  rintro ⟨b, s2, a1⟩ ⟨⟨⟨⟨hTr, -⟩, hbeq⟩, hFaS⟩, hMRb⟩
  cases b
  · -- the budget check stops the system call
    obtain ⟨z, hz, hz1, hJS⟩ := hFaS rfl
    obtain ⟨b', σb⟩ := z
    simp only at hz1; subst hz1
    obtain ⟨Gb, Vb, Acb, Lstb, Db, Jb⟩ := hJS
    show (do
      let (s3, a2) ← (if false = true then syscall.dispatch_syscall st arI s2 a1 n else ok (s2, a1))
      syscall.finish st arI s3 a2) ⦃ _ ⦄
    rw [if_neg (by decide)]
    simp only [bind_ok]
    have hx : ((.ok (), σb) : Except Unit Unit × Fl4Spec.State Unit) ∈ (specFront (invSysOf call true) σ).1 :=
      mem_specFront hF (mem_handleE_ok (mem_fl4HandleEvent hz mem_whenE_false))
    have F := hFin _ hx _ H Cs Acb Lstb Db s2 a1
      ⟨ct, v, false, s2, a1, hct, hbeq, Or.inl ⟨rfl, rfl, rfl⟩⟩ Jb.toR
    have hMσb := (budget_mr_at (σ0 := faultIPSt σ σ.curThread x) hM hnd hz hMRb hVI).1
    exact WP.spec_mono (jat_finishJRNMSt s2 a1 σb Jb.toR (SInvN.ns_front true (invSysOf call true) hNS0 _ hx) F.hd hnd
      hA F.vt hmb F.arch F.archNd F.fo F.sni F.send hT F.tail hmax htu hM hKD hMσb)
      fun r ⟨σ', hmem, hRJ, hM', hSt⟩ => ⟨σ', mem_kentry hx hmem, hRJ, hM', hSt.mv⟩
  · -- the system call runs: the I/O port invocation
    obtain ⟨σb, he, ekh, ect, ecs, eact, eidle, hCb, hOb, Ac', Lst', D', J'⟩ := hTr rfl
    show (do
      let (s3, a2) ← (if true = true then syscall.dispatch_syscall st arI s2 a1 n else ok (s2, a1))
      syscall.finish st arI s3 a2) ⦃ _ ⦄
    rw [if_pos rfl]
    have hb : (true, σb) ∈ (specBudget (faultIPSt σ σ.curThread x)).1 := by
      unfold specBudget
      rw [he]; exact Set.mem_singleton _
    have hBA : BudgetAt σ σb true := ⟨_, hF, hb⟩
    obtain ⟨hMRσb, -⟩ := budget_mr_at (σ0 := faultIPSt σ σ.curThread x) hM hnd
      (show (true, σb) ∈ _ by rw [he]; exact Set.mem_singleton _) hMRb hVI
    have hnib : Entered σb := ⟨by rw [ect, eidle]; exact hni0.1, by rw [eact]; exact hni0.2⟩
    -- the I/O port cap at the dispatch state
    obtain ⟨hct2, found, pf, pl, pz, hls, hcap⟩ := hio ct nx s2 a1 hct hnx' (by rw [hv]; exact hbeq)
    -- the dispatch state's entry facts (`KDispHypsKV27.to26`)
    obtain ⟨x0, hk0, -⟩ := hS.1.2
    obtain ⟨-, ek0, ect0, en0, ei0, eq0⟩ := BudgetAt.shape27 hnd hk0 hBA
    have ek0' : σb.kheap = Function.update σ.kheap σ.curThread
        (some (.tcb (setReg x0 .faultIP (x0.tcbArch.tcbContext.userRegs .nextIP - 2)))) := ek0
    obtain ⟨hvfh, -⟩ := SInvAll.sinvB_disp (x' := setReg x0 .faultIP (x0.tcbArch.tcbContext.userRegs .nextIP - 2))
      hS hni.1 hk0 rfl rfl ek0' ect0
    have hsg : SpecGlob σb :=
      specGlob_disp (x' := setReg x0 .faultIP (x0.tcbArch.tcbContext.userRegs .nextIP - 2)) hS.1.1.sg hk0 rfl ek0'
        en0 ei0
    have hqb : ∀ d p, σb.curThread ∉ σb.readyQueues d p := by rw [ect0, eq0]; exact hQ
    refine WP.spec_bind (spec_and_eq (dispatch_ioportJSt s2 a1 σb J' hARI hA hM hKD hIo hPI hnib hqb hvfh hsg
      hMRσb ct hct2 n call don hi found hls hcap) fun _ h => h) ?_
    rintro ⟨s3, a2⟩ ⟨⟨⟨u, σm⟩, hy, hy1, hRm, hJm, hMy⟩, hdeq⟩
    simp only at hy1; subst hy1
    obtain ⟨Gm, Vm, Acm, Lstm, Dm, Jm⟩ := hJm
    have hx : ((.ok (), σm) : Except Unit Unit × Fl4Spec.State Unit) ∈ (specFront (invSysOf call true) σ).1 :=
      mem_specFront hF (mem_handleE_ok (mem_fl4HandleEvent hb (mem_whenE_true hy)))
    have F := hFin _ hx _ H Cs Acm Lstm Dm s3 a2
      ⟨ct, v, true, s2, a1, hct, hbeq, Or.inr ⟨rfl, hdeq⟩⟩ Jm.toR
    exact WP.spec_mono (jat_finishJRNMSt s3 a2 σm Jm.toR (SInvN.ns_front true (invSysOf call true) hNS0 _ hx) F.hd
      hnd hA F.vt hmb F.arch F.archNd F.fo F.sni F.send hT F.tail hmax htu hM hKD hMy)
      fun r ⟨σ', hmem, hRJ, hM', hSt⟩ => ⟨σ', mem_kentry hx hmem, hRJ, hM', hSt.mv⟩

set_option maxHeartbeats 8000000 in
/-- (stpost) **The accepted I/O port entry beside the gate at given ghosts, stable** (module
docstring). -/
theorem kernel_entry_io_localSt17 [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR)
    (hPA : PPPlatA arI AR) (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s a σ)
    {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z]
    (n : I64) (c : Fl4Spec.Syscall) (hct : σ.curThread ≠ σ.idleThread) (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64)
      (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A),
        KFrontF (L := L) arI n s a s' a' →
        JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR13 (L := L) arI AR Z' H' Cs' s' a' x.2) :
    syscall.handle_ioport_local st arI s a n ⦃ r => r.1 = true →
      ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
        JReachU17 (L := L) arI AR MR r.2.1 r.2.2 σ' ∧ JStab (L := L) arI AR Z H Cs r.2.1 r.2.2 σ' ⦄ := by
  obtain ⟨hJ3, hGp, hIv, hDv⟩ := hJ
  obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, hR, -, -, -⟩ := jreach_invU3 hnd hJ3
  have hni := hX.entered hct
  have hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄ := hPA.minBudget
  have hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄ :=
    fun a => hT.mrt a
  have hD : SetDlDet := setDlDet_of arI hM hDR hR
  have hARK := hARI.toARKeep
  have hS := hX.sb
  have hQ := hX.ctQ
  have hU3 := sinvX_ut3 hX
  have hSg : SInvG.SpecGlobS σ := sinvX_sg hX
  have hC : CurInv σ := J.cur.resolve_left (by rw [hni.2]; intro e; cases e)
  have hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → KBudgetB arI a (faultIPSt σ σ.curThread x) :=
    fun x hk => ⟨hM.nowAgree hR hS.1.1.vmt, curInv_faultIPSt hk hC, offReady_faultIPSt hX.offReady, Or.inr hQ⟩
  have hFin' : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64)
      (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A),
        KFrontF (L := L) arI n s a s' a' →
        JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR (L := L) arI AR Z' H' Cs' s' a' x.2 := fun x hx Z' H' Cs' Ac' Lst' D' s' a' hF J' =>
    ((((hFin x hx Z' H' Cs' Ac' Lst' D' s' a' hF J').to11 J'
      (SInvIV.front_idleVtS σ.curThread true (.syscallEvent c) hSg (sinvX_idleOut hX) hU3 hIv x hx)).to8
      (J'.hdOK (dp_specFront hnd c (sinvX_dom hX) x hx))).to5 hnd hA hARK hRef hD hT J'
      (fun o e => SInvAll.sinvB_front_fo true c hS hct x hx o e)).to31 hA hD |>.to27.toR
      (fun o e => SInvAll.sinvB_front_fo true c hS hct x hx o e)
  obtain ⟨⟨b, s', a'⟩, e, -⟩ := P1.spec_ex_fd
    (P0.syscall.handle_ioport_local.p0 st arI s a n L.total hA)
  rw [e, WP.spec_ok]
  intro hb
  simp only at hb
  subst hb
  have hs := P1.ioport_local_same arI hA J.bxi hflag e
  obtain ⟨hn2, hio⟩ := P1.ioport_local_acc arI hA J.bxi e
  obtain ⟨call, don, hi⟩ : ∃ call don, InvSys n call true don := by
    rcases hn2 with rfl | rfl
    · exact ⟨true, true, Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl⟩)⟩
    · exact ⟨false, false, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
  have hrr : n ≠ fl4_abi.syscall.SysReplyRecv := by
    rcases hn2 with rfl | rfl <;>
      (simp only [fl4_abi.syscall.SysCall, fl4_abi.syscall.SysSend, fl4_abi.syscall.SysReplyRecv, ne_eq] <;> decide)
  have hc := nativeSys_invC hn hi
  subst hc
  have hG := kernel_entry_ioSt s a σ J hni hR hS.1.1.vim hS.1.1.ns n call don hi hflag hB hS hQ hFin' hio hARI hA
    hnd hM hKD hIo hPI hmrt hmb hT hmax htu
  have hG' : syscall.handle_syscall st arI s a n ⦃ r =>
      ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true (invSysOf call true) σ).1 ∧
        RJ (L := L) arI AR r.1 r.2 σ' ∧ MR r.2 σ'.machineState ∧ JStab (L := L) arI AR Z H Cs r.1 r.2 σ' ⦄ := by
    rw [handle_syscall_eq_general_of hflag hn.range hrr, P1.handle_syscall_general_eq]; exact hG
  rw [hs, WP.spec_ok] at hG'
  obtain ⟨σ', hy, hRJ, hM', hSt⟩ := hG'
  exact ⟨σ', hy, ⟨JReachU3.step _ _ hJ3 hct hn hs hy ⟨hRJ, hM'⟩,
    SInvGp.kentry_gpmOut (invSysOf call true) hSg hU3 hGp _ hy,
    SInvIV.kentry_idleVtS (invSysOf call true) hSg (sinvX_idleOut hX) hU3 hIv _ hy,
    SInvDV.kentry_devRange (invSysOf call true) hU3 hDv _ hy⟩, hSt⟩

end

end

end Fl4Proofs.P3.SInvR.G5
