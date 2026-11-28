/-
P3 (issue #16, m73): **`FastFaultOK` from the joint relation**, and the
event tops without it: `kernel_entry_reachE5` (`kernel_entry_reachE4`) and
`SInvR.G5.kernel_entry_reachUH2` (m72's `kernel_entry_reachUH`) whose
unknown-syscall clause no longer takes `P1.FastFaultOK` [J].

`P1.FastFaultOK s a n` (the general fault path's reads at the states where
`handle_syscall_fast` enters `fastpath.fault`) is derived at every `JAtZ`
entry state with the facts `JReachE4` / `JReachU` carry (`SInvX`: entered,
`SInvB`, the current thread in no ready queue, `OffReady`):

* the dispatch state (the entry's `FAULT_IP` write, a passing `budget_ok`;
  on the out-of-range route after a declined `debug_syscall`, which returns
  `ok (false, s, a)`: `P1.syscall.debug_syscall.same2`) carries `JAtZ` and
  `CurInv` (`JAtZ.fltDisp`, m69's `rrDisp` keeping `budgetOkB`'s `CurInv`);
* there P1's `fastFault_of` (FastFaultEntU) is used at the word set
  `OmegaU H Z kb σ = (Heap.omega H \ BufU Z σ) ∪ VsU Z kb`: `BufU` the IPC
  buffer words of `Z.T`'s TCBs (frame words, which are `Ω` words at `H`:
  KENTRY-PLAN m72's OBSTRUCTION), `VsU` the ASID-table and pool words
  (`VsWrite`). `JAtZ.bxiU`: `BXI` at `OmegaU` by `P1.BXI.reΩ` (the frame
  words and the kernel-state block are no buffer words: `rbufU`,
  `KsApart.buf`; the ASID words are placed like kernel words: `vsObjW`,
  `vsNodeW`, `vsW_al`). `JAtZ.asidOffU`: m63's `AsidOff` at `OmegaU`
  (derived: the table words and, for a nonzero entry, the pool's words,
  `VsRel.tmem`, are `VsU` words, off the frame words). `JAtZ.bufU_out`: the
  buffer words are outside the TCBs / nodes (`rbufU`) and off `OmegaU`
  (`TopPlaced.disj`: an IPC-buffer word of `Z.B` is no VSpace word).
  `JAtZ.bufOK`: every TCB's receive buffer (`lookup_buf_full`,
  `BufWordRel`) has its 128 words in `BufU`. `JAtZ.curNb`: the current
  thread is not blocked (`CurInv`'s `NotIpcBlk`, `TcbRel.st`).
  `JAtZ.fhTyped`: the fault-handler cap is typed (`JPlaced.typed`).
-/
import Fl4Proofs.P3.XTopJointKEntryUH
import Fl4Proofs.P3.XTopJointKEntryEv7
import Fl4Proofs.P3.XTopJointKEntryRRF
import Fl4Proofs.P3.XTopJointXferB
import Fl4Proofs.P3.XTopJointFinVs
import Fl4Proofs.P1.FastFaultEntU
import Fl4Proofs.P3.BufAtJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

/-- A thread state blocked on no endpoint or notification has a word that
is not `Blocked`. -/
theorem nb_of_code {ts : Fl4Spec.ThreadState} (h : NotIpcBlk ts) {w : U64} (hv : w.val = tsCode ts) :
    ¬ P1.Blocked w := by
  obtain ⟨-, -, r3, r4, r6⟩ := P1.ts_vals
  obtain ⟨n1, n2, n3⟩ := h
  rintro (e | e | e)
  · rw [e, r4] at hv
    cases ts <;> simp [tsCode] at hv
    exact n2 _ _ rfl
  · rw [e, r3] at hv
    cases ts <;> simp [tsCode] at hv
    exact n3 _ _ _ rfl
  · rw [e, r6] at hv
    cases ts <;> simp [tsCode] at hv
    exact n1 _ rfl

/-- The ASID-table and pool words. -/
def VsU (Z : XSets) (kb : U64) : Set U64 := {b | VsWrite Z.P kb b}

/-- **The word set P1's fault path is used at** (module docstring). -/
def OmegaU (H : P1.Heap) (Z : XSets) (kb : U64) (σ : Fl4Spec.State Unit) : Set U64 :=
  {b | (b ∈ P1.Heap.omega H ∧ b ∉ BufU Z σ) ∨ b ∈ VsU Z kb}

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {MR : A → Fl4Spec.MachineState → Prop}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

theorem JAtZ.vsU_place {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {b : U64} (hb : b ∈ VsU Z (L.ksb s)) : P1.OutsideObjs st (P1.Heap.tcbs H) Cs s b ∧
      (∀ e, (H e = some .ep ∨ H e = some .ntfn) → b.val + 8 ≤ e.val ∨ e.val + 16 ≤ b.val) ∧
      b ∉ P1.Heap.frame H := by
  have hW : VsW Z (L.ksb s) b := Or.inr hb
  have Ap : VsApart (L := L) Z H Cs s :=
    (jVsApartHyp (arI := arI) (AR := AR) (th := Z.th)) Z H Cs Ac Lst D s a σ rfl J
  have hal := J.vsW_al hW
  have hal' : b.val % 8 = 0 := hal
  have hHk := J.kern.heap
  refine ⟨⟨hal, fun t ht => ?_, fun c hc => ?_⟩, fun e he => ?_, fun hf => ?_⟩
  · have := J.vsObjW Ap hW (show H t = some .tcb from ht) (fun _ e => by cases e)
    simpa [P1.HKind.bits] using this
  · rcases J.vsNodeW hW hc with h | h
    · left; omega
    · right; exact h
  · rcases he with he | he
    · have ha := hHk.align e _ he
      have := J.vsObjW Ap hW he (fun _ e => by cases e)
      simp [P1.HKind.bits] at ha this
      omega
    · have ha := hHk.align e _ he
      have := J.vsObjW Ap hW he (fun _ e => by cases e)
      simp [P1.HKind.bits] at ha this
      omega
  · obtain ⟨-, p, k, hp, hk, hin⟩ := hf
    have hko : ∀ z, k ≠ .other z := by
      rcases hk with rfl | ⟨z, rfl⟩ | ⟨rfl, -⟩ <;> intro z e <;> cases e
    obtain ⟨g1, g2⟩ := hin
    rcases J.vsObjW Ap hW hp hko with e | e <;> omega

/-- **`BXI` at `OmegaU`** (module docstring). -/
theorem JAtZ.bxiU {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    P1.BXI st (P1.Heap.tcbs H) Cs (OmegaU H Z (L.ksb s) σ) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s := by
  have hI := J.bxi
  refine P1.BXI.reΩ hI (V := VsU Z (L.ksb s)) (fun a ha => ha.imp (fun h => h.1) id)
    (fun a ha => ⟨(J.vsU_place ha).1, (J.vsU_place ha).2.1⟩)
    (fun b hb => Or.inl ⟨P1.Heap.frame_omega hb, fun hu => (J.bufU_rbuf hu).2.2 hb⟩)
    (fun o h1 h2 => Or.inl ⟨hI.2.2.2.1.ksΩ o h1 h2, fun hu => ?_⟩)
  obtain ⟨wp, hwp, e⟩ := J.bufU_B hu
  have h0 := J.ks.buf wp hwp
  have hv : (core.num.U64.wrapping_add (L.ksb s) o).val = (L.ksb s).val + o.val := by
    have := J.kern.ksbFit
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  rw [e, hv] at h0; omega

/-- **m63's `AsidOff` at `OmegaU`, derived** (module docstring). -/
theorem JAtZ.asidOffU {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    P1.AsidOff (L := L) (OmegaU H Z (L.ksb s) σ) (P1.Heap.frame H) s := by
  intro hi hhi
  have hT : P1.atAF (L.ksb s) hi ∈ VsU Z (L.ksb s) :=
    show VsWrite Z.P (L.ksb s) _ from Or.inl ⟨hi, hhi, rfl⟩
  refine ⟨Or.inr hT, (J.vsU_place hT).2.2, fun hz lo hlo => ?_⟩
  have hP : L.mem s (P1.atAF (L.ksb s) hi) ∈ Z.P := J.xtop.fin.2.1.tmem hi hhi hz
  have hW : P1.peAF (L.mem s (P1.atAF (L.ksb s) hi)) lo ∈ VsU Z (L.ksb s) :=
    show VsWrite Z.P (L.ksb s) _ from Or.inr ⟨_, hP, lo, hlo, rfl⟩
  exact ⟨Or.inr hW, (J.vsU_place hW).2.2⟩

/-- **The IPC-buffer words off `OmegaU`** (module docstring). -/
theorem JAtZ.bufU_out {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {b : U64} (hb : b ∈ BufU Z σ) :
    P1.OutsideObjs st (P1.Heap.tcbs H) Cs s b ∧ b ∉ OmegaU H Z (L.ksb s) σ := by
  refine ⟨(J.bufU_rbuf hb).1, ?_⟩
  rintro (⟨-, hn⟩ | hv)
  · exact hn hb
  · obtain ⟨wp, hwp, e⟩ := J.bufU_B hb
    have hO : OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b :=
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨wp, hwp, by rw [e], by rw [e]; omega⟩))))))
    exact J.xtop.fin.1.2.disj b hO (vsWrite_vobj J.xtop.fin.1.2.vs hv)

/-- **The current thread not blocked** where `CurInv` holds (module
docstring). -/
theorem JAtZ.curNb {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hC : CurInv σ) : ¬ P1.Blocked (L.mem s (P1.stA (L.curW s))) := by
  obtain ⟨hcur, -⟩ := J.curEq (cur_thread_curW (L := L) s)
  have hctT : L.curW s ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hI := J.xtop.irelK J.ks J.buf
  obtain ⟨x0, hk0, hTR⟩ := hI.1.tcb _ hctT
  obtain ⟨xt, hkt, -, hnb⟩ := hC.tcb
  rw [hcur, hk0] at hkt
  simp only [Option.some.injEq, Fl4Spec.KernelObject.tcb.injEq] at hkt
  subst hkt
  have hv : (L.mem s (P1.stA (L.curW s))).val = tsCode x0.tcbState := by
    rw [P1.stA_eq, ← tStA_eq]; exact hTR.st
  exact nb_of_code hnb hv

/-- **The fault-handler cap typed** (`JPlaced.typed` at the TCB's slot 3). -/
theorem JAtZ.fhTyped {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    obj.Tcb.slot (L.curW s) layout.tcb.SLOT_FAULT_HANDLER ⦃ sl =>
      obj.Slot.cap st sl s ⦃ c => P1.CapTyped H (P1.Heap.replies H) (P1.Heap.ntfns H) c ⦄ ⦄ := by
  have htcb := J.curW_tcb (cur_thread_curW (L := L) s)
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hs : IsSlot Z.th (cslotAddr ((L.curW s).bv, Fl4Spec.tcbCnodeIndex 3)) :=
    AbsSlot.isSlot ⟨L.curW s, rfl, Or.inr ⟨htcb, 3, by decide, rfl⟩⟩
  rw [tcb_slot_fault, WP.spec_ok, slot_cap_eq, capAt_capV, WP.spec_ok]
  exact hJ.typed _ hs

set_option maxHeartbeats 4000000 in
/-- **m69's `JAtZ.rrDisp` with `CurInv` at the dispatch state** (from `JAtZ.budgetOkB`).
The dispatch state of the real run carries `JAtZ` (the prefix of
`kernel_entryJ13PUN`): after the entry's own `NEXT_IP` read and `FAULT_IP`
write and a passing `budget_ok`, `JAtZ` holds at the ghosts `Z.mv Z.G V0`, `H`,
`Cs`, its spec state with the kheap of `faultIPSt σ`. -/
theorem JAtZ.fltDisp {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z]
    (hni : Entered σ) (hR : MR a σ.machineState) (hS : SInvAll.SInvB σ)
    (hQ : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → OffReady (faultIPSt σ σ.curThread x))
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    {t nx : U64} {s1 s2 : S} {a2 : A} (et : sched.cur_thread st s = ok t)
    (enx : obj.Tcb.reg st t s layout.reg.NEXT_IP = ok nx)
    (es1 : obj.Tcb.set_reg st t s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1)
    (hb : syscall.budget_ok st arI s1 a = ok (true, s2, a2)) :
    ∃ σb, CurInv σb ∧
      ∃ V0 Ac' Lst' D', JAtZ (L := L) arI AR (Z.mv Z.G V0) H Cs Ac' Lst' D' s2 a2 σb := by
  obtain ⟨hcur, -⟩ := J.curEq et
  have hctT : t ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hI := J.xtop.irelK J.ks J.buf
  obtain ⟨x, hk, -⟩ := hI.1.tcb t hctT
  have hxs := hI.1.toE.at_tcb hctT hk
  have hk' : σ.kheap σ.curThread = some (.tcb x) := by rw [hcur]; exact hk
  have hnx : nx = L.mem s (regA t layout.reg.NEXT_IP) := by
    have := Endp.obj.Tcb.reg.spec (L := L) s t layout.reg.NEXT_IP
    rw [enx, WP.spec_ok] at this; exact this
  have hs1 : s1 = L.wr s (regA t layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx 2#u64) := by
    have := Endp.obj.Tcb.set_reg.spec (L := L) s t layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64)
    rw [es1, WP.spec_ok] at this; exact this
  subst hs1
  generalize hv : core.num.U64.wrapping_sub nx 2#u64 = v at hb
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
  have hC : CurInv σ := J.cur.resolve_left (by rw [hni.2]; intro e; cases e)
  have hBu : KBudgetB arI a (faultIPSt σ σ.curThread x) :=
    ⟨hM.nowAgree hR hS.1.1.vmt, curInv_faultIPSt hk' hC, hB x hk', Or.inr hQ⟩
  have hBud := JAtZ.budgetOkB (σ0 := faultIPSt σ σ.curThread x) J0 hni0 hBu
    (SInv.ns_fl4SyscallFaultIP σ.curThread σ hS.1.1.ns _ hF) hARI.toARKeep hA hnd hmrt hmb hmax htu
  rw [hb, WP.spec_ok] at hBud
  obtain ⟨σb, -, -, -, -, -, -, hCb, -, Ac', Lst', D', J'⟩ := hBud.1 rfl
  exact ⟨σb, hCb, V0, Ac', Lst', D', J'⟩

set_option maxHeartbeats 4000000 in
/-- **`P1.FastFaultOK` at a `JAtZ` entry state** (module docstring): no
premise beyond what `JReachE4` / `JReachU` carry. -/
theorem JAtZ.fastFaultOK {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z]
    (hni : Entered σ) (hR : MR a σ.machineState) (hS : SInvAll.SInvB σ)
    (hQ : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → OffReady (faultIPSt σ σ.curThread x))
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) (n : I64) :
    P1.FastFaultOK (L := L) arI s a n := by
  have disp : ∀ {t nx : U64} {s1 s2 : S} {a2 : A}, sched.cur_thread st s = ok t →
      obj.Tcb.reg st t s layout.reg.NEXT_IP = ok nx →
      obj.Tcb.set_reg st t s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1 →
      syscall.budget_ok st arI s1 a = ok (true, s2, a2) →
      ∀ (t2 m : U64), sched.cur_thread st s2 = ok t2 →
        P1.FaultOK (L := L) arI s2 a2 t2 m ∧ P1.FaultNvm (L := L) arI s2 a2 t2 m := by
    intro t nx s1 s2 a2 et enx es1 hb t2 m et2
    obtain ⟨σb, hCb, V0, Ac', Lst', D', J'⟩ :=
      J.fltDisp hni hR hS hQ hB hARI hA hnd hM hmrt hmb hmax htu et enx es1 hb
    exact P1.fastFault_of arI hA J'.bxiU et2 (J'.curNb hCb) J'.fhTyped (fun b hb => J'.bufU_out hb)
      (fun y hy => J'.bufOK hy) J'.asidOffU
  intro t nx s1 et enx es1
  refine ⟨fun s2 a2 t2 hb et2 => disp et enx es1 hb t2 _ et2, fun t1 s3 a3 et1 hd => ?_⟩
  have h := P1.syscall.debug_syscall.same2 (L := L) hA s1 a t1 n
  rw [hd, WP.spec_ok] at h
  obtain ⟨rfl, rfl⟩ := h rfl
  exact fun s2 a2 t2 hb et2 => disp et enx es1 hb t2 _ et2

end

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

end

end Fl4Proofs.P3.SInvR.G5
