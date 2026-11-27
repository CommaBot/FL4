/-
P3 (p3J gen 29): **`syscall.finish` writes only `ProjW` at a `CKI` `JAtZR` state** (`finFootJR`).

The native syscall's dispatch ends, on its unpreempted outcomes, in the receive exit form `JAtZR` (`JAtZ` with
`cur` weakened to `CurInvR`), not `JAtZ`; gen 26's `finFootJ_holds` is stated at `JAtZ`. Its proof reads only
fields `JAtZR` has as well (`xtop`, `blk`, `kern`, `ext`, `jpl` / `zH` / `thT` via `JAtZR.thTcb` /
`JAtZR.tcbs_eq`), so this module is that proof chain verbatim on `JAtZR` (P3JMcBuf's `lookup_ipc_buffer_ckiR`,
P3JMcFootC's `bufOK_empty_ckiR`, P3JMcFin's `bufAt_empty_ckiR`, `vcpuZ_of_JR`, `sched_projWR`, `finOld_projWR`,
`finFootJ_holds`), names suffixed `R`. No premise; no sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JMcFin
import Fl4Proofs.P3.BufAtJR
import Fl4Proofs.P3.XTopJointJAtZRA
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Mc
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs Fl4Proofs.P3.JBootQ

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
  {AR : A → Fl4Spec.Cr3 → Prop}

theorem lookup_ipc_buffer_ckiR {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hC : SInvCk.CKI σ) {t : U64} (ht : Z.th t = some .tcb) (rcv : Bool) :
    msg.lookup_ipc_buffer st s rcv t = ok 0#u64 := by
  have hR : StateRel Z.th (L.mem s) σ := J.xtop.rel.2.1.1
  obtain ⟨x, c, hkx, hc, hca⟩ := hR.bufCap ht
  have hco : capOpt (σ.kheap t.bv) (Fl4Spec.tcbCnodeIndex 2) = some x.tcbIpcframe := by
    simp only [capOpt, hkx]; exact Endp.tcbCnodeMap_two x
  have hk := hC _ _ _ hco
  rw [← hca.2] at hk
  obtain ⟨w, hw, -⟩ := spec_exists (Endp.obj.Tcb.ipc_buffer.spec' (L := L) s t)
  unfold msg.lookup_ipc_buffer
  rw [hw, bind_ok, Endp.tcb_slot_buffer, bind_ok, slot_cap_eq, hc, bind_ok]
  cases c <;> first | rfl | exact (by simp [absCap, SInvCk.KW] at hk)


theorem bufOK_empty_ckiR {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hC : SInvCk.CKI σ) {t : U64} (ht : Z.th t = some .tcb) (rcv : Bool) :
    msg.lookup_ipc_buffer st s rcv t ⦃ b => P1.BufOK ∅ b ⦄ := by
  rw [lookup_ipc_buffer_ckiR J hC ht rcv]
  exact (WP.spec_ok _).2 (fun h => (h rfl).elim)

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
  {AR : A → Fl4Spec.Cr3 → Prop}
variable {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A}
  {σ : Fl4Spec.State Unit}

/-- **`BufAt` at `U = ∅` at a `CKI` `JAtZ` state** (module docstring). -/
theorem bufAt_empty_ckiR (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) (hC : SInvCk.CKI σ) :
    P1.BufAt st (P1.Heap.tcbs H) Cs H (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) ∅ s :=
  ⟨fun b hb => absurd hb (Set.notMem_empty b), fun y hy =>
    bufOK_empty_ckiR J hC (J.thTcb (by rw [J.tcbs_eq.1]; exact hy)) true⟩

/-- Every TCB's VCPU word is `0` at a `JAtZ` state (`JExt.vw`). -/
theorem vcpuZ_of_JR (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    Fl4Proofs.P2.Stall.VcpuZ st (P1.Heap.tcbs H) s := fun t ht =>
  J.ext.vw t (J.thTcb (by rw [J.tcbs_eq.1]; exact ht))

/-- **`schedule` writes only `ProjW`** at a `CKI` `JAtZ` state (module docstring). -/
theorem sched_projWR (hA : P0.ArchTotal arI) (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hC : SInvCk.CKI σ) :
    sched.schedule st arI s a ⦃ s1 _ => P1.WritesIn st s s1 (ProjW (L := L) H Cs s) ⦄ := by
  have hblk := J.blk
  have hH := J.kern.heap
  have hBA := bufAt_empty_ckiR J hC
  have hNt : ∀ n ∈ P1.Heap.ntfns H, H n = some .ntfn := fun n hn => hn
  obtain ⟨Q, R, hq⟩ := J.blk.1
  refine WP.spec_mono (Fl4Proofs.P1.sched.schedule.sN (Kp := (∅ : Set U64)) hA (ibKeep_holds hA) hNt s a
    hblk hBA fun _ _ => ⟨fun y hy => absurd hy (Set.notMem_empty y), fun _ => Set.notMem_empty _,
      fun hk => absurd hk (Set.notMem_empty _)⟩) ?_
  rintro ⟨s1, a1⟩ hh
  simp only [WP.uncurry'_pair] at hh ⊢
  obtain ⟨rf, hrf, Fd, F⟩ := hh
  have k0 := Fl4Proofs.P2.Stall.timer.fire.idlF hA (ibKeep_holds hA) hNt s a hblk hBA
  rw [hrf] at k0
  have K : Fl4Proofs.P2.Stall.IdlK st Cs s rf.1 := (WP.spec_ok rf).1 k0
  have t0 := Fl4Proofs.P1.timer.fire.tinvF hA (ibKeep_holds hA) hNt s a hblk hBA
  rw [hrf] at t0
  have T1 : P1.TInv st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac rf.1 ∧
      FootDU st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (EH H) ∅ s rf.1 :=
    (WP.spec_ok rf).1 t0
  obtain ⟨⟨⟨Q1, R1, q1⟩, -⟩, -⟩ := T1
  have A1 := projW_of_footDU_idl hH hq.nodes Fd K
  have B1 := projW_of_sfootN hH q1.nodes (by rw [Fd.1]; exact J.kern.ksbFit) F
  exact A1.projW_trans B1

/-- **`finish_old` (`schedule`, `activate_thread`) writes only `ProjW`, ends in `EntryInv`**, and keeps the
buffer lookups and the VCPU words. -/
theorem finOld_projWR (hA : P0.ArchTotal arI) (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hC : SInvCk.CKI σ) :
    syscall.finish_old st arI s a ⦃ s2 _ => P1.WritesIn st s s2 (ProjW (L := L) H Cs s) ∧
      P1.EntryInv st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
        (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s2 ∧
      P1.IbFr (L := L) (P1.Heap.tcbs H) s s2 ∧ Fl4Proofs.P2.Stall.VcpuWK st (P1.Heap.tcbs H) s s2 ⦄ := by
  have hblk := J.blk
  have hH := J.kern.heap
  have hBA := bufAt_empty_ckiR J hC
  have hNt : ∀ n ∈ P1.Heap.ntfns H, H n = some .ntfn := fun n hn => hn
  have core : syscall.finish_old st arI s a ⦃ s2 _ => P1.WritesIn st s s2 (ProjW (L := L) H Cs s) ∧
      P1.EntryInv st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
        (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s2 ⦄ := by
    unfold syscall.finish_old
    obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := hblk
    refine WP.spec_bind (WP.spec_and
      (Fl4Proofs.P1.sched.schedule.entry hA (ibKeep_holds hA) hNt s a Q R h0 hB hS hX hSg hBA)
      (sched_projWR hA J hC)) ?_
    rintro ⟨s1, a1⟩ hh
    try simp only [WP.uncurry'_pair] at hh ⊢
    obtain ⟨E1, W1⟩ := hh
    have hq1 := E1.1.choose_spec.choose_spec
    refine WP.spec_mono (WP.spec_and (Fl4Proofs.P1.sched.activate_thread.entry hA s1 a1 E1)
      (Fl4Proofs.P2.Stall.sched.activate_thread.tws hA s1 a1 (EntryInv.bxi E1).blk)) ?_
    rintro ⟨s2, a2⟩ hh
    try simp only [WP.uncurry'_pair] at hh ⊢
    obtain ⟨E2, W2⟩ := hh
    refine ⟨W1.projW_trans (W2.mono fun b hb => tws_projW hH hq1.nodes hq1.cur hq1.curT hb), E2⟩
  refine WP.spec_mono (WP.spec_and (WP.spec_and core
    (Fl4Proofs.P1.syscall.finish_old.ibx hA hNt s a (BlkOK.bxi hblk) hBA))
    (Fl4Proofs.P2.Stall.syscall.finish_old.vc hA hNt s a (BlkOK.bxi hblk) hBA)) ?_
  rintro ⟨s2, a2⟩ hh
  try simp only [WP.uncurry'_pair] at hh ⊢
  obtain ⟨⟨⟨W, E⟩, I⟩, V, -⟩ := hh
  exact ⟨W, E, I, V⟩

/-- **`finish` writes only `ProjW` at a `CKI` `JAtZR` state** (`finFootJ_holds` on `JAtZR`). -/
theorem finFootJR (hA : P0.ArchTotal arI) (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hC : SInvCk.CKI σ) :
    syscall.finish st arI s a ⦃ r => P1.WritesIn st s r.1 (ProjW (L := L) H Cs s) ⦄ := by
  have hH := J.kern.heap
  have hBA := bufAt_empty_ckiR J hC
  have hVz := vcpuZ_of_JR J
  have hNt : ∀ n ∈ P1.Heap.ntfns H, H n = some .ntfn := fun n hn => hn
  rw [Fl4Proofs.P1.finish_eq_old]
  refine WP.spec_bind (finOld_projWR hA J hC) ?_
  rintro ⟨s2, a2⟩ hh
  try simp only [WP.uncurry'_pair] at hh ⊢
  obtain ⟨W2, E2, I2, V2⟩ := hh
  show (do let t ← sched.cur_thread st s2; vcpu.check st arI s2 a2 t) ⦃ _ ⦄
  rw [Fl4Proofs.P1.cur_thread_ok]; simp only [bind_ok]
  have hq2 := E2.1.choose_spec.choose_spec
  have hc2 : L.curW s2 ∈ P1.Heap.tcbs H := hq2.curT
  refine WP.spec_mono (Fl4Proofs.P2.Stall.vcpu.check.vckN (U := ∅) hA hNt s2 a2 E2
    (fun b hb => absurd hb (Set.notMem_empty b)) ((hBA.of_fr I2).2 _ hc2) fun hne => absurd ?_ hne) ?_
  · rw [V2 _ hc2]; exact hVz _ hc2
  rintro ⟨s3, a3⟩ hr
  try simp only [WP.uncurry'_pair] at hr ⊢
  exact W2.projW_trans (hr.mono fun b hb => vckN_projW hH hq2.nodes hq2.cur hc2 hb)


end

end Fl4Proofs.P3.Mc
