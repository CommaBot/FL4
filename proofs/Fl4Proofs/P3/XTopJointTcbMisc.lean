/-
P3 (DESIGN.md §9), TCB: **steps of the Thread cap's remaining labels at
`J`** (for XTopJointTcb's WriteFPU, SetTimer, …).

* `JAtZ.reg_frameFp`: XTopJointRegFrame's register frame (`JAtZ.reg_frameF`)
  widened to the TCBs' FPU images (offsets 512..3208: TCB words read by no
  relation of `JAtZ`; the spec's FPU state is not related to FL4's, see
  XTopJointFpu).
* `JAtZ.fpuWrJ`: one word of a TCB's FPU image written at `J`, the spec state
  kept (`XTopAt.tcbWrF`, P1's `BlkOK` by `blk_rf`, its footprint by
  `foot_field`).
* `JAtZ.copyFpuJ`: FL4's `copy_words` into a TCB's FPU image (WriteFPU's
  copy) at `J` (`copy_words_inv` with `JAtZ.fpuWrJ`).
* `JAtZ.archJ`: `JAtZ` at another arch state related to the same CR3 (the
  FPU operations of the arch backend: `ARKeep` [P]).
-/
import Fl4Proofs.P3.XTopJointDelR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

open Fl4Proofs.P1 in
set_option maxHeartbeats 8000000 in
/-- **`JAtZ` across a register step with FPU-image words** (as
XTopJointTcb's `JAtZ.reg_frameG`, the write set widened by the TCBs' FPU
images, offsets 512..3208). -/
theorem JAtZ.reg_frameFp (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit}
    {Ac' : Set U64}
    (hI3 : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ')
    (hw : P1.WritesIn st s s' (fun b => RegFW Z.T Z.C b ∨ ∃ y ∈ Z.T,
      y.val + 512 ≤ b.val ∧ b.val < y.val + 3208)) (hA : QKY σ σ') (hyk : YKeep σ σ') (hInv : Inv σ')
    (hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac' s')
    (hfoot : P1.WritesIn st s s' (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
      (P1.Heap.scBits H) ∅ s)) :
    ∃ V', JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst D s' a σ' := by
  have hI := J.xtop.irelK J.ks J.buf
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hF : IFrame (L := L) Z.th s s' := IRel.iframe_of hI hw fun b hb => by
    rcases hb with ((hb | ⟨q, hq, rfl⟩) | ⟨y, hy, hb⟩) | ⟨y, hy, h1, h2⟩
    · obtain ⟨y, hy, h1, h2⟩ := hb
      exact Or.inr (Or.inr (Or.inl ⟨y, hy, h1, by omega⟩))
    · obtain ⟨x0, n0, hk0, hx0⟩ := hs.scs q hq
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨q, hq, x0, n0, hk0, hx0.in_obj (hx0.hdr (K := 8#u64) (by simp) (by simp)).2⟩))))))
    · exact Or.inr (Or.inr (Or.inl ⟨y, hy, by omega, by omega⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨y, hy, by omega, by omega⟩))
  have hwF : P1.WritesIn st s s' (Ipc.FinW (st := st) Z.T Z.N Z.C Z.c s σ) := hw.mono fun b hb => by
    rcases hb with ((⟨y, hy, k1, k2⟩ | ⟨q, hq, rfl⟩) | ⟨y, hy, hb⟩) | ⟨y, hy, k1, k2⟩
    · exact Or.inr ⟨y, hy, b.val - y.val, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inl (KFoot.of_sw (sw_hdr hS hq (K := 8#u64) (by simp) (by simp) (by decide)))
    · exact Or.inr ⟨y, hy, 3376, by omega, by omega, by omega, by omega, by omega, hb⟩
    · exact Or.inr ⟨y, hy, b.val - y.val, by omega, by omega, by omega, by omega, by omega, by omega⟩
  have hck : Fl4Proofs.P3.CKeep σ σ' := hA.ckeepP
  have hAR : AR a σ.archState.x64CurrentCr3 := J.xtop.fin.1.1.2.2.2.2.2.2
  obtain ⟨V', hX3⟩ := XTopAt.irel_same J.xtop hI3 hAR hF.1 hck.cdt hck.orig hck.ks hF.2
  have hks : L.ksb s' = L.ksb s := hF.2
  obtain ⟨k1, k2, kb, k3, k4⟩ := J.finW_keeps hwF
  have ck := hA.callKeep
  obtain ⟨hCR', hRP'⟩ := CallRel.carry J.call J.rp ⟨k3, k4⟩ hks ck
  have hRF' := RFree.carry J.rfree J.call k4 ck
  have hDbg := J.kw_dbg (hfoot.mono fun b hb => kw_empty_mono hb _)
  have hS3 : SchedRel st Z.N Z.T Z.C Z.c s' σ' := hI3.2.2.1
  have hAI3 : ActIdle σ' := hA.actIdle J.act
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := J.deadP_qk hA hS3 hI3.1 hwF k3 hAI3.1
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ' := by
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    exact ⟨Tr, Cq, hJ.same hF.1 (fun q y n _ hq => hA.szKeep q.bv y n hq) hks (J.finW_irq hwF)⟩
  have hkern := J.kern_keep hks hwF.2.1 hS3 hA.ct hA.csc (fun sl h => Or.inl (by rw [← hA.orig]; exact h))
    (by rw [hA.arch])
    (fun q ao h => (hA.oth (fun _ e => by cases e) (fun _ _ e => by cases e)).2 h) hDbg
    (D' := D)
  have R : JRest (L := L) arI (Z.mv Z.G V') H Cs Ac' Lst D s' σ' :=
    ⟨hCR', hRF', J.yld.frame k2 hyk, J.mcp.frame k1 hA.mcpKeep, J.buf.frame kb hA.bufKeep, hRP',
      J.apart.sc_frame hks hA.szKeep, hjpl, J.jcov_keep hks hF.1 hdead (J.idleW_keep hS3 hA.idle), hkern,
      J.finW_utc hwF hF.1 hA.cdt hA.orig hA.arch hDbg, hA.nsc J.nsc, hInv, hA.cur J.cur, hA.own J.own, hA.off J.off,
      hAI3, hA.bsa J.bsa, hA.isorted J.isorted, hA.curRunM J.curRun, hblk⟩
  have hC0 := JCs.same J hF.1 hA.ksz
  have hC : JCs (L := L) (Z.mv Z.G V') s' σ' := ⟨hC0.del, hC0.ut, hC0.finM, hC0.sfree⟩
  exact ⟨V', J.cs_frameV hks hX3 hA.kback hC R⟩

open Fl4Proofs.P1 in
set_option maxHeartbeats 8000000 in
/-- **A word of a TCB's FPU image written at `J`** (`JAtZ.reg_frameFp` with
the spec state kept: `XTopAt.tcbWrF`, `IRel` by `XTopAt.irelK`, P1's `BlkOK`
by `blk_rf`, its footprint by `foot_field`). -/
theorem JAtZ.fpuWrJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T) (wa : U64)
    (Kv : Nat) (hK : 512 ≤ Kv ∧ Kv < 3208 ∧ Kv % 8 = 0) (hwav : wa.val = t.val + Kv) (v : U64) :
    ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D (L.wr s wa v) a σ := by
  have hT : TcbPlaced Z.T := J.ip.e.tcb
  have hta := hT t ht
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  have hTH : P1.TcbPlaced (P1.Heap.tcbs H) := by rw [← J.tcbs_eq.1]; exact hT
  set K : U64 := ⟨BitVec.ofNat 64 Kv⟩ with hKdef
  have hKv : K.val = Kv := by
    show (BitVec.ofNat 64 Kv).toNat = _
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hKt : (core.num.U64.wrapping_add t K).val = t.val + K.val := tfield_val hta (by omega)
  have hreq : wa = core.num.U64.wrapping_add t K := UScalar.eq_of_val_eq (by rw [hwav, hKt, hKv])
  subst hreq
  have hwa : P1.Aligned (core.num.U64.wrapping_add t K) := P1.field_aligned hta (by omega) (by omega)
  have hw : P1.WritesIn st s (L.wr s (core.num.U64.wrapping_add t K) v) (· = core.num.U64.wrapping_add t K) :=
    P1.writesIn_wr hwa
  have hblk := (P1.blk_rf J.blk (hw.mono fun b hb => Or.inl ⟨t, htH, K, by omega, by omega, hb⟩)).1
  have hfoot : P1.WritesIn st s (L.wr s (core.num.U64.wrapping_add t K) v) (P1.KW st (P1.Heap.tcbs H) Cs
      (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) ∅ s) :=
    P1.foot_field hTH htH (by omega) (by omega) (by omega) ⟨by omega, by omega⟩
  have hX' := J.xtop.tcbWrF ht _ Kv hK (by rw [hKt, hKv]) v
  have hks : L.ksb (L.wr s (core.num.U64.wrapping_add t K) v) = L.ksb s := hw.1
  have hwF : P1.WritesIn st s (L.wr s (core.num.U64.wrapping_add t K) v) (Ipc.FinW (st := st) Z.T Z.N Z.C Z.c s σ) :=
    hw.mono fun b hb => Or.inr ⟨t, ht, Kv, by omega, by omega, by omega, by omega, by omega, by rw [hb, hKt, hKv]⟩
  obtain ⟨-, -, kb, -, -⟩ := J.finW_keeps hwF
  have hA : QKY σ σ := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun p => Or.inl rfl⟩
  have hBW : BufWordRel Z.T (L.mem (L.wr s (core.num.U64.wrapping_add t K) v)) σ := J.buf.frame kb hA.bufKeep
  have hI3 := hX'.irelK (by rw [hks]; exact J.ks) hBW
  exact J.reg_frameFp hI3 (hw.mono fun b hb => Or.inr ⟨t, ht, by rw [hb, hKt, hKv]; omega,
    by rw [hb, hKt, hKv]; omega⟩) hA (YKeep.of_kheap rfl) J.inv hblk hfoot

set_option maxHeartbeats 8000000 in
/-- **WriteFPU's copy into a TCB's FPU image at `J`** (`copy_words_inv`,
each word by `JAtZ.fpuWrJ`). -/
theorem JAtZ.copyFpuJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T) (src : U64) :
    tcb.copy_words st s src (core.num.U64.wrapping_add t layout.tcb.FPU) 337#u64 ⦃ s' =>
      ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D s' a σ ⦄ := by
  obtain ⟨Q, R0, hcq, -⟩ := J.xtop.fin.1.1.1.lists
  have hpf := (hcq.tcbs t ht).fits
  have hpa := (hcq.tcbs t ht).align
  have hfpu : (core.num.U64.wrapping_add t layout.tcb.FPU).val = t.val + 512 := by
    unfold layout.tcb.FPU
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  refine copy_words_inv (fun s' => ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D s' a σ) s src _ _
    ⟨Z.vs, J⟩ ?_
  rintro s2 i ⟨V, J2⟩ hi v
  have hiv : (core.num.U64.wrapping_mul i 8#u64).val = 8 * i.val := by
    simp [core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]
    have : i.val < 337 := hi
    omega
  have hi' : i.val < 337 := hi
  obtain ⟨V', J3⟩ := J2.fpuWrJ (t := t) ht
    (core.num.U64.wrapping_add (core.num.U64.wrapping_add t layout.tcb.FPU) (core.num.U64.wrapping_mul i 8#u64))
    (512 + 8 * i.val) ⟨by omega, by omega, by omega⟩ (by
    have h1 : (core.num.U64.wrapping_add t layout.tcb.FPU).val + (core.num.U64.wrapping_mul i 8#u64).val < 2 ^ 64 := by
      rw [hfpu, hiv]; omega
    clear h1
    unfold layout.tcb.FPU
    simp only [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq]
    simp [U64.size, U64.numBits]
    omega) v
  exact ⟨V', J3⟩

/-- **`JAtZ` at another arch state related to the same CR3** (`JAtZ.arFrS`
with the spec state kept, `XTopAt.arch`). -/
theorem JAtZ.archJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {a' : A}
    (hAR : AR a' σ.archState.x64CurrentCr3) : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a' σ :=
  J.arFrS (arFr_fpuOwner σ σ.machineState σ.archState.x64CurrentFpuOwner) (J.xtop.arch hAR)

end

end

end Fl4Proofs.P3
