/-
P3 (issue #16, FL4 #71), VSpace FrameBatch: **`batch_map` at `J` with the
deletion's liveness facts** (KENTRY-PLAN fb3l): XTopJointFbMapJ's
`JAtZ.batchMapJ`, and on its `Ok` path `LiveDN` at the same sets (the slot's cap
replaced by a frame cap of the same frame, the page tables written), `NoSwitch`,
`SpecGlob` and `PPR0` kept (the batch's loop invariant `FbMidJ` carries them for
the DELETE entries' frame deletes): `LiveDN` by LiveFrame's `LiveDN.simX` (the slots'
caps alike, `LSim`), `SpecGlob` by `SpecGlob.of_capPage` (the spec's caps as before but a page
cap over a page cap), `PPR0` by `PPK.of_fbKeep`.
-/
import Fl4Proofs.P3.XTopJointFbMapJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section Spec
open Fl4Spec

/-- **`SpecGlob` across a step writing a page cap over a page cap** (the rest of the caps kept). -/
theorem SpecGlob.of_capPage {σ σ' : State Unit} {sl : CslotPtr} (h : SpecGlob σ) (hk : Vs.CapPage σ σ' sl)
    (h0 : ∃ a0, capOpt (σ.kheap sl.1) sl.2 = some a0 ∧ IsPageCap a0)
    (hn : σ'.interruptIrqNode = σ.interruptIrqNode) (hi : σ'.idleThread = σ.idleThread) : SpecGlob σ' := by
  obtain ⟨a0, ha0, hp0⟩ := h0
  refine ⟨fun irq a ha => ?_, fun p cref a ha hp => ?_, fun p cref a ha hp => ?_⟩
  · rw [hn] at ha
    rcases hk _ _ _ ha with h' | ⟨e1, e2, -⟩
    · exact h.irq irq a h'
    · exfalso
      rw [← e1, ← e2] at ha0
      rcases h.irq irq a0 ha0 with rfl | ⟨r, b, rs, rfl⟩ <;> exact hp0
  · rcases hk _ _ _ ha with h' | ⟨-, -, hpa⟩
    · intro irq; rw [hn]; exact h.ref p cref a h' hp irq
    · exact absurd hpa hp
  · rcases hk _ _ _ ha with h' | ⟨-, -, hpa⟩
    · rw [hi]; exact h.idle p cref a h' hp
    · exact absurd hpa hp

/-- **`FbKeep` keeps what `PPR0` reads.** -/
theorem PPK.of_fbKeep {σ σ' : State Unit} (h : FbKeep σ σ') : PPK σ σ' where
  cons := h.cons
  time := h.time
  csc := h.csc
  rel u hu := by rw [h.rel] at hu; exact hu
  sc p y n hp := by
    rcases h.kh p with e | ⟨a, a', -, ha', -⟩ | ⟨r, cs, cs', -, hc'⟩ | ⟨x, y', -, hy', -⟩
    · rw [← e]; exact hp
    · rw [hp] at ha'; cases ha'
    · rw [hp] at hc'; cases hc'
    · rw [hp] at hy'; cases hy'
  tcb p y hp := by
    rcases h.kh p with e | ⟨a, a', -, ha', -⟩ | ⟨r, cs, cs', -, hc'⟩ | ⟨x, y', hx, hy', hxy⟩
    · exact ⟨y, by rw [← e]; exact hp, rfl, id⟩
    · rw [hp] at ha'; cases ha'
    · rw [hp] at hc'; cases hc'
    · rw [hp] at hy'; cases hy'
      exact ⟨x, hx, hxy.2.2.2.2.2.1.symm, fun hb => by rw [hxy.1]; exact hb⟩
  ct := h.ct
  idle := h.idle
  ns hn u := by rw [h.act]; exact hn u
  ina p x y hx hy hs := by
    obtain ⟨y', hy', hc⟩ := h.tcb hx
    rw [hy] at hy'; cases hy'
    exact Or.inl (hc.1.trans hs)
  nq hq d p := by rw [h.ct, h.rq]; exact hq d p

end Spec

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 8000000 in
/-- **`JAtZ.batchMapJ` with the liveness facts** (module docstring). -/
theorem JAtZ.batchMapJL [Fl4Proofs.P1.PlainStore st] (hA : ArchRefines arI AR) {s : S} {a : A}
    {τ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a τ)
    (hLv : LiveDN (L := L) Z.th H Cs Z.G s τ) (hns : Vs.NoSwitch τ) (hsg : SpecGlob τ) (hp0 : PPR0 τ)
    {pc : U64} {r : Nat} (hpc : Z.th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {p1 as1 : U64} (has1 : as1 ≠ 0#u64) (has2 : as1.val < 2 ^ 20)
    (hf : ExceptT.run (Fl4Spec.findVspaceForAsid (Z := Unit) as1.bv) τ = ({(.ok p1.bv, τ)}, False))
    (op depth a1 cr a2 : U64) (dd : Bool) (cn dcn : capability.Cap) (a0 : U64)
    (b : Fl4Spec.Fl4FrameBatchInvocation) (hbv : b.vspace = p1.bv) (hba : b.asid = as1.bv)
    (hbm : b.mapRights = a1.bv) (hbat : b.attr = a2.bv) :
    vspace.batch_map st arI s a (cslotAddr (pc.bv, idx)) ⟨p1, as1, op, depth, a1, cr, a2, dd, cn, dcn⟩ a0 ⦃ res =>
      (∃ e e', res.1 = .Err e ∧ MapErrRel e e' ∧
        ExceptT.run (Fl4Spec.fbMap (Z := Unit) b (pc.bv, idx) a0.bv) τ = ({(.error e', τ)}, False) ∧
        res.2.1 = s ∧ res.2.2 = a) ∨
      (res.1 = .Ok () ∧ ∃ τ1, ((.ok (), τ1) : Except Fl4Spec.SyscallError Unit × Fl4Spec.State Unit) ∈
          (ExceptT.run (Fl4Spec.fbMap (Z := Unit) b (pc.bv, idx) a0.bv) τ).1 ∧
        JAtZ (L := L) arI AR Z H Cs Ac Lst D res.2.1 res.2.2 τ1 ∧ FbKeep τ τ1 ∧ FbFootK (L := L) Z s res.2.1 ∧
        LiveDN (L := L) Z.th H Cs Z.G res.2.1 τ1 ∧ Vs.NoSwitch τ1 ∧ SpecGlob τ1 ∧ PPR0 τ1) ⦄ := by
  refine WP.spec_mono (JAtZ.batchMapJX arI hA J hpc hidx has1 has2 hf op depth a1 cr a2 dd cn dcn a0 b hbv hba hbm
    hbat) ?_
  rintro ⟨r0, s', a'⟩ (h | ⟨h1, τ1, hm, J', hK, hF, F, hW, hsim, -, hCP, a00, ha00, hp00⟩)
  · exact Or.inl h
  refine Or.inr ⟨h1, τ1, hm, J', hK, hF, ?_, fun u => by rw [F.act]; exact hns u,
    hsg.of_capPage hCP ⟨a00, ha00, hp00⟩ F.irqN F.idle, hp0.of_ppk (PPK.of_fbKeep hK)⟩
  have Ap : VsApart (L := L) Z H Cs s := jVsApartHyp arI Z H Cs Ac Lst D s a τ rfl J
  have hdk : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s' := dbgKeep_of_writes J.blk hW fun b hb =>
    J.notDbg (fun p hp => J.vsxObjW Ap hpc hidx hb hp (fun z h => by cases h))
      (fun c hc => J.vsxNodeW hpc hidx hb hc)
  exact (LiveDN.simX J hLv J'.xtop rfl rfl rfl (fun p hp => J'.jcov.dead p (J.zD p hp)) F.idle hdk
    (fun sl h => by rw [F.orig] at h; exact h) hsim).1

end

end

end Fl4Proofs.P3
