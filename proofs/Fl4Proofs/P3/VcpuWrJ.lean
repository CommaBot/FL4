/-
P3 (line vlift, gen 6): **a write of a VCPU word at `J`** (the spec state kept).

The joint invariant `JAtZ` reads FL4 memory only at the words of its sets' objects (TCBs, endpoints, replies,
notifications, SCs, the typed heap's CNodes, the VSpace tables and pools), the kernel-state block and nodes, the
ASID-table area, the IPC-buffer words `Z.B`, and the RAM untyped caps' free parts (`UtCapP3.zero`). A VCPU is a
spec `vcpu` object (`archObj (.vcpu _)`, 2^15 bytes) and an `H` object `.other 15`; P3's relation reads none of
its words. So a write of any word of it (not an IPC-buffer word) keeps `JAtZ` with σ unchanged: this is
`JAtZ.frameWrJ` (XTopJointReadFpu) with its five side facts derived here from the VCPU's placement:

* `UserW`: apart from every non-`other` object of `H` (`HeapOK.disj`, the VCPU an `H` object of another kind),
  hence from the sets' TCBs / endpoints / replies / notifications (`zH`) and SCs (`JPlaced.sc`); apart from the
  typed heap's CNodes (`JPlaced.cnode`: an `H` object, and not the VCPU since it is a spec CNode,
  `CapRel`'s `cnode`) and from the VSpace tables / pools (`vsFr_other`: `H` objects of ≥ 4 KiB, spec tables /
  pools, so not the VCPU); off core `Z.c`'s node, the kernel-state block and the ASID-table area by `hks`.
* inside a spec object: the VCPU itself (`archKobjSize (.vcpu _) = 15`).
* off `[ksb, ksb + 304384)`: `hks`.

Premises (all facts of the VCPU, asked by the caller): `hσ` the spec object, `hH` the `H` object, `hks` its
placement off the kernel-global area. No named premise here; P2 states them (`P2/E2EVVcpuWr.lean`).
-/
import Fl4Proofs.P3.XTopJointReadFpu
import Fl4Proofs.P3.XTopJointFinVs
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 8000000 in
/-- **A word of a VCPU written at `J`** (module docstring; the spec state kept). -/
theorem JAtZ.vcpuWrJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {p w : U64}
    (hσ : ∃ x, σ.kheap p.bv = some (.archObj (.vcpu x))) (hH : H p = some (.other 15))
    (hks : p.val + 32768 ≤ (L.ksb s).val ∨ (L.ksb s).val + 304384 ≤ p.val)
    (hal : P1.Aligned w) (g1 : p.val ≤ w.val) (g2 : w.val < p.val + 32768)
    (hnB : ∀ wp ∈ Z.B, wp.1 ≠ w) (v : U64) :
    JAtZ (L := L) arI AR Z H Cs Ac Lst D (L.wr s w v) a σ := by
  obtain ⟨x, hσx⟩ := hσ
  have hHO := J.kern.heap
  have h15 : (2 : Nat) ^ 15 = 32768 := by norm_num
  have hw8 : w.val % 8 = 0 := hal
  have hpa : p.val % 32768 = 0 := by
    have := hHO.align p _ hH; simpa [P1.HKind.bits, h15] using this
  -- apart from every other `H` object
  have wap : ∀ q k', H q = some k' → q ≠ p → w.val + 8 ≤ q.val ∨ q.val + 2 ^ k'.bits ≤ w.val := by
    intro q k' hq hne
    rcases hHO.disj p _ q k' hH hq (Ne.symm hne) with h | h
    · simp only [P1.HKind.bits, h15] at h; left; omega
    · right; omega
  have hneK : ∀ q k', H q = some k' → (∀ z, k' ≠ .other z) → q ≠ p := fun q k' hq hk' e => by
    subst e; rw [hH] at hq; exact hk' 15 (Option.some.inj hq).symm
  have hAp : ∀ q k, H q = some k → (∀ z, k ≠ .other z) → w.val + 8 ≤ q.val ∨ q.val + 2 ^ k.bits ≤ w.val :=
    fun q k hq hk => wap q k hq (hneK q k hq hk)
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hR := J.xtop.rel.2.1.1
  -- the typed heap's CNodes are spec CNodes, so not the VCPU
  have hcn : ∀ q r, Z.th q = some (.cnode r) → w.val + 8 ≤ q.val ∨ q.val + 32 * 2 ^ r ≤ w.val := by
    intro q r hq
    have hne : q ≠ p := fun e => by
      subst e; obtain ⟨cs, hc, -⟩ := hR.cnode q r hq; rw [hc] at hσx; cases hσx
    have e32 : 2 ^ (r + 5) = 32 * 2 ^ r := by rw [pow_add]; norm_num; ring
    have := wap q _ (hJ.cnode q r hq) hne
    simp only [P1.HKind.bits] at this; rw [e32] at this; exact this
  have htc : ∀ t, Z.th t = some .tcb → w.val + 8 ≤ t.val ∨ t.val + 4096 ≤ w.val := by
    intro t ht
    have hHt := (hJ.tcb t).1 ht
    have := hAp t _ hHt fun _ e => by cases e
    simpa [P1.HKind.bits] using this
  -- the sets' tables and pools are spec tables / pools, so not the VCPU
  have hF := J.xtop.fin
  have hvs : ∀ q', (q' ∈ Z.P ∨ q' ∈ Z.L4 ∨ q' ∈ Z.L3 ∨ q' ∈ Z.L2 ∨ q' ∈ Z.L1) →
      w.val + 8 ≤ q'.val ∨ q'.val + 4096 ≤ w.val := by
    intro q' hq'
    obtain ⟨n', hn', hH'⟩ := J.vsFr_other hq'
    have hne : q' ≠ p := by
      intro e; subst e
      rcases hq' with hv | hv | hv | hv | hv
      · obtain ⟨f, hf, -⟩ := hF.2.1.pool q' hv; rw [hf] at hσx; cases hσx
      · obtain ⟨f, hf, -⟩ := hF.2.2.1.l4 q' hv; rw [hf] at hσx; cases hσx
      · obtain ⟨f, hf, -⟩ := hF.2.2.1.l3 q' hv; rw [hf] at hσx; cases hσx
      · obtain ⟨f, hf, -⟩ := hF.2.2.1.l2 q' hv; rw [hf] at hσx; cases hσx
      · obtain ⟨f, hf, -⟩ := hF.2.2.1.l1 q' hv; rw [hf] at hσx; cases hσx
    have h4 : 2 ^ 12 ≤ 2 ^ n' := Nat.pow_le_pow_right (by decide) hn'
    rcases wap q' _ hH' hne with h | h
    · exact Or.inl h
    · simp only [P1.HKind.bits] at h; right; omega
  -- core `Z.c`'s node lies below the ASID-table area
  obtain ⟨Q, R0, hcq, -⟩ := J.xtop.fin.1.1.1.lists
  have hcC : Z.c ∈ Cs := hcq.cur ▸ J.kern.cpuCs
  have hc64 := J.kern.csLt Z.c hcC
  have hnb : L.nodeBase s Z.c = (L.ksb s).val + 13568 + Z.c.val * 4288 := rfl
  have hksw : w.val + 8 ≤ (L.ksb s).val ∨ (L.ksb s).val + 304384 ≤ w.val := by omega
  have hu : UserW (L := L) Z s σ w :=
    { al := hal
      far := ⟨by rw [hnb]; omega,
        fun t ht => by
          have := hAp t _ (J.zH.1 t ht) fun _ e => by cases e
          simpa [P1.HKind.bits] using this,
        fun sc hsc y n hky => by
          have hHs := (hJ.sc sc y n (J.c0 sc hsc) hky).2
          have := hAp sc _ hHs fun _ e => by cases e
          simpa [P1.HKind.bits] using this⟩
      vobj := fun hv => by
        rcases hv with ⟨q, r, hq, c1, c2⟩ | ⟨t, ht, c1, c2⟩ | ⟨q', hq', c1, c2⟩ | h
        · have := hcn q r hq; omega
        · have := htc t ht; omega
        · have := hvs q' hq'; omega
        · omega
      ep := fun e he => by
        have := hAp e _ (J.zH.2.1 e he) fun _ e => by cases e
        simpa [P1.HKind.bits] using this
      rep := fun r hr => by
        have := hAp r _ (J.zH.2.2.1 r hr) fun _ e => by cases e
        simpa [P1.HKind.bits] using this
      ntfn := fun n hn => by
        have := hAp n _ (J.zH.2.2.2 n hn) fun _ e => by cases e
        simpa [P1.HKind.bits] using this }
  have hObj : ∃ o ko, σ.kheap o = some ko ∧ o.toNat ≤ w.val ∧ w.val < o.toNat + 2 ^ Fl4Spec.objBits ko :=
    ⟨p.bv, _, hσx, g1, by
      show w.val < p.val + 2 ^ Fl4Spec.archKobjSize (.vcpu x)
      simp only [Fl4Spec.archKobjSize, h15]; exact g2⟩
  exact J.frameWrJ hu hnB hAp hObj hksw v

end

end

end Fl4Proofs.P3
