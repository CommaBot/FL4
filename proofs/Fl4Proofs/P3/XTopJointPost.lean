/-
P3 (DESIGN.md §9), CSpace: **a cleanup cap's `post_cap_deletion` at `J`**
(`JPostDelHyp`, XTopJointDelR, discharged: `jPostDelHyp_of`). The IRQ
handler's and the IO port's cleanups are kernel-state steps (XTopPostDel's
`post_irqX`, `post_ioX`: FL4 writes `KsW` words only, the spec's step is
`KsStep`), so `JAtZ` after by `jowes_ks` and `cs_frame`, as StepSem's
kernel-state steps (`stepClosed_jat`).
-/
import Fl4Proofs.P3.XTopJointDelR
import Fl4Proofs.P3.XTopPostDel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

set_option maxHeartbeats 4000000 in
/-- **`JPostDelHyp` holds** (module docstring), from the kernel-state block's
layout at the `XTopAt` states (`IntLayout`, `IoLayout` [P]) and the arch IRQ
operations total and keeping `AR` (`ARMask` [P]), as `xPostDelHyp_of`. -/
theorem jPostDelHyp_of {AR : A → Fl4Spec.Cr3 → Prop} (hAM : ARMask arI AR) {th : TypedHeap}
    (hLay : ∀ (Z : XSets) s a σ, Z.th = th → XTopAt (L := L) AR Z s a σ →
      IntLayout th (L.ksb s) ∧ IoLayout th (L.ksb s))
    (hmask : ∀ (a : A) (irq : U64) (b : Bool), ∃ a', arI.mask_irq a irq b = ok a')
    (hfree : ∀ (a : A) (irq : U64), ∃ a', arI.irq_free a irq = ok a') :
    JPostDelHyp (L := L) arI AR th := by
  intro Z H Cs kb hth s a σ G cl _ ⟨V, Ac, Lst, D, J, hkb⟩ hcl hcln hclw
  subst hth
  have hX := J.xtop
  have hLy := hLay (Z.mv G V) s a σ rfl hX
  have hfin : ∀ (s' : S) (a' : A) (σ' : Fl4Spec.State Unit), SlotsSame (Z.mv G V).th (L.mem s) (L.mem s') →
      P1.WritesIn st s s' (KsW (L.ksb s)) → KsStep σ σ' → XTopAt (L := L) AR (Z.mv G V) s' a' σ' →
      WJ (L := L) arI AR Z H Cs kb s' a' σ' G := fun s' a' σ' hSS hw hO hX' => by
    obtain ⟨Ac', Lst', D', R⟩ := jowes_ks arI s s' a a' σ σ' hw hO _ H Cs Ac Lst D rfl J hX'
    exact ⟨V, Ac', Lst', D', J.cs_frame hw.1 hX' (KBack.of_kheap hO.kh) (JCs.same J hSS (KSz.of_kheap hO.kh)) R,
      by rw [hw.1]; exact hkb⟩
  cases cl <;> simp only [CleanCap] at hcl
  · exact absurd rfl hcln
  · refine WP.spec_mono (post_irqX arI hAM hX J.ks (hLy.1) hmask hfree _ hclw) ?_
    rintro r ⟨hSS, -, σ', hm, hCR, hw, hO, hX'⟩
    exact ⟨hSS, σ', hm, hCR, hfin _ _ _ hSS hw hO hX'⟩
  · obtain ⟨hf, hl, hfl⟩ := hclw
    refine WP.spec_mono (post_ioX arI hX J.ks (hLy.2) _ _ _ hfl hl) ?_
    rintro r ⟨hSS, -, σ', hm, hCR, hw, hO, hX'⟩
    exact ⟨hSS, σ', hm, hCR, hfin _ _ _ hSS hw hO hX'⟩

end

end

end Fl4Proofs.P3
