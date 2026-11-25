/-
P2 (line vlift, gen 3): **the timer paths' layout premises at `userV K`** (companion of `P2/E2EVTimer.lean`,
split off to keep each file's imports small).

`stLay_userV`, `irqLay_userV`, `stEnt_userV`, `stEntK_userV`, `irqEnt_userV`, `irqEntM_userV`: the timer paths'
`Pre` (`StEntK` / `IrqEntM`) at `userV K` from the `K` one, given `RegionOKV`, `VcpuKs` (derived from `VcpuHeap`
[J] and P3's `JKern.hksIn` in `P2/E2EVHeap.lean`), the kernel-state block's fit, `L.ksb s = K.ksb`
(`SlJAtZ.ksb`), `TabNoV` (ASID table / pool words, `tabNoV_of`) and `irq < 128` (the IRQ state word lies in the
block). Premises: none beyond those named arguments.
-/
import Fl4Proofs.P2.E2EVHeap
import Fl4Proofs.P2.E2EVTimer
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EV
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.PathObl Fl4Proofs.P2.E2E Fl4Proofs.P2.OwnMapV
open Fl4Proofs.P2.OwnMap (fld)

noncomputable section
open Classical

/-! ## The layout premises at `userV K` -/

section lay
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {K : KLayoutV}
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s : S}

theorem irqOff_val {irq : U64} (h : irq.val < 128) : (Fl4Proofs.P3.irqOff irq).val = 224 + 8 * irq.val := by
  unfold Fl4Proofs.P3.irqOff
  simp only [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq]
  simp [U64.size, U64.numBits]
  omega

theorem stLay_userV (hK : RegionOKV K) (hks : VcpuKs K) (hf : K.ksb.val + 13568 ≤ 2 ^ 64) (hk : L.ksb s = K.ksb)
    (h : StLay K.toKLayout st T Scs Z s) : StLay (userV K) st T Scs Z s where
  nd := h.nd
  tcb := h.tcb
  sc := h.sc
  dom := h.dom
  dtm := h.dtm
  domA := h.domA
  dtmA := h.dtmA
  user b hb := by
    rcases hb with hb | ⟨v, hv, _⟩
    · exact h.user b hb
    · exact hK.none v b hv
  domU := by
    rintro (hb | hv)
    · exact h.domU hb
    · rw [hk] at hv; exact notVData_of_noVcpu (ksv_of hks hf).1 hv
  dtmU := by
    rintro (hb | hv)
    · exact h.dtmU hb
    · rw [hk] at hv; exact notVData_of_noVcpu (ksv_of hks hf).2 hv

theorem irqLay_userV (hK : RegionOKV K) (hks : VcpuKs K) (hf : K.ksb.val + 13568 ≤ 2 ^ 64) (hk : L.ksb s = K.ksb)
    {irq : U64} (hirq : irq.val < 128) (hT : TabNoV (L := L) K s) (h : IrqLay K.toKLayout st Nt irq s) :
    IrqLay (userV K) st Nt irq s where
  iq := h.iq
  kr := h.kr
  tab := h.tab
  ntw := h.ntw
  cs := h.cs
  iqU i hi := by
    rintro (hb | hv)
    · exact h.iqU i hi hb
    · rw [Fl4Proofs.P3.state_off_eq] at hi
      have e := ok_inj_ff hi
      subst e
      rw [hk] at hv
      exact notVData_of_noVcpu (noVcpu_ks hks hf (by rw [irqOff_val hirq]; omega)) hv
  krU := by
    rintro (hb | hv)
    · exact h.krU hb
    · have e : krA (L := L) s = core.num.U64.wrapping_add K.ksb layout.ks.KERNEL_ROOT := by unfold krA; rw [hk]
      rw [e] at hv
      exact notVData_of_noVcpu (noVcpu_ks hks hf (by simp [layout.ks.KERNEL_ROOT])) hv
  tabU hi hh := by
    refine ⟨?_, fun lo hl hn => ?_⟩
    · rintro (hb | hv)
      · exact (h.tabU hi hh).1 hb
      · exact (hT hi hh).1 hv
    · rintro (hb | hv)
      · exact (h.tabU hi hh).2 lo hl hn hb
      · exact (hT hi hh).2 lo hl hn hv

variable {target irq : U64} {m : U64 → U64}

theorem stEnt_userV (hK : RegionOKV K) (hks : VcpuKs K) (hf : K.ksb.val + 13568 ≤ 2 ^ 64) (hk : L.ksb s = K.ksb)
    (h : StEnt K.toKLayout st T Cs Ω H Sg Rp Scs Nt Z Ac target s) :
    StEnt (userV K) st T Cs Ω H Sg Rp Scs Nt Z Ac target s :=
  ⟨h.inv, stLay_userV hK hks hf hk h.lay, h.pre, h.aff, h.tg⟩

theorem stEntK_userV (hK : RegionOKV K) (hks : VcpuKs K) (hf : K.ksb.val + 13568 ≤ 2 ^ 64) (hk : L.ksb s = K.ksb)
    (h : StEntK K.toKLayout st T Cs Ω H Sg Rp Scs Nt Z Ac target m s) :
    StEntK (userV K) st T Cs Ω H Sg Rp Scs Nt Z Ac target m s :=
  ⟨stEnt_userV hK hks hf hk h.ent, fun x hx hxu => h.mem x hx fun h' => hxu (Or.inl h')⟩

theorem irqEnt_userV (hK : RegionOKV K) (hks : VcpuKs K) (hf : K.ksb.val + 13568 ≤ 2 ^ 64) (hk : L.ksb s = K.ksb)
    (hirq : irq.val < 128) (hT : TabNoV (L := L) K s) (h : IrqEnt K.toKLayout st T Cs Ω H Sg Rp Scs Nt Z Ac irq s) :
    IrqEnt (userV K) st T Cs Ω H Sg Rp Scs Nt Z Ac irq s :=
  ⟨h.inv, stLay_userV hK hks hf hk h.lay, irqLay_userV hK hks hf hk hirq hT h.ly, h.asid, h.aff, h.nth⟩

theorem irqEntM_userV (hK : RegionOKV K) (hks : VcpuKs K) (hf : K.ksb.val + 13568 ≤ 2 ^ 64) (hk : L.ksb s = K.ksb)
    (hirq : irq.val < 128) (hT : TabNoV (L := L) K s)
    (h : IrqEntM K.toKLayout st T Cs Ω H Sg Rp Scs Nt Z Ac irq m s) :
    IrqEntM (userV K) st T Cs Ω H Sg Rp Scs Nt Z Ac irq m s :=
  ⟨irqEnt_userV hK hks hf hk hirq hT h.ent, fun x hx hxu => h.mem x hx fun h' => hxu (Or.inl h')⟩

end lay

end
end Fl4Proofs.P2.E2EV
