/-
P1: the VCPU list's link writes of a VCPU's creation (`vcpu::init`: the
kernel-global `VCPU_HEAD`, the old head's `PREV`) lie outside the retype
window but are cap-slot words (`CapW`), which `RetypeP1Step`'s write frame
admits: the head is a kernel-global word (`vhead_capw`), and a VCPU is a heap
object of kind `.other 15` (`vcpu_obj_capw`).
-/
import Fl4Proofs.P1.QueueFinIo
import Fl4Proofs.P1.QueueHeapAdd
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]
variable {H : Heap} {Cs : Set U64} {Ac : Set U64}

/-- **The VCPU list's head word is a cap-slot word** (`CapW`: a kernel-global
word, in `Ω` and off the frame words): a VCPU's creation (`vcpu::init`)
writes it outside the retype window, and `RetypeP1Step`'s write frame admits
it. -/
theorem vhead_capw {s : S}
    (h : BlkOK st H.tcbs Cs H.omega H H.frame H.replies H.scs H.ntfns H.scBits Ac s) :
    CapW H.tcbs H.omega H.frame (vHeadA st s) := by
  obtain ⟨⟨Q, R, h0⟩, -, -, -, hSg⟩ := h
  have hN := h0.nodes _ h0.cur
  have hfit := hN.fits
  unfold LawfulStore.nodeBase at hfit
  have hv : (vHeadA st s).val = (L.ksb s).val + 80 := by
    unfold vHeadA; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, layout.ks.VCPU_HEAD]
    omega
  refine Or.inr ⟨hSg.ksΩ _ (by simp [layout.ks.VCPU_HEAD]) (by simp [layout.ks.VCPU_HEAD]), fun hm => ?_⟩
  have := hSg.ks _ hm
  rw [hv] at this; omega

/-- **A word of a VCPU heap object is a cap-slot word** (`CapW`: in `Ω`, off
the frame words): the old list head's `PREV` word, which a VCPU's creation
writes outside the retype window, is one. -/
theorem vcpu_obj_capw (hH : HeapOK H) {v o : U64} (hv : H v = some (.other 15)) (ho : o.val < 2 ^ 15)
    (h8 : o.val % 8 = 0) : CapW H.tcbs H.omega H.frame (core.num.U64.wrapping_add v o) := by
  have hal := hH.align v _ hv
  have hfit := hH.fits v _ hv
  rw [show (HKind.other 15).bits = 15 from rfl] at hal hfit
  have hb : (core.num.U64.wrapping_add v o).val = v.val + o.val := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  have hal8 : (core.num.U64.wrapping_add v o).val % 8 = 0 := by
    rw [hb]; have : v.val % 8 = 0 := by omega
    omega
  refine Or.inr ⟨⟨hal8, v, .other 15, hv, Or.inr (Or.inr (Or.inl ⟨15, rfl⟩)), ⟨by rw [hb]; omega, by
    rw [hb, show (HKind.other 15).bits = 15 from rfl]; omega⟩⟩, ?_⟩
  rintro ⟨-, p, k, hp, hk, hin⟩
  have hne : p ≠ v := by
    rintro rfl; rw [hv] at hp; cases hp
    rcases hk with h | ⟨z, h⟩ | ⟨h, -⟩ <;> cases h
  have h1 := hin.1; have h2 := hin.2
  have e : (HKind.other 15).bits = 15 := rfl
  rw [hb] at h1 h2
  have := hH.disj v (.other 15) p k hv hp hne.symm
  rw [e] at this
  omega

end

end Fl4Proofs.P1
