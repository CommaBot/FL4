/-
P1 (aarch64, gen 39): **the non-VSpace steps of the Zombie loop keep every `VsR` word** (`VsKeep`), not only "kept
or zeroed" (`VsZ`).

Gen 37/38's loop (QueueZombieP / QueueZombieQ) exports only `VsZ` for its steps that are not VSpace finalisations
(`finVZ`, `cdt.empty_slot.vz`, `sched.preemption_point.vz`, `vsz_cw`), although each is proved from a write set that
misses every `VsR` word. A typing that must keep a nonzero `VsR` word (a `HighVSpace` root's entry 511, QueueHiTy) is
not kept by an abstract `VsZ` step; it is kept by a `VsKeep` step. This module re-states those steps with `VsKeep`
(the same write sets; the texts are QueueVsWs's `vsz_*` / QueueZombieP's `.vz` with `VsZ.of_w` replaced by
`VsKeep.of_w`):

* **`VsKeep kb Pt s s'`** (every `VsR kb Pt` word kept), `VsKeep.refl`, `VsKeep.trans`, `VsKeep.vsz`, `VsKeep.of_w`;
* `vsk_tw`, `vsk_cw`, `vsk_irq`, `sched.preemption_point.vk`, `cdt.delete_one.vk`, `finalise_cap.irq_vk`,
  **`finVK`** (every `ZS` cap's finalisation keeps every `VsR` word), `cdt.empty_slot.vk`.

No named premise; new definitions and theorems only.
-/
import Fl4ProofsA64.P1.QueueZombieP
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-- **Every `VsR` word kept.** -/
def VsKeep (st : machine.Store S) [L : LawfulStore st] (kb : U64) (Pt : Set U64) (s s' : S) : Prop :=
  ∀ b, VsR kb Pt b → L.mem s' b = L.mem s b

theorem VsKeep.refl {kb : U64} {Pt : Set U64} (s : S) : VsKeep st kb Pt s s := fun _ _ => rfl

theorem VsKeep.trans {kb : U64} {Pt : Set U64} {s1 s2 s3 : S} (h1 : VsKeep st kb Pt s1 s2)
    (h2 : VsKeep st kb Pt s2 s3) : VsKeep st kb Pt s1 s3 := fun b hb => (h2 b hb).trans (h1 b hb)

theorem VsKeep.vsz {kb : U64} {Pt : Set U64} {s s' : S} (h : VsKeep st kb Pt s s') : VsZ st kb Pt s s' :=
  VsZ.of_keep h

/-- A write set missing every `VsR` word keeps every `VsR` word. -/
theorem VsKeep.of_w {kb : U64} {Pt : Set U64} {s s' : S} {F : U64 → Prop} (hal : ∀ b, VsR kb Pt b → Aligned b)
    (hw : WritesIn st s s' F) (hF : ∀ b, VsR kb Pt b → ¬ F b) : VsKeep st kb Pt s s' :=
  fun b hb => hw.mem_eq (hal b hb) (hF b hb)

namespace W7
namespace R
namespace ST

local notation "wa" => core.num.U64.wrapping_add

variable {A : Type _} {ar : machine.Arch A}

section vk
variable {OS Vc Ub D : Set U64} {kb : U64} {Pt : Set U64}

theorem vsk_tw (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) {s s' : S} (hw : WritesIn st s s' (TW Ω Sg Scs Z Vc Ub)) :
    VsKeep st kb Pt s s' :=
  VsKeep.of_w hR.al hw fun b hb => vsr_not_tw hR hb

theorem vsk_cw {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {s0 : S}
    (q : SchedQueuesInvX st T Cs Ω H X s0 Q R) (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) {s s' : S}
    (hw : WritesIn st s s' (W7.CapW T {b | InOS OS b} ∅)) : VsKeep st kb Pt s s' :=
  VsKeep.of_w hR.al hw fun b hb => vsr_not_cw q hR hb

theorem vsk_irq {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {s0 : S}
    (q : SchedQueuesInvX st T Cs Ω H X s0 Q R) (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) {irq : U64}
    (hi : irq.val < 5376) {s s' : S}
    (hw : WritesIn st s s' (fun b => W7.CapW T {b | InOS OS b} ∅ b ∨ IrqStW kb irq b)) : VsKeep st kb Pt s s' :=
  VsKeep.of_w hR.al hw fun b hb h => h.elim (vsr_not_cw q hR hb) fun ⟨o, ho, e⟩ =>
    hR.ks b hb o (by omega) e.symm

set_option maxHeartbeats 2000000 in
/-- **The preemption point keeps every `VsR` word** (QueueVsWs's `.vz` text). -/
theorem sched.preemption_point.vk (hP : P0.ArchTotal ar) (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) {s0 s : S}
    {a : A} (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hk : L.ksb s = kb) :
    sched.preemption_point st ar s a ⦃ r => VsKeep st kb Pt s r.2.1 ⦄ := by
  obtain ⟨Ac', hb⟩ := h.1.parts
  have q := hb.1.choose_spec.choose_spec
  have hN := q.nodes _ q.cur
  refine WP.spec_mono (sched.preemption_point.pp (Ac := Ac') hP s a hb.blk) ?_
  rintro r ⟨-, w⟩
  refine VsKeep.of_w hR.al w fun b hb' hp => ?_
  have ho := q.omega _ (hR.om b hb')
  rcases hp with e | e | e
  · exact hR.ks b hb' layout.ks.WORK_UNITS (by simp [layout.ks.WORK_UNITS]) (by rw [e, hk])
  · unfold LawfulStore.nodeA at e
    exact out_ne_node ho q.cur hN (o := layout.node.CUR_TIME) (by simp [layout.node.CUR_TIME]) (by rw [e])
  · unfold LawfulStore.nodeA at e
    exact out_ne_node ho q.cur hN (o := layout.node.CONSUMED) (by simp [layout.node.CONSUMED]) (by rw [e])

set_option maxHeartbeats 4000000 in
/-- **`delete_one` of an IRQ-node slot holding a notification or `Null`** keeps every `VsR` word. -/
theorem cdt.delete_one.vk (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS)
    (hV : VcOK T Scs Z OS Vc Ub) (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) {s0 s : S} {a : A}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) {isl : U64} (hisl : isl ∈ OS)
    (hN : ∀ c, obj.Slot.cap st isl s = ok c → IrqNt c) :
    cdt.delete_one st ar s a isl ⦃ r => VsKeep st kb Pt s r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  obtain ⟨Ac', hb⟩ := h.1.parts
  have q := hb.1.choose_spec.choose_spec
  unfold cdt.delete_one
  obtain ⟨c, hc⟩ := DPF.spec_tot (P0.obj.Slot.cap.p0 st isl s hS)
  rw [hc, bind_ok]
  refine WP.spec_bind (P0.capability.Cap.is_null.p0 c) fun bn _ => ?_
  split
  · exact (WP.spec_ok _).2 (VsKeep.refl _)
  refine WP.spec_bind (P0.cdt.is_final_capability_with_cap.p0 st s isl c hS) fun fin _ => ?_
  have hl : ZL c := by
    rcases hN c hc with ⟨n, b0, b1, b2, rfl⟩ | rfl
    · exact Or.inr (Or.inr (Or.inl ⟨n, b0, b1, b2, rfl⟩))
    · exact zl_null
  have hnI : ∀ i, c ≠ .IrqHandler i := by
    rcases hN c hc with ⟨n, b0, b1, b2, rfl⟩ | rfl <;> intro i e <;> cases e
  rw [← fc_eq_fco ar s a fin hnI]
  refine WP.spec_bind (WP.spec_and (finL hP hO hA hV h hisl hc hl a fin) (finL.tw hP h hisl hc hl a fin)) ?_
  rintro ⟨⟨rem, cl⟩, s2, a2⟩ ⟨⟨e2, h2, k2⟩, w2⟩
  try simp only at e2 h2 k2 w2
  try dsimp only
  refine WP.spec_mono (cdt.empty_slot.os (P := fun _ => False) hO h2.1.2 hisl fun s1 a1 _ => by
    rw [pcd_null]; exact (WP.spec_ok _).2 (WritesIn.refl _ _)) fun r w3 => ?_
  exact (vsk_tw hR w2).trans (vsk_cw q hR (WritesIn.mono w3 fun b hb => hb.elim id False.elim))

set_option maxHeartbeats 2000000 in
/-- **A final IrqHandler cap's `finalise_cap`** (its node slot a notification or `Null`) keeps every `VsR` word. -/
theorem finalise_cap.irq_vk (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS)
    (hV : VcOK T Scs Z OS Vc Ub) (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) {s0 s : S} {a : A}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) {irq kb' : U64} (hIO : irqSlotA kb' irq ∈ OS)
    (hN : ∀ c, obj.Slot.cap st (irqSlotA kb' irq) s = ok c → IrqNt c) (hk : L.ksb s = kb') :
    objects.finalise_cap st ar s a (.IrqHandler irq) true false ⦃ r => VsKeep st kb Pt s r.2.1 ⦄ := by
  unfold objects.finalise_cap
  simp only [↓reduceIte]
  unfold interrupt.deleting_irq_handler
  refine WP.spec_bind (Pₘ := fun r : S × A => VsKeep st kb Pt s r.1) ?_ ?_
  · refine WP.spec_bind (interrupt.irq_slot.val s irq) fun isl e => ?_
    subst e
    rw [hk]
    exact cdt.delete_one.vk hP hO hA hV hR h hIO hN
  · rintro ⟨s2, a2⟩ h2
    first
    | (simp only [objects.finalise_cap_object, ↓reduceIte, WP.spec_ok]; exact h2)
    | (simp only [objects.finalise_cap_object, ↓reduceIte]; exact (WP.spec_ok _).2 h2)
    | (simp [objects.finalise_cap_object, WP.spec_ok]; exact h2)

set_option maxHeartbeats 4000000 in
/-- **Every `ZS` cap's finalisation keeps every `VsR` word** (QueueZombieP's `finVZ` text). -/
theorem finVK (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub)
    (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) {s0 s : S} (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s)
    (hIO : IrqOK OS D (L.ksb s0)) (hN : IrqN st (L.ksb s0) s) {x : U64} (hx : x ∈ OS) {c : capability.Cap}
    (hc : obj.Slot.cap st x s = ok c) (hX : ZS Vc D Scs (L.idleW s) (L.mem s (scA (L.idleW s))) c) (a : A)
    (fin : Bool) :
    objects.finalise_cap st ar s a c fin false ⦃ r => VsKeep st kb Pt s r.2.1 ⦄ := by
  have hty := (h.1.2 x hx).1 _ (by rw [DPF.slot_cap_dec] at hc; exact hc)
  rcases hX with ((hl | ⟨p, r, g, b, rfl, -⟩ | ⟨p, t, n, rfl, -⟩) | ⟨p, rfl, hid, -⟩ | ⟨v, rfl, hvV⟩) |
    ⟨p, b, rfl, hp, hp0, hpI⟩ | ⟨irq, rfl⟩
  · exact WP.spec_mono (finL.tw hP h hx hc hl a fin) fun r hr => vsk_tw hR hr
  · exact WP.spec_mono (fin_cnode.z ar s a p r g b fin) fun r hr => by rw [hr.1]; exact VsKeep.refl _
  · rw [fin_zombie.z]; exact (WP.spec_ok _).2 (VsKeep.refl _)
  · have hp : p ∈ T := hty.1.2.2.2.2.2 p rfl
    rw [fin_cap_eq_obj (by simp)]
    exact WP.spec_mono (fin_thread.tw hP hO hV h.1.1.1 h.2 a p fin hp hid) fun r hr => vsk_tw hR hr
  · rw [fin_cap_eq_obj (by simp)]
    exact WP.spec_mono (fin_vcpu.tw hP hO hV h.1.1.1 h.2 a v fin hvV) fun r hr => vsk_tw hR hr
  · have hk := scpl_of h hc hp hp0 hpI rfl
    exact WP.spec_mono (fin_sc.tw hP h a fin hk hc) fun r hr => vsk_tw hR hr
  · have hi : irq.val < 5376 := hty.1.2.1 irq rfl
    cases fin
    · rw [finalise_cap.nonfin ar s a (irqH_nonfin irq), WP.spec_ok]; exact VsKeep.refl _
    · exact finalise_cap.irq_vk hP hO hA hV hR h (hIO.1 irq hi) (hN irq hi) h.ksb

set_option maxHeartbeats 2000000 in
/-- **`empty_slot` of a slot of `OS` with a `ClOK` cleanup keeps every `VsR` word.** -/
theorem cdt.empty_slot.vk (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS) (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt)
    {s0 s : S} {a : A} {x : U64} {cl : capability.Cap} (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s)
    (hx : x ∈ OS) (hcl : ClOK cl) (hk : L.ksb s = kb) :
    cdt.empty_slot st ar s a x cl ⦃ r => VsKeep st kb Pt s r.1 ⦄ := by
  obtain ⟨Ac', hb⟩ := h.1.parts
  have q := hb.1.choose_spec.choose_spec
  rcases hcl with rfl | ⟨irq, rfl, hi⟩
  · exact WP.spec_mono (cdt.empty_slot.os (P := fun _ => False) hO h.1.2 hx fun s1 a1 _ => by
      rw [pcd_null]; exact (WP.spec_ok _).2 (WritesIn.refl _ _)) fun r hr =>
      vsk_cw q hR (WritesIn.mono hr fun b hb => hb.elim id False.elim)
  · have hpcd : ∀ (s1 : S) (a1 : A), L.ksb s1 = L.ksb s →
        objects.post_cap_deletion st ar s1 a1 (.IrqHandler irq) ⦃ r => WritesIn st s1 r.1 (IrqStW kb irq) ⦄ :=
      fun s1 a1 k1 => WP.spec_mono (pcd_irq.wr hP s1 a1 irq hi) fun r ⟨o, ho, v, e⟩ => by
        rw [e]
        have al := ks_aligned (o := o) q (by omega) (by omega)
        rw [← k1] at al
        exact (writesIn_wr al).mono fun b eb => ⟨o, ho, by rw [eb, k1, hk]⟩
    exact WP.spec_mono (cdt.empty_slot.os hO h.1.2 hx hpcd) fun r hr => vsk_irq q hR hi hr

end vk

end ST
end R
end W7

end

end Fl4ProofsA64.P1
