/-
P1 (aarch64, gen 33): **the IrqHandler kind over `JV`** (gen 30's QueueSlotTyIrq was at `J` only).

The deletion of an IrqHandler slot `x` (final or not, cdt.rs 271–318, interrupt.rs `deleting_irq_handler` /
`deleted_irq_handler`): a final cap first runs `delete_one` of the IRQ node slot (its cap finalised without a store
write, `IslTriv`, then `empty_slot`), the slot `x` is then emptied with the IrqHandler cleanup, whose
`post_cap_deletion` writes the IRQ-state word `ks + 224 + 8·irq` (`set_irq_state`) and masks / frees the IRQ (arch
only). Over `VcTy`:

* `VKeep.wr_ks`: a write of a kernel-global word `ks + o` (`o < 223488`, in `Ω`) in no `OS` slot keeps the `VcTy`
  words (`VcTy.ks`: no VCPU word is a kernel-global word; a TCB field is no word of `Ω`'s outside part; the buffer
  slots are `OS` slots);
* `pcd_irq.vk`, `cdt.empty_slot.vcC` (QueueVcTy's `cdt.empty_slot.vc` with a cleanup whose `post_cap_deletion`
  keeps the `VcTy` words), `cdt.delete_one.jv`, `finalise_cap.irq_finV`, `cdt.finalise_slot_immediate.irqV`;
* **`cdt.delete.irqV`** (`JV` to `JV`), **`cdt.delete.irqV_ent`** (from [J] `SlotTyEntV` at an `EntAt` decode
  start, after the restart, no apartness hypothesis left).

No new premise: `IrqStApart` is part of [J] `SlotTyEntV` (gen 30's `SlotTyEntI` field); no existing statement
changed.
-/
import Fl4ProofsA64.P1.QueueZombieV
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {P3Ok : S → Prop} {U : Set U64}

namespace W7
namespace R
namespace ST

local notation "wa" => core.num.U64.wrapping_add

section irqv
variable {OS Vc Ub : Set U64}

/-- **A kernel-global word written outside every `OS` slot keeps the `VcTy` words.** -/
theorem VKeep.wr_ks {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {s s1 : S}
    (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) (q : SchedQueuesInvX st T Cs Ω H X s Q R)
    (hv : VcTy st T Cs Ω H Sg Scs Z Vc Ub s) (k1 : L.ksb s1 = L.ksb s) {o v : U64} (ho : o.val < 223488)
    (h8 : o.val % 8 = 0) (hΩ : wa (L.ksb s) o ∈ Ω)
    (hap : ∀ y ∈ OS, ¬ (y.val ≤ (wa (L.ksb s) o).val ∧ (wa (L.ksb s) o).val < y.val + 32)) :
    VKeep st T Vc s1 (L.wr s1 (wa (L.ksb s1) o) v) := by
  rw [k1]
  have hb : Aligned (wa (L.ksb s) o) := ks_aligned q ho h8
  have hout := q.omega _ hΩ
  refine ⟨L.ksb_wr _ _ _, fun b' hb' => L.mem_wr_ne hb (hv.w hb').1
      (fun e => hv.ks b' hb' o ho (UScalar.eq_of_val_eq e)),
    fun t ht => L.mem_wr_ne hb (field_aligned (q.tcbs t ht) (by simp) (by simp))
      (fun e => out_ne_field (K := 3664#u64) hout ht (q.tcbs t ht) (by simp) e.symm),
    fun t ht => L.mem_wr_ne hb (field_aligned (q.tcbs t ht) (by simp) (by simp))
      (fun e => out_ne_field (K := 3672#u64) hout ht (q.tcbs t ht) (by simp) e.symm),
    fun t ht => Or.inl ?_⟩
  have hy := hV.bcov t ht
  obtain ⟨v8, -, -⟩ := vals hO hy
  have hn := hap _ hy
  rw [DPF.slot_cap_dec, DPF.slot_cap_dec, L.mem_wr_ne hb (hO.al0 hy) (fun e => hn ⟨by omega, by omega⟩),
    L.mem_wr_ne hb (hO.al hy (k := 8#u64) (by simp) (by simp)) (fun e => hn ⟨by omega, by omega⟩)]

set_option maxHeartbeats 2000000 in
/-- **`post_cap_deletion` of an `IrqHandler` cleanup keeps the `VcTy` words** (facts of the deletion's state `s`;
`s1` any state with the same `ks` base). -/
theorem pcd_irq.vk {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {X : Set U64}
    {Q : U64 → U64 → List U64} {R : U64 → List U64} (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub)
    {s s1 : S} {a : A} {irq : U64} (q : SchedQueuesInvX st T Cs Ω H X s Q R)
    (hksΩ : ∀ o : U64, o.val < 223488 → o.val % 8 = 0 → wa (L.ksb s) o ∈ Ω)
    (hv : VcTy st T Cs Ω H Sg Scs Z Vc Ub s) (hap : IrqStApart OS (L.ksb s)) (k1 : L.ksb s1 = L.ksb s)
    (hi : irq.val < 5376) :
    objects.post_cap_deletion st ar s1 a (.IrqHandler irq) ⦃ r => VKeep st T Vc s1 r.1 ⦄ := by
  unfold objects.post_cap_deletion
  unfold interrupt.deleted_irq_handler
  refine WP.spec_bind (Pₘ := fun r : S × A => VKeep st T Vc s1 r.1) ?_ ?_
  · unfold interrupt.set_irq_state interrupt.state_off
    simp only [lift, bind_ok]
    refine WP.spec_bind (Pₘ := fun o : U64 => o.val = 224 + 8 * irq.val) ?_ fun o ho => ?_
    · refine WP.spec_bind P0.Consts.layout.ks.IRQ_STATE.spec fun b eb => ?_
      subst eb
      refine (WP.spec_ok _).2 ?_
      simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]; omega
    have ho' : o.val < 223488 := by omega
    have h8 : o.val % 8 = 0 := by omega
    refine WP.spec_bind (obj.ks_set.spec s1 o interrupt.IRQ_INACTIVE) fun s2 e2 => ?_
    refine WP.spec_bind (hA.mask_irq a irq _) fun a1 _ => (WP.spec_ok _).2 ?_
    subst e2
    exact VKeep.wr_ks hO hV q hv k1 ho' h8 (hksΩ o ho' h8) (hap o (by omega) (by omega))
  · rintro ⟨s2, a2⟩ h2
    exact WP.spec_bind (hA.irq_free a2 irq) fun a3 _ => (WP.spec_ok _).2 h2

set_option maxHeartbeats 2000000 in
/-- **`empty_slot` of a slot of `OS` with a cleanup whose `post_cap_deletion` keeps the `VcTy` words keeps
`VcTy`** (QueueVcTy's `cdt.empty_slot.vc`, the cleanup step generalised). -/
theorem cdt.empty_slot.vcC {A : Type _} {ar : machine.Arch A} {X : Set U64} {Q : U64 → U64 → List U64}
    {R : U64 → List U64} (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) {s : S} {a : A} {x : U64}
    {cl : capability.Cap}
    (q : SchedQueuesInvX st T Cs Ω H X s Q R) (hT : SlotTy st T Ω Sg H Rp Nt OS s)
    (hv : VcTy st T Cs Ω H Sg Scs Z Vc Ub s) (hx : x ∈ OS)
    (hpcd : ∀ (s1 : S) (a1 : A), L.ksb s1 = L.ksb s →
      objects.post_cap_deletion st ar s1 a1 cl ⦃ r => VKeep st T Vc s1 r.1 ⦄) :
    cdt.empty_slot st ar s a x cl ⦃ r => VcTy st T Cs Ω H Sg Scs Z Vc Ub r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hal : ∀ b, VcW Vc b → Aligned b := fun b hb => (hv.w hb).1
  have W := fun {s1 : S} {p k v : U64} (hp : p ∈ OS) (hk : k.val < 32) (h8 : k.val % 8 = 0)
    (h0 : k.val = 0 → v = 0#u64) (h8' : k.val = 8 → L.mem s1 p = 0#u64) =>
    VKeep.wr_os (s := s1) (v := v) hO hV q hal hp hk h8 h0 h8'
  refine WP.spec_mono (?_ : cdt.empty_slot st ar s a x cl ⦃ r => VKeep st T Vc s r.1 ⦄) fun r hr => hv.keep hr
  unfold cdt.empty_slot
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st x s hS) fun c0 _ => ?_
  refine WP.spec_bind (P0.capability.Cap.is_null.p0 c0) fun bn _ => ?_
  split
  · exact (WP.spec_ok _).2 (VKeep.refl s)
  have hxo := hT x hx
  obtain ⟨nx, hnx⟩ := DPF.spec_tot (P0.obj.sext48.p0 (L.mem s (wa x 24#u64)))
  have hnl : LinkOK OS nx := hxo.2.2 nx hnx
  have hpv : LinkOK OS (L.mem s (wa x 16#u64)) := hxo.2.1
  rw [slot_prev_eq, bind_ok, slot_next_of hnx, bind_ok]
  refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st x s hS) fun fb _ => ?_
  simp only [obj.Slot.is_null, bind_ok]
  refine WP.spec_bind (Pₘ := fun s1 => VKeep st T Vc s s1) ?_ fun s1 h1 => ?_
  · split
    · exact (WP.spec_ok _).2 (VKeep.refl s)
    · rename_i hp0
      have hpO : L.mem s (wa x 16#u64) ∈ OS := hpv.resolve_left (by simpa using hp0)
      rw [set_next_eq, WP.spec_ok]
      exact W hpO (k := 24#u64) (by simp) (by simp) (by simp) (by simp)
  refine WP.spec_bind (Pₘ := fun s2 => VKeep st T Vc s s2) ?_ fun s2 h2 => ?_
  · split
    · exact (WP.spec_ok _).2 h1
    · rename_i hn0
      have hnO : nx ∈ OS := hnl.resolve_left (by simpa using hn0)
      rw [set_prev_eq, bind_ok]
      have h3 := h1.trans (W (s1 := s1) (v := L.mem s (wa x 16#u64)) hnO (k := 16#u64) (by simp) (by simp)
        (by simp) (by simp))
      refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st nx _ hS) fun nfb _ => ?_
      split
      · rw [set_fb_eq_t, WP.spec_ok]; exact h3.trans (W hnO (k := 24#u64) (by simp) (by simp) (by simp) (by simp))
      · cases fb
        · rw [set_fb_eq_f, WP.spec_ok]; exact h3.trans (W hnO (k := 24#u64) (by simp) (by simp) (by simp) (by simp))
        · rw [set_fb_eq_t, WP.spec_ok]; exact h3.trans (W hnO (k := 24#u64) (by simp) (by simp) (by simp) (by simp))
  rw [clear_eq, bind_ok]
  have a0 := hO.al0 hx
  have k0 := W (s1 := s2) (v := 0#u64) hx (k := 0#u64) (by simp) (by simp) (fun _ => rfl) (by simp)
  rw [SFF.wadd0'] at k0
  have k8 := W (s1 := L.wr s2 x 0#u64) (v := 0#u64) hx (k := 8#u64) (by simp) (by simp) (by simp)
    (fun _ => L.mem_wr_same a0)
  have k16 := W (s1 := L.wr (L.wr s2 x 0#u64) (wa x 8#u64) 0#u64) (v := 0#u64) hx (k := 16#u64) (by simp)
    (by simp) (by simp) (by simp)
  have k24 := W (s1 := L.wr (L.wr (L.wr s2 x 0#u64) (wa x 8#u64) 0#u64) (wa x 16#u64) 0#u64) (v := 0#u64) hx
    (k := 24#u64) (by simp) (by simp) (by simp) (by simp)
  have K := h2.trans (k0.trans (k8.trans (k16.trans k24)))
  exact WP.spec_mono (hpcd _ a K.ksb) fun r hr => K.trans hr

set_option maxHeartbeats 2000000 in
/-- **`delete_one` of an `IslTriv` slot keeps `JV`.** -/
theorem cdt.delete_one.jv {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S} {a : A} {isl : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hk : IslTriv st OS isl s) :
    cdt.delete_one st ar s a isl ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.1 ⦄ := by
  refine WP.spec_and (cdt.delete_one.ty hA hO h.1 hk) ?_
  have hS : P0.StoreTotal st := L.total
  obtain ⟨Ac', hb⟩ := h.1.parts
  unfold cdt.delete_one
  refine WP.spec_bind (spec_eqv (P0.obj.Slot.cap.p0 st isl s hS)) fun c hc => ?_
  refine WP.spec_bind (P0.capability.Cap.is_null.p0 c) fun bn _ => ?_
  split
  · exact (WP.spec_ok _).2 h.2
  refine WP.spec_bind (spec_eqv (P0.cdt.is_final_capability_with_cap.p0 st s isl c hS)) fun fin hfin => ?_
  have hk' := hk.2 c fin hc.1 hfin.1
  rw [← fc_eq_fco ar s a fin hk'.2]
  refine WP.spec_bind (finalise_cap.fintriv hA s a hk'.1) ?_
  rintro ⟨rc, s2, a2⟩ ⟨-, e2⟩
  simp only at e2
  subst e2
  try dsimp only
  exact cdt.empty_slot.vc hO hV hb.1.choose_spec.choose_spec h.1.2 h.2 hk.1

set_option maxHeartbeats 2000000 in
/-- **A final IrqHandler cap's `finalise_cap` over `JV`**: the IRQ node slot's `delete_one`, then
`(Null, IrqHandler irq)`. -/
theorem finalise_cap.irq_finV {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S} {a : A} {irq : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hk : IslTriv st OS (irqSlotA (L.ksb s) irq) s) :
    objects.finalise_cap st ar s a (.IrqHandler irq) true false ⦃ r =>
      JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧ r.1 = (.Null, .IrqHandler irq) ⦄ := by
  unfold objects.finalise_cap
  simp only [↓reduceIte]
  unfold interrupt.deleting_irq_handler
  refine WP.spec_bind (Pₘ := fun r : S × A => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.1) ?_ ?_
  · refine WP.spec_bind (interrupt.irq_slot.val s irq) fun isl e => ?_
    subst e
    exact cdt.delete_one.jv hA hO hV h hk
  · rintro ⟨s2, a2⟩ h2
    first
    | (simp only [objects.finalise_cap_object, ↓reduceIte, WP.spec_ok]; exact ⟨h2, rfl⟩)
    | (simp only [objects.finalise_cap_object, ↓reduceIte]; exact (WP.spec_ok _).2 ⟨h2, rfl⟩)
    | (simp [objects.finalise_cap_object, WP.spec_ok]; exact h2)

set_option maxHeartbeats 4000000 in
/-- `finalise_slot_immediate` of an IrqHandler slot over `JV`: a `Null` or `IrqHandler irq` cleanup. -/
theorem cdt.finalise_slot_immediate.irqV {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S} {a : A} {x irq : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s)
    (hc : obj.Slot.cap st x s = ok (.IrqHandler irq)) (hk : IslTriv st OS (irqSlotA (L.ksb s) irq) s) :
    cdt.finalise_slot_immediate st ar s a x ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      ∀ v, r.1 = .Ok v → v.cleanup = .Null ∨ v.cleanup = .IrqHandler irq ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.finalise_slot_immediate cdt.finalise_slot_immediate_loop
  apply loop.spec_decr_nat (measure := fun y => y.2.2.val) (inv := fun y => y.1 = s)
  · rintro ⟨s1, a1, fuel⟩ h1
    simp only at h1
    subst s1
    dsimp only
    unfold cdt.finalise_slot_immediate_loop.body
    split
    swap
    · exact (WP.spec_ok _).2 ⟨h, by intro v hv; simp_all⟩
    step as ⟨fuel1, hf1⟩
    rw [hc, bind_ok]
    refine WP.spec_bind (P0.capability.Cap.is_null.p0 _) fun bn _ => ?_
    split
    · exact (WP.spec_ok _).2 ⟨h, fun v hv => by cases hv; exact Or.inl rfl⟩
    refine WP.spec_bind (spec_eqv (P0.cdt.is_final_capability_with_cap.p0 st _ x _ hS)) fun fin hfin => ?_
    cases fin
    · rw [finalise_cap.nonfin ar _ a1 (irqH_nonfin irq), bind_ok]
      try dsimp only
      first
      | (simp only [cdt.cap_removable, bind_ok, ↓reduceIte]
         exact (WP.spec_ok _).2 ⟨h, fun v hv => by cases hv; exact Or.inl rfl⟩)
      | (simp only [cdt.cap_removable, bind_ok, ↓reduceIte, WP.spec_ok]
         exact ⟨h, fun v hv => by cases hv; exact Or.inl rfl⟩)
      | (simp [cdt.cap_removable, WP.spec_ok]; exact h)
    · refine WP.spec_bind (finalise_cap.irq_finV hA hO hV h hk) ?_
      rintro ⟨⟨rem, cl⟩, s2, a2⟩ ⟨h2, e⟩
      simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      try dsimp only
      first
      | (simp only [cdt.cap_removable, bind_ok, ↓reduceIte]
         exact (WP.spec_ok _).2 ⟨h2, fun v hv => by cases hv; exact Or.inr rfl⟩)
      | (simp only [cdt.cap_removable, bind_ok, ↓reduceIte, WP.spec_ok]
         exact ⟨h2, fun v hv => by cases hv; exact Or.inr rfl⟩)
      | (simp [cdt.cap_removable, WP.spec_ok]; exact h2)
  · rfl

set_option maxHeartbeats 2000000 in
/-- **The exposed `cdt.delete` of an IrqHandler slot of `OS` keeps `JV`** (final or not), under `IrqStApart`. -/
theorem cdt.delete.irqV {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S} {a : A} {x irq : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s)
    (hx : x ∈ OS) (hc : obj.Slot.cap st x s = ok (.IrqHandler irq))
    (hk : IslTriv st OS (irqSlotA (L.ksb s) irq) s) (hap : IrqStApart OS (L.ksb s0)) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ := by
  have hd : capability.Cap.decode (L.mem s x) (L.mem s (wa x 8#u64)) = ok (.IrqHandler irq) := by
    rw [← DPF.slot_cap_dec]; exact hc
  have hi : irq.val < 5376 := ((h.1.2 x hx).1 _ hd).1.2.1 irq rfl
  unfold cdt.delete
  simp only [↓reduceIte]
  refine WP.spec_bind (cdt.finalise_slot_immediate.irqV (ar := ar) (a := a) hA hO hV h hc hk) ?_
  rintro ⟨r, s1, a1⟩ ⟨h1, hv1⟩
  try simp only [uncurry_apply_pair] at h1 hv1 ⊢
  rcases r with v | e
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    rcases hv1 v rfl with e | e
    · rw [e]
      refine WP.spec_bind (cdt.empty_slot.jv hO hV h1 hx) ?_
      rintro ⟨s2, a2⟩ h2
      try simp only [uncurry_apply_pair] at h2 ⊢
      exact (WP.spec_ok _).2 h2
    · rw [e]
      obtain ⟨Ac', hb⟩ := h1.1.parts
      have q := hb.1.choose_spec.choose_spec
      obtain ⟨-, -, -, -, hSg⟩ := hb.blk
      have hk1 : L.ksb s1 = L.ksb s0 := h1.ksb
      refine WP.spec_bind (WP.spec_and (cdt.empty_slot.tyC hO h1.1 hx fun s3 a3 h3 => pcd_irq.ty hA hO h3 hi hap)
        (cdt.empty_slot.vcC hO hV q h1.1.2 h1.2 hx fun s3 a3 k3 =>
          pcd_irq.vk hA hO hV q (fun o h1' h2' => hSg.ksΩ o h1' h2') h1.2 (by rw [hk1]; exact hap) k3 hi)) ?_
      rintro ⟨s2, a2⟩ ⟨h2, v2⟩
      try simp only [uncurry_apply_pair] at h2 v2 ⊢
      exact (WP.spec_ok _).2 ⟨h2, v2⟩
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 h1

end irqv

/-- **The IrqHandler deletion over `JV` from the entry fact** ([J] `SlotTyEntV`): after the decode's restart, the
exposed `cdt.delete` of an IrqHandler slot of `OS` whose IRQ node slot is `IslTriv` keeps `JV`. -/
theorem cdt.delete.irqV_ent {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (hJ : SlotTyEntV st T Cs Ω Sg H Rp Scs Nt Z P3Ok) {s : S} (hE : EntAt st P3Ok s) {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) :
    ∃ OS Vc Ub, OSOK T Ω Sg OS ∧ SlotTy st T Ω Sg H Rp Nt OS s ∧ VcTy st T Cs Ω H Sg Scs Z Vc Ub s ∧
      sched.set_thread_state st s (L.curW s) sched.TS_RESTART ⦃ s1 =>
        JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s s1 ∧
        ∀ (a : A) (x irq : U64), x ∈ OS → obj.Slot.cap st x s1 = ok (.IrqHandler irq) →
          IslTriv st OS (irqSlotA (L.ksb s1) irq) s1 →
          cdt.delete st ar s1 a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s r.2.1 ⦄ ⦄ := by
  have q := D.bxi.1.choose_spec.choose_spec
  obtain ⟨OS, Vc, Ub, hO, hT, -, hap, -, hV, hv⟩ := hJ.entAt hE q.tcbs
  exact ⟨OS, Vc, Ub, hO, hT, hv, WP.spec_mono (JV.restart hO hV D hT hv) fun s1 h1 =>
    ⟨h1.1, fun a x irq hx hc hk => cdt.delete.irqV hA hO hV h1.1 hx hc hk hap⟩⟩

end ST
end R
end W7

end

end Fl4ProofsA64.P1
