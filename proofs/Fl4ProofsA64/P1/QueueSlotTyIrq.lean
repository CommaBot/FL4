/-
P1 (aarch64, gen 30): **the final IRQ handler kind over `SlotTy`** (`J` to `J`).

The exposed `cdt.delete` of a slot `x ∈ OS` holding `IrqHandler irq` (objects.rs `finalise_cap`, interrupt.rs
`deleting_irq_handler` / `deleted_irq_handler`; Funs.lean `objects.finalise_cap`, `interrupt.deleting_irq_handler`,
`cdt.delete_one`, `objects.post_cap_deletion`, `interrupt.set_irq_state`):

* not final: `finalise_cap` changes nothing, cleanup `Null` (`QueueSlotTyFin`'s `NonFinK`);
* final: `deleting_irq_handler` runs `cdt.delete_one` on the IRQ node slot `irqSlotA ks irq`
  (ks + 43232 + 32·irq), which finalises that slot's cap and empties it (`cdt.empty_slot … Null`, gen 29's
  `cdt.empty_slot.ty`); the cleanup is the `IrqHandler` cap, so `x`'s `empty_slot` ends in
  `deleted_irq_handler`, which writes the IRQ-state word `ks + 224 + 8·irq` (`set_irq_state … IRQ_INACTIVE`,
  `Cur0R.ks` for `Cur0R`) and touches the arch state only otherwise.

Hypotheses of the top `cdt.delete.irq` (case hypotheses and one placement fact of the ghost `OS`, no named
premise):
* `IslTriv`: the IRQ node slot is in `OS` and its cap's finalisation changes no store word (`FinTriv` and not an
  `IrqHandler` cap). On reachable states the IRQ node slot holds `Null` or the handler's notification cap
  (interrupt.rs `IRQHandler_SetNotification` installs a derived notification cap), so this covers a `Null` slot
  and a non-final notification cap; a final notification cap there is not covered.
* `IrqStApart OS kb`: the IRQ-state words `kb + 224 … kb + 43232` are in no `OS` slot. The IRQ-state table
  (layout.rs `ks::IRQ_STATE` = 224, 8 bytes per IRQ, 5376 IRQs) lies below the IRQ node (`ks::IRQ_NODE` =
  43232), and under QueueSlotTy's reading `OS`'s kernel-global slots are the IRQ node's: true on reachable
  states. It is a fact of the ghost set and the fixed `ks` base, not of a word class.

The IRQ bound `irq < 5376` comes from `SlotTy` (`A5.I.DelCapOK`). No existing statement changed.
-/
import Fl4ProofsA64.P1.QueueSlotTyFin
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

/-- **The IRQ-state words lie in no `OS` slot** (module docstring). -/
def IrqStApart (OS : Set U64) (kb : U64) : Prop :=
  ∀ o : U64, 224 ≤ o.val → o.val < 43232 → ∀ y ∈ OS, ¬ (y.val ≤ (wa kb o).val ∧ (wa kb o).val < y.val + 32)

/-- **The IRQ node slot's case**: in `OS`, its cap finalised without a store write, and no IrqHandler cap. -/
def IslTriv (st : machine.Store S) [L : LawfulStore st] (OS : Set U64) (isl : U64) (s : S) : Prop :=
  isl ∈ OS ∧ ∀ c fin, obj.Slot.cap st isl s = ok c → cdt.is_final_capability_with_cap st s isl c = ok fin →
    FinTriv st s c fin ∧ ∀ i, c ≠ .IrqHandler i

/-- One aligned write outside every `OS` slot keeps every `OS` word. -/
theorem OSKeep.wr1 {OS : Set U64} (hO : OSOK T Ω Sg OS) {s : S} {b v : U64} (hb : Aligned b)
    (hap : ∀ y ∈ OS, ¬ (y.val ≤ b.val ∧ b.val < y.val + 32)) : OSKeep st OS s (L.wr s b v) := fun y hy => by
  obtain ⟨v8, v16, v24⟩ := vals hO hy
  have := hap y hy
  exact ⟨L.mem_wr_ne hb (hO.al0 hy) (by omega), L.mem_wr_ne hb (hO.al hy (by simp) (by simp)) (by omega),
    L.mem_wr_ne hb (hO.al hy (by simp) (by simp)) (by omega), L.mem_wr_ne hb (hO.al hy (by simp) (by simp)) (by omega)⟩

set_option maxHeartbeats 2000000 in
/-- **`post_cap_deletion` of an `IrqHandler` cleanup** (`deleted_irq_handler`) keeps `J`. -/
theorem pcd_irq.ty {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {OS : Set U64} (hO : OSOK T Ω Sg OS)
    {s0 s : S} {a : A} {irq : U64} (h : J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 s) (hi : irq.val < 5376)
    (hap : IrqStApart OS (L.ksb s0)) :
    objects.post_cap_deletion st ar s a (.IrqHandler irq) ⦃ r => J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 r.1 ⦄ := by
  obtain ⟨Ac', hb⟩ := h.1.bxi
  have q := hb.1.choose_spec.choose_spec
  have hk : L.ksb s = L.ksb s0 := h.1.fr.1
  unfold objects.post_cap_deletion
  unfold interrupt.deleted_irq_handler
  refine WP.spec_bind (Pₘ := fun r : S × A => J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 r.1) ?_ ?_
  · unfold interrupt.set_irq_state interrupt.state_off
    simp only [lift, bind_ok]
    refine WP.spec_bind (Pₘ := fun o : U64 => o.val = 224 + 8 * irq.val) ?_ fun o ho => ?_
    · refine WP.spec_bind P0.Consts.layout.ks.IRQ_STATE.spec fun b eb => ?_
      subst eb
      refine (WP.spec_ok _).2 ?_
      simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]; omega
    have ho' : o.val < 223488 := by omega
    have h8 : o.val % 8 = 0 := by omega
    refine WP.spec_bind (WP.spec_and (Cur0R.ks (v := interrupt.IRQ_INACTIVE) h.1 ho' h8)
      (obj.ks_set.spec s o interrupt.IRQ_INACTIVE)) fun s1 h1 => ?_
    refine WP.spec_bind (hA.mask_irq a irq _) fun a1 _ => (WP.spec_ok _).2 ⟨h1.1, ?_⟩
    have e1 := h1.2
    subst e1
    refine h.2.keep (OSKeep.wr1 hO (ks_aligned q ho' h8) ?_)
    rw [hk]
    exact hap o (by omega) (by omega)
  · rintro ⟨s1, a1⟩ h1
    exact WP.spec_bind (hA.irq_free a1 irq) fun a2 _ => (WP.spec_ok _).2 h1

set_option maxHeartbeats 2000000 in
/-- `empty_slot` of a slot of `OS` with a cleanup whose `post_cap_deletion` keeps `J`, keeps `J`. -/
theorem cdt.empty_slot.tyC {A : Type _} {ar : machine.Arch A} {OS : Set U64} (hO : OSOK T Ω Sg OS)
    {s0 s : S} {a : A} {x : U64} {cl : capability.Cap} (h : J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 s) (hx : x ∈ OS)
    (hpcd : ∀ (s1 : S) (a1 : A), J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 s1 →
      objects.post_cap_deletion st ar s1 a1 cl ⦃ r => J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 r.1 ⦄) :
    cdt.empty_slot st ar s a x cl ⦃ r => J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.empty_slot
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st x s hS) fun c0 _ => ?_
  refine WP.spec_bind (P0.capability.Cap.is_null.p0 c0) fun bn _ => ?_
  split
  · exact (WP.spec_ok _).2 h
  have hxo := h.2 x hx
  obtain ⟨nx, hnx⟩ := DPF.spec_tot (P0.obj.sext48.p0 (L.mem s (wa x 24#u64)))
  have hnl : LinkOK OS nx := hxo.2.2 nx hnx
  have hni : obj.sext48 nx = ok nx := sx_idem _ _ hnx
  have hpv : LinkOK OS (L.mem s (wa x 16#u64)) := hxo.2.1
  rw [slot_prev_eq, bind_ok, slot_next_of hnx, bind_ok]
  refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st x s hS) fun fb _ => ?_
  simp only [obj.Slot.is_null, bind_ok]
  refine WP.spec_bind (Pₘ := fun s1 => J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 s1) ?_ fun s1 h1 => ?_
  · split
    · exact (WP.spec_ok _).2 h
    · rename_i hp0
      have hpO : L.mem s (wa x 16#u64) ∈ OS := hpv.resolve_left (by simpa using hp0)
      rw [set_next_eq, WP.spec_ok]
      exact J.next hO h hpO hnl hni
  refine WP.spec_bind (Pₘ := fun s2 => J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 s2) ?_ fun s2 h2 => ?_
  · split
    · exact (WP.spec_ok _).2 h1
    · rename_i hn0
      have hnO : nx ∈ OS := hnl.resolve_left (by simpa using hn0)
      rw [set_prev_eq, bind_ok]
      have h3 := J.prev hO h1 hnO hpv
      refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st nx _ hS) fun nfb _ => ?_
      split
      · rw [set_fb_eq_t, WP.spec_ok]; exact J.fb hO h3 hnO (Or.inr rfl)
      · cases fb
        · rw [set_fb_eq_f, WP.spec_ok]; exact J.fb hO h3 hnO (Or.inl rfl)
        · rw [set_fb_eq_t, WP.spec_ok]; exact J.fb hO h3 hnO (Or.inr rfl)
  rw [clear_eq, bind_ok]
  exact hpcd _ _ (J.clear hO h2 hx)

/-- For a cap other than an IrqHandler cap, `finalise_cap`'s pre-match does nothing. -/
theorem fc_eq_fco {A : Type _} (ar : machine.Arch A) (s : S) (a : A) {c : capability.Cap} (fin : Bool)
    (hc : ∀ i, c ≠ .IrqHandler i) :
    objects.finalise_cap st ar s a c fin false = objects.finalise_cap_object st ar s a c fin := by
  cases c
  case IrqHandler i => exact absurd rfl (hc i)
  all_goals first
    | rfl
    | (simp only [objects.finalise_cap, bind_ok]; done)
    | simp [objects.finalise_cap]

set_option maxHeartbeats 2000000 in
/-- **`delete_one` of an `IslTriv` slot** keeps `J`. -/
theorem cdt.delete_one.ty {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {OS : Set U64}
    (hO : OSOK T Ω Sg OS) {s0 s : S} {a : A} {isl : U64} (h : J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 s)
    (hk : IslTriv st OS isl s) :
    cdt.delete_one st ar s a isl ⦃ r => J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.delete_one
  refine WP.spec_bind (spec_eqv (P0.obj.Slot.cap.p0 st isl s hS)) fun c hc => ?_
  refine WP.spec_bind (P0.capability.Cap.is_null.p0 c) fun bn _ => ?_
  split
  · exact (WP.spec_ok _).2 h
  refine WP.spec_bind (spec_eqv (P0.cdt.is_final_capability_with_cap.p0 st s isl c hS)) fun fin hfin => ?_
  have hk' := hk.2 c fin hc.1 hfin.1
  rw [← fc_eq_fco ar s a fin hk'.2]
  refine WP.spec_bind (finalise_cap.fintriv hA s a hk'.1) ?_
  rintro ⟨rc, s2, a2⟩ ⟨-, e2⟩
  simp only at e2
  subst e2
  try dsimp only
  exact cdt.empty_slot.ty hO h hk.1

set_option maxHeartbeats 2000000 in
/-- **A final IrqHandler cap's `finalise_cap`**: the IRQ node slot's `delete_one`, then `(Null, IrqHandler irq)`. -/
theorem finalise_cap.irq_fin {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {OS : Set U64}
    (hO : OSOK T Ω Sg OS) {s0 s : S} {a : A} {irq : U64} (h : J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 s)
    (hk : IslTriv st OS (irqSlotA (L.ksb s) irq) s) :
    objects.finalise_cap st ar s a (.IrqHandler irq) true false ⦃ r =>
      J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 r.2.1 ∧ r.1 = (.Null, .IrqHandler irq) ⦄ := by
  unfold objects.finalise_cap
  simp only [↓reduceIte]
  unfold interrupt.deleting_irq_handler
  refine WP.spec_bind (Pₘ := fun r : S × A => J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 r.1) ?_ ?_
  · refine WP.spec_bind (interrupt.irq_slot.val s irq) fun isl e => ?_
    subst e
    exact cdt.delete_one.ty hA hO h hk
  · rintro ⟨s2, a2⟩ h2
    first
    | (simp only [objects.finalise_cap_object, ↓reduceIte, WP.spec_ok]; exact ⟨h2, rfl⟩)
    | (simp only [objects.finalise_cap_object, ↓reduceIte]; exact (WP.spec_ok _).2 ⟨h2, rfl⟩)
    | (simp [objects.finalise_cap_object, WP.spec_ok]; exact h2)

theorem irqH_nonfin (irq : U64) : NonFinK (.IrqHandler irq) := by
  unfold NonFinK
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨irq, rfl⟩)))))

set_option maxHeartbeats 4000000 in
/-- `finalise_slot_immediate` of an IrqHandler slot: `J`, a `Null` or `IrqHandler irq` cleanup. -/
theorem cdt.finalise_slot_immediate.irq {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {OS : Set U64}
    (hO : OSOK T Ω Sg OS) {s0 s : S} {a : A} {x irq : U64} (h : J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 s)
    (hc : obj.Slot.cap st x s = ok (.IrqHandler irq)) (hk : IslTriv st OS (irqSlotA (L.ksb s) irq) s) :
    cdt.finalise_slot_immediate st ar s a x ⦃ r => J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 r.2.1 ∧
      ∀ v, r.1 = .Ok v → v.cleanup = .Null ∨ v.cleanup = .IrqHandler irq ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.finalise_slot_immediate cdt.finalise_slot_immediate_loop
  apply loop.spec_decr_nat (measure := fun y => y.2.2.val) (inv := fun y => y.1 = s)
  · rintro ⟨s1, a1, fuel⟩ h1
    simp only at h1
    subst h1
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
    · refine WP.spec_bind (finalise_cap.irq_fin hA hO h hk) ?_
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
/-- **The exposed `cdt.delete` of an IrqHandler slot of `OS`** keeps `J` (`Cur0R` and `SlotTy`), final or not. -/
theorem cdt.delete.irq {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {OS : Set U64}
    (hO : OSOK T Ω Sg OS) {s0 s : S} {a : A} {x irq : U64} (h : J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 s)
    (hx : x ∈ OS) (hc : obj.Slot.cap st x s = ok (.IrqHandler irq))
    (hk : IslTriv st OS (irqSlotA (L.ksb s) irq) s) (hap : IrqStApart OS (L.ksb s0)) :
    cdt.delete st ar s a x true ⦃ r => J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 r.2.1 ⦄ := by
  have hd : capability.Cap.decode (L.mem s x) (L.mem s (wa x 8#u64)) = ok (.IrqHandler irq) := by
    rw [← DPF.slot_cap_dec]; exact hc
  have hi : irq.val < 5376 := ((h.2 x hx).1 _ hd).1.2.1 irq rfl
  unfold cdt.delete
  simp only [↓reduceIte]
  refine WP.spec_bind (cdt.finalise_slot_immediate.irq (ar := ar) (a := a) hA hO h hc hk) ?_
  rintro ⟨r, s1, a1⟩ ⟨h1, hv1⟩
  try simp only [uncurry_apply_pair] at h1 hv1 ⊢
  rcases r with v | e
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    rcases hv1 v rfl with e | e
    · rw [e]
      refine WP.spec_bind (cdt.empty_slot.ty hO h1 hx) ?_
      rintro ⟨s2, a2⟩ h2
      try simp only [uncurry_apply_pair] at h2 ⊢
      exact (WP.spec_ok _).2 h2
    · rw [e]
      refine WP.spec_bind (cdt.empty_slot.tyC hO h1 hx fun s3 a3 h3 => pcd_irq.ty hA hO h3 hi hap) ?_
      rintro ⟨s2, a2⟩ h2
      try simp only [uncurry_apply_pair] at h2 ⊢
      exact (WP.spec_ok _).2 h2
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 h1

end ST
end R
end W7

end

end Fl4ProofsA64.P1
