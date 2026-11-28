/-
P1 (aarch64, gen 36): **the Zombie loop with SC and IrqHandler caps inside covered slots** (`ZS`), over `JV`,
extending gen 35's `ZT` loop (QueueZombieT).

* **SC caps** (a64.md §39, route (b)). `ZS` admits `SchedContext p b` with `p ∈ Scs`, `p ≠ 0` and `p ≠ Is`, where
  the ghost `Is` is the idle thread's `SC` field at the deletion's start. The loop keeps `L.mem s (scA I) = Is`
  (QueueScKeep: every step keeps that word or clears it, and `BoundInv.idle` — `scA (idle) ≠ 0` — holds again at
  every round's end state, so it is kept); at a round's state `TSc` turns "`scTcbA p = I`" into "`scA I = p`",
  hence `FinPl`'s SC clause (`scpl_of`) and QueueSlotTySc / QueueVcTy's `finJV_sc`.
* **IrqHandler caps.** A final IrqHandler cap's finalisation runs `delete_one` of its IRQ-node slot
  (interrupt.rs `deleting_irq_handler`, cdt.rs `delete_one`) and returns the cleanup `IrqHandler irq`, whose
  `post_cap_deletion` (`empty_slot`) writes the IRQ-state word `ks + 224 + 8·irq` (interrupt.rs
  `deleted_irq_handler`). The node slot's case is the state fact **`IrqN kb s`** (every IRQ-node slot holds a
  notification or `Null`), finalised by the notification finaliser (`finL`, `idlL`, `siL`) then `empty_slot`; the
  ghost-set hypothesis **`IrqOK OS D kb`**: the IRQ-node slots are slots of `OS` and none is in `D` (state-free: the
  IRQ node is kernel-global, `ks + 43232`, layout.rs `ks::IRQ_NODE`, never a CNode or TCB slot). The frame of a
  round on the `OS` caps is **`OKA`** (every `OS` slot keeps its cap, or is an IRQ-node slot now `Null`), on the
  loop **`OKD`** (the same for the `OS` slots outside `D`). Cleanups are **`ClOK`** (`Null` or
  `IrqHandler irq`, `irq < 5376`); `empty_slot` with such a cleanup: **`cdt.empty_slot.gw`** (the write set:
  `W7.CapW` words and the cleanup's words; other slots' caps kept; the slot `Null`), **`cdt.empty_slot.zs`**.
* `finXS`, **`cdt.cap_swap_for_delete.zs`**, **`cdt.finalise_slot_deferred.zs`**, **`cdt.delete_deferred.zs`**,
  **`cdt.finalise_slot_immediate.zs`** (invariant `JV ∧ DomS ∧ XS ∧ idle = I ∧ scA I = Is`, `OKD` from the start),
  **`cdt.delete.zs`**, instances **`cdt.delete.threadS`**, **`cnodeS`**, **`zombieS`**, **`cdt.delete.zs_ent`**
  ([J] `SlotTyEntZ`).

Hypotheses beyond gen 35's: `IrqStApart OS (ks)` (already a field of [J] `SlotTyEntV`), `IrqOK OS D (ks)` and
`¬ IslN (ks) x` (state-free, on the ghost sets and the deleted slot), `IrqN (ks) s` (a fact of the start state).
No named premise; no existing statement changed.
-/
import Fl4ProofsA64.P1.QueueScKeep
import Fl4ProofsA64.P1.QueueIrqV
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

section zs
variable {OS Vc Ub D : Set U64}

/-! ## IRQ-node slots, the cap frames, cleanups -/

/-- `y` is an IRQ-node slot. -/
def IslN (kb y : U64) : Prop := ∃ i : U64, i.val < 5376 ∧ y = irqSlotA kb i

/-- A notification or `Null`. -/
def IrqNt (c : capability.Cap) : Prop := (∃ n b0 b1 b2, c = .Notification n b0 b1 b2) ∨ c = .Null

/-- **Every IRQ-node slot holds a notification or `Null`.** -/
def IrqN (st : machine.Store S) [L : LawfulStore st] (kb : U64) (s : S) : Prop :=
  ∀ i : U64, i.val < 5376 → ∀ c, obj.Slot.cap st (irqSlotA kb i) s = ok c → IrqNt c

/-- **The IRQ-node slots are slots of `OS`, none in `D`** (state-free). -/
def IrqOK (OS D : Set U64) (kb : U64) : Prop :=
  (∀ i : U64, i.val < 5376 → irqSlotA kb i ∈ OS) ∧ ∀ y ∈ D, ¬ IslN kb y

/-- Every `OS` slot keeps its cap, or is an IRQ-node slot now `Null`. -/
def OKA (st : machine.Store S) [L : LawfulStore st] (OS : Set U64) (kb : U64) (s s' : S) : Prop :=
  ∀ y ∈ OS, obj.Slot.cap st y s' = obj.Slot.cap st y s ∨ (IslN kb y ∧ obj.Slot.cap st y s' = ok .Null)

/-- `OKA` for the `OS` slots outside `D`. -/
def OKD (st : machine.Store S) [L : LawfulStore st] (OS D : Set U64) (kb : U64) (s s' : S) : Prop :=
  ∀ y ∈ OS, y ∉ D → obj.Slot.cap st y s' = obj.Slot.cap st y s ∨ (IslN kb y ∧ obj.Slot.cap st y s' = ok .Null)

/-- A cleanup `Null` or `IrqHandler irq`. -/
def ClOK (c : capability.Cap) : Prop := c = .Null ∨ ∃ irq, c = .IrqHandler irq ∧ irq.val < 5376

theorem OKA.refl {kb : U64} (s : S) : OKA st OS kb s s := fun _ _ => Or.inl rfl
theorem OKD.refl {kb : U64} (s : S) : OKD st OS D kb s s := fun _ _ _ => Or.inl rfl

theorem OKA.of_osk {kb : U64} {s s' : S} (k : OSKeep st OS s s') : OKA st OS kb s s' :=
  fun _ hy => Or.inl (k.cap hy)

theorem OKA.okd {kb : U64} {s s' : S} (k : OKA st OS kb s s') : OKD st OS D kb s s' := fun y hy _ => k y hy

theorem OKD.trans {kb : U64} {s1 s2 s3 : S} (h1 : OKD st OS D kb s1 s2) (h2 : OKD st OS D kb s2 s3) :
    OKD st OS D kb s1 s3 := fun y hy hn => by
  rcases h2 y hy hn with e | e
  · rcases h1 y hy hn with e' | e'
    · exact Or.inl (e.trans e')
    · exact Or.inr ⟨e'.1, e.trans e'.2⟩
  · exact Or.inr e

theorem OKD.of_ck {kb x : U64} {s s' : S} (k : CapKeep st OS x s s') (hx : x ∈ D) : OKD st OS D kb s s' :=
  fun y hy hn => Or.inl (k.cap hy fun e => hn (e ▸ hx))

theorem IrqN.okd {kb : U64} {s s' : S} (hI : IrqOK OS D kb) (h : IrqN st kb s) (k : OKD st OS D kb s s') :
    IrqN st kb s' := fun i hi c hc => by
  have hO := hI.1 i hi
  have hnD : irqSlotA kb i ∉ D := fun hD => hI.2 _ hD ⟨i, hi, rfl⟩
  rcases k _ hO hnD with e | e
  · rw [e] at hc; exact h i hi c hc
  · rw [e.2] at hc; rw [← okinj hc]; exact Or.inr rfl

/-! ## The domain class with SC and IrqHandler caps -/

/-- **A domain cap with threads, VCPUs, SCs and IrqHandlers** (module docstring). -/
def ZS (Vc D Scs : Set U64) (I Is : U64) (c : capability.Cap) : Prop :=
  ZT Vc D I c ∨ (∃ p b, c = .SchedContext p b ∧ p ∈ Scs ∧ p ≠ 0#u64 ∧ p ≠ Is) ∨ (∃ irq, c = .IrqHandler irq)

def DomS (st : machine.Store S) [L : LawfulStore st] (Vc D Scs : Set U64) (I Is : U64) (s : S) : Prop :=
  ∀ y ∈ D, ∀ c, obj.Slot.cap st y s = ok c → ZS Vc D Scs I Is c

def XS (st : machine.Store S) [L : LawfulStore st] (Vc D Scs : Set U64) (I Is : U64) (x : U64) (s : S) : Prop :=
  ∀ c, obj.Slot.cap st x s = ok c → ZS Vc D Scs I Is c

theorem zs_nf {I Is : U64} {c : capability.Cap} (h : ZS Vc D Scs I Is c) : NoFrame c := by
  rcases h with h | ⟨_, _, rfl, -⟩ | ⟨_, rfl⟩
  · exact zt_nf h
  · intro p sz r d m e a v hc; cases hc
  · intro p sz r d m e a v hc; cases hc

theorem DomS.oka {I Is kb : U64} {s s' : S} (h : DomS st Vc D Scs I Is s) (hI : ∀ y ∈ D, ¬ IslN kb y)
    (hDO : D ⊆ OS) (k : OKA st OS kb s s') : DomS st Vc D Scs I Is s' := fun y hy c hc => by
  rcases k y (hDO hy) with e | e
  · rw [e] at hc; exact h y hy c hc
  · exact absurd e.1 (hI y hy)

theorem DomS.upd {I Is : U64} {s s' : S} (h : DomS st Vc D Scs I Is s)
    (hk : ∀ y ∈ D, obj.Slot.cap st y s' = obj.Slot.cap st y s ∨
      ∀ c, obj.Slot.cap st y s' = ok c → ZS Vc D Scs I Is c) :
    DomS st Vc D Scs I Is s' := fun y hy c hc => by
  rcases hk y hy with e | e
  · rw [e] at hc; exact h y hy c hc
  · exact e c hc

theorem XS.oka {I Is kb x : U64} {s s' : S} (h : XS st Vc D Scs I Is x s) (hx : x ∈ OS) (hxI : ¬ IslN kb x)
    (k : OKA st OS kb s s') : XS st Vc D Scs I Is x s' := fun c hc => by
  rcases k x hx with e | e
  · rw [e] at hc; exact h c hc
  · exact absurd e.1 hxI

theorem zs_null {I Is : U64} : ZS Vc D Scs I Is .Null := Or.inl (Or.inl (Or.inl zl_null))

/-- "Kept or cleared" plus `BoundInv.idle` at the end state: kept. -/
theorem sik_fix {s0 s s' : S} (h' : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s')
    (hi : L.idleW s' = L.idleW s) (k : SIK st (L.idleW s) s s') :
    L.mem s' (scA (L.idleW s)) = L.mem s (scA (L.idleW s)) := by
  rcases k with e | e
  · exact e
  · obtain ⟨Ac', hb⟩ := h'.1.parts
    have := hb.blk.2.1.idle
    rw [hi] at this
    exact absurd e this

/-! ## `empty_slot` with a cleanup -/

theorem lnkw (hO : OSOK T Ω Sg OS) {s s1 : S} {p k v x : U64} (hp : p ∈ OS) (hk : k.val = 16 ∨ k.val = 24)
    (h : WritesIn st s s1 (W7.CapW T Ω Sg) ∧ CapKeep st OS x s s1) :
    WritesIn st s (L.wr s1 (wa p k) v) (W7.CapW T Ω Sg) ∧ CapKeep st OS x s (L.wr s1 (wa p k) v) := by
  have k32 : k.val < 32 := by rcases hk with e | e <;> omega
  have k8 : k.val % 8 = 0 := by rcases hk with e | e <;> omega
  exact ⟨h.1.trans1 ((writesIn_wr (v := v) (hO.al hp k32 k8)).mono fun b e => by subst e; exact hO.cw hp k32 k8),
    h.2.trans (CapKeep.lnk hO hp hk)⟩

set_option maxHeartbeats 4000000 in
/-- **`empty_slot` of a slot `x` of `OS` with a cleanup whose `post_cap_deletion` writes `P` words off every `OS`
slot**: the writes are `W7.CapW` or `P` words, every other `OS` slot keeps its cap words, `x` reads `Null`. -/
theorem cdt.empty_slot.gw {A : Type _} {ar : machine.Arch A} (hO : OSOK T Ω Sg OS) {s : S} {a : A} {x : U64}
    {cl : capability.Cap} {P : U64 → Prop} (hT : SlotTy st T Ω Sg H Rp Nt OS s) (hx : x ∈ OS)
    (hpcd : ∀ (s1 : S) (a1 : A), L.ksb s1 = L.ksb s →
      objects.post_cap_deletion st ar s1 a1 cl ⦃ r => WritesIn st s1 r.1 P ⦄)
    (hPO : ∀ y ∈ OS, ∀ b, y.val ≤ b.val → b.val < y.val + 32 → ¬ P b) :
    cdt.empty_slot st ar s a x cl ⦃ r => WritesIn st s r.1 (fun b => W7.CapW T Ω Sg b ∨ P b) ∧
      CapKeep st OS x s r.1 ∧ obj.Slot.cap st x r.1 = ok .Null ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.empty_slot
  obtain ⟨c0, hc0⟩ := DPF.spec_tot (P0.obj.Slot.cap.p0 st x s hS)
  rw [hc0, bind_ok]
  obtain ⟨bn, hbn⟩ := DPF.spec_tot (P0.capability.Cap.is_null.p0 c0)
  rw [hbn, bind_ok]
  split
  · rename_i hb
    subst hb
    refine (WP.spec_ok _).2 ⟨WritesIn.refl _ _, CapKeep.refl x s, ?_⟩
    rw [hc0]
    cases c0 <;> simp_all [capability.Cap.is_null]
  have hxo := hT x hx
  obtain ⟨nx, hnx⟩ := DPF.spec_tot (P0.obj.sext48.p0 (L.mem s (wa x 24#u64)))
  have hnl : LinkOK OS nx := hxo.2.2 nx hnx
  have hpv : LinkOK OS (L.mem s (wa x 16#u64)) := hxo.2.1
  rw [slot_prev_eq, bind_ok, slot_next_of hnx, bind_ok]
  refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st x s hS) fun fb _ => ?_
  simp only [obj.Slot.is_null, bind_ok]
  refine WP.spec_bind (Pₘ := fun s1 => WritesIn st s s1 (W7.CapW T Ω Sg) ∧ CapKeep st OS x s s1) ?_
    fun s1 h1 => ?_
  · split
    · exact (WP.spec_ok _).2 ⟨WritesIn.refl _ _, CapKeep.refl x s⟩
    · rename_i hp0
      have hpO : L.mem s (wa x 16#u64) ∈ OS := hpv.resolve_left (by simpa using hp0)
      rw [set_next_eq, WP.spec_ok]
      exact lnkw hO hpO (k := 24#u64) (by simp) ⟨WritesIn.refl _ _, CapKeep.refl x s⟩
  refine WP.spec_bind (Pₘ := fun s2 => WritesIn st s s2 (W7.CapW T Ω Sg) ∧ CapKeep st OS x s s2) ?_
    fun s2 h2 => ?_
  · split
    · exact (WP.spec_ok _).2 h1
    · rename_i hn0
      have hnO : nx ∈ OS := hnl.resolve_left (by simpa using hn0)
      rw [set_prev_eq, bind_ok]
      have h3 := lnkw (v := L.mem s (wa x 16#u64)) hO hnO (k := 16#u64) (by simp) h1
      refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st nx _ hS) fun nfb _ => ?_
      split
      · rw [set_fb_eq_t, WP.spec_ok]; exact lnkw hO hnO (k := 24#u64) (by simp) h3
      · cases fb
        · rw [set_fb_eq_f, WP.spec_ok]; exact lnkw hO hnO (k := 24#u64) (by simp) h3
        · rw [set_fb_eq_t, WP.spec_ok]; exact lnkw hO hnO (k := 24#u64) (by simp) h3
  rw [clear_eq, bind_ok]
  have a0 := hO.al0 hx
  have a8 := hO.al hx (k := 8#u64) (by simp) (by simp)
  have a16 := hO.al hx (k := 16#u64) (by simp) (by simp)
  have a24 := hO.al hx (k := 24#u64) (by simp) (by simp)
  obtain ⟨v8, v16, v24⟩ := vals hO hx
  have c8 := hO.cw hx (k := 8#u64) (by simp) (by simp)
  have c16 := hO.cw hx (k := 16#u64) (by simp) (by simp)
  have c24 := hO.cw hx (k := 24#u64) (by simp) (by simp)
  have wc : WritesIn st s2 (L.wr (L.wr (L.wr (L.wr s2 x 0#u64) (wa x 8#u64) 0#u64) (wa x 16#u64) 0#u64)
      (wa x 24#u64) 0#u64) (W7.CapW T Ω Sg) :=
    ((((writesIn_wr a0).mono fun b e => by subst e; exact hO.cw0 hx).trans1
      ((writesIn_wr a8).mono fun b e => by subst e; exact c8)).trans1
      ((writesIn_wr a16).mono fun b e => by subst e; exact c16)).trans1
      ((writesIn_wr a24).mono fun b e => by subst e; exact c24)
  have ck4 : CapKeep st OS x s2 (L.wr (L.wr (L.wr (L.wr s2 x 0#u64) (wa x 8#u64) 0#u64) (wa x 16#u64) 0#u64)
      (wa x 24#u64) 0#u64) := fun y hy hne => by
    obtain ⟨d1, d2, -, -⟩ := other_keep (st := st)
      (s := L.wr (L.wr (L.wr s2 x 0#u64) (wa x 8#u64) 0#u64) (wa x 16#u64) 0#u64) (v := 0#u64) hO hx hy hne a24
      (by omega)
    obtain ⟨e1, e2, -, -⟩ := other_keep (st := st) (s := L.wr (L.wr s2 x 0#u64) (wa x 8#u64) 0#u64) (v := 0#u64)
      hO hx hy hne a16 (by omega)
    obtain ⟨f1, f2, -, -⟩ := other_keep (st := st) (s := L.wr s2 x 0#u64) (v := 0#u64) hO hx hy hne a8 (by omega)
    obtain ⟨g1, g2, -, -⟩ := other_keep (st := st) (s := s2) (v := 0#u64) hO hx hy hne a0 (by omega)
    exact ⟨d1.trans (e1.trans (f1.trans g1)), d2.trans (e2.trans (f2.trans g2))⟩
  have cx4 : obj.Slot.cap st x (L.wr (L.wr (L.wr (L.wr s2 x 0#u64) (wa x 8#u64) 0#u64) (wa x 16#u64) 0#u64)
      (wa x 24#u64) 0#u64) = ok .Null := by
    rw [DPF.slot_cap_dec]
    rw [L.mem_wr_ne a24 a0 (by omega), L.mem_wr_ne a16 a0 (by omega), L.mem_wr_ne a8 a0 (by omega),
      L.mem_wr_same a0, L.mem_wr_ne a24 a8 (by omega), L.mem_wr_ne a16 a8 (by omega), L.mem_wr_same a8,
      decode_zero]
  have hk4 : L.ksb (L.wr (L.wr (L.wr (L.wr s2 x 0#u64) (wa x 8#u64) 0#u64) (wa x 16#u64) 0#u64)
      (wa x 24#u64) 0#u64) = L.ksb s := by simp only [L.ksb_wr]; exact h2.1.1
  refine WP.spec_mono (hpcd _ a hk4) fun r hr => ⟨(h2.1.trans1 wc).trans hr, ?_, ?_⟩
  · refine (h2.2.trans ck4).trans fun y hy hne => ?_
    obtain ⟨w8, -, -⟩ := vals hO hy
    have hy0 := hO.al0 hy
    have hy8 := hO.al hy (k := 8#u64) (by simp) (by simp)
    exact ⟨hr.mem_eq hy0 (hPO y hy y le_rfl (by omega)), hr.mem_eq hy8 (hPO y hy _ (by omega) (by omega))⟩
  · rw [DPF.slot_cap_dec, hr.mem_eq a0 (hPO x hx x le_rfl (by omega)),
      hr.mem_eq a8 (hPO x hx _ (by omega) (by omega)), ← DPF.slot_cap_dec]
    exact cx4

/-- **`post_cap_deletion` of an `IrqHandler` cleanup writes one IRQ-state word.** -/
theorem pcd_irq.wr {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s1 : S) (a : A) (irq : U64)
    (hi : irq.val < 5376) :
    objects.post_cap_deletion st ar s1 a (.IrqHandler irq) ⦃ r => ∃ o : U64, o.val = 224 + 8 * irq.val ∧
      ∃ v, r.1 = L.wr s1 (wa (L.ksb s1) o) v ⦄ := by
  unfold objects.post_cap_deletion
  unfold interrupt.deleted_irq_handler
  refine WP.spec_bind (Pₘ := fun r : S × A => ∃ o : U64, o.val = 224 + 8 * irq.val ∧
    ∃ v, r.1 = L.wr s1 (wa (L.ksb s1) o) v) ?_ ?_
  · unfold interrupt.set_irq_state interrupt.state_off
    simp only [lift, bind_ok]
    refine WP.spec_bind (Pₘ := fun o : U64 => o.val = 224 + 8 * irq.val) ?_ fun o ho => ?_
    · refine WP.spec_bind P0.Consts.layout.ks.IRQ_STATE.spec fun b eb => ?_
      subst eb
      refine (WP.spec_ok _).2 ?_
      simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]; omega
    refine WP.spec_bind (obj.ks_set.spec s1 o interrupt.IRQ_INACTIVE) fun s2 e2 => ?_
    refine WP.spec_bind (hA.mask_irq a irq _) fun a1 _ => (WP.spec_ok _).2 ?_
    subst e2
    exact ⟨o, ho, _, rfl⟩
  · rintro ⟨s2, a2⟩ h2
    exact WP.spec_bind (hA.irq_free a2 irq) fun a3 _ => (WP.spec_ok _).2 h2

/-- The IRQ-state word of `irq` (interrupt.rs `state_off`: `ks + 224 + 8·irq`). -/
def IrqStW (kb irq b : U64) : Prop := ∃ o : U64, o.val = 224 + 8 * irq.val ∧ b = wa kb o

theorem JV.idleT {s0 s : S} (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) : L.idleW s ∈ T := by
  obtain ⟨Ac', hb⟩ := h.1.parts
  exact hb.1.choose_spec.choose_spec.idleT

set_option maxHeartbeats 4000000 in
/-- **`empty_slot` of a slot of `OS` with a `ClOK` cleanup**: `JV`, the other `OS` slots' caps kept, the slot
`Null`, the idle word and every thread's `SC` field kept. -/
theorem cdt.empty_slot.zs {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS)
    (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S} {a : A} {x : U64} {cl : capability.Cap}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hcl : ClOK cl)
    (hap : IrqStApart OS (L.ksb s0)) :
    cdt.empty_slot st ar s a x cl ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.1 ∧
      CapKeep st OS x s r.1 ∧ obj.Slot.cap st x r.1 = ok .Null ∧ L.idleW r.1 = L.idleW s ∧ ScK st T s r.1 ⦄ := by
  obtain ⟨Ac', hb⟩ := h.1.parts
  have q := hb.1.choose_spec.choose_spec
  obtain ⟨-, -, -, -, hSg⟩ := hb.blk
  have hN := q.nodes _ q.cur
  have hk : L.ksb s = L.ksb s0 := h.ksb
  rcases hcl with rfl | ⟨irq, rfl, hi⟩
  · refine WP.spec_mono (WP.spec_and (WP.spec_and (cdt.empty_slot.jv hO hV h hx) (cdt.empty_slot.ck hO h.1.2 hx))
      (cdt.empty_slot.cw hO h.1.2 hx)) ?_
    rintro r ⟨⟨h2, k2, c2⟩, w2⟩
    exact ⟨h2, k2, c2, JV.idle_cw h w2, JV.sik_cw h w2⟩
  have hpcd : ∀ (s1 : S) (a1 : A), L.ksb s1 = L.ksb s →
      objects.post_cap_deletion st ar s1 a1 (.IrqHandler irq) ⦃ r => WritesIn st s1 r.1 (IrqStW (L.ksb s) irq) ⦄ :=
    fun s1 a1 k1 => WP.spec_mono (pcd_irq.wr hP s1 a1 irq hi) fun r ⟨o, ho, v, e⟩ => by
      rw [e]
      have al := ks_aligned (o := o) q (by omega) (by omega)
      rw [← k1] at al
      exact (writesIn_wr al).mono fun b eb => ⟨o, ho, by rw [eb, k1]⟩
  have hPO : ∀ y ∈ OS, ∀ b, y.val ≤ b.val → b.val < y.val + 32 → ¬ IrqStW (L.ksb s) irq b :=
    fun y hy b h1 h2 ⟨o, ho, eb⟩ => hap o (by omega) (by omega) y hy
      ⟨by rw [← hk, ← eb]; exact h1, by rw [← hk, ← eb]; exact h2⟩
  have hPΩ : ∀ b, IrqStW (L.ksb s) irq b → b ∈ Ω := fun b ⟨o, ho, eb⟩ => by
    rw [eb]; exact hSg.ksΩ o (by omega) (by omega)
  refine WP.spec_mono (WP.spec_and (WP.spec_and
    (cdt.empty_slot.tyC hO h.1 hx fun s3 a3 h3 => pcd_irq.ty hP hO h3 hi hap)
    (cdt.empty_slot.vcC hO hV q h.1.2 h.2 hx fun s3 a3 k3 =>
      pcd_irq.vk hP hO hV q (fun o h1' h2' => hSg.ksΩ o h1' h2') h.2 (by rw [hk]; exact hap) k3 hi))
    (cdt.empty_slot.gw hO h.1.2 hx hpcd hPO)) ?_
  rintro r ⟨⟨h2, v2⟩, w2, k2, c2⟩
  refine ⟨⟨h2, v2⟩, k2, c2, ?_, ?_⟩
  · unfold LawfulStore.idleW
    rw [w2.2.1, nodeAt_of_ksb w2.1]
    refine w2.mem_eq (nodeAt_aligned hN (by rw [idle8]; omega) (by rw [idle8])) fun hb' => ?_
    rcases hb' with hc | hp
    · exact capw_ne_node q hc q.cur (o := layout.node.IDLE_THREAD) (by rw [idle8]; omega) rfl
    · exact out_ne_node (q.omega _ (hPΩ _ hp)) q.cur hN (by rw [idle8]; omega) rfl
  · exact ScK.of_w q.tcbs w2 fun z hz hb' => hb'.elim (fun hc => capw_ne_sc q hc hz rfl)
      (fun hp => (out_ne_field (q.omega _ (hPΩ _ hp)) hz (q.tcbs z hz) (K := 3464#u64) (by simp)) rfl)

set_option maxHeartbeats 4000000 in
/-- **`delete_one` of an IRQ-node slot holding a notification or `Null`**: `JV`, `OKA` (the slot becomes
`Null`), the idle word kept, the idle thread's `SC` field kept or cleared. -/
theorem cdt.delete_one.zs {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS)
    (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S} {a : A}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) {isl kb : U64} (hisl : isl ∈ OS)
    (hN : ∀ c, obj.Slot.cap st isl s = ok c → IrqNt c) (hI : IslN kb isl) :
    cdt.delete_one st ar s a isl ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.1 ∧
      OKA st OS kb s r.1 ∧ L.idleW r.1 = L.idleW s ∧ SIK st (L.idleW s) s r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hiT := h.idleT
  unfold cdt.delete_one
  obtain ⟨c, hc⟩ := DPF.spec_tot (P0.obj.Slot.cap.p0 st isl s hS)
  rw [hc, bind_ok]
  refine WP.spec_bind (P0.capability.Cap.is_null.p0 c) fun bn _ => ?_
  split
  · exact (WP.spec_ok _).2 ⟨h, OKA.refl s, rfl, Or.inl rfl⟩
  refine WP.spec_bind (P0.cdt.is_final_capability_with_cap.p0 st s isl c hS) fun fin _ => ?_
  have hl : ZL c := by
    rcases hN c hc with ⟨n, b0, b1, b2, rfl⟩ | rfl
    · exact Or.inr (Or.inr (Or.inl ⟨n, b0, b1, b2, rfl⟩))
    · exact zl_null
  have hnI : ∀ i, c ≠ .IrqHandler i := by
    rcases hN c hc with ⟨n, b0, b1, b2, rfl⟩ | rfl <;> intro i e <;> cases e
  rw [← fc_eq_fco ar s a fin hnI]
  refine WP.spec_bind (WP.spec_and (WP.spec_and (finL hP hO hA hV h hisl hc hl a fin) (idlL hP h hisl hc hl a fin))
    (siL hP h hisl hc hl a fin)) ?_
  rintro ⟨⟨rem, cl⟩, s2, a2⟩ ⟨⟨⟨e2, h2, k2⟩, i2⟩, j2⟩
  try simp only at e2 h2 k2 i2 j2
  try dsimp only
  refine WP.spec_mono (WP.spec_and (WP.spec_and (cdt.empty_slot.jv hO hV h2 hisl) (cdt.empty_slot.ck hO h2.1.2 hisl))
    (cdt.empty_slot.cw hO h2.1.2 hisl)) ?_
  rintro ⟨s3, a3⟩ ⟨⟨h3, ck3, c3⟩, w3⟩
  try simp only at h3 ck3 c3 w3 ⊢
  have K3 := JV.sik_cw h2 w3
  refine ⟨h3, fun y hy => ?_, (JV.idle_cw h2 w3).trans i2, ?_⟩
  · by_cases e : y = isl
    · subst e; exact Or.inr ⟨hI, c3⟩
    · exact Or.inl ((ck3.cap hy e).trans (k2.cap hy))
  · rcases j2 with e | e
    · exact Or.inl ((K3 _ hiT).trans e)
    · exact Or.inr ((K3 _ hiT).trans e)

set_option maxHeartbeats 2000000 in
/-- **A final IrqHandler cap's `finalise_cap`** whose IRQ-node slot holds a notification or `Null`. -/
theorem finalise_cap.irq_finZS {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS)
    (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S} {a : A}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) {irq kb : U64} (hi : irq.val < 5376)
    (hIO : irqSlotA kb irq ∈ OS) (hN : ∀ c, obj.Slot.cap st (irqSlotA kb irq) s = ok c → IrqNt c)
    (hk : L.ksb s = kb) :
    objects.finalise_cap st ar s a (.IrqHandler irq) true false ⦃ r => r.1 = (.Null, .IrqHandler irq) ∧
      JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧ OKA st OS kb s r.2.1 ∧ L.idleW r.2.1 = L.idleW s ∧
      SIK st (L.idleW s) s r.2.1 ⦄ := by
  unfold objects.finalise_cap
  simp only [↓reduceIte]
  unfold interrupt.deleting_irq_handler
  refine WP.spec_bind (Pₘ := fun r : S × A => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.1 ∧
    OKA st OS kb s r.1 ∧ L.idleW r.1 = L.idleW s ∧ SIK st (L.idleW s) s r.1) ?_ ?_
  · refine WP.spec_bind (interrupt.irq_slot.val s irq) fun isl e => ?_
    subst e
    rw [hk]
    exact cdt.delete_one.zs hP hO hA hV h hIO hN ⟨irq, hi, rfl⟩
  · rintro ⟨s2, a2⟩ h2
    first
    | (simp only [objects.finalise_cap_object, ↓reduceIte, WP.spec_ok]; exact ⟨rfl, h2⟩)
    | (simp only [objects.finalise_cap_object, ↓reduceIte]; exact (WP.spec_ok _).2 ⟨rfl, h2⟩)
    | (simp [objects.finalise_cap_object, WP.spec_ok]; exact h2)

set_option maxHeartbeats 4000000 in
/-- **The finalisation of a `ZS` cap** (at the round's idle word and idle `SC` field). -/
theorem finXS {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS)
    (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hIO : IrqOK OS D (L.ksb s0))
    (hN : IrqN st (L.ksb s0) s) {x : U64} (hx : x ∈ OS) {c : capability.Cap} (hc : obj.Slot.cap st x s = ok c)
    (hX : ZS Vc D Scs (L.idleW s) (L.mem s (scA (L.idleW s))) c) (a : A) (fin : Bool) :
    objects.finalise_cap st ar s a c fin false ⦃ r => ClOK r.1.2 ∧
      JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧ OKA st OS (L.ksb s0) s r.2.1 ∧ ZRem st D r.1.1 ∧
      L.idleW r.2.1 = L.idleW s ∧ L.mem r.2.1 (scA (L.idleW s)) = L.mem s (scA (L.idleW s)) ⦄ := by
  rcases hX with hz | ⟨p, b, rfl, hp, hp0, hpI⟩ | ⟨irq, rfl⟩
  · refine WP.spec_mono (WP.spec_and (finXT hP hO hA hV h hx hc hz a fin) (siZT hP hO hV h hx hc hz a fin)) ?_
    rintro r ⟨⟨e, h2, k2, z2, i2⟩, j2⟩
    exact ⟨Or.inl e, h2, OKA.of_osk k2, z2, i2, sik_fix h2 i2 j2⟩
  · have hk := scpl_of h hc hp hp0 hpI rfl
    refine WP.spec_mono (WP.spec_and (finJV_sc hP hO hA hV h hk a _ fin hc) (osk_sc hP hO hA h a fin hk hc)) ?_
    rintro r ⟨⟨e, h2⟩, k2, i2, j2⟩
    rw [e]
    exact ⟨Or.inl rfl, h2, OKA.of_osk k2, Or.inl rfl, i2, sik_fix h2 i2 j2⟩
  · have hty := (h.1.2 x hx).1 _ (by rw [DPF.slot_cap_dec] at hc; exact hc)
    have hi : irq.val < 5376 := hty.1.2.1 irq rfl
    cases fin
    · rw [finalise_cap.nonfin ar s a (irqH_nonfin irq), WP.spec_ok]
      exact ⟨Or.inl rfl, h, OKA.refl s, Or.inl rfl, rfl, rfl⟩
    · refine WP.spec_mono (finalise_cap.irq_finZS hP hO hA hV h hi (hIO.1 irq hi) (hN irq hi) h.ksb) ?_
      rintro r ⟨e, h2, k2, i2, j2⟩
      rw [e]
      exact ⟨Or.inr ⟨irq, rfl, hi⟩, h2, k2, Or.inl rfl, i2, sik_fix h2 i2 j2⟩

/-! ## The swap and the deferred round -/

set_option maxHeartbeats 4000000 in
/-- **`cap_swap_for_delete` of two distinct slots of a domain of `ZS` caps.** -/
theorem cdt.cap_swap_for_delete.zs (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS)
    (hDC : DCan D) {s0 s : S} {I Is kb : U64} (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s)
    (hD : DomS st Vc D Scs I Is s) {p y : U64} (hp : p ∈ D) (hy : y ∈ D) (hne : p ≠ y) :
    cdt.cap_swap_for_delete st s p y ⦃ s' => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s' ∧
      DomS st Vc D Scs I Is s' ∧ OKD st OS D kb s s' ∧ L.idleW s' = L.idleW s ∧ ScK st T s s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.cap_swap_for_delete
  simp only [obj.Slot.Insts.CoreCmpPartialEqSlot.eq, bind_ok]
  split
  · rename_i he; exfalso; apply hne; simpa using he
  obtain ⟨c1, hc1⟩ := DPF.spec_tot (P0.obj.Slot.cap.p0 st p s hS)
  obtain ⟨c2, hc2⟩ := DPF.spec_tot (P0.obj.Slot.cap.p0 st y s hS)
  rw [hc1, bind_ok, hc2, bind_ok]
  have z1 := hD p hp c1 hc1
  have z2 := hD y hy c2 hc2
  refine WP.spec_mono (cdt.swap.jvw hO hV h (hDO hp) (hDO hy) hne (hDC p hp) (hDC y hy) hc1 hc2 (zs_nf z1)
    (zs_nf z2)) ?_
  rintro s' ⟨⟨h', e1, e2, ek⟩, w⟩
  refine ⟨h', fun z hz c hc => ?_,
    fun z hz hzD => Or.inl (ek z hz (fun e => hzD (e ▸ hp)) (fun e => hzD (e ▸ hy))), JV.idle_cw h w, JV.sik_cw h w⟩
  by_cases e1' : z = p
  · subst e1'; rw [e1] at hc; rw [← okinj hc]; exact z2
  · by_cases e2' : z = y
    · subst e2'; rw [e2] at hc; rw [← okinj hc]; exact z1
    · rw [ek z (hDO hz) e1' e2'] at hc; exact hD z hz c hc

set_option maxHeartbeats 4000000 in
/-- **`finalise_slot_deferred` of a slot of a domain of `ZS` caps**: `JV`, `DomS`, `OKD`, the idle word and the
idle `SC` field kept, a `ClOK` cleanup. -/
theorem cdt.finalise_slot_deferred.zs {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) {a : A} {y I Is : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hy : y ∈ D) (hD : DomS st Vc D Scs I Is s)
    (hI : L.idleW s = I) (hIs : L.mem s (scA I) = Is) (hN : IrqN st (L.ksb s0) s) :
    cdt.finalise_slot_deferred st ar s a y ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      DomS st Vc D Scs I Is r.2.1 ∧ OKD st OS D (L.ksb s0) s r.2.1 ∧ L.idleW r.2.1 = I ∧
      L.mem r.2.1 (scA I) = Is ∧ ∀ v, r.1 = .Ok v → ClOK v.cleanup ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.finalise_slot_deferred cdt.finalise_slot_deferred_loop
  apply loop.spec_decr_nat (measure := fun z => z.2.2.val)
    (inv := fun z => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 z.1 ∧ DomS st Vc D Scs I Is z.1 ∧
      OKD st OS D (L.ksb s0) s z.1 ∧ L.idleW z.1 = I ∧ L.mem z.1 (scA I) = Is)
  · rintro ⟨s1, a1, fuel⟩ ⟨h1, d1, o1, i1, j1⟩
    simp only at h1 d1 o1 i1 j1
    dsimp only
    unfold cdt.finalise_slot_deferred_loop.body
    split
    swap
    · exact (WP.spec_ok _).2 ⟨h1, d1, o1, i1, j1, by intro v hv; simp_all⟩
    rename_i hf
    have hf' : 0 < fuel.val := by simpa using hf
    step as ⟨fuel1, hf1⟩
    obtain ⟨c, hc⟩ := DPF.spec_tot (P0.obj.Slot.cap.p0 st y s1 hS)
    rw [hc, bind_ok]
    refine WP.spec_bind (P0.capability.Cap.is_null.p0 c) fun bn _ => ?_
    split
    · exact (WP.spec_ok _).2 ⟨h1, d1, o1, i1, j1, fun v hv => by cases hv; exact Or.inl rfl⟩
    refine WP.spec_bind (P0.cdt.is_final_capability_with_cap.p0 st s1 y c hS) fun fin _ => ?_
    have hN1 : IrqN st (L.ksb s0) s1 := hN.okd hIO o1
    refine WP.spec_bind (finXS hP hO hA hV h1 hIO hN1 (hDO hy) hc (by rw [i1, j1]; exact d1 y hy c hc) a1 fin) ?_
    rintro ⟨⟨rem, cl⟩, s2, a2⟩ ⟨hcl, h2, k2, hrem, j2, sc2⟩
    simp only at hcl hrem j2 sc2
    have d2 : DomS st Vc D Scs I Is s2 := d1.oka hIO.2 hDO k2
    have o2 : OKD st OS D (L.ksb s0) s s2 := o1.trans k2.okd
    have i2 : L.idleW s2 = I := j2.trans i1
    have js2 : L.mem s2 (scA I) = Is := by rw [i1] at sc2; exact sc2.trans j1
    rcases hrem with rfl | ⟨p, t, n, rfl, hcp, hcov⟩
    · try dsimp only
      first
      | (simp only [cdt.cap_removable, bind_ok, ↓reduceIte]
         exact (WP.spec_ok _).2 ⟨h2, d2, o2, i2, js2, fun v hv => by cases hv; exact hcl⟩)
      | (simp only [cdt.cap_removable, bind_ok, ↓reduceIte, WP.spec_ok]
         exact ⟨h2, d2, o2, i2, js2, fun v hv => by cases hv; exact hcl⟩)
      | (simp [cdt.cap_removable, WP.spec_ok]; exact ⟨h2, d2, o2, i2, js2, hcl⟩)
    refine WP.spec_bind (spec_eqv (P0.cdt.cap_removable.p0 (.Zombie p t n) y)) fun b1 hb1 => ?_
    try dsimp only
    split
    · exact (WP.spec_ok _).2 ⟨h2, d2, o2, i2, js2, fun v hv => by cases hv; exact hcl⟩
    rename_i hnr
    have hn0 : n ≠ 0#u64 := by
      have hb := hb1.1
      rintro rfl
      simp [cdt.cap_removable] at hb
      simp_all
    have hnp : 0 < n.val := by
      rcases Nat.eq_zero_or_pos n.val with e | e
      · exact absurd (UScalar.eq_of_val_eq (by simpa using e)) hn0
      · exact e
    have hp0 : p ∈ D := by have := hcov 0#u64 (by simpa using hnp); rwa [slotIdx0] at this
    refine WP.spec_bind (WP.spec_and (JV.setz hO hV h2 (hDO hy) hcp ⟨hDO hp0, fun i hi => hDO (hcov i hi)⟩)
      (W7.obj.Slot.set_cap.capw (hO.slot _ (hDO hy)))) ?_
    rintro s3 ⟨⟨h3, k3, c3⟩, w3⟩
    have i3 : L.idleW s3 = I := (JV.idle_cw h2 w3).trans i2
    have js3 : L.mem s3 (scA I) = Is := ((JV.sik_cw h2 w3) I (i2 ▸ h2.idleT)).trans js2
    have d3 : DomS st Vc D Scs I Is s3 := DomS.upd d2 fun z hz => by
      by_cases e : z = y
      · right; subst e; intro c' hc'; rw [c3] at hc'; rw [← okinj hc']
        exact Or.inl (Or.inl (Or.inr (Or.inr ⟨p, _, _, rfl, hcov⟩)))
      · left; exact capk4 k3 (hDO hz) e
    have o3 : OKD st OS D (L.ksb s0) s s3 := o2.trans fun z hz hzD => Or.inl (capk4 k3 hz (fun e => hzD (e ▸ hy)))
    refine WP.spec_bind (spec_eqv (P0.cdt.cap_cyclic_zombie.p0 (.Zombie p (t) n) y)) fun b2 hb2 => ?_
    try dsimp only
    split
    · exact (WP.spec_ok _).2 ⟨h3, d3, o3, i3, js3, fun v hv => by cases hv; first | exact Or.inl rfl | exact hcl⟩
    rename_i hcy
    have hpy : p ≠ y := by
      intro e
      have hb := hb2.1
      subst e
      simp [cdt.cap_cyclic_zombie] at hb
      simp_all
    try dsimp only
    try simp only []
    refine WP.spec_bind (cdt.cap_swap_for_delete.zs (kb := L.ksb s0) hO hV hDO hDC h3 d3 hp0 hy hpy) ?_
    rintro s4 ⟨h4, d4, o4, j4, K4⟩
    refine WP.spec_bind (WP.spec_and (sched.preemption_point.jv hP hO hV h4 (by rw [h4.ksb]; exact hW))
      (sched.preemption_point.si hP h4)) ?_
    rintro ⟨rr, s5, a5⟩ ⟨⟨h5, k5, j5⟩, K5⟩
    try simp only [uncurry_apply_pair] at h5 k5 j5 K5 ⊢
    have i5 : L.idleW s5 = I := j5.trans (j4.trans i3)
    have hIT : I ∈ T := i3 ▸ h3.idleT
    have js5 : L.mem s5 (scA I) = Is := (K5 I hIT).trans ((K4 I hIT).trans js3)
    have d5 : DomS st Vc D Scs I Is s5 := DomS.oka d4 hIO.2 hDO (OKA.of_osk k5)
    have o5 : OKD st OS D (L.ksb s0) s s5 := (o3.trans o4).trans (OKA.of_osk k5).okd
    rcases rr with _ | ee
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok]
      refine (WP.spec_ok _).2 ⟨h5, d5, o5, i5, js5, ?_⟩
      show fuel1.val < fuel.val
      omega
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_tc_ok]
      exact (WP.spec_ok _).2 ⟨h5, d5, o5, i5, js5, fun v hv => by cases hv⟩
  · exact ⟨h, hD, OKD.refl s, hI, hIs⟩

set_option maxHeartbeats 4000000 in
/-- **`delete_deferred` of a slot of a domain of `ZS` caps.** -/
theorem cdt.delete_deferred.zs {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {y I Is : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hy : y ∈ D) (hD : DomS st Vc D Scs I Is s)
    (hI : L.idleW s = I) (hIs : L.mem s (scA I) = Is) (hN : IrqN st (L.ksb s0) s) :
    cdt.delete_deferred st ar s a y ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      DomS st Vc D Scs I Is r.2.1 ∧ OKD st OS D (L.ksb s0) s r.2.1 ∧ L.idleW r.2.1 = I ∧
      L.mem r.2.1 (scA I) = Is ⦄ := by
  unfold cdt.delete_deferred
  refine WP.spec_bind (cdt.finalise_slot_deferred.zs (a := a) hP hO hA hV hDO hDC hW hIO h hy hD hI hIs hN) ?_
  rintro ⟨r, s1, a1⟩ ⟨h1, d1, o1, i1, j1, hv1⟩
  try simp only [uncurry_apply_pair] at h1 d1 o1 i1 j1 hv1 ⊢
  rcases r with v | e
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    split
    · refine WP.spec_bind (cdt.empty_slot.zs (a := a1) hP hO hV h1 (hDO hy) (hv1 v rfl) hap) ?_
      rintro ⟨s2, a2⟩ ⟨h2, k2, c2, w2, K2⟩
      try simp only [uncurry_apply_pair] at h2 k2 c2 w2 K2 ⊢
      refine (WP.spec_ok _).2 ⟨h2, DomS.upd d1 fun z hz => ?_, o1.trans (OKD.of_ck k2 hy), w2.trans i1,
        (K2 I (i1 ▸ h1.idleT)).trans j1⟩
      by_cases e : z = y
      · right; subst e; intro c hc; rw [c2] at hc; rw [← okinj hc]; exact zs_null
      · left; exact k2.cap (hDO hz) e
    · exact (WP.spec_ok _).2 ⟨h1, d1, o1, i1, j1⟩
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 ⟨h1, d1, o1, i1, j1⟩

/-! ## The immediate loop -/

theorem IrqN.oka {kb : U64} {s s' : S} (hIO : IrqOK OS D kb) (h : IrqN st kb s) (k : OKA st OS kb s s') :
    IrqN st kb s' := fun i hi c hc => by
  rcases k _ (hIO.1 i hi) with e | e
  · rw [e] at hc; exact h i hi c hc
  · rw [e.2] at hc; rw [← okinj hc]; exact Or.inr rfl

theorem IrqN.ck {kb x : U64} {s s' : S} (hIO : IrqOK OS D kb) (h : IrqN st kb s) (hxI : ¬ IslN kb x)
    (k : ∀ y ∈ OS, y ≠ x → obj.Slot.cap st y s' = obj.Slot.cap st y s) : IrqN st kb s' := fun i hi c hc => by
  rw [k _ (hIO.1 i hi) (fun e => hxI ⟨i, hi, e.symm⟩)] at hc
  exact h i hi c hc

set_option hygiene false in
/-- The preemption-point tail of an immediate round. -/
local macro "ztailS" : tactic => `(tactic| (
  refine WP.spec_bind (WP.spec_and (sched.preemption_point.jv hP hO hV h5 (by rw [h5.ksb]; exact hW))
    (sched.preemption_point.si hP h5)) ?_
  rintro ⟨rr, s6, a6⟩ ⟨⟨h6, k6, i6⟩, K6⟩
  try simp only [uncurry_apply_pair] at h6 k6 i6 K6 ⊢
  rcases rr with _ | ee
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok]
    refine (WP.spec_ok _).2 ⟨h6, DomS.oka d5 hIO.2 hDO (OKA.of_osk k6), XS.oka x5 hx hxI (OKA.of_osk k6),
      i6.trans j5, (K6 I (j5 ▸ h5.idleT)).trans js5, IrqN.oka hIO N5 (OKA.of_osk k6), ?_⟩
    show fuel1.val < fuel.val
    omega
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 ⟨h6, fun v hv => by cases hv⟩))

set_option maxHeartbeats 4000000 in
/-- **`finalise_slot_immediate` of a slot of `OS` whose cap is `ZS` over a domain `D` of `ZS` caps**: `JV` to
`JV`, a `ClOK` cleanup. -/
theorem cdt.finalise_slot_immediate.zs {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x I Is : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomS st Vc D Scs I Is s) (hX : XS st Vc D Scs I Is x s) (hI : L.idleW s = I)
    (hIs : L.mem s (scA I) = Is) (hN : IrqN st (L.ksb s0) s) :
    cdt.finalise_slot_immediate st ar s a x ⦃ r =>
      JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧ ∀ v, r.1 = .Ok v → ClOK v.cleanup ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.finalise_slot_immediate cdt.finalise_slot_immediate_loop
  apply loop.spec_decr_nat (measure := fun y => y.2.2.val)
    (inv := fun y => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 y.1 ∧ DomS st Vc D Scs I Is y.1 ∧
      XS st Vc D Scs I Is x y.1 ∧ L.idleW y.1 = I ∧ L.mem y.1 (scA I) = Is ∧ IrqN st (L.ksb s0) y.1)
  · rintro ⟨s1, a1, fuel⟩ ⟨h1, d1, x1, j1, js1, N1⟩
    simp only at h1 d1 x1 j1 js1 N1
    dsimp only
    unfold cdt.finalise_slot_immediate_loop.body
    split
    swap
    · exact (WP.spec_ok _).2 ⟨h1, by intro v hv; simp_all⟩
    rename_i hf
    have hf' : 0 < fuel.val := by simpa using hf
    step as ⟨fuel1, hf1⟩
    obtain ⟨c, hc⟩ := DPF.spec_tot (P0.obj.Slot.cap.p0 st x s1 hS)
    rw [hc, bind_ok]
    refine WP.spec_bind (P0.capability.Cap.is_null.p0 c) fun bn _ => ?_
    split
    · exact (WP.spec_ok _).2 ⟨h1, fun v hv => by cases hv; exact Or.inl rfl⟩
    refine WP.spec_bind (P0.cdt.is_final_capability_with_cap.p0 st s1 x c hS) fun fin _ => ?_
    refine WP.spec_bind (finXS hP hO hA hV h1 hIO N1 hx hc (by rw [j1, js1]; exact x1 c hc) a1 fin) ?_
    rintro ⟨⟨rem, cl⟩, s2, a2⟩ ⟨hcl, h2, k2, hrem, j2', sc2⟩
    simp only at hcl hrem j2' sc2
    have d2 : DomS st Vc D Scs I Is s2 := d1.oka hIO.2 hDO k2
    have j2 : L.idleW s2 = I := j2'.trans j1
    have js2 : L.mem s2 (scA I) = Is := by rw [j1] at sc2; exact sc2.trans js1
    have N2 : IrqN st (L.ksb s0) s2 := N1.oka hIO k2
    rcases hrem with rfl | ⟨p, t, n, rfl, hcp, hcov⟩
    · try dsimp only
      first
      | (simp only [cdt.cap_removable, bind_ok, ↓reduceIte]
         exact (WP.spec_ok _).2 ⟨h2, fun v hv => by cases hv; exact hcl⟩)
      | (simp only [cdt.cap_removable, bind_ok, ↓reduceIte, WP.spec_ok]; exact ⟨h2, fun v hv => by cases hv; exact hcl⟩)
      | (simp [cdt.cap_removable, WP.spec_ok]; exact ⟨h2, hcl⟩)
    refine WP.spec_bind (spec_eqv (P0.cdt.cap_removable.p0 (.Zombie p t n) x)) fun b1 hb1 => ?_
    try dsimp only
    split
    · exact (WP.spec_ok _).2 ⟨h2, fun v hv => by cases hv; exact hcl⟩
    rename_i hnr
    have hn0 : n ≠ 0#u64 := by
      have hb := hb1.1
      rintro rfl
      simp [cdt.cap_removable] at hb
      simp_all
    have hnp : 0 < n.val := by
      rcases Nat.eq_zero_or_pos n.val with e | e
      · exact absurd (UScalar.eq_of_val_eq (by simpa using e)) hn0
      · exact e
    have hp0 : p ∈ D := by have := hcov 0#u64 (by simpa using hnp); rwa [slotIdx0] at this
    refine WP.spec_bind (WP.spec_and (JV.setz hO hV h2 hx hcp ⟨hDO hp0, fun i hi => hDO (hcov i hi)⟩)
      (W7.obj.Slot.set_cap.capw (hO.slot _ hx))) ?_
    rintro s3 ⟨⟨h3, k3, c3⟩, w3⟩
    have j3 : L.idleW s3 = I := (JV.idle_cw h2 w3).trans j2
    have hIT : I ∈ T := j2 ▸ h2.idleT
    have js3 : L.mem s3 (scA I) = Is := ((JV.sik_cw h2 w3) I hIT).trans js2
    have N3 : IrqN st (L.ksb s0) s3 := N2.ck hIO hxI fun y hy e => capk4 k3 hy e
    have d3 : DomS st Vc D Scs I Is s3 := DomS.upd d2 fun z hz => by
      by_cases e : z = x
      · right; subst e; intro c' hc'; rw [c3] at hc'; rw [← okinj hc']
        exact Or.inl (Or.inl (Or.inr (Or.inr ⟨p, _, _, rfl, hcov⟩)))
      · left; exact capk4 k3 (hDO hz) e
    try dsimp only
    first
      | (refine WP.spec_bind (Pₘ := fun i => i = core.num.U64.wrapping_sub n 1#u64) ((WP.spec_ok _).2 rfl)
          fun i hi => ?_; subst hi)
      | simp only [lift, bind_ok]
    refine WP.spec_bind (slot_index_in p _) fun e he => ?_
    subst he
    have heD : slotIdx p (core.num.U64.wrapping_sub n 1#u64) ∈ D := hcov _ (by rw [wsub1 hn0]; omega)
    refine WP.spec_bind (cdt.delete_deferred.zs (a := a2) hP hO hA hV hDO hDC hW hIO hap h3 heD d3 j3 js3 N3) ?_
    rintro ⟨r4, s4, a4⟩ ⟨h4, d4, o4, j4, js4⟩
    try simp only [uncurry_apply_pair] at h4 d4 o4 j4 js4 ⊢
    have N4 : IrqN st (L.ksb s0) s4 := N3.okd hIO o4
    have xo4 : XS st Vc D Scs I Is x s4 := fun c' hc' => by
      by_cases hxD : x ∈ D
      · exact d4 x hxD c' hc'
      · rcases o4 x hx hxD with e | e
        · rw [e, c3] at hc'
          rw [← okinj hc']
          exact Or.inl (Or.inl (Or.inr (Or.inr ⟨p, _, _, rfl, hcov⟩)))
        · exact absurd e.1 hxI
    rcases r4 with _ | ee
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      obtain ⟨c4, hc4⟩ := DPF.spec_tot (P0.obj.Slot.cap.p0 st x s4 hS)
      rw [hc4, bind_ok]
      try dsimp only
      refine WP.spec_bind (Pₘ := fun y : S × A => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 y.1 ∧
        DomS st Vc D Scs I Is y.1 ∧ XS st Vc D Scs I Is x y.1 ∧ L.idleW y.1 = I ∧ L.mem y.1 (scA I) = Is ∧
        IrqN st (L.ksb s0) y.1) ?_ ?_
      · split
        all_goals first
          | exact (WP.spec_ok _).2 ⟨h4, d4, xo4, j4, js4, N4⟩
          | skip
        split
        · split
          · refine WP.spec_bind (Pₘ := fun s5 => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s5 ∧
              DomS st Vc D Scs I Is s5 ∧ XS st Vc D Scs I Is x s5 ∧ L.idleW s5 = I ∧ L.mem s5 (scA I) = Is ∧
              IrqN st (L.ksb s0) s5) ?_ fun s5 h5 => (WP.spec_ok _).2 h5
            split
            · try simp only [lift, bind_ok]
              refine WP.spec_mono (WP.spec_and (JV.setz hO hV h4 hx hcp ⟨hDO hp0, fun i hi => hDO (hcov i (by
                rw [wsub1 hn0] at hi; omega))⟩) (W7.obj.Slot.set_cap.capw (hO.slot _ hx))) ?_
              rintro s5 ⟨⟨h5, k5, c5⟩, w5⟩
              refine ⟨h5, DomS.upd d4 fun z hz => ?_, fun c' hc' => ?_, (JV.idle_cw h4 w5).trans j4,
                ((JV.sik_cw h4 w5) I (j4 ▸ h4.idleT)).trans js4, N4.ck hIO hxI fun y hy e => capk4 k5 hy e⟩
              · by_cases e : z = x
                · right; subst e; intro c' hc'; rw [c5] at hc'; rw [← okinj hc']
                  exact Or.inl (Or.inl (Or.inr (Or.inr ⟨p, _, _, rfl, fun i hi => hcov i (by
                    rw [wsub1 hn0] at hi; omega)⟩)))
                · left; exact capk4 k5 (hDO hz) e
              · rw [c5] at hc'; rw [← okinj hc']
                exact Or.inl (Or.inl (Or.inr (Or.inr ⟨p, _, _, rfl, fun i hi => hcov i (by
                  rw [wsub1 hn0] at hi; omega)⟩)))
            · exact (WP.spec_ok _).2 ⟨h4, d4, xo4, j4, js4, N4⟩
          · exact (WP.spec_ok _).2 ⟨h4, d4, xo4, j4, js4, N4⟩
        · exact (WP.spec_ok _).2 ⟨h4, d4, xo4, j4, js4, N4⟩
      rintro ⟨s5, a5⟩ ⟨h5, d5, x5, j5, js5, N5⟩
      try simp only [uncurry_apply_pair] at h5 d5 x5 j5 js5 N5 ⊢
      try dsimp only
      ztailS
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_tc_ok]
      exact (WP.spec_ok _).2 ⟨h4, fun v hv => by cases hv⟩
  · exact ⟨h, hD, hX, hI, hIs, hN⟩

/-! ## The exposed deletion -/

set_option maxHeartbeats 4000000 in
/-- **The exposed `cdt.delete` of a slot of `OS` whose cap is `ZS` over a domain of `ZS` caps keeps `JV`** (ghost
`I`, `Is`: the start state's idle word and idle `SC` field). -/
theorem cdt.delete.zsI {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x I Is : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomS st Vc D Scs I Is s) (hX : XS st Vc D Scs I Is x s) (hI : L.idleW s = I)
    (hIs : L.mem s (scA I) = Is) (hN : IrqN st (L.ksb s0) s) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ := by
  unfold cdt.delete
  simp only [↓reduceIte]
  refine WP.spec_bind (cdt.finalise_slot_immediate.zs (a := a) hP hO hA hV hDO hDC hW hIO hap h hx hxI hD hX hI
    hIs hN) ?_
  rintro ⟨r, s1, a1⟩ ⟨h1, hv1⟩
  try simp only [uncurry_apply_pair] at h1 hv1 ⊢
  rcases r with v | e
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    refine WP.spec_bind (cdt.empty_slot.zs hP hO hV h1 hx (hv1 v rfl) hap) ?_
    rintro ⟨s2, a2⟩ h2
    try simp only [uncurry_apply_pair] at h2 ⊢
    exact (WP.spec_ok _).2 h2.1
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 h1

/-- **`cdt.delete.zsI` at the start state's idle word and idle `SC` field.** -/
theorem cdt.delete.zs {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomS st Vc D Scs (L.idleW s) (L.mem s (scA (L.idleW s))) s)
    (hX : XS st Vc D Scs (L.idleW s) (L.mem s (scA (L.idleW s))) x s) (hN : IrqN st (L.ksb s0) s) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ :=
  cdt.delete.zsI hP hO hA hV hDO hDC hW hIO hap h hx hxI hD hX rfl rfl hN

/-- **The thread kind over a domain of `ZS` caps**: the exposed `cdt.delete` of `Thread p` (`p` not the idle
thread, its seven TCB slots in `D`), the slots of `D` holding leaf, CNode, Zombie, non-idle thread, VCPU, SC (not
the idle thread's SC) and IrqHandler caps, keeps `JV`. -/
theorem cdt.delete.threadS {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x p : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomS st Vc D Scs (L.idleW s) (L.mem s (scA (L.idleW s))) s) (hN : IrqN st (L.ksb s0) s)
    (hc : obj.Slot.cap st x s = ok (.Thread p)) (hid : p ≠ L.idleW s)
    (hcov : ∀ i : U64, i.val < 7 → slotIdx p i ∈ D) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ :=
  cdt.delete.zs hP hO hA hV hDO hDC hW hIO hap h hx hxI hD (fun c hc' => by
    rw [hc] at hc'; rw [← okinj hc']; exact Or.inl (Or.inr (Or.inl ⟨p, rfl, hid, hcov⟩))) hN

/-- **The CNode kind over a domain of `ZS` caps.** -/
theorem cdt.delete.cnodeS {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x p r g b : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomS st Vc D Scs (L.idleW s) (L.mem s (scA (L.idleW s))) s) (hN : IrqN st (L.ksb s0) s)
    (hc : obj.Slot.cap st x s = ok (.CNode p r g b))
    (hcov : ∀ i : U64, i.val < 2 ^ (r.val % 64) → slotIdx p i ∈ D) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ :=
  cdt.delete.zs hP hO hA hV hDO hDC hW hIO hap h hx hxI hD (fun c hc' => by
    rw [hc] at hc'; rw [← okinj hc']; exact Or.inl (Or.inl (Or.inr (Or.inl ⟨p, r, g, b, rfl, hcov⟩)))) hN

/-- **The Zombie kind over a domain of `ZS` caps.** -/
theorem cdt.delete.zombieS {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x p t n : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomS st Vc D Scs (L.idleW s) (L.mem s (scA (L.idleW s))) s) (hN : IrqN st (L.ksb s0) s)
    (hc : obj.Slot.cap st x s = ok (.Zombie p t n)) (hcov : ∀ i : U64, i.val < n.val → slotIdx p i ∈ D) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ :=
  cdt.delete.zs hP hO hA hV hDO hDC hW hIO hap h hx hxI hD (fun c hc' => by
    rw [hc] at hc'; rw [← okinj hc']; exact Or.inl (Or.inl (Or.inr (Or.inr ⟨p, t, n, rfl, hcov⟩)))) hN


end zs

/-! ## On the entry fact -/

/-- **The `ZS` loop from the entry fact**: at an `EntAt` decode start, under [J] `SlotTyEntZ` (whose fields give
`ScApart`, `WuApart` and `IrqStApart`), the restart starts `JV`, and from every state it reaches the exposed
`cdt.delete` of a slot of `OS` (no IRQ-node slot) whose cap is `ZS` over a canonical domain `D ⊆ OS` of `ZS` caps
(no IRQ-node slot in `D`, the IRQ-node slots in `OS`, each holding a notification or `Null`) keeps `JV`. -/
theorem cdt.delete.zs_ent {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hJ : SlotTyEntZ st T Cs Ω Sg H Rp Scs Nt Z P3Ok) {s : S} (hE : EntAt st P3Ok s) {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) :
    ∃ OS Vc Ub, OSOK T Ω Sg OS ∧ SlotTy st T Ω Sg H Rp Nt OS s ∧ VcTy st T Cs Ω H Sg Scs Z Vc Ub s ∧
      sched.set_thread_state st s (L.curW s) sched.TS_RESTART ⦃ s1 =>
        JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s s1 ∧
        ∀ (a : A) (x : U64) (Dm : Set U64), Dm ⊆ OS → DCan Dm → IrqOK OS Dm (L.ksb s) → x ∈ OS →
          ¬ IslN (L.ksb s) x → DomS st Vc Dm Scs (L.idleW s1) (L.mem s1 (scA (L.idleW s1))) s1 →
          XS st Vc Dm Scs (L.idleW s1) (L.mem s1 (scA (L.idleW s1))) x s1 → IrqN st (L.ksb s) s1 →
          cdt.delete st ar s1 a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s r.2.1 ⦄ ⦄ := by
  have q := D.bxi.1.choose_spec.choose_spec
  obtain ⟨OS, Vc, Ub, hO, hT, -, hap, hsc, hV, hv, hwu⟩ := hJ.entAt hE q.tcbs
  exact ⟨OS, Vc, Ub, hO, hT, hv, WP.spec_mono (JV.restart hO hV D hT hv) fun s1 h1 =>
    ⟨h1.1, fun a x Dm hDO hDC hIO hx hxI hD hX hN =>
      cdt.delete.zs hP hO hsc hV hDO hDC hwu hIO hap h1.1 hx hxI hD hX hN⟩⟩

end ST
end R
end W7

end

end Fl4ProofsA64.P1
