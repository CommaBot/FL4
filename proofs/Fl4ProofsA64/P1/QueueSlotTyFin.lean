/-
P1 (aarch64, gen 30): **more deletion kinds over `SlotTy`**: the finalisations that change no store word.

Gen 29's `cdt.delete.triv` covers the `TrivK` kinds, whose `finalise_cap` changes nothing for either finality.
Here the coverage grows by the finalisations that change no store word **for the finality and the state the
deletion actually meets** (objects.rs `finalise_cap` / `finalise_cap_object`, Funs.lean `objects.finalise_cap`,
`objects.finalise_cap_object`):

* **non-final caps** (`fin = false`, `NonFinK`) of the kinds whose `finalise_cap_object` then returns
  `(Null, Null)` and the state unchanged: `Endpoint`, `Notification`, `Reply`, `CNode`, `Thread`, `IrqHandler`
  (its pre-match `deleting_irq_handler` runs only when final), `SchedContext`, `PageTable` / `PageDirectory` /
  `Pdpt` / `Pml4` / `HighVSpace` (mapped or not), `Vcpu`, `Ept`, `AsidPool`;
* a **final endpoint with an idle queue** (`cancel_all_ipc` returns the state when the state bits are
  `EP_IDLE` = 0, endpoint.rs `cancel_all_ipc`);
* a **final reply object with no TCB** (`Reply.tcb` = 0: the `is_null` arm);
* an **unmapped frame, or one mapped with ASID 0**, final or not (no unmap; a final device frame's
  `retire_dma_frame` changes the arch state only, `ArchTotal`).

`FinTriv s c fin` collects these with `TrivK`; `CapFinTrivAt x s` says the cap in `x` is `FinTriv` for the
finality `is_final_capability_with_cap` computes at `s`. Proved, no named premise:
`finalise_cap.fintriv`, `cdt.finalise_slot_immediate.fintriv`, **`cdt.delete.fintriv`** (`J` to `J`, like
`cdt.delete.triv`), and `cdt.delete.fintriv_of_triv` (the old case is a special case).

Not covered (each needs a finaliser footprint finer than `Foot`'s `KW`, see the handoff §34): final endpoints with
waiters, final notifications, final replies with a TCB, final CNodes / threads / Zombies, final IRQ handlers,
final SCs, mapped frames with an ASID, final mapped VSpace caps, final VCPU / EPT / ASID-pool caps, I/O ports.

No existing statement changed; no new premise.
-/
import Fl4ProofsA64.P1.QueueSlotTyDec
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {P3Ok : S → Prop} {U : Set U64}

namespace W7
namespace R
namespace ST

theorem eq_of_spec {α : Type _} {m : Result α} {v : α} (h : m ⦃ r => r = v ⦄) : m = ok v := by
  revert h; cases m <;> simp [WP.spec_vis, WP.spec_div, WP.spec_ok]

/-- The kinds whose `finalise_cap_object` with `fin = false` returns `(Null, Null)` and the state unchanged. -/
def NonFinK (c : capability.Cap) : Prop :=
  (∃ p b x y z w, c = .Endpoint p b x y z w) ∨ (∃ p b x y, c = .Notification p b x y) ∨ (∃ p b, c = .Reply p b) ∨
  (∃ p r g b, c = .CNode p r g b) ∨ (∃ p, c = .Thread p) ∨ (∃ i, c = .IrqHandler i) ∨
  (∃ p b, c = .SchedContext p b) ∨ (∃ p m a v, c = .PageTable p m a v) ∨ (∃ p m a v, c = .PageDirectory p m a v) ∨
  (∃ p m a v, c = .Pdpt p m a v) ∨ (∃ p m a, c = .Pml4 p m a) ∨ (∃ p m a, c = .HighVSpace p m a) ∨
  (∃ p, c = .Vcpu p) ∨ (∃ p q r u w, c = .Ept p q r u w) ∨ (∃ p b, c = .AsidPool p b)

/-- **A finalisation that changes no store word**, for the finality `fin` and the state `s` (module docstring). -/
def FinTriv (st : machine.Store S) [L : LawfulStore st] (s : S) (c : capability.Cap) (fin : Bool) : Prop :=
  TrivK c ∨ (fin = false ∧ NonFinK c) ∨
  (∃ p b x y z w, c = .Endpoint p b x y z w ∧ L.epState s p = 0#u64) ∨
  (∃ p b, c = .Reply p b ∧ L.mem s (rTcbA p) = 0#u64) ∨
  (∃ p sz d dev m e asid v, c = .Frame p sz d dev m e asid v ∧ (m = false ∨ asid = 0#u64))

theorem finalise_cap.nonfin {A : Type _} (ar : machine.Arch A) (s : S) (a : A) {c : capability.Cap}
    (hk : NonFinK c) : objects.finalise_cap st ar s a c false false = ok ((.Null, .Null), s, a) := by
  rcases hk with ⟨_, _, _, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, rfl⟩ |
    ⟨_, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ |
    ⟨_, _, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, rfl⟩ <;>
  first
  | rfl
  | (simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok, Bool.false_eq_true, ↓reduceIte]; done)
  | (simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok, Bool.false_eq_true, ↓reduceIte]; rfl)
  | simp [objects.finalise_cap, objects.finalise_cap_object]

theorem cai_idle {s : S} {p : U64} (h : L.epState s p = 0#u64) : endpoint.cancel_all_ipc st s p = ok s := by
  unfold endpoint.cancel_all_ipc
  rw [eq_of_spec (obj.Ep.state.spec s p), bind_ok, h]
  have e : (0#u64 = obj.EP_IDLE) := by unfold obj.EP_IDLE; rfl
  rw [if_pos e]

theorem finalise_cap.ep_idle {A : Type _} (ar : machine.Arch A) (s : S) (a : A) {p b x y z w : _}
    (h : L.epState s p = 0#u64) (fin : Bool) :
    objects.finalise_cap st ar s a (.Endpoint p b x y z w) fin false = ok ((.Null, .Null), s, a) := by
  cases fin
  · exact finalise_cap.nonfin ar s a (by unfold NonFinK; exact Or.inl ⟨p, b, x, y, z, w, rfl⟩)
  · first
    | (simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok, ↓reduceIte, cai_idle h]; done)
    | (simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok, ↓reduceIte, cai_idle h]; rfl)
    | simp [objects.finalise_cap, objects.finalise_cap_object, cai_idle h]

theorem finalise_cap.reply_null {A : Type _} (ar : machine.Arch A) (s : S) (a : A) {p : U64} {b : Bool}
    (h : L.mem s (rTcbA p) = 0#u64) (fin : Bool) :
    objects.finalise_cap st ar s a (.Reply p b) fin false = ok ((.Null, .Null), s, a) := by
  cases fin
  · exact finalise_cap.nonfin ar s a (by unfold NonFinK; exact Or.inr (Or.inr (Or.inl ⟨p, b, rfl⟩)))
  · have e1 : obj.Reply.tcb st p s = ok 0#u64 := by rw [eq_of_spec (obj.Reply.tcb.blk s p), h]
    have e2 : obj.Tcb.is_null 0#u64 = ok true := by rw [eq_of_spec (obj.Tcb.is_null.spec 0#u64)]; simp
    first
    | (simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok, ↓reduceIte, e1, e2]; done)
    | (simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok, ↓reduceIte, e1, e2]; rfl)
    | simp [objects.finalise_cap, objects.finalise_cap_object, e1, e2]

set_option maxHeartbeats 2000000 in
theorem finalise_cap.frame_off {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    {p : U64} {sz : capability.FrameSize} {d : U64} {dev m e : Bool} {asid v : U64} (hm : m = false ∨ asid = 0#u64)
    (fin : Bool) :
    objects.finalise_cap st ar s a (.Frame p sz d dev m e asid v) fin false ⦃ r =>
      r.1 = (.Null, .Null) ∧ r.2.1 = s ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have key : ∀ m' asid' : _, (m' = false ∨ asid' = 0#u64) →
      objects.finalise_cap st ar s a (.Frame p sz d dev m' e asid' v) fin false ⦃ r =>
        r.1 = (.Null, .Null) ∧ r.2.1 = s ⦄ := by
    intro m' asid' hm'
    rcases hm' with rfl | rfl
    all_goals
      first
      | cases m'
      | skip
    all_goals
      cases fin <;> cases dev <;> cases e <;>
      first
      | (simp [objects.finalise_cap, objects.finalise_cap_object, WP.spec_ok]; done)
      | (simp [objects.finalise_cap, objects.finalise_cap_object]
         refine WP.spec_bind (P0.objects.retire_dma_frame.p0 st ar s a p sz hS hA) fun a2 _ => ?_
         simp [WP.spec_ok])
  exact key m asid hm

/-- **`finalise_cap` of a `FinTriv` cap**: `(Null, Null)` and the store state unchanged. -/
theorem finalise_cap.fintriv {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    {c : capability.Cap} {fin : Bool} (hk : FinTriv st s c fin) :
    objects.finalise_cap st ar s a c fin false ⦃ r => r.1 = (.Null, .Null) ∧ r.2.1 = s ⦄ := by
  rcases hk with hk | ⟨rfl, hk⟩ | ⟨p, b, x, y, z, w, rfl, h⟩ | ⟨p, b, rfl, h⟩ | ⟨p, sz, d, dev, m, e, asid, v, rfl, hm⟩
  · rw [finalise_cap.triv ar s a hk fin, WP.spec_ok]; exact ⟨rfl, rfl⟩
  · rw [finalise_cap.nonfin ar s a hk, WP.spec_ok]; exact ⟨rfl, rfl⟩
  · rw [finalise_cap.ep_idle ar s a h fin, WP.spec_ok]; exact ⟨rfl, rfl⟩
  · rw [finalise_cap.reply_null ar s a h fin, WP.spec_ok]; exact ⟨rfl, rfl⟩
  · exact finalise_cap.frame_off hA s a hm fin

/-- The cap in slot `x` is `FinTriv` for the finality computed at `s`. -/
def CapFinTrivAt (st : machine.Store S) [L : LawfulStore st] (x : U64) (s : S) : Prop :=
  ∀ c fin, obj.Slot.cap st x s = ok c → cdt.is_final_capability_with_cap st s x c = ok fin → FinTriv st s c fin

theorem CapFinTrivAt.of_triv {x : U64} {s : S} (h : CapTrivAt st x s) : CapFinTrivAt st x s :=
  fun c _ hc _ => Or.inl (h c hc)

set_option maxHeartbeats 4000000 in
/-- `finalise_slot_immediate` of a slot holding a `FinTriv` cap: the store unchanged, a null cleanup. -/
theorem cdt.finalise_slot_immediate.fintriv {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s : S}
    {a : A} {x : U64} (hk : CapFinTrivAt st x s) :
    cdt.finalise_slot_immediate st ar s a x ⦃ r => r.2.1 = s ∧ ∀ v, r.1 = .Ok v → v.cleanup = .Null ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.finalise_slot_immediate cdt.finalise_slot_immediate_loop
  apply loop.spec_decr_nat (measure := fun y => y.2.2.val) (inv := fun y => y.1 = s)
  · rintro ⟨s1, a1, fuel⟩ h1
    simp only at h1
    have hk1 : CapFinTrivAt st x s1 := h1 ▸ hk
    dsimp only
    unfold cdt.finalise_slot_immediate_loop.body
    split
    swap
    · exact (WP.spec_ok _).2 ⟨h1, by intro v hv; simp_all⟩
    step as ⟨fuel1, hf1⟩
    obtain ⟨c, hc⟩ := DPF.spec_tot (P0.obj.Slot.cap.p0 st x s1 hS)
    rw [hc, bind_ok]
    refine WP.spec_bind (P0.capability.Cap.is_null.p0 c) fun bn _ => ?_
    split
    · exact (WP.spec_ok _).2 ⟨h1, fun v hv => by cases hv; rfl⟩
    refine WP.spec_bind (spec_eqv (P0.cdt.is_final_capability_with_cap.p0 st s1 x c hS)) fun fin hfin => ?_
    refine WP.spec_bind (finalise_cap.fintriv hA s1 a1 (hk1 c fin hc hfin.1)) ?_
    rintro ⟨⟨rem, cl⟩, s2, a2⟩ ⟨e1, e2⟩
    simp only [Prod.mk.injEq] at e1 e2
    obtain ⟨rfl, rfl⟩ := e1
    subst e2
    try dsimp only
    first
    | (simp only [cdt.cap_removable, bind_ok, ↓reduceIte]; exact (WP.spec_ok _).2 ⟨h1, fun v hv => by cases hv; rfl⟩)
    | (simp only [cdt.cap_removable, bind_ok, ↓reduceIte, WP.spec_ok]; exact ⟨h1, fun v hv => by cases hv; rfl⟩)
    | (simp [cdt.cap_removable, WP.spec_ok]; exact h1)
    | (simp [cdt.cap_removable, WP.spec_ok, h1])
  · rfl

set_option maxHeartbeats 2000000 in
/-- **The exposed `cdt.delete` of a slot of `OS` holding a `FinTriv` cap keeps `J`** (`Cur0R` and `SlotTy`). -/
theorem cdt.delete.fintriv {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {OS : Set U64}
    (hO : OSOK T Ω Sg OS) {s0 s : S} {a : A} {x : U64} (h : J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 s)
    (hx : x ∈ OS) (hk : CapFinTrivAt st x s) :
    cdt.delete st ar s a x true ⦃ r => J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 r.2.1 ⦄ := by
  unfold cdt.delete
  simp only [↓reduceIte]
  refine WP.spec_bind (cdt.finalise_slot_immediate.fintriv (ar := ar) (a := a) hA hk) ?_
  rintro ⟨r, s1, a1⟩ ⟨e1, hv1⟩
  try simp only [uncurry_apply_pair] at e1 hv1 ⊢
  subst e1
  rcases r with v | e
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    rw [hv1 v rfl]
    refine WP.spec_bind (cdt.empty_slot.ty hO h hx) ?_
    rintro ⟨s2, a2⟩ h2
    try simp only [uncurry_apply_pair] at h2 ⊢
    exact (WP.spec_ok _).2 h2
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 h

/-- `cdt.delete.triv`'s case is a case of `cdt.delete.fintriv`. -/
theorem cdt.delete.fintriv_of_triv {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {OS : Set U64}
    (hO : OSOK T Ω Sg OS) {s0 s : S} {a : A} {x : U64} (h : J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 s)
    (hx : x ∈ OS) (hk : CapTrivAt st x s) :
    cdt.delete st ar s a x true ⦃ r => J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 r.2.1 ⦄ :=
  cdt.delete.fintriv hA hO h hx (CapFinTrivAt.of_triv hk)

end ST
end R
end W7

end

end Fl4ProofsA64.P1
