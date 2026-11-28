/-
P1 (aarch64, gen 38): **the Zombie loop over a VSpace-finaliser class** — gen 37's `ZP` loop (QueueZombieP) with
its `VsCap` arm replaced by **any** class `K` of caps whose finalisation, at the states of a typing `Ty`, returns
`(Null, Null)`, writes only `VsR` words and is a `VsZ` step (`FinK`), with `Ty` kept by every `VsZ` step (`TyZ`).
Gen 37's loop is the instance `K = VsCap`, `Ty = VsTy`; QueueVsK gives the instances with ASID pools, device frames
and page-table caps inside covered slots.

* **`ZQ K Vc D Scs Fp I Is y c`** = (`ZS` cap ∧ `ObjOut Fp`) ∨ (`y ∈ Fp` ∧ `K c`); `DomQ`, `XQ`.
* **`finXQ`**: gen 36's `finXS` (with QueueZombieP's `finVZ`, `remP`) for `ZS` caps; for `K` caps `FinK` and
  QueueVsPool's `JV.vsr` (a `VsR` write set keeps `JV`, every `OS` word, the idle word and every `SC` field).
* The loop (QueueZombieP's texts, `VsTy` replaced by `Ty`, `VsTy.keepZ` by `TyZ`): `cdt.cap_swap_for_delete.zq`,
  **`cdt.finalise_slot_deferred.zq`**, **`cdt.delete_deferred.zq`**, **`cdt.finalise_slot_immediate.zq`**,
  **`cdt.delete.zqI`**, **`cdt.delete.zq`**, **`cdt.delete.threadQ`**.

**Gen 39: the step property strengthened.** The loop's texts now run over the weaker class **`FinKT`** (a `K`
finalisation keeps `Ty` itself, need not be an abstract `VsZ` step) and **`TyK`** (`Ty` kept by every step that keeps
each `VsR` word — QueueVsKeep: the non-VSpace steps keep them, `finVK`, `cdt.empty_slot.vk`,
`sched.preemption_point.vk`, `vsk_cw`): **`finXQG`**, `cdt.cap_swap_for_delete.zqG`,
**`cdt.finalise_slot_deferred.zqG`**, **`cdt.delete_deferred.zqG`**, **`cdt.finalise_slot_immediate.zqG`**,
**`cdt.delete.zqIG`**, **`cdt.delete.zqG`**, **`cdt.delete.threadQG`**. Gen 38's statements (over `FinK` / `TyZ`) are
unchanged and are corollaries (`FinK.toT`, `TyZ.toK`). This lets a typing hold a nonzero `VsR` word fixed (a
`HighVSpace` root's entry 511, QueueHiTy), which no abstract `VsZ` step keeps.

`FinK` and `TyZ` are statements about the kernel functions at every `Ty` state, discharged by proved theorems in
every instance (QueueVsK), not premises. Case hypotheses as gen 37's (state-free, or facts of the start state), with
`Ty s` at the start state for `VsTy`. No named premise; new definitions and theorems only.

**Gen 41: `Ty` in the post.** **`cdt.finalise_slot_immediate.zqGT`** and **`cdt.delete.zqIGT`** carry `Ty` to the
end state (the loop's invariant already held it; the final `empty_slot` keeps it by `cdt.empty_slot.vk`); gen 39's
`zqG` / `zqIG` keep their exact statements as corollaries.

**Gen 48: a loop-invariant field.** `LoopM st ar OS D M`: a state predicate `M` kept by each step of the loops — the
finalisation (`fin`), the in-place `Zombie` cap write (`setz`), `cap_swap_for_delete` of two domain slots (`swap`),
the preemption point (`pre`) and `empty_slot` (`emp`) — as Hoare-triple obligations (an `M` needing context, e.g.
`JV`, includes it; `LoopM.and`). The loop proofs now live in **`cdt.finalise_slot_deferred.zqGM`**,
**`cdt.delete_deferred.zqGM`**, **`cdt.finalise_slot_immediate.zqGTM`**, **`cdt.delete.zqIGTM`** (invariant and post
carry `M`); gen 39/41's `zqG` / `zqGT` / `zqIGT` are their `M := True` instances (`LoopM.triv`) with statements
unchanged (script-checked). This is the slot for the MDB facts `MdbLk ∧ RngOneA64 ∧ KindA` (not a `Ty` instance:
they are not kept by every `VsKeep` step); their obligations are listed in the a64 handoff (gen 48).

**Gen 49: the field with context.** `LoopMC st ar OS D C M`: `LoopM`'s obligations each also given `C s` (and `swap`
the `Zombie` in its second slot); the loop proofs moved (not copied) into **`cdt.finalise_slot_deferred.zqGMC`**,
**`cdt.delete_deferred.zqGMC`**, **`cdt.finalise_slot_immediate.zqGTMC`**, **`cdt.delete.zqIGTMC`** at
`C := JV s0`; gen 48's `zqGM` / `zqGTM` / `zqIGTM` are their `LoopM.toC` instances, statements unchanged
(script-checked). The MDB obligations need `JV` (`pre`: `OSKeep`; `emp`: `ks` base), hence the context.

**Gen 50: the field seeing the finalisation.** `LoopMZ st ar OS D C X Zr M`: `LoopMC`'s obligations, `fin` also given
the loop's facts on the finalised cap (`X`, here `XQF`: `ZQ`, `Ty`, `IrqN` at the round's state) and the finality the
loop computed just before (`is_final_capability_with_cap … = ok f`), returning `Zr` of the slot for a `Zombie`
remainder; `setz` given `Canon p` and `Zr`; `zz` (a `Zombie` already in the slot gives `Zr`). The loop proofs moved
(not copied) into **`cdt.finalise_slot_deferred.zqGMZ`**, **`cdt.delete_deferred.zqGMZ`**,
**`cdt.finalise_slot_immediate.zqGTMZ`**, **`cdt.delete.zqIGTMZ`**; gen 49's `zqGMC` / `zqGTMC` / `zqIGTMC` are
their `LoopMC.toZ` instances, statements unchanged (script-checked, `scratch/a64/g50/loopmz.py`). The MDB field's
`fin` / `setz` need exactly this (MdbFin): the finaliser class to know which caps change `OS` words, the finality to
rule out a second cap of the object being turned into a `Zombie`.
-/
import Fl4ProofsA64.P1.QueueZombieP
import Fl4ProofsA64.P1.QueueVsPool
import Fl4ProofsA64.P1.QueueVsKeep
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

section zq
variable {OS Vc Ub D Fp : Set U64} {kb : U64} {Pt : Set U64} {K : capability.Cap → Prop} {Ty : S → Prop}

/-! ## The domain class over a finaliser class -/

/-- **The domain class over `K`** (module docstring). -/
def ZQ (K : capability.Cap → Prop) (Vc D Scs Fp : Set U64) (I Is y : U64) (c : capability.Cap) : Prop :=
  (ZS Vc D Scs I Is c ∧ ObjOut Fp c) ∨ (y ∈ Fp ∧ K c)

def DomQ (st : machine.Store S) [L : LawfulStore st] (K : capability.Cap → Prop) (Vc D Scs Fp : Set U64)
    (I Is : U64) (s : S) : Prop :=
  ∀ y ∈ D, ∀ c, obj.Slot.cap st y s = ok c → ZQ K Vc D Scs Fp I Is y c

def XQ (st : machine.Store S) [L : LawfulStore st] (K : capability.Cap → Prop) (Vc D Scs Fp : Set U64)
    (I Is : U64) (x : U64) (s : S) : Prop :=
  ∀ c, obj.Slot.cap st x s = ok c → ZQ K Vc D Scs Fp I Is x c

theorem zq_null {I Is y : U64} : ZQ K Vc D Scs Fp I Is y .Null := Or.inl ⟨zs_null, objout_null⟩

theorem zq_z {I Is y p t n : U64} (hcov : ∀ i : U64, i.val < n.val → slotIdx p i ∈ D) (h : p ∉ Fp) :
    ZQ K Vc D Scs Fp I Is y (.Zombie p t n) :=
  Or.inl ⟨Or.inl (Or.inl (Or.inr (Or.inr ⟨p, _, _, rfl, hcov⟩))), objout_z h⟩

theorem DomQ.oka {I Is kb' : U64} {s s' : S} (h : DomQ st K Vc D Scs Fp I Is s) (hI : ∀ y ∈ D, ¬ IslN kb' y)
    (hDO : D ⊆ OS) (k : OKA st OS kb' s s') : DomQ st K Vc D Scs Fp I Is s' := fun y hy c hc => by
  rcases k y (hDO hy) with e | e
  · rw [e] at hc; exact h y hy c hc
  · exact absurd e.1 (hI y hy)

theorem DomQ.upd {I Is : U64} {s s' : S} (h : DomQ st K Vc D Scs Fp I Is s)
    (hk : ∀ y ∈ D, obj.Slot.cap st y s' = obj.Slot.cap st y s ∨
      ∀ c, obj.Slot.cap st y s' = ok c → ZQ K Vc D Scs Fp I Is y c) :
    DomQ st K Vc D Scs Fp I Is s' := fun y hy c hc => by
  rcases hk y hy with e | e
  · rw [e] at hc; exact h y hy c hc
  · exact e c hc

theorem XQ.oka {I Is kb' x : U64} {s s' : S} (h : XQ st K Vc D Scs Fp I Is x s) (hx : x ∈ OS)
    (hxI : ¬ IslN kb' x) (k : OKA st OS kb' s s') : XQ st K Vc D Scs Fp I Is x s' := fun c hc => by
  rcases k x hx with e | e
  · rw [e] at hc; exact h c hc
  · exact absurd e.1 hxI

/-! ## The finaliser class -/

variable {A : Type _} {ar : machine.Arch A}

/-- **A VSpace-finaliser class over a typing `Ty`**: at a `Ty` state with `ks` base `kb`, finalising a `K` cap (any
finality) returns `(Null, Null)`, writes only `VsR kb Pt` words and is a `VsZ` step. -/
def FinK (st : machine.Store S) [L : LawfulStore st] (ar : machine.Arch A) (kb : U64) (Pt : Set U64)
    (Ty : S → Prop) (K : capability.Cap → Prop) : Prop :=
  ∀ (s : S) (a : A) (c : capability.Cap) (fin : Bool), Ty s → L.ksb s = kb → K c →
    objects.finalise_cap st ar s a c fin false ⦃ r =>
      r.1 = (.Null, .Null) ∧ WritesIn st s r.2.1 (VsR kb Pt) ∧ VsZ st kb Pt s r.2.1 ⦄

/-- **`Ty` is kept by every `VsZ` step.** -/
def TyZ (st : machine.Store S) [L : LawfulStore st] (kb : U64) (Pt : Set U64) (Ty : S → Prop) : Prop :=
  ∀ s s', Ty s → VsZ st kb Pt s s' → Ty s'

/-- **A VSpace-finaliser class carrying its typing** (gen 39; the generic loop's class): at a `Ty` state with `ks`
base `kb`, finalising a `K` cap (any finality) returns `(Null, Null)`, writes only `VsR kb Pt` words, and `Ty` holds
after it. Weaker than `FinK` + `TyZ` (`FinK.toT`): the finaliser need not be an abstract `VsZ` step. -/
def FinKT (st : machine.Store S) [L : LawfulStore st] (ar : machine.Arch A) (kb : U64) (Pt : Set U64)
    (Ty : S → Prop) (K : capability.Cap → Prop) : Prop :=
  ∀ (s : S) (a : A) (c : capability.Cap) (fin : Bool), Ty s → L.ksb s = kb → K c →
    objects.finalise_cap st ar s a c fin false ⦃ r =>
      r.1 = (.Null, .Null) ∧ WritesIn st s r.2.1 (VsR kb Pt) ∧ Ty r.2.1 ⦄

/-- **`Ty` is kept by every step keeping each `VsR` word** (gen 39; weaker than `TyZ`, `TyZ.toK`). -/
def TyK (st : machine.Store S) [L : LawfulStore st] (kb : U64) (Pt : Set U64) (Ty : S → Prop) : Prop :=
  ∀ s s', Ty s → VsKeep st kb Pt s s' → Ty s'

theorem TyZ.toK {kb : U64} (h : TyZ st kb Pt Ty) : TyK st kb Pt Ty := fun s s' hy k => h s s' hy k.vsz

/-- **A loop-invariant field** (gen 48): a state predicate `M` kept by each step of the Zombie loops below — the
finalisation, the in-place `Zombie` cap write, `cap_swap_for_delete` of two slots of the domain, the preemption point
and `empty_slot` — stated as Hoare-triple obligations on the kernel functions. `M := True` (`LoopM.triv`) gives back
the loops' earlier statements; an `M` that needs context (e.g. `JV`) includes it. -/
structure LoopM (st : machine.Store S) [L : LawfulStore st] (ar : machine.Arch A) (OS D : Set U64) (M : S → Prop) :
    Prop where
  fin : ∀ (s : S) (a : A) (x : U64) (c : capability.Cap) (f : Bool), M s → x ∈ OS → obj.Slot.cap st x s = ok c →
    objects.finalise_cap st ar s a c f false ⦃ r => M r.2.1 ⦄
  setz : ∀ (s : S) (x p t n : U64), M s → x ∈ OS → obj.Slot.set_cap st x s (.Zombie p t n) ⦃ s' => M s' ⦄
  swap : ∀ (s : S) (p y : U64), M s → p ∈ D → y ∈ D → p ≠ y → cdt.cap_swap_for_delete st s p y ⦃ s' => M s' ⦄
  pre : ∀ (s : S) (a : A), M s → sched.preemption_point st ar s a ⦃ r => M r.2.1 ⦄
  emp : ∀ (s : S) (a : A) (x : U64) (cl : capability.Cap), M s → x ∈ OS → ClOK cl →
    cdt.empty_slot st ar s a x cl ⦃ r => M r.1 ⦄

/-- The trivial field. -/
theorem LoopM.triv (hP : P0.ArchTotal ar) : LoopM st ar OS D (fun _ => True) where
  fin s a _ c f _ _ _ := WP.spec_mono (P0.objects.finalise_cap.p0 st ar s a c f false L.total hP) fun _ _ => trivial
  setz s x _ _ _ _ _ := WP.spec_mono (P0.obj.Slot.set_cap.p0 st x s _ L.total) fun _ _ => trivial
  swap s p y _ _ _ _ := WP.spec_mono (P0.cdt.cap_swap_for_delete.p0 st s p y L.total) fun _ _ => trivial
  pre s a _ := WP.spec_mono (P0.sched.preemption_point.p0 st ar s a L.total hP) fun _ _ => trivial
  emp s a x cl _ _ _ := WP.spec_mono (P0.cdt.empty_slot.p0 st ar s a x cl L.total hP) fun _ _ => trivial

/-- Two fields together. -/
theorem LoopM.and {M1 M2 : S → Prop} (h1 : LoopM st ar OS D M1) (h2 : LoopM st ar OS D M2) :
    LoopM st ar OS D (fun s => M1 s ∧ M2 s) where
  fin s a x c f m hx hc := WP.spec_and (h1.fin s a x c f m.1 hx hc) (h2.fin s a x c f m.2 hx hc)
  setz s x p t n m hx := WP.spec_and (h1.setz s x p t n m.1 hx) (h2.setz s x p t n m.2 hx)
  swap s p y m hp hy hne := WP.spec_and (h1.swap s p y m.1 hp hy hne) (h2.swap s p y m.2 hp hy hne)
  pre s a m := WP.spec_and (h1.pre s a m.1) (h2.pre s a m.2)
  emp s a x cl m hx hc := WP.spec_and (h1.emp s a x cl m.1 hx hc) (h2.emp s a x cl m.2 hx hc)

/-- **A loop-invariant field with context** (gen 49): `LoopM`'s obligations, each also given `C s` (the loops
instantiate `C` with their own `JV` at `s0`, which carries `ks` base and the slot typing), `swap` also given the
`Zombie` its second slot holds (cdt.rs:257–262: `slot` was just rewritten to the `Zombie`). `LoopM.toC`: every
`LoopM` field is one. -/
structure LoopMC (st : machine.Store S) [L : LawfulStore st] (ar : machine.Arch A) (OS D : Set U64)
    (C M : S → Prop) : Prop where
  fin : ∀ (s : S) (a : A) (x : U64) (c : capability.Cap) (f : Bool), C s → M s → x ∈ OS →
    obj.Slot.cap st x s = ok c → objects.finalise_cap st ar s a c f false ⦃ r => M r.2.1 ⦄
  setz : ∀ (s : S) (x p t n : U64), C s → M s → x ∈ OS → obj.Slot.set_cap st x s (.Zombie p t n) ⦃ s' => M s' ⦄
  swap : ∀ (s : S) (p y : U64), C s → M s → p ∈ D → y ∈ D → p ≠ y →
    (∃ p' t n, obj.Slot.cap st y s = ok (.Zombie p' t n)) → cdt.cap_swap_for_delete st s p y ⦃ s' => M s' ⦄
  pre : ∀ (s : S) (a : A), C s → M s → sched.preemption_point st ar s a ⦃ r => M r.2.1 ⦄
  emp : ∀ (s : S) (a : A) (x : U64) (cl : capability.Cap), C s → M s → x ∈ OS → ClOK cl →
    cdt.empty_slot st ar s a x cl ⦃ r => M r.1 ⦄

/-- A context-free field is a field with any context. -/
theorem LoopM.toC {M : S → Prop} (h : LoopM st ar OS D M) (C : S → Prop) : LoopMC st ar OS D C M where
  fin s a x c f _ m hx hc := h.fin s a x c f m hx hc
  setz s x p t n _ m hx := h.setz s x p t n m hx
  swap s p y _ m hp hy hne _ := h.swap s p y m hp hy hne
  pre s a _ m := h.pre s a m
  emp s a x cl _ m hx hc := h.emp s a x cl m hx hc

/-- **The loop's facts on the cap it finalises** (gen 50; `LoopMZ`'s `X` in the loops below): a `ZQ` cap at the
round's idle word and idle `SC` field, `Ty` and `IrqN` at the round's state. -/
abbrev XQF (st : machine.Store S) [L : LawfulStore st] (K : capability.Cap → Prop) (Vc D Scs Fp : Set U64)
    (Ty : S → Prop) (kb : U64) (s : S) (x : U64) (c : capability.Cap) : Prop :=
  ZQ K Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) x c ∧ Ty s ∧ IrqN st kb s

/-- **A loop-invariant field with the finalisation's facts** (gen 50): `LoopMC`'s obligations, `fin` also given the
loop's facts `X s x c` on the cap and the finality just computed (cdt.rs: `is_final_capability_with_cap` before
`finalise_cap`), and returning, for a `Zombie p t _` remainder, `Zr` of the slot at the end state; `setz` (the
`Zombie` write right after, or the shrunk `Zombie` of the immediate loop) given `Canon p` and `Zr`; `zz`: a slot
holding `Zombie p t _` satisfies `Zr` (the immediate loop's second write, cdt.rs: only when the slot still holds the
same `Zombie`). `LoopMC.toZ`: every `LoopMC` field is one (`Zr := True`). -/
structure LoopMZ (st : machine.Store S) [L : LawfulStore st] (ar : machine.Arch A) (OS D : Set U64)
    (C : S → Prop) (X : S → U64 → capability.Cap → Prop) (Zr : S → U64 → U64 → U64 → Prop) (M : S → Prop) :
    Prop where
  fin : ∀ (s : S) (a : A) (x : U64) (c : capability.Cap) (f : Bool), C s → M s → x ∈ OS →
    obj.Slot.cap st x s = ok c → X s x c → cdt.is_final_capability_with_cap st s x c = ok f →
    objects.finalise_cap st ar s a c f false ⦃ r => M r.2.1 ∧ ∀ p t n, r.1.1 = .Zombie p t n → Zr r.2.1 x p t ⦄
  zz : ∀ (s : S) (x p t n : U64), obj.Slot.cap st x s = ok (.Zombie p t n) → Zr s x p t
  setz : ∀ (s : S) (x p t n : U64), C s → M s → x ∈ OS → Canon p → Zr s x p t →
    obj.Slot.set_cap st x s (.Zombie p t n) ⦃ s' => M s' ⦄
  swap : ∀ (s : S) (p y : U64), C s → M s → p ∈ D → y ∈ D → p ≠ y →
    (∃ p' t n, obj.Slot.cap st y s = ok (.Zombie p' t n)) → cdt.cap_swap_for_delete st s p y ⦃ s' => M s' ⦄
  pre : ∀ (s : S) (a : A), C s → M s → sched.preemption_point st ar s a ⦃ r => M r.2.1 ⦄
  emp : ∀ (s : S) (a : A) (x : U64) (cl : capability.Cap), C s → M s → x ∈ OS → ClOK cl →
    cdt.empty_slot st ar s a x cl ⦃ r => M r.1 ⦄

/-- A `LoopMC` field is a `LoopMZ` field with any `X` and `Zr := True`. -/
theorem LoopMC.toZ {C M : S → Prop} (h : LoopMC st ar OS D C M) (X : S → U64 → capability.Cap → Prop) :
    LoopMZ st ar OS D C X (fun _ _ _ _ => True) M where
  fin s a x c f hC m hx hc _ _ := WP.spec_mono (h.fin s a x c f hC m hx hc) fun _ m' => ⟨m', fun _ _ _ _ => trivial⟩
  zz _ _ _ _ _ _ := trivial
  setz s x p t n hC m hx _ _ := h.setz s x p t n hC m hx
  swap s p y hC m hp hy hne hz := h.swap s p y hC m hp hy hne hz
  pre s a hC m := h.pre s a hC m
  emp s a x cl hC m hx hc := h.emp s a x cl hC m hx hc

theorem FinK.toT {kb : U64} (hK : FinK st ar kb Pt Ty K) (hT : TyZ st kb Pt Ty) : FinKT st ar kb Pt Ty K :=
  fun s a c fin hy hk hc => WP.spec_mono (hK s a c fin hy hk hc) fun r ⟨e, w, z⟩ => ⟨e, w, hT _ _ hy z⟩

set_option maxHeartbeats 4000000 in
/-- **The finalisation of a `ZQ` cap** (at the round's idle word and idle `SC` field, `Ty` at the round's state):
gen 36's `finXS` facts, a `ZRemP` remainder and a `VsZ` step. -/
theorem finXQ (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub)
    (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) (hK : FinK st ar kb Pt Ty K) {s0 s : S}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hIO : IrqOK OS D (L.ksb s0))
    (hN : IrqN st (L.ksb s0) s) (hY : Ty s) (hk : L.ksb s = kb) {x : U64} (hx : x ∈ OS)
    {c : capability.Cap} (hc : obj.Slot.cap st x s = ok c)
    (hX : ZQ K Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) x c) (a : A) (fin : Bool) :
    objects.finalise_cap st ar s a c fin false ⦃ r => ClOK r.1.2 ∧
      JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧ OKA st OS (L.ksb s0) s r.2.1 ∧ ZRemP D Fp r.1.1 ∧
      L.idleW r.2.1 = L.idleW s ∧ L.mem r.2.1 (scA (L.idleW s)) = L.mem s (scA (L.idleW s)) ∧
      VsZ st kb Pt s r.2.1 ⦄ := by
  rcases hX with ⟨hz, hout⟩ | ⟨-, hk'⟩
  · refine WP.spec_mono (WP.spec_and (WP.spec_and (finXS hP hO hA hV h hIO hN hx hc hz a fin)
      (finVZ hP hO hA hV hR h hIO hN hx hc hz a fin)) (remP hP hO hA hV h hIO hN hx hc hz a fin)) ?_
    rintro r ⟨⟨⟨e, h2, k2, z2, i2, j2⟩, v2⟩, p2⟩
    refine ⟨e, h2, k2, ?_, i2, j2, v2⟩
    rcases z2 with e' | ⟨p, t, n, e', hcp, hcov⟩
    · exact Or.inl e'
    · exact Or.inr ⟨p, t, n, e', hcp, hcov, hout p (p2 p t n e')⟩
  · have hiT := h.idleT
    refine WP.spec_mono (hK s a c fin hY hk hk') ?_
    rintro r ⟨e, w, z⟩
    obtain ⟨h2, k2, i2, K2⟩ := JV.vsr hO hV hR h w
    rw [e]
    exact ⟨Or.inl rfl, h2, OKA.of_osk k2, Or.inl rfl, i2, K2 _ hiT, z⟩

set_option maxHeartbeats 4000000 in
/-- **The finalisation of a `ZQ` cap over `FinKT` / `TyK`** (gen 39): `finXQ`'s facts with `Ty` after it. -/
theorem finXQG (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub)
    (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) (hK : FinKT st ar kb Pt Ty K) (hTy : TyK st kb Pt Ty) {s0 s : S}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hIO : IrqOK OS D (L.ksb s0))
    (hN : IrqN st (L.ksb s0) s) (hY : Ty s) (hk : L.ksb s = kb) {x : U64} (hx : x ∈ OS)
    {c : capability.Cap} (hc : obj.Slot.cap st x s = ok c)
    (hX : ZQ K Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) x c) (a : A) (fin : Bool) :
    objects.finalise_cap st ar s a c fin false ⦃ r => ClOK r.1.2 ∧
      JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧ OKA st OS (L.ksb s0) s r.2.1 ∧ ZRemP D Fp r.1.1 ∧
      L.idleW r.2.1 = L.idleW s ∧ L.mem r.2.1 (scA (L.idleW s)) = L.mem s (scA (L.idleW s)) ∧ Ty r.2.1 ⦄ := by
  rcases hX with ⟨hz, hout⟩ | ⟨-, hk'⟩
  · refine WP.spec_mono (WP.spec_and (WP.spec_and (finXS hP hO hA hV h hIO hN hx hc hz a fin)
      (finVK hP hO hA hV hR h hIO hN hx hc hz a fin)) (remP hP hO hA hV h hIO hN hx hc hz a fin)) ?_
    rintro r ⟨⟨⟨e, h2, k2, z2, i2, j2⟩, v2⟩, p2⟩
    refine ⟨e, h2, k2, ?_, i2, j2, hTy _ _ hY v2⟩
    rcases z2 with e' | ⟨p, t, n, e', hcp, hcov⟩
    · exact Or.inl e'
    · exact Or.inr ⟨p, t, n, e', hcp, hcov, hout p (p2 p t n e')⟩
  · have hiT := h.idleT
    refine WP.spec_mono (hK s a c fin hY hk hk') ?_
    rintro r ⟨e, w, y⟩
    obtain ⟨h2, k2, i2, K2⟩ := JV.vsr hO hV hR h w
    rw [e]
    exact ⟨Or.inl rfl, h2, OKA.of_osk k2, Or.inl rfl, i2, K2 _ hiT, y⟩

/-! ## The swap, the deferred round -/

set_option maxHeartbeats 4000000 in
/-- **`cap_swap_for_delete` of a slot of `D` outside `Fp` and a slot of `D` holding a `ZS` cap.** -/
theorem cdt.cap_swap_for_delete.zqG (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS)
    (hDC : DCan D) (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) {s0 s : S} {I Is kb' : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hD : DomQ st K Vc D Scs Fp I Is s) {p y : U64}
    (hp : p ∈ D) (hpF : p ∉ Fp) (hy : y ∈ D)
    (hyc : ∀ c, obj.Slot.cap st y s = ok c → ZS Vc D Scs I Is c ∧ ObjOut Fp c) (hne : p ≠ y) :
    cdt.cap_swap_for_delete st s p y ⦃ s' => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s' ∧
      DomQ st K Vc D Scs Fp I Is s' ∧ OKD st OS D kb' s s' ∧ L.idleW s' = L.idleW s ∧ ScK st T s s' ∧
      VsKeep st kb Pt s s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  obtain ⟨Ac', hb⟩ := h.1.parts
  have q := hb.1.choose_spec.choose_spec
  unfold cdt.cap_swap_for_delete
  simp only [obj.Slot.Insts.CoreCmpPartialEqSlot.eq, bind_ok]
  split
  · rename_i he; exfalso; apply hne; simpa using he
  obtain ⟨c1, hc1⟩ := DPF.spec_tot (P0.obj.Slot.cap.p0 st p s hS)
  obtain ⟨c2, hc2⟩ := DPF.spec_tot (P0.obj.Slot.cap.p0 st y s hS)
  rw [hc1, bind_ok, hc2, bind_ok]
  have z1 : ZS Vc D Scs I Is c1 ∧ ObjOut Fp c1 := by
    rcases hD p hp c1 hc1 with h1 | ⟨h1, -⟩
    · exact h1
    · exact absurd h1 hpF
  have z2 := hyc c2 hc2
  refine WP.spec_mono (cdt.swap.jvo hO hV h (hDO hp) (hDO hy) hne (hDC p hp) (hDC y hy) hc1 hc2 (zs_nf z1.1)
    (zs_nf z2.1)) ?_
  rintro s' ⟨⟨⟨h', e1, e2, ek⟩, w⟩, o⟩
  refine ⟨h', fun z hz c hc => ?_,
    fun z hz hzD => Or.inl (ek z hz (fun e => hzD (e ▸ hp)) (fun e => hzD (e ▸ hy))), JV.idle_cw h w,
    JV.sik_cw h w, vsk_cw q hR o⟩
  by_cases e1' : z = p
  · subst e1'; rw [e1] at hc; rw [← okinj hc]; exact Or.inl z2
  · by_cases e2' : z = y
    · subst e2'; rw [e2] at hc; rw [← okinj hc]; exact Or.inl z1
    · rw [ek z (hDO hz) e1' e2'] at hc; exact hD z hz c hc
/-- **`cap_swap_for_delete.zqG` with the `VsZ` post** (gen 38's statement). -/
theorem cdt.cap_swap_for_delete.zq (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS)
    (hDC : DCan D) (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) {s0 s : S} {I Is kb' : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hD : DomQ st K Vc D Scs Fp I Is s) {p y : U64}
    (hp : p ∈ D) (hpF : p ∉ Fp) (hy : y ∈ D)
    (hyc : ∀ c, obj.Slot.cap st y s = ok c → ZS Vc D Scs I Is c ∧ ObjOut Fp c) (hne : p ≠ y) :
    cdt.cap_swap_for_delete st s p y ⦃ s' => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s' ∧
      DomQ st K Vc D Scs Fp I Is s' ∧ OKD st OS D kb' s s' ∧ L.idleW s' = L.idleW s ∧ ScK st T s s' ∧
      VsZ st kb Pt s s' ⦄ :=
  WP.spec_mono (cdt.cap_swap_for_delete.zqG hO hV hDO hDC hR h hD hp hpF hy hyc hne) fun _ ⟨a1, a2, a3, a4, a5, a6⟩ =>
    ⟨a1, a2, a3, a4, a5, a6.vsz⟩

set_option maxHeartbeats 4000000 in
/-- **`finalise_slot_deferred.zqG` with a field `M` seeing the finalisation** (gen 50, `LoopMZ` at `C := JV s0`, `X := XQF`). -/
theorem cdt.finalise_slot_deferred.zqGMZ (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hK : FinKT st ar (L.ksb s0) Pt Ty K) (hTy : TyK st (L.ksb s0) Pt Ty)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) {a : A} {y I Is : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hy : y ∈ D) (hD : DomQ st K Vc D Scs Fp I Is s)
    (hI : L.idleW s = I) (hIs : L.mem s (scA I) = Is) (hN : IrqN st (L.ksb s0) s)
    (hY : Ty s)
    {M : S → Prop} {Zr : S → U64 → U64 → U64 → Prop}
    (hM : LoopMZ st ar OS D (JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0) (XQF st K Vc D Scs Fp Ty (L.ksb s0)) Zr M) (hm : M s) :
    cdt.finalise_slot_deferred st ar s a y ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      DomQ st K Vc D Scs Fp I Is r.2.1 ∧ OKD st OS D (L.ksb s0) s r.2.1 ∧ L.idleW r.2.1 = I ∧
      L.mem r.2.1 (scA I) = Is ∧ Ty r.2.1 ∧ M r.2.1 ∧ ∀ v, r.1 = .Ok v → ClOK v.cleanup ⦄ := by
  have hS : P0.StoreTotal st := L.total
  obtain ⟨Ac0, hb0⟩ := h.1.parts
  have q0 := hb0.1.choose_spec.choose_spec
  unfold cdt.finalise_slot_deferred cdt.finalise_slot_deferred_loop
  apply loop.spec_decr_nat (measure := fun z => z.2.2.val)
    (inv := fun z => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 z.1 ∧ DomQ st K Vc D Scs Fp I Is z.1 ∧
      OKD st OS D (L.ksb s0) s z.1 ∧ L.idleW z.1 = I ∧ L.mem z.1 (scA I) = Is ∧ Ty z.1 ∧ M z.1)
  · rintro ⟨s1, a1, fuel⟩ ⟨h1, d1, o1, i1, j1, y1, m1⟩
    simp only at h1 d1 o1 i1 j1 y1 m1
    dsimp only
    unfold cdt.finalise_slot_deferred_loop.body
    split
    swap
    · exact (WP.spec_ok _).2 ⟨h1, d1, o1, i1, j1, y1, m1, by intro v hv; simp_all⟩
    rename_i hf
    have hf' : 0 < fuel.val := by simpa using hf
    step as ⟨fuel1, hf1⟩
    obtain ⟨c, hc⟩ := DPF.spec_tot (P0.obj.Slot.cap.p0 st y s1 hS)
    rw [hc, bind_ok]
    refine WP.spec_bind (P0.capability.Cap.is_null.p0 c) fun bn _ => ?_
    split
    · exact (WP.spec_ok _).2 ⟨h1, d1, o1, i1, j1, y1, m1, fun v hv => by cases hv; exact Or.inl rfl⟩
    refine WP.spec_bind (spec_eqv (P0.cdt.is_final_capability_with_cap.p0 st s1 y c hS)) fun fin hfe => ?_
    have hN1 : IrqN st (L.ksb s0) s1 := hN.okd hIO o1
    refine WP.spec_bind (WP.spec_and (finXQG hP hO hA hV hR hK hTy h1 hIO hN1 y1 h1.ksb (hDO hy) hc
      (by rw [i1, j1]; exact d1 y hy c hc) a1 fin) (hM.fin s1 a1 y c fin h1 m1 (hDO hy) hc ⟨(by rw [i1, j1]; exact d1 y hy c hc), y1, hN1⟩ hfe.1)) ?_
    rintro ⟨⟨rem, cl⟩, s2, a2⟩ ⟨⟨hcl, h2, k2, hrem, j2, sc2, v2⟩, m2, z2⟩
    simp only at hcl hrem j2 sc2 v2 m2 z2
    have d2 : DomQ st K Vc D Scs Fp I Is s2 := d1.oka hIO.2 hDO k2
    have o2 : OKD st OS D (L.ksb s0) s s2 := o1.trans k2.okd
    have i2 : L.idleW s2 = I := j2.trans i1
    have js2 : L.mem s2 (scA I) = Is := by rw [i1] at sc2; exact sc2.trans j1
    have y2 : Ty s2 := v2
    rcases hrem with rfl | ⟨p, t, n, rfl, hcp, hcov, hpF⟩
    · try dsimp only
      first
      | (simp only [cdt.cap_removable, bind_ok, ↓reduceIte]
         exact (WP.spec_ok _).2 ⟨h2, d2, o2, i2, js2, y2, m2, fun v hv => by cases hv; exact hcl⟩)
      | (simp only [cdt.cap_removable, bind_ok, ↓reduceIte, WP.spec_ok]
         exact ⟨h2, d2, o2, i2, js2, y2, m2, fun v hv => by cases hv; exact hcl⟩)
      | (simp [cdt.cap_removable, WP.spec_ok]; exact ⟨h2, d2, o2, i2, js2, y2, m2, hcl⟩)
    refine WP.spec_bind (spec_eqv (P0.cdt.cap_removable.p0 (.Zombie p t n) y)) fun b1 hb1 => ?_
    try dsimp only
    split
    · exact (WP.spec_ok _).2 ⟨h2, d2, o2, i2, js2, y2, m2, fun v hv => by cases hv; exact hcl⟩
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
    refine WP.spec_bind (WP.spec_and (WP.spec_and (WP.spec_and (JV.setz hO hV h2 (hDO hy) hcp ⟨hDO hp0, fun i hi =>
      hDO (hcov i hi)⟩) (W7.obj.Slot.set_cap.capw (hO.slot _ (hDO hy)))) (W7.obj.Slot.set_cap.capw (osw hO (hDO hy))))
      (hM.setz s2 y p t n h2 m2 (hDO hy) hcp (z2 p t n rfl))) ?_
    rintro s3 ⟨⟨⟨⟨h3, k3, c3⟩, w3⟩, ow3⟩, m3⟩
    have i3 : L.idleW s3 = I := (JV.idle_cw h2 w3).trans i2
    have js3 : L.mem s3 (scA I) = Is := ((JV.sik_cw h2 w3) I (i2 ▸ h2.idleT)).trans js2
    have y3 : Ty s3 := hTy _ _ y2 (vsk_cw q0 hR ow3)
    have d3 : DomQ st K Vc D Scs Fp I Is s3 := DomQ.upd d2 fun z hz => by
      by_cases e : z = y
      · right; subst e; intro c' hc'; rw [c3] at hc'; rw [← okinj hc']
        exact zq_z hcov hpF
      · left; exact capk4 k3 (hDO hz) e
    have o3 : OKD st OS D (L.ksb s0) s s3 := o2.trans fun z hz hzD => Or.inl (capk4 k3 hz (fun e => hzD (e ▸ hy)))
    refine WP.spec_bind (spec_eqv (P0.cdt.cap_cyclic_zombie.p0 (.Zombie p (t) n) y)) fun b2 hb2 => ?_
    try dsimp only
    split
    · exact (WP.spec_ok _).2 ⟨h3, d3, o3, i3, js3, y3, m3, fun v hv => by
        cases hv; first | exact Or.inl rfl | exact hcl⟩
    rename_i hcy
    have hpy : p ≠ y := by
      intro e
      have hb := hb2.1
      subst e
      simp [cdt.cap_cyclic_zombie] at hb
      simp_all
    try dsimp only
    try simp only []
    have hyc : ∀ c', obj.Slot.cap st y s3 = ok c' → ZS Vc D Scs I Is c' ∧ ObjOut Fp c' := fun c' hc' => by
      rw [c3] at hc'; rw [← okinj hc']
      exact ⟨Or.inl (Or.inl (Or.inr (Or.inr ⟨p, _, _, rfl, hcov⟩))), objout_z hpF⟩
    refine WP.spec_bind (WP.spec_and (cdt.cap_swap_for_delete.zqG (kb' := L.ksb s0) hO hV hDO hDC hR h3 d3 hp0 hpF hy
      hyc hpy) (hM.swap s3 p y h3 m3 hp0 hy hpy ⟨p, _, n, c3⟩)) ?_
    rintro s4 ⟨⟨h4, d4, o4, j4, K4, v4⟩, m4⟩
    refine WP.spec_bind (WP.spec_and (WP.spec_and (WP.spec_and (sched.preemption_point.jv hP hO hV h4 (by
      rw [h4.ksb]; exact hW)) (sched.preemption_point.si hP h4)) (sched.preemption_point.vk hP hR h4 h4.ksb))
      (hM.pre s4 _ h4 m4)) ?_
    rintro ⟨rr, s5, a5⟩ ⟨⟨⟨⟨h5, k5, j5⟩, K5⟩, v5⟩, m5⟩
    try simp only [uncurry_apply_pair] at h5 k5 j5 K5 v5 m5 ⊢
    have i5 : L.idleW s5 = I := j5.trans (j4.trans i3)
    have hIT : I ∈ T := i3 ▸ h3.idleT
    have js5 : L.mem s5 (scA I) = Is := (K5 I hIT).trans ((K4 I hIT).trans js3)
    have d5 : DomQ st K Vc D Scs Fp I Is s5 := DomQ.oka d4 hIO.2 hDO (OKA.of_osk k5)
    have o5 : OKD st OS D (L.ksb s0) s s5 := (o3.trans o4).trans (OKA.of_osk k5).okd
    have y5 : Ty s5 := hTy _ _ (hTy _ _ y3 v4) v5
    rcases rr with _ | ee
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok]
      refine (WP.spec_ok _).2 ⟨h5, d5, o5, i5, js5, y5, m5, ?_⟩
      show fuel1.val < fuel.val
      omega
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_tc_ok]
      exact (WP.spec_ok _).2 ⟨h5, d5, o5, i5, js5, y5, m5, fun v hv => by cases hv⟩
  · exact ⟨h, hD, OKD.refl s, hI, hIs, hY, hm⟩

set_option maxHeartbeats 4000000 in
/-- **`finalise_slot_deferred.zqG` with a context field `M`** (gen 49, `LoopMC` at `C := JV s0`). -/
theorem cdt.finalise_slot_deferred.zqGMC (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hK : FinKT st ar (L.ksb s0) Pt Ty K) (hTy : TyK st (L.ksb s0) Pt Ty)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) {a : A} {y I Is : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hy : y ∈ D) (hD : DomQ st K Vc D Scs Fp I Is s)
    (hI : L.idleW s = I) (hIs : L.mem s (scA I) = Is) (hN : IrqN st (L.ksb s0) s)
    (hY : Ty s)
    {M : S → Prop} (hM : LoopMC st ar OS D (JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0) M) (hm : M s) :
    cdt.finalise_slot_deferred st ar s a y ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      DomQ st K Vc D Scs Fp I Is r.2.1 ∧ OKD st OS D (L.ksb s0) s r.2.1 ∧ L.idleW r.2.1 = I ∧
      L.mem r.2.1 (scA I) = Is ∧ Ty r.2.1 ∧ M r.2.1 ∧ ∀ v, r.1 = .Ok v → ClOK v.cleanup ⦄ :=
  cdt.finalise_slot_deferred.zqGMZ (a := a) hP hO hA hV hDO hDC hR hK hTy hW hIO h hy hD hI hIs hN hY (hM.toZ _) hm

set_option maxHeartbeats 4000000 in
/-- **`finalise_slot_deferred.zqG` with a loop-invariant field `M`** (gen 48, `LoopM`). -/
theorem cdt.finalise_slot_deferred.zqGM (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hK : FinKT st ar (L.ksb s0) Pt Ty K) (hTy : TyK st (L.ksb s0) Pt Ty)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) {a : A} {y I Is : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hy : y ∈ D) (hD : DomQ st K Vc D Scs Fp I Is s)
    (hI : L.idleW s = I) (hIs : L.mem s (scA I) = Is) (hN : IrqN st (L.ksb s0) s)
    (hY : Ty s)
    {M : S → Prop} (hM : LoopM st ar OS D M) (hm : M s) :
    cdt.finalise_slot_deferred st ar s a y ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      DomQ st K Vc D Scs Fp I Is r.2.1 ∧ OKD st OS D (L.ksb s0) s r.2.1 ∧ L.idleW r.2.1 = I ∧
      L.mem r.2.1 (scA I) = Is ∧ Ty r.2.1 ∧ M r.2.1 ∧ ∀ v, r.1 = .Ok v → ClOK v.cleanup ⦄ :=
  cdt.finalise_slot_deferred.zqGMC (a := a) hP hO hA hV hDO hDC hR hK hTy hW hIO h hy hD hI hIs hN hY (hM.toC _) hm

set_option maxHeartbeats 4000000 in
/-- **`finalise_slot_deferred` of a slot of a domain of `ZQ` caps**: gen 36's facts, `DomQ` and `Ty`. -/
theorem cdt.finalise_slot_deferred.zqG (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hK : FinKT st ar (L.ksb s0) Pt Ty K) (hTy : TyK st (L.ksb s0) Pt Ty)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) {a : A} {y I Is : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hy : y ∈ D) (hD : DomQ st K Vc D Scs Fp I Is s)
    (hI : L.idleW s = I) (hIs : L.mem s (scA I) = Is) (hN : IrqN st (L.ksb s0) s)
    (hY : Ty s) :
    cdt.finalise_slot_deferred st ar s a y ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      DomQ st K Vc D Scs Fp I Is r.2.1 ∧ OKD st OS D (L.ksb s0) s r.2.1 ∧ L.idleW r.2.1 = I ∧
      L.mem r.2.1 (scA I) = Is ∧ Ty r.2.1 ∧ ∀ v, r.1 = .Ok v → ClOK v.cleanup ⦄ :=
  WP.spec_mono (cdt.finalise_slot_deferred.zqGM (a := a) hP hO hA hV hDO hDC hR hK hTy hW hIO h hy hD hI hIs hN hY
    (LoopM.triv hP) trivial) fun _ ⟨a1, a2, a3, a4, a5, a6, _, a7⟩ => ⟨a1, a2, a3, a4, a5, a6, a7⟩

set_option maxHeartbeats 4000000 in
/-- **`delete_deferred.zqG` with a field `M` seeing the finalisation** (gen 50, `LoopMZ` at `C := JV s0`, `X := XQF`). -/
theorem cdt.delete_deferred.zqGMZ (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hK : FinKT st ar (L.ksb s0) Pt Ty K) (hTy : TyK st (L.ksb s0) Pt Ty)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {y I Is : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hy : y ∈ D) (hD : DomQ st K Vc D Scs Fp I Is s)
    (hI : L.idleW s = I) (hIs : L.mem s (scA I) = Is) (hN : IrqN st (L.ksb s0) s)
    (hY : Ty s)
    {M : S → Prop} {Zr : S → U64 → U64 → U64 → Prop}
    (hM : LoopMZ st ar OS D (JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0) (XQF st K Vc D Scs Fp Ty (L.ksb s0)) Zr M) (hm : M s) :
    cdt.delete_deferred st ar s a y ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      DomQ st K Vc D Scs Fp I Is r.2.1 ∧ OKD st OS D (L.ksb s0) s r.2.1 ∧ L.idleW r.2.1 = I ∧
      L.mem r.2.1 (scA I) = Is ∧ Ty r.2.1 ∧ M r.2.1 ⦄ := by
  unfold cdt.delete_deferred
  refine WP.spec_bind (cdt.finalise_slot_deferred.zqGMZ (a := a) hP hO hA hV hDO hDC hR hK hTy hW hIO h hy hD hI hIs
    hN hY hM hm) ?_
  rintro ⟨r, s1, a1⟩ ⟨h1, d1, o1, i1, j1, y1, m1, hv1⟩
  try simp only [uncurry_apply_pair] at h1 d1 o1 i1 j1 y1 m1 hv1 ⊢
  rcases r with v | e
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    split
    · refine WP.spec_bind (WP.spec_and (WP.spec_and (cdt.empty_slot.zs (a := a1) hP hO hV h1 (hDO hy) (hv1 v rfl) hap)
        (cdt.empty_slot.vk hP hO hR h1 (hDO hy) (hv1 v rfl) h1.ksb)) (hM.emp s1 a1 y _ h1 m1 (hDO hy) (hv1 v rfl))) ?_
      rintro ⟨s2, a2⟩ ⟨⟨⟨h2, k2, c2, w2, K2⟩, v2⟩, m2⟩
      try simp only [uncurry_apply_pair] at h2 k2 c2 w2 K2 v2 m2 ⊢
      refine (WP.spec_ok _).2 ⟨h2, DomQ.upd d1 fun z hz => ?_, o1.trans (OKD.of_ck k2 hy), w2.trans i1,
        (K2 I (i1 ▸ h1.idleT)).trans j1, hTy _ _ y1 v2, m2⟩
      by_cases e : z = y
      · right; subst e; intro c hc; rw [c2] at hc; rw [← okinj hc]; exact zq_null
      · left; exact k2.cap (hDO hz) e
    · exact (WP.spec_ok _).2 ⟨h1, d1, o1, i1, j1, y1, m1⟩
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 ⟨h1, d1, o1, i1, j1, y1, m1⟩

set_option maxHeartbeats 4000000 in
/-- **`delete_deferred.zqG` with a context field `M`** (gen 49, `LoopMC` at `C := JV s0`). -/
theorem cdt.delete_deferred.zqGMC (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hK : FinKT st ar (L.ksb s0) Pt Ty K) (hTy : TyK st (L.ksb s0) Pt Ty)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {y I Is : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hy : y ∈ D) (hD : DomQ st K Vc D Scs Fp I Is s)
    (hI : L.idleW s = I) (hIs : L.mem s (scA I) = Is) (hN : IrqN st (L.ksb s0) s)
    (hY : Ty s)
    {M : S → Prop} (hM : LoopMC st ar OS D (JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0) M) (hm : M s) :
    cdt.delete_deferred st ar s a y ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      DomQ st K Vc D Scs Fp I Is r.2.1 ∧ OKD st OS D (L.ksb s0) s r.2.1 ∧ L.idleW r.2.1 = I ∧
      L.mem r.2.1 (scA I) = Is ∧ Ty r.2.1 ∧ M r.2.1 ⦄ :=
  cdt.delete_deferred.zqGMZ (a := a) hP hO hA hV hDO hDC hR hK hTy hW hIO hap h hy hD hI hIs hN hY (hM.toZ _) hm

set_option maxHeartbeats 4000000 in
/-- **`delete_deferred.zqG` with a loop-invariant field `M`** (gen 48, `LoopM`). -/
theorem cdt.delete_deferred.zqGM (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hK : FinKT st ar (L.ksb s0) Pt Ty K) (hTy : TyK st (L.ksb s0) Pt Ty)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {y I Is : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hy : y ∈ D) (hD : DomQ st K Vc D Scs Fp I Is s)
    (hI : L.idleW s = I) (hIs : L.mem s (scA I) = Is) (hN : IrqN st (L.ksb s0) s)
    (hY : Ty s)
    {M : S → Prop} (hM : LoopM st ar OS D M) (hm : M s) :
    cdt.delete_deferred st ar s a y ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      DomQ st K Vc D Scs Fp I Is r.2.1 ∧ OKD st OS D (L.ksb s0) s r.2.1 ∧ L.idleW r.2.1 = I ∧
      L.mem r.2.1 (scA I) = Is ∧ Ty r.2.1 ∧ M r.2.1 ⦄ :=
  cdt.delete_deferred.zqGMC (a := a) hP hO hA hV hDO hDC hR hK hTy hW hIO hap h hy hD hI hIs hN hY (hM.toC _) hm

set_option maxHeartbeats 4000000 in
/-- **`delete_deferred` of a slot of a domain of `ZQ` caps.** -/
theorem cdt.delete_deferred.zqG (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hK : FinKT st ar (L.ksb s0) Pt Ty K) (hTy : TyK st (L.ksb s0) Pt Ty)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {y I Is : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hy : y ∈ D) (hD : DomQ st K Vc D Scs Fp I Is s)
    (hI : L.idleW s = I) (hIs : L.mem s (scA I) = Is) (hN : IrqN st (L.ksb s0) s)
    (hY : Ty s) :
    cdt.delete_deferred st ar s a y ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      DomQ st K Vc D Scs Fp I Is r.2.1 ∧ OKD st OS D (L.ksb s0) s r.2.1 ∧ L.idleW r.2.1 = I ∧
      L.mem r.2.1 (scA I) = Is ∧ Ty r.2.1 ⦄ :=
  WP.spec_mono (cdt.delete_deferred.zqGM (a := a) hP hO hA hV hDO hDC hR hK hTy hW hIO hap h hy hD hI hIs hN hY
    (LoopM.triv hP) trivial) fun _ ⟨a1, a2, a3, a4, a5, a6, _⟩ => ⟨a1, a2, a3, a4, a5, a6⟩

/-! ## The immediate loop -/

set_option hygiene false in
/-- The preemption-point tail of an immediate round, `Ty` kept on the error exit (gen 41), `M` kept (gen 48). -/
local macro "ztailQT" : tactic => `(tactic| (
  refine WP.spec_bind (WP.spec_and (WP.spec_and (WP.spec_and (sched.preemption_point.jv hP hO hV h5 (by
    rw [h5.ksb]; exact hW)) (sched.preemption_point.si hP h5)) (sched.preemption_point.vk hP hR h5 h5.ksb))
    (hM.pre s5 _ h5 m5)) ?_
  rintro ⟨rr, s6, a6⟩ ⟨⟨⟨⟨h6, k6, i6⟩, K6⟩, v6⟩, m6⟩
  try simp only [uncurry_apply_pair] at h6 k6 i6 K6 v6 m6 ⊢
  rcases rr with _ | ee
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok]
    refine (WP.spec_ok _).2 ⟨h6, DomQ.oka d5 hIO.2 hDO (OKA.of_osk k6), XQ.oka x5 hx hxI (OKA.of_osk k6),
      i6.trans j5, (K6 I (j5 ▸ h5.idleT)).trans js5, IrqN.oka hIO N5 (OKA.of_osk k6), hTy _ _ y5 v6, m6, ?_⟩
    show fuel1.val < fuel.val
    omega
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 ⟨h6, hTy _ _ y5 v6, m6, fun v hv => by cases hv⟩))

set_option maxHeartbeats 4000000 in
/-- **`finalise_slot_immediate.zqGT` with a field `M` seeing the finalisation** (gen 50, `LoopMZ` at `C := JV s0`, `X := XQF`). -/
theorem cdt.finalise_slot_immediate.zqGTMZ (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hK : FinKT st ar (L.ksb s0) Pt Ty K) (hTy : TyK st (L.ksb s0) Pt Ty)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x I Is : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st K Vc D Scs Fp I Is s) (hX : XQ st K Vc D Scs Fp I Is x s) (hI : L.idleW s = I)
    (hIs : L.mem s (scA I) = Is) (hN : IrqN st (L.ksb s0) s) (hY : Ty s)
    {M : S → Prop} {Zr : S → U64 → U64 → U64 → Prop}
    (hM : LoopMZ st ar OS D (JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0) (XQF st K Vc D Scs Fp Ty (L.ksb s0)) Zr M) (hm : M s) :
    cdt.finalise_slot_immediate st ar s a x ⦃ r =>
      JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧ Ty r.2.1 ∧ M r.2.1 ∧ ∀ v, r.1 = .Ok v → ClOK v.cleanup ⦄ := by
  have hS : P0.StoreTotal st := L.total
  obtain ⟨Ac0, hb0⟩ := h.1.parts
  have q0 := hb0.1.choose_spec.choose_spec
  unfold cdt.finalise_slot_immediate cdt.finalise_slot_immediate_loop
  apply loop.spec_decr_nat (measure := fun y => y.2.2.val)
    (inv := fun y => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 y.1 ∧ DomQ st K Vc D Scs Fp I Is y.1 ∧
      XQ st K Vc D Scs Fp I Is x y.1 ∧ L.idleW y.1 = I ∧ L.mem y.1 (scA I) = Is ∧ IrqN st (L.ksb s0) y.1 ∧
      Ty y.1 ∧ M y.1)
  · rintro ⟨s1, a1, fuel⟩ ⟨h1, d1, x1, j1, js1, N1, y1, m1⟩
    simp only at h1 d1 x1 j1 js1 N1 y1 m1
    dsimp only
    unfold cdt.finalise_slot_immediate_loop.body
    split
    swap
    · exact (WP.spec_ok _).2 ⟨h1, y1, m1, by intro v hv; simp_all⟩
    rename_i hf
    have hf' : 0 < fuel.val := by simpa using hf
    step as ⟨fuel1, hf1⟩
    obtain ⟨c, hc⟩ := DPF.spec_tot (P0.obj.Slot.cap.p0 st x s1 hS)
    rw [hc, bind_ok]
    refine WP.spec_bind (P0.capability.Cap.is_null.p0 c) fun bn _ => ?_
    split
    · exact (WP.spec_ok _).2 ⟨h1, y1, m1, fun v hv => by cases hv; exact Or.inl rfl⟩
    refine WP.spec_bind (spec_eqv (P0.cdt.is_final_capability_with_cap.p0 st s1 x c hS)) fun fin hfe => ?_
    refine WP.spec_bind (WP.spec_and (finXQG hP hO hA hV hR hK hTy h1 hIO N1 y1 h1.ksb hx hc
      (by rw [j1, js1]; exact x1 c hc) a1 fin) (hM.fin s1 a1 x c fin h1 m1 hx hc ⟨(by rw [j1, js1]; exact x1 c hc), y1, N1⟩ hfe.1)) ?_
    rintro ⟨⟨rem, cl⟩, s2, a2⟩ ⟨⟨hcl, h2, k2, hrem, j2', sc2, v2⟩, m2, z2⟩
    simp only at hcl hrem j2' sc2 v2 m2 z2
    have d2 : DomQ st K Vc D Scs Fp I Is s2 := d1.oka hIO.2 hDO k2
    have j2 : L.idleW s2 = I := j2'.trans j1
    have js2 : L.mem s2 (scA I) = Is := by rw [j1] at sc2; exact sc2.trans js1
    have N2 : IrqN st (L.ksb s0) s2 := N1.oka hIO k2
    have y2 : Ty s2 := v2
    rcases hrem with rfl | ⟨p, t, n, rfl, hcp, hcov, hpF⟩
    · try dsimp only
      first
      | (simp only [cdt.cap_removable, bind_ok, ↓reduceIte]
         exact (WP.spec_ok _).2 ⟨h2, y2, m2, fun v hv => by cases hv; exact hcl⟩)
      | (simp only [cdt.cap_removable, bind_ok, ↓reduceIte, WP.spec_ok]; exact ⟨h2, y2, m2, fun v hv => by cases hv; exact hcl⟩)
      | (simp [cdt.cap_removable, WP.spec_ok]; exact ⟨h2, y2, m2, hcl⟩)
    refine WP.spec_bind (spec_eqv (P0.cdt.cap_removable.p0 (.Zombie p t n) x)) fun b1 hb1 => ?_
    try dsimp only
    split
    · exact (WP.spec_ok _).2 ⟨h2, y2, m2, fun v hv => by cases hv; exact hcl⟩
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
    refine WP.spec_bind (WP.spec_and (WP.spec_and (WP.spec_and (JV.setz hO hV h2 hx hcp ⟨hDO hp0, fun i hi =>
      hDO (hcov i hi)⟩) (W7.obj.Slot.set_cap.capw (hO.slot _ hx))) (W7.obj.Slot.set_cap.capw (osw hO hx)))
      (hM.setz s2 x p t n h2 m2 hx hcp (z2 p t n rfl))) ?_
    rintro s3 ⟨⟨⟨⟨h3, k3, c3⟩, w3⟩, ow3⟩, m3⟩
    have j3 : L.idleW s3 = I := (JV.idle_cw h2 w3).trans j2
    have hIT : I ∈ T := j2 ▸ h2.idleT
    have js3 : L.mem s3 (scA I) = Is := ((JV.sik_cw h2 w3) I hIT).trans js2
    have N3 : IrqN st (L.ksb s0) s3 := N2.ck hIO hxI fun y hy e => capk4 k3 hy e
    have y3 : Ty s3 := hTy _ _ y2 (vsk_cw q0 hR ow3)
    have d3 : DomQ st K Vc D Scs Fp I Is s3 := DomQ.upd d2 fun z hz => by
      by_cases e : z = x
      · right; subst e; intro c' hc'; rw [c3] at hc'; rw [← okinj hc']
        exact zq_z hcov hpF
      · left; exact capk4 k3 (hDO hz) e
    try dsimp only
    first
      | (refine WP.spec_bind (Pₘ := fun i => i = core.num.U64.wrapping_sub n 1#u64) ((WP.spec_ok _).2 rfl)
          fun i hi => ?_; subst hi)
      | simp only [lift, bind_ok]
    refine WP.spec_bind (slot_index_in p _) fun e he => ?_
    subst he
    have heD : slotIdx p (core.num.U64.wrapping_sub n 1#u64) ∈ D := hcov _ (by rw [wsub1 hn0]; omega)
    refine WP.spec_bind (cdt.delete_deferred.zqGMZ (a := a2) hP hO hA hV hDO hDC hR hK hTy hW hIO hap h3 heD d3 j3 js3
      N3 y3 hM m3) ?_
    rintro ⟨r4, s4, a4⟩ ⟨h4, d4, o4, j4, js4, y4, m4⟩
    try simp only [uncurry_apply_pair] at h4 d4 o4 j4 js4 y4 m4 ⊢
    have N4 : IrqN st (L.ksb s0) s4 := N3.okd hIO o4
    have xo4 : XQ st K Vc D Scs Fp I Is x s4 := fun c' hc' => by
      by_cases hxD : x ∈ D
      · exact d4 x hxD c' hc'
      · rcases o4 x hx hxD with e | e
        · rw [e, c3] at hc'
          rw [← okinj hc']
          exact zq_z hcov hpF
        · exact absurd e.1 hxI
    rcases r4 with _ | ee
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      obtain ⟨c4, hc4⟩ := DPF.spec_tot (P0.obj.Slot.cap.p0 st x s4 hS)
      rw [hc4, bind_ok]
      try dsimp only
      refine WP.spec_bind (Pₘ := fun y : S × A => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 y.1 ∧
        DomQ st K Vc D Scs Fp I Is y.1 ∧ XQ st K Vc D Scs Fp I Is x y.1 ∧ L.idleW y.1 = I ∧ L.mem y.1 (scA I) = Is ∧
        IrqN st (L.ksb s0) y.1 ∧ Ty y.1 ∧ M y.1) ?_ ?_
      · split
        all_goals first
          | exact (WP.spec_ok _).2 ⟨h4, d4, xo4, j4, js4, N4, y4, m4⟩
          | skip
        split
        · split
          · refine WP.spec_bind (Pₘ := fun s5 => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s5 ∧
              DomQ st K Vc D Scs Fp I Is s5 ∧ XQ st K Vc D Scs Fp I Is x s5 ∧ L.idleW s5 = I ∧ L.mem s5 (scA I) = Is ∧
              IrqN st (L.ksb s0) s5 ∧ Ty s5 ∧ M s5) ?_ fun s5 h5 => (WP.spec_ok _).2 h5
            split
            · try simp only [lift, bind_ok]
              refine WP.spec_mono (WP.spec_and (WP.spec_and (WP.spec_and (JV.setz hO hV h4 hx hcp ⟨hDO hp0,
                fun i hi => hDO (hcov i (by rw [wsub1 hn0] at hi; omega))⟩) (W7.obj.Slot.set_cap.capw (hO.slot _ hx)))
                (W7.obj.Slot.set_cap.capw (osw hO hx))) (hM.setz s4 x p _ _ h4 m4 hx hcp (hM.zz s4 x p _ _ (by subst_vars; exact hc4)))) ?_
              rintro s5 ⟨⟨⟨⟨h5, k5, c5⟩, w5⟩, ow5⟩, m5⟩
              refine ⟨h5, DomQ.upd d4 fun z hz => ?_, fun c' hc' => ?_, (JV.idle_cw h4 w5).trans j4,
                ((JV.sik_cw h4 w5) I (j4 ▸ h4.idleT)).trans js4, N4.ck hIO hxI fun y hy e => capk4 k5 hy e,
                hTy _ _ y4 (vsk_cw q0 hR ow5), m5⟩
              · by_cases e : z = x
                · right; subst e; intro c' hc'; rw [c5] at hc'; rw [← okinj hc']
                  exact zq_z (fun i hi => hcov i (by rw [wsub1 hn0] at hi; omega)) hpF
                · left; exact capk4 k5 (hDO hz) e
              · rw [c5] at hc'; rw [← okinj hc']
                exact zq_z (fun i hi => hcov i (by rw [wsub1 hn0] at hi; omega)) hpF
            · exact (WP.spec_ok _).2 ⟨h4, d4, xo4, j4, js4, N4, y4, m4⟩
          · exact (WP.spec_ok _).2 ⟨h4, d4, xo4, j4, js4, N4, y4, m4⟩
        · exact (WP.spec_ok _).2 ⟨h4, d4, xo4, j4, js4, N4, y4, m4⟩
      rintro ⟨s5, a5⟩ ⟨h5, d5, x5, j5, js5, N5, y5, m5⟩
      try simp only [uncurry_apply_pair] at h5 d5 x5 j5 js5 N5 y5 m5 ⊢
      try dsimp only
      ztailQT
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_tc_ok]
      exact (WP.spec_ok _).2 ⟨h4, y4, m4, fun v hv => by cases hv⟩
  · exact ⟨h, hD, hX, hI, hIs, hN, hY, hm⟩

set_option maxHeartbeats 4000000 in
/-- **`finalise_slot_immediate.zqGT` with a context field `M`** (gen 49, `LoopMC` at `C := JV s0`). -/
theorem cdt.finalise_slot_immediate.zqGTMC (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hK : FinKT st ar (L.ksb s0) Pt Ty K) (hTy : TyK st (L.ksb s0) Pt Ty)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x I Is : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st K Vc D Scs Fp I Is s) (hX : XQ st K Vc D Scs Fp I Is x s) (hI : L.idleW s = I)
    (hIs : L.mem s (scA I) = Is) (hN : IrqN st (L.ksb s0) s) (hY : Ty s)
    {M : S → Prop} (hM : LoopMC st ar OS D (JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0) M) (hm : M s) :
    cdt.finalise_slot_immediate st ar s a x ⦃ r =>
      JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧ Ty r.2.1 ∧ M r.2.1 ∧ ∀ v, r.1 = .Ok v → ClOK v.cleanup ⦄ :=
  cdt.finalise_slot_immediate.zqGTMZ (a := a) hP hO hA hV hDO hDC hR hK hTy hW hIO hap h hx hxI hD hX hI hIs hN hY (hM.toZ _) hm

set_option maxHeartbeats 4000000 in
/-- **`finalise_slot_immediate.zqGT` with a loop-invariant field `M`** (gen 48, `LoopM`). -/
theorem cdt.finalise_slot_immediate.zqGTM (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hK : FinKT st ar (L.ksb s0) Pt Ty K) (hTy : TyK st (L.ksb s0) Pt Ty)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x I Is : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st K Vc D Scs Fp I Is s) (hX : XQ st K Vc D Scs Fp I Is x s) (hI : L.idleW s = I)
    (hIs : L.mem s (scA I) = Is) (hN : IrqN st (L.ksb s0) s) (hY : Ty s)
    {M : S → Prop} (hM : LoopM st ar OS D M) (hm : M s) :
    cdt.finalise_slot_immediate st ar s a x ⦃ r =>
      JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧ Ty r.2.1 ∧ M r.2.1 ∧ ∀ v, r.1 = .Ok v → ClOK v.cleanup ⦄ :=
  cdt.finalise_slot_immediate.zqGTMC (a := a) hP hO hA hV hDO hDC hR hK hTy hW hIO hap h hx hxI hD hX hI hIs hN hY (hM.toC _) hm

set_option maxHeartbeats 4000000 in
/-- **`finalise_slot_immediate` of a slot of `OS` whose cap is `ZQ` over a domain `D` of `ZQ` caps**: `JV` to
`JV`, `Ty` kept (gen 41), a `ClOK` cleanup. -/
theorem cdt.finalise_slot_immediate.zqGT (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hK : FinKT st ar (L.ksb s0) Pt Ty K) (hTy : TyK st (L.ksb s0) Pt Ty)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x I Is : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st K Vc D Scs Fp I Is s) (hX : XQ st K Vc D Scs Fp I Is x s) (hI : L.idleW s = I)
    (hIs : L.mem s (scA I) = Is) (hN : IrqN st (L.ksb s0) s) (hY : Ty s) :
    cdt.finalise_slot_immediate st ar s a x ⦃ r =>
      JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧ Ty r.2.1 ∧ ∀ v, r.1 = .Ok v → ClOK v.cleanup ⦄ :=
  WP.spec_mono (cdt.finalise_slot_immediate.zqGTM (a := a) hP hO hA hV hDO hDC hR hK hTy hW hIO hap h hx hxI hD hX hI
    hIs hN hY (LoopM.triv hP) trivial) fun _ ⟨a1, a2, _, a3⟩ => ⟨a1, a2, a3⟩

/-- Gen 39's statement (a corollary of `zqGT`). -/
theorem cdt.finalise_slot_immediate.zqG (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hK : FinKT st ar (L.ksb s0) Pt Ty K) (hTy : TyK st (L.ksb s0) Pt Ty)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x I Is : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st K Vc D Scs Fp I Is s) (hX : XQ st K Vc D Scs Fp I Is x s) (hI : L.idleW s = I)
    (hIs : L.mem s (scA I) = Is) (hN : IrqN st (L.ksb s0) s) (hY : Ty s) :
    cdt.finalise_slot_immediate st ar s a x ⦃ r =>
      JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧ ∀ v, r.1 = .Ok v → ClOK v.cleanup ⦄ :=
  WP.spec_mono (cdt.finalise_slot_immediate.zqGT (a := a) hP hO hA hV hDO hDC hR hK hTy hW hIO hap h hx hxI hD hX hI
    hIs hN hY) fun _ h => ⟨h.1, h.2.2⟩

/-! ## The exposed deletion -/

set_option maxHeartbeats 4000000 in
/-- **`cdt.delete.zqIGT` with a field `M` seeing the finalisation** (gen 50, `LoopMZ` at `C := JV s0`, `X := XQF`). -/
theorem cdt.delete.zqIGTMZ (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hK : FinKT st ar (L.ksb s0) Pt Ty K) (hTy : TyK st (L.ksb s0) Pt Ty)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x I Is : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st K Vc D Scs Fp I Is s) (hX : XQ st K Vc D Scs Fp I Is x s) (hI : L.idleW s = I)
    (hIs : L.mem s (scA I) = Is) (hN : IrqN st (L.ksb s0) s) (hY : Ty s)
    {M : S → Prop} {Zr : S → U64 → U64 → U64 → Prop}
    (hM : LoopMZ st ar OS D (JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0) (XQF st K Vc D Scs Fp Ty (L.ksb s0)) Zr M) (hm : M s) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧ Ty r.2.1 ∧ M r.2.1 ⦄ := by
  unfold cdt.delete
  simp only [↓reduceIte]
  refine WP.spec_bind (cdt.finalise_slot_immediate.zqGTMZ (a := a) hP hO hA hV hDO hDC hR hK hTy hW hIO hap h hx hxI
    hD hX hI hIs hN hY hM hm) ?_
  rintro ⟨r, s1, a1⟩ ⟨h1, y1, m1, hv1⟩
  try simp only [uncurry_apply_pair] at h1 y1 m1 hv1 ⊢
  rcases r with v | e
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    refine WP.spec_bind (WP.spec_and (WP.spec_and (cdt.empty_slot.zs hP hO hV h1 hx (hv1 v rfl) hap)
      (cdt.empty_slot.vk hP hO hR h1 hx (hv1 v rfl) h1.ksb)) (hM.emp s1 a1 x _ h1 m1 hx (hv1 v rfl))) ?_
    rintro ⟨s2, a2⟩ ⟨⟨h2, v2⟩, m2⟩
    try simp only [uncurry_apply_pair] at h2 v2 m2 ⊢
    exact (WP.spec_ok _).2 ⟨h2.1, hTy _ _ y1 v2, m2⟩
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 ⟨h1, y1, m1⟩

set_option maxHeartbeats 4000000 in
/-- **`cdt.delete.zqIGT` with a context field `M`** (gen 49, `LoopMC` at `C := JV s0`). -/
theorem cdt.delete.zqIGTMC (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hK : FinKT st ar (L.ksb s0) Pt Ty K) (hTy : TyK st (L.ksb s0) Pt Ty)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x I Is : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st K Vc D Scs Fp I Is s) (hX : XQ st K Vc D Scs Fp I Is x s) (hI : L.idleW s = I)
    (hIs : L.mem s (scA I) = Is) (hN : IrqN st (L.ksb s0) s) (hY : Ty s)
    {M : S → Prop} (hM : LoopMC st ar OS D (JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0) M) (hm : M s) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧ Ty r.2.1 ∧ M r.2.1 ⦄ :=
  cdt.delete.zqIGTMZ (a := a) hP hO hA hV hDO hDC hR hK hTy hW hIO hap h hx hxI hD hX hI hIs hN hY (hM.toZ _) hm

set_option maxHeartbeats 4000000 in
/-- **`cdt.delete.zqIGT` with a loop-invariant field `M`** (gen 48, `LoopM`). -/
theorem cdt.delete.zqIGTM (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hK : FinKT st ar (L.ksb s0) Pt Ty K) (hTy : TyK st (L.ksb s0) Pt Ty)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x I Is : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st K Vc D Scs Fp I Is s) (hX : XQ st K Vc D Scs Fp I Is x s) (hI : L.idleW s = I)
    (hIs : L.mem s (scA I) = Is) (hN : IrqN st (L.ksb s0) s) (hY : Ty s)
    {M : S → Prop} (hM : LoopM st ar OS D M) (hm : M s) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧ Ty r.2.1 ∧ M r.2.1 ⦄ :=
  cdt.delete.zqIGTMC (a := a) hP hO hA hV hDO hDC hR hK hTy hW hIO hap h hx hxI hD hX hI hIs hN hY (hM.toC _) hm

set_option maxHeartbeats 4000000 in
/-- **The exposed `cdt.delete` of a slot of `OS` whose cap is `ZQ` over a domain of `ZQ` caps keeps `JV`** (ghost
`I`, `Is`: the start state's idle word and idle `SC` field). -/
theorem cdt.delete.zqIGT (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hK : FinKT st ar (L.ksb s0) Pt Ty K) (hTy : TyK st (L.ksb s0) Pt Ty)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x I Is : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st K Vc D Scs Fp I Is s) (hX : XQ st K Vc D Scs Fp I Is x s) (hI : L.idleW s = I)
    (hIs : L.mem s (scA I) = Is) (hN : IrqN st (L.ksb s0) s) (hY : Ty s) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧ Ty r.2.1 ⦄ :=
  WP.spec_mono (cdt.delete.zqIGTM hP hO hA hV hDO hDC hR hK hTy hW hIO hap h hx hxI hD hX hI hIs hN hY
    (LoopM.triv hP) trivial) fun _ ⟨a1, a2, _⟩ => ⟨a1, a2⟩

/-- Gen 39's statement (a corollary of `zqIGT`). -/
theorem cdt.delete.zqIG (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hK : FinKT st ar (L.ksb s0) Pt Ty K) (hTy : TyK st (L.ksb s0) Pt Ty)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x I Is : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st K Vc D Scs Fp I Is s) (hX : XQ st K Vc D Scs Fp I Is x s) (hI : L.idleW s = I)
    (hIs : L.mem s (scA I) = Is) (hN : IrqN st (L.ksb s0) s) (hY : Ty s) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ :=
  WP.spec_mono (cdt.delete.zqIGT hP hO hA hV hDO hDC hR hK hTy hW hIO hap h hx hxI hD hX hI hIs hN hY)
    fun _ h => h.1

/-- **`cdt.delete.zqI` at the start state's idle word and idle `SC` field.** -/
theorem cdt.delete.zqG (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hK : FinKT st ar (L.ksb s0) Pt Ty K) (hTy : TyK st (L.ksb s0) Pt Ty)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st K Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) s)
    (hX : XQ st K Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) x s) (hN : IrqN st (L.ksb s0) s)
    (hY : Ty s) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ :=
  cdt.delete.zqIG hP hO hA hV hDO hDC hR hK hTy hW hIO hap h hx hxI hD hX rfl rfl hN hY

/-- **The thread kind over a domain of `ZQ` caps**: the exposed `cdt.delete` of `Thread p` (`p` not the idle
thread and no frame position, its seven TCB slots in `D`), the slots of `D` holding gen 36's `ZS` caps whose objects
are no frame positions, or — at frame positions — caps of the class `K`, keeps `JV`. -/
theorem cdt.delete.threadQG (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hK : FinKT st ar (L.ksb s0) Pt Ty K) (hTy : TyK st (L.ksb s0) Pt Ty)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x p : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st K Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) s) (hN : IrqN st (L.ksb s0) s)
    (hY : Ty s)
    (hc : obj.Slot.cap st x s = ok (.Thread p)) (hid : p ≠ L.idleW s) (hpF : p ∉ Fp)
    (hcov : ∀ i : U64, i.val < 7 → slotIdx p i ∈ D) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ :=
  cdt.delete.zqG hP hO hA hV hDO hDC hR hK hTy hW hIO hap h hx hxI hD (fun c hc' => by
    rw [hc] at hc'; rw [← okinj hc']
    refine Or.inl ⟨Or.inl (Or.inr (Or.inl ⟨p, rfl, hid, hcov⟩)), ?_⟩
    rintro p' (⟨r, g, b, e⟩ | e | ⟨t', n', e⟩)
    · cases e
    · cases e; exact hpF
    · cases e) hN hY

/-! ## Gen 38's statements over `FinK` / `TyZ` (corollaries of the generic forms) -/

theorem cdt.finalise_slot_deferred.zq (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hK : FinK st ar (L.ksb s0) Pt Ty K) (hTy : TyZ st (L.ksb s0) Pt Ty)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) {a : A} {y I Is : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hy : y ∈ D) (hD : DomQ st K Vc D Scs Fp I Is s)
    (hI : L.idleW s = I) (hIs : L.mem s (scA I) = Is) (hN : IrqN st (L.ksb s0) s)
    (hY : Ty s) :
    cdt.finalise_slot_deferred st ar s a y ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      DomQ st K Vc D Scs Fp I Is r.2.1 ∧ OKD st OS D (L.ksb s0) s r.2.1 ∧ L.idleW r.2.1 = I ∧
      L.mem r.2.1 (scA I) = Is ∧ Ty r.2.1 ∧ ∀ v, r.1 = .Ok v → ClOK v.cleanup ⦄ :=
  cdt.finalise_slot_deferred.zqG (a := a) hP hO hA hV hDO hDC hR (hK.toT hTy) hTy.toK hW hIO h hy hD hI hIs hN hY

theorem cdt.delete_deferred.zq (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hK : FinK st ar (L.ksb s0) Pt Ty K) (hTy : TyZ st (L.ksb s0) Pt Ty)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {y I Is : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hy : y ∈ D) (hD : DomQ st K Vc D Scs Fp I Is s)
    (hI : L.idleW s = I) (hIs : L.mem s (scA I) = Is) (hN : IrqN st (L.ksb s0) s)
    (hY : Ty s) :
    cdt.delete_deferred st ar s a y ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      DomQ st K Vc D Scs Fp I Is r.2.1 ∧ OKD st OS D (L.ksb s0) s r.2.1 ∧ L.idleW r.2.1 = I ∧
      L.mem r.2.1 (scA I) = Is ∧ Ty r.2.1 ⦄ :=
  cdt.delete_deferred.zqG (a := a) hP hO hA hV hDO hDC hR (hK.toT hTy) hTy.toK hW hIO hap h hy hD hI hIs hN hY

theorem cdt.finalise_slot_immediate.zq (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hK : FinK st ar (L.ksb s0) Pt Ty K) (hTy : TyZ st (L.ksb s0) Pt Ty)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x I Is : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st K Vc D Scs Fp I Is s) (hX : XQ st K Vc D Scs Fp I Is x s) (hI : L.idleW s = I)
    (hIs : L.mem s (scA I) = Is) (hN : IrqN st (L.ksb s0) s) (hY : Ty s) :
    cdt.finalise_slot_immediate st ar s a x ⦃ r =>
      JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧ ∀ v, r.1 = .Ok v → ClOK v.cleanup ⦄ :=
  cdt.finalise_slot_immediate.zqG (a := a) hP hO hA hV hDO hDC hR (hK.toT hTy) hTy.toK hW hIO hap h hx hxI hD hX hI hIs hN hY

theorem cdt.delete.zqI (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hK : FinK st ar (L.ksb s0) Pt Ty K) (hTy : TyZ st (L.ksb s0) Pt Ty)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x I Is : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st K Vc D Scs Fp I Is s) (hX : XQ st K Vc D Scs Fp I Is x s) (hI : L.idleW s = I)
    (hIs : L.mem s (scA I) = Is) (hN : IrqN st (L.ksb s0) s) (hY : Ty s) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ :=
  cdt.delete.zqIG (a := a) hP hO hA hV hDO hDC hR (hK.toT hTy) hTy.toK hW hIO hap h hx hxI hD hX hI hIs hN hY

theorem cdt.delete.zq (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hK : FinK st ar (L.ksb s0) Pt Ty K) (hTy : TyZ st (L.ksb s0) Pt Ty)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st K Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) s)
    (hX : XQ st K Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) x s) (hN : IrqN st (L.ksb s0) s)
    (hY : Ty s) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ :=
  cdt.delete.zqG (a := a) hP hO hA hV hDO hDC hR (hK.toT hTy) hTy.toK hW hIO hap h hx hxI hD hX hN hY

theorem cdt.delete.threadQ (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hK : FinK st ar (L.ksb s0) Pt Ty K) (hTy : TyZ st (L.ksb s0) Pt Ty)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x p : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st K Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) s) (hN : IrqN st (L.ksb s0) s)
    (hY : Ty s)
    (hc : obj.Slot.cap st x s = ok (.Thread p)) (hid : p ≠ L.idleW s) (hpF : p ∉ Fp)
    (hcov : ∀ i : U64, i.val < 7 → slotIdx p i ∈ D) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ :=
  cdt.delete.threadQG (a := a) hP hO hA hV hDO hDC hR (hK.toT hTy) hTy.toK hW hIO hap h hx hxI hD hN hY hc hid hpF hcov

end zq

end ST
end R
end W7

end

end Fl4ProofsA64.P1
