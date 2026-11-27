/-
P1 (aarch64): **the VCPU kind's finalisation proved** — taken out of the `arch` gap (`FinGapsAt4.arch`) and out of
[J] `FinRvRest4` — on a copy of QueueDelVsB's chain (namespace `W7.R.A5.B.V`).

`vcpu::finalise` (vcpu.rs:333–336, called by `finalise_cap_object`'s `Cap::Vcpu` arm, objects.rs:265, when the
cap is final) is `unbind(vc)` and `vcpu_flush(vc)` (an `Arch` call, no store write). `vcpu.unbind.ub`
(QueueUnbindB) proves `unbind` from `Cur0` to `UbF` (so `Cur0` and [J] `RunVcpuInv` kept), given that `vc` is a
VCPU object (`VcObj`) along the step. The finalised cap was read from a cap slot, so that fact is a slot
placement, carried with the cap like `FrMapOK`:

* `VcCap s0 c`: if `c = .Vcpu v` then `VcObj s' v` at every `Fr0 ∧ BXI` state `s'` from `s0`; `FrVc s0 c` =
  `FrMapOK c ∧ VcCap s0 c` (the predicate the deletion gaps carry from the slot read to the finaliser).
* **[P] `vco`** (field of `V.DelPlaceAt` = `B.DelPlaceAt` + `vco`): a cap read from a cap slot at a `Fr0 ∧ BXI`
  state satisfies `VcCap s0`. Source (crates/fl4-core/src/arch/aarch64): a `Cap::Vcpu { ptr }` is made only by
  the retype of an `ArmVcpu` object (objects.rs:51–53, `base` the new object; `vcpu::init`, vcpu.rs:157–160,
  zeroes `TCB` / `OWNER_CPU`), copied / moved / derived with the same `ptr` (objects.rs:123), so `ptr` is a VCPU
  heap object (`.other 12`: its words in `Ω \ Sg`, as [P] `VcpuW`); its `TCB` word is written only by
  `decode_set_tcb` (vcpu.rs:388, a thread cap's TCB) and `unbind` / `init` (0), its `RUN_CALLER` word only by
  `decode_run` (861, the current thread) and `cancel_run` / `complete_run` / `unbind` (0) — the sources of
  QueueUnbindB's `VcPl.vcb` and QueueDecVcpuB's [P] `VcpuObjA` (the same `VcObj` along a decode, there for the
  invoked cap, here for a slot cap). Caveat as every `DelPlaceAt` field: stated at every `Fr0 ∧ BXI` state.
* `FinRvRestKind5` / **[J] `FinRvRest5`** (= [J] `FinRvRest4` without the VCPU kind: Stage-2 and device frames),
  `FinGapsAt5` (`arch` over Stage-2 / device frames, `rv : FinRvRest5`), `FinGaps5`, `FinGapsAt5.of4` /
  `FinGaps5.of4` (strictly weaker than `FinGapsAt4` / `FinGaps4`).
* `vcpu.finalise.ub`, **`fin_vcpuV`** (the VCPU kind, `Cur0R` to `Cur0R`, from `B.DelPlaceAt.vc` and `VcCap`),
  `FinRvKindV`, `finRvAtV_of` (every `FinRvKind` but the VCPU's, from the placement and `FinRvRest5`), `ofC0V`.
* By script (`handoff/a64-wip/gen27/gen_delvsv.py`; cuts QueueDelVsB 67–342, 376–809, 811–880): `V.DelGapsAt`
  (`frm` / `fin` over `FrVc s0`), `V.DelGaps`, the chain `cdt.finalise_slot_immediate.cur0` … `decGap_cnode2`,
  `fin_vs` … `finRvRest_of3`, **`V.fin_all`** (the VCPU arm by `fin_vcpuV`, `arch` for Stage-2 / device frames
  only, `G : FinGapsAt5`), `V.delGaps_of`, `V.delGaps_of_gaps5`, **`V.decGap_cnode_rv5`**; `V.DelPlaceAt.toDelPlaceAt`,
  `V.DelPlace.toB` (for the consumers that read no `vco`).

Named premises: **[P] `vco`** (new), [J] `FinRvRest5` (narrows [J] `FinRvRest4`); the others as QueueDelVsB's.
No existing statement changed.
-/
import Fl4ProofsA64.P1.QueueDelVsB
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}

namespace W7
namespace R
namespace A5
namespace B
namespace V

/-- A VCPU cap names a VCPU object at every `Fr0 ∧ BXI` state from `s0` (module docstring). -/
def VcCap (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64)
    (Z : U64 → Nat) (s0 : S) (c : capability.Cap) : Prop :=
  ∀ v, c = .Vcpu v → ∀ (Ac' : Set U64) (s' : S), Fr0 st T Cs Ω H Sg Scs Z s0 s' →
    BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' s' → VcObj st T Ω Sg s' v

/-- The slot-read facts the finaliser takes: `FrMapOK` and `VcCap`. -/
def FrVc (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64)
    (Z : U64 → Nat) (s0 : S) (c : capability.Cap) : Prop :=
  FrMapOK c ∧ VcCap st T Cs Ω H Sg Rp Scs Nt Z s0 c

/-- The kinds whose `RunVcpuInv` preservation stays named ([J] `FinRvRest5`): Stage-2 and device frames. -/
def FinRvRestKind5 (c : capability.Cap) : Prop :=
  (∃ x1 x2 x3 x4 x5, c = .Ept x1 x2 x3 x4 x5) ∨ (∃ x1 x2 x3 x4 x5 x6 x7, c = .Frame x1 x2 x3 x4 x5 true x6 x7)

/-- **[J] (a64) `FinRvRest5`**: [J] `FinRvRest4` without the VCPU kind (proved: `fin_vcpuV`). -/
def FinRvRest5 (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A) (T Cs Ω : Set U64)
    (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (s0 : S) : Prop :=
  ∀ (Ac : Set U64) (s : S) (a : A) (c : capability.Cap) (fin : Bool),
    Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s → RunVcpuInv st T s → DelCapOK T Ω Sg H Rp Nt c →
    Fl4ProofsA64.P1.FinPl st Scs s c →
    FinRvRestKind5 c → objects.finalise_cap st ar s a c fin false ⦃ r => RunVcpuInv st T r.2.1 ⦄

/-- The finalisation gaps without the VCPU kind: the `arch` gap of the Stage-2 and device-frame kinds, and
[J] `FinRvRest5`. -/
structure FinGapsAt5 (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (s0 : S) : Prop where
  arch : W7.FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z (fun c => (∃ x1 x2 x3 x4 x5, c = .Ept x1 x2 x3 x4 x5) ∨
    (∃ x1 x2 x3 x4 x5 x6 x7, c = .Frame x1 x2 x3 x4 x5 true x6 x7)) s0
  /-- **[J] (a64)** `FinRvRest5` (above). -/
  rv : FinRvRest5 st ar T Cs Ω H Sg Rp Scs Nt Z s0

/-- `FinGapsAt5` at every decode start reached from a `P3Ok` entry. -/
def FinGaps5 (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (P3Ok : S → Prop) : Prop :=
  ∀ s0, EntAt st P3Ok s0 → FinGapsAt5 st ar T Cs Ω H Sg Rp Scs Nt Z s0

/-- `FinGapsAt5` is weaker than `FinGapsAt4`. -/
theorem FinGapsAt5.of4 {A : Type _} {ar : machine.Arch A} {s0 : S}
    (G : W7.R.FinGapsAt4 st ar T Cs Ω H Sg Rp Scs Nt Z s0) : FinGapsAt5 st ar T Cs Ω H Sg Rp Scs Nt Z s0 :=
  ⟨fun Ac s a c fin h hc hpl hk => G.arch Ac s a c fin h hc hpl (Or.inr hk),
    fun Ac s a c fin h hRV hc hpl hk => G.rv Ac s a c fin h hRV hc hpl (Or.inr hk)⟩

theorem FinGaps5.of4 {A : Type _} {ar : machine.Arch A}
    (G : W7.R.FinGaps4 st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok) : FinGaps5 st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok :=
  fun s0 hE => FinGapsAt5.of4 (G s0 hE)

/-- **`vcpu::finalise`** (`unbind`, then the `Arch` flush) from a `Cur0` state, `vc` a VCPU object along it. -/
theorem vcpu.finalise.ub {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s0 s : S}
    (Pl : VcPl st T Cs Ω H Sg Rp Scs Nt Z s0) (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (a : A) (v : U64)
    (hV : ∀ s' : S, Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' → BndK st T s s' → VcObj st T Ω Sg s' v) :
    vcpu.finalise st ar s a v ⦃ s' _ => UbF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s s' ⦄ := by
  unfold vcpu.finalise
  refine WP.spec_bind (vcpu.unbind.ub hA Pl h a v hV) ?_
  rintro ⟨s1, a1⟩ F1
  try simp only [WP.uncurry'_pair, uncurry_apply_pair] at F1 ⊢
  refine WP.spec_bind (hA.vcpu_flush_spec a1 v) fun a2 _ => ?_
  exact (WP.spec_ok _).2 F1

/-- **`R.DelGapsAt` with the frame-address and VCPU facts** (`frm`: `FrVc`, read with the cap from its slot) and the finalisation
of caps that satisfy it (`fin`); otherwise `W7.R.DelGapsAt`'s fields. -/
structure DelGapsAt (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (s0 : S) : Prop where
  cap : ∀ (Ac : Set U64) (s : S) (x : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    SlotW T Ω Sg x → obj.Slot.cap st x s ⦃ c => DelCapOK T Ω Sg H Rp Nt c ∧ FinPl st Scs s c ⦄
  frm : ∀ (Ac : Set U64) (s : S) (x : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    SlotW T Ω Sg x → obj.Slot.cap st x s ⦃ c => FrVc st T Cs Ω H Sg Rp Scs Nt Z s0 c ⦄
  fin : ∀ (Ac : Set U64) (s : S) (a : A) (c : capability.Cap) (fin : Bool),
    Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s → DelCapOK T Ω Sg H Rp Nt c → FinPl st Scs s c → FrVc st T Cs Ω H Sg Rp Scs Nt Z s0 c →
    objects.finalise_cap st ar s a c fin false ⦃ r => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧
      DelCapOK T Ω Sg H Rp Nt r.1.1 ∧ DelCapOK T Ω Sg H Rp Nt r.1.2 ⦄
  deferred : ∀ (Ac : Set U64) (s : S) (a : A) (x : U64), Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s →
    SlotW T Ω Sg x → cdt.delete_deferred st ar s a x ⦃ r => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ⦄
  empty : ∀ (Ac : Set U64) (s : S) (a : A) (x : U64) (c : capability.Cap),
    Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s → SlotW T Ω Sg x → DelCapOK T Ω Sg H Rp Nt c →
    cdt.empty_slot st ar s a x c ⦃ r => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 ⦄
  next : ∀ (Ac : Set U64) (s : S) (x : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    SlotW T Ω Sg x → obj.Slot.next st x s ⦃ n => n = 0#u64 ∨ SlotW T Ω Sg n ⦄

/-- The deletion gaps at every decode start reached from a `P3Ok` entry. -/
def DelGaps (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (P3Ok : S → Prop) : Prop :=
  ∀ s0, EntAt st P3Ok s0 → DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0

set_option hygiene false in
/-- The preemption-point tail of a loop round (`Cur0` at `s2`). -/
local macro "pptail" : tactic => `(tactic| (
  refine WP.spec_bind (sched.preemption_point.cur0 hA h2) ?_
  rintro ⟨rr, s3, a3⟩ h3
  try simp only [WP.uncurry'_pair] at h3 ⊢
  try simp only [uncurry_apply_pair] at h3 ⊢
  rcases rr with _ | ee
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok]
    refine (WP.spec_ok _).2 ⟨h3, ?_⟩
    show fuel1.val < fuel.val
    omega
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    first | exact (WP.spec_ok _).2 h3 | exact h3 | exact (WP.spec_ok _).2 ⟨h3, by intro v hv; simp_all⟩ |
      exact ⟨h3, by intro v hv; simp_all⟩))

set_option maxHeartbeats 4000000 in
theorem cdt.finalise_slot_immediate.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {s0 s : S} (G : DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0) {a : A} {x : U64}
    (h : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : SlotW T Ω Sg x) :
    cdt.finalise_slot_immediate st ar s a x ⦃ r => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧
      ∀ v, r.1 = .Ok v → DelCapOK T Ω Sg H Rp Nt v.cleanup ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.finalise_slot_immediate cdt.finalise_slot_immediate_loop
  apply loop.spec_decr_nat (measure := fun y => y.2.2.val)
    (inv := fun y => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 y.1)
  · rintro ⟨s1, a1, fuel⟩ h1
    simp only at h1
    dsimp only
    unfold cdt.finalise_slot_immediate_loop.body
    split
    swap
    · exact (WP.spec_ok _).2 ⟨h1, by intro v hv; simp_all⟩
    rename_i hf
    step as ⟨fuel1, hf1⟩
    obtain ⟨Acx, hbx⟩ := h1.bxi
    refine WP.spec_bind (WP.spec_and (G.cap Acx s1 x h1.fr hbx hx) (G.frm Acx s1 x h1.fr hbx hx))
      fun c ⟨⟨hc, hpl⟩, hfr⟩ => ?_
    refine WP.spec_bind (P0.capability.Cap.is_null.p0 c) fun bn _ => ?_
    split
    · exact (WP.spec_ok _).2 ⟨h1, fun v hv => by cases hv; exact DelCapOK.null⟩
    refine WP.spec_bind (P0.cdt.is_final_capability_with_cap.p0 st s1 x c hS) fun fin _ => ?_
    refine WP.spec_bind (G.fin Ac s1 a1 c fin h1 hc hpl hfr) ?_
    rintro ⟨⟨rem, cl⟩, s2, a2⟩ ⟨h2', hrem, hcl⟩
    try simp only [uncurry_apply_pair, WP.uncurry'_pair]
    refine WP.spec_bind (cdt.cap_removable.zombie rem x) fun br hbr => ?_
    split
    · exact (WP.spec_ok _).2 ⟨h2', fun v hv => by cases hv; exact hcl⟩
    rename_i hbr0
    have hbr' := hbr (by simpa using hbr0)
    refine WP.spec_bind (obj.Slot.set_cap.capw (c := rem) (s := s2) hx) fun s2' w2 => ?_
    have h2 := h2'.capw7 w2 fun _ hb => hb
    have hf' : 0 < fuel.val := by simpa using hf
    split
    all_goals try pptail
    -- the zombie: the deferred delete of its last slot, then the count
    simp only [lift, bind_ok]
    rename_i zp zt zn
    have hen := zombie_last hrem (hbr' zp zt zn rfl)
    unfold obj.Slot.index
    simp only [lift, bind_ok, cte_size]
    refine WP.spec_bind (G.deferred Ac s2' a2 _ h2 hen) ?_
    rintro ⟨r, s3, a3⟩ h3
    try simp only [uncurry_apply_pair] at h3 ⊢
    rcases r with _ | e
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      refine WP.spec_bind (P0.obj.Slot.cap.p0 st x s3 hS) fun c _ => ?_
      have SC : ∀ c', obj.Slot.set_cap st x s3 c' ⦃ s' => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := fun c' =>
        WP.spec_mono (obj.Slot.set_cap.capw hx) fun s' w => h3.capw7 w fun _ hb => hb
      refine WP.spec_bind (Pₘ := fun r : S × A => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1) ?_ ?_
      · split
        all_goals try exact (WP.spec_ok _).2 h3
        split
        · split
          · refine WP.spec_bind (Pₘ := fun s' => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s') ?_
              fun s' h' => (WP.spec_ok _).2 h'
            split
            · try simp only [lift, bind_ok]
              exact SC _
            · exact (WP.spec_ok _).2 h3
          · exact (WP.spec_ok _).2 h3
        · exact (WP.spec_ok _).2 h3
      · rintro ⟨s4, a4⟩ h2
        try simp only [uncurry_apply_pair] at h2 ⊢
        pptail
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_tc_ok]
      exact (WP.spec_ok _).2 ⟨h3, by intro v hv; simp_all⟩
  · exact h

/-- `cdt.delete` (exposed) of a cap slot. -/
theorem cdt.delete.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {s0 s : S} (G : DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0) {a : A} {x : U64}
    (h : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : SlotW T Ω Sg x) :
    cdt.delete st ar s a x true ⦃ r => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ⦄ := by
  unfold cdt.delete
  simp only [↓reduceIte]
  refine WP.spec_bind (cdt.finalise_slot_immediate.cur0 hA G h hx) ?_
  rintro ⟨r, s1, a1⟩ ⟨h1, hv1⟩
  try simp only [uncurry_apply_pair] at h1 hv1 ⊢
  rcases r with v | e
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    refine WP.spec_bind (G.empty Ac s1 a1 x _ h1 hx (hv1 v rfl)) ?_
    rintro ⟨s2, a2⟩ h2
    try simp only [uncurry_apply_pair] at h2 ⊢
    exact (WP.spec_ok _).2 h2
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 h1

set_option maxHeartbeats 2000000 in
/-- `cdt.revoke` of a cap slot. -/
theorem cdt.revoke.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {s0 s : S} (G : DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0) {a : A} {x : U64}
    (h : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : SlotW T Ω Sg x) :
    cdt.revoke st ar s a x ⦃ r => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.revoke cdt.revoke_loop
  apply loop.spec_decr_nat (measure := fun y => y.2.2.val)
    (inv := fun y => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 y.1)
  · rintro ⟨s1, a1, fuel⟩ h1
    simp only at h1
    dsimp only
    unfold cdt.revoke_loop.body
    split
    swap
    · exact (WP.spec_ok _).2 h1
    rename_i hf
    have hf' : 0 < fuel.val := by simpa using hf
    step as ⟨fuel1, hf1⟩
    have h1' := h1
    obtain ⟨-, Acx, hbx, -, -, -, -, -⟩ := h1'.1
    refine WP.spec_bind (G.next Acx s1 x h1.fr hbx hx) fun nx hnx => ?_
    simp only [obj.Slot.is_null, bind_ok]
    split
    · exact (WP.spec_ok _).2 h1
    rename_i hn0
    have hnW : SlotW T Ω Sg nx := hnx.resolve_left (by simpa using hn0)
    refine WP.spec_bind (P0.cdt.is_mdb_parent_of.p0 st s1 x nx hS) fun bp _ => ?_
    split
    · refine WP.spec_bind (cdt.delete.cur0 hA G h1 hnW) ?_
      rintro ⟨r, s2', a2⟩ h2
      try simp only [uncurry_apply_pair] at h2 ⊢
      rcases r with _ | e
      · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        refine WP.spec_bind (sched.preemption_point.cur0 hA h2) ?_
        rintro ⟨rr, s3, a3⟩ h3
        try simp only [uncurry_apply_pair] at h3 ⊢
        rcases rr with _ | ee
        · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok]
          refine (WP.spec_ok _).2 ⟨h3, ?_⟩
          show fuel1.val < fuel.val
          omega
        · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
            bind_tc_ok]
          exact (WP.spec_ok _).2 h3
      · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
          bind_tc_ok]
        exact (WP.spec_ok _).2 h2
    · exact (WP.spec_ok _).2 h1
  · exact h

/-- **CNode `Delete`** from `DelGaps`. -/
theorem cnode_del {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {s : S} (G : DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s) {a : A} {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {x : U64}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hx : SlotW T Ω Sg x) :
    (do
      let s1 ← sched.set_thread_state st s (L.curW s) sched.TS_RESTART
      cdt.delete st ar s1 a x true) ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ :=
  WP.spec_bind (Cur0R.restart D) fun s1 h1 => WP.spec_mono (cdt.delete.cur0 hA G h1 hx) fun r hr => by
    obtain ⟨r', s', a'⟩ := r; exact hr.post

/-- **CNode `Revoke`** from `DelGaps`. -/
theorem cnode_rev {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {s : S} (G : DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s) {a : A} {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {x : U64}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hx : SlotW T Ω Sg x) :
    (do
      let s1 ← sched.set_thread_state st s (L.curW s) sched.TS_RESTART
      cdt.revoke st ar s1 a x) ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ :=
  WP.spec_bind (Cur0R.restart D) fun s1 h1 => WP.spec_mono (cdt.revoke.cur0 hA G h1 hx) fun r hr => by
    obtain ⟨r', s', a'⟩ := r; exact hr.post

set_option hygiene false in
local macro "errleaf2" : tactic => `(tactic| first
  | exact D.err _
  | exact (WP.spec_ok _).2 (D.err _)
  | (simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, error.illegal, error.truncated, cnode.missing_source]
     first | exact D.err _ | exact (WP.spec_ok _).2 (D.err _)))

set_option maxHeartbeats 4000000 in
/-- **`cnode.decode`**, Delete and Revoke included. -/
theorem cnode.decode.dec2 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (C : CdtHyps2 st T Cs Ω H Sg Rp Scs Nt Z P3Ok) {s : S} (G : DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s)
    {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) (lbl len buf : U64)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hE : EntAt st P3Ok s) (c : capability.Cap) :
    cnode.decode st ar s a lbl len c buf extra ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cnode.decode
  simp only [error.illegal, error.truncated, bind_ok]
  split
  · errleaf2
  split
  · errleaf2
  split
  · errleaf2
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have e : ct = L.curW s := ect
  subst e
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun idx _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun dep _ => ?_
  refine WP.spec_bind (WP.spec_and (C.tgt Ac s c idx dep hE D.bxi) (C.tgtW Ac s c idx dep hE D.bxi)) fun r hr => ?_
  rcases r with v | e
  swap
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    errleaf2
  have hv := hr.1 v rfl
  have hvW := slotW_to7 (hr.2 v rfl)
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  repeat' (first
    | exact (WP.spec_ok _).2 (D.err _)
    | exact lift2 (cnode.decode_copy.dec C.toCdtHyps lbl len buf v D hE hv)
    | exact lift2 (cnode.decode_cancel_badged_sends.dec C.toCdtHyps v D hE hv)
    | exact lift2 (cnode.decode_rotate.dec C.toCdtHyps len buf v D hE hv)
    | exact cnode_del hA G D hvW
    | exact cnode_rev hA G D hvW
    | split)

/-- **InvGaps' `cnode`, discharged** from `CdtHyps2` and `DelGaps`. -/
theorem decGap_cnode2 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (C : CdtHyps2 st T Cs Ω H Sg Rp Scs Nt Z P3Ok) (G : DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok) :
    DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .cnode := by
  intro Ac s a lbl len slot cap blk call don fp buf extra hf D _hslot hE
  cases cap <;> simp [capFam] at hf
  unfold syscall.decode_invocation
  step with sched.cur_thread.spec as ⟨ct, _⟩
  try dsimp only
  split
  · exact (WP.spec_ok _).2 (DecPost.keep D.bxi (by simp))
  · exact cnode.decode.dec2 hA C (G s hE) a lbl len buf D hE _




/-- **The deletion placements with the VCPU slot fact**: `B.DelPlaceAt` and **[P] `vco`** (module docstring). -/
structure DelPlaceAt (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (V : U64 → Prop) (s0 : S) : Prop
    extends W7.R.A5.B.DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0 where
  /-- **[P] (a64) `vco`**: a VCPU cap read from a cap slot names a VCPU object along the decode (`VcCap`). -/
  vco : ∀ (Ac : Set U64) (s : S) (x : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    SlotW T Ω Sg x → obj.Slot.cap st x s ⦃ c => VcCap st T Cs Ω H Sg Rp Scs Nt Z s0 c ⦄

/-- `DelPlaceAt` at every decode start reached from a `P3Ok` entry. -/
def DelPlace (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (V : U64 → Prop) (P3Ok : S → Prop) : Prop :=
  ∀ s0, EntAt st P3Ok s0 → DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0

theorem DelPlace.toB {V : U64 → Prop} (P : DelPlace st T Cs Ω H Sg Rp Scs Nt Z V P3Ok) :
    W7.R.A5.B.DelPlace st T Cs Ω H Sg Rp Scs Nt Z V P3Ok :=
  fun s0 hE => (P s0 hE).toDelPlaceAt

/-- The slot read of `frm` and `vco` together. -/
theorem DelPlaceAt.frmV {V : U64 → Prop} {s0 : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0)
    (Ac : Set U64) (s : S) (x : U64) (hf : Fr0 st T Cs Ω H Sg Scs Z s0 s) (hb : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hx : SlotW T Ω Sg x) : obj.Slot.cap st x s ⦃ c => FrVc st T Cs Ω H Sg Rp Scs Nt Z s0 c ⦄ :=
  WP.spec_mono (WP.spec_and (P.frm Ac s x hf hb hx) (P.vco Ac s x hf hb hx)) fun _ h => h


set_option maxHeartbeats 2000000 in
/-- **The VSpace kinds** (`W7.R.fin_vs`) from the root-restricted walks (`VsDelAt`) and, for a mapped frame,
its address (`FrMapOK`). -/
theorem fin_vs {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s0 s : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) (W : VsDelAt st ar T Cs Ω H Sg Rp Scs Nt Z V s0)
    {a : A} {c : capability.Cap} {fin : Bool}
    (h : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hfr : FrMapOK c)
    (hc : (∃ x y z w, c = .PageTable x y z w) ∨ (∃ x y z w m asid vaddr, c = .Frame x y z w m false asid vaddr) ∨
      (∃ x y z, c = .Pml4 x y z) ∨ (∃ x y, c = .AsidPool x y) ∨ (∃ x y z w, c = .PageDirectory x y z w) ∨
      (∃ x y z w, c = .Pdpt x y z w) ∨ (∃ x y z, c = .HighVSpace x y z)) :
    objects.finalise_cap st ar s a c fin false ⦃ r => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧
      DelCapOK T Ω Sg H Rp Nt r.1.1 ∧ DelCapOK T Ω Sg H Rp Nt r.1.2 ⦄ := by
  have hb := h.bxi
  obtain ⟨Ac', hb⟩ := hb
  have W' : ∀ (m : Result (S × A)), m ⦃ r => WritesIn st s r.1 V ⦄ →
      (do let (s1, a1) ← m; ok ((capability.Cap.Null, capability.Cap.Null), s1, a1)) ⦃ r =>
        Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧ DelCapOK T Ω Sg H Rp Nt r.1.1 ∧
        DelCapOK T Ω Sg H Rp Nt r.1.2 ⦄ := fun m hm =>
    WP.spec_bind hm fun r hr => by
      obtain ⟨s1, a1⟩ := r
      exact (WP.spec_ok _).2 ⟨h.vs P.vs hr, DelCapOK.null, DelCapOK.null⟩
  have K : (ok ((capability.Cap.Null, capability.Cap.Null), s, a) : Result _) ⦃ r =>
      Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧ DelCapOK T Ω Sg H Rp Nt r.1.1 ∧
      DelCapOK T Ω Sg H Rp Nt r.1.2 ⦄ := (WP.spec_ok _).2 ⟨h, DelCapOK.null, DelCapOK.null⟩
  have UPT : ∀ asid vaddr pt, vspace.unmap_page_table st ar s a asid vaddr pt ⦃ r => WritesIn st s r.1 V ⦄ :=
    fun asid vaddr pt => vspace.unmap_page_table.vsA hA s a asid vaddr pt P.vs
      (W.ptw Ac' s h.fr hb asid vaddr pt) (W.elw Ac' s h.fr hb a asid vaddr pt)
  rcases hc with ⟨x, y, z, w, rfl⟩ | ⟨x, y, z, w, m, asid, vaddr, rfl⟩ | ⟨x, y, z, rfl⟩ | ⟨x, y, rfl⟩ |
    ⟨x, y, z, w, rfl⟩ | ⟨x, y, z, w, rfl⟩ | ⟨x, y, z, rfl⟩
  · simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok]
    split
    · split
      · exact W' _ (UPT z w x)
      · exact K
    · exact K
  · simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok, Bool.false_eq_true, ↓reduceIte]
    apply WP.spec_bind (Pₘ := fun r => WritesIn st s r.1 V)
    · split
      · split
        · rename_i hm hz
          have hv : HiOK vaddr := hfr x y z w asid vaddr (by subst hm; rfl) (by simpa using hz)
          exact vspace.unmap_page.vsA hA s a y asid vaddr x P.vs (W.ptslot Ac' s h.fr hb asid vaddr hv)
        · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
      · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
    · rintro ⟨s1, a1⟩ hw
      cases fin <;> cases w <;> simp only [↓reduceIte, Bool.false_eq_true, uncurry_apply_pair]
      all_goals first
        | exact (WP.spec_ok _).2 ⟨h.vs P.vs hw, DelCapOK.null, DelCapOK.null⟩
        | exact WP.spec_bind (P0.objects.retire_dma_frame.p0 st ar s1 a1 x y L.total hA) fun _ _ =>
            (WP.spec_ok _).2 ⟨h.vs P.vs hw, DelCapOK.null, DelCapOK.null⟩
  · simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok]
    split
    · split
      · exact W' _ (vspace.delete_asid.vs hA s a z x P.vs fun i => P.pool Ac' s z i h.fr hb)
      · exact K
    · exact K
  · simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok]
    split
    · exact W' _ (vspace.delete_asid_pool.vs hA s a y x fun hi => P.aset Ac' s hi h.fr hb)
    · exact K
  · simp only [objects.finalise_cap, objects.finalise_cap_object, vspace.unmap_page_directory, bind_ok]
    split
    · split
      · exact W' _ (UPT z w x)
      · exact K
    · exact K
  · simp only [objects.finalise_cap, objects.finalise_cap_object, vspace.unmap_pdpt, bind_ok]
    split
    · split
      · exact W' _ (UPT z w x)
      · exact K
    · exact K
  · simp only [objects.finalise_cap, objects.finalise_cap_object, lift, bind_ok]
    split
    · split
      · exact W' _ (vspace.delete_asid.vs hA s a z _ P.vs fun i => P.pool Ac' s z i h.fr hb)
      · exact K
    · exact K

set_option maxHeartbeats 1000000 in
/-- **`empty_slot`** of a cap slot, its cleanup cap typed. -/
theorem cdt.empty_slot.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s0 s : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) {a : A} {x : U64} {c : capability.Cap}
    (h : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : SlotW T Ω Sg x) (hc : DelCapOK T Ω Sg H Rp Nt c) :
    cdt.empty_slot st ar s a x c ⦃ r => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  obtain ⟨Ac', hb⟩ := h.bxi
  unfold cdt.empty_slot
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st x s hS) fun c0 _ => ?_
  refine WP.spec_bind (P0.capability.Cap.is_null.p0 c0) fun bn _ => ?_
  split
  · exact (WP.spec_ok _).2 h
  refine WP.spec_bind (P.prev Ac' s x h.fr hb hx) fun pv hpv => ?_
  refine WP.spec_bind (P.next Ac' s x h.fr hb hx) fun nx hnx => ?_
  refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st x s hS) fun fb _ => ?_
  simp only [obj.Slot.is_null, bind_ok]
  refine WP.spec_bind (Pₘ := fun s1 => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s1) ?_ fun s1 h1 => ?_
  · split
    · exact (WP.spec_ok _).2 h
    · rename_i hp0
      exact WP.spec_mono (obj.Slot.set_next.capw (hpv.resolve_left (by simpa using hp0))) fun s' w =>
        h.capw7 w fun _ hb => hb
  refine WP.spec_bind (Pₘ := fun s2 => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s2) ?_ fun s2 h2 => ?_
  · split
    · exact (WP.spec_ok _).2 h1
    · rename_i hn0
      have hnW := hnx.resolve_left (by simpa using hn0)
      refine WP.spec_bind (obj.Slot.set_prev.capw hnW) fun s3 w3 => ?_
      have h3 := h1.capw7 w3 fun _ hb => hb
      refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st nx s3 hS) fun nfb _ => ?_
      split <;> exact WP.spec_mono (obj.Slot.set_first_badged.capw hnW) fun s' w => h3.capw7 w fun _ hb => hb
  refine WP.spec_bind (obj.Slot.clear.capw hx) fun s3 w3 => ?_
  exact objects.post_cap_deletion.cur0 hA (h2.capw7 w3 fun _ hb => hb) hc
set_option maxHeartbeats 2000000 in
/-- **`cdt.swap`** of two cap slots. -/
theorem cdt.swap.cur0 {V : U64 → Prop} {s0 s : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0)
    {c1 c2 : capability.Cap} {x1 x2 : U64} (h : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s)
    (h1 : SlotW T Ω Sg x1) (h2 : SlotW T Ω Sg x2) :
    cdt.swap st s c1 x1 c2 x2 ⦃ s' => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.swap
  refine WP.spec_bind (h.cw7 (obj.Slot.set_cap.capw h1)) fun sa ha => ?_
  refine WP.spec_bind (ha.cw7 (obj.Slot.set_cap.capw h2)) fun sb hb => ?_
  obtain ⟨Acb, hbb⟩ := hb.bxi
  refine WP.spec_bind (P.prev Acb sb x1 hb.fr hbb h1) fun p1 hp1 => ?_
  refine WP.spec_bind (P.next Acb sb x1 hb.fr hbb h1) fun n1 hn1 => ?_
  refine WP.spec_bind (P0.obj.Slot.revocable.p0 st x1 sb hS) fun r1 _ => ?_
  refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st x1 sb hS) fun f1 _ => ?_
  simp only [obj.Slot.is_null, bind_ok]
  refine WP.spec_bind (Pₘ := fun s' => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s') ?_ fun sc hc => ?_
  · split
    · exact (WP.spec_ok _).2 hb
    · rename_i e; exact hb.cw7 (obj.Slot.set_next.capw (hp1.resolve_left (by simpa using e)))
  refine WP.spec_bind (Pₘ := fun s' => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s') ?_ fun sd hd => ?_
  · split
    · exact (WP.spec_ok _).2 hc
    · rename_i e; exact hc.cw7 (obj.Slot.set_prev.capw (hn1.resolve_left (by simpa using e)))
  obtain ⟨Acd, hbd⟩ := hd.bxi
  refine WP.spec_bind (P.prev Acd sd x2 hd.fr hbd h2) fun p2 hp2 => ?_
  refine WP.spec_bind (P.next Acd sd x2 hd.fr hbd h2) fun n2 hn2 => ?_
  refine WP.spec_bind (P0.obj.Slot.revocable.p0 st x2 sd hS) fun r2 _ => ?_
  refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st x2 sd hS) fun f2 _ => ?_
  refine WP.spec_bind (hd.cw7 (obj.Slot.set_prev.capw h1)) fun s5 h5 => ?_
  refine WP.spec_bind (h5.cw7 (obj.Slot.set_next_flags.capw h1)) fun s6 h6 => ?_
  refine WP.spec_bind (h6.cw7 (obj.Slot.set_prev.capw h2)) fun s7 h7 => ?_
  refine WP.spec_bind (h7.cw7 (obj.Slot.set_next_flags.capw h2)) fun s12 h12 => ?_
  refine WP.spec_bind (Pₘ := fun s' => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s') ?_ fun s13 h13 => ?_
  · split
    · exact (WP.spec_ok _).2 h12
    · rename_i e; exact h12.cw7 (obj.Slot.set_next.capw (hp2.resolve_left (by simpa using e)))
  split
  · exact (WP.spec_ok _).2 h13
  · rename_i e; exact h13.cw7 (obj.Slot.set_prev.capw (hn2.resolve_left (by simpa using e)))

theorem cdt.cap_swap_for_delete.cur0 {V : U64 → Prop} {s0 s : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0)
    {x1 x2 : U64} (h : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (h1 : SlotW T Ω Sg x1) (h2 : SlotW T Ω Sg x2) :
    cdt.cap_swap_for_delete st s x1 x2 ⦃ s' => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.cap_swap_for_delete obj.Slot.Insts.CoreCmpPartialEqSlot.eq
  simp only [bind_ok]
  split
  · exact (WP.spec_ok _).2 h
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st x1 s hS) fun c1 _ => ?_
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st x2 s hS) fun c2 _ => ?_
  exact cdt.swap.cur0 P h h1 h2

set_option hygiene false in
/-- The preemption-point tail of a deferred round (`Cur0` at `s3`). -/
local macro "dtail" : tactic => `(tactic| (
  refine WP.spec_bind (sched.preemption_point.cur0 hA h3) ?_
  rintro ⟨rr, s4, a4⟩ h4
  try simp only [uncurry_apply_pair] at h4 ⊢
  rcases rr with _ | ee
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok]
    refine (WP.spec_ok _).2 ⟨h4, ?_⟩
    show fuel1.val < fuel.val
    omega
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 ⟨h4, fun v hv => by cases hv⟩))

set_option maxHeartbeats 4000000 in
/-- **`finalise_slot_deferred`** of a cap slot: `Cur0`, the cleanup cap typed. -/
theorem cdt.finalise_slot_deferred.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s0 s : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) (F : FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z (FrVc st T Cs Ω H Sg Rp Scs Nt Z s0) s0)
    {a : A} {x : U64} (h : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : SlotW T Ω Sg x) :
    cdt.finalise_slot_deferred st ar s a x ⦃ r => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧
      ∀ v, r.1 = .Ok v → DelCapOK T Ω Sg H Rp Nt v.cleanup ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.finalise_slot_deferred cdt.finalise_slot_deferred_loop
  apply loop.spec_decr_nat (measure := fun y => y.2.2.val)
    (inv := fun y => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 y.1)
  · rintro ⟨s1, a1, fuel⟩ h1
    simp only at h1
    dsimp only
    unfold cdt.finalise_slot_deferred_loop.body
    split
    swap
    · exact (WP.spec_ok _).2 ⟨h1, fun v hv => by cases hv⟩
    rename_i hf
    have hf' : 0 < fuel.val := by simpa using hf
    step as ⟨fuel1, hf1⟩
    obtain ⟨Acx, hbx⟩ := h1.bxi
    refine WP.spec_bind (WP.spec_and (P.cap Acx s1 x h1.fr hbx hx) (P.frmV Acx s1 x h1.fr hbx hx))
      fun c ⟨⟨hc, hpl⟩, hfr⟩ => ?_
    refine WP.spec_bind (P0.capability.Cap.is_null.p0 c) fun bn _ => ?_
    split
    · exact (WP.spec_ok _).2 ⟨h1, fun v hv => by cases hv; exact DelCapOK.null⟩
    refine WP.spec_bind (P0.cdt.is_final_capability_with_cap.p0 st s1 x c hS) fun fin _ => ?_
    refine WP.spec_bind (F Ac s1 a1 c fin h1 hc hpl hfr) ?_
    rintro ⟨⟨rem, cl⟩, s2, a2⟩ ⟨h2', hrem, hcl⟩
    try simp only [uncurry_apply_pair]
    refine WP.spec_bind (P0.cdt.cap_removable.p0 rem x) fun br _ => ?_
    split
    · exact (WP.spec_ok _).2 ⟨h2', fun v hv => by cases hv; exact hcl⟩
    refine WP.spec_bind (h2'.cw7 (obj.Slot.set_cap.capw (c := rem) hx)) fun s2 h2 => ?_
    refine WP.spec_bind (P0.cdt.cap_cyclic_zombie.p0 rem x) fun bz _ => ?_
    split
    · exact (WP.spec_ok _).2 ⟨h2, fun v hv => by cases hv; exact hcl⟩
    refine WP.spec_bind (Pₘ := fun s' => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s') ?_ fun s3 h3 => ?_
    · split
      all_goals try exact (WP.spec_ok _).2 h2
      rename_i zp zt zn
      exact cdt.cap_swap_for_delete.cur0 P h2 (hrem.2.2.2.2.1 zp zt zn rfl).1 hx
    dtail
  · exact h

/-- **`delete_deferred`** of a cap slot. -/
theorem cdt.delete_deferred.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s0 s : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) (F : FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z (FrVc st T Cs Ω H Sg Rp Scs Nt Z s0) s0)
    {a : A} {x : U64} (h : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : SlotW T Ω Sg x) :
    cdt.delete_deferred st ar s a x ⦃ r => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ⦄ := by
  unfold cdt.delete_deferred
  refine WP.spec_bind (cdt.finalise_slot_deferred.cur0 hA P F h hx) ?_
  rintro ⟨r, s1, a1⟩ ⟨h1, hv1⟩
  try simp only [uncurry_apply_pair] at h1 hv1 ⊢
  rcases r with v | e
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    split
    · refine WP.spec_bind (cdt.empty_slot.cur0 hA P h1 hx (hv1 v rfl)) ?_
      rintro ⟨s2, a2⟩ h2
      exact (WP.spec_ok _).2 h2
    · exact (WP.spec_ok _).2 h1
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 h1

set_option maxHeartbeats 1000000 in
/-- `W7.cdt.empty_slot.cur0` (`Cur0` only) from the `rv`-free placement `R.DelPlaceAt`. -/
theorem cdt.empty_slot.c0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s0 s : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) {a : A} {x : U64} {c : capability.Cap}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : SlotW T Ω Sg x) (hc : DelCapOK T Ω Sg H Rp Nt c) :
    cdt.empty_slot st ar s a x c ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  obtain ⟨Ac', hb⟩ := h.bxi
  unfold cdt.empty_slot
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st x s hS) fun c0 _ => ?_
  refine WP.spec_bind (P0.capability.Cap.is_null.p0 c0) fun bn _ => ?_
  split
  · exact (WP.spec_ok _).2 h
  refine WP.spec_bind (P.prev Ac' s x h.fr hb hx) fun pv hpv => ?_
  refine WP.spec_bind (P.next Ac' s x h.fr hb hx) fun nx hnx => ?_
  refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st x s hS) fun fb _ => ?_
  simp only [obj.Slot.is_null, bind_ok]
  refine WP.spec_bind (Pₘ := fun s1 => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s1) ?_ fun s1 h1 => ?_
  · split
    · exact (WP.spec_ok _).2 h
    · rename_i hp0
      exact WP.spec_mono (obj.Slot.set_next.capw (hpv.resolve_left (by simpa using hp0))) fun s' w =>
        h.capw7 w fun _ hb => hb
  refine WP.spec_bind (Pₘ := fun s2 => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s2) ?_ fun s2 h2 => ?_
  · split
    · exact (WP.spec_ok _).2 h1
    · rename_i hn0
      have hnW := hnx.resolve_left (by simpa using hn0)
      refine WP.spec_bind (obj.Slot.set_prev.capw hnW) fun s3 w3 => ?_
      have h3 := h1.capw7 w3 fun _ hb => hb
      refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st nx s3 hS) fun nfb _ => ?_
      split <;> exact WP.spec_mono (obj.Slot.set_first_badged.capw hnW) fun s' w => h3.capw7 w fun _ hb => hb
  refine WP.spec_bind (obj.Slot.clear.capw hx) fun s3 w3 => ?_
  exact W7.objects.post_cap_deletion.cur0 hA (h2.capw7 w3 fun _ hb => hb) hc


/-! ## The thread kind over the corrected placements -/

set_option maxHeartbeats 2000000 in
/-- **The thread kind's finalisation, a bound VCPU or an `ARMVCPURun` possibly in flight** (`fin_thread.ubR`,
the placement's [P] `vc`). -/
theorem finGapB_thread {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop} {s0 : S}
    (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) :
    FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z (fun c => ∃ x1, c = .Thread x1) s0 := by
  intro Ac s a c fin h hc hpl ⟨p, e⟩
  subst e
  have hp := hc.2.2.2.2.2 p rfl
  have hid := hpl.1 p rfl
  obtain ⟨Ac', hb⟩ := h.bxi
  have hT := hb.1.choose_spec.choose_spec.tcbs
  rw [fin_cap_eq_obj (by simp)]
  refine WP.spec_mono (WP.spec_and (fin_thread.rem hA s a p fin) (fin_thread.ubR hA P.vc h.1 h.2 a p fin hp hid)) ?_
  rintro ⟨⟨r1, r2⟩, s', a'⟩ ⟨e, h2⟩
  simp only at e h2 ⊢
  refine ⟨h2, ?_, ?_⟩
  · simp only [Prod.mk.injEq] at e
    rw [e.1]; split
    · exact tcb_zombieOK hT hp
    · exact DelCapOK.null
  · simp only [Prod.mk.injEq] at e
    rw [e.2]; exact DelCapOK.null

/-- The thread kind keeps [J] `RunVcpuInv` (over `R.FinRvAt`'s `FinPl`), from the placement's [P] `vc`. -/
theorem finRv_thread {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop} {s0 s : S}
    (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) {a : A} {p : U64} {fin : Bool}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hRV : RunVcpuInv st T s)
    (hc : DelCapOK T Ω Sg H Rp Nt (.Thread p)) (hpl : Fl4ProofsA64.P1.FinPl st Scs s (.Thread p)) :
    objects.finalise_cap st ar s a (.Thread p) fin false ⦃ r => RunVcpuInv st T r.2.1 ⦄ := by
  have hp := hc.2.2.2.2.2 p rfl
  obtain ⟨hid, -⟩ := hpl.1 p rfl
  rw [fin_cap_eq_obj (by simp)]
  exact WP.spec_mono (fin_thread.ubR hA P.vc h hRV a p fin hp hid) fun r hr => hr.2


/-- `W7.finGap_irq` (`Cur0` part) from the `rv`-free placement. -/
theorem finGap_irq0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s0 : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) :
    C0Gap st ar T Cs Ω H Sg Rp Scs Nt Z (fun c => ∃ x1, c = .IrqHandler x1) s0 := by
  have hS : P0.StoreTotal st := L.total
  intro Ac s a c fin h _ hc _ ⟨irq, e⟩
  subst e
  have hi := hc.2.1 irq rfl
  obtain ⟨Ac', hb⟩ := h.bxi
  unfold objects.finalise_cap
  simp only [bind_ok]
  refine WP.spec_bind (Pₘ := fun r : S × A => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1) ?_ ?_
  · split
    · unfold interrupt.deleting_irq_handler
      refine WP.spec_bind (interrupt.irq_slot.val s irq) fun isl eisl => ?_
      subst eisl
      have hW := slotW_to7 (irq_slotW hb hi)
      unfold cdt.delete_one
      refine WP.spec_bind (WP.spec_and (P.irq Ac' s irq h.fr hb hi) (P.cap Ac' s _ h.fr hb hW)) fun c ⟨hc', hcd⟩ => ?_
      refine WP.spec_bind (P0.capability.Cap.is_null.p0 c) fun bn _ => ?_
      split
      · exact (WP.spec_ok _).2 h
      refine WP.spec_bind (P0.cdt.is_final_capability_with_cap.p0 st s _ c hS) fun f _ => ?_
      rcases hc' with rfl | ⟨n, b0, b1, b2, rfl⟩
      · simp [objects.finalise_cap_object]
        exact cdt.empty_slot.c0 hA P h hW DelCapOK.null
      · obtain ⟨hn, hH⟩ := hcd.1.1.2.1 n b0 b1 b2 rfl
        refine WP.spec_bind (fin_ntfn_obj.cur0 (ar := ar) (a := a) (fin := f) (b0 := b0) (b1 := b1) (b2 := b2) h hn hH) ?_
        rintro ⟨_, s1, a1⟩ ⟨-, h1⟩
        exact cdt.empty_slot.c0 hA P h1 hW DelCapOK.null
    · exact (WP.spec_ok _).2 h
  rintro ⟨s1, a1⟩ h1
  simp only at h1 ⊢
  unfold objects.finalise_cap_object
  dsimp only
  split
  · exact (WP.spec_ok _).2 ⟨h1, DelCapOK.null, hc⟩
  · exact (WP.spec_ok _).2 ⟨h1, DelCapOK.null, DelCapOK.null⟩

set_option maxHeartbeats 1000000 in
/-- The IRQ-handler kind keeps [J] `RunVcpuInv` (the handler slot's notification cap, then `empty_slot` over
`Cur0R`), from the `rv`-free placement. -/
theorem finRv_irq {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop} {s0 s : S}
    (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) {a : A} {irq : U64} {fin : Bool}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hRV : RunVcpuInv st T s)
    (hc : DelCapOK T Ω Sg H Rp Nt (.IrqHandler irq)) :
    objects.finalise_cap st ar s a (.IrqHandler irq) fin false ⦃ r => RunVcpuInv st T r.2.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hi := hc.2.1 irq rfl
  obtain ⟨Ac', hb⟩ := h.bxi
  unfold objects.finalise_cap
  simp only [bind_ok]
  refine WP.spec_bind (Pₘ := fun r : S × A => RunVcpuInv st T r.1) ?_ ?_
  · split
    · unfold interrupt.deleting_irq_handler
      refine WP.spec_bind (interrupt.irq_slot.val s irq) fun isl eisl => ?_
      subst eisl
      have hW := slotW_to7 (irq_slotW hb hi)
      unfold cdt.delete_one
      refine WP.spec_bind (WP.spec_and (P.irq Ac' s irq h.fr hb hi) (P.cap Ac' s _ h.fr hb hW)) fun c ⟨hc', hcd⟩ => ?_
      refine WP.spec_bind (P0.capability.Cap.is_null.p0 c) fun bn _ => ?_
      split
      · exact (WP.spec_ok _).2 hRV
      refine WP.spec_bind (P0.cdt.is_final_capability_with_cap.p0 st s _ c hS) fun f _ => ?_
      rcases hc' with rfl | ⟨n, b0, b1, b2, rfl⟩
      · simp [objects.finalise_cap_object]
        exact WP.spec_mono (cdt.empty_slot.cur0 hA P ⟨h, hRV⟩ hW DelCapOK.null) fun r hr => hr.2
      · obtain ⟨hn, hH⟩ := hcd.1.1.2.1 n b0 b1 b2 rfl
        refine WP.spec_bind (WP.spec_and (fin_ntfn_obj.cur0 (ar := ar) (a := a) (fin := f) (b0 := b0) (b1 := b1)
          (b2 := b2) h hn hH) (fin_ntfn_obj.rvi (ar := ar) s a n b0 b1 b2 f hb.blk hn hH hRV)) ?_
        rintro ⟨_, s1, a1⟩ ⟨⟨_, h1⟩, r1⟩
        exact WP.spec_mono (cdt.empty_slot.cur0 hA P ⟨h1, r1⟩ hW DelCapOK.null) fun r hr => hr.2
    · exact (WP.spec_ok _).2 hRV
  rintro ⟨s1, a1⟩ h1
  simp only at h1 ⊢
  unfold objects.finalise_cap_object
  dsimp only
  split
  · exact (WP.spec_ok _).2 h1
  · exact (WP.spec_ok _).2 h1

/-- **[J] `FinRvAt` from the `rv`-free placement and [J] `FinRvRest`.** -/
theorem finRvAt_of {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop} {s0 : S}
    (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) (G : FinRvRest st ar T Cs Ω H Sg Rp Scs Nt Z s0) :
    FinRvAt st ar T Cs Ω H Sg Rp Scs Nt Z s0 := by
  intro Ac s a c fin h hRV hc hpl hk
  rcases hk with ⟨x1, x2, x3, x4, x5, x6, rfl⟩ | ⟨x1, x2, x3, x4, rfl⟩ | hk | hk | hk | ⟨x1, rfl⟩ | hk | hk | hk
  · exact finRv_ep h hRV hc
  · exact finRv_ntfn h hRV hc
  · exact G Ac s a _ fin h hRV hc hpl (Or.inl hk)
  · exact G Ac s a _ fin h hRV hc hpl (Or.inr (Or.inl hk))
  · exact G Ac s a _ fin h hRV hc hpl (Or.inr (Or.inr (Or.inl hk)))
  · exact finRv_irq hA P h hRV hc
  · exact G Ac s a _ fin h hRV hc hpl (Or.inr (Or.inr (Or.inr (Or.inl hk))))
  · exact G Ac s a _ fin h hRV hc hpl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hk)))))
  · exact G Ac s a _ fin h hRV hc hpl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hk)))))

/-- **[J] `FinRvRest` from the `rv`-free placement and [J] `FinRvRest3`.** -/
theorem finRvRest_of3 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop} {s0 : S}
    (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) (G : FinRvRest3 st ar T Cs Ω H Sg Rp Scs Nt Z s0) :
    FinRvRest st ar T Cs Ω H Sg Rp Scs Nt Z s0 := by
  intro Ac s a c fin h hRV hc hpl hk
  rcases hk with hk | ⟨p, x, rfl⟩ | ⟨p, rfl⟩ | hk | hk | hk
  · exact G Ac s a _ fin h hRV hc hpl (Or.inl hk)
  · exact finRv_sc hA h hRV hpl
  · exact finRv_thread hA P h hRV hc hpl
  · exact G Ac s a _ fin h hRV hc hpl (Or.inr (Or.inl hk))
  · exact G Ac s a _ fin h hRV hc hpl (Or.inr (Or.inr (Or.inl hk)))
  · exact G Ac s a _ fin h hRV hc hpl (Or.inr (Or.inr (Or.inr hk)))


/-! ## The VCPU kind -/

set_option maxHeartbeats 1000000 in
/-- **The VCPU kind's finalisation**, `Cur0R` to `Cur0R` (`vcpu.finalise.ub`; `vc` a VCPU object along the step
by `VcCap`, `B.DelPlaceAt.vc` for `unbind`'s run caller). -/
theorem fin_vcpuV {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop} {s0 s : S}
    (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) {a : A} {v : U64} {fin : Bool}
    (h : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s)
    (hv : ∀ (Ac' : Set U64) (s' : S), Fr0 st T Cs Ω H Sg Scs Z s0 s' →
      BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' s' → VcObj st T Ω Sg s' v) :
    objects.finalise_cap st ar s a (.Vcpu v) fin false ⦃ r => Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧
      DelCapOK T Ω Sg H Rp Nt r.1.1 ∧ DelCapOK T Ω Sg H Rp Nt r.1.2 ⦄ := by
  rw [fin_cap_eq_obj (by simp)]
  cases fin
  · unfold objects.finalise_cap_object
    dsimp only
    split
    · rename_i hf; exact absurd hf (by simp)
    · exact (WP.spec_ok _).2 ⟨h, DelCapOK.null, DelCapOK.null⟩
  · unfold objects.finalise_cap_object
    dsimp only
    split
    · refine WP.spec_bind (vcpu.finalise.ub hA P.vc h.1 a v fun s' h' _ => ?_) ?_
      · obtain ⟨Ac', hb'⟩ := h'.bxi
        exact hv Ac' s' h'.fr hb'
      rintro ⟨s1, a1⟩ F1
      try simp only [WP.uncurry'_pair, uncurry_apply_pair] at F1 ⊢
      exact (WP.spec_ok _).2 ⟨⟨F1.cur, F1.rvi h.2⟩, DelCapOK.null, DelCapOK.null⟩
    · rename_i hf; exact absurd rfl hf

/-- `FinRvKind` without the VCPU kind. -/
def FinRvKindV (c : capability.Cap) : Prop :=
  (∃ x1 x2 x3 x4 x5 x6, c = .Endpoint x1 x2 x3 x4 x5 x6) ∨ (∃ x1 x2 x3 x4, c = .Notification x1 x2 x3 x4) ∨
  (∃ x1 x2, c = .Reply x1 x2) ∨ (∃ x1 x2, c = .SchedContext x1 x2) ∨ (∃ x1, c = .Thread x1) ∨
  (∃ x1, c = .IrqHandler x1) ∨ (∃ x1 x2 x3 x4 x5, c = .Ept x1 x2 x3 x4 x5) ∨
  (∃ x1 x2 x3 x4 x5 x6 x7, c = .Frame x1 x2 x3 x4 x5 true x6 x7)

/-- `RunVcpuInv` kept by every `FinRvKindV` kind's finalisation, from the placement and [J] `FinRvRest5`. -/
theorem finRvAtV_of {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop} {s0 : S}
    (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) (G : FinRvRest5 st ar T Cs Ω H Sg Rp Scs Nt Z s0) :
    ∀ (Ac : Set U64) (s : S) (a : A) (c : capability.Cap) (fin : Bool),
      Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s → RunVcpuInv st T s → DelCapOK T Ω Sg H Rp Nt c →
      Fl4ProofsA64.P1.FinPl st Scs s c → FinRvKindV c →
      objects.finalise_cap st ar s a c fin false ⦃ r => RunVcpuInv st T r.2.1 ⦄ := by
  intro Ac s a c fin h hRV hc hpl hk
  rcases hk with ⟨x1, x2, x3, x4, x5, x6, rfl⟩ | ⟨x1, x2, x3, x4, rfl⟩ | ⟨p, x, rfl⟩ | ⟨p, x, rfl⟩ | ⟨p, rfl⟩ |
    ⟨x1, rfl⟩ | hk | hk
  · exact finRv_ep h hRV hc
  · exact finRv_ntfn h hRV hc
  · exact finRv_reply hA h hRV hc
  · exact finRv_sc hA h hRV hpl
  · exact finRv_thread hA P h hRV hc hpl
  · exact finRv_irq hA P h hRV hc
  · exact G Ac s a _ fin h hRV hc hpl (Or.inl hk)
  · exact G Ac s a _ fin h hRV hc hpl (Or.inr hk)

/-- `ofC0` over `FinRvKindV`. -/
theorem ofC0V {A : Type _} {ar : machine.Arch A} {Pk : capability.Cap → Prop} {s0 : S}
    (g : C0Gap st ar T Cs Ω H Sg Rp Scs Nt Z Pk s0)
    (R : ∀ (Ac : Set U64) (s : S) (a : A) (c : capability.Cap) (fin : Bool),
      Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s → RunVcpuInv st T s → DelCapOK T Ω Sg H Rp Nt c →
      Fl4ProofsA64.P1.FinPl st Scs s c → FinRvKindV c →
      objects.finalise_cap st ar s a c fin false ⦃ r => RunVcpuInv st T r.2.1 ⦄)
    (hk : ∀ c, Pk c → FinRvKindV c) : W7.R.FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z Pk s0 :=
  fun Ac s a c fin h hc hpl hp =>
    WP.spec_mono (WP.spec_and (g Ac s a c fin h.1 h.2 hc hpl hp) (R Ac s a c fin h.1 h.2 hc hpl (hk c hp)))
      fun _ ⟨⟨a1, a2, a3⟩, b⟩ => ⟨⟨a1, b⟩, a2, a3⟩

/-! ## Every kind, the deletion gaps, the CNode family -/

/-- **Every cap kind's finalisation over `Cur0R`** for caps with `FrVc` (`B.fin_all` with the VCPU kind proved,
`fin_vcpuV`; `arch` for the Stage-2 / device-frame kinds only). -/
theorem fin_all {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s0 : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) (W : VsDelAt st ar T Cs Ω H Sg Rp Scs Nt Z V s0)
    (G : FinGapsAt5 st ar T Cs Ω H Sg Rp Scs Nt Z s0) :
    FinGapAt st ar T Cs Ω H Sg Rp Scs Nt Z (FrVc st T Cs Ω H Sg Rp Scs Nt Z s0) s0 := by
  have ep := FinGapAt.ofR (by rintro c hc ⟨_, rfl⟩; simp at hc) <| ofC0V (C0Gap.ofW7 (W7.FinGapAt.ofOld (finGap_ep.at s0) (by
      rintro c ⟨_, _, _, _, _, _, rfl⟩; exact ⟨fun _ _ _ _ h => (nomatch h), fun _ _ _ h => (nomatch h)⟩))) (finRvAtV_of hA P G.rv)
    (by rintro c ⟨_, _, _, _, _, _, rfl⟩; exact Or.inl ⟨_, _, _, _, _, _, rfl⟩)
  have ntfn := FinGapAt.ofR (by rintro c hc ⟨_, rfl⟩; simp at hc) <| ofC0V (C0Gap.ofW7 (W7.FinGapAt.ofOld (finGap_ntfn.at s0) (by
      rintro c ⟨_, _, _, _, rfl⟩; exact ⟨fun _ _ _ _ h => (nomatch h), fun _ _ _ h => (nomatch h)⟩))) (finRvAtV_of hA P G.rv)
    (by rintro c ⟨_, _, _, _, rfl⟩; exact Or.inr (Or.inl ⟨_, _, _, _, rfl⟩))
  have reply := FinGapAt.ofR (by rintro c hc ⟨_, rfl⟩; simp at hc) <| ofC0V (finGap_reply0 hA) (finRvAtV_of hA P G.rv)
    (by rintro c ⟨_, _, rfl⟩; exact Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩)))
  have sc := FinGapAt.ofR (by rintro c hc ⟨_, rfl⟩; simp at hc) <| ofC0V (C0Gap.ofW7 (W7.FinGapAt.ofOld ((finGap_sc hA).at s0) (by
      rintro c ⟨_, _, rfl⟩; exact ⟨fun _ _ _ _ h => (nomatch h), fun _ _ _ h => (nomatch h)⟩))) (finRvAtV_of hA P G.rv)
    (by rintro c ⟨_, _, rfl⟩; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩))))
  have thread := finGapB_thread hA P
  have irq := FinGapAt.ofR (by rintro c hc ⟨_, rfl⟩; simp at hc) <| ofC0V (finGap_irq0 hA P) (finRvAtV_of hA P G.rv)
    (by rintro c ⟨_, rfl⟩; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))))))
  have arch := FinGapAt.ofR (by rintro c hc ⟨_, rfl⟩; simp at hc) <| ofC0V (C0Gap.ofW7 G.arch) (finRvAtV_of hA P G.rv) (by
    rintro c (⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, _, _, rfl⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, _, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, _, _, _, _, _, rfl⟩)))))))
  intro Ac s a c fin h hc hpl hfr
  cases c with
  | Null => exact fin_noop h (Or.inl rfl)
  | Untyped => exact fin_noop h (Or.inr (Or.inl ⟨_, _, _, _, rfl⟩))
  | IrqControl => exact fin_noop h (Or.inr (Or.inr (Or.inl rfl)))
  | Domain => exact fin_noop h (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  | SchedControl => exact fin_noop h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩)))))
  | AsidControl => exact fin_noop h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  | IoPortControl => exact fin_noop h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  | TdxControl => exact fin_noop h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))
  | CNode => exact fin_cnode h hc
  | Zombie => exact fin_zombie h hc
  | PageTable => exact fin_vs hA P W h hfr.1 (Or.inl ⟨_, _, _, _, rfl⟩)
  | HighVSpace => exact fin_vs hA P W h hfr.1 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, _, rfl⟩))))))
  | Pml4 => exact fin_vs hA P W h hfr.1 (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl⟩)))
  | AsidPool => exact fin_vs hA P W h hfr.1 (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩))))
  | Frame x1 x2 x3 x4 x5 e x6 x7 =>
    cases e
    · exact fin_vs hA P W h hfr.1 (Or.inr (Or.inl ⟨_, _, _, _, _, _, _, rfl⟩))
    · exact arch _ _ _ _ _ h hc hpl (Or.inr ⟨_, _, _, _, _, _, _, rfl⟩)
  | Endpoint => exact ep _ _ _ _ _ h hc hpl ⟨_, _, _, _, _, _, rfl⟩
  | Notification => exact ntfn _ _ _ _ _ h hc hpl ⟨_, _, _, _, rfl⟩
  | Reply => exact reply _ _ _ _ _ h hc hpl ⟨_, _, rfl⟩
  | SchedContext => exact sc _ _ _ _ _ h hc hpl ⟨_, _, rfl⟩
  | Thread => exact thread _ _ _ _ _ h hc hpl ⟨_, rfl⟩
  | IrqHandler => exact irq _ _ _ _ _ h hc hpl ⟨_, rfl⟩
  | PageDirectory => exact fin_vs hA P W h hfr.1 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, rfl⟩)))))
  | Pdpt => exact fin_vs hA P W h hfr.1 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, rfl⟩))))))
  | Vcpu => exact fin_vcpuV hA P h (hfr.2 _ rfl)
  | Ept => exact arch _ _ _ _ _ h hc hpl (Or.inl ⟨_, _, _, _, _, rfl⟩)
  | IoPort => exact fin_ioPort h hc ⟨_, _, _, rfl⟩

/-- **`B.DelGapsAt`, discharged** from `B.DelPlaceAt`, [J] `VsDelAt` and `FinGapsAt5`. -/
theorem delGaps_of {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    {s0 : S} (P : DelPlaceAt st T Cs Ω H Sg Rp Scs Nt Z V s0) (W : VsDelAt st ar T Cs Ω H Sg Rp Scs Nt Z V s0)
    (G : FinGapsAt5 st ar T Cs Ω H Sg Rp Scs Nt Z s0) :
    DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0 where
  cap := P.cap
  frm := P.frmV
  fin Ac s a c fin h hc hpl hfr := fin_all hA P W G Ac s a c fin h hc hpl hfr
  deferred _ _ _ _ h hx := cdt.delete_deferred.cur0 hA P (fin_all hA P W G) h hx
  empty _ _ _ _ _ h hx hc := cdt.empty_slot.cur0 hA P h hx hc
  next := P.next

/-- **`V.DelGaps`** at every decode start from `V.DelPlace`, [J] `VsDel` and `FinGaps5`. -/
theorem delGaps_of_gaps5 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    (P : DelPlace st T Cs Ω H Sg Rp Scs Nt Z V P3Ok) (W : VsDel st ar T Cs Ω H Sg Rp Scs Nt Z V P3Ok)
    (G : FinGaps5 st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok) : DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok :=
  fun s0 hE => delGaps_of hA (P s0 hE) (W s0 hE) (G s0 hE)

/-- **The `CNode` family's decode gap** from `CdtHyps2`, `V.DelPlace`, [J] `VsDel` and `FinGaps5` (the VCPU kind
proved). -/
theorem decGap_cnode_rv5 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {V : U64 → Prop}
    (C : CdtHyps2 st T Cs Ω H Sg Rp Scs Nt Z P3Ok) (P : DelPlace st T Cs Ω H Sg Rp Scs Nt Z V P3Ok)
    (W : VsDel st ar T Cs Ω H Sg Rp Scs Nt Z V P3Ok)
    (G : FinGaps5 st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok) : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .cnode :=
  decGap_cnode2 hA C (delGaps_of_gaps5 hA P W G)

end V
end B
end A5
end R
end W7

end

end Fl4ProofsA64.P1
