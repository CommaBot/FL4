/-
P3 (p3J gen 43): **bucket 3, the deletion loop's invariant with a `ProjW` footprint** (gen 41's item 2): DelW's
`DelHypsWRZ W Wx Wp Rd Rz` lifted to the invariants `WFt s0 W := W ∧ WritesIn s0 · (ProjW H Cs s0)` (and the same
for `Wx`, `Wp`), the `Rd` / `Rz` readiness predicates unchanged.

FL4 `cdt.rs` l.271–316 (`finalise_slot_immediate`'s loop, `delete`): every store change of the loop is a
`finalise_cap` (object finalisation), a `preemption_point`, a `post_cap_deletion`, or a slot edit (zombie written,
`cap_swap_for_delete`, `empty_slot`), and DelW's bundle has one field for each. So the lift needs exactly:

* `hfin` — `finalise_cap` of a `FinObjKind` slot cap from a `W` state writes only `ProjW` of that state (per kind:
  P3JNtfnFt / P3JEpFt / P3JFinFt / P3JScThFt, dispatched by P3JFinAll's `JAtZ.finCapProjW`; the IRQ handler kind
  open, see P3JFinAll);
* `hpp` — `preemption_point` from a `W` state writes only `ProjW`;
* `hpost` — `post_cap_deletion` of a cleanup cap from a `W` state writes only `ProjW` (P3JFinAll's
  `JAtZ.postCapDelProjW`);
* `hsl` — at a `Wx` state the typed heap's slot words are `ProjW` words (P3JStepFt's `JAtZ.inSlotProjW`).

* `WFt`, `slotFrame2_projW`, `WPost.ft`, **`DelHypsWRZ.foot`** (the lift, both readings of `WF` and `WPost`
  threaded), `WFt.foot` / `WFt.inv`.
* At a `JAtZ` state: **`JAtZ.ppProjW`** (`hpp`: P1 `preemption_point.pp`'s `PPW` words) and **`JAtZ.slotWdProjW`**
  (`hsl`).

The four inputs are hypotheses of the lift lemma (no named premise); instantiating them at the install / CNode
Delete invariants is the next step. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JFinAll
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- (p3J gen 43) **The invariant with the `ProjW` footprint from `s0`** (module docstring). -/
def WFt (H : P1.Heap) (Cs : Set U64) (s0 : S) (W : S → A → Fl4Spec.State Unit → MdbGhost → Prop) :
    S → A → Fl4Spec.State Unit → MdbGhost → Prop :=
  fun s a σ G => W s a σ G ∧ P1.WritesIn st s0 s (Mc.ProjW (L := L) H Cs s0)

variable {H : P1.Heap} {Cs : Set U64}

theorem WFt.inv {s0 s : S} {a : A} {σ : Fl4Spec.State Unit} {G : MdbGhost}
    {W : S → A → Fl4Spec.State Unit → MdbGhost → Prop} (h : WFt (L := L) H Cs s0 W s a σ G) : W s a σ G := h.1

theorem WFt.foot {s0 s : S} {a : A} {σ : Fl4Spec.State Unit} {G : MdbGhost}
    {W : S → A → Fl4Spec.State Unit → MdbGhost → Prop} (h : WFt (L := L) H Cs s0 W s a σ G) :
    P1.WritesIn st s0 s (Mc.ProjW (L := L) H Cs s0) := h.2

/-- (p3J gen 43) A slot-word frame is a `ProjW` step where the slot words are `ProjW` words. -/
theorem slotFrame2_projW {th : TypedHeap} {s s' : S} (h : Vs.SlotFrame2 (L := L) th s s')
    (hsl : ∀ b, (∃ x k, IsSlot th x ∧ Off k ∧ b = wordOf x k) → Mc.ProjW (L := L) H Cs s b) :
    P1.WritesIn st s s' (Mc.ProjW (L := L) H Cs s) :=
  ⟨h.1, h.2.1, fun b hb hn => h.2.2 b hb fun hh => hn (hsl b hh)⟩

/-- (p3J gen 43) `WPost` with a fact conjoined to both invariants. -/
theorem WPost.ft {α : Type} {W Wp : S → A → Fl4Spec.State Unit → MdbGhost → Prop} {P : S → Prop}
    {r : core.result.Result α error.Exc} {s : S} {a : A} {σ : Fl4Spec.State Unit} {G : MdbGhost}
    (h : WPost W Wp r s a σ G) (hp : P s) :
    WPost (fun s a σ G => W s a σ G ∧ P s) (fun s a σ G => Wp s a σ G ∧ P s) r s a σ G := by
  cases r with
  | Ok x => exact ⟨h, hp⟩
  | Err e => cases e <;> exact ⟨h, hp⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 43) **The deletion bundle with the `ProjW` footprint** (module docstring). -/
theorem DelHypsWRZ.foot {W Wx Wp : S → A → Fl4Spec.State Unit → MdbGhost → Prop}
    {Rd Rz : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop} {th : TypedHeap}
    (h : DelHypsWRZ (L := L) arI W Wx Wp Rd Rz th) (s0 : S)
    (hfin : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (c : capability.Cap),
      DState (L := L) th s σ G → W s a σ G → AbsSlot th sl → capAt (L.mem s) (cslotAddr sl) = ok c →
      FinObjKind c →
      objects.finalise_cap st arI s a c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) false ⦃ r =>
        P1.WritesIn st s r.2.1 (Mc.ProjW (L := L) H Cs s) ⦄)
    (hpp : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost), DState (L := L) th s σ G → W s a σ G →
      sched.preemption_point st arI s a ⦃ r => P1.WritesIn st s r.2.1 (Mc.ProjW (L := L) H Cs s) ⦄)
    (hpost : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (cl : capability.Cap),
      DState (L := L) th s σ G → W s a σ G → CleanCap cl → cl ≠ .Null → CapWf cl →
      objects.post_cap_deletion st arI s a cl ⦃ r => P1.WritesIn st s r.1 (Mc.ProjW (L := L) H Cs s) ⦄)
    (hsl : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost), Wx s a σ G →
      ∀ b, (∃ x k, IsSlot th x ∧ Off k ∧ b = wordOf x k) → Mc.ProjW (L := L) H Cs s b) :
    DelHypsWRZ (L := L) arI (WFt (L := L) H Cs s0 W) (WFt (L := L) H Cs s0 Wx) (WFt (L := L) H Cs s0 Wp)
      Rd Rz th := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s a σ G sl c hDS hW hA hc hk ht
    refine WP.spec_mono (WP.spec_and (h.fin s a σ G sl c hDS hW.1 hA hc hk ht)
      (hfin s a σ G sl c hDS hW.1 hA hc hk)) ?_
    rintro r ⟨⟨h1, h2, h3, σ', G', h4, h5, h6, h7, h8, ⟨hw1, hw2⟩, h10, h11⟩, F⟩
    have w := hW.2.projW_trans F
    exact ⟨h1, h2, h3, σ', G', h4, h5, h6, h7, h8, ⟨fun hn => ⟨hw1 hn, w⟩, fun hr => ⟨hw2 hr, w⟩⟩, h10, h11⟩
  · intro s a σ G sl c hDS hW
    exact h.triv s a σ G sl c hDS hW.1
  · intro s a σ G hDS hW
    refine WP.spec_mono (WP.spec_and (h.pp s a σ G hDS hW.1) (hpp s a σ G hDS hW.1)) ?_
    rintro r ⟨⟨h1, σ', h2, h3, h4⟩, F⟩
    exact ⟨h1, σ', h2, h3, WPost.ft (P := fun s => P1.WritesIn st s0 s (Mc.ProjW (L := L) H Cs s0)) h4
      (hW.2.projW_trans F)⟩
  · intro s a σ G cl hDS hW hcl hn hwf
    refine WP.spec_mono (WP.spec_and (h.post s a σ G cl hDS hW.1 hcl hn hwf) (hpost s a σ G cl hDS hW.1 hcl hn hwf)) ?_
    rintro r ⟨⟨h1, σ', h2, h3, h4⟩, F⟩
    exact ⟨h1, σ', h2, h3, h4, hW.2.projW_trans F⟩
  · intro s s' a σ σ' G sl p zt n hW h1 h2 h3 h4 h5 hF h6 h7 h8 h9 h10 h11 h12
    exact ⟨h.zomb s s' a σ σ' G sl p zt n hW.1 h1 h2 h3 h4 h5 hF h6 h7 h8 h9 h10 h11 h12,
      hW.2.projW_trans (slotFrame2_projW hF (hsl s a σ G (h.wx s a σ G hW.1)))⟩
  · intro s s' a σ σ' G G' sl p zt n hW h1 h2 h3 hF h4 h5 h6 h7 h8 h9 h10
    exact ⟨h.swap s s' a σ σ' G G' sl p zt n hW.1 h1 h2 h3 hF h4 h5 h6 h7 h8 h9 h10,
      hW.2.projW_trans (slotFrame2_projW hF (hsl s a σ G (h.wx s a σ G hW.1)))⟩
  · intro s s' a σ σ' G G' sl hW h1 h2 h3 hF h4 h5 h6 h7 h8 h9
    exact ⟨h.empty s s' a σ σ' G G' sl hW.1 h1 h2 h3 hF h4 h5 h6 h7 h8 h9,
      hW.2.projW_trans (slotFrame2_projW hF (hsl s a σ G hW.1))⟩
  · intro s a σ G hW
    exact ⟨h.wx s a σ G hW.1, hW.2⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- (p3J gen 43) **`preemption_point` at a `JAtZ` state writes only `ProjW`** (P1 `sched.preemption_point.pp`'s
`PPW`: `WORK_UNITS`, the executing core's `CUR_TIME` / `CONSUMED`; FL4 `sched.rs` l.736–755). -/
theorem JAtZ.ppProjW (hA : P0.ArchTotal arI) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    sched.preemption_point st arI s a ⦃ r => P1.WritesIn st s r.2.1 (Mc.ProjW (L := L) H Cs s) ⦄ := by
  have h0 := J.blk.1.choose_spec.choose_spec
  refine WP.spec_mono (P1.sched.preemption_point.pp hA s a J.blk) fun r hr => hr.2.mono fun b hb => ?_
  have hwu : layout.ks.WORK_UNITS.val = 40 := by simp [layout.ks.WORK_UNITS]
  rcases hb with rfl | rfl | rfl
  · have hv := P1.ks_val h0 (o := layout.ks.WORK_UNITS) (by omega)
    exact Or.inr (Or.inl ⟨by rw [hv]; omega, by rw [hv]; omega⟩)
  · unfold P1.LawfulStore.nodeA
    exact Mc.node_projW (h0.nodes _ h0.cur) h0.cur (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
      (by simp [layout.node.CUR_TIME])
  · unfold P1.LawfulStore.nodeA
    exact Mc.node_projW (h0.nodes _ h0.cur) h0.cur (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
      (by simp [layout.node.CONSUMED])

/-- (p3J gen 43) **The typed heap's slot words are `ProjW` words** at a `JAtZ` state (the `hsl` input of
`DelHypsWRZ.foot`; P3JStepFt's `JAtZ.inSlotProjW`). -/
theorem JAtZ.slotWdProjW {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {b : U64} (hb : ∃ x k, IsSlot Z.th x ∧ Off k ∧ b = wordOf x k) : Mc.ProjW (L := L) H Cs s b := by
  obtain ⟨x, k, hx, hk, e⟩ := hb
  exact J.inSlotProjW (Ipc.slotWd_range J.xtop.rel.1 ⟨x, hx, k, hk, e⟩)

end

end Fl4Proofs.P3
