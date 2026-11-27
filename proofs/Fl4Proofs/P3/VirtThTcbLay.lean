/-
P3x for virtualization (line virt, gen 28, item 3): **the TCB-only-heap transfers mmuAD's `JAtZV4` migration needs
for JAtZBLay** (handoff `# gen 26` item 3, "re-proved via the bridge"): JAtZBLay applies the extracted-level
lemmas `vcpu_detach_jv(B)`, `vcpu_decode_settcb_jv(B)`, `vcpu_enter_unbound`, `vcpu_enter_boundL`,
`vcpu_finalise_vl`, `sts_jv` at a `JExtV V X th s`; at `JExtV2` they run at `thTcb th` (`JExtV2.toTcb` with
`NoIoTcb`), so their placement hypotheses must move to `thTcb th`. Each only weakens when CNodes leave the heap:

* **`jwpl_thTcb`** (`JWPl`, JExtVSteps [J]), **`detPl_thTcb`** (`DetPl` [J]), **`detAt_thTcb`** (`DetAt` [J]),
  **`finPl_thTcb`** (`FinPl`, JExtVSteps2 [J]) — the twins of gen 26's `lay_thTcb` / `detB_thTcb` (VirtJExtV2Del).
* **`JExtV2.lift`**: back from the TCB-only heap — `JExtV V' X (thTcb th) s'` after the step, `V ⊆ V'`, and every
  slot that is not a TCB slot keeping its cap give `JExtV2 V' X th s'` (the CNode slots' `VtxCap2` from the entry's
  `JExtV2`, the TCB slots' from `JExtV`). With `NoIoTcb.of_writes` / `of_capEq` (JExtV2Bind) for the `nio` field,
  each JAtZBLay use becomes `toTcb` → the extracted lemma at `thTcb th` with these transfers → `lift`.

No named premise (the transferred structures are the existing [J] ones, unchanged). New file only; no existing
statement changed.
-/
import Fl4Proofs.P3.VirtJExtV2Del
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtThTcbLay
open fl4_core Classical Fl4Proofs.P3 Fl4Proofs.P3.VirtJExtV2Del

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {V X : Set U64} {th : TypedHeap} {Ub : U64 → Set U64}

theorem jwpl_thTcb (P : JWPl V th) : JWPl V (thTcb th) where
  jw b h := P.jw b (jw_thTcb h)
  sw b h := P.sw b (sw_thTcb.1 h)
  swjw b h hj := P.swjw b (sw_thTcb.1 h) (jw_thTcb hj)
  slv y hy t ht := P.slv y (isSlot_thTcb hy) t (thTcb_tcb.1 ht)
  slb y hy v hv := P.slb y (isSlot_thTcb hy) v hv
  vb t ht v hv := P.vb t (thTcb_tcb.1 ht) v hv

theorem detPl_thTcb (D : DetPl V th Ub) : DetPl V (thTcb th) Ub where
  pl := jwpl_thTcb D.pl
  h0 h := D.h0 (thTcb_tcb.1 h)
  ta t ht := D.ta t (thTcb_tcb.1 ht)
  ua t ht := D.ua t (thTcb_tcb.1 ht)
  rep t ht b hb := ⟨fun h => (D.rep t (thTcb_tcb.1 ht) b hb).1 (jw_thTcb h),
    fun h => (D.rep t (thTcb_tcb.1 ht) b hb).2 (sw_thTcb.1 h)⟩
  vca := D.vca
  vc v hv b hb := ⟨fun h => (D.vc v hv b hb).1 (jw_thTcb h), fun h => (D.vc v hv b hb).2 (sw_thTcb.1 h)⟩

theorem detAt_thTcb {s : S} (Da : DetAt st V th Ub s) : DetAt st V (thTcb th) Ub s where
  node := Da.node
  nd b hb := ⟨fun h => (Da.nd b hb).1 (jw_thTcb h), fun h => (Da.nd b hb).2 (sw_thTcb.1 h)⟩
  buf s1 hw t ht := Da.buf s1 (hw.mono fun _ hb => hb.imp jw_thTcb cw_thTcb.1) t (thTcb_tcb.1 ht)

theorem finPl_thTcb {s : S} {v : U64} (F : FinPl st V th Ub s v) : FinPl st V (thTcb th) Ub s v where
  own b hb := ⟨(F.own b hb).1, fun h => (F.own b hb).2.1 (jw_thTcb h), fun h => (F.own b hb).2.2 (cw_thTcb.1 h)⟩
  nbr b hb := ⟨(F.nbr b hb).1, fun h => (F.nbr b hb).2.1 (jw_thTcb h), fun h => (F.nbr b hb).2.2 (sw_thTcb.1 h)⟩

/-- **Back from the TCB-only heap** (module docstring). -/
theorem JExtV2.lift {V' : Set U64} {s s' : S} (E : JExtV2 (L := L) V X th s)
    (E' : JExtV (L := L) V' X (thTcb th) s') (hV : V ⊆ V')
    (hk : ∀ y, IsSlot th y → ¬ IsSlot (thTcb th) y → capV (L.mem s') y = capV (L.mem s) y) :
    JExtV2 (L := L) V' X th s' := by
  refine JExtV2.ofTcb E' fun y hy => ?_
  by_cases ht : IsSlot (thTcb th) y
  · exact (E'.cap y ht).toV2
  · rw [hk y hy ht]; exact VtxCap2.mono hV (fun _ h => h) (E.cap y hy)

end

end
end Fl4Proofs.P3.VirtThTcbLay
