/-
# P2 (line p3mc, gen 19): the view keeps every timer word of an armed thread, value and owner

At an st start whose target is homed on `c`, `set_timer_target_ok` walks core `c`'s timer tree
(`in_core_timer_tree`) and the accepted run inserts the target there (`timer::insert`, rotations and recolouring).
The tree's nodes are armed threads whose height names `c`'s tree; some may be **other cores' threads** (armed in
`c`'s tree under the gate, or migrated since). Core `c`'s view rewrites another core's thread only at `AFFINITY`
(3520), the `TZero` offsets (`SC` 3464, `IN_QUEUES` 3592, `DEBUG_NEXT` 3576, `DEBUG_PREV` 3584) and a hidden `STATE`
(3328) (`CoreView.tcbRepl`); the timer fields are offsets 3528 … 3568 (`OwnMap.TimerField`), none of those. Their
owner is `tOwner`: for an armed thread, the core of its tree (`treeCore` of `TIMER_HEIGHT`), whatever its
`AFFINITY`. So:

* **`view_timer_keep`**: the view keeps the value of every timer word of every thread;
* **`vn_timer`**: for a thread armed in `ρ` (`TIMER_DEADLINE ≠ 0`), every timer word is `VN` (value and owner kept),
  generalising `vn_td` (the deadline word only).

What this does **not** give (the obstacle for the accepting route, recorded for the next step): `VNW` (the write
set of `safeVQ`) asks `¬ VDec`, and `VDec` holds for the `TIMER_DEADLINE` / `TIMER_HEIGHT` words of every
other-core thread (`DecOff`). The accepted run writes `TIMER_HEIGHT` (colour) of tree nodes, possibly another core's
thread, keeping its tree core (`set_timer_accG`'s `hwH`: the written height names `c`). Those writes keep every
owner, but they are not `VNW` words; the U14/U15 `safeVQ` route needs a write set that admits value-checked
`DecOff` writes.

No premise: every fact is a hypothesis. No existing statement changed.
-/
import Fl4Proofs.P2.E2EPU17
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.CoreView
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.PathObl
open Fl4Proofs.P2.OwnMap
open Fl4Proofs.P2.OwnMapP (KLayoutP ownP RegionOKP UserOKP ownP_pte ownP_off)
open Fl4Proofs.P2.OwnMapV (ownV_off ownV_on_mem)

noncomputable section
open Classical

/-- **The view keeps the value of every timer word** (module docstring). -/
theorem view_timer_keep {K : KLayout} {c : U64} {m : U64 → U64} {b t : U64} (hb : region K b = .tcb t)
    (h1 : 3528 ≤ b.val - t.val) (h2 : b.val - t.val ≤ 3568) : view K c m b = m b :=
  view_keep_tcb hb (by omega) (by unfold TZero; omega) (by omega)

/-- **Every timer word of an armed thread is kept by the view, value and owner, whoever's thread it is.** -/
theorem vn_timer {K : KLayoutP} (hK : RegionOKP K) (hX : RegionOKX K.toKLayout) {c : U64}
    {ρ : U64 → U64} {t o : U64} (ht : K.heap t = some .tcb) (h1 : 3528 ≤ o.val) (h2 : o.val ≤ 3568)
    (h3 : o.val % 8 = 0) (h0 : ρ (fld t oTIMER_DEADLINE) ≠ 0#u64) : VN K c ρ (fld t o) := by
  have hK0 := hK.base.base
  obtain ⟨hr, ho, -⟩ := hX.tcbW t ht o (by omega) (by omega) h3
  have hr0 : region K.toKLayout (fld t o) = .tcb t := hr
  have ho0 : (fld t o).val - t.val = o.val := ho
  obtain ⟨hrD, hoD⟩ := hK0.tcb t ht oTIMER_DEADLINE (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  obtain ⟨hrH, hoH⟩ := hK0.tcb t ht oTIMER_HEIGHT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  rw [oDL_val] at hoD; rw [oHT_val] at hoH
  have e1 : view K.toKLayout c ρ (fld t o) = ρ (fld t o) :=
    view_timer_keep hr0 (by rw [ho0]; exact h1) (by rw [ho0]; exact h2)
  have e2 : view K.toKLayout c ρ (fld t oTIMER_DEADLINE) = ρ (fld t oTIMER_DEADLINE) :=
    view_timer_keep hrD (by omega) (by omega)
  have e3 : view K.toKLayout c ρ (fld t oTIMER_HEIGHT) = ρ (fld t oTIMER_HEIGHT) :=
    view_timer_keep hrH (by omega) (by omega)
  refine ⟨e1, ?_⟩
  have hp : fld t o ∉ K.ptes := fun h => by rw [hK.none _ h] at hr0; cases hr0
  have hv : ¬ ∃ v, Fl4Proofs.P2.OwnMapV.InVcpu K.toKLayoutV v (fld t o) := by
    rintro ⟨v, hv⟩; rw [hK.base.none v _ hv] at hr0; cases hr0
  have hv0 : (ρ (fld t oTIMER_DEADLINE)).val ≠ 0 := fun h => h0 (by
    apply UScalar.eq_of_val_eq; rw [h]; rfl)
  have hG : ¬ GateField o.val := by unfold GateField; omega
  have hT : TimerField o.val := ⟨h1, h2⟩
  rw [ownP_off hp, ownP_off hp, ownV_off hv, ownV_off hv]
  simp only [own, hr0, ho0, tcbOwner, if_neg hG, if_pos hT, tOwner, e2, e3, hv0, ne_eq, not_false_eq_true,
    if_true]

end
end Fl4Proofs.P2.CoreView
