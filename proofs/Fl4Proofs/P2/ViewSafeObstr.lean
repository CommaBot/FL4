/-
# P2 (line p3mc, gen 6): why `VSafe` cannot hold for vmF / vmR / sl at a start reading another core's thread

U6–U8 annotate a local body at core `c`'s **view** start state `σ` (`StartAt … (view K c ρ)`): a read of `x` is
translated as a plain `rd` (no race) when `x` is in the path's read set at `σ`, i.e. held by `c` or the gate's under
the owners of `view K c ρ` (`IoRS`, `RPerm`). `VSafe` [J] then asks the body to be `Safe` at the physical memory `μ`
(`VEq ρ μ`). `Safe.rd` asks the word to be readable (`PO`) at `μ`.

For a thread `t` homed on another core (`ρ (AFFINITY t) ≠ c`), its home-owned words (`STATE`, `BLOCK_OBJ`,
`REPLY_OBJ`, `OwnMap.tcbOwner`: owner `.core (AFFINITY)`) are **held by `c` at the view** (`view_aff` puts
`AFFINITY = c`) but **owned by `t`'s core at `μ`** (`AFFINITY` is the gate's, so `VEq` fixes it at `ρ`'s value).
Proved here:
* `own_home_at`, `ownP_home`: such a word's owner is `.core (m (AFFINITY t))` in every memory `m`;
* **`view_home_rperm`**: at the view it is readable by `c` (so the view's read set holds it, and `rdN` makes its read
  a plain `rd`: `rdN_rd`);
* **`real_home_not_po`**: at every `μ` with `VEq ρ μ` it is not readable by `c`;
* `safe_rd_po`: `Safe μ (.rd x k)` needs `x` readable at `μ`;
* **`view_home_rd_unsafe`**: hence a view-annotated body is **not `Safe` at `μ`** at a read of such a word (and the
  view differs from `ρ` there, so `VSafe`'s guard holds: `view_ne_of_foreign`).

The bodies reach such a read before they check the thread's `AFFINITY` (crates/fl4-core/src):
* vmF: `fastpath_vm.rs:42` `dest.reply_obj(s)` (`dest` = head of the fault endpoint, `:41`), before
  `schedulable_here` (`:43` → `fastpath.rs:55`); sl's trap branch the same at `fastpath.rs:98`;
* vmR: `fastpath_vm.rs:105` `u.state(s)` (and `u.fault_type`, `r.next`, `u.sc`) with `u = r.tcb` (`:104`); sl's
  ReplyRecv branch the same at `fastpath.rs:197`.
So wherever such a run is reached (a fault handler, or a ReplyRecv caller, on another core: ordinary on SMP),
`VSafe` [J] of U6–U8 for these slots is **false** for that start, not merely unproved, and no proof of `ViewSafe` for
these slots can exist with the view annotation. (The run on the real memory reads those words racily, as the real
annotation of U5 has it.) Ways out: annotate the body with a read set that drops the words whose owner the view
changes (a new start correspondence), or reorder the kernel's checks so `AFFINITY` is read first (as
`AccessVmDec`'s docstring already suggests).

No premise. No existing statement changed.
-/
import Fl4Proofs.P2.ViewSafeOwn
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.CoreView
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.PathObl
open Fl4Proofs.P2.OwnMap
open Fl4Proofs.P2.OwnMapP (KLayoutP ownP RegionOKP ownP_off)
open Fl4Proofs.P2.OwnMapV (ownV_off)

noncomputable section
open Classical

/-- A home-owned TCB word: `STATE`, `BLOCK_OBJ`, `REPLY_OBJ`. -/
def HomeOff (off : U64) : Prop := off = oSTATE ∨ off = oBLOCK_OBJ ∨ off = oREPLY_OBJ

theorem homeOff_dec {off : U64} (h : HomeOff off) : off = oAFFINITY ∨ off = oSTATE ∨ off = oBLOCK_OBJ ∨
    off = oREPLY_OBJ ∨ off = oTIMER_DEADLINE ∨ off = oTIMER_HEIGHT := by
  rcases h with h | h | h <;> simp [h]

/-- **A home-owned TCB word has its thread's home core as owner.** -/
theorem own_home_at {K : KLayout} (hK : RegionOK K) {t off : U64} (ht : K.heap t = some .tcb)
    (hoff : HomeOff off) (m : U64 → U64) :
    own K m (fld t off) = .core (m (fld t oAFFINITY)) := by
  have hv : off.val = 3328 ∨ off.val = 3336 ∨ off.val = 3360 := by
    rcases hoff with h | h | h <;> subst h
    · exact Or.inl oSTATE_val
    · exact Or.inr (Or.inl oBOBJ_val)
    · exact Or.inr (Or.inr oROBJ_val)
  rw [own_tcb_at hK ht (homeOff_dec hoff)]
  have h1 : ¬ GateField off.val := by simp only [GateField]; omega
  have h2 : ¬ TimerField off.val := by simp only [TimerField]; omega
  have h3 : ¬ GField off.val := by simp only [GField]; omega
  simp only [tcbOwner, if_neg h1, if_neg h2, if_neg h3]

/-- `own_home_at` for `ownP` (the word is in no PTE and no VCPU). -/
theorem ownP_home {K : KLayoutP} (hK : RegionOKP K) {t off : U64} (ht : K.heap t = some .tcb)
    (hoff : HomeOff off) (m : U64 → U64) :
    ownP K m (fld t off) = .core (m (fld t oAFFINITY)) := by
  have hr := (hK.base.base.tcb t ht off (homeOff_dec hoff)).1
  have hp : fld t off ∉ K.ptes := fun h => by rw [hK.none _ h] at hr; cases hr
  have hv : ¬ ∃ v, Fl4Proofs.P2.OwnMapV.InVcpu K.toKLayoutV v (fld t off) := by
    rintro ⟨v, hv⟩; rw [hK.base.none v _ hv] at hr; cases hr
  rw [ownP_off hp, ownV_off hv]
  exact own_home_at hK.base.base ht hoff m

/-- **At core `c`'s view, every thread's home-owned words are readable (held) by `c`.** -/
theorem view_home_rperm {K : KLayoutP} (hK : RegionOKP K) {c : U64} {lk : U64 → Prop} {ρ : U64 → U64}
    {t off : U64} (ht : K.heap t = some .tcb) (hoff : HomeOff off) :
    RPerm (ownP K) c lk (view K.toKLayout c ρ) (fld t off) := by
  refine Or.inl ?_
  show HeldBy c lk (ownP K (view K.toKLayout c ρ) (fld t off))
  rw [ownP_home hK ht hoff, view_aff hK.base.base ht c ρ]
  exact rfl

/-- **At a memory `c` cannot tell from `ρ`, a home-owned word of a thread homed off `c` in `ρ` is not readable
by `c`.** -/
theorem real_home_not_po {K : KLayoutP} (hK : RegionOKP K) {cls : U64 → U64 → U64}
    {ko : U64 → Serial.ClsOwner U64} {c : U64} {hs : U64 → Prop} {ρ μ : U64 → U64} {t off : U64}
    (ht : K.heap t = some .tcb) (hoff : HomeOff off) (hf : ρ (fld t oAFFINITY) ≠ c)
    (hV : Serial.VEq (ownP K) cls ko c hs ρ μ) :
    ¬ Serial.PO c hs (ownP K μ (fld t off)) := by
  have hra := (hK.base.base.tcb t ht oAFFINITY (Or.inl rfl)).1
  have hpa : fld t oAFFINITY ∉ K.ptes := fun h => by rw [hK.none _ h] at hra; cases hra
  have hva : ¬ ∃ v, Fl4Proofs.P2.OwnMapV.InVcpu K.toKLayoutV v (fld t oAFFINITY) := by
    rintro ⟨v, hv⟩; rw [hK.base.none v _ hv] at hra; cases hra
  have hg : ownP K μ (fld t oAFFINITY) = .gate := by
    rw [ownP_off hpa, ownV_off hva]; exact own_aff_gate hK.base.base ht μ
  have ea : ρ (fld t oAFFINITY) = μ (fld t oAFFINITY) := hV.2.1 _ (by rw [hg]; exact Or.inr rfl)
  rw [ownP_home hK ht hoff, ← ea]
  intro h
  rcases h with h | h
  · exact hf h
  · cases h

/-- The view differs from `ρ` as soon as some thread is homed off `c` in `ρ`. -/
theorem view_ne_of_foreign {K : KLayoutP} (hK : RegionOKP K) {c : U64} {ρ : U64 → U64} {t : U64}
    (ht : K.heap t = some .tcb) (hf : ρ (fld t oAFFINITY) ≠ c) : view K.toKLayout c ρ ≠ ρ := by
  intro h
  have e := view_aff hK.base.base ht c ρ
  rw [h] at e
  exact hf e

/-- `Safe` at a plain read asks the word to be readable at the start memory. -/
theorem safe_rd_po {own : (U64 → U64) → U64 → Serial.Owner U64 U64} {cls : U64 → U64 → U64}
    {ko : U64 → Serial.ClsOwner U64} {c : U64} {hs : U64 → Prop} {μ : U64 → U64} {x : U64}
    {k : U64 → E2E.SP} (h : Serial.Safe own cls ko c hs μ (.rd x k)) : Serial.PO c hs (own μ x) := by
  cases h with
  | rd h1 _ => exact h1 _ (.refl _)

/-- A read of a word of the read set is translated as a plain `rd`. -/
theorem rdN_rd {R User : U64 → Prop} {cls : U64 → U64 → U64} {ko : U64 → Serial.ClsOwner U64} {c : U64}
    {Wd : Set U64} {x : U64} {k : U64 → E2E.SP} (hR : R x) (hU : ¬ User x) :
    E2E.rdN R User cls ko c Wd x k = .rd x k := by
  have : ¬ E2E.Racy R User Wd x := fun h => h ⟨hU, Or.inl hR⟩
  unfold E2E.rdN; rw [if_pos this]

/-- **A view-annotated body is not `Safe` at a read of another core's thread's home-owned word** (module
docstring): such a read is a plain `rd` wherever the read set holds what the view lets `c` read (`rdN_rd`,
`view_home_rperm`), and at the physical memory the word is not readable (`real_home_not_po`). -/
theorem view_home_rd_unsafe {K : KLayoutP} (hK : RegionOKP K) {cls : U64 → U64 → U64}
    {ko : U64 → Serial.ClsOwner U64} {c : U64} {hs : U64 → Prop} {ρ μ : U64 → U64} {t off : U64}
    (ht : K.heap t = some .tcb) (hoff : HomeOff off) (hf : ρ (fld t oAFFINITY) ≠ c)
    (hV : Serial.VEq (ownP K) cls ko c hs ρ μ) (k : U64 → E2E.SP) :
    ¬ Serial.Safe (ownP K) cls ko c hs μ (.rd (fld t off) k) :=
  fun h => real_home_not_po hK ht hoff hf hV (safe_rd_po h)

end
end Fl4Proofs.P2.CoreView
