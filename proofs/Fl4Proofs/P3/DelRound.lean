/-
P3 (DESIGN.md §9), CSpace: **one round of `finalise_slot`**: the cap's
finality and `finalise_cap`, on both sides, with the hypotheses for the
object-specific work.

Hypotheses (for related states with `DelInv`):
* `FinalHyp`: FL4's `is_final_capability` decides the spec's `is_final_cap`
  (an MDB-wide fact, l4v's `mdb_chunked`/`untyped_inc` consequences), and a
  zombie is final (l4v `zombies_final`);
* `FinObjHyp`: FL4's `finalise_cap` of an endpoint, notification, reply,
  thread, scheduling context, IRQ handler or arch cap refines the spec's
  `finalise_cap` (TCB suspend, endpoint cancel-all, SC unbind, notification
  unbind, unmap / delete_asid, the IRQ handler's slot): it keeps the
  finalised slot and every other slot's cap, except caps (not zombies)
  that it deletes, returns the spec's remainder (a TCB zombie for a final
  thread cap, else nothing) and cleanup, and keeps the relations and
  `DelInv`;
* `PPHypD`: the preemption point keeps every cap slot, and matches the
  spec's (Ok or preempted);
* `PostDelHyp`: `post_cap_deletion` of an IRQ handler or IO port cleanup cap
  keeps every cap slot and matches the spec's.

The CNode and zombie parts are proved: a final CNode cap becomes a zombie
over the CNode, a zombie stays.
-/
import Fl4Proofs.P3.DelOps
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-! ## Same-region facts for CNode and thread caps -/

theorem srB_cnode_left {p r gs g : U64} {b : capability.Cap} (h : srB (.CNode p r gs g) b = true) :
    ∃ gs' g', b = .CNode p r gs' g' := by
  have e := srB_eq (.CNode p r gs g) b
  rw [h] at e
  cases b <;> simp [objects.same_region_as] at e
  case CNode p' r' gs' g' =>
    split_ifs at e with h1 h2
    · subst h1 h2; exact ⟨gs', g', rfl⟩
    all_goals simp at e

theorem srB_cnode_right {a : capability.Cap} {p r gs g : U64} (h : srB a (.CNode p r gs g) = true) :
    isUt a = true ∨ ∃ gs' g', a = .CNode p r gs' g' := by
  have e := srB_eq a (.CNode p r gs g)
  rw [h] at e
  cases a <;> simp [objects.same_region_as, isUt] at e ⊢
  case CNode p' r' gs' g' =>
    split_ifs at e with h1 h2
    · subst h1 h2; exact ⟨rfl, rfl⟩
    all_goals simp at e

theorem srB_thread_left {t : U64} {b : capability.Cap} (h : srB (.Thread t) b = true) : b = .Thread t := by
  have e := srB_eq (.Thread t) b
  rw [h] at e
  cases b <;> simp [objects.same_region_as] at e
  case Thread t' => rw [UScalar.eq_of_val_eq e]

theorem srB_thread_right {a : capability.Cap} {t : U64} (h : srB a (.Thread t) = true) :
    isUt a = true ∨ a = .Thread t := by
  have e := srB_eq a (.Thread t)
  rw [h] at e
  cases a <;> simp [objects.same_region_as, isUt] at e ⊢
  case Thread t' => exact (UScalar.eq_of_val_eq e).symm

theorem srB_zombie_right {a : capability.Cap} {p zt n : U64} (h : srB a (.Zombie p zt n) = true) : isUt a = true := by
  by_contra hu
  rw [srB_nonut_zombie (by simpa using hu)] at h; cases h

/-! ## The hypotheses -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- Related states with `DelInv`. -/
def DState (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost) : Prop :=
  CRel th (L.mem s) σ G ∧ DelInv th (L.mem s)

def FinalHyp (th : TypedHeap) : Prop :=
  ∀ (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (c : capability.Cap),
    DState (L := L) th s σ G → AbsSlot th sl → capAt (L.mem s) (cslotAddr sl) = ok c → c ≠ .Null →
    cdt.is_final_capability st s (cslotAddr sl) = ok (decide (Fl4Spec.isFinalCap' (absCap c) σ)) ∧
    (isZb c = true → Fl4Spec.isFinalCap' (absCap c) σ)

/-- The caps whose finalisation is object-specific work. -/
def FinObjKind : capability.Cap → Prop
  | .Endpoint .. | .Notification .. | .Reply .. | .Thread _ | .SchedContext .. | .IrqHandler _
  | .Frame .. | .PageTable .. | .PageDirectory .. | .Pdpt .. | .Pml4 .. | .AsidPool .. | .IoPort .. => True
  | _ => False

/-- The remainder of an object cap's finalisation: a zombie over the TCB
for a final thread cap, else nothing. -/
def finRem (c : capability.Cap) (fin : Bool) : capability.Cap :=
  match c with
  | .Thread t => if fin then .Zombie t capability.ZOMBIE_TCB 5#u64 else .Null
  | _ => .Null

/-- Cleanup caps: none, an IRQ handler, an IO port. -/
def CleanCap : capability.Cap → Prop
  | .Null | .IrqHandler _ | .IoPort .. => True
  | _ => False

def FinObjHyp (th : TypedHeap) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (c : capability.Cap),
    DState (L := L) th s σ G → AbsSlot th sl → capAt (L.mem s) (cslotAddr sl) = ok c → FinObjKind c →
    objects.finalise_cap st arI s a c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) false ⦃ r =>
      r.1.1 = finRem c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) ∧ CleanCap r.1.2 ∧ CapWf r.1.2 ∧
      ∃ σ' G', ((absCap r.1.1, absCap r.1.2), σ') ∈
          (Fl4Spec.finaliseCap (Z := Unit) (absCap c) (decide (Fl4Spec.isFinalCap' (absCap c) σ)) σ).1 ∧
        DState (L := L) th r.2.1 σ' G' ∧ capV (L.mem r.2.1) (cslotAddr sl) = c ∧
        ∀ y, IsSlot th y → y ≠ cslotAddr sl → capV (L.mem r.2.1) y = capV (L.mem s) y ∨
          (capV (L.mem r.2.1) y = .Null ∧ isZb (capV (L.mem s) y) = false) ⦄

def PPHypD (th : TypedHeap) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost), DState (L := L) th s σ G →
    sched.preemption_point st arI s a ⦃ r =>
      SlotsSame th (L.mem s) (L.mem r.2.1) ∧ ∃ σ',
        ((r.1 = .Ok () ∧ (.ok (), σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1) ∨
          (r.1 = .Err .Preempted ∧ (.error (), σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1)) ∧
        CRel th (L.mem r.2.1) σ' G ⦄

def PostDelHyp (th : TypedHeap) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (cl : capability.Cap),
    DState (L := L) th s σ G → CleanCap cl → cl ≠ .Null → CapWf cl →
    objects.post_cap_deletion st arI s a cl ⦃ r =>
      SlotsSame th (L.mem s) (L.mem r.1) ∧ ∃ σ',
        ((), σ') ∈ (Fl4Spec.postCapDeletion (Z := Unit) (absCap cl) σ).1 ∧ CRel th (L.mem r.1) σ' G ⦄

end

/-! ## A zombie remainder's conditions -/

/-- What writing the zombie `Z` into `x` needs (`set_zombie`). -/
structure ZCond (th : TypedHeap) (mem : U64 → U64) (G : MdbGhost) (x p zt n : U64) : Prop where
  wf : CapWf (.Zombie p zt n)
  enc : EncWf (.Zombie p zt n)
  zok : ZOK th p zt n
  zu : ∀ y, IsSlot th y → y ≠ x → ∀ p' zt' n', capV mem y = .Zombie p' zt' n' → p' ≠ p
  bx : isBadged (capV mem x) = false
  bf : badgeF (capV mem x) = 0#u64
  h1 : ∀ y ∈ G.chains.flatten, y ≠ x → srB (capV mem y) (.Zombie p zt n) = srB (capV mem y) (capV mem x)
  h2 : ∀ y ∈ G.chains.flatten, y ≠ x → srB (capV mem x) (capV mem y) = false
  home : HomeZ mem x → p = x

theorem shl_radix {r : U64} (hr : r.val < 64) : ∃ z : U64, (1#u64 <<< (r &&& 63#u64)) = ok z ∧ z.val = 2 ^ r.val := by
  have h63 : (r &&& 63#u64).val = r.val := by
    have : (r &&& 63#u64).val = r.val % 64 := by simp; exact Nat.and_two_pow_sub_one_eq_mod r.val 6
    rw [this]; exact Nat.mod_eq_of_lt hr
  obtain ⟨z, hz, hv, -⟩ := spec_exists (U64.ShiftLeft_spec (x := 1#u64) (y := r &&& 63#u64) (by rw [h63]; omega))
  refine ⟨z, hz, ?_⟩
  rw [hv, h63, Nat.shiftLeft_eq]
  have h1 : (1#u64 : U64).val = 1 := rfl
  rw [h1, Nat.one_mul]
  exact Nat.mod_eq_of_lt (by have := Nat.pow_lt_pow_right (by decide : 1 < 2) hr; simpa [U64.size, U64.numBits] using this)

/-! ## Zombie conditions from finality -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem objRefs_cnode (p r gs g : U64) : Fl4Spec.objRefs (absCap (.CNode p r gs g)) = {p.bv} := rfl
theorem objRefs_thread (t : U64) : Fl4Spec.objRefs (absCap (.Thread t)) = {t.bv} := rfl
theorem objRefs_zombie (p zt n : U64) : Fl4Spec.objRefs (absCap (.Zombie p zt n)) = {p.bv} := rfl

/-- A final cap's object `o` is in no other slot's CNode, thread or zombie cap. -/
theorem final_not {th : TypedHeap} {s : S} {σ : Fl4Spec.State Unit} (hR : StateRel th (L.mem s) σ)
    (hP : Placed th) {xsl : Fl4Spec.CslotPtr} (hxs : AbsSlot th xsl) {cx : capability.Cap}
    (hcx : capAt (L.mem s) (cslotAddr xsl) = ok cx) (hfin : Fl4Spec.isFinalCap' (absCap cx) σ)
    {o : U64} (ho : o.bv ∈ Fl4Spec.objRefs (absCap cx)) {y : U64} (hy : IsSlot th y) (hyx : y ≠ cslotAddr xsl) :
    (∀ r gs g, capV (L.mem s) y ≠ .CNode o r gs g) ∧ capV (L.mem s) y ≠ .Thread o ∧
      (∀ zt n, capV (L.mem s) y ≠ .Zombie o zt n) := by
  have h := final_other hR hP hxs hcx hfin ho hy hyx
  refine ⟨fun r gs g e => ?_, fun e => ?_, fun zt n e => ?_⟩ <;> rw [e] at h <;> exact h rfl

theorem cnode_zcond {th : TypedHeap} {s : S} {σ : Fl4Spec.State Unit} {G : MdbGhost}
    (hR : StateRel th (L.mem s) σ) (hP : Placed th) (hM : MdbLinks th (L.mem s) G)
    {xsl : Fl4Spec.CslotPtr} (hxs : AbsSlot th xsl) {p r gs g : U64}
    (hcx : capAt (L.mem s) (cslotAddr xsl) = ok (.CNode p r gs g))
    (hfin : Fl4Spec.isFinalCap' (absCap (.CNode p r gs g)) σ)
    (hcv : th p = some (.cnode r.val)) (hr : r.val < 64) (hcan : Canonical p) (z : U64) (hz : z.val = 2 ^ r.val) :
    ZCond th (L.mem s) G (cslotAddr xsl) p r z := by
  have hcvx := capV_of_capAt hcx
  have hfn := fun {y} (hy : IsSlot th y) (hyx : y ≠ cslotAddr xsl) =>
    final_not hR hP hxs hcx hfin (o := p) (by rw [objRefs_cnode]; rfl) hy hyx
  have hslot : ∀ y, y ∈ G.chains.flatten → IsSlot th y := fun y h => ((hM.members y).1 h).1
  have hr65 : r.val ≠ 65 := by omega
  refine ⟨Or.inl (by omega), ⟨hcan, by omega⟩, Or.inr ⟨hr65, hcv, by omega⟩, ?_, by rw [hcvx]; rfl,
    by rw [hcvx]; rfl, ?_, ?_, ?_⟩
  · intro y hy hyx p' zt' n' e
    rintro rfl
    exact (hfn hy hyx).2.2 zt' n' e
  · intro y hy hyx
    rw [hcvx]
    cases hu : isUt (capV (L.mem s) y)
    · rw [srB_nonut_zombie hu]
      symm
      by_contra hb
      rcases srB_cnode_right (by simpa using hb) with h | ⟨gs', g', e⟩
      · rw [hu] at h; cases h
      · exact (hfn (hslot y hy) hyx).1 r gs' g' e
    · obtain ⟨q, sb, fi, d, e⟩ : ∃ q sb fi d, capV (L.mem s) y = .Untyped q sb fi d := by
        cases h : capV (L.mem s) y <;> rw [h] at hu <;> simp [isUt] at hu
        exact ⟨_, _, _, _, rfl⟩
      rw [e]; exact srB_ut_zombie_cnode q sb fi d p r gs g z hr65
  · intro y hy hyx
    rw [hcvx]
    by_contra hb
    obtain ⟨gs', g', e⟩ := srB_cnode_left (by simpa using hb)
    exact (hfn (hslot y hy) hyx).1 r gs' g' e
  · rintro ⟨zt, n, e⟩; rw [hcvx] at e; cases e

theorem thread_zcond {th : TypedHeap} {s : S} {σ : Fl4Spec.State Unit} {mem' : U64 → U64} {G' : MdbGhost}
    (hR : StateRel th (L.mem s) σ) (hP : Placed th) (hM' : MdbLinks th mem' G')
    {xsl : Fl4Spec.CslotPtr} (hxs : AbsSlot th xsl) {t : U64}
    (hcx : capAt (L.mem s) (cslotAddr xsl) = ok (.Thread t))
    (hfin : Fl4Spec.isFinalCap' (absCap (.Thread t)) σ) (hcv : th t = some .tcb) (hcan : Canonical t)
    (hx' : capV mem' (cslotAddr xsl) = .Thread t)
    (hch : ∀ y, IsSlot th y → y ≠ cslotAddr xsl → capV mem' y = capV (L.mem s) y ∨
      (capV mem' y = .Null ∧ isZb (capV (L.mem s) y) = false)) :
    ZCond th mem' G' (cslotAddr xsl) t capability.ZOMBIE_TCB 5#u64 := by
  have hfn := fun {y} (hy : IsSlot th y) (hyx : y ≠ cslotAddr xsl) =>
    final_not hR hP hxs hcx hfin (o := t) (by rw [objRefs_thread]; rfl) hy hyx
  have hslot : ∀ y, y ∈ G'.chains.flatten → IsSlot th y := fun y h => ((hM'.members y).1 h).1
  have h65 := zombie_tcb_val
  refine ⟨Or.inr h65, ⟨hcan, by omega⟩, Or.inl ⟨h65, hcv, by decide⟩, ?_, by rw [hx']; rfl,
    by rw [hx']; rfl, ?_, ?_, ?_⟩
  · intro y hy hyx p' zt' n' e
    rintro rfl
    rcases hch y hy hyx with h | ⟨h, -⟩
    · rw [h] at e; exact (hfn hy hyx).2.2 zt' n' e
    · rw [h] at e; cases e
  · intro y hy hyx
    rw [hx']
    rcases hch y (hslot y hy) hyx with h | ⟨h, -⟩
    · rw [h]
      cases hu : isUt (capV (L.mem s) y)
      · rw [srB_nonut_zombie hu]
        symm
        by_contra hb
        rcases srB_thread_right (by simpa using hb) with h' | e
        · rw [hu] at h'; cases h'
        · exact (hfn (hslot y hy) hyx).2.1 e
      · obtain ⟨q, sb, fi, d, e⟩ : ∃ q sb fi d, capV (L.mem s) y = .Untyped q sb fi d := by
          cases h : capV (L.mem s) y <;> rw [h] at hu <;> simp [isUt] at hu
          exact ⟨_, _, _, _, rfl⟩
        rw [e]; exact srB_ut_zombie_tcb q sb fi d t 5#u64
    · rw [h, srB_null, srB_null]
  · intro y hy hyx
    rw [hx']
    by_contra hb
    have e := srB_thread_left (by simpa using hb)
    rcases hch y (hslot y hy) hyx with h | ⟨h, -⟩
    · rw [h] at e; exact (hfn (hslot y hy) hyx).2.1 e
    · rw [h] at e; cases e
  · rintro ⟨zt, n, e⟩; rw [hx'] at e; cases e

end

end

end Fl4Proofs.P3
