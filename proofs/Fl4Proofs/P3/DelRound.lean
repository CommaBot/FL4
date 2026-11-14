/-
P3 (DESIGN.md §9), CSpace: **one round of `finalise_slot`**: the cap's
finality and `finalise_cap`, on both sides, with the hypotheses for the
object-specific work.

The deletion's states are related by `DState`: the CSpace relations,
`DelInv` and `FinInv`.

* `FinalHyp`: FL4's `is_final_capability` decides the spec's `is_final_cap`,
  and a zombie is final (l4v `zombies_final`). **Proved** (`finalHyp_full`),
  from `FinInv`.

Hypotheses:
* `FinObjHyp`: FL4's `finalise_cap` of an endpoint, notification, reply,
  thread, scheduling context, IRQ handler or arch cap refines the spec's
  `finalise_cap` (TCB suspend, endpoint cancel-all, SC unbind, notification
  unbind, unmap / delete_asid, the IRQ handler's slot): it keeps the
  finalised slot and every other slot's cap, except caps (not zombies)
  that it deletes, returns the spec's remainder (a TCB zombie for a final
  thread cap, else nothing) and cleanup, and keeps `DState`;
* `PPHypD`: the preemption point keeps every cap slot, and matches the
  spec's (Ok or preempted);
* `PostDelHyp`: `post_cap_deletion` of an IRQ handler or IO port cleanup cap
  keeps every cap slot and matches the spec's.

The CNode and zombie parts are proved: a final CNode cap becomes a zombie
over the CNode, a zombie stays. `FinInv` across the zombie writes:
`FinInv.set_zombie` (no other cap names the zombie's object, `ZCond.zf`).
-/
import Fl4Proofs.P3.DelOps
import Fl4Proofs.P3.FinSpec
import Fl4Proofs.P3.FinDefs
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

/-- Related states with `DelInv` and `FinInv`. -/
def DState (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost) : Prop :=
  CRel th (L.mem s) σ G ∧ DelInv th (L.mem s) ∧ FinInv th (L.mem s) σ G

def FinalHyp (th : TypedHeap) : Prop :=
  ∀ (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (c : capability.Cap),
    DState (L := L) th s σ G → AbsSlot th sl → capAt (L.mem s) (cslotAddr sl) = ok c → c ≠ .Null →
    ∃ b, cdt.is_final_capability st s (cslotAddr sl) = ok b ∧
      (NeedsFin c → b = decide (Fl4Spec.isFinalCap' (absCap c) σ)) ∧
      (isZb c = true → Fl4Spec.isFinalCap' (absCap c) σ)

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
  /-- No other slot's cap names the zombie's object. -/
  zf : ∀ y, IsSlot th y → y ≠ x → p.bv ∉ Fl4Spec.objRefs (absCap (capV mem y))

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
    by rw [hcvx]; rfl, ?_, ?_, ?_, fun y hy hyx => final_other hR hP hxs hcx hfin (by rw [objRefs_cnode]; rfl) hy hyx⟩
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
    by rw [hx']; rfl, ?_, ?_, ?_, fun y hy hyx => ?_⟩
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
  · rcases hch y hy hyx with h | ⟨h, -⟩
    · rw [h]; exact final_other hR hP hxs hcx hfin (by rw [objRefs_thread]; rfl) hy hyx
    · rw [h]; exact fun h => h


/-! ## `FinInv` across the zombie writes -/

theorem genObjRefs_zombie (p zt n : U64) :
    Fl4Spec.genObjRefs (absCap (.Zombie p zt n)) = {Fl4Spec.GenObjRef.objRef p.bv} := by
  ext g
  simp [Fl4Spec.genObjRefs, absCap, Fl4Spec.objRefs, Fl4Spec.capIrqs, Fl4Spec.capIrqOpt, Fl4Spec.archCapSetMap]

theorem ovl_zombie_iff {p zt n : U64} {c : Fl4Spec.Cap} :
    Ovl (absCap (.Zombie p zt n)) c ↔ p.bv ∈ Fl4Spec.objRefs c := by
  unfold Ovl
  rw [genObjRefs_zombie, ← Set.nonempty_iff_ne_empty]
  constructor
  · rintro ⟨g, hg1, hg2⟩
    rw [Set.mem_singleton_iff.1 hg1] at hg2
    simpa [Fl4Spec.genObjRefs] using hg2
  · intro h
    exact ⟨_, rfl, by simp [Fl4Spec.genObjRefs, h]⟩

theorem isUt_of_isFrame {c : capability.Cap} (h : isFrame c = true) : isUt c = false := by
  cases c <;> simp_all [isFrame, isUt]

/-- A zombie written over a slot's cap: `FinInv` kept when no other slot's
cap names the zombie's object. -/
theorem FinInv.set_zombie {th : TypedHeap} {mem mem' : U64 → U64} {σ σ' : Fl4Spec.State Unit} {G : MdbGhost}
    (hFI : FinInv th mem σ G) (hM : MdbLinks th mem G) (hK : KSub σ σ')
    {x p zt n : U64} (hx : capV mem' x = .Zombie p zt n)
    (hoth : ∀ y, IsSlot th y → y ≠ x → capV mem' y = capV mem y)
    (hzf : ∀ y, IsSlot th y → y ≠ x → p.bv ∉ Fl4Spec.objRefs (absCap (capV mem y))) :
    FinInv th mem' σ' G := by
  refine ⟨hFI.kt.sub hK, hFI.fm.refresh hM.tree.nodup x
    (fun z hz hzx => hoth z ((hM.members z).1 hz).1 hzx) (fun w hw hwx => ?_)⟩
  have hws := ((hM.members w).1 hw).1
  rw [hx, hoth w hws hwx]
  exact ⟨fun h => hzf w hws hwx (ovl_zombie_iff.1 h), srB_zombie _ _ _ _,
    fun hf => srB_nonut_zombie (isUt_of_isFrame hf) _ _ _⟩

/-- A zombie's object is named by no other slot's cap. -/
theorem FinInv.zombie_alone {th : TypedHeap} {mem : U64 → U64} {σ : Fl4Spec.State Unit} {G : MdbGhost}
    (hFI : FinInv th mem σ G) (hM : MdbLinks th mem G) {x p zt n : U64} (hxs : IsSlot th x)
    (hx : capV mem x = .Zombie p zt n) :
    ∀ y, IsSlot th y → y ≠ x → p.bv ∉ Fl4Spec.objRefs (absCap (capV mem y)) := by
  intro y hy hyx hp
  have hxm : x ∈ G.chains.flatten := (hM.members x).2 ⟨hxs, _, capAt_capV _ _, by rw [hx]; simp⟩
  by_cases hyn : capV mem y = .Null
  · rw [hyn] at hp; exact hp
  have hym : y ∈ G.chains.flatten := (hM.members y).2 ⟨hy, _, capAt_capV _ _, hyn⟩
  exact hFI.fm.zfin x hxm y hym (Ne.symm hyx) (by rw [hx]; rfl) (by rw [hx]; exact ovl_zombie_iff.2 hp)


/-! ## Finality -/

/-- **`FinalHyp` holds**: `DState` carries `FinInv`. -/
theorem finalHyp_full (th : TypedHeap) (hP : Placed th) : FinalHyp (L := L) th := by
  intro s σ G sl c hDS hA hc hcn
  obtain ⟨⟨hR, hV, hM, hC, hI⟩, hD, hF⟩ := hDS
  have hcv := capV_of_capAt hc
  have hx : cslotAddr sl ∈ G.chains.flatten := (hM.members _).2 ⟨hA.isSlot, c, hc, hcn⟩
  have hzf : isZb c = true → Fl4Spec.isFinalCap' (absCap c) σ := by
    intro hz
    have hne : Fl4Spec.genObjRefs (absCap (capV (L.mem s) (cslotAddr sl))) ≠ ∅ := by
      rw [hcv]; exact needsFin_refs (Or.inr (Or.inr hz))
    have := (final_iff hP hR hM hF hA hne).2 fun y hy hyx => hF.fm.zfin _ hx y hy (Ne.symm hyx) (by rw [hcv]; exact hz)
    rwa [hcv] at this
  refine ⟨finF (L.mem s) (cslotAddr sl), is_final_eq s _, fun hN => ?_, hzf⟩
  by_cases hz : isZb c = true
  · rw [decide_eq_true (hzf hz)]
    obtain ⟨p, zt, n, rfl⟩ : ∃ p zt n, c = .Zombie p zt n := by cases c <;> simp [isZb] at hz; exact ⟨_, _, _, rfl⟩
    unfold finF
    simp [hcv, soB_zombie_left, soB_zombie_right]
  · have hz' : isZb c = false := by simpa using hz
    rw [← hcv] at hN hz'
    have hne := needsFin_refs hN
    have e := (finF_iff hP hM hI hF hx hN hz').trans (final_iff hP hR hM hF hA hne).symm
    rw [hcv] at e
    exact Bool.eq_iff_iff.2 (e.trans decide_eq_true_iff.symm)

end

end

end Fl4Proofs.P3
