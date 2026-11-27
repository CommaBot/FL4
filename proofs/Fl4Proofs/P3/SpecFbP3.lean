/-
P3 (issue #16, fb3e): **the frame batch keeps `P3 N`** (`UtInv''` and the
IRQ-node fact; spec side only), and with it the full `p3_fl4ArchPerform`.

The batch is run with the carried fact `FbOKN` (its decode's: the destination
CNode cap sits in a slot). Every write of an entry is to a slot holding a
frame cap or a null cap (COPY_MAP's `cap_insert` into the emptied
destination, the map's and the deferred unmap's `set_cap` over the frame,
the frame delete's `empty_slot`), so the slot holding the CNode cap is never
written (`fbk_*`) and `FbOKN` is kept. At COPY_MAP's `cap_insert`:
* `CI3`: the inserted cap is the source frame cap's derived, masked copy
  (`RefRel`: the same frame);
* `PosOK` of the destination: the destination lookup ran at this state
  through the CNode cap in its slot (`okv_lookupSlotForCnodeOpN`: a
  `DestRefV` destination).
-/
import Fl4Proofs.P3.SpecFbM
open Classical

namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

variable {N : Irq → ObjRef}

/-! ## Writes that keep a slot -/

theorem fbk_setCap {c : Cap} {sl x : CslotPtr} {cx : Cap} (hx : x ≠ sl) :
    HV (fun w => w.2.1 x = some cx) (fun w => w.2.1 x = some cx) (setCap (Z := Unit) c sl) := by
  intro σ hσ y hy
  have e := hv_setCap c sl (uV σ) σ rfl y hy
  rw [e]; simp only [vCap, Function.update_apply, if_neg hx]; exact hσ

theorem fbk_emptySlot {sl x : CslotPtr} {info cx : Cap} (hx : x ≠ sl) :
    HV (fun w => w.2.1 x = some cx) (fun w => w.2.1 x = some cx) (emptySlot (Z := Unit) sl info) := by
  intro σ hσ y hy
  rcases emptySlot_view sl info (uV σ) σ rfl y hy with ⟨e, -⟩ | e
  · rw [e]; exact hσ
  · rw [e]; simp only [vEs, vCap, vOrig, vCdt, Function.update_apply, if_neg hx]; exact hσ

theorem fbk_pageMap {c : Cap} {sl x : CslotPtr} {en : VMPageEntry × ObjRef} {vs : ObjRef} {cx : Cap} (hx : x ≠ sl) :
    HV (fun w => w.2.1 x = some cx) (fun w => w.2.1 x = some cx)
      (performPageInvocation (Z := Unit) (.pageMap c sl en vs)) := by
  intro σ hσ y hy
  simp only [performPageInvocation] at hy
  obtain ⟨z1, hz1, hy⟩ := hy
  have e1 := hv_setCap c sl (uV σ) σ rfl z1 hz1
  have e2 : uV y.2 = uV z1.2 := (?_ : UK (uV z1.2) _) z1.2 rfl y hy
  · rw [e2, e1]; simp only [vCap, Function.update_apply, if_neg hx]; exact hσ
  · uk_auto

theorem fbkI_setCap {c : Cap} {sl x : CslotPtr} {cx : Cap} (hx : x ≠ sl) :
    IK (fun t => capAt t x = some cx) (setCap (Z := Unit) c sl) :=
  fun s hs y hy => fbk_setCap hx s hs y hy

theorem fbkI_uk {x : CslotPtr} {cx : Cap} {α : Type} {m : NonDet (State Unit) α} (h : ∀ v, UK v m) :
    IK (fun t => capAt t x = some cx) m := fun s hs y hy => by
  have e := congrArg (fun w : UView => w.2.1 x) (h (uV s) s rfl y hy)
  exact e.trans hs

theorem fb_mem_liftE {ε α : Type} {m : NonDet (State Unit) α} {s : State Unit} {x : α × State Unit}
    (hx : x ∈ (m s).1) : ((.ok x.1, x.2) : Except ε α × State Unit) ∈ ((NonDetE.liftE (ε := ε) m).run s).1 := by
  unfold NonDetE.liftE; rw [ExceptT.run_lift]; exact ⟨x, hx, rfl⟩

theorem fb_mem_archPage {pi : PageInvocation} {s : State Unit} {x : List Data × State Unit}
    (hx : x ∈ (performPageInvocation (Z := Unit) pi s).1) :
    ((.ok x.1, x.2) : Except Unit (List Data) × State Unit) ∈ ((archPerformInvocation (Z := Unit) (.invokePage pi)).run s).1 := by
  simp only [archPerformInvocation]; exact fb_mem_liftE hx

/-- `empty_slot` only nulls the emptied slot. -/
theorem fb_emptySlot_nul {sl : CslotPtr} {info : Cap} {s : State Unit} {x : Unit × State Unit}
    (hx : x ∈ (emptySlot (Z := Unit) sl info s).1) :
    ∀ sl', (uV x.2).2.1 sl' = (uV s).2.1 sl' ∨ (sl' = sl ∧ (uV x.2).2.1 sl' = some .nullCap) := by
  intro sl'
  rcases emptySlot_view sl info (uV s) s rfl x hx with ⟨e, -⟩ | e
  · rw [e]; exact Or.inl rfl
  · rw [e]
    by_cases h : sl' = sl
    · subst h; right; simp [vEs, vCap, vOrig, vCdt]
    · left; simp only [vEs, vCap, vOrig, vCdt, Function.update_apply, if_neg h]

theorem fbk_ne {c c' : Cap} (hc : isCnodeCap c = true) (hf : IsFrameCap c' ∨ c' = .nullCap) : c' ≠ c := by
  rintro rfl
  rcases hf with hf | rfl
  · cases c' <;> simp_all [isCnodeCap, IsFrameCap]
  · simp [isCnodeCap] at hc

/-- The slot holding the CNode cap is not a slot holding a frame or null cap. -/
theorem fbk_slot_ne {w : UView} {x sl : CslotPtr} {c c' : Cap} (hc : isCnodeCap c = true) (hx : w.2.1 x = some c)
    (hsl : w.2.1 sl = some c') (hf : IsFrameCap c' ∨ c' = .nullCap) : x ≠ sl := by
  rintro rfl
  rw [hx] at hsl
  exact fbk_ne hc hf (Option.some.inj hsl).symm

/-! ## The batch -/

/-- The carried family. -/
abbrev FbQ (N : Irq → ObjRef) (b : Fl4FrameBatchInvocation) (s : State Unit) : Prop := P3 N s ∧ FbOKN (uV s) b

theorem fbq_uk {b : Fl4FrameBatchInvocation} {α : Type} {m : NonDet (State Unit) α} (h : ∀ v, UK v m) :
    IK (FbQ N b) m := fun s hs x hx => by
  have e := h (uV s) s rfl x hx
  exact ⟨p3_of_view e hs.1, by rw [e]; exact hs.2⟩

/-- A write over a slot holding a frame or null cap keeps `FbOKN`. -/
theorem fbq_root {b : Fl4FrameBatchInvocation} {α : Type} {m : NonDet (State Unit) α} {s : State Unit}
    {sl : CslotPtr} {c' : Cap} (hs : FbOKN (uV s) b) (hsl : capAt s sl = some c') (hf : IsFrameCap c' ∨ c' = .nullCap)
    (hk : ∀ x cx, x ≠ sl → HV (fun w => w.2.1 x = some cx) (fun w => w.2.1 x = some cx) m) :
    ∀ y ∈ (m s).1, FbOKN (uV y.2) b := by
  intro y hy
  obtain ⟨hcn, x, hx⟩ := hs
  exact ⟨hcn, x, hk x _ (fbk_slot_ne hcn hx hsl hf) s hx y hy⟩

theorem fb_frame_refRel {dev : Bool} {p : ObjRef} {R : CapRights} {mt : VMMapType} {sz : VMPageSize}
    {m : Option (Asid × VSpaceRef)} {r : CapRights} {src : CslotPtr} {c : Cap} {s t : State Unit}
    (h : (.ok c, t) ∈ ((deriveCap (Z := Unit) src (maskCap r (.archObjectCap (.pageCap dev p R mt sz m)))).run s).1) :
    RefRel (.archObjectCap (.pageCap dev p R mt sz m)) c ∧ IsFrameCap c := by
  simp only [maskCap, capRightsUpdate, acapRightsUpdate, deriveCap, archDeriveCap] at h
  obtain ⟨e1, -⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h)
  simp only [Except.ok.injEq] at e1
  subst e1
  exact ⟨⟨fun x hx => hx, rfl, fun _ _ _ e => (by cases e), fun _ _ _ e => (by cases e),
    fun _ _ _ _ e => (by cases e)⟩, trivial⟩

/-- **The batch keeps `FbQ N b` and a view predicate `RV`** given `RV` across each write of an entry at its
run-time facts (the COPY_MAP destination a `DestRefV` slot, the slots the other writes hit holding frames). -/
theorem fbq_run {RV : UView → Prop} (b : Fl4FrameBatchInvocation)
    (hci : ∀ s c src dest c0, FbQ N b s → RV (uV s) → DestRefV (uV s) dest → capAt s dest = some .nullCap →
      capAt s src = some c0 → isPageCap c0 = true → IsFrameCap c → ∀ x ∈ (capInsert (Z := Unit) c src dest s).1,
      RV (uV x.2))
    (hpp : ∀ s pi sl dev p R mt sz m, FbQ N b s → RV (uV s) → ArchSpecOKN (uV s) (.invokePage pi) →
      PgSl sl (.invokePage pi) → capAt s sl = some (.archObjectCap (.pageCap dev p R mt sz m)) →
      ∀ x ∈ (performPageInvocation (Z := Unit) pi s).1, RV (uV x.2))
    (hes : ∀ s sl dev p R mt sz m, FbQ N b s → RV (uV s) → capAt s sl = some (.archObjectCap (.pageCap dev p R mt sz m)) →
      ∀ x ∈ (emptySlot (Z := Unit) sl .nullCap s).1, RV (uV x.2))
    (hset : ∀ s dev p R mt sz m sl, FbQ N b s → RV (uV s) →
      capAt s sl = some (.archObjectCap (.pageCap dev p R mt sz m)) →
      ∀ x ∈ (setCap (Z := Unit) (.archObjectCap (.pageCap dev p R .vmNoMap sz none)) sl s).1, RV (uV x.2)) :
    ∀ σ, FbQ N b σ → RV (uV σ) → ∀ y ∈ (performFrameBatch (Z := Unit) b σ).1, FbQ N b y.2 ∧ RV (uV y.2) := by
  intro σ hσ hr y hy
  have hu : ∀ {α : Type} {m : NonDet (State Unit) α}, (∀ v, UK v m) → IK (fun s => FbQ N b s ∧ RV (uV s)) m :=
    fun h s hs x hx => by
      have e := h (uV s) s rfl x hx
      exact ⟨fbq_uk h s hs.1 x hx, by rw [e]; exact hs.2⟩
  refine ik_performFrameBatchX (P := fun s => FbQ N b s ∧ RV (uV s)) (fun w => ik_fbEntryX_of b w
    fbx_lookupTargetSlot fbx_lookupSourceSlot fbx_ensureEmpty fbx_deriveCap ?_ ?_ ?_
    (fun _ _ _ _ => hu fun v => uk_unmapPageUnflushed _ _ _ _) ?_) (hu fun v => uk_flushAll _ _) σ ⟨hσ, hr⟩ y hy
  · -- COPY_MAP's `cap_insert`
    intro s c src dest c0 ⟨hs, hrs⟩ hfc hdest hnull hc0 hpg hder x hx
    have hD : DestRefV (uV s) dest :=
      okv_lookupSlotForCnodeOpN false _ _ _ hs.2.2 s rfl dest s hdest
    refine ⟨⟨?_, ?_⟩, hci s c src dest c0 hs hrs hD hnull hc0 hpg hfc x hx⟩
    · obtain ⟨dev, p, R, mt, sz, m, rfl⟩ := fbx_frame_of_isPageCap hpg
      have hR := (fb_frame_refRel hder).1
      exact hv_capInsert3 c src dest s ⟨hs.1, ⟨_, hc0, Or.inr hR⟩, posOK_of_destRef hs.1.1.2 hD⟩ x hx
    · have hnu : ∀ d b n f, c ≠ .untypedCap d b n f := fun d b n f e => by rw [e] at hfc; exact hfc
      exact fbq_root hs.2 hnull (Or.inr rfl) (fun x' cx hx' => hv_capInsert_keep c hnu src dest x' hx' cx) x hx
  · -- the map
    intro sl v
    refine ik_fbMapF2 b sl v (fun _ _ _ _ _ _ => hu fun v => uk_decodePageInvocation _ _ _ _ _) ?_
    intro s pi dev p R mt sz m ⟨hs, hrs⟩ hok hpg hcap x hx
    refine ⟨⟨p3_performPageInvocation pi s ⟨hs.1, hok⟩ x hx, ?_⟩, hpp s pi sl dev p R mt sz m hs hrs hok hpg hcap x hx⟩
    cases pi with
    | pageMap c sl' en vs =>
      simp only [PgSl] at hpg
      subst hpg
      exact fbq_root hs.2 hcap (Or.inl trivial) (fun x' cx hx' => fbk_pageMap hx') x hx
    | pageUnmap a sl' =>
      have hsl : capAt s sl' = some (.archObjectCap a) := hok
      obtain ⟨hcn, x0, hx0⟩ := hs.2
      cases a with
      | pageCap dev' p' R' mt' sz' mp' =>
        have hne := fbk_slot_ne hcn hx0 hsl (Or.inl trivial)
        refine ⟨hcn, x0, ?_⟩
        refine (?_ : IK (fun t => capAt t x0 = some b.destCnode) _) s hx0 x hx
        cases mp' <;> simp only [performPageInvocation, performPageInvocationUnmap] <;>
          repeat' (first | exact fbkI_setCap hne | exact fbkI_uk (fun v => uk_unmapPage _ _ _ _) | ik_step0 | ik_unfold)
      | _ => all_goals exact (hx : False).elim
    | pageGetAddr _ => exact ((fbq_uk (b := b) (N := N) fun v => by simp only [performPageInvocation]; uk_auto) s hs x hx).2
  · -- the frame delete
    intro sl
    refine ik_fbDelXF sl (fun _ => hu fun v => uk_isFinalCap _) (fun _ _ => hu fun v => uk_archFinaliseCap _ _) ?_
    intro s dev p R mt sz m ⟨hs, hrs⟩ hc x hx
    refine ⟨⟨⟨hv_emptySlotN sl _ s ⟨hs.1.1, fun c hc' => ?_⟩ x hx, io_emptySlot sl _ s hs.1.2 x hx⟩, ?_⟩,
      hes s sl dev p R mt sz m hs hrs hc x hx⟩
    · have : c = .archObjectCap (.pageCap dev p R mt sz m) := Option.some.inj (hc'.symm.trans hc)
      subst this
      exact safeDel_of_sRefs (by simp [sRefs])
    · exact fbq_root hs.2 hc (Or.inl trivial) (fun x' cx hx' => fbk_emptySlot hx') x hx
  · -- the deferred unmap's `set_cap`
    intro s dev p R mt sz m sl ⟨hs, hrs⟩ hc0 x hx
    exact ⟨⟨hv_setCapRE (c0 := .archObjectCap (.pageCap dev p R mt sz m)) (nnu_arch (.pageCap dev p R .vmNoMap sz none)) sl s
        ⟨hs.1, hc0, refEq_arch rfl rfl⟩ x hx,
      fbq_root hs.2 hc0 (Or.inl trivial) (fun x' cx hx' => fbk_setCap hx') x hx⟩,
      hset s dev p R mt sz m sl hs hrs hc0 x hx⟩

/-- **The frame batch keeps `P3 N`** from its decode's `FbOKN`. -/
theorem p3_performFrameBatch (b : Fl4FrameBatchInvocation) (σ : State Unit) (hI : P3 N σ) (hok : FbOKN (uV σ) b) :
    ∀ y ∈ (performFrameBatch (Z := Unit) b σ).1, P3 N y.2 := fun y hy =>
  (fbq_run (RV := fun _ => True) b (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial) σ ⟨hI, hok⟩ trivial y hy).1.1

/-- **Every arch invocation but `invokeASIDControl` keeps `P3 N`** (the frame batch included). -/
theorem p3_fl4ArchPerform (ai : Fl4ArchInvocation) (hm : ∀ a, ai ≠ .spec (.invokeASIDControl a)) (σ : State Unit)
    (hI : P3 N σ) (hok : ArchOKN (uV σ) ai) :
    ∀ y ∈ ((fl4ArchPerformInvocation (Z := Unit) ai).run σ).1, P3 N y.2 := by
  cases ai with
  | frameBatch b =>
    intro y hy
    simp only [fl4ArchPerformInvocation] at hy
    obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
    exact p3_performFrameBatch b σ hI hok x hx
  | _ => exact p3_fl4ArchPerform0 _ hm (fun _ e => by cases e) σ hI hok

end

end Fl4Proofs.P3.SInvU
