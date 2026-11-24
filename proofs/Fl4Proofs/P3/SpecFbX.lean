/-
P3 (issue #16, fb3c): **the frame batch without `rec_del`** (spec side only).

Every `cap_delete` in a frame batch (`fbEntry`: COPY_MAP's rollback, DELETE)
deletes a slot that holds a frame cap at that point. There `rec_del` takes
one round: `finalise_cap` of a frame (`arch_finalise_cap`: `unmap_page` if
mapped) leaves a Null remainder, which is removable, so no Zombie, no
recursion, no preemption point; then `empty_slot`.

* `fbDelX slot`: that round written out (read the cap; a frame: `is_final_cap`,
  `arch_finalise_cap`, `empty_slot slot Null`; anything else: `fail`, i.e. no
  outcome). **`capDelete_subX`**: at a state where `slot` holds a frame cap,
  every outcome of `capDelete slot` is an outcome of `fbDelX slot` (in
  particular `ok`: such a delete never throws).
* `fbEntryX` / `fbRunX` / `performFrameBatchX`: `fbEntry` / `fbRun` /
  `performFrameBatch` with `fbDelX` for `capDelete`. **`fbEntry_subX`**,
  **`performFrameBatch_subX`**: outcome inclusion (the slot facts carried
  along: `get_cap` reads, the unlessE frame check, `derive_cap` of a frame,
  `cap_insert` writes the destination, `fbMap`'s errors keep the cap view,
  the deferred unmap's `set_cap`).
* So a family's `IK P` of the batch follows from `IK P` of `fbEntryX`, whose
  cone has no least fixed point (`ike_fbEntry_ofX`, `ik_performFrameBatch_ofX`).
-/
import Fl4Proofs.P3.SpecInvFbK
import Fl4Proofs.P3.SpecInvUtC
import Fl4Proofs.P3.SpecInvUtF1
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Membership helpers -/

theorem fbx_mem_bindE {σ ε α β : Type} {m : NonDetE σ ε α} {f : α → NonDetE σ ε β} {s : σ}
    {x : Except ε β × σ} (hx : x ∈ ((m >>= f).run s).1) :
    ∃ z ∈ (m.run s).1, (∃ a, z.1 = .ok a ∧ x ∈ ((f a).run z.2).1) ∨ (∃ e, z.1 = .error e ∧ x = (.error e, z.2)) := by
  rw [ExceptT.run_bind] at hx
  obtain ⟨z, hz, hxz⟩ := hx
  refine ⟨z, hz, ?_⟩
  obtain ⟨r, s'⟩ := z
  cases r with
  | ok a => exact Or.inl ⟨a, rfl, hxz⟩
  | error e => exact Or.inr ⟨e, rfl, Set.mem_singleton_iff.1 hxz⟩

theorem fbx_mem_liftE {σ ε α : Type} {m : NonDet σ α} {s : σ} {y : Except ε α × σ}
    (h : y ∈ ((NonDetE.liftE (ε := ε) m).run s).1) : ∃ x ∈ (m s).1, y = (.ok x.1, x.2) := by
  unfold NonDetE.liftE at h
  rw [ExceptT.run_lift] at h
  obtain ⟨x, hx, hy⟩ := h
  exact ⟨x, hx, Set.mem_singleton_iff.1 hy⟩

/-- Inclusion through a bind whose first step is the same, the continuations
included at the outcomes satisfying `Q`. -/
theorem fbx_sub_bindE {σ ε α β : Type} {m : NonDetE σ ε α} {f f' : α → NonDetE σ ε β} {s : σ}
    (Q : α → σ → Prop) (hQ : ∀ a t, (.ok a, t) ∈ (m.run s).1 → Q a t)
    (hf : ∀ a t, Q a t → ∀ y ∈ ((f a).run t).1, y ∈ ((f' a).run t).1) :
    ∀ y ∈ ((m >>= f).run s).1, y ∈ ((m >>= f').run s).1 := by
  intro y hy
  rw [ExceptT.run_bind] at hy ⊢
  obtain ⟨z, hz, hyz⟩ := hy
  refine ⟨z, hz, ?_⟩
  obtain ⟨r, t⟩ := z
  cases r with
  | ok a => exact hf a t (hQ a t hz) y hyz
  | error e => exact hyz

theorem fbx_sub_handleE {σ ε ε' α : Type} {m m' : NonDetE σ ε α} {h : ε → NonDetE σ ε' α} {s : σ}
    (hm : ∀ y ∈ (m.run s).1, y ∈ (m'.run s).1) :
    ∀ y ∈ ((NonDetE.handleE m h).run s).1, y ∈ ((NonDetE.handleE m' h).run s).1 := by
  intro y hy
  unfold NonDetE.handleE at hy ⊢
  rw [ExceptT.run_mk] at hy ⊢
  obtain ⟨z, hz, hyz⟩ := hy
  exact ⟨z, hm z hz, hyz⟩

theorem fbx_sub_catch {σ ε α : Type} {m m' : NonDetE σ ε α} {h : ε → NonDet σ α} {s : σ}
    (hm : ∀ y ∈ (m.run s).1, y ∈ (m'.run s).1) :
    ∀ y ∈ ((NonDetE.catch m h) s).1, y ∈ ((NonDetE.catch m' h) s).1 := by
  intro y hy
  unfold NonDetE.catch at hy ⊢
  obtain ⟨z, hz, hyz⟩ := hy
  exact ⟨z, hm z hz, hyz⟩

theorem fbx_sub_liftE {σ ε α : Type} {m m' : NonDet σ α} {s : σ} (hm : ∀ y ∈ (m s).1, y ∈ (m' s).1) :
    ∀ y ∈ ((NonDetE.liftE (ε := ε) m).run s).1, y ∈ ((NonDetE.liftE (ε := ε) m').run s).1 := by
  intro y hy
  unfold NonDetE.liftE at hy ⊢
  rw [ExceptT.run_lift] at hy ⊢
  obtain ⟨z, hz, hyz⟩ := hy
  exact ⟨z, hm z hz, hyz⟩

/-! ## One round of `rec_del` on a frame -/

/-- `get_cap` of a slot holding `c` has the outcome `(c, σ)`. -/
theorem fbx_getCap_of_capAt {sl : CslotPtr} {σ : State Unit} {c : Cap} (hc : capAt σ sl = some c) :
    (c, σ) ∈ (getCap (Z := Unit) sl σ).1 := by
  obtain ⟨o, r⟩ := sl
  unfold capAt at hc
  revert hc
  cases hk : σ.kheap o with
  | none => intro hc; cases hc
  | some obj =>
    intro hc
    have hg : (obj, σ) ∈ (getObject (Z := Unit) o σ).1 := by
      unfold getObject NonDet.getsThe
      have : readObject (Z := Unit) o σ = some obj := hk
      rw [this]; exact Set.mem_singleton _
    unfold getCap
    refine ⟨(obj, σ), hg, ?_⟩
    cases obj with
    | cnode sz cn =>
      dsimp only at hc ⊢
      rw [capView_cnode] at hc
      split_ifs at hc with hwf
      · refine ⟨((), σ), ⟨hwf, rfl⟩, ?_⟩
        first
          | (show (c, σ) ∈ (NonDet.assertOpt (cn r) σ).1; rw [hc]; exact Set.mem_singleton _)
          | (refine ⟨(cn, σ), Set.mem_singleton _, ?_⟩
             show (c, σ) ∈ (NonDet.assertOpt (cn r) σ).1; rw [hc]; exact Set.mem_singleton _)
    | tcb t =>
      dsimp only at hc ⊢
      rw [capView_tcb] at hc
      refine ⟨(tcbCnodeMap t, σ), Set.mem_singleton _, ?_⟩
      show (c, σ) ∈ (NonDet.assertOpt (tcbCnodeMap t r) σ).1
      rw [hc]; exact Set.mem_singleton _
    | _ => simp [capView] at hc

/-- A frame cap. -/
def IsFrameCap : Cap → Prop
  | .archObjectCap (.pageCap ..) => True
  | _ => False

theorem isFrameCap_of_isPageCap {c : Cap} (h : isPageCap c = true) : IsFrameCap c := by
  cases c <;> simp [isPageCap] at h
  case archObjectCap a => cases a <;> simp [isPageCap] at h; exact trivial

/-- `cap_delete` of a frame, written out. -/
def fbDelX (slot : CslotPtr) : NonDetE (State Unit) Unit Unit :=
  NonDetE.liftE (do
    let c ← getCap (Z := Unit) slot
    match c with
    | .archObjectCap (.pageCap dev p R mt sz m) => do
        let fin ← isFinalCap (Z := Unit) (.archObjectCap (.pageCap dev p R mt sz m))
        let _ ← archFinaliseCap (Z := Unit) (.pageCap dev p R mt sz m) fin
        emptySlot (Z := Unit) slot .nullCap
    | _ => NonDet.fail)

theorem archFinaliseCap_frame {dev : Bool} {p : ObjRef} {R : CapRights} {mt : VMMapType} {sz : VMPageSize}
    {m : Option (Asid × VSpaceRef)} {fin : Bool} {s : State Unit} {y : (Cap × Cap) × State Unit}
    (hy : y ∈ (archFinaliseCap (Z := Unit) (.pageCap dev p R mt sz m) fin s).1) : y.1 = (.nullCap, .nullCap) := by
  rcases m with _ | ⟨a, v⟩ <;> cases fin <;> simp only [archFinaliseCap] at hy
  all_goals first
    | exact congrArg Prod.fst (Set.mem_singleton_iff.1 hy)
    | (obtain ⟨x, -, hy⟩ := hy; exact congrArg Prod.fst (Set.mem_singleton_iff.1 hy))

/-- What a `rec_del` call does when its slot holds a frame cap. -/
def QX (sl : CslotPtr) : RecDelCall → State Unit → Except Unit (Bool × Cap) × State Unit → Prop
  | .finaliseSlotCall sl' _, t, x => sl' = sl → ∀ dev p R mt sz m,
      capAt t sl = some (.archObjectCap (.pageCap dev p R mt sz m)) →
      ∃ z ∈ (archFinaliseCap (Z := Unit) (.pageCap dev p R mt sz m)
        (decide (isFinalCap' (Z := Unit) (.archObjectCap (.pageCap dev p R mt sz m)) t)) t).1,
        x = (.ok (true, .nullCap), z.2)
  | .cTEDeleteCall sl' e, t, x => sl' = sl → e = true → ∀ dev p R mt sz m,
      capAt t sl = some (.archObjectCap (.pageCap dev p R mt sz m)) →
      (∃ v, x.1 = .ok v) ∧ ∃ z ∈ (archFinaliseCap (Z := Unit) (.pageCap dev p R mt sz m)
        (decide (isFinalCap' (Z := Unit) (.archObjectCap (.pageCap dev p R mt sz m)) t)) t).1,
        ∃ w ∈ (emptySlot (Z := Unit) sl .nullCap z.2).1, x.2 = w.2
  | .reduceZombieCall _ _ _, _, _ => True

abbrev RDFX := fun (r : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))) (c : RecDelCall) =>
  recDelF (Z := Unit) r c

theorem qx_prefixed (sl : CslotPtr) :
    ∀ k t, RDFX (fun c σ => ({x | QX sl c σ x}, True)) k t ≤ (fun c σ => ({x | QX sl c σ x}, True)) k t := by
  intro k t
  refine ⟨fun x hx => ?_, fun _ => trivial⟩
  show QX sl k t x
  cases k with
  | cTEDeleteCall sl' ex =>
    intro hs he dev p R mt sz m hc
    subst hs he
    change x ∈ ((recDelF (Z := Unit) _ (.cTEDeleteCall sl' true)).run t).1 at hx
    unfold recDelF at hx
    obtain ⟨y, hy, ⟨a, ha, hx⟩ | ⟨e, he, rfl⟩⟩ := fbx_mem_bindE hx
    · obtain ⟨z, hz, hyz⟩ := (show QX sl' (.finaliseSlotCall sl' true) t y from hy) rfl dev p R mt sz m hc
      subst hyz
      simp only [Except.ok.injEq] at ha
      subst ha
      dsimp only at hx
      simp only [withoutPreemption] at hx
      obtain ⟨w, hw, ⟨b, -, hx⟩ | ⟨e, he, rfl⟩⟩ := fbx_mem_bindE hx
      · obtain ⟨w', hw', rfl⟩ := fbx_mem_liftE hw
        have hw2 : w' ∈ (emptySlot (Z := Unit) sl' .nullCap z.2).1 := by
          unfold NonDet.when at hw'; rw [if_pos (Or.inl rfl)] at hw'; exact hw'
        rw [Set.mem_singleton_iff.1 hx]
        exact ⟨⟨_, rfl⟩, z, hz, w', hw2, rfl⟩
      · obtain ⟨w', -, hw⟩ := fbx_mem_liftE hw
        rw [hw] at he; cases he
    · obtain ⟨z, -, hyz⟩ := (show QX sl' (.finaliseSlotCall sl' true) t y from hy) rfl dev p R mt sz m hc
      rw [hyz] at he; cases he
  | finaliseSlotCall sl' ex =>
    intro hs dev p R mt sz m hc
    subst hs
    change x ∈ ((recDelF (Z := Unit) _ (.finaliseSlotCall sl' ex)).run t).1 at hx
    unfold recDelF withoutPreemption at hx
    obtain ⟨y, hy, ⟨a, ha, hx⟩ | ⟨e, he, rfl⟩⟩ := fbx_mem_bindE hx
    · obtain ⟨y', hy', rfl⟩ := fbx_mem_liftE hy
      obtain ⟨e2, hcap⟩ := getCap_capAt hy'
      rw [hc] at hcap
      simp only [Except.ok.injEq] at ha
      rw [← ha, ← Option.some.inj hcap] at hx
      rw [e2] at hx
      rw [if_neg (by simp)] at hx
      obtain ⟨y2, hy2, ⟨a2, ha2, hx⟩ | ⟨e, he, rfl⟩⟩ := fbx_mem_bindE hx
      · obtain ⟨y2', hy2', rfl⟩ := fbx_mem_liftE hy2
        have e3 : y2' = (decide (isFinalCap' (Z := Unit) (.archObjectCap (.pageCap dev p R mt sz m)) t), t) :=
          Set.mem_singleton_iff.1 hy2'
        simp only [Except.ok.injEq] at ha2
        subst e3; subst ha2
        obtain ⟨y3, hy3, ⟨a3, ha3, hx⟩ | ⟨e, he, rfl⟩⟩ := fbx_mem_bindE hx
        · obtain ⟨y3', hy3', rfl⟩ := fbx_mem_liftE hy3
          have hf : y3' ∈ (archFinaliseCap (Z := Unit) (.pageCap dev p R mt sz m)
              (decide (isFinalCap' (Z := Unit) (.archObjectCap (.pageCap dev p R mt sz m)) t)) t).1 := hy3'
          have hn := archFinaliseCap_frame hf
          simp only [Except.ok.injEq] at ha3
          subst ha3
          rw [hn] at hx
          dsimp only at hx
          rw [if_pos (by simp [capRemoveable])] at hx
          rw [Set.mem_singleton_iff.1 hx]
          exact ⟨y3', hf, rfl⟩
        · obtain ⟨w', -, hw⟩ := fbx_mem_liftE hy3
          rw [hw] at he; cases he
      · obtain ⟨w', -, hw⟩ := fbx_mem_liftE hy2
        rw [hw] at he; cases he
    · obtain ⟨w', -, hw⟩ := fbx_mem_liftE hy
      rw [hw] at he; cases he
  | reduceZombieCall _ _ _ => trivial

/-- **`cap_delete` of a slot holding a frame cap** is `fbDelX`'s round. -/
theorem capDelete_subX {sl : CslotPtr} {σ : State Unit} {dev : Bool} {p : ObjRef} {R : CapRights}
    {mt : VMMapType} {sz : VMPageSize} {m : Option (Asid × VSpaceRef)}
    (hc : capAt σ sl = some (.archObjectCap (.pageCap dev p R mt sz m))) :
    ∀ y ∈ ((capDelete (Z := Unit) sl).run σ).1, y ∈ ((fbDelX sl).run σ).1 := by
  intro y hy
  unfold capDelete at hy
  obtain ⟨z, hz, ⟨a, -, hy⟩ | ⟨e, he, rfl⟩⟩ := fbx_mem_bindE hy
  · have hq := (ik_lfp_le RDFX _ (qx_prefixed sl) _ σ).1 hz
    obtain ⟨-, w, hw, w2, hw2, e2⟩ :=
      (show QX sl (.cTEDeleteCall sl true) σ z from hq) rfl rfl dev p R mt sz m hc
    have ey : y = (.ok (), z.2) := Set.mem_singleton_iff.1 hy
    rw [ey, e2]
    unfold fbDelX NonDetE.liftE
    rw [ExceptT.run_lift]
    refine ⟨((), w2.2), ?_, Set.mem_singleton _⟩
    refine ⟨(.archObjectCap (.pageCap dev p R mt sz m), σ), ?_, ?_⟩
    · exact fbx_getCap_of_capAt hc
    · refine ⟨(decide (isFinalCap' (Z := Unit) (.archObjectCap (.pageCap dev p R mt sz m)) σ), σ), rfl, ?_⟩
      exact ⟨w, hw, hw2⟩
  · have hq := (ik_lfp_le RDFX _ (qx_prefixed sl) _ σ).1 hz
    obtain ⟨⟨v, hv⟩, -⟩ := (show QX sl (.cTEDeleteCall sl true) σ z from hq) rfl rfl dev p R mt sz m hc
    rw [hv] at he; cases he

/-! ## The batch with `fbDelX` -/

/-- `fbDelete` with `fbDelX`. -/
def fbDeleteX (slot : CslotPtr) : NonDetE (State Unit) Data Unit :=
  NonDetE.handleE (fbDelX slot) fun _ => NonDetE.throwError (msgFromSyscallError .illegalOperation).1

/-- `fbEntry` with `fbDelX` for `capDelete`. -/
def fbEntryX (b : Fl4FrameBatchInvocation) (w : Data × Data × Data) : NonDetE (State Unit) Data Bool :=
  match b.op with
  | .copyMap => do
      let dest ← fbCode (Z := Unit) <| lookupTargetSlot b.destCnode (dataToCptr w.2.1) b.depth
      fbCode (Z := Unit) <| ensureEmpty dest
      let src ← fbCode (Z := Unit) <| lookupSourceSlot b.cnode (dataToCptr w.1) b.depth
      let srcCap ← NonDetE.liftE <| getCap (Z := Unit) src
      fbCode (Z := Unit) <| NonDetE.unlessE (isPageCap srcCap) <| NonDetE.throwError (.invalidCapability 0)
      let newCap ← fbCode (Z := Unit) <| deriveCap src (maskCap (dataToRights b.capRights) srcCap)
      NonDetE.liftE <| capInsert (Z := Unit) newCap src dest
      NonDetE.handleE (fbCode (Z := Unit) <| fbMap b dest w.2.2) fun c => do
        NonDetE.liftE <| NonDetE.catch (fbDelX dest) fun _ => NonDet.pure ()
        NonDetE.throwError c
      NonDetE.returnOk false
  | .remap => do
      let slot ← fbCode (Z := Unit) <| lookupSourceSlot b.cnode (dataToCptr w.1) b.depth
      fbCode (Z := Unit) <| fbMap b slot w.2.1
      NonDetE.returnOk false
  | .delete => do
      let slot ← fbCode (Z := Unit) <| lookupTargetSlot b.cnode (dataToCptr w.1) b.depth
      let c ← NonDetE.liftE <| getCap (Z := Unit) slot
      match c with
      | .nullCap => NonDetE.returnOk false
      | .archObjectCap (.pageCap dev p R mt sz m) => do
          let cleared ← match m with
            | some (asid', vaddr) =>
              if b.deferDelete ∧ mt = .vmVSpaceMap ∧ dev = false ∧ asid' = b.asid then
                NonDetE.liftE (do
                  let r ← unmapPageUnflushed (Z := Unit) sz b.vspace vaddr p
                  setCap (Z := Unit) (.archObjectCap (.pageCap dev p R .vmNoMap sz none)) slot
                  return r)
              else NonDetE.returnOk false
            | none => NonDetE.returnOk false
          fbDeleteX slot
          NonDetE.returnOk cleared
      | _ => NonDetE.throwError (msgFromSyscallError .illegalOperation).1

/-- `fbRun` with `fbEntryX`. -/
def fbRunX (b : Fl4FrameBatchInvocation) : List (Data × Data × Data) → Nat → Bool → NonDet (State Unit) (Nat × Data × Bool)
  | [], done, d => return (done, 0, d)
  | w :: ws, done, d => do
      let r ← (fbEntryX b w).run
      match r with
      | .ok d' => fbRunX b ws (done + 1) (d || d')
      | .error c => return (done, c, d)

/-- `performFrameBatch` with `fbRunX`. -/
def performFrameBatchX (b : Fl4FrameBatchInvocation) : NonDet (State Unit) (List Data) := do
  let (done, err, d) ← fbRunX b b.entries 0 false
  NonDet.when (d = true) <| flushAll (Z := Unit) b.vspace b.asid
  return [BitVec.ofNat 64 done, err]

/-! ## Slot facts along an entry -/

theorem fbx_sub_bindE2 {σ ε α β : Type} {m m' : NonDetE σ ε α} {f f' : α → NonDetE σ ε β} {s : σ}
    (hm : ∀ y ∈ (m.run s).1, y ∈ (m'.run s).1)
    (Q : α → σ → Prop) (hQ : ∀ a t, (.ok a, t) ∈ (m.run s).1 → Q a t)
    (hf : ∀ a t, Q a t → ∀ y ∈ ((f a).run t).1, y ∈ ((f' a).run t).1) :
    ∀ y ∈ ((m >>= f).run s).1, y ∈ ((m' >>= f').run s).1 := by
  intro y hy
  rw [ExceptT.run_bind] at hy ⊢
  obtain ⟨z, hz, hyz⟩ := hy
  refine ⟨z, hm z hz, ?_⟩
  obtain ⟨r, t⟩ := z
  cases r with
  | ok a => exact hf a t (hQ a t hz) y hyz
  | error e => exact hyz

theorem fbx_sub_handleE2 {σ ε ε' α : Type} {m : NonDetE σ ε α} {h h' : ε → NonDetE σ ε' α} {s : σ}
    (hh : ∀ e t, (.error e, t) ∈ (m.run s).1 → ∀ y ∈ ((h e).run t).1, y ∈ ((h' e).run t).1) :
    ∀ y ∈ ((NonDetE.handleE m h).run s).1, y ∈ ((NonDetE.handleE m h').run s).1 := by
  intro y hy
  unfold NonDetE.handleE at hy ⊢
  rw [ExceptT.run_mk] at hy ⊢
  obtain ⟨z, hz, hyz⟩ := hy
  refine ⟨z, hz, ?_⟩
  obtain ⟨r, t⟩ := z
  cases r with
  | ok a => exact hyz
  | error e => exact hh e t hz y hyz

theorem fbx_sub_bind {σ α β : Type} {m m' : NonDet σ α} {f f' : α → NonDet σ β} {s : σ}
    (hm : ∀ y ∈ (m s).1, y ∈ (m' s).1) (hf : ∀ a t, (a, t) ∈ (m s).1 → ∀ y ∈ (f a t).1, y ∈ (f' a t).1) :
    ∀ y ∈ ((m >>= f) s).1, y ∈ ((m' >>= f') s).1 := by
  intro y hy
  obtain ⟨z, hz, hyz⟩ := hy
  exact ⟨z, hm z hz, hf z.1 z.2 hz y hyz⟩

/-- An `ok` outcome of `fbCode m` is one of `m`. -/
theorem fbx_fbCode_ok {α : Type} {m : SEMonad Unit α} {s t : State Unit} {a : α}
    (h : (.ok a, t) ∈ ((fbCode (Z := Unit) m).run s).1) : (.ok a, t) ∈ (m.run s).1 := by
  unfold fbCode NonDetE.handleE at h
  rw [ExceptT.run_mk] at h
  obtain ⟨⟨r, u⟩, hz, h⟩ := h
  cases r with
  | ok a' =>
    obtain ⟨e1, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h)
    simp only [Except.ok.injEq] at e1
    subst e1; exact hz
  | error e => cases (Prod.mk.inj (Set.mem_singleton_iff.1 h)).1

/-- An `error` outcome of `fbCode m` is at the state of an `error` outcome of `m`. -/
theorem fbx_fbCode_err {α : Type} {m : SEMonad Unit α} {s t : State Unit} {c : Data}
    (h : (.error c, t) ∈ ((fbCode (Z := Unit) m).run s).1) : ∃ e, (.error e, t) ∈ (m.run s).1 := by
  unfold fbCode NonDetE.handleE at h
  rw [ExceptT.run_mk] at h
  obtain ⟨⟨r, u⟩, hz, h⟩ := h
  cases r with
  | ok a' => cases (Prod.mk.inj (Set.mem_singleton_iff.1 h)).1
  | error e =>
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h)
    exact ⟨e, hz⟩

theorem fbx_capInsert_at {c : Cap} {src dest : CslotPtr} {s : State Unit} {y : Unit × State Unit}
    (hy : y ∈ (capInsert (Z := Unit) c src dest s).1) : capAt y.2 dest = some c := by
  unfold capInsert at hy
  obtain ⟨z1, -, hy⟩ := hy
  obtain ⟨z2, -, hy⟩ := hy
  obtain ⟨z3, -, hy⟩ := hy
  obtain ⟨z4, -, hy⟩ := hy
  obtain ⟨z5, -, hy⟩ := hy
  obtain ⟨⟨u6, s6⟩, h6, hy⟩ := hy
  have h := setCap_at h6
  refine (?_ : IK (fun σ => capAt σ dest = some c) _) s6 h y hy
  repeat' (first | (exact ik_doExtendedOp (fun _ _ h => h) _) | ik_step0 | ik_unfold)

/-- `fbMap`'s errors are thrown before any write. -/
theorem fbx_fbMap_err {b : Fl4FrameBatchInvocation} {sl : CslotPtr} {v : Data} {s t : State Unit} {e : SyscallError}
    (h : (.error e, t) ∈ ((fbMap (Z := Unit) b sl v).run s).1) : capAt t = capAt s := by
  unfold fbMap at h
  obtain ⟨z, hz, ⟨c, hc, h⟩ | ⟨e', he, h⟩⟩ := fbx_mem_bindE h
  · obtain ⟨z', hz', rfl⟩ := fbx_mem_liftE hz
    obtain ⟨e1, -⟩ := getCap_capAt hz'
    simp only [Except.ok.injEq] at hc
    subst hc
    dsimp only at h
    rw [e1] at h
    split at h
    · obtain ⟨z2, hz2, ⟨a2, -, h⟩ | ⟨e2, he2, h⟩⟩ := fbx_mem_bindE h
      · have e2s : z2.2 = s := by
          unfold NonDetE.whenE at hz2
          split at hz2
          · exact congrArg Prod.snd (Set.mem_singleton_iff.1 hz2)
          · exact congrArg Prod.snd (Set.mem_singleton_iff.1 hz2)
        rw [e2s] at h
        obtain ⟨z3, hz3, ⟨a3, -, h⟩ | ⟨e3, he3, h⟩⟩ := fbx_mem_bindE h
        · split at h
          · obtain ⟨z4, hz4, ⟨a4, -, h⟩ | ⟨e4, he4, h⟩⟩ := fbx_mem_bindE h
            · cases (Prod.mk.inj (Set.mem_singleton_iff.1 h)).1
            · obtain ⟨w, -, hw⟩ := fbx_mem_liftE hz4
              rw [hw] at he4; cases he4
          · obtain ⟨w, hw, -⟩ := fbx_mem_liftE h
            exact hw.elim
        · obtain ⟨-, rfl⟩ := Prod.mk.inj h
          have := uk_decodePageInvocation (uvw := uV s) _ _ _ _ _ s rfl z3 hz3
          exact congrArg (fun w : UView => w.2.1) this
      · obtain ⟨-, rfl⟩ := Prod.mk.inj h
        unfold NonDetE.whenE at hz2
        split at hz2
        · exact congrArg capAt (congrArg Prod.snd (Set.mem_singleton_iff.1 hz2))
        · exact congrArg capAt (congrArg Prod.snd (Set.mem_singleton_iff.1 hz2))
    · obtain ⟨-, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h)
      rfl
  · obtain ⟨w, -, hw⟩ := fbx_mem_liftE hz
    rw [hw] at he; cases he

theorem fbx_unlessE_ok {P : Prop} [Decidable P] {e : SyscallError} {s t : State Unit} {a : Unit}
    (h : (.ok a, t) ∈ ((NonDetE.unlessE P (NonDetE.throwError e) : SEMonad Unit Unit).run s).1) : P ∧ t = s := by
  unfold NonDetE.unlessE at h
  split at h
  · exact ⟨by assumption, (Prod.mk.inj (Set.mem_singleton_iff.1 h)).2⟩
  · cases (Prod.mk.inj (Set.mem_singleton_iff.1 h)).1

theorem fbx_frame_of_isPageCap {c : Cap} (h : isPageCap c = true) :
    ∃ dev p R mt sz m, c = .archObjectCap (.pageCap dev p R mt sz m) := by
  cases c <;> simp [isPageCap] at h
  case archObjectCap a =>
    cases a <;> simp [isPageCap] at h
    exact ⟨_, _, _, _, _, _, rfl⟩

/-- **One entry**: every outcome of `fbEntry` is one of `fbEntryX`. -/
theorem fbEntry_subX (b : Fl4FrameBatchInvocation) (w : Data × Data × Data) (s : State Unit) :
    ∀ y ∈ ((fbEntry (Z := Unit) b w).run s).1, y ∈ ((fbEntryX b w).run s).1 := by
  rcases b with ⟨vs, asid, op, depth, mr, cr, attr, dd, cn, dcn, es⟩
  cases op
  case remap => exact fun y hy => hy
  case copyMap =>
    unfold fbEntry fbEntryX
    dsimp only
    refine fbx_sub_bindE (fun _ _ => True) (fun _ _ _ => trivial) fun dest t0 _ => ?_
    refine fbx_sub_bindE (fun _ _ => True) (fun _ _ _ => trivial) fun _ t1 _ => ?_
    refine fbx_sub_bindE (fun _ _ => True) (fun _ _ _ => trivial) fun src t2 _ => ?_
    refine fbx_sub_bindE (fun c t => t = t2 ∧ capAt t src = some c) (fun c t h => ?_) fun srcCap t3 h3 => ?_
    · obtain ⟨⟨c', t'⟩, hx, hxe⟩ := fbx_mem_liftE h
      simp only [Prod.mk.injEq, Except.ok.injEq] at hxe
      obtain ⟨rfl, rfl⟩ := hxe
      obtain ⟨e3, e4⟩ := getCap_capAt hx
      dsimp only at e3 e4
      exact ⟨e3, by rw [e3]; exact e4⟩
    refine fbx_sub_bindE (fun _ t => isPageCap srcCap = true ∧ t = t3) (fun _ t h =>
      fbx_unlessE_ok (fbx_fbCode_ok h)) fun _ t4 ⟨hpg, et4⟩ => ?_
    subst et4
    obtain ⟨dev, p, R, mt, sz, m, rfl⟩ := fbx_frame_of_isPageCap hpg
    refine fbx_sub_bindE (fun c t => IsFrameCap c) (fun c t h => ?_) fun newCap t5 h5 => ?_
    · have h' := fbx_fbCode_ok h
      simp only [maskCap, capRightsUpdate, acapRightsUpdate, deriveCap, archDeriveCap] at h'
      obtain ⟨e1, -⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h')
      simp only [Except.ok.injEq] at e1
      subst e1; exact trivial
    refine fbx_sub_bindE (fun _ t => capAt t dest = some newCap) (fun _ t h => ?_) fun _ t6 h6 => ?_
    · obtain ⟨x, hx, hxe⟩ := fbx_mem_liftE h
      obtain ⟨-, rfl⟩ := Prod.mk.inj hxe
      exact fbx_capInsert_at hx
    refine fbx_sub_bindE2 (fbx_sub_handleE2 fun c t7 h7 => ?_) (fun _ _ => True) (fun _ _ _ => trivial)
      fun _ _ _ => fun y hy => hy
    obtain ⟨e, he⟩ := fbx_fbCode_err h7
    have hca : capAt t7 dest = some newCap := by rw [fbx_fbMap_err he]; exact h6
    revert hca
    cases newCap
    case archObjectCap a =>
      cases a
      case pageCap dev' p' R' mt' sz' m' =>
        intro hca
        exact fbx_sub_bindE2 (fbx_sub_liftE (fbx_sub_catch (capDelete_subX hca))) (fun _ _ => True)
          (fun _ _ _ => trivial) fun _ _ _ => fun y hy => hy
      all_goals exact (h5 : False).elim
    all_goals exact (h5 : False).elim
  case delete =>
    unfold fbEntry fbEntryX
    dsimp only
    refine fbx_sub_bindE (fun _ _ => True) (fun _ _ _ => trivial) fun slot t0 _ => ?_
    refine fbx_sub_bindE (fun c t => capAt t slot = some c) (fun c t h => ?_) fun c t1 h1 => ?_
    · obtain ⟨⟨c', t'⟩, hx, hxe⟩ := fbx_mem_liftE h
      simp only [Prod.mk.injEq, Except.ok.injEq] at hxe
      obtain ⟨rfl, rfl⟩ := hxe
      obtain ⟨e3, e4⟩ := getCap_capAt hx
      dsimp only at e3 e4
      rw [e3]; exact e4
    cases c
    case archObjectCap a =>
      cases a
      case pageCap dev p R mt sz m =>
        have hdel : ∀ t2, capAt t2 slot = some (.archObjectCap (.pageCap dev p R .vmNoMap sz none)) ∨
            (t2 = t1) → ∀ cl : Bool, ∀ y ∈ ((fbDelete (Z := Unit) slot >>= fun _ =>
              (NonDetE.returnOk cl : NonDetE (State Unit) Data Bool)).run t2).1,
            y ∈ ((fbDeleteX slot >>= fun _ =>
              (NonDetE.returnOk cl : NonDetE (State Unit) Data Bool)).run t2).1 := by
          intro t2 h2 cl
          have hc2 : ∃ dev p R mt sz m, capAt t2 slot = some (.archObjectCap (.pageCap dev p R mt sz m)) := by
            rcases h2 with h2 | rfl
            · exact ⟨_, _, _, _, _, _, h2⟩
            · exact ⟨_, _, _, _, _, _, h1⟩
          obtain ⟨_, _, _, _, _, _, hc2⟩ := hc2
          exact fbx_sub_bindE2 (by unfold fbDelete fbDeleteX; exact fbx_sub_handleE (capDelete_subX hc2))
            (fun _ _ => True) (fun _ _ _ => trivial) fun _ _ _ => fun y hy => hy
        dsimp only
        rcases m with _ | ⟨asid', vaddr⟩
        · dsimp only
          refine fbx_sub_bindE2 (fun y hy => hy) (fun _ t => t = t1) (fun _ t h => ?_) fun cl t2 h2 =>
            hdel t2 (Or.inr h2) cl
          exact (Prod.mk.inj (Set.mem_singleton_iff.1 h)).2
        · dsimp only
          split
          · refine fbx_sub_bindE2 (fun y hy => hy)
              (fun _ t => capAt t slot = some (.archObjectCap (.pageCap dev p R .vmNoMap sz none)))
              (fun _ t h => ?_) fun cl t2 h2 => hdel t2 (Or.inl h2) cl
            obtain ⟨x, hx, hxe⟩ := fbx_mem_liftE h
            obtain ⟨-, rfl⟩ := Prod.mk.inj hxe
            obtain ⟨z1, -, hx⟩ := hx
            obtain ⟨z2, hz2, hx⟩ := hx
            rw [Set.mem_singleton_iff.1 hx]
            exact setCap_at hz2
          · refine fbx_sub_bindE2 (fun y hy => hy) (fun _ t => t = t1) (fun _ t h => ?_) fun cl t2 h2 =>
              hdel t2 (Or.inr h2) cl
            exact (Prod.mk.inj (Set.mem_singleton_iff.1 h)).2
      all_goals exact fun y hy => hy
    all_goals exact fun y hy => hy

/-- **The loop**. -/
theorem fbRun_subX (b : Fl4FrameBatchInvocation) :
    ∀ (ws : List (Data × Data × Data)) (n : Nat) (d : Bool) (s : State Unit),
      ∀ y ∈ (fbRun (Z := Unit) b ws n d s).1, y ∈ (fbRunX b ws n d s).1
  | [], n, d, s => fun y hy => hy
  | w :: ws, n, d, s => by
    unfold fbRun fbRunX
    refine fbx_sub_bind (fbEntry_subX b w s) fun r t _ => ?_
    cases r with
    | ok d' => exact fbRun_subX b ws (n + 1) (d || d') t
    | error c => exact fun y hy => hy

/-- **The batch**. -/
theorem performFrameBatch_subX (b : Fl4FrameBatchInvocation) (s : State Unit) :
    ∀ y ∈ (performFrameBatch (Z := Unit) b s).1, y ∈ (performFrameBatchX b s).1 := by
  unfold performFrameBatch performFrameBatchX
  exact fbx_sub_bind (fbRun_subX b _ _ _ s) fun _ _ _ => fun y hy => hy

/-! ## Families -/

theorem ike_fbEntry_ofX {P : State Unit → Prop} {b : Fl4FrameBatchInvocation} {w : Data × Data × Data}
    (h : IKE P (fbEntryX b w)) : IKE P (fbEntry (Z := Unit) b w) :=
  fun s hs y hy => h s hs y (fbEntry_subX b w s y hy)

theorem ik_performFrameBatch_ofX {P : State Unit → Prop} {b : Fl4FrameBatchInvocation}
    (h : IK P (performFrameBatchX b)) : IK P (performFrameBatch (Z := Unit) b) :=
  fun s hs y hy => h s hs y (performFrameBatch_subX b s y hy)

/-- `IK P` of `fbRunX` from `IK P` of one `fbEntryX`. -/
theorem ik_fbRunX {P : State Unit → Prop} {b : Fl4FrameBatchInvocation} (h : ∀ w, IKE P (fbEntryX b w)) :
    ∀ (ws : List (Data × Data × Data)) (n : Nat) (d : Bool), IK P (fbRunX b ws n d)
  | [], n, d => ik_pure _
  | w :: ws, n, d => by
    unfold fbRunX
    refine ik_bind (h w) fun r => ?_
    cases r with
    | ok d' => exact ik_fbRunX h ws (n + 1) (d || d')
    | error c => exact ik_pure _

/-- **`IK P` of the batch** from `IK P` of one `fbEntryX` and of the final flush. -/
theorem ik_performFrameBatchX {P : State Unit → Prop} {b : Fl4FrameBatchInvocation}
    (h : ∀ w, IKE P (fbEntryX b w)) (hf : IK P (flushAll (Z := Unit) b.vspace b.asid)) :
    IK P (performFrameBatch (Z := Unit) b) := by
  refine ik_performFrameBatch_ofX ?_
  unfold performFrameBatchX
  refine ik_bind (ik_fbRunX h _ _ _) fun r => ?_
  obtain ⟨done, err, d⟩ := r
  exact ik_bind (ik_when _ hf) fun _ => ik_pure _

/-! ## Relational families (pre/post relations, reflexive and transitive) -/

theorem rk_fbRunX {R : State Unit → State Unit → Prop} (hr : ∀ σ, R σ σ)
    (ht : ∀ a b c, R a b → R b c → R a c) {b : Fl4FrameBatchInvocation} (h : ∀ w σ, ∀ x ∈ ((fbEntryX b w).run σ).1, R σ x.2) :
    ∀ (ws : List (Data × Data × Data)) (n : Nat) (d : Bool) (σ : State Unit),
      ∀ x ∈ (fbRunX b ws n d σ).1, R σ x.2
  | [], n, d, σ => fun x hx => by rw [Set.mem_singleton_iff.1 hx]; exact hr σ
  | w :: ws, n, d, σ => fun x hx => by
    unfold fbRunX at hx
    obtain ⟨⟨r, u⟩, hz, hx⟩ := hx
    have h1 := h w σ _ hz
    cases r with
    | ok d' => exact ht _ _ _ h1 (rk_fbRunX hr ht h ws (n + 1) (d || d') u x hx)
    | error c => rw [Set.mem_singleton_iff.1 hx]; exact h1

/-- **A relational family of the batch** from one `fbEntryX` and the final flush. -/
theorem rk_performFrameBatchX {R : State Unit → State Unit → Prop} (hr : ∀ σ, R σ σ)
    (ht : ∀ a b c, R a b → R b c → R a c) {b : Fl4FrameBatchInvocation} (h : ∀ w σ, ∀ x ∈ ((fbEntryX b w).run σ).1, R σ x.2)
    (hf : ∀ σ, ∀ x ∈ (flushAll (Z := Unit) b.vspace b.asid σ).1, R σ x.2) :
    ∀ σ, ∀ x ∈ (performFrameBatch (Z := Unit) b σ).1, R σ x.2 := by
  intro σ x hx
  have hx' := performFrameBatch_subX b σ x hx
  unfold performFrameBatchX at hx'
  obtain ⟨⟨⟨done, err, d⟩, u⟩, hy, hx'⟩ := hx'
  have h1 := rk_fbRunX hr ht h _ _ _ σ _ hy
  obtain ⟨z, hz, hx'⟩ := hx'
  rw [Set.mem_singleton_iff.1 hx']
  refine ht _ _ _ h1 ?_
  unfold NonDet.when at hz
  split at hz
  · exact hf u z hz
  · rw [Set.mem_singleton_iff.1 hz]; exact hr u



theorem uk_unmapPageUnflushed {uvw : UView} (sz : VMPageSize) (vs : ObjRef) (va : VSpaceRef) (p : ObjRef) :
    UK uvw (unmapPageUnflushed (Z := Unit) sz vs va p) := by
  unfold unmapPageUnflushed; uk_auto

/-! ## The entry's reads, for any predicate (fb3e) -/

section RO
variable {P : State Unit → Prop}

theorem fbx_resolveAddressBits' (p : Cap × CapRef) : IKE P (resolveAddressBits' (Z := Unit) p) := by
  rw [resolveAddressBits']
  split
  · split
    · exact ike_liftE ik_fail
    · refine ike_bind (ike_whenE _ (ike_throw _)) fun _ => ike_bind (ike_whenE _ (ike_throw _)) fun _ => ?_
      refine ike_returnOk_bind ?_
      dsimp only
      split
      · exact ike_returnOk _
      · refine ike_bind (ike_liftE (by repeat' (first | ik_step0 | ik_unfold))) fun nc => ?_
        split
        · exact fbx_resolveAddressBits' _
        · exact ike_returnOk _
  · exact ike_throw _
termination_by p.2.length
decreasing_by
  simp only [List.length_drop]
  have h1 : p.2.length ≠ 0 := by
    intro h; simp_all [List.drop_eq_nil_of_le]
  omega

theorem fbx_resolveAddressBits (p : Cap × CapRef) : IKE P (resolveAddressBits (Z := Unit) p) := by
  unfold resolveAddressBits
  repeat' (first | (with_reducible exact fbx_resolveAddressBits' _) | ik_step0 | ik_unfold)

theorem fbx_lookupTargetSlot (cn : Cap) (c : CapRef) (d : Nat) : IKE P (lookupTargetSlot (Z := Unit) cn c d) := by
  unfold lookupTargetSlot
  repeat' (first | (with_reducible exact fbx_resolveAddressBits _) | (with_reducible exact fbx_resolveAddressBits' _) | ik_step0 | ik_unfold)

theorem fbx_lookupSourceSlot (cn : Cap) (c : CapRef) (d : Nat) : IKE P (lookupSourceSlot (Z := Unit) cn c d) := by
  unfold lookupSourceSlot
  repeat' (first | (with_reducible exact fbx_lookupTargetSlot _ _ _) | (with_reducible exact fbx_resolveAddressBits _) | (with_reducible exact fbx_resolveAddressBits' _) | ik_step0 | ik_unfold)

theorem fbx_ensureEmpty (sl : CslotPtr) : IKE P (ensureEmpty (Z := Unit) sl) := by
  unfold ensureEmpty; repeat' (first | ik_step0 | ik_unfold)

theorem fbx_deriveCap (sl : CslotPtr) (c : Cap) : IKE P (deriveCap (Z := Unit) sl c) := by
  unfold deriveCap; repeat' (first | ik_step0 | ik_unfold)

theorem fbx_decodePageInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap)
    (ex : List (Cap × CslotPtr)) : IKE P (decodePageInvocation (Z := Unit) label args cte cap ex) := by
  unfold decodePageInvocation; repeat' (first | ik_step0 | ik_unfold)

theorem fbx_isFinalCap (c : Cap) : IK P (isFinalCap (Z := Unit) c) := ik_gets _

end RO

/-! ## One entry from its steps (fb3e) -/

/-- `IKE` through a bind whose continuation is needed only at the outcomes satisfying `Q`. -/
theorem ike_bind_q {P : State Unit → Prop} {ε α β : Type} {m : NonDetE (State Unit) ε α}
    {g : α → NonDetE (State Unit) ε β} (Q : α → Prop) (hm : IKE P m)
    (hq : ∀ s a t, (.ok a, t) ∈ (m.run s).1 → Q a) (hg : ∀ a, Q a → IKE P (g a)) : IKE P (m >>= g) := by
  intro s hs y hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, -, rfl⟩⟩ := fbx_mem_bindE hy
  · obtain ⟨r, t⟩ := z
    simp only at ha; subst ha
    exact hg a (hq s a t hz) t (hm s hs _ hz) y hy
  · exact hm s hs z hz

/-- `IKE`-style reasoning at one state, the continuation needed only at the outcomes satisfying `Q`. -/
theorem fbx_ikp_bind {P : State Unit → Prop} {ε α β : Type} {m : NonDetE (State Unit) ε α}
    {g : α → NonDetE (State Unit) ε β} {s : State Unit} (Q : α → State Unit → Prop)
    (hm : ∀ y ∈ (m.run s).1, P y.2) (hq : ∀ a t, (.ok a, t) ∈ (m.run s).1 → Q a t)
    (hg : ∀ a t, Q a t → ∀ y ∈ ((g a).run t).1, P y.2) : ∀ y ∈ ((m >>= g).run s).1, P y.2 := by
  intro y hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, -, rfl⟩⟩ := fbx_mem_bindE hy
  · obtain ⟨r, t⟩ := z
    simp only at ha; subst ha
    exact hg a t (hq a t hz) y hy
  · exact hm z hz

theorem fbx_ik_getCap {P : State Unit → Prop} (sl : CslotPtr) : IK P (getCap (Z := Unit) sl) :=
  ik_of_eq fun _ _ hx => (getCap_capAt hx).1

theorem fbx_ensureEmpty_null {sl : CslotPtr} {s t : State Unit} {u : Unit}
    (h : (.ok u, t) ∈ ((ensureEmpty (Z := Unit) sl).run s).1) : capAt s sl = some .nullCap := by
  unfold ensureEmpty at h
  obtain ⟨z, hz, ⟨c, hc, h⟩ | ⟨e, -, h⟩⟩ := fbx_mem_bindE h
  · obtain ⟨x, hx, rfl⟩ := fbx_mem_liftE hz
    obtain ⟨-, hcap⟩ := getCap_capAt hx
    simp only [Except.ok.injEq] at hc
    subst hc
    unfold NonDetE.whenE at h
    split at h
    · cases (Prod.mk.inj (Set.mem_singleton_iff.1 h)).1
    · rename_i hn
      rw [hcap]; exact congrArg some (Classical.not_not.1 hn)
  · cases (Prod.mk.inj h).1

/-- **`IKE P` of one entry** from `IKE P` / `IK P` of its steps (a cap inserted or written by an entry is a
frame cap). A family proves each step with its own `*_auto`; no step unfolds the whole entry. -/
theorem ik_fbEntryX_of {P : State Unit → Prop} (b : Fl4FrameBatchInvocation) (w : Data × Data × Data)
    (hlt : ∀ cn c d, IKE P (lookupTargetSlot (Z := Unit) cn c d))
    (hls : ∀ cn c d, IKE P (lookupSourceSlot (Z := Unit) cn c d))
    (hee : ∀ sl, IKE P (ensureEmpty (Z := Unit) sl))
    (hdc : ∀ sl c, IKE P (deriveCap (Z := Unit) sl c))
    (hci : ∀ s c src dest c0, P s → IsFrameCap c →
      (.ok dest, s) ∈ ((lookupTargetSlot (Z := Unit) b.destCnode (dataToCptr w.2.1) b.depth).run s).1 →
      capAt s dest = some .nullCap → capAt s src = some c0 → isPageCap c0 = true →
      (.ok c, s) ∈ ((deriveCap (Z := Unit) src (maskCap (dataToRights b.capRights) c0)).run s).1 →
      ∀ x ∈ (capInsert (Z := Unit) c src dest s).1, P x.2)
    (hmap : ∀ sl v, IKE P (fbMap (Z := Unit) b sl v))
    (hdel : ∀ sl, IKE P (fbDelX sl))
    (hun : ∀ sz vs va p, IK P (unmapPageUnflushed (Z := Unit) sz vs va p))
    (hset : ∀ s dev p R mt sz m sl, P s → capAt s sl = some (.archObjectCap (.pageCap dev p R mt sz m)) →
      ∀ x ∈ (setCap (Z := Unit) (.archObjectCap (.pageCap dev p R .vmNoMap sz none)) sl s).1, P x.2) :
    IKE P (fbEntryX b w) := by
  have hcode : ∀ {Q : State Unit → Prop} {α : Type} {m : SEMonad Unit α}, IKE Q m → IKE Q (fbCode (Z := Unit) m) :=
    fun h => ike_handleE h fun _ => ike_throw _
  rcases b with ⟨vs, asid, op, depth, mr, cr, attr, dd, cn, dcn, es⟩
  cases op
  case remap =>
    unfold fbEntryX; dsimp only
    exact ike_bind (hcode (hls _ _ _)) fun sl => ike_bind (hcode (hmap _ _)) fun _ => ike_returnOk _
  case copyMap =>
    unfold fbEntryX; dsimp only
    intro s hs
    refine fbx_ikp_bind (fun dest t => t = s ∧
        (.ok dest, s) ∈ ((lookupTargetSlot (Z := Unit) dcn (dataToCptr w.2.1) depth).run s).1)
      (hcode (hlt _ _ _) s hs) (fun a t h => ?_) fun dest t ⟨e, hdest⟩ => ?_
    · have e : t = s := hcode (fbx_lookupTargetSlot (P := (· = s)) _ _ _) s rfl _ h
      subst t; exact ⟨rfl, fbx_fbCode_ok h⟩
    subst t
    refine fbx_ikp_bind (fun _ t => t = s ∧ capAt s dest = some .nullCap) (hcode (hee _) s hs) (fun a t h => ?_)
      fun _ t ⟨e, hnull⟩ => ?_
    · have e : t = s := hcode (fbx_ensureEmpty (P := (· = s)) _) s rfl _ h
      subst t; exact ⟨rfl, fbx_ensureEmpty_null (fbx_fbCode_ok h)⟩
    subst t
    refine fbx_ikp_bind (fun _ t => t = s) (hcode (hls _ _ _) s hs)
      (fun a t h => hcode (fbx_lookupSourceSlot (P := (· = s)) _ _ _) s rfl _ h) fun src t e => ?_
    subst t
    refine fbx_ikp_bind (fun c0 t => t = s ∧ capAt s src = some c0) (ike_liftE (fbx_ik_getCap _) s hs)
      (fun a t h => ?_) fun c0 t ⟨e, hc0⟩ => ?_
    · obtain ⟨x, hx, hxe⟩ := fbx_mem_liftE h
      simp only [Prod.mk.injEq, Except.ok.injEq] at hxe
      obtain ⟨rfl, rfl⟩ := hxe
      exact getCap_capAt hx
    subst t
    refine fbx_ikp_bind (fun _ t => isPageCap c0 = true ∧ t = s) (hcode (ike_unlessE _ (ike_throw _)) s hs)
      (fun a t h => fbx_unlessE_ok (fbx_fbCode_ok h)) fun _ t ⟨hpg, e⟩ => ?_
    subst t
    refine fbx_ikp_bind (fun c t => t = s ∧
        (.ok c, s) ∈ ((deriveCap (Z := Unit) src (maskCap (dataToRights cr) c0)).run s).1)
      (hcode (hdc _ _) s hs) (fun a t h => ?_) fun c t ⟨e, hder⟩ => ?_
    · have e : t = s := hcode (fbx_deriveCap (P := (· = s)) _ _) s rfl _ h
      subst t; exact ⟨rfl, fbx_fbCode_ok h⟩
    subst t
    have hfc : IsFrameCap c := by
      obtain ⟨dev, p, R, mt, sz, m, rfl⟩ := fbx_frame_of_isPageCap hpg
      have hder' := hder
      simp only [maskCap, capRightsUpdate, acapRightsUpdate, deriveCap, archDeriveCap] at hder'
      obtain ⟨e1, -⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 hder')
      simp only [Except.ok.injEq] at e1
      subst e1; exact trivial
    have hci' : ∀ y ∈ ((NonDetE.liftE (ε := Data) (capInsert (Z := Unit) c src dest)).run s).1, P y.2 := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := fbx_mem_liftE hy
      exact hci s c src dest c0 hs hfc hdest hnull hc0 hpg hder x hx
    refine fbx_ikp_bind (fun _ t => P t) hci' (fun a t h => hci' _ h) fun _ t ht => ?_
    exact (ike_bind (ike_handleE (hcode (hmap _ _)) fun c =>
      ike_bind (ike_liftE (ik_catch (hdel _) fun _ => ik_pure' _)) fun _ => ike_throw _)
      fun _ => ike_returnOk _ : IKE P _) t ht
  case delete =>
    unfold fbEntryX; dsimp only
    refine ike_bind (hcode (hlt _ _ _)) fun slot => ?_
    have hd : ∀ cl : Bool, IKE P (fbDeleteX slot >>= fun _ => (NonDetE.returnOk cl : NonDetE (State Unit) Data Bool)) :=
      fun cl => ike_bind (by unfold fbDeleteX; exact ike_handleE (hdel _) fun _ => ike_throw _) fun _ => ike_returnOk _
    intro s hs y hy
    obtain ⟨z, hz, hr⟩ := fbx_mem_bindE hy
    obtain ⟨x, hx, rfl⟩ := fbx_mem_liftE hz
    obtain ⟨e1, hcap⟩ := getCap_capAt hx
    rcases hr with ⟨c, hc, hy⟩ | ⟨e, he, -⟩
    swap; · cases he
    simp only [Except.ok.injEq] at hc
    subst hc
    obtain ⟨c, t⟩ := x
    try dsimp only at e1 hcap hy
    subst s
    cases c
    case nullCap => exact ike_returnOk _ t hs y hy
    case archObjectCap a =>
      cases a
      case pageCap dev p R mt sz m =>
        rcases m with _ | ⟨asid', vaddr⟩
        · try dsimp only at hy
          first | exact hd _ t hs y hy | exact ike_returnOk_bind (hd _) t hs y hy | exact ike_bind (ike_returnOk _) (fun cl => hd cl) t hs y hy
        · try dsimp only at hy
          by_cases hcond : (dd = true ∧ mt = .vmVSpaceMap ∧ dev = false ∧ asid' = asid)
          · rw [if_pos hcond] at hy
            obtain ⟨z2, hz2, hr2⟩ := fbx_mem_bindE hy
            obtain ⟨x2, hx2, rfl⟩ := fbx_mem_liftE hz2
            rcases hr2 with ⟨cl, -, hy⟩ | ⟨e, he, -⟩
            swap; · cases he
            obtain ⟨u1, hu1, hx2⟩ := hx2
            obtain ⟨u2, hu2, hx2⟩ := hx2
            rw [Set.mem_singleton_iff.1 hx2] at hy
            have hP1 := hun _ _ _ _ t hs u1 hu1
            have hv1 : uV u1.2 = uV t := uk_unmapPageUnflushed (uvw := uV t) _ _ _ _ t rfl u1 hu1
            have hc1 : capAt u1.2 slot = some (.archObjectCap (.pageCap dev p R mt sz (some (asid', vaddr)))) := by
              have := congrArg (fun w : UView => w.2.1 slot) hv1
              simp only [uV] at this
              rw [this]; exact hcap
            have hP2 := hset u1.2 dev p R mt sz (some (asid', vaddr)) slot hP1 hc1 u2 hu2
            exact hd _ _ hP2 y hy
          · rw [if_neg hcond] at hy
            first | exact hd _ t hs y hy | exact ike_returnOk_bind (hd _) t hs y hy | exact ike_bind (ike_returnOk _) (fun cl => hd cl) t hs y hy
      all_goals exact ike_throw _ t hs y hy
    all_goals exact ike_throw _ t hs y hy


/-- **`IKE P` of one entry** from the family's leaves for the entry's writes: `cap_insert` of a frame cap,
`perform_page_invocation`, `arch_finalise_cap` of a frame, `empty_slot _ Null`, the unflushed unmap and
`set_cap` of a frame cap (the reads are `fbx_*`). -/
theorem ik_fbEntryX_w {P : State Unit → Prop} (b : Fl4FrameBatchInvocation) (w : Data × Data × Data)
    (hci : ∀ c src dest, IsFrameCap c → IK P (capInsert (Z := Unit) c src dest))
    (hpp : ∀ pi, IK P (performPageInvocation (Z := Unit) pi))
    (haf : ∀ dev p R mt sz m fin, IK P (archFinaliseCap (Z := Unit) (.pageCap dev p R mt sz m) fin))
    (hes : ∀ sl, IK P (emptySlot (Z := Unit) sl .nullCap))
    (hun : ∀ sz vs va p, IK P (unmapPageUnflushed (Z := Unit) sz vs va p))
    (hset : ∀ c sl, IsFrameCap c → IK P (setCap (Z := Unit) c sl)) :
    IKE P (fbEntryX b w) := by
  refine ik_fbEntryX_of b w fbx_lookupTargetSlot fbx_lookupSourceSlot fbx_ensureEmpty fbx_deriveCap
    (fun s c src dest _ hs hc _ _ _ _ _ => hci c src dest hc s hs) (fun sl v => ?_) (fun sl => ?_) hun (fun s dev p R _ sz _ sl hs _ => hset (.archObjectCap (.pageCap dev p R .vmNoMap sz none)) sl trivial s hs)
  · unfold fbMap
    refine ike_bind (ike_liftE (fbx_ik_getCap _)) fun c => ?_
    split
    · refine ike_bind (ike_whenE _ (ike_throw _)) fun _ => ike_bind (fbx_decodePageInvocation _ _ _ _ _) fun iv => ?_
      split
      · exact ike_bind (ike_liftE (hpp _)) fun _ => ike_returnOk _
      · exact ike_liftE ik_fail
    · exact ike_throw _
  · unfold fbDelX
    refine ike_liftE (ik_bind (fbx_ik_getCap _) fun c => ?_)
    split
    · exact ik_bind (fbx_isFinalCap _) fun _ => ik_bind (haf _ _ _ _ _ _ _) fun _ => hes _
    · exact ik_fail

/-- **`IK P` of the batch** from the family's leaves for the entry's writes and the final flush. -/
theorem ik_performFrameBatchW {P : State Unit → Prop} (b : Fl4FrameBatchInvocation)
    (hci : ∀ c src dest, IsFrameCap c → IK P (capInsert (Z := Unit) c src dest))
    (hpp : ∀ pi, IK P (performPageInvocation (Z := Unit) pi))
    (haf : ∀ dev p R mt sz m fin, IK P (archFinaliseCap (Z := Unit) (.pageCap dev p R mt sz m) fin))
    (hes : ∀ sl, IK P (emptySlot (Z := Unit) sl .nullCap))
    (hun : ∀ sz vs va p, IK P (unmapPageUnflushed (Z := Unit) sz vs va p))
    (hset : ∀ c sl, IsFrameCap c → IK P (setCap (Z := Unit) c sl))
    (hf : IK P (flushAll (Z := Unit) b.vspace b.asid)) :
    IK P (performFrameBatch (Z := Unit) b) :=
  ik_performFrameBatchX (fun w => ik_fbEntryX_w b w hci hpp haf hes hun hset) hf

end

end Fl4Proofs.P3.SInv
