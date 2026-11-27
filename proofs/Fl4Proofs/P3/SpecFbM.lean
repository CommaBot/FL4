/-
P3 (issue #16, fb3d): **the frame batch's map and frame delete, for the
cap-sensitive families** (spec side only).

`fbMap b sl v` and `fbDelX sl` both start by reading `sl`; a family whose
cap writes need facts about the slot written (IfLive, `UtInv''`, the IRQ-node
families) gets them here:

* **`okv_decodePageInvocationF`**: the decoded map invocation is `ArchSpecOKN`
  at the decode's view, when the invoked slot holds the frame cap (no fact
  about the extra cap: the batch passes its PML4 cap with a placeholder slot).
* **`ik_fbMapF`**: `P` across `fbMap`, from `P` across the decode and from
  `P` across `performPageInvocation` of an `ArchSpecOKN` invocation (the
  family's existing x64 map / unmap / get-address lemma).
* **`ik_fbDelXF`**: `P` across `fbDelX`, from `P` across `isFinalCap` /
  `archFinaliseCap` and from `P` across `emptySlot sl Null` at a state where
  `sl` still holds the frame cap (both earlier steps keep the cap view).
-/
import Fl4Proofs.P3.SpecFbX
import Fl4Proofs.P3.SpecInvUtP1
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 4000000

/-- The decoded map / unmap / get-address of a frame cap held in the invoked slot. -/
theorem okv_decodePageInvocationF {w : UView} (label : Data) (args : List Data) (cte : CslotPtr)
    (dev : Bool) (p : ObjRef) (R : VMRights) (mt : VMMapType) (sz : VMPageSize) (m : Option (Asid × VSpaceRef))
    (ex : List (Cap × CslotPtr)) (hc : w.2.1 cte = some (.archObjectCap (.pageCap dev p R mt sz m))) :
    OkV w (ArchSpecOKN w) (decodePageInvocation (Z := Unit) label args cte (.pageCap dev p R mt sz m) ex) := by
  simp only [decodePageInvocation]
  repeat' okva_step
  all_goals first | exact okv_returnOk trivial | exact okv_returnOk hc | exact okv_returnOk ⟨_, hc, refEq_arch rfl rfl, nnu_arch _⟩

theorem fbm_whenE_state {P : Prop} [Decidable P] {e : SyscallError} {s : State Unit}
    {z : Except SyscallError Unit × State Unit}
    (h : z ∈ ((NonDetE.whenE P (NonDetE.throwError e) : SEMonad Unit Unit).run s).1) : z.2 = s := by
  unfold NonDetE.whenE at h
  split at h
  · exact congrArg Prod.snd (Set.mem_singleton_iff.1 h)
  · exact congrArg Prod.snd (Set.mem_singleton_iff.1 h)

/-- **`P` across `fbMap`.** -/
theorem ik_fbMapF {P : State Unit → Prop} (b : Fl4FrameBatchInvocation) (sl : CslotPtr) (v : Data)
    (hd : ∀ dev p R mt sz m, IKE P (decodePageInvocation (Z := Unit) fbPageMapLabel [v, b.mapRights, b.attr] sl
      (.pageCap dev p R mt sz m) [(.archObjectCap (.pml4Cap b.vspace (some b.asid)), sl)]))
    (hp : ∀ s pi, P s → ArchSpecOKN (uV s) (.invokePage pi) →
      ∀ x ∈ (performPageInvocation (Z := Unit) pi s).1, P x.2) :
    IKE P (fbMap (Z := Unit) b sl v) := by
  intro σ hσ y hy
  unfold fbMap at hy
  obtain ⟨z, hz, ⟨c, hc, hy⟩ | ⟨e, he, rfl⟩⟩ := fbx_mem_bindE hy
  · obtain ⟨z', hz', rfl⟩ := fbx_mem_liftE hz
    obtain ⟨e1, hcap⟩ := getCap_capAt hz'
    simp only [Except.ok.injEq] at hc
    subst hc
    dsimp only at hy
    rw [e1] at hy
    split at hy
    · rename_i dev p R mt sz m heq
      rw [heq] at hcap
      obtain ⟨z2, hz2, ⟨a2, -, hy⟩ | ⟨e2, -, rfl⟩⟩ := fbx_mem_bindE hy
      · rw [fbm_whenE_state hz2] at hy
        obtain ⟨z3, hz3, ⟨iv, hiv, hy⟩ | ⟨e3, -, rfl⟩⟩ := fbx_mem_bindE hy
        · have hv3 : uV z3.2 = uV σ := uk_decodePageInvocation (uvw := uV σ) _ _ _ _ _ σ rfl z3 hz3
          have hok : ArchSpecOKN (uV σ) iv := by
            obtain ⟨r3, s3⟩ := z3
            simp only at hiv; subst hiv
            exact okv_decodePageInvocationF _ _ _ _ _ _ _ _ _ _ hcap σ rfl iv s3 hz3
          have hP3 : P z3.2 := hd dev p R mt sz m σ hσ z3 hz3
          split at hy
          · rename_i pi
            obtain ⟨z4, hz4, ⟨_, -, hy⟩ | ⟨e4, he4, rfl⟩⟩ := fbx_mem_bindE hy
            · obtain ⟨x4, hx4, rfl⟩ := fbx_mem_liftE hz4
              rw [Set.mem_singleton_iff.1 hy]
              exact hp z3.2 pi hP3 (by rw [hv3]; exact hok) x4 hx4
            · obtain ⟨w4, -, hw4⟩ := fbx_mem_liftE hz4
              rw [hw4] at he4; cases he4
          · obtain ⟨w4, hw4, -⟩ := fbx_mem_liftE hy
            exact hw4.elim
        · exact hd dev p R mt sz m σ hσ z3 hz3
      · rw [fbm_whenE_state hz2]; exact hσ
    · rw [(Prod.mk.inj (Set.mem_singleton_iff.1 hy)).2]; exact hσ
  · obtain ⟨w, -, hw⟩ := fbx_mem_liftE hz
    rw [hw] at he; cases he

/-- **`P` across `fbDelX`.** -/
theorem ik_fbDelXF {P : State Unit → Prop} (sl : CslotPtr)
    (hf : ∀ c, IK P (isFinalCap (Z := Unit) c))
    (ha : ∀ c x, IK P (archFinaliseCap (Z := Unit) c x))
    (he : ∀ s dev p R mt sz m, P s → capAt s sl = some (.archObjectCap (.pageCap dev p R mt sz m)) →
      ∀ x ∈ (emptySlot (Z := Unit) sl .nullCap s).1, P x.2) :
    IKE P (fbDelX sl) := by
  intro σ hσ y hy
  unfold fbDelX at hy
  obtain ⟨x, hx, rfl⟩ := fbx_mem_liftE hy
  obtain ⟨z, hz, hx⟩ := hx
  obtain ⟨e1, hcap⟩ := getCap_capAt hz
  obtain ⟨c, s1⟩ := z
  simp only at e1 hcap; subst e1
  dsimp only at hx
  split at hx
  · rename_i dev p R mt sz m
    obtain ⟨z1, hz1, hx⟩ := hx
    have hv1 : uV z1.2 = uV s1 := uk_isFinalCap (uvw := uV s1) _ s1 rfl z1 hz1
    have hP1 := hf _ s1 hσ z1 hz1
    obtain ⟨z2, hz2, hx⟩ := hx
    have hv2 : uV z2.2 = uV z1.2 := uk_archFinaliseCap (uvw := uV z1.2) _ _ z1.2 rfl z2 hz2
    have hP2 := ha _ _ z1.2 hP1 z2 hz2
    have hc2 : capAt z2.2 sl = some (.archObjectCap (.pageCap dev p R mt sz m)) := by
      have := congrArg (fun w : UView => w.2.1 sl) (hv2.trans hv1)
      simp only [uV] at this
      rw [this]; exact hcap
    exact he z2.2 dev p R mt sz m hP2 hc2 x hx
  · exact hx.elim


/-- The slot a decoded frame map writes. -/
def PgSl (cte : CslotPtr) : ArchInvocation → Prop
  | .invokePage (.pageMap _ sl _ _) => sl = cte
  | _ => True

/-- `okv_decodePageInvocationF`, and a decoded map writes the invoked slot. -/
theorem okv_decodePageInvocationF2 {w : UView} (label : Data) (args : List Data) (cte : CslotPtr)
    (dev : Bool) (p : ObjRef) (R : VMRights) (mt : VMMapType) (sz : VMPageSize) (m : Option (Asid × VSpaceRef))
    (ex : List (Cap × CslotPtr)) (hc : w.2.1 cte = some (.archObjectCap (.pageCap dev p R mt sz m))) :
    OkV w (fun iv => ArchSpecOKN w iv ∧ PgSl cte iv)
      (decodePageInvocation (Z := Unit) label args cte (.pageCap dev p R mt sz m) ex) := by
  simp only [decodePageInvocation]
  repeat' okva_step
  all_goals first | exact okv_returnOk ⟨trivial, trivial⟩ | exact okv_returnOk ⟨hc, trivial⟩ | exact okv_returnOk ⟨⟨_, hc, refEq_arch rfl rfl, nnu_arch _⟩, rfl⟩ | exact okv_returnOk ⟨trivial, rfl⟩

/-- **`P` across `fbMap`**, the perform's step given the decode's facts and the frame cap in the slot. -/
theorem ik_fbMapF2 {P : State Unit → Prop} (b : Fl4FrameBatchInvocation) (sl : CslotPtr) (v : Data)
    (hd : ∀ dev p R mt sz m, IKE P (decodePageInvocation (Z := Unit) fbPageMapLabel [v, b.mapRights, b.attr] sl
      (.pageCap dev p R mt sz m) [(.archObjectCap (.pml4Cap b.vspace (some b.asid)), sl)]))
    (hp : ∀ s pi dev p R mt sz m, P s → ArchSpecOKN (uV s) (.invokePage pi) → PgSl sl (.invokePage pi) →
      capAt s sl = some (.archObjectCap (.pageCap dev p R mt sz m)) →
      ∀ x ∈ (performPageInvocation (Z := Unit) pi s).1, P x.2) :
    IKE P (fbMap (Z := Unit) b sl v) := by
  intro σ hσ y hy
  unfold fbMap at hy
  obtain ⟨z, hz, ⟨c, hc, hy⟩ | ⟨e, he, rfl⟩⟩ := fbx_mem_bindE hy
  · obtain ⟨z', hz', rfl⟩ := fbx_mem_liftE hz
    obtain ⟨e1, hcap⟩ := getCap_capAt hz'
    simp only [Except.ok.injEq] at hc
    subst hc
    dsimp only at hy
    rw [e1] at hy
    split at hy
    · rename_i dev p R mt sz m heq
      rw [heq] at hcap
      obtain ⟨z2, hz2, ⟨a2, -, hy⟩ | ⟨e2, -, rfl⟩⟩ := fbx_mem_bindE hy
      · rw [fbm_whenE_state hz2] at hy
        obtain ⟨z3, hz3, ⟨iv, hiv, hy⟩ | ⟨e3, -, rfl⟩⟩ := fbx_mem_bindE hy
        · have hv3 : uV z3.2 = uV σ := uk_decodePageInvocation (uvw := uV σ) _ _ _ _ _ σ rfl z3 hz3
          have hok : ArchSpecOKN (uV σ) iv ∧ PgSl sl iv := by
            obtain ⟨r3, s3⟩ := z3
            simp only at hiv; subst hiv
            exact okv_decodePageInvocationF2 _ _ _ _ _ _ _ _ _ _ hcap σ rfl iv s3 hz3
          have hP3 : P z3.2 := hd dev p R mt sz m σ hσ z3 hz3
          have hc3 : capAt z3.2 sl = some (.archObjectCap (.pageCap dev p R mt sz m)) := by
            have := congrArg (fun w : UView => w.2.1 sl) hv3
            simp only [uV] at this
            rw [this]; exact hcap
          split at hy
          · rename_i pi
            obtain ⟨z4, hz4, ⟨_, -, hy⟩ | ⟨e4, he4, rfl⟩⟩ := fbx_mem_bindE hy
            · obtain ⟨x4, hx4, rfl⟩ := fbx_mem_liftE hz4
              rw [Set.mem_singleton_iff.1 hy]
              exact hp z3.2 pi dev p R mt sz m hP3 (by rw [hv3]; exact hok.1) hok.2 hc3 x4 hx4
            · obtain ⟨w4, -, hw4⟩ := fbx_mem_liftE hz4
              rw [hw4] at he4; cases he4
          · obtain ⟨w4, hw4, -⟩ := fbx_mem_liftE hy
            exact hw4.elim
        · exact hd dev p R mt sz m σ hσ z3 hz3
      · rw [fbm_whenE_state hz2]; exact hσ
    · rw [(Prod.mk.inj (Set.mem_singleton_iff.1 hy)).2]; exact hσ
  · obtain ⟨w, -, hw⟩ := fbx_mem_liftE hz
    rw [hw] at he; cases he

end

end Fl4Proofs.P3.SInv
