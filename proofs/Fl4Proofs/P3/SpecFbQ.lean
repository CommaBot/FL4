/-
P3 (issue #16, fb3f): **the frame batch's map with a family-chosen decode fact** (spec side only).

`ik_fbMapQ`: `P` across `fbMap b sl v` from `P` across the page decode and
across `performPageInvocation` of a decoded invocation satisfying any `Q`
the family proves of `decodePageInvocation`'s outcomes when the slot holds
the frame (SpecFbM's `ik_fbMapF` fixes `Q` to `ArchSpecOKN`, which sits
downstream of modules that need the batch, e.g. SpecInvIoPortsS).
-/
import Fl4Proofs.P3.SpecFbX
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec Fl4Proofs.P3.SInvU

noncomputable section

theorem fbx_whenE_state {P : Prop} [Decidable P] {e : SyscallError} {s : State Unit}
    {z : Except SyscallError Unit × State Unit}
    (h : z ∈ ((NonDetE.whenE P (NonDetE.throwError e) : SEMonad Unit Unit).run s).1) : z.2 = s := by
  unfold NonDetE.whenE at h
  split at h
  · exact congrArg Prod.snd (Set.mem_singleton_iff.1 h)
  · exact congrArg Prod.snd (Set.mem_singleton_iff.1 h)

/-- **`P` across `fbMap`**, the perform's step given any fact `Q` the family proves of the decoded page
invocation at the decode's outcome (when the slot holds the frame). -/
theorem ik_fbMapQ {P : State Unit → Prop} {Q : State Unit → ArchInvocation → Prop} (b : Fl4FrameBatchInvocation)
    (sl : CslotPtr) (v : Data)
    (hd : ∀ dev p R mt sz m, IKE P (decodePageInvocation (Z := Unit) fbPageMapLabel [v, b.mapRights, b.attr] sl
      (.pageCap dev p R mt sz m) [(.archObjectCap (.pml4Cap b.vspace (some b.asid)), sl)]))
    (hq : ∀ s dev p R mt sz m, capAt s sl = some (.archObjectCap (.pageCap dev p R mt sz m)) →
      ∀ iv t, ((.ok iv, t) : Except SyscallError ArchInvocation × State Unit) ∈
        ((decodePageInvocation (Z := Unit) fbPageMapLabel [v, b.mapRights, b.attr] sl
          (.pageCap dev p R mt sz m) [(.archObjectCap (.pml4Cap b.vspace (some b.asid)), sl)]).run s).1 → Q t iv)
    (hp : ∀ s pi, P s → Q s (.invokePage pi) → ∀ x ∈ (performPageInvocation (Z := Unit) pi s).1, P x.2) :
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
      · rw [fbx_whenE_state hz2] at hy
        obtain ⟨z3, hz3, ⟨iv, hiv, hy⟩ | ⟨e3, -, rfl⟩⟩ := fbx_mem_bindE hy
        · have hok : Q z3.2 iv := by
            obtain ⟨r3, s3⟩ := z3
            simp only at hiv; subst hiv
            exact hq σ dev p R mt sz m hcap iv s3 hz3
          have hP3 : P z3.2 := hd dev p R mt sz m σ hσ z3 hz3
          split at hy
          · rename_i pi
            obtain ⟨z4, hz4, ⟨_, -, hy⟩ | ⟨e4, he4, rfl⟩⟩ := fbx_mem_bindE hy
            · obtain ⟨x4, hx4, rfl⟩ := fbx_mem_liftE hz4
              rw [Set.mem_singleton_iff.1 hy]
              exact hp z3.2 pi hP3 hok x4 hx4
            · obtain ⟨w4, -, hw4⟩ := fbx_mem_liftE hz4
              rw [hw4] at he4; cases he4
          · obtain ⟨w4, hw4, -⟩ := fbx_mem_liftE hy
            exact hw4.elim
        · exact hd dev p R mt sz m σ hσ z3 hz3
      · rw [fbx_whenE_state hz2]; exact hσ
    · rw [(Prod.mk.inj (Set.mem_singleton_iff.1 hy)).2]; exact hσ
  · obtain ⟨w, -, hw⟩ := fbx_mem_liftE hz
    rw [hw] at he; cases he

end

end Fl4Proofs.P3.SInv
