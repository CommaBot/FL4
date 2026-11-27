/-
P3x for virtualization (line virt, gen 23, item 2): **the spec side of the whole `resetUntypedCap`** and `VRelAll`
after the whole reset step.

Gen 22 (P3/VirtResetV) proved `VRelAll V` across FL4's `reset_untyped` (its `WFrame` over `ResetW`) given that the
spec's VCPUs are kept off the region (`hs`), and `vcpuAt_detype` for the spec's `delete_objects` alone. Here the
spec half is closed for every outcome of l4v's `reset_untyped_cap` (Fl4Spec `resetUntypedCap`, Retype.lean l. 203):

* `vcF σ` (the spec's VCPU contents, `vcpuAt` at every reference) is kept by `do_machine_op` (`vc_dmo`), by
  `do_extended_op` (`vc_deo`), by `set_object` of a non-VCPU object over a non-VCPU object (`vc_setObject`), by
  `set_cap` (`vc_setCap`: its object is a CNode or a TCB) and by `preemption_point` (`vc_pp`, MCS: it only touches
  the work units, the time fields and reads the current SC).
* **`vc_reset`**: every outcome of `resetUntypedCap sl` from a state whose cap at `sl` is `untypedCap dev pu sz fi`
  keeps `vcpuAt` at every reference off `regionSet pu sz` — an unused cap (`fi = 0`) changes nothing; otherwise
  `delete_objects` detypes the region (`vcpuAt_detype`) and the clearing loop (`do_machine_op`, `set_cap`,
  `preemption_point`, the arch hook) keeps every VCPU. Preempted outcomes included (`NAll` over the whole outcome
  set, errors too).
* **`VRelAll.of_resetFull`**: FL4's reset frame (`WFrame` over `ResetW`, UntypedFrame `reset_frame`) at the slot of
  an untyped cap without MDB children, `VCapped V` (P3/VirtResetV), and any outcome of the spec's reset from the
  related cap give **`VRelAll V` after the whole reset step** — `vcpu_out_of_reset` places every VCPU of `V` off
  the region, so `vc_reset` supplies gen 22's `hs` and `VRelAll.of_reset_noChildren` closes it.

No [J]/[P]/[W] premise. New file only; no existing statement changed.
-/
import Fl4Proofs.P3.VirtResetV
import Fl4Proofs.P3.UtRetResetJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtResetSpecV
open fl4_core Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.Vs Fl4Proofs.P3.VirtInitWalk Fl4Proofs.P3.VirtVKeep
open Fl4Proofs.P3.VirtResetV

noncomputable section

/-- The spec's VCPU contents at every reference. -/
def vcF (σ : State Unit) : ObjRef → Option VcpuState := fun o => vcpuAt σ o

theorem vcpuAt_of_ne {σ : State Unit} {p : ObjRef} {o : KernelObject} (h : σ.kheap p = some o)
    (ho : ∀ v, o ≠ .archObj (.vcpu v)) : vcpuAt σ p = none := by
  unfold vcpuAt; rw [h]
  split
  · rename_i st e
    exact absurd (Option.some.inj e) (ho st)
  · rfl

theorem vc_dmo {α : Type} (mop : NonDet MachineState α) : FK vcF (doMachineOp (Z := Unit) mop) := by
  unfold doMachineOp
  refine dk_bind (dk_gets _) (fun _ => dk_bind (dk_selectF _) (fun x => ?_))
  obtain ⟨r, ms⟩ := x
  exact dk_bind (dk_modify (fun σ => rfl)) (fun _ => dk_pure _)

theorem vc_deo (eop : DetExtMonad Unit) : FK vcF (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine dk_bind dk_get (fun _ => dk_bind (dk_selectF _) (fun _ => ?_))
  split
  exact dk_modify (fun σ => rfl)

/-- `set_object` of a non-VCPU object (its type check makes the old object a non-VCPU too) keeps `vcF`. -/
theorem vc_setObject (p : ObjRef) (o : KernelObject) (ho : ∀ v, o ≠ .archObj (.vcpu v))
    (hk : ∀ k, aType k = aType o → ∀ v, k ≠ .archObj (.vcpu v)) : FK vcF (setObject (Z := Unit) p o) := by
  intro σ x ⟨y, hy, hx⟩
  obtain ⟨k, hk', hyk⟩ : ∃ k, σ.kheap p = some k ∧ y = (k, σ) := by
    unfold getObject NonDet.getsThe readObject at hy
    cases h : σ.kheap p with
    | none => rw [h] at hy; exact hy.elim
    | some k => rw [h] at hy; exact ⟨k, rfl, Set.mem_singleton_iff.1 hy⟩
  subst hyk
  obtain ⟨z, hz, hx⟩ := hx
  obtain ⟨hty, rfl⟩ := hz
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  funext o'
  unfold vcF
  by_cases e : o' = p
  · subst e
    rw [vcpuAt_of_ne (o := o) (by simp) ho, vcpuAt_of_ne hk' (hk k hty)]
  · unfold vcpuAt
    simp only [Function.update_of_ne e]

theorem vc_bind_pure {α γ : Type} (a : α) {g : α → NonDet (State Unit) γ} (h : FK vcF (g a)) :
    FK vcF ((pure a : NonDet (State Unit) α) >>= g) := by
  intro σ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  exact h σ x hx

theorem vc_bind_fail {α γ : Type} {g : α → NonDet (State Unit) γ} :
    FK vcF ((NonDet.fail : NonDet (State Unit) α) >>= g) := by
  intro σ x ⟨y, hy, _⟩
  exact hy.elim

theorem aType_cnode_ne (sz : Nat) (cn : CnodeContents) (k : KernelObject) (h : aType k = aType (.cnode sz cn)) :
    ∀ v, k ≠ .archObj (.vcpu v) := by
  intro v e; subst e
  have e1 : aType (.archObj (.vcpu v)) = .aArch (aaType (.vcpu v)) := rfl
  rw [e1] at h
  by_cases hw : wellFormedCnodeN sz cn
  · rw [show aType (.cnode sz cn) = .aCapTable sz from if_pos hw] at h; cases h
  · rw [show aType (.cnode sz cn) = .aGarbage (cteLevelBits + sz) from if_neg hw] at h; cases h

theorem aType_tcb_ne (t : Tcb) (k : KernelObject) (h : aType k = aType (.tcb t)) :
    ∀ v, k ≠ .archObj (.vcpu v) := by
  intro v e; subst e; cases h

theorem vc_setCap (cap : Cap) (sl : CslotPtr) : FK vcF (setCap (Z := Unit) cap sl) := by
  obtain ⟨o, c⟩ := sl
  unfold setCap
  refine dk_bind (dk_getObject o) (fun obj => ?_)
  cases obj <;> simp only []
  all_goals repeat (first
    | exact vc_bind_pure _ (vc_setObject _ _ (fun _ h => by cases h) (aType_cnode_ne _ _))
    | exact vc_bind_pure _ (vc_setObject _ _ (fun _ h => by cases h) (aType_tcb_ne _))
    | exact vc_bind_fail
    | split)

theorem vc_pp : FKE vcF (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint orChoiceE updateTimeStamp getScActive
  repeat' (first
    | exact vc_dmo _
    | exact vc_deo _
    | dk_step0)

/-- **The spec's reset keeps every VCPU off its region** (module docstring), on every outcome. -/
theorem vc_reset {sl : CslotPtr} {σ : State Unit} {dev : Bool} {pu : ObjRef} {sz fi : Nat}
    (hg : getCap (Z := Unit) sl σ = ({(.untypedCap dev pu sz fi, σ)}, False)) :
    NAll (resetUntypedCap (Z := Unit) sl).run σ
      (fun y => ∀ o, o ∉ regionSet pu sz → vcpuAt y.2 o = vcpuAt σ o) := by
  unfold resetUntypedCap
  apply nallE_bind
  refine nall_det (run_liftE hg) ?_
  dsimp only
  by_cases hfi : fi = 0
  · simp only [NonDetE.returnOk, ndE_pure_bind, Fl4Spec.bitsOf, Fl4Spec.objRefOf, Fl4Spec.freeIndexOf,
      Fl4Spec.isDeviceUntypedCap, hfi, ↓reduceIte]
    refine NAll.mono (fke_nall (f := vcF) ?_ σ) fun x hx o _ => congrFun hx o
    dk_auto0
  simp only [NonDetE.returnOk, ndE_pure_bind, Fl4Spec.bitsOf, Fl4Spec.objRefOf, Fl4Spec.freeIndexOf,
    Fl4Spec.isDeviceUntypedCap, hfi, ↓reduceIte]
  apply nallE_bind
  apply nall_liftE
  intro y hy
  have hD : ∀ o, o ∉ regionSet pu sz → vcpuAt y.2 o = vcpuAt σ o := by
    unfold deleteObjects at hy
    obtain ⟨z, hz1, hz⟩ := hy
    rw [Set.mem_singleton_iff.1 hz]
    have e := vc_dmo _ σ z hz1
    intro o ho
    rw [vcpuAt_detype ho]
    exact congrFun e o
  dsimp only
  refine NAll.mono (P := fun x => vcF x.2 = vcF y.2) ?_ (fun x hx o ho => (congrFun hx o).trans (hD o ho))
  refine fke_nall ?_ y.2
  apply dke_ite
  · refine dke_bind (dke_liftE (dk_bind (dk_unless _ (vc_dmo _)) (fun _ => vc_setCap _ _))) (fun _ => ?_)
    unfold archPostResetUntyped; exact dke_liftE (dk_pure _)
  · refine dke_bind (dke_mapMEx (fun i => ?_) _) (fun _ => ?_)
    · exact dke_bind (dke_liftE (vc_dmo _)) (fun _ => dke_bind (dke_liftE (vc_setCap _ _)) (fun _ => vc_pp))
    · unfold archPostResetUntyped; exact dke_liftE (dk_pure _)

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`VRelAll V` after the whole reset step** (module docstring): FL4's reset frame of an untyped cap without
children and any outcome of the spec's `resetUntypedCap` from the related cap. -/
theorem VRelAll.of_resetFull {V : Set U64} (hf : ∀ v ∈ V, VFits v) {s s' : S} {σ : State Unit}
    (h : VRelAll V (memW st s) σ) {G : MdbGhost} (hU : UtInv (L.mem s) G)
    (hI : MdbInv (L.mem s) G) (hVC : VCapped V (L.mem s) G) {x p sb fi : U64} {d : Bool}
    (hx : x ∈ G.chains.flatten) (hcx : capV (L.mem s) x = .Untyped p sb fi d) (hnc : ∀ y, ¬ Mdb.Desc G.par y x)
    {PW : U64 → Prop} (hw : WFrame (L := L) s s' (ResetW p sb x PW))
    (hp8 : p.val % 8 = 0) (hsb3 : 3 ≤ sb.val) (hx8 : x.val % 8 = 0)
    (hxV : ∀ v ∈ V, x.val + 16 ≤ v.val ∨ v.val + 32768 ≤ x.val) (hPW : ∀ b, PW b → P1.Aligned b → OffV V b)
    {sl : CslotPtr} {dev : Bool} {fi' : Nat}
    (hg : getCap (Z := Unit) sl σ = ({(.untypedCap dev p.bv sb.val fi', σ)}, False))
    {y} (hy : y ∈ ((resetUntypedCap (Z := Unit) sl).run σ).1) :
    VRelAll V (memW st s') y.2 := by
  have hout := vcpu_out_of_reset hU hI hVC (fun v hv => (hf v hv).2) hx hcx hnc
  have hsb := capV_ut_sb hcx
  have hreg := hU.reg x hx (by rw [hcx]; exact ok_inj (phys_eq _).symm)
  rw [hcx] at hreg
  obtain ⟨-, -, hfit⟩ := ut_range hsb hreg
  refine VRelAll.of_reset_noChildren hf h hU hI hVC hx hcx hnc hw hp8 hsb3 hx8 hxV hPW (fun v hv => ?_)
  refine vc_reset hg y hy v.bv ?_
  rw [regionSet_iff p v sb.val hsb hfit]
  rcases hout v hv with e | e <;> omega

end

end
end Fl4Proofs.P3.VirtResetSpecV
