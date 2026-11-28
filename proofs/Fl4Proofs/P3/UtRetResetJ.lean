/-
P3 (DESIGN.md §9), untyped: **the retype with a reset at `J`** (handoff/utj.md
Round 13, item 3d): FL4's restart, then `untyped::retype` with `reset = true`
(`reset_untyped`, then the retype body from the reset's state), against the
spec's restart and `invoke_untyped` with a reset (`reset_untyped_cap`, then
the invocation without one from its outcome, `invoke_reset_ok`; a preempted
reset is the invocation's error outcome, `invoke_reset_err`).

* `retype_reset_wp`: FL4's `untyped::retype` with a reset is `reset_untyped`,
  then (on `Ok`) the retype without one.
* `khT`/`entF`, `reset_khT`, `ent_reset`: every outcome of the spec's reset of
  a used cap keeps every object's type but its region's (`delete_objects`), and
  the current thread, the idle thread and the scheduler action.
* `utRetPostJ_of_reset`/`utRetPostJ_of_preempt`: `UtRetPostJ` of the
  invocation with a reset from a body's `UtBodyPost` after the reset, or a
  preempted reset.
* `UtBodyHyp`: a retype body (UtEpRet's `JAtZ.utEpBodyJ` shape) for one
  invocation's arguments, from any `JAtZ` state.
* `JAtZ.utResetJ`: the composition at `J`: the restart (`JAtZ.restartJ`), the
  reset (`JAtZ.reset_untypedJ`; an unused cap, free index 0, resets nothing:
  `retype_reset_unused`), then the body at the reset's state, whose
  premises are re-established there: `Entered` (`ent_reset`), the arguments'
  `RetCtx` (the destination CNode off the region, `cnode_off_childless`; its
  slots and the node cap's slot kept, `ResetJPost`'s slot frame),
  `BufObjHyp`/`ArchFitHyp` (`reset_khT`, `SpecFree`), the kept references
  (the dropped heap has no object in the region).
  Premises: those of `JAtZ.reset_untypedJ` at the restart's state (`PPPlat`,
  `resetChunkBits = 16` [P]; `VsReachMiss` [J], here with no extra roots), the
  no-reset retype's (`BufObjHyp`, `ArchFitHyp`, `RegionUnrefJ` [J]), `hRd0`
  [J] (as the CNode decodes, for `PPR0`).
-/
import Fl4Proofs.P3.UtEpRet
import Fl4Proofs.P3.UtResetTopJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
  Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **FL4's retype with a reset** (`untyped::retype`, `reset = true`):
`reset_untyped`, then on `Ok` the retype without a reset from its state; an
error ends the retype with it. -/
theorem retype_reset_wp {A' : Type} (arI : machine.Arch A') (s : S) (a : A') (slot base nt us dest off win : U64)
    (dev : Bool) {P Q : core.result.Result Unit error.Exc × S × A' → Prop}
    (hr : untyped.reset_untyped st arI s a slot ⦃ P ⦄)
    (hok : ∀ s1 a1, P (.Ok (), s1, a1) → untyped.retype st arI s1 a1 slot false base nt us dest off win dev ⦃ Q ⦄)
    (herr : ∀ e s1 a1, P (.Err e, s1, a1) → Q (.Err e, s1, a1)) :
    untyped.retype st arI s a slot true base nt us dest off win dev ⦃ Q ⦄ := by
  unfold untyped.retype
  simp only [↓reduceIte]
  refine WP.spec_bind hr ?_
  rintro ⟨r, s1, a1⟩ hP
  cases r with
  | Ok u =>
    cases u
    have h := hok s1 a1 hP
    unfold untyped.retype at h
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair]
    exact h
  | Err e =>
    simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch, uncurry_apply_pair,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
    simp only [bind_tc_ok, bind_ok]
    exact (WP.spec_ok _).2 (herr e s1 a1 hP)

end

/-! ## The spec's reset: what it keeps -/

section SpecKeep
open Fl4Spec Fl4Proofs.P3.Vs

/-- The heap's object types. -/
def khT (σ : State Unit) : ObjRef → Option AType := fun o => (σ.kheap o).map aType

/-- The current thread, the idle thread and the scheduler action. -/
def entF (σ : State Unit) : ObjRef × ObjRef × SchedulerAction := (σ.curThread, σ.idleThread, σ.schedulerAction)

theorem kt_dmo {α : Type} (mop : NonDet MachineState α) : FK khT (doMachineOp (Z := Unit) mop) := by
  unfold doMachineOp
  refine dk_bind (dk_gets _) (fun _ => dk_bind (dk_selectF _) (fun x => ?_))
  obtain ⟨r, ms⟩ := x
  exact dk_bind (dk_modify (fun σ => rfl)) (fun _ => dk_pure _)

theorem kt_deo (eop : DetExtMonad Unit) : FK khT (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine dk_bind dk_get (fun _ => dk_bind (dk_selectF _) (fun _ => ?_))
  split
  exact dk_modify (fun σ => rfl)

theorem kt_setObject (p : ObjRef) (o : KernelObject) : FK khT (setObject (Z := Unit) p o) := by
  intro σ x ⟨y, hy, hx⟩
  obtain ⟨k, hk⟩ : ∃ k, σ.kheap p = some k ∧ y = (k, σ) := by
    unfold getObject NonDet.getsThe readObject at hy
    cases h : σ.kheap p with
    | none => rw [h] at hy; exact hy.elim
    | some k => rw [h] at hy; exact ⟨k, rfl, Set.mem_singleton_iff.1 hy⟩
  obtain ⟨hk, rfl⟩ := hk
  obtain ⟨z, hz, hx⟩ := hx
  obtain ⟨hty, rfl⟩ := hz
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  funext o'
  unfold khT
  by_cases e : o' = p
  · subst e; simp only [Function.update_self, hk, Option.map_some]; exact congrArg some hty.symm
  · simp only [Function.update_of_ne e]

theorem kt_setCap (cap : Cap) (sl : CslotPtr) : FK khT (setCap (Z := Unit) cap sl) := by
  obtain ⟨o, c⟩ := sl
  unfold setCap
  refine dk_bind (dk_getObject o) (fun obj => ?_)
  cases obj <;> simp only [] <;> repeat (first | exact kt_setObject _ _ | dk_step0)

theorem kt_pp : FKE khT (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint orChoiceE updateTimeStamp getScActive
  repeat' (first
    | exact kt_dmo _
    | exact kt_deo _
    | dk_step0)

theorem ent_dmo {α : Type} (mop : NonDet MachineState α) : FK entF (doMachineOp (Z := Unit) mop) := by
  unfold doMachineOp
  refine dk_bind (dk_gets _) (fun _ => dk_bind (dk_selectF _) (fun x => ?_))
  obtain ⟨r, ms⟩ := x
  exact dk_bind (dk_modify (fun σ => rfl)) (fun _ => dk_pure _)

theorem ent_deo (eop : DetExtMonad Unit) : FK entF (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine dk_bind dk_get (fun _ => dk_bind (dk_selectF _) (fun _ => ?_))
  split
  exact dk_modify (fun σ => rfl)

theorem ent_setObject (p : ObjRef) (o : KernelObject) : FK entF (setObject (Z := Unit) p o) := by
  unfold setObject; dk_auto0

theorem ent_setCap (cap : Cap) (sl : CslotPtr) : FK entF (setCap (Z := Unit) cap sl) := by
  obtain ⟨o, c⟩ := sl
  unfold setCap
  refine dk_bind (dk_getObject o) (fun obj => ?_)
  cases obj <;> simp only [] <;> repeat (first | exact ent_setObject _ _ | dk_step0)

theorem ent_getCap (sl : CslotPtr) : FK entF (getCap (Z := Unit) sl) := by
  obtain ⟨o, c⟩ := sl
  unfold getCap
  refine dk_bind (dk_getObject o) (fun obj => ?_)
  cases obj <;> simp only [] <;> repeat dk_step0

theorem ent_pp : FKE entF (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint orChoiceE updateTimeStamp getScActive
  repeat' (first
    | exact ent_dmo _
    | exact ent_deo _
    | dk_step0)

/-- **The reset keeps the current thread, the idle thread and the scheduler
action** (its outcomes, preempted or not). -/
theorem ent_reset (sl : CslotPtr) : FKE entF (resetUntypedCap (Z := Unit) sl) := by
  unfold resetUntypedCap
  refine dke_bind (dke_liftE (ent_getCap _)) (fun cap => ?_)
  refine dke_bind (dke_returnOk _) (fun _ => dke_bind (dke_returnOk _) (fun _ => ?_))
  refine dke_ite _ (dke_returnOk _) ?_
  refine dke_bind (dke_liftE ?_) (fun _ => dke_bind (dke_returnOk _) (fun _ => ?_))
  · unfold deleteObjects
    exact dk_bind (ent_dmo _) (fun _ => dk_modify (fun σ => rfl))
  apply dke_ite
  · refine dke_bind (dke_liftE (dk_bind (dk_unless _ (ent_dmo _)) (fun _ => ent_setCap _ _))) (fun _ => ?_)
    unfold archPostResetUntyped; exact dke_liftE (dk_pure _)
  · refine dke_bind (dke_mapMEx (fun i => ?_) _) (fun _ => ?_)
    · exact dke_bind (dke_liftE (ent_dmo _)) (fun _ => dke_bind (dke_liftE (ent_setCap _ _)) (fun _ => ent_pp))
    · unfold archPostResetUntyped; exact dke_liftE (dk_pure _)

theorem fke_nall {β ε α : Type} {f : State Unit → β} {m : NonDetE (State Unit) ε α} (h : FKE f m) (s : State Unit) :
    NAll m.run s (fun x => f x.2 = f s) := fun x hx => h s x hx

/-- **The reset of a used cap keeps every object's type but its region's**,
which it deletes (`delete_objects`), on every outcome. -/
theorem reset_khT {sl : CslotPtr} {σ : State Unit} {dev : Bool} {pu : ObjRef} {sz fi : Nat}
    (hg : getCap (Z := Unit) sl σ = ({(.untypedCap dev pu sz fi, σ)}, False)) (hfi : fi ≠ 0) :
    NAll (resetUntypedCap (Z := Unit) sl).run σ (fun y => khT y.2 = khT (detype (regionSet pu sz) σ)) := by
  unfold resetUntypedCap
  apply nallE_bind
  refine nall_det (run_liftE hg) ?_
  dsimp only
  simp only [NonDetE.returnOk, ndE_pure_bind, Fl4Spec.bitsOf, Fl4Spec.objRefOf, Fl4Spec.freeIndexOf,
    Fl4Spec.isDeviceUntypedCap, hfi, ↓reduceIte]
  apply nallE_bind
  apply nall_liftE
  intro y hy
  have hD : khT y.2 = khT (detype (regionSet pu sz) σ) := by
    unfold deleteObjects at hy
    obtain ⟨z, hz1, hz⟩ := hy
    rw [Set.mem_singleton_iff.1 hz]
    have e := kt_dmo _ σ z hz1
    funext o
    have e2 := congrFun e o
    simp only [khT, detype] at e2 ⊢
    split_ifs <;> simp_all
  dsimp only
  refine NAll.mono (P := fun x => khT x.2 = khT y.2) ?_ (fun x hx => hx.trans hD)
  refine fke_nall ?_ y.2
  apply dke_ite
  · refine dke_bind (dke_liftE (dk_bind (dk_unless _ (kt_dmo _)) (fun _ => kt_setCap _ _))) (fun _ => ?_)
    unfold archPostResetUntyped; exact dke_liftE (dk_pure _)
  · refine dke_bind (dke_mapMEx (fun i => ?_) _) (fun _ => ?_)
    · exact dke_bind (dke_liftE (kt_dmo _)) (fun _ => dke_bind (dke_liftE (kt_setCap _ _)) (fun _ => kt_pp))
    · unfold archPostResetUntyped; exact dke_liftE (dk_pure _)

end SpecKeep

section Comp
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

theorem aType_arch {ko : Fl4Spec.KernelObject} {ao : Fl4Spec.ArchKernelObj}
    (h : Fl4Spec.aType ko = Fl4Spec.aType (.archObj ao)) : ∃ ao', ko = .archObj ao' := by
  cases ko <;> simp only [Fl4Spec.aType] at h <;> first | exact ⟨_, rfl⟩ | (split_ifs at h <;> cases h) | cases h

/-- **`UtRetPostJ` with a done reset**: the body's outcome after the reset. -/
theorem utRetPostJ_of_reset {σ σ1 σ2 : Fl4Spec.State Unit} {blk call don : Bool} {sl : Fl4Spec.CslotPtr}
    {base rb : Fl4Spec.Word} {t : Fl4Spec.ApiObjectType} {us : Nat} {slots : List Fl4Spec.CslotPtr} {dev : Bool}
    {res : core.result.Result Unit error.Exc × S × A}
    (hst1 : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (hr : ((.ok (), σ2) : Except Unit Unit × Fl4Spec.State Unit) ∈ ((Fl4Spec.resetUntypedCap (Z := Unit) sl).run σ1).1)
    (h : UtBodyPost (L := L) arI AR σ2 (.retype sl false base rb t us slots dev) res) :
    UtRetPostJ (L := L) arI AR σ blk call don (.retype sl true base rb t us slots dev) res := by
  obtain ⟨σ', hrun, hok, ⟨th', G', hrel⟩, hJ⟩ := h
  have hy := invoke_reset_ok Fl4Spec.fl4ObjBitsApi sl base rb t us slots dev hr (mem_of_run hrun)
  refine ⟨σ1, hst1, (.ok [], σ'), mem_bindE_ok hy (mem_returnOk []), ⟨th', G', Or.inl ⟨hok, rfl⟩, hrel⟩, ?_⟩
  rw [if_neg (by rw [hok]; simp)]
  exact hJ

variable (arI) in
/-- **A retype body for one invocation's arguments** (UtEpRet's
`JAtZ.utEpBodyJ` shape): from any `JAtZ` state, entered, the source a CNode
slot's RAM untyped cap of free index `fi = fiv`, the arguments' `RetCtx` there
(any `reset` flag), `BufObjHyp`, `ArchFitHyp` and the kept references to a
range of the cap's free part, FL4's retype without a reset ends in
`UtBodyPost`. -/
def UtBodyHyp (AR : A → Fl4Spec.Cr3 → Prop) (pp : U64) (idx : List Bool) (p sb nt us dest off win : U64)
    (t : Fl4Spec.ApiObjectType) (r : Nat) (fiv : U64) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit), JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ → [VxE Z] → Entered σ →
    ∀ rs, Z.th pp = some (.cnode rs) → idx.length = rs →
    ∀ fi : U64, capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi false) → Z.c = 0#u64 →
    ∀ reset : Bool, RetCtx (L := L) Z.th s σ (pp.bv, idx) sb fi false nt us dest off win t r reset fiv → fiv = fi →
    BufObjHyp Z.B σ → ArchFitHyp H σ →
    (∀ lo hi : Nat, p.val + fi.val ≤ lo → hi ≤ p.val + 2 ^ sb.val →
      KeptRefsP3 (L := L) H (RegionD H lo hi) s ∧ DbgTimerKept (L := L) H (RegionD H lo hi) Cs s) →
    UtFreeZ σ (p.val + fi.val) (p.val + 2 ^ sb.val) → UtNodesAt (L.ksb s) p sb →
    untyped.retype st arI s ar (cslotAddr (pp.bv, idx)) false
        ⟨Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)⟩ nt us dest off win false ⦃ res =>
      UtBodyPost (L := L) arI AR σ (.retype (pp.bv, idx) false p.bv
        (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val) false) res ⦄

/-- `JAtZ.utEpBodyJ` as `UtBodyHyp` (endpoints, notifications, replies, VSpace
tables, frames). -/
theorem utEp_bodyHyp {pp : U64} {idx : List Bool} {p sb nt us dest off win : U64} {t : Fl4Spec.ApiObjectType}
    {r : Nat} {fiv : U64}
    (hnt : nt.val = 2 ∨ nt.val = 3 ∨ nt.val = 6 ∨ (nt.val = 7 ∨ nt.val = 12 ∨ nt.val = 13 ∨ nt.val = 9 ∨ nt.val = 10 ∨ nt.val = 11)) :
    UtBodyHyp (L := L) arI AR pp idx p sb nt us dest off win t r fiv :=
  fun _ _ _ _ _ _ _ _ _ J _ hni _ hpp hidx _ hcap hc0 _ hctx hfiv hBO hAF hRU hZ0 hKN =>
    J.utEpBodyJ hni hpp hidx hcap hnt hc0 hctx hfiv hBO hAF hRU hZ0 hKN

/-- UtScRet's `JAtZ.utScBodyJ` as `UtBodyHyp` (SCs). -/
theorem utSc_bodyHyp {pp : U64} {idx : List Bool} {p sb nt us dest off win : U64} {t : Fl4Spec.ApiObjectType}
    {r : Nat} {fiv : U64} (hnt : nt.val = 5) :
    UtBodyHyp (L := L) arI AR pp idx p sb nt us dest off win t r fiv :=
  fun _ _ _ _ _ _ _ _ _ J _ hni _ hpp hidx _ hcap hc0 _ hctx hfiv hBO hAF hRU _ _ =>
    J.utScBodyJ hni hpp hidx hcap hnt hc0 hctx hfiv hBO hAF hRU

/-- UtUtRet's `JAtZ.utUtBodyJ` as `UtBodyHyp` (untypeds). -/
theorem utUt_bodyHyp {pp : U64} {idx : List Bool} {p sb nt us dest off win : U64} {t : Fl4Spec.ApiObjectType}
    {r : Nat} {fiv : U64} (hnt : nt.val = 0) :
    UtBodyHyp (L := L) arI AR pp idx p sb nt us dest off win t r fiv :=
  fun _ _ _ _ _ _ _ _ _ J _ hni _ hpp hidx _ hcap hc0 _ hctx hfiv hBO hAF hRU _ _ =>
    J.utUtBodyJ hni hpp hidx hcap hnt hc0 hctx hfiv hBO hAF hRU

/-- UtPmRet's `JAtZ.utPmBodyJ` as `UtBodyHyp` (PML4s). -/
theorem utPm_bodyHyp {pp : U64} {idx : List Bool} {p sb nt us dest off win : U64} {t : Fl4Spec.ApiObjectType}
    {r : Nat} {fiv : U64} (hnt : nt.val = 8) :
    UtBodyHyp (L := L) arI AR pp idx p sb nt us dest off win t r fiv :=
  fun _ _ _ _ _ _ _ _ _ J _ hni _ hpp hidx _ hcap hc0 _ hctx hfiv hBO hAF hRU _ _ =>
    J.utPmBodyJ hni hpp hidx hcap hnt hc0 hctx hfiv hBO hAF hRU

/-- UtTcbRet's `JAtZ.utTcbBodyJ` as `UtBodyHyp` (TCBs). -/
theorem utTcb_bodyHyp {pp : U64} {idx : List Bool} {p sb nt us dest off win : U64} {t : Fl4Spec.ApiObjectType}
    {r : Nat} {fiv : U64} (hnt : nt.val = 1) :
    UtBodyHyp (L := L) arI AR pp idx p sb nt us dest off win t r fiv :=
  fun _ _ _ _ _ _ _ _ _ J _ hni _ hpp hidx _ hcap hc0 _ hctx hfiv hBO hAF hRU _ _ =>
    J.utTcbBodyJ hni hpp hidx hcap hnt hc0 hctx hfiv hBO hAF hRU

/-- UtCnRet's `JAtZ.utCnBodyJ` as `UtBodyHyp` (CNodes). -/
theorem utCn_bodyHyp {pp : U64} {idx : List Bool} {p sb nt us dest off win : U64} {t : Fl4Spec.ApiObjectType}
    {r : Nat} {fiv : U64} (hnt : nt.val = 4) :
    UtBodyHyp (L := L) arI AR pp idx p sb nt us dest off win t r fiv :=
  fun _ _ _ _ _ _ _ _ _ J _ hni _ hpp hidx _ hcap hc0 _ hctx hfiv hBO hAF hRU _ _ =>
    J.utCnBodyJ hni hpp hidx hcap hnt hc0 hctx hfiv hBO hAF hRU

end Comp

end

end Fl4Proofs.P3
