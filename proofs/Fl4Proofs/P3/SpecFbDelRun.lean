/-
P3 (issue #16, FL4 #71), VSpace FrameBatch (KENTRY-PLAN fb3l), spec side:
**the outcomes of a DELETE entry** (`fbEntry` at `b.op = .delete`), built
from its steps' outcomes: the target slot's lookup error, a null slot, a cap
neither null nor a frame, a frame deleted with or without the deferred
unmap.
-/
import Fl4Proofs.P3.XTopJointFbDefs
open Classical

namespace Fl4Proofs.P3
open Fl4Spec

noncomputable section

section
variable {ε α β : Type}

theorem fbr_bind_ok {m : NonDetE (State Unit) ε α} {f : α → NonDetE (State Unit) ε β} {s t : State Unit} {a : α}
    {y : Except ε β × State Unit} (h1 : (.ok a, t) ∈ (m.run s).1) (h2 : y ∈ ((f a).run t).1) :
    y ∈ ((m >>= f).run s).1 := by
  rw [ExceptT.run_bind]; exact ⟨_, h1, h2⟩

theorem fbr_bind_err {m : NonDetE (State Unit) ε α} {f : α → NonDetE (State Unit) ε β} {s t : State Unit} {e : ε}
    (h1 : (.error e, t) ∈ (m.run s).1) : (.error e, t) ∈ ((m >>= f).run s).1 := by
  rw [ExceptT.run_bind]; exact ⟨_, h1, Set.mem_singleton _⟩

theorem fbr_liftE {m : NonDet (State Unit) α} {s t : State Unit} {a : α} (h : (a, t) ∈ (m s).1) :
    (.ok a, t) ∈ ((NonDetE.liftE (ε := ε) m).run s).1 := by
  unfold NonDetE.liftE; rw [ExceptT.run_lift]; exact ⟨_, h, Set.mem_singleton _⟩

theorem fbr_ret {s : State Unit} (a : α) : (.ok a, s) ∈ ((NonDetE.returnOk (ε := ε) a : NonDetE (State Unit) ε α).run s).1 :=
  Set.mem_singleton _

theorem fbr_code_ok {m : SEMonad Unit α} {s t : State Unit} {a : α} (h : (.ok a, t) ∈ (m.run s).1) :
    (.ok a, t) ∈ ((fbCode (Z := Unit) m).run s).1 := by
  unfold fbCode NonDetE.handleE; rw [ExceptT.run_mk]; exact ⟨_, h, Set.mem_singleton _⟩

theorem fbr_code_err {m : SEMonad Unit α} {s t : State Unit} {e : SyscallError} (h : (.error e, t) ∈ (m.run s).1) :
    (.error (msgFromSyscallError e).1, t) ∈ ((fbCode (Z := Unit) m).run s).1 := by
  unfold fbCode NonDetE.handleE; rw [ExceptT.run_mk]; exact ⟨_, h, Set.mem_singleton _⟩

theorem fbr_delete_ok {sl : CslotPtr} {s t : State Unit} (h : (.ok (), t) ∈ ((capDelete (Z := Unit) sl).run s).1) :
    (.ok (), t) ∈ ((fbDelete (Z := Unit) sl).run s).1 := by
  unfold fbDelete NonDetE.handleE; rw [ExceptT.run_mk]; exact ⟨_, h, Set.mem_singleton _⟩

end

variable {b : Fl4FrameBatchInvocation} {w : Data × Data × Data} {τ : State Unit}

/-- The target slot's lookup fails. -/
theorem fbEntry_del_lookupErr (hop : b.op = .delete) {e : SyscallError}
    (h : (.error e, τ) ∈ ((lookupTargetSlot (Z := Unit) b.cnode (dataToCptr w.1) b.depth).run τ).1) :
    (.error (msgFromSyscallError e).1, τ) ∈ ((fbEntry (Z := Unit) b w).run τ).1 := by
  unfold fbEntry; rw [hop]
  exact fbr_bind_err (fbr_code_err h)

/-- A null target slot. -/
theorem fbEntry_del_null (hop : b.op = .delete) {sl : CslotPtr}
    (h : (.ok sl, τ) ∈ ((lookupTargetSlot (Z := Unit) b.cnode (dataToCptr w.1) b.depth).run τ).1)
    (hg : (.nullCap, τ) ∈ (getCap (Z := Unit) sl τ).1) :
    (.ok false, τ) ∈ ((fbEntry (Z := Unit) b w).run τ).1 := by
  unfold fbEntry; rw [hop]
  exact fbr_bind_ok (fbr_code_ok h) (fbr_bind_ok (fbr_liftE hg) (fbr_ret _))

/-- A cap neither null nor a frame. -/
theorem fbEntry_del_other (hop : b.op = .delete) {sl : CslotPtr} {c : Cap}
    (h : (.ok sl, τ) ∈ ((lookupTargetSlot (Z := Unit) b.cnode (dataToCptr w.1) b.depth).run τ).1)
    (hg : (c, τ) ∈ (getCap (Z := Unit) sl τ).1) (hn : c ≠ .nullCap)
    (hf : ∀ dev p R mt sz m, c ≠ .archObjectCap (.pageCap dev p R mt sz m)) :
    (.error (msgFromSyscallError .illegalOperation).1, τ) ∈ ((fbEntry (Z := Unit) b w).run τ).1 := by
  unfold fbEntry; rw [hop]
  refine fbr_bind_ok (fbr_code_ok h) (fbr_bind_ok (fbr_liftE hg) ?_)
  cases c
  all_goals first
    | exact absurd rfl hn
    | exact Set.mem_singleton _
    | (rename_i ac
       cases ac <;> first | exact Set.mem_singleton _ | exact absurd rfl (hf _ _ _ _ _ _))

/-- A frame deleted without the deferred unmap. -/
theorem fbEntry_del_frame (hop : b.op = .delete) {sl : CslotPtr} {dev : Bool} {p : ObjRef} {R : CapRights}
    {mt : VMMapType} {sz : VMPageSize} {m : Option (Asid × VSpaceRef)} {τ1 : State Unit}
    (h : (.ok sl, τ) ∈ ((lookupTargetSlot (Z := Unit) b.cnode (dataToCptr w.1) b.depth).run τ).1)
    (hg : (.archObjectCap (.pageCap dev p R mt sz m), τ) ∈ (getCap (Z := Unit) sl τ).1)
    (hnd : ∀ asid' vaddr, m = some (asid', vaddr) →
      ¬ (b.deferDelete ∧ mt = .vmVSpaceMap ∧ dev = false ∧ asid' = b.asid))
    (hd : (.ok (), τ1) ∈ ((capDelete (Z := Unit) sl).run τ).1) :
    (.ok false, τ1) ∈ ((fbEntry (Z := Unit) b w).run τ).1 := by
  unfold fbEntry; rw [hop]
  refine fbr_bind_ok (fbr_code_ok h) (fbr_bind_ok (fbr_liftE hg) ?_)
  refine fbr_bind_ok (a := false) (t := τ) ?_ (fbr_bind_ok (fbr_delete_ok hd) (fbr_ret _))
  rcases m with _ | ⟨a', v⟩
  · exact fbr_ret _
  · dsimp only
    rw [if_neg (hnd a' v rfl)]; exact fbr_ret _

/-- A frame deleted after the deferred unmap. -/
theorem fbEntry_del_frameD (hop : b.op = .delete) {sl : CslotPtr} {dev : Bool} {p : ObjRef} {R : CapRights}
    {mt : VMMapType} {sz : VMPageSize} {asid' vaddr : Data} {τu τs τ1 : State Unit} {r : Bool}
    (h : (.ok sl, τ) ∈ ((lookupTargetSlot (Z := Unit) b.cnode (dataToCptr w.1) b.depth).run τ).1)
    (hg : (.archObjectCap (.pageCap dev p R mt sz (some (asid', vaddr))), τ) ∈ (getCap (Z := Unit) sl τ).1)
    (hdf : b.deferDelete ∧ mt = .vmVSpaceMap ∧ dev = false ∧ asid' = b.asid)
    (hu : (r, τu) ∈ (unmapPageUnflushed (Z := Unit) sz b.vspace vaddr p τ).1)
    (hs : ((), τs) ∈ (setCap (Z := Unit) (.archObjectCap (.pageCap dev p R .vmNoMap sz none)) sl τu).1)
    (hd : (.ok (), τ1) ∈ ((capDelete (Z := Unit) sl).run τs).1) :
    (.ok r, τ1) ∈ ((fbEntry (Z := Unit) b w).run τ).1 := by
  unfold fbEntry; rw [hop]
  refine fbr_bind_ok (fbr_code_ok h) (fbr_bind_ok (fbr_liftE hg) ?_)
  dsimp only
  rw [if_pos hdf]
  refine fbr_bind_ok (fbr_liftE ⟨_, hu, _, hs, Set.mem_singleton _⟩) (fbr_bind_ok (fbr_delete_ok hd) (fbr_ret _))

end

end Fl4Proofs.P3
