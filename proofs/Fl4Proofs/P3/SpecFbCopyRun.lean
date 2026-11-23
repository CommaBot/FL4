/-
P3 (issue #16, FL4 #71), VSpace FrameBatch (KENTRY-PLAN fb3l), spec side:
**the outcomes of a COPY_MAP entry** (`fbEntry` at `b.op = .copyMap`), built
from its steps' outcomes (SpecFbDelRun's `fbr_*`): the destination's lookup
error, a non-empty destination, the source's lookup error, a source cap that
is no frame, a derive error, and after the insert the map's success or its
error (the fresh copy deleted, the error re-thrown).
-/
import Fl4Proofs.P3.SpecFbDelRun
open Classical

namespace Fl4Proofs.P3
open Fl4Spec

noncomputable section

section
variable {ε ε' α : Type}

theorem fbr_unless_ok {P : Prop} [Decidable P] (hP : P) (m : NonDetE (State Unit) ε Unit) (s : State Unit) :
    (.ok (), s) ∈ ((NonDetE.unlessE P m).run s).1 := by
  unfold NonDetE.unlessE; rw [if_pos hP]; exact Set.mem_singleton _

theorem fbr_unless_err {P : Prop} [Decidable P] (hP : ¬ P) {m : NonDetE (State Unit) ε Unit} {s : State Unit}
    {y : Except ε Unit × State Unit} (h : y ∈ (m.run s).1) : y ∈ ((NonDetE.unlessE P m).run s).1 := by
  unfold NonDetE.unlessE; rw [if_neg hP]; exact h

theorem fbr_throw (e : ε) (s : State Unit) :
    (.error e, s) ∈ ((NonDetE.throwError e : NonDetE (State Unit) ε α).run s).1 := Set.mem_singleton _

theorem fbr_handle_err {m : NonDetE (State Unit) ε α} {h : ε → NonDetE (State Unit) ε' α} {s t : State Unit}
    {e : ε} {y : Except ε' α × State Unit} (h1 : (.error e, t) ∈ (m.run s).1) (h2 : y ∈ ((h e).run t).1) :
    y ∈ ((NonDetE.handleE m h).run s).1 := by
  unfold NonDetE.handleE; rw [ExceptT.run_mk]; exact ⟨_, h1, h2⟩

theorem fbr_handle_ok {m : NonDetE (State Unit) ε α} {h : ε → NonDetE (State Unit) ε' α} {s t : State Unit}
    {a : α} (h1 : (.ok a, t) ∈ (m.run s).1) : (.ok a, t) ∈ ((NonDetE.handleE m h).run s).1 := by
  unfold NonDetE.handleE; rw [ExceptT.run_mk]; exact ⟨_, h1, Set.mem_singleton _⟩

theorem fbr_catch_ok {m : NonDetE (State Unit) ε α} {h : ε → NonDet (State Unit) α} {s t : State Unit} {a : α}
    (h1 : (.ok a, t) ∈ (m.run s).1) : (a, t) ∈ (NonDetE.catch m h s).1 := by
  unfold NonDetE.catch; exact ⟨_, h1, Set.mem_singleton _⟩

end

variable {b : Fl4FrameBatchInvocation} {w : Data × Data × Data} {τ : State Unit}

/-- The destination's lookup fails. -/
theorem fbEntry_copy_destErr (hop : b.op = .copyMap) {e : SyscallError}
    (h : (.error e, τ) ∈ ((lookupTargetSlot (Z := Unit) b.destCnode (dataToCptr w.2.1) b.depth).run τ).1) :
    (.error (msgFromSyscallError e).1, τ) ∈ ((fbEntry (Z := Unit) b w).run τ).1 := by
  unfold fbEntry; rw [hop]
  exact fbr_bind_err (fbr_code_err h)

/-- The destination is not empty. -/
theorem fbEntry_copy_full (hop : b.op = .copyMap) {dsl : CslotPtr}
    (hd : (.ok dsl, τ) ∈ ((lookupTargetSlot (Z := Unit) b.destCnode (dataToCptr w.2.1) b.depth).run τ).1)
    (he : (.error .deleteFirst, τ) ∈ ((ensureEmpty (Z := Unit) dsl).run τ).1) :
    (.error (msgFromSyscallError .deleteFirst).1, τ) ∈ ((fbEntry (Z := Unit) b w).run τ).1 := by
  unfold fbEntry; rw [hop]
  exact fbr_bind_ok (fbr_code_ok hd) (fbr_bind_err (fbr_code_err he))

/-- The source's lookup fails. -/
theorem fbEntry_copy_srcErr (hop : b.op = .copyMap) {dsl : CslotPtr} {e : SyscallError}
    (hd : (.ok dsl, τ) ∈ ((lookupTargetSlot (Z := Unit) b.destCnode (dataToCptr w.2.1) b.depth).run τ).1)
    (he : (.ok (), τ) ∈ ((ensureEmpty (Z := Unit) dsl).run τ).1)
    (h : (.error e, τ) ∈ ((lookupSourceSlot (Z := Unit) b.cnode (dataToCptr w.1) b.depth).run τ).1) :
    (.error (msgFromSyscallError e).1, τ) ∈ ((fbEntry (Z := Unit) b w).run τ).1 := by
  unfold fbEntry; rw [hop]
  exact fbr_bind_ok (fbr_code_ok hd) (fbr_bind_ok (fbr_code_ok he) (fbr_bind_err (fbr_code_err h)))

/-- The source's cap is no frame. -/
theorem fbEntry_copy_notPage (hop : b.op = .copyMap) {dsl ssl : CslotPtr} {sc : Cap}
    (hd : (.ok dsl, τ) ∈ ((lookupTargetSlot (Z := Unit) b.destCnode (dataToCptr w.2.1) b.depth).run τ).1)
    (he : (.ok (), τ) ∈ ((ensureEmpty (Z := Unit) dsl).run τ).1)
    (hs : (.ok ssl, τ) ∈ ((lookupSourceSlot (Z := Unit) b.cnode (dataToCptr w.1) b.depth).run τ).1)
    (hg : (sc, τ) ∈ (getCap (Z := Unit) ssl τ).1) (hp : ¬ isPageCap sc = true) :
    (.error (msgFromSyscallError (.invalidCapability 0)).1, τ) ∈ ((fbEntry (Z := Unit) b w).run τ).1 := by
  unfold fbEntry; rw [hop]
  exact fbr_bind_ok (fbr_code_ok hd) (fbr_bind_ok (fbr_code_ok he) (fbr_bind_ok (fbr_code_ok hs)
    (fbr_bind_ok (fbr_liftE hg) (fbr_bind_err (fbr_code_err (fbr_unless_err hp (fbr_throw _ τ)))))))

/-- The derive fails. -/
theorem fbEntry_copy_deriveErr (hop : b.op = .copyMap) {dsl ssl : CslotPtr} {sc : Cap} {e : SyscallError}
    (hd : (.ok dsl, τ) ∈ ((lookupTargetSlot (Z := Unit) b.destCnode (dataToCptr w.2.1) b.depth).run τ).1)
    (he : (.ok (), τ) ∈ ((ensureEmpty (Z := Unit) dsl).run τ).1)
    (hs : (.ok ssl, τ) ∈ ((lookupSourceSlot (Z := Unit) b.cnode (dataToCptr w.1) b.depth).run τ).1)
    (hg : (sc, τ) ∈ (getCap (Z := Unit) ssl τ).1) (hp : isPageCap sc = true)
    (hv : (.error e, τ) ∈ ((deriveCap (Z := Unit) ssl (maskCap (dataToRights b.capRights) sc)).run τ).1) :
    (.error (msgFromSyscallError e).1, τ) ∈ ((fbEntry (Z := Unit) b w).run τ).1 := by
  unfold fbEntry; rw [hop]
  exact fbr_bind_ok (fbr_code_ok hd) (fbr_bind_ok (fbr_code_ok he) (fbr_bind_ok (fbr_code_ok hs)
    (fbr_bind_ok (fbr_liftE hg) (fbr_bind_ok (fbr_code_ok (fbr_unless_ok hp _ τ))
      (fbr_bind_err (fbr_code_err hv))))))

/-- The map succeeds after the insert. -/
theorem fbEntry_copy_ok (hop : b.op = .copyMap) {dsl ssl : CslotPtr} {sc nc : Cap} {τ1 τ2 : State Unit}
    (hd : (.ok dsl, τ) ∈ ((lookupTargetSlot (Z := Unit) b.destCnode (dataToCptr w.2.1) b.depth).run τ).1)
    (he : (.ok (), τ) ∈ ((ensureEmpty (Z := Unit) dsl).run τ).1)
    (hs : (.ok ssl, τ) ∈ ((lookupSourceSlot (Z := Unit) b.cnode (dataToCptr w.1) b.depth).run τ).1)
    (hg : (sc, τ) ∈ (getCap (Z := Unit) ssl τ).1) (hp : isPageCap sc = true)
    (hv : (.ok nc, τ) ∈ ((deriveCap (Z := Unit) ssl (maskCap (dataToRights b.capRights) sc)).run τ).1)
    (hi : ((), τ1) ∈ (capInsert (Z := Unit) nc ssl dsl τ).1)
    (hm : (.ok (), τ2) ∈ ((fbMap (Z := Unit) b dsl w.2.2).run τ1).1) :
    (.ok false, τ2) ∈ ((fbEntry (Z := Unit) b w).run τ).1 := by
  unfold fbEntry; rw [hop]
  exact fbr_bind_ok (fbr_code_ok hd) (fbr_bind_ok (fbr_code_ok he) (fbr_bind_ok (fbr_code_ok hs)
    (fbr_bind_ok (fbr_liftE hg) (fbr_bind_ok (fbr_code_ok (fbr_unless_ok hp _ τ))
      (fbr_bind_ok (fbr_code_ok hv) (fbr_bind_ok (fbr_liftE hi)
        (fbr_bind_ok (fbr_handle_ok (fbr_code_ok hm)) (fbr_ret false))))))))

/-- The map fails after the insert: the copy deleted, the map's error. -/
theorem fbEntry_copy_mapErr (hop : b.op = .copyMap) {dsl ssl : CslotPtr} {sc nc : Cap} {τ1 τ2 τ3 : State Unit}
    {e : SyscallError}
    (hd : (.ok dsl, τ) ∈ ((lookupTargetSlot (Z := Unit) b.destCnode (dataToCptr w.2.1) b.depth).run τ).1)
    (he : (.ok (), τ) ∈ ((ensureEmpty (Z := Unit) dsl).run τ).1)
    (hs : (.ok ssl, τ) ∈ ((lookupSourceSlot (Z := Unit) b.cnode (dataToCptr w.1) b.depth).run τ).1)
    (hg : (sc, τ) ∈ (getCap (Z := Unit) ssl τ).1) (hp : isPageCap sc = true)
    (hv : (.ok nc, τ) ∈ ((deriveCap (Z := Unit) ssl (maskCap (dataToRights b.capRights) sc)).run τ).1)
    (hi : ((), τ1) ∈ (capInsert (Z := Unit) nc ssl dsl τ).1)
    (hm : (.error e, τ2) ∈ ((fbMap (Z := Unit) b dsl w.2.2).run τ1).1)
    (hdl : (.ok (), τ3) ∈ ((capDelete (Z := Unit) dsl).run τ2).1) :
    (.error (msgFromSyscallError e).1, τ3) ∈ ((fbEntry (Z := Unit) b w).run τ).1 := by
  unfold fbEntry; rw [hop]
  exact fbr_bind_ok (fbr_code_ok hd) (fbr_bind_ok (fbr_code_ok he) (fbr_bind_ok (fbr_code_ok hs)
    (fbr_bind_ok (fbr_liftE hg) (fbr_bind_ok (fbr_code_ok (fbr_unless_ok hp _ τ))
      (fbr_bind_ok (fbr_code_ok hv) (fbr_bind_ok (fbr_liftE hi)
        (fbr_bind_err (fbr_handle_err (fbr_code_err hm)
          (fbr_bind_ok (fbr_liftE (fbr_catch_ok hdl)) (fbr_throw _ τ3)))))))))

end

end Fl4Proofs.P3
