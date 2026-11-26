/-
P3 against the virtualization extension (line virt, gen 2; proofs/VIRT-PLAN.md §10 R7): **the decode posts
against the extended dispatcher**, and the label-88 route posted through them.

FL4 source: `crates/fl4-core/src/syscall.rs` (`decode_invocation`), `tcb.rs:404-430` (TCBSetEPTRoot).
Spec: `Fl4Spec/Ext/VirtDispatch` (`fl4DecodeInvocationV`, `fl4PerformInvocationV`), which extends l4v
`Syscall_A.handle_invocation`'s decode / perform (ported as `fl4DecodeInvocation` / `fl4PerformInvocation`).

* `TopPostV` / `DecOKV`: DecodeTop's `TopPost` / `DecOK` with the extended decoder (`specDecV`) and the
  extended perform (`fl4PerformInvocationV onCore`): FL4 returned the extended spec's error with the store
  unchanged, or the extended spec decodes, restarts the caller and has a related outcome of the extended
  invocation.
* **Reuse of the ported posts** (VIRT-PLAN §10, route A): `TopPost.toV` — a ported `TopPost` gives the extended
  one on `liftME .base` of the ported decode when no decoded invocation is one of the four the extension
  substitutes (`PerformSubst`); `TopPost.toV_err` — its error disjunct transfers unconditionally;
  `DecOK.toV` / `DecOK.toV_err` — at the dispatcher, off `VirtRoute` (VirtP3x's `fl4DecodeInvocationV_base`).
* **Label 88** (route B, from `VirtSetEptDec`): `decOKV_thread88` — FL4's dispatcher on a thread cap at
  `TCBSetEPTRoot` (second phase) satisfies `DecOKV` whenever the first extra cap is not a mapped level-0 EPT
  cap; `decOKV_thread88_noVirt` — in particular whenever the first spec extra cap is not a virtualization cap
  (`IsVirtCap`, so on every `NoVirtCaps` state): there the extended spec covers every label-88 invocation.

Premises (named hypotheses): `hstall` [J] (as `tcb_decode_refines`: the target's stall is a no-op), `hct`
(`cur_thread` reads), `hx0` / `hex` (`ExtraSRel`), `hl` (spec label 88), and for the transfers `hns` (the
decoded invocation is not substituted) and `hv` (`¬ VirtRoute`). No [P], no [W]. New file only.
-/
import Fl4Proofs.P3.VirtSetEptDec
import Fl4Proofs.P3.DecodeTop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`TopPost` against the extended kernel** (module docstring). -/
def TopPostV (onCore : Fl4Spec.ObjRef → Bool) (σ : Fl4Spec.State Unit) (blk call don : Bool)
    (m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4InvocationV)
    (s : S) (res : core.result.Result Unit error.Exc × S × A) : Prop :=
  (∃ e, res.1 = .Err e ∧ res.2.1 = s ∧ ∃ e', m.run σ = ({(.error e', σ)}, False) ∧ ErrRel e e') ∨
  (∃ inv, DecOut m σ inv ∧ ∃ σ1,
    Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
    ∃ y ∈ ((Fl4Spec.fl4PerformInvocationV (Z := Unit) onCore blk call don inv).run σ1).1, ∃ th' G',
      ((res.1 = .Ok () ∧ ∃ rr, y.1 = .ok rr) ∨ (res.1 = .Err .Preempted ∧ y.1 = .error ())) ∧
      Placed th' ∧ CRel th' (L.mem res.2.1) y.2 G' ∧ FinInv th' (L.mem res.2.1) y.2 G')

/-- **`DecOK` against the extended kernel.** -/
abbrev DecOKV (onCore : Fl4Spec.ObjRef → Bool) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (lbl length slot : U64)
    (c : capability.Cap) (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) : Prop :=
  syscall.decode_invocation st arI s ar lbl length slot c blk call don fp buf extra ⦃ res =>
    TopPostV (L := L) onCore σ blk call don (specDecV fp slbl args ci sl c excaps buffer) s res ⦄

/-- The error disjunct of a ported `TopPost` is the extended one's on `liftME .base`. -/
theorem TopPost.toV_err (onCore : Fl4Spec.ObjRef → Bool) {σ : Fl4Spec.State Unit} {blk call don : Bool}
    {m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation} {s : S} {res : core.result.Result Unit error.Exc × S × A}
    (h : ∃ e, res.1 = .Err e ∧ res.2.1 = s ∧ ∃ e', m.run σ = ({(.error e', σ)}, False) ∧ ErrRel e e') :
    TopPostV (L := L) onCore σ blk call don (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4InvocationV.base m) s res := by
  obtain ⟨e, h1, h2, e', h3, h4⟩ := h
  exact Or.inl ⟨e, h1, h2, e', run_liftME_err h3, h4⟩

/-- **A ported `TopPost` gives the extended one** when no decoded invocation is substituted by the
extension (module docstring). -/
theorem TopPost.toV (onCore : Fl4Spec.ObjRef → Bool) {σ : Fl4Spec.State Unit} {blk call don : Bool}
    {m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation} {s : S} {res : core.result.Result Unit error.Exc × S × A}
    (h : TopPost (L := L) σ blk call don m s res)
    (hns : ∀ inv, DecOut m σ inv → ¬ Fl4Spec.PerformSubst inv) :
    TopPostV (L := L) onCore σ blk call don (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4InvocationV.base m) s res := by
  rcases h with h | ⟨inv, hd, σ1, hs, y, hy, th', G', h5, h6, h7, h8⟩
  · exact TopPost.toV_err onCore h
  · refine Or.inr ⟨.base inv, DecOut.liftME hd, σ1, hs, y, ?_, th', G', h5, h6, h7, h8⟩
    rw [Fl4Spec.fl4PerformInvocationV_base onCore blk call don inv (hns inv hd)]
    exact hy

/-- **`DecOK` gives `DecOKV` off the virtualization routes** (module docstring). -/
theorem DecOK.toV (onCore : Fl4Spec.ObjRef → Bool) {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    {lbl length slot : U64} {c : capability.Cap} {blk call don fp : Bool} {buf : U64}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {slbl : Fl4Spec.Data} {args : List Fl4Spec.Data}
    {ci : Fl4Spec.CapRef} {sl : Fl4Spec.CslotPtr} {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    {buffer : Option Fl4Spec.ObjRef}
    (h : DecOK (L := L) arI s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer)
    (hv : ¬ Fl4Spec.VirtRoute fp slbl args (absCap c) excaps)
    (hns : ∀ inv, DecOut (specDec fp slbl args ci sl c excaps buffer) σ inv → ¬ Fl4Spec.PerformSubst inv) :
    DecOKV (L := L) arI onCore s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer := by
  unfold DecOKV specDecV
  rw [Fl4Spec.fl4DecodeInvocationV_base fp slbl args ci sl (absCap c) excaps buffer hv]
  exact WP.spec_mono h fun _ hr => hr.toV onCore hns

/-- `DecOK.toV` for the error outcomes only (no condition on the invocation). -/
theorem DecOK.toV_err (onCore : Fl4Spec.ObjRef → Bool) {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    {lbl length slot : U64} {c : capability.Cap} {blk call don fp : Bool} {buf : U64}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {slbl : Fl4Spec.Data} {args : List Fl4Spec.Data}
    {ci : Fl4Spec.CapRef} {sl : Fl4Spec.CslotPtr} {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    {buffer : Option Fl4Spec.ObjRef}
    (h : syscall.decode_invocation st arI s ar lbl length slot c blk call don fp buf extra ⦃ res =>
      ∃ e, res.1 = .Err e ∧ res.2.1 = s ∧ ∃ e',
        (specDec fp slbl args ci sl c excaps buffer).run σ = ({(.error e', σ)}, False) ∧ ErrRel e e' ⦄)
    (hv : ¬ Fl4Spec.VirtRoute fp slbl args (absCap c) excaps) :
    DecOKV (L := L) arI onCore s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer := by
  unfold DecOKV specDecV
  rw [Fl4Spec.fl4DecodeInvocationV_base fp slbl args ci sl (absCap c) excaps buffer hv]
  exact WP.spec_mono h fun _ hr => TopPost.toV_err onCore hr

/-- **Label 88 at the dispatcher, posted against the extended kernel** (module docstring). -/
theorem decOKV_thread88 (onCore : Fl4Spec.ObjRef → Bool) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (length slot : U64) (p : U64) (blk call don : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (th : TypedHeap) (x0 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (cps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraSRel th (L.mem s) x0 cps)
    (hbad : x0 = 0#u64 ∨ ¬ EptRootC (capV (L.mem s) x0))
    (slbl : Fl4Spec.Data) (hl : Fl4Spec.dataToNat slbl = Fl4Spec.fl4SetEptRootLabel) (args : List Fl4Spec.Data)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (buffer : Option Fl4Spec.ObjRef) :
    DecOKV (L := L) arI onCore s ar σ fl4_abi.label.TCBSetEPTRoot length slot (.Thread p) blk call don false buf
      extra slbl args ci sl cps buffer := by
  unfold DecOKV
  rw [decode_invocation_thread_eq arI s ar _ length slot p blk call don buf extra ct hct]
  obtain ⟨e, h1, e', h2, h3⟩ := setEptRoot_decode_err arI s ar σ p ⟨length, buf, call, slot, extra⟩ hstall th x0
    hx0 cps hex hbad slbl hl args ci sl buffer
  rw [h1, WP.spec_ok]
  exact Or.inl ⟨e, rfl, rfl, e', h2, h3⟩

/-- A mapped level-0 EPT cap is a virtualization cap of the spec. -/
theorem eptRootC_virt {c : capability.Cap} (h : EptRootC c) : Fl4Spec.IsVirtCap (absCap c) := by
  obtain ⟨q, asid, va, rfl⟩ := h
  first
    | trivial
    | simp [absCap, Fl4Spec.IsVirtCap]

/-- **Label 88 on a state without virtualization caps**: `DecOKV` holds whenever the first spec extra cap
is not a virtualization cap. -/
theorem decOKV_thread88_noVirt (onCore : Fl4Spec.ObjRef → Bool) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (length slot : U64) (p : U64) (blk call don : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (th : TypedHeap) (x0 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (cps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraSRel th (L.mem s) x0 cps)
    (hnv : ∀ x ∈ cps.head?, ¬ Fl4Spec.IsVirtCap x.1)
    (slbl : Fl4Spec.Data) (hl : Fl4Spec.dataToNat slbl = Fl4Spec.fl4SetEptRootLabel) (args : List Fl4Spec.Data)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (buffer : Option Fl4Spec.ObjRef) :
    DecOKV (L := L) arI onCore s ar σ fl4_abi.label.TCBSetEPTRoot length slot (.Thread p) blk call don false buf
      extra slbl args ci sl cps buffer := by
  have hbad : x0 = 0#u64 ∨ ¬ EptRootC (capV (L.mem s) x0) := by
    by_cases h0 : x0 = 0#u64
    · exact Or.inl h0
    · right
      intro hr
      rcases hex with ⟨h0', -⟩ | ⟨-, ps, rs, idxs, rest, -, -, -, rfl⟩
      · exact h0 h0'
      · exact hnv _ rfl (eptRootC_virt hr)
  exact decOKV_thread88 arI onCore s ar σ length slot p blk call don buf extra ct hct hstall th x0 hx0 cps hex
    hbad slbl hl args ci sl buffer

end

end

end Fl4Proofs.P3
