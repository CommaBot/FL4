/-
P3x for virtualization, spec side (line virt, gen 5; proofs/VIRT-PLAN.md §10 "Remaining (R7)" (e)):
**`InvOK` of the decoded invocations, from the ported decoder**, except for the TCB decode — which shrinks the
second half of VirtOffNv's `OffRoute3` [S].

* `okd_dataToObjType`: `data_to_obj_type` returns the VCPU type only for the number 14 (l4v `Decode_A`, X64
  `arch_data_to_obj_type` 7, shifted by the 7 API types).
* `okd_decodeUntypedVcpu`: an ok retype of FL4's untyped decoder (`decodeUntypedInvocationWith`) to the VCPU type
  has the retype label, ≥ 6 message words, an extra cap and type number 14 — i.e. it is on the VT-x gate
  `untypedVtxGate` when `virtKind = none`.
* **`okd_fl4Decode_invOK`**: every ok outcome of the ported dispatcher `fl4DecodeInvocation` is `InvOK`, given
  that the cap is not on the VT-x gate (`¬ Route3`'s untyped case), `virtKind = none`, and, for a thread cap, the
  TCB decode's outcomes (premise `htcb`).
* `OffRoute4` / `OffRouteS4`: VirtOffNv's `OffRoute3` / `OffRouteS3` with the `InvOK` half restricted to thread
  caps; `offRoute3_of4`, `offRouteS3_of4`.
* **`fl4CallKernelV_eqNR4`**: the extended kernel step is the ported one on an `NR` state, given the premises
  below.

Named premises:
* **`hvk : virtKind = .none` [S]** (route scope, as gen 2's `decOKV_untyped_vtxGate`): the platform has no VT-x
  backend. With a backend, the ported decoder retypes VCPUs and the extended perform initialises them
  (VIRT-PLAN R4), so the transport does not hold there.
* **`hoff4 : ∀ c, ev = .syscallEvent c → ∀ t, EntryPt σ t → OffRouteS4 c t` [S]**: at each decode point
  (1) `¬ Route3` (the three label / gate conditions), (2) for a thread cap, every decoded invocation is `InvOK`
  (`TcbCapsOK` of a `ThreadControlCaps`: the vih3 `OkV` carry through `fl4DecodeTcbInvocation`, open).

No [J]/[P]/[W]. New file only.
-/
import Fl4Proofs.P3.VirtOffNv
open Classical

namespace Fl4Proofs.P3.VirtInvOK
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvDom Fl4Proofs.P3.SInvL
  Fl4Proofs.P3.VirtR7b Fl4Proofs.P3.VirtR7e Fl4Proofs.P3.VirtR7eK Fl4Proofs.P3.VirtR7eK2 Fl4Proofs.P3.VirtOffNv

noncomputable section

set_option maxHeartbeats 1000000

section
variable {ε α β : Type} {σ : State Unit}

theorem okdAt_mono' {P Q : State Unit → α → Prop} {m : NonDetE (State Unit) ε α} (h : OkDAt σ Q m)
    (hq : ∀ s a, Q s a → P s a) : OkDAt σ P m := fun a s h' => hq s a (h a s h')

theorem okdAt_unlessE_bind {P : State Unit → β → Prop} (c : Prop) [Decidable c] (e : ε)
    {g : Unit → NonDetE (State Unit) ε β} (hg : c → OkDAt σ P (g ())) :
    OkDAt σ P (NonDetE.unlessE c (NonDetE.throwError e) >>= g) := by
  refine okdAt_bind fun a s h => ?_
  unfold NonDetE.unlessE at h
  split at h
  · rename_i hc
    rw [ExceptT.run_pure] at h
    have e := Set.mem_singleton_iff.1 h
    simp only [Prod.mk.injEq] at e
    obtain ⟨-, rfl⟩ := e
    exact hg hc
  · have e := Set.mem_singleton_iff.1 h; simp at e

theorem okdAt_true {m : NonDetE (State Unit) ε α} : OkDAt σ (fun _ _ => True) m := fun _ _ _ => trivial

end

theorem archDataToObjType_vcpu {k : Nat} (h : archDataToObjType k = some .vcpuObj) : k = 7 := by
  unfold archDataToObjType at h
  split_ifs at h <;> first | omega | cases h

/-- `data_to_obj_type` returns the VCPU type only for 14. -/
theorem okd_dataToObjType (type : Data) (σ : State Unit) :
    OkDAt σ (fun _ t => t = .archObject .vcpuObj → dataToNat type = 14) (dataToObjType (Z := Unit) type) := by
  unfold dataToObjType
  refine okdAt_returnOk_bind ?_
  by_cases h0 : dataToNat type = 0
  · rw [if_pos h0]; exact okdAt_returnOk (fun h => by cases h)
  rw [if_neg h0]
  by_cases h1 : dataToNat type = 1
  · rw [if_pos h1]; exact okdAt_returnOk (fun h => by cases h)
  rw [if_neg h1]
  by_cases h2 : dataToNat type = 2
  · rw [if_pos h2]; exact okdAt_returnOk (fun h => by cases h)
  rw [if_neg h2]
  by_cases h3 : dataToNat type = 3
  · rw [if_pos h3]; exact okdAt_returnOk (fun h => by cases h)
  rw [if_neg h3]
  by_cases h4 : dataToNat type = 4
  · rw [if_pos h4]; exact okdAt_returnOk (fun h => by cases h)
  rw [if_neg h4]
  by_cases h5 : dataToNat type = 5
  · rw [if_pos h5]; exact okdAt_returnOk (fun h => by cases h)
  rw [if_neg h5]
  by_cases h6 : dataToNat type = 6
  · rw [if_pos h6]; exact okdAt_returnOk (fun h => by cases h)
  rw [if_neg h6]
  split
  · rename_i tp htp
    refine okdAt_returnOk fun h => ?_
    cases h
    have := archDataToObjType_vcpu htp
    omega
  · exact okdAt_throw _

/-- The type of a retype. -/
def utType : UntypedInvocation → ApiObjectType
  | .retype _ _ _ _ t _ _ _ => t

/-- After the type is decoded, the retype's type is it. -/
macro "okt_auto" : tactic => `(tactic| repeat' (first
  | exact okdAt_throw _
  | (refine okdAt_returnOk ?_; rfl)
  | (with_reducible refine okdAt_bind fun ⟨_, _⟩ _ _ => ?_)
  | (with_reducible refine okdAt_bind fun _ _ _ => ?_)
  | (refine okdAt_ite _ ?_ ?_)
  | split))

/-- **A VCPU retype of the untyped decoder is on the VT-x gate's inputs.** -/
theorem okd_decodeUntypedVcpu (bitsApi : ApiObjectType → Nat → Nat) (label : Data) (args : List Data)
    (slot : CslotPtr) (cap : Cap) (excaps : List Cap) (σ : State Unit) :
    OkDAt σ (fun _ ui => utType ui = .archObject .vcpuObj →
        genInvocationType label = .untypedRetype ∧ 6 ≤ args.length ∧ excaps ≠ [] ∧
          dataToNat (args.getD 0 0) = 14)
      (decodeUntypedInvocationWith (Z := Unit) bitsApi label args slot cap excaps) := by
  unfold decodeUntypedInvocationWith
  refine okdAt_unlessE_bind _ _ fun hl => ?_
  refine okdAt_whenE_bind _ _ fun hlen => ?_
  refine okdAt_whenE_bind _ _ fun hex => ?_
  refine okdAt_returnOk_bind ?_
  refine okdAt_bind fun t s ht => ?_
  have ht' := okd_dataToObjType _ σ t s ht
  have hargs : the args[0]? = args.getD 0 0 := by
    cases args with
    | nil => simp at hlen
    | cons a l => rfl
  refine okdAt_mono' (Q := fun _ ui => utType ui = t) ?_ fun _ ui hu hv => ?_
  · okt_auto
  · refine ⟨hl, by omega, fun e => by simp [e] at hex, ?_⟩
    rw [← hargs]; exact ht' (hu.symm.trans hv)

/-- **`InvOK` of the ported dispatcher's outcomes** (module docstring). -/
theorem okd_fl4Decode_invOK (hvk : virtKind = .none) (fp : Bool) (label : Data) (args : List Data) (ci : CapRef)
    (sl : CslotPtr) (cap : Cap) (ex : List (Cap × CslotPtr)) (b : Option ObjRef) (σ : State Unit)
    (hg : ∀ d p n f, cap = .untypedCap d p n f → ¬ untypedVtxGate label args (ex.map Prod.fst))
    (htcb : ∀ p, cap = .threadCap p → OkDAt σ (fun _ i => InvOK i)
      (fl4DecodeTcbInvocation (Z := Unit) label args cap sl ex b)) :
    OkDAt σ (fun _ i => InvOK i) (fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex b) := by
  cases cap with
  | untypedCap d p n f =>
    simp only [fl4DecodeInvocation]
    refine okdAt_liftME ?_
    intro ui s hu
    obtain ⟨src, reset, base, rb, t, sz, slots, dev⟩ := ui
    show t ≠ .archObject .vcpuObj
    intro e
    obtain ⟨h1, h2, h3, h4⟩ := okd_decodeUntypedVcpu fl4ObjBitsApi label args sl _ _ σ _ s hu e
    refine hg d p n f rfl ⟨h1, h2, h3, ?_, hvk⟩
    show isVtxObjectTypeNum (dataToNat (args.getD 0 0)) = true
    rw [h4]; decide
  | threadCap p =>
    simp only [fl4DecodeInvocation]
    split
    · exact okdAt_throw _
    · exact htcb p rfl
  | endpointCap =>
    simp only [fl4DecodeInvocation]; split
    · exact okdAt_returnOk trivial
    · exact okdAt_throw _
  | notificationCap =>
    simp only [fl4DecodeInvocation]; split
    · exact okdAt_returnOk trivial
    · exact okdAt_throw _
  | replyCap => simp only [fl4DecodeInvocation]; exact okdAt_returnOk trivial
  | irqControlCap => simp only [fl4DecodeInvocation]; exact okdAt_liftME fun _ _ _ => trivial
  | irqHandlerCap => simp only [fl4DecodeInvocation]; exact okdAt_liftME fun _ _ _ => trivial
  | archObjectCap => simp only [fl4DecodeInvocation]; exact okdAt_liftME fun _ _ _ => trivial
  | domainCap =>
    simp only [fl4DecodeInvocation]; split
    · exact okdAt_throw _
    · exact okdAt_liftME fun _ _ _ => trivial
  | schedContextCap =>
    simp only [fl4DecodeInvocation]; split
    · exact okdAt_throw _
    · exact okdAt_liftME fun _ _ _ => trivial
  | schedControlCap =>
    simp only [fl4DecodeInvocation]; split
    · exact okdAt_throw _
    · exact okdAt_liftME fun _ _ _ => trivial
  | cnodeCap =>
    simp only [fl4DecodeInvocation]; split
    · exact okdAt_throw _
    · exact okdAt_liftME fun _ _ _ => trivial
  | _ => simp only [fl4DecodeInvocation]; exact okdAt_throw _

/-- **`OffRoute3` with the `InvOK` half for thread caps only** (the reduced [S] premise). -/
def OffRoute4 (fp : Bool) (cptr : CapRef) (s : State Unit) : Prop :=
  ∀ info a args u, DecPt cptr s info a args u →
    ¬ Route3 fp info.miLabel args a.2.1 a.2.2.1 ∧
    ∀ p, a.2.1 = .threadCap p → OkDAt u (fun _ i => InvOK i)
      (fl4DecodeTcbInvocation (Z := Unit) info.miLabel args a.2.1 a.1 a.2.2.1 a.2.2.2)

theorem offRoute3_of4 (hvk : virtKind = .none) {fp : Bool} {cptr : CapRef} {s : State Unit}
    (h : OffRoute4 fp cptr s) : OffRoute3 fp cptr s := by
  intro info a args u hd
  obtain ⟨hr, ht⟩ := h info a args u hd
  refine ⟨hr, fun i v hi => ?_⟩
  refine okd_fl4Decode_invOK hvk fp _ args cptr _ _ _ _ u (fun d p n f e => ?_) ht i v hi
  intro hgate
  apply hr
  rw [e]
  exact hgate

def OffRouteS4 (c : Syscall) (t : State Unit) : Prop :=
  ∀ reg, sysReg c = some reg → ∀ cptr t', (cptr, t') ∈ (getCapReg (Z := Unit) reg t).1 → ∀ fp, OffRoute4 fp cptr t'

theorem offRouteS3_of4 (hvk : virtKind = .none) {c : Syscall} {t : State Unit} (h : OffRouteS4 c t) :
    OffRouteS3 c t :=
  fun reg hr cptr t' hm fp => offRoute3_of4 hvk (h reg hr cptr t' hm fp)

/-- **R7 (e) with the scope reduced to the routes and the TCB decode** (premises `hvk`, `hoff4` [S], module
docstring). -/
theorem fl4CallKernelV_eqNR4 (hvk : virtKind = .none) (onCore : ObjRef → Bool) (rep : Bool) (ev : Event)
    {σ : State Unit} (hs : NR σ) (hoff4 : ∀ c, ev = .syscallEvent c → ∀ t, EntryPt σ t → OffRouteS4 c t) :
    fl4CallKernelV (Z := Unit) onCore rep ev σ = fl4CallKernel rep ev σ :=
  fl4CallKernelV_eqNR3 onCore rep ev hs fun c hc t ht => offRouteS3_of4 hvk (hoff4 c hc t ht)

end

end Fl4Proofs.P3.VirtInvOK
