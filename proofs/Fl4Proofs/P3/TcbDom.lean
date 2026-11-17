/-
P3 (DESIGN.md §9), TCB invocations: **the Thread cap's domain-schedule
frame** (`DomFrame`).

* `dke_invokeTcb`, `dke_invokeFl4Tcb`: every TCB invocation of the spec
  keeps `domain_list` and `domain_start_index` (`DK`, VsDom; deletions by
  DomRecDel); `dk_spec_thread`, the spec half of the Thread cap's
  `DomFrame` (the decode gives only TCB invocations, `okAll_specDec_threadK`).
* `TcbDomHyp`: FL4's `tcb::decode` at a label keeps the kernel-global base
  and the five domain-schedule words; `TcbDecFootP1`, the same in P1's shape
  (a `Foot` in `KW` of P1's sets, `KW` apart from the domain schedule,
  `KWDom`), for P1's `TcbGaps` labels: `tcbDomHyp_of_foot`.
* `domFrame_thread`: the Thread cap's `DomFrame`.
-/
import Fl4Proofs.P3.DomRecDel
import Fl4Proofs.P3.TcbReadRegsSpec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open Fl4Spec Classical

noncomputable section

theorem dk_orderedInsert' {α β : Type} [Nonempty β] (t : α) (ts : List α) (f : α → RMonad Unit β)
    (R : β → β → Prop) : DK (orderedInsert (Z := Unit) t ts f R) := by
  unfold orderedInsert; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_orderedInsert' _ _ _ _)

theorem dk_readyTimesAppend' (t : ObjRef) (q : List ObjRef) : DK (readyTimesAppend (Z := Unit) t q) := by
  unfold readyTimesAppend; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_readyTimesAppend' _ _)

theorem dk_tcbReleaseEnqueue' (t : ObjRef) : DK (tcbReleaseEnqueue (Z := Unit) t) := by
  unfold tcbReleaseEnqueue; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_tcbReleaseEnqueue' _)

theorem dk_tcbAppend' (t : ObjRef) (q : List ObjRef) : DK (tcbAppend (Z := Unit) t q) := by
  unfold tcbAppend; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_tcbAppend' _ _)

theorem dk_postpone' (sc : ObjRef) : DK (postpone (Z := Unit) sc) := by
  unfold postpone; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_postpone' _)

theorem dk_threadSetPriority' (t : ObjRef) (p : Priority) : DK (threadSetPriority (Z := Unit) t p) := by
  unfold threadSetPriority; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_threadSetPriority' _ _)

theorem dk_reorderEp' (e t : ObjRef) : DK (reorderEp (Z := Unit) e t) := by
  unfold reorderEp; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_reorderEp' _ _)

theorem dk_reorderNtfn' (n t : ObjRef) : DK (reorderNtfn (Z := Unit) n t) := by
  unfold reorderNtfn; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_reorderNtfn' _ _)

theorem dk_archPostModifyRegisters' (c t : ObjRef) : DK (archPostModifyRegisters (Z := Unit) c t) := by
  unfold archPostModifyRegisters; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_archPostModifyRegisters' _ _)

theorem dk_schedContextResume' (sc : ObjRef) : DK (schedContextResume (Z := Unit) sc) := by
  unfold schedContextResume; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_schedContextResume' _)

theorem dk_testPossibleSwitchTo' (t : ObjRef) : DK (testPossibleSwitchTo (Z := Unit) t) := by
  unfold testPossibleSwitchTo; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_testPossibleSwitchTo' _)

theorem dk_ifSporadicCurScTestRefillUnblockCheck' (o : Option ObjRef) : DK (ifSporadicCurScTestRefillUnblockCheck (Z := Unit) o) := by
  unfold ifSporadicCurScTestRefillUnblockCheck; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_ifSporadicCurScTestRefillUnblockCheck' _)

theorem dk_restart' (t : ObjRef) : DK (restart (Z := Unit) t) := by
  unfold restart; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_restart' _)

theorem dk_setMcpriority' (t : ObjRef) (m : Priority) : DK (setMcpriority (Z := Unit) t m) := by
  unfold setMcpriority; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_setMcpriority' _ _)

theorem dk_setPriority' (t : ObjRef) (p : Priority) : DK (setPriority (Z := Unit) t p) := by
  unfold setPriority; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_setPriority' _ _)

theorem dk_schedContextBindTcb' (sc t : ObjRef) : DK (schedContextBindTcb (Z := Unit) sc t) := by
  unfold schedContextBindTcb; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_schedContextBindTcb' _ _)

theorem dk_bindNotification' (t n : ObjRef) : DK (bindNotification (Z := Unit) t n) := by
  unfold bindNotification; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_bindNotification' _ _)

theorem dk_setFlags' (t : ObjRef) (f : TcbFlags) : DK (setFlags (Z := Unit) t f) := by
  unfold setFlags; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_setFlags' _ _)

theorem dk_lazyFpuRestore' (t : ObjRef) : DK (lazyFpuRestore (Z := Unit) t) := by
  unfold lazyFpuRestore; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_lazyFpuRestore' _)

theorem dk_archPostSetFlags' (t : ObjRef) (f : TcbFlags) : DK (archPostSetFlags (Z := Unit) t f) := by
  unfold archPostSetFlags; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_archPostSetFlags' _ _)

theorem dk_checkCapAt' (c : Cap) (sl : CslotPtr) {m : SMonad Unit Unit} (h : DK m) :
    DK (checkCapAt (Z := Unit) c sl m) := by
  unfold checkCapAt; dk_auto; exact h
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible refine dk_checkCapAt' _ _ ?_)

theorem dke_installTcbCap' (t : ObjRef) (sl : CslotPtr) (n : Nat) (o : Option (Cap × CslotPtr)) :
    DKE (installTcbCap (Z := Unit) t sl n o) := by
  unfold installTcbCap; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dke_installTcbCap' _ _ _ _)

theorem dke_installTcbFrameCap' (t : ObjRef) (sl : CslotPtr) (b : Option (VSpaceRef × Option (Cap × CslotPtr))) :
    DKE (installTcbFrameCap (Z := Unit) t sl b) := by
  unfold installTcbFrameCap; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dke_installTcbFrameCap' _ _ _)

/-! ## `invoke_tcb` -/

theorem dke_invokeTcb (i : TcbInvocation) : DKE (invokeTcb (Z := Unit) i) := by
  cases i <;> unfold invokeTcb <;> dk_auto

theorem dke_invokeFl4Tcb (i : Fl4TcbInvocation) : DKE (invokeFl4Tcb (Z := Unit) i) := by
  cases i <;> unfold invokeFl4Tcb <;> dk_auto

theorem dke_fl4PerformTcb (blk call don : Bool) (i : TcbInvocation) :
    DKE (fl4PerformInvocation (Z := Unit) blk call don (.invokeTCB i)) := dke_invokeTcb i

theorem dke_fl4PerformFl4Tcb (blk call don : Bool) (i : Fl4TcbInvocation) :
    DKE (fl4PerformInvocation (Z := Unit) blk call don (.invokeFl4TCB i)) := dke_invokeFl4Tcb i

end

end Fl4Proofs.P3.Vs

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Spec

noncomputable section

/-- The invocations of a Thread cap. -/
def TcbInvK (i : Fl4Invocation) : Prop := (∃ t, i = .invokeTCB t) ∨ ∃ t, i = .invokeFl4TCB t

/-- **A Thread cap's decode gives only TCB invocations.** -/
theorem okAll_specDec_threadK (fp : Bool) (slbl : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr)
    (p : U64) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    OkAll TcbInvK (specDec fp slbl args ci sl (.Thread p) excaps buffer) := by
  unfold specDec
  show OkAll TcbInvK (fl4DecodeInvocation (Z := Unit) fp slbl args ci sl (.threadCap p.bv) excaps buffer)
  unfold fl4DecodeInvocation
  dsimp only
  refine okAll_ite (fun _ => okAll_throw) (fun _ => ?_)
  unfold fl4DecodeTcbInvocation
  refine okAll_ite (fun _ => okAll_liftME (okAll_true _) fun a _ => Or.inr ⟨a, rfl⟩) (fun _ => ?_)
  cases fl4TcbExtLabelOf slbl with
  | some l => exact okAll_liftME (okAll_true _) fun a _ => Or.inr ⟨a, rfl⟩
  | none => exact okAll_liftME (okAll_true _) fun a _ => Or.inl ⟨a, rfl⟩

/-- **The spec half of the Thread cap's `DomFrame`.** -/
theorem dk_spec_thread {fp : Bool} {slbl : Data} {args : List Data} {ci : CapRef} {sl : CslotPtr} {p : U64}
    {excaps : List (Cap × CslotPtr)} {buffer : Option ObjRef} {blk call don : Bool} {σ : State Unit} {tcb : Tcb}
    (hkt : σ.kheap σ.curThread = some (.tcb tcb)) :
    ∀ inv σ1, DecOut (specDec fp slbl args ci sl (.Thread p) excaps buffer) σ inv →
      setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
      ∀ y ∈ ((fl4PerformInvocation (Z := Unit) blk call don inv).run σ1).1,
        y.2.domainList = σ.domainList ∧ y.2.domainStartIndex = σ.domainStartIndex := by
  intro inv σ1 hd he y hy
  have h1 := setThreadState_dom hkt he
  have h2 : y.2.domainList = σ1.domainList ∧ y.2.domainStartIndex = σ1.domainStartIndex := by
    rcases hd.okAll (okAll_specDec_threadK fp slbl args ci sl p excaps buffer) with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · exact Vs.DK.dom (Vs.dke_fl4PerformTcb blk call don t) hy
    · exact Vs.DK.dom (Vs.dke_fl4PerformFl4Tcb blk call don t) hy
  exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **FL4's `tcb::decode` at a label keeps the domain schedule's words** (and
the kernel-global base). -/
def TcbDomHyp (s : S) (ar : A) (lbl p : U64) (c : tcb.Ctx) : Prop :=
  tcb.decode st arI s ar lbl p c ⦃ r => L.ksb r.2.1 = L.ksb s ∧
    ∀ o ∈ domOffs, L.mem r.2.1 (ksW (L.ksb s) o) = L.mem s (ksW (L.ksb s) o) ⦄

/-- **`TcbDomHyp` in P1's shape**: `tcb::decode` at the label writes in `KW`
of P1's sets (`Foot`), `KW` lying apart from the domain schedule. -/
def TcbDecFootP1 (s : S) (ar : A) (lbl p : U64) (c : tcb.Ctx) : Prop :=
  ∃ (T Cs Sg Scs : Set U64) (Z : U64 → Nat) (H : P1.Heap),
    tcb.decode st arI s ar lbl p c ⦃ r => P1.Foot st T Cs Sg Scs Z (P1.EH H) s r.2.1 ⦄ ∧
    KWDom (L := L) T Cs Sg Scs Z (P1.EH H) s

theorem tcbDomHyp_of_foot {s : S} {ar : A} {lbl p : U64} {c : tcb.Ctx}
    (hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64) (hka : (L.ksb s).val % 8 = 0)
    (h : TcbDecFootP1 (L := L) arI s ar lbl p c) : TcbDomHyp (L := L) arI s ar lbl p c := by
  obtain ⟨T, Cs, Sg, Scs, Z, H, hf, hD⟩ := h
  refine WP.spec_mono hf fun r hr => ⟨hr.1, fun o ho => ?_⟩
  obtain ⟨h1, h2⟩ := Sched.domOffs_lt ho
  refine hr.mem_eq (ksW_al hkf hka h1 h2) fun hk => ?_
  have hv := ksW_val (kb := L.ksb s) (o := o) (by omega)
  rcases hD _ (ksW_al hkf hka h1 h2) hk with e | e <;> rw [hv] at e <;> omega

/-- **The Thread cap's `DomFrame`**, from `TcbDomHyp` at the label (when not
the first phase) and `dk_spec_thread`. -/
theorem domFrame_thread (s : S) (ar : A) (σ : State Unit) (lbl length slot : U64) (p : U64)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ct : U64)
    (hct : sched.cur_thread st s = ok ct) {tcb : Tcb} (hkt : σ.kheap σ.curThread = some (.tcb tcb))
    (slbl : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr) (excaps : List (Cap × CslotPtr))
    (buffer : Option ObjRef)
    (hF : fp = false → TcbDomHyp (L := L) arI s ar lbl p ⟨length, buf, call, slot, extra⟩) :
    DomFrame (L := L) arI s ar σ lbl length slot (.Thread p) blk call don fp buf extra slbl args ci sl excaps
      buffer := by
  refine ⟨?_, dk_spec_thread hkt⟩
  unfold syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact hF rfl
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    exact ⟨rfl, fun _ _ => rfl⟩

end

end

end Fl4Proofs.P3
