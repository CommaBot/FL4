/-
P3 (DESIGN.md §9), CSpace: **`FinWorkHyp` by the kind of cap**
(`finWorkHyp_split`). Proved here, each from P1's FL4-side lemma and a spec
frame (`NKC`, SpecCaps / SpecFinFrames): the notification, reply,
endpoint, thread and scheduling-context caps (`finWorkAt_ntfn`, `_reply`,
`_ep`, `_thread`, `_sc`). Left as named hypotheses: the IRQ handler caps
(`IrqFinHyp`, until the IRQ invariants are in `DState`), the VCPU and EPT
caps (`VmFinHyp`, outside the semantic scope), and the rest (`FinWorkAt
FinRestK`: the VSpace caps, proved by the VSpace side).

Each case: the finalisation writes no cap-slot word (P1), so FL4's slots
are unchanged (`SlotsSame`, through `SlotCapW`); the spec's keeps every cap
(`NKC`), so the CSpace relation carries over and the step is
`MdbStep.of_same`. What is left of a case is
* the coupling of P3's state to P1's invariant at the cap, in one shape for
  all kinds (`P1CapHyp th Obj`: `BlkOK` for some sets `P1Sets`, the slots
  among P1's `CapW` words, and the cap's object facts `Obj`; the instances
  `NtfnP1Hyp` .. `ScP1Hyp`);
* that the spec's finalisation has an outcome (`SpecFinOut`).
-/
import Fl4Proofs.P3.DelObj
import Fl4Proofs.P3.SpecFinFrames
import Fl4Proofs.P3.ScInstFoot
import Fl4Proofs.P3.DomDecode
import Fl4Proofs.P3.TcbCaps
import Fl4Proofs.P1.QueueFinCap
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical
open Fl4Proofs.P3.Sched (SlotCapW)

noncomputable section

/-- Notification caps. -/
def FinNtfnK (c : capability.Cap) : Prop := ∃ n b0 b1 b2, c = .Notification n b0 b1 b2
/-- Reply caps. -/
def FinReplyK (c : capability.Cap) : Prop := ∃ p x, c = .Reply p x
/-- Endpoint caps. -/
def FinEpK (c : capability.Cap) : Prop := ∃ e b x1 x2 x3 x4, c = .Endpoint e b x1 x2 x3 x4
/-- Thread caps. -/
def FinThreadK (c : capability.Cap) : Prop := ∃ p, c = .Thread p
/-- Scheduling-context caps. -/
def FinScK (c : capability.Cap) : Prop := ∃ p x, c = .SchedContext p x
/-- IRQ handler caps. -/
def FinIrqK (c : capability.Cap) : Prop := ∃ i, c = .IrqHandler i
/-- VCPU and EPT caps. -/
def FinVmK (c : capability.Cap) : Prop := (∃ p, c = .Vcpu p) ∨ ∃ p l m a v, c = .Ept p l m a v
/-- The other caps (the VSpace caps among the finalised ones). -/
def FinRestK (c : capability.Cap) : Prop :=
  ¬ FinNtfnK c ∧ ¬ FinReplyK c ∧ ¬ FinEpK c ∧ ¬ FinThreadK c ∧ ¬ FinScK c ∧ ¬ FinIrqK c ∧ ¬ FinVmK c

/-- The sets of P1's invariant `BlkOK`. -/
structure P1Sets where
  T : Set U64
  Cs : Set U64
  Ω : Set U64
  H : P1.Heap
  Sg : Set U64
  Rp : Set U64
  Scs : Set U64
  Nt : Set U64
  Z : U64 → Nat
  Ac : Set U64

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`FinWorkHyp` for the caps of kind `K`.** -/
def FinWorkAt (K : capability.Cap → Prop) (th : TypedHeap) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (c : capability.Cap),
    K c → DState (L := L) th s σ G → AbsSlot th sl → capAt (L.mem s) (cslotAddr sl) = ok c → FinObjKind c →
    FinWork c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) →
    objects.finalise_cap st arI s a c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) false ⦃ r =>
      r.1.1 = finRem c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) ∧ CleanCap r.1.2 ∧ CapWf r.1.2 ∧
      ∃ σ' G', ((absCap r.1.1, absCap r.1.2), σ') ∈
          (Fl4Spec.finaliseCap (Z := Unit) (absCap c) (decide (Fl4Spec.isFinalCap' (absCap c) σ)) σ).1 ∧
        DState (L := L) th r.2.1 σ' G' ∧ capV (L.mem r.2.1) (cslotAddr sl) = c ∧
        (∀ y, IsSlot th y → y ≠ cslotAddr sl → capV (L.mem r.2.1) y = capV (L.mem s) y ∨
          (capV (L.mem r.2.1) y = .Null ∧ isZb (capV (L.mem s) y) = false)) ∧
        MdbStep (L.mem s) G (L.mem r.2.1) G' ⦄

/-- **The IRQ handler case**, a hypothesis until the IRQ invariants
(`IrqSlotOK`, `IntLayout`, `IrqRel`) are in `DState`. -/
abbrev IrqFinHyp (th : TypedHeap) : Prop := FinWorkAt (L := L) arI FinIrqK th

/-- **The VCPU and EPT caps**, a hypothesis: their functional refinement is
outside the semantic scope (DESIGN.md §9). -/
abbrev VmFinHyp (th : TypedHeap) : Prop := FinWorkAt (L := L) arI FinVmK th

/-- **`FinWorkHyp` from its kinds.** -/
theorem finWorkHyp_split (th : TypedHeap) (hN : FinWorkAt (L := L) arI FinNtfnK th)
    (hR : FinWorkAt (L := L) arI FinReplyK th) (hE : FinWorkAt (L := L) arI FinEpK th)
    (hT : FinWorkAt (L := L) arI FinThreadK th) (hS : FinWorkAt (L := L) arI FinScK th)
    (hI : IrqFinHyp (L := L) arI th) (hV : VmFinHyp (L := L) arI th)
    (hX : FinWorkAt (L := L) arI FinRestK th) : FinWorkHyp (L := L) arI th := by
  intro s a σ G sl c
  by_cases h1 : FinNtfnK c
  · exact hN s a σ G sl c h1
  by_cases h2 : FinReplyK c
  · exact hR s a σ G sl c h2
  by_cases h3 : FinEpK c
  · exact hE s a σ G sl c h3
  by_cases h4 : FinThreadK c
  · exact hT s a σ G sl c h4
  by_cases h5 : FinScK c
  · exact hS s a σ G sl c h5
  by_cases h6 : FinIrqK c
  · exact hI s a σ G sl c h6
  by_cases h7 : FinVmK c
  · exact hV s a σ G sl c h7
  exact hX s a σ G sl c ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- **The spec's finalisation of a final cap of kind `K` has an outcome**
(with the remainder and no cleanup cap). -/
def SpecFinOut (K : capability.Cap → Prop) (th : TypedHeap) : Prop :=
  ∀ (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (c : capability.Cap),
    K c → DState (L := L) th s σ G → AbsSlot th sl → capAt (L.mem s) (cslotAddr sl) = ok c →
    Fl4Spec.isFinalCap' (absCap c) σ →
    ∃ σ', ((absCap (finRem c true), absCap .Null), σ') ∈ (Fl4Spec.finaliseCap (Z := Unit) (absCap c) true σ).1

/-- P1's invariant for the sets `X`. -/
abbrev P1Blk (X : P1Sets) (s : S) : Prop := P1.BlkOK st X.T X.Cs X.Ω X.H X.Sg X.Rp X.Scs X.Nt X.Z X.Ac s

/-- **P1's invariant at a cap** (one shape for every kind): at a related
state with the cap `c` in a slot, P1's invariant `BlkOK` holds for some sets
`X`, the cap slots are among P1's `CapW` words, and `Obj c X s` (the cap's
object in its set, the kind's side conditions). -/
def P1CapHyp (th : TypedHeap) (Obj : capability.Cap → P1Sets → S → Prop) : Prop :=
  ∀ (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (c : capability.Cap),
    DState (L := L) th s σ G → AbsSlot th sl → capAt (L.mem s) (cslotAddr sl) = ok c → FinObjKind c →
    ∃ X : P1Sets, P1Blk (st := st) X s ∧ SlotCapW th X.T X.Ω X.Sg ∧ Obj c X s

/-- The notification in P1's set. -/
def NtfnObj (c : capability.Cap) (X : P1Sets) (_ : S) : Prop :=
  ∀ n b0 b1 b2, c = .Notification n b0 b1 b2 → n ∈ X.Nt ∧ X.H n = some .ntfn
/-- The reply in P1's set. -/
def ReplyObj (c : capability.Cap) (X : P1Sets) (_ : S) : Prop := ∀ p x, c = .Reply p x → p ∈ X.Rp
/-- The endpoint an endpoint of P1's heap. -/
def EpObj (c : capability.Cap) (X : P1Sets) (_ : S) : Prop :=
  ∀ e b x1 x2 x3 x4, c = .Endpoint e b x1 x2 x3 x4 → X.H e = some .ep
/-- The thread in P1's set, not the scheduler's switch target nor the idle
thread, its VCPU link unbound. -/
def ThreadObj (c : capability.Cap) (X : P1Sets) (s : S) : Prop :=
  ∀ p, c = .Thread p → p ∈ X.T ∧ L.actionW s ≠ p ∧ L.idleW s ≠ p ∧
    L.mem s (core.num.U64.wrapping_add p 3664#u64) = 0#u64
/-- The SC in P1's set, non-zero, its TCB (if any) not the scheduler's
switch target nor the idle thread. -/
def ScObj (c : capability.Cap) (X : P1Sets) (s : S) : Prop :=
  ∀ p x, c = .SchedContext p x → p ∈ X.Scs ∧ p ≠ 0#u64 ∧
    (L.mem s (P1.scTcbA p) ≠ 0#u64 → L.actionW s ≠ L.mem s (P1.scTcbA p)) ∧
    (L.mem s (P1.scTcbA p) ≠ 0#u64 → L.idleW s ≠ L.mem s (P1.scTcbA p))

abbrev NtfnP1Hyp (th : TypedHeap) : Prop := P1CapHyp (L := L) th NtfnObj
abbrev ReplyP1Hyp (th : TypedHeap) : Prop := P1CapHyp (L := L) th ReplyObj
abbrev EpP1Hyp (th : TypedHeap) : Prop := P1CapHyp (L := L) th EpObj
abbrev ThreadP1Hyp (th : TypedHeap) : Prop := P1CapHyp (L := L) th (ThreadObj (L := L))
abbrev ScP1Hyp (th : TypedHeap) : Prop := P1CapHyp (L := L) th (ScObj (L := L))

/-- FL4's slots unchanged when no `CapW` word is. -/
theorem slotsSame_of_capw {th : TypedHeap} (hP : Placed th) {T Ω Sg : Set U64} (hSC : SlotCapW th T Ω Sg)
    {s s' : S} (h : ∀ b, P1.Aligned b → P1.CapW T Ω Sg b → L.mem s' b = L.mem s b) :
    SlotsSame th (L.mem s) (L.mem s') := fun a ha => by
  have w : ∀ k, Off k → L.mem s' (wordOf a k) = L.mem s (wordOf a k) := fun k hk =>
    h _ (slot_word_aligned hP ha hk) (hSC _ ⟨a, ha, k, hk, rfl⟩)
  exact ⟨by have := w _ off0; rwa [wordOf_zero] at this, w _ off8, w _ off16, w _ off24⟩

/-- **A finalisation with no slot change on FL4's side and no cap change on
the spec's** gives `FinWorkAt`'s post, with the remainder `rem`, no cleanup
cap and the ghost tree unchanged. -/
theorem finWork_post_same {th : TypedHeap} {s s' : S} {a' : A} {σ σ' : Fl4Spec.State Unit} {G : MdbGhost}
    {sl : Fl4Spec.CslotPtr} {c rem : capability.Cap} {b : Bool} (hDS : DState (L := L) th s σ G) (hA : AbsSlot th sl)
    (hc : capAt (L.mem s) (cslotAddr sl) = ok c) (hrem : finRem c b = rem)
    (hS : SlotsSame th (L.mem s) (L.mem s')) (hmem : ((absCap rem, absCap .Null), σ') ∈
      (Fl4Spec.finaliseCap (Z := Unit) (absCap c) b σ).1) (hK : CKeep σ σ') :
    let r : (capability.Cap × capability.Cap) × S × A := ((rem, .Null), s', a')
    r.1.1 = finRem c b ∧ CleanCap r.1.2 ∧ CapWf r.1.2 ∧
      ∃ σ' G', ((absCap r.1.1, absCap r.1.2), σ') ∈ (Fl4Spec.finaliseCap (Z := Unit) (absCap c) b σ).1 ∧
        DState (L := L) th r.2.1 σ' G' ∧ capV (L.mem r.2.1) (cslotAddr sl) = c ∧
        (∀ y, IsSlot th y → y ≠ cslotAddr sl → capV (L.mem r.2.1) y = capV (L.mem s) y ∨
          (capV (L.mem r.2.1) y = .Null ∧ isZb (capV (L.mem s) y) = false)) ∧
        MdbStep (L.mem s) G (L.mem r.2.1) G' := by
  intro r
  have hR' : StateRel th (L.mem s') σ' := (hDS.1.1.of_caps (fun x hx => hS.capAt hx)).of_ckeep hK
  obtain ⟨hCR', -⟩ := crel_step hDS.1 hDS.2.2 hS hK.ks hR' hK.cdt hK.orig
  refine ⟨hrem.symm, trivial, trivial, σ', G, hmem, DState.of_same hDS hS hCR' hK.ks, ?_,
    fun y hy _ => Or.inl (hS.capV hy), MdbStep.of_same hDS.1.2.2.1 hS⟩
  show capV (L.mem s') (cslotAddr sl) = c
  rw [hS.capV hA.isSlot]; exact capV_of_capAt hc

/-- **The notification case.** -/
theorem finWorkAt_ntfn (th : TypedHeap) (hP : Placed th) (hP1 : NtfnP1Hyp (L := L) th)
    (hEx : SpecFinOut (L := L) FinNtfnK th) : FinWorkAt (L := L) arI FinNtfnK th := by
  intro s a σ G sl c hk hDS hA hc hfk hw
  obtain ⟨n, b0, b1, b2, rfl⟩ := hk
  obtain ⟨X, hB, hSC, hO⟩ := hP1 s σ G sl _ hDS hA hc hfk
  obtain ⟨hn, hH⟩ := hO n b0 b1 b2 rfl
  have hfin : decide (Fl4Spec.isFinalCap' (absCap (.Notification n b0 b1 b2)) σ) = true := by
    simpa [FinWork, isFrame] using hw
  rw [hfin]
  obtain ⟨σ', hmem⟩ := hEx s σ G sl _ ⟨n, b0, b1, b2, rfl⟩ hDS hA hc (of_decide_eq_true hfin)
  refine WP.spec_mono (P1.fin_cap_ntfn.slots (ar := arI) s a n b0 b1 b2 true false hB hn hH) ?_
  rintro ⟨⟨r1, r2⟩, s', a'⟩ ⟨e, -, -, hW⟩
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact finWork_post_same (L := L) hDS hA hc rfl (slotsSame_of_capw hP hSC hW) hmem
    (finNtfn_nkc _ _ _ true σ _ hmem)

/-- **The reply case.** -/
theorem finWorkAt_reply (th : TypedHeap) (hP : Placed th) (hAT : P0.ArchTotal arI) (hP1 : ReplyP1Hyp (L := L) th)
    (hEx : SpecFinOut (L := L) FinReplyK th) : FinWorkAt (L := L) arI FinReplyK th := by
  intro s a σ G sl c hk hDS hA hc hfk hw
  obtain ⟨p, x, rfl⟩ := hk
  obtain ⟨X, hB, hSC, hO⟩ := hP1 s σ G sl _ hDS hA hc hfk
  have hp := hO p x rfl
  have hfin : decide (Fl4Spec.isFinalCap' (absCap (.Reply p x)) σ) = true := by
    simpa [FinWork, isFrame] using hw
  rw [hfin]
  obtain ⟨σ', hmem⟩ := hEx s σ G sl _ ⟨p, x, rfl⟩ hDS hA hc (of_decide_eq_true hfin)
  refine WP.spec_mono (P1.fin_cap_reply.slots hAT s a p x true false hB hp) ?_
  rintro ⟨⟨r1, r2⟩, s', a'⟩ ⟨e, -, -, hW⟩
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact finWork_post_same (L := L) hDS hA hc rfl (slotsSame_of_capw hP hSC hW) hmem
    (finReply_nkc _ _ true σ _ hmem)


/-- **The endpoint case.** -/
theorem finWorkAt_ep (th : TypedHeap) (hP : Placed th)
    (hP1 : EpP1Hyp (L := L) th) (hEx : SpecFinOut (L := L) FinEpK th) : FinWorkAt (L := L) arI FinEpK th := by
  intro s a σ G sl c hk hDS hA hc hfk hw
  obtain ⟨e, b, x1, x2, x3, x4, rfl⟩ := hk
  obtain ⟨X, hB, hSC, hO⟩ := hP1 s σ G sl _ hDS hA hc hfk
  have hH := hO e b x1 x2 x3 x4 rfl
  have hfin : decide (Fl4Spec.isFinalCap' (absCap (.Endpoint e b x1 x2 x3 x4)) σ) = true := by
    simpa [FinWork, isFrame] using hw
  rw [hfin]
  obtain ⟨σ', hmem⟩ := hEx s σ G sl _ ⟨e, b, x1, x2, x3, x4, rfl⟩ hDS hA hc (of_decide_eq_true hfin)
  refine WP.spec_mono (P1.fin_cap_ep.slots (ar := arI) s a e b x1 x2 x3 x4 true false hB hH) ?_
  rintro ⟨⟨r1, r2⟩, s', a'⟩ ⟨e', -, -, hW⟩
  simp only [Prod.mk.injEq] at e'
  obtain ⟨rfl, rfl⟩ := e'
  exact finWork_post_same (L := L) hDS hA hc rfl (slotsSame_of_capw hP hSC hW) hmem
    (finEp_nkc _ _ _ true σ _ hmem)

/-- **The thread case**: the remainder is the thread's zombie of six slots. -/
theorem finWorkAt_thread (th : TypedHeap) (hP : Placed th) (hAT : P0.ArchTotal arI)
    (hP1 : ThreadP1Hyp (L := L) th) (hEx : SpecFinOut (L := L) FinThreadK th) :
    FinWorkAt (L := L) arI FinThreadK th := by
  intro s a σ G sl c hk hDS hA hc hfk hw
  obtain ⟨p, rfl⟩ := hk
  obtain ⟨X, hB, hSC, hO⟩ := hP1 s σ G sl _ hDS hA hc hfk
  obtain ⟨hp, hna, hidle, hv0⟩ := hO p rfl
  have hfin : decide (Fl4Spec.isFinalCap' (absCap (.Thread p)) σ) = true := by
    simpa [FinWork, isFrame] using hw
  rw [hfin]
  obtain ⟨σ', hmem⟩ := hEx s σ G sl _ ⟨p, rfl⟩ hDS hA hc (of_decide_eq_true hfin)
  refine WP.spec_mono (P1.fin_cap_thread.slots hAT s a p true false hB hp hna hidle hv0) ?_
  rintro ⟨⟨r1, r2⟩, s', a'⟩ ⟨e, -, -, hW⟩
  simp only [Prod.mk.injEq, if_true] at e
  obtain ⟨rfl, rfl⟩ := e
  exact finWork_post_same (L := L) hDS hA hc rfl (slotsSame_of_capw hP hSC hW) hmem
    (finThread_nkc _ true σ _ hmem)

/-- **The scheduling-context case.** -/
theorem finWorkAt_sc (th : TypedHeap) (hP : Placed th) (hAT : P0.ArchTotal arI)
    (hP1 : ScP1Hyp (L := L) th) (hEx : SpecFinOut (L := L) FinScK th) : FinWorkAt (L := L) arI FinScK th := by
  intro s a σ G sl c hk hDS hA hc hfk hw
  obtain ⟨p, x, rfl⟩ := hk
  obtain ⟨X, hB, hSC, hO⟩ := hP1 s σ G sl _ hDS hA hc hfk
  obtain ⟨hp, hp0, hna, hidle⟩ := hO p x rfl
  have hfin : decide (Fl4Spec.isFinalCap' (absCap (.SchedContext p x)) σ) = true := by
    simpa [FinWork, isFrame] using hw
  rw [hfin]
  obtain ⟨σ', hmem⟩ := hEx s σ G sl _ ⟨p, x, rfl⟩ hDS hA hc (of_decide_eq_true hfin)
  refine WP.spec_mono (P1.fin_cap_sc.slots hAT s a p x true false hB hp hp0 hna hidle) ?_
  rintro ⟨⟨r1, r2⟩, s', a'⟩ ⟨e, -, -, hW⟩
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact finWork_post_same (L := L) hDS hA hc rfl (slotsSame_of_capw hP hSC hW) hmem
    (finSc_nkc _ _ true σ _ hmem)

end

end

end Fl4Proofs.P3
