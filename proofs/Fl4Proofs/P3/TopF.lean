/-
P3 (DESIGN.md §9): **the top-level posts with the frame invariant**
(`Vs.FrameInv`, VSpace's: every MDB cap naming a page of a large frame's
window is a frame cap in its chain; DeriveSubframe needs it).

`TopPostF` is `TopPost` with `FrameInv` after the invocation (for the same
ghost as `CRel` and `FinInv`), `DecOKF` its statement for one cap,
`TopPostDF` / `DecOKDF` the same with the domain schedule (`DomRel`).
`decode_invocation_refinesF` / `_refinesDF` are the dispatch from one
statement per cap; `TopPost` and `DecOK` follow (`TopPostF.top`).
-/
import Fl4Proofs.P3.DecodeTopD
import Fl4Proofs.P3.VsFrameInv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`TopPost` with the frame invariant** after the invocation. -/
def TopPostF (σ : Fl4Spec.State Unit) (blk call don : Bool) (m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation)
    (s : S) (res : core.result.Result Unit error.Exc × S × A) : Prop :=
  (∃ e, res.1 = .Err e ∧ res.2.1 = s ∧ ∃ e', m.run σ = ({(.error e', σ)}, False) ∧ ErrRel e e') ∨
  (∃ inv, DecOut m σ inv ∧ ∃ σ1,
    Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
    ∃ y ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don inv).run σ1).1, ∃ th' G',
      ((res.1 = .Ok () ∧ ∃ rr, y.1 = .ok rr) ∨ (res.1 = .Err .Preempted ∧ y.1 = .error ())) ∧
      Placed th' ∧ CRel th' (L.mem res.2.1) y.2 G' ∧ FinInv th' (L.mem res.2.1) y.2 G' ∧
      Vs.FrameInv (L.mem res.2.1) G')

theorem TopPostF.top {σ : Fl4Spec.State Unit} {blk call don : Bool} {m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation}
    {s : S} {res : core.result.Result Unit error.Exc × S × A} (h : TopPostF (L := L) σ blk call don m s res) :
    TopPost (L := L) σ blk call don m s res := by
  rcases h with h | ⟨inv, h1, σ1, h2, y, hy, th', G', h3, h4, h5, h6, -⟩
  · exact Or.inl h
  · exact Or.inr ⟨inv, h1, σ1, h2, y, hy, th', G', h3, h4, h5, h6⟩

/-- The statement for one cap, with the frame invariant. -/
abbrev DecOKF (s : S) (ar : A) (σ : Fl4Spec.State Unit) (lbl length slot : U64) (c : capability.Cap)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (slbl : Fl4Spec.Data)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) : Prop :=
  syscall.decode_invocation st arI s ar lbl length slot c blk call don fp buf extra ⦃ res =>
    TopPostF (L := L) σ blk call don (specDec fp slbl args ci sl c excaps buffer) s res ⦄

theorem DecOKF.toDecOK {s : S} {ar : A} {σ : Fl4Spec.State Unit} {lbl length slot : U64} {c : capability.Cap}
    {blk call don fp : Bool} {buf : U64} {extra : Aeneas.Std.Array obj.Slot 3#usize} {slbl : Fl4Spec.Data}
    {args : List Fl4Spec.Data} {ci : Fl4Spec.CapRef} {sl : Fl4Spec.CslotPtr}
    {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)} {buffer : Option Fl4Spec.ObjRef}
    (h : DecOKF (L := L) arI s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer) :
    DecOK (L := L) arI s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer :=
  WP.spec_mono h (fun _ h => h.top)

/-- **`TopPostF` with the domain schedule.** -/
def TopPostDF (σ : Fl4Spec.State Unit) (blk call don : Bool) (m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation)
    (s : S) (res : core.result.Result Unit error.Exc × S × A) : Prop :=
  (∃ e, res.1 = .Err e ∧ res.2.1 = s ∧ ∃ e', m.run σ = ({(.error e', σ)}, False) ∧ ErrRel e e') ∨
  (∃ inv, DecOut m σ inv ∧ ∃ σ1,
    Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
    ∃ y ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don inv).run σ1).1, ∃ th' G',
      ((res.1 = .Ok () ∧ ∃ rr, y.1 = .ok rr) ∨ (res.1 = .Err .Preempted ∧ y.1 = .error ())) ∧
      Placed th' ∧ CRel th' (L.mem res.2.1) y.2 G' ∧ FinInv th' (L.mem res.2.1) y.2 G' ∧
      DomRel (L.mem res.2.1) (L.ksb res.2.1) y.2 ∧ Vs.FrameInv (L.mem res.2.1) G')

theorem TopPostDF.toD {σ : Fl4Spec.State Unit} {blk call don : Bool} {m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation}
    {s : S} {res : core.result.Result Unit error.Exc × S × A} (h : TopPostDF (L := L) σ blk call don m s res) :
    TopPostD (L := L) σ blk call don m s res := by
  rcases h with h | ⟨inv, h1, σ1, h2, y, hy, th', G', h3, h4, h5, h6, h7, -⟩
  · exact Or.inl h
  · exact Or.inr ⟨inv, h1, σ1, h2, y, hy, th', G', h3, h4, h5, h6, h7⟩

/-- The statement for one cap, with the domain schedule and the frame
invariant. -/
abbrev DecOKDF (s : S) (ar : A) (σ : Fl4Spec.State Unit) (lbl length slot : U64) (c : capability.Cap)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (slbl : Fl4Spec.Data)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) : Prop :=
  syscall.decode_invocation st arI s ar lbl length slot c blk call don fp buf extra ⦃ res =>
    TopPostDF (L := L) σ blk call don (specDec fp slbl args ci sl c excaps buffer) s res ⦄

/-- **`DecOKF` with the domain schedule**, from the cap's `DomFrame`. -/
theorem DecOKF.withDom {s : S} {ar : A} {σ : Fl4Spec.State Unit} {lbl length slot : U64} {c : capability.Cap}
    {blk call don fp : Bool} {buf : U64} {extra : Aeneas.Std.Array obj.Slot 3#usize} {slbl : Fl4Spec.Data}
    {args : List Fl4Spec.Data} {ci : Fl4Spec.CapRef} {sl : Fl4Spec.CslotPtr}
    {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)} {buffer : Option Fl4Spec.ObjRef}
    (hDR : DomRel (L.mem s) (L.ksb s) σ)
    (h : DecOKF (L := L) arI s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer)
    (hF : DomFrame (L := L) arI s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer) :
    DecOKDF (L := L) arI s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer := by
  refine WP.spec_mono (WP.spec_and h hF.1) ?_
  rintro res ⟨hq, hkb, hw⟩
  rcases hq with hq | ⟨inv, h1, σ1, h2, y, hy, th', G', h3, h4, h5, h6, h7⟩
  · exact Or.inl hq
  · obtain ⟨hl, hst⟩ := hF.2 inv σ1 h1 h2 y hy
    refine Or.inr ⟨inv, h1, σ1, h2, y, hy, th', G', h3, h4, h5, h6, ?_, h7⟩
    rw [hkb]; exact hDR.frame hw hl hst

/-- The null and zombie caps: `InvalidCapability 0`, the state unchanged. -/
theorem decOKF_invalid (s : S) (ar : A) (σ : Fl4Spec.State Unit) (lbl length slot : U64) (cap : capability.Cap)
    (hc : cap = .Null ∨ ∃ p zt n, cap = .Zombie p zt n)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) :
    DecOKF (L := L) arI s ar σ lbl length slot cap blk call don fp buf extra slbl args ci sl excaps buffer := by
  rcases hc with rfl | ⟨p, zt, n, rfl⟩ <;>
  · unfold DecOKF syscall.decode_invocation
    rw [hct]; simp only [bind_ok]
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, _, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩

/-- **The dispatch of `decode_invocation` with the domain schedule and the
frame invariant**: from one statement per cap (`DecOKDF`), the null and
zombie caps aside. -/
theorem decode_invocation_refinesDF (s : S) (ar : A) (σ : Fl4Spec.State Unit) (lbl length slot : U64)
    (cap : capability.Cap) (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef)
    (hK : ∀ c, cap = c → (∀ p zt n, c ≠ .Zombie p zt n) → c ≠ .Null →
      DecOKDF (L := L) arI s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer) :
    DecOKDF (L := L) arI s ar σ lbl length slot cap blk call don fp buf extra slbl args ci sl excaps buffer := by
  by_cases hn : cap = .Null
  · subst hn
    unfold DecOKDF syscall.decode_invocation
    rw [hct]; simp only [bind_ok]
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, _, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩
  by_cases hz : ∃ p zt n, cap = .Zombie p zt n
  · obtain ⟨p, zt, n, rfl⟩ := hz
    unfold DecOKDF syscall.decode_invocation
    rw [hct]; simp only [bind_ok]
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, _, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩
  exact hK cap rfl (fun p zt n e => hz ⟨p, zt, n, e⟩) hn

/-- **The frame invariant across a step keeping every slot word** (the
ghost unchanged). -/
theorem FrameInv.of_same {th : TypedHeap} {m m' : U64 → U64} {G : MdbGhost} (hM : MdbLinks th m G)
    (hF : Vs.FrameInv m G) (hS : SlotsSame th m m') : Vs.FrameInv m' G :=
  hF.of_caps (fun z hz => hS.capV ((hM.members z).1 hz).1)

end

end

end Fl4Proofs.P3
