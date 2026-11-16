/-
P3 (DESIGN.md §9), CSpace: **the CNode cap's domain-schedule frame**
(`DomFrame`).

* `dk_spec_cnode`: the spec half: a CNode cap's decode gives only CNode
  invocations (`okAll_specDec_cnodeK`), and every CNode invocation keeps
  `domain_list` and `domain_start_index` (`dke_invokeCnode`, DomRecDel:
  deletions and revocations by `rec_del`'s and `cap_revoke`'s pre-fixed
  points).
* `CnodeDomHyp`: FL4's `cnode::decode` keeps the kernel-global base and the
  five domain-schedule words; `CnodeDecFootP1`, the same in P1's shape (a
  `Foot` in `KW`, `KW` apart from the domain schedule): `cnodeDomHyp_of_foot`.
* `domFrame_cnode`: the CNode cap's `DomFrame`.
-/
import Fl4Proofs.P3.TcbDom
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Spec

noncomputable section

/-- The invocations of a CNode cap. -/
def CnodeInvK (i : Fl4Invocation) : Prop := ∃ c, i = .invokeCNode c

/-- **A CNode cap's decode gives only CNode invocations.** -/
theorem okAll_specDec_cnodeK (fp : Bool) (slbl : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr)
    (p r gs g : U64) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    OkAll CnodeInvK (specDec fp slbl args ci sl (.CNode p r gs g) excaps buffer) := by
  unfold specDec
  show OkAll CnodeInvK (fl4DecodeInvocation (Z := Unit) fp slbl args ci sl
    (.cnodeCap p.bv r.val (bitsOf g.val gs.val)) excaps buffer)
  unfold fl4DecodeInvocation
  dsimp only
  exact okAll_ite (fun _ => okAll_throw) (fun _ => okAll_liftME (okAll_true _) fun a _ => ⟨a, rfl⟩)

theorem dke_fl4PerformCnode (blk call don : Bool) (i : CnodeInvocation) :
    Vs.DKE (fl4PerformInvocation (Z := Unit) blk call don (.invokeCNode i)) := by
  show Vs.DKE (do invokeCnode (Z := Unit) i; NonDetE.returnOk [])
  exact Vs.dke_bind (Vs.dke_invokeCnode i) fun _ => Vs.dke_returnOk _

/-- **The spec half of the CNode cap's `DomFrame`.** -/
theorem dk_spec_cnode {fp : Bool} {slbl : Data} {args : List Data} {ci : CapRef} {sl : CslotPtr}
    {p r gs g : U64} {excaps : List (Cap × CslotPtr)} {buffer : Option ObjRef} {blk call don : Bool}
    {σ : State Unit} {tcb : Tcb} (hkt : σ.kheap σ.curThread = some (.tcb tcb)) :
    ∀ inv σ1, DecOut (specDec fp slbl args ci sl (.CNode p r gs g) excaps buffer) σ inv →
      setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
      ∀ y ∈ ((fl4PerformInvocation (Z := Unit) blk call don inv).run σ1).1,
        y.2.domainList = σ.domainList ∧ y.2.domainStartIndex = σ.domainStartIndex := by
  intro inv σ1 hd he y hy
  have h1 := setThreadState_dom hkt he
  obtain ⟨c, rfl⟩ := hd.okAll (okAll_specDec_cnodeK fp slbl args ci sl p r gs g excaps buffer)
  have h2 := dke_fl4PerformCnode blk call don c σ1 y hy
  exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **FL4's `cnode::decode` keeps the domain schedule's words** (and the
kernel-global base). -/
def CnodeDomHyp (s : S) (ar : A) (lbl length : U64) (c : capability.Cap) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) : Prop :=
  cnode.decode st arI s ar lbl length c buf extra ⦃ r => L.ksb r.2.1 = L.ksb s ∧
    ∀ o ∈ domOffs, L.mem r.2.1 (ksW (L.ksb s) o) = L.mem s (ksW (L.ksb s) o) ⦄

/-- **`CnodeDomHyp` in P1's shape**: `cnode::decode` writes in `KW` of P1's
sets (`Foot`), `KW` lying apart from the domain schedule. -/
def CnodeDecFootP1 (s : S) (ar : A) (lbl length : U64) (c : capability.Cap) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) : Prop :=
  ∃ (T Cs Sg Scs : Set U64) (Z : U64 → Nat) (H : P1.Heap),
    cnode.decode st arI s ar lbl length c buf extra ⦃ r => P1.Foot st T Cs Sg Scs Z (P1.EH H) s r.2.1 ⦄ ∧
    KWDom (L := L) T Cs Sg Scs Z (P1.EH H) s

theorem cnodeDomHyp_of_foot {s : S} {ar : A} {lbl length : U64} {c : capability.Cap} {buf : U64}
    {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64) (hka : (L.ksb s).val % 8 = 0)
    (h : CnodeDecFootP1 (L := L) arI s ar lbl length c buf extra) :
    CnodeDomHyp (L := L) arI s ar lbl length c buf extra := by
  obtain ⟨T, Cs, Sg, Scs, Z, H, hf, hD⟩ := h
  refine WP.spec_mono hf fun r hr => ⟨hr.1, fun o ho => ?_⟩
  obtain ⟨h1, h2⟩ := Sched.domOffs_lt ho
  refine hr.mem_eq (ksW_al hkf hka h1 h2) fun hk => ?_
  have hv := ksW_val (kb := L.ksb s) (o := o) (by omega)
  rcases hD _ hk with e | e <;> rw [hv] at e <;> omega

/-- **The CNode cap's `DomFrame`**, from `CnodeDomHyp` (when not the first
phase) and `dk_spec_cnode`. -/
theorem domFrame_cnode (s : S) (ar : A) (σ : State Unit) (lbl length slot : U64) (p r gs g : U64)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ct : U64)
    (hct : sched.cur_thread st s = ok ct) {tcb : Tcb} (hkt : σ.kheap σ.curThread = some (.tcb tcb))
    (slbl : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr) (excaps : List (Cap × CslotPtr))
    (buffer : Option ObjRef)
    (hF : fp = false → CnodeDomHyp (L := L) arI s ar lbl length (.CNode p r gs g) buf extra) :
    DomFrame (L := L) arI s ar σ lbl length slot (.CNode p r gs g) blk call don fp buf extra slbl args ci sl
      excaps buffer := by
  refine ⟨?_, dk_spec_cnode hkt⟩
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
