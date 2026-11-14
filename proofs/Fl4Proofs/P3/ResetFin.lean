/-
P3 (DESIGN.md §9), untyped: **`FinInv` through `reset_untyped`**. The
spec's `reset_untyped_cap` removes only the objects of the untyped region
(`resetUntypedCap_mem`: every CNode and TCB afterwards was one before, and
the region holds none), so the restricted typed heap still types the spec's
CNodes and TCBs; the MDB is the same, the untyped cap's free index aside.
-/
import Fl4Proofs.P3.UntypedResetRefine
import Fl4Proofs.P3.FinSpec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
open Fl4Spec

/-- No object in the region `R`. -/
def REmpty (R : Set ObjRef) (σ : State Unit) : Prop := ∀ o ∈ R, σ.kheap o = none

theorem REmpty.sub {R : Set ObjRef} {σ σ' : State Unit} (h : REmpty R σ) (hK : KSub σ σ') : REmpty R σ' :=
  fun o ho => (hK o).2.2 (h o ho)

theorem nkse_mapMEx {α β : Type} {f : α → NonDetE (State Unit) Unit β} (hf : ∀ a, NKSE (f a)) :
    ∀ l, NKSE (NonDetE.mapMEx f l)
  | [] => nkse_pure _
  | a :: l => nkse_bind (hf a) (fun _ => nkse_mapMEx hf l)

theorem mem_bindE_inv {σ ε α β : Type} {m : NonDetE σ ε α} {f : α → NonDetE σ ε β} {s : σ}
    {x : Except ε β × σ} (hx : x ∈ ((m >>= f).run s).1) :
    ∃ z ∈ (m.run s).1, (∃ a, z.1 = .ok a ∧ x ∈ ((f a).run z.2).1) ∨ (∃ e, z.1 = .error e ∧ x = (.error e, z.2)) := by
  rw [ExceptT.run_bind] at hx
  obtain ⟨z, hz, hxz⟩ := hx
  refine ⟨z, hz, ?_⟩
  obtain ⟨r, s'⟩ := z
  cases r with
  | ok a => exact Or.inl ⟨a, rfl, hxz⟩
  | error e => exact Or.inr ⟨e, rfl, Set.mem_singleton_iff.1 hxz⟩

theorem deleteObjects_mem (base : ObjRef) (sz : Nat) {σ : State Unit} {y : Unit × State Unit}
    (hy : y ∈ (deleteObjects (Z := Unit) base sz σ).1) :
    KSub σ y.2 ∧ REmpty {x | base ≤ x ∧ x ≤ base + 2 ^ sz - 1} y.2 := by
  unfold deleteObjects at hy
  obtain ⟨z, hz, hy⟩ := hy
  have hk1 := nks_doMachineOp _ σ z hz
  rw [Set.mem_singleton_iff.1 hy]
  refine ⟨hk1.trans ?_, fun o ho => ?_⟩
  · intro o
    refine ⟨fun r cs h hw => ?_, fun t h => ?_, fun h => ?_⟩
    · simp only [detype] at h; split_ifs at h; exact ⟨cs, h, hw⟩
    · simp only [detype] at h; split_ifs at h; exact ⟨t, h⟩
    · simp only [detype]; split_ifs <;> simp_all
  · simp only [detype]; rw [if_pos ho]

theorem nks_clearMemory_step {dev : Bool} {base : ObjRef} {sz : Nat} {sl : CslotPtr} :
    NKSE (NonDetE.liftE (do
      NonDet.unless dev (doMachineOp (clearMemory base (2 ^ sz)))
      setCap (Z := Unit) (.untypedCap dev base sz 0) sl) : PMonad Unit Unit) := by
  refine nkse_liftE (nks_bind ?_ (fun _ => nks_setCap _ _))
  unfold NonDet.unless; split
  · exact nks_pure' _
  · exact nks_doMachineOp _

/-- **The spec's `reset_untyped_cap` removes only the region's objects.** -/
theorem resetUntypedCap_mem {sl : CslotPtr} {σ : State Unit} {dev : Bool} {base : ObjRef} {sz fi : Nat}
    (hg : getCap (Z := Unit) sl σ = ({(.untypedCap dev base sz fi, σ)}, False)) (hfi : fi ≠ 0)
    {y : Except Unit Unit × State Unit} (hy : y ∈ ((resetUntypedCap (Z := Unit) sl).run σ).1) :
    KSub σ y.2 ∧ REmpty {x | base ≤ x ∧ x ≤ base + 2 ^ sz - 1} y.2 := by
  unfold resetUntypedCap at hy
  rw [run_bind_ok (run_liftE hg)] at hy
  simp only [run_bind_ok (m := (NonDetE.returnOk _ : PMonad Unit _)) rfl, Fl4Spec.bitsOf, objRefOf, freeIndexOf,
    isDeviceUntypedCap, hfi, ↓reduceIte] at hy
  obtain ⟨z, hz, hcase⟩ := mem_bindE_inv hy
  -- the delete
  have hz' : ∃ w ∈ (deleteObjects (Z := Unit) base sz σ).1, z = (.ok w.1, w.2) := by
    unfold NonDetE.liftE at hz; rw [ExceptT.run_lift] at hz
    obtain ⟨w, hw, hzw⟩ := hz
    exact ⟨w, hw, Set.mem_singleton_iff.1 hzw⟩
  obtain ⟨w, hw, rfl⟩ := hz'
  obtain ⟨hK1, hE1⟩ := deleteObjects_mem base sz hw
  rcases hcase with ⟨a, -, hx⟩ | ⟨e, he, -⟩
  swap
  · cases he
  -- the rest keeps the CNodes and TCBs, and so the empty region
  have hK2 : KSub w.2 y.2 := by
    refine (?_ : NKSE _) w.2 y hx
    refine nkse_bind (nkse_returnOk _) (fun d => ?_)
    split
    · exact nkse_bind nks_clearMemory_step (fun _ => nkse_liftE (by unfold archPostResetUntyped; exact nks_pure _))
    · refine nkse_bind (nkse_mapMEx (fun i => ?_) _)
        (fun _ => nkse_liftE (by unfold archPostResetUntyped; exact nks_pure _))
      exact nkse_bind (nkse_liftE (nks_doMachineOp _)) (fun _ => nkse_bind (nkse_liftE (nks_setCap _ _))
        (fun _ => preemptionPoint_nks))
  exact ⟨hK1.trans hK2, hE1.sub hK2⟩

end

end

/-- **`FinInv` after a reset**, from an outcome of the spec's
`reset_untyped_cap` (up to its heap) and FL4's caps: the untyped cap like the
old one, the other caps of the MDB kept. -/
theorem reset_fin_of {th : TypedHeap} {mem mem' : U64 → U64} {σ σ' : Fl4Spec.State Unit} {G : MdbGhost}
    (hFI : FinInv th mem σ G) (hnd : G.chains.flatten.Nodup) {pp : U64} {idx : List Bool} {p sb fi : U64}
    {dev : Bool} (hsb : sb.val < 64) (hfit : p.val + 2 ^ sb.val ≤ 2 ^ 64)
    (hg : Fl4Spec.getCap (Z := Unit) (pp.bv, idx) σ = ({(.untypedCap dev p.bv sb.val fi.val, σ)}, False))
    (hfi0 : fi.val ≠ 0)
    (hy : ∃ y ∈ ((Fl4Spec.resetUntypedCap (Z := Unit) (pp.bv, idx)).run σ).1, y.2.kheap = σ'.kheap)
    (x : U64) (hx : CapSim (capV mem' x) (capV mem x))
    (hcap : ∀ z ∈ G.chains.flatten, z ≠ x → capV mem' z = capV mem z) :
    FinInv (restrictTh th p.val (p.val + 2 ^ sb.val)) mem' σ' G := by
  refine ⟨?_, hFI.fm.recap hnd x hx hcap⟩
  obtain ⟨y, hy, hk⟩ := hy
  obtain ⟨hKs, hEm⟩ := resetUntypedCap_mem hg hfi0 hy
  have hout : ∀ o : BitVec 64, (∃ k, y.2.kheap o = some k) →
      restrictTh th p.val (p.val + 2 ^ sb.val) ⟨o⟩ = th ⟨o⟩ := by
    rintro o ⟨k, hko⟩
    apply restrictTh_out
    rw [← regionSet_iff p ⟨o⟩ sb.val hsb hfit]
    intro ho; rw [hEm o ho] at hko; cases hko
  intro o
  refine ⟨fun r cs h hw => ?_, fun t h => ?_⟩
  · rw [← hk] at h
    rw [hout o ⟨_, h⟩]
    obtain ⟨cs0, h0, hw0⟩ := (hKs o).1 r cs h hw
    exact (hFI.kt o).1 r cs0 h0 hw0
  · rw [← hk] at h
    rw [hout o ⟨_, h⟩]
    obtain ⟨t0, h0⟩ := (hKs o).2.1 t h
    exact (hFI.kt o).2 t0 h0

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A' : Type} (arI : machine.Arch A')

/-- **`reset_untyped` keeps `FinInv`**: `reset_untyped_refines`, with
`FinInv` for the restricted typed heap and the spec's state of the outcome. -/
theorem reset_untyped_fin (th : TypedHeap) (s : S) (a : A') (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (hU : UtInv (L.mem s) G) (hFI : FinInv th (L.mem s) σ G)
    {pp : U64} {rs : Nat} (hpp : th pp = some (.cnode rs)) {idx : List Bool} (hidx : idx.length = rs)
    {p sb fi : U64} {dev : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi dev)) (hfi0 : fi.val ≠ 0)
    (hnd : ∀ y, ¬ Mdb.Desc G.par y (cslotAddr (pp.bv, idx)))
    (hpal : p.val % 2 ^ sb.val = 0) (hsb4 : 4 ≤ sb.val)
    (hN : NoStraddle th p.val (p.val + 2 ^ sb.val))
    (hns : ∀ a ∈ G.chains.flatten, a.val < p.val ∨ p.val + 2 ^ sb.val ≤ a.val)
    (hzero : ZeroRegion (L.mem s) (p.val + fi.val) (p.val + 2 ^ sb.val))
    (hrcb : Fl4Spec.resetChunkBits = 16) (hppS : PPFrame) {E : S → Prop} (hPP : PPHyp (L := L) arI th p sb E)
    (hEk : EKept (L := L) E p sb (cslotAddr (pp.bv, idx))) (hE : E s) :
    untyped.reset_untyped st arI s a (cslotAddr (pp.bv, idx)) ⦃ res =>
      ∃ σ' f, ((res.1 = .Ok () ∧ f = 0#u64 ∧
          NHas (Fl4Spec.resetUntypedCap (Z := Unit) (pp.bv, idx)).run σ (TopP (.ok ()) σ')) ∨
        (res.1 = .Err .Preempted ∧
          NHas (Fl4Spec.resetUntypedCap (Z := Unit) (pp.bv, idx)).run σ (TopP (.error ()) σ'))) ∧
        ResetRel (restrictTh th p.val (p.val + 2 ^ sb.val)) G (cslotAddr (pp.bv, idx)) p sb dev
          (L.mem res.2.1) σ' f ∧
        FinInv (restrictTh th p.val (p.val + 2 ^ sb.val)) (L.mem res.2.1) σ' G ⦄ := by
  have hsb : sb.val < 64 := capAt_untyped_inv hcap
  have hcv := capV_of_capAt hcap
  have hAs : AbsSlot th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hxm : cslotAddr (pp.bv, idx) ∈ G.chains.flatten := (hM.members _).2 ⟨hAs.isSlot, _, hcap, by simp⟩
  have hrx := hU.reg _ hxm (by rw [hcv]; exact physF_ut _ _ _ _)
  rw [hcv] at hrx
  obtain ⟨-, -, hfit⟩ := ut_range hsb hrx
  have hg : Fl4Spec.getCap (Z := Unit) (pp.bv, idx) σ = ({(.untypedCap dev p.bv sb.val fi.val, σ)}, False) := by
    obtain ⟨c, a, hc, hca, hg⟩ := hR.slot_cap (sl := (pp.bv, idx)) (p := pp) rfl (by simpa [hidx] using hpp)
    rw [hcap] at hc; have := eq_of_ok_eq hc; subst this
    rw [hg, hca.abs]; rfl
  refine WP.spec_mono (reset_untyped_refines arI th s a σ G hR hV hP hM hC hI hU hpp hidx hcap hfi0 hnd hpal hsb4
    hN hns hzero hrcb hppS hPP hEk hE) ?_
  rintro res ⟨-, σ', f, hcase, hRR, -, hcap', -⟩
  refine ⟨σ', f, hcase, hRR, reset_fin_of hFI hM.tree.nodup hsb hfit hg hfi0 ?_ (cslotAddr (pp.bv, idx))
    (by rw [hRR.cap, hcv]; exact CapSim.of_shape rfl rfl) (fun z hz hzx => hcap' z ((hRR.M.members z).1 hz).1 hzx)⟩
  rcases hcase with ⟨-, -, y, hy, -, hk⟩ | ⟨-, y, hy, -, hk⟩
  · exact ⟨y, hy, hk.1⟩
  · exact ⟨y, hy, hk.1⟩

end

end Fl4Proofs.P3
