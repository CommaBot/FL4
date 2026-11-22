/-
P3 (issue #16, sd7; KENTRY-PLAN g7a-4 (2)): **the arch, MakePool and untyped
performs keep `SI N t`** (sg1's SpecInvSgD for the idle vtable slot; spec side only).

* `IVS t σ := IVV t (uV σ)` and its leaves `ivk_setCap` / `ivk_capInsert` /
  `ivk_createCap` (off the vtable slot), `ivk_deleteObjects` (objects only removed),
  `ivk_retype` (new objects hold null caps only: ut8's `default_null`).
* Every slot these performs write a non-null cap into holds an arch / untyped cap
  (`notIV_of_held`), is a lookup destination, or lies in an object a cap covers
  (`notIV_of_cov`; the decode facts are sg1's / ut8's: `ArchSlN`, `MpOKN`, `UtGapOK`).
-/
import Fl4Proofs.P3.SpecInvSiC
open Classical

namespace Fl4Proofs.P3.SInvIV
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvG

noncomputable section

set_option maxHeartbeats 1000000

variable {N : Irq → ObjRef} {t : ObjRef}

/-- `IVV` on a state. -/
abbrev IVS (t : ObjRef) (σ : State Unit) : Prop := IVV t (uV σ)

/-! ## Leaves -/

theorem ivk_of_uk {α : Type} {m : NonDet (State Unit) α} (h : ∀ v, UK v m) : IK (IVS t) m :=
  ik_of_uk (fun _ _ e hI => by show IVV t _; rw [e]; exact hI) h

theorem ivke_of_uk {ε α : Type} {m : NonDetE (State Unit) ε α} (h : ∀ v, UKE v m) : IKE (IVS t) m := ivk_of_uk h

theorem ivk_setCap {c : Cap} {sl : CslotPtr} (h : NotIV t sl ∨ c = .nullCap) : IK (IVS t) (setCap (Z := Unit) c sl) :=
  fun σ hσ y hy => iv_setCap c sl σ ⟨hσ, h⟩ y hy

theorem ivk_capInsert {c : Cap} {src dest : CslotPtr} (h : NotIV t dest ∨ c = .nullCap) :
    IK (IVS t) (capInsert (Z := Unit) c src dest) :=
  fun σ hσ y hy => iv_capInsert c src dest σ ⟨hσ, h⟩ y hy

theorem ivk_deleteObjects (p : Word) (b : Nat) : IK (IVS t) (deleteObjects (Z := Unit) p b) := by
  intro σ hσ y hy
  obtain ⟨hk, -, -, -⟩ := deleteObjects_kheap hy
  intro a ha
  have ha' : capAt y.2 (t, tcbCnodeIndex 1) = some a := ha
  unfold capAt at ha'
  rw [hk] at ha'
  split_ifs at ha'
  exact hσ a ha'

theorem ivk_retype (bA : ApiObjectType → Nat → Nat) (rb : ObjRef) (n oB : Nat) (ty : ApiObjectType) (dev : Bool) :
    IK (IVS t) (retypeRegionWith (Z := Unit) bA rb n oB ty dev) := by
  intro σ hσ y hy
  obtain ⟨-, h5⟩ := retypeRegionWith_out hy
  rcases h5 with e | ⟨hty, e⟩
  · show IVV t (uV y.2); rw [e]; exact hσ
  · intro a ha
    have ha' : capAt y.2 (t, tcbCnodeIndex 1) = some a := ha
    rw [e] at ha'
    unfold capAt retKh at ha'
    try dsimp only at ha'
    split_ifs at ha' with hm
    · rw [default_null hty _ _ _ _ ha']
    · exact hσ a ha'

theorem ivk_retypeRegion (rb : ObjRef) (n oB : Nat) (ty : ApiObjectType) (dev : Bool) :
    IK (IVS t) (retypeRegion (Z := Unit) rb n oB ty dev) :=
  ivk_retype objBitsApi rb n oB ty dev

theorem ivk_createCap (ty : ApiObjectType) (sz : Nat) (src : CslotPtr) (dev : Bool) {d : CslotPtr} (p : ObjRef)
    (h : NotIV t d) : IK (IVS t) (createCap (Z := Unit) ty sz src dev (d, p)) := by
  show HV (IVV t) (IVV t) _
  unfold createCap
  refine hv_gets_bind (fun w => w.2.2.1 d) (fun _ => rfl) fun w1 hw1 => ?_
  refine hv_gets_bind (fun w => w.2.2.1) (fun _ => rfl) fun w2 hw2 => ?_
  subst hw2
  refine hv_bind (R := IVV t) (hv_mono (hv_setCdt _ _) fun w' e => by subst e; exact hw1) fun _ => ?_
  refine hv_bind (R := IVV t) (hv_doExtendedOp _) fun _ => ?_
  refine hv_bind (R := IVV t) (hv_pin fun w hw => hv_mono (hv_setOriginal _ _ w) fun w' e => by subst e; exact hw) fun _ => ?_
  exact hv_pre (iv_setCap _ _) fun w hw => ⟨hw, Or.inl h⟩

theorem ivk_mapMx_mem {α γ : Type} {g : α → NonDet (State Unit) γ} :
    ∀ xs : List α, (∀ a ∈ xs, IK (IVS t) (g a)) → IK (IVS t) (NonDet.mapMx g xs)
  | [], _ => ik_pure' _
  | a :: xs, h => ik_bind' (h a (by simp)) fun _ => ivk_mapMx_mem xs fun b hb => h b (by simp [hb])

macro "ivk_auto" : tactic => `(tactic| repeat' (first
  | (exact ivk_setCap (Or.inl (by assumption)))
  | (exact ivk_capInsert (Or.inl (by assumption)))
  | exact ivk_deleteObjects _ _ | exact ivk_retype _ _ _ _ _ _ | exact ivk_retypeRegion _ _ _ _ _
  | (refine ivk_of_uk fun _ => ?_; uk_leaf; done) | (refine ivke_of_uk fun _ => ?_; uk_leaf; done)
  | contradiction | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE)
  | (unfold NonDet.when) | (unfold NonDet.unless)))

/-! ## The arch performs (sg1's `ArchSlN` / `ArchWr`) -/

theorem ivk_performPageInvocationUnmap (a : ArchCap) {sl : CslotPtr} (h : NotIV t sl) :
    IK (IVS t) (performPageInvocationUnmap (Z := Unit) a sl) := by
  cases a with
  | pageCap dev p R mt sz mp => cases mp <;> (simp only [performPageInvocationUnmap]; ivk_auto)
  | _ => simp only [performPageInvocationUnmap]; ivk_auto

theorem ivk_performAsidPoolInvocation (iv : AsidPoolInvocation) :
    IK (IVS t) (performAsidPoolInvocation (Z := Unit) iv) := by
  cases iv with
  | assign asid poolPtr ctSlot =>
    show HV (IVV t) (IVV t) _
    unfold performAsidPoolInvocation
    refine hv_getCap_bind fun w c hw hc => ?_
    split
    · rename_i b m
      refine hv_bind (hv_pre (iv_setCap _ _) fun w' e => e ▸ ⟨hw, Or.inl (notIV_of_held hw hc ?_)⟩)
        fun _ => hv_uk fun _ => uk_storeAsidPoolEntry _ _ _
      intro e; cases e
    · intro σ _ y hy; exact hy.elim

macro "ivka_auto" : tactic => `(tactic| repeat' (first
  | (exact ivk_performPageInvocationUnmap _ (by assumption))
  | exact ivk_performAsidPoolInvocation _
  | (exact ivk_setCap (Or.inl (by assumption)))
  | (exact ivk_capInsert (Or.inl (by assumption)))
  | (refine ivk_of_uk fun _ => ?_; uk_leaf; done) | (refine ivke_of_uk fun _ => ?_; uk_leaf; done)
  | contradiction | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE)
  | (unfold NonDet.when) | (unfold NonDet.unless) | split))

set_option maxHeartbeats 4000000 in
theorem ivk_archPerform (i : ArchInvocation) (hm : ∀ a, i ≠ .invokeASIDControl a)
    (hS : ∀ sl, ArchWr i sl → NotIV t sl) : IKE (IVS t) (archPerformInvocation (Z := Unit) i) := by
  cases i with
  | invokeASIDControl a => exact absurd rfl (hm a)
  | invokePageTable iv =>
    cases iv with
    | pageTableMap c sl _ _ _ =>
      have h := hS sl (by simp [ArchWr])
      simp only [archPerformInvocation, performPageTableInvocation]; ivka_auto
    | pageTableUnmap c sl =>
      cases c
      case archObjectCap a =>
        have h := hS sl (by simp [ArchWr])
        cases a <;> (simp only [archPerformInvocation, performPageTableInvocation]; ivka_auto)
      all_goals (simp only [archPerformInvocation, performPageTableInvocation]; ivka_auto)
  | invokePageDirectory iv =>
    cases iv with
    | pageDirectoryMap c sl _ _ _ =>
      have h := hS sl (by simp [ArchWr])
      simp only [archPerformInvocation, performPageDirectoryInvocation]; ivka_auto
    | pageDirectoryUnmap c sl =>
      cases c
      case archObjectCap a =>
        have h := hS sl (by simp [ArchWr])
        cases a <;> (simp only [archPerformInvocation, performPageDirectoryInvocation]; ivka_auto)
      all_goals (simp only [archPerformInvocation, performPageDirectoryInvocation]; ivka_auto)
  | invokePDPT iv =>
    cases iv with
    | pdptMap c sl _ _ _ =>
      have h := hS sl (by simp [ArchWr])
      simp only [archPerformInvocation, performPdptInvocation]; ivka_auto
    | pdptUnmap c sl =>
      cases c
      case archObjectCap a =>
        have h := hS sl (by simp [ArchWr])
        cases a <;> (simp only [archPerformInvocation, performPdptInvocation]; ivka_auto)
      all_goals (simp only [archPerformInvocation, performPdptInvocation]; ivka_auto)
  | invokePage iv =>
    cases iv with
    | pageMap c sl _ _ =>
      have h := hS sl (by simp [ArchWr])
      simp only [archPerformInvocation, performPageInvocation]; ivka_auto
    | pageUnmap a sl =>
      have h := hS sl (by simp [ArchWr])
      cases a <;> (simp only [archPerformInvocation, performPageInvocation]; ivka_auto)
    | pageGetAddr p => simp only [archPerformInvocation, performPageInvocation]; ivka_auto
  | invokeASIDPool iv => simp only [archPerformInvocation]; ivka_auto
  | invokeIOPort iv => simp only [archPerformInvocation]; exact ike_liftE (ivk_of_uk fun _ => uk_performIoPortInvocation iv)
  | invokeIOPortControl iv =>
    cases iv with
    | ioPortControlInvocation f l d src =>
      have h := hS d (by simp [ArchWr])
      simp only [archPerformInvocation, performIoportControlInvocation]; ivka_auto

theorem archWr_notIV {σ : State Unit} (hI : SI N t σ) (i : ArchInvocation) (hok : ArchSpecOKN (uV σ) i)
    (hsl : ArchSlN (uV σ) i) : ∀ sl, ArchWr i sl → NotIV t sl := by
  have hA : ∀ s a, (uV σ).2.1 s = some (.archObjectCap a) → NotIV t s := fun s a h =>
    notIV_of_held hI.2.2 h (by intro e; cases e)
  intro sl hw
  cases i with
  | invokePageTable iv =>
    cases iv with
    | pageTableMap c s _ _ _ => obtain ⟨a, ha⟩ := hsl; simp only [ArchWr] at hw; subst hw; exact hA _ _ ha
    | pageTableUnmap c s =>
      cases c <;> simp only [ArchWr] at hw
      subst hw; exact hA _ _ hok
  | invokePageDirectory iv =>
    cases iv with
    | pageDirectoryMap c s _ _ _ => obtain ⟨a, ha⟩ := hsl; simp only [ArchWr] at hw; subst hw; exact hA _ _ ha
    | pageDirectoryUnmap c s =>
      cases c <;> simp only [ArchWr] at hw
      subst hw; exact hA _ _ hok
  | invokePDPT iv =>
    cases iv with
    | pdptMap c s _ _ _ => obtain ⟨a, ha⟩ := hsl; simp only [ArchWr] at hw; subst hw; exact hA _ _ ha
    | pdptUnmap c s =>
      cases c <;> simp only [ArchWr] at hw
      subst hw; exact hA _ _ hok
  | invokePage iv =>
    cases iv with
    | pageMap c s _ _ => obtain ⟨a, ha⟩ := hsl; simp only [ArchWr] at hw; subst hw; exact hA _ _ ha
    | pageUnmap a s => simp only [ArchWr] at hw; subst hw; exact hA _ _ hok
    | pageGetAddr p => simp only [ArchWr] at hw
  | invokeIOPortControl iv =>
    cases iv with
    | ioPortControlInvocation f l d src =>
      simp only [ArchWr] at hw; subst hw; exact notIV_of_destRef hI.2.1 hok.2
  | _ => simp only [ArchWr] at hw

theorem ivk_deriveSubframe (iv : Fl4SubframeInvocation) (h : ∀ d ∈ iv.dests, NotIV t d) :
    IK (IVS t) (performDeriveSubframe (Z := Unit) iv) := by
  unfold performDeriveSubframe
  exact ivk_mapMx_mem _ fun x hx => ivk_capInsert (Or.inl (h x.2 (List.of_mem_zip hx).2))

/-- **Every arch invocation but `invokeASIDControl` keeps `SI N t`.** -/
theorem iw_fl4ArchPerform (ai : Fl4ArchInvocation) (hm : ∀ a, ai ≠ .spec (.invokeASIDControl a)) (σ : State Unit)
    (hI : SI N t σ) (hok : ArchOKN (uV σ) ai) (hsl : Fl4ArchSlN (uV σ) ai) :
    ∀ y ∈ ((fl4ArchPerformInvocation (Z := Unit) ai).run σ).1, SI N t y.2 := by
  intro y hy
  refine ⟨p3_fl4ArchPerform ai hm σ hI.1 hok y hy,
    (p3_fl4ArchPerform (N := fun _ => t) ai hm σ ⟨hI.1.1, hI.2.1⟩ hok y hy).2, ?_⟩
  cases ai with
  | spec i =>
    simp only [fl4ArchPerformInvocation] at hy
    exact ivk_archPerform i (fun a e => hm a (by rw [e])) (archWr_notIV hI i hok hsl) σ hI.2.2 y hy
  | deriveSubframe iv =>
    simp only [fl4ArchPerformInvocation] at hy
    obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
    obtain ⟨p, r, mt, m, off, hsrc, hbase, hlen, s1, ptr, bits, g, hs1, hd⟩ := hok
    refine (ik_bind (ivk_deriveSubframe iv fun d hdm => ?_) fun _ => ivk_of_uk fun _ => by uk_auto) σ hI.2.2 x hx
    refine notIV_of_cov hI.2.1 hs1 ?_
    rw [(hd d hdm).1]
    simp [covR, capRng, objRefs]
  | _ => exact (ivke_of_uk fun _ => by simp only [fl4ArchPerformInvocation]; uk_auto) σ hI.2.2 y hy

/-! ## MakePool -/

theorem ivk_makePool (frame : ObjRef) {slot parent : CslotPtr} (base : Asid) (hp : NotIV t parent)
    (hs : NotIV t slot) :
    IK (IVS t) (performAsidControlInvocation (Z := Unit) (.makePool frame slot parent base)) := by
  unfold performAsidControlInvocation
  repeat' (first
    | exact ivk_setCap (Or.inl hp) | exact ivk_capInsert (Or.inl hs)
    | exact ivk_deleteObjects _ _ | exact ivk_retypeRegion _ _ _ _ _
    | (refine ivk_of_uk fun _ => ?_; uk_leaf; done)
    | ik_step0 | ik_unfold)

/-- **MakePool keeps `SI N t`.** -/
theorem iw_makePool {σ : State Unit} (hP : SI N t σ) {a : AsidControlInvocation} (hm : MpOKN (uV σ) a) :
    ∀ y ∈ (performAsidControlInvocation (Z := Unit) a σ).1, SI N t y.2 := by
  intro y hy
  refine ⟨p3_makePool hP.1 hm y hy, (p3_makePool (N := fun _ => t) ⟨hP.1.1, hP.2.1⟩ hm y hy).2, ?_⟩
  cases a with
  | makePool frame slot parent base =>
    obtain ⟨⟨dev, fi, hc, -⟩, hdr, -⟩ := hm
    have hp : NotIV t parent := notIV_of_held hP.2.2 hc (by intro e; cases e)
    exact ivk_makePool frame base hp (notIV_of_destRef hP.2.1 hdr) σ hP.2.2 y hy

/-! ## The untyped retype -/

set_option maxHeartbeats 4000000 in
theorem ivk_resetUntypedCap {s : CslotPtr} (hs : NotIV t s) : IKE (IVS t) (resetUntypedCap (Z := Unit) s) := by
  intro σ hσ y hy
  unfold resetUntypedCap at hy
  obtain ⟨x, hx, hy⟩ := run_liftE_bind_mem hy
  obtain ⟨cap, s0⟩ := x
  obtain ⟨hs0, -⟩ := getCap_capAt hx
  simp only at hs0; rw [hs0] at hy
  replace hy := run_returnOk_bind_mem hy
  replace hy := run_returnOk_bind_mem hy
  dsimp only at hy
  split at hy
  · rw [Set.mem_singleton_iff.1 hy]; exact hσ
  · obtain ⟨z, hz, hy⟩ := run_liftE_bind_mem hy
    have hz0 : IVS t z.2 := ivk_deleteObjects _ _ σ hσ z hz
    refine (?_ : IKE (IVS t) _) z.2 hz0 y hy
    repeat' (first
      | (exact ivk_setCap (Or.inl hs))
      | (exact ik_doMachineOp (fun _ _ h => h) _)
      | (exact ivke_of_uk fun _ => uk_preemptionPoint)
      | (exact ivk_of_uk fun _ => uk_archPostResetUntyped _ _)
      | (refine ike_mapMEx_mem _ fun _ _ => ?_)
      | ik_step0 | (unfold NonDet.unless) | (unfold NonDetE.whenE))

theorem ivk_invokeUntyped {s : CslotPtr} (reset : Bool) (base rb : ObjRef) (ty : ApiObjectType) (sz : Nat)
    {slots : List CslotPtr} (dev : Bool) (hs : NotIV t s) (hd : ∀ d ∈ slots, NotIV t d) :
    IKE (IVS t) (fl4InvokeUntyped (Z := Unit) (.retype s reset base rb ty sz slots dev)) := by
  simp only [invokeUntypedWith]
  refine ike_bind ?_ fun _ => ike_liftE ?_
  · unfold NonDetE.whenE
    split
    · exact ivk_resetUntypedCap hs
    · exact ike_returnOk _
  · repeat' (first
      | (refine ivk_mapMx_mem _ fun x hx => ?_; obtain ⟨d, p⟩ := x;
         exact ivk_createCap _ _ _ _ p (hd d (List.of_mem_zip hx).1))
      | exact ivk_setCap (Or.inl hs)
      | exact ivk_retype _ _ _ _ _ _
      | (exact ivk_of_uk fun _ => uk_initArchObjects _ _ _ _ _ _)
      | (refine ivk_of_uk fun _ => ?_; uk_leaf; done)
      | ik_step0 | ik_unfold)

/-- **`invoke_untyped` keeps `SI N t`** from the decode's facts. -/
theorem iw_invokeUntyped (ui : UntypedInvocation) (σ : State Unit) (hP : SI N t σ) (hok : UtGapOK (uV σ) ui) :
    ∀ y ∈ (ExceptT.run (fl4InvokeUntyped (Z := Unit) ui) σ).1, SI N t y.2 := by
  intro y hy
  refine ⟨p3_invokeUntyped ui σ hP.1 hok y hy, (p3_invokeUntyped (N := fun _ => t) ui σ ⟨hP.1.1, hP.2.1⟩ hok y hy).2, ?_⟩
  obtain ⟨h1, -, h3⟩ := hok
  obtain ⟨s, reset, base, rb, ty, sz, slots, dev⟩ := ui
  obtain ⟨bits, fi, hc, -⟩ := h1
  obtain ⟨-, s1, nc, off, win, hs1, hcn, -, he⟩ := h3
  have hsN : NotIV t s := notIV_of_held hP.2.2 hc (by intro e; cases e)
  have hdN : ∀ d ∈ slots, NotIV t d := by
    intro d hd
    rw [he] at hd
    obtain ⟨cref, -, rfl⟩ := List.mem_map.1 hd
    cases nc <;> simp [isCnodeCap] at hcn
    exact notIV_of_cov hP.2.1 hs1 (by simp [objRefOf, covR, capRng, objRefs])
  exact ivk_invokeUntyped reset base rb ty sz dev hsN hdN σ hP.2.2 y hy

end

end Fl4Proofs.P3.SInvIV
