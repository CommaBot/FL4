/-
P3 (issue #16, sd7; KENTRY-PLAN g7a-4 (2)): **the idle TCB's vtable slot as a
carried spec fact** (INV-PLAN §1.U3L D7), the sibling of sg1's `S N M` family
(SpecInvSgA), spec side only.

* **`IVV t w`**: the slot `(t, tcbCnodeIndex 1)` (the vtable of the TCB at `t`)
  holds no cap but the null cap. At the top `t` is the idle thread (l4v: the idle
  thread is created with null caps, `create_idle_thread`; no cap names it,
  `valid_global_refs`, so no TCB invocation reaches its slots).
* **`SIV N t w := P3V N w ∧ IrqOutV (fun _ => t) w ∧ IVV t w`** (`SI N t σ := SIV N t (uV σ)`):
  ut7/ut8's `P3 N`, the idle thread's range fact (sg1's `IdleOutV`), and the vtable
  slot. The first two conjuncts come from ut7/ut8's lemmas at `K = N` and
  `K = fun _ => t` (`iw_of`); only `IVV` needs new proofs.
* A slot written with a non-null cap is not the idle vtable (`NotIV t sl`): it holds a
  non-null cap (`notIV_of_held`, by `IVV`), it lies in an object a cap covers
  (`notIV_of_cov`, by the range fact: lookup destinations `notIV_of_destRef`, the TCB
  installs, whose inner `check_cap_at` finds the invoked thread cap in its slot).
* Deletion only nulls slots (sg1's `NulK`); `rec_del` as sg1's `no_recDel` (the
  reduce-zombie swap's slots: the zombie's own slot holds a non-null cap, the other
  lies in the zombie's object).
-/
import Fl4Proofs.P3.SpecInvSgE
open Classical

namespace Fl4Proofs.P3.SInvIV
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvG

noncomputable section

set_option maxHeartbeats 1000000

/-- **The vtable slot of the TCB at `t` holds the null cap** (if it holds anything). -/
def IVV (t : ObjRef) (w : UView) : Prop := ∀ a, w.2.1 (t, tcbCnodeIndex 1) = some a → a = .nullCap

/-- The slot is not `t`'s vtable slot. -/
def NotIV (t : ObjRef) (sl : CslotPtr) : Prop := sl ≠ (t, tcbCnodeIndex 1)

/-- **The carried family** (module docstring). -/
def SIV (N : Irq → ObjRef) (t : ObjRef) (w : UView) : Prop := P3V N w ∧ IrqOutV (fun _ => t) w ∧ IVV t w

abbrev SI (N : Irq → ObjRef) (t : ObjRef) (σ : State Unit) : Prop := SIV N t (uV σ)

section Basic
variable {N : Irq → ObjRef} {t : ObjRef}

theorem iv_nulK {w w' : UView} (h : IVV t w) (hk : NulK w w') : IVV t w' := by
  intro a ha
  rcases hk (t, tcbCnodeIndex 1) with e | e
  · rw [e] at ha; exact h a ha
  · rw [e] at ha; cases ha; rfl

theorem iv_vCap {w : UView} (h : IVV t w) {sl : CslotPtr} {c : Cap} (hs : NotIV t sl ∨ c = .nullCap) :
    IVV t (vCap sl c w) := by
  intro a ha
  rw [vCap_cap] at ha
  split_ifs at ha with e
  · cases ha
    rcases hs with hs | hs
    · exact absurd e.symm hs
    · exact hs
  · exact h a ha

theorem notIV_of_held {w : UView} (h : IVV t w) {sl : CslotPtr} {c : Cap} (hs : w.2.1 sl = some c)
    (hc : c ≠ .nullCap) : NotIV t sl := by
  intro e; subst e; exact hc (h c hs)

theorem notIV_of_cov {w : UView} (hO : IrqOutV (fun _ => t) w) {s sl : CslotPtr} {c : Cap} (hs : w.2.1 s = some c)
    (hr : sl.1 ∈ covR c) : NotIV t sl := by
  intro e; subst e; exact hO default s c hs hr

theorem notIV_of_destRef {w : UView} (hO : IrqOutV (fun _ => t) w) {d : CslotPtr} (hD : DestRefV w d) : NotIV t d := by
  obtain ⟨s1, c1, hs1, hr1, -, -⟩ := hD
  exact notIV_of_cov hO hs1 (capRng_sub_covR _ (sRefs_sub_capRng _ hr1))

/-- `IVV` across a step that only nulls slots. -/
theorem iv_of_nulK {α : Type} {m : NonDet (State Unit) α} (h : ∀ w, HV (· = w) (NulK w) m) :
    IK (fun σ => IVV t (uV σ)) m :=
  fun σ hσ y hy => iv_nulK hσ (h (uV σ) σ rfl y hy)

/-! ## The family -/

theorem iw_of {α : Type} {m : NonDet (State Unit) α} (h : ∀ K, IK (P3 K) m)
    (hn : ∀ σ, SI N t σ → ∀ y ∈ (m σ).1, IVV t (uV y.2)) : IK (SI N t) m :=
  fun σ hσ y hy => ⟨h N σ hσ.1 y hy, (h (fun _ => t) σ ⟨hσ.1.1, hσ.2.1⟩ y hy).2, hn σ hσ y hy⟩

theorem iw_of_uk {α : Type} {m : NonDet (State Unit) α} (h : ∀ v, UK v m) : IK (SI N t) m :=
  ik_of_uk (fun _ _ e hI => by show SIV N t _; rw [e]; exact hI) h

theorem iwe_of_uk {ε α : Type} {m : NonDetE (State Unit) ε α} (h : ∀ v, UKE v m) : IKE (SI N t) m := iw_of_uk h

theorem iw_of_view {σ σ' : State Unit} (h : uV σ' = uV σ) (hI : SI N t σ) : SI N t σ' := by
  show SIV N t (uV σ'); rw [h]; exact hI

theorem iw_capDeleteOne_iv (sl : CslotPtr) : IK (fun σ => IVV t (uV σ)) (capDeleteOne (Z := Unit) sl) :=
  iv_of_nulK (nulK_capDeleteOne sl)

theorem iw_capDeleteOne (sl : CslotPtr) : IK (SI N t) (capDeleteOne (Z := Unit) sl) :=
  iw_of (fun _ => p3_capDeleteOne sl) fun σ h y hy => iw_capDeleteOne_iv sl σ h.2.2 y hy

/-! ## `rec_del` -/

/-- The idle vtable facts kept by the deletion (no untyped invariant needed). -/
abbrev NI (t : ObjRef) (σ : State Unit) : Prop := IO (fun _ => t) σ ∧ IVV t (uV σ)

theorem ni_of_uk {α : Type} {m : NonDet (State Unit) α} (h : ∀ v, UK v m) : IK (NI t) m :=
  ik_of_uk (fun _ _ e hI => by show IrqOutV (fun _ => t) _ ∧ IVV t _; rw [e]; exact hI) h

theorem nie_of_uk {ε α : Type} {m : NonDetE (State Unit) ε α} (h : ∀ v, UKE v m) : IKE (NI t) m := ni_of_uk h

theorem ni_capDeleteOne (sl : CslotPtr) : IK (NI t) (capDeleteOne (Z := Unit) sl) :=
  fun σ h y hy => ⟨io_capDeleteOne sl σ h.1 y hy, iw_capDeleteOne_iv sl σ h.2 y hy⟩

theorem ni_emptySlot (s : CslotPtr) (info : Cap) : IK (NI t) (emptySlot (Z := Unit) s info) :=
  fun σ h y hy => ⟨io_emptySlot s info σ h.1 y hy, iv_of_nulK (nulK_emptySlot s info) σ h.2 y hy⟩

theorem ni_finaliseCap (c : Cap) (fin : Bool) : IK (NI t) (finaliseCap (Z := Unit) c fin) := by
  by_cases hirq : ∃ i, c = .irqHandlerCap i
  · obtain ⟨i, rfl⟩ := hirq
    simp only [finaliseCap, deletingIrqHandler, getIrqSlot]
    repeat' (first | exact ni_capDeleteOne _ | ik_step0)
  · exact ni_of_uk (uk_finaliseCap_nonIrq c (fun i e => hirq ⟨i, e⟩) fin)

/-- `cap_swap_for_delete` of two slots off the vtable. -/
theorem ni_capSwapForDelete {s1 s2 : CslotPtr} (h1 : NotIV t s1) (h2 : NotIV t s2) :
    IK (NI t) (capSwapForDelete (Z := Unit) s1 s2) := by
  intro σ hσ y hy
  refine ⟨io_capSwapForDelete s1 s2 σ hσ.1 y hy, ?_⟩
  have key : HV (· = uV σ) (fun w' => IVV t w') (capSwapForDelete (Z := Unit) s1 s2) := by
    unfold capSwapForDelete NonDet.when
    split
    · rename_i hne
      refine hv_getCap_bind fun w1 c1 hw _ => ?_
      subst hw
      refine hv_getCap_bind fun w' c2 hw' _ => ?_
      subst hw'
      refine hv_mono (capSwap_view hne c1 c2) fun w' e => ?_
      subst e
      refine iv_vCap (iv_vCap ?_ (Or.inl h1)) (Or.inl h2)
      intro a ha
      have e1 : sw s1 s2 (t, tcbCnodeIndex 1) = (t, tcbCnodeIndex 1) := by
        unfold sw; rw [if_neg (fun e => h1 e.symm), if_neg (fun e => h2 e.symm)]
      have ha' : (uV σ).2.1 (sw s1 s2 (t, tcbCnodeIndex 1)) = some a := ha
      rw [e1] at ha'
      exact hσ.2 a ha'
    · exact hv_mono (hv_uk fun _ => ik_pure' _) fun w' e => e ▸ hσ.2
  exact key σ rfl y hy

macro "ni0_auto" : tactic => `(tactic| repeat' (first
  | exact ni_emptySlot _ _
  | (refine ni_of_uk fun _ => ?_; uk_leaf; done) | (refine nie_of_uk fun _ => ?_; uk_leaf; done)
  | contradiction | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE)
  | (unfold NonDet.when) | (unfold NonDet.unless)))

/-- The deletion's call-dependent precondition: a reduce-zombie call's cap is in its slot. -/
def IPre (t : ObjRef) : RecDelCall → State Unit → Prop
  | .reduceZombieCall c s _, σ => NI t σ ∧ capAt σ s = some c
  | _, σ => NI t σ

theorem IPre.ni {k : RecDelCall} {σ : State Unit} (h : IPre t k σ) : NI t σ := by
  cases k with
  | reduceZombieCall => exact h.1
  | _ => exact h

/-- The remainder of a finalised cap written back into its slot. -/
theorem iv_fin_rem {w : UView} (h : IVV t w) {sl : CslotPtr} {cap : Cap} (hc : w.2.1 sl = some cap)
    {σ : State Unit} {x : (Cap × Cap) × State Unit} {fin : Bool} (hx : x ∈ (finaliseCap (Z := Unit) cap fin σ).1) :
    NotIV t sl ∨ x.1.1 = .nullCap := by
  by_cases hn : cap = .nullCap
  · right
    have e : x.1.1 = .nullCap := finaliseCap_null (by rw [hn]; rfl) fin σ x hx
    exact e
  · exact Or.inl (notIV_of_held h hc hn)

theorem ni_recDelF (f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap)))
    (hrec : ∀ k, HR (IPre t k) (fun _ => NI t) (f k)) (k : RecDelCall) :
    HR (IPre t k) (fun _ => NI t) (recDelF (Z := Unit) f k) := by
  have hfin : ∀ s e, IKE (ε := Unit) (NI t) (f (.finaliseSlotCall s e) : NonDetE (State Unit) Unit (Bool × Cap)) :=
    fun s e σ h y hy => hrec (.finaliseSlotCall s e) σ h y hy
  have hcte : ∀ s e, IKE (ε := Unit) (NI t) (f (.cTEDeleteCall s e) : NonDetE (State Unit) Unit (Bool × Cap)) :=
    fun s e σ h y hy => hrec (.cTEDeleteCall s e) σ h y hy
  cases k with
  | cTEDeleteCall s e =>
    intro σ hσ y hy
    replace hσ : NI t σ := hσ
    refine (show IKE (NI t) (recDelF (Z := Unit) f (.cTEDeleteCall s e)) by
      unfold recDelF withoutPreemption; ni0_auto
      all_goals first | exact hfin _ _ | exact hcte _ _) σ hσ y hy
  | finaliseSlotCall sl e =>
    intro σ hσ y hy
    replace hσ : NI t σ := hσ
    simp only [recDelF, withoutPreemption] at hy
    obtain ⟨z, hz, H⟩ := mem_bindE' hy
    obtain ⟨⟨cap, σ1⟩, hx, rfl⟩ := mem_liftE' hz
    obtain ⟨a, ha, hy1⟩ | ⟨er, her, -⟩ := H
    swap
    · cases her
    injection ha with ha'
    subst ha'
    obtain ⟨e1, hc⟩ := getCap_capAt hx
    simp only at e1 hc
    subst e1
    try dsimp only at hy1
    split at hy1
    · rw [mem_ret_ok hy1]; exact hσ
    · obtain ⟨z, hz, H⟩ := mem_bindE' hy1
      obtain ⟨⟨fin, σ2⟩, hx2, rfl⟩ := mem_liftE' hz
      obtain ⟨a, ha, hy2⟩ | ⟨er, her, -⟩ := H
      swap
      · cases her
      injection ha with ha'
      subst ha'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 hx2)
      try dsimp only at hy2
      obtain ⟨z, hz, H⟩ := mem_bindE' hy2
      obtain ⟨⟨rc, σ3⟩, hx3, rfl⟩ := mem_liftE' hz
      obtain ⟨a, ha, hy3⟩ | ⟨er, her, -⟩ := H
      swap
      · cases her
      injection ha with ha'
      subst ha'
      obtain ⟨rem, cl⟩ := rc
      have hO3 : NI t σ3 := ni_finaliseCap cap _ _ hσ _ hx3
      have hc3 : capAt σ3 sl = some cap := finaliseCap_keepAt hc _ _ hx3
      have hcov : covR rem ⊆ covR cap := finaliseCap_cov cap _ _ _ hx3
      have hrem : NotIV t sl ∨ rem = .nullCap := iv_fin_rem hσ.2 hc hx3
      have hO4 : NI t σ3 → IrqOutV (fun _ => t) (vCap sl rem (uV σ3)) ∧ IVV t (vCap sl rem (uV σ3)) := fun h =>
        ⟨irqOut_vCap h.1 (covBy_of hc3 hcov) sl, iv_vCap h.2 hrem⟩
      try dsimp only at hy3
      split at hy3
      · rw [mem_ret_ok hy3]; exact hO3
      · split at hy3
        · obtain ⟨z, hz, ⟨u, -, hy4⟩ | ⟨er, her, rfl⟩⟩ := mem_bindE' hy3
          · obtain ⟨⟨u', σ4⟩, hx4, rfl⟩ := mem_liftE' hz
            rw [mem_ret_ok hy4]
            have hv4 : uV σ4 = vCap sl rem (uV σ3) := hv_setCap rem sl (uV σ3) σ3 rfl _ hx4
            show IrqOutV (fun _ => t) (uV σ4) ∧ IVV t (uV σ4); rw [hv4]; exact hO4 hO3
          · obtain ⟨x, -, hx⟩ := mem_liftE' hz
            rw [hx] at her; cases her
        · obtain ⟨z, hz, H⟩ := mem_bindE' hy3
          obtain ⟨⟨u', σ4⟩, hx4, rfl⟩ := mem_liftE' hz
          obtain ⟨a, -, hy4⟩ | ⟨er, her, -⟩ := H
          swap
          · cases her
          have hv4 : uV σ4 = vCap sl rem (uV σ3) := hv_setCap rem sl (uV σ3) σ3 rfl _ hx4
          have hO5 : NI t σ4 := by show IrqOutV (fun _ => t) (uV σ4) ∧ IVV t (uV σ4); rw [hv4]; exact hO4 hO3
          have hc4 : capAt σ4 sl = some rem := by
            show (uV σ4).2.1 sl = some rem; rw [hv4, vCap_cap, if_pos rfl]
          obtain ⟨z, hz, H⟩ := mem_bindE' hy4
          have hI5 : NI t z.2 := hrec (.reduceZombieCall rem sl e) σ4 ⟨hO5, hc4⟩ z hz
          obtain ⟨a, -, hy5⟩ | ⟨er, -, rfl⟩ := H
          · obtain ⟨z6, hz6, H⟩ := mem_bindE' hy5
            have hv6 : uV z6.2 = uV z.2 := uk_preemptionPoint (uvw := uV z.2) z.2 rfl z6 hz6
            have hI6 : NI t z6.2 := by show IrqOutV (fun _ => t) (uV z6.2) ∧ IVV t (uV z6.2); rw [hv6]; exact hI5
            obtain ⟨a, -, hy6⟩ | ⟨er, -, rfl⟩ := H
            · exact hrec (.finaliseSlotCall sl e) z6.2 hI6 y hy6
            · exact hI6
          · exact hI5
  | reduceZombieCall c s e =>
    cases c with
    | zombie ptr bits n =>
      cases n with
      | zero => intro σ _ y hy; exact (rz_fail rfl hy).elim
      | succ n =>
        cases e with
        | false =>
          intro σ hσ y hy
          obtain ⟨hσ, hcs⟩ := hσ
          have h1 : NotIV t (firstCslotOf (.zombie ptr bits (n + 1))) :=
            notIV_of_cov (w := uV σ) hσ.1 hcs (by simp [firstCslotOf, covR, capRng, objRefs])
          have h2 : NotIV t s := notIV_of_held (w := uV σ) hσ.2 hcs (fun e => by cases e)
          refine (show IKE (NI t) (recDelF (Z := Unit) f (.reduceZombieCall (.zombie ptr bits (n + 1)) s false)) by
            simp only [recDelF, withoutPreemption]
            repeat' (first | exact ni_capSwapForDelete h1 h2 | ik_step0 | ik_unfold)) σ hσ y hy
        | true =>
          intro σ hσ y hy
          replace hσ := hσ.1
          simp only [recDelF, withoutPreemption] at hy
          obtain ⟨z, hz, ⟨es, hes, hy⟩ | ⟨er, her, rfl⟩⟩ := mem_bindE' hy
          · obtain rfl := mem_ret_ok hz
            cases hes
            try dsimp only at hy
            obtain ⟨z, hz, H⟩ := mem_bindE' hy
            have hp : NI t z.2 := hrec (.cTEDeleteCall _ _) σ hσ z hz
            rcases H with ⟨a, ha, hy⟩ | ⟨er, -, rfl⟩
            swap
            · exact hp
            obtain ⟨z2, hz2, ⟨nc, hnc, hy⟩ | ⟨er, her, rfl⟩⟩ := mem_bindE' hy
            swap
            · obtain ⟨x, -, hx⟩ := mem_liftE' hz2
              rw [hx] at her; cases her
            obtain ⟨⟨nc', σ5⟩, hx5, rfl⟩ := mem_liftE' hz2
            cases hnc
            obtain ⟨e5, hc5⟩ := getCap_capAt hx5
            simp only at e5 hc5
            subst e5
            try dsimp only at hy
            split at hy
            · rename_i hnz
              subst hnz
              obtain ⟨z3, hz3, ⟨u, -, hy⟩ | ⟨er, her, rfl⟩⟩ := mem_bindE' hy
              · obtain ⟨x, hx, rfl⟩ := mem_liftE' hz3
                rw [mem_ret_ok hy]
                have hv := hv_setCap (.zombie ptr bits n) s (uV z.2) z.2 rfl _ hx
                show IrqOutV (fun _ => t) (uV x.2) ∧ IVV t (uV x.2)
                rw [hv]
                exact ⟨irqOut_vCap hp.1 (covBy_of hc5 (fun q hq => by simpa [covR, capRng, objRefs] using hq)) s,
                  iv_vCap hp.2 (Or.inl (notIV_of_held (w := uV z.2) hp.2 hc5 (fun e => by cases e)))⟩
              · obtain ⟨x, -, hx⟩ := mem_liftE' hz3
                rw [hx] at her; cases her
            · obtain ⟨z3, hz3, ⟨u, -, hy⟩ | ⟨er, her, rfl⟩⟩ := mem_bindE' hy
              · obtain ⟨x, hx, rfl⟩ := mem_liftE' hz3
                obtain ⟨-, rfl⟩ := hx
                rw [mem_ret_ok hy]
                exact hp
              · obtain ⟨x, -, hx⟩ := mem_liftE' hz3
                rw [hx] at her; cases her
          · obtain rfl := mem_ret_ok hz; cases her
    | _ => intro σ _ y hy; exact (rz_fail rfl hy).elim

/-- **`rec_del` keeps the IRQ-node facts** (no premise beyond the call's own precondition). -/
theorem ni_recDel (k : RecDelCall) : HR (IPre t k) (fun _ => NI t) (recDel (Z := Unit) k) := by
  unfold recDel
  exact hr_lfp (IPre t) (fun _ _ => NI t) (fun f hf k => ni_recDelF f hf k) k

theorem iw_recDel_cte (s : CslotPtr) (e : Bool) : IKE (SI N t) (recDel (Z := Unit) (.cTEDeleteCall s e)) :=
  iw_of (fun _ => p3_recDel_cte s e) fun σ h y hy => (ni_recDel (.cTEDeleteCall s e) σ ⟨h.2.1, h.2.2⟩ y hy).2

theorem iw_recDel_fin (s : CslotPtr) (e : Bool) : IKE (SI N t) (recDel (Z := Unit) (.finaliseSlotCall s e)) :=
  iw_of (fun _ => p3_recDel_fin s e) fun σ h y hy => (ni_recDel (.finaliseSlotCall s e) σ ⟨h.2.1, h.2.2⟩ y hy).2

theorem iw_capDelete (slot : CslotPtr) : IKE (SI N t) (capDelete (Z := Unit) slot) := by
  unfold capDelete
  exact ike_bind (iw_recDel_cte _ _) fun _ => ike_returnOk _

/-! ## Inserts -/

/-- **`cap_insert` keeps `NOV`** when the destination is no node slot or the cap is null /
a notification cap (the source is rewritten only when it holds an untyped cap). -/
theorem iv_capInsert (c : Cap) (src dest : CslotPtr) :
    HV (fun w => IVV t w ∧ (NotIV t dest ∨ c = .nullCap)) (IVV t) (capInsert (Z := Unit) c src dest) := by
  refine hv_pin fun w0 hw0 => ?_
  unfold capInsert
  refine hv_getCap_bind fun w sc hw hsc => ?_
  subst hw
  refine hv_pure_bind ?_
  refine hv_getCap_bind fun w1 oc hw1 hoc => ?_
  subst w1
  refine hv_assert_bind fun _ => ?_
  unfold setUntypedCapAsFull
  split
  · rename_i hut
    have hsrc : NotIV t src := by
      refine notIV_of_held hw0.1 hsc ?_
      intro e; subst e; simp [isUntypedCap] at hut
    refine hv_bind (hv_setCap _ _ _) fun _ => ?_
    refine hv_bind (hv_setCap _ _ _) fun _ => ?_
    refine hv_gets_bind (fun w => w.2.2.2) (fun _ => rfl) fun w2 hw2 => ?_
    subst w2
    refine hv_pure_bind ?_
    refine hv_gets_bind (fun w => w.2.2.1 src) (fun _ => rfl) fun w3 hw3 => ?_
    subst w3
    refine hv_gets_bind (fun w => w.2.2.1 dest) (fun _ => rfl) fun w4 hw4 => ?_
    subst w4
    refine hv_bind (hv_updateCdt _ _) fun _ => ?_
    refine hv_bind (hv_doExtendedOp _) fun _ => ?_
    refine hv_mono (hv_setOriginal _ _ _) fun w' e => ?_
    subst e
    exact iv_vCap (iv_vCap hw0.1 (Or.inl hsrc)) hw0.2
  · refine hv_pure_bind ?_
    refine hv_bind (hv_setCap _ _ _) fun _ => ?_
    refine hv_gets_bind (fun w => w.2.2.2) (fun _ => rfl) fun w2 hw2 => ?_
    subst w2
    refine hv_pure_bind ?_
    refine hv_gets_bind (fun w => w.2.2.1 src) (fun _ => rfl) fun w3 hw3 => ?_
    subst w3
    refine hv_gets_bind (fun w => w.2.2.1 dest) (fun _ => rfl) fun w4 hw4 => ?_
    subst w4
    refine hv_bind (hv_updateCdt _ _) fun _ => ?_
    refine hv_bind (hv_doExtendedOp _) fun _ => ?_
    refine hv_mono (hv_setOriginal _ _ _) fun w' e => ?_
    subst e
    exact iv_vCap hw0.1 hw0.2

/-- **`cap_insert` keeps `SIV N t`** (ut7's `hv_capInsert3` at `N` and `M`, and `iv_capInsert`). -/
theorem hv_capInsertSI (c : Cap) (src dest : CslotPtr) :
    HV (fun w => SIV N t w ∧ CI3 w c src ∧ PosOK w dest ∧ (NotIV t dest ∨ c = .nullCap)) (SIV N t)
      (capInsert (Z := Unit) c src dest) := by
  intro σ hσ y hy
  obtain ⟨⟨h3, hM, hn⟩, hci, hp, hd⟩ := hσ
  exact ⟨hv_capInsert3 c src dest σ ⟨h3, hci, hp⟩ y hy,
    (hv_capInsert3 (N := fun _ => t) c src dest σ ⟨⟨h3.1, hM⟩, hci, hp⟩ y hy).2,
    iv_capInsert c src dest σ ⟨hn, hd⟩ y hy⟩

/-- `set_cap` keeps `NOV` off the node slots, or of a null / notification cap. -/
theorem iv_setCap (c : Cap) (sl : CslotPtr) :
    HV (fun w => IVV t w ∧ (NotIV t sl ∨ c = .nullCap)) (IVV t) (setCap (Z := Unit) c sl) := by
  refine hv_pin fun w hw => ?_
  exact hv_mono (hv_setCap c sl w) fun w' e => e ▸ iv_vCap hw.1 hw.2

/-! ## TCB installs -/

/-- The TCB install writes the invoked thread's slot: the inner check finds the thread
cap in its slot, so the thread is covered, hence not `t` (`IrqOutV (fun _ => t)`). -/
theorem iv_checkCapAt_ins (c : Cap) (src : CslotPtr) (tt : ObjRef) (sl : CslotPtr) (n : Nat) :
    HV (fun w => IVV t w ∧ IrqOutV (fun _ => t) w) (IVV t)
      (checkCapAt (Z := Unit) c src (checkCapAt (.threadCap tt) sl (capInsert c src (tt, tcbCnodeIndex n)))) := by
  unfold checkCapAt
  refine hv_getCap_bind fun w c' hw _ => ?_
  unfold NonDet.when
  split
  · refine hv_getCap_bind fun w' c'' hw' hc'' => ?_
    subst hw'
    split
    · rename_i hso
      have e := sameObj_thread hso
      subst e
      have hne : NotIV t (tt, tcbCnodeIndex n) :=
        notIV_of_cov hw.2 hc'' (by simp [covR, capRng, objRefs])
      exact hv_pre (iv_capInsert c src _) fun w1 e => e ▸ ⟨hw.1, Or.inl hne⟩
    · exact hv_mono (hv_uk fun _ => ik_pure' _) fun w1 e => e ▸ hw.1
  · exact hv_mono (hv_uk fun _ => ik_pure' _) fun w1 e => e ▸ hw.1

theorem iw_checkCapAt_ins (c : Cap) (src : CslotPtr) (tt : ObjRef) (sl : CslotPtr) (n : Nat) (hn : n < 6) :
    IK (SI N t) (checkCapAt (Z := Unit) c src (checkCapAt (.threadCap tt) sl (capInsert c src (tt, tcbCnodeIndex n)))) :=
  iw_of (fun _ => p3_checkCapAt_ins c src tt sl n hn) fun σ h y hy =>
    iv_checkCapAt_ins c src tt sl n σ ⟨h.2.2, h.2.1⟩ y hy

theorem iw_installTcbCap (target : ObjRef) (slot : CslotPtr) (n : Nat) (slotOpt : Option (Cap × CslotPtr))
    (hn : n < 6) : IKE (SI N t) (installTcbCap (Z := Unit) target slot n slotOpt) := by
  cases slotOpt with
  | none => exact ike_returnOk _
  | some p =>
    obtain ⟨c, src⟩ := p
    simp only [installTcbCap]
    refine ike_bind (iw_capDelete _) fun _ => ?_
    unfold NonDetE.unlessE
    split
    · exact ike_returnOk _
    · exact ike_liftE (iw_checkCapAt_ins c src target slot n hn)

/-! ## The IPC cap transfer -/

theorem iw_transferCapsLoop (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (caps : List (Cap × CslotPtr)) (n : Nat) (slots : List CslotPtr) (mi : MessageInfo) (σ : State Unit),
      SI N t σ → slots.length ≤ 1 → (∀ d ∈ slots, DestRefV (uV σ) d) →
      (slots ≠ [] → ∀ p ∈ caps, capAt σ p.2 = some p.1) →
      ∀ y ∈ (transferCapsLoop (Z := Unit) ep rb n caps slots mi σ).1, SI N t y.2
  | [], n, slots, mi, σ, hI, _, _, _, y, hy => by
    unfold transferCapsLoop at hy; rw [Set.mem_singleton_iff.1 hy]; exact hI
  | (cap, slot) :: more, n, slots, mi, σ, hI, hl, hD, hc, y, hy => by
    have ih := iw_transferCapsLoop ep rb more (n + 1)
    unfold transferCapsLoop constOnFailure NonDetE.catch at hy
    obtain ⟨z, hz, hy⟩ := hy
    have hyz : y.2 = z.2 := by
      obtain ⟨r, s⟩ := z
      cases r <;> (rw [Set.mem_singleton_iff.1 hy])
    rw [hyz]
    clear hy hyz
    replace hz := run_returnOk_bind_mem hz
    try dsimp only at hz
    split at hz
    · obtain ⟨x, hx, hz⟩ := run_liftE_bind_mem hz
      have hv := uk_mem (fun _ => uk_setExtraBadge _ _ _) hx
      obtain ⟨w, hw, rfl⟩ := mem_liftE' hz
      refine ih slots _ x.2 (iw_of_view hv hI) hl (fun d hd => by rw [hv]; exact hD d hd) (fun hne p hp => ?_) w hw
      rw [capAt_of_view hv]; exact hc hne p (List.mem_cons.2 (Or.inr hp))
    · split at hz
      · rename_i hne
        obtain ⟨z0, hz0, ⟨c', hc', hz⟩ | ⟨e, he, rfl⟩⟩ := mem_bindE' hz
        · obtain ⟨r0, s0⟩ := z0
          simp only at hc'; subst hc'
          have hv0 : uV s0 = uV σ := uk_deriveCap slot cap σ rfl _ hz0
          have hd := okv_deriveCapR slot cap σ rfl c' s0 hz0
          obtain ⟨z1, hz1, ⟨u, hu, hz⟩ | ⟨e, he, rfl⟩⟩ := mem_bindE' hz
          · obtain ⟨hnn, hs1⟩ := whenE_throw_ok hz1 hu
            obtain ⟨x, hx, hz⟩ := run_liftE_bind_mem hz
            rw [hs1] at hx
            have hI0 := iw_of_view hv0 hI
            have hcs := hc hne (cap, slot) (List.mem_cons.2 (Or.inl rfl))
            obtain ⟨dd, tl, rfl⟩ : ∃ dd tl, slots = dd :: tl := by
              cases slots with
              | nil => exact absurd rfl hne
              | cons a t => exact ⟨a, t, rfl⟩
            have hok : CI3 (uV s0) c' slot := by
              refine ⟨cap, by show capAt s0 slot = _; rw [capAt_of_view hv0]; exact hcs, ?_⟩
              rcases hd hnn with ⟨e1, hu', hk⟩ | hR
              · exact Or.inl ⟨e1, hu', by rw [hv0]; exact hk⟩
              · exact Or.inr hR
            have hDd : DestRefV (uV s0) dd := by rw [hv0]; exact hD dd (List.mem_cons_self)
            have hP : PosOK (uV s0) dd := posOK_of_destRef hI0.1.1.2 hDd
            have hIx := hv_capInsertSI c' slot dd s0
              ⟨hI0, hok, hP, Or.inl (notIV_of_destRef hI0.2.1 hDd)⟩ x hx
            obtain ⟨w, hw, rfl⟩ := mem_liftE' hz
            have htl : tl = [] := by
              simp only [List.length_cons] at hl; exact List.eq_nil_of_length_eq_zero (by omega)
            subst htl
            exact ih [] _ x.2 hIx (by simp) (fun _ h => absurd h List.not_mem_nil) (fun h => absurd rfl h) w hw
          · have hs1 : z1.2 = s0 := by
              unfold NonDetE.whenE at hz1
              split at hz1 <;> (rw [Set.mem_singleton_iff.1 hz1])
            show SI N t z1.2
            rw [hs1]; exact iw_of_view hv0 hI
        · exact iw_of_view (uk_deriveCap slot cap σ rfl _ hz0) hI
      · rw [Set.mem_singleton_iff.1 hz]; exact hI

theorem iw_transferCaps (info : MessageInfo) (caps : List (Cap × CslotPtr)) (ep : Option ObjRef) (recv : ObjRef)
    (rbuf : Option ObjRef) (σ : State Unit) (hI : SI N t σ) (hc : ∀ p ∈ caps, capAt σ p.2 = some p.1) :
    ∀ y ∈ (transferCaps (Z := Unit) info caps ep recv rbuf σ).1, SI N t y.2 := by
  intro y hy
  unfold transferCaps at hy
  obtain ⟨x, hx, hy⟩ := hy
  have hv := uk_mem (fun _ => uk_getReceiveSlots _ _) hx
  have hlen := getReceiveSlots_len recv rbuf σ x hx
  have hdst := getReceiveSlots_dest recv rbuf σ x hx
  obtain ⟨x2, hx2, hy⟩ := hy
  obtain rfl := Set.mem_singleton_iff.1 hx2
  dsimp only at hy
  cases rbuf with
  | none => rw [Set.mem_singleton_iff.1 hy]; exact iw_of_view hv hI
  | some b =>
    exact iw_transferCapsLoop ep b caps 0 x.1 _ x.2 (iw_of_view hv hI) hlen
      (fun d hd => by rw [hv]; exact hdst d hd)
      (fun _ p hp => by rw [capAt_of_view hv]; exact hc p hp) y hy

/-- **The normal IPC transfer keeps `SI N t`** (no premise). -/
theorem iw_doNormalTransfer (sender : ObjRef) (sbuf ep : Option ObjRef) (badge : Data) (grant : Bool)
    (recv : ObjRef) (rbuf : Option ObjRef) :
    IK (SI N t) (doNormalTransfer (Z := Unit) sender sbuf ep badge grant recv rbuf) := by
  intro σ hI y hy
  unfold doNormalTransfer at hy
  obtain ⟨x1, hx1, hy⟩ := hy
  have hv1 := uk_mem (fun _ => uk_getMessageInfo _) hx1
  have hI1 : SI N t x1.2 := iw_of_view hv1 hI
  have tail : ∀ (caps : List (Cap × CslotPtr)) (s : State Unit), SI N t s → (∀ p ∈ caps, capAt s p.2 = some p.1) →
      ∀ y ∈ ((do
        let mrsTransferred ← copyMrs (Z := Unit) sender sbuf recv rbuf x1.1.miLength
        let mi' ← transferCaps x1.1 caps ep recv rbuf
        setMessageInfo recv { miLength := mrsTransferred, miExtraCaps := mi'.miExtraCaps, miCapsUnwrapped := mi'.miCapsUnwrapped, miLabel := x1.1.miLabel }
        asUser recv (setRegister badge_register badge)) s).1, SI N t y.2 := by
    intro caps s hs hc y hy
    obtain ⟨x3, hx3, hy⟩ := hy
    have hv3 := uk_mem (fun _ => uk_copyMrs _ _ _ _ _) hx3
    obtain ⟨x4, hx4, hy⟩ := hy
    have hI4 := iw_transferCaps _ _ _ _ _ x3.2 (iw_of_view hv3 hs)
      (fun p hp => by rw [capAt_of_view hv3]; exact hc p hp) x4 hx4
    exact (iw_of_uk fun _ => by uk_auto) x4.2 hI4 y hy
  simp only at hy
  split at hy
  · obtain ⟨x2, hx2, hy⟩ := hy
    unfold NonDetE.catch at hx2
    obtain ⟨z, hz, hx2⟩ := hx2
    have hvz : uV z.2 = uV x1.2 := uk_lookupExtraCaps _ _ _ x1.2 rfl z hz
    obtain ⟨r, s⟩ := z
    cases r with
    | error e =>
      obtain rfl := Set.mem_singleton_iff.1 hx2
      exact tail [] s (iw_of_view hvz hI1) (fun p hp => absurd hp List.not_mem_nil) y hy
    | ok l =>
      obtain rfl := Set.mem_singleton_iff.1 hx2
      refine tail l s (iw_of_view hvz hI1) (fun p hp => ?_) y hy
      have := okv_lookupExtraCaps sender sbuf x1.1 x1.2 rfl l s hz p hp
      rw [capAt_of_view hvz]; exact this
  · obtain ⟨x2, hx2, hy⟩ := hy
    obtain rfl := Set.mem_singleton_iff.1 hx2
    exact tail [] x1.2 hI1 (fun p hp => absurd hp List.not_mem_nil) y hy

end Basic

end

end Fl4Proofs.P3.SInvIV
