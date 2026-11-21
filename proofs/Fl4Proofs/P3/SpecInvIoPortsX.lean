/-
P3 (DESIGN.md §9), invariant line G1 (g5c): **the deletion path of the IO-port
invariant `IOI`** (spec side only; outside the `JAtZ` cone; vih3's
SpecInvValidIrqHandlersX with IO ports for IRQ lines).

The deletion is the only place IO ports are freed: `rec_del`'s
`CTEDeleteCall` empties the slot with the cleanup cap `IOPortCap f l` that
`finalise_cap` returned for a *final* IO-port cap, and `post_cap_deletion`
(`arch_post_cap_deletion` → `free_ioport_range f l`) clears the ports `[f, l]`.
Finality (`is_final_cap'` over `gen_obj_refs`, which holds `IOPortRef f` for an
IO-port cap of first port `f`) leaves `UniqIo f sl`: only the emptied slot holds
an IO-port cap with first port `f`. After its `set_cap NullCap` no cap starts at
`f`; any remaining cap overlapping `[f, l]` would be equal to it by
`ioports_no_overlap` (`GoodS`), hence start at `f`, so every remaining cap's
ports stay allocated. This is why `IoNoOverlap` is carried: `valid_ioports`
alone is not inductive here.

* `ioi_tail`, `ioi_emptySlot_p` (the cleanup cap `ClOk`: an IO-port cleanup cap
  is a cap of the state and its first port is held only by the emptied slot).
* `rv_finaliseCap_io`: the remainder is never an IO-port cap; the cleanup cap is
  an IO-port cap only for the finalised IO-port cap itself, finalised as final
  (and then `finalise_cap` changes no state).
* **`ioi_recDel : HT IOI (RDPostIo k) (rec_del k)`**: a `FinaliseSlotCall slot`
  returning a cleanup cap leaves it `ClOk` at `slot` (`ht_lfp`).
  `ioi_capDelete`, `ioi_capRevoke`.
-/
import Fl4Proofs.P3.SpecInvIoPortsG
open Classical

namespace Fl4Proofs.P3.SInvIo
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvV Fl4Proofs.P3.SInvDom

noncomputable section

set_option maxHeartbeats 1000000

/-! ## `ioi_auto` -/

syntax "ioi_leaf" : tactic
macro_rules | `(tactic| ioi_leaf) => `(tactic| fail "no ioi_leaf")

macro "ioi_auto" : tactic => `(tactic| repeat' (first | ioi_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

/-- A function with an `HI S` lemma (every `S`) and an `IoK` lemma keeps `IOI`. -/
macro_rules | `(tactic| ioi_leaf) => `(tactic| ((with_reducible refine ik_ioi (fun _ => ?_) (fun _ => ?_)) <;> first | hv_leaf | iok_leaf))
macro_rules | `(tactic| ioi_leaf) => `(tactic| ((with_reducible refine ike_ioi (fun _ => ?_) (fun _ => ?_)) <;> first | hv_leaf | iok_leaf))
macro_rules | `(tactic| ioi_leaf) => `(tactic| ((with_reducible apply ik_modify); intro _ h; exact h))
macro_rules | `(tactic| ioi_leaf) => `(tactic| ((with_reducible refine ik_doMachineOp ?_ _); intro _ _ h; exact h))
macro_rules | `(tactic| ioi_leaf) => `(tactic| ((with_reducible refine ik_doExtendedOp ?_ _); intro _ _ h; exact h))
macro_rules | `(tactic| ioi_leaf) => `(tactic| with_reducible exact ik_getObject _)

/-! ## Uniqueness of a final IO-port cap's first port -/

/-- Only `sl` holds an IO-port cap with first port `f`. -/
def UniqIo (f : IoPort) (sl : CslotPtr) (σ : State Unit) : Prop :=
  ∀ p cref l, capOpt (σ.kheap p) cref = some (.archObjectCap (.ioPortCap f l)) → (p, cref) = sl

theorem io_mem_gen (f l : IoPort) :
    GenObjRef.archRef (.ioPortRef f) ∈ genObjRefs (.archObjectCap (.ioPortCap f l)) := by
  simp [genObjRefs, archCapSetMap, archGenObjRefs]

/-- **A final IO-port cap is the only cap with its first port.** -/
theorem final_io_unique {σ : State Unit} {f l : IoPort} {sl : CslotPtr}
    (hf : isFinalCap' (Z := Unit) (.archObjectCap (.ioPortCap f l)) σ)
    (hs : capOpt (σ.kheap sl.1) sl.2 = some (.archObjectCap (.ioPortCap f l))) : UniqIo f sl σ := by
  obtain ⟨c0, hc0⟩ := hf
  have mem : ∀ p cref l', capOpt (σ.kheap p) cref = some (.archObjectCap (.ioPortCap f l')) →
      (p, cref) ∈ {cref | ∃ cap', ((getCap cref : SMonad Unit Cap) σ).1 = {(cap', σ)} ∧
        genObjRefs (.archObjectCap (.ioPortCap f l)) ∩ genObjRefs cap' ≠ ∅} := by
    intro p cref l' h
    refine ⟨_, (getCap_set_iff σ p cref _).2 h, fun e => ?_⟩
    have : GenObjRef.archRef (.ioPortRef f) ∈
        genObjRefs (.archObjectCap (.ioPortCap f l)) ∩ genObjRefs (.archObjectCap (.ioPortCap f l')) :=
      ⟨io_mem_gen f l, io_mem_gen f l'⟩
    rw [e] at this; exact this
  intro p cref l' h
  have m1 := mem p cref l' h
  have m2 := mem sl.1 sl.2 l hs
  rw [hc0] at m1 m2
  rw [Set.mem_singleton_iff.1 m1]
  exact (Set.mem_singleton_iff.1 m2).symm

/-- The cleanup cap of an emptied slot is fine: an IO-port cleanup cap is a cap of the state whose
first port only the slot holds. -/
def ClOk (c : Cap) (sl : CslotPtr) (σ : State Unit) : Prop :=
  ∀ f l, c = .archObjectCap (.ioPortCap f l) → Has σ f l ∧ UniqIo f sl σ

instance (c : Cap) (sl : CslotPtr) : WLH (ClOk c sl) :=
  wlh_of_hV fun _ _ e h f l hc => ⟨by rw [has_of_hV e]; exact (h f l hc).1,
    fun p cref l' h' => (h f l hc).2 p cref l' (by rw [← hV_cap e]; exact h')⟩

theorem clOk_noIo {c : Cap} (h : ∀ f l, c ≠ .archObjectCap (.ioPortCap f l)) (sl : CslotPtr) (σ : State Unit) :
    ClOk c sl σ := fun f l e => absurd e (h f l)

/-! ## `empty_slot` -/

theorem setIoportMask_out {f l : IoPort} {v : Bool} {σ : State Unit} {x : Unit × State Unit}
    (hx : x ∈ (setIoportMask (Z := Unit) f l v σ).1) :
    x.2 = { σ with archState := { σ.archState with x64AllocatedIoPorts :=
      fun p => if p ≥ f ∧ p ≤ l then v else σ.archState.x64AllocatedIoPorts p } } := by
  unfold setIoportMask at hx
  obtain ⟨y, hy, hx⟩ := hx
  obtain rfl := Set.mem_singleton_iff.1 hy
  obtain ⟨z, hz, hx⟩ := hx
  obtain rfl := Set.mem_singleton_iff.1 hz
  obtain rfl := Set.mem_singleton_iff.1 hx
  rfl

/-- The tail of `empty_slot`: the null write, then `post_cap_deletion`. -/
theorem ioi_tail {c : Cap} {sl : CslotPtr} {σ : State Unit} (h : IOI σ) (hu : ClOk c sl σ) :
    ∀ x ∈ ((setCap (Z := Unit) .nullCap sl >>= fun _ => postCapDeletion (Z := Unit) c) σ).1, IOI x.2 := by
  rintro x ⟨y, hy, hx⟩
  have hS : VS (Has σ) y.2 :=
    ik_vs (hi_setCap .nullCap sl (by io_side)) (fun a => iok_setCap _ _) σ (vs_of_ioi h) y hy
  cases c with
  | archObjectCap a =>
    cases a with
    | ioPortCap f l =>
      obtain ⟨hhas, hun⟩ := hu f l rfl
      have hnone : ∀ l', ¬ Has y.2 f l' := by
        rintro l' ⟨p, cref, hc⟩
        obtain ⟨o, r⟩ := sl
        rcases (vih_setCap_out hy).2 p cref _ hc with ⟨-, -, e⟩ | ⟨hne, h0⟩
        · cases e
        · obtain ⟨e1, e2⟩ := Prod.mk.inj (hun p cref l' h0)
          rcases hne with e | e
          · exact e e1
          · exact e e2
      simp only [postCapDeletion, archPostCapDeletion, freeIoportRange] at hx
      have e := setIoportMask_out hx
      unfold IOI
      rw [e]
      refine ⟨fun f' l' hh => ?_, fun f1 l1 f2 l2 h1 h2 ho => hS.2.2 f1 l1 f2 l2 (hS.1 _ _ h1) (hS.1 _ _ h2) ho⟩
      have hh' : Has y.2 f' l' := hh
      obtain ⟨hle, hal⟩ := hS.2.1 f' l' (hS.1 f' l' hh')
      refine ⟨hle, fun q h1 h2 => ?_⟩
      show (if q ≥ f ∧ q ≤ l then false else y.2.archState.x64AllocatedIoPorts q) = true
      split_ifs with hq
      · exfalso
        obtain ⟨e1, -⟩ := hS.2.2 f l f' l' hhas (hS.1 f' l' hh') ⟨q, hq.1, hq.2, h1, h2⟩
        subst e1
        exact hnone l' hh'
      · exact hal q h1 h2
    | _ =>
      simp only [postCapDeletion, archPostCapDeletion] at hx
      exact (ik_pure () : IKH IOI _) _ (ioi_of_vs hS) x hx
  | irqHandlerCap irq =>
    simp only [postCapDeletion, deletedIrqHandler] at hx
    exact ik_ioi (fun _ => hi_setIrqState _ _) (fun _ => iok_setIrqState _ _) y.2 (ioi_of_vs hS) x hx
  | _ =>
    simp only [postCapDeletion] at hx
    exact (ik_pure () : IKH IOI _) _ (ioi_of_vs hS) x hx

theorem ik_and' {P Q : State Unit → Prop} {α : Type} {m : NonDet (State Unit) α} (hP : IKH P m) (hQ : IKH Q m) :
    IKH (fun σ => P σ ∧ Q σ) m := fun σ h x hx => ⟨hP σ h.1 x hx, hQ σ h.2 x hx⟩

/-- **`empty_slot`** with a fine cleanup cap. -/
theorem ioi_emptySlot_p (sl : CslotPtr) (c : Cap) (σ : State Unit) (hu : ClOk c sl σ) :
    IKp IOI σ (emptySlot (Z := Unit) sl c) := by
  unfold emptySlot
  refine ikp_getCap_bind fun cap _ => ?_
  split
  · exact ikp_of_ik (ik_pure _) σ
  · intro h x hx
    obtain ⟨y1, hy1, hx⟩ := hx
    obtain ⟨y2, hy2, hx⟩ := hx
    obtain ⟨y3, hy3, hx⟩ := hx
    obtain ⟨y4, hy4, hx⟩ := hx
    obtain ⟨y5, hy5, hx⟩ := hx
    obtain ⟨y6, hy6, hx⟩ := hx
    obtain rfl := Set.mem_singleton_iff.1 hy1
    obtain rfl := Set.mem_singleton_iff.1 hy2
    obtain rfl := Set.mem_singleton_iff.1 hy3
    have q4 := ik_and' (ik_ioi (fun _ => hv_setCdt _) (fun _ => iok_setCdt _)) (hv_setCdt (P := ClOk c sl) _)
      _ ⟨h, hu⟩ y4 hy4
    have q5 := ik_and' (P := IOI) (Q := ClOk c sl) (ik_doExtendedOp (fun _ _ h => h) _)
      (ik_doExtendedOp (fun σ e h => WLH.view σ { σ with exst := e } (by rfl) (by rfl) h) _) _ q4 y5 hy5
    have q6 := ik_and' (ik_ioi (fun _ => hv_setOriginal _ _) (fun _ => iok_setOriginal _ _))
      (hv_setOriginal (P := ClOk c sl) _ _) _ q5 y6 hy6
    exact ioi_tail q6.1 q6.2 x hx

/-! ## `finalise_cap`'s results -/

abbrev PrIo (c : Cap) (fin : Bool) (r : Cap × Cap) : Prop :=
  (∀ f l, r.1 ≠ .archObjectCap (.ioPortCap f l)) ∧
    (∀ f l, r.2 = .archObjectCap (.ioPortCap f l) → c = .archObjectCap (.ioPortCap f l) ∧ fin = true)

theorem rv_fc_pure_io {c : Cap} {fin : Bool} {a : Cap × Cap} (h1 : ∀ f l, a.1 ≠ .archObjectCap (.ioPortCap f l))
    (h2 : ∀ f l, a.2 = .archObjectCap (.ioPortCap f l) → c = .archObjectCap (.ioPortCap f l) ∧ fin = true) :
    RV (PrIo c fin) (pure a : NonDet (State Unit) (Cap × Cap)) :=
  rv_pure (And.intro h1 h2)

macro "rv_auto_io" : tactic => `(tactic| repeat' (first
  | (with_reducible refine rv_fc_pure_io (fun _ _ h => ?_) (fun _ _ h => ?_) <;> (try split at h) <;> simp_all; done)
  | (with_reducible refine rv_liftM (fun _ => And.intro (fun _ _ h => ?_) (fun _ _ h => ?_)) <;> simp_all; done)
  | (with_reducible exact rv_fail)
  | (with_reducible refine rv_bind fun _ => ?_)
  | split))

theorem rv_finaliseCap_io (c : Cap) (fin : Bool) : RV (PrIo c fin) (finaliseCap (Z := Unit) c fin) := by
  cases c with
  | archObjectCap a =>
    simp only [finaliseCap]; unfold archFinaliseCap
    rv_auto_io
  | _ => simp only [finaliseCap]; rv_auto_io

/-! ## `rec_del` -/

/-- The post of `rec_del`: `IOI`, and a `FinaliseSlotCall slot`'s cleanup cap is fine at `slot`. -/
def RDPostIo (k : RecDelCall) (r : Except Unit (Bool × Cap)) (s : State Unit) : Prop :=
  IOI s ∧ ∀ sl e, k = .finaliseSlotCall sl e → ∀ b c, r = .ok (b, c) → ClOk c sl s

theorem ik_of_ht_rdio {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (h : ∀ k, HT IOI (RDPostIo k) (f k)) (k : RecDelCall) : IKHE (ε := Unit) IOI (f k : PMonad Unit (Bool × Cap)) :=
  fun σ hσ x hx => (h k σ hσ x hx).1

theorem ht_of_ik_rdio {k : RecDelCall} {m : NonDet (State Unit) (Except Unit (Bool × Cap))} (h : IKH IOI m)
    (hk : ∀ sl e, k ≠ .finaliseSlotCall sl e) : HT IOI (RDPostIo k) m :=
  fun σ hσ x hx => ⟨h σ hσ x hx, fun sl e e' => absurd e' (hk sl e)⟩

theorem ioi_setCap_noIo (c : Cap) (sl : CslotPtr) (h : ∀ f l, c ≠ .archObjectCap (.ioPortCap f l)) :
    IKH IOI (setCap (Z := Unit) c sl) :=
  ik_ioi (fun S => hi_setCap c sl (ioIn_noIo h S)) (fun _ => iok_setCap _ _)

set_option maxHeartbeats 4000000 in
/-- The `FinaliseSlotCall` step. -/
theorem ht_recDelF_fin_io {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k, HT IOI (RDPostIo k) (f k)) (slot : CslotPtr) (ex : Bool) :
    HT IOI (RDPostIo (.finaliseSlotCall slot ex)) (recDelF (Z := Unit) f (.finaliseSlotCall slot ex)).run := by
  have hrec' := ik_of_ht_rdio hrec
  have post_ok : ∀ s b c, IOI s → ClOk c slot s → RDPostIo (.finaliseSlotCall slot ex) (.ok (b, c)) s := by
    intro s b c h hu
    refine ⟨h, fun sl e he b' c' hr => ?_⟩
    simp only [RecDelCall.finaliseSlotCall.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    simp only [Except.ok.injEq, Prod.mk.injEq] at hr
    rw [← hr.2]; exact hu
  have post_err : ∀ e s, IOI s → RDPostIo (.finaliseSlotCall slot ex) (.error e) s :=
    fun e s h => ⟨h, fun _ _ _ _ _ hr => by cases hr⟩
  unfold recDelF withoutPreemption
  -- the cap read
  refine hte_bind (Q' := fun r s => ∃ c, r = .ok c ∧ IOI s ∧ capOpt (s.kheap slot.1) slot.2 = some c)
    (fun σ h x hx => by
      obtain ⟨y, hy, rfl⟩ := mem_liftE_inv' hx
      obtain ⟨o, r⟩ := slot
      obtain ⟨e1, e2⟩ := vih_mem_getCap hy
      exact ⟨y.1, rfl, by rw [e1]; exact h, by rw [e1]; exact e2⟩) (fun cap => ?_)
    (fun e s ⟨_, he, _⟩ => by cases he)
  refine ht_mono (Q := fun s => IOI s ∧ capOpt (s.kheap slot.1) slot.2 = some cap) ?_
    (fun s ⟨c, hc, h, hs⟩ => by cases hc; exact ⟨h, hs⟩) (fun _ _ h => h)
  split
  · exact hte_returnOk fun s h => post_ok s _ _ h.1 (clOk_noIo (fun _ _ h' => by cases h') _ _)
  -- finality
  refine hte_bind (Q' := fun r s => ∃ b, r = .ok b ∧ IOI s ∧ capOpt (s.kheap slot.1) slot.2 = some cap ∧
      (b = true → isFinalCap' (Z := Unit) cap s))
    (fun σ h x hx => by
      obtain ⟨y, hy, rfl⟩ := mem_liftE_inv' hx
      unfold isFinalCap at hy
      obtain rfl := Set.mem_singleton_iff.1 hy
      exact ⟨_, rfl, h.1, h.2, fun hb => of_decide_eq_true hb⟩) (fun fin => ?_)
    (fun e s ⟨_, he, _⟩ => by cases he)
  refine ht_mono (Q := fun s => IOI s ∧ capOpt (s.kheap slot.1) slot.2 = some cap ∧
      (fin = true → isFinalCap' (Z := Unit) cap s)) ?_
    (fun s ⟨c, hc, h⟩ => by cases hc; exact h) (fun _ _ h => h)
  -- finalise_cap: remainder no IO-port cap, cleanup cap fine at `slot`
  refine hte_bind (Q' := fun r s => ∃ rc, r = .ok rc ∧ IOI s ∧ (∀ f l, rc.1 ≠ .archObjectCap (.ioPortCap f l)) ∧
      ClOk rc.2 slot s) ?_ (fun rc => ?_)
    (fun e s ⟨_, he, _⟩ => by cases he)
  · intro σ h x hx
    obtain ⟨y, hy, rfl⟩ := mem_liftE_inv' hx
    refine ⟨y.1, rfl, ik_ioi (fun _ => hi_finaliseCap cap fin) (fun _ => iok_finaliseCap cap fin) σ h.1 y hy,
      (rv_finaliseCap_io cap fin σ y hy).1, fun f l hc => ?_⟩
    obtain ⟨hcap, hfin⟩ := (rv_finaliseCap_io cap fin σ y hy).2 f l hc
    subst hcap; subst hfin
    have hu := final_io_unique (h.2.2 rfl) h.2.1
    simp only [finaliseCap, archFinaliseCap] at hy
    rw [Set.mem_singleton_iff.1 hy]
    exact ⟨⟨slot.1, slot.2, h.2.1⟩, hu⟩
  obtain ⟨rem, cl⟩ := rc
  refine ht_mono (Q := fun s => IOI s ∧ (∀ f l, rem ≠ .archObjectCap (.ioPortCap f l)) ∧ ClOk cl slot s) ?_
    (fun s ⟨c, hc, h⟩ => by cases hc; exact h) (fun _ _ h => h)
  dsimp only
  split
  · exact hte_returnOk fun s h => post_ok s _ _ h.1 h.2.2
  split
  · refine hte_bind (Q' := fun r s => ∃ u, r = .ok u ∧ IOI s) ?_ (fun _ => ?_)
      (fun e s ⟨_, he, _⟩ => by cases he)
    · intro σ h x hx
      obtain ⟨y, hy, rfl⟩ := mem_liftE_inv' hx
      exact ⟨_, rfl, ioi_setCap_noIo rem slot h.2.1 σ h.1 y hy⟩
    · exact ht_mono (hte_returnOk (Q := IOI) fun s h => post_ok s _ _ h (clOk_noIo (fun _ _ h' => by cases h') _ _))
        (fun s ⟨_, hc, h⟩ => h) (fun _ _ h => h)
  · refine hte_bind (Q' := fun r s => ∃ u, r = .ok u ∧ IOI s) ?_ (fun _ => ?_)
      (fun e s ⟨_, he, _⟩ => by cases he)
    · intro σ h x hx
      obtain ⟨y, hy, rfl⟩ := mem_liftE_inv' hx
      exact ⟨_, rfl, ioi_setCap_noIo rem slot h.2.1 σ h.1 y hy⟩
    refine ht_mono (Q := IOI) ?_ (fun s ⟨_, _, h⟩ => h) (fun _ _ h => h)
    refine hte_bind (Q' := fun r s => IOI s) (fun σ h x hx => hrec' _ σ h x hx) (fun _ => ?_) (fun e s h => post_err e s h)
    refine hte_bind (Q' := fun r s => IOI s)
      (fun σ h x hx => ike_ioi (fun _ => hv_preemptionPoint) (fun _ => iok_preemptionPoint) σ h x hx) (fun _ => ?_)
      (fun e s h => post_err e s h)
    exact hrec _

set_option maxHeartbeats 4000000 in
/-- One step of `rec_del`, its recursive calls satisfying `RDPostIo`. -/
theorem ht_recDelF_io {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k, HT IOI (RDPostIo k) (f k)) (k : RecDelCall) : HT IOI (RDPostIo k) (recDelF (Z := Unit) f k) := by
  have hrec' := ik_of_ht_rdio hrec
  cases k with
  | finaliseSlotCall sl e => exact ht_recDelF_fin_io hrec sl e
  | cTEDeleteCall sl e =>
    have hk : ∀ sl' e', RecDelCall.cTEDeleteCall sl e ≠ .finaliseSlotCall sl' e' := fun _ _ h => by cases h
    show HT IOI (RDPostIo _) (recDelF (Z := Unit) f (.cTEDeleteCall sl e)).run
    unfold recDelF withoutPreemption
    refine hte_bind (Q' := RDPostIo (.finaliseSlotCall sl e)) (hrec _) (fun r => ?_)
      (fun er s h => ⟨h.1, fun _ _ h' => absurd h' (hk _ _)⟩)
    obtain ⟨b, cl⟩ := r
    dsimp only
    refine hte_bind (Q' := fun r s => IOI s) ?_ (fun _ => hte_returnOk fun s h => ⟨h, fun _ _ h' => absurd h' (hk _ _)⟩)
      (fun er s h => ⟨h, fun _ _ h' => absurd h' (hk _ _)⟩)
    intro σ h x hx
    obtain ⟨y, hy, rfl⟩ := mem_liftE_inv' hx
    unfold NonDet.when at hy
    split at hy
    · exact ioi_emptySlot_p sl cl σ (h.2 sl e rfl b cl rfl) h.1 y hy
    · rw [Set.mem_singleton_iff.1 hy]; exact h.1
  | reduceZombieCall c sl e =>
    refine ht_of_ik_rdio ?_ (fun _ _ h => by cases h)
    show IKHE IOI (recDelF (Z := Unit) f (.reduceZombieCall c sl e))
    unfold recDelF withoutPreemption
    split <;> (try (exfalso; simp_all; done)) <;> ioi_auto
    all_goals exact hrec' _

/-- **`rec_del`** (module docstring). -/
theorem ioi_recDel (k : RecDelCall) : HT IOI (RDPostIo k) (recDel (Z := Unit) k) := by
  unfold recDel
  exact ht_lfp IOI RDPostIo (fun f hf k => ht_recDelF_io hf k) k

theorem ioi_recDelE (k : RecDelCall) : IKHE (ε := Unit) IOI (recDel (Z := Unit) k) :=
  fun σ h x hx => (ioi_recDel k σ h x hx).1

macro_rules | `(tactic| ioi_leaf) => `(tactic| with_reducible exact ioi_recDelE _)

theorem ioi_capDelete (sl : CslotPtr) : IKHE (ε := Unit) IOI (capDelete (Z := Unit) sl) := by
  unfold capDelete; ioi_auto

macro_rules | `(tactic| ioi_leaf) => `(tactic| with_reducible exact ioi_capDelete _)

theorem ioi_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, IKH IOI (f k)) (sl : CslotPtr) : IKHE (ε := Unit) IOI (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, IKHE (ε := Unit) IOI (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeF withoutPreemption selectExt
  ioi_auto
  all_goals exact hrec' _

theorem ioi_capRevoke (sl : CslotPtr) : IKHE (ε := Unit) IOI (capRevoke (Z := Unit) sl) := by
  unfold capRevoke
  exact ik_lfp (fun f hf k => ioi_capRevokeF hf k) sl

macro_rules | `(tactic| ioi_leaf) => `(tactic| with_reducible exact ioi_capRevoke _)

end

end Fl4Proofs.P3.SInvIo
