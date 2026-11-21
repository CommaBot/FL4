/-
P3 (DESIGN.md §9), invariant line G1 (g5c, KENTRY-PLAN g5c): **l4v
`valid_ioports` with `ioports_no_overlap`**, the definitions, the split into a
cap half and an allocation half, and the cap writers (spec side only; outside
the `JAtZ` cone).

* `Has σ f l`: some slot holds `IOPortCap f l` (as `get_cap` reads it,
  `capOpt`). `GoodS S a`: every range of `S` is well formed (`f ≤ l`) and
  allocated in `a`, and two ranges of `S` that overlap are equal (l4v
  `ioports_no_overlap`). **`IOI σ := GoodS (Has σ) (ioA σ)`** is the carried
  invariant (`SpecIoP ∧ IoNoOverlap`, SpecInvIoPortsS).
* The split: `HI S σ` (every IO-port cap of `σ` is in `S`) reads only the caps,
  so it is a `WLH` predicate (vih2's frames SpecInvValidIrqHandlersF1..F4 keep
  it); the allocated ports are kept by the `IoK` family (SpecInvIoK1..K6).
  `VS S σ := HI S σ ∧ GoodS S (ioA σ)`; `ik_vs`: a function keeping `HI S`
  and the allocated ports keeps `VS S`; `ik_ioi_of_vs`: keeping every `VS S`
  keeps `IOI` (take `S := Has σ`).
* `IoIn S c`: if `c` is an IO-port cap its range is in `S` (what a cap about to
  be written must satisfy; a pure fact, so it survives any step).
* `HI S` leaves, as `hv_leaf` rules (so vih2's `hv_auto` proves `HI S` of the
  cap writers): `set_cap` of an `IoIn S` cap, `set_untyped_cap_as_full`,
  `cap_insert` / `cap_move` / `cap_swap` of `IoIn S` caps,
  `cap_swap_for_delete` (both caps read from slots), `create_cap` (default
  caps), `retype_region` (default objects hold no IO-port cap),
  `delete_objects`.
* `IoK` of the functions the generated family left out although they write no
  allocated port: `cap_delete_one` (cleanup `NullCap`), `deleting_irq_handler`,
  `finalise_cap`.
-/
import Fl4Proofs.P3.SpecInvIoK6
import Fl4Proofs.P3.SpecInvValidIrqHandlersS
open Classical

namespace Fl4Proofs.P3.SInvIo
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvV Fl4Proofs.P3.SInvDom

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The invariant -/

/-- A set of IO-port ranges. -/
abbrev IoSet := IoPort → IoPort → Prop

/-- The allocated IO ports. -/
def ioA (σ : State Unit) : IoPort → Bool := σ.archState.x64AllocatedIoPorts

/-- Some slot holds `IOPortCap f l`. -/
def Has (σ : State Unit) : IoSet := fun f l =>
  ∃ p cref, capOpt (σ.kheap p) cref = some (.archObjectCap (.ioPortCap f l))

/-- Two port ranges share a port. -/
def Ovl (f l f' l' : IoPort) : Prop := ∃ q, f ≤ q ∧ q ≤ l ∧ f' ≤ q ∧ q ≤ l'

/-- Well formed and allocated ranges, overlapping only when equal. -/
def GoodS (S : IoSet) (a : IoPort → Bool) : Prop :=
  (∀ f l, S f l → f ≤ l ∧ ∀ q, f ≤ q → q ≤ l → a q = true) ∧
  (∀ f l f' l', S f l → S f' l' → Ovl f l f' l' → f = f' ∧ l = l')

/-- **The invariant** (l4v `valid_ioports` ∧ `ioports_no_overlap`). -/
def IOI (σ : State Unit) : Prop := GoodS (Has σ) (ioA σ)

/-- Every IO-port cap's range is in `S`. -/
def HI (S : IoSet) (σ : State Unit) : Prop := ∀ f l, Has σ f l → S f l

/-- The cap half bounded by `S`, the allocation half for `S`. -/
def VS (S : IoSet) (σ : State Unit) : Prop := HI S σ ∧ GoodS S (ioA σ)

/-- A cap that may be written: an IO-port cap's range is in `S`. -/
def IoIn (S : IoSet) (c : Cap) : Prop := ∀ f l, c = .archObjectCap (.ioPortCap f l) → S f l

variable {S : IoSet} {σ σ' : State Unit}

theorem goodS_mono {S' : IoSet} {a : IoPort → Bool} (h : GoodS S a) (hs : ∀ f l, S' f l → S f l) :
    GoodS S' a :=
  ⟨fun f l h' => h.1 f l (hs f l h'), fun f l f' l' h1 h2 ho => h.2 f l f' l' (hs f l h1) (hs f' l' h2) ho⟩

theorem ioi_of_vs (h : VS S σ) : IOI σ := goodS_mono h.2 h.1

theorem vs_of_ioi (h : IOI σ) : VS (Has σ) σ := ⟨fun _ _ h => h, h⟩

theorem ioIn_noIo {c : Cap} (h : ∀ f l, c ≠ .archObjectCap (.ioPortCap f l)) (S : IoSet) : IoIn S c :=
  fun f l e => absurd e (h f l)

theorem ioIn_of_slot (h : HI S σ) {p : ObjRef} {r : CnodeIndex} {c : Cap}
    (hc : capOpt (σ.kheap p) r = some c) : IoIn S c :=
  fun f l e => h f l ⟨p, r, e ▸ hc⟩

theorem has_of_hV (e : hV σ' = hV σ) : Has σ' = Has σ := by
  funext f l; unfold Has; simp only [hV_cap e]

instance (S : IoSet) : WLH (HI S) :=
  wlh_of_hV fun _ _ e h f l hh => h f l (by rw [has_of_hV e] at hh; exact hh)

/-! ## The split -/

/-- **Keeping `HI S` and the allocated ports keeps `VS S`.** -/
theorem ik_vs {α : Type} {m : NonDet (State Unit) α} (hH : IKH (HI S) m) (hI : ∀ a, IoK a m) :
    IKH (VS S) m := by
  intro σ h x hx
  have h2 : ioA x.2 = ioA σ := hI (ioA σ) σ rfl x hx
  exact ⟨hH σ h.1 x hx, by rw [h2]; exact h.2⟩

theorem ike_vs {ε α : Type} {m : NonDetE (State Unit) ε α} (hH : IKHE (HI S) m) (hI : ∀ a, IoKE a m) :
    IKHE (VS S) m :=
  ik_vs (m := ExceptT.run m) hH hI

/-- **Keeping every `VS S` keeps `IOI`.** -/
theorem ik_ioi_of_vs {α : Type} {m : NonDet (State Unit) α} (h : ∀ S, IKH (VS S) m) : IKH IOI m :=
  fun σ hσ x hx => ioi_of_vs (h _ σ (vs_of_ioi hσ) x hx)

theorem ike_ioi_of_vs {ε α : Type} {m : NonDetE (State Unit) ε α} (h : ∀ S, IKHE (VS S) m) : IKHE IOI m :=
  ik_ioi_of_vs (m := ExceptT.run m) h

/-- A function keeping every `WLH` predicate and the allocated ports keeps `IOI`. -/
theorem ik_ioi {α : Type} {m : NonDet (State Unit) α} (hH : ∀ S, IKH (HI S) m) (hI : ∀ a, IoK a m) :
    IKH IOI m :=
  ik_ioi_of_vs fun S => ik_vs (hH S) hI

theorem ike_ioi {ε α : Type} {m : NonDetE (State Unit) ε α} (hH : ∀ S, IKHE (HI S) m)
    (hI : ∀ a, IoKE a m) : IKHE IOI m :=
  ik_ioi (m := ExceptT.run m) hH hI

/-! ## `set_cap` and the cap writers (`HI S`) -/

/-- Side conditions `IoIn S c`. -/
macro "io_side" : tactic => `(tactic| first
  | assumption
  | (intro _ _ h; cases h; done)
  | exact ioIn_noIo (fun _ _ h => by cases h) _
  | (intro _ _ h; simp_all; done))

theorem hi_setCap_p (c : Cap) (sl : CslotPtr) (σ : State Unit) (hc : HI S σ → IoIn S c) :
    IKp (HI S) σ (setCap (Z := Unit) c sl) := by
  intro h x hx
  obtain ⟨o, r⟩ := sl
  intro f l hh
  obtain ⟨p, cref, hp⟩ := hh
  rcases (vih_setCap_out hx).2 p cref _ hp with ⟨-, -, e⟩ | ⟨-, h0⟩
  · exact hc h f l e.symm
  · exact h f l ⟨p, cref, h0⟩

theorem hi_setCap (c : Cap) (sl : CslotPtr) (hc : IoIn S c) : IKH (HI S) (setCap (Z := Unit) c sl) :=
  fun σ => hi_setCap_p c sl σ fun _ => hc

macro_rules | `(tactic| hv_leaf) => `(tactic| ((with_reducible refine hi_setCap _ _ ?_); io_side))

theorem ioIn_freeIndexUpdate_ut {c : Cap} (h : isUntypedCap c = true) (g : Nat → Nat) (S : IoSet) :
    IoIn S (freeIndexUpdate g c) := by
  cases c <;> first | (simp [isUntypedCap] at h; done) | exact ioIn_noIo (fun _ _ e => by simp [freeIndexUpdate] at e) _

theorem hi_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : CslotPtr) :
    IKH (HI S) (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull
  split
  · rename_i h
    exact hi_setCap _ _ (ioIn_freeIndexUpdate_ut (by simpa using h.1) _ S)
  · exact ik_pure _

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hi_setUntypedCapAsFull _ _ _)

theorem hi_capInsert (c : Cap) (src dst : CslotPtr) (hc : IoIn S c) :
    IKH (HI S) (capInsert (Z := Unit) c src dst) := by
  unfold capInsert; hv_auto

theorem hi_capMove (c : Cap) (src dst : CslotPtr) (hc : IoIn S c) :
    IKH (HI S) (capMove (Z := Unit) c src dst) := by
  unfold capMove; hv_auto

theorem hi_capSwap (c1 : Cap) (s1 : CslotPtr) (c2 : Cap) (s2 : CslotPtr) (hc1 : IoIn S c1) (hc2 : IoIn S c2) :
    IKH (HI S) (capSwap (Z := Unit) c1 s1 c2 s2) := by
  unfold capSwap; hv_auto

theorem hi_capSwapForDelete (s1 s2 : CslotPtr) : IKH (HI S) (capSwapForDelete (Z := Unit) s1 s2) := by
  unfold capSwapForDelete
  refine ik_when _ (ik_getCap_bind fun c1 σ h1 => ikp_getCap_bind fun c2 h2 hσ => ?_)
  exact hi_capSwap c1 s1 c2 s2 (ioIn_of_slot hσ h1) (ioIn_of_slot hσ h2) σ hσ

theorem ioIn_defaultCap (t : ApiObjectType) (o : ObjRef) (b : Nat) (d : Bool) (S : IoSet) :
    IoIn S (defaultCap t o b d) := by
  intro f l e
  cases t with
  | archObject a => simp only [defaultCap] at e; cases a <;> simp [archDefaultCap] at e
  | _ => simp only [defaultCap] at e; cases e

theorem hi_createCap (t : ApiObjectType) (b : Nat) (u : CslotPtr) (d : Bool) (x : CslotPtr × ObjRef) :
    IKH (HI S) (createCap (Z := Unit) t b u d x) := by
  obtain ⟨dest, oref⟩ := x
  unfold createCap; dsimp only
  refine ik_bind (ik_gets _) fun _ => ik_bind (ik_gets _) fun _ => ik_bind (hv_setCdt _) fun _ =>
    ik_bind (ik_doExtendedOp (fun _ _ h => WLH.view _ _ (by rfl) (by rfl) h) _) fun _ =>
    ik_bind (hv_setOriginal _ _) fun _ => hi_setCap _ _ (ioIn_defaultCap _ _ _ _ S)

theorem capOpt_default_noIo {ty : ApiObjectType} (hty : ty ≠ .untyped) (dev : Bool) (n : Nat) (d : Domain)
    (cref : CnodeIndex) (f l : IoPort) :
    capOpt (some (defaultObject ty dev n d)) cref ≠ some (.archObjectCap (.ioPortCap f l)) := by
  intro h
  cases ty with
  | untyped => exact hty rfl
  | capTableObject =>
    simp only [defaultObject, capOpt] at h
    split_ifs at h with h1
    simp only [emptyCnode] at h
    split_ifs at h with h2
    cases h
  | tcbObject =>
    simp only [defaultObject, capOpt, tcbCnodeMap, defaultTcb, Function.update_apply] at h
    split_ifs at h <;> cases h
  | archObject a => simp only [defaultObject, capOpt] at h; cases h
  | _ => simp only [defaultObject, capOpt] at h; cases h

theorem hi_retypeRegionWith (bA : ApiObjectType → Nat → Nat) (ptr : ObjRef) (n oB : Nat) (ty : ApiObjectType)
    (dev : Bool) : IKH (HI S) (retypeRegionWith (Z := Unit) bA ptr n oB ty dev) := by
  intro σ h y hy f l hh
  obtain ⟨p, cref, hc⟩ := hh
  rcases (SInvU.retypeRegionWith_out hy).2 with e' | ⟨hty, e'⟩
  · rw [e'] at hc; exact h f l ⟨p, cref, hc⟩
  · rw [e'] at hc
    simp only [SInvU.retKh] at hc
    split_ifs at hc
    · exact absurd hc (capOpt_default_noIo hty _ _ _ _ _ _)
    · exact h f l ⟨p, cref, hc⟩

theorem hi_retypeRegion (ptr : ObjRef) (n oB : Nat) (ty : ApiObjectType) (dev : Bool) :
    IKH (HI S) (retypeRegion (Z := Unit) ptr n oB ty dev) := by
  rw [← retypeRegionWith_objBitsApi]; exact hi_retypeRegionWith _ _ _ _ _ _

theorem hi_deleteObjects (ptr : Word) (bits : Nat) : IKH (HI S) (deleteObjects (Z := Unit) ptr bits) := by
  unfold deleteObjects
  refine ik_bind (WLH.msk _ (mt_freeMemory _ _)) fun _ => ik_modify fun σ h => ?_
  intro f l hh
  obtain ⟨p, cref, hc⟩ := hh
  simp only [detype] at hc
  split_ifs at hc
  · simp [capOpt] at hc
  · exact h f l ⟨p, cref, hc⟩

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hi_createCap _ _ _ _ _)
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hi_retypeRegionWith _ _ _ _ _ _)
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hi_retypeRegion _ _ _ _ _)
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hi_deleteObjects _ _)
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hi_capSwapForDelete _ _)

/-! ## `IoK` of the deletion leaves that write no allocated port -/

section K
variable {N : IoPort → Bool}

theorem iok_capDeleteOne (sl : CslotPtr) : IoK N (capDeleteOne (Z := Unit) sl) := by
  unfold capDeleteOne emptySlot
  simp only [postCapDeletion]
  iok_auto

macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_capDeleteOne _)

theorem iok_deletingIrqHandler (irq : Irq) : IoK N (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler; iok_auto

macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_deletingIrqHandler _)

theorem iok_finaliseCap (c : Cap) (fin : Bool) : IoK N (finaliseCap (Z := Unit) c fin) := by
  cases c <;> unfold finaliseCap <;> iok_auto

macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_finaliseCap _ _)

end K

end

end Fl4Proofs.P3.SInvIo
