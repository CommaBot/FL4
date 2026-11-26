/-
# P2 (line p3mc, gen 4): `ViewSafe` from narrowed run facts at the view (`viewSafeAt_of_narrow`)

`E2E.LocalPath.safeV` (`P2/ViewSafeGen.lean`) at `ρv := CoreView.view K c ρ`, for the ownership map `ownP K`, with the
sets fixed here (namespace `CoreView`):
* `VN K c ρ x`: the view keeps `x`'s value and owner (`ρv x = ρ x`, `ownP ρv x = ownP ρ x`);
* `VKc K c ρ x`: the view keeps `x`'s class owner (`ko K ρv x = ko K ρ x`); `ko K μ = ko K ρ` follows from `VEq ρ μ`
  (`ko_of_veq`: `ko` reads only `AFFINITY` words, which are the gate's);
* `VDD K c ρ y`: a word of a thread or SC homed off `c` in `ρ`, or of a notification; `VDec K c ρ q`: a word that decides
  the owner of some `VDD` word; `VNW K c ρ q := VN ∧ VKc ∧ ¬ VDec`: the words a path may write;
* `vown_off` (`hO1`: off `VDD`, the owner is fixed by the words the view keeps) and `vown_upd` (`hO2`: a write of a
  `¬ VDec` word changes no owner on `VDD`), both proved from `RegionOKP` / `UserOKP`;
* **`NarrowV P K c ρ`**: the two narrowed run facts of a path at the view: an accepted run from a view start state runs
  on the store guarded to reads of `VN ∧ (RS ∨ VKc)` words and writes of `VNW` words, and so does every declined run
  at every alternative of the start state;
* **`viewSafeAt_of_narrow`**: `NarrowV` of the path at every view gives the `ViewSafe` conclusion for that path.

No premise. No existing statement changed.
-/
import Fl4Proofs.P2.ViewSafeGen
import Fl4Proofs.P2.E2EPU7
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.CoreView
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.PathObl
open Fl4Proofs.P2.OwnMap
open Fl4Proofs.P2.OwnMapP (KLayoutP ownP RegionOKP UserOKP ownP_pte ownP_off)
open Fl4Proofs.P2.OwnMapV (ownV_off ownV_on_mem)

noncomputable section
open Classical

/-- The view keeps the value and the owner of `x`. -/
def VN (K : KLayoutP) (c : U64) (ρ : U64 → U64) (x : U64) : Prop :=
  view K.toKLayout c ρ x = ρ x ∧ ownP K (view K.toKLayout c ρ) x = ownP K ρ x

/-- The view keeps the class owner of `x`. -/
def VKc (K : KLayout) (c : U64) (ρ : U64 → U64) (x : U64) : Prop :=
  ko K (view K c ρ) x = ko K ρ x

/-- A word of a thread or SC homed off `c` in `ρ`, or of a notification. -/
def VDD (K : KLayout) (c : U64) (ρ : U64 → U64) (y : U64) : Prop :=
  (∃ t, region K y = .tcb t ∧ ρ (fld t oAFFINITY) ≠ c) ∨ (∃ p, region K y = .sc p ∧ ρ (fld p 16#u64) ≠ c) ∨
    (∃ p, region K y = .ntfn p)

/-- A word deciding the owner of some `VDD` word. -/
def VDec (K : KLayout) (c : U64) (ρ : U64 → U64) (q : U64) : Prop :=
  (∃ t off, K.heap t = some .tcb ∧ ρ (fld t oAFFINITY) ≠ c ∧ OwnMap.DecOff off ∧ q = fld t off) ∨
    (∃ p, K.heap p = some .ntfn ∧ q = fld p 24#u64) ∨ (∃ t, K.heap t = some .tcb ∧ q = fld t oAFFINITY) ∨
    (∃ p b, region K b = .sc p ∧ ρ (fld p 16#u64) ≠ c ∧ q = fld p 16#u64)

/-- The words a path at the view may write. -/
def VNW (K : KLayoutP) (c : U64) (ρ : U64 → U64) (q : U64) : Prop :=
  VN K c ρ q ∧ VKc K.toKLayout c ρ q ∧ ¬ VDec K.toKLayout c ρ q

theorem decOff_list {off : U64} (h : OwnMap.DecOff off) : off = oAFFINITY ∨ off = oSTATE ∨ off = oBLOCK_OBJ ∨
    off = oREPLY_OBJ ∨ off = oTIMER_DEADLINE ∨ off = oTIMER_HEIGHT := OwnMap.DecOff.reg h

/-- **`hO1` for `ownP`**: off `VDD`, the owner is fixed by the aligned kernel words the view keeps. -/
theorem vown_off {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K) {c : U64} {ρ : U64 → U64}
    (m m' : U64 → U64) (h : ∀ x, Aligned x → x ∉ K.user → view K.toKLayout c ρ x = ρ x → m x = m' x)
    (y : U64) (hy : ¬ VDD K.toKLayout c ρ y) : ownP K m y = ownP K m' y := by
  have hK0 := hK.base.base
  have hd : ∀ d, DecW K.toKLayout d → view K.toKLayout c ρ d = ρ d → m d = m' d := fun d hd hv =>
    h d (decW_ok hU.base.base hd).1 (decW_ok hU.base.base hd).2 hv
  by_cases hp : y ∈ K.ptes
  · rw [ownP_pte hp, ownP_pte hp]
  rw [ownP_off hp, ownP_off hp]
  by_cases hv : ∃ v, Fl4Proofs.P2.OwnMapV.InVcpu K.toKLayoutV v y
  · exact ownV_on_mem hK.base hv
  rw [ownV_off hv, ownV_off hv]
  cases hr : region K.toKLayout y with
  | tcb t =>
    have ht := hK0.tcbOf t y hr
    have ha : ρ (fld t oAFFINITY) = c := by
      by_contra hne; exact hy (Or.inl ⟨t, hr, hne⟩)
    have e : ∀ off, OwnMap.DecOff off → m (fld t off) = m' (fld t off) := fun off ho =>
      hd _ (decW_tcb ht ho) (view_tcb_fld hK0 ht ha (decOff_list ho))
    simp only [own, hr, tcbOwner, e oAFFINITY (Or.inl rfl), e oSTATE (Or.inr (Or.inl rfl)),
      e oBLOCK_OBJ (Or.inr (Or.inr (Or.inl rfl))), e oTIMER_DEADLINE (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
      e oTIMER_HEIGHT (Or.inr (Or.inr (Or.inr (Or.inr rfl))))]
  | sc p =>
    have ha : ρ (fld p 16#u64) = c := by
      by_contra hne; exact hy (Or.inr (Or.inl ⟨p, hr, hne⟩))
    have e : m (fld p 16#u64) = m' (fld p 16#u64) :=
      hd _ (Or.inr (Or.inr (Or.inr ⟨p, y, hr, rfl⟩))) (view_sc_home (hK0.scw p y hr).1 ha)
    simp only [own, hr, e]
  | ntfn p => exact absurd (Or.inr (Or.inr ⟨p, hr⟩)) hy
  | slot p =>
    have hs := hK0.slotOf p y hr
    have e : m p = m' p :=
      hd _ (Or.inr (Or.inl hs)) (view_none (by simp only [repl, repl2, hK0.slot p hs]))
    simp only [own, hr, slotOwner, e]
  | node d => simp only [own, hr]
  | obj p => simp only [own, hr]
  | none => simp only [own, hr]

/-- **`hO2` for `ownP`**: a write of a word that decides no `VDD` word's owner changes no owner on `VDD`. -/
theorem vown_upd {K : KLayoutP} (hK : RegionOKP K) {c : U64} {ρ : U64 → U64} {q : U64}
    (hq : ¬ VDec K.toKLayout c ρ q) (m : U64 → U64) (v y : U64) (hy : VDD K.toKLayout c ρ y) :
    ownP K (Function.update m q v) y = ownP K m y := by
  have hK0 := hK.base.base
  by_cases hp : y ∈ K.ptes
  · rw [ownP_pte hp, ownP_pte hp]
  rw [ownP_off hp, ownP_off hp]
  by_cases hv : ∃ v, Fl4Proofs.P2.OwnMapV.InVcpu K.toKLayoutV v y
  · exact ownV_on_mem hK.base hv
  rw [ownV_off hv, ownV_off hv]
  rcases hy with ⟨t, hr, ha⟩ | ⟨p, hr, ha⟩ | ⟨p, hr⟩
  · have ht := hK0.tcbOf t y hr
    have e : ∀ off, OwnMap.DecOff off → Function.update m q v (fld t off) = m (fld t off) := fun off ho =>
      Function.update_of_ne (fun e => hq (Or.inl ⟨t, off, ht, ha, ho, e.symm⟩)) _ _
    simp only [own, hr, tcbOwner, e oAFFINITY (Or.inl rfl), e oSTATE (Or.inr (Or.inl rfl)),
      e oBLOCK_OBJ (Or.inr (Or.inr (Or.inl rfl))), e oTIMER_DEADLINE (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
      e oTIMER_HEIGHT (Or.inr (Or.inr (Or.inr (Or.inr rfl))))]
  · have e : Function.update m q v (fld p 16#u64) = m (fld p 16#u64) :=
      Function.update_of_ne (fun e => hq (Or.inr (Or.inr (Or.inr ⟨p, y, hr, ha, e.symm⟩)))) _ _
    simp only [own, hr, e]
  · have hn := hK0.ntfnOf p y hr
    have e : Function.update m q v (fld p 24#u64) = m (fld p 24#u64) :=
      Function.update_of_ne (fun e => hq (Or.inr (Or.inl ⟨p, hn, e.symm⟩))) _ _
    simp only [own, hr, ntfnOwner, e]
    by_cases hb : K.heap (m (fld p 24#u64)) = some .tcb
    · have e2 : Function.update m q v (fld (m (fld p 24#u64)) oAFFINITY) = m (fld (m (fld p 24#u64)) oAFFINITY) :=
        Function.update_of_ne (fun e => hq (Or.inr (Or.inr (Or.inl ⟨_, hb, e.symm⟩)))) _ _
      rw [if_pos hb, if_pos hb, e2]
    · rw [if_neg hb, if_neg hb]

/-- **`ko` at a memory `μ` that `c` cannot tell from `ρ`** is `ko` at `ρ` (`ko` reads only gate words). -/
theorem ko_of_veq {K : KLayoutP} (hK : RegionOKP K) {c : U64} {hs : U64 → Prop} {ρ μ : U64 → U64}
    (hV : Serial.VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ) :
    OwnMap.ko K.toKLayout μ = OwnMap.ko K.toKLayout ρ :=
  (Fl4Proofs.P2.E2EP.ko_congrP hK fun y hy => hV.2.1 y (by rw [hy]; exact Or.inr rfl)).symm

/-- **The narrowed run facts of a path at core `c`'s view of `ρ`** (module docstring). -/
def NarrowV {K : KLayoutP} {c : U64} {ρ : U64 → U64}
    (P : E2E.LocalPath (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout (view K.toKLayout c ρ))
      (· ∈ K.user)) : Prop :=
  (∀ s0 a r, P.Pre s0 → P.L.cpu s0 = c → (∀ x, Aligned x → x ∉ K.user → P.L.mem s0 x = view K.toKLayout c ρ x) →
    P.F P.ar P.st s0 a = ok r → P.Acc r.1 →
    P.F P.ar (guard P.st (fun b => VN K c ρ b ∧ (P.RS s0 b ∨ VKc K.toKLayout c ρ b)) (VNW K c ρ)) s0 a = ok r) ∧
  (∀ s0 a r, P.Pre s0 → P.L.cpu s0 = c → (∀ x, Aligned x → x ∉ K.user → P.L.mem s0 x = view K.toKLayout c ρ x) →
    P.F P.ar P.st s0 a = ok r → ¬ P.Acc r.1 → ∀ s' r',
      @Alt _ P.st P.L (P.RS s0) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout (view K.toKLayout c ρ))
        (· ∈ K.user) s0 s' → P.F P.ar P.st s' a = ok r' →
    P.F P.ar (guard P.st (fun b => VN K c ρ b ∧ (P.RS s0 b ∨ VKc K.toKLayout c ρ b)) (VNW K c ρ)) s' a = ok r')

/-- **`ViewSafe`'s conclusion for one path from `NarrowV`** (module docstring). -/
theorem viewSafeAt_of_narrow {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K) {c : U64} {hs : U64 → Prop}
    {ρ μ : U64 → U64} {q : E2E.SP}
    (P : E2E.LocalPath (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout (view K.toKLayout c ρ))
      (· ∈ K.user)) (hN : NarrowV P)
    (hV : Serial.VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    (hS : E2E.StartAt P c hs (view K.toKLayout c ρ) q) :
    Serial.Safe (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ q := by
  have hko := ko_of_veq hK hV
  exact E2E.LocalPath.safeV P (Fl4Proofs.P2.OwnMapP.moveHeldP hK) (Fl4Proofs.P2.OwnMapP.ownDepP hK hU) hS hV
    (N := VN K c ρ) (Kc := VKc K.toKLayout c ρ) (NW := VNW K c ρ) (DD := VDD K.toKLayout c ρ)
    (fun x h => h.1) (fun x h => h.2) (fun x h => by rw [hko]; exact h) (fun x h => ⟨h.1, h.2.1⟩)
    (fun m m' h y hy => vown_off hK hU m m' h y hy) (fun q hq m v y hy => vown_upd hK hq.2.2 m v y hy)
    (NR := fun s0 b => VN K c ρ b ∧ (P.RS s0 b ∨ VKc K.toKLayout c ρ b)) (NWs := fun _ => VNW K c ρ)
    (fun _ _ h => h) (fun _ _ h => h) hN.1 hN.2

end
end Fl4Proofs.P2.CoreView
