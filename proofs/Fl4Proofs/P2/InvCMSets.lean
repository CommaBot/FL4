/-
# P2 (shared, stpost gen 14 / slhuf gen 9): the user-word read and write sets of the frame-cap invocation path

**Copied verbatim from par/slhuf3 81800a74c `P2/InvCM.lean`, section `sets`** (`InvCMRS`, `InvCMWS`, `ioRS_cm`,
`ioWS_cm`, `cmRS_nu`, `cmWS_nu`, `cmRS_eq`, `cmWS_eq`, `alt_cm_io`, `altOf_cm_io`, `grd_sub`, `IoWr.mono`,
`IsProgOn.mono`; same names, same statements, same proofs), so that the Copy / Mint path (slhuf) and the uncut
CNodeDelete path (stpost) share one definition. At integration `InvCM.lean` drops its `sets` section and imports this
module.

Also `racyU_monoR`, `tchU_monoR`, **`onceU_monoR`**: slhuf gen 7's `racy_monoR` / `tch_monoR` / `once_monoR`
(`P2/SlOnceL.lean`) under new names (`SlOnceL` imports the whole user-word loop; it is not on this branch), `Once` for a
smaller read set gives `Once` for a larger one.

No premise. No existing statement changes.
-/
import Fl4Proofs.P2.InvAcc
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField oAFFINITY)
open Fl4Proofs.P2.E2E (Once ReadOnce)

/-! ## The sets -/

section sets
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **What the Copy / Mint path may read**: aligned user words (the caller's IPC buffer among them) and `IoRS`. -/
def InvCMRS (K : KLayout) (Locks : S → U64 → Prop) (s : S) (x : U64) : Prop :=
  Aligned x ∧ (x ∈ K.user ∨ IoRS (st := st) K Locks s x)

/-- **What an accepted Copy / Mint run may write**: aligned user words (a `Sys` error's reply writes the caller's
buffer) and `IoWS`. -/
def InvCMWS (K : KLayout) (Locks : S → U64 → Prop) (s : S) (x : U64) : Prop :=
  Aligned x ∧ (x ∈ K.user ∨ IoWS (st := st) K Locks s x)

variable {K : KLayout} {Locks : S → U64 → Prop} {s : S} {x : U64}

theorem ioRS_cm (h : IoRS (st := st) K Locks s x) : InvCMRS (st := st) K Locks s x := ⟨h.1, Or.inr h⟩

theorem ioWS_cm (h : IoWS (st := st) K Locks s x) : InvCMWS (st := st) K Locks s x := ⟨h.1, Or.inr h⟩

theorem cmRS_nu (h : InvCMRS (st := st) K Locks s x) (hu : x ∉ K.user) : IoRS (st := st) K Locks s x :=
  h.2.resolve_left hu

theorem cmWS_nu (h : InvCMWS (st := st) K Locks s x) (hu : x ∉ K.user) : IoWS (st := st) K Locks s x :=
  h.2.resolve_left hu

/-- `InvCMRS` is user-write independent where `IoRS` is. -/
theorem cmRS_eq {s' : S} (h : IoRS (st := st) K Locks s' = IoRS (st := st) K Locks s) :
    InvCMRS (st := st) K Locks s' = InvCMRS (st := st) K Locks s := by
  funext y; unfold InvCMRS; rw [h]

/-- `InvCMWS` is user-write independent where `IoWS` is. -/
theorem cmWS_eq {s' : S} (h : IoWS (st := st) K Locks s' = IoWS (st := st) K Locks s) :
    InvCMWS (st := st) K Locks s' = InvCMWS (st := st) K Locks s := by
  funext y; unfold InvCMWS; rw [h]

/-- **An alternative for `InvCMRS s` is one for `IoRS s`.** -/
theorem alt_cm_io {cls : U64 → U64 → U64} {ko : U64 → Serial.ClsOwner U64} {s' : S}
    (Al : Alt st (InvCMRS (st := st) K Locks s) cls ko (· ∈ K.user) s s') :
    Alt st (IoRS (st := st) K Locks s) cls ko (· ∈ K.user) s s' :=
  ⟨Al.cpu, Al.ksb, Al.masks, fun y hy => Al.read y (ioRS_cm hy),
    fun y hy hu ho => Al.clsEq y (fun h => hy (cmRS_nu h hu)) hu ho⟩

/-- `AltOf` for `InvCMRS` lies in `AltOf` for `IoRS`. -/
theorem altOf_cm_io {P : S → Prop} {cls : U64 → U64 → U64} {ko : U64 → Serial.ClsOwner U64} {s' : S}
    (h : AltOf st P (InvCMRS (st := st) K Locks) cls ko (· ∈ K.user) s') :
    AltOf st P (IoRS (st := st) K Locks) cls ko (· ∈ K.user) s' :=
  let ⟨s0, hP, Al⟩ := h; ⟨s0, hP, alt_cm_io Al⟩

/-- A store guarded to `R` reads every word of a smaller `R'` as `st`. -/
theorem grd_sub {R R' W : U64 → Prop} (h : ∀ y, R' y → R y) : GRd (guard st R W) st R' where
  read hy _ := guard_read (h _ hy)
  read_pair hy h8 _ := guard_read_pair (h _ hy) (h _ h8)
  ks_base := rfl
  cur_cpu := rfl
  frame_masks := rfl

/-- `IoWr` for a larger write set. -/
theorem IoWr.mono {W W' : U64 → Prop} {Z : U64 → Nat} (h : ∀ y, W y → W' y) (w : IoWr st W Z s) :
    IoWr st W' Z s :=
  ⟨fun o h1 h2 => h _ (w.nd o h1 h2), fun r hr => h _ (w.reg r hr), fun b hb hi => h _ (w.ring b hb hi),
    h _ w.cons⟩

/-- `IsProgOn` on a smaller set of entry states. -/
theorem IsProgOn.mono {A X : Type} {f : machine.Store S → S → A → Result (X × S × A)} {ar : machine.Arch A}
    {G G' : S → Prop} {q : SProg X} (h : IsProgOn f ar st G q) (hG : ∀ y, G' y → G y) :
    IsProgOn f ar st G' q := fun st' N y hy a => h st' N y (hG y hy) a

end sets

section onceU
open Classical
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} {User : U64 → Prop}

theorem racyU_monoR {R R' : U64 → Prop} {Wd : Set U64} {q : U64} (hR : ∀ b, R b → R' b)
    (h : E2E.Racy R' User Wd q) : E2E.Racy R User Wd q := by
  unfold E2E.Racy at *
  rintro ⟨h1, h2⟩
  exact h ⟨h1, h2.imp_left (hR q)⟩

theorem tchU_monoR {R R' : U64 → Prop} {Wd T T' : Set U64} {q : U64} (hR : ∀ b, R b → R' b)
    (hT : T' ⊆ T) : E2E.tch R' User Wd q T' ⊆ E2E.tch R User Wd q T := by
  by_cases h' : E2E.Racy R' User Wd q
  · have h := racyU_monoR hR h'
    have e1 : E2E.tch R' User Wd q T' = insert q T' := by unfold E2E.tch; exact if_pos h'
    have e2 : E2E.tch R User Wd q T = insert q T := by unfold E2E.tch; exact if_pos h
    rw [e1, e2]
    exact Set.insert_subset_insert hT
  · have e1 : E2E.tch R' User Wd q T' = T' := by unfold E2E.tch; exact if_neg h'
    rw [e1]
    exact hT.trans E2E.tch_sub

/-- **`Once` for a smaller read set gives `Once` for a larger one** (fewer racy words), from a smaller
touched set. -/
theorem onceU_monoR {R R' : U64 → Prop} (hR : ∀ b, R b → R' b) {X : Type} (p : SProg X) :
    ∀ (Wd T T' : Set U64) (s : S) (a : A),
      Once st ar R User Wd T p s a → T' ⊆ T → Once st ar R' User Wd T' p s a := by
  induction p with
  | ret x => intros; simp only [Once]
  | err e => intros; simp only [Once]
  | rd q k ih =>
    intro Wd T T' s a h hT
    simp only [Once] at h ⊢
    exact ⟨fun hr hq => h.1 (racyU_monoR hR hr) (hT hq),
      fun v hv => ih v _ _ _ s a (h.2 v hv) (tchU_monoR hR hT)⟩
  | rdp q k ih =>
    intro Wd T T' s a h hT
    simp only [Once] at h ⊢
    exact ⟨fun hr hq => h.1 (racyU_monoR hR hr) (hT hq),
      fun hr hq => h.2.1 (racyU_monoR hR hr) (tchU_monoR hR hT hq),
      fun v hv => ih v _ _ _ s a (h.2.2 v hv) (tchU_monoR hR (tchU_monoR hR hT))⟩
  | wr q v k ih =>
    intro Wd T T' s a h hT
    simp only [Once] at h ⊢
    intro s' hs'
    have h1 := h s' hs'
    by_cases hu : User q
    · simp only [if_pos hu] at h1 ⊢
      exact ih _ _ _ s' a h1 (Set.insert_subset_insert hT)
    · simp only [if_neg hu] at h1 ⊢
      exact ih _ _ _ s' a h1 hT
  | zero q n k ih => intro Wd T T' s a h; simp only [Once] at h
  | clr q n k ih => intro Wd T T' s a h; simp only [Once] at h
  | ksb k ih =>
    intro Wd T T' s a h hT
    simp only [Once] at h ⊢
    exact fun v hv => ih v _ _ _ s a (h v hv) hT
  | cpu k ih =>
    intro Wd T T' s a h hT
    simp only [Once] at h ⊢
    exact fun v hv => ih v _ _ _ s a (h v hv) hT
  | masks k ih =>
    intro Wd T T' s a h hT
    simp only [Once] at h ⊢
    exact fun v hv => ih v _ _ _ s a (h v hv) hT
  | arch op k ih =>
    intro Wd T T' s a h hT
    simp only [Once] at h ⊢
    exact fun v a' hv => ih v _ _ _ s a' (h v a' hv) hT

end onceU

end Fl4Proofs.P2.PathObl
