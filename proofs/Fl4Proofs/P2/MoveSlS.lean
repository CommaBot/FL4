/-
# P2 (line stpost, generation 14): the checked store with slot `CAP0` writes (`PWs`)

p2sl's checked store `gd st R (PW K c lk m0)` (`P2/MoveSl.lean`) allows no write of a capability slot's `CAP0` (a
`DecW` word: it decides the slot's owner, rule 2 of `OwnMap.own`). The frame-cap invocation's Delete arm clears
`dest`'s `CAP0` (Frame → Null). This module adds a **parallel** guard, leaving `PW`, `IW`, `pw_step`,
`run_gd_mguard` untouched:

* `PWs K c lk m0 x a v := PW … ∨ (a ∈ K.slots ∧ ¬ TcbSlot K a ∧ lk a ∧ NullOrFrame (m0 a) ∧ NullOrFrame v)`:
  a `CAP0` write of a Null / Frame value into a locked non-TCB capability slot that held Null / Frame at the entry;
* `IWs` (`IW` and: every such slot still holds a Null / Frame word), `iws_start`;
* `nondec_slotw` (a non-base word of a capability slot decides nothing), `own_upd_slot` (**the lift fact**: writing
  a Null / Frame word over a Null / Frame `CAP0` changes no owner), `stepOK_slot` (such a write passes `StepOK`:
  no owner moves, and its value class is kept since `cls` lumps Null / Frame together);
* `pws_step`, **`run_gds_mguard`**: a successful run on `gd st R (PWs …)` is a run on `mguard st (StepOK …)`, i.e.
  a valid `PathObl.move` for the ownership map; `gds_write_cap0` (the `CAP0` write the new guard allows),
  `wall_pw_pws` (`WAll PW ⊆ WAll PWs`).

Premises: `RegionOK` [J], `UserOK` [J] (as `run_gd_mguard`). No existing statement changes.
-/
import Fl4Proofs.P2.MoveSl
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.OwnMap
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.E2E Fl4Proofs.P2.PathObl
open Fl4Proofs.P2.Serial (Owner ClsOwner)

noncomputable section
open Classical

variable {K : KLayout}

/-- A word of a capability slot other than its base decides nothing. -/
theorem nondec_slotw (hK : RegionOK K) {q x : U64} (hr : region K x = .slot q) (hne : x ≠ q) : ¬ DecW K x := by
  intro hd
  rcases hd with ⟨t, off, ht, ho, rfl⟩ | hs | ⟨p, hp, rfl⟩ | ⟨p, b, hb, rfl⟩
  · rw [(hK.tcb t ht off ho.reg).1] at hr; exact Region.noConfusion hr
  · rw [hK.slot x hs] at hr; cases hr; exact hne rfl
  · rw [(hK.ntfn p hp).1] at hr; exact Region.noConfusion hr
  · rw [(hK.scw p b hb).1] at hr; exact Region.noConfusion hr

/-- **Writing a Null / Frame word over a Null / Frame slot base changes no owner.** -/
theorem own_upd_slot (hK : RegionOK K) {q v : U64} {m : U64 → U64} (hq : q ∈ K.slots)
    (hn : NullOrFrame v ↔ NullOrFrame (m q)) : own K (Function.update m q v) = own K m := by
  have hrq := hK.slot q hq
  funext x
  have ht : ∀ t, K.heap t = some .tcb → ∀ o, tcbOwner (Function.update m q v) t o = tcbOwner m t o :=
    fun t ht o => tcbOwner_upd_other (fun off ho e => by
      have h1 := (hK.tcb t ht off ho.reg).1
      rw [e, hrq] at h1; exact Region.noConfusion h1) o
  cases hr : region K x with
  | node c => simp only [own, hr]
  | obj p => simp only [own, hr]
  | none => simp only [own, hr]
  | tcb t => simp only [own, hr, ht t (hK.tcbOf t x hr)]
  | sc p =>
    have h16 := (hK.scw p x hr).1
    have hne : fld p 16#u64 ≠ q := fun e => by rw [e, hrq] at h16; exact Region.noConfusion h16
    simp only [own, hr, Function.update_of_ne hne]
  | slot p =>
    simp only [own, hr, slotOwner]
    by_cases e : p = q
    · subst e
      simp only [Function.update_self]
      by_cases h1 : NullOrFrame v
      · simp only [h1, hn.1 h1, if_true]
      · have h2 : ¬ NullOrFrame (m p) := fun h => h1 (hn.2 h)
        simp only [h1, h2, if_false]
    · simp only [Function.update_of_ne e]
  | ntfn p =>
    have hp := hK.ntfnOf p x hr
    have h24 := (hK.ntfn p hp).1
    have hne : fld p 24#u64 ≠ q := fun e => by rw [e, hrq] at h24; exact Region.noConfusion h24
    simp only [own, hr, ntfnOwner, Function.update_of_ne hne]
    by_cases hd : K.heap (m (fld p 24#u64)) = some .tcb
    · have ha := (hK.tcb _ hd oAFFINITY (Or.inl rfl)).1
      have hne' : fld (m (fld p 24#u64)) oAFFINITY ≠ q := fun e => by
        rw [e, hrq] at ha; exact Region.noConfusion ha
      simp only [hd, Function.update_of_ne hne', if_true]
    · simp only [hd, ↓reduceIte]

theorem nof_zero : NullOrFrame 0#u64 := Or.inl (by simp)

section st
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **A Null / Frame write over a Null / Frame `CAP0` of a non-TCB capability slot passes the check.** -/
theorem stepOK_slot (hK : RegionOK K) (hU : UserOK K) {m0 : U64 → U64} {c : U64} {lk : U64 → Prop}
    {s : S} {q v : U64} (hq : q ∈ K.slots) (hT : ¬ TcbSlot K q) (hn : NullOrFrame (L.mem s q))
    (hv : NullOrFrame v) :
    PathObl.StepOK (own K) (cls K) (ko K m0) (· ∈ K.user) c lk (L.mem s) (L.mem (L.wr s q v)) := by
  have ha : Aligned q := (hU.slot q hq).1
  have e : own K (L.mem (L.wr s q v)) = own K (L.mem s) := by
    rw [own_wr hK hU ha, own_upd_slot hK hq ⟨fun _ => hn, fun _ => hv⟩]
  refine ⟨fun x hx => absurd (congrFun e x) hx, fun x hx _ => ?_⟩
  by_cases hd : DecW K x
  · have hxa := (decW_ok hU hd).1
    by_cases exq : x = q
    · subst exq
      left
      unfold cls
      rw [hK.slot x hq, mem_wr_upd ha ha, Function.update_self]
      simp only [true_and, hT, not_false_eq_true, hv, hn, and_self, if_true]
    · exfalso; apply hx
      rw [mem_wr_upd ha hxa, Function.update_of_ne exq]
  · exact Or.inr (Or.inr (ko_free_of_nondec hK hd m0))

variable (K) in
/-- **The checked store's writes, with slot `CAP0` writes** (module docstring). -/
def PWs (c : U64) (lk : U64 → Prop) (m0 : U64 → U64) (x : S) (a v : U64) : Prop :=
  PW (L := L) K c lk m0 x a v ∨ (a ∈ K.slots ∧ ¬ TcbSlot K a ∧ lk a ∧ NullOrFrame (m0 a) ∧ NullOrFrame v)

variable (K) in
/-- The invariant the `PWs` writes keep: `IW`, and every locked non-TCB slot holding Null / Frame at the entry still
does. -/
def IWs (c : U64) (lk : U64 → Prop) (m0 : U64 → U64) (x : S) : Prop :=
  IW (L := L) K c lk m0 x ∧
    ∀ q ∈ K.slots, ¬ TcbSlot K q → lk q → NullOrFrame (m0 q) → NullOrFrame (L.mem x q)

theorem iws_start {c : U64} {lk : U64 → Prop} (s : S) : IWs (L := L) K c lk (L.mem s) s :=
  ⟨iw_start s, fun _ _ _ _ h => h⟩

/-- A slot base is no `PW` write target. -/
theorem pw_ne_slot (hK : RegionOK K) {c : U64} {lk : U64 → Prop} {m0 : U64 → U64} {x : S} {a v q : U64}
    (hP : PW (L := L) K c lk m0 x a v) (hq : q ∈ K.slots) : a ≠ q := by
  rintro rfl
  rcases hP with ⟨-, hd⟩ | ⟨d, hdT, -, e, -⟩ | ⟨d, hdT, -, e, -⟩
  · exact hd (Or.inr (Or.inl hq))
  · have h1 := (hK.tcb d hdT oSTATE (Or.inr (Or.inl rfl))).1
    rw [← e, hK.slot _ hq] at h1; exact Region.noConfusion h1
  · have h1 := (hK.tcb d hdT oBLOCK_OBJ (Or.inr (Or.inr (Or.inl rfl)))).1
    rw [← e, hK.slot _ hq] at h1; exact Region.noConfusion h1

/-- **One `PWs` write**: it passes `StepOK` and keeps `IWs`. -/
theorem pws_step (hK : RegionOK K) (hU : UserOK K) {m : U64 → U64} {c : U64} {lk : U64 → Prop}
    {m0 : U64 → U64} (hm : ∀ d, K.heap d = some .tcb → m (fld d oAFFINITY) = m0 (fld d oAFFINITY))
    {x x' : S} {a v : U64} (hI : IWs (L := L) K c lk m0 x) (hP : PWs (L := L) K c lk m0 x a v)
    (hw : st.write x a v = ok x') :
    StepOK (own K) (cls K) (ko K m) (· ∈ K.user) c lk (L.mem x) (L.mem x') ∧
      IWs (L := L) K c lk m0 x' := by
  rcases hP with hP | ⟨hq, hT, hl, hn0, hv⟩
  · obtain ⟨h1, h2⟩ := pw_step hK hU hm hI.1 hP hw
    refine ⟨h1, h2, fun q hq hT hl hn0 => ?_⟩
    rw [L.write_eq] at hw
    obtain rfl : L.wr x a v = x' := by
      have h2 : (ok (L.wr x a v) : Result S) ⦃ r => r = x' ⦄ := by rw [hw]; exact (WP.spec_ok _).2 rfl
      exact (WP.spec_ok (L.wr x a v)).1 h2
    have hne := pw_ne_slot hK hP hq
    have hqa : Aligned q := (hU.slot q hq).1
    have ha : Aligned a := by
      rcases hP with ⟨ha, -⟩ | ⟨d, hdT, -, rfl, -⟩ | ⟨d, hdT, -, rfl, -⟩
      · exact ha
      · exact (hU.tcb d hdT oSTATE (Or.inr (Or.inl rfl))).1
      · exact (hU.tcb d hdT oBLOCK_OBJ (Or.inr (Or.inr (Or.inl rfl)))).1
    rw [mem_wr_upd ha hqa, Function.update_of_ne (Ne.symm hne)]
    exact hI.2 q hq hT hl hn0
  · rw [L.write_eq] at hw
    obtain rfl : L.wr x a v = x' := by
      have h2 : (ok (L.wr x a v) : Result S) ⦃ r => r = x' ⦄ := by rw [hw]; exact (WP.spec_ok _).2 rfl
      exact (WP.spec_ok (L.wr x a v)).1 h2
    have ha : Aligned a := (hU.slot a hq).1
    refine ⟨stepOK_slot hK hU hq hT (hI.2 a hq hT hl hn0) hv, fun d hdT => ?_, fun q hq' hT' hl' hn' => ?_⟩
    · have ne : ∀ off, DecOff off → fld d off ≠ a := fun off ho e => by
        have h1 := (hK.tcb d hdT off ho.reg).1
        rw [e, hK.slot a hq] at h1; exact Region.noConfusion h1
      rw [mem_wr_dec hU ha (decW_tcb hdT (Or.inl rfl)) (ne _ (Or.inl rfl)),
        mem_wr_dec hU ha (decW_tcb hdT (Or.inr (Or.inl rfl))) (ne _ (Or.inr (Or.inl rfl))),
        mem_wr_dec hU ha (decW_tcb hdT (Or.inr (Or.inr (Or.inl rfl)))) (ne _ (Or.inr (Or.inr (Or.inl rfl))))]
      exact hI.1 d hdT
    · by_cases e : q = a
      · subst e; rw [mem_wr_upd ha ha, Function.update_self]; exact hv
      · rw [mem_wr_upd ha (hU.slot q hq').1, Function.update_of_ne e]
        exact hI.2 q hq' hT' hl' hn'

variable {A X : Type}

/-- **From the checked store with slot `CAP0` writes to `mguard`**, for a tree (`run_gd_mguard` for `PWs`). -/
theorem run_gds_mguard (hK : RegionOK K) (hU : UserOK K) {m : U64 → U64} {lk : U64 → Prop} {s : S}
    (hm : ∀ d, K.heap d = some .tcb → m (fld d oAFFINITY) = L.mem s (fld d oAFFINITY))
    {ar : machine.Arch A} {R : U64 → Prop} (p : SProg X) {a : A} {r : X × S × A}
    (h : interp (gd st R (PWs (L := L) K (L.cpu s) lk (L.mem s))) ar p s a = ok r) :
    interp (mguard st fun x y => StepOK (own K) (cls K) (ko K m) (· ∈ K.user) (L.cpu s) lk (L.mem x) (L.mem y))
      ar p s a = ok r :=
  interp_gd (I := IWs (L := L) K (L.cpu s) lk (L.mem s))
    (fun _ _ _ _ hI hP hw => pws_step hK hU hm hI hP hw) p s a r (iws_start s) h

/-- The slot `CAP0` write the new guard allows. -/
theorem gds_write_cap0 {R : U64 → Prop} {c : U64} {lk : U64 → Prop} {m0 : U64 → U64} {x : S} {q v : U64}
    (hq : q ∈ K.slots) (hT : ¬ TcbSlot K q) (hl : lk q) (hn : NullOrFrame (m0 q)) (hv : NullOrFrame v) :
    (gd st R (PWs (L := L) K c lk m0)).write x q v = st.write x q v :=
  gd_write (Or.inr ⟨hq, hT, hl, hn, hv⟩)

/-- `PW` writes are `PWs` writes. -/
theorem wall_pw_pws {c : U64} {lk : U64 → Prop} {m0 : U64 → U64} {a : U64}
    (h : WAll (PW (L := L) K c lk m0) a) : WAll (PWs (L := L) K c lk m0) a :=
  fun x v => Or.inl (h x v)

/-- A `STATE` write the new guard allows (`PW`'s). -/
theorem gds_write_state {R : U64 → Prop} {c : U64} {lk : U64 → Prop} {m0 : U64 → U64} {x : S}
    {d v : U64} (hdT : K.heap d = some .tcb) (hS : Safe0 c lk m0 d)
    (hq : QueuedState v → lk (L.mem x (fld d oBLOCK_OBJ))) :
    (gd st R (PWs (L := L) K c lk m0)).write x (stA d) v = st.write x (stA d) v := by
  rw [stA_fld]
  exact gd_write (Or.inl (Or.inr (Or.inl ⟨d, hdT, hS, rfl, hq⟩)))

end st

end

end Fl4Proofs.P2.OwnMap
