/-
# P2 (line p2sl): `PathObl.move` from a run on the checked store `gd`

`PathObl.move` asks that a local path's run pass `StepOK` at every write (the
run on `mguard st Q` succeeds as the real one). For FL4's ownership map this
file reduces it to a run on the checked store `gd st R (PW K c lk m0)`
(`P2/GSt.lean`), where `PW` allows, at a state `x`, a write of `v` to `a` when

* `a` is an aligned word deciding no owner (any state, any value), or
* `a` is the `STATE` of a thread `d` that is `Safe0` at the entry (homed on
  core `c`; if queued at the entry, on a held lock), and `v` is not a queued
  state unless `d`'s current `BLOCK_OBJ` is a held lock, or
* `a` is the `BLOCK_OBJ` of such a thread, and `v` is a held lock if `d` is
  queued now.

`run_gd_mguard` (`interp_gd` with the invariant `IW`: home cores as at the
entry, and every `Safe0` thread queued only on a held lock) turns a successful
run on that `gd` into the run on `mguard` for `StepOK (own K) (cls K) (ko K m)`;
`move_of_gd` does the same for a body through `IsProg` [P].

With `PW` the guard leaves (`<f>.guard`, stated for any `GWr gS st W`) take
`W := WAll (PW …)`, which holds of every aligned word deciding nothing
(`wall_nondec`); the `STATE` / `BLOCK_OBJ` writes are leaf hypotheses of their
own (`gd_write_state`, `gd_write_bobj`).

Premises: `RegionOK` [J], `UserOK` [J] of the layout; `hm`: `ko`'s memory `m`
agrees with the entry state on every TCB's `AFFINITY` (gate-owned, `StartAt`).
-/
import Fl4Proofs.P2.GSt
import Fl4Proofs.P2.MoveOwn
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.OwnMap
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.E2E Fl4Proofs.P2.PathObl
open Fl4Proofs.P2.Serial (Owner ClsOwner)

noncomputable section
open Classical

variable {K : KLayout}

theorem stA_fld (t : U64) : stA t = fld t oSTATE := by
  unfold stA fld oSTATE
  congr 1
  exact UScalar.eq_of_val_eq (by simp)

theorem blockA_fld (t : U64) : blockA t = fld t oBLOCK_OBJ := rfl
theorem affA_fld (t : U64) : affA t = fld t oAFFINITY := rfl

/-- A thread fit for `STATE` / `BLOCK_OBJ` writes, at the entry memory `m0`:
homed on core `c`, and queued at the entry only on a held lock. -/
def Safe0 (c : U64) (lk : U64 → Prop) (m0 : U64 → U64) (d : U64) : Prop :=
  m0 (fld d oAFFINITY) = c ∧ (QueuedState (m0 (fld d oSTATE)) → lk (m0 (fld d oBLOCK_OBJ)))

section st
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

variable (K) in
/-- The writes the checked store allows (module docstring). -/
def PW (c : U64) (lk : U64 → Prop) (m0 : U64 → U64) (x : S) (a v : U64) : Prop :=
  (Aligned a ∧ ¬ DecW K a) ∨
  (∃ d, K.heap d = some .tcb ∧ Safe0 c lk m0 d ∧ a = fld d oSTATE ∧
    (QueuedState v → lk (L.mem x (fld d oBLOCK_OBJ)))) ∨
  (∃ d, K.heap d = some .tcb ∧ Safe0 c lk m0 d ∧ a = fld d oBLOCK_OBJ ∧
    (QueuedState (L.mem x (fld d oSTATE)) → lk v))

variable (K) in
/-- The invariant the allowed writes keep. -/
def IW (c : U64) (lk : U64 → Prop) (m0 : U64 → U64) (x : S) : Prop :=
  ∀ d, K.heap d = some .tcb → L.mem x (fld d oAFFINITY) = m0 (fld d oAFFINITY) ∧
    (Safe0 c lk m0 d → QueuedState (L.mem x (fld d oSTATE)) → lk (L.mem x (fld d oBLOCK_OBJ)))

theorem iw_start {c : U64} {lk : U64 → Prop} (s : S) : IW (L := L) K c lk (L.mem s) s :=
  fun _ _ => ⟨rfl, fun h => h.2⟩

theorem mem_wr_dec (hU : UserOK K) {x : S} {a v d : U64} (ha : Aligned a) (hd : DecW K d) (hne : d ≠ a) :
    L.mem (L.wr x a v) d = L.mem x d := by
  rw [mem_wr_upd ha (decW_ok hU hd).1, Function.update_of_ne hne]

/-- **One allowed write**: it passes `StepOK` and keeps `IW`. -/
theorem pw_step (hK : RegionOK K) (hU : UserOK K) {m : U64 → U64} {c : U64} {lk : U64 → Prop}
    {m0 : U64 → U64} (hm : ∀ d, K.heap d = some .tcb → m (fld d oAFFINITY) = m0 (fld d oAFFINITY))
    {x x' : S} {a v : U64} (hI : IW (L := L) K c lk m0 x) (hP : PW (L := L) K c lk m0 x a v)
    (hw : st.write x a v = ok x') :
    StepOK (own K) (cls K) (ko K m) (· ∈ K.user) c lk (L.mem x) (L.mem x') ∧
      IW (L := L) K c lk m0 x' := by
  rw [L.write_eq] at hw
  obtain rfl : L.wr x a v = x' := by
    have h2 : (ok (L.wr x a v) : Result S) ⦃ r => r = x' ⦄ := by rw [hw]; exact (WP.spec_ok _).2 rfl
    exact (WP.spec_ok (L.wr x a v)).1 h2
  have alT : ∀ d off, K.heap d = some .tcb → DecOff off → Aligned (fld d off) :=
    fun d off hd ho => (hU.tcb d hd off ho).1
  rcases hP with ⟨ha, hd⟩ | ⟨d, hdT, hS, rfl, hq⟩ | ⟨d, hdT, hS, rfl, hq⟩
  · refine ⟨stepOK_nondec hK hU ha hd, fun d hdT => ?_⟩
    have u : ∀ off, DecOff off → L.mem (L.wr x a v) (fld d off) = L.mem x (fld d off) :=
      fun off ho => mem_wr_dec hU ha (decW_tcb hdT ho)
        (fun e : fld d off = a => hd (e ▸ decW_tcb hdT ho))
    rw [u oAFFINITY (Or.inl rfl), u oSTATE (Or.inr (Or.inl rfl)), u oBLOCK_OBJ (Or.inr (Or.inr (Or.inl rfl)))]
    exact hI d hdT
  · have ha := alT d oSTATE hdT (Or.inr (Or.inl rfl))
    obtain ⟨haff, hq0⟩ := hI d hdT
    refine ⟨stepOK_state hK hU hdT (haff.trans hS.1) ((hm d hdT).trans hS.1) (hq0 hS) hq,
      fun d' hd' => ?_⟩
    by_cases e : d' = d
    · rw [e]
      have hA : fld d oAFFINITY ≠ fld d oSTATE := fld_ne_off hK hdT (Or.inl rfl) (Or.inr (Or.inl rfl))
        (by simp only [oAFF_val, oSTATE_val]; omega)
      have hB : fld d oBLOCK_OBJ ≠ fld d oSTATE := fld_ne_off hK hdT (Or.inr (Or.inr (Or.inl rfl)))
        (Or.inr (Or.inl rfl)) (by simp only [oBOBJ_val, oSTATE_val]; omega)
      rw [mem_wr_upd ha (alT d oAFFINITY hdT (Or.inl rfl)), Function.update_of_ne hA,
        mem_wr_upd ha ha, Function.update_self,
        mem_wr_upd ha (alT d oBLOCK_OBJ hdT (Or.inr (Or.inr (Or.inl rfl)))), Function.update_of_ne hB]
      exact ⟨haff, fun _ h => hq h⟩
    · have ne : ∀ off, DecOff off → fld d' off ≠ fld d oSTATE :=
        fun off ho e' => e (fld_inj hK hd' hdT ho (Or.inr (Or.inl rfl)) e').1
      rw [mem_wr_dec hU ha (decW_tcb hd' (Or.inl rfl)) (ne _ (Or.inl rfl)),
        mem_wr_dec hU ha (decW_tcb hd' (Or.inr (Or.inl rfl))) (ne _ (Or.inr (Or.inl rfl))),
        mem_wr_dec hU ha (decW_tcb hd' (Or.inr (Or.inr (Or.inl rfl)))) (ne _ (Or.inr (Or.inr (Or.inl rfl))))]
      exact hI d' hd'
  · have ha := alT d oBLOCK_OBJ hdT (Or.inr (Or.inr (Or.inl rfl)))
    obtain ⟨haff, hq0⟩ := hI d hdT
    have hSB : fld d oSTATE ≠ fld d oBLOCK_OBJ := fld_ne_off hK hdT (Or.inr (Or.inl rfl))
      (Or.inr (Or.inr (Or.inl rfl))) (by simp only [oBOBJ_val, oSTATE_val]; omega)
    refine ⟨stepOK_tcb hK hU hdT (Or.inr rfl) (haff.trans hS.1) ((hm d hdT).trans hS.1) (hq0 hS)
      (by rw [Function.update_of_ne hSB, Function.update_self]; exact hq), fun d' hd' => ?_⟩
    by_cases e : d' = d
    · rw [e]
      have hA : fld d oAFFINITY ≠ fld d oBLOCK_OBJ := fld_ne_off hK hdT (Or.inl rfl)
        (Or.inr (Or.inr (Or.inl rfl))) (by simp only [oAFF_val, oBOBJ_val]; omega)
      rw [mem_wr_upd ha (alT d oAFFINITY hdT (Or.inl rfl)), Function.update_of_ne hA,
        mem_wr_upd ha (alT d oSTATE hdT (Or.inr (Or.inl rfl))), Function.update_of_ne hSB,
        mem_wr_upd ha ha, Function.update_self]
      exact ⟨haff, fun _ h => hq h⟩
    · have ne : ∀ off, DecOff off → fld d' off ≠ fld d oBLOCK_OBJ :=
        fun off ho e' => e (fld_inj hK hd' hdT ho (Or.inr (Or.inr (Or.inl rfl))) e').1
      rw [mem_wr_dec hU ha (decW_tcb hd' (Or.inl rfl)) (ne _ (Or.inl rfl)),
        mem_wr_dec hU ha (decW_tcb hd' (Or.inr (Or.inl rfl))) (ne _ (Or.inr (Or.inl rfl))),
        mem_wr_dec hU ha (decW_tcb hd' (Or.inr (Or.inr (Or.inl rfl)))) (ne _ (Or.inr (Or.inr (Or.inl rfl))))]
      exact hI d' hd'

variable {A X : Type}

/-- **From the checked store to `mguard`**, for a tree. -/
theorem run_gd_mguard (hK : RegionOK K) (hU : UserOK K) {m : U64 → U64} {lk : U64 → Prop} {s : S}
    (hm : ∀ d, K.heap d = some .tcb → m (fld d oAFFINITY) = L.mem s (fld d oAFFINITY))
    {ar : machine.Arch A} {R : U64 → Prop} (p : SProg X) {a : A} {r : X × S × A}
    (h : interp (gd st R (PW (L := L) K (L.cpu s) lk (L.mem s))) ar p s a = ok r) :
    interp (mguard st fun x y => StepOK (own K) (cls K) (ko K m) (· ∈ K.user) (L.cpu s) lk (L.mem x) (L.mem y))
      ar p s a = ok r :=
  interp_gd (I := IW (L := L) K (L.cpu s) lk (L.mem s))
    (fun _ _ _ _ hI hP hw => pw_step hK hU hm hI hP hw) p s a r (iw_start s) h

/-- **From the checked store to `mguard`**, for a body (`IsProg` [P]). -/
theorem move_of_gd (hK : RegionOK K) (hU : UserOK K)
    {F : ∀ {A : Type}, machine.Arch A → machine.Store S → S → A → Result (X × S × A)} {p : SProg X}
    (hF : IsProg F p) (ar : machine.Arch A) {m : U64 → U64} {lk : U64 → Prop} {s : S}
    (hm : ∀ d, K.heap d = some .tcb → m (fld d oAFFINITY) = L.mem s (fld d oAFFINITY))
    {R : U64 → Prop} {a : A} {r : X × S × A}
    (h : F ar (gd st R (PW (L := L) K (L.cpu s) lk (L.mem s))) s a = ok r) :
    F ar (mguard st fun x y => StepOK (own K) (cls K) (ko K m) (· ∈ K.user) (L.cpu s) lk (L.mem x) (L.mem y))
      s a = ok r := by
  have hp : ∀ (m : machine.Store S) (x : S) (a : A), F ar m x a = interp m ar p x a :=
    fun m x a => congrFun (congrFun (hF A ar m) x) a
  rw [hp] at h ⊢
  exact run_gd_mguard hK hU hm p h

/-- Every aligned word deciding nothing is written as by `st`. -/
theorem wall_nondec {c : U64} {lk : U64 → Prop} {m0 : U64 → U64} {a : U64} (ha : Aligned a)
    (hd : ¬ DecW K a) : WAll (PW (L := L) K c lk m0) a :=
  fun _ _ => Or.inl ⟨ha, hd⟩

/-- A `STATE` write the checked store allows. -/
theorem gd_write_state {R : U64 → Prop} {c : U64} {lk : U64 → Prop} {m0 : U64 → U64} {x : S}
    {d v : U64} (hdT : K.heap d = some .tcb) (hS : Safe0 c lk m0 d)
    (hq : QueuedState v → lk (L.mem x (fld d oBLOCK_OBJ))) :
    (gd st R (PW (L := L) K c lk m0)).write x (stA d) v = st.write x (stA d) v := by
  rw [stA_fld]
  exact gd_write (Or.inr (Or.inl ⟨d, hdT, hS, rfl, hq⟩))

/-- A `BLOCK_OBJ` write the checked store allows. -/
theorem gd_write_bobj {R : U64 → Prop} {c : U64} {lk : U64 → Prop} {m0 : U64 → U64} {x : S}
    {d v : U64} (hdT : K.heap d = some .tcb) (hS : Safe0 c lk m0 d)
    (hq : QueuedState (L.mem x (fld d oSTATE)) → lk v) :
    (gd st R (PW (L := L) K c lk m0)).write x (blockA d) v = st.write x (blockA d) v :=
  gd_write (Or.inr (Or.inr ⟨d, hdT, hS, rfl, hq⟩))

end st

end

end Fl4Proofs.P2.OwnMap
