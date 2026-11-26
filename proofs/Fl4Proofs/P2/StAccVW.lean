/-
# P2 (line p3mc, gen 19): st's value check for `safeVQW` (`StVW`), its owner fact and the accepted run under it

For an st start at core `c`'s view of `ρ` with the target homed on `c`, the accepted run may recolour (write
`TIMER_HEIGHT` of) nodes of `c`'s timer tree that are **other cores' threads** (armed in `c`'s tree), and writes
`TIMER_DEADLINE` of the target only. The step check:

* **`StVW K c ρ X X'`**: for every thread `t` of the heap homed off `c` in `ρ`, `X → X'` keeps its `TIMER_DEADLINE`,
  and, if it is armed at `X`, keeps the tree named by its `TIMER_HEIGHT` (`val / 256`); `StPW` is its per-write form
  (address aligned, never another core's deadline, a height write of another core's armed thread naming the same
  tree), **`stPW_vw`**;
* **`stVW_own`**: `safeVQW`'s `hO2W` for `ownP K` over the write set "`¬ VDec`, or the `TIMER_HEIGHT` of another
  core's thread", at a check memory that agrees with the store state on the words the view keeps (the timer words of
  every thread: `view_timer_keep`): a `¬ VDec` write by `vown_upd`; a height write by `own_upd_timer` (the timer
  group's owner `tOwner` stays: the deadline is untouched and, if armed, the tree is the same);
* **`st_acc_vw`**: an accepted run of `localtimer.handle_set_timer_local` from an entry state with P1's invariant
  (`BXI`, `StLay`), target homed on `c` in `ρ`, is the same run on `mguard st (StVW K c ρ)`: it is
  `GED.set_timer_accGD` on the store `gd st ⊤ StPW` (the non-deciding writes by `st_wr_nondec`, the caller's
  `STATE`, the keys' heights under `hwH`'s condition, the target's deadline), moved to `mguard` by `interp_gd`.

No premise: every fact is a hypothesis (`RegionOK` / `UserOK` of the layout, `IsProg` of the st body). No existing
statement changed.
-/
import Fl4Proofs.P2.FootTimerSetAccD
import Fl4Proofs.P2.StVTimer
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.Serial (Owner ClsOwner)
open Fl4Proofs.P2.OwnMap Fl4Proofs.P2.PathObl
open Fl4Proofs.P2.OwnMapP (KLayoutP ownP RegionOKP UserOKP ownP_pte ownP_off)
open Fl4Proofs.P2.OwnMapV (ownV_off ownV_on_mem)
open Fl4Proofs.P2.CoreView (view VDec VDD)
open Classical

section
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]

/-- **st's step check** (module docstring). -/
def StVW (K : KLayout) (c : U64) (ρ : U64 → U64) (X X' : S) : Prop :=
  ∀ t, K.heap t = some .tcb → ρ (fld t oAFFINITY) ≠ c →
    L.mem X' (fld t oTIMER_DEADLINE) = L.mem X (fld t oTIMER_DEADLINE) ∧
    (L.mem X (fld t oTIMER_DEADLINE) ≠ 0#u64 →
      (L.mem X' (fld t oTIMER_HEIGHT)).val / 256 = (L.mem X (fld t oTIMER_HEIGHT)).val / 256)

/-- **st's per-write check** (module docstring). -/
def StPW (K : KLayout) (c : U64) (ρ : U64 → U64) (X : S) (q v : U64) : Prop :=
  Aligned q ∧ ∀ t, K.heap t = some .tcb → ρ (fld t oAFFINITY) ≠ c →
    q ≠ fld t oTIMER_DEADLINE ∧ (q = fld t oTIMER_HEIGHT → L.mem X (fld t oTIMER_DEADLINE) ≠ 0#u64 →
      v.val / 256 = (L.mem X q).val / 256)

variable {st}

theorem decOff_DL : OwnMap.DecOff oTIMER_DEADLINE := Or.inr (Or.inr (Or.inr (Or.inl rfl)))
theorem decOff_HT : OwnMap.DecOff oTIMER_HEIGHT := Or.inr (Or.inr (Or.inr (Or.inr rfl)))
theorem decOff_ST : OwnMap.DecOff oSTATE := Or.inr (Or.inl rfl)

/-- A write passing `StPW` passes `StVW`. -/
theorem stPW_vw {K : KLayout} (hUO : E2E.UserOK K) {c : U64} {ρ : U64 → U64} {X : S} {q v : U64}
    (h : StPW st K c ρ X q v) : StVW st K c ρ X (L.wr X q v) := by
  intro t ht ha
  obtain ⟨hq, h⟩ := h
  obtain ⟨n1, n2⟩ := h t ht ha
  have aD : Aligned (fld t oTIMER_DEADLINE) := (decW_ok hUO (decW_tcb ht decOff_DL)).1
  have aH : Aligned (fld t oTIMER_HEIGHT) := (decW_ok hUO (decW_tcb ht decOff_HT)).1
  refine ⟨mem_wr_ne' hq aD n1, fun hd => ?_⟩
  by_cases e : q = fld t oTIMER_HEIGHT
  · have h2 := n2 e hd
    rw [← e, L.mem_wr X q v q hq hq, if_pos rfl]; exact h2
  · rw [mem_wr_ne' hq aH e]

/-- **`hO2W` for `ownP` and st's check** (module docstring). -/
theorem stVW_own {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K) {c : U64} {ρ : U64 → U64} {q : U64}
    (hq : ¬ VDec K.toKLayout c ρ q ∨
      ∃ t, K.heap t = some .tcb ∧ ρ (fld t oAFFINITY) ≠ c ∧ q = fld t oTIMER_HEIGHT)
    (s : S) (v : U64) (m : U64 → U64) (hW : StVW st K.toKLayout c ρ s (L.wr s q v))
    (hm : ∀ x, Aligned x → x ∉ K.user → view K.toKLayout c ρ x = ρ x → m x = L.mem s x)
    (y : U64) (hy : VDD K.toKLayout c ρ y) : ownP K (Function.update m q v) y = ownP K m y := by
  rcases hq with hq | ⟨t, ht, ha, rfl⟩
  · exact CoreView.vown_upd hK hq m v y hy
  have hK0 := hK.base.base
  have hU0 := hU.base.base
  by_cases hp : y ∈ K.ptes
  · rw [ownP_pte hp, ownP_pte hp]
  rw [ownP_off hp, ownP_off hp]
  by_cases hv : ∃ v, Fl4Proofs.P2.OwnMapV.InVcpu K.toKLayoutV v y
  · exact ownV_on_mem hK.base hv
  rw [ownV_off hv, ownV_off hv]
  obtain ⟨aD, uD⟩ := decW_ok hU0 (decW_tcb ht decOff_DL)
  obtain ⟨aH, uH⟩ := decW_ok hU0 (decW_tcb ht decOff_HT)
  obtain ⟨hrD, hoD⟩ := hK0.tcb t ht oTIMER_DEADLINE (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  obtain ⟨hrH, hoH⟩ := hK0.tcb t ht oTIMER_HEIGHT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  rw [oDL_val] at hoD; rw [oHT_val] at hoH
  have eD : m (fld t oTIMER_DEADLINE) = L.mem s (fld t oTIMER_DEADLINE) :=
    hm _ aD uD (CoreView.view_timer_keep hrD (by omega) (by omega))
  have eH : m (fld t oTIMER_HEIGHT) = L.mem s (fld t oTIMER_HEIGHT) :=
    hm _ aH uH (CoreView.view_timer_keep hrH (by omega) (by omega))
  have nDH : fld t oTIMER_DEADLINE ≠ fld t oTIMER_HEIGHT :=
    fld_ne_off hK0 ht decOff_DL decOff_HT (by rw [oDL_val, oHT_val]; omega)
  have hO : own K.toKLayout (Function.update m (fld t oTIMER_HEIGHT) v) = own K.toKLayout m := by
    refine own_upd_timer hK0 ht (Or.inr rfl) ?_
    rw [Function.update_of_ne nDH, Function.update_self]
    unfold tOwner
    split_ifs with h0
    · have h0' : L.mem s (fld t oTIMER_DEADLINE) ≠ 0#u64 := by
        intro e; rw [eD, e] at h0; simp at h0
      have e2 := (hW t ht ha).2 h0'
      rw [L.mem_wr s _ v _ aH aH, if_pos rfl] at e2
      rw [eH]
      unfold treeCore
      rw [e2]
    · rfl
  exact congrFun hO y

end

section acc
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {A : Type} (ar : machine.Arch A)

theorem off_ne {a b : U64} (h : a.val ≠ b.val) : a ≠ b := fun e => h (congrArg _ e)

theorem shr8 (x : Nat) : x >>> 8 = x / 256 := Nat.shiftRight_eq_div_pow x 8

/-- **The accepted st run passes st's check** (module docstring). -/
theorem st_acc_vw (hA : P0.ArchTotal ar) (hK : RegionOK K) (hUO : E2E.UserOK K) {n : I64} {target : U64}
    {p : SProg Bool} (hp : IsProg (stBody S n target) p) {c : U64} {ρ : U64 → U64} {s s1 : S} {a a1 : A}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (htg : target ∈ T) (hL : StLay K st T Scs Z s)
    (htH : ρ (fld target oAFFINITY) = c)
    (h : localtimer.handle_set_timer_local st ar s a n target = ok (true, s1, a1)) :
    localtimer.handle_set_timer_local (mguard st (StVW st K c ρ)) ar s a n target = ok (true, s1, a1) := by
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced T := h0.tcbs
  have hcT : L.curW s ∈ T := h0.curT
  have heap : ∀ y ∈ T, K.heap y = some .tcb := fun y hy =>
    hK.tcbOf y _ (hL.tcb y hy 3328#u64 (by simp) (by simp))
  have es : stA (L.curW s) = fld (L.curW s) oSTATE := by rw [stA_eq]; rfl
  have hg : localtimer.handle_set_timer_local (gd st (fun _ => True) (StPW st K c ρ)) ar s a n target =
      ok (true, s1, a1) :=
    GED.set_timer_accGD (gS := gd st (fun _ => True) (StPW st K c ρ)) (R := fun _ => True)
      (W := WAll (StPW st K c ρ)) ar hA hI htg
      (fun _ _ _ _ => trivial)
      (fun ho w ha hw hn X v => by
        have hd := st_wr_nondec hK hI hL ho hw hn
        refine ⟨ha, fun t ht _ => ⟨fun e => hd (by rw [e]; exact decW_tcb ht decOff_DL), fun e => ?_⟩⟩
        exact (hd (by rw [e]; exact decW_tcb ht decOff_HT)).elim)
      (fun _ => trivial) (fun _ => trivial)
      (fun _ X v _ _ _ => gd_write (by
        refine ⟨by rw [stA_eq]; exact field_aligned (hT _ hcT) (by simp) (by simp), fun t ht _ => ⟨?_, ?_⟩⟩
        · rw [es]; intro e
          have := (fld_inj hK (heap _ hcT) ht decOff_ST decOff_DL e).2
          exact (off_ne (by simp [oTIMER_DEADLINE, oTIMER_HEIGHT, oSTATE]) this).elim
        · rw [es]; intro e
          have := (fld_inj hK (heap _ hcT) ht decOff_ST decOff_HT e).2
          exact (off_ne (by simp [oTIMER_DEADLINE, oTIMER_HEIGHT, oSTATE]) this).elim))
      (fun _ X y v hy hc => gd_write (by
        refine ⟨field_aligned (hT y hy.1) (by simp) (by simp), fun t ht _ => ⟨fun e => ?_, fun e hd => ?_⟩⟩
        · have := (fld_inj hK (heap y hy.1) ht decOff_HT decOff_DL e).2
          exact (off_ne (by simp [oTIMER_DEADLINE, oTIMER_HEIGHT, oSTATE]) this).elim
        · have ety := (fld_inj hK (heap y hy.1) ht decOff_HT decOff_HT e).1
          subst ety
          obtain ⟨h1, h2⟩ := hc hd
          rw [shr8] at h1 h2
          exact h2.trans h1.symm))
      (fun _ X v _ _ _ => gd_write (by
        refine ⟨field_aligned (hT target htg) (by simp) (by simp), fun t ht hta => ⟨fun e => ?_, fun e => ?_⟩⟩
        · have ett := (fld_inj hK (heap target htg) ht decOff_DL decOff_DL e).1
          subst ett; exact absurd htH hta
        · have := (fld_inj hK (heap target htg) ht decOff_DL decOff_HT e).2
          exact (off_ne (by simp [oTIMER_DEADLINE, oTIMER_HEIGHT, oSTATE]) this).elim))
      h
  have eP : ∀ mm : machine.Store S,
      localtimer.handle_set_timer_local mm ar s a n target = interp mm ar p s a :=
    fun mm => congrFun (congrFun (hp A ar mm) s) a
  rw [eP] at hg
  rw [eP]
  exact interp_gd (R := fun _ => True) (P := StPW st K c ρ) (Q := StVW st K c ρ) (I := fun _ => True)
    (fun x q v x' _ hq hw => by
      rw [L.write_eq] at hw
      have e := ok_inj_ff hw
      subst e
      exact ⟨stPW_vw hUO hq, trivial⟩) p s a _ trivial hg

end acc

end Fl4Proofs.P2
