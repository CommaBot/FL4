/-
P3 (issue #16, F1 stages 2, 3, 5; KENTRY-PLAN f2 / f4): **the `JAtZ` uses of
`VsNamed`** (split from VsNamed / VsNamedKeep in f4 so that the `VsNamed`
machinery sits upstream of JCarryDefs).

* `JAtZ.vsReachMiss`, `JAtZ.vsReachMissR`, `JAtZ.vsReachAsidC` (VsNamed's
  module docstring): the C17 / C23 / C24 vsReach discharge.
* `JAtZ.vsNamedRestart` (VsNamedKeep's; `JAtZ.vsNamedDrop` is in VsNamedRet).
-/
import Fl4Proofs.P3.UtDropJ2
import Fl4Proofs.P3.VsNamedStep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3

open fl4_core

/-! ## The discharge at `JAtZ` -/

section
open Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **(F1) C17 / C23 / C24 vsReach at a `JAtZ` state with `VsNamed`**: every
table reached from the `NeedR` roots misses a childless untyped cap's region
(module docstring). -/
theorem JAtZ.vsReachMiss (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hN : Vs.VsNamed Z.th (L.mem s) (L.ksb s)) {x p sb fi : U64} {dv : Bool} (hx : x ∈ Z.G.chains.flatten)
    (hcx : capV (L.mem s) x = .Untyped p sb fi dv) (hnd : ∀ y, ¬ Mdb.Desc Z.G.par y x) :
    Vs.VsReachMiss p.val (p.val + 2 ^ sb.val) (L.mem s) (L.ksb s)
      (Vs.NeedR Z.th (L.mem s) 5) (Vs.NeedR Z.th (L.mem s) 4) (Vs.NeedR Z.th (L.mem s) 3)
      (Vs.NeedR Z.th (L.mem s) 2) (Vs.NeedR Z.th (L.mem s) 1) := by
  have hca : capAt (L.mem s) x = ok (.Untyped p sb fi dv) := by rw [capAt_capV, hcx]
  have hsb : sb.val < 64 := capAt_untyped_inv hca
  have hrx := J.ut.reg x hx (by rw [hcx]; exact physF_ut _ _ _ _)
  rw [hcx] at hrx
  obtain ⟨-, -, hfit⟩ := ut_range hsb hrx
  intro k q hR
  have hy : ∃ y, IsSlot Z.th y ∧ Vs.VKey (capV (L.mem s) y) = some (k, q) := by
    rcases hR.split hN J.vsc with ⟨y, hy, hn⟩ | ⟨a, v, hw⟩
    · exact ⟨y, hy, (Vs.vkey_vneed hn).1⟩
    · obtain ⟨y, hy, hk, -⟩ := hN.named _ _ _ _ hw
      exact ⟨y, hy, hk⟩
  obtain ⟨y, hy, hk⟩ := hy
  obtain ⟨hp, hs, hph, hnu⟩ := Vs.vkey_tab hk
  exact J.tabOff hsb hfit hx hcx hnd hy hp hs hph hnu

/-- **(F1) The premise shape: C17 / C23 / C24 vsReach at the caller's restart
state** (`JUtPath.vsReach`, `JUtPathM(U16).vsReach`, `JDevPath.vsReach` with
`x = cslotAddr sl`): `set_thread_state Restart` keeps the slots and the `VObj`
words (`restart_top`), so a reach at `s1` is one at `s` (`VsReach.frame`). -/
theorem JAtZ.vsReachMissR (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hN : Vs.VsNamed Z.th (L.mem s) (L.ksb s)) (hni : Entered σ) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) {x p sb fi : U64} {dv : Bool} (hx : x ∈ Z.G.chains.flatten)
    (hcx : capV (L.mem s) x = .Untyped p sb fi dv) (hnd : ∀ y, ¬ Mdb.Desc Z.G.par y x) :
    ∀ s1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
      Vs.VsReachMiss p.val (p.val + 2 ^ sb.val) (L.mem s1) (L.ksb s1)
        (Vs.NeedR Z.th (L.mem s1) 5) (Vs.NeedR Z.th (L.mem s1) 4) (Vs.NeedR Z.th (L.mem s1) 3)
        (Vs.NeedR Z.th (L.mem s1) 2) (Vs.NeedR Z.th (L.mem s1) 1) := by
  intro s1 hs1
  obtain ⟨hcur, x0, hk, hrun⟩ := J.curRunnable hni hct
  have hF := J.xtop.fin
  have h := Vs.restart_top s a σ ct x0 hF.1 hF.2.1 hcur.symm hk hrun
  rw [hs1, WP.spec_ok] at h
  obtain ⟨-, -, -, hks, hmV⟩ := h
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s1) := slotsSame_of_vobj J.xtop.rel.1 hmV
  have hc : ∀ y, IsSlot Z.th y → capV (L.mem s1) y = capV (L.mem s) y := fun y hy => hSS.capV hy
  obtain ⟨hWt, hWp⟩ := Vs.walk_of_vobj hF.1.2.vs hF.1.2.pt hmV
  intro k q hR
  rw [hks] at hR
  simp only [Vs.NeedR.congr hc] at hR
  have hN' := J.vsc.needR
  exact J.vsReachMiss hN hx hcx hnd k q
    (hR.frame hF.2.1 hF.2.2.1 hF.2.2.2.1 hWt hWp hN'.1 hN'.2.1 hN'.2.2.1 hN'.2.2.2.1 hN'.2.2.2.2)

/-- **(F1) The `JAsidCPath.vsReach` shape** (C17). -/
theorem JAtZ.vsReachAsidC (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hN : Vs.VsNamed Z.th (L.mem s) (L.ksb s)) (hni : Entered σ) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) :
    ∀ (x p fi : U64) (s1 : S), x ∈ Z.G.chains.flatten →
      capV (L.mem s) x = .Untyped p fl4_abi.consts.bits.ASID_POOL fi false → (∀ y, ¬ Mdb.Desc Z.G.par y x) →
      sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
      Vs.VsReachMiss p.val (p.val + 2 ^ (fl4_abi.consts.bits.ASID_POOL).val) (L.mem s1) (L.ksb s1)
        (Vs.NeedR Z.th (L.mem s1) 5) (Vs.NeedR Z.th (L.mem s1) 4) (Vs.NeedR Z.th (L.mem s1) 3)
        (Vs.NeedR Z.th (L.mem s1) 2) (Vs.NeedR Z.th (L.mem s1) 1) :=
  fun _ _ _ s1 hx hc hnd hs1 => J.vsReachMissR hN hni hct hx hc hnd s1 hs1

end

namespace Vs
open Fl4Proofs.P1

noncomputable section

/-! ## The drop at `JAtZ` -/

section
open Fl4Proofs.P3.Sched
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **(F1 stage 3, frame class) `VsNamed` across the caller's restart**
(`set_thread_state Restart`: the slots and the `VObj` words kept,
`restart_top`), the frame `JAtZ.restartJ` makes. -/
theorem _root_.Fl4Proofs.P3.JAtZ.vsNamedRestart (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hN : VsNamed Z.th (L.mem s) (L.ksb s)) (hni : Entered σ) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) :
    ∀ s1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 → VsNamed Z.th (L.mem s1) (L.ksb s1) := by
  intro s1 hs1
  obtain ⟨hcur, x0, hk, hrun⟩ := J.curRunnable hni hct
  have hF := J.xtop.fin
  have h := restart_top s a σ ct x0 hF.1 hF.2.1 hcur.symm hk hrun
  rw [hs1, WP.spec_ok] at h
  obtain ⟨-, -, -, hks, hmV⟩ := h
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s1) := slotsSame_of_vobj J.xtop.rel.1 hmV
  obtain ⟨hWt, hWp⟩ := walk_of_vobj hF.1.2.vs hF.1.2.pt hmV
  rw [hks]
  exact hN.frame hF.2.1 hF.2.2.1 hF.2.2.2.1 hWt hWp J.vsc fun y hy => hSS.capV hy

end

end

end Vs

end Fl4Proofs.P3
