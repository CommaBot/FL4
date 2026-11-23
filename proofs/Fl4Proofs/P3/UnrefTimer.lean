/-
P3 (jc6d10, TIMER-RB-PLAN §14, KENTRY-PLAN jc6d): **part (d) of `RegionUnrefAt` (the timer
trees) from P1's red-black invariant**, given that the dead TCBs are unarmed.

* `DeadUnarmed H D s`: every TCB of the dead set `D` has deadline word 0 (`tdA`).  FL4's
  TCB finalise ends its timer part with `timer::remove` (deadline 0), and only
  `TCBSetTimer` arms a TCB, through a thread cap.  This is the one fact (d) still asks; it
  is not yet carried in `JAtZ` (TIMER-RB-PLAN §14: the deadline word has no spec
  counterpart, so the dead set's keep lemmas, which read every `DeadP` word through the
  relation, cannot keep it as they stand).
* `timerKeptDAll_of` (P1-level): from `TimerOK` (links typed), `TimerRB` (`no_link`: no
  tree word names an unarmed TCB) and `DeadUnarmed`, no TCB's `tl`/`tr`/`tp` link and no
  core's `TIMER_ROOT`/`TIMER_MIN` names an object of `D` (jc6a's carried form
  `TimerKeptDAll`).
* `JAtZ.keptD`: the same at any `JAtZ` state (`J.blk`'s `tm`/`rb`, `J.kern.h0`).
* `DeadUnarmed.sts`: `set_thread_state` keeps the deadline words (`KeepT.fld`).
* `JAtZ.unrefD`: (d) of `RegionUnrefAt` at an `Entered` `JAtZ` state with `DeadUnarmed`
  (the restart's `JAtZ` by `JAtZ.restartSJ`, then `keptD`, `TimerKeptDAll.region`).
* `RegionUnrefBCU` = (b) ∧ (c) ∧ `DeadUnarmed`; `JAtZ.regionUnrefBCD` rebuilds U25's
  `RegionUnrefBCD` from it.
-/
import Fl4Proofs.P3.UnrefParts
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **The dead TCBs are unarmed** (module docstring). -/
def DeadUnarmed (H : P1.Heap) (D : Set U64) (s : S) : Prop :=
  ∀ q ∈ D, H q = some .tcb → L.mem s (P1.tdA q) = 0#u64

/-- **No timer-tree word names a dead object** (module docstring): `TimerOK`'s typing,
`TimerRB.no_link` at each dead (hence unarmed) TCB. -/
theorem timerKeptDAll_of {H : P1.Heap} {Cs D : Set U64} {s : S} (h0 : H 0#u64 = none)
    (hT : P1.TcbPlaced (P1.Heap.tcbs H)) (hTm : P1.TimerOK st (P1.Heap.tcbs H) Cs s)
    (hRB : P1.TimerRB st (P1.Heap.tcbs H) Cs s) (hU : DeadUnarmed (L := L) H D s) :
    TimerKeptDAll (L := L) H Cs D s := by
  have key : ∀ x : U64, P1.Tz (P1.Heap.tcbs H) x →
      (∀ q, q ∈ P1.Heap.tcbs H → L.mem s (P1.tdA q) = 0#u64 → x ≠ q) → P1.KeptRef H (· ∈ D) x := by
    intro x hz hne hx hd
    rcases hz with e | hxT
    · subst e; exact hx h0
    · exact hne x hxT (hU x hd hxT) rfl
  refine ⟨fun y hy => ⟨key _ (hTm.lt y hy) fun q hq hq0 => ?_, key _ (hTm.rt y hy) fun q hq hq0 => ?_,
    key _ (hTm.pt y hy) fun q hq hq0 => ?_⟩, fun c hc => ⟨key _ (hTm.root c hc) fun q hq hq0 => ?_,
    key _ (hTm.min c hc) fun q hq hq0 => ?_⟩⟩
  · exact ((hRB.no_link hT hq hq0).1 y hy).1
  · exact ((hRB.no_link hT hq hq0).1 y hy).2.1
  · exact ((hRB.no_link hT hq hq0).1 y hy).2.2
  · exact ((hRB.no_link hT hq hq0).2 c hc).1
  · exact ((hRB.no_link hT hq hq0).2 c hc).2

/-- **`set_thread_state` keeps `DeadUnarmed`** (it writes no deadline word: `KeepT.fld`). -/
theorem DeadUnarmed.sts {H : P1.Heap} {Cs Ω Sg Rp Scs Nt Ac : Set U64} {Z : U64 → Nat} {D : Set U64}
    {s s1 : S} {t : obj.Tcb} {v : U64}
    (hb : P1.BlkOK st (P1.Heap.tcbs H) Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ P1.Heap.tcbs H)
    (hU : DeadUnarmed (L := L) H D s) (hs1 : sched.set_thread_state st s t v = ok s1) :
    DeadUnarmed (L := L) H D s1 := by
  obtain ⟨⟨Q, R, h0⟩, -, hX, -, hSg⟩ := hb
  have hh := P1.sched.set_thread_state.state s t v Q R h0 ht hX.1 hSg.sub
  rw [hs1, WP.spec_ok] at hh
  intro q hq hH
  have e := hh.2.fld q hH 3528#u64 (by simp) (by simp) (by simp) (by simp) (fun _ => ⟨by simp, by simp⟩)
  show L.mem s1 (core.num.U64.wrapping_add q 3528#u64) = 0#u64
  rw [e]
  exact hU q hq hH

/-- **(b) ∧ (c) ∧ `DeadUnarmed`**: what `kernel_entry_reachU26` asks in place of U25's
`RegionUnrefBCD` (the dispatch state's dead TCBs unarmed in place of (d)). -/
def RegionUnrefBCU (H : P1.Heap) (Cs D : Set U64) (s : S) : Prop :=
  RegionUnrefB (L := L) H D s ∧ RegionUnrefC (L := L) H Cs D s ∧ DeadUnarmed (L := L) H D s

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **(d), carried form, at any `JAtZ` state** with `DeadUnarmed`. -/
theorem JAtZ.keptD (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hU : DeadUnarmed (L := L) H D s) :
    TimerKeptDAll (L := L) H Cs D s := by
  obtain ⟨⟨Q, R, h0⟩, -, hX, -, -⟩ := J.blk
  exact timerKeptDAll_of J.kern.h0 h0.tcbs hX.2.2.tm hX.2.2.rb hU

/-- **(d) of `RegionUnrefAt` at an `Entered` `JAtZ` state** with `DeadUnarmed`: `keptD` at
the restart's `JAtZ` (`JAtZ.restartSJ`, the same `H` and `D`; `DeadUnarmed.sts`). -/
theorem JAtZ.unrefD (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ)
    (hU : DeadUnarmed (L := L) H D s) : RegionUnrefD (L := L) H Cs D s := by
  intro s1 hs1 lo hi hD
  have hct : sched.cur_thread st s = ok (L.curW s) := cur_thread_eq s
  obtain ⟨hcur, x, hk, hrun⟩ := J.curRunnable hni hct
  have htcb : Z.th (L.curW s) = some .tcb := (J.xtop.curTcb hcur).1
  obtain ⟨Ac', Lst', J1⟩ := J.restartSJ (jStepHyps arI) hcur hk htcb hrun hs1
  have htH : L.curW s ∈ P1.Heap.tcbs H := J.zH.1 _ (J.thT _ htcb)
  exact (J1.keptD (hU.sts J.blk htH hs1)).region hD

/-- **U25's `RegionUnrefBCD` from `RegionUnrefBCU`** at an `Entered` `JAtZ` state. -/
theorem JAtZ.regionUnrefBCD (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ)
    (h : RegionUnrefBCU (L := L) H Cs D s) : RegionUnrefBCD (L := L) H Cs D s :=
  ⟨h.1, h.2.1, J.unrefD hni h.2.2⟩

end

end

end Fl4Proofs.P3
