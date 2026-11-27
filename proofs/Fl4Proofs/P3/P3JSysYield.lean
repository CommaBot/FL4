/-
P3 (p3J gen 28): **the first native-syscall dispatch leaf with a projection footprint** — `SysYield`.

`syscall.handle_yield` (FL4 `syscall.rs` 279–285, seL4 MCS `handleYield`: `chargeBudget(head.amount, false)` then
the current SC's `CONSUMED` word) at a `JAtZ` state with action resume and every SC round-robin (`RR`, gen 25):

* the current SC's period word is `0` (spec period `0` by `RR`, FL4's by `ScRelW.period`, as P3JMcFlt's
  `budOk_projW_rr`), so P2's `Stall.sched.charge_budget.rr` applies at `Kp = ∅`, `Nd = False`: a `FootN` footprint,
  inside `ProjW` by `cur0wN_projW`;
* the final `set_consumed` writes a word of the current SC, an `H` object (`XInv`'s `cur`), so a `ProjW` word.

**`yieldProjW`**: `handle_yield` writes only `ProjW H Cs s`. No premise; no sorry. New module; no existing statement
changed.
-/
import Fl4Proofs.P3.P3JMcFlt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Mc
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs Fl4Proofs.P3.JBootQ

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
  {AR : A → Fl4Spec.Cr3 → Prop}
variable {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A}
  {σ : Fl4Spec.State Unit}

/-- A word inside an SC of `H` is a `ProjW` word. -/
theorem sc_projW {c b : U64} (hc : c ∈ P1.Heap.scs H) (hin : InSC c (P1.Heap.scBits H c) b) :
    ProjW (L := L) H Cs s b := by
  obtain ⟨z, hz⟩ := hc
  have e : P1.Heap.scBits H c = z := P1.Heap.scBits_eq hz
  rw [e] at hin
  exact Or.inl ⟨c, .sc z, hz, hin.1, by simpa only [P1.HKind.bits] using hin.2⟩

set_option maxHeartbeats 4000000 in
/-- **`handle_yield` writes only `ProjW`** at an `RR` `JAtZ` state with action resume (module docstring). -/
theorem yieldProjW (hA : P0.ArchTotal arI) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hres : σ.schedulerAction = .resumeCurThread) (hRR : SInvRr.RR σ) :
    syscall.handle_yield st arI s a ⦃ r => P1.WritesIn st s r.1 (ProjW (L := L) H Cs s) ⦄ := by
  have hI := J.entryInv hres
  obtain ⟨⟨Q0, R0, h0⟩, hB0, hX0, hS0, -, hcA0, hna0, hcsc0⟩ := hI
  have hSg0 : SgOK st (P1.Heap.omega H) (P1.Heap.frame H) s := J.blk.2.2.2.2
  -- the current SC's period is `0` (as `budOk_projW_rr`)
  have hC : CurInv σ := J.curInv (by rw [hres]; intro e; cases e)
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0', hc, hs⟩ := hS.lists
  obtain ⟨hscC, -, -, -, -, -, -⟩ := CurInv.facts hS J.inv hC
  have ecsc : L.cscW s = nodeW st s Z.c layout.node.CUR_SC := by
    show L.mem s (L.nodeAt s (L.cpu s) _) = _; rw [hc.cur]; rfl
  obtain ⟨x, n, hk, hx⟩ := hs.scs _ hscC
  have hx0 : x.scPeriod = 0 := SInvRr.rr_period hRR hk
  have hp0 : L.rperiod s (L.cscW s) = 0#u64 := by
    rw [ecsc]; exact P1.eq_of_bv (by rw [← hx.period, hx0]; rfl)
  have hcS : L.cscW s ∈ P1.Heap.scs H := hX0.2.2.cur
  unfold syscall.handle_yield
  step with sched.cur_sc.spec as ⟨csc, ecsc'⟩
  have e1 : csc = L.cscW s := ecsc'
  subst e1
  step with obj.Sc.consumed.spec as ⟨i⟩
  step with sched.consumed.spec as ⟨i1⟩
  step as ⟨total, _⟩
  step with sporadic.head.spec as ⟨hd, ehd⟩
  refine WP.spec_bind (Fl4Proofs.P2.Stall.sched.charge_budget.rr (Kp := ∅) (Nd := False)
    (Es := (∅ : Set U64)) hA s a hd.amount false Q0 R0 h0 hB0 hX0 hSg0 hS0 hcsc0 hna0 hcA0
    (Set.notMem_empty _) (fun _ h => h) hp0) ?_
  rintro ⟨s1, a1⟩ hr
  try simp only [WP.uncurry'_pair] at hr
  obtain ⟨⟨⟨Q1, R1, h1⟩, -, hX1, -, -⟩, F, -, -⟩ := hr
  have F1 : P1.WritesIn st s s1 (ProjW (L := L) H Cs s) :=
    (Fl4Proofs.P1.WritesA.w F).mono fun _ hb => cur0wN_projW J.kern.heap h0.nodes (Or.inl hb)
  try simp only [WP.uncurry'_pair]
  step with obj.Sc.set_consumed.spec as ⟨s2, e2⟩
  subst e2
  obtain ⟨hP, hz⟩ := hX1.1.sc _ hcS
  obtain ⟨h8, h128, -⟩ := sc_lo hP hz
  have hv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
  have hcv : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
  have hal : Aligned (core.num.U64.wrapping_add (L.cscW s) layout.sc.CONSUMED) := by
    unfold Aligned; rw [hv, hcv]; omega
  have hin : InSC (L.cscW s) (P1.Heap.scBits H (L.cscW s))
      (core.num.U64.wrapping_add (L.cscW s) layout.sc.CONSUMED) :=
    ⟨by rw [hv]; omega, by rw [hv]; omega⟩
  exact F1.projW_trans ((writesIn_wr hal).mono fun b hb => by subst hb; exact sc_projW hcS hin)

end

end Fl4Proofs.P3.Mc
