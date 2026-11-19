/-
P3 (DESIGN.md §9), Untyped's reset (the drop step), part 3: **`XTopAt`
across the spec's detype** (stage B of UtDropSets' plan; handoff/utj.md
"Round 8").

The step is ghost-only on FL4's side: the spec state goes from `σ` to `σ'`
(`SDrop` of the untyped's region `regionSet p (2^sb)`, the other fields
kept), FL4's state stays `s`. The sets after: the typed heap restricted to
off the region (`restrictTh`), the VSpace sets pruned (VsDrop's `pr*`), the
IPC and scheduler sets as given (they hold no object of the region, `hZ`:
`XTopAt.keepS` cuts them first, UtDropJ).

* `Vs.TopPlaced.dropMono`, `IpcApart.restrict`, `ScApart.restrict`: the
  placements at the smaller sets;
* `FinInv.drop`: `FinInv` at the restricted typed heap;
* `XTopAt.dropB`: the composite relation after the detype, with the VSpace
  part by `Vs.vsDropOK` (its premise `VsReachMiss` [J], VsDrop.lean), the
  CSpace part by `detype_rel` (the untyped cap childless, no straddling
  object and no MDB slot in the region: `UtCapP3`'s `nostr`/`ns`), the
  others by `TopSR.step` (an `OStep` whose region holds none of the sets'
  objects).
-/
import Fl4Proofs.P3.UtDropSpec
import Fl4Proofs.P3.VsDrop
import Fl4Proofs.P3.UntypedReset
import Fl4Proofs.P3.DecodeTopD
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

/-- `Z` after the detype of `[rl, rh)` (module docstring): the typed heap
restricted, the VSpace sets pruned at FL4's memory `m`. -/
abbrev XSets.dropV (Z : XSets) (rl rh : Nat) (m : U64 → U64) : XSets :=
  { Z with
    th := restrictTh Z.th rl rh
    P := prP rl rh m Z.P Z.L4 Z.L3 Z.L2 Z.L1
    L4 := pr4 rl rh m Z.L4 Z.L3 Z.L2 Z.L1
    L3 := pr3 rl rh m Z.L3 Z.L2 Z.L1
    L2 := pr2 rl rh m Z.L2 Z.L1
    L1 := pr1 rl rh Z.L1 }

section Mono
variable {th : TypedHeap} {lo hi : Nat}

theorem OutsideObjects.restrict {b : U64} (h : OutsideObjects th b) : OutsideObjects (restrictTh th lo hi) b :=
  ⟨h.1, fun p k hp => h.2 p k (restrictTh_some hp).1⟩

theorem Vs.SlotW.of_restrict {b : U64} (h : SlotW (restrictTh th lo hi) b) : SlotW th b := by
  obtain ⟨x, hx, e⟩ := h
  exact ⟨x, hx.of_restrict, e⟩

theorem Vs.VsWrite.mono {P P' : Set U64} (hP : P' ⊆ P) {ksb b : U64} (h : VsWrite P' ksb b) : VsWrite P ksb b := by
  rcases h with h | ⟨p, hp, lo, hl, e⟩
  · exact Or.inl h
  · exact Or.inr ⟨p, hP hp, lo, hl, e⟩

theorem Vs.PtWAll.mono {L4 L3 L2 L1 L4' L3' L2' L1' : Set U64} (h4 : L4' ⊆ L4) (h3 : L3' ⊆ L3) (h2 : L2' ⊆ L2)
    (h1 : L1' ⊆ L1) {b : U64} (h : PtWAll L4' L3' L2' L1' b) : PtWAll L4 L3 L2 L1 b := by
  obtain ⟨p, hp, i, hi, e⟩ := h
  refine ⟨p, ?_, i, hi, e⟩
  rcases hp with hp | hp | hp | hp
  · exact Or.inl (h4 hp)
  · exact Or.inr (Or.inl (h3 hp))
  · exact Or.inr (Or.inr (Or.inl (h2 hp)))
  · exact Or.inr (Or.inr (Or.inr (h1 hp)))

theorem Vs.VObj.mono {P L4 L3 L2 L1 P' L4' L3' L2' L1' : Set U64} (hP : P' ⊆ P) (h4 : L4' ⊆ L4) (h3 : L3' ⊆ L3)
    (h2 : L2' ⊆ L2) (h1 : L1' ⊆ L1) {ksb a : U64}
    (h : VObj (restrictTh th lo hi) P' L4' L3' L2' L1' ksb a) : VObj th P L4 L3 L2 L1 ksb a := by
  rcases h with ⟨q, r, hq, g⟩ | ⟨t, ht, g⟩ | ⟨q, hq, g⟩ | h
  · exact Or.inl ⟨q, r, (restrictTh_some hq).1, g⟩
  · exact Or.inr (Or.inl ⟨t, (restrictTh_some ht).1, g⟩)
  · refine Or.inr (Or.inr (Or.inl ⟨q, ?_, g⟩))
    rcases hq with hq | hq | hq | hq | hq
    · exact Or.inl (hP hq)
    · exact Or.inr (Or.inl (h4 hq))
    · exact Or.inr (Or.inr (Or.inl (h3 hq)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (h2 hq))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (h1 hq))))
  · exact Or.inr (Or.inr (Or.inr h))

variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`TopPlaced` at the restricted typed heap and smaller VSpace sets.** -/
theorem Vs.TopPlaced.dropMono {P L4 L3 L2 L1 P' L4' L3' L2' L1' N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)}
    {c : U64} {s : S} {σ : Fl4Spec.State Unit} (h : TopPlaced st th P L4 L3 L2 L1 N T C E R B c s σ)
    (hP : P' ⊆ P) (h4 : L4' ⊆ L4) (h3 : L3' ⊆ L3) (h2 : L2' ⊆ L2) (h1 : L1' ⊆ L1)
    (hvp : VsPlaced P' (L.ksb s)) (hpp : PtPlaced L4' L3' L2' L1') :
    TopPlaced st (restrictTh th lo hi) P' L4' L3' L2' L1' N T C E R B c s σ :=
  { ep := h.ep, vs := hvp, pt := hpp, pl := h.pl.restrict,
    disj := fun a ho hv => h.disj a ho (VObj.mono hP h4 h3 h2 h1 hv),
    nodeE := h.nodeE,
    po := fun b hb => (h.po b (PtWAll.mono h4 h3 h2 h1 hb)).restrict,
    ps := fun b hb hs => h.ps b (PtWAll.mono h4 h3 h2 h1 hb) hs.of_restrict,
    pv := fun b hb hw => h.pv b (PtWAll.mono h4 h3 h2 h1 hb) (hw.mono hP),
    vo := fun b hb => (h.vo b (hb.mono hP)).restrict,
    sd := fun b hb hs => h.sd b (hb.mono hP) hs.of_restrict,
    tko := fun t ht => h.tko t (restrictTh_some ht).1 }

theorem Ipc.IpcApart.restrict {N T E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {kb c : U64}
    (h : IpcApart th N T E R B kb c) : IpcApart (restrictTh th lo hi) N T E R B kb c :=
  { h with
    slot := fun a ha x hx => h.slot a ha x hx.of_restrict
    node := fun a h1 h2 x hx => h.node a h1 h2 x hx.of_restrict
    ks := fun a h1 h2 h3 x hx => h.ks a h1 h2 h3 x hx.of_restrict }

theorem Ipc.ScApart.restrict {C : Set U64} {σ : Fl4Spec.State Unit} (h : ScApart th C σ) :
    ScApart (restrictTh th lo hi) C σ :=
  fun sc hsc x n hk a ha y hy => h sc hsc x n hk a ha y hy.of_restrict

end Mono

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

/-- The detype's region. -/
abbrev RgOf (p sb : U64) : Fl4Spec.ObjRef → Prop := fun o => o ∈ regionSet p.bv sb.val

theorem rgOf_iff {p sb : U64} (hsb : sb.val < 64) (hfit : p.val + 2 ^ sb.val ≤ 2 ^ 64) (q : U64) :
    RgOf p sb q.bv ↔ p.val ≤ q.val ∧ q.val < p.val + 2 ^ sb.val :=
  regionSet_iff p q sb.val hsb hfit

/-- **`FinInv` across the detype** at the restricted typed heap. -/
theorem FinInv.drop {th : TypedHeap} {m : U64 → U64} {σ σ' : Fl4Spec.State Unit} {G : MdbGhost} {p sb : U64}
    (hsb : sb.val < 64) (hfit : p.val + 2 ^ sb.val ≤ 2 ^ 64) (hFI : FinInv th m σ G) (hD : SDrop (RgOf p sb) σ σ') :
    FinInv (restrictTh th p.val (p.val + 2 ^ sb.val)) m σ' G := by
  refine ⟨fun o => ⟨fun r cs h hw => ?_, fun t h => ?_⟩, hFI.fm⟩
  · obtain ⟨k0, hb⟩ := hD.back h
    rw [restrictTh_out (by rw [← rgOf_iff hsb hfit ⟨o⟩]; exact k0)]
    exact (hFI.kt o).1 r cs hb hw
  · obtain ⟨k0, hb⟩ := hD.back h
    rw [restrictTh_out (by rw [← rgOf_iff hsb hfit ⟨o⟩]; exact k0)]
    exact (hFI.kt o).2 t hb

set_option maxHeartbeats 4000000 in
/-- **`XTopAt` across the spec's detype** (module docstring). -/
theorem XTopAt.dropB {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {a : A} {σ σ' : Fl4Spec.State Unit}
    {p sb : U64} (hX : XTopAt (L := L) AR Z s a σ) (hsb : sb.val < 64) (hfit : p.val + 2 ^ sb.val ≤ 2 ^ 64)
    (hD : SDrop (RgOf p sb) σ σ') (hK : SKeep (RgOf p sb) σ)
    (hcdt : σ'.cdt = σ.cdt) (horig : σ'.isOriginalCap = σ.isOriginalCap)
    (hrepr : σ'.reprogramTimer = σ.reprogramTimer) (hcdom : σ'.curDomain = σ.curDomain)
    (hdtime : σ'.domainTime = σ.domainTime) (hist : σ'.interruptStates = σ.interruptStates)
    (hinode : σ'.interruptIrqNode = σ.interruptIrqNode) (harch : σ'.archState = σ.archState)
    (hdl : σ'.domainList = σ.domainList) (hdsi : σ'.domainStartIndex = σ.domainStartIndex)
    (hB : ∀ wp ∈ Z.B, loadWordAt σ'.machineState.underlyingMemory wp.2 =
      loadWordAt σ.machineState.underlyingMemory wp.2)
    (hZ : ∀ q : U64, p.val ≤ q.val → q.val < p.val + 2 ^ sb.val →
      q ∉ Z.T ∧ q ∉ Z.E ∧ q ∉ Z.R ∧ q ∉ Z.N ∧ q ∉ Z.C)
    (hU : UtInv (L.mem s) Z.G) {x fi : U64} {dev : Bool} (hx : x ∈ Z.G.chains.flatten)
    (hcx : capV (L.mem s) x = .Untyped p sb fi dev) (hnd : ∀ y, ¬ Mdb.Desc Z.G.par y x)
    (hN : NoStraddle Z.th p.val (p.val + 2 ^ sb.val))
    (hns : ∀ a ∈ Z.G.chains.flatten, a.val < p.val ∨ p.val + 2 ^ sb.val ≤ a.val)
    {XP X4 X3 X2 X1 : Set U64} (hXP : XP ⊆ Z.P) (hX4 : X4 ⊆ Z.L4) (hX3 : X3 ⊆ Z.L3) (hX2 : X2 ⊆ Z.L2)
    (hX1 : X1 ⊆ Z.L1) (hM : VsReachMiss p.val (p.val + 2 ^ sb.val) (L.mem s) (L.ksb s) XP X4 X3 X2 X1) :
    XTopAt (L := L) AR (Z.dropV p.val (p.val + 2 ^ sb.val) (L.mem s)) s a σ' ∧
      ∀ k q, VsReach (L.mem s) (L.ksb s) XP X4 X3 X2 X1 k q →
        q ∈ lvlSet (prP p.val (p.val + 2 ^ sb.val) (L.mem s) Z.P Z.L4 Z.L3 Z.L2 Z.L1)
          (pr4 p.val (p.val + 2 ^ sb.val) (L.mem s) Z.L4 Z.L3 Z.L2 Z.L1)
          (pr3 p.val (p.val + 2 ^ sb.val) (L.mem s) Z.L3 Z.L2 Z.L1)
          (pr2 p.val (p.val + 2 ^ sb.val) (L.mem s) Z.L2 Z.L1) (pr1 p.val (p.val + 2 ^ sb.val) Z.L1) k := by
  obtain ⟨⟨hS, hR, hPt, hPI, hCO⟩, ⟨hPl, hCR, hFI, hDm, hMO, hIA, hSA⟩, -, hE⟩ := hX
  obtain ⟨hSR, hV, hML, hC, hI⟩ := hCR
  have hO : OStep (RgOf p sb) σ σ' := by
    refine ⟨hD.rq, hD.rel, hD.ct, hD.act, hD.csc, hD.time, hD.cons, hrepr, hcdom, hdtime, hD.idle, hD.isc, hist,
      hinode, by rw [harch], by rw [harch], fun q hq => ?_⟩
    by_cases hr : RgOf p sb q
    · exact ⟨Or.inl hr, by rw [hD.kin q hr]; exact Or.inl rfl⟩
    · exact absurd (hD.kout q hr) hq
  have hS1 := TopSR.step (Rw := fun _ => False) hS rfl rfl (fun _ _ _ _ => rfl) (fun _ h => h.elim) hO
    (fun q hq => hZ q ((rgOf_iff hsb hfit q).1 hq).1 ((rgOf_iff hsb hfit q).1 hq).2) hB
    (fun h => by rw [harch]; exact h)
  have hkh : ∀ q : U64, q.val < p.val ∨ p.val + 2 ^ sb.val ≤ q.val → σ'.kheap q.bv = σ.kheap q.bv := fun q hq =>
    hD.kout _ (fun h => by have := (rgOf_iff hsb hfit q).1 h; omega)
  have hVD := vsDropOK hR hPt hPI hS.2.pt hS.2.vs (⟨fun _ _ => rfl, fun _ _ => rfl, hkh, harch⟩ :
      VsDrop p.val (p.val + 2 ^ sb.val) (L.ksb s) (L.mem s) (L.mem s) σ σ') hXP hX4 hX3 hX2 hX1 hM
  dsimp only at hVD
  obtain ⟨hR', hPt', hPI', ⟨s1, s2, s3, s4, s5⟩, -, hreach⟩ := hVD
  obtain ⟨hSR', hV', hML', hC'⟩ := detype_rel hSR hV hPl hML hC hI hU hx hcx hnd hN hns
    (fun q hq => hkh q (by omega)) hcdt horig
  refine ⟨⟨⟨⟨hS1.1, hS1.2.dropMono s1 s2 s3 s4 s5 (VsPlaced.pr hS.2.vs) (PtPlaced.pr hS.2.pt)⟩, hR', hPt', hPI', ?_⟩,
    ⟨hPl.restrict, ⟨hSR', hV', hML', hC', hI⟩, FinInv.drop hsb hfit hFI hD,
      DomRel.frame hDm (fun _ _ => rfl) hdl hdsi, hMO, hIA.restrict, (hSA.mono hD.szKeep).restrict⟩,
    IpcRel.of hS1.1.2.2.1 hS1.1.2.1 (sched_sc hS1.1.1), hE.mono rfl hD.szKeep⟩, hreach⟩
  obtain ⟨t, h1, h2, h3⟩ := hCO
  refine ⟨t, by rw [hD.ct]; exact h1, ?_, h3⟩
  show restrictTh Z.th p.val (p.val + 2 ^ sb.val) t = some .tcb
  rw [restrictTh_out (by rw [← rgOf_iff hsb hfit t, h1]; exact hK.cur.1)]
  exact h2

end

end

end Fl4Proofs.P3
