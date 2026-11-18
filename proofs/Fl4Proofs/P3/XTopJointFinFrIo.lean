/-
P3 (DESIGN.md §9), CSpace: **the frame and IO port caps' finalisation,
final or not** (toward XTopJointDelR's `jFinAt_frio`), at any loop invariant
`W` and readiness `Rd`.

FL4's `finalise_cap_object` of a frame cap unmaps it when mapped (whatever
its finality: l4v `arch_finalise_cap` of a `FrameCap`), of an IO port cap
revokes the owner VCPU's ports when it has one; the other frame and IO port
caps' finalisation does nothing (`fin_idle`).

* `FrMapK`: a frame cap mapped in a VSpace (FL4's `vspace::unmap_page`, the
  spec's `unmap_page`); `FrVtK`: the VT-x work, a frame cap mapped in an
  EPT (`ept::unmap`) or an IO port cap with an owner (`vcpu::revoke_ports`).
* `EmptyReady.of_apart`: a slot is ready when no object of P1's heap `H`
  meets its cap's range (a frame's memory is no kernel object);
  `EmptyReady.of_nonphys`: a slot of a non-physical cap (an IO port cap) is
  ready.
* `finFrIo_of`: the finalisation of every frame and IO port cap
  (`FinObjHypWRK` at `W`, `Rd`), from the `FrMapK` and `FrVtK` steps at `W`
  and `Rd` at the slot of such a cap at `W`; the others by `fin_idle`, the
  state kept.
-/
import Fl4Proofs.P3.XTopJointEmpty
import Fl4Proofs.P3.DelW
import Fl4Proofs.P3.DelObj
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

/-- A frame cap mapped in a VSpace (not an EPT): its finalisation unmaps it. -/
def FrMapK (c : capability.Cap) : Prop := ∃ p sz r d asid va, c = .Frame p sz r d true false asid va

/-- The VT-x work of a finalisation: a frame cap mapped in an EPT, or an IO
port cap with an owner VCPU. -/
def FrVtK (c : capability.Cap) : Prop :=
  (∃ p sz r d asid va, c = .Frame p sz r d true true asid va) ∨ ∃ f l o, c = .IoPort f l o ∧ o ≠ 0#u64

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **A slot is ready when no object of `H` meets its cap's range**: the
range's words off `H`'s objects (dead, `deadP_none`), the current SC (an
`H` object) outside it. -/
theorem EmptyReady.of_apart {H : P1.Heap} {G : MdbGhost} {s : S} {x : U64}
    (hap : ∀ q k, H q = some k → q.val + 2 ^ k.bits ≤ baseF (capV (L.mem s) x) ∨ topF (capV (L.mem s) x) < q.val) :
    EmptyReady (L := L) H G s x := by
  intro _ _
  refine ⟨fun lo hi hlh h1 h2 => Or.inr fun q hq => ?_, fun z hz h1 h2 => ?_⟩
  · cases hk : H q with
    | none => exact deadP_none hk
    | some k =>
      exfalso
      have : 1 ≤ 2 ^ k.bits := Nat.one_le_two_pow
      rcases hap q k hk with h | h <;> omega
  · exfalso
    have : 1 ≤ 2 ^ (P1.HKind.sc z).bits := Nat.one_le_two_pow
    rcases hap _ _ hz with h | h <;> omega

/-- **A slot of a non-physical cap is ready** (`EmptyReady` asks nothing of it). -/
theorem EmptyReady.of_nonphys {H : P1.Heap} {G : MdbGhost} {s : S} {x : U64}
    (hp : physF (capV (L.mem s) x) = false) : EmptyReady (L := L) H G s x := by
  intro h; rw [hp] at h; cases h

/-- An IO port cap is not physical. -/
theorem physF_ioPort (f l o : U64) : physF (.IoPort f l o) = false := ok_inj (phys_eq _).symm

/-- **A frame or IO port cap's slot is ready** when, for a frame, no object
of `H` meets its range. -/
theorem EmptyReady.frio {H : P1.Heap} {G : MdbGhost} {s : S} {x : U64} {c : capability.Cap}
    (hcv : capV (L.mem s) x = c) (hk : isFrame c = true ∨ ∃ f l o, c = .IoPort f l o)
    (hap : isFrame c = true → ∀ q k, H q = some k → q.val + 2 ^ k.bits ≤ baseF c ∨ topF c < q.val) :
    EmptyReady (L := L) H G s x := by
  rcases hk with hf | ⟨f, l, o, rfl⟩
  · exact EmptyReady.of_apart (by rw [hcv]; exact hap hf)
  · exact EmptyReady.of_nonphys (by rw [hcv]; exact physF_ioPort f l o)

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The frame and IO port caps' finalisation** (module docstring): the
mapped frames' (`FrMapK`) and the VT-x work's (`FrVtK`) at `W` given, `Rd`
after from `hRd`; the others do nothing (`fin_idle`). -/
theorem finFrIo_of {W : S → A → Fl4Spec.State Unit → MdbGhost → Prop}
    {Rd : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop} {th : TypedHeap}
    (hMap : FinObjHypWRK (L := L) arI W (fun _ _ _ _ _ => True) th FrMapK)
    (hVt : FinObjHypWRK (L := L) arI W (fun _ _ _ _ _ => True) th FrVtK)
    (hRd : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (c : capability.Cap),
      W s a σ G → AbsSlot th sl → capV (L.mem s) (cslotAddr sl) = c →
      (isFrame c = true ∨ ∃ f l o, c = .IoPort f l o) → Rd s a σ G (cslotAddr sl)) :
    FinObjHypWRK (L := L) arI W Rd th (fun c => isFrame c = true ∨ ∃ f l o, c = .IoPort f l o) := by
  intro s a σ G sl c hDS hW hA hc hk hK
  have hcv := capV_of_capAt hc
  -- the steps doing work, `Rd` after from `hRd`
  have lift : ∀ {Kd : capability.Cap → Prop},
      FinObjHypWRK (L := L) arI W (fun _ _ _ _ _ => True) th Kd → Kd c →
      objects.finalise_cap st arI s a c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) false ⦃ r =>
        r.1.1 = finRem c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) ∧ CleanCap r.1.2 ∧ CapWf r.1.2 ∧
        ∃ σ' G', ((absCap r.1.1, absCap r.1.2), σ') ∈
            (Fl4Spec.finaliseCap (Z := Unit) (absCap c) (decide (Fl4Spec.isFinalCap' (absCap c) σ)) σ).1 ∧
          DState (L := L) th r.2.1 σ' G' ∧ capV (L.mem r.2.1) (cslotAddr sl) = c ∧
          (∀ y, IsSlot th y → y ≠ cslotAddr sl → capV (L.mem r.2.1) y = capV (L.mem s) y ∨
            (capV (L.mem r.2.1) y = .Null ∧ isZb (capV (L.mem s) y) = false)) ∧
          MdbStep (L.mem s) G (L.mem r.2.1) G' ∧ W r.2.1 r.2.2 σ' G' ∧ Rd r.2.1 r.2.2 σ' G' (cslotAddr sl) ⦄ := by
    intro Kd hP hKd
    refine WP.spec_mono (hP s a σ G sl c hDS hW hA hc hk hKd) ?_
    rintro r ⟨h1, h2, h3, σ', G', h4, h5, h6, h7, h8, h9, -⟩
    exact ⟨h1, h2, h3, σ', G', h4, h5, h6, h7, h8, h9, hRd _ _ _ _ sl c h9 hA h6 hK⟩
  -- the idle ones: the state kept
  have idle : ¬ FinWork c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) →
      objects.finalise_cap st arI s a c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) false ⦃ r =>
        r.1.1 = finRem c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) ∧ CleanCap r.1.2 ∧ CapWf r.1.2 ∧
        ∃ σ' G', ((absCap r.1.1, absCap r.1.2), σ') ∈
            (Fl4Spec.finaliseCap (Z := Unit) (absCap c) (decide (Fl4Spec.isFinalCap' (absCap c) σ)) σ).1 ∧
          DState (L := L) th r.2.1 σ' G' ∧ capV (L.mem r.2.1) (cslotAddr sl) = c ∧
          (∀ y, IsSlot th y → y ≠ cslotAddr sl → capV (L.mem r.2.1) y = capV (L.mem s) y ∨
            (capV (L.mem r.2.1) y = .Null ∧ isZb (capV (L.mem s) y) = false)) ∧
          MdbStep (L.mem s) G (L.mem r.2.1) G' ∧ W r.2.1 r.2.2 σ' G' ∧ Rd r.2.1 r.2.2 σ' G' (cslotAddr sl) ⦄ := by
    intro hnw
    obtain ⟨cl, he, hmem, hcl, hrem, hnio⟩ := fin_idle (st := st) (L := L) arI s a σ c hk _ hnw
    obtain ⟨c', ac, hc', hca, -⟩ := hDS.1.1.abs_cap hA
    have hcw : CapWf c := by rw [hc] at hc'; rw [eq_of_ok_eq hc']; exact hca.1
    have hcc : CleanCap cl ∧ CapWf cl := by
      rcases hK with hf | ⟨f, l, o, rfl⟩
      · have e : cl = .Null := hnio (fun f l e => by rw [e] at hf; simp [isFrame] at hf)
        subst e; exact ⟨trivial, trivial⟩
      · rcases hcl with rfl | rfl
        · exact ⟨trivial, trivial⟩
        · exact ⟨trivial, hcw⟩
    rw [he, WP.spec_ok]
    exact ⟨hrem.symm, hcc.1, hcc.2, σ, G, hmem, hDS, hcv, fun y _ _ => Or.inl rfl, MdbStep.refl hDS.1.2.2.1,
      hW, hRd s a σ G sl c hW hA hcv hK⟩
  rcases hK with hf | ⟨f, l, o, rfl⟩
  · cases c <;> simp only [isFrame, Bool.false_eq_true] at hf
    case Frame p sz r d m ep asid va =>
      cases m
      · refine idle ?_
        rintro (⟨-, h, -⟩ | ⟨_, _, _, _, _, _, _, e⟩)
        · simp [isFrame] at h
        · cases e
      · cases ep
        · exact lift hMap ⟨p, sz, r, d, asid, va, rfl⟩
        · exact lift hVt (Or.inl ⟨p, sz, r, d, asid, va, rfl⟩)
  · by_cases ho : o = 0#u64
    · subst ho
      refine idle ?_
      rintro (⟨-, -, h⟩ | ⟨_, _, _, _, _, _, _, e⟩)
      · exact h f l rfl
      · cases e
    · exact lift hVt (Or.inr ⟨f, l, o, rfl, ho⟩)

end

end

end Fl4Proofs.P3
