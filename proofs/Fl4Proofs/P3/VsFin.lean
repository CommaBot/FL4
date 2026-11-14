/-
P3 (DESIGN.md §9), VSpace: **the VSpace half of `FinWorkHyp`** (DelObj):
`finalise_cap` of a final page-table, page-directory, PDPT, PML4 or ASID
pool cap (`unmap_page_table`, `unmap_page_directory`, `unmap_pdpt`,
`delete_asid`, `delete_asid_pool`) and of a mapped frame cap (`unmap_page`),
against l4v `arch_finalise_cap`.

Each post (`FinOKX`) is `FinObjHyp`'s, with the ghost tree unchanged
(`MdbStep.of_same`), plus `SlotsSame`: **none of these writes a cap slot**
(their words are page-table entries, `PtWAll`, or ASID-table and pool words,
`VsWrite`, all outside the objects), so the slot facts are the
slot-preserving ones (every cap kept). The extra relation `X` keeps `SR` and
`VsRel`.

The unmaps' and ASID deletions' relational theorems (VsPtUnmapRel, …,
VsDelRoot) are used at an instrumented relation `FinSR` (`SR`, the slots
since the start, the spec's `KFoot`, the kernel base), whose hypothesis
structures come from `SR`'s (`VsPtInnerHyps.fin`, …, `VsHyps.fin`).

The cap's side conditions (table in its ghost set, ASID non-zero, the PT's
alignment, the PML4 non-null, the pool base aligned) come from the cap
invariant `VsCapsIn`; the pool pointer non-null is a hypothesis on the ghost
pool set (`hP0`). `vs_fin_top` gives the lot at `SR := TopSR`.
-/
import Fl4Proofs.P3.VsTopCap
import Fl4Proofs.P3.VsDelRoot
import Fl4Proofs.P3.DelObj
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3 Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **`FinObjHyp`'s post**, with an extra relation `X` on the outcome. -/
def FinOKX {A : Type} (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr)
    (c : capability.Cap) (b : Bool) (X : S → A → Fl4Spec.State Unit → Prop)
    (r : (capability.Cap × capability.Cap) × S × A) : Prop :=
  r.1.1 = finRem c b ∧ CleanCap r.1.2 ∧ CapWf r.1.2 ∧
    ∃ σ' G', ((absCap r.1.1, absCap r.1.2), σ') ∈ (Fl4Spec.finaliseCap (Z := Unit) (absCap c) b σ).1 ∧
      DState (L := L) th r.2.1 σ' G' ∧ capV (L.mem r.2.1) (cslotAddr sl) = c ∧
      (∀ y, IsSlot th y → y ≠ cslotAddr sl → capV (L.mem r.2.1) y = capV (L.mem s) y ∨
        (capV (L.mem r.2.1) y = .Null ∧ isZb (capV (L.mem s) y) = false)) ∧
      MdbStep (L.mem s) G (L.mem r.2.1) G' ∧ X r.2.1 r.2.2 σ'

/-- Writes outside the objects keep every slot. -/
theorem SlotsSame.of_writes {th : TypedHeap} (hP : Placed th) {s s' : S} {W : U64 → Prop}
    (hW : WritesIn st s s' W) (hWo : ∀ b, W b → OutsideObjects th b) : SlotsSame th (L.mem s) (L.mem s') := by
  intro y hy
  have h0 := SlotFoot.of_writes hP hW hWo 0#u64 y hy
  have h1 := SlotFoot.of_writes hP hW hWo 1#u64 y hy
  by_cases e : y = 0#u64
  · subst e
    exact ⟨(h1.2.2 (by decide)).1, (h1.2.2 (by decide)).2, h1.1, h1.2.1⟩
  · exact ⟨(h0.2.2 e).1, (h0.2.2 e).2, h0.1, h0.2.1⟩

/-- **The finalisation's post from a slot-preserving step** with the spec's
`KFoot`. -/
theorem fin_after {th : TypedHeap} {s s' : S} {σ σ' : Fl4Spec.State Unit} {G : MdbGhost}
    {sl : Fl4Spec.CslotPtr} {c : capability.Cap} (hDS : DState (L := L) th s σ G) (hA : AbsSlot th sl)
    (hc : capAt (L.mem s) (cslotAddr sl) = ok c) (hSS : SlotsSame th (L.mem s) (L.mem s'))
    (hSt' : StateRel th (L.mem s') σ') (hK : KFoot σ σ') :
    DState (L := L) th s' σ' G ∧ capV (L.mem s') (cslotAddr sl) = c ∧
      (∀ y, IsSlot th y → y ≠ cslotAddr sl → capV (L.mem s') y = capV (L.mem s) y ∨
        (capV (L.mem s') y = .Null ∧ isZb (capV (L.mem s) y) = false)) ∧
      MdbStep (L.mem s) G (L.mem s') G := by
  obtain ⟨hCR, hD, hFI⟩ := hDS
  have hx := hA.isSlot
  have hcv : capV (L.mem s') (cslotAddr sl) = c := by rw [hSS.capV hx]; exact capV_of_capAt hc
  obtain ⟨hCR', hFI'⟩ := crel_after hCR hFI hc hSt' (P3.SlotsValid.of_caps hCR.2.1 (fun y hy => hSS.capAt hy))
    (SlotFoot.of_same hSS _) (by rw [hcv]; exact ⟨rfl, rfl, rfl⟩) hK
  exact ⟨⟨hCR', hD.of_same hSS, hFI'⟩, hcv, fun y hy _ => Or.inl (hSS.capV hy),
    MdbStep.of_same hCR.2.2.1 hSS⟩

/-- The finalisations without work keep everything. -/
theorem fin_none {A : Type} {th : TypedHeap} {s : S} {a : A} {σ : Fl4Spec.State Unit} {G : MdbGhost}
    {sl : Fl4Spec.CslotPtr} {c : capability.Cap} {b : Bool} {X : S → A → Fl4Spec.State Unit → Prop}
    (hDS : DState (L := L) th s σ G) (hc : capAt (L.mem s) (cslotAddr sl) = ok c) (hX : X s a σ)
    (hrem : finRem c b = .Null)
    (hspec : ((Fl4Spec.Cap.nullCap, Fl4Spec.Cap.nullCap), σ) ∈ (Fl4Spec.finaliseCap (Z := Unit) (absCap c) b σ).1) :
    FinOKX (L := L) th s σ G sl c b X ((.Null, .Null), s, a) ∧ SlotsSame th (L.mem s) (L.mem s) :=
  ⟨⟨hrem.symm, trivial, trivial, σ, G, hspec, hDS, capV_of_capAt hc, fun _ _ _ => Or.inl rfl,
    MdbStep.refl hDS.1.2.2.1, hX⟩, SlotsSame.refl _ _⟩

/-! ## The instrumented relation -/

/-- `SR` with the slots kept since `s0`, the spec's `KFoot` since `σ0`, and the
kernel base. -/
def FinSR (st : machine.Store S) [L : LawfulStore st] {A : Type} (th : TypedHeap)
    (SR : S → A → Fl4Spec.State Unit → Prop) (s0 : S) (σ0 : Fl4Spec.State Unit) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop :=
  SR s a σ ∧ SlotsSame th (L.mem s0) (L.mem s) ∧ KFoot σ0 σ ∧ L.ksb s = L.ksb s0

variable {A : Type} {ar : machine.Arch A} {th : TypedHeap} {P L4 L3 L2 L1 : Set U64}
  {SR : S → A → Fl4Spec.State Unit → Prop} {s0 : S} {σ0 : Fl4Spec.State Unit}

theorem FinSR.init {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : SR s a σ) : FinSR st th SR s σ s a σ :=
  ⟨h, SlotsSame.refl _ _, KFoot.refl _, rfl⟩

/-- A stability field carried to `FinSR`. -/
theorem fin_stab (hPl : Placed th) {X : U64 → Prop} {Step : Fl4Spec.State Unit → Fl4Spec.State Unit → Prop}
    (hX : ∀ b, X b → OutsideObjects th b) (hK : ∀ σ σ', Step σ σ' → KFoot σ σ')
    (h : ∀ s s' a σ σ', SR s a σ → WritesIn st s s' X → Step σ σ' → SR s' a σ') :
    ∀ s s' a σ σ', FinSR st th SR s0 σ0 s a σ → WritesIn st s s' X → Step σ σ' → FinSR st th SR s0 σ0 s' a σ' :=
  fun s s' a σ σ' ⟨h1, h2, h3, h4⟩ hw hst =>
    ⟨h s s' a σ σ' h1 hw hst, h2.trans (SlotsSame.of_writes hPl hw hX), h3.trans (hK σ σ' hst), hw.1.trans h4⟩

/-- A machine operation's outcome is `KFoot`. -/
theorem kfoot_mop {α : Type} {mop : Fl4Spec.NonDet Fl4Spec.MachineState α} {σ σ' : Fl4Spec.State Unit} {r : α}
    (h : (r, σ') ∈ (Fl4Spec.doMachineOp (Z := Unit) mop σ).1) : KFoot σ σ' := by
  obtain ⟨ms, rfl⟩ := doMachineOp_mem h; exact KFoot.ms _ ms

theorem kfoot_arch_step {σ σ' : Fl4Spec.State Unit}
    (h : ∃ p f f', σ.kheap p = some (.archObj f) ∧ σ' = updK σ p (.archObj f')) : KFoot σ σ' := by
  obtain ⟨p, f, f', hk, rfl⟩ := h; exact KFoot.arch hk _

theorem kfoot_cr3 (σ : Fl4Spec.State Unit) (c : Fl4Spec.Cr3) : KFoot σ (cr3Upd σ c) :=
  ⟨rfl, rfl, fun _ h => absurd rfl h⟩

theorem kfoot_table (σ : Fl4Spec.State Unit) (t : Fl4Spec.AsidHighIndex → Option Fl4Spec.ObjRef) :
    KFoot σ { σ with archState := { σ.archState with x64AsidTable := t } } :=
  ⟨rfl, rfl, fun _ h => absurd rfl h⟩

section Fin
variable (hPl : Placed th) (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b)
include hPl hPO

theorem VsPtInnerHyps.fin (hH : VsPtInnerHyps st A ar L2 SR) : VsPtInnerHyps st A ar L2 (FinSR st th SR s0 σ0) where
  pdStable := fin_stab hPl (fun b ⟨q, hq, i, hi, e⟩ => hPO b ⟨q, Or.inr (Or.inr (Or.inl hq)), i, hi, e⟩)
    (fun _ _ h => by obtain ⟨p, f, f', hk, rfl⟩ := h; exact KFoot.arch hk _) hH.pdStable
  flushOK := hH.flushOK
  flushPS := fun s a σ vs asid h => WP.spec_mono (hH.flushPS s a σ vs asid h.1)
    fun _ ⟨σ', hm, hS⟩ => ⟨σ', hm, hS, h.2.1, h.2.2.1.trans (kfoot_mop hm), h.2.2.2⟩
  flushTblOK := hH.flushTblOK
  flushTbl := fun s a σ vs v pt asid h hal hf => WP.spec_mono (hH.flushTbl s a σ vs v pt asid h.1 hal hf)
    fun _ ⟨σ', hm, hS⟩ => ⟨σ', hm, hS, h.2.1, h.2.2.1.trans (by obtain ⟨f, hk⟩ := hf; exact kfoot_flushTable hal hk _ hm),
      h.2.2.2⟩

theorem VsPdInnerHyps.fin (hH : VsPdInnerHyps st A ar L3 SR) : VsPdInnerHyps st A ar L3 (FinSR st th SR s0 σ0) where
  pdptStable := fin_stab hPl (fun b ⟨q, hq, i, hi, e⟩ => hPO b ⟨q, Or.inr (Or.inl hq), i, hi, e⟩)
    (fun _ _ h => by obtain ⟨p, f, f', hk, rfl⟩ := h; exact KFoot.arch hk _) hH.pdptStable
  flushOK := hH.flushOK
  flushPS := fun s a σ vs asid h => WP.spec_mono (hH.flushPS s a σ vs asid h.1)
    fun _ ⟨σ', hm, hS⟩ => ⟨σ', hm, hS, h.2.1, h.2.2.1.trans (kfoot_mop hm), h.2.2.2⟩
  flushAllOK := hH.flushAllOK
  flushAllH := fun s a σ vs asid h => WP.spec_mono (hH.flushAllH s a σ vs asid h.1)
    fun _ ⟨σ', hm, hS⟩ => ⟨σ', hm, hS, h.2.1, h.2.2.1.trans (kfoot_mop hm), h.2.2.2⟩

theorem VsPdptInnerHyps.fin (hH : VsPdptInnerHyps st A ar L4 SR) :
    VsPdptInnerHyps st A ar L4 (FinSR st th SR s0 σ0) where
  pml4Stable := fin_stab hPl (fun b ⟨q, hq, i, hi, e⟩ => hPO b ⟨q, Or.inl hq, i, hi, e⟩)
    (fun _ _ h => by obtain ⟨p, f, f', hk, rfl⟩ := h; exact KFoot.arch hk _) hH.pml4Stable
  flushAllOK := hH.flushAllOK
  flushAllH := fun s a σ vs asid h => WP.spec_mono (hH.flushAllH s a σ vs asid h.1)
    fun _ ⟨σ', hm, hS⟩ => ⟨σ', hm, hS, h.2.1, h.2.2.1.trans (kfoot_mop hm), h.2.2.2⟩

theorem VsUnmapPageHyps.fin (hH : VsUnmapPageHyps st A ar L3 L2 L1 SR) :
    VsUnmapPageHyps st A ar L3 L2 L1 (FinSR st th SR s0 σ0) where
  ptStable := fin_stab hPl (fun b ⟨q, hq, i, hi, e⟩ => hPO b ⟨q, Or.inr (Or.inr (Or.inr hq)), i, hi, e⟩)
    (fun _ _ h => by obtain ⟨p, f, f', hk, rfl⟩ := h; exact KFoot.arch hk _) hH.ptStable
  pdStable := fin_stab hPl (fun b ⟨q, hq, i, hi, e⟩ => hPO b ⟨q, Or.inr (Or.inr (Or.inl hq)), i, hi, e⟩)
    (fun _ _ h => by obtain ⟨p, f, f', hk, rfl⟩ := h; exact KFoot.arch hk _) hH.pdStable
  pdptStable := fin_stab hPl (fun b ⟨q, hq, i, hi, e⟩ => hPO b ⟨q, Or.inr (Or.inl hq), i, hi, e⟩)
    (fun _ _ h => by obtain ⟨p, f, f', hk, rfl⟩ := h; exact KFoot.arch hk _) hH.pdptStable
  flushPgOK := hH.flushPgOK
  flushPg := fun s a σ asid va h => WP.spec_mono (hH.flushPg s a σ asid va h.1)
    fun _ ⟨σ', hm, hS⟩ => ⟨σ', hm, hS, h.2.1, h.2.2.1.trans (kfoot_mop hm), h.2.2.2⟩

end Fin

/-- `VsHyps` carried to `FinSR` (the ASID-table and pool words outside the
objects). -/
theorem VsHyps.fin (hPl : Placed th) (hVO : ∀ b, VsWrite P (L.ksb s0) b → OutsideObjects th b)
    (hH : VsHyps st A ar P th SR) : VsHyps st A ar P th (FinSR st th SR s0 σ0) where
  stable := fun s s' a σ σ' h hw hst =>
    ⟨hH.stable s s' a σ σ' h.1 hw hst, h.2.1.trans (SlotsSame.of_writes hPl hw (fun b hb => hVO b (h.2.2.2 ▸ hb))),
      h.2.2.1.trans (by
        rcases hst with ⟨p, f, f', hk, rfl⟩ | ⟨t, rfl⟩
        · exact KFoot.arch hk _
        · exact kfoot_table _ t), hw.1.trans h.2.2.2⟩
  invalOK := hH.invalOK
  inval := fun s a σ asid vs hR h => WP.spec_mono (hH.inval s a σ asid vs hR h.1)
    fun _ ⟨σ', hm, hS⟩ => ⟨σ', hm, hS, h.2.1, h.2.2.1.trans (kfoot_mop hm), h.2.2.2⟩
  curT := fun s a σ h => hH.curT s a σ h.1
  root :=
    { setVs := fun s a σ ptr asid h => WP.spec_mono (hH.root.setVs s a σ ptr asid h.1)
        fun _ hS => ⟨hS, h.2.1, h.2.2.1.trans (kfoot_cr3 _ _), h.2.2.2⟩
      setKernel := fun s a σ h => WP.spec_mono (hH.root.setKernel s a σ h.1)
        fun _ ⟨e, hS⟩ => ⟨e, hS, h.2.1, h.2.2.1.trans (kfoot_cr3 _ _), h.2.2.2⟩ }


/-! ## The finalisations -/

/-- The extra relation of the posts: `SR` and `VsRel`. -/
def FinX (st : machine.Store S) [L : LawfulStore st] {A : Type} (P : Set U64) (SR : S → A → Fl4Spec.State Unit → Prop)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  SR s a σ ∧ VsRel P (L.mem s) (L.ksb s) σ

section Ops
variable {A : Type} {ar : machine.Arch A} {th : TypedHeap} {P L4 L3 L2 L1 : Set U64}
  {SR : S → A → Fl4Spec.State Unit → Prop}

set_option maxHeartbeats 1000000 in
/-- **A final page-table cap**: `unmap_page_table` if mapped (l4v
`unmap_page_table`); no cap slot written. -/
theorem fin_page_table (hH : VsPtInnerHyps st A ar L2 SR) (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (sl : Fl4Spec.CslotPtr) (hDS : DState (L := L) th s σ G) (hA : AbsSlot th sl) (hPl : Placed th)
    (hPP : PtPlaced L4 L3 L2 L1) (hPS : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ SlotW th b)
    (hPV : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ VsWrite P (L.ksb s) b)
    (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b) (hVP : VsPlaced P (L.ksb s))
    (hPI : PoolsIn P L4 (L.mem s)) (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (hS : SR s a σ) (hVC : VsCapsIn P L4 L3 L2 L1 (L.mem s) G)
    (p asid va : U64) (mp : Bool) (hc : capAt (L.mem s) (cslotAddr sl) = ok (.PageTable p mp asid va)) :
    objects.finalise_cap st ar s a (.PageTable p mp asid va) true false ⦃ r =>
      FinOKX (L := L) th s σ G sl (.PageTable p mp asid va) true (FinX st P SR) r ∧
        SlotsSame th (L.mem s) (L.mem r.2.1) ⦄ := by
  have hok := hVC.at hDS.1.2.2.1 hA.isSlot hc (by simp)
  simp only [VCapOK] at hok
  obtain ⟨hpL, -, hm⟩ := hok
  cases mp
  · simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok, Bool.false_eq_true, ↓reduceIte]
    exact (WP.spec_ok _).2 (fin_none (X := FinX st P SR) hDS hc ⟨hS, hR⟩ rfl (Set.mem_singleton _))
  obtain ⟨h0, hal⟩ := hm rfl
  simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok, ↓reduceIte]
  refine WP.spec_bind (unmap_page_table_rel (hH.fin (s0 := s) (σ0 := σ) hPl hPO) s a σ hPl hPP hPS hVP
    (fun b ⟨q, hq, i, hi, e⟩ => hPV b ⟨q, Or.inr (Or.inr (Or.inl hq)), i, hi, e⟩) hPI
    ⟨FinSR.init hS, hDS.1.1, hDS.1.2.1, hR, hPt⟩ asid va p h0 hal hpL) ?_
  rintro ⟨s1, a1⟩ ⟨-, -, σ', hm, ⟨⟨hS1, hSS, hK, -⟩, hSt1, -, hR1, -⟩, -⟩
  obtain ⟨hD', hcv, hsl, hMS⟩ := fin_after hDS hA hc hSS hSt1 hK
  refine (WP.spec_ok _).2 ⟨⟨rfl, trivial, trivial, σ', G, ?_, hD', hcv, hsl, hMS, hS1, hR1⟩, hSS⟩
  exact mem_bind_nd hm (Set.mem_singleton _)

set_option maxHeartbeats 1000000 in
/-- **A final page-directory cap**: `unmap_page_directory` if mapped (l4v
`unmap_pd`); no cap slot written. -/
theorem fin_page_directory (hH : VsPdInnerHyps st A ar L3 SR) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (hDS : DState (L := L) th s σ G) (hA : AbsSlot th sl) (hPl : Placed th)
    (hPP : PtPlaced L4 L3 L2 L1) (hPS : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ SlotW th b)
    (hPV : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ VsWrite P (L.ksb s) b)
    (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b) (hVP : VsPlaced P (L.ksb s))
    (hPI : PoolsIn P L4 (L.mem s)) (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (hS : SR s a σ) (hVC : VsCapsIn P L4 L3 L2 L1 (L.mem s) G)
    (p asid va : U64) (mp : Bool) (hc : capAt (L.mem s) (cslotAddr sl) = ok (.PageDirectory p mp asid va)) :
    objects.finalise_cap st ar s a (.PageDirectory p mp asid va) true false ⦃ r =>
      FinOKX (L := L) th s σ G sl (.PageDirectory p mp asid va) true (FinX st P SR) r ∧
        SlotsSame th (L.mem s) (L.mem r.2.1) ⦄ := by
  have hok := hVC.at hDS.1.2.2.1 hA.isSlot hc (by simp)
  simp only [VCapOK] at hok
  obtain ⟨hpL, -, hm⟩ := hok
  cases mp
  · simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok, Bool.false_eq_true, ↓reduceIte]
    exact (WP.spec_ok _).2 (fin_none (X := FinX st P SR) hDS hc ⟨hS, hR⟩ rfl (Set.mem_singleton _))
  have h0 := hm rfl
  simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok, ↓reduceIte]
  refine WP.spec_bind (unmap_page_directory_rel (hH.fin (s0 := s) (σ0 := σ) hPl hPO) s a σ hPl hPP hPS hVP
    (fun b ⟨q, hq, i, hi, e⟩ => hPV b ⟨q, Or.inr (Or.inl hq), i, hi, e⟩) hPI
    ⟨FinSR.init hS, hDS.1.1, hDS.1.2.1, hR, hPt⟩ asid va p h0 hpL) ?_
  rintro ⟨s1, a1⟩ ⟨-, -, σ', hm, ⟨⟨hS1, hSS, hK, -⟩, hSt1, -, hR1, -⟩, -⟩
  obtain ⟨hD', hcv, hsl, hMS⟩ := fin_after hDS hA hc hSS hSt1 hK
  refine (WP.spec_ok _).2 ⟨⟨rfl, trivial, trivial, σ', G, ?_, hD', hcv, hsl, hMS, hS1, hR1⟩, hSS⟩
  exact mem_bind_nd hm (Set.mem_singleton _)

set_option maxHeartbeats 1000000 in
/-- **A final PDPT cap**: `unmap_pdpt` if mapped (l4v `unmap_pdpt`); no cap
slot written. -/
theorem fin_pdpt (hH : VsPdptInnerHyps st A ar L4 SR) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (hDS : DState (L := L) th s σ G) (hA : AbsSlot th sl) (hPl : Placed th)
    (hPP : PtPlaced L4 L3 L2 L1) (hPS : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ SlotW th b)
    (hPV : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ VsWrite P (L.ksb s) b)
    (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b) (hVP : VsPlaced P (L.ksb s))
    (hPI : PoolsIn P L4 (L.mem s)) (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (hS : SR s a σ) (hVC : VsCapsIn P L4 L3 L2 L1 (L.mem s) G)
    (p asid va : U64) (mp : Bool) (hc : capAt (L.mem s) (cslotAddr sl) = ok (.Pdpt p mp asid va)) :
    objects.finalise_cap st ar s a (.Pdpt p mp asid va) true false ⦃ r =>
      FinOKX (L := L) th s σ G sl (.Pdpt p mp asid va) true (FinX st P SR) r ∧
        SlotsSame th (L.mem s) (L.mem r.2.1) ⦄ := by
  have hok := hVC.at hDS.1.2.2.1 hA.isSlot hc (by simp)
  simp only [VCapOK] at hok
  obtain ⟨hpL, -, hm⟩ := hok
  cases mp
  · simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok, Bool.false_eq_true, ↓reduceIte]
    exact (WP.spec_ok _).2 (fin_none (X := FinX st P SR) hDS hc ⟨hS, hR⟩ rfl (Set.mem_singleton _))
  have h0 := hm rfl
  simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok, ↓reduceIte]
  refine WP.spec_bind (unmap_pdpt_rel (hH.fin (s0 := s) (σ0 := σ) hPl hPO) s a σ hPl hPP hPS hVP
    (fun b ⟨q, hq, i, hi, e⟩ => hPV b ⟨q, Or.inl hq, i, hi, e⟩) hPI
    ⟨FinSR.init hS, hDS.1.1, hDS.1.2.1, hR, hPt⟩ asid va p h0 hpL) ?_
  rintro ⟨s1, a1⟩ ⟨-, -, σ', hm, ⟨⟨hS1, hSS, hK, -⟩, hSt1, -, hR1, -⟩, -⟩
  obtain ⟨hD', hcv, hsl, hMS⟩ := fin_after hDS hA hc hSS hSt1 hK
  refine (WP.spec_ok _).2 ⟨⟨rfl, trivial, trivial, σ', G, ?_, hD', hcv, hsl, hMS, hS1, hR1⟩, hSS⟩
  exact mem_bind_nd hm (Set.mem_singleton _)

set_option maxHeartbeats 1000000 in
/-- **A mapped frame cap** (final or not): `unmap_page` (l4v `unmap_page`); no
cap slot written. -/
theorem fin_frame (hH : VsUnmapPageHyps st A ar L3 L2 L1 SR) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (hDS : DState (L := L) th s σ G) (hA : AbsSlot th sl) (hPl : Placed th)
    (hPP : PtPlaced L4 L3 L2 L1) (hPS : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ SlotW th b)
    (hPV : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ VsWrite P (L.ksb s) b)
    (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b) (hVP : VsPlaced P (L.ksb s))
    (hPI : PoolsIn P L4 (L.mem s)) (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (hS : SR s a σ) (hVC : VsCapsIn P L4 L3 L2 L1 (L.mem s) G)
    (p : U64) (sz : capability.FrameSize) (rt : U64) (d : Bool) (asid va : U64) (b : Bool)
    (hc : capAt (L.mem s) (cslotAddr sl) = ok (.Frame p sz rt d true asid va)) :
    objects.finalise_cap st ar s a (.Frame p sz rt d true asid va) b false ⦃ r =>
      FinOKX (L := L) th s σ G sl (.Frame p sz rt d true asid va) b (FinX st P SR) r ∧
        SlotsSame th (L.mem s) (L.mem r.2.1) ⦄ := by
  have hok := hVC.at hDS.1.2.2.1 hA.isSlot hc (by simp)
  simp only [VCapOK] at hok
  have h0 : asid ≠ 0#u64 := by simpa using hok.1
  simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok, ↓reduceIte, bne_iff_ne, ne_eq, h0,
    not_false_eq_true]
  refine WP.spec_bind (unmap_page_rel (hH.fin (s0 := s) (σ0 := σ) hPl hPO) s a σ hPl hPP hPS hVP hPV hPI
    ⟨FinSR.init hS, hDS.1.1, hDS.1.2.1, hR, hPt⟩ sz asid va p h0) ?_
  rintro ⟨s1, a1⟩ ⟨-, -, σ', hm, ⟨⟨hS1, hSS, hK, -⟩, hSt1, -, hR1, -⟩, -⟩
  obtain ⟨hD', hcv, hsl, hMS⟩ := fin_after hDS hA hc hSS hSt1 hK
  refine (WP.spec_ok _).2 ⟨⟨rfl, trivial, trivial, σ', G, ?_, hD', hcv, hsl, hMS, hS1, hR1⟩, hSS⟩
  exact mem_bind_nd hm (Set.mem_singleton _)

set_option maxHeartbeats 1000000 in
/-- **A final PML4 cap**: `delete_asid` if mapped (l4v `delete_asid`); no
cap slot written. -/
theorem fin_pml4 (hH : VsHyps st A ar P th SR) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (hDS : DState (L := L) th s σ G) (hA : AbsSlot th sl) (hPl : Placed th)
    (hVO : ∀ b, VsWrite P (L.ksb s) b → OutsideObjects th b) (hSD : VsSlotsDisj th P (L.ksb s))
    (hVP : VsPlaced P (L.ksb s)) (hR : VsRel P (L.mem s) (L.ksb s) σ) (hCur : CurOK st th s σ)
    (hS : SR s a σ) (hVC : VsCapsIn P L4 L3 L2 L1 (L.mem s) G)
    (p asid : U64) (mp : Bool) (hc : capAt (L.mem s) (cslotAddr sl) = ok (.Pml4 p mp asid)) :
    objects.finalise_cap st ar s a (.Pml4 p mp asid) true false ⦃ r =>
      FinOKX (L := L) th s σ G sl (.Pml4 p mp asid) true (FinX st P SR) r ∧
        SlotsSame th (L.mem s) (L.mem r.2.1) ⦄ := by
  have hok := hVC.at (L1 := L1) hDS.1.2.2.1 hA.isSlot hc (by simp)
  simp only [VCapOK] at hok
  obtain ⟨-, hp0, -⟩ := hok
  cases mp
  · simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok, Bool.false_eq_true, ↓reduceIte]
    exact (WP.spec_ok _).2 (fin_none (X := FinX st P SR) hDS hc ⟨hS, hR⟩ rfl (Set.mem_singleton _))
  simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok, ↓reduceIte]
  refine WP.spec_bind (delete_asid_rel (hH.fin (s0 := s) (σ0 := σ) hPl hVO) s a σ hVP hR
    ⟨FinSR.init hS, hDS.1.1, hPl, hSD, hCur⟩ asid p hp0) ?_
  rintro ⟨s1, a1⟩ ⟨-, σ', hm, hR1, ⟨hS1, hSS, hK, -⟩, hSt1, -⟩
  obtain ⟨hD', hcv, hsl, hMS⟩ := fin_after hDS hA hc hSS hSt1 hK
  refine (WP.spec_ok _).2 ⟨⟨rfl, trivial, trivial, σ', G, ?_, hD', hcv, hsl, hMS, hS1, hR1⟩, hSS⟩
  exact mem_bind_nd hm (Set.mem_singleton _)

set_option maxHeartbeats 1000000 in
/-- **A final ASID pool cap**: `delete_asid_pool` (l4v `delete_asid_pool`);
no cap slot written. -/
theorem fin_asid_pool (hH : VsHyps st A ar P th SR) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (hDS : DState (L := L) th s σ G) (hA : AbsSlot th sl) (hPl : Placed th)
    (hVO : ∀ b, VsWrite P (L.ksb s) b → OutsideObjects th b) (hSD : VsSlotsDisj th P (L.ksb s))
    (hVP : VsPlaced P (L.ksb s)) (hR : VsRel P (L.mem s) (L.ksb s) σ) (hCur : CurOK st th s σ)
    (hS : SR s a σ) (hVC : VsCapsIn P L4 L3 L2 L1 (L.mem s) G) (hP0 : ∀ q ∈ P, q ≠ 0#u64)
    (p base : U64) (hc : capAt (L.mem s) (cslotAddr sl) = ok (.AsidPool p base)) :
    objects.finalise_cap st ar s a (.AsidPool p base) true false ⦃ r =>
      FinOKX (L := L) th s σ G sl (.AsidPool p base) true (FinX st P SR) r ∧
        SlotsSame th (L.mem s) (L.mem r.2.1) ⦄ := by
  have hok := hVC.at hDS.1.2.2.1 hA.isSlot hc (by simp)
  simp only [VCapOK] at hok
  obtain ⟨hpP, hb, -⟩ := hok
  simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok, ↓reduceIte]
  refine WP.spec_bind (delete_asid_pool_rel (hH.fin (s0 := s) (σ0 := σ) hPl hVO) s a σ hVP hR
    ⟨FinSR.init hS, hDS.1.1, hPl, hSD, hCur⟩ base p hb (hP0 p hpP)) ?_
  rintro ⟨s1, a1⟩ ⟨-, σ', hm, hR1, ⟨hS1, hSS, hK, -⟩, hSt1, -⟩
  obtain ⟨hD', hcv, hsl, hMS⟩ := fin_after hDS hA hc hSS hSt1 hK
  refine (WP.spec_ok _).2 ⟨⟨rfl, trivial, trivial, σ', G, ?_, hD', hcv, hsl, hMS, hS1, hR1⟩, hSS⟩
  exact mem_bind_nd hm (Set.mem_singleton _)

/-! ## All VSpace finalisations -/

/-- The VSpace caps whose finalisation may work. -/
def IsVsFin : capability.Cap → Prop
  | .Frame .. | .PageTable .. | .PageDirectory .. | .Pdpt .. | .Pml4 .. | .AsidPool .. => True
  | _ => False

/-- The hypotheses of the VSpace finalisations. -/
structure VsFinHyps (st : machine.Store S) [L : LawfulStore st] (A : Type) (ar : machine.Arch A) (th : TypedHeap)
    (P L4 L3 L2 L1 : Set U64) (SR : S → A → Fl4Spec.State Unit → Prop) : Prop where
  pt : VsPtInnerHyps st A ar L2 SR
  pd : VsPdInnerHyps st A ar L3 SR
  pdpt : VsPdptInnerHyps st A ar L4 SR
  pg : VsUnmapPageHyps st A ar L3 L2 L1 SR
  del : VsHyps st A ar P th SR

/-- **The VSpace half of `FinWorkHyp`**: a final table, PML4 or ASID pool
cap, or a mapped frame cap; no cap slot written (`SlotsSame`). -/
theorem vs_fin (hH : VsFinHyps st A ar th P L4 L3 L2 L1 SR) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (hDS : DState (L := L) th s σ G) (hA : AbsSlot th sl) (hPl : Placed th)
    (hPP : PtPlaced L4 L3 L2 L1) (hPS : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ SlotW th b)
    (hPV : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ VsWrite P (L.ksb s) b)
    (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b)
    (hVO : ∀ b, VsWrite P (L.ksb s) b → OutsideObjects th b) (hSD : VsSlotsDisj th P (L.ksb s))
    (hVP : VsPlaced P (L.ksb s)) (hPI : PoolsIn P L4 (L.mem s)) (hR : VsRel P (L.mem s) (L.ksb s) σ)
    (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ) (hCur : CurOK st th s σ) (hS : SR s a σ)
    (hVC : VsCapsIn P L4 L3 L2 L1 (L.mem s) G) (hP0 : ∀ q ∈ P, q ≠ 0#u64)
    (c : capability.Cap) (hc : capAt (L.mem s) (cslotAddr sl) = ok c) (hv : IsVsFin c) (b : Bool)
    (hw : FinWork c b) :
    objects.finalise_cap st ar s a c b false ⦃ r =>
      FinOKX (L := L) th s σ G sl c b (FinX st P SR) r ∧ SlotsSame th (L.mem s) (L.mem r.2.1) ⦄ := by
  have hb : isFrame c = false → b = true := by
    rintro hf; rcases hw with ⟨h, -⟩ | ⟨p, sz, r, d, asid, va, rfl⟩
    · exact h
    · simp [isFrame] at hf
  cases c <;> simp only [IsVsFin] at hv
  case Frame p sz rt d m asid va =>
    rcases hw with ⟨-, hf, -⟩ | ⟨p', sz', r', d', asid', va', e⟩
    · simp [isFrame] at hf
    · cases e
      exact fin_frame hH.pg s a σ G sl hDS hA hPl hPP hPS hPV hPO hVP hPI hR hPt hS hVC p sz rt d asid va b hc
  case PageTable p mp asid va =>
    rw [hb rfl]; exact fin_page_table hH.pt s a σ G sl hDS hA hPl hPP hPS hPV hPO hVP hPI hR hPt hS hVC p asid va mp hc
  case PageDirectory p mp asid va =>
    rw [hb rfl]
    exact fin_page_directory hH.pd s a σ G sl hDS hA hPl hPP hPS hPV hPO hVP hPI hR hPt hS hVC p asid va mp hc
  case Pdpt p mp asid va =>
    rw [hb rfl]; exact fin_pdpt hH.pdpt s a σ G sl hDS hA hPl hPP hPS hPV hPO hVP hPI hR hPt hS hVC p asid va mp hc
  case Pml4 p mp asid =>
    rw [hb rfl]; exact fin_pml4 hH.del s a σ G sl hDS hA hPl hVO hSD hVP hR hCur hS hVC p asid mp hc
  case AsidPool p base =>
    rw [hb rfl]; exact fin_asid_pool hH.del s a σ G sl hDS hA hPl hVO hSD hVP hR hCur hS hVC hP0 p base hc

end Ops


/-- `FinOKX` gives `FinObjHyp`'s post. -/
theorem FinOKX.base {A : Type} {th : TypedHeap} {s : S} {σ : Fl4Spec.State Unit} {G : MdbGhost}
    {sl : Fl4Spec.CslotPtr} {c : capability.Cap} {b : Bool} {X : S → A → Fl4Spec.State Unit → Prop}
    {r : (capability.Cap × capability.Cap) × S × A} (h : FinOKX (L := L) th s σ G sl c b X r) :
    r.1.1 = finRem c b ∧ CleanCap r.1.2 ∧ CapWf r.1.2 ∧
      ∃ σ' G', ((absCap r.1.1, absCap r.1.2), σ') ∈ (Fl4Spec.finaliseCap (Z := Unit) (absCap c) b σ).1 ∧
        DState (L := L) th r.2.1 σ' G' ∧ capV (L.mem r.2.1) (cslotAddr sl) = c ∧
        (∀ y, IsSlot th y → y ≠ cslotAddr sl → capV (L.mem r.2.1) y = capV (L.mem s) y ∨
          (capV (L.mem r.2.1) y = .Null ∧ isZb (capV (L.mem s) y) = false)) ∧
        MdbStep (L.mem s) G (L.mem r.2.1) G' := by
  obtain ⟨h1, h2, h3, σ', G', h4, h5, h6, h7, h8, -⟩ := h
  exact ⟨h1, h2, h3, σ', G', h4, h5, h6, h7, h8⟩

/-! ## At the composite relation -/

section Top
variable {th : TypedHeap} {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}
variable {A : Type} {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop}

/-- `VsHyps` for the composite relation. -/
theorem vsHyps_top (hA : ArchRefines arI AR) : VsHyps st A arI P th (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) where
  stable := fun s s' a σ σ' hS hw hc => vsStable_top s s' a σ σ' hS hw hc
  invalOK := fun asid vs σ => invalOK_top asid vs σ
  inval := fun s a σ asid vs _ hS => inval_top hA s a σ asid vs hS
  curT := fun s a σ hS => curT_top s a σ hS
  root := vsRootHyps_top hA

/-- `VsFinHyps` for the composite relation. -/
theorem vsFinHyps_top (hA : ArchRefines arI AR) :
    VsFinHyps st A arI th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) where
  pt := vsPtInnerHyps_top hA
  pd := vsPdInnerHyps_top hA
  pdpt := vsPdptInnerHyps_top hA
  pg := vsUnmapPageHyps_top hA
  del := vsHyps_top hA

/-- **The VSpace half of `FinWorkHyp` at `TopSR`**: the placement from
`TopPlaced`; `TopSR` and `VsRel` kept; no cap slot written. -/
theorem vs_fin_top (hA : ArchRefines arI AR) (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (sl : Fl4Spec.CslotPtr) (hDS : DState (L := L) th s σ G) (hAs : AbsSlot th sl)
    (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ) (hPI : PoolsIn P L4 (L.mem s))
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ) (hCur : CurOK st th s σ)
    (hVC : VsCapsIn P L4 L3 L2 L1 (L.mem s) G) (hP0 : ∀ q ∈ P, q ≠ 0#u64)
    (cp : capability.Cap) (hc : capAt (L.mem s) (cslotAddr sl) = ok cp) (hv : IsVsFin cp) (b : Bool)
    (hw : FinWork cp b) :
    objects.finalise_cap st arI s a cp b false ⦃ r =>
      FinOKX (L := L) th s σ G sl cp b (FinX st P (TopSR st th P L4 L3 L2 L1 N T C E R B c AR)) r ∧
        SlotsSame th (L.mem s) (L.mem r.2.1) ⦄ :=
  vs_fin (vsFinHyps_top hA) s a σ G sl hDS hAs hS.2.pl hS.2.pt hS.2.ps hS.2.pv hS.2.po hS.2.vo hS.2.sd hS.2.vs
    hPI hR hPt hCur hS hVC hP0 cp hc hv b hw

end Top

end

end

end Fl4Proofs.P3.Vs
