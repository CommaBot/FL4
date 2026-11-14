/-
P3 (DESIGN.md §9), VSpace: **the hypothesis structures of the VSpace
invocations for the composite relation** (`SR := TopSR`): every stability
and flush field from VsTop/VsArch (`capStable_top` … `flushTbl_top`, with
the arch interface `ArchRefines`); the `restart` fields (and ASID pool's
`curT`) stay arguments.
-/
import Fl4Proofs.P3.VsArch
import Fl4Proofs.P3.VsDecFrame
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3 Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- `VsMapHyps` for the composite relation. -/
theorem vsMapHyps_top {A : Type} {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} (hA : ArchRefines arI AR) :
    VsMapHyps st A arI L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) where
  stable := fun s s' a σ σ' hS hw hc => ptStable_top s s' a σ σ' hS hw hc
  flushOK := fun vs asid σ => flushOK_top vs asid σ
  noFlush := fun s a σ vs asid hS => noFlush_top s a σ vs asid hS
  flushPage := fun s a σ vs asid vaddr hS => flushPage_top hA s a σ vs asid vaddr hS
  flushAsid := fun s a σ vs asid hS => flushAsid_top hA s a σ vs asid hS

/-- `VsMapHypsAll` for the composite relation. -/
theorem vsMapHypsAll_top {A : Type} {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} (hA : ArchRefines arI AR) :
    VsMapHypsAll st A arI L1 L2 L3 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) where
  stable1 := fun s s' a σ σ' hS hw hc => ptStable_top s s' a σ σ' hS hw hc
  stable2 := fun s s' a σ σ' hS hw hc => pdStable_top s s' a σ σ' hS hw hc
  stable3 := fun s s' a σ σ' hS hw hc => pdptStable_top s s' a σ σ' hS hw hc
  flushOK := fun vs asid σ => flushOK_top vs asid σ
  noFlush := fun s a σ vs asid hS => noFlush_top s a σ vs asid hS
  flushPage := fun s a σ vs asid vaddr hS => flushPage_top hA s a σ vs asid vaddr hS
  flushAsid := fun s a σ vs asid hS => flushAsid_top hA s a σ vs asid hS

/-- `VsFrameHyps` for the composite relation (the restart field given). -/
theorem vsFrameHyps_top {A : Type} {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} (hA : ArchRefines arI AR)
    (hrestart : ∀ s a σ (ct : U64) (x : Fl4Spec.Tcb), StateRel th (L.mem s) σ → SlotsValid th (L.mem s) →
    VsRel P (L.mem s) (L.ksb s) σ → PtRel L4 L3 L2 L1 (L.mem s) σ → (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s a σ → ct.bv = σ.curThread →
    σ.kheap ct.bv = some (.tcb x) →
    sched.set_thread_state st s ct sched.TS_RESTART ⦃ s' =>
      StateRel th (L.mem s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      SlotsValid th (L.mem s') ∧
      VsRel P (L.mem s') (L.ksb s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      PtRel L4 L3 L2 L1 (L.mem s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s' a (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧ L.ksb s' = L.ksb s ⦄) :
    VsFrameHyps st A arI th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) where
  capStable := fun s s' a σ σ' hS hw hc => capStable_top s s' a σ σ' hS hw hc
  map := vsMapHyps_top hA
  restart := hrestart

/-- `VsFrameHypsL` for the composite relation (the restart field given). -/
theorem vsFrameHypsL_top {A : Type} {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} (hA : ArchRefines arI AR)
    (hrestart : ∀ s a σ (ct : U64) (x : Fl4Spec.Tcb), StateRel th (L.mem s) σ → SlotsValid th (L.mem s) →
    VsRel P (L.mem s) (L.ksb s) σ → PtRel L4 L3 L2 L1 (L.mem s) σ → (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s a σ → ct.bv = σ.curThread →
    σ.kheap ct.bv = some (.tcb x) →
    sched.set_thread_state st s ct sched.TS_RESTART ⦃ s' =>
      StateRel th (L.mem s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      SlotsValid th (L.mem s') ∧
      VsRel P (L.mem s') (L.ksb s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      PtRel L4 L3 L2 L1 (L.mem s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s' a (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧ L.ksb s' = L.ksb s ⦄) :
    VsFrameHypsL st A arI th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) where
  capStable := fun s s' a σ σ' hS hw hc => capStable_top s s' a σ σ' hS hw hc
  map := vsMapHypsAll_top hA
  restart := hrestart

/-- `VsUnmapPageHyps` for the composite relation. -/
theorem vsUnmapPageHyps_top {A : Type} {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} (hA : ArchRefines arI AR) :
    VsUnmapPageHyps st A arI L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) where
  ptStable := fun s s' a σ σ' hS hw hc => ptStable_top s s' a σ σ' hS hw hc
  pdStable := fun s s' a σ σ' hS hw hc => pdStable_top s s' a σ σ' hS hw hc
  pdptStable := fun s s' a σ σ' hS hw hc => pdptStable_top s s' a σ σ' hS hw hc
  flushPgOK := fun σ v asid => flushPgOK_top σ v asid
  flushPg := fun s a σ asid vaddr hS => flushPg_top hA s a σ asid vaddr hS

/-- `VsPtMapHyps` for the composite relation (the restart field given). -/
theorem vsPtMapHyps_top {A : Type} {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} (hA : ArchRefines arI AR)
    (hrestart : ∀ s a σ (ct : U64) (x : Fl4Spec.Tcb), StateRel th (L.mem s) σ → SlotsValid th (L.mem s) →
    VsRel P (L.mem s) (L.ksb s) σ → PtRel L4 L3 L2 L1 (L.mem s) σ → (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s a σ → ct.bv = σ.curThread →
    σ.kheap ct.bv = some (.tcb x) →
    sched.set_thread_state st s ct sched.TS_RESTART ⦃ s' =>
      StateRel th (L.mem s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      SlotsValid th (L.mem s') ∧
      VsRel P (L.mem s') (L.ksb s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      PtRel L4 L3 L2 L1 (L.mem s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s' a (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧ L.ksb s' = L.ksb s ⦄) :
    VsPtMapHyps st A arI th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) where
  capStable := fun s s' a σ σ' hS hw hc => capStable_top s s' a σ σ' hS hw hc
  pdStable := fun s s' a σ σ' hS hw hc => pdStable_top s s' a σ σ' hS hw hc
  flushOK := fun vs asid σ => flushOK_top vs asid σ
  flushPS := fun s a σ vs asid hS => flushPS_top hA s a σ vs asid hS
  restart := hrestart

/-- `VsPdMapHyps` for the composite relation (the restart field given). -/
theorem vsPdMapHyps_top {A : Type} {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} (hA : ArchRefines arI AR)
    (hrestart : ∀ s a σ (ct : U64) (x : Fl4Spec.Tcb), StateRel th (L.mem s) σ → SlotsValid th (L.mem s) →
    VsRel P (L.mem s) (L.ksb s) σ → PtRel L4 L3 L2 L1 (L.mem s) σ → (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s a σ → ct.bv = σ.curThread →
    σ.kheap ct.bv = some (.tcb x) →
    sched.set_thread_state st s ct sched.TS_RESTART ⦃ s' =>
      StateRel th (L.mem s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      SlotsValid th (L.mem s') ∧
      VsRel P (L.mem s') (L.ksb s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      PtRel L4 L3 L2 L1 (L.mem s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s' a (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧ L.ksb s' = L.ksb s ⦄) :
    VsPdMapHyps st A arI th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) where
  capStable := fun s s' a σ σ' hS hw hc => capStable_top s s' a σ σ' hS hw hc
  pdptStable := fun s s' a σ σ' hS hw hc => pdptStable_top s s' a σ σ' hS hw hc
  flushOK := fun vs asid σ => flushOK_top vs asid σ
  flushPS := fun s a σ vs asid hS => flushPS_top hA s a σ vs asid hS
  restart := hrestart

/-- `VsPdptMapHyps` for the composite relation (the restart field given). -/
theorem vsPdptMapHyps_top {A : Type} {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} (hA : ArchRefines arI AR)
    (hrestart : ∀ s a σ (ct : U64) (x : Fl4Spec.Tcb), StateRel th (L.mem s) σ → SlotsValid th (L.mem s) →
    VsRel P (L.mem s) (L.ksb s) σ → PtRel L4 L3 L2 L1 (L.mem s) σ → (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s a σ → ct.bv = σ.curThread →
    σ.kheap ct.bv = some (.tcb x) →
    sched.set_thread_state st s ct sched.TS_RESTART ⦃ s' =>
      StateRel th (L.mem s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      SlotsValid th (L.mem s') ∧
      VsRel P (L.mem s') (L.ksb s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      PtRel L4 L3 L2 L1 (L.mem s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s' a (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧ L.ksb s' = L.ksb s ⦄) :
    VsPdptMapHyps st A arI th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) where
  capStable := fun s s' a σ σ' hS hw hc => capStable_top s s' a σ σ' hS hw hc
  pml4Stable := fun s s' a σ σ' hS hw hc => pml4Stable_top s s' a σ σ' hS hw hc
  flushOK := fun vs asid σ => flushOK_top vs asid σ
  flushPS := fun s a σ vs asid hS => flushPS_top hA s a σ vs asid hS
  restart := hrestart

/-- `VsPtInnerHyps` for the composite relation. -/
theorem vsPtInnerHyps_top {A : Type} {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} (hA : ArchRefines arI AR) :
    VsPtInnerHyps st A arI L2 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) where
  pdStable := fun s s' a σ σ' hS hw hc => pdStable_top s s' a σ σ' hS hw hc
  flushOK := fun vs asid σ => flushOK_top vs asid σ
  flushPS := fun s a σ vs asid hS => flushPS_top hA s a σ vs asid hS
  flushTblOK := fun σ vs v pt asid hal hk => flushTblOK_top σ vs v pt asid hal hk
  flushTbl := fun s a σ vs v pt asid hS hal hk => flushTbl_top hA s a σ vs v pt asid hS hal hk

/-- `VsPdInnerHyps` for the composite relation. -/
theorem vsPdInnerHyps_top {A : Type} {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} (hA : ArchRefines arI AR) :
    VsPdInnerHyps st A arI L3 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) where
  pdptStable := fun s s' a σ σ' hS hw hc => pdptStable_top s s' a σ σ' hS hw hc
  flushOK := fun vs asid σ => flushOK_top vs asid σ
  flushPS := fun s a σ vs asid hS => flushPS_top hA s a σ vs asid hS
  flushAllOK := fun σ vs asid => flushAllOK_top σ vs asid
  flushAllH := fun s a σ vs asid hS => flushAllH_top hA s a σ vs asid hS

/-- `VsPdptInnerHyps` for the composite relation. -/
theorem vsPdptInnerHyps_top {A : Type} {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} (hA : ArchRefines arI AR) :
    VsPdptInnerHyps st A arI L4 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) where
  pml4Stable := fun s s' a σ σ' hS hw hc => pml4Stable_top s s' a σ σ' hS hw hc
  flushAllOK := fun σ vs asid => flushAllOK_top σ vs asid
  flushAllH := fun s a σ vs asid hS => flushAllH_top hA s a σ vs asid hS

/-- `VsFrameUnmapHyps` for the composite relation (the restart field given). -/
theorem vsFrameUnmapHyps_top {A : Type} {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} (hA : ArchRefines arI AR)
    (hrestart : ∀ s a σ (ct : U64) (x : Fl4Spec.Tcb), StateRel th (L.mem s) σ → SlotsValid th (L.mem s) →
    VsRel P (L.mem s) (L.ksb s) σ → PtRel L4 L3 L2 L1 (L.mem s) σ → (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s a σ → ct.bv = σ.curThread →
    σ.kheap ct.bv = some (.tcb x) →
    sched.set_thread_state st s ct sched.TS_RESTART ⦃ s' =>
      StateRel th (L.mem s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      SlotsValid th (L.mem s') ∧
      VsRel P (L.mem s') (L.ksb s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      PtRel L4 L3 L2 L1 (L.mem s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s' a (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧ L.ksb s' = L.ksb s ∧
      PoolsIn P L4 (L.mem s') ⦄) :
    VsFrameUnmapHyps st A arI th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) where
  toVsUnmapPageHyps := vsUnmapPageHyps_top hA
  capStable := fun s s' a σ σ' hS hw hc => capStable_top s s' a σ σ' hS hw hc
  restart := hrestart

/-- `VsPtUnmapHyps` for the composite relation (the restart field given). -/
theorem vsPtUnmapHyps_top {A : Type} {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} (hA : ArchRefines arI AR)
    (hrestart : ∀ s a σ (ct : U64) (x : Fl4Spec.Tcb), StateRel th (L.mem s) σ → SlotsValid th (L.mem s) →
    VsRel P (L.mem s) (L.ksb s) σ → PtRel L4 L3 L2 L1 (L.mem s) σ → (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s a σ → ct.bv = σ.curThread →
    σ.kheap ct.bv = some (.tcb x) →
    sched.set_thread_state st s ct sched.TS_RESTART ⦃ s' =>
      StateRel th (L.mem s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      SlotsValid th (L.mem s') ∧
      VsRel P (L.mem s') (L.ksb s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      PtRel L4 L3 L2 L1 (L.mem s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s' a (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧ L.ksb s' = L.ksb s ∧
      PoolsIn P L4 (L.mem s') ⦄) :
    VsPtUnmapHyps st A arI th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) where
  toVsPtInnerHyps := vsPtInnerHyps_top hA
  capStable := fun s s' a σ σ' hS hw hc => capStable_top s s' a σ σ' hS hw hc
  ptStable := fun s s' a σ σ' hS hw hc => ptStable_top s s' a σ σ' hS hw hc
  restart := hrestart

/-- `VsPdUnmapHyps` for the composite relation (the restart field given). -/
theorem vsPdUnmapHyps_top {A : Type} {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} (hA : ArchRefines arI AR)
    (hrestart : ∀ s a σ (ct : U64) (x : Fl4Spec.Tcb), StateRel th (L.mem s) σ → SlotsValid th (L.mem s) →
    VsRel P (L.mem s) (L.ksb s) σ → PtRel L4 L3 L2 L1 (L.mem s) σ → (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s a σ → ct.bv = σ.curThread →
    σ.kheap ct.bv = some (.tcb x) →
    sched.set_thread_state st s ct sched.TS_RESTART ⦃ s' =>
      StateRel th (L.mem s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      SlotsValid th (L.mem s') ∧
      VsRel P (L.mem s') (L.ksb s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      PtRel L4 L3 L2 L1 (L.mem s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s' a (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧ L.ksb s' = L.ksb s ∧
      PoolsIn P L4 (L.mem s') ⦄) :
    VsPdUnmapHyps st A arI th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) where
  toVsPdInnerHyps := vsPdInnerHyps_top hA
  capStable := fun s s' a σ σ' hS hw hc => capStable_top s s' a σ σ' hS hw hc
  pdStable := fun s s' a σ σ' hS hw hc => pdStable_top s s' a σ σ' hS hw hc
  restart := hrestart

/-- `VsPdptUnmapHyps` for the composite relation (the restart field given). -/
theorem vsPdptUnmapHyps_top {A : Type} {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} (hA : ArchRefines arI AR)
    (hrestart : ∀ s a σ (ct : U64) (x : Fl4Spec.Tcb), StateRel th (L.mem s) σ → SlotsValid th (L.mem s) →
    VsRel P (L.mem s) (L.ksb s) σ → PtRel L4 L3 L2 L1 (L.mem s) σ → (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s a σ → ct.bv = σ.curThread →
    σ.kheap ct.bv = some (.tcb x) →
    sched.set_thread_state st s ct sched.TS_RESTART ⦃ s' =>
      StateRel th (L.mem s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      SlotsValid th (L.mem s') ∧
      VsRel P (L.mem s') (L.ksb s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      PtRel L4 L3 L2 L1 (L.mem s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s' a (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧ L.ksb s' = L.ksb s ∧
      PoolsIn P L4 (L.mem s') ⦄) :
    VsPdptUnmapHyps st A arI th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) where
  toVsPdptInnerHyps := vsPdptInnerHyps_top hA
  capStable := fun s s' a σ σ' hS hw hc => capStable_top s s' a σ σ' hS hw hc
  pdptStable := fun s s' a σ σ' hS hw hc => pdptStable_top s s' a σ σ' hS hw hc
  restart := hrestart

variable {A : Type} (arI : machine.Arch A)

set_option maxHeartbeats 8000000 in
/-- **A frame cap with the composite relation** (`decode_invocation_frame`; the placement from `TopPlaced`). -/
theorem decode_invocation_frame_top (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {AR : A → Fl4Spec.Cr3 → Prop}
    (hA : ArchRefines arI AR) (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s ar σ)
    (hr1 : ∀ s a σ (ct : U64) (x : Fl4Spec.Tcb), StateRel th (L.mem s) σ → SlotsValid th (L.mem s) →
    VsRel P (L.mem s) (L.ksb s) σ → PtRel L4 L3 L2 L1 (L.mem s) σ → (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s a σ → ct.bv = σ.curThread →
    σ.kheap ct.bv = some (.tcb x) →
    sched.set_thread_state st s ct sched.TS_RESTART ⦃ s' =>
      StateRel th (L.mem s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      SlotsValid th (L.mem s') ∧
      VsRel P (L.mem s') (L.ksb s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      PtRel L4 L3 L2 L1 (L.mem s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s' a (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧ L.ksb s' = L.ksb s ⦄)
    (hrL : ∀ s a σ (ct : U64) (x : Fl4Spec.Tcb), StateRel th (L.mem s) σ → SlotsValid th (L.mem s) →
    VsRel P (L.mem s) (L.ksb s) σ → PtRel L4 L3 L2 L1 (L.mem s) σ → (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s a σ → ct.bv = σ.curThread →
    σ.kheap ct.bv = some (.tcb x) →
    sched.set_thread_state st s ct sched.TS_RESTART ⦃ s' =>
      StateRel th (L.mem s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      SlotsValid th (L.mem s') ∧
      VsRel P (L.mem s') (L.ksb s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      PtRel L4 L3 L2 L1 (L.mem s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s' a (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧ L.ksb s' = L.ksb s ⦄)
    (hrU : ∀ s a σ (ct : U64) (x : Fl4Spec.Tcb), StateRel th (L.mem s) σ → SlotsValid th (L.mem s) →
    VsRel P (L.mem s) (L.ksb s) σ → PtRel L4 L3 L2 L1 (L.mem s) σ → (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s a σ → ct.bv = σ.curThread →
    σ.kheap ct.bv = some (.tcb x) →
    sched.set_thread_state st s ct sched.TS_RESTART ⦃ s' =>
      StateRel th (L.mem s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      SlotsValid th (L.mem s') ∧
      VsRel P (L.mem s') (L.ksb s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      PtRel L4 L3 L2 L1 (L.mem s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s' a (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧ L.ksb s' = L.ksb s ∧
      PoolsIn P L4 (L.mem s') ⦄)
    (hD : VsSlotsDisj th P (L.ksb s))
    (hPS : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ SlotW th b) (hPV : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ VsWrite P (L.ksb s) b)
    (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b) (hPI : PoolsIn P L4 (L.mem s))
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : FrameLabel lbl slbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {p : U64} {sz : capability.FrameSize} {rt asid va : U64} {d m : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.Frame p sz rt d m asid va))
    (hfm : m = true → asid ≠ 0#u64)
    (hpaS : sz = .Small → (core.num.U64.wrapping_sub p layout.PPTR_BASE &&& 4503599627366400#u64) =
      core.num.U64.wrapping_sub p layout.PPTR_BASE)
    (hpaL : sz = .Large → (core.num.U64.wrapping_sub p layout.PPTR_BASE &&& 4503599625273344#u64) =
      core.num.U64.wrapping_sub p layout.PPTR_BASE)
    (hpaH : sz = .Huge → (core.num.U64.wrapping_sub p layout.PPTR_BASE &&& 4503598553628672#u64) =
      core.num.U64.wrapping_sub p layout.PPTR_BASE)
    (hAl : ErrRel (.Sys .AlignmentError) .alignmentError)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hext : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ x vc vc' xsl rest, vspace.extra extra 0#usize = ok (some x) ∧ capAt (L.mem s) x = ok vc ∧
        CapRel vc vc' ∧ excaps = (vc', xsl) :: rest ∧
        ∀ p' asid', vc = .Pml4 p' true asid' → p' ∈ L4 ∧ asid' ≠ 0#u64 ∧ asid'.val < 2 ^ 20)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef)
    (hGA : lbl = fl4_abi.label.X86PageGetAddress →
      DecOK (L := L) arI s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Frame p sz rt d m asid va) blk call don fp
        buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer)
    (hTAC : lbl = fl4_abi.label.X86PageTestAndClearAccessed →
      DecOK (L := L) arI s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Frame p sz rt d m asid va) blk call don fp
        buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer)
    (hDS : lbl = fl4_abi.label.X86PageDeriveSubframe →
      DecOK (L := L) arI s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Frame p sz rt d m asid va) blk call don fp
        buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer) :
    DecOK (L := L) arI s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Frame p sz rt d m asid va) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer := decode_invocation_frame arI th hS.2.pl s ar σ G hCR hFI (vsFrameHyps_top hA hr1) (vsFrameHypsL_top hA hrL)
    (vsFrameUnmapHyps_top hA hrU) hS hS.2.vs hD hS.2.pt hPS hPV hPO hPI hR hPt lbl slbl hlbl length buf ct hct hcur htcb
    hact args hlen hargs hpc hidx hcap hfm hpaS hpaL hpaH hAl extra excaps hext blk call don fp ci buffer hGA hTAC hDS

end

end

end Fl4Proofs.P3.Vs
