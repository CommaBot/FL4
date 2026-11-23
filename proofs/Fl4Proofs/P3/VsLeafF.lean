/-
P3 (issue #16, F1 stage 5; KENTRY-PLAN f4b): **what the frame-class VSpace
steps leave for `VsNamed`**, as facts the refinements export at their success
endpoints (as `PdptMapF` …, KENTRY-PLAN f4 (0)).

* `VWalk3` / `VWalk2` / `VWalk1`: FL4's walk words from a PML4 down to a PDPT /
  PD / PT (l4v `vs_lookup` below a PML4, VsNamed's `VsPath` constructors).
* **`MapLeafF`** (frame map, any size): the frame caps, the PML4 l4v's ASID lookup
  finds, the table written reached from it (`VWalk*`), its written entry no walk
  step before and after (a PT entry; a large / huge page entry or invalid), every
  other spec arch object and the ASID table kept.
* **`ArchShr`** / **`UnmapLeafF`** (frame unmap): every spec arch object kept or
  only entries cleared (`EntShr`), the ASID table kept.
-/
import Fl4Proofs.P3.VsAssignRel
import Fl4Proofs.P3.VsPt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3

noncomputable section

/-- A frame cap. -/
def IsFrameC : capability.Cap → Prop
  | .Frame .. => True
  | _ => False

/-- FL4's walk words from the PML4 `pm` to the PDPT `q`. -/
def VWalk3 (m : U64 → U64) (pm q : U64) : Prop :=
  ∃ i : U64, i.val < 256 ∧ eP (m (peA pm i)) ∧ eT (m (peA pm i)) = q

/-- FL4's walk words from the PML4 `pm` to the PD `q`. -/
def VWalk2 (m : U64 → U64) (pm q : U64) : Prop :=
  ∃ p i : U64, VWalk3 m pm p ∧ i.val < 512 ∧ eP (m (peA p i)) ∧ ¬ eS (m (peA p i)) ∧ eT (m (peA p i)) = q

/-- FL4's walk words from the PML4 `pm` to the PT `q`. -/
def VWalk1 (m : U64 → U64) (pm q : U64) : Prop :=
  ∃ p i : U64, VWalk2 m pm p ∧ i.val < 512 ∧ eP (m (peA p i)) ∧ ¬ eS (m (peA p i)) ∧ eT (m (peA p i)) = q

/-- A PD entry with no walk step (invalid or a large page). -/
def NoStep2 (d : Fl4Spec.PDE) : Prop := d = .invalidPDE ∨ ∃ a b c, d = .largePagePDE a b c

/-- A PDPT entry with no walk step (invalid or a huge page). -/
def NoStep3 (d : Fl4Spec.PDPTE) : Prop := d = .invalidPDPTE ∨ ∃ a b c, d = .hugePagePDPTE a b c

/-- **(F1 stage 5) What a frame map leaves for `VsNamed`** (VsNamedPost's
`ofMapLeafF`, VsNamedStep's `leafS`): the cap before and after a frame cap,
the PML4 `pm` l4v's ASID lookup finds, the table `q` written reached from it:
a PT, or a PD / PDPT whose entry `j` has no walk step before and after; every
other spec arch object and the ASID table kept. -/
def MapLeafF (m m' : U64 → U64) (x : U64) (c : capability.Cap) (σ σ' : Fl4Spec.State Unit) : Prop :=
  IsFrameC c ∧ IsFrameC (capV m' x) ∧ σ'.archState.x64AsidTable = σ.archState.x64AsidTable ∧
  ∃ asid pm q : U64, asid ≠ 0#u64 ∧ asid.val < 2 ^ 20 ∧
    ExceptT.run (Fl4Spec.findVspaceForAsid (Z := Unit) asid.bv) σ = ({(.ok pm.bv, σ)}, False) ∧
    ArchKeepBut q σ σ' ∧
    (VWalk1 m pm q ∨
     (VWalk2 m pm q ∧ ∃ (f : BitVec 9 → Fl4Spec.PDE) (j : U64) (d : Fl4Spec.PDE), j.val < 512 ∧
        σ.kheap q.bv = some (.archObj (.pageDirectory f)) ∧ NoStep2 (f (Fl4Spec.ucast 9 j.bv)) ∧ NoStep2 d ∧
        σ'.kheap q.bv = some (.archObj (.pageDirectory (Function.update f (Fl4Spec.ucast 9 j.bv) d)))) ∨
     (VWalk3 m pm q ∧ ∃ (f : BitVec 9 → Fl4Spec.PDPTE) (j : U64) (d : Fl4Spec.PDPTE), j.val < 512 ∧
        σ.kheap q.bv = some (.archObj (.pdPointerTable f)) ∧ NoStep3 (f (Fl4Spec.ucast 9 j.bv)) ∧ NoStep3 d ∧
        σ'.kheap q.bv = some (.archObj (.pdPointerTable (Function.update f (Fl4Spec.ucast 9 j.bv) d)))))

/-- A spec arch object kept, or a table with some entries cleared. -/
def EntShr (ao ao' : Fl4Spec.ArchKernelObj) : Prop :=
  ao' = ao ∨
  (∃ f g, ao = .pageTable f ∧ ao' = .pageTable g ∧ ∀ i, g i = f i ∨ g i = .invalidPTE) ∨
  (∃ f g, ao = .pageDirectory f ∧ ao' = .pageDirectory g ∧ ∀ i, g i = f i ∨ g i = .invalidPDE) ∨
  (∃ f g, ao = .pdPointerTable f ∧ ao' = .pdPointerTable g ∧ ∀ i, g i = f i ∨ g i = .invalidPDPTE) ∨
  (∃ f g, ao = .pageMapL4 f ∧ ao' = .pageMapL4 g ∧ ∀ i, g i = f i ∨ g i = .invalidPML4E)

/-- **(F1 stage 5) Only entries cleared**: every spec arch object stays one,
kept or with entries cleared; the ASID table kept. -/
def ArchShr (σ σ' : Fl4Spec.State Unit) : Prop :=
  σ'.archState.x64AsidTable = σ.archState.x64AsidTable ∧
  ∀ p ao, σ.kheap p = some (.archObj ao) → ∃ ao', σ'.kheap p = some (.archObj ao') ∧ EntShr ao ao'

/-- **(F1 stage 5) What a frame unmap leaves for `VsNamed`** (VsNamedPost's
`ofUnmapLeafF`, VsNamedOps' `shrink`): the cap before and after a frame cap,
only entries cleared. -/
def UnmapLeafF (m' : U64 → U64) (x : U64) (c : capability.Cap) (σ σ' : Fl4Spec.State Unit) : Prop :=
  IsFrameC c ∧ IsFrameC (capV m' x) ∧ ArchShr σ σ'

theorem ArchShr.of_keep {σ σ' : Fl4Spec.State Unit}
    (h1 : σ'.archState.x64AsidTable = σ.archState.x64AsidTable)
    (hk : ∀ p ao, σ.kheap p = some (.archObj ao) → σ'.kheap p = σ.kheap p) : ArchShr σ σ' :=
  ⟨h1, fun p ao hp => ⟨ao, (hk p ao hp).trans hp, .inl rfl⟩⟩

theorem ArchShr.refl (σ : Fl4Spec.State Unit) : ArchShr σ σ := ArchShr.of_keep rfl (fun _ _ _ => rfl)

theorem ArchShr.keep_left {σ σ1 σ2 : Fl4Spec.State Unit}
    (h1 : σ1.archState.x64AsidTable = σ.archState.x64AsidTable)
    (hk : ∀ p ao, σ.kheap p = some (.archObj ao) → σ1.kheap p = σ.kheap p) (h : ArchShr σ1 σ2) :
    ArchShr σ σ2 :=
  ⟨h.1.trans h1, fun p ao hp => h.2 p ao ((hk p ao hp).trans hp)⟩

theorem ArchShr.keep_right {σ σ1 σ2 : Fl4Spec.State Unit} (h : ArchShr σ σ1)
    (h1 : σ2.archState.x64AsidTable = σ1.archState.x64AsidTable)
    (hk : ∀ p ao, σ1.kheap p = some (.archObj ao) → σ2.kheap p = σ1.kheap p) : ArchShr σ σ2 :=
  ⟨h1.trans h.1, fun p ao hp =>
    let ⟨ao', h', he⟩ := h.2 p ao hp
    ⟨ao', (hk p ao' h').trans h', he⟩⟩

/-- The machine state written (a flush): no arch object touched. -/
theorem ArchShr.ms {σ σ1 : Fl4Spec.State Unit} (h : ArchShr σ σ1) (ms : Fl4Spec.MachineState) :
    ArchShr σ { σ1 with machineState := ms } := ⟨h.1, h.2⟩

/-- The current thread's state written (`set_thread_state`): no arch object
touched. -/
theorem sts_keep {σ : Fl4Spec.State Unit} {ct : Fl4Spec.ObjRef} {x : Fl4Spec.Tcb}
    (hk : σ.kheap ct = some (.tcb x)) (t : Fl4Spec.Tcb) :
    (stsAct (updK σ ct (.tcb t)) ct).archState.x64AsidTable = σ.archState.x64AsidTable ∧
    ∀ p ao, σ.kheap p = some (.archObj ao) → (stsAct (updK σ ct (.tcb t)) ct).kheap p = σ.kheap p := by
  refine ⟨by unfold stsAct; split <;> rfl, fun p ao hp => ?_⟩
  have hne : p ≠ ct := kheap_ne hp hk (fun _ h1 h2 => by subst h1; cases h2)
  rw [stsAct_kheap]; simp [updK, hne]

/-- A CNode slot written: no arch object touched. -/
theorem cnode_keep {σ : Fl4Spec.State Unit} {pc : Fl4Spec.ObjRef} {r : Nat} {cs : Fl4Spec.CnodeContents}
    (hk : σ.kheap pc = some (.cnode r cs)) (idx : List Bool) (c : Fl4Spec.Cap) :
    (setCnodeSlot σ pc r cs idx c).archState.x64AsidTable = σ.archState.x64AsidTable ∧
    ∀ p ao, σ.kheap p = some (.archObj ao) → (setCnodeSlot σ pc r cs idx c).kheap p = σ.kheap p := by
  refine ⟨rfl, fun p ao hp => ?_⟩
  have hne : p ≠ pc := kheap_ne hp hk (fun _ h1 h2 => by subst h1; cases h2)
  simp [setCnodeSlot, hne]

/-- One PT entry cleared. -/
theorem ArchShr.upd_pt {σ : Fl4Spec.State Unit} {q : Fl4Spec.ObjRef} {f : BitVec 9 → Fl4Spec.PTE}
    (hk : σ.kheap q = some (.archObj (.pageTable f))) (j : BitVec 9) :
    ArchShr σ (updK σ q (.archObj (.pageTable (Function.update f j .invalidPTE)))) := by
  refine ⟨rfl, fun p ao hp => ?_⟩
  by_cases e : p = q
  · subst e
    rw [hk] at hp; cases hp
    refine ⟨.pageTable (Function.update f j .invalidPTE), by simp [updK], .inr (.inl ⟨f, _, rfl, rfl, fun i => ?_⟩)⟩
    rw [Function.update_apply]; split_ifs <;> simp
  · exact ⟨ao, by simp [updK, e, hp], .inl rfl⟩

/-- One PD entry cleared. -/
theorem ArchShr.upd_pd {σ : Fl4Spec.State Unit} {q : Fl4Spec.ObjRef} {f : BitVec 9 → Fl4Spec.PDE}
    (hk : σ.kheap q = some (.archObj (.pageDirectory f))) (j : BitVec 9) :
    ArchShr σ (updK σ q (.archObj (.pageDirectory (Function.update f j .invalidPDE)))) := by
  refine ⟨rfl, fun p ao hp => ?_⟩
  by_cases e : p = q
  · subst e
    rw [hk] at hp; cases hp
    refine ⟨.pageDirectory (Function.update f j .invalidPDE), by simp [updK], .inr (.inr (.inl ⟨f, _, rfl, rfl, fun i => ?_⟩))⟩
    rw [Function.update_apply]; split_ifs <;> simp
  · exact ⟨ao, by simp [updK, e, hp], .inl rfl⟩

/-- One PDPT entry cleared. -/
theorem ArchShr.upd_pdpt {σ : Fl4Spec.State Unit} {q : Fl4Spec.ObjRef} {f : BitVec 9 → Fl4Spec.PDPTE}
    (hk : σ.kheap q = some (.archObj (.pdPointerTable f))) (j : BitVec 9) :
    ArchShr σ (updK σ q (.archObj (.pdPointerTable (Function.update f j .invalidPDPTE)))) := by
  refine ⟨rfl, fun p ao hp => ?_⟩
  by_cases e : p = q
  · subst e
    rw [hk] at hp; cases hp
    refine ⟨.pdPointerTable (Function.update f j .invalidPDPTE), by simp [updK], .inr (.inr (.inr (.inl ⟨f, _, rfl, rfl, fun i => ?_⟩)))⟩
    rw [Function.update_apply]; split_ifs <;> simp
  · exact ⟨ao, by simp [updK, e, hp], .inl rfl⟩

/-- One PML4 entry cleared. -/
theorem ArchShr.upd_pml4 {σ : Fl4Spec.State Unit} {q : Fl4Spec.ObjRef} {f : BitVec 9 → Fl4Spec.PML4E}
    (hk : σ.kheap q = some (.archObj (.pageMapL4 f))) (j : BitVec 9) :
    ArchShr σ (updK σ q (.archObj (.pageMapL4 (Function.update f j .invalidPML4E)))) := by
  refine ⟨rfl, fun p ao hp => ?_⟩
  by_cases e : p = q
  · subst e
    rw [hk] at hp; cases hp
    refine ⟨.pageMapL4 (Function.update f j .invalidPML4E), by simp [updK], .inr (.inr (.inr (.inr ⟨f, _, rfl, rfl, fun i => ?_⟩)))⟩
    rw [Function.update_apply]; split_ifs <;> simp
  · exact ⟨ao, by simp [updK, e, hp], .inl rfl⟩

end

end Fl4Proofs.P3.Vs
