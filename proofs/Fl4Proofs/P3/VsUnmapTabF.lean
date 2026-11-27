/-
P3 (issue #16, F1 stage 5; KENTRY-PLAN f4c): **what a table Unmap (PT / PD /
PDPT) leaves for `VsNamed`**, as a fact the refinements export at their
success endpoints (as `PdptMapF` …, KENTRY-PLAN f4 (0)).

* `SW4`, `SE4`, `SE3`: l4v's ASID lookup data (the ASID table entry, the
  pool's native root) and the PML4 / PDPT entries on a vaddr's indices, as spec
  objects (no lookup monad: the `J` layer builds them from a `VsPath`, the
  refinements read them against FL4's lookups through `PtRel`).
* `NoName4` / `NoName3` / `NoName2`: after the step, the parent entry at the
  cap's ref (asid, vaddr) does not name the unmapped table.
* **`UnmapTabF`**: the cap before a PT / PD / PDPT cap, after the same cap
  unmapped, `ArchShr` (only entries cleared), the `NoName*` of a mapped cap,
  and a mapped cap's table words not present after (FL4 zeroes the table).
* `lookup_pdpt_slot_nwalk`, `lookup_pd_slot_nwalk`: FL4's lookups fail only
  when the walk words are missing (mirror of VsFrameMapRel's `*_walk`).
-/
import Fl4Proofs.P3.VsFrameMapRel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3

noncomputable section

/-! ## The fact -/

/-- l4v's ASID lookup data for `asid`: the ASID table entry names a pool whose
entry is the native root `pm`. -/
def SW4 (σ : Fl4Spec.State Unit) (asid pm : U64) : Prop :=
  ∃ pool f, σ.archState.x64AsidTable (Fl4Spec.asidHighBitsOf asid.bv) = some pool ∧
    σ.kheap pool = some (.archObj (.asidPool f)) ∧
    Fl4Spec.nativeAsidRoot (f (Fl4Spec.asidLowBitsOf asid.bv)) = some pm.bv

/-- The PML4 `pm`'s entry on `va` names the PDPT `p3`. -/
def SE4 (σ : Fl4Spec.State Unit) (pm va p3 : U64) : Prop :=
  ∃ f ta tr, σ.kheap pm.bv = some (.archObj (.pageMapL4 f)) ∧
    f (Fl4Spec.ucast 9 (vIdx va 39).bv) = .pdPointerTablePML4E (Fl4Spec.addrFromPPtr p3.bv) ta tr

/-- The PDPT `p3`'s entry on `va` names the PD `p2`. -/
def SE3 (σ : Fl4Spec.State Unit) (p3 va p2 : U64) : Prop :=
  ∃ g ta tr, σ.kheap p3.bv = some (.archObj (.pdPointerTable g)) ∧
    g (Fl4Spec.ucast 9 (vIdx va 30).bv) = .pageDirectoryPDPTE (Fl4Spec.addrFromPPtr p2.bv) ta tr

/-- After a PDPT unmap: the PML4 of `asid` (before) does not name `q0` at
`va` (after). -/
def NoName4 (σ σ' : Fl4Spec.State Unit) (asid va q0 : U64) : Prop :=
  ∀ pm, SW4 σ asid pm → ∀ h, σ'.kheap pm.bv = some (.archObj (.pageMapL4 h)) → ∀ ta tr,
    h (Fl4Spec.ucast 9 (vIdx va 39).bv) ≠ .pdPointerTablePML4E (Fl4Spec.addrFromPPtr q0.bv) ta tr

/-- After a PD unmap: the PDPT at (`asid`, `va`) (before) does not name `q0`
(after). -/
def NoName3 (σ σ' : Fl4Spec.State Unit) (asid va q0 : U64) : Prop :=
  ∀ pm p3, SW4 σ asid pm → SE4 σ pm va p3 → ∀ h, σ'.kheap p3.bv = some (.archObj (.pdPointerTable h)) →
    ∀ ta tr, h (Fl4Spec.ucast 9 (vIdx va 30).bv) ≠ .pageDirectoryPDPTE (Fl4Spec.addrFromPPtr q0.bv) ta tr

/-- After a PT unmap: the PD at (`asid`, `va`) (before) does not name `q0`
(after). -/
def NoName2 (σ σ' : Fl4Spec.State Unit) (asid va q0 : U64) : Prop :=
  ∀ pm p3 p2, SW4 σ asid pm → SE4 σ pm va p3 → SE3 σ p3 va p2 →
    ∀ h, σ'.kheap p2.bv = some (.archObj (.pageDirectory h)) →
    ∀ ta tr, h (Fl4Spec.ucast 9 (vIdx va 21).bv) ≠ .pageTablePDE (Fl4Spec.addrFromPPtr q0.bv) ta tr

/-- **(F1 stage 5) What a table Unmap leaves for `VsNamed`** (VsNamedPost's
`ofUnmapTabF`, VsNamedOps' `unmapTab`): see the module docstring. The
decode's final check (`finF`) is added by VsDecFrame's `VsOpF`. -/
def UnmapTabF (m' : U64 → U64) (x : U64) (c : capability.Cap) (σ σ' : Fl4Spec.State Unit) : Prop :=
  ArchShr σ σ' ∧ ∃ (q0 : U64) (mp : Bool) (asid0 va0 : U64),
    ((c = .PageTable q0 mp asid0 va0 ∧ capV m' x = .PageTable q0 false 0#u64 0#u64 ∧
        (mp = true → NoName2 σ σ' asid0 va0 q0)) ∨
     (c = .PageDirectory q0 mp asid0 va0 ∧ capV m' x = .PageDirectory q0 false 0#u64 0#u64 ∧
        (mp = true → NoName3 σ σ' asid0 va0 q0)) ∨
     (c = .Pdpt q0 mp asid0 va0 ∧ capV m' x = .Pdpt q0 false 0#u64 0#u64 ∧
        (mp = true → NoName4 σ σ' asid0 va0 q0))) ∧
    (mp = true → ∀ i : U64, i.val < 512 → ¬ eP (m' (peA q0 i)))

/-! ## `ArchShr` -/

theorem entShr_trans {a b c : Fl4Spec.ArchKernelObj} (h1 : EntShr a b) (h2 : EntShr b c) : EntShr a c := by
  rcases h1 with rfl | ⟨f, g, rfl, rfl, hfg⟩ | ⟨f, g, rfl, rfl, hfg⟩ | ⟨f, g, rfl, rfl, hfg⟩ | ⟨f, g, rfl, rfl, hfg⟩
  · exact h2
  all_goals
    rcases h2 with rfl | ⟨f', g', e1, rfl, hfg'⟩ | ⟨f', g', e1, rfl, hfg'⟩ | ⟨f', g', e1, rfl, hfg'⟩ |
      ⟨f', g', e1, rfl, hfg'⟩
  all_goals first
    | (cases e1; done)
    | skip
  · exact .inr (.inl ⟨f, g, rfl, rfl, hfg⟩)
  · cases e1
    exact .inr (.inl ⟨f, g', rfl, rfl, fun i => by
      rcases hfg' i with h | h
      · rw [h]; exact hfg i
      · exact .inr h⟩)
  · exact .inr (.inr (.inl ⟨f, g, rfl, rfl, hfg⟩))
  · cases e1
    exact .inr (.inr (.inl ⟨f, g', rfl, rfl, fun i => by
      rcases hfg' i with h | h
      · rw [h]; exact hfg i
      · exact .inr h⟩))
  · exact .inr (.inr (.inr (.inl ⟨f, g, rfl, rfl, hfg⟩)))
  · cases e1
    exact .inr (.inr (.inr (.inl ⟨f, g', rfl, rfl, fun i => by
      rcases hfg' i with h | h
      · rw [h]; exact hfg i
      · exact .inr h⟩)))
  · exact .inr (.inr (.inr (.inr ⟨f, g, rfl, rfl, hfg⟩)))
  · cases e1
    exact .inr (.inr (.inr (.inr ⟨f, g', rfl, rfl, fun i => by
      rcases hfg' i with h | h
      · rw [h]; exact hfg i
      · exact .inr h⟩)))

theorem ArchShr.trans {σ σ1 σ2 : Fl4Spec.State Unit} (h1 : ArchShr σ σ1) (h2 : ArchShr σ1 σ2) : ArchShr σ σ2 :=
  ⟨h2.1.trans h1.1, fun p ao hp =>
    let ⟨ao1, hp1, he1⟩ := h1.2 p ao hp
    let ⟨ao2, hp2, he2⟩ := h2.2 p ao1 hp1
    ⟨ao2, hp2, entShr_trans he1 he2⟩⟩

/-- A PT zeroed (l4v: `InvalidPTE` in every slot). -/
theorem ArchShr.zero_pt {σ : Fl4Spec.State Unit} {q : Fl4Spec.ObjRef} {f : BitVec 9 → Fl4Spec.PTE}
    (hk : σ.kheap q = some (.archObj (.pageTable f))) :
    ArchShr σ (updK σ q (.archObj (.pageTable fun _ => .invalidPTE))) := by
  refine ⟨rfl, fun p ao hp => ?_⟩
  by_cases e : p = q
  · subst e
    rw [hk] at hp; cases hp
    exact ⟨.pageTable fun _ => .invalidPTE, by simp [updK], .inr (.inl ⟨f, _, rfl, rfl, fun _ => .inr rfl⟩)⟩
  · exact ⟨ao, by simp [updK, e, hp], .inl rfl⟩

/-- A PD zeroed. -/
theorem ArchShr.zero_pd {σ : Fl4Spec.State Unit} {q : Fl4Spec.ObjRef} {f : BitVec 9 → Fl4Spec.PDE}
    (hk : σ.kheap q = some (.archObj (.pageDirectory f))) :
    ArchShr σ (updK σ q (.archObj (.pageDirectory fun _ => .invalidPDE))) := by
  refine ⟨rfl, fun p ao hp => ?_⟩
  by_cases e : p = q
  · subst e
    rw [hk] at hp; cases hp
    exact ⟨.pageDirectory fun _ => .invalidPDE, by simp [updK], .inr (.inr (.inl ⟨f, _, rfl, rfl, fun _ => .inr rfl⟩))⟩
  · exact ⟨ao, by simp [updK, e, hp], .inl rfl⟩

/-- A PDPT zeroed. -/
theorem ArchShr.zero_pdpt {σ : Fl4Spec.State Unit} {q : Fl4Spec.ObjRef} {f : BitVec 9 → Fl4Spec.PDPTE}
    (hk : σ.kheap q = some (.archObj (.pdPointerTable f))) :
    ArchShr σ (updK σ q (.archObj (.pdPointerTable fun _ => .invalidPDPTE))) := by
  refine ⟨rfl, fun p ao hp => ?_⟩
  by_cases e : p = q
  · subst e
    rw [hk] at hp; cases hp
    exact ⟨.pdPointerTable fun _ => .invalidPDPTE, by simp [updK],
      .inr (.inr (.inr (.inl ⟨f, _, rfl, rfl, fun _ => .inr rfl⟩)))⟩
  · exact ⟨ao, by simp [updK, e, hp], .inl rfl⟩

/-! ## The lookup data across steps and against FL4's words -/

section
variable {σ σ1 : Fl4Spec.State Unit}

theorem SW4.keep (h1 : σ1.archState.x64AsidTable = σ.archState.x64AsidTable)
    (hk : ∀ p ao, σ.kheap p = some (.archObj ao) → σ1.kheap p = σ.kheap p) {asid pm : U64} (h : SW4 σ asid pm) :
    SW4 σ1 asid pm := by
  obtain ⟨pool, f, ht, hp, hr⟩ := h
  exact ⟨pool, f, by rw [h1]; exact ht, (hk _ _ hp).trans hp, hr⟩

theorem SE4.keep (hk : ∀ p ao, σ.kheap p = some (.archObj ao) → σ1.kheap p = σ.kheap p) {pm va p3 : U64}
    (h : SE4 σ pm va p3) : SE4 σ1 pm va p3 := by
  obtain ⟨f, ta, tr, hp, he⟩ := h
  exact ⟨f, ta, tr, (hk _ _ hp).trans hp, he⟩

theorem SE3.keep (hk : ∀ p ao, σ.kheap p = some (.archObj ao) → σ1.kheap p = σ.kheap p) {p3 va p2 : U64}
    (h : SE3 σ p3 va p2) : SE3 σ1 p3 va p2 := by
  obtain ⟨f, ta, tr, hp, he⟩ := h
  exact ⟨f, ta, tr, (hk _ _ hp).trans hp, he⟩

/-- l4v's `find_vspace_for_asid` on the lookup data. -/
theorem SW4.find {asid pm : U64} (h0 : asid ≠ 0#u64) (h : SW4 σ asid pm) :
    ExceptT.run (Fl4Spec.findVspaceForAsid (Z := Unit) asid.bv) σ = ({(.ok pm.bv, σ)}, False) := by
  obtain ⟨pool, f, ht, hp, hr⟩ := h
  have hpos : asid.bv > 0 := by
    have : asid.val ≠ 0 := fun h => h0 (UScalar.eq_of_val_eq (by simpa using h))
    show 0 < asid.bv.toNat
    exact Nat.pos_of_ne_zero this
  rw [findVspaceForAsid_some hpos ht hp, hr]

theorem run_ok_inj {α : Type} {a b : α} {σ : Fl4Spec.State Unit}
    (h : ((({(.ok a, σ)} : Set (Except Fl4Spec.LookupFailure α × Fl4Spec.State Unit))), False) =
      ({(.ok b, σ)}, False)) : a = b := by
  have := congrArg Prod.fst h
  simpa [Set.singleton_eq_singleton_iff] using this

theorem run_ok_ne_err {α : Type} {a : α} {e : Fl4Spec.LookupFailure} {σ : Fl4Spec.State Unit}
    (h : ((({(.ok a, σ)} : Set (Except Fl4Spec.LookupFailure α × Fl4Spec.State Unit))), False) =
      ({(.error e, σ)}, False)) : False := by
  have := congrArg Prod.fst h
  simp [Set.singleton_eq_singleton_iff] at this

/-- The physical address an entry word names, as a kernel pointer and back. -/
theorem addr_eT (w : U64) : Fl4Spec.addrFromPPtr (eT w).bv = (eA w).bv := by
  rw [eT_bv]; unfold Fl4Spec.ptrFromPAddr Fl4Spec.addrFromPPtr
  exact BitVec.add_sub_cancel _ _

variable {L4 L3 L2 L1 : Set U64} {m : U64 → U64}

/-- The PML4 entry data as FL4's words. -/
theorem SE4.word (hPt : PtRel L4 L3 L2 L1 m σ) {pm va p3 : U64} (hpm : pm ∈ L4) (hv : UserV va)
    (h : SE4 σ pm va p3) :
    eP (m (peA pm (vIdx va 39))) ∧ eT (m (peA pm (vIdx va 39))) = p3 ∧ p3 ∈ L3 := by
  obtain ⟨f, ta, tr, hk, he⟩ := h
  obtain ⟨g, hg, hr⟩ := hPt.l4 pm hpm
  rw [hk] at hg; cases hg
  have hw := hr _ (vIdx_lt_256_of_user hv)
  rw [he] at hw
  obtain ⟨hp, ha, hT⟩ := hw
  exact ⟨hp, eT_of_addr ha, eT_of_addr ha ▸ hT⟩

/-- The PDPT entry data as FL4's words. -/
theorem SE3.word (hPt : PtRel L4 L3 L2 L1 m σ) {p3 va p2 : U64} (hp3 : p3 ∈ L3) (h : SE3 σ p3 va p2) :
    eP (m (peA p3 (vIdx va 30))) ∧ ¬ eS (m (peA p3 (vIdx va 30))) ∧ eT (m (peA p3 (vIdx va 30))) = p2 ∧
      p2 ∈ L2 := by
  obtain ⟨f, ta, tr, hk, he⟩ := h
  obtain ⟨g, hg, hr⟩ := hPt.l3 p3 hp3
  rw [hk] at hg; cases hg
  have hw := hr _ (vIdx_lt va 30)
  rw [he] at hw
  obtain ⟨hp, hs, ha, hT⟩ := hw
  exact ⟨hp, hs, eT_of_addr ha, eT_of_addr ha ▸ hT⟩

/-- A present PML4 entry word names its table. -/
theorem entry4_of {w : U64} {d : Fl4Spec.PML4E} (hr : PML4ERel L3 w d) (hp : eP w) :
    ∃ ta tr, d = .pdPointerTablePML4E (Fl4Spec.addrFromPPtr (eT w).bv) ta tr := by
  cases d with
  | invalidPML4E => exact absurd hp hr
  | pdPointerTablePML4E tab ta tr => exact ⟨ta, tr, by rw [addr_eT, hr.2.1]⟩

/-- A present non-huge PDPT entry word names its table. -/
theorem entry3_of {w : U64} {d : Fl4Spec.PDPTE} (hr : PDPTERel L2 w d) (hp : eP w) (hs : ¬ eS w) :
    ∃ ta tr, d = .pageDirectoryPDPTE (Fl4Spec.addrFromPPtr (eT w).bv) ta tr := by
  cases d with
  | invalidPDPTE => exact absurd hp hr
  | pageDirectoryPDPTE tab ta tr => exact ⟨ta, tr, by rw [addr_eT, hr.2.2.1]⟩
  | hugePagePDPTE _ _ _ => exact absurd hr.2.1 hs

/-- A present non-large PD entry word names its table. -/
theorem entry2_of {w : U64} {d : Fl4Spec.PDE} (hr : PDERel L1 w d) (hp : eP w) (hs : ¬ eS w) :
    ∃ ta tr, d = .pageTablePDE (Fl4Spec.addrFromPPtr (eT w).bv) ta tr := by
  cases d with
  | invalidPDE => exact absurd hp hr
  | pageTablePDE tab ta tr => exact ⟨ta, tr, by rw [addr_eT, hr.2.2.1]⟩
  | largePagePDE _ _ _ => exact absurd hr.2.1 hs

/-- A zeroed PT's words are not present. -/
theorem zero_words_pt (hPt : PtRel L4 L3 L2 L1 m σ) {q : U64} (hq : q ∈ L1)
    (hk : σ.kheap q.bv = some (.archObj (.pageTable fun _ => .invalidPTE))) :
    ∀ i : U64, i.val < 512 → ¬ eP (m (peA q i)) := by
  intro i hi
  obtain ⟨g, hg, hr⟩ := hPt.l1 q hq
  rw [hk] at hg; cases hg
  exact hr i hi

/-- A zeroed PD's words are not present. -/
theorem zero_words_pd (hPt : PtRel L4 L3 L2 L1 m σ) {q : U64} (hq : q ∈ L2)
    (hk : σ.kheap q.bv = some (.archObj (.pageDirectory fun _ => .invalidPDE))) :
    ∀ i : U64, i.val < 512 → ¬ eP (m (peA q i)) := by
  intro i hi
  obtain ⟨g, hg, hr⟩ := hPt.l2 q hq
  rw [hk] at hg; cases hg
  exact hr i hi

/-- A zeroed PDPT's words are not present. -/
theorem zero_words_pdpt (hPt : PtRel L4 L3 L2 L1 m σ) {q : U64} (hq : q ∈ L3)
    (hk : σ.kheap q.bv = some (.archObj (.pdPointerTable fun _ => .invalidPDPTE))) :
    ∀ i : U64, i.val < 512 → ¬ eP (m (peA q i)) := by
  intro i hi
  obtain ⟨g, hg, hr⟩ := hPt.l3 q hq
  rw [hk] at hg; cases hg
  exact hr i hi

end

/-! ## FL4's lookups fail only on missing walk words -/

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- `lookup_pdpt_slot` fails only when the PML4 entry is not present. -/
theorem lookup_pdpt_slot_nwalk (s : S) (pm vaddr : U64) :
    vspace.lookup_pdpt_slot st s pm vaddr ⦃ r => ∀ e, r = .Err e → ¬ eP (L.mem s (peA pm (vIdx vaddr 39))) ⦄ := by
  unfold vspace.lookup_pdpt_slot
  rw [show vspace.idx vaddr 39#u64 = ok (vIdx vaddr 39) from idx_eq _ _ (by decide)]
  apply ok_bind_spec
  rw [entry_eq s pm _ (vIdx_lt _ _)]
  apply ok_bind_spec
  rw [P_PRESENT_eq]
  apply ok_bind_spec
  unfold lift
  apply ok_bind_spec
  by_cases h0 : (L.mem s (peA pm (vIdx vaddr 39)) &&& 1#u64) = 0#u64
  · simp only [h0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    exact (WP.spec_ok _).2 (fun _ _ hp => hp h0)
  · simp only [h0, ↓reduceIte]
    rw [table_of_eq]
    apply ok_bind_spec
    rw [show vspace.idx vaddr 30#u64 = ok (vIdx vaddr 30) from idx_eq _ _ (by decide)]
    apply ok_bind_spec
    rw [entry_addr_eq _ _ (vIdx_lt _ _)]
    apply ok_bind_spec
    exact (WP.spec_ok _).2 (fun _ he => by cases he)

/-- `lookup_pd_slot` fails only when the PML4 entry is not present, or the
PDPT entry is not present or a huge page. -/
theorem lookup_pd_slot_nwalk (s : S) (pm vaddr : U64) :
    vspace.lookup_pd_slot st s pm vaddr ⦃ r => ∀ e, r = .Err e →
      ¬ (eP (L.mem s (peA pm (vIdx vaddr 39))) ∧
        eP (L.mem s (peA (eT (L.mem s (peA pm (vIdx vaddr 39)))) (vIdx vaddr 30))) ∧
        ¬ eS (L.mem s (peA (eT (L.mem s (peA pm (vIdx vaddr 39)))) (vIdx vaddr 30)))) ⦄ := by
  unfold vspace.lookup_pd_slot
  refine WP.spec_bind (WP.spec_and (lookup_pdpt_slot_walk s pm vaddr) (lookup_pdpt_slot_nwalk s pm vaddr)) ?_
  rintro r ⟨hw, hn⟩
  cases r with
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from]
    apply ok_bind_spec
    cases e <;> exact (WP.spec_ok _).2 (fun _ _ h => hn _ rfl h.1)
  | Ok x =>
    obtain ⟨h4, rfl⟩ := hw x rfl
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    rw [L.read_eq]
    apply ok_bind_spec
    rw [P_PRESENT_eq]
    apply ok_bind_spec
    unfold lift
    apply ok_bind_spec
    by_cases h0 : (L.mem s (peA (eT (L.mem s (peA pm (vIdx vaddr 39)))) (vIdx vaddr 30)) &&& 1#u64) = 0#u64
    · simp only [h0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      exact (WP.spec_ok _).2 (fun _ _ h => h.2.1 h0)
    · simp only [h0, ↓reduceIte]
      rw [P_PS_eq]
      apply ok_bind_spec
      apply ok_bind_spec
      by_cases hs : eS (L.mem s (peA (eT (L.mem s (peA pm (vIdx vaddr 39)))) (vIdx vaddr 30)))
      · simp only [(eS_iff _).2 hs, ↓reduceIte]
        exact (WP.spec_ok _).2 (fun _ _ h => h.2.2 hs)
      · have hs' : ¬ ((L.mem s (peA (eT (L.mem s (peA pm (vIdx vaddr 39)))) (vIdx vaddr 30)) &&& 128#u64) != 0#u64) = true :=
          fun h => hs ((eS_iff _).1 h)
        simp only [hs', Bool.false_eq_true, ↓reduceIte]
        rw [table_of_eq]
        apply ok_bind_spec
        rw [show vspace.idx vaddr 21#u64 = ok (vIdx vaddr 21) from idx_eq _ _ (by decide)]
        apply ok_bind_spec
        rw [entry_addr_eq _ _ (vIdx_lt _ _)]
        apply ok_bind_spec
        exact (WP.spec_ok _).2 (fun _ he => by cases he)

end

end

end Fl4Proofs.P3.Vs
