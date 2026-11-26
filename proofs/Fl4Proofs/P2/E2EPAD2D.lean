/-
# P2 (line mmuAD, gen 17): **PageMap in VM epochs, part D** — user writes, the path, the slot, the start fact

* `uf` at the VM entry: `pageEntry_userWrX` / `findV_userWrX` (the walk reads only `VsW` words off `XD`, which are
  no user words: `WalkP` + VX9's `vsRdG_wrX`; natively P3's `lookup_pt_slot_ag` / `find_vspace_for_asid_ag`),
  `planMap_userWrX`, `pm_pdwGX`, `pmEx_wrX`, `pmRoot_wrX`, `pmGX_wr`, **`pm_hufGX`** (natively `pm_hufG`; the
  locks by the record's `lk` [P] at `InvLX` states, VX8's `InvPremX.lk`; `ownP` is memory-independent on VCPU words:
  `ownV_on_mem`).
* **`pmPathX`** = `pm_localPathU` at `Pre := PmPreGX` with every obligation proved (E2EPAD2A–C), under `ownP K`
  at a layout with VCPUs. **`pmSlotVX`** (the slot, void where its record `PmPremX` fails).
* Start fact **`PmStartX`**: `K.vcpus ≠ ∅`, the record, a start state with VX9's **`InvEntV9`** [S] whose entry part
  `G` is **`PmEntG`** = `PmQF ∧ PmEx ∧ PmRoot` (U1P's PageMap entry facts, natively `StartPmK`'s `PmQF ∧ PmEx` and
  `pmRoot_of_qf`) ∧ `WalkP` (vmscope gen 10's walk fact) ∧ `ne0` (no walk answers the null entry address),
  core / locks / memory link (`GlueAt` [P]), the armed program the path's body.
* **`pmStartX_at`**: `StartAt` of the slot from the start fact and the epoch's `VtxBundle4` (`InvLX` from
  `InvEntV9` with the closure of `InvLXS` under user writes by VX9's `ureach_cl` / `invLXS_wrX`).

## [S] justification of the new entry content (Rust: fl4-sync `lib.rs` `local_invocation` l. 538, fl4-core
`localinv.rs` `plan` / `plan_with` / `page_entry`, `arch/x86_64/vspace.rs` `find_vspace_for_asid`,
`lookup_pt_slot`, `decode_page_map`, `write_mapping`)
* `PmQF ∧ PmEx ∧ PmRoot`: what the glue's `localinv.plan` returned at the entry (`pmQF_of_plan`, `pmEx_of_plan`)
  and the mapped PML4 cap's ASID naming its root (natively `pmRoot_of_qf`, from P3's ASID-map invariant). The
  planning code runs the same in a VM epoch: `local_invocation` plans with no VCPU condition, and a guest writes
  only its VCPU's data words and guest frames (`HwStepP`), none of which the plan reads (slots, registers, ASID
  table / pools, paging objects).
* `WalkP`: as for the Delete PTE arm (vmscope gen 10, the same content).
* `ne0`: a `PT` entry address is the PT object's physical address plus an index; PT objects are retyped from
  untyped memory, which never covers physical page 0 (natively `SlJAtZ.spe_ne0`).

## [P]s
`PmPremX.lk` (= VX8's `InvPremX.lk`: the plan's locks survive a user write at an `InvLX` state; `planLocks p` is
state-independent, `pmPremX_planLocks`), `cs` (the index's cores below 64, convention). `GlueAt` data as every slot.

No sorry / admit / native_decide / bv_decide. New module; no existing statement changes.
-/
import Fl4Proofs.P2.E2EPAD2C
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField NullOrFrame TcbSlot)
open Fl4Proofs.P2.E2E (Once ReadOnce StartAt SP)
open Fl4Proofs.P2.Serial (Cfg Init ArmInv NoLoc RunAll)

noncomputable section
open Classical

/-! ## User writes at the VM entry -/

section wr
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayoutP} {s : S} {b : U64}
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}

/-- The walk words are kept by a user write. -/
theorem walkV_wr (hb : b ∈ K.user) (hba : Aligned b) (v : U64) :
    ∀ a, (VsW K.toKLayout a ∧ ¬ XD K a) → st.read (L.wr s b v) a = st.read s a :=
  fun _ ha => read_wr_nu (K := K.toKLayout) hb hba v ha.1.1 ha.1.2.2

/-- **`find_vspace_for_asid` is kept by a user write** at a `WalkP` state. -/
theorem findV_userWrX (W : WalkP st K s) (hb : b ∈ K.user) (hba : Aligned b) (v : U64) (asid : U64) :
    vspace.find_vspace_for_asid st (L.wr s b v) asid = vspace.find_vspace_for_asid st s asid :=
  (vsRdG_trX (m' := st) (x' := L.wr s b v) (W asid 0#u64 (by
    show (0#u64).val ≤ fl4_abi.consts.USER_TOP.val; simp)).1 (walkV_wr hb hba v) (ksBase_wr b v)).1

/-- **The walk from a root the ASID table names is kept by a user write** at a `WalkP` state. -/
theorem pageEntry_userWrX (W : WalkP st K s) (hb : b ∈ K.user) (hba : Aligned b) (v : U64) {asid root : U64}
    (hf : vspace.find_vspace_for_asid st s asid = ok (.Ok root)) (va : U64) :
    localinv.page_entry st (L.wr s b v) root va = localinv.page_entry st s root va := by
  unfold localinv.page_entry
  by_cases hu : va > fl4_abi.consts.USER_TOP
  · rw [if_pos hu, if_pos hu]
  · rw [if_neg hu, if_neg hu]
    have hva : va ≤ fl4_abi.consts.USER_TOP := by
      rw [gt_iff_lt, not_lt] at hu; exact hu
    have T := vsRdG_trX (m' := st) (x' := L.wr s b v) (W asid va hva).1 (walkV_wr hb hba v) (ksBase_wr b v)
    unfold vspace.small_page_entry
    rw [T.2 root hf]

variable {T Rp Scs Nt : Set U64} {H : Heap} {Z : U64 → Nat}

/-- **`plan_with` at `X86PageMap` answers alike after a user write** at a VM entry (`planMap_userWr`). -/
theorem planMap_userWrX (W : WalkP st K s)
    (P : IoPre st K.toKLayout K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (hb : b ∈ K.user) (hba : Aligned b) (v : U64) {sl : obj.Slot} (hsl : sl ∈ K.slots)
    {ex : Array obj.Slot 3#usize} {x : obj.Slot} (hx : Array.index_usize ex 0#usize = ok x) (hxK : x ∈ K.slots)
    {root rasid : U64} (hcx : obj.Slot.cap st x s = ok (.Pml4 root true rasid))
    (hf : vspace.find_vspace_for_asid st s rasid = ok (.Ok root)) :
    localinv.plan_with st (L.wr s b v) (L.curW s) fl4_abi.label.X86PageMap sl ex =
      localinv.plan_with st s (L.curW s) fl4_abi.label.X86PageMap sl ex := by
  have e10 := tcbReg_wrP P hb hba v (r := layout.reg.R10) (by simp [layout.reg.R10])
  have e9 := tcbReg_wrP P hb hba v (r := layout.reg.R9) (by simp [layout.reg.R9])
  have er0 : localinv.reg_arg st (L.wr s b v) (L.curW s) 0#u64 = localinv.reg_arg st s (L.curW s) 0#u64 := by
    unfold localinv.reg_arg; rw [sarg0_reg, sarg0_reg, reg_ok, reg_ok, e10]
  have er2 : localinv.reg_arg st (L.wr s b v) (L.curW s) 2#u64 = localinv.reg_arg st s (L.curW s) 2#u64 := by
    unfold localinv.reg_arg; rw [sarg2_reg, sarg2_reg, reg_ok, reg_ok, e9]
  have ecx := P.cap_userWr hb hba v hxK
  have hpe := pageEntry_userWrX W hb hba v hf
  have efind := findV_userWrX W hb hba v rasid
  unfold localinv.plan_with
  rw [P.cap_userWr hb hba v hsl]
  simp only [bind_ok, if_neg lbl_map_ne_copy, if_neg lbl_map_ne_mint, if_neg lbl_map_ne_del, er0, er2,
    planReadCap_userWr P hb hba v hsl, hx, ecx, hcx, hpe, efind]

/-- **`PmEx` is kept by a user write** (`pmEx_wr` without the bundle). -/
theorem pmEx_wrX (U : UserLayX L K.toKLayout)
    (P : IoPre st K.toKLayout K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    {p : localinv.Plan} (hl : PmEx st p s) (hb : b ∈ K.user) (hba : Aligned b) (v : U64) :
    PmEx st p (L.wr s b v) := by
  obtain ⟨x, hx, c, r1, hr1, hs⟩ := hl
  have hT : K.heap (L.curW s) = some .tcb := P.cT
  have ecur := curW_wrP U P hb hba v
  obtain ⟨C, hroot, hcl, hC⟩ := P.walk
  obtain ⟨res, hres, -⟩ := spec_ex_fd (P0.cspace.lookup_slot.p0 st (L.wr s b v) (L.curW s) c L.total)
  have back := lookup_slot_back (tcb_slot_ctable (L.curW s))
    (P.cap_userWr hb hba v (rootSlot_of P hT))
    (fun p r m y hp hm => P.cap_userWr hb hba v (hC p r m y hp hm).1) hcl hroot hres
  rw [hr1] at back
  have e := ok_inj_ff back
  subst e
  exact ⟨x, hx, c, r1, by rw [ecur]; exact hres, hs⟩

/-- **`PmRoot` is kept by a user write** at a `WalkP` state. -/
theorem pmRoot_wrX (W : WalkP st K s)
    (P : IoPre st K.toKLayout K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    {p : localinv.Plan} (hx : PmEx st p s) (hr : PmRoot st p s) (hb : b ∈ K.user) (hba : Aligned b) (v : U64) :
    PmRoot st p (L.wr s b v) := by
  intro x root rasid hx' hc
  obtain ⟨x0, hx0, hxK⟩ := pmEx_slots P hx
  rw [hx0] at hx'
  have e := ok_inj_ff hx'
  subst e
  rw [P.cap_userWr hb hba v hxK] at hc
  rw [findV_userWrX W hb hba v]
  exact hr x0 root rasid hx0 hc

/-- **`PmGX` is kept by a user write.** -/
theorem pmGX_wr (h : PmGX st K s) (hb : b ∈ K.user) (hba : Aligned b) (v : U64) : PmGX st K (L.wr s b v) := by
  refine ⟨walkP_wr (K := K) hb hba v h.walk, fun asid va he => ?_, h.ks, h.vf, h.rk, h.uk⟩
  have hva := spe_topX he
  obtain ⟨-, e⟩ := vsRdG_wrX (V := fun b => VsW K.toKLayout b ∧ ¬ XD K b) (walkV_wr hb hba v) (ksBase_wr b v)
    (h.walk asid va hva).1
  rw [e] at he
  exact h.ne0 asid va he

/-- **`pdw` at `PmPreGX`**: `InvPlanD` survives a user write (`pm_pdwG`). -/
theorem pm_pdwGX {p : localinv.Plan} {m : U64 → U64} (s : S) (b v : U64)
    (hE : PmPreGX st Cs Ω Sg Ac Locks p K m s) (hb : b ∈ K.user) (hba : Aligned b) :
    InvPlanD st p (L.wr s b v) := by
  obtain ⟨⟨hJ, hq, hG⟩, hEx, hR⟩ := hE
  have hq0 := hq
  obtain ⟨⟨hio, ⟨t, info, ex, ht, hi, hpw⟩, harm, -⟩, -⟩ := hq0
  have P := hio.1
  have et : t = L.curW s := by rw [cur_thread_ok] at ht; exact (ok_inj_ff ht).symm
  subst et
  have hlbl := (harm _ info (cur_thread_ok s) hi).1
  rw [hlbl] at hpw
  obtain ⟨-, -, -, -, -, -, hsK, -, -, -⟩ := pm_core hq
  obtain ⟨x, hx, hxK⟩ := pmEx_slots P hEx
  have hkp := plan_with_kp hpw
  obtain ⟨-, -, -, -, root, rasid, -, x0, -, -, hx0, -, hcx, -⟩ := plan_with_mapF hpw
  rw [← hkp.2, hx] at hx0
  obtain rfl := ok_inj_ff hx0
  refine ⟨L.curW s, info, ex, ?_, ?_, ?_⟩
  · rw [cur_thread_ok, curW_wrP hJ.ul P hb hba v]
  · rw [msgInfo_wrP P hb hba v]; exact hi
  · rw [hlbl, planMap_userWrX hG.walk P hb hba v hsK (by rw [← hkp.2]; exact hx) hxK hcx (hR x root rasid hx hcx)]
    exact hpw

/-- **`uf` of the PageMap slot at `PmPreGX`** (`pm_hufG` without the bundle). -/
theorem pm_hufGX {p : localinv.Plan} {m : U64 → U64} (hCs : ∀ c ∈ Cs, c.val < 64)
    (hlk : ∀ s b v, (∃ F, InvLX st F K.toKLayout s) → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s) :
    ∀ s b v, PmPreGX st Cs Ω Sg Ac Locks p K m s → b ∈ K.user → Aligned b →
      PmPreGX st Cs Ω Sg Ac Locks p K m (L.wr s b v) ∧
        Locks (L.wr s b v) = Locks s ∧
        PmRSU st K Locks (L.wr s b v) = PmRSU st K Locks s ∧
        PmWSU st K Locks (L.wr s b v) = PmWSU st K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s := by
  intro s b v hE hb hba
  have hE0 := hE
  obtain ⟨⟨hJ, ⟨⟨hio, hpd, harm, hlks⟩, hlk0⟩, hG⟩, hEx, hRt⟩ := hE
  have P := hio.1
  have el := hlk s b v ⟨_, hJ⟩ hb hba
  have ecur := curW_wrP hJ.ul P hb hba v
  have emsg := msgInfo_wrP P hb hba v
  have hct : ∀ t, sched.cur_thread st (L.wr s b v) = ok t → t = L.curW s := by
    intro t ht
    rw [cur_thread_ok, ecur] at ht
    exact (ok_inj_ff ht).symm
  have eo : OwnMap.own K.toKLayout (L.mem (L.wr s b v)) = OwnMap.own K.toKLayout (L.mem s) :=
    E2E.ownDep hJ.regionOK hJ.userOK _ _ (fun x hx hxu => mem_wr_ne' hba hx (fun e => hxu (e ▸ hb)))
  have eoP : ownP K (L.mem (L.wr s b v)) = ownP K (L.mem s) := by
    funext x
    by_cases hx : x ∈ K.ptes
    · rw [ownP_pte hx, ownP_pte hx]
    · rw [ownP_off hx, ownP_off hx]
      by_cases hv : ∃ w, InVcpu K.toKLayoutV w x
      · exact ownV_on_mem hG.rk.base hv
      · rw [ownV_off hv, ownV_off hv, eo]
  have e3 := (ioRWDS_wrI (Locks := Locks) hJ P hb hba v el).2.2
  have eR : PmRS st K Locks (L.wr s b v) = PmRS st K Locks s := by
    funext w
    simp only [PmRS, RPerm, GateOnly, eoP, el, LawfulStore.cpu_wr]
  have eW : PmWS st K Locks (L.wr s b v) = PmWS st K Locks s := by
    funext w
    simp only [PmWS, WPerm, eoP, el, LawfulStore.cpu_wr]
  refine ⟨⟨⟨hJ.wr hb hba v, ⟨⟨ioQ_wrX hJ.ul hCs hio hb hba v,
    pm_pdwGX s b v hE0 hb hba, ?_, ?_⟩, invLk_wrX hJ.ul P hlk0 hb hba v⟩, pmGX_wr hG hb hba v⟩,
    pmEx_wrX hJ.ul P hEx hb hba v, pmRoot_wrX hG.walk P hEx hRt hb hba v⟩, el, ?_, ?_, e3⟩
  · intro t info ht hi
    obtain rfl := hct t ht
    rw [emsg] at hi
    exact harm _ info (cur_thread_ok s) hi
  · intro i x hi hx
    rw [el]
    exact hlks i x hi hx
  · funext y; unfold PmRSU; rw [eR]
  · funext y; unfold PmWSU; rw [eW]

end wr

/-! ## The path and the slot -/

section slot
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)

/-- **The PageMap slot's record in VM epochs** (module docstring). -/
structure PmPremX (j : InvArg S) (K : KLayoutP) : Prop where
  /-- [P] (VX8's `InvPremX.lk`): the locks survive a user write at an `InvLX` state. -/
  lk : ∀ s b v, (∃ F, InvLX st F K.toKLayout s) → b ∈ K.user → Aligned b → j.Locks (L.wr s b v) = j.Locks s
  /-- The index's cores are below 64 (convention; natively `PmObl7.cs`). -/
  cs : ∀ c ∈ j.Cs, c.val < 64

/-- **The PageMap path in a VM epoch** (`pm_localPathU` at `PmPreGX`, every obligation proved). -/
noncomputable def pmPathX (j : InvArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (h : PmPremX st j K) :
    E2E.LocalPath (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) :=
  pm_localPathU (K := K) (m0 := m) (Locks := j.Locks) ar hA hK hU j.number j.p hm
    (P := PmPreGX st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K m) (fun _ h => h.1.2.1.1.1.1)
    (pm_accU_of_blkGX hA hK (pm_blkGX hA hK)) (fun s a r hE => pm_decX hA j.number s a r hE.1) (pm_mvGX hA hK hU)
    (fun s s' a r0 r hE => pm_raX hA j.number s s' a r0 r hE.1)
    (pm_hufGX h.cs h.lk)
    (R.invBodyPmG j.number j.p)
    ((pm_isProgOnX hA j.number).mono (fun _ hy => by
      obtain ⟨s0, hP, Al⟩ := hy
      exact ⟨s0, hP.1, alt_pmU Al⟩))
    (pm_noZero j.number j.p) (pm_roAGX hA hm hK) (fun s s' a r hE => pm_roX hA j.number s s' a r hE.1)

/-- **The PageMap slot in VM epochs, under `ownP`.** -/
noncomputable def pmSlotVX : PathsP (InvArg S) :=
  fun j K m hK hU => if h : PmPremX st j K then pmPathX st ar hA hm j K m hK hU h
    else E2EV.LocalPath.void (fl4Dflt st ar hm)
      (fun x hx => Fl4Proofs.P2.ko_aligned hK.base.base hU.base.base x hx)

theorem pmSlotVX_pos {j : InvArg S} {K : KLayoutP} {m : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K}
    (h : PmPremX st j K) : pmSlotVX st ar hA hm j K m hK hU = pmPathX st ar hA hm j K m hK hU h :=
  dif_pos h

/-- **The PageMap entry part of the VM start entry** (module docstring). -/
def PmEntG (j : InvArg S) (K : KLayoutP) (m : U64 → U64) (s : S) : Prop :=
  PmQF st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K m s ∧ PmEx st j.p s ∧ PmRoot st j.p s ∧ WalkP st K s ∧
    ∀ asid va, localinv.small_page_entry st s asid va ≠ ok (some 0#u64)

/-- **The PageMap slot's start fact in a VM epoch** (module docstring): the record, a start state with `InvEntV9`
[S] at `G := PmEntG`, core / locks / memory link ([P], as `GlueAt`), the armed program the path's body. -/
def PmStartX (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64) (hs : U64 → Prop)
    (q : SP) (j : InvArg S) : Prop :=
  K.vcpus ≠ ∅ ∧ ∃ h : PmPremX st j K, ∃ (σ : S) (a : A),
    InvEntV9 st K (PmEntG st j K m) σ ∧
    L.cpu σ = c ∧ j.Locks σ = hs ∧ (∀ x, Aligned x → ¬ x ∈ K.user → L.mem σ x = m x) ∧
    q = (pmPathX st ar hA hm j K m hK hU h).body σ a

variable {st ar hA hm}

/-- **`StartAt` of the PageMap slot in a VM epoch** from its start fact and the epoch's bundle. -/
theorem pmStartX_at {K : KLayoutP} {μ : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64}
    {hs : U64 → Prop} {q : SP} {j : InvArg S} (E : VtxBundle4 st L K)
    (h : PmStartX st ar hA hm K μ hK hU c hs q j) :
    StartAt (pmSlotVX st ar hA hm j K μ hK hU) c hs μ q := by
  obtain ⟨-, hp, σ, a, he, hc, hl, hμ, rfl⟩ := h
  rw [pmSlotVX_pos st ar hA hm hp]
  obtain ⟨hQ, hEx, hRt, hW, h0⟩ := he.ent.2
  have hcl : ∀ s', UReach (L := L) K.toKLayout σ s' → InvLXS st K.toKLayout s' ∧ True := by
    intro s' hr
    refine ⟨(ureach_cl (K := K.toKLayout)
      (P1 := fun s => InvLXS st K.toKLayout s ∧ IoPre st K.toKLayout K.heap.tcbs j.Cs j.Ω K.heap j.Sg
        K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits j.Ac s)
      (P := fun s => InvLXS st K.toKLayout s ∧ IoPre st K.toKLayout K.heap.tcbs j.Cs j.Ω K.heap j.Sg
        K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits j.Ac s)
      (fun s b v h hb hba => ⟨invLXS_wrX E.b.ul h.2 h.1 hb hba v, ioPre_wrL E.b.ul hp.cs h.2 hb hba v⟩)
      (fun s b v _ h hb hba => ⟨invLXS_wrX E.b.ul h.2 h.1 hb hba v, ioPre_wrL E.b.ul hp.cs h.2 hb hba v⟩)
      (fun s h => h) σ s' hr ⟨he.ent.1, hQ.1.1.1⟩).1, trivial⟩
  have hJ : InvLX st (fun _ => True) K.toKLayout σ :=
    ⟨hK.base.base, hU.base.base, E.la, E.b.ul, he.hz, hcl⟩
  exact ⟨σ, a, ⟨⟨hJ, hQ, ⟨hW, h0, he.qps.ks, ⟨E.b.vu, E.ko⟩, hK, hU⟩⟩, hEx, hRt⟩, hc, hl, hμ, rfl⟩

/-- **`PmPremX` holds for every index with a state-independent lock map and cores below 64.** -/
theorem pmPremX_planLocks {j : InvArg S} {K : KLayoutP} {p : localinv.Plan} (e : j.Locks = planLocks p)
    (hc : ∀ c ∈ j.Cs, c.val < 64) : PmPremX st j K :=
  ⟨fun _ _ _ _ _ _ => by rw [e]; rfl, hc⟩

end slot

end
end Fl4Proofs.P2.E2EP
