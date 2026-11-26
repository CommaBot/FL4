/-
# P2 (line hpzg, generation 8): `huf` of the frame-cap invocation path, reduced (`InvHuf`)

`inv_pathsKF` (stpost gen 13, P2/InvBlk.lean) takes [J] `huf`: at `Pre := SlJAt K ∧ InvQL …`, writing an aligned
user word keeps `Pre`, the locks, and the sets `IoRS` / `IoWS` / `IoDS`. Here `huf` is proved from three smaller
premises, each about one part of `InvQL`:

* `SlJAt` by `SlJAt.userWr` (P3's `JAtZ.userWrB`); the sets by `SlJAt.ioRWDS_wrSt` (`own` reads no user word);
  `IoQ` by stpost's `ioQ_wr` from [J] `hIw` (`IoPre` survives the write: the same open premise as `io_pathsKQ`'s);
* `InvArm`, `InvLen`: the current thread (`SlJAt.curW_wr`) and its `MSG_INFO` register (a TCB word,
  `SlJAt.tcbW_wr`) are kept (`msgInfo_wr`);
* the plan's locks held: by [P] `hlk` (the locks are determined by kernel words, slhuf's `hlk_of_kernelDetU`; the
  same premise as `io_pathsKQ`'s);
* **`InvLk`** (the plan's lookup), **proved** (`invLk_wr`): the lookup of the `CAP` register (a TCB word) walks
  the CTable root slot (the TCB's slot 0, a capability slot, `SlJAtZ.tslots`) and radix-masked slots of the walk's
  CNodes (capability slots, `IoPre.walk`). Capability-slot words are no user words (`IoPre.region_kernel`), so
  their caps are kept (`cap_wr`), and `lookup_slot_back` with P0 totality gives the same result;
* `InvPlanD` (the plan): [J] `hPDw`. The Delete arm of `plan_with` also reads the target's walk, the target's
  words and `small_page_entry`'s page-table words. A user word is in none of these, but P3 does not export that
  for page-table words. What it would have to export: every word `localinv.page_entry` / `find_vspace_for_asid`
  reads at a `JAtZ` state (ASID table and pool, PML4 / PDPT / PD / PT entries) is outside `Z.B`'s words. `SlJAt.userAsid`
  already covers the ASID table; the paging-structure words are missing.

* **`hufQL_of`**: `inv_pathsKF`'s `huf` from `hIw` [J], `hPDw` [J], `hlk` [P].

No statement of an existing declaration changes; no `kernel_entry_reach*` is touched.
-/
import Fl4Proofs.P2.InvBlk
import Fl4Proofs.P2.InvLay
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout fld)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {s : S} {b : U64}

/-- A TCB's register word is kept by a user write at a bundle state. -/
theorem tcbReg_wr (hJ : SlJAt (L := L) K s) (hb : b ∈ K.user) (hba : Aligned b) (v : U64) {t : U64}
    (ht : K.heap t = some .tcb) (hA : TcbAddr t) {r : U64} (hr : r.val < 384) :
    L.mem (L.wr s b v) (regA t r) = L.mem s (regA t r) := by
  obtain ⟨k, hk, e⟩ := regA_eq hA hr
  rw [e]
  have h := hJ.tcbW_wr hb hba v ht (o := k) (by omega) (by omega)
  unfold fld at h
  exact h

/-- The current thread's message info is kept by a user write at a bundle state. -/
theorem msgInfo_wr (hJ : SlJAt (L := L) K s) (hb : b ∈ K.user) (hba : Aligned b) (v : U64) {t : U64}
    (ht : K.heap t = some .tcb) (hA : TcbAddr t) :
    msg.msg_info st (L.wr s b v) t = msg.msg_info st s t := by
  unfold msg.msg_info
  rw [reg_ok, reg_ok, tcbReg_wr hJ hb hba v ht hA (by simp [layout.reg.MSG_INFO])]

/-- A TCB's CTable slot (its slot 0, at the TCB's address) is a capability slot. -/
theorem slJAt_root (hJ : SlJAt (L := L) K s) {t : U64} (ht : K.heap t = some .tcb) : t ∈ K.slots := by
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := hJ
  have h := B.tslots t ht 0#u64 (by simp)
  have e : slotIdx t 0#u64 = t := by
    apply UScalar.eq_of_val_eq
    simp [slotIdx, core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]
  rwa [e] at h

variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}

/-- A capability slot's cap is kept by an aligned write of a user word (at an `IoPre` state). -/
theorem IoPre.cap_userWr (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) (hb : b ∈ K.user) (hba : Aligned b)
    (v : U64) {sl : U64} (hsl : sl ∈ K.slots) : obj.Slot.cap st sl (L.wr s b v) = obj.Slot.cap st sl s := by
  obtain ⟨h8, hf⟩ := P.lay.slot8 sl hsl
  have hv : (core.num.U64.wrapping_add sl 8#u64).val = sl.val + 8 := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  have n0 : sl ∉ K.user :=
    P.region_kernel (Or.inl (by rw [P.lay.slotw sl hsl sl ⟨le_refl _, by omega⟩]; simp))
  have n8 : core.num.U64.wrapping_add sl 8#u64 ∉ K.user :=
    P.region_kernel (Or.inl (by rw [P.lay.slotw sl hsl _ ⟨by omega, by omega⟩]; simp))
  exact cap_wr hba h8 (by unfold Aligned; omega) (fun e => n0 (e ▸ hb)) (fun e => n8 (e ▸ hb))

/-- (hpzg gen 8) **The plan's lookup is kept by a user write** at a bundle state with `IoPre`. -/
theorem invLk_wr (hJ : SlJAt (L := L) K s)
    (P : IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    {p : localinv.Plan} (hl : InvLk st p s) (hb : b ∈ K.user) (hba : Aligned b) (v : U64) :
    InvLk st p (L.wr s b v) := by
  obtain ⟨x, hx, ex⟩ := hl
  have hT : K.heap (L.curW s) = some .tcb := P.cT
  have ecur := hJ.curW_wr hb hba v
  have ecap := tcbReg_wr hJ hb hba v hT P.tA (r := layout.reg.CAP) (by simp [layout.reg.CAP])
  obtain ⟨C, hroot, hcl, hC⟩ := P.walk
  obtain ⟨res, hres, -⟩ := spec_ex_fd (P0.cspace.lookup_slot.p0 st (L.wr s b v) (L.curW s)
    (L.mem s (regA (L.curW s) layout.reg.CAP)) L.total)
  have back := lookup_slot_back (tcb_slot_ctable (L.curW s))
    (P.cap_userWr hb hba v (slJAt_root hJ hT))
    (fun p r m y hp hm => P.cap_userWr hb hba v (hC p r m y hp hm).1) hcl hroot hres
  rw [hx] at back
  have e := ok_inj_ff back
  subst e
  refine ⟨x, ?_, ex⟩
  rw [ecur, ecap]
  exact hres

/-- (hpzg gen 8) **`inv_pathsKF`'s `huf`** at `Pre := SlJAt K ∧ InvQL …`, from [J] `hIw` (`IoPre` survives a
user write at a bundle state), [J] `hPDw` (`InvPlanD` does) and [P] `hlk` (the locks are kept). -/
theorem hufQL_of {Locks : S → U64 → Prop} {p : localinv.Plan}
    (hIw : ∀ K s b v, SlJAt (L := L) K s →
      IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s →
      b ∈ K.user → Aligned b →
      IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac (L.wr s b v))
    (hPDw : ∀ K m s b v, SlJAt (L := L) K s → InvQL st Cs Ω Sg Ac Locks p K m s → b ∈ K.user → Aligned b →
      InvPlanD st p (L.wr s b v))
    (hlk : ∀ K s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s) :
    ∀ K m s b v, SlJAt (L := L) K s → InvQL st Cs Ω Sg Ac Locks p K m s → b ∈ K.user → Aligned b →
      (SlJAt (L := L) K (L.wr s b v) ∧ InvQL st Cs Ω Sg Ac Locks p K m (L.wr s b v)) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s := by
  intro K m s b v hJ hq hb hba
  have hq0 := hq
  obtain ⟨⟨⟨hio, hpd, harm, hlks⟩, hlk0⟩, hlen⟩ := hq
  have P := hio.1
  have hT : K.heap (L.curW s) = some .tcb := P.cT
  have el := hlk K s b v hJ hb hba
  have ecur := hJ.curW_wr hb hba v
  have emsg := msgInfo_wr hJ hb hba v hT P.tA
  have hct : ∀ t, sched.cur_thread st (L.wr s b v) = ok t → t = L.curW s := by
    intro t ht
    rw [cur_thread_ok, ecur] at ht
    exact (ok_inj_ff ht).symm
  refine ⟨⟨hJ.userWr hb v, ⟨⟨ioQ_wr hIw K m s b v hJ hio hb hba, hPDw K m s b v hJ hq0 hb hba, ?_, ?_⟩,
    invLk_wr hJ P hlk0 hb hba v⟩, ?_⟩, el, hJ.ioRWDS_wrSt hb hba v el⟩
  · intro t info ht hi
    obtain rfl := hct t ht
    rw [emsg] at hi
    exact harm _ info (cur_thread_ok s) hi
  · intro i x hi hx
    rw [el]
    exact hlks i x hi hx
  · intro t info ht hi
    obtain rfl := hct t ht
    rw [emsg] at hi
    exact hlen _ info (cur_thread_ok s) hi

end

end Fl4Proofs.P2.PathObl
