/-
# P2 (line slhuf, gen 3): the syscall local path with the canonical `Q`

`sl_pathsKF` (P2/SlJFound.lean) keeps the caller's extra precondition `Q` generic and asks
`hQ` [J]: `Q` survives a write of a user word at a bundle (`SlJAt`) state. Here `Q` is fixed
to the conjunction of the entry facts the path reads,

  `SlQ := SlPreB ∧ SlEntL ∧ SlSyncC ∧ SlAccR`,

so `hPE` / `hEl` / `hC` / `hAr` become projections and `hQ` splits into one frame fact per
conjunct.

## Frame lemmas proved (at a `SlJAt` state, `b ∈ K.user`, `Aligned b`)
* `SlJAt.curW_wr`: the current thread is kept (its node word is no user word).
* `LayP.mem_wrT`: a word of a heap TCB is kept (`LayP.user`: user words lie in no TCB).
* `SlJAt.flags_wr`, `SlJAt.trap_wr`: the current thread's flags, hence `SlTrap`, are kept.
* `SlJAt.fh_wr`: the cap in the current thread's fault-handler slot is kept (TCB words).
* `SlJAtZ.cnOffU`: P3's `JAtZ.cnOff` (P3/XTopJointKEntryRRF.lean) with the frame words widened
  by the user words: the CNode slots reachable from the current thread's root are slots of
  `Zx.th`, so no user word (`LayP.userSlot`).
* `SlJAt.replyCaps_wr`: `reply_caps` of the current thread is kept (P1's `reply_caps_keep`:
  the TCB words it reads are no user word, the cap-slot words of `cnOffU` neither).
* **`SlJAt.syncC_wr`**: `SlSyncC` (fl4-sync's contract) is kept. No premise.
* **`SlJAt.entL_wr`**: `SlEntL` is kept, given the glue's locks are (`hlk` [P], as before).

## Not proved: `SlPreB`, `SlAccR` (narrow named premises of `sl_pathsKC`)
Both quantify over the `LocalPre` successors `X` of the entry state (the state after the
entry's `FAULT_IP` write and `update_timestamp`), and state facts about `X` (`BXI`, `RRPl`,
`FaultChecks`/`RRChecks`-guarded placement and lock facts). Carrying them from `s` to
`L.wr s b v` needs (1) that the successors of `L.wr s b v` are those of `s` with the user word
written, which holds only up to the memory function: `LawfulStore` has no extensionality
(`StoreExt` is not among `sl_pathsK`'s premises), so `wr` does not commute on states; and (2) a
frame lemma for each field over a user-word write at `X` (`BXI`, the `RRPl` placement, the
`FaultChecks` / `RRChecks` reads of endpoints, the scheduler bitmap, `schedulable_here`).
`SlPreB` has 15 such fields. They stay premises:
* `hPBw` [J]: `SlPreB` survives a user-word write at a bundle state.
* `hArw` [P]: `SlAccR` (`frl`, itself [P]) survives a user-word write at a bundle state.

## `sl_pathsKC`, `sl_pathsKC_startAt`
`sl_pathsKF` / `_startAt` at `Q := SlQ`; premises `hPBw` [J], `hArw` [P], `hlk` [P], `hpz` and
the totality / mask premises as before. `hPE`, `hEl`, `hC`, `hAr` are the projections of `SlQ`
(`hC` [P], `hEl` [P], `hAr` [P] are now facts at the entry state, as part of `Q`).
-/
import Fl4Proofs.P2.SlJFound
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap Fl4Proofs.P0.Consts
open Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P3.Vs

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **A word of a heap TCB is kept by a user-word write** (`LayP.user`). -/
theorem _root_.Fl4Proofs.P2.OwnMap.LayP.mem_wrT {K : KLayout} (hP : LayP K) {s : S} {b x t : U64} (hb : b ∈ K.user)
    (hba : Aligned b) (v : U64) (ht : K.heap t = some .tcb) (hx : Aligned x) (h1 : t.val ≤ x.val)
    (h2 : x.val < t.val + 4096) : L.mem (L.wr s b v) x = L.mem s x :=
  mem_wr_ne' hba hx fun e => hP.user b hb t .tcb ht (Or.inl rfl) (by
    subst e; exact ⟨h1, by simp only [HKind.bits]; omega⟩)

/-- **The current thread is kept by a user-word write** at a bundle state. -/
theorem SlJAt.curW_wr {K : KLayout} {s : S} (h : SlJAt (L := L) K s) {b : U64} (hb : b ∈ K.user)
    (hba : Aligned b) (v : U64) : L.curW (L.wr s b v) = L.curW s := by
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := h
  have hN : NodePlaced st (Heap.tcbs K.heap) s (L.cpu s) := TInv.nodes B.j.blk _ B.j.kern.cpuCs
  have hv := nodeAt_val hN (off := layout.node.CUR_THREAD) (by rw [curth_val]; omega)
  rw [curth_val] at hv
  simp only [LawfulStore.nodeBase, B.ksb] at hv
  unfold LawfulStore.curW
  rw [nodeAt_wr, LawfulStore.cpu_wr]
  refine mem_wr_ne' hba (nodeAt_aligned hN (by rw [curth_val]; omega) (by rw [curth_val])) fun e => ?_
  have hbv : b.val = K.ksb.val + 13568 + (L.cpu s).val * 4288 := by rw [e]; omega
  exact B.userNode b hb (L.cpu s) ⟨B.cpu, by omega, by omega⟩

theorem SlJAtZ.curTcb {A' : Type} {arI : machine.Arch A'} {AR : A' → Fl4Spec.Cr3 → Prop}
    {Zx : Fl4Proofs.P3.XSets} {Cx Ax : Set U64} {Lst : U64 → List U64} {D : Set U64} {K : KLayout}
    {s : S} {a' : A'} {σ : Fl4Spec.State Unit} (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) :
    K.heap (L.curW s) = some .tcb ∧ TcbAddr (L.curW s) := by
  obtain ⟨Tr, Cq, hJ⟩ := B.j.jpl
  have ht : K.heap (L.curW s) = some .tcb := (hJ.tcb _).1 (B.j.curW_tcb (cur_thread_ok (L := L) s))
  exact ⟨ht, TInv.tcbs B.j.blk _ ht⟩

/-- **The current thread's flags are kept by a user-word write** at a bundle state. -/
theorem SlJAt.flags_wr {K : KLayout} {s : S} (h : SlJAt (L := L) K s) {b : U64} (hb : b ∈ K.user)
    (hba : Aligned b) (v : U64) :
    obj.Tcb.flags st (L.curW s) (L.wr s b v) = obj.Tcb.flags st (L.curW s) s := by
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := h
  obtain ⟨ht, hA⟩ := B.curTcb
  have hv := tcb_wadd_val hA (o := 3456#u64) (by decide)
  rw [flags_mem, flags_mem, B.layP.mem_wrT hb hba v ht (field_aligned hA (by decide) (by decide))
    (by rw [hv]; omega) (by rw [hv]; simp)]

/-- **`SlTrap` is kept by a user-word write** at a bundle state. -/
theorem SlJAt.trap_wr {K : KLayout} {s : S} (h : SlJAt (L := L) K s) {b : U64} (hb : b ∈ K.user)
    (hba : Aligned b) (v : U64) : SlTrap st (L.wr s b v) ↔ SlTrap st s := by
  unfold SlTrap
  rw [h.curW_wr hb hba v, h.flags_wr hb hba v]

/-- **The current thread's fault-handler cap is kept by a user-word write** at a bundle state
(its two words are TCB words). -/
theorem SlJAt.fh_wr {K : KLayout} {s : S} (h : SlJAt (L := L) K s) {b : U64} (hb : b ∈ K.user)
    (hba : Aligned b) (v : U64) :
    obj.Slot.cap st (fhA (L := L) (L.wr s b v)) (L.wr s b v) = obj.Slot.cap st (fhA (L := L) s) s := by
  have ec := h.curW_wr hb hba v
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := h
  obtain ⟨ht, hA⟩ := B.curTcb
  have hf := hA.fits
  have hal := hA.align
  show obj.Slot.cap st (slotIdx (L.curW (L.wr s b v)) layout.tcb.SLOT_FAULT_HANDLER) (L.wr s b v) =
    obj.Slot.cap st (slotIdx (L.curW s) layout.tcb.SLOT_FAULT_HANDLER) s
  rw [ec]
  have hv : (slotIdx (L.curW s) layout.tcb.SLOT_FAULT_HANDLER).val = (L.curW s).val + 96 := by
    have := slj_slotIdx_val (t := L.curW s) (i := layout.tcb.SLOT_FAULT_HANDLER)
      (by simp [layout.tcb.SLOT_FAULT_HANDLER]; omega)
    simpa [layout.tcb.SLOT_FAULT_HANDLER] using this
  have hv8 : (core.num.U64.wrapping_add (slotIdx (L.curW s) layout.tcb.SLOT_FAULT_HANDLER) 8#u64).val =
      (L.curW s).val + 104 := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, hv]; omega
  unfold obj.Slot.cap
  rw [L.read_pair_eq, L.read_pair_eq,
    B.layP.mem_wrT hb hba v ht (by unfold Aligned; rw [hv]; omega) (by rw [hv]; omega) (by rw [hv]; omega),
    B.layP.mem_wrT hb hba v ht (by unfold Aligned; rw [hv8]; omega) (by rw [hv8]; omega) (by rw [hv8]; omega)]

/-- **`CnOff` with the user words outside the cap-slot words** (P3's `JAtZ.cnOff` with the
frame set widened by `K.user`): the indexed slots are slots of `Zx.th`, which hold no user word
(`LayP.userSlot`). -/
theorem SlJAtZ.cnOffU {A' : Type} {arI : machine.Arch A'} {AR : A' → Fl4Spec.Cr3 → Prop}
    {Zx : Fl4Proofs.P3.XSets} {Cx Ax : Set U64} {Lst : U64 → List U64} {D : Set U64} {K : KLayout}
    {s : S} {a' : A'} {σ : Fl4Spec.State Unit} (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ)
    {t : U64} (et : sched.cur_thread st s = ok t) :
    CnOff (L := L) (Heap.tcbs K.heap) Cx (Heap.frame K.heap ∪ K.user) s t := by
  have J := B.j
  have htcb := J.curW_tcb et
  have hR := J.xtop.rel.2.1.1
  have hV := J.xtop.rel.2.1.2.1
  intro sl root hsl hroot
  obtain ⟨tcb, c, -, hc, -, hval⟩ := hR.ctable hV htcb
  have hsl' := tcb_slot_spec t layout.tcb.SLOT_CTABLE
  rw [hsl, WP.spec_ok] at hsl'
  rw [hsl', show (layout.tcb.SLOT_CTABLE.bv : BitVec 64) = 0#64 by simp [layout.tcb.SLOT_CTABLE],
    slot_cap_eq, hc] at hroot
  obtain rfl := ok_inj_ff hroot
  refine ⟨fun p r => Zx.th p = some (.cnode r.val), fun p r gs g e => ?_, fun p r m x p' r' gs' g' hC hm e => ?_,
    fun p r m x hC hm => ?_⟩
  · subst e; exact hval.1
  · rw [cnSlot_eq, slot_cap_eq] at e
    exact (hV.cnode p r.val hC _ (andMask_lt_pow hm x) _ e).1
  · have hi := andMask_lt_pow hm x
    have hsS : slotOf p (x &&& m).val ∈ K.slots := by
      rw [B.slots]; exact ⟨p, _, Or.inl ⟨_, hC, hi⟩, rfl⟩
    obtain ⟨-, q, k, hq, hq1, hq2, -, -⟩ := B.layP.slot _ hsS
    have hfit := B.layP.heap.fits q k hq
    have nU : ∀ w, (w = slotOf p (x &&& m).val ∨
        w = core.num.U64.wrapping_add (slotOf p (x &&& m).val) 8#u64) → w ∉ K.user := by
      intro w hw hwu
      apply B.layP.userSlot w hwu _ hsS
      rcases hw with rfl | rfl
      · exact ⟨le_refl _, by omega⟩
      · have e : (core.num.U64.wrapping_add (slotOf p (x &&& m).val) 8#u64).val =
            (slotOf p (x &&& m).val).val + 8 := by
          generalize slotOf p (x &&& m).val = w0 at hq1 hq2 ⊢
          simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
        exact ⟨by rw [e]; omega, by rw [e]; omega⟩
    rw [cnSlot_eq]
    have h1 := J.capSW hC hi (Or.inl rfl)
    have h2 := J.capSW hC hi (Or.inr rfl)
    refine ⟨⟨h1.1, ?_⟩, ⟨h2.1, ?_⟩⟩
    · rintro (h | h)
      · exact h1.2 h
      · exact nU _ (Or.inl rfl) h
    · rintro (h | h)
      · exact h2.2 h
      · exact nU _ (Or.inr rfl) h

/-- **`reply_caps` of the current thread is kept by a user-word write** at a bundle state
(P1's `reply_caps_keep` with `SlJAtZ.cnOffU`). -/
theorem SlJAt.replyCaps_wr {K : KLayout} {s : S} (h : SlJAt (L := L) K s) {b : U64} (hb : b ∈ K.user)
    (hba : Aligned b) (v : U64) {rp ep : U64}
    (hrc : fastpath.reply_caps st s (L.curW s) = ok (some (rp, ep))) :
    fastpath.reply_caps st (L.wr s b v) (L.curW s) = ok (some (rp, ep)) := by
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := h
  obtain ⟨ht, hA⟩ := B.curTcb
  refine reply_caps_keep (T := Heap.tcbs K.heap) (Cs := Cx) (Sg := Heap.frame K.heap ∪ K.user) hA hrc
    (writesIn_wr hba) ?_ ?_ (B.cnOffU (cur_thread_ok (L := L) s))
  · intro Kk hK e
    have hKv : Kk.val < 4096 := by
      rcases hK with h | h | h | h <;>
        (try simp [layout.reg.REPLY, layout.reg.R12, layout.reg.CAP, layout.reg.RDI] at h) <;> omega
    have hw := tcb_wadd_val hA hKv
    exact B.layP.user b hb _ .tcb ht (Or.inl rfl)
      ⟨by rw [← e, hw]; omega, by rw [← e, hw]; simp only [HKind.bits]; omega⟩
  · intro w hw e
    exact hw.2 (Or.inr (by rw [e]; exact hb))

/-- **fl4-sync's contract `SlSyncC` is kept by a user-word write** at a bundle state. -/
theorem SlJAt.syncC_wr {K : KLayout} {s : S} (h : SlJAt (L := L) K s) {b : U64} (hb : b ∈ K.user)
    (hba : Aligned b) (v : U64) {n : I64} {found : U64 × U64} (C : SlSyncC st n found s) :
    SlSyncC st n found (L.wr s b v) := by
  have ec := h.curW_wr hb hba v
  have etr := h.trap_wr hb hba v
  refine ⟨?_, fun hS => C.arm fun h' => hS (etr.2 h')⟩
  intro t f et ef hf hn
  rw [cur_thread_ok] at et
  have e : t = L.curW s := by rw [← ec]; exact (ok_inj_ff et).symm
  subst e
  have ef' : obj.Tcb.flags st (L.curW s) s = ok f := by rw [← h.flags_wr hb hba v]; exact ef
  obtain ⟨rp, ep⟩ := found
  exact h.replyCaps_wr hb hba v (C.fd _ _ (cur_thread_ok (L := L) s) ef' hf hn)

/-- **The lock facts `SlEntL` are kept by a user-word write** at a bundle state, given the
glue's locks are (`hlk` [P]). -/
theorem SlJAt.entL_wr {K : KLayout} {s : S} (h : SlJAt (L := L) K s) {b : U64} (hb : b ∈ K.user)
    (hba : Aligned b) (v : U64) {Locks : S → U64 → Prop} {found : U64 × U64}
    (hl : Locks (L.wr s b v) = Locks s) (E : SlEntL (st := st) K Locks found s) :
    SlEntL (st := st) K Locks found (L.wr s b v) := by
  have etr := h.trap_wr hb hba v
  have efh := h.fh_wr hb hba v
  refine ⟨fun hS hE => ?_, fun hS => ?_⟩
  · rw [efh] at hE ⊢; rw [hl]; exact E.lep (etr.1 hS) hE
  · rw [hl]; exact E.lrp fun h' => hS (etr.2 h')

end

/-! ## The canonical `Q` -/

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Locks : S → U64 → Prop}
variable {A : Type}
variable {n : I64} {found : U64 × U64} {Cs Ω Sg Ac : Set U64}

variable (st) in
/-- **The canonical extra precondition of the syscall local path**: the entry facts it reads
(`SlPreB`, the lock facts `SlEntL` [P], fl4-sync's contract `SlSyncC` [P], `SlAccR` [P]). -/
def SlQ (ar : machine.Arch A) (Locks : S → U64 → Prop) (n : I64) (found : U64 × U64)
    (Cs Ω Sg Ac : Set U64) (K : KLayout) (m : U64 → U64) (s : S) : Prop :=
  SlPreB (st := st) ar K Locks m n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
      K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s ∧
    SlEntL (st := st) K Locks found s ∧ SlSyncC st n found s ∧ SlAccR (st := st) ar K Locks found s

/-- **`hQ` for `SlQ`** from the two frame premises left (`hPBw` [J], `hArw` [P]) and the locks
(`hlk` [P]); `SlEntL` and `SlSyncC` by `SlJAt.entL_wr` / `SlJAt.syncC_wr`. -/
theorem slQ_wr (ar : machine.Arch A)
    (hPBw : ∀ K m s b v, SlJAt (L := L) K s →
      SlPreB (st := st) ar K Locks m n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
        K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s → b ∈ K.user → Aligned b →
      SlPreB (st := st) ar K Locks m n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
        K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits (L.wr s b v))
    (hArw : ∀ K s b v, SlJAt (L := L) K s → SlAccR (st := st) ar K Locks found s → b ∈ K.user →
      Aligned b → SlAccR (st := st) ar K Locks found (L.wr s b v))
    (hlk : ∀ K s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s) :
    ∀ K m s b v, SlJAt (L := L) K s → SlQ st ar Locks n found Cs Ω Sg Ac K m s → b ∈ K.user →
      Aligned b → SlQ st ar Locks n found Cs Ω Sg Ac K m (L.wr s b v) :=
  fun K m s b v hJ q hb hba =>
    ⟨hPBw K m s b v hJ q.1 hb hba, hJ.entL_wr hb hba v (hlk K s b v hJ hb hba) q.2.1,
      hJ.syncC_wr hb hba v q.2.2.1, hArw K s b v hJ q.2.2.2 hb hba⟩

/-- **The syscall local path with the canonical `Q`** (`sl_pathsKF` at `Q := SlQ`): `hPE`,
`hEl`, `hC`, `hAr` are projections, `hQ` is `slQ_wr`. Premises: `hPBw` [J], `hArw` [P],
`hlk` [P], `hpz`, and `hSt`, `hA`, `hm`, `a0` as before. -/
noncomputable def sl_pathsKC (ar : machine.Arch A) (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar)
    (hm : Fl4Proofs.P2.E2E.MasksWr st) (a0 : A)
    (hPBw : ∀ K m s b v, SlJAt (L := L) K s →
      SlPreB (st := st) ar K Locks m n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
        K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s → b ∈ K.user → Aligned b →
      SlPreB (st := st) ar K Locks m n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
        K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits (L.wr s b v))
    (hArw : ∀ K s b v, SlJAt (L := L) K s → SlAccR (st := st) ar K Locks found s → b ∈ K.user →
      Aligned b → SlAccR (st := st) ar K Locks found (L.wr s b v))
    (hlk : ∀ K s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s)
    (hpz : ∀ K m, ∃ p : SProg Bool, IsProg (slBody S n found) p ∧ NoZero p ∧
      Fl4Proofs.P2.E2E.ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user)
        (fun s => SlJAt (L := L) K s ∧ SlQ st ar Locks n found Cs Ω Sg Ac K m s)
        (SlRS (st := st) K Locks)) :
    Fl4Proofs.P2.E2E.Paths Unit :=
  sl_pathsKF (Locks := Locks) ar hSt hA hm a0 (SlQ st ar Locks n found Cs Ω Sg Ac)
    (fun _ _ _ _ q => q.1) (fun _ _ _ _ q => q.2.1) (fun _ _ _ _ q => q.2.2.1) (fun _ _ _ _ q => q.2.2.2)
    (slQ_wr ar hPBw hArw hlk) hlk hpz

/-- **`StartAt` for `sl_pathsKC`**. -/
theorem sl_pathsKC_startAt (ar : machine.Arch A) (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar)
    (hm : Fl4Proofs.P2.E2E.MasksWr st) (a0 : A)
    (hPBw : ∀ K m s b v, SlJAt (L := L) K s →
      SlPreB (st := st) ar K Locks m n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
        K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s → b ∈ K.user → Aligned b →
      SlPreB (st := st) ar K Locks m n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
        K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits (L.wr s b v))
    (hArw : ∀ K s b v, SlJAt (L := L) K s → SlAccR (st := st) ar K Locks found s → b ∈ K.user →
      Aligned b → SlAccR (st := st) ar K Locks found (L.wr s b v))
    (hlk : ∀ K s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s)
    (hpz : ∀ K m, ∃ p : SProg Bool, IsProg (slBody S n found) p ∧ NoZero p ∧
      Fl4Proofs.P2.E2E.ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user)
        (fun s => SlJAt (L := L) K s ∧ SlQ st ar Locks n found Cs Ω Sg Ac K m s)
        (SlRS (st := st) K Locks))
    (K : KLayout) (m : U64 → U64) (hK : RegionOK K) (hU : Fl4Proofs.P2.E2E.UserOK K)
    {σ : S} (a : A) (hJ : SlJAt (L := L) K σ) (hq : SlQ st ar Locks n found Cs Ω Sg Ac K m σ)
    {c : U64} {hs : U64 → Prop} (hc : L.cpu σ = c) (hl : Locks σ = hs) {μ : U64 → U64}
    (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = μ x) :
    Fl4Proofs.P2.E2E.StartAt
      (sl_pathsKC (Locks := Locks) ar hSt hA hm a0 hPBw hArw hlk hpz () K m hK hU) c hs μ
      ((sl_pathsKC (Locks := Locks) ar hSt hA hm a0 hPBw hArw hlk hpz () K m hK hU).body σ a) :=
  sl_pathsKF_startAt ar hSt hA hm a0 _ _ _ _ _ (slQ_wr ar hPBw hArw hlk) hlk hpz K m hK hU a hJ hq hc hl hμ

end

end Fl4Proofs.P2.PathObl
