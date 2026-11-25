/-
# P2 (line slhuf): the syscall local path's user-write premise `huf`

`sl_pathsK` (P2/SlJLay.lean) and its `StartAt` forms (`sl_pathsK_startAt`, SlJStab's
`sl_pathsK_startAt_stab`, SlJLocMv's `sl_pathsK_startAt_stab'`) take `huf` [J]
(`PathSide.user_free`): a write of any aligned user word `b ∈ K.user` with any value keeps
`Pre = SlJAt K ∧ Q K m`, the glue's `Locks`, and the read / write / declined sets
`SlRS`, `SlWS`, `SlDS`. slj left it open because `SlJAt` contains `JAtZ`, which a user write
breaks unless the spec state σ is moved too.

## What is proved here
* `SlJAt.userWr`: `SlJAt K s → b ∈ K.user → SlJAt K (L.wr s b v)`. `SlJAt`'s spec state is
  existential, so it is moved by the matching user-memory store (`Endp.setUm`), and P3's
  `JAtZ.userWrB` (P3/UserWrB.lean, new) keeps `JAtZ` at the same ghosts for **any** word of
  `Zx.B` (the side facts `JAtZ.userWrJ` asks are derived from `JAtZ`: `JAtZ.bWordOK`). The
  layout is kept (`ksb_wr`), the core set and the scheduler action too (`setUm` changes the
  machine state only).
* `SlJAt.slDS_wr`: `SlDS` is kept: the current thread word (node `CUR_THREAD`) is no user
  word (`SlJAtZ.userNode`), the node addresses depend on `ksb` / `cpu` only.
* `SlJAt.slRWS_wr`: `SlRS` / `SlWS` are kept, given the glue's locks kept: `own K` reads no
  user word (`E2E.ownDep`, `RegionOK` / `UserOK` of `K` from the bundle, `SlJAtZ.okRU`).
* `sl_huf`: `huf` in `sl_pathsK`'s exact form from the two remaining premises below.
* `sl_pathsKU`, `sl_pathsKU_startAt`: `sl_pathsK` / `sl_pathsK_startAt` with `huf` replaced.
  The `stab` forms take `sl_huf …` for their `huf` argument as is.
* `LocUserB`, `locKeepSt_userB`: SlJLocMv's user step (`LocUser`) without its two side facts
  (now derived), `LocKeepSt` for it.

## Remaining premises (replacing `huf` [J])
* `hQ` [J]: the path's extra precondition `Q` (the caller's choice; the entry facts behind
  `hPE` / `hEr` / `hHr` / `hAr`) survives a user-word write at a `SlJAt` state. Nothing about
  `JAtZ` is left in it.
* `hlk` [P]: the glue's lock predicate `Locks` is not changed by a user-word write (as
  `TCB_SetTimer`'s `hlk`, P2/FootTimerSetLP.lean).
-/
import Fl4Proofs.P2.SlJLocMv
import Fl4Proofs.P3.UserWrB
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap Fl4Proofs.P0.Consts
open Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P3.Vs

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **The bundle survives a user-word write** (module docstring), σ moved by the matching
user-memory store (`JAtZ.userWrB`). -/
theorem SlJAt.userWr {K : KLayout} {s : S} (h : SlJAt (L := L) K s) {b : U64} (hb : b ∈ K.user) (v : U64) :
    SlJAt (L := L) K (L.wr s b v) := by
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := h
  have hb' := hb
  rw [B.user] at hb'
  obtain ⟨wp, hwB, rfl⟩ := hb'
  exact ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', _,
    { j := B.j.userWrB hwB v
      lay := by rw [L.ksb_wr]; exact B.lay
      cs := B.cs
      res := B.res }⟩

/-- **`SlDS` is kept by a user-word write** at a bundle state (module docstring). -/
theorem SlJAt.slDS_wr {K : KLayout} {s : S} (h : SlJAt (L := L) K s) {b : U64} (hb : b ∈ K.user)
    (hba : Aligned b) (v : U64) : SlDS (L := L) (L.wr s b v) = SlDS (L := L) s := by
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := h
  have hN : NodePlaced st (Heap.tcbs K.heap) s (L.cpu s) := TInv.nodes B.j.blk _ B.j.kern.cpuCs
  have hv := nodeAt_val hN (off := layout.node.CUR_THREAD) (by rw [curth_val]; omega)
  rw [curth_val] at hv
  simp only [LawfulStore.nodeBase, B.ksb] at hv
  have ec : L.curW (L.wr s b v) = L.curW s := by
    unfold LawfulStore.curW
    rw [nodeAt_wr, LawfulStore.cpu_wr]
    refine mem_wr_ne' hba (nodeAt_aligned hN (by rw [curth_val]; omega) (by rw [curth_val])) fun e => ?_
    have hbv : b.val = K.ksb.val + 13568 + (L.cpu s).val * 4288 := by rw [e]; omega
    exact B.userNode b hb (L.cpu s) ⟨B.cpu, by omega, by omega⟩
  funext w
  simp only [SlDS, ec, nodeAt_wr, LawfulStore.cpu_wr]

/-- **`SlRS` / `SlWS` are kept by a user-word write** at a bundle state, the locks kept
(module docstring). -/
theorem SlJAt.slRWS_wr {K : KLayout} {s : S} (h : SlJAt (L := L) K s) {b : U64} (hb : b ∈ K.user)
    (hba : Aligned b) (v : U64) (Locks : S → U64 → Prop) (hlk : Locks (L.wr s b v) = Locks s) :
    SlRS (st := st) K Locks (L.wr s b v) = SlRS (st := st) K Locks s ∧
      SlWS (st := st) K Locks (L.wr s b v) = SlWS (st := st) K Locks s := by
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := h
  obtain ⟨hK, hU⟩ := B.okRU
  have eo : own K (L.mem (L.wr s b v)) = own K (L.mem s) :=
    E2E.ownDep hK hU _ _ (fun x hx hxu => mem_wr_ne' hba hx (fun e => hxu (e ▸ hb)))
  refine ⟨?_, ?_⟩ <;> funext w <;> simp only [SlRS, SlWS, RPerm, WPerm, GateOnly, eo, hlk, LawfulStore.cpu_wr]

/-- **`huf` in `sl_pathsK`'s form** (module docstring), from `hQ` [J] (`Q` survives a
user-word write at a bundle state) and `hlk` [P] (the glue's locks are not changed by a
user-word write). -/
theorem sl_huf (Locks : S → U64 → Prop) (Q : KLayout → (U64 → U64) → S → Prop)
    (hQ : ∀ K m s b v, SlJAt (L := L) K s → Q K m s → b ∈ K.user → Aligned b → Q K m (L.wr s b v))
    (hlk : ∀ K s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s) :
    ∀ K m s b v, SlJAt (L := L) K s → Q K m s → b ∈ K.user → Aligned b →
      (SlJAt (L := L) K (L.wr s b v) ∧ Q K m (L.wr s b v)) ∧ Locks (L.wr s b v) = Locks s ∧
        SlRS (st := st) K Locks (L.wr s b v) = SlRS (st := st) K Locks s ∧
        SlWS (st := st) K Locks (L.wr s b v) = SlWS (st := st) K Locks s ∧
        SlDS (L := L) (L.wr s b v) = SlDS (L := L) s := by
  intro K m s b v hJ hq hb hba
  have hl := hlk K s b v hJ hb hba
  have hRW := hJ.slRWS_wr hb hba v Locks hl
  exact ⟨⟨hJ.userWr hb v, hQ K m s b v hJ hq hb hba⟩, hl, hRW.1, hRW.2, hJ.slDS_wr hb hba v⟩

end

/-! ## The local path with `huf` replaced -/

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Locks : S → U64 → Prop}
variable {A : Type}
variable {n : I64} {found : U64 × U64} {Cs Ω Sg Ac : Set U64}

/-- **`sl_pathsK` with `huf` replaced by `hQ` [J] and `hlk` [P]** (`sl_huf`). Other
premises as `sl_pathsK`. -/
noncomputable def sl_pathsKU (ar : machine.Arch A) (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar)
    (hm : Fl4Proofs.P2.E2E.MasksWr st) (a0 : A) (Q : KLayout → (U64 → U64) → S → Prop)
    (hPE : ∀ K m s, SlJAt (L := L) K s → Q K m s →
      SlPreB (st := st) ar K Locks m n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
        K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s)
    (hEr : ∀ K m s, SlJAt (L := L) K s → Q K m s → SlEntR (st := st) K Locks found s)
    (hHr : ∀ K m s, SlJAt (L := L) K s → Q K m s → SlHereR (st := st) K found s)
    (hAr : ∀ K m s, SlJAt (L := L) K s → Q K m s → SlAccR (st := st) ar K Locks found s)
    (hQ : ∀ K m s b v, SlJAt (L := L) K s → Q K m s → b ∈ K.user → Aligned b → Q K m (L.wr s b v))
    (hlk : ∀ K s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s)
    (hpz : ∀ K m, ∃ p : SProg Bool, IsProg (slBody S n found) p ∧ NoZero p ∧
      Fl4Proofs.P2.E2E.ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user)
        (fun s => SlJAt (L := L) K s ∧ Q K m s) (SlRS (st := st) K Locks)) :
    Fl4Proofs.P2.E2E.Paths Unit :=
  sl_pathsK (Locks := Locks) ar hSt hA hm a0 Q hPE hEr hHr hAr (sl_huf Locks Q hQ hlk) hpz

/-- **`StartAt` for `sl_pathsKU`** (`sl_pathsK_startAt` with `huf` replaced). -/
theorem sl_pathsKU_startAt (ar : machine.Arch A) (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar)
    (hm : Fl4Proofs.P2.E2E.MasksWr st) (a0 : A) (Q : KLayout → (U64 → U64) → S → Prop)
    (hPE : ∀ K m s, SlJAt (L := L) K s → Q K m s →
      SlPreB (st := st) ar K Locks m n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
        K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s)
    (hEr : ∀ K m s, SlJAt (L := L) K s → Q K m s → SlEntR (st := st) K Locks found s)
    (hHr : ∀ K m s, SlJAt (L := L) K s → Q K m s → SlHereR (st := st) K found s)
    (hAr : ∀ K m s, SlJAt (L := L) K s → Q K m s → SlAccR (st := st) ar K Locks found s)
    (hQ : ∀ K m s b v, SlJAt (L := L) K s → Q K m s → b ∈ K.user → Aligned b → Q K m (L.wr s b v))
    (hlk : ∀ K s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s)
    (hpz : ∀ K m, ∃ p : SProg Bool, IsProg (slBody S n found) p ∧ NoZero p ∧
      Fl4Proofs.P2.E2E.ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user)
        (fun s => SlJAt (L := L) K s ∧ Q K m s) (SlRS (st := st) K Locks))
    (K : KLayout) (m : U64 → U64) (hK : RegionOK K) (hU : Fl4Proofs.P2.E2E.UserOK K)
    {σ : S} (a : A) (hJ : SlJAt (L := L) K σ) (hq : Q K m σ) {c : U64} {hs : U64 → Prop}
    (hc : L.cpu σ = c) (hl : Locks σ = hs) {μ : U64 → U64}
    (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = μ x) :
    Fl4Proofs.P2.E2E.StartAt
      (sl_pathsKU (Locks := Locks) ar hSt hA hm a0 Q hPE hEr hHr hAr hQ hlk hpz () K m hK hU) c hs μ
      ((sl_pathsKU (Locks := Locks) ar hSt hA hm a0 Q hPE hEr hHr hAr hQ hlk hpz () K m hK hU).body σ a) :=
  sl_pathsK_startAt ar hSt hA hm a0 Q hPE hEr hHr hAr (sl_huf Locks Q hQ hlk) hpz K m hK hU a hJ hq hc hl hμ

end

/-! ## SlJLocMv's user step without its side facts -/

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type}
  {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop}

/-- **A user-word write** (SlJLocMv's `LocUser` without the two side facts, which
`JAtZ.bWordOK` derives): any word of `B`, any value; the spec stores the user word. -/
def LocUserB (B : Set (U64 × Fl4Spec.Word)) (s : S) (a : A) (σ : Fl4Spec.State Unit) (s' : S) (a' : A)
    (σ' : Fl4Spec.State Unit) : Prop :=
  ∃ wp ∈ B, ∃ v : U64, s' = L.wr s wp.1 v ∧ a' = a ∧
    σ' = Fl4Proofs.P3.Endp.setUm σ (Fl4Proofs.P3.Endp.storeMem σ.machineState.underlyingMemory wp.2 v.bv)

/-- **`LocKeepSt` for every user-word write** (`locKeepSt_user` with the side facts from
`JAtZ.bWordOK`). -/
theorem locKeepSt_userB (th : TypedHeap) (B : Set (U64 × Fl4Spec.Word)) (H : Heap) (Cs : Set U64) :
    LocKeepSt (L := L) arI AR (LocUserB (L := L) B) th B H Cs := by
  intro k s a σ s' a' σ' hS ⟨wp, hwB, v, hs, ha, hσ⟩
  obtain ⟨Z, Ac, Lst, D, hth, hB, hk, J, hvx⟩ := hS
  have hwZ : wp ∈ Z.B := hB ▸ hwB
  exact locKeepSt_user th B H Cs k s a σ s' a' σ' ⟨Z, Ac, Lst, D, hth, hB, hk, J, hvx⟩
    ⟨wp, hwB, v, (J.bWordOK hwZ).1, (J.bWordOK hwZ).2, hs, ha, hσ⟩

end

end Fl4Proofs.P2.PathObl
