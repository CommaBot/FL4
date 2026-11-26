/-
# P2 (line slhuf, gen 12): the Copy / Mint local path with the decode block proved (`inv_pathsKCM3`)

`inv_pathsKCM2` (gen 10, P2/InvCMOnce.lean) at the canonical `Q := InvQCMF` (`InvQCM ∧ InvLk ∧ InvEx`, all from
`localinv.plan` at the entry: `invQCM_intro`, `invLk_of_plan`, `invEx_of_plan`), with
* `hacc` from `invUAccW_of3` + **`invCMBlkUW3_of`** (the decode block: `cmAccG` / `cmFin`, P2/InvCMAcc.lean,
  P2/InvCMFin.lean, from `cmEnt_of`, P2/InvCMCore.lean);
* `hmv` from `invMoveW_ofU3` + **`invCMBlkGdUW3_of`** (`cmAccGd` / `cmFin` on `gd st (InvCMRS s) (PWs …)`: the
  destination's `CAP0` write Null → Frame is stpost's `PWs` slot disjunct; no Untyped source occurs, since
  `plan_with` admits only a non-EPT Frame source cap — gen 11's finding 1 is closed by the plan, not by a cut);
* `hSeen` / `hps` / `hSC` from `cm_core` (`cmSeen_of`, `cmPs_of`, `cmSC_of`);
* `hdo` (`InvCMDecOnceW`) from `invCMDecOnceW_of` (P2/InvCMDecOnce.lean) + `invCMTailW_of` (P2/InvCMTail.lean).

Premises of **`inv_pathsKCM3`**: `hA`; [P] `hm`; [J] `hbuf : InvBufJ` (receiver-side IPC buffer words, for the error
reply); [J] `hbufS : InvBufSJ` (sender-side IPC buffer words, for `copied_cap`'s `buf + 40` / `buf + 48`); [J]
`hnul : InvNulJ` (a slot whose first word decodes to `Null` holds a Null / Frame encoding); [J] `huf`. No [W].
`hz` (`0 ∉ K.slots`) and `hcdt` (`InvCdtJ`) come from `SlJAt` (hpzg gen 8, P2/InvLay.lean: `hz_of`, `invCdtJ_of`).
-/
import Fl4Proofs.P2.InvCMBlk
import Fl4Proofs.P2.InvCMCore
import Fl4Proofs.P2.InvCMTail
import Fl4Proofs.P2.InvCMAcc
import Fl4Proofs.P2.InvLay
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField NullOrFrame TcbSlot
  oAFFINITY)

section blk
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- (slhuf gen 12) **The Copy / Mint decode block on `guard st (InvCMRS s) (InvCMWS s)`** at `Pre := SlJAt K ∧
InvQCMF`, from [J] `hcdt`, `hz`, `hbuf`, `hbufS`, `hnul`. -/
theorem invCMBlkUW3_of {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {Cs Ω Sg Ac : Set U64}
    {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayout} {μ : U64 → U64}
    (hcdt : InvCdtJ st K (fun s => SlJAt (L := L) K s ∧ InvQCMF st Cs Ω Sg Ac Locks p K μ s))
    (hz : ∀ s, SlJAt (L := L) K s → (0#u64) ∉ K.slots)
    (hbuf : ∀ s, SlJAt (L := L) K s → InvQCMF st Cs Ω Sg Ac Locks p K μ s → InvBufJ st K s)
    (hbufS : ∀ s, SlJAt (L := L) K s → InvQCMF st Cs Ω Sg Ac Locks p K μ s → InvBufSJ st K s)
    (hnul : ∀ s, SlJAt (L := L) K s → InvQCMF st Cs Ω Sg Ac Locks p K μ s → InvNulJ st K s) :
    InvBlkUW3 st ar p K Locks (fun s => SlJAt (L := L) K s ∧ InvQCMF st Cs Ω Sg Ac Locks p K μ s) := by
  intro s a info nx s1 s2 a1 buf length cap hE emi C hb hl hcap y hy
  have hqf := hE.2
  have PE := hqf.1.1.1
  have hlb := hqf.1.2.2.1 (L.curW s) info (cur_thread_ok s) emi
  have E := cmEnt_of (P := fun s => SlJAt (L := L) K s ∧ InvQCMF st Cs Ω Sg Ac Locks p K μ s) hE hqf hcdt
    (hz s hE.1)
  have hsl := cmSl_of hqf
  have hbC : buf ≠ 0#u64 → ∀ i : U64, i.val < 512 →
      UserW K (core.num.U64.wrapping_add buf (core.num.U64.wrapping_mul i 8#u64)) :=
    hbufS s hE.1 hqf buf (by rw [← lib_prefix hA PE C false]; exact hb)
  obtain ⟨hdec, hrep⟩ := cmAccG hA PE E hsl (hnul s hE.1 hqf) hbC (hbuf s hE.1 hqf) hlb C hcap hy
  refine ⟨hdec, fun z hz' => ?_⟩
  have : GRd (guard st (InvCMRS (st := st) K Locks s) (InvCMWS (st := st) K Locks s)) st
      (IoRS (st := st) K Locks s) := grd_sub (fun _ hy => ioRS_cm hy)
  obtain ⟨h1, h2⟩ := cmFin (gS := (guard st (InvCMRS (st := st) K Locks s) (InvCMWS (st := st) K Locks s))) hA PE
    (PE.ioWr.mono (fun _ h => ioWS_cm h)) (SWr.of_W (ioWS_cm PE.stw.2)) E hsl (hbuf s hE.1 hqf) hlb C hcap hy hz'
  exact ⟨hrep z hz', h1, h2⟩

/-- (slhuf gen 12) **The Copy / Mint decode block on `gd st (InvCMRS s) (PWs …)`** (for `move`), as
`invCMBlkUW3_of`. -/
theorem invCMBlkGdUW3_of {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {Cs Ω Sg Ac : Set U64}
    {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayout} {μ : U64 → U64}
    (hcdt : InvCdtJ st K (fun s => SlJAt (L := L) K s ∧ InvQCMF st Cs Ω Sg Ac Locks p K μ s))
    (hz : ∀ s, SlJAt (L := L) K s → (0#u64) ∉ K.slots)
    (hbuf : ∀ s, SlJAt (L := L) K s → InvQCMF st Cs Ω Sg Ac Locks p K μ s → InvBufJ st K s)
    (hbufS : ∀ s, SlJAt (L := L) K s → InvQCMF st Cs Ω Sg Ac Locks p K μ s → InvBufSJ st K s)
    (hnul : ∀ s, SlJAt (L := L) K s → InvQCMF st Cs Ω Sg Ac Locks p K μ s → InvNulJ st K s) :
    InvBlkGdUW3 st ar p K Locks (fun s => SlJAt (L := L) K s ∧ InvQCMF st Cs Ω Sg Ac Locks p K μ s) := by
  intro s a info nx s1 s2 a1 buf length cap hE emi C hb hl hcap y hy
  have hqf := hE.2
  have PE := hqf.1.1.1
  have hK := hE.1.regionOK
  have hU := hE.1.userOK
  have hLA := hE.1.ioLayA
  have hlb := hqf.1.2.2.1 (L.curW s) info (cur_thread_ok s) emi
  have E := cmEnt_of (P := fun s => SlJAt (L := L) K s ∧ InvQCMF st Cs Ω Sg Ac Locks p K μ s) hE hqf hcdt
    (hz s hE.1)
  have hsl := cmSl_of hqf
  have hbC : buf ≠ 0#u64 → ∀ i : U64, i.val < 512 →
      UserW K (core.num.U64.wrapping_add buf (core.num.U64.wrapping_mul i 8#u64)) :=
    hbufS s hE.1 hqf buf (by rw [← lib_prefix hA PE C false]; exact hb)
  obtain ⟨hdec, hrep⟩ := cmAccGd hA PE hK hU hLA E hsl (hnul s hE.1 hqf) hbC (hbuf s hE.1 hqf) hlb C hcap hy
  refine ⟨hdec, fun z hz' => ?_⟩
  have hW := mvWrS PE hK hLA (c := L.cpu s) (lk := Locks s) (m := L.mem s)
  have hS0 : OwnMap.Safe0 (L.cpu s) (Locks s) (L.mem s) (L.curW s) := by
    refine ⟨?_, fun hq => absurd hq ?_⟩
    · rw [← OwnMap.affA_fld]; exact PE.curAff
    · rw [← OwnMap.stA_fld]; exact nq_run PE.run
  have hsw : SWr (gd st (InvCMRS (st := st) K Locks s) (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s))) st
      (L.curW s) sched.TS_RUNNING :=
    fun X => OwnMap.gds_write_state (PE.hT _ PE.cT) hS0 (fun hq => absurd hq (nq_run (Or.inr rfl)))
  have : GRd (gd st (InvCMRS (st := st) K Locks s) (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s))) st
      (IoRS (st := st) K Locks s) := gdr_sub (fun _ hy => ioRS_cm hy)
  obtain ⟨h1, h2⟩ := cmFin (gS := (gd st (InvCMRS (st := st) K Locks s)
    (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s)))) hA PE hW hsw E hsl (hbuf s hE.1 hqf) hlb C hcap hy hz'
  exact ⟨hrep z hz', h1, h2⟩

/-- (slhuf gen 12) **`hSC` for `Q := InvQCMF`** (no premise): the invoked slot is a capability slot holding a
CNode cap. -/
theorem cmSC_of {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} :
    InvSlotCNK st p (InvQCMF st Cs Ω Sg Ac Locks p) := by
  intro K μ s h
  obtain ⟨cp, cr, cg, cgb, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcap, hsK, -⟩ := cm_core h.2
  exact ⟨hsK, cp, cr, cg, cgb, hcap⟩

end blk

section paths
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}
variable {A : Type}

/-- (slhuf gen 12) **The Copy / Mint local path, decode block and `move` proved** (`Q := InvQCMF`; module
docstring). Premises: `hA`; [P] `hm`; [J] `hbuf`, `hbufS`, `hnul`, `huf` (`hz` / `hcdt` from `SlJAt` by hpzg's
`hz_of` / `invCdtJ_of`). -/
noncomputable def inv_pathsKCM3 (ar : machine.Arch A) (hA : P0.ArchTotal ar) (number : I64) (p : localinv.Plan)
    (hm : E2E.MasksWr st)
    (hbuf : ∀ K m s, SlJAt (L := L) K s → InvQCMF st Cs Ω Sg Ac Locks p K m s → InvBufJ st K s)
    (hbufS : ∀ K m s, SlJAt (L := L) K s → InvQCMF st Cs Ω Sg Ac Locks p K m s → InvBufSJ st K s)
    (hnul : ∀ K m s, SlJAt (L := L) K s → InvQCMF st Cs Ω Sg Ac Locks p K m s → InvNulJ st K s)
    (huf : ∀ K m s b v, SlJAt (L := L) K s → InvQCMF st Cs Ω Sg Ac Locks p K m s → b ∈ K.user → Aligned b →
      (SlJAt (L := L) K (L.wr s b v) ∧ InvQCMF st Cs Ω Sg Ac Locks p K m (L.wr s b v)) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s) :
    E2E.Paths Unit :=
  have hz : ∀ K s, SlJAt (L := L) K s → (0#u64) ∉ K.slots := hz_of
  have hcdt : ∀ K m, InvCdtJ st K (fun s => SlJAt (L := L) K s ∧ InvQCMF st Cs Ω Sg Ac Locks p K m s) :=
    fun _ _ => invCdtJ_of (fun _ h => h.1)
  inv_pathsKCM2 ar hA number p hm (InvQCMF st Cs Ω Sg Ac Locks p) (fun _ _ _ _ hq => hq.1.1.1)
    (fun K m => invUAccW_of3 hA (fun _ h => h.2.1.1.1)
      (fun s h => cmSeen_of (fun K _ s hJ _ => hz K s hJ) K m s h.1 h.2)
      (fun s h => cmPs_of K m s h.1 h.2) (invCMBlkUW3_of hA (hcdt K m) (hz K) (hbuf K m) (hbufS K m) (hnul K m)))
    (cmSeen_of (fun K _ s hJ _ => hz K s hJ)) cmPs_of
    (fun K m => invMoveW_ofU3 hA (fun _ h => h.1.regionOK) (fun _ h => h.1.userOK) (fun _ h => h.1.ioLayA)
      (fun _ h => h.2.1.1.1) (fun s h => cmSeen_of (fun K _ s hJ _ => hz K s hJ) K m s h.1 h.2)
      (fun s h => cmPs_of K m s h.1 h.2) (fun _ h => h.2.1.1.2)
      (inv_isProgOn (Locks := Locks) (m0 := m) hA (fun _ h => h.2.1.1.1) (cmSC_of K m) (inv_isProg S number p))
      (invCMBlkGdUW3_of hA (hcdt K m) (hz K) (hbuf K m) (hbufS K m) (hnul K m)))
    huf cmSC_of
    (fun K m => invCMDecOnceW_of hA (fun _ h => h.2.1.1.1) (fun _ h => h.2.1.2.2.1)
      (fun s h => cmEnt_of h h.2 (hcdt K m) (hz K s h.1)) (fun _ h => cmSl_of h.2)
      (invCMTailW_of hA (fun _ h => h.2.1.1.1) (fun _ h => h.2.1.2.2.1)
        (fun s h => cmEnt_of h h.2 (hcdt K m) (hz K s h.1)) (fun _ h => cmSl_of h.2)
        (fun s h => hbuf K m s h.1 h.2)))

end paths

end Fl4Proofs.P2.PathObl
