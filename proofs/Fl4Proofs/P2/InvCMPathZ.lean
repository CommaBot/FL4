/-
# P2 (line slhuf, gen 14): the Copy / Mint local path without `hnul` (`inv_pathsKCM7`)

With fl4-core's raw-zero target check (`plan_with`: the target's first word `= 0`), the target's word is a Null /
Frame encoding by the plan (`CMDestZ`, P2/InvCMAccZ.lean, from `plan_with_cmFZ` by `cmDestZ_of`, P2/InvCMDZ.lean), so
InvCMPath8's [J] `hnul` is gone: `invCMBlkUW3_ofZ` / `invCMBlkGdUW3_ofZ` (on `cmAccGZ` / `cmAccGdZ`), `cmSC_ofZ`, **`inv_pathsKCM6 ar hA number
p hm hIw hlk`** ([P] `hm`, [J] `hIw`, [P] `hlk`), **`inv_pathsKCM7 … hm hCs hlk`** ([P] `hm`, `hCs`, `hlk`).
-/
import Fl4Proofs.P2.InvCMPath8
import Fl4Proofs.P2.InvCMAccZ
import Fl4Proofs.P2.InvCMDZ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField NullOrFrame TcbSlot
  oAFFINITY)

section blk
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- (slhuf gen 14; gen 12's `invCMBlkUW3_of8` without `hnul`) **The Copy / Mint decode block on `guard st (InvCMRS s) (InvCMWS s)`** at `Pre := SlJAt K ∧
InvQCMW`, from [J] `hcdt`, `hz`, `hbuf`, `hbufS` (the target's zero word from the plan, `cmDestZ_of`). -/
theorem invCMBlkUW3_ofZ {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {Cs Ω Sg Ac : Set U64}
    {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayout} {μ : U64 → U64}
    (hcdt : InvCdtJ st K (fun s => SlJAt (L := L) K s ∧ InvQCMW st Cs Ω Sg Ac Locks p K μ s))
    (hz : ∀ s, SlJAt (L := L) K s → (0#u64) ∉ K.slots)
    (hbuf : ∀ s, SlJAt (L := L) K s → InvQCMW st Cs Ω Sg Ac Locks p K μ s → InvBufJ8 st K s)
    (hbufS : ∀ s, SlJAt (L := L) K s → InvQCMW st Cs Ω Sg Ac Locks p K μ s → InvBufSJ8 st K s)
:
    InvBlkUW3 st ar p K Locks (fun s => SlJAt (L := L) K s ∧ InvQCMW st Cs Ω Sg Ac Locks p K μ s) := by
  intro s a info nx s1 s2 a1 buf length cap hE emi C hb hl hcap y hy
  have hqf := hE.2
  have PE := hqf.1.1.1
  have hlb := hqf.1.2.2.1 (L.curW s) info (cur_thread_ok s) emi
  have E := cmEnt_ofW (P := fun s => SlJAt (L := L) K s ∧ InvQCMW st Cs Ω Sg Ac Locks p K μ s) hE hqf hcdt
    (hz s hE.1)
  have hsl := cmSl_ofW hqf
  have hbC : buf ≠ 0#u64 → ∀ i : U64, i.val < 128 →
      UserW K (core.num.U64.wrapping_add buf (core.num.U64.wrapping_mul i 8#u64)) :=
    hbufS s hE.1 hqf buf (by rw [← lib_prefix hA PE C false]; exact hb)
  obtain ⟨hdec, hrep⟩ := cmAccGZ hA PE E hsl (cmDestZ_of hqf) hbC (hbuf s hE.1 hqf) hlb C hcap hy
  refine ⟨hdec, fun z hz' => ?_⟩
  have : GRd (guard st (InvCMRS (st := st) K Locks s) (InvCMWS (st := st) K Locks s)) st
      (IoRS (st := st) K Locks s) := grd_sub (fun _ hy => ioRS_cm hy)
  obtain ⟨h1, h2⟩ := cmFin8 (gS := (guard st (InvCMRS (st := st) K Locks s) (InvCMWS (st := st) K Locks s))) hA PE
    (PE.ioWr.mono (fun _ h => ioWS_cm h)) (SWr.of_W (ioWS_cm PE.stw.2)) E hsl (hbuf s hE.1 hqf) hlb C hcap hy hz'
  exact ⟨hrep z hz', h1, h2⟩

/-- (slhuf gen 14; as `invCMBlkGdUW3_of8`) **The Copy / Mint decode block on `gd st (InvCMRS s) (PWs …)`** (for `move`), as
`invCMBlkUW3_ofZ`. -/
theorem invCMBlkGdUW3_ofZ {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {Cs Ω Sg Ac : Set U64}
    {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayout} {μ : U64 → U64}
    (hcdt : InvCdtJ st K (fun s => SlJAt (L := L) K s ∧ InvQCMW st Cs Ω Sg Ac Locks p K μ s))
    (hz : ∀ s, SlJAt (L := L) K s → (0#u64) ∉ K.slots)
    (hbuf : ∀ s, SlJAt (L := L) K s → InvQCMW st Cs Ω Sg Ac Locks p K μ s → InvBufJ8 st K s)
    (hbufS : ∀ s, SlJAt (L := L) K s → InvQCMW st Cs Ω Sg Ac Locks p K μ s → InvBufSJ8 st K s)
:
    InvBlkGdUW3 st ar p K Locks (fun s => SlJAt (L := L) K s ∧ InvQCMW st Cs Ω Sg Ac Locks p K μ s) := by
  intro s a info nx s1 s2 a1 buf length cap hE emi C hb hl hcap y hy
  have hqf := hE.2
  have PE := hqf.1.1.1
  have hK := hE.1.regionOK
  have hU := hE.1.userOK
  have hLA := hE.1.ioLayA
  have hlb := hqf.1.2.2.1 (L.curW s) info (cur_thread_ok s) emi
  have E := cmEnt_ofW (P := fun s => SlJAt (L := L) K s ∧ InvQCMW st Cs Ω Sg Ac Locks p K μ s) hE hqf hcdt
    (hz s hE.1)
  have hsl := cmSl_ofW hqf
  have hbC : buf ≠ 0#u64 → ∀ i : U64, i.val < 128 →
      UserW K (core.num.U64.wrapping_add buf (core.num.U64.wrapping_mul i 8#u64)) :=
    hbufS s hE.1 hqf buf (by rw [← lib_prefix hA PE C false]; exact hb)
  obtain ⟨hdec, hrep⟩ := cmAccGdZ hA PE hK hU hLA E hsl (cmDestZ_of hqf) hbC (hbuf s hE.1 hqf) hlb C hcap hy
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
  obtain ⟨h1, h2⟩ := cmFin8 (gS := (gd st (InvCMRS (st := st) K Locks s)
    (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s)))) hA PE hW hsw E hsl (hbuf s hE.1 hqf) hlb C hcap hy hz'
  exact ⟨hrep z hz', h1, h2⟩

/-- (slhuf gen 14; a copy of `cmSC_ofW`) **`hSC` for `Q := InvQCMW`** (no premise): the invoked slot is a capability slot holding a
CNode cap. -/
theorem cmSC_ofZ {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} :
    InvSlotCNK st p (InvQCMW st Cs Ω Sg Ac Locks p) := by
  intro K μ s h
  obtain ⟨cp, cr, cg, cgb, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcap, hsK, -⟩ := cm_coreW h.2
  exact ⟨hsK, cp, cr, cg, cgb, hcap⟩

end blk

end Fl4Proofs.P2.PathObl
