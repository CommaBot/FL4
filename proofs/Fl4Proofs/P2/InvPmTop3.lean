/-
# P2 (line pte, generation 13): the PageMap slot at the start fact `PmPreG` — `pdw` gone

Gen 12's `serializable_fl4_localW11PRIPmU` had `B : PmObl3` with [J] `pdw` (the plan survives a user write). It is
false at `PmPreF` states whose PML4 cap is orphaned (P2/InvPmPdw.lean) and proved at `PmPreG = PmPreF ∧ PmEx ∧ PmRoot`
(`pm_pdwG`). Here the slot is rebuilt at `PmPreG`:

* `pm_hufG` (`uf` at `PmPreG`: gen 11's `pm_huf` route with `pm_pdwG`, `pmEx_wr`, `pmRoot_wr`);
* **Finding**: gen 12's `PmBlkUW` quantifies the slot's `cap` and the `length` freely (as stpost's `InvBlkW`, which
  stpost gen 13 found false for that reason); for a `cap` the slot does not hold it is false (a `Large` frame cap
  maps through a PD entry the plan did not lock). Replaced by `PmBlkUW2` (`InvBlkW2`'s shape: the cap the accepted
  run reads from the slot and the length's computation as hypotheses), and `pm_accU_of_blkG` goes through stpost's
  `inv_acc_gen2`; `dec`, `ra`, `ro`, `isProgOn` by restriction;
* `PmObl4` = [W] `blk`, [W] `mv`, [W] `roA` (all at `PmPreG`), [P] `cs`, [P] `lk`; `pmPathsG`, `StartPmG`
  (the start fact with `PmEx`, from the plan by `pmEx_of_plan`, and `PmRoot`, not implied by the plan: runs with an
  orphaned PML4 cap are left out), `pm_hSFQG`, **`serializable_fl4_localW11PRIPmG`**.

Premises of `serializable_fl4_localW11PRIPmG` beyond `serializable_fl4_localW11PR`'s (`B : PmObl4`): [W] `blk`
(`PmBlkUW2`),
[W] `mv`, [W] `roA`, [P] `cs`, [P] `lk`. (Not named `…Pm3`: it still has [W] fields.)

No existing statement or file changed.
-/
import Fl4Proofs.P2.InvPmPdw
import Fl4Proofs.P2.InvBlk
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.E2E (Once ReadOnce StartAt SP)
open Fl4Proofs.P2.Serial (Cfg Init ArmInv NoLoc RunAll)

noncomputable section

section huf
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}

/-- **`uf` of the PageMap slot at `PmPreG`** (gen 11's `pm_huf` with `pm_pdwG`; `PmEx`, `PmRoot` kept). -/
theorem pm_hufG (hIw : PmIw st Cs Ω Sg Ac) (hlk : PmLk st Locks) :
    ∀ (j : I64 × localinv.Plan) (K : KLayoutP) m s b v, PmPreG st Cs Ω Sg Ac Locks j.2 K m s →
      b ∈ K.user → Aligned b →
      PmPreG st Cs Ω Sg Ac Locks j.2 K m (L.wr s b v) ∧
        Locks (L.wr s b v) = Locks s ∧
        PmRSU st K Locks (L.wr s b v) = PmRSU st K Locks s ∧
        PmWSU st K Locks (L.wr s b v) = PmWSU st K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s := by
  intro j K m s b v hE hb hba
  have hE0 := hE
  obtain ⟨⟨hJ, ⟨⟨hio, hpd, harm, hlks⟩, hlk0⟩, hG⟩, hEx, hRt⟩ := hE
  have P := hio.1
  have hT : K.heap (L.curW s) = some .tcb := P.cT
  have el := hlk K.toKLayout s b v hJ hb hba
  have ecur := hJ.curW_wr hb hba v
  have emsg := msgInfo_wr hJ hb hba v hT P.tA
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
    · have hv : ¬ ∃ w, InVcpu K.toKLayoutV w x := fun ⟨_, hw⟩ => not_inVcpu_empty hG.nv hw
      rw [ownP_off hx, ownP_off hx, ownV_off hv, ownV_off hv, eo]
  have e3 := (hJ.ioRWDS_wrSt (st := st) (Locks := Locks) hb hba v el).2.2
  have eR : PmRS st K Locks (L.wr s b v) = PmRS st K Locks s := by
    funext w
    simp only [PmRS, RPerm, GateOnly, eoP, el, LawfulStore.cpu_wr]
  have eW : PmWS st K Locks (L.wr s b v) = PmWS st K Locks s := by
    funext w
    simp only [PmWS, WPerm, eoP, el, LawfulStore.cpu_wr]
  refine ⟨⟨⟨hJ.userWr hb v, ⟨⟨ioQ_wr hIw K.toKLayout m s b v hJ hio hb hba,
    pm_pdwG j K m s b v hE0 hb hba, ?_, ?_⟩, invLk_wr hJ P hlk0 hb hba v⟩, gateEp_userWr hG hb hba⟩,
    pmEx_wr hJ P hEx hb hba v, pmRoot_wr hJ P hEx hRt hb hba v⟩, el, ?_, ?_, e3⟩
  · intro t info ht hi
    obtain rfl := hct t ht
    rw [emsg] at hi
    exact harm _ info (cur_thread_ok s) hi
  · intro i x hi hx
    rw [el]
    exact hlks i x hi hx
  · funext y; unfold PmRSU; rw [eR]
  · funext y; unfold PmWSU; rw [eW]

end huf

section obl
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP} {μ : U64 → U64}
variable {A : Type} {ar : machine.Arch A}

variable (st) in
/-- [W] **The decode block of an accepted PageMap run on the guarded store, with the slot's cap and the length's
computation as hypotheses** (`InvBlkW2`'s shape at the user-word sets and `ptU K`). Gen 12's `PmBlkUW` quantified
`cap` and `length` freely, as stpost's `InvBlkW` did; it is false for a `cap` the slot does not hold (a `Large` frame
cap maps through an unlocked PD entry), so the block is asked only for the cap the accepted run reads. -/
def PmBlkUW2 (ar : machine.Arch A) (p : localinv.Plan) (K : KLayoutP) (Locks : S → U64 → Prop)
    (P : S → Prop) : Prop :=
  ∀ s (a : A) info nx s1 s2 a1 buf length cap, P s → msg.msg_info st s (L.curW s) = ok info →
    InvChk st ar s a (L.curW s) p nx s1 s2 a1 →
    (if info.length > msg.N_MSG_REGISTERS then (if buf = 0#u64 then ok msg.N_MSG_REGISTERS else ok info.length)
      else ok info.length) = ok length →
    obj.Slot.cap st p.slot s2 = ok cap →
    ∀ y, syscall.decode_invocation st ar s2 a1 info.label length p.slot cap true true true false buf p.extra = ok y →
      syscall.decode_invocation (guard st (PmRSU st K Locks s) (PmWSU st K Locks s)) ar s2 a1
          info.label length p.slot cap true true true false buf p.extra = ok y ∧
      ∀ z, invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z →
        invRep (guard st (PmRSU st K Locks s) (PmWSU st K Locks s)) (L.curW s) y.2.1 y.2.2 y.1 = ok z ∧
        z.2.2 = core.result.Result.Ok () ∧
        FinOK (L := L) (guard st (PmRSU st K Locks s) (PmWSU st K Locks s))
          (IoRS (st := st) K.ptU Locks s) (PmWSU st K Locks s) ar s z.1 z.2.1

/-- **`acc` from the decode block at `PmPreG`** (gen 12's `pm_accU_of_blk` via stpost's `inv_acc_gen2`). -/
theorem pm_accU_of_blkG (hA : P0.ArchTotal ar) (hK : RegionOKP K) {number : I64}
    (hblk : PmBlkUW2 st ar p K Locks (PmPreG st Cs Ω Sg Ac Locks p K μ)) :
    PmAccUW st ar number p K Locks (PmPreG st Cs Ω Sg Ac Locks p K μ) := fun s a _ _ hE h => by
  obtain ⟨⟨hJ, hq, hG⟩, -, -⟩ := id hE
  have P := hq.1.1.1.ptU hG
  obtain ⟨-, -, -, -, -, -, hsl, -, -, -⟩ := pm_core hq
  obtain ⟨-, hf⟩ := P.lay.slot8 _ hsl
  have r0 : IoRS (st := st) K.ptU Locks s p.slot := by
    have := pm_slotRS hJ hq P (o := 0#u64) (by simp) (by simp)
    rwa [wadd_zero hf] at this
  have r8 := pm_slotRS hJ hq P (o := 8#u64) (by simp) (by simp)
  haveI : GRd (guard st (PmRSU st K Locks s) (PmWSU st K Locks s)) st (IoRS (st := st) K.ptU Locks s) :=
    grd_sub (fun _ hy => pmRSU_ioRS hG hy)
  exact inv_acc_gen2 (W := PmWSU st K Locks s) hA P
    ((P.ioWr (Locks := Locks)).mono (fun _ hy => pmWSU_ioWS hK hy)) (pm_seen hJ hq P) ⟨r0, r8⟩
    (fun info nx s1 s2 a1 buf length cap emi hc hl hk =>
      hblk s a info nx s1 s2 a1 buf length cap hE emi hc hl hk) h

end obl

section slot
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)

/-- **What is left of the PageMap slot's obligations at `PmPreG`** (module docstring). -/
structure PmObl4 (Cs Ω Sg Ac : Set U64) (Locks : S → U64 → Prop) : Prop where
  /-- [W] the decode block (what remains of `acc`). -/
  blk : ∀ (j : I64 × localinv.Plan) K m, PmBlkUW2 st ar j.2 K Locks (PmPreG st Cs Ω Sg Ac Locks j.2 K m)
  /-- [W] `move`. -/
  mv : ∀ (j : I64 × localinv.Plan) K m, PmMoveW st ar j.1 j.2 K Locks m (PmPreG st Cs Ω Sg Ac Locks j.2 K m)
  /-- [W] `ReadOnce` of accepting runs (the buffer word read once before its write). -/
  roA : ∀ (j : I64 × localinv.Plan) K m,
    PmRoAccW st ar j.1 j.2 K Locks m (R.invBodyPmG j.1 j.2) (PmPreG st Cs Ω Sg Ac Locks j.2 K m)
  /-- [P] the core set is below 64. -/
  cs : ∀ c ∈ Cs, c.val < 64
  /-- [P] the locks survive a user write. -/
  lk : PmLk st Locks

variable {st ar}

/-- **The PageMap slot family at `PmPreG`.** -/
def pmPathsG {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl4 st ar Cs Ω Sg Ac Locks) :
    PathsP (I64 × localinv.Plan) :=
  fun j K m hK hU =>
    pm_localPathU (K := K) (m0 := m) (Locks := Locks) ar hA hK hU j.1 j.2 hm
      (P := PmPreG st Cs Ω Sg Ac Locks j.2 K m) (fun _ h => h.1.2.1.1.1.1)
      (pm_accU_of_blkG hA hK (B.blk j K m)) (fun s a r hE => pm_dec hA j.1 s a r hE.1) (B.mv j K m)
      (fun s s' a r0 r hE => pm_ra hA j.1 s s' a r0 r hE.1)
      (pm_hufG (pm_iw B.cs) B.lk j K m)
      (R.invBodyPmG j.1 j.2)
      ((pm_isProgOn hA j.1).mono (fun _ hy => by
        obtain ⟨s0, hP, Al⟩ := hy
        exact ⟨s0, hP.1, alt_pmU Al⟩))
      (pm_noZero j.1 j.2) (B.roA j K m) (fun s s' a r hE => pm_ro hA j.1 s s' a r hE.1)

variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

end slot

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

end top

end
end Fl4Proofs.P2.E2EP
